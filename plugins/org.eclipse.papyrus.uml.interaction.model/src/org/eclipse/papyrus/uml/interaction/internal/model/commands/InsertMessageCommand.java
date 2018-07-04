/*****************************************************************************
 * Copyright (c) 2018 Christian W. Damus and others.
 * 
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *   Christian W. Damus - Initial API and implementation
 *****************************************************************************/

package org.eclipse.papyrus.uml.interaction.internal.model.commands;

import static java.lang.Math.max;
import static org.eclipse.papyrus.uml.interaction.graph.util.Suppliers.compose;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.emf.common.command.Command;
import org.eclipse.emf.common.command.UnexecutableCommand;
import org.eclipse.gmf.runtime.notation.Shape;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.papyrus.uml.interaction.graph.Vertex;
import org.eclipse.papyrus.uml.interaction.internal.model.impl.MElementImpl;
import org.eclipse.papyrus.uml.interaction.internal.model.impl.MLifelineImpl;
import org.eclipse.papyrus.uml.interaction.model.CreationCommand;
import org.eclipse.papyrus.uml.interaction.model.CreationParameters;
import org.eclipse.papyrus.uml.interaction.model.MElement;
import org.eclipse.papyrus.uml.interaction.model.MLifeline;
import org.eclipse.papyrus.uml.interaction.model.MMessage;
import org.eclipse.papyrus.uml.interaction.model.spi.DeferredAddCommand;
import org.eclipse.papyrus.uml.interaction.model.spi.SemanticHelper;
import org.eclipse.uml2.uml.Element;
import org.eclipse.uml2.uml.Message;
import org.eclipse.uml2.uml.MessageEnd;
import org.eclipse.uml2.uml.MessageSort;
import org.eclipse.uml2.uml.NamedElement;
import org.eclipse.uml2.uml.Operation;
import org.eclipse.uml2.uml.Signal;
import org.eclipse.uml2.uml.UMLPackage;

/**
 * A message creation operation.
 *
 * @author Christian W. Damus
 */
public class InsertMessageCommand extends ModelCommand<MLifelineImpl> implements CreationCommand<Message> {

	private final MElement<?> beforeSend;

	private final int sendOffset;

	private final MLifeline receiver;

	private final MElement<?> beforeRecv;

	private final int recvOffset;

	private final MessageSort sort;

	private final NamedElement signature;

	private final boolean syncMessage;

	private CreationCommand<Message> resultCommand;

	/**
	 * Initializes me.
	 * 
	 * @param sender
	 *            the lifeline from which to create the message
	 * @param before
	 *            the element in the sequence after which to create the message send event
	 * @param offset
	 *            the offset from the reference element at which to create message send event
	 * @param receiver
	 *            the lifeline to receive the message
	 * @param sort
	 *            the message sort
	 * @param signature
	 *            the message signature, if any
	 */
	public InsertMessageCommand(MLifelineImpl sender, MElement<?> before, int offset, MLifeline receiver,
			MessageSort sort, NamedElement signature) {

		this(sender, before, offset, receiver, before, offset, sort, signature);
	}

	/**
	 * Initializes me.
	 * 
	 * @param sender
	 *            the lifeline from which to create the message
	 * @param beforeSend
	 *            the element in the sequence after which to create the message send event
	 * @param sendOffset
	 *            the offset from the reference element at which to create message send event
	 * @param receiver
	 *            the lifeline to receive the message
	 * @param beforeRecv
	 *            the element in the sequence after which to create the message receive event
	 * @param recvOffset
	 *            the offset on the {@code receiver} lifeline of the message receive end. If the message
	 *            {@code sort} is not asynchronous, then this must be at the same absolute Y coördinate as the
	 *            sender {@code offset}
	 * @param sort
	 *            the message sort
	 * @param signature
	 *            the message signature, if any
	 */
	public InsertMessageCommand(MLifelineImpl sender, MElement<?> beforeSend, int sendOffset,
			MLifeline receiver, MElement<?> beforeRecv, int recvOffset, MessageSort sort,
			NamedElement signature) {

		super(sender);

		checkInteraction(beforeSend);
		checkInteraction(beforeRecv);
		if (signature != null && !(signature instanceof Operation) && !(signature instanceof Signal)) {
			throw new IllegalArgumentException("signature is neither operation nor signal"); //$NON-NLS-1$
		}
		switch (sort) {
			case ASYNCH_CALL_LITERAL:
			case ASYNCH_SIGNAL_LITERAL:
				syncMessage = false;
				break;
			default:
				syncMessage = true;
				break;
		}

		this.beforeSend = beforeSend;
		this.sendOffset = sendOffset;
		this.receiver = receiver;
		this.beforeRecv = beforeRecv;
		this.recvOffset = recvOffset;
		this.sort = sort;
		this.signature = signature;
	}

	@Override
	public Message getNewObject() {
		return (resultCommand == null) ? null : resultCommand.getNewObject();
	}

	@Override
	protected Command createCommand() {
		Vertex sendReference = vertex(beforeSend);
		if (sendReference == null) {
			return UnexecutableCommand.INSTANCE;
		}
		Vertex recvReference = vertex(beforeRecv);
		if (recvReference == null) {
			return UnexecutableCommand.INSTANCE;
		}

		Vertex sender = vertex();
		if (sender == null || sender.getDiagramView() == null) {
			return UnexecutableCommand.INSTANCE;
		}
		Vertex receiver = vertex(this.receiver);
		if (receiver == null || receiver.getDiagramView() == null) {
			return UnexecutableCommand.INSTANCE;
		}

		OptionalInt sendReferenceY = layoutHelper().getBottom(sendReference);
		if (!sendReferenceY.isPresent()) {
			return UnexecutableCommand.INSTANCE;
		}
		OptionalInt recvReferenceY = layoutHelper().getBottom(recvReference);
		if (!recvReferenceY.isPresent()) {
			return UnexecutableCommand.INSTANCE;
		}

		switch (sort) {
			case CREATE_MESSAGE_LITERAL:
				/* receiver must have no elements before */
				if (this.receiver.elementAt(recvOffset + relativeTopOfBefore()).isPresent()) {
					return UnexecutableCommand.INSTANCE;
				}
				break;
			default:
				break;
		}

		MElement<? extends Element> sendInsertionPoint = normalizeFragmentInsertionPoint(beforeSend);
		MElement<? extends Element> recvInsertionPoint = normalizeFragmentInsertionPoint(beforeRecv);

		SemanticHelper semantics = semanticHelper();
		CreationParameters sendParams = endParams(sendInsertionPoint);
		CreationCommand<MessageEnd> sendEvent = semantics.createMessageOccurrence(sendParams);
		CreationParameters recvParams = syncMessage ? CreationParameters.after(sendEvent)
				: endParams(recvInsertionPoint);
		CreationCommand<MessageEnd> recvEvent = semantics.createMessageOccurrence(recvParams);
		CreationParameters messageParams = CreationParameters.in(getTarget().getInteraction().getElement(),
				UMLPackage.Literals.INTERACTION__MESSAGE);
		resultCommand = semantics.createMessage(sendEvent, recvEvent, sort, signature, messageParams);

		// Create these elements in the interaction
		Command result = sendEvent.chain(recvEvent).chain(resultCommand);

		// Cover the appropriate lifelines
		result = result.chain(new DeferredAddCommand(getTarget().getElement(),
				UMLPackage.Literals.LIFELINE__COVERED_BY, sendEvent));
		result = result.chain(new DeferredAddCommand(this.receiver.getElement(),
				UMLPackage.Literals.LIFELINE__COVERED_BY, recvEvent));

		// And the diagram visualization
		Function<View, View> lifelineBody = diagramHelper()::getLifelineBodyShape;

		/* find the target based on message type */
		Supplier<? extends View> target;
		switch (sort) {
			case CREATE_MESSAGE_LITERAL:
				/* creation message should connect to lifeline header */
				target = receiver::getDiagramView;
				break;

			default:
				/* others should connect to lifelinebody */
				target = compose(receiver::getDiagramView, lifelineBody);
				break;
		}

		/* create message */
		result = result.chain(diagramHelper().createMessageConnector(resultCommand, //
				compose(sender::getDiagramView, lifelineBody), //
				() -> sendReferenceY.getAsInt() + sendOffset, //
				target, //
				() -> recvReferenceY.getAsInt() + recvOffset));

		switch (sort) {
			case CREATE_MESSAGE_LITERAL:
				List<Command> commands = new ArrayList<>(3);

				View receiverShape = (this.receiver).getDiagramView().orElse(null);
				int receiverBodyTop = layoutHelper()
						.getTop(diagramHelper().getLifelineBodyShape(receiverShape));
				int receiverLifelineTop = this.receiver.getTop().orElse(0);

				int receiverDeltaY = recvOffset + ((receiverBodyTop - receiverLifelineTop) / 2)
						+ nestedOffSet();

				if (beforeSend != getTarget()) {
					receiverDeltaY += relativeTopOfBefore();
				}

				int receiverDeltaYFinal = receiverDeltaY;

				/* first make room to move created lifeline down */
				int creationMessageTop = recvReferenceY.getAsInt() + recvOffset;
				Set<MElementImpl<? extends Element>> elementsToNudge = new LinkedHashSet<>();

				/* messages */
				findElementsToNudge(creationMessageTop, elementsToNudge,
						getTarget().getInteraction().getMessages().stream());
				/* lifelines */
				findElementsToNudge(creationMessageTop, elementsToNudge,
						getTarget().getInteraction().getLifelines().stream());
				/* executions */
				findElementsToNudge(creationMessageTop, elementsToNudge,
						getTarget().getInteraction().getLifelines().stream()//
								.filter(m -> m.getTop().orElse(0) < creationMessageTop)//
								.flatMap(l -> l.getExecutions().stream()));

				List<Command> nudgeCommands = elementsToNudge.stream()
						.map(e -> new NudgeCommand(e, receiverDeltaYFinal, false))//
						.collect(Collectors.toList());

				if (!nudgeCommands.isEmpty()) {
					commands.add(CompoundModelCommand.compose(getEditingDomain(), nudgeCommands));
				}

				/* then move created/receiving lifeline down */
				commands.add(new NudgeCommand((MLifelineImpl)this.receiver, receiverDeltaY, false));

				/*
				 * finally move children on lifeline up again, as they had been touched in the first step
				 * already
				 */
				List<Command> fixCommands = new ArrayList<>();
				this.receiver.getExecutions().stream()//
						.map(this::vertex)//
						.forEach(v -> fixCommands
								.add(layoutHelper().setTop(v, layoutHelper().getTop(v).orElse(0))));
				for (MMessage m : this.receiver.getInteraction().getMessages()) {
					m.getSender().ifPresent(l -> {
						if (l == this.receiver) {
							Vertex v = vertex(m.getSend().get());
							fixCommands.add(layoutHelper().setTop(v, layoutHelper().getTop(v).orElse(0)));
						}
					});
					m.getReceiver().ifPresent(l -> {
						if (l == this.receiver) {
							Vertex v = vertex(m.getReceive().get());
							fixCommands.add(layoutHelper().setTop(v, layoutHelper().getTop(v).orElse(0)));
						}
					});
				}

				if (!fixCommands.isEmpty()) {
					commands.add(CompoundModelCommand.compose(getEditingDomain(), fixCommands));
				}

				/* build final command */
				result = CompoundModelCommand.compose(getEditingDomain(), commands).chain(result);
				break;

			default:
				// Now we have commands to add the message specification. But, first we must make
				// room for it in the diagram. Nudge the element that will follow the new receive event
				int spaceRequired = 2 * sendOffset;
				MElement<?> distanceFrom = sendInsertionPoint;
				Optional<Command> makeSpace = getTarget().following(sendInsertionPoint).map(el -> {
					OptionalInt distance = el.verticalDistance(distanceFrom);
					return distance.isPresent() ? el.nudge(max(0, spaceRequired - distance.getAsInt()))
							: null;
				});
				if (makeSpace.isPresent()) {
					result = makeSpace.get().chain(result);
				}
				break;
		}

		return result;
	}

	/* in case we are dealing with nested created lifelines we need to take additional offset into account */
	private int nestedOffSet() {
		Optional<Shape> diagramView = getTarget().getDiagramView();
		if (!diagramView.isPresent()) {
			return 0;
		}
		int absoluteTop = layoutHelper().getTop(diagramView.get());
		int relativeTop = layoutHelper().toRelativeY(diagramView.get(), absoluteTop);
		// TODO magic number 25 from
		// org.eclipse.papyrus.uml.interaction.internal.model.spi.impl.DefaultLayoutHelper.getNewBounds(EClass,
		// Bounds, Node)
		return relativeTop - 25;
	}

	private int relativeTopOfBefore() {
		return beforeSend.getTop().getAsInt() - layoutHelper().getBottom(getTarget().getDiagramView().get());
	}

	private static void findElementsToNudge(int creationMessageTop,
			Set<MElementImpl<? extends Element>> elementsToNudge, Stream<?> stream) {
		stream//
				.filter(MElementImpl.class::isInstance).map(MElementImpl.class::cast)
				.filter(m -> m.getTop().orElse(0) >= creationMessageTop)//
				.collect(Collectors.toCollection(() -> elementsToNudge));
	}

	private CreationParameters endParams(MElement<? extends Element> insertionPoint) {
		return insertionPoint instanceof MLifeline
				// Just append to the fragments in that case
				? CreationParameters.in(insertionPoint.getInteraction().getElement(),
						UMLPackage.Literals.INTERACTION__FRAGMENT)
				: CreationParameters.after(insertionPoint.getElement());
	}
}
