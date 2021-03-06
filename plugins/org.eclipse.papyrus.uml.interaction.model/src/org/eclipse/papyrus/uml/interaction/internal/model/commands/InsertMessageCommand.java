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

import java.util.Optional;
import java.util.OptionalInt;
import java.util.function.Function;

import org.eclipse.emf.common.command.Command;
import org.eclipse.emf.common.command.UnexecutableCommand;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.papyrus.uml.interaction.graph.Vertex;
import org.eclipse.papyrus.uml.interaction.internal.model.impl.MLifelineImpl;
import org.eclipse.papyrus.uml.interaction.model.CreationCommand;
import org.eclipse.papyrus.uml.interaction.model.CreationParameters;
import org.eclipse.papyrus.uml.interaction.model.MElement;
import org.eclipse.papyrus.uml.interaction.model.MLifeline;
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
		result = result.chain(diagramHelper().createMessageConnector(resultCommand, //
				compose(sender::getDiagramView, lifelineBody), () -> sendReferenceY.getAsInt() + sendOffset, //
				compose(receiver::getDiagramView, lifelineBody),
				() -> recvReferenceY.getAsInt() + recvOffset));

		// Now we have commands to add the message specification. But, first we must make
		// room for it in the diagram. Nudge the element that will follow the new receive event
		int spaceRequired = 2 * sendOffset;
		MElement<?> distanceFrom = sendInsertionPoint;
		Optional<Command> makeSpace = getTarget().following(sendInsertionPoint).map(el -> {
			OptionalInt distance = el.verticalDistance(distanceFrom);
			return distance.isPresent() ? el.nudge(max(0, spaceRequired - distance.getAsInt())) : null;
		});
		if (makeSpace.isPresent()) {
			result = makeSpace.get().chain(result);
		}

		return result;
	}

	private CreationParameters endParams(MElement<? extends Element> insertionPoint) {
		return insertionPoint instanceof MLifeline
				// Just append to the fragments in that case
				? CreationParameters.in(insertionPoint.getInteraction().getElement(),
						UMLPackage.Literals.INTERACTION__FRAGMENT)
				: CreationParameters.after(insertionPoint.getElement());
	}
}
