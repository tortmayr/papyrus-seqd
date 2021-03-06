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
 *   
 *****************************************************************************/

package org.eclipse.papyrus.uml.diagram.sequence.runtime.internal.edit.policies;

import java.util.Optional;
import java.util.OptionalInt;

import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.emf.common.command.Command;
import org.eclipse.emf.common.command.UnexecutableCommand;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.gmf.runtime.emf.type.core.IElementType;
import org.eclipse.gmf.runtime.emf.type.core.IHintedType;
import org.eclipse.gmf.runtime.notation.Shape;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.papyrus.uml.diagram.sequence.runtime.util.SequenceTypeSwitch;
import org.eclipse.papyrus.uml.interaction.model.MElement;
import org.eclipse.papyrus.uml.interaction.model.MInteraction;
import org.eclipse.papyrus.uml.interaction.model.MLifeline;
import org.eclipse.papyrus.uml.interaction.model.MObject;
import org.eclipse.papyrus.uml.interaction.model.spi.ViewTypes;
import org.eclipse.papyrus.uml.interaction.model.util.SequenceDiagramSwitch;
import org.eclipse.uml2.uml.Element;
import org.eclipse.uml2.uml.Lifeline;

/**
 * Lifeline creation edit policy based on the <em>Logical Model</em>.
 */
public class LifelineCreationEditPolicy extends LogicalModelCreationEditPolicy {

	@Override
	protected Optional<org.eclipse.emf.common.command.Command> getCreationCommand(MInteraction interaction,
			Element parentElement, View parentView, Point location, Dimension size, IElementType type) {

		Optional<MLifeline> mLifeline = interaction.getLifeline((Lifeline)parentElement);

		// compute command for the given request
		class CommandSwitch extends SequenceDiagramSwitch<Command> {

			@Override
			@SuppressWarnings("hiding")
			public Command caseMLifeline(MLifeline lifeline) {
				return new SequenceTypeSwitch<Command>() {
					@Override
					public Command caseExecutionSpecification(IElementType type) {
						EClass eClass = type.getEClass();
						Optional<MElement<?>> before = lifeline.elementAt(location.y());

						int offset = location.y();

						if (before.isPresent()) {
							// Get the bottom of the before element
							OptionalInt bottom = before.get().getBottom();
							if (bottom.isPresent()) {
								int relativeBottom = bottom.getAsInt()
										- getLayoutHelper().getTop((Shape)parentView);
								offset = offset - relativeBottom;
							} else {
								// If it doesn't have a bottom, then ignore it
								before = Optional.empty();
							}
						}

						int height = size != null ? size.height
								: getLayoutConstraints().getMinimumHeight(ViewTypes.EXECUTION_SPECIFICATION);

						return lifeline.insertExecutionAfter(before.orElse(lifeline), offset, height, eClass);
					}

					@Override
					public Command caseAsyncMessage(IHintedType type) {
						return null;
					}

					@Override
					public Command defaultCase(Object object) {
						return CommandSwitch.super.caseMLifeline(lifeline);
					}
				}.doSwitch(type);
			}

			@Override
			public Command defaultCase(MObject object) {
				return UnexecutableCommand.INSTANCE;
			}
		}

		return mLifeline.map(new CommandSwitch()::doSwitch);
	}

}
