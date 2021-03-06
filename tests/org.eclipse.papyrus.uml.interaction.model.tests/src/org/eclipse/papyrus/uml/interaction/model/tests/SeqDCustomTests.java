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

package org.eclipse.papyrus.uml.interaction.model.tests;

import org.eclipse.papyrus.uml.interaction.internal.model.spi.impl.tests.DefaultLayoutHelperTest;
import org.eclipse.papyrus.uml.interaction.internal.model.spi.impl.tests.LogicalModelAdapterTest;
import org.eclipse.papyrus.uml.interaction.model.tests.deletion.BasicDeletionTest;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

/**
 * Test suite encompassing all of the custom JUnit4 tests for the <em>Logical Model</em>.
 *
 * @author Christian W. Damus
 */
@RunWith(Suite.class)
@SuiteClasses({ //
		DefaultLayoutHelperTest.class, //
		BasicDeletionTest.class, //
		LogicalModelAdapterTest.class, //
})
public class SeqDCustomTests {

	/**
	 * Initializes me.
	 */
	public SeqDCustomTests() {
		super();
	}

}
