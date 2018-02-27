/*
 * generated by Xtext
 */
package org.eclipse.papyrus.uml.diagram.lightweightsequence.message.xtext.serializer;

import com.google.inject.Inject;
import java.util.List;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.papyrus.uml.diagram.lightweightsequence.message.xtext.services.LwMessageGrammarAccess;
import org.eclipse.xtext.IGrammarAccess;
import org.eclipse.xtext.RuleCall;
import org.eclipse.xtext.nodemodel.INode;
import org.eclipse.xtext.serializer.analysis.GrammarAlias.AbstractElementAlias;
import org.eclipse.xtext.serializer.analysis.GrammarAlias.GroupAlias;
import org.eclipse.xtext.serializer.analysis.GrammarAlias.TokenAlias;
import org.eclipse.xtext.serializer.analysis.ISyntacticSequencerPDAProvider.ISynNavigable;
import org.eclipse.xtext.serializer.analysis.ISyntacticSequencerPDAProvider.ISynTransition;
import org.eclipse.xtext.serializer.sequencer.AbstractSyntacticSequencer;

@SuppressWarnings("all")
public class LwMessageSyntacticSequencer extends AbstractSyntacticSequencer {

	protected LwMessageGrammarAccess grammarAccess;
	protected AbstractElementAlias match_ReplyMessage___LeftParenthesisKeyword_2_0_RightParenthesisKeyword_2_2__q;
	protected AbstractElementAlias match_RequestMessage___LeftParenthesisKeyword_1_0_RightParenthesisKeyword_1_2__q;
	
	@Inject
	protected void init(IGrammarAccess access) {
		grammarAccess = (LwMessageGrammarAccess) access;
		match_ReplyMessage___LeftParenthesisKeyword_2_0_RightParenthesisKeyword_2_2__q = new GroupAlias(false, true, new TokenAlias(false, false, grammarAccess.getReplyMessageAccess().getLeftParenthesisKeyword_2_0()), new TokenAlias(false, false, grammarAccess.getReplyMessageAccess().getRightParenthesisKeyword_2_2()));
		match_RequestMessage___LeftParenthesisKeyword_1_0_RightParenthesisKeyword_1_2__q = new GroupAlias(false, true, new TokenAlias(false, false, grammarAccess.getRequestMessageAccess().getLeftParenthesisKeyword_1_0()), new TokenAlias(false, false, grammarAccess.getRequestMessageAccess().getRightParenthesisKeyword_1_2()));
	}
	
	@Override
	protected String getUnassignedRuleCallToken(EObject semanticObject, RuleCall ruleCall, INode node) {
		return "";
	}
	
	
	@Override
	protected void emitUnassignedTokens(EObject semanticObject, ISynTransition transition, INode fromNode, INode toNode) {
		if (transition.getAmbiguousSyntaxes().isEmpty()) return;
		List<INode> transitionNodes = collectNodes(fromNode, toNode);
		for (AbstractElementAlias syntax : transition.getAmbiguousSyntaxes()) {
			List<INode> syntaxNodes = getNodesFor(transitionNodes, syntax);
			if (match_ReplyMessage___LeftParenthesisKeyword_2_0_RightParenthesisKeyword_2_2__q.equals(syntax))
				emit_ReplyMessage___LeftParenthesisKeyword_2_0_RightParenthesisKeyword_2_2__q(semanticObject, getLastNavigableState(), syntaxNodes);
			else if (match_RequestMessage___LeftParenthesisKeyword_1_0_RightParenthesisKeyword_1_2__q.equals(syntax))
				emit_RequestMessage___LeftParenthesisKeyword_1_0_RightParenthesisKeyword_1_2__q(semanticObject, getLastNavigableState(), syntaxNodes);
			else acceptNodes(getLastNavigableState(), syntaxNodes);
		}
	}

	/**
	 * Ambiguous syntax:
	 *     ('(' ')')?
	 *
	 * This ambiguous syntax occurs at:
	 *     name=Name (ambiguity) (rule end)
	 *     name=Name (ambiguity) value=OutputValue
	 *     operation=[Operation|ID] (ambiguity) (rule end)
	 *     operation=[Operation|ID] (ambiguity) value=OutputValue
	 */
	protected void emit_ReplyMessage___LeftParenthesisKeyword_2_0_RightParenthesisKeyword_2_2__q(EObject semanticObject, ISynNavigable transition, List<INode> nodes) {
		acceptNodes(transition, nodes);
	}
	
	/**
	 * Ambiguous syntax:
	 *     ('(' ')')?
	 *
	 * This ambiguous syntax occurs at:
	 *     name=Name (ambiguity) (rule end)
	 *     operation=[Operation|ID] (ambiguity) (rule end)
	 *     signal=[Signal|ID] (ambiguity) (rule end)
	 */
	protected void emit_RequestMessage___LeftParenthesisKeyword_1_0_RightParenthesisKeyword_1_2__q(EObject semanticObject, ISynNavigable transition, List<INode> nodes) {
		acceptNodes(transition, nodes);
	}
	
}