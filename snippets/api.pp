[CoqSentence(contents='Let inv b: negb (negb b) = b.', messages=[], goals=[CoqGoal(name=None, conclusion='negb (negb b) = b', hypotheses=[CoqHypothesis(names=['b'], body=None, type='bool')])]),
 CoqText(contents='\n  '),
 CoqSentence(contents='destruct b.', messages=[], goals=[CoqGoal(name=None, conclusion='negb (negb true) = true', hypotheses=[]), CoqGoal(name=None, conclusion='negb (negb false) = false', hypotheses=[])]),
 CoqText(contents=' '),
 CoqSentence(contents='all: reflexivity.', messages=[], goals=[]),
 CoqText(contents='\n'),
 CoqSentence(contents='Qed.', messages=[], goals=[]),
 CoqText(contents='\n'),
 CoqSentence(contents='Print Assumptions inv.', messages=[CoqMessage(contents='Closed under the global context')], goals=[])]
