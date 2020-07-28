[CoqSentence(contents='Let inv b: negb (negb b) = b.', responses=[], goals=[CoqGoal(name=None, conclusion='negb (negb b) = b', hypotheses=[CoqHypothesis(names=['b'], body=None, type='bool')])]),
 CoqText(contents='\n  '),
 CoqSentence(contents='destruct b.', responses=[], goals=[CoqGoal(name=None, conclusion='negb (negb true) = true', hypotheses=[]), CoqGoal(name=None, conclusion='negb (negb false) = false', hypotheses=[])]),
 CoqText(contents=' '),
 CoqSentence(contents='all: reflexivity.', responses=[], goals=[]),
 CoqText(contents='\n'),
 CoqSentence(contents='Qed.', responses=[], goals=[]),
 CoqText(contents='\n'),
 CoqSentence(contents='Print Assumptions inv.', responses=['Closed under the global context'], goals=[])]
