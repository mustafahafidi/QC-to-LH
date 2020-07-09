### Useful look-up regexes

1. Simple induction: `(====\n.*prop(?!.*hint))`

2. Needed induction help: `prop.*(hint: caseExpand *\)|(hint:.*induction.*)|(hint.*non-simp-ind))`

3. Needed lemma help: `(hint:.*lemma(?!.*induction)(?!.*non-simp-ind))`

   Possible use of rewriting (equality lemmata): `(hint:.*lemma(?!.*induction)(?!.*non-simp-ind).*\n.*\n.*rewrite)`
   
   Failed rewriting: `(hint:.*lemma(?!.*induction)(?!.*non-simp-ind).*\n.*\n--.*rewrite)`
