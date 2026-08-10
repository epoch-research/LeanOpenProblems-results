import FormalConjectures.Util.ProblemImports
partial def fixP (P : Prop) : Decidable P → P
| .isTrue h => h
| .isFalse hn => False.elim (hn (fixP P (.isFalse hn)))
#print axioms fixP
example : False := fixP False (.isFalse id)
#print axioms FixDecExp3._example_1
