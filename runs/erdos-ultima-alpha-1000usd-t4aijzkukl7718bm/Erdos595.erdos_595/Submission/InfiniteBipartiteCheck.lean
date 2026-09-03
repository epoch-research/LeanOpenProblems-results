import Submission.InfinitePairRamsey
import Submission.HalfGraphRamsey
import Submission.PairBoxRamsey
#check Prod.Lex
#check Prod.Lex.instWellFoundedLT
#check Prod.Lex.toLex
#check toLex
#check Prod.Lex.left
#check Prod.Lex.right
#check Finset.sup
#check Filter.EventuallyEq.setoid
#check Quotient.out_eq
#check Quotient.mk_out
#check Setoid.quotient_eq_iff
#check Filter.eventually_atTop
example (A : Type*) [LinearOrder A] [WellFoundedLT A] : WellFoundedLT (A ×ₗ Fin 2) := inferInstance
example (A : Type*) [LinearOrder A] : LinearOrder (A ×ₗ Fin 2) := inferInstance
#check Prod.Lex.lt_iff
#check Prod.lex_lt_iff
#check Function.update_same
#check Function.update_noteq
#check Quotient.out_equiv_out
#check Quotient.eq_iff_equiv
