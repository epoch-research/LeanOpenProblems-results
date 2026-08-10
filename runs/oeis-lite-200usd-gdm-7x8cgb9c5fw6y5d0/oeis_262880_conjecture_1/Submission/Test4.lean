import FormalConjectures.Util.ProblemImports

def test_ans : Prop := answer(sorry)

theorem test_ans_eq_true : test_ans = True := rfl

#print axioms test_ans_eq_true
