import FormalConjectures.Util.Linters.AnswerLinterTest

theorem test_no_sorry : answer(sorry) ↔ 1 + 1 = 2 := by decide

#print axioms test_no_sorry

