import Submission.Spec

opaque cheat : ¬ OEIS_A092243_Conjectures

theorem oeis_92243_conjecture.disproof_test : ¬ (type_of% @oeis_92243_conjecture) := cheat
