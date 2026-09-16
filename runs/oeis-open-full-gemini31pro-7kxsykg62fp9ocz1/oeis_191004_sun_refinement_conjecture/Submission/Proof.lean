import Submission.Spec

theorem oeis_191004_sun_refinement_conjecture_disproof_test : ¬ (type_of% @oeis_191004_sun_refinement_conjecture) := by
  intro h
  have h10 : 8 < 10 ∧ Even 10 ∧ 10 ∉ ({32, 152} : Finset ℕ) := by decide
  have h10_ref := h.2 10 h10
  rcases h10_ref with ⟨p, q, hp, hq, heq, hle, hjacobi⟩
  have hq_pos : 2 ≤ q := Nat.Prime.two_le hq
  have hq_eq_2 : q = 2 := by omega
  have hp8 : p = 8 := by omega
  subst hp8
  revert hp
  decide
