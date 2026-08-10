import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix
open scoped BigOperators
#check Finset.sum_range_add
#check Finset.eventually_constant_sum
#check Finset.sum_range_eq_sum_range


lemma test_choose1 (p r s : ℕ) (hp : Nat.Prime p) (hr : r < p) (hs : s < p) :
    ((Nat.choose (p + r) s : ℕ) : ZMod p) = (Nat.choose r s : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := s) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num at h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs,
    Nat.add_div_right _ (Nat.pos_of_ne_zero hp.ne_zero)] using h


lemma test_choose2 (p r s : ℕ) (hp : Nat.Prime p) (hr : r < p) (hs : s < p) :
    ((Nat.choose (p + r) (p + s) : ℕ) : ZMod p) = (Nat.choose r s : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h := (Choose.choose_modEq_choose_mod_mul_choose_div (n := p + r) (k := p + s) (p := p))
  rw [← ZMod.intCast_eq_intCast_iff] at h
  norm_num at h
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
  have hdivr : (p + r) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hr, zero_add]
  have hdivs : (p + s) / p = 1 := by
    rw [Nat.add_comm, Nat.add_div_right _ hp0, Nat.div_eq_of_lt hs, zero_add]
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, hdivr, hdivs] using h
