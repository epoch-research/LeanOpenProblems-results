import Submission.FactorialLambert

/-!
# Congruence for factorial Lambert coefficients

These are auxiliary arithmetic lemmas, not a proof of Erdős 68.
-/

namespace Erdos68Development

lemma total_dvd_mul_choose (N a : ℕ) : N ∣ a * N.choose a := by
  cases a with
  | zero => simp
  | succ a =>
    cases N with
    | zero => simp
    | succ N =>
      rw [Nat.mul_comm (a + 1), ← Nat.add_one_mul_choose_eq]
      exact dvd_mul_right _ _

lemma total_dvd_count_mul_multinomial {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) {a : α} (ha : a ∈ s) :
    (∑ i ∈ s, f i) ∣ f a * Nat.multinomial s f := by
  conv_rhs => rw [← Finset.insert_erase ha,
    Nat.multinomial_insert (Finset.notMem_erase a s) f,
    Finset.add_sum_erase _ f ha]
  rw [← Nat.mul_assoc]
  exact dvd_mul_of_dvd_left (total_dvd_mul_choose _ _) _

lemma pred_dvd_uniform_multinomial (d k : ℕ) :
    ((d + 1) * (k + 2) - 1) ∣
      ((d + 1) * (k + 2)).factorial / (d + 1).factorial ^ (k + 2) := by
  let f : ℕ → ℕ := fun i => if i = 0 then d else d + 1
  let I := Nat.multinomial (Finset.range (k + 2)) f
  let N := (k + 1) * (d + 1) + d
  have hsum : (∑ i ∈ Finset.range (k + 2), f i) = N := by
    rw [show k + 2 = (k + 1) + 1 by omega, Finset.sum_range_succ']
    simp [f, N]
  have hprod : (∏ i ∈ Finset.range (k + 2), (f i).factorial) =
      (d + 1).factorial ^ (k + 1) * d.factorial := by
    rw [show k + 2 = (k + 1) + 1 by omega, Finset.prod_range_succ']
    simp [f]
  have hN : N + 1 = (d + 1) * (k + 2) := by dsimp [N]; ring
  have h0 : N ∣ d * I := by
    simpa only [hsum, f, if_pos rfl] using
      total_dvd_count_mul_multinomial (Finset.range (k + 2)) f
        (a := 0) (by simp)
  have h1 : N ∣ (d + 1) * I := by
    simpa only [hsum, f, show (1 : ℕ) ≠ 0 by omega, if_false] using
      total_dvd_count_mul_multinomial (Finset.range (k + 2)) f
        (a := 1) (by simp)
  have hI : N ∣ I := by
    have := Nat.dvd_sub h1 h0
    simpa [Nat.add_mul] using this
  have hspec : ((d + 1).factorial ^ (k + 1) * d.factorial) * I = N.factorial := by
    simpa only [hsum, hprod] using Nat.multinomial_spec (Finset.range (k + 2)) f
  have hM : ((d + 1) * (k + 2)).factorial /
      (d + 1).factorial ^ (k + 2) = (k + 2) * I := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [← hN, Nat.factorial_succ, ← hspec, hN,
      show k + 2 = (k + 1) + 1 by omega, pow_succ]
    rw [Nat.factorial_succ]
    ring
  rw [hM, ← hN, Nat.add_sub_cancel]
  exact dvd_mul_of_dvd_right hI _

lemma pred_dvd_proper_lambert_summand {d m : ℕ} (hd2 : 2 ≤ d)
    (hd : d ∣ m) (hm : 0 < m) (hne : d ≠ m) :
    m - 1 ∣ m.factorial / d.factorial ^ (m / d) := by
  have hmul : d * (m / d) = m := Nat.mul_div_cancel' hd
  have hqpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hd) (by omega)
  have hq : 2 ≤ m / d := by
    by_contra h
    have heq : m / d = 1 := by omega
    rw [heq, Nat.mul_one] at hmul
    exact hne hmul
  have h := pred_dvd_uniform_multinomial (d - 1) (m / d - 2)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ d), Nat.sub_add_cancel hq, hmul] at h
  exact h

lemma lambertCoeff_modEq_pred {m : ℕ} (hm : 2 ≤ m) :
    Nat.ModEq (m - 1) (lambertCoeff m) 1 := by
  have hsum : (∑ d ∈ m.divisors, if d = m then 1 else 0) = 1 := by
    simp [Nat.mem_divisors, show m ≠ 0 by omega]
  conv_rhs => rw [← hsum]
  apply Nat.ModEq.sum
  intro d hd
  by_cases heq : d = m
  · subst d
    simp only [if_pos hm, Nat.div_self (by omega : 0 < m),
      pow_one, Nat.div_self (Nat.factorial_pos m)]
    rfl
  · rw [if_neg heq]
    by_cases hd2 : 2 ≤ d
    · rw [if_pos hd2]
      exact Nat.modEq_zero_iff_dvd.mpr
        (pred_dvd_proper_lambert_summand hd2 (Nat.dvd_of_mem_divisors hd)
          (by omega) heq)
    · simp only [if_neg hd2]
      rfl

end Erdos68Development

#print axioms Erdos68Development.lambertCoeff_modEq_pred
