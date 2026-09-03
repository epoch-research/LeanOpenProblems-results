import Submission.ReciprocalMertens

/-! Uniform Mertens bounds for arbitrary finite prime sets, with a cardinality budget. -/
namespace Erdos970.WeightedMertens
open Finset Real

lemma tail_sum_le_card_div (P : Finset ℕ) (b : ℝ) (hb : 0 < b) :
    (∑ p ∈ P.filter (fun p : ℕ => b < (p : ℝ)), (p : ℝ)⁻¹) ≤ (P.card : ℝ) / b := by
  calc
    _ ≤ ∑ _p ∈ P.filter (fun p : ℕ => b < (p : ℝ)), b⁻¹ := by
      apply sum_le_sum
      intro p hp
      exact inv_anti₀ hb (mem_filter.mp hp).2.le
    _ = ((P.filter (fun p : ℕ => b < (p : ℝ))).card : ℝ) / b := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast card_filter_le P _) hb.le

/-- A reciprocal-tail estimate retaining both the exact log-log coefficient and the
cardinality-controlled contribution beyond an arbitrary upper cutoff. -/
theorem prime_set_tail (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ P.filter (fun p : ℕ => a < (p : ℝ)), (p : ℝ)⁻¹) ≤
      log (log b) - log (log a) + 2 * (boundConstant + 1) / log a + (P.card : ℝ) / b := by
  classical
  let T := P.filter (fun p : ℕ => a < (p : ℝ))
  have hsplit := sum_filter_add_sum_filter_not T (fun p : ℕ => (p : ℝ) ≤ b) (fun p : ℕ => (p : ℝ)⁻¹)
  have hsmall : (∑ p ∈ T.filter (fun p : ℕ => (p : ℝ) ≤ b), (p : ℝ)⁻¹) ≤ reciprocalInterval a b := by
    unfold reciprocalInterval
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpT, hpb⟩ := mem_filter.mp hp
      obtain ⟨hpP, hpa⟩ := mem_filter.mp hpT
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith)).mpr hpa,
        Nat.le_floor hpb⟩, hP p hpP⟩
    · intro p hp hn
      positivity
  have hlarge : (∑ p ∈ T.filter (fun p : ℕ => ¬(p : ℝ) ≤ b), (p : ℝ)⁻¹) ≤ (P.card : ℝ) / b := by
    calc
      _ ≤ ∑ p ∈ P.filter (fun p : ℕ => b < (p : ℝ)), (p : ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hp).1).1, lt_of_not_ge (mem_filter.mp hp).2⟩
        · intro p hp hn
          positivity
      _ ≤ _ := tail_sum_le_card_div P b (by linarith)
  have hmain := (abs_le.mp (abs_reciprocalInterval_sub_loglog ha hab)).2
  change (∑ p ∈ T, (p : ℝ)⁻¹) ≤ _
  linarith

noncomputable def reciprocalConstant : ℝ :=
  3 / 2 - log (log 2) + 2 * (boundConstant + 1) / log 2

lemma primes_small_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {b : ℝ} (hb : 2 ≤ b) :
    (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) ≤ b), (p : ℝ)⁻¹) ≤ 1 / 2 + reciprocalInterval 2 b := by
  have hsub : P.filter (fun p : ℕ => (p : ℝ) ≤ b) ⊆
      insert 2 ((Ioc 2 ⌊b⌋₊).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hpP, hpb⟩ := mem_filter.mp hp
    have hpp := hP p hpP
    by_cases hp2 : p = 2
    · simp [hp2]
    · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := hpp.two_le; omega,
        Nat.le_floor hpb⟩, hpp⟩)
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ℕ => (p : ℝ)⁻¹) (fun p hp hn => by positivity)
  simpa [reciprocalInterval] using h

/-- For any set of at most k primes, the reciprocal sum is at most log log(k+2)
plus one absolute constant. -/
theorem prime_set_reciprocal_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : P.card ≤ k) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ log (log ((k : ℝ) + 2)) + reciprocalConstant := by
  have hsplit := sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ (k : ℝ) + 2)
    (fun p : ℕ => (p : ℝ)⁻¹)
  have hs := primes_small_sum_le P hP (by have := Nat.cast_nonneg (α := ℝ) k; linarith : (2 : ℝ) ≤ (k : ℝ) + 2)
  have hl := tail_sum_le_card_div P ((k : ℝ) + 2) (by positivity)
  have hc : (P.card : ℝ) / ((k : ℝ) + 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have := (Nat.cast_le.mpr hk : (P.card : ℝ) ≤ k)
    linarith
  have hm := (abs_le.mp (abs_reciprocalInterval_sub_loglog (a := 2) (b := (k : ℝ) + 2)
    (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith))).2
  simp only [not_le] at hsplit
  dsimp only [reciprocalConstant]
  linarith

lemma reciprocal_correction_sum (n : ℕ) :
    (∑ p ∈ range (n + 2) with 2 ≤ p, 1 / ((p : ℝ) * (p - 1))) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num [sum_filter, sum_range_succ]
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, sum_filter, sum_range_succ, ← sum_filter, ih]
    simp only [Nat.le_add_left 2 n, if_true, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    ring_nf
    field_simp [hn.ne', hn2.ne', show (1 : ℝ) + n ≠ 0 by positivity]
    <;> ring

lemma reciprocal_correction_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, 2 ≤ p) :
    (∑ p ∈ P, 1 / ((p : ℝ) * (p - 1))) ≤ 1 := by
  have hsub : P ⊆ (range (P.sup id + 2)).filter (fun p : ℕ => 2 ≤ p) := by
    intro p hp
    have hh : p ≤ P.sup id := le_sup (f := id) hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), hP p hp⟩
  have h := sum_le_sum_of_subset_of_nonneg hsub (f := fun p : ℕ => 1 / ((p : ℝ) * (p - 1))) (by
    intro p hp hn
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2
    have : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    positivity)
  rw [reciprocal_correction_sum] at h
  have : 0 ≤ 1 / (((P.sup id : ℕ) : ℝ) + 1) := by positivity
  linarith

lemma log_factor_lower {p : ℕ} (hp : p.Prime) :
    -(p : ℝ)⁻¹ - 1 / ((p : ℝ) * (p - 1)) ≤ log (1 - (p : ℝ)⁻¹) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hf : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ hp0).mpr hpR)
  convert one_sub_inv_le_log_of_pos hf using 1
  have hpred : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hpred, hp0.ne']
  <;> ring

/-- The sharp logarithmic order of the Euler-product lower bound, uniformly in the prime set. -/
theorem prime_set_density_lower (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k : ℕ) (hk : P.card ≤ k) :
    exp (-reciprocalConstant - 1) / log ((k : ℝ) + 2) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  have hf (p : ℕ) (hp : p ∈ P) : 0 < 1 - (p : ℝ)⁻¹ := by
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hpR)
  have hlog : -(∑ p ∈ P, (p : ℝ)⁻¹) - 1 ≤ log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) := by
    rw [log_prod (fun p hp => (hf p hp).ne')]
    have hs := sum_le_sum (fun p hp => log_factor_lower (hP p hp))
    rw [sum_sub_distrib, sum_neg_distrib] at hs
    have hc := reciprocal_correction_le_one P (fun p hp => (hP p hp).two_le)
    linarith
  have hm := prime_set_reciprocal_le P hP k hk
  have hmain : -reciprocalConstant - 1 - log (log ((k : ℝ) + 2)) ≤
      log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) := by linarith
  have he := exp_le_exp.mpr hmain
  rw [exp_sub, exp_log (log_pos (show (1 : ℝ) < (k : ℝ) + 2 by have := Nat.cast_nonneg (α := ℝ) k; linarith)), exp_log (prod_pos hf)] at he
  exact he

#print axioms prime_set_tail
#print axioms prime_set_density_lower
end Erdos970.WeightedMertens
