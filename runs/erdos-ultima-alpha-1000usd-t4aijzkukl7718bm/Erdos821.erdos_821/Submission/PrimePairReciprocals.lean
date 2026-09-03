import Submission.CanonicalParentMassTest
import Submission.Sieve

/-!
# Reciprocal convergence for fixed-cofactor prime pairs

The two-prime upper sieve makes fixed-cofactor prime constellations negligible
for reciprocal-mass estimates, even if they occur infinitely often. This does
not control parents with large cofactors and does not settle Erdos 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

/-- A geometric counting criterion that does not require a monotone indicator. -/
lemma summable_reciprocal_of_summable_geometric_count (S : Set ℕ) (t : ℕ) (ht : 1 ≤ t)
    (H : Summable (fun L : ℕ =>
      (((range (2^(t*L))).filter (fun n => n ∈ S)).card : ℝ)/(2 : ℝ)^(t*L))) :
    Summable (S.indicator (fun n : ℕ => 1/(n : ℝ))) := by
  classical
  let f := S.indicator (fun n : ℕ => 1/(n : ℝ))
  let b : ℕ → ℕ := fun L => 2^(t*L)
  let c : ℕ → ℝ := fun L =>
    (((range (b (L+1))).filter (fun n => n ∈ S)).card : ℝ)/(b L : ℝ)
  have hf (n : ℕ) : 0 ≤ f n := Set.indicator_nonneg
    (fun n _ => div_nonneg (by norm_num) (Nat.cast_nonneg n)) n
  have hb (L : ℕ) : 0 < b L := pow_pos (by decide) _
  have hc (L : ℕ) : 0 ≤ c L := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcsum : Summable c := by
    convert ((summable_nat_add_iff 1).mpr H).mul_left ((2 : ℝ)^t) using 1
    ext L
    dsimp only [c, b, Function.comp_def]
    rw [Nat.cast_pow, Nat.cast_ofNat, Nat.mul_add, Nat.mul_one, pow_add]
    field_simp
    rw [pow_add]
    ring
  have hbmono (L : ℕ) : b L ≤ b (L+1) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left t (Nat.le_succ L))
  have hblock (L : ℕ) : (∑ n ∈ Ico (b L) (b (L+1)), f n) ≤ c L := by
    let E := (Ico (b L) (b (L+1))).filter (fun n => n ∈ S)
    have hsub : E ⊆ (range (b (L+1))).filter (fun n => n ∈ S) := by
      intro n hn
      obtain ⟨hnI, hnS⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hnI).2, hnS⟩
    calc
      _ = ∑ n ∈ E, 1/(n : ℝ) := by simp only [E, f, sum_filter, Set.indicator_apply]
      _ ≤ ∑ _n ∈ E, 1/(b L : ℝ) := by
        apply sum_le_sum
        intro n hn
        exact one_div_le_one_div_of_le (by exact_mod_cast hb L)
          (by exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1)
      _ = (E.card : ℝ)/(b L : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ c L := div_le_div_of_nonneg_right
        (by exact_mod_cast card_le_card hsub) (Nat.cast_nonneg _)
  have hpartial (L : ℕ) : (∑ n ∈ range (b L), f n) ≤
      (∑ n ∈ range (b 0), f n) + ∑ j ∈ range L, c j := by
    induction L with
    | zero => simp only [range_zero, sum_empty, add_zero, le_refl]
    | succ L ih =>
      rw [← sum_range_add_sum_Ico f (hbmono L), sum_range_succ]
      exact (_root_.add_le_add ih (hblock L)).trans_eq (add_assoc _ _ _)
  apply summable_of_sum_range_le hf
    (c := (∑ n ∈ range (b 0), f n) + ∑' j : ℕ, c j)
  intro N
  have hNb : N ≤ b N := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ (by omega)))
  exact (sum_le_sum_of_subset_of_nonneg (range_mono hNb) (fun n _ _ => hf n)).trans
    ((hpartial N).trans (_root_.add_le_add le_rfl
      (Summable.sum_le_tsum _ (fun j _ => hc j) hcsum)))

lemma pair_sieve_normalized_error (m : ℕ) :
    ((2 : ℝ)^(64*m)+(2 : ℝ)^(16*m)+1)/(2 : ℝ)^(128*m) ≤
      3*(1/2 : ℝ)^m := by
  have h64 : (2 : ℝ)^(64*m) ≤ (2 : ℝ)^(127*m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h16 : (2 : ℝ)^(16*m) ≤ (2 : ℝ)^(127*m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h1 : (1 : ℝ) ≤ (2 : ℝ)^(127*m) := one_le_pow₀ (by norm_num)
  have hsum : (2 : ℝ)^(64*m)+(2 : ℝ)^(16*m)+1 ≤ 3*(2 : ℝ)^(127*m) := by linarith
  refine (div_le_div_of_nonneg_right hsum (by positivity)).trans_eq ?_
  rw [mul_div_assoc, pow_mul (2 : ℝ) 127 m, pow_mul (2 : ℝ) 128 m, ← div_pow]
  norm_num

noncomputable def primePairSet (a : ℕ) : Set ℕ := {q | q.Prime ∧ (a*q+1).Prime}

lemma prime_pair_normalized_count (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    (((range (2^(128*m))).filter (fun q => q ∈ primePairSet a)).card : ℝ)/(2 : ℝ)^(128*m) ≤
      (2 / (((Nat.totient (2*a) : ℝ)/(2*a) * Real.log 2)^2))/(m : ℝ)^2 +
        3*(1/2 : ℝ)^m := by
  have h := Sieve.prime_pair_explicit_bound (2^(128*m)) a m ha hm
  have hN : (0 : ℝ) < (2 : ℝ)^(128*m) := by positivity
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hφ : (0 : ℝ) < Nat.totient (2*a) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < 2*a)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmain :
      (2 * ((2^(128*m) : ℕ) : ℝ) /
        (((Nat.totient (2*a) : ℝ)/(2*a) * m * Real.log 2)^2)) / (2 : ℝ)^(128*m) =
      (2 / (((Nat.totient (2*a) : ℝ)/(2*a) * Real.log 2)^2))/(m : ℝ)^2 := by
    push_cast only [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hd := div_le_div_of_nonneg_right h hN.le
  have hc : ((range (2^(128*m))).filter (fun q => q ∈ primePairSet a)).card =
      ((range (2^(128*m))).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card := by
    congr 1
    ext q
    simp only [mem_filter, primePairSet, Set.mem_setOf_eq]
  rw [hc]
  rw [add_div, add_div, add_div, hmain] at hd
  have he := pair_sieve_normalized_error m
  rw [add_div, add_div] at he
  have hfinal := _root_.add_le_add (le_refl (2 / (((Nat.totient (2*a) : ℝ)/(2*a) * Real.log 2)^2)/(m : ℝ)^2)) he
  rw [add_assoc, add_assoc] at hd
  exact hd.trans (by simpa only [add_assoc] using hfinal)

/-- Brun-type reciprocal convergence for q and a*q+1 at each fixed a>0. -/
theorem summable_prime_pair_reciprocal (a : ℕ) (ha : 0 < a) :
    Summable ((primePairSet a).indicator (fun q : ℕ => 1/(q : ℝ))) := by
  apply summable_reciprocal_of_summable_geometric_count (primePairSet a) 128 (by decide)
  apply (summable_nat_add_iff 1).mp
  let C : ℝ := 2 / (((Nat.totient (2*a) : ℝ)/(2*a) * Real.log 2)^2)
  have hp : Summable (fun m : ℕ => 1/(m : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  have hg : Summable (fun m : ℕ => (1/2 : ℝ)^m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have H := (((summable_nat_add_iff 1).mpr hp).mul_left C).add
    (((summable_nat_add_iff 1).mpr hg).mul_left 3)
  apply H.of_nonneg_of_le (fun m => div_nonneg (Nat.cast_nonneg _) (by positivity))
  intro m
  simpa only [Function.comp_def, mul_one_div, C] using
    prime_pair_normalized_count a (m+1) ha (by omega)

/-- The locally admissible pattern used to test pointwise contraction is
unconditionally reciprocal-summable. This does not imply it is finite. -/
theorem summable_canonical_test_pattern_reciprocal :
    Summable (({q : ℕ | q.Prime ∧ ∀ a ∈ canonicalTestCoefficients, (a*q+1).Prime} : Set ℕ).indicator
      (fun q : ℕ => 1/(q : ℝ))) := by
  apply (summable_prime_pair_reciprocal 2 (by decide)).of_nonneg_of_le
    (fun q => Set.indicator_nonneg
      (fun q _ => div_nonneg (by norm_num) (Nat.cast_nonneg q)) q)
  intro q
  by_cases hq : q ∈ ({q : ℕ | q.Prime ∧ ∀ a ∈ canonicalTestCoefficients, (a*q+1).Prime} : Set ℕ)
  · have hp : q ∈ primePairSet 2 := ⟨hq.1, hq.2 2 (by decide)⟩
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hq]
    exact Set.indicator_nonneg (fun q _ => div_nonneg (by norm_num) (Nat.cast_nonneg q)) q

/-- The larger primes in a fixed-cofactor prime pair. -/
noncomputable def primePairParentSet (a : ℕ) : Set ℕ :=
  (fun q : ℕ => a*q+1) '' primePairSet a

theorem summable_prime_pair_parent_reciprocal (a : ℕ) (ha : 0 < a) :
    Summable ((primePairParentSet a).indicator (fun p : ℕ => 1/(p : ℝ))) := by
  have hinj : Function.Injective (fun q : ℕ => a*q+1) := by
    intro q r heq
    exact Nat.eq_of_mul_eq_mul_left ha (Nat.add_right_cancel heq)
  have hsupp : ∀ p : ℕ, p ∉ Set.range (fun q : ℕ => a*q+1) →
      (primePairParentSet a).indicator (fun p : ℕ => 1/(p : ℝ)) p = 0 := by
    intro p hp
    apply Set.indicator_of_notMem
    intro h
    obtain ⟨q, _, heq⟩ := h
    exact hp ⟨q, heq⟩
  apply (hinj.summable_iff hsupp).mp
  apply (summable_prime_pair_reciprocal a ha).of_nonneg_of_le
    (fun q => Set.indicator_nonneg
      (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) (a*q+1))
  intro q
  change (primePairParentSet a).indicator (fun p : ℕ => 1/(p : ℝ)) (a*q+1) ≤ _
  rw [primePairParentSet, Set.indicator_image hinj]
  by_cases hq : q ∈ primePairSet a
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    apply one_div_le_one_div_of_le (by exact_mod_cast hq.1.pos)
    have hle : q ≤ a*q+1 := (Nat.le_mul_of_pos_left q ha).trans (Nat.le_succ _)
    exact_mod_cast hle
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

noncomputable def boundedCofactorParentSet (A : ℕ) : Set ℕ :=
  {p | ∃ a ∈ Icc 1 A, p ∈ primePairParentSet a}

/-- All parents with cofactors in a fixed bounded range have finite total
reciprocal mass. The cofactor bound A may be arbitrarily large, but is fixed. -/
theorem summable_bounded_cofactor_parent_reciprocal (A : ℕ) :
    Summable ((boundedCofactorParentSet A).indicator (fun p : ℕ => 1/(p : ℝ))) := by
  have H := summable_sum (s := Icc 1 A) (fun a ha =>
    summable_prime_pair_parent_reciprocal a (mem_Icc.mp ha).1)
  apply H.of_nonneg_of_le (fun p => Set.indicator_nonneg
    (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p)
  intro p
  by_cases hp : p ∈ boundedCofactorParentSet A
  · obtain ⟨a, ha, hpa⟩ := hp
    rw [Set.indicator_of_mem (show p ∈ boundedCofactorParentSet A from ⟨a, ha, hpa⟩)]
    have h := single_le_sum
      (f := fun a : ℕ => (primePairParentSet a).indicator (fun p : ℕ => 1/(p : ℝ)) p)
      (fun a (_ : a ∈ Icc 1 A) => Set.indicator_nonneg
      (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p) ha
    dsimp only at h
    rw [Set.indicator_of_mem hpa] at h
    exact h
  · rw [Set.indicator_of_notMem hp]
    exact sum_nonneg (fun a _ => Set.indicator_nonneg
      (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p)

lemma bounded_canonical_parent_mem (k A p q : ℕ) (hq : q.Prime)
    (hp : p ∈ canonicalRoughParentFinset k q) (hbound : p ≤ A*q+1) :
    p ∈ boundedCofactorParentSet A := by
  simp only [canonicalRoughParentFinset, mem_filter] at hp
  obtain ⟨_, hp, hqd, _, _⟩ := hp
  have hp0 : 0 < p-1 := by have := hp.two_le; omega
  let a := (p-1)/q
  have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hp0 hqd) hq.pos
  have heq : a*q = p-1 := Nat.div_mul_cancel hqd
  have hpEq : a*q+1 = p := by have := hp.two_le; omega
  have haA : a ≤ A := Nat.le_of_mul_le_mul_right (by omega : a*q ≤ A*q) hq.pos
  exact ⟨a, mem_Icc.mpr ⟨ha, haA⟩, q, ⟨hq, hpEq.symm ▸ hp⟩, hpEq⟩

/-- Restricting canonical parents to any fixed cofactor bound leaves a
reciprocal-summable set, uniformly in the choice of the root parameter k. -/
theorem summable_bounded_canonical_parent_reciprocal (k A : ℕ) :
    Summable (({p : ℕ | ∃ q : ℕ, q.Prime ∧ p ∈ canonicalRoughParentFinset k q ∧
      p ≤ A*q+1} : Set ℕ).indicator (fun p : ℕ => 1/(p : ℝ))) := by
  apply (summable_bounded_cofactor_parent_reciprocal A).of_nonneg_of_le
    (fun p => Set.indicator_nonneg
      (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p)
  intro p
  by_cases hp : p ∈ ({p : ℕ | ∃ q : ℕ, q.Prime ∧ p ∈ canonicalRoughParentFinset k q ∧
      p ≤ A*q+1} : Set ℕ)
  · obtain ⟨q, hq, hpq, hbound⟩ := hp
    have hpB := bounded_canonical_parent_mem k A p q hq hpq hbound
    rw [Set.indicator_of_mem (show p ∈ ({p : ℕ | ∃ q : ℕ, q.Prime ∧
      p ∈ canonicalRoughParentFinset k q ∧ p ≤ A*q+1} : Set ℕ) from ⟨q, hq, hpq, hbound⟩),
      Set.indicator_of_mem hpB]
  · rw [Set.indicator_of_notMem hp]
    exact Set.indicator_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p)) p

end Erdos821
