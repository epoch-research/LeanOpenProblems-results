import Submission.Density

/-!
# Propagating power-sparse sets along large predecessor factors

A set with a convergent power-weighted series remains power-sparse after any
fixed number of large-child steps. This is an auxiliary counting result,
not a proof or disproof of Erdos 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 3000000

/-- Positive integers with a divisor in A whose kth power covers the integer. -/
def largeDivisorLift (k : ℕ) (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ q ∈ A, 0 < q ∧ q ∣ n ∧ n ≤ q^k}

lemma sum_largeDivisorLift_le (k : ℕ) (A : Set ℕ) (b s u : ℝ)
    (hsu : s ≤ u) (hu : 1 < u) (hexp : (k : ℝ) * (u-s) - u ≤ -b)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) (F : Finset ℕ) :
    (∑ n ∈ F, (largeDivisorLift k A).indicator (fun n : ℕ => (n : ℝ)^(-s)) n) ≤
      (∑' a : ℕ, (a : ℝ)^(-u)) *
        ∑' q : ℕ, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q := by
  let C : ℝ := (∑' a : ℕ, (a : ℝ)^(-u)) *
    ∑' q : ℕ, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q
  let D := F.filter (fun n => n ∈ largeDivisorLift k A)
  let Q := D.biUnion (fun n => n.divisors.filter (fun q => q ∈ A ∧ n ≤ q^k))
  have hD (n : ℕ) (hn : n ∈ D) : 0 < n := (mem_filter.mp hn).2.1
  have hQ (q : ℕ) (hq : q ∈ Q) : 0 < q ∧ q ∈ A := by
    obtain ⟨n, hn, hq⟩ := mem_biUnion.mp hq
    exact ⟨Nat.pos_of_mem_divisors (mem_filter.mp hq).1, (mem_filter.mp hq).2.1⟩
  have hcover (n : ℕ) (hn : n ∈ D) : ∃ q ∈ Q, q ∣ n ∧ n ≤ q^k := by
    obtain ⟨hnF, hn0, q, hqA, hq0, hqn, hnq⟩ := mem_filter.mp hn
    refine ⟨q, mem_biUnion.mpr ⟨n, hn, ?_⟩, hqn, hnq⟩
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqn, hn0.ne'⟩, hqA, hnq⟩
  have hsumQ : (∑ q ∈ Q, (q : ℝ)^((k : ℝ)*(u-s)-u)) ≤
      ∑' q : ℕ, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q := by
    calc
      _ ≤ ∑ q ∈ Q, A.indicator (fun q : ℕ => (q : ℝ)^(-b)) q := by
        apply sum_le_sum
        intro q hq
        rw [Set.indicator_of_mem (hQ q hq).2]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (hQ q hq).1) hexp
      _ ≤ _ := Summable.sum_le_tsum _
        (fun q _ => Set.indicator_nonneg (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) _) q) H
  have hC0 : 0 ≤ ∑' a : ℕ, (a : ℝ)^(-u) :=
    tsum_nonneg (fun a => Real.rpow_nonneg (Nat.cast_nonneg a) _)
  calc
    _ = ∑ n ∈ D, (n : ℝ)^(-s) := by
      simp only [D, sum_filter, Set.indicator_apply]
    _ ≤ (∑' a : ℕ, (a : ℝ)^(-u)) * ∑ q ∈ Q, (q : ℝ)^((k : ℝ)*(u-s)-u) :=
      rough_divisor_weight_sum D Q k s u hsu hu hD (fun q hq => (hQ q hq).1) hcover
    _ ≤ C := mul_le_mul_of_nonneg_left hsumQ hC0

lemma summable_largeDivisorLift (k : ℕ) (A : Set ℕ) (b s u : ℝ)
    (hsu : s ≤ u) (hu : 1 < u) (hexp : (k : ℝ) * (u-s) - u ≤ -b)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    Summable ((largeDivisorLift k A).indicator (fun n : ℕ => (n : ℝ)^(-s))) := by
  exact summable_of_sum_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
    (sum_largeDivisorLift_le k A b s u hsu hu hexp H)

/-- Increasing the exponent preserves summability; the term at zero is
handled by shifting the natural-number series. -/
lemma summable_set_power_mono (A : Set ℕ) (b s : ℝ) (hbs : b ≤ s)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-s))) := by
  apply (summable_nat_add_iff 1).mp
  apply ((summable_nat_add_iff 1).mpr H).of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (n+1))
  intro n
  by_cases hn : n+1 ∈ A
  · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
      (by linarith)
  · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]

/-- A prime whose predecessor has a polynomially large prime divisor in A. -/
def largeChildParents (k : ℕ) (A : Set ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ q ∈ A, q.Prime ∧ q ∣ p-1 ∧ p-1 ≤ q^k}

lemma summable_largeChildParents (k : ℕ) (A : Set ℕ) (b s u : ℝ)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : 1 < u)
    (hexp : (k : ℝ) * (u-s) - u ≤ -b)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    Summable ((largeChildParents k A).indicator (fun p : ℕ => (p : ℝ)^(-s))) := by
  have HL := summable_largeDivisorLift k A b s u hsu hu hexp H
  apply (summable_nat_add_iff 1).mp
  apply HL.of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) (n+1))
  intro n
  by_cases hn : n+1 ∈ largeChildParents k A
  · have hnmem := hn
    obtain ⟨hp, q, hqA, hq, hqn, hnq⟩ := hn
    simp only [Nat.add_sub_cancel] at hqn hnq
    have hn0 : 0 < n := by have := hp.two_le; omega
    have hnL : n ∈ largeDivisorLift k A := ⟨hn0, q, hqA, hq.pos, hqn, hnq⟩
    rw [Set.indicator_of_mem hnmem, Set.indicator_of_mem hnL]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn0)
      (by exact_mod_cast (Nat.le_succ n)) (by linarith)
  · rw [Set.indicator_of_notMem hn]
    exact Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n

/-- One step retains an explicit positive gap below exponent one. -/
noncomputable def nextLargeChildExponent (k : ℕ) (b : ℝ) : ℝ :=
  1 - (1-b)/(2*(k : ℝ))

lemma nextLargeChildExponent_bounds (k : ℕ) (hk : 1 ≤ k) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) :
    b ≤ nextLargeChildExponent k b ∧
      0 ≤ nextLargeChildExponent k b ∧ nextLargeChildExponent k b < 1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 2*(k : ℝ) := by linarith
  have he : 0 < (1-b)/(2*(k : ℝ)) := div_pos (by linarith) hd
  have he' : (1-b)/(2*(k : ℝ)) ≤ 1-b := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  dsimp [nextLargeChildExponent]
  constructor
  · linarith
  constructor <;> linarith

lemma summable_largeChildParents_next (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ)
    (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    Summable ((largeChildParents k A).indicator
      (fun p : ℕ => (p : ℝ)^(-nextLargeChildExponent k b))) := by
  let e : ℝ := (1-b)/(2*(k : ℝ))
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have he : 0 < e := div_pos (by linarith) (mul_pos (by norm_num) hkR)
  have hid : 2*(k : ℝ)*e = 1-b := by dsimp [e]; field_simp
  apply summable_largeChildParents k A b (nextLargeChildExponent k b) (1+e)
    (nextLargeChildExponent_bounds k hk b hb hb1).2.1
    (by change 1-e ≤ 1+e; linarith) (by linarith) ?_ H
  change (k : ℝ)*((1+e)-(1-e))-(1+e) ≤ -b
  nlinarith only [hid, he]

/-- All points from which A is reached in at most L large-child steps. -/
def largeChildLayer (k : ℕ) (A : Set ℕ) : ℕ → Set ℕ
  | 0 => A
  | L+1 => largeChildLayer k A L ∪ largeChildParents k (largeChildLayer k A L)

noncomputable def largeChildLayerExponent (k : ℕ) (b : ℝ) : ℕ → ℝ
  | 0 => b
  | L+1 => nextLargeChildExponent k (largeChildLayerExponent k b L)

lemma largeChildLayerExponent_bounds (k : ℕ) (hk : 1 ≤ k) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1) (L : ℕ) :
    0 ≤ largeChildLayerExponent k b L ∧ largeChildLayerExponent k b L < 1 := by
  induction L with
  | zero => exact ⟨hb, hb1⟩
  | succ L ih => exact (nextLargeChildExponent_bounds k hk _ ih.1 ih.2).2

lemma largeChildLayerExponent_eq (k : ℕ) (hk : 1 ≤ k) (b : ℝ) (L : ℕ) :
    largeChildLayerExponent k b L = 1-(1-b)/(2*(k : ℝ))^L := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  induction L with
  | zero => simp [largeChildLayerExponent]
  | succ L ih =>
    rw [largeChildLayerExponent, nextLargeChildExponent, ih, pow_succ]
    field_simp
    ring

lemma summable_set_power_union (A B : Set ℕ) (s : ℝ)
    (HA : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-s))))
    (HB : Summable (B.indicator (fun n : ℕ => (n : ℝ)^(-s)))) :
    Summable ((A ∪ B).indicator (fun n : ℕ => (n : ℝ)^(-s))) := by
  apply (HA.add HB).of_nonneg_of_le
    (fun n => Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n)
  intro n
  change (A ∪ B).indicator (fun n : ℕ => (n : ℝ)^(-s)) n ≤
    A.indicator (fun n : ℕ => (n : ℝ)^(-s)) n +
      B.indicator (fun n : ℕ => (n : ℝ)^(-s)) n
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;>
    simp [hA, hB, Real.rpow_nonneg]

/-- Every fixed-depth ancestor set still has a convergent series below one. -/
theorem summable_largeChildLayer (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ) (b : ℝ)
    (hb : 0 ≤ b) (hb1 : b < 1)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) (L : ℕ) :
    Summable ((largeChildLayer k A L).indicator
      (fun p : ℕ => (p : ℝ)^(-largeChildLayerExponent k b L))) := by
  induction L with
  | zero => exact H
  | succ L ih =>
    have hL := largeChildLayerExponent_bounds k hk b hb hb1 L
    apply summable_set_power_union
    · exact summable_set_power_mono _ _ _
        (nextLargeChildExponent_bounds k hk _ hL.1 hL.2).1 ih
    · exact summable_largeChildParents_next k hk _ _ hL.1 hL.2 ih

lemma not_summable_prime_complement_power_one (A : Set ℕ) (b : ℝ) (hb : b ≤ 1)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    ¬Summable (({p : ℕ | p.Prime ∧ p ∉ A} : Set ℕ).indicator
      (fun p : ℕ => (p : ℝ)^(-(1 : ℝ)))) := by
  intro HB
  have HA := summable_set_power_mono A b 1 hb H
  have HU := summable_set_power_union A {p : ℕ | p.Prime ∧ p ∉ A} 1 HA HB
  apply not_summable_one_div_on_primes
  have HP : Summable (({p : ℕ | p.Prime} : Set ℕ).indicator
      (fun p : ℕ => (p : ℝ)^(-(1 : ℝ)))) := by
    apply HU.of_nonneg_of_le
      (fun p => Set.indicator_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) p)
    intro p
    by_cases hp : p.Prime
    · have hmem : p ∈ A ∪ {p : ℕ | p.Prime ∧ p ∉ A} := by
        by_cases hA : p ∈ A
        · exact Or.inl hA
        · exact Or.inr ⟨hp, hA⟩
      rw [Set.indicator_of_mem (show p ∈ {p : ℕ | p.Prime} from hp),
        Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℕ | p.Prime} from hp)]
      exact Set.indicator_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _) p
  simpa only [Real.rpow_neg_one, one_div] using HP

lemma infinite_primes_outside_summable_set (A : Set ℕ) (b : ℝ) (hb : b ≤ 1)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) :
    {p : ℕ | p.Prime ∧ p ∉ A}.Infinite := by
  intro hfin
  apply not_summable_prime_complement_power_one A b hb H
  apply summable_of_finite_support
  exact hfin.subset Set.support_indicator_subset

/-- There are arbitrarily large primes that do not reach A within any given
fixed number of large-child steps. This is not a uniform assertion as L grows. -/
theorem infinite_primes_outside_largeChildLayer (k : ℕ) (hk : 1 ≤ k)
    (A : Set ℕ) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) (L : ℕ) :
    {p : ℕ | p.Prime ∧ p ∉ largeChildLayer k A L}.Infinite := by
  exact infinite_primes_outside_summable_set _ _
    (largeChildLayerExponent_bounds k hk b hb hb1 L).2.le
    (summable_largeChildLayer k hk A b hb hb1 H L)

/-- The remaining primes even retain reciprocal divergence. -/
theorem not_summable_reciprocal_outside_largeChildLayer (k : ℕ) (hk : 1 ≤ k)
    (A : Set ℕ) (b : ℝ) (hb : 0 ≤ b) (hb1 : b < 1)
    (H : Summable (A.indicator (fun q : ℕ => (q : ℝ)^(-b)))) (L : ℕ) :
    ¬Summable (({p : ℕ | p.Prime ∧ p ∉ largeChildLayer k A L} : Set ℕ).indicator
      (fun p : ℕ => 1/(p : ℝ))) := by
  simpa only [Real.rpow_neg_one, one_div] using
    not_summable_prime_complement_power_one _ _
      (largeChildLayerExponent_bounds k hk b hb hb1 L).2.le
      (summable_largeChildLayer k hk A b hb hb1 H L)

lemma base_subset_largeChildLayer (k : ℕ) (A : Set ℕ) (L : ℕ) :
    A ⊆ largeChildLayer k A L := by
  induction L with
  | zero => exact Set.Subset.refl _
  | succ L ih => exact ih.trans Set.subset_union_left

/-- A path with L strict large-child edges, avoiding A at every vertex. -/
def largeChildAvoidingPath (k : ℕ) (A : Set ℕ) : ℕ → ℕ → Prop
  | 0, p => p.Prime ∧ p ∉ A
  | L+1, p => p.Prime ∧ p ∉ A ∧ ∃ q : ℕ,
      q ∣ p-1 ∧ p-1 < q^k ∧ largeChildAvoidingPath k A L q

lemma outside_largeChildLayer_has_avoiding_path (k : ℕ) (A : Set ℕ)
    (hsplit : ∀ p : ℕ, p.Prime → p ∉ A →
      ∃ q : ℕ, q.Prime ∧ q ∣ p-1 ∧ p-1 < q^k)
    (L p : ℕ) (hp : p.Prime) (hpL : p ∉ largeChildLayer k A L) :
    largeChildAvoidingPath k A L p := by
  induction L generalizing p with
  | zero => exact ⟨hp, hpL⟩
  | succ L ih =>
    have hpA : p ∉ A := fun h => hpL (base_subset_largeChildLayer k A (L+1) h)
    obtain ⟨q, hq, hqd, hqsize⟩ := hsplit p hp hpA
    refine ⟨hp, hpA, q, hqd, hqsize, ih q hq ?_⟩
    intro hqL
    exact hpL (Or.inr ⟨hp, q, hqL, hq, hqd, hqsize.le⟩)

end Erdos821
