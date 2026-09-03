import Submission.PrimeFamily
import Submission.PrimeLog
import Submission.LogKernel
import Submission.Reduction

/-!
# The quadratic prime-support bound

The prime-power mixed-orbit families split the sum kernel into a cross kernel
and a positive semidefinite self-opposite baseline.  The logarithm of the full
sum kernel is conditionally negative semidefinite.  Comparing sums with positive
absolute differences gives the strict separation required by the signed-family
bound.  Removing zero then yields a uniform quadratic cardinality bound.
-/

open scoped BigOperators
open Finset

namespace Erdos126Arithmetic

noncomputable section

open Erdos126Kernel Erdos126PrimeFamily Erdos126PrimeLog

variable {V : Type*} [Fintype V]

/-- Self-opposite residue classes give the baseline at one prime-power level. -/
def baselineLevel (a : V → ℕ) (p k : ℕ) (i j : V) : ℝ :=
  if residue a p k i = residue a p k j ∧
    residue a p k i = -residue a p k i then 1 else 0

/-- The weighted, truncated baseline at a single prime. -/
def localBaseline (a : V → ℕ) (p K : ℕ) (i j : V) : ℝ :=
  Real.log p * ∑ k ∈ range K, baselineLevel a p k i j

/-- The cross kernel indexed by the chosen primes. -/
def C (a : V → ℕ) (S : Finset ℕ) (K : ℕ) : V → V → ℝ :=
  crossKernel (fun p : S => kernel a p K)
    (fun p i => Erdos126PrimeCode.primeColor p (a i))

/-- The retained same-side kernel. -/
def R (a : V → ℕ) (S : Finset ℕ) (K : ℕ) : V → V → ℝ :=
  sameKernel (fun p : S => kernel a p K)
    (fun p i => Erdos126PrimeCode.primeColor p (a i))

/-- The baseline summed over all chosen primes. -/
def B (a : V → ℕ) (S : Finset ℕ) (K : ℕ) (i j : V) : ℝ :=
  ∑ p : S, localBaseline a p K i j

omit [Fintype V] in
lemma residue_eq_iff_dvd_dist (a : V → ℕ) (p k : ℕ) (i j : V) :
    residue a p k i = residue a p k j ↔ p ^ (k + 1) ∣ Nat.dist (a i) (a j) := by
  by_cases h : a i ≤ a j
  · rw [Nat.dist_eq_sub_of_le h]
    simpa only [Nat.cast_sub h, sub_eq_zero, residue, eq_comm] using
      (ZMod.natCast_eq_zero_iff (a j - a i) (p ^ (k + 1)))
  · have h' : a j ≤ a i := by omega
    rw [Nat.dist_eq_sub_of_le_right h']
    simpa only [Nat.cast_sub h', sub_eq_zero, residue] using
      (ZMod.natCast_eq_zero_iff (a i - a j) (p ^ (k + 1)))

omit [Fintype V] in
lemma cross_add_baselineLevel (a : V → ℕ) (p k : ℕ) (i j : V) :
    (if residue a p k i = -residue a p k j ∧
        residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0) +
      baselineLevel a p k i j =
      if p ^ (k + 1) ∣ a i + a j then 1 else 0 := by
  simp only [← residue_eq_neg_iff_dvd]
  unfold baselineLevel
  by_cases hs : residue a p k i = -residue a p k i
  · have he : residue a p k i = -residue a p k j ↔
        residue a p k i = residue a p k j := by
      constructor
      · intro h
        have h' := congrArg Neg.neg h
        simpa only [neg_neg, ← hs] using h'
      · intro h
        simpa only [← h] using hs
    rw [if_neg (fun h => h.2 hs)]
    have hb : (residue a p k i = residue a p k j ∧
        residue a p k i = -residue a p k i) ↔
        residue a p k i = -residue a p k j :=
      ⟨fun h => he.mpr h.1, fun h => ⟨he.mp h, hs⟩⟩
    simp only [hb, zero_add]
  · have hb : ¬ (residue a p k i = residue a p k j ∧
        residue a p k i = -residue a p k i) := fun h => hs h.2
    rw [if_neg hb]
    simp only [and_iff_left hs, add_zero]

omit [Fintype V] in
lemma same_add_baselineLevel (a : V → ℕ) (p k : ℕ) (i j : V) :
    (if residue a p k i = residue a p k j ∧
        residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0) +
      baselineLevel a p k i j =
      if p ^ (k + 1) ∣ Nat.dist (a i) (a j) then 1 else 0 := by
  simp only [← residue_eq_iff_dvd_dist]
  unfold baselineLevel
  by_cases hs : residue a p k i = -residue a p k i
  · rw [if_neg (fun h => h.2 hs)]
    simp only [and_iff_left hs, zero_add]
  · have hb : ¬ (residue a p k i = residue a p k j ∧
        residue a p k i = -residue a p k i) := fun h => hs h.2
    rw [if_neg hb]
    simp only [and_iff_left hs, add_zero]

lemma local_cross_add_baseline (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) =
        Erdos126PrimeCode.primeColor p (a j) then 0 else kernel a p K i j) +
      localBaseline a p K i j = Real.log p * countPowers p K (a i + a j) := by
  rw [kernel_cross_eq a p K hp ha]
  unfold localBaseline countPowers
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  exact cross_add_baselineLevel a p k i j

lemma local_same_add_baseline_le (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) =
        Erdos126PrimeCode.primeColor p (a j) then kernel a p K i j else 0) +
      localBaseline a p K i j ≤
      Real.log p * countPowers p K (Nat.dist (a i) (a j)) := by
  calc
    _ ≤ (Real.log p * ∑ k ∈ range K,
        if residue a p k i = residue a p k j ∧
          residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0) +
        localBaseline a p K i j :=
      add_le_add (kernel_same_le a p K hp ha i j) le_rfl
    _ = _ := by
      unfold localBaseline countPowers
      rw [← mul_add, ← sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro k hk
      exact same_add_baselineLevel a p k i j

lemma qform_smul (c : ℝ) (M : V → V → ℝ) (z : V → ℝ) :
    qform (fun i j => c * M i j) z = c * qform M z := by
  unfold qform
  simp only [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma localBaseline_psd (a : V → ℕ) (p K : ℕ) (z : V → ℝ) :
    0 ≤ qform (localBaseline a p K) z := by
  unfold localBaseline
  rw [qform_smul, qform_sum]
  apply mul_nonneg (Real.log_natCast_nonneg p)
  apply sum_nonneg
  intro k hk
  exact Erdos126Orbit.baseline_psd (residue a p k) z

lemma B_psd (a : V → ℕ) (S : Finset ℕ) (K : ℕ) (z : V → ℝ) :
    0 ≤ qform (B a S K) z := by
  unfold B
  rw [qform_sum]
  exact sum_nonneg (fun p _ => localBaseline_psd a p K z)

/-- Cross cancellation plus the baseline counts all supported prime powers. -/
lemma C_add_B_eq_sum (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0) (i j : V) :
    C a S K i j + B a S K i j =
      ∑ p ∈ S, Real.log p * countPowers p K (a i + a j) := by
  unfold C B crossKernel
  rw [← sum_add_distrib]
  calc
    _ = ∑ p : S, Real.log (p : ℕ) * countPowers p K (a i + a j) := by
      apply sum_congr rfl
      intro p hp
      exact local_cross_add_baseline a p K (hS p p.property) ha i j
    _ = _ := sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) * countPowers p K (a i + a j))

lemma C_add_B_eq_log (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (hK : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ K)
    (i j : V) (hij : i ≠ j) :
    C a S K i j + B a S K i j = Real.log (a i + a j : ℕ) := by
  rw [C_add_B_eq_sum a S K hS ha]
  exact sum_log_count_eq S hS K (a i + a j) (by have := ha i; omega)
    (hsupp i j hij) (fun p hp => hK p hp i j)

omit [Fintype V] in
lemma B_diag_le (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0) (i : V) :
    B a S K i i ≤ Real.log (2 * a i : ℕ) := by
  have heq : B a S K i i =
      ∑ p ∈ S, Real.log p * countPowers p K (2 * a i) := by
    unfold B localBaseline baselineLevel countPowers
    simp only [true_and, residue_eq_self_neg_iff_dvd_twice]
    exact sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) *
      ∑ k ∈ range K, if p ^ (k + 1) ∣ 2 * a i then (1 : ℝ) else 0)
  rw [heq]
  exact sum_log_count_le S hS K (2 * a i) (mul_ne_zero (by decide) (ha i))

lemma R_add_B_le_log_dist (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (i j : V) (hij : a i ≠ a j) :
    R a S K i j + B a S K i j ≤ Real.log (Nat.dist (a i) (a j) : ℕ) := by
  unfold R B sameKernel
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ p : S, Real.log (p : ℕ) * countPowers p K (Nat.dist (a i) (a j)) := by
      apply sum_le_sum
      intro p hp
      exact local_same_add_baseline_le a p K (hS p p.property) ha i j
    _ = ∑ p ∈ S, Real.log p * countPowers p K (Nat.dist (a i) (a j)) :=
      sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) * countPowers p K (Nat.dist (a i) (a j)))
    _ ≤ _ := sum_log_count_le S hS K _ (Nat.dist_pos_of_ne hij).ne'

/-- Conditional negativity survives subtracting the baseline and the missing
nonnegative diagonal prime contributions. -/
lemma C_cnd (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (hK : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ K) :
    CND (C a S K) := by
  intro z hz
  have hlog := Erdos126Log.log_add_cnd (fun i => (a i : ℝ)) z
    (fun i => by dsimp; exact_mod_cast Nat.pos_of_ne_zero (ha i)) hz
  have hbase := B_psd a S K z
  have hineq : qform (C a S K) z + qform (B a S K) z ≤
      ∑ i, ∑ j, z i * z j * Real.log ((a i : ℝ) + (a j : ℝ)) := by
    calc
      _ = ∑ i, ∑ j, z i * z j * (C a S K i j + B a S K i j) := by
        simp only [qform, mul_add, sum_add_distrib]
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        apply sum_le_sum
        intro j hj
        by_cases he : i = j
        · subst j
          have hb : B a S K i i ≤ Real.log ((a i : ℝ) + (a i : ℝ)) := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using B_diag_le a S K hS ha i
          have hc : C a S K i i = 0 := crossKernel_diag _ _ i
          rw [hc, zero_add]
          exact mul_le_mul_of_nonneg_left hb (mul_self_nonneg _)
        · rw [C_add_B_eq_log a S K hS ha hsupp hK i j he]
          simp only [Nat.cast_add, le_refl]
  linarith

/-- A positive pair sum is larger than the absolute difference, even after
retaining only the chosen prime powers of the difference. -/
lemma R_lt_C (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hinj : Function.Injective a)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (hK : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ K)
    (i j : V) (hij : i ≠ j) : R a S K i j < C a S K i j := by
  have hne : a i ≠ a j := fun h => hij (hinj h)
  have hdpos : 0 < Nat.dist (a i) (a j) := Nat.dist_pos_of_ne hne
  have hdlt : Nat.dist (a i) (a j) < a i + a j := by
    have hi := ha i
    have hj := ha j
    unfold Nat.dist
    omega
  have hlog : Real.log (Nat.dist (a i) (a j) : ℕ) < Real.log (a i + a j : ℕ) :=
    Real.log_lt_log (by exact_mod_cast hdpos) (by exact_mod_cast hdlt)
  have hsame := R_add_B_le_log_dist a S K hS ha i j hne
  have hcross := C_add_B_eq_log a S K hS ha hsupp hK i j hij
  linarith

/-- The quadratic bound for a positive injectively indexed set whose restricted
pair sums are supported on `S`. -/
theorem card_le_three_sq (a : V → ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hinj : Function.Injective a) (hn : 2 ≤ Fintype.card V)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    Fintype.card V ≤ 3 * S.card ^ 2 := by
  obtain ⟨K, hK⟩ := exists_factorization_cutoff a S
  have h := signed_family_card_bound
    (fun p : S => nodes a p K) (fun _ t => t.2) (fun p _ => Real.log (p : ℕ))
    (fun p i => Erdos126PrimeCode.primeColor p (a i)) hn
    (fun p _ _ => Real.log_natCast_nonneg p)
    (fun p => nodes_card_two_le a p K)
    (fun p => nodes_laminar a p K)
    (C_cnd a S K hS ha hsupp hK)
    (R_lt_C a S K hS ha hinj hsupp hK)
  have h' : (Fintype.card V : ℝ) ≤ 3 * (S.card : ℝ) ^ 2 := by
    simpa only [Fintype.card_coe] using h
  exact_mod_cast h'

/-- The uniform quadratic bound, including the harmless small sets and a
possible vertex zero. -/
theorem quadraticBound (A : Finset ℕ) :
    A.card ≤ 3 * (Erdos126Reduction.P A) ^ 2 + 2 := by
  classical
  let S := (Erdos126Reduction.sumProduct A).primeFactors
  change A.card ≤ 3 * S.card ^ 2 + 2
  have hcard : A.card ≤ (A.erase 0).card + 1 := by
    by_cases hzero : 0 ∈ A
    · exact (card_erase_add_one hzero).ge
    · rw [erase_eq_of_notMem hzero]
      omega
  by_cases hn : 2 ≤ (A.erase 0).card
  · have h : (A.erase 0).card ≤ 3 * S.card ^ 2 := by
      have hc := card_le_three_sq (fun i : A.erase 0 => (i : ℕ)) S
        (fun p hp => Nat.prime_of_mem_primeFactors hp)
        (fun i => (mem_erase.mp i.property).1)
        Subtype.val_injective (by simpa only [Fintype.card_coe] using hn)
        (by
          intro i j hij p hp
          have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
          have hprime := Nat.mem_primeFactors.mp hp
          exact Erdos126PrimeCode.prime_mem_sumProduct
            (mem_of_mem_erase i.property) (mem_of_mem_erase j.property)
            hne hprime.1 hprime.2.1)
      simpa only [Fintype.card_coe] using hc
    omega
  · omega

end

end Erdos126Arithmetic
