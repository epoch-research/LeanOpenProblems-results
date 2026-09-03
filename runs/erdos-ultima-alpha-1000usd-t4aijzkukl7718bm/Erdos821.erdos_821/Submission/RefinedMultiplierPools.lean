import Submission.PoolHyperbolicBound

/-!
# Fine dyadic partitions of a multiplier pool

The reciprocal main mass loses only 1+2^(-r), independently of the power
width of the original pool. There are L*2^r blocks, including empty ones.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

def multiplierLower (k r j : ℕ) : ℕ := (2^r+j)*2^(k-r)
def multiplierUpper (k r j : ℕ) : ℕ := (2^r+j+1)*2^(k-r)
noncomputable def refinedMultiplierPool (P : Finset ℕ) (k r j : ℕ) : Finset ℕ :=
  P.filter (fun c => multiplierLower k r j<c ∧ c ≤ multiplierUpper k r j)

lemma multiplierLower_pos (k r j : ℕ) : 0 < multiplierLower k r j := by
  unfold multiplierLower
  positivity

lemma multiplierLower_le_upper (k r j : ℕ) : multiplierLower k r j ≤ multiplierUpper k r j := by
  unfold multiplierLower multiplierUpper
  exact Nat.mul_le_mul_right _ (by omega)

lemma multiplierLower_lower (k r j : ℕ) (hrk : r ≤ k) : 2^k ≤ multiplierLower k r j := by
  have he : 2^r*2^(k-r)=(2 : ℕ)^k := by rw [← pow_add,Nat.add_sub_of_le hrk]
  rw [← he]
  exact Nat.mul_le_mul_right _ (by omega)

lemma multiplierUpper_upper (k r j : ℕ) (hj : j < 2^r) (hrk : r ≤ k) :
    multiplierUpper k r j ≤ 2^(k+1) := by
  have he : 2*2^r*2^(k-r)=(2 : ℕ)^(k+1) := by
    rw [mul_assoc,← pow_add,Nat.add_sub_of_le hrk,pow_succ]
    ring
  rw [← he]
  exact Nat.mul_le_mul_right _ (by omega)

lemma multiplierUpper_ratio (k r j : ℕ) :
    (multiplierUpper k r j : ℝ) ≤ (1+1/(2 : ℝ)^r)*(multiplierLower k r j : ℝ) := by
  have hh := refined_interval_ratio (2^r) (2^(k-r)) j (multiplierUpper k r j) (by positivity) le_rfl
  simpa only [multiplierLower,Nat.cast_pow,Nat.cast_ofNat] using hh

lemma refinedMultiplierPool_subset (P : Finset ℕ) (k r j : ℕ) :
    refinedMultiplierPool P k r j ⊆ Icc 1 (multiplierUpper k r j) := by
  intro c hc
  obtain ⟨_,hl,hu⟩ := mem_filter.mp hc
  exact mem_Icc.mpr ⟨(Nat.succ_le_iff.mpr (multiplierLower_pos k r j)).trans hl.le,hu⟩

lemma refinedMultiplierPool_sum (P : Finset ℕ) (k r j : ℕ) (f : ℕ → ℝ) :
    (∑ c ∈ refinedMultiplierPool P k r j, f c) =
      ∑ c ∈ Icc (multiplierLower k r j+1) (multiplierUpper k r j), if c ∈ P then f c else 0 := by
  rw [← sum_filter]
  congr 1
  ext c
  simp only [refinedMultiplierPool,mem_filter,mem_Icc,Nat.lt_iff_add_one_le]
  tauto

lemma sum_refinedMultiplierPools_dyadic (P : Finset ℕ) (k r : ℕ) (hrk : r ≤ k) (f : ℕ → ℝ) :
    (∑ j ∈ range (2^r), ∑ c ∈ refinedMultiplierPool P k r j, f c) =
      ∑ c ∈ Icc (2^k+1) (2^(k+1)), if c ∈ P then f c else 0 := by
  simp_rw [refinedMultiplierPool_sum]
  unfold multiplierLower multiplierUpper
  rw [sum_step_intervals]
  have he : 2^r*2^(k-r)=(2 : ℕ)^k := by rw [← pow_add,Nat.add_sub_of_le hrk]
  have he' : (2^r+2^r)*2^(k-r)=(2 : ℕ)^(k+1) := by
    rw [add_mul,he,pow_succ]
    omega
  rw [he,he']

/-- The full wide pool is partitioned exactly, not just covered with an
uncontrolled multiplicity. -/
lemma sum_refinedMultiplierPools (P : Finset ℕ) (K L r : ℕ) (hrK : r ≤ K)
    (hP : ∀ c ∈ P, 2^K<c ∧ c ≤ 2^(K+L)) (f : ℕ → ℝ) :
    (∑ i ∈ range L, ∑ j ∈ range (2^r), ∑ c ∈ refinedMultiplierPool P (K+i) r j, f c) =
      ∑ c ∈ P, f c := by
  have he (i : ℕ) : (∑ j ∈ range (2^r), ∑ c ∈ refinedMultiplierPool P (K+i) r j, f c) =
      ∑ c ∈ Icc (2^(K+i)+1) (2^(K+i+1)), if c ∈ P then f c else 0 :=
    sum_refinedMultiplierPools_dyadic P (K+i) r (by omega) f
  simp_rw [he]
  rw [sum_monotone_interval_blocks _ (fun k => 2^k) (fun _ _ h => Nat.pow_le_pow_right (by decide) h)]
  rw [← sum_filter]
  congr 1
  ext c
  simp only [mem_filter,mem_Icc]
  constructor
  · exact fun h => h.2
  · intro hc
    exact ⟨hP c hc,hc⟩

lemma refinedMultiplierPool_mass (P : Finset ℕ) (k r j : ℕ) :
    ((refinedMultiplierPool P k r j).card : ℝ)/(multiplierLower k r j : ℝ) ≤
      (1+1/(2 : ℝ)^r)*(∑ c ∈ refinedMultiplierPool P k r j, (c : ℝ)⁻¹) := by
  rw [mul_sum]
  calc
    _ = ∑ _c ∈ refinedMultiplierPool P k r j, 1/(multiplierLower k r j : ℝ) := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro c hc
      have hm := (mem_filter.mp hc).2
      have hC : (0 : ℝ) < multiplierLower k r j := by exact_mod_cast multiplierLower_pos k r j
      have hc0 : (0 : ℝ)<c := hC.trans (Nat.cast_lt.mpr hm.1)
      have hratio : (c : ℝ) ≤ (1+1/(2 : ℝ)^r)*(multiplierLower k r j : ℝ) :=
        (Nat.cast_le.mpr hm.2).trans (multiplierUpper_ratio k r j)
      change 1/(multiplierLower k r j : ℝ) ≤ (1+1/(2 : ℝ)^r)/(c : ℝ)
      apply (le_div_iff₀ hc0).mpr
      have hh := (div_le_iff₀ hC).mpr hratio
      simpa only [div_eq_mul_inv,mul_comm,one_mul] using hh

lemma sum_refinedMultiplierPool_mass (P : Finset ℕ) (K L r : ℕ) (hrK : r ≤ K)
    (hP : ∀ c ∈ P, 2^K<c ∧ c ≤ 2^(K+L)) :
    (∑ i ∈ range L, ∑ j ∈ range (2^r),
      ((refinedMultiplierPool P (K+i) r j).card : ℝ)/(multiplierLower (K+i) r j : ℝ)) ≤
        (1+1/(2 : ℝ)^r)*(∑ c ∈ P, (c : ℝ)⁻¹) := by
  calc
    _ ≤ ∑ i ∈ range L, ∑ j ∈ range (2^r),
        (1+1/(2 : ℝ)^r)*(∑ c ∈ refinedMultiplierPool P (K+i) r j, (c : ℝ)⁻¹) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => refinedMultiplierPool_mass P (K+i) r j))
    _ = _ := by simp_rw [← mul_sum]; rw [sum_refinedMultiplierPools P K L r hrK hP]

lemma refinedMultiplierPool_ambient (X k r j : ℕ) :
    (multiplierUpper k r j : ℝ)*((X/multiplierLower k r j : ℕ) : ℝ) ≤
      (1+1/(2 : ℝ)^r)*(X : ℝ) := by
  have hC : (0 : ℝ) < multiplierLower k r j := by exact_mod_cast multiplierLower_pos k r j
  calc
    _ ≤ (multiplierUpper k r j : ℝ)*((X : ℝ)/(multiplierLower k r j : ℝ)) :=
      mul_le_mul_of_nonneg_left (Nat.cast_div_le (α := ℝ)) (Nat.cast_nonneg _)
    _ ≤ ((1+1/(2 : ℝ)^r)*(multiplierLower k r j : ℝ))*((X : ℝ)/(multiplierLower k r j : ℝ)) :=
      mul_le_mul_of_nonneg_right (multiplierUpper_ratio k r j) (by positivity)
    _ = _ := by field_simp

end Erdos821.AnalyticSieve
