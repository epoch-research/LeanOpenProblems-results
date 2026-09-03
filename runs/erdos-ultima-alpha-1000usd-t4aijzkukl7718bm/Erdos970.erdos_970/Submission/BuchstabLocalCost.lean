import Submission.BuchstabScaledSource
import Submission.PrimeSetMertens

/-! Finite-prefix bounds for complete refinement errors. Summability of the
infinite prime sequence is unnecessary: the error is linear in the divisor
level and depends on the reciprocal sum of the actual finite reference prefix. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real

lemma lowerErrorStep_le_linear_local (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (E : ℕ → ℝ → ℝ) (B Z : ℝ) (hB : 1 ≤ B) (hZ : 0 ≤ Z)
    (hq : ∀ i, 0 ≤ q i) (K : ℕ) (hsum : ∀ k ≤ K, (∑ i : Fin k, q i.val) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hE : ∀ k ≤ K, ∀ D, 1 ≤ D → E k D ≤ B*D)
    (k : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep E k D ≤ B*(1+Z)*D := by
  classical
  unfold lowerErrorStep
  split_ifs with hkeepk
  · obtain ⟨hD1,hchild⟩ := hkeep k D hkeepk
    have hs : (∑ i : Fin k, E i.val (D*q i.val)) ≤ B*D*Z := by
      calc
        _ ≤ ∑ i : Fin k, B*(D*q i.val) := sum_le_sum (fun i _ =>
          hE i.val (i.isLt.le.trans hk) _ (hchild i.val i.isLt))
        _ = B*D*(∑ i : Fin k, q i.val) := by rw [mul_sum]; apply sum_congr rfl; intro i hi; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hsum k hk) (by positivity)
    have hBD : 1 ≤ B*D := one_le_mul_of_one_le_of_one_le hB hD1
    nlinarith only [hs,hBD]
  · positivity

lemma upperError_le_linear_local (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (cost : ℕ → ℝ → ℝ) (C Z : ℝ) (hC : 1 ≤ C) (hZ : 0 ≤ Z)
    (hq : ∀ i, 0 ≤ q i) (K : ℕ) (hsum : ∀ k ≤ K, (∑ i : Fin k, q i.val) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k ≤ K, ∀ D, 1 ≤ D → cost k D ≤ C*D)
    (n k : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 1 ≤ D) :
    upperError q keep cost n k D ≤ C*(1+Z)^(2*n)*D := by
  have hZ1 : 1 ≤ 1+Z := by linarith
  induction n generalizing k D with
  | zero => simpa only [upperError,Nat.mul_zero,pow_zero,mul_one] using hcost k hk D hD
  | succ n ih =>
    let B := C*(1+Z)^(2*n)
    have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hZ1)
    have hB0 : 0 ≤ B := by linarith
    have hD0 : 0 ≤ D := by linarith
    have he : C*(1+Z)^(2*(n+1)) = B*(1+Z)^2 := by
      dsimp only [B]
      rw [show 2*(n+1)=2*n+2 by omega,pow_add]
      ring
    rw [he]
    change max (upperError q keep cost n k D)
      (1+∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n) i.val (D*q i.val)) ≤ _
    apply max_le
    · have hb : upperError q keep cost n k D ≤ B*D := ih k hk D hD
      have hz : 1 ≤ (1+Z)^2 := one_le_pow₀ hZ1
      exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hz (mul_nonneg hB0 hD0)])
    · have hl := lowerErrorStep_le_linear_local q keep (upperError q keep cost n) B Z
        hB hZ hq K hsum hkeep (fun k hk D hD => ih k hk D hD)
      have hs : (∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n) i.val (D*q i.val)) ≤
          B*(1+Z)*D*Z := by
        calc
          _ ≤ ∑ i : Fin k, B*(1+Z)*(D*q i.val) := sum_le_sum (fun i _ =>
            hl i.val (i.isLt.le.trans hk) _ (mul_nonneg hD0 (hq i.val)))
          _ = B*(1+Z)*D*(∑ i : Fin k, q i.val) := by
            rw [mul_sum]; apply sum_congr rfl; intro i hi; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsum k hk) (by positivity)
      have hBD : 1 ≤ B*D := one_le_mul_of_one_le_of_one_le hB hD
      have hz : 1+(1+Z)*Z ≤ (1+Z)^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hz (mul_nonneg hB0 hD0)
      nlinarith only [hs,hBD,hh]

lemma refined_lowerError_le_linear_local (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (cost : ℕ → ℝ → ℝ) (C Z : ℝ) (hC : 1 ≤ C) (hZ : 0 ≤ Z)
    (hq : ∀ i, 0 ≤ q i) (K : ℕ) (hsum : ∀ k ≤ K, (∑ i : Fin k, q i.val) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k ≤ K, ∀ D, 1 ≤ D → cost k D ≤ C*D)
    (n k : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep (upperError q keep cost n) k D ≤ C*(1+Z)^(2*n+1)*D := by
  have hB : 1 ≤ C*(1+Z)^(2*n) := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by linarith))
  have hh := lowerErrorStep_le_linear_local q keep (upperError q keep cost n)
    (C*(1+Z)^(2*n)) Z hB hZ hq K hsum hkeep
    (fun k hk D hD => upperError_le_linear_local q keep cost C Z hC hZ hq K hsum hkeep hcost n k hk D hD)
    k hk D hD
  simpa only [pow_succ,mul_assoc] using hh

noncomputable def prefixReciprocal (p : ℕ → ℕ) (K : ℕ) : ℝ := ∑ i : Fin K, 1/(p i.val : ℝ)

lemma prefixReciprocal_nonneg (p : ℕ → ℕ) (K : ℕ) : 0 ≤ prefixReciprocal p K := by
  apply sum_nonneg
  intro i hi
  positivity

lemma prefixReciprocal_mono (p : ℕ → ℕ) : Monotone (prefixReciprocal p) := by
  intro k K hk
  unfold prefixReciprocal
  rw [Fin.sum_univ_eq_sum_range (fun i => 1/(p i : ℝ)) k,
    Fin.sum_univ_eq_sum_range (fun i => 1/(p i : ℝ)) K]
  apply sum_le_sum_of_subset_of_nonneg (range_mono hk)
  intro i hi _
  positivity

/-- Linear divisor-level cost, including every incurred error of all fixed
refinement depths. The finite reciprocal sum is retained explicitly. -/
theorem scaled_refined_lowerError_le_linear (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (n k K : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) scaledSelbergCost n) k D ≤
        4*(1+prefixReciprocal p K)^(2*n+1)*D := by
  apply refined_lowerError_le_linear_local (fun i => 1/(p i : ℝ)) (primeKeep p) scaledSelbergCost 4 (prefixReciprocal p K) (by norm_num)
    (prefixReciprocal_nonneg p K) (fun i => by positivity) K
    (fun k hk => prefixReciprocal_mono p hk) (primeKeep_levels p hp hmono)
    (fun k hk D hD => scaledSelbergCost_le k D hD) n k hk D hD

lemma prefixReciprocal_loglog (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (K : ℕ) :
    prefixReciprocal p K ≤ log (log ((K : ℝ)+2))+WeightedMertens.reciprocalConstant := by
  let P := (range K).image p
  have hP : ∀ q ∈ P, q.Prime := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hq
    exact hp i
  have hcard : P.card ≤ K := (card_image_le).trans (by simp)
  have hh := WeightedMertens.prime_set_reciprocal_le P hP K hcard
  dsimp only [prefixReciprocal,P] at hh ⊢
  rw [sum_image hinj.injOn] at hh
  rw [Fin.sum_univ_eq_sum_range (fun i => 1/(p i : ℝ)) K]
  simpa only [one_div] using hh

#print axioms scaled_refined_lowerError_le_linear
#print axioms prefixReciprocal_loglog
end Erdos970.RecursiveSieve.Buchstab
