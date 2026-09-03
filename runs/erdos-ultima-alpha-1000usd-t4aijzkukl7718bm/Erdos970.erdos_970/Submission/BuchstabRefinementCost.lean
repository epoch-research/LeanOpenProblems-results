import Submission.BuchstabRefinement

/-! Power bounds for the complete error budgets of fixed-depth Buchstab
refinement. The hypotheses explicitly include the minimum level at every
retained lower node. No discarded main branch discards an incurred error. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real

/-- A retained lower node has level at least one, as do all its upper children.
A power-summable family of marginals therefore controls its complete cost. -/
theorem lowerErrorStep_le_rpow (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (E : ℕ → ℝ → ℝ) (a B Z : ℝ) (ha : 0 ≤ a) (hB : 1 ≤ B) (hZ : 0 ≤ Z)
    (hq : ∀ i, 0 ≤ q i) (hpow : ∀ k, (∑ i : Fin k, q i.val ^ a) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hE : ∀ k D, 1 ≤ D → E k D ≤ B*D^a) (k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep E k D ≤ B*(1+Z)*D^a := by
  classical
  unfold lowerErrorStep
  split_ifs with hk
  · obtain ⟨hD1,hchild⟩ := hkeep k D hk
    have hs : (∑ i : Fin k, E i.val (D*q i.val)) ≤ B*D^a*Z := by
      calc
        _ ≤ ∑ i : Fin k, B*(D*q i.val)^a :=
          sum_le_sum (fun i _ => hE i.val _ (hchild i.val i.isLt))
        _ = B*D^a*(∑ i : Fin k, q i.val^a) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          rw [mul_rpow hD (hq i.val)]
          ring
        _ ≤ B*D^a*Z := mul_le_mul_of_nonneg_left (hpow k)
          (mul_nonneg (by linarith) (rpow_nonneg hD a))
    have hBD : 1 ≤ B*D^a := one_le_mul_of_one_le_of_one_le hB (one_le_rpow hD1 ha)
    calc
      _ ≤ B*D^a+B*D^a*Z := add_le_add hBD hs
      _ = _ := by ring
  · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (rpow_nonneg hD a)

/-- At each refinement pair the power-bound constant grows by at most
`(1+Z)^2`. The exponent and the bound are uniform in the prefix length. -/
theorem upperError_le_rpow (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (cost : ℕ → ℝ → ℝ) (a C Z : ℝ) (ha : 0 ≤ a) (hC : 1 ≤ C) (hZ : 0 ≤ Z)
    (hq : ∀ i, 0 ≤ q i) (hpow : ∀ k, (∑ i : Fin k, q i.val ^ a) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D^a)
    (n k : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    upperError q keep cost n k D ≤ C*(1+Z)^(2*n)*D^a := by
  have hZ1 : 1 ≤ 1+Z := by linarith
  induction n generalizing k D with
  | zero => simpa [upperError] using hcost k D hD
  | succ n ih =>
    let B := C*(1+Z)^(2*n)
    have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hZ1)
    have hB0 : 0 ≤ B := by linarith
    have hD0 : 0 ≤ D := by linarith
    have hDa : 0 ≤ D^a := rpow_nonneg hD0 a
    have he : C*(1+Z)^(2*(n+1)) = B*(1+Z)^2 := by
      dsimp [B]
      rw [show 2*(n+1) = 2*n+2 by omega, pow_add]
      ring
    rw [he]
    change max (upperError q keep cost n k D)
      (1+∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n)
        i.val (D*q i.val)) ≤ _
    apply max_le
    · have hb : upperError q keep cost n k D ≤ B*D^a := ih k D hD
      have hz : 1 ≤ (1+Z)^2 := one_le_pow₀ hZ1
      exact hb.trans (by nlinarith [mul_nonneg hB0 hDa])
    · have hl := lowerErrorStep_le_rpow q keep (upperError q keep cost n) a B Z
        ha hB hZ hq hpow hkeep (fun k D hD => ih k D hD)
      have hs : (∑ i : Fin k, lowerErrorStep q keep (upperError q keep cost n)
          i.val (D*q i.val)) ≤ B*(1+Z)*D^a*Z := by
        calc
          _ ≤ ∑ i : Fin k, B*(1+Z)*(D*q i.val)^a :=
            sum_le_sum (fun i _ => hl i.val _ (mul_nonneg hD0 (hq i.val)))
          _ = B*(1+Z)*D^a*(∑ i : Fin k, q i.val^a) := by
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            rw [mul_rpow hD0 (hq i.val)]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hpow k)
            (mul_nonneg (mul_nonneg hB0 (by linarith)) hDa)
      have hBD : 1 ≤ B*D^a := one_le_mul_of_one_le_of_one_le hB (one_le_rpow hD ha)
      have hz : 1+(1+Z)*Z ≤ (1+Z)^2 := by nlinarith
      calc
        _ ≤ B*D^a+B*(1+Z)*D^a*Z := add_le_add hBD hs
        _ = B*D^a*(1+(1+Z)*Z) := by ring
        _ ≤ B*D^a*(1+Z)^2 := mul_le_mul_of_nonneg_left hz (mul_nonneg hB0 hDa)
        _ = _ := by ring

/-- The lower bound after `n` upper refinements has one extra factor `1+Z`. -/
theorem refined_lowerError_le_rpow (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (cost : ℕ → ℝ → ℝ) (a C Z : ℝ) (ha : 0 ≤ a) (hC : 1 ≤ C) (hZ : 0 ≤ Z)
    (hq : ∀ i, 0 ≤ q i) (hpow : ∀ k, (∑ i : Fin k, q i.val ^ a) ≤ Z)
    (hkeep : ∀ k D, keep k D → 1 ≤ D ∧ ∀ i < k, 1 ≤ D*q i)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D^a)
    (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep q keep (upperError q keep cost n) k D ≤ C*(1+Z)^(2*n+1)*D^a := by
  have hZ1 : 1 ≤ 1+Z := by linarith
  have hb : 1 ≤ C*(1+Z)^(2*n) := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hZ1)
  have hh := lowerErrorStep_le_rpow q keep (upperError q keep cost n)
    a (C*(1+Z)^(2*n)) Z ha hb hZ hq hpow hkeep
      (fun k D hD => upperError_le_rpow q keep cost a C Z ha hC hZ hq hpow hkeep hcost n k D hD)
      k D hD
  simpa only [pow_succ, mul_assoc] using hh

#print axioms upperError_le_rpow
#print axioms refined_lowerError_le_rpow
end Erdos970.RecursiveSieve.Buchstab
