import Submission.FiniteEndpointTransfer

/-! Explicit cyclic boundary loss and the exact shorter natural endpoint
remaining after multiplier invariance is used. -/
namespace Erdos371.FiniteInformation
open Finset

variable {A : Type*}

noncomputable def naturalGapDiscrepancy (N q : ℕ) (L : ℕ → A) (C : A → A → ℝ) : ℝ :=
  q * prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) -
    prefixMean N (fun n => C (L n) (L (n+q)))

lemma cyclicGapDiscrepancy_prefix (N q : ℕ) [NeZero N] (L : ℕ → A) (C : A → A → ℝ) :
    cyclicGapDiscrepancy N q (fun x => L x.val) C =
      q * prefixMean N (fun n => if q ∣ n then C (L n) (L ((n+q)%N)) else 0) -
        prefixMean N (fun n => C (L n) (L ((n+q)%N))) := by
  unfold cyclicGapDiscrepancy
  rw [mean_uniform_zmod_prefix, mean_uniform_zmod_prefix]
  congr 1
  · congr 1
    apply prefixMean_congr
    intro n hn
    simp only [cyclicResidue, ← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt hn,
      ZMod.natCast_eq_zero_iff]
  · apply prefixMean_congr
    intro n hn
    simp only [← Nat.cast_add, ZMod.val_natCast, Nat.mod_eq_of_lt hn]

/-- A uniform bound for removing cyclic wrap-around. It is deliberately a
coarse bound; for the fixed entropy-decrement scales it vanishes as N grows. -/
theorem cyclic_natural_gap_error (N q : ℕ) [NeZero N] (hq : q ≤ N)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |cyclicGapDiscrepancy N q (fun x => L x.val) C - naturalGapDiscrepancy N q L C| ≤
      2*q*(q+1 : ℝ)/N := by
  classical
  let a : ℝ := prefixMean N (fun n => if q ∣ n then C (L n) (L ((n+q)%N)) else 0)
  let b : ℝ := prefixMean N (fun n => C (L n) (L ((n+q)%N)))
  let c : ℝ := prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q)) else 0)
  let d : ℝ := prefixMean N (fun n => C (L n) (L (n+q)))
  have hcond : |a-c| ≤ 2*q/N := by
    have h := prefixMean_tail_bound N q hq
      (fun n => if q ∣ n then C (L n) (L ((n+q)%N)) else 0)
      (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) 1
      (fun n _ => by dsimp only; split_ifs <;> simp_all)
      (fun n _ => by dsimp only; split_ifs <;> simp_all)
      (fun n hn => by dsimp only; rw [Nat.mod_eq_of_lt (by omega : n+q < N)])
    simpa only [mul_one] using h
  have hunc : |b-d| ≤ 2*q/N := by
    have h := prefixMean_tail_bound N q hq
      (fun n => C (L n) (L ((n+q)%N))) (fun n => C (L n) (L (n+q))) 1
      (fun _ _ => hC _ _) (fun _ _ => hC _ _)
      (fun n hn => by dsimp only; rw [Nat.mod_eq_of_lt (by omega : n+q < N)])
    simpa only [mul_one] using h
  rw [cyclicGapDiscrepancy_prefix, naturalGapDiscrepancy]
  change |((q : ℝ)*a-b)-((q : ℝ)*c-d)| ≤ _
  rw [show ((q : ℝ)*a-b)-((q : ℝ)*c-d) = (q : ℝ)*(a-c)-(b-d) by ring]
  calc
    _ ≤ |(q : ℝ)*(a-c)|+|b-d| := abs_sub _ _
    _ = (q : ℝ)*|a-c|+|b-d| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    _ ≤ (q : ℝ)*(2*q/N)+2*q/N :=
      add_le_add (mul_le_mul_of_nonneg_left hcond (Nat.cast_nonneg q)) hunc
    _ = _ := by ring

/-- Even for EXACT multiplier-invariant labels, the transferred adjacent
correlation is at N/q. This theorem makes that endpoint explicit. -/
theorem stable_cyclic_gap_endpoint_bound (N q : ℕ) [NeZero N]
    (hq : 0 < q) (hd : q ∣ N) (L : ℕ → A) (C : A → A → ℝ)
    (hC : ∀ a b, |C a b| ≤ 1) (hL : ∀ m, L (q*m) = L m) :
    |cyclicGapDiscrepancy N q (fun x => L x.val) C -
      (prefixMean (N/q) (fun n => C (L n) (L (n+1))) -
        prefixMean N (fun n => C (L n) (L (n+q))))| ≤ 2*q*(q+1 : ℝ)/N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h := cyclic_natural_gap_error N q (Nat.le_of_dvd hN hd) L C hC
  rw [naturalGapDiscrepancy, conditioned_prefix_dilation L C q N hq hN hd hL] at h
  exact h

lemma natural_gap_endpoint_error (M N q : ℕ) (hM : 0 < M) (hMN : M ≤ N)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |naturalGapDiscrepancy N q L C-naturalGapDiscrepancy M q L C| ≤
      2*(q+1 : ℝ)*(N-M : ℕ)/N := by
  classical
  have hc := prefixMean_endpoint_bound M N hM hMN
    (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) 1
    (fun n _ => by dsimp only; split_ifs <;> simp_all)
  have hu := prefixMean_endpoint_bound M N hM hMN
    (fun n => C (L n) (L (n+q))) 1 (fun _ _ => hC _ _)
  simp only [mul_one] at hc hu
  let a := prefixMean N (fun n => if q ∣ n then C (L n) (L (n+q)) else 0) -
    prefixMean M (fun n => if q ∣ n then C (L n) (L (n+q)) else 0)
  let b := prefixMean N (fun n => C (L n) (L (n+q))) -
    prefixMean M (fun n => C (L n) (L (n+q)))
  have he : naturalGapDiscrepancy N q L C-naturalGapDiscrepancy M q L C = (q : ℝ)*a-b := by
    dsimp [naturalGapDiscrepancy,a,b]
    ring
  rw [he]
  calc
    _ ≤ |(q : ℝ)*a|+|b| := abs_sub _ _
    _ = (q : ℝ)*|a|+|b| := by rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    _ ≤ (q : ℝ)*(2*(N-M : ℕ)/N)+2*(N-M : ℕ)/N :=
      add_le_add (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg q)) hu
    _ = _ := by ring

#print axioms cyclic_natural_gap_error
#print axioms stable_cyclic_gap_endpoint_bound
end Erdos371.FiniteInformation
