import FormalConjecturesUtil

/-! Generic resource-cost certificates for finite splitting networks.
These are necessary conditions for a construction model, not a proof that
arbitrary odd strict covering systems cannot exist. -/
namespace Erdos7SplittingCostCertificate
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A nonnegative superadditive function dominates the sum of its values. -/
lemma sum_le_of_superadditive {A : Type*} (s : Finset A) (g : A → ℕ)
    (φ : ℕ → ℚ) (hz : φ 0 = 0)
    (ha : ∀ a b, φ a + φ b ≤ φ (a+b)) :
    (∑ a ∈ s, φ (g a)) ≤ φ (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hz]
  | @insert a s h ih =>
    simp only [Finset.sum_insert h]
    exact (add_le_add_right ih _).trans (ha _ _)

/-- Superadditive node potentials cancel along internal edges. A local
splitting inequality therefore gives a lower bound on total leaf repair cost.
No acyclicity is needed for this cancellation theorem. -/
theorem resource_lower_bound {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I]
    (src dst : E → I) (p f : E → ℕ) (root leaf : I → ℕ)
    (φ : I → ℕ → ℚ) (cost : I → ℕ → ℚ)
    (hz : ∀ i, φ i 0 = 0)
    (hsuper : ∀ i a b, φ i a + φ i b ≤ φ i (a+b))
    (hbalance : ∀ i, root i + (∑ e, if dst e = i then p e*f e else 0) =
      leaf i + (∑ e, if src e = i then f e else 0))
    (hlocal : ∀ i, φ i (leaf i + (∑ e, if src e = i then f e else 0)) ≤
      cost i (leaf i) + (∑ e, if src e = i then φ (dst e) (p e*f e) else 0)) :
    (∑ i, φ i (root i)) ≤ ∑ i, cost i (leaf i) := by
  classical
  have hnode (i : I) :
      φ i (root i) + (∑ e, if dst e = i then φ (dst e) (p e*f e) else 0) ≤
      cost i (leaf i) + (∑ e, if src e = i then φ (dst e) (p e*f e) else 0) := by
    have hsum := sum_le_of_superadditive Finset.univ
      (fun e => if dst e = i then p e*f e else 0) (φ i) (hz i) (hsuper i)
    have heq : (∑ e, φ i (if dst e = i then p e*f e else 0)) =
        ∑ e, if dst e = i then φ (dst e) (p e*f e) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : dst e = i
      · simp [h]
      · simp [h, hz]
    rw [heq] at hsum
    exact ((add_le_add_right hsum _).trans (hsuper i _ _)).trans
      (by rw [hbalance]; exact hlocal i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hnode i)
  simp only [Finset.sum_add_distrib] at h
  have hin : (∑ i, ∑ e, if dst e = i then φ (dst e) (p e*f e) else 0) =
      ∑ e, φ (dst e) (p e*f e) := by
    rw [Finset.sum_comm]
    simp
  have hout : (∑ i, ∑ e, if src e = i then φ (dst e) (p e*f e) else 0) =
      ∑ e, φ (dst e) (p e*f e) := by
    rw [Finset.sum_comm]
    simp
  rw [hin, hout] at h
  exact (add_le_add_iff_right _).mp h

/-- Increasing discrete marginal costs imply superadditivity. -/
lemma superadditive_of_monotone_marginal (φ : ℕ → ℚ) (hz : φ 0 = 0)
    (hm : Monotone (fun n => φ (n+1) - φ n)) :
    ∀ a b, φ a + φ b ≤ φ (a+b) := by
  intro a b
  induction b with
  | zero => simp [hz]
  | succ b ih =>
    have h := hm (show b ≤ a+b by omega)
    simpa only [Nat.add_assoc] using (show φ a + φ (b+1) ≤ φ (a+b+1) by linarith)

/-- The elementary cost of one nonzero splitting edge. -/
lemma edge_hinge (w v p f : ℕ) (hw : w ≤ (p-1)*v) :
    w*f ≤ v*(p*f-1) := by
  by_cases hf : f = 0
  · simp [hf]
  have h : (p-1)*f ≤ p*f-1 := by
    rw [Nat.sub_mul]
    simp only [one_mul]
    omega
  calc
    w*f ≤ ((p-1)*v)*f := Nat.mul_le_mul_right f hw
    _ = v*((p-1)*f) := by ring
    _ ≤ v*(p*f-1) := Nat.mul_le_mul_left v h

/-- A particularly small certificate: linear hinge node potentials.
The branch condition uses p-1, not p; this is an integer-flow benefit. -/
theorem linear_hinge_bound {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I]
    (src dst : E → I) (p f : E → ℕ) (root leaf w c : I → ℕ)
    (hwc : ∀ i, w i ≤ c i)
    (hbranch : ∀ e, w (src e) ≤ (p e-1)*w (dst e))
    (hbalance : ∀ i, root i + (∑ e, if dst e = i then p e*f e else 0) =
      leaf i + (∑ e, if src e = i then f e else 0)) :
    (∑ i, w i*(root i-1)) ≤ ∑ i, c i*(leaf i-1) := by
  classical
  have hsuper (i : I) (a b : ℕ) :
      (w i*(a-1) : ℕ) + w i*(b-1) ≤ w i*(a+b-1) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (by omega)
  have hlocal (i : I) :
      w i*(leaf i + (∑ e, if src e = i then f e else 0)-1) ≤
      c i*(leaf i-1) + (∑ e, if src e = i then w (dst e)*(p e*f e-1) else 0) := by
    have hsum : w i*(∑ e, if src e = i then f e else 0) ≤
        ∑ e, if src e = i then w (dst e)*(p e*f e-1) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e _
      by_cases he : src e = i
      · simp only [if_pos he]
        exact edge_hinge _ _ _ _ (by simpa only [he] using hbranch e)
      · simp [he]
    calc
      _ ≤ w i*((leaf i-1) + (∑ e, if src e = i then f e else 0)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = w i*(leaf i-1) + w i*(∑ e, if src e = i then f e else 0) := by ring
      _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_right _ (hwc i)) hsum
  have h := resource_lower_bound src dst p f root leaf
    (fun i n => ((w i*(n-1) : ℕ) : ℚ))
    (fun i n => ((c i*(n-1) : ℕ) : ℚ))
    (by intro i; simp)
    (by intro i a b; dsimp only; exact_mod_cast hsuper i a b)
    hbalance (by intro i; dsimp only; exact_mod_cast hlocal i)
  dsimp only at h
  exact_mod_cast h

/-- Exact numerical margin for the31-prime, cofactor-square, E3=6 model.
This is only its scalar margin, not a formalized full graph instance. -/
lemma thirty_one_numeric_margin :
    (∏ p ∈ ([5,7,11,13,17,19,23,29,31] : List ℕ).toFinset, (p^2+p+1)) <
      3*2^6*(∏ p ∈ ([5,7,11,13,17,19,23,29,31] : List ℕ).toFinset, (p-1)^2) := by
  norm_num

#print axioms resource_lower_bound
#print axioms superadditive_of_monotone_marginal
#print axioms linear_hinge_bound
#print axioms thirty_one_numeric_margin
end Erdos7SplittingCostCertificate
