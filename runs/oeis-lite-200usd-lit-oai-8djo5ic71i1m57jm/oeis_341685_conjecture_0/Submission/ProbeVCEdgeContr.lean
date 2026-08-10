import FormalConjectures.Util.ProblemImports
open scoped Pointwise

-- For n=0, d=0, test empty/univ VCN statements on trivial group PUnit? Need CommGroup.
example : False := by
  have h : HasMulVCNDimAtMost (∅ : Set (Multiplicative (ZMod 2))) 0 0 := by simp
  unfold HasMulVCNDimAtMost at h
  let x : Fin 0 → Fin (0+1) → Multiplicative (ZMod 2) := fun i => i.elim0
  let y : Set (Fin 0 → Fin (0+1)) → Multiplicative (ZMod 2) := fun _ => 1
  have hall : ∀ i s, y s * ∏ k, x k (i k) ∈ (∅ : Set (Multiplicative (ZMod 2))) ↔ i ∈ s := by
    intro i s
    -- choose? This is not true for s containing i. Need h only says no hall.
    sorry
  exact h x y hall

-- For univ, perhaps choose s=empty gives true ↔ false impossible, so true.
example : HasMulVCNDimAtMost (.univ : Set (Multiplicative (ZMod 2))) 0 0 := by simp
