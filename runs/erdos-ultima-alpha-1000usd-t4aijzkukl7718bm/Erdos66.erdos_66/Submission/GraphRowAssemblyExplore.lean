import Submission.AffineLineAssemblyExplore

/-! Exact mixed counts for graph-indexed rows with arbitrary old fibers. -/
namespace Erdos66GraphRowAssembly
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly Erdos66SharedParameterSet
open scoped Classical
set_option maxHeartbeats 2200000
variable {G F : Type*} [AddCommGroup G] [DecidableEq G]
  [Field F] [Fintype F] [DecidableEq F]

noncomputable def rowAssembly (B : F → Finset G) (f : F → F) : Finset (G×(F×F)) :=
  Finset.univ.biUnion (fun x ↦ B x ×ˢ {(x,f x)})

omit [AddCommGroup G] [DecidableEq G] [Field F] [DecidableEq F] in
lemma rows_disjoint (B : F → Finset G) (f : F → F) :
    ((Finset.univ : Finset F) : Set F).PairwiseDisjoint (fun x ↦ B x ×ˢ {(x,f x)}) := by
  intro x hx y hy hxy
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hxz := Finset.mem_singleton.mp (Finset.mem_product.mp hz).2
  have hyz := Finset.mem_singleton.mp (Finset.mem_product.mp hz').2
  exact hxy (congrArg Prod.fst (hxz.symm.trans hyz))

omit [AddCommGroup G] [Field F] in
lemma mem_rowAssembly (B : F → Finset G) (f : F → F) (a : G) (x y : F) :
    (a,(x,y))∈rowAssembly B f ↔ a∈B x ∧ y=f x := by
  simp only [rowAssembly,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_product,Finset.mem_singleton,Prod.mk.injEq]
  constructor
  · rintro ⟨u,ha,hu,hy⟩
    subst u
    exact ⟨ha,hy⟩
  · rintro ⟨ha,hy⟩
    exact ⟨x,ha,rfl,hy⟩

omit [AddCommGroup G] [Field F] in
lemma rowAssembly_card (B : F → Finset G) (f : F → F) :
    (rowAssembly B f).card=∑ x : F, (B x).card := by
  rw [rowAssembly,Finset.card_biUnion (rows_disjoint B f)]
  simp only [Finset.card_product,Finset.card_singleton,mul_one]

lemma singleton_pairCount {H : Type*} [AddCommGroup H] [DecidableEq H] (a b z : H) :
    pairCount {a} {b} z=if a+b=z then 1 else 0 := by
  have he : z-a=b ↔ a+b=z := by
    rw [sub_eq_iff_eq_add]
    constructor <;> intro hh <;> simpa only [add_comm] using hh.symm
  simp only [pairCount,Finset.filter_singleton,Finset.mem_singleton,he]
  split_ifs <;> simp

/-- No disjointness assumption is imposed on the old fibers B,C: the
first graph coordinate distinguishes the rows exactly. -/
theorem rowAssembly_mixed_pairCount (B C : F → Finset G) (f h : F → F)
    (z : G) (s t : F) :
    pairCount (rowAssembly B f) (rowAssembly C h) (z,(s,t))=
      ∑ x : F, if f x+h (s-x)=t then pairCount (B x) (C (s-x)) z else 0 := by
  rw [rowAssembly,pairCount_biUnion_left _ _ (rows_disjoint B f)]
  simp_rw [rowAssembly,pairCount_biUnion_right _ _ (rows_disjoint C h),pairCount_product,
    singleton_pairCount]
  apply Finset.sum_congr rfl
  intro x hx
  have he (y : F) :
      pairCount (B x) (C y) z*(if (x,f x)+(y,h y)=(s,t) then 1 else 0)=
        if y=s-x then (if f x+h (s-x)=t then pairCount (B x) (C (s-x)) z else 0) else 0 := by
    by_cases hy : y=s-x
    · subst y
      simp
    · have hh : (x,f x)+(y,h y)≠(s,t) := by
        intro he
        apply hy
        have hfirst := congrArg Prod.fst he
        change x+y=s at hfirst
        linear_combination hfirst
      simp only [if_neg hh,if_neg hy,mul_zero]
  simp_rw [he]
  simp

/-- A root-count bound and old mixed-count cap transfer directly. -/
theorem rowAssembly_mixed_cap (B C : F → Finset G) (f h : F → F)
    (z : G) (s t : F) (g D : ℕ)
    (hcap : ∀ x y, pairCount (B x) (C y) z≤g)
    (hroot : (Finset.univ.filter (fun x : F ↦ f x+h (s-x)=t)).card≤D) :
    pairCount (rowAssembly B f) (rowAssembly C h) (z,(s,t))≤D*g := by
  rw [rowAssembly_mixed_pairCount,←Finset.sum_filter]
  calc
    _ ≤ ∑ _x∈Finset.univ.filter (fun x : F ↦ f x+h (s-x)=t), g :=
      Finset.sum_le_sum (fun x _ ↦ hcap x (s-x))
    _ = (Finset.univ.filter (fun x : F ↦ f x+h (s-x)=t)).card*g := by simp
    _ ≤ _ := Nat.mul_le_mul_right g hroot

end Erdos66GraphRowAssembly
