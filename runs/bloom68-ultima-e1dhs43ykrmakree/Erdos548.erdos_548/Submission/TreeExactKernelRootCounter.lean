import Submission.TreeParityKernel

/-!
# A finite counterexample to exact kernels with an arbitrary prescribed root

The graph is the path 0--1--2--3 with leaves 4,5 at 0 and leaves 6,7 at 3.
Its classes both have size four, but an exact c=3 kernel cannot contain root 1.
All finite checks use kernel-checked `decide`, not `native_decide`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Finset SimpleGraph TreeParityKernel TreeParityKernel.Part
namespace TreeExactKernelRootCounter

def oriented (x y : Fin 8) : Prop :=
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨
  (x = 0 ∧ y = 4) ∨ (x = 0 ∧ y = 5) ∨ (x = 3 ∧ y = 6) ∨ (x = 3 ∧ y = 7)

instance : DecidableRel oriented := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

def T : SimpleGraph (Fin 8) := SimpleGraph.fromRel oriented

instance : DecidableRel T.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel oriented).Adj)


theorem connected : T.Connected := by decide

theorem isTree : T.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨connected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

theorem no_odd_set : ¬ ∃ U : Finset (Fin 8), U.card = 3 ∧ 1 ∉ U ∧
    (∀ x ∈ U, ∀ y ∈ U, ¬ T.Adj x y) ∧
    (0 ∈ U ∨ 2 ∈ U) ∧
    (∀ x y, T.Adj x y → x ∉ U → y ∉ U → x = 1 ∨ y = 1) := by
  decide


def coloring : T.Coloring (Fin 2) :=
  Coloring.mk (fun x => if x ∈ ({0, 2, 6, 7} : Finset (Fin 8)) then 0 else 1) (by decide)

theorem color_card : ∀ i : Fin 2,
    (univ.filter (fun x => coloring x = i)).card = 4 := by decide

theorem edge_card : T.edgeFinset.card = 7 := by decide

/-- The same tree does have an unrooted exact certificate. -/
theorem exact_unrooted :
    IsParityKernel T 3 ({0, 4} : Finset (Fin 8)) {1, 3, 5} {2, 6, 7} ∧
      ({1, 3, 5} : Finset (Fin 8)).card = 3 := by
  refine ⟨?_, by decide⟩
  refine { disjointRU := by decide
           disjointRW := by decide
           disjointUW := by decide
           partition := by ext x; fin_cases x <;> simp
           nonempty := by decide
           connected := by decide
           independent := ?_
           neighbors := ?_
           odd_le := by decide
           outside_ge := by decide }
  · change ∀ x ∈ ({1, 3, 5} : Finset (Fin 8)), ∀ y ∈ ({1, 3, 5} : Finset (Fin 8)),
      x ≠ y → ¬ T.Adj x y
    decide
  · change ∀ w ∈ ({2, 6, 7} : Finset (Fin 8)), ∀ x, T.Adj w x →
      x ∈ ({1, 3, 5} : Finset (Fin 8))
    decide

/-- The proposed stronger rooted theorem is false, despite `3 < 4` for
both color classes and `3 ≤ 7/2`. No connectivity relaxation is used. -/
theorem no_exact_rooted : ¬ ∃ R U W : Finset (Fin 8),
    IsParityKernel T 3 R U W ∧ 1 ∈ R ∧ U.card = 3 := by
  classical
  rintro ⟨R, U, W, h, hr, hU⟩
  have hparts (x : Fin 8) : x ∈ R ∨ x ∈ U ∨ x ∈ W := by
    have hx := mem_univ x
    rw [← h.partition] at hx
    simpa only [mem_union, or_assoc] using hx
  have hbound := h.core_card_bound
  simp only [Fintype.card_fin] at hbound
  have hsmall : R.card ≤ 2 := by omega
  have hrU : (1 : Fin 8) ∉ U := fun hu => disjoint_left.mp h.disjointRU hr hu
  have htriple (x y : Fin 8) (hxR : x ∈ R) (hyR : y ∈ R)
      (hxy : x ≠ y) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : False := by
    have hsub : ({1, x, y} : Finset (Fin 8)) ⊆ R := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hr
      · exact hxR
      · exact hyR
    have hc3 : ({1, x, y} : Finset (Fin 8)).card = 3 := by
      simp [hx1.symm, hy1.symm, hxy]
    have := card_le_card hsub
    omega
  have hout (x y : Fin 8) (hxy : T.Adj x y) (hxU : x ∉ U) (hyU : y ∉ U) :
      x ∈ R ∧ y ∈ R := by
    constructor
    · rcases hparts x with hx | hx | hx
      · exact hx
      · exact (hxU hx).elim
      · exact (hyU (h.neighbors x hx hxy)).elim
    · rcases hparts y with hy | hy | hy
      · exact hy
      · exact (hyU hy).elim
      · exact (hxU (h.neighbors y hy hxy.symm)).elim
  apply no_odd_set
  refine ⟨U, hU, hrU, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact h.independent hx hy hxy.ne hxy
  · by_contra hh
    push_neg at hh
    have h10 : T.Adj 1 0 := by decide
    have h12 : T.Adj 1 2 := by decide
    exact htriple 0 2 (hout 1 0 h10 hrU hh.1).2 (hout 1 2 h12 hrU hh.2).2
      (by decide) (by decide) (by decide)
  · intro x y hxy hxU hyU
    by_contra hh
    push_neg at hh
    exact htriple x y (hout x y hxy hxU hyU).1 (hout x y hxy hxU hyU).2
      hxy.ne hh.1 hh.2

#print axioms no_odd_set
#print axioms isTree
#print axioms no_exact_rooted
#print axioms color_card
#print axioms exact_unrooted
end TreeExactKernelRootCounter
