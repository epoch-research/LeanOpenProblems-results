import Submission.CountableConflictCover
import Submission.LocalTupleCover

/-!
A countable clone-history obstruction. An edge inherited from two base roots,
or joining an apex root to a clone carrying its index, has a countable
triangle-free edge cover. Arbitrarily many possible stages are allowed; each
individual history must be countable. This does not settle Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595CloneHistory
open Erdos595Work Erdos595CountableConflict

variable {V B I : Type*}

/-- A root cannot also occur among that vertex's clone stages. -/
def ValidHistory (root : V → B ⊕ I) (history : V → Set I) : Prop :=
  ∀ v i, root v = Sum.inr i → i ∉ history v

/-- The two ways an edge can be inherited by a clone/apex construction. -/
def Inherited (H : SimpleGraph B) (root : V → B ⊕ I)
    (history : V → Set I) (v w : V) : Prop :=
  (∃ b c, root v = Sum.inl b ∧ root w = Sum.inl c ∧ H.Adj b c) ∨
  (∃ i, root v = Sum.inr i ∧ i ∈ history w) ∨
  (∃ i, root w = Sum.inr i ∧ i ∈ history v)

private def left (root : V → B ⊕ I) (color : B → ℕ) : ℕ ⊕ I → Set V
  | .inl n => {v | ∃ b, root v = Sum.inl b ∧ color b = n}
  | .inr i => {v | root v = Sum.inr i}

private def right (root : V → B ⊕ I) (history : V → Set I)
    (color : B → ℕ) : ℕ ⊕ I → Set V
  | .inl n => {v | ∃ b, root v = Sum.inl b ∧ n < color b}
  | .inr i => {v | i ∈ history v}

/-- In particular, a countably properly colorable starting graph cannot be
amplified to an Erdős 595 witness using only these countable histories.
No cardinal bound on the set of stages, and no clique bound, is needed. -/
theorem cover (G : SimpleGraph V) (H : SimpleGraph B)
    (color : H.Coloring ℕ) (root : V → B ⊕ I) (history : V → Set I)
    (hvalid : ValidHistory root history)
    (hcount : ∀ v, (history v).Countable)
    (hedge : ∀ v w, G.Adj v w → Inherited H root history v w) :
    IsCountableUnionOfTriangleFree G := by
  classical
  apply cover_of_local_bicliques G (left root color) (right root history color)
  · intro k
    apply Set.disjoint_left.mpr
    intro v hv hw
    cases k with
    | inl n =>
      obtain ⟨b,hb,hbn⟩ := hv
      obtain ⟨c,hc,hnc⟩ := hw
      have hbc : b = c := Sum.inl.inj (hb.symm.trans hc)
      subst c
      omega
    | inr i => exact hvalid v i hv hw
  · intro v
    let S : Set I := history v ∪ {i | root v = Sum.inr i}
    have hs : S.Countable := by
      apply (hcount v).union
      cases hr : root v with
      | inl b => simp only [Sum.inl_ne_inr, Set.setOf_false]; exact Set.countable_empty
      | inr i =>
        have he : {j | (Sum.inr i : B ⊕ I) = Sum.inr j} = {i} := by
          ext j
          simp only [Set.mem_setOf_eq, Sum.inr.injEq, Set.mem_singleton_iff]
          exact eq_comm
        simpa only [hr,he] using (Set.countable_singleton i)
    apply ((Set.to_countable (Set.univ : Set ℕ)).image Sum.inl |>.union
      (hs.image Sum.inr)).mono
    intro k hk
    cases k with
    | inl n => exact Or.inl ⟨n,Set.mem_univ n,rfl⟩
    | inr i =>
      refine Or.inr ⟨i,?_,rfl⟩
      exact hk.elim Or.inr Or.inl
  · intro v w hvw
    rcases hedge v w hvw with ⟨b,c,hb,hc,hbc⟩ | ⟨i,hi,hw⟩ | ⟨i,hi,hv⟩
    · have hne := color.valid hbc
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨Sum.inl (color b),Or.inl ⟨⟨b,hb,rfl⟩,⟨c,hc,hlt⟩⟩⟩
      · exact ⟨Sum.inl (color c),Or.inr ⟨⟨c,hc,rfl⟩,⟨b,hb,hgt⟩⟩⟩
    · exact ⟨Sum.inr i,Or.inl ⟨hi,hw⟩⟩
    · exact ⟨Sum.inr i,Or.inr ⟨hi,hv⟩⟩

/-- The starting graph only needs a countable triangle-free edge cover;
a countable proper vertex coloring is unnecessary. -/
theorem cover_of_covered_base (G : SimpleGraph V) (H : SimpleGraph B)
    (hH : IsCountableUnionOfTriangleFree H)
    (root : V → B ⊕ I) (history : V → Set I)
    (hvalid : ValidHistory root history)
    (hcount : ∀ v, (history v).Countable)
    (hedge : ∀ v w, G.Adj v w → Inherited H root history v w) :
    IsCountableUnionOfTriangleFree G := by
  classical
  let f : V → Bool := fun v => decide (∃ b, root v = Sum.inl b)
  apply Erdos595LocalTuple.cover_of_countable_fibers G f
  intro k
  cases k with
  | false =>
    let A := {v : V // f v = false}
    let r : A → Unit ⊕ I := fun v => (root v.val).map (fun _ => ()) id
    let c : (⊥ : SimpleGraph Unit).Coloring ℕ :=
      SimpleGraph.Coloring.mk (fun _ => 0) (by intro a b h; exact h.elim)
    apply cover (G.induce {v | f v = false}) ⊥ c r (fun v => history v.val)
    · intro v i hi
      cases he : root v.val with
      | inl b => simp only [r,he,Sum.map_inl,Sum.inl_ne_inr] at hi
      | inr j =>
        have hj : j = i := by simpa only [r,he,Sum.map_inr,id_eq,Sum.inr.injEq] using hi
        exact hvalid v.val i (he.trans (congrArg Sum.inr hj))
    · intro v
      exact hcount v.val
    · intro v w hvw
      rcases hedge v.val w.val hvw with ⟨b,d,hb,hd,hbd⟩ | ⟨i,hi,hw⟩ | ⟨i,hi,hv⟩
      · have hn : ¬∃ b, root v.val = Sum.inl b := of_decide_eq_false v.property
        exact (hn ⟨b,hb⟩).elim
      · exact Or.inr (Or.inl ⟨i,by simp only [r,hi,Sum.map_inr,id_eq],hw⟩)
      · exact Or.inr (Or.inr ⟨i,by simp only [r,hi,Sum.map_inr,id_eq],hv⟩)
  | true =>
    let A := {v : V // f v = true}
    have hv (v : A) : ∃ b, root v.val = Sum.inl b := of_decide_eq_true v.property
    let t : A → B := fun v => (hv v).choose
    have ht (v : A) : root v.val = Sum.inl (t v) := (hv v).choose_spec
    let hom : (G.induce {v | f v = true}) →g H :=
      ⟨t,by
        intro v w hvw
        rcases hedge v.val w.val hvw with ⟨b,d,hb,hd,hbd⟩ | ⟨i,hi,hw⟩ | ⟨i,hi,hv⟩
        · have hb' : t v = b := Sum.inl.inj ((ht v).symm.trans hb)
          have hd' : t w = d := Sum.inl.inj ((ht w).symm.trans hd)
          simpa only [hb',hd'] using hbd
        · exact (Sum.inl_ne_inr ((ht v).symm.trans hi)).elim
        · exact (Sum.inl_ne_inr ((ht w).symm.trans hi)).elim⟩
    exact countable_union_of_hom hom hH

#print axioms cover
#print axioms cover_of_covered_base
end Erdos595CloneHistory
