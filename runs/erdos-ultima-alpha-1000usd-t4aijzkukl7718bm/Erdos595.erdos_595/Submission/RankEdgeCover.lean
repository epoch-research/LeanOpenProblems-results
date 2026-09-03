import Submission.Work

/-! Independent rank classes can reuse their edge palettes when every strict
lower neighborhood has a proper countable vertex coloring. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595RankEdgeCover
open Erdos595Work
universe u v
variable {V : Type u} {I : Type v} [LinearOrder I]

/-- Rank assembly does not require the ranks themselves to be countable. -/
theorem cover_of_rank (G : SimpleGraph V) (r : V → I)
    (hl : ∀ v, Nonempty ((G.induce {w | G.Adj v w ∧ r w < r v}).Coloring ℕ))
    (hc : ∀ i, IsCountableUnionOfTriangleFree (G.induce {v | r v = i})) :
    IsCountableUnionOfTriangleFree G := by
  classical
  choose c valid using fun i => (countable_union_iff_edge_coloring _).mp (hc i)
  let loc (v : V) := (hl v).some
  let f (v w : V) := if h : G.Adj v w ∧ r w < r v then loc v ⟨w,h⟩ else 0
  have hf (a b d : V) (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d)
      (hb : r b < r a) (hd : r d < r a) : f a b ≠ f a d := by
    simpa [f,hab,hb,had,hd] using
      (loc a).valid (show (G.induce {w | G.Adj a w ∧ r w < r a}).Adj
        ⟨b,hab,hb⟩ ⟨d,had,hd⟩ from hbd)
  let same (i : I) (a b : V) : ℕ :=
    if h : r a = i ∧ r b = i then c i s(⟨a,h.1⟩,⟨b,h.2⟩) else 0
  have same_symm (i : I) (a b : V) : same i a b = same i b a := by
    by_cases h : r a = i ∧ r b = i
    · simp only [same,dif_pos h,dif_pos h.symm,Sym2.eq_swap]
    · have h' : ¬(r b = i ∧ r a = i) := fun hh => h hh.symm
      simp only [same,dif_neg h,dif_neg h']
  let code (a b : V) : ℕ ⊕ ℕ :=
    if r a = r b then Sum.inl (same (r a) a b)
    else Sum.inr (if r a < r b then f b a else f a b)
  have csymm (a b : V) : code a b = code b a := by
    rcases lt_trichotomy (r a) (r b) with h | h | h
    · simp [code,h.ne,h.ne.symm,h,not_lt_of_gt h]
    · simp only [code,h,ite_true]
      exact congrArg Sum.inl (same_symm _ _ _)
    · simp [code,h.ne,h.ne.symm,h,not_lt_of_gt h]
  have ordered (a b d : V) (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d)
      (habr : r a ≤ r b) (hbdr : r b ≤ r d) :
      ¬(code a b = code a d ∧ code a b = code b d) := by
    intro he
    by_cases hab' : r a = r b
    · by_cases hbd' : r b = r d
      · have had' := hab'.trans hbd'
        have hcol := valid (r d) ⟨a,had'⟩ ⟨b,hbd'⟩ ⟨d,rfl⟩ hab had hbd
        apply hcol
        simp only [code,if_pos hab',if_pos had',if_pos hbd',Sum.inl.injEq] at he
        rw [hab',hbd'] at he
        simpa only [same,dif_pos (And.intro had' hbd'),
          dif_pos (And.intro had' rfl),dif_pos (And.intro hbd' rfl)] using he
      · have had' : r a ≠ r d := by simpa only [hab'] using hbd'
        simp only [code,if_pos hab',if_neg had',Sum.inl_ne_inr,false_and] at he
    · have hablt := lt_of_le_of_ne habr hab'
      by_cases hbd' : r b = r d
      · simp only [code,if_neg hab',if_pos hbd',Sum.inr_ne_inl,and_false] at he
      · have hbdlt := lt_of_le_of_ne hbdr hbd'
        have hadlt := hablt.trans hbdlt
        have hh : f d a = f d b := by
          simpa only [code,if_neg hadlt.ne,if_neg hbd',if_pos hadlt,if_pos hbdlt,
            Sum.inr.injEq] using he.1.symm.trans he.2
        exact hf d a b had.symm hbd.symm hab hadlt hbdlt hh
  have all (a b d : V) (hab : G.Adj a b) (had : G.Adj a d) (hbd : G.Adj b d) :
      ¬(code a b = code a d ∧ code a b = code b d) := by
    intro he
    have he' : code a d = code b d := he.1.symm.trans he.2
    rcases le_total (r a) (r b) with habr | hbar
    · rcases le_total (r b) (r d) with hbdr | hdbr
      · exact ordered a b d hab had hbd habr hbdr he
      · rcases le_total (r a) (r d) with hadr | hdar
        · apply ordered a d b had hab hbd.symm hadr hdbr
          exact ⟨he.1.symm,he'.trans (csymm b d)⟩
        · apply ordered d a b had.symm hbd.symm hab hdar habr
          exact ⟨(csymm d a).trans (he'.trans (csymm b d)),
            (csymm d a).trans he.1.symm⟩
    · rcases le_total (r a) (r d) with hadr | hdar
      · apply ordered b a d hab.symm hbd had hbar hadr
        exact ⟨(csymm b a).trans he.2,(csymm b a).trans he.1⟩
      · rcases le_total (r b) (r d) with hbdr | hdbr
        · apply ordered b d a hbd hab.symm had.symm hbdr hdar
          exact ⟨he.2.symm.trans (csymm a b),he'.symm.trans (csymm a d)⟩
        · apply ordered d b a hbd.symm had.symm hab.symm hdbr hbar
          exact ⟨(csymm d b).trans (he'.symm.trans (csymm a d)),
            (csymm d b).trans (he.2.symm.trans (csymm a b))⟩
  let ec : Sym2 V → ℕ ⊕ ℕ := Sym2.lift ⟨code,csymm⟩
  apply (countable_union_iff_edge_coloring G).mpr
  refine ⟨fun e => Encodable.encode (ec e),?_⟩
  intro a b d hab had hbd he
  exact all a b d hab had hbd
    ⟨Encodable.encode_injective he.1,Encodable.encode_injective he.2⟩

#print axioms cover_of_rank
end Erdos595RankEdgeCover
