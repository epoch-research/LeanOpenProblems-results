import Submission.FiniteAdaptedExtension

/-!
Cloning an induced triangle-free subgraph and attaching its clones to an
existing hub preserves every prescribed countable triangle-avoiding edge
coloring literally. This is a construction obstruction, not a settlement
of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595HubClone
open Erdos595Work Erdos595FiniteAdapted

variable {V : Type*} (G : SimpleGraph V) (D : Set V) (r : V)

/-- Old--clone edges inherit adjacency within D, with extra edges to r.
The clone subgraph is a full induced copy of D. -/
def graph : SimpleGraph (V ⊕ D) where
  Adj
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr b => a = r ∨ (a ∈ D ∧ G.Adj a b.val)
    | .inr a, .inl b => b = r ∨ (b ∈ D ∧ G.Adj a.val b)
    | .inr a, .inr b => G.Adj a.val b.val
  symm := by
    intro a b h
    cases a <;> cases b
    · exact h.symm
    · exact h.imp_right (fun h => ⟨h.1,h.2.symm⟩)
    · exact h.imp_right (fun h => ⟨h.1,h.2.symm⟩)
    · exact h.symm
  loopless := by
    intro a h
    cases a with
    | inl a => exact h.ne rfl
    | inr a => exact h.ne rfl

private lemma no_triangle (hD : (G.induce D).CliqueFree 3)
    {a b c : V} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
  classical
  exact hD _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce D).Adj ⟨a,ha⟩ ⟨b,hb⟩ ∧
      (G.induce D).Adj ⟨a,ha⟩ ⟨c,hc⟩ ∧
      (G.induce D).Adj ⟨b,hb⟩ ⟨c,hc⟩ from ⟨hab,hac,hbc⟩))

/-- Every triangle containing a clone also contains the old hub. -/
theorem triangle_at_clone (hD : (G.induce D).CliqueFree 3)
    (a : D) (b c : V ⊕ D)
    (hab : (graph G D r).Adj (.inr a) b)
    (hac : (graph G D r).Adj (.inr a) c)
    (hbc : (graph G D r).Adj b c) : b = .inl r ∨ c = .inl r := by
  cases b with
  | inl b =>
    cases c with
    | inl c =>
      rcases hab with rfl | ⟨hb,hab⟩
      · exact Or.inl rfl
      rcases hac with rfl | ⟨hc,hac⟩
      · exact Or.inr rfl
      exact (no_triangle G D hD a.property hb hc hab hac hbc).elim
    | inr c =>
      rcases hab with rfl | ⟨hb,hab⟩
      · exact Or.inl rfl
      rcases hbc with rfl | ⟨_,hbc⟩
      · exact Or.inl rfl
      exact (no_triangle G D hD a.property hb c.property hab hac hbc).elim
  | inr b =>
    cases c with
    | inl c =>
      rcases hac with rfl | ⟨hc,hac⟩
      · exact Or.inr rfl
      rcases hbc with rfl | ⟨_,hbc⟩
      · exact Or.inr rfl
      exact (no_triangle G D hD a.property b.property hc hab hac hbc).elim
    | inr c =>
      exact (no_triangle G D hD a.property b.property c.property hab hac hbc).elim

private theorem no_four_at_clone (hD : (G.induce D).CliqueFree 3)
    (a : D) (b c d : V ⊕ D)
    (hab : (graph G D r).Adj (.inr a) b)
    (hac : (graph G D r).Adj (.inr a) c)
    (had : (graph G D r).Adj (.inr a) d)
    (hbc : (graph G D r).Adj b c)
    (hbd : (graph G D r).Adj b d)
    (hcd : (graph G D r).Adj c d) : False := by
  have h₁ := triangle_at_clone G D r hD a b c hab hac hbc
  have h₂ := triangle_at_clone G D r hD a b d hab had hbd
  have h₃ := triangle_at_clone G D r hD a c d hac had hcd
  rcases h₁ with hb | hc
  · rcases h₃ with hc | hd
    · exact hbc.ne (hb.trans hc.symm)
    · exact hbd.ne (hb.trans hd.symm)
  · rcases h₂ with hb | hd
    · exact hbc.ne (hb.trans hc.symm)
    · exact hcd.ne (hc.trans hd.symm)

/-- No four-clique is created, even when the hub itself belongs to D. -/
theorem cliqueFree (hD : (G.induce D).CliqueFree 3) (hG : G.CliqueFree 4) :
    (graph G D r).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha : ∀ i j : Fin 4, i ≠ j → (graph G D r).Adj (e i) (e j) :=
    fun _ _ hij => e.map_rel_iff.mpr hij
  have h01 := ha 0 1 (by decide)
  have h02 := ha 0 2 (by decide)
  have h03 := ha 0 3 (by decide)
  have h12 := ha 1 2 (by decide)
  have h13 := ha 1 3 (by decide)
  have h23 := ha 2 3 (by decide)
  cases h0 : e 0 with
  | inr a =>
    exact no_four_at_clone G D r hD a (e 1) (e 2) (e 3)
      (h0 ▸ h01) (h0 ▸ h02) (h0 ▸ h03) h12 h13 h23
  | inl a =>
    cases h1 : e 1 with
    | inr b =>
      exact no_four_at_clone G D r hD b (e 0) (e 2) (e 3)
        (h1 ▸ h01.symm) (h1 ▸ h12) (h1 ▸ h13) h02 h03 h23
    | inl b =>
      cases h2 : e 2 with
      | inr c =>
        exact no_four_at_clone G D r hD c (e 0) (e 1) (e 3)
          (h2 ▸ h02.symm) (h2 ▸ h12.symm) (h2 ▸ h23) h01 h03 h13
      | inl c =>
        cases h3 : e 3 with
        | inr d =>
          exact no_four_at_clone G D r hD d (e 0) (e 1) (e 2)
            (h3 ▸ h03.symm) (h3 ▸ h13.symm) (h3 ▸ h23.symm) h01 h02 h12
        | inl d =>
          simp only [h0,h1,h2,h3] at h01 h02 h03 h12 h13 h23
          exact no_adj_common_neighbors hG h01 h02 h12 h03 h13 h23

/-- The newly assigned colors are independent of the prescribed old colors. -/
noncomputable def color (c : Sym2 V → ℕ) : Sym2 (V ⊕ D) → ℕ := by
  classical
  exact Sym2.lift ⟨fun a b => match a,b with
    | .inl a,.inl b => c s(a,b)
    | .inl a,.inr _ => if a = r then 0 else 1
    | .inr _,.inl b => if b = r then 0 else 1
    | .inr _,.inr _ => 1,
    by intro a b; cases a <;> cases b <;> simp only [Sym2.eq_swap]⟩

lemma color_old (c : Sym2 V → ℕ) (a b : V) :
    color D r c s(Sum.inl a,Sum.inl b) = c s(a,b) := rfl

private theorem valid_at_clone (hD : (G.induce D).CliqueFree 3)
    (c : Sym2 V → ℕ) (a : D) (b d : V ⊕ D)
    (hab : (graph G D r).Adj (.inr a) b)
    (had : (graph G D r).Adj (.inr a) d)
    (hbd : (graph G D r).Adj b d) :
    ¬(color D r c s(.inr a,b) = color D r c s(.inr a,d) ∧
      color D r c s(.inr a,b) = color D r c s(b,d)) := by
  classical
  have hh := triangle_at_clone G D r hD a b d hab had hbd
  rcases hh with rfl | rfl
  · cases d with
    | inl d =>
      have hd : d ≠ r := (show G.Adj r d from hbd).ne.symm
      simp [color,hd]
    | inr d => simp [color]
  · cases b with
    | inl b =>
      have hb : b ≠ r := (show G.Adj b r from hbd).ne
      simp [color,hb]
    | inr b => simp [color]

/-- Literal extension, with no restriction on which old colors have been used. -/
theorem color_valid (hD : (G.induce D).CliqueFree 3)
    (c : Sym2 V → ℕ) (hc : Valid G c) : Valid (graph G D r) (color D r c) := by
  intro a b d hab had hbd he
  cases a with
  | inr a => exact valid_at_clone G D r hD c a b d hab had hbd he
  | inl a =>
    cases b with
    | inr b =>
      apply valid_at_clone G D r hD c b (.inl a) d hab.symm hbd had
      simpa only [Sym2.eq_swap] using And.intro he.2 he.1
    | inl b =>
      cases d with
      | inr d =>
        apply valid_at_clone G D r hD c d (.inl a) (.inl b) had.symm hbd.symm hab
        simpa only [Sym2.eq_swap] using And.intro (he.1.symm.trans he.2) he.1.symm
      | inl d => exact hc a b d hab had hbd he

/-- Single-step covering preservation is stronger here: the old coloring
can be kept literally, so coherent iterations can use the extension theorem. -/
theorem countable_cover (hD : (G.induce D).CliqueFree 3)
    (hG : IsCountableUnionOfTriangleFree G) :
    IsCountableUnionOfTriangleFree (graph G D r) := by
  obtain ⟨c,hc⟩ := (countable_union_iff_edge_coloring G).mp hG
  exact (countable_union_iff_edge_coloring _).mpr ⟨color D r c,color_valid G D r hD c hc⟩

#print axioms triangle_at_clone
#print axioms cliqueFree
#print axioms color_valid
#print axioms countable_cover
end Erdos595HubClone
