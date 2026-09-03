import Submission.RootLattice

/-!
Finite-exponent root Cayley graphs. The coefficient group is ZMod 5, so
no short root equations wrap around. Clique bounds and triangle-free edge
covers transfer exactly as in the integer-root construction. This is an
auxiliary construction, not a settlement of Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteRootCayley

variable {V : Type*}

noncomputable def unit (a : V) : V → ZMod 5 := by
  classical
  exact fun x => if x = a then 1 else 0

noncomputable def root (a b : V) : V → ZMod 5 := unit a - unit b

lemma root_swap (a b : V) : root b a = -root a b := by
  unfold root
  abel

lemma root_ne_zero {a b : V} (h : a ≠ b) : root a b ≠ 0 := by
  classical
  intro he
  have := congrFun he a
  simp [root, unit, h] at this
  exact (by decide : (1 : ZMod 5) ≠ 0) this

lemma root_injective {a b c d : V} (hab : a ≠ b)
    (h : root a b = root c d) : a = c ∧ b = d := by
  classical
  have ha := congrFun h a
  have hb := congrFun h b
  simp only [root, Pi.sub_apply, unit, if_neg hab, if_neg hab.symm] at ha hb
  have hac : a = c := by
    by_contra hn
    simp only [if_neg hn] at ha
    split_ifs at ha <;> norm_num at * <;>
      first | exact (by decide : (1 : ZMod 5) ≠ -1) ha
            | exact (by decide : (1 : ZMod 5) ≠ 0) ha
  have hbd : b = d := by
    by_contra hn
    simp only [if_neg hn] at hb
    split_ifs at hb <;> norm_num at * <;>
      first | exact (by decide : (-1 : ZMod 5) ≠ 1) hb
            | exact (by decide : (1 : ZMod 5) ≠ 0) hb
  exact ⟨hac, hbd⟩

/-- Distinct roots whose difference is a root share their positive or
negative endpoint. -/
lemma root_sub_root {a b c d e f : V} (hab : a ≠ b) (hcd : c ≠ d)
    (h : root a b - root c d = root e f) : a = c ∨ b = d := by
  classical
  by_contra hn
  have hac : a ≠ c := fun he => hn (Or.inl he)
  have hbd : b ≠ d := fun he => hn (Or.inr he)
  have ha := congrFun h a
  have hb := congrFun h b
  simp only [root, Pi.sub_apply, unit, if_neg hab, if_neg hab.symm,
    if_neg hac, if_neg hbd] at ha hb
  have hae : a = e := by
    by_contra hne
    simp only [if_neg hne] at ha
    split_ifs at ha <;> norm_num at * <;>
      first | exact (by decide : (1 : ZMod 5) ≠ -1) ha
            | exact (by decide : (1 : ZMod 5) ≠ 0) ha
            | exact (by decide : (2 : ZMod 5) ≠ -1) ha
            | exact (by decide : (2 : ZMod 5) ≠ 0) ha
  have hbf : b = f := by
    by_contra hne
    simp only [if_neg hne] at hb
    split_ifs at hb <;> norm_num at * <;>
      first | exact (by decide : (-1 : ZMod 5) ≠ 1) hb
            | exact (by decide : (1 : ZMod 5) ≠ 0) hb
            | exact (by decide : (-2 : ZMod 5) ≠ 1) hb
            | exact (by decide : (2 : ZMod 5) ≠ 0) hb
  have hz : root c d = 0 := by
    rw [← hae, ← hbf] at h
    exact sub_eq_self.mp h
  exact root_ne_zero hcd hz

/-- All translates of the oriented edges of G in an finite-exponent vector group. -/
def graph (G : SimpleGraph V) : SimpleGraph (V → ZMod 5) where
  Adj x y := ∃ a b, G.Adj a b ∧ y - x = root a b
  symm := by
    rintro x y ⟨a,b,hab,h⟩
    refine ⟨b,a,hab.symm,?_⟩
    rw [root_swap, ← h]
    abel
  loopless := by
    rintro x ⟨a,b,hab,h⟩
    exact root_ne_zero hab.ne (by simpa only [sub_self] using h.symm)

lemma adj_root_iff (G : SimpleGraph V) {a b : V} {x y : V → ZMod 5}
    (hxy : y - x = root a b) :
    (graph G).Adj x y ↔ G.Adj a b := by
  constructor
  · rintro ⟨c,d,hcd,h⟩
    obtain ⟨rfl,rfl⟩ := root_injective hcd.ne (h.symm.trans hxy)
    exact hcd
  · intro h
    exact ⟨a,b,h,hxy⟩

/-- The original graph occurs on the unit vectors. -/
noncomputable def unitHom (G : SimpleGraph V) : G →g graph G where
  toFun := unit
  map_rel' := fun {a b} hab => ⟨b,a,hab.symm,rfl⟩

lemma triangle_roots (G : SimpleGraph V) {x y z : V → ZMod 5}
    (hxy : (graph G).Adj x y) (hxz : (graph G).Adj x z)
    (hyz : (graph G).Adj y z) :
    ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  obtain ⟨a,b,hab,he⟩ := hxy
  obtain ⟨c,d,hcd,hf⟩ := hxz
  obtain ⟨e,f,hef,hg⟩ := hyz
  have hdiff : root c d - root a b = root e f := by
    rw [← he, ← hf, ← hg]
    abel
  rcases root_sub_root hcd.ne hab.ne hdiff with hac | hbd
  · subst c
    have hbd : b ≠ d := by
      intro h
      subst d
      have hz : root e f = 0 := by simpa only [sub_self] using hdiff.symm
      exact root_ne_zero hef.ne hz
    have hroot : root b d = root e f := by
      rw [← hdiff]
      unfold root
      abel
    obtain ⟨rfl,rfl⟩ := root_injective hbd hroot
    exact ⟨a,b,d,hab,hcd,hef⟩
  · subst d
    have hca : c ≠ a := by
      intro h
      subst c
      have hz : root e f = 0 := by simpa only [sub_self] using hdiff.symm
      exact root_ne_zero hef.ne hz
    have hroot : root c a = root e f := by
      rw [← hdiff]
      unfold root
      abel
    obtain ⟨rfl,rfl⟩ := root_injective hca hroot
    exact ⟨b,a,c,hab.symm,hcd.symm,hef.symm⟩

theorem cliqueFree_three (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (graph G).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  obtain ⟨a,b,c,hab,hac,hbc⟩ := triangle_roots G hxy hxz hyz
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)


lemma shared_endpoint (G : SimpleGraph V) {o x y : V → ZMod 5} {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hx : x - o = root a b) (hy : y - o = root c d)
    (hxy : (graph G).Adj x y) : a = c ∨ b = d := by
  obtain ⟨e,f,hef,h⟩ := hxy
  have hdiff : root a b - root c d = root f e := by
    rw [root_swap e f, ← hx, ← hy, ← h]
    abel
  exact root_sub_root hab.ne hcd.ne hdiff

lemma common_left_adj (G : SimpleGraph V) {o x y : V → ZMod 5} {a b c : V}
    (hx : x - o = root a b) (hy : y - o = root a c)
    (hxy : (graph G).Adj x y) : G.Adj b c := by
  apply (adj_root_iff G (show y - x = root b c from ?_)).mp hxy
  have : y - x = (y - o) - (x - o) := by abel
  rw [this, hx, hy]
  unfold root
  abel

lemma common_right_adj (G : SimpleGraph V) {o x y : V → ZMod 5} {a b c : V}
    (hx : x - o = root a c) (hy : y - o = root b c)
    (hxy : (graph G).Adj x y) : G.Adj a b := by
  apply G.symm
  apply (adj_root_iff G (show y - x = root b a from ?_)).mp hxy
  have : y - x = (y - o) - (x - o) := by abel
  rw [this, hx, hy]
  unfold root
  abel

lemma rook_triple {a b c d e f : V}
    (h₁ : a = c ∨ b = d) (h₂ : a = e ∨ b = f) (h₃ : c = e ∨ d = f) :
    (a = c ∧ a = e) ∨ (b = d ∧ b = f) := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;>
    rcases h₃ with h₃ | h₃ <;> aesop

theorem cliqueFree_four (G : SimpleGraph V) (hG : G.CliqueFree 4) :
    (graph G).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have adj : ∀ i j : Fin 4, i ≠ j → (graph G).Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  obtain ⟨a,b,hab,hb⟩ := adj 0 1 (by decide)
  obtain ⟨c,d,hcd,hd⟩ := adj 0 2 (by decide)
  obtain ⟨f,g,hfg,hg⟩ := adj 0 3 (by decide)
  have h₁ := shared_endpoint G hab hcd hb hd (adj 1 2 (by decide))
  have h₂ := shared_endpoint G hab hfg hb hg (adj 1 3 (by decide))
  have h₃ := shared_endpoint G hcd hfg hd hg (adj 2 3 (by decide))
  rcases rook_triple h₁ h₂ h₃ with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Erdos595Work.no_adj_common_neighbors hG hab hcd
      (common_left_adj G hb hd (adj 1 2 (by decide))) hfg
      (common_left_adj G hb hg (adj 1 3 (by decide)))
      (common_left_adj G hd hg (adj 2 3 (by decide)))
  · exact Erdos595Work.no_adj_common_neighbors hG hab.symm hcd.symm
      (common_right_adj G hb hd (adj 1 2 (by decide))) hfg.symm
      (common_right_adj G hb hg (adj 1 3 (by decide)))
      (common_right_adj G hd hg (adj 2 3 (by decide)))

/-- Translation of every vertex by the same vector preserves adjacency. -/
theorem adj_translate (G : SimpleGraph V) (t x y : V → ZMod 5) :
    (graph G).Adj (t + x) (t + y) ↔ (graph G).Adj x y := by
  change (∃ a b, G.Adj a b ∧ (t + y) - (t + x) = root a b) ↔ _
  have h : (t + y) - (t + x) = y - x := by abel
  rw [h]
  rfl

/-- The root-lattice construction commutes with arbitrary unions of graphs. -/
theorem graph_iSup {I : Type*} (H : I → SimpleGraph V) :
    graph (⨆ i, H i) = ⨆ i, graph (H i) := by
  ext x y
  simp only [graph, SimpleGraph.iSup_adj]
  aesop

/-- Coverability is exactly preserved, not merely inherited in one direction. -/
theorem countable_cover_iff (G : SimpleGraph V) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph G) ↔
      Erdos595Work.IsCountableUnionOfTriangleFree G := by
  constructor
  · exact Erdos595Work.countable_union_of_hom (unitHom G)
  · rintro ⟨H,hH,rfl⟩
    exact ⟨fun n => graph (H n), fun n => cliqueFree_three (H n) (hH n), graph_iSup H⟩

/-- For this particular Cayley family, an arbitrary countable cover can
be replaced by one invariant under all translations. This assertion is
not being assumed for arbitrary Cayley graphs. -/
theorem translation_invariant_cover (G : SimpleGraph V)
    (h : Erdos595Work.IsCountableUnionOfTriangleFree (graph G)) :
    ∃ H : ℕ → SimpleGraph (V → ZMod 5),
      (∀ n, (H n).CliqueFree 3) ∧ graph G = ⨆ n, H n ∧
      ∀ n t x y, (H n).Adj (t + x) (t + y) ↔ (H n).Adj x y := by
  obtain ⟨H,hH,hcov⟩ := (countable_cover_iff G).mp h
  refine ⟨fun n => graph (H n), fun n => cliqueFree_three (H n) (hH n), ?_, ?_⟩
  · rw [hcov]
    exact graph_iSup H
  · exact fun n t x y => adj_translate (H n) t x y

#print axioms cliqueFree_three
#print axioms cliqueFree_four
#print axioms countable_cover_iff
#print axioms translation_invariant_cover

end Erdos595FiniteRootCayley
