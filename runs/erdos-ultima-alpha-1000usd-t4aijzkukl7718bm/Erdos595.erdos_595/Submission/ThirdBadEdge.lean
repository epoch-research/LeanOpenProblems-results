import Submission.FiniteSupportObstruction

/-!
At the third mutual-ultrafilter stage, the vertices with no lifted original
triangle-free support need not be independent. In fact they can contain a
homomorphic copy of any triangle-free graph. The constructed graphs still
have three-piece triangle-free covers; this does not settle Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595MiddleCorner
namespace Erdos595ThirdBadEdge

universe u
variable {V : Type*}

def Cross (x y : Triple ℕ) : Prop :=
  x.a < y.b ∧ y.a < x.b ∧ x.b < y.c ∧ y.b < x.c

lemma Cross.symm {x y : Triple ℕ} (h : Cross x y) : Cross y x :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

lemma cross_common_one {x y z : Triple ℕ} (hxy : (graph ℕ).Adj x y)
    (hxz : Cross x z) (hyz : Cross y z) : (oneGraph ℕ).Adj x y := by
  rcases hxy with (h | h) | (h | h)
  · exact Or.inl h
  · have := hxz.2.2.2
    have := hyz.1
    change x.c = y.a at h
    omega
  · exact Or.inr h
  · have := hyz.2.2.2
    have := hxz.1
    change y.c = x.a at h
    omega

lemma no_three_one (x y z t : Triple ℕ)
    (hxy : (graph ℕ).Adj x y) (hxz : (graph ℕ).Adj x z)
    (hyz : (graph ℕ).Adj y z) (hxt : Cross x t) (hyt : Cross y t)
    (hzt : Cross z t) : False := by
  classical
  exact oneGraph_cliqueFree ℕ _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨cross_common_one hxy hxt hyt, cross_common_one hxz hxt hzt,
      cross_common_one hyz hyt hzt⟩)

lemma no_two_two (x y z t : Triple ℕ)
    (hxy : (graph ℕ).Adj x y) (hzt : (graph ℕ).Adj z t)
    (hxz : Cross x z) (hxt : Cross x t) (hyz : Cross y z) (hyt : Cross y t) : False := by
  have hxy' := cross_common_one hxy hxz hyz
  have hzt' := cross_common_one hzt hxz.symm hxt.symm
  rcases hxy' with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    rcases hzt' with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;>
    obtain ⟨ha,hb,hc,hd⟩ := hxz <;>
    obtain ⟨he,hf,hg,hh⟩ := hxt <;>
    obtain ⟨hi,hj,hk,hl⟩ := hyz <;>
    obtain ⟨hm,hn,ho,hp⟩ := hyt <;> omega

/-- Shift-square fibers joined by coordinate-overlap edges over B. -/
def H (B : SimpleGraph V) : SimpleGraph (V × Triple ℕ) where
  Adj x y := (x.1 = y.1 ∧ (graph ℕ).Adj x.2 y.2) ∨
    (B.Adj x.1 y.1 ∧ Cross x.2 y.2)
  symm := fun _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)
  loopless := fun _ h => h.elim (fun h => (graph ℕ).loopless _ h.2)
    (fun h => B.loopless _ h.1)

lemma same_adj (B : SimpleGraph V) (v : V) (x y : Triple ℕ) :
    (H B).Adj (v,x) (v,y) ↔ (graph ℕ).Adj x y := by
  simp [H]

lemma different_adj (B : SimpleGraph V) {x y : V × Triple ℕ}
    (h : (H B).Adj x y) (hne : x.1 ≠ y.1) :
    B.Adj x.1 y.1 ∧ Cross x.2 y.2 :=
  h.elim (fun h => (hne h.1).elim) id

private lemma no_four_same (B : SimpleGraph V) (hB : B.CliqueFree 3)
    (x y z t : V × Triple ℕ) (he : x.1 = y.1)
    (hxy : (H B).Adj x y) (hxz : (H B).Adj x z) (hxt : (H B).Adj x t)
    (hyz : (H B).Adj y z) (hyt : (H B).Adj y t) (hzt : (H B).Adj z t) : False := by
  have hi : (graph ℕ).Adj x.2 y.2 := hxy.elim And.right
    (fun h => (h.1.ne he).elim)
  by_cases hz : x.1 = z.1
  · have hxz' : (graph ℕ).Adj x.2 z.2 := hxz.elim And.right
      (fun h => (h.1.ne hz).elim)
    have hyz' : (graph ℕ).Adj y.2 z.2 := hyz.elim And.right
      (fun h => (h.1.ne (he.symm.trans hz)).elim)
    by_cases ht : x.1 = t.1
    · have hxt' : (graph ℕ).Adj x.2 t.2 := hxt.elim And.right
        (fun h => (h.1.ne ht).elim)
      have hyt' : (graph ℕ).Adj y.2 t.2 := hyt.elim And.right
        (fun h => (h.1.ne (he.symm.trans ht)).elim)
      have hzt' : (graph ℕ).Adj z.2 t.2 := hzt.elim And.right
        (fun h => (h.1.ne (hz.symm.trans ht)).elim)
      exact no_adj_common_neighbors (graph_cliqueFree ℕ) hi hxz' hyz' hxt' hyt' hzt'
    · exact no_three_one x.2 y.2 z.2 t.2 hi hxz' hyz'
        (different_adj B hxt ht).2
        (different_adj B hyt (fun h => ht (he.trans h))).2
        (different_adj B hzt (fun h => ht (hz.trans h))).2
  · by_cases ht : x.1 = t.1
    · have hxt' : (graph ℕ).Adj x.2 t.2 := hxt.elim And.right
        (fun h => (h.1.ne ht).elim)
      have hyt' : (graph ℕ).Adj y.2 t.2 := hyt.elim And.right
        (fun h => (h.1.ne (he.symm.trans ht)).elim)
      exact no_three_one x.2 y.2 t.2 z.2 hi hxt' hyt'
        (different_adj B hxz hz).2
        (different_adj B hyz (fun h => hz (he.trans h))).2
        (different_adj B hzt.symm (fun h => hz (ht.trans h))).2
    · have hxz' := different_adj B hxz hz
      have hxt' := different_adj B hxt ht
      by_cases hzt' : z.1 = t.1
      · have hi' : (graph ℕ).Adj z.2 t.2 := hzt.elim And.right
          (fun h => (h.1.ne hzt').elim)
        exact no_two_two x.2 y.2 z.2 t.2 hi hi' hxz'.2 hxt'.2
          (different_adj B hyz (fun h => hz (he.trans h))).2
          (different_adj B hyt (fun h => ht (he.trans h))).2
      · classical
        exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr
          ⟨hxz'.1, hxt'.1, (different_adj B hzt hzt').1⟩)

theorem H_cliqueFree (B : SimpleGraph V) (hB : B.CliqueFree 3) : (H B).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha : ∀ i j : Fin 4, i ≠ j → (H B).Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  have h01 := ha 0 1 (by decide)
  have h02 := ha 0 2 (by decide)
  have h03 := ha 0 3 (by decide)
  have h12 := ha 1 2 (by decide)
  have h13 := ha 1 3 (by decide)
  have h23 := ha 2 3 (by decide)
  by_cases h : (e 0).1 = (e 1).1
  · exact no_four_same B hB _ _ _ _ h h01 h02 h03 h12 h13 h23
  by_cases h' : (e 0).1 = (e 2).1
  · exact no_four_same B hB _ _ _ _ h' h02 h01 h03 h12.symm h23 h13
  by_cases h'' : (e 1).1 = (e 2).1
  · exact no_four_same B hB _ _ _ _ h'' h12 h01.symm h13 h02.symm h23 h03
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨(different_adj B h01 h).1, (different_adj B h02 h').1,
      (different_adj B h12 h'').1⟩)

abbrev H₁ (B : SimpleGraph V) (hB : B.CliqueFree 3) := ultrafilterGraph (H B) (H_cliqueFree B hB)
abbrev H₂ (B : SimpleGraph V) (hB : B.CliqueFree 3) :=
  ultrafilterGraph (H₁ B hB) (ultrafilterGraph_cliqueFree _ _)
abbrev H₃ (B : SimpleGraph V) (hB : B.CliqueFree 3) :=
  ultrafilterGraph (H₂ B hB) (ultrafilterGraph_cliqueFree _ _)

noncomputable def U : Ultrafilter ℕ := Filter.hyperfilter ℕ
lemma tail (n : ℕ) : {m : ℕ | n < m} ∈ U :=
  Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop n)

abbrev triple := Erdos595FiniteSupport.triple

lemma triple_eq (a b c : ℕ) (hab : a < b) (hbc : b < c) :
    triple a b c = ⟨a,b,c,hab,hbc⟩ := by
  simp [Erdos595FiniteSupport.triple, Nat.max_eq_right (by omega : a + 1 ≤ b),
    Nat.max_eq_right (by omega : b + 1 ≤ c)]

noncomputable def p (v : V) (a b : ℕ) : Ultrafilter (V × Triple ℕ) :=
  Ultrafilter.map (fun c => (v, triple a b c)) U

noncomputable def P (v : V) (a : ℕ) : Ultrafilter (Ultrafilter (V × Triple ℕ)) :=
  Ultrafilter.map (p v a) U

noncomputable def X (v : V) : Ultrafilter (Ultrafilter (Ultrafilter (V × Triple ℕ))) :=
  Ultrafilter.map (P v) U

lemma first_cross (B : SimpleGraph V) (hB : B.CliqueFree 3)
    {v w : V} (hvw : B.Adj v w) (a b c d : ℕ)
    (hab : a < b) (hcd : c < d) (had : a < d) (hcb : c < b) :
    (H₁ B hB).Adj (p v a b) (p w c d) := by
  have hdirect : ∀ (v w : V), B.Adj v w → ∀ (a b c d : ℕ),
      a < b → c < d → a < d → c < b →
      fubiniAdj (H B) (p v a b) (p w c d) := by
    intro v w hvw a b c d hab hcd had hcb
    change {e | {f | (H B).Adj (v,triple a b e) (w,triple c d f)} ∈ U} ∈ U
    apply Filter.mem_of_superset (tail (max b d))
    intro e he
    change max b d < e at he
    apply Filter.mem_of_superset (tail (max b d))
    intro f hf
    change max b d < f at hf
    change (H B).Adj (v,triple a b e) (w,triple c d f)
    rw [triple_eq a b e hab (by omega), triple_eq c d f hcd (by omega)]
    exact Or.inr ⟨hvw, had, hcb, by change b < f; omega, by change d < e; omega⟩
  exact ⟨hdirect v w hvw a b c d hab hcd had hcb,
    hdirect w v hvw.symm c d a b hcd hab hcb had⟩

lemma second_cross (B : SimpleGraph V) (hB : B.CliqueFree 3)
    {v w : V} (hvw : B.Adj v w) (a c : ℕ) :
    (H₂ B hB).Adj (P v a) (P w c) := by
  have hdirect : ∀ (v w : V), B.Adj v w → ∀ (a c : ℕ),
      fubiniAdj (H₁ B hB) (P v a) (P w c) := by
    intro v w hvw a c
    change {b | {d | (H₁ B hB).Adj (p v a b) (p w c d)} ∈ U} ∈ U
    apply Filter.mem_of_superset (tail (max a c))
    intro b hb
    change max a c < b at hb
    apply Filter.mem_of_superset (tail (max a c))
    intro d hd
    change max a c < d at hd
    exact first_cross B hB hvw a b c d (by omega) (by omega) (by omega) (by omega)
  exact ⟨hdirect v w hvw a c, hdirect w v hvw.symm c a⟩

lemma third_cross (B : SimpleGraph V) (hB : B.CliqueFree 3)
    {v w : V} (hvw : B.Adj v w) : (H₃ B hB).Adj (X v) (X w) := by
  constructor
  · change {a | {c | (H₂ B hB).Adj (P v a) (P w c)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun a => Filter.Eventually.of_forall
      (fun c => second_cross B hB hvw a c))
  · change {c | {a | (H₂ B hB).Adj (P w c) (P v a)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall
      (fun a => second_cross B hB hvw.symm c a))

/-- A lifted support from the original vertex set, at the third stage. -/
def lift₃ (S : Set (V × Triple ℕ)) :
    Set (Ultrafilter (Ultrafilter (V × Triple ℕ))) :=
  {Q | {q | S ∈ q} ∈ Q}

/-- All the selected third-stage vertices lack original triangle-free supports. -/
theorem no_original_support (B : SimpleGraph V) (v : V)
    (S : Set (V × Triple ℕ)) (hS : ((H B).induce S).CliqueFree 3) : lift₃ S ∉ X v := by
  classical
  intro hm
  change {a | {b | {c | (v,triple a b c) ∈ S} ∈ U} ∈ U} ∈ U at hm
  let T : ℕ → Set ℕ := fun a => {b | {c | (v,triple a b c) ∈ S} ∈ U}
  have hT : {a | T a ∈ U} ∈ U := hm
  obtain ⟨a,ha⟩ := Ultrafilter.nonempty_of_mem hT
  obtain ⟨b,hb,hab,hbA⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hT (Filter.inter_mem (tail a) ha))
  obtain ⟨c,hc,hbc,hcA,hcB⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hT (Filter.inter_mem (tail b) (Filter.inter_mem hbA hb)))
  obtain ⟨d,hcd,hdB,hdC⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (tail c) (Filter.inter_mem hcB hc))
  obtain ⟨e,hde,heC⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (tail d) hdC)
  have hx : (v,triple a b c) ∈ S := hcA
  have hy : (v,triple b c d) ∈ S := hdB
  have hz : (v,triple c d e) ∈ S := heC
  apply hS _
  apply SimpleGraph.is3Clique_triple_iff.mpr
  change ((H B).induce S).Adj ⟨(v,triple a b c),hx⟩ ⟨(v,triple b c d),hy⟩ ∧
    ((H B).induce S).Adj ⟨(v,triple a b c),hx⟩ ⟨(v,triple c d e),hz⟩ ∧
    ((H B).induce S).Adj ⟨(v,triple b c d),hy⟩ ⟨(v,triple c d e),hz⟩
  change (H B).Adj (v,triple a b c) (v,triple b c d) ∧
    (H B).Adj (v,triple a b c) (v,triple c d e) ∧
    (H B).Adj (v,triple b c d) (v,triple c d e)
  rw [same_adj, same_adj, same_adj,
    triple_eq a b c hab hbc, triple_eq b c d hbc hcd, triple_eq c d e hcd hde]
  exact ⟨Or.inl (Or.inl ⟨rfl,rfl⟩), Or.inl (Or.inr rfl),
    Or.inl (Or.inl ⟨rfl,rfl⟩)⟩

def Bad (B : SimpleGraph V) :
    Set (Ultrafilter (Ultrafilter (Ultrafilter (V × Triple ℕ)))) :=
  {R | ∀ S, ((H B).induce S).CliqueFree 3 → lift₃ S ∉ R}

/-- The unsupported third-stage part is not constrained to have small
ordinary vertex chromatic number. -/
noncomputable def badHom (B : SimpleGraph V) (hB : B.CliqueFree 3) :
    B →g (H₃ B hB).induce (Bad B) where
  toFun v := ⟨X v,no_original_support B v⟩
  map_rel' := third_cross B hB

lemma triangleFree_comap {A C : Type*} (G : SimpleGraph C) (hG : G.CliqueFree 3)
    (f : A → C) : (G.comap f).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show G.Adj (f a) (f b) ∧ G.Adj (f a) (f c) ∧ G.Adj (f b) (f c) from
      ⟨hab,hac,hbc⟩))

def piece (B : SimpleGraph V) (i : Fin 3) : SimpleGraph (V × Triple ℕ) :=
  H B ⊓ if i = 0 then (oneGraph ℕ).comap Prod.snd
    else if i = 1 then (twoGraph ℕ).comap Prod.snd else B.comap Prod.fst

lemma piece_cliqueFree (B : SimpleGraph V) (hB : B.CliqueFree 3) (i : Fin 3) :
    (piece B i).CliqueFree 3 := by
  fin_cases i
  · exact (triangleFree_comap _ (oneGraph_cliqueFree ℕ) Prod.snd).anti inf_le_right
  · exact (triangleFree_comap _ (twoGraph_cliqueFree ℕ) Prod.snd).anti inf_le_right
  · exact (triangleFree_comap B hB Prod.fst).anti inf_le_right

lemma three_pieces (B : SimpleGraph V) : H B = ⨆ i : Fin 3, piece B i := by
  ext x y
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro h
    rcases h with ⟨he,(h | h) | (h | h)⟩ | ⟨hB,hC⟩
    · exact ⟨0, Or.inl ⟨he,Or.inl (Or.inl h)⟩, Or.inl h⟩
    · exact ⟨1, Or.inl ⟨he,Or.inl (Or.inr h)⟩, Or.inl h⟩
    · exact ⟨0, Or.inl ⟨he,Or.inr (Or.inl h)⟩, Or.inr h⟩
    · exact ⟨1, Or.inl ⟨he,Or.inr (Or.inr h)⟩, Or.inr h⟩
    · exact ⟨2, Or.inr ⟨hB,hC⟩, hB⟩
  · rintro ⟨i,hi⟩
    exact hi.1

/-- Despite the unsupported subgraph, the whole third extension has a
three-piece triangle-free edge cover. -/
theorem third_three_pieces (B : SimpleGraph V) (hB : B.CliqueFree 3) :
    ∃ K : Fin 3 → SimpleGraph (Ultrafilter (Ultrafilter (Ultrafilter (V × Triple ℕ)))),
      (∀ i, (K i).CliqueFree 3) ∧ H₃ B hB = ⨆ i, K i := by
  obtain ⟨K₁,hK₁,he₁⟩ := ultrafilterGraph_finite_cover (H B) (H_cliqueFree B hB)
    (piece B) (piece_cliqueFree B hB) (three_pieces B)
  obtain ⟨K₂,hK₂,he₂⟩ := ultrafilterGraph_finite_cover (H₁ B hB)
    (ultrafilterGraph_cliqueFree _ _) K₁ hK₁ he₁
  exact ultrafilterGraph_finite_cover (H₂ B hB)
    (ultrafilterGraph_cliqueFree _ _) K₂ hK₂ he₂

/-- A concrete countable base refutes independence of the unsupported part. -/
theorem exists_bad_edge :
    ∃ (B : SimpleGraph (Fin 2)) (hB : B.CliqueFree 3)
      (R S : Ultrafilter (Ultrafilter (Ultrafilter (Fin 2 × Triple ℕ)))),
      (H₃ B hB).Adj R S ∧ R ∈ Bad B ∧ S ∈ Bad B := by
  let B : SimpleGraph (Fin 2) := ⊤
  have hB : B.CliqueFree 3 :=
    (SimpleGraph.Coloring.mk (G := B) id (fun h => h)).colorable.cliqueFree (by decide)
  exact ⟨B,hB,X 0,X 1,third_cross B hB (by decide),
    no_original_support B 0,no_original_support B 1⟩

/-- No fixed palette bounds ordinary vertex coloring of unsupported parts
when arbitrary (not necessarily countable) bases are allowed. -/
theorem unsupported_no_color_bound (C : Type u) :
    ∃ (V : Type u) (B : SimpleGraph V) (hB : B.CliqueFree 3),
      IsEmpty (((H₃ B hB).induce (Bad B)).Coloring C) := by
  obtain ⟨V,B,hB,hC⟩ := exists_triangleFree_not_colorable C
  refine ⟨V,B,hB,⟨fun c => ?_⟩⟩
  exact hC.false (c.comp (badHom B hB))

#print axioms H_cliqueFree
#print axioms third_cross
#print axioms no_original_support
#print axioms third_three_pieces
#print axioms exists_bad_edge
#print axioms unsupported_no_color_bound
end Erdos595ThirdBadEdge
