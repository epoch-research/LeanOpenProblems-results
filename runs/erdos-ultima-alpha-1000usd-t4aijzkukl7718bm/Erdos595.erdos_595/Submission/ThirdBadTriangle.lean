import Submission.ThirdBadEdge

/-!
A countable K4-free base whose THIRD mutual-ultrafilter extension has a triangle
entirely among vertices without original triangle-free supports. An extra tuple
coordinate is essential to this construction. The example has a finite edge
cover and is not a witness for Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595MiddleCorner
open Erdos595ThirdBadEdge (U tail)
namespace Erdos595ThirdBadTriangle
universe u
variable {V : Type*}

structure Quad where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ab : a < b
  bc : b < c
  cd : c < d

instance : Countable Quad := by
  apply Function.Injective.countable (f := fun x : Quad => (x.a,x.b,x.c,x.d))
  intro x y h
  cases x; cases y
  simpa using h

def project (x : Quad) : Triple ℕ := ⟨x.a,x.c,x.d,x.ab.trans x.bc,x.cd⟩

def Cross (x y : Quad) : Prop :=
  x.a < y.b ∧ y.a < x.b ∧ x.b < y.c ∧ y.b < x.c ∧ (x.d < y.c ∨ y.d < x.c)

lemma Cross.symm {x y : Quad} (h : Cross x y) : Cross y x :=
  ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,h.2.2.2.2.symm⟩

lemma no_common_cross {x y z : Quad} (hxy : (graph ℕ).Adj (project x) (project y))
    (hxz : Cross x z) (hyz : Cross y z) : False := by
  have h1 := hxz.2.2.2.1
  have h2 := hyz.1
  have h3 := hyz.2.2.2.1
  have h4 := hxz.1
  have hxc := x.cd
  have hyc := y.cd
  rcases hxy with (⟨h,_⟩ | h) | (⟨h,_⟩ | h) <;>
    change _ = _ at h <;> dsimp [project] at h <;> omega

def H (B : SimpleGraph V) : SimpleGraph (V × Quad) where
  Adj x y := (x.1 = y.1 ∧ (graph ℕ).Adj (project x.2) (project y.2)) ∨
    (B.Adj x.1 y.1 ∧ Cross x.2 y.2)
  symm := fun _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)
  loopless := fun _ h => h.elim (fun h => (graph ℕ).loopless _ h.2)
    (fun h => B.loopless _ h.1)

lemma same_fiber (B : SimpleGraph V) {x y z : V × Quad}
    (he : x.1 = y.1) (hxy : (H B).Adj x y) (hxz : (H B).Adj x z) (hyz : (H B).Adj y z) :
    x.1 = z.1 := by
  by_contra hn
  have hi : (graph ℕ).Adj (project x.2) (project y.2) :=
    hxy.elim And.right (fun h => (h.1.ne he).elim)
  have hx := hxz.resolve_left (fun h => hn h.1)
  have hy := hyz.resolve_left (fun h => hn (he.trans h.1))
  exact no_common_cross hi hx.2 hy.2

private lemma no_four_same (B : SimpleGraph V)
    (x y z t : V × Quad) (he : x.1 = y.1)
    (hxy : (H B).Adj x y) (hxz : (H B).Adj x z) (hxt : (H B).Adj x t)
    (hyz : (H B).Adj y z) (hyt : (H B).Adj y t) (hzt : (H B).Adj z t) : False := by
  have hz := same_fiber B he hxy hxz hyz
  have ht := same_fiber B he hxy hxt hyt
  have hi : ∀ {p q : V × Quad}, (H B).Adj p q → p.1 = q.1 →
      (graph ℕ).Adj (project p.2) (project q.2) :=
    fun h he => h.elim And.right (fun h => (h.1.ne he).elim)
  exact no_adj_common_neighbors (graph_cliqueFree ℕ) (hi hxy he) (hi hxz hz)
    (hi hyz (he.symm.trans hz)) (hi hxt ht) (hi hyt (he.symm.trans ht))
    (hi hzt (hz.symm.trans ht))

theorem H_cliqueFree (B : SimpleGraph V) (hB : B.CliqueFree 4) : (H B).CliqueFree 4 := by
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
  by_cases h01' : (e 0).1 = (e 1).1
  · exact no_four_same B _ _ _ _ h01' h01 h02 h03 h12 h13 h23
  by_cases h02' : (e 0).1 = (e 2).1
  · exact no_four_same B _ _ _ _ h02' h02 h01 h03 h12.symm h23 h13
  by_cases h03' : (e 0).1 = (e 3).1
  · exact no_four_same B _ _ _ _ h03' h03 h01 h02 h13.symm h23.symm h12
  by_cases h12' : (e 1).1 = (e 2).1
  · exact no_four_same B _ _ _ _ h12' h12 h01.symm h13 h02.symm h23 h03
  by_cases h13' : (e 1).1 = (e 3).1
  · exact no_four_same B _ _ _ _ h13' h13 h01.symm h12 h03.symm h23.symm h02
  by_cases h23' : (e 2).1 = (e 3).1
  · exact no_four_same B _ _ _ _ h23' h23 h02.symm h12.symm h03.symm h13.symm h01
  have hb : ∀ i j : Fin 4, i ≠ j → (e i).1 ≠ (e j).1 → B.Adj (e i).1 (e j).1 := by
    intro i j hij he
    exact (ha i j hij).elim (fun h => (he h.1).elim) And.left
  exact no_adj_common_neighbors hB (hb 0 1 (by decide) h01')
    (hb 0 2 (by decide) h02') (hb 1 2 (by decide) h12')
    (hb 0 3 (by decide) h03') (hb 1 3 (by decide) h13') (hb 2 3 (by decide) h23')

abbrev H₁ (B : SimpleGraph V) (hB : B.CliqueFree 4) := ultrafilterGraph (H B) (H_cliqueFree B hB)
abbrev H₂ (B : SimpleGraph V) (hB : B.CliqueFree 4) :=
  ultrafilterGraph (H₁ B hB) (ultrafilterGraph_cliqueFree _ _)
abbrev H₃ (B : SimpleGraph V) (hB : B.CliqueFree 4) :=
  ultrafilterGraph (H₂ B hB) (ultrafilterGraph_cliqueFree _ _)

/-- The base is countably vertex-colorable even when V is arbitrarily large. -/
theorem base_countably_colorable (B : SimpleGraph V) : Nonempty ((H B).Coloring ℕ) := by
  classical
  obtain ⟨enc,henc⟩ := exists_injective_nat Quad
  refine ⟨SimpleGraph.Coloring.mk (fun x => enc x.2) ?_⟩
  intro x y h he
  have hq := henc he
  rcases h with ⟨_,h⟩ | ⟨_,h⟩
  · exact h.ne (congrArg project hq)
  · have hl := h.2.2.2.2
    rw [hq] at hl
    exact hl.elim (fun h => (lt_asymm y.2.cd h)) (fun h => (lt_asymm y.2.cd h))

def quad (a b c d : ℕ) : Quad :=
  let b' := max (a+1) b
  let c' := max (b'+1) c
  ⟨a,b',c',max (c'+1) d,by dsimp [b']; omega,by dsimp [c']; omega,by omega⟩

lemma quad_eq (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    quad a b c d = ⟨a,b,c,d,hab,hbc,hcd⟩ := by
  simp [quad,Nat.max_eq_right (by omega : a+1 ≤ b),
    Nat.max_eq_right (by omega : b+1 ≤ c),Nat.max_eq_right (by omega : c+1 ≤ d)]

noncomputable def p (v : V) (a b : ℕ) : Ultrafilter (V × Quad) :=
  U.bind (fun c => Ultrafilter.map (fun d => (v,quad a b c d)) U)

lemma mem_p (v : V) (a b : ℕ) (S : Set (V × Quad)) :
    S ∈ p v a b ↔ {c | {d | (v,quad a b c d) ∈ S} ∈ U} ∈ U := by
  change S ∈ Filter.bind (U : Filter ℕ)
    (fun c => (Ultrafilter.map (fun d => (v,quad a b c d)) U).toFilter) ↔ _
  rw [Filter.mem_bind']
  rfl

noncomputable def P (v : V) (a : ℕ) : Ultrafilter (Ultrafilter (V × Quad)) :=
  Ultrafilter.map (p v a) U

noncomputable def X (v : V) : Ultrafilter (Ultrafilter (Ultrafilter (V × Quad))) :=
  Ultrafilter.map (P v) U

lemma first_cross (B : SimpleGraph V) (hB : B.CliqueFree 4)
    {v w : V} (hvw : B.Adj v w) (a b c d : ℕ)
    (hab : a < b) (hcd : c < d) (had : a < d) (hcb : c < b) :
    (H₁ B hB).Adj (p v a b) (p w c d) := by
  have hdirect : ∀ (v w : V), B.Adj v w → ∀ (a b c d : ℕ),
      a < b → c < d → a < d → c < b →
      fubiniAdj (H B) (p v a b) (p w c d) := by
    intro v w hvw a b c d hab hcd had hcb
    change {x | (H B).neighborSet x ∈ p w c d} ∈ p v a b
    rw [mem_p]
    apply Filter.mem_of_superset (tail (max b d))
    intro e he
    change max b d < e at he
    apply Filter.mem_of_superset (tail e)
    intro f hf
    change e < f at hf
    change (H B).neighborSet (v,quad a b e f) ∈ p w c d
    rw [mem_p]
    apply Filter.mem_of_superset (tail (max f d))
    intro g hg
    change max f d < g at hg
    apply Filter.mem_of_superset (tail g)
    intro k hk
    change g < k at hk
    change (H B).Adj (v,quad a b e f) (w,quad c d g k)
    rw [quad_eq a b e f hab (by omega) hf,quad_eq c d g k hcd (by omega) hk]
    refine Or.inr ⟨hvw,had,hcb,?_,?_,Or.inl ?_⟩
    · change b < g; omega
    · change d < e; omega
    · change f < g; omega
  exact ⟨hdirect v w hvw a b c d hab hcd had hcb,
    hdirect w v hvw.symm c d a b hcd hab hcb had⟩

lemma second_cross (B : SimpleGraph V) (hB : B.CliqueFree 4)
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
  exact ⟨hdirect v w hvw a c,hdirect w v hvw.symm c a⟩

lemma third_cross (B : SimpleGraph V) (hB : B.CliqueFree 4)
    {v w : V} (hvw : B.Adj v w) : (H₃ B hB).Adj (X v) (X w) := by
  constructor
  · change {a | {c | (H₂ B hB).Adj (P v a) (P w c)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun a => Filter.Eventually.of_forall
      (fun c => second_cross B hB hvw a c))
  · change {c | {a | (H₂ B hB).Adj (P w c) (P v a)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall
      (fun a => second_cross B hB hvw.symm c a))

def lift₃ (S : Set (V × Quad)) : Set (Ultrafilter (Ultrafilter (V × Quad))) :=
  {Q | {q | S ∈ q} ∈ Q}

/-- Eight chosen coordinates give a shift triangle in any allegedly large support. -/
theorem no_original_support (B : SimpleGraph V) (v : V)
    (S : Set (V × Quad)) (hS : ((H B).induce S).CliqueFree 3) : lift₃ S ∉ X v := by
  classical
  intro hm
  change {a | {b | S ∈ p v a b} ∈ U} ∈ U at hm
  simp_rw [mem_p] at hm
  let T : ℕ → Set ℕ := fun a => {b | {c | {d | (v,quad a b c d) ∈ S} ∈ U} ∈ U}
  have hT : {a | T a ∈ U} ∈ U := hm
  obtain ⟨a,ha⟩ := Ultrafilter.nonempty_of_mem hT
  obtain ⟨b,hab,hb⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (tail a) ha)
  obtain ⟨c,hc,hbc,hcX⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hT (Filter.inter_mem (tail b) hb))
  obtain ⟨d,hcd,hd⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (tail c) hc)
  obtain ⟨e,he,hde,heX,heY⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hT (Filter.inter_mem (tail d) (Filter.inter_mem hcX hd)))
  obtain ⟨f,hef,hf⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (tail e) he)
  obtain ⟨g,hfg,hgY,hgZ⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem (tail f) (Filter.inter_mem heY hf))
  obtain ⟨h,hgh,hhZ⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem (tail g) hgZ)
  have hx : (v,quad a b c e) ∈ S := heX
  have hy : (v,quad c d e g) ∈ S := hgY
  have hz : (v,quad e f g h) ∈ S := hhZ
  apply hS _
  apply SimpleGraph.is3Clique_triple_iff.mpr
  change ((H B).induce S).Adj ⟨(v,quad a b c e),hx⟩ ⟨(v,quad c d e g),hy⟩ ∧
    ((H B).induce S).Adj ⟨(v,quad a b c e),hx⟩ ⟨(v,quad e f g h),hz⟩ ∧
    ((H B).induce S).Adj ⟨(v,quad c d e g),hy⟩ ⟨(v,quad e f g h),hz⟩
  change (H B).Adj (v,quad a b c e) (v,quad c d e g) ∧
    (H B).Adj (v,quad a b c e) (v,quad e f g h) ∧
    (H B).Adj (v,quad c d e g) (v,quad e f g h)
  rw [quad_eq a b c e hab hbc (hcd.trans hde),
    quad_eq c d e g hcd hde (hef.trans hfg),quad_eq e f g h hef hfg hgh]
  exact ⟨Or.inl ⟨rfl,Or.inl (Or.inl ⟨rfl,rfl⟩)⟩,
    Or.inl ⟨rfl,Or.inl (Or.inr rfl)⟩,Or.inl ⟨rfl,Or.inl (Or.inl ⟨rfl,rfl⟩)⟩⟩

def Bad (B : SimpleGraph V) : Set (Ultrafilter (Ultrafilter (Ultrafilter (V × Quad)))) :=
  {R | ∀ S, ((H B).induce S).CliqueFree 3 → lift₃ S ∉ R}

/-- Every K4-free input, including inputs with triangles, maps into the
unsupported part of the third extension of a countably vertex-colorable base. -/
noncomputable def badHom (B : SimpleGraph V) (hB : B.CliqueFree 4) :
    B →g (H₃ B hB).induce (Bad B) where
  toFun v := ⟨X v,no_original_support B v⟩
  map_rel' := third_cross B hB

/-- A genuine countable-base counterexample to triangle-freeness of the
third-stage unsupported part. -/
theorem unsupported_can_contain_triangle :
    ∃ (B : SimpleGraph (Fin 3)) (hB : B.CliqueFree 4),
      ¬((H₃ B hB).induce (Bad B)).CliqueFree 3 := by
  classical
  let B : SimpleGraph (Fin 3) := ⊤
  have hB : B.CliqueFree 4 :=
    (SimpleGraph.Coloring.mk (G := B) id (fun h => h)).colorable.cliqueFree (by decide)
  let f := badHom B hB
  refine ⟨B,hB,fun h => ?_⟩
  exact h _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨f.map_adj (by decide : B.Adj 0 1),f.map_adj (by decide : B.Adj 0 2),
      f.map_adj (by decide : B.Adj 1 2)⟩)

/-- Universal coverability of these unsupported parts would already settle
universal coverability of arbitrary K4-free graphs. This is only an equivalence. -/
theorem all_cover_iff_bad_cover :
    (∀ (V : Type u) (B : SimpleGraph V), B.CliqueFree 4 → IsCountableUnionOfTriangleFree B) ↔
    (∀ (V : Type u) (B : SimpleGraph V) (hB : B.CliqueFree 4),
      IsCountableUnionOfTriangleFree ((H₃ B hB).induce (Bad B))) := by
  constructor
  · intro hall V B hB
    apply hall
    exact (ultrafilterGraph_cliqueFree (H₂ B hB)
      (ultrafilterGraph_cliqueFree _ _)).comap (SimpleGraph.Embedding.induce _)
  · intro hall V B hB
    exact countable_union_of_hom (badHom B hB) (hall V B hB)

/-- Finite input covers pass to a finite cover of the new base, with two extra pieces. -/
theorem base_finite_cover {I : Type*} [Finite I] (B : SimpleGraph V)
    (K : I → SimpleGraph V) (hK : ∀ i, (K i).CliqueFree 3) (hcov : B = ⨆ i, K i) :
    ∃ L : Fin 2 ⊕ I → SimpleGraph (V × Quad),
      (∀ i, (L i).CliqueFree 3) ∧ H B = ⨆ i, L i := by
  classical
  let L : Fin 2 ⊕ I → SimpleGraph (V × Quad) := fun i => H B ⊓ match i with
    | .inl 0 => (oneGraph ℕ).comap (project ∘ Prod.snd)
    | .inl _ => (twoGraph ℕ).comap (project ∘ Prod.snd)
    | .inr i => (K i).comap Prod.fst
  refine ⟨L,?_,?_⟩
  · rintro (i | i)
    · fin_cases i
      · exact (Erdos595ThirdBadEdge.triangleFree_comap _ (oneGraph_cliqueFree ℕ)
          (project ∘ Prod.snd)).anti inf_le_right
      · exact (Erdos595ThirdBadEdge.triangleFree_comap _ (twoGraph_cliqueFree ℕ)
          (project ∘ Prod.snd)).anti inf_le_right
    · exact (Erdos595ThirdBadEdge.triangleFree_comap _ (hK i) Prod.fst).anti inf_le_right
  · ext x y
    rw [SimpleGraph.iSup_adj]
    constructor
    · intro h
      have hh := h
      rcases h with ⟨he,(h | h) | (h | h)⟩ | ⟨hb,hc⟩
      · exact ⟨Sum.inl 0,hh,Or.inl h⟩
      · exact ⟨Sum.inl 1,hh,Or.inl h⟩
      · exact ⟨Sum.inl 0,hh,Or.inr h⟩
      · exact ⟨Sum.inl 1,hh,Or.inr h⟩
      · rw [hcov,SimpleGraph.iSup_adj] at hb
        obtain ⟨i,hi⟩ := hb
        exact ⟨Sum.inr i,hh,hi⟩
    · rintro ⟨i,hi⟩
      exact hi.1

/-- Finite edge covers also persist through all three mutual extensions. -/
theorem third_finite_cover {I : Type*} [Finite I] (B : SimpleGraph V) (hB : B.CliqueFree 4)
    (K : I → SimpleGraph V) (hK : ∀ i, (K i).CliqueFree 3) (hcov : B = ⨆ i, K i) :
    ∃ L : Fin 2 ⊕ I → SimpleGraph (Ultrafilter (Ultrafilter (Ultrafilter (V × Quad)))),
      (∀ i, (L i).CliqueFree 3) ∧ H₃ B hB = ⨆ i, L i := by
  obtain ⟨L,hL,he⟩ := base_finite_cover B K hK hcov
  obtain ⟨L₁,hL₁,he₁⟩ := ultrafilterGraph_finite_cover (H B) (H_cliqueFree B hB) L hL he
  obtain ⟨L₂,hL₂,he₂⟩ := ultrafilterGraph_finite_cover (H₁ B hB)
    (ultrafilterGraph_cliqueFree _ _) L₁ hL₁ he₁
  exact ultrafilterGraph_finite_cover (H₂ B hB) (ultrafilterGraph_cliqueFree _ _) L₂ hL₂ he₂

def trianglePiece (i : Fin 2) : SimpleGraph (Fin 3) :=
  (⊤ : SimpleGraph Bool).comap (fun v => decide (v.val = i.val))

lemma trianglePiece_cliqueFree (i : Fin 2) : (trianglePiece i).CliqueFree 3 := by
  apply Erdos595ThirdBadEdge.triangleFree_comap
  exact (SimpleGraph.Coloring.mk (G := (⊤ : SimpleGraph Bool)) id
    (fun h => h)).colorable.cliqueFree (by decide)

lemma triangle_two_pieces : (⊤ : SimpleGraph (Fin 3)) = ⨆ i : Fin 2, trianglePiece i := by
  ext v w
  rw [SimpleGraph.iSup_adj]
  change v ≠ w ↔ ∃ i : Fin 2, (decide (v.val = i.val) : Bool) ≠ decide (w.val = i.val)
  fin_cases v <;> fin_cases w <;> decide +kernel

/-- In the concrete countable-base triangle example four edge pieces suffice. -/
theorem concrete_four_pieces (hB : (⊤ : SimpleGraph (Fin 3)).CliqueFree 4) :
    ∃ L : Fin 2 ⊕ Fin 2 → SimpleGraph (Ultrafilter (Ultrafilter (Ultrafilter (Fin 3 × Quad)))),
      (∀ i, (L i).CliqueFree 3) ∧ H₃ ⊤ hB = ⨆ i, L i :=
  third_finite_cover ⊤ hB trianglePiece trianglePiece_cliqueFree triangle_two_pieces

#print axioms H_cliqueFree
#print axioms base_countably_colorable
#print axioms third_cross
#print axioms no_original_support
#print axioms unsupported_can_contain_triangle
#print axioms all_cover_iff_bad_cover
#print axioms third_finite_cover
#print axioms concrete_four_pieces
end Erdos595ThirdBadTriangle
