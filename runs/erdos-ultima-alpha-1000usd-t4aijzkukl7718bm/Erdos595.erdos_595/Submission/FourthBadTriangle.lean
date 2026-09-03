import Submission.ThirdBadEdge

/-!
A countable K4-free base with a triangle of unsupported vertices in its FOURTH
mutual-ultrafilter extension. All stages remain finitely edge-coverable.
This is an auxiliary support obstruction, not a settlement of Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595MiddleCorner Erdos595ThirdBadEdge
namespace Erdos595FourthBadTriangle
variable {V : Type*}

/-- The additional order comparison separates two integration levels. -/
def D (B : SimpleGraph V) (lab : V → ℕ) : SimpleGraph (V × Triple ℕ) where
  Adj x y := (x.1 = y.1 ∧ (graph ℕ).Adj x.2 y.2) ∨
    (B.Adj x.1 y.1 ∧ Cross x.2 y.2 ∧
      (lab x.1 < lab y.1 → x.2.b < y.2.b) ∧
      (lab y.1 < lab x.1 → y.2.b < x.2.b))
  symm := fun _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm,h.2.symm⟩)
    (fun h => Or.inr ⟨h.1.symm,h.2.1.symm,h.2.2.2,h.2.2.1⟩)
  loopless := fun _ h => h.elim (fun h => (graph ℕ).loopless _ h.2)
    (fun h => B.loopless _ h.1)

lemma D_le (B : SimpleGraph V) (lab : V → ℕ) : D B lab ≤ H B :=
  fun _ _ h => h.elim Or.inl (fun h => Or.inr ⟨h.1,h.2.1⟩)

/-- Common neighbors of an internal fiber edge have the same level. -/
lemma same_level (B : SimpleGraph V) (lab : V → ℕ)
    {x y z : V × Triple ℕ} (he : x.1 = y.1)
    (hxy : (D B lab).Adj x y) (hxz : (D B lab).Adj x z) (hyz : (D B lab).Adj y z) :
    lab x.1 = lab z.1 := by
  by_contra hn
  have hx : x.1 ≠ z.1 := fun h => hn (congrArg lab h)
  have hy : y.1 ≠ z.1 := fun h => hx (he.trans h)
  have hi : (graph ℕ).Adj x.2 y.2 :=
    hxy.elim And.right (fun h => (h.1.ne he).elim)
  have hcx := hxz.resolve_left (fun h => hx h.1)
  have hcy := hyz.resolve_left (fun h => hy h.1)
  have hxy' := cross_common_one hi hcx.2.1 hcy.2.1
  have hl : lab x.1 = lab y.1 := congrArg lab he
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hm1 := hcx.2.2.1 hlt
    have hm2 := hcy.2.2.1 (by omega)
    have hc1 := hcx.2.1.2.2.2
    have hc2 := hcy.2.1.2.2.2
    rcases hxy' with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
  · have hm1 := hcx.2.2.2 hgt
    have hm2 := hcy.2.2.2 (by omega)
    have hc1 := hcx.2.1.1
    have hc2 := hcy.2.1.1
    rcases hxy' with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega

def mono (B : SimpleGraph V) (lab : V → ℕ) : SimpleGraph V where
  Adj x y := B.Adj x y ∧ lab x = lab y
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => B.loopless _ h.1

lemma mono_adj (B : SimpleGraph V) (lab : V → ℕ)
    {x y : V × Triple ℕ} (h : (D B lab).Adj x y) (he : lab x.1 = lab y.1) :
    (H (mono B lab)).Adj x y :=
  h.elim Or.inl (fun h => Or.inr ⟨⟨h.1,he⟩,h.2.1⟩)

private lemma no_four_same (B : SimpleGraph V) (lab : V → ℕ)
    (hmono : (mono B lab).CliqueFree 3)
    (x y z t : V × Triple ℕ) (he : x.1 = y.1)
    (hxy : (D B lab).Adj x y) (hxz : (D B lab).Adj x z) (hxt : (D B lab).Adj x t)
    (hyz : (D B lab).Adj y z) (hyt : (D B lab).Adj y t) (hzt : (D B lab).Adj z t) : False := by
  have hl := congrArg lab he
  have hz := same_level B lab he hxy hxz hyz
  have ht := same_level B lab he hxy hxt hyt
  exact no_adj_common_neighbors (H_cliqueFree (mono B lab) hmono)
    (mono_adj B lab hxy hl) (mono_adj B lab hxz hz)
    (mono_adj B lab hyz (hl.symm.trans hz)) (mono_adj B lab hxt ht)
    (mono_adj B lab hyt (hl.symm.trans ht)) (mono_adj B lab hzt (hz.symm.trans ht))

/-- K4-freeness follows if the base is K4-free and its level fibers are triangle-free. -/
theorem D_cliqueFree (B : SimpleGraph V) (lab : V → ℕ)
    (hB : B.CliqueFree 4) (hmono : (mono B lab).CliqueFree 3) : (D B lab).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have ha : ∀ i j : Fin 4, i ≠ j → (D B lab).Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  have h01 := ha 0 1 (by decide)
  have h02 := ha 0 2 (by decide)
  have h03 := ha 0 3 (by decide)
  have h12 := ha 1 2 (by decide)
  have h13 := ha 1 3 (by decide)
  have h23 := ha 2 3 (by decide)
  by_cases h01' : (e 0).1 = (e 1).1
  · exact no_four_same B lab hmono _ _ _ _ h01' h01 h02 h03 h12 h13 h23
  by_cases h02' : (e 0).1 = (e 2).1
  · exact no_four_same B lab hmono _ _ _ _ h02' h02 h01 h03 h12.symm h23 h13
  by_cases h03' : (e 0).1 = (e 3).1
  · exact no_four_same B lab hmono _ _ _ _ h03' h03 h01 h02 h13.symm h23.symm h12
  by_cases h12' : (e 1).1 = (e 2).1
  · exact no_four_same B lab hmono _ _ _ _ h12' h12 h01.symm h13 h02.symm h23 h03
  by_cases h13' : (e 1).1 = (e 3).1
  · exact no_four_same B lab hmono _ _ _ _ h13' h13 h01.symm h12 h03.symm h23.symm h02
  by_cases h23' : (e 2).1 = (e 3).1
  · exact no_four_same B lab hmono _ _ _ _ h23' h23 h02.symm h12.symm h03.symm h13.symm h01
  have hb : ∀ i j : Fin 4, i ≠ j → (e i).1 ≠ (e j).1 → B.Adj (e i).1 (e j).1 := by
    intro i j hij he
    exact (ha i j hij).elim (fun h => (he h.1).elim) And.left
  exact no_adj_common_neighbors hB (hb 0 1 (by decide) h01')
    (hb 0 2 (by decide) h02') (hb 1 2 (by decide) h12')
    (hb 0 3 (by decide) h03') (hb 1 3 (by decide) h13') (hb 2 3 (by decide) h23')

abbrev Base := Fin 3 × Triple ℕ

def level (v : Fin 3) : ℕ := if v = 2 then 1 else 0

def G : SimpleGraph Base := D ⊤ level

lemma mono_triangleFree : (mono (⊤ : SimpleGraph (Fin 3)) level).CliqueFree 3 := by
  let c : (mono (⊤ : SimpleGraph (Fin 3)) level).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk (fun v => ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩)
      (by intro v w h; fin_cases v <;> fin_cases w <;> norm_num [mono,level,Fin.ext_iff] at *)
  exact c.colorable.cliqueFree (by decide)

lemma G_cliqueFree : G.CliqueFree 4 := by
  apply D_cliqueFree _ _ _ mono_triangleFree
  exact (SimpleGraph.Coloring.mk (G := (⊤ : SimpleGraph (Fin 3))) id
    (fun h => h)).colorable.cliqueFree (by decide)

abbrev G₁ := ultrafilterGraph G G_cliqueFree
abbrev G₂ := ultrafilterGraph G₁ (ultrafilterGraph_cliqueFree _ _)
abbrev G₃ := ultrafilterGraph G₂ (ultrafilterGraph_cliqueFree _ _)
abbrev G₄ := ultrafilterGraph G₃ (ultrafilterGraph_cliqueFree _ _)

lemma adj_pure {A : Type*} (K : SimpleGraph A) (hK : K.CliqueFree 4)
    (q : Ultrafilter A) (v : A) :
    (ultrafilterGraph K hK).Adj q (pure v) ↔ K.neighborSet v ∈ q := by
  change ({w | K.neighborSet w ∈ (pure v : Ultrafilter A)} ∈ q ∧
    {w | K.neighborSet w ∈ q} ∈ (pure v : Ultrafilter A)) ↔ _
  simp only [Ultrafilter.mem_pure,Set.mem_setOf_eq,SimpleGraph.mem_neighborSet]
  have he : {w | K.Adj w v} = K.neighborSet v := by ext w; exact K.adj_comm w v
  rw [he]
  exact ⟨And.left,fun h => ⟨h,h⟩⟩

lemma pure_pure {A : Type*} (K : SimpleGraph A) (hK : K.CliqueFree 4)
    {v w : A} (h : K.Adj v w) : (ultrafilterGraph K hK).Adj (pure v) (pure w) := by
  rw [adj_pure,Ultrafilter.mem_pure]
  exact h.symm

lemma first_cross {v w : Fin 3} (hvw : v ≠ w) (a b c d : ℕ)
    (hab : a < b) (hcd : c < d) (had : a < d) (hcb : c < b)
    (hl : level v < level w → b < d) (hr : level w < level v → d < b) :
    G₁.Adj (p v a b) (p w c d) := by
  have hdirect : ∀ (v w : Fin 3), v ≠ w → ∀ (a b c d : ℕ),
      a < b → c < d → a < d → c < b →
      (level v < level w → b < d) → (level w < level v → d < b) →
      fubiniAdj G (p v a b) (p w c d) := by
    intro v w hvw a b c d hab hcd had hcb hl hr
    change {e | {f | G.Adj (v,triple a b e) (w,triple c d f)} ∈ U} ∈ U
    apply Filter.mem_of_superset (tail (max b d))
    intro e he
    change max b d < e at he
    apply Filter.mem_of_superset (tail (max b d))
    intro f hf
    change max b d < f at hf
    change G.Adj (v,triple a b e) (w,triple c d f)
    rw [triple_eq a b e hab (by omega),triple_eq c d f hcd (by omega)]
    exact Or.inr ⟨hvw,⟨had,hcb,by change b < f; omega,by change d < e; omega⟩,hl,hr⟩
  exact ⟨hdirect v w hvw a b c d hab hcd had hcb hl hr,
    hdirect w v hvw.symm c d a b hcd hab hcb had hr hl⟩

noncomputable def A (v : Fin 3) (a : ℕ) : Ultrafilter (Ultrafilter (Ultrafilter Base)) :=
  Ultrafilter.map (fun b => pure (p v a b)) U

noncomputable def Z (v : Fin 3) (allocation : Bool) :
    Ultrafilter (Ultrafilter (Ultrafilter (Ultrafilter Base))) :=
  if allocation then Ultrafilter.map (A v) U
  else Ultrafilter.map (fun a => pure (P v a)) U

lemma third_same_level {v w : Fin 3} (hvw : v ≠ w) (hlevel : level v = level w)
    (a c : ℕ) : G₃.Adj (A v a) (A w c) := by
  have hdirect : ∀ (v w : Fin 3), v ≠ w → level v = level w → ∀ (a c : ℕ),
      fubiniAdj G₂ (A v a) (A w c) := by
    intro v w hvw hlevel a c
    change {b | {d | G₂.Adj (pure (p v a b)) (pure (p w c d))} ∈ U} ∈ U
    apply Filter.mem_of_superset (tail (max a c))
    intro b hb
    change max a c < b at hb
    apply Filter.mem_of_superset (tail (max a c))
    intro d hd
    change max a c < d at hd
    apply pure_pure G₁ (ultrafilterGraph_cliqueFree _ _)
    exact first_cross hvw a b c d (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  exact ⟨hdirect v w hvw hlevel a c,hdirect w v hvw.symm hlevel.symm c a⟩

lemma third_different_level {v w : Fin 3} (hvw : level v < level w) (a c : ℕ) :
    G₃.Adj (A v a) (pure (P w c)) := by
  rw [adj_pure,A,Ultrafilter.mem_map]
  apply Filter.mem_of_superset (tail (max a c))
  intro b hb
  change max a c < b at hb
  change G₂.Adj (P w c) (pure (p v a b))
  rw [adj_pure,P,Ultrafilter.mem_map]
  apply Filter.mem_of_superset (tail (max b c))
  intro d hd
  change max b c < d at hd
  change G₁.Adj (p v a b) (p w c d)
  exact first_cross (fun he => (ne_of_lt hvw) (congrArg level he)) a b c d
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

lemma fourth_same_level {v w : Fin 3} (hvw : v ≠ w) (hlevel : level v = level w) :
    G₄.Adj (Z v true) (Z w true) := by
  constructor
  · change {a | {c | G₃.Adj (A v a) (A w c)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun a => Filter.Eventually.of_forall
      (fun c => third_same_level hvw hlevel a c))
  · change {c | {a | G₃.Adj (A w c) (A v a)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall
      (fun a => (third_same_level hvw hlevel a c).symm))

lemma fourth_different_level {v w : Fin 3} (hvw : level v < level w) :
    G₄.Adj (Z v true) (Z w false) := by
  constructor
  · change {a | {c | G₃.Adj (A v a) (pure (P w c))} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun a => Filter.Eventually.of_forall
      (fun c => third_different_level hvw a c))
  · change {c | {a | G₃.Adj (pure (P w c)) (A v a)} ∈ U} ∈ U
    exact Filter.Eventually.of_forall (fun c => Filter.Eventually.of_forall
      (fun a => (third_different_level hvw a c).symm))

/-- A genuine triangle is obtained with two different middle integration levels. -/
theorem fourth_triangle : G₄.Adj (Z 0 true) (Z 1 true) ∧
    G₄.Adj (Z 0 true) (Z 2 false) ∧ G₄.Adj (Z 1 true) (Z 2 false) :=
  ⟨fourth_same_level (by decide) (by decide),
    fourth_different_level (by decide),fourth_different_level (by decide)⟩

def lift₄ (S : Set Base) : Set (Ultrafilter (Ultrafilter (Ultrafilter Base))) :=
  {R | lift₃ S ∈ R}

theorem no_original_support (v : Fin 3) (allocation : Bool)
    (S : Set Base) (hS : (G.induce S).CliqueFree 3) : lift₄ S ∉ Z v allocation := by
  classical
  intro hm
  have hmem : {a | {b | {c | (v,triple a b c) ∈ S} ∈ U} ∈ U} ∈ U := by
    cases allocation <;> exact hm
  let T : ℕ → Set ℕ := fun a => {b | {c | (v,triple a b c) ∈ S} ∈ U}
  have hT : {a | T a ∈ U} ∈ U := hmem
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
  change (G.induce S).Adj ⟨(v,triple a b c),hx⟩ ⟨(v,triple b c d),hy⟩ ∧
    (G.induce S).Adj ⟨(v,triple a b c),hx⟩ ⟨(v,triple c d e),hz⟩ ∧
    (G.induce S).Adj ⟨(v,triple b c d),hy⟩ ⟨(v,triple c d e),hz⟩
  change G.Adj (v,triple a b c) (v,triple b c d) ∧
    G.Adj (v,triple a b c) (v,triple c d e) ∧
    G.Adj (v,triple b c d) (v,triple c d e)
  rw [triple_eq a b c hab hbc,triple_eq b c d hbc hcd,triple_eq c d e hcd hde]
  exact ⟨Or.inl ⟨rfl,Or.inl (Or.inl ⟨rfl,rfl⟩)⟩,
    Or.inl ⟨rfl,Or.inl (Or.inr rfl)⟩,Or.inl ⟨rfl,Or.inl (Or.inl ⟨rfl,rfl⟩)⟩⟩

def Bad : Set (Ultrafilter (Ultrafilter (Ultrafilter (Ultrafilter Base)))) :=
  {R | ∀ S, (G.induce S).CliqueFree 3 → lift₄ S ∉ R}

/-- Fourth-stage unsupported vertices can themselves form a triangle.
The subsequently completed ThirdBadTriangle.lean gives this already at stage three. -/
theorem unsupported_not_triangleFree : ¬(G₄.induce Bad).CliqueFree 3 := by
  classical
  intro h
  let x : Bad := ⟨Z 0 true,no_original_support 0 true⟩
  let y : Bad := ⟨Z 1 true,no_original_support 1 true⟩
  let z : Bad := ⟨Z 2 false,no_original_support 2 false⟩
  exact h _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G₄.induce Bad).Adj x y ∧ (G₄.induce Bad).Adj x z ∧
      (G₄.induce Bad).Adj y z from fourth_triangle))

def bit₀ (i : Fin 3) : Bool := decide (i = 1)
def bit₁ (i : Fin 3) : Bool := decide (i = 2)

lemma cut_ne (i j : Fin 3) (h : i ≠ j) : bit₀ i ≠ bit₀ j ∨ bit₁ i ≠ bit₁ j := by
  fin_cases i <;> fin_cases j <;> simp_all [bit₀,bit₁,Fin.ext_iff]

def piece (i : Fin 4) : SimpleGraph Base :=
  G ⊓ if i = 0 then (oneGraph ℕ).comap Prod.snd
    else if i = 1 then (twoGraph ℕ).comap Prod.snd
    else if i = 2 then (⊤ : SimpleGraph Bool).comap (bit₀ ∘ Prod.fst)
    else (⊤ : SimpleGraph Bool).comap (bit₁ ∘ Prod.fst)

lemma piece_cliqueFree (i : Fin 4) : (piece i).CliqueFree 3 := by
  have hbool : (⊤ : SimpleGraph Bool).CliqueFree 3 :=
    (SimpleGraph.Coloring.mk (G := (⊤ : SimpleGraph Bool)) id
      (fun h => h)).colorable.cliqueFree (by decide)
  fin_cases i
  · exact (triangleFree_comap _ (oneGraph_cliqueFree ℕ) Prod.snd).anti inf_le_right
  · exact (triangleFree_comap _ (twoGraph_cliqueFree ℕ) Prod.snd).anti inf_le_right
  · exact (triangleFree_comap _ hbool (bit₀ ∘ Prod.fst)).anti inf_le_right
  · exact (triangleFree_comap _ hbool (bit₁ ∘ Prod.fst)).anti inf_le_right

lemma four_pieces : G = ⨆ i : Fin 4, piece i := by
  ext x y
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro h
    have hG := h
    rcases h with ⟨he,(h | h) | (h | h)⟩ | ⟨hB,hrest⟩
    · exact ⟨0,hG,Or.inl h⟩
    · exact ⟨1,hG,Or.inl h⟩
    · exact ⟨0,hG,Or.inr h⟩
    · exact ⟨1,hG,Or.inr h⟩
    · rcases cut_ne _ _ hB with h | h
      · exact ⟨2,hG,h⟩
      · exact ⟨3,hG,h⟩
  · rintro ⟨i,hi⟩
    exact hi.1

/-- The fourth-stage obstruction nevertheless has a four-piece edge cover. -/
theorem fourth_four_pieces :
    ∃ K : Fin 4 → SimpleGraph (Ultrafilter (Ultrafilter (Ultrafilter (Ultrafilter Base)))),
      (∀ i, (K i).CliqueFree 3) ∧ G₄ = ⨆ i, K i := by
  obtain ⟨K₁,hK₁,he₁⟩ := ultrafilterGraph_finite_cover G G_cliqueFree
    piece piece_cliqueFree four_pieces
  obtain ⟨K₂,hK₂,he₂⟩ := ultrafilterGraph_finite_cover G₁
    (ultrafilterGraph_cliqueFree _ _) K₁ hK₁ he₁
  obtain ⟨K₃,hK₃,he₃⟩ := ultrafilterGraph_finite_cover G₂
    (ultrafilterGraph_cliqueFree _ _) K₂ hK₂ he₂
  exact ultrafilterGraph_finite_cover G₃
    (ultrafilterGraph_cliqueFree _ _) K₃ hK₃ he₃

#print axioms D_cliqueFree
#print axioms G_cliqueFree
#print axioms fourth_triangle
#print axioms no_original_support
#print axioms unsupported_not_triangleFree
#print axioms fourth_four_pieces
end Erdos595FourthBadTriangle
