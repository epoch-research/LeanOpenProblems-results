import Submission.ArcTwoCover

/-!
The arc/right-adjoint round trip preserves countable triangle-free edge
coverability. This is an obstruction to a candidate construction, not a
settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
open Erdos595Work Erdos595ArcAdjoint

namespace Erdos595ArcRoundTrip

variable {V : Type*} (G : SimpleGraph V)

abbrev R := right (arcGraph G)
abbrev B := Biclique (arcGraph G)

private def Pos (p : B G) : Prop :=
  ∃ v, (∀ e ∈ p.1.1, e.1.2 = v) ∧ ∀ e ∈ p.1.2, e.1.1 = v

private def Neg (p : B G) : Prop :=
  ∃ v, (∀ e ∈ p.1.1, e.1.1 = v) ∧ ∀ e ∈ p.1.2, e.1.2 = v

private theorem arc_ext {e f : Arc G} (ht : e.1.1 = f.1.1) (hh : e.1.2 = f.1.2) :
    e = f := Subtype.ext (Prod.ext ht hh)

/-- Adjacent arcs have at most one common neighbor. -/
private theorem common_unique {e f a b : Arc G}
    (hef : (arcGraph G).Adj e f) (hea : (arcGraph G).Adj e a)
    (hfa : (arcGraph G).Adj f a) (heb : (arcGraph G).Adj e b)
    (hfb : (arcGraph G).Adj f b) : a = b := by
  have he := e.2.ne
  have hf := f.2.ne
  have ha := a.2.ne
  have hb := b.2.ne
  rcases arc_triangle hef hea hfa with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;>
    rcases arc_triangle hef heb hfb with ⟨k1,k2,k3⟩ | ⟨k1,k2,k3⟩
  · exact arc_ext G (h2.symm.trans k2) (h3.trans k3.symm)
  · exact (ha (h2.symm.trans (k1.trans h3.symm))).elim
  · exact (hb (k2.symm.trans (h1.trans k3.symm))).elim
  · exact arc_ext G (h2.symm.trans k2) (h3.trans k3.symm)

private theorem left_independent (p : B G) (hB : ¬p.1.2.Subsingleton)
    {e f : Arc G} (he : e ∈ p.1.1) (hf : f ∈ p.1.1) :
    ¬(arcGraph G).Adj e f := by
  intro hef
  apply hB
  intro a ha b hb
  exact common_unique G hef (p.2 e he a ha) (p.2 f hf a ha)
    (p.2 e he b hb) (p.2 f hf b hb)

private theorem same_heads (p : B G) (hB : ¬p.1.2.Subsingleton)
    {e f : Arc G} (he : e ∈ p.1.1) (hf : f ∈ p.1.1)
    (hne : e ≠ f) (hh : e.1.2 = f.1.2) : Pos G p := by
  have ht : e.1.1 ≠ f.1.1 := fun h => hne (arc_ext G h hh)
  have hb : ∀ b ∈ p.1.2, b.1.1 = e.1.2 := by
    intro b hb
    rcases p.2 e he b hb with h | h
    · exact h.symm
    · rcases p.2 f hf b hb with k | k
      · exact k.symm.trans hh.symm
      · exact (ht (h.symm.trans k)).elim
  refine ⟨e.1.2, ?_, hb⟩
  intro a ha
  by_contra hn
  apply hB
  intro b hb' c hc'
  have hbh : b.1.2 = a.1.1 := (p.2 a ha b hb').resolve_left
    (fun h => hn (h.trans (hb b hb')))
  have hch : c.1.2 = a.1.1 := (p.2 a ha c hc').resolve_left
    (fun h => hn (h.trans (hb c hc')))
  exact arc_ext G ((hb b hb').trans (hb c hc').symm) (hbh.trans hch.symm)

private theorem same_tails (p : B G) (hB : ¬p.1.2.Subsingleton)
    {e f : Arc G} (he : e ∈ p.1.1) (hf : f ∈ p.1.1)
    (hne : e ≠ f) (ht : e.1.1 = f.1.1) : Neg G p := by
  have hh : e.1.2 ≠ f.1.2 := fun h => hne (arc_ext G ht h)
  have hb : ∀ b ∈ p.1.2, b.1.2 = e.1.1 := by
    intro b hb
    rcases p.2 e he b hb with h | h
    · rcases p.2 f hf b hb with k | k
      · exact (hh (h.trans k.symm)).elim
      · exact k.trans ht.symm
    · exact h
  refine ⟨e.1.1, ?_, hb⟩
  intro a ha
  by_contra hn
  apply hB
  intro b hb' c hc'
  have hbt : a.1.2 = b.1.1 := (p.2 a ha b hb').resolve_right
    (fun h => hn (h.symm.trans (hb b hb')))
  have hct : a.1.2 = c.1.1 := (p.2 a ha c hc').resolve_right
    (fun h => hn (h.symm.trans (hb c hc')))
  exact arc_ext G (hbt.symm.trans hct) ((hb b hb').trans (hb c hc').symm)

private def swap (p : B G) : B G :=
  ⟨(p.1.2,p.1.1), fun e he f hf => (p.2 f hf e he).symm⟩

private def Good (p : B G) : Prop :=
  ¬p.1.1.Subsingleton ∧ ¬p.1.2.Subsingleton ∧ ¬Pos G p ∧ ¬Neg G p

private theorem swap_good {p : B G} (h : Good G p) : Good G (swap G p) := by
  refine ⟨h.2.1,h.1,?_,?_⟩
  · rintro ⟨v,hA,hB⟩
    exact h.2.2.2 ⟨v,hB,hA⟩
  · rintro ⟨v,hA,hB⟩
    exact h.2.2.1 ⟨v,hB,hA⟩

private theorem left_tail_inj {p : B G} (h : Good G p)
    {e f : Arc G} (he : e ∈ p.1.1) (hf : f ∈ p.1.1)
    (ht : e.1.1 = f.1.1) : e = f := by
  by_contra hn
  exact h.2.2.2 (same_tails G p h.2.1 he hf hn ht)

private theorem left_head_inj {p : B G} (h : Good G p)
    {e f : Arc G} (he : e ∈ p.1.1) (hf : f ∈ p.1.1)
    (ht : e.1.2 = f.1.2) : e = f := by
  by_contra hn
  exact h.2.2.1 (same_heads G p h.2.1 he hf hn ht)

private theorem right_tail_inj {p : B G} (h : Good G p)
    {e f : Arc G} (he : e ∈ p.1.2) (hf : f ∈ p.1.2)
    (ht : e.1.1 = f.1.1) : e = f :=
  left_tail_inj G (swap_good G h) he hf ht

private theorem right_head_inj {p : B G} (h : Good G p)
    {e f : Arc G} (he : e ∈ p.1.2) (hf : f ∈ p.1.2)
    (ht : e.1.2 = f.1.2) : e = f :=
  left_head_inj G (swap_good G h) he hf ht

/-- In fact a triangle cannot contain two of the remaining bicliques. -/
private theorem no_triangle_two_good {p q r : B G} (hp : Good G p) (hq : Good G q)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r) (hqr : (R G).Adj q r) : False := by
  obtain ⟨e,heB,heA⟩ := hpq.1
  obtain ⟨e',he'B,he'A⟩ := hpq.2
  obtain ⟨f,hfB,hfA⟩ := hqr.1
  obtain ⟨g,hgB,hgA⟩ := hpr.2
  have hef := q.2 e heA f hfB
  have heg := p.2 g hgA e heB |>.symm
  have hfg := r.2 f hfA g hgB
  have hee' := q.2 e heA e' he'B
  rcases arc_triangle hef heg hfg with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
  · rcases hee' with h | h
    · have heq : e' = f := right_tail_inj G hq he'B hfB (h.symm.trans h1)
      exact left_independent G p hp.2.1 (heq ▸ he'A) hgA hfg
    · have heq : e' = g := left_head_inj G hp he'A hgA (h.trans h3.symm)
      exact left_independent G (swap G q) hq.1 hfB (heq ▸ he'B) hfg
  · rcases hee' with h | h
    · have heq : e' = g := left_tail_inj G hp he'A hgA (h.symm.trans h2)
      exact left_independent G (swap G q) hq.1 hfB (heq ▸ he'B) hfg
    · have heq : e' = f := right_head_inj G hq he'B hfB (h.trans h1.symm)
      exact left_independent G p hp.2.1 (heq ▸ he'A) hgA hfg

private theorem good_cliqueFree : ((R G).induce {p | Good G p}).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  exact no_triangle_two_good G p.2 q.2 hpq hpr hqr

private theorem cliqueFree_cover {W : Type*} (H : SimpleGraph W) (hH : H.CliqueFree 3) :
    IsCountableUnionOfTriangleFree H := ⟨fun _ => H, fun _ => hH, by simp⟩

private theorem arc_cover : IsCountableUnionOfTriangleFree (arcGraph G) := by
  classical
  obtain ⟨H,K,hH,hK,hcov⟩ := arc_two_cover G
  refine ⟨fun n => if n = 0 then H else K, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs <;> assumption
  · rw [hcov]
    ext x y
    rw [SimpleGraph.sup_adj, SimpleGraph.iSup_adj]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    · rintro ⟨n,h⟩
      split_ifs at h
      · exact Or.inl h
      · exact Or.inr h

private noncomputable def pick [Nonempty (Arc G)] (S : Set (Arc G)) : Arc G := by
  classical
  exact if h : S.Nonempty then h.choose else Classical.arbitrary _

private theorem pick_mem [Nonempty (Arc G)] {S : Set (Arc G)} (hS : S.Nonempty) :
    pick G S ∈ S := by simp only [pick, dif_pos hS]; exact hS.choose_spec

private noncomputable def small_left_hom [Nonempty (Arc G)] :
    (R G).induce {p | p.1.1.Subsingleton} →g arcGraph G where
  toFun p := pick G p.1.1.1
  map_rel' := by
    intro p q hpq
    obtain ⟨e,heB,heA⟩ := hpq.1
    obtain ⟨f,hfB,hfA⟩ := hpq.2
    have hpm := pick_mem G ⟨f,hfA⟩
    have hqm := pick_mem G ⟨e,heA⟩
    have heq := q.2 heA hqm
    exact heq ▸ p.1.2 _ hpm e heB

private noncomputable def small_right_hom [Nonempty (Arc G)] :
    (R G).induce {p | p.1.2.Subsingleton} →g arcGraph G where
  toFun p := pick G p.1.1.2
  map_rel' := by
    intro p q hpq
    obtain ⟨e,heB,heA⟩ := hpq.1
    obtain ⟨f,hfB,hfA⟩ := hpq.2
    have hpm := pick_mem G ⟨e,heB⟩
    have hqm := pick_mem G ⟨f,hfB⟩
    have heq := p.2 heB hpm
    have hadj := q.1.2 e heA (pick G q.1.1.2) hqm
    rwa [heq] at hadj

private noncomputable def pos_hom : (R G).induce {p | Pos G p} →g G where
  toFun p := p.2.choose
  map_rel' := by
    intro p q hpq
    obtain ⟨e,heB,heA⟩ := hpq.1
    have h₁ := p.2.choose_spec.2 e heB
    have h₂ := q.2.choose_spec.1 e heA
    exact h₁ ▸ h₂ ▸ e.2

private noncomputable def neg_hom : (R G).induce {p | Neg G p} →g G where
  toFun p := p.2.choose
  map_rel' := by
    intro p q hpq
    obtain ⟨e,heB,heA⟩ := hpq.1
    have h₁ := p.2.choose_spec.2 e heB
    have h₂ := q.2.choose_spec.1 e heA
    exact h₁ ▸ h₂ ▸ e.2.symm

/-- A finite cover by coverable induced subgraphs is sufficient; edges
between the pieces can be handled by binary cuts. -/
private theorem cover_of_finite_vertex_cover {W I : Type*} [Finite I]
    (H : SimpleGraph W) (S : I → Set W) (hS : ∀ i, IsCountableUnionOfTriangleFree (H.induce (S i)))
    (hall : ∀ w, ∃ i, w ∈ S i) : IsCountableUnionOfTriangleFree H := by
  classical
  choose tag htag using hall
  obtain ⟨enc,henc⟩ := exists_injective_nat I
  let code : I → ℕ → Fin 2 := fun i n => if enc i = n then 1 else 0
  have hcode : Function.Injective code := by
    intro i j hij
    apply henc
    have h := congrFun hij (enc i)
    by_contra hn
    have hji : enc j ≠ enc i := Ne.symm hn
    simp [code, hji] at h
  let f : W → ℕ → Fin 2 := fun w => code (tag w)
  apply countable_union_of_vertex_pieces H f
  intro b
  by_cases hb : ∃ w, f w = b
  · obtain ⟨w₀,hw₀⟩ := hb
    have hv : ∀ w, f w = b → w ∈ S (tag w₀) := by
      intro w hw
      have he : tag w = tag w₀ := hcode (hw.trans hw₀.symm)
      exact he ▸ htag w
    let g : vertexPiece H f b →g H.induce (S (tag w₀)) :=
      { toFun := fun w => if h : w ∈ S (tag w₀) then ⟨w,h⟩ else ⟨w₀,htag w₀⟩
        map_rel' := by
          intro x y hxy
          rw [dif_pos (hv x hxy.2.1), dif_pos (hv y hxy.2.2)]
          exact hxy.1 }
    exact countable_union_of_hom g (hS (tag w₀))
  · have hbot : vertexPiece H f b = ⊥ := by
      ext x y
      exact ⟨fun h => hb ⟨x,h.2.1⟩, False.elim⟩
    rw [hbot]
    exact cliqueFree_cover _ (SimpleGraph.cliqueFree_bot (by omega))

/-- The arc/right-adjoint round trip cannot destroy a countable
triangle-free edge cover, even without a clique-bound assumption. -/
theorem right_arc_cover (hG : IsCountableUnionOfTriangleFree G) :
    IsCountableUnionOfTriangleFree (right (arcGraph G)) := by
  classical
  by_cases hn : Nonempty (Arc G)
  · letI := hn
    let S : Fin 5 → Set (B G) := ![
      {p | p.1.1.Subsingleton}, {p | p.1.2.Subsingleton},
      {p | Pos G p}, {p | Neg G p}, {p | Good G p}]
    apply cover_of_finite_vertex_cover (R G) S
    · intro i
      fin_cases i
      · exact countable_union_of_hom (small_left_hom G) (arc_cover G)
      · exact countable_union_of_hom (small_right_hom G) (arc_cover G)
      · exact countable_union_of_hom (pos_hom G) hG
      · exact countable_union_of_hom (neg_hom G) hG
      · exact cliqueFree_cover _ (good_cliqueFree G)
    · intro p
      by_cases hA : p.1.1.Subsingleton
      · exact ⟨0,hA⟩
      by_cases hB : p.1.2.Subsingleton
      · exact ⟨1,hB⟩
      by_cases hp : Pos G p
      · exact ⟨2,hp⟩
      by_cases hm : Neg G p
      · exact ⟨3,hm⟩
      exact ⟨4,hA,hB,hp,hm⟩
  · have hbot : right (arcGraph G) = ⊥ := by
      ext p q
      exact ⟨fun h => hn ⟨h.1.choose⟩, False.elim⟩
    rw [hbot]
    exact cliqueFree_cover _ (SimpleGraph.cliqueFree_bot (by omega))

theorem right_arc_cover_iff :
    IsCountableUnionOfTriangleFree (right (arcGraph G)) ↔
      IsCountableUnionOfTriangleFree G :=
  ⟨countable_union_of_hom (unit G), right_arc_cover G⟩

#print axioms right_arc_cover
#print axioms right_arc_cover_iff

#print axioms good_cliqueFree

/-- A common neighbor of arcs with distinct tails has one of just two tails. -/
theorem common_tail_two {p q a : Arc G} (hpq : p.1.1 ≠ q.1.1)
    (hap : (arcGraph G).Adj a p) (haq : (arcGraph G).Adj a q) :
    a.1.1 = p.1.2 ∨ a.1.1 = q.1.2 := by
  rcases hap with h | h
  · rcases haq with k | k
    · exact (hpq (h.symm.trans k)).elim
    · exact Or.inr k.symm
  · exact Or.inl h.symm

/-- The three common neighbors cannot have three different tails. -/
theorem common_tails_three {p q a b c : Arc G} (hpq : p.1.1 ≠ q.1.1)
    (hap : (arcGraph G).Adj a p) (haq : (arcGraph G).Adj a q)
    (hbp : (arcGraph G).Adj b p) (hbq : (arcGraph G).Adj b q)
    (hcp : (arcGraph G).Adj c p) (hcq : (arcGraph G).Adj c q) :
    a.1.1 = b.1.1 ∨ a.1.1 = c.1.1 ∨ b.1.1 = c.1.1 := by
  rcases common_tail_two G hpq hap haq with h | h <;>
    rcases common_tail_two G hpq hbp hbq with k | k <;>
    rcases common_tail_two G hpq hcp hcq with l | l <;> aesop

/-- Even the five-vertex alternating K3,2 pattern is absent when arc tails
are increasing. This holds for every base graph, with no clique bound. -/
theorem no_alternating_five [LinearOrder V] {p q r s t : Arc G}
    (hpq : p.1.1 < q.1.1) (hqr : q.1.1 < r.1.1)
    (hrs : r.1.1 < s.1.1) (hst : s.1.1 < t.1.1)
    (apq : (arcGraph G).Adj p q) (aps : (arcGraph G).Adj p s)
    (arq : (arcGraph G).Adj r q) (ars : (arcGraph G).Adj r s)
    (atq : (arcGraph G).Adj t q) (ats : (arcGraph G).Adj t s) : False := by
  rcases common_tails_three G (hqr.trans hrs).ne apq aps arq ars atq ats with h | h | h
  · exact (hpq.trans hqr).ne h
  · exact (hpq.trans (hqr.trans (hrs.trans hst))).ne h
  · exact (hrs.trans hst).ne h

private theorem small_left_no_four {W : Type*} {H : SimpleGraph W}
    (hH : H.CliqueFree 4) {p q r s : Biclique H} (hp : p.1.1.Subsingleton)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hps : (right H).Adj p s) (hqr : (right H).Adj q r)
    (hqs : (right H).Adj q s) (hrs : (right H).Adj r s) : False := by
  obtain ⟨e,heq,hep⟩ := hpq.2
  have hqe : e ∈ q.1.2 := heq
  have hre : e ∈ r.1.2 := by
    obtain ⟨f,hfr,hfp⟩ := hpr.2
    exact hp hfp hep ▸ hfr
  have hse : e ∈ s.1.2 := by
    obtain ⟨f,hfs,hfp⟩ := hps.2
    exact hp hfp hep ▸ hfs
  obtain ⟨x,hxq,hxr⟩ := hqr.1
  obtain ⟨y,hyr,hys⟩ := hrs.1
  obtain ⟨z,hzs,hzq⟩ := hqs.2
  exact no_adj_common_neighbors hH
    (q.2 z hzq e hqe) (q.2 z hzq x hxq)
    (r.2 x hxr e hre).symm (s.2 y hys z hzs).symm
    (s.2 y hys e hse).symm (r.2 x hxr y hyr)

private theorem swap_adj {p q : B G} (h : (R G).Adj p q) :
    (R G).Adj (swap G p) (swap G q) := by
  obtain ⟨⟨e,heB,heA⟩,⟨f,hfB,hfA⟩⟩ := h
  exact ⟨⟨f,hfA,hfB⟩,⟨e,heA,heB⟩⟩

private theorem small_right_no_four {p q r s : B G} (hp : p.1.2.Subsingleton)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) : False :=
  small_left_no_four (arc_cliqueFree_four G) (p := swap G p) hp
    (swap_adj G hpq) (swap_adj G hpr) (swap_adj G hps)
    (swap_adj G hqr) (swap_adj G hqs) (swap_adj G hrs)

private theorem good_left_three {p : B G} (hp : Good G p) {e f g : Arc G}
    (he : e ∈ p.1.1) (hf : f ∈ p.1.1) (hg : g ∈ p.1.1) :
    e = f ∨ e = g ∨ f = g := by
  obtain ⟨b,hb,c,hc,hbc⟩ := Set.not_subsingleton_iff.mp hp.2.1
  rcases p.2 e he b hb with h | h <;>
    rcases p.2 f hf b hb with k | k <;>
    rcases p.2 g hg b hb with l | l
  · exact Or.inl (left_head_inj G hp he hf (h.trans k.symm))
  · exact Or.inl (left_head_inj G hp he hf (h.trans k.symm))
  · exact Or.inr (Or.inl (left_head_inj G hp he hg (h.trans l.symm)))
  · exact Or.inr (Or.inr (left_tail_inj G hp hf hg (k.symm.trans l)))
  · exact Or.inr (Or.inr (left_head_inj G hp hf hg (k.trans l.symm)))
  · exact Or.inr (Or.inl (left_tail_inj G hp he hg (h.symm.trans l)))
  · exact Or.inl (left_tail_inj G hp he hf (h.symm.trans k))
  · exact Or.inl (left_tail_inj G hp he hf (h.symm.trans k))

private theorem pos_neg_pos {p q r : B G} (hp : Pos G p) (hq : Neg G q)
    (hr : Pos G r) (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : False := by
  obtain ⟨u,huA,huB⟩ := hp
  obtain ⟨v,hvA,hvB⟩ := hq
  obtain ⟨w,hwA,hwB⟩ := hr
  obtain ⟨e,heB,heA⟩ := hpq.1
  obtain ⟨f,hfB,hfA⟩ := hqr.2
  obtain ⟨g,hgB,hgA⟩ := hpr.1
  have huv : u = v := (huB e heB).symm.trans (hvA e heA)
  have hwv : w = v := (hwB f hfB).symm.trans (hvA f hfA)
  exact g.2.ne ((huB g hgB).trans (huv.trans (hwv.symm.trans (hwA g hgA).symm)))

private theorem neg_pos_neg {p q r : B G} (hp : Neg G p) (hq : Pos G q)
    (hr : Neg G r) (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : False := by
  apply pos_neg_pos G (p := swap G p) (q := swap G q) (r := swap G r)
  · obtain ⟨v,hA,hB⟩ := hp; exact ⟨v,hB,hA⟩
  · obtain ⟨v,hA,hB⟩ := hq; exact ⟨v,hB,hA⟩
  · obtain ⟨v,hA,hB⟩ := hr; exact ⟨v,hB,hA⟩
  · exact swap_adj G hpq
  · exact swap_adj G hpr
  · exact swap_adj G hqr

private theorem triangle_uniform {p q r : B G}
    (hp : Pos G p ∨ Neg G p) (hq : Pos G q ∨ Neg G q)
    (hr : Pos G r ∨ Neg G r) (hpq : (R G).Adj p q)
    (hpr : (R G).Adj p r) (hqr : (R G).Adj q r) :
    (Pos G p ∧ Pos G q ∧ Pos G r) ∨ (Neg G p ∧ Neg G q ∧ Neg G r) := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr
  · exact Or.inl ⟨hp,hq,hr⟩
  · exact (pos_neg_pos G hp hr hq hpr hpq hqr.symm).elim
  · exact (pos_neg_pos G hp hq hr hpq hpr hqr).elim
  · exact (neg_pos_neg G hq hp hr hpq.symm hqr hpr).elim
  · exact (pos_neg_pos G hq hp hr hpq.symm hqr hpr).elim
  · exact (neg_pos_neg G hp hq hr hpq hpr hqr).elim
  · exact (neg_pos_neg G hp hr hq hpr hpq hqr.symm).elim
  · exact Or.inr ⟨hp,hq,hr⟩

private theorem good_no_pos_triangle {p q r s : B G} (hp : Good G p)
    (hq : Pos G q) (hr : Pos G r) (hs : Pos G s)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) : False := by
  obtain ⟨e,heB,heA⟩ := hpq.2
  obtain ⟨f,hfB,hfA⟩ := hpr.2
  obtain ⟨g,hgB,hgA⟩ := hps.2
  have hneq : ∀ {a b : B G}, Pos G a → Pos G b → (R G).Adj a b →
      ∀ {x y : Arc G}, x ∈ a.1.2 → y ∈ b.1.2 → x ≠ y := by
    rintro a b ⟨u,huA,huB⟩ ⟨v,hvA,hvB⟩ hab x y hx hy rfl
    obtain ⟨z,hza,hzb⟩ := hab.1
    exact z.2.ne ((huB z hza).trans
      ((huB x hx).symm.trans ((hvB x hy).trans (hvA z hzb).symm)))
  rcases good_left_three G hp heA hfA hgA with h | h | h
  · exact hneq hq hr hqr heB hfB h
  · exact hneq hq hs hqs heB hgB h
  · exact hneq hr hs hrs hfB hgB h

private theorem good_no_neg_triangle {p q r s : B G} (hp : Good G p)
    (hq : Neg G q) (hr : Neg G r) (hs : Neg G s)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) : False := by
  apply good_no_pos_triangle G (q := swap G q) (r := swap G r)
    (s := swap G s) (swap_good G hp)
  · obtain ⟨v,hA,hB⟩ := hq; exact ⟨v,hB,hA⟩
  · obtain ⟨v,hA,hB⟩ := hr; exact ⟨v,hB,hA⟩
  · obtain ⟨v,hA,hB⟩ := hs; exact ⟨v,hB,hA⟩
  · exact swap_adj G hpq
  · exact swap_adj G hpr
  · exact swap_adj G hps
  · exact swap_adj G hqr
  · exact swap_adj G hqs
  · exact swap_adj G hrs

private theorem pos_or_neg {p : B G} (hA : ¬p.1.1.Subsingleton)
    (hB : ¬p.1.2.Subsingleton) (hn : ¬Good G p) : Pos G p ∨ Neg G p := by
  by_contra h
  exact hn ⟨hA,hB,fun hp => h (Or.inl hp),fun hp => h (Or.inr hp)⟩

private theorem good_no_four {p q r s : B G} (hp : Good G p)
    (hqA : ¬q.1.1.Subsingleton) (hqB : ¬q.1.2.Subsingleton)
    (hrA : ¬r.1.1.Subsingleton) (hrB : ¬r.1.2.Subsingleton)
    (hsA : ¬s.1.1.Subsingleton) (hsB : ¬s.1.2.Subsingleton)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) : False := by
  have hq := pos_or_neg G hqA hqB
    (fun h => no_triangle_two_good G hp h hpq hpr hqr)
  have hr := pos_or_neg G hrA hrB
    (fun h => no_triangle_two_good G hp h hpr hpq hqr.symm)
  have hs := pos_or_neg G hsA hsB
    (fun h => no_triangle_two_good G hp h hps hpq hqs.symm)
  rcases triangle_uniform G hq hr hs hqr hqs hrs with ⟨hq,hr,hs⟩ | ⟨hq,hr,hs⟩
  · exact good_no_pos_triangle G hp hq hr hs hpq hpr hps hqr hqs hrs
  · exact good_no_neg_triangle G hp hq hr hs hpq hpr hps hqr hqs hrs

private theorem nonsmall_in_four {p q r s : B G}
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) :
    ¬p.1.1.Subsingleton ∧ ¬p.1.2.Subsingleton :=
  ⟨fun h => small_left_no_four (arc_cliqueFree_four G) h hpq hpr hps hqr hqs hrs,
   fun h => small_right_no_four G h hpq hpr hps hqr hqs hrs⟩

private theorem posneg_in_four {p q r s : B G}
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) : Pos G p ∨ Neg G p := by
  have hp := nonsmall_in_four G hpq hpr hps hqr hqs hrs
  have hq := nonsmall_in_four G hpq.symm hqr hqs hpr hps hrs
  have hr := nonsmall_in_four G hpr.symm hqr.symm hrs hpq hps hqs
  have hs := nonsmall_in_four G hps.symm hqs.symm hrs.symm hpq hpr hqr
  exact pos_or_neg G hp.1 hp.2
    (fun h => good_no_four G h hq.1 hq.2 hr.1 hr.2 hs.1 hs.2 hpq hpr hps hqr hqs hrs)

private theorem right_arc_no_four (hG : G.CliqueFree 4) {p q r s : B G}
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hps : (R G).Adj p s) (hqr : (R G).Adj q r)
    (hqs : (R G).Adj q s) (hrs : (R G).Adj r s) : False := by
  have hp := posneg_in_four G hpq hpr hps hqr hqs hrs
  have hq := posneg_in_four G hpq.symm hqr hqs hpr hps hrs
  have hr := posneg_in_four G hpr.symm hqr.symm hrs hpq hps hqs
  have hs := posneg_in_four G hps.symm hqs.symm hrs.symm hpq hpr hqr
  rcases triangle_uniform G hp hq hr hpq hpr hqr with ⟨hp,hq,hr⟩ | ⟨hp,hq,hr⟩
  · rcases hs with hs | hs
    · let f := pos_hom G
      have h : ∀ {a b : B G} (ha : Pos G a) (hb : Pos G b),
          (R G).Adj a b → G.Adj (f ⟨a,ha⟩) (f ⟨b,hb⟩) :=
        fun {_ _} _ _ hab => f.map_adj hab
      exact no_adj_common_neighbors hG (h hp hq hpq) (h hp hr hpr)
        (h hq hr hqr) (h hp hs hps) (h hq hs hqs) (h hr hs hrs)
    · exact pos_neg_pos G hp hs hq hps hpq hqs.symm
  · rcases hs with hs | hs
    · exact neg_pos_neg G hp hs hq hps hpq hqs.symm
    · let f := neg_hom G
      have h : ∀ {a b : B G} (ha : Neg G a) (hb : Neg G b),
          (R G).Adj a b → G.Adj (f ⟨a,ha⟩) (f ⟨b,hb⟩) :=
        fun {_ _} _ _ hab => f.map_adj hab
      exact no_adj_common_neighbors hG (h hp hq hpq) (h hp hr hpr)
        (h hq hr hqr) (h hp hs hps) (h hq hs hqs) (h hr hs hrs)

/-- In contrast to a general right adjoint, the arc/right round trip
preserves K4-freeness. Together with `right_arc_cover_iff`, this construction
preserves both conditions of the Erdős problem. It is not a witness. -/
theorem right_arc_cliqueFree (hG : G.CliqueFree 4) :
    (right (arcGraph G)).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have h (i j : Fin 4) (hij : i ≠ j) : (R G).Adj (e i) (e j) :=
    e.map_rel_iff.mpr hij
  exact right_arc_no_four G hG (h 0 1 (by decide)) (h 0 2 (by decide))
    (h 0 3 (by decide)) (h 1 2 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))

/-- The K4-free restriction is reflected as well as preserved. -/
theorem right_arc_cliqueFree_iff :
    (right (arcGraph G)).CliqueFree 4 ↔ G.CliqueFree 4 := by
  refine ⟨?_,right_arc_cliqueFree G⟩
  intro hG
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have h (i j : Fin 4) (hij : i ≠ j) : (R G).Adj (unit G (e i)) (unit G (e j)) :=
    (unit G).map_adj (e.map_rel_iff.mpr hij)
  exact no_adj_common_neighbors hG (h 0 1 (by decide)) (h 0 2 (by decide))
    (h 1 2 (by decide)) (h 0 3 (by decide)) (h 1 3 (by decide)) (h 2 3 (by decide))

/-- An arc homomorphism from the four-clique's arc graph already forces
a four-clique in the original graph. -/
theorem arc_four_hom_iff :
    Nonempty (arcGraph (⊤ : SimpleGraph (Fin 4)) →g arcGraph G) ↔ ¬G.CliqueFree 4 := by
  rw [← right_not_cliqueFree_iff, right_arc_cliqueFree_iff]

#print axioms common_tail_two
#print axioms common_tails_three
#print axioms no_alternating_five
#print axioms right_arc_cliqueFree
#print axioms right_arc_cliqueFree_iff
#print axioms arc_four_hom_iff

/-- The diamond-free condition used to reflect triangle-connected sources. -/
def UniqueTriangleEdge : Prop :=
  ∀ ⦃a b c d : V⦄, G.Adj a b → G.Adj a c → G.Adj b c →
    G.Adj a d → G.Adj b d → c = d

private theorem exists_other {A : Type*} {S : Set A} (h : ¬S.Subsingleton)
    (a : A) : ∃ b ∈ S, b ≠ a := by
  obtain ⟨b,hb,c,hc,hbc⟩ := Set.not_subsingleton_iff.mp h
  by_cases hba : b = a
  · exact ⟨c,hc,fun hca => hbc (hba.trans hca.symm)⟩
  · exact ⟨b,hb,hba⟩

private theorem good_no_forward (hG : UniqueTriangleEdge G) {p : B G}
    (hp : Good G p) {e f g : Arc G} (he : e ∈ p.1.1) (hf : f ∈ p.1.2)
    (h₁ : e.1.2 = f.1.1) (h₂ : f.1.2 = g.1.1) (h₃ : g.1.2 = e.1.1) : False := by
  obtain ⟨e',he',hne⟩ := exists_other hp.1 e
  obtain ⟨f',hf',hnf⟩ := exists_other hp.2.1 f
  have he't : e'.1.1 = f.1.2 := by
    rcases p.2 e' he' f hf with h | h
    · exact (hne (left_head_inj G hp he' he (h.trans h₁.symm))).elim
    · exact h.symm
  have hf'h : f'.1.2 = e.1.1 := by
    rcases p.2 e he f' hf' with h | h
    · exact (hnf (right_tail_inj G hp hf' hf (h.symm.trans h₁))).elim
    · exact h
  have he'h : e'.1.2 = f'.1.1 := by
    rcases p.2 e' he' f' hf' with h | h
    · exact h
    · exact (g.2.ne (h₂.symm.trans (he't.symm.trans (h.symm.trans (hf'h.trans h₃.symm))))).elim
  have hac : G.Adj e.1.1 f.1.2 := by
    simpa only [h₂,h₃] using g.2.symm
  have hcb : G.Adj f.1.2 e.1.2 := h₁.symm ▸ f.2.symm
  have had : G.Adj e.1.1 e'.1.2 := by
    simpa only [he'h,hf'h] using f'.2.symm
  have hcd : G.Adj f.1.2 e'.1.2 := he't ▸ e'.2
  have hbd := hG hac e.2 hcb had hcd
  exact hne (left_head_inj G hp he' he hbd.symm)

private theorem good_no_triangle (hG : UniqueTriangleEdge G) {p q r : B G}
    (hp : Good G p) (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : False := by
  obtain ⟨e,heB,heA⟩ := hpq.1
  obtain ⟨f,hfB,hfA⟩ := hqr.1
  obtain ⟨g,hgB,hgA⟩ := hpr.2
  have hge := p.2 g hgA e heB
  have hgf := (r.2 f hfA g hgB).symm
  have hef := q.2 e heA f hfB
  rcases arc_triangle hge hgf hef with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩
  · exact good_no_forward G hG hp hgA heB h₁ h₂ h₃
  · exact good_no_forward G hG (swap_good G hp) heB hgA h₁ h₂ h₃

private theorem small_left_triangle {p q r : B G} (hp : p.1.1.Subsingleton)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : q.1.1.Subsingleton := by
  by_contra hq
  obtain ⟨e,heq,hep⟩ := hpq.2
  obtain ⟨e',her,he'p⟩ := hpr.2
  have he'r : e ∈ r.1.2 := hp he'p hep ▸ her
  obtain ⟨f,hfq,hfr⟩ := hqr.1
  exact left_independent G (swap G q) hq hfq heq (r.2 f hfr e he'r)

private theorem small_right_triangle {p q r : B G} (hp : p.1.2.Subsingleton)
    (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : q.1.2.Subsingleton :=
  small_left_triangle G (p := swap G p) hp (swap_adj G hpq)
    (swap_adj G hpr) (swap_adj G hqr)

private def RichPos (p : B G) : Prop :=
  ¬p.1.1.Subsingleton ∧ ¬p.1.2.Subsingleton ∧ Pos G p
private def RichNeg (p : B G) : Prop :=
  ¬p.1.1.Subsingleton ∧ ¬p.1.2.Subsingleton ∧ Neg G p

private theorem pos_neg_small {p : B G} (hp : Pos G p) (hn : Neg G p) :
    p.1.1.Subsingleton := by
  obtain ⟨v,hv,_⟩ := hp
  obtain ⟨w,hw,_⟩ := hn
  intro e he f hf
  exact arc_ext G ((hw e he).trans (hw f hf).symm) ((hv e he).trans (hv f hf).symm)

private theorem rich_pos_triangle (hG : UniqueTriangleEdge G) {p q r : B G}
    (hp : RichPos G p) (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : RichPos G q := by
  have hqa : ¬q.1.1.Subsingleton := fun h =>
    hp.1 (small_left_triangle G h hpq.symm hqr hpr)
  have hqb : ¬q.1.2.Subsingleton := fun h =>
    hp.2.1 (small_right_triangle G h hpq.symm hqr hpr)
  have hra : ¬r.1.1.Subsingleton := fun h =>
    hp.1 (small_left_triangle G h hpr.symm hqr.symm hpq)
  have hrb : ¬r.1.2.Subsingleton := fun h =>
    hp.2.1 (small_right_triangle G h hpr.symm hqr.symm hpq)
  have hq := pos_or_neg G hqa hqb (fun h => good_no_triangle G hG h hpq.symm hqr hpr)
  have hr := pos_or_neg G hra hrb (fun h => good_no_triangle G hG h hpr.symm hqr.symm hpq)
  rcases triangle_uniform G (Or.inl hp.2.2) hq hr hpq hpr hqr with h | h
  · exact ⟨hqa,hqb,h.2.1⟩
  · exact (hp.1 (pos_neg_small G hp.2.2 h.1)).elim

private theorem rich_neg_triangle (hG : UniqueTriangleEdge G) {p q r : B G}
    (hp : RichNeg G p) (hpq : (R G).Adj p q) (hpr : (R G).Adj p r)
    (hqr : (R G).Adj q r) : RichNeg G q := by
  have hp' : RichPos G (swap G p) := by
    obtain ⟨v,hA,hB⟩ := hp.2.2
    exact ⟨hp.2.1,hp.1,v,hB,hA⟩
  have h := rich_pos_triangle G hG hp' (swap_adj G hpq) (swap_adj G hpr) (swap_adj G hqr)
  obtain ⟨v,hA,hB⟩ := h.2.2
  exact ⟨h.2.1,h.1,v,hB,hA⟩

/-- Projection of an arc onto its tail is a graph homomorphism. -/
def tailHom : arcGraph G →g G where
  toFun e := e.1.1
  map_rel' := by
    intro e f h
    rcases h with h | h
    · exact h ▸ e.2
    · exact h ▸ f.2.symm

/-- A triangle-connected source mapping into the arc/right round trip of
 a diamond-free graph already maps into that graph. The hypothesis on
 predicates is connectivity using only edges that occur in triangles. -/
theorem triangle_connected_hom {A : Type*} (F : SimpleGraph A) (a₀ : A)
    (htri : ∃ b c, F.Adj a₀ b ∧ F.Adj a₀ c ∧ F.Adj b c)
    (hconn : ∀ P : A → Prop, P a₀ →
      (∀ a b c, F.Adj a b → F.Adj a c → F.Adj b c → P a → P b) → ∀ a, P a)
    (hG : UniqueTriangleEdge G) (f : F →g R G) : Nonempty (F →g G) := by
  classical
  obtain ⟨b,c,hab,hac,hbc⟩ := htri
  have hpq := f.map_adj hab
  have hpr := f.map_adj hac
  have hqr := f.map_adj hbc
  obtain ⟨e,_,_⟩ := hpq.1
  letI : Nonempty (Arc G) := ⟨e⟩
  by_cases hA : (f a₀).1.1.Subsingleton
  · have hall := hconn (fun a => (f a).1.1.Subsingleton) hA (by
      intro a b c hab hac hbc ha
      exact small_left_triangle G ha (f.map_adj hab) (f.map_adj hac) (f.map_adj hbc))
    let g : F →g (R G).induce {p | p.1.1.Subsingleton} :=
      ⟨fun a => ⟨f a,hall a⟩,fun h => f.map_adj h⟩
    exact ⟨(tailHom G).comp ((small_left_hom G).comp g)⟩
  by_cases hB : (f a₀).1.2.Subsingleton
  · have hall := hconn (fun a => (f a).1.2.Subsingleton) hB (by
      intro a b c hab hac hbc ha
      exact small_right_triangle G ha (f.map_adj hab) (f.map_adj hac) (f.map_adj hbc))
    let g : F →g (R G).induce {p | p.1.2.Subsingleton} :=
      ⟨fun a => ⟨f a,hall a⟩,fun h => f.map_adj h⟩
    exact ⟨(tailHom G).comp ((small_right_hom G).comp g)⟩
  have hpn := pos_or_neg G hA hB (fun h => good_no_triangle G hG h hpq hpr hqr)
  rcases hpn with hp | hn
  · have hall := hconn (fun a => RichPos G (f a)) ⟨hA,hB,hp⟩ (by
      intro a b c hab hac hbc ha
      exact rich_pos_triangle G hG ha (f.map_adj hab) (f.map_adj hac) (f.map_adj hbc))
    let g : F →g (R G).induce {p | Pos G p} :=
      ⟨fun a => ⟨f a,(hall a).2.2⟩,fun h => f.map_adj h⟩
    exact ⟨(pos_hom G).comp g⟩
  · have hall := hconn (fun a => RichNeg G (f a)) ⟨hA,hB,hn⟩ (by
      intro a b c hab hac hbc ha
      exact rich_neg_triangle G hG ha (f.map_adj hab) (f.map_adj hac) (f.map_adj hbc))
    let g : F →g (R G).induce {p | Neg G p} :=
      ⟨fun a => ⟨f a,(hall a).2.2⟩,fun h => f.map_adj h⟩
    exact ⟨(neg_hom G).comp g⟩

theorem arc_unique_triangle_edge : UniqueTriangleEdge (arcGraph G) := by
  intro a b c d hab hac hbc had hbd
  exact common_unique G hab hac hbc had hbd

#print axioms triangle_connected_hom
#print axioms arc_unique_triangle_edge

end Erdos595ArcRoundTrip
