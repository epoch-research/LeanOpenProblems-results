import Submission.NoAlternatingBiclique
import Submission.MiddleCornerObstruction

/-!
The no-alternating-C4 order property is preserved by the biclique right
adjoint, after choosing a new order. In particular, its countable-cover
obstruction persists through every finite right-adjoint iteration.
This is auxiliary work, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
open Erdos595ArcAdjoint Erdos595Work Erdos595NoAlternating
namespace Erdos595NoAlternatingIteration

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

/-- At overlapping inner sides, a common exterior point is on the same
side of both of them. -/
private theorem outside_overlap {A B C D : Set V}
    (hA : Erdos595NoAlternating.Inner A C) (hB : Erdos595NoAlternating.Inner B D) (hAB : (A ∩ B).Nonempty)
    {x a b : V} (hxC : x ∈ C) (hxD : x ∈ D) (ha : a ∈ A) (hb : b ∈ B) :
    (x < a ∧ x < b) ∨ (a < x ∧ b < x) := by
  obtain ⟨t,htA,htB⟩ := hAB
  rcases hA x hxC with h | h <;> rcases hB x hxD with k | k
  · exact Or.inl ⟨h a ha,k b hb⟩
  · exact (lt_asymm (h t htA) (k t htB)).elim
  · exact (lt_asymm (k t htB) (h t htA)).elim
  · exact Or.inr ⟨h a ha,k b hb⟩

private theorem witness_left (p q : Biclique G)
    (hp : Erdos595NoAlternating.Inner p.1.1 p.1.2) (hq : Erdos595NoAlternating.Inner q.1.1 q.1.2)
    (hcut : cut p.1.1 ≤ cut q.1.1) (hpq : (right G).Adj p q)
    {x : V} (hxp : x ∈ p.1.1) (hxq : x ∈ q.1.2) :
    ∀ b ∈ q.1.1, x < b := by
  rcases hq x hxq with h | h
  · exact h
  · obtain ⟨y,hyp,hyq⟩ := hpq.1
    exact (lt_asymm (witness_right G p q hp hcut hyp hyq x hxp) (h y hyq)).elim

private theorem three_inner_one (hG : NoAlternating G) (p q r s : Biclique G)
    (hp : Erdos595NoAlternating.Inner p.1.1 p.1.2) (hq : Erdos595NoAlternating.Inner q.1.1 q.1.2)
    (hr : Erdos595NoAlternating.Inner r.1.1 r.1.2) (hs : Erdos595NoAlternating.Inner s.1.2 s.1.1)
    (hpq : cut p.1.1 ≤ cut q.1.1) (hqr : cut q.1.1 ≤ cut r.1.1)
    (apq : (right G).Adj p q) (aqr : (right G).Adj q r)
    (ars : (right G).Adj r s) (asp : (right G).Adj s p) : False := by
  obtain ⟨x,hxp,hxq⟩ := apq.1
  obtain ⟨y,hyq,hyr⟩ := aqr.1
  obtain ⟨z,hzr,hzs⟩ := ars.1
  obtain ⟨w,hws,hwp⟩ := asp.1
  have hwx := witness_right G p q hp hpq hxp hxq w hwp
  have hxy := witness_right G q r hq hqr hyq hyr x hxq
  have hwx' := p.2 w hwp x hxp
  have hxy' := q.2 x hxq y hyq
  have hyz' := r.2 y hyr z hzr
  have hzw' := s.2 z hzs w hws
  have hov : (r.1.1 ∩ s.1.2).Nonempty := by
    obtain ⟨t,hts,htr⟩ := ars.2
    exact ⟨t,htr,hts⟩
  rcases outside_overlap hr hs hov hzr hzs hyr hws with ⟨hzy,hzw⟩ | ⟨hyz,hwz⟩
  · exact hG z w x y hzw hwx hxy hzw' hwx' hxy' hyz'
  · exact hG w x y z hwx hxy hyz hwx' hxy' hyz' hzw'

private theorem two_inner_two (hG : NoAlternating G) (p q r s : Biclique G)
    (hp : Erdos595NoAlternating.Inner p.1.1 p.1.2) (hq : Erdos595NoAlternating.Inner q.1.1 q.1.2)
    (hr : Erdos595NoAlternating.Inner r.1.2 r.1.1) (hs : Erdos595NoAlternating.Inner s.1.2 s.1.1)
    (hpq : cut p.1.1 ≤ cut q.1.1) (hrs : cut r.1.2 ≤ cut s.1.2)
    (apq : (right G).Adj p q) (aqr : (right G).Adj q r)
    (ars : (right G).Adj r s) (asp : (right G).Adj s p) : False := by
  obtain ⟨x,hxp,hxq⟩ := apq.1
  obtain ⟨y,hyq,hyr⟩ := aqr.1
  obtain ⟨z,hzr,hzs⟩ := ars.1
  obtain ⟨w,hws,hwp⟩ := asp.1
  have hwx := witness_right G p q hp hpq hxp hxq w hwp
  have hzw := witness_left G (swap G r) (swap G s) hr hs hrs (swap_adj G ars)
    hzr hzs w hws
  have hwx' := p.2 w hwp x hxp
  have hxy' := q.2 x hxq y hyq
  have hyz' := r.2 y hyr z hzr
  have hzw' := s.2 z hzs w hws
  have hov : (q.1.1 ∩ r.1.2).Nonempty := by
    obtain ⟨t,htr,htq⟩ := aqr.2
    exact ⟨t,htq,htr⟩
  rcases outside_overlap hq hr hov hyq hyr hxq hzr with ⟨hyx,hyz⟩ | ⟨hxy,hzy⟩
  · exact hG y z w x hyz hzw hwx hyz' hzw' hwx' hxy'
  · exact hG z w x y hzw hwx hxy hzw' hwx' hxy' hyz'

private theorem swap_swap (p : Biclique G) : swap G (swap G p) = p := by
  cases p
  rfl

private theorem swap_adj_iff (p q : Biclique G) :
    (right G).Adj (swap G p) (swap G q) ↔ (right G).Adj p q := by
  refine ⟨fun h => ?_,swap_adj G⟩
  simpa only [swap_swap] using swap_adj G h

/-- Both signs use the SAME increasing order of the inner-side cuts. -/
private abbrev Signed := Bool × {p : Biclique G // Erdos595NoAlternating.Inner p.1.1 p.1.2}

private def decode (p : Signed G) : Biclique G :=
  if p.1 then swap G p.2.1 else p.2.1

private def signedGraph : SimpleGraph (Signed G) := (right G).comap (decode G)

private def label (p : Signed G) : Bool ×ₗ LowerSet V :=
  toLex (p.1,cut p.2.1.1.1)

private theorem label_ne (p q : Signed G) (h : (signedGraph G).Adj p q) :
    label G p ≠ label G q := by
  intro he
  have he' : (p.1,cut p.2.1.1.1) = (q.1,cut q.2.1.1.1) := toLex_inj.mp he
  have hb : p.1 = q.1 := congrArg (fun t : Bool × LowerSet V => t.1) he'
  have hc : cut p.2.1.1.1 = cut q.2.1.1.1 := congrArg (fun t : Bool × LowerSet V => t.2) he' 
  have hadj : (right G).Adj p.2.1 q.2.1 := by
    change (right G).Adj (decode G p) (decode G q) at h
    cases hp : p.1 <;> simp only [decode, hp, ← hb, Bool.false_eq_true,
      ↓reduceIte] at h
    · exact h
    · exact (swap_adj_iff G _ _).mp h
  exact cut_ne G _ _ p.2.2 q.2.2 hadj hc

private theorem signed_no_alternating (hG : NoAlternating G) :
    NoAlternatingLabel (signedGraph G) (label G) := by
  rintro ⟨bp,p⟩ ⟨bq,q⟩ ⟨br,r⟩ ⟨bs,s⟩ hpq hqr hrs apq aqr ars asp
  have pq := (Prod.Lex.lt_iff).mp hpq
  have qr := (Prod.Lex.lt_iff).mp hqr
  have rs := (Prod.Lex.lt_iff).mp hrs
  change (right G).Adj (decode G (bp,p)) (decode G (bq,q)) at apq
  change (right G).Adj (decode G (bq,q)) (decode G (br,r)) at aqr
  change (right G).Adj (decode G (br,r)) (decode G (bs,s)) at ars
  change (right G).Adj (decode G (bs,s)) (decode G (bp,p)) at asp
  have htf : ¬((true : Bool) < false) := by decide
  cases bp <;> cases bq <;> cases br <;> cases bs <;>
    simp [label, decode, swap_adj_iff, htf] at pq qr rs apq aqr ars asp
  · exact inner_no_alternating G hG p q r s p.2 q.2 r.2 pq.le qr.le rs.le apq aqr ars asp
  · exact three_inner_one G hG p q r (swap G s) p.2 q.2 r.2 s.2 pq.le qr.le
      apq aqr ars asp
  · exact two_inner_two G hG p q (swap G r) (swap G s) p.2 q.2 r.2 s.2 pq.le rs.le
      apq aqr (swap_adj G ars) asp
  · apply three_inner_one G hG q r s (swap G p) q.2 r.2 s.2 p.2 qr.le rs.le aqr ars
    · simpa only [swap_swap] using swap_adj G asp
    · simpa only [swap_swap] using swap_adj G apq
  · exact inner_no_alternating G hG p q r s p.2 q.2 r.2 pq.le qr.le rs.le apq aqr ars asp

private noncomputable def signedPoint (hG : NoAlternating G) (p : Biclique G) : Signed G := by
  classical
  exact if h : Erdos595NoAlternating.Inner p.1.1 p.1.2 then (false,⟨p,h⟩)
    else (true,⟨swap G p,(inner_or G hG p).resolve_left h⟩)

private theorem decode_signedPoint (hG : NoAlternating G) (p : Biclique G) :
    decode G (signedPoint G hG p) = p := by
  classical
  unfold signedPoint
  split_ifs <;> simp [decode, swap_swap]

private noncomputable def signedLift (hG : NoAlternating G) : right G →g signedGraph G where
  toFun := signedPoint G hG
  map_rel' := by
    intro p q hpq
    change (right G).Adj (decode G (signedPoint G hG p)) (decode G (signedPoint G hG q))
    simpa only [decode_signedPoint] using hpq

/-- Existence of a suitable order, independently of any order already on V. -/
def Orderable {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ o : LinearOrder W, @NoAlternating W o H

omit [LinearOrder V] in
/-- Break label ties by a well-order; an edge never has equal labels. -/
theorem orderable_of_label {K : Type*} [LinearOrder K] (f : V → K)
    (hne : ∀ a b, G.Adj a b → f a ≠ f b) (hG : NoAlternatingLabel G f) : Orderable G := by
  classical
  let old : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder V := old
  let e (v : V) : K ×ₗ V := toLex (f v,v)
  have he : Function.Injective e := by
    intro a b hab
    exact congrArg Prod.snd (toLex_inj.mp hab)
  let target : LinearOrder (K ×ₗ V) := inferInstance
  letI : LinearOrder V := @LinearOrder.lift' V (K ×ₗ V) target e he
  have hlt : ∀ a b : V, a < b → G.Adj a b → f a < f b := by
    intro a b hab hAdj
    have hh : @LT.lt (K ×ₗ V) target.toLT (e a) (e b) := hab
    have hor : f a < f b ∨ f a = f b ∧ @LT.lt V old.toLT a b :=
      (@Prod.Lex.lt_iff K V _ old.toLT (e a) (e b)).mp hh
    exact hor.elim id (fun h => (hne a b hAdj h.1).elim)
  refine ⟨inferInstance,?_⟩
  intro a b c d hab hbc hcd hab' hbc' hcd' hda
  exact hG a b c d (hlt a b hab hab') (hlt b c hbc hbc') (hlt c d hcd hcd')
    hab' hbc' hcd' hda

/-- The no-alternating-C4 property survives the ENTIRE right adjoint,
not merely the two separately oriented vertex classes. -/
theorem right_orderable (hG : NoAlternating G) : Orderable (right G) := by
  classical
  let f := signedLift G hG
  apply orderable_of_label (right G) (fun p => label G (f p))
  · intro p q hpq
    exact label_ne G (f p) (f q) (f.map_adj hpq)
  · intro p q r s hpq hqr hrs apq aqr ars asp
    exact signed_no_alternating G hG (f p) (f q) (f r) (f s) hpq hqr hrs
      (f.map_adj apq) (f.map_adj aqr) (f.map_adj ars) (f.map_adj asp)

omit [LinearOrder V] in
theorem Orderable.right (hG : Orderable G) : Orderable (right G) := by
  obtain ⟨o,ho⟩ := hG
  letI := o
  exact right_orderable G ho

omit [LinearOrder V] in
theorem Orderable.cover (hG : Orderable G) : IsCountableUnionOfTriangleFree G := by
  obtain ⟨o,ho⟩ := hG
  letI := o
  exact cover_of_label G id (fun _ _ h => h.ne) ho

omit [LinearOrder V] in
/-- A clique of four always contains an increasing four-cycle. -/
theorem Orderable.cliqueFree (hG : Orderable G) : G.CliqueFree 4 := by
  classical
  obtain ⟨o,ho⟩ := hG
  letI := o
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  let t : Finset V := Finset.univ.image e
  have ht : t.card = 4 := by
    rw [Finset.card_image_of_injective _ e.injective]
    rfl
  let f : Fin 4 ↪o V := t.orderEmbOfFin ht
  have hf (i : Fin 4) : f i ∈ t := t.orderEmbOfFin_mem ht i
  have hadj (i j : Fin 4) (hij : i ≠ j) : G.Adj (f i) (f j) := by
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (hf i)
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp (hf j)
    rw [← ha,← hb]
    apply e.map_rel_iff.mpr
    intro he
    exact hij (f.injective (ha.symm.trans (he ▸ hb)))
  exact ho (f 0) (f 1) (f 2) (f 3)
    (f.strictMono (by decide)) (f.strictMono (by decide)) (f.strictMono (by decide))
    (hadj 0 1 (by decide)) (hadj 1 2 (by decide)) (hadj 2 3 (by decide))
    (hadj 3 0 (by decide))

universe u
/-- All finite right-adjoint iterates, with their changing vertex types. -/
def iterate {W : Type u} (H : SimpleGraph W) : ℕ → Σ X : Type u, SimpleGraph X
  | 0 => ⟨W,H⟩
  | n+1 => ⟨Biclique (iterate H n).2, right (iterate H n).2⟩

theorem iterate_orderable {W : Type u} (H : SimpleGraph W) (hH : Orderable H) :
    ∀ n, Orderable (iterate H n).2 := by
  intro n
  induction n with
  | zero => exact hH
  | succ n ih => exact Orderable.right _ ih

theorem iterate_cover {W : Type u} (H : SimpleGraph W) (hH : Orderable H) (n : ℕ) :
    IsCountableUnionOfTriangleFree (iterate H n).2 :=
  Orderable.cover _ (iterate_orderable H hH n)

theorem iterate_cliqueFree {W : Type u} (H : SimpleGraph W) (hH : Orderable H) (n : ℕ) :
    (iterate H n).2.CliqueFree 4 :=
  Orderable.cliqueFree _ (iterate_orderable H hH n)

/-- The equality shift-square has the required order property. -/
theorem shift_orderable (A : Type*) [LinearOrder A] :
    Orderable (Erdos595MiddleCorner.graph A) := by
  apply orderable_of_label (Erdos595MiddleCorner.graph A) (fun x => x.a)
  · exact fun _ _ h => Erdos595MiddleCorner.first_ne h
  · intro a b c d hab hbc hcd apq aqr _ asp
    have h₁ := Erdos595MiddleCorner.forward_of_le apq hab.le
    have h₂ := Erdos595MiddleCorner.forward_of_le aqr hbc.le
    have h₃ := Erdos595MiddleCorner.forward_of_le asp.symm ((hab.trans hbc).trans hcd).le
    have bounds (x y : Erdos595MiddleCorner.Triple A) (h : Erdos595MiddleCorner.Forward x y) :
        y.a ≤ x.c ∧ x.c ≤ y.b ∧ x.b ≤ y.a := by
      rcases h with ⟨h,h'⟩ | h
      · rw [← h,← h']
        exact ⟨x.bc.le,le_rfl,le_rfl⟩
      · change x.c = y.a at h
        rw [← h]
        exact ⟨le_rfl,h.le.trans y.ab.le,x.bc.le⟩
    have ha := bounds a b h₁
    have hb := bounds b c h₂
    have hd := bounds a d h₃
    exact (not_lt_of_ge (hd.1.trans (ha.2.1.trans hb.2.2))) hcd

/-- In particular, the previously unresolved second and later iterations
of the equality-shift candidate are ALL countably coverable. -/
theorem shift_iterate_cover (A : Type u) [LinearOrder A] (n : ℕ) :
    IsCountableUnionOfTriangleFree (iterate (Erdos595MiddleCorner.graph A) n).2 :=
  iterate_cover _ (shift_orderable A) n

theorem shift_iterate_cliqueFree (A : Type u) [LinearOrder A] (n : ℕ) :
    (iterate (Erdos595MiddleCorner.graph A) n).2.CliqueFree 4 :=
  iterate_cliqueFree _ (shift_orderable A) n

#print axioms right_orderable
#print axioms iterate_cover
#print axioms shift_iterate_cover
#print axioms shift_iterate_cliqueFree

end Erdos595NoAlternatingIteration
