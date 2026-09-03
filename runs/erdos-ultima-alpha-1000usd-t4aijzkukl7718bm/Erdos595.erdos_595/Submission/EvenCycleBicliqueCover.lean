import Submission.BoundedIncreasingPath

/-!
A fixed even increasing-cycle obstruction bounds the local chromatic numbers
of a biclique right adjoint. This is auxiliary work, not a settlement of
Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
open Erdos595ArcAdjoint Erdos595BoundedPath Erdos595Work
namespace Erdos595EvenCycle

variable {V W : Type*} [LinearOrder V]

def up (H : SimpleGraph V) (x y : V) : Prop := H.Adj x y ∧ x < y

def NoClosing (H : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ x y, Chain (up H) n x y → ¬H.Adj x y

/-- A separated complete biclique, together with an arc map anchored on
its two sides, imposes a finite proper coloring on the domain graph. -/
theorem separated_coloring (H : SimpleGraph V) (F : SimpleGraph W) (m : ℕ)
    (hn : NoClosing H (m+2)) (a b : W → V)
    (hcross : ∀ u v, H.Adj (a u) (b v)) (hsep : ∀ u v, a u < b v)
    (c : arcGraph F →g H)
    (ha : ∀ e : Arc F, H.Adj (c e) (a e.1.2))
    (hb : ∀ e : Arc F, H.Adj (c e) (b e.1.1)) : Nonempty (F.Coloring ℕ) := by
  classical
  let tag (e : Arc F) : Bool × Bool :=
    (decide (c e < a e.1.2),decide (b e.1.1 < c e))
  let r (e d : Arc F) : Prop := (arcGraph F).Adj e d ∧ c e < c d ∧ tag e = tag d
  have hno : ∀ e d, ¬Chain r m e d := by
    intro e d h
    have hwalk : Chain (up H) m (c e) (c d) :=
      h.map c (fun _ _ h => ⟨c.map_adj h.1,h.2.1⟩)
    have ht : tag e = tag d := h.constant tag (fun _ _ h => h.2.2)
    by_cases hL : c d < a d.1.2
    · have hwalk' := (hwalk.snoc ⟨ha d,hL⟩).snoc
        ⟨hcross d.1.2 e.1.1,hsep d.1.2 e.1.1⟩
      exact hn _ _ hwalk' (hb e)
    by_cases hR : b e.1.1 < c e
    · have hwalk' := (hwalk.prepend ⟨(hb e).symm,hR⟩).prepend
        ⟨hcross d.1.2 e.1.1,hsep d.1.2 e.1.1⟩
      exact hn _ _ hwalk' (ha d).symm
    have hLe : ¬c e < a e.1.2 := by
      have he : decide (c e < a e.1.2) = decide (c d < a d.1.2) := congrArg Prod.fst ht
      exact of_decide_eq_false (he.trans (decide_eq_false hL))
    have hRd : ¬b d.1.1 < c d := by
      have he : decide (b e.1.1 < c e) = decide (b d.1.1 < c d) := congrArg Prod.snd ht
      exact of_decide_eq_false (he.symm.trans (decide_eq_false hR))
    have hAe : a e.1.2 < c e := lt_of_le_of_ne (le_of_not_gt hLe) (ha e).ne.symm
    have hBd : c d < b d.1.1 := lt_of_le_of_ne (le_of_not_gt hRd) (hb d).ne
    have hwalk' := (hwalk.prepend ⟨(ha e).symm,hAe⟩).snoc ⟨hb d,hBd⟩
    exact hn _ _ hwalk' (hcross e.1.2 d.1.1)
  obtain ⟨height,hheight⟩ := finite_rank r m hno
  let palette := (Bool × Bool) × Fin (m+1)
  let ca : (arcGraph F).Coloring palette := SimpleGraph.Coloring.mk (fun e => (tag e,height e)) (by
    intro e d hadj he
    have ht : tag e = tag d := congrArg Prod.fst he
    have hh : height e = height d := congrArg Prod.snd he
    rcases lt_or_gt_of_ne (c.map_adj hadj).ne with h | h
    · exact (hheight e d ⟨hadj,h,ht⟩).ne hh
    · exact (hheight d e ⟨hadj.symm,h,ht.symm⟩).ne hh.symm)
  let cf := coloring_of_arc F ca
  obtain ⟨enc,henc⟩ := exists_injective_nat (Set palette)
  exact ⟨SimpleGraph.Coloring.mk (enc ∘ cf) (fun hadj he => cf.valid hadj (henc he))⟩

/-- The even-cycle condition makes arbitrary biclique anchors separable
on finitely many rank classes. -/
theorem anchor_coloring (H : SimpleGraph V) (F : SimpleGraph W) (k : ℕ)
    (hn : NoClosing H (2*k+3)) (a b : W → V)
    (hcross : ∀ u v, H.Adj (a u) (b v))
    (c : arcGraph F →g H)
    (ha : ∀ e : Arc F, H.Adj (c e) (a e.1.2))
    (hb : ∀ e : Arc F, H.Adj (c e) (b e.1.1)) : Nonempty (F.Coloring ℕ) := by
  classical
  let val (x : Bool × W) := if x.1 then b x.2 else a x.2
  let r (x y : Bool × W) := x.1 ≠ y.1 ∧ val x < val y
  have hcross' (x y : Bool × W) (h : x.1 ≠ y.1) : H.Adj (val x) (val y) := by
    cases hx : x.1 <;> cases hy : y.1
    · exact False.elim (h (hx.trans hy.symm))
    · simpa only [val, hx, hy, Bool.false_eq_true, if_false, if_true] using hcross x.2 y.2
    · simpa only [val, hx, hy, Bool.false_eq_true, if_false, if_true] using (hcross y.2 x.2).symm
    · exact False.elim (h (hx.trans hy.symm))
  have hno : ∀ x y, ¬Chain r (2*k+3) x y := by
    intro x y h
    have h' : Chain r (2*(k+1)+1) x y := by convert h using 1
    have ht := h'.odd_bool Prod.fst (fun _ _ h => h.1)
    exact hn _ _ (h.map val (fun x y h => ⟨hcross' x y h.1,h.2⟩)) (hcross' x y ht)
  obtain ⟨height,hh⟩ := finite_rank r (2*k+3) hno
  let tag (u : W) := (height (false,u),height (true,u))
  apply coloring_of_countable_fibers F tag
  intro i
  let S := {u | tag u = i}
  let Fi := F.induce S
  let inc : Fi →g F := ⟨Subtype.val,fun h => h⟩
  let ci : arcGraph Fi →g H := c.comp (arcMap inc)
  let ai (u : S) := a u.1
  let bi (u : S) := b u.1
  have hai (e : Arc Fi) : H.Adj (ci e) (ai e.1.2) := ha (arcMap inc e)
  have hbi (e : Arc Fi) : H.Adj (ci e) (bi e.1.1) := hb (arcMap inc e)
  have hcrossi (u v : S) : H.Adj (ai u) (bi v) := hcross u.1 v.1
  have hheightA (u : S) : height (false,u.1) = i.1 := congrArg Prod.fst u.2
  have hheightB (u : S) : height (true,u.1) = i.2 := congrArg Prod.snd u.2
  have hn' : NoClosing H ((2*k+1)+2) := by convert hn using 1
  rcases lt_trichotomy i.1 i.2 with hi | hi | hi
  · apply separated_coloring H Fi (2*k+1) hn' ai bi hcrossi _ ci hai hbi
    intro u v
    by_contra hnsep
    have hback : val (true,v.1) < val (false,u.1) :=
      lt_of_le_of_ne (le_of_not_gt hnsep) (hcrossi u v).ne.symm
    have hr := hh (true,v.1) (false,u.1) ⟨by simp,hback⟩
    rw [hheightB v,hheightA u] at hr
    exact (lt_asymm hi hr)
  · have hempty : IsEmpty S := ⟨by
      intro u
      rcases lt_or_gt_of_ne (hcrossi u u).ne with h | h
      · have hr := hh (false,u.1) (true,u.1) ⟨by simp,h⟩
        rw [hheightA u,hheightB u,hi] at hr
        exact (lt_irrefl _ hr)
      · have hr := hh (true,u.1) (false,u.1) ⟨by simp,h⟩
        rw [hheightB u,hheightA u,hi] at hr
        exact (lt_irrefl _ hr)⟩
    letI := hempty
    exact ⟨SimpleGraph.Coloring.mk (fun _ => 0) (fun {u} => isEmptyElim u)⟩
  · have hsep (u v : S) : bi u < ai v := by
      by_contra hnsep
      have hback : val (false,v.1) < val (true,u.1) :=
        lt_of_le_of_ne (le_of_not_gt hnsep) (hcrossi v u).ne
      have hr := hh (false,v.1) (true,u.1) ⟨by simp,hback⟩
      rw [hheightA v,hheightB u] at hr
      exact (lt_asymm hi hr)
    exact separated_coloring H Fi (2*k+1) hn' bi ai
      (fun u v => (hcrossi v u).symm) hsep (ci.comp (reverseArc Fi))
      (fun e => hbi (reverseArc Fi e)) (fun e => hai (reverseArc Fi e))

/-- Every neighborhood in the right adjoint has a countable proper
coloring when one even increasing cycle is excluded in the base order. -/
theorem neighborhood_coloring (H : SimpleGraph V) (k : ℕ)
    (hn : NoClosing H (2*k+3)) (p : Biclique H) :
    Nonempty (((right H).induce ((right H).neighborSet p)).Coloring ℕ) := by
  classical
  let S := (right H).neighborSet p
  let F := (right H).induce S
  let inc : F →g right H := ⟨Subtype.val,fun h => h⟩
  let a (q : S) : V := q.2.2.choose
  let b (q : S) : V := q.2.1.choose
  have has (q : S) : a q ∈ q.1.1.2 ∧ a q ∈ p.1.1 := q.2.2.choose_spec
  have hbs (q : S) : b q ∈ p.1.2 ∧ b q ∈ q.1.1.1 := q.2.1.choose_spec
  let c := fromRight inc
  have hcs (e : Arc F) : c e ∈ e.1.1.1.1.2 ∧ c e ∈ e.1.2.1.1.1 :=
    (inc.map_adj e.2).1.choose_spec
  apply anchor_coloring H F k hn a b
    (fun u v => p.2 _ (has u).2 _ (hbs v).1) c
  · intro e
    exact e.1.2.1.2 _ (hcs e).2 _ (has e.1.2).1
  · intro e
    exact (e.1.1.1.2 _ (hbs e.1.1).2 _ (hcs e).1).symm

/-- A usable general obstruction to a right-adjoint witness for Erdős 595. -/
theorem right_cover (H : SimpleGraph V) (k : ℕ) (hn : NoClosing H (2*k+3)) :
    IsCountableUnionOfTriangleFree (right H) := by
  classical
  let G := right H
  let c (p : Biclique H) : (G.induce (G.neighborSet p)).Coloring ℕ :=
    Classical.choice (neighborhood_coloring H k hn p)
  let f (p q : Biclique H) := if h : G.Adj p q then c p ⟨q,h⟩ else 0
  letI : LinearOrder (Biclique H) := IsWellOrder.linearOrder WellOrderingRel
  apply countable_union_of_earlier_neighbor_coloring G f
  intro p q r _ _ hpq hpr hqr
  simpa only [f, dif_pos hpq, dif_pos hpr] using (c p).valid (show
    (G.induce (G.neighborSet p)).Adj ⟨q,hpq⟩ ⟨r,hpr⟩ from hqr)

omit [LinearOrder V] in
/-- An order on labels suffices; ties may be broken by a well-order. -/
theorem right_cover_of_label {K : Type*} [LinearOrder K]
    (H : SimpleGraph V) (f : V → K) (k : ℕ)
    (hne : ∀ a b, H.Adj a b → f a ≠ f b)
    (hn : ∀ x y, Chain (fun a b => H.Adj a b ∧ f a < f b) (2*k+3) x y →
      ¬H.Adj x y) : IsCountableUnionOfTriangleFree (right H) := by
  classical
  let old : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder V := old
  let e (v : V) : K ×ₗ V := toLex (f v,v)
  have he : Function.Injective e := by
    intro a b hab
    exact congrArg Prod.snd (toLex_inj.mp hab)
  let target : LinearOrder (K ×ₗ V) := inferInstance
  letI : LinearOrder V := @LinearOrder.lift' V (K ×ₗ V) target e he
  have hlt : ∀ a b : V, a < b → H.Adj a b → f a < f b := by
    intro a b hab hAdj
    have hh : @LT.lt (K ×ₗ V) target.toLT (e a) (e b) := hab
    have hor : f a < f b ∨ f a = f b ∧ @LT.lt V old.toLT a b :=
      (@Prod.Lex.lt_iff K V _ old.toLT (e a) (e b)).mp hh
    exact hor.elim id (fun h => (hne a b hAdj h.1).elim)
  apply right_cover H k
  intro x y h
  exact hn x y (h.map id (fun a b hab => ⟨hab.1,hlt a b hab.2 hab.1⟩))

#print axioms separated_coloring
#print axioms anchor_coloring
#print axioms neighborhood_coloring
#print axioms right_cover
#print axioms right_cover_of_label
end Erdos595EvenCycle
