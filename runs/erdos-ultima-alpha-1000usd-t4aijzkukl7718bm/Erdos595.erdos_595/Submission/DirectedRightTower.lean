import Submission.RightTowerCountableCover

/-!
Directed biclique right adjoints: arrows are retained between stages, and
only the final graph is mutualGraph. This auxiliary file does not settle Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595DirectedRight

variable {V W : Type*}

abbrev Biclique (R : V → V → Prop) :=
  {p : Set V × Set V // ∀ a ∈ p.1, ∀ b ∈ p.2, R a b}

def right (R : V → V → Prop) (p q : Biclique R) : Prop :=
  (p.val.2 ∩ q.val.1).Nonempty

lemma right_irrefl {R : V → V → Prop} (hR : Irreflexive R) : Irreflexive (right R) := by
  intro p hp
  obtain ⟨v,hvB,hvA⟩ := hp
  exact hR v (p.property v hvA v hvB)

def mutualGraph (R : V → V → Prop) (hR : Irreflexive R) : SimpleGraph V where
  Adj a b := R a b ∧ R b a
  symm := fun _ _ h => h.symm
  loopless := fun a h => hR a h.1

abbrev Arc (R : V → V → Prop) := {p : V × V // R p.1 p.2}

def arc (R : V → V → Prop) (e f : Arc R) : Prop := e.val.2 = f.val.1

/-- Currying preserves the arrows; symmetrization must not be inserted here. -/
def curry {S : V → V → Prop} {R : W → W → Prop}
    (f : Arc S → W) (hf : ∀ e d, arc S e d → R (f e) (f d)) (v : V) : Biclique R :=
  ⟨({w | ∃ e : Arc S, e.val.2 = v ∧ f e = w},
    {w | ∃ e : Arc S, e.val.1 = v ∧ f e = w}),by
      rintro a ⟨e,he,rfl⟩ b ⟨d,hd,rfl⟩
      exact hf e d (he.trans hd.symm)⟩

lemma curry_rel {S : V → V → Prop} {R : W → W → Prop}
    (f : Arc S → W) (hf : ∀ e d, arc S e d → R (f e) (f d))
    {v w : V} (hvw : S v w) : right R (curry f hf v) (curry f hf w) := by
  let e : Arc S := ⟨(v,w),hvw⟩
  exact ⟨f e,⟨e,rfl,rfl⟩,⟨e,rfl,rfl⟩⟩

/-- A directed three-cycle pulls back through one right-adjoint stage. -/
lemma cycle_pullback {R : V → V → Prop} {p q r : Biclique R}
    (hpq : right R p q) (hqr : right R q r) (hrp : right R r p) :
    ∃ a b c, R a b ∧ R b c ∧ R c a := by
  obtain ⟨a,haB,haA⟩ := hpq
  obtain ⟨b,hbB,hbA⟩ := hqr
  obtain ⟨c,hcB,hcA⟩ := hrp
  exact ⟨a,b,c,q.property _ haA _ hbB,r.property _ hbA _ hcB,p.property _ hcA _ haB⟩

def HasRectangles (R : V → V → Prop) : Prop :=
  ∃ d : ℕ → Biclique R, ∀ a b, R a b → ∃ n, a ∈ (d n).val.1 ∧ b ∈ (d n).val.2

def matrix (R : V → V → Prop) (d : ℕ → Biclique R)
    (m : Fin 2 → Fin 2 → ℕ) : Biclique R :=
  ⟨({a | ∃ i, ∀ j, a ∈ (d (m i j)).val.1},
    {b | ∃ j, ∀ i, b ∈ (d (m i j)).val.2}),by
      rintro a ⟨i,hi⟩ b ⟨j,hj⟩
      exact (d (m i j)).property a (hi j) b (hj i)⟩

/-- Countable directed rectangles give countable pair detectors in the mutualGraph
right adjoint, just as in the symmetric case. -/
theorem detector {R : V → V → Prop} (hR : Irreflexive R) (hRect : HasRectangles R) :
    ∃ d : ℕ → Biclique R, ∀ p q,
      (∃ r, (mutualGraph (right R) (right_irrefl hR)).Adj p r ∧
        (mutualGraph (right R) (right_irrefl hR)).Adj q r) →
      ∃ n, (mutualGraph (right R) (right_irrefl hR)).Adj p (d n) ∧
        (mutualGraph (right R) (right_irrefl hR)).Adj q (d n) := by
  classical
  obtain ⟨d,hd⟩ := hRect
  obtain ⟨e,he⟩ := exists_surjective_nat (Fin 2 → Fin 2 → ℕ)
  refine ⟨fun n => matrix R d (e n),?_⟩
  intro p q h
  obtain ⟨r,hpr,hqr⟩ := h
  obtain ⟨a,haP,haR⟩ := hpr.1
  obtain ⟨b,hbR,hbP⟩ := hpr.2
  obtain ⟨c,hcQ,hcR⟩ := hqr.1
  obtain ⟨t,htR,htQ⟩ := hqr.2
  let x : Fin 2 → V := ![a,c]
  let y : Fin 2 → V := ![b,t]
  have hx : ∀ i, x i ∈ r.val.1 := by intro i; fin_cases i <;> assumption
  have hy : ∀ j, y j ∈ r.val.2 := by intro j; fin_cases j <;> assumption
  choose m hm using fun i j => hd (x i) (y j) (r.property _ (hx i) _ (hy j))
  obtain ⟨n,hn⟩ := he m
  refine ⟨n,?_⟩
  dsimp only
  rw [hn]
  have hleft : ∀ i, x i ∈ (matrix R d m).val.1 := fun i => ⟨i,fun j => (hm i j).1⟩
  have hright : ∀ j, y j ∈ (matrix R d m).val.2 := fun j => ⟨j,fun i => (hm i j).2⟩
  exact ⟨⟨⟨a,haP,hleft 0⟩,⟨b,hright 0,hbP⟩⟩,
    ⟨⟨c,hcQ,hleft 1⟩,⟨t,hright 1,htQ⟩⟩⟩

/-- A countable base gives countably many directed rectangles at its first stage. -/
theorem right_rectangles [Countable V] (R : V → V → Prop) : HasRectangles (right R) := by
  classical
  obtain ⟨e,he⟩ := exists_surjective_nat (Option V)
  let d : ℕ → Biclique (right R) := fun n => match e n with
    | none => ⟨(∅,∅),by simp⟩
    | some a => ⟨({p | a ∈ p.val.2},{q | a ∈ q.val.1}),fun p hp q hq => ⟨a,hp,hq⟩⟩
  refine ⟨d,?_⟩
  intro p q hpq
  obtain ⟨a,ha,hb⟩ := hpq
  obtain ⟨n,hn⟩ := he (some a)
  exact ⟨n,by simpa only [d,hn,Set.mem_setOf_eq] using And.intro ha hb⟩

abbrev twice (H : SimpleGraph V) :=
  mutualGraph (right (right H.Adj)) (right_irrefl (right_irrefl H.loopless))

/-- Triangle-freeness survives both DIRECTED right stages and final mutualization. -/
theorem twice_triangleFree (H : SimpleGraph V) (hH : H.CliqueFree 3) :
    (twice H).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨p,q,r,hpq,hpr,hqr,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  obtain ⟨a,b,c,hab,hbc,hca⟩ := cycle_pullback hpq.1 hqr.1 hpr.2
  obtain ⟨x,y,z,hxy,hyz,hzx⟩ := cycle_pullback hab hbc hca
  exact hH _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hzx.symm,hyz⟩)

/-- For a triangle-free countable target, the second directed right stage,
after mutualization, has a countable proper vertex coloring. -/
theorem twice_countable_coloring [Countable V] (H : SimpleGraph V) (hH : H.CliqueFree 3) :
    Nonempty ((twice H).Coloring ℕ) := by
  obtain ⟨d,hd⟩ := detector (right_irrefl H.loopless) (right_rectangles H.Adj)
  exact Erdos595CommonNeighborDetector.countable_coloring _ d
    ((twice_triangleFree H hH).mono (by decide)) hd

#print axioms twice_triangleFree
#print axioms twice_countable_coloring
end Erdos595DirectedRight
