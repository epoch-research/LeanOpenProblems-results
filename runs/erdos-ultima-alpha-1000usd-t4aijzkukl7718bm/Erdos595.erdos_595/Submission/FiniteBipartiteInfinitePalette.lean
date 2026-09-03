import Submission.PairBoxRamsey
import Submission.FiniteFolkmanAmalgamation

/-!
Every finite bipartite graph has an induced bipartite edge-Ramsey host for
an arbitrary color palette. The target is finite; the host is not
asserted finite. Free amalgamation therefore homogenizes any designated
finite induced bipartite subgraph of a K4-free graph. This does not supply
Ramsey hosts for arbitrary infinite bipartite targets or compatible choices
at infinitely many partite stages.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595FiniteBipartiteInfinitePalette
open Erdos595PairBoxRamsey

universe u
variable {L R : Type u} (E : L → R → Prop)

/-- A graph with its two sides explicitly marked. -/
def graph : SimpleGraph (L ⊕ R) where
  Adj
    | .inl a,.inr b => E a b
    | .inr b,.inl a => E a b
    | _,_ => False
  symm := by intro a b h; cases a <;> cases b <;> exact h
  loopless := by intro a h; cases a <;> exact h

abbrev Coord (L R : Type u) := L ⊕ (R ⊕ (L × R))

noncomputable def left (a : L) : Coord L R → Fin 4 := by
  classical
  exact fun k => match k with
    | .inl i => if a = i then 1 else 0
    | .inr (.inl _) => 0
    | .inr (.inr (i,j)) => if E i j then 0 else if a = i then 2 else 0

noncomputable def right (b : R) : Coord L R → Fin 4 := by
  classical
  exact fun k => match k with
    | .inl _ => 3
    | .inr (.inl j) => if b = j then 2 else 3
    | .inr (.inr (i,j)) => if E i j then 3 else if b = j then 1 else 3

lemma left_injective : Function.Injective (left E) := by
  classical
  intro a b he
  by_contra hn
  have h := congrFun he (.inl a)
  simp [left,Ne.symm hn] at h

lemma right_injective : Function.Injective (right E) := by
  classical
  intro a b he
  by_contra hn
  have h := congrFun he (.inr (.inl a))
  simp [right,Ne.symm hn] at h

/-- Every target edge has the SAME positive inequality at every coordinate;
a nonedge is reversed at its own dedicated coordinate. -/
lemma inequalities_iff (a : L) (b : R) :
    (∀ k, left E a k < right E b k) ↔ E a b := by
  classical
  constructor
  · intro h
    by_contra hn
    have hh := h (.inr (.inr (a,b)))
    simp [left,right,hn] at hh
  · intro hab k
    rcases k with i | j | ⟨i,j⟩
    · by_cases h : a = i <;> simp [left,right,h]
    · by_cases h : b = j <;> simp [left,right,h]
    · by_cases hij : E i j
      · simp [left,right,hij]
      · by_cases ha : a = i <;> by_cases hb : b = j <;>
          simp_all [left,right]

variable {I : Type u} (A : I → Axis.{u})

abbrev Point := ∀ i, (A i).Carrier

def dominance : SimpleGraph (Point A ⊕ Point A) where
  Adj
    | .inl a,.inr b => ∀ i, a i < b i
    | .inr b,.inl a => ∀ i, a i < b i
    | _,_ => False
  symm := by intro a b h; cases a <;> cases b <;> exact h
  loopless := by intro a h; cases a <;> exact h

lemma dominance_triangleFree : (dominance A).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  cases a <;> cases b <;> cases c <;>
    first | exact hab | exact hac | exact hbc

variable (A : Coord L R → Axis.{u}) (f : ∀ k, Fin 4 ↪o (A k).Carrier)

noncomputable def embedMap : L ⊕ R → Point A ⊕ Point A
  | .inl a => .inl (fun k => f k (left E a k))
  | .inr b => .inr (fun k => f k (right E b k))

lemma embedMap_injective : Function.Injective (embedMap E A f) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      apply congrArg Sum.inl (left_injective E ?_)
      exact funext (fun k => (f k).injective (congrFun (Sum.inl_injective h) k))
    | inr b => simp [embedMap] at h
  | inr a =>
    cases y with
    | inl b => simp [embedMap] at h
    | inr b =>
      apply congrArg Sum.inr (right_injective E ?_)
      exact funext (fun k => (f k).injective (congrFun (Sum.inr_injective h) k))

lemma embedMap_rel (x y : L ⊕ R) :
    (dominance A).Adj (embedMap E A f x) (embedMap E A f y) ↔ (graph E).Adj x y := by
  cases x <;> cases y
  · rfl
  · simp only [embedMap,dominance,graph,OrderEmbedding.lt_iff_lt]
    exact inequalities_iff E _ _
  · simp only [embedMap,dominance,graph,OrderEmbedding.lt_iff_lt]
    exact inequalities_iff E _ _
  · rfl

noncomputable def embedding : graph E ↪g dominance A where
  toFun := embedMap E A f
  inj' := embedMap_injective E A f
  map_rel_iff' := embedMap_rel E A f _ _

/-- An induced, part-preserving monochromatic copy of the entire finite
bipartite target, even when the palette is infinite. -/
theorem ramsey_nonempty [Finite L] [Finite R] (C : Type u) [Nonempty C] :
    ∃ (B : Type u) (K : SimpleGraph (B ⊕ B)), K.CliqueFree 3 ∧
      ∀ c : Sym2 (B ⊕ B) → C, ∃ (e : graph E ↪g K) (z : C),
        (∀ a, ∃ b, e (.inl a) = .inl b) ∧
        (∀ a, ∃ b, e (.inr a) = .inr b) ∧
        ∀ x y, (graph E).Adj x y → c s(e x,e y) = z := by
  classical
  obtain ⟨A,hA⟩ := box_finite (Coord L R) C
  refine ⟨Point A,dominance A,dominance_triangleFree A,?_⟩
  intro c
  let d : Family A → C := fun p =>
    c s(Sum.inl (fun k => (p k).val.1),Sum.inr (fun k => (p k).val.2))
  obtain ⟨f,z,hf⟩ := hA d
  let e := embedding E A f
  have he (a : L) (b : R) (hab : E a b) : c s(e (.inl a),e (.inr b)) = z := by
    let p : Coord L R → SmallPair := fun k =>
      ⟨(left E a k,right E b k),(inequalities_iff E a b).mpr hab k⟩
    exact hf p
  refine ⟨e,z,fun a => ⟨_,rfl⟩,fun b => ⟨_,rfl⟩,?_⟩
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl b => exact hxy.elim
    | inr b => exact he a b hxy
  | inr a =>
    cases y with
    | inl b => simpa only [Sym2.eq_swap] using he b a hxy
    | inr b => exact hxy.elim

/-- The empty-palette case is vacuous on a nonempty host. -/
theorem ramsey [Finite L] [Finite R] (C : Type u) :
    ∃ (B : Type u) (K : SimpleGraph (B ⊕ B)), K.CliqueFree 3 ∧
      ∀ c : Sym2 (B ⊕ B) → C, ∃ (e : graph E ↪g K) (z : C),
        (∀ a, ∃ b, e (.inl a) = .inl b) ∧
        (∀ a, ∃ b, e (.inr a) = .inr b) ∧
        ∀ x y, (graph E).Adj x y → c s(e x,e y) = z := by
  cases isEmpty_or_nonempty C with
  | inl hc =>
    refine ⟨ULift.{u} Unit,⊥,SimpleGraph.cliqueFree_bot (by decide),?_⟩
    intro c
    exact isEmptyElim (c s(Sum.inl ⟨()⟩,Sum.inl ⟨()⟩))
  | inr hc => exact ramsey_nonempty E C

/-- A designated finite induced bipartite subgraph can be homogenized inside
an arbitrary K4-free ambient graph. Later copies need not be compatible. -/
theorem finite_bipartite_step [Finite L] [Finite R] {V C : Type u}
    (H : SimpleGraph V) (hH : H.CliqueFree 4) (D : Set V)
    (e : graph E ≃g H.induce D) :
    ∃ (W : Type u) (G : SimpleGraph W), G.CliqueFree 4 ∧
      ∀ c : Sym2 W → C, ∃ (f : H ↪g G) (z : C),
        ∀ x y : D, H.Adj x.val y.val → c s(f x.val,f y.val) = z := by
  classical
  obtain ⟨B,K,hK,hRam⟩ := ramsey E C
  let J := H.induce D ↪g K
  let G := Erdos595FiniteFolkmanAmalgamation.graph H K D (fun i : J => i)
  refine ⟨_,G,Erdos595FiniteFolkmanAmalgamation.cliqueFree H K D _ hH
    (hK.mono (by decide)),?_⟩
  intro c
  let cK : Sym2 (B ⊕ B) → C := fun s => c (s.map Sum.inl)
  obtain ⟨g,z,_,_,hg⟩ := hRam cK
  let i : J := g.comp e.symm.toEmbedding
  let f := Erdos595FiniteFolkmanAmalgamation.copyEmbedding H K D (fun i : J => i) i
  refine ⟨f,z,?_⟩
  intro x y hxy
  have hh := hg (e.symm x) (e.symm y) (e.symm.map_rel_iff.mpr hxy)
  change c s(Erdos595FiniteFolkmanAmalgamation.copy H K D (fun i : J => i) i x.val,
    Erdos595FiniteFolkmanAmalgamation.copy H K D (fun i : J => i) i y.val) = z
  rw [Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ x.property,
    Erdos595FiniteFolkmanAmalgamation.copy_of_mem _ _ _ _ _ _ y.property]
  exact hh

#print axioms inequalities_iff
#print axioms embedding
#print axioms ramsey
#print axioms finite_bipartite_step
end Erdos595FiniteBipartiteInfinitePalette
