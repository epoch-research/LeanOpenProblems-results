import Submission.Work

/-!
Order-type obstruction to finite-tuple constructions: a uniform pair type
which supports a triangle supports a four-clique. This file is auxiliary.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595TupleType

variable {A I : Type*} [LinearOrder A]

/-- The complete weak-order type of a pair of tuples, including the
internal order types of both tuples. -/
def pairType (x y : I → A) : (Bool × I) → (Bool × I) → Prop :=
  fun p q => (if p.1 then y p.2 else x p.2) ≤
    (if q.1 then y q.2 else x q.2)

lemma pairType_eq_iff {x y z w : I → A} :
    pairType x y = pairType z w ↔
      (∀ a b, (x a ≤ x b ↔ z a ≤ z b)) ∧
      (∀ a b, (x a ≤ y b ↔ z a ≤ w b)) ∧
      (∀ a b, (y a ≤ x b ↔ w a ≤ z b)) ∧
      (∀ a b, (y a ≤ y b ↔ w a ≤ w b)) := by
  constructor
  · intro h
    have hh (p q : Bool × I) := congrFun (congrFun h p) q
    exact ⟨fun a b => by simpa [pairType] using hh (false,a) (false,b),
      fun a b => by simpa [pairType] using hh (false,a) (true,b),
      fun a b => by simpa [pairType] using hh (true,a) (false,b),
      fun a b => by simpa [pairType] using hh (true,a) (true,b)⟩
  · rintro ⟨h₀,h₁,h₂,h₃⟩
    funext p q
    apply propext
    obtain ⟨p,a⟩ := p
    obtain ⟨q,b⟩ := q
    cases p <;> cases q <;> simp only [pairType, Bool.false_eq_true,
      ↓reduceIte] <;> first | exact h₀ a b | exact h₁ a b | exact h₂ a b | exact h₃ a b

private def modelLE {R : Type*} [LinearOrder R] (x y : I → A)
    (p q : R × I) : Prop :=
  if p.1 < q.1 then x p.2 ≤ y q.2 else
    if q.1 < p.1 then y p.2 ≤ x q.2 else x p.2 ≤ x q.2

private lemma modelLE_three (x : Fin 3 → I → A)
    (h₁ : pairType (x 0) (x 1) = pairType (x 0) (x 2))
    (h₂ : pairType (x 0) (x 1) = pairType (x 1) (x 2))
    (i j : Fin 3) (a b : I) :
    modelLE (x 0) (x 1) (i,a) (j,b) ↔ x i a ≤ x j b := by
  obtain ⟨h₁₀,h₁₁,h₁₂,h₁₃⟩ := pairType_eq_iff.mp h₁
  obtain ⟨h₂₀,h₂₁,h₂₂,h₂₃⟩ := pairType_eq_iff.mp h₂
  fin_cases i <;> fin_cases j <;> simp only [modelLE, Fin.reduceLT, ↓reduceIte]
  · rfl
  · rfl
  · exact h₁₁ a b
  · rfl
  · exact h₂₀ a b
  · exact h₂₁ a b
  · exact h₁₂ a b
  · exact h₂₂ a b
  · exact (h₂₀ a b).trans (h₂₃ a b)

/-- Any three elements of a linear order have the same comparison pattern
as a triple in `Fin 3`, with repetitions retained. -/
private lemma compress_three {R : Type*} [LinearOrder R] (v : Fin 3 → R) :
    ∃ f : Fin 3 → Fin 3, ∀ i j, (f i < f j ↔ v i < v j) := by
  classical
  let S : Finset R := Finset.univ.image v
  have hc : S.card ≤ 3 := (Finset.card_image_le).trans (by simp)
  let e : S ↪o Fin 3 := (S.orderIsoOfFin rfl).symm.toOrderEmbedding.trans
    (Fin.castLEOrderEmb hc)
  let f : Fin 3 → Fin 3 := fun i => e ⟨v i, by simp [S]⟩
  exact ⟨f, fun i j => e.lt_iff_lt⟩

private lemma modelLE_transfer {R T : Type*} [LinearOrder R] [LinearOrder T]
    (x y : I → A) {r s : R} {u v : T} (h₁ : r < s ↔ u < v)
    (h₂ : s < r ↔ v < u) (a b : I) :
    modelLE x y (r,a) (s,b) ↔ modelLE x y (u,a) (v,b) := by
  simp only [modelLE, h₁, h₂]

private lemma modelLE_trans {R : Type*} [LinearOrder R]
    (x : Fin 3 → I → A)
    (h₁ : pairType (x 0) (x 1) = pairType (x 0) (x 2))
    (h₂ : pairType (x 0) (x 1) = pairType (x 1) (x 2)) :
    Transitive (modelLE (R := R) (x 0) (x 1)) := by
  intro p q r hpq hqr
  let v : Fin 3 → R := ![p.1,q.1,r.1]
  obtain ⟨f, hf⟩ := compress_three v
  have ht (i j : Fin 3) (a b : I) :
      modelLE (x 0) (x 1) (v i,a) (v j,b) ↔ x (f i) a ≤ x (f j) b :=
    (modelLE_transfer (x 0) (x 1) (hf i j).symm (hf j i).symm a b).trans
      (modelLE_three x h₁ h₂ (f i) (f j) a b)
  exact (ht 0 2 p.2 r.2).mpr
    (((ht 0 1 p.2 q.2).mp hpq).trans ((ht 1 2 q.2 r.2).mp hqr))

/-- A finite total preorder is realized by weak comparisons in any
infinite linear order. -/
private lemma realize_finite_preorder {P : Type*} [Finite P]
    (R : P → P → Prop) (hr : Reflexive R) (ht : Transitive R)
    (hc : ∀ a b, R a b ∨ R b a) [Infinite A] :
    ∃ f : P → A, ∀ a b, (R a b ↔ f a ≤ f b) := by
  classical
  letI : Preorder P := { le := R, le_refl := hr, le_trans := fun _ _ _ h h' => ht h h' }
  letI : Std.Total (α := P) (· ≤ ·) := ⟨hc⟩
  let Q := Antisymmetrization P (· ≤ ·)
  haveI : Finite Q := inferInstanceAs (Finite (Quotient _))
  obtain ⟨e⟩ := nonempty_orderEmbedding_of_finite_infinite Q A
  refine ⟨fun a => e (toAntisymmetrization (· ≤ ·) a), fun a b => ?_⟩
  exact (e.le_iff_le.trans toAntisymmetrization_le_toAntisymmetrization_iff).symm

/-- A homogeneous triple of finite tuples can be reproduced as four
tuples with exactly the same pair type. -/
theorem homogeneous_three_to_four [Finite I] [Infinite A]
    (x : Fin 3 → I → A)
    (h₁ : pairType (x 0) (x 1) = pairType (x 0) (x 2))
    (h₂ : pairType (x 0) (x 1) = pairType (x 1) (x 2)) :
    ∃ y : Fin 4 → I → A, ∀ i j, i < j →
      pairType (y i) (y j) = pairType (x 0) (x 1) := by
  have hr : Reflexive (modelLE (R := Fin 4) (x 0) (x 1)) := by
    intro p
    simp [modelLE]
  have hc : ∀ p q : Fin 4 × I, modelLE (x 0) (x 1) p q ∨
      modelLE (x 0) (x 1) q p := by
    intro p q
    by_cases h : p.1 < q.1
    · simp only [modelLE, h, not_lt_of_gt h, ↓reduceIte]
      exact le_total _ _
    · by_cases h' : q.1 < p.1
      · simp only [modelLE, h, h', ↓reduceIte]
        exact le_total _ _
      · simp only [modelLE, h, h', ↓reduceIte]
        exact le_total _ _
  obtain ⟨f, hf⟩ := realize_finite_preorder (A := A)
    (modelLE (R := Fin 4) (x 0) (x 1)) hr (modelLE_trans x h₁ h₂) hc
  refine ⟨fun i a => f (i,a), fun i j hij => ?_⟩
  apply pairType_eq_iff.mpr
  have hh := (pairType_eq_iff.mp h₂).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    simpa only [modelLE, lt_self_iff_false, ↓reduceIte] using (hf (i,a) (i,b)).symm
  · intro a b
    simpa only [modelLE, hij, not_lt_of_gt hij, ↓reduceIte] using (hf (i,a) (j,b)).symm
  · intro a b
    simpa only [modelLE, hij, not_lt_of_gt hij, ↓reduceIte] using (hf (j,a) (i,b)).symm
  · intro a b
    have hs : f (j,a) ≤ f (j,b) ↔ x 0 a ≤ x 0 b := by
      simpa only [modelLE, lt_self_iff_false, ↓reduceIte] using (hf (j,a) (j,b)).symm
    exact hs.trans (hh a b)

/-- Invariance means adjacency depends only on the finite order type of
its two endpoint tuples. No definability assumption is hidden here. -/
def OrderTypeInvariant (G : SimpleGraph (I → A)) : Prop :=
  ∀ x y z w, pairType x y = pairType z w → G.Adj x y → G.Adj z w

lemma no_homogeneous_triangle [Finite I] [Infinite A]
    (G : SimpleGraph (I → A)) (hG : G.CliqueFree 4) (hInv : OrderTypeInvariant G)
    (x : Fin 3 → I → A) (hAdj : G.Adj (x 0) (x 1))
    (h₁ : pairType (x 0) (x 1) = pairType (x 0) (x 2))
    (h₂ : pairType (x 0) (x 1) = pairType (x 1) (x 2)) : False := by
  obtain ⟨y,hy⟩ := homogeneous_three_to_four x h₁ h₂
  have ha (i j : Fin 4) (hij : i < j) : G.Adj (y i) (y j) :=
    hInv _ _ _ _ (hy i j hij).symm hAdj
  exact Erdos595Work.no_adj_common_neighbors hG
    (ha 0 1 (by decide)) (ha 0 2 (by decide)) (ha 1 2 (by decide))
    (ha 0 3 (by decide)) (ha 1 3 (by decide)) (ha 2 3 (by decide))

private structure Tuple (I A : Type*) where
  val : I → A

/-- Every K4-free graph on fixed finite tuples, with adjacency invariant
under pair order type, is a countable union of triangle-free graphs. -/
theorem countable_cover [Finite I] [Infinite A]
    (G : SimpleGraph (I → A)) (hG : G.CliqueFree 4) (hInv : OrderTypeInvariant G) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  letI : LinearOrder (Tuple I A) := IsWellOrder.linearOrder WellOrderingRel
  let G' : SimpleGraph (Tuple I A) := G.comap Tuple.val
  let incl : G →g G' := { toFun := Tuple.mk, map_rel' := fun h => h }
  apply Erdos595Work.countable_union_of_hom incl
  obtain ⟨enc,henc⟩ := exists_injective_nat ((Bool × I) → (Bool × I) → Prop)
  let H : ℕ → SimpleGraph (Tuple I A) := fun n =>
    { Adj := fun x y => G'.Adj x y ∧ enc (pairType (min x y).val (max x y).val) = n
      symm := fun x y h => ⟨h.1.symm, by simpa only [min_comm, max_comm] using h.2⟩
      loopless := fun x h => G'.loopless x h.1 }
  refine ⟨H, ?_, ?_⟩
  · intro n S hS
    let x : Fin 3 ↪o Tuple I A := S.orderEmbOfFin hS.2
    have hadj (i j : Fin 3) (hij : i < j) : (H n).Adj (x i) (x j) :=
      hS.1 (S.orderEmbOfFin_mem _ i) (S.orderEmbOfFin_mem _ j) (x.strictMono hij).ne
    have ht (i j : Fin 3) (hij : i < j) : enc (pairType (x i).val (x j).val) = n := by
      have h := (hadj i j hij).2
      simpa only [min_eq_left (x.monotone hij.le), max_eq_right (x.monotone hij.le)] using h
    exact no_homogeneous_triangle G hG hInv (fun i => (x i).val) (hadj 0 1 (by decide)).1
      (henc ((ht 0 1 (by decide)).trans (ht 0 2 (by decide)).symm))
      (henc ((ht 0 1 (by decide)).trans (ht 1 2 (by decide)).symm))
  · ext x y
    simp only [SimpleGraph.iSup_adj]
    change G'.Adj x y ↔ ∃ n, G'.Adj x y ∧
      enc (pairType (min x y).val (max x y).val) = n
    simp

#print axioms no_homogeneous_triangle
#print axioms countable_cover
#print axioms homogeneous_three_to_four
end Erdos595TupleType
