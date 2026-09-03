import FormalConjecturesUtil

/-!
An obstruction to attempts to reduce four common-neighbor equations to a
one-variable exceptional polynomial by making the other variables affine.
This is not a proof or disproof of Erdős Problem 714.
-/

open SimpleGraph Finset

namespace Erdos714AffineSlices

/-- The incidence graph of functions on a parameter set. -/
def graph {R X A : Type*} (f : R → X → A) : SimpleGraph (R ⊕ (X × A)) where
  Adj u v := match u, v with
    | .inl r, .inr p => f r p.1 = p.2
    | .inr p, .inl r => f r p.1 = p.2
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- If restrictions to a slice factor through a small coefficient set, sufficiently
many rows have the same restriction, and therefore form a biclique on that slice. -/
theorem not_free_of_slice_factorization
    {R X Y A C : Type*} [Fintype R] [Fintype Y] [Fintype C]
    (f : R → X → A) (slice : Y ↪ X) (coeff : R → C) (eval : C → Y → A)
    (hfactor : ∀ r y, f r (slice y) = eval (coeff r) y)
    {s t : ℕ} (hs : 0 < s) (ht : t ≤ Fintype.card Y)
    (hcard : Fintype.card C * (s - 1) < Fintype.card R) :
    ¬ (completeBipartiteGraph (Fin s) (Fin t)).Free (graph f) := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := (univ : Finset R)) (t := (univ : Finset C)) (f := coeff)
    (fun _ _ => mem_univ _) (by simpa using hcard)
  let T := (univ : Finset R).filter (fun r => coeff r = c)
  have hT : s ≤ T.card := by dsimp [T]; omega
  obtain ⟨rows, hrows⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin s) (s := T) (by simpa using hT)
  obtain ⟨cols⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin t) (β := Y) (by simpa using ht)
  have hcoeff (i : Fin s) : coeff (rows i) = c :=
    (mem_filter.mp (hrows ⟨i, rfl⟩)).2
  let points : Fin t ↪ X × A :=
    ⟨fun j => (slice (cols j), eval c (cols j)), by
      intro i j hij
      exact cols.injective (slice.injective (congrArg Prod.fst hij))⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨rows.sumMap points, ?_⟩, (rows.sumMap points).injective⟩⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j =>
      change f (rows i) (slice (cols j)) = eval c (cols j)
      rw [hfactor, hcoeff]
  | inr j =>
    cases b with
    | inl i =>
      change f (rows i) (slice (cols j)) = eval c (cols j)
      rw [hfactor, hcoeff]
    | inr i => simp at hab

/-- Coefficient-count bound for every free full evaluation graph in this model. -/
theorem row_bound_of_slice_factorization
    {R X Y A C : Type*} [Fintype R] [Fintype Y] [Fintype C]
    (f : R → X → A) (slice : Y ↪ X) (coeff : R → C) (eval : C → Y → A)
    (hfactor : ∀ r y, f r (slice y) = eval (coeff r) y)
    {s t : ℕ} (hs : 0 < s) (ht : t ≤ Fintype.card Y)
    (hfree : (completeBipartiteGraph (Fin s) (Fin t)).Free (graph f)) :
    Fintype.card R ≤ Fintype.card C * (s - 1) := by
  by_contra! hcard
  exact not_free_of_slice_factorization f slice coeff eval hfactor hs ht hcard hfree

/-- For a fixed first coordinate, all affine two-variable restrictions are
specified by three coefficients. Arbitrary dependence on the first coordinate
cannot avoid this obstruction. -/
theorem affine_slice_obstruction {F R T : Type*} [Semiring F] [Fintype F]
    [Fintype R] (t₀ : T) (A B C : R → T → F)
    (hq : 4 ≤ Fintype.card F) (hR : Fintype.card F ^ 3 * 3 < Fintype.card R) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun r (p : T × (F × F)) =>
        A r p.1 + B r p.1 * p.2.1 + C r p.1 * p.2.2)) := by
  let slice : F × F ↪ T × (F × F) :=
    ⟨fun p => (t₀, p), fun _ _ h => congrArg Prod.snd h⟩
  apply not_free_of_slice_factorization _ slice
    (fun r => (A r t₀, B r t₀, C r t₀))
    (fun c p => c.1 + c.2.1 * p.1 + c.2.2 * p.2)
    (fun _ _ => rfl) (by decide : 0 < 4)
  · simp only [Fintype.card_prod]
    nlinarith
  · simpa only [Fintype.card_prod, Nat.reduceSub, pow_succ, pow_zero, one_mul,
      mul_assoc] using hR

/-- In particular, a four-dimensional row set is too large over every field
of order at least four. The conclusion also holds over finite semirings. -/
theorem fourth_case {F T : Type*} [Semiring F] [Fintype F]
    (t₀ : T) (A B C : (Fin 4 → F) → T → F) (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun r (p : T × (F × F)) =>
        A r p.1 + B r p.1 * p.2.1 + C r p.1 * p.2.2)) := by
  apply affine_slice_obstruction t₀ A B C hq
  simp only [Fintype.card_fun, Fintype.card_fin]
  calc
    Fintype.card F ^ 3 * 3 < Fintype.card F ^ 3 * Fintype.card F :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    _ = Fintype.card F ^ 4 := by ring

end Erdos714AffineSlices

#print axioms Erdos714AffineSlices.not_free_of_slice_factorization
#print axioms Erdos714AffineSlices.row_bound_of_slice_factorization
#print axioms Erdos714AffineSlices.affine_slice_obstruction
#print axioms Erdos714AffineSlices.fourth_case
