import FormalConjecturesUtil

/-!
A free tag cannot simply be added to a full homogeneous weighted lift.
The common scalar ray gives an actual biclique, independently of the formula
for the homogeneous functions. This does not settle the extremal conjecture.
-/

open SimpleGraph Finset Classical

namespace Erdos714HomogeneousTags

variable {F V L R : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Tagged homogeneous functions with full nonzero scalar weights on both sides. -/
def graph (f : L → R → V → F) :
    SimpleGraph ((L × V × Fˣ) ⊕ (R × V × Fˣ)) where
  Adj u v := match u, v with
    | .inl x, .inr y => f x.1 y.1 (x.2.1 + y.2.1) = (x.2.2 : F)*(y.2.2 : F)
    | .inr y, .inl x => f x.1 y.1 (x.2.1 + y.2.1) = (x.2.2 : F)*(y.2.2 : F)
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- Distinct tags can be normalized at a common center. The nonzero scalars
then parameterize distinct columns on one ray. No polynomial assumption is used. -/
def rayCopy (f : L → R → V → F) (d : ℕ)
    (hf : ∀ l r (a : F) v, f l r (a • v) = a^d * f l r v)
    (r₀ : R) (v : V) (hv : v ≠ 0) (x₀ : V)
    {s t : ℕ} (tags : Fin s ↪ L) (scalars : Fin t ↪ Fˣ)
    (hnz : ∀ i, f (tags i) r₀ v ≠ 0) :
    Copy (completeBipartiteGraph (Fin s) (Fin t)) (graph f) := by
  classical
  let rows : Fin s ↪ L × V × Fˣ :=
    ⟨fun i => (tags i, -x₀, Units.mk0 (f (tags i) r₀ v) (hnz i)), by
      intro i j h
      exact tags.injective (congrArg Prod.fst h)⟩
  let cols : Fin t ↪ R × V × Fˣ :=
    ⟨fun j => (r₀, x₀ + (scalars j : F) • v, (scalars j)^d), by
      intro i j h
      apply scalars.injective
      apply Units.ext
      apply smul_left_injective F hv
      exact add_left_cancel (congrArg (fun p : R × V × Fˣ => p.2.1) h)⟩
  refine ⟨⟨rows.sumMap cols, ?_⟩, (rows.sumMap cols).injective⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j =>
      change f (tags i) r₀ (-x₀ + (x₀ + (scalars j : F) • v)) =
        f (tags i) r₀ v * ((scalars j)^d : Fˣ)
      simpa only [neg_add_cancel_left, Units.val_pow_eq_pow_val, mul_comm] using
        hf (tags i) r₀ (scalars j) v
  | inr j =>
    cases b with
    | inr i => simp at hab
    | inl i =>
      change f (tags i) r₀ (-x₀ + (x₀ + (scalars j : F) • v)) =
        f (tags i) r₀ v * ((scalars j)^d : Fˣ)
      simpa only [neg_add_cancel_left, Units.val_pow_eq_pow_val, mul_comm] using
        hf (tags i) r₀ (scalars j) v

/-- Enough usable tags at just one nonzero point already force the forbidden copy. -/
theorem not_free_of_tags [Fintype F] [Fintype L]
    (f : L → R → V → F) (d : ℕ)
    (hf : ∀ l r (a : F) v, f l r (a • v) = a^d * f l r v)
    (r₀ : R) (v : V) (hv : v ≠ 0) {r : ℕ}
    (hF : r ≤ Fintype.card Fˣ)
    (hL : r ≤ (univ.filter (fun l => f l r₀ v ≠ 0)).card) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph f) := by
  classical
  obtain ⟨tags, htags⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := univ.filter (fun l => f l r₀ v ≠ 0)) (by simpa using hL)
  obtain ⟨scalars⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := Fˣ) (by simpa using hF)
  intro hfree
  exact hfree ⟨rayCopy f d hf r₀ v hv 0 tags scalars
    (fun i => (mem_filter.mp (htags ⟨i,rfl⟩)).2)⟩

/-- Freeness bounds the number of nonvanishing tags at every nonzero point. -/
theorem support_bound [Fintype F] [Fintype L]
    (f : L → R → V → F) (d : ℕ)
    (hf : ∀ l r (a : F) v, f l r (a • v) = a^d * f l r v)
    {r : ℕ} (hF : r ≤ Fintype.card Fˣ)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph f))
    (r₀ : R) (v : V) (hv : v ≠ 0) :
    (univ.filter (fun l => f l r₀ v ≠ 0)).card ≤ r-1 := by
  classical
  have hlt : (univ.filter (fun l => f l r₀ v ≠ 0)).card < r := by
    by_contra! h
    exact not_free_of_tags f d hf r₀ v hv hF h hfree
  omega

/-- In particular, anisotropic homogeneous forms cannot be extended by an
unrestricted tag set of size at least four, over any field of size at least five. -/
theorem fourth_case [Fintype F] [Fintype L]
    (f : L → R → V → F) (d : ℕ)
    (hf : ∀ l r (a : F) v, f l r (a • v) = a^d * f l r v)
    (r₀ : R) (v : V) (hv : v ≠ 0)
    (hnz : ∀ l, f l r₀ v ≠ 0)
    (hq : 5 ≤ Fintype.card F) (hL : 4 ≤ Fintype.card L) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph f) := by
  classical
  apply not_free_of_tags f d hf r₀ v hv
  · rw [Fintype.card_units]
    omega
  · simpa [hnz] using hL

#print axioms rayCopy
#print axioms not_free_of_tags
#print axioms support_bound
#print axioms fourth_case

end Erdos714HomogeneousTags
