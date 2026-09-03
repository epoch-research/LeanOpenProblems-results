import FormalConjecturesUtil

/-! An obstruction to low-degree polynomial fibers in weighted graph constructions.
This does not assert a proof or disproof of the extremal conjecture.
-/

open Finset Polynomial SimpleGraph Classical

namespace Erdos714PolynomialFibers

variable {F V X : Type*} [Field F]

/-- A column `v` is joined to `(x,a)` when its polynomial takes the nonzero
value `a` at `x`. All nonzero row weights are included. -/
def graph (x : X → F) (P : V → F[X]) : SimpleGraph ((X × Fˣ) ⊕ V) where
  Adj u v := match u, v with
    | .inl u, .inr y => (P y).eval (x u.1) = (u.2 : F)
    | .inr y, .inl u => (P y).eval (x u.1) = (u.2 : F)
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- Bounded-degree polynomials are determined by their first `d+1` coefficients. -/
lemma eq_of_coefficients {p q : F[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (h : (fun i : Fin (d+1) => p.coeff i) = (fun i : Fin (d+1) => q.coeff i)) :
    p = q := by
  ext n
  by_cases hn : n < d+1
  · exact congrFun h ⟨n, hn⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n),
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n)]

variable [Fintype F] [Fintype X]

/-- On any injectively parameterized finite set, a nonzero polynomial has
at most `d` zero values if its degree is at most `d`. -/
lemma many_nonzero_values (x : X ↪ F) {p : F[X]} {d r : ℕ}
    (hp : p ≠ 0) (hd : p.natDegree ≤ d) (hq : r + d ≤ Fintype.card X) :
    r ≤ (univ.filter (fun u : X => p.eval (x u) ≠ 0)).card := by
  classical
  let Z : Finset X := univ.filter (fun u => p.eval (x u) = 0)
  have hz : Z.card ≤ d := by
    have hroots : (Z.map x).val ⊆ p.roots := by
      intro a ha
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
      apply (Polynomial.mem_roots hp).mpr
      exact (Finset.mem_filter.mp hu).2
    have hz' := (Polynomial.card_le_degree_of_subset_roots hroots).trans hd
    simpa using hz'
  have hsplit : Z.card + (univ.filter (fun u : X => p.eval (x u) ≠ 0)).card =
      Fintype.card X := by
    simpa [Z] using Finset.card_filter_add_card_filter_not
      (s := (univ : Finset X)) (p := fun u : X => p.eval (x u) = 0)
  omega

/-- More than `(r-1)q^(d+1)` nonzero polynomial columns of degree at most `d`
force a balanced `r`-by-`r` biclique once the parameter set has at least `r+d` points. -/
theorem not_free_of_many_columns (x : X ↪ F) (P : V → F[X]) (R : Finset V) {r d : ℕ}
    (hr : 0 < r) (hq : r + d ≤ Fintype.card X)
    (hd : ∀ v, (P v).natDegree ≤ d) (hnz : ∀ v ∈ R, P v ≠ 0)
    (hc : (Fintype.card F) ^ (d+1) * (r-1) < R.card) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph x P) := by
  classical
  let coefficients : V → (Fin (d+1) → F) := fun v i => (P v).coeff i
  obtain ⟨c, _, hcf⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := R) (t := univ) (f := coefficients) (fun _ _ => mem_univ _)
    (by simpa using hc)
  let T := R.filter (fun v => coefficients v = c)
  have hT : r ≤ T.card := by dsimp [T]; omega
  obtain ⟨g : Fin r ↪ V, hg⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := Fin r) (s := T) (by simpa using hT)
  have hgi (i : Fin r) : g i ∈ T := hg ⟨i, rfl⟩
  let i₀ : Fin r := ⟨0, hr⟩
  let p := P (g i₀)
  have hp : p ≠ 0 := hnz (g i₀) (mem_filter.mp (hgi i₀)).1
  have hpg (i : Fin r) : P (g i) = p := by
    apply eq_of_coefficients (hd (g i)) (hd (g i₀))
    exact (mem_filter.mp (hgi i)).2.trans (mem_filter.mp (hgi i₀)).2.symm
  have hU := many_nonzero_values x hp (hd (g i₀)) hq
  let U : Finset X := univ.filter (fun u => p.eval (x u) ≠ 0)
  obtain ⟨u : Fin r ↪ X, hu⟩ :=
    Function.Embedding.exists_of_card_le_finset (α := Fin r) (s := U)
      (by simpa [U] using hU)
  have hnu (i : Fin r) : p.eval (x (u i)) ≠ 0 := (mem_filter.mp (hu ⟨i, rfl⟩)).2
  let f : Fin r ↪ X × Fˣ :=
    ⟨fun i => (u i, Units.mk0 (p.eval (x (u i))) (hnu i)), by
      intro i j hij
      exact u.injective (congrArg Prod.fst hij)⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨f.sumMap g, ?_⟩, (f.sumMap g).injective⟩⟩
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => simp at hab
    | inr j => change (P (g j)).eval (x (u i)) = p.eval (x (u i)); rw [hpg]
  | inr j =>
    cases b with
    | inl i => change (P (g j)).eval (x (u i)) = p.eval (x (u i)); rw [hpg]
    | inr i => simp at hab

/-- In particular, a free graph in this model has few nonzero columns. Zero
columns are permitted, but they have no neighbors. -/
theorem nonzero_column_bound [Fintype V] (x : X ↪ F) (P : V → F[X]) {r d : ℕ}
    (hr : 0 < r) (hq : r + d ≤ Fintype.card X)
    (hd : ∀ v, (P v).natDegree ≤ d)
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free (graph x P)) :
    (univ.filter (fun v => P v ≠ 0)).card ≤ (Fintype.card F) ^ (d+1) * (r-1) := by
  classical
  by_contra! hc
  exact not_free_of_many_columns x P _ hr hq hd
    (fun v hv => (mem_filter.mp hv).2) hc hfree

/-- The particular quadratic obstruction relevant to an attempted four-dimensional
weighted construction. Six distinct parameter points are sufficient. -/
theorem quadratic_obstruction [Fintype V] (x : X ↪ F) (P : V → F[X])
    (hx : 6 ≤ Fintype.card X) (hV : Fintype.card V = (Fintype.card F) ^ 4)
    (hd : ∀ v, (P v).natDegree ≤ 2) (hnz : ∀ v, P v ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph x P) := by
  classical
  have hq : 6 ≤ Fintype.card F := hx.trans (Fintype.card_le_of_embedding x)
  apply not_free_of_many_columns x P univ (r := 4) (d := 2) (by omega)
    (by omega) hd (fun v _ => hnz v)
  simp only [card_univ, hV]
  norm_num only [Nat.reduceAdd, Nat.reduceSub]
  calc
    (Fintype.card F) ^ 3 * 3 < (Fintype.card F) ^ 3 * Fintype.card F :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
    _ = (Fintype.card F) ^ 4 := by ring

/-- A polynomial-family copy transfers the obstruction to an arbitrary ambient
graph. The ambient graph need not itself have a polynomial definition. -/
theorem not_free_of_polynomial_copy {W : Type*} (G : SimpleGraph W)
    (x : X ↪ F) (P : V → F[X]) (e : Copy (graph x P) G)
    (R : Finset V) {r d : ℕ} (hr : 0 < r) (hx : r + d ≤ Fintype.card X)
    (hd : ∀ v, (P v).natDegree ≤ d) (hnz : ∀ v ∈ R, P v ≠ 0)
    (hc : (Fintype.card F) ^ (d+1) * (r-1) < R.card) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free G := by
  intro hfree
  apply not_free_of_many_columns x P R hr hx hd hnz hc
  rintro ⟨c⟩
  exact hfree ⟨e.comp c⟩

end Erdos714PolynomialFibers

#print axioms Erdos714PolynomialFibers.not_free_of_many_columns
#print axioms Erdos714PolynomialFibers.nonzero_column_bound

#print axioms Erdos714PolynomialFibers.quadratic_obstruction
#print axioms Erdos714PolynomialFibers.not_free_of_polynomial_copy
