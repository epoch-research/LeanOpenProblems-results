import Submission.IntervalHullWindow

/-! Computable finite formulas for a closed hull step, with an exact comparison
with the infinite-domain definitions. No quadratic positivity is asserted. -/
namespace Erdos970.IntervalRescaling.IntegerHull
open BlockSieve.SievePolynomial

/-- Finite evaluation is meaningful over integers as well as over reals. -/
def finiteStep {R : Type*} [LinearOrder R] [Sub R] (p : ℕ)
    (old : (ℕ → R) × (ℕ → R)) : (ℕ → R) × (ℕ → R) :=
  (fun n => (lowerCandidates p n).sup' ⟨n, Finset.mem_insert_self _ _⟩
    (fun m => old.1 m - old.2 (ceilQuotient m p)),
   fun n => (upperCandidates p n).inf' ⟨n, Finset.mem_insert_self _ _⟩
    (fun m => old.2 m - old.1 (m / p)))

theorem finiteStep_eq_closed {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 2 ≤ p) :
    finiteStep p (l, u) =
      (lowerHull (rawLower p l u), upperHull (rawUpper p l u)) := by
  apply Prod.ext
  · funext n
    exact (lowerHull_eq_candidates (h.lower_mono hl) p (by omega) n).symm
  · funext n
    exact (h.upperHull_eq_candidates hl p hp n).symm

noncomputable def intCastLatticeHom : LatticeHom ℤ ℝ where
  toFun := Int.cast
  map_sup' _ _ := Int.cast_max
  map_inf' _ _ := Int.cast_min

noncomputable def realPair (v : (ℕ → ℤ) × (ℕ → ℤ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (fun n => (v.1 n : ℝ), fun n => (v.2 n : ℝ))

/-- Kernel computations with integer bounds evaluate the same finite formula. -/
theorem cast_finiteStep (p : ℕ) (v : (ℕ → ℤ) × (ℕ → ℤ)) :
    realPair (finiteStep p v) = finiteStep p (realPair v) := by
  apply Prod.ext <;> funext n
  · change intCastLatticeHom ((lowerCandidates p n).sup'
      ⟨n, Finset.mem_insert_self _ _⟩ (fun m => v.1 m - v.2 (ceilQuotient m p))) = _
    rw [map_finset_sup']
    apply Finset.sup'_congr _ rfl
    intro m hm
    exact Int.cast_sub _ _
  · change intCastLatticeHom ((upperCandidates p n).inf'
      ⟨n, Finset.mem_insert_self _ _⟩ (fun m => v.2 m - v.1 (m / p))) = _
    rw [map_finset_inf']
    apply Finset.inf'_congr _ rfl
    intro m hm
    exact Int.cast_sub _ _

/-- Integer finite evaluation and the infinite real-valued closed step agree. -/
theorem cast_finiteStep_eq_closed (p : ℕ) (hp : 2 ≤ p) (v : (ℕ → ℤ) × (ℕ → ℤ))
    (h : Compatible (realPair v).1 (realPair v).2) (hl : ∀ n, 0 ≤ (realPair v).1 n) :
    realPair (finiteStep p v) =
      (lowerHull (rawLower p (realPair v).1 (realPair v).2),
       upperHull (rawUpper p (realPair v).1 (realPair v).2)) := by
  rw [cast_finiteStep]
  exact finiteStep_eq_closed h hl p hp


noncomputable def closedStep (p : ℕ) (v : (ℕ → ℝ) × (ℕ → ℝ)) :
    (ℕ → ℝ) × (ℕ → ℝ) :=
  (lowerHull (rawLower p v.1 v.2), upperHull (rawUpper p v.1 v.2))

theorem cast_finiteStep_shape (p : ℕ) (hp : 2 ≤ p) (v : (ℕ → ℤ) × (ℕ → ℤ))
    (h : Compatible (realPair v).1 (realPair v).2) (hl : ∀ n, 0 ≤ (realPair v).1 n) :
    Compatible (realPair (finiteStep p v)).1 (realPair (finiteStep p v)).2 ∧
      ∀ n, 0 ≤ (realPair (finiteStep p v)).1 n := by
  rw [cast_finiteStep_eq_closed p hp v h hl]
  exact h.closed_step hl p (by omega)

/-- Two integer finite steps evaluate exactly the two infinite real steps. -/
theorem cast_finiteStep_twice (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (v : (ℕ → ℤ) × (ℕ → ℤ))
    (h : Compatible (realPair v).1 (realPair v).2) (hl : ∀ n, 0 ≤ (realPair v).1 n) :
    realPair (finiteStep q (finiteStep p v)) = closedStep q (closedStep p (realPair v)) := by
  have hs := cast_finiteStep_shape p hp v h hl
  change _ = closedStep q (closedStep p (realPair v))
  have he : realPair (finiteStep q (finiteStep p v)) =
      closedStep q (realPair (finiteStep p v)) :=
    cast_finiteStep_eq_closed q hq (finiteStep p v) hs.1 hs.2
  rw [he]
  congr 1
  exact cast_finiteStep_eq_closed p hp v h hl

#print axioms cast_finiteStep_eq_closed
#print axioms cast_finiteStep_twice
end Erdos970.IntervalRescaling.IntegerHull
