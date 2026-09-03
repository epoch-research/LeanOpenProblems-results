import Submission.PolynomialGraph
import Submission.DivisorPower

/-!
# Uniform finite obstructions to bounded polynomial graph covers

For fixed natural numbers `C` and `M`, a polynomial graph of prime-square
complementary factors has `M * R.card < H` for all sufficiently large `H`,
uniformly in the finite set, the representations, and the polynomial. Only the
bounds on the positive denominator and the absolute constant value are used;
there is no bound on the degree or on the other polynomial coefficients.

Consequently a set with `3 * H ≤ 16 * R.card` cannot be covered by a fixed number
`L` of these bounded graphs. The graphs may overlap. The proof counts their
filtered fibres and also handles `C = 0`, `M = 0`, and `L = 0`.

Combining this obstruction with `PrivateSquares` gives witnesses in any interval
containing no squarefree number, and these witnesses admit no such bounded cover.
This is only a necessary condition: no inverse theorem asserting existence of a
bounded graph cover is assumed or proved. In particular, this does not settle a
squarefree-gap conjecture.
-/

open Finset Filter

namespace GraphCover

/-- A uniform sublinear bound for a single polynomial graph. The threshold
only depends on `C` and `M`, not on the polynomial, its degree, or the finite set. -/
theorem eventually_graph_card_lt (C M : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ R : Finset ℕ, ∀ p m : ℕ → ℕ,
      ∀ F : Polynomial ℤ, ∀ b : ℕ,
      0 < b → b ≤ H ^ C → Int.natAbs (F.eval 0) ≤ H ^ C →
      (∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) →
      Set.InjOn p (R : Set ℕ) → Set.InjOn m (R : Set ℕ) →
      (∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ)) →
      M * R.card < H := by
  filter_upwards [DivisorPower.eventually_mul_card_divisors_lt C M,
    eventually_ge_atTop 2, eventually_gt_atTop (M * C)] with H hdiv hH hMC
  intro R p m F b hb hbC hFC hrep hpinj hminj hgraph
  rcases PolynomialGraph.polynomial_graph_card_bound R p m F H b C
      hb hH hbC hrep hpinj hminj hgraph with ⟨_, hcard⟩ | hcard
  · exact (Nat.mul_le_mul_left M hcard).trans_lt (hdiv _ hFC)
  · have hRC : R.card ≤ C := by omega
    exact (Nat.mul_le_mul_left M hRC).trans_lt hMC

/-- A uniformly positive-density set of distinct prime-square representations
cannot be covered by `L` polynomial graphs of bounded denominator and constant
value, eventually in `H`. No degree bound is required. -/
theorem eventually_no_bounded_graph_cover (C L : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ R : Finset ℕ, ∀ p m : ℕ → ℕ,
      3 * H ≤ 16 * R.card →
      (∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) →
      Set.InjOn p (R : Set ℕ) → Set.InjOn m (R : Set ℕ) →
      ¬ ∃ (F : Fin L → Polynomial ℤ) (b : Fin L → ℕ),
        (∀ j, 0 < b j ∧ b j ≤ H ^ C ∧ Int.natAbs ((F j).eval 0) ≤ H ^ C) ∧
        (∀ n ∈ R, ∃ j, (b j : ℤ) * (m n : ℤ) = (F j).eval (n : ℤ)) := by
  classical
  filter_upwards [eventually_graph_card_lt C (16 * L), eventually_ge_atTop 1]
    with H hsmall hH
  intro R p m hcard hrep hpinj hminj
  rintro ⟨F, b, hbounds, hcover⟩
  by_cases hL : L = 0
  · subst L
    have hR : R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨j, _⟩ := hcover n hn
      exact Fin.elim0 j
    simp only [hR, card_empty, mul_zero] at hcard
    omega
  · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
    let Rj : Fin L → Finset ℕ := fun j =>
      R.filter (fun n => (b j : ℤ) * (m n : ℤ) = (F j).eval (n : ℤ))
    have hsub (j : Fin L) : Rj j ⊆ R := filter_subset _ _
    have hfibre (j : Fin L) : (16 * L) * (Rj j).card < H := by
      apply hsmall (Rj j) p m (F j) (b j)
        (hbounds j).1 (hbounds j).2.1 (hbounds j).2.2
      · exact fun n hn => hrep n (hsub j hn)
      · exact Set.InjOn.mono (hsub j) hpinj
      · exact Set.InjOn.mono (hsub j) hminj
      · exact fun n hn => (mem_filter.mp hn).2
    have hcovered : R ⊆ (univ : Finset (Fin L)).biUnion Rj := by
      intro n hn
      obtain ⟨j, hj⟩ := hcover n hn
      exact mem_biUnion.mpr ⟨j, mem_univ j, mem_filter.mpr ⟨hn, hj⟩⟩
    have hcount : R.card ≤ ∑ j : Fin L, (Rj j).card :=
      (card_le_card hcovered).trans card_biUnion_le
    have hscaled : L * (16 * R.card) ≤ L * H := by
      calc
        L * (16 * R.card) = (16 * L) * R.card := by ring
        _ ≤ (16 * L) * ∑ j : Fin L, (Rj j).card := Nat.mul_le_mul_left _ hcount
        _ = ∑ j : Fin L, (16 * L) * (Rj j).card := mul_sum _ _ _
        _ ≤ ∑ _j : Fin L, H := sum_le_sum (fun j _ => (hfibre j).le)
        _ = L * H := by simp
    have hbound : 16 * R.card ≤ H := Nat.le_of_mul_le_mul_left hscaled hLpos
    omega

/-- Every sufficiently long interval containing no squarefree number supplies
private-square witnesses with no bounded `L`-graph cover. This combines necessary
conditions only; the missing inverse assertion that a cover exists is not used. -/
theorem eventually_exists_private_squares_no_bounded_graph_cover (C L : ℕ) :
    ∀ᶠ H : ℕ in atTop, ∀ x : ℕ,
      (∀ n : ℕ, x < n → n ≤ x + H → ¬ Squarefree n) →
      ∃ R : Finset ℕ, ∃ p m : ℕ → ℕ,
        3 * H ≤ 16 * R.card ∧ R ⊆ Ioc x (x + H) ∧
        (∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n) ∧
        Set.InjOn p (R : Set ℕ) ∧ Set.InjOn m (R : Set ℕ) ∧
        (∀ n ∈ R, ∀ n' ∈ R, n ≠ n' → ¬ p n ∣ n') ∧
        ¬ ∃ (F : Fin L → Polynomial ℤ) (b : Fin L → ℕ),
          (∀ j, 0 < b j ∧ b j ≤ H ^ C ∧ Int.natAbs ((F j).eval 0) ≤ H ^ C) ∧
          (∀ n ∈ R, ∃ j, (b j : ℤ) * (m n : ℤ) = (F j).eval (n : ℤ)) := by
  filter_upwards [PrivateSquares.eventually_exists_private_squares 1 (by decide),
    eventually_no_bounded_graph_cover C L] with H hprivate hno
  intro x hall
  obtain ⟨R, p, m, hcard, hR, hrep, hpinj, hminj, hpriv⟩ := hprivate x hall
  simp only [one_mul] at hrep
  exact ⟨R, p, m, hcard, hR, hrep, hpinj, hminj, hpriv,
    hno R p m hcard hrep hpinj hminj⟩

#print axioms eventually_graph_card_lt
#print axioms eventually_no_bounded_graph_cover
#print axioms eventually_exists_private_squares_no_bounded_graph_cover

end GraphCover
