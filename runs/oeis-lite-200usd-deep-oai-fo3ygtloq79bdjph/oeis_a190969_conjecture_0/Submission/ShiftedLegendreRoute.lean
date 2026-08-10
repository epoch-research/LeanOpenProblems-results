import FormalConjectures.Util.ProblemImports

open Finset Nat Polynomial
open scoped BigOperators

/-!
Scratch file for `oeis_a190969_conjecture_0`: shifted-Legendre and
recurrence reductions with fully closed proofs.
-/

def aSL : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * aSL (n + 1) - 8 * aSL n

/-- The fourth subsequence of A190969 satisfies the second-order recurrence with
characteristic roots the fourth powers of the roots of `x^2 - 5x + 8`. -/
def bSL : ℕ → ℤ
| 0 => 0
| 1 => 45
| n + 2 => -47 * bSL (n + 1) - 4096 * bSL n

def cSL (n : ℕ) : ℤ := aSL (n + 8) + 47 * aSL (n + 4) + 4096 * aSL n

lemma cSL_succ_succ (n : ℕ) : cSL (n + 2) = 5 * cSL (n + 1) - 8 * cSL n := by
  unfold cSL
  change aSL ((n + 8) + 2) + 47 * aSL ((n + 4) + 2) + 4096 * aSL (n + 2) =
    5 * (aSL ((n + 7) + 2) + 47 * aSL ((n + 3) + 2) + 4096 * aSL (n + 1)) -
      8 * (aSL (n + 8) + 47 * aSL (n + 4) + 4096 * aSL n)
  simp [aSL]
  ring

lemma cSL_eq_zero (n : ℕ) : cSL n = 0 := by
  suffices h : cSL n = 0 ∧ cSL (n + 1) = 0 from h.1
  induction n with
  | zero => norm_num [cSL, aSL]
  | succ n ih =>
      exact ⟨ih.2, by rw [cSL_succ_succ n, ih.1, ih.2]; ring⟩

lemma aSL_add_eight (n : ℕ) : aSL (n + 8) = -47 * aSL (n + 4) - 4096 * aSL n := by
  have h := cSL_eq_zero n
  unfold cSL at h
  omega

lemma aSL_four_mul_eq_bSL_pair (k : ℕ) :
    aSL (4 * k) = bSL k ∧ aSL (4 * (k + 1)) = bSL (k + 1) := by
  induction k with
  | zero => norm_num [aSL, bSL]
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [bSL]
      have h := aSL_add_eight (4 * k)
      have h1 : 4 * (k + 1) = 4 * k + 4 := by omega
      have h2 : 4 * (k + 2) = 4 * k + 8 := by omega
      rw [h2, h, ← h1, ih.2, ih.1]

lemma aSL_four_mul_eq_bSL (k : ℕ) : aSL (4 * k) = bSL k :=
  (aSL_four_mul_eq_bSL_pair k).1

/-- Mathlib's shifted Legendre polynomial expanded after evaluation in any ring.  This is
 the exact finite hypergeometric polynomial whose coefficients are congruent to
 `choose (2*k) k ^ 2 / 16^k` modulo an odd prime when `n = (p-1)/2`. -/
lemma aeval_shiftedLegendre_eq_sum (n : ℕ) {R : Type*} [CommRing R] (x : R) :
    aeval x (Polynomial.shiftedLegendre n) =
      ∑ k ∈ range (n + 1),
        ((((-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n + k).choose n : ℤ)) : ℤ) : R) * x ^ k := by
  simp [Polynomial.shiftedLegendre]

/-- Coefficient form of the same shifted-Legendre expansion, useful for rewriting
 truncated hypergeometric sums as polynomial evaluations. -/
lemma shiftedLegendre_coeff_int (n k : ℕ) :
    (Polynomial.shiftedLegendre n).coeff k =
      (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n + k).choose n : ℤ) := by
  simpa using Polynomial.coeff_shiftedLegendre n k

lemma central_choose_dvd_of_half_SL {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    p ∣ (2 * k).choose k := by
  apply hp.dvd_choose (a := k) (b := 2 * k)
  · exact hk
  · have hsub : 2 * k - k = k := by omega
    simpa [hsub] using hk
  · exact hhalf

lemma central_choose_cast_cube_eq_zero_zmod_pow2_SL {p k : ℕ}
    (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    (((2 * k).choose k : ℕ) : ZMod (p ^ 2)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans
    (by
      rcases central_choose_dvd_of_half_SL hp hk hhalf with ⟨d, hd⟩
      rw [hd]
      use d ^ 3
      ring)

/-- For all upper-half terms (`p ≤ 2*k`) the summand in the `p^2` part of the target theorem
 is already zero.  Thus only the lower half of the truncated hypergeometric sum remains. -/
lemma original_upper_half_term_zero_pow2_SL {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    (let num : ZMod (p ^ 2) := (aSL (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
     let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
     num * den⁻¹) = 0 := by
  dsimp
  rw [central_choose_cast_cube_eq_zero_zmod_pow2_SL hp hk hhalf]
  simp

/-- Combined recurrence and upper-half reduction for the `p^2` congruence. -/
lemma target_sum_pow2_reduces_to_lower_half_bSL (p : ℕ) (hp : p.Prime) :
    (range p).sum (fun k =>
      let num : ZMod (p ^ 2) := (aSL (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
      let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
      num * den⁻¹) =
    ((range p).filter (fun k => 2 * k < p)).sum (fun k =>
      let num : ZMod (p ^ 2) := (bSL k : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
      let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
      num * den⁻¹) := by
  rw [← sum_filter_add_sum_filter_not (s := range p) (p := fun k => 2 * k < p)]
  calc
    ((range p).filter (fun k => 2 * k < p)).sum (fun k =>
        let num : ZMod (p ^ 2) := (aSL (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
        let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
        num * den⁻¹) +
      ((range p).filter (fun k => ¬ 2 * k < p)).sum (fun k =>
        let num : ZMod (p ^ 2) := (aSL (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
        let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
        num * den⁻¹)
        = ((range p).filter (fun k => 2 * k < p)).sum (fun k =>
            let num : ZMod (p ^ 2) := (aSL (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
            let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
            num * den⁻¹) := by
          rw [add_eq_left]
          apply sum_eq_zero
          intro k hk
          simp only [mem_filter, mem_range, not_lt] at hk
          exact original_upper_half_term_zero_pow2_SL hp hk.1 hk.2
    _ = ((range p).filter (fun k => 2 * k < p)).sum (fun k =>
          let num : ZMod (p ^ 2) := (bSL k : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
          let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
          num * den⁻¹) := by
        apply sum_congr rfl
        intro k hk
        rw [aSL_four_mul_eq_bSL]
