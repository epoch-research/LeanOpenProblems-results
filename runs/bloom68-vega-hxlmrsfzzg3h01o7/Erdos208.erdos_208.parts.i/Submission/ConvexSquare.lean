import FormalConjecturesUtil

/-!
# Strict convexity of integer cofactors of square multiples

If three square multiples hit `(x, x + H]`, and their ordered bases lie in
`[N, 2 * N]` with `64 * H ≤ N`, their cofactors strictly decrease and are
strictly convex as a function of the base. No additional hypothesis on `x`
(such as a cubic horizon condition) is needed.

The proof is division-free. A drop of at least one in the first pair forces
`N ≤ 8 * b * (v - u)`. The integer gap `1 ≤ w - v` then makes the main term
in an exact scaled determinant identity larger than the interval errors.
-/

namespace ConvexSquare

/-- Positive determinant means that the middle cofactor is strictly below the
chord joining the two outer cofactors. -/
def cofactorDet (u v w a b c : ℤ) : ℤ :=
  (w - v) * (a - b) - (v - u) * (b - c)

/-- Exact interpolation identity, centered at the middle square multiple.
There are no divisions and only two error terms. -/
lemma cofactorDet_identity (u v w a b c : ℤ) :
    cofactorDet u v w a b c * (u ^ 2 * w ^ 2) =
      b * (v - u) * (w - v) * (w - u) * (u * v + u * w + v * w) +
        (a * u ^ 2 - b * v ^ 2) * (w - v) * w ^ 2 +
        (c * w ^ 2 - b * v ^ 2) * (v - u) * u ^ 2 := by
  unfold cofactorDet
  ring

private lemma cofactor_pos {x u a : ℤ} (hx : 0 ≤ x)
    (ha : x < a * u ^ 2) : 0 < a := by
  by_contra h
  have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (sq_nonneg u)
  linarith

/-- Narrow intervals force strict decrease; no upper bound on the bases is
needed for this part. -/
lemma cofactor_decreasing_int {x H N u v a b : ℤ}
    (hx : 0 ≤ x) (hN : 0 < N) (hH : H ≤ N)
    (hu : N ≤ u) (huv : u < v)
    (ha : x < a * u ^ 2 ∧ a * u ^ 2 ≤ x + H)
    (hb : x < b * v ^ 2 ∧ b * v ^ 2 ≤ x + H) : b < a := by
  have ha1 : 1 ≤ a := by have := cofactor_pos hx ha.1; omega
  have hu0 : 0 < u := hN.trans_le hu
  have huv1 : u + 1 ≤ v := by omega
  have hsqle : (u + 1) ^ 2 ≤ v ^ 2 :=
    pow_le_pow_left₀ (by omega) huv1 2
  have hgap : H < v ^ 2 - u ^ 2 := by nlinarith only [hsqle, hu, hH, hN]
  by_contra hab
  have hab' : a ≤ b := le_of_not_gt hab
  have hp := mul_le_mul_of_nonneg_right hab' (sq_nonneg v)
  have hq := mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ v ^ 2 - u ^ 2)
  nlinarith only [hp, hq, hgap, ha.1, hb.2]

/-- One integral cofactor drop forces a quantitative separation. -/
lemma cofactor_gap_bound_int {x H N u v a b : ℤ}
    (hx : 0 ≤ x) (hN : 0 < N) (hH : 2 * H ≤ N)
    (hu : N ≤ u) (huv : u < v) (hv : v ≤ 2 * N)
    (ha : x < a * u ^ 2 ∧ a * u ^ 2 ≤ x + H)
    (hb : x < b * v ^ 2 ∧ b * v ^ 2 ≤ x + H) :
    N ≤ 8 * b * (v - u) := by
  have hab : b < a := cofactor_decreasing_int hx hN (by linarith) hu huv ha hb
  have hb0 : 0 < b := cofactor_pos hx hb.1
  have hr0 : 0 ≤ v - u := by omega
  have hdrop : 1 ≤ a - b := by omega
  have hNsq : N ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hN.le hu 2
  have hdropSq := mul_le_mul_of_nonneg_right hdrop (sq_nonneg u)
  have hsum : u + v ≤ 4 * N := by linarith
  have hupper := mul_le_mul_of_nonneg_left hsum (mul_nonneg hb0.le hr0)
  have hbase : N ^ 2 ≤ 4 * N * (b * (v - u)) + H := by
    nlinarith only [hNsq, hdropSq, hupper, ha.2, hb.1]
  have hHsq : 2 * H ≤ N ^ 2 := by nlinarith only [hH, hN]
  have hscaled : N * N ≤ (8 * b * (v - u)) * N := by
    nlinarith only [hbase, hHsq]
  exact le_of_mul_le_mul_right hscaled hN

/-- Integer-cofactor convexity on a dyadic band. The cofactors themselves need
not be assumed positive: their positivity follows from the hits and `0 ≤ x`.
The constant is `64`, and there is no horizon hypothesis on `x`. -/
theorem square_multiple_cofactors_strictly_convex_int
    {x H N u v w a b c : ℤ}
    (hx : 0 ≤ x) (hH0 : 0 ≤ H) (hN : 0 < N) (hH : 64 * H ≤ N)
    (hu : N ≤ u) (huv : u < v) (hvw : v < w) (hw : w ≤ 2 * N)
    (ha : x < a * u ^ 2 ∧ a * u ^ 2 ≤ x + H)
    (hb : x < b * v ^ 2 ∧ b * v ^ 2 ≤ x + H)
    (hc : x < c * w ^ 2 ∧ c * w ^ 2 ≤ x + H) :
    b < a ∧ c < b ∧ 0 < cofactorDet u v w a b c := by
  have hHN : H ≤ N := by linarith
  have hab := cofactor_decreasing_int hx hN hHN hu huv ha hb
  have hbc := cofactor_decreasing_int hx hN hHN (hu.trans huv.le) hvw hb hc
  refine ⟨hab, hbc, ?_⟩
  have hHpos : 0 < H := by linarith [ha.1, ha.2]
  have hbpos : 0 < b := cofactor_pos hx hb.1
  have hu0 : 0 < u := hN.trans_le hu
  have hv0 : 0 < v := hu0.trans huv
  have hw0 : 0 < w := hv0.trans hvw
  have hr : 0 < v - u := sub_pos.mpr huv
  have hs : 0 < w - v := sub_pos.mpr hvw
  have hs1 : 1 ≤ w - v := by omega
  have ht : 0 < w - u := by omega
  have hbr : N ≤ 8 * b * (v - u) :=
    cofactor_gap_bound_int hx hN (by linarith) hu huv (by linarith) ha hb
  have hbrs : N ≤ 8 * (b * (v - u) * (w - v)) := by
    have hp := mul_le_mul_of_nonneg_left hs1
      (show 0 ≤ 8 * b * (v - u) by positivity)
    nlinarith only [hbr, hp]
  have hcurv : 4 * H < b * (v - u) * (w - v) := by
    nlinarith only [hH, hbrs, hHpos]
  have hP : N ^ 2 ≤ u * v + u * w + v * w := by
    have huvN : N * N ≤ u * v :=
      mul_le_mul hu (hu.trans huv.le) hN.le hu0.le
    nlinarith only [huvN, mul_nonneg hu0.le hw0.le, mul_nonneg hv0.le hw0.le]
  have hmain : 4 * H * (w - u) * N ^ 2 <
      b * (v - u) * (w - v) * (w - u) * (u * v + u * w + v * w) := by
    calc
      4 * H * (w - u) * N ^ 2 <
          (b * (v - u) * (w - v)) * ((w - u) * N ^ 2) := by
        simpa only [mul_assoc] using
          mul_lt_mul_of_pos_right hcurv (mul_pos ht (pow_pos hN 2))
      _ = (b * (v - u) * (w - v) * (w - u)) * N ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
  have huSq : u ^ 2 ≤ 4 * N ^ 2 := by
    have hp := pow_le_pow_left₀ hu0.le (show u ≤ 2 * N by omega) 2
    nlinarith only [hp]
  have hwSq : w ^ 2 ≤ 4 * N ^ 2 := by
    have hp := pow_le_pow_left₀ hw0.le hw 2
    nlinarith only [hp]
  have hea : -H ≤ a * u ^ 2 - b * v ^ 2 := by linarith [ha.1, hb.2]
  have hec : -H ≤ c * w ^ 2 - b * v ^ 2 := by linarith [hc.1, hb.2]
  have herrorA : -(4 * H * (w - v) * N ^ 2) ≤
      (a * u ^ 2 - b * v ^ 2) * (w - v) * w ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hea (mul_nonneg hs.le (sq_nonneg w))
    have h₂ := mul_le_mul_of_nonneg_left hwSq (mul_nonneg hH0 hs.le)
    nlinarith only [h₁, h₂]
  have herrorC : -(4 * H * (v - u) * N ^ 2) ≤
      (c * w ^ 2 - b * v ^ 2) * (v - u) * u ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hec (mul_nonneg hr.le (sq_nonneg u))
    have h₂ := mul_le_mul_of_nonneg_left huSq (mul_nonneg hH0 hr.le)
    nlinarith only [h₁, h₂]
  have hscaled : 0 < cofactorDet u v w a b c * (u ^ 2 * w ^ 2) := by
    rw [cofactorDet_identity]
    nlinarith only [hmain, herrorA, herrorC]
  exact pos_of_mul_pos_left hscaled (mul_nonneg (sq_nonneg u) (sq_nonneg w))

/-- Natural-number version, with genuine (nontruncated) drops guaranteed by
`b < a` and `c < b`. In particular, three such points cannot be collinear. -/
theorem square_multiple_cofactors_strictly_convex
    {x H N u v w a b c : ℕ}
    (hN : 0 < N) (hH : 64 * H ≤ N)
    (hu : N ≤ u) (huv : u < v) (hvw : v < w) (hw : w ≤ 2 * N)
    (ha : x < a * u ^ 2 ∧ a * u ^ 2 ≤ x + H)
    (hb : x < b * v ^ 2 ∧ b * v ^ 2 ≤ x + H)
    (hc : x < c * w ^ 2 ∧ c * w ^ 2 ≤ x + H) :
    b < a ∧ c < b ∧ (v - u) * (b - c) < (w - v) * (a - b) := by
  have hi := square_multiple_cofactors_strictly_convex_int
    (x := (x : ℤ)) (H := (H : ℤ)) (N := (N : ℤ))
    (u := (u : ℤ)) (v := (v : ℤ)) (w := (w : ℤ))
    (a := (a : ℤ)) (b := (b : ℤ)) (c := (c : ℤ))
    (Nat.cast_nonneg x) (Nat.cast_nonneg H) (by exact_mod_cast hN)
    (by exact_mod_cast hH) (by exact_mod_cast hu) (by exact_mod_cast huv)
    (by exact_mod_cast hvw) (by exact_mod_cast hw)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
  have hab : b < a := by exact_mod_cast hi.1
  have hbc : c < b := by exact_mod_cast hi.2.1
  refine ⟨hab, hbc, ?_⟩
  have hdet := hi.2.2
  unfold cofactorDet at hdet
  have hineq : ((v : ℤ) - u) * ((b : ℤ) - c) <
      ((w : ℤ) - v) * ((a : ℤ) - b) := by linarith only [hdet]
  have hcast : (((v - u) * (b - c) : ℕ) : ℤ) <
      (((w - v) * (a - b) : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_sub huv.le, Nat.cast_sub hbc.le,
      Nat.cast_sub hvw.le, Nat.cast_sub hab.le] using hineq
  exact_mod_cast hcast

end ConvexSquare
