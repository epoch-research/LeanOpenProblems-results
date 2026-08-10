import FormalConjectures.Util.ProblemImports

open Nat Finset Set

-- Integer version of the reduced inhomogeneous ternary form.
def AZ (L u v r : ℤ) : ℤ :=
  u^2 + 3*v^2 + 6*r^2 + 2*u*v + 3*u*r + 6*v*r + L*(u + 2*v + 3*r)

-- Twice the integer generalized pentagonal polynomial, avoiding division.
def PZ2 (k : ℤ) : ℤ := k * (3*k + 1)

def FZ2 (x y z w : ℤ) : ℤ := PZ2 x + PZ2 y + 2 * PZ2 z + 3 * PZ2 w


lemma doubled_interval_offset_identity (t L u v r : ℤ) :
    FZ2 (t + (L + u + 2*v + 3*r)) (t - u) (t - v) (t - r) - 7 * PZ2 t =
      6 * t * L + L * (3*L + 1) + 6 * AZ L u v r := by
  unfold FZ2 PZ2 AZ
  ring

lemma doubled_interval_offset_identity_of_eq {t L u v r N D : ℤ}
    (hN : AZ L u v r = N)
    (hD : 2 * D = 6 * t * L + L * (3*L + 1) + 6 * N) :
    FZ2 (t + (L + u + 2*v + 3*r)) (t - u) (t - v) (t - r) - 7 * PZ2 t = 2 * D := by
  rw [doubled_interval_offset_identity, hN]
  exact hD.symm

lemma doubled_interval_offset_case_neg1 {t u v r N D : ℤ}
    (hN : AZ (-1) u v r = N) (hD : 3 * N = D + 3 * t - 1) :
    FZ2 (t + ((-1) + u + 2*v + 3*r)) (t - u) (t - v) (t - r) - 7 * PZ2 t = 2 * D := by
  apply doubled_interval_offset_identity_of_eq hN
  nlinarith

lemma doubled_interval_offset_case_neg2 {t u v r N D : ℤ}
    (hN : AZ (-2) u v r = N) (hD : 3 * N = D + 6 * t - 5) :
    FZ2 (t + ((-2) + u + 2*v + 3*r)) (t - u) (t - v) (t - r) - 7 * PZ2 t = 2 * D := by
  apply doubled_interval_offset_identity_of_eq hN
  nlinarith

lemma doubled_interval_offset_case_neg3 {t u v r N D : ℤ}
    (hN : AZ (-3) u v r = N) (hD : 3 * N = D + 9 * t - 12) :
    FZ2 (t + ((-3) + u + 2*v + 3*r)) (t - u) (t - v) (t - r) - 7 * PZ2 t = 2 * D := by
  apply doubled_interval_offset_identity_of_eq hN
  nlinarith


lemma interval_bound_case_neg1 {D t N : ℤ}
    (hD0 : 0 ≤ D) (hDlt : D < 21 * t + 14)
    (hN : 3 * N = D + 3 * t - 1) (ht : 17 ≤ t) :
    2 * N + (-1 : ℤ)^2 < t^2 := by
  have hNle : 3 * N < 24 * t + 13 := by nlinarith
  have hmain : 2 * N + 1 < 16 * t + 10 := by nlinarith
  have hquad : 16 * t + 10 ≤ t^2 := by nlinarith
  nlinarith

lemma interval_bound_case_neg2 {D t N : ℤ}
    (hD0 : 0 ≤ D) (hDlt : D < 21 * t + 14)
    (hN : 3 * N = D + 6 * t - 5) (ht : 19 ≤ t) :
    2 * N + (-2 : ℤ)^2 < t^2 := by
  have hNle : 3 * N < 27 * t + 9 := by nlinarith
  have hmain : 2 * N + 4 < 18 * t + 10 := by nlinarith
  have hquad : 18 * t + 10 ≤ t^2 := by nlinarith
  nlinarith

lemma interval_bound_case_neg3 {D t N : ℤ}
    (hD0 : 0 ≤ D) (hDlt : D < 21 * t + 14)
    (hN : 3 * N = D + 9 * t - 12) (ht : 21 ≤ t) :
    2 * N + (-3 : ℤ)^2 < t^2 := by
  have hNle : 3 * N < 30 * t + 2 := by nlinarith
  have hmain : 2 * N + 9 < 20 * t + 11 := by nlinarith
  have hquad : 20 * t + 11 ≤ t^2 := by nlinarith
  nlinarith


lemma interval_N_nonneg_case_neg1 {D t N : ℤ}
    (hD0 : 0 ≤ D) (hN : 3 * N = D + 3 * t - 1) (ht : 1 ≤ t) : 0 ≤ N := by
  nlinarith

lemma interval_N_nonneg_case_neg2 {D t N : ℤ}
    (hD0 : 0 ≤ D) (hN : 3 * N = D + 6 * t - 5) (ht : 1 ≤ t) : 0 ≤ N := by
  nlinarith

lemma interval_N_nonneg_case_neg3 {D t N : ℤ}
    (hD0 : 0 ≤ D) (hN : 3 * N = D + 9 * t - 12) (ht : 2 ≤ t) : 0 ≤ N := by
  nlinarith



lemma AZ_quaternary_identity (L u v r : ℤ) :
    2 * AZ L u v r + L^2 =
      (u + 2*v + 3*r + L)^2 + u^2 + 2*v^2 + 3*r^2 := by
  unfold AZ
  ring


lemma sq_le_of_AZ_eq {L u v r N : ℤ} (hN : AZ L u v r = N) :
    (u + 2*v + 3*r + L)^2 ≤ 2 * N + L^2 ∧
    u^2 ≤ 2 * N + L^2 ∧
    2 * v^2 ≤ 2 * N + L^2 ∧
    3 * r^2 ≤ 2 * N + L^2 := by
  have h := AZ_quaternary_identity L u v r
  rw [hN] at h
  constructor
  · nlinarith [sq_nonneg u, sq_nonneg v, sq_nonneg r]
  constructor
  · nlinarith [sq_nonneg (u + 2*v + 3*r + L), sq_nonneg v, sq_nonneg r]
  constructor
  · nlinarith [sq_nonneg (u + 2*v + 3*r + L), sq_nonneg u, sq_nonneg r]
  · nlinarith [sq_nonneg (u + 2*v + 3*r + L), sq_nonneg u, sq_nonneg v]


lemma abs_lt_of_sq_le_of_lt_sq {a B t : ℤ}
    (ht : 0 < t) (hle : a^2 ≤ B) (hB : B < t^2) : -t < a ∧ a < t := by
  constructor
  · by_contra h
    have ha : a ≤ -t := by omega
    have h1 : a + t ≤ 0 := by omega
    have h2 : a - t ≤ 0 := by omega
    have hprod : 0 ≤ (a + t) * (a - t) := mul_nonneg_of_nonpos_of_nonpos h1 h2
    have hs : t^2 ≤ a^2 := by nlinarith
    omega
  · by_contra h
    have ha : t ≤ a := by omega
    have hs : t^2 ≤ a^2 := by nlinarith
    omega

lemma offset_bounds_of_AZ_eq {L u v r N t : ℤ}
    (hN : AZ L u v r = N) (ht : 0 < t) (hB : 2 * N + L^2 < t^2) :

/-- A stronger, parametrized version of `Dickson3714` that already includes the
congruence/sign normalization needed to recover an `AZ` witness.  This is only a
proposition, not an axiom. -/
def Dickson3714Param : Prop :=
  ∀ L : ℤ, L = -1 ∨ L = -2 ∨ L = -3 → ∀ N : ℤ, 0 ≤ N →
    ∃ x y z : ℤ,
      56 * N + 24 * L^2 =
        14 * (2*x + z + L)^2 + 7 * (4*y - z + L)^2 + 3 * (7*z + L)^2

lemma AZ_universal_of_Dickson3714Param
    (H : Dickson3714Param) (L : ℤ) (hL : L = -1 ∨ L = -2 ∨ L = -3) :
    ∀ N : ℤ, 0 ≤ N → ∃ u v r : ℤ, AZ L u v r = N := by
  exact AZ_universal_of_diagonal_param L (H L hL)

    (-t < u + 2*v + 3*r + L ∧ u + 2*v + 3*r + L < t) ∧
    (-t < u ∧ u < t) ∧
    (-t < v ∧ v < t) ∧
    (-t < r ∧ r < t) := by
  have hsq := sq_le_of_AZ_eq hN
  constructor
  · exact abs_lt_of_sq_le_of_lt_sq ht hsq.1 hB
  constructor
  · exact abs_lt_of_sq_le_of_lt_sq ht hsq.2.1 hB
  constructor
  · have hv : v^2 ≤ 2 * N + L^2 := by nlinarith [hsq.2.2.1, sq_nonneg v]
    exact abs_lt_of_sq_le_of_lt_sq ht hv hB
  · have hr : r^2 ≤ 2 * N + L^2 := by nlinarith [hsq.2.2.2, sq_nonneg r]
    exact abs_lt_of_sq_le_of_lt_sq ht hr hB


lemma diagonal_identity (L x y z : ℤ) :
    56 * AZ L (x - y) (y - z) z + 24 * L^2 =
      14 * (2*x + z + L)^2 + 7 * (4*y - z + L)^2 + 3 * (7*z + L)^2 := by
  unfold AZ
  ring

-- The older diagonalization of the homogeneous part.
lemma homogeneous_identity (u v r : ℤ) :
    8 * AZ 0 u v r =
      2 * (2*u + 2*v + 3*r)^2 + (4*v + 3*r)^2 + 21 * r^2 := by
  unfold AZ
  ring

-- Triangular-number reformulation of the odd diagonal case.
def TZ (k : ℤ) : ℤ := k * (k + 1) / 2

lemma odd_square_eq_eight_triangular_add_one (k : ℤ) :
    (2 * k + 1)^2 = 8 * TZ k + 1 := by
  unfold TZ
  have h_even : (2 : ℤ) ∣ k * (k + 1) := by
    rcases Int.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · use t * (k + 1)
      rw [ht]
      ring
    · use k * (t + 1)
      rw [ht]
      ring
  have hdiv : k * (k + 1) / 2 * 2 = k * (k + 1) := Int.ediv_mul_cancel h_even
  nlinarith

lemma diagonal_odd_to_triangular (x y z m : ℤ)
    (h : 8 * m = 14 * (2*x+1)^2 + 7 * (2*y+1)^2 + 3 * (2*z+1)^2) :
    m = 14 * TZ x + 7 * TZ y + 3 * TZ z + 3 := by
  have hx := odd_square_eq_eight_triangular_add_one x
  have hy := odd_square_eq_eight_triangular_add_one y
  have hz := odd_square_eq_eight_triangular_add_one z
  nlinarith




lemma AZ_of_diagonal_with_parameters (L N x y z : ℤ)
    (hdiag : 56 * N + 24 * L^2 =
      14 * (2*x + z + L)^2 + 7 * (4*y - z + L)^2 + 3 * (7*z + L)^2) :
    AZ L (x - y) (y - z) z = N := by
  have h := diagonal_identity L x y z
  nlinarith

-- A conditional version of the desired universality statement for the reduced forms.
lemma AZ_universal_of_diagonal_param (L : ℤ)
    (h : ∀ N : ℤ, 0 ≤ N → ∃ x y z : ℤ,
      56 * N + 24 * L^2 =
        14 * (2*x + z + L)^2 + 7 * (4*y - z + L)^2 + 3 * (7*z + L)^2) :
    ∀ N : ℤ, 0 ≤ N → ∃ u v r : ℤ, AZ L u v r = N := by
  intro N hN
  rcases h N hN with ⟨x, y, z, hdiag⟩
  exact ⟨x - y, y - z, z, AZ_of_diagonal_with_parameters L N x y z hdiag⟩

/-- The exact classical regularity statement for the ternary form `<3,7,14>`
which would close the main infinite obstruction if proved.  This theorem is stated
as a proposition only; no axiom or proof is introduced. -/
def Dickson3714 : Prop :=
  ∀ m : ℕ, m % 7 = 3 ∨ m % 7 = 5 ∨ m % 7 = 6 →
    ∃ X Y Z : ℤ, 8 * (m : ℤ) = 14 * X^2 + 7 * Y^2 + 3 * Z^2

lemma diagonal_needed_from_Dickson3714
    (H : Dickson3714) (N : ℕ) :
    (∃ X Y Z : ℤ, 56 * (N : ℤ) + 24 * (-1 : ℤ)^2 =
      14 * X^2 + 7 * Y^2 + 3 * Z^2) ∧
    (∃ X Y Z : ℤ, 56 * (N : ℤ) + 24 * (-2 : ℤ)^2 =
      14 * X^2 + 7 * Y^2 + 3 * Z^2) ∧
    (∃ X Y Z : ℤ, 56 * (N : ℤ) + 24 * (-3 : ℤ)^2 =
      14 * X^2 + 7 * Y^2 + 3 * Z^2) := by
  unfold Dickson3714 at H
  constructor
  · rcases H (7 * N + 3) (by omega) with ⟨X, Y, Z, h⟩
    refine ⟨X, Y, Z, ?_⟩
    norm_num at h ⊢
    omega
  constructor
  · rcases H (7 * N + 12) (by omega) with ⟨X, Y, Z, h⟩
    refine ⟨X, Y, Z, ?_⟩
    norm_num at h ⊢
    omega
  · rcases H (7 * N + 27) (by omega) with ⟨X, Y, Z, h⟩
    refine ⟨X, Y, Z, ?_⟩
    norm_num at h ⊢
    omega
