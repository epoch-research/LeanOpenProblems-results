import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/-!
  Analysis of squarefree n with ω(n) ≥ 5.
  For five odd primes, P(n)+1 = 32n - 2 * fiveDelta, so odd n ∣ P(n)+1
  iff n ∣ fiveDelta.
-/

def fiveDelta (p q r s t : ℕ) : ℤ :=
  8 * (p * q * r * s + p * q * r * t + p * q * s * t + p * r * s * t
      + q * r * s * t : ℤ)
    - 4 * (p * q * r + p * q * s + p * q * t + p * r * s + p * r * t
      + p * s * t + q * r * s + q * r * t + q * s * t + r * s * t)
    + 2 * (p * q + p * r + p * s + p * t + q * r + q * s + q * t
      + r * s + r * t + s * t)
    - (p + q + r + s + t)

lemma cast_two_mul_sub_five (p : ℕ) (hp : 1 ≤ p) :
    ((2 * p - 1 : ℕ) : ℤ) = 2 * (p : ℤ) - 1 := by
  have : 1 ≤ 2 * p := by omega
  rw [Nat.cast_sub this]
  push_cast
  rfl

lemma expand_five_int (p q r s t : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ((((2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * (2 * t - 1)
        + 1 : ℕ) : ℤ)) =
      32 * (p : ℤ) * q * r * s * t
        - 16 * (p * q * r * s + p * q * r * t + p * q * s * t + p * r * s * t
          + q * r * s * t)
        + 8 * (p * q * r + p * q * s + p * q * t + p * r * s + p * r * t
          + p * s * t + q * r * s + q * r * t + q * s * t + r * s * t)
        - 4 * (p * q + p * r + p * s + p * t + q * r + q * s + q * t
          + r * s + r * t + s * t)
        + 2 * (p + q + r + s + t) := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_one]
  rw [cast_two_mul_sub_five p hp, cast_two_mul_sub_five q hq,
    cast_two_mul_sub_five r hr, cast_two_mul_sub_five s hs,
    cast_two_mul_sub_five t ht]
  ring

lemma five_prod_add_one_eq (p q r s t : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ((((2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * (2 * t - 1)
        + 1 : ℕ) : ℤ)) =
      32 * (p : ℤ) * q * r * s * t - 2 * fiveDelta p q r s t := by
  rw [expand_five_int p q r s t hp hq hr hs ht]
  unfold fiveDelta
  ring

lemma five_delta_int_of_dvd {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hrodd : Odd r) (hsodd : Odd s) (htodd : Odd t)
    (hdvd : p * q * r * s * t ∣
      (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * (2 * t - 1) + 1) :
    (p * q * r * s * t : ℤ) ∣ fiveDelta p q r s t := by
  have hex := five_prod_add_one_eq p q r s t hp.pos hq.pos hr.pos hs.pos ht.pos
  have hI : (p * q * r * s * t : ℤ) ∣
      ((((2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) * (2 * t - 1)
          + 1 : ℕ) : ℤ)) :=
    Int.natCast_dvd_natCast.mpr hdvd
  rw [hex] at hI
  have h32 : (p * q * r * s * t : ℤ) ∣ 32 * p * q * r * s * t := ⟨32, by ring⟩
  have hsub := Int.dvd_sub h32 hI
  have h2 : (p * q * r * s * t : ℤ) ∣ 2 * fiveDelta p q r s t := by
    convert hsub using 1
    ring
  have hodd : Odd (p * q * r * s * t) :=
    ((((hpodd.mul hqodd).mul hrodd).mul hsodd).mul htodd)
  have hc : IsCoprime (p * q * r * s * t : ℤ) (2 : ℕ) :=
    hodd.coprime_two_right.isCoprime
  exact hc.dvd_of_dvd_mul_left h2

/-- `fiveDelta` as a linear polynomial in `t`. -/
def fiveA (p q r s : ℕ) : ℤ :=
  8 * (p * q * r + p * q * s + p * r * s + q * r * s : ℤ)
    - 4 * (p * q + p * r + p * s + q * r + q * s + r * s)
    + 2 * (p + q + r + s) - 1

def fiveB (p q r s : ℕ) : ℤ :=
  8 * (p * q * r * s : ℤ)
    - 4 * (p * q * r + p * q * s + p * r * s + q * r * s)
    + 2 * (p * q + p * r + p * s + q * r + q * s + r * s)
    - (p + q + r + s)

lemma fiveDelta_decomp (p q r s t : ℕ) :
    fiveDelta p q r s t = (t : ℤ) * fiveA p q r s + fiveB p q r s := by
  unfold fiveDelta fiveA fiveB; ring

lemma fiveB_eq_four_related (p q r s : ℕ) :
    fiveB p q r s =
      8 * (p * q * r * s : ℤ)
        - 4 * (p * q * r + p * q * s + p * r * s + q * r * s)
        + 2 * (p * q + p * r + p * s + q * r + q * s + r * s)
        - (p + q + r + s) := by
  unfold fiveB; rfl

lemma n_sub_fiveDelta (p q r s t : ℕ) :
    (p * q * r * s * t : ℤ) - fiveDelta p q r s t =
      (t : ℤ) * ((p : ℤ) * q * r * s - fiveA p q r s) - fiveB p q r s := by
  unfold fiveDelta fiveA fiveB; ring

lemma fiveA_pos {p q r s : ℕ}
    (hp : 5 ≤ p) (hq : 5 ≤ q) (hr : 5 ≤ r) (hs : 5 ≤ s) :
    (0 : ℤ) < fiveA p q r s := by
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (5 : ℤ) ≤ s := by exact_mod_cast hs
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hs0 : (0 : ℤ) ≤ s := by omega
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hps : (0 : ℤ) ≤ p * s := mul_nonneg hp0 hs0
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  have hqs : (0 : ℤ) ≤ q * s := mul_nonneg hq0 hs0
  have hrs : (0 : ℤ) ≤ r * s := mul_nonneg hr0 hs0
  -- each pair * 5 ≤ a corresponding triple
  have h1 : (5 : ℤ) * (p * q) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hr' hpq
    convert this using 1 <;> ring
  have h2 : (5 : ℤ) * (p * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hq' hpr
    convert this using 1 <;> ring
  have h3 : (5 : ℤ) * (q * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hp' hqr
    convert this using 1 <;> ring
  have h4 : (5 : ℤ) * (p * s) ≤ p * q * s := by
    have := mul_le_mul_of_nonneg_left hq' hps
    convert this using 1 <;> ring
  have h5 : (5 : ℤ) * (q * s) ≤ p * q * s := by
    have := mul_le_mul_of_nonneg_left hp' hqs
    convert this using 1 <;> ring
  have h6 : (5 : ℤ) * (r * s) ≤ p * r * s := by
    have := mul_le_mul_of_nonneg_left hp' hrs
    convert this using 1 <;> ring
  unfold fiveA
  nlinarith

lemma fiveB_pos {p q r s : ℕ}
    (hp : 5 ≤ p) (hq : 5 ≤ q) (hr : 5 ≤ r) (hs : 5 ≤ s) :
    (0 : ℤ) < fiveB p q r s := by
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (5 : ℤ) ≤ s := by exact_mod_cast hs
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hs0 : (0 : ℤ) ≤ s := by omega
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hps : (0 : ℤ) ≤ p * s := mul_nonneg hp0 hs0
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  have hqs : (0 : ℤ) ≤ q * s := mul_nonneg hq0 hs0
  have hrs : (0 : ℤ) ≤ r * s := mul_nonneg hr0 hs0
  have hpqr : (0 : ℤ) ≤ p * q * r := mul_nonneg hpq hr0
  have hpqs : (0 : ℤ) ≤ p * q * s := mul_nonneg hpq hs0
  have hprs : (0 : ℤ) ≤ p * r * s := mul_nonneg hpr hs0
  have hqrs : (0 : ℤ) ≤ q * r * s := mul_nonneg hqr hs0
  -- 8pqrs vs 4(pqr+pqs+prs+qrs): use each ≥ 5
  have h1 : (5 : ℤ) * (p * q * r) ≤ p * q * r * s := by
    have := mul_le_mul_of_nonneg_left hs' hpqr
    convert this using 1 <;> ring
  have h2 : (5 : ℤ) * (p * q * s) ≤ p * q * r * s := by
    have := mul_le_mul_of_nonneg_left hr' hpqs
    convert this using 1 <;> ring
  have h3 : (5 : ℤ) * (p * r * s) ≤ p * q * r * s := by
    have := mul_le_mul_of_nonneg_left hq' hprs
    convert this using 1 <;> ring
  have h4 : (5 : ℤ) * (q * r * s) ≤ p * q * r * s := by
    have := mul_le_mul_of_nonneg_left hp' hqrs
    convert this using 1 <;> ring
  unfold fiveB
  nlinarith

lemma fiveDelta_pos {p q r s t : ℕ}
    (hp : 5 ≤ p) (hq : 5 ≤ q) (hr : 5 ≤ r) (hs : 5 ≤ s) (ht : 5 ≤ t) :
    0 < fiveDelta p q r s t := by
  have ht' : (5 : ℤ) ≤ t := by exact_mod_cast ht
  have hA := fiveA_pos hp hq hr hs
  have hB := fiveB_pos hp hq hr hs
  rw [fiveDelta_decomp]
  nlinarith

/-- `41 * e₄ ≤ 5 n` when every prime is ≥ 41. -/
lemma fortyone_e4_le_five_n {p q r s t : ℕ}
    (hp : 41 ≤ p) (hq : 41 ≤ q) (hr : 41 ≤ r) (hs : 41 ≤ s) (ht : 41 ≤ t) :
    (41 : ℤ) * (p * q * r * s + p * q * r * t + p * q * s * t + p * r * s * t
      + q * r * s * t) ≤ 5 * (p * q * r * s * t : ℤ) := by
  have hp' : (41 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (41 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (41 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (41 : ℤ) ≤ s := by exact_mod_cast hs
  have ht' : (41 : ℤ) ≤ t := by exact_mod_cast ht
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hs0 : (0 : ℤ) ≤ s := by omega
  have ht0 : (0 : ℤ) ≤ t := by omega
  have hpqrs : (0 : ℤ) ≤ p * q * r * s :=
    mul_nonneg (mul_nonneg (mul_nonneg hp0 hq0) hr0) hs0
  have hpqrt : (0 : ℤ) ≤ p * q * r * t :=
    mul_nonneg (mul_nonneg (mul_nonneg hp0 hq0) hr0) ht0
  have hpqst : (0 : ℤ) ≤ p * q * s * t :=
    mul_nonneg (mul_nonneg (mul_nonneg hp0 hq0) hs0) ht0
  have hprst : (0 : ℤ) ≤ p * r * s * t :=
    mul_nonneg (mul_nonneg (mul_nonneg hp0 hr0) hs0) ht0
  have hqrst : (0 : ℤ) ≤ q * r * s * t :=
    mul_nonneg (mul_nonneg (mul_nonneg hq0 hr0) hs0) ht0
  have h1 : (41 : ℤ) * (p * q * r * s) ≤ p * q * r * s * t := by
    have := mul_le_mul_of_nonneg_left ht' hpqrs
    convert this using 1 <;> ring
  have h2 : (41 : ℤ) * (p * q * r * t) ≤ p * q * r * s * t := by
    have := mul_le_mul_of_nonneg_left hs' hpqrt
    convert this using 1 <;> ring
  have h3 : (41 : ℤ) * (p * q * s * t) ≤ p * q * r * s * t := by
    have := mul_le_mul_of_nonneg_left hr' hpqst
    convert this using 1 <;> ring
  have h4 : (41 : ℤ) * (p * r * s * t) ≤ p * q * r * s * t := by
    have := mul_le_mul_of_nonneg_left hq' hprst
    convert this using 1 <;> ring
  have h5 : (41 : ℤ) * (q * r * s * t) ≤ p * q * r * s * t := by
    have := mul_le_mul_of_nonneg_left hp' hqrst
    convert this using 1 <;> ring
  nlinarith

lemma eight_e4_lt_n {p q r s t : ℕ}
    (hp : 41 ≤ p) (hq : 41 ≤ q) (hr : 41 ≤ r) (hs : 41 ≤ s) (ht : 41 ≤ t) :
    8 * (p * q * r * s + p * q * r * t + p * q * s * t + p * r * s * t
      + q * r * s * t : ℤ) < p * q * r * s * t := by
  have h := fortyone_e4_le_five_n hp hq hr hs ht
  have hp' : (41 : ℤ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℤ) < p * q * r * s * t := by
    have hq' : (41 : ℤ) ≤ q := by exact_mod_cast hq
    have hr' : (41 : ℤ) ≤ r := by exact_mod_cast hr
    have hs' : (41 : ℤ) ≤ s := by exact_mod_cast hs
    have ht' : (41 : ℤ) ≤ t := by exact_mod_cast ht
    have hp0 : (0 : ℤ) < p := lt_of_lt_of_le (by norm_num) hp'
    have hq0 : (0 : ℤ) < q := lt_of_lt_of_le (by norm_num) hq'
    have hr0 : (0 : ℤ) < r := lt_of_lt_of_le (by norm_num) hr'
    have hs0 : (0 : ℤ) < s := lt_of_lt_of_le (by norm_num) hs'
    have ht0 : (0 : ℤ) < t := lt_of_lt_of_le (by norm_num) ht'
    exact mul_pos (mul_pos (mul_pos (mul_pos hp0 hq0) hr0) hs0) ht0
  -- 41 * 8 e4 ≤ 40 n  ⇒  328 e4 ≤ 40 n < 41 n
  have h8 : 8 * (41 : ℤ) *
      (p * q * r * s + p * q * r * t + p * q * s * t + p * r * s * t
        + q * r * s * t) ≤ 40 * (p * q * r * s * t : ℤ) := by
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℤ) ≤ 8)
    convert this using 1 <;> ring
  have h40 : (40 : ℤ) * (p * q * r * s * t) < 41 * (p * q * r * s * t) := by
    nlinarith [hpos]
  nlinarith

lemma fiveDelta_lt_eight_e4 {p q r s t : ℕ}
    (hp : 5 ≤ p) (hq : 5 ≤ q) (hr : 5 ≤ r) (hs : 5 ≤ s) (ht : 5 ≤ t) :
    fiveDelta p q r s t <
      8 * (p * q * r * s + p * q * r * t + p * q * s * t + p * r * s * t
        + q * r * s * t : ℤ) := by
  -- equivalent to 0 < 4 e₃ - 2 e₂ + e₁
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (5 : ℤ) ≤ s := by exact_mod_cast hs
  have ht' : (5 : ℤ) ≤ t := by exact_mod_cast ht
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hs0 : (0 : ℤ) ≤ s := by omega
  have ht0 : (0 : ℤ) ≤ t := by omega
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hps : (0 : ℤ) ≤ p * s := mul_nonneg hp0 hs0
  have hpt : (0 : ℤ) ≤ p * t := mul_nonneg hp0 ht0
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  have hqs : (0 : ℤ) ≤ q * s := mul_nonneg hq0 hs0
  have hqt : (0 : ℤ) ≤ q * t := mul_nonneg hq0 ht0
  have hrs : (0 : ℤ) ≤ r * s := mul_nonneg hr0 hs0
  have hrt : (0 : ℤ) ≤ r * t := mul_nonneg hr0 ht0
  have hst : (0 : ℤ) ≤ s * t := mul_nonneg hs0 ht0
  -- 5 * pair ≤ some triple, so 2 e2 < 4 e3
  have a1 : (5 : ℤ) * (p * q) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hr' hpq; convert this using 1 <;> ring
  have a2 : (5 : ℤ) * (p * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hq' hpr; convert this using 1 <;> ring
  have a3 : (5 : ℤ) * (q * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hp' hqr; convert this using 1 <;> ring
  have a4 : (5 : ℤ) * (p * s) ≤ p * q * s := by
    have := mul_le_mul_of_nonneg_left hq' hps; convert this using 1 <;> ring
  have a5 : (5 : ℤ) * (q * s) ≤ p * q * s := by
    have := mul_le_mul_of_nonneg_left hp' hqs; convert this using 1 <;> ring
  have a6 : (5 : ℤ) * (r * s) ≤ p * r * s := by
    have := mul_le_mul_of_nonneg_left hp' hrs; convert this using 1 <;> ring
  have a7 : (5 : ℤ) * (p * t) ≤ p * q * t := by
    have := mul_le_mul_of_nonneg_left hq' hpt; convert this using 1 <;> ring
  have a8 : (5 : ℤ) * (q * t) ≤ p * q * t := by
    have := mul_le_mul_of_nonneg_left hp' hqt; convert this using 1 <;> ring
  have a9 : (5 : ℤ) * (r * t) ≤ p * r * t := by
    have := mul_le_mul_of_nonneg_left hp' hrt; convert this using 1 <;> ring
  have a10 : (5 : ℤ) * (s * t) ≤ p * s * t := by
    have := mul_le_mul_of_nonneg_left hp' hst; convert this using 1 <;> ring
  unfold fiveDelta
  nlinarith [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]

lemma fiveDelta_lt_n_of_large {p q r s t : ℕ}
    (hp : 41 ≤ p) (hq : 41 ≤ q) (hr : 41 ≤ r) (hs : 41 ≤ s) (ht : 41 ≤ t) :
    fiveDelta p q r s t < (p * q * r * s * t : ℤ) := by
  have h1 := fiveDelta_lt_eight_e4 (le_trans (by norm_num : 5 ≤ 41) hp)
    (le_trans (by norm_num : 5 ≤ 41) hq) (le_trans (by norm_num : 5 ≤ 41) hr)
    (le_trans (by norm_num : 5 ≤ 41) hs) (le_trans (by norm_num : 5 ≤ 41) ht)
  have h2 := eight_e4_lt_n hp hq hr hs ht
  linarith
