import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

lemma cancel_two_of_odd {n : ℕ} {a : ℤ} (hodd : Odd n)
    (h : (n : ℤ) ∣ 2 * a) : (n : ℤ) ∣ a := by
  have hc : IsCoprime (n : ℤ) (2 : ℕ) := hodd.coprime_two_right.isCoprime
  exact hc.dvd_of_dvd_mul_left h

lemma cast_two_mul_sub (q : ℕ) (hq : 1 ≤ q) :
    ((2 * q - 1 : ℕ) : ℤ) = 2 * (q : ℤ) - 1 := by
  have h2q : 1 ≤ 2 * q := by omega
  rw [Nat.cast_sub h2q]
  push_cast
  rfl

lemma expand_four_int (p q r s : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ((((2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 : ℕ) : ℤ)) =
      16 * (p : ℤ) * q * r * s
        - 8 * (p * q * r + p * q * s + p * r * s + q * r * s)
        + 4 * (p * q + p * r + p * s + q * r + q * s + r * s)
        - 2 * (p + q + r + s) + 2 := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_one]
  rw [cast_two_mul_sub p hp, cast_two_mul_sub q hq, cast_two_mul_sub r hr,
    cast_two_mul_sub s hs]
  ring

def fourDelta (p q r s : ℕ) : ℤ :=
  4 * (p * q * r + p * q * s + p * r * s + q * r * s : ℤ)
    - 2 * (p * q + p * r + p * s + q * r + q * s + r * s)
    + (p + q + r + s) - 1

lemma four_delta_int_of_dvd {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hrodd : Odd r) (hsodd : Odd s)
    (hdvd : p * q * r * s ∣
      (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1) :
    (p * q * r * s : ℤ) ∣ fourDelta p q r s := by
  have hex := expand_four_int p q r s hp.pos hq.pos hr.pos hs.pos
  have hI : (p * q * r * s : ℤ) ∣
      ((((2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 : ℕ) : ℤ)) :=
    Int.natCast_dvd_natCast.mpr hdvd
  rw [hex] at hI
  have h16 : (p * q * r * s : ℤ) ∣ 16 * p * q * r * s := ⟨16, by ring⟩
  have hsub := Int.dvd_sub h16 hI
  have h2 : (p * q * r * s : ℤ) ∣ 2 * fourDelta p q r s := by
    unfold fourDelta
    convert hsub using 1
    ring
  have hodd : Odd (p * q * r * s) :=
    ((hpodd.mul hqodd).mul hrodd).mul hsodd
  exact cancel_two_of_odd hodd h2

lemma fourDelta_decomp (p q r s : ℕ) :
    fourDelta p q r s =
      (s : ℤ) * (4 * (p * q + p * r + q * r) - 2 * (p + q + r) + 1)
        + (4 * (p * q * r : ℤ) - 2 * (p * q + p * r + q * r) + (p + q + r) - 1) := by
  unfold fourDelta; ring

lemma fourDelta_const_pos {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    (0 : ℤ) < 4 * (p * q * r : ℤ) - 2 * (p * q + p * r + q * r) + (p + q + r) - 1 := by
  have hp' : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (3 : ℤ) ≤ r := by exact_mod_cast hr
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg (by omega) (by omega)
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg (by omega) (by omega)
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg (by omega) (by omega)
  have h1 : (3 : ℤ) * (p * q) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hr' hpq
    convert this using 1 <;> ring
  have h2 : (3 : ℤ) * (p * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hq' hpr
    convert this using 1 <;> ring
  have h3 : (3 : ℤ) * (q * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hp' hqr
    convert this using 1 <;> ring
  nlinarith

lemma fourDelta_coeff_pos {p q r : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) :
    (0 : ℤ) < 4 * (p * q + p * r + q * r : ℤ) - 2 * (p + q + r) + 1 := by
  have hp' : (3 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (3 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith

lemma fourDelta_pos {p q r s : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r) (hs : 3 ≤ s) :
    0 < fourDelta p q r s := by
  have hs' : (3 : ℤ) ≤ s := by exact_mod_cast hs
  have hc := fourDelta_coeff_pos hp hq hr
  have hk := fourDelta_const_pos hp hq hr
  rw [fourDelta_decomp]
  nlinarith

lemma not_int_dvd_of_pos_lt {n : ℕ} {d : ℤ} (hn : 0 < n)
    (hpos : 0 < d) (hlt : d < (n : ℤ)) : ¬ (n : ℤ) ∣ d := by
  intro ⟨k, hk⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hkn : 0 < (n : ℤ) * k := by
    rwa [← hk]
  have hkpos : 0 < k := by
    by_contra hk0
    have : k ≤ 0 := le_of_not_gt hk0
    have : (n : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn'.le this
    linarith
  have hk1 : (1 : ℤ) ≤ k := by omega
  have : (n : ℤ) ≤ d := by
    rw [hk]
    exact le_mul_of_one_le_right hn'.le hk1
  linarith

#check four_delta_int_of_dvd
#check fourDelta_pos
#check not_int_dvd_of_pos_lt

lemma thirteen_lt_prime_seventeen {q : ℕ} (hq : q.Prime) (h : 13 < q) : 17 ≤ q := by
  have hne14 : q ≠ 14 := fun eq ↦ (by decide : ¬ Nat.Prime 14) (eq ▸ hq)
  have hne15 : q ≠ 15 := fun eq ↦ (by decide : ¬ Nat.Prime 15) (eq ▸ hq)
  have hne16 : q ≠ 16 := fun eq ↦ (by decide : ¬ Nat.Prime 16) (eq ▸ hq)
  omega

lemma seventeen_lt_prime_nineteen {q : ℕ} (hq : q.Prime) (h : 17 < q) : 19 ≤ q := by
  have hne18 : q ≠ 18 := fun eq ↦ (by decide : ¬ Nat.Prime 18) (eq ▸ hq)
  omega

lemma nineteen_lt_prime_twentythree {q : ℕ} (hq : q.Prime) (h : 19 < q) : 23 ≤ q := by
  have hne20 : q ≠ 20 := fun eq ↦ (by decide : ¬ Nat.Prime 20) (eq ▸ hq)
  have hne21 : q ≠ 21 := fun eq ↦ (by decide : ¬ Nat.Prime 21) (eq ▸ hq)
  have hne22 : q ≠ 22 := fun eq ↦ (by decide : ¬ Nat.Prime 22) (eq ▸ hq)
  omega

lemma fourDelta_sub_eq (p q r s : ℕ) :
    (p * q * r * s : ℤ) - fourDelta p q r s =
      (p * q * r : ℤ) * s
        - 4 * (p * q * r + p * q * s + p * r * s + q * r * s)
        + 2 * (p * q + p * r + p * s + q * r + q * s + r * s)
        - (p + q + r + s) + 1 := by
  unfold fourDelta; ring

/-- `n - Δ` as a linear polynomial in `s`. -/
lemma n_sub_fourDelta_decomp (p q r s : ℕ) :
    (p * q * r * s : ℤ) - fourDelta p q r s =
      (s : ℤ) * ((p * q * r : ℤ) - 4 * (p * q + p * r + q * r) + 2 * (p + q + r) - 1)
        + (-4 * (p * q * r : ℤ) + 2 * (p * q + p * r + q * r) - (p + q + r) + 1) := by
  unfold fourDelta; ring

lemma mul_le_mul_right_of_le {a b c : ℤ} (h : 0 ≤ c) (hab : a ≤ b) : a * c ≤ b * c :=
  mul_le_mul_of_nonneg_right hab h


lemma fourDelta_lt_prod_of_bounds {p q r s : ℕ}
    (hp : 13 ≤ p) (hq : 17 ≤ q) (hr : 19 ≤ r) (hs : 23 ≤ s) :
    fourDelta p q r s < p * q * r * s := by
  have hp' : (13 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (17 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (19 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (23 : ℤ) ≤ s := by exact_mod_cast hs
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hpq0 : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr0 : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hqr0 : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  have hpq_b : (13 * 17 * 19 : ℤ) * (p * q) ≤ (13 * 17 : ℤ) * (p * q * r) := by
    calc (13 * 17 * 19 : ℤ) * (p * q)
        = (13 * 17 : ℤ) * ((p * q : ℤ) * 19) := by ring
      _ ≤ (13 * 17 : ℤ) * (p * q * r) :=
          mul_le_mul_of_nonneg_left
            (by
              have := mul_le_mul_of_nonneg_left hr' hpq0
              linarith)
            (by norm_num)
  have hpr_b : (13 * 17 * 19 : ℤ) * (p * r) ≤ (13 * 19 : ℤ) * (p * q * r) := by
    calc (13 * 17 * 19 : ℤ) * (p * r)
        = (13 * 19 : ℤ) * ((p * r : ℤ) * 17) := by ring
      _ ≤ (13 * 19 : ℤ) * (p * q * r) :=
          mul_le_mul_of_nonneg_left
            (by
              have := mul_le_mul_of_nonneg_left hq' hpr0
              linarith)
            (by norm_num)
  have hqr_b : (13 * 17 * 19 : ℤ) * (q * r) ≤ (17 * 19 : ℤ) * (p * q * r) := by
    calc (13 * 17 * 19 : ℤ) * (q * r)
        = (17 * 19 : ℤ) * (13 * (q * r)) := by ring
      _ ≤ (17 * 19 : ℤ) * (p * q * r) :=
          mul_le_mul_of_nonneg_left
            (by
              have := mul_le_mul_of_nonneg_right hp' hqr0
              linarith)
            (by norm_num)
  have hsum :
      (13 * 17 * 19 : ℤ) * (p * q + p * r + q * r)
        ≤ (13 * 17 + 13 * 19 + 17 * 19 : ℤ) * (p * q * r) := by
    nlinarith [hpq_b, hpr_b, hqr_b]
  have hform :
      (p * q * r * s : ℤ) - fourDelta p q r s =
        (p * q * r : ℤ) * (s - 4)
          - (p * q + p * r + q * r : ℤ) * (4 * s - 2)
          + (p + q + r : ℤ) * (2 * s - 1) - s + 1 := by
    unfold fourDelta; ring
  have hcmp :
      (4 * (s : ℤ) - 2) * (13 * 17 + 13 * 19 + 17 * 19)
        < (s - 4) * (13 * 17 * 19) := by
    nlinarith [hs']
  have hmain :
      (p * q + p * r + q * r : ℤ) * (4 * s - 2)
        < (p * q * r : ℤ) * (s - 4) := by
    have hpos4s : (0 : ℤ) ≤ 4 * s - 2 := by omega
    have hL :
        (p * q + p * r + q * r : ℤ) * (4 * s - 2) * (13 * 17 * 19)
          ≤ (p * q * r : ℤ) * (13 * 17 + 13 * 19 + 17 * 19) * (4 * s - 2) := by
      have := mul_le_mul_of_nonneg_right hsum hpos4s
      convert this using 1 <;> ring
    have hpqrpos : (0 : ℤ) < p * q * r := by
      nlinarith [hp', hq', hr']
    have hR :
        (p * q * r : ℤ) * (13 * 17 + 13 * 19 + 17 * 19) * (4 * s - 2)
          < (p * q * r : ℤ) * (s - 4) * (13 * 17 * 19) := by
      nlinarith [hcmp, hpqrpos]
    have hden : (0 : ℤ) < 13 * 17 * 19 := by norm_num
    nlinarith
  have hextra : (0 : ℤ) ≤ (p + q + r : ℤ) * (2 * s - 1) - s + 1 := by
    nlinarith [hp', hq', hr', hs']
  have : 0 < (p * q * r * s : ℤ) - fourDelta p q r s := by
    rw [hform]
    nlinarith [hmain, hextra]
  linarith

lemma odd_prime_ge_three {p : ℕ} (hp : p.Prime) (hodd : Odd p) : 3 ≤ p := by
  have hne2 : p ≠ 2 := fun h2 ↦ Nat.not_odd_iff_even.2 even_two (h2 ▸ hodd)
  have : 2 < p := hp.two_le.lt_of_ne' hne2
  omega

lemma not_dvd_pillai_four_odd_primes_sorted {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpodd : Odd p) (hqodd : Odd q) (hrodd : Odd r) (hsodd : Odd s)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrs : r ≠ s)
    (hord : p ≤ q ∧ q ≤ r ∧ r ≤ s)
    (hp13 : 13 ≤ p) :
    ¬ (p * q * r * s) ∣
      (2 * p - 1) * (2 * q - 1) * (2 * r - 1) * (2 * s - 1) + 1 := by
  intro h
  obtain ⟨hpq_le, hqr_le, hrs_le⟩ := hord
  have hq17 : 17 ≤ q := by
    rcases lt_or_eq_of_le hpq_le with hlt | rfl
    · exact thirteen_lt_prime_seventeen hq (hp13.trans_lt hlt)
    · exact (hpq rfl).elim
  have hr19 : 19 ≤ r := by
    rcases lt_or_eq_of_le hqr_le with hlt | rfl
    · exact seventeen_lt_prime_nineteen hr (hq17.trans_lt hlt)
    · exact (hqr rfl).elim
  have hs23 : 23 ≤ s := by
    rcases lt_or_eq_of_le hrs_le with hlt | rfl
    · exact nineteen_lt_prime_twentythree hs (hr19.trans_lt hlt)
    · exact (hrs rfl).elim
  have hdvd := four_delta_int_of_dvd hp hq hr hs hpodd hqodd hrodd hsodd h
  have hpos := fourDelta_pos (by omega : 3 ≤ p) (by omega : 3 ≤ q)
    (by omega : 3 ≤ r) (by omega : 3 ≤ s)
  have hlt := fourDelta_lt_prod_of_bounds hp13 hq17 hr19 hs23
  have hnpos : 0 < p * q * r * s :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos) hs.pos
  exact not_int_dvd_of_pos_lt hnpos hpos hlt hdvd

/-- Specialization: `fourDelta 3 q r s - 3*q*r*s`. -/
lemma fourDelta_sub_n_of_three (q r s : ℕ) :
    fourDelta 3 q r s - (3 * q * r * s : ℤ) =
      (q * r * s : ℤ) + 10 * (q * r + q * s + r * s) - 5 * (q + r + s) + 2 := by
  unfold fourDelta; ring

lemma fourDelta_sub_two_n_of_three (q r s : ℕ) :
    fourDelta 3 q r s - 2 * (3 * q * r * s : ℤ) =
      -2 * (q * r * s : ℤ) + 10 * (q * r + q * s + r * s) - 5 * (q + r + s) + 2 := by
  unfold fourDelta; ring

lemma fourDelta_gt_n_of_three {q r s : ℕ}
    (hq : 5 ≤ q) (hr : 5 ≤ r) (hs : 5 ≤ s) :
    (3 * q * r * s : ℤ) < fourDelta 3 q r s := by
  rw [← sub_pos, fourDelta_sub_n_of_three]
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (5 : ℤ) ≤ s := by exact_mod_cast hs
  have hcoeff : (0 : ℤ) < q * r + 10 * q + 10 * r - 5 := by nlinarith
  have hconst : (0 : ℤ) < 10 * q * r - 5 * q - 5 * r + 2 := by nlinarith
  have hdecomp :
      (q * r * s : ℤ) + 10 * (q * r + q * s + r * s) - 5 * (q + r + s) + 2 =
        (s : ℤ) * (q * r + 10 * q + 10 * r - 5)
          + (10 * q * r - 5 * q - 5 * r + 2) := by ring
  rw [hdecomp]
  nlinarith

lemma fourDelta_lt_two_n_of_three_large {q r s : ℕ}
    (hq : 13 ≤ q) (hr : 17 ≤ r) (hs : 19 ≤ s) :
    fourDelta 3 q r s < 2 * (3 * q * r * s : ℤ) := by
  have hdiff : fourDelta 3 q r s - 2 * (3 * q * r * s : ℤ) < 0 := by
    rw [fourDelta_sub_two_n_of_three]
    have hq' : (13 : ℤ) ≤ q := by exact_mod_cast hq
    have hr' : (17 : ℤ) ≤ r := by exact_mod_cast hr
    have hs' : (19 : ℤ) ≤ s := by exact_mod_cast hs
    have hden : (0 : ℤ) < 2 * q * r - 10 * q - 10 * r + 5 := by nlinarith
    have hdecomp :
        -2 * (q * r * s : ℤ) + 10 * (q * r + q * s + r * s) - 5 * (q + r + s) + 2 =
          -((s : ℤ) * (2 * q * r - 10 * q - 10 * r + 5)
            - (10 * q * r - 5 * q - 5 * r + 2)) := by ring
    rw [hdecomp]
    have : (10 * q * r - 5 * q - 5 * r + 2) <
        (s : ℤ) * (2 * q * r - 10 * q - 10 * r + 5) := by
      have hsden : (19 : ℤ) * (2 * q * r - 10 * q - 10 * r + 5)
          ≤ s * (2 * q * r - 10 * q - 10 * r + 5) :=
        mul_le_mul_of_nonneg_right hs' (le_of_lt hden)
      nlinarith
    linarith
  linarith

lemma prime_4093 : Nat.Prime 4093 := by
  rw [Nat.prime_def_minFac]
  constructor <;> norm_num

lemma int_factor_4093 {a b : ℤ} (h : a * b = 4093) :
    a = 1 ∧ b = 4093 ∨ a = -1 ∧ b = -4093 ∨
    a = 4093 ∧ b = 1 ∨ a = -4093 ∧ b = -1 := by
  have habs : a.natAbs * b.natAbs = 4093 := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_mul] using this
  have hpr := prime_4093
  have ha : a.natAbs = 1 ∨ a.natAbs = 4093 := by
    have := (Nat.dvd_prime hpr).1 ⟨b.natAbs, habs.symm⟩
    exact this
  rcases ha with ha | ha
  · have ha1 : a = 1 ∨ a = -1 := Int.natAbs_eq_iff.mp ha
    rcases ha1 with rfl | rfl
    · have : b = 4093 := by
        have : (1 : ℤ) * b = 4093 := h
        simpa using this
      exact Or.inl ⟨rfl, this⟩
    · have : b = -4093 := by
        have : (-1 : ℤ) * b = 4093 := h
        linarith
      exact Or.inr (Or.inl ⟨rfl, this⟩)
  · have ha1 : a = 4093 ∨ a = -4093 := Int.natAbs_eq_iff.mp ha
    rcases ha1 with rfl | rfl
    · have : b = 1 := by
        have : (4093 : ℤ) * b = 4093 := h
        nlinarith
      exact Or.inr (Or.inr (Or.inl ⟨rfl, this⟩))
    · have : b = -1 := by
        have : (-4093 : ℤ) * b = 4093 := h
        nlinarith
      exact Or.inr (Or.inr (Or.inr ⟨rfl, this⟩))

lemma not_eq_two_n_three_seven (r s : ℕ) :
    fourDelta 3 7 r s ≠ 2 * (3 * 7 * r * s : ℤ) := by
  intro heq
  have hdiff : fourDelta 3 7 r s - 2 * (3 * 7 * r * s : ℤ) = 0 := by
    linarith
  have hexp : fourDelta 3 7 r s - 2 * (3 * 7 * r * s : ℤ) =
      -4 * (r : ℤ) * s + 65 * r + 65 * s - 33 := by
    have h := fourDelta_sub_two_n_of_three 7 r s
    convert h using 1; ring
  rw [hexp] at hdiff
  have hprod : (4 * (r : ℤ) - 65) * (4 * s - 65) = 4093 := by
    nlinarith
  rcases int_factor_4093 hprod with h | h | h | h
  · have : (4 * (r : ℤ) - 65) = 1 := h.1
    have : (4 * r : ℤ) = 66 := by linarith
    have : ¬ (4 ∣ (66 : ℤ)) := by decide
    exact this ⟨r, by linarith⟩
  · have : (4 * (s : ℤ) - 65) = -4093 := h.2
    have : (s : ℤ) = -1007 := by linarith
    have : (0 : ℤ) ≤ s := by exact_mod_cast (Nat.zero_le s)
    linarith
  · have : (4 * (r : ℤ) - 65) = 4093 := h.1
    have : (4 * r : ℤ) = 4158 := by linarith
    have : ¬ (4 ∣ (4158 : ℤ)) := by decide
    exact this ⟨r, by linarith⟩
  · have : (4 * (r : ℤ) - 65) = -4093 := h.1
    have : (r : ℤ) = -1007 := by linarith
    have : (0 : ℤ) ≤ r := by exact_mod_cast (Nat.zero_le r)
    linarith





lemma fourDelta_lt_three_n_of_three {q r s : ℕ}
    (hq : 7 ≤ q) (hr : 11 ≤ r) (hs : 13 ≤ s) :
    fourDelta 3 q r s < 3 * (3 * q * r * s : ℤ) := by
  have hq' : (7 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (11 : ℤ) ≤ r := by exact_mod_cast hr
  have hs' : (13 : ℤ) ≤ s := by exact_mod_cast hs
  have hform :
      3 * (3 * q * r * s : ℤ) - fourDelta 3 q r s =
        5 * (q * r * s : ℤ) - 10 * (q * r + q * s + r * s)
          + 5 * (q + r + s) - 2 := by
    unfold fourDelta; ring
  have hpos : 0 < 3 * (3 * q * r * s : ℤ) - fourDelta 3 q r s := by
    rw [hform]
    have hcoeff : (0 : ℤ) < 5 * q * r - 10 * q - 10 * r + 5 := by nlinarith
    have hdecomp :
        5 * (q * r * s : ℤ) - 10 * (q * r + q * s + r * s) + 5 * (q + r + s) - 2 =
          (s : ℤ) * (5 * q * r - 10 * q - 10 * r + 5)
            + (-10 * q * r + 5 * q + 5 * r - 2) := by ring
    rw [hdecomp]
    -- s*coeff ≥ 13*(5*7*11 - 10*7 - 10*11 + 5) = 13*(385-70-110+5)=13*210=2730
    -- -10qr+5q+5r-2 ≥ -10*q*s_max? Upper q,r unbounded makes -10qr more negative!
    -- Need s*5qr to beat 10qr: 5s > 10, s>2. Yes asymptotically.
    --  s*(5qr-10q-10r+5) -10qr +5q+5r-2
    -- = qr(5s-10) -s(10q+10r-5) +5q+5r-2
    have : (q * r : ℤ) * (5 * s - 10) - s * (10 * q + 10 * r - 5) + 5 * q + 5 * r - 2 > 0 := by
      have hqr : (7 * 11 : ℤ) ≤ q * r := by nlinarith
      have hs10 : (5 * (13 : ℤ) - 10) ≤ 5 * s - 10 := by omega
      nlinarith
    nlinarith
  linarith

lemma not_int_dvd_between_one_and_three {n : ℕ} {d : ℤ}
    (hn : 0 < n) (hgt : (n : ℤ) < d) (hne : d ≠ 2 * (n : ℤ))
    (hlt : d < 3 * (n : ℤ)) : ¬ (n : ℤ) ∣ d := by
  intro ⟨k, hk⟩
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hkpos : 0 < k := by
    have hdpos : 0 < d := lt_trans hn' hgt
    have hkn : 0 < (n : ℤ) * k := by rwa [← hk]
    by_contra hk0
    have : k ≤ 0 := le_of_not_gt hk0
    have : (n : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn'.le this
    linarith
  have hk1 : (1 : ℤ) ≤ k := by omega
  have hk_ne1 : k ≠ 1 := by
    intro h1; subst h1
    have : d = (n : ℤ) := by simpa [mul_one] using hk
    linarith
  have hk_ne2 : k ≠ 2 := by
    intro h2; subst h2
    apply hne
    simpa [mul_comm] using hk
  have hkge3 : (3 : ℤ) ≤ k := by omega
  have : (3 : ℤ) * n ≤ d := by
    rw [hk, mul_comm (n : ℤ) k]
    exact mul_le_mul_of_nonneg_right hkge3 hn'.le
  linarith

lemma ne_three_of_odd_prime_ne {p : ℕ} (hp : p.Prime) (hne : p ≠ 3)
    (hodd : Odd p) : 5 ≤ p :=
  hp.five_le_of_ne_two_of_ne_three
    (fun h2 ↦ Nat.not_odd_iff_even.2 even_two (h2 ▸ hodd)) hne

#check not_int_dvd_between_one_and_three
#check fourDelta_lt_three_n_of_three

lemma four_finset_min_spec {p q r s : ℕ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    let S : Finset ℕ := {p, q, r, s}
    S.card = 4 := by
  simp [hpq, hpr, hps, hqr, hqs, hrs]

#check four_finset_min_spec
