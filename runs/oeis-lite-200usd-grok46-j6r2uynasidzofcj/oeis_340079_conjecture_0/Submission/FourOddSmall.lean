import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def fourDelta (p q r s : ℕ) : ℤ :=
  4 * (p * q * r + p * q * s + p * r * s + q * r * s : ℤ)
    - 2 * (p * q + p * r + p * s + q * r + q * s + r * s)
    + (p + q + r + s) - 1

def fourA (p q r : ℕ) : ℤ :=
  4 * (p * q + p * r + q * r : ℤ) - 2 * (p + q + r) + 1

def fourB (p q r : ℕ) : ℤ :=
  4 * (p * q * r : ℤ) - 2 * (p * q + p * r + q * r) + (p + q + r) - 1

lemma two_n_sub_fourDelta (p q r s : ℕ) :
    2 * (p * q * r * s : ℤ) - fourDelta p q r s =
      (s : ℤ) * (2 * (p * q * r : ℤ) - fourA p q r) - fourB p q r := by
  unfold fourDelta fourA fourB; ring

lemma n_sub_fourDelta (p q r s : ℕ) :
    (p * q * r * s : ℤ) - fourDelta p q r s =
      (s : ℤ) * ((p * q * r : ℤ) - fourA p q r) - fourB p q r := by
  unfold fourDelta fourA fourB; ring

lemma fourB_pos {p q r : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (hr : 5 ≤ r) :
    (0 : ℤ) < fourB p q r := by
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (5 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (5 : ℤ) ≤ r := by exact_mod_cast hr
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  have h1 : (5 : ℤ) * (p * q) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hr' hpq
    convert this using 1 <;> ring
  have h2 : (5 : ℤ) * (p * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hq' hpr
    convert this using 1 <;> ring
  have h3 : (5 : ℤ) * (q * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hp' hqr
    convert this using 1 <;> ring
  unfold fourB
  nlinarith

lemma two_pqr_sub_fourA_pos {p q r : ℕ}
    (hp : 5 ≤ p) (hq : 7 ≤ q) (hr : 11 ≤ r) :
    (0 : ℤ) < 2 * (p * q * r : ℤ) - fourA p q r := by
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (7 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (11 : ℤ) ≤ r := by exact_mod_cast hr
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  -- Compare 2pqr vs 4(pq+pr+qr) using r≥11, q≥7, p≥5
  have h1 : (11 : ℤ) * (p * q) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hr' hpq
    convert this using 1 <;> ring
  have h2 : (7 : ℤ) * (p * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hq' hpr
    convert this using 1 <;> ring
  have h3 : (5 : ℤ) * (q * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hp' hqr
    convert this using 1 <;> ring
  unfold fourA
  -- 2pqr - 4pq - 4pr - 4qr + 2p+2q+2r - 1
  -- ≥ pqr * (2 - 4/11 - 4/7 - 4/5) + positive
  -- 4/11+4/7+4/5 = (140+220+308)/385 = 668/385 ≈ 1.735 < 2
  nlinarith

lemma fourB_lt_thirteen_coeff {p q r : ℕ}
    (hp : 5 ≤ p) (hq : 7 ≤ q) (hr : 11 ≤ r) :
    fourB p q r < 13 * (2 * (p * q * r : ℤ) - fourA p q r) := by
  have hp' : (5 : ℤ) ≤ p := by exact_mod_cast hp
  have hq' : (7 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (11 : ℤ) ≤ r := by exact_mod_cast hr
  have hp0 : (0 : ℤ) ≤ p := by omega
  have hq0 : (0 : ℤ) ≤ q := by omega
  have hr0 : (0 : ℤ) ≤ r := by omega
  have hpq : (0 : ℤ) ≤ p * q := mul_nonneg hp0 hq0
  have hpr : (0 : ℤ) ≤ p * r := mul_nonneg hp0 hr0
  have hqr : (0 : ℤ) ≤ q * r := mul_nonneg hq0 hr0
  have h1 : (11 : ℤ) * (p * q) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hr' hpq
    convert this using 1 <;> ring
  have h2 : (7 : ℤ) * (p * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hq' hpr
    convert this using 1 <;> ring
  have h3 : (5 : ℤ) * (q * r) ≤ p * q * r := by
    have := mul_le_mul_of_nonneg_left hp' hqr
    convert this using 1 <;> ring
  unfold fourA fourB
  nlinarith

lemma fourDelta_lt_two_n {p q r s : ℕ}
    (hp : 5 ≤ p) (hq : 7 ≤ q) (hr : 11 ≤ r) (hs : 13 ≤ s) :
    fourDelta p q r s < 2 * (p * q * r * s : ℤ) := by
  have hs' : (13 : ℤ) ≤ s := by exact_mod_cast hs
  have hcoeff := two_pqr_sub_fourA_pos hp hq hr
  have hcmp := fourB_lt_thirteen_coeff hp hq hr
  have h13 : (13 : ℤ) * (2 * (p * q * r : ℤ) - fourA p q r)
      ≤ s * (2 * (p * q * r : ℤ) - fourA p q r) :=
    mul_le_mul_of_nonneg_right hs' (le_of_lt hcoeff)
  have hpos : 0 < 2 * (p * q * r * s : ℤ) - fourDelta p q r s := by
    rw [two_n_sub_fourDelta]
    linarith
  linarith

lemma fourA_ge_pqr_five_seven {r : ℕ} (hr : 7 ≤ r) :
    (5 : ℤ) * 7 * r ≤ fourA 5 7 r := by
  have hr' : (7 : ℤ) ≤ r := by exact_mod_cast hr
  unfold fourA
  push_cast
  nlinarith

lemma fourA_ge_pqr_five_eleven {r : ℕ} (hr : 11 ≤ r) :
    (5 : ℤ) * 11 * r ≤ fourA 5 11 r := by
  have hr' : (11 : ℤ) ≤ r := by exact_mod_cast hr
  unfold fourA
  push_cast
  nlinarith

lemma fourA_ge_pqr_five_thirteen {r : ℕ} (hr : 13 ≤ r) :
    (5 : ℤ) * 13 * r ≤ fourA 5 13 r := by
  have hr' : (13 : ℤ) ≤ r := by exact_mod_cast hr
  unfold fourA
  push_cast
  nlinarith

lemma fourA_ge_pqr_five_seventeen {r : ℕ} (hr : 17 ≤ r) :
    (5 : ℤ) * 17 * r ≤ fourA 5 17 r := by
  have hr' : (17 : ℤ) ≤ r := by exact_mod_cast hr
  unfold fourA
  push_cast
  nlinarith

lemma fourDelta_gt_n_of_A {p q r s : ℕ}
    (hA : (p : ℤ) * q * r ≤ fourA p q r)
    (hB : 0 < fourB p q r)
    (hs : 1 ≤ s) :
    (p : ℤ) * q * r * s < fourDelta p q r s := by
  have hs' : (1 : ℤ) ≤ s := by exact_mod_cast hs
  have hform := n_sub_fourDelta p q r s
  have : fourDelta p q r s - (p : ℤ) * q * r * s =
      (s : ℤ) * (fourA p q r - (p : ℤ) * q * r) + fourB p q r := by
    unfold fourDelta fourA fourB at *
    linarith
  have h1 : (0 : ℤ) ≤ (s : ℤ) * (fourA p q r - (p : ℤ) * q * r) :=
    mul_nonneg (by omega) (sub_nonneg.mpr hA)
  linarith

/-- `r * (pqr - A) - B` expanded. -/
lemma r_mul_D_sub_B_simp (p q r : ℕ) :
    (r : ℤ) * ((p : ℤ) * q * r - fourA p q r) - fourB p q r =
      (p : ℤ) * q * r * r
        - 8 * p * q * r
        - 4 * p * r * r
        - 4 * q * r * r
        + 4 * p * r + 4 * q * r + 2 * r * r
        + 2 * p * q
        - p - q - 2 * r + 1 := by
  unfold fourA fourB; ring

lemma five_diff_eq (q r : ℕ) :
    (r : ℤ) * ((5 : ℤ) * q * r - fourA 5 q r) - fourB 5 q r =
      (q : ℤ) * (r * r - 36 * r + 9) - 18 * r * r + 18 * r - 4 := by
  unfold fourA fourB; ring

lemma fourB_lt_r_mul_D_five_large {q r : ℕ}
    (hq : 53 ≤ q) (hr : 59 ≤ r) :
    fourB 5 q r < (r : ℤ) * ((5 : ℤ) * q * r - fourA 5 q r) := by
  have hq' : (53 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (59 : ℤ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < (r : ℤ) * ((5 : ℤ) * q * r - fourA 5 q r) - fourB 5 q r := by
    rw [five_diff_eq]
    have hquad : (0 : ℤ) < r * r - 36 * r + 9 := by nlinarith
    have h1 : (53 : ℤ) * (r * r - 36 * r + 9) ≤ q * (r * r - 36 * r + 9) :=
      mul_le_mul_of_nonneg_right hq' (le_of_lt hquad)
    nlinarith
  linarith

lemma seven_diff_eq (q r : ℕ) :
    (r : ℤ) * ((7 : ℤ) * q * r - fourA 7 q r) - fourB 7 q r =
      (q : ℤ) * (3 * r * r - 52 * r + 13) - 26 * r * r + 26 * r - 6 := by
  unfold fourA fourB; ring

lemma fourB_lt_r_mul_D_seven_large {q r : ℕ}
    (hq : 23 ≤ q) (hr : 29 ≤ r) :
    fourB 7 q r < (r : ℤ) * ((7 : ℤ) * q * r - fourA 7 q r) := by
  have hq' : (23 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (29 : ℤ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < (r : ℤ) * ((7 : ℤ) * q * r - fourA 7 q r) - fourB 7 q r := by
    rw [seven_diff_eq]
    have hquad : (0 : ℤ) < 3 * r * r - 52 * r + 13 := by nlinarith
    have h1 : (23 : ℤ) * (3 * r * r - 52 * r + 13) ≤ q * (3 * r * r - 52 * r + 13) :=
      mul_le_mul_of_nonneg_right hq' (le_of_lt hquad)
    nlinarith
  linarith

lemma eleven_diff_eq (q r : ℕ) :
    (r : ℤ) * ((11 : ℤ) * q * r - fourA 11 q r) - fourB 11 q r =
      (q : ℤ) * (7 * r * r - 84 * r + 21) - 42 * r * r + 42 * r - 10 := by
  unfold fourA fourB; ring

lemma fourB_lt_r_mul_D_eleven_large {q r : ℕ}
    (hq : 17 ≤ q) (hr : 19 ≤ r) :
    fourB 11 q r < (r : ℤ) * ((11 : ℤ) * q * r - fourA 11 q r) := by
  have hq' : (17 : ℤ) ≤ q := by exact_mod_cast hq
  have hr' : (19 : ℤ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < (r : ℤ) * ((11 : ℤ) * q * r - fourA 11 q r) - fourB 11 q r := by
    rw [eleven_diff_eq]
    have hquad : (0 : ℤ) < 7 * r * r - 84 * r + 21 := by nlinarith
    have h1 : (17 : ℤ) * (7 * r * r - 84 * r + 21) ≤ q * (7 * r * r - 84 * r + 21) :=
      mul_le_mul_of_nonneg_right hq' (le_of_lt hquad)
    nlinarith
  linarith


lemma D_eq_lin (p q r : ℕ) :
    (p : ℤ) * q * r - fourA p q r =
      ((p : ℤ) * q - 4 * p - 4 * q + 2) * r
        + (-4 * p * q + 2 * p + 2 * q - 1) := by
  unfold fourA; ring

lemma B_eq_lin (p q r : ℕ) :
    fourB p q r =
      ((4 : ℤ) * p * q - 2 * p - 2 * q + 1) * r
        + (-2 * p * q + p + q - 1) := by
  unfold fourB; ring

lemma rho_identity (p q r : ℕ) :
    let α := (p : ℤ) * q - 4 * p - 4 * q + 2
    let β := (-4 : ℤ) * p * q + 2 * p + 2 * q - 1
    let γ := (4 : ℤ) * p * q - 2 * p - 2 * q + 1
    let δ := (-2 : ℤ) * p * q + p + q - 1
    α * (γ * r + δ) - γ * (α * r + β) = α * δ - β * γ := by
  ring

lemma fourDelta_eq_n_iff (p q r s : ℕ) :
    fourDelta p q r s = (p : ℤ) * q * r * s ↔
      (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r := by
  have h := n_sub_fourDelta p q r s
  constructor
  · intro heq; linarith
  · intro heq; linarith

lemma natAbs_eq_self_of_pos {d : ℤ} {n : ℕ} (hd : 0 < d) (h : d.natAbs = n) :
    d = n := by
  have := Int.natAbs_eq_iff.mp h
  rcases this with h | h
  · exact h
  · linarith

lemma dvd_rho_of_s_mul {p q r s : ℕ}
    (heq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r) :
    ((p : ℤ) * q - 4 * p - 4 * q + 2) * r
        + ((-4 : ℤ) * p * q + 2 * p + 2 * q - 1)
      ∣
    (((p : ℤ) * q - 4 * p - 4 * q + 2)
        * ((-2 : ℤ) * p * q + p + q - 1)
      - ((-4 : ℤ) * p * q + 2 * p + 2 * q - 1)
        * ((4 : ℤ) * p * q - 2 * p - 2 * q + 1)) := by
  set α := (p : ℤ) * q - 4 * p - 4 * q + 2
  set β := (-4 : ℤ) * p * q + 2 * p + 2 * q - 1
  set γ := (4 : ℤ) * p * q - 2 * p - 2 * q + 1
  set δ := (-2 : ℤ) * p * q + p + q - 1
  have hD := D_eq_lin p q r
  have hB := B_eq_lin p q r
  have hEq' : (s : ℤ) * (α * r + β) = γ * r + δ := by
    dsimp [α, β, γ, δ]
    rw [← hD, ← hB]; exact heq
  have hDB : (α * r + β) ∣ (γ * r + δ) :=
    ⟨s, (hEq'.symm.trans (mul_comm _ _))⟩
  have hid : α * (γ * r + δ) - γ * (α * r + β) = α * δ - β * γ := by ring
  have h1 : (α * r + β) ∣ α * (γ * r + δ) := hDB.mul_left α
  have h2 : (α * r + β) ∣ γ * (α * r + β) := ⟨γ, by ring⟩
  have hsub := Int.dvd_sub h1 h2
  rw [hid] at hsub
  simpa [α, β, γ, δ] using hsub

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

lemma divisors_260342 : Nat.divisors 260342 = {1, 2, 130171, 260342} := by
  native_decide

lemma fourDelta_ne_n_p5_q29 {r s : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrmin : 31 ≤ r) :
    fourDelta 5 29 r s ≠ (5 : ℤ) * 29 * r * s := by
  -- Work with p, q as ℕ variables so all casts are `↑p`.
  let p : ℕ := 5
  let q : ℕ := 29
  have hp : p = 5 := rfl
  have hq : q = 29 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (11 : ℤ) * r - 513 := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 31) hrmin)
  set D := (11 : ℤ) * r - 513
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (260342 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 260342 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 260342 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_260342] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (11 : ℤ) * r = 514 := by unfold D at hDeq; linarith
    have hdvd' : (11 : ℤ) ∣ 514 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((11 : ℤ) ∣ (514 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (11 : ℤ) * r = 515 := by unfold D at hDeq; linarith
    have hdvd' : (11 : ℤ) ∣ 515 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((11 : ℤ) ∣ (515 : ℤ))) hdvd'
  · have hDeq : D = 130171 := natAbs_eq_self_of_pos hDpos h
    have : (11 : ℤ) * r = 130684 := by unfold D at hDeq; linarith
    have hdvd' : (11 : ℤ) ∣ 130684 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((11 : ℤ) ∣ (130684 : ℤ))) hdvd'
  · have hDeq : D = 260342 := natAbs_eq_self_of_pos hDpos h
    have : (11 : ℤ) * r = 260855 := by unfold D at hDeq; linarith
    have hdvd' : (11 : ℤ) ∣ 260855 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((11 : ℤ) ∣ (260855 : ℤ))) hdvd'

/-- Auto-generated remaining pairs. -/

lemma divisors_110722 : Nat.divisors 110722 = {1, 2, 23, 29, 46, 58, 83, 166, 667, 1334, 1909, 2407, 3818, 4814, 55361, 110722} := by
  native_decide

lemma fourDelta_ne_n_p5_q19 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 23 ≤ r) :
    fourDelta 5 19 r s ≠ (5 : ℤ) * 19 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 19
  have hp : p = 5 := rfl
  have hq : q = 19 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (1 : ℤ) * r + (-333) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 23) hrmin)
  set D := (1 : ℤ) * r + (-333)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (110722 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 110722 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 110722 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_110722] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 334 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 334 := by nlinarith
    have hrnat : r = 334 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 334) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 335 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 335 := by nlinarith
    have hrnat : r = 335 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 335) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 23 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 356 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 356 := by nlinarith
    have hrnat : r = 356 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 356) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 29 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 362 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 362 := by nlinarith
    have hrnat : r = 362 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 362) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 46 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 379 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 379 := by nlinarith
    have hrnat : r = 379 := by exact_mod_cast hrval
    subst hrnat
    have hseq : (s : ℤ) * 46 = 126040 := by
      have hB : fourB p q 379 = 126040 := by
        unfold fourB p q; norm_num
      rw [hDeq, hB] at hEq; exact hEq
    have hsval : s = 2740 := by
      have : (s : ℤ) = 2740 := by nlinarith
      exact_mod_cast this
    have : ¬ (Nat.Prime 2740) := by norm_num
    exact this (hsval ▸ hs)
  · have hDeq : D = 58 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 391 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 391 := by nlinarith
    have hrnat : r = 391 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 391) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 83 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 416 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 416 := by nlinarith
    have hrnat : r = 416 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 416) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 166 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 499 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 499 := by nlinarith
    have hrnat : r = 499 := by exact_mod_cast hrval
    subst hrnat
    have hseq : (s : ℤ) * 166 = 166000 := by
      have hB : fourB p q 499 = 166000 := by
        unfold fourB p q; norm_num
      rw [hDeq, hB] at hEq; exact hEq
    have hsval : s = 1000 := by
      have : (s : ℤ) = 1000 := by nlinarith
      exact_mod_cast this
    have : ¬ (Nat.Prime 1000) := by norm_num
    exact this (hsval ▸ hs)
  · have hDeq : D = 667 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 1000 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 1000 := by nlinarith
    have hrnat : r = 1000 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 1000) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 1334 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 1667 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 1667 := by nlinarith
    have hrnat : r = 1667 := by exact_mod_cast hrval
    subst hrnat
    have hseq : (s : ℤ) * 1334 = 554944 := by
      have hB : fourB p q 1667 = 554944 := by
        unfold fourB p q; norm_num
      rw [hDeq, hB] at hEq; exact hEq
    have hsval : s = 416 := by
      have : (s : ℤ) = 416 := by nlinarith
      exact_mod_cast this
    have : ¬ (Nat.Prime 416) := by norm_num
    exact this (hsval ▸ hs)
  · have hDeq : D = 1909 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 2242 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 2242 := by nlinarith
    have hrnat : r = 2242 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 2242) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 2407 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 2740 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 2740 := by nlinarith
    have hrnat : r = 2740 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 2740) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 3818 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 4151 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 4151 := by nlinarith
    have hrnat : r = 4151 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 4151) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 4814 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 5147 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 5147 := by nlinarith
    have hrnat : r = 5147 := by exact_mod_cast hrval
    subst hrnat
    have hseq : (s : ℤ) * 4814 = 1713784 := by
      have hB : fourB p q 5147 = 1713784 := by
        unfold fourB p q; norm_num
      rw [hDeq, hB] at hEq; exact hEq
    have hsval : s = 356 := by
      have : (s : ℤ) = 356 := by nlinarith
      exact_mod_cast this
    have : ¬ (Nat.Prime 356) := by norm_num
    exact this (hsval ▸ hs)
  · have hDeq : D = 55361 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 55694 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 55694 := by nlinarith
    have hrnat : r = 55694 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 55694) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 110722 := natAbs_eq_self_of_pos hDpos h
    have : (1 : ℤ) * r = 111055 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 111055 := by nlinarith
    have hrnat : r = 111055 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 111055) := by norm_num
    exact this (hrnat ▸ hr)

lemma divisors_163010 : Nat.divisors 163010 = {1, 2, 5, 10, 16301, 32602, 81505, 163010} := by
  native_decide

lemma fourDelta_ne_n_p5_q23 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 29 ≤ r) :
    fourDelta 5 23 r s ≠ (5 : ℤ) * 23 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 23
  have hp : p = 5 := rfl
  have hq : q = 23 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (5 : ℤ) * r + (-405) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 29) hrmin)
  set D := (5 : ℤ) * r + (-405)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (163010 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 163010 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 163010 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_163010] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 406 := by unfold D at hDeq; linarith
    have hdvd' : (5 : ℤ) ∣ 406 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((5 : ℤ) ∣ (406 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 407 := by unfold D at hDeq; linarith
    have hdvd' : (5 : ℤ) ∣ 407 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((5 : ℤ) ∣ (407 : ℤ))) hdvd'
  · have hDeq : D = 5 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 410 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 82 := by nlinarith
    have hrnat : r = 82 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 82) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 10 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 415 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 83 := by nlinarith
    have hrnat : r = 83 := by exact_mod_cast hrval
    subst hrnat
    have hB : fourB p q 83 = 33412 := by unfold fourB p q; norm_num
    rw [hDeq, hB] at hEq
    exact (by decide : ¬ ((10 : ℤ) ∣ (33412 : ℤ))) ⟨s, by linarith⟩
  · have hDeq : D = 16301 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 16706 := by unfold D at hDeq; linarith
    have hdvd' : (5 : ℤ) ∣ 16706 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((5 : ℤ) ∣ (16706 : ℤ))) hdvd'
  · have hDeq : D = 32602 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 33007 := by unfold D at hDeq; linarith
    have hdvd' : (5 : ℤ) ∣ 33007 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((5 : ℤ) ∣ (33007 : ℤ))) hdvd'
  · have hDeq : D = 81505 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 81910 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 16382 := by nlinarith
    have hrnat : r = 16382 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 16382) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 163010 := natAbs_eq_self_of_pos hDpos h
    have : (5 : ℤ) * r = 163415 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 32683 := by nlinarith
    have hrnat : r = 32683 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 32683) := by norm_num
    exact this (hrnat ▸ hr)

lemma divisors_297826 : Nat.divisors 297826 = {1, 2, 148913, 297826} := by
  native_decide

lemma fourDelta_ne_n_p5_q31 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 37 ≤ r) :
    fourDelta 5 31 r s ≠ (5 : ℤ) * 31 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 31
  have hp : p = 5 := rfl
  have hq : q = 31 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (13 : ℤ) * r + (-549) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 37) hrmin)
  set D := (13 : ℤ) * r + (-549)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (297826 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 297826 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 297826 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_297826] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 550 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 550 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (550 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 551 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 551 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (551 : ℤ))) hdvd'
  · have hDeq : D = 148913 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 149462 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 149462 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (149462 : ℤ))) hdvd'
  · have hDeq : D = 297826 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 298375 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 298375 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (298375 : ℤ))) hdvd'

lemma divisors_425398 : Nat.divisors 425398 = {1, 2, 227, 454, 937, 1874, 212699, 425398} := by
  native_decide

lemma fourDelta_ne_n_p5_q37 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 41 ≤ r) :
    fourDelta 5 37 r s ≠ (5 : ℤ) * 37 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 37
  have hp : p = 5 := rfl
  have hq : q = 37 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (19 : ℤ) * r + (-657) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 41) hrmin)
  set D := (19 : ℤ) * r + (-657)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (425398 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 425398 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 425398 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_425398] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 658 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 658 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (658 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 659 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 659 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (659 : ℤ))) hdvd'
  · have hDeq : D = 227 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 884 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 884 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (884 : ℤ))) hdvd'
  · have hDeq : D = 454 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 1111 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 1111 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (1111 : ℤ))) hdvd'
  · have hDeq : D = 937 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 1594 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 1594 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (1594 : ℤ))) hdvd'
  · have hDeq : D = 1874 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 2531 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 2531 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (2531 : ℤ))) hdvd'
  · have hDeq : D = 212699 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 213356 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 213356 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (213356 : ℤ))) hdvd'
  · have hDeq : D = 425398 := natAbs_eq_self_of_pos hDpos h
    have : (19 : ℤ) * r = 426055 := by unfold D at hDeq; linarith
    have hdvd' : (19 : ℤ) ∣ 426055 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((19 : ℤ) ∣ (426055 : ℤ))) hdvd'

lemma divisors_523046 : Nat.divisors 523046 = {1, 2, 261523, 523046} := by
  native_decide

lemma fourDelta_ne_n_p5_q41 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 43 ≤ r) :
    fourDelta 5 41 r s ≠ (5 : ℤ) * 41 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 41
  have hp : p = 5 := rfl
  have hq : q = 41 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (23 : ℤ) * r + (-729) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 43) hrmin)
  set D := (23 : ℤ) * r + (-729)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (523046 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 523046 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 523046 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_523046] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (23 : ℤ) * r = 730 := by unfold D at hDeq; linarith
    have hdvd' : (23 : ℤ) ∣ 730 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((23 : ℤ) ∣ (730 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (23 : ℤ) * r = 731 := by unfold D at hDeq; linarith
    have hdvd' : (23 : ℤ) ∣ 731 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((23 : ℤ) ∣ (731 : ℤ))) hdvd'
  · have hDeq : D = 261523 := natAbs_eq_self_of_pos hDpos h
    have : (23 : ℤ) * r = 262252 := by unfold D at hDeq; linarith
    have hdvd' : (23 : ℤ) ∣ 262252 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((23 : ℤ) ∣ (262252 : ℤ))) hdvd'
  · have hDeq : D = 523046 := natAbs_eq_self_of_pos hDpos h
    have : (23 : ℤ) * r = 523775 := by unfold D at hDeq; linarith
    have hdvd' : (23 : ℤ) ∣ 523775 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((23 : ℤ) ∣ (523775 : ℤ))) hdvd'

lemma divisors_575650 : Nat.divisors 575650 = {1, 2, 5, 10, 25, 29, 50, 58, 145, 290, 397, 725, 794, 1450, 1985, 3970, 9925, 11513, 19850, 23026, 57565, 115130, 287825, 575650} := by
  native_decide

lemma fourDelta_ne_n_p5_q43 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 47 ≤ r) :
    fourDelta 5 43 r s ≠ (5 : ℤ) * 43 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 43
  have hp : p = 5 := rfl
  have hq : q = 43 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (25 : ℤ) * r + (-765) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 47) hrmin)
  set D := (25 : ℤ) * r + (-765)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (575650 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 575650 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 575650 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_575650] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 766 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 766 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (766 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 767 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 767 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (767 : ℤ))) hdvd'
  · have hDeq : D = 5 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 770 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 770 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (770 : ℤ))) hdvd'
  · have hDeq : D = 10 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 775 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 31 := by nlinarith
    have hrnat : r = 31 := by exact_mod_cast hrval
    subst hrnat
    have hB : fourB p q 31 = 23332 := by unfold fourB p q; norm_num
    rw [hDeq, hB] at hEq
    exact (by decide : ¬ ((10 : ℤ) ∣ (23332 : ℤ))) ⟨s, by linarith⟩
  · have hDeq : D = 25 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 790 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 790 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (790 : ℤ))) hdvd'
  · have hDeq : D = 29 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 794 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 794 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (794 : ℤ))) hdvd'
  · have hDeq : D = 50 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 815 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 815 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (815 : ℤ))) hdvd'
  · have hDeq : D = 58 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 823 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 823 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (823 : ℤ))) hdvd'
  · have hDeq : D = 145 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 910 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 910 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (910 : ℤ))) hdvd'
  · have hDeq : D = 290 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 1055 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 1055 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (1055 : ℤ))) hdvd'
  · have hDeq : D = 397 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 1162 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 1162 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (1162 : ℤ))) hdvd'
  · have hDeq : D = 725 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 1490 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 1490 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (1490 : ℤ))) hdvd'
  · have hDeq : D = 794 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 1559 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 1559 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (1559 : ℤ))) hdvd'
  · have hDeq : D = 1450 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 2215 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 2215 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (2215 : ℤ))) hdvd'
  · have hDeq : D = 1985 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 2750 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 110 := by nlinarith
    have hrnat : r = 110 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 110) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 3970 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 4735 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 4735 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (4735 : ℤ))) hdvd'
  · have hDeq : D = 9925 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 10690 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 10690 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (10690 : ℤ))) hdvd'
  · have hDeq : D = 11513 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 12278 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 12278 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (12278 : ℤ))) hdvd'
  · have hDeq : D = 19850 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 20615 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 20615 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (20615 : ℤ))) hdvd'
  · have hDeq : D = 23026 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 23791 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 23791 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (23791 : ℤ))) hdvd'
  · have hDeq : D = 57565 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 58330 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 58330 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (58330 : ℤ))) hdvd'
  · have hDeq : D = 115130 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 115895 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 115895 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (115895 : ℤ))) hdvd'
  · have hDeq : D = 287825 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 288590 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 288590 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (288590 : ℤ))) hdvd'
  · have hDeq : D = 575650 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 576415 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 576415 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (576415 : ℤ))) hdvd'

lemma divisors_688418 : Nat.divisors 688418 = {1, 2, 344209, 688418} := by
  native_decide

lemma fourDelta_ne_n_p5_q47 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 53 ≤ r) :
    fourDelta 5 47 r s ≠ (5 : ℤ) * 47 * r * s := by
  let p : ℕ := 5
  let q : ℕ := 47
  have hp : p = 5 := rfl
  have hq : q = 47 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (29 : ℤ) * r + (-837) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 53) hrmin)
  set D := (29 : ℤ) * r + (-837)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (688418 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 688418 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 688418 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_688418] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (29 : ℤ) * r = 838 := by unfold D at hDeq; linarith
    have hdvd' : (29 : ℤ) ∣ 838 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((29 : ℤ) ∣ (838 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (29 : ℤ) * r = 839 := by unfold D at hDeq; linarith
    have hdvd' : (29 : ℤ) ∣ 839 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((29 : ℤ) ∣ (839 : ℤ))) hdvd'
  · have hDeq : D = 344209 := natAbs_eq_self_of_pos hDpos h
    have : (29 : ℤ) * r = 345046 := by unfold D at hDeq; linarith
    have hdvd' : (29 : ℤ) ∣ 345046 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((29 : ℤ) ∣ (345046 : ℤ))) hdvd'
  · have hDeq : D = 688418 := natAbs_eq_self_of_pos hDpos h
    have : (29 : ℤ) * r = 689255 := by unfold D at hDeq; linarith
    have hdvd' : (29 : ℤ) ∣ 689255 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((29 : ℤ) ∣ (689255 : ℤ))) hdvd'

lemma divisors_73570 : Nat.divisors 73570 = {1, 2, 5, 7, 10, 14, 35, 70, 1051, 2102, 5255, 7357, 10510, 14714, 36785, 73570} := by
  native_decide

lemma fourDelta_ne_n_p7_q11 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 13 ≤ r) :
    fourDelta 7 11 r s ≠ (7 : ℤ) * 11 * r * s := by
  let p : ℕ := 7
  let q : ℕ := 11
  have hp : p = 7 := rfl
  have hq : q = 11 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (7 : ℤ) * r + (-273) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 13) hrmin)
  set D := (7 : ℤ) * r + (-273)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (73570 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 73570 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 73570 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_73570] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 274 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 274 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (274 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 275 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 275 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (275 : ℤ))) hdvd'
  · have hDeq : D = 5 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 278 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 278 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (278 : ℤ))) hdvd'
  · have hDeq : D = 7 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 280 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 40 := by nlinarith
    have hrnat : r = 40 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 40) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 10 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 283 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 283 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (283 : ℤ))) hdvd'
  · have hDeq : D = 14 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 287 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 41 := by nlinarith
    have hrnat : r = 41 := by exact_mod_cast hrval
    subst hrnat
    have hB : fourB p q 41 = 11056 := by unfold fourB p q; norm_num
    rw [hDeq, hB] at hEq
    exact (by decide : ¬ ((14 : ℤ) ∣ (11056 : ℤ))) ⟨s, by linarith⟩
  · have hDeq : D = 35 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 308 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 44 := by nlinarith
    have hrnat : r = 44 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 44) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 70 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 343 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 49 := by nlinarith
    have hrnat : r = 49 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 49) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 1051 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 1324 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 1324 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (1324 : ℤ))) hdvd'
  · have hDeq : D = 2102 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 2375 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 2375 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (2375 : ℤ))) hdvd'
  · have hDeq : D = 5255 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 5528 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 5528 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (5528 : ℤ))) hdvd'
  · have hDeq : D = 7357 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 7630 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 1090 := by nlinarith
    have hrnat : r = 1090 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 1090) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 10510 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 10783 := by unfold D at hDeq; linarith
    have hdvd' : (7 : ℤ) ∣ 10783 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((7 : ℤ) ∣ (10783 : ℤ))) hdvd'
  · have hDeq : D = 14714 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 14987 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 2141 := by nlinarith
    have hrnat : r = 2141 := by exact_mod_cast hrval
    subst hrnat
    have hB : fourB p q 2141 = 584356 := by unfold fourB p q; norm_num
    rw [hDeq, hB] at hEq
    exact (by decide : ¬ ((14714 : ℤ) ∣ (584356 : ℤ))) ⟨s, by linarith⟩
  · have hDeq : D = 36785 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 37058 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 5294 := by nlinarith
    have hrnat : r = 5294 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 5294) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 73570 := natAbs_eq_self_of_pos hDpos h
    have : (7 : ℤ) * r = 73843 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 10549 := by nlinarith
    have hrnat : r = 10549 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 10549) := by norm_num
    exact this (hrnat ▸ hr)

lemma divisors_103506 : Nat.divisors 103506 = {1, 2, 3, 6, 13, 26, 39, 78, 1327, 2654, 3981, 7962, 17251, 34502, 51753, 103506} := by
  native_decide

lemma fourDelta_ne_n_p7_q13 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 17 ≤ r) :
    fourDelta 7 13 r s ≠ (7 : ℤ) * 13 * r * s := by
  let p : ℕ := 7
  let q : ℕ := 13
  have hp : p = 7 := rfl
  have hq : q = 13 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (13 : ℤ) * r + (-325) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 17) hrmin)
  set D := (13 : ℤ) * r + (-325)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (103506 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 103506 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 103506 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_103506] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 326 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 326 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (326 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 327 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 327 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (327 : ℤ))) hdvd'
  · have hDeq : D = 3 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 328 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 328 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (328 : ℤ))) hdvd'
  · have hDeq : D = 6 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 331 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 331 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (331 : ℤ))) hdvd'
  · have hDeq : D = 13 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 338 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 26 := by nlinarith
    have hrnat : r = 26 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 26) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 26 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 351 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 27 := by nlinarith
    have hrnat : r = 27 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 27) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 39 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 364 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 28 := by nlinarith
    have hrnat : r = 28 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 28) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 78 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 403 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 31 := by nlinarith
    have hrnat : r = 31 := by exact_mod_cast hrval
    subst hrnat
    have hB : fourB p q 31 = 9912 := by unfold fourB p q; norm_num
    rw [hDeq, hB] at hEq
    exact (by decide : ¬ ((78 : ℤ) ∣ (9912 : ℤ))) ⟨s, by linarith⟩
  · have hDeq : D = 1327 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 1652 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 1652 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (1652 : ℤ))) hdvd'
  · have hDeq : D = 2654 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 2979 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 2979 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (2979 : ℤ))) hdvd'
  · have hDeq : D = 3981 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 4306 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 4306 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (4306 : ℤ))) hdvd'
  · have hDeq : D = 7962 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 8287 := by unfold D at hDeq; linarith
    have hdvd' : (13 : ℤ) ∣ 8287 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((13 : ℤ) ∣ (8287 : ℤ))) hdvd'
  · have hDeq : D = 17251 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 17576 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 1352 := by nlinarith
    have hrnat : r = 1352 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 1352) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 34502 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 34827 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 2679 := by nlinarith
    have hrnat : r = 2679 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 2679) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 51753 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 52078 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 4006 := by nlinarith
    have hrnat : r = 4006 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 4006) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 103506 := natAbs_eq_self_of_pos hDpos h
    have : (13 : ℤ) * r = 103831 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 7987 := by nlinarith
    have hrnat : r = 7987 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 7987) := by norm_num
    exact this (hrnat ▸ hr)

lemma divisors_178666 : Nat.divisors 178666 = {1, 2, 157, 314, 569, 1138, 89333, 178666} := by
  native_decide

lemma fourDelta_ne_n_p7_q17 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 19 ≤ r) :
    fourDelta 7 17 r s ≠ (7 : ℤ) * 17 * r * s := by
  let p : ℕ := 7
  let q : ℕ := 17
  have hp : p = 7 := rfl
  have hq : q = 17 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (25 : ℤ) * r + (-429) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 19) hrmin)
  set D := (25 : ℤ) * r + (-429)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (178666 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 178666 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 178666 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_178666] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 430 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 430 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (430 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 431 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 431 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (431 : ℤ))) hdvd'
  · have hDeq : D = 157 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 586 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 586 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (586 : ℤ))) hdvd'
  · have hDeq : D = 314 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 743 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 743 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (743 : ℤ))) hdvd'
  · have hDeq : D = 569 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 998 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 998 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (998 : ℤ))) hdvd'
  · have hDeq : D = 1138 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 1567 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 1567 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (1567 : ℤ))) hdvd'
  · have hDeq : D = 89333 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 89762 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 89762 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (89762 : ℤ))) hdvd'
  · have hDeq : D = 178666 := natAbs_eq_self_of_pos hDpos h
    have : (25 : ℤ) * r = 179095 := by unfold D at hDeq; linarith
    have hdvd' : (25 : ℤ) ∣ 179095 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((25 : ℤ) ∣ (179095 : ℤ))) hdvd'

lemma divisors_223890 : Nat.divisors 223890 = {1, 2, 3, 5, 6, 10, 15, 17, 30, 34, 51, 85, 102, 170, 255, 439, 510, 878, 1317, 2195, 2634, 4390, 6585, 7463, 13170, 14926, 22389, 37315, 44778, 74630, 111945, 223890} := by
  native_decide

lemma fourDelta_ne_n_p7_q19 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 23 ≤ r) :
    fourDelta 7 19 r s ≠ (7 : ℤ) * 19 * r * s := by
  let p : ℕ := 7
  let q : ℕ := 19
  have hp : p = 7 := rfl
  have hq : q = 19 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (31 : ℤ) * r + (-481) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 23) hrmin)
  set D := (31 : ℤ) * r + (-481)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (223890 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 223890 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 223890 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_223890] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 482 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 482 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (482 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 483 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 483 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (483 : ℤ))) hdvd'
  · have hDeq : D = 3 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 484 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 484 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (484 : ℤ))) hdvd'
  · have hDeq : D = 5 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 486 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 486 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (486 : ℤ))) hdvd'
  · have hDeq : D = 6 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 487 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 487 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (487 : ℤ))) hdvd'
  · have hDeq : D = 10 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 491 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 491 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (491 : ℤ))) hdvd'
  · have hDeq : D = 15 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 496 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 16 := by nlinarith
    have hrnat : r = 16 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 16) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 17 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 498 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 498 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (498 : ℤ))) hdvd'
  · have hDeq : D = 30 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 511 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 511 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (511 : ℤ))) hdvd'
  · have hDeq : D = 34 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 515 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 515 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (515 : ℤ))) hdvd'
  · have hDeq : D = 51 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 532 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 532 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (532 : ℤ))) hdvd'
  · have hDeq : D = 85 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 566 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 566 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (566 : ℤ))) hdvd'
  · have hDeq : D = 102 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 583 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 583 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (583 : ℤ))) hdvd'
  · have hDeq : D = 170 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 651 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 21 := by nlinarith
    have hrnat : r = 21 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 21) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 255 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 736 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 736 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (736 : ℤ))) hdvd'
  · have hDeq : D = 439 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 920 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 920 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (920 : ℤ))) hdvd'
  · have hDeq : D = 510 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 991 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 991 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (991 : ℤ))) hdvd'
  · have hDeq : D = 878 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 1359 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 1359 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (1359 : ℤ))) hdvd'
  · have hDeq : D = 1317 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 1798 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 58 := by nlinarith
    have hrnat : r = 58 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 58) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 2195 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 2676 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 2676 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (2676 : ℤ))) hdvd'
  · have hDeq : D = 2634 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 3115 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 3115 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (3115 : ℤ))) hdvd'
  · have hDeq : D = 4390 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 4871 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 4871 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (4871 : ℤ))) hdvd'
  · have hDeq : D = 6585 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 7066 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 7066 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (7066 : ℤ))) hdvd'
  · have hDeq : D = 7463 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 7944 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 7944 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (7944 : ℤ))) hdvd'
  · have hDeq : D = 13170 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 13651 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 13651 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (13651 : ℤ))) hdvd'
  · have hDeq : D = 14926 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 15407 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 497 := by nlinarith
    have hrnat : r = 497 := by exact_mod_cast hrval
    have : ¬ (Nat.Prime 497) := by norm_num
    exact this (hrnat ▸ hr)
  · have hDeq : D = 22389 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 22870 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 22870 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (22870 : ℤ))) hdvd'
  · have hDeq : D = 37315 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 37796 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 37796 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (37796 : ℤ))) hdvd'
  · have hDeq : D = 44778 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 45259 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 45259 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (45259 : ℤ))) hdvd'
  · have hDeq : D = 74630 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 75111 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 75111 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (75111 : ℤ))) hdvd'
  · have hDeq : D = 111945 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 112426 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 112426 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (112426 : ℤ))) hdvd'
  · have hDeq : D = 223890 := natAbs_eq_self_of_pos hDpos h
    have : (31 : ℤ) * r = 224371 := by unfold D at hDeq; linarith
    have hdvd' : (31 : ℤ) ∣ 224371 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((31 : ℤ) ∣ (224371 : ℤ))) hdvd'

lemma divisors_262738 : Nat.divisors 262738 = {1, 2, 7, 14, 49, 98, 343, 383, 686, 766, 2681, 5362, 18767, 37534, 131369, 262738} := by
  native_decide

lemma fourDelta_ne_n_p11_q13 {r s : ℕ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hrmin : 17 ≤ r) :
    fourDelta 11 13 r s ≠ (11 : ℤ) * 13 * r * s := by
  let p : ℕ := 11
  let q : ℕ := 13
  have hp : p = 11 := rfl
  have hq : q = 13 := rfl
  change fourDelta p q r s ≠ (p : ℤ) * q * r * s
  intro heq
  have hEq : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r) = fourB p q r :=
    (fourDelta_eq_n_iff p q r s).mp heq
  have hDlin : (p : ℤ) * q * r - fourA p q r = (49 : ℤ) * r + (-525) := by
    rw [D_eq_lin, hp, hq]; ring
  rw [hDlin] at hEq
  have hBpos : 0 < fourB p q r :=
    fourB_pos (by simp [p]) (by simp [q])
      (le_trans (by norm_num : (5 : ℕ) ≤ 17) hrmin)
  set D := (49 : ℤ) * r + (-525)
  by_cases hDle : D ≤ 0
  · have hA : (p : ℤ) * q * r ≤ fourA p q r := by linarith
    have hgt := fourDelta_gt_n_of_A hA hBpos hs.pos
    linarith
  have hDpos : 0 < D := not_le.mp hDle
  have hdvd : D ∣ (262738 : ℤ) := by
    have hdvd0 := dvd_rho_of_s_mul (p := p) (q := q) (r := r) (s := s)
      ((fourDelta_eq_n_iff p q r s).mp heq)
    simp only [p, q] at hdvd0
    norm_num at hdvd0
    convert hdvd0 using 1 <;> ring
  have habs : D.natAbs ∣ 262738 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hmem : D.natAbs ∈ Nat.divisors 262738 :=
    Nat.mem_divisors.2 ⟨habs, by norm_num⟩
  rw [divisors_262738] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hDeq : D = 1 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 526 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 526 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (526 : ℤ))) hdvd'
  · have hDeq : D = 2 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 527 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 527 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (527 : ℤ))) hdvd'
  · have hDeq : D = 7 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 532 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 532 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (532 : ℤ))) hdvd'
  · have hDeq : D = 14 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 539 := by unfold D at hDeq; linarith
    have hrval : (r : ℤ) = 11 := by nlinarith
    have hrnat : r = 11 := by exact_mod_cast hrval
    omega -- r = 11 < 17 ≤ r
  · have hDeq : D = 49 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 574 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 574 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (574 : ℤ))) hdvd'
  · have hDeq : D = 98 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 623 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 623 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (623 : ℤ))) hdvd'
  · have hDeq : D = 343 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 868 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 868 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (868 : ℤ))) hdvd'
  · have hDeq : D = 383 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 908 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 908 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (908 : ℤ))) hdvd'
  · have hDeq : D = 686 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 1211 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 1211 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (1211 : ℤ))) hdvd'
  · have hDeq : D = 766 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 1291 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 1291 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (1291 : ℤ))) hdvd'
  · have hDeq : D = 2681 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 3206 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 3206 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (3206 : ℤ))) hdvd'
  · have hDeq : D = 5362 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 5887 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 5887 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (5887 : ℤ))) hdvd'
  · have hDeq : D = 18767 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 19292 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 19292 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (19292 : ℤ))) hdvd'
  · have hDeq : D = 37534 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 38059 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 38059 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (38059 : ℤ))) hdvd'
  · have hDeq : D = 131369 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 131894 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 131894 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (131894 : ℤ))) hdvd'
  · have hDeq : D = 262738 := natAbs_eq_self_of_pos hDpos h
    have : (49 : ℤ) * r = 263263 := by unfold D at hDeq; linarith
    have hdvd' : (49 : ℤ) ∣ 263263 := ⟨r, by simpa using this.symm⟩
    exact (by decide : ¬ ((49 : ℤ) ∣ (263263 : ℤ))) hdvd'



lemma not_prime_comp (n : ℕ) (h : ¬ Nat.Prime n) {q : ℕ} (hq : q.Prime) : q ≠ n :=
  fun eq => h (eq ▸ hq)

lemma fiftythree_le_of_prime_gt_fortyseven {q : ℕ} (hq : q.Prime) (h : 47 < q) :
    53 ≤ q := by
  have h48 : q ≠ 48 := not_prime_comp 48 (by decide) hq
  have h49 : q ≠ 49 := not_prime_comp 49 (by decide) hq
  have h50 : q ≠ 50 := not_prime_comp 50 (by decide) hq
  have h51 : q ≠ 51 := not_prime_comp 51 (by decide) hq
  have h52 : q ≠ 52 := not_prime_comp 52 (by decide) hq
  omega

lemma twentythree_le_of_prime_gt_nineteen {q : ℕ} (hq : q.Prime) (h : 19 < q) :
    23 ≤ q := by
  have : q ≠ 20 := not_prime_comp 20 (by decide) hq
  have : q ≠ 21 := not_prime_comp 21 (by decide) hq
  have : q ≠ 22 := not_prime_comp 22 (by decide) hq
  omega

lemma seventeen_le_of_prime_gt_thirteen {q : ℕ} (hq : q.Prime) (h : 13 < q) :
    17 ≤ q := by
  have : q ≠ 14 := not_prime_comp 14 (by decide) hq
  have : q ≠ 15 := not_prime_comp 15 (by decide) hq
  have : q ≠ 16 := not_prime_comp 16 (by decide) hq
  omega

lemma fourDelta_ne_n_of_A_ge {p q r s : ℕ}
    (hA : (p : ℤ) * q * r ≤ fourA p q r)
    (hB : 0 < fourB p q r) (hs : 1 ≤ s) :
    fourDelta p q r s ≠ (p : ℤ) * q * r * s := by
  have hgt := fourDelta_gt_n_of_A hA hB hs
  linarith

lemma fourDelta_ne_n_of_B_lt {p q r s : ℕ}
    (hDpos : 0 < (p : ℤ) * q * r - fourA p q r)
    (hBlt : fourB p q r < (r : ℤ) * ((p : ℤ) * q * r - fourA p q r))
    (hrs : r ≤ s) :
    fourDelta p q r s ≠ (p : ℤ) * q * r * s := by
  intro heq
  have hEq := (fourDelta_eq_n_iff p q r s).mp heq
  have hsD : (s : ℤ) * ((p : ℤ) * q * r - fourA p q r)
      ≥ (r : ℤ) * ((p : ℤ) * q * r - fourA p q r) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (le_of_lt hDpos)
  linarith

lemma fourDelta_ne_n_five {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : 7 ≤ q) (hrs : q ≤ r) (hss : r ≤ s)
    (hne_qr : q ≠ r) :
    fourDelta 5 q r s ≠ (5 : ℤ) * q * r * s := by
  have hr7 : 7 ≤ r := le_trans hqr hrs
  have hs1 : 1 ≤ s := hs.pos
  have hB : 0 < fourB 5 q r :=
    fourB_pos (by norm_num) (le_trans (by norm_num : 5 ≤ 7) hqr) (le_trans (by norm_num : 5 ≤ 7) hr7)
  by_cases h7 : q = 7
  · subst h7
    exact fourDelta_ne_n_of_A_ge (fourA_ge_pqr_five_seven hr7) hB hs1
  by_cases h11 : q = 11
  · subst h11
    have hr11 : 11 ≤ r := le_trans (by omega) hrs
    exact fourDelta_ne_n_of_A_ge (fourA_ge_pqr_five_eleven hr11) hB hs1
  by_cases h13 : q = 13
  · subst h13
    have hr13 : 13 ≤ r := le_trans (by omega) hrs
    exact fourDelta_ne_n_of_A_ge (fourA_ge_pqr_five_thirteen hr13) hB hs1
  by_cases h17 : q = 17
  · subst h17
    have hr17 : 17 ≤ r := le_trans (by omega) hrs
    exact fourDelta_ne_n_of_A_ge (fourA_ge_pqr_five_seventeen hr17) hB hs1
  by_cases h19 : q = 19
  · subst h19
    have hr23 : 23 ≤ r := by
      have hlt : 19 < r := lt_of_le_of_ne hrs hne_qr
      exact twentythree_le_of_prime_gt_nineteen hr (by omega)
    exact fourDelta_ne_n_p5_q19 hr hs hr23
  by_cases h23 : q = 23
  · subst h23
    have hr29 : 29 ≤ r := by
      have hlt : 23 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 24 := not_prime_comp 24 (by decide) hr
      have : r ≠ 25 := not_prime_comp 25 (by decide) hr
      have : r ≠ 26 := not_prime_comp 26 (by decide) hr
      have : r ≠ 27 := not_prime_comp 27 (by decide) hr
      have : r ≠ 28 := not_prime_comp 28 (by decide) hr
      omega
    exact fourDelta_ne_n_p5_q23 hr hs hr29
  by_cases h29 : q = 29
  · subst h29
    have hr31 : 31 ≤ r := by
      have hlt : 29 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 30 := not_prime_comp 30 (by decide) hr
      omega
    exact fourDelta_ne_n_p5_q29 hr hs hr31
  by_cases h31 : q = 31
  · subst h31
    have hr37 : 37 ≤ r := by
      have hlt : 31 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 32 := not_prime_comp 32 (by decide) hr
      have : r ≠ 33 := not_prime_comp 33 (by decide) hr
      have : r ≠ 34 := not_prime_comp 34 (by decide) hr
      have : r ≠ 35 := not_prime_comp 35 (by decide) hr
      have : r ≠ 36 := not_prime_comp 36 (by decide) hr
      omega
    exact fourDelta_ne_n_p5_q31 hr hs hr37
  by_cases h37 : q = 37
  · subst h37
    have hr41 : 41 ≤ r := by
      have hlt : 37 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 38 := not_prime_comp 38 (by decide) hr
      have : r ≠ 39 := not_prime_comp 39 (by decide) hr
      have : r ≠ 40 := not_prime_comp 40 (by decide) hr
      omega
    exact fourDelta_ne_n_p5_q37 hr hs hr41
  by_cases h41 : q = 41
  · subst h41
    have hr43 : 43 ≤ r := by
      have hlt : 41 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 42 := not_prime_comp 42 (by decide) hr
      omega
    exact fourDelta_ne_n_p5_q41 hr hs hr43
  by_cases h43 : q = 43
  · subst h43
    have hr47 : 47 ≤ r := by
      have hlt : 43 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 44 := not_prime_comp 44 (by decide) hr
      have : r ≠ 45 := not_prime_comp 45 (by decide) hr
      have : r ≠ 46 := not_prime_comp 46 (by decide) hr
      omega
    exact fourDelta_ne_n_p5_q43 hr hs hr47
  by_cases h47 : q = 47
  · subst h47
    have hr53 : 53 ≤ r := by
      have hlt : 47 < r := lt_of_le_of_ne hrs hne_qr
      exact fiftythree_le_of_prime_gt_fortyseven hr hlt
    exact fourDelta_ne_n_p5_q47 hr hs hr53
  have hq53 : 53 ≤ q := by
    have h48 : q ≠ 48 := not_prime_comp 48 (by decide) hq
    have h49 : q ≠ 49 := not_prime_comp 49 (by decide) hq
    have h50 : q ≠ 50 := not_prime_comp 50 (by decide) hq
    have h51 : q ≠ 51 := not_prime_comp 51 (by decide) hq
    have h52 : q ≠ 52 := not_prime_comp 52 (by decide) hq
    have h4 : q ≠ 4 := not_prime_comp 4 (by decide) hq
    have h6 : q ≠ 6 := not_prime_comp 6 (by decide) hq
    have h8 : q ≠ 8 := not_prime_comp 8 (by decide) hq
    have h9 : q ≠ 9 := not_prime_comp 9 (by decide) hq
    have h10 : q ≠ 10 := not_prime_comp 10 (by decide) hq
    have h12 : q ≠ 12 := not_prime_comp 12 (by decide) hq
    have h14 : q ≠ 14 := not_prime_comp 14 (by decide) hq
    have h15 : q ≠ 15 := not_prime_comp 15 (by decide) hq
    have h16 : q ≠ 16 := not_prime_comp 16 (by decide) hq
    have h18 : q ≠ 18 := not_prime_comp 18 (by decide) hq
    have h20 : q ≠ 20 := not_prime_comp 20 (by decide) hq
    have h21 : q ≠ 21 := not_prime_comp 21 (by decide) hq
    have h22 : q ≠ 22 := not_prime_comp 22 (by decide) hq
    have h24 : q ≠ 24 := not_prime_comp 24 (by decide) hq
    have h25 : q ≠ 25 := not_prime_comp 25 (by decide) hq
    have h26 : q ≠ 26 := not_prime_comp 26 (by decide) hq
    have h27 : q ≠ 27 := not_prime_comp 27 (by decide) hq
    have h28 : q ≠ 28 := not_prime_comp 28 (by decide) hq
    have h30 : q ≠ 30 := not_prime_comp 30 (by decide) hq
    have h32 : q ≠ 32 := not_prime_comp 32 (by decide) hq
    have h33 : q ≠ 33 := not_prime_comp 33 (by decide) hq
    have h34 : q ≠ 34 := not_prime_comp 34 (by decide) hq
    have h35 : q ≠ 35 := not_prime_comp 35 (by decide) hq
    have h36 : q ≠ 36 := not_prime_comp 36 (by decide) hq
    have h38 : q ≠ 38 := not_prime_comp 38 (by decide) hq
    have h39 : q ≠ 39 := not_prime_comp 39 (by decide) hq
    have h40 : q ≠ 40 := not_prime_comp 40 (by decide) hq
    have h42 : q ≠ 42 := not_prime_comp 42 (by decide) hq
    have h44 : q ≠ 44 := not_prime_comp 44 (by decide) hq
    have h45 : q ≠ 45 := not_prime_comp 45 (by decide) hq
    have h46 : q ≠ 46 := not_prime_comp 46 (by decide) hq
    omega
  have hr59 : 59 ≤ r := by
    have hlt : q < r := lt_of_le_of_ne hrs hne_qr
    have : 53 < r := lt_of_le_of_lt hq53 hlt
    have : r ≠ 54 := not_prime_comp 54 (by decide) hr
    have : r ≠ 55 := not_prime_comp 55 (by decide) hr
    have : r ≠ 56 := not_prime_comp 56 (by decide) hr
    have : r ≠ 57 := not_prime_comp 57 (by decide) hr
    have : r ≠ 58 := not_prime_comp 58 (by decide) hr
    omega
  by_cases hDle : (5 : ℤ) * q * r - fourA 5 q r ≤ 0
  · have hA : (5 : ℤ) * q * r ≤ fourA 5 q r := by linarith
    exact fourDelta_ne_n_of_A_ge hA hB hs1
  · have hDpos : 0 < (5 : ℤ) * q * r - fourA 5 q r := not_le.mp hDle
    have hBlt := fourB_lt_r_mul_D_five_large hq53 hr59
    exact fourDelta_ne_n_of_B_lt hDpos hBlt hss

lemma fourDelta_ne_n_seven {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : 11 ≤ q) (hrs : q ≤ r) (hss : r ≤ s)
    (hne_qr : q ≠ r) :
    fourDelta 7 q r s ≠ (7 : ℤ) * q * r * s := by
  have hs1 : 1 ≤ s := hs.pos
  have hB : 0 < fourB 7 q r :=
    fourB_pos (by norm_num) (le_trans (by norm_num : 5 ≤ 11) hqr)
      (le_trans (by norm_num : 5 ≤ 11) (le_trans hqr hrs))
  by_cases h11 : q = 11
  · subst h11
    have hr13 : 13 ≤ r := by
      have hlt : 11 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 12 := not_prime_comp 12 (by decide) hr
      omega
    exact fourDelta_ne_n_p7_q11 hr hs hr13
  by_cases h13 : q = 13
  · subst h13
    have hr17 : 17 ≤ r := by
      have hlt : 13 < r := lt_of_le_of_ne hrs hne_qr
      exact seventeen_le_of_prime_gt_thirteen hr hlt
    exact fourDelta_ne_n_p7_q13 hr hs hr17
  by_cases h17 : q = 17
  · subst h17
    have hr19 : 19 ≤ r := by
      have hlt : 17 < r := lt_of_le_of_ne hrs hne_qr
      have : r ≠ 18 := not_prime_comp 18 (by decide) hr
      omega
    exact fourDelta_ne_n_p7_q17 hr hs hr19
  by_cases h19 : q = 19
  · subst h19
    have hr23 : 23 ≤ r := by
      have hlt : 19 < r := lt_of_le_of_ne hrs hne_qr
      exact twentythree_le_of_prime_gt_nineteen hr hlt
    exact fourDelta_ne_n_p7_q19 hr hs hr23
  have hq23 : 23 ≤ q := by
    have h12 : q ≠ 12 := not_prime_comp 12 (by decide) hq
    have h14 : q ≠ 14 := not_prime_comp 14 (by decide) hq
    have h15 : q ≠ 15 := not_prime_comp 15 (by decide) hq
    have h16 : q ≠ 16 := not_prime_comp 16 (by decide) hq
    have h18 : q ≠ 18 := not_prime_comp 18 (by decide) hq
    have h20 : q ≠ 20 := not_prime_comp 20 (by decide) hq
    have h21 : q ≠ 21 := not_prime_comp 21 (by decide) hq
    have h22 : q ≠ 22 := not_prime_comp 22 (by decide) hq
    omega
  have hr29 : 29 ≤ r := by
    have hlt : q < r := lt_of_le_of_ne hrs hne_qr
    have : 23 < r := lt_of_le_of_lt hq23 hlt
    have : r ≠ 24 := not_prime_comp 24 (by decide) hr
    have : r ≠ 25 := not_prime_comp 25 (by decide) hr
    have : r ≠ 26 := not_prime_comp 26 (by decide) hr
    have : r ≠ 27 := not_prime_comp 27 (by decide) hr
    have : r ≠ 28 := not_prime_comp 28 (by decide) hr
    omega
  by_cases hDle : (7 : ℤ) * q * r - fourA 7 q r ≤ 0
  · have hA : (7 : ℤ) * q * r ≤ fourA 7 q r := by linarith
    exact fourDelta_ne_n_of_A_ge hA hB hs1
  · have hDpos : 0 < (7 : ℤ) * q * r - fourA 7 q r := not_le.mp hDle
    have hBlt := fourB_lt_r_mul_D_seven_large hq23 hr29
    exact fourDelta_ne_n_of_B_lt hDpos hBlt hss

lemma fourDelta_ne_n_eleven {q r s : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hqr : 13 ≤ q) (hrs : q ≤ r) (hss : r ≤ s)
    (hne_qr : q ≠ r) :
    fourDelta 11 q r s ≠ (11 : ℤ) * q * r * s := by
  have hs1 : 1 ≤ s := hs.pos
  have hB : 0 < fourB 11 q r :=
    fourB_pos (by norm_num) (le_trans (by norm_num : 5 ≤ 13) hqr)
      (le_trans (by norm_num : 5 ≤ 13) (le_trans hqr hrs))
  by_cases h13 : q = 13
  · subst h13
    have hr17 : 17 ≤ r := by
      have hlt : 13 < r := lt_of_le_of_ne hrs hne_qr
      exact seventeen_le_of_prime_gt_thirteen hr hlt
    exact fourDelta_ne_n_p11_q13 hr hs hr17
  have hq17 : 17 ≤ q := by
    have h14 : q ≠ 14 := not_prime_comp 14 (by decide) hq
    have h15 : q ≠ 15 := not_prime_comp 15 (by decide) hq
    have h16 : q ≠ 16 := not_prime_comp 16 (by decide) hq
    omega
  have hr19 : 19 ≤ r := by
    have hlt : q < r := lt_of_le_of_ne hrs hne_qr
    have : 17 < r := lt_of_le_of_lt hq17 hlt
    have : r ≠ 18 := not_prime_comp 18 (by decide) hr
    omega
  by_cases hDle : (11 : ℤ) * q * r - fourA 11 q r ≤ 0
  · have hA : (11 : ℤ) * q * r ≤ fourA 11 q r := by linarith
    exact fourDelta_ne_n_of_A_ge hA hB hs1
  · have hDpos : 0 < (11 : ℤ) * q * r - fourA 11 q r := not_le.mp hDle
    have hBlt := fourB_lt_r_mul_D_eleven_large hq17 hr19
    exact fourDelta_ne_n_of_B_lt hDpos hBlt hss

lemma fourDelta_ne_n_small {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hord : p ≤ q ∧ q ≤ r ∧ r ≤ s)
    (hpq : p ≠ q) (hqr : q ≠ r)
    (hp_small : p = 5 ∨ p = 7 ∨ p = 11) :
    fourDelta p q r s ≠ (p : ℤ) * q * r * s := by
  obtain ⟨hpqle, hqrle, hrsle⟩ := hord
  rcases hp_small with rfl | rfl | rfl
  · have hq7 : 7 ≤ q := by
      have hlt : 5 < q := lt_of_le_of_ne hpqle hpq
      have : q ≠ 6 := not_prime_comp 6 (by decide) hq
      omega
    exact fourDelta_ne_n_five hq hr hs hq7 hqrle hrsle hqr
  · have hq11 : 11 ≤ q := by
      have hlt : 7 < q := lt_of_le_of_ne hpqle hpq
      have : q ≠ 8 := not_prime_comp 8 (by decide) hq
      have : q ≠ 9 := not_prime_comp 9 (by decide) hq
      have : q ≠ 10 := not_prime_comp 10 (by decide) hq
      omega
    exact fourDelta_ne_n_seven hq hr hs hq11 hqrle hrsle hqr
  · have hq13 : 13 ≤ q := by
      have hlt : 11 < q := lt_of_le_of_ne hpqle hpq
      have : q ≠ 12 := not_prime_comp 12 (by decide) hq
      omega
    exact fourDelta_ne_n_eleven hq hr hs hq13 hqrle hrsle hqr

