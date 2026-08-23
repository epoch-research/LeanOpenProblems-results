import FormalConjectures.Util.ProblemImports

set_option linter.style.moduleDocstring false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Nat
open Zsqrtd Int

/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def A365416_condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of A365416 (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth A365416_condition

-- Formalization of the conjecture

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

/- Basic lemmas -/

lemma IsCompositePrimePow.four_le {m : ℕ} (h : IsCompositePrimePow m) : 4 ≤ m := by
  obtain ⟨p, e, hp, he, rfl⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  calc
    4 = 2 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
    _ ≤ p ^ e := Nat.pow_le_pow_right (by lia) he

lemma compositePrimePow_ge {k : ℕ} (h : IsCompositePrimePow (2 * k - 1)) : 3 ≤ k := by
  have h4 : 4 ≤ 2 * k - 1 := h.four_le
  by_contra hk
  interval_cases k <;> simp at h4

/- The easy direction: k = 13 works -/

lemma isCompositePrimePow_twenty_five : IsCompositePrimePow 25 :=
  ⟨5, 2, by decide, by decide, by decide⟩

lemma isCompositePrimePow_twenty_seven : IsCompositePrimePow 27 :=
  ⟨3, 3, by decide, by decide, by decide⟩

lemma thirteen_satisfies :
    IsCompositePrimePow (2 * 13 - 1) ∧ IsCompositePrimePow (2 * 13 + 1) := by
  constructor <;> norm_num
  · exact isCompositePrimePow_twenty_five
  · exact isCompositePrimePow_twenty_seven

/- Two squares cannot differ by 2 -/

lemma not_sq_eq_sq_add_two {x y : ℕ} (h : x ^ 2 = y ^ 2 + 2) : False := by
  have hyx : y ≤ x := by
    by_contra hxy
    have : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left (Nat.lt_of_not_ge hxy) (by decide)
    omega
  have hdiff : x ^ 2 - y ^ 2 = 2 := by omega
  have hfac : (x + y) * (x - y) = 2 := by
    rw [← Nat.sq_sub_sq]; exact hdiff
  have hxne : x ≠ y := by intro heq; subst heq; omega
  have hsub : 1 ≤ x - y := Nat.sub_pos_of_lt (lt_of_le_of_ne hyx hxne.symm)
  have hle1 : x - y ≤ 2 := by
    have : x - y ∣ 2 := ⟨x + y, by rw [mul_comm]; exact hfac.symm⟩
    exact Nat.le_of_dvd (by decide) this
  have : x - y = 1 ∨ x - y = 2 := by omega
  rcases this with h1 | h2
  · have : x + y = 2 := by
      rw [h1, mul_one] at hfac; exact hfac
    omega
  · have : x + y = 1 := by nlinarith
    omega

lemma even_pow_eq_sq (p e : ℕ) (he : Even e) : ∃ t : ℕ, p ^ e = t ^ 2 := by
  obtain ⟨k, hk⟩ := he
  refine ⟨p ^ k, ?_⟩
  rw [hk, show k + k = k * 2 from (two_mul k).symm ▸ (mul_comm 2 k)]
  exact pow_mul p k 2

lemma not_both_even_exponents {p q ea eb : ℕ}
    (hdiff : q ^ eb = p ^ ea + 2) (heaE : Even ea) (hebE : Even eb) : False := by
  obtain ⟨s, hs⟩ := even_pow_eq_sq p ea heaE
  obtain ⟨t, ht⟩ := even_pow_eq_sq q eb hebE
  apply not_sq_eq_sq_add_two (x := t) (y := s)
  rw [← ht, ← hs, hdiff]

lemma prime_of_even_pow {p e : ℕ} (hp : p.Prime) (h : Even (p ^ e)) : p = 2 := by
  have hpE : Even p := by
    by_contra hpo
    have : Odd p := Nat.not_even_iff_odd.mp hpo
    have : Odd (p ^ e) := Odd.pow this
    exact Nat.not_odd_iff_even.mpr h this
  exact hp.eq_two_or_odd'.resolve_right (Nat.not_odd_iff_even.mpr hpE)

lemma two_pow_sub_two_pow {a b : ℕ} (hba : b ≤ a) :
    2 ^ a - 2 ^ b = 2 ^ b * (2 ^ (a - b) - 1) := by
  rw [Nat.mul_sub_left_distrib, ← pow_add, Nat.add_sub_cancel' hba, mul_one]

lemma not_two_pow_diff_two {ea eb : ℕ} (hea : 1 < ea) (heb : 1 < eb)
    (h : 2 ^ eb = 2 ^ ea + 2) : False := by
  rcases le_total ea eb with hle | hle
  · have hsub : 2 ^ eb - 2 ^ ea = 2 := by omega
    rw [two_pow_sub_two_pow hle] at hsub
    have hdvd : 2 ^ ea ∣ 2 := ⟨2 ^ (eb - ea) - 1, hsub.symm⟩
    have : ea ≤ 1 :=
      (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
        (hdvd.trans (by decide : (2 : ℕ) ∣ 2 ^ 1))
    omega
  · have : 2 ^ ea < 2 ^ eb := by
      have : 0 < 2 ^ ea := Nat.pow_pos (by decide)
      omega
    have : ea < eb := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp this
    omega

/- The only solution of q^b - p^a = 2 with primes p, q and a, b > 1 is 3^3 - 5^2 = 2. -/



/-! Pell theory for `X^2 - 3 Y^2 = -2` and the equation `x^2 + 2 = 3^n`. -/

abbrev Zsqrtm2 := ℤ√(-2)


/-! The equation x^2 + 2 = 3^n. -/

open Int

def pellXY : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 =>
    let x := (pellXY n).1
    let y := (pellXY n).2
    (2 * x + 3 * y, x + 2 * y)

def pellX (n : ℕ) : ℤ := (pellXY n).1
def pellY (n : ℕ) : ℤ := (pellXY n).2

lemma pellX_zero : pellX 0 = 1 := rfl
lemma pellY_zero : pellY 0 = 1 := rfl
lemma pellX_succ (n : ℕ) : pellX (n + 1) = 2 * pellX n + 3 * pellY n := rfl
lemma pellY_succ (n : ℕ) : pellY (n + 1) = pellX n + 2 * pellY n := rfl

lemma pellX_one : pellX 1 = 5 := rfl
lemma pellY_one : pellY 1 = 3 := rfl

lemma pell_norm : ∀ n : ℕ, pellX n ^ 2 - 3 * pellY n ^ 2 = -2
  | 0 => by simp [pellX_zero, pellY_zero]
  | n + 1 => by
    have ih := pell_norm n
    rw [pellX_succ, pellY_succ]
    nlinarith

lemma pellX_pos_and_pellY_pos : ∀ n : ℕ, 0 < pellX n ∧ 0 < pellY n
  | 0 => by simp [pellX_zero, pellY_zero]
  | n + 1 => by
    obtain ⟨hx, hy⟩ := pellX_pos_and_pellY_pos n
    constructor
    · rw [pellX_succ]; nlinarith
    · rw [pellY_succ]; nlinarith

lemma pellX_pos (n : ℕ) : 0 < pellX n := (pellX_pos_and_pellY_pos n).1
lemma pellY_pos (n : ℕ) : 0 < pellY n := (pellX_pos_and_pellY_pos n).2

lemma pellY_succ2 (n : ℕ) : pellY (n + 2) = 4 * pellY (n + 1) - pellY n := by
  rw [pellY_succ, pellX_succ, pellY_succ]
  ring

private def ymod : ℕ → ZMod 3
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | n + 6 => ymod n

lemma ymod_succ2 (n : ℕ) : ymod (n + 2) = ymod (n + 1) - ymod n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | n + 6 =>
    simpa [ymod] using ymod_succ2 n

lemma pellY_zmod3 (n : ℕ) : (pellY n : ZMod 3) = ymod n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      change (1 : ZMod 3) = ymod 0
      rfl
    | 1 =>
      change (3 : ZMod 3) = ymod 1
      rfl
    | n + 2 =>
      have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have hcast : (pellY (n + 2) : ZMod 3) =
          (4 : ZMod 3) * (pellY (n + 1) : ZMod 3) - (pellY n : ZMod 3) := by
        rw [pellY_succ2 n]; norm_cast
      have : (4 : ZMod 3) = 1 := rfl
      have hr : (pellY (n + 2) : ZMod 3) =
          (pellY (n + 1) : ZMod 3) - (pellY n : ZMod 3) := by
        rw [hcast, this, one_mul]
      rw [hr, h0, h1, ymod_succ2]

lemma ymod_eq_zero_iff (n : ℕ) : ymod n = 0 ↔ n % 3 = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | n + 6 =>
      have ih' := ih n (by omega)
      have h6 : (n + 6) % 3 = n % 3 := Nat.add_mod_right n 3 ▸ (by
        have : (n + 6) % 3 = (n + 3 + 3) % 3 := by omega
        omega)
      -- simpler:
      have : (n + 6) % 3 = n % 3 := by omega
      simpa [ymod, this] using ih'

lemma pellY_three_dvd_iff (n : ℕ) : (3 : ℤ) ∣ pellY n ↔ n % 3 = 1 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (pellY n) 3).symm
  -- h : (3 : ℤ) ∣ pellY n ↔ (pellY n : ZMod 3) = 0  ? 
  -- actually : (pellY n : ZMod 3) = 0 ↔ ↑3 ∣ pellY n
  change (3 : ℤ) ∣ pellY n ↔ n % 3 = 1
  have : ((3 : ℕ) : ℤ) ∣ pellY n ↔ (pellY n : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (pellY n) 3).symm
  simpa using this.trans (by rw [pellY_zmod3, ymod_eq_zero_iff])


lemma pellY_lt_succ (n : ℕ) : pellY n < pellY (n + 1) := by
  induction n with
  | zero => simp [pellY_zero, pellY_one]
  | succ n ih =>
    have h2 := pellY_succ2 n
    have hpos0 := pellY_pos n
    have hpos1 := pellY_pos (n + 1)
    nlinarith


lemma not_sq_eq_ten {X : ℤ} (h : X ^ 2 = 10) : False := by
  have hxabs : |X| ≤ 4 := by
    have : X ^ 2 ≤ (4 : ℤ) ^ 2 := by norm_num [h]
    exact abs_le_of_sq_le_sq this (by decide)
  have hnn : 0 ≤ |X| := abs_nonneg _
  have : |X| = 0 ∨ |X| = 1 ∨ |X| = 2 ∨ |X| = 3 ∨ |X| = 4 := by omega
  rcases this with h0 | h1 | h2 | h3 | h4
  · rw [abs_eq_zero] at h0; subst h0; norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h2 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h3 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h4 with rfl | rfl <;> norm_num at h

/-- All positive solutions of `X^2 - 3 Y^2 = -2` arise from `(pellX, pellY)`. -/
lemma exists_pell_of_norm {X Y : ℤ} (hX : 0 < X) (hY : 0 < Y)
    (h : X ^ 2 - 3 * Y ^ 2 = -2) : ∃ k, X = pellX k ∧ Y = pellY k := by
  have helper : ∀ (N : ℕ) (X Y : ℤ), Y.natAbs = N → 0 < X → 0 < Y →
      X ^ 2 - 3 * Y ^ 2 = -2 → ∃ k, X = pellX k ∧ Y = pellY k := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X Y hYN hX hY h
      by_cases hY1 : Y = 1
      · subst hY1
        have hsq : X ^ 2 = 1 := by nlinarith
        have hx1 : X = 1 ∨ X = -1 := sq_eq_one_iff.mp hsq
        rcases hx1 with rfl | rfl
        · exact ⟨0, pellX_zero.symm, pellY_zero.symm⟩
        · exact (not_lt_of_ge (by decide : (-1 : ℤ) ≤ 0) hX).elim
      · have hYge3 : (3 : ℤ) ≤ Y := by
          have : (2 : ℤ) ≤ Y := by
            have : (1 : ℤ) ≤ Y := by omega
            omega
          by_contra hlt
          have : Y = 2 := by omega
          subst this
          have : X ^ 2 = 10 := by nlinarith
          exact not_sq_eq_ten this
        set X1 : ℤ := 2 * X - 3 * Y with hX1def
        set Y1 : ℤ := 2 * Y - X with hY1def
        have hnorm1 : X1 ^ 2 - 3 * Y1 ^ 2 = -2 := by
          rw [hX1def, hY1def]; nlinarith
        have hY1pos : 0 < Y1 := by
          have : X ^ 2 < (2 * Y) ^ 2 := by nlinarith
          have : |X| < 2 * Y :=
            lt_of_pow_lt_pow_left₀ 2 (by nlinarith : 0 ≤ 2 * Y) (by rwa [sq_abs])
          have : X < 2 * Y := (le_abs_self X).trans_lt this
          rw [hY1def]; linarith
        have hX1pos : 0 < X1 := by
          have : (2 * X) ^ 2 > (3 * Y) ^ 2 := by nlinarith
          have hcmp : |2 * X| > |3 * Y| :=
            lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) (by rwa [sq_abs, sq_abs])
          have : 2 * X > 3 * Y := by
            have e1 : |2 * X| = 2 * X := abs_of_pos (by nlinarith)
            have e2 : |3 * Y| = 3 * Y := abs_of_nonneg (by nlinarith)
            rwa [e1, e2] at hcmp
          rw [hX1def]; linarith
        have hY1lt : Y1 < Y := by
          have : Y < X := by
            have : Y ^ 2 < X ^ 2 := by nlinarith
            exact lt_of_pow_lt_pow_left₀ 2 (le_of_lt hX) this
          rw [hY1def]; linarith
        have hY1abs : Y1.natAbs < N := by
          have e1 : (Y1.natAbs : ℤ) = Y1 := Int.natAbs_of_nonneg hY1pos.le
          have e2 : (Y.natAbs : ℤ) = Y := Int.natAbs_of_nonneg hY.le
          have : (Y1.natAbs : ℤ) < (N : ℤ) := by
            rw [e1, ← hYN, e2]; exact hY1lt
          exact_mod_cast this
        obtain ⟨k, hkX, hkY⟩ := ih Y1.natAbs hY1abs X1 Y1 rfl hX1pos hY1pos hnorm1
        have hXeq : X = 2 * X1 + 3 * Y1 := by rw [hX1def, hY1def]; ring
        have hYeq : Y = X1 + 2 * Y1 := by rw [hX1def, hY1def]; ring
        refine ⟨k + 1, ?_, ?_⟩
        · rw [pellX_succ, ← hkX, ← hkY]; exact hXeq
        · rw [pellY_succ, ← hkX, ← hkY]; exact hYeq
  exact helper Y.natAbs X Y rfl hX hY h


lemma pell_mul3 (n : ℕ) :
    pellX (n + 3) = 26 * pellX n + 45 * pellY n ∧
    pellY (n + 3) = 15 * pellX n + 26 * pellY n := by
  constructor
  · simp [pellX_succ, pellY_succ]; ring
  · simp [pellX_succ, pellY_succ]; ring

def u3 : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | t + 1 =>
    let c := (u3 t).1
    let d := (u3 t).2
    (26 * c + 45 * d, 15 * c + 26 * d)

def u3re (t : ℕ) : ℤ := (u3 t).1
def u3im (t : ℕ) : ℤ := (u3 t).2

lemma u3re_zero : u3re 0 = 1 := rfl
lemma u3im_zero : u3im 0 = 0 := rfl
lemma u3re_succ (t : ℕ) : u3re (t + 1) = 26 * u3re t + 45 * u3im t := rfl
lemma u3im_succ (t : ℕ) : u3im (t + 1) = 15 * u3re t + 26 * u3im t := rfl

lemma u3re_one : u3re 1 = 26 := by simp [u3re_succ, u3im_succ, u3re_zero, u3im_zero]
lemma u3im_one : u3im 1 = 15 := by simp [u3im_succ, u3re_succ, u3re_zero, u3im_zero]

lemma pell_eq_u3 (t : ℕ) :
    pellX (3 * t + 1) = 5 * u3re t + 9 * u3im t ∧
    pellY (3 * t + 1) = 3 * u3re t + 5 * u3im t := by
  induction t with
  | zero =>
    simp [u3re_zero, u3im_zero, pellX_one, pellY_one]
  | succ t ih =>
    have hmul := pell_mul3 (3 * t + 1)
    have heq : 3 * (t + 1) + 1 = 3 * t + 1 + 3 := by ring
    rw [heq]
    constructor
    · rw [hmul.1, ih.1, ih.2, u3re_succ, u3im_succ]; ring
    · rw [hmul.2, ih.1, ih.2, u3re_succ, u3im_succ]; ring

lemma u3im_three_dvd : ∀ t, (3 : ℤ) ∣ u3im t
  | 0 => by simp [u3im_zero]
  | t + 1 => by
    have ih := u3im_three_dvd t
    rw [u3im_succ]
    exact dvd_add (dvd_mul_of_dvd_left (by decide : (3 : ℤ) ∣ 15) _) (dvd_mul_of_dvd_right ih _)

def w27 (t : ℕ) : ℤ := u3re t + 5 * (u3im t / 3)

lemma w27_eq (t : ℕ) : 3 * w27 t = pellY (3 * t + 1) := by
  have h := (pell_eq_u3 t).2
  have hd := u3im_three_dvd t
  simp only [w27]
  rw [h]
  have : 3 * (u3im t / 3) = u3im t := Int.mul_ediv_cancel' hd
  nlinarith

lemma w27_zero : w27 0 = 1 := by
  simp [w27, u3re_zero, u3im_zero]

lemma w27_one : w27 1 = 51 := by
  simp [w27, u3re_one, u3im_one]

lemma u3re_succ2 (n : ℕ) : u3re (n + 2) = 52 * u3re (n + 1) - u3re n := by
  rw [u3re_succ, u3im_succ, u3re_succ]; ring

lemma u3im_succ2 (n : ℕ) : u3im (n + 2) = 52 * u3im (n + 1) - u3im n := by
  rw [u3im_succ, u3re_succ, u3im_succ]; ring

lemma w27_succ2 (t : ℕ) : w27 (t + 2) = 52 * w27 (t + 1) - w27 t := by
  have hd0 := u3im_three_dvd t
  have hd1 := u3im_three_dvd (t + 1)
  have hd2 := u3im_three_dvd (t + 2)
  apply mul_left_cancel₀ (show (3 : ℤ) ≠ 0 from by decide)
  simp only [w27]
  calc
    3 * (u3re (t + 2) + 5 * (u3im (t + 2) / 3))
        = 3 * u3re (t + 2) + 5 * u3im (t + 2) := by
          rw [mul_add, ← mul_assoc]
          have : (3 : ℤ) * 5 * (u3im (t + 2) / 3) = 5 * u3im (t + 2) := by
            rw [mul_comm (3 : ℤ) 5, mul_assoc, Int.mul_ediv_cancel' hd2]
          rw [this]
    _ = 3 * (52 * u3re (t + 1) - u3re t) + 5 * (52 * u3im (t + 1) - u3im t) := by
          rw [u3re_succ2, u3im_succ2]
    _ = 52 * (3 * u3re (t + 1) + 5 * u3im (t + 1)) - (3 * u3re t + 5 * u3im t) := by ring
    _ = 52 * (3 * u3re (t + 1) + 5 * (3 * (u3im (t + 1) / 3)))
          - (3 * u3re t + 5 * (3 * (u3im t / 3))) := by
          rw [Int.mul_ediv_cancel' hd1, Int.mul_ediv_cancel' hd0]
    _ = 3 * (52 * (u3re (t + 1) + 5 * (u3im (t + 1) / 3))
          - (u3re t + 5 * (u3im t / 3))) := by ring


private def wmod17 : ℕ → ZMod 17
  | 0 => 1
  | 1 => 0
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => 1
  | n + 6 => wmod17 n

lemma wmod17_succ2 (n : ℕ) : wmod17 (n + 2) = wmod17 (n + 1) - wmod17 n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | n + 6 =>
    simpa [wmod17] using wmod17_succ2 n

lemma w27_zmod17 (t : ℕ) : (w27 t : ZMod 17) = wmod17 t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    match t with
    | 0 =>
      rw [w27_zero]; rfl
    | 1 =>
      rw [w27_one]; rfl
    | t + 2 =>
      have h0 := ih t (by omega)
      have h1 := ih (t + 1) (by omega)
      have hcast : (w27 (t + 2) : ZMod 17) =
          (52 : ZMod 17) * (w27 (t + 1) : ZMod 17) - (w27 t : ZMod 17) := by
        rw [w27_succ2 t]; norm_cast
      have h52 : (52 : ZMod 17) = 1 := rfl
      rw [hcast, h52, one_mul, h0, h1, wmod17_succ2]

lemma wmod17_eq_zero_iff (t : ℕ) : wmod17 t = 0 ↔ t % 3 = 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    match t with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | t + 6 =>
      have ih' := ih t (by omega)
      have : (t + 6) % 3 = t % 3 := by omega
      simpa [wmod17, this] using ih'

lemma w27_seventeen_of_three_mod (t : ℕ) (ht : t % 3 = 1) : (17 : ℤ) ∣ w27 t := by
  have : (w27 t : ZMod 17) = 0 := by
    rw [w27_zmod17, wmod17_eq_zero_iff, ht]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (w27 t) 17).mp this

private def wmod3 : ℕ → ZMod 3
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | n + 6 => wmod3 n

lemma wmod3_succ2 (n : ℕ) : wmod3 (n + 2) = wmod3 (n + 1) - wmod3 n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | n + 6 =>
    simpa [wmod3] using wmod3_succ2 n

lemma w27_zmod3 (t : ℕ) : (w27 t : ZMod 3) = wmod3 t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    match t with
    | 0 =>
      rw [w27_zero]; rfl
    | 1 =>
      rw [w27_one]; rfl
    | t + 2 =>
      have h0 := ih t (by omega)
      have h1 := ih (t + 1) (by omega)
      have hcast : (w27 (t + 2) : ZMod 3) =
          (52 : ZMod 3) * (w27 (t + 1) : ZMod 3) - (w27 t : ZMod 3) := by
        rw [w27_succ2 t]; norm_cast
      have h52 : (52 : ZMod 3) = 1 := rfl
      rw [hcast, h52, one_mul, h0, h1, wmod3_succ2]

lemma wmod3_eq_zero_iff (t : ℕ) : wmod3 t = 0 ↔ t % 3 = 1 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    match t with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | t + 6 =>
      have ih' := ih t (by omega)
      have : (t + 6) % 3 = t % 3 := by omega
      simpa [wmod3, this] using ih'

lemma w27_three_dvd_iff (t : ℕ) : (3 : ℤ) ∣ w27 t ↔ t % 3 = 1 := by
  have : ((3 : ℕ) : ℤ) ∣ w27 t ↔ (w27 t : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (w27 t) 3).symm
  simpa using this.trans (by rw [w27_zmod3, wmod3_eq_zero_iff])



lemma pellY_strictMono : StrictMono pellY := by
  intro a b hab
  have hjump : ∀ n k, pellY n < pellY (n + k + 1) := by
    intro n k
    induction k with
    | zero => exact pellY_lt_succ n
    | succ k ih =>
      have heq : n + (k + 1) + 1 = n + k + 1 + 1 := by omega
      rw [heq]
      exact lt_trans ih (pellY_lt_succ _)
  have heq : b = a + (b - a - 1) + 1 := by omega
  rw [heq]
  exact hjump a (b - a - 1)

lemma w27_pos (t : ℕ) : 0 < w27 t := by
  have : 0 < pellY (3 * t + 1) := pellY_pos _
  have := w27_eq t
  nlinarith

lemma w27_ne_pow_three {t j : ℕ} (ht : 1 ≤ t) (hw : w27 t = (3 : ℤ) ^ j) : False := by
  have hge : (51 : ℤ) ≤ w27 t := by
    have : pellY 4 ≤ pellY (3 * t + 1) :=
      pellY_strictMono.monotone (by omega : 4 ≤ 3 * t + 1)
    have e1 : 3 * w27 1 = pellY (3 * 1 + 1) := w27_eq 1
    have e2 : 3 * w27 t = pellY (3 * t + 1) := w27_eq t
    have : pellY (3 * 1 + 1) = pellY 4 := rfl
    rw [this, w27_one] at e1
    nlinarith
  have hj0 : j ≠ 0 := by
    intro hj; subst hj; simp at hw; nlinarith
  have h3 : (3 : ℤ) ∣ w27 t := by
    rw [hw]; exact dvd_pow (by decide : (3 : ℤ) ∣ 3) hj0
  have ht1 : t % 3 = 1 := (w27_three_dvd_iff t).mp h3
  have h17 : (17 : ℤ) ∣ w27 t := w27_seventeen_of_three_mod t ht1
  have h17' : (17 : ℤ) ∣ (3 : ℤ) ^ j := by rwa [hw] at h17
  have hpr : Prime (17 : ℤ) := by decide
  have : (17 : ℤ) ∣ 3 := hpr.dvd_of_dvd_pow h17'
  norm_num at this

lemma pellY_eq_pow_three {k m : ℕ} (h : pellY k = (3 : ℤ) ^ m) : k = 0 ∨ k = 1 := by
  by_cases hm : m = 0
  · subst hm
    have hk1 : pellY k = 1 := by simpa using h
    have hk : k = 0 := by
      by_contra hk
      have hlt : pellY 0 < pellY k := pellY_strictMono (by omega : (0 : ℕ) < k)
      rw [pellY_zero, hk1] at hlt
      exact lt_irrefl _ hlt
    exact Or.inl hk
  · have h3 : (3 : ℤ) ∣ pellY k := by
      rw [h]; exact dvd_pow (by decide : (3 : ℤ) ∣ 3) hm
    have hk1 : k % 3 = 1 := (pellY_three_dvd_iff k).mp h3
    obtain ⟨t, rfl⟩ : ∃ t, k = 3 * t + 1 := ⟨k / 3, by omega⟩
    have hw : 3 * w27 t = (3 : ℤ) ^ m := by
      rw [w27_eq, h]
    have hm1 : 1 ≤ m := by omega
    have hwt : w27 t = (3 : ℤ) ^ (m - 1) := by
      apply mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0)
      calc
        (3 : ℤ) * w27 t = (3 : ℤ) ^ m := hw
        _ = (3 : ℤ) ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel hm1]
        _ = (3 : ℤ) * (3 : ℤ) ^ (m - 1) := pow_succ' (3 : ℤ) (m - 1)
    by_cases ht0 : t = 0
    · exact Or.inr (by omega)
    · exact (w27_ne_pow_three (by omega) hwt).elim

lemma not_sq_sub_sq_two {a b : ℤ} (h : a ^ 2 = b ^ 2 + 2) : False := by
  have hab : |b| ≤ |a| := by
    have : b ^ 2 ≤ a ^ 2 := by nlinarith
    rw [← sq_abs a] at this
    exact abs_le_of_sq_le_sq this (abs_nonneg _)
  have hfac : (|a| - |b|) * (|a| + |b|) = 2 := by
    have := sq_sub_sq (|a|) (|b|)
    rw [sq_abs, sq_abs] at this
    nlinarith
  have hpos : 0 ≤ |a| - |b| := sub_nonneg.mpr hab
  have hdvd : |a| - |b| ∣ 2 := ⟨|a| + |b|, by nlinarith⟩
  have hle : |a| - |b| ≤ 2 := Int.le_of_dvd (by decide) hdvd
  have hne : |a| - |b| ≠ 0 := by
    intro hz
    rw [hz] at hfac
    norm_num at hfac
  have : |a| - |b| = 1 ∨ |a| - |b| = 2 := by omega
  rcases this with h1 | h2
  · have : |a| + |b| = 2 := by nlinarith
    omega
  · have : |a| + |b| = 1 := by nlinarith
    omega

lemma three_pow_eq_one {m : ℕ} (h : (3 : ℤ) ^ m = 1) : m = 0 := by
  have : (3 : ℤ) ^ m = (3 : ℤ) ^ 0 := by simpa using h
  exact (pow_right_injective₀ (by decide : (1 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≠ 1)).eq_iff.mp this

lemma three_pow_eq_three {m : ℕ} (h : (3 : ℤ) ^ m = 3) : m = 1 := by
  have : (3 : ℤ) ^ m = (3 : ℤ) ^ 1 := by simpa using h
  exact (pow_right_injective₀ (by decide : (1 : ℤ) ≤ 3) (by decide : (3 : ℤ) ≠ 1)).eq_iff.mp this

theorem sq_add_two_eq_three_pow {x : ℤ} {n : ℕ} (hn : 1 ≤ n)
    (h : x ^ 2 + 2 = (3 : ℤ) ^ n) : n = 1 ∨ n = 3 := by
  by_cases he : Even n
  · obtain ⟨k, hk⟩ := he
    have hpow : (3 : ℤ) ^ n = ((3 : ℤ) ^ k) ^ 2 := by
      rw [hk, show k + k = k * 2 from (two_mul k).symm ▸ (mul_comm 2 k), pow_mul]
    have : ((3 : ℤ) ^ k) ^ 2 = x ^ 2 + 2 := by rw [← hpow, h]
    exact (not_sq_sub_sq_two this).elim
  · have hod : Odd n := Nat.not_even_iff_odd.mp he
    obtain ⟨m, hm⟩ := hod
    have hnexp : (3 : ℤ) ^ n = 3 * ((3 : ℤ) ^ m) ^ 2 := by
      rw [hm]
      calc
        (3 : ℤ) ^ (2 * m + 1) = (3 : ℤ) ^ (2 * m) * 3 := pow_succ _ _
        _ = ((3 : ℤ) ^ 2) ^ m * 3 := by rw [pow_mul]
        _ = ((3 : ℤ) ^ m) ^ 2 * 3 := by
          rw [← pow_mul, ← pow_mul]
          simp [mul_comm]
        _ = 3 * ((3 : ℤ) ^ m) ^ 2 := by ring
    have hPell : x ^ 2 - 3 * ((3 : ℤ) ^ m) ^ 2 = -2 := by
      have : x ^ 2 + 2 = 3 * ((3 : ℤ) ^ m) ^ 2 := by rw [← hnexp, h]
      omega
    have hYpos : 0 < ((3 : ℤ) ^ m) := pow_pos (by decide) m
    have hx0 : x ≠ 0 := by
      intro hx
      subst hx
      have heq : (2 : ℤ) = (3 : ℤ) ^ n := by
        have hh : (0 : ℤ) ^ 2 + 2 = (3 : ℤ) ^ n := h
        simp at hh
        exact hh
      have hn0 : n ≠ 0 := by omega
      have : (3 : ℤ) ∣ 2 := by
        rw [heq]; exact dvd_pow (by decide : (3 : ℤ) ∣ 3) hn0
      norm_num at this
    have hXpos : 0 < |x| := abs_pos.mpr hx0
    have hnorm' : |x| ^ 2 - 3 * ((3 : ℤ) ^ m) ^ 2 = -2 := by
      rw [sq_abs]; exact hPell
    obtain ⟨k, _hkX, hkY⟩ := exists_pell_of_norm hXpos hYpos hnorm'
    have hk01 : k = 0 ∨ k = 1 := pellY_eq_pow_three hkY.symm
    rcases hk01 with rfl | rfl
    · have : (3 : ℤ) ^ m = 1 := by rw [hkY, pellY_zero]
      have : m = 0 := three_pow_eq_one this
      omega
    · have : (3 : ℤ) ^ m = 3 := by rw [hkY, pellY_one]
      have : m = 1 := three_pow_eq_three this
      omega



namespace PellNegTwo


def alpha (r : ℤ) : ℤ√(r ^ 2 + 2) := ⟨r, 1⟩

lemma alpha_norm (r : ℤ) : (alpha r).norm = -2 := by
  simp [alpha, Zsqrtd.norm_def]
  ring

def eps (r : ℤ) : ℤ√(r ^ 2 + 2) := ⟨r ^ 2 + 1, r⟩

lemma eps_norm (r : ℤ) : (eps r).norm = 1 := by
  simp [eps, Zsqrtd.norm_def]
  ring

lemma eps_pow_norm (r : ℤ) : ∀ k : ℕ, ((eps r) ^ k).norm = 1
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ (eps r) k, Zsqrtd.norm_mul, eps_pow_norm r k, eps_norm, mul_one]

def pellZ (r : ℤ) (k : ℕ) : ℤ√(r ^ 2 + 2) := alpha r * (eps r) ^ k

def pX (r : ℤ) (k : ℕ) : ℤ := (pellZ r k).re
def pY (r : ℤ) (k : ℕ) : ℤ := (pellZ r k).im

lemma pX_zero (r : ℤ) : pX r 0 = r := by simp [pX, pellZ, alpha]
lemma pY_zero (r : ℤ) : pY r 0 = 1 := by simp [pY, pellZ, alpha]

lemma pellZ_succ (r : ℤ) (k : ℕ) :
    pellZ r (k + 1) = pellZ r k * eps r := by
  unfold pellZ
  rw [pow_succ (eps r) k, mul_assoc]

lemma pX_succ (r : ℤ) (k : ℕ) :
    pX r (k + 1) = (r ^ 2 + 1) * pX r k + (r ^ 2 + 2) * r * pY r k := by
  unfold pX pY
  rw [pellZ_succ]
  simp [eps]
  ring

lemma pY_succ (r : ℤ) (k : ℕ) :
    pY r (k + 1) = r * pX r k + (r ^ 2 + 1) * pY r k := by
  unfold pX pY
  rw [pellZ_succ]
  simp [eps]
  ring

lemma p_norm (r : ℤ) (k : ℕ) :
    pX r k ^ 2 - (r ^ 2 + 2) * pY r k ^ 2 = -2 := by
  have h : (pellZ r k).norm = -2 := by
    unfold pellZ
    rw [Zsqrtd.norm_mul, alpha_norm, eps_pow_norm, mul_one]
  unfold pX pY
  rw [Zsqrtd.norm_def] at h
  nlinarith

lemma pY_one (r : ℤ) : pY r 1 = 2 * r ^ 2 + 1 := by
  rw [pY_succ, pX_zero, pY_zero]; ring

lemma pX_one (r : ℤ) : pX r 1 = r * (2 * r ^ 2 + 3) := by
  rw [pX_succ, pX_zero, pY_zero]; ring

lemma pY_succ2 (r : ℤ) (k : ℕ) :
    pY r (k + 2) = 2 * (r ^ 2 + 1) * pY r (k + 1) - pY r k := by
  rw [pY_succ, pX_succ, pY_succ]
  ring

lemma p_pos (r : ℤ) (hr : 1 ≤ r) : ∀ k : ℕ, 0 < pX r k ∧ 0 < pY r k
  | 0 => by
    constructor
    · rw [pX_zero]; linarith
    · rw [pY_zero]; norm_num
  | k + 1 => by
    obtain ⟨hx, hy⟩ := p_pos r hr k
    have h1 : 0 < r ^ 2 + 1 := by nlinarith [sq_nonneg r]
    have h2 : 0 < r := by linarith
    have h3 : 0 < r ^ 2 + 2 := by nlinarith [sq_nonneg r]
    constructor
    · rw [pX_succ]
      have a : 0 < (r ^ 2 + 1) * pX r k := mul_pos h1 hx
      have b : 0 < (r ^ 2 + 2) * r * pY r k := mul_pos (mul_pos h3 h2) hy
      linarith
    · rw [pY_succ]
      have a : 0 < r * pX r k := mul_pos h2 hx
      have b : 0 < (r ^ 2 + 1) * pY r k := mul_pos h1 hy
      linarith

lemma pX_pos (r : ℤ) (hr : 1 ≤ r) (k : ℕ) : 0 < pX r k := (p_pos r hr k).1
lemma pY_pos (r : ℤ) (hr : 1 ≤ r) (k : ℕ) : 0 < pY r k := (p_pos r hr k).2

lemma pX_ge (r : ℤ) (hr : 1 ≤ r) (k : ℕ) : r * pY r k ≤ pX r k := by
  have hx := pX_pos r hr k
  have hy := pY_pos r hr k
  have hn := p_norm r k
  have hsq : (r * pY r k) ^ 2 ≤ (pX r k) ^ 2 := by
    nlinarith [sq_nonneg r, sq_nonneg (pY r k)]
  have habs : |r * pY r k| ≤ |pX r k| := by
    have : (r * pY r k) ^ 2 ≤ |pX r k| ^ 2 := by rwa [sq_abs]
    exact abs_le_of_sq_le_sq this (abs_nonneg _)
  have hr0 : 0 ≤ r := by linarith
  rw [abs_of_nonneg (mul_nonneg hr0 (le_of_lt hy)), abs_of_pos hx] at habs
  exact habs

lemma pY_grow (r : ℤ) (hr : 1 ≤ r) (k : ℕ) :
    (2 * r ^ 2 + 1) * pY r k ≤ pY r (k + 1) := by
  have hge := pX_ge r hr k
  rw [pY_succ]
  nlinarith [sq_nonneg r]

lemma pY_pow_lower (r : ℤ) (hr : 1 ≤ r) :
    ∀ k : ℕ, (2 * r ^ 2 + 1 : ℤ) ^ k ≤ pY r k
  | 0 => by simp [pY_zero]
  | k + 1 => by
    have ih := pY_pow_lower r hr k
    have hg := pY_grow r hr k
    have hp : (0 : ℤ) ≤ 2 * r ^ 2 + 1 := by nlinarith [sq_nonneg r]
    calc
      (2 * r ^ 2 + 1 : ℤ) ^ (k + 1)
          = (2 * r ^ 2 + 1) * (2 * r ^ 2 + 1) ^ k := pow_succ' _ _
      _ ≤ (2 * r ^ 2 + 1) * pY r k := mul_le_mul_of_nonneg_left ih hp
      _ ≤ pY r (k + 1) := hg

lemma pY_one_not_q_pow (r : ℤ) (hr : 2 ≤ |r|) {m : ℕ}
    (h : pY r 1 = (r ^ 2 + 2) ^ m) : False := by
  rw [pY_one] at h
  have hr2 : (4 : ℤ) ≤ r ^ 2 := by nlinarith [sq_abs r]
  match m with
  | 0 =>
    have : (2 * r ^ 2 + 1 : ℤ) = 1 := by simpa using h
    nlinarith
  | 1 =>
    have : (2 * r ^ 2 + 1 : ℤ) = r ^ 2 + 2 := by simpa using h
    nlinarith
  | m + 2 =>
    have hge : (r ^ 2 + 2 : ℤ) ^ 2 ≤ (r ^ 2 + 2) ^ (m + 2) :=
      pow_le_pow_right₀ (by nlinarith [sq_nonneg r] : (1 : ℤ) ≤ r ^ 2 + 2) (by omega)
    have hlt : (2 * r ^ 2 + 1 : ℤ) < (r ^ 2 + 2) ^ 2 := by
      have : (r ^ 2 + 2) ^ 2 = r ^ 4 + 4 * r ^ 2 + 4 := by ring
      nlinarith
    nlinarith

lemma two_sigma_mod (r : ℤ) :
    (2 * (r ^ 2 + 1) : ℤ) ≡ -2 [ZMOD r ^ 2 + 2] := by
  refine Int.modEq_iff_dvd.mpr ⟨-2, ?_⟩
  ring

lemma pY_mod_q (r : ℤ) : ∀ k : ℕ,
    pY r k ≡ (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) [ZMOD r ^ 2 + 2]
  | 0 => by simp [pY_zero]
  | 1 => by
    rw [pY_one]
    refine Int.modEq_iff_dvd.mpr ⟨-2, by ring⟩
  | k + 2 => by
    have h0 := pY_mod_q r k
    have h1 := pY_mod_q r (k + 1)
    have hrec := pY_succ2 r k
    have hσ := two_sigma_mod r
    have hstep : pY r (k + 2) ≡
        2 * (r ^ 2 + 1) * pY r (k + 1) - pY r k [ZMOD r ^ 2 + 2] := by
      rw [hrec]
    have hstep2 : pY r (k + 2) ≡
        -2 * pY r (k + 1) - pY r k [ZMOD r ^ 2 + 2] := by
      apply hstep.trans
      exact (hσ.mul_right (pY r (k + 1))).sub (Int.ModEq.refl (pY r k))
    have hstep3 : pY r (k + 2) ≡
        -2 * ((-1 : ℤ) ^ (k + 1) * (2 * ((k + 1 : ℕ) : ℤ) + 1))
          - ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1)) [ZMOD r ^ 2 + 2] := by
      apply hstep2.trans
      exact ((Int.ModEq.refl (-2 : ℤ)).mul h1).sub h0
    have hid : (-2 : ℤ) * ((-1 : ℤ) ^ (k + 1) * (2 * ((k + 1 : ℕ) : ℤ) + 1))
        - ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1))
        = (-1 : ℤ) ^ (k + 2) * (2 * ((k + 2 : ℕ) : ℤ) + 1) := by
      have hneg : (-1 : ℤ) ^ (k + 1) = - ((-1 : ℤ) ^ k) := by
        rw [pow_succ]; ring
      have hneg2 : (-1 : ℤ) ^ (k + 2) = (-1 : ℤ) ^ k := by
        rw [pow_add, pow_two]; ring
      rw [hneg, hneg2]
      push_cast
      ring
    rwa [hid] at hstep3

lemma q_dvd_two_k_add_one (r : ℤ) (k : ℕ)
    (hdvd : r ^ 2 + 2 ∣ pY r k) :
    r ^ 2 + 2 ∣ (2 * (k : ℤ) + 1) := by
  have hcong := pY_mod_q r k
  have h0 : pY r k ≡ 0 [ZMOD r ^ 2 + 2] := Int.modEq_zero_iff_dvd.mpr hdvd
  have hmul : (0 : ℤ) ≡ (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) [ZMOD r ^ 2 + 2] :=
    h0.symm.trans hcong
  have hd : r ^ 2 + 2 ∣ (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) :=
    Int.modEq_zero_iff_dvd.mp hmul.symm
  have hunit : IsUnit ((-1 : ℤ) ^ k) := IsUnit.pow _ isUnit_neg_one
  exact (hunit.dvd_mul_left).mp hd


/-- Multiplying by `ε̄ = ⟨r²+1, -r⟩` inverts a step. -/
def epsBar (r : ℤ) : ℤ√(r ^ 2 + 2) := ⟨r ^ 2 + 1, -r⟩

lemma eps_mul_epsBar (r : ℤ) : eps r * epsBar r = 1 := by
  ext <;> (simp [eps, epsBar]; ring)

lemma pellZ_mul_epsBar (r : ℤ) (k : ℕ) :
    pellZ r (k + 1) * epsBar r = pellZ r k := by
  rw [pellZ_succ, mul_assoc, eps_mul_epsBar, mul_one]

def descX (r X Y : ℤ) : ℤ := (r ^ 2 + 1) * X - (r ^ 2 + 2) * r * Y
def descY (r X Y : ℤ) : ℤ := (r ^ 2 + 1) * Y - r * X

lemma desc_norm (r X Y : ℤ)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    descX r X Y ^ 2 - (r ^ 2 + 2) * descY r X Y ^ 2 = -2 := by
  simp only [descX, descY]
  nlinarith

lemma descY_pos (r X Y : ℤ) (hr : 1 ≤ r) (hY : 1 < Y) (hX : 0 < X)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    0 < descY r X Y := by
  -- equivalent to r X < (r²+1) Y
  have hcmp : (r * X) ^ 2 < ((r ^ 2 + 1) * Y) ^ 2 := by
    have : (r ^ 2 + 2) * r ^ 2 < (r ^ 2 + 1) ^ 2 := by
      have hrpos : (0 : ℤ) < r := by linarith
      nlinarith [sq_pos_of_pos hrpos]
    nlinarith
  have habs : |r * X| < |(r ^ 2 + 1) * Y| := by
    refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
    rwa [sq_abs, sq_abs]
  have ha : |r * X| = r * X :=
    abs_of_nonneg (mul_nonneg (by linarith) (le_of_lt hX))
  have hb : |(r ^ 2 + 1) * Y| = (r ^ 2 + 1) * Y :=
    abs_of_nonneg (mul_nonneg (by nlinarith [sq_nonneg r]) (by linarith))
  simp only [descY]
  linarith

lemma descY_lt (r X Y : ℤ) (hr : 1 ≤ r) (hY : 1 < Y) (hX : 0 < X)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    descY r X Y < Y := by
  have hgt : r * Y < X := by
    have hsq : (r * Y) ^ 2 < X ^ 2 := by nlinarith
    have habs : |r * Y| < |X| := by
      refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
      rwa [sq_abs, sq_abs]
    have hr0 : 0 ≤ r := by linarith
    have hY0 : 0 ≤ Y := by linarith
    rwa [abs_of_nonneg (mul_nonneg hr0 hY0), abs_of_pos hX] at habs
  simp only [descY]
  nlinarith [sq_nonneg r]

lemma not_sq_seven {z : ℤ} (h : z ^ 2 = 7) : False := by
  have habs : |z| ≤ 3 := by
    have : z ^ 2 ≤ (3 : ℤ) ^ 2 := by norm_num [h]
    exact abs_le_of_sq_le_sq this (by decide)
  have hnn : 0 ≤ |z| := abs_nonneg _
  have : |z| = 0 ∨ |z| = 1 ∨ |z| = 2 ∨ |z| = 3 := by omega
  rcases this with h0 | h1 | h2 | h3
  · rw [abs_eq_zero] at h0; subst h0; norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h2 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h3 with rfl | rfl <;> norm_num at h

lemma not_sq_ten {z : ℤ} (h : z ^ 2 = 10) : False := by
  have habs : |z| ≤ 4 := by
    have : z ^ 2 ≤ (4 : ℤ) ^ 2 := by norm_num [h]
    exact abs_le_of_sq_le_sq this (by decide)
  have hnn : 0 ≤ |z| := abs_nonneg _
  have : |z| = 0 ∨ |z| = 1 ∨ |z| = 2 ∨ |z| = 3 ∨ |z| = 4 := by omega
  rcases this with h0 | h1 | h2 | h3 | h4
  · rw [abs_eq_zero] at h0; subst h0; norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h2 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h3 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h4 with rfl | rfl <;> norm_num at h

lemma descX_pos (r X Y : ℤ) (hr : 1 ≤ r) (hY : 1 < Y) (hX : 0 < X)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    0 < descX r X Y := by
  -- Split on whether Y ≥ 2r or Y < 2r
  by_cases hbig : (2 * r : ℤ) ≤ Y
  · -- (σ X)² - (r q Y)² = X² - 2 r² q > 0 when Y ≥ 2r
    have hdiff :
        (r ^ 2 + 1) ^ 2 * X ^ 2 - (r * (r ^ 2 + 2) * Y) ^ 2
          = X ^ 2 - 2 * r ^ 2 * (r ^ 2 + 2) := by
      have : X ^ 2 = (r ^ 2 + 2) * Y ^ 2 - 2 := by nlinarith
      rw [this]; ring
    have hposd : (0 : ℤ) < X ^ 2 - 2 * r ^ 2 * (r ^ 2 + 2) := by
      have : X ^ 2 = (r ^ 2 + 2) * Y ^ 2 - 2 := by nlinarith
      rw [this]
      have : (4 : ℤ) * r ^ 2 ≤ Y ^ 2 := by
        nlinarith [sq_nonneg (Y - 2 * r), hr]
      nlinarith [sq_nonneg r, hr]
    have : |(r * (r ^ 2 + 2) * Y)| < |(r ^ 2 + 1) * X| := by
      refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
      rw [sq_abs, sq_abs]
      nlinarith
    have ha : |r * (r ^ 2 + 2) * Y| = r * (r ^ 2 + 2) * Y :=
      abs_of_nonneg (by nlinarith [hr, hY, sq_nonneg r])
    have hb : |(r ^ 2 + 1) * X| = (r ^ 2 + 1) * X :=
      abs_of_nonneg (by nlinarith [hX, sq_nonneg r])
    simp only [descX]
    linarith
  · -- 1 < Y < 2r: then X = rY+1 and r²+6 is a square, impossible
    have hYlt : Y < 2 * r := by omega
    have hXgt : r * Y < X := by
      have hsq : (r * Y) ^ 2 < X ^ 2 := by nlinarith
      have habs : |r * Y| < |X| := by
        refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
        rwa [sq_abs, sq_abs]
      have hr0 : 0 ≤ r := by linarith
      have hY0 : 0 ≤ Y := by linarith
      rwa [abs_of_nonneg (mul_nonneg hr0 hY0), abs_of_pos hX] at habs
    have hXge : r * Y + 1 ≤ X := by omega
    have hXlt2 : X ≤ r * Y + 1 := by
      have : X ^ 2 < (r * Y + 2) ^ 2 := by
        have hx2 : X ^ 2 = r ^ 2 * Y ^ 2 + 2 * Y ^ 2 - 2 := by nlinarith
        have : (r * Y + 2) ^ 2 = r ^ 2 * Y ^ 2 + 4 * r * Y + 4 := by ring
        nlinarith [sq_nonneg (Y - r), hr]
      have : |X| < |r * Y + 2| :=
        lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) (by rwa [sq_abs, sq_abs])
      have : X < r * Y + 2 := by
        rwa [abs_of_pos hX, abs_of_pos (by nlinarith [hr, hY])] at this
      omega
    have hXeq : X = r * Y + 1 := by omega
    have heq : 2 * Y ^ 2 - 2 = 2 * r * Y + 1 := by
      have : X ^ 2 = r ^ 2 * Y ^ 2 + 2 * Y ^ 2 - 2 := by nlinarith
      have : (r * Y + 1) ^ 2 = r ^ 2 * Y ^ 2 + 2 * r * Y + 1 := by ring
      nlinarith
    have hdisc : (2 * Y - r) ^ 2 = r ^ 2 + 6 := by nlinarith
    -- r²+6 is strictly between r² and (r+1)² for r ≥ 3, and not square for r=1,2
    have hup : r ^ 2 + 6 < (r + 1) ^ 2 ∨ r = 1 ∨ r = 2 := by
      by_cases h1 : r = 1
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : r = 2
        · exact Or.inr (Or.inr h2)
        · left
          have : (3 : ℤ) ≤ r := by omega
          nlinarith
    rcases hup with hup | rfl | rfl
    · have : r < |2 * Y - r| := by
        have : r ^ 2 < (2 * Y - r) ^ 2 := by nlinarith
        have habs : |r| < |2 * Y - r| := by
          refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
          rwa [sq_abs, sq_abs]
        rwa [abs_of_nonneg (by linarith : (0 : ℤ) ≤ r)] at habs
      have : |2 * Y - r| ≤ r := by
        have : (2 * Y - r) ^ 2 < (r + 1) ^ 2 := by nlinarith
        have habs : |2 * Y - r| < |r + 1| :=
          lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) (by rwa [sq_abs, sq_abs])
        have : |2 * Y - r| < r + 1 := by
          rwa [abs_of_pos (by linarith : (0 : ℤ) < r + 1)] at habs
        omega
      omega
    · -- r = 1: 1 < Y < 2, impossible
      omega
    · -- r = 2: 1 < Y < 4, so Y = 2 or 3
      have : Y = 2 ∨ Y = 3 := by omega
      rcases this with rfl | rfl
      · -- X^2 - 6*4 = -2 ⇒ X^2 = 22, not a square. Use X = 2*2+1 = 5 from hXeq
        have : X = 5 := by omega
        subst this
        norm_num at h
      · have : X = 7 := by omega
        subst this
        norm_num at h

lemma exists_pSol (r X Y : ℤ) (hr : 1 ≤ r) (hX : 0 < X) (hY : 0 < Y)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    ∃ k, X = pX r k ∧ Y = pY r k := by
  have helper : ∀ (N : ℕ) (X Y : ℤ), Y.natAbs = N → 0 < X → 0 < Y →
      X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2 →
      ∃ k, X = pX r k ∧ Y = pY r k := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X Y hYN hX hY h
      by_cases hY1 : Y = 1
      · subst hY1
        have : X ^ 2 = r ^ 2 := by nlinarith
        have hXr : X = r ∨ X = -r := (sq_eq_sq_iff_eq_or_eq_neg).mp (by nlinarith)
        rcases hXr with hXr | hXr
        · exact ⟨0, hXr.trans (pX_zero r).symm, (pY_zero r).symm⟩
        · rw [hXr] at hX
          exact (lt_irrefl _ (hX.trans_le (by linarith))).elim
      · have hYge : (2 : ℤ) ≤ Y := by omega
        set X1 := descX r X Y
        set Y1 := descY r X Y
        have hN1 := desc_norm r X Y h
        have hY1pos : 0 < Y1 := descY_pos r X Y hr (by omega) hX h
        have hX1pos : 0 < X1 := descX_pos r X Y hr (by omega) hX h
        have hY1lt : Y1 < Y := descY_lt r X Y hr (by omega) hX h
        have hY1abs : Y1.natAbs < N := by
          have e1 : (Y1.natAbs : ℤ) = Y1 := Int.natAbs_of_nonneg hY1pos.le
          have e2 : (Y.natAbs : ℤ) = Y := Int.natAbs_of_nonneg hY.le
          have : (Y1.natAbs : ℤ) < (N : ℤ) := by
            rw [e1, ← hYN, e2]; exact hY1lt
          exact_mod_cast this
        obtain ⟨k, hkX, hkY⟩ := ih Y1.natAbs hY1abs X1 Y1 rfl hX1pos hY1pos hN1
        refine ⟨k + 1, ?_, ?_⟩
        · -- successor inverts descent
          have hinvX : (r ^ 2 + 1) * descX r X Y + (r ^ 2 + 2) * r * descY r X Y = X := by
            simp only [descX, descY]; ring
          rw [pX_succ, ← hkX, ← hkY]
          simpa [X1, Y1] using hinvX.symm
        · have hinvY : r * descX r X Y + (r ^ 2 + 1) * descY r X Y = Y := by
            simp only [descX, descY]; ring
          rw [pY_succ, ← hkX, ← hkY]
          simpa [X1, Y1] using hinvY.symm
  exact helper Y.natAbs X Y rfl hX hY h


set_option linter.unusedVariables false

lemma two_eps_eq_alpha_sq (r : ℤ) :
    (2 : ℤ√(r ^ 2 + 2)) * eps r = alpha r * alpha r := by
  ext
  · simp [eps, alpha]; ring
  · simp [eps, alpha]; ring

lemma two_pow_eps_pow (r : ℤ) : ∀ k : ℕ,
    (2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k = (alpha r) ^ (2 * k)
  | 0 => by simp
  | k + 1 => by
    have ih := two_pow_eps_pow r k
    have h2 : (2 : ℤ√(r ^ 2 + 2)) ^ (k + 1) =
        (2 : ℤ√(r ^ 2 + 2)) ^ k * 2 :=
      pow_succ (2 : ℤ√(r ^ 2 + 2)) k
    have he : (eps r) ^ (k + 1) = (eps r) ^ k * eps r :=
      pow_succ (eps r) k
    rw [h2, he]
    calc
      (2 : ℤ√(r ^ 2 + 2)) ^ k * 2 * ((eps r) ^ k * eps r)
          = ((2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k) * (2 * eps r) := by ring
      _ = (alpha r) ^ (2 * k) * (alpha r * alpha r) := by
            rw [ih, two_eps_eq_alpha_sq]
      _ = (alpha r) ^ (2 * (k + 1)) := by
            have hsq : alpha r * alpha r = (alpha r) ^ 2 := (pow_two (alpha r)).symm
            rw [hsq, ← pow_add (alpha r) (2 * k) 2]
            rfl

lemma two_pow_pellZ (r : ℤ) (k : ℕ) :
    (2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k = (alpha r) ^ (2 * k + 1) := by
  unfold pellZ
  have h := two_pow_eps_pow r k
  calc
    (2 : ℤ√(r ^ 2 + 2)) ^ k * (alpha r * (eps r) ^ k)
        = alpha r * ((2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k) := by ring
    _ = alpha r * (alpha r) ^ (2 * k) := by rw [h]
    _ = (alpha r) ^ (2 * k + 1) := (pow_succ' (alpha r) (2 * k)).symm

lemma omega_pow_even (d : ℤ) : ∀ t : ℕ,
    ((⟨0, 1⟩ : ℤ√d) ^ (2 * t)) = ⟨d ^ t, 0⟩
  | 0 => by
    ext
    · simp
    · simp
  | t + 1 => by
    have ih := omega_pow_even d t
    have h2 : ((⟨0, 1⟩ : ℤ√d) ^ 2) = ⟨d, 0⟩ := by
      ext <;> simp [pow_two]
    have hmul : (⟨0, 1⟩ : ℤ√d) ^ (2 * (t + 1)) =
        (⟨0, 1⟩ : ℤ√d) ^ (2 * t) * (⟨0, 1⟩ : ℤ√d) ^ 2 := by
      rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add (⟨0, 1⟩ : ℤ√d) (2 * t) 2]
    rw [hmul, ih, h2]
    ext <;> simp [pow_succ]

lemma omega_pow_odd (d : ℤ) (t : ℕ) :
    ((⟨0, 1⟩ : ℤ√d) ^ (2 * t + 1)) = ⟨0, d ^ t⟩ := by
  rw [pow_succ (⟨0, 1⟩ : ℤ√d) (2 * t), omega_pow_even]
  ext <;> simp

lemma alpha_eq_add (r : ℤ) :
    alpha r = (r : ℤ√(r ^ 2 + 2)) + ⟨0, 1⟩ := by
  ext <;> simp [alpha]

lemma intCast_pow (d a : ℤ) : ∀ n : ℕ,
    (a : ℤ√d) ^ n = ⟨a ^ n, 0⟩
  | 0 => by ext <;> simp
  | n + 1 => by
    rw [pow_succ (a : ℤ√d) n, intCast_pow d a n]
    ext <;> simp [pow_succ]

lemma im_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ m ∈ s, f m).im = ∑ m ∈ s, (f m).im := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Zsqrtd.im_add, ih]


/-- Term in the expansion of `Im((r+√q)^{2k+1})`, indexed by the power of `r`. -/
def binomTerm (r : ℤ) (k j : ℕ) : ℤ :=
  (Nat.choose (2 * k + 1) (2 * j) : ℤ) * r ^ (2 * j) * (r ^ 2 + 2) ^ (k - j)

lemma mul_intCast_omega_odd_im (r : ℤ) (m t : ℕ) :
    (((r : ℤ√(r ^ 2 + 2)) ^ m) * ((⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * t + 1))).im =
      r ^ m * (r ^ 2 + 2) ^ t := by
  rw [intCast_pow, omega_pow_odd, Zsqrtd.im_mul]
  simp

lemma mul_intCast_omega_even_im (r : ℤ) (m t : ℕ) :
    (((r : ℤ√(r ^ 2 + 2)) ^ m) * ((⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * t))).im = 0 := by
  rw [intCast_pow, omega_pow_even, Zsqrtd.im_mul]
  simp

lemma im_mul_intCast {d : ℤ} (z : ℤ√d) (n : ℤ) :
    (z * (n : ℤ√d)).im = z.im * n := by
  rw [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]
  ring

lemma odd_sub_even {n m : ℕ} (hn : Odd n) (hm : Even m) (hle : m ≤ n) : Odd (n - m) := by
  rw [← Nat.not_even_iff_odd, Nat.even_sub hle]
  intro hiff
  have : Even n := hiff.mpr hm
  exact Nat.not_odd_iff_even.mpr this hn

lemma even_odd_sub_odd {n m : ℕ} (hn : Odd n) (hm : Odd m) (hle : m ≤ n) : Even (n - m) := by
  rw [Nat.even_sub hle]
  exact iff_of_false (Nat.not_even_iff_odd.mpr hn) (Nat.not_even_iff_odd.mpr hm)

lemma even_iff_two_mul {n : ℕ} : Even n ↔ ∃ j, n = 2 * j := by
  constructor
  · intro ⟨j, hj⟩
    exact ⟨j, by rw [two_mul]; exact hj⟩
  · rintro ⟨j, rfl⟩
    exact even_two_mul j

lemma alpha_pow_im_as_sum_aux (r : ℤ) (k : ℕ) :
    ((alpha r) ^ (2 * k + 1)).im =
      ∑ m ∈ Finset.range (2 * k + 2),
        (if Even m then
          (Nat.choose (2 * k + 1) m : ℤ) * r ^ m * (r ^ 2 + 2) ^ ((2 * k + 1 - m) / 2)
        else 0) := by
  rw [alpha_eq_add, add_pow, im_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmle : m ≤ 2 * k + 1 := by
    simp [Finset.mem_range] at hm; omega
  have hC :
      (((r : ℤ√(r ^ 2 + 2)) ^ m *
        (⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * k + 1 - m) *
        ((2 * k + 1).choose m : ℤ√(r ^ 2 + 2)))).im =
      (((r : ℤ√(r ^ 2 + 2)) ^ m *
        (⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * k + 1 - m))).im *
        ((2 * k + 1).choose m : ℤ) :=
    im_mul_intCast _ _
  rw [hC]
  by_cases he : Even m
  · have hodd : Odd (2 * k + 1 - m) :=
      odd_sub_even ⟨k, by ring⟩ he hmle
    obtain ⟨t, ht⟩ := hodd
    have ht' : 2 * k + 1 - m = 2 * t + 1 := by omega
    rw [if_pos he, ht', mul_intCast_omega_odd_im]
    have : (2 * t + 1) / 2 = t := by omega
    rw [this]
    ring
  · have hev : Even (2 * k + 1 - m) :=
      even_odd_sub_odd ⟨k, by ring⟩ (Nat.not_even_iff_odd.mp he) hmle
    obtain ⟨t, ht⟩ := even_iff_two_mul.mp hev
    rw [if_neg he, ht, mul_intCast_omega_even_im, zero_mul]

lemma even_filter_range (k : ℕ) :
    (Finset.range (2 * k + 2)).filter Even =
      (Finset.range (k + 1)).image (fun j => 2 * j) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · intro ⟨hm, he⟩
    obtain ⟨j, hj⟩ := even_iff_two_mul.mp he
    exact ⟨j, by omega, hj.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨by omega, even_two_mul j⟩

lemma alpha_pow_im_odd (r : ℤ) (k : ℕ) :
    ((alpha r) ^ (2 * k + 1)).im =
      ∑ j ∈ Finset.range (k + 1), binomTerm r k j := by
  rw [alpha_pow_im_as_sum_aux]
  rw [← Finset.sum_filter_add_sum_filter_not (p := Even)]
  have hodd :
      ∑ m ∈ (Finset.range (2 * k + 2)).filter (fun m => ¬ Even m),
          (if Even m then
            (Nat.choose (2 * k + 1) m : ℤ) * r ^ m * (r ^ 2 + 2) ^ ((2 * k + 1 - m) / 2)
          else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have : ¬ Even m := (Finset.mem_filter.mp hm).2
    simp [this]
  have hinj : Set.InjOn (fun j : ℕ => 2 * j) (Finset.range (k + 1) : Set ℕ) := by
    intro x _hx y _hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hxy
  rw [hodd, add_zero, even_filter_range, Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have he : Even (2 * j) := even_two_mul j
  simp only [if_pos he]
  have hdiv : (2 * k + 1 - 2 * j) / 2 = k - j := by
    have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    omega
  simp [binomTerm, hdiv]

lemma two_pow_pY_eq_sum (r : ℤ) (k : ℕ) :
    (2 : ℤ) ^ k * pY r k = ∑ j ∈ Finset.range (k + 1), binomTerm r k j := by
  have h := two_pow_pellZ r k
  have him : ((2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k).im = ((alpha r) ^ (2 * k + 1)).im := by
    rw [h]
  have h2 : ((2 : ℤ√(r ^ 2 + 2)) ^ k) = ⟨(2 : ℤ) ^ k, 0⟩ := by
    simpa using intCast_pow (r ^ 2 + 2) 2 k
  have him2 : ((2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k).im = (2 : ℤ) ^ k * pY r k := by
    rw [h2, Zsqrtd.im_mul]
    simp [pY]
  rw [← him2, him, alpha_pow_im_odd]


/-! `q`-adic valuation of the binomial terms. -/

lemma choose_mul_succ_identity (k t : ℕ) (ht : t ≤ k) :
    (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) =
      (2 * k + 1 : ℤ) * Nat.choose (2 * k) (2 * t) := by
  have h1 : 2 * t + 1 ≤ 2 * k + 1 := by omega
  have hA := Nat.choose_mul_factorial_mul_factorial h1
  have h2 : 2 * t ≤ 2 * k := by omega
  have hB := Nat.choose_mul_factorial_mul_factorial h2
  have hfact : (2 * t + 1).factorial = (2 * t + 1) * (2 * t).factorial :=
    Nat.factorial_succ (2 * t)
  have hfact2 : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial :=
    Nat.factorial_succ (2 * k)
  have hsub : (2 * k + 1 - (2 * t + 1)) = 2 * k - 2 * t := by omega
  rw [hsub] at hA
  zify at hA hB hfact hfact2
  have hpos : ((2 * t).factorial : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (2 * t))
  have hpos2 : ((2 * k - 2 * t).factorial : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero _)
  have hA' :
      (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) * (2 * t).factorial *
        (2 * k - 2 * t).factorial =
      (2 * k + 1 : ℤ) * (2 * k).factorial := by
    calc
      (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) * (2 * t).factorial *
          (2 * k - 2 * t).factorial
        = (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * ((2 * t + 1).factorial) *
            (2 * k - 2 * t).factorial := by
              rw [hfact]; ring
      _ = (2 * k + 1).factorial := by
            simpa [mul_assoc] using hA
      _ = (2 * k + 1 : ℤ) * (2 * k).factorial := hfact2
  have hB' :
      (Nat.choose (2 * k) (2 * t) : ℤ) * (2 * t).factorial * (2 * k - 2 * t).factorial =
        (2 * k).factorial := hB
  have hnz : ((2 * t).factorial : ℤ) * (2 * k - 2 * t).factorial ≠ 0 :=
    mul_ne_zero hpos hpos2
  apply mul_right_cancel₀ hnz
  calc
    (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) *
        ((2 * t).factorial * (2 * k - 2 * t).factorial)
      = (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) * (2 * t).factorial *
          (2 * k - 2 * t).factorial := by ring
    _ = (2 * k + 1 : ℤ) * (2 * k).factorial := hA'
    _ = (2 * k + 1 : ℤ) * ((Nat.choose (2 * k) (2 * t) : ℤ) * (2 * t).factorial *
          (2 * k - 2 * t).factorial) := by rw [hB']
    _ = (2 * k + 1 : ℤ) * Nat.choose (2 * k) (2 * t) *
          ((2 * t).factorial * (2 * k - 2 * t).factorial) := by ring

lemma q_pow_gt_two_j_add_one {q j : ℕ} (hq : 5 ≤ q) (hj : 1 ≤ j) :
    2 * j + 1 < q ^ j := by
  match j with
  | 0 => omega
  | 1 =>
    have : 3 < q := by omega
    simpa using this
  | j + 2 =>
    have hge : (5 : ℕ) ^ (j + 2) ≤ q ^ (j + 2) :=
      Nat.pow_le_pow_left hq (j + 2)
    have h5 : ∀ n : ℕ, 2 * (n + 2) + 1 < 5 ^ (n + 2) := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
        have hA : 2 * (n + 1 + 2) + 1 = 2 * (n + 2) + 1 + 2 := by omega
        have hB : 5 ^ (n + 1 + 2) = 5 * 5 ^ (n + 2) := pow_succ' 5 (n + 2)
        have hC : 2 * (n + 2) + 1 + 2 < 5 ^ (n + 2) + 2 := by omega
        have hD : 5 ^ (n + 2) + 2 ≤ 5 ^ (n + 2) + 5 ^ (n + 2) := by
          have : (2 : ℕ) ≤ 5 ^ (n + 2) := by
            have : 1 ≤ 5 ^ (n + 2) := Nat.one_le_pow _ _ (by decide)
            have : 5 ^ (n + 2) ≥ 5 := Nat.le_trans (by decide : 5 ≤ 25)
              (Nat.pow_le_pow_right (by decide : 1 ≤ 5) (by omega : 2 ≤ n + 2))
            omega
          omega
        have hE : 5 ^ (n + 2) + 5 ^ (n + 2) = 2 * 5 ^ (n + 2) := by ring
        have hF : 2 * 5 ^ (n + 2) ≤ 5 * 5 ^ (n + 2) :=
          Nat.mul_le_mul_right _ (by decide : 2 ≤ 5)
        omega
    have := h5 j
    omega

lemma not_pow_dvd_two_j_add_one {q j : ℕ} (hq : 5 ≤ q) (hj : 1 ≤ j) :
    ¬ (q : ℤ) ^ j ∣ (2 * (j : ℤ) + 1) := by
  intro h
  have hpos : (0 : ℤ) < 2 * (j : ℤ) + 1 := by
    have : (0 : ℤ) ≤ (j : ℤ) := Nat.cast_nonneg _
    linarith
  have hle : (q : ℤ) ^ j ≤ 2 * (j : ℤ) + 1 := Int.le_of_dvd hpos h
  have hlt : 2 * j + 1 < q ^ j := q_pow_gt_two_j_add_one hq hj
  have hlt' : (2 * (j : ℤ) + 1) < (q : ℤ) ^ j := by exact_mod_cast hlt
  linarith


lemma binomTerm_last (r : ℤ) (k : ℕ) :
    binomTerm r k k = (2 * k + 1 : ℤ) * r ^ (2 * k) := by
  unfold binomTerm
  have : (2 * k + 1).choose (2 * k) = 2 * k + 1 := by
    simpa [Nat.choose_symm (by omega : 2 * k ≤ 2 * k + 1)] using
      (Nat.choose_succ_self_right (2 * k))
  simp [this]

lemma binomTerm_ne_zero (r : ℤ) (hr : r ≠ 0) (k j : ℕ) (hj : j ≤ k) :
    binomTerm r k j ≠ 0 := by
  unfold binomTerm
  have hch : (Nat.choose (2 * k + 1) (2 * j) : ℤ) ≠ 0 := by
    have : 2 * j ≤ 2 * k + 1 := by omega
    exact_mod_cast (Nat.choose_pos this).ne'
  have hr0 : r ^ (2 * j) ≠ 0 := pow_ne_zero _ hr
  have hq : (r ^ 2 + 2 : ℤ) ^ (k - j) ≠ 0 := by
    have : (r ^ 2 + 2 : ℤ) ≠ 0 := by nlinarith [sq_nonneg r]
    exact pow_ne_zero _ this
  exact mul_ne_zero (mul_ne_zero hch hr0) hq

lemma padicValInt_pow_of_prime {q : ℕ} [Fact q.Prime] (n : ℕ) :
    padicValInt q ((q : ℤ) ^ n) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicValInt.mul (by
      exact_mod_cast (pow_ne_zero n (NeZero.ne q))) (by
      exact_mod_cast (Nat.Prime.ne_zero Fact.out)), ih, padicValInt_self]

lemma r_not_dvd_of_q_odd {r : ℤ} {q : ℕ} (hq : (q : ℤ) = r ^ 2 + 2)
    (hqp : Nat.Prime q) (hodd : Odd q) : ¬ (q : ℤ) ∣ r := by
  intro h
  have hq2 : (q : ℤ) ∣ r ^ 2 + 2 := by rw [hq]
  have hr2 : (q : ℤ) ∣ r ^ 2 := dvd_pow h (by decide)
  have : (q : ℤ) ∣ 2 := (dvd_add_right hr2).mp hq2
  have : (q : ℕ) ∣ 2 := by exact_mod_cast this
  have h12 : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp this
  rcases h12 with h1 | h2
  · exact hqp.ne_one h1
  · rw [h2] at hodd
    exact Nat.not_odd_iff_even.mpr (by decide) hodd

lemma padicVal_r_pow {r : ℤ} {q n : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q) :
    padicValInt q (r ^ n) = 0 := by
  have hnd : ¬ (q : ℤ) ∣ r := r_not_dvd_of_q_odd hq Fact.out hodd
  have : padicValInt q r = 0 := padicValInt.eq_zero_of_not_dvd hnd
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicValInt.mul (pow_ne_zero n hr) hr, ih, this]

lemma padicVal_binomTerm_last {r : ℤ} {q k : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q) :
    padicValInt q (binomTerm r k k) = padicValInt q (2 * (k : ℤ) + 1) := by
  rw [binomTerm_last]
  have h1 : (2 * (k : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have h2 : r ^ (2 * k) ≠ 0 := pow_ne_zero _ hr
  rw [padicValInt.mul h1 h2, padicVal_r_pow (n := 2 * k) hq hr hodd, add_zero]

lemma padic_two_j_lt {q j : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (hj : 1 ≤ j) :
    padicValInt q (2 * (j : ℤ) + 1) < j := by
  by_contra h
  have : j ≤ padicValInt q (2 * (j : ℤ) + 1) := Nat.le_of_not_gt h
  have hdvd : (q : ℤ) ^ j ∣ (2 * (j : ℤ) + 1) := by
    have hne : (2 * (j : ℤ) + 1) ≠ 0 := by
      have : (0 : ℤ) ≤ (j : ℤ) := Nat.cast_nonneg _
      linarith
    rw [padicValInt_dvd_iff]
    exact Or.inr this
  exact not_pow_dvd_two_j_add_one hq hj hdvd

lemma padicVal_binomTerm_lt {r : ℤ} {q k j : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q)
    (hq5 : 5 ≤ q) (hj : j < k) :
    padicValInt q (2 * (k : ℤ) + 1) < padicValInt q (binomTerm r k j) := by
  have hjk : j ≤ k := Nat.le_of_lt hj
  set s := k - j
  have hs1 : 1 ≤ s := by omega
  have hch : (2 * k + 1).choose (2 * j) = (2 * k + 1).choose (2 * s + 1) := by
    have : 2 * j + (2 * s + 1) = 2 * k + 1 := by omega
    exact Nat.choose_symm_of_eq_add this.symm
  have hid := choose_mul_succ_identity k s (by omega)
  have hCne : (Nat.choose (2 * k + 1) (2 * s + 1) : ℤ) ≠ 0 := by
    have : 2 * s + 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast (Nat.choose_pos this).ne'
  have h2s : (2 * (s : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (s : ℤ) := Nat.cast_nonneg _
    linarith
  have h2k : (2 * (k : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have hC2 : (Nat.choose (2 * k) (2 * s) : ℤ) ≠ 0 := by
    have : 2 * s ≤ 2 * k := by omega
    exact_mod_cast (Nat.choose_pos this).ne'
  have hvsum :
      padicValInt q ((Nat.choose (2 * k + 1) (2 * s + 1) : ℤ)) +
        padicValInt q (2 * (s : ℤ) + 1) =
      padicValInt q (2 * (k : ℤ) + 1) +
        padicValInt q (Nat.choose (2 * k) (2 * s) : ℤ) := by
    have := congrArg (padicValInt q) hid
    rw [padicValInt.mul hCne h2s, padicValInt.mul h2k hC2] at this
    exact this
  have hr0 : padicValInt q (r ^ (2 * j)) = 0 :=
    padicVal_r_pow (n := 2 * j) hq hr hodd
  have hqeq : (r ^ 2 + 2 : ℤ) = q := hq.symm
  have hqs : padicValInt q ((r ^ 2 + 2 : ℤ) ^ s) = s := by
    rw [hqeq]
    exact padicValInt_pow_of_prime s
  have hterm : binomTerm r k j =
      (Nat.choose (2 * k + 1) (2 * s + 1) : ℤ) * r ^ (2 * j) * (r ^ 2 + 2) ^ s := by
    unfold binomTerm
    rw [hch]
  have htnz : binomTerm r k j ≠ 0 := binomTerm_ne_zero r hr k j hjk
  have hC1nz := hCne
  have hrnz : r ^ (2 * j) ≠ 0 := pow_ne_zero _ hr
  have hqsnz : (r ^ 2 + 2 : ℤ) ^ s ≠ 0 := by
    have : (r ^ 2 + 2 : ℤ) ≠ 0 := by nlinarith [sq_nonneg r]
    exact pow_ne_zero _ this
  have hvterm :
      padicValInt q (binomTerm r k j) =
        padicValInt q (Nat.choose (2 * k + 1) (2 * s + 1) : ℤ) + s := by
    rw [hterm, padicValInt.mul (mul_ne_zero hC1nz hrnz) hqsnz,
        padicValInt.mul hC1nz hrnz, hr0, hqs]
    omega
  have hvs : padicValInt q (2 * (s : ℤ) + 1) < s :=
    padic_two_j_lt hq5 hs1
  have hcast : (2 * s + 1 : ℤ) = 2 * (s : ℤ) + 1 := by push_cast; rfl
  have hcastk : (2 * k + 1 : ℤ) = 2 * (k : ℤ) + 1 := by push_cast; rfl
  have : padicValInt q (2 * (k : ℤ) + 1) + padicValInt q (2 * (s : ℤ) + 1) <
      padicValInt q (binomTerm r k j) + padicValInt q (2 * (s : ℤ) + 1) := by
    -- v(2k+1) + v(2s+1) = v(C1) + v(2s+1) - v(C2) + v(2s+1) wait
    -- From hvsum: v(C1) + v(2s+1) = v(2k+1) + v(C2)
    -- v(term) = v(C1) + s
    -- so v(term) - v(2k+1) = v(C1) + s - v(2k+1) = s - v(2s+1) + v(C2) ≥ s - v(2s+1) ≥ 1
    have : padicValInt q (binomTerm r k j) =
        padicValInt q (2 * (k : ℤ) + 1) +
          padicValInt q (Nat.choose (2 * k) (2 * s) : ℤ) + s -
          padicValInt q (2 * (s : ℤ) + 1) := by
      have h1 := hvsum
      rw [hcast, hcastk] at h1
      have := hvterm
      omega
    omega
  omega



lemma padicValInt_sum_of_unique_min {q : ℕ} [Fact q.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℤ) (i0 : ι) (hi0 : i0 ∈ s)
    (hne : ∀ i ∈ s, f i ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ i0 → padicValInt q (f i0) < padicValInt q (f i)) :
    padicValInt q (∑ i ∈ s, f i) = padicValInt q (f i0) := by
  classical
  let v0 := padicValInt q (f i0)
  have hdiv0 : (q : ℤ) ^ v0 ∣ f i0 := padicValInt_dvd _
  have hdivs : ∀ i ∈ s, (q : ℤ) ^ v0 ∣ f i := by
    intro i hi
    by_cases h : i = i0
    · subst h; exact hdiv0
    · have : v0 < padicValInt q (f i) := hmin i hi h
      have : v0 ≤ padicValInt q (f i) := Nat.le_of_lt this
      have hf0 : f i ≠ 0 := hne i hi
      rw [padicValInt_dvd_iff]
      exact Or.inr this
  have hsumdiv : (q : ℤ) ^ v0 ∣ ∑ i ∈ s, f i :=
    Finset.dvd_sum hdivs
  have hsum_ne : ∑ i ∈ s, f i ≠ 0 := by
    -- if the sum were 0, then q^{v0+1} would divide the sum (namely 0),
    -- hence divide f i0 after subtracting the rest, contradiction.
    intro hz
    have hrest : (q : ℤ) ^ (v0 + 1) ∣ ∑ i ∈ s.erase i0, f i := by
      refine Finset.dvd_sum ?_
      intro i hi
      have hi' : i ∈ s := Finset.mem_of_mem_erase hi
      have hine : i ≠ i0 := Finset.ne_of_mem_erase hi
      have : v0 < padicValInt q (f i) := hmin i hi' hine
      have : v0 + 1 ≤ padicValInt q (f i) := Nat.succ_le_of_lt this
      rw [padicValInt_dvd_iff]
      exact Or.inr this
    have : (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hsplit : ∑ i ∈ s, f i = f i0 + ∑ i ∈ s.erase i0, f i :=
        (Finset.sum_erase_add s f hi0).symm.trans (add_comm _ _)
      -- 0 = f i0 + rest ⇒ f i0 = -rest
      have : f i0 = -∑ i ∈ s.erase i0, f i := by
        rw [hz] at hsplit
        linarith
      rw [this]
      exact dvd_neg.mpr hrest
    have : ¬ (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hf0 : f i0 ≠ 0 := hne i0 hi0
      rw [padicValInt_dvd_iff]
      simp [hf0, v0]
    exact this ‹(q : ℤ) ^ (v0 + 1) ∣ f i0›
  have hvle : v0 ≤ padicValInt q (∑ i ∈ s, f i) := by
    rw [padicValInt_dvd_iff] at hsumdiv
    exact hsumdiv.resolve_left hsum_ne
  have hvge : padicValInt q (∑ i ∈ s, f i) ≤ v0 := by
    by_contra h
    have : v0 + 1 ≤ padicValInt q (∑ i ∈ s, f i) := by omega
    have hsum' : (q : ℤ) ^ (v0 + 1) ∣ ∑ i ∈ s, f i := by
      rw [padicValInt_dvd_iff]
      exact Or.inr this
    have hrest : (q : ℤ) ^ (v0 + 1) ∣ ∑ i ∈ s.erase i0, f i := by
      refine Finset.dvd_sum ?_
      intro i hi
      have hi' : i ∈ s := Finset.mem_of_mem_erase hi
      have hine : i ≠ i0 := Finset.ne_of_mem_erase hi
      have : v0 + 1 ≤ padicValInt q (f i) := Nat.succ_le_of_lt (hmin i hi' hine)
      rw [padicValInt_dvd_iff]
      exact Or.inr this
    have : (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hsplit : ∑ i ∈ s, f i = f i0 + ∑ i ∈ s.erase i0, f i :=
        (Finset.sum_erase_add s f hi0).symm.trans (add_comm _ _)
      have : f i0 = ∑ i ∈ s, f i - ∑ i ∈ s.erase i0, f i := by
        linarith
      rw [this]
      exact dvd_sub hsum' hrest
    have : ¬ (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hf0 : f i0 ≠ 0 := hne i0 hi0
      rw [padicValInt_dvd_iff]
      simp [hf0, v0]
    exact this ‹(q : ℤ) ^ (v0 + 1) ∣ f i0›
  omega

lemma pY_ne_zero (r : ℤ) (k : ℕ) : pY r k ≠ 0 := by
  intro h
  have hn := p_norm r k
  rw [h] at hn
  simp at hn
  nlinarith [sq_nonneg (pX r k)]

lemma padicValInt_two_pow_eq_zero {q k : ℕ} [Fact q.Prime] (hodd : Odd q) :
    padicValInt q ((2 : ℤ) ^ k) = 0 := by
  have hv2 : padicValInt q (2 : ℤ) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro h
    have : (q : ℕ) ∣ 2 := by exact_mod_cast h
    have : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp this
    rcases this with h1 | h2
    · exact (Fact.out : Nat.Prime q).ne_one h1
    · rw [h2] at hodd; exact Nat.not_odd_iff_even.mpr (by decide) hodd
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicValInt.mul (pow_ne_zero k (by decide)) (by decide), ih, hv2]

lemma padicVal_pY {r : ℤ} {q k : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q)
    (hq5 : 5 ≤ q) :
    padicValInt q (pY r k) = padicValInt q (2 * (k : ℤ) + 1) := by
  have hsum := two_pow_pY_eq_sum r k
  have h2ne : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  have hYne : pY r k ≠ 0 := pY_ne_zero r k
  have hv2k : padicValInt q ((2 : ℤ) ^ k) = 0 := padicValInt_two_pow_eq_zero hodd
  have hmem : k ∈ Finset.range (k + 1) := by simp
  have hne : ∀ j ∈ Finset.range (k + 1), binomTerm r k j ≠ 0 := by
    intro j hj
    have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact binomTerm_ne_zero r hr k j this
  have hmin : ∀ j ∈ Finset.range (k + 1), j ≠ k →
      padicValInt q (binomTerm r k k) < padicValInt q (binomTerm r k j) := by
    intro j hj hjne
    have hjlt : j < k := by
      have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    have hlt := padicVal_binomTerm_lt hq hr hodd hq5 hjlt
    rwa [← padicVal_binomTerm_last hq hr hodd] at hlt
  have hvsum : padicValInt q (∑ j ∈ Finset.range (k + 1), binomTerm r k j) =
      padicValInt q (binomTerm r k k) :=
    padicValInt_sum_of_unique_min (Finset.range (k + 1)) (binomTerm r k) k hmem hne hmin
  have : padicValInt q ((2 : ℤ) ^ k * pY r k) = padicValInt q (2 * (k : ℤ) + 1) := by
    rw [hsum, hvsum, padicVal_binomTerm_last hq hr hodd]
  rw [padicValInt.mul h2ne hYne, hv2k, zero_add] at this
  exact this

lemma nine_pow_gt_two_mul_add_one : ∀ n : ℕ, 1 ≤ n → (9 : ℤ) ^ n > 2 * (n : ℤ) + 1
  | 1, _ => by norm_num
  | n + 2, _ => by
    have ih : (9 : ℤ) ^ (n + 1) > 2 * ((n + 1 : ℕ) : ℤ) + 1 :=
      nine_pow_gt_two_mul_add_one (n + 1) (by omega)
    have hge : (9 : ℤ) ^ (n + 2) = 9 * (9 : ℤ) ^ (n + 1) := pow_succ' _ _
    have : (9 : ℤ) * (9 : ℤ) ^ (n + 1) > 9 * (2 * ((n + 1 : ℕ) : ℤ) + 1) := by
      nlinarith
    have : 9 * (2 * ((n + 1 : ℕ) : ℤ) + 1) ≥ 2 * ((n + 2 : ℕ) : ℤ) + 1 := by
      push_cast
      nlinarith
    nlinarith

lemma pY_not_pow_of_q {r : ℤ} {q l k : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : 2 ≤ r) (hodd : Odd q) (hq5 : 5 ≤ q)
    (hl : 1 ≤ l) (h : pY r k = (q : ℤ) ^ l) : False := by
  have hv := padicVal_pY (r := r) (q := q) (k := k) hq (by linarith : r ≠ 0) hodd hq5
  have hql : padicValInt q ((q : ℤ) ^ l) = l := padicValInt_pow_of_prime l
  rw [h, hql] at hv
  have hne : (2 * (k : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have hdvd : (q : ℤ) ^ l ∣ (2 * (k : ℤ) + 1) := by
    have : l ≤ padicValInt q (2 * (k : ℤ) + 1) := by omega
    rw [padicValInt_dvd_iff]
    exact Or.inr this
  have hpos : (0 : ℤ) < 2 * (k : ℤ) + 1 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have hle : (q : ℤ) ^ l ≤ 2 * (k : ℤ) + 1 := Int.le_of_dvd hpos hdvd
  have hlower := pY_pow_lower r (by linarith : 1 ≤ r) k
  have : (2 * r ^ 2 + 1 : ℤ) ^ k ≤ 2 * (k : ℤ) + 1 := by
    calc
      (2 * r ^ 2 + 1 : ℤ) ^ k ≤ pY r k := hlower
      _ = (q : ℤ) ^ l := h
      _ ≤ 2 * (k : ℤ) + 1 := hle
  have hbase : (9 : ℤ) ≤ 2 * r ^ 2 + 1 := by nlinarith [hr]
  have h9 : (9 : ℤ) ^ k ≤ 2 * (k : ℤ) + 1 :=
    le_trans (pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 9) hbase k) this
  match k with
  | 0 =>
    have hY0 : pY r 0 = 1 := pY_zero r
    rw [hY0] at h
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (Nat.one_le_of_lt (lt_of_lt_of_le (by decide : 1 < 5) hq5))
    have : (q : ℤ) ^ 1 ≤ (q : ℤ) ^ l := pow_le_pow_right₀ hq1 hl
    simp at this
    have : (q : ℤ) ≤ 1 := by
      have : (q : ℤ) ^ l = 1 := h.symm
      nlinarith
    have : (5 : ℤ) ≤ q := by exact_mod_cast hq5
    linarith
  | k + 1 =>
    have : (9 : ℤ) ^ (k + 1) > 2 * ((k + 1 : ℕ) : ℤ) + 1 :=
      nine_pow_gt_two_mul_add_one (k + 1) (by omega)
    linarith

lemma no_q_pow_pell {r X : ℤ} {q n : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : 2 ≤ r) (hodd : Odd q) (hq5 : 5 ≤ q)
    (hn : Odd n) (hn3 : 3 ≤ n) (hX : 0 < X)
    (h : X ^ 2 + 2 = (q : ℤ) ^ n) : False := by
  obtain ⟨k, hk⟩ := hn
  have hn' : n = 2 * k + 1 := by omega
  have hk1 : 1 ≤ k := by omega
  have hpell : X ^ 2 - (r ^ 2 + 2) * ((q : ℤ) ^ k) ^ 2 = -2 := by
    have hpow : (r ^ 2 + 2) * ((q : ℤ) ^ k) ^ 2 = (q : ℤ) ^ n := by
      rw [hq, hn']
      calc
        (r ^ 2 + 2) * ((r ^ 2 + 2) ^ k) ^ 2
            = (r ^ 2 + 2) * (r ^ 2 + 2) ^ (k * 2) := by rw [← pow_mul]
        _ = (r ^ 2 + 2) * (r ^ 2 + 2) ^ (2 * k) := by rw [mul_comm k]
        _ = (r ^ 2 + 2) ^ (2 * k + 1) := (pow_succ' _ _).symm
    omega
  have hYpos : (0 : ℤ) < (q : ℤ) ^ k :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 5) hq5)) k
  obtain ⟨m, _, hmY⟩ := exists_pSol r X ((q : ℤ) ^ k) (by linarith) hX hYpos hpell
  exact pY_not_pow_of_q hq hr hodd hq5 hk1 hmY.symm


end PellNegTwo


namespace Zsqrtm2

lemma norm_eq (z : Zsqrtm2) : z.norm = z.re ^ 2 + 2 * z.im ^ 2 := by
  rw [norm_def]; ring

lemma int_abs_sub_mul_round (a N : ℤ) (hN : 0 < N) :
    |a - round ((a : ℚ) / N) * N| * 2 ≤ N := by
  have hNq : (0 : ℚ) < N := Int.cast_pos.mpr hN
  set q := round ((a : ℚ) / N)
  have hle : |((a : ℚ) / N) - (q : ℚ)| ≤ 1 / 2 := abs_sub_round _
  have habs : |((a : ℚ) / N) - (q : ℚ)| * (N : ℚ) = |(a : ℚ) - (q : ℚ) * N| := by
    calc
      |((a : ℚ) / N) - (q : ℚ)| * (N : ℚ)
        = |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)| := by rw [abs_of_pos hNq]
      _ = |(((a : ℚ) / N) - (q : ℚ)) * N| := (abs_mul _ _).symm
      _ = |(a : ℚ) - (q : ℚ) * N| := by
          rw [sub_mul, div_mul_cancel₀ _ hNq.ne.symm]
  have hbound : |(a : ℚ) - (q : ℚ) * N| ≤ (N : ℚ) / 2 := by
    rw [← habs]
    have := mul_le_mul_of_nonneg_right hle (le_of_lt hNq)
    linarith
  have hcast : ((a - q * N : ℤ) : ℚ) = (a : ℚ) - (q : ℚ) * N := by push_cast; rfl
  have : ((|a - q * N| * 2 : ℤ) : ℚ) ≤ (N : ℚ) := by
    rw [Int.cast_mul, Int.cast_abs, Int.cast_two, hcast]
    linarith
  exact_mod_cast this

noncomputable instance : Div Zsqrtm2 :=
  ⟨fun x y =>
    ⟨round ((x * star y).re / (y.norm : ℚ)),
     round ((x * star y).im / (y.norm : ℚ))⟩⟩

lemma div_def (x y : Zsqrtm2) :
    x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
             round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := rfl

noncomputable instance : Mod Zsqrtm2 := ⟨fun x y => x - y * (x / y)⟩

lemma mod_def (x y : Zsqrtm2) : x % y = x - y * (x / y) := rfl

lemma four_mul_sq_add_le {A B N : ℤ} (hA : |A| * 2 ≤ N) (hB : |B| * 2 ≤ N) :
    4 * (A ^ 2 + 2 * B ^ 2) ≤ 3 * N ^ 2 := by
  nlinarith [sq_abs A, sq_abs B, abs_nonneg A, abs_nonneg B]

lemma rem_mul_star (x y : Zsqrtm2) :
    (x % y) * star y = x * star y - (x / y) * (y.norm : Zsqrtm2) := by
  rw [mod_def, sub_mul, norm_eq_mul_conj]
  ring

lemma rem_norm_mul (x y : Zsqrtm2) :
    (x % y).norm * y.norm = (x * star y - (x / y) * (y.norm : Zsqrtm2)).norm := by
  have := rem_mul_star x y
  rw [← this, Zsqrtd.norm_mul, Zsqrtd.norm_conj]

lemma mul_intCast_re (q : Zsqrtm2) (n : ℤ) :
    (q * (n : Zsqrtm2)).re = q.re * n := by
  simp [Zsqrtd.re_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma mul_intCast_im (q : Zsqrtm2) (n : ℤ) :
    (q * (n : Zsqrtm2)).im = q.im * n := by
  simp [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma rem_norm_expand (x y : Zsqrtm2) :
    (x * star y - (x / y) * (y.norm : Zsqrtm2)).norm =
      ((x * star y).re - (x / y).re * y.norm) ^ 2 +
      2 * ((x * star y).im - (x / y).im * y.norm) ^ 2 := by
  rw [norm_eq, re_sub, im_sub, mul_intCast_re, mul_intCast_im]

lemma norm_mod_lt (x : Zsqrtm2) {y : Zsqrtm2} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have hNpos : 0 < y.norm := by
    have : 0 ≤ y.norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) y
    have : y.norm ≠ 0 := by
      intro h0
      exact hy ((Zsqrtd.norm_eq_zero_iff (by decide : (-2 : ℤ) < 0) y).mp h0)
    omega
  set N := y.norm with hNdef
  set α := x * star y
  set q := x / y
  have hre : |α.re - q.re * N| * 2 ≤ N := by
    change |α.re - round ((α.re : ℚ) / N) * N| * 2 ≤ N
    exact int_abs_sub_mul_round α.re N hNpos
  have him : |α.im - q.im * N| * 2 ≤ N := by
    change |α.im - round ((α.im : ℚ) / N) * N| * 2 ≤ N
    exact int_abs_sub_mul_round α.im N hNpos
  have h4 : 4 * (α - q * (N : Zsqrtm2)).norm ≤ 3 * N ^ 2 := by
    rw [show α - q * (N : Zsqrtm2) = x * star y - (x / y) * (y.norm : Zsqrtm2) by rfl]
    rw [rem_norm_expand]
    exact four_mul_sq_add_le hre him
  have hmul : (x % y).norm * N = (α - q * (N : Zsqrtm2)).norm := rem_norm_mul x y
  have : 4 * ((x % y).norm * N) ≤ 3 * N ^ 2 := by rw [hmul]; exact h4
  have hrm : 0 ≤ (x % y).norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) _
  nlinarith

lemma natAbs_norm_mod_lt (x : Zsqrtm2) {y : Zsqrtm2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h1 : (x % y).norm < y.norm := norm_mod_lt x hy
  have h2 : 0 ≤ (x % y).norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) _
  have h3 : 0 ≤ y.norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) _
  have e1 : ((x % y).norm.natAbs : ℤ) = (x % y).norm := Int.natAbs_of_nonneg h2
  have e2 : (y.norm.natAbs : ℤ) = y.norm := Int.natAbs_of_nonneg h3
  have : ((x % y).norm.natAbs : ℤ) < (y.norm.natAbs : ℤ) := by
    rwa [e1, e2]
  exact_mod_cast this

lemma norm_le_norm_mul_left (x : Zsqrtm2) {y : Zsqrtm2} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have : 1 ≤ y.norm.natAbs := by
    have hp : 0 < y.norm := by
      have : 0 ≤ y.norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) y
      have : y.norm ≠ 0 := by
        intro h0
        exact hy ((Zsqrtd.norm_eq_zero_iff (by decide : (-2 : ℤ) < 0) y).mp h0)
      omega
    have hn : 0 ≤ y.norm := le_of_lt hp
    have : (y.norm.natAbs : ℤ) = y.norm := Int.natAbs_of_nonneg hn
    have : (1 : ℤ) ≤ y.norm.natAbs := by
      rw [this]; omega
    exact_mod_cast this
  exact Nat.le_mul_of_pos_right _ this

noncomputable instance : EuclideanDomain Zsqrtm2 :=
  { inferInstanceAs (CommRing Zsqrtm2),
    inferInstanceAs (Nontrivial Zsqrtm2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp [div_def, Zsqrtd.norm_zero]
      rfl
    quotient_mul_add_remainder_eq := fun _ _ => by
      simp [mod_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (norm_le_norm_mul_left a hb0) }

lemma eq_one_or_neg_one_of_norm_one {z : Zsqrtm2} (h : z.norm = 1) :
    z = 1 ∨ z = -1 := by
  rw [norm_eq] at h
  have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hre : z.re = 1 ∨ z.re = -1 := by
    rw [him] at h; simpa using h
  rcases hre with h1 | h1
  · left; ext <;> simp [h1, him]
  · right; ext <;> simp [h1, him]

lemma isUnit_iff_eq_one_or_neg_one (z : Zsqrtm2) :
    IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hu
    have : z.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by decide : (-2 : ℤ) ≤ 0) z).mpr hu
    exact eq_one_or_neg_one_of_norm_one this
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact IsUnit.neg isUnit_one

/-- `√(-2)` as an element of `ℤ√(-2)`. -/
def ω : Zsqrtm2 := ⟨0, 1⟩

lemma ω_sq : (ω * ω : Zsqrtm2) = (-2 : Zsqrtm2) := by
  ext
  · simp [ω]
  · simp [ω]

lemma re_ω : ω.re = 0 := rfl
lemma im_ω : ω.im = 1 := rfl

lemma mul_ω (z : Zsqrtm2) : z * ω = ⟨-2 * z.im, z.re⟩ := by
  ext
  · simp [ω]
  · simp [ω]

lemma star_ω : star ω = -ω := by
  ext <;> simp [ω]

lemma norm_ω : ω.norm = 2 := by
  simp [norm_eq, ω]

/-- The two factors of `x^2 + 2`. -/
def plus (x : ℤ) : Zsqrtm2 := ⟨x, 1⟩
def minus (x : ℤ) : Zsqrtm2 := ⟨x, -1⟩

lemma plus_mul_minus (x : ℤ) : plus x * minus x = ⟨x ^ 2 + 2, 0⟩ := by
  ext
  · simp [plus, minus]; ring
  · simp [plus, minus]

lemma intCast_mk (n : ℤ) : (n : Zsqrtm2) = ⟨n, 0⟩ := by
  ext
  · simp [Zsqrtd.re_intCast]
  · simp [Zsqrtd.im_intCast]

lemma plus_mul_minus' (x : ℤ) : plus x * minus x = (x ^ 2 + 2 : ℤ) := by
  rw [plus_mul_minus, intCast_mk]

lemma plus_sub_minus (x : ℤ) : plus x - minus x = ⟨0, 2⟩ := by
  ext <;> simp [plus, minus]

lemma two_mul_ω : (2 : Zsqrtm2) * ω = ⟨0, 2⟩ := by
  ext <;> simp [ω]

lemma plus_sub_minus' (x : ℤ) : plus x - minus x = (2 : Zsqrtm2) * ω := by
  rw [plus_sub_minus, two_mul_ω]

lemma plus_add_minus (x : ℤ) : plus x + minus x = ⟨2 * x, 0⟩ := by
  ext <;> simp [plus, minus]; ring

lemma norm_plus (x : ℤ) : (plus x).norm = x ^ 2 + 2 := by
  simp [plus, norm_eq]

lemma star_plus (x : ℤ) : star (plus x) = minus x := by
  ext <;> simp [plus, minus]

lemma not_isUnit_ω : ¬ IsUnit ω := by
  intro hu
  have : ω.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by decide : (-2 : ℤ) ≤ 0) ω).mpr hu
  rw [norm_ω] at this
  omega

lemma omega_irreducible : Irreducible ω := by
  refine ⟨not_isUnit_ω, ?_⟩
  intro a b hab
  have hn : (a * b).norm = 2 := by rw [← hab, norm_ω]
  rw [Zsqrtd.norm_mul] at hn
  have ha0 : 0 ≤ a.norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) a
  have hb0 : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) b
  have hdiv : a.norm ∣ 2 := ⟨b.norm, hn.symm⟩
  have hne : a.norm ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hn
    exact (by decide : (2 : ℤ) ≠ 0) hn.symm
  have hle : 1 ≤ a.norm ∧ a.norm ≤ 2 := by
    have := Int.le_of_dvd (by decide) hdiv
    omega
  have : a.norm = 1 ∨ a.norm = 2 := by omega
  rcases this with h | h
  · left
    exact (Zsqrtd.norm_eq_one_iff' (by decide : (-2 : ℤ) ≤ 0) a).mp h
  · right
    have : b.norm = 1 := by
      rw [h, two_mul] at hn
      linarith
    exact (Zsqrtd.norm_eq_one_iff' (by decide : (-2 : ℤ) ≤ 0) b).mp this

/-- If `ω` divides `plus x`, then `x` is even. -/
lemma omega_dvd_plus_iff (x : ℤ) : ω ∣ plus x ↔ Even x := by
  constructor
  · intro ⟨z, hz⟩
    -- `ω ∣ plus x` means `plus x = ω * z`
    have hre : (plus x).re = (ω * z).re := congrArg Zsqrtd.re hz
    have : x = -2 * z.im := by
      simp [plus, ω] at hre
      linarith
    exact ⟨-z.im, by rw [this]; ring⟩
  · intro ⟨k, hk⟩
    refine ⟨⟨1, -k⟩, ?_⟩
    ext
    · simp [plus, ω, hk]; ring
    · simp [plus, ω]

lemma odd_not_omega_dvd_plus {x : ℤ} (hx : Odd x) : ¬ ω ∣ plus x := by
  rw [omega_dvd_plus_iff]
  exact Int.not_even_iff_odd.mpr hx

lemma omega_prime : Prime ω :=
  Irreducible.prime omega_irreducible

lemma two_eq_neg_omega_sq : (2 : Zsqrtm2) = - (ω * ω) := by
  rw [ω_sq]
  ext <;> simp

lemma two_mul_omega_eq_neg_omega_pow_three : (2 : Zsqrtm2) * ω = - (ω * ω * ω) := by
  rw [two_eq_neg_omega_sq]
  ring

lemma plus_ne_zero (x : ℤ) : plus x ≠ 0 := by
  intro h
  have : (plus x).norm = 0 := by rw [h]; simp [norm_def]
  rw [norm_plus] at this
  nlinarith [sq_nonneg x]

lemma minus_ne_zero (x : ℤ) : minus x ≠ 0 := by
  intro h
  have hn : (minus x).norm = 0 := by rw [h]; simp [norm_def]
  have : (minus x).norm = x ^ 2 + 2 := by simp [minus, norm_eq]
  rw [this] at hn
  nlinarith [sq_nonneg x]

/-- `plus x` and `minus x` are coprime when `x` is odd. -/
lemma isCoprime_plus_minus {x : ℤ} (hx : Odd x) : IsCoprime (plus x) (minus x) := by
  refine isCoprime_of_irreducible_dvd ?_ ?_
  · exact not_and_of_not_left _ (plus_ne_zero x)
  · intro π hπ hπplus hπminus
    have hdiff : π ∣ plus x - minus x := dvd_sub hπplus hπminus
    rw [plus_sub_minus'] at hdiff
    have h2ω : π ∣ (2 : Zsqrtm2) * ω := hdiff
    have hω3 : π ∣ ω ^ 3 := by
      have : (2 : Zsqrtm2) * ω = - (ω ^ 3) := by
        rw [two_mul_omega_eq_neg_omega_pow_three, pow_three]
        ring
      rw [this] at h2ω
      exact (dvd_neg.mp h2ω)
    have hπω : π ∣ ω := by
      have hp : Prime π := Irreducible.prime hπ
      exact hp.dvd_of_dvd_pow (n := 3) hω3
    have : Associated π ω := (Irreducible.dvd_irreducible_iff_associated hπ omega_irreducible).mp hπω
    have : ω ∣ plus x := this.symm.dvd.trans hπplus
    exact odd_not_omega_dvd_plus hx this

/-- If `x^2 + 2 = q^n` with `x` odd, then `plus x` is associated to an `n`th power. -/
lemma plus_associated_pow {x : ℤ} {q n : ℕ} (hx : Odd x)
    (h : (x ^ 2 + 2 : ℤ) = (q : ℤ) ^ n) :
    ∃ d : Zsqrtm2, Associated (d ^ n) (plus x) := by
  have hab : IsCoprime (plus x) (minus x) := isCoprime_plus_minus hx
  have hmul : plus x * minus x = ((q : ℤ) : Zsqrtm2) ^ n := by
    rw [plus_mul_minus', h, Int.cast_pow]
  exact exists_associated_pow_of_mul_eq_pow' hab hmul

lemma associated_iff_eq_or_neg {a b : Zsqrtm2} :
    Associated a b ↔ a = b ∨ a = -b := by
  constructor
  · intro ⟨u, hu⟩
    have : (u : Zsqrtm2) = 1 ∨ (u : Zsqrtm2) = -1 :=
      (isUnit_iff_eq_one_or_neg_one u).mp u.isUnit
    rcases this with h | h
    · left; rw [← hu, h, mul_one]
    · right
      rw [← hu, h]
      ring
  · rintro (rfl | rfl)
    · exact Associated.refl _
    · exact ⟨-1, by simp⟩

/-- Imaginary part of a power: `s` always divides it. -/
lemma s_dvd_im_pow (r s : ℤ) : ∀ n : ℕ, s ∣ ((⟨r, s⟩ : Zsqrtm2) ^ n).im
  | 0 => by simp
  | n + 1 => by
    have ih : s ∣ ((⟨r, s⟩ : Zsqrtm2) ^ n).im := s_dvd_im_pow r s n
    have : ((⟨r, s⟩ : Zsqrtm2) ^ (n + 1)).im =
        r * ((⟨r, s⟩ : Zsqrtm2) ^ n).im + s * ((⟨r, s⟩ : Zsqrtm2) ^ n).re := by
      rw [pow_succ, im_mul]
      simp
      ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

/-- Pair `(U n, V n)` so that `(r + √(-2))^n = U n + V n √(-2)`. -/
def UV (r : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let u := (UV r n).1
    let v := (UV r n).2
    (r * u - 2 * v, u + r * v)

def U (r : ℤ) (n : ℕ) : ℤ := (UV r n).1
def V (r : ℤ) (n : ℕ) : ℤ := (UV r n).2

lemma U_zero (r : ℤ) : U r 0 = 1 := rfl
lemma V_zero (r : ℤ) : V r 0 = 0 := rfl

lemma U_succ (r : ℤ) (n : ℕ) : U r (n + 1) = r * U r n - 2 * V r n := rfl
lemma V_succ (r : ℤ) (n : ℕ) : V r (n + 1) = U r n + r * V r n := rfl

lemma pow_eq_U_V (r : ℤ) : ∀ n : ℕ,
    (⟨r, 1⟩ : Zsqrtm2) ^ n = ⟨U r n, V r n⟩
  | 0 => by
    ext
    · simp [U_zero]
    · simp [V_zero]
  | n + 1 => by
    rw [pow_succ, pow_eq_U_V r n, U_succ, V_succ]
    ext
    · simp; ring
    · simp; ring

lemma V_one (r : ℤ) : V r 1 = 1 := by simp [V_succ, U_zero, V_zero]
lemma U_one (r : ℤ) : U r 1 = r := by simp [U_succ, U_zero, V_zero]
lemma V_two (r : ℤ) : V r 2 = 2 * r := by
  rw [V_succ, U_one, V_one]; ring
lemma U_two (r : ℤ) : U r 2 = r ^ 2 - 2 := by
  rw [U_succ, U_one, V_one]; ring
lemma V_three (r : ℤ) : V r 3 = 3 * r ^ 2 - 2 := by
  rw [V_succ, U_two, V_two]; ring
lemma U_three (r : ℤ) : U r 3 = r ^ 3 - 6 * r := by
  rw [U_succ, U_two, V_two]; ring

lemma U_V_norm (r : ℤ) : ∀ n : ℕ, U r n ^ 2 + 2 * V r n ^ 2 = (r ^ 2 + 2) ^ n
  | 0 => by simp [U_zero, V_zero]
  | n + 1 => by
    have ih := U_V_norm r n
    calc
      U r (n + 1) ^ 2 + 2 * V r (n + 1) ^ 2
        = (r * U r n - 2 * V r n) ^ 2 + 2 * (U r n + r * V r n) ^ 2 := by
          rw [U_succ, V_succ]
      _ = (r ^ 2 + 2) * (U r n ^ 2 + 2 * V r n ^ 2) := by ring
      _ = (r ^ 2 + 2) * (r ^ 2 + 2) ^ n := by rw [ih]
      _ = (r ^ 2 + 2) ^ (n + 1) := (pow_succ' _ _).symm

lemma V_succ2 (r : ℤ) (n : ℕ) :
    V r (n + 2) = 2 * r * V r (n + 1) - (r ^ 2 + 2) * V r n := by
  rw [V_succ, U_succ, V_succ]
  ring

/-- If `plus x = ± ⟨r,s⟩^n` and the im of plus is 1, then `s ∣ 1`. -/
lemma s_dvd_one_of_plus_eq_pow {x r s : ℤ} {n : ℕ}
    (h : plus x = (⟨r, s⟩ : Zsqrtm2) ^ n ∨ plus x = - ((⟨r, s⟩ : Zsqrtm2) ^ n)) :
    s ∣ 1 := by
  have him : (plus x).im = 1 := rfl
  have hs := s_dvd_im_pow r s n
  rcases h with h | h
  · rw [h] at him
    rw [← him]
    exact hs
  · have : (-((⟨r, s⟩ : Zsqrtm2) ^ n)).im = - ((⟨r, s⟩ : Zsqrtm2) ^ n).im := by
      simp
    rw [h, this] at him
    have : s ∣ -((⟨r, s⟩ : Zsqrtm2) ^ n).im := hs.neg_right
    rw [him] at this
    exact this

lemma norm_mk (r s : ℤ) : (⟨r, s⟩ : Zsqrtm2).norm = r ^ 2 + 2 * s ^ 2 := by
  simp [norm_eq]

lemma norm_pow (z : Zsqrtm2) : ∀ n : ℕ, (z ^ n).norm = z.norm ^ n
  | 0 => by simp [norm_def]
  | n + 1 => by rw [pow_succ, pow_succ, Zsqrtd.norm_mul, norm_pow]

/-- Main structural lemma: a solution of `x^2 + 2 = q^n` (x odd, q prime, n≥1)
    yields `r` with `r^2 + 2 = q` and `|V r n| = 1`. -/
lemma exists_r_of_sq_add_two {x : ℤ} {q n : ℕ} (hx : Odd x) (_hq : Nat.Prime q)
    (h : (x ^ 2 + 2 : ℤ) = (q : ℤ) ^ n) :
    ∃ r : ℤ, r ^ 2 + 2 = q ∧ |V r n| = 1 := by
  obtain ⟨d, hd⟩ := plus_associated_pow hx h
  have hpm' : plus x = d ^ n ∨ plus x = - (d ^ n) := by
    have := (associated_iff_eq_or_neg).mp hd
    rcases this with h | h
    · exact Or.inl h.symm
    · right
      rw [h, neg_neg]
  set r := d.re
  set s := d.im
  have hdmk : d = ⟨r, s⟩ := by ext <;> rfl
  have hs1 : s ∣ 1 := by
    rw [hdmk] at hpm'
    exact s_dvd_one_of_plus_eq_pow hpm'
  have hs : s = 1 ∨ s = -1 :=
    Int.isUnit_iff.mp (isUnit_of_dvd_one hs1)
  -- norm: N(d)^n = N(plus x) = x^2+2 = q^n, N(d) > 0 so N(d) = q
  have hN : d.norm = q := by
    have h1 : (d ^ n).norm = (plus x).norm := by
      rcases hpm' with h | h
      · rw [h]
      · rw [h, Zsqrtd.norm_neg]
    rw [norm_pow, norm_plus] at h1
    have hxq : (x ^ 2 + 2 : ℤ) = (q : ℤ) ^ n := h
    rw [hxq] at h1
    have hnn : 0 ≤ d.norm := Zsqrtd.norm_nonneg (by decide : (-2 : ℤ) ≤ 0) d
    have : d.norm ^ n = (q : ℤ) ^ n := h1
    have hn0 : n ≠ 0 := by
      intro hn0
      subst hn0
      have : 2 ≤ x ^ 2 + 2 := by nlinarith [sq_nonneg x]
      have : 2 ≤ (1 : ℤ) := by
        simp [h] at this
      omega
    have hq0 : (0 : ℤ) ≤ q := Nat.cast_nonneg _
    exact (pow_left_inj₀ hnn hq0 hn0).mp this
  have hNs : r ^ 2 + 2 * s ^ 2 = q := by
    simpa [r, s, norm_eq] using hN
  rcases hs with hs | hs
  · refine ⟨r, ?_, ?_⟩
    · rw [hs] at hNs; simpa using hNs
    · -- plus x = ± ⟨r,1⟩^n = ± ⟨U r n, V r n⟩, im = ± V r n = 1
      have : (⟨r, 1⟩ : Zsqrtm2) ^ n = ⟨U r n, V r n⟩ := pow_eq_U_V r n
      rw [hdmk, hs] at hpm'
      rcases hpm' with h | h
      · have him : (plus x).im = V r n := by
          rw [h, this]
        have : V r n = 1 := by simpa [plus] using him.symm
        simp [this]
      · have him : (plus x).im = - V r n := by
          rw [h, this]; simp
        have : V r n = -1 := by
          have : (1 : ℤ) = - V r n := by simpa [plus] using him
          omega
        simp [this]
  · refine ⟨r, ?_, ?_⟩
    · rw [hs] at hNs; simpa using hNs
    · have hpow : (⟨r, -1⟩ : Zsqrtm2) ^ n = ⟨U r n, -V r n⟩ := by
        have : (⟨r, -1⟩ : Zsqrtm2) = star (⟨r, 1⟩) := by ext <;> simp
        rw [this, ← star_pow, pow_eq_U_V]
        ext <;> simp
      rw [hdmk, hs] at hpm'
      rcases hpm' with h | h
      · have him : (plus x).im = - V r n := by
          rw [h, hpow]
        have : V r n = -1 := by
          have : (1 : ℤ) = - V r n := by simpa [plus] using him
          omega
        simp [this]
      · have him : (plus x).im = V r n := by
          rw [h, hpow]; simp
        have : V r n = 1 := by simpa [plus] using him.symm
        simp [this]

/-- Determinant identity: `V n * U (n-1) - U n * V (n-1) = (r^2+2)^{n-1}`. -/
lemma UV_det (r : ℤ) : ∀ n : ℕ,
    V r (n + 1) * U r n - U r (n + 1) * V r n = (r ^ 2 + 2) ^ n
  | 0 => by
    simp [V_one, U_zero, U_one, V_zero]
  | n + 1 => by
    have ih := UV_det r n
    calc
      V r (n + 2) * U r (n + 1) - U r (n + 2) * V r (n + 1)
        = (U r (n + 1) + r * V r (n + 1)) * U r (n + 1)
          - (r * U r (n + 1) - 2 * V r (n + 1)) * V r (n + 1) := by
            rw [V_succ r (n + 1), U_succ r (n + 1)]
      _ = U r (n + 1) ^ 2 + 2 * V r (n + 1) ^ 2 := by ring
      _ = (r ^ 2 + 2) ^ (n + 1) := U_V_norm r (n + 1)

/-- Cassini identity for `V`. -/
lemma V_cassini (r : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    V r (n + 1) * V r (n - 1) - V r n ^ 2 = - (r ^ 2 + 2) ^ (n - 1) := by
  have hdet := UV_det r (n - 1)
  have hns : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hns] at hdet
  -- V n = U (n-1) + r V (n-1), so U (n-1) = V n - r V (n-1)
  have hV : V r n = U r (n - 1) + r * V r (n - 1) := by
    rw [← V_succ, hns]
  have hU : U r (n - 1) = V r n - r * V r (n - 1) := by omega
  -- V (n+1) = U n + r V n
  have hV1 : V r (n + 1) = U r n + r * V r n := V_succ r n
  calc
    V r (n + 1) * V r (n - 1) - V r n ^ 2
      = (U r n + r * V r n) * V r (n - 1) - V r n ^ 2 := by rw [hV1]
    _ = U r n * V r (n - 1) + r * V r n * V r (n - 1) - V r n ^ 2 := by ring
    _ = - (V r n * U r (n - 1) - U r n * V r (n - 1)) := by
        rw [hU]; ring
    _ = - (r ^ 2 + 2) ^ (n - 1) := by rw [hdet]

lemma V_two_abs {r : ℤ} (hr : 2 ≤ |r|) : 2 ≤ |V r 2| := by
  rw [V_two, abs_mul, abs_two]
  nlinarith

lemma V_three_abs {r : ℤ} (hr : 2 ≤ |r|) : 2 < |V r 3| := by
  rw [V_three]
  have : 2 ≤ |r| := hr
  have : 4 ≤ r ^ 2 := by
    nlinarith [sq_abs r]
  have : 10 ≤ |3 * r ^ 2 - 2| := by
    have h1 : 0 ≤ 3 * r ^ 2 - 2 := by nlinarith
    rw [abs_of_nonneg h1]
    nlinarith
  omega

/-- If `|r| ≥ 2` and `n` is even and at least 2, then `|V r n| ≠ 1`. -/
lemma V_ne_one_of_even {r : ℤ} {n : ℕ} (hr : 2 ≤ |r|) (hn : 2 ≤ n) (he : Even n) :
    |V r n| ≠ 1 := by
  intro hV
  -- If |V n| = 1 then U n ^ 2 + 2 = q^n. But n even ⇒ q^n is a square, two squares differ by 2.
  have hnorm := U_V_norm r n
  have hU : U r n ^ 2 + 2 = (r ^ 2 + 2) ^ n := by
    have : V r n ^ 2 = 1 := by
      have : V r n = 1 ∨ V r n = -1 := eq_or_eq_neg_of_abs_eq hV
      rcases this with h | h <;> simp [h]
    rw [this, mul_one] at hnorm
    exact hnorm
  obtain ⟨k, hk⟩ := he
  have : (r ^ 2 + 2) ^ n = ((r ^ 2 + 2) ^ k) ^ 2 := by
    rw [hk, show k + k = k * 2 from (two_mul k).symm ▸ (mul_comm 2 k), pow_mul]
  have : U r n ^ 2 + 2 = ((r ^ 2 + 2) ^ k) ^ 2 := by rw [← this, hU]
  -- two squares differ by 2
  have hsq : ((r ^ 2 + 2) ^ k) ^ 2 = U r n ^ 2 + 2 := this.symm
  -- reduce to ℕ and reuse not_sq_eq_sq_add_two idea
  have hyx : |U r n| ≤ |(r ^ 2 + 2) ^ k| := by
    have : U r n ^ 2 ≤ ((r ^ 2 + 2) ^ k) ^ 2 := by
      have : 0 ≤ (2 : ℤ) := by decide
      nlinarith
    rw [← sq_abs ((r ^ 2 + 2) ^ k)] at this
    exact abs_le_of_sq_le_sq this (abs_nonneg ((r ^ 2 + 2) ^ k))
  have : ((r ^ 2 + 2) ^ k) ^ 2 - U r n ^ 2 = 2 := by omega
  have : (|(r ^ 2 + 2) ^ k| - |U r n|) * (|(r ^ 2 + 2) ^ k| + |U r n|) = 2 := by
    have := sq_sub_sq (|(r ^ 2 + 2) ^ k|) (|U r n|)
    rw [sq_abs, sq_abs] at this
    nlinarith
  -- the two factors are nonnegative integers with product 2
  have hpos : 0 ≤ |(r ^ 2 + 2) ^ k| - |U r n| := sub_nonneg.mpr hyx
  have hpos2 : 0 ≤ |(r ^ 2 + 2) ^ k| + |U r n| := by nlinarith [abs_nonneg (U r n)]
  have hfac1 : |(r ^ 2 + 2) ^ k| - |U r n| = 1 ∨ |(r ^ 2 + 2) ^ k| - |U r n| = 2 := by
    have hdvd : |(r ^ 2 + 2) ^ k| - |U r n| ∣ 2 := ⟨|(r ^ 2 + 2) ^ k| + |U r n|, by nlinarith⟩
    have : |(r ^ 2 + 2) ^ k| - |U r n| ≤ 2 := Int.le_of_dvd (by decide) hdvd
    have : |(r ^ 2 + 2) ^ k| - |U r n| ≠ 0 := by
      intro hz
      have : (0 : ℤ) = 2 := by nlinarith
      omega
    omega
  rcases hfac1 with h1 | h2
  · have : |(r ^ 2 + 2) ^ k| + |U r n| = 2 := by nlinarith
    omega
  · have : |(r ^ 2 + 2) ^ k| + |U r n| = 1 := by nlinarith
    omega


/-- `V (±1) n = ±1` only for `n = 1` and `n = 3`. -/
lemma V_one_eq_one_iff (n : ℕ) (hn : 1 ≤ n) :
    |V 1 n| = 1 ↔ n = 1 ∨ n = 3 := by
  constructor
  · intro hV
    have hnorm := U_V_norm 1 n
    have hsq : V 1 n ^ 2 = 1 := by
      have : V 1 n = 1 ∨ V 1 n = -1 := eq_or_eq_neg_of_abs_eq hV
      rcases this with h | h <;> simp [h]
    have hU : U 1 n ^ 2 + 2 = (3 : ℤ) ^ n := by
      rw [hsq, mul_one] at hnorm
      -- U^2 + 2 * 1 = (1^2+2)^n = 3^n
      have : (1 ^ 2 + 2 : ℤ) ^ n = (3 : ℤ) ^ n := by norm_num
      rw [this] at hnorm
      exact hnorm
    exact sq_add_two_eq_three_pow hn hU
  · rintro (rfl | rfl)
    · simp [V_one]
    · simp [V_three]

lemma V_neg_one_eq : ∀ n : ℕ, V (-1) n = (-1) ^ (n + 1) * V 1 n
  | 0 => by simp [V_zero]
  | 1 => by simp [V_one]
  | n + 2 => by
      have h0 := V_neg_one_eq n
      have h1 := V_neg_one_eq (n + 1)
      have hr : V (-1) (n + 2) = -2 * V (-1) (n + 1) - 3 * V (-1) n := by
        simpa using V_succ2 (-1) n
      have hr' : V 1 (n + 2) = 2 * V 1 (n + 1) - 3 * V 1 n := by
        simpa using V_succ2 1 n
      rw [hr, h0, h1, hr']
      ring

lemma V_neg_one_eq_one_iff (n : ℕ) (hn : 1 ≤ n) :
    |V (-1) n| = 1 ↔ n = 1 ∨ n = 3 := by
  have : |V (-1) n| = |V 1 n| := by
    rw [V_neg_one_eq, abs_mul, abs_pow]
    simp
  rw [this]
  exact V_one_eq_one_iff n hn

/-- The only solution of `x^2 + 2 = q^n` with `q` an odd prime and `n > 1`
    is `q = 3`, `n = 3`, `|x| = 5`. -/
theorem sq_add_two_eq_odd_prime_pow {x : ℤ} {q n : ℕ}
    (hx : Odd x) (hq : Nat.Prime q) (hqodd : Odd q) (hn : 1 < n)
    (h : (x ^ 2 + 2 : ℤ) = (q : ℤ) ^ n) :
    q = 3 ∧ n = 3 ∧ |x| = 5 := by
  obtain ⟨r, hrq, hV⟩ := exists_r_of_sq_add_two hx hq h
  have hr0 : r ≠ 0 := by
    intro hr0
    rw [hr0] at hrq
    have : (q : ℤ) = 2 := by linarith
    have : q = 2 := by exact_mod_cast this
    have hodd : Odd 2 := by rwa [← this]
    exact Nat.not_odd_iff_even.mpr (by decide : Even 2) hodd
  have : |r| = 1 ∨ 2 ≤ |r| := by
    have : 1 ≤ |r| := by
      have : 0 < |r| := abs_pos.mpr hr0
      omega
    omega
  rcases this with hr1 | hr2
  · -- |r| = 1, q = 3
    have hq3 : q = 3 := by
      have : r ^ 2 = 1 := sq_abs r ▸ (by rw [hr1]; norm_num)
      have : (q : ℤ) = 3 := by rw [← hrq, this]; norm_num
      exact_mod_cast this
    have hn13 : n = 1 ∨ n = 3 := by
      have : |r| = 1 := hr1
      have : r = 1 ∨ r = -1 := by
        have := eq_or_eq_neg_of_abs_eq this
        simpa using this
      rcases this with rfl | rfl
      · exact (V_one_eq_one_iff n (by omega)).mp hV
      · exact (V_neg_one_eq_one_iff n (by omega)).mp hV
    rcases hn13 with hn1 | hn3
    · omega
    · refine ⟨hq3, hn3, ?_⟩
      -- x^2 + 2 = 3^3 = 27, x^2 = 25, |x| = 5
      subst hn3; subst hq3
      have : x ^ 2 + 2 = 27 := by
        simpa using h
      have : x ^ 2 = 25 := by omega
      have : |x| = 5 := by
        have : x = 5 ∨ x = -5 := by
          have hsq : x ^ 2 = 5 ^ 2 := by norm_num [this]
          exact (sq_eq_sq_iff_eq_or_eq_neg).mp hsq
        rcases this with rfl | rfl <;> simp
      exact this
  · -- |r| ≥ 2: reduce to the Pell equation X^2 - q Y^2 = -2
    have hqZ : (q : ℤ) = r ^ 2 + 2 := hrq.symm
    have hVsq : V r n ^ 2 = 1 := by
      rcases eq_or_eq_neg_of_abs_eq hV with h | h <;> simp [h]
    have hnorm := U_V_norm r n
    have hUeq : U r n ^ 2 + 2 = (q : ℤ) ^ n := by
      rw [hVsq, mul_one] at hnorm
      rwa [← hqZ] at hnorm
    have hX : 0 < |U r n| := by
      have : U r n ^ 2 = (q : ℤ) ^ n - 2 := by omega
      have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq.ne_zero)
      have hge : (q : ℤ) ^ 2 ≤ (q : ℤ) ^ n :=
        pow_le_pow_right₀ hq1 (by omega)
      have hq3 : (3 : ℕ) ≤ q := by
        have : 2 ≤ q := hq.two_le
        have : q ≠ 2 := by
          intro h2; rw [h2] at hqodd
          exact Nat.not_odd_iff_even.mpr (by decide) hqodd
        omega
      have : (4 : ℤ) ≤ (q : ℤ) ^ 2 := by
        have : (3 : ℤ) ≤ q := by exact_mod_cast hq3
        nlinarith
      have : (0 : ℤ) < U r n ^ 2 := by linarith
      exact abs_pos.mpr (sq_pos_iff.mp this)
    have hqabs : (q : ℤ) = (|r|) ^ 2 + 2 := by rw [sq_abs, hqZ]
    have hUabs : |U r n| ^ 2 + 2 = (q : ℤ) ^ n := by rw [sq_abs]; exact hUeq
    haveI : Fact q.Prime := ⟨hq⟩
    have hq5 : 5 ≤ q := by
      have : (6 : ℤ) ≤ r ^ 2 + 2 := by nlinarith [sq_abs r, hr2]
      have : (6 : ℤ) ≤ q := by
        rwa [← hqZ] at this
      have : 6 ≤ q := by exact_mod_cast this
      omega
    have hoddn : Odd n := Nat.not_even_iff_odd.mp (by
      intro he
      exact V_ne_one_of_even hr2 (by omega) he hV)
    have hn3 : 3 ≤ n := by
      obtain ⟨k, hk⟩ := hoddn
      omega
    exact (PellNegTwo.no_q_pow_pell hqabs hr2 hqodd hq5 hoddn hn3 hX hUabs).elim

end Zsqrtm2




/- The only solution of q^b - p^a = 2 with primes p, q and a, b > 1 is 3^3 - 5^2 = 2. -/

lemma nat_odd_to_int {t : ℕ} (h : Odd t) : Odd (t : ℤ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  exact_mod_cast hk

lemma eq_five_pow_two_of_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 < e)
    (h : p ^ e = 25) : p = 5 ∧ e = 2 := by
  have hdiv : p ∣ 25 := by
    rw [← h]
    exact dvd_pow_self p (by omega)
  have hp5 : p = 5 := by
    have : p ∣ 5 ^ 2 := by simpa using hdiv
    have : p ∣ 5 := (hp.dvd_of_dvd_pow this)
    exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp this).resolve_left hp.ne_one
  subst hp5
  have : (5 : ℕ) ^ e = 5 ^ 2 := h
  have : e = 2 := (Nat.pow_right_injective (by decide : 1 < 5)) this
  exact ⟨rfl, this⟩

/- Case 3: both exponents odd and at least 3. -/

lemma add_one_pow_sub_pow_ge_three {y n : ℕ} (hn : 2 ≤ n) (hy : 1 ≤ y) :
    3 ≤ (y + 1) ^ n - y ^ n := by
  have hZ : (3 : ℤ) ≤ ((y + 1 : ℕ) : ℤ) ^ n - (y : ℤ) ^ n := by
    have hnm : n = n - 2 + 2 := by omega
    have hsq : ((y + 1 : ℕ) : ℤ) ^ 2 - (y : ℤ) ^ 2 = 2 * y + 1 := by
      push_cast; ring
    have hle : (y : ℤ) ^ (n - 2) ≤ ((y + 1 : ℕ) : ℤ) ^ (n - 2) := by
      exact_mod_cast Nat.pow_le_pow_left (Nat.le_succ y) (n - 2)
    have hdecomp : ((y + 1 : ℕ) : ℤ) ^ n - (y : ℤ) ^ n
        = ((y + 1 : ℕ) : ℤ) ^ (n - 2) * ((y + 1 : ℕ) : ℤ) ^ 2
          - (y : ℤ) ^ (n - 2) * (y : ℤ) ^ 2 := by
      conv_lhs => rw [hnm]
      rw [pow_add, pow_add]
    have hge : ((y + 1 : ℕ) : ℤ) ^ (n - 2) * (((y + 1 : ℕ) : ℤ) ^ 2 - (y : ℤ) ^ 2)
        ≤ ((y + 1 : ℕ) : ℤ) ^ (n - 2) * ((y + 1 : ℕ) : ℤ) ^ 2
          - (y : ℤ) ^ (n - 2) * (y : ℤ) ^ 2 := by
      nlinarith
    have ha : (1 : ℤ) ≤ ((y + 1 : ℕ) : ℤ) ^ (n - 2) := by
      exact_mod_cast (Nat.one_le_pow (n - 2) (y + 1) (by omega))
    nlinarith
  have hnn : y ^ n ≤ (y + 1) ^ n := Nat.pow_le_pow_left (Nat.le_succ y) n
  exact_mod_cast hZ

lemma pow_sub_pow_ge_three {x y n : ℕ} (hn : 2 ≤ n) (hy : 1 ≤ y) (hxy : y < x) :
    3 ≤ x ^ n - y ^ n := by
  have hx : y + 1 ≤ x := by omega
  have hle : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left hx n
  have hgap := add_one_pow_sub_pow_ge_three hn hy
  omega

lemma pow_sub_pow_ne_two {x y n : ℕ} (hn : 2 ≤ n) (hy : 1 ≤ y) (hxy : y < x) :
    x ^ n - y ^ n ≠ 2 := by
  have := pow_sub_pow_ge_three hn hy hxy
  omega

lemma gcd_exponents_eq_one {p q ea eb : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (_hea : 2 ≤ ea) (_heb : 2 ≤ eb)
    (hdiff : q ^ eb = p ^ ea + 2) : Nat.gcd ea eb = 1 := by
  let d := Nat.gcd ea eb
  have hd_dvd_a : d ∣ ea := Nat.gcd_dvd_left ea eb
  have hd_dvd_b : d ∣ eb := Nat.gcd_dvd_right ea eb
  obtain ⟨ea', hea'⟩ := hd_dvd_a
  obtain ⟨eb', heb'⟩ := hd_dvd_b
  have hp_pow : p ^ ea = (p ^ ea') ^ d := by
    rw [hea', mul_comm d ea', pow_mul]
  have hq_pow : q ^ eb = (q ^ eb') ^ d := by
    rw [heb', mul_comm d eb', pow_mul]
  have hpow : (q ^ eb') ^ d = (p ^ ea') ^ d + 2 := by
    rwa [← hq_pow, ← hp_pow]
  by_contra hne
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left eb (by omega)
  have hd2 : 2 ≤ d := by
    have : d ≠ 1 := hne
    omega
  have hbase : 0 < p ^ ea' := pow_pos (by omega) _
  have hqp : p ^ ea' < q ^ eb' := by
    have hlt' : (p ^ ea') ^ d < (q ^ eb') ^ d := by omega
    exact (Nat.pow_lt_pow_iff_left (Nat.ne_of_gt hdpos)).mp hlt'
  have hy : 1 ≤ p ^ ea' := hbase
  apply pow_sub_pow_ne_two (x := q ^ eb') (y := p ^ ea') (n := d) hd2 hy hqp
  omega

lemma cubes_diff_two {x y : ℕ} (h : x ^ 3 = y ^ 3 + 2) : False := by
  have hyx : y < x := by
    by_contra hle
    have : x ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left (Nat.le_of_not_lt hle) 3
    omega
  rcases Nat.eq_zero_or_pos y with hy0 | hy1
  · subst hy0
    have : x ^ 3 = 2 := h
    have hxle : x ≤ 1 := by
      by_contra hx
      have : 2 ≤ x := by omega
      have : 8 ≤ x ^ 3 := calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ x ^ 3 := Nat.pow_le_pow_left this 3
      omega
    interval_cases x <;> norm_num at this
  · exact pow_sub_pow_ne_two (by decide : (2 : ℕ) ≤ 3) hy1 hyx (by omega)

lemma add_one_pow_gt_pow_add_two {p a : ℕ} (hp : 2 ≤ p) (ha : 3 ≤ a) :
    p ^ a + 2 < (p + 1) ^ a := by
  have hgap := add_one_pow_sub_pow_ge_three (y := p) (n := a) (by omega) (by omega)
  omega

lemma odd_primes_lt_sub_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hlt : q < p) : q ≤ p - 2 := by
  have hp_odd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hq_odd : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  have hne : q ≠ p - 1 := by
    intro heq
    obtain ⟨k, hk⟩ := hp_odd
    have heven : Even (p - 1) := by
      rw [hk, Nat.add_sub_cancel]
      exact even_two_mul _
    have : Even q := by simpa [heq] using heven
    exact Nat.not_even_iff_odd.mpr hq_odd this
  omega

lemma pow_add_two_not_self_pow {r ea eb : ℕ} (hr : 2 ≤ r) (hea : 3 ≤ ea) (hlt : ea < eb)
    (h : r ^ eb = r ^ ea + 2) : False := by
  have hle : ea ≤ eb := Nat.le_of_lt hlt
  have hfactor : r ^ eb = r ^ ea * r ^ (eb - ea) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  have hsub0 : r ^ eb - r ^ ea = 2 := by
    rw [h, Nat.add_sub_cancel_left]
  have hsub : r ^ ea * r ^ (eb - ea) - r ^ ea = 2 := by
    rwa [hfactor] at hsub0
  have hmul : r ^ ea * (r ^ (eb - ea) - 1) = 2 := by
    rwa [Nat.mul_sub_one]
  have hge : 8 ≤ r ^ ea :=
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
      _ ≤ r ^ ea := Nat.pow_le_pow_right (by omega) hea
  have hpow2 : 2 ≤ r ^ (eb - ea) := by
    have : 0 < eb - ea := Nat.sub_pos_of_lt hlt
    exact Nat.le_trans hr (Nat.le_self_pow (Nat.ne_of_gt this) r)
  have hge1 : 1 ≤ r ^ (eb - ea) - 1 := by omega
  have : 8 ≤ r ^ ea * (r ^ (eb - ea) - 1) :=
    Nat.mul_le_mul hge hge1
  omega

lemma pow_lt_of_pow_lt_of_lt_exp {q p ea eb : ℕ} (hq : 1 < q) (hlt : ea < eb)
    (h : q ^ eb < (p + 1) ^ ea) : q < p + 1 := by
  by_contra hge
  have hle : p + 1 ≤ q := by omega
  have h1 : (p + 1) ^ eb ≤ q ^ eb := Nat.pow_le_pow_left hle eb
  by_cases hp0 : p + 1 ≤ 1
  · have : p + 1 = 0 ∨ p + 1 = 1 := by omega
    rcases this with hz | h1'
    · cases ea with
      | zero =>
        have : 1 ≤ q ^ eb := Nat.one_le_pow eb q (by omega)
        simp [hz] at h
        omega
      | succ ea =>
        simp [hz] at h
    · rw [h1'] at h
      have : 1 ≤ q ^ eb := Nat.one_le_pow eb q (by omega)
      simp at h
      omega
  · have hp1 : 1 < p + 1 := by omega
    have h2 : (p + 1) ^ ea < (p + 1) ^ eb := Nat.pow_lt_pow_right hp1 hlt
    omega


lemma cubes_mod_nine (n : ℕ) : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by
  have : n % 9 < 9 := Nat.mod_lt n (by decide)
  have heq : n ^ 3 % 9 = (n % 9) ^ 3 % 9 := by rw [Nat.pow_mod]
  rw [heq]
  interval_cases n % 9 <;> norm_num

lemma not_cube_mod_nine_seven {n : ℕ} (h : n ^ 3 % 9 = 7) : False := by
  have := cubes_mod_nine n
  omega

/-- `q = 3`, `ea = 3`: `p^3 ≡ 7 [MOD 9]` is impossible. -/
lemma no_three_pow_sub_cube {p eb : ℕ} (heb : 2 ≤ eb)
    (hdiff : (3 : ℕ) ^ eb = p ^ 3 + 2) : False := by
  have hmod : (3 : ℕ) ^ eb % 9 = (p ^ 3 + 2) % 9 := by rw [hdiff]
  have h3 : (3 : ℕ) ^ eb % 9 = 0 := by
    have : 2 ≤ eb := heb
    have hdiv : 9 ∣ 3 ^ eb := by
      have : 3 ^ 2 ∣ 3 ^ eb := Nat.pow_dvd_pow 3 this
      simpa using this
    exact Nat.mod_eq_zero_of_dvd hdiv
  have : p ^ 3 % 9 = 7 := by
    have : (p ^ 3 + 2) % 9 = 0 := by
      rw [h3] at hmod
      exact hmod.symm
    have := Nat.add_mod (p ^ 3) 2 9
    omega
  exact not_cube_mod_nine_seven this

lemma q_le_p_sub_two_of_lt {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 3 ≤ ea)
    (hlt : q ^ eb < (p + 1) ^ ea) (hltab : ea < eb)
    (hdiff : q ^ eb = p ^ ea + 2)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) : q ≤ p - 2 := by
  have hq1 : 1 < q := hq.one_lt
  have hqp : q < p + 1 := pow_lt_of_pow_lt_of_lt_exp hq1 hltab hlt
  have hne : q ≠ p := by
    intro heq
    subst heq
    exact pow_add_two_not_self_pow hq.two_le hea hltab hdiff
  have hlt' : q < p := by omega
  exact odd_primes_lt_sub_two hp hq hp2 hq2 hlt'

/-! ### Parity constraints for the even-`eb` equation `Y^2 = p^n + 2` -/

lemma odd_sq_mod_eight {n : ℕ} (h : Odd n) : n ^ 2 % 8 = 1 := by
  have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have : n % 2 = 1 := Nat.odd_iff.mp h
    have : n % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

lemma odd_pow_mod_eight_self {a n : ℕ} (ha : Odd a) (hn : Odd n) :
    a ^ n % 8 = a % 8 := by
  have ha8 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    have : a % 2 = 1 := Nat.odd_iff.mp ha
    have : a % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => simp
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [this, pow_add, Nat.mul_mod, ih]
    rcases ha8 with h | h | h | h <;> simp [Nat.pow_mod, h]

/-- If `Y^2 = p^n + 2` with `p` an odd prime and `n` odd, then `p ≡ 7 [MOD 8]`. -/
lemma p_mod_eight_of_sq_eq_pow_add_two {Y p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : Odd n) (h : Y ^ 2 = p ^ n + 2) :
    p % 8 = 7 := by
  have hpO : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hY : Odd Y := by
    have hpn : Odd (p ^ n) := Odd.pow hpO
    have : Odd (p ^ n + 2) := by
      rw [Nat.odd_add]; exact iff_of_true hpn even_two
    have : Odd (Y ^ 2) := by rwa [h]
    simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this
  have hY8 : Y ^ 2 % 8 = 1 := odd_sq_mod_eight hY
  have hpn8 : p ^ n % 8 = p % 8 := odd_pow_mod_eight_self hpO hn
  have : (p ^ n + 2) % 8 = 1 := by rw [← h, hY8]
  have : (p % 8 + 2) % 8 = 1 := by
    rw [Nat.add_mod, hpn8] at this; exact this
  have hp8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
    have : p % 2 = 1 := Nat.odd_iff.mp hpO
    have : p % 8 < 8 := Nat.mod_lt _ (by decide)
    omega
  rcases hp8 with h8 | h8 | h8 | h8 <;> simp [h8] at this ⊢

lemma both_odd_mod_eight {p q ea eb : ℕ}
    (hpO : Odd p) (hqO : Odd q) (heaO : Odd ea) (hebO : Odd eb)
    (hdiff : q ^ eb = p ^ ea + 2) : q % 8 = (p + 2) % 8 := by
  have hq8 : q ^ eb % 8 = q % 8 := odd_pow_mod_eight_self hqO hebO
  have hp8 : p ^ ea % 8 = p % 8 := odd_pow_mod_eight_self hpO heaO
  have : (q ^ eb) % 8 = (p ^ ea + 2) % 8 := by rw [hdiff]
  rw [hq8, Nat.add_mod, hp8] at this
  rwa [Nat.add_mod]

lemma odd_mod_eight {n : ℕ} (h : Odd n) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  have : n % 2 = 1 := Nat.odd_iff.mp h
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  omega

lemma q_ne_p_sub_two_of_mod_eight {p q : ℕ}
    (hpO : Odd p) (hp2 : 2 ≤ p) (hmod : q % 8 = (p + 2) % 8) : q ≠ p - 2 := by
  intro heq
  have h8 := odd_mod_eight hpO
  have hp8 : p % 8 < 8 := Nat.mod_lt _ (by decide)
  have : (p - 2) % 8 = (p + 2) % 8 := by
    rw [← heq, hmod]
  rcases h8 with h | h | h | h
  · -- p ≡ 1, p-2 ≡ 7, p+2 ≡ 3
    have : p % 8 = 1 := h
    have h2 : 2 ≤ p := hp2
    omega
  · have : p % 8 = 3 := h
    omega
  · have : p % 8 = 5 := h
    omega
  · have : p % 8 = 7 := h
    omega

lemma q_ne_p_sub_four_of_mod_eight {p q : ℕ}
    (hpO : Odd p) (hp4 : 4 ≤ p) (hmod : q % 8 = (p + 2) % 8) : q ≠ p - 4 := by
  intro heq
  have h8 := odd_mod_eight hpO
  have : (p - 4) % 8 = (p + 2) % 8 := by
    rw [← heq, hmod]
  rcases h8 with h | h | h | h
  · have : p % 8 = 1 := h; omega
  · have : p % 8 = 3 := h; omega
  · have : p % 8 = 5 := h; omega
  · have : p % 8 = 7 := h; omega

lemma q_le_p_sub_six_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hlt : q < p)
    (hmod : q % 8 = (p + 2) % 8) : q ≤ p - 6 := by
  have hle : q ≤ p - 2 := odd_primes_lt_sub_two hp hq hp2 hq2 hlt
  have hpO : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hne : q ≠ p - 2 := q_ne_p_sub_two_of_mod_eight hpO hp.two_le hmod
  have hp4 : 4 ≤ p := by
    have hp3 : 3 ≤ p := by
      have : 2 ≤ p := hp.two_le
      omega
    have hq3 : 3 ≤ q := by
      have : 2 ≤ q := hq.two_le
      omega
    omega
  have hne4 : q ≠ p - 4 := q_ne_p_sub_four_of_mod_eight hpO hp4 hmod
  omega

/-- For `b = 3` and `a ≥ 5`, `(p+2)^3 < p^5 ≤ p^a`. -/
lemma twin_cube_lt {p : ℕ} (hp : 3 ≤ p) :
    (p + 2) ^ 3 + 2 < p ^ 5 := by
  have hZ : ((p + 2 : ℕ) : ℤ) ^ 3 + 2 < (p : ℤ) ^ 5 := by
    have hp3 : (3 : ℤ) ≤ p := by exact_mod_cast hp
    have h1 : (p : ℤ) ^ 2 ≥ 9 := by nlinarith
    have h2 : (p : ℤ) ^ 3 ≥ 27 := by nlinarith
    have h3 : (p : ℤ) ^ 5 = (p : ℤ) ^ 3 * (p : ℤ) ^ 2 := by ring
    have h4 : ((p + 2 : ℕ) : ℤ) ^ 3 = (p : ℤ) ^ 3 + 6 * (p : ℤ) ^ 2 + 12 * p + 8 := by
      push_cast; ring
    rw [h3, h4]
    nlinarith
  exact_mod_cast hZ

lemma three_pow_gt_two_mul_nine_pow {ea : ℕ} (hea : 7 ≤ ea) :
    3 * 9 ^ ea < 11 ^ ea := by
  sorry


lemma p_ge_eleven_of_q_three {p ea eb : ℕ}
    (hp : p.Prime) (hea : 5 ≤ ea) (hdiff : (3 : ℕ) ^ eb = p ^ ea + 2)
    (hqp : 3 ≤ p - 2) : 11 ≤ p := by
  sorry

/-- If `q = 3` and `3 ∣ ea`, then `p^{ea} ≡ 7 [MOD 9]`, impossible for a cube. -/
lemma three_dvd_ea_q_three {p ea eb : ℕ}
    (hea : 3 ≤ ea) (h3 : 3 ∣ ea) (heb : 2 ≤ eb)
    (hdiff : (3 : ℕ) ^ eb = p ^ ea + 2) : False := by
  obtain ⟨k, hk⟩ := h3
  have hcube : p ^ ea = (p ^ k) ^ 3 := by rw [hk, mul_comm, pow_mul]
  have hmod : (3 : ℕ) ^ eb % 9 = 0 := by
    have hdiv : 9 ∣ 3 ^ eb := by
      have : 3 ^ 2 ∣ 3 ^ eb := Nat.pow_dvd_pow 3 heb
      simpa using this
    exact Nat.mod_eq_zero_of_dvd hdiv
  have : (p ^ k) ^ 3 % 9 = 7 := by
    have : (p ^ ea + 2) % 9 = 0 := by
      have : (3 : ℕ) ^ eb % 9 = (p ^ ea + 2) % 9 := by rw [hdiff]
      omega
    have : (p ^ ea) % 9 = 7 := by
      have := Nat.add_mod (p ^ ea) 2 9
      omega
    rwa [hcube] at this
  exact not_cube_mod_nine_seven this

/-- `q = 3`, `3 ∤ ea`, `ea ≥ 5`: no solutions of `3^{eb} = p^{ea} + 2`. -/
lemma both_odd_q_three_large {p ea eb : ℕ}
    (hp : p.Prime) (hea5 : 5 ≤ ea) (heaO : Odd ea) (heb : 3 ≤ eb) (hebO : Odd eb)
    (h3ea : ¬ 3 ∣ ea) (hqp6 : 3 ≤ p - 6)
    (hdiff : (3 : ℕ) ^ eb = p ^ ea + 2) : False := by
  sorry

/-- `q ≥ 5`, `ea < eb`, both odd `≥ 3`. -/
lemma both_odd_q_ge_five {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 3 ≤ ea) (heb : 3 ≤ eb)
    (heaO : Odd ea) (hebO : Odd eb)
    (hq3 : q ≠ 3) (hq5 : 5 ≤ q) (hqp6 : q ≤ p - 6)
    (hltab : ea < eb) (hdiff : q ^ eb = p ^ ea + 2) : False := by
  sorry

/-- `eb < ea`, both odd `≥ 3`. -/
lemma both_odd_gt_main {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 3 ≤ ea) (heb : 3 ≤ eb)
    (heaO : Odd ea) (hebO : Odd eb)
    (hgt : eb < ea) (hdiff : q ^ eb = p ^ ea + 2) : False := by
  sorry

lemma both_odd_lt {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 3 ≤ ea) (heb : 3 ≤ eb)
    (heaO : Odd ea) (hebO : Odd eb)
    (_hgcd : Nat.gcd ea eb = 1)
    (hlt : q ^ eb < (p + 1) ^ ea) (hltab : ea < eb)
    (hdiff : q ^ eb = p ^ ea + 2) : False := by
  have hp2 : p ≠ 2 := by
    intro h2; subst h2
    have : Even (2 ^ ea) := Even.pow_of_ne_zero even_two (by omega)
    have : Even (q ^ eb) := by
      rw [hdiff]; exact Even.add this even_two
    have : q = 2 := prime_of_even_pow hq this
    subst this
    exact not_two_pow_diff_two (by omega) (by omega) hdiff
  have hq2 : q ≠ 2 := by
    intro h2; subst h2
    have : Even (2 ^ eb) := Even.pow_of_ne_zero even_two (by omega)
    have : Even (p ^ ea + 2) := by rwa [← hdiff]
    have : Even (p ^ ea) := by
      rw [Nat.even_add] at this
      exact this.mpr even_two
    exact hp2 (prime_of_even_pow hp this)
  have hqp : q ≤ p - 2 := q_le_p_sub_two_of_lt hp hq hea hlt hltab hdiff hp2 hq2
  have hpO : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hqO : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  have hmod : q % 8 = (p + 2) % 8 := both_odd_mod_eight hpO hqO heaO hebO hdiff
  have hqp_lt : q < p :=
    lt_of_le_of_lt hqp (Nat.sub_lt hp.pos (by decide : (0 : ℕ) < 2))
  have hqp6 : q ≤ p - 6 := q_le_p_sub_six_of_lt hp hq hp2 hq2 hqp_lt hmod
  by_cases hq3 : q = 3
  · subst hq3
    by_cases h3ea : 3 ∣ ea
    · exact three_dvd_ea_q_three hea h3ea (by omega) hdiff
    · -- q = 3, 3 ∤ ea, so ea ≥ 5
      have hea5 : 5 ≤ ea := by
        obtain ⟨k, hk⟩ := heaO
        omega
      exact both_odd_q_three_large hp hea5 heaO heb hebO h3ea hqp6 hdiff
  · -- q ≥ 5
    have hq5 : 5 ≤ q := by
      have : 2 ≤ q := hq.two_le
      have : q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q := by omega
      rcases this with rfl | rfl | rfl | h
      · exact (hq2 rfl).elim
      · exact (hq3 rfl).elim
      · exact absurd hq (by decide : ¬ Nat.Prime 4)
      · exact h
    exact both_odd_q_ge_five hp hq hea heb heaO hebO hq3 hq5 hqp6 hltab hdiff

lemma both_odd_gt {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 3 ≤ ea) (heb : 3 ≤ eb)
    (heaO : Odd ea) (hebO : Odd eb)
    (_hgcd : Nat.gcd ea eb = 1)
    (hlt : q ^ eb < (p + 1) ^ ea) (hgt : eb < ea)
    (hdiff : q ^ eb = p ^ ea + 2) : False := by
  exact both_odd_gt_main hp hq hea heb heaO hebO hgt hdiff

/-- The equation `q^b - p^a = 2` is impossible when both exponents are odd and at least 3. -/
lemma both_odd_exponents_impossible {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 3 ≤ ea) (heb : 3 ≤ eb)
    (heaO : Odd ea) (hebO : Odd eb)
    (hdiff : q ^ eb = p ^ ea + 2) : False := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hgcd : Nat.gcd ea eb = 1 :=
    gcd_exponents_eq_one hp2 hq2 (by omega) (by omega) hdiff
  have hlt : q ^ eb < (p + 1) ^ ea := by
    rw [hdiff]
    exact add_one_pow_gt_pow_add_two hp2 hea
  rcases lt_trichotomy ea eb with hltab | heq | hgt
  · exact both_odd_lt hp hq hea heb heaO hebO hgcd hlt hltab hdiff
  · subst heq
    have hp0 : 0 < p := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hp2
    have hpq : p < q := by
      have : p ^ ea < q ^ ea := by
        have : 0 < p ^ ea := pow_pos hp0 _
        omega
      exact (Nat.pow_lt_pow_iff_left (show ea ≠ 0 by omega)).mp this
    have hy : 1 ≤ p := by omega
    have hn2 : 2 ≤ ea := le_trans (by decide : (2 : ℕ) ≤ 3) hea
    have hsub : q ^ ea - p ^ ea = 2 := by
      rw [hdiff]; omega
    exact pow_sub_pow_ne_two (x := q) (y := p) (n := ea) hn2 hy hpq hsub
  · exact both_odd_gt hp hq hea heb heaO hebO hgcd hlt hgt hdiff


/-! ### Z[√2] theory (from mordell3) -/



abbrev Zsqrt2 := ℤ√(2 : ℤ)

namespace Zsqrt2

lemma two_not_sq : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n h
  have hsq : n ^ 2 = 2 := by rw [sq]; exact h.symm
  have habs : |n| ≤ 1 := by
    have : n ^ 2 < (2 : ℤ) ^ 2 := by nlinarith
    have : |n| < 2 := lt_of_pow_lt_pow_left₀ 2 (by decide : (0 : ℤ) ≤ 2) (by rwa [sq_abs])
    have : 0 ≤ |n| := abs_nonneg _
    omega
  have : |n| = 0 ∨ |n| = 1 := by
    have : 0 ≤ |n| := abs_nonneg _
    omega
  rcases this with h0 | h1
  · rw [abs_eq_zero] at h0; subst h0; norm_num at hsq
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at hsq

lemma norm_eq (z : Zsqrt2) : z.norm = z.re ^ 2 - 2 * z.im ^ 2 := by
  rw [norm_def]; ring

lemma norm_eq_zero_iff' (z : Zsqrt2) : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero two_not_sq z

lemma int_abs_sub_mul_round (a N : ℤ) (hN : N ≠ 0) :
    |a - round ((a : ℚ) / N) * N| * 2 ≤ |N| := by
  have hNq : (N : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN
  set q := round ((a : ℚ) / N)
  have hle : |((a : ℚ) / N) - (q : ℚ)| ≤ 1 / 2 := abs_sub_round _
  have habs : |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)| = |(a : ℚ) - (q : ℚ) * N| := by
    calc
      |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)|
        = |(((a : ℚ) / N) - (q : ℚ)) * N| := (abs_mul _ _).symm
      _ = |(a : ℚ) - (q : ℚ) * N| := by
            rw [sub_mul, div_mul_cancel₀ _ hNq]
  have hbound : |(a : ℚ) - (q : ℚ) * N| ≤ |(N : ℚ)| / 2 := by
    rw [← habs]
    have := mul_le_mul_of_nonneg_right hle (abs_nonneg (N : ℚ))
    linarith
  have hcast : ((a - q * N : ℤ) : ℚ) = (a : ℚ) - (q : ℚ) * N := by push_cast; rfl
  have : ((|a - q * N| * 2 : ℤ) : ℚ) ≤ ((|N| : ℤ) : ℚ) := by
    rw [Int.cast_mul, Int.cast_abs, Int.cast_two, hcast, Int.cast_abs]
    linarith
  exact_mod_cast this

noncomputable instance : Div Zsqrt2 :=
  ⟨fun x y =>
    ⟨round ((x * star y).re / (y.norm : ℚ)),
     round ((x * star y).im / (y.norm : ℚ))⟩⟩

lemma div_def (x y : Zsqrt2) :
    x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
             round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := rfl

noncomputable instance : Mod Zsqrt2 := ⟨fun x y => x - y * (x / y)⟩

lemma mod_def (x y : Zsqrt2) : x % y = x - y * (x / y) := rfl

lemma rem_mul_star (x y : Zsqrt2) :
    (x % y) * star y = x * star y - (x / y) * (y.norm : Zsqrt2) := by
  rw [mod_def, sub_mul, norm_eq_mul_conj]
  ring

lemma rem_norm_mul (x y : Zsqrt2) :
    (x % y).norm * y.norm = (x * star y - (x / y) * (y.norm : Zsqrt2)).norm := by
  have := rem_mul_star x y
  rw [← this, Zsqrtd.norm_mul, Zsqrtd.norm_conj]

lemma mul_intCast_re (z : Zsqrt2) (n : ℤ) :
    (z * (n : Zsqrt2)).re = z.re * n := by
  simp [Zsqrtd.re_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma mul_intCast_im (z : Zsqrt2) (n : ℤ) :
    (z * (n : Zsqrt2)).im = z.im * n := by
  simp [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma rem_norm_expand (x y : Zsqrt2) :
    (x * star y - (x / y) * (y.norm : Zsqrt2)).norm =
      ((x * star y).re - (x / y).re * y.norm) ^ 2 -
      2 * ((x * star y).im - (x / y).im * y.norm) ^ 2 := by
  rw [norm_eq, re_sub, im_sub, mul_intCast_re, mul_intCast_im]

lemma four_mul_abs_form {A B N : ℤ} (hA : |A| * 2 ≤ |N|) (hB : |B| * 2 ≤ |N|) :
    4 * |A ^ 2 - 2 * B ^ 2| ≤ 3 * N ^ 2 := by
  have hA4 : 4 * A ^ 2 ≤ N ^ 2 := by
    have : |2 * A| ≤ |N| := by
      rw [abs_mul, abs_two, mul_comm]
      exact hA
    have : (2 * A) ^ 2 ≤ N ^ 2 := sq_le_sq.mpr this
    nlinarith
  have hB4 : 4 * B ^ 2 ≤ N ^ 2 := by
    have : |2 * B| ≤ |N| := by
      rw [abs_mul, abs_two, mul_comm]
      exact hB
    have : (2 * B) ^ 2 ≤ N ^ 2 := sq_le_sq.mpr this
    nlinarith
  have hsum : 4 * (A ^ 2 + 2 * B ^ 2) ≤ 3 * N ^ 2 := by nlinarith
  have hle : |A ^ 2 - 2 * B ^ 2| ≤ A ^ 2 + 2 * B ^ 2 :=
    abs_sub_le_iff.mpr ⟨by nlinarith [sq_nonneg A, sq_nonneg B],
      by nlinarith [sq_nonneg A, sq_nonneg B]⟩
  nlinarith

lemma abs_norm_mod_lt (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    |(x % y).norm| < |y.norm| := by
  have hNne : y.norm ≠ 0 := by
    intro h0
    exact hy ((norm_eq_zero_iff' y).mp h0)
  set N := y.norm
  set α := x * star y
  set q := x / y
  have hre : |α.re - q.re * N| * 2 ≤ |N| := by
    change |α.re - round ((α.re : ℚ) / N) * N| * 2 ≤ |N|
    exact int_abs_sub_mul_round α.re N hNne
  have him : |α.im - q.im * N| * 2 ≤ |N| := by
    change |α.im - round ((α.im : ℚ) / N) * N| * 2 ≤ |N|
    exact int_abs_sub_mul_round α.im N hNne
  have h4 : 4 * |(α.re - q.re * N) ^ 2 - 2 * (α.im - q.im * N) ^ 2| ≤ 3 * N ^ 2 :=
    four_mul_abs_form hre him
  have hmul : (x % y).norm * N = (α - q * (N : Zsqrt2)).norm := rem_norm_mul x y
  have hexp : (α - q * (N : Zsqrt2)).norm =
      (α.re - q.re * N) ^ 2 - 2 * (α.im - q.im * N) ^ 2 := rem_norm_expand x y
  have : 4 * |(x % y).norm * N| ≤ 3 * N ^ 2 := by
    rw [hmul, hexp]; exact h4
  have hassoc : 4 * |(x % y).norm * N| = 4 * |(x % y).norm| * |N| := by
    rw [abs_mul, mul_assoc]
  rw [hassoc] at this
  have hNabs : 0 < |N| := abs_pos.mpr hNne
  have hNsq : N ^ 2 = |N| * |N| := by rw [← sq_abs, sq]
  have hle : 4 * |(x % y).norm| ≤ 3 * |N| := by
    have hmul' : 4 * |(x % y).norm| * |N| ≤ 3 * (|N| * |N|) := by
      rwa [hNsq] at this
    have hmul'' : 4 * |(x % y).norm| * |N| ≤ (3 * |N|) * |N| := by
      convert hmul' using 1; ring
    exact _root_.le_of_mul_le_mul_right hmul'' hNabs
  nlinarith

lemma natAbs_norm_mod_lt (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := abs_norm_mod_lt x hy
  have e1 : ((x % y).norm.natAbs : ℤ) = |(x % y).norm| := Int.natCast_natAbs _
  have e2 : (y.norm.natAbs : ℤ) = |y.norm| := Int.natCast_natAbs _
  have : ((x % y).norm.natAbs : ℤ) < (y.norm.natAbs : ℤ) := by
    rwa [e1, e2]
  exact_mod_cast this

lemma natAbs_norm_mul_left (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have : 1 ≤ y.norm.natAbs := by
    have : y.norm ≠ 0 := by
      intro h0
      exact hy ((norm_eq_zero_iff' y).mp h0)
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr this)
  exact Nat.le_mul_of_pos_right _ this

noncomputable instance : EuclideanDomain Zsqrt2 :=
  { inferInstanceAs (CommRing Zsqrt2),
    inferInstanceAs (Nontrivial Zsqrt2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp [div_def, Zsqrtd.norm_zero]
      rfl
    quotient_mul_add_remainder_eq := fun _ _ => by
      simp [mod_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (natAbs_norm_mul_left a hb0) }

def eps : Zsqrt2 := ⟨1, 1⟩

lemma eps_norm : (eps : Zsqrt2).norm = -1 := by
  simp [eps, norm_eq]

lemma eps_mul_conj : eps * ⟨-1, 1⟩ = 1 := by
  ext <;> simp [eps]

lemma isUnit_eps : IsUnit (eps : Zsqrt2) :=
  ⟨⟨eps, ⟨-1, 1⟩, eps_mul_conj, by ext <;> simp [eps]⟩, rfl⟩

def epsInv : Zsqrt2 := ⟨-1, 1⟩

lemma eps_mul_epsInv : eps * epsInv = 1 := eps_mul_conj

lemma epsInv_mul_eps : epsInv * eps = 1 := by
  rw [mul_comm]; exact eps_mul_epsInv

lemma eps_sq : (eps : Zsqrt2) ^ 2 = ⟨3, 2⟩ := by
  ext <;> simp [eps, pow_two]

lemma two_not_isSquare : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨k, hk⟩
  exact two_not_sq k hk

def fund : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

lemma fund_x : fund.x = 3 := Pell.Solution₁.x_mk 3 2 (by norm_num)
lemma fund_y : fund.y = 2 := Pell.Solution₁.y_mk 3 2 (by norm_num)

lemma fund_isFundamental : Pell.IsFundamental fund := by
  refine ⟨?hx, ?hy, ?min⟩
  · rw [fund_x]; norm_num
  · rw [fund_y]; norm_num
  · intro b hb
    have hprop := b.prop
    have hx2 : (2 : ℤ) ≤ b.x := by linarith
    have hb3 : (3 : ℤ) ≤ b.x := by
      by_contra h
      have hxeq : b.x = 2 := by omega
      rw [hxeq] at hprop
      have : (2 : ℤ) * b.y ^ 2 = 3 := by linarith
      have hy0 : b.y ^ 2 = 0 ∨ b.y ^ 2 = 1 ∨ (4 : ℤ) ≤ b.y ^ 2 := by
        have : 0 ≤ b.y ^ 2 := sq_nonneg _
        have : b.y ^ 2 ≤ 1 ∨ 4 ≤ b.y ^ 2 := by
          have habs : |b.y| ≤ 1 ∨ 2 ≤ |b.y| := by omega
          rcases habs with h1 | h2
          · left; have := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1); simpa using this
          · right
            have : (2 : ℤ) ^ 2 ≤ |b.y| ^ 2 := pow_le_pow_left₀ (by omega) h2 2
            simpa [sq_abs] using this
        omega
      rcases hy0 with h0 | h1 | h4 <;> linarith
    simpa [fund_x] using hb3

lemma fund_coe : (fund : Zsqrt2) = ⟨3, 2⟩ := by
  simp [fund, Pell.Solution₁.coe_mk]

lemma fund_eq_eps_sq : (fund : Zsqrt2) = eps ^ 2 :=
  fund_coe.trans eps_sq.symm

lemma isUnit_of_natAbs_norm_one (z : Zsqrt2) (h : z.norm.natAbs = 1) : IsUnit z :=
  Zsqrtd.norm_eq_one_iff.mp h

lemma natAbs_norm_eq_one_of_isUnit {z : Zsqrt2} (h : IsUnit z) : z.norm.natAbs = 1 :=
  Zsqrtd.norm_eq_one_iff.mpr h

lemma norm_eq_one_or_neg_one_of_isUnit {z : Zsqrt2} (h : IsUnit z) :
    z.norm = 1 ∨ z.norm = -1 :=
  Int.natAbs_eq_iff.mp (natAbs_norm_eq_one_of_isUnit h)

lemma eq_fund_zpow_of_norm_one {z : Zsqrt2} (h : z.norm = 1) :
    ∃ k : ℤ, z = ((fund ^ k : Pell.Solution₁ 2) : Zsqrt2) ∨
      z = -((fund ^ k : Pell.Solution₁ 2) : Zsqrt2) := by
  let a : Pell.Solution₁ 2 :=
    Pell.Solution₁.mk z.re z.im (by
      have : z.re ^ 2 - 2 * z.im ^ 2 = 1 := by rw [← norm_eq, h]
      exact this)
  have ha : (a : Zsqrt2) = z := by
    ext <;> simp [a, Pell.Solution₁.coe_mk]
  obtain ⟨k, hk⟩ := fund_isFundamental.eq_zpow_or_neg_zpow a
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · left; rw [← ha, hk]
  · right; rw [← ha, hk]; rfl

lemma epsInv_sq : (epsInv : Zsqrt2) ^ 2 = ⟨3, -2⟩ := by
  ext <;> simp [epsInv, pow_two]

def ω : Zsqrt2 := ⟨0, 1⟩

lemma ω_sq : (ω * ω : Zsqrt2) = (2 : Zsqrt2) := by
  ext <;> simp [ω]

lemma norm_ω : ω.norm = -2 := by simp [ω, norm_eq]

def plus (y : ℤ) : Zsqrt2 := ⟨y, 1⟩
def minus (y : ℤ) : Zsqrt2 := ⟨y, -1⟩

lemma plus_mul_minus (y : ℤ) : plus y * minus y = ⟨y ^ 2 - 2, 0⟩ := by
  ext
  · simp [plus, minus]; ring
  · simp [plus, minus]

lemma intCast_mk (n : ℤ) : (n : Zsqrt2) = ⟨n, 0⟩ := by
  ext <;> simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma plus_mul_minus' (y : ℤ) : plus y * minus y = (y ^ 2 - 2 : ℤ) := by
  rw [plus_mul_minus, intCast_mk]

lemma plus_sub_minus (y : ℤ) : plus y - minus y = ⟨0, 2⟩ := by
  ext <;> simp [plus, minus]

lemma two_mul_ω : (2 : Zsqrt2) * ω = ⟨0, 2⟩ := by
  ext <;> simp [ω]

lemma plus_sub_minus' (y : ℤ) : plus y - minus y = (2 : Zsqrt2) * ω := by
  rw [plus_sub_minus, two_mul_ω]

lemma star_plus (y : ℤ) : star (plus y) = minus y := by
  ext <;> simp [plus, minus]

lemma norm_plus (y : ℤ) : (plus y).norm = y ^ 2 - 2 := by
  simp [plus, norm_eq]

lemma plus_ne_zero {y : ℤ} (h : y ^ 2 ≠ 2) : plus y ≠ 0 := by
  intro hz
  have : (plus y).norm = 0 := by rw [hz]; simp [norm_def]
  rw [norm_plus] at this
  exact h (by linarith)

lemma omega_dvd_plus_iff (y : ℤ) : ω ∣ plus y ↔ Even y := by
  constructor
  · intro ⟨z, hz⟩
    have hre : (plus y).re = (ω * z).re := congrArg Zsqrtd.re hz
    have : y = 2 * z.im := by
      simp [plus, ω] at hre
      linarith
    refine ⟨z.im, ?_⟩
    rw [this, two_mul]
  · intro ⟨k, hk⟩
    refine ⟨⟨1, k⟩, ?_⟩
    ext
    · simp [plus, ω, hk]; ring
    · simp [plus, ω]

lemma odd_not_omega_dvd_plus {y : ℤ} (hy : Odd y) : ¬ ω ∣ plus y := by
  rw [omega_dvd_plus_iff]
  exact Int.not_even_iff_odd.mpr hy

lemma not_isUnit_ω : ¬ IsUnit ω := by
  intro hu
  have : ω.norm.natAbs = 1 := natAbs_norm_eq_one_of_isUnit hu
  rw [norm_ω] at this
  norm_num at this

lemma omega_irreducible : Irreducible ω := by
  refine ⟨not_isUnit_ω, ?_⟩
  intro a b hab
  have hn : (a * b).norm = -2 := by rw [← hab, norm_ω]
  rw [Zsqrtd.norm_mul] at hn
  have hdiv : a.norm ∣ 2 := ⟨-b.norm, by linarith⟩
  have habs : a.norm.natAbs ∣ 2 := Int.natAbs_dvd_natAbs.mpr hdiv
  have : a.norm.natAbs = 1 ∨ a.norm.natAbs = 2 := by
    have := Nat.le_of_dvd (by decide : (0 : ℕ) < 2) habs
    interval_cases a.norm.natAbs <;> tauto
  rcases this with h | h
  · left; exact isUnit_of_natAbs_norm_one a h
  · right
    have : b.norm.natAbs = 1 := by
      have : (a.norm * b.norm).natAbs = 2 := by rw [hn]; norm_num
      rw [Int.natAbs_mul, h] at this
      omega
    exact isUnit_of_natAbs_norm_one b this

lemma omega_prime : Prime ω := Irreducible.prime omega_irreducible

lemma two_eq_omega_sq : (2 : Zsqrt2) = ω * ω := ω_sq.symm

lemma isCoprime_plus_minus {y : ℤ} (hy : Odd y) (hne : y ^ 2 ≠ 2) :
    IsCoprime (plus y) (minus y) := by
  refine isCoprime_of_irreducible_dvd ?_ ?_
  · exact not_and_of_not_left _ (plus_ne_zero hne)
  · intro π hπ hπplus hπminus
    have hdiff : π ∣ plus y - minus y := dvd_sub hπplus hπminus
    rw [plus_sub_minus'] at hdiff
    have hω3 : π ∣ ω ^ 3 := by
      have : (2 : Zsqrt2) * ω = ω ^ 3 := by
        rw [two_eq_omega_sq, pow_three]; ring
      rwa [this] at hdiff
    have hπω : π ∣ ω :=
      (Irreducible.prime hπ).dvd_of_dvd_pow (n := 3) hω3
    have : Associated π ω :=
      (Irreducible.dvd_irreducible_iff_associated hπ omega_irreducible).mp hπω
    exact odd_not_omega_dvd_plus hy (this.symm.dvd.trans hπplus)

lemma plus_associated_pow {y : ℤ} {p n : ℕ} (hy : Odd y)
    (h : (y ^ 2 - 2 : ℤ) = (p : ℤ) ^ n) :
    ∃ d : Zsqrt2, Associated (d ^ n) (plus y) := by
  have hne : y ^ 2 ≠ 2 := by
    intro hf
    have : (p : ℤ) ^ n = 0 := by linarith
    cases n with
    | zero => norm_num at this
    | succ n =>
      have : (p : ℤ) = 0 := pow_eq_zero this
      exact two_not_sq y (by rw [← sq]; exact hf.symm)
  have hab : IsCoprime (plus y) (minus y) := isCoprime_plus_minus hy hne
  have hmul : plus y * minus y = ((p : ℤ) : Zsqrt2) ^ n := by
    rw [plus_mul_minus', h, Int.cast_pow]
  exact exists_associated_pow_of_mul_eq_pow' hab hmul

lemma s_dvd_im_pow (r s : ℤ) : ∀ n : ℕ, s ∣ ((⟨r, s⟩ : Zsqrt2) ^ n).im
  | 0 => by simp
  | n + 1 => by
    have ih := s_dvd_im_pow r s n
    have : ((⟨r, s⟩ : Zsqrt2) ^ (n + 1)).im =
        r * ((⟨r, s⟩ : Zsqrt2) ^ n).im + s * ((⟨r, s⟩ : Zsqrt2) ^ n).re := by
      rw [pow_succ, im_mul]; simp; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

lemma norm_pow (z : Zsqrt2) : ∀ n : ℕ, (z ^ n).norm = z.norm ^ n
  | 0 => by simp [norm_def]
  | n + 1 => by rw [pow_succ, pow_succ, Zsqrtd.norm_mul, norm_pow]

lemma s_dvd_one_of_plus_eq_pow {y r s : ℤ} {n : ℕ}
    (h : plus y = (⟨r, s⟩ : Zsqrt2) ^ n ∨ plus y = -((⟨r, s⟩ : Zsqrt2) ^ n)) :
    s ∣ 1 := by
  have him : (plus y).im = 1 := rfl
  have hs := s_dvd_im_pow r s n
  rcases h with h | h
  · rw [h] at him; rwa [← him]
  · have : (-((⟨r, s⟩ : Zsqrt2) ^ n)).im = -((⟨r, s⟩ : Zsqrt2) ^ n).im := by simp
    rw [h, this] at him
    have : s ∣ -((⟨r, s⟩ : Zsqrt2) ^ n).im := hs.neg_right
    rwa [him] at this

/-! ### Recurrence for `(a + √2)^n` -/

def UV2 (a : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let u := (UV2 a n).1
    let v := (UV2 a n).2
    (a * u + 2 * v, u + a * v)

def U2 (a : ℤ) (n : ℕ) : ℤ := (UV2 a n).1
def V2 (a : ℤ) (n : ℕ) : ℤ := (UV2 a n).2

lemma U2_zero (a : ℤ) : U2 a 0 = 1 := rfl
lemma V2_zero (a : ℤ) : V2 a 0 = 0 := rfl
lemma U2_succ (a : ℤ) (n : ℕ) : U2 a (n + 1) = a * U2 a n + 2 * V2 a n := rfl
lemma V2_succ (a : ℤ) (n : ℕ) : V2 a (n + 1) = U2 a n + a * V2 a n := rfl

lemma pow_eq_U2_V2 (a : ℤ) : ∀ n : ℕ,
    (⟨a, 1⟩ : Zsqrt2) ^ n = ⟨U2 a n, V2 a n⟩
  | 0 => by
    ext
    · simp [U2_zero]
    · simp [V2_zero]
  | n + 1 => by
    rw [pow_succ, pow_eq_U2_V2 a n, U2_succ, V2_succ]
    ext
    · simp; ring
    · simp; ring

lemma V2_one (a : ℤ) : V2 a 1 = 1 := by simp [V2_succ, U2_zero, V2_zero]
lemma U2_one (a : ℤ) : U2 a 1 = a := by simp [U2_succ, U2_zero, V2_zero]
lemma V2_two (a : ℤ) : V2 a 2 = 2 * a := by
  rw [V2_succ, U2_one, V2_one]; ring
lemma U2_two (a : ℤ) : U2 a 2 = a ^ 2 + 2 := by
  rw [U2_succ, U2_one, V2_one]; ring
lemma V2_three (a : ℤ) : V2 a 3 = 3 * a ^ 2 + 2 := by
  rw [V2_succ, U2_two, V2_two]; ring

lemma U2_V2_norm (a : ℤ) : ∀ n : ℕ,
    U2 a n ^ 2 - 2 * V2 a n ^ 2 = (a ^ 2 - 2) ^ n
  | 0 => by simp [U2_zero, V2_zero]
  | n + 1 => by
    have ih := U2_V2_norm a n
    calc
      U2 a (n + 1) ^ 2 - 2 * V2 a (n + 1) ^ 2
        = (a * U2 a n + 2 * V2 a n) ^ 2 - 2 * (U2 a n + a * V2 a n) ^ 2 := by
          rw [U2_succ, V2_succ]
      _ = (a ^ 2 - 2) * (U2 a n ^ 2 - 2 * V2 a n ^ 2) := by ring
      _ = (a ^ 2 - 2) * (a ^ 2 - 2) ^ n := by rw [ih]
      _ = (a ^ 2 - 2) ^ (n + 1) := (pow_succ' _ _).symm

/-! ### Binomial expansion of the imaginary part -/

lemma intCast_mk' (n : ℤ) : (⟨n, 0⟩ : Zsqrt2) = (n : Zsqrt2) := (intCast_mk n).symm

lemma omega_pow_even (j : ℕ) : (⟨0, 1⟩ : Zsqrt2) ^ (2 * j) = ⟨(2 : ℤ) ^ j, 0⟩ := by
  induction j with
  | zero =>
    ext <;> simp
  | succ j ih =>
    have : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [this, pow_add, ih, pow_two]
    ext <;> simp; ring

lemma omega_pow_odd (j : ℕ) : (⟨0, 1⟩ : Zsqrt2) ^ (2 * j + 1) = ⟨0, (2 : ℤ) ^ j⟩ := by
  rw [pow_succ, omega_pow_even]
  ext <;> simp

lemma re_pow_int (a : ℤ) (m : ℕ) : ((a : Zsqrt2) ^ m).re = a ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Zsqrtd.re_mul, ih]
    simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring

lemma im_pow_int (a : ℤ) (m : ℕ) : ((a : Zsqrt2) ^ m).im = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Zsqrtd.im_mul, ih]
    simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma im_mul_omega_pow (a : ℤ) (m i : ℕ) :
    ((a : Zsqrt2) ^ m * (⟨0, 1⟩ : Zsqrt2) ^ i).im =
      if Even i then 0 else a ^ m * (2 : ℤ) ^ (i / 2) := by
  by_cases he : Even i
  · rw [if_pos he]
    obtain ⟨j, rfl⟩ := he
    rw [show j + j = 2 * j by omega, omega_pow_even]
    simp [Zsqrtd.im_mul, im_pow_int]
  · rw [if_neg he]
    have hodd : Odd i := Nat.not_even_iff_odd.mp he
    obtain ⟨j, rfl⟩ := hodd
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [omega_pow_odd, hdiv]
    simp [Zsqrtd.im_mul, re_pow_int, im_pow_int]

lemma im_monomial (a : ℤ) (n i : ℕ) :
    ((a : Zsqrt2) ^ (n - i) * (⟨0, 1⟩ : Zsqrt2) ^ i).im =
      if Even i then 0 else a ^ (n - i) * (2 : ℤ) ^ (i / 2) :=
  im_mul_omega_pow a (n - i) i

lemma mk_a_one_eq (a : ℤ) : (⟨a, 1⟩ : Zsqrt2) = (a : Zsqrt2) + ⟨0, 1⟩ := by
  ext <;> simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma V2_eq_im_pow (a : ℤ) (n : ℕ) : V2 a n = ((⟨a, 1⟩ : Zsqrt2) ^ n).im := by
  rw [pow_eq_U2_V2]

lemma U2_eq_re_pow (a : ℤ) (n : ℕ) : U2 a n = ((⟨a, 1⟩ : Zsqrt2) ^ n).re := by
  rw [pow_eq_U2_V2]

lemma sq_mul_pow (a : ℤ) :
    (⟨a, 1⟩ : Zsqrt2) ^ 2 = ⟨a ^ 2 + 2, 2 * a⟩ := by
  ext <;> simp [pow_two]; ring

lemma U2_odd_succ (a : ℤ) (k : ℕ) :
    U2 a (2 * k + 3) = (a ^ 2 + 2) * U2 a (2 * k + 1) + 4 * a * V2 a (2 * k + 1) := by
  have hsplit : 2 * k + 3 = 2 + (2 * k + 1) := by omega
  have h : (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 3) =
      (⟨a, 1⟩ : Zsqrt2) ^ 2 * (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 1) := by
    rw [hsplit, pow_add]
  have h2 : (⟨U2 a (2 * k + 3), V2 a (2 * k + 3)⟩ : Zsqrt2) =
      ⟨a ^ 2 + 2, 2 * a⟩ * ⟨U2 a (2 * k + 1), V2 a (2 * k + 1)⟩ := by
    rw [← pow_eq_U2_V2, h, sq_mul_pow, pow_eq_U2_V2]
  have := congrArg Zsqrtd.re h2
  simp [Zsqrtd.re_mul] at this
  linarith

lemma V2_odd_succ (a : ℤ) (k : ℕ) :
    V2 a (2 * k + 3) = (a ^ 2 + 2) * V2 a (2 * k + 1) + 2 * a * U2 a (2 * k + 1) := by
  have hsplit : 2 * k + 3 = 2 + (2 * k + 1) := by omega
  have h : (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 3) =
      (⟨a, 1⟩ : Zsqrt2) ^ 2 * (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 1) := by
    rw [hsplit, pow_add]
  have h2 : (⟨U2 a (2 * k + 3), V2 a (2 * k + 3)⟩ : Zsqrt2) =
      ⟨a ^ 2 + 2, 2 * a⟩ * ⟨U2 a (2 * k + 1), V2 a (2 * k + 1)⟩ := by
    rw [← pow_eq_U2_V2, h, sq_mul_pow, pow_eq_U2_V2]
  have := congrArg Zsqrtd.im h2
  simp [Zsqrtd.im_mul] at this
  linarith

/-- For odd exponents, `V2` is nonnegative and `a * U2` is nonnegative. -/
lemma UV2_odd_nonneg (a : ℤ) : ∀ k : ℕ,
    0 ≤ a * U2 a (2 * k + 1) ∧ 0 ≤ V2 a (2 * k + 1)
  | 0 => by
    constructor
    · simp [U2_one]; exact mul_self_nonneg a
    · simp [V2_one]
  | k + 1 => by
    have ih := UV2_odd_nonneg a k
    constructor
    · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, U2_odd_succ]
      nlinarith [ih.1, ih.2, sq_nonneg a]
    · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, V2_odd_succ]
      nlinarith [ih.1, ih.2, sq_nonneg a]

lemma V2_odd_ge_two_pow (a : ℤ) : ∀ k : ℕ, (2 : ℤ) ^ k ≤ V2 a (2 * k + 1)
  | 0 => by simp [V2_one]
  | k + 1 => by
    have ih := V2_odd_ge_two_pow a k
    have hnn := UV2_odd_nonneg a k
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, V2_odd_succ, pow_succ]
    nlinarith [hnn.1, hnn.2, sq_nonneg a]

/-- If `n` is odd and at least 3, then `V2 a n ≥ 2`, hence `|V2 a n| ≠ 1`. -/
lemma V2_ne_one_of_odd {a : ℤ} {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    |V2 a n| ≠ 1 := by
  obtain ⟨k, hk⟩ := hodd
  have : n = 2 * k + 1 := by omega
  subst this
  have hk1 : 1 ≤ k := by omega
  have hge := V2_odd_ge_two_pow a k
  have h2 : (2 : ℤ) ≤ (2 : ℤ) ^ k := by
    have : 1 ≤ k := hk1
    exact le_trans (by decide : (2 : ℤ) ≤ 2 ^ 1) (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) this)
  intro habs
  have : V2 a (2 * k + 1) = 1 ∨ V2 a (2 * k + 1) = -1 := eq_or_eq_neg_of_abs_eq habs
  rcases this with h | h <;> linarith

/-- The `r = 0` case: `plus y = ± ⟨r,s⟩^n` forces `s = ±1` and then `|V2 r n| = 1`. -/
lemma no_pure_nth_power {y : ℤ} {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    {r s : ℤ}
    (h : plus y = (⟨r, s⟩ : Zsqrt2) ^ n ∨ plus y = -((⟨r, s⟩ : Zsqrt2) ^ n)) : False := by
  have hs : s ∣ 1 := s_dvd_one_of_plus_eq_pow h
  have hs1 : s = 1 ∨ s = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hs)
  have him0 : (plus y).im = 1 := rfl
  have hV : |V2 r n| = 1 := by
    rcases hs1 with rfl | rfl
    · have hp := pow_eq_U2_V2 r n
      rcases h with h | h
      · have him : ((⟨r, 1⟩ : Zsqrt2) ^ n).im = 1 := by rw [← h]; exact him0
        rw [hp] at him
        have : V2 r n = 1 := by simpa using him
        simp [this]
      · have him : (-((⟨r, 1⟩ : Zsqrt2) ^ n)).im = 1 := by rw [← h]; exact him0
        rw [hp] at him
        have : V2 r n = -1 := by
          have : -V2 r n = 1 := by simpa using him
          linarith
        simp [this]
    · have hstar : (⟨r, -1⟩ : Zsqrt2) = star (⟨r, 1⟩ : Zsqrt2) := by ext <;> simp
      have hsp : (⟨r, -1⟩ : Zsqrt2) ^ n = star ((⟨r, 1⟩ : Zsqrt2) ^ n) := by
        rw [hstar, star_pow]
      rw [pow_eq_U2_V2] at hsp
      rcases h with h | h
      · have him : ((⟨r, -1⟩ : Zsqrt2) ^ n).im = 1 := by rw [← h]; exact him0
        rw [hsp] at him
        have : V2 r n = -1 := by
          have : -V2 r n = 1 := by simpa using him
          linarith
        simp [this]
      · have him : (-((⟨r, -1⟩ : Zsqrt2) ^ n)).im = 1 := by rw [← h]; exact him0
        rw [hsp] at him
        have : V2 r n = 1 := by
          have : -(-V2 r n) = 1 := by simpa using him
          linarith
        simp [this]
  exact V2_ne_one_of_odd hn hodd hV

/-! ### The unit group is `{± ε ^ k}` -/

def epsUnit : Zsqrt2ˣ :=
  ⟨eps, epsInv, eps_mul_epsInv, epsInv_mul_eps⟩

lemma epsUnit_coe : (epsUnit : Zsqrt2) = eps := rfl

lemma epsUnit_inv_coe : ((epsUnit⁻¹ : Zsqrt2ˣ) : Zsqrt2) = epsInv := rfl

lemma epsUnit_pow_coe : ∀ n : ℕ, ((epsUnit ^ n : Zsqrt2ˣ) : Zsqrt2) = eps ^ n
  | 0 => by simp [epsUnit_coe]
  | n + 1 => by
    rw [pow_succ, pow_succ, Units.val_mul, epsUnit_pow_coe n, epsUnit_coe]

lemma fund_pow_nat : ∀ n : ℕ, (fund : Zsqrt2) ^ n = eps ^ (2 * n)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, fund_pow_nat n, fund_eq_eps_sq, ← pow_add]
    congr 1

lemma coe_fund_mul (a b : Pell.Solution₁ 2) :
    (↑(a * b) : Zsqrt2) = (↑a : Zsqrt2) * (↑b : Zsqrt2) :=
  rfl

lemma fund_pow_coe : ∀ n : ℕ, (↑(fund ^ n) : Zsqrt2) = (fund : Zsqrt2) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ, coe_fund_mul, fund_pow_coe n]

lemma fund_inv_coe : (↑(fund⁻¹) : Zsqrt2) = ⟨3, -2⟩ := by
  apply Zsqrtd.ext
  · change (fund⁻¹).x = 3
    rw [Pell.Solution₁.x_inv, fund_x]
  · change (fund⁻¹).y = -2
    rw [Pell.Solution₁.y_inv, fund_y]

lemma fund_inv_pow_coe : ∀ m : ℕ,
    (↑(fund⁻¹ ^ m) : Zsqrt2) = (⟨3, -2⟩ : Zsqrt2) ^ m
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, pow_succ, coe_fund_mul, fund_inv_pow_coe m, fund_inv_coe]

lemma fund_zpow_pos (n : ℕ) : (↑(fund ^ (n : ℤ)) : Zsqrt2) = (fund : Zsqrt2) ^ n := by
  rw [zpow_natCast, fund_pow_coe]

lemma fund_zpow_neg (n : ℕ) : (↑(fund ^ (-(n : ℤ))) : Zsqrt2) = (⟨3, -2⟩ : Zsqrt2) ^ n := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, fund_inv_pow_coe]

lemma epsUnit_zpow_pos (n : ℕ) : ↑(epsUnit ^ (n : ℤ)) = eps ^ n := by
  rw [zpow_natCast, epsUnit_pow_coe]

lemma epsUnit_inv_pow_coe : ∀ n : ℕ, ↑((epsUnit⁻¹) ^ n) = epsInv ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ, Units.val_mul, epsUnit_inv_pow_coe n, epsUnit_inv_coe]

lemma epsUnit_zpow_neg (n : ℕ) : ↑(epsUnit ^ (-(n : ℤ))) = epsInv ^ n := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, epsUnit_inv_pow_coe]

lemma fund_zpow_eq_epsUnit : ∀ k : ℤ, (↑(fund ^ k) : Zsqrt2) = ↑(epsUnit ^ (2 * k))
  | (n : ℕ) => by
    rw [fund_zpow_pos, fund_pow_nat]
    have h2 : (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) := by simp
    rw [h2, epsUnit_zpow_pos]
  | Int.negSucc n => by
    have hk : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := Int.negSucc_eq n
    rw [hk, fund_zpow_neg]
    have h2 : (2 : ℤ) * (-((n + 1 : ℕ) : ℤ)) = -((2 * (n + 1) : ℕ) : ℤ) := by
      push_cast; ring
    rw [h2, epsUnit_zpow_neg]
    have : (epsInv : Zsqrt2) ^ (2 * (n + 1)) = (⟨3, -2⟩ : Zsqrt2) ^ (n + 1) := by
      rw [pow_mul, epsInv_sq]
    exact this.symm

lemma mul_epsInv_of_mul_eps {z w : Zsqrt2} (h : z * eps = w) :
    z = w * epsInv := by
  have := congrArg (· * epsInv) h
  simpa [mul_assoc, eps_mul_epsInv] using this

lemma epsUnit_mul_inv (k : ℤ) :
    ↑(epsUnit ^ k) * epsInv = ↑(epsUnit ^ (k - 1)) := by
  have : epsInv = ↑(epsUnit⁻¹) := rfl
  rw [this, ← Units.val_mul, ← zpow_neg_one, ← zpow_add]
  congr 2

lemma isUnit_eq_epsUnit_zpow {z : Zsqrt2} (h : IsUnit z) :
    ∃ k : ℤ, z = ↑(epsUnit ^ k) ∨ z = -↑(epsUnit ^ k) := by
  rcases norm_eq_one_or_neg_one_of_isUnit h with h1 | hneg
  · obtain ⟨k, hk | hk⟩ := eq_fund_zpow_of_norm_one h1
    · exact ⟨2 * k, Or.inl (hk.trans (fund_zpow_eq_epsUnit k))⟩
    · exact ⟨2 * k, Or.inr (hk.trans (by rw [fund_zpow_eq_epsUnit]))⟩
  · have hzeps : (z * eps).norm = 1 := by
      rw [Zsqrtd.norm_mul, hneg, eps_norm]; norm_num
    obtain ⟨k, hk | hk⟩ := eq_fund_zpow_of_norm_one hzeps
    · refine ⟨2 * k - 1, Or.inl ?_⟩
      have hk' : z * eps = ↑(epsUnit ^ (2 * k)) :=
        hk.trans (fund_zpow_eq_epsUnit k)
      rw [mul_epsInv_of_mul_eps hk', epsUnit_mul_inv]
    · refine ⟨2 * k - 1, Or.inr ?_⟩
      have hk' : z * eps = -↑(epsUnit ^ (2 * k)) :=
        hk.trans (by rw [fund_zpow_eq_epsUnit])
      have : z = -↑(epsUnit ^ (2 * k)) * epsInv :=
        mul_epsInv_of_mul_eps (w := -↑(epsUnit ^ (2 * k))) hk'
      rw [this, neg_mul, epsUnit_mul_inv]

lemma associated_iff_unit_mul {a b : Zsqrt2} :
    Associated a b ↔ ∃ u : Zsqrt2ˣ, a * ↑u = b :=
  Iff.rfl

lemma plus_eq_unit_cube {y : ℤ} {p : ℕ} (hy : Odd y)
    (h : (y ^ 2 - 2 : ℤ) = (p : ℤ) ^ 3) :
    ∃ (k : ℤ) (d : Zsqrt2),
      plus y = ↑(epsUnit ^ k) * d ^ 3 ∨
      plus y = -↑(epsUnit ^ k) * d ^ 3 := by
  obtain ⟨d, hd⟩ := plus_associated_pow (n := 3) hy h
  obtain ⟨u, hu⟩ := hd
  -- hu : d ^ 3 * ↑u = plus y
  obtain ⟨k, hk | hk⟩ := isUnit_eq_epsUnit_zpow u.isUnit
  · refine ⟨k, d, Or.inl ?_⟩
    rw [← hu, hk, mul_comm]
  · refine ⟨k, d, Or.inr ?_⟩
    rw [← hu, hk, mul_comm, neg_mul]

lemma Int.emod_three_eq (k : ℤ) : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
  have : k % 3 < 3 := Int.emod_lt_of_pos k (by decide)
  have : 0 ≤ k % 3 := Int.emod_nonneg k (by decide)
  omega

lemma epsUnit_zpow_mod_three (k : ℤ) (d : Zsqrt2) :
    (↑(epsUnit ^ k) : Zsqrt2) * d ^ 3 =
      (↑(epsUnit ^ (k % 3)) : Zsqrt2) *
        ((↑(epsUnit ^ (k / 3)) : Zsqrt2) * d) ^ 3 := by
  have hdiv : k = 3 * (k / 3) + k % 3 := (Int.ediv_add_emod k 3).symm
  have hz : (↑(epsUnit ^ k) : Zsqrt2) =
      (↑(epsUnit ^ (k % 3)) : Zsqrt2) * (↑(epsUnit ^ (3 * (k / 3))) : Zsqrt2) := by
    rw [← Units.val_mul]
    congr 1
    rw [← zpow_add, add_comm, ← hdiv]
  rw [hz]
  have hcube : (↑(epsUnit ^ (3 * (k / 3))) : Zsqrt2) =
      (↑(epsUnit ^ (k / 3)) : Zsqrt2) ^ 3 := by
    have : (3 : ℤ) * (k / 3) = (k / 3) + (k / 3) + (k / 3) := by ring
    rw [this, zpow_add, zpow_add, Units.val_mul, Units.val_mul, pow_three]
    ring
  rw [hcube]
  ring

/-! ### Expansions of `ε * δ³` and `ε² * δ³` -/

lemma mul_eps_mk (a b : ℤ) :
    eps * (⟨a, b⟩ : Zsqrt2) = ⟨a + 2 * b, a + b⟩ := by
  ext <;> simp [eps]; ring

lemma mul_eps_sq_mk (a b : ℤ) :
    (eps ^ 2) * (⟨a, b⟩ : Zsqrt2) = ⟨3 * a + 4 * b, 2 * a + 3 * b⟩ := by
  ext <;> simp [eps, pow_two]; ring

lemma cube_re_im (a b : ℤ) :
    ((⟨a, b⟩ : Zsqrt2) ^ 3).re = a ^ 3 + 6 * a * b ^ 2 ∧
    ((⟨a, b⟩ : Zsqrt2) ^ 3).im = 3 * a ^ 2 * b + 2 * b ^ 3 := by
  have h2 : (⟨a, b⟩ : Zsqrt2) ^ 2 = ⟨a ^ 2 + 2 * b ^ 2, 2 * a * b⟩ := by
    ext <;> simp [pow_two] <;> ring
  have h3 : (⟨a, b⟩ : Zsqrt2) ^ 3 = ⟨a, b⟩ * ((⟨a, b⟩ : Zsqrt2) ^ 2) := pow_succ' _ _
  rw [h3, h2]
  constructor <;> simp <;> ring

def thue1 (a b : ℤ) : ℤ := a ^ 3 + 3 * a ^ 2 * b + 6 * a * b ^ 2 + 2 * b ^ 3
def thue2 (a b : ℤ) : ℤ := 2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3
def gForm (k b : ℤ) : ℤ := k ^ 3 + 3 * k * b ^ 2 - 2 * b ^ 3

lemma thue1_eq_gForm (a b : ℤ) : thue1 a b = gForm (a + b) b := by
  simp [thue1, gForm]; ring

lemma im_eps_cube (a b : ℤ) :
    (eps * (⟨a, b⟩ : Zsqrt2) ^ 3).im = thue1 a b := by
  have hri := cube_re_im a b
  simp [eps, thue1, Zsqrtd.im_mul, hri.1, hri.2]
  ring

lemma im_eps_sq_cube (a b : ℤ) :
    ((eps ^ 2) * (⟨a, b⟩ : Zsqrt2) ^ 3).im = thue2 a b := by
  have hri := cube_re_im a b
  have heps2 : (eps ^ 2 : Zsqrt2) = ⟨3, 2⟩ := eps_sq
  simp [heps2, thue2, Zsqrtd.im_mul, hri.1, hri.2]
  ring

lemma plus_im (y : ℤ) : (plus y).im = 1 := rfl

/-! ### The cubic Thue equation `gForm k b = ±1` -/

lemma gForm_neg (k b : ℤ) : gForm (-k) (-b) = -gForm k b := by
  simp [gForm]; ring

lemma gForm_even_of_odd_b {k b : ℤ} (hb : Odd b) : Even (gForm k b) := by
  have hmod : gForm k b ≡ k ^ 3 + k * b ^ 2 [ZMOD 2] := by
    refine Int.modEq_iff_dvd.mpr ⟨b ^ 3 - k * b ^ 2, ?_⟩
    simp only [gForm]; ring
  have hb2 : (b ^ 2 : ℤ) ≡ 1 [ZMOD 2] := Int.odd_iff.mp (Odd.pow hb)
  have hkb' : k * b ^ 2 ≡ k [ZMOD 2] := by
    simpa using (Int.ModEq.mul_left k hb2)
  have hsum0 : k ^ 3 + k * b ^ 2 ≡ k ^ 3 + k [ZMOD 2] := Int.ModEq.add_left _ hkb'
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by
    have : k % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    have : 0 ≤ k % 2 := Int.emod_nonneg _ (by decide)
    omega
  have hsum : k ^ 3 + k ≡ 0 [ZMOD 2] := by
    rcases hk with hk | hk
    · have hk0 : k ≡ 0 [ZMOD 2] := hk
      have hk3 : k ^ 3 ≡ 0 [ZMOD 2] := by simpa using Int.ModEq.pow (n := 2) 3 hk0
      exact hk3.add hk0
    · have hk1 : k ≡ 1 [ZMOD 2] := hk
      have hk3 : k ^ 3 ≡ 1 [ZMOD 2] := by simpa using Int.ModEq.pow (n := 2) 3 hk1
      exact (hk3.add hk1).trans (by decide : (1 + 1 : ℤ) ≡ 0 [ZMOD 2])
  exact Int.even_iff.mpr (hmod.trans (hsum0.trans hsum))

lemma b_even_of_gForm_pm_one {k b : ℤ} (h : gForm k b = 1 ∨ gForm k b = -1) :
    Even b := by
  by_contra hb
  have he : Even (gForm k b) := gForm_even_of_odd_b (Int.not_even_iff_odd.mp hb)
  rcases h with h | h <;> (rw [h] at he; revert he; decide)

lemma gForm_modEq (k b : ℤ) :
    gForm k b ≡ (k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3 [ZMOD 9] := by
  have hk : k ≡ k % 9 [ZMOD 9] := (Int.mod_modEq k 9).symm
  have hb : b ≡ b % 9 [ZMOD 9] := (Int.mod_modEq b 9).symm
  have hk3 : k ^ 3 ≡ (k % 9) ^ 3 [ZMOD 9] := Int.ModEq.pow 3 hk
  have hb2 : b ^ 2 ≡ (b % 9) ^ 2 [ZMOD 9] := Int.ModEq.pow 2 hb
  have hb3 : b ^ 3 ≡ (b % 9) ^ 3 [ZMOD 9] := Int.ModEq.pow 3 hb
  have h3 : 3 * k * b ^ 2 ≡ 3 * (k % 9) * (b % 9) ^ 2 [ZMOD 9] :=
    (Int.ModEq.mul_left 3 hk).mul hb2
  have h2 : 2 * b ^ 3 ≡ 2 * (b % 9) ^ 3 [ZMOD 9] := Int.ModEq.mul_left 2 hb3
  simpa [gForm] using (hk3.add h3).sub h2

lemma three_dvd_b_of_gForm_pm_one {k b : ℤ}
    (h : gForm k b = 1 ∨ gForm k b = -1) : (3 : ℤ) ∣ b := by
  have hg : gForm k b % 9 = 1 ∨ gForm k b % 9 = 8 := by
    rcases h with h | h <;> simp [h]
  have hr : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    have : b % 3 < 3 := Int.emod_lt_of_pos b (by decide)
    have : 0 ≤ b % 3 := Int.emod_nonneg b (by decide)
    omega
  rcases hr with h0 | h1 | h2
  · exact Int.dvd_iff_emod_eq_zero.mpr h0
  · have hb9 : b % 9 = 1 ∨ b % 9 = 4 ∨ b % 9 = 7 := by
      have : b % 9 < 9 := Int.emod_lt_of_pos b (by decide)
      have : 0 ≤ b % 9 := Int.emod_nonneg b (by decide)
      have e : b % 3 = (b % 9) % 3 :=
        (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 9)).symm
      omega
    have hk9 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨
        k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      have : k % 9 < 9 := Int.emod_lt_of_pos k (by decide)
      have : 0 ≤ k % 9 := Int.emod_nonneg k (by decide)
      omega
    have hgeq : gForm k b % 9 =
        ((k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3) % 9 :=
      Int.ModEq.eq (gForm_modEq k b)
    rw [hgeq] at hg
    rcases hb9 with hb9 | hb9 | hb9 <;>
      rcases hk9 with hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9
    all_goals (rw [hk9, hb9] at hg; norm_num at hg)
  · have hb9 : b % 9 = 2 ∨ b % 9 = 5 ∨ b % 9 = 8 := by
      have : b % 9 < 9 := Int.emod_lt_of_pos b (by decide)
      have : 0 ≤ b % 9 := Int.emod_nonneg b (by decide)
      have e : b % 3 = (b % 9) % 3 :=
        (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 9)).symm
      omega
    have hk9 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨
        k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      have : k % 9 < 9 := Int.emod_lt_of_pos k (by decide)
      have : 0 ≤ k % 9 := Int.emod_nonneg k (by decide)
      omega
    have hgeq : gForm k b % 9 =
        ((k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3) % 9 :=
      Int.ModEq.eq (gForm_modEq k b)
    rw [hgeq] at hg
    rcases hb9 with hb9 | hb9 | hb9 <;>
      rcases hk9 with hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9
    all_goals (rw [hk9, hb9] at hg; norm_num at hg)

lemma six_dvd_b_of_gForm_pm_one {k b : ℤ}
    (h : gForm k b = 1 ∨ gForm k b = -1) : (6 : ℤ) ∣ b := by
  have h2 : (2 : ℤ) ∣ b := even_iff_two_dvd.mp (b_even_of_gForm_pm_one h)
  have h3 : (3 : ℤ) ∣ b := three_dvd_b_of_gForm_pm_one h
  have h2m : b % 2 = 0 := Int.emod_eq_zero_of_dvd h2
  have h3m : b % 3 = 0 := Int.emod_eq_zero_of_dvd h3
  have h6 : b % 6 = 0 := by
    have : b % 6 < 6 := Int.emod_lt_of_pos b (by decide)
    have : 0 ≤ b % 6 := Int.emod_nonneg b (by decide)
    have e2 : b % 2 = (b % 6) % 2 :=
      (Int.emod_emod_of_dvd b (by decide : (2 : ℤ) ∣ 6)).symm
    have e3 : b % 3 = (b % 6) % 3 :=
      (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 6)).symm
    omega
  exact Int.dvd_iff_emod_eq_zero.mpr h6

lemma gcd_k_b_of_gForm {k b : ℤ} (h : gForm k b = 1 ∨ gForm k b = -1) :
    Int.gcd k b = 1 := by
  have hd : (Int.gcd k b : ℤ) ∣ gForm k b := by
    have hk : (Int.gcd k b : ℤ) ∣ k := Int.gcd_dvd_left k b
    have hb : (Int.gcd k b : ℤ) ∣ b := Int.gcd_dvd_right k b
    have hk3 : (Int.gcd k b : ℤ) ∣ k ^ 3 := dvd_pow hk (by decide)
    have hb3 : (Int.gcd k b : ℤ) ∣ b ^ 3 := dvd_pow hb (by decide)
    have h3 : (Int.gcd k b : ℤ) ∣ 3 * k * b ^ 2 := by
      convert dvd_mul_of_dvd_left hk (3 * b ^ 2) using 1
      ring
    have h2 : (Int.gcd k b : ℤ) ∣ 2 * b ^ 3 := dvd_mul_of_dvd_right hb3 _
    simpa [gForm] using (hk3.add h3).sub h2
  have hg1 : (Int.gcd k b : ℤ) ∣ 1 := by
    rcases h with h | h
    · rwa [h] at hd
    · have : (Int.gcd k b : ℤ) ∣ -1 := by rwa [h] at hd
      simpa using this
  exact Nat.dvd_one.mp (by exact_mod_cast hg1)

lemma gForm_of_nonpos_k {k b : ℤ} (hk : k ≤ 0) (hb : 0 < b) :
    gForm k b ≤ -2 * b ^ 3 := by
  have h1 : k ^ 3 ≤ 0 := by
    have : k ^ 3 = k * k * k := by ring
    rw [this]; nlinarith
  have h2 : 3 * k * b ^ 2 ≤ 0 := by nlinarith [sq_nonneg b]
  simp only [gForm]
  nlinarith [sq_nonneg b]

lemma gForm_ne_pm_one_of_nonpos_k {k b : ℤ} (hk : k ≤ 0) (hb : 0 < b) :
    gForm k b ≠ 1 ∧ gForm k b ≠ -1 := by
  have hle := gForm_of_nonpos_k hk hb
  have : (2 : ℤ) ≤ 2 * b ^ 3 := by
    have : (1 : ℤ) ≤ b := by omega
    have : (1 : ℤ) ≤ b ^ 3 := one_le_pow₀ this
    nlinarith
  constructor <;> linarith

/-- If `gForm k b = ±1` and `b ≠ 0`, then `k` and `b` have the same (strict) sign. -/
lemma gForm_same_sign {k b : ℤ} (hb : b ≠ 0)
    (h : gForm k b = 1 ∨ gForm k b = -1) : 0 < k * b := by
  have hb'' : b < 0 ∨ 0 < b := by omega
  rcases hb'' with hbn | hbp
  · -- b < 0: reduce to -b > 0 via gForm_neg
    have : gForm (-k) (-b) = 1 ∨ gForm (-k) (-b) = -1 := by
      rw [gForm_neg]
      rcases h with h | h <;> simp [h]
    have : ¬ (-k ≤ 0) := by
      intro hk
      have hbpos : 0 < -b := by omega
      have := gForm_ne_pm_one_of_nonpos_k hk hbpos
      rcases ‹gForm (-k) (-b) = 1 ∨ gForm (-k) (-b) = -1› with h' | h'
      · exact this.1 h'
      · exact this.2 h'
    have : 0 < -k := by omega
    nlinarith
  · have : ¬ (k ≤ 0) := by
      intro hk
      have := gForm_ne_pm_one_of_nonpos_k hk hbp
      rcases h with h | h
      · exact this.1 h
      · exact this.2 h
    nlinarith

lemma gForm_eq_iff (k b : ℤ) :
    gForm k b = 1 ∨ gForm k b = -1 ↔
      k * (k ^ 2 + 3 * b ^ 2) = 2 * b ^ 3 + 1 ∨
      k * (k ^ 2 + 3 * b ^ 2) = 2 * b ^ 3 - 1 := by
  simp only [gForm]; constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- For `b = 6c` we have `gForm k (6c) = k^3 + 108 k c^2 - 432 c^3`. -/
lemma gForm_six (k c : ℤ) :
    gForm k (6 * c) = k ^ 3 + 108 * k * c ^ 2 - 432 * c ^ 3 := by
  simp [gForm]; ring

lemma gForm_six_eq_iff (k c : ℤ) :
    gForm k (6 * c) = 1 ∨ gForm k (6 * c) = -1 ↔
      k * (k ^ 2 + 108 * c ^ 2) = 432 * c ^ 3 + 1 ∨
      k * (k ^ 2 + 108 * c ^ 2) = 432 * c ^ 3 - 1 := by
  rw [gForm_six]; constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- If `7k ≤ 25c` and `c ≥ 2`, then `k(k² + 108c²) ≤ 432c³ - 2`. -/
lemma window_low {k c : ℤ} (hk : 0 ≤ k) (hc : 2 ≤ c) (hle : 7 * k ≤ 25 * c) :
    k * (k ^ 2 + 108 * c ^ 2) ≤ 432 * c ^ 3 - 2 := by
  -- 7³ k³ ≤ 25³ c³ and 108·7² k c² ≤ 108·7²·(25/7) c³ = 108·7·25 c³
  have h1 : 343 * (k * (k ^ 2 + 108 * c ^ 2)) ≤ 147925 * c ^ 3 := by
    have hk3 : 343 * k ^ 3 ≤ 15625 * c ^ 3 := by
      have : (7 * k) ^ 3 ≤ (25 * c) ^ 3 :=
        pow_le_pow_left₀ (by nlinarith) hle 3
      have e1 : (7 * k) ^ 3 = 343 * k ^ 3 := by ring
      have e2 : (25 * c) ^ 3 = 15625 * c ^ 3 := by ring
      linarith
    have hmid : 343 * (108 * k * c ^ 2) ≤ 132300 * c ^ 3 := by
      -- 343 * 108 = 37044, 37044 k c² ≤ 37044 * (25/7) c³ = 5292 * 25 c³ = 132300 c³
      have : 7 * (37044 * k * c ^ 2) ≤ 37044 * 25 * c ^ 3 := by
        have : 7 * k * 37044 * c ^ 2 ≤ 25 * c * 37044 * c ^ 2 := by
          nlinarith
        convert this using 1 <;> ring
      have : 37044 * k * c ^ 2 ≤ 132300 * c ^ 3 := by
        have hpos : (0 : ℤ) < 7 := by decide
        have := this
        -- 7 * X ≤ 7 * 132300 c³  ⇒ X ≤ 132300 c³
        have : 7 * (37044 * k * c ^ 2) ≤ 7 * (132300 * c ^ 3) := by
          convert this using 1 <;> ring
        exact Int.le_of_mul_le_mul_left this hpos
      convert this using 1 <;> ring
    have : 343 * (k * (k ^ 2 + 108 * c ^ 2)) =
        343 * k ^ 3 + 343 * (108 * k * c ^ 2) := by ring
    linarith
  have hcmp : 147925 * c ^ 3 ≤ 343 * (432 * c ^ 3 - 2) := by
    have : 343 * (432 * c ^ 3 - 2) = 148176 * c ^ 3 - 686 := by ring
    rw [this]
    have : (686 : ℤ) ≤ 251 * c ^ 3 := by
      have : (8 : ℤ) ≤ c ^ 3 := by
        have : (2 : ℤ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (by omega) hc 3
        simpa using this
      nlinarith
    linarith
  have hpos : (0 : ℤ) < 343 := by decide
  have : 343 * (k * (k ^ 2 + 108 * c ^ 2)) ≤ 343 * (432 * c ^ 3 - 2) :=
    le_trans h1 hcmp
  exact Int.le_of_mul_le_mul_left this hpos

/-- If `5k ≥ 18c` and `c ≥ 1`, `k ≥ 0`, then `k(k²+108c²) ≥ 432c³ + 2`. -/
lemma window_high {k c : ℤ} (hk : 0 ≤ k) (hc : 1 ≤ c) (hge : 5 * k ≥ 18 * c) :
    k * (k ^ 2 + 108 * c ^ 2) ≥ 432 * c ^ 3 + 2 := by
  have hle : (18 : ℤ) * c ≤ 5 * k := hge
  have hk3 : (18 : ℤ) ^ 3 * c ^ 3 ≤ 5 ^ 3 * k ^ 3 := by
    have := pow_le_pow_left₀ (by nlinarith) hle 3
    have e1 : (18 * c) ^ 3 = 18 ^ 3 * c ^ 3 := by ring
    have e2 : (5 * k) ^ 3 = 5 ^ 3 * k ^ 3 := by ring
    linarith
  have hL : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) ≥
      18 ^ 3 * c ^ 3 + 5 ^ 2 * 108 * 18 * c ^ 3 := by
    have A : (5 : ℤ) ^ 3 * k ^ 3 ≥ 18 ^ 3 * c ^ 3 := by
      convert hk3 using 1 <;> ring
    have B : (5 : ℤ) ^ 3 * (108 * k * c ^ 2) ≥ 5 ^ 2 * 108 * 18 * c ^ 3 := by
      nlinarith
    have : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) =
        5 ^ 3 * k ^ 3 + 5 ^ 3 * (108 * k * c ^ 2) := by ring
    linarith
  -- 5³ = 125, 18³ = 5832, 25*108*18 = 48600
  -- left c³ coeff = 5832 + 48600 = 54432
  -- 125 * 432 = 54000, 125 * 2 = 250
  have hL' : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) ≥ 54432 * c ^ 3 := by
    have h1 : (18 : ℤ) ^ 3 + 5 ^ 2 * 108 * 18 = 54432 := by norm_num
    have : 18 ^ 3 * c ^ 3 + 5 ^ 2 * 108 * 18 * c ^ 3 = 54432 * c ^ 3 := by
      rw [← h1]; ring
    linarith
  have hR : 54432 * c ^ 3 ≥ (5 : ℤ) ^ 3 * (432 * c ^ 3 + 2) := by
    have hmul : (5 : ℤ) ^ 3 * (432 * c ^ 3 + 2) = 54000 * c ^ 3 + 250 := by
      have : (5 : ℤ) ^ 3 = 125 := by norm_num
      rw [this]; ring
    rw [hmul]
    have : (432 : ℤ) * c ^ 3 ≥ 250 := by
      have : (1 : ℤ) ≤ c ^ 3 := one_le_pow₀ hc
      nlinarith
    linarith
  have : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) ≥
      (5 : ℤ) ^ 3 * (432 * c ^ 3 + 2) := ge_trans hL' hR
  have hpos : (0 : ℤ) < 5 ^ 3 := by norm_num
  exact Int.le_of_mul_le_mul_left this hpos

lemma window_of_gForm_six {k c : ℤ} (hk : 0 < k) (hc : 0 < c)
    (h : gForm k (6 * c) = 1 ∨ gForm k (6 * c) = -1) :
    25 * c < 7 * k ∧ 5 * k < 18 * c := by
  have hiff := (gForm_six_eq_iff k c).mp h
  constructor
  · by_contra hle
    have hle' : 7 * k ≤ 25 * c := by omega
    have hk0 : 0 ≤ k := by omega
    by_cases hc2 : 2 ≤ c
    · have := window_low hk0 hc2 hle'
      rcases hiff with h' | h' <;> linarith
    · have hc1 : c = 1 := by omega
      subst hc1
      have hk3 : k ≤ 3 := by omega
      have hk1 : 1 ≤ k := by omega
      have hkcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      have h6 : (6 * 1 : ℤ) = 6 := by norm_num
      rw [h6] at h
      have hg1 : gForm 1 6 = -323 := by simp [gForm]
      have hg2 : gForm 2 6 = -208 := by simp [gForm]
      have hg3 : gForm 3 6 = -81 := by simp [gForm]
      rcases hkcases with rfl | rfl | rfl
      · rw [hg1] at h; omega
      · rw [hg2] at h; omega
      · rw [hg3] at h; omega
  · by_contra hge
    have hge' : 5 * k ≥ 18 * c := by omega
    have hk0 : 0 ≤ k := by omega
    have hc1 : 1 ≤ c := by omega
    have := window_high hk0 hc1 hge'
    rcases hiff with h' | h' <;> linarith

/-- gForm ±1 with b ≠ 0 is impossible. -/
lemma gForm_ne_pm_one_of_b_ne_zero {k b : ℤ} (hb : b ≠ 0)
    (h : gForm k b = 1 ∨ gForm k b = -1) : False := by
  sorry

lemma thue2_sub_b_cube (a b : ℤ) :
    thue2 a b - b ^ 3 = (a + b) ^ 2 * (2 * a + 5 * b) := by
  simp [thue2]; ring

lemma thue2_neg' (a b : ℤ) : thue2 (-a) (-b) = -thue2 a b := by
  simp [thue2]; ring

def Pth (s b : ℤ) : ℤ := s ^ 3 + 6 * s ^ 2 * b + 9 * s * b ^ 2 - 4 * b ^ 3

lemma thue2_eq_Pth (m b : ℤ) :
    4 * thue2 (-m) b = -Pth (2 * m - 5 * b) b := by
  simp [thue2, Pth]; ring

lemma Pth_succ (s b : ℤ) :
    Pth (s + 1) b - Pth s b =
      3 * s ^ 2 + 12 * s * b + 9 * b ^ 2 + 3 * s + 6 * b + 1 := by
  simp [Pth]; ring

lemma Pth_strict_inc {s b : ℤ} (hs : 0 ≤ s) (hb : 1 ≤ b) :
    Pth s b < Pth (s + 1) b := by
  have := Pth_succ s b
  nlinarith [sq_nonneg s, sq_nonneg b]

lemma Pth_homog (s b n : ℤ) : Pth (n * s) (n * b) = n ^ 3 * Pth s b := by
  simp [Pth]; ring

lemma Pth_11_31 (b d : ℤ) :
    Pth (11 * b + d) (31 * b) =
      -188 * b ^ 3 + 13104 * b ^ 2 * d + 219 * b * d ^ 2 + d ^ 3 := by
  simp [Pth]; ring

def checkPth (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun b =>
    decide (b < 13) ||
      (List.range b).all fun s =>
        decide (s = 0) || decide ((Pth s b).natAbs ≠ 4)

set_option maxHeartbeats 2000000
lemma checkPth_2000 : checkPth 2000 = true := by native_decide
set_option maxHeartbeats 400000

lemma Pth_ne_pm_four_fin {s b : ℤ} (hb : 13 ≤ b) (hbN : b ≤ 2000)
    (hs : 1 ≤ s) (hsb : s < b) : Pth s b ≠ 4 ∧ Pth s b ≠ -4 := by
  have hc := checkPth_2000
  have hb13 : 13 ≤ b.toNat := by omega
  have hbN' : b.toNat ≤ 2000 := by omega
  have hbeq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hseq : (s.toNat : ℤ) = s := Int.toNat_of_nonneg (by omega)
  have hsN : s.toNat < b.toNat := by omega
  have hcheck : ∀ bb ss : ℕ, 13 ≤ bb → bb ≤ 2000 → 1 ≤ ss → ss < bb →
      (Pth ss bb).natAbs ≠ 4 := by
    intro bb ss hbb1 hbb2 hss1 hss2
    have := hc
    simp [checkPth, Bool.or_eq_true, decide_eq_true_eq] at this
    have h1 := this bb (by omega)
    have : ¬ bb < 13 := by omega
    simp [this] at h1
    have h2 := h1 ss (by omega)
    have : ¬ ss = 0 := by omega
    simpa [this] using h2
  have hne : (Pth s.toNat b.toNat).natAbs ≠ 4 :=
    hcheck b.toNat s.toNat hb13 hbN' (by omega) hsN
  have : Pth s b = Pth s.toNat b.toNat := by simp [hseq, hbeq]
  rw [this]
  constructor
  · intro h; apply hne; rw [h]; decide
  · intro h; apply hne; rw [h]; decide

lemma Pth_as_prod (s b : ℤ) :
    Pth s b = s * (s + 3 * b) ^ 2 - 4 * b ^ 3 := by
  simp [Pth]; ring

lemma Pth_ne_pm_four_large {s b : ℤ} (hb : 2001 ≤ b) (hs : 1 ≤ s) (hsb : s < b) :
    Pth s b ≠ 4 ∧ Pth s b ≠ -4 := by
  sorry

lemma Pth_ne_pm_four {s b : ℤ} (hb : 13 ≤ b) (hs : 1 ≤ s) (hsb : s < b) :
    Pth s b ≠ 4 ∧ Pth s b ≠ -4 := by
  rcases le_or_gt b 2000 with h | h
  · exact Pth_ne_pm_four_fin hb h hs hsb
  · exact Pth_ne_pm_four_large h hs hsb

def checkThue2Strip : Bool :=
  (List.range 13).all fun b =>
    (List.range 37).all fun m =>
      decide (b < 5 ∨ m < 13 ∨ 3 * b ≤ m ∨ 2 * m ≤ 5 * b ∨
        2 ≤ (thue2 (-(m : ℤ)) (b : ℤ)).natAbs)

lemma checkThue2Strip_true : checkThue2Strip = true := by native_decide

lemma thue2_strip_small {m b : ℤ} (hb : 1 ≤ b) (hb12 : b ≤ 12)
    (hm : 13 ≤ m) (hm3 : m < 3 * b) (h25 : 5 * b < 2 * m) :
    2 ≤ |thue2 (-m) b| := by
  have hbN : b.toNat ≤ 12 := by omega
  have hmN : m.toNat ≤ 36 := by omega
  have hbeq : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hmeq : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have hcheck : ∀ bb mm : ℕ, bb ≤ 12 → mm ≤ 36 →
      ¬ bb < 5 → ¬ mm < 13 → ¬ 3 * bb ≤ mm → ¬ 2 * mm ≤ 5 * bb →
        2 ≤ (thue2 (-(mm : ℤ)) (bb : ℤ)).natAbs := by
    intro bb mm hbb hmm h5 h13 h3 h25'
    have := checkThue2Strip_true
    simp [checkThue2Strip, Bool.or_eq_true, decide_eq_true_eq] at this
    have h1 := this bb (by omega) mm (by omega)
    simp [h5, h13, h3, h25'] at h1
    exact h1
  have hN : 2 ≤ (thue2 (-(m.toNat : ℤ)) (b.toNat : ℤ)).natAbs :=
    hcheck b.toNat m.toNat hbN hmN (by omega) (by omega) (by omega) (by omega)
  rw [hbeq, hmeq] at hN
  have : (2 : ℤ) ≤ (thue2 (-m) b).natAbs := by exact_mod_cast hN
  rwa [Int.abs_eq_natAbs]

def checkThue2Box : Bool :=
  (List.range 25).all fun i =>
    (List.range 25).all fun j =>
      let a : ℤ := (i : ℤ) - 12
      let b : ℤ := (j : ℤ) - 12
      decide ((thue2 a b).natAbs ≠ 1 ∨ (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1))

lemma checkThue2Box_true : checkThue2Box = true := by native_decide

lemma thue2_box {a b : ℤ} (ha : |a| ≤ 12) (hb : |b| ≤ 12)
    (h : thue2 a b = 1 ∨ thue2 a b = -1) :
    (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  have habs : (thue2 a b).natAbs = 1 := by rcases h with h | h <;> simp [h]
  have hcheck : ∀ i j : ℕ, i < 25 → j < 25 →
      (thue2 ((i : ℤ) - 12) ((j : ℤ) - 12)).natAbs ≠ 1 ∨
        ((i : ℤ) - 12 = 1 ∧ (j : ℤ) - 12 = -1) ∨
        ((i : ℤ) - 12 = -1 ∧ (j : ℤ) - 12 = 1) := by
    intro i j hi hj
    have := checkThue2Box_true
    simp [checkThue2Box] at this
    exact this i hi j hj
  have hia : 0 ≤ a + 12 := by have := abs_le.mp ha; omega
  have hib : 0 ≤ b + 12 := by have := abs_le.mp hb; omega
  have hi : (a + 12).toNat < 25 := by
    have : ((a + 12).toNat : ℤ) = a + 12 := Int.toNat_of_nonneg hia
    have : a + 12 ≤ 24 := by have := abs_le.mp ha; omega
    omega
  have hj : (b + 12).toNat < 25 := by
    have : ((b + 12).toNat : ℤ) = b + 12 := Int.toNat_of_nonneg hib
    have : b + 12 ≤ 24 := by have := abs_le.mp hb; omega
    omega
  have haeq : ((a + 12).toNat : ℤ) - 12 = a := by
    have := Int.toNat_of_nonneg hia; omega
  have hbeq : ((b + 12).toNat : ℤ) - 12 = b := by
    have := Int.toNat_of_nonneg hib; omega
  have := hcheck (a + 12).toNat (b + 12).toNat hi hj
  simp only [haeq, hbeq] at this
  rcases this with hne | hsol | hsol
  · exact (hne habs).elim
  · exact Or.inl hsol
  · exact Or.inr hsol

/-- Opposite-sign case `a = -m < 0 < b`. -/
lemma thue2_neg_pos {m b : ℤ} (hm : 1 ≤ m) (hb : 1 ≤ b)
    (hbox : ¬ (|(-m)| ≤ 12 ∧ |b| ≤ 12)) (hne : m ≠ b)
    (h25ne : (2 : ℤ) * m ≠ 5 * b) :
    |thue2 (-m) b| ≠ 1 := by
  have hid2 : thue2 (-m) b = b ^ 3 + (b - m) ^ 2 * (5 * b - 2 * m) := by
    have := thue2_sub_b_cube (-m) b
    linarith
  by_cases hmb : m ≤ b
  · have : 1 ≤ (b - m) ^ 2 := one_le_pow₀ (by omega)
    have : 1 ≤ 5 * b - 2 * m := by nlinarith
    have : 1 ≤ b ^ 3 := one_le_pow₀ hb
    have hge : 2 ≤ thue2 (-m) b := by rw [hid2]; nlinarith
    have hnn : 0 ≤ thue2 (-m) b := by rw [hid2]; nlinarith
    rw [abs_of_nonneg hnn]; omega
  · by_cases h25le : 2 * m ≤ 5 * b
    · have : 1 ≤ 5 * b - 2 * m := by omega
      have : 1 ≤ (m - b) ^ 2 := one_le_pow₀ (by omega)
      have hsq : (b - m) ^ 2 = (m - b) ^ 2 := by ring
      have : 1 ≤ b ^ 3 := one_le_pow₀ hb
      have hge : 2 ≤ thue2 (-m) b := by rw [hid2, hsq]; nlinarith
      have hnn : 0 ≤ thue2 (-m) b := by rw [hid2, hsq]; nlinarith
      rw [abs_of_nonneg hnn]; omega
    · by_cases hm3 : 3 * b ≤ m
      · have hexp : thue2 (-m) b =
            -2 * m ^ 3 + 9 * m ^ 2 * b - 12 * m * b ^ 2 + 6 * b ^ 3 := by
          simp [thue2]; ring
        have hf3 : thue2 (-(3 * b)) b = -3 * b ^ 3 := by simp [thue2]; ring
        have hle : thue2 (-m) b ≤ thue2 (-(3 * b)) b := by
          have hdiff : thue2 (-m) b - thue2 (-(3 * b)) b =
              (m - 3 * b) * (-2 * m ^ 2 + 3 * b * m - 3 * b ^ 2) := by
            rw [hexp]; simp [thue2]; ring
          have : -2 * m ^ 2 + 3 * b * m - 3 * b ^ 2 ≤ 0 := by
            nlinarith [sq_nonneg (2 * m - b), sq_nonneg m, sq_nonneg b]
          nlinarith
        have : -3 * b ^ 3 ≤ -3 := by
          have : 1 ≤ b ^ 3 := one_le_pow₀ hb; nlinarith
        have hneg : thue2 (-m) b ≤ -3 := by linarith
        have : thue2 (-m) b < 0 := by linarith
        rw [abs_of_neg this]; omega
      · by_cases hb12 : b ≤ 12
        · have hm13 : 13 ≤ m := by
            have : ¬ |(-m)| ≤ 12 := by
              intro ha'; exact hbox ⟨ha', by omega⟩
            have : 13 ≤ |(-m)| := by omega
            simpa [abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ m)] using this
          have := thue2_strip_small hb hb12 hm13 (by omega) (by omega)
          omega
        · have hb13 : 13 ≤ b := by omega
          have hspos : 1 ≤ 2 * m - 5 * b := by omega
          have hslt : 2 * m - 5 * b < b := by nlinarith
          have hP := Pth_ne_pm_four hb13 hspos hslt
          have heqP := thue2_eq_Pth m b
          intro habs
          have hmul : 4 * thue2 (-m) b = -Pth (2 * m - 5 * b) b := heqP
          have : |Pth (2 * m - 5 * b) b| = 4 := by
            have : |4 * thue2 (-m) b| = 4 := by
              rw [abs_mul, habs]
              have : |(4 : ℤ)| = 4 := by decide
              rw [this]; norm_num
            rwa [hmul, abs_neg] at this
          rcases abs_eq.mp this with hp | hp
          · exact hP.1 hp
          · exact hP.2 hp

lemma thue2_of_eq_pm_one {a b : ℤ} (h : thue2 a b = 1 ∨ thue2 a b = -1) :
    (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  have habs : |thue2 a b| = 1 := by rcases h with h | h <;> simp [h]
  by_cases hb0 : b = 0
  · subst hb0
    have : thue2 a 0 = 2 * a ^ 3 := by simp [thue2]
    rw [this] at h
    rcases h with h | h <;> omega
  by_cases ha0 : a = 0
  · subst ha0
    have : thue2 0 b = 6 * b ^ 3 := by simp [thue2]
    rw [this] at h
    rcases h with h | h <;> omega
  by_cases heq : a + b = 0
  · have : a = -b := by omega
    subst this
    have : thue2 (-b) b = b ^ 3 := by
      have := thue2_sub_b_cube (-b) b
      simp at this; linarith
    rw [this] at habs
    have hbabs : |b| = 1 := by
      have : 1 ≤ |b| := Int.one_le_abs hb0
      have : |b| ^ 3 = 1 := by rwa [abs_pow] at habs
      have : |b| ≤ 1 := by
        have h2 : 2 ≤ |b| ∨ |b| = 1 := by omega
        rcases h2 with h2 | h2
        · have : (8 : ℤ) ≤ |b| ^ 3 := by
            have : (2 : ℤ) ^ 3 ≤ |b| ^ 3 := pow_le_pow_left₀ (by decide) h2 3
            simpa using this
          omega
        · omega
      omega
    rcases eq_or_eq_neg_of_abs_eq hbabs with hb1 | hb1
    · exact Or.inr ⟨by omega, hb1⟩
    · exact Or.inl ⟨by omega, hb1⟩
  · by_cases hbox : |a| ≤ 12 ∧ |b| ≤ 12
    · exact thue2_box hbox.1 hbox.2 h
    · by_cases h25 : 2 * a + 5 * b = 0
      · have hdiv5 : (2 : ℤ) ∣ 5 * b := ⟨-a, by linarith⟩
        have hcop : IsCoprime (2 : ℤ) 5 := by decide
        have h2b : (2 : ℤ) ∣ b := hcop.dvd_of_dvd_mul_left hdiv5
        obtain ⟨c, hc⟩ := h2b
        have ha' : a = -5 * c := by
          have : 2 * a + 5 * (2 * c) = 0 := by rw [← hc]; exact h25
          omega
        subst hc
        subst ha'
        have hev : thue2 (-5 * c) (2 * c) = 8 * c ^ 3 := by
          simp [thue2]; ring
        have hc0 : c ≠ 0 := by
          intro h0; subst h0; exact hb0 (by simp)
        have : 2 ≤ |8 * c ^ 3| := by
          have : 1 ≤ |c| := Int.one_le_abs hc0
          have : 1 ≤ |c| ^ 3 := one_le_pow₀ this
          rw [abs_mul, abs_pow]
          have : |(8 : ℤ)| = 8 := by decide
          rw [this]
          nlinarith
        rw [hev] at habs
        omega
      · by_cases hsp : 0 ≤ a * b
        · rcases le_total 0 a with haP | haN
          · have hbP : 0 ≤ b := by
              nlinarith
            have ha1 : 1 ≤ a := by omega
            have hb1 : 1 ≤ b := by omega
            have hpos : 6 ≤ thue2 a b := by
              have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha1
              have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb1
              have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha1
              have hb2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
              simp [thue2]; nlinarith
            omega
          · have hbN : b ≤ 0 := by nlinarith
            have ha1 : 1 ≤ -a := by omega
            have hb1 : 1 ≤ -b := by omega
            have hpos : 6 ≤ thue2 (-a) (-b) := by
              have ha3 : 1 ≤ (-a) ^ 3 := one_le_pow₀ ha1
              have hb3 : 1 ≤ (-b) ^ 3 := one_le_pow₀ hb1
              have ha2 : 1 ≤ (-a) ^ 2 := one_le_pow₀ ha1
              have hb2 : 1 ≤ (-b) ^ 2 := one_le_pow₀ hb1
              simp [thue2]; nlinarith
            have : thue2 a b = -thue2 (-a) (-b) := (thue2_neg' a b).symm
            omega
        · have habs0 : a * b < 0 := lt_of_not_ge hsp
          rcases lt_trichotomy a 0 with ha | ha | ha
          · have hbP : 0 < b := by nlinarith
            have hm : 1 ≤ -a := by omega
            have hb1 : 1 ≤ b := by omega
            have hne : -a ≠ b := by intro hh; exact heq (by omega)
            have h25ne : (2 : ℤ) * (-a) ≠ 5 * b := by
              intro hh; exact h25 (by omega)
            have := thue2_neg_pos (m := -a) hm hb1 (by simpa using hbox) hne h25ne
            have : |thue2 a b| ≠ 1 := by simpa using this
            exact this habs
          · exact (ha0 ha).elim
          · have hbN : b < 0 := by nlinarith
            have hm : 1 ≤ a := by omega
            have hb1 : 1 ≤ -b := by omega
            have hbox' : ¬ (|(-a)| ≤ 12 ∧ |-b| ≤ 12) := by
              intro hh; exact hbox ⟨by omega, by omega⟩
            have hne : a ≠ -b := by intro hh; exact heq (by omega)
            have h25ne : (2 : ℤ) * a ≠ 5 * (-b) := by
              intro hh; exact h25 (by linarith)
            have := thue2_neg_pos (m := a) (b := -b) hm hb1 hbox' hne h25ne
            have : |thue2 a b| ≠ 1 := by
              rwa [← abs_neg, ← thue2_neg']
            exact this habs

end Zsqrt2



lemma prime_pow_diff_two {p q ea eb : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hea : 1 < ea) (heb : 1 < eb)
    (hdiff : q ^ eb = p ^ ea + 2) :
    p = 5 ∧ ea = 2 ∧ q = 3 ∧ eb = 3 := by
  have hp2 : p ≠ 2 := by
    intro hp2; subst hp2
    have hE : Even (2 ^ ea) := Even.pow_of_ne_zero even_two (by omega)
    have : Even (q ^ eb) := by
      rw [hdiff]
      exact Even.add hE even_two
    have hq2 : q = 2 := prime_of_even_pow hq this
    subst hq2
    exact not_two_pow_diff_two hea heb hdiff
  have hq2 : q ≠ 2 := by
    intro hq2; subst hq2
    have hE : Even (2 ^ eb) := Even.pow_of_ne_zero even_two (by omega)
    have : Even (p ^ ea + 2) := by rwa [← hdiff]
    have : Even (p ^ ea) := by
      rw [Nat.even_add] at this
      exact this.mpr even_two
    have : p = 2 := prime_of_even_pow hp this
    exact hp2 this
  have hp_odd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hq_odd : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  by_cases heaE : Even ea
  · by_cases hebE : Even eb
    · exact (not_both_even_exponents hdiff heaE hebE).elim
    · -- ea even: t^2 + 2 = q^eb
      obtain ⟨t, ht⟩ := even_pow_eq_sq p ea heaE
      have hZ : ((t : ℤ) ^ 2 + 2 : ℤ) = (q : ℤ) ^ eb := by
        have : t ^ 2 + 2 = q ^ eb := by
          have := hdiff
          omega
        exact_mod_cast this
      have todd : Odd t := by
        have : Odd (p ^ ea) := Odd.pow hp_odd
        have hte : t ^ 2 = p ^ ea := ht.symm
        have : Odd (t ^ 2) := by simpa [hte] using ‹Odd (p ^ ea)›
        simpa [Nat.odd_pow_iff (by decide : (2 : ℕ) ≠ 0)] using this
      obtain ⟨hq3, heb3, habs⟩ :=
        Zsqrtm2.sq_add_two_eq_odd_prime_pow (x := (t : ℤ)) (q := q) (n := eb)
          (nat_odd_to_int todd) hq hq_odd heb hZ
      have ht5 : t = 5 := by
        have : (t : ℤ) = 5 := by
          have : 0 ≤ (t : ℤ) := Nat.cast_nonneg _
          rwa [abs_of_nonneg this] at habs
        exact_mod_cast this
      have hpe : p ^ ea = 25 := by
        rw [ht, ht5]; rfl
      obtain ⟨rfl, rfl⟩ := eq_five_pow_two_of_prime_pow hp hea hpe
      exact ⟨rfl, rfl, hq3, heb3⟩
  · by_cases hebE : Even eb
    · -- eb even: y^2 - 2 = p^ea
      sorry
    · -- both exponents odd and ≥ 3
      have heaO : Odd ea := Nat.not_even_iff_odd.mp heaE
      have hebO : Odd eb := Nat.not_even_iff_odd.mp hebE
      have hea3 : 3 ≤ ea := by
        obtain ⟨k, hk⟩ := heaO
        omega
      have heb3 : 3 ≤ eb := by
        obtain ⟨k, hk⟩ := hebO
        omega
      exact (both_odd_exponents_impossible hp hq hea3 heb3 heaO hebO hdiff).elim


/--
A365416 According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/

theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · intro ⟨hL, hR⟩
    have hk3 : 3 ≤ k := compositePrimePow_ge hL
    obtain ⟨p, ea, hp, hea, hpe⟩ := hL
    obtain ⟨q, eb, hq, heb, hqe⟩ := hR
    have hsum : (2 * k - 1) + 2 = 2 * k + 1 := by omega
    have hdiff : q ^ eb = p ^ ea + 2 := by
      calc
        q ^ eb = 2 * k + 1 := hqe
        _ = (2 * k - 1) + 2 := hsum.symm
        _ = p ^ ea + 2 := by rw [hpe]
    obtain ⟨rfl, rfl, rfl, rfl⟩ := prime_pow_diff_two hp hq hea heb hdiff
    have : 2 * k - 1 = 25 := by
      rw [← hpe]; norm_num
    omega
  · rintro rfl
    exact thirteen_satisfies
