import FormalConjectures.Util.ProblemImports

open Nat

/--
A355898: $a(1) = a(2) = 1$; $a(n) = \gcd(a(n-1), a(n-2)) + \frac{a(n-1) + a(n-2)}{\gcd(a(n-1), a(n-2))}$.
-/
def A355898 : ℕ → ℕ
| 0 => 0 -- Sequence starts properly at A355898(1)
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

theorem A355898_succ (n : ℕ) : A355898 (n + 3) =
    Nat.gcd (A355898 (n+2)) (A355898 (n+1)) +
      (A355898 (n+2) + A355898 (n+1)) / Nat.gcd (A355898 (n+2)) (A355898 (n+1)) := by
  rw [A355898]

theorem A355898_pos : ∀ n, 0 < A355898 (n+1) ∧ 0 < A355898 (n+2) := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [A355898_succ]
    have := Nat.gcd_pos_of_pos_right (A355898 (n+2)) ih.1
    exact lt_of_lt_of_le this (Nat.le_add_right _ _)

def pairIter : ℕ → ℕ × ℕ
| 0 => (1, 1)
| k+1 => let u := (pairIter k).1; let v := (pairIter k).2; let g := Nat.gcd v u; (v, g + (v + u) / g)

theorem pairIter_eq (k : ℕ) : pairIter k = (A355898 (k+1), A355898 (k+2)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pairIter, ih, A355898]

set_option maxRecDepth 100000 in
theorem A355898_vals : (A355898 3773 + 1) % 195318521017 = 77940394259 ∧
    (A355898 3774 + 1) % 195318521017 = 99768150822 := by
  have h : pairIter 3772 = (A355898 3773, A355898 3774) := pairIter_eq 3772
  have h2 : ((pairIter 3772).1 + 1) % 195318521017 = 77940394259 ∧
      ((pairIter 3772).2 + 1) % 195318521017 = 99768150822 := by decide +kernel
  rw [h] at h2
  exact h2

def fibMod (p : ℕ) : ℕ → ℕ → ℕ × ℕ
| 0, _ => (0, 1 % p)
| fuel+1, n =>
  if n = 0 then (0, 1 % p) else
  let r := fibMod p fuel (n / 2)
  let a := r.1
  let b := r.2
  let c := (a * (2 * b + p - a)) % p
  let d := (a * a + b * b) % p
  if n % 2 = 0 then (c, d) else (d, (c + d) % p)

theorem fibMod_key1 (p : ℕ) (hp : 0 < p) (m : ℕ) :
    (Nat.fib m % p * (2 * (Nat.fib (m+1) % p) + p - Nat.fib m % p)) % p = Nat.fib (2*m) % p := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have h1 : Nat.fib m % p ≤ 2 * (Nat.fib (m+1) % p) + p := by
    have := Nat.mod_lt (Nat.fib m) hp; omega
  have h2 : Nat.fib m ≤ 2 * Nat.fib (m+1) := by
    have := Nat.fib_le_fib_succ (n := m); omega
  rw [Nat.fib_two_mul]
  push_cast [h1, h2]
  simp only [ZMod.natCast_mod, ZMod.natCast_self]
  ring

theorem fibMod_key2 (p : ℕ) (m : ℕ) :
    (Nat.fib m % p * (Nat.fib m % p) + Nat.fib (m+1) % p * (Nat.fib (m+1) % p)) % p = Nat.fib (2*m+1) % p := by
  rw [← ZMod.natCast_eq_natCast_iff']
  rw [Nat.fib_two_mul_add_one]
  push_cast
  simp only [ZMod.natCast_mod]
  ring

theorem fibMod_eq (p : ℕ) (hp : 0 < p) : ∀ fuel n, n < 2 ^ fuel →
    fibMod p fuel n = (Nat.fib n % p, Nat.fib (n+1) % p) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    simp at hn
    subst hn
    simp [fibMod]
  | succ fuel ih =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [fibMod]
    · have hm : n / 2 < 2 ^ fuel := by rw [pow_succ] at hn; omega
      have hr := ih (n/2) hm
      rw [fibMod, if_neg h0, hr]
      simp only
      rw [fibMod_key1 p hp, fibMod_key2 p]
      rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
      · subst hm
        have : 2 * m % 2 = 0 := by omega
        rw [if_pos this]
        simp only [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      · subst hm
        have h2 : (2 * m + 1) % 2 ≠ 0 := by omega
        rw [if_neg h2]
        have h3 : (2 * m + 1) / 2 = m := by omega
        rw [h3]
        rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring, Nat.fib_add_two, ← Nat.add_mod]

set_option maxRecDepth 100000 in
example : fibMod 195318521017 38 249580073232 = (117378126758, 21827756563) := by decide +kernel

/-- Contradiction lemma: if gcd ≥ 2 the two formulas differ. -/
theorem gcd_formula_ne (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hg : 2 ≤ Nat.gcd u v) :
    Nat.gcd u v + (u + v) / Nat.gcd u v ≠ 1 + u + v := by
  intro h
  set g := Nat.gcd u v with hg_def
  have hdvd : g ∣ u + v := Nat.dvd_add (Nat.gcd_dvd_left u v) (Nat.gcd_dvd_right u v)
  obtain ⟨q, hq⟩ := hdvd
  have hgu : g ≤ u := Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)
  rw [hq, Nat.mul_div_cancel_left _ (by omega)] at h
  have hq2 : 2 ≤ q := by
    by_contra hcon
    push_neg at hcon
    interval_cases q <;> omega
  have : g * q ≥ 2 * q := Nat.mul_le_mul_right q hg
  have : g * q ≥ g * 2 := Nat.mul_le_mul_left g hq2
  omega

/-- Closed form for a Fibonacci-like sequence in a commutative ring. -/
theorem fib_like_closed {R : Type*} [CommRing R] (c : ℕ → R) (M : ℕ)
    (hrec : ∀ m, m + 2 ≤ M → c (m+2) = c (m+1) + c m) :
    ∀ m, m + 1 ≤ M → c (m+1) = (Nat.fib (m+1) : R) * c 1 + (Nat.fib m : R) * c 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases m with _ | m
    · simp
    rcases m with _ | m
    · have := hrec 0 hm
      simpa using this
    · rw [hrec (m+1) hm, ih (m+1) (by omega) (by omega), ih m (by omega) (by omega)]
      rw [Nat.fib_add_two (n := m+1), Nat.fib_add_two (n := m)]
      push_cast
      ring



theorem final_contra (m p : ℕ) (hp : 2 ≤ p)
    (hrec : A355898 (3775 + m) = 1 + A355898 (3774 + m) + A355898 (3773 + m))
    (h1 : p ∣ A355898 (3773 + m)) (h2 : p ∣ A355898 (3774 + m)) : False := by
  have e := A355898_succ (3772 + m)
  rw [show 3772 + m + 3 = 3775 + m by omega, show 3772 + m + 2 = 3774 + m by omega,
    show 3772 + m + 1 = 3773 + m by omega] at e
  rw [e] at hrec
  have hu : 0 < A355898 (3774 + m) := by
    have := (A355898_pos (3773 + m)).1
    rwa [show 3773 + m + 1 = 3774 + m by omega] at this
  have hv : 0 < A355898 (3773 + m) := by
    have := (A355898_pos (3772 + m)).1
    rwa [show 3772 + m + 1 = 3773 + m by omega] at this
  have hg : 2 ≤ Nat.gcd (A355898 (3774 + m)) (A355898 (3773 + m)) := by
    have hdg := Nat.dvd_gcd h2 h1
    have hpos := Nat.gcd_pos_of_pos_left (A355898 (3773 + m)) hu
    have := Nat.le_of_dvd hpos hdg
    omega
  exact gcd_formula_ne _ _ hu hv hg hrec

set_option maxRecDepth 100000 in
theorem fibvals : Nat.fib 249580073232 % 195318521017 = 117378126758 ∧
    Nat.fib (249580073232 + 1) % 195318521017 = 21827756563 := by
  have h := fibMod_eq 195318521017 (by norm_num) 38 249580073232 (by norm_num)
  have h2 : fibMod 195318521017 38 249580073232 = (117378126758, 21827756563) := by decide +kernel
  rw [h2] at h
  exact ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.
-/
theorem oeis_a355898_conjecture (n : ℕ) (h : 3775 ≤ n) :
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) :=
by sorry

theorem oeis_a355898_conjecture.disproof : ¬ (type_of% @oeis_a355898_conjecture) := by
  intro H
  have hrec : ∀ m, A355898 (3775 + m) = 1 + A355898 (3774 + m) + A355898 (3773 + m) := by
    intro m
    have h := (H (3775 + m) (by omega)).1
    rw [show 3775 + m - 1 = 3774 + m by omega, show 3775 + m - 2 = 3773 + m by omega] at h
    exact h
  -- the sequence c m = a (3773 + m) + 1 in ZMod p
  let c : ℕ → ZMod 195318521017 := fun m => (A355898 (3773 + m) : ZMod 195318521017) + 1
  have hc : ∀ m, c (m+2) = c (m+1) + c m := by
    intro m
    simp only [c]
    rw [show 3773 + (m + 2) = 3775 + m by ring, hrec m, show 3773 + (m+1) = 3774 + m by ring]
    push_cast
    ring
  have hclosed := fib_like_closed c (249580073232 + 3) (fun m _ => hc m)
  have h1 := hclosed 249580073232 (by omega)
  have h2 := hclosed (249580073232+1) (by omega)
  have hvals := A355898_vals
  have hfib := fibvals
  have hc0 : c 0 = ((77940394259 : ℕ) : ZMod 195318521017) := by
    simp only [c]
    rw [← hvals.1, ZMod.natCast_mod]
    push_cast; ring
  have hc1 : c 1 = ((99768150822 : ℕ) : ZMod 195318521017) := by
    simp only [c]
    rw [← hvals.2, ZMod.natCast_mod]
    push_cast; ring
  have hf0 : (Nat.fib 249580073232 : ZMod 195318521017) = ((117378126758 : ℕ) : ZMod 195318521017) := by
    rw [← hfib.1, ZMod.natCast_mod]
  have hf1 : (Nat.fib (249580073232+1) : ZMod 195318521017) = ((21827756563 : ℕ) : ZMod 195318521017) := by
    rw [← hfib.2, ZMod.natCast_mod]
  have hf2 : (Nat.fib (249580073232+1+1) : ZMod 195318521017) = ((139205883321 : ℕ) : ZMod 195318521017) := by
    rw [Nat.fib_add_two, Nat.cast_add, hf0, hf1, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff']
  -- c (j+1) = 1 and c (j+2) = 1
  have hcj1 : c (249580073232+1) = 1 := by
    rw [h1, hf0, hf1, hc0, hc1, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff']
  have hcj2 : c (249580073232+1+1) = 1 := by
    rw [h2, hf1, hf2, hc0, hc1, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff']
  -- so p divides both
  have hd1 : 195318521017 ∣ A355898 (3773 + (249580073232+1)) := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h := hcj1
    change (A355898 (3773 + (249580073232+1)) : ZMod 195318521017) + 1 = 1 at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have hd2 : 195318521017 ∣ A355898 (3773 + (249580073232+1+1)) := by
    rw [← ZMod.natCast_eq_zero_iff]
    have h := hcj2
    change (A355898 (3773 + (249580073232+1+1)) : ZMod 195318521017) + 1 = 1 at h
    exact add_right_cancel (h.trans (zero_add _).symm)
  have hd2' : 195318521017 ∣ A355898 (3774 + (249580073232+1)) := by
    rw [show 3774 + (249580073232+1) = 3773 + (249580073232+1+1) by omega]
    exact hd2
  exact final_contra (249580073232+1) 195318521017 (by norm_num) (hrec (249580073232+1)) hd1 hd2'

