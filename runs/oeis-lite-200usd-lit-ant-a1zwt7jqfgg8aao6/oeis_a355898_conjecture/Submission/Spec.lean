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

-- symbolic recurrence
theorem Arec (n : ℕ) : A355898 (n+3) =
    Nat.gcd (A355898 (n+2)) (A355898 (n+1))
    + (A355898 (n+2) + A355898 (n+1)) / Nat.gcd (A355898 (n+2)) (A355898 (n+1)) := by
  rw [A355898]

-- positivity
theorem A_pos : ∀ n, 1 ≤ A355898 (n+1) ∧ 1 ≤ A355898 (n+2) := by
  intro n
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hgpos : 1 ≤ Nat.gcd (A355898 (k+2)) (A355898 (k+1)) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    show 1 ≤ A355898 (k+1+2)
    rw [show k+1+2 = k+3 from by omega, Arec k]
    exact le_trans hgpos (Nat.le_add_right _ _)

-- fast tail-recursive version
def stepA (xy : ℕ × ℕ) : ℕ × ℕ :=
  (xy.2, Nat.gcd xy.2 xy.1 + (xy.2 + xy.1) / Nat.gcd xy.2 xy.1)

def fastAux : ℕ → ℕ × ℕ
| 0 => (1, 1)
| n+1 => stepA (fastAux n)

theorem fastAux_correct : ∀ n, fastAux n = (A355898 (n+1), A355898 (n+2)) := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [fastAux, ih, stepA]
    have : A355898 (k+3) = Nat.gcd (A355898 (k+2)) (A355898 (k+1)) + (A355898 (k+2) + A355898 (k+1)) / Nat.gcd (A355898 (k+2)) (A355898 (k+1)) := by
      rw [A355898]
    rw [this]

-- base values as ModEq
set_option maxRecDepth 4000000 in
theorem base3773 : A355898 3773 ≡ 77940394258 [MOD 195318521017] := by
  show A355898 3773 % _ = 77940394258 % _
  rw [Nat.mod_eq_of_lt (show 77940394258 < 195318521017 by norm_num)]
  have h : A355898 3773 = (fastAux 3772).1 := by rw [fastAux_correct]
  rw [h]; decide

set_option maxRecDepth 4000000 in
theorem base3774 : A355898 3774 ≡ 99768150821 [MOD 195318521017] := by
  show A355898 3774 % _ = 99768150821 % _
  rw [Nat.mod_eq_of_lt (show 99768150821 < 195318521017 by norm_num)]
  have h : A355898 3774 = (fastAux 3772).2 := by rw [fastAux_correct]
  rw [h]; decide

-- fast fibonacci mod m over ZMod
def fibZ (m : ℕ) : ℕ → ℕ → ZMod m × ZMod m
| 0, _ => (0, 1)
| fuel+1, n =>
    if n = 0 then (0,1)
    else
      let k := n/2
      let pr := fibZ m fuel k
      let a := pr.1
      let b := pr.2
      let c := a * (2*b - a)
      let d := b*b + a*a
      if n % 2 = 0 then (c, d) else (d, c + d)

theorem fibZ_correct (m : ℕ) : ∀ (fuel n : ℕ), n < 2^fuel →
    fibZ m fuel n = ((Nat.fib n : ZMod m), (Nat.fib (n+1) : ZMod m)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    simp only [pow_zero, Nat.lt_one_iff] at hn
    subst hn
    simp [fibZ]
  | succ f ih =>
    intro n hn
    rw [fibZ]
    by_cases hn0 : n = 0
    · subst hn0; simp
    · simp only [hn0, if_false]
      have hk : n / 2 < 2 ^ f := by
        have : n < 2 * 2^f := by rw [pow_succ] at hn; omega
        omega
      have ihk := ih (n/2) hk
      set k := n / 2 with hkdef
      rw [ihk]
      simp only []
      have hle : Nat.fib k ≤ 2 * Nat.fib (k+1) := by
        have := Nat.fib_le_fib_succ (n := k)
        omega
      by_cases hpar : n % 2 = 0
      · simp only [hpar, if_true]
        have hn2 : n = 2 * k := by
          have := Nat.div_add_mod n 2
          omega
        rw [Prod.mk.injEq]; refine ⟨?_, ?_⟩
        · rw [hn2, Nat.fib_two_mul]
          push_cast [Nat.cast_sub hle]
          ring
        · rw [hn2]
          rw [show 2*k+1 = 2*k+1 from rfl, Nat.fib_two_mul_add_one]
          push_cast
          ring
      · simp only [hpar, if_false]
        have hn2 : n = 2 * k + 1 := by
          have := Nat.div_add_mod n 2
          omega
        rw [Prod.mk.injEq]; refine ⟨?_, ?_⟩
        · rw [hn2, Nat.fib_two_mul_add_one]
          push_cast
          ring
        · rw [hn2]
          rw [show 2*k+1+1 = (2*k)+2 from by ring, Nat.fib_add_two, Nat.fib_two_mul, Nat.fib_two_mul_add_one]
          push_cast [Nat.cast_sub hle]
          ring

set_option maxRecDepth 4000000 in
theorem fibvals1 : fibZ 195318521017 40 249580073232 =
    ((117378126758 : ZMod 195318521017), (21827756563 : ZMod 195318521017)) := by
  decide

set_option maxRecDepth 4000000 in
theorem fibvals2 : fibZ 195318521017 40 249580073233 =
    ((21827756563 : ZMod 195318521017), (139205883321 : ZMod 195318521017)) := by
  decide

theorem fibtm1 : Nat.fib 249580073232 ≡ 117378126758 [MOD 195318521017] := by
  have hc := fibZ_correct 195318521017 40 249580073232 (by norm_num)
  rw [fibvals1, Prod.mk.injEq] at hc
  have hfst := hc.1
  rw [show (117378126758 : ZMod 195318521017) = ((117378126758:ℕ):ZMod 195318521017) from (Nat.cast_ofNat).symm] at hfst
  rw [ZMod.natCast_eq_natCast_iff] at hfst
  exact hfst.symm

theorem fibt : Nat.fib 249580073233 ≡ 21827756563 [MOD 195318521017] := by
  have hc := fibZ_correct 195318521017 40 249580073233 (by norm_num)
  rw [fibvals2, Prod.mk.injEq] at hc
  have hfst := hc.1
  rw [show (21827756563 : ZMod 195318521017) = ((21827756563:ℕ):ZMod 195318521017) from (Nat.cast_ofNat).symm] at hfst
  rw [ZMod.natCast_eq_natCast_iff] at hfst
  exact hfst.symm

theorem fibtp1 : Nat.fib 249580073234 ≡ 139205883321 [MOD 195318521017] := by
  have hc := fibZ_correct 195318521017 40 249580073233 (by norm_num)
  rw [fibvals2, Prod.mk.injEq] at hc
  have hsnd := hc.2
  rw [show (139205883321 : ZMod 195318521017) = ((139205883321:ℕ):ZMod 195318521017) from (Nat.cast_ofNat).symm] at hsnd
  rw [ZMod.natCast_eq_natCast_iff] at hsnd
  -- hsnd : 249580073233 + 1 ≡ ... ; note 249580073233+1 = 249580073234
  exact hsnd.symm

theorem fibClosed (c : ℕ → ℕ) (hc : ∀ s, c (s+2) = c (s+1) + c s) :
    ∀ m, c (m+1) = Nat.fib (m+1) * c 1 + Nat.fib m * c 0
       ∧ c (m+2) = Nat.fib (m+2) * c 1 + Nat.fib (m+1) * c 0 := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · have h0 := hc 0
      rw [h0]
      simp [Nat.fib_two]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    have hk := hc (k+1)
    rw [show k+1+2 = k+3 from by omega, show k+1+1 = k+2 from by omega] at hk ⊢
    rw [hk, ih2, ih1]
    have e2 : Nat.fib (k+2) = Nat.fib k + Nat.fib (k+1) := Nat.fib_add_two
    have e3 : Nat.fib (k+3) = Nat.fib (k+1) + Nat.fib (k+2) := by
      have h := @Nat.fib_add_two (k+1)
      rw [show k+1+2 = k+3 from by omega, show k+1+1 = k+2 from by omega] at h
      exact h
    rw [e3, e2]
    ring

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.

This conjecture is FALSE: it fails (at the latest) at n = 249580077008.
-/
theorem oeis_a355898_conjecture.disproof : ¬ ∀ (n : ℕ), 3775 ≤ n →
    (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
    ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1) := by
  intro h
  have hP1 : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n-1) + A355898 (n-2) :=
    fun n hn => (h n hn).1
  -- Fibonacci-like recurrence for c s = A355898 (3773+s) + 1
  set c : ℕ → ℕ := fun s => A355898 (3773 + s) + 1 with hcdef
  have hd : ∀ s, c (s+2) = c (s+1) + c s := by
    intro s
    have hr := hP1 (3775+s) (by omega)
    rw [show (3775+s)-1 = 3774+s from by omega, show (3775+s)-2 = 3773+s from by omega] at hr
    simp only [hcdef]
    rw [show 3773+(s+2) = 3775+s from by omega, show 3773+(s+1) = 3774+s from by omega]
    omega
  have hcf := fibClosed c hd
  -- c 0 and c 1
  have hc0 : c 0 = A355898 3773 + 1 := by simp [hcdef]
  have hc1 : c 1 = A355898 3774 + 1 := by simp [hcdef]
  -- Evaluate closed form at m = 249580073232
  obtain ⟨HC1, HC2⟩ := hcf 249580073232
  rw [hc0, hc1] at HC1 HC2
  -- HC1 : c (249580073232+1) = fib(249580073232+1)*(A3774+1) + fib 249580073232 * (A3773+1)
  -- Simplify c indices to A355898 values
  have hval1 : c 249580073233 = A355898 249580077006 + 1 := by
    show A355898 (3773 + 249580073233) + 1 = A355898 249580077006 + 1
    norm_num
  have hval2 : c 249580073234 = A355898 249580077007 + 1 := by
    show A355898 (3773 + 249580073234) + 1 = A355898 249580077007 + 1
    norm_num
  rw [show (249580073232:ℕ)+1 = 249580073233 from by norm_num, hval1] at HC1
  rw [show (249580073232:ℕ)+2 = 249580073234 from by norm_num,
      show (249580073232:ℕ)+1 = 249580073233 from by norm_num, hval2] at HC2
  -- ModEq base facts
  have d0m : A355898 3773 + 1 ≡ 77940394259 [MOD 195318521017] := base3773.add_right 1
  have d1m : A355898 3774 + 1 ≡ 99768150822 [MOD 195318521017] := base3774.add_right 1
  -- p divides A355898 249580077006
  have m1 : A355898 249580077006 + 1 ≡ 1 [MOD 195318521017] := by
    rw [HC1]
    calc Nat.fib 249580073233 * (A355898 3774 + 1) + Nat.fib 249580073232 * (A355898 3773 + 1)
        ≡ 21827756563 * 99768150822 + 117378126758 * 77940394259 [MOD 195318521017] :=
          Nat.ModEq.add (Nat.ModEq.mul fibt d1m) (Nat.ModEq.mul fibtm1 d0m)
      _ ≡ 1 [MOD 195318521017] := by decide
  have hpa2 : (195318521017 : ℕ) ∣ A355898 249580077006 := by
    have : A355898 249580077006 ≡ 0 [MOD 195318521017] :=
      Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) (by simpa using m1)
    exact (Nat.modEq_zero_iff_dvd).mp this
  -- p divides A355898 249580077007
  have m2 : A355898 249580077007 + 1 ≡ 1 [MOD 195318521017] := by
    rw [HC2]
    calc Nat.fib 249580073234 * (A355898 3774 + 1) + Nat.fib 249580073233 * (A355898 3773 + 1)
        ≡ 139205883321 * 99768150822 + 21827756563 * 77940394259 [MOD 195318521017] :=
          Nat.ModEq.add (Nat.ModEq.mul fibtp1 d1m) (Nat.ModEq.mul fibt d0m)
      _ ≡ 1 [MOD 195318521017] := by decide
  have hpa1 : (195318521017 : ℕ) ∣ A355898 249580077007 := by
    have : A355898 249580077007 ≡ 0 [MOD 195318521017] :=
      Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) (by simpa using m2)
    exact (Nat.modEq_zero_iff_dvd).mp this
  -- positivity
  have ha1pos : 1 ≤ A355898 249580077007 := by
    have := (A_pos 249580077006).1
    simpa using this
  have ha2pos : 1 ≤ A355898 249580077006 := by
    have := (A_pos 249580077005).1
    simpa using this
  -- P1 and def at n0 = 249580077008
  have hP1n0 : A355898 249580077008 = 1 + A355898 249580077007 + A355898 249580077006 := by
    have := hP1 249580077008 (by norm_num)
    rwa [show (249580077008:ℕ)-1 = 249580077007 from by norm_num,
         show (249580077008:ℕ)-2 = 249580077006 from by norm_num] at this
  have hdefn0 : A355898 249580077008 =
      Nat.gcd (A355898 249580077007) (A355898 249580077006)
      + (A355898 249580077007 + A355898 249580077006) /
        Nat.gcd (A355898 249580077007) (A355898 249580077006) := by
    have hh := Arec 249580077005
    rw [show (249580077005:ℕ)+3 = 249580077008 from by norm_num,
        show (249580077005:ℕ)+2 = 249580077007 from by norm_num,
        show (249580077005:ℕ)+1 = 249580077006 from by norm_num] at hh
    exact hh
  -- contradiction
  set a1 := A355898 249580077007 with ha1def
  set a2 := A355898 249580077006 with ha2def
  set g := Nat.gcd a1 a2 with hgdef
  have hpg : (195318521017 : ℕ) ∣ g := Nat.dvd_gcd hpa1 hpa2
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hg_ge : (195318521017 : ℕ) ≤ g := Nat.le_of_dvd hgpos hpg
  have hg_dvd_sum : g ∣ (a1 + a2) := Nat.dvd_add (Nat.gcd_dvd_left a1 a2) (Nat.gcd_dvd_right a1 a2)
  have hr : (a1 + a2) / g * g = a1 + a2 := Nat.div_mul_cancel hg_dvd_sum
  have hg_le_a1 : g ≤ a1 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left a1 a2)
  set r := (a1 + a2) / g with hrdef
  have eq0 : 1 + a1 + a2 = g + r := by rw [← hP1n0, hdefn0]
  have hsum : g * r = a1 + a2 := by rw [Nat.mul_comm]; exact hr
  -- push to integers
  have hz : (g:ℤ) + r = 1 + (g:ℤ) * r := by
    have A : (1:ℤ) + a1 + a2 = (g:ℤ) + r := by exact_mod_cast eq0
    have B : (g:ℤ) * r = (a1:ℤ) + a2 := by exact_mod_cast hsum
    linarith
  have hg2 : (2:ℤ) ≤ (g:ℤ) := by
    have : (195318521017:ℤ) ≤ g := by exact_mod_cast hg_ge
    linarith
  have hr1 : (r:ℤ) = 1 := by
    have h2 : ((r:ℤ) - 1) * ((g:ℤ) - 1) = 0 := by linear_combination -hz
    rcases mul_eq_zero.mp h2 with hh | hh
    · linarith
    · linarith
  have hgz : (g:ℤ) = (a1:ℤ) + a2 := by
    have B : (g:ℤ) * r = (a1:ℤ) + a2 := by exact_mod_cast hsum
    rw [hr1] at B; linarith
  have hgla : (g:ℤ) ≤ a1 := by exact_mod_cast hg_le_a1
  have ha2z : (1:ℤ) ≤ a2 := by exact_mod_cast ha2pos
  linarith
