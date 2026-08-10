import FormalConjectures.Util.ProblemImports
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.style.moduleDocstring false
set_option linter.unusedVariables false


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

/-  A linear evaluator for the first few thousand terms. -/

def Astep (p : ℕ × ℕ) : ℕ × ℕ :=
  let g := Nat.gcd p.2 p.1
  (p.2, g + (p.2 + p.1) / g)

def Apair : ℕ → ℕ × ℕ
| 0 => (0,1)
| 1 => (1,1)
| n+2 => Astep (Apair (n+1))

opaque Apair_spec (n : ℕ) : Apair n = (A355898 n, A355898 (n+1)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Apair, A355898]
  | one => simp [Apair, A355898]
  | more n ih0 ih1 =>
      rw [Apair, ih1]
      cases n with
      | zero => simp [Astep, A355898]
      | succ n =>
          change Astep (A355898 (n.succ + 1), A355898 (n.succ + 1 + 1)) =
            (A355898 (n.succ + 2), A355898 (n.succ + 2 + 1))
          simp [Astep]
          rw [show n.succ + 2 + 1 = (n+1) + 3 by omega]
          rw [A355898]
          rfl

/- Fast doubling for Fibonacci numbers modulo `p`, along a fixed binary expansion. -/

def fibStepMod (m : ℕ) (p : ℕ × ℕ) (bit : Bool) : ℕ × ℕ :=
  let a := p.1; let b := p.2
  let c := (a * ((2*b + m - a) % m)) % m
  let d := (a*a + b*b) % m
  if bit then (d,(c+d)%m) else (c,d)

def evalBitsMod (m : ℕ) : ℕ × ℕ → List Bool → ℕ × ℕ
| p, [] => p
| p, b::bs => evalBitsMod m (fibStepMod m p b) bs

def bitsValFrom : ℕ → List Bool → ℕ
| k, [] => k
| k, b::bs => bitsValFrom (2*k + b.toNat) bs

lemma fib_two_mul_zmod (p q : ℕ) :
    (Nat.fib q : ZMod p) * (2 * (Nat.fib (q+1) : ZMod p) - (Nat.fib q : ZMod p)) =
      (Nat.fib (2*q) : ZMod p) := by
  have hle : Nat.fib q ≤ 2 * Nat.fib (q+1) := by
    exact le_trans Nat.fib_le_fib_succ (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2))
  rw [Nat.fib_two_mul q]
  rw [Nat.cast_mul, Nat.cast_sub hle]
  norm_num

lemma fib_two_mul_add_one_zmod (p q : ℕ) :
    (Nat.fib q : ZMod p) * (Nat.fib q : ZMod p) +
      (Nat.fib (q+1) : ZMod p) * (Nat.fib (q+1) : ZMod p) =
      (Nat.fib (2*q+1) : ZMod p) := by
  rw [Nat.fib_two_mul_add_one q]
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow]
  ring

lemma fib_two_mul_add_two_zmod (p q : ℕ) :
    (Nat.fib q : ZMod p) * (2 * (Nat.fib (q+1) : ZMod p) - (Nat.fib q : ZMod p)) +
      ((Nat.fib q : ZMod p) * (Nat.fib q : ZMod p) +
        (Nat.fib (q+1) : ZMod p) * (Nat.fib (q+1) : ZMod p)) =
      (Nat.fib (2*q+2) : ZMod p) := by
  rw [show 2*q+2 = 2*q+1+1 by omega]
  rw [Nat.fib_add_two, Nat.cast_add]
  rw [← fib_two_mul_zmod p q, ← fib_two_mul_add_one_zmod p q]

lemma fibStepMod_all (m k : ℕ) (p : ℕ × ℕ) (hm : 0 < m)
    (h1lt : p.1 < m) (h2lt : p.2 < m)
    (h1 : (p.1 : ZMod m) = (Nat.fib k : ZMod m))
    (h2 : (p.2 : ZMod m) = (Nat.fib (k+1) : ZMod m)) (bit : Bool) :
    (fibStepMod m p bit).1 < m ∧ (fibStepMod m p bit).2 < m ∧
    ((fibStepMod m p bit).1 : ZMod m) = (Nat.fib (2*k + bit.toNat) : ZMod m) ∧
    ((fibStepMod m p bit).2 : ZMod m) = (Nat.fib (2*k + bit.toNat + 1) : ZMod m) := by
  let a:=p.1; let b:=p.2
  have ha_le : a ≤ 2*b + m := by omega
  have hsub0 : ((2*b + m - a : ℕ) : ZMod m) = (2*(b:ZMod m) - (a:ZMod m)) := by
    rw [Nat.cast_sub ha_le]; norm_num
  cases bit
  · simp [fibStepMod, a, b]
    refine ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hm, ?_, ?_⟩
    · rw [hsub0, h1, h2]
      simpa using fib_two_mul_zmod m k
    · rw [h1, h2]
      simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using fib_two_mul_add_one_zmod m k
  · simp [fibStepMod, a, b]
    refine ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hm, ?_, ?_⟩
    · rw [h1, h2]
      simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using fib_two_mul_add_one_zmod m k
    · rw [show 2*k + 1 + 1 = 2*k+2 by omega]
      rw [hsub0, h1, h2]
      exact fib_two_mul_add_two_zmod m k

theorem evalBitsMod_all (m k : ℕ) (p : ℕ × ℕ) (bs : List Bool) (hm : 0 < m)
    (h1lt : p.1 < m) (h2lt : p.2 < m)
    (h1 : (p.1 : ZMod m) = (Nat.fib k : ZMod m))
    (h2 : (p.2 : ZMod m) = (Nat.fib (k+1) : ZMod m)) :
    (evalBitsMod m p bs).1 < m ∧ (evalBitsMod m p bs).2 < m ∧
    ((evalBitsMod m p bs).1 : ZMod m) = (Nat.fib (bitsValFrom k bs) : ZMod m) ∧
    ((evalBitsMod m p bs).2 : ZMod m) = (Nat.fib (bitsValFrom k bs + 1) : ZMod m) := by
  induction bs generalizing k p with
  | nil => simpa [evalBitsMod, bitsValFrom] using And.intro h1lt (And.intro h2lt (And.intro h1 h2))
  | cons bit bs ih =>
      have st := fibStepMod_all m k p hm h1lt h2lt h1 h2 bit
      exact ih (2*k+bit.toNat) (fibStepMod m p bit) st.1 st.2.1 st.2.2.1 st.2.2.2

abbrev P : ℕ := 195318521017
abbrev M : ℕ := 249580077007
abbrev Nbad : ℕ := 249580077008

set_option maxRecDepth 20000 in
opaque Apair_cert :
    ((Apair 3772).1 : ZMod P) = (21827756562 : ZMod P) ∧
    ((Apair 3774).1 : ZMod P) = (99768150821 : ZMod P) := by
  decide

opaque A3772_zmod : (A355898 3772 : ZMod P) = (21827756562 : ZMod P) := by
  have h : (Apair 3772).1 = A355898 3772 := by
    simpa using congrArg Prod.fst (Apair_spec 3772)
  rw [← h]
  exact Apair_cert.1

opaque A3774_zmod : (A355898 3774 : ZMod P) = (99768150821 : ZMod P) := by
  have h : (Apair 3774).1 = A355898 3774 := by
    simpa using congrArg Prod.fst (Apair_spec 3774)
  rw [← h]
  exact Apair_cert.2

def bits_249580073235 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, true, true]

def bits_249580073233 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, true]

def bits_249580073234 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, true, false]

def bits_249580073232 : List Bool :=
  [true, true, true, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, false, false, false, true, true, false, true, true, false, false, false, true, false, false, false, true, false, false, false, false]

opaque fib_bits_zmod (bs : List Bool) (n r : ℕ)
    (h : (evalBitsMod P (0,1%P) bs).1 = r ∧ bitsValFrom 0 bs = n) :
    (Nat.fib n : ZMod P) = (r : ZMod P) := by
  have h0 := (evalBitsMod_all P 0 (0,1%P) bs (by norm_num [P]) (by norm_num [P]) (by norm_num [P]) (by simp) (by simp)).2.2.1
  rw [h.2] at h0
  rw [← h0, h.1]

set_option maxRecDepth 1000 in
opaque fib_cert_249580073235 :
    (evalBitsMod P (0,1%P) bits_249580073235).1 = 161033639884 ∧
      bitsValFrom 0 bits_249580073235 = 249580073235 := by
  decide

set_option maxRecDepth 1000 in
opaque fib_cert_249580073233 :
    (evalBitsMod P (0,1%P) bits_249580073233).1 = 21827756563 ∧
      bitsValFrom 0 bits_249580073233 = 249580073233 := by
  decide

set_option maxRecDepth 1000 in
opaque fib_cert_249580073234 :
    (evalBitsMod P (0,1%P) bits_249580073234).1 = 139205883321 ∧
      bitsValFrom 0 bits_249580073234 = 249580073234 := by
  decide

set_option maxRecDepth 1000 in
opaque fib_cert_249580073232 :
    (evalBitsMod P (0,1%P) bits_249580073232).1 = 117378126758 ∧
      bitsValFrom 0 bits_249580073232 = 249580073232 := by
  decide

opaque fib_249580073235 : (Nat.fib 249580073235 : ZMod P) = (161033639884 : ZMod P) :=
  fib_bits_zmod bits_249580073235 _ _ fib_cert_249580073235
opaque fib_249580073233 : (Nat.fib 249580073233 : ZMod P) = (21827756563 : ZMod P) :=
  fib_bits_zmod bits_249580073233 _ _ fib_cert_249580073233
opaque fib_249580073234 : (Nat.fib 249580073234 : ZMod P) = (139205883321 : ZMod P) :=
  fib_bits_zmod bits_249580073234 _ _ fib_cert_249580073234
opaque fib_249580073232 : (Nat.fib 249580073232 : ZMod P) = (117378126758 : ZMod P) :=
  fib_bits_zmod bits_249580073232 _ _ fib_cert_249580073232

opaque cast_tsub_tsub_eq_zero_of_zmod (X Y : ℕ)
    (h : (X : ZMod P) - (Y : ZMod P) - 1 = 0) :
    (((X - Y - 1 : ℕ) : ZMod P) = 0) := by
  by_cases hYX : Y ≤ X
  · by_cases h1 : 1 ≤ X - Y
    · rw [Nat.cast_sub h1, Nat.cast_sub hYX]
      exact h
    · have hz : X - Y - 1 = 0 := by omega
      rw [hz]
      norm_num
  · have hz : X - Y - 1 = 0 := by omega
    rw [hz]
    norm_num

opaque rhs_m_cast :
    (((A355898 3774 + 1) * Nat.fib (M - 3772) - (A355898 3772 + 1) * Nat.fib (M - 3774) - 1 : ℕ) : ZMod P) = 0 := by
  apply cast_tsub_tsub_eq_zero_of_zmod
  rw [show M - 3772 = 249580073235 by norm_num, show M - 3774 = 249580073233 by norm_num]
  push_cast
  rw [A3774_zmod, A3772_zmod, fib_249580073235, fib_249580073233]
  decide

opaque rhs_mprev_cast :
    (((A355898 3774 + 1) * Nat.fib ((M-1) - 3772) - (A355898 3772 + 1) * Nat.fib ((M-1) - 3774) - 1 : ℕ) : ZMod P) = 0 := by
  apply cast_tsub_tsub_eq_zero_of_zmod
  rw [show (M-1) - 3772 = 249580073234 by norm_num, show (M-1) - 3774 = 249580073232 by norm_num]
  push_cast
  rw [A3774_zmod, A3772_zmod, fib_249580073234, fib_249580073232]
  decide

opaque not_recurrence_if_common_dvd (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hdx : P ∣ x) (hdy : P ∣ y) :
    Nat.gcd x y + (x + y) / Nat.gcd x y ≠ 1 + x + y := by
  intro heq
  let g := Nat.gcd x y
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hpdg : P ∣ g := Nat.dvd_gcd hdx hdy
  have hgle : P ≤ g := Nat.le_of_dvd hgpos hpdg
  have hg2 : 2 ≤ g := by norm_num [P] at hgle ⊢; omega
  rcases Nat.gcd_dvd_left x y with ⟨a, hxa⟩
  rcases Nat.gcd_dvd_right x y with ⟨b, hyb⟩
  have hxa' : x = g * a := hxa
  have hyb' : y = g * b := hyb
  have ha : 0 < a := by
    by_contra h0
    have : a = 0 := by omega
    subst a
    simp [g] at hxa'
    omega
  have hb : 0 < b := by
    by_contra h0
    have : b = 0 := by omega
    subst b
    simp [g] at hyb'
    omega
  have hdiv : (x + y) / g = a + b := by
    rw [hxa', hyb']
    rw [← Nat.mul_add]
    exact Nat.mul_div_right (a+b) hgpos
  have heq1 : g + (a+b) = 1 + x + y := by
    rw [hdiv] at heq
    exact heq
  have heq2 : g + (a+b) = 1 + g*a + g*b := by
    rw [hxa', hyb'] at heq1
    simpa [add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] using heq1
  have hs2 : 2 ≤ a + b := by omega
  have hlt : g + (a+b) < 1 + g*a + g*b := by
    calc
      g + (a+b) ≤ g * (a+b) := Nat.add_le_mul hg2 hs2
      _ = g*a + g*b := by rw [Nat.mul_add]
      _ < 1 + (g*a + g*b) := by simpa [Nat.add_comm] using Nat.lt_succ_self (g*a + g*b)
      _ = 1 + g*a + g*b := by rw [add_assoc]
  exact (_root_.ne_of_lt hlt) heq2

/-- The OEIS conjecture is false.  The closed formula would force two consecutive
terms to be divisible by `195318521017`; the defining recurrence is then strictly
smaller than `1 + a(n-1)+a(n-2)`. -/
opaque oeis_a355898_conjecture.disproof_aux :
  ¬ (∀ (n : ℕ), 3775 ≤ n →
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro H
  have hm3 := (H M (by norm_num)).2.2
  have hm1_3 := (H (M-1) (by norm_num)).2.2
  have hxm_z : (A355898 M : ZMod P) = 0 := by
    rw [hm3]
    exact rhs_m_cast
  have hym_z : (A355898 (M-1) : ZMod P) = 0 := by
    rw [hm1_3]
    exact rhs_mprev_cast
  have hdx : P ∣ A355898 M := (ZMod.natCast_eq_zero_iff (A355898 M) P).mp hxm_z
  have hdy : P ∣ A355898 (M-1) := (ZMod.natCast_eq_zero_iff (A355898 (M-1)) P).mp hym_z
  let x := A355898 M
  let y := A355898 (M-1)
  let g := Nat.gcd x y
  have hm1 := (H M (by norm_num)).1
  have hm1prev := (H (M-1) (by norm_num)).1
  have hxpos : 0 < x := by
    dsimp [x]
    rw [hm1]
    omega
  have hypos : 0 < y := by
    dsimp [y]
    change 0 < A355898 (M-1)
    rw [hm1prev]
    omega
  have hdef : A355898 Nbad = g + (x+y)/g := by
    change A355898 (249580077005 + 3) = g + (x+y)/g
    rw [A355898]
    rfl
  have htail := (H Nbad (by norm_num)).1
  have heq : g + (x+y)/g = 1 + x + y := by
    rw [← hdef]
    exact htail
  exact not_recurrence_if_common_dvd x y hxpos hypos hdx hdy heq

theorem oeis_a355898_conjecture.disproof :
  ¬ (∀ (n : ℕ), 3775 ≤ n →
  (A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
  ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
  ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) :=
  oeis_a355898_conjecture.disproof_aux

