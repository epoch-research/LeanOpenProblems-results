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

/-!
### Disproof of the conjecture

We show that the three formulas cannot hold for every `n ≥ 3775`.

**Strategy.**  Assume formula (1) holds for all `n ≥ 3775`.  Then the shifted sequence
`u k = A355898 (3773 + k) + 1` satisfies the Fibonacci recurrence
`u (k+2) = u (k+1) + u k`, hence — viewed in `ZMod p` for the prime
`p = 195318521017` — it is given by the closed form
`u k = u 0 * fib (k+1) + (u 1 - u 0) * fib k`.

A discrete-logarithm computation in `GF(p²)` (done outside of Lean; `p` divides
`D + 1` where `D` is the invariant `b₁² - b₁b₀ - b₀²` of the recurrence) produces
the explicit exponent `k₀ = 249580073233` with `u k₀ = u (k₀+1) = 1` in `ZMod p`,
i.e. `p` divides both `A355898 (3773 + k₀)` and `A355898 (3774 + k₀)`.

Consequently `g = gcd(A355898 (3774 + k₀), A355898 (3773 + k₀)) ≥ p ≥ 2`, and the
defining recurrence gives `A355898 (3775 + k₀) = g + (x + y) / g < 1 + x + y`,
contradicting formula (1) at `n = 3775 + k₀`.

The only nontrivial computations Lean has to check are:
* the exact values of `A355898 3773` and `A355898 3774` (via an efficient pair iterator);
* Fibonacci values `fib k₀`, `fib (k₀ + 1)` modulo `p` (via binary doubling).
-/

namespace OeisA355898

/- ### An efficient iterator computing consecutive pairs of `A355898`. -/

def step (q : ℕ × ℕ) : ℕ × ℕ :=
  (q.2, Nat.gcd q.2 q.1 + (q.2 + q.1) / Nat.gcd q.2 q.1)

def S : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => step (S n)

lemma S_eq (n : ℕ) : S n = (A355898 (n + 1), A355898 (n + 2)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [S, ih]; simp only [step, A355898]

set_option maxRecDepth 1000000 in
lemma S3772 : S 3772 = (7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617, 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283) := by decide

lemma pair3773 : ((7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 : ℕ), (58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 : ℕ)) = (A355898 3773, A355898 3774) := by
  have h := S_eq 3772
  rw [S3772] at h
  simpa using h

lemma a3773_cast : (A355898 3773 : ZMod 195318521017) = ((77940394258 : ℕ) : ZMod 195318521017) := by
  have hmod : (((7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 : ℕ) % 195318521017 : ℕ) : ZMod 195318521017) = ((77940394258 : ℕ) : ZMod 195318521017) := by norm_num
  have hp := pair3773
  rw [Prod.mk.injEq] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [← h1, ← ZMod.natCast_mod 7425763529563641656343950118919476361854496605895809221806730373403166836250554598912216231675893720246035801259006550047856708037120829047465510779038156824824471379179617511560002202519545851588002449939311799386981815701822134145342315490302441466084428121032068752422449560944883235622403419180199789756819086776097880710867416354388617 195318521017, hmod]

lemma a3774_cast : (A355898 3774 : ZMod 195318521017) = ((99768150821 : ℕ) : ZMod 195318521017) := by
  have hmod : (((58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 : ℕ) % 195318521017 : ℕ) : ZMod 195318521017) = ((99768150821 : ℕ) : ZMod 195318521017) := by norm_num
  have hp := pair3773
  rw [Prod.mk.injEq] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [← h2, ← ZMod.natCast_mod 58247620166949433924152349110387952083697979943894432862563828976040095229520447551846447106151838744759854302693877131497631690251007647345990824945923089962629840263458365713419764969401061223771086474022889794898006618157003102858034604369810330403334719184536749507414607510201847709900422830948846697746280327160364518807058513260008283 195318521017, hmod]

/- ### Fibonacci numbers modulo `p = 195318521017` via binary doubling. -/

def dbl : ℕ × ℕ → Bool → ℕ × ℕ
  | (x, y), false => (x * (2 * y + (195318521017 - x)) % 195318521017, (x * x + y * y) % 195318521017)
  | (x, y), true =>
      ((x * x + y * y) % 195318521017, (x * (2 * y + (195318521017 - x)) % 195318521017 + (x * x + y * y) % 195318521017) % 195318521017)

def fpm : List Bool → ℕ × ℕ
  | [] => (0, 1)
  | b :: bs => dbl (fpm bs) b

def bval : List Bool → ℕ
  | [] => 0
  | b :: bs => (match b with | false => 0 | true => 1) + 2 * bval bs

lemma fpm_correct (bs : List Bool) :
    ((fpm bs).1 : ZMod 195318521017) = (fib (bval bs) : ℕ) ∧
    ((fpm bs).2 : ZMod 195318521017) = (fib (bval bs + 1) : ℕ) ∧ (fpm bs).1 ≤ 195318521017 := by
  induction bs with
  | nil => refine ⟨by simp [fpm, bval], by simp [fpm, bval], by norm_num [fpm]⟩
  | cons b bs ih =>
    obtain ⟨ihx, ihy, hxle⟩ := ih
    have hmlt : ∀ m : ℕ, m % 195318521017 ≤ 195318521017 := fun m => le_of_lt (Nat.mod_lt _ (by norm_num))
    set m := bval bs with hm
    rcases hfp : fpm bs with ⟨fx, fy⟩
    rw [hfp] at ihx ihy hxle
    simp only at ihx ihy hxle
    have hfle : fib m ≤ 2 * fib (m + 1) := by
      have := Nat.fib_le_fib_succ (n := m); linarith
    have hc : ((fx * (2 * fy + (195318521017 - fx)) % 195318521017 : ℕ) : ZMod 195318521017) = (fib (2 * m) : ℕ) := by
      rw [ZMod.natCast_mod, Nat.fib_two_mul]
      push_cast [Nat.cast_sub hxle, Nat.cast_sub hfle]
      rw [ihx, ihy, show ((195318521017 : ZMod 195318521017)) = 0 from by decide]
      ring
    have hd : (((fx * fx + fy * fy) % 195318521017 : ℕ) : ZMod 195318521017) = (fib (2 * m + 1) : ℕ) := by
      rw [ZMod.natCast_mod, Nat.fib_two_mul_add_one]
      push_cast
      rw [ihx, ihy]
      ring
    have hstep : fpm (b :: bs) = dbl (fx, fy) b := by rw [fpm, hfp]
    cases b with
    | false =>
      rw [hstep]
      refine ⟨?_, ?_, hmlt _⟩
      · simpa [dbl, bval, ← hm] using hc
      · simpa [dbl, bval, ← hm] using hd
    | true =>
      rw [hstep]
      refine ⟨?_, ?_, hmlt _⟩
      · simpa [dbl, bval, ← hm, show 1 + 2 * m = 2 * m + 1 by omega] using hd
      · have he : (((fx * (2 * fy + (195318521017 - fx)) % 195318521017 + (fx * fx + fy * fy) % 195318521017) % 195318521017 : ℕ)
              : ZMod 195318521017) = (fib (2 * m + 2) : ℕ) := by
          rw [ZMod.natCast_mod]
          push_cast
          rw [hc, hd, show 2 * m + 2 = 2 * m + 0 + 2 from rfl, Nat.fib_add_two]
          push_cast
          ring
        simpa [dbl, bval, ← hm, show 1 + 2 * m + 1 = 2 * m + 2 by omega] using he

def K0BITS : List Bool := [true, false, false, false, true, false, false, false, true, false, false, false, true, true, false, true, true, false, false, false, false, true, false, false, false, false, true, true, true, false, false, false, false, true, false, true, true, true]

lemma bval_K0 : bval K0BITS = 249580073233 := by decide

lemma fpm_K0 : fpm K0BITS = (21827756563, 139205883321) := by decide

lemma fib_k0 : ((fib 249580073233 : ℕ) : ZMod 195318521017) = ((21827756563 : ℕ) : ZMod 195318521017) := by
  have h := (fpm_correct K0BITS).1
  rw [bval_K0, fpm_K0] at h
  exact h.symm

lemma fib_k0succ : ((fib (249580073233 + 1) : ℕ) : ZMod 195318521017) = ((139205883321 : ℕ) : ZMod 195318521017) := by
  have h := (fpm_correct K0BITS).2.1
  rw [bval_K0, fpm_K0] at h
  exact h.symm

lemma fib_k0succ2 : ((fib (249580073233 + 1 + 1) : ℕ) : ZMod 195318521017) = ((161033639884 : ℕ) : ZMod 195318521017) := by
  rw [show (249580073233 : ℕ) + 1 + 1 = 249580073233 + 2 from rfl, Nat.fib_add_two,
    Nat.cast_add, fib_k0, fib_k0succ]
  decide

/- ### The closed form for Fibonacci-like sequences in `ZMod p`. -/

lemma closed_form (u : ℕ → ZMod 195318521017) (hrec : ∀ k, u (k + 2) = u (k + 1) + u k) :
    ∀ k, u k = u 0 * (fib (k + 1) : ℕ) + (u 1 - u 0) * (fib k : ℕ) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simp [fib_one]
  | more n ih1 ih2 =>
    rw [hrec n, ih1, ih2,
      show n + 2 + 1 = n + 1 + 2 from rfl, Nat.fib_add_two (n := n + 1),
      show n + 2 = n + 0 + 2 from rfl, Nat.fib_add_two (n := n)]
    push_cast
    ring

lemma A_step (n : ℕ) : A355898 (n + 3) =
    Nat.gcd (A355898 (n + 2)) (A355898 (n + 1))
    + (A355898 (n + 2) + A355898 (n + 1)) / Nat.gcd (A355898 (n + 2)) (A355898 (n + 1)) := by
  simp only [A355898]

lemma crux (g q : ℕ) (hg : 2 ≤ g) (hq : 2 ≤ q) (h : g + q = 1 + g * q) : False := by
  have h1 : 2 * q ≤ g * q := Nat.mul_le_mul_right q hg
  have h2 : g * 2 ≤ g * q := Nat.mul_le_mul_left g hq
  linarith

theorem main : ¬ ∀ (n : ℕ), 3775 ≤ n →
    ((A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
    ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) := by
  intro H
  have H1' : ∀ k : ℕ, A355898 (3775 + k) = 1 + A355898 (3774 + k) + A355898 (3773 + k) := by
    intro k
    have h := (H (3775 + k) (by omega)).1
    have e1 : 3775 + k - 1 = 3774 + k := by omega
    have e2 : 3775 + k - 2 = 3773 + k := by omega
    rwa [e1, e2] at h
  -- the shifted sequence `u k = A355898 (3773 + k) + 1` in `ZMod p` satisfies the
  -- Fibonacci recurrence, so it is given by the closed form.
  set u : ℕ → ZMod 195318521017 := fun k => (A355898 (3773 + k) : ZMod 195318521017) + 1 with hu
  have hrec : ∀ k, u (k + 2) = u (k + 1) + u k := by
    intro k
    have h := H1' k
    have e : 3773 + (k + 2) = 3775 + k := by omega
    have e2 : 3773 + (k + 1) = 3774 + k := by omega
    simp only [hu, e, e2, h]
    push_cast
    ring
  have hu0 : u 0 = ((77940394258 : ℕ) : ZMod 195318521017) + 1 := by
    simp only [hu]
    rw [show (3773 : ℕ) + 0 = 3773 from rfl, a3773_cast]
  have hu1 : u 1 = ((99768150821 : ℕ) : ZMod 195318521017) + 1 := by
    simp only [hu]
    rw [show (3773 : ℕ) + 1 = 3774 from rfl, a3774_cast]
  have hcf := closed_form u hrec
  have huk0 : u 249580073233 = 1 := by
    rw [hcf 249580073233, hu0, hu1, fib_k0, fib_k0succ]
    decide
  have huk0' : u (249580073233 + 1) = 1 := by
    rw [hcf (249580073233 + 1), hu0, hu1, fib_k0succ, fib_k0succ2]
    decide
  -- hence p divides both `A355898 (3773 + k0)` and `A355898 (3774 + k0)`
  have hdvd1 : (195318521017 : ℕ) ∣ A355898 (3773 + 249580073233) := by
    have h : (A355898 (3773 + 249580073233) : ZMod 195318521017) + 1 = 1 := huk0
    have h0 : (A355898 (3773 + 249580073233) : ZMod 195318521017) = 1 - 1 := eq_sub_of_add_eq h
    rw [sub_self] at h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  have hdvd2 : (195318521017 : ℕ) ∣ A355898 (3774 + 249580073233) := by
    have h : (A355898 (3773 + (249580073233 + 1)) : ZMod 195318521017) + 1 = 1 := huk0'
    rw [show 3773 + (249580073233 + 1) = 3774 + 249580073233 from rfl] at h
    have h0 : (A355898 (3774 + 249580073233) : ZMod 195318521017) = 1 - 1 := eq_sub_of_add_eq h
    rw [sub_self] at h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0
  -- positivity of the two terms
  have hx1 : 1 ≤ A355898 (3774 + 249580073233) := by
    have h := H1' (249580073233 - 1)
    rw [show 3775 + (249580073233 - 1) = 3774 + 249580073233 from rfl] at h
    omega
  have hy1 : 1 ≤ A355898 (3773 + 249580073233) := by
    have h := H1' (249580073233 - 2)
    rw [show 3775 + (249580073233 - 2) = 3773 + 249580073233 from rfl] at h
    omega
  -- unfold the definition of `A355898` at `3775 + k0`
  have hdef : A355898 (3775 + 249580073233) =
      Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
      + (A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233))
        / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := by
    rw [show (3775 : ℕ) + 249580073233 = 3772 + 249580073233 + 3 from rfl, A_step,
        show (3772 : ℕ) + 249580073233 + 2 = 3774 + 249580073233 from rfl,
        show (3772 : ℕ) + 249580073233 + 1 = 3773 + 249580073233 from rfl]
  have heq : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
      + (A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233))
        / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
      = 1 + A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233) := by
    rw [← hdef]
    exact H1' 249580073233
  -- now derive `False`
  have hgx : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) ∣ A355898 (3774 + 249580073233) :=
    Nat.gcd_dvd_left _ _
  have hgy : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) ∣ A355898 (3773 + 249580073233) :=
    Nat.gcd_dvd_right _ _
  have hpg : (195318521017 : ℕ) ∣ Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) :=
    Nat.dvd_gcd hdvd2 hdvd1
  have hgpos : 0 < Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := by
    rcases Nat.eq_zero_or_pos (Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))) with h0 | h1
    · have := Nat.eq_zero_of_gcd_eq_zero_left h0
      omega
    · exact h1
  have hg2 : 2 ≤ Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := by
    have := Nat.le_of_dvd hgpos hpg
    omega
  have hxg : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) ≤ A355898 (3774 + 249580073233) :=
    Nat.le_of_dvd (by omega) hgx
  have hyg : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) ≤ A355898 (3773 + 249580073233) :=
    Nat.le_of_dvd (by omega) hgy
  have hmul : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
      * ((A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233))
        / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)))
      = A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233) :=
    Nat.mul_div_cancel' (Nat.dvd_add hgx hgy)
  have hq2 : 2 ≤ (A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233))
      / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233)) := by
    rw [Nat.le_div_iff_mul_le hgpos]
    omega
  have hfinal : Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
      + (A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233))
        / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
      = 1 + Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))
        * ((A355898 (3774 + 249580073233) + A355898 (3773 + 249580073233))
          / Nat.gcd (A355898 (3774 + 249580073233)) (A355898 (3773 + 249580073233))) := by
    rw [hmul]
    omega
  exact crux _ _ hg2 hq2 hfinal


end OeisA355898

/--
Conjecture: For n >= 3775 a(n) can also be expressed in the following three ways:
1) a(n) = 1 + a(n-1) + a(n-2).
2) a(n) = 2*a(n-1) - a(n-3).
3) If A = a(3774), B = a(3772) and F = Fibonacci A000045(n),
   a(n) = (A+1)*F(n-3772) - (B+1)*F(n-3774) - 1.
These three formulas only work for n >= 3775.

This conjecture is **false**: it fails (far) beyond the range in which it was
numerically verified.  See `OeisA355898.main` above for the disproof.
-/
theorem oeis_a355898_conjecture.disproof : ¬ ∀ (n : ℕ), 3775 ≤ n →
    ((A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2))
    ∧ (A355898 n = 2 * A355898 (n - 1) - A355898 (n - 3))
    ∧ (A355898 n = (A355898 3774 + 1) * Nat.fib (n - 3772) - (A355898 3772 + 1) * Nat.fib (n - 3774) - 1)) :=
  OeisA355898.main
