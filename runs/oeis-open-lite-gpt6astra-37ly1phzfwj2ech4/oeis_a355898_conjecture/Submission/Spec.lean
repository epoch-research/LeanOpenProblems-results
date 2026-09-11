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

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Counterexample

/-- Compute two consecutive terms without duplicating recursive work. -/
def seqPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k+1 => let p := seqPair k
           (p.2, p.1.gcd p.2 + (p.1 + p.2) / p.1.gcd p.2)

lemma seqPair_eq (k : ℕ) : seqPair k = (A355898 (k+1), A355898 (k+2)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [seqPair, ih, A355898]
    rw [Nat.gcd_comm]
    ac_rfl

open Matrix

/-- Repeated squaring, used only for the finite modular certificate below. -/
def fastPower {M : Type*} [Monoid M] (x : M) (n : ℕ) : M :=
  if n = 0 then 1 else
    let y := fastPower x (n / 2)
    if n % 2 = 0 then y * y else x * (y * y)
termination_by n

theorem fastPower_eq {M : Type*} [Monoid M] (x : M) (n : ℕ) :
    fastPower x n = x ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fastPower]
    split_ifs with h0 h2
    · simp [h0]
    · rw [ih (n / 2) (by omega), ← pow_add]
      congr 1
      omega
    · dsimp only
      rw [ih (n / 2) (by omega), ← pow_add, ← pow_succ' x (n / 2 + n / 2)]
      congr 1
      omega

abbrev p : ℕ := 195318521017
abbrev R := ZMod p

def T : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 1]
def initial : Fin 2 → R :=
  ![((seqPair 3772).1 + 1 : ℕ), ((seqPair 3772).2 + 1 : ℕ)]

/-- Starting with a(3773)+1 and a(3774)+1, the Fibonacci transition
reaches (1,1) modulo p after 249580073233 steps. -/
theorem modular_certificate : fastPower T 249580073233 *ᵥ initial = ![1, 1] := by
  decide +kernel


theorem matrix_recurrence
    (H : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n-1) + A355898 (n-2))
    (k : ℕ) :
    T ^ k *ᵥ initial =
      ![↑(A355898 (3773+k) + 1), ↑(A355898 (3774+k) + 1)] := by
  induction k with
  | zero => simp [initial, seqPair_eq]
  | succ k ih =>
    rw [_root_.pow_succ', ← mulVec_mulVec, ih]
    have hrec : A355898 (3775+k) = 1 + A355898 (3774+k) + A355898 (3773+k) := by
      have hh := H (3775+k) (by omega)
      simpa only [show 3775+k-1 = 3774+k by omega,
        show 3775+k-2 = 3773+k by omega] using hh
    rw [show 3773+(k+1) = 3774+k by omega,
      show 3774+(k+1) = 3775+k by omega, hrec]
    ext i
    fin_cases i <;> simp [T, mulVec, dotProduct, Fin.sum_univ_two, Nat.cast_add]
    ring


/-- For positive inputs, agreement of the two recurrences forces coprimality. -/
theorem gcd_eq_one_of_formula (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : x.gcd y + (x+y) / x.gcd y = 1+x+y) : x.gcd y = 1 := by
  have hg := Nat.gcd_pos_of_pos_left y hx
  have hgx := Nat.gcd_le_left y hx
  have hgy := Nat.gcd_le_right x hy
  have hd := Nat.div_mul_cancel (Nat.dvd_add (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y))
  by_contra hn
  have h1 : x.gcd y - 1 + 1 = x.gcd y := by omega
  have h2 : x+y-x.gcd y + x.gcd y = x+y := by omega
  have hp : 0 < (x.gcd y - 1) * (x+y-x.gcd y) := Nat.mul_pos (by omega) (by omega)
  nlinarith

theorem impossible
    (H : ∀ n, 3775 ≤ n → A355898 n = 1 + A355898 (n-1) + A355898 (n-2)) : False := by
  have hm := modular_certificate
  rw [fastPower_eq, matrix_recurrence H] at hm
  have hx : (A355898 249580077006 : R) = 0 := by
    have h0 := congrFun hm 0
    simp only [Nat.cast_add, Nat.cast_one, Matrix.cons_val_zero] at h0
    exact add_right_cancel (h0.trans (zero_add 1).symm)
  have hy : (A355898 249580077007 : R) = 0 := by
    have h1 := congrFun hm 1
    simp only [Nat.cast_add, Nat.cast_one, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    exact add_right_cancel (h1.trans (zero_add 1).symm)
  have hdx : p ∣ A355898 249580077006 := (ZMod.natCast_eq_zero_iff _ _).mp hx
  have hdy : p ∣ A355898 249580077007 := (ZMod.natCast_eq_zero_iff _ _).mp hy
  have hpx : 0 < A355898 249580077006 := by
    have hh := H 249580077006 (by decide)
    omega
  have hpy : 0 < A355898 249580077007 := by
    have hh := H 249580077007 (by decide)
    omega
  have hlast := H 249580077008 (by decide)
  have hactual := A355898.eq_4 249580077005
  norm_num only [Nat.reduceAdd, Nat.succ_eq_add_one] at hactual
  norm_num only [Nat.reduceSub] at hlast
  have hg : (A355898 249580077007).gcd (A355898 249580077006) = 1 :=
    gcd_eq_one_of_formula _ _ hpy hpx (hactual.symm.trans hlast)
  have hdiv := Nat.dvd_gcd hdy hdx
  rw [hg] at hdiv
  norm_num [p] at hdiv

end Counterexample

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
  exact Counterexample.impossible (fun n hn => (H n hn).1)
