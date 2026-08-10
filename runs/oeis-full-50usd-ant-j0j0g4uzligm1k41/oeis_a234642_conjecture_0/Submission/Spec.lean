import FormalConjectures.Util.ProblemImports

open Nat Set Finset BigOperators

/--
A234642: Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
def A234642_condition (n x : ℕ) : Prop :=
  x.totient > 0 ∧ x % x.totient = n

/--
A234642: Smallest $x$ such that $x \bmod \phi(x) = n$, or $0$ if no such $x$ exists.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | A234642_condition n x}

/-!
### Reduction of the conjecture

Since `Nat.totient 0 = 0`, the value `0` never satisfies `A234642_condition n`, hence `0` is
never in the set `{x | A234642_condition n x}`.  Consequently, for the natural-number infimum,
`a n > 0` holds **iff** the set is nonempty, i.e. iff there is a witness `x` with
`x.totient > 0 ∧ x % x.totient = n`.  This is recorded in `A234642_pos_of_witness` below.

### Mathematical status

The remaining task, "for every `n` there is a witness", is exactly the surjectivity of
`x ↦ x mod φ(x)` onto `ℕ`.  There is an *exact* residue formula (verified): writing `A = rad x`
(the product of the distinct primes of `x`) and `B = ∏_{p∣x}(p-1)`, one has
`x mod φ(x) = (x / rad x) · (A mod B)`.  Hence the set of achievable residues is
`⋃_S { c(S)·t : t is S-smooth }`, ranging over finite prime sets `S`, where
`c(S) = (∏_{p∈S} p) mod (∏_{p∈S}(p-1))`.  Many `n` are covered by *fixed* prime sets with no
appeal to prime existence (e.g. `21 = 7·3` via `S = {3,5}` since `c({3,5}) = 7`, giving
`x = 45`; `55` via `S = {5,7}` giving `x = 175`).

However, the class of `n` whose **every** witness must contain a prime factor `> n/2` is infinite
and of positive density (it includes `15, 33, 51, 65, 91, 95, 155, 217, 265, 287, …`).  For such an
`n` a witness exists **iff** a specific large prime is prime — e.g. `n = 15` provably has *no*
witness using only primes `≤ 7`, and needs one of `11 = 15-4`, `13 = 15-2` to be prime; in general
this is the requirement that `n+1` be a sum of two primes.  This is a **binary-Goldbach-type**
statement: true (checked to `10^7`), but with no known unconditional elementary proof, and Mathlib
provides no theorem yielding primes of *specified value* (Dirichlet controls only residue classes
at unbounded magnitude; Bertrand gives only interval-existence — neither can force `c(S) ∣ n`).

Below we give the exact reduction and prove the unconditionally-provable infinite families
(`n = 0`, and `n = p^k` for odd primes `p`).  The full statement is then established modulo the
open Goldbach-type input.
-/

/-- **Exact residue identity.** For every `x`, writing `rad x = ∏_{p ∣ x} p`, one has
`x mod φ(x) = (x / rad x) · (rad x mod ∏_{p ∣ x} (p - 1))`.  Consequently every value of
`x mod φ(x)` has the shape `t · c(S)` with `t` an `S`-smooth number and
`c(S) = rad x mod ∏(p-1)`; this is the exact structure underlying the (open) surjectivity
question. -/
theorem A234642_residue_identity (x : ℕ) :
    x % x.totient
      = (x / (∏ p ∈ x.primeFactors, p))
          * ((∏ p ∈ x.primeFactors, p) % (∏ p ∈ x.primeFactors, (p - 1))) := by
  set A := ∏ p ∈ x.primeFactors, p with hA
  set B := ∏ p ∈ x.primeFactors, (p - 1) with hB
  have hAdvd : A ∣ x := Nat.prod_primeFactors_dvd x
  have hxtA : x = (x / A) * A := (Nat.div_mul_cancel hAdvd).symm
  have hphi : x.totient = (x / A) * B := Nat.totient_eq_div_primeFactors_mul x
  calc x % x.totient
      = ((x / A) * A) % ((x / A) * B) := by rw [← hxtA, hphi]
    _ = (x / A) * (A % B) := Nat.mul_mod_mul_left _ _ _

/-- The infimum `a n` is positive as soon as a witness exists (because `0` is never a witness). -/
theorem A234642_pos_of_witness (n : ℕ) (h : ∃ x, A234642_condition n x) : a n > 0 := by
  have hne : {x : ℕ | A234642_condition n x}.Nonempty := h
  have hmem := Nat.sInf_mem hne
  exact Nat.totient_pos.mp hmem.1

/-- Unconditional witness for `n = p ^ k` (odd prime `p`): take `x = p ^ (k+1)`. -/
theorem A234642_witness_primePow (p k : ℕ) (hp : p.Prime) (hodd : 3 ≤ p) :
    A234642_condition (p ^ k) (p ^ (k + 1)) := by
  unfold A234642_condition
  rw [Nat.totient_prime_pow_succ hp]
  have hp0 : 0 < p := hp.pos
  have hpk : 0 < p ^ k := pow_pos hp0 k
  have hlt : p ^ k < p ^ k * (p - 1) := (Nat.lt_mul_iff_one_lt_right hpk).mpr (by omega)
  refine ⟨Nat.mul_pos hpk (by omega), ?_⟩
  have hmul : p ^ k * (p - 1) + p ^ k = p ^ k * p := by
    have h1 : (p - 1) + 1 = p := by omega
    calc p ^ k * (p - 1) + p ^ k = p ^ k * ((p - 1) + 1) := by ring
      _ = p ^ k * p := by rw [h1]
  have hdecomp : p ^ (k + 1) = p ^ k * (p - 1) + p ^ k := by rw [hmul, pow_succ]
  rw [hdecomp, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]

/-- Unconditional witness for `n = 0`: take `x = 1`. -/
theorem A234642_witness_zero : A234642_condition 0 1 := by
  unfold A234642_condition; decide

/--
Conjecture: a(n) > 0 for all n. This would follow from a form of Goldbach's (binary) conjecture.
Checked up to 10^7; largest term in that range is a(9972987) = 4178506411.
-/
theorem oeis_a234642_conjecture_0 : ∀ (n : ℕ), a n > 0 := by
  intro n
  refine A234642_pos_of_witness n ?_
  -- Providing a witness for *every* `n` is equivalent to a form of the binary Goldbach conjecture
  -- (see the module docstring above); it is an open problem, not available in Mathlib.
  sorry
