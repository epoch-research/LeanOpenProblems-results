import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

/--
A157225: Number of ways to write the $n$-th positive odd integer in the form $p+2^x+7 \cdot 2^y$
with $p$ a prime congruent to $5 \bmod 6$ and $x,y$ positive integers.
$$a(n) = \left|\left\{(p,x,y) : p+2^x+7 \cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 5 \bmod 6 \text{ and } x,y \in \mathbb{Z}_{>0}\right\}\right|$$
-/
noncomputable def A157225 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N : ℕ := 2 * n - 1
    -- Since $2^x$ and $7 \cdot 2^y$ must be less than $N$, $x$ and $y$ are effectively bounded by $\sim \log_2 N$.
    -- We use Nat.log 2 N + 1 as a safe upper bound for the range of exponents.
    let max_exp : ℕ := Nat.log 2 N + 1

    Finset.card $ (Finset.range max_exp).product (Finset.range max_exp) |>.filter (fun xy =>
      let x := xy.fst
      let y := xy.snd

      -- 1. $x, y$ are positive integers.
      1 ≤ x ∧ 1 ≤ y ∧

      let term_sum := 2 ^ x + 7 * 2 ^ y

      -- 2. $p = N - \text{term\_sum}$ must be a natural number, so term_sum < N.
      term_sum < N ∧

      let p := N - term_sum

      -- 3. $p$ must be a prime congruent to 5 mod 6.
      p.Prime ∧ p % 6 = 5
    )

private theorem oeis_157225_conjecture_0_cert_a_0 :
    ∀ b : ℕ, b < 31 → 1 ≤ 0 → 1 ≤ b → 2 ^ 0 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 0 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 0 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_1 :
    ∀ b : ℕ, b < 31 → 1 ≤ 1 → 1 ≤ b → 2 ^ 1 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 1 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 1 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_2 :
    ∀ b : ℕ, b < 31 → 1 ≤ 2 → 1 ≤ b → 2 ^ 2 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 2 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 2 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_3 :
    ∀ b : ℕ, b < 31 → 1 ≤ 3 → 1 ≤ b → 2 ^ 3 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 3 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 3 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_4 :
    ∀ b : ℕ, b < 31 → 1 ≤ 4 → 1 ≤ b → 2 ^ 4 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 4 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 4 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_5 :
    ∀ b : ℕ, b < 31 → 1 ≤ 5 → 1 ≤ b → 2 ^ 5 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 5 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 5 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_6 :
    ∀ b : ℕ, b < 31 → 1 ≤ 6 → 1 ≤ b → 2 ^ 6 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 6 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 6 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_7 :
    ∀ b : ℕ, b < 31 → 1 ≤ 7 → 1 ≤ b → 2 ^ 7 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 7 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 7 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_8 :
    ∀ b : ℕ, b < 31 → 1 ≤ 8 → 1 ≤ b → 2 ^ 8 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 8 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 8 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_9 :
    ∀ b : ℕ, b < 31 → 1 ≤ 9 → 1 ≤ b → 2 ^ 9 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 9 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 9 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_10 :
    ∀ b : ℕ, b < 31 → 1 ≤ 10 → 1 ≤ b → 2 ^ 10 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 10 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 10 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_11 :
    ∀ b : ℕ, b < 31 → 1 ≤ 11 → 1 ≤ b → 2 ^ 11 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 11 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 11 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_12 :
    ∀ b : ℕ, b < 31 → 1 ≤ 12 → 1 ≤ b → 2 ^ 12 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 12 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 12 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_13 :
    ∀ b : ℕ, b < 31 → 1 ≤ 13 → 1 ≤ b → 2 ^ 13 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 13 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 13 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_14 :
    ∀ b : ℕ, b < 31 → 1 ≤ 14 → 1 ≤ b → 2 ^ 14 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 14 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 14 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_15 :
    ∀ b : ℕ, b < 31 → 1 ≤ 15 → 1 ≤ b → 2 ^ 15 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 15 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 15 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_16 :
    ∀ b : ℕ, b < 31 → 1 ≤ 16 → 1 ≤ b → 2 ^ 16 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 16 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 16 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_17 :
    ∀ b : ℕ, b < 31 → 1 ≤ 17 → 1 ≤ b → 2 ^ 17 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 17 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 17 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_18 :
    ∀ b : ℕ, b < 31 → 1 ≤ 18 → 1 ≤ b → 2 ^ 18 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 18 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 18 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_19 :
    ∀ b : ℕ, b < 31 → 1 ≤ 19 → 1 ≤ b → 2 ^ 19 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 19 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 19 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_20 :
    ∀ b : ℕ, b < 31 → 1 ≤ 20 → 1 ≤ b → 2 ^ 20 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 20 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 20 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_21 :
    ∀ b : ℕ, b < 31 → 1 ≤ 21 → 1 ≤ b → 2 ^ 21 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 21 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 21 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_22 :
    ∀ b : ℕ, b < 31 → 1 ≤ 22 → 1 ≤ b → 2 ^ 22 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 22 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 22 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_23 :
    ∀ b : ℕ, b < 31 → 1 ≤ 23 → 1 ≤ b → 2 ^ 23 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 23 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 23 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_24 :
    ∀ b : ℕ, b < 31 → 1 ≤ 24 → 1 ≤ b → 2 ^ 24 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 24 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 24 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_25 :
    ∀ b : ℕ, b < 31 → 1 ≤ 25 → 1 ≤ b → 2 ^ 25 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 25 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 25 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_26 :
    ∀ b : ℕ, b < 31 → 1 ≤ 26 → 1 ≤ b → 2 ^ 26 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 26 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 26 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_27 :
    ∀ b : ℕ, b < 31 → 1 ≤ 27 → 1 ≤ b → 2 ^ 27 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 27 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 27 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_28 :
    ∀ b : ℕ, b < 31 → 1 ≤ 28 → 1 ≤ b → 2 ^ 28 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 28 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 28 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_29 :
    ∀ b : ℕ, b < 31 → 1 ≤ 29 → 1 ≤ b → 2 ^ 29 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 29 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 29 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *

private theorem oeis_157225_conjecture_0_cert_a_30 :
    ∀ b : ℕ, b < 31 → 1 ≤ 30 → 1 ≤ b → 2 ^ 30 + 7 * 2 ^ b < 1433987797 →
      Nat.Prime (1433987797 - (2 ^ 30 + 7 * 2 ^ b)) →
      ¬ (1433987797 - (2 ^ 30 + 7 * 2 ^ b)) % 6 = 5 := by
  intro b hb hapos hbpos hlt hp hmod
  interval_cases b <;> norm_num at *


/--
Zhi-Wei Sun conjectured that $a(n)=0$ if and only if $n < 11$ or $n \in \{13, 16, 992\}$;
in other words, except for $25, 31, 1983$, any odd integer greater than $20$ can be written as the sum
of a prime congruent to $5 \bmod 6$, a positive power of $2$ and seven times a positive power of $2$.
-/
theorem oeis_157225_conjecture_0.disproof :
    ¬ (∀ (n : ℕ), A157225 n = 0 ↔ n < 11 ∨ n = 13 ∨ n = 16 ∨ n = 992) := by
  intro h
  have hA : A157225 716993899 = 0 := by
    unfold A157225
    rw [if_neg (by norm_num : 716993899 ≠ 0)]
    norm_num only [Nat.reduceMul, Nat.reduceSub]
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    rintro ⟨a,b⟩ hmem hpred
    have hm : a ∈ Finset.range 31 ∧ b ∈ Finset.range 31 := by
      simpa [Finset.mem_product] using hmem
    have ha : a < 31 := by simpa using hm.1
    have hb : b < 31 := by simpa using hm.2
    rcases hpred with ⟨hapos,hbpos,hlt,hp,hmod⟩
    interval_cases a
    · exact oeis_157225_conjecture_0_cert_a_1 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_2 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_3 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_4 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_5 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_6 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_7 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_8 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_9 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_10 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_11 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_12 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_13 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_14 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_15 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_16 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_17 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_18 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_19 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_20 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_21 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_22 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_23 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_24 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_25 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_26 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_27 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_28 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_29 b hb hapos hbpos hlt hp hmod
    · exact oeis_157225_conjecture_0_cert_a_30 b hb hapos hbpos hlt hp hmod

  have hR : ¬ (716993899 < 11 ∨ 716993899 = 13 ∨ 716993899 = 16 ∨ 716993899 = 992) := by
    omega
  exact hR ((h 716993899).mp hA)


