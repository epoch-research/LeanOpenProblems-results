import FormalConjectures.Util.ProblemImports
import Submission.Cases

open Nat BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  -- Helper for the binomial coefficient term: B(k) = binomial(2*k+1, k)
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k

  -- The maximum value for $a, b$ is $\lfloor \sqrt{n} \rfloor$.
  -- We use a safe upper bound for iteration. `n.sqrt + 1` is slightly more than needed, but safe.
  let R_sq := Finset.range (n.sqrt + 1)
  -- The maximum value for $c, d$ is when B(c) is not too large. Since B(0)=1, B(1)=3, B(2)=10,
  -- a rough upper bound for k is needed, n+1 is certainly safe but inefficient.
  -- A tighter bound is not strictly necessary for definition.
  -- Since $\binom{2k+1}{k} \approx 4^k / \sqrt{\pi k}$, we only need to iterate c and d up to around log_4(n).
  -- For formalization, we keep the provided `n+1` range or a slightly better one.
  let R_binom := Finset.range (n + 1)

  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

lemma no_sol_c0 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 0 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · exact no_sol_0_0 a' b' h
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · exact no_sol_0_1 a' b' h
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · exact no_sol_0_2 a' b' h
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · exact no_sol_0_3 a' b' h
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · exact no_sol_0_4 a' b' h
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · exact no_sol_0_5 a' b' h
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_0_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_0_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_0_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_0_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_0_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_0_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_0_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_0_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_0_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_0_15 a' b' h
  omega

lemma no_sol_c1 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 1 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 1 = 800322180 := by omega
    exact no_sol_0_1 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · exact no_sol_1_1 a' b' h
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · exact no_sol_1_2 a' b' h
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · exact no_sol_1_3 a' b' h
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · exact no_sol_1_4 a' b' h
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · exact no_sol_1_5 a' b' h
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_1_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_1_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_1_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_1_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_1_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_1_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_1_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_1_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_1_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_1_15 a' b' h
  omega

lemma no_sol_c2 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 2 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 2 = 800322180 := by omega
    exact no_sol_0_2 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 2 = 800322180 := by omega
    exact no_sol_1_2 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · exact no_sol_2_2 a' b' h
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · exact no_sol_2_3 a' b' h
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · exact no_sol_2_4 a' b' h
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · exact no_sol_2_5 a' b' h
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_2_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_2_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_2_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_2_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_2_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_2_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_2_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_2_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_2_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_2_15 a' b' h
  omega

lemma no_sol_c3 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 3 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 3 = 800322180 := by omega
    exact no_sol_0_3 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 3 = 800322180 := by omega
    exact no_sol_1_3 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 3 = 800322180 := by omega
    exact no_sol_2_3 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · exact no_sol_3_3 a' b' h
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · exact no_sol_3_4 a' b' h
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · exact no_sol_3_5 a' b' h
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_3_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_3_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_3_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_3_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_3_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_3_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_3_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_3_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_3_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_3_15 a' b' h
  omega

lemma no_sol_c4 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 4 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 4 = 800322180 := by omega
    exact no_sol_0_4 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 4 = 800322180 := by omega
    exact no_sol_1_4 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 4 = 800322180 := by omega
    exact no_sol_2_4 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 4 = 800322180 := by omega
    exact no_sol_3_4 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · exact no_sol_4_4 a' b' h
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · exact no_sol_4_5 a' b' h
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_4_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_4_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_4_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_4_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_4_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_4_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_4_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_4_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_4_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_4_15 a' b' h
  omega

lemma no_sol_c5 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 5 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 5 = 800322180 := by omega
    exact no_sol_0_5 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 5 = 800322180 := by omega
    exact no_sol_1_5 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 5 = 800322180 := by omega
    exact no_sol_2_5 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 5 = 800322180 := by omega
    exact no_sol_3_5 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 5 = 800322180 := by omega
    exact no_sol_4_5 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · exact no_sol_5_5 a' b' h
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_5_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_5_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_5_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_5_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_5_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_5_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_5_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_5_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_5_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_5_15 a' b' h
  omega

lemma no_sol_c6 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 6 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 6 = 800322180 := by omega
    exact no_sol_0_6 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 6 = 800322180 := by omega
    exact no_sol_1_6 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 6 = 800322180 := by omega
    exact no_sol_2_6 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 6 = 800322180 := by omega
    exact no_sol_3_6 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 6 = 800322180 := by omega
    exact no_sol_4_6 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 6 = 800322180 := by omega
    exact no_sol_5_6 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · exact no_sol_6_6 a' b' h
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_6_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_6_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_6_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_6_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_6_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_6_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_6_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_6_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_6_15 a' b' h
  omega

lemma no_sol_c7 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 7 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 7 = 800322180 := by omega
    exact no_sol_0_7 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 7 = 800322180 := by omega
    exact no_sol_1_7 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 7 = 800322180 := by omega
    exact no_sol_2_7 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 7 = 800322180 := by omega
    exact no_sol_3_7 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 7 = 800322180 := by omega
    exact no_sol_4_7 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 7 = 800322180 := by omega
    exact no_sol_5_7 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 7 = 800322180 := by omega
    exact no_sol_6_7 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · exact no_sol_7_7 a' b' h
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_7_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_7_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_7_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_7_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_7_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_7_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_7_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_7_15 a' b' h
  omega

lemma no_sol_c8 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 8 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 8 = 800322180 := by omega
    exact no_sol_0_8 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 8 = 800322180 := by omega
    exact no_sol_1_8 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 8 = 800322180 := by omega
    exact no_sol_2_8 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 8 = 800322180 := by omega
    exact no_sol_3_8 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 8 = 800322180 := by omega
    exact no_sol_4_8 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 8 = 800322180 := by omega
    exact no_sol_5_8 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 8 = 800322180 := by omega
    exact no_sol_6_8 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 8 = 800322180 := by omega
    exact no_sol_7_8 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · exact no_sol_8_8 a' b' h
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_8_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_8_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_8_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_8_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_8_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_8_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_8_15 a' b' h
  omega

lemma no_sol_c9 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 9 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 9 = 800322180 := by omega
    exact no_sol_0_9 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 9 = 800322180 := by omega
    exact no_sol_1_9 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 9 = 800322180 := by omega
    exact no_sol_2_9 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 9 = 800322180 := by omega
    exact no_sol_3_9 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 9 = 800322180 := by omega
    exact no_sol_4_9 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 9 = 800322180 := by omega
    exact no_sol_5_9 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 9 = 800322180 := by omega
    exact no_sol_6_9 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 9 = 800322180 := by omega
    exact no_sol_7_9 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 9 = 800322180 := by omega
    exact no_sol_8_9 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · exact no_sol_9_9 a' b' h
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_9_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_9_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_9_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_9_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_9_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_9_15 a' b' h
  omega

lemma no_sol_c10 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 10 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 10 = 800322180 := by omega
    exact no_sol_0_10 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 10 = 800322180 := by omega
    exact no_sol_1_10 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 10 = 800322180 := by omega
    exact no_sol_2_10 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 10 = 800322180 := by omega
    exact no_sol_3_10 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 10 = 800322180 := by omega
    exact no_sol_4_10 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 10 = 800322180 := by omega
    exact no_sol_5_10 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 10 = 800322180 := by omega
    exact no_sol_6_10 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 10 = 800322180 := by omega
    exact no_sol_7_10 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 10 = 800322180 := by omega
    exact no_sol_8_10 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 9 + B 10 = 800322180 := by omega
    exact no_sol_9_10 a' b' h2
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · exact no_sol_10_10 a' b' h
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_10_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_10_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_10_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_10_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_10_15 a' b' h
  omega

lemma no_sol_c11 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 11 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 11 = 800322180 := by omega
    exact no_sol_0_11 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 11 = 800322180 := by omega
    exact no_sol_1_11 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 11 = 800322180 := by omega
    exact no_sol_2_11 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 11 = 800322180 := by omega
    exact no_sol_3_11 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 11 = 800322180 := by omega
    exact no_sol_4_11 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 11 = 800322180 := by omega
    exact no_sol_5_11 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 11 = 800322180 := by omega
    exact no_sol_6_11 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 11 = 800322180 := by omega
    exact no_sol_7_11 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 11 = 800322180 := by omega
    exact no_sol_8_11 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 9 + B 11 = 800322180 := by omega
    exact no_sol_9_11 a' b' h2
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 10 + B 11 = 800322180 := by omega
    exact no_sol_10_11 a' b' h2
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · exact no_sol_11_11 a' b' h
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_11_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_11_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_11_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_11_15 a' b' h
  omega

lemma no_sol_c12 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 12 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 12 = 800322180 := by omega
    exact no_sol_0_12 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 12 = 800322180 := by omega
    exact no_sol_1_12 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 12 = 800322180 := by omega
    exact no_sol_2_12 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 12 = 800322180 := by omega
    exact no_sol_3_12 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 12 = 800322180 := by omega
    exact no_sol_4_12 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 12 = 800322180 := by omega
    exact no_sol_5_12 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 12 = 800322180 := by omega
    exact no_sol_6_12 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 12 = 800322180 := by omega
    exact no_sol_7_12 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 12 = 800322180 := by omega
    exact no_sol_8_12 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 9 + B 12 = 800322180 := by omega
    exact no_sol_9_12 a' b' h2
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 10 + B 12 = 800322180 := by omega
    exact no_sol_10_12 a' b' h2
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 11 + B 12 = 800322180 := by omega
    exact no_sol_11_12 a' b' h2
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · exact no_sol_12_12 a' b' h
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_12_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_12_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_12_15 a' b' h
  omega

lemma no_sol_c13 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 13 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 13 = 800322180 := by omega
    exact no_sol_0_13 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 13 = 800322180 := by omega
    exact no_sol_1_13 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 13 = 800322180 := by omega
    exact no_sol_2_13 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 13 = 800322180 := by omega
    exact no_sol_3_13 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 13 = 800322180 := by omega
    exact no_sol_4_13 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 13 = 800322180 := by omega
    exact no_sol_5_13 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 13 = 800322180 := by omega
    exact no_sol_6_13 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 13 = 800322180 := by omega
    exact no_sol_7_13 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 13 = 800322180 := by omega
    exact no_sol_8_13 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 9 + B 13 = 800322180 := by omega
    exact no_sol_9_13 a' b' h2
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 10 + B 13 = 800322180 := by omega
    exact no_sol_10_13 a' b' h2
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 11 + B 13 = 800322180 := by omega
    exact no_sol_11_13 a' b' h2
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 12 + B 13 = 800322180 := by omega
    exact no_sol_12_13 a' b' h2
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · exact no_sol_13_13 a' b' h
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_13_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_13_15 a' b' h
  omega

lemma no_sol_c14 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 14 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 14 = 800322180 := by omega
    exact no_sol_0_14 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 14 = 800322180 := by omega
    exact no_sol_1_14 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 14 = 800322180 := by omega
    exact no_sol_2_14 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 14 = 800322180 := by omega
    exact no_sol_3_14 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 14 = 800322180 := by omega
    exact no_sol_4_14 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 14 = 800322180 := by omega
    exact no_sol_5_14 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 14 = 800322180 := by omega
    exact no_sol_6_14 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 14 = 800322180 := by omega
    exact no_sol_7_14 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 14 = 800322180 := by omega
    exact no_sol_8_14 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 9 + B 14 = 800322180 := by omega
    exact no_sol_9_14 a' b' h2
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 10 + B 14 = 800322180 := by omega
    exact no_sol_10_14 a' b' h2
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 11 + B 14 = 800322180 := by omega
    exact no_sol_11_14 a' b' h2
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 12 + B 14 = 800322180 := by omega
    exact no_sol_12_14 a' b' h2
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 13 + B 14 = 800322180 := by omega
    exact no_sol_13_14 a' b' h2
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · exact no_sol_14_14 a' b' h
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_14_15 a' b' h
  omega

lemma no_sol_c15 (a' b' d : ℕ) (hd_le : d < 16) : a' ^ 2 + b' ^ 2 + B 15 + B d ≠ 800322180 := by
  intro h
  have hd0 : d = 0 ∨ d ≠ 0 := Decidable.em _
  rcases hd0 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 0 + B 15 = 800322180 := by omega
    exact no_sol_0_15 a' b' h2
  have hd1 : d = 1 ∨ d ≠ 1 := Decidable.em _
  rcases hd1 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 1 + B 15 = 800322180 := by omega
    exact no_sol_1_15 a' b' h2
  have hd2 : d = 2 ∨ d ≠ 2 := Decidable.em _
  rcases hd2 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 2 + B 15 = 800322180 := by omega
    exact no_sol_2_15 a' b' h2
  have hd3 : d = 3 ∨ d ≠ 3 := Decidable.em _
  rcases hd3 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 3 + B 15 = 800322180 := by omega
    exact no_sol_3_15 a' b' h2
  have hd4 : d = 4 ∨ d ≠ 4 := Decidable.em _
  rcases hd4 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 4 + B 15 = 800322180 := by omega
    exact no_sol_4_15 a' b' h2
  have hd5 : d = 5 ∨ d ≠ 5 := Decidable.em _
  rcases hd5 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 5 + B 15 = 800322180 := by omega
    exact no_sol_5_15 a' b' h2
  have hd6 : d = 6 ∨ d ≠ 6 := Decidable.em _
  rcases hd6 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 6 + B 15 = 800322180 := by omega
    exact no_sol_6_15 a' b' h2
  have hd7 : d = 7 ∨ d ≠ 7 := Decidable.em _
  rcases hd7 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 7 + B 15 = 800322180 := by omega
    exact no_sol_7_15 a' b' h2
  have hd8 : d = 8 ∨ d ≠ 8 := Decidable.em _
  rcases hd8 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 8 + B 15 = 800322180 := by omega
    exact no_sol_8_15 a' b' h2
  have hd9 : d = 9 ∨ d ≠ 9 := Decidable.em _
  rcases hd9 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 9 + B 15 = 800322180 := by omega
    exact no_sol_9_15 a' b' h2
  have hd10 : d = 10 ∨ d ≠ 10 := Decidable.em _
  rcases hd10 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 10 + B 15 = 800322180 := by omega
    exact no_sol_10_15 a' b' h2
  have hd11 : d = 11 ∨ d ≠ 11 := Decidable.em _
  rcases hd11 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 11 + B 15 = 800322180 := by omega
    exact no_sol_11_15 a' b' h2
  have hd12 : d = 12 ∨ d ≠ 12 := Decidable.em _
  rcases hd12 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 12 + B 15 = 800322180 := by omega
    exact no_sol_12_15 a' b' h2
  have hd13 : d = 13 ∨ d ≠ 13 := Decidable.em _
  rcases hd13 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 13 + B 15 = 800322180 := by omega
    exact no_sol_13_15 a' b' h2
  have hd14 : d = 14 ∨ d ≠ 14 := Decidable.em _
  rcases hd14 with rfl | _
  · have h2 : a' ^ 2 + b' ^ 2 + B 14 + B 15 = 800322180 := by omega
    exact no_sol_14_15 a' b' h2
  have hd15 : d = 15 ∨ d ≠ 15 := Decidable.em _
  rcases hd15 with rfl | _
  · exact no_sol_15_15 a' b' h
  omega

lemma no_sol (a' b' c d : ℕ) : a' ^ 2 + b' ^ 2 + B c + B d ≠ 800322180 := by
  intro h
  have hc_le : c < 16 := by
    by_contra hc
    push_neg at hc
    have hB := B_ge_16 c hc
    omega
  have hd_le : d < 16 := by
    by_contra hd
    push_neg at hd
    have hB := B_ge_16 d hd
    omega
  have hc0 : c = 0 ∨ c ≠ 0 := Decidable.em _
  rcases hc0 with rfl | _
  · exact no_sol_c0 a' b' d hd_le h
  have hc1 : c = 1 ∨ c ≠ 1 := Decidable.em _
  rcases hc1 with rfl | _
  · exact no_sol_c1 a' b' d hd_le h
  have hc2 : c = 2 ∨ c ≠ 2 := Decidable.em _
  rcases hc2 with rfl | _
  · exact no_sol_c2 a' b' d hd_le h
  have hc3 : c = 3 ∨ c ≠ 3 := Decidable.em _
  rcases hc3 with rfl | _
  · exact no_sol_c3 a' b' d hd_le h
  have hc4 : c = 4 ∨ c ≠ 4 := Decidable.em _
  rcases hc4 with rfl | _
  · exact no_sol_c4 a' b' d hd_le h
  have hc5 : c = 5 ∨ c ≠ 5 := Decidable.em _
  rcases hc5 with rfl | _
  · exact no_sol_c5 a' b' d hd_le h
  have hc6 : c = 6 ∨ c ≠ 6 := Decidable.em _
  rcases hc6 with rfl | _
  · exact no_sol_c6 a' b' d hd_le h
  have hc7 : c = 7 ∨ c ≠ 7 := Decidable.em _
  rcases hc7 with rfl | _
  · exact no_sol_c7 a' b' d hd_le h
  have hc8 : c = 8 ∨ c ≠ 8 := Decidable.em _
  rcases hc8 with rfl | _
  · exact no_sol_c8 a' b' d hd_le h
  have hc9 : c = 9 ∨ c ≠ 9 := Decidable.em _
  rcases hc9 with rfl | _
  · exact no_sol_c9 a' b' d hd_le h
  have hc10 : c = 10 ∨ c ≠ 10 := Decidable.em _
  rcases hc10 with rfl | _
  · exact no_sol_c10 a' b' d hd_le h
  have hc11 : c = 11 ∨ c ≠ 11 := Decidable.em _
  rcases hc11 with rfl | _
  · exact no_sol_c11 a' b' d hd_le h
  have hc12 : c = 12 ∨ c ≠ 12 := Decidable.em _
  rcases hc12 with rfl | _
  · exact no_sol_c12 a' b' d hd_le h
  have hc13 : c = 13 ∨ c ≠ 13 := Decidable.em _
  rcases hc13 with rfl | _
  · exact no_sol_c13 a' b' d hd_le h
  have hc14 : c = 14 ∨ c ≠ 14 := Decidable.em _
  rcases hc14 with rfl | _
  · exact no_sol_c14 a' b' d hd_le h
  have hc15 : c = 15 ∨ c ≠ 15 := Decidable.em _
  rcases hc15 with rfl | _
  · exact no_sol_c15 a' b' d hd_le h
  omega

/--
Conjecture: a(n) > 0 for all n > 1.
-/
theorem oeis_303639_conjecture_0 : ∀ (n : ℕ), n > 1 → a n > 0 := by
  sorry

theorem oeis_303639_conjecture_0.disproof : ¬ (type_of% @oeis_303639_conjecture_0) := by
  intro h
  have h8 := h 800322180 (by decide)
  have h_a : a 800322180 = 0 := by
    unfold a
    apply Finset.sum_eq_zero; intro a' _
    apply Finset.sum_eq_zero; intro b' _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    have h_no := no_sol a' b' c d
    split_ifs with h_if
    · rcases h_if with ⟨_, _, h_eq⟩
      exact h_no h_eq
    · rfl
  rw [h_a] at h8
  omega
