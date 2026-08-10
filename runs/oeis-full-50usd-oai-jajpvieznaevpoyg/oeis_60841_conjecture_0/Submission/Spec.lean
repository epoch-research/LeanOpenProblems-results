import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 10000000
set_option exponentiation.threshold 4096
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Nat Finset Rat
open scoped BigOperators

/--
A060841: Numerator of $1/\det(M)$ where $M$ is the $n \times n$ matrix with $M[i,j] = 1/\operatorname{lcm}(i,j)$.
The value is $\frac{1}{\det(M)} = \prod_{k=1}^n \frac{k^2}{\phi(k)}$
-/
noncomputable def A060841 (n : ℕ) : ℕ :=
  let val_rat : ℚ := (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))
  val_rat.num.natAbs

/-- The rational value $1/\det(M_n) = \prod_{k=1}^n \frac{k^2}{\phi(k)}$. -/
noncomputable def A060841_val_rat (n : ℕ) : ℚ :=
  (Icc 1 n).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))

@[simp] lemma totient_cert_1 : Nat.totient 1 = 1 := by
  norm_num [Nat.totient]
@[simp] lemma totient_cert_2 : Nat.totient 2 = 1 := by
  rw [show 2 = 2^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_3 : Nat.totient 3 = 2 := by
  rw [show 3 = 3^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_4 : Nat.totient 4 = 2 := by
  rw [show 4 = 2^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_5 : Nat.totient 5 = 4 := by
  rw [show 5 = 5^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_6 : Nat.totient 6 = 2 := by
  rw [show 6 = 2 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 3)]
  rw [totient_cert_2, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_7 : Nat.totient 7 = 6 := by
  rw [show 7 = 7^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_8 : Nat.totient 8 = 4 := by
  rw [show 8 = 2^3 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 3)] <;> norm_num
@[simp] lemma totient_cert_9 : Nat.totient 9 = 6 := by
  rw [show 9 = 3^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_10 : Nat.totient 10 = 4 := by
  rw [show 10 = 2 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 5)]
  rw [totient_cert_2, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_11 : Nat.totient 11 = 10 := by
  rw [show 11 = 11^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 11) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_12 : Nat.totient 12 = 4 := by
  rw [show 12 = 4 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 3)]
  rw [totient_cert_4, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_13 : Nat.totient 13 = 12 := by
  rw [show 13 = 13^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 13) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_14 : Nat.totient 14 = 6 := by
  rw [show 14 = 2 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 7)]
  rw [totient_cert_2, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_15 : Nat.totient 15 = 8 := by
  rw [show 15 = 3 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 5)]
  rw [totient_cert_3, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_16 : Nat.totient 16 = 8 := by
  rw [show 16 = 2^4 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 4)] <;> norm_num
@[simp] lemma totient_cert_17 : Nat.totient 17 = 16 := by
  rw [show 17 = 17^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 17) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_18 : Nat.totient 18 = 6 := by
  rw [show 18 = 2 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 9)]
  rw [totient_cert_2, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_19 : Nat.totient 19 = 18 := by
  rw [show 19 = 19^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 19) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_20 : Nat.totient 20 = 8 := by
  rw [show 20 = 4 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 5)]
  rw [totient_cert_4, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_21 : Nat.totient 21 = 12 := by
  rw [show 21 = 3 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 7)]
  rw [totient_cert_3, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_22 : Nat.totient 22 = 10 := by
  rw [show 22 = 2 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 11)]
  rw [totient_cert_2, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_23 : Nat.totient 23 = 22 := by
  rw [show 23 = 23^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 23) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_24 : Nat.totient 24 = 8 := by
  rw [show 24 = 8 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 3)]
  rw [totient_cert_8, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_25 : Nat.totient 25 = 20 := by
  rw [show 25 = 5^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_26 : Nat.totient 26 = 12 := by
  rw [show 26 = 2 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 13)]
  rw [totient_cert_2, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_27 : Nat.totient 27 = 18 := by
  rw [show 27 = 3^3 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 3)] <;> norm_num
@[simp] lemma totient_cert_28 : Nat.totient 28 = 12 := by
  rw [show 28 = 4 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 7)]
  rw [totient_cert_4, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_29 : Nat.totient 29 = 28 := by
  rw [show 29 = 29^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 29) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_30 : Nat.totient 30 = 8 := by
  rw [show 30 = 2 * 15 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 15)]
  rw [totient_cert_2, totient_cert_15] <;> norm_num
@[simp] lemma totient_cert_31 : Nat.totient 31 = 30 := by
  rw [show 31 = 31^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 31) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_32 : Nat.totient 32 = 16 := by
  rw [show 32 = 2^5 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 5)] <;> norm_num
@[simp] lemma totient_cert_33 : Nat.totient 33 = 20 := by
  rw [show 33 = 3 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 11)]
  rw [totient_cert_3, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_34 : Nat.totient 34 = 16 := by
  rw [show 34 = 2 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 17)]
  rw [totient_cert_2, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_35 : Nat.totient 35 = 24 := by
  rw [show 35 = 5 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 7)]
  rw [totient_cert_5, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_36 : Nat.totient 36 = 12 := by
  rw [show 36 = 4 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 9)]
  rw [totient_cert_4, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_37 : Nat.totient 37 = 36 := by
  rw [show 37 = 37^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 37) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_38 : Nat.totient 38 = 18 := by
  rw [show 38 = 2 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 19)]
  rw [totient_cert_2, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_39 : Nat.totient 39 = 24 := by
  rw [show 39 = 3 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 13)]
  rw [totient_cert_3, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_40 : Nat.totient 40 = 16 := by
  rw [show 40 = 8 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 5)]
  rw [totient_cert_8, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_41 : Nat.totient 41 = 40 := by
  rw [show 41 = 41^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 41) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_42 : Nat.totient 42 = 12 := by
  rw [show 42 = 2 * 21 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 21)]
  rw [totient_cert_2, totient_cert_21] <;> norm_num
@[simp] lemma totient_cert_43 : Nat.totient 43 = 42 := by
  rw [show 43 = 43^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 43) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_44 : Nat.totient 44 = 20 := by
  rw [show 44 = 4 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 11)]
  rw [totient_cert_4, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_45 : Nat.totient 45 = 24 := by
  rw [show 45 = 9 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 5)]
  rw [totient_cert_9, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_46 : Nat.totient 46 = 22 := by
  rw [show 46 = 2 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 23)]
  rw [totient_cert_2, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_47 : Nat.totient 47 = 46 := by
  rw [show 47 = 47^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 47) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_48 : Nat.totient 48 = 16 := by
  rw [show 48 = 16 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 3)]
  rw [totient_cert_16, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_49 : Nat.totient 49 = 42 := by
  rw [show 49 = 7^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_50 : Nat.totient 50 = 20 := by
  rw [show 50 = 2 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 25)]
  rw [totient_cert_2, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_51 : Nat.totient 51 = 32 := by
  rw [show 51 = 3 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 17)]
  rw [totient_cert_3, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_52 : Nat.totient 52 = 24 := by
  rw [show 52 = 4 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 13)]
  rw [totient_cert_4, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_53 : Nat.totient 53 = 52 := by
  rw [show 53 = 53^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 53) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_54 : Nat.totient 54 = 18 := by
  rw [show 54 = 2 * 27 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 27)]
  rw [totient_cert_2, totient_cert_27] <;> norm_num
@[simp] lemma totient_cert_55 : Nat.totient 55 = 40 := by
  rw [show 55 = 5 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 11)]
  rw [totient_cert_5, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_56 : Nat.totient 56 = 24 := by
  rw [show 56 = 8 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 7)]
  rw [totient_cert_8, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_57 : Nat.totient 57 = 36 := by
  rw [show 57 = 3 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 19)]
  rw [totient_cert_3, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_58 : Nat.totient 58 = 28 := by
  rw [show 58 = 2 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 29)]
  rw [totient_cert_2, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_59 : Nat.totient 59 = 58 := by
  rw [show 59 = 59^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 59) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_60 : Nat.totient 60 = 16 := by
  rw [show 60 = 4 * 15 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 15)]
  rw [totient_cert_4, totient_cert_15] <;> norm_num
@[simp] lemma totient_cert_61 : Nat.totient 61 = 60 := by
  rw [show 61 = 61^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 61) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_62 : Nat.totient 62 = 30 := by
  rw [show 62 = 2 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 31)]
  rw [totient_cert_2, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_63 : Nat.totient 63 = 36 := by
  rw [show 63 = 9 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 7)]
  rw [totient_cert_9, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_64 : Nat.totient 64 = 32 := by
  rw [show 64 = 2^6 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 6)] <;> norm_num
@[simp] lemma totient_cert_65 : Nat.totient 65 = 48 := by
  rw [show 65 = 5 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 13)]
  rw [totient_cert_5, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_66 : Nat.totient 66 = 20 := by
  rw [show 66 = 2 * 33 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 33)]
  rw [totient_cert_2, totient_cert_33] <;> norm_num
@[simp] lemma totient_cert_67 : Nat.totient 67 = 66 := by
  rw [show 67 = 67^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 67) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_68 : Nat.totient 68 = 32 := by
  rw [show 68 = 4 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 17)]
  rw [totient_cert_4, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_69 : Nat.totient 69 = 44 := by
  rw [show 69 = 3 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 23)]
  rw [totient_cert_3, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_70 : Nat.totient 70 = 24 := by
  rw [show 70 = 2 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 35)]
  rw [totient_cert_2, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_71 : Nat.totient 71 = 70 := by
  rw [show 71 = 71^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 71) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_72 : Nat.totient 72 = 24 := by
  rw [show 72 = 8 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 9)]
  rw [totient_cert_8, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_73 : Nat.totient 73 = 72 := by
  rw [show 73 = 73^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 73) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_74 : Nat.totient 74 = 36 := by
  rw [show 74 = 2 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 37)]
  rw [totient_cert_2, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_75 : Nat.totient 75 = 40 := by
  rw [show 75 = 3 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 25)]
  rw [totient_cert_3, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_76 : Nat.totient 76 = 36 := by
  rw [show 76 = 4 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 19)]
  rw [totient_cert_4, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_77 : Nat.totient 77 = 60 := by
  rw [show 77 = 7 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 11)]
  rw [totient_cert_7, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_78 : Nat.totient 78 = 24 := by
  rw [show 78 = 2 * 39 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 39)]
  rw [totient_cert_2, totient_cert_39] <;> norm_num
@[simp] lemma totient_cert_79 : Nat.totient 79 = 78 := by
  rw [show 79 = 79^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 79) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_80 : Nat.totient 80 = 32 := by
  rw [show 80 = 16 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 5)]
  rw [totient_cert_16, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_81 : Nat.totient 81 = 54 := by
  rw [show 81 = 3^4 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 4)] <;> norm_num
@[simp] lemma totient_cert_82 : Nat.totient 82 = 40 := by
  rw [show 82 = 2 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 41)]
  rw [totient_cert_2, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_83 : Nat.totient 83 = 82 := by
  rw [show 83 = 83^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 83) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_84 : Nat.totient 84 = 24 := by
  rw [show 84 = 4 * 21 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 21)]
  rw [totient_cert_4, totient_cert_21] <;> norm_num
@[simp] lemma totient_cert_85 : Nat.totient 85 = 64 := by
  rw [show 85 = 5 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 17)]
  rw [totient_cert_5, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_86 : Nat.totient 86 = 42 := by
  rw [show 86 = 2 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 43)]
  rw [totient_cert_2, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_87 : Nat.totient 87 = 56 := by
  rw [show 87 = 3 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 29)]
  rw [totient_cert_3, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_88 : Nat.totient 88 = 40 := by
  rw [show 88 = 8 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 11)]
  rw [totient_cert_8, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_89 : Nat.totient 89 = 88 := by
  rw [show 89 = 89^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 89) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_90 : Nat.totient 90 = 24 := by
  rw [show 90 = 2 * 45 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 45)]
  rw [totient_cert_2, totient_cert_45] <;> norm_num
@[simp] lemma totient_cert_91 : Nat.totient 91 = 72 := by
  rw [show 91 = 7 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 13)]
  rw [totient_cert_7, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_92 : Nat.totient 92 = 44 := by
  rw [show 92 = 4 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 23)]
  rw [totient_cert_4, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_93 : Nat.totient 93 = 60 := by
  rw [show 93 = 3 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 31)]
  rw [totient_cert_3, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_94 : Nat.totient 94 = 46 := by
  rw [show 94 = 2 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 47)]
  rw [totient_cert_2, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_95 : Nat.totient 95 = 72 := by
  rw [show 95 = 5 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 19)]
  rw [totient_cert_5, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_96 : Nat.totient 96 = 32 := by
  rw [show 96 = 32 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 3)]
  rw [totient_cert_32, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_97 : Nat.totient 97 = 96 := by
  rw [show 97 = 97^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 97) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_98 : Nat.totient 98 = 42 := by
  rw [show 98 = 2 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 49)]
  rw [totient_cert_2, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_99 : Nat.totient 99 = 60 := by
  rw [show 99 = 9 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 11)]
  rw [totient_cert_9, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_100 : Nat.totient 100 = 40 := by
  rw [show 100 = 4 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 25)]
  rw [totient_cert_4, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_101 : Nat.totient 101 = 100 := by
  rw [show 101 = 101^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 101) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_102 : Nat.totient 102 = 32 := by
  rw [show 102 = 2 * 51 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 51)]
  rw [totient_cert_2, totient_cert_51] <;> norm_num
@[simp] lemma totient_cert_103 : Nat.totient 103 = 102 := by
  rw [show 103 = 103^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 103) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_104 : Nat.totient 104 = 48 := by
  rw [show 104 = 8 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 13)]
  rw [totient_cert_8, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_105 : Nat.totient 105 = 48 := by
  rw [show 105 = 3 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 35)]
  rw [totient_cert_3, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_106 : Nat.totient 106 = 52 := by
  rw [show 106 = 2 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 53)]
  rw [totient_cert_2, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_107 : Nat.totient 107 = 106 := by
  rw [show 107 = 107^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 107) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_108 : Nat.totient 108 = 36 := by
  rw [show 108 = 4 * 27 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 27)]
  rw [totient_cert_4, totient_cert_27] <;> norm_num
@[simp] lemma totient_cert_109 : Nat.totient 109 = 108 := by
  rw [show 109 = 109^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 109) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_110 : Nat.totient 110 = 40 := by
  rw [show 110 = 2 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 55)]
  rw [totient_cert_2, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_111 : Nat.totient 111 = 72 := by
  rw [show 111 = 3 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 37)]
  rw [totient_cert_3, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_112 : Nat.totient 112 = 48 := by
  rw [show 112 = 16 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 7)]
  rw [totient_cert_16, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_113 : Nat.totient 113 = 112 := by
  rw [show 113 = 113^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 113) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_114 : Nat.totient 114 = 36 := by
  rw [show 114 = 2 * 57 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 57)]
  rw [totient_cert_2, totient_cert_57] <;> norm_num
@[simp] lemma totient_cert_115 : Nat.totient 115 = 88 := by
  rw [show 115 = 5 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 23)]
  rw [totient_cert_5, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_116 : Nat.totient 116 = 56 := by
  rw [show 116 = 4 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 29)]
  rw [totient_cert_4, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_117 : Nat.totient 117 = 72 := by
  rw [show 117 = 9 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 13)]
  rw [totient_cert_9, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_118 : Nat.totient 118 = 58 := by
  rw [show 118 = 2 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 59)]
  rw [totient_cert_2, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_119 : Nat.totient 119 = 96 := by
  rw [show 119 = 7 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 17)]
  rw [totient_cert_7, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_120 : Nat.totient 120 = 32 := by
  rw [show 120 = 8 * 15 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 15)]
  rw [totient_cert_8, totient_cert_15] <;> norm_num
@[simp] lemma totient_cert_121 : Nat.totient 121 = 110 := by
  rw [show 121 = 11^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 11) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_122 : Nat.totient 122 = 60 := by
  rw [show 122 = 2 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 61)]
  rw [totient_cert_2, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_123 : Nat.totient 123 = 80 := by
  rw [show 123 = 3 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 41)]
  rw [totient_cert_3, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_124 : Nat.totient 124 = 60 := by
  rw [show 124 = 4 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 31)]
  rw [totient_cert_4, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_125 : Nat.totient 125 = 100 := by
  rw [show 125 = 5^3 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 3)] <;> norm_num
@[simp] lemma totient_cert_126 : Nat.totient 126 = 36 := by
  rw [show 126 = 2 * 63 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 63)]
  rw [totient_cert_2, totient_cert_63] <;> norm_num
@[simp] lemma totient_cert_127 : Nat.totient 127 = 126 := by
  rw [show 127 = 127^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 127) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_128 : Nat.totient 128 = 64 := by
  rw [show 128 = 2^7 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 7)] <;> norm_num
@[simp] lemma totient_cert_129 : Nat.totient 129 = 84 := by
  rw [show 129 = 3 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 43)]
  rw [totient_cert_3, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_130 : Nat.totient 130 = 48 := by
  rw [show 130 = 2 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 65)]
  rw [totient_cert_2, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_131 : Nat.totient 131 = 130 := by
  rw [show 131 = 131^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 131) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_132 : Nat.totient 132 = 40 := by
  rw [show 132 = 4 * 33 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 33)]
  rw [totient_cert_4, totient_cert_33] <;> norm_num
@[simp] lemma totient_cert_133 : Nat.totient 133 = 108 := by
  rw [show 133 = 7 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 19)]
  rw [totient_cert_7, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_134 : Nat.totient 134 = 66 := by
  rw [show 134 = 2 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 67)]
  rw [totient_cert_2, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_135 : Nat.totient 135 = 72 := by
  rw [show 135 = 27 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 5)]
  rw [totient_cert_27, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_136 : Nat.totient 136 = 64 := by
  rw [show 136 = 8 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 17)]
  rw [totient_cert_8, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_137 : Nat.totient 137 = 136 := by
  rw [show 137 = 137^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 137) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_138 : Nat.totient 138 = 44 := by
  rw [show 138 = 2 * 69 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 69)]
  rw [totient_cert_2, totient_cert_69] <;> norm_num
@[simp] lemma totient_cert_139 : Nat.totient 139 = 138 := by
  rw [show 139 = 139^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 139) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_140 : Nat.totient 140 = 48 := by
  rw [show 140 = 4 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 35)]
  rw [totient_cert_4, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_141 : Nat.totient 141 = 92 := by
  rw [show 141 = 3 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 47)]
  rw [totient_cert_3, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_142 : Nat.totient 142 = 70 := by
  rw [show 142 = 2 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 71)]
  rw [totient_cert_2, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_143 : Nat.totient 143 = 120 := by
  rw [show 143 = 11 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 13)]
  rw [totient_cert_11, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_144 : Nat.totient 144 = 48 := by
  rw [show 144 = 16 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 9)]
  rw [totient_cert_16, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_145 : Nat.totient 145 = 112 := by
  rw [show 145 = 5 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 29)]
  rw [totient_cert_5, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_146 : Nat.totient 146 = 72 := by
  rw [show 146 = 2 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 73)]
  rw [totient_cert_2, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_147 : Nat.totient 147 = 84 := by
  rw [show 147 = 3 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 49)]
  rw [totient_cert_3, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_148 : Nat.totient 148 = 72 := by
  rw [show 148 = 4 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 37)]
  rw [totient_cert_4, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_149 : Nat.totient 149 = 148 := by
  rw [show 149 = 149^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 149) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_150 : Nat.totient 150 = 40 := by
  rw [show 150 = 2 * 75 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 75)]
  rw [totient_cert_2, totient_cert_75] <;> norm_num
@[simp] lemma totient_cert_151 : Nat.totient 151 = 150 := by
  rw [show 151 = 151^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 151) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_152 : Nat.totient 152 = 72 := by
  rw [show 152 = 8 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 19)]
  rw [totient_cert_8, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_153 : Nat.totient 153 = 96 := by
  rw [show 153 = 9 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 17)]
  rw [totient_cert_9, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_154 : Nat.totient 154 = 60 := by
  rw [show 154 = 2 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 77)]
  rw [totient_cert_2, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_155 : Nat.totient 155 = 120 := by
  rw [show 155 = 5 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 31)]
  rw [totient_cert_5, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_156 : Nat.totient 156 = 48 := by
  rw [show 156 = 4 * 39 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 39)]
  rw [totient_cert_4, totient_cert_39] <;> norm_num
@[simp] lemma totient_cert_157 : Nat.totient 157 = 156 := by
  rw [show 157 = 157^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 157) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_158 : Nat.totient 158 = 78 := by
  rw [show 158 = 2 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 79)]
  rw [totient_cert_2, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_159 : Nat.totient 159 = 104 := by
  rw [show 159 = 3 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 53)]
  rw [totient_cert_3, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_160 : Nat.totient 160 = 64 := by
  rw [show 160 = 32 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 5)]
  rw [totient_cert_32, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_161 : Nat.totient 161 = 132 := by
  rw [show 161 = 7 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 23)]
  rw [totient_cert_7, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_162 : Nat.totient 162 = 54 := by
  rw [show 162 = 2 * 81 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 81)]
  rw [totient_cert_2, totient_cert_81] <;> norm_num
@[simp] lemma totient_cert_163 : Nat.totient 163 = 162 := by
  rw [show 163 = 163^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 163) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_164 : Nat.totient 164 = 80 := by
  rw [show 164 = 4 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 41)]
  rw [totient_cert_4, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_165 : Nat.totient 165 = 80 := by
  rw [show 165 = 3 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 55)]
  rw [totient_cert_3, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_166 : Nat.totient 166 = 82 := by
  rw [show 166 = 2 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 83)]
  rw [totient_cert_2, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_167 : Nat.totient 167 = 166 := by
  rw [show 167 = 167^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 167) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_168 : Nat.totient 168 = 48 := by
  rw [show 168 = 8 * 21 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 21)]
  rw [totient_cert_8, totient_cert_21] <;> norm_num
@[simp] lemma totient_cert_169 : Nat.totient 169 = 156 := by
  rw [show 169 = 13^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 13) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_170 : Nat.totient 170 = 64 := by
  rw [show 170 = 2 * 85 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 85)]
  rw [totient_cert_2, totient_cert_85] <;> norm_num
@[simp] lemma totient_cert_171 : Nat.totient 171 = 108 := by
  rw [show 171 = 9 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 19)]
  rw [totient_cert_9, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_172 : Nat.totient 172 = 84 := by
  rw [show 172 = 4 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 43)]
  rw [totient_cert_4, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_173 : Nat.totient 173 = 172 := by
  rw [show 173 = 173^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 173) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_174 : Nat.totient 174 = 56 := by
  rw [show 174 = 2 * 87 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 87)]
  rw [totient_cert_2, totient_cert_87] <;> norm_num
@[simp] lemma totient_cert_175 : Nat.totient 175 = 120 := by
  rw [show 175 = 25 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 7)]
  rw [totient_cert_25, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_176 : Nat.totient 176 = 80 := by
  rw [show 176 = 16 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 11)]
  rw [totient_cert_16, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_177 : Nat.totient 177 = 116 := by
  rw [show 177 = 3 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 59)]
  rw [totient_cert_3, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_178 : Nat.totient 178 = 88 := by
  rw [show 178 = 2 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 89)]
  rw [totient_cert_2, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_179 : Nat.totient 179 = 178 := by
  rw [show 179 = 179^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 179) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_180 : Nat.totient 180 = 48 := by
  rw [show 180 = 4 * 45 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 45)]
  rw [totient_cert_4, totient_cert_45] <;> norm_num
@[simp] lemma totient_cert_181 : Nat.totient 181 = 180 := by
  rw [show 181 = 181^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 181) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_182 : Nat.totient 182 = 72 := by
  rw [show 182 = 2 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 91)]
  rw [totient_cert_2, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_183 : Nat.totient 183 = 120 := by
  rw [show 183 = 3 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 61)]
  rw [totient_cert_3, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_184 : Nat.totient 184 = 88 := by
  rw [show 184 = 8 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 23)]
  rw [totient_cert_8, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_185 : Nat.totient 185 = 144 := by
  rw [show 185 = 5 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 37)]
  rw [totient_cert_5, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_186 : Nat.totient 186 = 60 := by
  rw [show 186 = 2 * 93 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 93)]
  rw [totient_cert_2, totient_cert_93] <;> norm_num
@[simp] lemma totient_cert_187 : Nat.totient 187 = 160 := by
  rw [show 187 = 11 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 17)]
  rw [totient_cert_11, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_188 : Nat.totient 188 = 92 := by
  rw [show 188 = 4 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 47)]
  rw [totient_cert_4, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_189 : Nat.totient 189 = 108 := by
  rw [show 189 = 27 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 7)]
  rw [totient_cert_27, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_190 : Nat.totient 190 = 72 := by
  rw [show 190 = 2 * 95 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 95)]
  rw [totient_cert_2, totient_cert_95] <;> norm_num
@[simp] lemma totient_cert_191 : Nat.totient 191 = 190 := by
  rw [show 191 = 191^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 191) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_192 : Nat.totient 192 = 64 := by
  rw [show 192 = 64 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 3)]
  rw [totient_cert_64, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_193 : Nat.totient 193 = 192 := by
  rw [show 193 = 193^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 193) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_194 : Nat.totient 194 = 96 := by
  rw [show 194 = 2 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 97)]
  rw [totient_cert_2, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_195 : Nat.totient 195 = 96 := by
  rw [show 195 = 3 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 65)]
  rw [totient_cert_3, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_196 : Nat.totient 196 = 84 := by
  rw [show 196 = 4 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 49)]
  rw [totient_cert_4, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_197 : Nat.totient 197 = 196 := by
  rw [show 197 = 197^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 197) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_198 : Nat.totient 198 = 60 := by
  rw [show 198 = 2 * 99 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 99)]
  rw [totient_cert_2, totient_cert_99] <;> norm_num
@[simp] lemma totient_cert_199 : Nat.totient 199 = 198 := by
  rw [show 199 = 199^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 199) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_200 : Nat.totient 200 = 80 := by
  rw [show 200 = 8 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 25)]
  rw [totient_cert_8, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_201 : Nat.totient 201 = 132 := by
  rw [show 201 = 3 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 67)]
  rw [totient_cert_3, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_202 : Nat.totient 202 = 100 := by
  rw [show 202 = 2 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 101)]
  rw [totient_cert_2, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_203 : Nat.totient 203 = 168 := by
  rw [show 203 = 7 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 29)]
  rw [totient_cert_7, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_204 : Nat.totient 204 = 64 := by
  rw [show 204 = 4 * 51 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 51)]
  rw [totient_cert_4, totient_cert_51] <;> norm_num
@[simp] lemma totient_cert_205 : Nat.totient 205 = 160 := by
  rw [show 205 = 5 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 41)]
  rw [totient_cert_5, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_206 : Nat.totient 206 = 102 := by
  rw [show 206 = 2 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 103)]
  rw [totient_cert_2, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_207 : Nat.totient 207 = 132 := by
  rw [show 207 = 9 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 23)]
  rw [totient_cert_9, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_208 : Nat.totient 208 = 96 := by
  rw [show 208 = 16 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 13)]
  rw [totient_cert_16, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_209 : Nat.totient 209 = 180 := by
  rw [show 209 = 11 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 19)]
  rw [totient_cert_11, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_210 : Nat.totient 210 = 48 := by
  rw [show 210 = 2 * 105 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 105)]
  rw [totient_cert_2, totient_cert_105] <;> norm_num
@[simp] lemma totient_cert_211 : Nat.totient 211 = 210 := by
  rw [show 211 = 211^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 211) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_212 : Nat.totient 212 = 104 := by
  rw [show 212 = 4 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 53)]
  rw [totient_cert_4, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_213 : Nat.totient 213 = 140 := by
  rw [show 213 = 3 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 71)]
  rw [totient_cert_3, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_214 : Nat.totient 214 = 106 := by
  rw [show 214 = 2 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 107)]
  rw [totient_cert_2, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_215 : Nat.totient 215 = 168 := by
  rw [show 215 = 5 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 43)]
  rw [totient_cert_5, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_216 : Nat.totient 216 = 72 := by
  rw [show 216 = 8 * 27 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 27)]
  rw [totient_cert_8, totient_cert_27] <;> norm_num
@[simp] lemma totient_cert_217 : Nat.totient 217 = 180 := by
  rw [show 217 = 7 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 31)]
  rw [totient_cert_7, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_218 : Nat.totient 218 = 108 := by
  rw [show 218 = 2 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 109)]
  rw [totient_cert_2, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_219 : Nat.totient 219 = 144 := by
  rw [show 219 = 3 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 73)]
  rw [totient_cert_3, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_220 : Nat.totient 220 = 80 := by
  rw [show 220 = 4 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 55)]
  rw [totient_cert_4, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_221 : Nat.totient 221 = 192 := by
  rw [show 221 = 13 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 17)]
  rw [totient_cert_13, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_222 : Nat.totient 222 = 72 := by
  rw [show 222 = 2 * 111 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 111)]
  rw [totient_cert_2, totient_cert_111] <;> norm_num
@[simp] lemma totient_cert_223 : Nat.totient 223 = 222 := by
  rw [show 223 = 223^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 223) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_224 : Nat.totient 224 = 96 := by
  rw [show 224 = 32 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 7)]
  rw [totient_cert_32, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_225 : Nat.totient 225 = 120 := by
  rw [show 225 = 9 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 25)]
  rw [totient_cert_9, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_226 : Nat.totient 226 = 112 := by
  rw [show 226 = 2 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 113)]
  rw [totient_cert_2, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_227 : Nat.totient 227 = 226 := by
  rw [show 227 = 227^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 227) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_228 : Nat.totient 228 = 72 := by
  rw [show 228 = 4 * 57 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 57)]
  rw [totient_cert_4, totient_cert_57] <;> norm_num
@[simp] lemma totient_cert_229 : Nat.totient 229 = 228 := by
  rw [show 229 = 229^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 229) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_230 : Nat.totient 230 = 88 := by
  rw [show 230 = 2 * 115 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 115)]
  rw [totient_cert_2, totient_cert_115] <;> norm_num
@[simp] lemma totient_cert_231 : Nat.totient 231 = 120 := by
  rw [show 231 = 3 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 77)]
  rw [totient_cert_3, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_232 : Nat.totient 232 = 112 := by
  rw [show 232 = 8 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 29)]
  rw [totient_cert_8, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_233 : Nat.totient 233 = 232 := by
  rw [show 233 = 233^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 233) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_234 : Nat.totient 234 = 72 := by
  rw [show 234 = 2 * 117 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 117)]
  rw [totient_cert_2, totient_cert_117] <;> norm_num
@[simp] lemma totient_cert_235 : Nat.totient 235 = 184 := by
  rw [show 235 = 5 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 47)]
  rw [totient_cert_5, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_236 : Nat.totient 236 = 116 := by
  rw [show 236 = 4 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 59)]
  rw [totient_cert_4, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_237 : Nat.totient 237 = 156 := by
  rw [show 237 = 3 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 79)]
  rw [totient_cert_3, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_238 : Nat.totient 238 = 96 := by
  rw [show 238 = 2 * 119 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 119)]
  rw [totient_cert_2, totient_cert_119] <;> norm_num
@[simp] lemma totient_cert_239 : Nat.totient 239 = 238 := by
  rw [show 239 = 239^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 239) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_240 : Nat.totient 240 = 64 := by
  rw [show 240 = 16 * 15 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 15)]
  rw [totient_cert_16, totient_cert_15] <;> norm_num
@[simp] lemma totient_cert_241 : Nat.totient 241 = 240 := by
  rw [show 241 = 241^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 241) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_242 : Nat.totient 242 = 110 := by
  rw [show 242 = 2 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 121)]
  rw [totient_cert_2, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_243 : Nat.totient 243 = 162 := by
  rw [show 243 = 3^5 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 5)] <;> norm_num
@[simp] lemma totient_cert_244 : Nat.totient 244 = 120 := by
  rw [show 244 = 4 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 61)]
  rw [totient_cert_4, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_245 : Nat.totient 245 = 168 := by
  rw [show 245 = 5 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 49)]
  rw [totient_cert_5, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_246 : Nat.totient 246 = 80 := by
  rw [show 246 = 2 * 123 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 123)]
  rw [totient_cert_2, totient_cert_123] <;> norm_num
@[simp] lemma totient_cert_247 : Nat.totient 247 = 216 := by
  rw [show 247 = 13 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 19)]
  rw [totient_cert_13, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_248 : Nat.totient 248 = 120 := by
  rw [show 248 = 8 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 31)]
  rw [totient_cert_8, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_249 : Nat.totient 249 = 164 := by
  rw [show 249 = 3 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 83)]
  rw [totient_cert_3, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_250 : Nat.totient 250 = 100 := by
  rw [show 250 = 2 * 125 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 125)]
  rw [totient_cert_2, totient_cert_125] <;> norm_num
@[simp] lemma totient_cert_251 : Nat.totient 251 = 250 := by
  rw [show 251 = 251^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 251) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_252 : Nat.totient 252 = 72 := by
  rw [show 252 = 4 * 63 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 63)]
  rw [totient_cert_4, totient_cert_63] <;> norm_num
@[simp] lemma totient_cert_253 : Nat.totient 253 = 220 := by
  rw [show 253 = 11 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 23)]
  rw [totient_cert_11, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_254 : Nat.totient 254 = 126 := by
  rw [show 254 = 2 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 127)]
  rw [totient_cert_2, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_255 : Nat.totient 255 = 128 := by
  rw [show 255 = 3 * 85 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 85)]
  rw [totient_cert_3, totient_cert_85] <;> norm_num
@[simp] lemma totient_cert_256 : Nat.totient 256 = 128 := by
  rw [show 256 = 2^8 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 8)] <;> norm_num
@[simp] lemma totient_cert_257 : Nat.totient 257 = 256 := by
  rw [show 257 = 257^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 257) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_258 : Nat.totient 258 = 84 := by
  rw [show 258 = 2 * 129 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 129)]
  rw [totient_cert_2, totient_cert_129] <;> norm_num
@[simp] lemma totient_cert_259 : Nat.totient 259 = 216 := by
  rw [show 259 = 7 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 37)]
  rw [totient_cert_7, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_260 : Nat.totient 260 = 96 := by
  rw [show 260 = 4 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 65)]
  rw [totient_cert_4, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_261 : Nat.totient 261 = 168 := by
  rw [show 261 = 9 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 29)]
  rw [totient_cert_9, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_262 : Nat.totient 262 = 130 := by
  rw [show 262 = 2 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 131)]
  rw [totient_cert_2, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_263 : Nat.totient 263 = 262 := by
  rw [show 263 = 263^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 263) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_264 : Nat.totient 264 = 80 := by
  rw [show 264 = 8 * 33 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 33)]
  rw [totient_cert_8, totient_cert_33] <;> norm_num
@[simp] lemma totient_cert_265 : Nat.totient 265 = 208 := by
  rw [show 265 = 5 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 53)]
  rw [totient_cert_5, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_266 : Nat.totient 266 = 108 := by
  rw [show 266 = 2 * 133 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 133)]
  rw [totient_cert_2, totient_cert_133] <;> norm_num
@[simp] lemma totient_cert_267 : Nat.totient 267 = 176 := by
  rw [show 267 = 3 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 89)]
  rw [totient_cert_3, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_268 : Nat.totient 268 = 132 := by
  rw [show 268 = 4 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 67)]
  rw [totient_cert_4, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_269 : Nat.totient 269 = 268 := by
  rw [show 269 = 269^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 269) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_270 : Nat.totient 270 = 72 := by
  rw [show 270 = 2 * 135 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 135)]
  rw [totient_cert_2, totient_cert_135] <;> norm_num
@[simp] lemma totient_cert_271 : Nat.totient 271 = 270 := by
  rw [show 271 = 271^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 271) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_272 : Nat.totient 272 = 128 := by
  rw [show 272 = 16 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 17)]
  rw [totient_cert_16, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_273 : Nat.totient 273 = 144 := by
  rw [show 273 = 3 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 91)]
  rw [totient_cert_3, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_274 : Nat.totient 274 = 136 := by
  rw [show 274 = 2 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 137)]
  rw [totient_cert_2, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_275 : Nat.totient 275 = 200 := by
  rw [show 275 = 25 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 11)]
  rw [totient_cert_25, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_276 : Nat.totient 276 = 88 := by
  rw [show 276 = 4 * 69 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 69)]
  rw [totient_cert_4, totient_cert_69] <;> norm_num
@[simp] lemma totient_cert_277 : Nat.totient 277 = 276 := by
  rw [show 277 = 277^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 277) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_278 : Nat.totient 278 = 138 := by
  rw [show 278 = 2 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 139)]
  rw [totient_cert_2, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_279 : Nat.totient 279 = 180 := by
  rw [show 279 = 9 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 31)]
  rw [totient_cert_9, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_280 : Nat.totient 280 = 96 := by
  rw [show 280 = 8 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 35)]
  rw [totient_cert_8, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_281 : Nat.totient 281 = 280 := by
  rw [show 281 = 281^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 281) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_282 : Nat.totient 282 = 92 := by
  rw [show 282 = 2 * 141 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 141)]
  rw [totient_cert_2, totient_cert_141] <;> norm_num
@[simp] lemma totient_cert_283 : Nat.totient 283 = 282 := by
  rw [show 283 = 283^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 283) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_284 : Nat.totient 284 = 140 := by
  rw [show 284 = 4 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 71)]
  rw [totient_cert_4, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_285 : Nat.totient 285 = 144 := by
  rw [show 285 = 3 * 95 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 95)]
  rw [totient_cert_3, totient_cert_95] <;> norm_num
@[simp] lemma totient_cert_286 : Nat.totient 286 = 120 := by
  rw [show 286 = 2 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 143)]
  rw [totient_cert_2, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_287 : Nat.totient 287 = 240 := by
  rw [show 287 = 7 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 41)]
  rw [totient_cert_7, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_288 : Nat.totient 288 = 96 := by
  rw [show 288 = 32 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 9)]
  rw [totient_cert_32, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_289 : Nat.totient 289 = 272 := by
  rw [show 289 = 17^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 17) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_290 : Nat.totient 290 = 112 := by
  rw [show 290 = 2 * 145 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 145)]
  rw [totient_cert_2, totient_cert_145] <;> norm_num
@[simp] lemma totient_cert_291 : Nat.totient 291 = 192 := by
  rw [show 291 = 3 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 97)]
  rw [totient_cert_3, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_292 : Nat.totient 292 = 144 := by
  rw [show 292 = 4 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 73)]
  rw [totient_cert_4, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_293 : Nat.totient 293 = 292 := by
  rw [show 293 = 293^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 293) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_294 : Nat.totient 294 = 84 := by
  rw [show 294 = 2 * 147 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 147)]
  rw [totient_cert_2, totient_cert_147] <;> norm_num
@[simp] lemma totient_cert_295 : Nat.totient 295 = 232 := by
  rw [show 295 = 5 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 59)]
  rw [totient_cert_5, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_296 : Nat.totient 296 = 144 := by
  rw [show 296 = 8 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 37)]
  rw [totient_cert_8, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_297 : Nat.totient 297 = 180 := by
  rw [show 297 = 27 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 11)]
  rw [totient_cert_27, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_298 : Nat.totient 298 = 148 := by
  rw [show 298 = 2 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 149)]
  rw [totient_cert_2, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_299 : Nat.totient 299 = 264 := by
  rw [show 299 = 13 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 23)]
  rw [totient_cert_13, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_300 : Nat.totient 300 = 80 := by
  rw [show 300 = 4 * 75 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 75)]
  rw [totient_cert_4, totient_cert_75] <;> norm_num
@[simp] lemma totient_cert_301 : Nat.totient 301 = 252 := by
  rw [show 301 = 7 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 43)]
  rw [totient_cert_7, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_302 : Nat.totient 302 = 150 := by
  rw [show 302 = 2 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 151)]
  rw [totient_cert_2, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_303 : Nat.totient 303 = 200 := by
  rw [show 303 = 3 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 101)]
  rw [totient_cert_3, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_304 : Nat.totient 304 = 144 := by
  rw [show 304 = 16 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 19)]
  rw [totient_cert_16, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_305 : Nat.totient 305 = 240 := by
  rw [show 305 = 5 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 61)]
  rw [totient_cert_5, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_306 : Nat.totient 306 = 96 := by
  rw [show 306 = 2 * 153 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 153)]
  rw [totient_cert_2, totient_cert_153] <;> norm_num
@[simp] lemma totient_cert_307 : Nat.totient 307 = 306 := by
  rw [show 307 = 307^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 307) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_308 : Nat.totient 308 = 120 := by
  rw [show 308 = 4 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 77)]
  rw [totient_cert_4, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_309 : Nat.totient 309 = 204 := by
  rw [show 309 = 3 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 103)]
  rw [totient_cert_3, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_310 : Nat.totient 310 = 120 := by
  rw [show 310 = 2 * 155 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 155)]
  rw [totient_cert_2, totient_cert_155] <;> norm_num
@[simp] lemma totient_cert_311 : Nat.totient 311 = 310 := by
  rw [show 311 = 311^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 311) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_312 : Nat.totient 312 = 96 := by
  rw [show 312 = 8 * 39 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 39)]
  rw [totient_cert_8, totient_cert_39] <;> norm_num
@[simp] lemma totient_cert_313 : Nat.totient 313 = 312 := by
  rw [show 313 = 313^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 313) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_314 : Nat.totient 314 = 156 := by
  rw [show 314 = 2 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 157)]
  rw [totient_cert_2, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_315 : Nat.totient 315 = 144 := by
  rw [show 315 = 9 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 35)]
  rw [totient_cert_9, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_316 : Nat.totient 316 = 156 := by
  rw [show 316 = 4 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 79)]
  rw [totient_cert_4, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_317 : Nat.totient 317 = 316 := by
  rw [show 317 = 317^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 317) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_318 : Nat.totient 318 = 104 := by
  rw [show 318 = 2 * 159 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 159)]
  rw [totient_cert_2, totient_cert_159] <;> norm_num
@[simp] lemma totient_cert_319 : Nat.totient 319 = 280 := by
  rw [show 319 = 11 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 29)]
  rw [totient_cert_11, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_320 : Nat.totient 320 = 128 := by
  rw [show 320 = 64 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 5)]
  rw [totient_cert_64, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_321 : Nat.totient 321 = 212 := by
  rw [show 321 = 3 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 107)]
  rw [totient_cert_3, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_322 : Nat.totient 322 = 132 := by
  rw [show 322 = 2 * 161 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 161)]
  rw [totient_cert_2, totient_cert_161] <;> norm_num
@[simp] lemma totient_cert_323 : Nat.totient 323 = 288 := by
  rw [show 323 = 17 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 19)]
  rw [totient_cert_17, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_324 : Nat.totient 324 = 108 := by
  rw [show 324 = 4 * 81 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 81)]
  rw [totient_cert_4, totient_cert_81] <;> norm_num
@[simp] lemma totient_cert_325 : Nat.totient 325 = 240 := by
  rw [show 325 = 25 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 13)]
  rw [totient_cert_25, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_326 : Nat.totient 326 = 162 := by
  rw [show 326 = 2 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 163)]
  rw [totient_cert_2, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_327 : Nat.totient 327 = 216 := by
  rw [show 327 = 3 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 109)]
  rw [totient_cert_3, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_328 : Nat.totient 328 = 160 := by
  rw [show 328 = 8 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 41)]
  rw [totient_cert_8, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_329 : Nat.totient 329 = 276 := by
  rw [show 329 = 7 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 47)]
  rw [totient_cert_7, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_330 : Nat.totient 330 = 80 := by
  rw [show 330 = 2 * 165 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 165)]
  rw [totient_cert_2, totient_cert_165] <;> norm_num
@[simp] lemma totient_cert_331 : Nat.totient 331 = 330 := by
  rw [show 331 = 331^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 331) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_332 : Nat.totient 332 = 164 := by
  rw [show 332 = 4 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 83)]
  rw [totient_cert_4, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_333 : Nat.totient 333 = 216 := by
  rw [show 333 = 9 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 37)]
  rw [totient_cert_9, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_334 : Nat.totient 334 = 166 := by
  rw [show 334 = 2 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 167)]
  rw [totient_cert_2, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_335 : Nat.totient 335 = 264 := by
  rw [show 335 = 5 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 67)]
  rw [totient_cert_5, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_336 : Nat.totient 336 = 96 := by
  rw [show 336 = 16 * 21 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 21)]
  rw [totient_cert_16, totient_cert_21] <;> norm_num
@[simp] lemma totient_cert_337 : Nat.totient 337 = 336 := by
  rw [show 337 = 337^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 337) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_338 : Nat.totient 338 = 156 := by
  rw [show 338 = 2 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 169)]
  rw [totient_cert_2, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_339 : Nat.totient 339 = 224 := by
  rw [show 339 = 3 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 113)]
  rw [totient_cert_3, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_340 : Nat.totient 340 = 128 := by
  rw [show 340 = 4 * 85 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 85)]
  rw [totient_cert_4, totient_cert_85] <;> norm_num
@[simp] lemma totient_cert_341 : Nat.totient 341 = 300 := by
  rw [show 341 = 11 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 31)]
  rw [totient_cert_11, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_342 : Nat.totient 342 = 108 := by
  rw [show 342 = 2 * 171 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 171)]
  rw [totient_cert_2, totient_cert_171] <;> norm_num
@[simp] lemma totient_cert_343 : Nat.totient 343 = 294 := by
  rw [show 343 = 7^3 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 7) (by norm_num : 0 < 3)] <;> norm_num
@[simp] lemma totient_cert_344 : Nat.totient 344 = 168 := by
  rw [show 344 = 8 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 43)]
  rw [totient_cert_8, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_345 : Nat.totient 345 = 176 := by
  rw [show 345 = 3 * 115 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 115)]
  rw [totient_cert_3, totient_cert_115] <;> norm_num
@[simp] lemma totient_cert_346 : Nat.totient 346 = 172 := by
  rw [show 346 = 2 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 173)]
  rw [totient_cert_2, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_347 : Nat.totient 347 = 346 := by
  rw [show 347 = 347^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 347) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_348 : Nat.totient 348 = 112 := by
  rw [show 348 = 4 * 87 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 87)]
  rw [totient_cert_4, totient_cert_87] <;> norm_num
@[simp] lemma totient_cert_349 : Nat.totient 349 = 348 := by
  rw [show 349 = 349^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 349) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_350 : Nat.totient 350 = 120 := by
  rw [show 350 = 2 * 175 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 175)]
  rw [totient_cert_2, totient_cert_175] <;> norm_num
@[simp] lemma totient_cert_351 : Nat.totient 351 = 216 := by
  rw [show 351 = 27 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 13)]
  rw [totient_cert_27, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_352 : Nat.totient 352 = 160 := by
  rw [show 352 = 32 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 11)]
  rw [totient_cert_32, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_353 : Nat.totient 353 = 352 := by
  rw [show 353 = 353^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 353) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_354 : Nat.totient 354 = 116 := by
  rw [show 354 = 2 * 177 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 177)]
  rw [totient_cert_2, totient_cert_177] <;> norm_num
@[simp] lemma totient_cert_355 : Nat.totient 355 = 280 := by
  rw [show 355 = 5 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 71)]
  rw [totient_cert_5, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_356 : Nat.totient 356 = 176 := by
  rw [show 356 = 4 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 89)]
  rw [totient_cert_4, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_357 : Nat.totient 357 = 192 := by
  rw [show 357 = 3 * 119 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 119)]
  rw [totient_cert_3, totient_cert_119] <;> norm_num
@[simp] lemma totient_cert_358 : Nat.totient 358 = 178 := by
  rw [show 358 = 2 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 179)]
  rw [totient_cert_2, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_359 : Nat.totient 359 = 358 := by
  rw [show 359 = 359^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 359) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_360 : Nat.totient 360 = 96 := by
  rw [show 360 = 8 * 45 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 45)]
  rw [totient_cert_8, totient_cert_45] <;> norm_num
@[simp] lemma totient_cert_361 : Nat.totient 361 = 342 := by
  rw [show 361 = 19^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 19) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_362 : Nat.totient 362 = 180 := by
  rw [show 362 = 2 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 181)]
  rw [totient_cert_2, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_363 : Nat.totient 363 = 220 := by
  rw [show 363 = 3 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 121)]
  rw [totient_cert_3, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_364 : Nat.totient 364 = 144 := by
  rw [show 364 = 4 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 91)]
  rw [totient_cert_4, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_365 : Nat.totient 365 = 288 := by
  rw [show 365 = 5 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 73)]
  rw [totient_cert_5, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_366 : Nat.totient 366 = 120 := by
  rw [show 366 = 2 * 183 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 183)]
  rw [totient_cert_2, totient_cert_183] <;> norm_num
@[simp] lemma totient_cert_367 : Nat.totient 367 = 366 := by
  rw [show 367 = 367^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 367) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_368 : Nat.totient 368 = 176 := by
  rw [show 368 = 16 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 23)]
  rw [totient_cert_16, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_369 : Nat.totient 369 = 240 := by
  rw [show 369 = 9 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 41)]
  rw [totient_cert_9, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_370 : Nat.totient 370 = 144 := by
  rw [show 370 = 2 * 185 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 185)]
  rw [totient_cert_2, totient_cert_185] <;> norm_num
@[simp] lemma totient_cert_371 : Nat.totient 371 = 312 := by
  rw [show 371 = 7 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 53)]
  rw [totient_cert_7, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_372 : Nat.totient 372 = 120 := by
  rw [show 372 = 4 * 93 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 93)]
  rw [totient_cert_4, totient_cert_93] <;> norm_num
@[simp] lemma totient_cert_373 : Nat.totient 373 = 372 := by
  rw [show 373 = 373^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 373) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_374 : Nat.totient 374 = 160 := by
  rw [show 374 = 2 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 187)]
  rw [totient_cert_2, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_375 : Nat.totient 375 = 200 := by
  rw [show 375 = 3 * 125 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 125)]
  rw [totient_cert_3, totient_cert_125] <;> norm_num
@[simp] lemma totient_cert_376 : Nat.totient 376 = 184 := by
  rw [show 376 = 8 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 47)]
  rw [totient_cert_8, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_377 : Nat.totient 377 = 336 := by
  rw [show 377 = 13 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 29)]
  rw [totient_cert_13, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_378 : Nat.totient 378 = 108 := by
  rw [show 378 = 2 * 189 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 189)]
  rw [totient_cert_2, totient_cert_189] <;> norm_num
@[simp] lemma totient_cert_379 : Nat.totient 379 = 378 := by
  rw [show 379 = 379^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 379) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_380 : Nat.totient 380 = 144 := by
  rw [show 380 = 4 * 95 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 95)]
  rw [totient_cert_4, totient_cert_95] <;> norm_num
@[simp] lemma totient_cert_381 : Nat.totient 381 = 252 := by
  rw [show 381 = 3 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 127)]
  rw [totient_cert_3, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_382 : Nat.totient 382 = 190 := by
  rw [show 382 = 2 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 191)]
  rw [totient_cert_2, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_383 : Nat.totient 383 = 382 := by
  rw [show 383 = 383^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 383) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_384 : Nat.totient 384 = 128 := by
  rw [show 384 = 128 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 128 3)]
  rw [totient_cert_128, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_385 : Nat.totient 385 = 240 := by
  rw [show 385 = 5 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 77)]
  rw [totient_cert_5, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_386 : Nat.totient 386 = 192 := by
  rw [show 386 = 2 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 193)]
  rw [totient_cert_2, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_387 : Nat.totient 387 = 252 := by
  rw [show 387 = 9 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 43)]
  rw [totient_cert_9, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_388 : Nat.totient 388 = 192 := by
  rw [show 388 = 4 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 97)]
  rw [totient_cert_4, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_389 : Nat.totient 389 = 388 := by
  rw [show 389 = 389^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 389) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_390 : Nat.totient 390 = 96 := by
  rw [show 390 = 2 * 195 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 195)]
  rw [totient_cert_2, totient_cert_195] <;> norm_num
@[simp] lemma totient_cert_391 : Nat.totient 391 = 352 := by
  rw [show 391 = 17 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 23)]
  rw [totient_cert_17, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_392 : Nat.totient 392 = 168 := by
  rw [show 392 = 8 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 49)]
  rw [totient_cert_8, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_393 : Nat.totient 393 = 260 := by
  rw [show 393 = 3 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 131)]
  rw [totient_cert_3, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_394 : Nat.totient 394 = 196 := by
  rw [show 394 = 2 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 197)]
  rw [totient_cert_2, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_395 : Nat.totient 395 = 312 := by
  rw [show 395 = 5 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 79)]
  rw [totient_cert_5, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_396 : Nat.totient 396 = 120 := by
  rw [show 396 = 4 * 99 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 99)]
  rw [totient_cert_4, totient_cert_99] <;> norm_num
@[simp] lemma totient_cert_397 : Nat.totient 397 = 396 := by
  rw [show 397 = 397^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 397) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_398 : Nat.totient 398 = 198 := by
  rw [show 398 = 2 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 199)]
  rw [totient_cert_2, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_399 : Nat.totient 399 = 216 := by
  rw [show 399 = 3 * 133 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 133)]
  rw [totient_cert_3, totient_cert_133] <;> norm_num
@[simp] lemma totient_cert_400 : Nat.totient 400 = 160 := by
  rw [show 400 = 16 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 25)]
  rw [totient_cert_16, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_401 : Nat.totient 401 = 400 := by
  rw [show 401 = 401^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 401) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_402 : Nat.totient 402 = 132 := by
  rw [show 402 = 2 * 201 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 201)]
  rw [totient_cert_2, totient_cert_201] <;> norm_num
@[simp] lemma totient_cert_403 : Nat.totient 403 = 360 := by
  rw [show 403 = 13 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 31)]
  rw [totient_cert_13, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_404 : Nat.totient 404 = 200 := by
  rw [show 404 = 4 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 101)]
  rw [totient_cert_4, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_405 : Nat.totient 405 = 216 := by
  rw [show 405 = 81 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 81 5)]
  rw [totient_cert_81, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_406 : Nat.totient 406 = 168 := by
  rw [show 406 = 2 * 203 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 203)]
  rw [totient_cert_2, totient_cert_203] <;> norm_num
@[simp] lemma totient_cert_407 : Nat.totient 407 = 360 := by
  rw [show 407 = 11 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 37)]
  rw [totient_cert_11, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_408 : Nat.totient 408 = 128 := by
  rw [show 408 = 8 * 51 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 51)]
  rw [totient_cert_8, totient_cert_51] <;> norm_num
@[simp] lemma totient_cert_409 : Nat.totient 409 = 408 := by
  rw [show 409 = 409^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 409) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_410 : Nat.totient 410 = 160 := by
  rw [show 410 = 2 * 205 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 205)]
  rw [totient_cert_2, totient_cert_205] <;> norm_num
@[simp] lemma totient_cert_411 : Nat.totient 411 = 272 := by
  rw [show 411 = 3 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 137)]
  rw [totient_cert_3, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_412 : Nat.totient 412 = 204 := by
  rw [show 412 = 4 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 103)]
  rw [totient_cert_4, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_413 : Nat.totient 413 = 348 := by
  rw [show 413 = 7 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 59)]
  rw [totient_cert_7, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_414 : Nat.totient 414 = 132 := by
  rw [show 414 = 2 * 207 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 207)]
  rw [totient_cert_2, totient_cert_207] <;> norm_num
@[simp] lemma totient_cert_415 : Nat.totient 415 = 328 := by
  rw [show 415 = 5 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 83)]
  rw [totient_cert_5, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_416 : Nat.totient 416 = 192 := by
  rw [show 416 = 32 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 13)]
  rw [totient_cert_32, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_417 : Nat.totient 417 = 276 := by
  rw [show 417 = 3 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 139)]
  rw [totient_cert_3, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_418 : Nat.totient 418 = 180 := by
  rw [show 418 = 2 * 209 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 209)]
  rw [totient_cert_2, totient_cert_209] <;> norm_num
@[simp] lemma totient_cert_419 : Nat.totient 419 = 418 := by
  rw [show 419 = 419^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 419) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_420 : Nat.totient 420 = 96 := by
  rw [show 420 = 4 * 105 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 105)]
  rw [totient_cert_4, totient_cert_105] <;> norm_num
@[simp] lemma totient_cert_421 : Nat.totient 421 = 420 := by
  rw [show 421 = 421^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 421) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_422 : Nat.totient 422 = 210 := by
  rw [show 422 = 2 * 211 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 211)]
  rw [totient_cert_2, totient_cert_211] <;> norm_num
@[simp] lemma totient_cert_423 : Nat.totient 423 = 276 := by
  rw [show 423 = 9 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 47)]
  rw [totient_cert_9, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_424 : Nat.totient 424 = 208 := by
  rw [show 424 = 8 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 53)]
  rw [totient_cert_8, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_425 : Nat.totient 425 = 320 := by
  rw [show 425 = 25 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 17)]
  rw [totient_cert_25, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_426 : Nat.totient 426 = 140 := by
  rw [show 426 = 2 * 213 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 213)]
  rw [totient_cert_2, totient_cert_213] <;> norm_num
@[simp] lemma totient_cert_427 : Nat.totient 427 = 360 := by
  rw [show 427 = 7 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 61)]
  rw [totient_cert_7, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_428 : Nat.totient 428 = 212 := by
  rw [show 428 = 4 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 107)]
  rw [totient_cert_4, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_429 : Nat.totient 429 = 240 := by
  rw [show 429 = 3 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 143)]
  rw [totient_cert_3, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_430 : Nat.totient 430 = 168 := by
  rw [show 430 = 2 * 215 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 215)]
  rw [totient_cert_2, totient_cert_215] <;> norm_num
@[simp] lemma totient_cert_431 : Nat.totient 431 = 430 := by
  rw [show 431 = 431^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 431) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_432 : Nat.totient 432 = 144 := by
  rw [show 432 = 16 * 27 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 27)]
  rw [totient_cert_16, totient_cert_27] <;> norm_num
@[simp] lemma totient_cert_433 : Nat.totient 433 = 432 := by
  rw [show 433 = 433^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 433) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_434 : Nat.totient 434 = 180 := by
  rw [show 434 = 2 * 217 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 217)]
  rw [totient_cert_2, totient_cert_217] <;> norm_num
@[simp] lemma totient_cert_435 : Nat.totient 435 = 224 := by
  rw [show 435 = 3 * 145 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 145)]
  rw [totient_cert_3, totient_cert_145] <;> norm_num
@[simp] lemma totient_cert_436 : Nat.totient 436 = 216 := by
  rw [show 436 = 4 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 109)]
  rw [totient_cert_4, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_437 : Nat.totient 437 = 396 := by
  rw [show 437 = 19 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 23)]
  rw [totient_cert_19, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_438 : Nat.totient 438 = 144 := by
  rw [show 438 = 2 * 219 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 219)]
  rw [totient_cert_2, totient_cert_219] <;> norm_num
@[simp] lemma totient_cert_439 : Nat.totient 439 = 438 := by
  rw [show 439 = 439^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 439) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_440 : Nat.totient 440 = 160 := by
  rw [show 440 = 8 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 55)]
  rw [totient_cert_8, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_441 : Nat.totient 441 = 252 := by
  rw [show 441 = 9 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 49)]
  rw [totient_cert_9, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_442 : Nat.totient 442 = 192 := by
  rw [show 442 = 2 * 221 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 221)]
  rw [totient_cert_2, totient_cert_221] <;> norm_num
@[simp] lemma totient_cert_443 : Nat.totient 443 = 442 := by
  rw [show 443 = 443^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 443) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_444 : Nat.totient 444 = 144 := by
  rw [show 444 = 4 * 111 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 111)]
  rw [totient_cert_4, totient_cert_111] <;> norm_num
@[simp] lemma totient_cert_445 : Nat.totient 445 = 352 := by
  rw [show 445 = 5 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 89)]
  rw [totient_cert_5, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_446 : Nat.totient 446 = 222 := by
  rw [show 446 = 2 * 223 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 223)]
  rw [totient_cert_2, totient_cert_223] <;> norm_num
@[simp] lemma totient_cert_447 : Nat.totient 447 = 296 := by
  rw [show 447 = 3 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 149)]
  rw [totient_cert_3, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_448 : Nat.totient 448 = 192 := by
  rw [show 448 = 64 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 7)]
  rw [totient_cert_64, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_449 : Nat.totient 449 = 448 := by
  rw [show 449 = 449^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 449) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_450 : Nat.totient 450 = 120 := by
  rw [show 450 = 2 * 225 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 225)]
  rw [totient_cert_2, totient_cert_225] <;> norm_num
@[simp] lemma totient_cert_451 : Nat.totient 451 = 400 := by
  rw [show 451 = 11 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 41)]
  rw [totient_cert_11, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_452 : Nat.totient 452 = 224 := by
  rw [show 452 = 4 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 113)]
  rw [totient_cert_4, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_453 : Nat.totient 453 = 300 := by
  rw [show 453 = 3 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 151)]
  rw [totient_cert_3, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_454 : Nat.totient 454 = 226 := by
  rw [show 454 = 2 * 227 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 227)]
  rw [totient_cert_2, totient_cert_227] <;> norm_num
@[simp] lemma totient_cert_455 : Nat.totient 455 = 288 := by
  rw [show 455 = 5 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 91)]
  rw [totient_cert_5, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_456 : Nat.totient 456 = 144 := by
  rw [show 456 = 8 * 57 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 57)]
  rw [totient_cert_8, totient_cert_57] <;> norm_num
@[simp] lemma totient_cert_457 : Nat.totient 457 = 456 := by
  rw [show 457 = 457^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 457) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_458 : Nat.totient 458 = 228 := by
  rw [show 458 = 2 * 229 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 229)]
  rw [totient_cert_2, totient_cert_229] <;> norm_num
@[simp] lemma totient_cert_459 : Nat.totient 459 = 288 := by
  rw [show 459 = 27 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 17)]
  rw [totient_cert_27, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_460 : Nat.totient 460 = 176 := by
  rw [show 460 = 4 * 115 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 115)]
  rw [totient_cert_4, totient_cert_115] <;> norm_num
@[simp] lemma totient_cert_461 : Nat.totient 461 = 460 := by
  rw [show 461 = 461^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 461) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_462 : Nat.totient 462 = 120 := by
  rw [show 462 = 2 * 231 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 231)]
  rw [totient_cert_2, totient_cert_231] <;> norm_num
@[simp] lemma totient_cert_463 : Nat.totient 463 = 462 := by
  rw [show 463 = 463^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 463) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_464 : Nat.totient 464 = 224 := by
  rw [show 464 = 16 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 29)]
  rw [totient_cert_16, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_465 : Nat.totient 465 = 240 := by
  rw [show 465 = 3 * 155 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 155)]
  rw [totient_cert_3, totient_cert_155] <;> norm_num
@[simp] lemma totient_cert_466 : Nat.totient 466 = 232 := by
  rw [show 466 = 2 * 233 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 233)]
  rw [totient_cert_2, totient_cert_233] <;> norm_num
@[simp] lemma totient_cert_467 : Nat.totient 467 = 466 := by
  rw [show 467 = 467^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 467) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_468 : Nat.totient 468 = 144 := by
  rw [show 468 = 4 * 117 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 117)]
  rw [totient_cert_4, totient_cert_117] <;> norm_num
@[simp] lemma totient_cert_469 : Nat.totient 469 = 396 := by
  rw [show 469 = 7 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 67)]
  rw [totient_cert_7, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_470 : Nat.totient 470 = 184 := by
  rw [show 470 = 2 * 235 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 235)]
  rw [totient_cert_2, totient_cert_235] <;> norm_num
@[simp] lemma totient_cert_471 : Nat.totient 471 = 312 := by
  rw [show 471 = 3 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 157)]
  rw [totient_cert_3, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_472 : Nat.totient 472 = 232 := by
  rw [show 472 = 8 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 59)]
  rw [totient_cert_8, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_473 : Nat.totient 473 = 420 := by
  rw [show 473 = 11 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 43)]
  rw [totient_cert_11, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_474 : Nat.totient 474 = 156 := by
  rw [show 474 = 2 * 237 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 237)]
  rw [totient_cert_2, totient_cert_237] <;> norm_num
@[simp] lemma totient_cert_475 : Nat.totient 475 = 360 := by
  rw [show 475 = 25 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 19)]
  rw [totient_cert_25, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_476 : Nat.totient 476 = 192 := by
  rw [show 476 = 4 * 119 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 119)]
  rw [totient_cert_4, totient_cert_119] <;> norm_num
@[simp] lemma totient_cert_477 : Nat.totient 477 = 312 := by
  rw [show 477 = 9 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 53)]
  rw [totient_cert_9, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_478 : Nat.totient 478 = 238 := by
  rw [show 478 = 2 * 239 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 239)]
  rw [totient_cert_2, totient_cert_239] <;> norm_num
@[simp] lemma totient_cert_479 : Nat.totient 479 = 478 := by
  rw [show 479 = 479^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 479) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_480 : Nat.totient 480 = 128 := by
  rw [show 480 = 32 * 15 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 15)]
  rw [totient_cert_32, totient_cert_15] <;> norm_num
@[simp] lemma totient_cert_481 : Nat.totient 481 = 432 := by
  rw [show 481 = 13 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 37)]
  rw [totient_cert_13, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_482 : Nat.totient 482 = 240 := by
  rw [show 482 = 2 * 241 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 241)]
  rw [totient_cert_2, totient_cert_241] <;> norm_num
@[simp] lemma totient_cert_483 : Nat.totient 483 = 264 := by
  rw [show 483 = 3 * 161 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 161)]
  rw [totient_cert_3, totient_cert_161] <;> norm_num
@[simp] lemma totient_cert_484 : Nat.totient 484 = 220 := by
  rw [show 484 = 4 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 121)]
  rw [totient_cert_4, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_485 : Nat.totient 485 = 384 := by
  rw [show 485 = 5 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 97)]
  rw [totient_cert_5, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_486 : Nat.totient 486 = 162 := by
  rw [show 486 = 2 * 243 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 243)]
  rw [totient_cert_2, totient_cert_243] <;> norm_num
@[simp] lemma totient_cert_487 : Nat.totient 487 = 486 := by
  rw [show 487 = 487^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 487) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_488 : Nat.totient 488 = 240 := by
  rw [show 488 = 8 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 61)]
  rw [totient_cert_8, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_489 : Nat.totient 489 = 324 := by
  rw [show 489 = 3 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 163)]
  rw [totient_cert_3, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_490 : Nat.totient 490 = 168 := by
  rw [show 490 = 2 * 245 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 245)]
  rw [totient_cert_2, totient_cert_245] <;> norm_num
@[simp] lemma totient_cert_491 : Nat.totient 491 = 490 := by
  rw [show 491 = 491^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 491) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_492 : Nat.totient 492 = 160 := by
  rw [show 492 = 4 * 123 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 123)]
  rw [totient_cert_4, totient_cert_123] <;> norm_num
@[simp] lemma totient_cert_493 : Nat.totient 493 = 448 := by
  rw [show 493 = 17 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 29)]
  rw [totient_cert_17, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_494 : Nat.totient 494 = 216 := by
  rw [show 494 = 2 * 247 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 247)]
  rw [totient_cert_2, totient_cert_247] <;> norm_num
@[simp] lemma totient_cert_495 : Nat.totient 495 = 240 := by
  rw [show 495 = 9 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 55)]
  rw [totient_cert_9, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_496 : Nat.totient 496 = 240 := by
  rw [show 496 = 16 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 31)]
  rw [totient_cert_16, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_497 : Nat.totient 497 = 420 := by
  rw [show 497 = 7 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 71)]
  rw [totient_cert_7, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_498 : Nat.totient 498 = 164 := by
  rw [show 498 = 2 * 249 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 249)]
  rw [totient_cert_2, totient_cert_249] <;> norm_num
@[simp] lemma totient_cert_499 : Nat.totient 499 = 498 := by
  rw [show 499 = 499^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 499) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_500 : Nat.totient 500 = 200 := by
  rw [show 500 = 4 * 125 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 125)]
  rw [totient_cert_4, totient_cert_125] <;> norm_num
@[simp] lemma totient_cert_501 : Nat.totient 501 = 332 := by
  rw [show 501 = 3 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 167)]
  rw [totient_cert_3, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_502 : Nat.totient 502 = 250 := by
  rw [show 502 = 2 * 251 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 251)]
  rw [totient_cert_2, totient_cert_251] <;> norm_num
@[simp] lemma totient_cert_503 : Nat.totient 503 = 502 := by
  rw [show 503 = 503^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 503) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_504 : Nat.totient 504 = 144 := by
  rw [show 504 = 8 * 63 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 63)]
  rw [totient_cert_8, totient_cert_63] <;> norm_num
@[simp] lemma totient_cert_505 : Nat.totient 505 = 400 := by
  rw [show 505 = 5 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 101)]
  rw [totient_cert_5, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_506 : Nat.totient 506 = 220 := by
  rw [show 506 = 2 * 253 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 253)]
  rw [totient_cert_2, totient_cert_253] <;> norm_num
@[simp] lemma totient_cert_507 : Nat.totient 507 = 312 := by
  rw [show 507 = 3 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 169)]
  rw [totient_cert_3, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_508 : Nat.totient 508 = 252 := by
  rw [show 508 = 4 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 127)]
  rw [totient_cert_4, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_509 : Nat.totient 509 = 508 := by
  rw [show 509 = 509^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 509) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_510 : Nat.totient 510 = 128 := by
  rw [show 510 = 2 * 255 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 255)]
  rw [totient_cert_2, totient_cert_255] <;> norm_num
@[simp] lemma totient_cert_511 : Nat.totient 511 = 432 := by
  rw [show 511 = 7 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 73)]
  rw [totient_cert_7, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_512 : Nat.totient 512 = 256 := by
  rw [show 512 = 2^9 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 9)] <;> norm_num
@[simp] lemma totient_cert_513 : Nat.totient 513 = 324 := by
  rw [show 513 = 27 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 19)]
  rw [totient_cert_27, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_514 : Nat.totient 514 = 256 := by
  rw [show 514 = 2 * 257 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 257)]
  rw [totient_cert_2, totient_cert_257] <;> norm_num
@[simp] lemma totient_cert_515 : Nat.totient 515 = 408 := by
  rw [show 515 = 5 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 103)]
  rw [totient_cert_5, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_516 : Nat.totient 516 = 168 := by
  rw [show 516 = 4 * 129 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 129)]
  rw [totient_cert_4, totient_cert_129] <;> norm_num
@[simp] lemma totient_cert_517 : Nat.totient 517 = 460 := by
  rw [show 517 = 11 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 47)]
  rw [totient_cert_11, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_518 : Nat.totient 518 = 216 := by
  rw [show 518 = 2 * 259 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 259)]
  rw [totient_cert_2, totient_cert_259] <;> norm_num
@[simp] lemma totient_cert_519 : Nat.totient 519 = 344 := by
  rw [show 519 = 3 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 173)]
  rw [totient_cert_3, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_520 : Nat.totient 520 = 192 := by
  rw [show 520 = 8 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 65)]
  rw [totient_cert_8, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_521 : Nat.totient 521 = 520 := by
  rw [show 521 = 521^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 521) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_522 : Nat.totient 522 = 168 := by
  rw [show 522 = 2 * 261 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 261)]
  rw [totient_cert_2, totient_cert_261] <;> norm_num
@[simp] lemma totient_cert_523 : Nat.totient 523 = 522 := by
  rw [show 523 = 523^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 523) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_524 : Nat.totient 524 = 260 := by
  rw [show 524 = 4 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 131)]
  rw [totient_cert_4, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_525 : Nat.totient 525 = 240 := by
  rw [show 525 = 3 * 175 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 175)]
  rw [totient_cert_3, totient_cert_175] <;> norm_num
@[simp] lemma totient_cert_526 : Nat.totient 526 = 262 := by
  rw [show 526 = 2 * 263 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 263)]
  rw [totient_cert_2, totient_cert_263] <;> norm_num
@[simp] lemma totient_cert_527 : Nat.totient 527 = 480 := by
  rw [show 527 = 17 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 31)]
  rw [totient_cert_17, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_528 : Nat.totient 528 = 160 := by
  rw [show 528 = 16 * 33 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 33)]
  rw [totient_cert_16, totient_cert_33] <;> norm_num
@[simp] lemma totient_cert_529 : Nat.totient 529 = 506 := by
  rw [show 529 = 23^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 23) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_530 : Nat.totient 530 = 208 := by
  rw [show 530 = 2 * 265 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 265)]
  rw [totient_cert_2, totient_cert_265] <;> norm_num
@[simp] lemma totient_cert_531 : Nat.totient 531 = 348 := by
  rw [show 531 = 9 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 59)]
  rw [totient_cert_9, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_532 : Nat.totient 532 = 216 := by
  rw [show 532 = 4 * 133 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 133)]
  rw [totient_cert_4, totient_cert_133] <;> norm_num
@[simp] lemma totient_cert_533 : Nat.totient 533 = 480 := by
  rw [show 533 = 13 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 41)]
  rw [totient_cert_13, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_534 : Nat.totient 534 = 176 := by
  rw [show 534 = 2 * 267 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 267)]
  rw [totient_cert_2, totient_cert_267] <;> norm_num
@[simp] lemma totient_cert_535 : Nat.totient 535 = 424 := by
  rw [show 535 = 5 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 107)]
  rw [totient_cert_5, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_536 : Nat.totient 536 = 264 := by
  rw [show 536 = 8 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 67)]
  rw [totient_cert_8, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_537 : Nat.totient 537 = 356 := by
  rw [show 537 = 3 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 179)]
  rw [totient_cert_3, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_538 : Nat.totient 538 = 268 := by
  rw [show 538 = 2 * 269 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 269)]
  rw [totient_cert_2, totient_cert_269] <;> norm_num
@[simp] lemma totient_cert_539 : Nat.totient 539 = 420 := by
  rw [show 539 = 49 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 11)]
  rw [totient_cert_49, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_540 : Nat.totient 540 = 144 := by
  rw [show 540 = 4 * 135 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 135)]
  rw [totient_cert_4, totient_cert_135] <;> norm_num
@[simp] lemma totient_cert_541 : Nat.totient 541 = 540 := by
  rw [show 541 = 541^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 541) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_542 : Nat.totient 542 = 270 := by
  rw [show 542 = 2 * 271 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 271)]
  rw [totient_cert_2, totient_cert_271] <;> norm_num
@[simp] lemma totient_cert_543 : Nat.totient 543 = 360 := by
  rw [show 543 = 3 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 181)]
  rw [totient_cert_3, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_544 : Nat.totient 544 = 256 := by
  rw [show 544 = 32 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 17)]
  rw [totient_cert_32, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_545 : Nat.totient 545 = 432 := by
  rw [show 545 = 5 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 109)]
  rw [totient_cert_5, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_546 : Nat.totient 546 = 144 := by
  rw [show 546 = 2 * 273 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 273)]
  rw [totient_cert_2, totient_cert_273] <;> norm_num
@[simp] lemma totient_cert_547 : Nat.totient 547 = 546 := by
  rw [show 547 = 547^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 547) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_548 : Nat.totient 548 = 272 := by
  rw [show 548 = 4 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 137)]
  rw [totient_cert_4, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_549 : Nat.totient 549 = 360 := by
  rw [show 549 = 9 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 61)]
  rw [totient_cert_9, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_550 : Nat.totient 550 = 200 := by
  rw [show 550 = 2 * 275 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 275)]
  rw [totient_cert_2, totient_cert_275] <;> norm_num
@[simp] lemma totient_cert_551 : Nat.totient 551 = 504 := by
  rw [show 551 = 19 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 29)]
  rw [totient_cert_19, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_552 : Nat.totient 552 = 176 := by
  rw [show 552 = 8 * 69 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 69)]
  rw [totient_cert_8, totient_cert_69] <;> norm_num
@[simp] lemma totient_cert_553 : Nat.totient 553 = 468 := by
  rw [show 553 = 7 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 79)]
  rw [totient_cert_7, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_554 : Nat.totient 554 = 276 := by
  rw [show 554 = 2 * 277 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 277)]
  rw [totient_cert_2, totient_cert_277] <;> norm_num
@[simp] lemma totient_cert_555 : Nat.totient 555 = 288 := by
  rw [show 555 = 3 * 185 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 185)]
  rw [totient_cert_3, totient_cert_185] <;> norm_num
@[simp] lemma totient_cert_556 : Nat.totient 556 = 276 := by
  rw [show 556 = 4 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 139)]
  rw [totient_cert_4, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_557 : Nat.totient 557 = 556 := by
  rw [show 557 = 557^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 557) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_558 : Nat.totient 558 = 180 := by
  rw [show 558 = 2 * 279 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 279)]
  rw [totient_cert_2, totient_cert_279] <;> norm_num
@[simp] lemma totient_cert_559 : Nat.totient 559 = 504 := by
  rw [show 559 = 13 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 43)]
  rw [totient_cert_13, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_560 : Nat.totient 560 = 192 := by
  rw [show 560 = 16 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 35)]
  rw [totient_cert_16, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_561 : Nat.totient 561 = 320 := by
  rw [show 561 = 3 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 187)]
  rw [totient_cert_3, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_562 : Nat.totient 562 = 280 := by
  rw [show 562 = 2 * 281 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 281)]
  rw [totient_cert_2, totient_cert_281] <;> norm_num
@[simp] lemma totient_cert_563 : Nat.totient 563 = 562 := by
  rw [show 563 = 563^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 563) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_564 : Nat.totient 564 = 184 := by
  rw [show 564 = 4 * 141 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 141)]
  rw [totient_cert_4, totient_cert_141] <;> norm_num
@[simp] lemma totient_cert_565 : Nat.totient 565 = 448 := by
  rw [show 565 = 5 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 113)]
  rw [totient_cert_5, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_566 : Nat.totient 566 = 282 := by
  rw [show 566 = 2 * 283 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 283)]
  rw [totient_cert_2, totient_cert_283] <;> norm_num
@[simp] lemma totient_cert_567 : Nat.totient 567 = 324 := by
  rw [show 567 = 81 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 81 7)]
  rw [totient_cert_81, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_568 : Nat.totient 568 = 280 := by
  rw [show 568 = 8 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 71)]
  rw [totient_cert_8, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_569 : Nat.totient 569 = 568 := by
  rw [show 569 = 569^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 569) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_570 : Nat.totient 570 = 144 := by
  rw [show 570 = 2 * 285 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 285)]
  rw [totient_cert_2, totient_cert_285] <;> norm_num
@[simp] lemma totient_cert_571 : Nat.totient 571 = 570 := by
  rw [show 571 = 571^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 571) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_572 : Nat.totient 572 = 240 := by
  rw [show 572 = 4 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 143)]
  rw [totient_cert_4, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_573 : Nat.totient 573 = 380 := by
  rw [show 573 = 3 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 191)]
  rw [totient_cert_3, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_574 : Nat.totient 574 = 240 := by
  rw [show 574 = 2 * 287 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 287)]
  rw [totient_cert_2, totient_cert_287] <;> norm_num
@[simp] lemma totient_cert_575 : Nat.totient 575 = 440 := by
  rw [show 575 = 25 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 23)]
  rw [totient_cert_25, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_576 : Nat.totient 576 = 192 := by
  rw [show 576 = 64 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 9)]
  rw [totient_cert_64, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_577 : Nat.totient 577 = 576 := by
  rw [show 577 = 577^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 577) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_578 : Nat.totient 578 = 272 := by
  rw [show 578 = 2 * 289 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 289)]
  rw [totient_cert_2, totient_cert_289] <;> norm_num
@[simp] lemma totient_cert_579 : Nat.totient 579 = 384 := by
  rw [show 579 = 3 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 193)]
  rw [totient_cert_3, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_580 : Nat.totient 580 = 224 := by
  rw [show 580 = 4 * 145 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 145)]
  rw [totient_cert_4, totient_cert_145] <;> norm_num
@[simp] lemma totient_cert_581 : Nat.totient 581 = 492 := by
  rw [show 581 = 7 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 83)]
  rw [totient_cert_7, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_582 : Nat.totient 582 = 192 := by
  rw [show 582 = 2 * 291 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 291)]
  rw [totient_cert_2, totient_cert_291] <;> norm_num
@[simp] lemma totient_cert_583 : Nat.totient 583 = 520 := by
  rw [show 583 = 11 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 53)]
  rw [totient_cert_11, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_584 : Nat.totient 584 = 288 := by
  rw [show 584 = 8 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 73)]
  rw [totient_cert_8, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_585 : Nat.totient 585 = 288 := by
  rw [show 585 = 9 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 65)]
  rw [totient_cert_9, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_586 : Nat.totient 586 = 292 := by
  rw [show 586 = 2 * 293 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 293)]
  rw [totient_cert_2, totient_cert_293] <;> norm_num
@[simp] lemma totient_cert_587 : Nat.totient 587 = 586 := by
  rw [show 587 = 587^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 587) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_588 : Nat.totient 588 = 168 := by
  rw [show 588 = 4 * 147 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 147)]
  rw [totient_cert_4, totient_cert_147] <;> norm_num
@[simp] lemma totient_cert_589 : Nat.totient 589 = 540 := by
  rw [show 589 = 19 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 31)]
  rw [totient_cert_19, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_590 : Nat.totient 590 = 232 := by
  rw [show 590 = 2 * 295 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 295)]
  rw [totient_cert_2, totient_cert_295] <;> norm_num
@[simp] lemma totient_cert_591 : Nat.totient 591 = 392 := by
  rw [show 591 = 3 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 197)]
  rw [totient_cert_3, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_592 : Nat.totient 592 = 288 := by
  rw [show 592 = 16 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 37)]
  rw [totient_cert_16, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_593 : Nat.totient 593 = 592 := by
  rw [show 593 = 593^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 593) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_594 : Nat.totient 594 = 180 := by
  rw [show 594 = 2 * 297 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 297)]
  rw [totient_cert_2, totient_cert_297] <;> norm_num
@[simp] lemma totient_cert_595 : Nat.totient 595 = 384 := by
  rw [show 595 = 5 * 119 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 119)]
  rw [totient_cert_5, totient_cert_119] <;> norm_num
@[simp] lemma totient_cert_596 : Nat.totient 596 = 296 := by
  rw [show 596 = 4 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 149)]
  rw [totient_cert_4, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_597 : Nat.totient 597 = 396 := by
  rw [show 597 = 3 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 199)]
  rw [totient_cert_3, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_598 : Nat.totient 598 = 264 := by
  rw [show 598 = 2 * 299 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 299)]
  rw [totient_cert_2, totient_cert_299] <;> norm_num
@[simp] lemma totient_cert_599 : Nat.totient 599 = 598 := by
  rw [show 599 = 599^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 599) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_600 : Nat.totient 600 = 160 := by
  rw [show 600 = 8 * 75 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 75)]
  rw [totient_cert_8, totient_cert_75] <;> norm_num
@[simp] lemma totient_cert_601 : Nat.totient 601 = 600 := by
  rw [show 601 = 601^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 601) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_602 : Nat.totient 602 = 252 := by
  rw [show 602 = 2 * 301 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 301)]
  rw [totient_cert_2, totient_cert_301] <;> norm_num
@[simp] lemma totient_cert_603 : Nat.totient 603 = 396 := by
  rw [show 603 = 9 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 67)]
  rw [totient_cert_9, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_604 : Nat.totient 604 = 300 := by
  rw [show 604 = 4 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 151)]
  rw [totient_cert_4, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_605 : Nat.totient 605 = 440 := by
  rw [show 605 = 5 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 121)]
  rw [totient_cert_5, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_606 : Nat.totient 606 = 200 := by
  rw [show 606 = 2 * 303 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 303)]
  rw [totient_cert_2, totient_cert_303] <;> norm_num
@[simp] lemma totient_cert_607 : Nat.totient 607 = 606 := by
  rw [show 607 = 607^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 607) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_608 : Nat.totient 608 = 288 := by
  rw [show 608 = 32 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 19)]
  rw [totient_cert_32, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_609 : Nat.totient 609 = 336 := by
  rw [show 609 = 3 * 203 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 203)]
  rw [totient_cert_3, totient_cert_203] <;> norm_num
@[simp] lemma totient_cert_610 : Nat.totient 610 = 240 := by
  rw [show 610 = 2 * 305 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 305)]
  rw [totient_cert_2, totient_cert_305] <;> norm_num
@[simp] lemma totient_cert_611 : Nat.totient 611 = 552 := by
  rw [show 611 = 13 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 47)]
  rw [totient_cert_13, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_612 : Nat.totient 612 = 192 := by
  rw [show 612 = 4 * 153 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 153)]
  rw [totient_cert_4, totient_cert_153] <;> norm_num
@[simp] lemma totient_cert_613 : Nat.totient 613 = 612 := by
  rw [show 613 = 613^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 613) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_614 : Nat.totient 614 = 306 := by
  rw [show 614 = 2 * 307 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 307)]
  rw [totient_cert_2, totient_cert_307] <;> norm_num
@[simp] lemma totient_cert_615 : Nat.totient 615 = 320 := by
  rw [show 615 = 3 * 205 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 205)]
  rw [totient_cert_3, totient_cert_205] <;> norm_num
@[simp] lemma totient_cert_616 : Nat.totient 616 = 240 := by
  rw [show 616 = 8 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 77)]
  rw [totient_cert_8, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_617 : Nat.totient 617 = 616 := by
  rw [show 617 = 617^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 617) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_618 : Nat.totient 618 = 204 := by
  rw [show 618 = 2 * 309 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 309)]
  rw [totient_cert_2, totient_cert_309] <;> norm_num
@[simp] lemma totient_cert_619 : Nat.totient 619 = 618 := by
  rw [show 619 = 619^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 619) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_620 : Nat.totient 620 = 240 := by
  rw [show 620 = 4 * 155 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 155)]
  rw [totient_cert_4, totient_cert_155] <;> norm_num
@[simp] lemma totient_cert_621 : Nat.totient 621 = 396 := by
  rw [show 621 = 27 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 23)]
  rw [totient_cert_27, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_622 : Nat.totient 622 = 310 := by
  rw [show 622 = 2 * 311 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 311)]
  rw [totient_cert_2, totient_cert_311] <;> norm_num
@[simp] lemma totient_cert_623 : Nat.totient 623 = 528 := by
  rw [show 623 = 7 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 89)]
  rw [totient_cert_7, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_624 : Nat.totient 624 = 192 := by
  rw [show 624 = 16 * 39 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 39)]
  rw [totient_cert_16, totient_cert_39] <;> norm_num
@[simp] lemma totient_cert_625 : Nat.totient 625 = 500 := by
  rw [show 625 = 5^4 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by norm_num : 0 < 4)] <;> norm_num
@[simp] lemma totient_cert_626 : Nat.totient 626 = 312 := by
  rw [show 626 = 2 * 313 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 313)]
  rw [totient_cert_2, totient_cert_313] <;> norm_num
@[simp] lemma totient_cert_627 : Nat.totient 627 = 360 := by
  rw [show 627 = 3 * 209 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 209)]
  rw [totient_cert_3, totient_cert_209] <;> norm_num
@[simp] lemma totient_cert_628 : Nat.totient 628 = 312 := by
  rw [show 628 = 4 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 157)]
  rw [totient_cert_4, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_629 : Nat.totient 629 = 576 := by
  rw [show 629 = 17 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 37)]
  rw [totient_cert_17, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_630 : Nat.totient 630 = 144 := by
  rw [show 630 = 2 * 315 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 315)]
  rw [totient_cert_2, totient_cert_315] <;> norm_num
@[simp] lemma totient_cert_631 : Nat.totient 631 = 630 := by
  rw [show 631 = 631^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 631) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_632 : Nat.totient 632 = 312 := by
  rw [show 632 = 8 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 79)]
  rw [totient_cert_8, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_633 : Nat.totient 633 = 420 := by
  rw [show 633 = 3 * 211 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 211)]
  rw [totient_cert_3, totient_cert_211] <;> norm_num
@[simp] lemma totient_cert_634 : Nat.totient 634 = 316 := by
  rw [show 634 = 2 * 317 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 317)]
  rw [totient_cert_2, totient_cert_317] <;> norm_num
@[simp] lemma totient_cert_635 : Nat.totient 635 = 504 := by
  rw [show 635 = 5 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 127)]
  rw [totient_cert_5, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_636 : Nat.totient 636 = 208 := by
  rw [show 636 = 4 * 159 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 159)]
  rw [totient_cert_4, totient_cert_159] <;> norm_num
@[simp] lemma totient_cert_637 : Nat.totient 637 = 504 := by
  rw [show 637 = 49 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 13)]
  rw [totient_cert_49, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_638 : Nat.totient 638 = 280 := by
  rw [show 638 = 2 * 319 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 319)]
  rw [totient_cert_2, totient_cert_319] <;> norm_num
@[simp] lemma totient_cert_639 : Nat.totient 639 = 420 := by
  rw [show 639 = 9 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 71)]
  rw [totient_cert_9, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_640 : Nat.totient 640 = 256 := by
  rw [show 640 = 128 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 128 5)]
  rw [totient_cert_128, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_641 : Nat.totient 641 = 640 := by
  rw [show 641 = 641^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 641) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_642 : Nat.totient 642 = 212 := by
  rw [show 642 = 2 * 321 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 321)]
  rw [totient_cert_2, totient_cert_321] <;> norm_num
@[simp] lemma totient_cert_643 : Nat.totient 643 = 642 := by
  rw [show 643 = 643^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 643) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_644 : Nat.totient 644 = 264 := by
  rw [show 644 = 4 * 161 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 161)]
  rw [totient_cert_4, totient_cert_161] <;> norm_num
@[simp] lemma totient_cert_645 : Nat.totient 645 = 336 := by
  rw [show 645 = 3 * 215 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 215)]
  rw [totient_cert_3, totient_cert_215] <;> norm_num
@[simp] lemma totient_cert_646 : Nat.totient 646 = 288 := by
  rw [show 646 = 2 * 323 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 323)]
  rw [totient_cert_2, totient_cert_323] <;> norm_num
@[simp] lemma totient_cert_647 : Nat.totient 647 = 646 := by
  rw [show 647 = 647^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 647) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_648 : Nat.totient 648 = 216 := by
  rw [show 648 = 8 * 81 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 81)]
  rw [totient_cert_8, totient_cert_81] <;> norm_num
@[simp] lemma totient_cert_649 : Nat.totient 649 = 580 := by
  rw [show 649 = 11 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 59)]
  rw [totient_cert_11, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_650 : Nat.totient 650 = 240 := by
  rw [show 650 = 2 * 325 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 325)]
  rw [totient_cert_2, totient_cert_325] <;> norm_num
@[simp] lemma totient_cert_651 : Nat.totient 651 = 360 := by
  rw [show 651 = 3 * 217 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 217)]
  rw [totient_cert_3, totient_cert_217] <;> norm_num
@[simp] lemma totient_cert_652 : Nat.totient 652 = 324 := by
  rw [show 652 = 4 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 163)]
  rw [totient_cert_4, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_653 : Nat.totient 653 = 652 := by
  rw [show 653 = 653^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 653) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_654 : Nat.totient 654 = 216 := by
  rw [show 654 = 2 * 327 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 327)]
  rw [totient_cert_2, totient_cert_327] <;> norm_num
@[simp] lemma totient_cert_655 : Nat.totient 655 = 520 := by
  rw [show 655 = 5 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 131)]
  rw [totient_cert_5, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_656 : Nat.totient 656 = 320 := by
  rw [show 656 = 16 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 41)]
  rw [totient_cert_16, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_657 : Nat.totient 657 = 432 := by
  rw [show 657 = 9 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 73)]
  rw [totient_cert_9, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_658 : Nat.totient 658 = 276 := by
  rw [show 658 = 2 * 329 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 329)]
  rw [totient_cert_2, totient_cert_329] <;> norm_num
@[simp] lemma totient_cert_659 : Nat.totient 659 = 658 := by
  rw [show 659 = 659^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 659) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_660 : Nat.totient 660 = 160 := by
  rw [show 660 = 4 * 165 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 165)]
  rw [totient_cert_4, totient_cert_165] <;> norm_num
@[simp] lemma totient_cert_661 : Nat.totient 661 = 660 := by
  rw [show 661 = 661^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 661) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_662 : Nat.totient 662 = 330 := by
  rw [show 662 = 2 * 331 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 331)]
  rw [totient_cert_2, totient_cert_331] <;> norm_num
@[simp] lemma totient_cert_663 : Nat.totient 663 = 384 := by
  rw [show 663 = 3 * 221 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 221)]
  rw [totient_cert_3, totient_cert_221] <;> norm_num
@[simp] lemma totient_cert_664 : Nat.totient 664 = 328 := by
  rw [show 664 = 8 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 83)]
  rw [totient_cert_8, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_665 : Nat.totient 665 = 432 := by
  rw [show 665 = 5 * 133 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 133)]
  rw [totient_cert_5, totient_cert_133] <;> norm_num
@[simp] lemma totient_cert_666 : Nat.totient 666 = 216 := by
  rw [show 666 = 2 * 333 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 333)]
  rw [totient_cert_2, totient_cert_333] <;> norm_num
@[simp] lemma totient_cert_667 : Nat.totient 667 = 616 := by
  rw [show 667 = 23 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 29)]
  rw [totient_cert_23, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_668 : Nat.totient 668 = 332 := by
  rw [show 668 = 4 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 167)]
  rw [totient_cert_4, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_669 : Nat.totient 669 = 444 := by
  rw [show 669 = 3 * 223 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 223)]
  rw [totient_cert_3, totient_cert_223] <;> norm_num
@[simp] lemma totient_cert_670 : Nat.totient 670 = 264 := by
  rw [show 670 = 2 * 335 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 335)]
  rw [totient_cert_2, totient_cert_335] <;> norm_num
@[simp] lemma totient_cert_671 : Nat.totient 671 = 600 := by
  rw [show 671 = 11 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 61)]
  rw [totient_cert_11, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_672 : Nat.totient 672 = 192 := by
  rw [show 672 = 32 * 21 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 21)]
  rw [totient_cert_32, totient_cert_21] <;> norm_num
@[simp] lemma totient_cert_673 : Nat.totient 673 = 672 := by
  rw [show 673 = 673^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 673) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_674 : Nat.totient 674 = 336 := by
  rw [show 674 = 2 * 337 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 337)]
  rw [totient_cert_2, totient_cert_337] <;> norm_num
@[simp] lemma totient_cert_675 : Nat.totient 675 = 360 := by
  rw [show 675 = 27 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 25)]
  rw [totient_cert_27, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_676 : Nat.totient 676 = 312 := by
  rw [show 676 = 4 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 169)]
  rw [totient_cert_4, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_677 : Nat.totient 677 = 676 := by
  rw [show 677 = 677^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 677) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_678 : Nat.totient 678 = 224 := by
  rw [show 678 = 2 * 339 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 339)]
  rw [totient_cert_2, totient_cert_339] <;> norm_num
@[simp] lemma totient_cert_679 : Nat.totient 679 = 576 := by
  rw [show 679 = 7 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 97)]
  rw [totient_cert_7, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_680 : Nat.totient 680 = 256 := by
  rw [show 680 = 8 * 85 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 85)]
  rw [totient_cert_8, totient_cert_85] <;> norm_num
@[simp] lemma totient_cert_681 : Nat.totient 681 = 452 := by
  rw [show 681 = 3 * 227 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 227)]
  rw [totient_cert_3, totient_cert_227] <;> norm_num
@[simp] lemma totient_cert_682 : Nat.totient 682 = 300 := by
  rw [show 682 = 2 * 341 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 341)]
  rw [totient_cert_2, totient_cert_341] <;> norm_num
@[simp] lemma totient_cert_683 : Nat.totient 683 = 682 := by
  rw [show 683 = 683^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 683) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_684 : Nat.totient 684 = 216 := by
  rw [show 684 = 4 * 171 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 171)]
  rw [totient_cert_4, totient_cert_171] <;> norm_num
@[simp] lemma totient_cert_685 : Nat.totient 685 = 544 := by
  rw [show 685 = 5 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 137)]
  rw [totient_cert_5, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_686 : Nat.totient 686 = 294 := by
  rw [show 686 = 2 * 343 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 343)]
  rw [totient_cert_2, totient_cert_343] <;> norm_num
@[simp] lemma totient_cert_687 : Nat.totient 687 = 456 := by
  rw [show 687 = 3 * 229 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 229)]
  rw [totient_cert_3, totient_cert_229] <;> norm_num
@[simp] lemma totient_cert_688 : Nat.totient 688 = 336 := by
  rw [show 688 = 16 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 43)]
  rw [totient_cert_16, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_689 : Nat.totient 689 = 624 := by
  rw [show 689 = 13 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 53)]
  rw [totient_cert_13, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_690 : Nat.totient 690 = 176 := by
  rw [show 690 = 2 * 345 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 345)]
  rw [totient_cert_2, totient_cert_345] <;> norm_num
@[simp] lemma totient_cert_691 : Nat.totient 691 = 690 := by
  rw [show 691 = 691^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 691) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_692 : Nat.totient 692 = 344 := by
  rw [show 692 = 4 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 173)]
  rw [totient_cert_4, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_693 : Nat.totient 693 = 360 := by
  rw [show 693 = 9 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 77)]
  rw [totient_cert_9, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_694 : Nat.totient 694 = 346 := by
  rw [show 694 = 2 * 347 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 347)]
  rw [totient_cert_2, totient_cert_347] <;> norm_num
@[simp] lemma totient_cert_695 : Nat.totient 695 = 552 := by
  rw [show 695 = 5 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 139)]
  rw [totient_cert_5, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_696 : Nat.totient 696 = 224 := by
  rw [show 696 = 8 * 87 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 87)]
  rw [totient_cert_8, totient_cert_87] <;> norm_num
@[simp] lemma totient_cert_697 : Nat.totient 697 = 640 := by
  rw [show 697 = 17 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 41)]
  rw [totient_cert_17, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_698 : Nat.totient 698 = 348 := by
  rw [show 698 = 2 * 349 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 349)]
  rw [totient_cert_2, totient_cert_349] <;> norm_num
@[simp] lemma totient_cert_699 : Nat.totient 699 = 464 := by
  rw [show 699 = 3 * 233 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 233)]
  rw [totient_cert_3, totient_cert_233] <;> norm_num
@[simp] lemma totient_cert_700 : Nat.totient 700 = 240 := by
  rw [show 700 = 4 * 175 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 175)]
  rw [totient_cert_4, totient_cert_175] <;> norm_num
@[simp] lemma totient_cert_701 : Nat.totient 701 = 700 := by
  rw [show 701 = 701^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 701) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_702 : Nat.totient 702 = 216 := by
  rw [show 702 = 2 * 351 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 351)]
  rw [totient_cert_2, totient_cert_351] <;> norm_num
@[simp] lemma totient_cert_703 : Nat.totient 703 = 648 := by
  rw [show 703 = 19 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 37)]
  rw [totient_cert_19, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_704 : Nat.totient 704 = 320 := by
  rw [show 704 = 64 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 11)]
  rw [totient_cert_64, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_705 : Nat.totient 705 = 368 := by
  rw [show 705 = 3 * 235 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 235)]
  rw [totient_cert_3, totient_cert_235] <;> norm_num
@[simp] lemma totient_cert_706 : Nat.totient 706 = 352 := by
  rw [show 706 = 2 * 353 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 353)]
  rw [totient_cert_2, totient_cert_353] <;> norm_num
@[simp] lemma totient_cert_707 : Nat.totient 707 = 600 := by
  rw [show 707 = 7 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 101)]
  rw [totient_cert_7, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_708 : Nat.totient 708 = 232 := by
  rw [show 708 = 4 * 177 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 177)]
  rw [totient_cert_4, totient_cert_177] <;> norm_num
@[simp] lemma totient_cert_709 : Nat.totient 709 = 708 := by
  rw [show 709 = 709^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 709) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_710 : Nat.totient 710 = 280 := by
  rw [show 710 = 2 * 355 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 355)]
  rw [totient_cert_2, totient_cert_355] <;> norm_num
@[simp] lemma totient_cert_711 : Nat.totient 711 = 468 := by
  rw [show 711 = 9 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 79)]
  rw [totient_cert_9, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_712 : Nat.totient 712 = 352 := by
  rw [show 712 = 8 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 89)]
  rw [totient_cert_8, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_713 : Nat.totient 713 = 660 := by
  rw [show 713 = 23 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 31)]
  rw [totient_cert_23, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_714 : Nat.totient 714 = 192 := by
  rw [show 714 = 2 * 357 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 357)]
  rw [totient_cert_2, totient_cert_357] <;> norm_num
@[simp] lemma totient_cert_715 : Nat.totient 715 = 480 := by
  rw [show 715 = 5 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 143)]
  rw [totient_cert_5, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_716 : Nat.totient 716 = 356 := by
  rw [show 716 = 4 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 179)]
  rw [totient_cert_4, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_717 : Nat.totient 717 = 476 := by
  rw [show 717 = 3 * 239 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 239)]
  rw [totient_cert_3, totient_cert_239] <;> norm_num
@[simp] lemma totient_cert_718 : Nat.totient 718 = 358 := by
  rw [show 718 = 2 * 359 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 359)]
  rw [totient_cert_2, totient_cert_359] <;> norm_num
@[simp] lemma totient_cert_719 : Nat.totient 719 = 718 := by
  rw [show 719 = 719^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 719) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_720 : Nat.totient 720 = 192 := by
  rw [show 720 = 16 * 45 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 45)]
  rw [totient_cert_16, totient_cert_45] <;> norm_num
@[simp] lemma totient_cert_721 : Nat.totient 721 = 612 := by
  rw [show 721 = 7 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 103)]
  rw [totient_cert_7, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_722 : Nat.totient 722 = 342 := by
  rw [show 722 = 2 * 361 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 361)]
  rw [totient_cert_2, totient_cert_361] <;> norm_num
@[simp] lemma totient_cert_723 : Nat.totient 723 = 480 := by
  rw [show 723 = 3 * 241 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 241)]
  rw [totient_cert_3, totient_cert_241] <;> norm_num
@[simp] lemma totient_cert_724 : Nat.totient 724 = 360 := by
  rw [show 724 = 4 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 181)]
  rw [totient_cert_4, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_725 : Nat.totient 725 = 560 := by
  rw [show 725 = 25 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 29)]
  rw [totient_cert_25, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_726 : Nat.totient 726 = 220 := by
  rw [show 726 = 2 * 363 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 363)]
  rw [totient_cert_2, totient_cert_363] <;> norm_num
@[simp] lemma totient_cert_727 : Nat.totient 727 = 726 := by
  rw [show 727 = 727^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 727) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_728 : Nat.totient 728 = 288 := by
  rw [show 728 = 8 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 91)]
  rw [totient_cert_8, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_729 : Nat.totient 729 = 486 := by
  rw [show 729 = 3^6 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) (by norm_num : 0 < 6)] <;> norm_num
@[simp] lemma totient_cert_730 : Nat.totient 730 = 288 := by
  rw [show 730 = 2 * 365 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 365)]
  rw [totient_cert_2, totient_cert_365] <;> norm_num
@[simp] lemma totient_cert_731 : Nat.totient 731 = 672 := by
  rw [show 731 = 17 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 43)]
  rw [totient_cert_17, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_732 : Nat.totient 732 = 240 := by
  rw [show 732 = 4 * 183 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 183)]
  rw [totient_cert_4, totient_cert_183] <;> norm_num
@[simp] lemma totient_cert_733 : Nat.totient 733 = 732 := by
  rw [show 733 = 733^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 733) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_734 : Nat.totient 734 = 366 := by
  rw [show 734 = 2 * 367 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 367)]
  rw [totient_cert_2, totient_cert_367] <;> norm_num
@[simp] lemma totient_cert_735 : Nat.totient 735 = 336 := by
  rw [show 735 = 3 * 245 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 245)]
  rw [totient_cert_3, totient_cert_245] <;> norm_num
@[simp] lemma totient_cert_736 : Nat.totient 736 = 352 := by
  rw [show 736 = 32 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 23)]
  rw [totient_cert_32, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_737 : Nat.totient 737 = 660 := by
  rw [show 737 = 11 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 67)]
  rw [totient_cert_11, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_738 : Nat.totient 738 = 240 := by
  rw [show 738 = 2 * 369 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 369)]
  rw [totient_cert_2, totient_cert_369] <;> norm_num
@[simp] lemma totient_cert_739 : Nat.totient 739 = 738 := by
  rw [show 739 = 739^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 739) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_740 : Nat.totient 740 = 288 := by
  rw [show 740 = 4 * 185 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 185)]
  rw [totient_cert_4, totient_cert_185] <;> norm_num
@[simp] lemma totient_cert_741 : Nat.totient 741 = 432 := by
  rw [show 741 = 3 * 247 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 247)]
  rw [totient_cert_3, totient_cert_247] <;> norm_num
@[simp] lemma totient_cert_742 : Nat.totient 742 = 312 := by
  rw [show 742 = 2 * 371 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 371)]
  rw [totient_cert_2, totient_cert_371] <;> norm_num
@[simp] lemma totient_cert_743 : Nat.totient 743 = 742 := by
  rw [show 743 = 743^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 743) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_744 : Nat.totient 744 = 240 := by
  rw [show 744 = 8 * 93 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 93)]
  rw [totient_cert_8, totient_cert_93] <;> norm_num
@[simp] lemma totient_cert_745 : Nat.totient 745 = 592 := by
  rw [show 745 = 5 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 149)]
  rw [totient_cert_5, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_746 : Nat.totient 746 = 372 := by
  rw [show 746 = 2 * 373 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 373)]
  rw [totient_cert_2, totient_cert_373] <;> norm_num
@[simp] lemma totient_cert_747 : Nat.totient 747 = 492 := by
  rw [show 747 = 9 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 83)]
  rw [totient_cert_9, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_748 : Nat.totient 748 = 320 := by
  rw [show 748 = 4 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 187)]
  rw [totient_cert_4, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_749 : Nat.totient 749 = 636 := by
  rw [show 749 = 7 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 107)]
  rw [totient_cert_7, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_750 : Nat.totient 750 = 200 := by
  rw [show 750 = 2 * 375 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 375)]
  rw [totient_cert_2, totient_cert_375] <;> norm_num
@[simp] lemma totient_cert_751 : Nat.totient 751 = 750 := by
  rw [show 751 = 751^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 751) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_752 : Nat.totient 752 = 368 := by
  rw [show 752 = 16 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 47)]
  rw [totient_cert_16, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_753 : Nat.totient 753 = 500 := by
  rw [show 753 = 3 * 251 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 251)]
  rw [totient_cert_3, totient_cert_251] <;> norm_num
@[simp] lemma totient_cert_754 : Nat.totient 754 = 336 := by
  rw [show 754 = 2 * 377 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 377)]
  rw [totient_cert_2, totient_cert_377] <;> norm_num
@[simp] lemma totient_cert_755 : Nat.totient 755 = 600 := by
  rw [show 755 = 5 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 151)]
  rw [totient_cert_5, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_756 : Nat.totient 756 = 216 := by
  rw [show 756 = 4 * 189 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 189)]
  rw [totient_cert_4, totient_cert_189] <;> norm_num
@[simp] lemma totient_cert_757 : Nat.totient 757 = 756 := by
  rw [show 757 = 757^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 757) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_758 : Nat.totient 758 = 378 := by
  rw [show 758 = 2 * 379 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 379)]
  rw [totient_cert_2, totient_cert_379] <;> norm_num
@[simp] lemma totient_cert_759 : Nat.totient 759 = 440 := by
  rw [show 759 = 3 * 253 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 253)]
  rw [totient_cert_3, totient_cert_253] <;> norm_num
@[simp] lemma totient_cert_760 : Nat.totient 760 = 288 := by
  rw [show 760 = 8 * 95 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 95)]
  rw [totient_cert_8, totient_cert_95] <;> norm_num
@[simp] lemma totient_cert_761 : Nat.totient 761 = 760 := by
  rw [show 761 = 761^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 761) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_762 : Nat.totient 762 = 252 := by
  rw [show 762 = 2 * 381 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 381)]
  rw [totient_cert_2, totient_cert_381] <;> norm_num
@[simp] lemma totient_cert_763 : Nat.totient 763 = 648 := by
  rw [show 763 = 7 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 109)]
  rw [totient_cert_7, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_764 : Nat.totient 764 = 380 := by
  rw [show 764 = 4 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 191)]
  rw [totient_cert_4, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_765 : Nat.totient 765 = 384 := by
  rw [show 765 = 9 * 85 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 85)]
  rw [totient_cert_9, totient_cert_85] <;> norm_num
@[simp] lemma totient_cert_766 : Nat.totient 766 = 382 := by
  rw [show 766 = 2 * 383 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 383)]
  rw [totient_cert_2, totient_cert_383] <;> norm_num
@[simp] lemma totient_cert_767 : Nat.totient 767 = 696 := by
  rw [show 767 = 13 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 59)]
  rw [totient_cert_13, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_768 : Nat.totient 768 = 256 := by
  rw [show 768 = 256 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 256 3)]
  rw [totient_cert_256, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_769 : Nat.totient 769 = 768 := by
  rw [show 769 = 769^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 769) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_770 : Nat.totient 770 = 240 := by
  rw [show 770 = 2 * 385 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 385)]
  rw [totient_cert_2, totient_cert_385] <;> norm_num
@[simp] lemma totient_cert_771 : Nat.totient 771 = 512 := by
  rw [show 771 = 3 * 257 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 257)]
  rw [totient_cert_3, totient_cert_257] <;> norm_num
@[simp] lemma totient_cert_772 : Nat.totient 772 = 384 := by
  rw [show 772 = 4 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 193)]
  rw [totient_cert_4, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_773 : Nat.totient 773 = 772 := by
  rw [show 773 = 773^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 773) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_774 : Nat.totient 774 = 252 := by
  rw [show 774 = 2 * 387 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 387)]
  rw [totient_cert_2, totient_cert_387] <;> norm_num
@[simp] lemma totient_cert_775 : Nat.totient 775 = 600 := by
  rw [show 775 = 25 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 31)]
  rw [totient_cert_25, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_776 : Nat.totient 776 = 384 := by
  rw [show 776 = 8 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 97)]
  rw [totient_cert_8, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_777 : Nat.totient 777 = 432 := by
  rw [show 777 = 3 * 259 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 259)]
  rw [totient_cert_3, totient_cert_259] <;> norm_num
@[simp] lemma totient_cert_778 : Nat.totient 778 = 388 := by
  rw [show 778 = 2 * 389 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 389)]
  rw [totient_cert_2, totient_cert_389] <;> norm_num
@[simp] lemma totient_cert_779 : Nat.totient 779 = 720 := by
  rw [show 779 = 19 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 41)]
  rw [totient_cert_19, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_780 : Nat.totient 780 = 192 := by
  rw [show 780 = 4 * 195 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 195)]
  rw [totient_cert_4, totient_cert_195] <;> norm_num
@[simp] lemma totient_cert_781 : Nat.totient 781 = 700 := by
  rw [show 781 = 11 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 71)]
  rw [totient_cert_11, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_782 : Nat.totient 782 = 352 := by
  rw [show 782 = 2 * 391 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 391)]
  rw [totient_cert_2, totient_cert_391] <;> norm_num
@[simp] lemma totient_cert_783 : Nat.totient 783 = 504 := by
  rw [show 783 = 27 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 29)]
  rw [totient_cert_27, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_784 : Nat.totient 784 = 336 := by
  rw [show 784 = 16 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 49)]
  rw [totient_cert_16, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_785 : Nat.totient 785 = 624 := by
  rw [show 785 = 5 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 157)]
  rw [totient_cert_5, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_786 : Nat.totient 786 = 260 := by
  rw [show 786 = 2 * 393 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 393)]
  rw [totient_cert_2, totient_cert_393] <;> norm_num
@[simp] lemma totient_cert_787 : Nat.totient 787 = 786 := by
  rw [show 787 = 787^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 787) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_788 : Nat.totient 788 = 392 := by
  rw [show 788 = 4 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 197)]
  rw [totient_cert_4, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_789 : Nat.totient 789 = 524 := by
  rw [show 789 = 3 * 263 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 263)]
  rw [totient_cert_3, totient_cert_263] <;> norm_num
@[simp] lemma totient_cert_790 : Nat.totient 790 = 312 := by
  rw [show 790 = 2 * 395 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 395)]
  rw [totient_cert_2, totient_cert_395] <;> norm_num
@[simp] lemma totient_cert_791 : Nat.totient 791 = 672 := by
  rw [show 791 = 7 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 113)]
  rw [totient_cert_7, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_792 : Nat.totient 792 = 240 := by
  rw [show 792 = 8 * 99 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 99)]
  rw [totient_cert_8, totient_cert_99] <;> norm_num
@[simp] lemma totient_cert_793 : Nat.totient 793 = 720 := by
  rw [show 793 = 13 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 61)]
  rw [totient_cert_13, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_794 : Nat.totient 794 = 396 := by
  rw [show 794 = 2 * 397 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 397)]
  rw [totient_cert_2, totient_cert_397] <;> norm_num
@[simp] lemma totient_cert_795 : Nat.totient 795 = 416 := by
  rw [show 795 = 3 * 265 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 265)]
  rw [totient_cert_3, totient_cert_265] <;> norm_num
@[simp] lemma totient_cert_796 : Nat.totient 796 = 396 := by
  rw [show 796 = 4 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 199)]
  rw [totient_cert_4, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_797 : Nat.totient 797 = 796 := by
  rw [show 797 = 797^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 797) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_798 : Nat.totient 798 = 216 := by
  rw [show 798 = 2 * 399 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 399)]
  rw [totient_cert_2, totient_cert_399] <;> norm_num
@[simp] lemma totient_cert_799 : Nat.totient 799 = 736 := by
  rw [show 799 = 17 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 47)]
  rw [totient_cert_17, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_800 : Nat.totient 800 = 320 := by
  rw [show 800 = 32 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 25)]
  rw [totient_cert_32, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_801 : Nat.totient 801 = 528 := by
  rw [show 801 = 9 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 89)]
  rw [totient_cert_9, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_802 : Nat.totient 802 = 400 := by
  rw [show 802 = 2 * 401 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 401)]
  rw [totient_cert_2, totient_cert_401] <;> norm_num
@[simp] lemma totient_cert_803 : Nat.totient 803 = 720 := by
  rw [show 803 = 11 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 73)]
  rw [totient_cert_11, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_804 : Nat.totient 804 = 264 := by
  rw [show 804 = 4 * 201 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 201)]
  rw [totient_cert_4, totient_cert_201] <;> norm_num
@[simp] lemma totient_cert_805 : Nat.totient 805 = 528 := by
  rw [show 805 = 5 * 161 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 161)]
  rw [totient_cert_5, totient_cert_161] <;> norm_num
@[simp] lemma totient_cert_806 : Nat.totient 806 = 360 := by
  rw [show 806 = 2 * 403 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 403)]
  rw [totient_cert_2, totient_cert_403] <;> norm_num
@[simp] lemma totient_cert_807 : Nat.totient 807 = 536 := by
  rw [show 807 = 3 * 269 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 269)]
  rw [totient_cert_3, totient_cert_269] <;> norm_num
@[simp] lemma totient_cert_808 : Nat.totient 808 = 400 := by
  rw [show 808 = 8 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 101)]
  rw [totient_cert_8, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_809 : Nat.totient 809 = 808 := by
  rw [show 809 = 809^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 809) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_810 : Nat.totient 810 = 216 := by
  rw [show 810 = 2 * 405 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 405)]
  rw [totient_cert_2, totient_cert_405] <;> norm_num
@[simp] lemma totient_cert_811 : Nat.totient 811 = 810 := by
  rw [show 811 = 811^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 811) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_812 : Nat.totient 812 = 336 := by
  rw [show 812 = 4 * 203 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 203)]
  rw [totient_cert_4, totient_cert_203] <;> norm_num
@[simp] lemma totient_cert_813 : Nat.totient 813 = 540 := by
  rw [show 813 = 3 * 271 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 271)]
  rw [totient_cert_3, totient_cert_271] <;> norm_num
@[simp] lemma totient_cert_814 : Nat.totient 814 = 360 := by
  rw [show 814 = 2 * 407 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 407)]
  rw [totient_cert_2, totient_cert_407] <;> norm_num
@[simp] lemma totient_cert_815 : Nat.totient 815 = 648 := by
  rw [show 815 = 5 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 163)]
  rw [totient_cert_5, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_816 : Nat.totient 816 = 256 := by
  rw [show 816 = 16 * 51 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 51)]
  rw [totient_cert_16, totient_cert_51] <;> norm_num
@[simp] lemma totient_cert_817 : Nat.totient 817 = 756 := by
  rw [show 817 = 19 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 43)]
  rw [totient_cert_19, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_818 : Nat.totient 818 = 408 := by
  rw [show 818 = 2 * 409 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 409)]
  rw [totient_cert_2, totient_cert_409] <;> norm_num
@[simp] lemma totient_cert_819 : Nat.totient 819 = 432 := by
  rw [show 819 = 9 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 91)]
  rw [totient_cert_9, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_820 : Nat.totient 820 = 320 := by
  rw [show 820 = 4 * 205 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 205)]
  rw [totient_cert_4, totient_cert_205] <;> norm_num
@[simp] lemma totient_cert_821 : Nat.totient 821 = 820 := by
  rw [show 821 = 821^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 821) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_822 : Nat.totient 822 = 272 := by
  rw [show 822 = 2 * 411 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 411)]
  rw [totient_cert_2, totient_cert_411] <;> norm_num
@[simp] lemma totient_cert_823 : Nat.totient 823 = 822 := by
  rw [show 823 = 823^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 823) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_824 : Nat.totient 824 = 408 := by
  rw [show 824 = 8 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 103)]
  rw [totient_cert_8, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_825 : Nat.totient 825 = 400 := by
  rw [show 825 = 3 * 275 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 275)]
  rw [totient_cert_3, totient_cert_275] <;> norm_num
@[simp] lemma totient_cert_826 : Nat.totient 826 = 348 := by
  rw [show 826 = 2 * 413 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 413)]
  rw [totient_cert_2, totient_cert_413] <;> norm_num
@[simp] lemma totient_cert_827 : Nat.totient 827 = 826 := by
  rw [show 827 = 827^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 827) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_828 : Nat.totient 828 = 264 := by
  rw [show 828 = 4 * 207 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 207)]
  rw [totient_cert_4, totient_cert_207] <;> norm_num
@[simp] lemma totient_cert_829 : Nat.totient 829 = 828 := by
  rw [show 829 = 829^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 829) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_830 : Nat.totient 830 = 328 := by
  rw [show 830 = 2 * 415 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 415)]
  rw [totient_cert_2, totient_cert_415] <;> norm_num
@[simp] lemma totient_cert_831 : Nat.totient 831 = 552 := by
  rw [show 831 = 3 * 277 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 277)]
  rw [totient_cert_3, totient_cert_277] <;> norm_num
@[simp] lemma totient_cert_832 : Nat.totient 832 = 384 := by
  rw [show 832 = 64 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 13)]
  rw [totient_cert_64, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_833 : Nat.totient 833 = 672 := by
  rw [show 833 = 49 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 17)]
  rw [totient_cert_49, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_834 : Nat.totient 834 = 276 := by
  rw [show 834 = 2 * 417 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 417)]
  rw [totient_cert_2, totient_cert_417] <;> norm_num
@[simp] lemma totient_cert_835 : Nat.totient 835 = 664 := by
  rw [show 835 = 5 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 167)]
  rw [totient_cert_5, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_836 : Nat.totient 836 = 360 := by
  rw [show 836 = 4 * 209 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 209)]
  rw [totient_cert_4, totient_cert_209] <;> norm_num
@[simp] lemma totient_cert_837 : Nat.totient 837 = 540 := by
  rw [show 837 = 27 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 31)]
  rw [totient_cert_27, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_838 : Nat.totient 838 = 418 := by
  rw [show 838 = 2 * 419 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 419)]
  rw [totient_cert_2, totient_cert_419] <;> norm_num
@[simp] lemma totient_cert_839 : Nat.totient 839 = 838 := by
  rw [show 839 = 839^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 839) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_840 : Nat.totient 840 = 192 := by
  rw [show 840 = 8 * 105 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 105)]
  rw [totient_cert_8, totient_cert_105] <;> norm_num
@[simp] lemma totient_cert_841 : Nat.totient 841 = 812 := by
  rw [show 841 = 29^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 29) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_842 : Nat.totient 842 = 420 := by
  rw [show 842 = 2 * 421 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 421)]
  rw [totient_cert_2, totient_cert_421] <;> norm_num
@[simp] lemma totient_cert_843 : Nat.totient 843 = 560 := by
  rw [show 843 = 3 * 281 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 281)]
  rw [totient_cert_3, totient_cert_281] <;> norm_num
@[simp] lemma totient_cert_844 : Nat.totient 844 = 420 := by
  rw [show 844 = 4 * 211 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 211)]
  rw [totient_cert_4, totient_cert_211] <;> norm_num
@[simp] lemma totient_cert_845 : Nat.totient 845 = 624 := by
  rw [show 845 = 5 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 169)]
  rw [totient_cert_5, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_846 : Nat.totient 846 = 276 := by
  rw [show 846 = 2 * 423 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 423)]
  rw [totient_cert_2, totient_cert_423] <;> norm_num
@[simp] lemma totient_cert_847 : Nat.totient 847 = 660 := by
  rw [show 847 = 7 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 121)]
  rw [totient_cert_7, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_848 : Nat.totient 848 = 416 := by
  rw [show 848 = 16 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 53)]
  rw [totient_cert_16, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_849 : Nat.totient 849 = 564 := by
  rw [show 849 = 3 * 283 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 283)]
  rw [totient_cert_3, totient_cert_283] <;> norm_num
@[simp] lemma totient_cert_850 : Nat.totient 850 = 320 := by
  rw [show 850 = 2 * 425 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 425)]
  rw [totient_cert_2, totient_cert_425] <;> norm_num
@[simp] lemma totient_cert_851 : Nat.totient 851 = 792 := by
  rw [show 851 = 23 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 37)]
  rw [totient_cert_23, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_852 : Nat.totient 852 = 280 := by
  rw [show 852 = 4 * 213 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 213)]
  rw [totient_cert_4, totient_cert_213] <;> norm_num
@[simp] lemma totient_cert_853 : Nat.totient 853 = 852 := by
  rw [show 853 = 853^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 853) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_854 : Nat.totient 854 = 360 := by
  rw [show 854 = 2 * 427 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 427)]
  rw [totient_cert_2, totient_cert_427] <;> norm_num
@[simp] lemma totient_cert_855 : Nat.totient 855 = 432 := by
  rw [show 855 = 9 * 95 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 95)]
  rw [totient_cert_9, totient_cert_95] <;> norm_num
@[simp] lemma totient_cert_856 : Nat.totient 856 = 424 := by
  rw [show 856 = 8 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 107)]
  rw [totient_cert_8, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_857 : Nat.totient 857 = 856 := by
  rw [show 857 = 857^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 857) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_858 : Nat.totient 858 = 240 := by
  rw [show 858 = 2 * 429 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 429)]
  rw [totient_cert_2, totient_cert_429] <;> norm_num
@[simp] lemma totient_cert_859 : Nat.totient 859 = 858 := by
  rw [show 859 = 859^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 859) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_860 : Nat.totient 860 = 336 := by
  rw [show 860 = 4 * 215 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 215)]
  rw [totient_cert_4, totient_cert_215] <;> norm_num
@[simp] lemma totient_cert_861 : Nat.totient 861 = 480 := by
  rw [show 861 = 3 * 287 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 287)]
  rw [totient_cert_3, totient_cert_287] <;> norm_num
@[simp] lemma totient_cert_862 : Nat.totient 862 = 430 := by
  rw [show 862 = 2 * 431 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 431)]
  rw [totient_cert_2, totient_cert_431] <;> norm_num
@[simp] lemma totient_cert_863 : Nat.totient 863 = 862 := by
  rw [show 863 = 863^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 863) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_864 : Nat.totient 864 = 288 := by
  rw [show 864 = 32 * 27 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 27)]
  rw [totient_cert_32, totient_cert_27] <;> norm_num
@[simp] lemma totient_cert_865 : Nat.totient 865 = 688 := by
  rw [show 865 = 5 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 173)]
  rw [totient_cert_5, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_866 : Nat.totient 866 = 432 := by
  rw [show 866 = 2 * 433 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 433)]
  rw [totient_cert_2, totient_cert_433] <;> norm_num
@[simp] lemma totient_cert_867 : Nat.totient 867 = 544 := by
  rw [show 867 = 3 * 289 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 289)]
  rw [totient_cert_3, totient_cert_289] <;> norm_num
@[simp] lemma totient_cert_868 : Nat.totient 868 = 360 := by
  rw [show 868 = 4 * 217 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 217)]
  rw [totient_cert_4, totient_cert_217] <;> norm_num
@[simp] lemma totient_cert_869 : Nat.totient 869 = 780 := by
  rw [show 869 = 11 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 79)]
  rw [totient_cert_11, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_870 : Nat.totient 870 = 224 := by
  rw [show 870 = 2 * 435 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 435)]
  rw [totient_cert_2, totient_cert_435] <;> norm_num
@[simp] lemma totient_cert_871 : Nat.totient 871 = 792 := by
  rw [show 871 = 13 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 67)]
  rw [totient_cert_13, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_872 : Nat.totient 872 = 432 := by
  rw [show 872 = 8 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 109)]
  rw [totient_cert_8, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_873 : Nat.totient 873 = 576 := by
  rw [show 873 = 9 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 97)]
  rw [totient_cert_9, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_874 : Nat.totient 874 = 396 := by
  rw [show 874 = 2 * 437 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 437)]
  rw [totient_cert_2, totient_cert_437] <;> norm_num
@[simp] lemma totient_cert_875 : Nat.totient 875 = 600 := by
  rw [show 875 = 125 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 125 7)]
  rw [totient_cert_125, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_876 : Nat.totient 876 = 288 := by
  rw [show 876 = 4 * 219 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 219)]
  rw [totient_cert_4, totient_cert_219] <;> norm_num
@[simp] lemma totient_cert_877 : Nat.totient 877 = 876 := by
  rw [show 877 = 877^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 877) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_878 : Nat.totient 878 = 438 := by
  rw [show 878 = 2 * 439 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 439)]
  rw [totient_cert_2, totient_cert_439] <;> norm_num
@[simp] lemma totient_cert_879 : Nat.totient 879 = 584 := by
  rw [show 879 = 3 * 293 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 293)]
  rw [totient_cert_3, totient_cert_293] <;> norm_num
@[simp] lemma totient_cert_880 : Nat.totient 880 = 320 := by
  rw [show 880 = 16 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 55)]
  rw [totient_cert_16, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_881 : Nat.totient 881 = 880 := by
  rw [show 881 = 881^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 881) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_882 : Nat.totient 882 = 252 := by
  rw [show 882 = 2 * 441 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 441)]
  rw [totient_cert_2, totient_cert_441] <;> norm_num
@[simp] lemma totient_cert_883 : Nat.totient 883 = 882 := by
  rw [show 883 = 883^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 883) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_884 : Nat.totient 884 = 384 := by
  rw [show 884 = 4 * 221 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 221)]
  rw [totient_cert_4, totient_cert_221] <;> norm_num
@[simp] lemma totient_cert_885 : Nat.totient 885 = 464 := by
  rw [show 885 = 3 * 295 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 295)]
  rw [totient_cert_3, totient_cert_295] <;> norm_num
@[simp] lemma totient_cert_886 : Nat.totient 886 = 442 := by
  rw [show 886 = 2 * 443 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 443)]
  rw [totient_cert_2, totient_cert_443] <;> norm_num
@[simp] lemma totient_cert_887 : Nat.totient 887 = 886 := by
  rw [show 887 = 887^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 887) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_888 : Nat.totient 888 = 288 := by
  rw [show 888 = 8 * 111 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 111)]
  rw [totient_cert_8, totient_cert_111] <;> norm_num
@[simp] lemma totient_cert_889 : Nat.totient 889 = 756 := by
  rw [show 889 = 7 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 127)]
  rw [totient_cert_7, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_890 : Nat.totient 890 = 352 := by
  rw [show 890 = 2 * 445 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 445)]
  rw [totient_cert_2, totient_cert_445] <;> norm_num
@[simp] lemma totient_cert_891 : Nat.totient 891 = 540 := by
  rw [show 891 = 81 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 81 11)]
  rw [totient_cert_81, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_892 : Nat.totient 892 = 444 := by
  rw [show 892 = 4 * 223 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 223)]
  rw [totient_cert_4, totient_cert_223] <;> norm_num
@[simp] lemma totient_cert_893 : Nat.totient 893 = 828 := by
  rw [show 893 = 19 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 47)]
  rw [totient_cert_19, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_894 : Nat.totient 894 = 296 := by
  rw [show 894 = 2 * 447 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 447)]
  rw [totient_cert_2, totient_cert_447] <;> norm_num
@[simp] lemma totient_cert_895 : Nat.totient 895 = 712 := by
  rw [show 895 = 5 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 179)]
  rw [totient_cert_5, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_896 : Nat.totient 896 = 384 := by
  rw [show 896 = 128 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 128 7)]
  rw [totient_cert_128, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_897 : Nat.totient 897 = 528 := by
  rw [show 897 = 3 * 299 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 299)]
  rw [totient_cert_3, totient_cert_299] <;> norm_num
@[simp] lemma totient_cert_898 : Nat.totient 898 = 448 := by
  rw [show 898 = 2 * 449 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 449)]
  rw [totient_cert_2, totient_cert_449] <;> norm_num
@[simp] lemma totient_cert_899 : Nat.totient 899 = 840 := by
  rw [show 899 = 29 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 31)]
  rw [totient_cert_29, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_900 : Nat.totient 900 = 240 := by
  rw [show 900 = 4 * 225 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 225)]
  rw [totient_cert_4, totient_cert_225] <;> norm_num
@[simp] lemma totient_cert_901 : Nat.totient 901 = 832 := by
  rw [show 901 = 17 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 53)]
  rw [totient_cert_17, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_902 : Nat.totient 902 = 400 := by
  rw [show 902 = 2 * 451 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 451)]
  rw [totient_cert_2, totient_cert_451] <;> norm_num
@[simp] lemma totient_cert_903 : Nat.totient 903 = 504 := by
  rw [show 903 = 3 * 301 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 301)]
  rw [totient_cert_3, totient_cert_301] <;> norm_num
@[simp] lemma totient_cert_904 : Nat.totient 904 = 448 := by
  rw [show 904 = 8 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 113)]
  rw [totient_cert_8, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_905 : Nat.totient 905 = 720 := by
  rw [show 905 = 5 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 181)]
  rw [totient_cert_5, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_906 : Nat.totient 906 = 300 := by
  rw [show 906 = 2 * 453 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 453)]
  rw [totient_cert_2, totient_cert_453] <;> norm_num
@[simp] lemma totient_cert_907 : Nat.totient 907 = 906 := by
  rw [show 907 = 907^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 907) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_908 : Nat.totient 908 = 452 := by
  rw [show 908 = 4 * 227 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 227)]
  rw [totient_cert_4, totient_cert_227] <;> norm_num
@[simp] lemma totient_cert_909 : Nat.totient 909 = 600 := by
  rw [show 909 = 9 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 101)]
  rw [totient_cert_9, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_910 : Nat.totient 910 = 288 := by
  rw [show 910 = 2 * 455 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 455)]
  rw [totient_cert_2, totient_cert_455] <;> norm_num
@[simp] lemma totient_cert_911 : Nat.totient 911 = 910 := by
  rw [show 911 = 911^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 911) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_912 : Nat.totient 912 = 288 := by
  rw [show 912 = 16 * 57 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 57)]
  rw [totient_cert_16, totient_cert_57] <;> norm_num
@[simp] lemma totient_cert_913 : Nat.totient 913 = 820 := by
  rw [show 913 = 11 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 83)]
  rw [totient_cert_11, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_914 : Nat.totient 914 = 456 := by
  rw [show 914 = 2 * 457 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 457)]
  rw [totient_cert_2, totient_cert_457] <;> norm_num
@[simp] lemma totient_cert_915 : Nat.totient 915 = 480 := by
  rw [show 915 = 3 * 305 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 305)]
  rw [totient_cert_3, totient_cert_305] <;> norm_num
@[simp] lemma totient_cert_916 : Nat.totient 916 = 456 := by
  rw [show 916 = 4 * 229 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 229)]
  rw [totient_cert_4, totient_cert_229] <;> norm_num
@[simp] lemma totient_cert_917 : Nat.totient 917 = 780 := by
  rw [show 917 = 7 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 131)]
  rw [totient_cert_7, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_918 : Nat.totient 918 = 288 := by
  rw [show 918 = 2 * 459 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 459)]
  rw [totient_cert_2, totient_cert_459] <;> norm_num
@[simp] lemma totient_cert_919 : Nat.totient 919 = 918 := by
  rw [show 919 = 919^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 919) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_920 : Nat.totient 920 = 352 := by
  rw [show 920 = 8 * 115 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 115)]
  rw [totient_cert_8, totient_cert_115] <;> norm_num
@[simp] lemma totient_cert_921 : Nat.totient 921 = 612 := by
  rw [show 921 = 3 * 307 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 307)]
  rw [totient_cert_3, totient_cert_307] <;> norm_num
@[simp] lemma totient_cert_922 : Nat.totient 922 = 460 := by
  rw [show 922 = 2 * 461 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 461)]
  rw [totient_cert_2, totient_cert_461] <;> norm_num
@[simp] lemma totient_cert_923 : Nat.totient 923 = 840 := by
  rw [show 923 = 13 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 71)]
  rw [totient_cert_13, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_924 : Nat.totient 924 = 240 := by
  rw [show 924 = 4 * 231 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 231)]
  rw [totient_cert_4, totient_cert_231] <;> norm_num
@[simp] lemma totient_cert_925 : Nat.totient 925 = 720 := by
  rw [show 925 = 25 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 37)]
  rw [totient_cert_25, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_926 : Nat.totient 926 = 462 := by
  rw [show 926 = 2 * 463 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 463)]
  rw [totient_cert_2, totient_cert_463] <;> norm_num
@[simp] lemma totient_cert_927 : Nat.totient 927 = 612 := by
  rw [show 927 = 9 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 103)]
  rw [totient_cert_9, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_928 : Nat.totient 928 = 448 := by
  rw [show 928 = 32 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 29)]
  rw [totient_cert_32, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_929 : Nat.totient 929 = 928 := by
  rw [show 929 = 929^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 929) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_930 : Nat.totient 930 = 240 := by
  rw [show 930 = 2 * 465 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 465)]
  rw [totient_cert_2, totient_cert_465] <;> norm_num
@[simp] lemma totient_cert_931 : Nat.totient 931 = 756 := by
  rw [show 931 = 49 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 19)]
  rw [totient_cert_49, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_932 : Nat.totient 932 = 464 := by
  rw [show 932 = 4 * 233 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 233)]
  rw [totient_cert_4, totient_cert_233] <;> norm_num
@[simp] lemma totient_cert_933 : Nat.totient 933 = 620 := by
  rw [show 933 = 3 * 311 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 311)]
  rw [totient_cert_3, totient_cert_311] <;> norm_num
@[simp] lemma totient_cert_934 : Nat.totient 934 = 466 := by
  rw [show 934 = 2 * 467 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 467)]
  rw [totient_cert_2, totient_cert_467] <;> norm_num
@[simp] lemma totient_cert_935 : Nat.totient 935 = 640 := by
  rw [show 935 = 5 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 187)]
  rw [totient_cert_5, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_936 : Nat.totient 936 = 288 := by
  rw [show 936 = 8 * 117 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 117)]
  rw [totient_cert_8, totient_cert_117] <;> norm_num
@[simp] lemma totient_cert_937 : Nat.totient 937 = 936 := by
  rw [show 937 = 937^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 937) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_938 : Nat.totient 938 = 396 := by
  rw [show 938 = 2 * 469 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 469)]
  rw [totient_cert_2, totient_cert_469] <;> norm_num
@[simp] lemma totient_cert_939 : Nat.totient 939 = 624 := by
  rw [show 939 = 3 * 313 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 313)]
  rw [totient_cert_3, totient_cert_313] <;> norm_num
@[simp] lemma totient_cert_940 : Nat.totient 940 = 368 := by
  rw [show 940 = 4 * 235 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 235)]
  rw [totient_cert_4, totient_cert_235] <;> norm_num
@[simp] lemma totient_cert_941 : Nat.totient 941 = 940 := by
  rw [show 941 = 941^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 941) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_942 : Nat.totient 942 = 312 := by
  rw [show 942 = 2 * 471 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 471)]
  rw [totient_cert_2, totient_cert_471] <;> norm_num
@[simp] lemma totient_cert_943 : Nat.totient 943 = 880 := by
  rw [show 943 = 23 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 41)]
  rw [totient_cert_23, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_944 : Nat.totient 944 = 464 := by
  rw [show 944 = 16 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 59)]
  rw [totient_cert_16, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_945 : Nat.totient 945 = 432 := by
  rw [show 945 = 27 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 35)]
  rw [totient_cert_27, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_946 : Nat.totient 946 = 420 := by
  rw [show 946 = 2 * 473 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 473)]
  rw [totient_cert_2, totient_cert_473] <;> norm_num
@[simp] lemma totient_cert_947 : Nat.totient 947 = 946 := by
  rw [show 947 = 947^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 947) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_948 : Nat.totient 948 = 312 := by
  rw [show 948 = 4 * 237 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 237)]
  rw [totient_cert_4, totient_cert_237] <;> norm_num
@[simp] lemma totient_cert_949 : Nat.totient 949 = 864 := by
  rw [show 949 = 13 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 73)]
  rw [totient_cert_13, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_950 : Nat.totient 950 = 360 := by
  rw [show 950 = 2 * 475 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 475)]
  rw [totient_cert_2, totient_cert_475] <;> norm_num
@[simp] lemma totient_cert_951 : Nat.totient 951 = 632 := by
  rw [show 951 = 3 * 317 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 317)]
  rw [totient_cert_3, totient_cert_317] <;> norm_num
@[simp] lemma totient_cert_952 : Nat.totient 952 = 384 := by
  rw [show 952 = 8 * 119 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 119)]
  rw [totient_cert_8, totient_cert_119] <;> norm_num
@[simp] lemma totient_cert_953 : Nat.totient 953 = 952 := by
  rw [show 953 = 953^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 953) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_954 : Nat.totient 954 = 312 := by
  rw [show 954 = 2 * 477 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 477)]
  rw [totient_cert_2, totient_cert_477] <;> norm_num
@[simp] lemma totient_cert_955 : Nat.totient 955 = 760 := by
  rw [show 955 = 5 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 191)]
  rw [totient_cert_5, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_956 : Nat.totient 956 = 476 := by
  rw [show 956 = 4 * 239 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 239)]
  rw [totient_cert_4, totient_cert_239] <;> norm_num
@[simp] lemma totient_cert_957 : Nat.totient 957 = 560 := by
  rw [show 957 = 3 * 319 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 319)]
  rw [totient_cert_3, totient_cert_319] <;> norm_num
@[simp] lemma totient_cert_958 : Nat.totient 958 = 478 := by
  rw [show 958 = 2 * 479 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 479)]
  rw [totient_cert_2, totient_cert_479] <;> norm_num
@[simp] lemma totient_cert_959 : Nat.totient 959 = 816 := by
  rw [show 959 = 7 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 137)]
  rw [totient_cert_7, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_960 : Nat.totient 960 = 256 := by
  rw [show 960 = 64 * 15 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 15)]
  rw [totient_cert_64, totient_cert_15] <;> norm_num
@[simp] lemma totient_cert_961 : Nat.totient 961 = 930 := by
  rw [show 961 = 31^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 31) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_962 : Nat.totient 962 = 432 := by
  rw [show 962 = 2 * 481 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 481)]
  rw [totient_cert_2, totient_cert_481] <;> norm_num
@[simp] lemma totient_cert_963 : Nat.totient 963 = 636 := by
  rw [show 963 = 9 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 107)]
  rw [totient_cert_9, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_964 : Nat.totient 964 = 480 := by
  rw [show 964 = 4 * 241 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 241)]
  rw [totient_cert_4, totient_cert_241] <;> norm_num
@[simp] lemma totient_cert_965 : Nat.totient 965 = 768 := by
  rw [show 965 = 5 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 193)]
  rw [totient_cert_5, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_966 : Nat.totient 966 = 264 := by
  rw [show 966 = 2 * 483 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 483)]
  rw [totient_cert_2, totient_cert_483] <;> norm_num
@[simp] lemma totient_cert_967 : Nat.totient 967 = 966 := by
  rw [show 967 = 967^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 967) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_968 : Nat.totient 968 = 440 := by
  rw [show 968 = 8 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 121)]
  rw [totient_cert_8, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_969 : Nat.totient 969 = 576 := by
  rw [show 969 = 3 * 323 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 323)]
  rw [totient_cert_3, totient_cert_323] <;> norm_num
@[simp] lemma totient_cert_970 : Nat.totient 970 = 384 := by
  rw [show 970 = 2 * 485 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 485)]
  rw [totient_cert_2, totient_cert_485] <;> norm_num
@[simp] lemma totient_cert_971 : Nat.totient 971 = 970 := by
  rw [show 971 = 971^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 971) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_972 : Nat.totient 972 = 324 := by
  rw [show 972 = 4 * 243 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 243)]
  rw [totient_cert_4, totient_cert_243] <;> norm_num
@[simp] lemma totient_cert_973 : Nat.totient 973 = 828 := by
  rw [show 973 = 7 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 139)]
  rw [totient_cert_7, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_974 : Nat.totient 974 = 486 := by
  rw [show 974 = 2 * 487 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 487)]
  rw [totient_cert_2, totient_cert_487] <;> norm_num
@[simp] lemma totient_cert_975 : Nat.totient 975 = 480 := by
  rw [show 975 = 3 * 325 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 325)]
  rw [totient_cert_3, totient_cert_325] <;> norm_num
@[simp] lemma totient_cert_976 : Nat.totient 976 = 480 := by
  rw [show 976 = 16 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 61)]
  rw [totient_cert_16, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_977 : Nat.totient 977 = 976 := by
  rw [show 977 = 977^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 977) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_978 : Nat.totient 978 = 324 := by
  rw [show 978 = 2 * 489 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 489)]
  rw [totient_cert_2, totient_cert_489] <;> norm_num
@[simp] lemma totient_cert_979 : Nat.totient 979 = 880 := by
  rw [show 979 = 11 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 89)]
  rw [totient_cert_11, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_980 : Nat.totient 980 = 336 := by
  rw [show 980 = 4 * 245 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 245)]
  rw [totient_cert_4, totient_cert_245] <;> norm_num
@[simp] lemma totient_cert_981 : Nat.totient 981 = 648 := by
  rw [show 981 = 9 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 109)]
  rw [totient_cert_9, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_982 : Nat.totient 982 = 490 := by
  rw [show 982 = 2 * 491 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 491)]
  rw [totient_cert_2, totient_cert_491] <;> norm_num
@[simp] lemma totient_cert_983 : Nat.totient 983 = 982 := by
  rw [show 983 = 983^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 983) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_984 : Nat.totient 984 = 320 := by
  rw [show 984 = 8 * 123 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 123)]
  rw [totient_cert_8, totient_cert_123] <;> norm_num
@[simp] lemma totient_cert_985 : Nat.totient 985 = 784 := by
  rw [show 985 = 5 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 197)]
  rw [totient_cert_5, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_986 : Nat.totient 986 = 448 := by
  rw [show 986 = 2 * 493 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 493)]
  rw [totient_cert_2, totient_cert_493] <;> norm_num
@[simp] lemma totient_cert_987 : Nat.totient 987 = 552 := by
  rw [show 987 = 3 * 329 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 329)]
  rw [totient_cert_3, totient_cert_329] <;> norm_num
@[simp] lemma totient_cert_988 : Nat.totient 988 = 432 := by
  rw [show 988 = 4 * 247 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 247)]
  rw [totient_cert_4, totient_cert_247] <;> norm_num
@[simp] lemma totient_cert_989 : Nat.totient 989 = 924 := by
  rw [show 989 = 23 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 43)]
  rw [totient_cert_23, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_990 : Nat.totient 990 = 240 := by
  rw [show 990 = 2 * 495 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 495)]
  rw [totient_cert_2, totient_cert_495] <;> norm_num
@[simp] lemma totient_cert_991 : Nat.totient 991 = 990 := by
  rw [show 991 = 991^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 991) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_992 : Nat.totient 992 = 480 := by
  rw [show 992 = 32 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 31)]
  rw [totient_cert_32, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_993 : Nat.totient 993 = 660 := by
  rw [show 993 = 3 * 331 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 331)]
  rw [totient_cert_3, totient_cert_331] <;> norm_num
@[simp] lemma totient_cert_994 : Nat.totient 994 = 420 := by
  rw [show 994 = 2 * 497 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 497)]
  rw [totient_cert_2, totient_cert_497] <;> norm_num
@[simp] lemma totient_cert_995 : Nat.totient 995 = 792 := by
  rw [show 995 = 5 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 199)]
  rw [totient_cert_5, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_996 : Nat.totient 996 = 328 := by
  rw [show 996 = 4 * 249 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 249)]
  rw [totient_cert_4, totient_cert_249] <;> norm_num
@[simp] lemma totient_cert_997 : Nat.totient 997 = 996 := by
  rw [show 997 = 997^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 997) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_998 : Nat.totient 998 = 498 := by
  rw [show 998 = 2 * 499 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 499)]
  rw [totient_cert_2, totient_cert_499] <;> norm_num
@[simp] lemma totient_cert_999 : Nat.totient 999 = 648 := by
  rw [show 999 = 27 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 37)]
  rw [totient_cert_27, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_1000 : Nat.totient 1000 = 400 := by
  rw [show 1000 = 8 * 125 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 125)]
  rw [totient_cert_8, totient_cert_125] <;> norm_num
@[simp] lemma totient_cert_1001 : Nat.totient 1001 = 720 := by
  rw [show 1001 = 7 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 143)]
  rw [totient_cert_7, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_1002 : Nat.totient 1002 = 332 := by
  rw [show 1002 = 2 * 501 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 501)]
  rw [totient_cert_2, totient_cert_501] <;> norm_num
@[simp] lemma totient_cert_1003 : Nat.totient 1003 = 928 := by
  rw [show 1003 = 17 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 59)]
  rw [totient_cert_17, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_1004 : Nat.totient 1004 = 500 := by
  rw [show 1004 = 4 * 251 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 251)]
  rw [totient_cert_4, totient_cert_251] <;> norm_num
@[simp] lemma totient_cert_1005 : Nat.totient 1005 = 528 := by
  rw [show 1005 = 3 * 335 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 335)]
  rw [totient_cert_3, totient_cert_335] <;> norm_num
@[simp] lemma totient_cert_1006 : Nat.totient 1006 = 502 := by
  rw [show 1006 = 2 * 503 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 503)]
  rw [totient_cert_2, totient_cert_503] <;> norm_num
@[simp] lemma totient_cert_1007 : Nat.totient 1007 = 936 := by
  rw [show 1007 = 19 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 53)]
  rw [totient_cert_19, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1008 : Nat.totient 1008 = 288 := by
  rw [show 1008 = 16 * 63 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 63)]
  rw [totient_cert_16, totient_cert_63] <;> norm_num
@[simp] lemma totient_cert_1009 : Nat.totient 1009 = 1008 := by
  rw [show 1009 = 1009^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1009) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1010 : Nat.totient 1010 = 400 := by
  rw [show 1010 = 2 * 505 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 505)]
  rw [totient_cert_2, totient_cert_505] <;> norm_num
@[simp] lemma totient_cert_1011 : Nat.totient 1011 = 672 := by
  rw [show 1011 = 3 * 337 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 337)]
  rw [totient_cert_3, totient_cert_337] <;> norm_num
@[simp] lemma totient_cert_1012 : Nat.totient 1012 = 440 := by
  rw [show 1012 = 4 * 253 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 253)]
  rw [totient_cert_4, totient_cert_253] <;> norm_num
@[simp] lemma totient_cert_1013 : Nat.totient 1013 = 1012 := by
  rw [show 1013 = 1013^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1013) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1014 : Nat.totient 1014 = 312 := by
  rw [show 1014 = 2 * 507 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 507)]
  rw [totient_cert_2, totient_cert_507] <;> norm_num
@[simp] lemma totient_cert_1015 : Nat.totient 1015 = 672 := by
  rw [show 1015 = 5 * 203 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 203)]
  rw [totient_cert_5, totient_cert_203] <;> norm_num
@[simp] lemma totient_cert_1016 : Nat.totient 1016 = 504 := by
  rw [show 1016 = 8 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 127)]
  rw [totient_cert_8, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_1017 : Nat.totient 1017 = 672 := by
  rw [show 1017 = 9 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 113)]
  rw [totient_cert_9, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_1018 : Nat.totient 1018 = 508 := by
  rw [show 1018 = 2 * 509 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 509)]
  rw [totient_cert_2, totient_cert_509] <;> norm_num
@[simp] lemma totient_cert_1019 : Nat.totient 1019 = 1018 := by
  rw [show 1019 = 1019^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1019) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1020 : Nat.totient 1020 = 256 := by
  rw [show 1020 = 4 * 255 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 255)]
  rw [totient_cert_4, totient_cert_255] <;> norm_num
@[simp] lemma totient_cert_1021 : Nat.totient 1021 = 1020 := by
  rw [show 1021 = 1021^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1021) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1022 : Nat.totient 1022 = 432 := by
  rw [show 1022 = 2 * 511 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 511)]
  rw [totient_cert_2, totient_cert_511] <;> norm_num
@[simp] lemma totient_cert_1023 : Nat.totient 1023 = 600 := by
  rw [show 1023 = 3 * 341 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 341)]
  rw [totient_cert_3, totient_cert_341] <;> norm_num
@[simp] lemma totient_cert_1024 : Nat.totient 1024 = 512 := by
  rw [show 1024 = 2^10 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 2) (by norm_num : 0 < 10)] <;> norm_num
@[simp] lemma totient_cert_1025 : Nat.totient 1025 = 800 := by
  rw [show 1025 = 25 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 41)]
  rw [totient_cert_25, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_1026 : Nat.totient 1026 = 324 := by
  rw [show 1026 = 2 * 513 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 513)]
  rw [totient_cert_2, totient_cert_513] <;> norm_num
@[simp] lemma totient_cert_1027 : Nat.totient 1027 = 936 := by
  rw [show 1027 = 13 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 79)]
  rw [totient_cert_13, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_1028 : Nat.totient 1028 = 512 := by
  rw [show 1028 = 4 * 257 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 257)]
  rw [totient_cert_4, totient_cert_257] <;> norm_num
@[simp] lemma totient_cert_1029 : Nat.totient 1029 = 588 := by
  rw [show 1029 = 3 * 343 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 343)]
  rw [totient_cert_3, totient_cert_343] <;> norm_num
@[simp] lemma totient_cert_1030 : Nat.totient 1030 = 408 := by
  rw [show 1030 = 2 * 515 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 515)]
  rw [totient_cert_2, totient_cert_515] <;> norm_num
@[simp] lemma totient_cert_1031 : Nat.totient 1031 = 1030 := by
  rw [show 1031 = 1031^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1031) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1032 : Nat.totient 1032 = 336 := by
  rw [show 1032 = 8 * 129 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 129)]
  rw [totient_cert_8, totient_cert_129] <;> norm_num
@[simp] lemma totient_cert_1033 : Nat.totient 1033 = 1032 := by
  rw [show 1033 = 1033^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1033) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1034 : Nat.totient 1034 = 460 := by
  rw [show 1034 = 2 * 517 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 517)]
  rw [totient_cert_2, totient_cert_517] <;> norm_num
@[simp] lemma totient_cert_1035 : Nat.totient 1035 = 528 := by
  rw [show 1035 = 9 * 115 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 115)]
  rw [totient_cert_9, totient_cert_115] <;> norm_num
@[simp] lemma totient_cert_1036 : Nat.totient 1036 = 432 := by
  rw [show 1036 = 4 * 259 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 259)]
  rw [totient_cert_4, totient_cert_259] <;> norm_num
@[simp] lemma totient_cert_1037 : Nat.totient 1037 = 960 := by
  rw [show 1037 = 17 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 61)]
  rw [totient_cert_17, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_1038 : Nat.totient 1038 = 344 := by
  rw [show 1038 = 2 * 519 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 519)]
  rw [totient_cert_2, totient_cert_519] <;> norm_num
@[simp] lemma totient_cert_1039 : Nat.totient 1039 = 1038 := by
  rw [show 1039 = 1039^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1039) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1040 : Nat.totient 1040 = 384 := by
  rw [show 1040 = 16 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 65)]
  rw [totient_cert_16, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_1041 : Nat.totient 1041 = 692 := by
  rw [show 1041 = 3 * 347 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 347)]
  rw [totient_cert_3, totient_cert_347] <;> norm_num
@[simp] lemma totient_cert_1042 : Nat.totient 1042 = 520 := by
  rw [show 1042 = 2 * 521 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 521)]
  rw [totient_cert_2, totient_cert_521] <;> norm_num
@[simp] lemma totient_cert_1043 : Nat.totient 1043 = 888 := by
  rw [show 1043 = 7 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 149)]
  rw [totient_cert_7, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_1044 : Nat.totient 1044 = 336 := by
  rw [show 1044 = 4 * 261 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 261)]
  rw [totient_cert_4, totient_cert_261] <;> norm_num
@[simp] lemma totient_cert_1045 : Nat.totient 1045 = 720 := by
  rw [show 1045 = 5 * 209 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 209)]
  rw [totient_cert_5, totient_cert_209] <;> norm_num
@[simp] lemma totient_cert_1046 : Nat.totient 1046 = 522 := by
  rw [show 1046 = 2 * 523 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 523)]
  rw [totient_cert_2, totient_cert_523] <;> norm_num
@[simp] lemma totient_cert_1047 : Nat.totient 1047 = 696 := by
  rw [show 1047 = 3 * 349 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 349)]
  rw [totient_cert_3, totient_cert_349] <;> norm_num
@[simp] lemma totient_cert_1048 : Nat.totient 1048 = 520 := by
  rw [show 1048 = 8 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 131)]
  rw [totient_cert_8, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_1049 : Nat.totient 1049 = 1048 := by
  rw [show 1049 = 1049^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1049) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1050 : Nat.totient 1050 = 240 := by
  rw [show 1050 = 2 * 525 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 525)]
  rw [totient_cert_2, totient_cert_525] <;> norm_num
@[simp] lemma totient_cert_1051 : Nat.totient 1051 = 1050 := by
  rw [show 1051 = 1051^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1051) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1052 : Nat.totient 1052 = 524 := by
  rw [show 1052 = 4 * 263 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 263)]
  rw [totient_cert_4, totient_cert_263] <;> norm_num
@[simp] lemma totient_cert_1053 : Nat.totient 1053 = 648 := by
  rw [show 1053 = 81 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 81 13)]
  rw [totient_cert_81, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_1054 : Nat.totient 1054 = 480 := by
  rw [show 1054 = 2 * 527 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 527)]
  rw [totient_cert_2, totient_cert_527] <;> norm_num
@[simp] lemma totient_cert_1055 : Nat.totient 1055 = 840 := by
  rw [show 1055 = 5 * 211 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 211)]
  rw [totient_cert_5, totient_cert_211] <;> norm_num
@[simp] lemma totient_cert_1056 : Nat.totient 1056 = 320 := by
  rw [show 1056 = 32 * 33 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 33)]
  rw [totient_cert_32, totient_cert_33] <;> norm_num
@[simp] lemma totient_cert_1057 : Nat.totient 1057 = 900 := by
  rw [show 1057 = 7 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 151)]
  rw [totient_cert_7, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_1058 : Nat.totient 1058 = 506 := by
  rw [show 1058 = 2 * 529 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 529)]
  rw [totient_cert_2, totient_cert_529] <;> norm_num
@[simp] lemma totient_cert_1059 : Nat.totient 1059 = 704 := by
  rw [show 1059 = 3 * 353 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 353)]
  rw [totient_cert_3, totient_cert_353] <;> norm_num
@[simp] lemma totient_cert_1060 : Nat.totient 1060 = 416 := by
  rw [show 1060 = 4 * 265 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 265)]
  rw [totient_cert_4, totient_cert_265] <;> norm_num
@[simp] lemma totient_cert_1061 : Nat.totient 1061 = 1060 := by
  rw [show 1061 = 1061^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1061) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1062 : Nat.totient 1062 = 348 := by
  rw [show 1062 = 2 * 531 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 531)]
  rw [totient_cert_2, totient_cert_531] <;> norm_num
@[simp] lemma totient_cert_1063 : Nat.totient 1063 = 1062 := by
  rw [show 1063 = 1063^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1063) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1064 : Nat.totient 1064 = 432 := by
  rw [show 1064 = 8 * 133 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 133)]
  rw [totient_cert_8, totient_cert_133] <;> norm_num
@[simp] lemma totient_cert_1065 : Nat.totient 1065 = 560 := by
  rw [show 1065 = 3 * 355 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 355)]
  rw [totient_cert_3, totient_cert_355] <;> norm_num
@[simp] lemma totient_cert_1066 : Nat.totient 1066 = 480 := by
  rw [show 1066 = 2 * 533 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 533)]
  rw [totient_cert_2, totient_cert_533] <;> norm_num
@[simp] lemma totient_cert_1067 : Nat.totient 1067 = 960 := by
  rw [show 1067 = 11 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 97)]
  rw [totient_cert_11, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_1068 : Nat.totient 1068 = 352 := by
  rw [show 1068 = 4 * 267 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 267)]
  rw [totient_cert_4, totient_cert_267] <;> norm_num
@[simp] lemma totient_cert_1069 : Nat.totient 1069 = 1068 := by
  rw [show 1069 = 1069^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1069) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1070 : Nat.totient 1070 = 424 := by
  rw [show 1070 = 2 * 535 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 535)]
  rw [totient_cert_2, totient_cert_535] <;> norm_num
@[simp] lemma totient_cert_1071 : Nat.totient 1071 = 576 := by
  rw [show 1071 = 9 * 119 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 119)]
  rw [totient_cert_9, totient_cert_119] <;> norm_num
@[simp] lemma totient_cert_1072 : Nat.totient 1072 = 528 := by
  rw [show 1072 = 16 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 67)]
  rw [totient_cert_16, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_1073 : Nat.totient 1073 = 1008 := by
  rw [show 1073 = 29 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 37)]
  rw [totient_cert_29, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_1074 : Nat.totient 1074 = 356 := by
  rw [show 1074 = 2 * 537 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 537)]
  rw [totient_cert_2, totient_cert_537] <;> norm_num
@[simp] lemma totient_cert_1075 : Nat.totient 1075 = 840 := by
  rw [show 1075 = 25 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 43)]
  rw [totient_cert_25, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1076 : Nat.totient 1076 = 536 := by
  rw [show 1076 = 4 * 269 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 269)]
  rw [totient_cert_4, totient_cert_269] <;> norm_num
@[simp] lemma totient_cert_1077 : Nat.totient 1077 = 716 := by
  rw [show 1077 = 3 * 359 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 359)]
  rw [totient_cert_3, totient_cert_359] <;> norm_num
@[simp] lemma totient_cert_1078 : Nat.totient 1078 = 420 := by
  rw [show 1078 = 2 * 539 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 539)]
  rw [totient_cert_2, totient_cert_539] <;> norm_num
@[simp] lemma totient_cert_1079 : Nat.totient 1079 = 984 := by
  rw [show 1079 = 13 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 83)]
  rw [totient_cert_13, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_1080 : Nat.totient 1080 = 288 := by
  rw [show 1080 = 8 * 135 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 135)]
  rw [totient_cert_8, totient_cert_135] <;> norm_num
@[simp] lemma totient_cert_1081 : Nat.totient 1081 = 1012 := by
  rw [show 1081 = 23 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 47)]
  rw [totient_cert_23, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1082 : Nat.totient 1082 = 540 := by
  rw [show 1082 = 2 * 541 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 541)]
  rw [totient_cert_2, totient_cert_541] <;> norm_num
@[simp] lemma totient_cert_1083 : Nat.totient 1083 = 684 := by
  rw [show 1083 = 3 * 361 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 361)]
  rw [totient_cert_3, totient_cert_361] <;> norm_num
@[simp] lemma totient_cert_1084 : Nat.totient 1084 = 540 := by
  rw [show 1084 = 4 * 271 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 271)]
  rw [totient_cert_4, totient_cert_271] <;> norm_num
@[simp] lemma totient_cert_1085 : Nat.totient 1085 = 720 := by
  rw [show 1085 = 5 * 217 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 217)]
  rw [totient_cert_5, totient_cert_217] <;> norm_num
@[simp] lemma totient_cert_1086 : Nat.totient 1086 = 360 := by
  rw [show 1086 = 2 * 543 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 543)]
  rw [totient_cert_2, totient_cert_543] <;> norm_num
@[simp] lemma totient_cert_1087 : Nat.totient 1087 = 1086 := by
  rw [show 1087 = 1087^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1087) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1088 : Nat.totient 1088 = 512 := by
  rw [show 1088 = 64 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 17)]
  rw [totient_cert_64, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_1089 : Nat.totient 1089 = 660 := by
  rw [show 1089 = 9 * 121 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 121)]
  rw [totient_cert_9, totient_cert_121] <;> norm_num
@[simp] lemma totient_cert_1090 : Nat.totient 1090 = 432 := by
  rw [show 1090 = 2 * 545 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 545)]
  rw [totient_cert_2, totient_cert_545] <;> norm_num
@[simp] lemma totient_cert_1091 : Nat.totient 1091 = 1090 := by
  rw [show 1091 = 1091^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1091) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1092 : Nat.totient 1092 = 288 := by
  rw [show 1092 = 4 * 273 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 273)]
  rw [totient_cert_4, totient_cert_273] <;> norm_num
@[simp] lemma totient_cert_1093 : Nat.totient 1093 = 1092 := by
  rw [show 1093 = 1093^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1093) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1094 : Nat.totient 1094 = 546 := by
  rw [show 1094 = 2 * 547 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 547)]
  rw [totient_cert_2, totient_cert_547] <;> norm_num
@[simp] lemma totient_cert_1095 : Nat.totient 1095 = 576 := by
  rw [show 1095 = 3 * 365 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 365)]
  rw [totient_cert_3, totient_cert_365] <;> norm_num
@[simp] lemma totient_cert_1096 : Nat.totient 1096 = 544 := by
  rw [show 1096 = 8 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 137)]
  rw [totient_cert_8, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_1097 : Nat.totient 1097 = 1096 := by
  rw [show 1097 = 1097^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1097) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1098 : Nat.totient 1098 = 360 := by
  rw [show 1098 = 2 * 549 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 549)]
  rw [totient_cert_2, totient_cert_549] <;> norm_num
@[simp] lemma totient_cert_1099 : Nat.totient 1099 = 936 := by
  rw [show 1099 = 7 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 157)]
  rw [totient_cert_7, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_1100 : Nat.totient 1100 = 400 := by
  rw [show 1100 = 4 * 275 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 275)]
  rw [totient_cert_4, totient_cert_275] <;> norm_num
@[simp] lemma totient_cert_1101 : Nat.totient 1101 = 732 := by
  rw [show 1101 = 3 * 367 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 367)]
  rw [totient_cert_3, totient_cert_367] <;> norm_num
@[simp] lemma totient_cert_1102 : Nat.totient 1102 = 504 := by
  rw [show 1102 = 2 * 551 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 551)]
  rw [totient_cert_2, totient_cert_551] <;> norm_num
@[simp] lemma totient_cert_1103 : Nat.totient 1103 = 1102 := by
  rw [show 1103 = 1103^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1103) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1104 : Nat.totient 1104 = 352 := by
  rw [show 1104 = 16 * 69 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 69)]
  rw [totient_cert_16, totient_cert_69] <;> norm_num
@[simp] lemma totient_cert_1105 : Nat.totient 1105 = 768 := by
  rw [show 1105 = 5 * 221 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 221)]
  rw [totient_cert_5, totient_cert_221] <;> norm_num
@[simp] lemma totient_cert_1106 : Nat.totient 1106 = 468 := by
  rw [show 1106 = 2 * 553 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 553)]
  rw [totient_cert_2, totient_cert_553] <;> norm_num
@[simp] lemma totient_cert_1107 : Nat.totient 1107 = 720 := by
  rw [show 1107 = 27 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 41)]
  rw [totient_cert_27, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_1108 : Nat.totient 1108 = 552 := by
  rw [show 1108 = 4 * 277 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 277)]
  rw [totient_cert_4, totient_cert_277] <;> norm_num
@[simp] lemma totient_cert_1109 : Nat.totient 1109 = 1108 := by
  rw [show 1109 = 1109^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1109) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1110 : Nat.totient 1110 = 288 := by
  rw [show 1110 = 2 * 555 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 555)]
  rw [totient_cert_2, totient_cert_555] <;> norm_num
@[simp] lemma totient_cert_1111 : Nat.totient 1111 = 1000 := by
  rw [show 1111 = 11 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 101)]
  rw [totient_cert_11, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_1112 : Nat.totient 1112 = 552 := by
  rw [show 1112 = 8 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 139)]
  rw [totient_cert_8, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_1113 : Nat.totient 1113 = 624 := by
  rw [show 1113 = 3 * 371 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 371)]
  rw [totient_cert_3, totient_cert_371] <;> norm_num
@[simp] lemma totient_cert_1114 : Nat.totient 1114 = 556 := by
  rw [show 1114 = 2 * 557 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 557)]
  rw [totient_cert_2, totient_cert_557] <;> norm_num
@[simp] lemma totient_cert_1115 : Nat.totient 1115 = 888 := by
  rw [show 1115 = 5 * 223 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 223)]
  rw [totient_cert_5, totient_cert_223] <;> norm_num
@[simp] lemma totient_cert_1116 : Nat.totient 1116 = 360 := by
  rw [show 1116 = 4 * 279 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 279)]
  rw [totient_cert_4, totient_cert_279] <;> norm_num
@[simp] lemma totient_cert_1117 : Nat.totient 1117 = 1116 := by
  rw [show 1117 = 1117^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1117) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1118 : Nat.totient 1118 = 504 := by
  rw [show 1118 = 2 * 559 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 559)]
  rw [totient_cert_2, totient_cert_559] <;> norm_num
@[simp] lemma totient_cert_1119 : Nat.totient 1119 = 744 := by
  rw [show 1119 = 3 * 373 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 373)]
  rw [totient_cert_3, totient_cert_373] <;> norm_num
@[simp] lemma totient_cert_1120 : Nat.totient 1120 = 384 := by
  rw [show 1120 = 32 * 35 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 35)]
  rw [totient_cert_32, totient_cert_35] <;> norm_num
@[simp] lemma totient_cert_1121 : Nat.totient 1121 = 1044 := by
  rw [show 1121 = 19 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 59)]
  rw [totient_cert_19, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_1122 : Nat.totient 1122 = 320 := by
  rw [show 1122 = 2 * 561 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 561)]
  rw [totient_cert_2, totient_cert_561] <;> norm_num
@[simp] lemma totient_cert_1123 : Nat.totient 1123 = 1122 := by
  rw [show 1123 = 1123^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1123) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1124 : Nat.totient 1124 = 560 := by
  rw [show 1124 = 4 * 281 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 281)]
  rw [totient_cert_4, totient_cert_281] <;> norm_num
@[simp] lemma totient_cert_1125 : Nat.totient 1125 = 600 := by
  rw [show 1125 = 9 * 125 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 125)]
  rw [totient_cert_9, totient_cert_125] <;> norm_num
@[simp] lemma totient_cert_1126 : Nat.totient 1126 = 562 := by
  rw [show 1126 = 2 * 563 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 563)]
  rw [totient_cert_2, totient_cert_563] <;> norm_num
@[simp] lemma totient_cert_1127 : Nat.totient 1127 = 924 := by
  rw [show 1127 = 49 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 23)]
  rw [totient_cert_49, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_1128 : Nat.totient 1128 = 368 := by
  rw [show 1128 = 8 * 141 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 141)]
  rw [totient_cert_8, totient_cert_141] <;> norm_num
@[simp] lemma totient_cert_1129 : Nat.totient 1129 = 1128 := by
  rw [show 1129 = 1129^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1129) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1130 : Nat.totient 1130 = 448 := by
  rw [show 1130 = 2 * 565 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 565)]
  rw [totient_cert_2, totient_cert_565] <;> norm_num
@[simp] lemma totient_cert_1131 : Nat.totient 1131 = 672 := by
  rw [show 1131 = 3 * 377 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 377)]
  rw [totient_cert_3, totient_cert_377] <;> norm_num
@[simp] lemma totient_cert_1132 : Nat.totient 1132 = 564 := by
  rw [show 1132 = 4 * 283 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 283)]
  rw [totient_cert_4, totient_cert_283] <;> norm_num
@[simp] lemma totient_cert_1133 : Nat.totient 1133 = 1020 := by
  rw [show 1133 = 11 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 103)]
  rw [totient_cert_11, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_1134 : Nat.totient 1134 = 324 := by
  rw [show 1134 = 2 * 567 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 567)]
  rw [totient_cert_2, totient_cert_567] <;> norm_num
@[simp] lemma totient_cert_1135 : Nat.totient 1135 = 904 := by
  rw [show 1135 = 5 * 227 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 227)]
  rw [totient_cert_5, totient_cert_227] <;> norm_num
@[simp] lemma totient_cert_1136 : Nat.totient 1136 = 560 := by
  rw [show 1136 = 16 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 71)]
  rw [totient_cert_16, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_1137 : Nat.totient 1137 = 756 := by
  rw [show 1137 = 3 * 379 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 379)]
  rw [totient_cert_3, totient_cert_379] <;> norm_num
@[simp] lemma totient_cert_1138 : Nat.totient 1138 = 568 := by
  rw [show 1138 = 2 * 569 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 569)]
  rw [totient_cert_2, totient_cert_569] <;> norm_num
@[simp] lemma totient_cert_1139 : Nat.totient 1139 = 1056 := by
  rw [show 1139 = 17 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 67)]
  rw [totient_cert_17, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_1140 : Nat.totient 1140 = 288 := by
  rw [show 1140 = 4 * 285 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 285)]
  rw [totient_cert_4, totient_cert_285] <;> norm_num
@[simp] lemma totient_cert_1141 : Nat.totient 1141 = 972 := by
  rw [show 1141 = 7 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 163)]
  rw [totient_cert_7, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_1142 : Nat.totient 1142 = 570 := by
  rw [show 1142 = 2 * 571 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 571)]
  rw [totient_cert_2, totient_cert_571] <;> norm_num
@[simp] lemma totient_cert_1143 : Nat.totient 1143 = 756 := by
  rw [show 1143 = 9 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 127)]
  rw [totient_cert_9, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_1144 : Nat.totient 1144 = 480 := by
  rw [show 1144 = 8 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 143)]
  rw [totient_cert_8, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_1145 : Nat.totient 1145 = 912 := by
  rw [show 1145 = 5 * 229 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 229)]
  rw [totient_cert_5, totient_cert_229] <;> norm_num
@[simp] lemma totient_cert_1146 : Nat.totient 1146 = 380 := by
  rw [show 1146 = 2 * 573 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 573)]
  rw [totient_cert_2, totient_cert_573] <;> norm_num
@[simp] lemma totient_cert_1147 : Nat.totient 1147 = 1080 := by
  rw [show 1147 = 31 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 31 37)]
  rw [totient_cert_31, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_1148 : Nat.totient 1148 = 480 := by
  rw [show 1148 = 4 * 287 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 287)]
  rw [totient_cert_4, totient_cert_287] <;> norm_num
@[simp] lemma totient_cert_1149 : Nat.totient 1149 = 764 := by
  rw [show 1149 = 3 * 383 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 383)]
  rw [totient_cert_3, totient_cert_383] <;> norm_num
@[simp] lemma totient_cert_1150 : Nat.totient 1150 = 440 := by
  rw [show 1150 = 2 * 575 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 575)]
  rw [totient_cert_2, totient_cert_575] <;> norm_num
@[simp] lemma totient_cert_1151 : Nat.totient 1151 = 1150 := by
  rw [show 1151 = 1151^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1151) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1152 : Nat.totient 1152 = 384 := by
  rw [show 1152 = 128 * 9 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 128 9)]
  rw [totient_cert_128, totient_cert_9] <;> norm_num
@[simp] lemma totient_cert_1153 : Nat.totient 1153 = 1152 := by
  rw [show 1153 = 1153^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1153) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1154 : Nat.totient 1154 = 576 := by
  rw [show 1154 = 2 * 577 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 577)]
  rw [totient_cert_2, totient_cert_577] <;> norm_num
@[simp] lemma totient_cert_1155 : Nat.totient 1155 = 480 := by
  rw [show 1155 = 3 * 385 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 385)]
  rw [totient_cert_3, totient_cert_385] <;> norm_num
@[simp] lemma totient_cert_1156 : Nat.totient 1156 = 544 := by
  rw [show 1156 = 4 * 289 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 289)]
  rw [totient_cert_4, totient_cert_289] <;> norm_num
@[simp] lemma totient_cert_1157 : Nat.totient 1157 = 1056 := by
  rw [show 1157 = 13 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 89)]
  rw [totient_cert_13, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_1158 : Nat.totient 1158 = 384 := by
  rw [show 1158 = 2 * 579 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 579)]
  rw [totient_cert_2, totient_cert_579] <;> norm_num
@[simp] lemma totient_cert_1159 : Nat.totient 1159 = 1080 := by
  rw [show 1159 = 19 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 61)]
  rw [totient_cert_19, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_1160 : Nat.totient 1160 = 448 := by
  rw [show 1160 = 8 * 145 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 145)]
  rw [totient_cert_8, totient_cert_145] <;> norm_num
@[simp] lemma totient_cert_1161 : Nat.totient 1161 = 756 := by
  rw [show 1161 = 27 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 43)]
  rw [totient_cert_27, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1162 : Nat.totient 1162 = 492 := by
  rw [show 1162 = 2 * 581 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 581)]
  rw [totient_cert_2, totient_cert_581] <;> norm_num
@[simp] lemma totient_cert_1163 : Nat.totient 1163 = 1162 := by
  rw [show 1163 = 1163^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1163) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1164 : Nat.totient 1164 = 384 := by
  rw [show 1164 = 4 * 291 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 291)]
  rw [totient_cert_4, totient_cert_291] <;> norm_num
@[simp] lemma totient_cert_1165 : Nat.totient 1165 = 928 := by
  rw [show 1165 = 5 * 233 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 233)]
  rw [totient_cert_5, totient_cert_233] <;> norm_num
@[simp] lemma totient_cert_1166 : Nat.totient 1166 = 520 := by
  rw [show 1166 = 2 * 583 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 583)]
  rw [totient_cert_2, totient_cert_583] <;> norm_num
@[simp] lemma totient_cert_1167 : Nat.totient 1167 = 776 := by
  rw [show 1167 = 3 * 389 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 389)]
  rw [totient_cert_3, totient_cert_389] <;> norm_num
@[simp] lemma totient_cert_1168 : Nat.totient 1168 = 576 := by
  rw [show 1168 = 16 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 73)]
  rw [totient_cert_16, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_1169 : Nat.totient 1169 = 996 := by
  rw [show 1169 = 7 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 167)]
  rw [totient_cert_7, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_1170 : Nat.totient 1170 = 288 := by
  rw [show 1170 = 2 * 585 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 585)]
  rw [totient_cert_2, totient_cert_585] <;> norm_num
@[simp] lemma totient_cert_1171 : Nat.totient 1171 = 1170 := by
  rw [show 1171 = 1171^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1171) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1172 : Nat.totient 1172 = 584 := by
  rw [show 1172 = 4 * 293 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 293)]
  rw [totient_cert_4, totient_cert_293] <;> norm_num
@[simp] lemma totient_cert_1173 : Nat.totient 1173 = 704 := by
  rw [show 1173 = 3 * 391 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 391)]
  rw [totient_cert_3, totient_cert_391] <;> norm_num
@[simp] lemma totient_cert_1174 : Nat.totient 1174 = 586 := by
  rw [show 1174 = 2 * 587 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 587)]
  rw [totient_cert_2, totient_cert_587] <;> norm_num
@[simp] lemma totient_cert_1175 : Nat.totient 1175 = 920 := by
  rw [show 1175 = 25 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 47)]
  rw [totient_cert_25, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1176 : Nat.totient 1176 = 336 := by
  rw [show 1176 = 8 * 147 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 147)]
  rw [totient_cert_8, totient_cert_147] <;> norm_num
@[simp] lemma totient_cert_1177 : Nat.totient 1177 = 1060 := by
  rw [show 1177 = 11 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 107)]
  rw [totient_cert_11, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_1178 : Nat.totient 1178 = 540 := by
  rw [show 1178 = 2 * 589 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 589)]
  rw [totient_cert_2, totient_cert_589] <;> norm_num
@[simp] lemma totient_cert_1179 : Nat.totient 1179 = 780 := by
  rw [show 1179 = 9 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 131)]
  rw [totient_cert_9, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_1180 : Nat.totient 1180 = 464 := by
  rw [show 1180 = 4 * 295 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 295)]
  rw [totient_cert_4, totient_cert_295] <;> norm_num
@[simp] lemma totient_cert_1181 : Nat.totient 1181 = 1180 := by
  rw [show 1181 = 1181^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1181) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1182 : Nat.totient 1182 = 392 := by
  rw [show 1182 = 2 * 591 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 591)]
  rw [totient_cert_2, totient_cert_591] <;> norm_num
@[simp] lemma totient_cert_1183 : Nat.totient 1183 = 936 := by
  rw [show 1183 = 7 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 169)]
  rw [totient_cert_7, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_1184 : Nat.totient 1184 = 576 := by
  rw [show 1184 = 32 * 37 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 37)]
  rw [totient_cert_32, totient_cert_37] <;> norm_num
@[simp] lemma totient_cert_1185 : Nat.totient 1185 = 624 := by
  rw [show 1185 = 3 * 395 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 395)]
  rw [totient_cert_3, totient_cert_395] <;> norm_num
@[simp] lemma totient_cert_1186 : Nat.totient 1186 = 592 := by
  rw [show 1186 = 2 * 593 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 593)]
  rw [totient_cert_2, totient_cert_593] <;> norm_num
@[simp] lemma totient_cert_1187 : Nat.totient 1187 = 1186 := by
  rw [show 1187 = 1187^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1187) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1188 : Nat.totient 1188 = 360 := by
  rw [show 1188 = 4 * 297 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 297)]
  rw [totient_cert_4, totient_cert_297] <;> norm_num
@[simp] lemma totient_cert_1189 : Nat.totient 1189 = 1120 := by
  rw [show 1189 = 29 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 41)]
  rw [totient_cert_29, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_1190 : Nat.totient 1190 = 384 := by
  rw [show 1190 = 2 * 595 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 595)]
  rw [totient_cert_2, totient_cert_595] <;> norm_num
@[simp] lemma totient_cert_1191 : Nat.totient 1191 = 792 := by
  rw [show 1191 = 3 * 397 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 397)]
  rw [totient_cert_3, totient_cert_397] <;> norm_num
@[simp] lemma totient_cert_1192 : Nat.totient 1192 = 592 := by
  rw [show 1192 = 8 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 149)]
  rw [totient_cert_8, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_1193 : Nat.totient 1193 = 1192 := by
  rw [show 1193 = 1193^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1193) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1194 : Nat.totient 1194 = 396 := by
  rw [show 1194 = 2 * 597 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 597)]
  rw [totient_cert_2, totient_cert_597] <;> norm_num
@[simp] lemma totient_cert_1195 : Nat.totient 1195 = 952 := by
  rw [show 1195 = 5 * 239 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 239)]
  rw [totient_cert_5, totient_cert_239] <;> norm_num
@[simp] lemma totient_cert_1196 : Nat.totient 1196 = 528 := by
  rw [show 1196 = 4 * 299 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 299)]
  rw [totient_cert_4, totient_cert_299] <;> norm_num
@[simp] lemma totient_cert_1197 : Nat.totient 1197 = 648 := by
  rw [show 1197 = 9 * 133 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 133)]
  rw [totient_cert_9, totient_cert_133] <;> norm_num
@[simp] lemma totient_cert_1198 : Nat.totient 1198 = 598 := by
  rw [show 1198 = 2 * 599 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 599)]
  rw [totient_cert_2, totient_cert_599] <;> norm_num
@[simp] lemma totient_cert_1199 : Nat.totient 1199 = 1080 := by
  rw [show 1199 = 11 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 109)]
  rw [totient_cert_11, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_1200 : Nat.totient 1200 = 320 := by
  rw [show 1200 = 16 * 75 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 75)]
  rw [totient_cert_16, totient_cert_75] <;> norm_num
@[simp] lemma totient_cert_1201 : Nat.totient 1201 = 1200 := by
  rw [show 1201 = 1201^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1201) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1202 : Nat.totient 1202 = 600 := by
  rw [show 1202 = 2 * 601 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 601)]
  rw [totient_cert_2, totient_cert_601] <;> norm_num
@[simp] lemma totient_cert_1203 : Nat.totient 1203 = 800 := by
  rw [show 1203 = 3 * 401 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 401)]
  rw [totient_cert_3, totient_cert_401] <;> norm_num
@[simp] lemma totient_cert_1204 : Nat.totient 1204 = 504 := by
  rw [show 1204 = 4 * 301 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 301)]
  rw [totient_cert_4, totient_cert_301] <;> norm_num
@[simp] lemma totient_cert_1205 : Nat.totient 1205 = 960 := by
  rw [show 1205 = 5 * 241 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 241)]
  rw [totient_cert_5, totient_cert_241] <;> norm_num
@[simp] lemma totient_cert_1206 : Nat.totient 1206 = 396 := by
  rw [show 1206 = 2 * 603 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 603)]
  rw [totient_cert_2, totient_cert_603] <;> norm_num
@[simp] lemma totient_cert_1207 : Nat.totient 1207 = 1120 := by
  rw [show 1207 = 17 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 71)]
  rw [totient_cert_17, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_1208 : Nat.totient 1208 = 600 := by
  rw [show 1208 = 8 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 151)]
  rw [totient_cert_8, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_1209 : Nat.totient 1209 = 720 := by
  rw [show 1209 = 3 * 403 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 403)]
  rw [totient_cert_3, totient_cert_403] <;> norm_num
@[simp] lemma totient_cert_1210 : Nat.totient 1210 = 440 := by
  rw [show 1210 = 2 * 605 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 605)]
  rw [totient_cert_2, totient_cert_605] <;> norm_num
@[simp] lemma totient_cert_1211 : Nat.totient 1211 = 1032 := by
  rw [show 1211 = 7 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 173)]
  rw [totient_cert_7, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_1212 : Nat.totient 1212 = 400 := by
  rw [show 1212 = 4 * 303 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 303)]
  rw [totient_cert_4, totient_cert_303] <;> norm_num
@[simp] lemma totient_cert_1213 : Nat.totient 1213 = 1212 := by
  rw [show 1213 = 1213^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1213) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1214 : Nat.totient 1214 = 606 := by
  rw [show 1214 = 2 * 607 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 607)]
  rw [totient_cert_2, totient_cert_607] <;> norm_num
@[simp] lemma totient_cert_1215 : Nat.totient 1215 = 648 := by
  rw [show 1215 = 243 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 243 5)]
  rw [totient_cert_243, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_1216 : Nat.totient 1216 = 576 := by
  rw [show 1216 = 64 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 19)]
  rw [totient_cert_64, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_1217 : Nat.totient 1217 = 1216 := by
  rw [show 1217 = 1217^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1217) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1218 : Nat.totient 1218 = 336 := by
  rw [show 1218 = 2 * 609 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 609)]
  rw [totient_cert_2, totient_cert_609] <;> norm_num
@[simp] lemma totient_cert_1219 : Nat.totient 1219 = 1144 := by
  rw [show 1219 = 23 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 53)]
  rw [totient_cert_23, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1220 : Nat.totient 1220 = 480 := by
  rw [show 1220 = 4 * 305 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 305)]
  rw [totient_cert_4, totient_cert_305] <;> norm_num
@[simp] lemma totient_cert_1221 : Nat.totient 1221 = 720 := by
  rw [show 1221 = 3 * 407 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 407)]
  rw [totient_cert_3, totient_cert_407] <;> norm_num
@[simp] lemma totient_cert_1222 : Nat.totient 1222 = 552 := by
  rw [show 1222 = 2 * 611 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 611)]
  rw [totient_cert_2, totient_cert_611] <;> norm_num
@[simp] lemma totient_cert_1223 : Nat.totient 1223 = 1222 := by
  rw [show 1223 = 1223^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1223) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1224 : Nat.totient 1224 = 384 := by
  rw [show 1224 = 8 * 153 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 153)]
  rw [totient_cert_8, totient_cert_153] <;> norm_num
@[simp] lemma totient_cert_1225 : Nat.totient 1225 = 840 := by
  rw [show 1225 = 25 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 49)]
  rw [totient_cert_25, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_1226 : Nat.totient 1226 = 612 := by
  rw [show 1226 = 2 * 613 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 613)]
  rw [totient_cert_2, totient_cert_613] <;> norm_num
@[simp] lemma totient_cert_1227 : Nat.totient 1227 = 816 := by
  rw [show 1227 = 3 * 409 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 409)]
  rw [totient_cert_3, totient_cert_409] <;> norm_num
@[simp] lemma totient_cert_1228 : Nat.totient 1228 = 612 := by
  rw [show 1228 = 4 * 307 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 307)]
  rw [totient_cert_4, totient_cert_307] <;> norm_num
@[simp] lemma totient_cert_1229 : Nat.totient 1229 = 1228 := by
  rw [show 1229 = 1229^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1229) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1230 : Nat.totient 1230 = 320 := by
  rw [show 1230 = 2 * 615 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 615)]
  rw [totient_cert_2, totient_cert_615] <;> norm_num
@[simp] lemma totient_cert_1231 : Nat.totient 1231 = 1230 := by
  rw [show 1231 = 1231^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1231) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1232 : Nat.totient 1232 = 480 := by
  rw [show 1232 = 16 * 77 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 77)]
  rw [totient_cert_16, totient_cert_77] <;> norm_num
@[simp] lemma totient_cert_1233 : Nat.totient 1233 = 816 := by
  rw [show 1233 = 9 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 137)]
  rw [totient_cert_9, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_1234 : Nat.totient 1234 = 616 := by
  rw [show 1234 = 2 * 617 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 617)]
  rw [totient_cert_2, totient_cert_617] <;> norm_num
@[simp] lemma totient_cert_1235 : Nat.totient 1235 = 864 := by
  rw [show 1235 = 5 * 247 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 247)]
  rw [totient_cert_5, totient_cert_247] <;> norm_num
@[simp] lemma totient_cert_1236 : Nat.totient 1236 = 408 := by
  rw [show 1236 = 4 * 309 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 309)]
  rw [totient_cert_4, totient_cert_309] <;> norm_num
@[simp] lemma totient_cert_1237 : Nat.totient 1237 = 1236 := by
  rw [show 1237 = 1237^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1237) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1238 : Nat.totient 1238 = 618 := by
  rw [show 1238 = 2 * 619 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 619)]
  rw [totient_cert_2, totient_cert_619] <;> norm_num
@[simp] lemma totient_cert_1239 : Nat.totient 1239 = 696 := by
  rw [show 1239 = 3 * 413 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 413)]
  rw [totient_cert_3, totient_cert_413] <;> norm_num
@[simp] lemma totient_cert_1240 : Nat.totient 1240 = 480 := by
  rw [show 1240 = 8 * 155 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 155)]
  rw [totient_cert_8, totient_cert_155] <;> norm_num
@[simp] lemma totient_cert_1241 : Nat.totient 1241 = 1152 := by
  rw [show 1241 = 17 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 73)]
  rw [totient_cert_17, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_1242 : Nat.totient 1242 = 396 := by
  rw [show 1242 = 2 * 621 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 621)]
  rw [totient_cert_2, totient_cert_621] <;> norm_num
@[simp] lemma totient_cert_1243 : Nat.totient 1243 = 1120 := by
  rw [show 1243 = 11 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 113)]
  rw [totient_cert_11, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_1244 : Nat.totient 1244 = 620 := by
  rw [show 1244 = 4 * 311 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 311)]
  rw [totient_cert_4, totient_cert_311] <;> norm_num
@[simp] lemma totient_cert_1245 : Nat.totient 1245 = 656 := by
  rw [show 1245 = 3 * 415 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 415)]
  rw [totient_cert_3, totient_cert_415] <;> norm_num
@[simp] lemma totient_cert_1246 : Nat.totient 1246 = 528 := by
  rw [show 1246 = 2 * 623 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 623)]
  rw [totient_cert_2, totient_cert_623] <;> norm_num
@[simp] lemma totient_cert_1247 : Nat.totient 1247 = 1176 := by
  rw [show 1247 = 29 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 43)]
  rw [totient_cert_29, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1248 : Nat.totient 1248 = 384 := by
  rw [show 1248 = 32 * 39 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 39)]
  rw [totient_cert_32, totient_cert_39] <;> norm_num
@[simp] lemma totient_cert_1249 : Nat.totient 1249 = 1248 := by
  rw [show 1249 = 1249^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1249) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1250 : Nat.totient 1250 = 500 := by
  rw [show 1250 = 2 * 625 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 625)]
  rw [totient_cert_2, totient_cert_625] <;> norm_num
@[simp] lemma totient_cert_1251 : Nat.totient 1251 = 828 := by
  rw [show 1251 = 9 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 139)]
  rw [totient_cert_9, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_1252 : Nat.totient 1252 = 624 := by
  rw [show 1252 = 4 * 313 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 313)]
  rw [totient_cert_4, totient_cert_313] <;> norm_num
@[simp] lemma totient_cert_1253 : Nat.totient 1253 = 1068 := by
  rw [show 1253 = 7 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 179)]
  rw [totient_cert_7, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_1254 : Nat.totient 1254 = 360 := by
  rw [show 1254 = 2 * 627 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 627)]
  rw [totient_cert_2, totient_cert_627] <;> norm_num
@[simp] lemma totient_cert_1255 : Nat.totient 1255 = 1000 := by
  rw [show 1255 = 5 * 251 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 251)]
  rw [totient_cert_5, totient_cert_251] <;> norm_num
@[simp] lemma totient_cert_1256 : Nat.totient 1256 = 624 := by
  rw [show 1256 = 8 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 157)]
  rw [totient_cert_8, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_1257 : Nat.totient 1257 = 836 := by
  rw [show 1257 = 3 * 419 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 419)]
  rw [totient_cert_3, totient_cert_419] <;> norm_num
@[simp] lemma totient_cert_1258 : Nat.totient 1258 = 576 := by
  rw [show 1258 = 2 * 629 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 629)]
  rw [totient_cert_2, totient_cert_629] <;> norm_num
@[simp] lemma totient_cert_1259 : Nat.totient 1259 = 1258 := by
  rw [show 1259 = 1259^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1259) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1260 : Nat.totient 1260 = 288 := by
  rw [show 1260 = 4 * 315 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 315)]
  rw [totient_cert_4, totient_cert_315] <;> norm_num
@[simp] lemma totient_cert_1261 : Nat.totient 1261 = 1152 := by
  rw [show 1261 = 13 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 97)]
  rw [totient_cert_13, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_1262 : Nat.totient 1262 = 630 := by
  rw [show 1262 = 2 * 631 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 631)]
  rw [totient_cert_2, totient_cert_631] <;> norm_num
@[simp] lemma totient_cert_1263 : Nat.totient 1263 = 840 := by
  rw [show 1263 = 3 * 421 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 421)]
  rw [totient_cert_3, totient_cert_421] <;> norm_num
@[simp] lemma totient_cert_1264 : Nat.totient 1264 = 624 := by
  rw [show 1264 = 16 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 79)]
  rw [totient_cert_16, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_1265 : Nat.totient 1265 = 880 := by
  rw [show 1265 = 5 * 253 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 253)]
  rw [totient_cert_5, totient_cert_253] <;> norm_num
@[simp] lemma totient_cert_1266 : Nat.totient 1266 = 420 := by
  rw [show 1266 = 2 * 633 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 633)]
  rw [totient_cert_2, totient_cert_633] <;> norm_num
@[simp] lemma totient_cert_1267 : Nat.totient 1267 = 1080 := by
  rw [show 1267 = 7 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 181)]
  rw [totient_cert_7, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_1268 : Nat.totient 1268 = 632 := by
  rw [show 1268 = 4 * 317 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 317)]
  rw [totient_cert_4, totient_cert_317] <;> norm_num
@[simp] lemma totient_cert_1269 : Nat.totient 1269 = 828 := by
  rw [show 1269 = 27 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 47)]
  rw [totient_cert_27, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1270 : Nat.totient 1270 = 504 := by
  rw [show 1270 = 2 * 635 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 635)]
  rw [totient_cert_2, totient_cert_635] <;> norm_num
@[simp] lemma totient_cert_1271 : Nat.totient 1271 = 1200 := by
  rw [show 1271 = 31 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 31 41)]
  rw [totient_cert_31, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_1272 : Nat.totient 1272 = 416 := by
  rw [show 1272 = 8 * 159 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 159)]
  rw [totient_cert_8, totient_cert_159] <;> norm_num
@[simp] lemma totient_cert_1273 : Nat.totient 1273 = 1188 := by
  rw [show 1273 = 19 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 67)]
  rw [totient_cert_19, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_1274 : Nat.totient 1274 = 504 := by
  rw [show 1274 = 2 * 637 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 637)]
  rw [totient_cert_2, totient_cert_637] <;> norm_num
@[simp] lemma totient_cert_1275 : Nat.totient 1275 = 640 := by
  rw [show 1275 = 3 * 425 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 425)]
  rw [totient_cert_3, totient_cert_425] <;> norm_num
@[simp] lemma totient_cert_1276 : Nat.totient 1276 = 560 := by
  rw [show 1276 = 4 * 319 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 319)]
  rw [totient_cert_4, totient_cert_319] <;> norm_num
@[simp] lemma totient_cert_1277 : Nat.totient 1277 = 1276 := by
  rw [show 1277 = 1277^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1277) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1278 : Nat.totient 1278 = 420 := by
  rw [show 1278 = 2 * 639 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 639)]
  rw [totient_cert_2, totient_cert_639] <;> norm_num
@[simp] lemma totient_cert_1279 : Nat.totient 1279 = 1278 := by
  rw [show 1279 = 1279^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1279) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1280 : Nat.totient 1280 = 512 := by
  rw [show 1280 = 256 * 5 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 256 5)]
  rw [totient_cert_256, totient_cert_5] <;> norm_num
@[simp] lemma totient_cert_1281 : Nat.totient 1281 = 720 := by
  rw [show 1281 = 3 * 427 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 427)]
  rw [totient_cert_3, totient_cert_427] <;> norm_num
@[simp] lemma totient_cert_1282 : Nat.totient 1282 = 640 := by
  rw [show 1282 = 2 * 641 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 641)]
  rw [totient_cert_2, totient_cert_641] <;> norm_num
@[simp] lemma totient_cert_1283 : Nat.totient 1283 = 1282 := by
  rw [show 1283 = 1283^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1283) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1284 : Nat.totient 1284 = 424 := by
  rw [show 1284 = 4 * 321 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 321)]
  rw [totient_cert_4, totient_cert_321] <;> norm_num
@[simp] lemma totient_cert_1285 : Nat.totient 1285 = 1024 := by
  rw [show 1285 = 5 * 257 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 257)]
  rw [totient_cert_5, totient_cert_257] <;> norm_num
@[simp] lemma totient_cert_1286 : Nat.totient 1286 = 642 := by
  rw [show 1286 = 2 * 643 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 643)]
  rw [totient_cert_2, totient_cert_643] <;> norm_num
@[simp] lemma totient_cert_1287 : Nat.totient 1287 = 720 := by
  rw [show 1287 = 9 * 143 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 143)]
  rw [totient_cert_9, totient_cert_143] <;> norm_num
@[simp] lemma totient_cert_1288 : Nat.totient 1288 = 528 := by
  rw [show 1288 = 8 * 161 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 161)]
  rw [totient_cert_8, totient_cert_161] <;> norm_num
@[simp] lemma totient_cert_1289 : Nat.totient 1289 = 1288 := by
  rw [show 1289 = 1289^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1289) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1290 : Nat.totient 1290 = 336 := by
  rw [show 1290 = 2 * 645 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 645)]
  rw [totient_cert_2, totient_cert_645] <;> norm_num
@[simp] lemma totient_cert_1291 : Nat.totient 1291 = 1290 := by
  rw [show 1291 = 1291^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1291) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1292 : Nat.totient 1292 = 576 := by
  rw [show 1292 = 4 * 323 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 323)]
  rw [totient_cert_4, totient_cert_323] <;> norm_num
@[simp] lemma totient_cert_1293 : Nat.totient 1293 = 860 := by
  rw [show 1293 = 3 * 431 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 431)]
  rw [totient_cert_3, totient_cert_431] <;> norm_num
@[simp] lemma totient_cert_1294 : Nat.totient 1294 = 646 := by
  rw [show 1294 = 2 * 647 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 647)]
  rw [totient_cert_2, totient_cert_647] <;> norm_num
@[simp] lemma totient_cert_1295 : Nat.totient 1295 = 864 := by
  rw [show 1295 = 5 * 259 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 259)]
  rw [totient_cert_5, totient_cert_259] <;> norm_num
@[simp] lemma totient_cert_1296 : Nat.totient 1296 = 432 := by
  rw [show 1296 = 16 * 81 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 81)]
  rw [totient_cert_16, totient_cert_81] <;> norm_num
@[simp] lemma totient_cert_1297 : Nat.totient 1297 = 1296 := by
  rw [show 1297 = 1297^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1297) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1298 : Nat.totient 1298 = 580 := by
  rw [show 1298 = 2 * 649 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 649)]
  rw [totient_cert_2, totient_cert_649] <;> norm_num
@[simp] lemma totient_cert_1299 : Nat.totient 1299 = 864 := by
  rw [show 1299 = 3 * 433 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 433)]
  rw [totient_cert_3, totient_cert_433] <;> norm_num
@[simp] lemma totient_cert_1300 : Nat.totient 1300 = 480 := by
  rw [show 1300 = 4 * 325 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 325)]
  rw [totient_cert_4, totient_cert_325] <;> norm_num
@[simp] lemma totient_cert_1301 : Nat.totient 1301 = 1300 := by
  rw [show 1301 = 1301^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1301) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1302 : Nat.totient 1302 = 360 := by
  rw [show 1302 = 2 * 651 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 651)]
  rw [totient_cert_2, totient_cert_651] <;> norm_num
@[simp] lemma totient_cert_1303 : Nat.totient 1303 = 1302 := by
  rw [show 1303 = 1303^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1303) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1304 : Nat.totient 1304 = 648 := by
  rw [show 1304 = 8 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 163)]
  rw [totient_cert_8, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_1305 : Nat.totient 1305 = 672 := by
  rw [show 1305 = 9 * 145 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 145)]
  rw [totient_cert_9, totient_cert_145] <;> norm_num
@[simp] lemma totient_cert_1306 : Nat.totient 1306 = 652 := by
  rw [show 1306 = 2 * 653 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 653)]
  rw [totient_cert_2, totient_cert_653] <;> norm_num
@[simp] lemma totient_cert_1307 : Nat.totient 1307 = 1306 := by
  rw [show 1307 = 1307^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1307) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1308 : Nat.totient 1308 = 432 := by
  rw [show 1308 = 4 * 327 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 327)]
  rw [totient_cert_4, totient_cert_327] <;> norm_num
@[simp] lemma totient_cert_1309 : Nat.totient 1309 = 960 := by
  rw [show 1309 = 7 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 187)]
  rw [totient_cert_7, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_1310 : Nat.totient 1310 = 520 := by
  rw [show 1310 = 2 * 655 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 655)]
  rw [totient_cert_2, totient_cert_655] <;> norm_num
@[simp] lemma totient_cert_1311 : Nat.totient 1311 = 792 := by
  rw [show 1311 = 3 * 437 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 437)]
  rw [totient_cert_3, totient_cert_437] <;> norm_num
@[simp] lemma totient_cert_1312 : Nat.totient 1312 = 640 := by
  rw [show 1312 = 32 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 41)]
  rw [totient_cert_32, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_1313 : Nat.totient 1313 = 1200 := by
  rw [show 1313 = 13 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 101)]
  rw [totient_cert_13, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_1314 : Nat.totient 1314 = 432 := by
  rw [show 1314 = 2 * 657 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 657)]
  rw [totient_cert_2, totient_cert_657] <;> norm_num
@[simp] lemma totient_cert_1315 : Nat.totient 1315 = 1048 := by
  rw [show 1315 = 5 * 263 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 263)]
  rw [totient_cert_5, totient_cert_263] <;> norm_num
@[simp] lemma totient_cert_1316 : Nat.totient 1316 = 552 := by
  rw [show 1316 = 4 * 329 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 329)]
  rw [totient_cert_4, totient_cert_329] <;> norm_num
@[simp] lemma totient_cert_1317 : Nat.totient 1317 = 876 := by
  rw [show 1317 = 3 * 439 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 439)]
  rw [totient_cert_3, totient_cert_439] <;> norm_num
@[simp] lemma totient_cert_1318 : Nat.totient 1318 = 658 := by
  rw [show 1318 = 2 * 659 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 659)]
  rw [totient_cert_2, totient_cert_659] <;> norm_num
@[simp] lemma totient_cert_1319 : Nat.totient 1319 = 1318 := by
  rw [show 1319 = 1319^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1319) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1320 : Nat.totient 1320 = 320 := by
  rw [show 1320 = 8 * 165 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 165)]
  rw [totient_cert_8, totient_cert_165] <;> norm_num
@[simp] lemma totient_cert_1321 : Nat.totient 1321 = 1320 := by
  rw [show 1321 = 1321^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1321) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1322 : Nat.totient 1322 = 660 := by
  rw [show 1322 = 2 * 661 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 661)]
  rw [totient_cert_2, totient_cert_661] <;> norm_num
@[simp] lemma totient_cert_1323 : Nat.totient 1323 = 756 := by
  rw [show 1323 = 27 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 49)]
  rw [totient_cert_27, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_1324 : Nat.totient 1324 = 660 := by
  rw [show 1324 = 4 * 331 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 331)]
  rw [totient_cert_4, totient_cert_331] <;> norm_num
@[simp] lemma totient_cert_1325 : Nat.totient 1325 = 1040 := by
  rw [show 1325 = 25 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 53)]
  rw [totient_cert_25, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1326 : Nat.totient 1326 = 384 := by
  rw [show 1326 = 2 * 663 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 663)]
  rw [totient_cert_2, totient_cert_663] <;> norm_num
@[simp] lemma totient_cert_1327 : Nat.totient 1327 = 1326 := by
  rw [show 1327 = 1327^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1327) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1328 : Nat.totient 1328 = 656 := by
  rw [show 1328 = 16 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 83)]
  rw [totient_cert_16, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_1329 : Nat.totient 1329 = 884 := by
  rw [show 1329 = 3 * 443 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 443)]
  rw [totient_cert_3, totient_cert_443] <;> norm_num
@[simp] lemma totient_cert_1330 : Nat.totient 1330 = 432 := by
  rw [show 1330 = 2 * 665 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 665)]
  rw [totient_cert_2, totient_cert_665] <;> norm_num
@[simp] lemma totient_cert_1331 : Nat.totient 1331 = 1210 := by
  rw [show 1331 = 11^3 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 11) (by norm_num : 0 < 3)] <;> norm_num
@[simp] lemma totient_cert_1332 : Nat.totient 1332 = 432 := by
  rw [show 1332 = 4 * 333 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 333)]
  rw [totient_cert_4, totient_cert_333] <;> norm_num
@[simp] lemma totient_cert_1333 : Nat.totient 1333 = 1260 := by
  rw [show 1333 = 31 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 31 43)]
  rw [totient_cert_31, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1334 : Nat.totient 1334 = 616 := by
  rw [show 1334 = 2 * 667 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 667)]
  rw [totient_cert_2, totient_cert_667] <;> norm_num
@[simp] lemma totient_cert_1335 : Nat.totient 1335 = 704 := by
  rw [show 1335 = 3 * 445 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 445)]
  rw [totient_cert_3, totient_cert_445] <;> norm_num
@[simp] lemma totient_cert_1336 : Nat.totient 1336 = 664 := by
  rw [show 1336 = 8 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 167)]
  rw [totient_cert_8, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_1337 : Nat.totient 1337 = 1140 := by
  rw [show 1337 = 7 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 191)]
  rw [totient_cert_7, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_1338 : Nat.totient 1338 = 444 := by
  rw [show 1338 = 2 * 669 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 669)]
  rw [totient_cert_2, totient_cert_669] <;> norm_num
@[simp] lemma totient_cert_1339 : Nat.totient 1339 = 1224 := by
  rw [show 1339 = 13 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 103)]
  rw [totient_cert_13, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_1340 : Nat.totient 1340 = 528 := by
  rw [show 1340 = 4 * 335 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 335)]
  rw [totient_cert_4, totient_cert_335] <;> norm_num
@[simp] lemma totient_cert_1341 : Nat.totient 1341 = 888 := by
  rw [show 1341 = 9 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 149)]
  rw [totient_cert_9, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_1342 : Nat.totient 1342 = 600 := by
  rw [show 1342 = 2 * 671 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 671)]
  rw [totient_cert_2, totient_cert_671] <;> norm_num
@[simp] lemma totient_cert_1343 : Nat.totient 1343 = 1248 := by
  rw [show 1343 = 17 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 79)]
  rw [totient_cert_17, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_1344 : Nat.totient 1344 = 384 := by
  rw [show 1344 = 64 * 21 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 21)]
  rw [totient_cert_64, totient_cert_21] <;> norm_num
@[simp] lemma totient_cert_1345 : Nat.totient 1345 = 1072 := by
  rw [show 1345 = 5 * 269 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 269)]
  rw [totient_cert_5, totient_cert_269] <;> norm_num
@[simp] lemma totient_cert_1346 : Nat.totient 1346 = 672 := by
  rw [show 1346 = 2 * 673 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 673)]
  rw [totient_cert_2, totient_cert_673] <;> norm_num
@[simp] lemma totient_cert_1347 : Nat.totient 1347 = 896 := by
  rw [show 1347 = 3 * 449 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 449)]
  rw [totient_cert_3, totient_cert_449] <;> norm_num
@[simp] lemma totient_cert_1348 : Nat.totient 1348 = 672 := by
  rw [show 1348 = 4 * 337 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 337)]
  rw [totient_cert_4, totient_cert_337] <;> norm_num
@[simp] lemma totient_cert_1349 : Nat.totient 1349 = 1260 := by
  rw [show 1349 = 19 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 71)]
  rw [totient_cert_19, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_1350 : Nat.totient 1350 = 360 := by
  rw [show 1350 = 2 * 675 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 675)]
  rw [totient_cert_2, totient_cert_675] <;> norm_num
@[simp] lemma totient_cert_1351 : Nat.totient 1351 = 1152 := by
  rw [show 1351 = 7 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 193)]
  rw [totient_cert_7, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_1352 : Nat.totient 1352 = 624 := by
  rw [show 1352 = 8 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 169)]
  rw [totient_cert_8, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_1353 : Nat.totient 1353 = 800 := by
  rw [show 1353 = 3 * 451 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 451)]
  rw [totient_cert_3, totient_cert_451] <;> norm_num
@[simp] lemma totient_cert_1354 : Nat.totient 1354 = 676 := by
  rw [show 1354 = 2 * 677 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 677)]
  rw [totient_cert_2, totient_cert_677] <;> norm_num
@[simp] lemma totient_cert_1355 : Nat.totient 1355 = 1080 := by
  rw [show 1355 = 5 * 271 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 271)]
  rw [totient_cert_5, totient_cert_271] <;> norm_num
@[simp] lemma totient_cert_1356 : Nat.totient 1356 = 448 := by
  rw [show 1356 = 4 * 339 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 339)]
  rw [totient_cert_4, totient_cert_339] <;> norm_num
@[simp] lemma totient_cert_1357 : Nat.totient 1357 = 1276 := by
  rw [show 1357 = 23 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 59)]
  rw [totient_cert_23, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_1358 : Nat.totient 1358 = 576 := by
  rw [show 1358 = 2 * 679 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 679)]
  rw [totient_cert_2, totient_cert_679] <;> norm_num
@[simp] lemma totient_cert_1359 : Nat.totient 1359 = 900 := by
  rw [show 1359 = 9 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 151)]
  rw [totient_cert_9, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_1360 : Nat.totient 1360 = 512 := by
  rw [show 1360 = 16 * 85 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 85)]
  rw [totient_cert_16, totient_cert_85] <;> norm_num
@[simp] lemma totient_cert_1361 : Nat.totient 1361 = 1360 := by
  rw [show 1361 = 1361^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1361) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1362 : Nat.totient 1362 = 452 := by
  rw [show 1362 = 2 * 681 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 681)]
  rw [totient_cert_2, totient_cert_681] <;> norm_num
@[simp] lemma totient_cert_1363 : Nat.totient 1363 = 1288 := by
  rw [show 1363 = 29 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 47)]
  rw [totient_cert_29, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1364 : Nat.totient 1364 = 600 := by
  rw [show 1364 = 4 * 341 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 341)]
  rw [totient_cert_4, totient_cert_341] <;> norm_num
@[simp] lemma totient_cert_1365 : Nat.totient 1365 = 576 := by
  rw [show 1365 = 3 * 455 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 455)]
  rw [totient_cert_3, totient_cert_455] <;> norm_num
@[simp] lemma totient_cert_1366 : Nat.totient 1366 = 682 := by
  rw [show 1366 = 2 * 683 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 683)]
  rw [totient_cert_2, totient_cert_683] <;> norm_num
@[simp] lemma totient_cert_1367 : Nat.totient 1367 = 1366 := by
  rw [show 1367 = 1367^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1367) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1368 : Nat.totient 1368 = 432 := by
  rw [show 1368 = 8 * 171 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 171)]
  rw [totient_cert_8, totient_cert_171] <;> norm_num
@[simp] lemma totient_cert_1369 : Nat.totient 1369 = 1332 := by
  rw [show 1369 = 37^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 37) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_1370 : Nat.totient 1370 = 544 := by
  rw [show 1370 = 2 * 685 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 685)]
  rw [totient_cert_2, totient_cert_685] <;> norm_num
@[simp] lemma totient_cert_1371 : Nat.totient 1371 = 912 := by
  rw [show 1371 = 3 * 457 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 457)]
  rw [totient_cert_3, totient_cert_457] <;> norm_num
@[simp] lemma totient_cert_1372 : Nat.totient 1372 = 588 := by
  rw [show 1372 = 4 * 343 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 343)]
  rw [totient_cert_4, totient_cert_343] <;> norm_num
@[simp] lemma totient_cert_1373 : Nat.totient 1373 = 1372 := by
  rw [show 1373 = 1373^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1373) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1374 : Nat.totient 1374 = 456 := by
  rw [show 1374 = 2 * 687 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 687)]
  rw [totient_cert_2, totient_cert_687] <;> norm_num
@[simp] lemma totient_cert_1375 : Nat.totient 1375 = 1000 := by
  rw [show 1375 = 125 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 125 11)]
  rw [totient_cert_125, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_1376 : Nat.totient 1376 = 672 := by
  rw [show 1376 = 32 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 43)]
  rw [totient_cert_32, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1377 : Nat.totient 1377 = 864 := by
  rw [show 1377 = 81 * 17 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 81 17)]
  rw [totient_cert_81, totient_cert_17] <;> norm_num
@[simp] lemma totient_cert_1378 : Nat.totient 1378 = 624 := by
  rw [show 1378 = 2 * 689 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 689)]
  rw [totient_cert_2, totient_cert_689] <;> norm_num
@[simp] lemma totient_cert_1379 : Nat.totient 1379 = 1176 := by
  rw [show 1379 = 7 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 197)]
  rw [totient_cert_7, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_1380 : Nat.totient 1380 = 352 := by
  rw [show 1380 = 4 * 345 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 345)]
  rw [totient_cert_4, totient_cert_345] <;> norm_num
@[simp] lemma totient_cert_1381 : Nat.totient 1381 = 1380 := by
  rw [show 1381 = 1381^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1381) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1382 : Nat.totient 1382 = 690 := by
  rw [show 1382 = 2 * 691 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 691)]
  rw [totient_cert_2, totient_cert_691] <;> norm_num
@[simp] lemma totient_cert_1383 : Nat.totient 1383 = 920 := by
  rw [show 1383 = 3 * 461 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 461)]
  rw [totient_cert_3, totient_cert_461] <;> norm_num
@[simp] lemma totient_cert_1384 : Nat.totient 1384 = 688 := by
  rw [show 1384 = 8 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 173)]
  rw [totient_cert_8, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_1385 : Nat.totient 1385 = 1104 := by
  rw [show 1385 = 5 * 277 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 277)]
  rw [totient_cert_5, totient_cert_277] <;> norm_num
@[simp] lemma totient_cert_1386 : Nat.totient 1386 = 360 := by
  rw [show 1386 = 2 * 693 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 693)]
  rw [totient_cert_2, totient_cert_693] <;> norm_num
@[simp] lemma totient_cert_1387 : Nat.totient 1387 = 1296 := by
  rw [show 1387 = 19 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 73)]
  rw [totient_cert_19, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_1388 : Nat.totient 1388 = 692 := by
  rw [show 1388 = 4 * 347 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 347)]
  rw [totient_cert_4, totient_cert_347] <;> norm_num
@[simp] lemma totient_cert_1389 : Nat.totient 1389 = 924 := by
  rw [show 1389 = 3 * 463 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 463)]
  rw [totient_cert_3, totient_cert_463] <;> norm_num
@[simp] lemma totient_cert_1390 : Nat.totient 1390 = 552 := by
  rw [show 1390 = 2 * 695 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 695)]
  rw [totient_cert_2, totient_cert_695] <;> norm_num
@[simp] lemma totient_cert_1391 : Nat.totient 1391 = 1272 := by
  rw [show 1391 = 13 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 107)]
  rw [totient_cert_13, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_1392 : Nat.totient 1392 = 448 := by
  rw [show 1392 = 16 * 87 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 87)]
  rw [totient_cert_16, totient_cert_87] <;> norm_num
@[simp] lemma totient_cert_1393 : Nat.totient 1393 = 1188 := by
  rw [show 1393 = 7 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 199)]
  rw [totient_cert_7, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_1394 : Nat.totient 1394 = 640 := by
  rw [show 1394 = 2 * 697 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 697)]
  rw [totient_cert_2, totient_cert_697] <;> norm_num
@[simp] lemma totient_cert_1395 : Nat.totient 1395 = 720 := by
  rw [show 1395 = 9 * 155 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 155)]
  rw [totient_cert_9, totient_cert_155] <;> norm_num
@[simp] lemma totient_cert_1396 : Nat.totient 1396 = 696 := by
  rw [show 1396 = 4 * 349 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 349)]
  rw [totient_cert_4, totient_cert_349] <;> norm_num
@[simp] lemma totient_cert_1397 : Nat.totient 1397 = 1260 := by
  rw [show 1397 = 11 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 127)]
  rw [totient_cert_11, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_1398 : Nat.totient 1398 = 464 := by
  rw [show 1398 = 2 * 699 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 699)]
  rw [totient_cert_2, totient_cert_699] <;> norm_num
@[simp] lemma totient_cert_1399 : Nat.totient 1399 = 1398 := by
  rw [show 1399 = 1399^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1399) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1400 : Nat.totient 1400 = 480 := by
  rw [show 1400 = 8 * 175 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 175)]
  rw [totient_cert_8, totient_cert_175] <;> norm_num
@[simp] lemma totient_cert_1401 : Nat.totient 1401 = 932 := by
  rw [show 1401 = 3 * 467 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 467)]
  rw [totient_cert_3, totient_cert_467] <;> norm_num
@[simp] lemma totient_cert_1402 : Nat.totient 1402 = 700 := by
  rw [show 1402 = 2 * 701 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 701)]
  rw [totient_cert_2, totient_cert_701] <;> norm_num
@[simp] lemma totient_cert_1403 : Nat.totient 1403 = 1320 := by
  rw [show 1403 = 23 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 61)]
  rw [totient_cert_23, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_1404 : Nat.totient 1404 = 432 := by
  rw [show 1404 = 4 * 351 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 351)]
  rw [totient_cert_4, totient_cert_351] <;> norm_num
@[simp] lemma totient_cert_1405 : Nat.totient 1405 = 1120 := by
  rw [show 1405 = 5 * 281 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 281)]
  rw [totient_cert_5, totient_cert_281] <;> norm_num
@[simp] lemma totient_cert_1406 : Nat.totient 1406 = 648 := by
  rw [show 1406 = 2 * 703 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 703)]
  rw [totient_cert_2, totient_cert_703] <;> norm_num
@[simp] lemma totient_cert_1407 : Nat.totient 1407 = 792 := by
  rw [show 1407 = 3 * 469 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 469)]
  rw [totient_cert_3, totient_cert_469] <;> norm_num
@[simp] lemma totient_cert_1408 : Nat.totient 1408 = 640 := by
  rw [show 1408 = 128 * 11 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 128 11)]
  rw [totient_cert_128, totient_cert_11] <;> norm_num
@[simp] lemma totient_cert_1409 : Nat.totient 1409 = 1408 := by
  rw [show 1409 = 1409^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1409) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1410 : Nat.totient 1410 = 368 := by
  rw [show 1410 = 2 * 705 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 705)]
  rw [totient_cert_2, totient_cert_705] <;> norm_num
@[simp] lemma totient_cert_1411 : Nat.totient 1411 = 1312 := by
  rw [show 1411 = 17 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 83)]
  rw [totient_cert_17, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_1412 : Nat.totient 1412 = 704 := by
  rw [show 1412 = 4 * 353 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 353)]
  rw [totient_cert_4, totient_cert_353] <;> norm_num
@[simp] lemma totient_cert_1413 : Nat.totient 1413 = 936 := by
  rw [show 1413 = 9 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 157)]
  rw [totient_cert_9, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_1414 : Nat.totient 1414 = 600 := by
  rw [show 1414 = 2 * 707 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 707)]
  rw [totient_cert_2, totient_cert_707] <;> norm_num
@[simp] lemma totient_cert_1415 : Nat.totient 1415 = 1128 := by
  rw [show 1415 = 5 * 283 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 283)]
  rw [totient_cert_5, totient_cert_283] <;> norm_num
@[simp] lemma totient_cert_1416 : Nat.totient 1416 = 464 := by
  rw [show 1416 = 8 * 177 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 177)]
  rw [totient_cert_8, totient_cert_177] <;> norm_num
@[simp] lemma totient_cert_1417 : Nat.totient 1417 = 1296 := by
  rw [show 1417 = 13 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 109)]
  rw [totient_cert_13, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_1418 : Nat.totient 1418 = 708 := by
  rw [show 1418 = 2 * 709 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 709)]
  rw [totient_cert_2, totient_cert_709] <;> norm_num
@[simp] lemma totient_cert_1419 : Nat.totient 1419 = 840 := by
  rw [show 1419 = 3 * 473 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 473)]
  rw [totient_cert_3, totient_cert_473] <;> norm_num
@[simp] lemma totient_cert_1420 : Nat.totient 1420 = 560 := by
  rw [show 1420 = 4 * 355 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 355)]
  rw [totient_cert_4, totient_cert_355] <;> norm_num
@[simp] lemma totient_cert_1421 : Nat.totient 1421 = 1176 := by
  rw [show 1421 = 49 * 29 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 29)]
  rw [totient_cert_49, totient_cert_29] <;> norm_num
@[simp] lemma totient_cert_1422 : Nat.totient 1422 = 468 := by
  rw [show 1422 = 2 * 711 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 711)]
  rw [totient_cert_2, totient_cert_711] <;> norm_num
@[simp] lemma totient_cert_1423 : Nat.totient 1423 = 1422 := by
  rw [show 1423 = 1423^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1423) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1424 : Nat.totient 1424 = 704 := by
  rw [show 1424 = 16 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 89)]
  rw [totient_cert_16, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_1425 : Nat.totient 1425 = 720 := by
  rw [show 1425 = 3 * 475 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 475)]
  rw [totient_cert_3, totient_cert_475] <;> norm_num
@[simp] lemma totient_cert_1426 : Nat.totient 1426 = 660 := by
  rw [show 1426 = 2 * 713 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 713)]
  rw [totient_cert_2, totient_cert_713] <;> norm_num
@[simp] lemma totient_cert_1427 : Nat.totient 1427 = 1426 := by
  rw [show 1427 = 1427^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1427) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1428 : Nat.totient 1428 = 384 := by
  rw [show 1428 = 4 * 357 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 357)]
  rw [totient_cert_4, totient_cert_357] <;> norm_num
@[simp] lemma totient_cert_1429 : Nat.totient 1429 = 1428 := by
  rw [show 1429 = 1429^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1429) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1430 : Nat.totient 1430 = 480 := by
  rw [show 1430 = 2 * 715 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 715)]
  rw [totient_cert_2, totient_cert_715] <;> norm_num
@[simp] lemma totient_cert_1431 : Nat.totient 1431 = 936 := by
  rw [show 1431 = 27 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 53)]
  rw [totient_cert_27, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1432 : Nat.totient 1432 = 712 := by
  rw [show 1432 = 8 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 179)]
  rw [totient_cert_8, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_1433 : Nat.totient 1433 = 1432 := by
  rw [show 1433 = 1433^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1433) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1434 : Nat.totient 1434 = 476 := by
  rw [show 1434 = 2 * 717 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 717)]
  rw [totient_cert_2, totient_cert_717] <;> norm_num
@[simp] lemma totient_cert_1435 : Nat.totient 1435 = 960 := by
  rw [show 1435 = 5 * 287 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 287)]
  rw [totient_cert_5, totient_cert_287] <;> norm_num
@[simp] lemma totient_cert_1436 : Nat.totient 1436 = 716 := by
  rw [show 1436 = 4 * 359 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 359)]
  rw [totient_cert_4, totient_cert_359] <;> norm_num
@[simp] lemma totient_cert_1437 : Nat.totient 1437 = 956 := by
  rw [show 1437 = 3 * 479 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 479)]
  rw [totient_cert_3, totient_cert_479] <;> norm_num
@[simp] lemma totient_cert_1438 : Nat.totient 1438 = 718 := by
  rw [show 1438 = 2 * 719 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 719)]
  rw [totient_cert_2, totient_cert_719] <;> norm_num
@[simp] lemma totient_cert_1439 : Nat.totient 1439 = 1438 := by
  rw [show 1439 = 1439^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1439) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1440 : Nat.totient 1440 = 384 := by
  rw [show 1440 = 32 * 45 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 45)]
  rw [totient_cert_32, totient_cert_45] <;> norm_num
@[simp] lemma totient_cert_1441 : Nat.totient 1441 = 1300 := by
  rw [show 1441 = 11 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 131)]
  rw [totient_cert_11, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_1442 : Nat.totient 1442 = 612 := by
  rw [show 1442 = 2 * 721 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 721)]
  rw [totient_cert_2, totient_cert_721] <;> norm_num
@[simp] lemma totient_cert_1443 : Nat.totient 1443 = 864 := by
  rw [show 1443 = 3 * 481 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 481)]
  rw [totient_cert_3, totient_cert_481] <;> norm_num
@[simp] lemma totient_cert_1444 : Nat.totient 1444 = 684 := by
  rw [show 1444 = 4 * 361 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 361)]
  rw [totient_cert_4, totient_cert_361] <;> norm_num
@[simp] lemma totient_cert_1445 : Nat.totient 1445 = 1088 := by
  rw [show 1445 = 5 * 289 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 289)]
  rw [totient_cert_5, totient_cert_289] <;> norm_num
@[simp] lemma totient_cert_1446 : Nat.totient 1446 = 480 := by
  rw [show 1446 = 2 * 723 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 723)]
  rw [totient_cert_2, totient_cert_723] <;> norm_num
@[simp] lemma totient_cert_1447 : Nat.totient 1447 = 1446 := by
  rw [show 1447 = 1447^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1447) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1448 : Nat.totient 1448 = 720 := by
  rw [show 1448 = 8 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 181)]
  rw [totient_cert_8, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_1449 : Nat.totient 1449 = 792 := by
  rw [show 1449 = 9 * 161 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 161)]
  rw [totient_cert_9, totient_cert_161] <;> norm_num
@[simp] lemma totient_cert_1450 : Nat.totient 1450 = 560 := by
  rw [show 1450 = 2 * 725 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 725)]
  rw [totient_cert_2, totient_cert_725] <;> norm_num
@[simp] lemma totient_cert_1451 : Nat.totient 1451 = 1450 := by
  rw [show 1451 = 1451^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1451) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1452 : Nat.totient 1452 = 440 := by
  rw [show 1452 = 4 * 363 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 363)]
  rw [totient_cert_4, totient_cert_363] <;> norm_num
@[simp] lemma totient_cert_1453 : Nat.totient 1453 = 1452 := by
  rw [show 1453 = 1453^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1453) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1454 : Nat.totient 1454 = 726 := by
  rw [show 1454 = 2 * 727 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 727)]
  rw [totient_cert_2, totient_cert_727] <;> norm_num
@[simp] lemma totient_cert_1455 : Nat.totient 1455 = 768 := by
  rw [show 1455 = 3 * 485 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 485)]
  rw [totient_cert_3, totient_cert_485] <;> norm_num
@[simp] lemma totient_cert_1456 : Nat.totient 1456 = 576 := by
  rw [show 1456 = 16 * 91 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 91)]
  rw [totient_cert_16, totient_cert_91] <;> norm_num
@[simp] lemma totient_cert_1457 : Nat.totient 1457 = 1380 := by
  rw [show 1457 = 31 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 31 47)]
  rw [totient_cert_31, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1458 : Nat.totient 1458 = 486 := by
  rw [show 1458 = 2 * 729 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 729)]
  rw [totient_cert_2, totient_cert_729] <;> norm_num
@[simp] lemma totient_cert_1459 : Nat.totient 1459 = 1458 := by
  rw [show 1459 = 1459^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1459) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1460 : Nat.totient 1460 = 576 := by
  rw [show 1460 = 4 * 365 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 365)]
  rw [totient_cert_4, totient_cert_365] <;> norm_num
@[simp] lemma totient_cert_1461 : Nat.totient 1461 = 972 := by
  rw [show 1461 = 3 * 487 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 487)]
  rw [totient_cert_3, totient_cert_487] <;> norm_num
@[simp] lemma totient_cert_1462 : Nat.totient 1462 = 672 := by
  rw [show 1462 = 2 * 731 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 731)]
  rw [totient_cert_2, totient_cert_731] <;> norm_num
@[simp] lemma totient_cert_1463 : Nat.totient 1463 = 1080 := by
  rw [show 1463 = 7 * 209 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 209)]
  rw [totient_cert_7, totient_cert_209] <;> norm_num
@[simp] lemma totient_cert_1464 : Nat.totient 1464 = 480 := by
  rw [show 1464 = 8 * 183 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 183)]
  rw [totient_cert_8, totient_cert_183] <;> norm_num
@[simp] lemma totient_cert_1465 : Nat.totient 1465 = 1168 := by
  rw [show 1465 = 5 * 293 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 293)]
  rw [totient_cert_5, totient_cert_293] <;> norm_num
@[simp] lemma totient_cert_1466 : Nat.totient 1466 = 732 := by
  rw [show 1466 = 2 * 733 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 733)]
  rw [totient_cert_2, totient_cert_733] <;> norm_num
@[simp] lemma totient_cert_1467 : Nat.totient 1467 = 972 := by
  rw [show 1467 = 9 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 163)]
  rw [totient_cert_9, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_1468 : Nat.totient 1468 = 732 := by
  rw [show 1468 = 4 * 367 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 367)]
  rw [totient_cert_4, totient_cert_367] <;> norm_num
@[simp] lemma totient_cert_1469 : Nat.totient 1469 = 1344 := by
  rw [show 1469 = 13 * 113 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 113)]
  rw [totient_cert_13, totient_cert_113] <;> norm_num
@[simp] lemma totient_cert_1470 : Nat.totient 1470 = 336 := by
  rw [show 1470 = 2 * 735 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 735)]
  rw [totient_cert_2, totient_cert_735] <;> norm_num
@[simp] lemma totient_cert_1471 : Nat.totient 1471 = 1470 := by
  rw [show 1471 = 1471^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1471) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1472 : Nat.totient 1472 = 704 := by
  rw [show 1472 = 64 * 23 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 23)]
  rw [totient_cert_64, totient_cert_23] <;> norm_num
@[simp] lemma totient_cert_1473 : Nat.totient 1473 = 980 := by
  rw [show 1473 = 3 * 491 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 491)]
  rw [totient_cert_3, totient_cert_491] <;> norm_num
@[simp] lemma totient_cert_1474 : Nat.totient 1474 = 660 := by
  rw [show 1474 = 2 * 737 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 737)]
  rw [totient_cert_2, totient_cert_737] <;> norm_num
@[simp] lemma totient_cert_1475 : Nat.totient 1475 = 1160 := by
  rw [show 1475 = 25 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 59)]
  rw [totient_cert_25, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_1476 : Nat.totient 1476 = 480 := by
  rw [show 1476 = 4 * 369 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 369)]
  rw [totient_cert_4, totient_cert_369] <;> norm_num
@[simp] lemma totient_cert_1477 : Nat.totient 1477 = 1260 := by
  rw [show 1477 = 7 * 211 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 211)]
  rw [totient_cert_7, totient_cert_211] <;> norm_num
@[simp] lemma totient_cert_1478 : Nat.totient 1478 = 738 := by
  rw [show 1478 = 2 * 739 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 739)]
  rw [totient_cert_2, totient_cert_739] <;> norm_num
@[simp] lemma totient_cert_1479 : Nat.totient 1479 = 896 := by
  rw [show 1479 = 3 * 493 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 493)]
  rw [totient_cert_3, totient_cert_493] <;> norm_num
@[simp] lemma totient_cert_1480 : Nat.totient 1480 = 576 := by
  rw [show 1480 = 8 * 185 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 185)]
  rw [totient_cert_8, totient_cert_185] <;> norm_num
@[simp] lemma totient_cert_1481 : Nat.totient 1481 = 1480 := by
  rw [show 1481 = 1481^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1481) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1482 : Nat.totient 1482 = 432 := by
  rw [show 1482 = 2 * 741 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 741)]
  rw [totient_cert_2, totient_cert_741] <;> norm_num
@[simp] lemma totient_cert_1483 : Nat.totient 1483 = 1482 := by
  rw [show 1483 = 1483^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1483) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1484 : Nat.totient 1484 = 624 := by
  rw [show 1484 = 4 * 371 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 371)]
  rw [totient_cert_4, totient_cert_371] <;> norm_num
@[simp] lemma totient_cert_1485 : Nat.totient 1485 = 720 := by
  rw [show 1485 = 27 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 55)]
  rw [totient_cert_27, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_1486 : Nat.totient 1486 = 742 := by
  rw [show 1486 = 2 * 743 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 743)]
  rw [totient_cert_2, totient_cert_743] <;> norm_num
@[simp] lemma totient_cert_1487 : Nat.totient 1487 = 1486 := by
  rw [show 1487 = 1487^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1487) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1488 : Nat.totient 1488 = 480 := by
  rw [show 1488 = 16 * 93 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 93)]
  rw [totient_cert_16, totient_cert_93] <;> norm_num
@[simp] lemma totient_cert_1489 : Nat.totient 1489 = 1488 := by
  rw [show 1489 = 1489^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1489) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1490 : Nat.totient 1490 = 592 := by
  rw [show 1490 = 2 * 745 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 745)]
  rw [totient_cert_2, totient_cert_745] <;> norm_num
@[simp] lemma totient_cert_1491 : Nat.totient 1491 = 840 := by
  rw [show 1491 = 3 * 497 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 497)]
  rw [totient_cert_3, totient_cert_497] <;> norm_num
@[simp] lemma totient_cert_1492 : Nat.totient 1492 = 744 := by
  rw [show 1492 = 4 * 373 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 373)]
  rw [totient_cert_4, totient_cert_373] <;> norm_num
@[simp] lemma totient_cert_1493 : Nat.totient 1493 = 1492 := by
  rw [show 1493 = 1493^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1493) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1494 : Nat.totient 1494 = 492 := by
  rw [show 1494 = 2 * 747 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 747)]
  rw [totient_cert_2, totient_cert_747] <;> norm_num
@[simp] lemma totient_cert_1495 : Nat.totient 1495 = 1056 := by
  rw [show 1495 = 5 * 299 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 299)]
  rw [totient_cert_5, totient_cert_299] <;> norm_num
@[simp] lemma totient_cert_1496 : Nat.totient 1496 = 640 := by
  rw [show 1496 = 8 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 187)]
  rw [totient_cert_8, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_1497 : Nat.totient 1497 = 996 := by
  rw [show 1497 = 3 * 499 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 499)]
  rw [totient_cert_3, totient_cert_499] <;> norm_num
@[simp] lemma totient_cert_1498 : Nat.totient 1498 = 636 := by
  rw [show 1498 = 2 * 749 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 749)]
  rw [totient_cert_2, totient_cert_749] <;> norm_num
@[simp] lemma totient_cert_1499 : Nat.totient 1499 = 1498 := by
  rw [show 1499 = 1499^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1499) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1500 : Nat.totient 1500 = 400 := by
  rw [show 1500 = 4 * 375 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 375)]
  rw [totient_cert_4, totient_cert_375] <;> norm_num
@[simp] lemma totient_cert_1501 : Nat.totient 1501 = 1404 := by
  rw [show 1501 = 19 * 79 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 79)]
  rw [totient_cert_19, totient_cert_79] <;> norm_num
@[simp] lemma totient_cert_1502 : Nat.totient 1502 = 750 := by
  rw [show 1502 = 2 * 751 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 751)]
  rw [totient_cert_2, totient_cert_751] <;> norm_num
@[simp] lemma totient_cert_1503 : Nat.totient 1503 = 996 := by
  rw [show 1503 = 9 * 167 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 167)]
  rw [totient_cert_9, totient_cert_167] <;> norm_num
@[simp] lemma totient_cert_1504 : Nat.totient 1504 = 736 := by
  rw [show 1504 = 32 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 47)]
  rw [totient_cert_32, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1505 : Nat.totient 1505 = 1008 := by
  rw [show 1505 = 5 * 301 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 301)]
  rw [totient_cert_5, totient_cert_301] <;> norm_num
@[simp] lemma totient_cert_1506 : Nat.totient 1506 = 500 := by
  rw [show 1506 = 2 * 753 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 753)]
  rw [totient_cert_2, totient_cert_753] <;> norm_num
@[simp] lemma totient_cert_1507 : Nat.totient 1507 = 1360 := by
  rw [show 1507 = 11 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 137)]
  rw [totient_cert_11, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_1508 : Nat.totient 1508 = 672 := by
  rw [show 1508 = 4 * 377 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 377)]
  rw [totient_cert_4, totient_cert_377] <;> norm_num
@[simp] lemma totient_cert_1509 : Nat.totient 1509 = 1004 := by
  rw [show 1509 = 3 * 503 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 503)]
  rw [totient_cert_3, totient_cert_503] <;> norm_num
@[simp] lemma totient_cert_1510 : Nat.totient 1510 = 600 := by
  rw [show 1510 = 2 * 755 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 755)]
  rw [totient_cert_2, totient_cert_755] <;> norm_num
@[simp] lemma totient_cert_1511 : Nat.totient 1511 = 1510 := by
  rw [show 1511 = 1511^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1511) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1512 : Nat.totient 1512 = 432 := by
  rw [show 1512 = 8 * 189 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 189)]
  rw [totient_cert_8, totient_cert_189] <;> norm_num
@[simp] lemma totient_cert_1513 : Nat.totient 1513 = 1408 := by
  rw [show 1513 = 17 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 89)]
  rw [totient_cert_17, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_1514 : Nat.totient 1514 = 756 := by
  rw [show 1514 = 2 * 757 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 757)]
  rw [totient_cert_2, totient_cert_757] <;> norm_num
@[simp] lemma totient_cert_1515 : Nat.totient 1515 = 800 := by
  rw [show 1515 = 3 * 505 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 505)]
  rw [totient_cert_3, totient_cert_505] <;> norm_num
@[simp] lemma totient_cert_1516 : Nat.totient 1516 = 756 := by
  rw [show 1516 = 4 * 379 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 379)]
  rw [totient_cert_4, totient_cert_379] <;> norm_num
@[simp] lemma totient_cert_1517 : Nat.totient 1517 = 1440 := by
  rw [show 1517 = 37 * 41 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 37 41)]
  rw [totient_cert_37, totient_cert_41] <;> norm_num
@[simp] lemma totient_cert_1518 : Nat.totient 1518 = 440 := by
  rw [show 1518 = 2 * 759 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 759)]
  rw [totient_cert_2, totient_cert_759] <;> norm_num
@[simp] lemma totient_cert_1519 : Nat.totient 1519 = 1260 := by
  rw [show 1519 = 49 * 31 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 49 31)]
  rw [totient_cert_49, totient_cert_31] <;> norm_num
@[simp] lemma totient_cert_1520 : Nat.totient 1520 = 576 := by
  rw [show 1520 = 16 * 95 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 95)]
  rw [totient_cert_16, totient_cert_95] <;> norm_num
@[simp] lemma totient_cert_1521 : Nat.totient 1521 = 936 := by
  rw [show 1521 = 9 * 169 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 169)]
  rw [totient_cert_9, totient_cert_169] <;> norm_num
@[simp] lemma totient_cert_1522 : Nat.totient 1522 = 760 := by
  rw [show 1522 = 2 * 761 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 761)]
  rw [totient_cert_2, totient_cert_761] <;> norm_num
@[simp] lemma totient_cert_1523 : Nat.totient 1523 = 1522 := by
  rw [show 1523 = 1523^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1523) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1524 : Nat.totient 1524 = 504 := by
  rw [show 1524 = 4 * 381 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 381)]
  rw [totient_cert_4, totient_cert_381] <;> norm_num
@[simp] lemma totient_cert_1525 : Nat.totient 1525 = 1200 := by
  rw [show 1525 = 25 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 61)]
  rw [totient_cert_25, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_1526 : Nat.totient 1526 = 648 := by
  rw [show 1526 = 2 * 763 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 763)]
  rw [totient_cert_2, totient_cert_763] <;> norm_num
@[simp] lemma totient_cert_1527 : Nat.totient 1527 = 1016 := by
  rw [show 1527 = 3 * 509 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 509)]
  rw [totient_cert_3, totient_cert_509] <;> norm_num
@[simp] lemma totient_cert_1528 : Nat.totient 1528 = 760 := by
  rw [show 1528 = 8 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 191)]
  rw [totient_cert_8, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_1529 : Nat.totient 1529 = 1380 := by
  rw [show 1529 = 11 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 139)]
  rw [totient_cert_11, totient_cert_139] <;> norm_num
@[simp] lemma totient_cert_1530 : Nat.totient 1530 = 384 := by
  rw [show 1530 = 2 * 765 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 765)]
  rw [totient_cert_2, totient_cert_765] <;> norm_num
@[simp] lemma totient_cert_1531 : Nat.totient 1531 = 1530 := by
  rw [show 1531 = 1531^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1531) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1532 : Nat.totient 1532 = 764 := by
  rw [show 1532 = 4 * 383 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 383)]
  rw [totient_cert_4, totient_cert_383] <;> norm_num
@[simp] lemma totient_cert_1533 : Nat.totient 1533 = 864 := by
  rw [show 1533 = 3 * 511 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 511)]
  rw [totient_cert_3, totient_cert_511] <;> norm_num
@[simp] lemma totient_cert_1534 : Nat.totient 1534 = 696 := by
  rw [show 1534 = 2 * 767 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 767)]
  rw [totient_cert_2, totient_cert_767] <;> norm_num
@[simp] lemma totient_cert_1535 : Nat.totient 1535 = 1224 := by
  rw [show 1535 = 5 * 307 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 307)]
  rw [totient_cert_5, totient_cert_307] <;> norm_num
@[simp] lemma totient_cert_1536 : Nat.totient 1536 = 512 := by
  rw [show 1536 = 512 * 3 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 512 3)]
  rw [totient_cert_512, totient_cert_3] <;> norm_num
@[simp] lemma totient_cert_1537 : Nat.totient 1537 = 1456 := by
  rw [show 1537 = 29 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 53)]
  rw [totient_cert_29, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1538 : Nat.totient 1538 = 768 := by
  rw [show 1538 = 2 * 769 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 769)]
  rw [totient_cert_2, totient_cert_769] <;> norm_num
@[simp] lemma totient_cert_1539 : Nat.totient 1539 = 972 := by
  rw [show 1539 = 81 * 19 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 81 19)]
  rw [totient_cert_81, totient_cert_19] <;> norm_num
@[simp] lemma totient_cert_1540 : Nat.totient 1540 = 480 := by
  rw [show 1540 = 4 * 385 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 385)]
  rw [totient_cert_4, totient_cert_385] <;> norm_num
@[simp] lemma totient_cert_1541 : Nat.totient 1541 = 1452 := by
  rw [show 1541 = 23 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 67)]
  rw [totient_cert_23, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_1542 : Nat.totient 1542 = 512 := by
  rw [show 1542 = 2 * 771 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 771)]
  rw [totient_cert_2, totient_cert_771] <;> norm_num
@[simp] lemma totient_cert_1543 : Nat.totient 1543 = 1542 := by
  rw [show 1543 = 1543^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1543) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1544 : Nat.totient 1544 = 768 := by
  rw [show 1544 = 8 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 193)]
  rw [totient_cert_8, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_1545 : Nat.totient 1545 = 816 := by
  rw [show 1545 = 3 * 515 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 515)]
  rw [totient_cert_3, totient_cert_515] <;> norm_num
@[simp] lemma totient_cert_1546 : Nat.totient 1546 = 772 := by
  rw [show 1546 = 2 * 773 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 773)]
  rw [totient_cert_2, totient_cert_773] <;> norm_num
@[simp] lemma totient_cert_1547 : Nat.totient 1547 = 1152 := by
  rw [show 1547 = 7 * 221 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 221)]
  rw [totient_cert_7, totient_cert_221] <;> norm_num
@[simp] lemma totient_cert_1548 : Nat.totient 1548 = 504 := by
  rw [show 1548 = 4 * 387 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 387)]
  rw [totient_cert_4, totient_cert_387] <;> norm_num
@[simp] lemma totient_cert_1549 : Nat.totient 1549 = 1548 := by
  rw [show 1549 = 1549^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1549) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1550 : Nat.totient 1550 = 600 := by
  rw [show 1550 = 2 * 775 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 775)]
  rw [totient_cert_2, totient_cert_775] <;> norm_num
@[simp] lemma totient_cert_1551 : Nat.totient 1551 = 920 := by
  rw [show 1551 = 3 * 517 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 517)]
  rw [totient_cert_3, totient_cert_517] <;> norm_num
@[simp] lemma totient_cert_1552 : Nat.totient 1552 = 768 := by
  rw [show 1552 = 16 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 97)]
  rw [totient_cert_16, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_1553 : Nat.totient 1553 = 1552 := by
  rw [show 1553 = 1553^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1553) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1554 : Nat.totient 1554 = 432 := by
  rw [show 1554 = 2 * 777 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 777)]
  rw [totient_cert_2, totient_cert_777] <;> norm_num
@[simp] lemma totient_cert_1555 : Nat.totient 1555 = 1240 := by
  rw [show 1555 = 5 * 311 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 311)]
  rw [totient_cert_5, totient_cert_311] <;> norm_num
@[simp] lemma totient_cert_1556 : Nat.totient 1556 = 776 := by
  rw [show 1556 = 4 * 389 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 389)]
  rw [totient_cert_4, totient_cert_389] <;> norm_num
@[simp] lemma totient_cert_1557 : Nat.totient 1557 = 1032 := by
  rw [show 1557 = 9 * 173 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 173)]
  rw [totient_cert_9, totient_cert_173] <;> norm_num
@[simp] lemma totient_cert_1558 : Nat.totient 1558 = 720 := by
  rw [show 1558 = 2 * 779 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 779)]
  rw [totient_cert_2, totient_cert_779] <;> norm_num
@[simp] lemma totient_cert_1559 : Nat.totient 1559 = 1558 := by
  rw [show 1559 = 1559^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1559) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1560 : Nat.totient 1560 = 384 := by
  rw [show 1560 = 8 * 195 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 195)]
  rw [totient_cert_8, totient_cert_195] <;> norm_num
@[simp] lemma totient_cert_1561 : Nat.totient 1561 = 1332 := by
  rw [show 1561 = 7 * 223 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 223)]
  rw [totient_cert_7, totient_cert_223] <;> norm_num
@[simp] lemma totient_cert_1562 : Nat.totient 1562 = 700 := by
  rw [show 1562 = 2 * 781 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 781)]
  rw [totient_cert_2, totient_cert_781] <;> norm_num
@[simp] lemma totient_cert_1563 : Nat.totient 1563 = 1040 := by
  rw [show 1563 = 3 * 521 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 521)]
  rw [totient_cert_3, totient_cert_521] <;> norm_num
@[simp] lemma totient_cert_1564 : Nat.totient 1564 = 704 := by
  rw [show 1564 = 4 * 391 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 391)]
  rw [totient_cert_4, totient_cert_391] <;> norm_num
@[simp] lemma totient_cert_1565 : Nat.totient 1565 = 1248 := by
  rw [show 1565 = 5 * 313 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 313)]
  rw [totient_cert_5, totient_cert_313] <;> norm_num
@[simp] lemma totient_cert_1566 : Nat.totient 1566 = 504 := by
  rw [show 1566 = 2 * 783 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 783)]
  rw [totient_cert_2, totient_cert_783] <;> norm_num
@[simp] lemma totient_cert_1567 : Nat.totient 1567 = 1566 := by
  rw [show 1567 = 1567^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1567) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1568 : Nat.totient 1568 = 672 := by
  rw [show 1568 = 32 * 49 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 49)]
  rw [totient_cert_32, totient_cert_49] <;> norm_num
@[simp] lemma totient_cert_1569 : Nat.totient 1569 = 1044 := by
  rw [show 1569 = 3 * 523 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 523)]
  rw [totient_cert_3, totient_cert_523] <;> norm_num
@[simp] lemma totient_cert_1570 : Nat.totient 1570 = 624 := by
  rw [show 1570 = 2 * 785 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 785)]
  rw [totient_cert_2, totient_cert_785] <;> norm_num
@[simp] lemma totient_cert_1571 : Nat.totient 1571 = 1570 := by
  rw [show 1571 = 1571^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1571) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1572 : Nat.totient 1572 = 520 := by
  rw [show 1572 = 4 * 393 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 393)]
  rw [totient_cert_4, totient_cert_393] <;> norm_num
@[simp] lemma totient_cert_1573 : Nat.totient 1573 = 1320 := by
  rw [show 1573 = 121 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 121 13)]
  rw [totient_cert_121, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_1574 : Nat.totient 1574 = 786 := by
  rw [show 1574 = 2 * 787 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 787)]
  rw [totient_cert_2, totient_cert_787] <;> norm_num
@[simp] lemma totient_cert_1575 : Nat.totient 1575 = 720 := by
  rw [show 1575 = 9 * 175 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 175)]
  rw [totient_cert_9, totient_cert_175] <;> norm_num
@[simp] lemma totient_cert_1576 : Nat.totient 1576 = 784 := by
  rw [show 1576 = 8 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 197)]
  rw [totient_cert_8, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_1577 : Nat.totient 1577 = 1476 := by
  rw [show 1577 = 19 * 83 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 83)]
  rw [totient_cert_19, totient_cert_83] <;> norm_num
@[simp] lemma totient_cert_1578 : Nat.totient 1578 = 524 := by
  rw [show 1578 = 2 * 789 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 789)]
  rw [totient_cert_2, totient_cert_789] <;> norm_num
@[simp] lemma totient_cert_1579 : Nat.totient 1579 = 1578 := by
  rw [show 1579 = 1579^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1579) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1580 : Nat.totient 1580 = 624 := by
  rw [show 1580 = 4 * 395 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 395)]
  rw [totient_cert_4, totient_cert_395] <;> norm_num
@[simp] lemma totient_cert_1581 : Nat.totient 1581 = 960 := by
  rw [show 1581 = 3 * 527 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 527)]
  rw [totient_cert_3, totient_cert_527] <;> norm_num
@[simp] lemma totient_cert_1582 : Nat.totient 1582 = 672 := by
  rw [show 1582 = 2 * 791 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 791)]
  rw [totient_cert_2, totient_cert_791] <;> norm_num
@[simp] lemma totient_cert_1583 : Nat.totient 1583 = 1582 := by
  rw [show 1583 = 1583^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1583) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1584 : Nat.totient 1584 = 480 := by
  rw [show 1584 = 16 * 99 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 99)]
  rw [totient_cert_16, totient_cert_99] <;> norm_num
@[simp] lemma totient_cert_1585 : Nat.totient 1585 = 1264 := by
  rw [show 1585 = 5 * 317 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 317)]
  rw [totient_cert_5, totient_cert_317] <;> norm_num
@[simp] lemma totient_cert_1586 : Nat.totient 1586 = 720 := by
  rw [show 1586 = 2 * 793 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 793)]
  rw [totient_cert_2, totient_cert_793] <;> norm_num
@[simp] lemma totient_cert_1587 : Nat.totient 1587 = 1012 := by
  rw [show 1587 = 3 * 529 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 529)]
  rw [totient_cert_3, totient_cert_529] <;> norm_num
@[simp] lemma totient_cert_1588 : Nat.totient 1588 = 792 := by
  rw [show 1588 = 4 * 397 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 397)]
  rw [totient_cert_4, totient_cert_397] <;> norm_num
@[simp] lemma totient_cert_1589 : Nat.totient 1589 = 1356 := by
  rw [show 1589 = 7 * 227 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 227)]
  rw [totient_cert_7, totient_cert_227] <;> norm_num
@[simp] lemma totient_cert_1590 : Nat.totient 1590 = 416 := by
  rw [show 1590 = 2 * 795 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 795)]
  rw [totient_cert_2, totient_cert_795] <;> norm_num
@[simp] lemma totient_cert_1591 : Nat.totient 1591 = 1512 := by
  rw [show 1591 = 37 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 37 43)]
  rw [totient_cert_37, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1592 : Nat.totient 1592 = 792 := by
  rw [show 1592 = 8 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 199)]
  rw [totient_cert_8, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_1593 : Nat.totient 1593 = 1044 := by
  rw [show 1593 = 27 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 59)]
  rw [totient_cert_27, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_1594 : Nat.totient 1594 = 796 := by
  rw [show 1594 = 2 * 797 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 797)]
  rw [totient_cert_2, totient_cert_797] <;> norm_num
@[simp] lemma totient_cert_1595 : Nat.totient 1595 = 1120 := by
  rw [show 1595 = 5 * 319 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 319)]
  rw [totient_cert_5, totient_cert_319] <;> norm_num
@[simp] lemma totient_cert_1596 : Nat.totient 1596 = 432 := by
  rw [show 1596 = 4 * 399 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 399)]
  rw [totient_cert_4, totient_cert_399] <;> norm_num
@[simp] lemma totient_cert_1597 : Nat.totient 1597 = 1596 := by
  rw [show 1597 = 1597^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1597) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1598 : Nat.totient 1598 = 736 := by
  rw [show 1598 = 2 * 799 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 799)]
  rw [totient_cert_2, totient_cert_799] <;> norm_num
@[simp] lemma totient_cert_1599 : Nat.totient 1599 = 960 := by
  rw [show 1599 = 3 * 533 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 533)]
  rw [totient_cert_3, totient_cert_533] <;> norm_num
@[simp] lemma totient_cert_1600 : Nat.totient 1600 = 640 := by
  rw [show 1600 = 64 * 25 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 25)]
  rw [totient_cert_64, totient_cert_25] <;> norm_num
@[simp] lemma totient_cert_1601 : Nat.totient 1601 = 1600 := by
  rw [show 1601 = 1601^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1601) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1602 : Nat.totient 1602 = 528 := by
  rw [show 1602 = 2 * 801 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 801)]
  rw [totient_cert_2, totient_cert_801] <;> norm_num
@[simp] lemma totient_cert_1603 : Nat.totient 1603 = 1368 := by
  rw [show 1603 = 7 * 229 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 229)]
  rw [totient_cert_7, totient_cert_229] <;> norm_num
@[simp] lemma totient_cert_1604 : Nat.totient 1604 = 800 := by
  rw [show 1604 = 4 * 401 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 401)]
  rw [totient_cert_4, totient_cert_401] <;> norm_num
@[simp] lemma totient_cert_1605 : Nat.totient 1605 = 848 := by
  rw [show 1605 = 3 * 535 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 535)]
  rw [totient_cert_3, totient_cert_535] <;> norm_num
@[simp] lemma totient_cert_1606 : Nat.totient 1606 = 720 := by
  rw [show 1606 = 2 * 803 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 803)]
  rw [totient_cert_2, totient_cert_803] <;> norm_num
@[simp] lemma totient_cert_1607 : Nat.totient 1607 = 1606 := by
  rw [show 1607 = 1607^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1607) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1608 : Nat.totient 1608 = 528 := by
  rw [show 1608 = 8 * 201 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 201)]
  rw [totient_cert_8, totient_cert_201] <;> norm_num
@[simp] lemma totient_cert_1609 : Nat.totient 1609 = 1608 := by
  rw [show 1609 = 1609^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1609) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1610 : Nat.totient 1610 = 528 := by
  rw [show 1610 = 2 * 805 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 805)]
  rw [totient_cert_2, totient_cert_805] <;> norm_num
@[simp] lemma totient_cert_1611 : Nat.totient 1611 = 1068 := by
  rw [show 1611 = 9 * 179 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 179)]
  rw [totient_cert_9, totient_cert_179] <;> norm_num
@[simp] lemma totient_cert_1612 : Nat.totient 1612 = 720 := by
  rw [show 1612 = 4 * 403 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 403)]
  rw [totient_cert_4, totient_cert_403] <;> norm_num
@[simp] lemma totient_cert_1613 : Nat.totient 1613 = 1612 := by
  rw [show 1613 = 1613^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1613) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1614 : Nat.totient 1614 = 536 := by
  rw [show 1614 = 2 * 807 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 807)]
  rw [totient_cert_2, totient_cert_807] <;> norm_num
@[simp] lemma totient_cert_1615 : Nat.totient 1615 = 1152 := by
  rw [show 1615 = 5 * 323 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 323)]
  rw [totient_cert_5, totient_cert_323] <;> norm_num
@[simp] lemma totient_cert_1616 : Nat.totient 1616 = 800 := by
  rw [show 1616 = 16 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 101)]
  rw [totient_cert_16, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_1617 : Nat.totient 1617 = 840 := by
  rw [show 1617 = 3 * 539 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 539)]
  rw [totient_cert_3, totient_cert_539] <;> norm_num
@[simp] lemma totient_cert_1618 : Nat.totient 1618 = 808 := by
  rw [show 1618 = 2 * 809 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 809)]
  rw [totient_cert_2, totient_cert_809] <;> norm_num
@[simp] lemma totient_cert_1619 : Nat.totient 1619 = 1618 := by
  rw [show 1619 = 1619^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1619) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1620 : Nat.totient 1620 = 432 := by
  rw [show 1620 = 4 * 405 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 405)]
  rw [totient_cert_4, totient_cert_405] <;> norm_num
@[simp] lemma totient_cert_1621 : Nat.totient 1621 = 1620 := by
  rw [show 1621 = 1621^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1621) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1622 : Nat.totient 1622 = 810 := by
  rw [show 1622 = 2 * 811 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 811)]
  rw [totient_cert_2, totient_cert_811] <;> norm_num
@[simp] lemma totient_cert_1623 : Nat.totient 1623 = 1080 := by
  rw [show 1623 = 3 * 541 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 541)]
  rw [totient_cert_3, totient_cert_541] <;> norm_num
@[simp] lemma totient_cert_1624 : Nat.totient 1624 = 672 := by
  rw [show 1624 = 8 * 203 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 203)]
  rw [totient_cert_8, totient_cert_203] <;> norm_num
@[simp] lemma totient_cert_1625 : Nat.totient 1625 = 1200 := by
  rw [show 1625 = 125 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 125 13)]
  rw [totient_cert_125, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_1626 : Nat.totient 1626 = 540 := by
  rw [show 1626 = 2 * 813 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 813)]
  rw [totient_cert_2, totient_cert_813] <;> norm_num
@[simp] lemma totient_cert_1627 : Nat.totient 1627 = 1626 := by
  rw [show 1627 = 1627^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1627) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1628 : Nat.totient 1628 = 720 := by
  rw [show 1628 = 4 * 407 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 407)]
  rw [totient_cert_4, totient_cert_407] <;> norm_num
@[simp] lemma totient_cert_1629 : Nat.totient 1629 = 1080 := by
  rw [show 1629 = 9 * 181 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 181)]
  rw [totient_cert_9, totient_cert_181] <;> norm_num
@[simp] lemma totient_cert_1630 : Nat.totient 1630 = 648 := by
  rw [show 1630 = 2 * 815 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 815)]
  rw [totient_cert_2, totient_cert_815] <;> norm_num
@[simp] lemma totient_cert_1631 : Nat.totient 1631 = 1392 := by
  rw [show 1631 = 7 * 233 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 233)]
  rw [totient_cert_7, totient_cert_233] <;> norm_num
@[simp] lemma totient_cert_1632 : Nat.totient 1632 = 512 := by
  rw [show 1632 = 32 * 51 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 51)]
  rw [totient_cert_32, totient_cert_51] <;> norm_num
@[simp] lemma totient_cert_1633 : Nat.totient 1633 = 1540 := by
  rw [show 1633 = 23 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 71)]
  rw [totient_cert_23, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_1634 : Nat.totient 1634 = 756 := by
  rw [show 1634 = 2 * 817 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 817)]
  rw [totient_cert_2, totient_cert_817] <;> norm_num
@[simp] lemma totient_cert_1635 : Nat.totient 1635 = 864 := by
  rw [show 1635 = 3 * 545 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 545)]
  rw [totient_cert_3, totient_cert_545] <;> norm_num
@[simp] lemma totient_cert_1636 : Nat.totient 1636 = 816 := by
  rw [show 1636 = 4 * 409 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 409)]
  rw [totient_cert_4, totient_cert_409] <;> norm_num
@[simp] lemma totient_cert_1637 : Nat.totient 1637 = 1636 := by
  rw [show 1637 = 1637^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1637) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1638 : Nat.totient 1638 = 432 := by
  rw [show 1638 = 2 * 819 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 819)]
  rw [totient_cert_2, totient_cert_819] <;> norm_num
@[simp] lemma totient_cert_1639 : Nat.totient 1639 = 1480 := by
  rw [show 1639 = 11 * 149 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 149)]
  rw [totient_cert_11, totient_cert_149] <;> norm_num
@[simp] lemma totient_cert_1640 : Nat.totient 1640 = 640 := by
  rw [show 1640 = 8 * 205 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 205)]
  rw [totient_cert_8, totient_cert_205] <;> norm_num
@[simp] lemma totient_cert_1641 : Nat.totient 1641 = 1092 := by
  rw [show 1641 = 3 * 547 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 547)]
  rw [totient_cert_3, totient_cert_547] <;> norm_num
@[simp] lemma totient_cert_1642 : Nat.totient 1642 = 820 := by
  rw [show 1642 = 2 * 821 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 821)]
  rw [totient_cert_2, totient_cert_821] <;> norm_num
@[simp] lemma totient_cert_1643 : Nat.totient 1643 = 1560 := by
  rw [show 1643 = 31 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 31 53)]
  rw [totient_cert_31, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1644 : Nat.totient 1644 = 544 := by
  rw [show 1644 = 4 * 411 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 411)]
  rw [totient_cert_4, totient_cert_411] <;> norm_num
@[simp] lemma totient_cert_1645 : Nat.totient 1645 = 1104 := by
  rw [show 1645 = 5 * 329 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 329)]
  rw [totient_cert_5, totient_cert_329] <;> norm_num
@[simp] lemma totient_cert_1646 : Nat.totient 1646 = 822 := by
  rw [show 1646 = 2 * 823 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 823)]
  rw [totient_cert_2, totient_cert_823] <;> norm_num
@[simp] lemma totient_cert_1647 : Nat.totient 1647 = 1080 := by
  rw [show 1647 = 27 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 61)]
  rw [totient_cert_27, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_1648 : Nat.totient 1648 = 816 := by
  rw [show 1648 = 16 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 103)]
  rw [totient_cert_16, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_1649 : Nat.totient 1649 = 1536 := by
  rw [show 1649 = 17 * 97 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 97)]
  rw [totient_cert_17, totient_cert_97] <;> norm_num
@[simp] lemma totient_cert_1650 : Nat.totient 1650 = 400 := by
  rw [show 1650 = 2 * 825 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 825)]
  rw [totient_cert_2, totient_cert_825] <;> norm_num
@[simp] lemma totient_cert_1651 : Nat.totient 1651 = 1512 := by
  rw [show 1651 = 13 * 127 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 127)]
  rw [totient_cert_13, totient_cert_127] <;> norm_num
@[simp] lemma totient_cert_1652 : Nat.totient 1652 = 696 := by
  rw [show 1652 = 4 * 413 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 413)]
  rw [totient_cert_4, totient_cert_413] <;> norm_num
@[simp] lemma totient_cert_1653 : Nat.totient 1653 = 1008 := by
  rw [show 1653 = 3 * 551 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 551)]
  rw [totient_cert_3, totient_cert_551] <;> norm_num
@[simp] lemma totient_cert_1654 : Nat.totient 1654 = 826 := by
  rw [show 1654 = 2 * 827 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 827)]
  rw [totient_cert_2, totient_cert_827] <;> norm_num
@[simp] lemma totient_cert_1655 : Nat.totient 1655 = 1320 := by
  rw [show 1655 = 5 * 331 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 331)]
  rw [totient_cert_5, totient_cert_331] <;> norm_num
@[simp] lemma totient_cert_1656 : Nat.totient 1656 = 528 := by
  rw [show 1656 = 8 * 207 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 207)]
  rw [totient_cert_8, totient_cert_207] <;> norm_num
@[simp] lemma totient_cert_1657 : Nat.totient 1657 = 1656 := by
  rw [show 1657 = 1657^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1657) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1658 : Nat.totient 1658 = 828 := by
  rw [show 1658 = 2 * 829 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 829)]
  rw [totient_cert_2, totient_cert_829] <;> norm_num
@[simp] lemma totient_cert_1659 : Nat.totient 1659 = 936 := by
  rw [show 1659 = 3 * 553 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 553)]
  rw [totient_cert_3, totient_cert_553] <;> norm_num
@[simp] lemma totient_cert_1660 : Nat.totient 1660 = 656 := by
  rw [show 1660 = 4 * 415 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 415)]
  rw [totient_cert_4, totient_cert_415] <;> norm_num
@[simp] lemma totient_cert_1661 : Nat.totient 1661 = 1500 := by
  rw [show 1661 = 11 * 151 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 151)]
  rw [totient_cert_11, totient_cert_151] <;> norm_num
@[simp] lemma totient_cert_1662 : Nat.totient 1662 = 552 := by
  rw [show 1662 = 2 * 831 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 831)]
  rw [totient_cert_2, totient_cert_831] <;> norm_num
@[simp] lemma totient_cert_1663 : Nat.totient 1663 = 1662 := by
  rw [show 1663 = 1663^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1663) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1664 : Nat.totient 1664 = 768 := by
  rw [show 1664 = 128 * 13 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 128 13)]
  rw [totient_cert_128, totient_cert_13] <;> norm_num
@[simp] lemma totient_cert_1665 : Nat.totient 1665 = 864 := by
  rw [show 1665 = 9 * 185 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 185)]
  rw [totient_cert_9, totient_cert_185] <;> norm_num
@[simp] lemma totient_cert_1666 : Nat.totient 1666 = 672 := by
  rw [show 1666 = 2 * 833 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 833)]
  rw [totient_cert_2, totient_cert_833] <;> norm_num
@[simp] lemma totient_cert_1667 : Nat.totient 1667 = 1666 := by
  rw [show 1667 = 1667^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1667) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1668 : Nat.totient 1668 = 552 := by
  rw [show 1668 = 4 * 417 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 417)]
  rw [totient_cert_4, totient_cert_417] <;> norm_num
@[simp] lemma totient_cert_1669 : Nat.totient 1669 = 1668 := by
  rw [show 1669 = 1669^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1669) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1670 : Nat.totient 1670 = 664 := by
  rw [show 1670 = 2 * 835 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 835)]
  rw [totient_cert_2, totient_cert_835] <;> norm_num
@[simp] lemma totient_cert_1671 : Nat.totient 1671 = 1112 := by
  rw [show 1671 = 3 * 557 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 557)]
  rw [totient_cert_3, totient_cert_557] <;> norm_num
@[simp] lemma totient_cert_1672 : Nat.totient 1672 = 720 := by
  rw [show 1672 = 8 * 209 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 209)]
  rw [totient_cert_8, totient_cert_209] <;> norm_num
@[simp] lemma totient_cert_1673 : Nat.totient 1673 = 1428 := by
  rw [show 1673 = 7 * 239 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 239)]
  rw [totient_cert_7, totient_cert_239] <;> norm_num
@[simp] lemma totient_cert_1674 : Nat.totient 1674 = 540 := by
  rw [show 1674 = 2 * 837 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 837)]
  rw [totient_cert_2, totient_cert_837] <;> norm_num
@[simp] lemma totient_cert_1675 : Nat.totient 1675 = 1320 := by
  rw [show 1675 = 25 * 67 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 67)]
  rw [totient_cert_25, totient_cert_67] <;> norm_num
@[simp] lemma totient_cert_1676 : Nat.totient 1676 = 836 := by
  rw [show 1676 = 4 * 419 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 419)]
  rw [totient_cert_4, totient_cert_419] <;> norm_num
@[simp] lemma totient_cert_1677 : Nat.totient 1677 = 1008 := by
  rw [show 1677 = 3 * 559 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 559)]
  rw [totient_cert_3, totient_cert_559] <;> norm_num
@[simp] lemma totient_cert_1678 : Nat.totient 1678 = 838 := by
  rw [show 1678 = 2 * 839 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 839)]
  rw [totient_cert_2, totient_cert_839] <;> norm_num
@[simp] lemma totient_cert_1679 : Nat.totient 1679 = 1584 := by
  rw [show 1679 = 23 * 73 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 23 73)]
  rw [totient_cert_23, totient_cert_73] <;> norm_num
@[simp] lemma totient_cert_1680 : Nat.totient 1680 = 384 := by
  rw [show 1680 = 16 * 105 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 105)]
  rw [totient_cert_16, totient_cert_105] <;> norm_num
@[simp] lemma totient_cert_1681 : Nat.totient 1681 = 1640 := by
  rw [show 1681 = 41^2 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 41) (by norm_num : 0 < 2)] <;> norm_num
@[simp] lemma totient_cert_1682 : Nat.totient 1682 = 812 := by
  rw [show 1682 = 2 * 841 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 841)]
  rw [totient_cert_2, totient_cert_841] <;> norm_num
@[simp] lemma totient_cert_1683 : Nat.totient 1683 = 960 := by
  rw [show 1683 = 9 * 187 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 187)]
  rw [totient_cert_9, totient_cert_187] <;> norm_num
@[simp] lemma totient_cert_1684 : Nat.totient 1684 = 840 := by
  rw [show 1684 = 4 * 421 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 421)]
  rw [totient_cert_4, totient_cert_421] <;> norm_num
@[simp] lemma totient_cert_1685 : Nat.totient 1685 = 1344 := by
  rw [show 1685 = 5 * 337 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 337)]
  rw [totient_cert_5, totient_cert_337] <;> norm_num
@[simp] lemma totient_cert_1686 : Nat.totient 1686 = 560 := by
  rw [show 1686 = 2 * 843 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 843)]
  rw [totient_cert_2, totient_cert_843] <;> norm_num
@[simp] lemma totient_cert_1687 : Nat.totient 1687 = 1440 := by
  rw [show 1687 = 7 * 241 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 241)]
  rw [totient_cert_7, totient_cert_241] <;> norm_num
@[simp] lemma totient_cert_1688 : Nat.totient 1688 = 840 := by
  rw [show 1688 = 8 * 211 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 211)]
  rw [totient_cert_8, totient_cert_211] <;> norm_num
@[simp] lemma totient_cert_1689 : Nat.totient 1689 = 1124 := by
  rw [show 1689 = 3 * 563 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 563)]
  rw [totient_cert_3, totient_cert_563] <;> norm_num
@[simp] lemma totient_cert_1690 : Nat.totient 1690 = 624 := by
  rw [show 1690 = 2 * 845 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 845)]
  rw [totient_cert_2, totient_cert_845] <;> norm_num
@[simp] lemma totient_cert_1691 : Nat.totient 1691 = 1584 := by
  rw [show 1691 = 19 * 89 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 19 89)]
  rw [totient_cert_19, totient_cert_89] <;> norm_num
@[simp] lemma totient_cert_1692 : Nat.totient 1692 = 552 := by
  rw [show 1692 = 4 * 423 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 423)]
  rw [totient_cert_4, totient_cert_423] <;> norm_num
@[simp] lemma totient_cert_1693 : Nat.totient 1693 = 1692 := by
  rw [show 1693 = 1693^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1693) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1694 : Nat.totient 1694 = 660 := by
  rw [show 1694 = 2 * 847 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 847)]
  rw [totient_cert_2, totient_cert_847] <;> norm_num
@[simp] lemma totient_cert_1695 : Nat.totient 1695 = 896 := by
  rw [show 1695 = 3 * 565 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 565)]
  rw [totient_cert_3, totient_cert_565] <;> norm_num
@[simp] lemma totient_cert_1696 : Nat.totient 1696 = 832 := by
  rw [show 1696 = 32 * 53 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 53)]
  rw [totient_cert_32, totient_cert_53] <;> norm_num
@[simp] lemma totient_cert_1697 : Nat.totient 1697 = 1696 := by
  rw [show 1697 = 1697^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1697) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1698 : Nat.totient 1698 = 564 := by
  rw [show 1698 = 2 * 849 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 849)]
  rw [totient_cert_2, totient_cert_849] <;> norm_num
@[simp] lemma totient_cert_1699 : Nat.totient 1699 = 1698 := by
  rw [show 1699 = 1699^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1699) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1700 : Nat.totient 1700 = 640 := by
  rw [show 1700 = 4 * 425 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 425)]
  rw [totient_cert_4, totient_cert_425] <;> norm_num
@[simp] lemma totient_cert_1701 : Nat.totient 1701 = 972 := by
  rw [show 1701 = 243 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 243 7)]
  rw [totient_cert_243, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_1702 : Nat.totient 1702 = 792 := by
  rw [show 1702 = 2 * 851 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 851)]
  rw [totient_cert_2, totient_cert_851] <;> norm_num
@[simp] lemma totient_cert_1703 : Nat.totient 1703 = 1560 := by
  rw [show 1703 = 13 * 131 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 131)]
  rw [totient_cert_13, totient_cert_131] <;> norm_num
@[simp] lemma totient_cert_1704 : Nat.totient 1704 = 560 := by
  rw [show 1704 = 8 * 213 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 213)]
  rw [totient_cert_8, totient_cert_213] <;> norm_num
@[simp] lemma totient_cert_1705 : Nat.totient 1705 = 1200 := by
  rw [show 1705 = 5 * 341 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 341)]
  rw [totient_cert_5, totient_cert_341] <;> norm_num
@[simp] lemma totient_cert_1706 : Nat.totient 1706 = 852 := by
  rw [show 1706 = 2 * 853 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 853)]
  rw [totient_cert_2, totient_cert_853] <;> norm_num
@[simp] lemma totient_cert_1707 : Nat.totient 1707 = 1136 := by
  rw [show 1707 = 3 * 569 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 569)]
  rw [totient_cert_3, totient_cert_569] <;> norm_num
@[simp] lemma totient_cert_1708 : Nat.totient 1708 = 720 := by
  rw [show 1708 = 4 * 427 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 427)]
  rw [totient_cert_4, totient_cert_427] <;> norm_num
@[simp] lemma totient_cert_1709 : Nat.totient 1709 = 1708 := by
  rw [show 1709 = 1709^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1709) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1710 : Nat.totient 1710 = 432 := by
  rw [show 1710 = 2 * 855 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 855)]
  rw [totient_cert_2, totient_cert_855] <;> norm_num
@[simp] lemma totient_cert_1711 : Nat.totient 1711 = 1624 := by
  rw [show 1711 = 29 * 59 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 59)]
  rw [totient_cert_29, totient_cert_59] <;> norm_num
@[simp] lemma totient_cert_1712 : Nat.totient 1712 = 848 := by
  rw [show 1712 = 16 * 107 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 107)]
  rw [totient_cert_16, totient_cert_107] <;> norm_num
@[simp] lemma totient_cert_1713 : Nat.totient 1713 = 1140 := by
  rw [show 1713 = 3 * 571 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 571)]
  rw [totient_cert_3, totient_cert_571] <;> norm_num
@[simp] lemma totient_cert_1714 : Nat.totient 1714 = 856 := by
  rw [show 1714 = 2 * 857 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 857)]
  rw [totient_cert_2, totient_cert_857] <;> norm_num
@[simp] lemma totient_cert_1715 : Nat.totient 1715 = 1176 := by
  rw [show 1715 = 5 * 343 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 343)]
  rw [totient_cert_5, totient_cert_343] <;> norm_num
@[simp] lemma totient_cert_1716 : Nat.totient 1716 = 480 := by
  rw [show 1716 = 4 * 429 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 429)]
  rw [totient_cert_4, totient_cert_429] <;> norm_num
@[simp] lemma totient_cert_1717 : Nat.totient 1717 = 1600 := by
  rw [show 1717 = 17 * 101 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 101)]
  rw [totient_cert_17, totient_cert_101] <;> norm_num
@[simp] lemma totient_cert_1718 : Nat.totient 1718 = 858 := by
  rw [show 1718 = 2 * 859 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 859)]
  rw [totient_cert_2, totient_cert_859] <;> norm_num
@[simp] lemma totient_cert_1719 : Nat.totient 1719 = 1140 := by
  rw [show 1719 = 9 * 191 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 191)]
  rw [totient_cert_9, totient_cert_191] <;> norm_num
@[simp] lemma totient_cert_1720 : Nat.totient 1720 = 672 := by
  rw [show 1720 = 8 * 215 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 215)]
  rw [totient_cert_8, totient_cert_215] <;> norm_num
@[simp] lemma totient_cert_1721 : Nat.totient 1721 = 1720 := by
  rw [show 1721 = 1721^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1721) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1722 : Nat.totient 1722 = 480 := by
  rw [show 1722 = 2 * 861 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 861)]
  rw [totient_cert_2, totient_cert_861] <;> norm_num
@[simp] lemma totient_cert_1723 : Nat.totient 1723 = 1722 := by
  rw [show 1723 = 1723^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1723) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1724 : Nat.totient 1724 = 860 := by
  rw [show 1724 = 4 * 431 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 431)]
  rw [totient_cert_4, totient_cert_431] <;> norm_num
@[simp] lemma totient_cert_1725 : Nat.totient 1725 = 880 := by
  rw [show 1725 = 3 * 575 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 575)]
  rw [totient_cert_3, totient_cert_575] <;> norm_num
@[simp] lemma totient_cert_1726 : Nat.totient 1726 = 862 := by
  rw [show 1726 = 2 * 863 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 863)]
  rw [totient_cert_2, totient_cert_863] <;> norm_num
@[simp] lemma totient_cert_1727 : Nat.totient 1727 = 1560 := by
  rw [show 1727 = 11 * 157 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 157)]
  rw [totient_cert_11, totient_cert_157] <;> norm_num
@[simp] lemma totient_cert_1728 : Nat.totient 1728 = 576 := by
  rw [show 1728 = 64 * 27 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 64 27)]
  rw [totient_cert_64, totient_cert_27] <;> norm_num
@[simp] lemma totient_cert_1729 : Nat.totient 1729 = 1296 := by
  rw [show 1729 = 7 * 247 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 247)]
  rw [totient_cert_7, totient_cert_247] <;> norm_num
@[simp] lemma totient_cert_1730 : Nat.totient 1730 = 688 := by
  rw [show 1730 = 2 * 865 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 865)]
  rw [totient_cert_2, totient_cert_865] <;> norm_num
@[simp] lemma totient_cert_1731 : Nat.totient 1731 = 1152 := by
  rw [show 1731 = 3 * 577 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 577)]
  rw [totient_cert_3, totient_cert_577] <;> norm_num
@[simp] lemma totient_cert_1732 : Nat.totient 1732 = 864 := by
  rw [show 1732 = 4 * 433 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 433)]
  rw [totient_cert_4, totient_cert_433] <;> norm_num
@[simp] lemma totient_cert_1733 : Nat.totient 1733 = 1732 := by
  rw [show 1733 = 1733^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1733) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1734 : Nat.totient 1734 = 544 := by
  rw [show 1734 = 2 * 867 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 867)]
  rw [totient_cert_2, totient_cert_867] <;> norm_num
@[simp] lemma totient_cert_1735 : Nat.totient 1735 = 1384 := by
  rw [show 1735 = 5 * 347 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 347)]
  rw [totient_cert_5, totient_cert_347] <;> norm_num
@[simp] lemma totient_cert_1736 : Nat.totient 1736 = 720 := by
  rw [show 1736 = 8 * 217 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 217)]
  rw [totient_cert_8, totient_cert_217] <;> norm_num
@[simp] lemma totient_cert_1737 : Nat.totient 1737 = 1152 := by
  rw [show 1737 = 9 * 193 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 193)]
  rw [totient_cert_9, totient_cert_193] <;> norm_num
@[simp] lemma totient_cert_1738 : Nat.totient 1738 = 780 := by
  rw [show 1738 = 2 * 869 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 869)]
  rw [totient_cert_2, totient_cert_869] <;> norm_num
@[simp] lemma totient_cert_1739 : Nat.totient 1739 = 1656 := by
  rw [show 1739 = 37 * 47 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 37 47)]
  rw [totient_cert_37, totient_cert_47] <;> norm_num
@[simp] lemma totient_cert_1740 : Nat.totient 1740 = 448 := by
  rw [show 1740 = 4 * 435 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 435)]
  rw [totient_cert_4, totient_cert_435] <;> norm_num
@[simp] lemma totient_cert_1741 : Nat.totient 1741 = 1740 := by
  rw [show 1741 = 1741^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1741) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1742 : Nat.totient 1742 = 792 := by
  rw [show 1742 = 2 * 871 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 871)]
  rw [totient_cert_2, totient_cert_871] <;> norm_num
@[simp] lemma totient_cert_1743 : Nat.totient 1743 = 984 := by
  rw [show 1743 = 3 * 581 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 581)]
  rw [totient_cert_3, totient_cert_581] <;> norm_num
@[simp] lemma totient_cert_1744 : Nat.totient 1744 = 864 := by
  rw [show 1744 = 16 * 109 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 109)]
  rw [totient_cert_16, totient_cert_109] <;> norm_num
@[simp] lemma totient_cert_1745 : Nat.totient 1745 = 1392 := by
  rw [show 1745 = 5 * 349 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 349)]
  rw [totient_cert_5, totient_cert_349] <;> norm_num
@[simp] lemma totient_cert_1746 : Nat.totient 1746 = 576 := by
  rw [show 1746 = 2 * 873 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 873)]
  rw [totient_cert_2, totient_cert_873] <;> norm_num
@[simp] lemma totient_cert_1747 : Nat.totient 1747 = 1746 := by
  rw [show 1747 = 1747^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1747) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1748 : Nat.totient 1748 = 792 := by
  rw [show 1748 = 4 * 437 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 437)]
  rw [totient_cert_4, totient_cert_437] <;> norm_num
@[simp] lemma totient_cert_1749 : Nat.totient 1749 = 1040 := by
  rw [show 1749 = 3 * 583 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 583)]
  rw [totient_cert_3, totient_cert_583] <;> norm_num
@[simp] lemma totient_cert_1750 : Nat.totient 1750 = 600 := by
  rw [show 1750 = 2 * 875 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 875)]
  rw [totient_cert_2, totient_cert_875] <;> norm_num
@[simp] lemma totient_cert_1751 : Nat.totient 1751 = 1632 := by
  rw [show 1751 = 17 * 103 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 17 103)]
  rw [totient_cert_17, totient_cert_103] <;> norm_num
@[simp] lemma totient_cert_1752 : Nat.totient 1752 = 576 := by
  rw [show 1752 = 8 * 219 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 219)]
  rw [totient_cert_8, totient_cert_219] <;> norm_num
@[simp] lemma totient_cert_1753 : Nat.totient 1753 = 1752 := by
  rw [show 1753 = 1753^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1753) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1754 : Nat.totient 1754 = 876 := by
  rw [show 1754 = 2 * 877 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 877)]
  rw [totient_cert_2, totient_cert_877] <;> norm_num
@[simp] lemma totient_cert_1755 : Nat.totient 1755 = 864 := by
  rw [show 1755 = 27 * 65 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 27 65)]
  rw [totient_cert_27, totient_cert_65] <;> norm_num
@[simp] lemma totient_cert_1756 : Nat.totient 1756 = 876 := by
  rw [show 1756 = 4 * 439 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 439)]
  rw [totient_cert_4, totient_cert_439] <;> norm_num
@[simp] lemma totient_cert_1757 : Nat.totient 1757 = 1500 := by
  rw [show 1757 = 7 * 251 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 251)]
  rw [totient_cert_7, totient_cert_251] <;> norm_num
@[simp] lemma totient_cert_1758 : Nat.totient 1758 = 584 := by
  rw [show 1758 = 2 * 879 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 879)]
  rw [totient_cert_2, totient_cert_879] <;> norm_num
@[simp] lemma totient_cert_1759 : Nat.totient 1759 = 1758 := by
  rw [show 1759 = 1759^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1759) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1760 : Nat.totient 1760 = 640 := by
  rw [show 1760 = 32 * 55 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 32 55)]
  rw [totient_cert_32, totient_cert_55] <;> norm_num
@[simp] lemma totient_cert_1761 : Nat.totient 1761 = 1172 := by
  rw [show 1761 = 3 * 587 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 587)]
  rw [totient_cert_3, totient_cert_587] <;> norm_num
@[simp] lemma totient_cert_1762 : Nat.totient 1762 = 880 := by
  rw [show 1762 = 2 * 881 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 881)]
  rw [totient_cert_2, totient_cert_881] <;> norm_num
@[simp] lemma totient_cert_1763 : Nat.totient 1763 = 1680 := by
  rw [show 1763 = 41 * 43 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 41 43)]
  rw [totient_cert_41, totient_cert_43] <;> norm_num
@[simp] lemma totient_cert_1764 : Nat.totient 1764 = 504 := by
  rw [show 1764 = 4 * 441 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 441)]
  rw [totient_cert_4, totient_cert_441] <;> norm_num
@[simp] lemma totient_cert_1765 : Nat.totient 1765 = 1408 := by
  rw [show 1765 = 5 * 353 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 353)]
  rw [totient_cert_5, totient_cert_353] <;> norm_num
@[simp] lemma totient_cert_1766 : Nat.totient 1766 = 882 := by
  rw [show 1766 = 2 * 883 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 883)]
  rw [totient_cert_2, totient_cert_883] <;> norm_num
@[simp] lemma totient_cert_1767 : Nat.totient 1767 = 1080 := by
  rw [show 1767 = 3 * 589 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 589)]
  rw [totient_cert_3, totient_cert_589] <;> norm_num
@[simp] lemma totient_cert_1768 : Nat.totient 1768 = 768 := by
  rw [show 1768 = 8 * 221 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 221)]
  rw [totient_cert_8, totient_cert_221] <;> norm_num
@[simp] lemma totient_cert_1769 : Nat.totient 1769 = 1680 := by
  rw [show 1769 = 29 * 61 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 29 61)]
  rw [totient_cert_29, totient_cert_61] <;> norm_num
@[simp] lemma totient_cert_1770 : Nat.totient 1770 = 464 := by
  rw [show 1770 = 2 * 885 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 885)]
  rw [totient_cert_2, totient_cert_885] <;> norm_num
@[simp] lemma totient_cert_1771 : Nat.totient 1771 = 1320 := by
  rw [show 1771 = 7 * 253 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 253)]
  rw [totient_cert_7, totient_cert_253] <;> norm_num
@[simp] lemma totient_cert_1772 : Nat.totient 1772 = 884 := by
  rw [show 1772 = 4 * 443 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 443)]
  rw [totient_cert_4, totient_cert_443] <;> norm_num
@[simp] lemma totient_cert_1773 : Nat.totient 1773 = 1176 := by
  rw [show 1773 = 9 * 197 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 197)]
  rw [totient_cert_9, totient_cert_197] <;> norm_num
@[simp] lemma totient_cert_1774 : Nat.totient 1774 = 886 := by
  rw [show 1774 = 2 * 887 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 887)]
  rw [totient_cert_2, totient_cert_887] <;> norm_num
@[simp] lemma totient_cert_1775 : Nat.totient 1775 = 1400 := by
  rw [show 1775 = 25 * 71 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 25 71)]
  rw [totient_cert_25, totient_cert_71] <;> norm_num
@[simp] lemma totient_cert_1776 : Nat.totient 1776 = 576 := by
  rw [show 1776 = 16 * 111 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 16 111)]
  rw [totient_cert_16, totient_cert_111] <;> norm_num
@[simp] lemma totient_cert_1777 : Nat.totient 1777 = 1776 := by
  rw [show 1777 = 1777^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1777) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1778 : Nat.totient 1778 = 756 := by
  rw [show 1778 = 2 * 889 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 889)]
  rw [totient_cert_2, totient_cert_889] <;> norm_num
@[simp] lemma totient_cert_1779 : Nat.totient 1779 = 1184 := by
  rw [show 1779 = 3 * 593 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 593)]
  rw [totient_cert_3, totient_cert_593] <;> norm_num
@[simp] lemma totient_cert_1780 : Nat.totient 1780 = 704 := by
  rw [show 1780 = 4 * 445 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 445)]
  rw [totient_cert_4, totient_cert_445] <;> norm_num
@[simp] lemma totient_cert_1781 : Nat.totient 1781 = 1632 := by
  rw [show 1781 = 13 * 137 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 137)]
  rw [totient_cert_13, totient_cert_137] <;> norm_num
@[simp] lemma totient_cert_1782 : Nat.totient 1782 = 540 := by
  rw [show 1782 = 2 * 891 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 891)]
  rw [totient_cert_2, totient_cert_891] <;> norm_num
@[simp] lemma totient_cert_1783 : Nat.totient 1783 = 1782 := by
  rw [show 1783 = 1783^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1783) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1784 : Nat.totient 1784 = 888 := by
  rw [show 1784 = 8 * 223 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 223)]
  rw [totient_cert_8, totient_cert_223] <;> norm_num
@[simp] lemma totient_cert_1785 : Nat.totient 1785 = 768 := by
  rw [show 1785 = 3 * 595 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 595)]
  rw [totient_cert_3, totient_cert_595] <;> norm_num
@[simp] lemma totient_cert_1786 : Nat.totient 1786 = 828 := by
  rw [show 1786 = 2 * 893 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 893)]
  rw [totient_cert_2, totient_cert_893] <;> norm_num
@[simp] lemma totient_cert_1787 : Nat.totient 1787 = 1786 := by
  rw [show 1787 = 1787^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1787) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1788 : Nat.totient 1788 = 592 := by
  rw [show 1788 = 4 * 447 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 447)]
  rw [totient_cert_4, totient_cert_447] <;> norm_num
@[simp] lemma totient_cert_1789 : Nat.totient 1789 = 1788 := by
  rw [show 1789 = 1789^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1789) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1790 : Nat.totient 1790 = 712 := by
  rw [show 1790 = 2 * 895 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 895)]
  rw [totient_cert_2, totient_cert_895] <;> norm_num
@[simp] lemma totient_cert_1791 : Nat.totient 1791 = 1188 := by
  rw [show 1791 = 9 * 199 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 9 199)]
  rw [totient_cert_9, totient_cert_199] <;> norm_num
@[simp] lemma totient_cert_1792 : Nat.totient 1792 = 768 := by
  rw [show 1792 = 256 * 7 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 256 7)]
  rw [totient_cert_256, totient_cert_7] <;> norm_num
@[simp] lemma totient_cert_1793 : Nat.totient 1793 = 1620 := by
  rw [show 1793 = 11 * 163 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 11 163)]
  rw [totient_cert_11, totient_cert_163] <;> norm_num
@[simp] lemma totient_cert_1794 : Nat.totient 1794 = 528 := by
  rw [show 1794 = 2 * 897 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 897)]
  rw [totient_cert_2, totient_cert_897] <;> norm_num
@[simp] lemma totient_cert_1795 : Nat.totient 1795 = 1432 := by
  rw [show 1795 = 5 * 359 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 359)]
  rw [totient_cert_5, totient_cert_359] <;> norm_num
@[simp] lemma totient_cert_1796 : Nat.totient 1796 = 896 := by
  rw [show 1796 = 4 * 449 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 449)]
  rw [totient_cert_4, totient_cert_449] <;> norm_num
@[simp] lemma totient_cert_1797 : Nat.totient 1797 = 1196 := by
  rw [show 1797 = 3 * 599 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 599)]
  rw [totient_cert_3, totient_cert_599] <;> norm_num
@[simp] lemma totient_cert_1798 : Nat.totient 1798 = 840 := by
  rw [show 1798 = 2 * 899 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 899)]
  rw [totient_cert_2, totient_cert_899] <;> norm_num
@[simp] lemma totient_cert_1799 : Nat.totient 1799 = 1536 := by
  rw [show 1799 = 7 * 257 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 7 257)]
  rw [totient_cert_7, totient_cert_257] <;> norm_num
@[simp] lemma totient_cert_1800 : Nat.totient 1800 = 480 := by
  rw [show 1800 = 8 * 225 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 8 225)]
  rw [totient_cert_8, totient_cert_225] <;> norm_num
@[simp] lemma totient_cert_1801 : Nat.totient 1801 = 1800 := by
  rw [show 1801 = 1801^1 by norm_num, Nat.totient_prime_pow (by norm_num : Nat.Prime 1801) (by norm_num : 0 < 1)] <;> norm_num
@[simp] lemma totient_cert_1802 : Nat.totient 1802 = 832 := by
  rw [show 1802 = 2 * 901 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 901)]
  rw [totient_cert_2, totient_cert_901] <;> norm_num
@[simp] lemma totient_cert_1803 : Nat.totient 1803 = 1200 := by
  rw [show 1803 = 3 * 601 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 3 601)]
  rw [totient_cert_3, totient_cert_601] <;> norm_num
@[simp] lemma totient_cert_1804 : Nat.totient 1804 = 800 := by
  rw [show 1804 = 4 * 451 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 4 451)]
  rw [totient_cert_4, totient_cert_451] <;> norm_num
@[simp] lemma totient_cert_1805 : Nat.totient 1805 = 1368 := by
  rw [show 1805 = 5 * 361 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 5 361)]
  rw [totient_cert_5, totient_cert_361] <;> norm_num
@[simp] lemma totient_cert_1806 : Nat.totient 1806 = 504 := by
  rw [show 1806 = 2 * 903 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 2 903)]
  rw [totient_cert_2, totient_cert_903] <;> norm_num
@[simp] lemma totient_cert_1807 : Nat.totient 1807 = 1656 := by
  rw [show 1807 = 13 * 139 by norm_num, Nat.totient_mul (by norm_num : Nat.Coprime 13 139)]
  rw [totient_cert_13, totient_cert_139] <;> norm_num

lemma den_not_power_1807 : ¬ (A060841_val_rat 1807).den.isPowerOfTwo := by
  have hden : (A060841_val_rat 1807).den = 3 * 2 ^ 2342 := by
    change ((Icc 1 1807).prod (fun k : ℕ => ((k : ℚ) ^ 2) / (k.totient : ℚ))).den = 3 * 2 ^ 2342
    norm_num [Finset.prod_Icc_succ_top]
  rw [Nat.isPowerOfTwo]
  rintro ⟨k, hk⟩
  have h3 : 3 ∣ 2 ^ k := by
    rw [← hk, hden]
    exact dvd_mul_right 3 (2 ^ 2342)
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at h32

/-- Conjecture: 1/det(M) is an integer only for n: 1 - 34, 36 and 38.
All denominators are powers of two (A000079). -/
theorem oeis_60841_conjecture_0.disproof :
  ¬ (∀ (n : ℕ), 1 ≤ n →
    (A060841_val_rat n).den.isPowerOfTwo ∧
    ((A060841_val_rat n).isInt ↔ n ∈ Icc 1 34 ∨ n = 36 ∨ n = 38)) :=
by
  intro h
  exact den_not_power_1807 (h 1807 (by norm_num : 1 ≤ 1807)).1
