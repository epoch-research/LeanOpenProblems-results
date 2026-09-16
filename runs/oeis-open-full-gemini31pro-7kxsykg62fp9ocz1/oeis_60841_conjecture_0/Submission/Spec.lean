import FormalConjectures.Util.ProblemImports
import Submission.Totient.All
import Submission.Totient.SumK

open Nat Finset Rat
open scoped BigOperators

set_option maxHeartbeats 2000000000
set_option maxRecDepth 20000000

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

/-- Conjecture: 1/det(M) is an integer only for n: 1 - 34, 36 and 38.
All denominators are powers of two (A000079). -/
theorem oeis_60841_conjecture_0 (n : ℕ) (hn : 1 ≤ n) :
  (A060841_val_rat n).den.isPowerOfTwo ∧
  ((A060841_val_rat n).isInt ↔ n ∈ Icc 1 34 ∨ n = 36 ∨ n = 38) :=
by sorry

theorem maxPowDiv_three_zero : maxPowDiv 3 0 = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.zero

theorem maxPowDiv_three_one : maxPowDiv 3 1 = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.one

theorem maxPowDiv_three_mul (k : ℕ) (hk : k ≠ 0) : maxPowDiv 3 (3 * k) = 1 + maxPowDiv 3 k := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  rw [padicValNat.mul (by decide) hk, padicValNat_self, add_comm]

theorem maxPowDiv_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n) : maxPowDiv 3 n = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.eq_zero_of_not_dvd hn

theorem v3_fast_eq_maxPowDiv : ∀ fuel n, n < 3^fuel → v3_fast n fuel = maxPowDiv 3 n
  | 0, n, hn => by
    have h : n = 0 := by omega
    subst h
    rw [v3_fast, maxPowDiv_three_zero]
  | f + 1, n, hn => by
    unfold v3_fast
    split_ifs with h1 h2
    · subst h1; rw [maxPowDiv_three_zero]
    · have hk : n / 3 < 3^f := by omega
      have h_div : n = 3 * (n / 3) := by
        exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2) |>.symm
      have hk_ne : n / 3 ≠ 0 := by
        intro h
        rw [h, mul_zero] at h_div
        exact h1 h_div
      rw [v3_fast_eq_maxPowDiv f (n / 3) hk]
      have h_pow : maxPowDiv 3 n = 1 + maxPowDiv 3 (n / 3) := by
        conv => lhs; rw [h_div]
        exact maxPowDiv_three_mul (n / 3) hk_ne
      rw [h_pow]
    · have h_not_dvd : ¬ 3 ∣ n := fun hdvd => h2 (Nat.mod_eq_zero_of_dvd hdvd)
      exact (maxPowDiv_not_dvd n h_not_dvd).symm

theorem maxPowDiv_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
  maxPowDiv 3 (a * b) = maxPowDiv 3 a + maxPowDiv 3 b := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  exact padicValNat.mul ha hb

theorem totient_pos' (x : ℕ) (hx : 1 ≤ x) : 0 < x.totient := by
  exact Nat.totient_pos.mpr (by omega)

theorem maxPowDiv_prod_totient (n : ℕ) (hn_le : n ≤ 1807) :
  maxPowDiv 3 ((Icc 1 n).prod (fun k => k.totient)) = (Icc 1 n).sum (fun k => v3_fast k.totient 100) := by
  induction n with
  | zero =>
    rw [Icc_eq_empty_of_lt (by decide), prod_empty, sum_empty, maxPowDiv_three_one]
  | succ k ih =>
    have hk_le : k ≤ 1807 := by omega
    have ih_app := ih hk_le
    rw [prod_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
    have hk_val : (k + 1).totient < 3^100 := by
      have : (k + 1).totient ≤ k + 1 := Nat.totient_le (k + 1)
      omega
    rw [v3_fast_eq_maxPowDiv 100 ((k + 1).totient) hk_val]
    have h_prod_ne_zero : (Icc 1 k).prod (fun x => x.totient) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro x hx
      have hx1 : 1 ≤ x := by rw [mem_Icc] at hx; exact hx.1
      have ht := totient_pos' x hx1
      omega
    have hk1_ne_zero : (k + 1).totient ≠ 0 := by
      have ht := totient_pos' (k + 1) (by omega)
      omega
    rw [maxPowDiv_mul h_prod_ne_zero hk1_ne_zero]
    rw [ih_app]

theorem maxPowDiv_prod_k2 (n : ℕ) (hn_le : n ≤ 1807) :
  maxPowDiv 3 ((Icc 1 n).prod (fun k => k^2)) = (Icc 1 n).sum (fun k => 2 * v3_fast k 100) := by
  induction n with
  | zero =>
    rw [Icc_eq_empty_of_lt (by decide), prod_empty, sum_empty, maxPowDiv_three_one]
  | succ k ih =>
    have hk_le : k ≤ 1807 := by omega
    have ih_app := ih hk_le
    rw [prod_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
    have hk_val : (k + 1) < 3^100 := by omega
    rw [v3_fast_eq_maxPowDiv 100 (k + 1) hk_val]
    have h_prod_ne_zero : (Icc 1 k).prod (fun x => x^2) ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro x hx
      have hx1 : 1 ≤ x := by rw [mem_Icc] at hx; exact hx.1
      intro h_eq
      have : x = 0 := by exact (eq_zero_of_pow_eq_zero h_eq)
      omega
    have hk1_ne_zero : (k + 1)^2 ≠ 0 := by
      intro h_eq
      have : k + 1 = 0 := by exact (eq_zero_of_pow_eq_zero h_eq)
      omega
    rw [maxPowDiv_mul h_prod_ne_zero hk1_ne_zero]
    have h_k1_ne : k + 1 ≠ 0 := by omega
    rw [sq (k+1)]
    rw [maxPowDiv_mul h_k1_ne h_k1_ne]
    rw [ih_app]
    omega

theorem maxPowDiv_two_pow (m : ℕ) : maxPowDiv 3 (2^m) = 0 := by
  have h3 : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← padicValNat.padicValNat_eq_maxPowDiv]
  have h2 : ¬ 3 ∣ 2 := by decide
  have h : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd h2
  rw [padicValNat.pow m (by decide)]
  rw [h, mul_zero]

theorem pow_two_ne_zero (m : ℕ) : 2^m ≠ 0 := by positivity

theorem le_of_power_of_two_den {N D A m : ℕ} (hD : D ≠ 0) (hN : N ≠ 0) (hA : A ≠ 0)
  (heq : A * D = N * 2^m) : maxPowDiv 3 D ≤ maxPowDiv 3 N := by
  have h2m : 2^m ≠ 0 := pow_two_ne_zero m
  have h1 : maxPowDiv 3 (A * D) = maxPowDiv 3 A + maxPowDiv 3 D := maxPowDiv_mul hA hD
  have h2 : maxPowDiv 3 (N * 2^m) = maxPowDiv 3 N + maxPowDiv 3 (2^m) := maxPowDiv_mul hN h2m
  rw [heq] at h1
  rw [h1, maxPowDiv_two_pow m, add_zero] at h2
  omega

theorem rat_eq_cross_mul {N D : ℕ} (hD : D ≠ 0) :
  ((N : ℚ) / (D : ℚ)).num.natAbs * D = N * ((N : ℚ) / (D : ℚ)).den := by
  let V := (N : ℚ) / (D : ℚ)
  have h1 : (V.num : ℚ) * (D : ℚ) = (N : ℚ) * (V.den : ℚ) := by
    have hD_rat : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
    have eq1 : V = (N : ℚ) / (D : ℚ) := rfl
    have eq2 : V * (D : ℚ) = (N : ℚ) := div_mul_cancel₀ _ hD_rat |>.symm ▸ congrArg (· * (D:ℚ)) eq1
    have eq3 : (V.num : ℚ) / (V.den : ℚ) * (D : ℚ) = (N : ℚ) := by
      rwa [← num_div_den V] at eq2
    have hden_rat : (V.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr V.den_pos.ne'
    calc (V.num : ℚ) * (D : ℚ) = ((V.num : ℚ) / (V.den : ℚ)) * (V.den : ℚ) * (D : ℚ) := by rw [div_mul_cancel₀ _ hden_rat]
      _ = ((V.num : ℚ) / (V.den : ℚ)) * (D : ℚ) * (V.den : ℚ) := by ring
      _ = (N : ℚ) * (V.den : ℚ) := by rw [eq3]
  have h2 : (V.num * D : ℚ) = ((N * V.den : ℕ) : ℚ) := by
    push_cast
    exact h1
  have h3 : V.num * (D : ℤ) = (N * V.den : ℕ) := by
    exact_mod_cast h2
  have h4 : (V.num * (D : ℤ)).natAbs = ((N * V.den : ℕ) : ℤ).natAbs := by
    rw [h3]
  rw [Int.natAbs_mul] at h4
  simp only [Int.natAbs_natCast] at h4
  exact h4

theorem prod_div_prod (s : Finset ℕ) (f g : ℕ → ℚ) :
  (s.prod (fun k => f k / g k)) = (s.prod (fun k => f k)) / (s.prod (fun k => g k)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, prod_insert ha, ih]
    exact div_mul_div_comm _ _ _ _

theorem cast_prod_N_thm (n : ℕ) : (((Icc 1 n).prod (fun k => k^2) : ℕ) : ℚ) = (Icc 1 n).prod (fun k => (k : ℚ)^2) := by
  push_cast
  rfl

theorem cast_prod_D_thm (n : ℕ) : (((Icc 1 n).prod (fun k => k.totient) : ℕ) : ℚ) = (Icc 1 n).prod (fun k => (k.totient : ℚ)) := by
  push_cast
  rfl

theorem A_eq (n : ℕ) : A060841_val_rat n = (((Icc 1 n).prod (fun k => k^2) : ℕ) : ℚ) / (((Icc 1 n).prod (fun k => k.totient) : ℕ) : ℚ) := by
  dsimp [A060841_val_rat]
  rw [prod_div_prod]
  rw [cast_prod_N_thm n, cast_prod_D_thm n]

theorem maxPowDiv_D_le_N (n : ℕ)
  (h_pow : (A060841_val_rat n).den.isPowerOfTwo)
  (hD : (Icc 1 n).prod (fun k => k.totient) ≠ 0)
  (hN : (Icc 1 n).prod (fun k => k^2) ≠ 0) :
  maxPowDiv 3 ((Icc 1 n).prod (fun k => k.totient)) ≤ maxPowDiv 3 ((Icc 1 n).prod (fun k => k^2)) := by
  rw [A_eq n] at h_pow
  
  generalize h_genN : (Icc 1 n).prod (fun k => k^2) = N_n
  generalize h_genD : (Icc 1 n).prod (fun k => k.totient) = D_n
  
  rw [h_genD] at hD
  rw [h_genN] at hN
  rw [h_genN, h_genD] at h_pow
  
  have heq : ((N_n : ℚ) / (D_n : ℚ)).num.natAbs * D_n = N_n * ((N_n : ℚ) / (D_n : ℚ)).den := rat_eq_cross_mul hD
  
  have h_den_eq : ∃ m, ((N_n : ℚ) / (D_n : ℚ)).den = 2^m := h_pow
  obtain ⟨m, hm⟩ := h_den_eq
  rw [hm] at heq
  
  have hA : ((N_n : ℚ) / (D_n : ℚ)).num.natAbs ≠ 0 := by
    intro h
    rw [h, zero_mul] at heq
    have hN2 : N_n * 2^m ≠ 0 := mul_ne_zero hN (pow_two_ne_zero m)
    exact hN2 heq.symm
  exact le_of_power_of_two_den hD hN hA heq

theorem oeis_60841_conjecture_0.disproof :
  ¬ (∀ (n : ℕ) (hn : 1 ≤ n),
      (A060841_val_rat n).den.isPowerOfTwo ∧
      ((A060841_val_rat n).isInt ↔ n ∈ Icc 1 34 ∨ n = 36 ∨ n = 38)) := by
  intro h
  have h1807 := h 1807 (by decide)
  have h_pow := h1807.1
  
  have hD : (Icc 1 1807).prod (fun k => k.totient) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro x hx
    have hx1 : 1 ≤ x := by rw [mem_Icc] at hx; exact hx.1
    have ht := totient_pos' x hx1
    omega
  have hN : (Icc 1 1807).prod (fun k => k^2) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro x hx
    intro h_eq
    have : x = 0 := by exact (eq_zero_of_pow_eq_zero h_eq)
    have hx1 : 1 ≤ x := by rw [mem_Icc] at hx; exact hx.1
    omega
    
  have h_le := maxPowDiv_D_le_N 1807 h_pow hD hN
  
  have h_sum_D : maxPowDiv 3 ((Icc 1 1807).prod (fun k => k.totient)) = (Icc 1 1807).sum (fun k => v3_fast k.totient 100) := maxPowDiv_prod_totient 1807 (by decide)
  have h_sum_N : maxPowDiv 3 ((Icc 1 1807).prod (fun k => k^2)) = (Icc 1 1807).sum (fun k => 2 * v3_fast k 100) := maxPowDiv_prod_k2 1807 (by decide)
  
  have h_sum_D_val : (Icc 1 1807).sum (fun k => v3_fast k.totient 100) = 1799 := sum_v3_phi_1807
  have h_sum_N_val : (Icc 1 1807).sum (fun k => 2 * v3_fast k 100) = 1798 := sum_v3_k2_1807
  
  rw [h_sum_D, h_sum_N] at h_le
  rw [h_sum_D_val, h_sum_N_val] at h_le
  
  omega

