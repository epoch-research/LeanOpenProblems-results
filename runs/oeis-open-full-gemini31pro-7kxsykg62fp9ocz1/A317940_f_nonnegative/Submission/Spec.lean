import Mathlib.NumberTheory.ArithmeticFunction.Defs
import FormalConjectures.Util.ProblemImports
open Nat
open PowerSeries

/--
A005187: Sum of $\lfloor n / 2^k 
floor$ for $k \ge 0$.
This is $\sum_{k=0}^\infty \lfloor n / 2^k 
floor$.
-/
noncomputable def A005187 (e : ℕ) : ℕ :=
  Finset.sum (Finset.range (e + 1)) fun k ↦ e / (2^k)

/--
A046644: Multiplicative function defined on prime powers $p^e$ as $2^{	ext{A005187}(e)}$.
-/
noncomputable def A046644 (n : ℕ) : ℚ :=
  if n = 0 then 0
  else n.factorization.prod fun _ e ↦ (2 : ℚ) ^ (A005187 e)

/--
The sequence $f(n) \in \mathbb{Q}$ such that $f * f = 	ext{A046644}$.
Defined by well-founded recursion on $\mathbb{N}$ w.r.t. $<$.
-/
noncomputable def A317940_f : ℕ → ℚ :=
  WellFounded.fix (measure id).wf fun n IH ↦
    if n = 0 then 0
    else if n = 1 then 1
    else
      let A_n : ℚ := A046644 n

      let sum_of_products : ℚ := Finset.sum (divisors n) fun d ↦
        if h_prop : d > 1 ∧ d < n then
          have d_lt_n : d < n := h_prop.2
          let q := n / d
          have q_lt_n : q < n := Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) h_prop.1
          IH d d_lt_n * IH q q_lt_n
        else 0
      (A_n - sum_of_products) / 2

/--
A317940: Numerators of sequence whose Dirichlet convolution with itself yields A046644.
$a(n) = 	ext{numerator}(f(n))$, where $f*f = 	ext{A046644}$.
-/
noncomputable def A317940 (n : ℕ) : ℕ :=
  (A317940_f n).num.natAbs

theorem F_deriv_eq (F A Q : PowerSeries ℚ)
  (hA : A = F^2)
  (hderiv : X * derivative ℚ A = 2 * Q * A)
  (hF0 : constantCoeff F ≠ 0) :
  X * derivative ℚ F = Q * F := by
  have h1 : X * derivative ℚ A = 2 * F * (X * derivative ℚ F) := by
    rw [hA, sq, Derivation.leibniz]
    change X * (F * derivative ℚ F + F * derivative ℚ F) = 2 * F * (X * derivative ℚ F)
    ring
  have h2 : 2 * F * (X * derivative ℚ F) = 2 * F * (Q * F) := by
    calc 2 * F * (X * derivative ℚ F) = X * derivative ℚ A := h1.symm
      _ = 2 * Q * A := hderiv
      _ = 2 * Q * F^2 := by rw [hA]
      _ = 2 * F * (Q * F) := by ring
  have h_const : constantCoeff (2 * F) ≠ 0 := by
    simp
    constructor
    · have : constantCoeff (2 : PowerSeries ℚ) = 2 := rfl
      rw [this]
      norm_num
    · exact hF0
  have h_mul_inv : (2 * F)⁻¹ * (2 * F) = 1 := by
    have h_inv := PowerSeries.inv_mul_cancel (2 * F) h_const
    exact h_inv
  have h3 : (2 * F)⁻¹ * (2 * F * (X * derivative ℚ F)) = (2 * F)⁻¹ * (2 * F * (Q * F)) := by
    rw [h2]
  rw [← mul_assoc, h_mul_inv, one_mul] at h3
  rw [← mul_assoc, h_mul_inv, one_mul] at h3
  exact h3

open ArithmeticFunction

def s2 : ℕ → ℕ
| 0 => 0
| (n+1) => s2 ((n+1) / 2) + (n+1) % 2
termination_by n => n

lemma s2_eq (n : ℕ) : s2 n = if n = 0 then 0 else s2 (n / 2) + n % 2 := by
  cases n with
  | zero => simp [s2.eq_1]
  | succ n => simp [s2.eq_2]

@[simp] lemma s2_zero : s2 0 = 0 := by rw [s2_eq]; simp
@[simp] lemma s2_one : s2 1 = 1 := by rw [s2_eq]; simp

lemma s2_add_pow2 (m n : ℕ) (h : n < 2^m) : s2 (n + 2^m) = s2 n + 1 := by
  induction m generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    simp
  | succ m ih =>
    rw [s2_eq (n + 2^(m+1))]
    have hn_pos : n + 2^(m+1) ≠ 0 := by omega
    rw [if_neg hn_pos]
    rw [s2_eq n]
    by_cases hn0 : n = 0
    · simp [hn0]
      have hm1 : 2^(m+1) / 2 = 2^m := by
        rw [pow_add, pow_one]
        exact Nat.mul_div_cancel (2^m) (by omega)
      have hm2 : 2^(m+1) % 2 = 0 := by
        rw [pow_add, pow_one]
        exact Nat.mul_mod_left (2^m) 2
      rw [hm1, hm2, add_zero]
      have : 0 < 2^m := by positivity
      have ih_res := ih 0 this
      simp at ih_res
      exact ih_res
    · simp [hn0]
      have hm1 : (n + 2^(m+1)) / 2 = n / 2 + 2^m := by
        rw [pow_add, pow_one]
        exact Nat.add_mul_div_right n (2^m) (by omega)
      have hm2 : (n + 2^(m+1)) % 2 = n % 2 := by
        rw [pow_add, pow_one]
        exact Nat.add_mul_mod_self_right n (2^m) 2
      rw [hm1, hm2]
      have : n / 2 < 2^m := by
        apply Nat.div_lt_of_lt_mul
        have h1 : n < 2 * 2^m := by
          have h2 : 2^(m+1) = 2 * 2^m := by ring
          omega
        exact h1
      have ih_res := ih (n / 2) this
      omega


lemma s2_le_2n (n : ℕ) : s2 n ≤ 2 * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · rw [s2_eq n, if_pos hn]
      simp
    · rw [s2_eq n, if_neg hn]
      have h1 : n / 2 < n := Nat.div_lt_self (by omega) (by omega)
      have ih_res := ih (n / 2) h1
      have hm : n % 2 ≤ 1 := by omega
      have hn2 : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
      omega


lemma A005187_step (e : ℕ) : A005187 e = e + A005187 (e / 2) := by
  dsimp [A005187]
  by_cases he : e = 0
  · simp [he]
  have h1 : (Finset.range (e + 1)).sum (fun k => e / 2^k) =
            (Finset.range e).sum (fun k => e / 2^(k+1)) + e / 2^0 := by
    exact Finset.sum_range_succ' (fun k => e / 2^k) e
  rw [h1]
  have h_div : e / 2^0 = e := by simp
  rw [h_div, add_comm]
  congr 1
  have h2 : ∀ k, e / 2^(k+1) = (e / 2) / 2^k := by
    intro k
    have h_pow : 2^(k+1) = 2 * 2^k := by ring
    rw [h_pow]
    exact (Nat.div_div_eq_div_mul e 2 (2^k)).symm
  have h3 : (Finset.range e).sum (fun k => e / 2^(k+1)) = (Finset.range e).sum (fun k => (e / 2) / 2^k) := by
    apply Finset.sum_congr rfl
    intro k _
    exact h2 k
  rw [h3]
  have h4 : e / 2 + 1 ≤ e := by omega
  have h5 := Finset.sum_range_add_sum_Ico (fun k => (e / 2) / 2^k) h4
  rw [← h5]
  have h6 : (Finset.Ico (e / 2 + 1) e).sum (fun k => (e / 2) / 2^k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h7 : 2^k > e / 2 := by
      have h8 : e / 2 < 2^(e / 2) := Nat.lt_pow_self (by omega)
      have h9 : 2^(e / 2) ≤ 2^k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact Nat.div_eq_of_lt h7
  rw [h6, add_zero]

lemma A005187_eq (e : ℕ) : A005187 e = 2 * e - s2 e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e = 0
    · simp [he, A005187, s2_eq]
    · rw [A005187_step e]
      have h_lt : e / 2 < e := Nat.div_lt_self (by omega) (by omega)
      rw [ih (e / 2) h_lt]
      rw [s2_eq e, if_neg he]
      have h_div : 2 * (e / 2) + e % 2 = e := Nat.div_add_mod e 2
      have hm : e % 2 ≤ 1 := by omega
      have h_s2 : s2 (e / 2) ≤ 2 * (e / 2) := s2_le_2n (e / 2)
      omega


noncomputable def c_val (i : ℕ) : ℚ := (2 : ℚ) ^ (2^(i+1) - 1)

noncomputable def P (i : ℕ) : PowerSeries ℚ :=
  1 + (C (c_val i)) * X ^ (2^i)

noncomputable def P_prod : ℕ → PowerSeries ℚ
| 0 => 1
| (m + 1) => P_prod m * P m


lemma A_seq_step (m n : ℕ) (h : n < 2^m) :
  (2 : ℚ) ^ (2 * (n + 2^m) - s2 (n + 2^m)) = (2 : ℚ) ^ (2 * n - s2 n) * c_val m := by
  rw [s2_add_pow2 m n h, c_val]
  have hs : s2 n ≤ 2 * n := s2_le_2n n
  have hp : 1 ≤ 2^(m+1) := by exact Nat.one_le_two_pow
  have h2 : 2^(m+1) = 2 * 2^m := by ring
  have h1 : 2 * (n + 2^m) - (s2 n + 1) = (2 * n - s2 n) + (2^(m+1) - 1) := by omega
  rw [h1, pow_add]

def A_seq (n : ℕ) : ℚ := (2 : ℚ) ^ (2 * n - s2 n)

lemma coeff_C_mul_A (A : PowerSeries ℚ) (c : ℚ) (n : ℕ) :
  coeff n (C c * A) = c * coeff n A := by
  have h1 : C c * A = c • A := by
    have h2 : (C c : PowerSeries ℚ) = algebraMap ℚ (PowerSeries ℚ) c := rfl
    rw [h2, ← Algebra.smul_def c A]
  rw [h1]
  exact LinearMap.map_smul (coeff n) c A

lemma coeff_mul_C_mul_X_pow (A : PowerSeries ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (A * (C c * X ^ k)) = if h : n ≥ k then coeff (n - k) A * c else 0 := by
  have h1 : A * (C c * X ^ k) = C c * A * X ^ k := by ring
  rw [h1, coeff_mul_X_pow']
  by_cases hk : n ≥ k
  · have h2 : k ≤ n := by omega
    rw [if_pos h2, dif_pos hk, coeff_C_mul_A]
    ring
  · have : ¬ (k ≤ n) := by omega
    rw [if_neg this]
    have h3 : ¬ (n ≥ k) := by omega
    rw [dif_neg h3]

lemma coeff_P_prod_zero (m n : ℕ) (h : n ≥ 2^m) : coeff n (P_prod m) = 0 := by
  induction m generalizing n with
  | zero =>
    have hn : n > 0 := by omega
    cases n with
    | zero => contradiction
    | succ n => simp [P_prod]
  | succ m ih =>
    dsimp [P_prod, P]
    rw [mul_add, mul_one, map_add]
    rw [coeff_mul_C_mul_X_pow]
    by_cases hn2 : n ≥ 2^m
    · rw [dif_pos hn2]
      have h1 : coeff n (P_prod m) = 0 := ih n hn2
      rw [h1, zero_add]
      have h2 : n - 2^m ≥ 2^m := by omega
      have h3 : coeff (n - 2^m) (P_prod m) = 0 := ih (n - 2^m) h2
      rw [h3, zero_mul]
    · have : ¬ (n ≥ 2^m) := hn2
      omega

lemma coeff_P_prod (m n : ℕ) (h : n < 2^m) : coeff n (P_prod m) = A_seq n := by
  induction m generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    simp [hn, P_prod, A_seq]
  | succ m ih =>
    dsimp [P_prod, P]
    rw [mul_add, mul_one, map_add]
    rw [coeff_mul_C_mul_X_pow]
    by_cases hn2 : n ≥ 2^m
    · rw [dif_pos hn2]
      have h1 : coeff n (P_prod m) = 0 := coeff_P_prod_zero m n hn2
      rw [h1, zero_add]
      have h2 : n - 2^m < 2^m := by omega
      have h3 : coeff (n - 2^m) (P_prod m) = A_seq (n - 2^m) := ih (n - 2^m) h2
      rw [h3]
      have h_n : n = (n - 2^m) + 2^m := by omega
      nth_rw 2 [h_n]
      have h4 := A_seq_step m (n - 2^m) h2
      exact h4.symm
    · have h_not : ¬ (n ≥ 2^m) := hn2
      rw [dif_neg h_not, add_zero]
      have h_lt : n < 2^m := by omega
      exact ih n h_lt

noncomputable def Q (i : ℕ) : PowerSeries ℚ :=
  mk fun n ↦
    if n > 0 ∧ n % 2^i = 0 then
      let m := n / 2^i
      (-1 : ℚ) ^ (m - 1) * (c_val i) ^ m * (2^i : ℕ)
    else 0

noncomputable def Q_sum : ℕ → PowerSeries ℚ
| 0 => 0
| (m + 1) => Q_sum m + Q m

lemma coeff_Q_sum (m n : ℕ) :
  coeff n (Q_sum m) = (Finset.range m).sum (fun i => coeff n (Q i)) := by
  induction m with
  | zero => simp [Q_sum]
  | succ m ih =>
    dsimp [Q_sum]
    rw [LinearMap.map_add, ih, Finset.sum_range_succ]

lemma le_padicValNat_of_dvd (n i : ℕ) (hn : n > 0) (h : 2^i ∣ n) : i ≤ padicValNat 2 n := by
  by_contra h_contra
  push_neg at h_contra
  have : 2 ^ (padicValNat 2 n + 1) ∣ 2 ^ i := Nat.pow_dvd_pow _ h_contra
  have h_dvd : 2 ^ (padicValNat 2 n + 1) ∣ n := Nat.dvd_trans this h
  have hn_neq : n ≠ 0 := by omega
  have h_not : ¬ 2 ^ (padicValNat 2 n + 1) ∣ n := pow_succ_padicValNat_not_dvd hn_neq
  contradiction


lemma neg_one_pow_even {n : ℕ} (h : n % 2 = 0) : (-1 : ℚ) ^ n = 1 := by
  have : (-1 : ℚ) ^ n = ((-1 : ℚ) ^ 2) ^ (n / 2) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [this]
  have : (-1 : ℚ) ^ 2 = 1 := by norm_num
  rw [this, one_pow]

lemma neg_one_pow_odd {n : ℕ} (h : n % 2 = 1) : (-1 : ℚ) ^ n = -1 := by
  have : (-1 : ℚ) ^ n = (-1 : ℚ) ^ (n - 1) * (-1 : ℚ) := by
    have h1 : n = n - 1 + 1 := by omega
    nth_rw 1 [h1]
    rw [pow_add, pow_one]
  rw [this]
  have h2 : (n - 1) % 2 = 0 := by omega
  rw [neg_one_pow_even h2]
  ring

lemma Q_sign_lt (k a i : ℕ) (hk : k > 0) (ha : a = padicValNat 2 k) (hi : i < a) :
  (-1 : ℚ) ^ (k / 2^i - 1) = -1 := by
  have h1 : k / 2^i = (k / 2^a) * 2^(a - i) := by
    have h_dvd : 2^a ∣ k := by
      rw [ha]
      exact pow_padicValNat_dvd
    have h_k : k = (k / 2^a) * 2^a := (Nat.div_mul_cancel h_dvd).symm
    nth_rw 1 [h_k]
    have h_pow : 2^a = 2^(a - i) * 2^i := by
      rw [← pow_add]
      congr 1
      omega
    rw [h_pow, ← mul_assoc]
    have h2 : 2^i > 0 := by positivity
    exact Nat.mul_div_cancel _ h2
  have h2 : 2 ∣ 2^(a-i) := by
    have : a - i = a - i - 1 + 1 := by omega
    rw [this, pow_add, pow_one]
    exact dvd_mul_left 2 (2 ^ (a - i - 1))
  rcases h2 with ⟨c, hc⟩
  have h3 : k / 2^i = 2 * ((k / 2^a) * c) := by
    rw [h1, hc]
    ring
  have h4 : k / 2^i ≥ 1 := by
    have : 2^i ≤ k := by
      have : 2^i ≤ 2^a := Nat.pow_le_pow_right (by omega) (by omega)
      have h_a : 2^a ≤ k := by
        have h_dvd : 2^a ∣ k := by rw [ha]; exact pow_padicValNat_dvd
        exact Nat.le_of_dvd hk h_dvd
      omega
    exact Nat.div_pos this (by positivity)
  have h5 : (k / 2^i - 1) % 2 = 1 := by omega
  exact neg_one_pow_odd h5

lemma inv_pow_le {n m : ℕ} (h : n ≤ m) : (2 : ℚ)⁻¹ ^ m ≤ (2 : ℚ)⁻¹ ^ n := by
  have h1 : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ m := by
    apply pow_le_pow_right₀ (by norm_num) h
  have h2 : 0 < (2 : ℚ) ^ n := by positivity
  have h3 : 0 < (2 : ℚ) ^ m := by positivity
  rw [inv_pow, inv_pow]
  rw [inv_le_inv₀ h3 h2]
  exact h1

lemma sum_bound_strong (a m0 : ℕ) (hm : m0 ≥ 1) :
  (Finset.range a).sum (fun i => (2 : ℚ)⁻¹ ^ (i + 1 + m0 * 2^(i + 1))) ≤ (2 : ℚ)⁻¹ ^ (2 * m0) - (2 : ℚ)⁻¹ ^ (a + 2 * m0) := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [Finset.sum_range_succ]
    have h1 : (2 : ℚ)⁻¹ ^ (a + 1 + m0 * 2 ^ (a + 1)) ≤ (2 : ℚ)⁻¹ ^ (a + 1 + 2 * m0) := by
      apply inv_pow_le
      have h_pow2 : 2 ≤ 2 ^ (a + 1) := by
        have : (2 : ℕ) ^ 1 ≤ 2 ^ (a + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact this
      nlinarith
    have h2 : (2 : ℚ)⁻¹ ^ (a + 2 * m0) = (2 : ℚ)⁻¹ ^ (a + 1 + 2 * m0) + (2 : ℚ)⁻¹ ^ (a + 1 + 2 * m0) := by
      have h_pow : (2 : ℚ)⁻¹ ^ (a + 2 * m0) = (2 : ℚ)⁻¹ ^ (a + 2 * m0) * (2 : ℚ)⁻¹ * 2 := by ring
      have h_pow2 : (2 : ℚ)⁻¹ ^ (a + 2 * m0) * (2 : ℚ)⁻¹ = (2 : ℚ)⁻¹ ^ (a + 2 * m0 + 1) := by
        rw [mul_comm]
        exact (pow_succ' (2 : ℚ)⁻¹ (a + 2 * m0)).symm
      rw [h_pow2] at h_pow
      have h_pow3 : a + 2 * m0 + 1 = a + 1 + 2 * m0 := by omega
      rw [h_pow3] at h_pow
      rw [h_pow]
      ring
    linarith

lemma sum_bound (a m0 : ℕ) (hm : m0 ≥ 1) :
  (Finset.range a).sum (fun i => (2 : ℚ)⁻¹ ^ (i + 1 + m0 * 2^(i + 1))) ≤ (2 : ℚ)⁻¹ ^ (2 * m0) := by
  have : (2 : ℚ)⁻¹ ^ (a + 2 * m0) ≥ 0 := by positivity
  have h1 := sum_bound_strong a m0 hm
  linarith

lemma Q_sum_bound (a m0 : ℕ) (hm : m0 ≥ 1) :
  (Finset.range a).sum (fun i => (2 : ℚ) ^ (m0 * 2^(a+1) - m0 * 2^(a-i) + i)) ≤ (2 : ℚ) ^ (m0 * 2^(a+1) - 2 * m0 + a) := by
  have h1 : (Finset.range a).sum (fun i => (2 : ℚ) ^ (m0 * 2^(a+1) - m0 * 2^(a-i) + i)) =
         (Finset.range a).sum (fun i => (2 : ℚ) ^ (m0 * 2^(a+1) + a) / (2 : ℚ) ^ (i + 1 + m0 * 2^(i+1))) := by
    rw [← Finset.sum_range_reflect _ a]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h_pow1 : 2^(i+1) ≤ 2^(a+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h_sub : m0 * 2^(a+1) + a - (i + 1 + m0 * 2^(i+1)) = m0 * 2^(a+1) - m0 * 2^(i+1) + (a - 1 - i) := by
      have : m0 * 2^(i+1) ≤ m0 * 2^(a+1) := Nat.mul_le_mul_left m0 h_pow1
      omega
    have h_sub2 : m0 * 2^(a+1) - m0 * 2^(a - (a - 1 - i)) + (a - 1 - i) = m0 * 2^(a+1) - m0 * 2^(i+1) + (a - 1 - i) := by
      have : a - (a - 1 - i) = i + 1 := by omega
      rw [this]
    rw [h_sub2, ← h_sub]
    have h_neq : (2 : ℚ) ≠ 0 := by norm_num
    have h_le : i + 1 + m0 * 2^(i+1) ≤ m0 * 2^(a+1) + a := by
      have : m0 * 2^(i+1) ≤ m0 * 2^(a+1) := Nat.mul_le_mul_left m0 h_pow1
      omega
    rw [pow_sub₀ _ h_neq h_le]
    exact div_eq_mul_inv (2 ^ (m0 * 2 ^ (a + 1) + a)) (2 ^ (i + 1 + m0 * 2 ^ (i + 1)))
  rw [h1]
  have h2 : (Finset.range a).sum (fun i => (2 : ℚ) ^ (m0 * 2^(a+1) + a) / (2 : ℚ) ^ (i + 1 + m0 * 2^(i+1))) =
            (2 : ℚ) ^ (m0 * 2^(a+1) + a) * (Finset.range a).sum (fun i => (2 : ℚ)⁻¹ ^ (i + 1 + m0 * 2^(i+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h_inv : (2 : ℚ)⁻¹ ^ (i + 1 + m0 * 2 ^ (i + 1)) = (2 ^ (i + 1 + m0 * 2 ^ (i + 1)))⁻¹ := by
      exact inv_pow (2 : ℚ) _
    rw [h_inv]
    exact div_eq_mul_inv (2 ^ (m0 * 2 ^ (a + 1) + a)) (2 ^ (i + 1 + m0 * 2 ^ (i + 1)))
  rw [h2]
  have h3 := sum_bound a m0 hm
  have h4 : (2 : ℚ) ^ (m0 * 2^(a+1) + a) * (Finset.range a).sum (fun i => (2 : ℚ)⁻¹ ^ (i + 1 + m0 * 2^(i+1))) ≤
            (2 : ℚ) ^ (m0 * 2^(a+1) + a) * (2 : ℚ)⁻¹ ^ (2 * m0) := by
    apply mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : (2 : ℚ) ^ (m0 * 2^(a+1) + a) * (2 : ℚ)⁻¹ ^ (2 * m0) = (2 : ℚ) ^ (m0 * 2^(a+1) - 2 * m0 + a) := by
    have h_inv : (2 : ℚ)⁻¹ ^ (2 * m0) = (2 ^ (2 * m0))⁻¹ := by
      exact inv_pow (2 : ℚ) _
    rw [h_inv]
    have h_neq : (2 : ℚ) ≠ 0 := by norm_num
    have h_le : 2 * m0 ≤ m0 * 2^(a+1) + a := by
      have hm_ineq : 2 * m0 ≤ m0 * 2^(a+1) := by
        have h_pow2 : 2^1 ≤ 2^(a+1) := Nat.pow_le_pow_right (by omega) (by omega)
        have h_mul := Nat.mul_le_mul_left m0 h_pow2
        have h2m : m0 * 2^1 = 2 * m0 := by ring
        rw [h2m] at h_mul
        exact h_mul
      omega
    have h_sub : m0 * 2^(a+1) + a - 2 * m0 = m0 * 2^(a+1) - 2 * m0 + a := by
      have : 2 * m0 ≤ m0 * 2^(a+1) := by
        have h_pow2 : 2^1 ≤ 2^(a+1) := Nat.pow_le_pow_right (by omega) (by omega)
        have h_mul := Nat.mul_le_mul_left m0 h_pow2
        have h2m : m0 * 2^1 = 2 * m0 := by ring
        rw [h2m] at h_mul
        exact h_mul
      omega
    have h_pow_sub := pow_sub₀ (2 : ℚ) h_neq h_le
    rw [← h_pow_sub, h_sub]
    
  linarith

lemma m0_odd (k a : ℕ) (hk : k > 0) (ha : a = padicValNat 2 k) : (k / 2^a) % 2 = 1 := by
  have hn_neq : k ≠ 0 := by omega
  have h1 : ¬ 2 ^ (a + 1) ∣ k := by
    rw [ha]
    exact pow_succ_padicValNat_not_dvd hn_neq
  have h2 : 2 ^ a ∣ k := by
    rw [ha]
    exact pow_padicValNat_dvd
  have h_dvd : (k / 2^a) % 2 = 0 ∨ (k / 2^a) % 2 = 1 := by omega
  cases h_dvd with
  | inl h0 =>
    have : 2 ∣ (k / 2^a) := Nat.dvd_of_mod_eq_zero h0
    rcases this with ⟨m, hm⟩
    have h_k : k = (k / 2^a) * 2^a := (Nat.div_mul_cancel h2).symm
    rw [hm] at h_k
    have h_k2 : k = 2^(a+1) * m := by
      calc k = 2 * m * 2^a := h_k
           _ = 2^(a+1) * m := by ring
    have : 2^(a+1) ∣ k := ⟨m, h_k2⟩
    contradiction
  | inr h1_eq => exact h1_eq


lemma Q_sign_a (k a : ℕ) (hk : k > 0) (ha : a = padicValNat 2 k) : (-1 : ℚ) ^ (k / 2^a - 1) = 1 := by
  have h1 := m0_odd k a hk ha
  have h2 : (k / 2^a - 1) % 2 = 0 := by omega
  exact neg_one_pow_even h2

lemma Q_term_a_bound (a m0 : ℕ) (hm : m0 ≥ 1) :
  (2 : ℚ) ^ (m0 * 2^(a+1) - 2 * m0 + a) ≤ (2 : ℚ) ^ (m0 * 2^(a+1) - m0 + a) := by
  have : m0 * 2^(a+1) - 2 * m0 + a ≤ m0 * 2^(a+1) - m0 + a := by
    have : 2 * m0 ≤ m0 * 2^(a+1) := by
      have h_pow2 : 2^1 ≤ 2^(a+1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h_mul := Nat.mul_le_mul_left m0 h_pow2
      have h2m : m0 * 2^1 = 2 * m0 := by ring
      rw [h2m] at h_mul
      exact h_mul
    omega
  exact pow_le_pow_right₀ (by norm_num) this

lemma c_val_pow (i m : ℕ) (hm : m ≥ 1) : c_val i ^ m * (2 : ℚ) ^ i = (2 : ℚ) ^ (m * 2^(i+1) - m + i) := by
  dsimp [c_val]
  rw [← pow_mul, ← pow_add]
  congr 1
  have h_le : 1 ≤ 2 ^ (i + 1) := by exact Nat.one_le_two_pow
  have h_mul : (2 ^ (i + 1) - 1) * m = m * 2 ^ (i + 1) - m := by
    rw [Nat.mul_comm, Nat.mul_sub_left_distrib]
    omega
  rw [h_mul]

lemma Q_term_eq (m0 a i : ℕ) (hm0 : m0 ≥ 1) (h_le : i ≤ a) :
  c_val i ^ (m0 * 2^(a-i)) * (2 : ℚ) ^ i = (2 : ℚ) ^ (m0 * 2^(a+1) - m0 * 2^(a-i) + i) := by
  have hm : m0 * 2^(a-i) ≥ 1 := by
    apply Nat.mul_pos hm0 (by positivity)
  rw [c_val_pow i (m0 * 2^(a-i)) hm]
  congr 1
  have h1 : m0 * 2 ^ (a - i) * 2 ^ (i + 1) = m0 * 2 ^ (a + 1) := by
    rw [mul_assoc, ← pow_add]
    have : a - i + (i + 1) = a + 1 := by omega
    rw [this]
  omega

lemma coeff_Q_sum_k_plus_one (k : ℕ) (hk : k > 0) :
  coeff k (Q_sum (k + 1)) = coeff k (Q_sum (padicValNat 2 k + 1)) := by
  rw [coeff_Q_sum, coeff_Q_sum]
  have h1 : padicValNat 2 k + 1 ≤ k + 1 := by
    have : 2^(padicValNat 2 k) ≤ k := by
      have h_dvd : 2^(padicValNat 2 k) ∣ k := pow_padicValNat_dvd
      exact Nat.le_of_dvd hk h_dvd
    have h2 : padicValNat 2 k ≤ 2^(padicValNat 2 k) := Nat.lt_pow_self (by omega) |>.le
    omega
  have h2 := Finset.sum_range_add_sum_Ico (fun i => coeff k (Q i)) h1
  rw [← h2]
  have h3 : (Finset.Ico (padicValNat 2 k + 1) (k + 1)).sum (fun i => coeff k (Q i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h_not_dvd : ¬ 2^i ∣ k := by
      intro hdvd
      have := le_padicValNat_of_dvd k i hk hdvd
      omega
    have h_mod : k % 2^i ≠ 0 := by
      intro hmod
      have hdvd : 2^i ∣ k := Nat.dvd_of_mod_eq_zero hmod
      contradiction
    dsimp [Q]
    rw [coeff_mk]
    simp [h_mod]
  rw [h3, add_zero]

lemma coeff_Q_sum_eval (k : ℕ) (hk : k > 0) :
  coeff k (Q_sum (padicValNat 2 k + 1)) =
  (Finset.range (padicValNat 2 k + 1)).sum (fun i =>
    let a := padicValNat 2 k
    let m0 := k / 2^a
    if i = a then (c_val a) ^ m0 * (2^a : ℚ)
    else -(c_val i) ^ (m0 * 2^(a-i)) * (2^i : ℚ)) := by
  rw [coeff_Q_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h_le : i ≤ padicValNat 2 k := by omega
  have h_dvd : 2^i ∣ k := by
    have : 2^i ∣ 2^(padicValNat 2 k) := Nat.pow_dvd_pow _ h_le
    have h2 : 2^(padicValNat 2 k) ∣ k := pow_padicValNat_dvd
    exact Nat.dvd_trans this h2
  have h_mod : k % 2^i = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  have h_pos : k > 0 := hk
  have h_eq : coeff k (Q i) = (-1 : ℚ) ^ (k / 2^i - 1) * c_val i ^ (k / 2^i) * (2^i : ℚ) := by
    dsimp [Q]
    rw [coeff_mk]
    simp [h_pos, h_mod]
  rw [h_eq]
  have ha : padicValNat 2 k = padicValNat 2 k := rfl
  by_cases hia : i = padicValNat 2 k
  · rw [if_pos hia]
    rw [hia]
    have hs := Q_sign_a k (padicValNat 2 k) hk ha
    rw [hs, one_mul]
  · rw [if_neg hia]
    have h_lt : i < padicValNat 2 k := by omega
    have hs := Q_sign_lt k (padicValNat 2 k) i hk ha h_lt
    rw [hs]
    have hm0_pow : k / 2^i = (k / 2^(padicValNat 2 k)) * 2^(padicValNat 2 k - i) := by
      have h_dvd2 : 2^(padicValNat 2 k) ∣ k := pow_padicValNat_dvd
      have h_k2 : k = (k / 2^(padicValNat 2 k)) * 2^(padicValNat 2 k) := by
        exact Eq.symm (Nat.div_mul_cancel h_dvd2)
      nth_rw 1 [h_k2]
      have h_pow2 : 2^(padicValNat 2 k) = 2^(padicValNat 2 k - i) * 2^i := by
        rw [← pow_add]
        congr 1
        omega
      rw [h_pow2, ← mul_assoc]
      have h2 : 2^i > 0 := by positivity
      exact Nat.mul_div_cancel _ h2
    rw [hm0_pow]
    ring

noncomputable def q_val (n : ℕ) : ℚ := coeff n (Q_sum (n + 1)) / 2

lemma q_val_nonneg (k : ℕ) (hk : k > 0) : q_val k ≥ 0 := by
  dsimp [q_val]
  have h_eval := coeff_Q_sum_eval k hk
  have h_k_plus_one := coeff_Q_sum_k_plus_one k hk
  rw [h_k_plus_one, h_eval]
  have a_eq : padicValNat 2 k = padicValNat 2 k := rfl
  have m0_eq : k / 2 ^ padicValNat 2 k = k / 2 ^ padicValNat 2 k := rfl
  let a := padicValNat 2 k
  let m0 := k / 2^a
  have h1 : (Finset.range (a + 1)).sum (fun i =>
    if i = a then (c_val a) ^ m0 * (2^a : ℚ)
    else -(c_val i) ^ (m0 * 2^(a-i)) * (2^i : ℚ)) =
    (c_val a) ^ m0 * (2^a : ℚ) - (Finset.range a).sum (fun i => (c_val i) ^ (m0 * 2^(a-i)) * (2^i : ℚ)) := by
    rw [Finset.sum_range_succ]
    have h_if : (if a = a then c_val a ^ m0 * (2 ^ a : ℚ) else -c_val a ^ (m0 * 2 ^ (a - a)) * (2 ^ a : ℚ)) = c_val a ^ m0 * (2 ^ a : ℚ) := by simp
    rw [h_if]
    have h_sum : (Finset.range a).sum (fun i => if i = a then c_val a ^ m0 * (2 ^ a : ℚ) else -c_val i ^ (m0 * 2 ^ (a - i)) * (2 ^ i : ℚ)) = (Finset.range a).sum (fun i => -((c_val i) ^ (m0 * 2 ^ (a - i)) * (2 ^ i : ℚ))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have h_neq : i ≠ a := by omega
      rw [if_neg h_neq]
      ring
    rw [h_sum, Finset.sum_neg_distrib, sub_eq_add_neg, add_comm]
  change ( _ : ℚ) / 2 ≥ 0
  have hm0 : m0 ≥ 1 := by
    have hdvd : 2^a ∣ k := pow_padicValNat_dvd
    have h_k : k = (k / 2^a) * 2^a := by exact Eq.symm (Nat.div_mul_cancel hdvd)
    by_contra h_contra
    push_neg at h_contra
    have h_zero : m0 = 0 := by clear_value m0; omega
    have h_k_zero : k = 0 := by
      calc k = m0 * 2^a := h_k
           _ = 0 * 2^a := by rw [h_zero]
           _ = 0 := by ring
    omega
  have h_bound := Q_sum_bound a m0 hm0
  have h_term := Q_term_a_bound a m0 hm0
  have h_a : (c_val a) ^ m0 * (2^a : ℚ) = (2 : ℚ) ^ (m0 * 2^(a+1) - m0 + a) := by
    have hp : (2^a : ℚ) = (2 : ℚ)^a := by push_cast; rfl
    rw [hp]
    exact c_val_pow a m0 hm0
  have h_i : (Finset.range a).sum (fun i => (c_val i) ^ (m0 * 2^(a-i)) * (2^i : ℚ)) =
             (Finset.range a).sum (fun i => (2 : ℚ) ^ (m0 * 2^(a+1) - m0 * 2^(a-i) + i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hp : (2^i : ℚ) = (2 : ℚ)^i := by push_cast; rfl
    rw [hp]
    exact Q_term_eq m0 a i hm0 (by omega)
  rw [h1, h_a, h_i]
  linarith

def conv (A B : ℕ → ℚ) (n : ℕ) : ℚ :=
  (Finset.range (n + 1)).sum fun k ↦ A k * B (n - k)

lemma coeff_X_mul_deriv (A : PowerSeries ℚ) (n : ℕ) :
  coeff n (X * derivative ℚ A) = (n : ℚ) * coeff n A := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_derivative]; ring

lemma coeff_mul_eq_conv (A B : PowerSeries ℚ) (n : ℕ) :
  coeff n (A * B) = conv (fun k => coeff k A) (fun k => coeff k B) n := by
  dsimp [conv]
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff i A * coeff j B) n

lemma coeff_mul_eq_sum (A B : PowerSeries ℚ) (n : ℕ) :
  coeff n (A * B) = (Finset.range (n + 1)).sum (fun k => coeff k A * coeff (n - k) B) := by
  rw [coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff i A * coeff j B) n

lemma F_ps_sq_eq (F Q : PowerSeries ℚ) (hF : X * derivative ℚ F = Q * F) :
  X * derivative ℚ (F * F) = (2 • Q) * (F * F) := by
  have h1 : derivative ℚ (F * F) = F * derivative ℚ F + F * derivative ℚ F := by
    rw [Derivation.leibniz]
    change F * derivative ℚ F + F * derivative ℚ F = _
    rfl
  have h2 : X * derivative ℚ (F * F) = F * (X * derivative ℚ F) + F * (X * derivative ℚ F) := by
    rw [h1, mul_add, mul_comm X]
    ring
  rw [h2, hF]
  have h3 : F * (Q * F) + F * (Q * F) = (2 : ℚ) • (Q * (F * F)) := by
    change F * (Q * F) + F * (Q * F) = (2 : ℚ) • (Q * (F * F))
    have h4 : F * (Q * F) = Q * (F * F) := by ring
    rw [h4]
    change Q * (F * F) + Q * (F * F) = (2 : ℚ) • (Q * (F * F))
    rw [two_smul]
  have h4 : (2 : ℚ) • (Q * (F * F)) = ((2 : ℚ) • Q) * (F * F) := (smul_mul_assoc (2 : ℚ) Q (F * F)).symm
  rw [h3, h4]
  exact rfl

lemma conv_recurrence (F_seq Q_seq : ℕ → ℚ) (hQ0 : Q_seq 0 = 0)
  (hF : ∀ n : ℕ, n > 0 → (n : ℚ) * F_seq n = (Finset.Ico 1 (n + 1)).sum (fun k => Q_seq k * F_seq (n - k))) (n : ℕ) (hn : n > 0) :
  (n : ℚ) * conv F_seq F_seq n = (Finset.Ico 1 (n + 1)).sum (fun k => (2 * Q_seq k) * conv F_seq F_seq (n - k)) := by
  let F := mk F_seq
  let Q := mk Q_seq
  have h_eq : X * derivative ℚ F = Q * F := by
    ext m
    rw [coeff_X_mul_deriv, coeff_mul_eq_sum]
    by_cases hm : m = 0
    · simp [hm]
      have hc0 : constantCoeff Q = 0 := hQ0
      left
      exact hc0
    · have hm_pos : m > 0 := by omega
      have hFm := hF m hm_pos
      have h_sum : (Finset.range (m + 1)).sum (fun k => coeff k Q * coeff (m - k) F) =
                   (Finset.Ico 1 (m + 1)).sum (fun k => Q_seq k * F_seq (m - k)) := by
        have h_split : (Finset.range (m + 1)).sum (fun k => coeff k Q * coeff (m - k) F) =
                       coeff 0 Q * coeff (m - 0) F + (Finset.Ico 1 (m + 1)).sum (fun k => coeff k Q * coeff (m - k) F) := by
          have h_range : Finset.range (m + 1) = insert 0 (Finset.Ico 1 (m + 1)) := by
            ext x
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
            omega
          rw [h_range, Finset.sum_insert]
          simp
        rw [h_split]
        have hc0 : coeff 0 Q = 0 := by change coeff 0 (mk Q_seq) = 0; rw [coeff_mk]; exact hQ0
        rw [hc0, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro k hk
        have h1 : coeff k Q = Q_seq k := coeff_mk _ _
        have h2 : coeff (m - k) F = F_seq (m - k) := coeff_mk _ _
        simp only [h1, h2]
      have hc : (m : ℚ) * coeff m F = (m : ℚ) * F_seq m := by
        have h3 : coeff m F = F_seq m := coeff_mk _ _
        rw [h3]
      rw [hc, h_sum]
      exact hFm
  have h2 := F_ps_sq_eq F Q h_eq
  have h_coeff : coeff n (X * derivative ℚ (F * F)) = coeff n ((2 • Q) * (F * F)) := by rw [h2]
  rw [coeff_X_mul_deriv] at h_coeff
  have h_RHS_exp : coeff n ((2 • Q) * (F * F)) = (Finset.range (n + 1)).sum (fun k => coeff k (2 • Q) * coeff (n - k) (F * F)) := coeff_mul_eq_sum (2 • Q) (F * F) n
  rw [h_RHS_exp] at h_coeff
  have h_LHS : coeff n (F * F) = conv F_seq F_seq n := by
    rw [coeff_mul_eq_conv]
    apply Finset.sum_congr rfl
    intro k hk
    have h1 : coeff k F = F_seq k := coeff_mk _ _
    have h2 : coeff (n - k) F = F_seq (n - k) := coeff_mk _ _
    simp only [h1, h2]
  have hc : (n : ℚ) * coeff n (F * F) = (n : ℚ) * conv F_seq F_seq n := by rw [h_LHS]
  have h_LHS_2 : (n : ℚ) * coeff n (F * F) = (n : ℚ) * conv F_seq F_seq n := by rw [h_LHS]
  rw [h_LHS_2] at h_coeff
  have h_RHS : (Finset.range (n + 1)).sum (fun k => coeff k (2 • Q) * coeff (n - k) (F * F)) =
               (Finset.Ico 1 (n + 1)).sum (fun k => (2 * Q_seq k) * conv F_seq F_seq (n - k)) := by
    have h_split : (Finset.range (n + 1)).sum (fun k => coeff k (2 • Q) * coeff (n - k) (F * F)) =
                   coeff 0 (2 • Q) * coeff (n - 0) (F * F) + (Finset.Ico 1 (n + 1)).sum (fun k => coeff k (2 • Q) * coeff (n - k) (F * F)) := by
      have h_range : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
        omega
      rw [h_range, Finset.sum_insert]
      simp
    rw [h_split]
    have hc0 : coeff 0 (2 • Q) = 0 := by
      change (2 : ℚ) * coeff 0 Q = 0
      have h0 : coeff 0 Q = 0 := by
        change coeff 0 (mk Q_seq) = 0
        rw [coeff_mk, hQ0]
      rw [h0, mul_zero]
    rw [hc0, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    have hc1 : coeff k (2 • Q) = 2 * Q_seq k := by
      change (2 : ℚ) * coeff k Q = _
      have h1 : coeff k Q = Q_seq k := coeff_mk _ _
      rw [h1]
    have hc2 : coeff (n - k) (F * F) = conv F_seq F_seq (n - k) := by
      rw [coeff_mul_eq_conv]
      apply Finset.sum_congr rfl
      intro j hj
      have h1 : coeff j F = F_seq j := coeff_mk _ _
      have h2 : coeff (n - k - j) F = F_seq (n - k - j) := coeff_mk _ _
      simp only [h1, h2]
    rw [hc1, hc2]
  rw [h_RHS] at h_coeff
  exact h_coeff

noncomputable def F_seq : ℕ → ℚ :=
  WellFounded.fix (measure (fun n : ℕ => n)).wf fun n IH ↦
    if n = 0 then 1
    else
      (Finset.Ico 1 (n + 1)).sum (fun k =>
        if h_k : k ∈ Finset.Ico 1 (n + 1) then
          have h_lt : n - k < n := by
            rw [Finset.mem_Ico] at h_k
            omega
          IH (n - k) h_lt * q_val k
        else 0
      ) / (n : ℚ)

lemma F_seq_eq_simp (n : ℕ) : F_seq n = if n = 0 then 1 else (Finset.Ico 1 (n + 1)).sum (fun k => F_seq (n - k) * q_val k) / (n : ℚ) := by
  have h_eq : F_seq n = if n = 0 then 1 else
    (Finset.Ico 1 (n + 1)).sum (fun k =>
      if h_k : k ∈ Finset.Ico 1 (n + 1) then
        F_seq (n - k) * q_val k
      else 0
    ) / (n : ℚ) := by
    rw [F_seq, WellFounded.fix_eq]
  rw [h_eq]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [dif_pos hk]

lemma F_seq_nonneg (h_q_nonneg : ∀ k > 0, q_val k ≥ 0) : ∀ n, F_seq n ≥ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [F_seq_eq_simp]
    by_cases hn : n = 0
    · rw [if_pos hn]; norm_num
    · rw [if_neg hn]
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro k hk
        rw [Finset.mem_Ico] at hk
        have h_lt : n - k < n := by omega
        have h_F := ih _ h_lt
        have h_q := h_q_nonneg k hk.1
        positivity
      · positivity


noncomputable def g_arith (F : ℕ → ℚ) : ArithmeticFunction ℚ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod fun _ e => F e, by simp⟩

lemma g_arith_nonneg (F : ℕ → ℚ) (hF : ∀ k, F k ≥ 0) (n : ℕ) : g_arith F n ≥ 0 := by
  dsimp [g_arith]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    apply Finset.prod_nonneg
    intro p hp
    exact hF _

lemma g_isMultiplicative (F : ℕ → ℚ) (hF0 : F 0 = 1) : (g_arith F).IsMultiplicative := by
  constructor
  · simp [g_arith, hF0]
  · intro m n hcoprime
    by_cases hm : m = 0; · simp [hm]
    by_cases hn : n = 0; · simp [hn]
    have h_mn : m * n ≠ 0 := mul_ne_zero hm hn
    dsimp [g_arith]
    rw [if_neg hm, if_neg hn, if_neg h_mn]
    rw [Nat.factorization_mul hm hn]
    have h_disj : Disjoint m.factorization.support n.factorization.support := by
      rw [Finset.disjoint_left]
      intro p hp hp2
      have hp_ne : m.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
      have hp2_ne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp2
      have h1 : p ∣ m := Nat.dvd_of_factorization_pos hp_ne
      have h2 : p ∣ n := Nat.dvd_of_factorization_pos hp2_ne
      have h3 : p ∣ m.gcd n := Nat.dvd_gcd h1 h2
      rw [hcoprime] at h3
      have hp1 : p = 1 := Nat.eq_one_of_dvd_one h3
      subst hp1
      have : m.factorization 1 = 0 := by simp
      contradiction
    exact Finsupp.prod_add_index_of_disjoint h_disj (fun _ e => F e)

lemma g_prime_power (F : ℕ → ℚ) (hF0 : F 0 = 1) (p k : ℕ) (hp : p.Prime) :
  g_arith F (p ^ k) = F k := by
  dsimp [g_arith]
  by_cases hk : k = 0
  · simp [hk, hF0]
  have h1 : p ^ k ≠ 0 := by
    have : p > 0 := Nat.Prime.pos hp
    positivity
  rw [if_neg h1]
  have h2 : (p ^ k).factorization = Finsupp.single p k := Nat.Prime.factorization_pow hp
  rw [h2]
  exact Finsupp.prod_single_index hF0
lemma g_recurrence (g : ArithmeticFunction ℚ) (hg1 : g 1 = 1) (A : ℕ → ℚ) (hg_mul : ∀ n > 0, (g * g) n = A n) :
  ∀ n > 1, g n = (A n - Finset.sum (divisors n) (fun d => if d > 1 ∧ d < n then g d * g (n / d) else 0)) / 2 := by
  intro n hn
  have h_A : A n = (g * g) n := (hg_mul n (by omega)).symm
  rw [h_A]
  have h_mul : (g * g) n = Finset.sum (divisors n) (fun d => g d * g (n / d)) := by
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun a b => g a * g b)
  rw [h_mul]
  have h1 : 1 ∈ divisors n := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hn_mem : n ∈ divisors n := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have h_neq : 1 ≠ n := by omega
  have h_sum_split : Finset.sum (divisors n) (fun d => g d * g (n / d)) =
    g 1 * g (n / 1) + g n * g (n / n) +
    Finset.sum ((divisors n).erase 1 |>.erase n) (fun d => g d * g (n / d)) := by
    have s1 : Finset.sum (divisors n) (fun d => g d * g (n / d)) =
      g 1 * g (n / 1) + Finset.sum ((divisors n).erase 1) (fun d => g d * g (n / d)) := (Finset.add_sum_erase _ _ h1).symm
    rw [s1]
    have hn_mem2 : n ∈ (divisors n).erase 1 := Finset.mem_erase_of_ne_of_mem h_neq.symm hn_mem
    have s2 : Finset.sum ((divisors n).erase 1) (fun d => g d * g (n / d)) =
      g n * g (n / n) + Finset.sum (((divisors n).erase 1).erase n) (fun d => g d * g (n / d)) := (Finset.add_sum_erase _ _ hn_mem2).symm
    rw [s2, add_assoc]
  rw [h_sum_split]
  have h_div1 : n / 1 = n := Nat.div_one n
  have h_divn : n / n = 1 := Nat.div_self (by omega)
  rw [h_div1, h_divn, hg1]
  have h_if : Finset.sum (divisors n) (fun d => if d > 1 ∧ d < n then g d * g (n / d) else 0) =
              Finset.sum ((divisors n).erase 1 |>.erase n) (fun d => g d * g (n / d)) := by
    have h_eq : Finset.sum (divisors n) (fun d => if d > 1 ∧ d < n then g d * g (n / d) else 0) =
                Finset.sum (Finset.filter (fun d => d > 1 ∧ d < n) (divisors n)) (fun d => g d * g (n / d)) := by
      exact (Finset.sum_filter _ _).symm
    rw [h_eq]
    apply Finset.sum_congr _
    · intro d _
      rfl
    · ext d
      simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdvd, hpos⟩, hgt1, hltn⟩
        have h_neq1 : d ≠ 1 := by omega
        have h_neqn : d ≠ n := by omega
        exact ⟨h_neqn, h_neq1, hdvd, hpos⟩
      · rintro ⟨h_neqn, h_neq1, hdvd, hpos⟩
        have hgt1 : d > 1 := by
          have : d ≠ 0 := by rintro rfl; omega
          omega
        have hltn : d < n := by
          have : d ≤ n := Nat.le_of_dvd (by omega) hdvd
          omega
        exact ⟨⟨hdvd, hpos⟩, hgt1, hltn⟩
  rw [h_if]
  ring

lemma seq_unique (X Y C : ℕ → ℚ) (hX0 : X 0 = Y 0)
  (hX : ∀ n : ℕ, n > 0 → (n : ℚ) * X n = (Finset.Ico 1 (n + 1)).sum (fun k => X (n - k) * C k))
  (hY : ∀ n : ℕ, n > 0 → (n : ℚ) * Y n = (Finset.Ico 1 (n + 1)).sum (fun k => Y (n - k) * C k)) :
  ∀ n, X n = Y n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn, hX0]
    · have h_pos : n > 0 := by omega
      have hXn := hX n h_pos
      have hYn := hY n h_pos
      have h_sum : (Finset.Ico 1 (n + 1)).sum (fun k => X (n - k) * C k) =
                   (Finset.Ico 1 (n + 1)).sum (fun k => Y (n - k) * C k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Ico] at hk
        have h_lt : n - k < n := by omega
        rw [ih (n - k) h_lt]
      rw [h_sum] at hXn
      have h_eq : (n : ℚ) * X n = (n : ℚ) * Y n := by
        rw [hXn, hYn]
      have hn_neq : (n : ℚ) ≠ 0 := by exact Nat.cast_ne_zero.mpr (by omega)
      exact mul_left_cancel₀ hn_neq h_eq




lemma A046644_eq_g_arith (n : ℕ) : A046644 n = g_arith A_seq n := by
  dsimp [A046644, g_arith, A_seq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    apply Finsupp.prod_congr
    intro p hp
    rw [A005187_eq]


theorem coeff_P (i n : ℕ) : coeff n (P i) = if n = 0 then 1 else if n = 2^i then c_val i else 0 := by
  dsimp [P]
  rw [map_add, coeff_one, coeff_C_mul, coeff_X_pow]
  have h_pos : 2^i > 0 := by positivity
  by_cases hn0 : n = 0
  · simp [hn0]
    have : ¬ 0 = 2^i := by omega
    simp [this]
  · by_cases hn_eq : n = 2^i
    · simp [hn_eq]
    · simp [hn_eq]

theorem coeff_Q (i n : ℕ) : coeff n (Q i) =
  if n > 0 ∧ n % 2^i = 0 then
    let m := n / 2^i
    (-1 : ℚ) ^ (m - 1) * (c_val i) ^ m * (2^i : ℕ)
  else 0 := by
  dsimp [Q]
  rw [coeff_mk]

theorem P_deriv_eq (i : ℕ) : X * derivative ℚ (P i) = (Q i) * (P i) := by
  ext n
  rw [coeff_X_mul_deriv, coeff_mul_eq_conv]
  dsimp [conv]
  have h_pos : 0 < 2^i := by positivity
  by_cases hn : n < 2^i
  · have h_P_0 : coeff n (P i) = if n = 0 then 1 else 0 := by
      rw [coeff_P]
      have : n ≠ 2^i := by omega
      simp [this]
    rw [h_P_0]
    have h1 : (Finset.range (n + 1)).sum (fun (k : ℕ) ↦ coeff k (Q i) * coeff (n - k) (P i)) = coeff n (Q i) := by
      rw [Finset.sum_eq_single n]
      · simp [coeff_P]
      · intro k hk h_neq
        have hk_lt : k < n + 1 := Finset.mem_range.mp hk
        have : n - k ≠ 0 := by omega
        have h2 : n - k ≠ 2^i := by omega
        simp [coeff_P, this, h2]
      · intro hn_range
        exfalso
        apply hn_range
        simp
    rw [h1]
    by_cases hn0 : n = 0
    · simp [hn0, coeff_Q]
    · have h_mod : ¬ (n > 0 ∧ n % 2^i = 0) := by
        intro h_and
        have : n % 2^i = n := Nat.mod_eq_of_lt hn
        omega
      simp [hn0, coeff_Q, h_mod]
  · by_cases hn_eq : n = 2^i
    · rw [hn_eq]
      have h1 : (Finset.range (2^i + 1)).sum (fun k ↦ coeff k (Q i) * coeff (2^i - k) (P i)) =
                coeff (2^i) (Q i) * coeff 0 (P i) + coeff 0 (Q i) * coeff (2^i) (P i) := by
        have h_sum : (Finset.range (2^i + 1)).sum (fun k ↦ coeff k (Q i) * coeff (2^i - k) (P i)) =
               (fun k ↦ coeff k (Q i) * coeff (2^i - k) (P i)) (2^i) + (fun k ↦ coeff k (Q i) * coeff (2^i - k) (P i)) 0 := by
          apply Finset.sum_eq_add_of_mem (2^i) 0
          · simp
          · simp
          · omega
          · rintro k hk ⟨h1, h2⟩
            have hk_lt : k < 2^i + 1 := Finset.mem_range.mp hk
            have : 2^i - k ≠ 0 := by omega
            have h_2i : 2^i - k ≠ 2^i := by omega
            simp [coeff_P, this, h_2i]
        rw [h_sum]
        change coeff (2^i) (Q i) * coeff (2^i - 2^i) (P i) + coeff 0 (Q i) * coeff (2^i - 0) (P i) = _
        have hsub1 : 2^i - 2^i = 0 := by omega
        have hsub2 : 2^i - 0 = 2^i := by omega
        rw [hsub1, hsub2]
      rw [h1]
      have hP0 : coeff 0 (P i) = 1 := by simp [coeff_P]
      have hP2 : coeff (2^i) (P i) = c_val i := by simp [coeff_P]
      have hQ0 : coeff 0 (Q i) = 0 := by simp [coeff_Q]
      have hQ2 : coeff (2^i) (Q i) = c_val i * 2^i := by
        rw [coeff_Q]
        have hmod : 2^i % 2^i = 0 := Nat.mod_self _
        have hdiv : 2^i / 2^i = 1 := Nat.div_self h_pos
        simp [h_pos, hmod, hdiv]
      simp [hP0, hP2, hQ0, hQ2]
      ring
    · have h_gt : n > 2^i := by omega
      have hn0 : n ≠ 0 := by omega
      have hn_eq2 : n ≠ 2^i := by omega
      have h_P_0 : coeff n (P i) = 0 := by
        rw [coeff_P]
        simp [hn0, hn_eq2]
      rw [h_P_0]
      simp
      have h1 : (Finset.range (n + 1)).sum (fun k ↦ coeff k (Q i) * coeff (n - k) (P i)) =
                coeff n (Q i) * coeff 0 (P i) + coeff (n - 2^i) (Q i) * coeff (2^i) (P i) := by
        have h_sum : (Finset.range (n + 1)).sum (fun k ↦ coeff k (Q i) * coeff (n - k) (P i)) =
               (fun k ↦ coeff k (Q i) * coeff (n - k) (P i)) n + (fun k ↦ coeff k (Q i) * coeff (n - k) (P i)) (n - 2^i) := by
          apply Finset.sum_eq_add_of_mem n (n - 2^i)
          · simp
          · simp [Finset.mem_range]
          · omega
          · rintro k hk ⟨h1, h2⟩
            have hk_lt : k < n + 1 := Finset.mem_range.mp hk
            have : n - k ≠ 0 := by omega
            have h_2i : n - k ≠ 2^i := by omega
            simp [coeff_P, this, h_2i]
        rw [h_sum]
        change coeff n (Q i) * coeff (n - n) (P i) + coeff (n - 2^i) (Q i) * coeff (n - (n - 2^i)) (P i) = _
        have hsub1 : n - n = 0 := by omega
        have hsub2 : n - (n - 2^i) = 2^i := by omega
        rw [hsub1, hsub2]
      rw [h1]
      have hP0 : coeff 0 (P i) = 1 := by simp [coeff_P]
      have hP2 : coeff (2^i) (P i) = c_val i := by simp [coeff_P]
      rw [hP0, hP2]
      by_cases h_mod : n % 2^i = 0
      · have hdvd : 2^i ∣ n := Nat.dvd_of_mod_eq_zero h_mod
        rcases hdvd with ⟨m, hm⟩
        have hm2 : n = m * 2^i := by rw [hm, mul_comm]
        have hm_gt : m > 1 := by
          cases m
          · simp [hm2] at h_gt
          · case succ m' =>
            by_cases hm1 : m' = 0
            · simp [hm1] at hm2; omega
            · omega
        have hsub : n - 2^i = (m - 1) * 2^i := by
          rw [hm2]
          have h_distrib := Nat.mul_sub_right_distrib m 1 (2^i)
          rw [Nat.one_mul] at h_distrib
          exact h_distrib.symm
        have h_mod2 : (n - 2^i) % 2^i = 0 := by
          rw [hsub]
          simp
        have h_div1 : n / 2^i = m := by
          rw [hm2]
          exact Nat.mul_div_cancel m h_pos
        have h_div2 : (n - 2^i) / 2^i = m - 1 := by
          rw [hsub]
          exact Nat.mul_div_cancel (m - 1) h_pos
        have hn_sub_pos : n - 2^i > 0 := by omega
        have hn_pos : n > 0 := by omega
        rw [coeff_Q, coeff_Q]
        simp [hn_pos, h_mod, hn_sub_pos, h_mod2, h_div1, h_div2]
        have h_pow : (-1 : ℚ) ^ (m - 1) = - (-1 : ℚ) ^ (m - 2) := by
          have : m - 1 = (m - 2) + 1 := by omega
          rw [this, pow_add]
          simp
        rw [h_pow]
        have h_c_pow : c_val i ^ m = c_val i ^ (m - 1) * c_val i := by
          have : m = (m - 1) + 1 := by omega
          nth_rw 1 [this]
          rw [pow_add]
          simp
        rw [h_c_pow]
        have : m - 1 - 1 = m - 2 := by omega
        rw [this]
        ring
      · rw [coeff_Q, coeff_Q]
        simp [h_mod]
        have h_mod2 : ¬ (n - 2^i) % 2^i = 0 := by
          intro contra
          have hdvd : 2^i ∣ n - 2^i := Nat.dvd_of_mod_eq_zero contra
          rcases hdvd with ⟨k, hk⟩
          have h_n_eq : n = (k + 1) * 2^i := by
            have hx : n = (n - 2^i) + 2^i := by omega
            rw [hx, hk, Nat.mul_comm (2^i) k]
            have h_distrib := Nat.add_mul k 1 (2^i)
            rw [Nat.one_mul] at h_distrib
            exact h_distrib.symm
          have hn_mod_zero : n % 2^i = 0 := by
            rw [h_n_eq]
            simp
          exact h_mod hn_mod_zero
        simp [h_mod2]

theorem P_prod_deriv (m : ℕ) : X * derivative ℚ (P_prod m) = (Q_sum m) * (P_prod m) := by
  induction m with
  | zero =>
    simp [P_prod, Q_sum]
  | succ m ih =>
    dsimp [P_prod, Q_sum]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 : X * (P_prod m * derivative ℚ (P m) + P m * derivative ℚ (P_prod m)) =
              P_prod m * (X * derivative ℚ (P m)) + P m * (X * derivative ℚ (P_prod m)) := by ring
    rw [h1, P_deriv_eq, ih]
    ring


lemma coeff_Q_large (k i : ℕ) (hk : k > 0) (hi : i ≥ k + 1) : coeff k (Q i) = 0 := by
  dsimp [Q]
  rw [coeff_mk]
  have h_mod : ¬ (k % 2^i = 0) := by
    have h_lt : k < 2^i := by
      have h1 : 2^(k+1) ≤ 2^i := Nat.pow_le_pow_right (by omega) hi
      have h2 : k < 2^k := Nat.lt_pow_self (by omega)
      have h3 : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
      calc k < 2^k := h2
           _ ≤ 2^(k+1) := h3
           _ ≤ 2^i := h1
    intro contra
    have h_eq : k = 0 := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero contra) h_lt
    omega
  simp [h_mod]

lemma Q_sum_succ (m : ℕ) : Q_sum (m + 1) = Q_sum m + Q m := rfl

lemma coeff_Q_sum_large (m k : ℕ) (hk : k > 0) (hm : m ≥ k + 1) :
  coeff k (Q_sum m) = coeff k (Q_sum (k + 1)) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h_eq : m = k
    · subst h_eq
      rfl
    · have hm2 : m ≥ k + 1 := by omega
      have h1 := ih hm2
      rw [Q_sum_succ, LinearMap.map_add, h1]
      have h2 : coeff k (Q m) = 0 := coeff_Q_large k m hk hm2
      rw [h2, add_zero]

lemma coeff_Q_zero (i : ℕ) : coeff 0 (Q i) = 0 := by
  dsimp [Q]
  rw [coeff_mk]
  simp

lemma coeff_Q_sum_zero (m : ℕ) : coeff 0 (Q_sum m) = 0 := by
  induction m with
  | zero => simp [Q_sum]
  | succ m ih =>
    rw [Q_sum_succ, LinearMap.map_add, ih, coeff_Q_zero, add_zero]

lemma n_lt_pow (n : ℕ) : n < 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    omega

lemma A_seq_recurrence (n : ℕ) (hn : n > 0) :
  (n : ℚ) * A_seq n = (Finset.Ico 1 (n + 1)).sum (fun k => (2 * q_val k) * A_seq (n - k)) := by
  have h_deriv := P_prod_deriv (n + 1)
  have h_coeff : coeff n (X * derivative ℚ (P_prod (n + 1))) = coeff n (Q_sum (n + 1) * P_prod (n + 1)) := by
    rw [h_deriv]
  rw [coeff_X_mul_deriv] at h_coeff
  have h_An : coeff n (P_prod (n + 1)) = A_seq n := by
    apply coeff_P_prod
    have h1 : n < n + 1 := by omega
    have h2 : n + 1 < 2^(n + 1) := Nat.lt_pow_self (by omega)
    omega
  rw [h_An] at h_coeff
  have h_sum_lem : coeff n (Q_sum (n + 1) * P_prod (n + 1)) = (Finset.range (n + 1)).sum (fun k => coeff k (Q_sum (n + 1)) * coeff (n - k) (P_prod (n + 1))) := by
    exact coeff_mul_eq_sum (Q_sum (n + 1)) (P_prod (n + 1)) n
  rw [h_sum_lem] at h_coeff
  have h_sum : (Finset.range (n + 1)).sum (fun k => coeff k (Q_sum (n + 1)) * coeff (n - k) (P_prod (n + 1))) =
               (Finset.Ico 1 (n + 1)).sum (fun k => (2 * q_val k) * A_seq (n - k)) := by
    have h1 : (Finset.range (n + 1)).sum (fun k => coeff k (Q_sum (n + 1)) * coeff (n - k) (P_prod (n + 1))) =
              coeff 0 (Q_sum (n + 1)) * coeff (n - 0) (P_prod (n + 1)) +
              (Finset.Ico 1 (n + 1)).sum (fun k => coeff k (Q_sum (n + 1)) * coeff (n - k) (P_prod (n + 1))) := by
      have h_range : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
        omega
      rw [h_range, Finset.sum_insert]
      simp
    rw [coeff_Q_sum_zero, zero_mul, zero_add] at h1
    rw [h1]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk_pos : k > 0 := hk.1
    have hm : n + 1 ≥ k + 1 := hk.2
    have hQ := coeff_Q_sum_large (n + 1) k hk_pos hm
    have hq_val : q_val k = coeff k (Q_sum (k + 1)) / 2 := rfl
    have hQ2 : coeff k (Q_sum (n + 1)) = 2 * q_val k := by
      rw [hQ, hq_val]
      ring
    rw [hQ2]
    have hn_k_lt : n - k < 2^(n + 1) := by
      have hlt : n < 2^(n + 1) := n_lt_pow n
      omega
    have hP := coeff_P_prod (n + 1) (n - k) hn_k_lt
    rw [hP]
  rw [h_sum] at h_coeff
  exact h_coeff

lemma F_seq_conv_eq_A_seq (n : ℕ) : conv F_seq F_seq n = A_seq n := by
  have hF0 : F_seq 0 = 1 := by rw [F_seq_eq_simp, if_pos rfl]
  have hA0 : A_seq 0 = 1 := by simp [A_seq]
  have h_eq0 : conv F_seq F_seq 0 = A_seq 0 := by
    dsimp [conv]
    simp [hF0, hA0]
  have h_conv := conv_recurrence F_seq q_val (by rw [q_val]; simp [coeff_Q_sum_zero])
  have hF_rec : ∀ n : ℕ, n > 0 → (n : ℚ) * F_seq n = (Finset.Ico 1 (n + 1)).sum (fun k => q_val k * F_seq (n - k)) := by
    intro m hm
    rw [F_seq_eq_simp, if_neg (by omega)]
    have h_div : (Finset.Ico 1 (m + 1)).sum (fun k => F_seq (m - k) * q_val k) / (m : ℚ) * (m : ℚ) =
                 (Finset.Ico 1 (m + 1)).sum (fun k => F_seq (m - k) * q_val k) := by
      exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (by omega))
    have h_mul : (m : ℚ) * ((Finset.Ico 1 (m + 1)).sum (fun k => F_seq (m - k) * q_val k) / (m : ℚ)) =
                 (Finset.Ico 1 (m + 1)).sum (fun k => F_seq (m - k) * q_val k) := by
      rw [mul_comm, h_div]
    rw [h_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have h_conv2 : ∀ n : ℕ, n > 0 → (n : ℚ) * conv F_seq F_seq n = (Finset.Ico 1 (n + 1)).sum (fun k => conv F_seq F_seq (n - k) * (2 * q_val k)) := by
    intro m hm
    have h1 := h_conv hF_rec m hm
    rw [h1]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hA_rec : ∀ n : ℕ, n > 0 → (n : ℚ) * A_seq n = (Finset.Ico 1 (n + 1)).sum (fun k => A_seq (n - k) * (2 * q_val k)) := by
    intro m hm
    rw [A_seq_recurrence m hm]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  exact seq_unique (conv F_seq F_seq) A_seq (fun k => 2 * q_val k) h_eq0 h_conv2 hA_rec n

lemma mul_eval_prime_power (F : ℕ → ℚ) (hF0 : F 0 = 1) (p k : ℕ) (hp : p.Prime) :
  (g_arith F * g_arith F) (p ^ k) = conv F F k := by
  have h_mul : (g_arith F * g_arith F) (p ^ k) = Finset.sum (divisors (p ^ k)) (fun d => g_arith F d * g_arith F (p ^ k / d)) := by
    rw [ArithmeticFunction.mul_apply]
    exact Nat.sum_divisorsAntidiagonal (fun a b => g_arith F a * g_arith F b)
  rw [h_mul]
  have h_divs : divisors (p ^ k) = (Finset.range (k + 1)).map ⟨fun i => p ^ i, Nat.pow_right_injective hp.two_le⟩ := by
    exact Nat.divisors_prime_pow hp k
  rw [h_divs]
  rw [Finset.sum_map]
  dsimp
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h_div : (p ^ k) / (p ^ i) = p ^ (k - i) := by
    have h_le : i ≤ k := by omega
    exact Nat.pow_div h_le (Nat.Prime.pos hp)
  rw [h_div]
  have h_gi := g_prime_power F hF0 p i hp
  have h_gki := g_prime_power F hF0 p (k - i) hp
  rw [h_gi, h_gki]


lemma A317940_f_eq_g (n : ℕ) : A317940_f n = g_arith F_seq n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · rw [hn0]
      have h1 : A317940_f 0 = 0 := by
        rw [A317940_f, WellFounded.fix_eq]
        simp
      have h2 : g_arith F_seq 0 = 0 := by
        dsimp [g_arith]
      rw [h1, h2]
    by_cases hn1 : n = 1
    · rw [hn1]
      have h1 : A317940_f 1 = 1 := by
        rw [A317940_f, WellFounded.fix_eq]
        simp
      have h2 : g_arith F_seq 1 = 1 := by
        dsimp [g_arith]
        simp
      rw [h1, h2]
    have hn_gt1 : n > 1 := by omega
    have h_g_rec := g_recurrence (g_arith F_seq) (by dsimp [g_arith]; simp) A046644
    have hA : ∀ m > 0, (g_arith F_seq * g_arith F_seq) m = A046644 m := by
      intro m hm
      have hF0 : F_seq 0 = 1 := by rw [F_seq_eq_simp, if_pos rfl]
      have h_mult := g_isMultiplicative F_seq hF0
      have h_mult2 : (g_arith F_seq * g_arith F_seq).IsMultiplicative := ArithmeticFunction.IsMultiplicative.mul h_mult h_mult
      have hA0 : A_seq 0 = 1 := by simp [A_seq, s2_zero]
      have h_A_mult : (g_arith A_seq).IsMultiplicative := g_isMultiplicative A_seq hA0
      have h_eq : g_arith F_seq * g_arith F_seq = g_arith A_seq := by
        rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers (g_arith F_seq * g_arith F_seq) h_mult2 (g_arith A_seq) h_A_mult]
        intro p i hp
        rw [mul_eval_prime_power F_seq hF0 p i hp]
        have hAi := g_prime_power A_seq hA0 p i hp
        rw [hAi]
        exact F_seq_conv_eq_A_seq i
      rw [h_eq]
      exact (A046644_eq_g_arith m).symm
    
    have h_g_rec2 := h_g_rec hA n hn_gt1
    rw [h_g_rec2]
    have h_f_rec : A317940_f n = (A046644 n - Finset.sum (divisors n) (fun d => if h : d > 1 ∧ d < n then A317940_f d * A317940_f (n / d) else 0)) / 2 := by
      rw [A317940_f, WellFounded.fix_eq]
      by_cases hn0_2 : n = 0; contradiction
      by_cases hn1_2 : n = 1; contradiction
      rw [if_neg hn0_2, if_neg hn1_2]
    rw [h_f_rec]
    congr 2
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hd1 : d > 1 ∧ d < n
    · rw [dif_pos hd1, if_pos hd1]
      have h1 : d < n := hd1.2
      have hd_pos : d > 0 := by omega
      have h2 : n / d < n := Nat.div_lt_self (by omega) hd1.1
      rw [ih d h1, ih (n / d) h2]
    · rw [dif_neg hd1, if_neg hd1]


theorem A317940_f_nonnegative (n : ℕ) (h : n > 0) : A317940_f n ≥ 0 := by
  rw [A317940_f_eq_g n]
  have hF_nonneg : ∀ k, F_seq k ≥ 0 := F_seq_nonneg q_val_nonneg
  exact g_arith_nonneg F_seq hF_nonneg n

theorem A317940_f_nonnegative.disproof : ¬ (type_of% @A317940_f_nonnegative) := sorry


