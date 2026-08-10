import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

lemma S1_eq_choose (n : ℕ) (hn : n ≥ 1) :
    Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k) = (3 * n).choose n := by
  have h_rew : ∀ k ∈ range (2 * n + 1), (n + k - 1).choose k = (k + (n - 1)).choose (n - 1) := by
    intro k _
    have h_eq1 : n + k - 1 = k + (n - 1) := by omega
    rw [h_eq1]
    have h_symm : (k + (n - 1)).choose k = (k + (n - 1)).choose (k + (n - 1) - k) := by rw [choose_symm (Nat.le_add_right k (n - 1))]
    have h_sub : k + (n - 1) - k = n - 1 := by omega
    rw [h_symm, h_sub]
  rw [sum_congr rfl h_rew]
  have h_sum := sum_range_add_choose (2 * n) (n - 1)
  have h_eq2 : 2 * n + (n - 1) + 1 = 3 * n := by omega
  have h_eq3 : n - 1 + 1 = n := by omega
  rw [h_eq2, h_eq3] at h_sum
  exact h_sum

lemma choose_mul_fast (p : ℕ) (hp : p.Prime) :
    (3 * p).choose p = 3 * (3 * p - 1).choose (p - 1) := by
  have hp_pos : p > 0 := hp.pos
  have h1 : (3 * p - 1 + 1) * (3 * p - 1).choose (p - 1) = (3 * p - 1 + 1).choose (p - 1 + 1) * (p - 1 + 1) := by
    exact add_one_mul_choose_eq (3 * p - 1) (p - 1)
  have h_eq1 : 3 * p - 1 + 1 = 3 * p := by omega
  have h_eq2 : p - 1 + 1 = p := by omega
  rw [h_eq1, h_eq2] at h1
  have h_eq3 : 3 * p * (3 * p - 1).choose (p - 1) = p * (3 * (3 * p - 1).choose (p - 1)) := by ring
  have h_eq4 : (3 * p).choose p * p = p * (3 * p).choose p := by ring
  rw [h_eq3, h_eq4] at h1
  exact (Nat.eq_of_mul_eq_mul_left hp_pos h1).symm

lemma algebra_mod_p5 (p : ℤ) (x y : ℤ) (hx : p^3 ∣ x) (hy : p^3 ∣ y) (hsum : p^5 ∣ 4 * x + 3 * y) :
    p^5 ∣ (x + 3)^4 * (y + 3)^3 - 2187 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  have h_exp : (p^3 * a + 3)^4 * (p^3 * b + 3)^3 - 2187 =
      p^5 * (p * (a^4 * b^3 * p^15 + 9 * a^4 * b^2 * p^12 + 27 * a^4 * b * p^9 + 27 * a^4 * p^6 +
                  12 * a^3 * b^3 * p^12 + 108 * a^3 * b^2 * p^9 + 324 * a^3 * b * p^6 + 324 * a^3 * p^3 +
                  54 * a^2 * b^3 * p^9 + 486 * a^2 * b^2 * p^6 + 1458 * a^2 * b * p^3 + 1458 * a^2 +
                  108 * a * b^3 * p^6 + 972 * a * b^2 * p^3 + 2916 * a * b + 81 * b^3 * p^3 + 729 * b^2)) +
      729 * (4 * (p^3 * a) + 3 * (p^3 * b)) := by
    ring
  rw [h_exp]
  apply dvd_add
  · exact dvd_mul_right (p^5) _
  · exact dvd_mul_of_dvd_right hsum _

-- Helper sequences and definitions for the Wolstenholme reduction
def A_seq : ℕ → ℤ
  | 0 => 0
  | k + 1 => (k.factorial : ℤ) + (k + 1 : ℤ) * A_seq k

def B_seq : ℕ → ℤ
  | 0 => 0
  | k + 1 => A_seq k + (k + 1 : ℤ) * B_seq k

def C_seq (p : ℤ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 8 * B_seq k + (2 * p + k + 1 : ℤ) * C_seq p k

def f_seq (p : ℤ) : ℕ → ℤ
  | 0 => 1
  | k + 1 => (2 * p + k + 1 : ℤ) * f_seq p k

lemma product_identity (p : ℤ) (k : ℕ) :
    f_seq p k = (k.factorial : ℤ) + 2 * p * A_seq k + 4 * p^2 * B_seq k + p^3 * C_seq p k := by
  induction k with
  | zero =>
    simp [f_seq, A_seq, B_seq, C_seq]
  | succ k ih =>
    simp [f_seq, A_seq, B_seq, C_seq]
    rw [ih]
    rw [Nat.factorial_succ]
    push_cast
    ring

lemma choose_mul_factorial_succ (n k : ℕ) :
    (2 * n + k + 1).choose (k + 1) * (k + 1).factorial = (2 * n + k + 1) * (2 * n + k).choose k * k.factorial := by
  have h1 : (2 * n + k + 1).choose (k + 1) * (k + 1) = (2 * n + k + 1) * (2 * n + k).choose k := by
    exact (add_one_mul_choose_eq (2 * n + k) k).symm
  have h_fact : (k + 1).factorial = (k + 1) * k.factorial := rfl
  rw [h_fact, ← mul_assoc, h1, mul_assoc]

lemma f_seq_eq_choose_mul_factorial (n : ℕ) (k : ℕ) :
    f_seq (n : ℤ) k = (((2 * n + k).choose k * k.factorial : ℕ) : ℤ) := by
  induction k with
  | zero =>
    simp [f_seq]
  | succ k ih =>
    simp [f_seq]
    rw [ih]
    push_cast
    have h_mul := choose_mul_factorial_succ n k
    have h_assoc : (2 * n + (k + 1)).choose (k + 1) * (k + 1).factorial = (2 * n + k + 1) * ((2 * n + k).choose k * k.factorial) := by
      have h_rew : 2 * n + (k + 1) = 2 * n + k + 1 := by omega
      rw [h_rew]
      rw [h_mul]
      ring
    exact_mod_cast h_assoc.symm

lemma nat_div_cast_zmod (p : ℕ) [Fact p.Prime] (a b : ℕ) (h_dvd : b ∣ a) (hb : (b : ZMod p) ≠ 0) :
    ((a / b : ℕ) : ZMod p) = (a : ZMod p) / (b : ZMod p) := by
  have h_eq : a = b * (a / b) := (Nat.mul_div_cancel' h_dvd).symm
  have h_cast : (a : ZMod p) = (b : ZMod p) * ((a / b : ℕ) : ZMod p) := by
    have h_c : ((a : ℕ) : ZMod p) = ((b * (a / b) : ℕ) : ZMod p) := congr_arg (fun (x : ℕ) => (x : ZMod p)) h_eq
    push_cast at h_c
    exact h_c
  rw [h_cast, mul_div_cancel_left₀ _ hb]

lemma fact_div_cast_zmod (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p - 1) :
    (((p - 1).factorial / (i + 1) : ℕ) : ZMod p) = - (1 + i : ZMod p)⁻¹ := by
  have hdvd : i + 1 ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have h_ne : ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hdvd2
    have h_div : (p : ℤ) ∣ (i + 1 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (i + 1 : ℤ) p).mp (by exact_mod_cast hdvd2)
    have h_div_nat : p ∣ i + 1 := by exact_mod_cast h_div
    have h_lt : i + 1 < p := by omega
    have h_le := Nat.le_of_dvd (by omega) h_div_nat
    omega
  have h_rew : ((i + 1 : ℕ) : ZMod p) = ((1 + i : ℕ) : ZMod p) := by
    congr 1
    omega
  rw [nat_div_cast_zmod p (p - 1).factorial (i + 1) hdvd h_ne]
  have h_wilson := ZMod.wilsons_lemma p
  rw [h_wilson, h_rew]
  push_cast
  ring


lemma coprime_of_sum_eq_prime (p a b : ℕ) (hp : p.Prime) (hsum : a + b = p) (ha : a < p) (ha_pos : a > 0) :
    Nat.Coprime a b := by
  have h_gcd : Nat.gcd a b ∣ p := by
    have h1 : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    have h2 : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have h3 : Nat.gcd a b ∣ a + b := dvd_add h1 h2
    rwa [hsum] at h3
  rcases hp.eq_one_or_self_of_dvd _ h_gcd with h_one | h_self
  · exact h_one
  · have h_le : Nat.gcd a b ≤ a := Nat.le_of_dvd ha_pos (Nat.gcd_dvd_left a b)
    omega

lemma coprime_p_factorial (p : ℕ) (hp : p.Prime) :
    Nat.Coprime (p ^ 3) (p - 1).factorial := by
  have hp_pos : p > 0 := hp.pos
  have h_lt : p - 1 < p := by omega
  have h_cop : Nat.Coprime p (p - 1).factorial := Nat.Prime.coprime_factorial_of_lt hp h_lt
  exact Nat.Coprime.pow_left 3 h_cop

def A_sum (k : ℕ) : ℤ :=
  ∑ j ∈ range k, (((k.factorial / (j + 1) : ℕ) : ℤ))

lemma A_seq_eq_A_sum (k : ℕ) :
    A_seq k = A_sum k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [A_seq, ih]
    have h_sum_succ : A_sum (k + 1) = ∑ j ∈ range k, (((k + 1).factorial / (j + 1) : ℕ) : ℤ) + (((k + 1).factorial / (k + 1) : ℕ) : ℤ) := by
      exact sum_range_succ (fun j => (((k + 1).factorial / (j + 1) : ℕ) : ℤ)) k
    rw [h_sum_succ]
    have h_last : (((k + 1).factorial / (k + 1) : ℕ) : ℤ) = (k.factorial : ℤ) := by
      have h_div : (k + 1).factorial / (k + 1) = k.factorial := by
        rw [factorial_succ]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h_div]
    rw [h_last]
    have h_eq : (k + 1 : ℤ) * A_sum k = ∑ j ∈ range k, (((k + 1).factorial / (j + 1) : ℕ) : ℤ) := by
      rw [A_sum, mul_sum]
      apply sum_congr rfl
      intro x hx
      have hx_lt : x < k := by rwa [mem_range] at hx
      have h_dvd : x + 1 ∣ k.factorial := Nat.dvd_factorial (by omega) (by omega)
      have h_div_assoc : (k + 1).factorial / (x + 1) = (k + 1) * (k.factorial / (x + 1)) := by
        rw [factorial_succ]
        exact Nat.mul_div_assoc _ h_dvd
      rw [h_div_assoc]
      push_cast
      ring
    rw [h_eq, add_comm]

lemma product_dvd_factorial (p j : ℕ) (hp : p.Prime) (hj : j < p - 1) :
    (j + 1) * (p - 1 - j) ∣ (p - 1).factorial := by
  have h_sum : (j + 1) + (p - 1 - j) = p := by omega
  have h_lt1 : j + 1 < p := by omega
  have h_lt2 : p - 1 - j < p := by omega
  have h_cop : Nat.Coprime (j + 1) (p - 1 - j) := coprime_of_sum_eq_prime p (j + 1) (p - 1 - j) hp h_sum h_lt1 (by omega)
  have hdvd1 : j + 1 ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have hdvd2 : p - 1 - j ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop hdvd1 hdvd2

lemma div_add_div_eq_mul_div (F A B p : ℕ) (h_dvd : A * B ∣ F) (h_sum : A + B = p) (hA : A > 0) (hB : B > 0) :
    F / A + F / B = p * (F / (A * B)) := by
  rcases h_dvd with ⟨K, rfl⟩
  have h_div1 : (A * B * K) / A = B * K := by
    have h_assoc : A * B * K = A * (B * K) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left (B * K) hA
  have h_div2 : (A * B * K) / B = A * K := by
    have h_assoc : A * B * K = B * (A * K) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left (A * K) hB
  have h_div3 : (A * B * K) / (A * B) = K := by
    exact Nat.mul_div_cancel_left K (Nat.mul_pos hA hB)
  rw [h_div1, h_div2, h_div3]
  rw [← add_mul, ← h_sum]
  ring

lemma sum_factorial_div_reflect (p : ℕ) (hp3 : p ≥ 3) :
    ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
    ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := by
  have h_ref := Finset.sum_range_reflect (fun j => (((p - 1).factorial / (j + 1) : ℕ) : ℤ)) (p - 1)
  have h_congr : ∑ i ∈ range (p - 1), (((p - 1).factorial / (p - 1 - 1 - i + 1) : ℕ) : ℤ) =
                 ∑ i ∈ range (p - 1), (((p - 1).factorial / (p - 1 - i) : ℕ) : ℤ) := by
    apply sum_congr rfl
    intro i hi
    have hi_lt : i < p - 1 := by rwa [mem_range] at hi
    congr 2
    omega
  rw [h_congr] at h_ref
  exact h_ref

lemma A_seq_div_p (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ) ∣ A_seq (p - 1) := by
  rw [A_seq_eq_A_sum]
  have h_reflect := sum_factorial_div_reflect p (by omega)
  have h_add : 2 * A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
    have h_two : 2 * A_sum (p - 1) = A_sum (p - 1) + A_sum (p - 1) := by ring
    rw [h_two]
    have h_sum1 : A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := rfl
    have h_sum2 : A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
      rw [A_sum, sum_factorial_div_reflect p (by omega)]
    nth_rw 1 [h_sum1]
    nth_rw 1 [h_sum2]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    rfl
  have h_rew_reflect : ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                       ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := h_reflect
  have h_sum_add : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) + ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   2 * A_sum (p - 1) := by
    rw [h_rew_reflect, ← two_mul]
    rfl
  have h_dvd_sum : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   (p : ℤ) * ∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj_lt : j < p - 1 := by rwa [mem_range] at hj
    have hdvd := product_dvd_factorial p j hp hj_lt
    have h_sum : (j + 1) + (p - 1 - j) = p := by omega
    have h_div := div_add_div_eq_mul_div (p - 1).factorial (j + 1) (p - 1 - j) p hdvd h_sum (by omega) (by omega)
    push_cast [h_div]
    ring
  rw [h_add, h_dvd_sum] at h_sum_add
  have h_div_z : (p : ℤ) ∣ 2 * A_sum (p - 1) := by
    rw [h_add, h_dvd_sum]
    exact dvd_mul_right (p : ℤ) _
  rw [Int.natCast_dvd] at h_div_z
  have h_abs : (2 * A_sum (p - 1)).natAbs = 2 * (A_sum (p - 1)).natAbs := by
    rw [Int.natAbs_mul]
    rfl
  rw [h_abs] at h_div_z
  have h_cop : Nat.Coprime p 2 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hdvd
    have h_le := Nat.le_of_dvd (by omega) hdvd
    omega
  have h_div_z_comm : p ∣ (A_sum (p - 1)).natAbs * 2 := by
    rw [mul_comm]
    exact h_div_z
  have h_div_abs : p ∣ (A_sum (p - 1)).natAbs := (Nat.Coprime.dvd_mul_right h_cop).mp h_div_z_comm
  rwa [← Int.natCast_dvd] at h_div_abs

lemma two_ne_zero_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h_div : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp (by exact_mod_cast h)
  have h_div_nat : p ∣ 2 := by exact_mod_cast h_div
  have h_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_div_nat
  omega

def equiv_mul_two (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) : ZMod p ≃ ZMod p where
  toFun x := 2 * x
  invFun x := (2 : ZMod p)⁻¹ * x
  left_inv x := by
    dsimp
    have h2 := two_ne_zero_zmod p hp5
    rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  right_inv x := by
    dsimp
    have h2 := two_ne_zero_zmod p hp5
    rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]

lemma sum_inv_square_zero (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    ∑ x : ZMod p, (x⁻¹ ^ 2) = 0 := by
  let h_equiv := equiv_mul_two p hp5
  have h_sum_rew : ∑ x : ZMod p, ((2 * x)⁻¹ ^ 2) = ∑ x : ZMod p, (x⁻¹ ^ 2) :=
    Fintype.sum_equiv h_equiv (fun x => (2 * x)⁻¹ ^ 2) (fun x => x⁻¹ ^ 2) (by intro x; dsimp [h_equiv, equiv_mul_two])
  have h_term : ∀ x : ZMod p, ((2 * x)⁻¹ ^ 2) = (2 : ZMod p)⁻¹ ^ 2 * (x⁻¹ ^ 2) := by
    intro x
    rw [mul_inv, mul_pow]
  have h_sum_mul : ∑ x : ZMod p, ((2 * x)⁻¹ ^ 2) = (2 : ZMod p)⁻¹ ^ 2 * ∑ x : ZMod p, (x⁻¹ ^ 2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    exact h_term x
  have h_alg_eq : (1 - (2 : ZMod p)⁻¹ ^ 2) * ∑ x : ZMod p, (x⁻¹ ^ 2) = 0 := by
    calc
      (1 - (2 : ZMod p)⁻¹ ^ 2) * ∑ x : ZMod p, (x⁻¹ ^ 2) = ∑ x : ZMod p, (x⁻¹ ^ 2) - (2 : ZMod p)⁻¹ ^ 2 * ∑ x : ZMod p, (x⁻¹ ^ 2) := by ring
      _ = ∑ x : ZMod p, (x⁻¹ ^ 2) - ∑ x : ZMod p, ((2 * x)⁻¹ ^ 2) := by rw [h_sum_mul]
      _ = 0 := by rw [h_sum_rew, sub_self]
  have h_ne : 1 - (2 : ZMod p)⁻¹ ^ 2 ≠ 0 := by
    intro h_zero
    have h_eq1 : (1 : ZMod p) = (2 : ZMod p)⁻¹ ^ 2 := by
      exact sub_eq_zero.mp h_zero
    have h_eq2 : (2 : ZMod p)⁻¹ ^ 2 = (4 : ZMod p)⁻¹ := by
      have h_rew : (2 : ZMod p) ^ 2 = 4 := by ring
      rw [inv_pow, h_rew]
    rw [h_eq2] at h_eq1
    have h_eq3 : (1 : ZMod p) = 4 := by
      have h_inv := congr_arg (fun x => x⁻¹) h_eq1
      simp only [inv_one, inv_inv] at h_inv
      exact h_inv
    have h_eq4 : (3 : ZMod p) = 0 := by
      calc
        (3 : ZMod p) = 4 - 1 := by ring
        _ = 1 - 1 := by rw [← h_eq3]
        _ = 0 := by ring
    have h_div : (p : ℤ) ∣ 3 := (ZMod.intCast_zmod_eq_zero_iff_dvd 3 p).mp (by exact_mod_cast h_eq4)
    have h_div_nat : p ∣ 3 := by exact_mod_cast h_div
    have h_le : p ≤ 3 := Nat.le_of_dvd (by decide) h_div_nat
    omega
  rcases mul_eq_zero.mp h_alg_eq with h_one | h_two
  · contradiction
  · exact h_two

lemma sum_zmod_range (p : ℕ) [Fact p.Prime] (g_func : ZMod p → ZMod p) :
    ∑ x : ZMod p, g_func x = ∑ i ∈ range p, g_func i := by
  rcases p with _ | n
  · have hp : Nat.Prime 0 := Fact.out
    exfalso
    exact Nat.not_prime_zero hp
  · let h_equiv := (ZMod.finEquiv (n + 1)).toEquiv
    have h_sum := Fintype.sum_equiv h_equiv (fun (i : Fin (n + 1)) => g_func (h_equiv i)) g_func (fun (i : Fin (n + 1)) => rfl)
    rw [h_sum.symm]
    have h_def : (fun (i : Fin (n + 1)) => g_func (h_equiv i)) = (fun (i : Fin (n + 1)) => g_func i) := rfl
    rw [h_def]
    have h_val : (fun i : Fin (n + 1) => g_func i) = (fun i : Fin (n + 1) => g_func ((i : ℕ) : ZMod (n + 1))) := by
      ext i
      congr 1
      apply Fin.ext
      change i.val = i.val % (n + 1)
      exact (Nat.mod_eq_of_lt i.isLt).symm
    rw [h_val]
    exact Fin.sum_univ_eq_sum_range (n := n + 1) (fun (i : ℕ) => g_func (i : ZMod (n + 1)))

def S2_sum (k : ℕ) : ℤ := ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2

lemma S2_sum_cast_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    ((S2_sum (p - 1) : ℤ) : ZMod p) = ∑ i ∈ range (p - 1), ((1 + i : ZMod p)⁻¹ ^ 2) := by
  unfold S2_sum
  have h_hom : ((∑ i ∈ range (p - 1), (((p - 1).factorial / (i + 1) : ℕ) : ℤ)^2 : ℤ) : ZMod p) =
               (Int.castRingHom (ZMod p)) (∑ i ∈ range (p - 1), (((p - 1).factorial / (i + 1) : ℕ) : ℤ)^2) := rfl
  rw [h_hom, map_sum]
  apply sum_congr rfl
  intro i hi
  have hi_lt : i < p - 1 := by rwa [mem_range] at hi
  have h_fact := fact_div_cast_zmod p i hi_lt
  have h_goal : (Int.castRingHom (ZMod p)) ((((p - 1).factorial / (i + 1) : ℕ) : ℤ) ^ 2) =
                ((((p - 1).factorial / (i + 1) : ℕ) : ZMod p) ^ 2) := by
    rw [map_pow]
    simp only [Int.coe_castRingHom]
    norm_cast
  rw [h_goal, h_fact]
  ring

lemma hS2_proof (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    (p : ℤ) ∣ S2_sum (p - 1) := by
  rcases p with _ | n
  · have hp : Nat.Prime 0 := Fact.out
    exfalso
    exact Nat.not_prime_zero hp
  · have h_sum_zero := sum_inv_square_zero (n + 1) hp5
    have h_range := sum_zmod_range (n + 1) (fun x => x⁻¹ ^ 2)
    have h_range2 : ∑ i ∈ range (n + 1), (i : ZMod (n + 1))⁻¹ ^ 2 = 0 := by
      trans ∑ x : ZMod (n + 1), x⁻¹ ^ 2
      · exact h_range.symm
      · exact h_sum_zero
    rw [sum_range_succ'] at h_range2
    have h_zero : ((0 : ℕ) : ZMod (n + 1))⁻¹ ^ 2 = 0 := by simp
    rw [h_zero, add_zero] at h_range2
    have h_congr : ∑ i ∈ range n, ((i + 1 : ZMod (n + 1))⁻¹ ^ 2) = ∑ i ∈ range n, ((1 + i : ZMod (n + 1))⁻¹ ^ 2) := by
      apply sum_congr rfl
      intro i _
      congr 1
      ring
    push_cast at h_range2
    rw [h_congr] at h_range2
    have h_cast := S2_sum_cast_zmod (n + 1) hp5
    have h_sub_one : n + 1 - 1 = n := by omega
    rw [h_sub_one] at h_cast
    rw [h_range2] at h_cast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (S2_sum n) (n + 1)).mp h_cast

def S_prime (p : ℕ) : ℤ := ∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ)

lemma S_prime_cast_zmod (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    ((S_prime p : ℤ) : ZMod p) = ∑ j ∈ range (p - 1), ((1 + j : ZMod p)⁻¹ ^ 2) := by
  unfold S_prime
  have h_hom : ((∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ) : ℤ) : ZMod p) =
               (Int.castRingHom (ZMod p)) (∑ j ∈ range (p - 1), (((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ)) := rfl
  rw [h_hom, map_sum]
  apply sum_congr rfl
  intro j hj
  have hj_lt : j < p - 1 := by rwa [mem_range] at hj
  have hdvd := product_dvd_factorial p j Fact.out hj_lt
  have h_ne : (((j + 1) * (p - 1 - j) : ℕ) : ZMod p) ≠ 0 := by
    intro h_zero
    have h_div : (p : ℤ) ∣ (((j + 1) * (p - 1 - j) : ℕ) : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (((j + 1) * (p - 1 - j) : ℕ) : ℤ) p).mp (by exact_mod_cast h_zero)
    have h_div_nat : p ∣ (j + 1) * (p - 1 - j) := by exact_mod_cast h_div
    rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime p)).mp h_div_nat with h1 | h2
    · have h_lt : j + 1 < p := by omega
      have h_le := Nat.le_of_dvd (by omega) h1
      omega
    · have h_lt : p - 1 - j < p := by omega
      have h_le := Nat.le_of_dvd (by omega) h2
      omega
  have h_goal : (Int.castRingHom (ZMod p)) ((((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ℤ)) =
                ((((p - 1).factorial / ((j + 1) * (p - 1 - j)) : ℕ) : ZMod p)) := by
    simp only [Int.coe_castRingHom]
    norm_cast
  rw [h_goal]
  rw [nat_div_cast_zmod p (p - 1).factorial ((j + 1) * (p - 1 - j)) hdvd h_ne]
  have h_wilson := ZMod.wilsons_lemma p
  rw [h_wilson]
  have h_sub_eq : (((p - 1 - j : ℕ) : ZMod p)) = - (1 + j : ZMod p) := by
    have hp_zero : (p : ZMod p) = 0 := by exact CharP.cast_eq_zero (ZMod p) p
    have h_omega : p - 1 - j = p - (1 + j) := by omega
    have h_le : 1 + j ≤ p := by omega
    rw [h_omega, Nat.cast_sub h_le]
    push_cast
    rw [hp_zero, zero_sub]
  push_cast
  rw [h_sub_eq]
  have h_mul_ne : (1 + j : ZMod p) ≠ 0 := by
    intro hj0
    have h_div : (p : ℤ) ∣ (1 + j : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + j : ℤ) p).mp (by exact_mod_cast hj0)
    have h_div_nat : p ∣ 1 + j := by exact_mod_cast h_div
    have h_lt : 1 + j < p := by omega
    have h_le := Nat.le_of_dvd (by omega) h_div_nat
    omega
  have h_mul_neg : (j + 1 : ZMod p) * - (1 + j : ZMod p) = - (1 + j : ZMod p)^2 := by
    have h_eq : (j + 1 : ZMod p) = (1 + j : ZMod p) := by ring
    rw [h_eq]
    ring
  rw [h_mul_neg]
  have h_div_neg : -1 / (- (1 + j : ZMod p)^2) = (1 + j : ZMod p)⁻¹ ^ 2 := by
    rw [neg_div_neg_eq]
    have h_inv_eq : (1 + j : ZMod p)^2 = ((1 + j : ZMod p)^2) := rfl
    rw [one_div, inv_pow]
  exact h_div_neg

lemma S_prime_div_p (p : ℕ) [Fact p.Prime] (hp5 : p ≥ 5) :
    (p : ℤ) ∣ S_prime p := by
  rcases p with _ | n
  · have hp : Nat.Prime 0 := Fact.out
    exfalso
    exact Nat.not_prime_zero hp
  · have h_sum_zero := sum_inv_square_zero (n + 1) hp5
    have h_range := sum_zmod_range (n + 1) (fun x => x⁻¹ ^ 2)
    have h_range2 : ∑ i ∈ range (n + 1), (i : ZMod (n + 1))⁻¹ ^ 2 = 0 := by
      trans ∑ x : ZMod (n + 1), x⁻¹ ^ 2
      · exact h_range.symm
      · exact h_sum_zero
    rw [sum_range_succ'] at h_range2
    have h_zero : ((0 : ℕ) : ZMod (n + 1))⁻¹ ^ 2 = 0 := by simp
    rw [h_zero, add_zero] at h_range2
    have h_congr : ∑ i ∈ range n, ((i + 1 : ZMod (n + 1))⁻¹ ^ 2) = ∑ i ∈ range n, ((1 + i : ZMod (n + 1))⁻¹ ^ 2) := by
      apply sum_congr rfl
      intro i _
      congr 1
      ring
    push_cast at h_range2
    rw [h_congr] at h_range2
    have h_cast := S_prime_cast_zmod (n + 1) hp5
    have h_sub_one : n + 1 - 1 = n := by omega
    rw [h_sub_one] at h_cast
    rw [h_range2] at h_cast
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (S_prime (n + 1)) (n + 1)).mp h_cast

lemma A_seq_div_p2 (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    (p : ℤ)^2 ∣ A_seq (p - 1) := by
  rw [A_seq_eq_A_sum]
  have h_reflect := sum_factorial_div_reflect p (by omega)
  have h_add : 2 * A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
    have h_two : 2 * A_sum (p - 1) = A_sum (p - 1) + A_sum (p - 1) := by ring
    rw [h_two]
    have h_sum1 : A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := rfl
    have h_sum2 : A_sum (p - 1) = ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) := by
      rw [A_sum, sum_factorial_div_reflect p (by omega)]
    nth_rw 1 [h_sum1]
    nth_rw 1 [h_sum2]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    push_cast
    rfl
  have h_rew_reflect : ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                       ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) := h_reflect
  have h_sum_add : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) : ℕ) : ℤ) + ∑ j ∈ range (p - 1), (((p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   2 * A_sum (p - 1) := by
    rw [h_rew_reflect, ← two_mul]
    rfl
  have h_dvd_sum : ∑ j ∈ range (p - 1), (((p - 1).factorial / (j + 1) + (p - 1).factorial / (p - 1 - j) : ℕ) : ℤ) =
                   (p : ℤ) * S_prime p := by
    unfold S_prime
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have hj_lt : j < p - 1 := by rwa [mem_range] at hj
    have hdvd := product_dvd_factorial p j hp hj_lt
    have h_sum : (j + 1) + (p - 1 - j) = p := by omega
    have h_div := div_add_div_eq_mul_div (p - 1).factorial (j + 1) (p - 1 - j) p hdvd h_sum (by omega) (by omega)
    push_cast [h_div]
    ring
  have h_mul_eq : 2 * A_sum (p - 1) = (p : ℤ) * S_prime p := h_add.trans h_dvd_sum
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have h_div_S := S_prime_div_p p hp5
  rcases h_div_S with ⟨k, hk⟩
  have h_mul : 2 * A_sum (p - 1) = (p : ℤ)^2 * k := by
    calc
      2 * A_sum (p - 1) = (p : ℤ) * S_prime p := h_mul_eq
      _ = (p : ℤ) * ((p : ℤ) * k) := by rw [hk]
      _ = (p : ℤ)^2 * k := by ring
  have h_div_2A : (p : ℤ)^2 ∣ 2 * A_sum (p - 1) := by
    rw [h_mul]
    exact dvd_mul_right _ _
  have h_pow_cast : (p : ℤ)^2 = ((p^2 : ℕ) : ℤ) := by push_cast; rfl
  rw [h_pow_cast] at h_div_2A
  rw [Int.natCast_dvd] at h_div_2A
  have h_abs : (2 * A_sum (p - 1)).natAbs = 2 * (A_sum (p - 1)).natAbs := by
    rw [Int.natAbs_mul]
    rfl
  rw [h_abs] at h_div_2A
  rw [mul_comm] at h_div_2A
  have h_cop : Nat.Coprime (p^2) 2 := by
    have h_cop_p : Nat.Coprime p 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have h_le := Nat.le_of_dvd (by omega) hdvd
      omega
    exact Nat.Coprime.pow_left 2 h_cop_p
  have h_div_abs : p^2 ∣ (A_sum (p - 1)).natAbs := (Nat.Coprime.dvd_mul_right h_cop).mp h_div_2A
  rwa [← Int.natCast_dvd] at h_div_abs


lemma B_seq_identity (k : ℕ) :
    2 * (k.factorial : ℤ) * B_seq k = (A_seq k)^2 - ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2 := by
  induction k with
  | zero => simp [A_seq, B_seq]
  | succ k ih =>
    have h_LHS : 2 * ((k + 1).factorial : ℤ) * B_seq (k + 1) =
        2 * (k + 1 : ℤ) * (k.factorial : ℤ) * (A_seq k + (k + 1 : ℤ) * B_seq k) := by
      rw [factorial_succ, B_seq]
      push_cast
      ring
    rw [h_LHS]
    have h_split : 2 * (k + 1 : ℤ) * (k.factorial : ℤ) * (A_seq k + (k + 1 : ℤ) * B_seq k) =
        2 * (k + 1 : ℤ) * (k.factorial : ℤ) * A_seq k + (k + 1 : ℤ)^2 * (2 * (k.factorial : ℤ) * B_seq k) := by ring
    rw [h_split, ih]
    have h_sum_succ : ∑ i ∈ range (k + 1), (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2 =
        ∑ i ∈ range k, (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2 + (((k + 1).factorial / (k + 1) : ℕ) : ℤ)^2 := by
      exact sum_range_succ (fun i => (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2) k
    have h_last : (((k + 1).factorial / (k + 1) : ℕ) : ℤ)^2 = (k.factorial : ℤ)^2 := by
      have h_div : (k + 1).factorial / (k + 1) = k.factorial := by
        rw [factorial_succ]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [h_div]
    have h_scale : ∑ i ∈ range k, (((k + 1).factorial / (i + 1) : ℕ) : ℤ)^2 =
        (k + 1 : ℤ)^2 * ∑ i ∈ range k, (((k.factorial / (i + 1) : ℕ) : ℤ))^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      have hx_lt : x < k := by rwa [mem_range] at hx
      have h_dvd : x + 1 ∣ k.factorial := Nat.dvd_factorial (by omega) (by omega)
      have h_div_assoc : (k + 1).factorial / (x + 1) = (k + 1) * (k.factorial / (x + 1)) := by
        rw [factorial_succ]
        exact Nat.mul_div_assoc _ h_dvd
      push_cast [h_div_assoc]
      ring
    have h_A_succ : (A_seq (k + 1))^2 = ((k.factorial : ℤ) + (k + 1 : ℤ) * A_seq k)^2 := by
      rw [A_seq]
    rw [h_A_succ, h_sum_succ, h_scale, h_last]
    ring

lemma B_seq_div_of_A_S2_div (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5)
    (hA : (p : ℤ) ∣ A_seq (p - 1)) (hS2 : (p : ℤ) ∣ S2_sum (p - 1)) :
    (p : ℤ) ∣ B_seq (p - 1) := by
  have h_ident := B_seq_identity (p - 1)
  have h_S2_eq : S2_sum (p - 1) = ∑ i ∈ range (p - 1), (((p - 1).factorial / (i + 1) : ℕ) : ℤ)^2 := rfl
  rw [← h_S2_eq] at h_ident
  have h_sub : (p : ℤ) ∣ (A_seq (p - 1))^2 - S2_sum (p - 1) := by
    apply _root_.dvd_sub
    · exact dvd_pow hA (by omega)
    · exact hS2
  rw [← h_ident] at h_sub
  rw [Int.natCast_dvd] at h_sub
  have h_abs : (2 * ((p - 1).factorial : ℤ) * B_seq (p - 1)).natAbs =
      (2 * (p - 1).factorial) * (B_seq (p - 1)).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    rfl
  rw [h_abs] at h_sub
  have h_cop : Nat.Coprime p (2 * (p - 1).factorial) := by
    have h_cop_fact : Nat.Coprime p (p - 1).factorial := by
      have h_lt : p - 1 < p := by omega
      exact Nat.Prime.coprime_factorial_of_lt hp h_lt
    have h_cop_2 : Nat.Coprime p 2 := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hdvd
      have h_le := Nat.le_of_dvd (by omega) hdvd
      omega
    exact Nat.Coprime.mul_right h_cop_2 h_cop_fact
  have h_sub_comm : p ∣ (B_seq (p - 1)).natAbs * (2 * (p - 1).factorial) := by
    rw [mul_comm]
    exact h_sub
  have h_div_abs : p ∣ (B_seq (p - 1)).natAbs := by
    exact (Nat.Coprime.dvd_mul_right h_cop).mp h_sub_comm
  rwa [← Int.natCast_dvd] at h_div_abs

lemma dvd_RHS_of_dvd_A_B (p : ℕ) (A_div : (p : ℤ)^2 ∣ A_seq (p - 1)) (B_div : (p : ℤ) ∣ B_seq (p - 1)) :
    (p : ℤ)^3 ∣ 2 * p * A_seq (p - 1) + 4 * p^2 * B_seq (p - 1) + p^3 * C_seq p (p - 1) := by
  rcases A_div with ⟨a, ha⟩
  rcases B_div with ⟨b, hb⟩
  rw [ha, hb]
  use 2 * a + 4 * b + C_seq p (p - 1)
  ring

lemma h_S1_mod_deduction (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3)
    (h_div : (p : ℤ)^3 ∣ 2 * p * A_seq (p - 1) + 4 * p^2 * B_seq (p - 1) + p^3 * C_seq p (p - 1)) :
    (p : ℤ)^3 ∣ (3 * (3 * p - 1).choose (p - 1) : ℤ) - 3 := by
  have h_prod := product_identity p (p - 1)
  have h_choose := f_seq_eq_choose_mul_factorial p (p - 1)
  rw [h_choose] at h_prod
  have h_choose_eq : 2 * p + (p - 1) = 3 * p - 1 := by omega
  rw [h_choose_eq] at h_prod
  rw [h_choose_eq] at h_choose
  have h_choose_ge : (3 * p - 1).choose (p - 1) ≥ 1 := by
    apply Nat.choose_pos
    omega
  have h_sub : ((((3 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : ℤ) - ((p - 1).factorial : ℤ)) =
      ((((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial : ℕ) : ℤ) := by
    have h_mul_sub : ((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial = (3 * p - 1).choose (p - 1) * (p - 1).factorial - (p - 1).factorial := by
      rw [Nat.sub_mul, one_mul]
    have h_ge : (p - 1).factorial ≤ (3 * p - 1).choose (p - 1) * (p - 1).factorial := by
      have h_ge1 : 1 ≤ (3 * p - 1).choose (p - 1) := h_choose_ge
      exact Nat.le_mul_of_pos_left _ h_ge1
    have h_cast : (((3 * p - 1).choose (p - 1) * (p - 1).factorial - (p - 1).factorial : ℕ) : ℤ) =
        (((3 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : ℤ) - ((p - 1).factorial : ℤ) := Nat.cast_sub h_ge
    rw [← h_cast]
    exact_mod_cast h_mul_sub.symm
  have h_algebra : (((3 * p - 1).choose (p - 1) * (p - 1).factorial : ℕ) : ℤ) - ((p - 1).factorial : ℤ) =
      2 * (p : ℤ) * A_seq (p - 1) + 4 * (p : ℤ)^2 * B_seq (p - 1) + (p : ℤ)^3 * C_seq p (p - 1) := by
    push_cast
    push_cast at h_prod
    push_cast at h_choose
    linarith [h_prod, h_choose]
  rw [h_sub] at h_algebra
  have h_div_z : (p : ℤ)^3 ∣ ((((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial : ℕ) : ℤ) := by
    rwa [← h_algebra] at h_div
  have h_div_n : p^3 ∣ ((3 * p - 1).choose (p - 1) - 1) * (p - 1).factorial := by
    exact_mod_cast h_div_z
  have h_cop : Nat.Coprime (p ^ 3) (p - 1).factorial := coprime_p_factorial p hp
  have h_dvd_n : p^3 ∣ (3 * p - 1).choose (p - 1) - 1 := by
    exact (Nat.Coprime.dvd_mul_right h_cop).mp h_div_n
  have h_dvd_z2 : (p : ℤ)^3 ∣ (((3 * p - 1).choose (p - 1) - 1 : ℕ) : ℤ) := by
    exact_mod_cast h_dvd_n
  have h_final_sub : (((3 * p - 1).choose (p - 1) - 1 : ℕ) : ℤ) = ((3 * p - 1).choose (p - 1) : ℤ) - 1 := by
    exact Nat.cast_sub h_choose_ge
  rw [h_final_sub] at h_dvd_z2
  have h_mult : (3 * (3 * p - 1).choose (p - 1) : ℤ) - 3 = 3 * (((3 * p - 1).choose (p - 1) : ℤ) - 1) := by ring
  rw [h_mult]
  exact dvd_mul_of_dvd_right h_dvd_z2 3


lemma int_dvd_of_dvd_mul_left_of_coprime (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) (Y : ℤ) (h_dvd : (p : ℤ)^3 ∣ 3 * Y) :
    (p : ℤ)^3 ∣ Y := by
  have h_cop : IsCoprime ((p : ℤ)^3) 3 := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_nat_coprime]
    have h_p_abs : (p : ℤ).natAbs = p := rfl
    have h_3_abs : (3 : ℤ).natAbs = 3 := rfl
    rw [h_p_abs, h_3_abs]
    apply hp.coprime_iff_not_dvd.mpr
    intro h_dvd3
    have h_le := Nat.le_of_dvd (by decide) h_dvd3
    omega
  exact IsCoprime.dvd_of_dvd_mul_left h_cop h_dvd


/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  rcases eq_or_ne p 3 with rfl | hp_ne
  · decide
  · have hp5 : p ≥ 5 := by
      have h_ne4 : p ≠ 4 := by
        intro h_eq
        subst h_eq
        have : ¬ Nat.Prime 4 := by decide
        contradiction
      omega
    have h_S1 : Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) = (3 * p).choose p := by
      exact S1_eq_choose p (by omega)
    have h_S1_fast : (3 * p).choose p = 3 * (3 * p - 1).choose (p - 1) := by
      exact choose_mul_fast p hp
    have h_S1_comp : Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) = 3 * (3 * p - 1).choose (p - 1) := by
      rw [h_S1, h_S1_fast]
    
    have h_S1_mod : (p : ℤ)^3 ∣ (3 * (3 * p - 1).choose (p - 1) : ℤ) - 3 := by
      have A_div : (p : ℤ)^2 ∣ A_seq (p - 1) := A_seq_div_p2 p hp hp5
      have B_div : (p : ℤ) ∣ B_seq (p - 1) := by
        have hA : (p : ℤ) ∣ A_seq (p - 1) := A_seq_div_p p hp hp5
        have hS2 : (p : ℤ) ∣ S2_sum (p - 1) := by
          haveI : Fact p.Prime := ⟨hp⟩
          exact hS2_proof p hp5
        exact B_seq_div_of_A_S2_div p hp hp5 hA hS2
      have h_div_AB := dvd_RHS_of_dvd_A_B p A_div B_div
      exact h_S1_mod_deduction p hp hp3 h_div_AB
      
    have h_sum_mod : (p : ℤ)^5 ∣ 4 * ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3) + 3 * (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3) := by
      sorry

    have h_S2_mod : (p : ℤ)^3 ∣ ((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3 := by
      have h_p3_p5 : (p : ℤ)^3 ∣ (p : ℤ)^5 := by
        use (p : ℤ)^2
        ring
      have h_sum_p3 : (p : ℤ)^3 ∣ 4 * ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3) + 3 * (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3) := dvd_trans h_p3_p5 h_sum_mod
      have h_4X_p3 : (p : ℤ)^3 ∣ 4 * ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3) := dvd_mul_of_dvd_right h_S1_mod 4
      have h_3Y_p3 : (p : ℤ)^3 ∣ 3 * (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3) := by
        have h_sub : 3 * (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3) =
                     (4 * ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3) + 3 * (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3)) -
                     4 * ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3) := by ring
        rw [h_sub]
        exact dvd_sub h_sum_p3 h_4X_p3
      exact int_dvd_of_dvd_mul_left_of_coprime p hp hp5 _ h_3Y_p3

    -- Now we apply our proven algebra_mod_p5 to combine these properties:
    have h_alg := algebra_mod_p5 (p : ℤ)
        ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3)
        (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3)
        h_S1_mod h_S2_mod h_sum_mod
    
    have h_sim : ((3 * (3 * p - 1).choose (p - 1) : ℤ) - 3 + 3) = (3 * (3 * p - 1).choose (p - 1) : ℤ) := by ring
    have h_sim2 : (((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) - 3 + 3) = ((Finset.sum (range (2 * p + 1)) (fun k => ((p + k - 1).choose k) ^ 2) : ℕ) : ℤ) := by ring
    rw [h_sim, h_sim2] at h_alg
    
    have h_rew_S1 : ((Finset.sum (range (2 * p + 1)) (fun k => (p + k - 1).choose k) : ℕ) : ℤ) = (3 * (3 * p - 1).choose (p - 1) : ℤ) := by
      exact_mod_cast h_S1_comp
    rw [← h_rew_S1] at h_alg
    
    have h_A1 : A357674 1 = 2187 := by decide
    rw [Nat.modEq_iff_dvd]
    push_cast
    rw [h_A1]
    have h_flip : ((2187 : ℕ) : ℤ) - ((A357674 p : ℕ) : ℤ) = -(((A357674 p : ℕ) : ℤ) - ((2187 : ℕ) : ℤ)) := by ring
    rw [h_flip, dvd_neg]
    unfold A357674
    dsimp
    push_cast
    push_cast at h_alg
    exact h_alg
