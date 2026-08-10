import FormalConjectures.Util.ProblemImports

open Nat
open scoped BigOperators

/--
A289411: $\mathrm{a}(n) = \sum_{k=0}^n \mathrm{sign}(\mathrm{A007953}(5k) - \mathrm{A007953}(k))$.
$\mathrm{A007953}(n)$ is the digital sum of $n$ in base 10.
The sequence is non-negative, so the sum over $\mathbb{Z}$ is converted to $\mathbb{N}$.
-/
def A289411 (n : ℕ) : ℕ :=
  let digital_sum_ten (m : ℕ) : ℕ := (Nat.digits 10 m).sum
  (Finset.range (n + 1)).sum (fun k =>
    Int.sign ((digital_sum_ten (5 * k) : ℤ) - (digital_sum_ten k : ℤ)))
  |>.toNat

private def D (n : ℕ) : ℕ := (Nat.digits 10 n).sum

private lemma D_zero : D 0 = 0 := by
  simp [D]

private lemma D_pos (n : ℕ) (hn : n ≠ 0) : D n = n % 10 + D (n / 10) := by
  dsimp [D]
  rw [Nat.digits_eq_cons_digits_div (by decide) hn]
  rfl

private lemma div_mod_ten_helper (A B : ℕ) (hB : B < 10) :
    (10 * A + B) / 10 = A ∧ (10 * A + B) % 10 = B := by
  omega

private lemma five_q_eq (q : ℕ) : 5 * q = 10 * (q / 2) + 5 * (q % 2) := by
  have h := Nat.div_add_mod q 2
  omega

private lemma D_five_q (q : ℕ) : D (5 * q) = 5 * (q % 2) + D (q / 2) := by
  by_cases hq : q = 0
  · subst hq
    simp [D_zero]
  · have h5q : 5 * q ≠ 0 := by omega
    rw [D_pos (5 * q) h5q]
    have hq2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
    have h_b : 5 * (q % 2) < 10 := by omega
    have h_eq : 5 * q = 10 * (q / 2) + 5 * (q % 2) := five_q_eq q
    have h_div_mod := div_mod_ten_helper (q / 2) (5 * (q % 2)) h_b
    rw [h_eq]
    rw [h_div_mod.1, h_div_mod.2]

private lemma D_five_q_add (q : ℕ) (c : ℕ) (hc : c < 5) : D (5 * q + c) = 5 * (q % 2) + c + D (q / 2) := by
  by_cases h0 : 5 * q + c = 0
  · have h_q : q = 0 := by omega
    have h_c : c = 0 := by omega
    subst h_q h_c
    simp [D_zero]
  · rw [D_pos (5 * q + c) h0]
    have hq2 : q % 2 < 2 := Nat.mod_lt _ (by decide)
    have h_b : 5 * (q % 2) + c < 10 := by omega
    have h_eq : 5 * q + c = 10 * (q / 2) + (5 * (q % 2) + c) := by
      have h := five_q_eq q
      omega
    have h_div_mod := div_mod_ten_helper (q / 2) (5 * (q % 2) + c) h_b
    rw [h_eq]
    rw [h_div_mod.1, h_div_mod.2]

private lemma D_five_q_add_universal (q : ℕ) (c : ℕ) (hc : c < 5) : D (5 * q + c) = D (5 * q) + c := by
  rw [D_five_q_add q c hc]
  rw [D_five_q q]
  omega

private lemma f_r_add_f_nine_sub_r (r : ℕ) (hr : r < 10) :
    (r / 2 + 5 * (r % 2)) + ((9 - r) / 2 + 5 * ((9 - r) % 2)) = 9 := by
  revert r hr
  decide

private lemma D_def (n : ℕ) : D n = n % 10 + D (n / 10) := by
  by_cases hn : n = 0
  · subst hn; simp [D_zero]
  · rw [D_pos n hn]

private lemma D_add_D_nine_complement (k : ℕ) : ∀ x : ℕ, x < 10 ^ k → D x + D (10 ^ k - 1 - x) = 9 * k := by
  induction k with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    simp [D_zero]
  | succ k ih =>
    intro x hx
    have h_div : x / 10 < 10 ^ k := by
      have h1 : 10 ^ (k + 1) = 10 ^ k * 10 := by ring
      rw [h1] at hx
      omega
    have h_mod : x % 10 < 10 := Nat.mod_lt _ (by decide)
    have h_y : 10 ^ (k + 1) - 1 - x = 10 * (10 ^ k - 1 - x / 10) + (9 - x % 10) := by
      have h1 : 10 ^ (k + 1) = 10 ^ k * 10 := by ring
      omega
    have h_dx : D x = x % 10 + D (x / 10) := D_def x
    have h_dy : D (10 ^ (k + 1) - 1 - x) = (9 - x % 10) + D (10 ^ k - 1 - x / 10) := by
      rw [h_y]
      have h_b : 9 - x % 10 < 10 := by omega
      have h_div_mod := div_mod_ten_helper (10 ^ k - 1 - x / 10) (9 - x % 10) h_b
      by_cases h0 : 10 * (10 ^ k - 1 - x / 10) + (9 - x % 10) = 0
      · have h_q' : 10 ^ k - 1 - x / 10 = 0 := by omega
        have h_r' : 9 - x % 10 = 0 := by omega
        rw [h0, D_zero]
        rw [h_q', D_zero]
        omega
      · rw [D_pos _ h0]
        rw [h_div_mod.1, h_div_mod.2]
    rw [h_dx, h_dy]
    have h_ih := ih (x / 10) h_div
    omega

private lemma D_five_mul_decomp (q r : ℕ) (hr : r < 10) :
    D (5 * (10 * q + r)) = D (5 * q) + r / 2 + 5 * (r % 2) := by
  have h_eq : 5 * (10 * q + r) = 10 * (5 * q + r / 2) + 5 * (r % 2) := by omega
  have h_b : 5 * (r % 2) < 10 := by
    have : r % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have h_div_mod := div_mod_ten_helper (5 * q + r / 2) (5 * (r % 2)) h_b
  by_cases h0 : 10 * (5 * q + r / 2) + 5 * (r % 2) = 0
  · have h_q2 : 5 * q + r / 2 = 0 := by omega
    have h_r2 : 5 * (r % 2) = 0 := by omega
    have h_q : q = 0 := by omega
    have h_r : r = 0 := by omega
    subst h_q h_r
    simp [D_zero]
  · rw [h_eq]
    rw [D_pos _ h0]
    rw [h_div_mod.1, h_div_mod.2]
    have h_c : r / 2 < 5 := by omega
    rw [D_five_q_add_universal q (r / 2) h_c]
    omega

private lemma D_five_mul_add_D_five_mul_nine_complement (k : ℕ) :
    ∀ x : ℕ, x < 10 ^ k → D (5 * x) + D (5 * (10 ^ k - 1 - x)) = 9 * k := by
  induction k with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by omega
    subst hx0
    simp [D_zero]
  | succ k ih =>
    intro x hx
    have h_div : x / 10 < 10 ^ k := by
      have h1 : 10 ^ (k + 1) = 10 ^ k * 10 := by ring
      rw [h1] at hx
      omega
    have h_mod : x % 10 < 10 := Nat.mod_lt _ (by decide)
    have h_y : 10 ^ (k + 1) - 1 - x = 10 * (10 ^ k - 1 - x / 10) + (9 - x % 10) := by
      have h1 : 10 ^ (k + 1) = 10 ^ k * 10 := by ring
      omega
    have h_dx : D (5 * x) = D (5 * (x / 10)) + (x % 10) / 2 + 5 * ((x % 10) % 2) := by
      have h_eq : x = 10 * (x / 10) + x % 10 := (Nat.div_add_mod x 10).symm
      nth_rw 1 [h_eq]
      apply D_five_mul_decomp (x / 10) (x % 10) h_mod
    have h_dy : D (5 * (10 ^ (k + 1) - 1 - x)) = D (5 * (10 ^ k - 1 - x / 10)) + (9 - x % 10) / 2 + 5 * ((9 - x % 10) % 2) := by
      rw [h_y]
      have h_b : 9 - x % 10 < 10 := by omega
      apply D_five_mul_decomp (10 ^ k - 1 - x / 10) (9 - x % 10) h_b
    rw [h_dx, h_dy]
    have h_ih := ih (x / 10) h_div
    have h_f := f_r_add_f_nine_sub_r (x % 10) h_mod
    omega

private lemma Int_sign_neg (x : ℤ) : Int.sign (-x) = - Int.sign x := by
  cases x with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n => rfl
  | negSucc n => rfl

private lemma sign_sub_eq_neg_sign_sub (A B C D : ℕ) (h : A + B = C + D) :
    Int.sign ((A : ℤ) - (C : ℤ)) = - Int.sign ((B : ℤ) - (D : ℤ)) := by
  have h_eq : (A : ℤ) - (C : ℤ) = - ((B : ℤ) - (D : ℤ)) := by omega
  rw [h_eq]
  rw [Int_sign_neg]

private lemma sign_sub_nine_complement (k : ℕ) (x : ℕ) (hx : x < 10 ^ k) :
    Int.sign (((D (5 * (10 ^ k - 1 - x)) : ℤ) - (D (10 ^ k - 1 - x) : ℤ))) =
    - Int.sign (((D (5 * x) : ℤ) - (D x) : ℤ)) := by
  have h1 := D_add_D_nine_complement k x hx
  have h2 := D_five_mul_add_D_five_mul_nine_complement k x hx
  have h_sum : D (5 * (10 ^ k - 1 - x)) + D (5 * x) = D (10 ^ k - 1 - x) + D x := by omega
  apply sign_sub_eq_neg_sign_sub _ _ _ _ h_sum

private lemma ico_sum_zero (k : ℕ) (hk : 0 < k) :
    let m_k : ℕ := (10 ^ k) / 2 - 1
    let f : ℕ → ℤ := fun j => Int.sign ((D (5 * j) : ℤ) - (D j : ℤ))
    ∀ i : ℕ, i ≤ m_k → (Finset.Ico (m_k - i + 1) (m_k + i + 1)).sum f = 0 := by
  intro m_k f i hi
  induction i with
  | zero =>
    have : m_k - 0 + 1 = m_k + 1 := by omega
    rw [this]
    simp
  | succ i ih =>
    have hi_succ : i < m_k := by omega
    have ih_val : (Finset.Ico (m_k - i + 1) (m_k + i + 1)).sum f = 0 := ih (by omega)
    let a := m_k - i
    let b := m_k + i + 1
    have hab : a < b := by dsimp [a, b]; omega
    have hab_le : a ≤ b := by omega
    have h_top := Finset.sum_Ico_succ_top hab_le f
    have h_bot := Finset.sum_eq_sum_Ico_succ_bot hab f
    have h_decomp : (Finset.Ico (m_k - i) (m_k + i + 2)).sum f = f (m_k - i) + (Finset.Ico (m_k - i + 1) (m_k + i + 1)).sum f + f (m_k + i + 1) := by
      have h1 : b + 1 = m_k + i + 2 := by omega
      have h2 : a + 1 = m_k - i + 1 := by omega
      rw [← h1, ← h2]
      rw [h_top, h_bot]
    have h_goal : (Finset.Ico (m_k - (i + 1) + 1) (m_k + (i + 1) + 1)).sum f = (Finset.Ico (m_k - i) (m_k + i + 2)).sum f := by
      congr 2 <;> omega
    rw [h_goal, h_decomp, ih_val]
    have h_f : f (m_k + i + 1) = - f (m_k - i) := by
      dsimp [f]
      have hx : m_k - i < 10 ^ k := by
        have h_mk : m_k = 10 ^ k / 2 - 1 := rfl
        have hk_pow : 10 ^ k ≥ 2 := by
          have : 10 ^ k ≥ 10 ^ 1 := Nat.pow_le_pow_right (by decide) hk
          omega
        omega
      have h_compl : 10 ^ k - 1 - (m_k - i) = m_k + i + 1 := by
        have h_mk : m_k = 10 ^ k / 2 - 1 := rfl
        have hk_pow : 10 ^ k ≥ 2 := by
          have : 10 ^ k ≥ 10 ^ 1 := Nat.pow_le_pow_right (by decide) hk
          omega
        have h_even : 10 ^ k = 2 * (10 ^ k / 2) := by
          have h_div : 10 ^ k % 2 = 0 := by
            match k with
            | 0 => omega
            | k + 1 =>
              rw [Nat.pow_succ]
              have : 10 ^ k * 10 = 2 * (10 ^ k * 5) := by ring
              rw [this]
              simp
          omega
        omega
      rw [← h_compl]
      apply sign_sub_nine_complement k (m_k - i) hx
    rw [h_f]
    omega

/--
this relation is conjectured to hold for any k > 0, where $m_k = 10^k/2 - 1$.
The relation is $a(m_k - i) = a(m_k + i)$ for $i = 0 \dots m_k$.
-/
theorem oeis_289411_conjecture_0 (k : ℕ) (hk : 0 < k) :
  let m_k : ℕ := (10 ^ k) / 2 - 1
  ∀ i : ℕ, i ≤ m_k → A289411 (m_k - i) = A289411 (m_k + i) := by
  intro m_k i hi
  dsimp [A289411]
  let f : ℕ → ℤ := fun j => Int.sign (((Nat.digits 10 (5 * j)).sum : ℤ) - ((Nat.digits 10 j).sum : ℤ))
  have h_le : m_k - i + 1 ≤ m_k + i + 1 := by omega
  have h_sum := Finset.sum_range_add_sum_Ico f h_le
  have h_ico : (Finset.Ico (m_k - i + 1) (m_k + i + 1)).sum f = 0 := by
    apply ico_sum_zero k hk i hi
  rw [h_ico] at h_sum
  rw [add_zero] at h_sum
  rw [h_sum]


