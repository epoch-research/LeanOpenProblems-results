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

def dsum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

lemma dsum_mul10_add (a d : ℕ) (hd : d < 10) : dsum (10 * a + d) = dsum a + d := by
  by_cases h0 : d = 0 ∧ a = 0
  · rcases h0 with ⟨rfl, rfl⟩
    simp [dsum]
  · have hxy : d ≠ 0 ∨ a ≠ 0 := by omega
    rw [show 10 * a + d = d + 10 * a by omega]
    simp [dsum, Nat.digits_add 10 (by norm_num) d a hd hxy]
    omega

lemma div10_carry_le (d c : ℕ) (hd : d < 10) (hc : c ≤ 4) : (5 * d + c) / 10 ≤ 4 := by
  omega

lemma carry_compl_div (d c : ℕ) (hd : d < 10) (hc : c ≤ 4) :
    (49 - (5 * d + c)) / 10 = 4 - (5 * d + c) / 10 := by
  interval_cases d <;> interval_cases c <;> norm_num

lemma carry_compl_mod (d c : ℕ) (hd : d < 10) (hc : c ≤ 4) :
    (5 * d + c) % 10 + (49 - (5 * d + c)) % 10 = 9 := by
  interval_cases d <;> interval_cases c <;> norm_num

lemma low_expr_le_49 (d c : ℕ) (hd : d < 10) (hc : c ≤ 4) : 5 * d + c ≤ 49 := by omega

lemma dsum_five_compl_carry (L q c : ℕ) (hq : q < 10 ^ L) (hc : c ≤ 4) :
    dsum (5 * q + c) + dsum (5 * (10 ^ L - 1 - q) + (4 - c)) = 9 * L + 4 := by
  induction L generalizing q c with
  | zero =>
      have hq0 : q = 0 := by omega
      subst q
      interval_cases c <;> norm_num [dsum]
  | succ L ih =>
      let a := q / 10
      let d := q % 10
      have hd : d < 10 := by
        dsimp [d]
        exact Nat.mod_lt _ (by norm_num)
      have hq_eq : q = 10 * a + d := by
        dsimp [a, d]
        omega
      have hpow : 10 ^ (L + 1) = 10 * 10 ^ L := by
        simpa [pow_succ'] using (Nat.mul_comm (10 ^ L) 10)
      have ha : a < 10 ^ L := by
        dsimp [a]
        rw [hpow] at hq
        exact Nat.div_lt_of_lt_mul hq
      let C := (5 * d + c) / 10
      let R := (5 * d + c) % 10
      have hCle : C ≤ 4 := by exact div10_carry_le d c hd hc
      have hRlt : R < 10 := by
        dsimp [R]
        exact Nat.mod_lt _ (by norm_num)
      have h1 : 5 * q + c = 10 * (5 * a + C) + R := by
        dsimp [C, R]
        rw [hq_eq]
        have := Nat.div_add_mod (5 * d + c) 10
        omega
      let Q := 10 ^ L - 1 - a
      let B := 49 - (5 * d + c)
      have hBdiv : B / 10 = 4 - C := by
        dsimp [B, C]
        exact carry_compl_div d c hd hc
      have hBmodsum : R + B % 10 = 9 := by
        dsimp [R, B]
        exact carry_compl_mod d c hd hc
      have hBlt : B % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h2 : 5 * (10 ^ (L + 1) - 1 - q) + (4 - c) = 10 * (5 * Q + (4 - C)) + B % 10 := by
        dsimp [Q, B, C]
        rw [hpow, hq_eq]
        have hdle : d ≤ 9 := by omega
        have hcle : c ≤ 4 := hc
        have hlo : 5 * d + c ≤ 49 := low_expr_le_49 d c hd hc
        have hdivmod := Nat.div_add_mod (49 - (5 * d + c)) 10
        omega
      rw [h1, h2]
      rw [dsum_mul10_add (5 * a + C) R hRlt]
      rw [dsum_mul10_add (5 * Q + (4 - C)) (B % 10) hBlt]
      have ih' := ih a C ha hCle
      -- combine arithmetic
      nlinarith [ih', hBmodsum]


lemma dsum_compl (L q : ℕ) (hq : q < 10 ^ L) :
    dsum q + dsum (10 ^ L - 1 - q) = 9 * L := by
  induction L generalizing q with
  | zero =>
      have hq0 : q = 0 := by omega
      subst q
      norm_num [dsum]
  | succ L ih =>
      let a := q / 10
      let d := q % 10
      have hd : d < 10 := by
        dsimp [d]
        exact Nat.mod_lt _ (by norm_num)
      have hq_eq : q = 10 * a + d := by
        dsimp [a, d]
        omega
      have hpow : 10 ^ (L + 1) = 10 * 10 ^ L := by
        simpa [pow_succ'] using (Nat.mul_comm (10 ^ L) 10)
      have ha : a < 10 ^ L := by
        dsimp [a]
        rw [hpow] at hq
        exact Nat.div_lt_of_lt_mul hq
      let Q := 10 ^ L - 1 - a
      have hd9 : 9 - d < 10 := by omega
      have hcomp : 10 ^ (L + 1) - 1 - q = 10 * Q + (9 - d) := by
        dsimp [Q]
        rw [hpow, hq_eq]
        omega
      rw [hcomp]
      rw [hq_eq]
      rw [dsum_mul10_add a d hd]
      rw [dsum_mul10_add Q (9 - d) hd9]
      have ih' := ih a ha
      change dsum a + d + (dsum (10 ^ L - 1 - a) + (9 - d)) = 9 * (L + 1)
      omega


lemma dsum_five_add_four (n : ℕ) : dsum (5 * n + 4) = dsum (5 * n) + 4 := by
  let a := n / 10
  let d := n % 10
  have hd : d < 10 := by
    dsimp [d]
    exact Nat.mod_lt _ (by norm_num)
  have hn_eq : n = 10 * a + d := by
    dsimp [a, d]
    omega
  let C := (5 * d) / 10
  let R := (5 * d) % 10
  have hRlt : R < 10 := by
    dsimp [R]
    exact Nat.mod_lt _ (by norm_num)
  have hR4lt : R + 4 < 10 := by
    dsimp [R]
    interval_cases d <;> norm_num
  have h1 : 5 * n = 10 * (5 * a + C) + R := by
    dsimp [C, R]
    rw [hn_eq]
    have := Nat.div_add_mod (5 * d) 10
    omega
  have h2 : 5 * n + 4 = 10 * (5 * a + C) + (R + 4) := by
    rw [h1]
    omega
  rw [h2]
  rw [h1]
  rw [dsum_mul10_add (5 * a + C) R hRlt]
  rw [dsum_mul10_add (5 * a + C) (R + 4) hR4lt]
  omega

lemma dsum_five_compl (L q : ℕ) (hq : q < 10 ^ L) :
    dsum (5 * q) + dsum (5 * (10 ^ L - 1 - q)) = 9 * L := by
  have h := dsum_five_compl_carry L q 0 hq (by norm_num)
  simp only [tsub_zero] at h
  rw [dsum_five_add_four (10 ^ L - 1 - q)] at h
  change dsum (5 * q) + (dsum (5 * (10 ^ L - 1 - q)) + 4) = 9 * L + 4 at h
  omega


def term (n : ℕ) : ℤ := Int.sign ((dsum (5 * n) : ℤ) - (dsum n : ℤ))
def psum (n : ℕ) : ℤ := ∑ x ∈ Finset.range (n + 1), term x

lemma Int_sign_add_eq_zero {a b : ℤ} (h : a + b = 0) : Int.sign a + Int.sign b = 0 := by
  have hb : b = -a := by omega
  subst b
  simp

lemma term_compl (L q : ℕ) (hq : q < 10 ^ L) :
    term q + term (10 ^ L - 1 - q) = 0 := by
  let y := 10 ^ L - 1 - q
  have hds := dsum_compl L q hq
  have h5 := dsum_five_compl L q hq
  have hdiff : ((dsum (5 * q) : ℤ) - (dsum q : ℤ)) +
      ((dsum (5 * y) : ℤ) - (dsum y : ℤ)) = 0 := by
    dsimp [y]
    omega
  unfold term
  dsimp [y] at hdiff ⊢
  exact Int_sign_add_eq_zero hdiff

lemma psum_succ (n : ℕ) : psum (n + 1) = psum n + term (n + 1) := by
  unfold psum
  rw [show n + 1 + 1 = (n + 1) + 1 by omega]
  rw [Finset.sum_range_succ]

lemma psum_eq_prev_add (n : ℕ) (hn : 0 < n) : psum n = psum (n - 1) + term n := by
  have h : n - 1 + 1 = n := by omega
  have hs := psum_succ (n - 1)
  rwa [h] at hs


lemma psum_symm_of_center (L m : ℕ) (hm : 2 * m + 1 = 10 ^ L - 1) :
    ∀ i : ℕ, i ≤ m → psum (m - i) = psum (m + i) := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
      have hi_le : i ≤ m := by omega
      have hsucc : i + 1 ≤ m := hi
      have hpos : 0 < m - i := by omega
      have hprev := psum_eq_prev_add (m - i) hpos
      have hsub : (m - i) - 1 = m - (i + 1) := by omega
      rw [hsub] at hprev
      have hs := psum_succ (m + i)
      have hcomp_arg_lt : m - i < 10 ^ L := by omega
      have hcomp_eq : 10 ^ L - 1 - (m - i) = m + i + 1 := by omega
      have hpair := term_compl L (m - i) hcomp_arg_lt
      rw [hcomp_eq] at hpair
      have hih := ih hi_le
      rw [show m + (i + 1) = m + i + 1 by omega]
      omega

lemma A289411_eq (n : ℕ) : A289411 n = (psum n).toNat := by
  simp [A289411, psum, term, dsum]


/--
this relation is conjectured to hold for any k > 0, where $m_k = 10^k/2 - 1$.
The relation is $a(m_k - i) = a(m_k + i)$ for $i = 0 \dots m_k$.
-/
theorem oeis_289411_conjecture_0 (k : ℕ) (hk : 0 < k) :
  let m_k : ℕ := (10 ^ k) / 2 - 1
  ∀ i : ℕ, i ≤ m_k → A289411 (m_k - i) = A289411 (m_k + i) :=
by
  cases k with
  | zero => omega
  | succ K =>
      dsimp
      intro i hi
      let m : ℕ := 10 ^ (K + 1) / 2 - 1
      change i ≤ m at hi
      have hpow2 : 10 ^ (K + 1) = 2 * (5 * 10 ^ K) := by
        rw [pow_succ']
        ring
      have hhalf : 10 ^ (K + 1) / 2 = 5 * 10 ^ K := by
        rw [hpow2]
        exact Nat.mul_div_right (5 * 10 ^ K) (by norm_num : 0 < 2)
      have hm : 2 * m + 1 = 10 ^ (K + 1) - 1 := by
        dsimp [m]
        rw [hhalf, hpow2]
        have hpos : 0 < 10 ^ K := pow_pos (by norm_num) K
        omega
      have hsym := psum_symm_of_center (K + 1) m hm i hi
      rw [A289411_eq, A289411_eq]
      exact congrArg Int.toNat hsym
