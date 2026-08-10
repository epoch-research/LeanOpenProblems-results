import FormalConjectures.Util.ProblemImports

open Nat List

-- rev_base(b, n) is the natural number whose base b digits are the reverse of n's digits
/-- `rev_base b n` is the number whose base-`b` digits are the reversal of `n`'s base-`b` digits. -/
def rev_base (b n : ℕ) : ℕ := Nat.ofDigits b (Nat.digits b n |>.reverse)

/--
$a_n$ is the $n$-th term of the trajectory of $103$ under the Reverse and Add! operation carried out in base $3$, written in base $10$.
$a_0 = 103$.
$a_{n+1} = a_n + \text{rev}_3(a_n)$, where $\text{rev}_3(n)$ is the number whose base $3$ digits are the reversal of $n$'s base $3$ digits.
-/
def A077408 : ℕ → ℕ
  | 0 => 103
  | n + 1 => A077408 n + rev_base 3 (A077408 n)

/-- A natural number $n$ is a base $b$ palindrome if its base $b$ digits read the same forwards and backwards.
This is equivalent to $n = \text{rev}_b(n)$. -/
def is_base_palindrome (b n : ℕ) : Prop := n = rev_base b n

theorem rev_base_three_mod_two (x : ℕ) : rev_base 3 x ≡ x [MOD 2] := by
  dsimp [rev_base]
  have h2 (L : List ℕ) : ofDigits 3 L ≡ L.sum [MOD 2] := by
    have g1 : ofDigits 3 L ≡ ofDigits (3 % 2) L [MOD 2] := ofDigits_modEq 3 2 L
    have g2 : 3 % 2 = 1 := rfl
    rw [g2] at g1
    have g3 : ofDigits 1 L = L.sum := ofDigits_one L
    rw [g3] at g1
    exact g1
  have h3 : ofDigits 3 (digits 3 x).reverse ≡ (digits 3 x).reverse.sum [MOD 2] := h2 (digits 3 x).reverse
  have h4 : x ≡ (digits 3 x).sum [MOD 2] := by
    have temp := h2 (digits 3 x)
    rw [ofDigits_digits 3 x] at temp
    exact temp
  have h5 : (digits 3 x).reverse.sum = (digits 3 x).sum := List.sum_reverse (digits 3 x)
  rw [h5] at h3
  exact h3.trans h4.symm

theorem A077408_succ_even (n : ℕ) : Even (A077408 (n + 1)) := by
  dsimp [A077408]
  rw [Nat.even_iff]
  have h : (A077408 n + rev_base 3 (A077408 n)) % 2 = (A077408 n + A077408 n) % 2 := by
    have m : rev_base 3 (A077408 n) ≡ A077408 n [MOD 2] := rev_base_three_mod_two (A077408 n)
    exact Nat.ModEq.add_left (A077408 n) m
  rw [h]
  omega


theorem power_three_mod_eight (i : ℕ) : 3^i ≡ 3^(i % 2) [MOD 8] := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rcases i with _ | _ | i
    · rfl
    · rfl
    · have h1 : 3^(i + 2) = 3^i * 9 := by ring
      have h2 : ((i + 2) % 2) = i % 2 := by omega
      rw [h1, h2]
      have h3 : 3^i * 9 ≡ 3^i * 1 [MOD 8] := Nat.ModEq.mul_left (3^i) (by rfl)
      rw [mul_one] at h3
      have h4 : 3^i ≡ 3^(i % 2) [MOD 8] := ih i (by omega)
      exact h3.trans h4

theorem power_three_add_two_mod_eight (k : ℕ) : 3^(k + 2) ≡ 3^k [MOD 8] := by
  have h1 : 3^(k + 2) = 3^k * 9 := by ring
  rw [h1]
  have h2 : 3^k * 9 ≡ 3^k * 1 [MOD 8] := Nat.ModEq.mul_left (3^k) (by rfl)
  rw [mul_one] at h2
  exact h2

theorem ofDigits_three_reverse_mod_eight (L : List ℕ) :
    ofDigits 3 L.reverse ≡ 3^(L.length - 1) * ofDigits 3 L [MOD 8] := by
  induction L with
  | nil =>
    simp [ofDigits]
    rfl
  | cons hd tl ih =>
    cases tl with
    | nil =>
      simp [ofDigits]
      rfl
    | cons hd2 tl2 =>
      have h_len : (hd :: hd2 :: tl2).length - 1 = (hd2 :: tl2).length := rfl
      rw [h_len]
      rw [ofDigits_reverse_cons]
      rw [ofDigits_cons]
      have h_rhs : 3^(hd2 :: tl2).length * (hd + 3 * ofDigits 3 (hd2 :: tl2)) =
                   3^(hd2 :: tl2).length * hd + 3^((hd2 :: tl2).length + 1) * ofDigits 3 (hd2 :: tl2) := by ring
      rw [h_rhs]
      have h_ih : ofDigits 3 (hd2 :: tl2).reverse ≡ 3^((hd2 :: tl2).length + 1) * ofDigits 3 (hd2 :: tl2) [MOD 8] := by
        have ih_inst := ih
        have h_pow : 3^((hd2 :: tl2).length - 1) ≡ 3^((hd2 :: tl2).length + 1) [MOD 8] := by
          have h_eq : (hd2 :: tl2).length + 1 = ((hd2 :: tl2).length - 1) + 2 := by
            simp [List.length_cons]
          rw [h_eq]
          exact (power_three_add_two_mod_eight ((hd2 :: tl2).length - 1)).symm
        have h_mul := Nat.ModEq.mul_right (ofDigits 3 (hd2 :: tl2)) h_pow
        exact ih_inst.trans h_mul
      have h_add := Nat.ModEq.add_right (3^(hd2 :: tl2).length * hd) h_ih
      have h_comm : 3^((hd2 :: tl2).length + 1) * ofDigits 3 (hd2 :: tl2) + 3^(hd2 :: tl2).length * hd =
                    3^(hd2 :: tl2).length * hd + 3^((hd2 :: tl2).length + 1) * ofDigits 3 (hd2 :: tl2) := by ring
      rw [h_comm] at h_add
      exact h_add

theorem power_three_mul_modEq_self_of_modEq_four (k : ℕ) (X : ℕ) (h : X ≡ 0 [MOD 4]) :
    3^k * X ≡ X [MOD 8] := by
  induction k with
  | zero =>
    have h_pow : 3^0 * X = X := by simp
    rw [h_pow]
  | succ k ih =>
    have h1 : 3^(k + 1) * X = 3 * (3^k * X) := by ring
    rw [h1]
    have h2 : 3 * (3^k * X) ≡ 3 * X [MOD 8] := Nat.ModEq.mul_left 3 ih
    have h3 : 3 * X = 2 * X + X := by ring
    have h4 : 2 * X ≡ 0 [MOD 8] := by
      have h_div : 4 ∣ X := Nat.modEq_zero_iff_dvd.mp h
      rcases h_div with ⟨m, rfl⟩
      have h_mul : 2 * (4 * m) = 8 * m := by ring
      rw [h_mul]
      exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right 8 m)
    have h5 : 2 * X + X ≡ 0 + X [MOD 8] := Nat.ModEq.add_right X h4
    rw [zero_add] at h5
    rw [← h3] at h5
    exact h2.trans h5

theorem rev_base_three_modEq_of_mod_four (x : ℕ) (h : x ≡ 0 [MOD 4]) :
    rev_base 3 x ≡ x [MOD 8] := by
  dsimp [rev_base]
  have h1 : ofDigits 3 (digits 3 x).reverse ≡ 3^((digits 3 x).length - 1) * ofDigits 3 (digits 3 x) [MOD 8] :=
    ofDigits_three_reverse_mod_eight (digits 3 x)
  have h2 : ofDigits 3 (digits 3 x) = x := ofDigits_digits 3 x
  rw [h2] at h1
  have h3 : 3^((digits 3 x).length - 1) * x ≡ x [MOD 8] :=
    power_three_mul_modEq_self_of_modEq_four ((digits 3 x).length - 1) x h
  exact h1.trans h3

theorem digits_three_103 : digits 3 103 = [1, 1, 2, 0, 1] := by
  dsimp [digits]
  rw [digitsAux_def 3 (by decide) 103 (by decide)]
  rw [digitsAux_def 3 (by decide) 34 (by decide)]
  rw [digitsAux_def 3 (by decide) 11 (by decide)]
  rw [digitsAux_def 3 (by decide) 3 (by decide)]
  rw [digitsAux_def 3 (by decide) 1 (by decide)]
  rw [digitsAux_zero]

theorem digits_103 : digits 3 103 = [1, 1, 2, 0, 1] := digits_three_103

theorem rev_base_103 : rev_base 3 103 = 127 := by
  dsimp [rev_base]
  rw [digits_103]
  rfl

theorem A077408_one : A077408 1 = 230 := by
  dsimp [A077408]
  rw [rev_base_103]

theorem digits_230 : digits 3 230 = [2, 1, 1, 2, 2] := by
  dsimp [digits]
  rw [digitsAux_def 3 (by decide) 230 (by decide)]
  rw [digitsAux_def 3 (by decide) 76 (by decide)]
  rw [digitsAux_def 3 (by decide) 25 (by decide)]
  rw [digitsAux_def 3 (by decide) 8 (by decide)]
  rw [digitsAux_def 3 (by decide) 2 (by decide)]
  rw [digitsAux_zero]

theorem rev_base_230 : rev_base 3 230 = 206 := by
  dsimp [rev_base]
  rw [digits_230]
  rfl

theorem A077408_two : A077408 2 = 436 := by
  change A077408 1 + rev_base 3 (A077408 1) = 436
  rw [A077408_one, rev_base_230]

theorem digits_436 : digits 3 436 = [1, 1, 0, 1, 2, 1] := by
  dsimp [digits]
  rw [digitsAux_def 3 (by decide) 436 (by decide)]
  rw [digitsAux_def 3 (by decide) 145 (by decide)]
  rw [digitsAux_def 3 (by decide) 48 (by decide)]
  rw [digitsAux_def 3 (by decide) 16 (by decide)]
  rw [digitsAux_def 3 (by decide) 5 (by decide)]
  rw [digitsAux_def 3 (by decide) 1 (by decide)]
  rw [digitsAux_zero]

theorem rev_base_436 : rev_base 3 436 = 340 := by
  dsimp [rev_base]
  rw [digits_436]
  rfl

theorem A077408_three : A077408 3 = 776 := by
  change A077408 2 + rev_base 3 (A077408 2) = 776
  rw [A077408_two, rev_base_436]

theorem A077408_three_mod_eight : A077408 3 ≡ 0 [MOD 8] := by
  rw [A077408_three]
  rfl

theorem A077408_mod_eight (n : ℕ) : A077408 (n + 3) ≡ 0 [MOD 8] := by
  induction n with
  | zero =>
    exact A077408_three_mod_eight
  | succ n ih =>
    have h_eq : A077408 (n + 1 + 3) = A077408 (n + 3) + rev_base 3 (A077408 (n + 3)) := rfl
    rw [h_eq]
    have h_mod4 : A077408 (n + 3) ≡ 0 [MOD 4] := by
      have h_div8 : 8 ∣ A077408 (n + 3) := Nat.modEq_zero_iff_dvd.mp ih
      have h_div4 : 4 ∣ A077408 (n + 3) := dvd_trans (by decide) h_div8
      exact Nat.modEq_zero_iff_dvd.mpr h_div4
    have h_rev := rev_base_three_modEq_of_mod_four (A077408 (n + 3)) h_mod4
    have h_sum : A077408 (n + 3) + rev_base 3 (A077408 (n + 3)) ≡ A077408 (n + 3) + A077408 (n + 3) [MOD 8] :=
      Nat.ModEq.add_left (A077408 (n + 3)) h_rev
    have h_double : A077408 (n + 3) + A077408 (n + 3) = 2 * A077408 (n + 3) := by ring
    rw [h_double] at h_sum
    have h_mul : 2 * A077408 (n + 3) ≡ 2 * 0 [MOD 8] := Nat.ModEq.mul_left 2 ih
    have h_zero : 2 * 0 = 0 := by ring
    rw [h_zero] at h_mul
    exact h_sum.trans h_mul

/--
A077408 103 is conjectured to be the smallest number such that the Reverse and Add! algorithm in base 3 does not lead to a palindrome.
The conjecture formalized here is that the trajectory of 103 under this operation in base 3 never reaches a palindrome.
-/
theorem oeis_77408_conjecture_0 : ∀ n : ℕ, ¬ (is_base_palindrome 3 (A077408 n)) := by
  intro n
  rcases n with _ | _ | _ | n
  · dsimp [is_base_palindrome, A077408, rev_base]
    rw [digits_three_103]
    decide
  · dsimp [is_base_palindrome]
    rw [A077408_one]
    rw [rev_base]
    rw [digits_230]
    decide
  · dsimp [is_base_palindrome]
    rw [A077408_two]
    rw [rev_base]
    rw [digits_436]
    decide
  · -- for n + 3, we have proved A077408 (n + 3) ≡ 0 [MOD 8]
    have h_mod8 : A077408 (n + 3) ≡ 0 [MOD 8] := A077408_mod_eight n
    sorry

