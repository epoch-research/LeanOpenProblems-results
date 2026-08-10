import FormalConjectures.Util.ProblemImports
open Nat Int Rat

/--
A275460: The rational-valued auxiliary function for the sequence, defined by the recurrence relation:
$a(n) = a(n-1) \cdot \frac{3(9n-7)(9n-5)(9n-2)}{n^2(3n-2)}$ for $n \ge 1$, with $a(0)=1$.
This recurrence is equivalent to the generating function definition.
-/
noncomputable def A275460_rational : ℕ → ℚ
  | 0 => 1
  | Nat.succ k =>
    let n : ℕ := k + 1
    let a_prev : ℚ := A275460_rational k
    let n_q : ℚ := n.cast
    -- Recurrence coefficient: 3 * (9n-7)(9n-5)(9n-2) / (n^2 * (3n-2))
    let num : ℚ := 3 * (9 * n_q - 7) * (9 * n_q - 5) * (9 * n_q - 2)
    let den : ℚ := n_q^2 * (3 * n_q - 2)
    a_prev * (num / den)

/--
A275460: G.f.: $\hphantom{}_3F_2([2/9, 4/9, 7/9], [1/3, 1], 729 x)$.
The coefficients are natural numbers, so we cast the rational result to $\mathbb{N}$.
We use the recurrence definition as it is the simplest algebraic representation of the D-finite series coefficients.
-/
@[simp] noncomputable def a (n : ℕ) : ℕ :=
  (A275460_rational n).floor.toNat

/--
oeis_275460_conjecture_0: "Other hypergeometric 'blind spots' for Christol’s conjecture" - (see Bostan link).
The necessary condition for the OEIS definition `A275460_rational n` to correspond to a sequence of natural numbers is that these rational values are always integers.
This specific conjecture states that all coefficients $a(n)$ are integers.
-/

lemma lin_dvd_iff_modEq {q r rep t : ℕ} (hg : Nat.gcd q 9 = 1) (hrep : q ∣ 9*rep + r) :
    (q ∣ 9*t + r) ↔ t ≡ rep [MOD q] := by
  constructor
  · intro ht
    have h1 : 9*t + r ≡ 0 [MOD q] := ht.modEq_zero_nat
    have h2 : 9*rep + r ≡ 0 [MOD q] := hrep.modEq_zero_nat
    have hsum : 9*t + r ≡ 9*rep + r [MOD q] := h1.trans h2.symm
    have hmul : 9*t ≡ 9*rep [MOD q] := Nat.ModEq.add_right_cancel' r hsum
    exact Nat.ModEq.cancel_left_of_coprime hg hmul
  · intro h
    have hmul : 9*t ≡ 9*rep [MOD q] := h.mul_left 9
    have hsum : 9*t + r ≡ 9*rep + r [MOD q] := hmul.add_right r
    have hzero : 9*rep + r ≡ 0 [MOD q] := hrep.modEq_zero_nat
    exact Nat.modEq_zero_iff_dvd.mp (hsum.trans hzero)

lemma sum_if_dvd_eq_count_modEq {q r rep n : ℕ} (hg : Nat.gcd q 9 = 1) (hrep : q ∣ 9*rep+r) :
    (∑ t ∈ Finset.range n, if q ∣ 9*t+r then 1 else 0) = n.count (fun t => t ≡ rep [MOD q]) := by
  rw [Nat.count_eq_card_filter_range]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : q ∣ 9*t+r
  · simp [h, (lin_dvd_iff_modEq hg hrep).mp h]
  · have h' : ¬ t ≡ rep [MOD q] := fun hm => h ((lin_dvd_iff_modEq hg hrep).mpr hm)
    simp [h, h']

lemma gcd_9m_add_9 (m c : ℕ) (hc : c.Coprime 9) : Nat.gcd (9*m+c) 9 = 1 := by
  rw [← Nat.coprime_iff_gcd_eq_one]
  have h : (c + 9*m).Coprime 9 := by
    rw [Nat.coprime_add_mul_left_left]
    exact hc
  convert h using 1
  omega

lemma div_three_decomp (n q : ℕ) (hq : 0 < q) :
    (3*n)/q = 3*(n/q) + (3*(n%q))/q := by
  have h := Nat.div_add_mod n q
  conv_lhs => rw [← h]
  rw [mul_add]
  have harr : 3 * (q * (n / q)) + 3 * (n % q) = 3 * (n % q) + q * (3 * (n / q)) := by ring
  rw [harr, Nat.add_mul_div_left _ _ hq]
  ring

lemma count_ineq_branch1 (n m : ℕ) (hm : 1 ≤ m) :
    (3*n)/(9*m+1) + n/(9*m+1) ≤
      (∑ t ∈ Finset.range n, if (9*m+1) ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+1) ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+1) ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+1) ∣ 9*t+7 then 1 else 0) := by
  let q := 9*m+1
  have hq : 0 < q := by omega
  have hg : Nat.gcd q 9 = 1 := by simpa [q] using gcd_9m_add_9 m 1 (by decide)
  have h2d : q ∣ 9*(2*m)+2 := by use 2; omega
  have h4d : q ∣ 9*(4*m)+4 := by use 4; omega
  have h6d : q ∣ 9*(6*m)+6 := by use 6; omega
  have h7d : q ∣ 9*(7*m)+7 := by use 7; omega
  rw [sum_if_dvd_eq_count_modEq hg h2d, sum_if_dvd_eq_count_modEq hg h4d,
      sum_if_dvd_eq_count_modEq hg h6d, sum_if_dvd_eq_count_modEq hg h7d]
  rw [Nat.count_modEq_card n hq (2*m), Nat.count_modEq_card n hq (4*m),
      Nat.count_modEq_card n hq (6*m), Nat.count_modEq_card n hq (7*m)]
  have h2 : (2*m) % q = 2*m := by apply Nat.mod_eq_of_lt; omega
  have h4 : (4*m) % q = 4*m := by apply Nat.mod_eq_of_lt; omega
  have h6 : (6*m) % q = 6*m := by apply Nat.mod_eq_of_lt; omega
  have h7 : (7*m) % q = 7*m := by apply Nat.mod_eq_of_lt; omega
  rw [h2,h4,h6,h7, div_three_decomp n q hq]
  have hb : n % q < q := Nat.mod_lt n hq
  suffices (3 * (n % q)) / q ≤
      (if 2 * m < n % q then 1 else 0) + (if 4 * m < n % q then 1 else 0) +
      (if 6 * m < n % q then 1 else 0) + (if 7 * m < n % q then 1 else 0) by
    dsimp [q] at *
    omega
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  split_ifs <;> dsimp [q] at * <;> omega

lemma count_ineq_branch2 (n m : ℕ) :
    (3*n)/(9*m+2) + n/(9*m+2) ≤
      (∑ t ∈ Finset.range n, if (9*m+2) ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+2) ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+2) ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+2) ∣ 9*t+7 then 1 else 0) := by

  let q := 9*m+2
  have hq : 0 < q := by omega
  have hg : Nat.gcd q 9 = 1 := by simpa [q] using gcd_9m_add_9 m 2 (by decide)
  have h2d : q ∣ 9*(m)+2 := by use 1; omega
  have h4d : q ∣ 9*(2*m)+4 := by use 2; omega
  have h6d : q ∣ 9*(3*m)+6 := by use 3; omega
  have h7d : q ∣ 9*(8*m+1)+7 := by use 8; omega
  rw [sum_if_dvd_eq_count_modEq hg h2d, sum_if_dvd_eq_count_modEq hg h4d, sum_if_dvd_eq_count_modEq hg h6d, sum_if_dvd_eq_count_modEq hg h7d]
  rw [Nat.count_modEq_card n hq (m), Nat.count_modEq_card n hq (2*m), Nat.count_modEq_card n hq (3*m), Nat.count_modEq_card n hq (8*m+1)]
  have hm0 : (m) % q = m := by apply Nat.mod_eq_of_lt; omega
  have hm1 : (2*m) % q = 2*m := by apply Nat.mod_eq_of_lt; omega
  have hm2 : (3*m) % q = 3*m := by apply Nat.mod_eq_of_lt; omega
  have hm3 : (8*m+1) % q = 8*m+1 := by apply Nat.mod_eq_of_lt; omega
  rw [hm0,hm1,hm2,hm3, div_three_decomp n q hq]
  have hb : n % q < q := Nat.mod_lt n hq
  suffices (3 * (n % q)) / q ≤
      (if m < n % q then 1 else 0) +
      (if 2*m < n % q then 1 else 0) +
      (if 3*m < n % q then 1 else 0) +
      (if 8*m+1 < n % q then 1 else 0) by

    dsimp [q] at *
    omega
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  split_ifs <;> dsimp [q] at * <;> omega

lemma count_ineq_branch4 (n m : ℕ) :
    (3*n)/(9*m+4) + n/(9*m+4) ≤
      (∑ t ∈ Finset.range n, if (9*m+4) ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+4) ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+4) ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+4) ∣ 9*t+7 then 1 else 0) := by

  let q := 9*m+4
  have hq : 0 < q := by omega
  have hg : Nat.gcd q 9 = 1 := by simpa [q] using gcd_9m_add_9 m 4 (by decide)
  have h2d : q ∣ 9*(5*m+2)+2 := by use 5; omega
  have h4d : q ∣ 9*(m)+4 := by use 1; omega
  have h6d : q ∣ 9*(6*m+2)+6 := by use 6; omega
  have h7d : q ∣ 9*(4*m+1)+7 := by use 4; omega
  rw [sum_if_dvd_eq_count_modEq hg h2d, sum_if_dvd_eq_count_modEq hg h4d, sum_if_dvd_eq_count_modEq hg h6d, sum_if_dvd_eq_count_modEq hg h7d]
  rw [Nat.count_modEq_card n hq (5*m+2), Nat.count_modEq_card n hq (m), Nat.count_modEq_card n hq (6*m+2), Nat.count_modEq_card n hq (4*m+1)]
  have hm0 : (5*m+2) % q = 5*m+2 := by apply Nat.mod_eq_of_lt; omega
  have hm1 : (m) % q = m := by apply Nat.mod_eq_of_lt; omega
  have hm2 : (6*m+2) % q = 6*m+2 := by apply Nat.mod_eq_of_lt; omega
  have hm3 : (4*m+1) % q = 4*m+1 := by apply Nat.mod_eq_of_lt; omega
  rw [hm0,hm1,hm2,hm3, div_three_decomp n q hq]
  have hb : n % q < q := Nat.mod_lt n hq
  suffices (3 * (n % q)) / q ≤
      (if 5*m+2 < n % q then 1 else 0) +
      (if m < n % q then 1 else 0) +
      (if 6*m+2 < n % q then 1 else 0) +
      (if 4*m+1 < n % q then 1 else 0) by

    dsimp [q] at *
    omega
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  split_ifs <;> dsimp [q] at * <;> omega

lemma count_ineq_branch5 (n m : ℕ) :
    (3*n)/(9*m+5) + n/(9*m+5) ≤
      (∑ t ∈ Finset.range n, if (9*m+5) ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+5) ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+5) ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+5) ∣ 9*t+7 then 1 else 0) := by

  let q := 9*m+5
  have hq : 0 < q := by omega
  have hg : Nat.gcd q 9 = 1 := by simpa [q] using gcd_9m_add_9 m 5 (by decide)
  have h2d : q ∣ 9*(4*m+2)+2 := by use 4; omega
  have h4d : q ∣ 9*(8*m+4)+4 := by use 8; omega
  have h6d : q ∣ 9*(3*m+1)+6 := by use 3; omega
  have h7d : q ∣ 9*(5*m+2)+7 := by use 5; omega
  rw [sum_if_dvd_eq_count_modEq hg h2d, sum_if_dvd_eq_count_modEq hg h4d, sum_if_dvd_eq_count_modEq hg h6d, sum_if_dvd_eq_count_modEq hg h7d]
  rw [Nat.count_modEq_card n hq (4*m+2), Nat.count_modEq_card n hq (8*m+4), Nat.count_modEq_card n hq (3*m+1), Nat.count_modEq_card n hq (5*m+2)]
  have hm0 : (4*m+2) % q = 4*m+2 := by apply Nat.mod_eq_of_lt; omega
  have hm1 : (8*m+4) % q = 8*m+4 := by apply Nat.mod_eq_of_lt; omega
  have hm2 : (3*m+1) % q = 3*m+1 := by apply Nat.mod_eq_of_lt; omega
  have hm3 : (5*m+2) % q = 5*m+2 := by apply Nat.mod_eq_of_lt; omega
  rw [hm0,hm1,hm2,hm3, div_three_decomp n q hq]
  have hb : n % q < q := Nat.mod_lt n hq
  suffices (3 * (n % q)) / q ≤
      (if 4*m+2 < n % q then 1 else 0) +
      (if 8*m+4 < n % q then 1 else 0) +
      (if 3*m+1 < n % q then 1 else 0) +
      (if 5*m+2 < n % q then 1 else 0) by

    dsimp [q] at *
    omega
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  split_ifs <;> dsimp [q] at * <;> omega

lemma count_ineq_branch7 (n m : ℕ) :
    (3*n)/(9*m+7) + n/(9*m+7) ≤
      (∑ t ∈ Finset.range n, if (9*m+7) ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+7) ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+7) ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+7) ∣ 9*t+7 then 1 else 0) := by

  let q := 9*m+7
  have hq : 0 < q := by omega
  have hg : Nat.gcd q 9 = 1 := by simpa [q] using gcd_9m_add_9 m 7 (by decide)
  have h2d : q ∣ 9*(8*m+6)+2 := by use 8; omega
  have h4d : q ∣ 9*(7*m+5)+4 := by use 7; omega
  have h6d : q ∣ 9*(6*m+4)+6 := by use 6; omega
  have h7d : q ∣ 9*(m)+7 := by use 1; omega
  rw [sum_if_dvd_eq_count_modEq hg h2d, sum_if_dvd_eq_count_modEq hg h4d, sum_if_dvd_eq_count_modEq hg h6d, sum_if_dvd_eq_count_modEq hg h7d]
  rw [Nat.count_modEq_card n hq (8*m+6), Nat.count_modEq_card n hq (7*m+5), Nat.count_modEq_card n hq (6*m+4), Nat.count_modEq_card n hq (m)]
  have hm0 : (8*m+6) % q = 8*m+6 := by apply Nat.mod_eq_of_lt; omega
  have hm1 : (7*m+5) % q = 7*m+5 := by apply Nat.mod_eq_of_lt; omega
  have hm2 : (6*m+4) % q = 6*m+4 := by apply Nat.mod_eq_of_lt; omega
  have hm3 : (m) % q = m := by apply Nat.mod_eq_of_lt; omega
  rw [hm0,hm1,hm2,hm3, div_three_decomp n q hq]
  have hb : n % q < q := Nat.mod_lt n hq
  suffices (3 * (n % q)) / q ≤
      (if 8*m+6 < n % q then 1 else 0) +
      (if 7*m+5 < n % q then 1 else 0) +
      (if 6*m+4 < n % q then 1 else 0) +
      (if m < n % q then 1 else 0) by

    dsimp [q] at *
    omega
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  split_ifs <;> dsimp [q] at * <;> omega

lemma count_ineq_branch8 (n m : ℕ) :
    (3*n)/(9*m+8) + n/(9*m+8) ≤
      (∑ t ∈ Finset.range n, if (9*m+8) ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+8) ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+8) ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if (9*m+8) ∣ 9*t+7 then 1 else 0) := by

  let q := 9*m+8
  have hq : 0 < q := by omega
  have hg : Nat.gcd q 9 = 1 := by simpa [q] using gcd_9m_add_9 m 8 (by decide)
  have h2d : q ∣ 9*(7*m+6)+2 := by use 7; omega
  have h4d : q ∣ 9*(5*m+4)+4 := by use 5; omega
  have h6d : q ∣ 9*(3*m+2)+6 := by use 3; omega
  have h7d : q ∣ 9*(2*m+1)+7 := by use 2; omega
  rw [sum_if_dvd_eq_count_modEq hg h2d, sum_if_dvd_eq_count_modEq hg h4d, sum_if_dvd_eq_count_modEq hg h6d, sum_if_dvd_eq_count_modEq hg h7d]
  rw [Nat.count_modEq_card n hq (7*m+6), Nat.count_modEq_card n hq (5*m+4), Nat.count_modEq_card n hq (3*m+2), Nat.count_modEq_card n hq (2*m+1)]
  have hm0 : (7*m+6) % q = 7*m+6 := by apply Nat.mod_eq_of_lt; omega
  have hm1 : (5*m+4) % q = 5*m+4 := by apply Nat.mod_eq_of_lt; omega
  have hm2 : (3*m+2) % q = 3*m+2 := by apply Nat.mod_eq_of_lt; omega
  have hm3 : (2*m+1) % q = 2*m+1 := by apply Nat.mod_eq_of_lt; omega
  rw [hm0,hm1,hm2,hm3, div_three_decomp n q hq]
  have hb : n % q < q := Nat.mod_lt n hq
  suffices (3 * (n % q)) / q ≤
      (if 7*m+6 < n % q then 1 else 0) +
      (if 5*m+4 < n % q then 1 else 0) +
      (if 3*m+2 < n % q then 1 else 0) +
      (if 2*m+1 < n % q then 1 else 0) by

    dsimp [q] at *
    omega
  rw [Nat.div_le_iff_le_mul_add_pred hq]
  split_ifs <;> dsimp [q] at * <;> omega


lemma count_ineq_coprime9 (n q : ℕ) (hq : 1 < q) (hg : Nat.gcd q 9 = 1) :
    (3*n)/q + n/q ≤
      (∑ t ∈ Finset.range n, if q ∣ 9*t+2 then 1 else 0) +
      (∑ t ∈ Finset.range n, if q ∣ 9*t+4 then 1 else 0) +
      (∑ t ∈ Finset.range n, if q ∣ 9*t+6 then 1 else 0) +
      (∑ t ∈ Finset.range n, if q ∣ 9*t+7 then 1 else 0) := by
  let m := q / 9
  have hdivmod : q = 9*m + q % 9 := by
    dsimp [m]
    rw [Nat.div_add_mod]
  have hrem_lt : q % 9 < 9 := Nat.mod_lt q (by norm_num)
  have hrem_cases : q % 9 = 0 ∨ q % 9 = 1 ∨ q % 9 = 2 ∨ q % 9 = 3 ∨ q % 9 = 4 ∨ q % 9 = 5 ∨ q % 9 = 6 ∨ q % 9 = 7 ∨ q % 9 = 8 := by omega
  rcases hrem_cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · have hq3 : q % 3 = 0 := by omega
    have hdvd : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hq3
    have hgdvd : 3 ∣ Nat.gcd q 9 := Nat.dvd_gcd hdvd (by decide)
    rw [hg] at hgdvd
    norm_num at hgdvd
  · have hqeq : q = 9*m + 1 := by omega
    have hm : 1 ≤ m := by omega
    simpa [hqeq] using count_ineq_branch1 n m hm
  · have hqeq : q = 9*m + 2 := by omega
    simpa [hqeq] using count_ineq_branch2 n m
  · have hq3 : q % 3 = 0 := by omega
    have hdvd : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hq3
    have hgdvd : 3 ∣ Nat.gcd q 9 := Nat.dvd_gcd hdvd (by decide)
    rw [hg] at hgdvd
    norm_num at hgdvd
  · have hqeq : q = 9*m + 4 := by omega
    simpa [hqeq] using count_ineq_branch4 n m
  · have hqeq : q = 9*m + 5 := by omega
    simpa [hqeq] using count_ineq_branch5 n m
  · have hq3 : q % 3 = 0 := by omega
    have hdvd : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.mpr hq3
    have hgdvd : 3 ∣ Nat.gcd q 9 := Nat.dvd_gcd hdvd (by decide)
    rw [hg] at hgdvd
    norm_num at hgdvd
  · have hqeq : q = 9*m + 7 := by omega
    simpa [hqeq] using count_ineq_branch7 n m
  · have hqeq : q = 9*m + 8 := by omega
    simpa [hqeq] using count_ineq_branch8 n m

-- Divisibility development

def CTerm (t : ℕ) : ℕ := (9*t+2)*(9*t+4)*(9*t+6)*(9*t+7)
def P4 (n : ℕ) : ℕ := ∏ t ∈ Finset.range n, CTerm t
def CNum (n : ℕ) : ℕ := 3^n * P4 n
def CDen (n : ℕ) : ℕ := (3*n)! * Nat.factorial n

lemma CTerm_pos (t : ℕ) : 0 < CTerm t := by
  unfold CTerm
  positivity

lemma P4_pos (n : ℕ) : 0 < P4 n := by
  unfold P4
  exact Finset.prod_pos (by intro t ht; exact CTerm_pos t)

lemma CNum_pos (n : ℕ) : 0 < CNum n := by
  unfold CNum
  exact mul_pos (pow_pos (by norm_num) n) (P4_pos n)

lemma CDen_pos (n : ℕ) : 0 < CDen n := by
  unfold CDen
  exact mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)






lemma factorization_eq_sum_indicators_of_lt {p x B : ℕ} (hp : Nat.Prime p) (hx : 0 < x) (hB : x < p^B) :
    x.factorization p = ∑ i ∈ Finset.Ico 1 B, if p^i ∣ x then 1 else 0 := by
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hx hB]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma CTerm_factorization_eq_sum (p B t : ℕ) (hp : Nat.Prime p)
    (h2 : 9*t+2 < p^B) (h4 : 9*t+4 < p^B) (h6 : 9*t+6 < p^B) (h7 : 9*t+7 < p^B) :
    (CTerm t).factorization p =
      ∑ i ∈ Finset.Ico 1 B,
        ((if p^i ∣ 9*t+2 then 1 else 0) + (if p^i ∣ 9*t+4 then 1 else 0) +
         (if p^i ∣ 9*t+6 then 1 else 0) + (if p^i ∣ 9*t+7 then 1 else 0)) := by
  unfold CTerm
  rw [Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul]
  · simp only [Finsupp.add_apply]
    rw [factorization_eq_sum_indicators_of_lt hp (by omega : 0 < 9*t+2) h2]
    rw [factorization_eq_sum_indicators_of_lt hp (by omega : 0 < 9*t+4) h4]
    rw [factorization_eq_sum_indicators_of_lt hp (by omega : 0 < 9*t+6) h6]
    rw [factorization_eq_sum_indicators_of_lt hp (by omega : 0 < 9*t+7) h7]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  all_goals positivity

lemma lin_lt_prime_pow_bound {p n t c : ℕ} (hp : Nat.Prime p) (ht : t ∈ Finset.range n) (hc : c ≤ 7) :
    9*t + c < p ^ ((9*n+8)^4) := by
  have htlt : t < n := by simpa using ht
  have hlin : 9*t + c < 9*n + 8 := by omega
  let B := (9*n+8)^4
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hbase_le_B : 9*n + 8 ≤ B := by
    dsimp [B]
    simpa using (Nat.pow_le_pow_right (by omega : 9*n+8 > 0) (by norm_num : (1:ℕ) ≤ 4))
  have hltB : 9*t + c < B := lt_of_lt_of_le hlin hbase_le_B
  have hBlt2 : B < 2^B := @Nat.lt_two_pow_self B
  have h2lep : 2 ≤ p := hp.two_le
  have h2pow : 2^B ≤ p^B := Nat.pow_le_pow_left h2lep B
  exact lt_of_lt_of_le (lt_trans hltB hBlt2) h2pow

lemma P4_factorization_eq_sum (p n : ℕ) (hp : Nat.Prime p) :
    (P4 n).factorization p =
      ∑ i ∈ Finset.Ico 1 ((9*n+8)^4),
        ∑ t ∈ Finset.range n,
          ((if p^i ∣ 9*t+2 then 1 else 0) + (if p^i ∣ 9*t+4 then 1 else 0) +
           (if p^i ∣ 9*t+6 then 1 else 0) + (if p^i ∣ 9*t+7 then 1 else 0)) := by
  unfold P4
  rw [Nat.factorization_prod_apply]
  · trans ∑ t ∈ Finset.range n,
        ∑ i ∈ Finset.Ico 1 ((9*n+8)^4),
          ((if p^i ∣ 9*t+2 then 1 else 0) + (if p^i ∣ 9*t+4 then 1 else 0) +
           (if p^i ∣ 9*t+6 then 1 else 0) + (if p^i ∣ 9*t+7 then 1 else 0))
    · apply Finset.sum_congr rfl
      intro t ht
      apply CTerm_factorization_eq_sum p ((9*n+8)^4) t hp
      · exact lin_lt_prime_pow_bound hp ht (by omega : 2 ≤ 7)
      · exact lin_lt_prime_pow_bound hp ht (by omega : 4 ≤ 7)
      · exact lin_lt_prime_pow_bound hp ht (by omega : 6 ≤ 7)
      · exact lin_lt_prime_pow_bound hp ht (by omega : 7 ≤ 7)
    · exact Finset.sum_comm
  · intro t ht
    exact (CTerm_pos t).ne'

lemma small_lt_prime_pow_bound {p n x : ℕ} (hp : Nat.Prime p) (hx : x < 9*n+8) :
    x < p ^ ((9*n+8)^4) := by
  let B := (9*n+8)^4
  have hbase_le_B : 9*n + 8 ≤ B := by
    dsimp [B]
    simpa using (Nat.pow_le_pow_right (by omega : 9*n+8 > 0) (by norm_num : (1:ℕ) ≤ 4))
  have hltB : x < B := lt_of_lt_of_le hx hbase_le_B
  have hBlt2 : B < 2^B := @Nat.lt_two_pow_self B
  have h2pow : 2^B ≤ p^B := Nat.pow_le_pow_left hp.two_le B
  exact lt_of_lt_of_le (lt_trans hltB hBlt2) h2pow


lemma log_3n_lt_bound (p n : ℕ) (hp : Nat.Prime p) : Nat.log p (3*n) < (9*n+8)^4 := by
  apply Nat.log_lt_of_lt_pow'
  · positivity
  · exact small_lt_prime_pow_bound hp (by omega : 3*n < 9*n+8)

lemma log_n_lt_bound (p n : ℕ) (hp : Nat.Prime p) : Nat.log p n < (9*n+8)^4 := by
  apply Nat.log_lt_of_lt_pow'
  · positivity
  · exact small_lt_prime_pow_bound hp (by omega : n < 9*n+8)

lemma prime_pow_coprime9 {p i : ℕ} (hp : Nat.Prime p) (hp3 : p ≠ 3) : Nat.gcd (p^i) 9 = 1 := by
  rw [← Nat.coprime_iff_gcd_eq_one]
  apply Nat.Coprime.pow_left
  rw [hp.coprime_iff_not_dvd]
  intro h
  have h9 : 9 = 3^2 := by norm_num
  rw [h9] at h
  have hp_dvd3 : p ∣ 3 := hp.dvd_of_dvd_pow h
  have heq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hp_dvd3
  exact hp3 heq

lemma P4_factorization_ge_factorials_ne3 (n p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    ((3*n)!).factorization p + (Nat.factorial n).factorization p ≤ (P4 n).factorization p := by
  rw [Nat.factorization_factorial hp (log_3n_lt_bound p n hp)]
  rw [Nat.factorization_factorial hp (log_n_lt_bound p n hp)]
  rw [P4_factorization_eq_sum p n hp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hq : 1 < p^i := by
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact one_lt_pow₀ hp.one_lt (by omega : i ≠ 0)
  have hg : Nat.gcd (p^i) 9 = 1 := prime_pow_coprime9 hp hp3
  have h := count_ineq_coprime9 n (p^i) hq hg
  simpa [Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using h

lemma CTerm_factorization_three_ge_one (t : ℕ) : 1 ≤ (CTerm t).factorization 3 := by
  unfold CTerm
  rw [Nat.factorization_mul, Nat.factorization_mul, Nat.factorization_mul]
  · simp only [Finsupp.add_apply]
    have hdiv : 3 ∣ 9*t+6 := by use 3*t+2; omega
    have hpos : 0 < (9*t+6).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd (by decide : Nat.Prime 3) (by omega) hdiv
    omega
  all_goals positivity

lemma P4_factorization_three_ge (n : ℕ) : n ≤ (P4 n).factorization 3 := by
  unfold P4
  rw [Nat.factorization_prod_apply]
  · calc
      n = ∑ t ∈ Finset.range n, 1 := by simp
      _ ≤ ∑ t ∈ Finset.range n, (CTerm t).factorization 3 := by
        apply Finset.sum_le_sum
        intro t ht
        exact CTerm_factorization_three_ge_one t
  · intro t ht
    exact (CTerm_pos t).ne'


lemma CDen_factorization_le_CNum_three (n : ℕ) : (CDen n).factorization 3 ≤ (CNum n).factorization 3 := by
  unfold CDen CNum
  rw [Nat.factorization_mul, Nat.factorization_mul]
  · simp only [Finsupp.add_apply]
    rw [Nat.factorization_factorial_mul (by decide : Nat.Prime 3)]
    rw [Nat.factorization_pow, Finsupp.nsmul_apply, Nat.Prime.factorization_self (by decide : Nat.Prime 3)]
    simp only [nsmul_eq_mul, mul_one]
    have hfac := Nat.factorization_factorial_le_div_pred (by decide : Nat.Prime 3) n
    norm_num at hfac
    have hP := P4_factorization_three_ge n
    let f := (Nat.factorial n).factorization 3
    let P := (P4 n).factorization 3
    have h2f : 2 * f ≤ n := by
      dsimp [f]
      omega
    have hgoal : f + n + f ≤ n + P := by
      dsimp [f, P]
      omega
    simpa [f, P, two_mul, add_assoc, add_comm, add_left_comm] using hgoal
  all_goals
    first
    | exact (Nat.factorial_pos _).ne'
    | exact (pow_pos (by norm_num : 0 < 3) n).ne'
    | exact (P4_pos n).ne'


lemma CDen_factorization_le_CNum_ne_three (n p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3) :
    (CDen n).factorization p ≤ (CNum n).factorization p := by
  unfold CDen CNum
  rw [Nat.factorization_mul, Nat.factorization_mul]
  · simp only [Finsupp.add_apply]
    rw [Nat.factorization_pow, Finsupp.nsmul_apply]
    have hnot : ¬ p ∣ 3 := by
      intro h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h)
    rw [Nat.factorization_eq_zero_of_not_dvd hnot]
    simp
    exact P4_factorization_ge_factorials_ne3 n p hp hp3
  all_goals
    first
    | exact (Nat.factorial_pos _).ne'
    | exact (pow_pos (by norm_num : 0 < 3) n).ne'
    | exact (P4_pos n).ne'

lemma CDen_dvd_CNum (n : ℕ) : CDen n ∣ CNum n := by
  rw [← Nat.factorization_le_iff_dvd (CDen_pos n).ne' (CNum_pos n).ne']
  intro p
  by_cases hp : Nat.Prime p
  · by_cases h3 : p = 3
    · subst p
      exact CDen_factorization_le_CNum_three n
    · exact CDen_factorization_le_CNum_ne_three n p hp h3
  · have hzero : (CDen n).factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      exact Or.inl hp
    rw [hzero]
    exact Nat.zero_le _

lemma CDen_succ (k : ℕ) : CDen (k+1) = CDen k * ((3*k+1)*(3*k+2)*(3*k+3)*(k+1)) := by
  unfold CDen
  have h : 3 * (k + 1) = 3*k + 3 := by omega
  rw [h]
  conv_lhs => rw [show 3*k+3 = (3*k+2)+1 by omega, Nat.factorial_succ]
  conv_lhs => rw [show 3*k+2 = (3*k+1)+1 by omega, Nat.factorial_succ]
  conv_lhs => rw [show 3*k+1 = (3*k)+1 by omega, Nat.factorial_succ]
  rw [Nat.factorial_succ]
  ring

lemma CNum_succ (k : ℕ) : CNum (k+1) = CNum k * (3 * CTerm k) := by
  unfold CNum P4
  rw [pow_succ]
  rw [Finset.prod_range_succ]
  ring

lemma A_closed_range (n : ℕ) : A275460_rational n = (CNum n : ℚ) / (CDen n : ℚ) := by
  induction n with
  | zero => norm_num [A275460_rational, CNum, P4, CDen]
  | succ k ih =>
    rw [A275460_rational, ih]
    rw [CNum_succ, CDen_succ]
    have hCDen_pos : 0 < CDen k := by unfold CDen; positivity
    have hfac_pos : 0 < (3*k+1)*(3*k+2)*(3*k+3)*(k+1) := by positivity
    have hden : ((CDen k : ℚ) * (((3*k+1)*(3*k+2)*(3*k+3)*(k+1) : ℕ) : ℚ)) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hCDen_pos.ne') (by exact_mod_cast hfac_pos.ne')
    have hk1 : ((k+1:ℕ):ℚ) ≠ 0 := by positivity
    have hlin_pos : 0 < 3 * ((k+1:ℕ):ℚ) - 2 := by
      norm_num
      have hk_nonneg : (0 : ℚ) ≤ k := by exact_mod_cast Nat.zero_le k
      linarith
    have hlin : (3 * ((k+1:ℕ):ℚ) - 2) ≠ 0 := hlin_pos.ne'
    have hc2 : (((9*k+2 : ℕ) : ℚ)) = 9*(k:ℚ)+2 := by norm_num [Nat.cast_add, Nat.cast_mul]
    have hc4 : (((9*k+4 : ℕ) : ℚ)) = 9*(k:ℚ)+4 := by norm_num [Nat.cast_add, Nat.cast_mul]
    have hc6 : (((9*k+6 : ℕ) : ℚ)) = 9*(k:ℚ)+6 := by norm_num [Nat.cast_add, Nat.cast_mul]
    have hc7 : (((9*k+7 : ℕ) : ℚ)) = 9*(k:ℚ)+7 := by norm_num [Nat.cast_add, Nat.cast_mul]
    unfold CTerm
    field_simp [hden, hk1, hlin]
    norm_num [Nat.cast_mul, Nat.cast_add, pow_two]
    ring_nf


lemma rat_isInt_of_nat_dvd {N D : ℕ} (hD : D ≠ 0) (h : D ∣ N) : (((N : ℚ) / (D : ℚ)).isInt) := by
  rcases h with ⟨k, rfl⟩
  rw [Nat.cast_mul]
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  rw [mul_comm (D : ℚ) (k : ℚ), mul_div_cancel_right₀ _ hDq]
  rw [Rat.isInt]
  simp


theorem A275460_is_integral (n : ℕ) : (A275460_rational n).isInt := by
  rw [A_closed_range]
  apply rat_isInt_of_nat_dvd
  · exact (CDen_pos n).ne'
  · exact CDen_dvd_CNum n
