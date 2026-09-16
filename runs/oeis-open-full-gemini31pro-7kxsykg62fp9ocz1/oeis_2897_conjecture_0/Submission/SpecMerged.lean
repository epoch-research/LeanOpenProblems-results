import FormalConjectures.Util.ProblemImports
open Finset Nat MvPolynomial Finsupp


def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3
abbrev Vars := Fin 3
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)
local notation "P" => MvPolynomial Vars ℤ
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n


lemma drop_filter_sum (n j : ℕ) :
  ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v ) =
  ∑ v ∈ range (2 * j + 1),
    ( (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v ) := by
  apply sum_subset
  · apply filter_subset
  · intro v hv hv_not
    have hn : n < v := by
      simp only [mem_filter, not_and] at hv_not
      have h1 := hv_not hv
      omega
    have h_zero : n.choose v = 0 := choose_eq_zero_of_lt hn
    rw [h_zero]
    simp


lemma trinomial (A X Y : ℕ) :
  A.choose X * (A - X).choose Y = A.choose Y * (A - Y).choose X := by
  by_cases h : X + Y ≤ A
  · have ht1 : A.choose (X + Y) * (X + Y).choose X = A.choose X * (A - X).choose (X + Y - X) := choose_mul (by omega)
    have hX : X + Y - X = Y := by omega
    rw [hX] at ht1
    have ht2 : A.choose (Y + X) * (Y + X).choose Y = A.choose Y * (A - Y).choose (Y + X - Y) := choose_mul (by omega)
    have hY : Y + X - Y = X := by omega
    rw [hY] at ht2
    have hc : X + Y = Y + X := by omega
    rw [hc] at ht1
    have hs : (Y + X).choose X = (Y + X).choose Y := by
      have h_symm := choose_symm (n := Y + X) (k := X) (by omega)
      have h_sub : Y + X - X = Y := by omega
      rw [h_sub] at h_symm
      exact h_symm.symm
    rw [hs] at ht1
    rw [← ht1, ← ht2]
  · by_cases hX : X ≤ A
    · have hnX : A - X < Y := by omega
      have ht1 : (A - X).choose Y = 0 := choose_eq_zero_of_lt hnX
      rw [ht1, mul_zero]
      by_cases hY : Y ≤ A
      · have hnY : A - Y < X := by omega
        have ht2 : (A - Y).choose X = 0 := choose_eq_zero_of_lt hnY
        rw [ht2, mul_zero]
      · have ht2 : A.choose Y = 0 := choose_eq_zero_of_lt (by omega)
        rw [ht2, zero_mul]
    · have ht1 : A.choose X = 0 := choose_eq_zero_of_lt (by omega)
      rw [ht1, zero_mul]
      by_cases hY : Y ≤ A
      · have hnY : A - Y < X := by omega
        have ht2 : (A - Y).choose X = 0 := choose_eq_zero_of_lt hnY
        rw [ht2, mul_zero]
      · have ht2 : A.choose Y = 0 := choose_eq_zero_of_lt (by omega)
        rw [ht2, zero_mul]

lemma binom_id (n j k : ℕ) (h1 : k ≤ 2*j) (h4 : k ≤ n) :
  (2*n).choose (2*j) * (2*n - 2*j).choose (n - k) * (2*j).choose k =
  (2*n).choose n * n.choose k * n.choose (2*j - k) := by
  have step1 : (2*n).choose (2*j) * (2*j).choose k = (2*n).choose k * (2*n - k).choose (2*j - k) := choose_mul h1
  have LHS_eq : (2*n).choose (2*j) * (2*n - 2*j).choose (n - k) * (2*j).choose k =
                (2*n).choose k * (2*n - k).choose (2*j - k) * (2*n - 2*j).choose (n - k) := by
    calc (2*n).choose (2*j) * (2*n - 2*j).choose (n - k) * (2*j).choose k
      _ = (2*n).choose (2*j) * (2*j).choose k * (2*n - 2*j).choose (n - k) := by ring
      _ = (2*n).choose k * (2*n - k).choose (2*j - k) * (2*n - 2*j).choose (n - k) := by rw [step1]
  rw [LHS_eq]
  have step2 : (2*n - k).choose (2*j - k) * (2*n - 2*j).choose (n - k) = (2*n - k).choose (n - k) * n.choose (2*j - k) := by
    have ht := trinomial (2*n - k) (2*j - k) (n - k)
    by_cases hj : 2*n - k ≥ 2*j - k
    · have h_sub : 2*n - k - (2*j - k) = 2*n - 2*j := by omega
      rw [h_sub] at ht
      by_cases hk : 2*n - k ≥ n - k
      · have h_sub2 : 2*n - k - (n - k) = n := by omega
        rw [h_sub2] at ht
        exact ht
      · have h_sub2 : 2*n - k < n - k := by omega
        exfalso
        omega
    · have hj2 : 2*n - k < 2*j - k := by omega
      have ht1 : (2*n - k).choose (2*j - k) = 0 := choose_eq_zero_of_lt hj2
      have ht2 : (2*n - k).choose (n - k) * n.choose (2*j - k) = 0 := by
        have hn : n < 2*j - k := by omega
        have hn2 : n.choose (2*j - k) = 0 := choose_eq_zero_of_lt hn
        rw [hn2, mul_zero]
      rw [ht1, zero_mul, ht2]
  have LHS_eq2 : (2*n).choose k * (2*n - k).choose (2*j - k) * (2*n - 2*j).choose (n - k) =
                 (2*n).choose k * (2*n - k).choose (n - k) * n.choose (2*j - k) := by
    calc (2*n).choose k * (2*n - k).choose (2*j - k) * (2*n - 2*j).choose (n - k)
      _ = (2*n).choose k * ((2*n - k).choose (2*j - k) * (2*n - 2*j).choose (n - k)) := by ring
      _ = (2*n).choose k * ((2*n - k).choose (n - k) * n.choose (2*j - k)) := by rw [step2]
      _ = (2*n).choose k * (2*n - k).choose (n - k) * n.choose (2*j - k) := by ring
  rw [LHS_eq2]
  have step3 : (2*n).choose n * n.choose k = (2*n).choose k * (2*n - k).choose (n - k) := by
    have ht := choose_mul (n := 2*n) (k := n) (s := k) h4
    rw [ht]
  calc (2 * n).choose k * (2 * n - k).choose (n - k) * n.choose (2 * j - k)
    _ = ((2 * n).choose k * (2 * n - k).choose (n - k)) * n.choose (2 * j - k) := by ring
    _ = ((2 * n).choose n * n.choose k) * n.choose (2 * j - k) := by rw [← step3]
    _ = (2 * n).choose n * n.choose k * n.choose (2 * j - k) := by ring

def my_small_sum2 (n : ℕ) : ℤ :=
  ∑ j ∈ range (n + 1), ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( ((2 * n).choose (2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
    ( ((2 * n).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ v )

lemma small_sum2_simplified (n : ℕ) : my_small_sum2 n =
  ∑ j ∈ range (n + 1), ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ) := by
  unfold my_small_sum2
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro v hv
  have hj_mem := mem_range.1 hj
  have hv_mem_range := mem_filter.1 hv
  have hv_le_2j := mem_range.1 hv_mem_range.1
  have hv_le_n := hv_mem_range.2
  have h_binom := binom_id n j v (by omega) (by omega)
  have hc : (((2 * n).choose (2 * j) : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ)) =
            (((2 * n).choose n : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ)) := by
    exact_mod_cast h_binom
  calc (((2 * n).choose (2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
        (((2 * n).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ v)
    _ = (((2 * n).choose (2 * j) : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ)) *
        ((2 * n).choose n : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j * (-1 : ℤ) ^ v := by ring
    _ = (((2 * n).choose n : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ)) *
        ((2 * n).choose n : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j * (-1 : ℤ) ^ v := by rw [hc]
    _ = ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) := by
      rw [pow_add]
      ring


lemma coeff_one_sub_X_pow (n v : ℕ) :
  coeff ((1 - X : ℤ[X]) ^ n) v = (-1 : ℤ) ^ v * (n.choose v : ℤ) := by
  have h_sub : (1 - X : ℤ[X]) = - X + 1 := by ring
  rw [h_sub]
  have h := add_pow (- X : ℤ[X]) 1 n
  rw [h]
  simp only [one_pow, mul_one]
  rw [finset_sum_coeff]
  have h_term : ∀ m, coeff ((- X : ℤ[X]) ^ m * (n.choose m : ℤ[X])) v = if m = v then ((-1 : ℤ) ^ m * (n.choose m : ℤ)) else 0 := by
    intro m
    have hc : (- X : ℤ[X]) ^ m * (n.choose m : ℤ[X]) = C ((-1 : ℤ) ^ m * (n.choose m : ℤ)) * (X : ℤ[X]) ^ m := by
      calc (- X : ℤ[X]) ^ m * (n.choose m : ℤ[X]) = (-1 * X : ℤ[X]) ^ m * (n.choose m : ℤ[X]) := by ring_nf
        _ = (-1 : ℤ[X]) ^ m * (X : ℤ[X]) ^ m * (n.choose m : ℤ[X]) := by rw [mul_pow]
        _ = C ((-1 : ℤ) ^ m) * (X : ℤ[X]) ^ m * C (n.choose m : ℤ) := by
          have h1 : (-1 : ℤ[X]) = C (-1 : ℤ) := by simp
          have h2 : (n.choose m : ℤ[X]) = C (n.choose m : ℤ) := by rfl
          rw [h1, h2, map_pow]
        _ = C ((-1 : ℤ) ^ m * (n.choose m : ℤ)) * (X : ℤ[X]) ^ m := by
          rw [map_mul]
          ring
    rw [hc]
    rw [coeff_C_mul_X_pow]
    by_cases hm : m = v
    · subst hm
      rfl
    · have h_not : ¬ v = m := by intro contra; exact hm contra.symm
      rw [if_neg hm, if_neg h_not]
  have h_sum : ∑ m ∈ range (n + 1), coeff ((- X : ℤ[X]) ^ m * (n.choose m : ℤ[X])) v = ∑ m ∈ range (n + 1), (if m = v then ((-1 : ℤ) ^ m * (n.choose m : ℤ)) else 0) := sum_congr rfl (fun m _ => h_term m)
  rw [h_sum]
  rw [sum_ite_eq']
  by_cases hv : v ∈ range (n + 1)
  · rw [if_pos hv]
  · rw [if_neg hv]
    have hn : n < v := by
      have h1 := mem_range.not.1 hv
      omega
    have h_zero : n.choose v = 0 := choose_eq_zero_of_lt hn
    rw [h_zero]
    simp

lemma inner_sum_eval (n j : ℕ) :
  ∑ v ∈ range (2 * j + 1), ( (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v ) =
  (n.choose j : ℤ) * (-1 : ℤ) ^ j := by
  have h_poly : (1 - X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n = (1 - X ^ 2) ^ n := by
    calc (1 - X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n = ((1 - X) * (1 + X)) ^ n := (mul_pow (1 - X : ℤ[X]) (1 + X) n).symm
      _ = (1 - X ^ 2) ^ n := by ring_nf
  have LHS : coeff ((1 - X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n) (2 * j) =
             ∑ v ∈ range (2 * j + 1), ( (-1 : ℤ) ^ v * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) ) := by
    rw [coeff_mul]
    have h_sum : ∑ x ∈ antidiagonal (2 * j), coeff ((1 - X : ℤ[X]) ^ n) x.1 * coeff ((1 + X : ℤ[X]) ^ n) x.2 =
                 ∑ v ∈ range (2 * j + 1), coeff ((1 - X : ℤ[X]) ^ n) v * coeff ((1 + X : ℤ[X]) ^ n) (2 * j - v) := by
      exact sum_antidiagonal_eq_sum_range_succ (fun k l => coeff ((1 - X : ℤ[X]) ^ n) k * coeff ((1 + X : ℤ[X]) ^ n) l) (2 * j)
    rw [h_sum]
    apply sum_congr rfl
    intro v _
    have h1 : coeff ((1 - X : ℤ[X]) ^ n) v = (-1 : ℤ) ^ v * (n.choose v : ℤ) := coeff_one_sub_X_pow n v
    have h2 : coeff ((1 + X : ℤ[X]) ^ n) (2 * j - v) = (n.choose (2 * j - v) : ℤ) := Polynomial.coeff_one_add_X_pow ℤ n (2 * j - v)
    rw [h1, h2]
  have RHS : coeff ((1 - X ^ 2 : ℤ[X]) ^ n) (2 * j) = (-1 : ℤ) ^ j * (n.choose j : ℤ) := by
    have h_sub : (1 - X ^ 2 : ℤ[X]) = - X ^ 2 + 1 := by ring
    rw [h_sub]
    have h_pow := add_pow (- X ^ 2 : ℤ[X]) 1 n
    rw [h_pow]
    simp only [one_pow, mul_one]
    rw [finset_sum_coeff]
    have h_term : ∀ m, coeff ((- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X])) (2 * j) = if m = j then ((-1 : ℤ) ^ m * (n.choose m : ℤ)) else 0 := by
      intro m
      have hc : (- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) = C ((-1 : ℤ) ^ m * (n.choose m : ℤ)) * (X : ℤ[X]) ^ (2 * m) := by
        calc (- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) = (-1 * X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) := by ring_nf
          _ = (-1 : ℤ[X]) ^ m * (X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X]) := by rw [mul_pow]
          _ = C ((-1 : ℤ) ^ m) * (X : ℤ[X]) ^ (2 * m) * C (n.choose m : ℤ) := by
            have h1 : (-1 : ℤ[X]) = C (-1 : ℤ) := by simp
            have h2 : (n.choose m : ℤ[X]) = C (n.choose m : ℤ) := by rfl
            have h3 : (X ^ 2 : ℤ[X]) ^ m = (X : ℤ[X]) ^ (2 * m) := by rw [← pow_mul]
            rw [h1, h2, map_pow, h3]
          _ = C ((-1 : ℤ) ^ m * (n.choose m : ℤ)) * (X : ℤ[X]) ^ (2 * m) := by
            rw [map_mul]
            ring
      rw [hc, coeff_C_mul_X_pow]
      by_cases hm : m = j
      · subst hm
        rw [if_pos rfl, if_pos rfl]
      · have h_not : ¬ 2 * j = 2 * m := by intro contra; exact hm (by omega)
        rw [if_neg hm, if_neg h_not]
    have h_sum : ∑ m ∈ range (n + 1), coeff ((- X ^ 2 : ℤ[X]) ^ m * (n.choose m : ℤ[X])) (2 * j) = ∑ m ∈ range (n + 1), (if m = j then ((-1 : ℤ) ^ m * (n.choose m : ℤ)) else 0) := sum_congr rfl (fun m _ => h_term m)
    rw [h_sum, sum_ite_eq']
    by_cases hj : j ∈ range (n + 1)
    · rw [if_pos hj]
    · rw [if_neg hj]
      have hn : n < j := by have h1 := mem_range.not.1 hj; omega
      have h_zero : n.choose j = 0 := choose_eq_zero_of_lt hn
      rw [h_zero]
      simp
  have h_eq : ∑ v ∈ range (2 * j + 1), (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v =
              ∑ v ∈ range (2 * j + 1), (-1 : ℤ) ^ v * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) := by
    apply sum_congr rfl
    intro v _
    ring
  rw [h_eq, ← LHS, h_poly, RHS]
  ring


lemma sum_choose_square (n : ℕ) :
  ∑ j ∈ range (n + 1), (n.choose j : ℤ) ^ 2 = ((2 * n).choose n : ℤ) := by
  have h_poly : (1 + X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n = (1 + X) ^ (2 * n) := by
    rw [← pow_add]
    have h2 : n + n = 2 * n := by omega
    rw [h2]
  have LHS : coeff ((1 + X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n) n =
             ∑ j ∈ range (n + 1), (n.choose j : ℤ) ^ 2 := by
    rw [coeff_mul]
    have h_sum : ∑ x ∈ antidiagonal n, coeff ((1 + X : ℤ[X]) ^ n) x.1 * coeff ((1 + X : ℤ[X]) ^ n) x.2 =
                 ∑ j ∈ range (n + 1), coeff ((1 + X : ℤ[X]) ^ n) j * coeff ((1 + X : ℤ[X]) ^ n) (n - j) := by
      exact sum_antidiagonal_eq_sum_range_succ (fun k l => coeff ((1 + X : ℤ[X]) ^ n) k * coeff ((1 + X : ℤ[X]) ^ n) l) n
    rw [h_sum]
    apply sum_congr rfl
    intro j hj
    have h1 : coeff ((1 + X : ℤ[X]) ^ n) j = (n.choose j : ℤ) := Polynomial.coeff_one_add_X_pow ℤ n j
    have h2 : coeff ((1 + X : ℤ[X]) ^ n) (n - j) = (n.choose (n - j) : ℤ) := Polynomial.coeff_one_add_X_pow ℤ n (n - j)
    rw [h1, h2]
    have hj_le : j ≤ n := by
      have h1 := mem_range.1 hj
      omega
    have h_symm : n.choose (n - j) = n.choose j := choose_symm hj_le
    rw [h_symm]
    ring
  have RHS : coeff ((1 + X : ℤ[X]) ^ (2 * n)) n = ((2 * n).choose n : ℤ) := by
    exact Polynomial.coeff_one_add_X_pow ℤ (2 * n) n
  rw [← LHS, h_poly, RHS]


lemma comm_ring_id {R : Type*} [CommRing R] (A B C : R) (n : ℕ) :
  (A + B) ^ (2 * n) * (A + C) ^ n * (A - C) ^ n =
  ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
    ( ( (2 * n).choose i : R) * (n.choose j : R) * (-1 : R) ^ j ) *
    ( A ^ (4 * n - i - 2 * j) * B ^ i * C ^ (2 * j) ) := by
  have h1 : (A + C) ^ n * (A - C) ^ n = (A ^ 2 - C ^ 2) ^ n := by
    calc (A + C) ^ n * (A - C) ^ n = ((A + C) * (A - C)) ^ n := (mul_pow (A + C) (A - C) n).symm
      _ = (A ^ 2 - C ^ 2) ^ n := by ring_nf
  have h2 : (A ^ 2 - C ^ 2) ^ n = ∑ j ∈ range (n + 1), (- C ^ 2) ^ j * (A ^ 2) ^ (n - j) * (n.choose j : R) := by
    have h_sub : A^2 - C^2 = -C^2 + A^2 := by ring
    rw [h_sub]
    exact add_pow (-C^2) (A^2) n
  have h3 : (A + B) ^ (2 * n) = ∑ i ∈ range (2 * n + 1), B ^ i * A ^ (2 * n - i) * ((2 * n).choose i : R) := by
    have h_sub : A + B = B + A := by ring
    rw [h_sub]
    exact add_pow B A (2 * n)
  calc (A + B) ^ (2 * n) * (A + C) ^ n * (A - C) ^ n
    _ = (A + B) ^ (2 * n) * ((A + C) ^ n * (A - C) ^ n) := by ring
    _ = (∑ i ∈ range (2 * n + 1), B ^ i * A ^ (2 * n - i) * ((2 * n).choose i : R)) *
        (∑ j ∈ range (n + 1), (- C ^ 2) ^ j * (A ^ 2) ^ (n - j) * (n.choose j : R)) := by rw [h1, h3, h2]
    _ = ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
          (B ^ i * A ^ (2 * n - i) * ((2 * n).choose i : R)) *
          ((- C ^ 2) ^ j * (A ^ 2) ^ (n - j) * (n.choose j : R)) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have mem_i : i ≤ 2 * n := by
    have h_lt := mem_range.1 hi
    omega
  have mem_j : j ≤ n := by
    have h_lt := mem_range.1 hj
    omega
  have h_pow1 : (- C ^ 2) ^ j = (-1 : R) ^ j * C ^ (2 * j) := by
    calc (- C ^ 2) ^ j = (-1 * C ^ 2) ^ j := by ring_nf
      _ = (-1 : R) ^ j * (C ^ 2) ^ j := mul_pow (-1 : R) (C ^ 2) j
      _ = (-1 : R) ^ j * C ^ (2 * j) := by rw [pow_mul]
  have h_pow2 : (A ^ 2) ^ (n - j) = A ^ (2 * n - 2 * j) := by
    rw [← pow_mul]
    have h_mul : 2 * (n - j) = 2 * n - 2 * j := by omega
    rw [h_mul]
  have h_pow3 : A ^ (2 * n - i) * A ^ (2 * n - 2 * j) = A ^ (4 * n - i - 2 * j) := by
    rw [← pow_add]
    have h_add : 2 * n - i + (2 * n - 2 * j) = 4 * n - i - 2 * j := by omega
    rw [h_add]
  rw [h_pow1, h_pow2]
  calc (B ^ i * A ^ (2 * n - i) * ↑((2 * n).choose i)) *
      ((-1) ^ j * C ^ (2 * j) * A ^ (2 * n - 2 * j) * ↑(n.choose j))
    _ = (↑((2 * n).choose i) * ↑(n.choose j) * (-1) ^ j) *
        (A ^ (2 * n - i) * A ^ (2 * n - 2 * j) * B ^ i * C ^ (2 * j)) := by ring
    _ = (↑((2 * n).choose i) * ↑(n.choose j) * (-1) ^ j) *
        (A ^ (4 * n - i - 2 * j) * B ^ i * C ^ (2 * j)) := by rw [h_pow3]


lemma if_cascade (n i j k u v : ℕ) (hv_le : v ≤ 2 * j) (hu_le : u ≤ i) (hj_le : j ≤ n) :
  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
  if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0 := by
  have H : n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) ↔
           k = n ∧ u = n - v ∧ v ≤ n ∧ i = 2 * n - 2 * j := by
    constructor
    · intro ⟨h1, h2, h3⟩
      have hv : v ≤ n := by omega
      have hu : u = n - v := by omega
      have hi : (n : ℤ) = (i - u + (2 * j - v) : ℕ) := by exact_mod_cast h3
      rw [Nat.cast_add, Nat.cast_sub hu_le, Nat.cast_sub hv_le] at hi
      have hi2 : i = 2 * n - 2 * j := by omega
      exact ⟨h1.symm, hu, hv, hi2⟩
    · intro ⟨hk, hu, hv, hi⟩
      have h1 : n = k := hk.symm
      have h2 : n = u + v := by omega
      have h3 : (n : ℤ) = (i - u + (2 * j - v) : ℕ) := by
        have hu2 : u ≤ i := by omega
        rw [Nat.cast_add, Nat.cast_sub hu2, Nat.cast_sub hv_le]
        omega
      exact ⟨h1, h2, by exact_mod_cast h3⟩
  by_cases h : n = k ∧ n = u + v ∧ n = i - u + (2 * j - v)
  · rw [if_pos h]
    have h' := H.mp h
    rw [if_pos h'.1, if_pos ⟨h'.2.1, h'.2.2.1⟩, if_pos h'.2.2.2]
  · rw [if_neg h]
    by_cases hk : k = n
    · rw [if_pos hk]
      by_cases huv : u = n - v ∧ v ≤ n
      · rw [if_pos huv]
        by_cases hi : i = 2 * n - 2 * j
        · rw [if_pos hi]
          have contra := H.mpr ⟨hk, huv.1, huv.2, hi⟩
          exact False.elim (h contra)
        · rw [if_neg hi]
      · rw [if_neg huv]
    · rw [if_neg hk]



lemma sum_ite_eq_drop (n k : ℕ) (f : ℕ → ℤ) (h_zero : ∀ x > n, f x = 0) :
  ∑ x ∈ range (n + 1), (if x = k then f x else 0) = f k := by
  rw [sum_ite_eq']
  by_cases hk : k ∈ range (n + 1)
  · rw [if_pos hk]
  · rw [if_neg hk]
    have h_gt : k > n := by
      have h1 := mem_range.not.1 hk
      omega
    exact (h_zero k h_gt).symm

lemma evaluate_k (n i j u v : ℕ) :
  ∑ k ∈ range (4 * n - i - 2 * j + 1),
    ( ((4 * n - i - 2 * j).choose k : ℤ) * (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) ) =
  ((4 * n - i - 2 * j).choose n : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) := by
  have h_term : ∀ k, (((4 * n - i - 2 * j).choose k : ℤ) * (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0)) =
                     if k = n then (((4 * n - i - 2 * j).choose k : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0)) else 0 := by
    intro k
    by_cases hk : k = n
    · rw [if_pos hk, if_pos hk, hk]
    · rw [if_neg hk, if_neg hk]
      simp
  have h_sum : ∑ k ∈ range (4 * n - i - 2 * j + 1), (((4 * n - i - 2 * j).choose k : ℤ) * (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0)) =
               ∑ k ∈ range (4 * n - i - 2 * j + 1), if k = n then (((4 * n - i - 2 * j).choose k : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0)) else 0 := sum_congr rfl (fun k _ => h_term k)
  rw [h_sum]
  have hs := sum_ite_eq_drop (4 * n - i - 2 * j) n (fun k => ((4 * n - i - 2 * j).choose k : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0))
  have h_zero : ∀ x > 4 * n - i - 2 * j, ((4 * n - i - 2 * j).choose x : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) = 0 := by
    intro x hx
    have h_choose : (4 * n - i - 2 * j).choose x = 0 := choose_eq_zero_of_lt hx
    rw [h_choose]
    simp
  exact hs h_zero

lemma evaluate_u (n i j v : ℕ) :
  ∑ u ∈ range (i + 1),
    ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
      (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) =
  if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
    (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 := by
  have h_term : ∀ u, (((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0)) =
                     if u = n - v then (if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0 := by
    intro u
    by_cases hu : u = n - v
    · by_cases hv : v ≤ n
      · simp [hu, hv]
      · simp [hu, hv]
    · simp [hu]
  have h_sum : ∑ u ∈ range (i + 1), (((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0)) =
               ∑ u ∈ range (i + 1), if u = n - v then (if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0 := sum_congr rfl (fun u _ => h_term u)
  rw [h_sum]
  have hs := sum_ite_eq_drop i (n - v) (fun u => if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0)
  have h_zero : ∀ x > i, (if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose x : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) = 0 := by
    intro x hx
    have h_choose : i.choose x = 0 := choose_eq_zero_of_lt hx
    simp [h_choose]
  exact hs h_zero

lemma evaluate_i (n j v : ℕ) :
  ∑ i ∈ range (2 * n + 1),
    (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
    ( if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
      (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 ) =
  if v ≤ n then (((2 * n).choose (2 * n - 2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - (2 * n - 2 * j) - 2 * j).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0 := by
  have h_term : ∀ i, (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * (if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) =
                     if i = 2 * n - 2 * j then (if v ≤ n then (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0) else 0 := by
    intro i
    by_cases h1 : v ≤ n
    · by_cases h2 : i = 2 * n - 2 * j
      · simp [h1, h2]
        ring
      · simp [h1, h2]
    · simp [h1]
  have h_sum : ∑ i ∈ range (2 * n + 1), (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * (if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) * (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) =
               ∑ i ∈ range (2 * n + 1), if i = 2 * n - 2 * j then (if v ≤ n then (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0) else 0 := sum_congr rfl (fun i _ => h_term i)
  rw [h_sum]
  have hs := sum_ite_eq_drop (2 * n) (2 * n - 2 * j) (fun i => if v ≤ n then (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0)
  have h_zero : ∀ x > 2 * n, (if v ≤ n then (((2 * n).choose x : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - x - 2 * j).choose n : ℤ) * (x.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0) = 0 := by
    intro x hx
    have h_choose : (2 * n).choose x = 0 := choose_eq_zero_of_lt hx
    simp [h_choose]
  exact hs h_zero


abbrev Vars := Fin 3
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

lemma coeff_monomial_three (n k u v j i : ℕ) :
  coeff (xyz_pow_n n) (
    (X 0 : MvPolynomial (Fin 3) ℤ) ^ k *
    (X 1) ^ (u + v) *
    (X 2) ^ (i - u + (2 * j - v))
  ) = if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0 := by
  have h1 : (X 0 : MvPolynomial (Fin 3) ℤ) ^ k * (X 1) ^ (u + v) * (X 2) ^ (i - u + (2 * j - v)) =
    monomial (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v))) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial]
    rw [monomial_mul, monomial_mul, mul_one, mul_one]
  rw [h1]
  rw [coeff_monomial]
  have h2 : xyz_pow_n n = single 0 n + single 1 n + single 2 n := by
    ext x
    have h0 : x = 0 ∨ x = 1 ∨ x = 2 := by
      match x with
      | ⟨0, _⟩ => exact Or.inl rfl
      | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
      | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
    rcases h0 with rfl | rfl | rfl
    · simp [xyz_pow_n, Finsupp.ofSupportFinite, single, add_apply]
    · simp [xyz_pow_n, Finsupp.ofSupportFinite, single, add_apply]
    · simp [xyz_pow_n, Finsupp.ofSupportFinite, single, add_apply]
  have h_eq : single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) = xyz_pow_n n ↔
    n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) := by
    rw [h2]
    constructor
    · intro h
      have h0 : (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) : Finsupp Vars ℕ) 0 = (single 0 n + single 1 n + single 2 n : Finsupp Vars ℕ) 0 := by rw [h]
      have h1 : (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) : Finsupp Vars ℕ) 1 = (single 0 n + single 1 n + single 2 n : Finsupp Vars ℕ) 1 := by rw [h]
      have h2 : (single 0 k + single 1 (u + v) + single 2 (i - u + (2 * j - v)) : Finsupp Vars ℕ) 2 = (single 0 n + single 1 n + single 2 n : Finsupp Vars ℕ) 2 := by rw [h]
      simp [add_apply] at h0 h1 h2
      exact ⟨h0.symm, h1.symm, h2.symm⟩
    · intro h
      rcases h with ⟨hk, hu, hv⟩
      rw [← hk, ← hu, ← hv]
  by_cases h_if : n = k ∧ n = u + v ∧ n = i - u + (2 * j - v)
  · rw [if_pos h_if]
    rw [if_pos (h_eq.mpr h_if)]
  · rw [if_neg h_if]
    rw [if_neg]
    intro contra
    exact h_if (h_eq.mp contra)

lemma C_eq (k : ℤ) : (k : MvPolynomial (Fin 3) ℤ) = C k := rfl

lemma triple_sum_mul (A i j : ℕ) (f g h : ℕ → MvPolynomial (Fin 3) ℤ) :
  (∑ k ∈ range (A + 1), f k) * (∑ u ∈ range (i + 1), g u) * (∑ v ∈ range (2 * j + 1), h v) =
  ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f k * g u * h v := by
  calc (∑ k ∈ range (A + 1), f k) * (∑ u ∈ range (i + 1), g u) * (∑ v ∈ range (2 * j + 1), h v)
    _ = (∑ k ∈ range (A + 1), f k * ∑ u ∈ range (i + 1), g u) * (∑ v ∈ range (2 * j + 1), h v) := by rw [Finset.sum_mul]
    _ = (∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), f k * g u) * (∑ v ∈ range (2 * j + 1), h v) := by
      congr 1
      apply sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ k ∈ range (A + 1), (∑ u ∈ range (i + 1), f k * g u) * (∑ v ∈ range (2 * j + 1), h v) := by rw [Finset.sum_mul]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), (f k * g u) * (∑ v ∈ range (2 * j + 1), h v) := by
      apply sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (f k * g u) * h v := by
      apply sum_congr rfl
      intro k _
      apply sum_congr rfl
      intro u _
      rw [Finset.mul_sum]

lemma coeff_P_ij (n i j : ℕ) (A : ℕ) :
  coeff (xyz_pow_n n) ((1 + X 0 : MvPolynomial (Fin 3) ℤ) ^ A * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j)) =
  ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
    ( (A.choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
    (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
  have h1 : (1 + X 0 : MvPolynomial (Fin 3) ℤ) ^ A = ∑ k ∈ range (A + 1), C (A.choose k : ℤ) * (X 0) ^ k := by
    rw [add_comm 1 (X 0), add_pow]
    apply sum_congr rfl
    intro k hk
    have hc : (A.choose k : MvPolynomial (Fin 3) ℤ) = C (A.choose k : ℤ) := by simp
    rw [hc]; simp; ring
  have h2 : (X 1 + X 2 : MvPolynomial (Fin 3) ℤ) ^ i = ∑ u ∈ range (i + 1), C (i.choose u : ℤ) * (X 1) ^ u * (X 2) ^ (i - u) := by
    rw [add_pow]
    apply sum_congr rfl
    intro u hu
    have hc : (i.choose u : MvPolynomial (Fin 3) ℤ) = C (i.choose u : ℤ) := by simp
    rw [hc]; ring
  have h3 : (X 1 - X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j) = ∑ v ∈ range (2 * j + 1), C (((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v)) * (X 1) ^ v * (X 2) ^ (2 * j - v) := by
    rw [sub_eq_add_neg, add_pow]
    apply sum_congr rfl
    intro v hv
    have hc : ((2 * j).choose v : MvPolynomial (Fin 3) ℤ) = C ((2 * j).choose v : ℤ) := by simp
    rw [hc]
    have hneg : (-X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v) = C ((-1 : ℤ) ^ (2 * j - v)) * X 2 ^ (2 * j - v) := by
      have h_neg1 : (-X 2 : MvPolynomial (Fin 3) ℤ) = C (-1 : ℤ) * X 2 := by simp
      rw [h_neg1, mul_pow]; simp
    rw [hneg]; simp; ring
  calc coeff (xyz_pow_n n) ((1 + X 0 : MvPolynomial (Fin 3) ℤ) ^ A * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j))
    _ = coeff (xyz_pow_n n) ((∑ k ∈ range (A + 1), C (A.choose k : ℤ) * X 0 ^ k) * (∑ u ∈ range (i + 1), C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (∑ v ∈ range (2 * j + 1), C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by rw [h1, h2, h3]
    _ = coeff (xyz_pow_n n) (∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by
      rw [triple_sum_mul A i j]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), coeff (xyz_pow_n n) ((C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by
      have hc1 : coeff (xyz_pow_n n) (∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) =
                 ∑ k ∈ range (A + 1), coeff (xyz_pow_n n) (∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by exact MvPolynomial.coeff_sum _ _ _
      rw [hc1]
      apply sum_congr rfl
      intro k hk
      have hc2 : coeff (xyz_pow_n n) (∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) =
                 ∑ u ∈ range (i + 1), coeff (xyz_pow_n n) (∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by exact MvPolynomial.coeff_sum _ _ _
      rw [hc2]
      apply sum_congr rfl
      intro u hu
      have hc3 : coeff (xyz_pow_n n) (∑ v ∈ range (2 * j + 1), (C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) =
                 ∑ v ∈ range (2 * j + 1), coeff (xyz_pow_n n) ((C (A.choose k : ℤ) * X 0 ^ k) * (C (i.choose u : ℤ) * X 1 ^ u * X 2 ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * X 1 ^ v * X 2 ^ (2 * j - v))) := by exact MvPolynomial.coeff_sum _ _ _
      rw [hc3]
    _ = ∑ k ∈ range (A + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
          ( (A.choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
          (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
      apply sum_congr rfl
      intro k hk
      apply sum_congr rfl
      intro u hu
      apply sum_congr rfl
      intro v hv
      have hc : (C (A.choose k : ℤ) * (X 0 : MvPolynomial (Fin 3) ℤ) ^ k) * (C (i.choose u : ℤ) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ u * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ v * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v)) =
                C ((A.choose k : ℤ) * (i.choose u : ℤ) * (((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v))) *
                ((X 0 : MvPolynomial (Fin 3) ℤ) ^ k * (X 1) ^ (u + v) * (X 2) ^ (i - u + (2 * j - v))) := by
        calc (C (A.choose k : ℤ) * (X 0 : MvPolynomial (Fin 3) ℤ) ^ k) * (C (i.choose u : ℤ) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ u * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u)) * (C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v)) * (X 1 : MvPolynomial (Fin 3) ℤ) ^ v * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v))
          _ = (C (A.choose k : ℤ) * C (i.choose u : ℤ) * C (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v))) * ((X 0 : MvPolynomial (Fin 3) ℤ) ^ k * ((X 1 : MvPolynomial (Fin 3) ℤ) ^ u * (X 1 : MvPolynomial (Fin 3) ℤ) ^ v) * ((X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u) * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (2 * j - v))) := by ring
          _ = C ((A.choose k : ℤ) * (i.choose u : ℤ) * (↑((2 * j).choose v) * (-1 : ℤ) ^ (2 * j - v))) * ((X 0 : MvPolynomial (Fin 3) ℤ) ^ k * (X 1 : MvPolynomial (Fin 3) ℤ) ^ (u + v) * (X 2 : MvPolynomial (Fin 3) ℤ) ^ (i - u + (2 * j - v))) := by
            rw [← map_mul, ← map_mul, ← pow_add, ← pow_add]
      rw [hc, coeff_C_mul, coeff_monomial_three]
      split_ifs
      · ring
      · ring



lemma sum_perm (n j : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℤ) :
  ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f i k u v =
  ∑ v ∈ range (2 * j + 1), ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), f i k u v := by
  have h1 : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f i k u v =
            ∑ i ∈ range (2 * n + 1), ∑ v ∈ range (2 * j + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), f i k u v := by
    apply sum_congr rfl
    intro i _
    have hk_swap : ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1), f i k u v =
                   ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ v ∈ range (2 * j + 1), ∑ u ∈ range (i + 1), f i k u v := by
      apply sum_congr rfl
      intro k _
      rw [sum_comm]
    rw [hk_swap]
    rw [sum_comm]
  rw [h1, sum_comm]



abbrev Vars_local := Fin 3
noncomputable def xyz_pow_n_local (n : ℕ) : Finsupp Vars_local ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars_local => n) (Set.toFinite _)
local notation "P" => MvPolynomial Vars_local ℤ
noncomputable def P_n_local (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

lemma P_n_eq (n : ℕ) :
  P_n_local n = ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
    ( ( (2 * n).choose i : MvPolynomial Vars_local ℤ) * (n.choose j : MvPolynomial Vars_local ℤ) * (-1 : MvPolynomial Vars_local ℤ) ^ j ) *
    ( (1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j) ) := by
  unfold P_n_local
  have h := comm_ring_id (1 + X 0 : MvPolynomial Vars_local ℤ) (X 1 + X 2) (X 1 - X 2) n
  have hB : (1 + X 0 : MvPolynomial Vars_local ℤ) + (X 1 + X 2) = 1 + X 0 + X 1 + X 2 := by ring
  have hC1 : (1 + X 0 : MvPolynomial Vars_local ℤ) + (X 1 - X 2) = 1 + X 0 + X 1 - X 2 := by ring
  have hC2 : (1 + X 0 : MvPolynomial Vars_local ℤ) - (X 1 - X 2) = 1 + X 0 - X 1 + X 2 := by ring
  rw [hB, hC1, hC2] at h
  exact h

lemma coeff_P_n (n : ℕ) :
  coeff (xyz_pow_n_local n) (P_n_local n) =
  ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1),
    ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
      ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
      ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
      (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
  rw [P_n_eq]
  rw [coeff_sum]
  apply sum_congr rfl
  intro i hi
  rw [coeff_sum]
  apply sum_congr rfl
  intro j hj
  have hc : coeff (xyz_pow_n_local n) ((((2 * n).choose i : MvPolynomial Vars_local ℤ) * (n.choose j : MvPolynomial Vars_local ℤ) * (-1 : MvPolynomial Vars_local ℤ) ^ j) * ((1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j))) =
            (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
            coeff (xyz_pow_n_local n) ((1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j)) := by
    have h_C : (((2 * n).choose i : MvPolynomial Vars_local ℤ) * (n.choose j : MvPolynomial Vars_local ℤ) * (-1 : MvPolynomial Vars_local ℤ) ^ j) =
               C (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) := by
      simp
    rw [h_C, coeff_C_mul]
  rw [hc]
  have hc_pij : coeff (xyz_pow_n_local n) ((1 + X 0 : MvPolynomial Vars_local ℤ) ^ (4 * n - i - 2 * j) * (X 1 + X 2) ^ i * (X 1 - X 2) ^ (2 * j)) =
                coeff_P_ij n i j (4 * n - i - 2 * j) |>.symm ▸ coeff_P_ij n i j (4 * n - i - 2 * j) := by exact rfl
  rw [coeff_P_ij]
  rw [← mul_sum, ← sum_mul]
  apply sum_congr rfl
  intro k _
  rw [← mul_sum, ← sum_mul]
  apply sum_congr rfl
  intro u _
  rw [← mul_sum, ← sum_mul]
  apply sum_congr rfl
  intro v _
  ring


lemma sum_filter_eq_sum_ite (n j : ℕ) (F : ℕ → ℤ) :
  ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n), F v =
  ∑ v ∈ range (2 * j + 1), if v ≤ n then F v else 0 := by
  rw [sum_filter]

lemma step1 (n j i u v : ℕ) :
  ∑ k ∈ range (4 * n - i - 2 * j + 1),
    ( ((4 * n - i - 2 * j).choose k : ℤ) * (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) ) =
  ((4 * n - i - 2 * j).choose n : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) := by
  exact evaluate_k n i j u v

lemma step2 (n j i v : ℕ) :
  ∑ u ∈ range (i + 1),
    ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
      (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) =
  if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
    (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 := by
  exact evaluate_u n i j v

lemma step3 (n j v : ℕ) :
  ∑ i ∈ range (2 * n + 1),
    (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
    ( if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
      (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 ) =
  if v ≤ n then (((2 * n).choose (2 * n - 2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - (2 * n - 2 * j) - 2 * j).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0 := by
  exact evaluate_i n j v


lemma collapse_sums (n j v : ℕ) :
  ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
    ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
    ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
    (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) =
  if v ≤ n then (((2 * n).choose (2 * n - 2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - (2 * n - 2 * j) - 2 * j).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0 := by
  have hk : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) =
            ∑ i ∈ range (2 * n + 1), ∑ u ∈ range (i + 1),
              ∑ k ∈ range (4 * n - i - 2 * j + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) := by
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
  rw [hk]
  have hk2 : ∀ i u, ∑ k ∈ range (4 * n - i - 2 * j + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) =
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
              (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) := by
    intro i u
    calc ∑ k ∈ range (4 * n - i - 2 * j + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0)
      _ = ∑ k ∈ range (4 * n - i - 2 * j + 1),
          ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
          (((4 * n - i - 2 * j).choose k : ℤ) * (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0)) *
          ((i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v)) := by
        apply sum_congr rfl
        intro k _
        ring
      _ = ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
          (∑ k ∈ range (4 * n - i - 2 * j + 1), (((4 * n - i - 2 * j).choose k : ℤ) * (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0))) *
          ((i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v)) := by
        rw [← sum_mul, ← mul_sum]
      _ = ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
          ( ((4 * n - i - 2 * j).choose n : ℤ) * (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) *
          ((i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v)) := by
        rw [evaluate_k]
      _ = ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
          ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
          (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) := by
        ring
  have hk3 : ∑ i ∈ range (2 * n + 1), ∑ u ∈ range (i + 1),
              ∑ k ∈ range (4 * n - i - 2 * j + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) =
             ∑ i ∈ range (2 * n + 1), ∑ u ∈ range (i + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
              (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) := sum_congr rfl (fun i _ => sum_congr rfl (fun u _ => hk2 i u))
  rw [hk3]
  have hu : ∀ i, ∑ u ∈ range (i + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
              (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) =
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
                (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 ) := by
    intro i
    calc ∑ u ∈ range (i + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
              (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) )
      _ = ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
          ∑ u ∈ range (i + 1), ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
              (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) := by rw [← mul_sum]
      _ = ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
          ( if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
            (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 ) := by rw [evaluate_u]
  have hu2 : ∑ i ∈ range (2 * n + 1), ∑ u ∈ range (i + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
              (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) ) =
             ∑ i ∈ range (2 * n + 1),
              ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
              ( if v ≤ n then ((4 * n - i - 2 * j).choose n : ℤ) * (i.choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) *
                (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0 ) := sum_congr rfl (fun i _ => hu i)
  rw [hu2]
  exact evaluate_i n j v





lemma my_small_sum2_eq_coeff_full (n : ℕ) :
  my_small_sum2 n = coeff (xyz_pow_n n) (P_n n) := by
  unfold my_small_sum2
  rw [coeff_P_n]
  have h_swap : ∑ i ∈ range (2 * n + 1), ∑ j ∈ range (n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1), ∑ v ∈ range (2 * j + 1),
                  ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
                ∑ j ∈ range (n + 1), ∑ v ∈ range (2 * j + 1), ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
                  ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    exact sum_perm n j _
  rw [h_swap]
  apply sum_congr rfl
  intro j hj
  rw [sum_filter_eq_sum_ite]
  apply sum_congr rfl
  intro v hv
  have hv_le : v ≤ 2 * j := by
    have h1 := mem_range.1 hv
    omega
  have hj_le : j ≤ n := by
    have h1 := mem_range.1 hj
    omega
  have h_inner : ∀ i k u, ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
                  ( ((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j ) *
                  ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
                  (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) := by
    intro i k u
    by_cases hu : u ≤ i
    · rw [if_cascade n i j k u v hv_le hu hj_le]
    · have h_zero : (i.choose u : ℤ) = 0 := by
        have h_lt : i < u := by omega
        exact_mod_cast choose_eq_zero_of_lt h_lt
      rw [h_zero]
      simp
  have hc : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if n = k ∧ n = u + v ∧ n = i - u + (2 * j - v) then (1 : ℤ) else 0) =
            ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro u _
    rw [h_inner]
  rw [hc]
  have hc2 : ∑ i ∈ range (2 * n + 1), ∑ k ∈ range (4 * n - i - 2 * j + 1), ∑ u ∈ range (i + 1),
              (((2 * n).choose i : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
              ( ((4 * n - i - 2 * j).choose k : ℤ) * (i.choose u : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) ) *
              (if k = n then (if u = n - v ∧ v ≤ n then (if i = 2 * n - 2 * j then (1 : ℤ) else 0) else 0) else 0) =
            if v ≤ n then (((2 * n).choose (2 * n - 2 * j) : ℤ) * (n.choose j : ℤ) * (-1 : ℤ) ^ j) * ((4 * n - (2 * n - 2 * j) - 2 * j).choose n : ℤ) * ((2 * n - 2 * j).choose (n - v) : ℤ) * ((2 * j).choose v : ℤ) * (-1 : ℤ) ^ (2 * j - v) else 0 := by
    exact collapse_sums n j v
  rw [hc2]
  by_cases hvn : v ≤ n
  · rw [if_pos hvn, if_pos hvn]
    have h_choose : (4 * n - (2 * n - 2 * j) - 2 * j).choose n = (2 * n).choose n := by
      congr 1
      omega
    rw [h_choose]
    have h_choose_symm : (2 * n).choose (2 * n - 2 * j) = (2 * n).choose (2 * j) := by
      have hle : 2 * j ≤ 2 * n := by omega
      exact choose_symm hle
    rw [h_choose_symm]
    have h_neg : (-1 : ℤ) ^ (2 * j - v) = (-1 : ℤ) ^ v := by
      have h1 : (2 * j - v) + v = 2 * j := by omega
      have h2 : (-1 : ℤ) ^ (2 * j - v) * (-1 : ℤ) ^ v = (-1 : ℤ) ^ (2 * j) := by rw [← pow_add, h1]
      have h3 : (-1 : ℤ) ^ (2 * j) = 1 := by
        have h_mul : 2 * j = 2 * j := rfl
        rw [h_mul]
        have hpow : (-1 : ℤ) ^ (2 * j) = ((-1 : ℤ) ^ 2) ^ j := by exact pow_mul (-1) 2 j
        rw [hpow]
        simp
      rw [h3] at h2
      calc (-1 : ℤ) ^ (2 * j - v) = (-1 : ℤ) ^ (2 * j - v) * 1 := by ring
        _ = (-1 : ℤ) ^ (2 * j - v) * ((-1 : ℤ) ^ v * (-1 : ℤ) ^ v) := by
          have hv2 : (-1 : ℤ) ^ v * (-1 : ℤ) ^ v = (1 : ℤ) := by
            rw [← pow_add]
            have h4 : v + v = 2 * v := by omega
            have hpow2 : (-1 : ℤ) ^ (v + v) = ((-1 : ℤ) ^ 2) ^ v := by
              rw [h4]
              exact pow_mul (-1) 2 v
            rw [hpow2]
            simp
          rw [hv2]
        _ = ((-1 : ℤ) ^ (2 * j - v) * (-1 : ℤ) ^ v) * (-1 : ℤ) ^ v := by ring
        _ = 1 * (-1 : ℤ) ^ v := by rw [h2]
        _ = (-1 : ℤ) ^ v := by ring
    rw [h_neg]
    ring
  · rw [if_neg hvn, if_neg hvn]



def a_local (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

lemma small_sum2_eq_a (n : ℕ)
  (small_sum2_simplified : my_small_sum2 n =
    ∑ j ∈ range (n + 1), ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
      ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ))
  (drop_filter_sum : ∀ j, ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) =
                          ∑ v ∈ range (2 * j + 1), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v))
  (inner_sum_eval : ∀ j, ∑ v ∈ range (2 * j + 1), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) =
                         (n.choose j : ℤ) * (-1 : ℤ) ^ j)
  (sum_choose_square : ∑ j ∈ range (n + 1), (n.choose j : ℤ) ^ 2 = ((2 * n).choose n : ℤ)) :
  my_small_sum2 n = (a_local n : ℤ) := by
  unfold a_local
  rw [small_sum2_simplified]
  have h_inner : ∀ j, ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ) =
    ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2 := by
    intro j
    calc ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
          ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) )
      _ = ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
          ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j * ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) ) := by
        apply sum_congr rfl
        intro v _
        rw [pow_add]
        ring
      _ = (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
          ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) := by
        rw [← mul_sum]
      _ = (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
          ∑ v ∈ range (2 * j + 1), ((n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ v) := by
        rw [drop_filter_sum j]
      _ = (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (-1 : ℤ) ^ j) *
          ((n.choose j : ℤ) * (-1 : ℤ) ^ j) := by
        rw [inner_sum_eval j]
      _ = ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2 * ((-1 : ℤ) ^ j) ^ 2 := by
        ring
      _ = ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2 := by
        have h_even : ((-1 : ℤ) ^ j) ^ 2 = 1 := by
          rw [← pow_mul]
          have h_mul : j * 2 = 2 * j := by ring
          rw [h_mul, pow_mul]
          simp
        rw [h_even, mul_one]
  have h_sum : ∑ j ∈ range (n + 1), ∑ v ∈ (range (2 * j + 1)).filter (fun v => v ≤ n),
    ( ((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) * (n.choose v : ℤ) * (n.choose (2 * j - v) : ℤ) * (-1 : ℤ) ^ (j + v) ) =
    ∑ j ∈ range (n + 1), (((2 * n).choose n : ℤ) ^ 2 * (n.choose j : ℤ) ^ 2) := sum_congr rfl (fun j _ => h_inner j)
  rw [h_sum]
  rw [← mul_sum]
  rw [sum_choose_square]
  push_cast
  ring

theorem oeis_2897_conjecture_0 (n : ℕ) :
  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) := by
  have h1 := small_sum2_eq_a n (small_sum2_simplified n) (drop_filter_sum n) (inner_sum_eval n) (sum_choose_square n)
  have h2 := my_small_sum2_eq_coeff_full n
  rw [← h1, h2]

theorem oeis_2897_conjecture_0.disproof : ¬ (type_of% @oeis_2897_conjecture_0) := sorry
