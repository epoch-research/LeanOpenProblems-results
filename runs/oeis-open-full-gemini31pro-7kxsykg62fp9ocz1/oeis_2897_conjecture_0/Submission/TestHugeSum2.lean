import FormalConjectures.Util.ProblemImports
open Finset Nat Polynomial

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

