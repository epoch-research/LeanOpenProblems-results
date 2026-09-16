import FormalConjectures.Util.ProblemImports
open Finset Nat MvPolynomial Finsupp

lemma sum_ite_eq_drop (n k : ℕ) (f : ℕ → ℤ) (h_zero : ∀ x > n, f x = 0) :
  ∑ x ∈ range (n + 1), (if x = k then f x else 0) = f k := by
  rw [Finset.sum_ite_eq']
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


