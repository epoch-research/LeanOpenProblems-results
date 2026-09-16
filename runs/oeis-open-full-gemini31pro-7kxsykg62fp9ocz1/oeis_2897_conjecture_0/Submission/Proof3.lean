import Submission.Proof
open Finset Nat MvPolynomial

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

