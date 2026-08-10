import FormalConjectures.Util.ProblemImports

open Nat

lemma match_find?_ne_zero (candidates : List ℕ)
  (h : ∃ p ∈ candidates, Nat.Prime p) :
  (match candidates.find? (fun b => decide (Nat.Prime b)) with
   | some p => p
   | none => 0) ≠ 0 := by
  by_cases hc : candidates.find? (fun b => decide (Nat.Prime b)) = none
  · rw [List.find?_eq_none] at hc
    rcases h with ⟨p, hp_in, hp_prime⟩
    have h_not := hc p hp_in
    simp only [Bool.not_eq_true, decide_eq_false_iff_not] at h_not
    exact False.elim (h_not hp_prime)
  · match h_some : candidates.find? (fun b => decide (Nat.Prime b)) with
    | none => exact (hc h_some).elim
    | some p =>
      have h_prop := List.find?_some h_some
      simp only [decide_eq_true_iff] at h_prop
      exact Nat.Prime.ne_zero h_prop

noncomputable def a (n : ℕ) : ℕ :=

  -- Helper function to get the concatenated digits of a list of numbers in MSD-first order.
  let get_all_digits_msf (L : List ℕ) : List ℕ :=
    let to_digits_msb (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse
    -- Concatenates the list of digit lists using foldr, equivalent to List.join (List.map to_digits_msb L).
    List.foldr (fun num acc_digits => (to_digits_msb num) ++ acc_digits) [] L

  -- Helper function to convert a list of digits (MSF) to a number.
  let of_msb_digits (D : List ℕ) : ℕ :=
    D.foldl (fun acc d => acc * 10 + d) 0

  -- The core concatenation logic: n || (n-1) || ... || (n-k)
  let concatenated_number (k : ℕ) : ℕ :=
    -- The list of numbers is `[n, n-1, ..., n-k]`. We ensure subtraction is safe for `i < n`.
    let num_list : List ℕ := List.map (fun i => n - i) (List.range (k + 1))
    of_msb_digits (get_all_digits_msf num_list)

  -- The possible values for k are 0 up to n-1.
  -- List.range n generates [0, 1, ..., n-1].
  let candidates : List ℕ :=
    List.map concatenated_number (List.range n)

  -- Find the smallest prime.
  match List.find? Nat.Prime candidates with
  | some p => p
  | none   => 0

lemma a_ne_zero_helper (n : ℕ) (p : ℕ) (k : ℕ) (hk : k < n)
  (h_cand : (
    let get_all_digits_msf (L : List ℕ) : List ℕ :=
      let to_digits_msb (num : ℕ) : List ℕ := (Nat.digits 10 num).reverse
      List.foldr (fun num acc_digits => (to_digits_msb num) ++ acc_digits) [] L
    let of_msb_digits (D : List ℕ) : ℕ :=
      D.foldl (fun acc d => acc * 10 + d) 0
    let num_list : List ℕ := List.map (fun i => n - i) (List.range (k + 1))
    of_msb_digits (get_all_digits_msf num_list)
  ) = p)
  (hp_prime : Nat.Prime p) :
  a n ≠ 0 := by
  unfold a
  dsimp only
  apply match_find?_ne_zero
  use p
  constructor
  · rw [List.mem_map]
    use k
    refine ⟨?_, h_cand⟩
    rw [List.mem_range]
    exact hk
  · exact hp_prime

lemma a4_ne_zero : a 4 ≠ 0 := by
  apply a_ne_zero_helper 4 43 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 4 - i) [0, 1] = [4, 3] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [4, 3] =
      (digits 10 4).reverse ++ ((digits 10 3).reverse ++ []) := rfl
    rw [h_foldr]
    have h4 : digits 10 4 = [4] := digits_of_lt 10 4 (by decide) (by decide)
    have h3 : digits 10 3 = [3] := digits_of_lt 10 3 (by decide) (by decide)
    rw [h4, h3]
    rfl
  · norm_num

lemma a10_ne_zero : a 10 ≠ 0 := by
  apply a_ne_zero_helper 10 109 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 10 - i) [0, 1] = [10, 9] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [10, 9] =
      (digits 10 10).reverse ++ ((digits 10 9).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have h10 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have h9 : digits 10 9 = [9] := digits_of_lt 10 9 (by decide) (by decide)
    rw [h10, h9]
    rfl
  · norm_num

lemma a22_ne_zero : a 22 ≠ 0 := by
  apply a_ne_zero_helper 22 2221 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 22 - i) [0, 1] = [22, 21] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [22, 21] =
      (digits 10 22).reverse ++ ((digits 10 21).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_22 : digits 10 2 = [2] := digits_of_lt 10 2 (by decide) (by decide)
    have h22 : digits 10 22 = [2, 2] := by
      have h_add := digits_add 10 (by decide) 2 2 (by decide) (by decide)
      have h_calc : 2 + 10 * 2 = 22 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_22]
    have hy_21 : digits 10 2 = [2] := digits_of_lt 10 2 (by decide) (by decide)
    have h21 : digits 10 21 = [1, 2] := by
      have h_add := digits_add 10 (by decide) 1 2 (by decide) (by decide)
      have h_calc : 1 + 10 * 2 = 21 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_21]
    rw [h22, h21]
    rfl
  · norm_num

lemma a202_ne_zero : a 202 ≠ 0 := by
  apply a_ne_zero_helper 202 202201 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 202 - i) [0, 1] = [202, 201] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [202, 201] =
      (digits 10 202).reverse ++ ((digits 10 201).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_20 : digits 10 2 = [2] := digits_of_lt 10 2 (by decide) (by decide)
    have hy_202 : digits 10 20 = [0, 2] := by
      have h_add := digits_add 10 (by decide) 0 2 (by decide) (by decide)
      have h_calc : 0 + 10 * 2 = 20 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_20]
    have h202 : digits 10 202 = [2, 0, 2] := by
      have h_add := digits_add 10 (by decide) 2 20 (by decide) (by decide)
      have h_calc : 2 + 10 * 20 = 202 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_202]
    have hy_20 : digits 10 2 = [2] := digits_of_lt 10 2 (by decide) (by decide)
    have hy_201 : digits 10 20 = [0, 2] := by
      have h_add := digits_add 10 (by decide) 0 2 (by decide) (by decide)
      have h_calc : 0 + 10 * 2 = 20 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_20]
    have h201 : digits 10 201 = [1, 0, 2] := by
      have h_add := digits_add 10 (by decide) 1 20 (by decide) (by decide)
      have h_calc : 1 + 10 * 20 = 201 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_201]
    rw [h202, h201]
    rfl
  · norm_num

lemma a304_ne_zero : a 304 ≠ 0 := by
  apply a_ne_zero_helper 304 304303 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 304 - i) [0, 1] = [304, 303] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [304, 303] =
      (digits 10 304).reverse ++ ((digits 10 303).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_30 : digits 10 3 = [3] := digits_of_lt 10 3 (by decide) (by decide)
    have hy_304 : digits 10 30 = [0, 3] := by
      have h_add := digits_add 10 (by decide) 0 3 (by decide) (by decide)
      have h_calc : 0 + 10 * 3 = 30 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_30]
    have h304 : digits 10 304 = [4, 0, 3] := by
      have h_add := digits_add 10 (by decide) 4 30 (by decide) (by decide)
      have h_calc : 4 + 10 * 30 = 304 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_304]
    have hy_30 : digits 10 3 = [3] := digits_of_lt 10 3 (by decide) (by decide)
    have hy_303 : digits 10 30 = [0, 3] := by
      have h_add := digits_add 10 (by decide) 0 3 (by decide) (by decide)
      have h_calc : 0 + 10 * 3 = 30 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_30]
    have h303 : digits 10 303 = [3, 0, 3] := by
      have h_add := digits_add 10 (by decide) 3 30 (by decide) (by decide)
      have h_calc : 3 + 10 * 30 = 303 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_303]
    rw [h304, h303]
    rfl
  · norm_num

lemma a1002_ne_zero : a 1002 ≠ 0 := by
  apply a_ne_zero_helper 1002 10021001 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 1002 - i) [0, 1] = [1002, 1001] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [1002, 1001] =
      (digits 10 1002).reverse ++ ((digits 10 1001).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1002 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have h1002 : digits 10 1002 = [2, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 2 100 (by decide) (by decide)
      have h_calc : 2 + 10 * 100 = 1002 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1002]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1001 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have h1001 : digits 10 1001 = [1, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 1 100 (by decide) (by decide)
      have h_calc : 1 + 10 * 100 = 1001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1001]
    rw [h1002, h1001]
    rfl
  · norm_num

lemma a10008_ne_zero : a 10008 ≠ 0 := by
  apply a_ne_zero_helper 10008 1000810007 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 10008 - i) [0, 1] = [10008, 10007] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [10008, 10007] =
      (digits 10 10008).reverse ++ ((digits 10 10007).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1000 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have hy_10008 : digits 10 1000 = [0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 100 (by decide) (by decide)
      have h_calc : 0 + 10 * 100 = 1000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1000]
    have h10008 : digits 10 10008 = [8, 0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 8 1000 (by decide) (by decide)
      have h_calc : 8 + 10 * 1000 = 10008 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10008]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1000 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have hy_10007 : digits 10 1000 = [0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 100 (by decide) (by decide)
      have h_calc : 0 + 10 * 100 = 1000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1000]
    have h10007 : digits 10 10007 = [7, 0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 7 1000 (by decide) (by decide)
      have h_calc : 7 + 10 * 1000 = 10007 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10007]
    rw [h10008, h10007]
    rfl
  · norm_num

lemma a10014_ne_zero : a 10014 ≠ 0 := by
  apply a_ne_zero_helper 10014 1001410013 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 10014 - i) [0, 1] = [10014, 10013] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [10014, 10013] =
      (digits 10 10014).reverse ++ ((digits 10 10013).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1001 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have hy_10014 : digits 10 1001 = [1, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 1 100 (by decide) (by decide)
      have h_calc : 1 + 10 * 100 = 1001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1001]
    have h10014 : digits 10 10014 = [4, 1, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 4 1001 (by decide) (by decide)
      have h_calc : 4 + 10 * 1001 = 10014 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10014]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1001 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have hy_10013 : digits 10 1001 = [1, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 1 100 (by decide) (by decide)
      have h_calc : 1 + 10 * 100 = 1001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1001]
    have h10013 : digits 10 10013 = [3, 1, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 3 1001 (by decide) (by decide)
      have h_calc : 3 + 10 * 1001 = 10013 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10013]
    rw [h10014, h10013]
    rfl
  · norm_num

lemma a20004_ne_zero : a 20004 ≠ 0 := by
  apply a_ne_zero_helper 20004 2000420003 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 20004 - i) [0, 1] = [20004, 20003] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [20004, 20003] =
      (digits 10 20004).reverse ++ ((digits 10 20003).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_20 : digits 10 2 = [2] := digits_of_lt 10 2 (by decide) (by decide)
    have hy_200 : digits 10 20 = [0, 2] := by
      have h_add := digits_add 10 (by decide) 0 2 (by decide) (by decide)
      have h_calc : 0 + 10 * 2 = 20 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_20]
    have hy_2000 : digits 10 200 = [0, 0, 2] := by
      have h_add := digits_add 10 (by decide) 0 20 (by decide) (by decide)
      have h_calc : 0 + 10 * 20 = 200 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_200]
    have hy_20004 : digits 10 2000 = [0, 0, 0, 2] := by
      have h_add := digits_add 10 (by decide) 0 200 (by decide) (by decide)
      have h_calc : 0 + 10 * 200 = 2000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_2000]
    have h20004 : digits 10 20004 = [4, 0, 0, 0, 2] := by
      have h_add := digits_add 10 (by decide) 4 2000 (by decide) (by decide)
      have h_calc : 4 + 10 * 2000 = 20004 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_20004]
    have hy_20 : digits 10 2 = [2] := digits_of_lt 10 2 (by decide) (by decide)
    have hy_200 : digits 10 20 = [0, 2] := by
      have h_add := digits_add 10 (by decide) 0 2 (by decide) (by decide)
      have h_calc : 0 + 10 * 2 = 20 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_20]
    have hy_2000 : digits 10 200 = [0, 0, 2] := by
      have h_add := digits_add 10 (by decide) 0 20 (by decide) (by decide)
      have h_calc : 0 + 10 * 20 = 200 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_200]
    have hy_20003 : digits 10 2000 = [0, 0, 0, 2] := by
      have h_add := digits_add 10 (by decide) 0 200 (by decide) (by decide)
      have h_calc : 0 + 10 * 200 = 2000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_2000]
    have h20003 : digits 10 20003 = [3, 0, 0, 0, 2] := by
      have h_add := digits_add 10 (by decide) 3 2000 (by decide) (by decide)
      have h_calc : 3 + 10 * 2000 = 20003 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_20003]
    rw [h20004, h20003]
    rfl
  · norm_num

lemma a30034_ne_zero : a 30034 ≠ 0 := by
  apply a_ne_zero_helper 30034 3003430033 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 30034 - i) [0, 1] = [30034, 30033] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [30034, 30033] =
      (digits 10 30034).reverse ++ ((digits 10 30033).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_30 : digits 10 3 = [3] := digits_of_lt 10 3 (by decide) (by decide)
    have hy_300 : digits 10 30 = [0, 3] := by
      have h_add := digits_add 10 (by decide) 0 3 (by decide) (by decide)
      have h_calc : 0 + 10 * 3 = 30 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_30]
    have hy_3003 : digits 10 300 = [0, 0, 3] := by
      have h_add := digits_add 10 (by decide) 0 30 (by decide) (by decide)
      have h_calc : 0 + 10 * 30 = 300 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_300]
    have hy_30034 : digits 10 3003 = [3, 0, 0, 3] := by
      have h_add := digits_add 10 (by decide) 3 300 (by decide) (by decide)
      have h_calc : 3 + 10 * 300 = 3003 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_3003]
    have h30034 : digits 10 30034 = [4, 3, 0, 0, 3] := by
      have h_add := digits_add 10 (by decide) 4 3003 (by decide) (by decide)
      have h_calc : 4 + 10 * 3003 = 30034 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_30034]
    have hy_30 : digits 10 3 = [3] := digits_of_lt 10 3 (by decide) (by decide)
    have hy_300 : digits 10 30 = [0, 3] := by
      have h_add := digits_add 10 (by decide) 0 3 (by decide) (by decide)
      have h_calc : 0 + 10 * 3 = 30 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_30]
    have hy_3003 : digits 10 300 = [0, 0, 3] := by
      have h_add := digits_add 10 (by decide) 0 30 (by decide) (by decide)
      have h_calc : 0 + 10 * 30 = 300 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_300]
    have hy_30033 : digits 10 3003 = [3, 0, 0, 3] := by
      have h_add := digits_add 10 (by decide) 3 300 (by decide) (by decide)
      have h_calc : 3 + 10 * 300 = 3003 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_3003]
    have h30033 : digits 10 30033 = [3, 3, 0, 0, 3] := by
      have h_add := digits_add 10 (by decide) 3 3003 (by decide) (by decide)
      have h_calc : 3 + 10 * 3003 = 30033 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_30033]
    rw [h30034, h30033]
    rfl
  · norm_num

lemma a40054_ne_zero : a 40054 ≠ 0 := by
  apply a_ne_zero_helper 40054 4005440053 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 40054 - i) [0, 1] = [40054, 40053] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [40054, 40053] =
      (digits 10 40054).reverse ++ ((digits 10 40053).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_40 : digits 10 4 = [4] := digits_of_lt 10 4 (by decide) (by decide)
    have hy_400 : digits 10 40 = [0, 4] := by
      have h_add := digits_add 10 (by decide) 0 4 (by decide) (by decide)
      have h_calc : 0 + 10 * 4 = 40 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_40]
    have hy_4005 : digits 10 400 = [0, 0, 4] := by
      have h_add := digits_add 10 (by decide) 0 40 (by decide) (by decide)
      have h_calc : 0 + 10 * 40 = 400 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_400]
    have hy_40054 : digits 10 4005 = [5, 0, 0, 4] := by
      have h_add := digits_add 10 (by decide) 5 400 (by decide) (by decide)
      have h_calc : 5 + 10 * 400 = 4005 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_4005]
    have h40054 : digits 10 40054 = [4, 5, 0, 0, 4] := by
      have h_add := digits_add 10 (by decide) 4 4005 (by decide) (by decide)
      have h_calc : 4 + 10 * 4005 = 40054 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_40054]
    have hy_40 : digits 10 4 = [4] := digits_of_lt 10 4 (by decide) (by decide)
    have hy_400 : digits 10 40 = [0, 4] := by
      have h_add := digits_add 10 (by decide) 0 4 (by decide) (by decide)
      have h_calc : 0 + 10 * 4 = 40 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_40]
    have hy_4005 : digits 10 400 = [0, 0, 4] := by
      have h_add := digits_add 10 (by decide) 0 40 (by decide) (by decide)
      have h_calc : 0 + 10 * 40 = 400 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_400]
    have hy_40053 : digits 10 4005 = [5, 0, 0, 4] := by
      have h_add := digits_add 10 (by decide) 5 400 (by decide) (by decide)
      have h_calc : 5 + 10 * 400 = 4005 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_4005]
    have h40053 : digits 10 40053 = [3, 5, 0, 0, 4] := by
      have h_add := digits_add 10 (by decide) 3 4005 (by decide) (by decide)
      have h_calc : 3 + 10 * 4005 = 40053 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_40053]
    rw [h40054, h40053]
    rfl
  · norm_num

lemma a50034_ne_zero : a 50034 ≠ 0 := by
  apply a_ne_zero_helper 50034 5003450033 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 50034 - i) [0, 1] = [50034, 50033] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [50034, 50033] =
      (digits 10 50034).reverse ++ ((digits 10 50033).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_50 : digits 10 5 = [5] := digits_of_lt 10 5 (by decide) (by decide)
    have hy_500 : digits 10 50 = [0, 5] := by
      have h_add := digits_add 10 (by decide) 0 5 (by decide) (by decide)
      have h_calc : 0 + 10 * 5 = 50 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_50]
    have hy_5003 : digits 10 500 = [0, 0, 5] := by
      have h_add := digits_add 10 (by decide) 0 50 (by decide) (by decide)
      have h_calc : 0 + 10 * 50 = 500 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_500]
    have hy_50034 : digits 10 5003 = [3, 0, 0, 5] := by
      have h_add := digits_add 10 (by decide) 3 500 (by decide) (by decide)
      have h_calc : 3 + 10 * 500 = 5003 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_5003]
    have h50034 : digits 10 50034 = [4, 3, 0, 0, 5] := by
      have h_add := digits_add 10 (by decide) 4 5003 (by decide) (by decide)
      have h_calc : 4 + 10 * 5003 = 50034 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_50034]
    have hy_50 : digits 10 5 = [5] := digits_of_lt 10 5 (by decide) (by decide)
    have hy_500 : digits 10 50 = [0, 5] := by
      have h_add := digits_add 10 (by decide) 0 5 (by decide) (by decide)
      have h_calc : 0 + 10 * 5 = 50 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_50]
    have hy_5003 : digits 10 500 = [0, 0, 5] := by
      have h_add := digits_add 10 (by decide) 0 50 (by decide) (by decide)
      have h_calc : 0 + 10 * 50 = 500 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_500]
    have hy_50033 : digits 10 5003 = [3, 0, 0, 5] := by
      have h_add := digits_add 10 (by decide) 3 500 (by decide) (by decide)
      have h_calc : 3 + 10 * 500 = 5003 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_5003]
    have h50033 : digits 10 50033 = [3, 3, 0, 0, 5] := by
      have h_add := digits_add 10 (by decide) 3 5003 (by decide) (by decide)
      have h_calc : 3 + 10 * 5003 = 50033 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_50033]
    rw [h50034, h50033]
    rfl
  · norm_num

lemma a60012_ne_zero : a 60012 ≠ 0 := by
  apply a_ne_zero_helper 60012 6001260011 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 60012 - i) [0, 1] = [60012, 60011] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [60012, 60011] =
      (digits 10 60012).reverse ++ ((digits 10 60011).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_60 : digits 10 6 = [6] := digits_of_lt 10 6 (by decide) (by decide)
    have hy_600 : digits 10 60 = [0, 6] := by
      have h_add := digits_add 10 (by decide) 0 6 (by decide) (by decide)
      have h_calc : 0 + 10 * 6 = 60 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_60]
    have hy_6001 : digits 10 600 = [0, 0, 6] := by
      have h_add := digits_add 10 (by decide) 0 60 (by decide) (by decide)
      have h_calc : 0 + 10 * 60 = 600 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_600]
    have hy_60012 : digits 10 6001 = [1, 0, 0, 6] := by
      have h_add := digits_add 10 (by decide) 1 600 (by decide) (by decide)
      have h_calc : 1 + 10 * 600 = 6001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_6001]
    have h60012 : digits 10 60012 = [2, 1, 0, 0, 6] := by
      have h_add := digits_add 10 (by decide) 2 6001 (by decide) (by decide)
      have h_calc : 2 + 10 * 6001 = 60012 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_60012]
    have hy_60 : digits 10 6 = [6] := digits_of_lt 10 6 (by decide) (by decide)
    have hy_600 : digits 10 60 = [0, 6] := by
      have h_add := digits_add 10 (by decide) 0 6 (by decide) (by decide)
      have h_calc : 0 + 10 * 6 = 60 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_60]
    have hy_6001 : digits 10 600 = [0, 0, 6] := by
      have h_add := digits_add 10 (by decide) 0 60 (by decide) (by decide)
      have h_calc : 0 + 10 * 60 = 600 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_600]
    have hy_60011 : digits 10 6001 = [1, 0, 0, 6] := by
      have h_add := digits_add 10 (by decide) 1 600 (by decide) (by decide)
      have h_calc : 1 + 10 * 600 = 6001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_6001]
    have h60011 : digits 10 60011 = [1, 1, 0, 0, 6] := by
      have h_add := digits_add 10 (by decide) 1 6001 (by decide) (by decide)
      have h_calc : 1 + 10 * 6001 = 60011 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_60011]
    rw [h60012, h60011]
    rfl
  · norm_num

lemma a70024_ne_zero : a 70024 ≠ 0 := by
  apply a_ne_zero_helper 70024 7002470023 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 70024 - i) [0, 1] = [70024, 70023] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [70024, 70023] =
      (digits 10 70024).reverse ++ ((digits 10 70023).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_70 : digits 10 7 = [7] := digits_of_lt 10 7 (by decide) (by decide)
    have hy_700 : digits 10 70 = [0, 7] := by
      have h_add := digits_add 10 (by decide) 0 7 (by decide) (by decide)
      have h_calc : 0 + 10 * 7 = 70 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_70]
    have hy_7002 : digits 10 700 = [0, 0, 7] := by
      have h_add := digits_add 10 (by decide) 0 70 (by decide) (by decide)
      have h_calc : 0 + 10 * 70 = 700 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_700]
    have hy_70024 : digits 10 7002 = [2, 0, 0, 7] := by
      have h_add := digits_add 10 (by decide) 2 700 (by decide) (by decide)
      have h_calc : 2 + 10 * 700 = 7002 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_7002]
    have h70024 : digits 10 70024 = [4, 2, 0, 0, 7] := by
      have h_add := digits_add 10 (by decide) 4 7002 (by decide) (by decide)
      have h_calc : 4 + 10 * 7002 = 70024 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_70024]
    have hy_70 : digits 10 7 = [7] := digits_of_lt 10 7 (by decide) (by decide)
    have hy_700 : digits 10 70 = [0, 7] := by
      have h_add := digits_add 10 (by decide) 0 7 (by decide) (by decide)
      have h_calc : 0 + 10 * 7 = 70 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_70]
    have hy_7002 : digits 10 700 = [0, 0, 7] := by
      have h_add := digits_add 10 (by decide) 0 70 (by decide) (by decide)
      have h_calc : 0 + 10 * 70 = 700 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_700]
    have hy_70023 : digits 10 7002 = [2, 0, 0, 7] := by
      have h_add := digits_add 10 (by decide) 2 700 (by decide) (by decide)
      have h_calc : 2 + 10 * 700 = 7002 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_7002]
    have h70023 : digits 10 70023 = [3, 2, 0, 0, 7] := by
      have h_add := digits_add 10 (by decide) 3 7002 (by decide) (by decide)
      have h_calc : 3 + 10 * 7002 = 70023 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_70023]
    rw [h70024, h70023]
    rfl
  · norm_num

lemma a80004_ne_zero : a 80004 ≠ 0 := by
  apply a_ne_zero_helper 80004 8000480003 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 80004 - i) [0, 1] = [80004, 80003] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [80004, 80003] =
      (digits 10 80004).reverse ++ ((digits 10 80003).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_80 : digits 10 8 = [8] := digits_of_lt 10 8 (by decide) (by decide)
    have hy_800 : digits 10 80 = [0, 8] := by
      have h_add := digits_add 10 (by decide) 0 8 (by decide) (by decide)
      have h_calc : 0 + 10 * 8 = 80 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_80]
    have hy_8000 : digits 10 800 = [0, 0, 8] := by
      have h_add := digits_add 10 (by decide) 0 80 (by decide) (by decide)
      have h_calc : 0 + 10 * 80 = 800 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_800]
    have hy_80004 : digits 10 8000 = [0, 0, 0, 8] := by
      have h_add := digits_add 10 (by decide) 0 800 (by decide) (by decide)
      have h_calc : 0 + 10 * 800 = 8000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_8000]
    have h80004 : digits 10 80004 = [4, 0, 0, 0, 8] := by
      have h_add := digits_add 10 (by decide) 4 8000 (by decide) (by decide)
      have h_calc : 4 + 10 * 8000 = 80004 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_80004]
    have hy_80 : digits 10 8 = [8] := digits_of_lt 10 8 (by decide) (by decide)
    have hy_800 : digits 10 80 = [0, 8] := by
      have h_add := digits_add 10 (by decide) 0 8 (by decide) (by decide)
      have h_calc : 0 + 10 * 8 = 80 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_80]
    have hy_8000 : digits 10 800 = [0, 0, 8] := by
      have h_add := digits_add 10 (by decide) 0 80 (by decide) (by decide)
      have h_calc : 0 + 10 * 80 = 800 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_800]
    have hy_80003 : digits 10 8000 = [0, 0, 0, 8] := by
      have h_add := digits_add 10 (by decide) 0 800 (by decide) (by decide)
      have h_calc : 0 + 10 * 800 = 8000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_8000]
    have h80003 : digits 10 80003 = [3, 0, 0, 0, 8] := by
      have h_add := digits_add 10 (by decide) 3 8000 (by decide) (by decide)
      have h_calc : 3 + 10 * 8000 = 80003 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_80003]
    rw [h80004, h80003]
    rfl
  · norm_num

lemma a90018_ne_zero : a 90018 ≠ 0 := by
  apply a_ne_zero_helper 90018 9001890017 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 90018 - i) [0, 1] = [90018, 90017] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [90018, 90017] =
      (digits 10 90018).reverse ++ ((digits 10 90017).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_90 : digits 10 9 = [9] := digits_of_lt 10 9 (by decide) (by decide)
    have hy_900 : digits 10 90 = [0, 9] := by
      have h_add := digits_add 10 (by decide) 0 9 (by decide) (by decide)
      have h_calc : 0 + 10 * 9 = 90 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_90]
    have hy_9001 : digits 10 900 = [0, 0, 9] := by
      have h_add := digits_add 10 (by decide) 0 90 (by decide) (by decide)
      have h_calc : 0 + 10 * 90 = 900 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_900]
    have hy_90018 : digits 10 9001 = [1, 0, 0, 9] := by
      have h_add := digits_add 10 (by decide) 1 900 (by decide) (by decide)
      have h_calc : 1 + 10 * 900 = 9001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_9001]
    have h90018 : digits 10 90018 = [8, 1, 0, 0, 9] := by
      have h_add := digits_add 10 (by decide) 8 9001 (by decide) (by decide)
      have h_calc : 8 + 10 * 9001 = 90018 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_90018]
    have hy_90 : digits 10 9 = [9] := digits_of_lt 10 9 (by decide) (by decide)
    have hy_900 : digits 10 90 = [0, 9] := by
      have h_add := digits_add 10 (by decide) 0 9 (by decide) (by decide)
      have h_calc : 0 + 10 * 9 = 90 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_90]
    have hy_9001 : digits 10 900 = [0, 0, 9] := by
      have h_add := digits_add 10 (by decide) 0 90 (by decide) (by decide)
      have h_calc : 0 + 10 * 90 = 900 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_900]
    have hy_90017 : digits 10 9001 = [1, 0, 0, 9] := by
      have h_add := digits_add 10 (by decide) 1 900 (by decide) (by decide)
      have h_calc : 1 + 10 * 900 = 9001 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_9001]
    have h90017 : digits 10 90017 = [7, 1, 0, 0, 9] := by
      have h_add := digits_add 10 (by decide) 7 9001 (by decide) (by decide)
      have h_calc : 7 + 10 * 9001 = 90017 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_90017]
    rw [h90018, h90017]
    rfl
  · norm_num

lemma a100000_ne_zero : a 100000 ≠ 0 := by
  apply a_ne_zero_helper 100000 10000099999 1 (by decide)
  · dsimp only
    have h_range : List.range (1 + 1) = [0, 1] := rfl
    have h_map : List.map (fun i => 100000 - i) [0, 1] = [100000, 99999] := rfl
    rw [h_range, h_map]
    have h_foldr : List.foldr (fun num acc_digits => (digits 10 num).reverse ++ acc_digits) [] [100000, 99999] =
      (digits 10 100000).reverse ++ ((digits 10 99999).reverse ++ []) := rfl
    rw [h_foldr]
    have hy_10 : digits 10 1 = [1] := digits_of_lt 10 1 (by decide) (by decide)
    have hy_100 : digits 10 10 = [0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1 (by decide) (by decide)
      have h_calc : 0 + 10 * 1 = 10 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10]
    have hy_1000 : digits 10 100 = [0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10 (by decide) (by decide)
      have h_calc : 0 + 10 * 10 = 100 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100]
    have hy_10000 : digits 10 1000 = [0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 100 (by decide) (by decide)
      have h_calc : 0 + 10 * 100 = 1000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_1000]
    have hy_100000 : digits 10 10000 = [0, 0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 1000 (by decide) (by decide)
      have h_calc : 0 + 10 * 1000 = 10000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_10000]
    have h100000 : digits 10 100000 = [0, 0, 0, 0, 0, 1] := by
      have h_add := digits_add 10 (by decide) 0 10000 (by decide) (by decide)
      have h_calc : 0 + 10 * 10000 = 100000 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_100000]
    have hy_99 : digits 10 9 = [9] := digits_of_lt 10 9 (by decide) (by decide)
    have hy_999 : digits 10 99 = [9, 9] := by
      have h_add := digits_add 10 (by decide) 9 9 (by decide) (by decide)
      have h_calc : 9 + 10 * 9 = 99 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_99]
    have hy_9999 : digits 10 999 = [9, 9, 9] := by
      have h_add := digits_add 10 (by decide) 9 99 (by decide) (by decide)
      have h_calc : 9 + 10 * 99 = 999 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_999]
    have hy_99999 : digits 10 9999 = [9, 9, 9, 9] := by
      have h_add := digits_add 10 (by decide) 9 999 (by decide) (by decide)
      have h_calc : 9 + 10 * 999 = 9999 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_9999]
    have h99999 : digits 10 99999 = [9, 9, 9, 9, 9] := by
      have h_add := digits_add 10 (by decide) 9 9999 (by decide) (by decide)
      have h_calc : 9 + 10 * 9999 = 99999 := by rfl
      rw [h_calc] at h_add
      rw [h_add, hy_99999]
    rw [h100000, h99999]
    rfl
  · norm_num


/-- Conjecture; There are infinitely many composite numbers n such that a(n) is nonzero. -/
theorem oeis_a087571_conjecture :
  -- The set of N such that N > 1 and N is composite and a(N) != 0 is infinite.
  ∀ M : ℕ, ∃ n : ℕ, n > M ∧ (n > 1 ∧ ¬ Nat.Prime n) ∧ a n ≠ 0 := by
  intro M
  by_cases h4 : M < 4
  · use 4
    refine ⟨h4, ?_⟩
    constructor
    · norm_num
    · exact a4_ne_zero
  · by_cases h10 : M < 10
    · use 10
      refine ⟨h10, ?_⟩
      constructor
      · norm_num
      · exact a10_ne_zero
    · by_cases h22 : M < 22
      · use 22
        refine ⟨h22, ?_⟩
        constructor
        · norm_num
        · exact a22_ne_zero
      · by_cases h202 : M < 202
        · use 202
          refine ⟨h202, ?_⟩
          constructor
          · norm_num
          · exact a202_ne_zero
        · by_cases h304 : M < 304
          · use 304
            refine ⟨h304, ?_⟩
            constructor
            · norm_num
            · exact a304_ne_zero
          · by_cases h1002 : M < 1002
            · use 1002
              refine ⟨h1002, ?_⟩
              constructor
              · norm_num
              · exact a1002_ne_zero
            · by_cases h10008 : M < 10008
              · use 10008
                refine ⟨h10008, ?_⟩
                constructor
                · norm_num
                · exact a10008_ne_zero
              · by_cases h10014 : M < 10014
                · use 10014
                  refine ⟨h10014, ?_⟩
                  constructor
                  · norm_num
                  · exact a10014_ne_zero
                · by_cases h20004 : M < 20004
                  · use 20004
                    refine ⟨h20004, ?_⟩
                    constructor
                    · norm_num
                    · exact a20004_ne_zero
                  · by_cases h30034 : M < 30034
                    · use 30034
                      refine ⟨h30034, ?_⟩
                      constructor
                      · norm_num
                      · exact a30034_ne_zero
                    · by_cases h40054 : M < 40054
                      · use 40054
                        refine ⟨h40054, ?_⟩
                        constructor
                        · norm_num
                        · exact a40054_ne_zero
                      · by_cases h50034 : M < 50034
                        · use 50034
                          refine ⟨h50034, ?_⟩
                          constructor
                          · norm_num
                          · exact a50034_ne_zero
                        · by_cases h60012 : M < 60012
                          · use 60012
                            refine ⟨h60012, ?_⟩
                            constructor
                            · norm_num
                            · exact a60012_ne_zero
                          · by_cases h70024 : M < 70024
                            · use 70024
                              refine ⟨h70024, ?_⟩
                              constructor
                              · norm_num
                              · exact a70024_ne_zero
                            · by_cases h80004 : M < 80004
                              · use 80004
                                refine ⟨h80004, ?_⟩
                                constructor
                                · norm_num
                                · exact a80004_ne_zero
                              · by_cases h90018 : M < 90018
                                · use 90018
                                  refine ⟨h90018, ?_⟩
                                  constructor
                                  · norm_num
                                  · exact a90018_ne_zero
                                · by_cases h100000 : M < 100000
                                  · use 100000
                                    refine ⟨h100000, ?_⟩
                                    constructor
                                    · norm_num
                                    · exact a100000_ne_zero
                                  · sorry
