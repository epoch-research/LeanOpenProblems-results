import Submission.Test12

open Nat
open Finset

lemma sum_digitsFromExponents (X : List ℕ) (max_exp : ℕ) (h_max : ∀ x ∈ X, x < max_exp) (h_dup : X.Nodup) :
    (digitsFromExponents X max_exp).sum = X.length := by
  dsimp [digitsFromExponents]
  rw [List.sum_ofFn]
  have Hsum : (∑ i : Fin max_exp, (if (i:ℕ) ∈ X then 1 else 0)) = ∑ i ∈ range max_exp, if i ∈ X then 1 else 0 := by
    exact (sum_range (fun i => if i ∈ X then 1 else 0)).symm
  rw [Hsum]
  have H3 : (∑ i ∈ range max_exp, if i ∈ X then 1 else 0) = ∑ i ∈ (range max_exp).filter (· ∈ X), 1 := by
    exact (sum_filter _ _).symm
  rw [H3]
  have H4 : (range max_exp).filter (· ∈ X) = X.toFinset := by
    ext a
    simp only [mem_filter, mem_range, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨h_max a h, h⟩⟩
  rw [H4, sum_const, nsmul_eq_mul, mul_one, List.toFinset_card_of_nodup h_dup]

lemma digitsFromExponents_lt (X : List ℕ) (max_exp : ℕ) (x : ℕ) (hx : x ∈ digitsFromExponents X max_exp) :
    x < 10 := by
  dsimp [digitsFromExponents] at hx
  rw [List.mem_ofFn] at hx
  rcases hx with ⟨i, rfl⟩
  split_ifs
  · decide
  · decide

lemma digitsFromExponents_length (X : List ℕ) (max_exp : ℕ) :
    (digitsFromExponents X max_exp).length = max_exp := by
  dsimp [digitsFromExponents]
  exact List.length_ofFn _
