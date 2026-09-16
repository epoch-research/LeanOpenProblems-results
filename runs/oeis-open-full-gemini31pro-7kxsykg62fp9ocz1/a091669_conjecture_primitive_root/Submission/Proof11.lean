import Mathlib
import Submission.Spec
import Submission.Proof8
import Submission.Proof10

open Nat BigOperators

lemma p_pow_dvd_P (n p : ℕ) [Fact p.Prime] (hn2 : n > 2) (hodd : p > 2) :
  p ^ ((n - 2) / (p - 1)) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
  let k := (n - 2) / (p - 1)
  let S := (Finset.Ico 1 (k + 1)).image (fun j => j * (p - 1))
  have h_sub : S ⊆ Finset.Ico 1 (n - 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [Finset.mem_Ico] at hj ⊢
    constructor
    · have : p - 1 ≥ 2 := by omega
      have : j ≥ 1 := hj.1
      nlinarith
    · have h_k_def : k = (n - 2) / (p - 1) := rfl
      have hj_le_k : j ≤ k := by omega
      have h1 : j * (p - 1) ≤ k * (p - 1) := Nat.mul_le_mul_right (p - 1) hj_le_k
      have h2 : k * (p - 1) ≤ n - 2 := by
        rw [h_k_def]
        exact Nat.div_mul_le_self (n - 2) (p - 1)
      have h3 : j * (p - 1) ≤ n - 2 := le_trans h1 h2
      have : n ≥ 3 := hn2
      omega
  have h_dvd : ∀ x ∈ S, p ∣ 2 ^ x - 1 := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨j, _, rfl⟩
    exact fermat p hodd j
  have h_prod : p ^ S.card ∣ S.prod (fun k => 2 ^ k - 1) := dvd_prod_of_dvd h_dvd
  have h_card : S.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have : p - 1 > 0 := by omega
      exact Nat.eq_of_mul_eq_mul_right this hab
  rw [h_card] at h_prod
  have h_dvd_prod : S.prod (fun k => 2 ^ k - 1) ∣ (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) := by
    exact Finset.prod_dvd_prod_of_subset S (Finset.Ico 1 (n - 1)) (fun k => 2^k - 1) h_sub
  exact dvd_trans h_prod h_dvd_prod
