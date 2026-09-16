import Mathlib

open Equiv Equiv.Perm Finset Matrix

lemma sum_range_id_mul_two' (p : ℕ) : 2 * Finset.sum (Finset.range p) (fun x => x) = p * (p - 1) := by
  induction' p with p ih
  · simp
  · rw [Finset.sum_range_succ, mul_add, ih]
    cases p with
    | zero => simp
    | succ n =>
      have : n + 1 + 1 - 1 = n + 1 := rfl
      rw [this]
      have : n + 1 - 1 = n := rfl
      rw [this]
      ring

lemma sum_fin_nat (p : ℕ) : 2 * Finset.sum Finset.univ (fun (i : Fin p) => (i : ℕ)) = p * (p - 1) := by
  have H : Finset.sum Finset.univ (fun (i : Fin p) => (i : ℕ)) = Finset.sum (Finset.range p) (fun x => x) := Fin.sum_univ_eq_sum_range (fun (i : ℕ) => i) p
  rw [H, sum_range_id_mul_two']

lemma sum_i_add_sigma_i (p : ℕ) (σ : Perm (Fin p)) :
    ∑ i : Fin p, ((i : ℕ) + (σ i : ℕ)) = p * (p - 1) := by
  have H : ∑ i : Fin p, (σ i : ℕ) = ∑ i : Fin p, (i : ℕ) :=
    Equiv.sum_comp σ (fun i => (i : ℕ))
  calc ∑ i : Fin p, ((i : ℕ) + (σ i : ℕ))
    _ = ∑ i : Fin p, (i : ℕ) + ∑ i : Fin p, (σ i : ℕ) := sum_add_distrib
    _ = 2 * ∑ i : Fin p, (i : ℕ) := by rw [H, two_mul]
    _ = p * (p - 1) := sum_fin_nat p

lemma anti_diagonal_perm (p : ℕ) (hp : 0 < p) (σ : Perm (Fin p))
    (h : ∀ i : Fin p, (i : ℕ) + (σ i : ℕ) ≤ p - 1) :
    ∀ i : Fin p, (i : ℕ) + (σ i : ℕ) = p - 1 := by
  have h_sum : ∑ i : Fin p, ((i : ℕ) + (σ i : ℕ)) = ∑ i : Fin p, (p - 1) := by
    rw [sum_i_add_sigma_i p σ, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  intro i
  have h_le : ∀ j ∈ (univ : Finset (Fin p)), (j : ℕ) + (σ j : ℕ) ≤ p - 1 := fun j _ => h j
  have h2 := (sum_eq_sum_iff_of_le h_le).mp h_sum
  exact h2 i (mem_univ i)
