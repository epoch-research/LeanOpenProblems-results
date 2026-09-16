import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma sum_image_px (p M : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hM : p ∣ M - 1) (hM_ge : p ≤ M) :
  p - 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) := by
  have H1 : ∑ x ∈ Icc (M - p + 3) M, padicValNat p (p * x) =
            ∑ x ∈ Icc (M - p + 3) M, (1 + padicValNat p x) := by
    apply sum_congr rfl
    intro x hx
    have hp_ne : p ≠ 0 := by omega
    have hx_ne : x ≠ 0 := by
      rw [mem_Icc] at hx
      omega
    rw [padicValNat.mul hp_ne hx_ne]
    have hp_prime : p.Prime := Fact.out
    have : padicValNat p p = 1 := padicValNat.self hp_prime.one_lt
    rw [this]
  rw [H1]
  have H2 : ∑ x ∈ Icc (M - p + 3) M, (1 + padicValNat p x) =
            (Icc (M - p + 3) M).card + ∑ x ∈ Icc (M - p + 3) M, padicValNat p x := by
    rw [sum_add_distrib, sum_const]
    simp
  rw [H2, Nat.card_Icc]
  have H3 : M + 1 - (M - p + 3) = p - 2 := by omega
  rw [H3]
  have H4 : 1 ≤ padicValNat p (M - 1) := by
    have h_ne : M - 1 ≠ 0 := by omega
    exact one_le_padicValNat_of_dvd h_ne hM
  have H5 : M - 1 ∈ Icc (M - p + 3) M := by
    rw [mem_Icc]
    constructor <;> omega
  have H6 : 1 ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p x := by
    have : padicValNat p (M - 1) ≤ ∑ x ∈ Icc (M - p + 3) M, padicValNat p x :=
      single_le_sum (fun _ _ => zero_le _) H5
    omega
  omega
