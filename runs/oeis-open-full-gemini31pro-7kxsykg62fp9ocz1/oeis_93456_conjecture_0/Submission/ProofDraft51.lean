import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

lemma sum_subset_le (s t : Finset ℕ) (f : ℕ → ℕ) (h : s ⊆ t) :
  ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  exact sum_le_sum_of_subset h

lemma algebra_ineq (p M x : ℕ) (hp5 : 5 ≤ p) (hx : M - p + 3 ≤ x) (hM : p ≤ M) :
  p * M - p * p + 2 * p + 2 ≤ p * x := by
  zify [show p * p ≤ p * M by nlinarith, show p ≤ M by nlinarith]
  have hz : (M : ℤ) - (p : ℤ) + 3 ≤ (x : ℤ) := by
    zify [show p ≤ M by nlinarith] at hx
    exact hx
  nlinarith

lemma image_subset_S (p n M : ℕ) (hp5 : 5 ≤ p)
  (h_R : n * (n - 1) / 2 = p * M)
  (h_L : n * (n - 1) / 2 - n + 2 = p * M - p * p + 2 * p + 2)
  (hM : p ≤ M) :
  (Icc (M - p + 3) M).image (fun x => p * x) ⊆
  (Icc (n * (n - 1) / 2 - n + 2) (n * (n - 1) / 2)).filter (fun k => 1 < k ∧ ¬ k.Prime) := by
  intro y
  simp only [mem_image, mem_filter, mem_Icc]
  rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [h_L]
    exact algebra_ineq p M x hp5 hx1 hM
  · rw [h_R]
    exact Nat.mul_le_mul_left p hx2
  · have : p * 1 < p * x := by
      apply Nat.mul_lt_mul_of_pos_left
      · have : 3 ≤ M - p + 3 := by omega
        omega
      · omega
    omega
  · intro h_prime
    have hdvd : p ∣ p * x := dvd_mul_right p x
    have hx_gt1 : 1 < x := by
      have : 3 ≤ M - p + 3 := by omega
      omega
    have hp_gt1 : 1 < p := by omega
    have := h_prime.eq_one_or_self_of_dvd p hdvd
    rcases this with h1 | h2
    · omega
    · have : x = 1 := by nlinarith
      omega

lemma padicValNat_le_one (p c d : ℕ) [Fact p.Prime] (h1 : 1 ≤ d) (h2 : d ≤ p - 2) :
  padicValNat p (p * (c * p + 1 + d)) = 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have h_ne : c * p + 1 + d ≠ 0 := by omega
  rw [padicValNat.mul hp.ne_zero h_ne]
  have h_self : padicValNat p p = 1 := padicValNat.self hp1
  rw [h_self]
  have h_not_dvd : ¬ (p ∣ c * p + 1 + d) := by
    intro hdvd
    have h1_dvd : p ∣ c * p := dvd_mul_left p c
    have hdvd_add : p ∣ (c * p) + (1 + d) := by
      have : c * p + 1 + d = (c * p) + (1 + d) := by omega
      rw [← this]
      exact hdvd
    have h2_dvd : p ∣ 1 + d := by
      exact (Nat.dvd_add_iff_right h1_dvd).mpr hdvd_add
    have : 1 + d = p := by
      apply le_antisymm
      · omega
      · exact Nat.le_of_dvd (by omega) h2_dvd
    omega
  have hz : padicValNat p (c * p + 1 + d) = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
  omega
