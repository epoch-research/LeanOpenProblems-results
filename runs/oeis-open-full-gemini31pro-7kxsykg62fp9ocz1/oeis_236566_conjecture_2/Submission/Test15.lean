import Mathlib

def a236566_conjecture_part_ii : Prop :=
  ∀ n : ℕ, 30 < n → ∃ (p q : ℕ),
    Nat.Prime p ∧
    Nat.Prime q ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2) ∧
    2 * n + 1 = 2 * p + q

def S := {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)}

lemma S_infinite (h : a236566_conjecture_part_ii) : Set.Infinite S := by
  intro h_fin
  have h_finset : ∃ F : Finset ℕ, ∀ x, x ∈ F ↔ x ∈ S := by
    classical exact ⟨h_fin.toFinset, fun x => Set.Finite.mem_toFinset _⟩
  rcases h_finset with ⟨F, hF⟩
  let N0 := F.sup (fun x => x)
  let N := max 30 N0
  have h_le : ∀ p ∈ S, p ≤ N := by
    intro p hp
    have h1 : p ∈ F := (hF p).mpr hp
    have h2 : p ≤ N0 := Finset.le_sup (f := id) h1
    omega
  let N2 := 2 * N + 2
  let M := N2.factorial
  let n := M / 2
  have hM_even : 2 ∣ M := by
    apply Nat.dvd_factorial (by decide)
    have : N ≥ 30 := by exact le_max_left 30 N0
    omega
  have hM : M = 2 * n := by
    have : M / 2 * 2 = M := Nat.div_mul_cancel hM_even
    omega
  have hn_gt : n > 30 := by
    have hN2 : N2 ≥ 62 := by
      have : N ≥ 30 := by exact le_max_left 30 N0
      omega
    have : N2.factorial ≥ 62 := by
      apply Nat.le_trans (m := N2)
      · omega
      · apply Nat.self_le_factorial
    omega
  obtain ⟨p, q, hp, hq, hpS, heq⟩ := h n hn_gt
  have hp_in_S : p ∈ S := ⟨hp, hpS⟩
  have hp_le_N : p ≤ N := h_le p hp_in_S
  have h_2p_sub_1_gt_0 : 2 * p - 1 > 0 := by
    have : p ≥ 2 := hp.two_le
    omega
  have h_2p_sub_1_le_N2 : 2 * p - 1 ≤ N2 := by
    omega
  have h_div : 2 * p - 1 ∣ M := Nat.dvd_factorial h_2p_sub_1_gt_0 h_2p_sub_1_le_N2
  have h_q_eq : q = M - (2 * p - 1) := by
    have h1 : 2 * n + 1 = 2 * p + q := heq
    have h2 : M + 1 = 2 * p + q := by omega
    have : p ≥ 2 := hp.two_le
    omega
  have h_q_div : 2 * p - 1 ∣ q := by
    rw [h_q_eq]
    apply Nat.dvd_sub
    · exact h_div
    · exact dvd_rfl
  have h_q_gt : q > 2 * p - 1 := by
    rw [h_q_eq]
    have hp2 : p ≥ 2 := hp.two_le
    have : 2 * p - 1 ≤ 2 * N + 1 := by omega
    have hN_30 : N ≥ 30 := by exact le_max_left 30 N0
    have h_fac : M > 4 * N := by
      have h1 : 2 * N + 2 = (2 * N + 1) + 1 := by omega
      have h2 : (2 * N + 2).factorial = (2 * N + 2) * (2 * N + 1).factorial := by
        rw [h1, Nat.factorial_succ]
      have h3 : (2 * N + 1).factorial ≥ 2 := by
        apply Nat.le_trans (m := 2 * N + 1)
        · omega
        · apply Nat.self_le_factorial
      nlinarith
    omega
  have h_q_comp : ¬ Nat.Prime q := by
    intro hq_prime
    have := hq_prime.eq_one_or_self_of_dvd (2 * p - 1) h_q_div
    rcases this with h1 | h2
    · have : p ≥ 2 := hp.two_le
      omega
    · omega
  exact h_q_comp hq
