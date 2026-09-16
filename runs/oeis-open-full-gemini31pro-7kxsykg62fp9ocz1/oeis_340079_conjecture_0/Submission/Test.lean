import Mathlib

open Nat BigOperators Finset

def A018804 (n : ℕ) : ℕ := (Ico 1 (n + 1)).sum fun k => Nat.gcd k n
def a (n : ℕ) : ℕ := n / Nat.gcd n (1 + A018804 n)

lemma A018804_eq_sum_divisors (n : ℕ) (hn : 0 < n) :
  A018804 n = ∑ d ∈ n.divisors, d * (n / d).totient := by
  have H1 : A018804 n = ∑ k ∈ range n, k.gcd n := by
    unfold A018804
    have h1 : range n = insert 0 (Ico 1 n) := by
      ext x; simp [mem_range, mem_insert, mem_Ico]; omega
    have h2 : Ico 1 (n + 1) = insert n (Ico 1 n) := by
      ext x; simp [mem_Ico, mem_insert]; omega
    rw [h1, h2]
    have hd1 : 0 ∉ Ico 1 n := by simp
    have hd2 : n ∉ Ico 1 n := by simp
    rw [sum_insert hd1, sum_insert hd2, gcd_zero_left, gcd_self]
  rw [H1]
  have H2 : ∑ k ∈ range n, k.gcd n = ∑ k ∈ range n, n.gcd k := by
    apply sum_congr rfl
    intro k _
    rw [gcd_comm]
  rw [H2]
  have H3 : ∑ k ∈ range n, n.gcd k = ∑ d ∈ n.divisors, ∑ k ∈ filter (fun k => n.gcd k = d) (range n), n.gcd k := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro k hk
    rw [mem_divisors]
    exact ⟨Nat.gcd_dvd_left n k, hn.ne'⟩
  rw [H3]
  apply sum_congr rfl
  intro d hd
  have H4 : ∑ k ∈ filter (fun k => n.gcd k = d) (range n), n.gcd k = ∑ k ∈ filter (fun k => n.gcd k = d) (range n), d := by
    apply sum_congr rfl
    intro k hk
    rw [mem_filter] at hk
    exact hk.2
  rw [H4, sum_const]
  have H5 : (filter (fun k => n.gcd k = d) (range n)).card = (n / d).totient := by
    rw [mem_divisors] at hd
    exact (totient_div_of_dvd hd.1).symm
  rw [H5, smul_eq_mul, mul_comm]

lemma a_not_one {n : ℕ} (hn : n > 1) (hp : ¬ Nat.Prime n) : a n ≠ 1 := by
  intro h
  have H : Nat.gcd n (1 + A018804 n) = n := by
    have h1 : n / Nat.gcd n (1 + A018804 n) = 1 := h
    have h2 : Nat.gcd n (1 + A018804 n) ∣ n := Nat.gcd_dvd_left _ _
    have h3 : 0 < Nat.gcd n (1 + A018804 n) := by
      apply Nat.gcd_pos_of_pos_left
      exact gt_trans hn Nat.zero_lt_one
    exact ((Nat.div_eq_iff_eq_mul_right h3 h2).mp h1 |>.trans (mul_one _)).symm
  have H2 : n ∣ 1 + A018804 n := by
    have h1 : Nat.gcd n (1 + A018804 n) ∣ 1 + A018804 n := Nat.gcd_dvd_right _ _
    rwa [H] at h1
  sorry
