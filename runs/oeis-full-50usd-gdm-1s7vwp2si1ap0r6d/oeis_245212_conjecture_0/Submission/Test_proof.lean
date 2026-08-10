import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma card_divisors_le_of_proper_divisor (m d : ℕ) (hm : m ≠ 0) (hd : d ∈ m.properDivisors) :
    d.divisors.card + 1 ≤ m.divisors.card := by
  rw [mem_properDivisors] at hd
  have hd_div : d.divisors ⊆ m.divisors := by
    intro x hx
    rw [mem_divisors] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    constructor
    · exact dvd_trans hx1 hd.1
    · exact hm
  have hm_notin : m ∉ d.divisors := by
    rw [mem_divisors]
    rintro ⟨h1, h2⟩
    have h_le := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
    omega
  have hm_in : m ∈ m.divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, hm⟩
  have h_insert : insert m d.divisors ⊆ m.divisors := by
    rw [insert_subset_iff]
    exact ⟨hm_in, hd_div⟩
  have h_card := card_le_card h_insert
  rw [card_insert_of_notMem hm_notin] at h_card
  exact h_card

def sigma (n : ℕ) : ℤ :=
  n.divisors.sum (fun d => (d : ℤ))

lemma sum_properDivisors_eq_sigma_sub_self (m : ℕ) (hm : m ≠ 0) :
    m.properDivisors.sum (fun d => (d : ℤ)) = sigma m - m := by
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors hm).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  rw [sigma]
  rw [h_insert, sum_insert h_not_mem]
  push_cast
  ring

lemma C_plus_S_le_m_plus_tau_S (m : ℕ) (hm : m ≠ 0) :
    m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) ≤
    (m : ℤ) + (m.divisors.card : ℤ) * sigma m := by
  have h_insert : m.divisors = insert m m.properDivisors := by
    exact (insert_self_properDivisors hm).symm
  have h_not_mem : m ∉ m.properDivisors := self_notMem_properDivisors
  have h_eq : m.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) =
      (m : ℤ) * (m.divisors.card : ℤ) + (m : ℤ) +
      m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) := by
    nth_rw 1 [h_insert]
    rw [sum_insert h_not_mem]
  rw [h_eq]
  have h_le : m.properDivisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ) + (d : ℤ)) ≤
      m.properDivisors.sum (fun d => (d : ℤ) * (m.divisors.card : ℤ)) := by
    apply sum_le_sum
    intro d hd
    have h_card := card_divisors_le_of_proper_divisor m d hm hd
    have h_d_pos : (d : ℤ) ≥ 0 := by positivity
    nlinarith
  have h_sum_prop : m.properDivisors.sum (fun d => (d : ℤ) * (m.divisors.card : ℤ)) =
      (m.divisors.card : ℤ) * m.properDivisors.sum (fun d => (d : ℤ)) := by
    rw [← sum_mul]
    ring


  rw [h_sum_prop] at h_le
  rw [sum_properDivisors_eq_sigma_sub_self m hm] at h_le
  linarith


