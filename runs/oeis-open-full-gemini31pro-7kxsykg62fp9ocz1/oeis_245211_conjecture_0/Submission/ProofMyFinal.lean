import Mathlib

open Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  let full_sum := (Nat.divisors n).sum (fun d => d * (Nat.divisors d).card)
  let self_term := n * (Nat.divisors n).card
  full_sum - self_term

lemma a_eq_sum_proper {n : ℕ} (hn : 0 < n) :
  a n = ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := by
  unfold a
  have h_in : n ∈ n.divisors := by rw [Nat.mem_divisors]; exact ⟨dvd_refl n, hn.ne.symm⟩
  have h_split := Finset.sum_erase_add n.divisors (fun d => d * (Nat.divisors d).card) h_in
  rw [add_comm] at h_split
  dsimp
  rw [← h_split]
  exact Nat.add_sub_cancel_left _ _
  have h_divs : p.divisors = {1, p} := Nat.Prime.divisors hp
  have h_ne : 1 ≠ p := by
    have := hp.two_le
    omega
  have h_not_mem : 1 ∉ ({p} : Finset ℕ) := by rw [mem_singleton]; exact h_ne
  have h_taup : (Nat.divisors p).card = 2 := by
    rw [h_divs, card_insert_of_notMem h_not_mem, card_singleton]
  unfold a
  change p.divisors.sum (fun d => d * (Nat.divisors d).card) - p * p.divisors.card = 1
  rw [h_divs]
  have h_card : ({1, p} : Finset ℕ).card = 2 := by
    exact card_insert_of_notMem h_not_mem |>.trans (by rw [card_singleton])
  have h_sum : ({1, p} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 1 + 2 * p := by
    rw [sum_insert h_not_mem, sum_singleton]
    have h_tau1 : (Nat.divisors 1).card = 1 := rfl
    rw [h_tau1, h_taup]
    ring
  rw [h_card, h_sum]
  omega

lemma a_p2 (p : ℕ) (hp : p.Prime) : a (p ^ 2) = 1 + 2 * p := by
  have h_divs : (p ^ 2).divisors = {p ^ 2, p, 1} := hp.divisors_sq
  have h_ne1 : p ≠ p ^ 2 := by have := hp.two_le; nlinarith
  have h_ne2 : 1 ≠ p ^ 2 := by have := hp.two_le; nlinarith
  have h_ne3 : 1 ≠ p := by have := hp.two_le; omega
  have h_not_mem1 : p ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne3.symm
  have h_not_mem2 : p ^ 2 ∉ ({p, 1} : Finset ℕ) := by
    rw [mem_insert, mem_singleton]
    push_neg
    exact ⟨h_ne1.symm, h_ne2.symm⟩
  have h_tau_p2 : (Nat.divisors (p ^ 2)).card = 3 := by
    rw [h_divs, card_insert_of_notMem h_not_mem2, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_not_mem3 : p ∉ ({1} : Finset ℕ) := h_not_mem1
  have h_tau_p : (Nat.divisors p).card = 2 := by
    have : p.divisors = {p, 1} := by
      ext x
      rw [hp.divisors, mem_insert, mem_insert, mem_singleton, mem_singleton]
      tauto
    rw [this, card_insert_of_notMem h_not_mem3, card_singleton]
  have h_tau_1 : (Nat.divisors 1).card = 1 := rfl
  unfold a
  change (p ^ 2).divisors.sum (fun d => d * (Nat.divisors d).card) - (p ^ 2) * (p ^ 2).divisors.card = 1 + 2 * p
  rw [h_divs]
  have h_card : ({p ^ 2, p, 1} : Finset ℕ).card = 3 := by
    exact card_insert_of_notMem h_not_mem2 |>.trans (by rw [card_insert_of_notMem h_not_mem1, card_singleton])
  have h_sum : ({p ^ 2, p, 1} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 3 * (p ^ 2) + 2 * p + 1 := by
    rw [sum_insert h_not_mem2, sum_insert h_not_mem1, sum_singleton]
    rw [h_tau_1, h_tau_p, h_tau_p2]
    ring
  rw [h_card, h_sum]
  omega

lemma divisors_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
  (p * q).divisors = {p * q, q, p, 1} := by
  have hd_p : p.divisors = {1, p} := hp.divisors
  have hd_q : q.divisors = {1, q} := hq.divisors
  rw [Nat.divisors_mul, hd_p, hd_q]
  ext x
  rw [mem_mul]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rcases hy with rfl | rfl
    · rcases hz with rfl | rfl
      · right; right; right; ring
      · right; left; ring
    · rcases hz with rfl | rfl
      · right; right; left; ring
      · left; ring
  · intro hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact ⟨p, by right; rfl, q, by right; rfl, by ring⟩
    · rw [hx]; exact ⟨1, by left; rfl, q, by right; rfl, by ring⟩
    · rw [hx]; exact ⟨p, by right; rfl, 1, by left; rfl, by ring⟩
    · rw [hx]; exact ⟨1, by left; rfl, 1, by left; rfl, by ring⟩

lemma a_pq (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : a (p * q) = 1 + 2 * p + 2 * q := by
  have h_divs := divisors_pq hp hq hpq
  have h_ne1 : p * q ≠ q := by
    intro h
    have : p * q = 1 * q := by rw [h, one_mul]
    have hp1 : p = 1 := mul_right_cancel₀ hq.pos.ne.symm this
    have := hp.two_le; omega
  have h_ne2 : p * q ≠ p := by
    intro h
    have : p * q = p * 1 := by rw [h, mul_one]
    have hq1 : q = 1 := mul_left_cancel₀ hp.pos.ne.symm this
    have := hq.two_le; omega
  have h_ne3 : p * q ≠ 1 := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have h_ne4 : q ≠ p := hpq.symm
  have h_ne5 : q ≠ 1 := by have := hq.two_le; omega
  have h_ne6 : p ≠ 1 := by have := hp.two_le; omega
  
  have h_not_mem1 : p ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne6
  have h_not_mem2 : q ∉ ({p, 1} : Finset ℕ) := by
    rw [mem_insert, mem_singleton]
    push_neg
    exact ⟨h_ne4, h_ne5⟩
  have h_not_mem3 : p * q ∉ ({q, p, 1} : Finset ℕ) := by
    rw [mem_insert, mem_insert, mem_singleton]
    push_neg
    exact ⟨h_ne1, h_ne2, h_ne3⟩
    
  have h_tau_p : (Nat.divisors p).card = 2 := by
    have hd : p.divisors = {p, 1} := by
      ext x
      rw [hp.divisors, mem_insert, mem_insert, mem_singleton, mem_singleton]
      tauto
    rw [hd, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_tau_q : (Nat.divisors q).card = 2 := by
    have hq_not : q ∉ ({1} : Finset ℕ) := by rw [mem_singleton]; exact h_ne5
    have hd : q.divisors = {q, 1} := by
      ext x
      rw [hq.divisors, mem_insert, mem_insert, mem_singleton, mem_singleton]
      tauto
    rw [hd, card_insert_of_notMem hq_not, card_singleton]
  have h_tau_pq : (Nat.divisors (p * q)).card = 4 := by
    rw [h_divs, card_insert_of_notMem h_not_mem3, card_insert_of_notMem h_not_mem2, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_tau_1 : (Nat.divisors 1).card = 1 := rfl
  
  unfold a
  change (p * q).divisors.sum (fun d => d * (Nat.divisors d).card) - (p * q) * (p * q).divisors.card = 1 + 2 * p + 2 * q
  rw [h_divs]
  
  have h_card : ({p * q, q, p, 1} : Finset ℕ).card = 4 := by
    rw [card_insert_of_notMem h_not_mem3, card_insert_of_notMem h_not_mem2, card_insert_of_notMem h_not_mem1, card_singleton]
  have h_sum : ({p * q, q, p, 1} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 4 * (p * q) + 2 * q + 2 * p + 1 := by
    rw [sum_insert h_not_mem3, sum_insert h_not_mem2, sum_insert h_not_mem1, sum_singleton]
    rw [h_tau_1, h_tau_p, h_tau_q, h_tau_pq]
    ring
  rw [h_card, h_sum]
  omega

lemma mul_eq_5 {a b : ℕ} (h : a * b = 5) : (a = 1 ∧ b = 5) ∨ (a = 5 ∧ b = 1) := by
  have ha : a ≤ 5 := by
    have : a ∣ 5 := ⟨b, h.symm⟩
    exact Nat.le_of_dvd (by decide) this
  interval_cases a
  · norm_num at h
  · left; constructor; rfl; linarith
  · omega
  · omega
  · omega
  · right; constructor; rfl; linarith

lemma pq_eq_21 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h_eq : a (p * q) = p * q) : p * q = 21 := by
  have h_val := a_pq p q hp hq hpq
  rw [h_eq] at h_val
  have h_eq2 : (p - 2) * (q - 2) = 5 := by
    have hp2 : 2 ≤ p := hp.two_le
    have hq2 : 2 ≤ q := hq.two_le
    have h_val_z : (p * q : ℤ) = 1 + 2 * (p : ℤ) + 2 * (q : ℤ) := by exact_mod_cast h_val
    have h_z : ((p : ℤ) - 2) * ((q : ℤ) - 2) = 5 := by
      calc ((p : ℤ) - 2) * ((q : ℤ) - 2) = (p * q : ℤ) - 2 * (p : ℤ) - 2 * (q : ℤ) + 4 := by ring
        _ = 1 + 2 * (p : ℤ) + 2 * (q : ℤ) - 2 * (p : ℤ) - 2 * (q : ℤ) + 4 := by rw [h_val_z]
        _ = 5 := by ring
    exact_mod_cast h_z
  have h_cases := mul_eq_5 h_eq2
  rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : p = 3 := by omega
    have : q = 7 := by omega
    omega
  · have : p = 7 := by omega
    have : q = 3 := by omega
    omega

lemma a_pk (p k : ℕ) (hp : p.Prime) :
  a (p ^ k) = ∑ j ∈ range k, (j + 1) * p ^ j := by
  unfold a
  have h_divs := Nat.divisors_prime_pow hp k
  change (p ^ k).divisors.sum (fun d => d * (Nat.divisors d).card) - (p ^ k) * (Nat.divisors (p ^ k)).card = _
  have h_tau_pk : (Nat.divisors (p ^ k)).card = k + 1 := by
    rw [Nat.divisors_prime_pow hp k, card_map, card_range]
  rw [h_tau_pk, h_divs, sum_map]
  have h_sum : (∑ j ∈ range (k + 1), (p ^ j) * (Nat.divisors (p ^ j)).card) =
    ∑ j ∈ range (k + 1), (j + 1) * p ^ j := by
    apply sum_congr rfl
    intro j hj
    have h_tau : (Nat.divisors (p ^ j)).card = j + 1 := by
      rw [Nat.divisors_prime_pow hp j, card_map, card_range]
    rw [h_tau]
