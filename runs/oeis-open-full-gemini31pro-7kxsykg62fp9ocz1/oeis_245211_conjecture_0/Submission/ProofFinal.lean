import Submission.Spec
import Mathlib

open Nat Finset


lemma a_prime (p : ℕ) (hp : p.Prime) : a p = 1 := by
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
    ring
  change (∑ j ∈ range (k + 1), (p ^ j) * (Nat.divisors (p ^ j)).card) - (p ^ k) * (k + 1) = _
  rw [h_sum]
  have h_split : ∑ j ∈ range (k + 1), (j + 1) * p ^ j = (∑ j ∈ range k, (j + 1) * p ^ j) + (k + 1) * p ^ k := by
    exact sum_range_succ (fun j => (j + 1) * p ^ j) k
  rw [h_split]
  have : (p ^ k) * (k + 1) = (k + 1) * p ^ k := mul_comm _ _
  rw [this]
  exact Nat.add_sub_cancel _ _

lemma sum_eq_add_sum_Ico_0 {k : ℕ} (f : ℕ → ℕ) (h_0 : 0 < k) :
  ∑ j ∈ range k, f j = f 0 + ∑ j ∈ Ico 1 k, f j := by
  rw [range_eq_Ico]
  have h1 : 0 < k := h_0
  exact sum_eq_sum_Ico_succ_bot h1 f

lemma a_pk_ne_pk_proof_step (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) (h_val : p ^ k = ∑ j ∈ range k, (j + 1) * p ^ j) : False := by
  have h_split : ∑ j ∈ range k, (j + 1) * p ^ j = 1 + ∑ j ∈ Ico 1 k, (j + 1) * p ^ j := by
    have h_0 : 0 < k := by omega
    have := sum_eq_add_sum_Ico_0 (fun j => (j + 1) * p ^ j) h_0
    dsimp only at this
    have hz : (0 + 1) * p ^ 0 = 1 := by ring
    rw [hz] at this
    exact this
  rw [h_split] at h_val
  have hdvd1 : p ∣ p ^ k := dvd_pow_self _ (by omega)
  have hdvd2 : p ∣ ∑ j ∈ Ico 1 k, (j + 1) * p ^ j := by
    apply dvd_sum
    intro j hj
    have hj_pos : 0 < j := by
      rw [mem_Ico] at hj
      exact hj.1
    have : p ∣ p ^ j := dvd_pow_self _ (by omega)
    exact dvd_mul_of_dvd_right this _
  have h_dvd3 : p ∣ 1 := by
    have h_sub : 1 = p ^ k - ∑ j ∈ Ico 1 k, (j + 1) * p ^ j := by omega
    rw [h_sub]
    exact Nat.dvd_sub hdvd1 hdvd2
  have h_p1 : p = 1 := Nat.dvd_one.mp h_dvd3
  have h_p_ge2 : 2 ≤ p := hp.two_le
  omega

lemma sum_inv_eq {n : ℕ} (hn : 0 < n) :
  (∑ d ∈ n.divisors, (d : ℚ)) / (n : ℚ) = ∑ d ∈ n.divisors, 1 / (d : ℚ) := by
  have h_eq : (∑ d ∈ n.divisors, (d : ℚ)) / (n : ℚ) = ∑ d ∈ n.divisors, ((d : ℚ) / (n : ℚ)) := by
    rw [sum_div]
  rw [h_eq]
  have h_reindex : ∑ d ∈ n.divisors, ((d : ℚ) / (n : ℚ)) = ∑ d ∈ n.divisors, (((n / d : ℕ) : ℚ) / (n : ℚ)) := by
    have := Nat.sum_div_divisors n (fun d => ((d : ℕ) : ℚ) / (n : ℚ))
    exact this.symm
  rw [h_reindex]
  apply sum_congr rfl
  intro d hd
  rw [mem_divisors] at hd
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hn.ne.symm (eq_zero_of_zero_dvd hd.1))
  have hd_ne_zero : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne.symm
  have h_cast : ((n / d : ℕ) : ℚ) = (n : ℚ) / (d : ℚ) := by
    exact_mod_cast Nat.cast_div hd.1 hd_ne_zero
  rw [h_cast]
  have hn_pos_q : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne.symm
  calc ((n : ℚ) / (d : ℚ)) / (n : ℚ) = ((n : ℚ) / (n : ℚ)) / (d : ℚ) := by ring
    _ = 1 / (d : ℚ) := by rw [div_self hn_pos_q]

lemma sum_inv_subset {n m : ℕ} (hn : 0 < n) (hdvd : m ∣ n) :
  ∑ d ∈ m.divisors, 1 / (d : ℚ) ≤ ∑ d ∈ n.divisors, 1 / (d : ℚ) := by
  have h_sub : m.divisors ⊆ n.divisors := by
    intro d hd
    rw [mem_divisors] at hd ⊢
    exact ⟨dvd_trans hd.1 hdvd, hn.ne.symm⟩
  apply sum_le_sum_of_subset_of_nonneg h_sub
  intro i _ _
  positivity


lemma dvd_div_of_distinct_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hdp : p ∣ n) (hdq : q ∣ n) :
  q ∣ n / p := by
  have h_coprime : p.Coprime q := by
    rw [hp.coprime_iff_not_dvd]
    intro h
    exact hpq.symm ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one).symm
  have h_dvd_mul : p * q ∣ n := h_coprime.mul_dvd_of_dvd_of_dvd hdp hdq
  have ⟨k, hk⟩ := h_dvd_mul
  use k
  have : n / p = q * k := by
    rw [hk]
    have h_assoc : p * q * k = p * (q * k) := by ring
    rw [h_assoc]
    exact Nat.mul_div_cancel_left _ hp.pos
  rw [this]

lemma tau_ge_four {m q r : ℕ} (hm : 0 < m) (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (hdq : q ∣ m) (hdr : r ∣ m) :
  4 ≤ (Nat.divisors m).card := by
  have h_coprime : q.Coprime r := by
    rw [hq.coprime_iff_not_dvd]
    intro h
    exact hqr.symm ((hr.eq_one_or_self_of_dvd q h).resolve_left hq.ne_one).symm
  have hdvd : q * r ∣ m := h_coprime.mul_dvd_of_dvd_of_dvd hdq hdr
  have h_sub : {q * r, r, q, 1} ⊆ m.divisors := by
    intro d hd
    rw [mem_divisors]
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact ⟨hdvd, hm.ne.symm⟩
    · exact ⟨hdr, hm.ne.symm⟩
    · exact ⟨hdq, hm.ne.symm⟩
    · exact ⟨one_dvd m, hm.ne.symm⟩
  have h_card : ({q * r, r, q, 1} : Finset ℕ).card = 4 := by
    have hq2 : 2 ≤ q := hq.two_le
    have hr2 : 2 ≤ r := hr.two_le
    have h1 : q * r ∉ ({r, q, 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      push_neg
      constructor
      · intro h; nlinarith
      · constructor
        · intro h; nlinarith
        · intro h; nlinarith
    have h2 : r ∉ ({q, 1} : Finset ℕ) := by
      simp only [mem_insert, mem_singleton]
      push_neg
      exact ⟨hqr.symm, hr.ne_one⟩
    have h3 : q ∉ ({1} : Finset ℕ) := by
      simp only [mem_singleton]
      exact hq.ne_one
    rw [card_insert_of_notMem h1, card_insert_of_notMem h2, card_insert_of_notMem h3, card_singleton]
  rw [← h_card]
  exact card_le_card h_sub

lemma tau_div_ge_four {n p q r : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) 
  (h1 : p ≠ q) (h2 : q ≠ r) (h3 : p ≠ r)
  (hdp : p ∣ n) (hdq : q ∣ n) (hdr : r ∣ n) :
  4 ≤ (Nat.divisors (n / p)).card := by
  have h_pos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn_pos hdp) hp.pos
  have hdq_div : q ∣ n / p := dvd_div_of_distinct_primes hp hq h1 hdp hdq
  have hdr_div : r ∣ n / p := dvd_div_of_distinct_primes hp hr h3 hdp hdr
  exact tau_ge_four h_pos hq hr h2 hdq_div hdr_div


lemma a_eq_sum_proper {n : ℕ} (hn : 0 < n) :
  a n = ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := by
  unfold a
  have h_in : n ∈ n.divisors := by rw [Nat.mem_divisors]; exact ⟨dvd_refl n, hn.ne.symm⟩
  have h_split := Finset.sum_erase_add n.divisors (fun d => d * (Nat.divisors d).card) h_in
  rw [add_comm] at h_split
  rw [← h_split]
  exact Nat.add_sub_cancel_left _ _

lemma a_ge_three_primes_step {n p : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hdp : p ∣ n) :
  n / p ∈ n.divisors.erase n := by
  rw [mem_erase, mem_divisors]
  refine ⟨?_, ⟨Nat.div_dvd_of_dvd hdp, hn_pos.ne.symm⟩⟩
  intro h
  have hn_eq : n / p * p = n := Nat.div_mul_cancel hdp
  rw [h] at hn_eq
  have : n * 1 = n * p := by
    calc n * 1 = n := by ring
      _ = n * p := hn_eq.symm
  have hp1 : 1 = p := mul_left_cancel₀ hn_pos.ne.symm this
  have : 2 ≤ p := hp.two_le
  omega

lemma a_ge_three_primes_ne {n p q : ℕ} (hn_pos : 0 < n) (hdp : p ∣ n) (hdq : q ∣ n) (h1 : p ≠ q) :
  n / p ≠ n / q := by
  intro h
  have h_eq1 : (n / p) * p = (n / q) * p := by rw [h]
  rw [Nat.div_mul_cancel hdp] at h_eq1
  have h_eq2 : n * q = (n / q) * p * q := by rw [← h_eq1]
  have h_assoc : (n / q) * p * q = (n / q) * q * p := by ring
  rw [h_assoc, Nat.div_mul_cancel hdq] at h_eq2
  have h_pq : q = p := mul_left_cancel₀ hn_pos.ne.symm h_eq2
  exact h1 h_pq.symm

lemma a_ge_three_primes {n p q r : ℕ} (hn_pos : 0 < n) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
  (h1 : p ≠ q) (h2 : q ≠ r) (h3 : p ≠ r)
  (hdp : p ∣ n) (hdq : q ∣ n) (hdr : r ∣ n) :
  4 * (n / p) + 4 * (n / q) + 4 * (n / r) ≤ a n := by
  have hd_p : n / p ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hp hdp
  have hd_q : n / q ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hq hdq
  have hd_r : n / r ∈ n.divisors.erase n := a_ge_three_primes_step hn_pos hr hdr
  have h_sub : {n / p, n / q, n / r} ⊆ n.divisors.erase n := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hd_p
    · exact hd_q
    · exact hd_r
  have hpq_ne : n / p ≠ n / q := a_ge_three_primes_ne hn_pos hdp hdq h1
  have hqr_ne : n / q ≠ n / r := a_ge_three_primes_ne hn_pos hdq hdr h2
  have hpr_ne : n / p ≠ n / r := a_ge_three_primes_ne hn_pos hdp hdr h3
  have h_card : ({n / p, n / q, n / r} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · intro h; rw [Finset.mem_singleton] at h; exact hqr_ne h
    · intro h; rw [Finset.mem_insert, Finset.mem_singleton] at h; rcases h with h | h
      · exact hpq_ne h
      · exact hpr_ne h
  rw [a_eq_sum_proper hn_pos]
  have h_sum : ({n / p, n / q, n / r} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) ≤ ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := by
    exact sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)
  have h_eval : ({n / p, n / q, n / r} : Finset ℕ).sum (fun d => d * (Nat.divisors d).card) = 
    (n / p) * (Nat.divisors (n / p)).card + (n / q) * (Nat.divisors (n / q)).card + (n / r) * (Nat.divisors (n / r)).card := by
    rw [sum_insert, sum_insert, sum_singleton]
    · ring
    · intro h; rw [Finset.mem_singleton] at h; exact hqr_ne h
    · intro h; rw [Finset.mem_insert, Finset.mem_singleton] at h; rcases h with h | h
      · exact hpq_ne h
      · exact hpr_ne h
  rw [h_eval] at h_sum
  have h_tau_p : 4 ≤ (Nat.divisors (n / p)).card := tau_div_ge_four hn_pos hp hq hr h1 h2 h3 hdp hdq hdr
  have h_tau_q : 4 ≤ (Nat.divisors (n / q)).card := tau_div_ge_four hn_pos hq hp hr h1.symm h3 h2 hdq hdp hdr
  have h_tau_r : 4 ≤ (Nat.divisors (n / r)).card := tau_div_ge_four hn_pos hr hp hq h3.symm h1 h2.symm hdr hdp hdq
  calc 4 * (n / p) + 4 * (n / q) + 4 * (n / r) ≤ (n / p) * 4 + (n / q) * 4 + (n / r) * 4 := by ring_nf; rfl
    _ ≤ (n / p) * (Nat.divisors (n / p)).card + (n / q) * (Nat.divisors (n / q)).card + (n / r) * (Nat.divisors (n / r)).card := by
      gcongr
    _ ≤ ∑ d ∈ n.divisors.erase n, d * (Nat.divisors d).card := h_sum

