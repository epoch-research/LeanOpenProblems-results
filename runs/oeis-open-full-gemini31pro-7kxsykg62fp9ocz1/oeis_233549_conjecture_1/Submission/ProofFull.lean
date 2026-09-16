import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)

lemma extract_p {n : ℕ} (h : 0 < a n) :
    ∃ p < n, p.Prime ∧ Nat.Prime ((p.totient * (n - p).totient) ^ 4 + 1) := by
  have h1 := Finset.card_pos.mp h
  rcases h1 with ⟨p, hp⟩
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hp_range, hp_cond⟩
  rw [Finset.mem_range] at hp_range
  exact ⟨p, hp_range, hp_cond⟩

lemma odd_of_not_two_dvd {m : ℕ} (h : ¬ 2 ∣ m) : Odd m := by
  have h1 : m % 2 ≠ 0 := by
    intro h1
    have : 2 ∣ m := dvd_of_mod_eq_zero h1
    contradiction
  have : m % 2 = 1 := by omega
  use m / 2
  omega

lemma le_sq_sub_one {p : ℕ} (h : 3 ≤ p) : p ≤ (p - 1) ^ 2 := by
  have : ∃ k, p - 1 = k ∧ 2 ≤ k := ⟨p - 1, rfl, by omega⟩
  rcases this with ⟨k, hk, hk2⟩
  have : p = k + 1 := by omega
  subst this
  have : k + 1 ≤ k ^ 2 := by nlinarith
  exact this

lemma totient_bound_lemma (q : ℕ) : q ≤ 2 * q.totient ^ 2 ∧ (Odd q → q ≤ q.totient ^ 2) := by
  induction' q using Nat.strong_induction_on with q ih
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  if hq1 : q = 1 then
    subst hq1
    simp
  else
    have hq2 : 1 < q := by omega
    let p := q.minFac
    let m := q / p
    have hp_prime : p.Prime := minFac_prime hq1
    have h_pm : p * m = q := Nat.mul_div_cancel' (minFac_dvd q)
    have hm_lt : m < q := Nat.div_lt_self hq hp_prime.one_lt
    rcases ih m hm_lt with ⟨ih_m_even, ih_m_odd⟩
    by_cases h_pm_dvd : p ∣ m
    · have h_tot : q.totient = p * m.totient := by
        rw [← h_pm]
        exact totient_mul_of_prime_of_dvd hp_prime h_pm_dvd
      constructor
      · rw [h_tot]
        calc q = p * m := h_pm.symm
          _ ≤ p * (2 * m.totient ^ 2) := mul_le_mul_left p ih_m_even
          _ = 2 * p * m.totient ^ 2 := by ring
          _ ≤ 2 * p ^ 2 * m.totient ^ 2 := by
            gcongr
            nlinarith
          _ = 2 * (p * m.totient) ^ 2 := by ring
      · intro hq_odd
        have hp_odd : Odd p := Odd.of_mul_left (h_pm.symm ▸ hq_odd)
        have hm_odd : Odd m := Odd.of_mul_right (h_pm.symm ▸ hq_odd)
        rw [h_tot]
        calc q = p * m := h_pm.symm
          _ ≤ p * (m.totient ^ 2) := mul_le_mul_left p (ih_m_odd hm_odd)
          _ ≤ p ^ 2 * m.totient ^ 2 := by
            gcongr
            nlinarith
          _ = (p * m.totient) ^ 2 := by ring
    · have h_tot : q.totient = (p - 1) * m.totient := by
        rw [← h_pm]
        exact totient_mul_of_prime_of_not_dvd hp_prime h_pm_dvd
      constructor
      · rw [h_tot]
        by_cases hp2 : p = 2
        · have hm_odd : Odd m := by
            have h_not_dvd : ¬ 2 ∣ m := by
              have : p = 2 := hp2
              rwa [←this]
            exact odd_of_not_two_dvd h_not_dvd
          calc q = p * m := h_pm.symm
            _ = 2 * m := by rw [hp2]
            _ ≤ 2 * m.totient ^ 2 := mul_le_mul_left 2 (ih_m_odd hm_odd)
            _ = 2 * ( (2 - 1) * m.totient ) ^ 2 := by ring
            _ = 2 * ( (p - 1) * m.totient ) ^ 2 := by rw [hp2]
        · have hp_ge_2 : 2 ≤ p := hp_prime.two_le
          have hp3 : 3 ≤ p := by omega
          calc q = p * m := h_pm.symm
            _ ≤ p * (2 * m.totient ^ 2) := mul_le_mul_left p ih_m_even
            _ = 2 * p * m.totient ^ 2 := by ring
            _ ≤ 2 * (p - 1) ^ 2 * m.totient ^ 2 := by
              gcongr
              exact le_sq_sub_one hp3
            _ = 2 * ((p - 1) * m.totient) ^ 2 := by ring
      · intro hq_odd
        have hp_odd : Odd p := Odd.of_mul_left (h_pm.symm ▸ hq_odd)
        have hm_odd : Odd m := Odd.of_mul_right (h_pm.symm ▸ hq_odd)
        rw [h_tot]
        have hp_ge_2 : 2 ≤ p := hp_prime.two_le
        rcases hp_odd with ⟨k, hk⟩
        have hp3 : 3 ≤ p := by omega
        calc q = p * m := h_pm.symm
          _ ≤ p * m.totient ^ 2 := mul_le_mul_left p (ih_m_odd hm_odd)
          _ ≤ (p - 1) ^ 2 * m.totient ^ 2 := by
            gcongr
            exact le_sq_sub_one hp3
          _ = ((p - 1) * m.totient) ^ 2 := by ring

lemma x_le_x4_add_1 (x : ℕ) : x ≤ x ^ 4 + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 4 := Nat.pow_le_pow_right hx (by decide)
      _ ≤ x ^ 4 + 1 := by omega

lemma bdd_of_finite (S : Set ℕ) (h : S.Finite) : ∃ B, ∀ y ∈ S, y ≤ B := by
  exact h.bddAbove

lemma p_le_B (p q B : ℕ) (h1 : p * q ≤ B) (h2 : 1 ≤ q) : p ≤ B := by
  calc p = p * 1 := (mul_one p).symm
    _ ≤ p * q := Nat.mul_le_mul_left p h2
    _ ≤ B := h1

theorem oeis_233549_conjecture_1 :
  (∀ n, 2 < n → 0 < a n) →
  Set.Infinite {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} := by
  intro h_all
  by_contra h_inf
  have h_fin : ( {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} : Set ℕ ).Finite := Set.not_infinite.mp h_inf
  rcases bdd_of_finite _ h_fin with ⟨B, hB⟩
  let n := 2 * B ^ 2 + B + 3
  have hn_gt_2 : 2 < n := by omega
  have ha_pos := h_all n hn_gt_2
  rcases extract_p ha_pos with ⟨p, hp_lt, hp_prime, h_prime2⟩
  let q := n - p
  have hq_pos : 0 < q := Nat.sub_pos_of_lt hp_lt
  let x := p.totient * q.totient
  have hx_in : x ^ 4 + 1 ∈ {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} := by
    simp only [Set.mem_setOf_eq]
    exact ⟨h_prime2, x, rfl⟩
  have h_x4_le_B : x ^ 4 + 1 ≤ B := hB (x ^ 4 + 1) hx_in
  have hx_le_B : x ≤ B := le_trans (x_le_x4_add_1 x) h_x4_le_B
  have hq_tot_ge_1 : 1 ≤ q.totient := totient_pos.mpr hq_pos
  have hp_tot_le_B : p.totient ≤ B := p_le_B p.totient q.totient B hx_le_B hq_tot_ge_1
  have hp_tot_eq : p.totient = p - 1 := totient_prime hp_prime
  have hp_le_B_add_1 : p ≤ B + 1 := by
    rw [hp_tot_eq] at hp_tot_le_B
    omega
  have hp_tot_ge_1 : 1 ≤ p.totient := by
    rw [hp_tot_eq]
    have : 2 ≤ p := hp_prime.two_le
    omega
  have hq_tot_le_B : q.totient ≤ B := by
    have hx_le_B2 : q.totient * p.totient ≤ B := by
      calc q.totient * p.totient = p.totient * q.totient := mul_comm _ _
        _ = x := rfl
        _ ≤ B := hx_le_B
    exact p_le_B q.totient p.totient B hx_le_B2 hp_tot_ge_1
  have hq_le : q ≤ 2 * q.totient ^ 2 := (totient_bound_lemma q).1
  have hq_le_2B2 : q ≤ 2 * B ^ 2 := by
    calc q ≤ 2 * q.totient ^ 2 := hq_le
      _ ≤ 2 * B ^ 2 := by
        gcongr
  have hn_le : n ≤ 2 * B ^ 2 + B + 1 := by
    have : n = p + q := Nat.add_sub_cancel' (le_of_lt hp_lt) |>.symm
    omega
  have hn_eq : n = 2 * B ^ 2 + B + 3 := rfl
  omega
