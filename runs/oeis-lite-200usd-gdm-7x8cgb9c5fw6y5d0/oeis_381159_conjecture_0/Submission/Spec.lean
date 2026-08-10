import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

lemma exists_i_divisible (a d n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 150) (h_coprime : d.Coprime n) :
  ∃ i : Fin 150, n ∣ a + i.val * d := by
  have : NeZero n := ⟨by omega⟩
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime d h_coprime
  let val : ZMod n := - (a : ZMod n) * ↑(u⁻¹)
  let i_val := val.val
  have hi_lt : i_val < n := ZMod.val_lt val
  have hi_150 : i_val < 150 := lt_of_lt_of_le hi_lt hn2
  use ⟨i_val, hi_150⟩
  rw [← CharP.cast_eq_zero_iff (ZMod n) n]
  push_cast
  have h_val : (i_val : ZMod n) = val := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [h_val]
  have h_ud : (↑u : ZMod n)⁻¹ * (d : ZMod n) = 1 := by
    have h_coe_u : (u : ZMod n) = d := rfl
    rw [← h_coe_u]
    exact Units.inv_mul u
  calc
    (a : ZMod n) + (- (a : ZMod n) * (↑u : ZMod n)⁻¹) * (d : ZMod n) = (a : ZMod n) + (- (a : ZMod n)) * ((↑u : ZMod n)⁻¹ * (d : ZMod n)) := by ring
    _ = (a : ZMod n) + (- (a : ZMod n)) * 1 := by rw [h_ud]
    _ = 0 := by ring

lemma card_image_ge_two {α β : Type} [DecidableEq β] {s : Finset α} {f : α → β} {x y : α}
  (hx : x ∈ s) (hy : y ∈ s) (h_ne : f x ≠ f y) : 2 ≤ Finset.card (s.image f) := by
  have h1 : f x ∈ s.image f := Finset.mem_image_of_mem f hx
  have h2 : f y ∈ s.image f := Finset.mem_image_of_mem f hy
  have h_sub : {f x, f y} ⊆ s.image f := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨h1, h2⟩
  have h_card : Finset.card {f x, f y} = 2 := by
    rw [Finset.card_pair h_ne]
  have h_le := Finset.card_le_card h_sub
  omega

lemma no_lopsided_ap_for_pair (a d p q : ℕ) (ha : 2 ≤ a) (hp : p.Prime) (hq : q.Prime)
  (hp_nd : ¬ p ∣ d) (hq_nd : ¬ q ∣ d) (h_ne : p % 10 ≠ q % 10) (hpq : p * q ≤ 150) :
  ¬ (∀ (i : Fin 150), A381159_condition (a + i.val * d)) := by
  intro h_cond
  have hcp : p.Coprime d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hp_nd
  have hcq : q.Coprime d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hq_nd
  have hcdp : d.Coprime p := hcp.symm
  have hcdq : d.Coprime q := hcq.symm
  have hcdpq : d.Coprime (p * q) := hcdp.mul_right hcdq
  have hpq_ge1 : 1 ≤ p * q := by
    have hp1 : 1 < p := hp.one_lt
    have hq1 : 1 < q := hq.one_lt
    have hp_pos : 0 < p := by omega
    have hq_pos : 0 < q := by omega
    have h_pos : 0 < p * q := Nat.mul_pos hp_pos hq_pos
    omega
  obtain ⟨i, h_div⟩ := exists_i_divisible a d (p * q) hpq_ge1 hpq hcdpq
  let n := a + i.val * d
  have hn_nz : n ≠ 0 := by
    have : 2 ≤ n := by omega
    omega
  have hp_div : p ∣ n := dvd_trans (dvd_mul_right p q) h_div
  have hq_div : q ∣ n := dvd_trans (dvd_mul_left q p) h_div
  have hp_mem : p ∈ n.primeFactors := (Nat.mem_primeFactors).mpr ⟨hp, hp_div, hn_nz⟩
  have hq_mem : q ∈ n.primeFactors := (Nat.mem_primeFactors).mpr ⟨hq, hq_div, hn_nz⟩
  have h_card_ge2 : 2 ≤ Finset.card (n.primeFactors.image (fun x => x % 10)) :=
    card_image_ge_two hp_mem hq_mem h_ne
  have h_cond_i := h_cond i
  have : Finset.card (n.primeFactors.image (fun x => x % 10)) ≤ 1 := h_cond_i
  omega

lemma d_has_coprime_pair : ∀ d < 2026, 1 ≤ d →
  (¬(11 ∣ d) ∧ ¬(13 ∣ d)) ∨
  (¬(7 ∣ d) ∧ ¬(19 ∣ d)) ∨
  (¬(5 ∣ d) ∧ ¬(29 ∣ d)) ∨
  (¬(3 ∣ d) ∧ ¬(17 ∣ d)) ∨
  (¬(2 ∣ d) ∧ ¬(17 ∣ d)) := by
  decide

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0.disproof :
  ¬ ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd1, hd2, h_cond⟩
  have h_or := d_has_coprime_pair d (by omega) hd1
  rcases h_or with h | h | h | h | h
  · exact no_lopsided_ap_for_pair a d 11 13 ha (by decide) (by decide) h.1 h.2 (by decide) (by decide) h_cond
  · exact no_lopsided_ap_for_pair a d 7 19 ha (by decide) (by decide) h.1 h.2 (by decide) (by decide) h_cond
  · exact no_lopsided_ap_for_pair a d 5 29 ha (by decide) (by decide) h.1 h.2 (by decide) (by decide) h_cond
  · exact no_lopsided_ap_for_pair a d 3 17 ha (by decide) (by decide) h.1 h.2 (by decide) (by decide) h_cond
  · exact no_lopsided_ap_for_pair a d 2 17 ha (by decide) (by decide) h.1 h.2 (by decide) (by decide) h_cond

