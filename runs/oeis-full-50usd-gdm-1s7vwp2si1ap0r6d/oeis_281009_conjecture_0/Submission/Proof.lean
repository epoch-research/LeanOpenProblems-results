import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Let's define the helper concepts
def odd_part (d : ℕ) : ℕ :=
  d / 2^(padicValNat 2 d)
lemma padicValNat_two_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat 2 (a * b) = padicValNat 2 a + padicValNat 2 b := by
  have inst : Fact (Nat.Prime 2) := Nat.fact_prime_two
  exact padicValNat.mul ha hb

lemma Nat.mul_div_mul_of_dvd {a b x y : ℕ} (hx : x ∣ a) (hy : y ∣ b) :
    (a * b) / (x * y) = (a / x) * (b / y) := by
  rcases hx with ⟨u, rfl⟩
  rcases hy with ⟨v, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0; simp
  by_cases hy0 : y = 0
  · subst hy0; simp
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  rw [mul_assoc x u (y * v), ← mul_assoc u y v, mul_comm u y, mul_assoc y u v, ← mul_assoc x y (u * v)]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hxy0)]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hx0)]
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hy0)]

lemma odd_part_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    odd_part (a * b) = odd_part a * odd_part b := by
  unfold odd_part
  rw [padicValNat_two_mul ha hb, pow_add]
  exact Nat.mul_div_mul_of_dvd pow_padicValNat_dvd pow_padicValNat_dvd
lemma odd_part_dvd_odd_part {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    odd_part d ∣ odd_part n := by
  rcases hd with ⟨c, rfl⟩
  have hd0 : d ≠ 0 := mul_ne_zero_iff.mp hn |>.1
  have hc0 : c ≠ 0 := mul_ne_zero_iff.mp hn |>.2
  rw [odd_part_mul hd0 hc0]
  exact dvd_mul_right (odd_part d) (odd_part c)
lemma odd_part_odd {d : ℕ} (hd0 : d ≠ 0) : odd_part d % 2 = 1 := by
  have inst : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have dvd : 2 ^ padicValNat 2 d ∣ d := pow_padicValNat_dvd
  have h_val : padicValNat 2 (odd_part d) = 0 := by
    unfold odd_part
    rw [padicValNat.div_pow dvd]
    exact Nat.sub_self (padicValNat 2 d)
  have h_odd : ¬ 2 ∣ odd_part d := by
    intro hdvd
    have h_ne_zero : odd_part d ≠ 0 := by
      intro h_zero
      have h_eq : d = (odd_part d) * 2 ^ padicValNat 2 d := by
        exact (Nat.div_mul_cancel pow_padicValNat_dvd).symm
      rw [h_zero, zero_mul] at h_eq
      exact hd0 h_eq
    have h_val2 : padicValNat 2 (odd_part d) ≠ 0 := by
      rw [← dvd_iff_padicValNat_ne_zero h_ne_zero]
      exact hdvd
    exact h_val2 h_val
  omega
lemma padicValNat_two_pow (a : ℕ) : padicValNat 2 (2 ^ a) = a := by
  have inst : Fact (Nat.Prime 2) := Nat.fact_prime_two
  exact padicValNat.prime_pow a

lemma odd_part_two_pow_mul (a j : ℕ) (hj : j % 2 = 1) :
    odd_part (2 ^ a * j) = j := by
  have hj0 : j ≠ 0 := by omega
  have h_two_pow : 2 ^ a ≠ 0 := by positivity
  unfold odd_part
  rw [padicValNat_two_mul h_two_pow hj0]
  have h_val_j : padicValNat 2 j = 0 := by
    rw [padicValNat.eq_zero_iff]
    right; right
    intro hdvd
    rcases hdvd with ⟨c, rfl⟩
    omega
  rw [h_val_j, add_zero]
  rw [padicValNat_two_pow a]
  exact Nat.mul_div_cancel_left j (pow_pos (by decide) a)

def M_even (n : ℕ) : Finset ℕ :=
  (divisors n).filter (fun d => d % 2 = 0 ∧ n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n)

def E_M (n : ℕ) (j : ℕ) : Finset ℕ :=
  (M_even n).filter (fun d => odd_part d = j)

def S_a (n j : ℕ) : Finset ℕ :=
  (Ioc 0 (padicValNat 2 n)).filter (fun a => 2 ^ a * j ∈ M_even n)

lemma card_E_M_eq_card_S_a (n j : ℕ) (hj : j % 2 = 1) :
    (E_M n j).card = (S_a n j).card := by
  have h_img : E_M n j = (S_a n j).image (fun a => 2 ^ a * j) := by
    ext d
    rw [mem_image]
    constructor
    · intro hd
      rw [E_M, mem_filter] at hd
      have hd_M : d ∈ M_even n := hd.1
      have hd_odd : odd_part d = j := hd.2
      have hn0 : n ≠ 0 := by
        rw [M_even, mem_filter, mem_divisors] at hd_M
        exact hd_M.1.2
      have hd0 : d ≠ 0 := by
        rw [M_even, mem_filter] at hd_M
        rcases hd_M with ⟨-, -, hn_le, -⟩
        intro h_zero
        subst h_zero
        omega
      have hd_div : d ∣ n := by
        rw [M_even, mem_filter, mem_divisors] at hd_M
        exact hd_M.1.1
      have h_even : d % 2 = 0 := by
        rw [M_even, mem_filter] at hd_M
        exact hd_M.2.1
      have ha_pos : padicValNat 2 d > 0 := by
        have inst : Fact (Nat.Prime 2) := Nat.fact_prime_two
        have hdvd : 2 ∣ d := Nat.dvd_of_mod_eq_zero h_even
        have h_ne : padicValNat 2 d ≠ 0 := (dvd_iff_padicValNat_ne_zero hd0).mp hdvd
        omega
      have ha_le : padicValNat 2 d ≤ padicValNat 2 n := by
        have inst : Fact (Nat.Prime 2) := Nat.fact_prime_two
        have hdvd : 2 ^ padicValNat 2 d ∣ n := dvd_trans pow_padicValNat_dvd hd_div
        rw [padicValNat_dvd_iff_le hn0] at hdvd
        exact hdvd
      have h_a_mem : padicValNat 2 d ∈ S_a n j := by
        rw [S_a, mem_filter, mem_Ioc]
        refine ⟨⟨ha_pos, ha_le⟩, ?_⟩
        have h_eq : d = 2 ^ padicValNat 2 d * j := by
          have h_can : d = 2 ^ padicValNat 2 d * odd_part d := by
            rw [mul_comm]
            exact (Nat.div_mul_cancel pow_padicValNat_dvd).symm
          rw [hd_odd] at h_can
          exact h_can
        rw [← h_eq]
        exact hd_M
      refine ⟨padicValNat 2 d, h_a_mem, ?_⟩
      have h_eq : d = 2 ^ padicValNat 2 d * j := by
        have h_can : d = 2 ^ padicValNat 2 d * odd_part d := by
          rw [mul_comm]
          exact (Nat.div_mul_cancel pow_padicValNat_dvd).symm
        rw [hd_odd] at h_can
        exact h_can
      exact h_eq.symm
    · rintro ⟨a, ha, rfl⟩
      rw [S_a, mem_filter, mem_Ioc] at ha
      have ha_pos : a > 0 := ha.1.1
      have ha_le : a ≤ padicValNat 2 n := ha.1.2
      have h_M : 2 ^ a * j ∈ M_even n := ha.2
      rw [E_M, mem_filter]
      refine ⟨h_M, ?_⟩
      exact odd_part_two_pow_mul a j hj
  rw [h_img, Finset.card_image_of_injOn]
  intro x hx y hy hxy
  have hj0 : j ≠ 0 := by omega
  have h_eq : 2 ^ x = 2 ^ y := by
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hj0) hxy
  exact Nat.pow_right_injective (by decide) h_eq

lemma card_S_a_le_one (n j : ℕ) : (S_a n j).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a1 a2 ha1 ha2
  by_contra h_ne
  dsimp [S_a] at ha1 ha2
  rw [mem_filter] at ha1 ha2
  have ha1_M : 2 ^ a1 * j ∈ M_even n := ha1.2
  have ha2_M : 2 ^ a2 * j ∈ M_even n := ha2.2
  rw [M_even, mem_filter] at ha1_M ha2_M
  have h1 : n ≤ 2 * (2 ^ a1 * j) ^ 2 := ha1_M.2.2.1
  have h2 : (2 ^ a2 * j) ^ 2 < 2 * n := ha2_M.2.2.2
  rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
  · have h_pow : (2 ^ a2 * j) ^ 2 = (2 ^ (a2 - a1)) ^ 2 * (2 ^ a1 * j) ^ 2 := by
      have h_add : a2 = a1 + (a2 - a1) := (Nat.add_sub_cancel' (Nat.le_of_lt h_lt)).symm
      nth_rw 1 [h_add]
      have h_ring : 2 ^ (a1 + (a2 - a1)) * j = 2 ^ (a2 - a1) * (2 ^ a1 * j) := by ring
      rw [h_ring]
      exact mul_pow (2 ^ (a2 - a1)) (2 ^ a1 * j) 2
    have h_ge4 : (2 ^ (a2 - a1)) ^ 2 ≥ 4 := by
      have h_diff : a2 - a1 ≥ 1 := by omega
      have : 2 ^ 1 ≤ 2 ^ (a2 - a1) := Nat.pow_le_pow_right (by decide) h_diff
      have : 2 ^ (a2 - a1) ≥ 2 := this
      nlinarith
    have h_contra : (2 ^ a2 * j) ^ 2 ≥ 2 * n := by
      rw [h_pow]
      nlinarith
    omega
  · have h_pow : (2 ^ a1 * j) ^ 2 = (2 ^ (a1 - a2)) ^ 2 * (2 ^ a2 * j) ^ 2 := by
      have h_add : a1 = a2 + (a1 - a2) := (Nat.add_sub_cancel' (Nat.le_of_lt h_gt)).symm
      nth_rw 1 [h_add]
      have h_ring : 2 ^ (a2 + (a1 - a2)) * j = 2 ^ (a1 - a2) * (2 ^ a2 * j) := by ring
      rw [h_ring]
      exact mul_pow (2 ^ (a1 - a2)) (2 ^ a2 * j) 2
    have h_ge4 : (2 ^ (a1 - a2)) ^ 2 ≥ 4 := by
      have h_diff : a1 - a2 ≥ 1 := by omega
      have : 2 ^ 1 ≤ 2 ^ (a1 - a2) := Nat.pow_le_pow_right (by decide) h_diff
      have : 2 ^ (a1 - a2) ≥ 2 := this
      nlinarith
    have h_contra : (2 ^ a1 * j) ^ 2 ≥ 2 * n := by
      rw [h_pow]
      nlinarith
    omega
lemma card_eq_if_nonempty {α : Type*} {s : Finset α} (h : s.card ≤ 1) :
    s.card = if s.Nonempty then 1 else 0 := by
  split_ifs with h_nonempty
  · rcases h_nonempty with ⟨x, hx⟩
    have : s.card ≥ 1 := by
      have : {x} ⊆ s := by
        rw [singleton_subset_iff]
        exact hx
      have h1 : ({x} : Finset α).card ≤ s.card := card_le_card this
      rw [card_singleton] at h1
      exact h1
    omega
  · rw [nonempty_iff_ne_empty, not_not] at h_nonempty
    rw [h_nonempty, card_empty]




lemma card_M_even_eq_sum_card_E_M (n : ℕ) (hn : n ≠ 0) :
    (M_even n).card = ∑ j ∈ divisors (odd_part n), (E_M n j).card := by
  apply Finset.card_eq_sum_card_fiberwise
  intro d hd
  rw [Finset.mem_coe] at hd
  rw [Finset.mem_coe, mem_divisors]
  have hd_dvd : d ∣ n := by
    rw [M_even] at hd
    rw [mem_filter, mem_divisors] at hd
    exact hd.1.1
  have h_odd_dvd : odd_part d ∣ odd_part n := odd_part_dvd_odd_part hn hd_dvd
  have h_m0 : odd_part n ≠ 0 := by
    intro h_zero
    have h_eq : n = (odd_part n) * 2 ^ padicValNat 2 n := by
      unfold odd_part
      exact (Nat.div_mul_cancel pow_padicValNat_dvd).symm
    rw [h_zero, zero_mul] at h_eq
    exact hn h_eq
  exact ⟨h_odd_dvd, h_m0⟩





