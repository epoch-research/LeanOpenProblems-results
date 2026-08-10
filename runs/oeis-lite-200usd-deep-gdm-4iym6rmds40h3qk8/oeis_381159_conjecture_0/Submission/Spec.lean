import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

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

lemma exists_i_dvd_helper (a d p q : ℕ) (i : ℕ)
  (hdiv_p : p ∣ (a % (p * q)) + i * d) (hdiv_q : q ∣ (a % (p * q)) + i * d) :
  p ∣ a + i * d ∧ q ∣ a + i * d := by
  have h_div : a % (p * q) + (p * q) * (a / (p * q)) = a := Nat.mod_add_div a (p * q)
  have h_eq : a + i * d = ((a % (p * q)) + i * d) + (p * q) * (a / (p * q)) := by
    omega
  have hdvd_p_mul : p ∣ (p * q) * (a / (p * q)) := by
    use q * (a / (p * q))
    ring
  have hdvd_q_mul : q ∣ (p * q) * (a / (p * q)) := by
    use p * (a / (p * q))
    ring
  constructor
  · rw [h_eq]
    exact dvd_add hdiv_p hdvd_p_mul
  · rw [h_eq]
    exact dvd_add hdiv_q hdvd_q_mul

lemma no_lopsided_of_primes (a d p q i : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hdiff : p % 10 ≠ q % 10) (hdiv_p : p ∣ a + i * d) (hdiv_q : q ∣ a + i * d)
  (ha : 2 ≤ a) : ¬ A381159_condition (a + i * d) := by
  intro h_cond
  have h_nz : a + i * d ≠ 0 := by
    omega
  have hp_mem : p ∈ (a + i * d).primeFactors := by
    rw [mem_primeFactors]
    exact ⟨hp, hdiv_p, h_nz⟩
  have hq_mem : q ∈ (a + i * d).primeFactors := by
    rw [mem_primeFactors]
    exact ⟨hq, hdiv_q, h_nz⟩
  have hp_im : p % 10 ∈ ((a + i * d).primeFactors.image (fun p => p % 10)) := Finset.mem_image_of_mem _ hp_mem
  have hq_im : q % 10 ∈ ((a + i * d).primeFactors.image (fun p => p % 10)) := Finset.mem_image_of_mem _ hq_mem
  have h_eq : p % 10 = q % 10 := by
    have h_subset : {p % 10, q % 10} ⊆ ((a + i * d).primeFactors.image (fun p => p % 10)) := by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp_im, hq_im⟩
    have h_card_subset := Finset.card_le_card h_subset
    have h_card_pair : Finset.card {p % 10, q % 10} ≤ 1 := le_trans h_card_subset h_cond
    rw [Finset.card_pair hdiff] at h_card_pair
    omega
  exact hdiff h_eq

def pair_for_d (d : ℕ) : ℕ × ℕ :=
  if d % 2 ≠ 0 ∧ d % 3 ≠ 0 then (2, 3)
  else if d % 2 ≠ 0 ∧ d % 5 ≠ 0 then (2, 5)
  else if d % 2 ≠ 0 ∧ d % 7 ≠ 0 then (2, 7)
  else if d % 3 ≠ 0 ∧ d % 5 ≠ 0 then (3, 5)
  else if d % 3 ≠ 0 ∧ d % 7 ≠ 0 then (3, 7)
  else if d % 2 ≠ 0 ∧ d % 11 ≠ 0 then (2, 11)
  else if d % 2 ≠ 0 ∧ d % 13 ≠ 0 then (2, 13)
  else if d % 3 ≠ 0 ∧ d % 11 ≠ 0 then (3, 11)
  else if d % 5 ≠ 0 ∧ d % 7 ≠ 0 then (5, 7)
  else if d % 3 ≠ 0 ∧ d % 17 ≠ 0 then (3, 17)
  else if d % 5 ≠ 0 ∧ d % 11 ≠ 0 then (5, 11)
  else if d % 5 ≠ 0 ∧ d % 13 ≠ 0 then (5, 13)
  else if d % 7 ≠ 0 ∧ d % 11 ≠ 0 then (7, 11)
  else if d % 7 ≠ 0 ∧ d % 13 ≠ 0 then (7, 13)
  else if d % 11 ≠ 0 ∧ d % 13 ≠ 0 then (11, 13)
  else (2, 3)

def find_i_loop (a d pq : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => if (a + i * d) % pq = 0 then i else find_i_loop a d pq i

theorem exists_i_dvd_decidable_1 : ∀ d, 1 ≤ d → d ≤ 200 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_2 : ∀ d, 201 ≤ d → d ≤ 400 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_3 : ∀ d, 401 ≤ d → d ≤ 600 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_4 : ∀ d, 601 ≤ d → d ≤ 800 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_5 : ∀ d, 801 ≤ d → d ≤ 1000 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_6 : ∀ d, 1001 ≤ d → d ≤ 1200 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_7 : ∀ d, 1201 ≤ d → d ≤ 1400 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_8 : ∀ d, 1401 ≤ d → d ≤ 1600 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_9 : ∀ d, 1601 ≤ d → d ≤ 1800 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable_10 : ∀ d, 1801 ≤ d → d ≤ 2025 →
  let (p, q) := pair_for_d d
  ∀ a_mod < p * q,
    let i := find_i_loop a_mod d (p * q) (p * q)
    i < p * q ∧ p ∣ a_mod + i * d ∧ q ∣ a_mod + i * d := by
  decide

theorem exists_i_dvd_decidable : ∀ d, 1 ≤ d → d ≤ 2025 →
  ∀ a_mod < (pair_for_d d).1 * (pair_for_d d).2,
    ∃ i < (pair_for_d d).1 * (pair_for_d d).2,
      (pair_for_d d).1 ∣ a_mod + i * d ∧ (pair_for_d d).2 ∣ a_mod + i * d := fun d hd1 hd2 a_mod ha_mod ↦
  let p := (pair_for_d d).1
  let q := (pair_for_d d).2
  if h1 : d ≤ 200 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_1 d hd1 h1 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h2 : d ≤ 400 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_2 d (not_le.mp h1) h2 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h3 : d ≤ 600 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_3 d (not_le.mp h2) h3 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h4 : d ≤ 800 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_4 d (not_le.mp h3) h4 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h5 : d ≤ 1000 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_5 d (not_le.mp h4) h5 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h6 : d ≤ 1200 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_6 d (not_le.mp h5) h6 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h7 : d ≤ 1400 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_7 d (not_le.mp h6) h7 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h8 : d ≤ 1600 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_8 d (not_le.mp h7) h8 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else if h9 : d ≤ 1800 then
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_9 d (not_le.mp h8) h9 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩
  else
    let ⟨hi, hp, hq⟩ := exists_i_dvd_decidable_10 d (not_le.mp h9) hd2 a_mod ha_mod
    ⟨find_i_loop a_mod d (p * q) (p * q), hi, hp, hq⟩

theorem pair_for_d_ok : ∀ d, 1 ≤ d → d ≤ 2025 →
  let (p, q) := pair_for_d d
  Nat.Prime p ∧ Nat.Prime q ∧ p % 10 ≠ q % 10 ∧ p * q ≤ 150 := by
  decide

theorem oeis_381159_conjecture_0.disproof :
  ¬ ∃ (a d : ℕ),
    2 ≤ a ∧
    1 ≤ d ∧
    d ≤ 2025 ∧
    ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd_pos, hd_le, h_cond⟩
  have h_prop := pair_for_d_ok d hd_pos hd_le
  have h_dec := exists_i_dvd_decidable d hd_pos hd_le
  generalize h_pair : pair_for_d d = pq at h_prop h_dec
  rcases pq with ⟨p, q⟩
  rcases h_prop with ⟨hp, hq, hdiff, hpq_le⟩
  have hpq_pos : 0 < p * q := by
    have hp_pos : 0 < p := Nat.Prime.pos hp
    have hq_pos : 0 < q := Nat.Prime.pos hq
    exact Nat.mul_pos hp_pos hq_pos
  have h_lt : a % (p * q) < p * q := Nat.mod_lt a hpq_pos
  rcases h_dec (a % (p * q)) h_lt with ⟨i, hi_lt, hdiv_p_mod, hdiv_q_mod⟩
  have ⟨hdiv_p, hdiv_q⟩ := exists_i_dvd_helper a d p q i hdiv_p_mod hdiv_q_mod
  have hi_150 : i < 150 := lt_of_lt_of_le hi_lt hpq_le
  have h_not := no_lopsided_of_primes a d p q i hp hq hdiff hdiv_p hdiv_q ha
  exact h_not (h_cond ⟨i, hi_150⟩)
