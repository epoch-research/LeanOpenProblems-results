import FormalConjectures.Util.ProblemImports

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

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0 :
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d)
  := by sorry

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def check_pair (p q d : ℕ) : Bool :=
  let pq := p * q
  let d_mod := d % pq
  (List.range pq).all (fun a =>
    (List.range pq).any (fun i => (a + i * d_mod) % p == 0 && (a + i * d_mod) % q == 0)
  )

def get_valid_pair (d : ℕ) : ℕ × ℕ :=
  let pairs := [(2, 3), (2, 5), (2, 7), (2, 11), (2, 13), (3, 5), (3, 7), (3, 11), (3, 17), (5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]
  pairs.find? (fun ⟨p, q⟩ => d % p != 0 && d % q != 0) |>.getD (2, 3)

def my_is_prime (p : ℕ) : Bool :=
  p == 2 || p == 3 || p == 5 || p == 7 || p == 11 || p == 13 || p == 17

def d_is_bad (d : ℕ) : Bool :=
  let ⟨p, q⟩ := get_valid_pair d
  Nat.ble (p * q) 150 && (p % 10 != q % 10) && check_pair p q d && my_is_prime p && my_is_prime q

theorem all_d_bad : (List.range 2026).all (fun d => if d == 0 then true else d_is_bad d) = true := by decide

lemma my_is_prime_eq_prime (p : ℕ) (h : my_is_prime p = true) : p.Prime := by
  have h_bound : p < 18 := by
    by_contra h_ge
    have h_false : my_is_prime p = false := by
      unfold my_is_prime
      have h1 : p ≠ 2 := by omega
      have h2 : p ≠ 3 := by omega
      have h3 : p ≠ 5 := by omega
      have h4 : p ≠ 7 := by omega
      have h5 : p ≠ 11 := by omega
      have h6 : p ≠ 13 := by omega
      have h7 : p ≠ 17 := by omega
      simp [h1, h2, h3, h4, h5, h6, h7]
    rw [h] at h_false
    contradiction
  have H : ∀ (x : ℕ), x < 18 → my_is_prime x = true → x.Prime := by decide
  exact H p h_bound h

lemma check_pair_lifts (p q d a : ℕ) (hpq : p * q > 0)
    (h : check_pair p q d = true) :
    ∃ i < p * q, (a + i * d) % p = 0 ∧ (a + i * d) % q = 0 := by
  let pq := p * q
  have h1 : ((List.range pq).all (fun a => (List.range pq).any (fun i => (a + i * (d % pq)) % p == 0 && (a + i * (d % pq)) % q == 0))) = true := h
  have h2 := List.all_eq_true.mp h1
  have h3 := h2 (a % pq) (List.mem_range.mpr (Nat.mod_lt a hpq))
  have h4 := List.any_eq_true.mp h3
  rcases h4 with ⟨i, hi, h5⟩
  have hi_lt : i < pq := List.mem_range.mp hi
  use i
  constructor
  · exact hi_lt
  · rw [Bool.and_eq_true] at h5
    rcases h5 with ⟨h5p, h5q⟩
    have heqp : ((a % pq + i * (d % pq)) % p = 0) := beq_iff_eq.mp h5p
    have heqq : ((a % pq + i * (d % pq)) % q = 0) := beq_iff_eq.mp h5q
    have h_div_mod : pq * (a / pq) + a % pq = a := Nat.div_add_mod a pq
    have h_d_div_mod : pq * (d / pq) + d % pq = d := Nat.div_add_mod d pq
    constructor
    · have H_eq1 : a + i * d = (a % pq + i * (d % pq)) + (a / pq * q + i * (d / pq) * q) * p := by
        calc a + i * d = (pq * (a / pq) + a % pq) + i * d := by rw [h_div_mod]
             _ = (pq * (a / pq) + a % pq) + i * (pq * (d / pq) + d % pq) := by rw [h_d_div_mod]
             _ = a % pq + i * (d % pq) + (p * q) * (a / pq) + i * ((p * q) * (d / pq)) := by ring
             _ = (a % pq + i * (d % pq)) + (a / pq * q + i * (d / pq) * q) * p := by ring
      rw [H_eq1, Nat.add_mul_mod_self_right]
      exact heqp
    · have H_eq1 : a + i * d = (a % pq + i * (d % pq)) + (a / pq * p + i * (d / pq) * p) * q := by
        calc a + i * d = (pq * (a / pq) + a % pq) + i * d := by rw [h_div_mod]
             _ = (pq * (a / pq) + a % pq) + i * (pq * (d / pq) + d % pq) := by rw [h_d_div_mod]
             _ = a % pq + i * (d % pq) + (p * q) * (a / pq) + i * ((p * q) * (d / pq)) := by ring
             _ = (a % pq + i * (d % pq)) + (a / pq * p + i * (d / pq) * p) * q := by ring
      rw [H_eq1, Nat.add_mul_mod_self_right]
      exact heqq

theorem oeis_381159_conjecture_0.disproof : ¬ (type_of% @oeis_381159_conjecture_0) := by
  intro h
  rcases h with ⟨a, d, ha, hd1, hd2, H⟩
  have hd_mem : d ∈ List.range 2026 := List.mem_range.mpr (by omega)
  have hd_bad_all := List.all_eq_true.mp all_d_bad d hd_mem
  have h_not : ¬((d == 0) = true) := by
    intro h_eq
    rw [beq_iff_eq] at h_eq
    omega
  rw [if_neg h_not] at hd_bad_all
  change d_is_bad d = true at hd_bad_all
  unfold d_is_bad at hd_bad_all
  revert hd_bad_all
  have h_pair : get_valid_pair d = get_valid_pair d := rfl
  generalize h_pair' : get_valid_pair d = pair
  rcases pair with ⟨p, q⟩
  intro hd_bad
  repeat rw [Bool.and_eq_true] at hd_bad
  rcases hd_bad with ⟨⟨⟨⟨hpq_le, hpq_ne⟩, hpq_check⟩, hp_prime⟩, hq_prime⟩
  have hp_pos : p > 0 := Nat.Prime.pos (my_is_prime_eq_prime p hp_prime)
  have hq_pos : q > 0 := Nat.Prime.pos (my_is_prime_eq_prime q hq_prime)
  have h_pq_gt_0 : p * q > 0 := Nat.mul_pos hp_pos hq_pos
  have ⟨i, hi_lt, ⟨hip, hiq⟩⟩ := check_pair_lifts p q d a h_pq_gt_0 hpq_check
  have h_pq_le_150 : p * q ≤ 150 := Nat.le_of_ble_eq_true hpq_le
  have hi_150 : i < 150 := by omega
  have H_i := H ⟨i, hi_150⟩
  have H_cond : A381159_condition (a + i * d) := H_i
  have haid : a + i * d ≥ 2 := by omega
  have h_p_prime : p.Prime := my_is_prime_eq_prime p hp_prime
  have h_q_prime : q.Prime := my_is_prime_eq_prime q hq_prime
  have h_p_dvd : p ∣ a + i * d := Nat.dvd_of_mod_eq_zero hip
  have h_q_dvd : q ∣ a + i * d := Nat.dvd_of_mod_eq_zero hiq
  have h_p_in : p ∈ (a + i * d).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨h_p_prime, h_p_dvd, by omega⟩
  have h_q_in : q ∈ (a + i * d).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨h_q_prime, h_q_dvd, by omega⟩
  unfold A381159_condition at H_cond
  have h_p_im : (p % 10) ∈ (a + i * d).primeFactors.image (fun x => x % 10) := by
    rw [Finset.mem_image]
    exact ⟨p, h_p_in, rfl⟩
  have h_q_im : (q % 10) ∈ (a + i * d).primeFactors.image (fun x => x % 10) := by
    rw [Finset.mem_image]
    exact ⟨q, h_q_in, rfl⟩
  have h_eq : p % 10 = q % 10 := by
    have h_card : ((a + i * d).primeFactors.image (fun x => x % 10)).card ≤ 1 := H_cond
    have H_le_one : ∀ (x y : ℕ), x ∈ (a + i * d).primeFactors.image (fun x => x % 10) → y ∈ (a + i * d).primeFactors.image (fun x => x % 10) → x = y := by
      intro x y hx hy
      exact Finset.card_le_one.mp h_card x hx y hy
    exact H_le_one (p % 10) (q % 10) h_p_im h_q_im
  have h_ne : p % 10 ≠ q % 10 := bne_iff_ne.mp hpq_ne
  contradiction
