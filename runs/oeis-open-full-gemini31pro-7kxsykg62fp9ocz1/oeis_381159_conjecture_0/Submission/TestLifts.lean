import Mathlib

def check_pair (p q d : ℕ) : Bool :=
  let pq := p * q
  (List.range pq).all (fun a =>
    (List.range pq).any (fun i => (a + i * d) % p == 0 && (a + i * d) % q == 0)
  )

lemma check_pair_lifts (p q d a : ℕ) (hpq : p * q > 0)
    (h : check_pair p q d = true) :
    ∃ i < p * q, (a + i * d) % p = 0 ∧ (a + i * d) % q = 0 := by
  let pq := p * q
  have h1 : ((List.range pq).all (fun a => (List.range pq).any (fun i => (a + i * d) % p == 0 && (a + i * d) % q == 0))) = true := h
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
    have heqp : ((a % pq + i * d) % p = 0) := beq_iff_eq.mp h5p
    have heqq : ((a % pq + i * d) % q = 0) := beq_iff_eq.mp h5q
    have h_div_mod : pq * (a / pq) + a % pq = a := Nat.div_add_mod a pq
    constructor
    · have H_eq1 : a + i * d = (a % pq + i * d) + ((a / pq) * q) * p := by
        calc a + i * d = (pq * (a / pq) + a % pq) + i * d := by rw [h_div_mod]
             _ = a % pq + i * d + (p * q) * (a / pq) := by ring
             _ = (a % pq + i * d) + ((a / pq) * q) * p := by ring
      rw [H_eq1, Nat.add_mul_mod_self_right]
      exact heqp
    · have H_eq1 : a + i * d = (a % pq + i * d) + ((a / pq) * p) * q := by
        calc a + i * d = (pq * (a / pq) + a % pq) + i * d := by rw [h_div_mod]
             _ = a % pq + i * d + (p * q) * (a / pq) := by ring
             _ = (a % pq + i * d) + ((a / pq) * p) * q := by ring
      rw [H_eq1, Nat.add_mul_mod_self_right]
      exact heqq
