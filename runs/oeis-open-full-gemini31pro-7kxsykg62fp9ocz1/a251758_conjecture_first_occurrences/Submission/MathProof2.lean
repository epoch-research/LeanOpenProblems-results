import Mathlib

open Nat Finset

lemma divisors_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
  (Nat.divisors (p * q)) = {1, p, q, p * q} := by
  ext d
  rw [Nat.mem_divisors]
  simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨hdvd, hnz⟩
    have h1 : d ∣ p ∨ p ∣ d := by sorry
    sorry
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨one_dvd _, mul_ne_zero hp.ne_zero hq.ne_zero⟩
    · exact ⟨dvd_mul_right _ _, mul_ne_zero hp.ne_zero hq.ne_zero⟩
    · exact ⟨dvd_mul_left _ _, mul_ne_zero hp.ne_zero hq.ne_zero⟩
    · exact ⟨dvd_rfl, mul_ne_zero hp.ne_zero hq.ne_zero⟩

