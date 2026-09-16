import Submission.Spec
import Mathlib

open Nat Finset

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
