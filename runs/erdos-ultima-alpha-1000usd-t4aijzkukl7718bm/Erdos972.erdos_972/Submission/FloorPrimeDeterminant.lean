import FormalConjecturesUtil

/-! A multiplicity restriction for the four-factor floor strip. This file
supplies no signed correlation bound and does not settle Erdős 972. -/
namespace Erdos972FloorPrimeDeterminant

/-- In the indicated balanced range, two lattice points in the same floor
strip have equal cross products. The strict floor endpoint is retained. -/
lemma cross_products_eq {α : ℝ} {m k p q r s : ℕ}
    (hα : 0 < α) (hm : 0 < m) (hq : 0 < q) (hs : 0 < s)
    (hqM : (q : ℝ) ≤ α * m) (hsM : (s : ℝ) ≤ α * m)
    (h₁ : k * q = ⌊α * (m * p : ℕ)⌋₊)
    (h₂ : k * s = ⌊α * (m * r : ℕ)⌋₊) :
    p * s = r * q := by
  have hC : 0 < α * m := mul_pos hα (Nat.cast_pos.mpr hm)
  have hp0 : 0 ≤ α * (m * p : ℕ) := by positivity
  have hr0 : 0 ≤ α * (m * r : ℕ) := by positivity
  have h₁lo := Nat.floor_le hp0
  have h₁hi := Nat.lt_floor_add_one (α * (m * p : ℕ))
  have h₂lo := Nat.floor_le hr0
  have h₂hi := Nat.lt_floor_add_one (α * (m * r : ℕ))
  rw [← h₁] at h₁lo h₁hi
  rw [← h₂] at h₂lo h₂hi
  push_cast at h₁lo h₁hi h₂lo h₂hi
  have hA := mul_lt_mul_of_pos_right h₁hi (Nat.cast_pos.mpr hs : (0 : ℝ) < s)
  have hB := mul_le_mul_of_nonneg_right h₂lo (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hD := mul_lt_mul_of_pos_right h₂hi (Nat.cast_pos.mpr hq : (0 : ℝ) < q)
  have hE := mul_le_mul_of_nonneg_right h₁lo (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hps : (p : ℝ) * s < r * q + 1 := by
    apply (mul_lt_mul_iff_right₀ hC).mp
    nlinarith only [hA, hB, hsM]
  have hrq : (r : ℝ) * q < p * s + 1 := by
    apply (mul_lt_mul_iff_right₀ hC).mp
    nlinarith only [hD, hE, hqM]
  have hps' : p * s < r * q + 1 := by exact_mod_cast hps
  have hrq' : r * q < p * s + 1 := by exact_mod_cast hrq
  omega

/-- Equality of two ratios of primes gives identical ordered pairs, apart
from the diagonal ratio one. -/
lemma prime_ratio_alternatives {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (_hs : s.Prime)
    (he : p * s = r * q) :
    (p = r ∧ q = s) ∨ (p = q ∧ r = s) := by
  have hd : p ∣ r * q := he ▸ dvd_mul_right p s
  rcases hp.dvd_mul.mp hd with hpr | hpq
  · have hpr' : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
    subst r
    have hsq : s = q := Nat.eq_of_mul_eq_mul_left hp.pos he
    exact Or.inl ⟨rfl, hsq.symm⟩
  · have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    subst q
    have hsr : s = r := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa [mul_comm] using he)
    exact Or.inr ⟨rfl, hsr.symm⟩

/-- Each fixed pair of outer multipliers admits at most one non-diagonal
prime pair in this balanced range. There may still be many different outer
multiplier pairs, with uncontrolled coefficient signs. -/
theorem non_diagonal_pair_unique {α : ℝ} {m k p q r s : ℕ}
    (hα : 0 < α) (hm : 0 < m)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q)
    (hqM : (q : ℝ) ≤ α * m) (hsM : (s : ℝ) ≤ α * m)
    (h₁ : k * q = ⌊α * (m * p : ℕ)⌋₊)
    (h₂ : k * s = ⌊α * (m * r : ℕ)⌋₊) :
    p = r ∧ q = s := by
  have he := cross_products_eq hα hm hq.pos hs.pos hqM hsM h₁ h₂
  exact (prime_ratio_alternatives hp hq hr hs he).resolve_right (fun h => hpq h.1)

#print axioms cross_products_eq
#print axioms non_diagonal_pair_unique

end Erdos972FloorPrimeDeterminant
