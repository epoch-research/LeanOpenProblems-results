import FormalConjectures.Util.ProblemImports

open Finset

-- General product expansion modulo e^3 = 0.
-- ∏ (1 + e * b i) = 1 + e * (∑ b) + e² * ((∑b)² - ∑ b²) * half,  where 2*half=1.
theorem prod_one_add_e {R : Type*} [CommRing R] (e : R) (he : e^3 = 0)
    (half : R) (hhalf : 2 * half = 1)
    (s : Finset ℕ) (b : ℕ → R) :
    ∏ i ∈ s, (1 + e * b i)
      = 1 + e * (∑ i ∈ s, b i)
          + e^2 * ((∑ i ∈ s, b i)^2 - (∑ i ∈ s, (b i)^2)) * half := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    linear_combination (-(e^2 * b a * (∑ i ∈ s, b i))) * hhalf
      + (b a * ((∑ i ∈ s, b i)^2 - (∑ i ∈ s, (b i)^2)) * half) * he

-- Sum of all elements of ZMod p is 0 (p odd prime)
theorem sum_zmod_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2:ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
      have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hneg : ∑ x : ZMod p, x = ∑ x : ZMod p, (-x) :=
    (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => x)).symm
  rw [Finset.sum_neg_distrib] at hneg
  have h2eq : (2 : ZMod p) * ∑ x : ZMod p, x = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2eq).resolve_left h2

-- Sum of inverses of all elements is 0
theorem sum_inv_zmod_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
    Equiv.sum_comp (Equiv.mk (·⁻¹) (·⁻¹) inv_inv inv_inv) (fun x => x)
  rw [this]; exact sum_zmod_eq_zero p hp2
