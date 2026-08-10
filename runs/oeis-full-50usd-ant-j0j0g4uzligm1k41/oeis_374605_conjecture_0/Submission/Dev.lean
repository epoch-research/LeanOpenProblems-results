import FormalConjectures.Util.ProblemImports

open Finset

/-- Power sum over `ZMod p`: for `j ≤ p-2`, `∑_{x} x^j = 0`. -/
theorem powsum (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : j < p - 1) :
    ∑ x : ZMod p, x ^ j = 0 :=
  FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) j (by rw [ZMod.card]; exact hj)

open Nat in
/-- `descFactorial` of `p - m` as a product in `ZMod p`. -/
theorem descFac_cast (p m k : ℕ) [Fact p.Prime] (hm : m ≤ p) :
    ((Nat.descFactorial (p - m) k : ZMod p)) = ∏ i ∈ Finset.range k, ((-(m : ZMod p)) - i) := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.prod_range_natCast_sub]
  apply Finset.prod_congr rfl
  intro i _
  push_cast [Nat.cast_sub hm]
  rw [ZMod.natCast_self]
  ring

/-- `k!` is invertible in `ZMod p` when `k < p`. -/
theorem fac_ne (p k : ℕ) [Fact p.Prime] (hk : k < p) : (Nat.factorial k : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro h
  exact absurd ((Nat.Prime.dvd_factorial Fact.out).mp h) (by omega)

/-- Nat product identity `∏ (m+i) = descFactorial (m+k-1) k`. -/
theorem ascprod_nat (m k : ℕ) :
    (∏ i ∈ Finset.range k, (m + i)) = (m + k - 1).descFactorial k := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.prod_range_reflect]
  apply Finset.prod_congr rfl
  intro i hi; rw [Finset.mem_range] at hi; omega

/-- Product form in `ZMod p`. -/
theorem ascprod_cast (p m k : ℕ) [Fact p.Prime] :
    (∏ i ∈ Finset.range k, ((m : ZMod p) + i)) = (Nat.descFactorial (m + k - 1) k : ZMod p) := by
  rw [← ascprod_nat]; push_cast; ring

/-- Mod-`p` binomial residue: `C(p-m,k) ≡ (-1)^k C(m+k-1,k)`. -/
theorem binom_modp (p m k : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hmp : m ≤ p) (hk : k < p) :
    ((p - m).choose k : ZMod p) = (-1) ^ k * ((m + k - 1).choose k : ZMod p) := by
  have hf := fac_ne p k hk
  have key : (Nat.factorial k : ZMod p) * ((p - m).choose k : ZMod p)
      = (Nat.factorial k : ZMod p) * ((-1) ^ k * ((m + k - 1).choose k : ZMod p)) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, descFac_cast p m k hmp]
    have e1 : ∏ i ∈ Finset.range k, ((-(m : ZMod p)) - i)
        = (-1) ^ k * ∏ i ∈ Finset.range k, ((m : ZMod p) + i) := by
      rw [show ((-1 : ZMod p)) ^ k = ∏ _i ∈ Finset.range k, (-1 : ZMod p) by
            rw [Finset.prod_const, Finset.card_range], ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _; ring
    rw [e1, ascprod_cast p m k, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  exact mul_left_cancel₀ hf key

/-- Unit power-sum: `∑ x : units, x^j = 0` when `p-1 ∤ j`. -/
theorem upow (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : ¬ (p - 1 ∣ j)) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ j = 0 := by
  have := FiniteField.sum_pow_units (K := ZMod p) j
  rw [ZMod.card] at this
  rw [this, if_neg hj]

/-- Inverse power-sum over units `∑ (x⁻¹)^j = 0` when `p-1 ∤ j`. -/
theorem harmj (p : ℕ) [Fact p.Prime] (j : ℕ) (hj : ¬ (p - 1 ∣ j)) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p))⁻¹ ^ j = 0 := by
  have hb : ∑ x : (ZMod p)ˣ, ((x : ZMod p))⁻¹ ^ j = ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ j := by
    apply Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ)
    intro x
    simp only [Equiv.inv_apply]
    rw [Units.val_inv_eq_inv_val, inv_pow]
  rw [hb]; exact upow p j hj

/-- Harmonic sum over units is 0 (for `p ≥ 3`). -/
theorem harm (p : ℕ) [Fact p.Prime] (hp3 : 3 ≤ p) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p))⁻¹ = 0 := by
  have := harmj p 1 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  simpa only [pow_one] using this

/-- Sum of inverse squares over units is 0 (for `p ≥ 5`). -/
theorem harm2 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : (ZMod p)ˣ, ((x : ZMod p))⁻¹ ^ 2 = 0 :=
  harmj p 2 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
