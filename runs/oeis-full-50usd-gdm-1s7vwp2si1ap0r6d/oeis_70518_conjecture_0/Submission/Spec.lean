import FormalConjectures.Util.ProblemImports

open Polynomial

set_option maxRecDepth 200000 in
/--
A070518: Value of $n$-th cyclotomic polynomial at $n$.
$$ a(n) = \Phi_n(n) $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Polynomial.eval (Int.ofNat n) (cyclotomic n ℤ)).natAbs


def gas_pow {M : Type*} [Mul M] [One M] (x : M) : ℕ → ℕ → M
  | 0, _ => 1
  | _, 0 => 1
  | gas + 1, n =>
    if n % 2 = 0 then
      let y := gas_pow x gas (n / 2)
      y * y
    else
      let y := gas_pow x gas (n / 2)
      y * y * x

lemma gas_pow_eq_pow {M : Type*} [CommMonoid M] (x : M) :
    ∀ (gas n : ℕ), n < 2 ^ gas → gas_pow x gas n = x ^ n := by
  intro gas
  induction' gas with gas ih
  · intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    simp [gas_pow]
  · intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      simp [gas_pow]
    · have h_div : n / 2 < 2 ^ gas := by
        rw [Nat.pow_succ] at hn
        omega
      have ih_div := ih (n / 2) h_div
      rcases gas with _ | gas'
      · have hn1 : n = 1 := by omega
        subst hn1
        simp [gas_pow]
      · simp only [gas_pow]
        by_cases h_even : n % 2 = 0
        · rw [if_pos h_even, ih_div]
          rw [← sq, ← pow_mul]
          congr 1
          omega
        · rw [if_neg h_even, ih_div]
          rw [← sq, ← pow_mul, ← pow_succ]
          congr 1
          omega

set_option maxRecDepth 200000 in
theorem proper_coprimes :
    ∀ d ∈ Nat.properDivisors 28341, ((gas_pow (28341 : ZMod (283411^2)) 15 d - 1).val).Coprime (283411^2) := by
  decide

theorem pow_28341 : (28341 : ZMod (283411^2)) ^ 28341 = 1 := by
  rw [← gas_pow_eq_pow _ 30 28341 (by decide)]
  rfl

lemma test_eval_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) (p : R[X]) :
    eval (f r) (map f p) = f (eval r p) := by
  rw [eval_map, eval₂_at_apply]

lemma eval_dvd_of_dvd {R : Type*} [CommRing R] {p q : R[X]} (h : p ∣ q) (x : R) :
    p.eval x ∣ q.eval x := by
  rcases h with ⟨r, rfl⟩
  rw [eval_mul]
  exact dvd_mul_right (eval x p) (eval x r)

lemma eval_X_pow_sub_one {R : Type*} [CommRing R] (d : ℕ) (n : R) :
    eval n (X ^ d - 1 : R[X]) = n ^ d - 1 := by
  simp

lemma eval_cyclotomic_dvd {R : Type*} [CommRing R] (d : ℕ) (n : R) :
    eval n (cyclotomic d R) ∣ n ^ d - 1 := by
  have h := eval_dvd_of_dvd (cyclotomic.dvd_X_pow_sub_one d R) n
  rw [eval_X_pow_sub_one] at h
  exact h

lemma isUnit_iff_val_coprime {M : ℕ} [NeZero M] (x : ZMod M) :
    IsUnit x ↔ x.val.Coprime M := by
  have h_val := ZMod.natCast_zmod_val x
  nth_rw 1 [← h_val]
  exact ZMod.isUnit_iff_coprime x.val M

lemma eq_zero_of_prod_eq_zero_of_units {R : Type*} [CommRing R] {s : Finset ℕ} {f : ℕ → R} {k : ℕ} (hk : k ∈ s)
    (h_prod : ∏ i ∈ s, f i = 0) (h_units : ∀ i ∈ s, i ≠ k → IsUnit (f i)) :
    f k = 0 := by
  rw [← Finset.mul_prod_erase s f hk] at h_prod
  have h_prod_units : IsUnit (∏ i ∈ s.erase k, f i) := by
    rw [IsUnit.prod_iff]
    intro i hi
    have hi_mem := Finset.mem_of_mem_erase hi
    rw [Finset.mem_erase] at hi
    exact h_units i hi_mem hi.1
  rcases h_prod_units with ⟨u, hu⟩
  rw [← hu] at h_prod
  have h_inv : f k * ↑u * ↑(u⁻¹) = 0 * ↑(u⁻¹) := by
    rw [h_prod, zero_mul]
  rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, zero_mul] at h_inv
  exact h_inv

lemma eval_prod_cyclotomic {R : Type*} [CommRing R] {n : ℕ} (hpos : 0 < n) (x : R) :
    ∏ i ∈ Nat.divisors n, eval x (cyclotomic i R) = x ^ n - 1 := by
  rw [← eval_prod, prod_cyclotomic_eq_X_pow_sub_one hpos, eval_X_pow_sub_one]

theorem zmod_zero_iff_dvd_natAbs (a : ℤ) (b : ℕ) :
    (a : ZMod b) = 0 ↔ b ∣ a.natAbs := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]

theorem eval_cyclotomic_zmod (n : ℕ) (M : ℕ) :
    ((eval (Int.ofNat n) (cyclotomic n ℤ) : ℤ) : ZMod M) = eval (n : ZMod M) (cyclotomic n (ZMod M)) := by
  have h := cyclotomic.eval_apply (Int.ofNat n) n (Int.castRingHom (ZMod M))
  simp only [Int.coe_castRingHom] at h
  rw [← h]
  simp

set_option maxRecDepth 200000 in
/--
A070518 a(28341) is divisible by 283411^2. What is the next n such that a(n) is not squarefree? - _Jianing Song_, Nov 01 2024
-/
theorem oeis_70518_conjecture_0 :
    (283411 : ℕ) ^ 2 ∣ a 28341 := by
  unfold a
  rw [← zmod_zero_iff_dvd_natAbs]
  rw [eval_cyclotomic_zmod]
  have h_prod := eval_prod_cyclotomic (by decide : 0 < 28341) (28341 : ZMod (283411^2))
  have h_pow := pow_28341
  have h_prod_zero : ∏ i ∈ Nat.divisors 28341, eval (28341 : ZMod (283411^2)) (cyclotomic i (ZMod (283411^2))) = 0 := by
    rw [h_prod]
    rw [h_pow]
    ring
  have h_units : ∀ i ∈ Nat.divisors 28341, i ≠ 28341 → IsUnit (eval (28341 : ZMod (283411^2)) (cyclotomic i (ZMod (283411^2)))) := by
    intro i hi hi_ne
    have hi_prop : i ∈ Nat.properDivisors 28341 := by
      rw [Nat.mem_properDivisors]
      have h_dvd := Nat.dvd_of_mem_divisors hi
      have h_le := Nat.divisor_le hi
      exact ⟨h_dvd, by omega⟩
    have hi_lt : i < 32768 := by
      have := (Nat.mem_properDivisors.mp hi_prop).2
      omega
    have h_unit_pow : IsUnit ((28341 : ZMod (283411^2)) ^ i - 1) := by
      rw [isUnit_iff_val_coprime]
      have h_gas := gas_pow_eq_pow (28341 : ZMod (283411^2)) 15 i hi_lt
      rw [← h_gas]
      exact proper_coprimes i hi_prop
    have h_dvd := eval_cyclotomic_dvd i (28341 : ZMod (283411^2))
    exact isUnit_of_dvd_unit h_dvd h_unit_pow
  exact eq_zero_of_prod_eq_zero_of_units (Nat.mem_divisors_self 28341 (by decide)) h_prod_zero h_units


