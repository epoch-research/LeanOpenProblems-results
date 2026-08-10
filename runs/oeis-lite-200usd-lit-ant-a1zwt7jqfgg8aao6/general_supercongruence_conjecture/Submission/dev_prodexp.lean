import Mathlib
open scoped BigOperators
open Finset

variable {R : Type*} [CommRing R]

-- (a) d ∣ ∏(1+x) - 1
theorem prodexp_a (d : R) (x : ι → R) (s : Finset ι) (hx : ∀ j ∈ s, d ∣ x j) :
    d ∣ (∏ j ∈ s, (1 + x j)) - 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hP : (1 + x i) * ∏ j ∈ s, (1 + x j) - 1
        = ((∏ j ∈ s, (1 + x j)) - 1) + x i * ∏ j ∈ s, (1 + x j) := by ring
    rw [hP]
    apply dvd_add
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · exact Dvd.dvd.mul_right (hx i (Finset.mem_insert_self i s)) _

-- (b) d² ∣ ∏(1+x) - 1 - ∑x
theorem prodexp_b (d : R) (x : ι → R) (s : Finset ι) (hx : ∀ j ∈ s, d ∣ x j) :
    d^2 ∣ (∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hP : (1 + x i) * ∏ j ∈ s, (1 + x j) - 1 - (x i + ∑ j ∈ s, x j)
        = ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j)
          + x i * ((∏ j ∈ s, (1 + x j)) - 1) := by ring
    rw [hP]
    apply dvd_add
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · rw [pow_two]
      exact mul_dvd_mul (hx i (Finset.mem_insert_self i s))
        (prodexp_a d x s (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

-- (c) d³ ∣ 2∏ - 2 - 2∑x - ((∑x)² - ∑x²)
theorem prodexp_c (d : R) (x : ι → R) (s : Finset ι) (hx : ∀ j ∈ s, d ∣ x j) :
    d^3 ∣ 2 * (∏ j ∈ s, (1 + x j)) - 2 - 2 * (∑ j ∈ s, x j)
          - ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    have hP : 2 * ((1 + x i) * ∏ j ∈ s, (1 + x j)) - 2 - 2 * (x i + ∑ j ∈ s, x j)
          - ((x i + ∑ j ∈ s, x j)^2 - ((x i)^2 + ∑ j ∈ s, (x j)^2))
        = (2 * (∏ j ∈ s, (1 + x j)) - 2 - 2 * (∑ j ∈ s, x j)
            - ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2))
          + 2 * x i * ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j) := by ring
    rw [hP]
    apply dvd_add
    · exact ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    · rw [pow_succ, pow_two]
      have h1 : d ∣ x i := hx i (Finset.mem_insert_self i s)
      have h2 : d^2 ∣ (∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j :=
        prodexp_b d x s (fun j hj => hx j (Finset.mem_insert_of_mem hj))
      have : d * d * d ∣ (2 * x i) * ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j) := by
        have hxi : d ∣ 2 * x i := Dvd.dvd.mul_left h1 2
        calc d * d * d = d * (d * d) := by ring
          _ ∣ (2 * x i) * ((∏ j ∈ s, (1 + x j)) - 1 - ∑ j ∈ s, x j) := by
              rw [← pow_two]; exact mul_dvd_mul hxi h2
      exact this

-- main: in ZMod (p^c), product ≡ 1 mod p^{3a}
theorem prod_expansion_main {p a c : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hac : 3 * a ≤ c)
    (x : ι → ZMod (p^c)) (s : Finset ι)
    (hx : ∀ j ∈ s, ((p^a : ℕ) : ZMod (p^c)) ∣ x j)
    (hs1 : ((p^(3*a) : ℕ) : ZMod (p^c)) ∣ ∑ j ∈ s, x j)
    (hs2 : ((p^(3*a) : ℕ) : ZMod (p^c)) ∣ ∑ j ∈ s, (x j)^2) :
    ((p^(3*a) : ℕ) : ZMod (p^c)) ∣ (∏ j ∈ s, (1 + x j)) - 1 := by
  haveI : NeZero (p^c) := ⟨pow_ne_zero _ (Fact.out : p.Prime).pos.ne'⟩
  set d : ZMod (p^c) := ((p^a : ℕ) : ZMod (p^c)) with hd
  have hcast : ((p^(3*a) : ℕ) : ZMod (p^c)) = d^3 := by
    rw [hd, ← Nat.cast_pow, ← pow_mul]; congr 1; ring
  rw [hcast] at hs1 hs2 ⊢
  have hc := prodexp_c d x s hx
  -- d^3 ∣ 2*(∏-1)
  have hsx2 : d^3 ∣ (∑ j ∈ s, x j)^2 := by
    rw [pow_two]; exact Dvd.dvd.mul_right hs1 _
  have key : d^3 ∣ 2 * ((∏ j ∈ s, (1 + x j)) - 1) := by
    have e : 2 * ((∏ j ∈ s, (1 + x j)) - 1)
        = (2 * (∏ j ∈ s, (1 + x j)) - 2 - 2 * (∑ j ∈ s, x j)
            - ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2))
          + 2 * (∑ j ∈ s, x j) + ((∑ j ∈ s, x j)^2 - ∑ j ∈ s, (x j)^2) := by ring
    rw [e]
    apply dvd_add
    apply dvd_add hc (Dvd.dvd.mul_left hs1 2)
    exact dvd_sub hsx2 hs2
  -- 2 is a unit
  have h2u : IsUnit (2 : ZMod (p^c)) := by
    have : IsUnit (((2:ℕ) : ZMod (p^c))) := by
      rw [ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.pow_right; rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
        (by intro hd2; have := Nat.le_of_dvd (by norm_num) hd2; omega)
    simpa using this
  obtain ⟨w, hw⟩ := key
  obtain ⟨v, hv⟩ := h2u.exists_left_inv
  refine ⟨v * w, ?_⟩
  rw [show (∏ j ∈ s, (1 + x j)) - 1 = v * (2 * ((∏ j ∈ s, (1 + x j)) - 1)) by
        rw [← mul_assoc, hv, one_mul], hw]
  ring
