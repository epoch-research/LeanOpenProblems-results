import Spec

open Nat Finset BigOperators

lemma choose_relation (p i : ℕ) :
    (p + i).choose (i + 1) * (i + 1) = p * (p + i).choose i := by
  have h1 : (p + i).choose (i + 1) * (p + i + 1) = (p + i + 1).choose (i + 1) * p := by
    have h := choose_mul_succ_eq (p + i) (i + 1)
    have : p + i + 1 - (i + 1) = p := by omega
    rwa [this] at h
  have h2 : (p + i + 1) * (p + i).choose i = (p + i + 1).choose (i + 1) * (i + 1) := by
    have h := succ_mul_choose_eq (p + i) i
    rfl
  have h5 : (p + i).choose (i + 1) * (i + 1) * (p + i + 1) = p * (p + i).choose i * (p + i + 1) := by
    calc (p + i).choose (i + 1) * (i + 1) * (p + i + 1)
      _ = (p + i).choose (i + 1) * (p + i + 1) * (i + 1) := by ring
      _ = (p + i + 1).choose (i + 1) * p * (i + 1) := by rw [h1]
      _ = (p + i + 1).choose (i + 1) * (i + 1) * p := by ring
      _ = (p + i + 1) * (p + i).choose i * p := by rw [← h2]
      _ = p * (p + i).choose i * (p + i + 1) := by ring
  have h_pos : p + i + 1 > 0 := by omega
  exact Nat.eq_of_mul_eq_mul_right h_pos h5

lemma choose_relation_gt (p j : ℕ) :
    (2 * p + j - 1).choose (p + j) * (2 * p + j) = p * (2 * p + j).choose (p + j) := by
  have h := choose_mul_succ_eq (2 * p + j - 1) (p + j)
  have h1 : 2 * p + j - 1 + 1 = 2 * p + j := by omega
  have h2 : 2 * p + j - 1 + 1 - (p + j) = p := by omega
  rw [h1, h2] at h
  rw [h, mul_comm]

lemma choose_pi_i_mod_p (p i : ℕ) (hp : p.Prime) (hi : i < p - 1) :
    (p + i).choose i ≡ 1 [MOD p] := by
  have : Fact hp.Prime := ⟨hp⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p + i) (k := i)
  have h1 : (p + i) % p = i := by
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : i % p = i := Nat.mod_eq_of_lt (by omega)
  have h3 : (p + i) / p = 1 := by
    rw [Nat.add_div (by omega)]
    have : i / p = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]
    simp
  have h4 : i / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h1, h2, h3, h4] at h
  have h5 : i.choose i = 1 := Nat.choose_self i
  have h6 : Nat.choose 1 0 = 1 := Nat.choose_zero_right 1
  rw [h5, h6] at h
  simp only [mul_one] at h
  exact h

lemma term_sq_eq (p i : ℕ) (hp : p.Prime) (hi : i < p - 1) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (((p + i : ℕ).choose (i + 1) : ZMod (p ^ 3)) ^ 2) = (p : ZMod (p ^ 3)) ^ 2 * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
  intro h_p3
  have h_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi
  have h_relation := choose_relation p i
  have h_cast : (((p + i).choose (i + 1) * (i + 1) : ℕ) : ZMod (p ^ 3)) = (((p * (p + i).choose i) : ℕ) : ZMod (p ^ 3)) := by
    congr 1
  push_cast at h_cast
  have h_mul : ((p + i).choose (i + 1) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) * ((p + i).choose i : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by
    calc ((p + i).choose (i + 1) : ZMod (p ^ 3))
      _ = ((p + i).choose (i + 1) : ZMod (p ^ 3)) * (((i + 1 : ℕ) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹) := by rw [unit_mul_inv h_unit, mul_one]
      _ = (((p + i).choose (i + 1) : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by ring
      _ = (p : ZMod (p ^ 3)) * ((p + i).choose i : ZMod (p ^ 3)) * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [h_cast]
  have h_sq : ((p + i).choose (i + 1) : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((p + i).choose i : ZMod (p ^ 3)) ^ 2 * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2 := by
    rw [h_mul]
    ring
  rw [h_sq]
  have h_mod_p : (p + i).choose i ≡ 1 [MOD p] := choose_pi_i_mod_p p i hp hi
  have h_cast_p : (((p + i).choose i : ZMod (p ^ 3)).cast : ZMod p) = (1 : ZMod p) := by
    have h_eq : (((p + i).choose i : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rwa [ZMod.natCast_eq_natCast_iff]
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map : (((p + i).choose i : ZMod (p ^ 3)).cast : ZMod p) = f ((p + i).choose i : ZMod (p ^ 3)) := rfl
    rw [h_map, map_natCast f]
    exact h_eq
  have h_cast_sq : (((((p + i).choose i : ZMod (p ^ 3)) ^ 2).cast) : ZMod p) = 1 := by
    rw [RingHom.map_pow, h_cast_p]
    ring
  have h_sub_cast : (((((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1).cast) : ZMod p) = 0 := by
    rw [RingHom.map_sub, h_cast_sq]
    simp
  have h_mul_zero := p_sq_mul_zero_of_cast_zero p hp (((p + i).choose i : ZMod (p ^ 3)) ^ 2 - 1) h_sub_cast
  have h_final : (p : ZMod (p ^ 3)) ^ 2 * ((p + i).choose i : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 := by
    linear_combination h_mul_zero
  rw [h_final]

lemma sum_term_sq_zero (p : ℕ) (hp : p.Prime) (hp5 : p ≥ 5) :
    letI : NeZero (p ^ 3) := ⟨by
      have : p > 0 := hp.pos
      positivity⟩
    (∑ k ∈ Finset.Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) = 0 := by
  intro h_p3
  have h_sum : (∑ k ∈ Finset.Ico 1 p, (((p + k - 1).choose k : ZMod (p ^ 3)) ^ 2)) =
      ∑ i ∈ Finset.range (p - 1), (((p + i).choose (i + 1) : ZMod (p ^ 3)) ^ 2) := by
    rw [range_eq_Ico]
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      rw [Finset.mem_Ico] at hi ⊢
      omega
    · intro i1 hi1 i2 hi2 h_eq
      omega
    · intro j hj
      rw [Finset.mem_Ico] at hj
      refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
    · intro i hi
      rfl
  rw [h_sum]
  have h_congr : (∑ i ∈ Finset.range (p - 1), (((p + i).choose (i + 1) : ZMod (p ^ 3)) ^ 2)) =
      ∑ i ∈ Finset.range (p - 1), ((p : ZMod (p ^ 3)) ^ 2 * ((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < p - 1 := Finset.mem_range.mp hi
    exact term_sq_eq p i hp hi_lt
  rw [h_congr, ← mul_sum]
  have h_cast_eq : (((∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = 0) := by
    let f : ZMod (p ^ 3) →+* ZMod p := ZMod.castHom (by
      have : p > 0 := hp.pos
      exact dvd_pow_self p (by omega)) (ZMod p)
    have h_map_eq : (((∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)).cast : ZMod p) = f (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2))) := by
      rw [ZMod.castHom_apply]
    rw [h_map_eq, map_sum]
    have h_simp_term : ∀ i ∈ Finset.range (p - 1), f (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2) = ((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2 := by
      intro i hi
      have hi_lt : i < p - 1 := Finset.mem_range.mp hi
      have hi_unit : IsUnit ((i + 1 : ℕ) : ZMod (p ^ 3)) := isUnit_of_lt p i 3 hp hi_lt
      rw [f.map_pow, ringHom_map_inv f ((i + 1 : ℕ) : ZMod (p ^ 3)) hi_unit, map_natCast f (i + 1)]
    rw [sum_congr rfl h_simp_term]
    have h_sum_Ico : (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod p)⁻¹ ^ 2)) = ∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹ ^ 2) := by
      rw [range_eq_Ico]
      apply Finset.sum_bij (fun i _ => i + 1)
      · intro i hi
        rw [Finset.mem_Ico] at hi ⊢
        omega
      · intro i1 hi1 i2 hi2 h_eq
        omega
      · intro j hj
        rw [Finset.mem_Ico] at hj
        refine ⟨j - 1, by rw [Finset.mem_Ico]; omega, by omega⟩
      · intro i hi
        rfl
    rw [h_sum_Ico]
    exact sum_inv_sq_zero_ico p hp hp5
  have h_zero := p_sq_mul_zero_of_cast_zero p hp (∑ i ∈ Finset.range (p - 1), (((i + 1 : ℕ) : ZMod (p ^ 3))⁻¹ ^ 2)) h_cast_eq
  rw [h_zero]
