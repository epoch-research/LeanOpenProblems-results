import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 1000000


open Nat Matrix Complex Equiv

/--
A002454: Central factorial numbers: $a(n) = 4^n \cdot (n!)^2$.
-/
def a (n : ℕ) : ℕ := 4 ^ n * n.factorial ^ 2

open Matrix Complex

theorem permanent_fin_two {R : Type*} [CommSemiring R] (M : Matrix (Fin 2) (Fin 2) R) :
  M.permanent = M 0 0 * M 1 1 + M 0 1 * M 1 0 := by
  simp [permanent]
  have h_univ : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by
    decide
  rw [h_univ]
  have h_not_mem : (1 : Perm (Fin 2)) ∉ ({swap 0 1} : Finset (Perm (Fin 2))) := by
    decide
  rw [Finset.sum_insert h_not_mem]
  simp [Finset.sum_singleton]
  ring


theorem perm_fin_four_univ : (Finset.univ : Finset (Perm (Fin 4))) = {
  1,
  swap 2 3,
  swap 1 2,
  swap 2 3 * swap 1 2,
  swap 1 3 * swap 1 2,
  swap 1 3,
  swap 0 1,
  swap 2 3 * swap 0 1,
  swap 1 2 * swap 0 1,
  swap 2 3 * swap 1 2 * swap 0 1,
  swap 1 3 * swap 1 2 * swap 0 1,
  swap 1 3 * swap 0 1,
  swap 0 2 * swap 0 1,
  swap 2 3 * swap 0 2 * swap 0 1,
  swap 0 2,
  swap 2 3 * swap 0 2,
  swap 1 3 * swap 0 2,
  swap 1 3 * swap 0 2 * swap 0 1,
  swap 0 3 * swap 0 2 * swap 0 1,
  swap 0 3 * swap 0 1,
  swap 0 3 * swap 0 2,
  swap 0 3,
  swap 1 2 * swap 0 3 * swap 0 1,
  swap 1 2 * swap 0 3
} := by
  decide

theorem fin_four_univ : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
  decide

/--
Conjecture A002454: Let $\zeta$ be a primitive $(2n+1)$-th root of unity.
Then the permanent of the $2n \times 2n$ matrix $[m(j,k)]_{j,k=1..2n}$ is
$a(n)/(2n+1) = ((2n)!!)^2/(2n+1)$, where $m(j,k)$ is $1$ or $\frac{1+\zeta^{j-k}}{1-\zeta^{j-k}}$
according as $j = k$ or not.

Note: We use $0$-indexed matrices $j, k \in \operatorname{Fin}(2n)$ corresponding to $1$-based indices $j+1, k+1$.
The difference in exponent $j-k$ remains the same.
-/
theorem oeis_2454_conjecture_0 (n : ℕ) :
  let N : ℕ := 2 * n
  -- The order of the root of unity
  let K : ℕ := N + 1
  -- We work in the complex numbers ℂ.
  -- Assume a primitive K-th root of unity
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ K →
  (
    let M : Matrix (Fin N) (Fin N) ℂ := of fun j k : Fin N =>
      if j = k
      then 1
      else
        -- j and k are Nat, coerced to ℤ for the power exponent
        let pow : ℤ := (j : ℤ) - (k : ℤ)
        (1 + ζ ^ pow) / (1 - ζ ^ pow)
    M.permanent = (a n : ℂ) / (K : ℂ)
  ) := by
  intro N K ζ hζ
  cases n with
  | zero =>
    dsimp only [N, K]
    have h : (of fun j k : Fin 0 =>
      if j = k
      then 1
      else
        let pow : ℤ := (j : ℤ) - (k : ℤ)
        (1 + ζ ^ pow) / (1 - ζ ^ pow)).permanent = 1 := permanent_isEmpty
    rw [h]
    simp [a]
  | succ n =>
    cases n with
    | zero =>
      dsimp only [N, K]
      have h_perm : (of fun j k : Fin 2 =>
        if j = k
        then 1
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)).permanent =
        (of fun j k : Fin 2 =>
        if j = k
        then 1
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)) 0 0 * (of fun j k : Fin 2 =>
        if j = k
        then 1
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)) 1 1 +
        (of fun j k : Fin 2 =>
        if j = k
        then 1
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)) 0 1 * (of fun j k : Fin 2 =>
        if j = k
        then 1
        else
          let pow : ℤ := (j : ℤ) - (k : ℤ)
          (1 + ζ ^ pow) / (1 - ζ ^ pow)) 1 0 := by
        apply permanent_fin_two
      rw [h_perm]
      have h00 : (of fun j k : Fin 2 => if j = k then (1 : ℂ) else (1 + ζ ^ ((j : ℤ) - (k : ℤ))) / (1 - ζ ^ ((j : ℤ) - (k : ℤ)))) 0 0 = 1 := by rfl
      have h11 : (of fun j k : Fin 2 => if j = k then (1 : ℂ) else (1 + ζ ^ ((j : ℤ) - (k : ℤ))) / (1 - ζ ^ ((j : ℤ) - (k : ℤ)))) 1 1 = 1 := by rfl
      have h01 : (of fun j k : Fin 2 => if j = k then (1 : ℂ) else (1 + ζ ^ ((j : ℤ) - (k : ℤ))) / (1 - ζ ^ ((j : ℤ) - (k : ℤ)))) 0 1 = (1 + ζ ^ (-1 : ℤ)) / (1 - ζ ^ (-1 : ℤ)) := by rfl
      have h10 : (of fun j k : Fin 2 => if j = k then (1 : ℂ) else (1 + ζ ^ ((j : ℤ) - (k : ℤ))) / (1 - ζ ^ ((j : ℤ) - (k : ℤ)))) 1 0 = (1 + ζ ^ (1 : ℤ)) / (1 - ζ ^ (1 : ℤ)) := by rfl
      rw [h00, h11, h01, h10]
      have h_pow1 : ζ ^ (1 : ℤ) = ζ := by simp
      have h_pow_neg1 : ζ ^ (-1 : ℤ) = ζ⁻¹ := by simp
      rw [h_pow1, h_pow_neg1]
      
      have h_root : ζ ^ 2 + ζ + 1 = 0 := by
        have h1 : ζ ^ 3 = 1 := hζ.pow_eq_one
        have h2 : ζ ≠ 1 := hζ.ne_one (by norm_num)
        have h3 : ζ ^ 3 - 1 = (ζ - 1) * (ζ ^ 2 + ζ + 1) := by ring
        have h4 : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
          rw [← h3, h1, sub_self]
        cases mul_eq_zero.mp h4 with
        | inl h_inl =>
          have : ζ = 1 := sub_eq_zero.mp h_inl
          contradiction
        | inr h_inr =>
          exact h_inr

      have h_nz : ζ ≠ 0 := by
        have h1 : ζ ^ 3 = 1 := hζ.pow_eq_one
        intro h
        rw [h] at h1
        norm_num at h1

      have h_a1 : (a 1 : ℂ) = 4 := by
        unfold a
        norm_num

      rw [h_a1]
      
      have h_inv : (1 + ζ⁻¹) / (1 - ζ⁻¹) = (ζ + 1) / (ζ - 1) := by
        have h_num : 1 + ζ⁻¹ = (ζ + 1) / ζ := by
          field_simp
        have h_den : 1 - ζ⁻¹ = (ζ - 1) / ζ := by
          field_simp
        rw [h_num, h_den]
        have h_div : ((ζ + 1) / ζ) / ((ζ - 1) / ζ) = (ζ + 1) / (ζ - 1) := by
          field_simp
        exact h_div

      rw [h_inv]
      
      have h_sub_nz : ζ - 1 ≠ 0 := by
        intro h
        have : ζ = 1 := sub_eq_zero.mp h
        have h2 : ζ ≠ 1 := hζ.ne_one (by norm_num)
        contradiction
      have h_sub_nz2 : 1 - ζ ≠ 0 := by
        intro h
        have : 1 = ζ := sub_eq_zero.mp h
        have : ζ = 1 := this.symm
        have h2 : ζ ≠ 1 := hζ.ne_one (by norm_num)
        contradiction

      field_simp [h_sub_nz, h_sub_nz2]
      linear_combination 4 * h_root
    | succ n =>
      cases n with
      | zero =>
        intro M
        dsimp only [N, K]
        have h_root : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
          have h1 : ζ ^ 5 = 1 := hζ.pow_eq_one
          have h2 : ζ ≠ 1 := hζ.ne_one (by norm_num)
          have h3 : ζ ^ 5 - 1 = (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) := by ring
          have h4 : (ζ - 1) * (ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1) = 0 := by
            rw [← h3, h1, sub_self]
          cases mul_eq_zero.mp h4 with
          | inl h_inl =>
            have : ζ = 1 := sub_eq_zero.mp h_inl
            contradiction
          | inr h_inr =>
            exact h_inr
        have h_pow5 : ζ ^ 5 - 1 = 0 := by
          rw [hζ.pow_eq_one, sub_self]

        have h_nz1 : 1 - ζ ≠ 0 := by
          intro h
          have h2 : ζ ^ 1 = 1 := by rw [pow_one, sub_eq_zero.mp h]
          have h_dvd : 5 ∣ 1 := hζ.dvd_of_pow_eq_one 1 h2
          norm_num at h_dvd
        have h_nz2 : 1 - ζ ^ 2 ≠ 0 := by
          intro h
          have h1 : 1 = ζ ^ 2 := sub_eq_zero.mp h
          have h_dvd : 5 ∣ 2 := hζ.dvd_of_pow_eq_one 2 h1.symm
          norm_num at h_dvd
        have h_nz3 : 1 - ζ ^ 3 ≠ 0 := by
          intro h
          have h1 : 1 = ζ ^ 3 := sub_eq_zero.mp h
          have h_dvd : 5 ∣ 3 := hζ.dvd_of_pow_eq_one 3 h1.symm
          norm_num at h_dvd
        have h_nz4 : 1 - ζ ^ 4 ≠ 0 := by
          intro h
          have h1 : 1 = ζ ^ 4 := sub_eq_zero.mp h
          have h_dvd : 5 ∣ 4 := hζ.dvd_of_pow_eq_one 4 h1.symm
          norm_num at h_dvd

        have h_mul1 : (1 + ζ) / (1 - ζ) = 2/5 * ζ ^ 3 + 4/5 * ζ ^ 2 + 6/5 * ζ + 3/5 := by
          have h_mul : (1 + ζ) = (2/5 * ζ ^ 3 + 4/5 * ζ ^ 2 + 6/5 * ζ + 3/5) * (1 - ζ) := by
            linear_combination 2/5 * h_root
          field_simp [h_nz1]
          rw [h_mul]
          ring
        have h_mul2 : (1 + ζ ^ 2) / (1 - ζ ^ 2) = -4/5 * ζ ^ 3 + 2/5 * ζ ^ 2 - 2/5 * ζ - 1/5 := by
          have h_mul : (1 + ζ ^ 2) = (-4/5 * ζ ^ 3 + 2/5 * ζ ^ 2 - 2/5 * ζ - 1/5) * (1 - ζ ^ 2) := by
            linear_combination 2/5 * h_root - 4/5 * h_pow5
          field_simp [h_nz2]
          rw [h_mul]
          ring
        have h_mul3 : (1 + ζ ^ 3) / (1 - ζ ^ 3) = 4/5 * ζ ^ 3 - 2/5 * ζ ^ 2 + 2/5 * ζ + 1/5 := by
          have h_mul : (1 + ζ ^ 3) = (4/5 * ζ ^ 3 - 2/5 * ζ ^ 2 + 2/5 * ζ + 1/5) * (1 - ζ ^ 3) := by
            linear_combination 2/5 * h_root + (4/5 * ζ - 2/5) * h_pow5
          field_simp [h_nz3]
          rw [h_mul]
          ring
        have h_mul4 : (1 + ζ ^ 4) / (1 - ζ ^ 4) = -2/5 * ζ ^ 3 - 4/5 * ζ ^ 2 - 6/5 * ζ - 3/5 := by
          have h_mul : (1 + ζ ^ 4) = (-2/5 * ζ ^ 3 - 4/5 * ζ ^ 2 - 6/5 * ζ - 3/5) * (1 - ζ ^ 4) := by
            linear_combination 2/5 * h_root + (-2/5 * ζ ^ 2 - 4/5 * ζ - 6/5) * h_pow5
          field_simp [h_nz4]
          rw [h_mul]
          ring

        have h00 : M 0 0 = 1 := by rfl
        have h01 : M 0 1 = (1 + ζ ^ (-1 : ℤ)) / (1 - ζ ^ (-1 : ℤ)) := by rfl
        have h02 : M 0 2 = (1 + ζ ^ (-2 : ℤ)) / (1 - ζ ^ (-2 : ℤ)) := by rfl
        have h03 : M 0 3 = (1 + ζ ^ (-3 : ℤ)) / (1 - ζ ^ (-3 : ℤ)) := by rfl
        have h10 : M 1 0 = (1 + ζ ^ (1 : ℤ)) / (1 - ζ ^ (1 : ℤ)) := by rfl
        have h11 : M 1 1 = 1 := by rfl
        have h12 : M 1 2 = (1 + ζ ^ (-1 : ℤ)) / (1 - ζ ^ (-1 : ℤ)) := by rfl
        have h13 : M 1 3 = (1 + ζ ^ (-2 : ℤ)) / (1 - ζ ^ (-2 : ℤ)) := by rfl
        have h20 : M 2 0 = (1 + ζ ^ (2 : ℤ)) / (1 - ζ ^ (2 : ℤ)) := by rfl
        have h21 : M 2 1 = (1 + ζ ^ (1 : ℤ)) / (1 - ζ ^ (1 : ℤ)) := by rfl
        have h22 : M 2 2 = 1 := by rfl
        have h23 : M 2 3 = (1 + ζ ^ (-1 : ℤ)) / (1 - ζ ^ (-1 : ℤ)) := by rfl
        have h30 : M 3 0 = (1 + ζ ^ (3 : ℤ)) / (1 - ζ ^ (3 : ℤ)) := by rfl
        have h31 : M 3 1 = (1 + ζ ^ (2 : ℤ)) / (1 - ζ ^ (2 : ℤ)) := by rfl
        have h32 : M 3 2 = (1 + ζ ^ (1 : ℤ)) / (1 - ζ ^ (1 : ℤ)) := by rfl
        have h33 : M 3 3 = 1 := by rfl

        simp [permanent, perm_fin_four_univ]
        repeat (rw [Finset.sum_insert (by decide)])
        rw [Finset.sum_singleton]
        simp only [fin_four_univ]
        repeat (rw [Finset.prod_insert (by decide)])
        simp only [Finset.prod_singleton]
        
        simp [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.swap_apply_def]
        rw [h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]

        have h_z1 : ζ ^ (1 : ℤ) = ζ := by rw [zpow_ofNat, pow_one]
        have h_z2 : ζ ^ (2 : ℤ) = ζ ^ 2 := by rw [zpow_ofNat]
        have h_z3 : ζ ^ (3 : ℤ) = ζ ^ 3 := by rw [zpow_ofNat]

        have h_nz_zero : ζ ≠ 0 := by
          have h1 : ζ ^ 5 = 1 := hζ.pow_eq_one
          intro h_zero
          rw [h_zero] at h1
          norm_num at h1
        have h_pow5_eq : ζ ^ 5 = 1 := hζ.pow_eq_one

        have h_z_neg1 : ζ ^ (-1 : ℤ) = ζ ^ 4 := by
          have : ζ ^ (-1 : ℤ) = ζ⁻¹ := by simp
          rw [this]
          field_simp [h_nz_zero]
          exact h_pow5_eq.symm
        have h_z_neg2 : ζ ^ (-2 : ℤ) = ζ ^ 3 := by
          have : ζ ^ (-2 : ℤ) = (ζ ^ 2)⁻¹ := rfl
          rw [this]
          have h_nz2 : ζ ^ 2 ≠ 0 := pow_ne_zero 2 h_nz_zero
          field_simp [h_nz2]
          exact h_pow5_eq.symm
        have h_z_neg3 : ζ ^ (-3 : ℤ) = ζ ^ 2 := by
          have : ζ ^ (-3 : ℤ) = (ζ ^ 3)⁻¹ := rfl
          rw [this]
          have h_nz3 : ζ ^ 3 ≠ 0 := pow_ne_zero 3 h_nz_zero
          field_simp [h_nz3]
          exact h_pow5_eq.symm

        have h_a2 : (a 2 : ℂ) = 64 := by
          unfold a
          norm_num
        rw [h_a2]

        rw [h_z1, h_z2, h_z3, h_z_neg1, h_z_neg2, h_z_neg3]
        rw [h_mul1, h_mul2, h_mul3, h_mul4]
        linear_combination (656/625 * ζ ^ 8 - 688/625 * ζ ^ 7 + 2288/625 * ζ ^ 6 - 1696/625 * ζ ^ 5 + 528/125 * ζ ^ 4 + 1984/625 * ζ ^ 3 - 272/625 * ζ ^ 2 + 5552/625 * ζ - 8064/625) * h_root
      | succ n => sorry



#print axioms oeis_2454_conjecture_0
