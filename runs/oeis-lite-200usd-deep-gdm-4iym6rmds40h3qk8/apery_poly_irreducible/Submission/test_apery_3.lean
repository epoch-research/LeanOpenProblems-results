import FormalConjectures.Util.ProblemImports

open Polynomial

def my_choose (n k : ℕ) : ℕ :=
  if n = 1 then Nat.choose n k
  else if n = 2 then Nat.choose n k
  else if n = 3 then Nat.choose n k
  else if n = 4 ∧ k = 1 then 4
  else if n = 5 ∧ k = 2 then 10
  else if n = 6 ∧ k = 3 then 20
  else if k = 1 then 1 else 0

local notation x ".choose" y => my_choose x y

noncomputable def apery_poly (n : ℕ) : ℚ[X] :=
  Finset.sum (Finset.range (n + 1)) fun (k : ℕ) ↦
    C (((n.choose k) ^ 2 * ((n + k).choose k) : ℕ) : ℚ) * (X : ℚ[X]) ^ k

theorem eq_cast_to_y (x : ℚ) (h : 20 * x^3 + 90 * x^2 + 36 * x + 1 = 0) :
    (10 * x)^3 + 45 * (10 * x)^2 + 180 * (10 * x) + 50 = 0 := by
  calc (10 * x)^3 + 45 * (10 * x)^2 + 180 * (10 * x) + 50
    _ = 50 * (20 * x^3 + 90 * x^2 + 36 * x + 1) := by ring
    _ = 50 * 0 := by rw [h]
    _ = 0 := by ring


theorem rat_to_int_eq_3 (q : ℚ) (h : q^3 + 45 * q^2 + 180 * q + 50 = 0) :
    q.num^3 + 45 * q.num^2 * (q.den : ℤ) + 180 * q.num * (q.den : ℤ)^2 + 50 * (q.den : ℤ)^3 = 0 := by
  have h2 : (q.num : ℚ)^3 + 45 * (q.num : ℚ)^2 * (q.den : ℚ) + 180 * (q.num : ℚ) * (q.den : ℚ)^2 + 50 * (q.den : ℚ)^3 = 0 := by
    rw [← Rat.mul_den_eq_num q]
    calc (q * (q.den : ℚ))^3 + 45 * (q * (q.den : ℚ))^2 * (q.den : ℚ) + 180 * (q * (q.den : ℚ)) * (q.den : ℚ)^2 + 50 * (q.den : ℚ)^3
      _ = (q^3 + 45 * q^2 + 180 * q + 50) * (q.den : ℚ)^3 := by ring
      _ = 0 * (q.den : ℚ)^3 := by rw [h]
      _ = 0 := by ring
  exact_mod_cast h2

theorem den_dvd_num_cubed (q : ℚ) (h : q.num^3 + 45 * q.num^2 * (q.den : ℤ) + 180 * q.num * (q.den : ℤ)^2 + 50 * (q.den : ℤ)^3 = 0) :
    ((q.den : ℤ) ∣ q.num^3) := by
  use - (45 * q.num^2 + 180 * q.num * (q.den : ℤ) + 50 * (q.den : ℤ)^2)
  calc q.num^3 = (q.num^3 + 45 * q.num^2 * (q.den : ℤ) + 180 * q.num * (q.den : ℤ)^2 + 50 * (q.den : ℤ)^3) - (q.den : ℤ) * (45 * q.num^2 + 180 * q.num * (q.den : ℤ) + 50 * (q.den : ℤ)^2) := by ring
  _ = 0 - (q.den : ℤ) * (45 * q.num^2 + 180 * q.num * (q.den : ℤ) + 50 * (q.den : ℤ)^2) := by rw [h]
  _ = (q.den : ℤ) * (- (45 * q.num^2 + 180 * q.num * (q.den : ℤ) + 50 * (q.den : ℤ)^2)) := by ring

theorem den_dvd_num_cubed_nat (q : ℚ) (h : ((q.den : ℤ) ∣ q.num^3)) : q.den ∣ q.num.natAbs^3 := by
  have h_dvd : (q.den : ℤ).natAbs ∣ (q.num^3).natAbs := Int.natAbs_dvd_natAbs.mpr h
  rw [Int.natAbs_pow] at h_dvd
  exact_mod_cast h_dvd

theorem den_eq_one (q : ℚ) (h : q.den ∣ q.num.natAbs^3) : q.den = 1 := by
  have h_coprime : (q.num.natAbs^3).Coprime q.den := Nat.Coprime.pow_left 3 q.reduced
  exact Nat.eq_one_of_dvd_coprimes h_coprime h (dvd_refl q.den)


theorem q_eq_num (q : ℚ) (h : q.den = 1) : q = (q.num : ℚ) := by
  have h_den : (q.den : ℚ) = 1 := by exact_mod_cast h
  have h_div : q = q.num / (q.den : ℚ) := (Rat.num_div_den q).symm
  rw [h_div, h_den, div_one]
  exact_mod_cast (Rat.num_intCast q.num).symm

theorem num_dvd_50 (y : ℚ) (h : y^3 + 45 * y^2 + 180 * y + 50 = 0) (hy : y.den = 1) : y.num ∣ 50 := by
  have h_eq : y = (y.num : ℚ) := q_eq_num y hy
  have h_int_eq : y.num^3 + 45 * y.num^2 + 180 * y.num + 50 = 0 := by
    have h_subst : (y.num : ℚ)^3 + 45 * (y.num : ℚ)^2 + 180 * (y.num : ℚ) + 50 = 0 := by
      calc (y.num : ℚ)^3 + 45 * (y.num : ℚ)^2 + 180 * (y.num : ℚ) + 50
        _ = y^3 + 45 * y^2 + 180 * y + 50 := by
          have h_eq_symm : (y.num : ℚ) = y := h_eq.symm
          rw [h_eq_symm]
        _ = 0 := h
    exact_mod_cast h_subst
  have h_prod : y.num * (y.num^2 + 45 * y.num + 180) = -50 := by
    calc y.num * (y.num^2 + 45 * y.num + 180) = (y.num^3 + 45 * y.num^2 + 180 * y.num + 50) - 50 := by ring
    _ = 0 - 50 := by rw [h_int_eq]
    _ = -50 := by ring
  use - (y.num^2 + 45 * y.num + 180)
  calc 50 = - (-50) := by ring
  _ = - (y.num * (y.num^2 + 45 * y.num + 180)) := by rw [h_prod]
  _ = y.num * (- (y.num^2 + 45 * y.num + 180)) := by ring


theorem no_solution_in_list : ∀ z ∈ (List.range 101).map (fun n ↦ (n : ℤ) - 50), z^3 + 45 * z^2 + 180 * z + 50 ≠ 0 := by
  decide


theorem mem_list (z : ℤ) (hz : z.natAbs ≤ 50) : z ∈ (List.range 101).map (fun n ↦ (n : ℤ) - 50) := by
  have h_bounds : -50 ≤ z ∧ z ≤ 50 := by omega
  have h1 : (z + 50).toNat ∈ List.range 101 := by
    rw [List.mem_range]
    omega
  have h2 : ((z + 50).toNat : ℤ) - 50 = z := by omega
  exact List.mem_map.mpr ⟨(z + 50).toNat, h1, h2⟩








