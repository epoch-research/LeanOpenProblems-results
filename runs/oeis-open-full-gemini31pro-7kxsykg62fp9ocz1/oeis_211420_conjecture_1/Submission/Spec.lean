import FormalConjectures.Util.ProblemImports
import Submission.PolyId

open Nat

def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

def denominator_product (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ)) |>.prod

lemma D_ne_zero (n r : ℕ) : denominator_product n r ≠ 0 := by
  dsimp [denominator_product]
  apply List.prod_ne_zero
  intro h
  rw [List.mem_map] at h
  rcases h with ⟨k, _, hk⟩
  have : (8 * (n:ℤ) - (2 * (k:ℤ) + 1)) % 2 = 0 := by rw [hk, Int.zero_emod]
  have h2 : (8 * (n:ℤ) - (2 * (k:ℤ) + 1)) % 2 = 1 := by
    calc (8 * (n:ℤ) - (2 * (k:ℤ) + 1)) % 2 = (8 * (n:ℤ) - 2 * (k:ℤ) - 1) % 2 := by ring_nf
    _ = 1 := by omega
  rw [h2] at this
  exact one_ne_zero this

theorem oeis_211420_conjecture_1 : ∀ r : ℕ, ∃ K : ℤ, K > 0 ∧ ∀ n : ℕ,
    denominator_product n r ∣ (a n : ℤ) * K := by
  intro r
  let K1 : ℤ := ((8 * r).factorial : ℤ)
  let K2 : ℤ := (List.range (r + 1)).map (fun i => (denominator_product i r) ^ 2) |>.prod
  use K1 * K2
  constructor
  · have hK1 : K1 > 0 := by positivity
    have hK2 : K2 > 0 := by
      dsimp [K2]
      apply List.prod_pos
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨i, _, rfl⟩
      have := D_ne_zero i r
      positivity
    positivity
  
  intro n
  by_cases hn : n ≤ r
  · have hdvd : denominator_product n r ∣ K2 := by
      dsimp [K2]
      have H1 : (denominator_product n r) ^ 2 ∈ (List.range (r + 1)).map (fun i => (denominator_product i r) ^ 2) := by
        rw [List.mem_map]
        use n
        constructor
        · rw [List.mem_range]; omega
        · rfl
      have H2 : (denominator_product n r) ^ 2 ∣ K2 := List.dvd_prod H1
      have H3 : denominator_product n r ∣ (denominator_product n r) ^ 2 := dvd_pow_self _ (by omega)
      exact dvd_trans H3 H2
    have hK2 : K2 ∣ (a n : ℤ) * (K1 * K2) := by use (a n : ℤ) * K1; ring
    exact dvd_trans hdvd hK2
  · have hr : r ≤ 4 * n := by omega
    have h_a_dvd := a_dvd n
    have ha_eq : (a n : ℤ) * ↑((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) = ↑((8 * n).factorial * n.factorial) := by
      have h_div := Nat.div_mul_cancel h_a_dvd
      dsimp [a]
      push_cast
      exact_mod_cast h_div
    
    have hV := V_dvd n r hr
    rcases hV with ⟨V, hV_eq⟩
    have hV_Z : ↑((4 * n - r).factorial * (3 * n).factorial * (2 * n).factorial) * (V : ℤ) = ↑((8 * n - 2 * r).factorial * (8 * r).factorial * n.factorial) := by
      push_cast
      exact_mod_cast hV_eq.symm

    have h_poly := poly_id_Z n r hr
    have D_eq : denominator_product n r = D n r := rfl

    have H1 : ((a n : ℤ) * K1) * (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial) * ↑((4 * n - r).factorial)) =
              (D n r * (2 ^ r : ℤ) * V) * (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial) * ↑((4 * n - r).factorial)) := by
      calc ((a n : ℤ) * K1) * (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial) * ↑((4 * n - r).factorial))
        = ((a n : ℤ) * (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial))) * K1 * ↑((4 * n - r).factorial) := by ring
        _ = (↑((8 * n).factorial) * ↑(n.factorial)) * K1 * ↑((4 * n - r).factorial) := by
          have h_cast : ↑((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) = (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial) : ℤ) := by push_cast; rfl
          rw [← h_cast, ha_eq]
          push_cast; rfl
        _ = (↑((8 * n).factorial) * ↑((4 * n - r).factorial)) * K1 * ↑(n.factorial) := by ring
        _ = (D n r * (2 ^ r : ℤ) * ↑((4 * n).factorial) * ↑((8 * n - 2 * r).factorial)) * K1 * ↑(n.factorial) := by rw [← h_poly]
        _ = D n r * (2 ^ r : ℤ) * ↑((4 * n).factorial) * (↑((8 * n - 2 * r).factorial) * K1 * ↑(n.factorial)) := by ring
        _ = D n r * (2 ^ r : ℤ) * ↑((4 * n).factorial) * (↑((8 * n - 2 * r).factorial * (8 * r).factorial * n.factorial)) := by
          dsimp [K1]
        _ = D n r * (2 ^ r : ℤ) * ↑((4 * n).factorial) * (↑((4 * n - r).factorial * (3 * n).factorial * (2 * n).factorial) * (V : ℤ)) := by rw [← hV_Z]
        _ = (D n r * (2 ^ r : ℤ) * V) * (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial) * ↑((4 * n - r).factorial)) := by
          push_cast
          ring

    have h_cancel : (a n : ℤ) * K1 = D n r * (2 ^ r : ℤ) * V := by
      have nz : (↑((4 * n).factorial) * ↑((3 * n).factorial) * ↑((2 * n).factorial) * ↑((4 * n - r).factorial) : ℤ) ≠ 0 := by positivity
      exact mul_right_cancel₀ nz H1

    have hdvd : D n r ∣ (a n : ℤ) * K1 := by
      rw [h_cancel]
      have := dvd_mul_right (D n r) ((2 ^ r : ℤ) * V)
      rw [← mul_assoc] at this
      exact this
    
    rw [← D_eq] at hdvd
    have hK1 : (a n : ℤ) * K1 ∣ (a n : ℤ) * (K1 * K2) := by use K2; ring
    exact dvd_trans hdvd hK1

-- theorem oeis_211420_conjecture_1.disproof : ¬ (type_of% @oeis_211420_conjecture_1) := sorry

theorem oeis_211420_conjecture_1.disproof : ¬ (type_of% @oeis_211420_conjecture_1) := sorry
