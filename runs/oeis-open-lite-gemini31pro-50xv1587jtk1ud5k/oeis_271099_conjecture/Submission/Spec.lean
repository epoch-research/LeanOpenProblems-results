import FormalConjectures.Util.ProblemImports

open Nat Finset Real

def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (⌊three_half_pow_k_real⌋)
    (2 ^ k + floor_val).pred.pred

namespace A271099

theorem oeis_271099_conjecture :
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧
  (∀ k : ℕ, k > 2 →
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )
:= by
  sorry

end A271099

theorem A271099.oeis_271099_conjecture.disproof : ¬ (type_of% @A271099.oeis_271099_conjecture) := by
  intro h
  rcases h with ⟨_, _, _, h4⟩
  have h4_spec := h4 6 (by decide)
  rcases h4_spec with ⟨c, hc1, hc2, hc3⟩
  have h_waring_6 : waring_g 6 = 73 := by
    dsimp [waring_g]
    have h1 : (3 / 2 : ℝ) ^ (6 : ℝ) = (3 / 2 : ℝ) ^ 6 := by
      exact Real.rpow_natCast (3 / 2) 6
    rw [h1]
    have h2 : (3 / 2 : ℝ) ^ 6 = 729 / 64 := by norm_num
    rw [h2]
    have h3 : ⌊(729 / 64 : ℝ)⌋ = 11 := by
      apply Int.floor_eq_iff.mpr
      norm_num
    rw [h3]
    rfl
  rw [h_waring_6] at hc3
  
  have H : 1 ∈ Set.range (fun x : Fin 11 → ℕ => ∑ i : Fin 11, (c i) * (x i) ^ 6) := by
    rw [hc2]
    exact Set.mem_univ 1
  rcases H with ⟨x, hx⟩
  
  have h_x_bound : ∀ i : Fin 11, x i < 2 := by
    intro i
    by_contra hc
    push_neg at hc
    have h_x_pow : x i ^ 6 ≥ 64 := by
      have h2 : 2^6 ≤ x i ^ 6 := by exact Nat.pow_le_pow_left hc 6
      have h64 : 2^6 = 64 := by decide
      rw [h64] at h2
      exact h2
    
    have h_c_pos : c i ≥ 1 := by
      exact hc1 i
    
    have h_c_x_pow : c i * x i ^ 6 ≥ 64 := by
      nlinarith
    
    have h_sum : ∑ j : Fin 11, c j * x j ^ 6 ≥ 64 := by
      calc ∑ j : Fin 11, c j * x j ^ 6
        _ ≥ c i * x i ^ 6 := by apply Finset.single_le_sum (by intro j hj; apply Nat.zero_le) (Finset.mem_univ i)
        _ ≥ 64 := h_c_x_pow
        
    have h_sum_1 : ∑ j : Fin 11, c j * x j ^ 6 = 1 := hx
    linarith
  
  have h_x_pow_eq_x : ∀ i : Fin 11, x i ^ 6 = x i := by
    intro i
    have hxi := h_x_bound i
    have h01 : x i = 0 ∨ x i = 1 := by omega
    rcases h01 with h0 | h1
    · rw [h0]
      rfl
    · rw [h1]
      rfl
  
  have h_sum_simp : ∑ i : Fin 11, c i * x i = 1 := by
    have h_subst : (fun i => c i * x i ^ 6) = (fun i => c i * x i) := by
      ext i
      rw [h_x_pow_eq_x i]
    rw [← h_subst]
    exact hx
  
  sorry

