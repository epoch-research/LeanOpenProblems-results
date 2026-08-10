import FormalConjectures.Util.ProblemImports

open Rat Nat

lemma sum_range_two_mul_zmod_two (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m), (k : ZMod 2)) = (m : ZMod 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h_eq : 2 * (m + 1) = (2 * m) + 2 := by ring
    rw [h_eq, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [ih]
    have h_two : (2 : ZMod 2) = 0 := rfl
    push_cast
    rw [h_two]
    ring

lemma zmod_two_pow_odd (n : ℕ) (hn : 1 < n) (x : ZMod 2) : x ^ (n - 1) = x := by
  have h_pos : n - 1 ≠ 0 := by omega
  fin_cases x <;> simp [h_pos]

lemma sum_range_pow_zmod_two (m : ℕ) (hm : 1 < 2 * m) :
    (∑ k ∈ Finset.range (2 * m), (k : ZMod 2) ^ (2 * m - 1)) = (m : ZMod 2) := by
  have h_odd : ∀ x : ZMod 2, x ^ (2 * m - 1) = x := zmod_two_pow_odd (2 * m) hm
  simp_rw [h_odd]
  exact sum_range_two_mul_zmod_two m

lemma agoh_giuga_even_implies_m_odd (m : ℕ) (hm : 1 < 2 * m) (h_ag : (2 * m : ℤ) ∣ (∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1)) :
    Odd m := by
  have h2 : (2 : ℤ) ∣ (2 * m : ℤ) := by use m
  have h_dvd : (2 : ℤ) ∣ (∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1) := dvd_trans h2 h_ag
  have h_cast : ((∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1 : ℤ) : ZMod 2) = 0 := by
    exact CharP.intCast_eq_zero_iff (ZMod 2) 2 _ |>.mpr h_dvd
  push_cast at h_cast
  rw [sum_range_pow_zmod_two m hm] at h_cast
  have h_m_one : (m : ZMod 2) = 1 := by
    have h_eq : (m : ZMod 2) + 1 = 1 + 1 := by
      rw [h_cast]
      rfl
    exact add_right_cancel h_eq
  rwa [ZMod.natCast_eq_one_iff_odd] at h_m_one

lemma odd_2m_sub_one (m : ℕ) (hm : 0 < m) : Odd (2 * m - 1) := by
  use m - 1
  omega

lemma zmod_sum_pow_eq_zero (m : ℕ) [NeZero m] (hm : 1 < m) (h_odd : Odd m) :
    (∑ x : ZMod m, x ^ (2 * m - 1)) = 0 := by
  let S' := ∑ x : ZMod m, x ^ (2 * m - 1)
  have h_neg : S' = -S' := by
    calc S' = ∑ x : ZMod m, (-x) ^ (2 * m - 1) := by
              exact (Equiv.sum_comp (Equiv.neg (ZMod m)) (fun x => x ^ (2 * m - 1))).symm
         _ = ∑ x : ZMod m, -(x ^ (2 * m - 1)) := by
              congr 1
              ext x
              have hm_pos : 0 < m := by omega
              have h_odd_pow := odd_2m_sub_one m hm_pos
              exact Odd.neg_pow h_odd_pow x
         _ = -S' := by
              rw [← Finset.sum_neg_distrib]
  have h_add : S' + S' = 0 := by
    nth_rw 1 [h_neg]
    ring
  rwa [ZMod.add_self_eq_zero_iff_eq_zero h_odd] at h_add

lemma sum_range_two_mul_zmod (m : ℕ) (hm : 1 < m) (h_odd : Odd m) :
    (∑ k ∈ Finset.range (2 * m), (k : ZMod m)^(2 * m - 1)) = 0 := by
  rcases m with _ | m
  · contradiction
  haveI : NeZero (m + 1) := ⟨by omega⟩
  have h_add : 2 * (m + 1) = (m + 1) + (m + 1) := by ring
  nth_rw 1 [h_add]
  rw [Finset.sum_range_add]
  have h_term1 : (∑ i ∈ Finset.range (m + 1), ((i : ZMod (m + 1)) ^ (2 * (m + 1) - 1))) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    have h_coe : (fun i : Fin (m + 1) => ((i : ℕ) : ZMod (m + 1)) ^ (2 * (m + 1) - 1)) = (fun x : ZMod (m + 1) => x ^ (2 * (m + 1) - 1)) := by
      ext i
      congr 1
      exact @ZMod.natCast_zmod_val (m + 1) ⟨by omega⟩ (i : ZMod (m + 1))
    rw [h_coe]
    exact zmod_sum_pow_eq_zero (m + 1) hm h_odd
  have h_term2 : (∑ i ∈ Finset.range (m + 1), (((m + 1 + i : ℕ) : ZMod (m + 1)) ^ (2 * (m + 1) - 1))) = 0 := by
    have h_mod : ∀ i : ℕ, ((m + 1 + i : ℕ) : ZMod (m + 1)) = (i : ZMod (m + 1)) := by
      intro i
      push_cast
      simp
    simp_rw [h_mod]
    rw [← Fin.sum_univ_eq_sum_range]
    have h_coe : (fun i : Fin (m + 1) => ((i : ℕ) : ZMod (m + 1)) ^ (2 * (m + 1) - 1)) = (fun x : ZMod (m + 1) => x ^ (2 * (m + 1) - 1)) := by
      ext i
      congr 1
      exact @ZMod.natCast_zmod_val (m + 1) ⟨by omega⟩ (i : ZMod (m + 1))
    rw [h_coe]
    exact zmod_sum_pow_eq_zero (m + 1) hm h_odd
  rw [h_term1, h_term2, add_zero]

lemma agoh_giuga_even_false (m : ℕ) [NeZero m] (hm : 3 ≤ m) (h_odd : Odd m) :
    ¬ ((2 * m : ℤ) ∣ (∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1)) := by
  intro h_dvd
  have h_m_dvd : (m : ℤ) ∣ (2 * m : ℤ) := dvd_mul_left (m : ℤ) 2
  have h_dvd_m : (m : ℤ) ∣ (∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1) := dvd_trans h_m_dvd h_dvd
  have h_cast : ((∑ k ∈ Finset.range (2 * m), (k : ℤ)^(2 * m - 1) + 1 : ℤ) : ZMod m) = 0 := by
    exact CharP.intCast_eq_zero_iff (ZMod m) m _ |>.mpr h_dvd_m
  push_cast at h_cast
  have hm1 : 1 < m := by omega
  rw [sum_range_two_mul_zmod m hm1 h_odd] at h_cast
  simp only [zero_add] at h_cast
  have h_ne : (1 : ZMod m) ≠ 0 := by
    intro h_one
    rw [← Nat.cast_one] at h_one
    rw [ZMod.natCast_eq_zero_iff] at h_one
    have h_le : m ≤ 1 := Nat.le_of_dvd (by decide) h_one
    omega
  contradiction

lemma den_sum_dvd (f : ℕ → ℚ) (s : Finset ℕ) :
    (∑ x ∈ s, f x).den ∣ ∏ x ∈ s, (f x).den := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have h_div : (f x + ∑ i ∈ s, f i).den ∣ (f x).den * (∑ i ∈ s, f i).den := Rat.add_den_dvd (f x) (∑ i ∈ s, f i)
    exact dvd_trans h_div (mul_dvd_mul_left (f x).den ih)

lemma not_dvd_den_sum (f : ℕ → ℚ) (s : Finset ℕ) (p : ℕ) (hp : Nat.Prime p) (h : ∀ x ∈ s, ¬ p ∣ (f x).den) :
    ¬ p ∣ (∑ x ∈ s, f x).den := by
  intro h_dvd
  have h_sum_div : (∑ x ∈ s, f x).den ∣ ∏ x ∈ s, (f x).den := den_sum_dvd f s
  have h_p_div : p ∣ ∏ x ∈ s, (f x).den := dvd_trans h_dvd h_sum_div
  rcases (Nat.Prime.prime hp).exists_mem_finset_dvd h_p_div with ⟨x, hx, h_p_div_f⟩
  exact h x hx h_p_div_f


lemma D_sum3_eq_int (n : ℕ) (hn : 1 < n) (bernoulli_sum_identity : ∀ (n : ℕ) (hn : 1 < n),
    ((bernoulli (n - 1)).den : ℚ) * ((∑ k ∈ Finset.range n, (k : ℚ) ^ (n - 1)) + 1) =
    ((n * (bernoulli (n - 1)).num + (bernoulli (n - 1)).den : ℤ) : ℚ) +
    ((bernoulli (n - 1)).den : ℚ) * (∑ i ∈ Finset.range (n - 1), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 1))) :
    ((bernoulli (n - 1)).den : ℚ) * (∑ i ∈ Finset.range (n - 1), bernoulli i * ↑(n.choose i) * (n : ℚ) ^ (n - i - 1)) =
    (((bernoulli (n - 1)).den * ((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1) - (n * (bernoulli (n - 1)).num + (bernoulli (n - 1)).den) : ℤ) : ℚ) := by
  have h_id := bernoulli_sum_identity n hn
  have h_cast_S : ((∑ k ∈ Finset.range n, (k : ℚ) ^ (n - 1)) + 1) = (((∑ k ∈ Finset.range n, (k : ℤ) ^ (n - 1)) + 1 : ℤ) : ℚ) := by
    push_cast
    rfl
  rw [h_cast_S] at h_id
  push_cast at *
  linarith

lemma key_equiv_5 : a 5 = 1 ↔ agoh_giuga_condition 5 := by
  have h_a : a 5 = 1 := by
    unfold a
    split_ifs
    · contradiction
    have h_b4 : bernoulli 4 = -1/30 := by
      rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
      exact bernoulli'_four
    -- now we have F_5
    -- Let's simplify num and den
    have h_num : (bernoulli 4).num = -1 := by rw [h_b4]; rfl
    have h_den : (bernoulli 4).den = 30 := by rw [h_b4]; rfl
    simp [h_num, h_den]
    rfl
  have h_ag : agoh_giuga_condition 5 := by
    unfold agoh_giuga_condition
    decide
  simp [h_a, h_ag]





