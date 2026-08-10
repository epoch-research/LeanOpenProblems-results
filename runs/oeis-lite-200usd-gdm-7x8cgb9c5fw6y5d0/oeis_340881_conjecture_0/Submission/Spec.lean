import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
Row sums of A340880.
$$a(n) = \sum_{k = 0}^{n-1} 2^{k(k+1)/2} \cdot \left( \prod_{j = k+1}^{n-1} (2^j - 1) \right)$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k ↦
    (2 ^ Nat.choose (k + 1) 2) *
    (Finset.prod (Finset.Ico (k + 1) n) fun j ↦ (2 ^ j - 1))

/--
Conjectures: 1) For prime p, the sequence taken modulo p is purely periodic with
minimum period dividing 2*(p - 1).
-/
theorem a_succ (n : ℕ) : a (n + 1) = (2 ^ n - 1) * a n + 2 ^ Nat.choose (n + 1) 2 := by
  dsimp [a]
  rw [sum_range_succ]
  have h_empty : Ico (n + 1) (n + 1) = ∅ := Ico_self (n + 1)
  rw [h_empty, prod_empty, mul_one]
  have h_sum : (∑ k ∈ range n, (2 ^ Nat.choose (k + 1) 2) * ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ j - 1)) =
               (∑ k ∈ range n, (2 ^ Nat.choose (k + 1) 2) * (∏ j ∈ Ico (k + 1) n, (2 ^ j - 1)) * (2 ^ n - 1)) := by
    apply sum_congr rfl
    intro k hk
    have hk_lt : k < n := mem_range.mp hk
    have h_le : k + 1 ≤ n := succ_le_of_lt hk_lt
    rw [prod_Ico_succ_top h_le]
    ring
  rw [h_sum]
  rw [← sum_mul]
  ring

lemma coprime_two_of_prime_odd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : Coprime 2 p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro h_dvd
  have h_le := Nat.le_of_dvd (by decide) h_dvd
  have hp_ge := hp.two_le
  have hp_cases : p = 2 := by omega
  exact hp2 hp_cases

lemma sq_sub_one_eq (A : ℕ) (hA : A ≥ 1) : A ^ 2 - 1 = (A - 1) * (A + 1) := by
  have h_ne : A ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h_ne
  have h_sub : (k + 1) - 1 = k := rfl
  have h_add : (k + 1) + 1 = k + 2 := rfl
  rw [h_sub, h_add]
  have h1 : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
  rw [h1]
  rfl

lemma a_odd (n : ℕ) (hn : n ≥ 1) : a n % 2 = 1 := by
  induction' n, hn using Nat.le_induction with n hn ih
  · rfl
  · rw [a_succ]
    have h_choose : (n + 1).choose 2 ≥ 1 := by
      have h2 : 2 = succ 1 := rfl
      rw [h2]
      rw [Nat.choose_succ_succ]
      rw [Nat.choose_one_right]
      omega
    have h_pow_choose : 2 ^ (n + 1).choose 2 = 2 ^ ((n + 1).choose 2 - 1) * 2 := by
      have h_eq : (n + 1).choose 2 = ((n + 1).choose 2 - 1) + 1 := by omega
      nth_rw 1 [h_eq]
      rw [pow_succ]
    have h_pow2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      have h_eq : n = (n - 1) + 1 := by omega
      nth_rw 1 [h_eq]
      rw [pow_succ]
    have h_pow2_ge : 2 ^ (n - 1) ≥ 1 := by
      exact Nat.one_le_pow _ _ (by decide)
    have h_sub_eq : 2 ^ (n - 1) * 2 - 1 = (2 ^ (n - 1) - 1) * 2 + 1 := by
      omega
    rw [Nat.add_mod, Nat.mul_mod, ih, h_pow2, h_sub_eq]
    rw [h_pow_choose]
    have h_mod_zero : (2 ^ ((n + 1).choose 2 - 1) * 2) % 2 = 0 := by
      omega
    have h_mod_one : ((2 ^ (n - 1) - 1) * 2 + 1) % 2 = 1 := by
      omega
    rw [h_mod_zero, h_mod_one]

lemma double_choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  induction' n with n ih
  · rfl
  · rcases n with rfl | n
    · rfl
    · have h_choose : Nat.choose (n + 2) 2 = Nat.choose (n + 1) 2 + (n + 1) := by
        have h_succ : 2 = succ 1 := rfl
        rw [h_succ, Nat.choose_succ_succ, Nat.choose_one_right]
        omega
      have h_sub : n + 1 - 1 = n := by omega
      have h_sub2 : n + 2 - 1 = n + 1 := by omega
      rw [h_choose, mul_add, ih, h_sub, h_sub2]
      ring

lemma choose_T_add_congruence (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.choose (2 * (p - 1) + k + 1) 2 = Nat.choose (k + 1) 2 + (p - 1) * (2 * k + 2 * p - 1) := by
  have hp_ge : p ≥ 3 := by
    have hp_ge2 := hp.two_le
    omega
  set U := p - 1
  have hU : p = U + 1 := by omega
  have hT : 2 * (p - 1) = 2 * U := rfl
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  rw [mul_add, double_choose_two, double_choose_two]
  rw [hT, hU]
  have h_sub1 : 2 * U + k + 1 - 1 = 2 * U + k := by omega
  have h_sub2 : k + 1 - 1 = k := by omega
  have h_sub3 : 2 * k + 2 * (U + 1) - 1 = 2 * U + 2 * k + 1 := by omega
  rw [h_sub1, h_sub2, h_sub3]
  ring

lemma zmod_pow_eq_of_modeq (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) {x y : ℕ} (h : x ≡ y [MOD p - 1]) : a ^ x = a ^ y := by
  have : Fact p.Prime := ⟨hp⟩
  rcases le_total x y with h_le | h_le
  · rw [Nat.modEq_iff_exists_eq_add h_le] at h
    obtain ⟨t, rfl⟩ := h
    rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow, mul_one]
  · have h_symm : y ≡ x [MOD p - 1] := h.symm
    rw [Nat.modEq_iff_exists_eq_add h_le] at h_symm
    obtain ⟨t, rfl⟩ := h_symm
    rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one ha, one_pow, mul_one]

theorem oeis_340881_conjecture_0 (p : ℕ) (hp : Nat.Prime p) :
  ∀ (n : ℕ), n ≥ 1 → a (n + 2 * (p - 1)) % p = a n % p := by
  intro n hn
  rcases eq_or_ne p 2 with rfl | hp2
  · -- p = 2 case
    have h_left : a (n + 2 * (2 - 1)) % 2 = 1 := by
      have h_eq : n + 2 * (2 - 1) = n + 2 := by omega
      rw [h_eq]
      apply a_odd
      omega
    have h_right : a n % 2 = 1 := a_odd n hn
    rw [h_left, h_right]
  · -- p ≠ 2 case
    have h_cop : Coprime 2 p := coprime_two_of_prime_odd p hp hp2
    have h_fermat : (2 ^ (p - 1) - 1) % p = 0 := Nat.pow_card_sub_one_sub_one_mod_card hp h_cop
    have h_dvd_fermat : p ∣ (2 ^ (p - 1) - 1) := Nat.dvd_iff_mod_eq_zero.mpr h_fermat
    set T := 2 * (p - 1)
    have hp_ge : p ≥ 3 := by
      have hp_ge2 := hp.two_le
      omega
    have hT_ge : T ≥ 4 := by omega
    have h_a_add : a (n + T) = (∑ k ∈ range T, (2 ^ Nat.choose (k + 1) 2) * ∏ j ∈ Ico (k + 1) (T + n), (2 ^ j - 1)) +
                              (∑ k ∈ range n, (2 ^ Nat.choose (T + k + 1) 2) * ∏ j ∈ Ico (T + k + 1) (T + n), (2 ^ j - 1)) := by
      dsimp [a]
      rw [add_comm n T]
      rw [sum_range_add]
    have hT_eq : T = (p - 1) * 2 := by omega
    have h_powT : 2 ^ T = (2 ^ (p - 1)) ^ 2 := by
      rw [hT_eq, pow_mul]
    have h_pow2_ge : 2 ^ (p - 1) ≥ 1 := Nat.one_le_pow _ _ (by decide)
    have h_div_sq : 2 ^ (p - 1) - 1 ∣ (2 ^ (p - 1)) ^ 2 - 1 := by
      rw [sq_sub_one_eq (2 ^ (p - 1)) h_pow2_ge]
      exact dvd_mul_right (2 ^ (p - 1) - 1) (2 ^ (p - 1) + 1)
    have h_dvd_T : p ∣ 2 ^ T - 1 := dvd_trans h_dvd_fermat (by rwa [h_powT])
    have h_powT_mod : 2 ^ T % p = 1 := by
      have h_sub_mod : (2 ^ T - 1) % p = 0 := Nat.mod_eq_zero_of_dvd h_dvd_T
      have h_ge1 : 2 ^ T ≥ 1 := Nat.one_le_pow _ _ (by decide)
      have h_eq : 2 ^ T = (2 ^ T - 1) + 1 := by omega
      nth_rw 1 [h_eq]
      rw [Nat.add_mod, h_sub_mod]
      have hp1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
      rw [zero_add, Nat.mod_mod]
      exact hp1
    have h_choose_congr (k : ℕ) : Nat.choose (T + k + 1) 2 ≡ Nat.choose (k + 1) 2 [MOD p - 1] := by
      rw [choose_T_add_congruence p k hp hp2]
      dsimp [Nat.ModEq]
      rw [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
    have h_zmod_two : (2 : ZMod p) ≠ 0 := by
      intro h_zero
      have h_zero' : ((2 : ℕ) : ZMod p) = 0 := h_zero
      rw [CharP.cast_eq_zero_iff (ZMod p) p] at h_zero'
      have hp2_le : p ≤ 2 := Nat.le_of_dvd (by decide) h_zero'
      omega
    have hT_mod : T % (p - 1) = 0 := by
      rw [hT_eq]
      exact Nat.mul_mod_right (p - 1) 2
    have h_exp (j : ℕ) : T + j ≡ j [MOD p - 1] := by
      dsimp [Nat.ModEq]
      rw [Nat.add_mod, hT_mod, zero_add, Nat.mod_mod]
    have h_pow_eq (j : ℕ) : (2 : ZMod p) ^ (T + j) = (2 : ZMod p) ^ j :=
      zmod_pow_eq_of_modeq p hp 2 h_zmod_two (h_exp j)
    have h_zmod_eq : ((∑ k ∈ range n, (2 ^ Nat.choose (T + k + 1) 2) * ∏ j ∈ Ico (T + k + 1) (T + n), (2 ^ j - 1)) : ZMod p) = (a n : ZMod p) := by
      dsimp [a]
      push_cast
      apply Finset.sum_congr rfl
      intro k hk
      have h_prod_shift : ∏ j ∈ Ico (T + k + 1) (T + n), ((2 : ZMod p) ^ j - 1) = ∏ j ∈ Ico (k + 1) n, ((2 : ZMod p) ^ (T + j) - 1) := by
        have h_assoc : T + k + 1 = k + 1 + T := by omega
        have h_comm : T + n = n + T := by omega
        rw [h_assoc, h_comm]
        rw [← prod_Ico_add (fun j ↦ (2 : ZMod p) ^ j - 1) (k + 1) n T]
      have h_prod_congr : ∏ j ∈ Ico (k + 1) n, ((2 : ZMod p) ^ (T + j) - 1) = ∏ j ∈ Ico (k + 1) n, ((2 : ZMod p) ^ j - 1) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [h_pow_eq j]
      have h_pow_choose : (2 : ZMod p) ^ Nat.choose (T + k + 1) 2 = (2 : ZMod p) ^ Nat.choose (k + 1) 2 := by
        apply zmod_pow_eq_of_modeq p hp 2 h_zmod_two (h_choose_congr k)
      have h_rhs : (∏ i ∈ Ico (k + 1) n, ((2 ^ i - 1 : ℕ) : ZMod p)) = ∏ i ∈ Ico (k + 1) n, ((2 : ZMod p) ^ i - 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        have h_le : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by decide)
        rw [Nat.cast_sub h_le]
        push_cast
        rfl
      rw [h_pow_choose, h_prod_shift, h_prod_congr, h_rhs]
    have h_sum1_dvd : p ∣ ∑ k ∈ range T, (2 ^ Nat.choose (k + 1) 2) * ∏ j ∈ Ico (k + 1) (T + n), (2 ^ j - 1) := by
      apply dvd_sum
      intro k hk
      have hk_lt : k < T := mem_range.mp hk
      apply dvd_mul_of_dvd_right
      rcases le_or_gt (k + 1) (p - 1) with h_le1 | h_gt1
      · have hj_mem : p - 1 ∈ Ico (k + 1) (T + n) := by
          rw [mem_Ico]
          constructor
          · exact h_le1
          · omega
        have hdvd : p ∣ 2 ^ (p - 1) - 1 := h_dvd_fermat
        exact dvd_trans hdvd (dvd_prod_of_mem (fun j ↦ 2 ^ j - 1) hj_mem)
      · have hj_mem : T ∈ Ico (k + 1) (T + n) := by
          rw [mem_Ico]
          constructor
          · omega
          · omega
        have hdvd : p ∣ 2 ^ T - 1 := h_dvd_T
        exact dvd_trans hdvd (dvd_prod_of_mem (fun j ↦ 2 ^ j - 1) hj_mem)
    have h_mod1 : (∑ k ∈ range T, (2 ^ Nat.choose (k + 1) 2) * ∏ j ∈ Ico (k + 1) (T + n), (2 ^ j - 1)) % p = 0 :=
      Nat.mod_eq_zero_of_dvd h_sum1_dvd
    have h_mod_add : a (n + T) % p = (∑ k ∈ range n, (2 ^ Nat.choose (T + k + 1) 2) * ∏ j ∈ Ico (T + k + 1) (T + n), (2 ^ j - 1)) % p := by
      rw [h_a_add]
      rw [Nat.add_mod, h_mod1, zero_add, Nat.mod_mod]
    have h_mod_eq : (∑ k ∈ range n, (2 ^ Nat.choose (T + k + 1) 2) * ∏ j ∈ Ico (T + k + 1) (T + n), (2 ^ j - 1)) ≡ a n [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      rw [Nat.cast_sum]
      have h_lhs : (∑ x ∈ range n, ( (2 ^ (T + x + 1).choose 2 * ∏ j ∈ Ico (T + x + 1) (T + n), (2 ^ j - 1) : ℕ) : ZMod p )) =
                   (∑ k ∈ range n, (2 : ZMod p) ^ (T + k + 1).choose 2 * ∏ j ∈ Ico (T + k + 1) (T + n), ((2 : ZMod p) ^ j - 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod]
        have h_rhs' : (∏ j ∈ Ico (T + k + 1) (T + n), ((2 ^ j - 1 : ℕ) : ZMod p)) = ∏ j ∈ Ico (T + k + 1) (T + n), ((2 : ZMod p) ^ j - 1) := by
          apply Finset.prod_congr rfl
          intro j hj
          have h_le : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by decide)
          rw [Nat.cast_sub h_le]
          push_cast
          rfl
        rw [h_rhs']
        rfl
      rw [h_lhs]
      exact h_zmod_eq
    rw [h_mod_add]
    exact h_mod_eq
