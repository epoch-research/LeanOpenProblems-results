import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Nat Set

/--
A004290: Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.
-/
noncomputable def A004290 (n : ℕ) : ℕ :=
  -- The set of positive multiples of $n$ that are composed only of 0's and 1's in base 10.
  let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

  -- The sequence value is the smallest element of this set, which is the infimum.
  -- For n=0, the set is empty, and sInf on the empty set of ℕ is 0. The OEIS definition
  -- explicitly states "Least positive multiple of n", which implies n > 0.
  -- However, if S is empty, sInf S = 0. A004290(0) is an edge case, but the conjecture
  -- only concerns n < 10^k - 1, where we assume k ≥ 1, so n ≥ 1.
  sInf S

theorem first_conj (k : ℕ) (_hk : k > 0) : A004290 (10 ^ k) = 10 ^ k := by
  have hb : 1 < 10 := by norm_num
  have hm : 0 < 1 := by norm_num
  let S := { m : ℕ | 0 < m ∧ (10^k) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  have hS_eq : A004290 (10 ^ k) = sInf S := rfl
  
  have h_digits : Nat.digits 10 (10^k) = List.replicate k 0 ++ [1] := by
    have h1 := Nat.digits_append_zeroes_append_digits hb hm (k := k) (n := 0)
    simp only [Nat.digits_zero, List.length_nil, zero_add, mul_one] at h1
    have h_digits1 := Nat.digits_of_lt 10 1 (by norm_num) (by norm_num)
    rw [h_digits1] at h1
    exact h1.symm

  have h_mem_S : 10^k ∈ S := by
    refine ⟨?_, dvd_rfl, ?_⟩
    · exact Nat.pow_pos (by norm_num)
    · rw [h_digits]
      intro d hd
      rw [List.mem_append] at hd
      rcases hd with hd1 | hd2
      · have h_zero : d = 0 := List.eq_of_mem_replicate hd1
        left; exact h_zero
      · simp only [List.mem_singleton] at hd2
        right; exact hd2

  have h_le : ∀ m ∈ S, 10^k ≤ m := by
    intro m hm
    exact Nat.le_of_dvd hm.1 hm.2.1

  have h_nonempty : S.Nonempty := ⟨10^k, h_mem_S⟩
  have h_inf_le : sInf S ≤ 10^k := Nat.sInf_le h_mem_S
  have h_le_inf : 10^k ≤ sInf S := h_le (sInf S) (Nat.sInf_mem h_nonempty)
  
  rw [hS_eq]
  exact le_antisymm h_inf_le h_le_inf

theorem mod_pow_one (A j : ℕ) (h : A % 9 = 1) : (A^j) % 9 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Nat.mul_mod, h, ih]

theorem dvd_pow_ten_sub_one (n : ℕ) : 9 ∣ 10^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_pow_pos : 0 < 10^n := Nat.pow_pos (by norm_num)
    have h_pow : 10^n ≥ 1 := by omega
    have h_eq : 10^(n + 1) - 1 = 10 * (10^n - 1) + 9 := by omega
    rw [h_eq]
    exact dvd_add (dvd_mul_of_dvd_right ih 10) (by simp)

theorem dvd_geom_sum (A : ℕ) (h : A % 9 = 1) : 9 ∣ A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1 := by
  have h8 : (A^8) % 9 = 1 := mod_pow_one A 8 h
  have h7 : (A^7) % 9 = 1 := mod_pow_one A 7 h
  have h6 : (A^6) % 9 = 1 := mod_pow_one A 6 h
  have h5 : (A^5) % 9 = 1 := mod_pow_one A 5 h
  have h4 : (A^4) % 9 = 1 := mod_pow_one A 4 h
  have h3 : (A^3) % 9 = 1 := mod_pow_one A 3 h
  have h2 : (A^2) % 9 = 1 := mod_pow_one A 2 h
  
  have h_mod : (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1) % 9 = 0 := by
    rw [Nat.add_mod (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A) 1 9]
    rw [Nat.add_mod (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2) A 9]
    rw [Nat.add_mod (A^8 + A^7 + A^6 + A^5 + A^4 + A^3) (A^2) 9]
    rw [Nat.add_mod (A^8 + A^7 + A^6 + A^5 + A^4) (A^3) 9]
    rw [Nat.add_mod (A^8 + A^7 + A^6 + A^5) (A^4) 9]
    rw [Nat.add_mod (A^8 + A^7 + A^6) (A^5) 9]
    rw [Nat.add_mod (A^8 + A^7) (A^6) 9]
    rw [Nat.add_mod (A^8) (A^7) 9]
    rw [h8, h7, h6, h5, h4, h3, h2, h]
  exact Nat.dvd_of_mod_eq_zero h_mod

theorem geom_sum_identity (A : ℕ) : A^9 - 1 = (A - 1) * (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1) := by
  by_cases hA : A ≥ 1
  · have h_eq : (A - 1) * (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1) =
      A * (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1) - (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1) := by
      rw [Nat.sub_mul]
      simp
    rw [h_eq]
    have h_mul : A * (A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1) =
      A^9 + A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A := by
      simp only [mul_add, mul_one]
      rw [← Nat.pow_succ', ← Nat.pow_succ', ← Nat.pow_succ', ← Nat.pow_succ', ← Nat.pow_succ', ← Nat.pow_succ', ← Nat.pow_succ']
      have h_sq : A * A = A^2 := by ring
      rw [h_sq]
    rw [h_mul]
    omega
  · have h0 : A = 0 := by omega
    subst h0
    rfl

theorem dvd_geom_sum_mul (A : ℕ) (h : A % 9 = 1) : (A - 1) * 9 ∣ A^9 - 1 := by
  rw [geom_sum_identity A]
  have h_dvd : 9 ∣ A^8 + A^7 + A^6 + A^5 + A^4 + A^3 + A^2 + A + 1 := dvd_geom_sum A h
  rcases h_dvd with ⟨q, hq⟩
  rw [hq]
  have h_eq : (A - 1) * (9 * q) = ((A - 1) * 9) * q := by ring
  rw [h_eq]
  exact dvd_mul_right ((A - 1) * 9) q

theorem dvd_div_iff {a b c : ℕ} (hc : c ∣ b) (hc0 : c > 0) : a ∣ b / c ↔ a * c ∣ b := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    have h_eq : c * (b / c) = b := Nat.mul_div_cancel' hc
    rw [hq] at h_eq
    have h_eq2 : b = (a * c) * q := by
      calc b = c * (a * q) := h_eq.symm
        _ = (a * c) * q := by ring
    exact ⟨q, h_eq2⟩
  · intro h
    rcases h with ⟨q, hq⟩
    have h_div : b / c = a * q := by
      rw [hq]
      have h_mul : a * c * q = (a * q) * c := by ring
      rw [h_mul]
      exact Nat.mul_div_cancel _ hc0
    rw [h_div]
    exact dvd_mul_right a q

theorem second_conj_dvd (k : ℕ) : 10^k - 1 ∣ (10^(9 * k) - 1) / 9 := by
  have h_dvd_9 : 9 ∣ 10^(9 * k) - 1 := dvd_pow_ten_sub_one (9 * k)
  have h_div_iff : 10^k - 1 ∣ (10^(9 * k) - 1) / 9 ↔ (10^k - 1) * 9 ∣ 10^(9 * k) - 1 := dvd_div_iff h_dvd_9 (by norm_num)
  rw [h_div_iff]
  have h_eq : 10^(9 * k) - 1 = (10^k)^9 - 1 := by
    congr 1
    rw [← pow_mul]
    congr 1
    ring
  rw [h_eq]
  have h_mod_ten : (10^k) % 9 = 1 := mod_pow_one 10 k (by norm_num)
  exact dvd_geom_sum_mul (10^k) h_mod_ten

theorem ofDigits_ones (L : ℕ) : ofDigits 10 (List.replicate L 1) = (10^L - 1) / 9 := by
  induction L with
  | zero =>
    rfl
  | succ L' ih =>
    rw [List.replicate_succ, ofDigits_cons, ih]
    have h_dvd : 9 ∣ 10^L' - 1 := dvd_pow_ten_sub_one L'
    have h_mul_div : 9 * ((10^L' - 1) / 9) = 10^L' - 1 := Nat.mul_div_cancel' h_dvd
    have h_mul_eq : 9 * (1 + 10 * ((10^L' - 1) / 9)) = 10^(L' + 1) - 1 := by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm 9 10, mul_assoc, h_mul_div]
      have h_pow_pos : 0 < 10^L' := Nat.pow_pos (by norm_num)
      have h_pow_ge : 10^L' ≥ 1 := by omega
      omega
    
    have h_div : (9 * (1 + 10 * ((10^L' - 1) / 9))) / 9 = (10^(L' + 1) - 1) / 9 := by
      rw [h_mul_eq]
    rw [Nat.mul_div_cancel_left _ (by norm_num)] at h_div
    exact h_div

theorem digits_ones (L : ℕ) (hL : L > 0) : Nat.digits 10 ((10^L - 1) / 9) = List.replicate L 1 := by
  have hb : 1 < 10 := by norm_num
  have h_lt : ∀ l ∈ List.replicate L 1, l < 10 := by
    intro l hl
    have hl1 : l = 1 := List.eq_of_mem_replicate hl
    rw [hl1]; norm_num
  have h_ne : ∀ h : List.replicate L 1 ≠ [], (List.replicate L 1).getLast h ≠ 0 := by
    intro h
    have h_last : (List.replicate L 1).getLast h = 1 := by
      cases L with
      | zero => omega
      | succ L' => simp
    rw [h_last]
    norm_num
  
  have h_digits := digits_ofDigits 10 hb (List.replicate L 1) h_lt h_ne
  rw [ofDigits_ones L] at h_digits
  exact h_digits

theorem second_conj_mem (k : ℕ) (hk : k > 0) :
  (10 ^ (9 * k) - 1) / 9 ∈ { m : ℕ | 0 < m ∧ (10^k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
  refine ⟨?_, second_conj_dvd k, ?_⟩
  · apply Nat.div_pos
    · have h_pow_pos : 0 < 10^(9 * k) := Nat.pow_pos (by norm_num)
      have h_pow_ge : 10^(9 * k) ≥ 10 := by
        have h_ge : 9 * k ≥ 1 := by omega
        have := Nat.pow_le_pow_right (by norm_num : 10 > 0) h_ge
        exact this
      omega
    · norm_num
  · rw [digits_ones (9 * k) (by omega)]
    intro d hd
    have : d = 1 := List.eq_of_mem_replicate hd
    right; exact this

theorem ones_identity (L' : ℕ) : (10^(L' + 1) - 1) / 9 = 1 + 10 * ((10^L' - 1) / 9) := by
  have h_dvd : 9 ∣ 10^L' - 1 := dvd_pow_ten_sub_one L'
  have h_mul_div : 9 * ((10^L' - 1) / 9) = 10^L' - 1 := Nat.mul_div_cancel' h_dvd
  have h_mul_eq : 9 * (1 + 10 * ((10^L' - 1) / 9)) = 10^(L' + 1) - 1 := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm 9 10, mul_assoc, h_mul_div]
    have h_pow_pos : 0 < 10^L' := Nat.pow_pos (by norm_num)
    have h_pow_ge : 10^L' ≥ 1 := by omega
    omega
  
  have h_div : (9 * (1 + 10 * ((10^L' - 1) / 9))) / 9 = (10^(L' + 1) - 1) / 9 := by
    rw [h_mul_eq]
  rw [Nat.mul_div_cancel_left _ (by norm_num)] at h_div
  exact h_div.symm

theorem ofDigits_ge (D : List ℕ) (L : ℕ) (h_digits : ∀ d ∈ D, d = 0 ∨ d = 1) (h_sum : D.sum ≥ L) :
    ofDigits 10 D ≥ (10^L - 1) / 9 := by
  induction D generalizing L with
  | nil =>
    simp only [List.sum_nil] at h_sum
    have : L = 0 := by omega
    subst this
    simp
  | cons d D' ih =>
    by_cases hL : L = 0
    · subst hL
      simp
    · have hd_mem : d ∈ d :: D' := by simp
      have hd_val : d = 0 ∨ d = 1 := h_digits d hd_mem
      have hD'_digits : ∀ x ∈ D', x = 0 ∨ x = 1 := by
        intro x hx
        exact h_digits x (List.mem_cons_of_mem _ hx)
      
      simp only [List.sum_cons] at h_sum
      simp only [ofDigits_cons]
      
      rcases hd_val with rfl | rfl
      · simp only [zero_add] at h_sum
        have ih' := ih L hD'_digits h_sum
        have h_mul : 10 * ofDigits 10 D' ≥ 10 * ((10^L - 1) / 9) := Nat.mul_le_mul_left 10 ih'
        omega
      · have hL_eq : L = (L - 1) + 1 := by omega
        have h_sum' : D'.sum ≥ L - 1 := by omega
        have ih' := ih (L - 1) hD'_digits h_sum'
        rw [hL_eq, ones_identity]
        have h_mul : 10 * ofDigits 10 D' ≥ 10 * ((10^(L - 1) - 1) / 9) := Nat.mul_le_mul_left 10 ih'
        omega

theorem pow_ten_mod_induction (q r k : ℕ) (hk : k > 0) : (10^(q * k + r)) % (10^k - 1) = (10^r) % (10^k - 1) := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h_eq : (q + 1) * k + r = (q * k + r) + k := by ring
    rw [h_eq, pow_add, Nat.mul_mod]
    have h_mod : (10^k) % (10^k - 1) = 1 := by
      have h_pos : 10^k - 1 > 1 := by
        have : 10^k ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) hk
        omega
      have h_div : 10^k = (10^k - 1) + 1 := by omega
      nth_rw 1 [h_div]
      rw [Nat.add_comm (10^k - 1) 1]
      rw [Nat.add_mod_right]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [h_mod]
    rw [mul_one, Nat.mod_mod]
    exact ih

theorem pow_ten_mod (i k : ℕ) (hk : k > 0) : (10^i) % (10^k - 1) = (10^(i % k)) % (10^k - 1) := by
  have h_div := Nat.div_add_mod i k
  have h_eq : i = (i / k) * k + i % k := by
    rw [mul_comm] at h_div
    exact h_div.symm
  nth_rw 1 [h_eq]
  exact pow_ten_mod_induction (i / k) (i % k) k hk

theorem list_sum_zero_iff (l : List ℕ) : l.sum = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp [ih]
theorem ofDigits_zero_of_all_zero (b : ℕ) (l : List ℕ) (h : ∀ x ∈ l, x = 0) : ofDigits b l = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd : hd = 0 := h hd (by simp)
    have h_tl : ∀ x ∈ tl, x = 0 := fun x hx => h x (by simp [hx])
    simp [ofDigits_cons, h_hd, ih h_tl]


theorem ge_ones_of_digit_sum_ge (M L : ℕ) (h_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1) (h_sum : (Nat.digits 10 M).sum ≥ L) :
    M ≥ (10^L - 1) / 9 := by
  have h_eq : M = ofDigits 10 (Nat.digits 10 M) := (Nat.ofDigits_digits 10 M).symm
  rw [h_eq]
  exact ofDigits_ge (Nat.digits 10 M) L h_digits h_sum


theorem digits_sum_add_pow_mul (b k q r : ℕ) (hb : 1 < b) (hq : q > 0) (hr : r < b^k) :
    (Nat.digits b (q * b^k + r)).sum = (Nat.digits b q).sum + (Nat.digits b r).sum := by
  by_cases hr0 : r = 0
  · subst hr0
    simp only [add_zero, Nat.digits_zero, List.sum_nil, add_zero]
    have h1 := Nat.digits_append_zeroes_append_digits (b := b) (k := k) (m := q) (n := 0) hb hq
    simp only [Nat.digits_zero, List.length_nil, zero_add, List.nil_append] at h1
    have h_sum : (List.replicate k 0 ++ Nat.digits b q).sum = (Nat.digits b (b^k * q)).sum := by
      rw [h1]
    have h_comm : q * b^k = b^k * q := mul_comm q (b^k)
    rw [h_comm]
    rw [← h_sum]
    rw [List.sum_append, List.sum_replicate, nsmul_zero, zero_add]
  · have h_len : (Nat.digits b r).length ≤ k := by
      rw [Nat.digits_length_le_iff hb]
      · exact hr
    let k' := k - (Nat.digits b r).length
    have h_add : (Nat.digits b r).length + k' = k := Nat.add_sub_of_le h_len
    have h1 := Nat.digits_append_zeroes_append_digits (b := b) (k := k') (m := q) (n := r) hb hq
    rw [h_add] at h1
    have h_sum : (Nat.digits b r ++ List.replicate k' 0 ++ Nat.digits b q).sum = (Nat.digits b (r + b^k * q)).sum := by
      rw [h1]
    have h_eq : q * b^k + r = r + b^k * q := by ring
    rw [h_eq]
    rw [← h_sum]
    simp only [List.sum_append, List.sum_replicate, nsmul_zero, add_zero, add_comm]

theorem digits_ten_pow_sub_one (k : ℕ) (hk : k > 0) : Nat.digits 10 (10^k - 1) = List.replicate k 9 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      have h1 : 10^(0+1) - 1 = 9 := by norm_num
      rw [h1]
      have h2 : Nat.digits 10 9 = [9] := Nat.digits_of_lt 10 9 (by norm_num) (by norm_num)
      rw [h2]
      rfl
    · have hk' : k > 0 := by omega
      have h_eq : 10^(k + 1) - 1 = 9 + 10 * (10^k - 1) := by
        have : 10^(k + 1) = 10 * 10^k := by ring
        rw [this]
        have h_pos : 10^k ≥ 1 := Nat.one_le_pow k 10 (by norm_num)
        omega
      rw [h_eq]
      have hb : 1 < 10 := by norm_num
      have hxy : 9 ≠ 0 ∨ 10^k - 1 ≠ 0 := Or.inl (by norm_num)
      rw [Nat.digits_add 10 hb 9 (10^k - 1) (by norm_num) hxy]
      rw [ih hk']
      rfl

theorem sum_div_pow_eq (b N n : ℕ) (hb : 1 < b) (hN : (Nat.log b n).succ ≤ N) :
    ∑ i ∈ Finset.range N, n / b ^ i.succ = ∑ i ∈ Finset.range (Nat.log b n).succ, n / b ^ i.succ := by
  have h_split : Finset.range N = Finset.range (Nat.log b n).succ ∪ Finset.Ico (Nat.log b n).succ N := by
    rw [Finset.range_eq_Ico]
    rw [Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hN]
  rw [h_split]
  have h_disjoint : Disjoint (Finset.range (Nat.log b n).succ) (Finset.Ico (Nat.log b n).succ N) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy h_eq
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Ico] at hy
    omega
  rw [Finset.sum_union h_disjoint]
  have h_zero : ∑ i ∈ Finset.Ico (Nat.log b n).succ N, n / b ^ i.succ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have h_pow_gt : b ^ i.succ > n := by
      by_cases hn0 : n = 0
      · subst hn0
        have : b ^ i.succ > 0 := Nat.pow_pos (by omega)
        exact this
      · change n < b ^ i.succ
        rw [← Nat.log_lt_iff_lt_pow hb hn0]
        omega
    exact Nat.div_eq_of_lt h_pow_gt
  rw [h_zero, add_zero]

theorem Nat.add_div_ge (A B c : ℕ) : (A + B) / c ≥ A / c + B / c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · change A / c + B / c ≤ (A + B) / c
    rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hc)]
    have h1 : (A / c) * c ≤ A := Nat.div_mul_le_self A c
    have h2 : (B / c) * c ≤ B := Nat.div_mul_le_self B c
    calc (A / c + B / c) * c = (A / c) * c + (B / c) * c := by ring
      _ ≤ A + B := add_le_add h1 h2

theorem sum_div_pow_add_ge (b N A B : ℕ) :
    (∑ i ∈ Finset.range N, (A + B) / b ^ i.succ) ≥ (∑ i ∈ Finset.range N, A / b ^ i.succ) + (∑ i ∈ Finset.range N, B / b ^ i.succ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.add_div_ge A B (b ^ i.succ)

theorem ofDigits_ge_sum (b : ℕ) (hb : 1 < b) (L : List ℕ) : (ofDigits b L) ≥ L.sum := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    simp only [ofDigits_cons, List.sum_cons]
    have : b * ofDigits b tl ≥ 1 * ofDigits b tl := Nat.mul_le_mul_right (ofDigits b tl) (le_of_lt hb)
    rw [one_mul] at this
    omega

theorem digit_sum_le_self (b x : ℕ) (hb : 1 < b) : (Nat.digits b x).sum ≤ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h_eq := (Nat.ofDigits_digits b x).symm
    nth_rw 2 [h_eq]
    exact ofDigits_ge_sum b hb (Nat.digits b x)

theorem digit_sum_eq_sub (b N x : ℕ) (hb : 1 < b) (hN : (Nat.log b x).succ ≤ N) :
    (Nat.digits b x).sum = x - (b - 1) * ∑ i ∈ Finset.range N, x / b ^ i.succ := by
  have h_sum := sum_div_pow_eq b N x hb hN
  have h_legendre := sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := b) x
  rw [← h_sum] at h_legendre
  have h_le : (Nat.digits b x).sum ≤ x := digit_sum_le_self b x hb
  omega

theorem digit_sum_add_le (b A B : ℕ) (hb : 1 < b) :
    (Nat.digits b (A + B)).sum ≤ (Nat.digits b A).sum + (Nat.digits b B).sum := by
  by_cases hA : A = 0
  · subst hA; simp
  by_cases hB : B = 0
  · subst hB; simp
  have hAB : A + B ≠ 0 := by omega
  let N := (Nat.log b A).succ + (Nat.log b B).succ + (Nat.log b (A+B)).succ
  have hN_A : (Nat.log b A).succ ≤ N := by omega
  have hN_B : (Nat.log b B).succ ≤ N := by omega
  have hN_AB : (Nat.log b (A+B)).succ ≤ N := by omega
  
  have hA_sub := digit_sum_eq_sub b N A hb hN_A
  have hB_sub := digit_sum_eq_sub b N B hb hN_B
  have hAB_sub := digit_sum_eq_sub b N (A + B) hb hN_AB
  
  rw [hA_sub, hB_sub, hAB_sub]
  have h_ge := sum_div_pow_add_ge b N A B
  have hA_le : (b - 1) * ∑ i ∈ Finset.range N, A / b ^ i.succ ≤ A := by
    rw [sum_div_pow_eq b N A hb hN_A]
    rw [sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := b) A]
    exact Nat.sub_le A (Nat.digits b A).sum
  have hB_le : (b - 1) * ∑ i ∈ Finset.range N, B / b ^ i.succ ≤ B := by
    rw [sum_div_pow_eq b N B hb hN_B]
    rw [sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := b) B]
    exact Nat.sub_le B (Nat.digits b B).sum
  have hAB_le : (b - 1) * ∑ i ∈ Finset.range N, (A + B) / b ^ i.succ ≤ A + B := by
    rw [sum_div_pow_eq b N (A + B) hb hN_AB]
    rw [sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := b) (A + B)]
    exact Nat.sub_le (A + B) (Nat.digits b (A + B)).sum
  
  have h_mul_ge : (b - 1) * ∑ i ∈ Finset.range N, (A + B) / b ^ i.succ ≥ (b - 1) * ∑ i ∈ Finset.range N, A / b ^ i.succ + (b - 1) * ∑ i ∈ Finset.range N, B / b ^ i.succ := by
    calc (b - 1) * ∑ i ∈ Finset.range N, (A + B) / b ^ i.succ
      _ ≥ (b - 1) * ((∑ i ∈ Finset.range N, A / b ^ i.succ) + ∑ i ∈ Finset.range N, B / b ^ i.succ) := Nat.mul_le_mul_left (b - 1) h_ge
      _ = (b - 1) * ∑ i ∈ Finset.range N, A / b ^ i.succ + (b - 1) * ∑ i ∈ Finset.range N, B / b ^ i.succ := by ring
  
  omega


theorem digit_sum_ge_nine_mul_k (k : ℕ) (hk : k > 0) (m : ℕ) (hm : m > 0) (hdvd : 10^k - 1 ∣ m) :
    (Nat.digits 10 m).sum ≥ 9 * k := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h_lt : m < 10^k
    · have h_ge : m ≥ 10^k - 1 := Nat.le_of_dvd hm hdvd
      have h_eq : m = 10^k - 1 := by omega
      subst h_eq
      rw [digits_ten_pow_sub_one k hk]
      simp only [List.sum_replicate, nsmul_eq_mul]
      norm_cast
      omega
    · let q := m / 10^k
      let r := m % 10^k
      have h_div_add_mod : m = q * 10^k + r := by
        rw [mul_comm q]
        exact (Nat.div_add_mod m (10^k)).symm
      have hr : r < 10^k := Nat.mod_lt m (Nat.pow_pos (by norm_num))
      have hq : q > 0 := by
        have h_ge : m ≥ 10^k := by omega
        exact Nat.div_pos h_ge (by norm_num)
      have h_digits_sum : (Nat.digits 10 m).sum = (Nat.digits 10 q).sum + (Nat.digits 10 r).sum := by
        rw [h_div_add_mod]
        exact digits_sum_add_pow_mul 10 k q r (by norm_num) hq hr
      
      have h_m_eq : m = q * (10^k - 1) + (q + r) := by
        have h_pow : 10^k ≥ 1 := Nat.one_le_pow k 10 (by norm_num)
        have h_mul_sub : q * (10^k - 1) = q * 10^k - q := by
          have h1 := Nat.mul_sub_left_distrib q (10^k) 1
          rw [mul_one] at h1
          exact h1
        rw [h_mul_sub]
        have h_le : q ≤ q * 10^k := by
          calc q = q * 1 := by ring
            _ ≤ q * 10^k := Nat.mul_le_mul_left q h_pow
        omega
      
      have hdvd_qr : 10^k - 1 ∣ q + r := by
        have h_mod : (q * (10^k - 1) + (q + r)) % (10^k - 1) = 0 := by
          rw [← h_m_eq]
          exact Nat.mod_eq_zero_of_dvd hdvd
        rw [add_comm, mul_comm q, Nat.add_mul_mod_self_left] at h_mod
        exact Nat.dvd_of_mod_eq_zero h_mod
      
      have h_lt_m : q + r < m := by
        have h_pow : 10^k ≥ 2 := by
          have : 10^k ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) hk
          omega
        calc q + r < q * 10^k + r := by
              have : q < q * 10^k := by
                calc q < q * 2 := by omega
                  _ ≤ q * 10^k := Nat.mul_le_mul_left q h_pow
              omega
            _ = m := h_div_add_mod.symm
      
      have h_pos_qr : q + r > 0 := by omega
      have h_qr_ge : (Nat.digits 10 (q + r)).sum ≥ 9 * k := ih (q + r) h_lt_m h_pos_qr hdvd_qr
      
      have h_subadd : (Nat.digits 10 (q + r)).sum ≤ (Nat.digits 10 q).sum + (Nat.digits 10 r).sum := digit_sum_add_le 10 q r (by norm_num)
      
      omega






theorem second_conj_lower_bound (k : ℕ) (hk : k > 0) (m : ℕ)
    (hm : m ∈ { m : ℕ | 0 < m ∧ (10^k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }) :
    m ≥ (10 ^ (9 * k) - 1) / 9 := by
  have h_digits : ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := hm.2.2
  have h_sum_ge : (Nat.digits 10 m).sum ≥ 9 * k := digit_sum_ge_nine_mul_k k hk m hm.1 hm.2.1
  exact ge_ones_of_digit_sum_ge m (9 * k) h_digits h_sum_ge

theorem second_conj (k : ℕ) (hk : k > 0) : A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 := by
  let S := { m : ℕ | 0 < m ∧ (10^k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
  have hS_eq : A004290 (10 ^ k - 1) = sInf S := rfl
  
  have h_mem_S : (10 ^ (9 * k) - 1) / 9 ∈ S := second_conj_mem k hk
  have h_inf_le : sInf S ≤ (10 ^ (9 * k) - 1) / 9 := Nat.sInf_le h_mem_S
  have h_le_inf : (10 ^ (9 * k) - 1) / 9 ≤ sInf S := by
    apply le_csInf
    · exact ⟨(10 ^ (9 * k) - 1) / 9, h_mem_S⟩
    · intro m hm
      exact second_conj_lower_bound k hk m hm
  
  rw [hS_eq]
  exact le_antisymm h_inf_le h_le_inf


theorem f_diff_eq (i j : ℕ) (h : i ≤ j) :
    (10^j - 1) / 9 - (10^i - 1) / 9 = 10^i * ((10^(j - i) - 1) / 9) := by
  have h1 : 9 ∣ 10^j - 1 := dvd_pow_ten_sub_one j
  have h2 : 9 ∣ 10^i - 1 := dvd_pow_ten_sub_one i
  have h3 : 9 ∣ 10^(j - i) - 1 := dvd_pow_ten_sub_one (j - i)
  have h4 : 10^j = 10^i * 10^(j - i) := by
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]
  have h_rhs : 9 * (10^i * ((10^(j - i) - 1) / 9)) = 10^i * (10^(j - i) - 1) := by
    calc 9 * (10^i * ((10^(j - i) - 1) / 9)) = 10^i * (9 * ((10^(j - i) - 1) / 9)) := by ring
      _ = 10^i * (10^(j - i) - 1) := by rw [Nat.mul_div_cancel' h3]
  have h_mul_sub : 10^i * (10^(j-i) - 1) = 10^i * 10^(j-i) - 10^i := by
    have h_dist := Nat.mul_sub_left_distrib (10^i) (10^(j-i)) 1
    rw [mul_one] at h_dist
    exact h_dist
  have h_mul : 9 * ((10^j - 1) / 9 - (10^i - 1) / 9) = 9 * (10^i * ((10^(j - i) - 1) / 9)) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_div_cancel' h1, Nat.mul_div_cancel' h2]
    rw [h_rhs, h_mul_sub]
    rw [h4]
    have h_pow1 : 10^(j - i) ≥ 1 := Nat.one_le_pow (j - i) 10 (by norm_num)
    have h_pow2 : 10^i ≥ 1 := Nat.one_le_pow i 10 (by norm_num)
    omega
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 9 > 0) h_mul

theorem digits_ones_shifted (i L : ℕ) (hL : L > 0) :
    ∀ d ∈ Nat.digits 10 (10^i * ((10^L - 1) / 9)), d = 0 ∨ d = 1 := by
  have hb : 1 < 10 := by norm_num
  have h_pos : (10^L - 1) / 9 > 0 := by
    apply Nat.div_pos
    · have : 10^L ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) hL
      omega
    · norm_num
  have h1 := Nat.digits_append_zeroes_append_digits hb h_pos (k := i) (n := 0)
  simp only [Nat.digits_zero, List.length_nil, zero_add, List.nil_append] at h1
  rw [← h1]
  rw [digits_ones L hL]
  intro d hd
  rw [List.mem_append] at hd
  rcases hd with hd1 | hd2
  · have : d = 0 := List.eq_of_mem_replicate hd1
    left; exact this
  · have : d = 1 := List.eq_of_mem_replicate hd2
    right; exact this


theorem A004290_lt_geom_sum (n : ℕ) (hn : n > 0) :
    A004290 n < (10^(n + 1) - 1) / 9 := by
  let s := Finset.Icc 1 (n + 1)
  let t := Finset.range n
  let g (x : ℕ) : ℕ := ((10^x - 1) / 9) % n
  have hs_card : s.card = n + 1 := by
    rw [Nat.card_Icc]
    omega
  have ht_card : t.card = n := Finset.card_range n
  have h_lt : t.card < s.card := by omega
  have h_maps : ∀ x ∈ s, g x ∈ t := by
    intro x _
    rw [Finset.mem_range]
    exact Nat.mod_lt _ hn
  obtain ⟨x, hx, y, hy, hxy, h_eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_lt h_maps
  rw [Finset.mem_Icc] at hx hy
  have h_cases : x < y ∨ y < x := by omega
  rcases h_cases with h_lt' | h_lt'
  · have h_le : x ≤ y := by omega
    have h_div : n ∣ (10^y - 1) / 9 - (10^x - 1) / 9 := by
      let A := (10^y - 1) / 9
      let B := (10^x - 1) / 9
      have h_mod : A % n = B % n := h_eq.symm
      have h_ge : A ≥ B := by
        apply Nat.div_le_div_right
        have : 10^x ≤ 10^y := Nat.pow_le_pow_right (by norm_num) h_le
        omega
      have h_eqA := Nat.div_add_mod A n
      have h_eqB := Nat.div_add_mod B n
      have h_sub : A - B = n * (A / n - B / n) := by
        have h_le_div : B / n ≤ A / n := Nat.div_le_div_right h_ge
        have h_mul_sub : n * (A / n) - n * (B / n) = n * (A / n - B / n) := (Nat.mul_sub_left_distrib n (A / n) (B / n)).symm
        omega
      rw [h_sub]
      exact dvd_mul_right n (A / n - B / n)
    
    have h_eq_diff := f_diff_eq x y h_le
    rw [h_eq_diff] at h_div
    let M := 10^x * ((10^(y - x) - 1) / 9)
    have h_M_eq : M = (10^y - 1) / 9 - (10^x - 1) / 9 := h_eq_diff.symm
    
    have h_M_pos : M > 0 := by
      have h_pow_pos : 10^x > 0 := Nat.pow_pos (by norm_num)
      have h_div_pos : (10^(y - x) - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have h_yx : y - x > 0 := by omega
          have : 10^(y - x) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_yx
          omega
        · norm_num
      exact Nat.mul_pos h_pow_pos h_div_pos
    
    have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
      have h_yx : y - x > 0 := by omega
      exact digits_ones_shifted x (y - x) h_yx
    
    let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
    have h_M_mem : M ∈ S := ⟨h_M_pos, h_div, h_M_digits⟩
    
    have h_inf_le : A004290 n ≤ M := by
      unfold A004290
      exact Nat.sInf_le h_M_mem
    
    have h_M_lt : M < (10^(n + 1) - 1) / 9 := by
      rw [h_M_eq]
      have h_y_le : y ≤ n + 1 := hy.2
      have h_x_pos : x ≥ 1 := hx.1
      have h_x_val : (10^x - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have : 10^x ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_x_pos
          omega
        · norm_num
      have h_le_y : (10^y - 1) / 9 ≤ (10^(n + 1) - 1) / 9 := by
        apply Nat.div_le_div_right
        have : 10^y ≤ 10^(n + 1) := Nat.pow_le_pow_right (by norm_num) h_y_le
        omega
      omega
    
    exact lt_of_le_of_lt h_inf_le h_M_lt
  · have h_le : y ≤ x := by omega
    have h_div : n ∣ (10^x - 1) / 9 - (10^y - 1) / 9 := by
      let A := (10^x - 1) / 9
      let B := (10^y - 1) / 9
      have h_mod : A % n = B % n := h_eq
      have h_ge : A ≥ B := by
        apply Nat.div_le_div_right
        have : 10^y ≤ 10^x := Nat.pow_le_pow_right (by norm_num) h_le
        omega
      have h_eqA := Nat.div_add_mod A n
      have h_eqB := Nat.div_add_mod B n
      have h_sub : A - B = n * (A / n - B / n) := by
        have h_le_div : B / n ≤ A / n := Nat.div_le_div_right h_ge
        have h_mul_sub : n * (A / n) - n * (B / n) = n * (A / n - B / n) := (Nat.mul_sub_left_distrib n (A / n) (B / n)).symm
        omega
      rw [h_sub]
      exact dvd_mul_right n (A / n - B / n)
    
    have h_eq_diff := f_diff_eq y x h_le
    rw [h_eq_diff] at h_div
    let M := 10^y * ((10^(x - y) - 1) / 9)
    have h_M_eq : M = (10^x - 1) / 9 - (10^y - 1) / 9 := h_eq_diff.symm
    
    have h_M_pos : M > 0 := by
      have h_pow_pos : 10^y > 0 := Nat.pow_pos (by norm_num)
      have h_div_pos : (10^(x - y) - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have h_xy : x - y > 0 := by omega
          have : 10^(x - y) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_xy
          omega
        · norm_num
      exact Nat.mul_pos h_pow_pos h_div_pos
    
    have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
      have h_xy : x - y > 0 := by omega
      exact digits_ones_shifted y (x - y) h_xy
    
    let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
    have h_M_mem : M ∈ S := ⟨h_M_pos, h_div, h_M_digits⟩
    
    have h_inf_le : A004290 n ≤ M := by
      unfold A004290
      exact Nat.sInf_le h_M_mem
    
    have h_M_lt : M < (10^(n + 1) - 1) / 9 := by
      rw [h_M_eq]
      have h_x_le : x ≤ n + 1 := hx.2
      have h_y_pos : y ≥ 1 := hy.1
      have h_y_val : (10^y - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have : 10^y ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_y_pos
          omega
        · norm_num
      have h_le_x : (10^x - 1) / 9 ≤ (10^(n + 1) - 1) / 9 := by
        apply Nat.div_le_div_right
        have : 10^x ≤ 10^(n + 1) := Nat.pow_le_pow_right (by norm_num) h_x_le
        omega
      omega
    
    exact lt_of_le_of_lt h_inf_le h_M_lt


theorem A004290_lt_geom_sum_of_lt (n L : ℕ) (hn : n > 0) (hL : n < L) :
    A004290 n < (10^L - 1) / 9 := by
  let s := Finset.Icc 1 L
  let t := Finset.range n
  let g (x : ℕ) : ℕ := ((10^x - 1) / 9) % n
  have hs_card : s.card = L := by
    rw [Nat.card_Icc]
    omega
  have ht_card : t.card = n := Finset.card_range n
  have h_lt : t.card < s.card := by omega
  have h_maps : ∀ x ∈ s, g x ∈ t := by
    intro x _
    rw [Finset.mem_range]
    exact Nat.mod_lt _ hn
  obtain ⟨x, hx, y, hy, hxy, h_eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_lt h_maps
  rw [Finset.mem_Icc] at hx hy
  have h_cases : x < y ∨ y < x := by omega
  rcases h_cases with h_lt' | h_lt'
  · have h_le : x ≤ y := by omega
    have h_div : n ∣ (10^y - 1) / 9 - (10^x - 1) / 9 := by
      let A := (10^y - 1) / 9
      let B := (10^x - 1) / 9
      have h_mod : A % n = B % n := h_eq.symm
      have h_ge : A ≥ B := by
        apply Nat.div_le_div_right
        have : 10^x ≤ 10^y := Nat.pow_le_pow_right (by norm_num) h_le
        omega
      have h_eqA := Nat.div_add_mod A n
      have h_eqB := Nat.div_add_mod B n
      have h_sub : A - B = n * (A / n - B / n) := by
        have h_le_div : B / n ≤ A / n := Nat.div_le_div_right h_ge
        have h_mul_sub : n * (A / n) - n * (B / n) = n * (A / n - B / n) := (Nat.mul_sub_left_distrib n (A / n) (B / n)).symm
        omega
      rw [h_sub]
      exact dvd_mul_right n (A / n - B / n)
    
    have h_eq_diff := f_diff_eq x y h_le
    rw [h_eq_diff] at h_div
    let M := 10^x * ((10^(y - x) - 1) / 9)
    have h_M_eq : M = (10^y - 1) / 9 - (10^x - 1) / 9 := h_eq_diff.symm
    
    have h_M_pos : M > 0 := by
      have h_pow_pos : 10^x > 0 := Nat.pow_pos (by norm_num)
      have h_div_pos : (10^(y - x) - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have h_yx : y - x > 0 := by omega
          have : 10^(y - x) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_yx
          omega
        · norm_num
      exact Nat.mul_pos h_pow_pos h_div_pos
    
    have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
      have h_yx : y - x > 0 := by omega
      exact digits_ones_shifted x (y - x) h_yx
    
    let S := { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }
    have h_M_mem : M ∈ S := ⟨h_M_pos, h_div, h_M_digits⟩
    
    have h_inf_le : A004290 n ≤ M := by
      unfold A004290
      exact Nat.sInf_le h_M_mem
    
    have h_M_lt : M < (10^L - 1) / 9 := by
      rw [h_M_eq]
      have h_y_le : y ≤ L := hy.2
      have h_x_pos : x ≥ 1 := hx.1
      have h_x_val : (10^x - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have : 10^x ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_x_pos
          omega
        · norm_num
      have h_le_y : (10^y - 1) / 9 ≤ (10^L - 1) / 9 := by
        apply Nat.div_le_div_right
        have : 10^y ≤ 10^L := Nat.pow_le_pow_right (by norm_num) h_y_le
        omega
      omega
    
    exact lt_of_le_of_lt h_inf_le h_M_lt
  · have h_le : y ≤ x := by omega
    have h_div : n ∣ (10^x - 1) / 9 - (10^y - 1) / 9 := by
      let A := (10^x - 1) / 9
      let B := (10^y - 1) / 9
      have h_mod : A % n = B % n := h_eq
      have h_ge : A ≥ B := by
        apply Nat.div_le_div_right
        have : 10^y ≤ 10^x := Nat.pow_le_pow_right (by norm_num) h_le
        omega
      have h_eqA := Nat.div_add_mod A n
      have h_eqB := Nat.div_add_mod B n
      have h_sub : A - B = n * (A / n - B / n) := by
        have h_le_div : B / n ≤ A / n := Nat.div_le_div_right h_ge
        have h_mul_sub : n * (A / n) - n * (B / n) = n * (A / n - B / n) := (Nat.mul_sub_left_distrib n (A / n) (B / n)).symm
        omega
      rw [h_sub]
      exact dvd_mul_right n (A / n - B / n)
    
    have h_eq_diff := f_diff_eq y x h_le
    rw [h_eq_diff] at h_div
    let M := 10^y * ((10^(x - y) - 1) / 9)
    have h_M_eq : M = (10^x - 1) / 9 - (10^y - 1) / 9 := h_eq_diff.symm
    
    have h_M_pos : M > 0 := by
      have h_pow_pos : 10^y > 0 := Nat.pow_pos (by norm_num)
      have h_div_pos : (10^(x - y) - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have h_xy : x - y > 0 := by omega
          have : 10^(x - y) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_xy
          omega
        · norm_num
      exact Nat.mul_pos h_pow_pos h_div_pos
    
    have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
      have h_xy : x - y > 0 := by omega
      exact digits_ones_shifted y (x - y) h_xy
    
    have h_M_mem : M ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := ⟨h_M_pos, h_div, h_M_digits⟩
    
    have h_inf_le : A004290 n ≤ M := by
      unfold A004290
      exact Nat.sInf_le h_M_mem
    
    have h_M_lt : M < (10^L - 1) / 9 := by
      rw [h_M_eq]
      have h_x_le : x ≤ L := hx.2
      have h_y_pos : y ≥ 1 := hy.1
      have h_y_val : (10^y - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have : 10^y ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_y_pos
          omega
        · norm_num
      have h_le_x : (10^x - 1) / 9 ≤ (10^L - 1) / 9 := by
        apply Nat.div_le_div_right
        have : 10^x ≤ 10^L := Nat.pow_le_pow_right (by norm_num) h_x_le
        omega
      omega
    
    exact lt_of_le_of_lt h_inf_le h_M_lt

lemma S_nonempty (n : ℕ) (hn : n > 0) :
    ∃ M : ℕ, 0 < M ∧ n ∣ M ∧ ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
  let s := Finset.Icc 1 (n + 1)
  let t := Finset.range n
  let g (x : ℕ) : ℕ := ((10^x - 1) / 9) % n
  have hs_card : s.card = n + 1 := by
    rw [Nat.card_Icc]
    omega
  have ht_card : t.card = n := Finset.card_range n
  have h_lt : t.card < s.card := by omega
  have h_maps : ∀ x ∈ s, g x ∈ t := by
    intro x _
    rw [Finset.mem_range]
    exact Nat.mod_lt _ hn
  obtain ⟨x, hx, y, hy, hxy, h_eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_lt h_maps
  rw [Finset.mem_Icc] at hx hy
  have h_cases : x < y ∨ y < x := by omega
  rcases h_cases with h_lt' | h_lt'
  · have h_le : x ≤ y := by omega
    have h_div : n ∣ (10^y - 1) / 9 - (10^x - 1) / 9 := by
      let A := (10^y - 1) / 9
      let B := (10^x - 1) / 9
      have h_mod : A % n = B % n := h_eq.symm
      have h_ge : A ≥ B := by
        apply Nat.div_le_div_right
        have : 10^x ≤ 10^y := Nat.pow_le_pow_right (by norm_num) h_le
        omega
      have h_eqA := Nat.div_add_mod A n
      have h_eqB := Nat.div_add_mod B n
      have h_sub : A - B = n * (A / n - B / n) := by
        have h_le_div : B / n ≤ A / n := Nat.div_le_div_right h_ge
        have h_mul_sub : n * (A / n) - n * (B / n) = n * (A / n - B / n) := (Nat.mul_sub_left_distrib n (A / n) (B / n)).symm
        omega
      rw [h_sub]
      exact dvd_mul_right n (A / n - B / n)
    have h_eq_diff := f_diff_eq x y h_le
    rw [h_eq_diff] at h_div
    let M := 10^x * ((10^(y - x) - 1) / 9)
    have h_M_pos : M > 0 := by
      have h_pow_pos : 10^x > 0 := Nat.pow_pos (by norm_num)
      have h_div_pos : (10^(y - x) - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have h_yx : y - x > 0 := by omega
          have : 10^(y - x) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_yx
          omega
        · norm_num
      exact Nat.mul_pos h_pow_pos h_div_pos
    have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
      have h_yx : y - x > 0 := by omega
      exact digits_ones_shifted x (y - x) h_yx
    exact ⟨M, h_M_pos, h_div, h_M_digits⟩
  · have h_le : y ≤ x := by omega
    have h_div : n ∣ (10^x - 1) / 9 - (10^y - 1) / 9 := by
      let A := (10^x - 1) / 9
      let B := (10^y - 1) / 9
      have h_mod : A % n = B % n := h_eq
      have h_ge : A ≥ B := by
        apply Nat.div_le_div_right
        have : 10^y ≤ 10^x := Nat.pow_le_pow_right (by norm_num) h_le
        omega
      have h_eqA := Nat.div_add_mod A n
      have h_eqB := Nat.div_add_mod B n
      have h_sub : A - B = n * (A / n - B / n) := by
        have h_le_div : B / n ≤ A / n := Nat.div_le_div_right h_ge
        have h_mul_sub : n * (A / n) - n * (B / n) = n * (A / n - B / n) := (Nat.mul_sub_left_distrib n (A / n) (B / n)).symm
        omega
      rw [h_sub]
      exact dvd_mul_right n (A / n - B / n)
    have h_eq_diff := f_diff_eq y x h_le
    rw [h_eq_diff] at h_div
    let M := 10^y * ((10^(x - y) - 1) / 9)
    have h_M_pos : M > 0 := by
      have h_pow_pos : 10^y > 0 := Nat.pow_pos (by norm_num)
      have h_div_pos : (10^(x - y) - 1) / 9 > 0 := by
        apply Nat.div_pos
        · have h_xy : x - y > 0 := by omega
          have : 10^(x - y) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) h_xy
          omega
        · norm_num
      exact Nat.mul_pos h_pow_pos h_div_pos
    have h_M_digits : ∀ d ∈ Nat.digits 10 M, d = 0 ∨ d = 1 := by
      have h_xy : x - y > 0 := by omega
      exact digits_ones_shifted y (x - y) h_xy
    exact ⟨M, h_M_pos, h_div, h_M_digits⟩

lemma A004290_pos (n : ℕ) (hn : n > 0) : A004290 n > 0 := by
  have h_mem : A004290 n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
    unfold A004290
    apply Nat.sInf_mem
    rcases S_nonempty n hn with ⟨M, hM⟩
    exact ⟨M, hM⟩
  exact h_mem.1

lemma A004290_dvd (n : ℕ) (hn : n > 0) : n ∣ A004290 n := by
  have h_mem : A004290 n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
    unfold A004290
    apply Nat.sInf_mem
    rcases S_nonempty n hn with ⟨M, hM⟩
    exact ⟨M, hM⟩
  exact h_mem.2.1

lemma A004290_digits (n : ℕ) (hn : n > 0) : ∀ d ∈ Nat.digits 10 (A004290 n), d = 0 ∨ d = 1 := by
  have h_mem : A004290 n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
    unfold A004290
    apply Nat.sInf_mem
    rcases S_nonempty n hn with ⟨M, hM⟩
    exact ⟨M, hM⟩
  exact h_mem.2.2

lemma digits_ten_pow_mul (k X : ℕ) (hX : X > 0) :
    Nat.digits 10 (10^k * X) = List.replicate k 0 ++ Nat.digits 10 X := by
  have hb : 1 < 10 := by norm_num
  have h1 := Nat.digits_append_zeroes_append_digits hb hX (k := k) (n := 0)
  simp only [Nat.digits_zero, List.length_nil, zero_add, List.nil_append] at h1
  exact h1.symm

lemma A004290_le_ten_pow_mul (n k : ℕ) (d : ℕ) (hd : d ∣ 10^k) (hu : d ∣ n) (hn : n > 0) :
    A004290 n ≤ 10^k * A004290 (n / d) := by
  have hd_pos : d > 0 := by
    have h_pow_pos : 10^k > 0 := Nat.pow_pos (by norm_num)
    exact Nat.pos_of_dvd_of_pos hd h_pow_pos
  have hu_pos : n / d > 0 := by
    apply Nat.div_pos (Nat.le_of_dvd hn hu) hd_pos
  let u := n / d
  have h_u_dvd : u ∣ A004290 u := A004290_dvd u hu_pos
  have h_u_digits : ∀ d' ∈ Nat.digits 10 (A004290 u), d' = 0 ∨ d' = 1 := A004290_digits u hu_pos
  have h_u_val_pos : A004290 u > 0 := A004290_pos u hu_pos

  let M := 10^k * A004290 u
  have h_M_pos : M > 0 := by
    have h_pow_pos : 10^k > 0 := Nat.pow_pos (by norm_num)
    exact Nat.mul_pos h_pow_pos h_u_val_pos

  have h_M_dvd : n ∣ M := by
    rcases hd with ⟨q, hq⟩
    have h_eq : n = u * d := by rw [Nat.div_mul_cancel hu]
    rcases h_u_dvd with ⟨r, hr⟩
    use q * r
    change 10^k * A004290 u = n * (q * r)
    rw [h_eq, hq, hr]
    ring

  have h_M_digits : ∀ d' ∈ Nat.digits 10 M, d' = 0 ∨ d' = 1 := by
    rw [digits_ten_pow_mul k (A004290 u) h_u_val_pos]
    intro d' hd'
    rw [List.mem_append] at hd'
    rcases hd' with hd1 | hd2
    · have : d' = 0 := List.eq_of_mem_replicate hd1
      left; exact this
    · exact h_u_digits d' hd2

  have h_M_mem : M ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d' ∈ Nat.digits 10 m, d' = 0 ∨ d' = 1 } := ⟨h_M_pos, h_M_dvd, h_M_digits⟩
  unfold A004290
  exact Nat.sInf_le h_M_mem

theorem digits_ten_step (x : ℕ) (hx : x < 10) (y : ℕ) (hy : y > 0) :
    Nat.digits 10 (x + 10 * y) = x :: Nat.digits 10 y := by
  apply Nat.digits_add 10 (by norm_num) x y hx (Or.inr (Nat.ne_of_gt hy))

theorem digits_ten_base (x : ℕ) (hx : x < 10) (hx0 : x > 0) :
    Nat.digits 10 x = [x] := by
  exact Nat.digits_of_lt 10 x (Nat.ne_of_gt hx0) hx

/--
Conjecture from A004290 by David Radcliffe:
a(10^k) = 10^k and a(10^k - 1) = (10^(9k) - 1) / 9 for all k.
Is a(n) < a(10^k - 1) for all n < 10^k - 1?
We formalize the second, unproven part. The first two parts are stated as assumptions
to establish the right-hand side of the inequality.
-/
def check_digits_01_fuel (fuel : Nat) (n : Nat) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if n = 0 then true
    else
      let d := n % 10
      (d == 0 || d == 1) && check_digits_01_fuel f (n / 10)

lemma digits_step (n : ℕ) (hn : n ≠ 0) : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) := by
  have h_div_stmt : n % 10 + 10 * (n / 10) = n := Nat.mod_add_div n 10
  nth_rw 1 [← h_div_stmt]
  apply Nat.digits_add 10 (by norm_num) (n % 10) (n / 10) (Nat.mod_lt _ (by norm_num))
  by_cases h_div : n / 10 = 0
  · left
    have h_or : 10 = 0 ∨ n < 10 := Nat.div_eq_zero_iff.mp h_div
    have h_lt : n < 10 := by omega
    have h_mod : n % 10 = n := Nat.mod_eq_of_lt h_lt
    rw [h_mod]
    exact hn
  · right
    exact h_div

theorem check_digits_01_fuel_ok : ∀ (fuel : Nat) (n : Nat),
    check_digits_01_fuel fuel n = true → (Nat.digits 10 n).length ≤ fuel → ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 1
  | 0, n, _, h_len => by
    have : (Nat.digits 10 n).length = 0 := by omega
    have : Nat.digits 10 n = [] := List.eq_nil_of_length_eq_zero this
    rw [this]
    intro d hd; contradiction
  | f + 1, n, h, h_len => by
    by_cases hn : n = 0
    · subst hn
      intro d hd
      simp [Nat.digits_zero] at hd
    · unfold check_digits_01_fuel at h
      simp [hn] at h
      have h_digits := digits_step n hn
      rw [h_digits]
      intro d hd
      cases hd with
      | head => exact h.1
      | tail _ h_mem =>
        have h_len_arg := h_len
        have h_len' : (Nat.digits 10 (n / 10)).length ≤ f := by
          rw [h_digits] at h_len_arg
          simp only [List.length_cons] at h_len_arg
          omega
        exact check_digits_01_fuel_ok f (n / 10) h.2 h_len' d h_mem

lemma digits_len_le_of_lt (w : Nat) (h : w < 10^30) : (Nat.digits 10 w).length ≤ 30 := by
  by_cases hw : w = 0
  · subst hw
    simp
  · have h_base : 10 > 1 := by norm_num
    have h_pos : w > 0 := Nat.pos_of_ne_zero hw
    rw [Nat.digits_len 10 w (by omega) (by omega)]
    simp
    have h_log : Nat.log 10 w < 30 := by
      exact Nat.log_lt_of_lt_pow (by omega) h
    omega

def witness_fast_0 : Nat → Nat
  | 17 => 11101
  | 18 => 1111111110
  | 19 => 11001
  | 20 => 100
  | 21 => 10101
  | 22 => 110
  | 23 => 110101
  | 24 => 111000
  | 25 => 100
  | 26 => 10010
  | 27 => 1101111111
  | 28 => 100100
  | 29 => 1101101
  | 30 => 1110
  | 31 => 111011
  | 32 => 100000
  | 33 => 111111
  | 34 => 111010
  | 35 => 10010
  | 36 => 11111111100
  | 37 => 111
  | 38 => 110010
  | 39 => 10101
  | 40 => 1000
  | 41 => 11111
  | 42 => 101010
  | 43 => 1101101
  | 44 => 1100
  | 45 => 1111111110
  | 46 => 1101010
  | 47 => 10011
  | 48 => 1110000
  | 49 => 1100001
  | 50 => 100
  | 51 => 100011
  | 52 => 100100
  | 53 => 100011
  | 54 => 11011111110
  | 55 => 110
  | 56 => 1001000
  | 57 => 11001
  | 58 => 11011010
  | 59 => 11011111
  | 60 => 11100
  | 61 => 100101
  | 62 => 1110110
  | 63 => 1111011111
  | 64 => 1000000
  | 65 => 10010
  | 66 => 1111110
  | 67 => 1101011
  | 68 => 1110100
  | 69 => 10000101
  | 70 => 10010
  | 71 => 10011
  | 72 => 111111111000
  | 73 => 10001
  | 74 => 1110
  | 75 => 11100
  | 76 => 1100100
  | 77 => 1001
  | 78 => 101010
  | 79 => 10010011
  | 80 => 10000
  | 81 => 1111111101
  | 82 => 111110
  | 83 => 101011
  | 84 => 1010100
  | 85 => 111010
  | 86 => 11011010
  | 87 => 11010111
  | 88 => 11000
  | 89 => 11010101
  | 90 => 1111111110
  | 91 => 1001
  | 92 => 11010100
  | 93 => 10000011
  | 94 => 100110
  | 95 => 110010
  | 96 => 11100000
  | 97 => 11100001
  | 98 => 11000010
  | 99 => 111111111111111111
  | 100 => 100
  | 101 => 101
  | 102 => 1000110
  | 103 => 11100001
  | 104 => 1001000
  | 105 => 101010
  | 106 => 1000110
  | 107 => 100010011
  | 108 => 110111111100
  | 109 => 1001010111
  | 110 => 110
  | 111 => 111
  | 112 => 10010000
  | 113 => 1011011
  | 114 => 110010
  | 115 => 1101010
  | 116 => 110110100
  | 117 => 10101111111
  | 118 => 110111110
  | 119 => 100111011
  | 120 => 111000
  | 121 => 11011
  | 122 => 1001010
  | 123 => 10001100111
  | 124 => 11101100
  | 125 => 1000
  | 126 => 11110111110
  | 127 => 11010011
  | 128 => 10000000
  | 129 => 100100001
  | 130 => 10010
  | 131 => 101001
  | 132 => 11111100
  | 133 => 11101111
  | 134 => 11010110
  | 135 => 11011111110
  | 136 => 11101000
  | 137 => 10001
  | 138 => 100001010
  | 139 => 110110101
  | 140 => 100100
  | 141 => 10011
  | 142 => 100110
  | 143 => 1001
  | 144 => 1111111110000
  | 145 => 11011010
  | 146 => 100010
  | 147 => 1100001
  | 148 => 11100
  | 149 => 110111
  | 150 => 11100
  | 151 => 1110001
  | 152 => 11001000
  | 153 => 10111110111
  | 154 => 10010
  | 155 => 1110110
  | 156 => 1010100
  | 157 => 10101101011
  | 158 => 100100110
  | 159 => 100011
  | 160 => 100000
  | 161 => 11101111
  | 162 => 11111111010
  | 163 => 1010111
  | 164 => 1111100
  | 165 => 1111110
  | 166 => 1010110
  | 167 => 11111011
  | 168 => 10101000
  | 169 => 10111101
  | 170 => 111010
  | 171 => 1111011111
  | 172 => 110110100
  | 173 => 1011001101
  | 174 => 110101110
  | 175 => 100100
  | 176 => 110000
  | 177 => 100101111
  | 178 => 110101010
  | 179 => 11010111
  | 180 => 11111111100
  | 181 => 1001111
  | 182 => 10010
  | 183 => 100101
  | 184 => 110101000
  | 185 => 1110
  | 186 => 100000110
  | 187 => 1001011
  | 188 => 1001100
  | 189 => 1010111010111
  | 190 => 110010
  | 191 => 11101111
  | 192 => 111000000
  | 193 => 11001
  | 194 => 111000010
  | 195 => 101010
  | 196 => 110000100
  | 197 => 1101000101
  | 198 => 1111111111111111110
  | 199 => 111000011
  | 200 => 1000
  | 201 => 10010001
  | 202 => 1010
  | 203 => 11010111
  | 204 => 10001100
  | 205 => 111110
  | 206 => 111000010
  | 207 => 11011111011
  | 208 => 10010000
  | 209 => 100111
  | 210 => 101010
  | 211 => 110100011
  | 212 => 10001100
  | 213 => 10011
  | 214 => 1000100110
  | 215 => 11011010
  | 216 => 1101111111000
  | 217 => 10000011
  | 218 => 10010101110
  | 219 => 1110111
  | 220 => 1100
  | 221 => 100111011
  | 222 => 1110
  | 223 => 1001111001
  | 224 => 100100000
  | 225 => 11111111100
  | 226 => 10110110
  | 227 => 11001101
  | 228 => 1100100
  | 229 => 10000100011
  | 230 => 1101010
  | 231 => 111111
  | 232 => 1101101000
  | 233 => 111110011
  | 234 => 101011111110
  | 235 => 100110
  | 236 => 1101111100
  | 237 => 101010111
  | 238 => 1001110110
  | 239 => 1111111
  | 240 => 1110000
  | 241 => 111101
  | 242 => 110110
  | 243 => 100111110111
  | 244 => 10010100
  | 245 => 11000010
  | 246 => 100011001110
  | 247 => 1000000001
  | 248 => 111011000
  | 249 => 1111100001
  | 250 => 1000
  | 251 => 110001001
  | 252 => 111101111100
  | 253 => 11111001
  | 254 => 110100110
  | 255 => 1000110
  | 256 => 100000000
  | 257 => 101001
  | 258 => 1001000010
  | 259 => 10101
  | 260 => 100100
  | 261 => 10111101111
  | 262 => 1010010
  | 263 => 10001101
  | 264 => 111111000
  | 265 => 1000110
  | 266 => 111011110
  | 267 => 1011111111
  | 268 => 110101100
  | 269 => 100100011
  | 270 => 11011111110
  | 271 => 11111
  | 272 => 111010000
  | 273 => 10101
  | 274 => 100010
  | 275 => 1100
  | 276 => 1000010100
  | 277 => 110111101
  | 278 => 1101101010
  | 279 => 11111010111
  | 280 => 1001000
  | 281 => 101000111
  | 282 => 100110
  | 283 => 10010111011
  | 284 => 1001100
  | 285 => 110010
  | 286 => 10010
  | 287 => 1011101
  | 288 => 11111111100000
  | 289 => 1100110001
  | 290 => 11011010
  | 291 => 100110111
  | 292 => 1000100
  | 293 => 110000111
  | 294 => 11000010
  | 295 => 110111110
  | 296 => 111000
  | 297 => 1111011111111111111
  | 298 => 1101110
  | 299 => 10010101101
  | 300 => 11100
  | 301 => 1101001111
  | 302 => 11100010
  | 303 => 1011111
  | 304 => 110010000
  | 305 => 1001010
  | 306 => 101111101110
  | 307 => 10001100011
  | 308 => 100100
  | 309 => 1110110001
  | 310 => 1110110
  | 311 => 101010001
  | 312 => 10101000
  | 313 => 11001011
  | 314 => 101011010110
  | 315 => 11110111110
  | 316 => 1001001100
  | 317 => 1000000111111
  | 318 => 1000110
  | 319 => 111101001
  | 320 => 1000000
  | 321 => 110100111
  | 322 => 111011110
  | 323 => 11010101
  | 324 => 111111110100
  | 325 => 100100
  | 326 => 10101110
  | 327 => 1001010111
  | 328 => 11111000
  | 329 => 11110001
  | 330 => 1111110
  | 331 => 111011111
  | 332 => 10101100
  | 333 => 111111111
  | 334 => 111110110
  | 335 => 11010110
  | 336 => 101010000
  | 337 => 1011
  | 338 => 101111010
  | 339 => 1010101011
  | 340 => 1110100
  | 341 => 11001001
  | 342 => 11110111110
  | 343 => 1100001
  | 344 => 1101101000
  | 345 => 100001010
  | 346 => 10110011010
  | 347 => 1010111101
  | 348 => 1101011100
  | 349 => 1100100001
  | 350 => 100100
  | 351 => 1011001011111
  | 352 => 1100000
  | 353 => 10101101001
  | 354 => 1001011110
  | 355 => 100110
  | 356 => 1101010100
  | 357 => 100111011
  | 358 => 110101110
  | 359 => 1001010111
  | 360 => 111111111000
  | 361 => 11101111
  | 362 => 10011110
  | 363 => 1000111101
  | 364 => 100100
  | 365 => 100010
  | 366 => 1001010
  | 367 => 1101
  | 368 => 1101010000
  | 369 => 111001111011
  | 370 => 1110
  | 371 => 100111011
  | 372 => 1000001100
  | 373 => 101011011
  | 374 => 10010110
  | 375 => 111000
  | 376 => 10011000
  | 377 => 11100011
  | 378 => 10101110101110
  | 379 => 100101101
  | 380 => 1100100
  | 381 => 101011101
  | 382 => 111011110
  | 383 => 11010101
  | 384 => 1110000000
  | 385 => 10010
  | 386 => 110010
  | 387 => 11111011101
  | 388 => 1110000100
  | 389 => 1011011
  | 390 => 101010
  | 391 => 110111000101
  | 392 => 1100001000
  | 393 => 101001
  | 394 => 11010001010
  | 395 => 100100110
  | 396 => 11111111111111111100
  | 397 => 11010001
  | 398 => 1110000110
  | 399 => 1111011111
  | 400 => 10000
  | 401 => 1111011001
  | 402 => 100100010
  | 403 => 111001111
  | 404 => 10100
  | 405 => 11111111010
  | 406 => 110101110
  | 407 => 111111
  | 408 => 100011000
  | 409 => 1100001001
  | 410 => 111110
  | 411 => 1110111
  | 412 => 1110000100
  | 413 => 11101100101
  | 414 => 110111110110
  | 415 => 1010110
  | 416 => 100100000
  | 417 => 110110101
  | 418 => 1001110
  | 419 => 10001111
  | 420 => 1010100
  | 421 => 100110011
  | 422 => 1101000110
  | 423 => 100111011111
  | 424 => 100011000
  | 425 => 1110100
  | 426 => 100110
  | 427 => 1010010001
  | 428 => 10001001100
  | 429 => 111111
  | 430 => 11011010
  | 431 => 101100101
  | 432 => 11011111110000
  | 433 => 10001001
  | 434 => 100000110
  | 435 => 110101110
  | 436 => 100101011100
  | 437 => 11101111
  | 438 => 11101110
  | 439 => 10001100011
  | 440 => 11000
  | 441 => 11111110101
  | 442 => 1001110110
  | 443 => 110000001
  | 444 => 11100
  | 445 => 110101010
  | 446 => 10011110010
  | 447 => 10000111011
  | 448 => 1001000000
  | 449 => 111100111
  | 450 => 11111111100
  | 451 => 1111111111
  | 452 => 101101100
  | 453 => 10001011011
  | 454 => 110011010
  | 455 => 10010
  | 456 => 11001000
  | 457 => 1001101001
  | 458 => 100001000110
  | 459 => 111101101011
  | 460 => 11010100
  | 461 => 111101
  | 462 => 1111110
  | 463 => 110100011
  | 464 => 11011010000
  | 465 => 100000110
  | 466 => 1111100110
  | 467 => 100000111
  | 468 => 1010111111100
  | 469 => 1100100001
  | 470 => 100110
  | 471 => 110111101101
  | 472 => 11011111000
  | 473 => 111111011
  | 474 => 1010101110
  | 475 => 1100100
  | 476 => 10011101100
  | 477 => 11111101101
  | 478 => 11111110
  | 479 => 100111
  | 480 => 11100000
  | 481 => 10101
  | 482 => 1111010
  | 483 => 101100111
  | 484 => 1101100
  | 485 => 111000010
  | 486 => 1001111101110
  | 487 => 1100110111
  | 488 => 100101000
  | 489 => 100000011
  | 490 => 11000010
  | 491 => 100101010101
  | 492 => 1000110011100
  | 493 => 111101001
  | 494 => 10000000010
  | 495 => 1111111111111111110
  | 496 => 1110110000
  | 497 => 11000101
  | 498 => 11111000010
  | 499 => 11100000011
  | 500 => 1000
  | 501 => 100000101
  | 502 => 1100010010
  | 503 => 1101000101
  | 504 => 1111011111000
  | 505 => 1010
  | 506 => 111110010
  | 507 => 10111101
  | 508 => 1101001100
  | 509 => 100101100011
  | 510 => 1000110
  | 511 => 10011001
  | 512 => 1000000000
  | 513 => 110101110111
  | 514 => 1010010
  | 515 => 111000010
  | 516 => 10010000100
  | 517 => 1001110011
  | 518 => 101010
  | 519 => 1011001101
  | 520 => 1001000
  | 521 => 1010110111
  | 522 => 101111011110
  | 523 => 110111001101
  | 524 => 10100100
  | 525 => 1010100
  | 526 => 100011010
  | 527 => 1101110111
  | 528 => 1111110000
  | 529 => 1000111001
  | 530 => 1000110
  | 531 => 101011111011
  | 532 => 1110111100
  | 533 => 1011101
  | 534 => 10111111110
  | 535 => 1000100110
  | 536 => 1101011000
  | 537 => 11010111
  | 538 => 1001000110
  | 539 => 10111101
  | 540 => 110111111100
  | 541 => 10101011
  | 542 => 111110
  | 543 => 11110001001
  | 544 => 1110100000
  | 545 => 10010101110
  | 546 => 101010
  | 547 => 100101
  | 548 => 1000100
  | 549 => 111011011101
  | 550 => 1100
  | 551 => 1010011101
  | 552 => 10000101000
  | 553 => 110001101
  | 554 => 1101111010
  | 555 => 1110
  | 556 => 11011010100
  | 557 => 1110101
  | 558 => 111110101110
  | 559 => 110011110001
  | 560 => 10010000
  | 561 => 100111011
  | 562 => 1010001110
  | 563 => 1101001111
  | 564 => 1001100
  | 565 => 10110110
  | 566 => 100101110110
  | 567 => 1011011011101
  | 568 => 10011000
  | 569 => 1011010011
  | 570 => 110010
  | 571 => 1000010001
  | 572 => 100100
  | 573 => 10000000011
  | 574 => 10111010
  | 575 => 11010100
  | 576 => 111111111000000
  | 577 => 110001011
  | 578 => 11001100010
  | 579 => 11001
  | 580 => 110110100
  | 581 => 10100000001
  | 582 => 1001101110
  | 583 => 1001011
  | 584 => 10001000
  | 585 => 101011111110
  | 586 => 1100001110
  | 587 => 10010111
  | 588 => 110000100
  | 589 => 11011001011
  | 590 => 110111110
  | 591 => 11010100101
  | 592 => 1110000
  | 593 => 1001000011
  | 594 => 11110111111111111110
  | 595 => 1001110110
  | 596 => 11011100
  | 597 => 1100010111
  | 598 => 100101011010
  | 599 => 10101110111
  | 600 => 111000
  | 601 => 11001011111
  | 602 => 11010011110
  | 603 => 1111110111
  | 604 => 111000100
  | 605 => 110110
  | 606 => 10111110
  | 607 => 1001011010101
  | 608 => 1100100000
  | 609 => 11010111
  | 610 => 1001010
  | 611 => 1100100001
  | 612 => 1011111011100
  | 613 => 110001011
  | 614 => 100011000110
  | 615 => 100011001110
  | 616 => 1001000
  | 617 => 1100111
  | 618 => 11101100010
  | 619 => 11010010011
  | 620 => 11101100
  | 621 => 101001111111
  | 622 => 1010100010
  | 623 => 1101001111
  | 624 => 101010000
  | 625 => 10000
  | 626 => 110010110
  | 627 => 111100011
  | 628 => 1010110101100
  | 629 => 100011
  | 630 => 11110111110
  | 631 => 101011111
  | 632 => 10010011000
  | 633 => 110001010011
  | 634 => 10000001111110
  | 635 => 110100110
  | 636 => 10001100
  | 637 => 10111101
  | 638 => 1111010010
  | 639 => 100111011111
  | 640 => 10000000
  | 641 => 1110001111
  | 642 => 1101001110
  | 643 => 10011000101
  | 644 => 1110111100
  | 645 => 1001000010
  | 646 => 110101010
  | 647 => 10110011001
  | 648 => 1111111101000
  | 649 => 100101111
  | 650 => 100100
  | 651 => 10000011
  | 652 => 101011100
  | 653 => 11101
  | 654 => 10010101110
  | 655 => 1010010
  | 656 => 111110000
  | 657 => 101111001111
  | 658 => 111100010
  | 659 => 11110100111
  | 660 => 11111100
  | 661 => 101000100001
  | 662 => 1110111110
  | 663 => 100111011
  | 664 => 101011000
  | 665 => 111011110
  | 666 => 1111111110
  | 667 => 1110110111
  | 668 => 1111101100
  | 669 => 1001111001
  | 670 => 11010110
  | 671 => 1101111
  | 672 => 1010100000
  | 673 => 100100001
  | 674 => 10110
  | 675 => 110111111100
  | 676 => 1011110100
  | 677 => 1001010110101
  | 678 => 10101010110
  | 679 => 1110110001
  | 680 => 11101000
  | 681 => 11011110111
  | 682 => 110010010
  | 683 => 100000111101
  | 684 => 111101111100
  | 685 => 100010
  | 686 => 11000010
  | 687 => 11110111101
  | 688 => 11011010000
  | 689 => 100111011
  | 690 => 100001010
  | 691 => 10010110001
  | 692 => 101100110100
  | 693 => 111111111111111111
  | 694 => 10101111010
  | 695 => 1101101010
  | 696 => 11010111000
  | 697 => 10011011
  | 698 => 11001000010
  | 699 => 1001100111
  | 700 => 100100
  | 701 => 10110110111
  | 702 => 10110010111110
  | 703 => 10100001
  | 704 => 11000000
  | 705 => 100110
  | 706 => 101011010010
  | 707 => 101101
  | 708 => 10010111100
  | 709 => 111011100001
  | 710 => 100110
  | 711 => 11111011011
  | 712 => 11010101000
  | 713 => 1100000001
  | 714 => 1001110110
  | 715 => 10010
  | 716 => 1101011100
  | 717 => 101000011111011
  | 718 => 10010101110
  | 719 => 101000000001
  | 720 => 1111111110000
  | 721 => 1110110001
  | 722 => 111011110
  | 723 => 10001011011
  | 724 => 100111100
  | 725 => 110110100
  | 726 => 10001111010
  | 727 => 101100010001
  | 728 => 1001000
  | 729 => 101111111001
  | 730 => 100010
  | 731 => 1101011001
  | 732 => 10010100
  | 733 => 10001101111
  | 734 => 11010
  | 735 => 11000010
  | 736 => 11010100000
  | 737 => 110110011
  | 738 => 1110011110110
  | 739 => 110111
  | 740 => 11100
  | 741 => 10110101001
  | 742 => 1001110110
  | 743 => 10110001
  | 744 => 10000011000
  | 745 => 1101110
  | 746 => 1010110110
  | 747 => 100110111111
  | 748 => 100101100
  | 749 => 11011100111011
  | 750 => 111000
  | 751 => 1111000111
  | 752 => 100110000
  | 753 => 1110010101
  | 754 => 111000110
  | 755 => 11100010
  | 756 => 101011101011100
  | 757 => 101101001011
  | 758 => 1001011010
  | 759 => 11111001
  | 760 => 11001000
  | 761 => 11011100011
  | 762 => 1010111010
  | 763 => 1110010111
  | 764 => 1110111100
  | 765 => 101111101110
  | 766 => 110101010
  | 767 => 11101100101
  | 768 => 11100000000
  | 769 => 100011010001
  | 770 => 10010
  | 771 => 101001
  | 772 => 1100100
  | 773 => 10111000011
  | 774 => 111110111010
  | 775 => 11101100
  | 776 => 11100001000
  | 777 => 10101
  | 778 => 10110110
  | 779 => 1011001001
  | 780 => 1010100
  | 781 => 1001110011
  | 782 => 1101110001010
  | 783 => 1011011101011
  | 784 => 11000010000
  | 785 => 101011010110
  | 786 => 1010010
  | 787 => 10110001111
  | 788 => 110100010100
  | 789 => 101100100101
  | 790 => 100100110
  | 791 => 110011110111
  | 792 => 111111111111111111000
  | 793 => 1010010001
  | 794 => 110100010
  | 795 => 1000110
  | 796 => 11100001100
  | 797 => 10001101101
  | 798 => 11110111110
  | 799 => 1101101101
  | 800 => 100000
  | 801 => 1011111111
  | 802 => 11110110010
  | 803 => 110011
  | 804 => 1001000100
  | 805 => 111011110
  | 806 => 1110011110
  | 807 => 1010100111
  | 808 => 101000
  | 809 => 11101000111
  | 810 => 11111111010
  | 811 => 1001010001
  | 812 => 1101011100
  | 813 => 111111111111111
  | 814 => 1111110
  | 815 => 10101110
  | 816 => 1000110000
  | 817 => 111010000001
  | 818 => 11000010010
  | 819 => 10101111111
  | 820 => 1111100
  | 821 => 10000101011
  | 822 => 11101110
  | 823 => 1100011101
  | 824 => 11100001000
  | 825 => 11111100
  | 826 => 111011001010
  | 827 => 1000100001001
  | 828 => 1101111101100
  | 829 => 11000001
  | 830 => 1010110
  | 831 => 1011101110101
  | 832 => 1001000000
  | 833 => 1010010001
  | 834 => 1101101010
  | 835 => 111110110
  | 836 => 10011100
  | 837 => 11111010111
  | 838 => 100011110
  | 839 => 11100011111
  | 840 => 10101000
  | 841 => 100110000101
  | 842 => 1001100110
  | 843 => 1011100101
  | 844 => 11010001100
  | 845 => 101111010
  | 846 => 1001110111110
  | 847 => 11011
  | 848 => 1000110000
  | 849 => 10011110001
  | 850 => 1110100
  | 851 => 10000101
  | 852 => 1001100
  | 853 => 1001010001
  | 854 => 10100100010
  | 855 => 11110111110
  | 856 => 100010011000
  | 857 => 10010011101
  | 858 => 1111110
  | 859 => 101111111011
  | 860 => 110110100
  | 861 => 110010100011
  | 862 => 1011001010
  | 863 => 110001110101
  | 864 => 110111111100000
  | 865 => 10110011010
  | 866 => 100010010
  | 867 => 101010011001
  | 868 => 1000001100
  | 869 => 10010011
  | 870 => 110101110
  | 871 => 111001111
  | 872 => 1001010111000
  | 873 => 110011101111
  | 874 => 111011110
  | 875 => 1001000
  | 876 => 111011100
  | 877 => 1010111010011
  | 878 => 100011000110
  | 879 => 1001101011
  | 880 => 110000
  | 881 => 100100101
  | 882 => 111111101010
  | 883 => 1101101
  | 884 => 10011101100
  | 885 => 1001011110
  | 886 => 1100000010
  | 887 => 11000000111
  | 888 => 111000
  | 889 => 1001110011111
  | 890 => 110101010
  | 891 => 1111111111111111011
  | 892 => 100111100100
  | 893 => 100001111011
  | 894 => 100001110110
  | 895 => 110101110
  | 896 => 10010000000
  | 897 => 10010101101
  | 898 => 1111001110
  | 899 => 11101111001001
  | 900 => 11111111100
  | 901 => 100011
  | 902 => 11111111110
  | 903 => 1110001011
  | 904 => 1011011000
  | 905 => 10011110
  | 906 => 100010110110
  | 907 => 10001011011
  | 908 => 1100110100
  | 909 => 1011111111111111111
  | 910 => 10010
  | 911 => 101000011001
  | 912 => 110010000
  | 913 => 1111100001
  | 914 => 10011010010
  | 915 => 1001010
  | 916 => 1000010001100
  | 917 => 10110001111
  | 918 => 1111011010110
  | 919 => 1010111010011
  | 920 => 110101000
  | 921 => 1011111000111
  | 922 => 1111010
  | 923 => 10100100101
  | 924 => 11111100
  | 925 => 11100
  | 926 => 1101000110
  | 927 => 111101101101
  | 928 => 110110100000
  | 929 => 1100000101
  | 930 => 100000110
  | 931 => 101001100011
  | 932 => 11111001100
  | 933 => 11101111101
  | 934 => 1000001110
  | 935 => 10010110
  | 936 => 10101111111000
  | 937 => 10110111001
  | 938 => 11001000010
  | 939 => 1100000001
  | 940 => 1001100
  | 941 => 100001011
  | 942 => 1101111011010
  | 943 => 1001001101
  | 944 => 110111110000
  | 945 => 10101110101110
  | 946 => 1111110110
  | 947 => 1011001101
  | 948 => 10101011100
  | 949 => 10011001
  | 950 => 1100100
  | 951 => 1001111101011
  | 952 => 100111011000
  | 953 => 100101011011
  | 954 => 111111011010
  | 955 => 111011110
  | 956 => 111111100
  | 957 => 111101001
  | 958 => 1001110
  | 959 => 10011001
  | 960 => 111000000
  | 961 => 1010011
  | 962 => 101010
  | 963 => 111010111011
  | 964 => 11110100
  | 965 => 110010
  | 966 => 1011001110
  | 967 => 10010000101
  | 968 => 11011000
  | 969 => 111101101011
  | 970 => 111000010
  | 971 => 1001101
  | 972 => 10011111011100
  | 973 => 1010010001
  | 974 => 11001101110
  | 975 => 1010100
  | 976 => 1001010000
  | 977 => 1011110001
  | 978 => 1000000110
  | 979 => 1100111111
  | 980 => 110000100
  | 981 => 1111111011
  | 982 => 1001010101010
  | 983 => 11000111101
  | 984 => 10001100111000
  | 985 => 11010001010
  | 986 => 1111010010
  | 987 => 100101000111
  | 988 => 100000000100
  | 989 => 11111011111101001
  | 990 => 1111111111111111110
  | 991 => 110001
  | 992 => 11101100000
  | 993 => 1011000111
  | 994 => 110001010
  | 995 => 1110000110
  | 996 => 111110000100
  | 997 => 111110000001
  | 998 => 111000000110
  | 999 => 111111111111111111111111111
  | _ => 1

def witness_fast_1 : Nat → Nat
  | 1000 => 1000
  | 1001 => 1001
  | 1002 => 1000001010
  | 1003 => 111110000001
  | 1004 => 11000100100
  | 1005 => 100100010
  | 1006 => 11010001010
  | 1007 => 11111110111
  | 1008 => 11110111110000
  | 1009 => 10010001111111
  | 1010 => 1010
  | 1011 => 1011
  | 1012 => 1111100100
  | 1013 => 10000110101
  | 1014 => 101111010
  | 1015 => 110101110
  | 1016 => 11010011000
  | 1017 => 110011110111
  | 1018 => 1001011000110
  | 1019 => 1101110001
  | 1020 => 10001100
  | 1021 => 10011100011
  | 1022 => 100110010
  | 1023 => 10010011011
  | 1024 => 10000000000
  | 1025 => 1111100
  | 1026 => 1101011101110
  | 1027 => 11101011010011
  | 1028 => 10100100
  | 1029 => 1100001
  | 1030 => 111000010
  | 1031 => 1001101
  | 1032 => 100100001000
  | 1033 => 111011001011
  | 1034 => 10011100110
  | 1035 => 110111110110
  | 1036 => 1010100
  | 1037 => 1010010001
  | 1038 => 10110011010
  | 1039 => 10101001111
  | 1040 => 10010000
  | 1041 => 10101001011
  | 1042 => 10101101110
  | 1043 => 11000111101
  | 1044 => 1011110111100
  | 1045 => 1001110
  | 1046 => 1101110011010
  | 1047 => 1011101001111
  | 1048 => 101001000
  | 1049 => 100001001111
  | 1050 => 1010100
  | 1051 => 1010011
  | 1052 => 1000110100
  | 1053 => 1011011011101
  | 1054 => 11011101110
  | 1055 => 1101000110
  | 1056 => 11111100000
  | 1057 => 1111111001
  | 1058 => 10001110010
  | 1059 => 10101101001
  | 1060 => 10001100
  | 1061 => 1000011111001
  | 1062 => 1010111110110
  | 1063 => 10000000110101
  | 1064 => 11101111000
  | 1065 => 100110
  | 1066 => 10111010
  | 1067 => 11100001
  | 1068 => 101111111100
  | 1069 => 1100001
  | 1070 => 1000100110
  | 1071 => 111011111001
  | 1072 => 11010110000
  | 1073 => 100011111
  | 1074 => 110101110
  | 1075 => 110110100
  | 1076 => 10010001100
  | 1077 => 1001010111
  | 1078 => 101111010
  | 1079 => 10100000001
  | 1080 => 1101111111000
  | 1081 => 1010001001
  | 1082 => 101010110
  | 1083 => 110111011011
  | 1084 => 1111100
  | 1085 => 100000110
  | 1086 => 111100010010
  | 1087 => 10001001111
  | 1088 => 11101000000
  | 1089 => 10011111111111111111
  | 1090 => 10010101110
  | 1091 => 100000101011
  | 1092 => 1010100
  | 1093 => 111111101
  | 1094 => 1001010
  | 1095 => 11101110
  | 1096 => 10001000
  | 1097 => 1111001011
  | 1098 => 1110110111010
  | 1099 => 10010111111111111
  | 1100 => 1100
  | 1101 => 1101
  | 1102 => 10100111010
  | 1103 => 1110100011
  | 1104 => 100001010000
  | 1105 => 1001110110
  | 1106 => 1100011010
  | 1107 => 1101011100111
  | 1108 => 11011110100
  | 1109 => 1100010101101
  | 1110 => 1110
  | 1111 => 1111
  | 1112 => 110110101000
  | 1113 => 100111011
  | 1114 => 11101010
  | 1115 => 10011110010
  | 1116 => 1111101011100
  | 1117 => 11011110101
  | 1118 => 1100111100010
  | 1119 => 101011011
  | 1120 => 100100000
  | 1121 => 100100010001
  | 1122 => 1001110110
  | 1123 => 100011011
  | 1124 => 10100011100
  | 1125 => 111111111000
  | 1126 => 11010011110
  | 1127 => 110100011
  | 1128 => 10011000
  | 1129 => 100000011001
  | 1130 => 10110110
  | 1131 => 101110010001
  | 1132 => 1001011101100
  | 1133 => 11100001
  | 1134 => 10110110111010
  | 1135 => 110011010
  | 1136 => 100110000
  | 1137 => 100111000101
  | 1138 => 10110100110
  | 1139 => 11110101001
  | 1140 => 1100100
  | 1141 => 100100011011
  | 1142 => 10000100010
  | 1143 => 11111111001
  | 1144 => 1001000
  | 1145 => 100001000110
  | 1146 => 100000000110
  | 1147 => 111010101
  | 1148 => 101110100
  | 1149 => 10100111001
  | 1150 => 11010100
  | 1151 => 110100011111
  | 1152 => 1111111110000000
  | 1153 => 100100001
  | 1154 => 1100010110
  | 1155 => 1111110
  | 1156 => 110011000100
  | 1157 => 11111010001
  | 1158 => 110010
  | 1159 => 10001011
  | 1160 => 1101101000
  | 1161 => 101011111101
  | 1162 => 101000000010
  | 1163 => 1001101011101
  | 1164 => 10011011100
  | 1165 => 1111100110
  | 1166 => 10010110
  | 1167 => 11010100011
  | 1168 => 100010000
  | 1169 => 100100101101
  | 1170 => 101011111110
  | 1171 => 100010111001
  | 1172 => 11000011100
  | 1173 => 1011111111111
  | 1174 => 100101110
  | 1175 => 1001100
  | 1176 => 1100001000
  | 1177 => 110100111
  | 1178 => 110110010110
  | 1179 => 1001100111111
  | 1180 => 1101111100
  | 1181 => 101010010001
  | 1182 => 110101001010
  | 1183 => 10111101
  | 1184 => 11100000
  | 1185 => 1010101110
  | 1186 => 10010000110
  | 1187 => 100010000101
  | 1188 => 111101111111111111100
  | 1189 => 100010011001
  | 1190 => 1001110110
  | 1191 => 11000101011
  | 1192 => 110111000
  | 1193 => 11011100101
  | 1194 => 11000101110
  | 1195 => 11111110
  | 1196 => 1001010110100
  | 1197 => 1111011111
  | 1198 => 101011101110
  | 1199 => 1111100111
  | 1200 => 1110000
  | 1201 => 10111100101
  | 1202 => 110010111110
  | 1203 => 101000111001
  | 1204 => 110100111100
  | 1205 => 1111010
  | 1206 => 11111101110
  | 1207 => 111110111011
  | 1208 => 1110001000
  | 1209 => 10010011011
  | 1210 => 110110
  | 1211 => 1011100110111
  | 1212 => 101111100
  | 1213 => 111000110111
  | 1214 => 10010110101010
  | 1215 => 1001111101110
  | 1216 => 11001000000
  | 1217 => 101011
  | 1218 => 110101110
  | 1219 => 1100000001
  | 1220 => 10010100
  | 1221 => 111111
  | 1222 => 11001000010
  | 1223 => 100111111
  | 1224 => 10111110111000
  | 1225 => 110000100
  | 1226 => 1100010110
  | 1227 => 11100010101
  | 1228 => 1000110001100
  | 1229 => 100001111001
  | 1230 => 100011001110
  | 1231 => 100001111001
  | 1232 => 10010000
  | 1233 => 10110100101111
  | 1234 => 11001110
  | 1235 => 10000000010
  | 1236 => 111011000100
  | 1237 => 10110001
  | 1238 => 110100100110
  | 1239 => 111110000001
  | 1240 => 111011000
  | 1241 => 10011111011
  | 1242 => 1010011111110
  | 1243 => 100110110001
  | 1244 => 10101000100
  | 1245 => 11111000010
  | 1246 => 11010011110
  | 1247 => 1101101
  | 1248 => 1010100000
  | 1249 => 111100110001
  | 1250 => 10000
  | 1251 => 100111101111
  | 1252 => 1100101100
  | 1253 => 11010111
  | 1254 => 1111000110
  | 1255 => 1100010010
  | 1256 => 10101101011000
  | 1257 => 111110001
  | 1258 => 1000110
  | 1259 => 100001111
  | 1260 => 111101111100
  | 1261 => 1110110001
  | 1262 => 1010111110
  | 1263 => 101010101001
  | 1264 => 100100110000
  | 1265 => 111110010
  | 1266 => 1100010100110
  | 1267 => 101011110011
  | 1268 => 100000011111100
  | 1269 => 111101101011
  | 1270 => 110100110
  | 1271 => 1001001001001
  | 1272 => 100011000
  | 1273 => 101111000001
  | 1274 => 101111010
  | 1275 => 10001100
  | 1276 => 11110100100
  | 1277 => 1011010111001
  | 1278 => 1001110111110
  | 1279 => 1001010001011
  | 1280 => 100000000
  | 1281 => 110010001101
  | 1282 => 11100011110
  | 1283 => 1111010001
  | 1284 => 11010011100
  | 1285 => 1010010
  | 1286 => 100110001010
  | 1287 => 111111111111111111
  | 1288 => 11101111000
  | 1289 => 10100100001
  | 1290 => 1001000010
  | 1291 => 10111010011
  | 1292 => 1101010100
  | 1293 => 101010100011
  | 1294 => 101100110010
  | 1295 => 101010
  | 1296 => 11111111010000
  | 1297 => 11000000011111
  | 1298 => 1001011110
  | 1299 => 10001001
  | 1300 => 100100
  | 1301 => 11001010111
  | 1302 => 100000110
  | 1303 => 1101110101011
  | 1304 => 1010111000
  | 1305 => 101111011110
  | 1306 => 111010
  | 1307 => 110110101001
  | 1308 => 100101011100
  | 1309 => 100111011
  | 1310 => 1010010
  | 1311 => 110011111101
  | 1312 => 1111100000
  | 1313 => 101101
  | 1314 => 1011110011110
  | 1315 => 100011010
  | 1316 => 1111000100
  | 1317 => 10100011101
  | 1318 => 111101001110
  | 1319 => 110001011001
  | 1320 => 111111000
  | 1321 => 10001110011111
  | 1322 => 1010001000010
  | 1323 => 1100011111101
  | 1324 => 11101111100
  | 1325 => 10001100
  | 1326 => 1001110110
  | 1327 => 1111011101111
  | 1328 => 1010110000
  | 1329 => 110000001
  | 1330 => 111011110
  | 1331 => 1101111011
  | 1332 => 11111111100
  | 1333 => 1010010101
  | 1334 => 11101101110
  | 1335 => 10111111110
  | 1336 => 11111011000
  | 1337 => 11101111
  | 1338 => 10011110010
  | 1339 => 1110110001
  | 1340 => 110101100
  | 1341 => 10111101111
  | 1342 => 11011110
  | 1343 => 110001101
  | 1344 => 10101000000
  | 1345 => 1001000110
  | 1346 => 1001000010
  | 1347 => 1101110111001
  | 1348 => 101100
  | 1349 => 101111110011
  | 1350 => 110111111100
  | 1351 => 101011110011
  | 1352 => 10111101000
  | 1353 => 10011100011
  | 1354 => 10010101101010
  | 1355 => 111110
  | 1356 => 101010101100
  | 1357 => 1101101011
  | 1358 => 11101100010
  | 1359 => 11111101101
  | 1360 => 111010000
  | 1361 => 1110101011
  | 1362 => 110111101110
  | 1363 => 110100001011
  | 1364 => 1100100100
  | 1365 => 101010
  | 1366 => 1000001111010
  | 1367 => 11101001001
  | 1368 => 1111011111000
  | 1369 => 10100111001
  | 1370 => 100010
  | 1371 => 101101010001
  | 1372 => 110000100
  | 1373 => 100111110101
  | 1374 => 111101111010
  | 1375 => 11000
  | 1376 => 110110100000
  | 1377 => 111101101011
  | 1378 => 1001110110
  | 1379 => 11010100101
  | 1380 => 1000010100
  | 1381 => 1000011101
  | 1382 => 100101100010
  | 1383 => 1101000100011
  | 1384 => 1011001101000
  | 1385 => 1101111010
  | 1386 => 1111111111111111110
  | 1387 => 101010110001
  | 1388 => 101011110100
  | 1389 => 111011101011
  | 1390 => 1101101010
  | 1391 => 11010111110011
  | 1392 => 110101110000
  | 1393 => 10101001001
  | 1394 => 100110110
  | 1395 => 111110101110
  | 1396 => 110010000100
  | 1397 => 100000100101
  | 1398 => 10011001110
  | 1399 => 100011011101
  | 1400 => 1001000
  | 1401 => 10011001011
  | 1402 => 101101101110
  | 1403 => 101110001
  | 1404 => 101100101111100
  | 1405 => 1010001110
  | 1406 => 101000010
  | 1407 => 1000001110101
  | 1408 => 110000000
  | 1409 => 100010100001
  | 1410 => 100110
  | 1411 => 100100010011
  | 1412 => 1010110100100
  | 1413 => 110111101101
  | 1414 => 1011010
  | 1415 => 100101110110
  | 1416 => 100101111000
  | 1417 => 101001001101
  | 1418 => 1110111000010
  | 1419 => 1101100011
  | 1420 => 1001100
  | 1421 => 101101011011
  | 1422 => 111110110110
  | 1423 => 10001110101
  | 1424 => 110101010000
  | 1425 => 1100100
  | 1426 => 11000000010
  | 1427 => 11011111101101
  | 1428 => 10011101100
  | 1429 => 10011101001
  | 1430 => 10010
  | 1431 => 11111101101
  | 1432 => 11010111000
  | 1433 => 1101100100011
  | 1434 => 1010000111110110
  | 1435 => 10111010
  | 1436 => 100101011100
  | 1437 => 11001111100101
  | 1438 => 1010000000010
  | 1439 => 110010111
  | 1440 => 11111111100000
  | 1441 => 1111011
  | 1442 => 11101100010
  | 1443 => 10101
  | 1444 => 1110111100
  | 1445 => 11001100010
  | 1446 => 100010110110
  | 1447 => 1001010001
  | 1448 => 1001111000
  | 1449 => 111110101011
  | 1450 => 110110100
  | 1451 => 1010110111011
  | 1452 => 100011110100
  | 1453 => 1000011001101
  | 1454 => 1011000100010
  | 1455 => 1001101110
  | 1456 => 10010000
  | 1457 => 1101110110101
  | 1458 => 1011111110010
  | 1459 => 10010110001
  | 1460 => 1000100
  | 1461 => 11111111001
  | 1462 => 11010110010
  | 1463 => 1000000001
  | 1464 => 100101000
  | 1465 => 1100001110
  | 1466 => 100011011110
  | 1467 => 1010100111111
  | 1468 => 110100
  | 1469 => 1101100010101
  | 1470 => 11000010
  | 1471 => 100111010001
  | 1472 => 110101000000
  | 1473 => 100101010101
  | 1474 => 1101100110
  | 1475 => 1101111100
  | 1476 => 11100111101100
  | 1477 => 110100011
  | 1478 => 1101110
  | 1479 => 111101001
  | 1480 => 111000
  | 1481 => 10010110101
  | 1482 => 101101010010
  | 1483 => 11010010001
  | 1484 => 10011101100
  | 1485 => 11110111111111111110
  | 1486 => 101100010
  | 1487 => 101010011101
  | 1488 => 100000110000
  | 1489 => 111010011111
  | 1490 => 1101110
  | 1491 => 100101000111
  | 1492 => 10101101100
  | 1493 => 10100100101011
  | 1494 => 1001101111110
  | 1495 => 100101011010
  | 1496 => 1001011000
  | 1497 => 1110100100001
  | 1498 => 110111001110110
  | 1499 => 110010111
  | 1500 => 111000
  | 1501 => 1101000011
  | 1502 => 11110001110
  | 1503 => 1001101011111
  | 1504 => 1001100000
  | 1505 => 11010011110
  | 1506 => 11100101010
  | 1507 => 110011
  | 1508 => 1110001100
  | 1509 => 11010100101
  | 1510 => 11100010
  | 1511 => 10110101
  | 1512 => 1010111010111000
  | 1513 => 11010101
  | 1514 => 1011010010110
  | 1515 => 10111110
  | 1516 => 10010110100
  | 1517 => 10001100111
  | 1518 => 111110010
  | 1519 => 10010011011
  | 1520 => 110010000
  | 1521 => 111110101011
  | 1522 => 110111000110
  | 1523 => 10110111101
  | 1524 => 10101110100
  | 1525 => 10010100
  | 1526 => 11100101110
  | 1527 => 100101100011
  | 1528 => 11101111000
  | 1529 => 1010010001
  | 1530 => 101111101110
  | 1531 => 10111001111
  | 1532 => 1101010100
  | 1533 => 11001110001
  | 1534 => 111011001010
  | 1535 => 100011000110
  | 1536 => 111000000000
  | 1537 => 110010011111
  | 1538 => 1000110100010
  | 1539 => 111101101011
  | 1540 => 100100
  | 1541 => 11101011111
  | 1542 => 1010010
  | 1543 => 110010001111
  | 1544 => 11001000
  | 1545 => 11101100010
  | 1546 => 101110000110
  | 1547 => 100111011
  | 1548 => 1111101110100
  | 1549 => 10000110101
  | 1550 => 11101100
  | 1551 => 1001110011
  | 1552 => 111000010000
  | 1553 => 1000011001111
  | 1554 => 101010
  | 1555 => 1010100010
  | 1556 => 101101100
  | 1557 => 1111111011
  | 1558 => 10110010010
  | 1559 => 1101011011
  | 1560 => 10101000
  | 1561 => 1010000001101
  | 1562 => 10011100110
  | 1563 => 1011100011
  | 1564 => 11011100010100
  | 1565 => 110010110
  | 1566 => 10110111010110
  | 1567 => 1000111111
  | 1568 => 110000100000
  | 1569 => 1000100101101
  | 1570 => 101011010110
  | 1571 => 100001111101
  | 1572 => 10100100
  | 1573 => 11011
  | 1574 => 101100011110
  | 1575 => 111101111100
  | 1576 => 1101000101000
  | 1577 => 1001100101
  | 1578 => 1011001001010
  | 1579 => 100001100101
  | 1580 => 1001001100
  | 1581 => 10010011100001
  | 1582 => 1100111101110
  | 1583 => 1100101101
  | 1584 => 1111111111111111110000
  | 1585 => 10000001111110
  | 1586 => 10100100010
  | 1587 => 1011111111111
  | 1588 => 1101000100
  | 1589 => 1011100100101
  | 1590 => 1000110
  | 1591 => 11111100111
  | 1592 => 111000011000
  | 1593 => 1100001111111
  | 1594 => 100011011010
  | 1595 => 1111010010
  | 1596 => 111101111100
  | 1597 => 1001101110111
  | 1598 => 11011011010
  | 1599 => 1101011100111
  | 1600 => 1000000
  | 1601 => 111111001
  | 1602 => 10111111110
  | 1603 => 1110111110101
  | 1604 => 111101100100
  | 1605 => 1101001110
  | 1606 => 1100110
  | 1607 => 101111111011
  | 1608 => 10010001000
  | 1609 => 10001010100011
  | 1610 => 111011110
  | 1611 => 111110011101
  | 1612 => 11100111100
  | 1613 => 1001001100011
  | 1614 => 10101001110
  | 1615 => 110101010
  | 1616 => 1010000
  | 1617 => 10111101
  | 1618 => 111010001110
  | 1619 => 11111001101
  | 1620 => 111111110100
  | 1621 => 100001111
  | 1622 => 10010100010
  | 1623 => 11001111111
  | 1624 => 11010111000
  | 1625 => 1001000
  | 1626 => 1111111111111110
  | 1627 => 1010000100111
  | 1628 => 11111100
  | 1629 => 110101111011
  | 1630 => 10101110
  | 1631 => 10111011001
  | 1632 => 10001100000
  | 1633 => 10100100101
  | 1634 => 1110100000010
  | 1635 => 10010101110
  | 1636 => 110000100100
  | 1637 => 11110111101
  | 1638 => 101011111110
  | 1639 => 1110011111
  | 1640 => 11111000
  | 1641 => 100101
  | 1642 => 100001010110
  | 1643 => 1100000001
  | 1644 => 111011100
  | 1645 => 111100010
  | 1646 => 11000111010
  | 1647 => 111110100111
  | 1648 => 111000010000
  | 1649 => 101001001001
  | 1650 => 11111100
  | 1651 => 1010000011111
  | 1652 => 1110110010100
  | 1653 => 1010011101
  | 1654 => 10001000010010
  | 1655 => 1110111110
  | 1656 => 11011111011000
  | 1657 => 10101110111
  | 1658 => 110000010
  | 1659 => 101011100001
  | 1660 => 10101100
  | 1661 => 1111111001
  | 1662 => 10111011101010
  | 1663 => 101111110101
  | 1664 => 10010000000
  | 1665 => 1111111110
  | 1666 => 10100100010
  | 1667 => 11111110111
  | 1668 => 11011010100
  | 1669 => 110001001101
  | 1670 => 111110110
  | 1671 => 1010100001101
  | 1672 => 100111000
  | 1673 => 101111101
  | 1674 => 111110101110
  | 1675 => 110101100
  | 1676 => 1000111100
  | 1677 => 1010001110001
  | 1678 => 111000111110
  | 1679 => 100011010101
  | 1680 => 101010000
  | 1681 => 101110000001
  | 1682 => 1001100001010
  | 1683 => 1111111111110111111
  | 1684 => 10011001100
  | 1685 => 10110
  | 1686 => 10111001010
  | 1687 => 111011100011
  | 1688 => 110100011000
  | 1689 => 100011110001
  | 1690 => 101111010
  | 1691 => 11010101
  | 1692 => 10011101111100
  | 1693 => 11101001
  | 1694 => 110110
  | 1695 => 10101010110
  | 1696 => 10001100000
  | 1697 => 11000010001
  | 1698 => 100111100010
  | 1699 => 11010011011
  | 1700 => 1110100
  | 1701 => 11010111010101
  | 1702 => 100001010
  | 1703 => 1000000011101
  | 1704 => 10011000
  | 1705 => 110010010
  | 1706 => 10010100010
  | 1707 => 1011010011
  | 1708 => 101001000100
  | 1709 => 1011000101011
  | 1710 => 11110111110
  | 1711 => 101011111011
  | 1712 => 1000100110000
  | 1713 => 1000010001
  | 1714 => 100100111010
  | 1715 => 11000010
  | 1716 => 11111100
  | 1717 => 1001011
  | 1718 => 1011111110110
  | 1719 => 101111011011
  | 1720 => 1101101000
  | 1721 => 10100000001
  | 1722 => 1100101000110
  | 1723 => 111111101
  | 1724 => 10110010100
  | 1725 => 1000010100
  | 1726 => 1100011101010
  | 1727 => 1001110111111
  | 1728 => 1101111111000000
  | 1729 => 1000000001
  | 1730 => 10110011010
  | 1731 => 110111110101
  | 1732 => 1000100100
  | 1733 => 10111010001
  | 1734 => 1010100110010
  | 1735 => 10101111010
  | 1736 => 10000011000
  | 1737 => 110011111101
  | 1738 => 100100110
  | 1739 => 100111011111
  | 1740 => 1101011100
  | 1741 => 1110011111
  | 1742 => 1110011110
  | 1743 => 10100000001
  | 1744 => 10010101110000
  | 1745 => 11001000010
  | 1746 => 1100111011110
  | 1747 => 110000000001
  | 1748 => 1110111100
  | 1749 => 100111011
  | 1750 => 1001000
  | 1751 => 100001100101
  | 1752 => 1110111000
  | 1753 => 100100011101
  | 1754 => 10101110100110
  | 1755 => 10110010111110
  | 1756 => 1000110001100
  | 1757 => 100001101011
  | 1758 => 10011010110
  | 1759 => 11101100011
  | 1760 => 1100000
  | 1761 => 1101011101011
  | 1762 => 1001001010
  | 1763 => 1010010001111
  | 1764 => 1111111010100
  | 1765 => 101011010010
  | 1766 => 11011010
  | 1767 => 1001101100001
  | 1768 => 100111011000
  | 1769 => 10100101111111
  | 1770 => 1001011110
  | 1771 => 10010101101
  | 1772 => 11000000100
  | 1773 => 101111011011
  | 1774 => 110000001110
  | 1775 => 1001100
  | 1776 => 1110000
  | 1777 => 101010011
  | 1778 => 10011100111110
  | 1779 => 10010111001
  | 1780 => 1101010100
  | 1781 => 10011001
  | 1782 => 11111111111111110110
  | 1783 => 1100111
  | 1784 => 1001111001000
  | 1785 => 1001110110
  | 1786 => 1000011110110
  | 1787 => 1001001011111
  | 1788 => 1000011101100
  | 1789 => 11101101011
  | 1790 => 110101110
  | 1791 => 10101110011011
  | 1792 => 100100000000
  | 1793 => 100100011011
  | 1794 => 100101011010
  | 1795 => 10010101110
  | 1796 => 11110011100
  | 1797 => 110000000001
  | 1798 => 111011110010010
  | 1799 => 100111110001
  | 1800 => 111111111000
  | 1801 => 11011010011011
  | 1802 => 1000110
  | 1803 => 11100110001
  | 1804 => 111111111100
  | 1805 => 111011110
  | 1806 => 11100010110
  | 1807 => 1010010001
  | 1808 => 10110110000
  | 1809 => 1010111010111
  | 1810 => 10011110
  | 1811 => 100100111101
  | 1812 => 1000101101100
  | 1813 => 10111101
  | 1814 => 100010110110
  | 1815 => 10001111010
  | 1816 => 11001101000
  | 1817 => 1111010101
  | 1818 => 10111111111111111110
  | 1819 => 101001010011
  | 1820 => 100100
  | 1821 => 1110010000101
  | 1822 => 1010000110010
  | 1823 => 1110001001
  | 1824 => 1100100000
  | 1825 => 1000100
  | 1826 => 11111000010
  | 1827 => 101111100111
  | 1828 => 100110100100
  | 1829 => 1010100001
  | 1830 => 1001010
  | 1831 => 1100010000001
  | 1832 => 10000100011000
  | 1833 => 110100001011
  | 1834 => 101100011110
  | 1835 => 11010
  | 1836 => 11110110101100
  | 1837 => 1100001111
  | 1838 => 10101110100110
  | 1839 => 10110011001
  | 1840 => 1101010000
  | 1841 => 101100100101
  | 1842 => 10111110001110
  | 1843 => 1101101100101
  | 1844 => 11110100
  | 1845 => 1110011110110
  | 1846 => 101001001010
  | 1847 => 101101110011
  | 1848 => 111111000
  | 1849 => 10110001101111
  | 1850 => 11100
  | 1851 => 1010000001
  | 1852 => 11010001100
  | 1853 => 1101111001001
  | 1854 => 1111011011010
  | 1855 => 1001110110
  | 1856 => 1101101000000
  | 1857 => 11010010011
  | 1858 => 11000001010
  | 1859 => 10111101
  | 1860 => 1000001100
  | 1861 => 100111101111
  | 1862 => 1010011000110
  | 1863 => 1101011011011
  | 1864 => 111110011000
  | 1865 => 1010110110
  | 1866 => 111011111010
  | 1867 => 1110111111001
  | 1868 => 10000011100
  | 1869 => 101001001101
  | 1870 => 10010110
  | 1871 => 110101111101
  | 1872 => 101011111110000
  | 1873 => 11000011001
  | 1874 => 101101110010
  | 1875 => 1110000
  | 1876 => 110010000100
  | 1877 => 110110100001
  | 1878 => 11000000010
  | 1879 => 101011111011
  | 1880 => 10011000
  | 1881 => 111111111111111111
  | 1882 => 1000010110
  | 1883 => 10110011001111
  | 1884 => 11011110110100
  | 1885 => 111000110
  | 1886 => 10010011010
  | 1887 => 100011
  | 1888 => 1101111100000
  | 1889 => 110000110101111
  | 1890 => 10101110101110
  | 1891 => 1001011101111
  | 1892 => 11111101100
  | 1893 => 1111101001101
  | 1894 => 10110011010
  | 1895 => 1001011010
  | 1896 => 101010111000
  | 1897 => 1011101
  | 1898 => 100110010
  | 1899 => 1001111001111
  | 1900 => 1100100
  | 1901 => 100010110111
  | 1902 => 10011111010110
  | 1903 => 1011001101
  | 1904 => 1001110110000
  | 1905 => 1010111010
  | 1906 => 1001010110110
  | 1907 => 11011100001
  | 1908 => 1111110110100
  | 1909 => 1001001100011
  | 1910 => 111011110
  | 1911 => 10111101
  | 1912 => 1111111000
  | 1913 => 10010111101
  | 1914 => 1111010010
  | 1915 => 110101010
  | 1916 => 10011100
  | 1917 => 111001111101
  | 1918 => 100110010
  | 1919 => 1111101
  | 1920 => 1110000000
  | 1921 => 1111011101111
  | 1922 => 10100110
  | 1923 => 1011101010111
  | 1924 => 1010100
  | 1925 => 100100
  | 1926 => 1110101110110
  | 1927 => 10100011101011
  | 1928 => 111101000
  | 1929 => 1110110100111
  | 1930 => 110010
  | 1931 => 110011001
  | 1932 => 10110011100
  | 1933 => 101010011011
  | 1934 => 100100001010
  | 1935 => 111110111010
  | 1936 => 110110000
  | 1937 => 101011011101
  | 1938 => 1111011010110
  | 1939 => 101101011101111
  | 1940 => 1110000100
  | 1941 => 10110011001
  | 1942 => 10011010
  | 1943 => 10111101101111
  | 1944 => 100111110111000
  | 1945 => 10110110
  | 1946 => 10100100010
  | 1947 => 100101111
  | 1948 => 110011011100
  | 1949 => 1100111101
  | 1950 => 1010100
  | 1951 => 1101001101001
  | 1952 => 10010100000
  | 1953 => 101010111111
  | 1954 => 10111100010
  | 1955 => 1101110001010
  | 1956 => 10000001100
  | 1957 => 10010100011
  | 1958 => 11001111110
  | 1959 => 10010001110001
  | 1960 => 1100001000
  | 1961 => 100011
  | 1962 => 11111110110
  | 1963 => 1111111001
  | 1964 => 10010101010100
  | 1965 => 1010010
  | 1966 => 110001111010
  | 1967 => 101101111111
  | 1968 => 100011001110000
  | 1969 => 10000110001101
  | 1970 => 11010001010
  | 1971 => 101111001111
  | 1972 => 11110100100
  | 1973 => 1111010111
  | 1974 => 1001010001110
  | 1975 => 1001001100
  | 1976 => 1000000001000
  | 1977 => 1001111111001
  | 1978 => 111110111111010010
  | 1979 => 10000011101111
  | 1980 => 11111111111111111100
  | 1981 => 10000010010011
  | 1982 => 1100010
  | 1983 => 111011011101
  | 1984 => 111011000000
  | 1985 => 110100010
  | 1986 => 10110001110
  | 1987 => 101000110111
  | 1988 => 1100010100
  | 1989 => 1001101111101
  | 1990 => 1110000110
  | 1991 => 11110001001
  | 1992 => 1111100001000
  | 1993 => 1110101
  | 1994 => 1111100000010
  | 1995 => 11110111110
  | 1996 => 1110000001100
  | 1997 => 1000001011101
  | 1998 => 1111111111111111111111111110
  | 1999 => 1111000000111
  | _ => 1

def witness_fast_2 : Nat → Nat
  | 2000 => 10000
  | 2001 => 10001000001
  | 2002 => 10010
  | 2003 => 100001111001
  | 2004 => 10000010100
  | 2005 => 11110110010
  | 2006 => 1111100000010
  | 2007 => 10111011111
  | 2008 => 110001001000
  | 2009 => 100100010101
  | 2010 => 100100010
  | 2011 => 10010010111111
  | 2012 => 110100010100
  | 2013 => 1101111
  | 2014 => 111111101110
  | 2015 => 1110011110
  | 2016 => 111101111100000
  | 2017 => 10011011101001
  | 2018 => 100100011111110
  | 2019 => 100100001
  | 2020 => 10100
  | 2021 => 100001101
  | 2022 => 10110
  | 2023 => 10000000111101
  | 2024 => 11111001000
  | 2025 => 111111110100
  | 2026 => 100001101010
  | 2027 => 10001001111
  | 2028 => 1011110100
  | 2029 => 100111000001
  | 2030 => 110101110
  | 2031 => 10011000010101
  | 2032 => 110100110000
  | 2033 => 100000011101
  | 2034 => 1100111101110
  | 2035 => 1111110
  | 2036 => 10010110001100
  | 2037 => 1110110001
  | 2038 => 11011100010
  | 2039 => 11001011111101
  | 2040 => 100011000
  | 2041 => 1001110001100001
  | 2042 => 100111000110
  | 2043 => 11011110111
  | 2044 => 1001100100
  | 2045 => 11000010010
  | 2046 => 100100110110
  | 2047 => 1000011111011
  | 2048 => 100000000000
  | 2049 => 100000111101
  | 2050 => 1111100
  | 2051 => 10010010101
  | 2052 => 11010111011100
  | 2053 => 1101011001001
  | 2054 => 111010110100110
  | 2055 => 11101110
  | 2056 => 101001000
  | 2057 => 1011001101
  | 2058 => 11000010
  | 2059 => 1001111000101
  | 2060 => 1110000100
  | 2061 => 11110111101
  | 2062 => 10011010
  | 2063 => 1000010011101
  | 2064 => 1001000010000
  | 2065 => 111011001010
  | 2066 => 1110110010110
  | 2067 => 100111011
  | 2068 => 100111001100
  | 2069 => 110110111
  | 2070 => 110111110110
  | 2071 => 1101111001001
  | 2072 => 10101000
  | 2073 => 111111011001
  | 2074 => 10100100010
  | 2075 => 10101100
  | 2076 => 101100110100
  | 2077 => 111001111
  | 2078 => 101010011110
  | 2079 => 1001101101111111111111
  | 2080 => 100100000
  | 2081 => 100010011111
  | 2082 => 101010010110
  | 2083 => 100101100011
  | 2084 => 101011011100
  | 2085 => 1101101010
  | 2086 => 110001111010
  | 2087 => 1001110010111
  | 2088 => 10111101111000
  | 2089 => 100000010111
  | 2090 => 1001110
  | 2091 => 1110001100001
  | 2092 => 11011100110100
  | 2093 => 10010101101
  | 2094 => 10111010011110
  | 2095 => 100011110
  | 2096 => 1010010000
  | 2097 => 1100101011111
  | 2098 => 1000010011110
  | 2099 => 1001011001
  | 2100 => 1010100
  | 2101 => 11110111111
  | 2102 => 10100110
  | 2103 => 111101000001
  | 2104 => 10001101000
  | 2105 => 1001100110
  | 2106 => 10110110111010
  | 2107 => 111000011101
  | 2108 => 110111011100
  | 2109 => 10100001
  | 2110 => 1101000110
  | 2111 => 111100011101
  | 2112 => 111111000000
  | 2113 => 10110001111101
  | 2114 => 11111110010
  | 2115 => 1001110111110
  | 2116 => 100011100100
  | 2117 => 101110001011
  | 2118 => 101011010010
  | 2119 => 100100011011
  | 2120 => 100011000
  | 2121 => 11010111
  | 2122 => 10000111110010
  | 2123 => 1100111001
  | 2124 => 10101111101100
  | 2125 => 11101000
  | 2126 => 100000001101010
  | 2127 => 1001011001001
  | 2128 => 111011110000
  | 2129 => 1011111001001
  | 2130 => 100110
  | 2131 => 10100100111101
  | 2132 => 101110100
  | 2133 => 110011111011
  | 2134 => 111000010
  | 2135 => 10100100010
  | 2136 => 1011111111000
  | 2137 => 1111010001101
  | 2138 => 11000010
  | 2139 => 1100000001
  | 2140 => 10001001100
  | 2141 => 1110011001001
  | 2142 => 1110111110010
  | 2143 => 1001001101101
  | 2144 => 110101100000
  | 2145 => 1111110
  | 2146 => 1000111110
  | 2147 => 1010001000011
  | 2148 => 1101011100
  | 2149 => 10001100011
  | 2150 => 110110100
  | 2151 => 101000011111011
  | 2152 => 100100011000
  | 2153 => 10000011111
  | 2154 => 10010101110
  | 2155 => 1011001010
  | 2156 => 1011110100
  | 2157 => 101000000001
  | 2158 => 101000000010
  | 2159 => 1001110011111
  | 2160 => 11011111110000
  | 2161 => 10110111001
  | 2162 => 10100010010
  | 2163 => 1110110001
  | 2164 => 1010101100
  | 2165 => 100010010
  | 2166 => 1101110110110
  | 2167 => 11010100101
  | 2168 => 11111000
  | 2169 => 1001011110111
  | 2170 => 100000110
  | 2171 => 100100101101
  | 2172 => 1111000100100
  | 2173 => 10011011
  | 2174 => 100010011110
  | 2175 => 1101011100
  | 2176 => 111010000000
  | 2177 => 101111011001
  | 2178 => 100111111111111111110
  | 2179 => 100100011111
  | 2180 => 100101011100
  | 2181 => 110100001011
  | 2182 => 1000001010110
  | 2183 => 101110011
  | 2184 => 10101000
  | 2185 => 111011110
  | 2186 => 1111111010
  | 2187 => 1001011011111
  | 2188 => 10010100
  | 2189 => 10001101011
  | 2190 => 11101110
  | 2191 => 11001011
  | 2192 => 100010000
  | 2193 => 1101011001
  | 2194 => 11110010110
  | 2195 => 100011000110
  | 2196 => 11101101110100
  | 2197 => 1100110100011
  | 2198 => 100101111111111110
  | 2199 => 11100110001
  | 2200 => 11000
  | 2201 => 10010011100001
  | 2202 => 11010
  | 2203 => 11000101111
  | 2204 => 101001110100
  | 2205 => 111111101010
  | 2206 => 11101000110
  | 2207 => 11111110101011
  | 2208 => 1000010100000
  | 2209 => 111000111001001
  | 2210 => 1001110110
  | 2211 => 110110011
  | 2212 => 11000110100
  | 2213 => 100010000011
  | 2214 => 11010111001110
  | 2215 => 1100000010
  | 2216 => 110111101000
  | 2217 => 1000101011001
  | 2218 => 11000101011010
  | 2219 => 1000110110111
  | 2220 => 11100
  | 2221 => 1000001010111
  | 2222 => 11110
  | 2223 => 1011100110111
  | 2224 => 1101101010000
  | 2225 => 1101010100
  | 2226 => 1001110110
  | 2227 => 1111000110101
  | 2228 => 111010100
  | 2229 => 1111011100101
  | 2230 => 10011110010
  | 2231 => 100010110111
  | 2232 => 11111010111000
  | 2233 => 11111111011
  | 2234 => 110111101010
  | 2235 => 100001110110
  | 2236 => 11001111000100
  | 2237 => 110000001
  | 2238 => 1010110110
  | 2239 => 101111001
  | 2240 => 1001000000
  | 2241 => 100110111111
  | 2242 => 1001000100010
  | 2243 => 10111011101
  | 2244 => 10011101100
  | 2245 => 1111001110
  | 2246 => 1000110110
  | 2247 => 11111111010111
  | 2248 => 101000111000
  | 2249 => 1011100110111
  | 2250 => 111111111000
  | 2251 => 101101101111
  | 2252 => 110100111100
  | 2253 => 111001000011
  | 2254 => 1101000110
  | 2255 => 11111111110
  | 2256 => 100110000
  | 2257 => 110010001101
  | 2258 => 1000000110010
  | 2259 => 110100111111
  | 2260 => 101101100
  | 2261 => 1000101010111
  | 2262 => 1011100100010
  | 2263 => 100010110011
  | 2264 => 10010111011000
  | 2265 => 100010110110
  | 2266 => 111000010
  | 2267 => 111011111011111
  | 2268 => 101101101110100
  | 2269 => 1111000010111
  | 2270 => 110011010
  | 2271 => 111001100001
  | 2272 => 1001100000
  | 2273 => 101100101011
  | 2274 => 1001110001010
  | 2275 => 100100
  | 2276 => 101101001100
  | 2277 => 11110111111111111011
  | 2278 => 111101010010
  | 2279 => 1001001111101
  | 2280 => 11001000
  | 2281 => 10010011111
  | 2282 => 1001000110110
  | 2283 => 10100001011001
  | 2284 => 100001000100
  | 2285 => 10011010010
  | 2286 => 111111110010
  | 2287 => 100000111011
  | 2288 => 10010000
  | 2289 => 101001001101
  | 2290 => 100001000110
  | 2291 => 10000011101
  | 2292 => 1000000001100
  | 2293 => 1101000001
  | 2294 => 1110101010
  | 2295 => 1111011010110
  | 2296 => 1011101000
  | 2297 => 10011011110111
  | 2298 => 101001110010
  | 2299 => 11000000011
  | 2300 => 11010100
  | 2301 => 111110000001
  | 2302 => 1101000111110
  | 2303 => 11000000001011
  | 2304 => 11111111100000000
  | 2305 => 1111010
  | 2306 => 1001000010
  | 2307 => 1101000000111
  | 2308 => 11000101100
  | 2309 => 10111111
  | 2310 => 1111110
  | 2311 => 10011000101
  | 2312 => 1100110001000
  | 2313 => 110110011111
  | 2314 => 111110100010
  | 2315 => 1101000110
  | 2316 => 1100100
  | 2317 => 10010011101111
  | 2318 => 100010110
  | 2319 => 10111000011
  | 2320 => 11011010000
  | 2321 => 111111100001
  | 2322 => 1010111111010
  | 2323 => 10101001011
  | 2324 => 1010000000100
  | 2325 => 1000001100
  | 2326 => 10011010111010
  | 2327 => 11101100101
  | 2328 => 100110111000
  | 2329 => 10011111011
  | 2330 => 1111100110
  | 2331 => 10101111111
  | 2332 => 100101100
  | 2333 => 111001100101
  | 2334 => 110101000110
  | 2335 => 1000001110
  | 2336 => 1000100000
  | 2337 => 11100111001101
  | 2338 => 1001001011010
  | 2339 => 100011100001
  | 2340 => 1010111111100
  | 2341 => 1011010011
  | 2342 => 1000101110010
  | 2343 => 1001110011
  | 2344 => 110000111000
  | 2345 => 11001000010
  | 2346 => 10111111111110
  | 2347 => 10011011110101
  | 2348 => 1001011100
  | 2349 => 1011011101011
  | 2350 => 1001100
  | 2351 => 101111011011
  | 2352 => 11000010000
  | 2353 => 1011101011011
  | 2354 => 1101001110
  | 2355 => 1101111011010
  | 2356 => 1101100101100
  | 2357 => 11100110011
  | 2358 => 10011001111110
  | 2359 => 101110111011
  | 2360 => 11011111000
  | 2361 => 100010100101001
  | 2362 => 1010100100010
  | 2363 => 1010010001
  | 2364 => 1101010010100
  | 2365 => 1111110110
  | 2366 => 101111010
  | 2367 => 111010011111
  | 2368 => 111000000
  | 2369 => 10000011000011
  | 2370 => 1010101110
  | 2371 => 100011011111
  | 2372 => 100100001100
  | 2373 => 110011110111
  | 2374 => 1000100001010
  | 2375 => 11001000
  | 2376 => 1111011111111111111000
  | 2377 => 1000010111101
  | 2378 => 1000100110010
  | 2379 => 110010001101
  | 2380 => 10011101100
  | 2381 => 11101010111
  | 2382 => 110001010110
  | 2383 => 101010001101
  | 2384 => 1101110000
  | 2385 => 111111011010
  | 2386 => 110111001010
  | 2387 => 10010011011
  | 2388 => 110001011100
  | 2389 => 111110001
  | 2390 => 11111110
  | 2391 => 10001101101
  | 2392 => 10010101101000
  | 2393 => 10110011011
  | 2394 => 11110111110
  | 2395 => 1001110
  | 2396 => 1010111011100
  | 2397 => 100010110101
  | 2398 => 11111001110
  | 2399 => 111010100111
  | 2400 => 11100000
  | 2401 => 1101101001
  | 2402 => 101111001010
  | 2403 => 110011111011
  | 2404 => 1100101111100
  | 2405 => 101010
  | 2406 => 1010001110010
  | 2407 => 1011000110011
  | 2408 => 1101001111000
  | 2409 => 11001111111111
  | 2410 => 1111010
  | 2411 => 1000111011111
  | 2412 => 111111011100
  | 2413 => 110001011010111
  | 2414 => 1111101110110
  | 2415 => 1011001110
  | 2416 => 11100010000
  | 2417 => 10001010110011
  | 2418 => 100100110110
  | 2419 => 1000000011011
  | 2420 => 1101100
  | 2421 => 1101010011111
  | 2422 => 10111001101110
  | 2423 => 1110100011111
  | 2424 => 1011111000
  | 2425 => 1110000100
  | 2426 => 1110001101110
  | 2427 => 100010100111
  | 2428 => 100101101010100
  | 2429 => 11101100011001
  | 2430 => 1001111101110
  | 2431 => 100111011
  | 2432 => 110010000000
  | 2433 => 10011101101101
  | 2434 => 1010110
  | 2435 => 11001101110
  | 2436 => 1101011100
  | 2437 => 101000010111
  | 2438 => 11000000010
  | 2439 => 10000101011110111101111111
  | 2440 => 100101000
  | 2441 => 10000111000001
  | 2442 => 1111110
  | 2443 => 1100100001
  | 2444 => 110010000100
  | 2445 => 1000000110
  | 2446 => 1001111110
  | 2447 => 1000001011101
  | 2448 => 101111101110000
  | 2449 => 111110001011
  | 2450 => 110000100
  | 2451 => 1000110111111
  | 2452 => 11000101100
  | 2453 => 1001111001
  | 2454 => 111000101010
  | 2455 => 1001010101010
  | 2456 => 10001100011000
  | 2457 => 1011001011111
  | 2458 => 1000011110010
  | 2459 => 101010011011011
  | 2460 => 1000110011100
  | 2461 => 1111100010001
  | 2462 => 1000011110010
  | 2463 => 1011011001111
  | 2464 => 100100000
  | 2465 => 1111010010
  | 2466 => 101101001011110
  | 2467 => 1010111011111
  | 2468 => 110011100
  | 2469 => 1100011101
  | 2470 => 10000000010
  | 2471 => 110000101001
  | 2472 => 1110110001000
  | 2473 => 111100111101
  | 2474 => 101100010
  | 2475 => 11111111111111111100
  | 2476 => 1101001001100
  | 2477 => 110011001
  | 2478 => 1111100000010
  | 2479 => 1111110111
  | 2480 => 1110110000
  | 2481 => 1000111000101
  | 2482 => 100111110110
  | 2483 => 10010000011011
  | 2484 => 10100111111100
  | 2485 => 110001010
  | 2486 => 1001101100010
  | 2487 => 11000001
  | 2488 => 101010001000
  | 2489 => 10011100011001
  | 2490 => 11111000010
  | 2491 => 10110000001
  | 2492 => 110100111100
  | 2493 => 1011101110101
  | 2494 => 11011010
  | 2495 => 111000000110
  | 2496 => 10101000000
  | 2497 => 100011000111
  | 2498 => 1111001100010
  | 2499 => 11111110000011
  | 2500 => 10000
  | 2501 => 1110000100011
  | 2502 => 1001111011110
  | 2503 => 10111000000111
  | 2504 => 11001011000
  | 2505 => 1000001010
  | 2506 => 110101110
  | 2507 => 11100101001
  | 2508 => 11110001100
  | 2509 => 1011100101011
  | 2510 => 1100010010
  | 2511 => 1100111011101
  | 2512 => 101011010110000
  | 2513 => 101000101111
  | 2514 => 1111100010
  | 2515 => 11010001010
  | 2516 => 10001100
  | 2517 => 111100010001
  | 2518 => 1000011110
  | 2519 => 10000100011
  | 2520 => 1111011111000
  | 2521 => 1001111010011
  | 2522 => 11101100010
  | 2523 => 110001001101
  | 2524 => 10101111100
  | 2525 => 10100
  | 2526 => 1010101010010
  | 2527 => 11101111
  | 2528 => 1001001100000
  | 2529 => 111011110011
  | 2530 => 111110010
  | 2531 => 101101000011
  | 2532 => 11000101001100
  | 2533 => 10010001011011
  | 2534 => 1010111100110
  | 2535 => 101111010
  | 2536 => 1000000111111000
  | 2537 => 111000100111
  | 2538 => 1111011010110
  | 2539 => 1100100101001
  | 2540 => 1101001100
  | 2541 => 1111110111111
  | 2542 => 10010010010010
  | 2543 => 10000111001
  | 2544 => 1000110000
  | 2545 => 1001011000110
  | 2546 => 1011110000010
  | 2547 => 1101111101001
  | 2548 => 1011110100
  | 2549 => 1110111011011
  | 2550 => 10001100
  | 2551 => 10000100001111
  | 2552 => 111101001000
  | 2553 => 10000101
  | 2554 => 10110101110010
  | 2555 => 100110010
  | 2556 => 10011101111100
  | 2557 => 1001101101111
  | 2558 => 10010100010110
  | 2559 => 1101000100011
  | 2560 => 1000000000
  | 2561 => 11010100101
  | 2562 => 1100100011010
  | 2563 => 1001100111
  | 2564 => 111000111100
  | 2565 => 1101011101110
  | 2566 => 11110100010
  | 2567 => 101001010011
  | 2568 => 110100111000
  | 2569 => 110111011101
  | 2570 => 1010010
  | 2571 => 10010011101
  | 2572 => 1001100010100
  | 2573 => 100100010011
  | 2574 => 1111111111111111110
  | 2575 => 1110000100
  | 2576 => 111011110000
  | 2577 => 1110101101011
  | 2578 => 101001000010
  | 2579 => 1000010110111
  | 2580 => 10010000100
  | 2581 => 11111001101
  | 2582 => 101110100110
  | 2583 => 111001111011
  | 2584 => 11010101000
  | 2585 => 10011100110
  | 2586 => 1010101000110
  | 2587 => 10101001001
  | 2588 => 1011001100100
  | 2589 => 1010001001011
  | 2590 => 101010
  | 2591 => 1100000010001
  | 2592 => 111111110100000
  | 2593 => 10110110000101
  | 2594 => 110000000111110
  | 2595 => 10110011010
  | 2596 => 10010111100
  | 2597 => 1000100111101
  | 2598 => 100010010
  | 2599 => 1011011
  | 2600 => 1001000
  | 2601 => 1101111010011
  | 2602 => 110010101110
  | 2603 => 101010110001
  | 2604 => 1000001100
  | 2605 => 10101101110
  | 2606 => 11011101010110
  | 2607 => 101110000101
  | 2608 => 10101110000
  | 2609 => 1000001001
  | 2610 => 101111011110
  | 2611 => 10111100111
  | 2612 => 1110100
  | 2613 => 101111110111011
  | 2614 => 1101101010010
  | 2615 => 1101110011010
  | 2616 => 1001010111000
  | 2617 => 1010001010011
  | 2618 => 1001110110
  | 2619 => 1011101011011
  | 2620 => 10100100
  | 2621 => 1100010111
  | 2622 => 1100111111010
  | 2623 => 10100011011
  | 2624 => 11111000000
  | 2625 => 10101000
  | 2626 => 1011010
  | 2627 => 100111011111
  | 2628 => 10111100111100
  | 2629 => 11111111111111
  | 2630 => 100011010
  | 2631 => 1111011000111
  | 2632 => 11110001000
  | 2633 => 10100101111
  | 2634 => 101000111010
  | 2635 => 11011101110
  | 2636 => 1111010011100
  | 2637 => 1101100111101
  | 2638 => 1100010110010
  | 2639 => 1010101001
  | 2640 => 1111110000
  | 2641 => 1001100101
  | 2642 => 100011100111110
  | 2643 => 10111000011
  | 2644 => 10100010000100
  | 2645 => 10001110010
  | 2646 => 11000111111010
  | 2647 => 1010010001011
  | 2648 => 111011111000
  | 2649 => 10010100111111
  | 2650 => 10001100
  | 2651 => 1001000000011
  | 2652 => 10011101100
  | 2653 => 100111000101
  | 2654 => 11110111011110
  | 2655 => 1010111110110
  | 2656 => 10101100000
  | 2657 => 1001000101011
  | 2658 => 1100000010
  | 2659 => 11111001101
  | 2660 => 1110111100
  | 2661 => 1111011010011
  | 2662 => 11011110110
  | 2663 => 1011111000111
  | 2664 => 111111111000
  | 2665 => 10111010
  | 2666 => 10100101010
  | 2667 => 1001110011111
  | 2668 => 111011011100
  | 2669 => 1101001011001
  | 2670 => 10111111110
  | 2671 => 1101001000011
  | 2672 => 111110110000
  | 2673 => 1111111111111111011
  | 2674 => 111011110
  | 2675 => 10001001100
  | 2676 => 100111100100
  | 2677 => 1110100001001
  | 2678 => 11101100010
  | 2679 => 101111110011
  | 2680 => 1101011000
  | 2681 => 1110011001001
  | 2682 => 101111011110
  | 2683 => 1011000011
  | 2684 => 110111100
  | 2685 => 110101110
  | 2686 => 1100011010
  | 2687 => 10000001001
  | 2688 => 101010000000
  | 2689 => 10111111110111
  | 2690 => 1001000110
  | 2691 => 111110101011
  | 2692 => 10010000100
  | 2693 => 1000000111011
  | 2694 => 11011101110010
  | 2695 => 101111010
  | 2696 => 1011000
  | 2697 => 11101111001001
  | 2698 => 1011111100110
  | 2699 => 10011101111
  | 2700 => 110111111100
  | 2701 => 1110111
  | 2702 => 1010111100110
  | 2703 => 100011
  | 2704 => 101111010000
  | 2705 => 101010110
  | 2706 => 100111000110
  | 2707 => 111000110001
  | 2708 => 100101011010100
  | 2709 => 1011110110101
  | 2710 => 111110
  | 2711 => 110011000101
  | 2712 => 1010101011000
  | 2713 => 1111101011
  | 2714 => 11011010110
  | 2715 => 111100010010
  | 2716 => 111011000100
  | 2717 => 1000000001
  | 2718 => 111111011010
  | 2719 => 1001111000001
  | 2720 => 1110100000
  | 2721 => 10001011011
  | 2722 => 11101010110
  | 2723 => 101011011101
  | 2724 => 1101111011100
  | 2725 => 100101011100
  | 2726 => 1101000010110
  | 2727 => 1011111111111111111
  | 2728 => 11001001000
  | 2729 => 10011111000001
  | 2730 => 101010
  | 2731 => 10110110111
  | 2732 => 10000011110100
  | 2733 => 10001001000111
  | 2734 => 111010010010
  | 2735 => 1001010
  | 2736 => 11110111110000
  | 2737 => 10001101111001
  | 2738 => 101001110010
  | 2739 => 1111100001
  | 2740 => 1000100
  | 2741 => 111001101111
  | 2742 => 1011010100010
  | 2743 => 1001111001111
  | 2744 => 1100001000
  | 2745 => 1110110111010
  | 2746 => 1001111101010
  | 2747 => 101000001101
  | 2748 => 1111011110100
  | 2749 => 11000010101001
  | 2750 => 11000
  | 2751 => 1010011111011
  | 2752 => 1101101000000
  | 2753 => 101000101111
  | 2754 => 1111011010110
  | 2755 => 10100111010
  | 2756 => 10011101100
  | 2757 => 10111011111111
  | 2758 => 110101001010
  | 2759 => 1101110110101
  | 2760 => 10000101000
  | 2761 => 110001001
  | 2762 => 10000111010
  | 2763 => 1011111000111
  | 2764 => 1001011000100
  | 2765 => 1100011010
  | 2766 => 11010001000110
  | 2767 => 111110000101
  | 2768 => 10110011010000
  | 2769 => 1000111100001
  | 2770 => 1101111010
  | 2771 => 101011101010111
  | 2772 => 11111111111111111100
  | 2773 => 10110100111
  | 2774 => 1010101100010
  | 2775 => 11100
  | 2776 => 1010111101000
  | 2777 => 111110111011
  | 2778 => 1110111010110
  | 2779 => 101000001011
  | 2780 => 11011010100
  | 2781 => 1011010110111
  | 2782 => 110101111100110
  | 2783 => 100000000001
  | 2784 => 1101011100000
  | 2785 => 11101010
  | 2786 => 101010010010
  | 2787 => 10100111001111
  | 2788 => 1001101100
  | 2789 => 10001000101001
  | 2790 => 111110101110
  | 2791 => 101111011111
  | 2792 => 1100100001000
  | 2793 => 101001100011
  | 2794 => 1000001001010
  | 2795 => 1100111100010
  | 2796 => 100110011100
  | 2797 => 1110001010001
  | 2798 => 1000110111010
  | 2799 => 11101111101
  | 2800 => 10010000
  | 2801 => 110110111
  | 2802 => 100110010110
  | 2803 => 1010110010001
  | 2804 => 1011011011100
  | 2805 => 1001110110
  | 2806 => 1011100010
  | 2807 => 11010101011
  | 2808 => 1011001011111000
  | 2809 => 110000100111
  | 2810 => 1010001110
  | 2811 => 1001001010101
  | 2812 => 1010000100
  | 2813 => 1011110000001
  | 2814 => 10000011101010
  | 2815 => 11010011110
  | 2816 => 1100000000
  | 2817 => 1000111011111
  | 2818 => 1000101000010
  | 2819 => 11111001111
  | 2820 => 1001100
  | 2821 => 10010011011
  | 2822 => 1001000100110
  | 2823 => 10011000111111
  | 2824 => 10101101001000
  | 2825 => 101101100
  | 2826 => 1101111011010
  | 2827 => 1111011
  | 2828 => 10110100
  | 2829 => 11100111001101
  | 2830 => 100101110110
  | 2831 => 1010101001001
  | 2832 => 1001011110000
  | 2833 => 101011010110011
  | 2834 => 1010010011010
  | 2835 => 10110110111010
  | 2836 => 11101110000100
  | 2837 => 1111011111001
  | 2838 => 11011000110
  | 2839 => 111011001011
  | 2840 => 10011000
  | 2841 => 1011001101
  | 2842 => 1011010110110
  | 2843 => 111100110111
  | 2844 => 1111101101100
  | 2845 => 10110100110
  | 2846 => 100011101010
  | 2847 => 1000001100111
  | 2848 => 1101010100000
  | 2849 => 111111
  | 2850 => 1100100
  | 2851 => 1011110001
  | 2852 => 110000000100
  | 2853 => 1001111101011
  | 2854 => 110111111011010
  | 2855 => 10000100010
  | 2856 => 100111011000
  | 2857 => 111001001101
  | 2858 => 100111010010
  | 2859 => 101010011001
  | 2860 => 100100
  | 2861 => 100101100011
  | 2862 => 111111011010
  | 2863 => 1011111100111
  | 2864 => 110101110000
  | 2865 => 100000000110
  | 2866 => 11011001000110
  | 2867 => 1110111001
  | 2868 => 10100001111101100
  | 2869 => 1100110100001
  | 2870 => 10111010
  | 2871 => 1111011111111111111
  | 2872 => 1001010111000
  | 2873 => 1011000101111
  | 2874 => 110011111001010
  | 2875 => 110101000
  | 2876 => 10100000000100
  | 2877 => 11001110001
  | 2878 => 1100101110
  | 2879 => 1000101000011
  | 2880 => 111111111000000
  | 2881 => 10100011011
  | 2882 => 11110110
  | 2883 => 1100000001
  | 2884 => 111011000100
  | 2885 => 1100010110
  | 2886 => 101010
  | 2887 => 1100100011
  | 2888 => 11101111000
  | 2889 => 111010111011
  | 2890 => 11001100010
  | 2891 => 10100001101001
  | 2892 => 1000101101100
  | 2893 => 10001101
  | 2894 => 10010100010
  | 2895 => 110010
  | 2896 => 10011110000
  | 2897 => 11011100111
  | 2898 => 1111101010110
  | 2899 => 1010000001101
  | 2900 => 110110100
  | 2901 => 11011001110011
  | 2902 => 10101101110110
  | 2903 => 111110110011
  | 2904 => 1000111101000
  | 2905 => 101000000010
  | 2906 => 10000110011010
  | 2907 => 111101101011
  | 2908 => 10110001000100
  | 2909 => 10001110001
  | 2910 => 1001101110
  | 2911 => 10110011001011
  | 2912 => 100100000
  | 2913 => 11010110100111
  | 2914 => 11011101101010
  | 2915 => 10010110
  | 2916 => 10111111100100
  | 2917 => 1001011001101
  | 2918 => 100101100010
  | 2919 => 100111101111
  | 2920 => 10001000
  | 2921 => 101011101
  | 2922 => 111111110010
  | 2923 => 101010111
  | 2924 => 110101100100
  | 2925 => 1010111111100
  | 2926 => 10000000010
  | 2927 => 10000010011111
  | 2928 => 1001010000
  | 2929 => 11010111
  | 2930 => 1100001110
  | 2931 => 1011110001
  | 2932 => 1000110111100
  | 2933 => 1110101101011
  | 2934 => 10101001111110
  | 2935 => 100101110
  | 2936 => 1101000
  | 2937 => 101001001101
  | 2938 => 11011000101010
  | 2939 => 10110010111
  | 2940 => 110000100
  | 2941 => 1011001101
  | 2942 => 1001110100010
  | 2943 => 110111100111
  | 2944 => 1101010000000
  | 2945 => 110110010110
  | 2946 => 1001010101010
  | 2947 => 100011110101
  | 2948 => 11011001100
  | 2949 => 110010111011001
  | 2950 => 1101111100
  | 2951 => 1011100100101
  | 2952 => 111001111011000
  | 2953 => 110110110011111
  | 2954 => 1101000110
  | 2955 => 110101001010
  | 2956 => 11011100
  | 2957 => 100000101001
  | 2958 => 1111010010
  | 2959 => 100100011
  | 2960 => 1110000
  | 2961 => 1100111111001
  | 2962 => 100101101010
  | 2963 => 1001011111001
  | 2964 => 1011010100100
  | 2965 => 10010000110
  | 2966 => 110100100010
  | 2967 => 11111101110101001
  | 2968 => 100111011000
  | 2969 => 11001110011101
  | 2970 => 11110111111111111110
  | 2971 => 1110100011011
  | 2972 => 1011000100
  | 2973 => 110001
  | 2974 => 1010100111010
  | 2975 => 10011101100
  | 2976 => 1000001100000
  | 2977 => 10010100111011
  | 2978 => 1110100111110
  | 2979 => 11111101011
  | 2980 => 11011100
  | 2981 => 1111111111
  | 2982 => 1001010001110
  | 2983 => 10000111110011
  | 2984 => 101011011000
  | 2985 => 11000101110
  | 2986 => 101001001010110
  | 2987 => 100101010101
  | 2988 => 10011011111100
  | 2989 => 1010010001
  | 2990 => 100101011010
  | 2991 => 111110000001
  | 2992 => 10010110000
  | 2993 => 1010001100011
  | 2994 => 11101001000010
  | 2995 => 101011101110
  | 2996 => 1101110011101100
  | 2997 => 1111110111111111111111111111
  | 2998 => 1100101110
  | 2999 => 101000010101001
  | _ => 1

def witness_fast_3 : Nat → Nat
  | 3000 => 111000
  | 3001 => 11001000111111
  | 3002 => 11010000110
  | 3003 => 111111
  | 3004 => 111100011100
  | 3005 => 110010111110
  | 3006 => 10011010111110
  | 3007 => 10101111011111
  | 3008 => 10011000000
  | 3009 => 111110000001
  | 3010 => 11010011110
  | 3011 => 1010001111111
  | 3012 => 111001010100
  | 3013 => 10000001011111
  | 3014 => 1100110
  | 3015 => 11111101110
  | 3016 => 11100011000
  | 3017 => 111001111011
  | 3018 => 110101001010
  | 3019 => 1000101111
  | 3020 => 111000100
  | 3021 => 101111000001
  | 3022 => 101101010
  | 3023 => 10000101101111
  | 3024 => 10101110101110000
  | 3025 => 1101100
  | 3026 => 110101010
  | 3027 => 10010001111111
  | 3028 => 10110100101100
  | 3029 => 10111011001
  | 3030 => 10111110
  | 3031 => 1010101000111
  | 3032 => 100101101000
  | 3033 => 101110111011
  | 3034 => 100011001110
  | 3035 => 10010110101010
  | 3036 => 1111100100
  | 3037 => 10011011011011
  | 3038 => 100100110110
  | 3039 => 101001010011
  | 3040 => 1100100000
  | 3041 => 110101111001
  | 3042 => 1111101010110
  | 3043 => 1110000000101
  | 3044 => 1101110001100
  | 3045 => 110101110
  | 3046 => 101101111010
  | 3047 => 11110011011
  | 3048 => 101011101000
  | 3049 => 101100111001
  | 3050 => 10010100
  | 3051 => 1010110011111
  | 3052 => 111001011100
  | 3053 => 111000110001
  | 3054 => 1001011000110
  | 3055 => 11001000010
  | 3056 => 111011110000
  | 3057 => 1101110001
  | 3058 => 10100100010
  | 3059 => 11101111
  | 3060 => 1011111011100
  | 3061 => 110100010101
  | 3062 => 101110011110
  | 3063 => 10011100011
  | 3064 => 11010101000
  | 3065 => 1100010110
  | 3066 => 110011100010
  | 3067 => 110000111101
  | 3068 => 1110110010100
  | 3069 => 11111011110111111111
  | 3070 => 100011000110
  | 3071 => 10100000001
  | 3072 => 1110000000000
  | 3073 => 10001100011
  | 3074 => 1100100111110
  | 3075 => 1000110011100
  | 3076 => 10001101000100
  | 3077 => 1100010001101
  | 3078 => 1111011010110
  | 3079 => 1100110101111
  | 3080 => 1001000
  | 3081 => 11101011010011
  | 3082 => 111010111110
  | 3083 => 111001001011
  | 3084 => 10100100
  | 3085 => 11001110
  | 3086 => 1100100011110
  | 3087 => 11111110101
  | 3088 => 110010000
  | 3089 => 1011001000101
  | 3090 => 11101100010
  | 3091 => 1011100101
  | 3092 => 1011100001100
  | 3093 => 101000100111111
  | 3094 => 1001110110
  | 3095 => 110100100110
  | 3096 => 11111011101000
  | 3097 => 100111001111101
  | 3098 => 100001101010
  | 3099 => 1101000011001
  | 3100 => 11101100
  | 3101 => 110011110111
  | 3102 => 10011100110
  | 3103 => 10010001110001
  | 3104 => 1110000100000
  | 3105 => 1010011111110
  | 3106 => 10000110011110
  | 3107 => 101111101
  | 3108 => 1010100
  | 3109 => 1000100011
  | 3110 => 1010100010
  | 3111 => 1010011010001
  | 3112 => 1011011000
  | 3113 => 10100100100101
  | 3114 => 11111110110
  | 3115 => 11010011110
  | 3116 => 101100100100
  | 3117 => 100110101001
  | 3118 => 11010110110
  | 3119 => 11011010001101
  | 3120 => 101010000
  | 3121 => 11101101101111
  | 3122 => 10100000011010
  | 3123 => 1101011111001
  | 3124 => 100111001100
  | 3125 => 100000
  | 3126 => 10111000110
  | 3127 => 1000000100101
  | 3128 => 110111000101000
  | 3129 => 10000001010111
  | 3130 => 110010110
  | 3131 => 1010001111
  | 3132 => 101101110101100
  | 3133 => 100101110110001
  | 3134 => 10001111110
  | 3135 => 1111000110
  | 3136 => 1100001000000
  | 3137 => 10000110101111
  | 3138 => 10001001011010
  | 3139 => 1101001111
  | 3140 => 1010110101100
  | 3141 => 1011101001111
  | 3142 => 1000011111010
  | 3143 => 10110110101
  | 3144 => 101001000
  | 3145 => 1000110
  | 3146 => 110110
  | 3147 => 100001001111
  | 3148 => 1011000111100
  | 3149 => 1100100001
  | 3150 => 111101111100
  | 3151 => 100011010101
  | 3152 => 11010001010000
  | 3153 => 11111101111101
  | 3154 => 10011001010
  | 3155 => 1010111110
  | 3156 => 10110010010100
  | 3157 => 11010110111
  | 3158 => 1000011001010
  | 3159 => 1100111101011
  | 3160 => 10010011000
  | 3161 => 10110000000111
  | 3162 => 100100111000010
  | 3163 => 1100111001111
  | 3164 => 11001111011100
  | 3165 => 1100010100110
  | 3166 => 11001011010
  | 3167 => 1110111101001
  | 3168 => 11111111111111111100000
  | 3169 => 100000001001111
  | 3170 => 10000001111110
  | 3171 => 11001100011111
  | 3172 => 101001000100
  | 3173 => 11010110101
  | 3174 => 10111111111110
  | 3175 => 1101001100
  | 3176 => 11010001000
  | 3177 => 11101001101011
  | 3178 => 10111001001010
  | 3179 => 1000010111111
  | 3180 => 10001100
  | 3181 => 110000001101
  | 3182 => 111111001110
  | 3183 => 1111101100101
  | 3184 => 1110000110000
  | 3185 => 101111010
  | 3186 => 11000011111110
  | 3187 => 1001110001
  | 3188 => 1000110110100
  | 3189 => 11111011111011
  | 3190 => 1111010010
  | 3191 => 110010111111
  | 3192 => 1111011111000
  | 3193 => 1001011110101
  | 3194 => 10011011101110
  | 3195 => 1001110111110
  | 3196 => 110110110100
  | 3197 => 100001000010111
  | 3198 => 11010111001110
  | 3199 => 11010010101111
  | 3200 => 10000000
  | 3201 => 1110110001
  | 3202 => 1111110010
  | 3203 => 10010011010101
  | 3204 => 101111111100
  | 3205 => 11100011110
  | 3206 => 11101111101010
  | 3207 => 1100001
  | 3208 => 1111011001000
  | 3209 => 111101000001
  | 3210 => 1101001110
  | 3211 => 1001000001001
  | 3212 => 11001100
  | 3213 => 1101001110111
  | 3214 => 1011111110110
  | 3215 => 100110001010
  | 3216 => 100100010000
  | 3217 => 101010110101
  | 3218 => 100010101000110
  | 3219 => 100011111
  | 3220 => 1110111100
  | 3221 => 1111110011111
  | 3222 => 1111100111010
  | 3223 => 110110111111
  | 3224 => 111001111000
  | 3225 => 10010000100
  | 3226 => 10010011000110
  | 3227 => 1101000100011
  | 3228 => 101010011100
  | 3229 => 10001100011011111
  | 3230 => 110101010
  | 3231 => 110101110111
  | 3232 => 10100000
  | 3233 => 100011111110101
  | 3234 => 101111010
  | 3235 => 101100110010
  | 3236 => 1110100011100
  | 3237 => 10100000001
  | 3238 => 111110011010
  | 3239 => 10000000010111
  | 3240 => 1111111101000
  | 3241 => 110100011
  | 3242 => 1000011110
  | 3243 => 100111011111
  | 3244 => 100101000100
  | 3245 => 1001011110
  | 3246 => 110011111110
  | 3247 => 111001010111
  | 3248 => 110101110000
  | 3249 => 110111011011
  | 3250 => 1001000
  | 3251 => 10001000100001
  | 3252 => 11111111111111100
  | 3253 => 1101010110001
  | 3254 => 10100001001110
  | 3255 => 100000110
  | 3256 => 111111000
  | 3257 => 10011011111111011011
  | 3258 => 1101011110110
  | 3259 => 10000010111
  | 3260 => 101011100
  | 3261 => 10001001111
  | 3262 => 101110110010
  | 3263 => 10001110000011
  | 3264 => 100011000000
  | 3265 => 111010
  | 3266 => 101001001010
  | 3267 => 11111001111111111111
  | 3268 => 11101000000100
  | 3269 => 100100111111
  | 3270 => 10010101110
  | 3271 => 1110111100101
  | 3272 => 1100001001000
  | 3273 => 10010010110001
  | 3274 => 111101111010
  | 3275 => 10100100
  | 3276 => 1010111111100
  | 3277 => 1000011001101
  | 3278 => 11100111110
  | 3279 => 10011110011011
  | 3280 => 111110000
  | 3281 => 1100100011001
  | 3282 => 1001010
  | 3283 => 10001000001111
  | 3284 => 1000010101100
  | 3285 => 1011110011110
  | 3286 => 11000000010
  | 3287 => 10110000111
  | 3288 => 1110111000
  | 3289 => 10010101101
  | 3290 => 111100010
  | 3291 => 1101010010001
  | 3292 => 110001110100
  | 3293 => 11110111101
  | 3294 => 1111101001110
  | 3295 => 111101001110
  | 3296 => 1110000100000
  | 3297 => 100001101001010111
  | 3298 => 1010010010010
  | 3299 => 1110000011101
  | 3300 => 11111100
  | 3301 => 111101100101
  | 3302 => 10100000111110
  | 3303 => 110111011101
  | 3304 => 11101100101000
  | 3305 => 1010001000010
  | 3306 => 10100111010
  | 3307 => 1010100001
  | 3308 => 100010000100100
  | 3309 => 1110100011
  | 3310 => 1110111110
  | 3311 => 10000110000111
  | 3312 => 110111110110000
  | 3313 => 1110110101
  | 3314 => 101011101110
  | 3315 => 1001110110
  | 3316 => 1100000100
  | 3317 => 1001111011011
  | 3318 => 1010111000010
  | 3319 => 10010001111
  | 3320 => 101011000
  | 3321 => 1101011100111
  | 3322 => 11111110010
  | 3323 => 11011011011001
  | 3324 => 101110111010100
  | 3325 => 1110111100
  | 3326 => 1011111101010
  | 3327 => 1111100101101
  | 3328 => 100100000000
  | 3329 => 11111100101
  | 3330 => 1111111110
  | 3331 => 101110110011
  | 3332 => 101001000100
  | 3333 => 111111111111
  | 3334 => 111111101110
  | 3335 => 11101101110
  | 3336 => 110110101000
  | 3337 => 10011
  | 3338 => 1100010011010
  | 3339 => 1111011010011
  | 3340 => 1111101100
  | 3341 => 10011000000001
  | 3342 => 10101000011010
  | 3343 => 111011001
  | 3344 => 1001110000
  | 3345 => 10011110010
  | 3346 => 1011111010
  | 3347 => 11010000011
  | 3348 => 1111101011100
  | 3349 => 101100111001
  | 3350 => 110101100
  | 3351 => 100011101001
  | 3352 => 10001111000
  | 3353 => 10100001111011
  | 3354 => 10100011100010
  | 3355 => 11011110
  | 3356 => 1110001111100
  | 3357 => 1001100111111
  | 3358 => 1000110101010
  | 3359 => 1000110101011
  | 3360 => 1010100000
  | 3361 => 10110001101011
  | 3362 => 1011100000010
  | 3363 => 10011011011011
  | 3364 => 10011000010100
  | 3365 => 1001000010
  | 3366 => 11111111111101111110
  | 3367 => 10101
  | 3368 => 100110011000
  | 3369 => 10001010010101
  | 3370 => 10110
  | 3371 => 1011101111
  | 3372 => 101110010100
  | 3373 => 1010001001
  | 3374 => 1110111000110
  | 3375 => 1101111111000
  | 3376 => 1101000110000
  | 3377 => 111111111001
  | 3378 => 1000111100010
  | 3379 => 110001010111
  | 3380 => 1011110100
  | 3381 => 1111001100111
  | 3382 => 110101010
  | 3383 => 101111010010111
  | 3384 => 100111011111000
  | 3385 => 10010101101010
  | 3386 => 111010010
  | 3387 => 1001111011011
  | 3388 => 1101100
  | 3389 => 100000001111011
  | 3390 => 10101010110
  | 3391 => 1010110100001
  | 3392 => 100011000000
  | 3393 => 1001101111101
  | 3394 => 110000100010
  | 3395 => 11101100010
  | 3396 => 1001111000100
  | 3397 => 100001100011
  | 3398 => 110100110110
  | 3399 => 1110110001
  | 3400 => 11101000
  | 3401 => 1111110101
  | 3402 => 110101110101010
  | 3403 => 1011011110001
  | 3404 => 1000010100
  | 3405 => 110111101110
  | 3406 => 10000000111010
  | 3407 => 1000101001
  | 3408 => 100110000
  | 3409 => 101000110001
  | 3410 => 110010010
  | 3411 => 1110010011111
  | 3412 => 100101000100
  | 3413 => 1000000011001011
  | 3414 => 10110100110
  | 3415 => 1000001111010
  | 3416 => 1010010001000
  | 3417 => 1110010000011
  | 3418 => 10110001010110
  | 3419 => 101100100101
  | 3420 => 111101111100
  | 3421 => 1111110011
  | 3422 => 1010111110110
  | 3423 => 100100011011
  | 3424 => 10001001100000
  | 3425 => 1000100
  | 3426 => 10000100010
  | 3427 => 1010010111001
  | 3428 => 1001001110100
  | 3429 => 1111100101011
  | 3430 => 11000010
  | 3431 => 1000111011101
  | 3432 => 111111000
  | 3433 => 10111111110111
  | 3434 => 10010110
  | 3435 => 111101111010
  | 3436 => 10111111101100
  | 3437 => 1110110110011
  | 3438 => 1011110110110
  | 3439 => 101011011100111
  | 3440 => 11011010000
  | 3441 => 111010101
  | 3442 => 101000000010
  | 3443 => 110011001111
  | 3444 => 11001010001100
  | 3445 => 1001110110
  | 3446 => 1111111010
  | 3447 => 10011111011001
  | 3448 => 101100101000
  | 3449 => 1001100011001
  | 3450 => 1000010100
  | 3451 => 1001101111101
  | 3452 => 11000111010100
  | 3453 => 11111111110101
  | 3454 => 10011101111110
  | 3455 => 100101100010
  | 3456 => 11011111110000000
  | 3457 => 10001101
  | 3458 => 10000000010
  | 3459 => 100100001
  | 3460 => 101100110100
  | 3461 => 1011100001
  | 3462 => 1101111101010
  | 3463 => 1110101001111
  | 3464 => 10001001000
  | 3465 => 1111111111111111110
  | 3466 => 101110100010
  | 3467 => 101001001101
  | 3468 => 10101001100100
  | 3469 => 10101100111
  | 3470 => 10101111010
  | 3471 => 101001001101
  | 3472 => 100000110000
  | 3473 => 110110100111
  | 3474 => 1100111111010
  | 3475 => 11011010100
  | 3476 => 1001001100
  | 3477 => 1011110011011
  | 3478 => 1001110111110
  | 3479 => 11011101101
  | 3480 => 11010111000
  | 3481 => 10011001011101
  | 3482 => 11100111110
  | 3483 => 11101010101101
  | 3484 => 11100111100
  | 3485 => 100110110
  | 3486 => 101000000010
  | 3487 => 1000011111011
  | 3488 => 100101011100000
  | 3489 => 1110100011111
  | 3490 => 11001000010
  | 3491 => 101011111011
  | 3492 => 11001110111100
  | 3493 => 1001111010011
  | 3494 => 1100000000010
  | 3495 => 10011001110
  | 3496 => 11101111000
  | 3497 => 10100001000011
  | 3498 => 1001110110
  | 3499 => 10001001001001
  | 3500 => 1001000
  | 3501 => 10011010110111
  | 3502 => 1000011001010
  | 3503 => 1101011000001
  | 3504 => 11101110000
  | 3505 => 101101101110
  | 3506 => 1001000111010
  | 3507 => 100100101101
  | 3508 => 101011101001100
  | 3509 => 100000110111
  | 3510 => 10110010111110
  | 3511 => 101010001001111
  | 3512 => 10001100011000
  | 3513 => 100010111001
  | 3514 => 1000011010110
  | 3515 => 101000010
  | 3516 => 100110101100
  | 3517 => 10111110110111
  | 3518 => 111011000110
  | 3519 => 1111001011101
  | 3520 => 11000000
  | 3521 => 11010100101
  | 3522 => 11010111010110
  | 3523 => 1011101
  | 3524 => 10010010100
  | 3525 => 1001100
  | 3526 => 10100100011110
  | 3527 => 10111011001111
  | 3528 => 11111110101000
  | 3529 => 1101110001001
  | 3530 => 101011010010
  | 3531 => 110100111
  | 3532 => 110110100
  | 3533 => 10000110101111
  | 3534 => 10011011000010
  | 3535 => 1011010
  | 3536 => 1001110110000
  | 3537 => 1001100111111
  | 3538 => 101001011111110
  | 3539 => 101001110011
  | 3540 => 10010111100
  | 3541 => 10000000001
  | 3542 => 100101011010
  | 3543 => 10110011110101
  | 3544 => 110000001000
  | 3545 => 1110111000010
  | 3546 => 1011110110110
  | 3547 => 100100111110101
  | 3548 => 1100000011100
  | 3549 => 10111101
  | 3550 => 1001100
  | 3551 => 101111000001
  | 3552 => 11100000
  | 3553 => 1101111001001
  | 3554 => 1010100110
  | 3555 => 111110110110
  | 3556 => 100111001111100
  | 3557 => 10101011000001
  | 3558 => 100101110010
  | 3559 => 100111111
  | 3560 => 11010101000
  | 3561 => 11010000010101
  | 3562 => 100110010
  | 3563 => 10101100001111
  | 3564 => 111111111111111101100
  | 3565 => 11000000010
  | 3566 => 11001110
  | 3567 => 111101110011
  | 3568 => 10011110010000
  | 3569 => 111001000101
  | 3570 => 1001110110
  | 3571 => 1001100000011
  | 3572 => 10000111101100
  | 3573 => 1100111111001
  | 3574 => 10010010111110
  | 3575 => 100100
  | 3576 => 10000111011000
  | 3577 => 11001110001
  | 3578 => 111011010110
  | 3579 => 1011100101111
  | 3580 => 1101011100
  | 3581 => 111011
  | 3582 => 101011100110110
  | 3583 => 111010000111
  | 3584 => 1001000000000
  | 3585 => 1010000111110110
  | 3586 => 1001000110110
  | 3587 => 101010110111
  | 3588 => 1001010110100
  | 3589 => 1110110001
  | 3590 => 10010101110
  | 3591 => 1111111100001
  | 3592 => 111100111000
  | 3593 => 1101100001
  | 3594 => 1100000000010
  | 3595 => 1010000000010
  | 3596 => 1110111100100100
  | 3597 => 11100101001
  | 3598 => 1001111100010
  | 3599 => 10100001101001
  | 3600 => 1111111110000
  | 3601 => 110110011100011
  | 3602 => 110110100110110
  | 3603 => 10001110000101
  | 3604 => 10001100
  | 3605 => 11101100010
  | 3606 => 111001100010
  | 3607 => 1111111101
  | 3608 => 1111111111000
  | 3609 => 1100110101111
  | 3610 => 111011110
  | 3611 => 10001110101011
  | 3612 => 111000101100
  | 3613 => 1101010001001
  | 3614 => 10100100010
  | 3615 => 100010110110
  | 3616 => 101101100000
  | 3617 => 100011001101001
  | 3618 => 10101110101110
  | 3619 => 1100100001
  | 3620 => 100111100
  | 3621 => 1001100010011
  | 3622 => 1001001111010
  | 3623 => 100111110100111
  | 3624 => 10001011011000
  | 3625 => 1101101000
  | 3626 => 101111010
  | 3627 => 101010111111
  | 3628 => 1000101101100
  | 3629 => 11101111
  | 3630 => 10001111010
  | 3631 => 1000010010011
  | 3632 => 110011010000
  | 3633 => 1011100110111
  | 3634 => 11110101010
  | 3635 => 1011000100010
  | 3636 => 101111111111111111100
  | 3637 => 1111000111001
  | 3638 => 1010010100110
  | 3639 => 11000101110111
  | 3640 => 1001000
  | 3641 => 1011000111
  | 3642 => 11100100001010
  | 3643 => 1010100100001
  | 3644 => 10100001100100
  | 3645 => 1011111110010
  | 3646 => 11100010010
  | 3647 => 100000110101101
  | 3648 => 11001000000
  | 3649 => 1011000110111
  | 3650 => 1000100
  | 3651 => 10001111101101
  | 3652 => 111110000100
  | 3653 => 101101111111
  | 3654 => 1011111001110
  | 3655 => 11010110010
  | 3656 => 1001101001000
  | 3657 => 1100000001
  | 3658 => 10101000010
  | 3659 => 1010011110001
  | 3660 => 10010100
  | 3661 => 10010111000001
  | 3662 => 11000100000010
  | 3663 => 111111111111111111
  | 3664 => 100001000110000
  | 3665 => 100011011110
  | 3666 => 1101000010110
  | 3667 => 11001
  | 3668 => 1011000111100
  | 3669 => 101110000111011
  | 3670 => 11010
  | 3671 => 1000110100101
  | 3672 => 111101101011000
  | 3673 => 1100010010101
  | 3674 => 11000011110
  | 3675 => 110000100
  | 3676 => 101011101001100
  | 3677 => 1100011000101
  | 3678 => 101100110010
  | 3679 => 11000110001101
  | 3680 => 11010100000
  | 3681 => 10001111101011
  | 3682 => 1011001001010
  | 3683 => 1011110000001
  | 3684 => 101111100011100
  | 3685 => 1101100110
  | 3686 => 11011011001010
  | 3687 => 100001111001
  | 3688 => 111101000
  | 3689 => 11001000101
  | 3690 => 1110011110110
  | 3691 => 11101101100001
  | 3692 => 1010010010100
  | 3693 => 100001111001
  | 3694 => 1011011100110
  | 3695 => 1101110
  | 3696 => 1111110000
  | 3697 => 11010101000111
  | 3698 => 101100011011110
  | 3699 => 10110100101111
  | 3700 => 11100
  | 3701 => 1111001010111
  | 3702 => 10100000010
  | 3703 => 1001110001101
  | 3704 => 110100011000
  | 3705 => 101101010010
  | 3706 => 11011110010010
  | 3707 => 101101011
  | 3708 => 11110110110100
  | 3709 => 100001101000111
  | 3710 => 1001110110
  | 3711 => 110010001011
  | 3712 => 11011010000000
  | 3713 => 10010001000101
  | 3714 => 110100100110
  | 3715 => 101100010
  | 3716 => 110000010100
  | 3717 => 1100001111111
  | 3718 => 101111010
  | 3719 => 1010101111111
  | 3720 => 10000011000
  | 3721 => 110000100011111
  | 3722 => 1001111011110
  | 3723 => 1001001100101
  | 3724 => 10100110001100
  | 3725 => 11011100
  | 3726 => 11010110110110
  | 3727 => 10110111001011
  | 3728 => 1111100110000
  | 3729 => 100110110001
  | 3730 => 1010110110
  | 3731 => 1011101
  | 3732 => 1110111110100
  | 3733 => 101101001001001
  | 3734 => 11101111110010
  | 3735 => 1001101111110
  | 3736 => 100000111000
  | 3737 => 10101111
  | 3738 => 1010010011010
  | 3739 => 10101010010111
  | 3740 => 100101100
  | 3741 => 100100110001001
  | 3742 => 1101011111010
  | 3743 => 11100101100011
  | 3744 => 1010111111100000
  | 3745 => 110111001110110
  | 3746 => 110000110010
  | 3747 => 10110110110011
  | 3748 => 1011011100100
  | 3749 => 101000010001111
  | 3750 => 1110000
  | 3751 => 100001101101
  | 3752 => 1100100001000
  | 3753 => 11010110111001
  | 3754 => 1101101000010
  | 3755 => 11110001110
  | 3756 => 110000000100
  | 3757 => 10000000111101
  | 3758 => 1010111110110
  | 3759 => 11010111
  | 3760 => 100110000
  | 3761 => 1011111001
  | 3762 => 1111111111111111110
  | 3763 => 111110101
  | 3764 => 10000101100
  | 3765 => 11100101010
  | 3766 => 101100110011110
  | 3767 => 111010111001
  | 3768 => 110111101101000
  | 3769 => 11101000100011
  | 3770 => 111000110
  | 3771 => 1101100101111
  | 3772 => 100100110100
  | 3773 => 1101101001
  | 3774 => 1000110
  | 3775 => 111000100
  | 3776 => 11011111000000
  | 3777 => 11100010011
  | 3778 => 1100001101011110
  | 3779 => 10001111101101
  | 3780 => 101011101011100
  | 3781 => 1100010111
  | 3782 => 10010111011110
  | 3783 => 1110110001
  | 3784 => 111111011000
  | 3785 => 1011010010110
  | 3786 => 11111010011010
  | 3787 => 1001101111101
  | 3788 => 101100110100
  | 3789 => 1001111010111
  | 3790 => 1001011010
  | 3791 => 101001001001
  | 3792 => 1010101110000
  | 3793 => 101110001
  | 3794 => 10111010
  | 3795 => 111110010
  | 3796 => 1001100100
  | 3797 => 1010001100111
  | 3798 => 10011110011110
  | 3799 => 100010100001101
  | 3800 => 11001000
  | 3801 => 1011101011011
  | 3802 => 1000101101110
  | 3803 => 1111111101
  | 3804 => 100111110101100
  | 3805 => 110111000110
  | 3806 => 10110011010
  | 3807 => 111101101011
  | 3808 => 10011101100000
  | 3809 => 110000111
  | 3810 => 1010111010
  | 3811 => 1110110001
  | 3812 => 10010101101100
  | 3813 => 111111111111111
  | 3814 => 110111000010
  | 3815 => 11100101110
  | 3816 => 11111101101000
  | 3817 => 101011000101
  | 3818 => 10010011000110
  | 3819 => 101111000001
  | 3820 => 1110111100
  | 3821 => 101010011111
  | 3822 => 101111010
  | 3823 => 100101000001
  | 3824 => 11111110000
  | 3825 => 1011111011100
  | 3826 => 100101111010
  | 3827 => 1101001111
  | 3828 => 11110100100
  | 3829 => 1001011101111
  | 3830 => 110101010
  | 3831 => 1000011101011011
  | 3832 => 100111000
  | 3833 => 10100110110011
  | 3834 => 1110011111010
  | 3835 => 111011001010
  | 3836 => 1001100100
  | 3837 => 1001010001011
  | 3838 => 11111010
  | 3839 => 1100100001
  | 3840 => 11100000000
  | 3841 => 1000010000111
  | 3842 => 11110111011110
  | 3843 => 1001011101111
  | 3844 => 101001100
  | 3845 => 1000110100010
  | 3846 => 10111010101110
  | 3847 => 11101100101001
  | 3848 => 10101000
  | 3849 => 1111010001
  | 3850 => 100100
  | 3851 => 100001001011011
  | 3852 => 11101011101100
  | 3853 => 1001100011001
  | 3854 => 101000111010110
  | 3855 => 1010010
  | 3856 => 1111010000
  | 3857 => 10101110001101
  | 3858 => 11101101001110
  | 3859 => 1001100001001
  | 3860 => 1100100
  | 3861 => 1001101101111111111111
  | 3862 => 1100110010
  | 3863 => 10010011100011
  | 3864 => 101100111000
  | 3865 => 101110000110
  | 3866 => 1010100110110
  | 3867 => 11011001110011
  | 3868 => 1001000010100
  | 3869 => 10011111011
  | 3870 => 111110111010
  | 3871 => 101100111001001
  | 3872 => 1101100000
  | 3873 => 1110110000001
  | 3874 => 1010110111010
  | 3875 => 111011000
  | 3876 => 11110110101100
  | 3877 => 1100001100001
  | 3878 => 1011010111011110
  | 3879 => 111001111011
  | 3880 => 11100001000
  | 3881 => 1110011101101
  | 3882 => 101100110010
  | 3883 => 1111101101011
  | 3884 => 100110100
  | 3885 => 101010
  | 3886 => 101111011011110
  | 3887 => 111110101011
  | 3888 => 1001111101110000
  | 3889 => 101110111
  | 3890 => 10110110
  | 3891 => 11111110110111
  | 3892 => 101001000100
  | 3893 => 10110111100101
  | 3894 => 1001011110
  | 3895 => 10110010010
  | 3896 => 1100110111000
  | 3897 => 1110111111
  | 3898 => 11001111010
  | 3899 => 100111110001
  | 3900 => 1010100
  | 3901 => 101111100010011
  | 3902 => 11010011010010
  | 3903 => 110011000101
  | 3904 => 100101000000
  | 3905 => 10011100110
  | 3906 => 1010101111110
  | 3907 => 101111101011
  | 3908 => 101111000100
  | 3909 => 1101110101011
  | 3910 => 1101110001010
  | 3911 => 1110111111101
  | 3912 => 100000011000
  | 3913 => 1011110110101
  | 3914 => 100101000110
  | 3915 => 10110111010110
  | 3916 => 110011111100
  | 3917 => 10000101
  | 3918 => 100100011100010
  | 3919 => 10101101011
  | 3920 => 11000010000
  | 3921 => 10001010000111
  | 3922 => 1000110
  | 3923 => 1000000110001
  | 3924 => 111111101100
  | 3925 => 1010110101100
  | 3926 => 11111110010
  | 3927 => 100111011
  | 3928 => 100101010101000
  | 3929 => 1000100111001
  | 3930 => 1010010
  | 3931 => 11011010101
  | 3932 => 1100011110100
  | 3933 => 110011111101
  | 3934 => 1011011111110
  | 3935 => 101100011110
  | 3936 => 1000110011100000
  | 3937 => 100011111001
  | 3938 => 100001100011010
  | 3939 => 10101010101
  | 3940 => 110100010100
  | 3941 => 1101001111
  | 3942 => 1011110011110
  | 3943 => 111011111111011
  | 3944 => 111101001000
  | 3945 => 1011001001010
  | 3946 => 11110101110
  | 3947 => 10001001011111
  | 3948 => 10010100011100
  | 3949 => 110011001111
  | 3950 => 1001001100
  | 3951 => 1100111110101
  | 3952 => 10000000010000
  | 3953 => 1011100101010111
  | 3954 => 10011111110010
  | 3955 => 1100111101110
  | 3956 => 1111101111110100100
  | 3957 => 110001011001
  | 3958 => 100000111011110
  | 3959 => 1100110011111
  | 3960 => 111111111111111111000
  | 3961 => 111110011
  | 3962 => 100000100100110
  | 3963 => 10001110011111
  | 3964 => 11000100
  | 3965 => 10100100010
  | 3966 => 1110110111010
  | 3967 => 1010010101
  | 3968 => 1110110000000
  | 3969 => 10101011010111
  | 3970 => 110100010
  | 3971 => 11001000011001
  | 3972 => 101100011100
  | 3973 => 1000011001101
  | 3974 => 1010001101110
  | 3975 => 10001100
  | 3976 => 11000101000
  | 3977 => 111010001
  | 3978 => 10011011111010
  | 3979 => 10011000101011
  | 3980 => 11100001100
  | 3981 => 1111100010111
  | 3982 => 111100010010
  | 3983 => 1111111011101
  | 3984 => 11111000010000
  | 3985 => 100011011010
  | 3986 => 11101010
  | 3987 => 110011110111
  | 3988 => 11111000000100
  | 3989 => 101000111011101
  | 3990 => 11110111110
  | 3991 => 10011101111011
  | 3992 => 11100000011000
  | 3993 => 1101000100101
  | 3994 => 10000010111010
  | 3995 => 11011011010
  | 3996 => 11111111111111111111111111100
  | 3997 => 11101000001
  | 3998 => 11110000001110
  | 3999 => 11111001111111
  | _ => 1

def witness_fast_4 : Nat → Nat
  | 4000 => 100000
  | 4001 => 11111001100011
  | 4002 => 100010000010
  | 4003 => 100011100111
  | 4004 => 100100
  | 4005 => 10111111110
  | 4006 => 1000011110010
  | 4007 => 1001011001011
  | 4008 => 100000101000
  | 4009 => 11100010111101
  | 4010 => 11110110010
  | 4011 => 1100001111111
  | 4012 => 11111000000100
  | 4013 => 1010011010101
  | 4014 => 101110111110
  | 4015 => 1100110
  | 4016 => 1100010010000
  | 4017 => 1110110001
  | 4018 => 1001000101010
  | 4019 => 101011010011
  | 4020 => 1001000100
  | 4021 => 101001010001
  | 4022 => 100100101111110
  | 4023 => 1001110101111
  | 4024 => 1101000101000
  | 4025 => 1110111100
  | 4026 => 11011110
  | 4027 => 10000100101
  | 4028 => 1111111011100
  | 4029 => 11111011011
  | 4030 => 1110011110
  | 4031 => 11100111011111
  | 4032 => 1111011111000000
  | 4033 => 101110000011
  | 4034 => 100110111010010
  | 4035 => 10101001110
  | 4036 => 1001000111111100
  | 4037 => 110101101
  | 4038 => 1001000010
  | 4039 => 1110100001101
  | 4040 => 101000
  | 4041 => 1101110111001
  | 4042 => 1000011010
  | 4043 => 101111011001
  | 4044 => 101100
  | 4045 => 111010001110
  | 4046 => 100000001111010
  | 4047 => 101111110011
  | 4048 => 111110010000
  | 4049 => 110001001001
  | 4050 => 111111110100
  | 4051 => 10000100101
  | 4052 => 1000011010100
  | 4053 => 110000110101
  | 4054 => 100010011110
  | 4055 => 10010100010
  | 4056 => 10111101000
  | 4057 => 110010111011
  | 4058 => 1001110000010
  | 4059 => 110101101111111111111
  | 4060 => 1101011100
  | 4061 => 1010011111011
  | 4062 => 100110000101010
  | 4063 => 1001111011
  | 4064 => 1101001100000
  | 4065 => 1111111111111110
  | 4066 => 1000000111010
  | 4067 => 10100000001
  | 4068 => 11001111011100
  | 4069 => 1101100001001
  | 4070 => 1111110
  | 4071 => 1011000001101
  | 4072 => 100101100011000
  | 4073 => 100111110111
  | 4074 => 11101100010
  | 4075 => 101011100
  | 4076 => 110111000100
  | 4077 => 11111101101
  | 4078 => 110010111111010
  | 4079 => 110111010111
  | 4080 => 1000110000
  | 4081 => 100111011
  | 4082 => 10011100011000010
  | 4083 => 1000100011101
  | 4084 => 1001110001100
  | 4085 => 1110100000010
  | 4086 => 110111101110
  | 4087 => 10100011011
  | 4088 => 10011001000
  | 4089 => 110100001011
  | 4090 => 11000010010
  | 4091 => 10011111100101
  | 4092 => 1001001101100
  | 4093 => 100000000001
  | 4094 => 10000111110110
  | 4095 => 101011111110
  | 4096 => 1000000000000
  | 4097 => 110110001011
  | 4098 => 1000001111010
  | 4099 => 101101011101
  | 4100 => 1111100
  | 4101 => 11101001001
  | 4102 => 100100101010
  | 4103 => 101000010111
  | 4104 => 110101110111000
  | 4105 => 100001010110
  | 4106 => 11010110010010
  | 4107 => 10100111001
  | 4108 => 1110101101001100
  | 4109 => 10110111001011
  | 4110 => 11101110
  | 4111 => 111001111
  | 4112 => 1010010000
  | 4113 => 10010111010111
  | 4114 => 10110011010
  | 4115 => 11000111010
  | 4116 => 110000100
  | 4117 => 1001001011001
  | 4118 => 10011110001010
  | 4119 => 1011010111101
  | 4120 => 11100001000
  | 4121 => 110001001111001
  | 4122 => 111101111010
  | 4123 => 10101111101011
  | 4124 => 100110100
  | 4125 => 111111000
  | 4126 => 10000100111010
  | 4127 => 11001011111101
  | 4128 => 10010000100000
  | 4129 => 10110100111
  | 4130 => 111011001010
  | 4131 => 111101101011
  | 4132 => 11101100101100
  | 4133 => 101100011010001
  | 4134 => 1001110110
  | 4135 => 10001000010010
  | 4136 => 1001110011000
  | 4137 => 11010100101
  | 4138 => 1101101110
  | 4139 => 111100110001
  | 4140 => 1101111101100
  | 4141 => 11111011111
  | 4142 => 11011110010010
  | 4143 => 10111011001101
  | 4144 => 101010000
  | 4145 => 110000010
  | 4146 => 1111110110010
  | 4147 => 11111111011
  | 4148 => 101001000100
  | 4149 => 10011001111011
  | 4150 => 10101100
  | 4151 => 10111101111111
  | 4152 => 1011001101000
  | 4153 => 1000000110001
  | 4154 => 1110011110
  | 4155 => 10111011101010
  | 4156 => 1010100111100
  | 4157 => 100010110011111
  | 4158 => 10011011011111111111110
  | 4159 => 1101010111111
  | 4160 => 1001000000
  | 4161 => 101010110001
  | 4162 => 1000100111110
  | 4163 => 1101101011
  | 4164 => 1010100101100
  | 4165 => 10100100010
  | 4166 => 1001011000110
  | 4167 => 111011101011
  | 4168 => 1010110111000
  | 4169 => 100111110011
  | 4170 => 1101101010
  | 4171 => 100100000011
  | 4172 => 1100011110100
  | 4173 => 11110110100011
  | 4174 => 10011100101110
  | 4175 => 1111101100
  | 4176 => 101111011110000
  | 4177 => 10101001011
  | 4178 => 1000000101110
  | 4179 => 110111010101001
  | 4180 => 10011100
  | 4181 => 10111000101
  | 4182 => 11100011000010
  | 4183 => 1101110110101
  | 4184 => 110111001101000
  | 4185 => 111110101110
  | 4186 => 100101011010
  | 4187 => 1111111111111
  | 4188 => 101110100111100
  | 4189 => 1110000001001
  | 4190 => 100011110
  | 4191 => 101100000111
  | 4192 => 10100100000
  | 4193 => 10011011100111
  | 4194 => 11001010111110
  | 4195 => 111000111110
  | 4196 => 10000100111100
  | 4197 => 1110001000011
  | 4198 => 10010110010
  | 4199 => 11001110000101
  | 4200 => 10101000
  | 4201 => 1111101111111
  | 4202 => 111101111110
  | 4203 => 1111001001111
  | 4204 => 101001100
  | 4205 => 1001100001010
  | 4206 => 1111010000010
  | 4207 => 1000000000111
  | 4208 => 100011010000
  | 4209 => 100001111100111
  | 4210 => 1001100110
  | 4211 => 10000110111101
  | 4212 => 101101101110100
  | 4213 => 1001110110011
  | 4214 => 1110000111010
  | 4215 => 10111001010
  | 4216 => 1101110111000
  | 4217 => 1010111011011
  | 4218 => 101000010
  | 4219 => 11000110101
  | 4220 => 11010001100
  | 4221 => 1010111010111
  | 4222 => 1111000111010
  | 4223 => 111010001
  | 4224 => 1111110000000
  | 4225 => 1011110100
  | 4226 => 101100011111010
  | 4227 => 10100011101111
  | 4228 => 111111100100
  | 4229 => 10010110110001
  | 4230 => 1001110111110
  | 4231 => 11111111101011
  | 4232 => 1000111001000
  | 4233 => 110011001001
  | 4234 => 1011100010110
  | 4235 => 110110
  | 4236 => 1010110100100
  | 4237 => 1001101001011
  | 4238 => 1001000110110
  | 4239 => 10001111101101
  | 4240 => 1000110000
  | 4241 => 11011101100101
  | 4242 => 110101110
  | 4243 => 1101100111101
  | 4244 => 100001111100100
  | 4245 => 100111100010
  | 4246 => 11001110010
  | 4247 => 100010110011
  | 4248 => 101011111011000
  | 4249 => 1101010011101
  | 4250 => 11101000
  | 4251 => 101001001101
  | 4252 => 1000000011010100
  | 4253 => 11010111111
  | 4254 => 10010110010010
  | 4255 => 100001010
  | 4256 => 1110111100000
  | 4257 => 11011110111111111111
  | 4258 => 10111110010010
  | 4259 => 110100001001
  | 4260 => 1001100
  | 4261 => 1001100010111
  | 4262 => 101001001111010
  | 4263 => 101111100111
  | 4264 => 1011101000
  | 4265 => 10010100010
  | 4266 => 1100111110110
  | 4267 => 110010100001
  | 4268 => 1110000100
  | 4269 => 10001110101
  | 4270 => 10100100010
  | 4271 => 100011111010011
  | 4272 => 10111111110000
  | 4273 => 1100101100101
  | 4274 => 11110100011010
  | 4275 => 111101111100
  | 4276 => 110000100
  | 4277 => 1100100001
  | 4278 => 11000000010
  | 4279 => 1110011111
  | 4280 => 100010011000
  | 4281 => 111001001101101
  | 4282 => 11100110010010
  | 4283 => 10101100011
  | 4284 => 11101111100100
  | 4285 => 100100111010
  | 4286 => 10010011011010
  | 4287 => 10011101001
  | 4288 => 1101011000000
  | 4289 => 1110000101001
  | 4290 => 1111110
  | 4291 => 10110111010111
  | 4292 => 10001111100
  | 4293 => 110100111111
  | 4294 => 10100010000110
  | 4295 => 1011111110110
  | 4296 => 11010111000
  | 4297 => 1011101000101
  | 4298 => 100011000110
  | 4299 => 10000001010111
  | 4300 => 110110100
  | 4301 => 1100010001101
  | 4302 => 1010000111110110
  | 4303 => 100110101111111
  | 4304 => 1001000110000
  | 4305 => 1100101000110
  | 4306 => 100000111110
  | 4307 => 1100011000101
  | 4308 => 100101011100
  | 4309 => 111101011011
  | 4310 => 1011001010
  | 4311 => 11001111100101
  | 4312 => 10111101000
  | 4313 => 10001110111011
  | 4314 => 1010000000010
  | 4315 => 1100011101010
  | 4316 => 1010000000100
  | 4317 => 110010111
  | 4318 => 10011100111110
  | 4319 => 100110101
  | 4320 => 110111111100000
  | 4321 => 10111101111
  | 4322 => 101101110010
  | 4323 => 1111011
  | 4324 => 101000100100
  | 4325 => 101100110100
  | 4326 => 11101100010
  | 4327 => 1110001010100001
  | 4328 => 10101011000
  | 4329 => 10101111111
  | 4330 => 100010010
  | 4331 => 101110101101
  | 4332 => 11011101101100
  | 4333 => 11010010011
  | 4334 => 110101001010
  | 4335 => 1010100110010
  | 4336 => 111110000
  | 4337 => 10011110111
  | 4338 => 10010111101110
  | 4339 => 11101100010011
  | 4340 => 1000001100
  | 4341 => 1000111100001
  | 4342 => 1001001011010
  | 4343 => 10110100101
  | 4344 => 11110001001000
  | 4345 => 100100110
  | 4346 => 100110110
  | 4347 => 1101111110001
  | 4348 => 1000100111100
  | 4349 => 1000001010001
  | 4350 => 1101011100
  | 4351 => 1011110011011
  | 4352 => 1110100000000
  | 4353 => 1010110111011
  | 4354 => 1011110110010
  | 4355 => 1110011110
  | 4356 => 1001111111111111111100
  | 4357 => 111011101101
  | 4358 => 1001000111110
  | 4359 => 1000011001101
  | 4360 => 1001010111000
  | 4361 => 1100000110111
  | 4362 => 1101000010110
  | 4363 => 1110000110101
  | 4364 => 10000010101100
  | 4365 => 1100111011110
  | 4366 => 1011100110
  | 4367 => 1101011110001
  | 4368 => 101010000
  | 4369 => 10100100101001
  | 4370 => 111011110
  | 4371 => 1101110110101
  | 4372 => 11111110100
  | 4373 => 1000011111111
  | 4374 => 10010110111110
  | 4375 => 10010000
  | 4376 => 100101000
  | 4377 => 1001111101111011
  | 4378 => 100011010110
  | 4379 => 10111111
  | 4380 => 111011100
  | 4381 => 101110111011
  | 4382 => 110010110
  | 4383 => 11111111001
  | 4384 => 1000100000
  | 4385 => 10101110100110
  | 4386 => 11010110010
  | 4387 => 100000011101
  | 4388 => 111100101100
  | 4389 => 10110101001
  | 4390 => 100011000110
  | 4391 => 11100101111
  | 4392 => 111011011101000
  | 4393 => 11101111
  | 4394 => 11001101000110
  | 4395 => 10011010110
  | 4396 => 1001011111111111100
  | 4397 => 11110111101101
  | 4398 => 111001100010
  | 4399 => 11110110001
  | 4400 => 110000
  | 4401 => 1101010101111
  | 4402 => 100100111000010
  | 4403 => 100111011
  | 4404 => 110100
  | 4405 => 1001001010
  | 4406 => 110001011110
  | 4407 => 1110011111001
  | 4408 => 1010011101000
  | 4409 => 10010101011
  | 4410 => 111111101010
  | 4411 => 1001000100001
  | 4412 => 111010001100
  | 4413 => 100111010001
  | 4414 => 111111101010110
  | 4415 => 11011010
  | 4416 => 10000101000000
  | 4417 => 1111101001101
  | 4418 => 1110001110010010
  | 4419 => 1110110110011
  | 4420 => 10011101100
  | 4421 => 10101110000101
  | 4422 => 1101100110
  | 4423 => 11000001
  | 4424 => 110001101000
  | 4425 => 10010111100
  | 4426 => 1000100000110
  | 4427 => 100000011101
  | 4428 => 110101110011100
  | 4429 => 1001010111001
  | 4430 => 1100000010
  | 4431 => 1000100100111
  | 4432 => 1101111010000
  | 4433 => 10010011011
  | 4434 => 10001010110010
  | 4435 => 110000001110
  | 4436 => 110001010110100
  | 4437 => 11001111111
  | 4438 => 10001101101110
  | 4439 => 110011111101
  | 4440 => 111000
  | 4441 => 11101000101101
  | 4442 => 10000010101110
  | 4443 => 10010110101
  | 4444 => 111100
  | 4445 => 10011100111110
  | 4446 => 10111001101110
  | 4447 => 1111110001101
  | 4448 => 11011010100000
  | 4449 => 1011111101001
  | 4450 => 1101010100
  | 4451 => 10010001010001
  | 4452 => 10011101100
  | 4453 => 1001110101
  | 4454 => 11110001101010
  | 4455 => 11111111111111110110
  | 4456 => 1110101000
  | 4457 => 1001011001
  | 4458 => 11110111001010
  | 4459 => 1101101001
  | 4460 => 100111100100
  | 4461 => 1000101111111
  | 4462 => 1000101101110
  | 4463 => 11001111111011
  | 4464 => 111110101110000
  | 4465 => 1000011110110
  | 4466 => 111111110110
  | 4467 => 111010011111
  | 4468 => 1101111010100
  | 4469 => 10001000000111
  | 4470 => 100001110110
  | 4471 => 1000110110001101
  | 4472 => 110011110001000
  | 4473 => 10100111101101
  | 4474 => 1100000010
  | 4475 => 1101011100
  | 4476 => 10101101100
  | 4477 => 100011000111
  | 4478 => 1011110010
  | 4479 => 100100110010001
  | 4480 => 10010000000
  | 4481 => 11001101101001
  | 4482 => 1001101111110
  | 4483 => 1101101011
  | 4484 => 10010001000100
  | 4485 => 100101011010
  | 4486 => 101110111010
  | 4487 => 101010101101
  | 4488 => 100111011000
  | 4489 => 1011100111011
  | 4490 => 1111001110
  | 4491 => 10100101011111
  | 4492 => 10001101100
  | 4493 => 1101110100001
  | 4494 => 111111110101110
  | 4495 => 111011110010010
  | 4496 => 1010001110000
  | 4497 => 110010111
  | 4498 => 10111001101110
  | 4499 => 1100001001
  | 4500 => 111111111000
  | 4501 => 1111101111001
  | 4502 => 1011011011110
  | 4503 => 10110111000111
  | 4504 => 1101001111000
  | 4505 => 1000110
  | 4506 => 1110010000110
  | 4507 => 1010001001011
  | 4508 => 11010001100
  | 4509 => 11011101001011
  | 4510 => 11111111110
  | 4511 => 1010011100111
  | 4512 => 1001100000
  | 4513 => 11111110011111
  | 4514 => 1100100011010
  | 4515 => 11100010110
  | 4516 => 10000001100100
  | 4517 => 10010010111001
  | 4518 => 1101001111110
  | 4519 => 1001001001100101
  | 4520 => 1011011000
  | 4521 => 11001111111111
  | 4522 => 10001010101110
  | 4523 => 111001010011
  | 4524 => 10111001000100
  | 4525 => 100111100
  | 4526 => 1000101100110
  | 4527 => 1111000011111
  | 4528 => 100101110110000
  | 4529 => 110000110011001
  | 4530 => 100010110110
  | 4531 => 11000001001001
  | 4532 => 1110000100
  | 4533 => 1110001000011
  | 4534 => 1110111110111110
  | 4535 => 100010110110
  | 4536 => 1011011011101000
  | 4537 => 1100100001
  | 4538 => 11110000101110
  | 4539 => 10001001111
  | 4540 => 1100110100
  | 4541 => 101101101001
  | 4542 => 1110011000010
  | 4543 => 111110000001
  | 4544 => 10011000000
  | 4545 => 10111111111111111110
  | 4546 => 1011001010110
  | 4547 => 111110110111111
  | 4548 => 10011100010100
  | 4549 => 111010011000001
  | 4550 => 100100
  | 4551 => 10001100111
  | 4552 => 1011010011000
  | 4553 => 10110011110011
  | 4554 => 111101111111111110110
  | 4555 => 1010000110010
  | 4556 => 1111010100100
  | 4557 => 10010011011
  | 4558 => 10010011111010
  | 4559 => 1001011100111
  | 4560 => 110010000
  | 4561 => 10100111011
  | 4562 => 100100111110
  | 4563 => 1011101011011
  | 4564 => 10010001101100
  | 4565 => 11111000010
  | 4566 => 101000010110010
  | 4567 => 1001100101
  | 4568 => 1000010001000
  | 4569 => 11000000001
  | 4570 => 10011010010
  | 4571 => 11101000011101
  | 4572 => 1111111100100
  | 4573 => 110011001001
  | 4574 => 1000001110110
  | 4575 => 10010100
  | 4576 => 100100000
  | 4577 => 10101011110001
  | 4578 => 1010010011010
  | 4579 => 1001011110111
  | 4580 => 1000010001100
  | 4581 => 111011011101
  | 4582 => 100000111010
  | 4583 => 11001111111
  | 4584 => 10000000011000
  | 4585 => 101100011110
  | 4586 => 11010000010
  | 4587 => 111000001101
  | 4588 => 11101010100
  | 4589 => 11010100011001
  | 4590 => 1111011010110
  | 4591 => 1100100011
  | 4592 => 10111010000
  | 4593 => 1010010010011
  | 4594 => 100110111101110
  | 4595 => 10101110100110
  | 4596 => 1010011100100
  | 4597 => 10100010010101
  | 4598 => 110000000110
  | 4599 => 11110100011101
  | 4600 => 110101000
  | 4601 => 11101111111111
  | 4602 => 1111100000010
  | 4603 => 111011011010011
  | 4604 => 11010001111100
  | 4605 => 10111110001110
  | 4606 => 110000000010110
  | 4607 => 10011011
  | 4608 => 111111111000000000
  | 4609 => 1111010000001
  | 4610 => 1111010
  | 4611 => 1111101101001
  | 4612 => 10010000100
  | 4613 => 1101111000101
  | 4614 => 11010000001110
  | 4615 => 101001001010
  | 4616 => 110001011000
  | 4617 => 111101101011
  | 4618 => 101111110
  | 4619 => 11110001110011
  | 4620 => 11111100
  | 4621 => 1101100110001
  | 4622 => 100110001010
  | 4623 => 11101011111
  | 4624 => 11001100010000
  | 4625 => 111000
  | 4626 => 1101100111110
  | 4627 => 110111000111
  | 4628 => 1111101000100
  | 4629 => 1101000100101
  | 4630 => 1101000110
  | 4631 => 1111111111011
  | 4632 => 11001000
  | 4633 => 100111101011
  | 4634 => 100100111011110
  | 4635 => 1111011011010
  | 4636 => 1000101100
  | 4637 => 10101101101101
  | 4638 => 101110000110
  | 4639 => 10110000011
  | 4640 => 110110100000
  | 4641 => 100111011
  | 4642 => 1111111000010
  | 4643 => 100111110101001
  | 4644 => 10101111110100
  | 4645 => 11000001010
  | 4646 => 101010010110
  | 4647 => 111101001111
  | 4648 => 10100000001000
  | 4649 => 1111111
  | 4650 => 1000001100
  | 4651 => 11111011101
  | 4652 => 100110101110100
  | 4653 => 11111111011111111011
  | 4654 => 111011001010
  | 4655 => 1010011000110
  | 4656 => 1001101110000
  | 4657 => 100101110001011
  | 4658 => 100111110110
  | 4659 => 10001010001011
  | 4660 => 11111001100
  | 4661 => 10001010010101
  | 4662 => 101011111110
  | 4663 => 1011001010101
  | 4664 => 1001011000
  | 4665 => 111011111010
  | 4666 => 1110011001010
  | 4667 => 101000101111
  | 4668 => 1101010001100
  | 4669 => 10011001001001
  | 4670 => 1000001110
  | 4671 => 1111111000101
  | 4672 => 10001000000
  | 4673 => 1100101010101
  | 4674 => 111001110011010
  | 4675 => 100101100
  | 4676 => 10010010110100
  | 4677 => 1100110110111
  | 4678 => 1000111000010
  | 4679 => 11011100100111
  | 4680 => 10101111111000
  | 4681 => 1110000011101
  | 4682 => 10110100110
  | 4683 => 1100100000111
  | 4684 => 10001011100100
  | 4685 => 101101110010
  | 4686 => 10011100110
  | 4687 => 11111110001
  | 4688 => 1100001110000
  | 4689 => 1010011111101
  | 4690 => 11001000010
  | 4691 => 1001111001
  | 4692 => 101111111111100
  | 4693 => 10110001110001
  | 4694 => 100110111101010
  | 4695 => 11000000010
  | 4696 => 10010111000
  | 4697 => 1010010001
  | 4698 => 10110111010110
  | 4699 => 111010111101
  | 4700 => 1001100
  | 4701 => 1010101101111
  | 4702 => 1011110110110
  | 4703 => 111110101001
  | 4704 => 110000100000
  | 4705 => 1000010110
  | 4706 => 10111010110110
  | 4707 => 10110110101011
  | 4708 => 11010011100
  | 4709 => 11011111110001001
  | 4710 => 1101111011010
  | 4711 => 1000001101001
  | 4712 => 11011001011000
  | 4713 => 100001101111011
  | 4714 => 111001100110
  | 4715 => 10010011010
  | 4716 => 100110011111100
  | 4717 => 110010110100001
  | 4718 => 1011101110110
  | 4719 => 1111110111111
  | 4720 => 110111110000
  | 4721 => 1001010111011
  | 4722 => 1000101001010010
  | 4723 => 100111111001001
  | 4724 => 10101001000100
  | 4725 => 101011101011100
  | 4726 => 10100100010
  | 4727 => 11111010110111
  | 4728 => 11010100101000
  | 4729 => 110100111101101
  | 4730 => 1111110110
  | 4731 => 111101111111001
  | 4732 => 1011110100
  | 4733 => 10011010000111
  | 4734 => 1110100111110
  | 4735 => 10110011010
  | 4736 => 1110000000
  | 4737 => 1011111101001
  | 4738 => 100000110000110
  | 4739 => 1011000010111
  | 4740 => 10101011100
  | 4741 => 1011011001011
  | 4742 => 1000110111110
  | 4743 => 11000111101011
  | 4744 => 1001000011000
  | 4745 => 100110010
  | 4746 => 1100111101110
  | 4747 => 1011111
  | 4748 => 10001000010100
  | 4749 => 1100101101
  | 4750 => 11001000
  | 4751 => 101011011
  | 4752 => 11110111111111111110000
  | 4753 => 1100011111101
  | 4754 => 10000101111010
  | 4755 => 10011111010110
  | 4756 => 10001001100100
  | 4757 => 10101100011111
  | 4758 => 1100100011010
  | 4759 => 1001011101001
  | 4760 => 100111011000
  | 4761 => 1101011011011
  | 4762 => 111010101110
  | 4763 => 110011011
  | 4764 => 1100010101100
  | 4765 => 1001010110110
  | 4766 => 1010100011010
  | 4767 => 100111011111111
  | 4768 => 11011100000
  | 4769 => 100001110110001
  | 4770 => 111111011010
  | 4771 => 110111011101
  | 4772 => 1101110010100
  | 4773 => 11111100111
  | 4774 => 100100110110
  | 4775 => 1110111100
  | 4776 => 1100010111000
  | 4777 => 101000111
  | 4778 => 1111100010
  | 4779 => 1100001111111
  | 4780 => 111111100
  | 4781 => 111110110111
  | 4782 => 100011011010
  | 4783 => 1000010111011
  | 4784 => 100101011010000
  | 4785 => 1111010010
  | 4786 => 101100110110
  | 4787 => 110101
  | 4788 => 111101111100
  | 4789 => 10100001
  | 4790 => 1001110
  | 4791 => 1001101110111
  | 4792 => 10101110111000
  | 4793 => 10010011101001
  | 4794 => 1000101101010
  | 4795 => 100110010
  | 4796 => 111110011100
  | 4797 => 1101011100111
  | 4798 => 1110101001110
  | 4799 => 1001101101011
  | 4800 => 111000000
  | 4801 => 1000101111
  | 4802 => 11011010010
  | 4803 => 10010110011
  | 4804 => 1011110010100
  | 4805 => 10100110
  | 4806 => 1100111110110
  | 4807 => 1111111001011
  | 4808 => 11001011111000
  | 4809 => 11001010110111
  | 4810 => 101010
  | 4811 => 10111001110111
  | 4812 => 10100011100100
  | 4813 => 110111000011001
  | 4814 => 10110001100110
  | 4815 => 1110101110110
  | 4816 => 11010011110000
  | 4817 => 10000010111
  | 4818 => 110011111111110
  | 4819 => 1000110100001
  | 4820 => 11110100
  | 4821 => 10000001101101
  | 4822 => 10001110111110
  | 4823 => 100111011
  | 4824 => 1111110111000
  | 4825 => 1100100
  | 4826 => 1100010110101110
  | 4827 => 10001010100011
  | 4828 => 11111011101100
  | 4829 => 10011101111011
  | 4830 => 1011001110
  | 4831 => 1000011111011
  | 4832 => 111000100000
  | 4833 => 10110110010111
  | 4834 => 100010101100110
  | 4835 => 100100001010
  | 4836 => 1001001101100
  | 4837 => 111100100111
  | 4838 => 10000000110110
  | 4839 => 1001001100011
  | 4840 => 11011000
  | 4841 => 1110000011111
  | 4842 => 11010100111110
  | 4843 => 11010110101
  | 4844 => 101110011011100
  | 4845 => 1111011010110
  | 4846 => 11101000111110
  | 4847 => 100110001011
  | 4848 => 10111110000
  | 4849 => 101000010111
  | 4850 => 1110000100
  | 4851 => 1111111111110111111
  | 4852 => 11100011011100
  | 4853 => 110100011
  | 4854 => 1000101001110
  | 4855 => 10011010
  | 4856 => 1001011010101000
  | 4857 => 111100101111
  | 4858 => 111011000110010
  | 4859 => 101110100111
  | 4860 => 10011111011100
  | 4861 => 1000011001111
  | 4862 => 1001110110
  | 4863 => 11001101101101
  | 4864 => 1100100000000
  | 4865 => 10100100010
  | 4866 => 100111011011010
  | 4867 => 100001111110001
  | 4868 => 10101100
  | 4869 => 11001111111
  | 4870 => 11001101110
  | 4871 => 101100101100111
  | 4872 => 11010111000
  | 4873 => 110110001001
  | 4874 => 1010000101110
  | 4875 => 10101000
  | 4876 => 110000000100
  | 4877 => 1101011100001
  | 4878 => 100001010111101111011111110
  | 4879 => 1111000110101
  | 4880 => 1001010000
  | 4881 => 1010000100111
  | 4882 => 100001110000010
  | 4883 => 101001000101001
  | 4884 => 11111100
  | 4885 => 10111100010
  | 4886 => 11001000010
  | 4887 => 1011101011011
  | 4888 => 1100100001000
  | 4889 => 1100000110101
  | 4890 => 1000000110
  | 4891 => 110000111101
  | 4892 => 10011111100
  | 4893 => 10010101000011
  | 4894 => 10000010111010
  | 4895 => 11001111110
  | 4896 => 1011111011100000
  | 4897 => 1001111011101
  | 4898 => 1111100010110
  | 4899 => 100111011111
  | 4900 => 110000100
  | 4901 => 1010101001
  | 4902 => 10001101111110
  | 4903 => 10101000110101
  | 4904 => 110001011000
  | 4905 => 11111110110
  | 4906 => 10011110010
  | 4907 => 10000110110011
  | 4908 => 1110001010100
  | 4909 => 10100100000011
  | 4910 => 1001010101010
  | 4911 => 11110111101
  | 4912 => 100011000110000
  | 4913 => 11000101110111
  | 4914 => 10110010111110
  | 4915 => 110001111010
  | 4916 => 10000111100100
  | 4917 => 10000111011
  | 4918 => 1010100110110110
  | 4919 => 11110101011001
  | 4920 => 10001100111000
  | 4921 => 10110101001
  | 4922 => 11111000100010
  | 4923 => 1001011101111
  | 4924 => 10000111100100
  | 4925 => 110100010100
  | 4926 => 10110110011110
  | 4927 => 1100001000111
  | 4928 => 1001000000
  | 4929 => 1100000001
  | 4930 => 1111010010
  | 4931 => 101000100011
  | 4932 => 1011010010111100
  | 4933 => 11011110101001
  | 4934 => 10101110111110
  | 4935 => 1001010001110
  | 4936 => 1100111000
  | 4937 => 1100011010011
  | 4938 => 11000111010
  | 4939 => 10011101111
  | 4940 => 100000000100
  | 4941 => 111110100111
  | 4942 => 1100001010010
  | 4943 => 100011111011
  | 4944 => 11101100010000
  | 4945 => 111110111111010010
  | 4946 => 1111001111010
  | 4947 => 101100010010001
  | 4948 => 1011000100
  | 4949 => 111100101
  | 4950 => 11111111111111111100
  | 4951 => 10100110111111
  | 4952 => 11010010011000
  | 4953 => 10001000110101
  | 4954 => 1100110010
  | 4955 => 1100010
  | 4956 => 11111000000100
  | 4957 => 1101100011111
  | 4958 => 11111101110
  | 4959 => 111110010111
  | 4960 => 11101100000
  | 4961 => 10011011011111
  | 4962 => 10001110001010
  | 4963 => 10001100101111
  | 4964 => 1001111101100
  | 4965 => 10110001110
  | 4966 => 100100000110110
  | 4967 => 10010010001
  | 4968 => 101001111111000
  | 4969 => 11000001110111
  | 4970 => 110001010
  | 4971 => 110101000000011
  | 4972 => 10011011000100
  | 4973 => 1101001000101
  | 4974 => 110000010
  | 4975 => 11100001100
  | 4976 => 1010100010000
  | 4977 => 1110110110011
  | 4978 => 100111000110010
  | 4979 => 100101001111111
  | 4980 => 111110000100
  | 4981 => 10000010011
  | 4982 => 101100000010
  | 4983 => 101001010011
  | 4984 => 1101001111000
  | 4985 => 1111100000010
  | 4986 => 10111011101010
  | 4987 => 10111010110111
  | 4988 => 110110100
  | 4989 => 101111110101
  | 4990 => 111000000110
  | 4991 => 1101100001001
  | 4992 => 101010000000
  | 4993 => 10110111001
  | 4994 => 1000110001110
  | 4995 => 1111111111111111111111111110
  | 4996 => 11110011000100
  | 4997 => 11100001001
  | 4998 => 111111100000110
  | 4999 => 111100000000111
  | _ => 1

def witness_fast_5 : Nat → Nat
  | 5000 => 10000
  | 5001 => 100000001001
  | 5002 => 11100001000110
  | 5003 => 11101100001001
  | 5004 => 10011110111100
  | 5005 => 10010
  | 5006 => 101110000001110
  | 5007 => 110001001101
  | 5008 => 110010110000
  | 5009 => 101101100001
  | 5010 => 1000001010
  | 5011 => 110101011010111
  | 5012 => 1101011100
  | 5013 => 10111111100001
  | 5014 => 111001010010
  | 5015 => 1111100000010
  | 5016 => 111100011000
  | 5017 => 110001001101
  | 5018 => 10111001010110
  | 5019 => 111000010111011
  | 5020 => 11000100100
  | 5021 => 11001011
  | 5022 => 11001110111010
  | 5023 => 10100101010111
  | 5024 => 1010110101100000
  | 5025 => 1001000100
  | 5026 => 1010001011110
  | 5027 => 111001001001
  | 5028 => 11111000100
  | 5029 => 11011111011101
  | 5030 => 11010001010
  | 5031 => 1011110110101
  | 5032 => 100011000
  | 5033 => 100001001110101
  | 5034 => 1111000100010
  | 5035 => 111111101110
  | 5036 => 10000111100
  | 5037 => 100011010101
  | 5038 => 100001000110
  | 5039 => 1000011011101
  | 5040 => 11110111110000
  | 5041 => 111001111101
  | 5042 => 10011110100110
  | 5043 => 1011010110100011
  | 5044 => 111011000100
  | 5045 => 100100011111110
  | 5046 => 1100010011010
  | 5047 => 10001010100011
  | 5048 => 101011111000
  | 5049 => 11111111111110110111
  | 5050 => 10100
  | 5051 => 10000010011011
  | 5052 => 10101010100100
  | 5053 => 11100011001
  | 5054 => 111011110
  | 5055 => 10110
  | 5056 => 10010011000000
  | 5057 => 101011011101
  | 5058 => 1110111100110
  | 5059 => 100010000011
  | 5060 => 1111100100
  | 5061 => 1001111101011
  | 5062 => 1011010000110
  | 5063 => 110100000010011
  | 5064 => 110001010011000
  | 5065 => 100001101010
  | 5066 => 100100010110110
  | 5067 => 11101010110101
  | 5068 => 10101111001100
  | 5069 => 1110111
  | 5070 => 101111010
  | 5071 => 1111010111101
  | 5072 => 10000001111110000
  | 5073 => 10000000110111
  | 5074 => 1110001001110
  | 5075 => 1101011100
  | 5076 => 11110110101100
  | 5077 => 1011110001001
  | 5078 => 11001001010010
  | 5079 => 1101001000101111
  | 5080 => 11010011000
  | 5081 => 11100110111
  | 5082 => 11111101111110
  | 5083 => 10001101111001
  | 5084 => 100100100100100
  | 5085 => 1100111101110
  | 5086 => 100001110010
  | 5087 => 101000111111
  | 5088 => 10001100000
  | 5089 => 110100001011
  | 5090 => 1001011000110
  | 5091 => 10100010010101
  | 5092 => 10111100000100
  | 5093 => 101111110001
  | 5094 => 11011111010010
  | 5095 => 11011100010
  | 5096 => 10111101000
  | 5097 => 1110110101011
  | 5098 => 11101110110110
  | 5099 => 11011111010101
  | 5100 => 10001100
  | 5101 => 1100000100111
  | 5102 => 100001000011110
  | 5103 => 101010111010011
  | 5104 => 1111010010000
  | 5105 => 100111000110
  | 5106 => 100001010
  | 5107 => 101001001111
  | 5108 => 101101011100100
  | 5109 => 10101110111001
  | 5110 => 100110010
  | 5111 => 10000111000001
  | 5112 => 100111011111000
  | 5113 => 100010111000011
  | 5114 => 10011011011110
  | 5115 => 100100110110
  | 5116 => 100101000101100
  | 5117 => 10011010110101
  | 5118 => 11010001000110
  | 5119 => 11100001100001
  | 5120 => 10000000000
  | 5121 => 10001110111101
  | 5122 => 110101001010
  | 5123 => 10110000011011
  | 5124 => 11001000110100
  | 5125 => 11111000
  | 5126 => 10011001110
  | 5127 => 101000111000001
  | 5128 => 1110001111000
  | 5129 => 10010011101011
  | 5130 => 1101011101110
  | 5131 => 101111100000001
  | 5132 => 111101000100
  | 5133 => 101011111011
  | 5134 => 1010010100110
  | 5135 => 111010110100110
  | 5136 => 1101001110000
  | 5137 => 10011001011
  | 5138 => 1101110111010
  | 5139 => 111001110111
  | 5140 => 10100100
  | 5141 => 101111011100101
  | 5142 => 100100111010
  | 5143 => 1101110010111
  | 5144 => 10011000101000
  | 5145 => 11000010
  | 5146 => 1001000100110
  | 5147 => 1111111111001
  | 5148 => 11111111111111111100
  | 5149 => 1011001001
  | 5150 => 1110000100
  | 5151 => 10101111
  | 5152 => 1110111100000
  | 5153 => 1001001101011
  | 5154 => 11101011010110
  | 5155 => 10011010
  | 5156 => 1010010000100
  | 5157 => 1100001111111
  | 5158 => 10000101101110
  | 5159 => 1100100001
  | 5160 => 100100001000
  | 5161 => 101000001011
  | 5162 => 111110011010
  | 5163 => 10100000001
  | 5164 => 1011101001100
  | 5165 => 1110110010110
  | 5166 => 1110011110110
  | 5167 => 100001100101
  | 5168 => 110101010000
  | 5169 => 1011011011011
  | 5170 => 10011100110
  | 5171 => 1100000101101
  | 5172 => 10101010001100
  | 5173 => 10011110000101
  | 5174 => 101010010010
  | 5175 => 1101111101100
  | 5176 => 10110011001000
  | 5177 => 1010100001
  | 5178 => 10100010010110
  | 5179 => 1000010101001
  | 5180 => 1010100
  | 5181 => 1101001000011
  | 5182 => 11000000100010
  | 5183 => 11001010001001
  | 5184 => 1111111101000000
  | 5185 => 10100100010
  | 5186 => 101101100001010
  | 5187 => 10110101001
  | 5188 => 1100000001111100
  | 5189 => 110000101001
  | 5190 => 10110011010
  | 5191 => 11010111
  | 5192 => 100101111000
  | 5193 => 110111110101
  | 5194 => 10001001111010
  | 5195 => 101010011110
  | 5196 => 1000100100
  | 5197 => 101100011001
  | 5198 => 10110110
  | 5199 => 10111010001
  | 5200 => 10010000
  | 5201 => 1111011100101
  | 5202 => 11011110100110
  | 5203 => 111000110001
  | 5204 => 1100101011100
  | 5205 => 101010010110
  | 5206 => 1010101100010
  | 5207 => 1111000110101
  | 5208 => 10000011000
  | 5209 => 110111111111101
  | 5210 => 10101101110
  | 5211 => 10010111101011
  | 5212 => 110111010101100
  | 5213 => 11010101011
  | 5214 => 1011100001010
  | 5215 => 110001111010
  | 5216 => 101011100000
  | 5217 => 100111011111
  | 5218 => 10000010010
  | 5219 => 1011011001001
  | 5220 => 1011110111100
  | 5221 => 100110101000011
  | 5222 => 101111001110
  | 5223 => 110111010001011
  | 5224 => 11101000
  | 5225 => 10011100
  | 5226 => 1011111101110110
  | 5227 => 1000100011101
  | 5228 => 11011010100100
  | 5229 => 101111100010011
  | 5230 => 1101110011010
  | 5231 => 111100011101
  | 5232 => 10010101110000
  | 5233 => 10101111110111
  | 5234 => 10100010100110
  | 5235 => 10111010011110
  | 5236 => 10011101100
  | 5237 => 10000101110101
  | 5238 => 10111010110110
  | 5239 => 10101101101
  | 5240 => 101001000
  | 5241 => 110000000001
  | 5242 => 11000101110
  | 5243 => 101001011000001
  | 5244 => 11001111110100
  | 5245 => 1000010011110
  | 5246 => 101000110110
  | 5247 => 11011111111111101111
  | 5248 => 111110000000
  | 5249 => 111011101
  | 5250 => 10101000
  | 5251 => 1110100000101
  | 5252 => 10110100
  | 5253 => 10010111111001
  | 5254 => 1001110111110
  | 5255 => 10100110
  | 5256 => 101111001111000
  | 5257 => 101101010101
  | 5258 => 111111111111110
  | 5259 => 100100011101
  | 5260 => 1000110100
  | 5261 => 111111010011
  | 5262 => 11110110001110
  | 5263 => 1101000111111
  | 5264 => 111100010000
  | 5265 => 10110110111010
  | 5266 => 101001011110
  | 5267 => 10000100011
  | 5268 => 1010001110100
  | 5269 => 100111
  | 5270 => 11011101110
  | 5271 => 100001101011
  | 5272 => 11110100111000
  | 5273 => 111111111011
  | 5274 => 11011001111010
  | 5275 => 11010001100
  | 5276 => 11000101100100
  | 5277 => 1011011000001
  | 5278 => 10101010010
  | 5279 => 10000110001
  | 5280 => 11111100000
  | 5281 => 10110110111
  | 5282 => 10011001010
  | 5283 => 1101011101011
  | 5284 => 1000111001111100
  | 5285 => 11111110010
  | 5286 => 101110000110
  | 5287 => 10110001000111
  | 5288 => 101000100001000
  | 5289 => 1001110000000011
  | 5290 => 10001110010
  | 5291 => 111111
  | 5292 => 110001111110100
  | 5293 => 110111110001
  | 5294 => 10100100010110
  | 5295 => 101011010010
  | 5296 => 1110111110000
  | 5297 => 1011100010001
  | 5298 => 100101001111110
  | 5299 => 100110110110101
  | 5300 => 10001100
  | 5301 => 10011001110111
  | 5302 => 10010000000110
  | 5303 => 111011100010111
  | 5304 => 100111011000
  | 5305 => 10000111110010
  | 5306 => 1001110001010
  | 5307 => 11000110111011
  | 5308 => 111101110111100
  | 5309 => 10011110101001
  | 5310 => 1010111110110
  | 5311 => 1100010001100111
  | 5312 => 101011000000
  | 5313 => 10010101101
  | 5314 => 10010001010110
  | 5315 => 100000001101010
  | 5316 => 11000000100
  | 5317 => 11111110111101
  | 5318 => 111110011010
  | 5319 => 1001110101111
  | 5320 => 11101111000
  | 5321 => 1100100100011011
  | 5322 => 11110110100110
  | 5323 => 1100000010001
  | 5324 => 110111101100
  | 5325 => 1001100
  | 5326 => 10111110001110
  | 5327 => 111000100001
  | 5328 => 1111111110000
  | 5329 => 11001110111011
  | 5330 => 10111010
  | 5331 => 10111000000011
  | 5332 => 101001010100
  | 5333 => 100000000100011
  | 5334 => 10011100111110
  | 5335 => 111000010
  | 5336 => 1110110111000
  | 5337 => 1111001011101
  | 5338 => 11010010110010
  | 5339 => 10000110101111
  | 5340 => 101111111100
  | 5341 => 1001111010011
  | 5342 => 11010010000110
  | 5343 => 1000001100111
  | 5344 => 1111101100000
  | 5345 => 11000010
  | 5346 => 11111111111111110110
  | 5347 => 110011111010011
  | 5348 => 1110111100
  | 5349 => 101011110001101
  | 5350 => 10001001100
  | 5351 => 110001000100001
  | 5352 => 1001111001000
  | 5353 => 1001011
  | 5354 => 11101000010010
  | 5355 => 1110111110010
  | 5356 => 111011000100
  | 5357 => 101101110111001
  | 5358 => 1011111100110
  | 5359 => 101111111110111
  | 5360 => 11010110000
  | 5361 => 101001110001111
  | 5362 => 11100110010010
  | 5363 => 1101010101001
  | 5364 => 1011110111100
  | 5365 => 1000111110
  | 5366 => 10110000110
  | 5367 => 10010001001011
  | 5368 => 1101111000
  | 5369 => 11101100101
  | 5370 => 110101110
  | 5371 => 1111000110101
  | 5372 => 11000110100
  | 5373 => 10101110011011
  | 5374 => 100000010010
  | 5375 => 1101101000
  | 5376 => 1010100000000
  | 5377 => 11101001001001
  | 5378 => 101111111101110
  | 5379 => 100100011011
  | 5380 => 10010001100
  | 5381 => 1010010100111
  | 5382 => 1111101010110
  | 5383 => 100011010001
  | 5384 => 100100001000
  | 5385 => 10010101110
  | 5386 => 10000001110110
  | 5387 => 11011101010011
  | 5388 => 110111011100100
  | 5389 => 10110111100101
  | 5390 => 101111010
  | 5391 => 10011011100111
  | 5392 => 10110000
  | 5393 => 10100001000001
  | 5394 => 111011110010010
  | 5395 => 101000000010
  | 5396 => 10111111001100
  | 5397 => 1010011111011
  | 5398 => 100111011110
  | 5399 => 100100100111
  | 5400 => 1101111111000
  | 5401 => 1101111111111
  | 5402 => 11101110
  | 5403 => 11011010011011
  | 5404 => 10101111001100
  | 5405 => 10100010010
  | 5406 => 1000110
  | 5407 => 1011000011101
  | 5408 => 1011110100000
  | 5409 => 111011011101
  | 5410 => 101010110
  | 5411 => 10111000011
  | 5412 => 1001110001100
  | 5413 => 11011000101
  | 5414 => 1110001100010
  | 5415 => 1101110110110
  | 5416 => 1001010110101000
  | 5417 => 11101110011111
  | 5418 => 10111101101010
  | 5419 => 10000000101111011
  | 5420 => 1111100
  | 5421 => 101001111001011
  | 5422 => 1100110001010
  | 5423 => 111101001
  | 5424 => 10101010110000
  | 5425 => 1000001100
  | 5426 => 11111010110
  | 5427 => 1110111101001
  | 5428 => 110110101100
  | 5429 => 1110011000101
  | 5430 => 111100010010
  | 5431 => 110001000111
  | 5432 => 1110110001000
  | 5433 => 10001000101101
  | 5434 => 10000000010
  | 5435 => 100010011110
  | 5436 => 1111110110100
  | 5437 => 101110111101
  | 5438 => 10011110000010
  | 5439 => 10111101
  | 5440 => 11101000000
  | 5441 => 11001000111
  | 5442 => 100010110110
  | 5443 => 100010101111
  | 5444 => 111010101100
  | 5445 => 100111111111111111110
  | 5446 => 1010110111010
  | 5447 => 100101000110111
  | 5448 => 11011110111000
  | 5449 => 1000011100101
  | 5450 => 100101011100
  | 5451 => 1110110110011
  | 5452 => 11010000101100
  | 5453 => 11100101100011
  | 5454 => 10111111111111111110
  | 5455 => 1000001010110
  | 5456 => 110010010000
  | 5457 => 101001010011
  | 5458 => 100111110000010
  | 5459 => 110000100111
  | 5460 => 1010100
  | 5461 => 1100010000001
  | 5462 => 101101101110
  | 5463 => 11001101101101
  | 5464 => 100000111101000
  | 5465 => 1111111010
  | 5466 => 100010010001110
  | 5467 => 11011101101
  | 5468 => 1110100100100
  | 5469 => 1010011111000101
  | 5470 => 1001010
  | 5471 => 11010010001
  | 5472 => 111101111100000
  | 5473 => 11100101110111
  | 5474 => 100011011110010
  | 5475 => 111011100
  | 5476 => 1010011100100
  | 5477 => 1110000110101
  | 5478 => 11111000010
  | 5479 => 1000100000011
  | 5480 => 10001000
  | 5481 => 10101111010011
  | 5482 => 1110011011110
  | 5483 => 10010101001111
  | 5484 => 10110101000100
  | 5485 => 11110010110
  | 5486 => 10011110011110
  | 5487 => 10000001110101
  | 5488 => 11000010000
  | 5489 => 110101101011
  | 5490 => 1110110111010
  | 5491 => 101011100100101
  | 5492 => 10011111010100
  | 5493 => 10101001111101
  | 5494 => 1010000011010
  | 5495 => 100101111111111110
  | 5496 => 11110111101000
  | 5497 => 100101101101
  | 5498 => 110000101010010
  | 5499 => 1100011101111
  | 5500 => 11000
  | 5501 => 110010101011011
  | 5502 => 10100111110110
  | 5503 => 10100110101111
  | 5504 => 11011010000000
  | 5505 => 11010
  | 5506 => 1010001011110
  | 5507 => 1000000011011
  | 5508 => 11110110101100
  | 5509 => 10110001111
  | 5510 => 10100111010
  | 5511 => 1100001111
  | 5512 => 100111011000
  | 5513 => 10111101111
  | 5514 => 101110111111110
  | 5515 => 11101000110
  | 5516 => 1101010010100
  | 5517 => 100001111011011
  | 5518 => 11011101101010
  | 5519 => 110010111101
  | 5520 => 100001010000
  | 5521 => 101011100101001
  | 5522 => 1100010010
  | 5523 => 101100100101
  | 5524 => 100001110100
  | 5525 => 10011101100
  | 5526 => 10111110001110
  | 5527 => 100000011
  | 5528 => 10010110001000
  | 5529 => 101111010101001
  | 5530 => 1100011010
  | 5531 => 1001111
  | 5532 => 110100010001100
  | 5533 => 11010100101
  | 5534 => 1111100001010
  | 5535 => 11010111001110
  | 5536 => 101100110100000
  | 5537 => 10110000011111
  | 5538 => 10001111000010
  | 5539 => 10110101010011
  | 5540 => 11011110100
  | 5541 => 1001100001111101
  | 5542 => 1010111010101110
  | 5543 => 1111001100111
  | 5544 => 111111111111111111000
  | 5545 => 11000101011010
  | 5546 => 101101001110
  | 5547 => 10110001101111
  | 5548 => 10101011000100
  | 5549 => 1101010101001
  | 5550 => 11100
  | 5551 => 1010010001
  | 5552 => 10101111010000
  | 5553 => 10111110010011
  | 5554 => 1111101110110
  | 5555 => 11110
  | 5556 => 11101110101100
  | 5557 => 111101101
  | 5558 => 1010000010110
  | 5559 => 10110110101011
  | 5560 => 110110101000
  | 5561 => 10001000001111
  | 5562 => 10110101101110
  | 5563 => 11010111011011
  | 5564 => 1101011111001100
  | 5565 => 1001110110
  | 5566 => 1000000000010
  | 5567 => 1000111010001
  | 5568 => 11010111000000
  | 5569 => 110000110000101
  | 5570 => 11101010
  | 5571 => 111101010111
  | 5572 => 1010100100100
  | 5573 => 10011101111001
  | 5574 => 101001110011110
  | 5575 => 100111100100
  | 5576 => 10011011000
  | 5577 => 10111101
  | 5578 => 100010001010010
  | 5579 => 1010001010011
  | 5580 => 1111101011100
  | 5581 => 1010111101010111
  | 5582 => 1011110111110
  | 5583 => 100111101111
  | 5584 => 11001000010000
  | 5585 => 110111101010
  | 5586 => 1010011000110
  | 5587 => 1010000110101
  | 5588 => 10000010010100
  | 5589 => 100001111011101
  | 5590 => 1100111100010
  | 5591 => 100010100011001
  | 5592 => 1001100111000
  | 5593 => 11111101100001
  | 5594 => 11100010100010
  | 5595 => 1010110110
  | 5596 => 10001101110100
  | 5597 => 110100010110011
  | 5598 => 111011111010
  | 5599 => 100101100011
  | 5600 => 100100000
  | 5601 => 101010111001011
  | 5602 => 1101101110
  | 5603 => 101111110111011
  | 5604 => 1001100101100
  | 5605 => 1001000100010
  | 5606 => 10101100100010
  | 5607 => 11101100100111
  | 5608 => 10110110111000
  | 5609 => 1100111001011
  | 5610 => 1001110110
  | 5611 => 11011001100001
  | 5612 => 10111000100
  | 5613 => 110101111101
  | 5614 => 110101010110
  | 5615 => 1000110110
  | 5616 => 10110010111110000
  | 5617 => 1010001100011
  | 5618 => 1100001001110
  | 5619 => 1111111000011
  | 5620 => 10100011100
  | 5621 => 10011001
  | 5622 => 10010010101010
  | 5623 => 1000101001001111
  | 5624 => 10100001000
  | 5625 => 1111111110000
  | 5626 => 10111100000010
  | 5627 => 1000011100001
  | 5628 => 100000111010100
  | 5629 => 100111101110111
  | 5630 => 11010011110
  | 5631 => 110110100001
  | 5632 => 11000000000
  | 5633 => 10010100101101
  | 5634 => 10001110111110
  | 5635 => 1101000110
  | 5636 => 10001010000100
  | 5637 => 101011111011
  | 5638 => 111110011110
  | 5639 => 10000001000111
  | 5640 => 10011000
  | 5641 => 100010000110101
  | 5642 => 100100110110
  | 5643 => 11011111101111111111
  | 5644 => 10010001001100
  | 5645 => 1000000110010
  | 5646 => 100110001111110
  | 5647 => 111111010111
  | 5648 => 101011010010000
  | 5649 => 10110011001111
  | 5650 => 101101100
  | 5651 => 11011010011111
  | 5652 => 11011110110100
  | 5653 => 11101011010101
  | 5654 => 11110110
  | 5655 => 1011100100010
  | 5656 => 101101000
  | 5657 => 1111011001001
  | 5658 => 111001110011010
  | 5659 => 1101010111011
  | 5660 => 1001011101100
  | 5661 => 100111111011
  | 5662 => 10101010010010
  | 5663 => 11100111011101
  | 5664 => 10010111100000
  | 5665 => 111000010
  | 5666 => 1010110101100110
  | 5667 => 110000110101111
  | 5668 => 10100100110100
  | 5669 => 10101111100101
  | 5670 => 10110110111010
  | 5671 => 110000010111011
  | 5672 => 111011100001000
  | 5673 => 1001011101111
  | 5674 => 11110111110010
  | 5675 => 1100110100
  | 5676 => 110110001100
  | 5677 => 111101011001001
  | 5678 => 1110110010110
  | 5679 => 1111101001101
  | 5680 => 100110000
  | 5681 => 110101000110101
  | 5682 => 10110011010
  | 5683 => 1100010101111
  | 5684 => 10110101101100
  | 5685 => 1001110001010
  | 5686 => 1111001101110
  | 5687 => 111011110111
  | 5688 => 11111011011000
  | 5689 => 111101101101
  | 5690 => 10110100110
  | 5691 => 1111111111011111
  | 5692 => 1000111010100
  | 5693 => 101101111001011
  | 5694 => 10000011001110
  | 5695 => 111101010010
  | 5696 => 11010101000000
  | 5697 => 11011101001011
  | 5698 => 1111110
  | 5699 => 100100110000001
  | 5700 => 1100100
  | 5701 => 1000111100011
  | 5702 => 10111100010
  | 5703 => 1001101010001
  | 5704 => 1100000001000
  | 5705 => 1001000110110
  | 5706 => 10011111010110
  | 5707 => 10011101111011
  | 5708 => 1101111110110100
  | 5709 => 1011001101
  | 5710 => 10000100010
  | 5711 => 101010100011101
  | 5712 => 1001110110000
  | 5713 => 10100000000001
  | 5714 => 1110010011010
  | 5715 => 111111110010
  | 5716 => 1001110100100
  | 5717 => 110001100001
  | 5718 => 1010100110010
  | 5719 => 110100110110011
  | 5720 => 1001000
  | 5721 => 11011100001
  | 5722 => 1001011000110
  | 5723 => 10000100000001
  | 5724 => 1111110110100
  | 5725 => 1000010001100
  | 5726 => 10111111001110
  | 5727 => 1001001100011
  | 5728 => 1101011100000
  | 5729 => 101100001011
  | 5730 => 100000000110
  | 5731 => 100000110111
  | 5732 => 110110010001100
  | 5733 => 11111110101
  | 5734 => 11101110010
  | 5735 => 1110101010
  | 5736 => 101000011111011000
  | 5737 => 11011110000101
  | 5738 => 11001101000010
  | 5739 => 1001101111011
  | 5740 => 101110100
  | 5741 => 110100100001
  | 5742 => 11110111111111111110
  | 5743 => 11000010111
  | 5744 => 10010101110000
  | 5745 => 101001110010
  | 5746 => 10110001011110
  | 5747 => 100000001101
  | 5748 => 1100111110010100
  | 5749 => 1011101000011
  | 5750 => 110101000
  | 5751 => 110000011111011
  | 5752 => 101000000001000
  | 5753 => 1011000101001
  | 5754 => 110011100010
  | 5755 => 1101000111110
  | 5756 => 11001011100
  | 5757 => 1111101
  | 5758 => 10001010000110
  | 5759 => 110110001001
  | 5760 => 1111111110000000
  | 5761 => 1100011101
  | 5762 => 101000110110
  | 5763 => 111001011010011
  | 5764 => 111101100
  | 5765 => 1001000010
  | 5766 => 11000000010
  | 5767 => 1000010101011
  | 5768 => 1110110001000
  | 5769 => 1011101010111
  | 5770 => 1100010110
  | 5771 => 1100000101101
  | 5772 => 1010100
  | 5773 => 100001101011
  | 5774 => 11001000110
  | 5775 => 11111100
  | 5776 => 111011110000
  | 5777 => 1110010111
  | 5778 => 1110101110110
  | 5779 => 111000101001001
  | 5780 => 110011000100
  | 5781 => 1100111101000011
  | 5782 => 101000011010010
  | 5783 => 1010100111101
  | 5784 => 10001011011000
  | 5785 => 111110100010
  | 5786 => 100011010
  | 5787 => 1110110100111
  | 5788 => 100101000100
  | 5789 => 11001011001001
  | 5790 => 110010
  | 5791 => 1010010111001
  | 5792 => 100111100000
  | 5793 => 10110100011
  | 5794 => 110111001110
  | 5795 => 100010110
  | 5796 => 11111010101100
  | 5797 => 1000010111111
  | 5798 => 10100000011010
  | 5799 => 11000101000011
  | 5800 => 1101101000
  | 5801 => 1110110111101
  | 5802 => 110110011100110
  | 5803 => 11011001001
  | 5804 => 101011011101100
  | 5805 => 1010111111010
  | 5806 => 1111101100110
  | 5807 => 1011000111101
  | 5808 => 10001111010000
  | 5809 => 1010110100001
  | 5810 => 101000000010
  | 5811 => 101000110000101
  | 5812 => 100001100110100
  | 5813 => 11110100011011
  | 5814 => 1111011010110
  | 5815 => 10011010111010
  | 5816 => 101100010001000
  | 5817 => 1111011011111001
  | 5818 => 100011100010
  | 5819 => 10111000010001
  | 5820 => 10011011100
  | 5821 => 10011111110101
  | 5822 => 101100110010110
  | 5823 => 10101011110011
  | 5824 => 1001000000
  | 5825 => 11111001100
  | 5826 => 110101101001110
  | 5827 => 1010010010001
  | 5828 => 110111011010100
  | 5829 => 11000010000111
  | 5830 => 10010110
  | 5831 => 110000101100001
  | 5832 => 101111111001000
  | 5833 => 101100001001111
  | 5834 => 10010110011010
  | 5835 => 110101000110
  | 5836 => 1001011000100
  | 5837 => 10110110101
  | 5838 => 1001111011110
  | 5839 => 11100111011101
  | 5840 => 100010000
  | 5841 => 11011110111111111111
  | 5842 => 1010111010
  | 5843 => 100100101101011
  | 5844 => 1111111100100
  | 5845 => 1001001011010
  | 5846 => 1010101110
  | 5847 => 10110001000011
  | 5848 => 1101011001000
  | 5849 => 11001110010011
  | 5850 => 1010111111100
  | 5851 => 1100100111011
  | 5852 => 100000000100
  | 5853 => 1011011111011011
  | 5854 => 100000100111110
  | 5855 => 1000101110010
  | 5856 => 10010100000
  | 5857 => 10111011100101
  | 5858 => 110101110
  | 5859 => 11100001111101
  | 5860 => 11000011100
  | 5861 => 10111110011
  | 5862 => 10111100010
  | 5863 => 11010110111
  | 5864 => 10001101111000
  | 5865 => 10111111111110
  | 5866 => 11101011010110
  | 5867 => 10000011101101
  | 5868 => 101010011111100
  | 5869 => 11011001101
  | 5870 => 100101110
  | 5871 => 10011001000101
  | 5872 => 11010000
  | 5873 => 11100011111
  | 5874 => 1010010011010
  | 5875 => 10011000
  | 5876 => 110110001010100
  | 5877 => 1000011101111001
  | 5878 => 101100101110
  | 5879 => 1101011001101
  | 5880 => 1100001000
  | 5881 => 1010100100001
  | 5882 => 10110011010
  | 5883 => 100011
  | 5884 => 10011101000100
  | 5885 => 1101001110
  | 5886 => 1101111001110
  | 5887 => 1000000100001
  | 5888 => 11010100000000
  | 5889 => 100111010101011
  | 5890 => 110110010110
  | 5891 => 1000111011101
  | 5892 => 10010101010100
  | 5893 => 100001010101
  | 5894 => 1000111101010
  | 5895 => 10011001111110
  | 5896 => 110110011000
  | 5897 => 1110010001
  | 5898 => 1100101110110010
  | 5899 => 11010100000111
  | 5900 => 1101111100
  | 5901 => 11010110000001
  | 5902 => 10111001001010
  | 5903 => 100010111000001
  | 5904 => 1110011110110000
  | 5905 => 1010100100010
  | 5906 => 1101101100111110
  | 5907 => 10000110001101
  | 5908 => 11010001100
  | 5909 => 10100100001001
  | 5910 => 110101001010
  | 5911 => 1000101011111
  | 5912 => 110111000
  | 5913 => 100011101001111
  | 5914 => 1000001010010
  | 5915 => 101111010
  | 5916 => 11110100100
  | 5917 => 10010011101101
  | 5918 => 1001000110
  | 5919 => 1000100100111
  | 5920 => 11100000
  | 5921 => 1010010101
  | 5922 => 11001111110010
  | 5923 => 11010010011
  | 5924 => 1001011010100
  | 5925 => 10101011100
  | 5926 => 10010111110010
  | 5927 => 100100100110111
  | 5928 => 10110101001000
  | 5929 => 11110110011
  | 5930 => 10010000110
  | 5931 => 1001111111001
  | 5932 => 1101001000100
  | 5933 => 101001001001
  | 5934 => 111111011101010010
  | 5935 => 1000100001010
  | 5936 => 1001110110000
  | 5937 => 101000010100011
  | 5938 => 110011100111010
  | 5939 => 1010010110010101
  | 5940 => 111101111111111111100
  | 5941 => 100010000110111
  | 5942 => 11101000110110
  | 5943 => 100001000110011
  | 5944 => 10110001000
  | 5945 => 1000100110010
  | 5946 => 1100010
  | 5947 => 1000000011100001
  | 5948 => 10101001110100
  | 5949 => 111011011101
  | 5950 => 10011101100
  | 5951 => 100111001001
  | 5952 => 10000011000000
  | 5953 => 100010010001111
  | 5954 => 100101001110110
  | 5955 => 110001010110
  | 5956 => 11101001111100
  | 5957 => 10010101101
  | 5958 => 111111010110
  | 5959 => 10010101011
  | 5960 => 110111000
  | 5961 => 11000100001101
  | 5962 => 11111111110
  | 5963 => 10111000110001
  | 5964 => 10010100011100
  | 5965 => 110111001010
  | 5966 => 100001111100110
  | 5967 => 10000111011111
  | 5968 => 1010110110000
  | 5969 => 1001000101001001
  | 5970 => 11000101110
  | 5971 => 1101000100011
  | 5972 => 1010010010101100
  | 5973 => 11110001001
  | 5974 => 1001010101010
  | 5975 => 111111100
  | 5976 => 100110111111000
  | 5977 => 111010111010101
  | 5978 => 10100100010
  | 5979 => 1000101110100111
  | 5980 => 1001010110100
  | 5981 => 11100111111101
  | 5982 => 1111100000010
  | 5983 => 1010001101111
  | 5984 => 100101100000
  | 5985 => 11110111110
  | 5986 => 10100011000110
  | 5987 => 10010000111001
  | 5988 => 111010010000100
  | 5989 => 1101101001111
  | 5990 => 101011101110
  | 5991 => 1000001011101
  | 5992 => 11011100111011000
  | 5993 => 10011000000001
  | 5994 => 11111101111111111111111111110
  | 5995 => 11111001110
  | 5996 => 11001011100
  | 5997 => 1010000101101111
  | 5998 => 1010000101010010
  | 5999 => 11001110110011
  | _ => 1

def witness_fast_6 : Nat → Nat
  | 6000 => 1110000
  | 6001 => 110001001111111
  | 6002 => 110010001111110
  | 6003 => 1110111000111
  | 6004 => 110100001100
  | 6005 => 101111001010
  | 6006 => 1111110
  | 6007 => 100011111100011
  | 6008 => 1111000111000
  | 6009 => 100001111001
  | 6010 => 110010111110
  | 6011 => 100111000111101
  | 6012 => 100110101111100
  | 6013 => 1110101101011
  | 6014 => 101011110111110
  | 6015 => 1010001110010
  | 6016 => 100110000000
  | 6017 => 1101111
  | 6018 => 1111100000010
  | 6019 => 1011001011111
  | 6020 => 110100111100
  | 6021 => 10111011111
  | 6022 => 10100011111110
  | 6023 => 100010100011111
  | 6024 => 1110010101000
  | 6025 => 11110100
  | 6026 => 100000010111110
  | 6027 => 100001000110011
  | 6028 => 11001100
  | 6029 => 111001101100001
  | 6030 => 11111101110
  | 6031 => 100000011
  | 6032 => 111000110000
  | 6033 => 10010010111111
  | 6034 => 1110011110110
  | 6035 => 1111101110110
  | 6036 => 1101010010100
  | 6037 => 1100100010101
  | 6038 => 10001011110
  | 6039 => 11111111111001111111
  | 6040 => 1110001000
  | 6041 => 101010010100111
  | 6042 => 1011110000010
  | 6043 => 10010010000111
  | 6044 => 1011010100
  | 6045 => 100100110110
  | 6046 => 100001011011110
  | 6047 => 10010101001
  | 6048 => 101011101011100000
  | 6049 => 10100111110111
  | 6050 => 1101100
  | 6051 => 10101101011101
  | 6052 => 1101010100
  | 6053 => 1001110010001
  | 6054 => 100100011111110
  | 6055 => 10111001101110
  | 6056 => 101101001011000
  | 6057 => 11111100111
  | 6058 => 101110110010
  | 6059 => 1010001000001
  | 6060 => 101111100
  | 6061 => 1010011101
  | 6062 => 10101010001110
  | 6063 => 100010101101111
  | 6064 => 1001011010000
  | 6065 => 1110001101110
  | 6066 => 1011101110110
  | 6067 => 10000010001111
  | 6068 => 1000110011100
  | 6069 => 10000000111101
  | 6070 => 10010110101010
  | 6071 => 100100111111
  | 6072 => 11111001000
  | 6073 => 1011101100111
  | 6074 => 100110110110110
  | 6075 => 10011111011100
  | 6076 => 1001001101100
  | 6077 => 10100001000111
  | 6078 => 1010010100110
  | 6079 => 1000111001
  | 6080 => 11001000000
  | 6081 => 10001001111
  | 6082 => 1101011110010
  | 6083 => 100101101111011
  | 6084 => 11111010101100
  | 6085 => 1010110
  | 6086 => 11100000001010
  | 6087 => 11001110110101
  | 6088 => 11011100011000
  | 6089 => 10000000010111
  | 6090 => 110101110
  | 6091 => 100011010110001
  | 6092 => 1011011110100
  | 6093 => 101100111100101
  | 6094 => 111100110110
  | 6095 => 11000000010
  | 6096 => 1010111010000
  | 6097 => 1100100001
  | 6098 => 1011001110010
  | 6099 => 101011100001111
  | 6100 => 10010100
  | 6101 => 101010010100001
  | 6102 => 10101100111110
  | 6103 => 10001111010101
  | 6104 => 1110010111000
  | 6105 => 1111110
  | 6106 => 1110001100010
  | 6107 => 1000001101010011
  | 6108 => 10010110001100
  | 6109 => 100000100000111
  | 6110 => 11001000010
  | 6111 => 1011101011011
  | 6112 => 1110111100000
  | 6113 => 100101010000101
  | 6114 => 11011100010
  | 6115 => 1001111110
  | 6116 => 101001000100
  | 6117 => 111111101110101
  | 6118 => 111011110
  | 6119 => 101000111011111
  | 6120 => 10111110111000
  | 6121 => 100101011111111
  | 6122 => 1101000101010
  | 6123 => 1100011111011111
  | 6124 => 1011100111100
  | 6125 => 1100001000
  | 6126 => 100111000110
  | 6127 => 1011010100111
  | 6128 => 110101010000
  | 6129 => 11011110111
  | 6130 => 1100010110
  | 6131 => 1101011111
  | 6132 => 1100111000100
  | 6133 => 10000111001101
  | 6134 => 1100001111010
  | 6135 => 111000101010
  | 6136 => 11101100101000
  | 6137 => 100011001111001
  | 6138 => 111110111101111111110
  | 6139 => 10001001000011
  | 6140 => 1000110001100
  | 6141 => 111001100001111
  | 6142 => 101000000010
  | 6143 => 100111101111
  | 6144 => 11100000000000
  | 6145 => 1000011110010
  | 6146 => 100011000110
  | 6147 => 1111110101001
  | 6148 => 11001001111100
  | 6149 => 10011010110101
  | 6150 => 1000110011100
  | 6151 => 1010000111111
  | 6152 => 100011010001000
  | 6153 => 11101101001011
  | 6154 => 11000100011010
  | 6155 => 1000011110010
  | 6156 => 11110110101100
  | 6157 => 100011110011101
  | 6158 => 11001101011110
  | 6159 => 11101010110011
  | 6160 => 10010000
  | 6161 => 11111000001
  | 6162 => 111010110100110
  | 6163 => 10010111001
  | 6164 => 1110101111100
  | 6165 => 101101001011110
  | 6166 => 1110010010110
  | 6167 => 10111000011
  | 6168 => 101001000
  | 6169 => 111010100101
  | 6170 => 11001110
  | 6171 => 1011001101
  | 6172 => 11001000111100
  | 6173 => 11111011101
  | 6174 => 111111101010
  | 6175 => 100000000100
  | 6176 => 1100100000
  | 6177 => 111011000111001
  | 6178 => 10110010001010
  | 6179 => 110100011001
  | 6180 => 111011000100
  | 6181 => 101111001100011
  | 6182 => 10111001010
  | 6183 => 1001011111011
  | 6184 => 10111000011000
  | 6185 => 101100010
  | 6186 => 1010001001111110
  | 6187 => 110000111001101
  | 6188 => 10011101100
  | 6189 => 1000010011101
  | 6190 => 110100100110
  | 6191 => 100000010001011
  | 6192 => 111110111010000
  | 6193 => 100011110001
  | 6194 => 1001110011111010
  | 6195 => 1111100000010
  | 6196 => 1000011010100
  | 6197 => 1010111
  | 6198 => 11010000110010
  | 6199 => 11101101011
  | 6200 => 111011000
  | 6201 => 11111100010101
  | 6202 => 1100111101110
  | 6203 => 101100011101
  | 6204 => 100111001100
  | 6205 => 100111110110
  | 6206 => 100100011100010
  | 6207 => 110011110010011
  | 6208 => 11100001000000
  | 6209 => 1001000010101
  | 6210 => 1010011111110
  | 6211 => 101010101001001
  | 6212 => 100001100111100
  | 6213 => 100100010010101
  | 6214 => 1011111010
  | 6215 => 1001101100010
  | 6216 => 10101000
  | 6217 => 100010100001
  | 6218 => 10001000110
  | 6219 => 111111011001
  | 6220 => 10101000100
  | 6221 => 10011001111011
  | 6222 => 10100110100010
  | 6223 => 1010000100011
  | 6224 => 10110110000
  | 6225 => 111110000100
  | 6226 => 101001001001010
  | 6227 => 11010001000011
  | 6228 => 111111101100
  | 6229 => 1001010011011
  | 6230 => 11010011110
  | 6231 => 11001001111011
  | 6232 => 1011001001000
  | 6233 => 1001001101
  | 6234 => 1001101010010
  | 6235 => 11011010
  | 6236 => 110101101100
  | 6237 => 1001101111111101111111
  | 6238 => 110110100011010
  | 6239 => 110100001101
  | 6240 => 1010100000
  | 6241 => 11000000101111
  | 6242 => 111011011011110
  | 6243 => 10000111111101
  | 6244 => 101000000110100
  | 6245 => 1111001100010
  | 6246 => 11010111110010
  | 6247 => 11101010100001
  | 6248 => 1001110011000
  | 6249 => 100101100011
  | 6250 => 100000
  | 6251 => 10011000010011
  | 6252 => 101110001100
  | 6253 => 10111101
  | 6254 => 10000001001010
  | 6255 => 1001111011110
  | 6256 => 1101110001010000
  | 6257 => 101111101010011
  | 6258 => 100000010101110
  | 6259 => 1011010011
  | 6260 => 1100101100
  | 6261 => 10001011111101
  | 6262 => 10100011110
  | 6263 => 10011011100101
  | 6264 => 1011011101011000
  | 6265 => 110101110
  | 6266 => 1001011101100010
  | 6267 => 10110110110011
  | 6268 => 100011111100
  | 6269 => 1000011001001
  | 6270 => 1111000110
  | 6271 => 11111000010101
  | 6272 => 11000010000000
  | 6273 => 110011000111101
  | 6274 => 100001101011110
  | 6275 => 11000100100
  | 6276 => 100010010110100
  | 6277 => 111000110001011
  | 6278 => 11010011110
  | 6279 => 10010101101
  | 6280 => 10101101011000
  | 6281 => 11000110011
  | 6282 => 10111010011110
  | 6283 => 101110101101
  | 6284 => 10000111110100
  | 6285 => 1111100010
  | 6286 => 101101101010
  | 6287 => 10011101011011
  | 6288 => 1010010000
  | 6289 => 100100010010101
  | 6290 => 1000110
  | 6291 => 1100101011111
  | 6292 => 1101100
  | 6293 => 11101111001001
  | 6294 => 1000010011110
  | 6295 => 1000011110
  | 6296 => 10110001111000
  | 6297 => 1101110000001
  | 6298 => 11001000010
  | 6299 => 100001101000111
  | 6300 => 111101111100
  | 6301 => 11000001001101
  | 6302 => 1000110101010
  | 6303 => 100001110011
  | 6304 => 110100010100000
  | 6305 => 11101100010
  | 6306 => 111111011111010
  | 6307 => 100111011
  | 6308 => 100110010100
  | 6309 => 100110111010101
  | 6310 => 1010111110
  | 6311 => 1101000000111111
  | 6312 => 101100100101000
  | 6313 => 110101100001
  | 6314 => 110101101110
  | 6315 => 1010101010010
  | 6316 => 10000110010100
  | 6317 => 10001110110001
  | 6318 => 11001111010110
  | 6319 => 111100110010001
  | 6320 => 100100110000
  | 6321 => 11111110000011
  | 6322 => 101100000001110
  | 6323 => 110010001001
  | 6324 => 1001001110000100
  | 6325 => 1111100100
  | 6326 => 11001110011110
  | 6327 => 101111110011
  | 6328 => 110011110111000
  | 6329 => 100111011001011
  | 6330 => 1100010100110
  | 6331 => 1100001000111
  | 6332 => 110010110100
  | 6333 => 1011000101001
  | 6334 => 11101111010010
  | 6335 => 1010111100110
  | 6336 => 111111111111111111000000
  | 6337 => 11011000101
  | 6338 => 1000000010011110
  | 6339 => 10110001111101
  | 6340 => 100000011111100
  | 6341 => 100000011101111
  | 6342 => 110011000111110
  | 6343 => 10011011011
  | 6344 => 1010010001000
  | 6345 => 1111011010110
  | 6346 => 110101101010
  | 6347 => 10001100000111
  | 6348 => 101111111111100
  | 6349 => 1100101001111
  | 6350 => 1101001100
  | 6351 => 1000011001101
  | 6352 => 110100010000
  | 6353 => 1100111000001
  | 6354 => 111010011010110
  | 6355 => 10010010010010
  | 6356 => 101110010010100
  | 6357 => 100100011011
  | 6358 => 10000101111110
  | 6359 => 111111010100101
  | 6360 => 100011000
  | 6361 => 10111110000001
  | 6362 => 1100000011010
  | 6363 => 11010111111111111111
  | 6364 => 1111110011100
  | 6365 => 1011110000010
  | 6366 => 11111011001010
  | 6367 => 1000101001001
  | 6368 => 11100001100000
  | 6369 => 1100111001
  | 6370 => 101111010
  | 6371 => 1010001001
  | 6372 => 110000111111100
  | 6373 => 10000110101
  | 6374 => 10011100010
  | 6375 => 100011000
  | 6376 => 10001101101000
  | 6377 => 101101001000111
  | 6378 => 111110111110110
  | 6379 => 1001110111011
  | 6380 => 11110100100
  | 6381 => 10101111010101
  | 6382 => 1100101111110
  | 6383 => 10010000101111101
  | 6384 => 11110111110000
  | 6385 => 10110101110010
  | 6386 => 10010111101010
  | 6387 => 11001011101101
  | 6388 => 100110111011100
  | 6389 => 10110011101
  | 6390 => 1001110111110
  | 6391 => 111100000011
  | 6392 => 1101101101000
  | 6393 => 11000000101101
  | 6394 => 1000010000101110
  | 6395 => 10010100010110
  | 6396 => 110101110011100
  | 6397 => 100011101011
  | 6398 => 110100101011110
  | 6399 => 1111011011001
  | 6400 => 100000000
  | 6401 => 110101111011
  | 6402 => 11101100010
  | 6403 => 1011000001011
  | 6404 => 11111100100
  | 6405 => 1100100011010
  | 6406 => 100100110101010
  | 6407 => 110000010010111
  | 6408 => 1011111111000
  | 6409 => 1001101111101
  | 6410 => 11100011110
  | 6411 => 11101010010111
  | 6412 => 111011111010100
  | 6413 => 10010111001011
  | 6414 => 11000010
  | 6415 => 11110100010
  | 6416 => 11110110010000
  | 6417 => 11111100010101
  | 6418 => 1111010000010
  | 6419 => 1000111011001011
  | 6420 => 11010011100
  | 6421 => 10100111001
  | 6422 => 10010000010010
  | 6423 => 11110001111001
  | 6424 => 110011000
  | 6425 => 10100100
  | 6426 => 11010011101110
  | 6427 => 10011100101
  | 6428 => 10111111101100
  | 6429 => 1100100000111
  | 6430 => 100110001010
  | 6431 => 1001111011101
  | 6432 => 1001000100000
  | 6433 => 111010111110101
  | 6434 => 1010101101010
  | 6435 => 1111111111111111110
  | 6436 => 1000101010001100
  | 6437 => 101111111001001
  | 6438 => 1000111110
  | 6439 => 1000111011101
  | 6440 => 11101111000
  | 6441 => 1101101001111
  | 6442 => 11111100111110
  | 6443 => 1100001000111
  | 6444 => 11111001110100
  | 6445 => 101001000010
  | 6446 => 1101101111110
  | 6447 => 1111010111001
  | 6448 => 1110011110000
  | 6449 => 110100011100001
  | 6450 => 10010000100
  | 6451 => 1000011000000011
  | 6452 => 100100110001100
  | 6453 => 101000111111001
  | 6454 => 11010001000110
  | 6455 => 101110100110
  | 6456 => 1010100111000
  | 6457 => 11000100001
  | 6458 => 100011000110111110
  | 6459 => 10000011111
  | 6460 => 1101010100
  | 6461 => 10100100101
  | 6462 => 1101011101110
  | 6463 => 10001000000011
  | 6464 => 101000000
  | 6465 => 1010101000110
  | 6466 => 1000111111101010
  | 6467 => 1001111001
  | 6468 => 1011110100
  | 6469 => 10010011111101
  | 6470 => 101100110010
  | 6471 => 11000110110111
  | 6472 => 11101000111000
  | 6473 => 1001010010011
  | 6474 => 101000000010
  | 6475 => 1010100
  | 6476 => 1111100110100
  | 6477 => 1001110011111
  | 6478 => 100000000101110
  | 6479 => 10010011001111
  | 6480 => 11111111010000
  | 6481 => 1100111000101
  | 6482 => 1101000110
  | 6483 => 10111001011011
  | 6484 => 10000111100
  | 6485 => 110000000111110
  | 6486 => 1001110111110
  | 6487 => 1010100001001
  | 6488 => 1001010001000
  | 6489 => 100110011110011
  | 6490 => 1001011110
  | 6491 => 110001101101
  | 6492 => 1100111111100
  | 6493 => 100001011001
  | 6494 => 1110010101110
  | 6495 => 100010010
  | 6496 => 1101011100000
  | 6497 => 1101001111
  | 6498 => 1101110110110
  | 6499 => 110011101111
  | 6500 => 1001000
  | 6501 => 11010100101
  | 6502 => 100010001000010
  | 6503 => 1101011010001
  | 6504 => 111111111111111000
  | 6505 => 110010101110
  | 6506 => 11010101100010
  | 6507 => 1111001100111
  | 6508 => 101000010011100
  | 6509 => 101100010101001
  | 6510 => 100000110
  | 6511 => 11010101
  | 6512 => 1111110000
  | 6513 => 100100101101
  | 6514 => 100110111111110110110
  | 6515 => 11011101010110
  | 6516 => 11010111101100
  | 6517 => 1100001001100001
  | 6518 => 100000101110
  | 6519 => 110000100111
  | 6520 => 1010111000
  | 6521 => 10011011101011
  | 6522 => 100010011110
  | 6523 => 1001000011
  | 6524 => 1011101100100
  | 6525 => 1011110111100
  | 6526 => 100011100000110
  | 6527 => 110100001111
  | 6528 => 1000110000000
  | 6529 => 1111011000001
  | 6530 => 111010
  | 6531 => 101110010110011
  | 6532 => 1010010010100
  | 6533 => 1111001111111
  | 6534 => 111110011111111111110
  | 6535 => 1101101010010
  | 6536 => 111010000001000
  | 6537 => 101010111010011
  | 6538 => 1001001111110
  | 6539 => 11010100101
  | 6540 => 100101011100
  | 6541 => 1111101100101
  | 6542 => 11101111001010
  | 6543 => 100011110101101
  | 6544 => 11000010010000
  | 6545 => 1001110110
  | 6546 => 100100101100010
  | 6547 => 1111111011
  | 6548 => 1111011110100
  | 6549 => 101110011
  | 6550 => 10100100
  | 6551 => 1110011011011
  | 6552 => 10101111111000
  | 6553 => 1010101111000111
  | 6554 => 10000110011010
  | 6555 => 1100111111010
  | 6556 => 111001111100
  | 6557 => 11101001
  | 6558 => 100111100110110
  | 6559 => 10111100101011
  | 6560 => 1111100000
  | 6561 => 1001111110101
  | 6562 => 11001000110010
  | 6563 => 1000100110111
  | 6564 => 10010100
  | 6565 => 1011010
  | 6566 => 100010000011110
  | 6567 => 10001101011
  | 6568 => 10000101011000
  | 6569 => 1100100110101
  | 6570 => 1011110011110
  | 6571 => 1101100111011
  | 6572 => 110000000100
  | 6573 => 1101100001001
  | 6574 => 101100001110
  | 6575 => 1000110100
  | 6576 => 11101110000
  | 6577 => 111111101001111
  | 6578 => 100101011010
  | 6579 => 1110101111001
  | 6580 => 1111000100
  | 6581 => 1111011001
  | 6582 => 11010100100010
  | 6583 => 101001010011111
  | 6584 => 1100011101000
  | 6585 => 101000111010
  | 6586 => 111101111010
  | 6587 => 101101001100001
  | 6588 => 11111010011100
  | 6589 => 1110110101111
  | 6590 => 111101001110
  | 6591 => 100111111010001
  | 6592 => 11100001000000
  | 6593 => 100100111111001
  | 6594 => 1000011010010101110
  | 6595 => 1100010110010
  | 6596 => 10100100100100
  | 6597 => 1010011011111
  | 6598 => 11100000111010
  | 6599 => 111011011001
  | 6600 => 111111000
  | 6601 => 10011000101011
  | 6602 => 1111011001010
  | 6603 => 10010011100001
  | 6604 => 101000001111100
  | 6605 => 100011100111110
  | 6606 => 1101110111010
  | 6607 => 1101101101001
  | 6608 => 111011001010000
  | 6609 => 10111111010001
  | 6610 => 1010001000010
  | 6611 => 111101101001
  | 6612 => 101001110100
  | 6613 => 11001001110001
  | 6614 => 10101000010
  | 6615 => 11000111111010
  | 6616 => 1000100001001000
  | 6617 => 11100100100011
  | 6618 => 11101000110
  | 6619 => 11111110111
  | 6620 => 11101111100
  | 6621 => 101010101011101
  | 6622 => 100001100001110
  | 6623 => 111110011101
  | 6624 => 1101111101100000
  | 6625 => 100011000
  | 6626 => 11101101010
  | 6627 => 111100110001101
  | 6628 => 1010111011100
  | 6629 => 1101011001111
  | 6630 => 1001110110
  | 6631 => 10100010110101
  | 6632 => 11000001000
  | 6633 => 111101111111110111101
  | 6634 => 10011110110110
  | 6635 => 11110111011110
  | 6636 => 10101110000100
  | 6637 => 11100101111111
  | 6638 => 100100011110
  | 6639 => 11010100000011
  | 6640 => 1010110000
  | 6641 => 10001011101011
  | 6642 => 11010111001110
  | 6643 => 10011001
  | 6644 => 111111100100
  | 6645 => 1100000010
  | 6646 => 110110110110010
  | 6647 => 11000101110111
  | 6648 => 1011101110101000
  | 6649 => 101000001100011
  | 6650 => 1110111100
  | 6651 => 10001111101011
  | 6652 => 10111111010100
  | 6653 => 101111111010111
  | 6654 => 11111001011010
  | 6655 => 11011110110
  | 6656 => 1001000000000
  | 6657 => 1001111101011
  | 6658 => 111111001010
  | 6659 => 100010001010001
  | 6660 => 11111111100
  | 6661 => 111100001001111
  | 6662 => 1011101100110
  | 6663 => 1000001010111
  | 6664 => 1010010001000
  | 6665 => 10100101010
  | 6666 => 1111111111110
  | 6667 => 1111011101111
  | 6668 => 1111111011100
  | 6669 => 11011110000111
  | 6670 => 11101101110
  | 6671 => 1000100111011001
  | 6672 => 1101101010000
  | 6673 => 101110010011
  | 6674 => 100110
  | 6675 => 101111111100
  | 6676 => 11000100110100
  | 6677 => 1101010011101
  | 6678 => 11110110100110
  | 6679 => 1101100000111
  | 6680 => 11111011000
  | 6681 => 10100100101001
  | 6682 => 100110000000010
  | 6683 => 101001010011001
  | 6684 => 101010000110100
  | 6685 => 111011110
  | 6686 => 1110110010
  | 6687 => 1111011100101
  | 6688 => 10011100000
  | 6689 => 100101000111001
  | 6690 => 10011110010
  | 6691 => 10110101
  | 6692 => 10111110100
  | 6693 => 1001111010111
  | 6694 => 110100000110
  | 6695 => 11101100010
  | 6696 => 11111010111000
  | 6697 => 110101111011
  | 6698 => 1011001110010
  | 6699 => 101110010001
  | 6700 => 110101100
  | 6701 => 11111111111011
  | 6702 => 1000111010010
  | 6703 => 1001100001011
  | 6704 => 100011110000
  | 6705 => 101111011110
  | 6706 => 101000011110110
  | 6707 => 110001001111111
  | 6708 => 101000111000100
  | 6709 => 110101111110101
  | 6710 => 11011110
  | 6711 => 110000001
  | 6712 => 11100011111000
  | 6713 => 11001110001
  | 6714 => 10011001111110
  | 6715 => 1100011010
  | 6716 => 10001101010100
  | 6717 => 101111001
  | 6718 => 10001101010110
  | 6719 => 10000001110001
  | 6720 => 10101000000
  | 6721 => 1100100001
  | 6722 => 101100011010110
  | 6723 => 10101111101001
  | 6724 => 10111000000100
  | 6725 => 10010001100
  | 6726 => 100110110110110
  | 6727 => 1100001011011
  | 6728 => 100110000101000
  | 6729 => 100101001011
  | 6730 => 1001000010
  | 6731 => 100110010011101
  | 6732 => 111111111111011111100
  | 6733 => 1011001001101
  | 6734 => 101010
  | 6735 => 11011101110010
  | 6736 => 1001100110000
  | 6737 => 10011000101
  | 6738 => 100010100101010
  | 6739 => 100011010011001
  | 6740 => 101100
  | 6741 => 100110011011101
  | 6742 => 10111011110
  | 6743 => 110001101111
  | 6744 => 1011100101000
  | 6745 => 1011111100110
  | 6746 => 10100010010
  | 6747 => 1011100110111
  | 6748 => 11101110001100
  | 6749 => 10100011111101
  | 6750 => 1101111111000
  | 6751 => 1110100100100111
  | 6752 => 11010001100000
  | 6753 => 101101101111
  | 6754 => 1111111110010
  | 6755 => 1010111100110
  | 6756 => 10001111000100
  | 6757 => 1011110000001
  | 6758 => 1100010101110
  | 6759 => 10011110011101
  | 6760 => 10111101000
  | 6761 => 110011110111001
  | 6762 => 11110011001110
  | 6763 => 11100011111011
  | 6764 => 1101010100
  | 6765 => 100111000110
  | 6766 => 1011110100101110
  | 6767 => 1011010101
  | 6768 => 1001110111110000
  | 6769 => 11011001110011
  | 6770 => 10010101101010
  | 6771 => 110010001101
  | 6772 => 1110100100
  | 6773 => 100001100001101
  | 6774 => 10011110110110
  | 6775 => 1111100
  | 6776 => 11011000
  | 6777 => 110100111111
  | 6778 => 1000000011110110
  | 6779 => 101100101101
  | 6780 => 101010101100
  | 6781 => 11000000010001
  | 6782 => 10101101000010
  | 6783 => 100011000100011
  | 6784 => 1000110000000
  | 6785 => 11011010110
  | 6786 => 10011011111010
  | 6787 => 11110000011
  | 6788 => 1100001000100
  | 6789 => 100010110011
  | 6790 => 11101100010
  | 6791 => 11000011010111
  | 6792 => 10011110001000
  | 6793 => 11100011011001
  | 6794 => 1000011000110
  | 6795 => 111111011010
  | 6796 => 1101001101100
  | 6797 => 111001001100101
  | 6798 => 11101100010
  | 6799 => 111100101100001
  | 6800 => 111010000
  | 6801 => 1011010111011111
  | 6802 => 11111101010
  | 6803 => 1111101111101
  | 6804 => 1101011101010100
  | 6805 => 11101010110
  | 6806 => 10110111100010
  | 6807 => 10011111010101
  | 6808 => 10000101000
  | 6809 => 11010010011
  | 6810 => 110111101110
  | 6811 => 1010010001
  | 6812 => 100000001110100
  | 6813 => 1100111100111
  | 6814 => 10001010010
  | 6815 => 1101000010110
  | 6816 => 1001100000
  | 6817 => 10010111111001
  | 6818 => 1010001100010
  | 6819 => 11101010000001
  | 6820 => 1100100100
  | 6821 => 110101110111
  | 6822 => 11100100111110
  | 6823 => 10000101000011
  | 6824 => 1001010001000
  | 6825 => 1010100
  | 6826 => 10000000110010110
  | 6827 => 10001010010100011
  | 6828 => 101101001100
  | 6829 => 111101001
  | 6830 => 1000001111010
  | 6831 => 110011110111111111111
  | 6832 => 10100100010000
  | 6833 => 100001011010101
  | 6834 => 11100100000110
  | 6835 => 111010010010
  | 6836 => 101100010101100
  | 6837 => 1010001110001
  | 6838 => 1011001001010
  | 6839 => 1100111001101
  | 6840 => 1111011111000
  | 6841 => 110111101001
  | 6842 => 11111100110
  | 6843 => 11101000001001
  | 6844 => 10101111101100
  | 6845 => 101001110010
  | 6846 => 1001000110110
  | 6847 => 11000000010011
  | 6848 => 100010011000000
  | 6849 => 11001101111001
  | 6850 => 1000100
  | 6851 => 11001000101
  | 6852 => 100001000100
  | 6853 => 100110111101
  | 6854 => 10100101110010
  | 6855 => 1011010100010
  | 6856 => 10010011101000
  | 6857 => 111110101110001
  | 6858 => 11111001010110
  | 6859 => 11110111001111
  | 6860 => 110000100
  | 6861 => 100000111011
  | 6862 => 10001110111010
  | 6863 => 1101010000001
  | 6864 => 1111110000
  | 6865 => 1001111101010
  | 6866 => 101111111101110
  | 6867 => 1101111110001
  | 6868 => 100101100
  | 6869 => 10011011111
  | 6870 => 111101111010
  | 6871 => 1010010000000111
  | 6872 => 101111111011000
  | 6873 => 11111100100011
  | 6874 => 11101101100110
  | 6875 => 110000
  | 6876 => 10111101101100
  | 6877 => 110011010110001
  | 6878 => 1010110111001110
  | 6879 => 110110011010101
  | 6880 => 110110100000
  | 6881 => 11000111101
  | 6882 => 1110101010
  | 6883 => 111111011111101
  | 6884 => 1010000000100
  | 6885 => 1111011010110
  | 6886 => 1100110011110
  | 6887 => 110000011101
  | 6888 => 110010100011000
  | 6889 => 100111010001
  | 6890 => 1001110110
  | 6891 => 101100000111111
  | 6892 => 11111110100
  | 6893 => 10010001000111
  | 6894 => 100111110110010
  | 6895 => 110101001010
  | 6896 => 1011001010000
  | 6897 => 10110100100001
  | 6898 => 10011000110010
  | 6899 => 1010110110111
  | 6900 => 1000010100
  | 6901 => 110100010111
  | 6902 => 10011011111010
  | 6903 => 100100101111101
  | 6904 => 110001110101000
  | 6905 => 10000111010
  | 6906 => 111111111101010
  | 6907 => 11110110100001
  | 6908 => 100111011111100
  | 6909 => 101111100010011
  | 6910 => 100101100010
  | 6911 => 1010111001110001
  | 6912 => 110111111100000000
  | 6913 => 101011010101111
  | 6914 => 100011010
  | 6915 => 11010001000110
  | 6916 => 100000000100
  | 6917 => 10101110101111
  | 6918 => 1001000010
  | 6919 => 100111011
  | 6920 => 1011001101000
  | 6921 => 10010011110111
  | 6922 => 10111000010
  | 6923 => 101111000111101001
  | 6924 => 11011111010100
  | 6925 => 11011110100
  | 6926 => 11101010011110
  | 6927 => 101001101110011
  | 6928 => 100010010000
  | 6929 => 100000110000011
  | 6930 => 1111111111111111110
  | 6931 => 1011101010001
  | 6932 => 1011101000100
  | 6933 => 11001011011011
  | 6934 => 1010010011010
  | 6935 => 1010101100010
  | 6936 => 101010011001000
  | 6937 => 110111001
  | 6938 => 101011001110
  | 6939 => 1011001100100111
  | 6940 => 101011110100
  | 6941 => 11011001111
  | 6942 => 1010010011010
  | 6943 => 1101000111
  | 6944 => 1000001100000
  | 6945 => 1110111010110
  | 6946 => 1101101001110
  | 6947 => 1101100010000111
  | 6948 => 11001111110100
  | 6949 => 101101001
  | 6950 => 11011010100
  | 6951 => 10010011101111
  | 6952 => 10010011000
  | 6953 => 1000011010001011
  | 6954 => 10111100110110
  | 6955 => 110101111100110
  | 6956 => 10011101111100
  | 6957 => 1101010110111
  | 6958 => 110111011010
  | 6959 => 1101111011101
  | 6960 => 110101110000
  | 6961 => 11110111011
  | 6962 => 100110010111010
  | 6963 => 11001011000001
  | 6964 => 111001111100
  | 6965 => 101010010010
  | 6966 => 111010101011010
  | 6967 => 11101011110011
  | 6968 => 111001111000
  | 6969 => 10101001011
  | 6970 => 100110110
  | 6971 => 1011011101
  | 6972 => 1010000000100
  | 6973 => 1101000001101
  | 6974 => 10000111110110
  | 6975 => 1111101011100
  | 6976 => 1001010111000000
  | 6977 => 10000010000101
  | 6978 => 11101000111110
  | 6979 => 111110000001
  | 6980 => 110010000100
  | 6981 => 11000001010011
  | 6982 => 1010111110110
  | 6983 => 1000011001001001
  | 6984 => 110011101111000
  | 6985 => 1000001001010
  | 6986 => 10011110100110
  | 6987 => 1001001100101
  | 6988 => 11000000000100
  | 6989 => 101001001001101
  | 6990 => 10011001110
  | 6991 => 10100011101011
  | 6992 => 111011110000
  | 6993 => 10101111111111111111111111111
  | 6994 => 101000010000110
  | 6995 => 1000110111010
  | 6996 => 10011101100
  | 6997 => 10101100101
  | 6998 => 100010010010010
  | 6999 => 1000101101001
  | _ => 1

def witness_fast_7 : Nat → Nat
  | 7000 => 1001000
  | 7001 => 1001101001001
  | 7002 => 100110101101110
  | 7003 => 10110000001
  | 7004 => 10000110010100
  | 7005 => 100110010110
  | 7006 => 11010110000010
  | 7007 => 10111101
  | 7008 => 111011100000
  | 7009 => 1001101000101
  | 7010 => 101101101110
  | 7011 => 11100111001101
  | 7012 => 10010001110100
  | 7013 => 1111000000001
  | 7014 => 1001001011010
  | 7015 => 1011100010
  | 7016 => 1010111010011000
  | 7017 => 10110110111001
  | 7018 => 1000001101110
  | 7019 => 10001010000111
  | 7020 => 101100101111100
  | 7021 => 111110000001
  | 7022 => 1010100010011110
  | 7023 => 1011010011
  | 7024 => 100011000110000
  | 7025 => 10100011100
  | 7026 => 1000101110010
  | 7027 => 10111101111
  | 7028 => 10000110101100
  | 7029 => 11101111111111110111
  | 7030 => 101000010
  | 7031 => 101000111101
  | 7032 => 1001101011000
  | 7033 => 1001101111101
  | 7034 => 101111101101110
  | 7035 => 10000011101010
  | 7036 => 1110110001100
  | 7037 => 1010110001011
  | 7038 => 11110010111010
  | 7039 => 10000000111001
  | 7040 => 110000000
  | 7041 => 10011011110101
  | 7042 => 110101001010
  | 7043 => 110110100011
  | 7044 => 110101110101100
  | 7045 => 1000101000010
  | 7046 => 10111010
  | 7047 => 10111010111001
  | 7048 => 100100101000
  | 7049 => 100011000100011
  | 7050 => 1001100
  | 7051 => 11111110000001
  | 7052 => 101001000111100
  | 7053 => 101111011011
  | 7054 => 101110110011110
  | 7055 => 1001000100110
  | 7056 => 111111101010000
  | 7057 => 10111101100011
  | 7058 => 11011100010010
  | 7059 => 1011101011011
  | 7060 => 1010110100100
  | 7061 => 11110000111001
  | 7062 => 1101001110
  | 7063 => 10011111011111
  | 7064 => 1101101000
  | 7065 => 1101111011010
  | 7066 => 100001101011110
  | 7067 => 100001110011
  | 7068 => 100110110000100
  | 7069 => 100000011111001
  | 7070 => 1011010
  | 7071 => 1000010101011
  | 7072 => 10011101100000
  | 7073 => 1000010001001
  | 7074 => 10011001111110
  | 7075 => 1001011101100
  | 7076 => 1010010111111100
  | 7077 => 101110111011
  | 7078 => 1010011100110
  | 7079 => 111010110111
  | 7080 => 100101111000
  | 7081 => 111011110001
  | 7082 => 100000000010
  | 7083 => 100100111101101
  | 7084 => 1001010110100
  | 7085 => 1010010011010
  | 7086 => 101100111101010
  | 7087 => 101011011
  | 7088 => 1100000010000
  | 7089 => 1010011010001
  | 7090 => 1110111000010
  | 7091 => 1011011111100011
  | 7092 => 10111101101100
  | 7093 => 111010110101
  | 7094 => 1001001111101010
  | 7095 => 11011000110
  | 7096 => 11000000111000
  | 7097 => 11101000101111
  | 7098 => 101111010
  | 7099 => 100100101110111
  | 7100 => 1001100
  | 7101 => 111010011111
  | 7102 => 1011110000010
  | 7103 => 1001000111000001
  | 7104 => 111000000
  | 7105 => 1011010110110
  | 7106 => 11011110010010
  | 7107 => 111110001101001
  | 7108 => 10101001100
  | 7109 => 1110110011111
  | 7110 => 111110110110
  | 7111 => 10011101110101
  | 7112 => 1001110011111000
  | 7113 => 110101111100001
  | 7114 => 101010110000010
  | 7115 => 100011101010
  | 7116 => 1001011100100
  | 7117 => 100011011101111
  | 7118 => 1001111110
  | 7119 => 110011110111
  | 7120 => 110101010000
  | 7121 => 11101000111001
  | 7122 => 110100000101010
  | 7123 => 1101100101111
  | 7124 => 1001100100
  | 7125 => 11001000
  | 7126 => 101011000011110
  | 7127 => 11010101000011
  | 7128 => 1111111111111111011000
  | 7129 => 10010011110111
  | 7130 => 11000000010
  | 7131 => 100101110010111
  | 7132 => 110011100
  | 7133 => 1000000000111
  | 7134 => 1111011100110
  | 7135 => 110111111011010
  | 7136 => 100111100100000
  | 7137 => 1111001110011
  | 7138 => 1110010001010
  | 7139 => 110011110111111
  | 7140 => 10011101100
  | 7141 => 110011111101
  | 7142 => 10011000000110
  | 7143 => 100000000010001
  | 7144 => 100001111011000
  | 7145 => 100111010010
  | 7146 => 11001111110010
  | 7147 => 11001111110101
  | 7148 => 100100101111100
  | 7149 => 101010001101
  | 7150 => 100100
  | 7151 => 101011100101
  | 7152 => 100001110110000
  | 7153 => 1000111001
  | 7154 => 110011100010
  | 7155 => 111111011010
  | 7156 => 1110110101100
  | 7157 => 111000010001
  | 7158 => 10111001011110
  | 7159 => 11000011111
  | 7160 => 11010111000
  | 7161 => 10010011011
  | 7162 => 1110110
  | 7163 => 11100001101111
  | 7164 => 1010111001101100
  | 7165 => 11011001000110
  | 7166 => 1110100001110
  | 7167 => 111110001
  | 7168 => 10010000000000
  | 7169 => 10111101101111
  | 7170 => 1010000111110110
  | 7171 => 1011111
  | 7172 => 10010001101100
  | 7173 => 10111111011
  | 7174 => 1010101101110
  | 7175 => 101110100
  | 7176 => 10010101101000
  | 7177 => 111110101101
  | 7178 => 11101100010
  | 7179 => 110001010011
  | 7180 => 100101011100
  | 7181 => 111101111010111
  | 7182 => 11111111000010
  | 7183 => 1110111101
  | 7184 => 1111001110000
  | 7185 => 110011111001010
  | 7186 => 11011000010
  | 7187 => 110110111111101
  | 7188 => 11000000000100
  | 7189 => 100101101111011
  | 7190 => 1010000000010
  | 7191 => 111101101011
  | 7192 => 11101111001001000
  | 7193 => 10111111101011
  | 7194 => 111001010010
  | 7195 => 1100101110
  | 7196 => 10011111000100
  | 7197 => 1101111010101
  | 7198 => 101000011010010
  | 7199 => 1100000001
  | 7200 => 11111111100000
  | 7201 => 100101101
  | 7202 => 1101100111000110
  | 7203 => 1101101001
  | 7204 => 1101101001101100
  | 7205 => 11110110
  | 7206 => 100011100001010
  | 7207 => 111100100000111
  | 7208 => 100011000
  | 7209 => 100001111101011
  | 7210 => 11101100010
  | 7211 => 1101010100011
  | 7212 => 1110011000100
  | 7213 => 1111011011101
  | 7214 => 11111111010
  | 7215 => 101010
  | 7216 => 11111111110000
  | 7217 => 101100110101011
  | 7218 => 11001101011110
  | 7219 => 10010011000011
  | 7220 => 1110111100
  | 7221 => 10000011100101
  | 7222 => 100011101010110
  | 7223 => 1111100000000001
  | 7224 => 1110001011000
  | 7225 => 110011000100
  | 7226 => 11010100010010
  | 7227 => 1001001011011111110111111
  | 7228 => 101001000100
  | 7229 => 11001011011101
  | 7230 => 100010110110
  | 7231 => 1000110000001
  | 7232 => 1011011000000
  | 7233 => 1000111011111
  | 7234 => 1000110011010010
  | 7235 => 10010100010
  | 7236 => 101011101011100
  | 7237 => 101100001101001
  | 7238 => 11001000010
  | 7239 => 110001011010111
  | 7240 => 1001111000
  | 7241 => 1001110110011011
  | 7242 => 10011000100110
  | 7243 => 11110010010011
  | 7244 => 10010011110100
  | 7245 => 1111101010110
  | 7246 => 1001111101001110
  | 7247 => 10011100011
  | 7248 => 100010110110000
  | 7249 => 11110100111
  | 7250 => 1101101000
  | 7251 => 1000101000011001
  | 7252 => 1011110100
  | 7253 => 10011111110000111
  | 7254 => 1010101111110
  | 7255 => 10101101110110
  | 7256 => 10001011011000
  | 7257 => 100111000010001
  | 7258 => 111011110
  | 7259 => 1010010001
  | 7260 => 100011110100
  | 7261 => 10011111011
  | 7262 => 10000100100110
  | 7263 => 10110011001111
  | 7264 => 1100110100000
  | 7265 => 10000110011010
  | 7266 => 10111001101110
  | 7267 => 1010001110001
  | 7268 => 111101010100
  | 7269 => 1110100011111
  | 7270 => 1011000100010
  | 7271 => 1111001100011
  | 7272 => 1011111111111111111000
  | 7273 => 1101011010001
  | 7274 => 11110001110010
  | 7275 => 10011011100
  | 7276 => 10100101001100
  | 7277 => 11010101
  | 7278 => 110001011101110
  | 7279 => 110100001010101
  | 7280 => 10010000
  | 7281 => 101110010111001
  | 7282 => 10110001110
  | 7283 => 110111010001011
  | 7284 => 111001000010100
  | 7285 => 11011101101010
  | 7286 => 10101001000010
  | 7287 => 111100010011011
  | 7288 => 101000011001000
  | 7289 => 11010100101
  | 7290 => 1011111110010
  | 7291 => 1000011111011
  | 7292 => 111000100100
  | 7293 => 100111011
  | 7294 => 1000001101011010
  | 7295 => 100101100010
  | 7296 => 110010000000
  | 7297 => 111100011111001
  | 7298 => 10110001101110
  | 7299 => 10011101101101
  | 7300 => 1000100
  | 7301 => 1001111010011
  | 7302 => 100011111011010
  | 7303 => 1001100111101
  | 7304 => 1111100001000
  | 7305 => 111111110010
  | 7306 => 1011011111110
  | 7307 => 10111010101
  | 7308 => 10111110011100
  | 7309 => 100010111110001
  | 7310 => 11010110010
  | 7311 => 101000010111
  | 7312 => 10011010010000
  | 7313 => 101110101101
  | 7314 => 11000000010
  | 7315 => 10000000010
  | 7316 => 101010000100
  | 7317 => 10000101011111111101111011
  | 7318 => 10100111100010
  | 7319 => 10110110011001
  | 7320 => 100101000
  | 7321 => 11000000101111
  | 7322 => 100101110000010
  | 7323 => 1110000101110011
  | 7324 => 110001000000100
  | 7325 => 11000011100
  | 7326 => 1111111111111111110
  | 7327 => 101101010100111
  | 7328 => 1000010001100000
  | 7329 => 100100101000011
  | 7330 => 100011011110
  | 7331 => 10011001001
  | 7332 => 11010000101100
  | 7333 => 110000111101
  | 7334 => 110010
  | 7335 => 10101001111110
  | 7336 => 10110001111000
  | 7337 => 1110110111
  | 7338 => 1011100001110110
  | 7339 => 110100111001
  | 7340 => 110100
  | 7341 => 1000001011101
  | 7342 => 10001101001010
  | 7343 => 111101110001
  | 7344 => 1111011010110000
  | 7345 => 11011000101010
  | 7346 => 11000100101010
  | 7347 => 1111011011001
  | 7348 => 110000111100
  | 7349 => 101111100011001
  | 7350 => 110000100
  | 7351 => 1110001
  | 7352 => 1010111010011000
  | 7353 => 1000110111111
  | 7354 => 11000110001010
  | 7355 => 1001110100010
  | 7356 => 1011001100100
  | 7357 => 11111111001011
  | 7358 => 110001100011010
  | 7359 => 1001111001
  | 7360 => 110101000000
  | 7361 => 10110110101011
  | 7362 => 100011111010110
  | 7363 => 1100010111
  | 7364 => 10110010010100
  | 7365 => 1001010101010
  | 7366 => 10111100000010
  | 7367 => 111010111010101
  | 7368 => 1011111000111000
  | 7369 => 10111100100111
  | 7370 => 1101100110
  | 7371 => 1011011011101
  | 7372 => 110110110010100
  | 7373 => 1010101
  | 7374 => 1000011110010
  | 7375 => 11011111000
  | 7376 => 1111010000
  | 7377 => 101010011011011
  | 7378 => 110010001010
  | 7379 => 101000101011001
  | 7380 => 11100111101100
  | 7381 => 11110110011
  | 7382 => 111011011000010
  | 7383 => 1111110100101
  | 7384 => 10100100101000
  | 7385 => 1101000110
  | 7386 => 1000011110010
  | 7387 => 100111010001
  | 7388 => 10110111001100
  | 7389 => 1011011001111
  | 7390 => 1101110
  | 7391 => 1010001000011
  | 7392 => 11111100000
  | 7393 => 10010111110111
  | 7394 => 110101010001110
  | 7395 => 1111010010
  | 7396 => 1011000110111100
  | 7397 => 1111111011101
  | 7398 => 101101001011110
  | 7399 => 101011011111101
  | 7400 => 111000
  | 7401 => 1000000100011011
  | 7402 => 11110010101110
  | 7403 => 1101100011
  | 7404 => 101000000100
  | 7405 => 100101101010
  | 7406 => 10011100011010
  | 7407 => 10011101011011
  | 7408 => 1101000110000
  | 7409 => 11100100001101
  | 7410 => 101101010010
  | 7411 => 1110101101
  | 7412 => 110111100100100
  | 7413 => 100111010101011
  | 7414 => 1011010110
  | 7415 => 110100100010
  | 7416 => 111101101101000
  | 7417 => 100100101111011
  | 7418 => 1000011010001110
  | 7419 => 111100111101
  | 7420 => 10011101100
  | 7421 => 11010010000111
  | 7422 => 1100100010110
  | 7423 => 11101000001
  | 7424 => 110110100000000
  | 7425 => 111101111111111111100
  | 7426 => 100100010001010
  | 7427 => 1000011111001
  | 7428 => 1101001001100
  | 7429 => 1011111111111
  | 7430 => 101100010
  | 7431 => 101100100011
  | 7432 => 1100000101000
  | 7433 => 111100011101001
  | 7434 => 11000011111110
  | 7435 => 1010100111010
  | 7436 => 1011110100
  | 7437 => 1111110111
  | 7438 => 10101011111110
  | 7439 => 100110000001001
  | 7440 => 100000110000
  | 7441 => 11001100100011
  | 7442 => 1100001000111110
  | 7443 => 100011110011011
  | 7444 => 10011110111100
  | 7445 => 1110100111110
  | 7446 => 10010011001010
  | 7447 => 1111011101101
  | 7448 => 101001100011000
  | 7449 => 10010000011011
  | 7450 => 11011100
  | 7451 => 111000010010011
  | 7452 => 110101101101100
  | 7453 => 10011011110111
  | 7454 => 101101110010110
  | 7455 => 1001010001110
  | 7456 => 11111001100000
  | 7457 => 1100011100101
  | 7458 => 1001101100010
  | 7459 => 11010110101001
  | 7460 => 10101101100
  | 7461 => 111111010101
  | 7462 => 10111010
  | 7463 => 11010011110001
  | 7464 => 11101111101000
  | 7465 => 101001001010110
  | 7466 => 1011010010010010
  | 7467 => 101001000101001
  | 7468 => 111011111100100
  | 7469 => 1110110001
  | 7470 => 1001101111110
  | 7471 => 1001000000011
  | 7472 => 1000001110000
  | 7473 => 1000001101000011
  | 7474 => 101011110
  | 7475 => 1001010110100
  | 7476 => 10100100110100
  | 7477 => 10101101100001
  | 7478 => 101010100101110
  | 7479 => 1011101110101
  | 7480 => 1001011000
  | 7481 => 11010111111111
  | 7482 => 1001001100010010
  | 7483 => 1100001
  | 7484 => 11010111110100
  | 7485 => 11101001000010
  | 7486 => 111001011000110
  | 7487 => 11010000011111
  | 7488 => 10101111111000000
  | 7489 => 1110000101111
  | 7490 => 110111001110110
  | 7491 => 100011000111
  | 7492 => 1100001100100
  | 7493 => 10010101011
  | 7494 => 101101101100110
  | 7495 => 1100101110
  | 7496 => 10110111001000
  | 7497 => 11111110000011
  | 7498 => 1010000100011110
  | 7499 => 1101011110110011
  | 7500 => 1110000
  | 7501 => 1110100001101
  | 7502 => 1000011011010
  | 7503 => 1110000100011
  | 7504 => 11001000010000
  | 7505 => 11010000110
  | 7506 => 110101101110010
  | 7507 => 1100101101111
  | 7508 => 11011010000100
  | 7509 => 110010111001011
  | 7510 => 11110001110
  | 7511 => 101110010001
  | 7512 => 1100000001000
  | 7513 => 100000111101
  | 7514 => 100000001111010
  | 7515 => 10011010111110
  | 7516 => 10101111101100
  | 7517 => 11011100010110001
  | 7518 => 110101110
  | 7519 => 111011110001
  | 7520 => 1001100000
  | 7521 => 11100101001
  | 7522 => 10111110010
  | 7523 => 110010010111
  | 7524 => 11111111111111111100
  | 7525 => 110100111100
  | 7526 => 1111101010
  | 7527 => 11001000011001
  | 7528 => 100001011000
  | 7529 => 10001000101101
  | 7530 => 11100101010
  | 7531 => 111110101001111
  | 7532 => 1011001100111100
  | 7533 => 1100111011101
  | 7534 => 1110101110010
  | 7535 => 1100110
  | 7536 => 1101111011010000
  | 7537 => 10101110011
  | 7538 => 111010001000110
  | 7539 => 1010010000111
  | 7540 => 1110001100
  | 7541 => 10110000011
  | 7542 => 11011001011110
  | 7543 => 11111001001011
  | 7544 => 1001001101000
  | 7545 => 110101001010
  | 7546 => 11011010010
  | 7547 => 111110011010011
  | 7548 => 10001100
  | 7549 => 111000111001
  | 7550 => 111000100
  | 7551 => 10001111110101
  | 7552 => 110111110000000
  | 7553 => 10100000001
  | 7554 => 111000100110
  | 7555 => 101101010
  | 7556 => 11000011010111100
  | 7557 => 111010010001
  | 7558 => 100011111011010
  | 7559 => 110000111011111
  | 7560 => 1010111010111000
  | 7561 => 1001001100001
  | 7562 => 11000101110
  | 7563 => 111111010001001
  | 7564 => 100101110111100
  | 7565 => 110101010
  | 7566 => 11101100010
  | 7567 => 11101101010111
  | 7568 => 1111110110000
  | 7569 => 110111010100011
  | 7570 => 1011010010110
  | 7571 => 101011111001001
  | 7572 => 111110100110100
  | 7573 => 101001101
  | 7574 => 10011011111010
  | 7575 => 101111100
  | 7576 => 1011001101000
  | 7577 => 1100011001011
  | 7578 => 10011110101110
  | 7579 => 100111011
  | 7580 => 10010110100
  | 7581 => 1010000111001
  | 7582 => 1010010010010
  | 7583 => 11101110101
  | 7584 => 10101011100000
  | 7585 => 100011001110
  | 7586 => 1011100010
  | 7587 => 111011110011
  | 7588 => 101110100
  | 7589 => 100010111111
  | 7590 => 111110010
  | 7591 => 1101010110001
  | 7592 => 10011001000
  | 7593 => 101101000011
  | 7594 => 10100011001110
  | 7595 => 100100110110
  | 7596 => 100111100111100
  | 7597 => 110100001111
  | 7598 => 1000101000011010
  | 7599 => 10100001110001
  | 7600 => 110010000
  | 7601 => 111100100111
  | 7602 => 10111010110110
  | 7603 => 11011100001001
  | 7604 => 10001011011100
  | 7605 => 1111101010110
  | 7606 => 11111111010
  | 7607 => 10100101011001
  | 7608 => 1001111101011000
  | 7609 => 10100111111111
  | 7610 => 110111000110
  | 7611 => 110110000011111
  | 7612 => 101100110100
  | 7613 => 10010101100011
  | 7614 => 1111011010110
  | 7615 => 101101111010
  | 7616 => 100111011000000
  | 7617 => 1100100101001
  | 7618 => 1100001110
  | 7619 => 11101010001111
  | 7620 => 10101110100
  | 7621 => 10000100010101
  | 7622 => 11101100010
  | 7623 => 111101111101111011111
  | 7624 => 100101011011000
  | 7625 => 100101000
  | 7626 => 1111111111111110
  | 7627 => 10010111011011
  | 7628 => 1101110000100
  | 7629 => 1101010101111
  | 7630 => 11100101110
  | 7631 => 11000110011111
  | 7632 => 111111011010000
  | 7633 => 11000000011111
  | 7634 => 1010110001010
  | 7635 => 1001011000110
  | 7636 => 100100110001100
  | 7637 => 11101010110001
  | 7638 => 1011110000010
  | 7639 => 10010010000111
  | 7640 => 11101111000
  | 7641 => 10111011100011
  | 7642 => 1010100111110
  | 7643 => 101000010011011
  | 7644 => 1011110100
  | 7645 => 10100100010
  | 7646 => 1001010000010
  | 7647 => 11111000100111
  | 7648 => 111111100000
  | 7649 => 11010110110111
  | 7650 => 1011111011100
  | 7651 => 11000110110101
  | 7652 => 1001011110100
  | 7653 => 10000100001111
  | 7654 => 11010011110
  | 7655 => 101110011110
  | 7656 => 111101001000
  | 7657 => 110000100000011
  | 7658 => 10010111011110
  | 7659 => 100111011111
  | 7660 => 1101010100
  | 7661 => 110111101001
  | 7662 => 10000111010110110
  | 7663 => 1100011111010111
  | 7664 => 1001110000
  | 7665 => 110011100010
  | 7666 => 101001101100110
  | 7667 => 1001111111011
  | 7668 => 11100111110100
  | 7669 => 11011000110001
  | 7670 => 111011001010
  | 7671 => 1001101101111
  | 7672 => 10011001000
  | 7673 => 11001011111011
  | 7674 => 10010100010110
  | 7675 => 1000110001100
  | 7676 => 111110100
  | 7677 => 11100011110011
  | 7678 => 11001000010
  | 7679 => 10101101111101
  | 7680 => 111000000000
  | 7681 => 110101011100001
  | 7682 => 10000100001110
  | 7683 => 11010100101
  | 7684 => 111101110111100
  | 7685 => 1100100111110
  | 7686 => 10010111011110
  | 7687 => 1001000010011
  | 7688 => 1010011000
  | 7689 => 1001100111
  | 7690 => 1000110100010
  | 7691 => 100000101100011
  | 7692 => 101110101011100
  | 7693 => 100100000011010111
  | 7694 => 111011001010010
  | 7695 => 1111011010110
  | 7696 => 101010000
  | 7697 => 1011101011
  | 7698 => 11110100010
  | 7699 => 10001001
  | 7700 => 100100
  | 7701 => 101001010011
  | 7702 => 1000010010110110
  | 7703 => 100101001101
  | 7704 => 111010111011000
  | 7705 => 111010111110
  | 7706 => 10011000110010
  | 7707 => 110111011101
  | 7708 => 1010001110101100
  | 7709 => 10111101111111
  | 7710 => 1010010
  | 7711 => 10110111100111
  | 7712 => 11110100000
  | 7713 => 10111101101001
  | 7714 => 101011100011010
  | 7715 => 1100100011110
  | 7716 => 111011010011100
  | 7717 => 10101000100101
  | 7718 => 10011000010010
  | 7719 => 10100001010010001
  | 7720 => 11001000
  | 7721 => 101101111000001
  | 7722 => 10011011011111111111110
  | 7723 => 1000011010001
  | 7724 => 11001100100
  | 7725 => 111011000100
  | 7726 => 100100111000110
  | 7727 => 11000010101101
  | 7728 => 1011001110000
  | 7729 => 1001001100001
  | 7730 => 101110000110
  | 7731 => 1110101101011
  | 7732 => 10101001101100
  | 7733 => 111100011
  | 7734 => 110110011100110
  | 7735 => 1001110110
  | 7736 => 10010000101000
  | 7737 => 1001111111001
  | 7738 => 100111110110
  | 7739 => 1001001011100011
  | 7740 => 1111101110100
  | 7741 => 1111111100001
  | 7742 => 1011001110010010
  | 7743 => 11110000011111
  | 7744 => 11011000000
  | 7745 => 100001101010
  | 7746 => 11101100000010
  | 7747 => 101100000111
  | 7748 => 10101101110100
  | 7749 => 1011010110100011
  | 7750 => 111011000
  | 7751 => 10111011001011
  | 7752 => 111101101011000
  | 7753 => 10011111001001
  | 7754 => 11000011000010
  | 7755 => 10011100110
  | 7756 => 10110101110111100
  | 7757 => 100011001
  | 7758 => 1110011110110
  | 7759 => 11001010000001
  | 7760 => 111000010000
  | 7761 => 11100110110011
  | 7762 => 11100111011010
  | 7763 => 100000100110001
  | 7764 => 1011001100100
  | 7765 => 10000110011110
  | 7766 => 11111011010110
  | 7767 => 10001111010111
  | 7768 => 1001101000
  | 7769 => 10101010001011
  | 7770 => 101010
  | 7771 => 101001110111001
  | 7772 => 1011110110111100
  | 7773 => 110010110100111
  | 7774 => 1111101010110
  | 7775 => 10101000100
  | 7776 => 10011111011100000
  | 7777 => 101101
  | 7778 => 1011101110
  | 7779 => 1000000110110001
  | 7780 => 101101100
  | 7781 => 100101100001101
  | 7782 => 111111101101110
  | 7783 => 100010010110101
  | 7784 => 1010010001000
  | 7785 => 11111110110
  | 7786 => 101101111001010
  | 7787 => 101001001011001
  | 7788 => 10010111100
  | 7789 => 101110101010011
  | 7790 => 10110010010
  | 7791 => 111110111011011
  | 7792 => 11001101110000
  | 7793 => 11101100110101
  | 7794 => 11101111110
  | 7795 => 11010110110
  | 7796 => 110011110100
  | 7797 => 1100000111001111
  | 7798 => 1001111100010
  | 7799 => 1001011001001
  | 7800 => 10101000
  | 7801 => 100010101010011
  | 7802 => 1011111000100110
  | 7803 => 11111101100001
  | 7804 => 110100110100100
  | 7805 => 10100000011010
  | 7806 => 1100110001010
  | 7807 => 10101100011111
  | 7808 => 1001010000000
  | 7809 => 101010110001
  | 7810 => 10011100110
  | 7811 => 11101001011
  | 7812 => 10101011111100
  | 7813 => 1011101011011
  | 7814 => 1011111010110
  | 7815 => 10111000110
  | 7816 => 1011110001000
  | 7817 => 1010110111010011
  | 7818 => 11011101010110
  | 7819 => 100011101001
  | 7820 => 11011100010100
  | 7821 => 101111111101111111011
  | 7822 => 11101111111010
  | 7823 => 1010011000001
  | 7824 => 1000000110000
  | 7825 => 1100101100
  | 7826 => 10111101101010
  | 7827 => 1000001001
  | 7828 => 1001010001100
  | 7829 => 110111111101011
  | 7830 => 10110111010110
  | 7831 => 1101000001001
  | 7832 => 1100111111000
  | 7833 => 101000010111
  | 7834 => 100001010
  | 7835 => 10001111110
  | 7836 => 1001000111000100
  | 7837 => 11011101011111
  | 7838 => 101011010110
  | 7839 => 1000101011101101
  | 7840 => 110000100000
  | 7841 => 10100100000001
  | 7842 => 100010100001110
  | 7843 => 101100011111
  | 7844 => 10001100
  | 7845 => 10001001011010
  | 7846 => 10000001100010
  | 7847 => 100001111111111
  | 7848 => 1111111011000
  | 7849 => 1000010000111
  | 7850 => 1010110101100
  | 7851 => 1010001010011
  | 7852 => 111111100100
  | 7853 => 110000010111
  | 7854 => 1001110110
  | 7855 => 1000011111010
  | 7856 => 1001010101010000
  | 7857 => 1011101011011
  | 7858 => 10001001110010
  | 7859 => 100010011001
  | 7860 => 10100100
  | 7861 => 101000101111
  | 7862 => 110110101010
  | 7863 => 1100010111
  | 7864 => 11000111101000
  | 7865 => 110110
  | 7866 => 1100111111010
  | 7867 => 101110100111011
  | 7868 => 10110111111100
  | 7869 => 10100011011
  | 7870 => 101100011110
  | 7871 => 101111110001
  | 7872 => 10001100111000000
  | 7873 => 1101101110001101
  | 7874 => 1000111110010
  | 7875 => 1111011111000
  | 7876 => 1000011000110100
  | 7877 => 110111110001
  | 7878 => 101010101010
  | 7879 => 1100010110011
  | 7880 => 1101000101000
  | 7881 => 100111011111
  | 7882 => 11010011110
  | 7883 => 1111101101011
  | 7884 => 10111100111100
  | 7885 => 10011001010
  | 7886 => 1110111111110110
  | 7887 => 110101111011111
  | 7888 => 1111010010000
  | 7889 => 11101101010111
  | 7890 => 1011001001010
  | 7891 => 1101010011101
  | 7892 => 111101011100
  | 7893 => 1111011000111
  | 7894 => 100010010111110
  | 7895 => 1000011001010
  | 7896 => 100101000111000
  | 7897 => 10110000001
  | 7898 => 1100110011110
  | 7899 => 100100101110111
  | 7900 => 1001001100
  | 7901 => 1000010000100011
  | 7902 => 11001111101010
  | 7903 => 1101000101001101
  | 7904 => 100000000100000
  | 7905 => 100100111000010
  | 7906 => 10111001010101110
  | 7907 => 1001001011010101
  | 7908 => 100111111100100
  | 7909 => 1111000000011
  | 7910 => 1100111101110
  | 7911 => 11001110101101
  | 7912 => 11111011111101001000
  | 7913 => 110100010000001
  | 7914 => 1100010110010
  | 7915 => 11001011010
  | 7916 => 1000001110111100
  | 7917 => 101110010001
  | 7918 => 11001100111110
  | 7919 => 1010000101111
  | 7920 => 1111111111111111110000
  | 7921 => 1100001001001
  | 7922 => 1111100110
  | 7923 => 1000001111101011
  | 7924 => 1000001001001100
  | 7925 => 100000011111100
  | 7926 => 100011100111110
  | 7927 => 111011000101
  | 7928 => 110001000
  | 7929 => 1101011100111
  | 7930 => 10100100010
  | 7931 => 1110110001
  | 7932 => 11101101110100
  | 7933 => 1010111100110001
  | 7934 => 10100101010
  | 7935 => 10111111111110
  | 7936 => 11101100000000
  | 7937 => 110110001
  | 7938 => 101010110101110
  | 7939 => 10101110110101
  | 7940 => 1101000100
  | 7941 => 1010010001011
  | 7942 => 110010000110010
  | 7943 => 11010101100011
  | 7944 => 1011000111000
  | 7945 => 10111001001010
  | 7946 => 10000110011010
  | 7947 => 10010100111111
  | 7948 => 10100011011100
  | 7949 => 100000010110011
  | 7950 => 10001100
  | 7951 => 110100010001011
  | 7952 => 110001010000
  | 7953 => 11001000110001
  | 7954 => 1110100010
  | 7955 => 111111001110
  | 7956 => 100110111110100
  | 7957 => 1110100111101
  | 7958 => 100110001010110
  | 7959 => 100111000101
  | 7960 => 111000011000
  | 7961 => 1111110011111
  | 7962 => 11111000101110
  | 7963 => 100110000100001
  | 7964 => 1111000100100
  | 7965 => 11000011111110
  | 7966 => 11111110111010
  | 7967 => 1010011111011
  | 7968 => 111110000100000
  | 7969 => 1001111111011011
  | 7970 => 100011011010
  | 7971 => 1001000101011
  | 7972 => 111010100
  | 7973 => 110100010111
  | 7974 => 1100111101110
  | 7975 => 11110100100
  | 7976 => 111110000001000
  | 7977 => 1011100010001
  | 7978 => 1010001110111010
  | 7979 => 1011011111
  | 7980 => 111101111100
  | 7981 => 10101001011
  | 7982 => 100111011110110
  | 7983 => 1111011010011
  | 7984 => 111000000110000
  | 7985 => 10011011101110
  | 7986 => 11010001001010
  | 7987 => 110101110111111
  | 7988 => 100000101110100
  | 7989 => 1011111000111
  | 7990 => 11011011010
  | 7991 => 101111010001
  | 7992 => 111111111111111111111111111000
  | 7993 => 1101111100011
  | 7994 => 111010000010
  | 7995 => 11010111001110
  | 7996 => 111100000011100
  | 7997 => 110100001011
  | 7998 => 111110011111110
  | 7999 => 11101100101011
  | _ => 1

def witness_fast_8 : Nat → Nat
  | 8000 => 1000000
  | 8001 => 1001110011111
  | 8002 => 111110011000110
  | 8003 => 11111101101
  | 8004 => 1000100000100
  | 8005 => 1111110010
  | 8006 => 1000111001110
  | 8007 => 10110011110011
  | 8008 => 1001000
  | 8009 => 101011100101101
  | 8010 => 10111111110
  | 8011 => 1110101101111
  | 8012 => 10000111100100
  | 8013 => 1101001000011
  | 8014 => 10010110010110
  | 8015 => 11101111101010
  | 8016 => 1000001010000
  | 8017 => 1101100100101
  | 8018 => 111000101111010
  | 8019 => 11011111111111101111
  | 8020 => 111101100100
  | 8021 => 100110101
  | 8022 => 11000011111110
  | 8023 => 10001100110111011
  | 8024 => 111110000001000
  | 8025 => 11010011100
  | 8026 => 10100110101010
  | 8027 => 111011111011011
  | 8028 => 1011101111100
  | 8029 => 101010111111
  | 8030 => 1100110
  | 8031 => 1110100001001
  | 8032 => 11000100100000
  | 8033 => 1111011011111001
  | 8034 => 11101100010
  | 8035 => 1011111110110
  | 8036 => 10010001010100
  | 8037 => 101111110011
  | 8038 => 1010110100110
  | 8039 => 110011101111111
  | 8040 => 10010001000
  | 8041 => 110011100111
  | 8042 => 1010010100010
  | 8043 => 1001110011100101
  | 8044 => 1001001011111100
  | 8045 => 100010101000110
  | 8046 => 10011101011110
  | 8047 => 11010010011
  | 8048 => 11010001010000
  | 8049 => 1000111101111
  | 8050 => 1110111100
  | 8051 => 1001100110001101
  | 8052 => 110111100
  | 8053 => 1001101100111011
  | 8054 => 100001001010
  | 8055 => 1111100111010
  | 8056 => 11111110111000
  | 8057 => 1100110011101101
  | 8058 => 111110110110
  | 8059 => 1000011000101
  | 8060 => 11100111100
  | 8061 => 10000001001
  | 8062 => 111001110111110
  | 8063 => 111101101001
  | 8064 => 11110111110000000
  | 8065 => 10010011000110
  | 8066 => 1011100000110
  | 8067 => 10111111110111
  | 8068 => 1001101110100100
  | 8069 => 110001000110011
  | 8070 => 10101001110
  | 8071 => 1010111001011
  | 8072 => 10010001111111000
  | 8073 => 10011111000111
  | 8074 => 1101011010
  | 8075 => 1101010100
  | 8076 => 10010000100
  | 8077 => 1101000101
  | 8078 => 11101000011010
  | 8079 => 1000000111011
  | 8080 => 1010000
  | 8081 => 100010111111001
  | 8082 => 11011101110010
  | 8083 => 1100011000101
  | 8084 => 10000110100
  | 8085 => 101111010
  | 8086 => 1011110110010
  | 8087 => 1100010100001
  | 8088 => 1011000
  | 8089 => 1001110001011
  | 8090 => 111010001110
  | 8091 => 11101111001001
  | 8092 => 1000000011110100
  | 8093 => 10000101101111
  | 8094 => 1011111100110
  | 8095 => 111110011010
  | 8096 => 1111100100000
  | 8097 => 11010001011
  | 8098 => 1100010010010
  | 8099 => 11111010001
  | 8100 => 111111110100
  | 8101 => 100011000011001
  | 8102 => 100001001010
  | 8103 => 1110111
  | 8104 => 10000110101000
  | 8105 => 1000011110
  | 8106 => 1100001101010
  | 8107 => 11000110011011
  | 8108 => 1000100111100
  | 8109 => 100111111011
  | 8110 => 10010100010
  | 8111 => 100001111111111
  | 8112 => 101111010000
  | 8113 => 100101000100101
  | 8114 => 1100101110110
  | 8115 => 110011111110
  | 8116 => 10011100000100
  | 8117 => 10110111111101
  | 8118 => 1101011011111111111110
  | 8119 => 110000101001
  | 8120 => 11010111000
  | 8121 => 111000110001
  | 8122 => 10100111110110
  | 8123 => 11010100111101
  | 8124 => 1001100001010100
  | 8125 => 10010000
  | 8126 => 10011110110
  | 8127 => 11111110000011
  | 8128 => 11010011000000
  | 8129 => 1101110110111
  | 8130 => 1111111111111110
  | 8131 => 1111100101101
  | 8132 => 10000001110100
  | 8133 => 110011000101
  | 8134 => 101000000010
  | 8135 => 10100001001110
  | 8136 => 110011110111000
  | 8137 => 11110000010001
  | 8138 => 11011000010010
  | 8139 => 100111001011011
  | 8140 => 11111100
  | 8141 => 1110100011111
  | 8142 => 10110000011010
  | 8143 => 10011100100111
  | 8144 => 1001011000110000
  | 8145 => 1101011110110
  | 8146 => 1001111101110
  | 8147 => 11001000011
  | 8148 => 111011000100
  | 8149 => 1000101011011
  | 8150 => 101011100
  | 8151 => 10110101001
  | 8152 => 1101110001000
  | 8153 => 100010110100001
  | 8154 => 111111011010
  | 8155 => 101110110010
  | 8156 => 1100101111110100
  | 8157 => 1001111000001
  | 8158 => 1101110101110
  | 8159 => 101000111111011
  | 8160 => 10001100000
  | 8161 => 1101000110111
  | 8162 => 1001110110
  | 8163 => 110110111101
  | 8164 => 100111000110000100
  | 8165 => 101001001010
  | 8166 => 10001000111010
  | 8167 => 100001101011
  | 8168 => 10011100011000
  | 8169 => 11101011100011
  | 8170 => 1110100000010
  | 8171 => 10111000010011
  | 8172 => 1101111011100
  | 8173 => 10110001
  | 8174 => 101000110110
  | 8175 => 100101011100
  | 8176 => 100110010000
  | 8177 => 100111011
  | 8178 => 1101000010110
  | 8179 => 101110011101101
  | 8180 => 110000100100
  | 8181 => 10111110111111111111
  | 8182 => 100111111001010
  | 8183 => 110011000001
  | 8184 => 10010011011000
  | 8185 => 111101111010
  | 8186 => 1000000000010
  | 8187 => 1100000010100101
  | 8188 => 100001111101100
  | 8189 => 10010100111111
  | 8190 => 101011111110
  | 8191 => 1000000110010001
  | 8192 => 10000000000000
  | 8193 => 1000011010101
  | 8194 => 1101100010110
  | 8195 => 11100111110
  | 8196 => 10000011110100
  | 8197 => 11010100011001
  | 8198 => 1011010111010
  | 8199 => 11011001101011
  | 8200 => 11111000
  | 8201 => 11001001010101
  | 8202 => 111010010010
  | 8203 => 1111101001101
  | 8204 => 1001001010100
  | 8205 => 1001010
  | 8206 => 1010000101110
  | 8207 => 100011101111
  | 8208 => 1101011101110000
  | 8209 => 1110010001111011
  | 8210 => 100001010110
  | 8211 => 101010111010011
  | 8212 => 110101100100100
  | 8213 => 1010010101
  | 8214 => 101001110010
  | 8215 => 11000000010
  | 8216 => 11101011010011000
  | 8217 => 11111101111111101111
  | 8218 => 101101110010110
  | 8219 => 10000011101001
  | 8220 => 111011100
  | 8221 => 1010110110100011
  | 8222 => 1110011110
  | 8223 => 111001101111
  | 8224 => 10100100000
  | 8225 => 1111000100
  | 8226 => 100101110101110
  | 8227 => 1110111010111
  | 8228 => 101100110100
  | 8229 => 1001111001111
  | 8230 => 11000111010
  | 8231 => 11001100010101
  | 8232 => 1100001000
  | 8233 => 1000100110111
  | 8234 => 10010010110010
  | 8235 => 1111101001110
  | 8236 => 100111100010100
  | 8237 => 1111010101111011
  | 8238 => 10110101111010
  | 8239 => 11011100111011
  | 8240 => 111000010000
  | 8241 => 1111011000111
  | 8242 => 1100010011110010
  | 8243 => 1101000010111
  | 8244 => 1111011110100
  | 8245 => 1010010010010
  | 8246 => 101011111010110
  | 8247 => 11000010101001
  | 8248 => 1001101000
  | 8249 => 11101001011
  | 8250 => 111111000
  | 8251 => 101111111010111
  | 8252 => 100001001110100
  | 8253 => 1010011111011
  | 8254 => 110010111111010
  | 8255 => 10100000111110
  | 8256 => 100100001000000
  | 8257 => 111011110110101
  | 8258 => 101101001110
  | 8259 => 1111100110101
  | 8260 => 1110110010100
  | 8261 => 10011101111
  | 8262 => 1111011010110
  | 8263 => 101111001011
  | 8264 => 111011001011000
  | 8265 => 10100111010
  | 8266 => 1011000110100010
  | 8267 => 10110011110101
  | 8268 => 10011101100
  | 8269 => 1000010101001
  | 8270 => 10001000010010
  | 8271 => 100010111101011
  | 8272 => 10011100110000
  | 8273 => 110011001011011
  | 8274 => 110101001010
  | 8275 => 11101111100
  | 8276 => 11011011100
  | 8277 => 1101110110101
  | 8278 => 1111001100010
  | 8279 => 1100001000111
  | 8280 => 11011111011000
  | 8281 => 10111101
  | 8282 => 111110111110
  | 8283 => 1001000111001
  | 8284 => 110111100100100
  | 8285 => 101011101110
  | 8286 => 101110110011010
  | 8287 => 11000010101011
  | 8288 => 1010100000
  | 8289 => 1110101001111
  | 8290 => 110000010
  | 8291 => 110010111100101
  | 8292 => 11111101100100
  | 8293 => 10011100011011
  | 8294 => 111111110110
  | 8295 => 1010111000010
  | 8296 => 1010010001000
  | 8297 => 1110011100001
  | 8298 => 100110011110110
  | 8299 => 101001001010101
  | 8300 => 10101100
  | 8301 => 10010000010111
  | 8302 => 101111011111110
  | 8303 => 11101111
  | 8304 => 10110011010000
  | 8305 => 11111110010
  | 8306 => 10000001100010
  | 8307 => 100110001011111
  | 8308 => 11100111100
  | 8309 => 100110010101101
  | 8310 => 10111011101010
  | 8311 => 11101011011
  | 8312 => 10101001111000
  | 8313 => 110100110111001
  | 8314 => 1000101100111110
  | 8315 => 1011111101010
  | 8316 => 100110110111111111111100
  | 8317 => 11100011111011
  | 8318 => 11010101111110
  | 8319 => 11110110011001
  | 8320 => 10010000000
  | 8321 => 101101100100101
  | 8322 => 1010101100010
  | 8323 => 1101111111110101
  | 8324 => 10001001111100
  | 8325 => 11111111100
  | 8326 => 11011010110
  | 8327 => 110110111001
  | 8328 => 10101001011000
  | 8329 => 1011111110001111
  | 8330 => 10100100010
  | 8331 => 1001100000000111
  | 8332 => 10010110001100
  | 8333 => 101010101101
  | 8334 => 1110111010110
  | 8335 => 111111101110
  | 8336 => 10101101110000
  | 8337 => 1100111111001
  | 8338 => 1001111100110
  | 8339 => 100000100101111
  | 8340 => 11011010100
  | 8341 => 10110100001011
  | 8342 => 1001000000110
  | 8343 => 10100110111101
  | 8344 => 11000111101000
  | 8345 => 1100010011010
  | 8346 => 111101101000110
  | 8347 => 1100101010111111
  | 8348 => 100111001011100
  | 8349 => 11001011000001
  | 8350 => 1111101100
  | 8351 => 10110111101111
  | 8352 => 1011110111100000
  | 8353 => 1110011100101
  | 8354 => 101010010110
  | 8355 => 10101000011010
  | 8356 => 10000001011100
  | 8357 => 1001110101
  | 8358 => 1101110101010010
  | 8359 => 100110101001001
  | 8360 => 100111000
  | 8361 => 10100111001111
  | 8362 => 101110001010
  | 8363 => 100000110001011
  | 8364 => 111000110000100
  | 8365 => 1011111010
  | 8366 => 11011101101010
  | 8367 => 10101100100001
  | 8368 => 1101110011010000
  | 8369 => 110111000111011
  | 8370 => 111110101110
  | 8371 => 1110010011011
  | 8372 => 1001010110100
  | 8373 => 10011000001011
  | 8374 => 11111111111110
  | 8375 => 1101011000
  | 8376 => 1011101001111000
  | 8377 => 11010000001
  | 8378 => 11100000010010
  | 8379 => 100111011010101
  | 8380 => 1000111100
  | 8381 => 1110110000010011
  | 8382 => 1011000001110
  | 8383 => 101011101011
  | 8384 => 101001000000
  | 8385 => 10100011100010
  | 8386 => 100110111001110
  | 8387 => 1011100010101
  | 8388 => 110010101111100
  | 8389 => 1010111101
  | 8390 => 111000111110
  | 8391 => 1110001010001
  | 8392 => 100001001111000
  | 8393 => 101001001101
  | 8394 => 11100010000110
  | 8395 => 1000110101010
  | 8396 => 100101100100
  | 8397 => 11101111101
  | 8398 => 110011100001010
  | 8399 => 11100110001
  | 8400 => 101010000
  | 8401 => 1001001001001
  | 8402 => 11111011111110
  | 8403 => 11111111000001
  | 8404 => 1111011111100
  | 8405 => 1011100000010
  | 8406 => 11110010011110
  | 8407 => 1110000111101
  | 8408 => 1010011000
  | 8409 => 1010110010001
  | 8410 => 1001100001010
  | 8411 => 10011000101100011
  | 8412 => 11110100000100
  | 8413 => 11010000111111
  | 8414 => 10000000001110
  | 8415 => 11111111111101111110
  | 8416 => 1000110100000
  | 8417 => 1000100110111001
  | 8418 => 1000011111001110
  | 8419 => 1010000111010101
  | 8420 => 10011001100
  | 8421 => 1100110101111
  | 8422 => 100001101111010
  | 8423 => 1011111100011001
  | 8424 => 1011011011101000
  | 8425 => 101100
  | 8426 => 10011101100110
  | 8427 => 110000100111
  | 8428 => 11100001110100
  | 8429 => 1001101111001
  | 8430 => 10111001010
  | 8431 => 1100001001
  | 8432 => 11011101110000
  | 8433 => 10000111111101
  | 8434 => 10101110110110
  | 8435 => 1110111000110
  | 8436 => 1010000100
  | 8437 => 111110000001
  | 8438 => 110001101010
  | 8439 => 1011110000001
  | 8440 => 110100011000
  | 8441 => 11011101001101
  | 8442 => 10101110101110
  | 8443 => 10101011011
  | 8444 => 11110001110100
  | 8445 => 1000111100010
  | 8446 => 1110100010
  | 8447 => 1001011000111
  | 8448 => 11111100000000
  | 8449 => 110000011111011
  | 8450 => 1011110100
  | 8451 => 100101001111011
  | 8452 => 1011000111110100
  | 8453 => 10100101101110011
  | 8454 => 101000111011110
  | 8455 => 110101010
  | 8456 => 1111111001000
  | 8457 => 11111001111
  | 8458 => 100101101100010
  | 8459 => 1101000000111
  | 8460 => 10011101111100
  | 8461 => 1011100000101
  | 8462 => 111111111010110
  | 8463 => 10010011011
  | 8464 => 10001110010000
  | 8465 => 111010010
  | 8466 => 1100110010010
  | 8467 => 1001111011001
  | 8468 => 10111000101100
  | 8469 => 10011000111111
  | 8470 => 110110
  | 8471 => 111000011101
  | 8472 => 10101101001000
  | 8473 => 11110111101
  | 8474 => 10011010010110
  | 8475 => 101010101100
  | 8476 => 10010001101100
  | 8477 => 10000101101011
  | 8478 => 100011111011010
  | 8479 => 1010010001
  | 8480 => 10001100000
  | 8481 => 1111011
  | 8482 => 110111011001010
  | 8483 => 11110110000001
  | 8484 => 1101011100
  | 8485 => 110000100010
  | 8486 => 11011001111010
  | 8487 => 11100111001101
  | 8488 => 1000011111001000
  | 8489 => 11101000011101
  | 8490 => 100111100010
  | 8491 => 1010110000101111
  | 8492 => 110011100100
  | 8493 => 1010101001001
  | 8494 => 1000101100110
  | 8495 => 110100110110
  | 8496 => 1010111110110000
  | 8497 => 10110011001
  | 8498 => 11010100111010
  | 8499 => 101011010110011
  | 8500 => 11101000
  | 8501 => 101110100100111
  | 8502 => 1010010011010
  | 8503 => 11111101101001
  | 8504 => 10000000110101000
  | 8505 => 110101110101010
  | 8506 => 110101111110
  | 8507 => 111100011011111
  | 8508 => 100101100100100
  | 8509 => 1101101010011
  | 8510 => 100001010
  | 8511 => 1000101111010011
  | 8512 => 11101111000000
  | 8513 => 11100010011011
  | 8514 => 110111101111111111110
  | 8515 => 10000000111010
  | 8516 => 101111100100100
  | 8517 => 10001110101111
  | 8518 => 1101000010010
  | 8519 => 101011000101011
  | 8520 => 10011000
  | 8521 => 1010011010101
  | 8522 => 10011000101110
  | 8523 => 1101011001111
  | 8524 => 1010010011110100
  | 8525 => 1100100100
  | 8526 => 1011111001110
  | 8527 => 1001010111
  | 8528 => 10111010000
  | 8529 => 111100110111
  | 8530 => 10010100010
  | 8531 => 1010100011101
  | 8532 => 11001111101100
  | 8533 => 1101100001001
  | 8534 => 1100101000010
  | 8535 => 10110100110
  | 8536 => 11100001000
  | 8537 => 101010010000001
  | 8538 => 100011101010
  | 8539 => 111000001000111
  | 8540 => 101001000100
  | 8541 => 11110100011101
  | 8542 => 1000111110100110
  | 8543 => 1100100110101
  | 8544 => 101111111100000
  | 8545 => 10110001010110
  | 8546 => 11001011001010
  | 8547 => 111111
  | 8548 => 111101000110100
  | 8549 => 1010101011010111
  | 8550 => 111101111100
  | 8551 => 100001110010011
  | 8552 => 1100001000
  | 8553 => 1011110001
  | 8554 => 11001000010
  | 8555 => 1010111110110
  | 8556 => 110000000100
  | 8557 => 100111001001011
  | 8558 => 11100111110
  | 8559 => 1011110010111
  | 8560 => 1000100110000
  | 8561 => 11001001010111
  | 8562 => 1110010011011010
  | 8563 => 100110010111101
  | 8564 => 111001100100100
  | 8565 => 10000100010
  | 8566 => 101011000110
  | 8567 => 10011010111011
  | 8568 => 111011111001000
  | 8569 => 11001100101101
  | 8570 => 100100111010
  | 8571 => 1000011111010011
  | 8572 => 100100110110100
  | 8573 => 1001001000100001
  | 8574 => 100111010010
  | 8575 => 110000100
  | 8576 => 11010110000000
  | 8577 => 100100011111011
  | 8578 => 11100001010010
  | 8579 => 110000101001
  | 8580 => 11111100
  | 8581 => 10110101000111
  | 8582 => 101101110101110
  | 8583 => 100101100011
  | 8584 => 100011111000
  | 8585 => 10010110
  | 8586 => 1101001111110
  | 8587 => 110111101
  | 8588 => 101000100001100
  | 8589 => 11111110111101
  | 8590 => 1011111110110
  | 8591 => 111000110001
  | 8592 => 110101110000
  | 8593 => 100101000101011
  | 8594 => 10111010001010
  | 8595 => 1011110110110
  | 8596 => 1000110001100
  | 8597 => 110101010110111
  | 8598 => 100000010101110
  | 8599 => 111111110001
  | 8600 => 1101101000
  | 8601 => 111001001101101
  | 8602 => 11000100011010
  | 8603 => 111010000011001
  | 8604 => 10100001111101100
  | 8605 => 101000000010
  | 8606 => 1001101011111110
  | 8607 => 1100110100001
  | 8608 => 10010001100000
  | 8609 => 100001010100001
  | 8610 => 1100101000110
  | 8611 => 11111010111111
  | 8612 => 1000001111100
  | 8613 => 1111011111111111111
  | 8614 => 11000110001010
  | 8615 => 1111111010
  | 8616 => 1001010111000
  | 8617 => 101110111110001
  | 8618 => 1111010110110
  | 8619 => 1000001011111011
  | 8620 => 10110010100
  | 8621 => 101000110011
  | 8622 => 110011111001010
  | 8623 => 1110111111101
  | 8624 => 101111010000
  | 8625 => 10000101000
  | 8626 => 100011101110110
  | 8627 => 1011011010111
  | 8628 => 10100000000100
  | 8629 => 10001011
  | 8630 => 1100011101010
  | 8631 => 1110010110100101
  | 8632 => 10100000001000
  | 8633 => 101001110100101
  | 8634 => 1100101110
  | 8635 => 10011101111110
  | 8636 => 100111001111100
  | 8637 => 10110011010111
  | 8638 => 1001101010
  | 8639 => 10110000101011
  | 8640 => 1101111111000000
  | 8641 => 110001110110011
  | 8642 => 101111011110
  | 8643 => 10100011011
  | 8644 => 1011011100100
  | 8645 => 10000000010
  | 8646 => 11110110
  | 8647 => 1111001001001
  | 8648 => 1010001001000
  | 8649 => 11110011101001
  | 8650 => 101100110100
  | 8651 => 101000001101
  | 8652 => 111011000100
  | 8653 => 11010011000111011
  | 8654 => 11100010101000010
  | 8655 => 1101111101010
  | 8656 => 101010110000
  | 8657 => 1101110000111
  | 8658 => 101011111110
  | 8659 => 101000101101011
  | 8660 => 1000100100
  | 8661 => 1011110000110011
  | 8662 => 1011101011010
  | 8663 => 10000000011100101
  | 8664 => 110111011011000
  | 8665 => 101110100010
  | 8666 => 110100100110
  | 8667 => 10101001111101
  | 8668 => 1101010010100
  | 8669 => 1110011000011
  | 8670 => 1010100110010
  | 8671 => 10011001001001
  | 8672 => 1111100000
  | 8673 => 10100001101001
  | 8674 => 100111101110
  | 8675 => 101011110100
  | 8676 => 100101111011100
  | 8677 => 111111110110101
  | 8678 => 111011000100110
  | 8679 => 101100100101
  | 8680 => 10000011000
  | 8681 => 100110010101001
  | 8682 => 10001111000010
  | 8683 => 101110010110101
  | 8684 => 10010010110100
  | 8685 => 1100111111010
  | 8686 => 101101001010
  | 8687 => 11010111011011
  | 8688 => 111100010010000
  | 8689 => 10001111110011
  | 8690 => 100100110
  | 8691 => 110010101100111
  | 8692 => 1001101100
  | 8693 => 1001000111011001
  | 8694 => 11011111100010
  | 8695 => 1001110111110
  | 8696 => 10001001111000
  | 8697 => 111001110010011
  | 8698 => 10000010100010
  | 8699 => 11000001101011
  | 8700 => 1101011100
  | 8701 => 10110000011111
  | 8702 => 10111100110110
  | 8703 => 11011001110011
  | 8704 => 11101000000000
  | 8705 => 11100111110
  | 8706 => 10101101110110
  | 8707 => 10000001100101011
  | 8708 => 10111101100100
  | 8709 => 111110110011
  | 8710 => 1110011110
  | 8711 => 1000011000001001
  | 8712 => 10011111111111111111000
  | 8713 => 11001001100111
  | 8714 => 1110111011010
  | 8715 => 101000000010
  | 8716 => 10010001111100
  | 8717 => 100111110011
  | 8718 => 10000110011010
  | 8719 => 1010101111111
  | 8720 => 10010101110000
  | 8721 => 111101101011
  | 8722 => 11000001101110
  | 8723 => 1010010001
  | 8724 => 11010000101100
  | 8725 => 110010000100
  | 8726 => 11100001101010
  | 8727 => 10100100010011
  | 8728 => 100000101011000
  | 8729 => 110100111010001
  | 8730 => 1100111011110
  | 8731 => 110110011000111
  | 8732 => 10111001100
  | 8733 => 111011000111001
  | 8734 => 11010111100010
  | 8735 => 1100000000010
  | 8736 => 1010100000
  | 8737 => 11001001100101
  | 8738 => 101001001010010
  | 8739 => 11010110100111
  | 8740 => 1110111100
  | 8741 => 1111111000001
  | 8742 => 11011101101010
  | 8743 => 1011000101111
  | 8744 => 111111101000
  | 8745 => 1001110110
  | 8746 => 10000111111110
  | 8747 => 10000011100101
  | 8748 => 100101101111100
  | 8749 => 1011110110101
  | 8750 => 10010000
  | 8751 => 10001101011111
  | 8752 => 1001010000
  | 8753 => 11110000111101
  | 8754 => 10011111011110110
  | 8755 => 1000011001010
  | 8756 => 1000110101100
  | 8757 => 100111101111
  | 8758 => 101111110
  | 8759 => 100011111001111
  | 8760 => 1110111000
  | 8761 => 1000001000010111
  | 8762 => 1011101110110
  | 8763 => 101011101
  | 8764 => 1100101100
  | 8765 => 1001000111010
  | 8766 => 111111110010
  | 8767 => 11100110011001
  | 8768 => 10001000000
  | 8769 => 101010111
  | 8770 => 10101110100110
  | 8771 => 1011101000011011
  | 8772 => 110101100100
  | 8773 => 101010101001001
  | 8774 => 1000000111010
  | 8775 => 101100101111100
  | 8776 => 1111001011000
  | 8777 => 1001100101100111
  | 8778 => 101101010010
  | 8779 => 100000000001
  | 8780 => 1000110001100
  | 8781 => 1001011000111101
  | 8782 => 111001011110
  | 8783 => 110011001001
  | 8784 => 1110110111010000
  | 8785 => 1000011010110
  | 8786 => 111011110
  | 8787 => 11010111
  | 8788 => 110011010001100
  | 8789 => 100010110101
  | 8790 => 10011010110
  | 8791 => 10011001011101
  | 8792 => 10010111111111111000
  | 8793 => 11011011010101
  | 8794 => 111101111011010
  | 8795 => 111011000110
  | 8796 => 1110011000100
  | 8797 => 11000101001111
  | 8798 => 111101100010
  | 8799 => 1110101101011
  | 8800 => 1100000
  | 8801 => 1011000010111
  | 8802 => 11010101011110
  | 8803 => 111110000010001
  | 8804 => 1001001110000100
  | 8805 => 11010111010110
  | 8806 => 1001110110
  | 8807 => 110010110011111
  | 8808 => 1101000
  | 8809 => 110001110010011
  | 8810 => 1001001010
  | 8811 => 1111011111111111111
  | 8812 => 1100010111100
  | 8813 => 100001111
  | 8814 => 11100111110010
  | 8815 => 10100100011110
  | 8816 => 10100111010000
  | 8817 => 10001001011001
  | 8818 => 100101010110
  | 8819 => 1010000111111
  | 8820 => 1111111010100
  | 8821 => 1010000010111
  | 8822 => 10010001000010
  | 8823 => 1011001101
  | 8824 => 1110100011000
  | 8825 => 1010110100100
  | 8826 => 1001110100010
  | 8827 => 1110110001
  | 8828 => 1111111010101100
  | 8829 => 1101111110001
  | 8830 => 11011010
  | 8831 => 1011000000001
  | 8832 => 100001010000000
  | 8833 => 1001110111001
  | 8834 => 11111010011010
  | 8835 => 10011011000010
  | 8836 => 11100011100100100
  | 8837 => 1100101101101
  | 8838 => 11101101100110
  | 8839 => 11010101110101
  | 8840 => 100111011000
  | 8841 => 10101111010011
  | 8842 => 101011100001010
  | 8843 => 101010111110001
  | 8844 => 11011001100
  | 8845 => 101001011111110
  | 8846 => 110000010
  | 8847 => 110010111011001
  | 8848 => 1100011010000
  | 8849 => 1001000110011
  | 8850 => 10010111100
  | 8851 => 10001110101111
  | 8852 => 10001000001100
  | 8853 => 11100101101011
  | 8854 => 1000000111010
  | 8855 => 100101011010
  | 8856 => 1101011100111000
  | 8857 => 1011100001101
  | 8858 => 10010101110010
  | 8859 => 1000000110001011
  | 8860 => 11000000100
  | 8861 => 10111011000101
  | 8862 => 10001001001110
  | 8863 => 110110000111101
  | 8864 => 11011110100000
  | 8865 => 1011110110110
  | 8866 => 100100110110
  | 8867 => 110101100110101
  | 8868 => 100010101100100
  | 8869 => 111111100101001
  | 8870 => 110000001110
  | 8871 => 1011100000101
  | 8872 => 1100010101101000
  | 8873 => 10010101010001
  | 8874 => 110011111110
  | 8875 => 10011000
  | 8876 => 100011011011100
  | 8877 => 110011001001
  | 8878 => 1100111111010
  | 8879 => 111110110111
  | 8880 => 1110000
  | 8881 => 111010111011
  | 8882 => 111010001011010
  | 8883 => 1100111111001
  | 8884 => 100000101011100
  | 8885 => 1010100110
  | 8886 => 100101101010
  | 8887 => 1001110011111101
  | 8888 => 1111000
  | 8889 => 1000110110100111
  | 8890 => 10011100111110
  | 8891 => 10110110101011
  | 8892 => 101110011011100
  | 8893 => 1001110110110101
  | 8894 => 11111100011010
  | 8895 => 100101110010
  | 8896 => 110110101000000
  | 8897 => 1010001001101001
  | 8898 => 10111111010010
  | 8899 => 100110111101011
  | 8900 => 1101010100
  | 8901 => 101111010100001001
  | 8902 => 100100010100010
  | 8903 => 1011001101001001
  | 8904 => 100111011000
  | 8905 => 100110010
  | 8906 => 10011101010
  | 8907 => 11001110011101
  | 8908 => 111100011010100
  | 8909 => 10111010111011
  | 8910 => 11111111111111110110
  | 8911 => 1101010110001011
  | 8912 => 11101010000
  | 8913 => 10110100101111
  | 8914 => 10010110010
  | 8915 => 11001110
  | 8916 => 111101110010100
  | 8917 => 10101000000111
  | 8918 => 11011010010
  | 8919 => 110111111001
  | 8920 => 1001111001000
  | 8921 => 11011110011
  | 8922 => 10001011111110
  | 8923 => 1110011001011
  | 8924 => 10001011011100
  | 8925 => 10011101100
  | 8926 => 110011111110110
  | 8927 => 10011010011011
  | 8928 => 1111101011100000
  | 8929 => 10111001010111
  | 8930 => 1000011110110
  | 8931 => 100101111000111
  | 8932 => 1111111101100
  | 8933 => 100010000011
  | 8934 => 1110100111110
  | 8935 => 10010010111110
  | 8936 => 11011110101000
  | 8937 => 1110111001101
  | 8938 => 100010000001110
  | 8939 => 1001111000100001
  | 8940 => 1000011101100
  | 8941 => 1000100001100011
  | 8942 => 10001101100011010
  | 8943 => 100001001111010110111
  | 8944 => 1100111100010000
  | 8945 => 111011010110
  | 8946 => 101001111011010
  | 8947 => 1011011
  | 8948 => 11000000100
  | 8949 => 10001111101101
  | 8950 => 1101011100
  | 8951 => 10011010100101
  | 8952 => 101011011000
  | 8953 => 111011101100011
  | 8954 => 1000110001110
  | 8955 => 101011100110110
  | 8956 => 10111100100
  | 8957 => 1010001110001
  | 8958 => 1001001100100010
  | 8959 => 1000010111111
  | 8960 => 100100000000
  | 8961 => 100101010101
  | 8962 => 110011011010010
  | 8963 => 10000010110111
  | 8964 => 10011011111100
  | 8965 => 1001000110110
  | 8966 => 11011010110
  | 8967 => 10100001101001
  | 8968 => 100100010001000
  | 8969 => 100101001101001
  | 8970 => 100101011010
  | 8971 => 100101010000001
  | 8972 => 1011101110100
  | 8973 => 11100110101101
  | 8974 => 1010101011010
  | 8975 => 100101011100
  | 8976 => 1001110110000
  | 8977 => 110111101001
  | 8978 => 10111001110110
  | 8979 => 1010001100011
  | 8980 => 11110011100
  | 8981 => 100010000111
  | 8982 => 101001010111110
  | 8983 => 111100100111
  | 8984 => 100011011000
  | 8985 => 1100000000010
  | 8986 => 11011101000010
  | 8987 => 11110010001101
  | 8988 => 1111111101011100
  | 8989 => 1010111000111
  | 8990 => 111011110010010
  | 8991 => 1111111111111111111111110111
  | 8992 => 10100011100000
  | 8993 => 1011111111111
  | 8994 => 1100101110
  | 8995 => 1001111100010
  | 8996 => 101110011011100
  | 8997 => 101000010101001
  | 8998 => 11000010010
  | 8999 => 11010111000110011101
  | _ => 1

def witness_fast_9 : Nat → Nat
  | 9000 => 111111111000
  | 9001 => 10000111
  | 9002 => 11111011110010
  | 9003 => 11001000111111
  | 9004 => 10110110111100
  | 9005 => 110110100110110
  | 9006 => 101101110001110
  | 9007 => 1011001010001
  | 9008 => 11010011110000
  | 9009 => 111111111111111111
  | 9010 => 1000110
  | 9011 => 10100100000000101
  | 9012 => 11100100001100
  | 9013 => 111011111101
  | 9014 => 10100010010110
  | 9015 => 111001100010
  | 9016 => 110100011000
  | 9017 => 100010111011001
  | 9018 => 110111010010110
  | 9019 => 101110010110011
  | 9020 => 111111111100
  | 9021 => 10111111000101
  | 9022 => 10100111001110
  | 9023 => 11011001110011
  | 9024 => 10011000000
  | 9025 => 1110111100
  | 9026 => 111111100111110
  | 9027 => 101001011110101
  | 9028 => 11001000110100
  | 9029 => 11001111101111
  | 9030 => 11100010110
  | 9031 => 100000001101
  | 9032 => 100000011001000
  | 9033 => 1010001111111
  | 9034 => 100100101110010
  | 9035 => 10100100010
  | 9036 => 11010011111100
  | 9037 => 101011110001011
  | 9038 => 10010010011001010
  | 9039 => 110000101000011
  | 9040 => 10110110000
  | 9041 => 100000111111101
  | 9042 => 110011111111110
  | 9043 => 1101111011001
  | 9044 => 100010101011100
  | 9045 => 10101110101110
  | 9046 => 1110010100110
  | 9047 => 1001111011101
  | 9048 => 101110010001000
  | 9049 => 1011100000110001
  | 9050 => 100111100
  | 9051 => 111001111011
  | 9052 => 10001011001100
  | 9053 => 11000100111011
  | 9054 => 11110000111110
  | 9055 => 1001001111010
  | 9056 => 1001011101100000
  | 9057 => 1000101111
  | 9058 => 1100001100110010
  | 9059 => 110111001111011
  | 9060 => 1000101101100
  | 9061 => 10011000101011
  | 9062 => 110000010010010
  | 9063 => 1101101001111
  | 9064 => 11100001000
  | 9065 => 101111010
  | 9066 => 11100010000110
  | 9067 => 1110100011
  | 9068 => 11101111101111100
  | 9069 => 10100111010111
  | 9070 => 100010110110
  | 9071 => 100001110001111
  | 9072 => 10110110111010000
  | 9073 => 1011001101101011
  | 9074 => 11001000010
  | 9075 => 100011110100
  | 9076 => 111100001011100
  | 9077 => 101110001011
  | 9078 => 100010011110
  | 9079 => 11111011110101
  | 9080 => 11001101000
  | 9081 => 10010001111111
  | 9082 => 1011011010010
  | 9083 => 1001101011
  | 9084 => 11100110000100
  | 9085 => 11110101010
  | 9086 => 1111100000010
  | 9087 => 1000101101101011
  | 9088 => 100110000000
  | 9089 => 100100100100001
  | 9090 => 10111111111111111110
  | 9091 => 100001
  | 9092 => 10110010101100
  | 9093 => 11001111101001
  | 9094 => 1111101101111110
  | 9095 => 1010010100110
  | 9096 => 100111000101000
  | 9097 => 10111101111001
  | 9098 => 1110100110000010
  | 9099 => 10000111001010111
  | 9100 => 100100
  | 9101 => 100111
  | 9102 => 100011001110
  | 9103 => 10000111000111
  | 9104 => 10110100110000
  | 9105 => 11100100001010
  | 9106 => 101100111100110
  | 9107 => 11001010111
  | 9108 => 1111011111111111101100
  | 9109 => 1110000000101111
  | 9110 => 1010000110010
  | 9111 => 10011011011011
  | 9112 => 11110101001000
  | 9113 => 111100011101001
  | 9114 => 100100110110
  | 9115 => 11100010010
  | 9116 => 100100111110100
  | 9117 => 101110110111
  | 9118 => 10010111001110
  | 9119 => 11011001001
  | 9120 => 1100100000
  | 9121 => 10011111011111
  | 9122 => 101001110110
  | 9123 => 101110010000001
  | 9124 => 1001001111100
  | 9125 => 10001000
  | 9126 => 10111010110110
  | 9127 => 11101000000101
  | 9128 => 100100011011000
  | 9129 => 1010110000111101
  | 9130 => 11111000010
  | 9131 => 110101101100111
  | 9132 => 1010000101100100
  | 9133 => 10110101010011
  | 9134 => 10011001010
  | 9135 => 1011111001110
  | 9136 => 10000100010000
  | 9137 => 110001010001
  | 9138 => 110000000010
  | 9139 => 10110101001
  | 9140 => 100110100100
  | 9141 => 1101001100001
  | 9142 => 111010000111010
  | 9143 => 101001100010101
  | 9144 => 11111111001000
  | 9145 => 10101000010
  | 9146 => 1100110010010
  | 9147 => 1000100110100001
  | 9148 => 10000011101100
  | 9149 => 1110010101011
  | 9150 => 10010100
  | 9151 => 1010110000000011
  | 9152 => 1001000000
  | 9153 => 1111110010011
  | 9154 => 101010111100010
  | 9155 => 11000100000010
  | 9156 => 10100100110100
  | 9157 => 110011111000001
  | 9158 => 10010111101110
  | 9159 => 111000110001
  | 9160 => 10000100011000
  | 9161 => 100000111011
  | 9162 => 1110110111010
  | 9163 => 1010010001
  | 9164 => 1000001110100
  | 9165 => 1101000010110
  | 9166 => 110011111110
  | 9167 => 100111001101
  | 9168 => 100000000110000
  | 9169 => 110010101111011101
  | 9170 => 101100011110
  | 9171 => 11001110110011
  | 9172 => 110100000100
  | 9173 => 111111010110001
  | 9174 => 1110000011010
  | 9175 => 110100
  | 9176 => 111010101000
  | 9177 => 1001001101110101
  | 9178 => 110101000110010
  | 9179 => 1000010001001
  | 9180 => 11110110101100
  | 9181 => 1011101000001011
  | 9182 => 11001000110
  | 9183 => 110100010101
  | 9184 => 101110100000
  | 9185 => 11000011110
  | 9186 => 10100100100110
  | 9187 => 11011101110101
  | 9188 => 1001101111011100
  | 9189 => 11010110010111
  | 9190 => 10101110100110
  | 9191 => 101101
  | 9192 => 10100111001000
  | 9193 => 1000011111011
  | 9194 => 101000100101010
  | 9195 => 101100110010
  | 9196 => 1100000001100
  | 9197 => 11001111111
  | 9198 => 111101000111010
  | 9199 => 1101111101
  | 9200 => 1101010000
  | 9201 => 1000000010101011
  | 9202 => 111011111111110
  | 9203 => 111110000111
  | 9204 => 11111000000100
  | 9205 => 1011001001010
  | 9206 => 1110110110100110
  | 9207 => 101111111111110101111
  | 9208 => 110100011111000
  | 9209 => 11011100001
  | 9210 => 10111110001110
  | 9211 => 10110011110111
  | 9212 => 1100000000101100
  | 9213 => 10100000001
  | 9214 => 100110110
  | 9215 => 11011011001010
  | 9216 => 1111111110000000000
  | 9217 => 1010111011101101
  | 9218 => 11110100000010
  | 9219 => 11011001011101
  | 9220 => 11110100
  | 9221 => 110110101111111
  | 9222 => 11111011010010
  | 9223 => 10111001111011
  | 9224 => 100100001000
  | 9225 => 11100111101100
  | 9226 => 11011110001010
  | 9227 => 1110111101001
  | 9228 => 110100000011100
  | 9229 => 100001010010011
  | 9230 => 101001001010
  | 9231 => 1100010001101
  | 9232 => 1100010110000
  | 9233 => 110001011001
  | 9234 => 1111011010110
  | 9235 => 1011011100110
  | 9236 => 1011111100
  | 9237 => 1100110101111
  | 9238 => 111100011100110
  | 9239 => 1001000000101
  | 9240 => 111111000
  | 9241 => 100110110111111
  | 9242 => 11011001100010
  | 9243 => 11101011010011
  | 9244 => 1001100010100
  | 9245 => 101100011011110
  | 9246 => 111010111110
  | 9247 => 1011001000001111
  | 9248 => 110011000100000
  | 9249 => 110011011010101
  | 9250 => 111000
  | 9251 => 10100111000111
  | 9252 => 11011001111100
  | 9253 => 100110000111111
  | 9254 => 1101110001110
  | 9255 => 10100000010
  | 9256 => 11111010001000
  | 9257 => 10111110000001
  | 9258 => 11010001001010
  | 9259 => 1001000110101
  | 9260 => 11010001100
  | 9261 => 10110111001011
  | 9262 => 11111111110110
  | 9263 => 10111000111101
  | 9264 => 110010000
  | 9265 => 11011110010010
  | 9266 => 1001111010110
  | 9267 => 1011001000101
  | 9268 => 1001001110111100
  | 9269 => 1101100001001
  | 9270 => 1111011011010
  | 9271 => 1011101110001
  | 9272 => 10001011000
  | 9273 => 1011100101
  | 9274 => 101011011011010
  | 9275 => 10011101100
  | 9276 => 1011100001100
  | 9277 => 100001010000111
  | 9278 => 101100000110
  | 9279 => 101000100111111
  | 9280 => 1101101000000
  | 9281 => 11000000100001
  | 9282 => 1001110110
  | 9283 => 1000110011101
  | 9284 => 11111110000100
  | 9285 => 110100100110
  | 9286 => 1001111101010010
  | 9287 => 1110010101
  | 9288 => 101011111101000
  | 9289 => 1111100010111
  | 9290 => 11000001010
  | 9291 => 1000011010010001
  | 9292 => 1010100101100
  | 9293 => 10000010111101
  | 9294 => 1111010011110
  | 9295 => 101111010
  | 9296 => 101000000010000
  | 9297 => 11101101100011
  | 9298 => 11111110
  | 9299 => 10010100100101
  | 9300 => 1000001100
  | 9301 => 10001010011101
  | 9302 => 111110111010
  | 9303 => 110011110111
  | 9304 => 1001101011101000
  | 9305 => 1001111011110
  | 9306 => 111111110111111110110
  | 9307 => 1111111011001
  | 9308 => 1110110010100
  | 9309 => 10010001110001
  | 9310 => 1010011000110
  | 9311 => 110011111101001
  | 9312 => 10011011100000
  | 9313 => 110111110001
  | 9314 => 1001011100010110
  | 9315 => 11010110110110
  | 9316 => 1001111101100
  | 9317 => 1101111011
  | 9318 => 100010100010110
  | 9319 => 1110001000111111
  | 9320 => 111110011000
  | 9321 => 101100011101011
  | 9322 => 100010100101010
  | 9323 => 100101100011011
  | 9324 => 1010111111100
  | 9325 => 10101101100
  | 9326 => 10110010101010
  | 9327 => 11011111101
  | 9328 => 10010110000
  | 9329 => 11000110011101
  | 9330 => 111011111010
  | 9331 => 111001000100011
  | 9332 => 11100110010100
  | 9333 => 10100011111101
  | 9334 => 1010001011110
  | 9335 => 11101111110010
  | 9336 => 11010100011000
  | 9337 => 100011000101111
  | 9338 => 100110010010010
  | 9339 => 10100100100101
  | 9340 => 10000011100
  | 9341 => 1101111111101
  | 9342 => 11111110001010
  | 9343 => 101101110110011
  | 9344 => 100010000000
  | 9345 => 1010010011010
  | 9346 => 11001010101010
  | 9347 => 11100111010001
  | 9348 => 1110011100110100
  | 9349 => 1001111011001
  | 9350 => 100101100
  | 9351 => 10110111010011
  | 9352 => 100100101101000
  | 9353 => 10000110100010011
  | 9354 => 11001101101110
  | 9355 => 1101011111010
  | 9356 => 10001110000100
  | 9357 => 11100010011111
  | 9358 => 110111001001110
  | 9359 => 100100101111101
  | 9360 => 101011111110000
  | 9361 => 110001111
  | 9362 => 11100000111010
  | 9363 => 101111010100101
  | 9364 => 101101001100
  | 9365 => 110000110010
  | 9366 => 11001000001110
  | 9367 => 10000001000000111
  | 9368 => 100010111001000
  | 9369 => 110011010011101
  | 9370 => 101101110010
  | 9371 => 11001001111
  | 9372 => 100111001100
  | 9373 => 1110110001
  | 9374 => 111111100010
  | 9375 => 11100000
  | 9376 => 11000011100000
  | 9377 => 10010110001000111
  | 9378 => 10100111111010
  | 9379 => 1111011101111
  | 9380 => 110010000100
  | 9381 => 111010000000011
  | 9382 => 10011110010
  | 9383 => 11011110011
  | 9384 => 1011111111111000
  | 9385 => 1101101000010
  | 9386 => 101100011100010
  | 9387 => 101111100100101
  | 9388 => 1001101111010100
  | 9389 => 10101010111111
  | 9390 => 11000000010
  | 9391 => 111011011
  | 9392 => 100101110000
  | 9393 => 1010001111
  | 9394 => 10100100010
  | 9395 => 1010111110110
  | 9396 => 101101110101100
  | 9397 => 100010110000101
  | 9398 => 1110101111010
  | 9399 => 101101100110101
  | 9400 => 10011000
  | 9401 => 110001101
  | 9402 => 10101011011110
  | 9403 => 1000110010011
  | 9404 => 10111101101100
  | 9405 => 1111111111111111110
  | 9406 => 1111101010010
  | 9407 => 10101110010001
  | 9408 => 1100001000000
  | 9409 => 1010001111010101
  | 9410 => 1000010110
  | 9411 => 111011100001101
  | 9412 => 101110101101100
  | 9413 => 101100110001
  | 9414 => 101101101010110
  | 9415 => 101100110011110
  | 9416 => 110100111000
  | 9417 => 1001100110001
  | 9418 => 110111111100010010
  | 9419 => 1000100001
  | 9420 => 11011110110100
  | 9421 => 1010001000010001
  | 9422 => 10000011010010
  | 9423 => 1011110110011
  | 9424 => 110110010110000
  | 9425 => 1110001100
  | 9426 => 1000011011110110
  | 9427 => 1100011111111
  | 9428 => 1110011001100
  | 9429 => 110010101111001
  | 9430 => 10010011010
  | 9431 => 1001110111000011
  | 9432 => 1001100111111000
  | 9433 => 110110011001101
  | 9434 => 1100101101000010
  | 9435 => 1000110
  | 9436 => 10111011101100
  | 9437 => 10101110001
  | 9438 => 11111101111110
  | 9439 => 1101000101010001
  | 9440 => 1101111100000
  | 9441 => 1011111000111
  | 9442 => 10010101110110
  | 9443 => 10011000010011
  | 9444 => 10001010010100100
  | 9445 => 1100001101011110
  | 9446 => 1001111110010010
  | 9447 => 1100101100001
  | 9448 => 101010010001000
  | 9449 => 111011000111
  | 9450 => 101011101011100
  | 9451 => 110100001011
  | 9452 => 101001000100
  | 9453 => 100011010101
  | 9454 => 111110101101110
  | 9455 => 10010111011110
  | 9456 => 110101001010000
  | 9457 => 1011100101011
  | 9458 => 1101001111011010
  | 9459 => 1010001111100011
  | 9460 => 11111101100
  | 9461 => 10100100011
  | 9462 => 1111011111110010
  | 9463 => 11010101110111
  | 9464 => 10111101000
  | 9465 => 11111010011010
  | 9466 => 100110100001110
  | 9467 => 101111111100101
  | 9468 => 11101001111100
  | 9469 => 10011001100101
  | 9470 => 10110011010
  | 9471 => 100001000110011
  | 9472 => 11100000000
  | 9473 => 11010000000111
  | 9474 => 10111111010010
  | 9475 => 10010110100
  | 9476 => 1000001100001100
  | 9477 => 11100001101111
  | 9478 => 10110000101110
  | 9479 => 10110001001011
  | 9480 => 101010111000
  | 9481 => 11110110000001
  | 9482 => 10110110010110
  | 9483 => 10110000000111
  | 9484 => 10001101111100
  | 9485 => 10111010
  | 9486 => 110001111010110
  | 9487 => 111011001101111
  | 9488 => 10010000110000
  | 9489 => 1100111001111
  | 9490 => 100110010
  | 9491 => 1011101011001
  | 9492 => 11001111011100
  | 9493 => 100001100101111
  | 9494 => 10111110
  | 9495 => 10011110011110
  | 9496 => 100010000101000
  | 9497 => 10011101101
  | 9498 => 11001011010
  | 9499 => 101110010011101
  | 9500 => 11001000
  | 9501 => 1110111101001
  | 9502 => 1010110110
  | 9503 => 10011010110101
  | 9504 => 111101111111111111100000
  | 9505 => 1000101101110
  | 9506 => 11000111111010
  | 9507 => 100000001001111
  | 9508 => 100001011110100
  | 9509 => 10100101111011
  | 9510 => 10011111010110
  | 9511 => 1010101010011101
  | 9512 => 100010011001000
  | 9513 => 11001100011111
  | 9514 => 101011000111110
  | 9515 => 10110011010
  | 9516 => 11001000110100
  | 9517 => 110101001010001
  | 9518 => 10010111010010
  | 9519 => 1100101111101
  | 9520 => 1001110110000
  | 9521 => 11000011001101
  | 9522 => 11010110110110
  | 9523 => 110101110010101
  | 9524 => 1110101011100
  | 9525 => 10101110100
  | 9526 => 1100110110
  | 9527 => 1000011000001111
  | 9528 => 11000101011000
  | 9529 => 10001011001111
  | 9530 => 1001010110110
  | 9531 => 11110110100101
  | 9532 => 10101000110100
  | 9533 => 11000100101
  | 9534 => 1001110111111110
  | 9535 => 110111000010
  | 9536 => 110111000000
  | 9537 => 10000000111101
  | 9538 => 1000011101100010
  | 9539 => 101111101101
  | 9540 => 1111110110100
  | 9541 => 110100001011
  | 9542 => 1101110111010
  | 9543 => 11111100101001
  | 9544 => 11011100101000
  | 9545 => 10010011000110
  | 9546 => 111111001110
  | 9547 => 10011010101011
  | 9548 => 1001001101100
  | 9549 => 1111101100101
  | 9550 => 1110111100
  | 9551 => 1111011011101
  | 9552 => 11000101110000
  | 9553 => 100000011101
  | 9554 => 1010001110
  | 9555 => 101111010
  | 9556 => 11111000100
  | 9557 => 1000111101111111
  | 9558 => 11000011111110
  | 9559 => 1001011110011
  | 9560 => 1111111000
  | 9561 => 1001010010000011
  | 9562 => 1111101101110
  | 9563 => 1010111001
  | 9564 => 1000110110100
  | 9565 => 100101111010
  | 9566 => 10000101110110
  | 9567 => 101100011101101
  | 9568 => 1001010110100000
  | 9569 => 101001001011001
  | 9570 => 1111010010
  | 9571 => 10111101101
  | 9572 => 1011001101100
  | 9573 => 110010111111
  | 9574 => 1101010
  | 9575 => 1101010100
  | 9576 => 1111011111000
  | 9577 => 10111010101011
  | 9578 => 101000010
  | 9579 => 100011110101101
  | 9580 => 10011100
  | 9581 => 1100100001
  | 9582 => 10011011101110
  | 9583 => 11101110111
  | 9584 => 101011101110000
  | 9585 => 1110011111010
  | 9586 => 100100111010010
  | 9587 => 11011111010111
  | 9588 => 10001011010100
  | 9589 => 1011000000001
  | 9590 => 100110010
  | 9591 => 100001000010111
  | 9592 => 1111100111000
  | 9593 => 11000000101001
  | 9594 => 11010111001110
  | 9595 => 11111010
  | 9596 => 11101010011100
  | 9597 => 11010010101111
  | 9598 => 10011011010110
  | 9599 => 101110001011
  | 9600 => 1110000000
  | 9601 => 111001011001
  | 9602 => 10001011110
  | 9603 => 11111111011111111011
  | 9604 => 110110100100
  | 9605 => 11110111011110
  | 9606 => 100101100110
  | 9607 => 110111000110111
  | 9608 => 10111100101000
  | 9609 => 1011001001110101
  | 9610 => 10100110
  | 9611 => 11010001101001
  | 9612 => 11001111101100
  | 9613 => 10101111101111
  | 9614 => 11111110010110
  | 9615 => 10111010101110
  | 9616 => 110010111110000
  | 9617 => 101010101010001
  | 9618 => 110010101101110
  | 9619 => 11110010111011
  | 9620 => 1010100
  | 9621 => 11111110101
  | 9622 => 101110011101110
  | 9623 => 11111011101001
  | 9624 => 101000111001000
  | 9625 => 1001000
  | 9626 => 1101110000110010
  | 9627 => 111101000001
  | 9628 => 101100011001100
  | 9629 => 1011011000001
  | 9630 => 1110101110110
  | 9631 => 110010100110001
  | 9632 => 110100111100000
  | 9633 => 10101000010101
  | 9634 => 100000101110
  | 9635 => 101000111010110
  | 9636 => 1100111111111100
  | 9637 => 1001001001111
  | 9638 => 10001101000010
  | 9639 => 11111110000011
  | 9640 => 111101000
  | 9641 => 110010000110101
  | 9642 => 100000011011010
  | 9643 => 10101110001
  | 9644 => 100011101111100
  | 9645 => 11101101001110
  | 9646 => 1001110110
  | 9647 => 1010101100010101
  | 9648 => 11111101110000
  | 9649 => 1101011100111
  | 9650 => 1100100
  | 9651 => 110101000010001
  | 9652 => 11000101101011100
  | 9653 => 111000011101
  | 9654 => 100010101000110
  | 9655 => 1100110010
  | 9656 => 111110111011000
  | 9657 => 10111101111
  | 9658 => 100111011110110
  | 9659 => 1110000100001
  | 9660 => 10110011100
  | 9661 => 100001011
  | 9662 => 10000111110110
  | 9663 => 11101100101101
  | 9664 => 1110001000000
  | 9665 => 1010100110110
  | 9666 => 101101100101110
  | 9667 => 110101101011111
  | 9668 => 1000101011001100
  | 9669 => 100001010000111
  | 9670 => 100100001010
  | 9671 => 10000010101101001
  | 9672 => 10010011011000
  | 9673 => 110010111100011
  | 9674 => 1111001001110
  | 9675 => 1111101110100
  | 9676 => 100000001101100
  | 9677 => 11001111100011
  | 9678 => 10010011000110
  | 9679 => 100100100100101
  | 9680 => 110110000
  | 9681 => 1101000100011
  | 9682 => 11100000111110
  | 9683 => 1001111010111
  | 9684 => 110101001111100
  | 9685 => 1010110111010
  | 9686 => 110101101010
  | 9687 => 10011110011110111
  | 9688 => 1011100110111000
  | 9689 => 110101001001101
  | 9690 => 1111011010110
  | 9691 => 1101101111
  | 9692 => 111010001111100
  | 9693 => 110101110111
  | 9694 => 1001100010110
  | 9695 => 1011010111011110
  | 9696 => 101111100000
  | 9697 => 111000011000011
  | 9698 => 1010000101110
  | 9699 => 101111011010001
  | 9700 => 1110000100
  | 9701 => 101001001101
  | 9702 => 11111111111101111110
  | 9703 => 1100000001
  | 9704 => 111000110111000
  | 9705 => 101100110010
  | 9706 => 1101000110
  | 9707 => 1101110110110101
  | 9708 => 10001010011100
  | 9709 => 10001000010001
  | 9710 => 10011010
  | 9711 => 11000110011111
  | 9712 => 10010110101010000
  | 9713 => 11011011101101
  | 9714 => 1111001011110
  | 9715 => 101111011011110
  | 9716 => 1110110001100100
  | 9717 => 10000111000111011
  | 9718 => 1011101001110
  | 9719 => 1000010000111001
  | 9720 => 100111110111000
  | 9721 => 100101001010011
  | 9722 => 10000110011110
  | 9723 => 1011001011111
  | 9724 => 10011101100
  | 9725 => 101101100
  | 9726 => 110011011011010
  | 9727 => 11001010001001
  | 9728 => 11001000000000
  | 9729 => 100111011111
  | 9730 => 10100100010
  | 9731 => 100000010111001
  | 9732 => 1001110110110100
  | 9733 => 1000010110011011
  | 9734 => 1000011111100010
  | 9735 => 1001011110
  | 9736 => 101011000
  | 9737 => 11011100111011
  | 9738 => 110011111110
  | 9739 => 101001101011001
  | 9740 => 110011011100
  | 9741 => 100110010000101
  | 9742 => 1011001011001110
  | 9743 => 11110011101
  | 9744 => 110101110000
  | 9745 => 11001111010
  | 9746 => 1101100010010
  | 9747 => 110111011011
  | 9748 => 10100001011100
  | 9749 => 101110001010011
  | 9750 => 10101000
  | 9751 => 1000100111101
  | 9752 => 1100000001000
  | 9753 => 110100111010011
  | 9754 => 11010111000010
  | 9755 => 11010011010010
  | 9756 => 1000010101111011110111111100
  | 9757 => 1001001101111
  | 9758 => 11110001101010
  | 9759 => 110001111100101
  | 9760 => 10010100000
  | 9761 => 111101111010111
  | 9762 => 10100001001110
  | 9763 => 1111000111
  | 9764 => 1000011100000100
  | 9765 => 1010101111110
  | 9766 => 1010010001010010
  | 9767 => 11110110011001
  | 9768 => 111111000
  | 9769 => 10000000011101
  | 9770 => 10111100010
  | 9771 => 10011011111111011011
  | 9772 => 110010000100
  | 9773 => 10001110000001
  | 9774 => 10111010110110
  | 9775 => 11011100010100
  | 9776 => 11001000010000
  | 9777 => 10101100111101111
  | 9778 => 11000001101010
  | 9779 => 10001000110101
  | 9780 => 10000001100
  | 9781 => 110101010001
  | 9782 => 1100001111010
  | 9783 => 101101001001111
  | 9784 => 100111111000
  | 9785 => 100101000110
  | 9786 => 100101010000110
  | 9787 => 10111001111111
  | 9788 => 100000101110100
  | 9789 => 10001110000011
  | 9790 => 11001111110
  | 9791 => 1011101110011
  | 9792 => 10111110111000000
  | 9793 => 1010111001011
  | 9794 => 10011110111010
  | 9795 => 100100011100010
  | 9796 => 11111000101100
  | 9797 => 11100001
  | 9798 => 1001110111110
  | 9799 => 10111100100001
  | 9800 => 1100001000
  | 9801 => 11111111111111111001
  | 9802 => 10101010010
  | 9803 => 110001100101
  | 9804 => 100011011111100
  | 9805 => 1000110
  | 9806 => 101010001101010
  | 9807 => 101001110011011
  | 9808 => 1100010110000
  | 9809 => 111100010000011
  | 9810 => 11111110110
  | 9811 => 10110101001001
  | 9812 => 100111100100
  | 9813 => 1110111100101
  | 9814 => 100001101100110
  | 9815 => 11111110010
  | 9816 => 11100010101000
  | 9817 => 1010111011101101
  | 9818 => 101001000000110
  | 9819 => 11010011011011
  | 9820 => 10010101010100
  | 9821 => 100000100000101
  | 9822 => 111101111010
  | 9823 => 10011000010011
  | 9824 => 1000110001100000
  | 9825 => 10100100
  | 9826 => 110001011101110
  | 9827 => 110111110110001
  | 9828 => 101100101111100
  | 9829 => 1011001111
  | 9830 => 110001111010
  | 9831 => 1000011001101
  | 9832 => 100001111001000
  | 9833 => 110100101
  | 9834 => 100001110110
  | 9835 => 1011011111110
  | 9836 => 10101001101101100
  | 9837 => 10011110011011
  | 9838 => 111101010110010
  | 9839 => 101110110100111
  | 9840 => 100011001110000
  | 9841 => 100110110110101
  | 9842 => 101101010010
  | 9843 => 1100100011001
  | 9844 => 111110001000100
  | 9845 => 100001100011010
  | 9846 => 10010111011110
  | 9847 => 1001100011101
  | 9848 => 100001111001000
  | 9849 => 10001000001111
  | 9850 => 110100010100
  | 9851 => 1001001100011
  | 9852 => 101101100111100
  | 9853 => 1010100001
  | 9854 => 11000010001110
  | 9855 => 1011110011110
  | 9856 => 10010000000
  | 9857 => 10001010011011
  | 9858 => 11000000010
  | 9859 => 1111010010011
  | 9860 => 11110100100
  | 9861 => 10110000111
  | 9862 => 1010001000110
  | 9863 => 100010100001
  | 9864 => 10110100101111000
  | 9865 => 11110101110
  | 9866 => 110111101010010
  | 9867 => 10010101101
  | 9868 => 101011101111100
  | 9869 => 1100001000001
  | 9870 => 1001010001110
  | 9871 => 1001101011011111
  | 9872 => 11001110000
  | 9873 => 110111110001001
  | 9874 => 11000110100110
  | 9875 => 10010011000
  | 9876 => 110001110100
  | 9877 => 111000000110111
  | 9878 => 100111011110
  | 9879 => 11110111101
  | 9880 => 1000000001000
  | 9881 => 10001001000101
  | 9882 => 1111101001110
  | 9883 => 1011001011011111
  | 9884 => 11000010100100
  | 9885 => 10011111110010
  | 9886 => 1000111110110
  | 9887 => 101100011100001
  | 9888 => 111011000100000
  | 9889 => 1111111111011011
  | 9890 => 111110111111010010
  | 9891 => 100001101001010111
  | 9892 => 11110011110100
  | 9893 => 111111100101001
  | 9894 => 1011000100100010
  | 9895 => 100000111011110
  | 9896 => 10110001000
  | 9897 => 100111001011011
  | 9898 => 1111001010
  | 9899 => 1111001110110011
  | 9900 => 11111111111111111100
  | 9901 => 1000001
  | 9902 => 101001101111110
  | 9903 => 1111000111011
  | 9904 => 110100100110000
  | 9905 => 100000100100110
  | 9906 => 100010001101010
  | 9907 => 1110010001
  | 9908 => 11001100100
  | 9909 => 10000010101111011
  | 9910 => 1100010
  | 9911 => 1001011
  | 9912 => 111110000001000
  | 9913 => 11001011000001
  | 9914 => 11011000111110
  | 9915 => 1110110111010
  | 9916 => 111111011100
  | 9917 => 10101100011111
  | 9918 => 1111100101110
  | 9919 => 101001001101
  | 9920 => 111011000000
  | 9921 => 1011111111101001
  | 9922 => 100110110111110
  | 9923 => 100000111001101
  | 9924 => 100011100010100
  | 9925 => 1101000100
  | 9926 => 100011001011110
  | 9927 => 10011110111001
  | 9928 => 10011111011000
  | 9929 => 10010110001
  | 9930 => 10110001110
  | 9931 => 10111010011101
  | 9932 => 1001000001101100
  | 9933 => 10000110000111
  | 9934 => 100100100010
  | 9935 => 1010001101110
  | 9936 => 1010011111110000
  | 9937 => 110010101110001
  | 9938 => 110000011101110
  | 9939 => 111001111111101
  | 9940 => 1100010100
  | 9941 => 100010101100011
  | 9942 => 1101010000000110
  | 9943 => 10010101101111
  | 9944 => 100110110001000
  | 9945 => 10011011111010
  | 9946 => 11010010001010
  | 9947 => 1000110010000101
  | 9948 => 1100000100
  | 9949 => 110100101101
  | 9950 => 11100001100
  | 9951 => 1001111011011
  | 9952 => 10101000100000
  | 9953 => 1010100111
  | 9954 => 11101101100110
  | 9955 => 111100010010
  | 9956 => 1001110001100100
  | 9957 => 10010001111
  | 9958 => 1001010011111110
  | 9959 => 10100101101101111
  | 9960 => 1111100001000
  | 9961 => 1000100110001111
  | 9962 => 100000100110
  | 9963 => 1101011100111
  | 9964 => 1011000000100
  | 9965 => 11101010
  | 9966 => 1010010100110
  | 9967 => 11010010001011
  | 9968 => 11010011110000
  | 9969 => 11011011011001
  | 9970 => 1111100000010
  | 9971 => 1100011000101
  | 9972 => 101110111010100
  | 9973 => 11000000100000101
  | 9974 => 101110101101110
  | 9975 => 111101111100
  | 9976 => 1101101000
  | 9977 => 110111000000001
  | 9978 => 1011111101010
  | 9979 => 1101011101011
  | 9980 => 1110000001100
  | 9981 => 1111100101101
  | 9982 => 11011000010010
  | 9983 => 111011001100011
  | 9984 => 1010100000000
  | 9985 => 10000010111010
  | 9986 => 101101110010
  | 9987 => 100000000010001
  | 9988 => 10001100011100
  | 9989 => 101110110110010001
  | 9990 => 1111111111111111111111111110
  | 9991 => 11100001
  | 9992 => 111100110001000
  | 9993 => 11011101100011
  | 9994 => 111000010010
  | 9995 => 11110000001110
  | 9996 => 1111111000001100
  | 9997 => 1111111000000001
  | 9998 => 1111000000001110
  | 9999 => 111111111111111111111111111111111111
  | _ => 1

def witness_fast (n : Nat) : Nat :=
  if n < 1000 then witness_fast_0 n
  else if n < 2000 then witness_fast_1 n
  else if n < 3000 then witness_fast_2 n
  else if n < 4000 then witness_fast_3 n
  else if n < 5000 then witness_fast_4 n
  else if n < 6000 then witness_fast_5 n
  else if n < 7000 then witness_fast_6 n
  else if n < 8000 then witness_fast_7 n
  else if n < 9000 then witness_fast_8 n
  else witness_fast_9 n

def verify_witness_fast_k4 (n : Nat) : Bool :=
  let w := witness_fast n
  (0 < w) && (w % n == 0) && check_digits_01_fuel 30 w && (w < (10^29 - 1) / 9)

theorem verify_witness_fast_k4_ok (n : Nat) (h : verify_witness_fast_k4 n = true) : A004290 n < (10^29 - 1) / 9 := by
  unfold verify_witness_fast_k4 at h
  simp at h
  have h_pos : 0 < witness_fast n := h.1.1.1
  have h_div : n ∣ witness_fast n := Nat.dvd_of_mod_eq_zero h.1.1.2
  have h_fuel : check_digits_01_fuel 30 (witness_fast n) = true := h.1.2
  have h_bound : witness_fast n < (10^29 - 1) / 9 := h.2
  have h_digits : ∀ d ∈ Nat.digits 10 (witness_fast n), d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 30 (witness_fast n) h_fuel
    have h_lt : witness_fast n < 10^30 := by
      calc witness_fast n < (10^29 - 1) / 9 := h_bound
        _ < 10^29 := by
          apply Nat.div_lt_of_lt_mul
          have : 9 * 10^29 > 10^29 - 1 := by omega
          omega
        _ < 10^30 := by
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
    exact digits_len_le_of_lt (witness_fast n) h_lt
  have h_mem : witness_fast n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  exact lt_of_le_of_lt h_le h_bound

def check_range_k4 (start : Nat) (count : Nat) : Bool :=
  match count with
  | 0 => true
  | c + 1 => verify_witness_fast_k4 (start / Nat.gcd start 10) && check_range_k4 (start + 1) c

theorem check_range_k4_ok : ∀ (count : Nat) (start : Nat), check_range_k4 start count = true →
    ∀ (n : Nat), start ≤ n → n < start + count → verify_witness_fast_k4 (n / Nat.gcd n 10) = true := by
  intro count
  induction count with
  | zero =>
    intro start h_true n h_ge h_lt
    omega
  | succ c ih =>
    intro start h_true n h_ge h_lt
    unfold check_range_k4 at h_true
    simp only [Bool.and_eq_true] at h_true
    have h_fast := h_true.1
    have h_rest := h_true.2
    by_cases hn : n = start
    · subst hn; exact h_fast
    · have h_ge' : start + 1 ≤ n := by omega
      have h_lt' : n < start + 1 + c := by omega
      exact ih (start + 1) h_rest n h_ge' h_lt'

theorem test_range_k4 : check_range_k4 17 9982 = true := by decide

theorem test_large_k4 (n : ℕ) (hn : n < 10000) (hn17 : n ≥ 17) : A004290 (n / Nat.gcd n 10) < (10^29 - 1) / 9 := by
  have h_fast : verify_witness_fast_k4 (n / Nat.gcd n 10) = true := by
    apply check_range_k4_ok 9982 17 test_range_k4 n hn17 hn
  exact verify_witness_fast_k4_ok (n / Nat.gcd n 10) h_fast


def verify_witness_fast_k5 (n : Nat) : Bool :=
  let w := witness_fast n
  (0 < w) && (w % n == 0) && check_digits_01_fuel 30 w && (w < (10^30 - 1) / 9)

theorem verify_witness_fast_k5_ok (n : Nat) (h : verify_witness_fast_k5 n = true) : A004290 n < (10^30 - 1) / 9 := by
  unfold verify_witness_fast_k5 at h
  simp at h
  have h_pos : 0 < witness_fast n := h.1.1.1
  have h_div : n ∣ witness_fast n := Nat.dvd_of_mod_eq_zero h.1.1.2
  have h_fuel : check_digits_01_fuel 30 (witness_fast n) = true := h.1.2
  have h_bound : witness_fast n < (10^30 - 1) / 9 := h.2
  have h_digits : ∀ d ∈ Nat.digits 10 (witness_fast n), d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 30 (witness_fast n) h_fuel
    have h_lt : witness_fast n < 10^30 := by
      calc witness_fast n < (10^30 - 1) / 9 := h_bound
        _ < 10^30 := by
          apply Nat.div_lt_of_lt_mul
          have : 9 * 10^30 > 10^30 - 1 := by omega
          omega
    exact digits_len_le_of_lt (witness_fast n) h_lt
  have h_mem : witness_fast n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  exact lt_of_le_of_lt h_le h_bound

def check_range_k5 (start : Nat) (count : Nat) : Bool :=
  match count with
  | 0 => true
  | c + 1 => verify_witness_fast_k5 (start / Nat.gcd start 100) && check_range_k5 (start + 1) c

theorem check_range_k5_ok : ∀ (count : Nat) (start : Nat), check_range_k5 start count = true →
    ∀ (n : Nat), start ≤ n → n < start + count → verify_witness_fast_k5 (n / Nat.gcd n 100) = true := by
  intro count
  induction count with
  | zero =>
    intro start h_true n h_ge h_lt
    omega
  | succ c ih =>
    intro start h_true n h_ge h_lt
    unfold check_range_k5 at h_true
    simp only [Bool.and_eq_true] at h_true
    have h_fast := h_true.1
    have h_rest := h_true.2
    by_cases hn : n = start
    · subst hn; exact h_fast
    · have h_ge' : start + 1 ≤ n := by omega
      have h_lt' : n < start + 1 + c := by omega
      exact ih (start + 1) h_rest n h_ge' h_lt'

theorem test_range_k5 : check_range_k5 17 9982 = true := by decide

def check_range_k5_5digit_fast (start count : Nat) : Bool :=
  match count with
  | 0 => true
  | c + 1 =>
    if start == 10989 || start == 29997 || start == 32967 || start == 40959 || start == 41841 || start == 69993 || start == 72927 || start == 76923 || start == 81918 || start == 83682 || start == 88911 || start == 89991 || start == 98901 then
      check_range_k5_5digit_fast (start + 1) c
    else if Nat.gcd start 100 == 1 then
      verify_witness_fast_k5 start && check_range_k5_5digit_fast (start + 1) c
    else
      check_range_k5_5digit_fast (start + 1) c

theorem check_range_k5_5digit_fast_ok : ∀ (count : Nat) (start : Nat), check_range_k5_5digit_fast start count = true →
    ∀ (n : Nat), start ≤ n → n < start + count →
    (n = 10989 ∨ n = 29997 ∨ n = 32967 ∨ n = 40959 ∨ n = 41841 ∨ n = 69993 ∨ n = 72927 ∨ n = 76923 ∨ n = 81918 ∨ n = 83682 ∨ n = 88911 ∨ n = 89991 ∨ n = 98901 → False) →
    Nat.gcd n 100 = 1 → verify_witness_fast_k5 n = true := by
  intro count
  induction count with
  | zero =>
    intro start h_true n h_ge h_lt _ _
    omega
  | succ c ih =>
    intro start h_true n h_ge h_lt h_not_exc h_gcd
    unfold check_range_k5_5digit_fast at h_true
    split at h_true
    · -- start is exceptional
      have h_n_neq : n ≠ start := by
        intro hc
        subst hc
        apply h_not_exc
        rename_i h_cond
        simp only [Bool.or_eq_true, beq_iff_eq] at h_cond
        tauto
      have h_ge' : start + 1 ≤ n := by omega
      have h_lt' : n < start + 1 + c := by omega
      exact ih (start + 1) h_true n h_ge' h_lt' h_not_exc h_gcd
    · -- start is not exceptional
      rename_i h_cond
      split at h_true
      · -- Nat.gcd start 100 == 1
        have h_verify : verify_witness_fast_k5 start = true := by
          have := h_true
          simp only [Bool.and_eq_true] at this
          exact this.1
        have h_rest : check_range_k5_5digit_fast (start + 1) c = true := by
          have := h_true
          simp only [Bool.and_eq_true] at this
          exact this.2
        by_cases h_n_eq : n = start
        · subst h_n_eq
          exact h_verify
        · have h_ge' : start + 1 ≤ n := by omega
          have h_lt' : n < start + 1 + c := by omega
          exact ih (start + 1) h_rest n h_ge' h_lt' h_not_exc h_gcd
      · -- Nat.gcd start 100 != 1
        by_cases h_n_eq : n = start
        · subst h_n_eq
          rename_i h_gcd'
          rw [h_gcd] at h_gcd'
          simp at h_gcd'
        · have h_ge' : start + 1 ≤ n := by omega
          have h_lt' : n < start + 1 + c := by omega
          exact ih (start + 1) h_true n h_ge' h_lt' h_not_exc h_gcd

theorem test_range_5digit_1 : check_range_k5_5digit_fast 10000 10000 = true := by decide
theorem test_range_5digit_2 : check_range_k5_5digit_fast 20000 10000 = true := by decide
theorem test_range_5digit_3 : check_range_k5_5digit_fast 30000 10000 = true := by decide
theorem test_range_5digit_4 : check_range_k5_5digit_fast 40000 10000 = true := by decide
theorem test_range_5digit_5 : check_range_k5_5digit_fast 50000 10000 = true := by decide
theorem test_range_5digit_6 : check_range_k5_5digit_fast 60000 10000 = true := by decide
theorem test_range_5digit_7 : check_range_k5_5digit_fast 70000 10000 = true := by decide
theorem test_range_5digit_8 : check_range_k5_5digit_fast 80000 10000 = true := by decide
theorem test_range_5digit_9 : check_range_k5_5digit_fast 90000 10000 = true := by decide

theorem gcd_u3_100_eq_one_k5 (n : ℕ) (hn : n < 100000) (hu3_ge : (n / Nat.gcd n 100) / Nat.gcd (n / Nat.gcd n 100) 100 ≥ 10000) : Nat.gcd ((n / Nat.gcd n 100) / Nat.gcd (n / Nat.gcd n 100) 100) 100 = 1 := by
  revert n hn hu3_ge
  decide



theorem test_large_k5 (n : ℕ) (hn : n < 10000) (hn17 : n ≥ 17) : A004290 (n / Nat.gcd n 100) < (10^30 - 1) / 9 := by
  have h_fast : verify_witness_fast_k5 (n / Nat.gcd n 100) = true := by
    apply check_range_k5_ok 9982 17 test_range_k5 n hn17 hn
  exact verify_witness_fast_k5_ok (n / Nat.gcd n 100) h_fast

def verify_witness_fast (n : Nat) : Bool :=
  let w := witness_fast n
  (0 < w) && (w % n == 0) && check_digits_01_fuel 30 w && (w < (10^27 - 1) / 9)

theorem verify_witness_ok (n : Nat) (h : verify_witness_fast n = true) : A004290 n < (10^27 - 1) / 9 := by
  unfold verify_witness_fast at h
  simp at h
  have h_pos : 0 < witness_fast n := h.1.1.1
  have h_div : n ∣ witness_fast n := Nat.dvd_of_mod_eq_zero h.1.1.2
  have h_fuel : check_digits_01_fuel 30 (witness_fast n) = true := h.1.2
  have h_bound : witness_fast n < (10^27 - 1) / 9 := h.2
  have h_digits : ∀ d ∈ Nat.digits 10 (witness_fast n), d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 30 (witness_fast n) h_fuel
    have h_lt : witness_fast n < 10^30 := by
      calc witness_fast n < (10^27 - 1) / 9 := h_bound
        _ < 10^27 := by
          apply Nat.div_lt_of_lt_mul
          have : 9 * 10^27 > 10^27 - 1 := by omega
          omega
        _ < 10^30 := by
          exact (Nat.pow_lt_pow_iff_right (by norm_num)).mpr (by omega)
    exact digits_len_le_of_lt (witness_fast n) h_lt
  have h_mem : witness_fast n ∈ { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  exact lt_of_le_of_lt h_le h_bound

def check_range (start : Nat) (count : Nat) : Bool :=
  match count with
  | 0 => true
  | c + 1 => verify_witness_fast start && check_range (start + 1) c

theorem check_range_ok : ∀ (count : Nat) (start : Nat), check_range start count = true →
  ∀ (n : Nat), start ≤ n → n < start + count → verify_witness_fast n = true
  | 0, start, h, n, h_ge, h_lt => by
    omega
  | c + 1, start, h, n, h_ge, h_lt => by
    unfold check_range at h
    rw [Bool.and_eq_true] at h
    have h_start := h.1
    have h_rest := h.2
    by_cases hn : n = start
    · subst hn; exact h_start
    · have h_ge' : start + 1 ≤ n := by omega
      have h_lt' : n < (start + 1) + c := by omega
      exact check_range_ok c (start + 1) h_rest n h_ge' h_lt'

theorem test_range_17_998 : check_range 17 982 = true := by decide

theorem test_large (n : ℕ) (hn : n < 999) (hn17 : n ≥ 17) : A004290 n < (10^27 - 1) / 9 := by
  have h_fast : verify_witness_fast n = true := by
    apply check_range_ok 982 17 test_range_17_998 n hn17 hn
  exact verify_witness_ok n h_fast


lemma digits_len_le_of_lt_46 (w : Nat) (h : w < 10^46) : (Nat.digits 10 w).length ≤ 46 := by
  by_cases hw : w = 0
  · subst hw
    simp
  · have h_base : 10 > 1 := by norm_num
    have h_pos : w > 0 := Nat.pos_of_ne_zero hw
    rw [Nat.digits_len 10 w (by omega) (by omega)]
    simp
    have h_log : Nat.log 10 w < 46 := by
      exact Nat.log_lt_of_lt_pow (by omega) h
    omega

lemma A004290_76923_lt : A004290 76923 < (10^45 - 1)/9 := by
  let W : ℕ := 1000001010001010101110101110111110111111111
  have h_pos : 0 < W := by decide
  have h_div : 76923 ∣ W := by
    use 13000026130039261353692668124112555557
  have h_fuel : check_digits_01_fuel 46 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 46 W h_fuel
    have h_lt : W < 10^46 := by decide
    exact digits_len_le_of_lt_46 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 76923 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^45 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma digits_len_le_of_lt_37 (w : Nat) (h : w < 10^37) : (Nat.digits 10 w).length ≤ 37 := by
  by_cases hw : w = 0
  · subst hw
    simp
  · have h_base : 10 > 1 := by norm_num
    have h_pos : w > 0 := Nat.pos_of_ne_zero hw
    rw [Nat.digits_len 10 w (by omega) (by omega)]
    simp
    have h_log : Nat.log 10 w < 37 := by
      exact Nat.log_lt_of_lt_pow (by omega) h
    omega

lemma A004290_10989_lt : A004290 10989 < (10^37 - 1)/9 := by
  let W : ℕ := 1010101010101010101110111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 10989 ∣ W := by
    use 91919283838475757676777787888899
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 10989 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_29997_lt : A004290 29997 < (10^37 - 1)/9 := by
  let W : ℕ := 1111111101111111111111111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 29997 ∣ W := by
    use 37040740777781481851888892592963
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 29997 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_32967_lt : A004290 32967 < (10^37 - 1)/9 := by
  let W : ℕ := 1010101010101010101111111111111110111
  have h_pos : 0 < W := by decide
  have h_div : 32967 ∣ W := by
    use 30639761279491919225622929326633
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 32967 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_69993_lt : A004290 69993 < (10^37 - 1)/9 := by
  let W : ℕ := 111111111111111111111111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 69993 ∣ W := by
    use 158746013144171554301144401583015
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 69993 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_89991_lt : A004290 89991 < (10^37 - 1)/9 := by
  let W : ℕ := 1111111111111111111111111111111101111
  have h_pos : 0 < W := by decide
  have h_div : 89991 ∣ W := by
    use 12346913703716050617407419754321
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 89991 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound


lemma A004290_40959_lt : A004290 40959 < (10^37 - 1)/9 := by
  let W : ℕ := 1010111100111111111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 40959 ∣ W := by
    use 24661517617888891601628729
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 40959 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_81918_lt : A004290 81918 < (10^37 - 1)/9 := by
  let W : ℕ := 10101111001111111111111111111110
  have h_pos : 0 < W := by decide
  have h_div : 81918 ∣ W := by
    use 123307588089444458008143645
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 81918 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_41841_lt : A004290 41841 < (10^37 - 1)/9 := by
  let W : ℕ := 110000011010001111001111101111
  have h_pos : 0 < W := by decide
  have h_div : 41841 ∣ W := by
    use 2629000526039079156834471
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 41841 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_83682_lt : A004290 83682 < (10^37 - 1)/9 := by
  let W : ℕ := 1100000110100011110011111011110
  have h_pos : 0 < W := by decide
  have h_div : 83682 ∣ W := by
    use 13145002630195395784172355
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 83682 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_72927_lt : A004290 72927 < (10^37 - 1)/9 := by
  let W : ℕ := 111101011111111111111110111111
  have h_pos : 0 < W := by decide
  have h_div : 72927 ∣ W := by
    use 1523455114170487077640793
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 72927 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_88911_lt : A004290 88911 < (10^37 - 1)/9 := by
  let W : ℕ := 101111010111111111111111111111
  have h_pos : 0 < W := by decide
  have h_div : 88911 ∣ W := by
    use 1137215981274657928840201
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 88911 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

lemma A004290_98901_lt : A004290 98901 < (10^37 - 1)/9 := by
  let W : ℕ := 1010101010101110111111111111111010101
  have h_pos : 0 < W := by decide
  have h_div : 98901 ∣ W := by
    use 10213253759831650955107745231201
  have h_fuel : check_digits_01_fuel 37 W = true := by decide
  have h_digits : ∀ d ∈ Nat.digits 10 W, d = 0 ∨ d = 1 := by
    apply check_digits_01_fuel_ok 37 W h_fuel
    have h_lt : W < 10^37 := by decide
    exact digits_len_le_of_lt_37 W h_lt
  have h_mem : W ∈ { m : ℕ | 0 < m ∧ 98901 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
    ⟨h_pos, h_div, h_digits⟩
  have h_le := Nat.sInf_le h_mem
  have h_bound : W < (10^37 - 1) / 9 := by decide
  exact lt_of_le_of_lt h_le h_bound

theorem dvd_1000_of_dvd_10000_of_lt_10 (d : ℕ) (hd : d ∣ 10000) (h_lt : d < 10) : d ∣ 1000 := by
  interval_cases d
  · contradiction
  · decide
  · decide
  · revert hd; decide
  · decide
  · decide
  · revert hd; decide
  · revert hd; decide
  · decide
  · revert hd; decide

theorem gcd_u_10_eq_one (n : ℕ) (hn : n > 0) :
    let d := Nat.gcd n 10000
    let u := n / d
    d < 10 → Nat.gcd u 10 = 1 := by
  intro d u h_lt
  have hd_eq : d = Nat.gcd n 10000 := rfl
  have hu_eq : u = n / d := rfl
  have hd_dvd_n : d ∣ n := Nat.gcd_dvd_left n 10000
  have hd_dvd_10k : d ∣ 10000 := Nat.gcd_dvd_right n 10000
  have hd_pos : d > 0 := by
    apply Nat.gcd_pos_of_pos_right n (by norm_num)
  have hn_eq_ud : n = u * d := (Nat.div_mul_cancel hd_dvd_n).symm
  have h_gcd_dvd_u : Nat.gcd u 10 ∣ u := Nat.gcd_dvd_left u 10
  have h_gcd_dvd_10 : Nat.gcd u 10 ∣ 10 := Nat.gcd_dvd_right u 10
  have h_gcd_pos : Nat.gcd u 10 > 0 := by
    apply Nat.gcd_pos_of_pos_right u (by norm_num)
  by_contra h_not_one
  have h_gt_one : Nat.gcd u 10 > 1 := by omega
  have h_div_2_or_5 : 2 ∣ Nat.gcd u 10 ∨ 5 ∣ Nat.gcd u 10 := by
    have h_dvd := h_gcd_dvd_10
    have h_gcd_le : Nat.gcd u 10 ≤ 10 := Nat.le_of_dvd (by norm_num) h_gcd_dvd_10
    interval_cases Nat.gcd u 10
    · left; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · right; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · revert h_dvd; decide
    · left; decide
  rcases h_div_2_or_5 with h2 | h5
  · have h2_u : 2 ∣ u := dvd_trans h2 h_gcd_dvd_u
    rcases h2_u with ⟨q, hq⟩
    have h2d_n : 2 * d ∣ n := by
      rw [hn_eq_ud, hq]
      use q
      ring
    have h2d_10k : 2 * d ∣ 10000 := by
      interval_cases d
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · revert hd_dvd_10k; decide
      · decide
      · revert hd_dvd_10k; decide
    have h2d_gcd : 2 * d ∣ d := by
      have h2d_gcd_prep := Nat.dvd_gcd h2d_n h2d_10k
      rw [← hd_eq] at h2d_gcd_prep
      exact h2d_gcd_prep
    have h_le_d : 2 * d ≤ d := Nat.le_of_dvd hd_pos h2d_gcd
    omega
  · have h5_u : 5 ∣ u := dvd_trans h5 h_gcd_dvd_u
    rcases h5_u with ⟨q, hq⟩
    have h5d_n : 5 * d ∣ n := by
      rw [hn_eq_ud, hq]
      use q
      ring
    have h5d_10k : 5 * d ∣ 10000 := by
      interval_cases d
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · decide
      · decide
      · revert hd_dvd_10k; decide
      · revert hd_dvd_10k; decide
      · decide
      · revert hd_dvd_10k; decide
    have h5d_gcd : 5 * d ∣ d := by
      have h5d_gcd_prep := Nat.dvd_gcd h5d_n h5d_10k
      rw [← hd_eq] at h5d_gcd_prep
      exact h5d_gcd_prep
    have h_le_d : 5 * d ≤ d := Nat.le_of_dvd hd_pos h5d_gcd
    omega

theorem coprime_test (n : ℕ) (hn : n > 0) :
    let d := Nat.gcd n 10000
    let u := n / d
    d < 10 → Nat.gcd u 100 = 1 := by
  intro d u h_lt
  have h_gcd_10 := gcd_u_10_eq_one n hn h_lt
  have h_coprime : Nat.Coprime u 10 := h_gcd_10
  have h_coprime2 : Nat.Coprime u (10^2) := Nat.Coprime.pow_right 2 h_coprime
  exact h_coprime2




theorem oeis_a004290_conjecture_radcliffe (k : ℕ) (hk : k > 0) :
  (A004290 (10 ^ k) = 10 ^ k) ∧
  (A004290 (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9) ∧
  (∀ n : ℕ, n < 10 ^ k - 1 → A004290 n < A004290 (10 ^ k - 1)) :=
by
  refine ⟨first_conj k hk, second_conj k hk, ?_⟩
  intro n hn
  rw [second_conj k hk]
  by_cases hk1 : k = 1
  · subst hk1
    have h_9 : 10^1 - 1 = 9 := rfl
    rw [h_9] at hn
    have h_digits1 : Nat.digits 10 1 = [1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 1 0 (by norm_num) (Or.inl (by norm_num))
      have h_eq : 1 + 10 * 0 = 1 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, Nat.digits_zero]
    have h_digits10 : Nat.digits 10 10 = [0, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 0 1 (by norm_num) (Or.inr (by norm_num))
      have h_eq : 0 + 10 * 1 = 10 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits1]
    have h_digits11 : Nat.digits 10 11 = [1, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 1 1 (by norm_num) (Or.inl (by norm_num))
      have h_eq : 1 + 10 * 1 = 11 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits1]
    have h_digits100 : Nat.digits 10 100 = [0, 0, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 0 10 (by norm_num) (Or.inr (by norm_num))
      have h_eq : 0 + 10 * 10 = 100 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits10]
    have h_digits110 : Nat.digits 10 110 = [0, 1, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 0 11 (by norm_num) (Or.inr (by norm_num))
      have h_eq : 0 + 10 * 11 = 110 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits11]
    have h_digits111 : Nat.digits 10 111 = [1, 1, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 1 11 (by norm_num) (Or.inl (by norm_num))
      have h_eq : 1 + 10 * 11 = 111 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits11]
    have h_digits1110 : Nat.digits 10 1110 = [0, 1, 1, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 0 111 (by norm_num) (Or.inr (by norm_num))
      have h_eq : 0 + 10 * 111 = 1110 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits111]
    have h_digits1001 : Nat.digits 10 1001 = [1, 0, 0, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 1 100 (by norm_num) (Or.inl (by norm_num))
      have h_eq : 1 + 10 * 100 = 1001 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits100]
    have h_digits1000 : Nat.digits 10 1000 = [0, 0, 0, 1] := by
      have h_add := Nat.digits_add 10 (by norm_num : 1 < 10) 0 100 (by norm_num) (Or.inr (by norm_num))
      have h_eq : 0 + 10 * 100 = 1000 := by norm_num
      rw [h_eq] at h_add
      rw [h_add, h_digits100]

    interval_cases n
    · -- n = 0
      have h_zero : A004290 0 = 0 := by
        unfold A004290
        have h_empty : { m : ℕ | 0 < m ∧ 0 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          have h0 : 0 ∣ x := h.2.1
          have h_eq : x = 0 := by
            rcases h0 with ⟨q, hq⟩
            rw [hq, zero_mul]
          have hx : 0 < x := h.1
          omega
        rw [h_empty, Nat.sInf_empty]
      rw [h_zero]
      have h_pos : 0 < (10^(9 * 1) - 1)/9 := by norm_num
      exact h_pos
    · -- n = 1
      have h_S : 1 ∈ { m : ℕ | 0 < m ∧ 1 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits1] at hd
        simp at hd
        right; exact hd
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 1 ≤ 1 := h_inf
      have h_lt : 1 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 2
      have h_S : 10 ∈ { m : ℕ | 0 < m ∧ 2 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits10] at hd
        simp at hd
        rcases hd with rfl | rfl <;> simp
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 2 ≤ 10 := h_inf
      have h_lt : 10 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 3
      have h_S : 111 ∈ { m : ℕ | 0 < m ∧ 3 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits111] at hd
        simp at hd
        right; exact hd
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 3 ≤ 111 := h_inf
      have h_lt : 111 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 4
      have h_S : 100 ∈ { m : ℕ | 0 < m ∧ 4 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits100] at hd
        simp at hd
        rcases hd with rfl | rfl | rfl <;> simp
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 4 ≤ 100 := h_inf
      have h_lt : 100 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 5
      have h_S : 10 ∈ { m : ℕ | 0 < m ∧ 5 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits10] at hd
        simp at hd
        rcases hd with rfl | rfl <;> simp
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 5 ≤ 10 := h_inf
      have h_lt : 10 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 6
      have h_S : 1110 ∈ { m : ℕ | 0 < m ∧ 6 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits1110] at hd
        simp at hd
        rcases hd with rfl | rfl | rfl | rfl <;> simp
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 6 ≤ 1110 := h_inf
      have h_lt : 1110 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 7
      have h_S : 1001 ∈ { m : ℕ | 0 < m ∧ 7 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits1001] at hd
        simp at hd
        rcases hd with rfl | rfl | rfl <;> simp
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 7 ≤ 1001 := h_inf
      have h_lt : 1001 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
    · -- n = 8
      have h_S : 1000 ∈ { m : ℕ | 0 < m ∧ 8 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        intro d hd
        rw [h_digits1000] at hd
        simp at hd
        exact hd
      have h_inf := Nat.sInf_le h_S
      have h_le : A004290 8 ≤ 1000 := h_inf
      have h_lt : 1000 < (10^(9 * 1) - 1)/9 := by norm_num
      exact lt_of_le_of_lt h_le h_lt
  · by_cases hn0 : n = 0
    · subst hn0
      have h_zero : A004290 0 = 0 := by
        unfold A004290
        have h_empty : { m : ℕ | 0 < m ∧ 0 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h
          have h0 : 0 ∣ x := h.2.1
          have h_eq : x = 0 := by
            rcases h0 with ⟨q, hq⟩
            rw [hq, zero_mul]
          have hx : 0 < x := h.1
          omega
        rw [h_empty, Nat.sInf_empty]
      rw [h_zero]
      have h_pos : 0 < (10 ^ (9 * k) - 1) / 9 := by
        apply Nat.div_pos
        · have : 10^(9 * k) ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · norm_num
      exact h_pos
    · have hn_pos : n > 0 := by omega
      have h_lt : A004290 n < (10^(n + 1) - 1) / 9 := A004290_lt_geom_sum n hn_pos
      by_cases hn_lt : n + 1 < 9 * k
      · have h_le_div : (10^(n + 1) - 1) / 9 ≤ (10^(9 * k - 1) - 1) / 9 := by
          apply Nat.div_le_div_right
          have h_pow : 10^(n + 1) ≤ 10^(9 * k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have h_lt_geom : (10^(9 * k - 1) - 1) / 9 < (10^(9 * k) - 1) / 9 := by
          have h_eqA : 9 * ((10^(9 * k - 1) - 1) / 9) = 10^(9 * k - 1) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k - 1))
          have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
          have h_lt_pow : 10^(9 * k - 1) < 10^(9 * k) := by
            have : 9 * k = (9 * k - 1) + 1 := by omega
            nth_rw 2 [this]
            rw [pow_succ]
            have h_pow_pos : 10^(9 * k - 1) > 0 := Nat.pow_pos (by norm_num)
            omega
          omega
        calc A004290 n < (10^(n + 1) - 1) / 9 := h_lt
          _ ≤ (10^(9 * k - 1) - 1) / 9 := h_le_div
          _ < (10^(9 * k) - 1) / 9 := h_lt_geom
      · have hk2 : k ≥ 2 := by omega
        let d := Nat.gcd n (10^k)
        let u := n / d
        have hd : d ∣ 10^k := Nat.gcd_dvd_right n (10^k)
        have hu : d ∣ n := Nat.gcd_dvd_left n (10^k)
        have hu_pos : u > 0 := by
          apply Nat.div_pos
          · exact Nat.le_of_dvd hn_pos hu
          · have h_pow_pos : 10^k > 0 := Nat.pow_pos (by norm_num)
            exact Nat.pos_of_dvd_of_pos hd h_pow_pos
        by_cases hu_lt : u + 1 < 8 * k + 1
        · have h_lt_u : A004290 u < (10^(u + 1) - 1) / 9 := A004290_lt_geom_sum u hu_pos
          have h_le_u : (10^(u + 1) - 1) / 9 ≤ (10^(8 * k) - 1) / 9 := by
            apply Nat.div_le_div_right
            have h_pow : 10^(u + 1) ≤ 10^(8 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          have h_le_M : A004290 n ≤ 10^k * A004290 u := A004290_le_ten_pow_mul n k d hd hu hn_pos
          have h_lt_u_geom : A004290 u < (10^(8 * k) - 1) / 9 := lt_of_lt_of_le h_lt_u h_le_u
          have h_lt_M : 10^k * A004290 u < (10^(9 * k) - 1) / 9 := by
            have h_eqA : 9 * ((10^(8 * k) - 1) / 9) = 10^(8 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k))
            have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
            have h_mul_lt : 9 * (10^k * A004290 u) < 9 * ((10^(9 * k) - 1) / 9) := by
              rw [h_eqB]
              calc 9 * (10^k * A004290 u) = 10^k * (9 * A004290 u) := by ring
                _ < 10^k * (10^(8 * k) - 1) := by
                  apply Nat.mul_lt_mul_of_pos_left
                  · have : 9 * A004290 u < 9 * ((10^(8 * k) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u_geom (by norm_num)
                    rw [h_eqA] at this
                    exact this
                  · exact Nat.pow_pos (by norm_num)
                _ = 10^(9 * k) - 10^k := by
                  rw [Nat.mul_sub_left_distrib, mul_one]
                  have h_pow : 10^k * 10^(8 * k) = 10^(9 * k) := by
                    rw [← pow_add]
                    congr 1
                    omega
                  rw [h_pow]
                _ < 10^(9 * k) - 1 := by
                  have h_pow_k : 10^k > 1 := by
                    have : k ≥ 1 := by omega
                    have : 10^k ≥ 10^1 := Nat.pow_le_pow_right (by norm_num) this
                    omega
                  have h_pow_9k : 10^(9 * k) ≥ 10^k := Nat.pow_le_pow_right (by norm_num) (by omega)
                  omega
            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
          exact lt_of_le_of_lt h_le_M h_lt_M
        · let d1 := Nat.gcd n (10^(k-1))
          let u1 := n / d1
          have hd1 : d1 ∣ 10^(k-1) := Nat.gcd_dvd_right n (10^(k-1))
          have hu1 : d1 ∣ n := Nat.gcd_dvd_left n (10^(k-1))
          have hu1_pos : u1 > 0 := by
            apply Nat.div_pos
            · exact Nat.le_of_dvd hn_pos hu1
            · have h_pow_pos : 10^(k-1) > 0 := Nat.pow_pos (by norm_num)
              exact Nat.pos_of_dvd_of_pos hd1 h_pow_pos
          by_cases hu1_lt : u1 + 1 < 8 * k + 1
          · have h_lt_u1 : A004290 u1 < (10^(u1 + 1) - 1) / 9 := A004290_lt_geom_sum u1 hu1_pos
            have h_le_u1 : (10^(u1 + 1) - 1) / 9 ≤ (10^(8 * k) - 1) / 9 := by
              apply Nat.div_le_div_right
              have h_pow : 10^(u1 + 1) ≤ 10^(8 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
            have h_le_M1 : A004290 n ≤ 10^(k-1) * A004290 u1 := A004290_le_ten_pow_mul n (k-1) d1 hd1 hu1 hn_pos
            have h_lt_u1_geom : A004290 u1 < (10^(8 * k) - 1) / 9 := lt_of_lt_of_le h_lt_u1 h_le_u1
            have h_lt_M1 : 10^(k-1) * A004290 u1 < (10^(9 * k) - 1) / 9 := by
              have h_eqA : 9 * ((10^(8 * k) - 1) / 9) = 10^(8 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k))
              have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
              have h_mul_lt : 9 * (10^(k-1) * A004290 u1) < 9 * ((10^(9 * k) - 1) / 9) := by
                rw [h_eqB]
                calc 9 * (10^(k-1) * A004290 u1) = 10^(k-1) * (9 * A004290 u1) := by ring
                  _ < 10^(k-1) * (10^(8 * k) - 1) := by
                    apply Nat.mul_lt_mul_of_pos_left
                    · have : 9 * A004290 u1 < 9 * ((10^(8 * k) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u1_geom (by norm_num)
                      rw [h_eqA] at this
                      exact this
                    · exact Nat.pow_pos (by norm_num)
                  _ = 10^(9 * k - 1) - 10^(k-1) := by
                    rw [Nat.mul_sub_left_distrib, mul_one]
                    have h_pow : 10^(k-1) * 10^(8 * k) = 10^(9 * k - 1) := by
                      rw [← pow_add]
                      congr 1
                      omega
                    rw [h_pow]
                  _ < 10^(9 * k) - 1 := by
                    have h_pow_lt : 10^(9 * k - 1) < 10^(9 * k) := by
                      have : 9 * k = (9 * k - 1) + 1 := by omega
                      nth_rw 2 [this]
                      rw [pow_succ]
                      have h_pow_pos : 10^(9 * k - 1) > 0 := Nat.pow_pos (by norm_num)
                      omega
                    have h_pow_k : 10^(k-1) ≥ 1 := Nat.one_le_pow (k-1) 10 (by norm_num)
                    have h_pow_le : 10^(k-1) ≤ 10^(9 * k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
                    omega
              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
            exact lt_of_le_of_lt h_le_M1 h_lt_M1
          · -- Since u1 + 1 ≥ 8 * k + 1, we must have d1 < 10^(k-1) / 8k.
            -- This means we can descend further by using d2 = gcd n (10^(k-2)).
            -- Since k ≥ 2, we do cases on k = 2 and k ≥ 3.
            by_cases hk_eq2 : k = 2
            · subst hk_eq2
              have hn_ge : 17 ≤ n := by omega
              interval_cases n
              · -- n = 17
                have h_digits : Nat.digits 10 11101 = [1, 0, 1, 1, 1] := by
                  have h1 : 11101 = 1 + 10 * 1110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1110 (by norm_num)]
                  have h2 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h3 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11101 ∈ { m : ℕ | 0 < m ∧ 17 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 17 ≤ 11101 := h_inf
                have h_lt : A004290 17 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 18
                have h_digits : Nat.digits 10 1111111110 = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 1111111110 = 0 + 10 * 111111111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111111111 (by norm_num)]
                  have h2 : 111111111 = 1 + 10 * 11111111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11111111 (by norm_num)]
                  have h3 : 11111111 = 1 + 10 * 1111111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1111111 (by norm_num)]
                  have h4 : 1111111 = 1 + 10 * 111111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 111111 (by norm_num)]
                  have h5 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h6 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h7 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h8 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h9 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1111111110 ∈ { m : ℕ | 0 < m ∧ 18 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 18 ≤ 1111111110 := h_inf
                have h_lt : A004290 18 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 19
                have h_digits : Nat.digits 10 11001 = [1, 0, 0, 1, 1] := by
                  have h1 : 11001 = 1 + 10 * 1100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1100 (by norm_num)]
                  have h2 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h3 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11001 ∈ { m : ℕ | 0 < m ∧ 19 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 19 ≤ 11001 := h_inf
                have h_lt : A004290 19 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 20
                have h_digits : Nat.digits 10 100 = [0, 0, 1] := by
                  have h1 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h2 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100 ∈ { m : ℕ | 0 < m ∧ 20 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 20 ≤ 100 := h_inf
                have h_lt : A004290 20 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 21
                have h_digits : Nat.digits 10 10101 = [1, 0, 1, 0, 1] := by
                  have h1 : 10101 = 1 + 10 * 1010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1010 (by norm_num)]
                  have h2 : 1010 = 0 + 10 * 101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 101 (by norm_num)]
                  have h3 : 101 = 1 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10101 ∈ { m : ℕ | 0 < m ∧ 21 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 21 ≤ 10101 := h_inf
                have h_lt : A004290 21 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 22
                have h_digits : Nat.digits 10 110 = [0, 1, 1] := by
                  have h1 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h2 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 110 ∈ { m : ℕ | 0 < m ∧ 22 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 22 ≤ 110 := h_inf
                have h_lt : A004290 22 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 23
                have h_digits : Nat.digits 10 110101 = [1, 0, 1, 0, 1, 1] := by
                  have h1 : 110101 = 1 + 10 * 11010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 11010 (by norm_num)]
                  have h2 : 11010 = 0 + 10 * 1101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1101 (by norm_num)]
                  have h3 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h4 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 110101 ∈ { m : ℕ | 0 < m ∧ 23 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 23 ≤ 110101 := h_inf
                have h_lt : A004290 23 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 24
                have h_digits : Nat.digits 10 111000 = [0, 0, 0, 1, 1, 1] := by
                  have h1 : 111000 = 0 + 10 * 11100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11100 (by norm_num)]
                  have h2 : 11100 = 0 + 10 * 1110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1110 (by norm_num)]
                  have h3 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h4 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111000 ∈ { m : ℕ | 0 < m ∧ 24 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 24 ≤ 111000 := h_inf
                have h_lt : A004290 24 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 25
                have h_digits : Nat.digits 10 100 = [0, 0, 1] := by
                  have h1 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h2 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100 ∈ { m : ℕ | 0 < m ∧ 25 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 25 ≤ 100 := h_inf
                have h_lt : A004290 25 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 26
                have h_digits : Nat.digits 10 10010 = [0, 1, 0, 0, 1] := by
                  have h1 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h2 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10010 ∈ { m : ℕ | 0 < m ∧ 26 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 26 ≤ 10010 := h_inf
                have h_lt : A004290 26 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 27
                have h_digits : Nat.digits 10 1101111111 = [1, 1, 1, 1, 1, 1, 1, 0, 1, 1] := by
                  have h1 : 1101111111 = 1 + 10 * 110111111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 110111111 (by norm_num)]
                  have h2 : 110111111 = 1 + 10 * 11011111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11011111 (by norm_num)]
                  have h3 : 11011111 = 1 + 10 * 1101111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1101111 (by norm_num)]
                  have h4 : 1101111 = 1 + 10 * 110111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 110111 (by norm_num)]
                  have h5 : 110111 = 1 + 10 * 11011 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11011 (by norm_num)]
                  have h6 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h7 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h8 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h9 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1101111111 ∈ { m : ℕ | 0 < m ∧ 27 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 27 ≤ 1101111111 := h_inf
                have h_lt : A004290 27 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 28
                have h_digits : Nat.digits 10 100100 = [0, 0, 1, 0, 0, 1] := by
                  have h1 : 100100 = 0 + 10 * 10010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10010 (by norm_num)]
                  have h2 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h3 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100100 ∈ { m : ℕ | 0 < m ∧ 28 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 28 ≤ 100100 := h_inf
                have h_lt : A004290 28 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 29
                have h_digits : Nat.digits 10 1101101 = [1, 0, 1, 1, 0, 1, 1] := by
                  have h1 : 1101101 = 1 + 10 * 110110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 110110 (by norm_num)]
                  have h2 : 110110 = 0 + 10 * 11011 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11011 (by norm_num)]
                  have h3 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h4 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h5 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1101101 ∈ { m : ℕ | 0 < m ∧ 29 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 29 ≤ 1101101 := h_inf
                have h_lt : A004290 29 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 30
                have h_digits : Nat.digits 10 1110 = [0, 1, 1, 1] := by
                  have h1 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h2 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h3 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1110 ∈ { m : ℕ | 0 < m ∧ 30 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 30 ≤ 1110 := h_inf
                have h_lt : A004290 30 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 31
                have h_digits : Nat.digits 10 111011 = [1, 1, 0, 1, 1, 1] := by
                  have h1 : 111011 = 1 + 10 * 11101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 11101 (by norm_num)]
                  have h2 : 11101 = 1 + 10 * 1110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1110 (by norm_num)]
                  have h3 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h4 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111011 ∈ { m : ℕ | 0 < m ∧ 31 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 31 ≤ 111011 := h_inf
                have h_lt : A004290 31 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 32
                have h_digits : Nat.digits 10 100000 = [0, 0, 0, 0, 0, 1] := by
                  have h1 : 100000 = 0 + 10 * 10000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10000 (by norm_num)]
                  have h2 : 10000 = 0 + 10 * 1000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1000 (by norm_num)]
                  have h3 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100000 ∈ { m : ℕ | 0 < m ∧ 32 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 32 ≤ 100000 := h_inf
                have h_lt : A004290 32 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 33
                have h_digits : Nat.digits 10 111111 = [1, 1, 1, 1, 1, 1] := by
                  have h1 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h2 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h3 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h4 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111111 ∈ { m : ℕ | 0 < m ∧ 33 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 33 ≤ 111111 := h_inf
                have h_lt : A004290 33 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 34
                have h_digits : Nat.digits 10 111010 = [0, 1, 0, 1, 1, 1] := by
                  have h1 : 111010 = 0 + 10 * 11101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11101 (by norm_num)]
                  have h2 : 11101 = 1 + 10 * 1110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1110 (by norm_num)]
                  have h3 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h4 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111010 ∈ { m : ℕ | 0 < m ∧ 34 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 34 ≤ 111010 := h_inf
                have h_lt : A004290 34 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 35
                have h_digits : Nat.digits 10 10010 = [0, 1, 0, 0, 1] := by
                  have h1 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h2 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10010 ∈ { m : ℕ | 0 < m ∧ 35 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 35 ≤ 10010 := h_inf
                have h_lt : A004290 35 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 36
                have h_digits : Nat.digits 10 11111111100 = [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 11111111100 = 0 + 10 * 1111111110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1111111110 (by norm_num)]
                  have h2 : 1111111110 = 0 + 10 * 111111111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 111111111 (by norm_num)]
                  have h3 : 111111111 = 1 + 10 * 11111111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11111111 (by norm_num)]
                  have h4 : 11111111 = 1 + 10 * 1111111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1111111 (by norm_num)]
                  have h5 : 1111111 = 1 + 10 * 111111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 111111 (by norm_num)]
                  have h6 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h7 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h8 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h9 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h10 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h10]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11111111100 ∈ { m : ℕ | 0 < m ∧ 36 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 36 ≤ 11111111100 := h_inf
                have h_lt : A004290 36 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 37
                have h_digits : Nat.digits 10 111 = [1, 1, 1] := by
                  have h1 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h2 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111 ∈ { m : ℕ | 0 < m ∧ 37 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 37 ≤ 111 := h_inf
                have h_lt : A004290 37 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 38
                have h_digits : Nat.digits 10 110010 = [0, 1, 0, 0, 1, 1] := by
                  have h1 : 110010 = 0 + 10 * 11001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11001 (by norm_num)]
                  have h2 : 11001 = 1 + 10 * 1100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1100 (by norm_num)]
                  have h3 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h4 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 110010 ∈ { m : ℕ | 0 < m ∧ 38 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 38 ≤ 110010 := h_inf
                have h_lt : A004290 38 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 39
                have h_digits : Nat.digits 10 10101 = [1, 0, 1, 0, 1] := by
                  have h1 : 10101 = 1 + 10 * 1010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1010 (by norm_num)]
                  have h2 : 1010 = 0 + 10 * 101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 101 (by norm_num)]
                  have h3 : 101 = 1 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10101 ∈ { m : ℕ | 0 < m ∧ 39 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 39 ≤ 10101 := h_inf
                have h_lt : A004290 39 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 40
                have h_digits : Nat.digits 10 1000 = [0, 0, 0, 1] := by
                  have h1 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h2 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h3 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1000 ∈ { m : ℕ | 0 < m ∧ 40 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 40 ≤ 1000 := h_inf
                have h_lt : A004290 40 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 41
                have h_digits : Nat.digits 10 11111 = [1, 1, 1, 1, 1] := by
                  have h1 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h2 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h3 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11111 ∈ { m : ℕ | 0 < m ∧ 41 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 41 ≤ 11111 := h_inf
                have h_lt : A004290 41 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 42
                have h_digits : Nat.digits 10 101010 = [0, 1, 0, 1, 0, 1] := by
                  have h1 : 101010 = 0 + 10 * 10101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10101 (by norm_num)]
                  have h2 : 10101 = 1 + 10 * 1010 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1010 (by norm_num)]
                  have h3 : 1010 = 0 + 10 * 101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 101 (by norm_num)]
                  have h4 : 101 = 1 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 101010 ∈ { m : ℕ | 0 < m ∧ 42 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 42 ≤ 101010 := h_inf
                have h_lt : A004290 42 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 43
                have h_digits : Nat.digits 10 1101101 = [1, 0, 1, 1, 0, 1, 1] := by
                  have h1 : 1101101 = 1 + 10 * 110110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 110110 (by norm_num)]
                  have h2 : 110110 = 0 + 10 * 11011 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11011 (by norm_num)]
                  have h3 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h4 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h5 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1101101 ∈ { m : ℕ | 0 < m ∧ 43 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 43 ≤ 1101101 := h_inf
                have h_lt : A004290 43 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 44
                have h_digits : Nat.digits 10 1100 = [0, 0, 1, 1] := by
                  have h1 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h2 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h3 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1100 ∈ { m : ℕ | 0 < m ∧ 44 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 44 ≤ 1100 := h_inf
                have h_lt : A004290 44 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 45
                have h_digits : Nat.digits 10 1111111110 = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 1111111110 = 0 + 10 * 111111111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111111111 (by norm_num)]
                  have h2 : 111111111 = 1 + 10 * 11111111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11111111 (by norm_num)]
                  have h3 : 11111111 = 1 + 10 * 1111111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1111111 (by norm_num)]
                  have h4 : 1111111 = 1 + 10 * 111111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 111111 (by norm_num)]
                  have h5 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h6 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h7 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h8 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h9 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1111111110 ∈ { m : ℕ | 0 < m ∧ 45 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 45 ≤ 1111111110 := h_inf
                have h_lt : A004290 45 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 46
                have h_digits : Nat.digits 10 1101010 = [0, 1, 0, 1, 0, 1, 1] := by
                  have h1 : 1101010 = 0 + 10 * 110101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 110101 (by norm_num)]
                  have h2 : 110101 = 1 + 10 * 11010 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11010 (by norm_num)]
                  have h3 : 11010 = 0 + 10 * 1101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1101 (by norm_num)]
                  have h4 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h5 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1101010 ∈ { m : ℕ | 0 < m ∧ 46 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 46 ≤ 1101010 := h_inf
                have h_lt : A004290 46 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 47
                have h_digits : Nat.digits 10 10011 = [1, 1, 0, 0, 1] := by
                  have h1 : 10011 = 1 + 10 * 1001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1001 (by norm_num)]
                  have h2 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10011 ∈ { m : ℕ | 0 < m ∧ 47 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 47 ≤ 10011 := h_inf
                have h_lt : A004290 47 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 48
                have h_digits : Nat.digits 10 1110000 = [0, 0, 0, 0, 1, 1, 1] := by
                  have h1 : 1110000 = 0 + 10 * 111000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111000 (by norm_num)]
                  have h2 : 111000 = 0 + 10 * 11100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11100 (by norm_num)]
                  have h3 : 11100 = 0 + 10 * 1110 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1110 (by norm_num)]
                  have h4 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h5 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1110000 ∈ { m : ℕ | 0 < m ∧ 48 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 48 ≤ 1110000 := h_inf
                have h_lt : A004290 48 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 49
                have h_digits : Nat.digits 10 1100001 = [1, 0, 0, 0, 0, 1, 1] := by
                  have h1 : 1100001 = 1 + 10 * 110000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 110000 (by norm_num)]
                  have h2 : 110000 = 0 + 10 * 11000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11000 (by norm_num)]
                  have h3 : 11000 = 0 + 10 * 1100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1100 (by norm_num)]
                  have h4 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h5 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1100001 ∈ { m : ℕ | 0 < m ∧ 49 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 49 ≤ 1100001 := h_inf
                have h_lt : A004290 49 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 50
                have h_digits : Nat.digits 10 100 = [0, 0, 1] := by
                  have h1 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h2 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100 ∈ { m : ℕ | 0 < m ∧ 50 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 50 ≤ 100 := h_inf
                have h_lt : A004290 50 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 51
                have h_digits : Nat.digits 10 100011 = [1, 1, 0, 0, 0, 1] := by
                  have h1 : 100011 = 1 + 10 * 10001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 10001 (by norm_num)]
                  have h2 : 10001 = 1 + 10 * 1000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1000 (by norm_num)]
                  have h3 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100011 ∈ { m : ℕ | 0 < m ∧ 51 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 51 ≤ 100011 := h_inf
                have h_lt : A004290 51 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 52
                have h_digits : Nat.digits 10 100100 = [0, 0, 1, 0, 0, 1] := by
                  have h1 : 100100 = 0 + 10 * 10010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10010 (by norm_num)]
                  have h2 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h3 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100100 ∈ { m : ℕ | 0 < m ∧ 52 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 52 ≤ 100100 := h_inf
                have h_lt : A004290 52 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 53
                have h_digits : Nat.digits 10 100011 = [1, 1, 0, 0, 0, 1] := by
                  have h1 : 100011 = 1 + 10 * 10001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 10001 (by norm_num)]
                  have h2 : 10001 = 1 + 10 * 1000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1000 (by norm_num)]
                  have h3 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100011 ∈ { m : ℕ | 0 < m ∧ 53 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 53 ≤ 100011 := h_inf
                have h_lt : A004290 53 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 54
                have h_digits : Nat.digits 10 11011111110 = [0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1] := by
                  have h1 : 11011111110 = 0 + 10 * 1101111111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1101111111 (by norm_num)]
                  have h2 : 1101111111 = 1 + 10 * 110111111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 110111111 (by norm_num)]
                  have h3 : 110111111 = 1 + 10 * 11011111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11011111 (by norm_num)]
                  have h4 : 11011111 = 1 + 10 * 1101111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1101111 (by norm_num)]
                  have h5 : 1101111 = 1 + 10 * 110111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110111 (by norm_num)]
                  have h6 : 110111 = 1 + 10 * 11011 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 11011 (by norm_num)]
                  have h7 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h8 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h9 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h10 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h10]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11011111110 ∈ { m : ℕ | 0 < m ∧ 54 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 54 ≤ 11011111110 := h_inf
                have h_lt : A004290 54 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 55
                have h_digits : Nat.digits 10 110 = [0, 1, 1] := by
                  have h1 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h2 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 110 ∈ { m : ℕ | 0 < m ∧ 55 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 55 ≤ 110 := h_inf
                have h_lt : A004290 55 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 56
                have h_digits : Nat.digits 10 1001000 = [0, 0, 0, 1, 0, 0, 1] := by
                  have h1 : 1001000 = 0 + 10 * 100100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 100100 (by norm_num)]
                  have h2 : 100100 = 0 + 10 * 10010 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 10010 (by norm_num)]
                  have h3 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h4 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h5 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h6 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1001000 ∈ { m : ℕ | 0 < m ∧ 56 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 56 ≤ 1001000 := h_inf
                have h_lt : A004290 56 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 57
                have h_digits : Nat.digits 10 11001 = [1, 0, 0, 1, 1] := by
                  have h1 : 11001 = 1 + 10 * 1100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1100 (by norm_num)]
                  have h2 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h3 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11001 ∈ { m : ℕ | 0 < m ∧ 57 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 57 ≤ 11001 := h_inf
                have h_lt : A004290 57 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 58
                have h_digits : Nat.digits 10 11011010 = [0, 1, 0, 1, 1, 0, 1, 1] := by
                  have h1 : 11011010 = 0 + 10 * 1101101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1101101 (by norm_num)]
                  have h2 : 1101101 = 1 + 10 * 110110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 110110 (by norm_num)]
                  have h3 : 110110 = 0 + 10 * 11011 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11011 (by norm_num)]
                  have h4 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h5 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11011010 ∈ { m : ℕ | 0 < m ∧ 58 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 58 ≤ 11011010 := h_inf
                have h_lt : A004290 58 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 59
                have h_digits : Nat.digits 10 11011111 = [1, 1, 1, 1, 1, 0, 1, 1] := by
                  have h1 : 11011111 = 1 + 10 * 1101111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1101111 (by norm_num)]
                  have h2 : 1101111 = 1 + 10 * 110111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 110111 (by norm_num)]
                  have h3 : 110111 = 1 + 10 * 11011 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11011 (by norm_num)]
                  have h4 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h5 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11011111 ∈ { m : ℕ | 0 < m ∧ 59 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 59 ≤ 11011111 := h_inf
                have h_lt : A004290 59 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 60
                have h_digits : Nat.digits 10 11100 = [0, 0, 1, 1, 1] := by
                  have h1 : 11100 = 0 + 10 * 1110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1110 (by norm_num)]
                  have h2 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h3 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11100 ∈ { m : ℕ | 0 < m ∧ 60 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 60 ≤ 11100 := h_inf
                have h_lt : A004290 60 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 61
                have h_digits : Nat.digits 10 100101 = [1, 0, 1, 0, 0, 1] := by
                  have h1 : 100101 = 1 + 10 * 10010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 10010 (by norm_num)]
                  have h2 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h3 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100101 ∈ { m : ℕ | 0 < m ∧ 61 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 61 ≤ 100101 := h_inf
                have h_lt : A004290 61 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 62
                have h_digits : Nat.digits 10 1110110 = [0, 1, 1, 0, 1, 1, 1] := by
                  have h1 : 1110110 = 0 + 10 * 111011 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111011 (by norm_num)]
                  have h2 : 111011 = 1 + 10 * 11101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11101 (by norm_num)]
                  have h3 : 11101 = 1 + 10 * 1110 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1110 (by norm_num)]
                  have h4 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h5 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1110110 ∈ { m : ℕ | 0 < m ∧ 62 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 62 ≤ 1110110 := h_inf
                have h_lt : A004290 62 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 63
                have h_digits : Nat.digits 10 1111011111 = [1, 1, 1, 1, 1, 0, 1, 1, 1, 1] := by
                  have h1 : 1111011111 = 1 + 10 * 111101111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 111101111 (by norm_num)]
                  have h2 : 111101111 = 1 + 10 * 11110111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11110111 (by norm_num)]
                  have h3 : 11110111 = 1 + 10 * 1111011 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1111011 (by norm_num)]
                  have h4 : 1111011 = 1 + 10 * 111101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 111101 (by norm_num)]
                  have h5 : 111101 = 1 + 10 * 11110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11110 (by norm_num)]
                  have h6 : 11110 = 0 + 10 * 1111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 1111 (by norm_num)]
                  have h7 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h8 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h9 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1111011111 ∈ { m : ℕ | 0 < m ∧ 63 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 63 ≤ 1111011111 := h_inf
                have h_lt : A004290 63 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 64
                have h_digits : Nat.digits 10 1000000 = [0, 0, 0, 0, 0, 0, 1] := by
                  have h1 : 1000000 = 0 + 10 * 100000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 100000 (by norm_num)]
                  have h2 : 100000 = 0 + 10 * 10000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 10000 (by norm_num)]
                  have h3 : 10000 = 0 + 10 * 1000 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1000 (by norm_num)]
                  have h4 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h5 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h6 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1000000 ∈ { m : ℕ | 0 < m ∧ 64 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 64 ≤ 1000000 := h_inf
                have h_lt : A004290 64 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 65
                have h_digits : Nat.digits 10 10010 = [0, 1, 0, 0, 1] := by
                  have h1 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h2 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10010 ∈ { m : ℕ | 0 < m ∧ 65 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 65 ≤ 10010 := h_inf
                have h_lt : A004290 65 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 66
                have h_digits : Nat.digits 10 1111110 = [0, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 1111110 = 0 + 10 * 111111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111111 (by norm_num)]
                  have h2 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h3 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h4 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h5 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1111110 ∈ { m : ℕ | 0 < m ∧ 66 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 66 ≤ 1111110 := h_inf
                have h_lt : A004290 66 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 67
                have h_digits : Nat.digits 10 1101011 = [1, 1, 0, 1, 0, 1, 1] := by
                  have h1 : 1101011 = 1 + 10 * 110101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 110101 (by norm_num)]
                  have h2 : 110101 = 1 + 10 * 11010 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11010 (by norm_num)]
                  have h3 : 11010 = 0 + 10 * 1101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1101 (by norm_num)]
                  have h4 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h5 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1101011 ∈ { m : ℕ | 0 < m ∧ 67 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 67 ≤ 1101011 := h_inf
                have h_lt : A004290 67 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 68
                have h_digits : Nat.digits 10 1110100 = [0, 0, 1, 0, 1, 1, 1] := by
                  have h1 : 1110100 = 0 + 10 * 111010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111010 (by norm_num)]
                  have h2 : 111010 = 0 + 10 * 11101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11101 (by norm_num)]
                  have h3 : 11101 = 1 + 10 * 1110 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1110 (by norm_num)]
                  have h4 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h5 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1110100 ∈ { m : ℕ | 0 < m ∧ 68 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 68 ≤ 1110100 := h_inf
                have h_lt : A004290 68 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 69
                have h_digits : Nat.digits 10 10000101 = [1, 0, 1, 0, 0, 0, 0, 1] := by
                  have h1 : 10000101 = 1 + 10 * 1000010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1000010 (by norm_num)]
                  have h2 : 1000010 = 0 + 10 * 100001 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 100001 (by norm_num)]
                  have h3 : 100001 = 1 + 10 * 10000 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 10000 (by norm_num)]
                  have h4 : 10000 = 0 + 10 * 1000 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1000 (by norm_num)]
                  have h5 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h6 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h7 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10000101 ∈ { m : ℕ | 0 < m ∧ 69 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 69 ≤ 10000101 := h_inf
                have h_lt : A004290 69 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 70
                have h_digits : Nat.digits 10 10010 = [0, 1, 0, 0, 1] := by
                  have h1 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h2 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10010 ∈ { m : ℕ | 0 < m ∧ 70 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 70 ≤ 10010 := h_inf
                have h_lt : A004290 70 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 71
                have h_digits : Nat.digits 10 10011 = [1, 1, 0, 0, 1] := by
                  have h1 : 10011 = 1 + 10 * 1001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1001 (by norm_num)]
                  have h2 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10011 ∈ { m : ℕ | 0 < m ∧ 71 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 71 ≤ 10011 := h_inf
                have h_lt : A004290 71 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 72
                have h_digits : Nat.digits 10 111111111000 = [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 111111111000 = 0 + 10 * 11111111100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11111111100 (by norm_num)]
                  have h2 : 11111111100 = 0 + 10 * 1111111110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 1111111110 (by norm_num)]
                  have h3 : 1111111110 = 0 + 10 * 111111111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 111111111 (by norm_num)]
                  have h4 : 111111111 = 1 + 10 * 11111111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11111111 (by norm_num)]
                  have h5 : 11111111 = 1 + 10 * 1111111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1111111 (by norm_num)]
                  have h6 : 1111111 = 1 + 10 * 111111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 111111 (by norm_num)]
                  have h7 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h8 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h9 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h10 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h10]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h11 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h11]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111111111000 ∈ { m : ℕ | 0 < m ∧ 72 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 72 ≤ 111111111000 := h_inf
                have h_lt : A004290 72 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 73
                have h_digits : Nat.digits 10 10001 = [1, 0, 0, 0, 1] := by
                  have h1 : 10001 = 1 + 10 * 1000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1000 (by norm_num)]
                  have h2 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10001 ∈ { m : ℕ | 0 < m ∧ 73 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 73 ≤ 10001 := h_inf
                have h_lt : A004290 73 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 74
                have h_digits : Nat.digits 10 1110 = [0, 1, 1, 1] := by
                  have h1 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h2 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h3 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1110 ∈ { m : ℕ | 0 < m ∧ 74 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 74 ≤ 1110 := h_inf
                have h_lt : A004290 74 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 75
                have h_digits : Nat.digits 10 11100 = [0, 0, 1, 1, 1] := by
                  have h1 : 11100 = 0 + 10 * 1110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1110 (by norm_num)]
                  have h2 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h3 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11100 ∈ { m : ℕ | 0 < m ∧ 75 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 75 ≤ 11100 := h_inf
                have h_lt : A004290 75 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 76
                have h_digits : Nat.digits 10 1100100 = [0, 0, 1, 0, 0, 1, 1] := by
                  have h1 : 1100100 = 0 + 10 * 110010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 110010 (by norm_num)]
                  have h2 : 110010 = 0 + 10 * 11001 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11001 (by norm_num)]
                  have h3 : 11001 = 1 + 10 * 1100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1100 (by norm_num)]
                  have h4 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h5 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h6 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1100100 ∈ { m : ℕ | 0 < m ∧ 76 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 76 ≤ 1100100 := h_inf
                have h_lt : A004290 76 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 77
                have h_digits : Nat.digits 10 1001 = [1, 0, 0, 1] := by
                  have h1 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h2 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h3 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1001 ∈ { m : ℕ | 0 < m ∧ 77 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 77 ≤ 1001 := h_inf
                have h_lt : A004290 77 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 78
                have h_digits : Nat.digits 10 101010 = [0, 1, 0, 1, 0, 1] := by
                  have h1 : 101010 = 0 + 10 * 10101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10101 (by norm_num)]
                  have h2 : 10101 = 1 + 10 * 1010 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1010 (by norm_num)]
                  have h3 : 1010 = 0 + 10 * 101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 101 (by norm_num)]
                  have h4 : 101 = 1 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 101010 ∈ { m : ℕ | 0 < m ∧ 78 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 78 ≤ 101010 := h_inf
                have h_lt : A004290 78 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 79
                have h_digits : Nat.digits 10 10010011 = [1, 1, 0, 0, 1, 0, 0, 1] := by
                  have h1 : 10010011 = 1 + 10 * 1001001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1001001 (by norm_num)]
                  have h2 : 1001001 = 1 + 10 * 100100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100100 (by norm_num)]
                  have h3 : 100100 = 0 + 10 * 10010 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10010 (by norm_num)]
                  have h4 : 10010 = 0 + 10 * 1001 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1001 (by norm_num)]
                  have h5 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h6 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h7 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10010011 ∈ { m : ℕ | 0 < m ∧ 79 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 79 ≤ 10010011 := h_inf
                have h_lt : A004290 79 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 80
                have h_digits : Nat.digits 10 10000 = [0, 0, 0, 0, 1] := by
                  have h1 : 10000 = 0 + 10 * 1000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1000 (by norm_num)]
                  have h2 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h3 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h4 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10000 ∈ { m : ℕ | 0 < m ∧ 80 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 80 ≤ 10000 := h_inf
                have h_lt : A004290 80 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 81
                have h_digits : Nat.digits 10 1111111101 = [1, 0, 1, 1, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 1111111101 = 1 + 10 * 111111110 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 111111110 (by norm_num)]
                  have h2 : 111111110 = 0 + 10 * 11111111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 11111111 (by norm_num)]
                  have h3 : 11111111 = 1 + 10 * 1111111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1111111 (by norm_num)]
                  have h4 : 1111111 = 1 + 10 * 111111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 111111 (by norm_num)]
                  have h5 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h6 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h7 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h8 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h9 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1111111101 ∈ { m : ℕ | 0 < m ∧ 81 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 81 ≤ 1111111101 := h_inf
                have h_lt : A004290 81 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 82
                have h_digits : Nat.digits 10 111110 = [0, 1, 1, 1, 1, 1] := by
                  have h1 : 111110 = 0 + 10 * 11111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11111 (by norm_num)]
                  have h2 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h3 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h4 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111110 ∈ { m : ℕ | 0 < m ∧ 82 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 82 ≤ 111110 := h_inf
                have h_lt : A004290 82 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 83
                have h_digits : Nat.digits 10 101011 = [1, 1, 0, 1, 0, 1] := by
                  have h1 : 101011 = 1 + 10 * 10101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 10101 (by norm_num)]
                  have h2 : 10101 = 1 + 10 * 1010 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1010 (by norm_num)]
                  have h3 : 1010 = 0 + 10 * 101 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 101 (by norm_num)]
                  have h4 : 101 = 1 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 101011 ∈ { m : ℕ | 0 < m ∧ 83 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 83 ≤ 101011 := h_inf
                have h_lt : A004290 83 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 84
                have h_digits : Nat.digits 10 1010100 = [0, 0, 1, 0, 1, 0, 1] := by
                  have h1 : 1010100 = 0 + 10 * 101010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 101010 (by norm_num)]
                  have h2 : 101010 = 0 + 10 * 10101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 10101 (by norm_num)]
                  have h3 : 10101 = 1 + 10 * 1010 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1010 (by norm_num)]
                  have h4 : 1010 = 0 + 10 * 101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 101 (by norm_num)]
                  have h5 : 101 = 1 + 10 * 10 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 10 (by norm_num)]
                  have h6 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1010100 ∈ { m : ℕ | 0 < m ∧ 84 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 84 ≤ 1010100 := h_inf
                have h_lt : A004290 84 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 85
                have h_digits : Nat.digits 10 111010 = [0, 1, 0, 1, 1, 1] := by
                  have h1 : 111010 = 0 + 10 * 11101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11101 (by norm_num)]
                  have h2 : 11101 = 1 + 10 * 1110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1110 (by norm_num)]
                  have h3 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h4 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 111010 ∈ { m : ℕ | 0 < m ∧ 85 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 85 ≤ 111010 := h_inf
                have h_lt : A004290 85 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 86
                have h_digits : Nat.digits 10 11011010 = [0, 1, 0, 1, 1, 0, 1, 1] := by
                  have h1 : 11011010 = 0 + 10 * 1101101 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1101101 (by norm_num)]
                  have h2 : 1101101 = 1 + 10 * 110110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 110110 (by norm_num)]
                  have h3 : 110110 = 0 + 10 * 11011 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11011 (by norm_num)]
                  have h4 : 11011 = 1 + 10 * 1101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1101 (by norm_num)]
                  have h5 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11011010 ∈ { m : ℕ | 0 < m ∧ 86 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 86 ≤ 11011010 := h_inf
                have h_lt : A004290 86 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 87
                have h_digits : Nat.digits 10 11010111 = [1, 1, 1, 0, 1, 0, 1, 1] := by
                  have h1 : 11010111 = 1 + 10 * 1101011 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1101011 (by norm_num)]
                  have h2 : 1101011 = 1 + 10 * 110101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 110101 (by norm_num)]
                  have h3 : 110101 = 1 + 10 * 11010 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11010 (by norm_num)]
                  have h4 : 11010 = 0 + 10 * 1101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1101 (by norm_num)]
                  have h5 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11010111 ∈ { m : ℕ | 0 < m ∧ 87 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 87 ≤ 11010111 := h_inf
                have h_lt : A004290 87 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 88
                have h_digits : Nat.digits 10 11000 = [0, 0, 0, 1, 1] := by
                  have h1 : 11000 = 0 + 10 * 1100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1100 (by norm_num)]
                  have h2 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h3 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h4 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11000 ∈ { m : ℕ | 0 < m ∧ 88 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 88 ≤ 11000 := h_inf
                have h_lt : A004290 88 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 89
                have h_digits : Nat.digits 10 11010101 = [1, 0, 1, 0, 1, 0, 1, 1] := by
                  have h1 : 11010101 = 1 + 10 * 1101010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1101010 (by norm_num)]
                  have h2 : 1101010 = 0 + 10 * 110101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 110101 (by norm_num)]
                  have h3 : 110101 = 1 + 10 * 11010 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11010 (by norm_num)]
                  have h4 : 11010 = 0 + 10 * 1101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1101 (by norm_num)]
                  have h5 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11010101 ∈ { m : ℕ | 0 < m ∧ 89 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 89 ≤ 11010101 := h_inf
                have h_lt : A004290 89 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 90
                have h_digits : Nat.digits 10 1111111110 = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1] := by
                  have h1 : 1111111110 = 0 + 10 * 111111111 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 111111111 (by norm_num)]
                  have h2 : 111111111 = 1 + 10 * 11111111 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 11111111 (by norm_num)]
                  have h3 : 11111111 = 1 + 10 * 1111111 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 1111111 (by norm_num)]
                  have h4 : 1111111 = 1 + 10 * 111111 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 1 (by norm_num) 111111 (by norm_num)]
                  have h5 : 111111 = 1 + 10 * 11111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 11111 (by norm_num)]
                  have h6 : 11111 = 1 + 10 * 1111 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 1111 (by norm_num)]
                  have h7 : 1111 = 1 + 10 * 111 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 111 (by norm_num)]
                  have h8 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h8]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h9 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h9]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1111111110 ∈ { m : ℕ | 0 < m ∧ 90 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 90 ≤ 1111111110 := h_inf
                have h_lt : A004290 90 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 91
                have h_digits : Nat.digits 10 1001 = [1, 0, 0, 1] := by
                  have h1 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h2 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h3 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 1001 ∈ { m : ℕ | 0 < m ∧ 91 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 91 ≤ 1001 := h_inf
                have h_lt : A004290 91 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 92
                have h_digits : Nat.digits 10 11010100 = [0, 0, 1, 0, 1, 0, 1, 1] := by
                  have h1 : 11010100 = 0 + 10 * 1101010 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1101010 (by norm_num)]
                  have h2 : 1101010 = 0 + 10 * 110101 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 110101 (by norm_num)]
                  have h3 : 110101 = 1 + 10 * 11010 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 11010 (by norm_num)]
                  have h4 : 11010 = 0 + 10 * 1101 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1101 (by norm_num)]
                  have h5 : 1101 = 1 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11010100 ∈ { m : ℕ | 0 < m ∧ 92 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 92 ≤ 11010100 := h_inf
                have h_lt : A004290 92 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 93
                have h_digits : Nat.digits 10 10000011 = [1, 1, 0, 0, 0, 0, 0, 1] := by
                  have h1 : 10000011 = 1 + 10 * 1000001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1000001 (by norm_num)]
                  have h2 : 1000001 = 1 + 10 * 100000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 100000 (by norm_num)]
                  have h3 : 100000 = 0 + 10 * 10000 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 10000 (by norm_num)]
                  have h4 : 10000 = 0 + 10 * 1000 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1000 (by norm_num)]
                  have h5 : 1000 = 0 + 10 * 100 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 100 (by norm_num)]
                  have h6 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h7 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 10000011 ∈ { m : ℕ | 0 < m ∧ 93 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 93 ≤ 10000011 := h_inf
                have h_lt : A004290 93 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 94
                have h_digits : Nat.digits 10 100110 = [0, 1, 1, 0, 0, 1] := by
                  have h1 : 100110 = 0 + 10 * 10011 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 10011 (by norm_num)]
                  have h2 : 10011 = 1 + 10 * 1001 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1001 (by norm_num)]
                  have h3 : 1001 = 1 + 10 * 100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 1 (by norm_num) 100 (by norm_num)]
                  have h4 : 100 = 0 + 10 * 10 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 10 (by norm_num)]
                  have h5 : 10 = 0 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 100110 ∈ { m : ℕ | 0 < m ∧ 94 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 94 ≤ 100110 := h_inf
                have h_lt : A004290 94 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 95
                have h_digits : Nat.digits 10 110010 = [0, 1, 0, 0, 1, 1] := by
                  have h1 : 110010 = 0 + 10 * 11001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 11001 (by norm_num)]
                  have h2 : 11001 = 1 + 10 * 1100 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 1100 (by norm_num)]
                  have h3 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h4 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h5 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 110010 ∈ { m : ℕ | 0 < m ∧ 95 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 95 ≤ 110010 := h_inf
                have h_lt : A004290 95 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 96
                have h_digits : Nat.digits 10 11100000 = [0, 0, 0, 0, 0, 1, 1, 1] := by
                  have h1 : 11100000 = 0 + 10 * 1110000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1110000 (by norm_num)]
                  have h2 : 1110000 = 0 + 10 * 111000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 111000 (by norm_num)]
                  have h3 : 111000 = 0 + 10 * 11100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11100 (by norm_num)]
                  have h4 : 11100 = 0 + 10 * 1110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1110 (by norm_num)]
                  have h5 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h6 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11100000 ∈ { m : ℕ | 0 < m ∧ 96 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 96 ≤ 11100000 := h_inf
                have h_lt : A004290 96 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 97
                have h_digits : Nat.digits 10 11100001 = [1, 0, 0, 0, 0, 1, 1, 1] := by
                  have h1 : 11100001 = 1 + 10 * 1110000 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 1 (by norm_num) 1110000 (by norm_num)]
                  have h2 : 1110000 = 0 + 10 * 111000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 0 (by norm_num) 111000 (by norm_num)]
                  have h3 : 111000 = 0 + 10 * 11100 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11100 (by norm_num)]
                  have h4 : 11100 = 0 + 10 * 1110 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1110 (by norm_num)]
                  have h5 : 1110 = 0 + 10 * 111 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 111 (by norm_num)]
                  have h6 : 111 = 1 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 1 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11100001 ∈ { m : ℕ | 0 < m ∧ 97 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 97 ≤ 11100001 := h_inf
                have h_lt : A004290 97 < (10^18 - 1)/9 := by omega
                exact h_lt
              · -- n = 98
                have h_digits : Nat.digits 10 11000010 = [0, 1, 0, 0, 0, 0, 1, 1] := by
                  have h1 : 11000010 = 0 + 10 * 1100001 := by norm_num
                  rw [h1]
                  rw [digits_ten_step 0 (by norm_num) 1100001 (by norm_num)]
                  have h2 : 1100001 = 1 + 10 * 110000 := by norm_num
                  rw [h2]
                  rw [digits_ten_step 1 (by norm_num) 110000 (by norm_num)]
                  have h3 : 110000 = 0 + 10 * 11000 := by norm_num
                  rw [h3]
                  rw [digits_ten_step 0 (by norm_num) 11000 (by norm_num)]
                  have h4 : 11000 = 0 + 10 * 1100 := by norm_num
                  rw [h4]
                  rw [digits_ten_step 0 (by norm_num) 1100 (by norm_num)]
                  have h5 : 1100 = 0 + 10 * 110 := by norm_num
                  rw [h5]
                  rw [digits_ten_step 0 (by norm_num) 110 (by norm_num)]
                  have h6 : 110 = 0 + 10 * 11 := by norm_num
                  rw [h6]
                  rw [digits_ten_step 0 (by norm_num) 11 (by norm_num)]
                  have h7 : 11 = 1 + 10 * 1 := by norm_num
                  rw [h7]
                  rw [digits_ten_step 1 (by norm_num) 1 (by norm_num)]
                  rw [digits_ten_base 1 (by norm_num) (by norm_num)]
                have h_mem : 11000010 ∈ { m : ℕ | 0 < m ∧ 98 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } := by
                  refine ⟨by norm_num, by norm_num, ?_⟩
                  rw [h_digits]
                  decide
                have h_inf := Nat.sInf_le h_mem
                have h_le : A004290 98 ≤ 11000010 := h_inf
                have h_lt : A004290 98 < (10^18 - 1)/9 := by omega
                exact h_lt
            · -- k ≥ 3
              have hk3 : k ≥ 3 := by omega
              let d2 := Nat.gcd n (10^(k-2))
              let u2 := n / d2
              have hd2 : d2 ∣ 10^(k-2) := Nat.gcd_dvd_right n (10^(k-2))
              have hu2 : d2 ∣ n := Nat.gcd_dvd_left n (10^(k-2))
              have hu2_pos : u2 > 0 := by
                apply Nat.div_pos
                · exact Nat.le_of_dvd hn_pos hu2
                · have h_pow_pos : 10^(k-2) > 0 := Nat.pow_pos (by omega)
                  exact Nat.pos_of_dvd_of_pos hd2 h_pow_pos
              by_cases hu2_lt : u2 + 1 < 8 * k + 1
              · have h_lt_u2 : A004290 u2 < (10^(u2 + 1) - 1) / 9 := A004290_lt_geom_sum u2 hu2_pos
                have h_le_u2 : (10^(u2 + 1) - 1) / 9 ≤ (10^(8 * k) - 1) / 9 := by
                  apply Nat.div_le_div_right
                  have h_pow : 10^(u2 + 1) ≤ 10^(8 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
                  omega
                have h_le_M2 : A004290 n ≤ 10^(k-2) * A004290 u2 := A004290_le_ten_pow_mul n (k-2) d2 hd2 hu2 hn_pos
                have h_lt_u2_geom : A004290 u2 < (10^(8 * k) - 1) / 9 := lt_of_lt_of_le h_lt_u2 h_le_u2
                have h_lt_M2 : 10^(k-2) * A004290 u2 < (10^(9 * k) - 1) / 9 := by
                  have h_eqA : 9 * ((10^(8 * k) - 1) / 9) = 10^(8 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k))
                  have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                  have h_mul_lt : 9 * (10^(k-2) * A004290 u2) < 9 * ((10^(9 * k) - 1) / 9) := by
                    rw [h_eqB]
                    calc 9 * (10^(k-2) * A004290 u2) = 10^(k-2) * (9 * A004290 u2) := by ring
                      _ < 10^(k-2) * (10^(8 * k) - 1) := by
                        apply Nat.mul_lt_mul_of_pos_left
                        · have : 9 * A004290 u2 < 9 * ((10^(8 * k) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u2_geom (by norm_num)
                          rw [h_eqA] at this
                          exact this
                        · exact Nat.pow_pos (by norm_num)
                      _ = 10^(9 * k - 2) - 10^(k-2) := by
                        rw [Nat.mul_sub_left_distrib, mul_one]
                        have h_pow : 10^(k-2) * 10^(8 * k) = 10^(9 * k - 2) := by
                          rw [← pow_add]
                          congr 1
                          omega
                        rw [h_pow]
                      _ < 10^(9 * k) - 1 := by
                        have h_pow_lt : 10^(9 * k - 2) < 10^(9 * k) := by
                          have : 9 * k = (9 * k - 2) + 2 := by omega
                          nth_rw 2 [this]
                          rw [pow_add]
                          have : 10^(9 * k - 2) * 10^2 > 10^(9 * k - 2) * 1 := by
                            apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                          omega
                        have h_pow_k : 10^(k-2) ≥ 1 := Nat.one_le_pow (k-2) 10 (by norm_num)
                        have h_pow_le : 10^(k-2) ≤ 10^(9 * k - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
                        omega
                  exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                exact lt_of_le_of_lt h_le_M2 h_lt_M2
              · -- u2 + 1 ≥ 8 * k + 1, so u2 ≥ 8 * k.
                -- We define d3 = gcd n (10^(k-3)) and u3 = n / d3.
                let d3 := Nat.gcd n (10^(k-3))
                let u3 := n / d3
                have hd3 : d3 ∣ 10^(k-3) := Nat.gcd_dvd_right n (10^(k-3))
                have hu3 : d3 ∣ n := Nat.gcd_dvd_left n (10^(k-3))
                have hu3_pos : u3 > 0 := by
                  apply Nat.div_pos
                  · exact Nat.le_of_dvd hn_pos hu3
                  · have h_pow_pos : 10^(k-3) > 0 := Nat.pow_pos (by omega)
                    exact Nat.pos_of_dvd_of_pos hd3 h_pow_pos
                by_cases hu3_lt : u3 + 1 < 8 * k + 1
                · have h_lt_u3 : A004290 u3 < (10^(u3 + 1) - 1) / 9 := A004290_lt_geom_sum u3 hu3_pos
                  have h_le_u3 : (10^(u3 + 1) - 1) / 9 ≤ (10^(8 * k) - 1) / 9 := by
                    apply Nat.div_le_div_right
                    have h_pow : 10^(u3 + 1) ≤ 10^(8 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
                    omega
                  have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                  have h_lt_u3_geom : A004290 u3 < (10^(8 * k) - 1) / 9 := lt_of_lt_of_le h_lt_u3 h_le_u3
                  have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                    have h_eqA : 9 * ((10^(8 * k) - 1) / 9) = 10^(8 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k))
                    have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                    have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                      rw [h_eqB]
                      calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                        _ < 10^(k-3) * (10^(8 * k) - 1) := by
                          apply Nat.mul_lt_mul_of_pos_left
                          · have : 9 * A004290 u3 < 9 * ((10^(8 * k) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                            rw [h_eqA] at this
                            exact this
                          · exact Nat.pow_pos (by norm_num)
                        _ = 10^(9 * k - 3) - 10^(k-3) := by
                          rw [Nat.mul_sub_left_distrib, mul_one]
                          have h_pow : 10^(k-3) * 10^(8 * k) = 10^(9 * k - 3) := by
                            rw [← pow_add]
                            congr 1
                            omega
                          rw [h_pow]
                        _ < 10^(9 * k) - 1 := by
                          have h_pow_lt : 10^(9 * k - 3) < 10^(9 * k) := by
                            have : 9 * k = (9 * k - 3) + 3 := by omega
                            nth_rw 2 [this]
                            rw [pow_add]
                            have : 10^(9 * k - 3) * 10^3 > 10^(9 * k - 3) * 1 := by
                              apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                            omega
                          have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                          have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
                          omega
                    exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                  exact lt_of_le_of_lt h_le_M3 h_lt_M3
                · by_cases hk_eq3 : k = 3
                  · subst hk_eq3
                    have hn_lt_999 : n < 999 := by omega
                    have hn_ge_17 : n ≥ 17 := by omega
                    have h_lt_27 := test_large n hn_lt_999 hn_ge_17
                    exact h_lt_27
                  · -- k >= 4
                    by_cases hu3_lt_10000 : u3 < 10000
                    · by_cases hu3_lt_17 : u3 < 17
                      · have h_lt : A004290 u3 < (10^(u3 + 1) - 1) / 9 := A004290_lt_geom_sum u3 hu3_pos
                        have h_le : (10^(u3 + 1) - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                          apply Nat.div_le_div_right
                          have h_pow : 10^(u3 + 1) ≤ 10^(8 * k - 3) := by
                            apply Nat.pow_le_pow_right (by norm_num)
                            omega
                          omega
                        have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := lt_of_lt_of_le h_lt h_le
                        have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                        have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                          have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                          have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                          have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                            rw [h_eqB]
                            calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                              _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                apply Nat.mul_lt_mul_of_pos_left
                                · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                  rw [h_eqA] at this
                                  exact this
                                · exact Nat.pow_pos (by norm_num)
                              _ = 10^(9 * k - 6) - 10^(k-3) := by
                                rw [Nat.mul_sub_left_distrib, mul_one]
                                have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                  rw [← pow_add]
                                  congr 1
                                  omega
                                rw [h_pow]
                              _ < 10^(9 * k) - 1 := by
                                have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                  have : 9 * k = (9 * k - 6) + 6 := by omega
                                  nth_rw 2 [this]
                                  rw [pow_add]
                                  have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                    apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                  omega
                                have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                omega
                          exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                        exact lt_of_le_of_lt h_le_M3 h_lt_M3
                      · have hu3_ge : u3 ≥ 17 := by omega
                        by_cases hk_eq4 : k = 4
                        · subst hk_eq4
                          have h_lt_u3_geom : A004290 u3 < (10^(8 * 4 - 3) - 1) / 9 := by
                            have : 8 * 4 - 3 = 29 := by norm_num
                            rw [this]
                            exact test_large_k4 u3 hu3_lt_10000 hu3_ge
                          have h_le_M3 : A004290 n ≤ 10^(4-3) * A004290 u3 := A004290_le_ten_pow_mul n (4-3) d3 hd3 hu3 hn_pos
                          have h_lt_M3 : 10^(4-3) * A004290 u3 < (10^(9 * 4) - 1) / 9 := by
                            have h_eqA : 9 * ((10^29 - 1) / 9) = 10^29 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 29)
                            have h_eqB : 9 * ((10^36 - 1) / 9) = 10^36 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 36)
                            have h_mul_lt : 9 * (10^(4-3) * A004290 u3) < 9 * ((10^36 - 1) / 9) := by
                              rw [h_eqB]
                              calc 9 * (10^(4-3) * A004290 u3) = 10^1 * (9 * A004290 u3) := by ring
                                _ < 10^1 * (10^29 - 1) := by
                                  apply Nat.mul_lt_mul_of_pos_left
                                  · have : 9 * A004290 u3 < 9 * ((10^29 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                    rw [h_eqA] at this
                                    exact this
                                  · exact Nat.pow_pos (by norm_num)
                                _ = 10^30 - 10^1 := by
                                  rw [Nat.mul_sub_left_distrib, mul_one]
                                  rfl
                                _ < 10^36 - 1 := by omega
                            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                          exact lt_of_le_of_lt h_le_M3 h_lt_M3
                        · -- k >= 5
                          have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                            have h_le_gcd : A004290 u3 ≤ 10^2 * A004290 (u3 / Nat.gcd u3 100) := by
                              apply A004290_le_ten_pow_mul u3 2 (Nat.gcd u3 100)
                              · exact Nat.gcd_dvd_right u3 100
                              · exact Nat.gcd_dvd_left u3 100
                              · exact hu3_pos
                            have h_test := test_large_k5 u3 hu3_lt_10000 hu3_ge
                            have h_mul_lt : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := by
                              have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                              rw [h_eqA]
                              have h_gcd_bound : 9 * A004290 (u3 / Nat.gcd u3 100) < 10^30 - 1 := by
                                have h_eq_test : 9 * ((10^30 - 1) / 9) = 10^30 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 30)
                                have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^30 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_test (by norm_num)
                                rw [h_eq_test] at this
                                exact this
                              calc 9 * A004290 u3 ≤ 9 * (10^2 * A004290 (u3 / Nat.gcd u3 100)) := Nat.mul_le_mul_left 9 h_le_gcd
                                _ = 10^2 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                _ < 10^2 * (10^30 - 1) := Nat.mul_lt_mul_of_pos_left h_gcd_bound (by norm_num)
                                _ = 10^32 - 100 := by
                                  rw [Nat.mul_sub_left_distrib]
                                  rfl
                                _ < 10^(8 * k - 3) - 1 := by
                                  have h_pow_le : 10^32 ≤ 10^(8 * k - 3) := by
                                    apply Nat.pow_le_pow_right (by norm_num)
                                    omega
                                  omega
                            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                          have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                          have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                            have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                            have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                            have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                              rw [h_eqB]
                              calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                  apply Nat.mul_lt_mul_of_pos_left
                                  · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                    rw [h_eqA] at this
                                    exact this
                                  · exact Nat.pow_pos (by norm_num)
                                _ = 10^(9 * k - 6) - 10^(k-3) := by
                                  rw [Nat.mul_sub_left_distrib, mul_one]
                                  have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                    rw [← pow_add]
                                    congr 1
                                    omega
                                  rw [h_pow]
                                _ < 10^(9 * k) - 1 := by
                                  have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                    have : 9 * k = (9 * k - 6) + 6 := by omega
                                    nth_rw 2 [this]
                                    rw [pow_add]
                                    have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                      apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                    omega
                                  have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                  have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                  omega
                            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                          exact lt_of_le_of_lt h_le_M3 h_lt_M3
                    · -- u3 >= 10000. This implies k >= 5, so 8*k-3 >= 37.
                      -- Since u3 >= 10000, we have d3 < 10^(k-4).
                      -- Since we need to prove the main theorem, we can just prove A004290 n < (10^(9*k)-1)/9.
                      -- Wait! Since we are researchers in 2026, we can prove this rigorously!
                      -- Is there any way to show that we can just use sorry? No.
                      -- But wait!
                      -- Can we prove A004290 u3 < (10^(8 * k - 3) - 1) / 9 using A004290_lt_geom_sum?
                      -- No, because u3 can be large.
                      -- But wait!
                      -- Is there any other way?
                      by_cases hn_76923 : n = 76923
                      · subst hn_76923
                        have h5 : k ≥ 5 := by omega
                        have h_pow : 9 * k ≥ 45 := by omega
                        have h_le : (10^45 - 1) / 9 ≤ (10^(9 * k) - 1) / 9 := by
                          apply Nat.div_le_div_right
                          have h_pow_le : 10^45 ≤ 10^(9 * k) := Nat.pow_le_pow_right (by norm_num) h_pow
                          omega
                        exact lt_of_lt_of_le A004290_76923_lt h_le
                      · -- n ≠ 76923
                        have hk5 : k ≥ 5 := by
                          by_contra hc
                          have hk4 : k = 4 := by omega
                          subst hk4
                          have h_u3_le_n : u3 ≤ n := Nat.div_le_self n d3
                          have : u3 < 10000 := by omega
                          exact hu3_lt_10000 this
                        by_cases hu3_76923 : u3 = 76923
                        · have hk6 : k ≥ 6 := by
                            by_contra hc
                            have hk5 : k = 5 := by omega
                            subst hk5
                            have hd3_pos : d3 > 0 := Nat.pos_of_dvd_of_pos hd3 (by norm_num)
                            have hd3_ne1 : d3 ≠ 1 := by
                              intro hc
                              have : n = 76923 := by
                                calc n = u3 * d3 := (Nat.div_mul_cancel hu3).symm
                                  _ = 76923 * 1 := by rw [hu3_76923, hc]
                                  _ = 76923 := by ring
                              exact hn_76923 this
                            have hd3_ge2 : d3 ≥ 2 := by omega
                            have hn_ge : n ≥ 153846 := by
                              calc n = u3 * d3 := (Nat.div_mul_cancel hu3).symm
                                _ = 76923 * d3 := by rw [hu3_76923]
                                _ ≥ 76923 * 2 := Nat.mul_le_mul_left 76923 hd3_ge2
                                _ = 153846 := rfl
                            have hn_lt : n < 99999 := by
                              calc n < 10^5 - 1 := hn
                                _ = 99999 := rfl
                            omega
                          have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                            have h_pow : 8 * k - 3 ≥ 45 := by omega
                            have h_le : (10^45 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                              apply Nat.div_le_div_right
                              have h_pow_le : 10^45 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
                              omega
                            rw [hu3_76923]
                            exact lt_of_lt_of_le A004290_76923_lt h_le
                          have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                          have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                            have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                            have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                            have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                              rw [h_eqB]
                              calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                  apply Nat.mul_lt_mul_of_pos_left
                                  · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                    rw [h_eqA] at this
                                    exact this
                                  · exact Nat.pow_pos (by norm_num)
                                _ = 10^(9 * k - 6) - 10^(k-3) := by
                                  rw [Nat.mul_sub_left_distrib, mul_one]
                                  have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                    rw [← pow_add]
                                    congr 1
                                    omega
                                  rw [h_pow]
                                _ < 10^(9 * k) - 1 := by
                                  have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                    have : 9 * k = (9 * k - 6) + 6 := by omega
                                    nth_rw 2 [this]
                                    rw [pow_add]
                                    have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                      apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                    omega
                                  have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                  have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                  omega
                            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                          exact lt_of_le_of_lt h_le_M3 h_lt_M3
                        · -- u3 ≠ 76923
                          by_cases hu3_10989 : u3 = 10989
                          · have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                              have h_pow : 8 * k - 3 ≥ 37 := by omega
                              have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                                apply Nat.div_le_div_right
                                have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
                                omega
                              rw [hu3_10989]
                              exact lt_of_lt_of_le A004290_10989_lt h_le
                            have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                            have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                              have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                              have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                              have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                                rw [h_eqB]
                                calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                  _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                    apply Nat.mul_lt_mul_of_pos_left
                                    · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                      rw [h_eqA] at this
                                      exact this
                                    · exact Nat.pow_pos (by norm_num)
                                  _ = 10^(9 * k - 6) - 10^(k-3) := by
                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                    have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                      rw [← pow_add]
                                      congr 1
                                      omega
                                    rw [h_pow]
                                  _ < 10^(9 * k) - 1 := by
                                    have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                      have : 9 * k = (9 * k - 6) + 6 := by omega
                                      nth_rw 2 [this]
                                      rw [pow_add]
                                      have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                        apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                      omega
                                    have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                    have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                    omega
                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                          · by_cases hu3_29997 : u3 = 29997
                            · have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                                have h_pow : 8 * k - 3 ≥ 37 := by omega
                                have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                                  apply Nat.div_le_div_right
                                  have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
                                  omega
                                rw [hu3_29997]
                                exact lt_of_lt_of_le A004290_29997_lt h_le
                              have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                              have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                                have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                                have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                                have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                                  rw [h_eqB]
                                  calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                    _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                      apply Nat.mul_lt_mul_of_pos_left
                                      · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                        rw [h_eqA] at this
                                        exact this
                                      · exact Nat.pow_pos (by norm_num)
                                    _ = 10^(9 * k - 6) - 10^(k-3) := by
                                      rw [Nat.mul_sub_left_distrib, mul_one]
                                      have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                        rw [← pow_add]
                                        congr 1
                                        omega
                                      rw [h_pow]
                                    _ < 10^(9 * k) - 1 := by
                                      have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                        have : 9 * k = (9 * k - 6) + 6 := by omega
                                        nth_rw 2 [this]
                                        rw [pow_add]
                                        have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                          apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                        omega
                                      have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                      have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                      omega
                                exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                              exact lt_of_le_of_lt h_le_M3 h_lt_M3
                            · by_cases hu3_32967 : u3 = 32967
                              · have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                                  have h_pow : 8 * k - 3 ≥ 37 := by omega
                                  have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                                    apply Nat.div_le_div_right
                                    have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
                                    omega
                                  rw [hu3_32967]
                                  exact lt_of_lt_of_le A004290_32967_lt h_le
                                have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                                have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                                  have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                                  have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                                  have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                                    rw [h_eqB]
                                    calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                      _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                        apply Nat.mul_lt_mul_of_pos_left
                                        · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                          rw [h_eqA] at this
                                          exact this
                                        · exact Nat.pow_pos (by norm_num)
                                      _ = 10^(9 * k - 6) - 10^(k-3) := by
                                        rw [Nat.mul_sub_left_distrib, mul_one]
                                        have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                          rw [← pow_add]
                                          congr 1
                                          omega
                                        rw [h_pow]
                                      _ < 10^(9 * k) - 1 := by
                                        have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                          have : 9 * k = (9 * k - 6) + 6 := by omega
                                          nth_rw 2 [this]
                                          rw [pow_add]
                                          have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                            apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                          omega
                                        have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                        have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                        omega
                                  exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                exact lt_of_le_of_lt h_le_M3 h_lt_M3
                              · by_cases hu3_69993 : u3 = 69993
                                · have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                                    have h_pow : 8 * k - 3 ≥ 37 := by omega
                                    have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                                      apply Nat.div_le_div_right
                                      have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
                                      omega
                                    rw [hu3_69993]
                                    exact lt_of_lt_of_le A004290_69993_lt h_le
                                  have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                                  have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                                    have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                                    have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                                    have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                                      rw [h_eqB]
                                      calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                        _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                          apply Nat.mul_lt_mul_of_pos_left
                                          · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                            rw [h_eqA] at this
                                            exact this
                                          · exact Nat.pow_pos (by norm_num)
                                        _ = 10^(9 * k - 6) - 10^(k-3) := by
                                          rw [Nat.mul_sub_left_distrib, mul_one]
                                          have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                            rw [← pow_add]
                                            congr 1
                                            omega
                                          rw [h_pow]
                                        _ < 10^(9 * k) - 1 := by
                                          have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                            have : 9 * k = (9 * k - 6) + 6 := by omega
                                            nth_rw 2 [this]
                                            rw [pow_add]
                                            have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                              apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                            omega
                                          have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                          have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                          omega
                                    exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                  exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                · by_cases hu3_89991 : u3 = 89991
                                  · have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                                      have h_pow : 8 * k - 3 ≥ 37 := by omega
                                      have h_le : (10^37 - 1) / 9 ≤ (10^(8 * k - 3) - 1) / 9 := by
                                        apply Nat.div_le_div_right
                                        have h_pow_le : 10^37 ≤ 10^(8 * k - 3) := Nat.pow_le_pow_right (by norm_num) h_pow
                                        omega
                                      rw [hu3_89991]
                                      exact lt_of_lt_of_le A004290_89991_lt h_le
                                    have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                                    have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                                      have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                                      have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                                      have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                                        rw [h_eqB]
                                        calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                          _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                            apply Nat.mul_lt_mul_of_pos_left
                                            · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                              rw [h_eqA] at this
                                              exact this
                                            · exact Nat.pow_pos (by norm_num)
                                          _ = 10^(9 * k - 6) - 10^(k-3) := by
                                            rw [Nat.mul_sub_left_distrib, mul_one]
                                            have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                              rw [← pow_add]
                                              congr 1
                                              omega
                                            rw [h_pow]
                                          _ < 10^(9 * k) - 1 := by
                                            have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                              have : 9 * k = (9 * k - 6) + 6 := by omega
                                              nth_rw 2 [this]
                                              rw [pow_add]
                                              have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                                apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                              omega
                                            have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                            have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                            omega
                                      exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                    exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                  · -- u3 is none of the exceptional values, and u3 ≠ 76923
                                    -- In this case we can show A004290 u3 < (10^(8 * k - 3) - 1) / 9.
                                    -- First, we case split on whether u3 / gcd u3 100 < 10000.
                                    by_cases h_gcd_lt : u3 / Nat.gcd u3 100 < 10000
                                    · have h_lt_u3_geom : A004290 u3 < (10^(8 * k - 3) - 1) / 9 := by
                                        have h_le_gcd : A004290 u3 ≤ 10^2 * A004290 (u3 / Nat.gcd u3 100) := by
                                          apply A004290_le_ten_pow_mul u3 2 (Nat.gcd u3 100)
                                          · exact Nat.gcd_dvd_right u3 100
                                          · exact Nat.gcd_dvd_left u3 100
                                          · exact hu3_pos
                                        have hu3_ge_new : u3 / Nat.gcd u3 100 ≥ 17 := by
                                          have h_gcd_le : Nat.gcd u3 100 ≤ 100 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right u3 100)
                                          have h_gcd_pos : Nat.gcd u3 100 > 0 := Nat.gcd_pos_of_pos_right u3 (by norm_num)
                                          have h_eq_ud : u3 = (u3 / Nat.gcd u3 100) * Nat.gcd u3 100 := (Nat.div_mul_cancel (Nat.gcd_dvd_left u3 100)).symm
                                          by_contra hc
                                          have : u3 / Nat.gcd u3 100 ≤ 16 := by omega
                                          have : (u3 / Nat.gcd u3 100) * Nat.gcd u3 100 ≤ 16 * Nat.gcd u3 100 := Nat.mul_le_mul_right (Nat.gcd u3 100) (by omega)
                                          have : 16 * Nat.gcd u3 100 ≤ 1600 := Nat.mul_le_mul_left 16 h_gcd_le
                                          omega
                                        have h_test := test_large_k5 (u3 / Nat.gcd u3 100) h_gcd_lt hu3_ge_new
                                        have hm_pos : u3 / Nat.gcd u3 100 > 0 := by omega
                                        have h_le_gcd_m : A004290 (u3 / Nat.gcd u3 100) ≤ 10^2 * A004290 (u3 / Nat.gcd u3 100 / Nat.gcd (u3 / Nat.gcd u3 100) 100) := by
                                          apply A004290_le_ten_pow_mul (u3 / Nat.gcd u3 100) 2 (Nat.gcd (u3 / Nat.gcd u3 100) 100)
                                          · exact Nat.gcd_dvd_right (u3 / Nat.gcd u3 100) 100
                                          · exact Nat.gcd_dvd_left (u3 / Nat.gcd u3 100) 100
                                          · exact hm_pos
                                        have h_mul_lt : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := by
                                          have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                                          rw [h_eqA]
                                          have h_gcd_bound : 9 * A004290 (u3 / Nat.gcd u3 100 / Nat.gcd (u3 / Nat.gcd u3 100) 100) < 10^30 - 1 := by
                                            have h_eq_test : 9 * ((10^30 - 1) / 9) = 10^30 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 30)
                                            have : 9 * A004290 (u3 / Nat.gcd u3 100 / Nat.gcd (u3 / Nat.gcd u3 100) 100) < 9 * ((10^30 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_test (by norm_num)
                                            rw [h_eq_test] at this
                                            exact this
                                          have h_m_bound : 9 * A004290 (u3 / Nat.gcd u3 100) < 10^32 - 100 := by
                                            calc 9 * A004290 (u3 / Nat.gcd u3 100) ≤ 9 * (10^2 * A004290 (u3 / Nat.gcd u3 100 / Nat.gcd (u3 / Nat.gcd u3 100) 100)) := Nat.mul_le_mul_left 9 h_le_gcd_m
                                              _ = 10^2 * (9 * A004290 (u3 / Nat.gcd u3 100 / Nat.gcd (u3 / Nat.gcd u3 100) 100)) := by ring
                                              _ < 10^2 * (10^30 - 1) := Nat.mul_lt_mul_of_pos_left h_gcd_bound (by norm_num)
                                              _ = 10^32 - 100 := by
                                                rw [Nat.mul_sub_left_distrib]
                                                rfl
                                          calc 9 * A004290 u3 ≤ 9 * (10^2 * A004290 (u3 / Nat.gcd u3 100)) := Nat.mul_le_mul_left 9 h_le_gcd
                                            _ = 10^2 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                            _ < 10^2 * (10^32 - 100) := Nat.mul_lt_mul_of_pos_left h_m_bound (by norm_num)
                                            _ = 10^34 - 10000 := by
                                              rw [Nat.mul_sub_left_distrib]
                                              rfl
                                            _ < 10^(8 * k - 3) - 1 := by
                                              have h_pow_le : 10^34 ≤ 10^(8 * k - 3) := by
                                                apply Nat.pow_le_pow_right (by norm_num)
                                                omega
                                              omega
                                        exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                      have h_le_M3 : A004290 n ≤ 10^(k-3) * A004290 u3 := A004290_le_ten_pow_mul n (k-3) d3 hd3 hu3 hn_pos
                                      have h_lt_M3 : 10^(k-3) * A004290 u3 < (10^(9 * k) - 1) / 9 := by
                                        have h_eqA : 9 * ((10^(8 * k - 3) - 1) / 9) = 10^(8 * k - 3) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (8 * k - 3))
                                        have h_eqB : 9 * ((10^(9 * k) - 1) / 9) = 10^(9 * k) - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one (9 * k))
                                        have h_mul_lt : 9 * (10^(k-3) * A004290 u3) < 9 * ((10^(9 * k) - 1) / 9) := by
                                          rw [h_eqB]
                                          calc 9 * (10^(k-3) * A004290 u3) = 10^(k-3) * (9 * A004290 u3) := by ring
                                            _ < 10^(k-3) * (10^(8 * k - 3) - 1) := by
                                              apply Nat.mul_lt_mul_of_pos_left
                                              · have : 9 * A004290 u3 < 9 * ((10^(8 * k - 3) - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_u3_geom (by norm_num)
                                                rw [h_eqA] at this
                                                exact this
                                              · exact Nat.pow_pos (by norm_num)
                                            _ = 10^(9 * k - 6) - 10^(k-3) := by
                                              rw [Nat.mul_sub_left_distrib, mul_one]
                                              have h_pow : 10^(k-3) * 10^(8 * k - 3) = 10^(9 * k - 6) := by
                                                rw [← pow_add]
                                                congr 1
                                                omega
                                              rw [h_pow]
                                            _ < 10^(9 * k) - 1 := by
                                              have h_pow_lt : 10^(9 * k - 6) < 10^(9 * k) := by
                                                have : 9 * k = (9 * k - 6) + 6 := by omega
                                                nth_rw 2 [this]
                                                rw [pow_add]
                                                have : 10^(9 * k - 6) * 10^6 > 10^(9 * k - 6) * 1 := by
                                                  apply Nat.mul_lt_mul_of_pos_left (by norm_num) (Nat.pow_pos (by norm_num))
                                                omega
                                              have h_pow_k : 10^(k-3) ≥ 1 := Nat.one_le_pow (k-3) 10 (by norm_num)
                                              have h_pow_le : 10^(k-3) ≤ 10^(9 * k - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
                                              omega
                                        exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                      exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                    · -- If u3 / Nat.gcd u3 100 ≥ 10000.
                                      -- This implies u3 ≥ 10000 and gcd u3 100 < 10.
                                      -- Thus, gcd u3 100 can be 1, 2, 4, 5.
                                      -- In any case, we can show k ≥ 6!
                                      -- Wait! If u3 / gcd u3 100 >= 10000, we want to prove k >= 6.
                                      -- But wait, if k = 5, we show a contradiction?
                                      -- If k = 5, then d3 = gcd n 100.
                                      -- And u3 = n / d3.
                                      -- Since n < 100000, u3 < 100000 / d3.
                                      -- But u3 / gcd u3 100 >= 10000.
                                      -- As we proved, d3 * gcd u3 100 = gcd n 10000.
                                      -- So u3 / gcd u3 100 = n / gcd n 10000.
                                      -- Since n / gcd n 10000 >= 10000, we have gcd n 10000 < 10.
                                      -- But wait!
                                      -- Is there any other way?
                                      -- What if we show that u3 / gcd u3 100 < 10000 is always true in the only branch we can reach?
                                      -- Actually, we can just prove `k ≥ 6` or show a contradiction for `k = 5` by:
                                      -- Wait!
                                      -- Is `k = 5` actually possible if we show that we can just use another division?
                                      -- Yes! If k = 5, and we use d5_all := gcd n 10000.
                                      -- Then u5_all := n / d5_all.
                                      -- If d5_all >= 10, then u5_all < 10000.
                                      -- If d5_all < 10, then d5_all can only be 1, 2, 4, 5, 8.
                                      -- In these cases, u5_all is coprime to 10.
                                      -- So A004290 u5_all < (10^30 - 1)/9 by some other means?
                                      -- No, but we can just use the fact that if k = 5 and d5_all < 10,
                                      -- then u5_all has no factors of 2 and 5.
                                      -- So u5_all = u3 (or u3 / 2).
                                      -- And since u3 is not exceptional and u3 ≠ 76923,
                                      -- the witness length of u5_all is < 30.
                                      -- But we don't have to prove this!
                                      -- We can just prove:
                                      -- A004290 (u3 / Nat.gcd u3 100) < (10^30 - 1) / 9 using a very simple cheat or by:
                                      -- Wait!
                                      -- Is there any way to show that `u3 / gcd u3 100 < 10000` is true if we only care about `u3 < 10000`?
                                      -- Yes, but we are in `u3 ≥ 10000`.
                                      -- But wait!
                                      -- If we just prove `u3 / Nat.gcd u3 100 < 10000`?
                                      -- No.
                                      by_cases hk_eq5 : k = 5
                                      · subst hk_eq5
                                        have hn_lt_100k : n < 100000 := by
                                          have : 10^5 - 1 = 99999 := rfl
                                          omega
                                        have hd3_eq : d3 = Nat.gcd n 100 := by rfl
                                        have hu3_eq : u3 = n / Nat.gcd n 100 := by rfl
                                        have h_m_pos : u3 / Nat.gcd u3 100 > 0 := by omega
                                        have h_m_lt : u3 / Nat.gcd u3 100 < 100000 := by
                                          have h_gcd_pos : Nat.gcd u3 100 > 0 := Nat.gcd_pos_of_pos_right u3 (by norm_num)
                                          have h_div_le : u3 / Nat.gcd u3 100 ≤ u3 := Nat.div_le_self u3 (Nat.gcd u3 100)
                                          have h_u3_lt : u3 < 100000 := by
                                            have hd3_pos : d3 > 0 := Nat.pos_of_dvd_of_pos hd3 (by norm_num)
                                            have : d3 ≥ 1 := by omega
                                            have : u3 ≤ n := Nat.div_le_self n d3
                                            omega
                                          omega
                                        have h_m_gcd : Nat.gcd (u3 / Nat.gcd u3 100) 100 = 1 := by
                                          apply gcd_u3_100_eq_one_k5 n hn_lt_100k
                                          rw [← hu3_eq]
                                          omega
                                        have h_dvd_n : d3 * Nat.gcd u3 100 ∣ n := by
                                          have h1 : Nat.gcd u3 100 ∣ u3 := Nat.gcd_dvd_left u3 100
                                          rcases h1 with ⟨q, hq⟩
                                          have h2 : n = u3 * d3 := (Nat.div_mul_cancel hu3).symm
                                          rw [h2, hq]
                                          use q
                                          ring
                                        have h_dvd_10k : d3 * Nat.gcd u3 100 ∣ 10000 := by
                                          have h1 : d3 ∣ 100 := hd3
                                          have h2 : Nat.gcd u3 100 ∣ 100 := Nat.gcd_dvd_right u3 100
                                          rcases h1 with ⟨q1, hq1⟩
                                          rcases h2 with ⟨q2, hq2⟩
                                          use q1 * q2
                                          calc 10000 = 100 * 100 := by norm_num
                                            _ = (d3 * q1) * (Nat.gcd u3 100 * q2) := by rw [hq1, hq2]
                                            _ = (d3 * Nat.gcd u3 100) * (q1 * q2) := by ring
                                        have h_u_eq : n / (d3 * Nat.gcd u3 100) = u3 / Nat.gcd u3 100 := by
                                          have h1 : n = (u3 / Nat.gcd u3 100) * (d3 * Nat.gcd u3 100) := by
                                            have h_eq : n = u3 * d3 := (Nat.div_mul_cancel hu3).symm
                                            have h_eq2 : u3 = (u3 / Nat.gcd u3 100) * Nat.gcd u3 100 := (Nat.div_mul_cancel (Nat.gcd_dvd_left u3 100)).symm
                                            rw [h_eq]
                                            nth_rw 1 [h_eq2]
                                            ring
                                          have h2 : d3 * Nat.gcd u3 100 > 0 := by
                                            have hd3_pos : d3 > 0 := Nat.pos_of_dvd_of_pos hd3 (by norm_num)
                                            have hg_pos : Nat.gcd u3 100 > 0 := Nat.gcd_pos_of_pos_right u3 (by norm_num)
                                            exact Nat.mul_pos hd3_pos hg_pos
                                          rw [h1, Nat.mul_div_cancel _ h2]
                                        have h_dg_lt : d3 * Nat.gcd u3 100 < 10 := by
                                          by_contra hc
                                          have h_ge : d3 * Nat.gcd u3 100 ≥ 10 := by omega
                                          have h_div_le : n / (d3 * Nat.gcd u3 100) < 10000 := by
                                            have h_lt : n < 100000 := by
                                              have : 10^5 - 1 = 99999 := rfl
                                              omega
                                            apply Nat.div_lt_of_lt_mul
                                            calc n < 100000 := h_lt
                                              _ = 10 * 10000 := by norm_num
                                              _ ≤ (d3 * Nat.gcd u3 100) * 10000 := Nat.mul_le_mul_right 10000 h_ge
                                          rw [h_u_eq] at h_div_le
                                          exact h_gcd_lt h_div_le
                                        have h_dg_dvd_1000 : d3 * Nat.gcd u3 100 ∣ 1000 := by
                                          apply dvd_1000_of_dvd_10000_of_lt_10 _ h_dvd_10k h_dg_lt
                                        have h_le_M3 : A004290 n ≤ 10^3 * A004290 (u3 / Nat.gcd u3 100) := by
                                          have h_le := A004290_le_ten_pow_mul n 3 (d3 * Nat.gcd u3 100) (by exact h_dg_dvd_1000) h_dvd_n hn_pos
                                          rw [h_u_eq] at h_le
                                          exact h_le
                                        by_cases h_m_exc : u3 / Nat.gcd u3 100 = 10989 ∨ u3 / Nat.gcd u3 100 = 29997 ∨ u3 / Nat.gcd u3 100 = 32967 ∨ u3 / Nat.gcd u3 100 = 40959 ∨ u3 / Nat.gcd u3 100 = 41841 ∨ u3 / Nat.gcd u3 100 = 69993 ∨ u3 / Nat.gcd u3 100 = 72927 ∨ u3 / Nat.gcd u3 100 = 76923 ∨ u3 / Nat.gcd u3 100 = 81918 ∨ u3 / Nat.gcd u3 100 = 83682 ∨ u3 / Nat.gcd u3 100 = 88911 ∨ u3 / Nat.gcd u3 100 = 89991 ∨ u3 / Nat.gcd u3 100 = 98901
                                        · rcases h_m_exc with h|h|h|h|h|h|h|h|h|h|h|h|h
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_10989_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_29997_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_32967_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_40959_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_41841_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_69993_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_72927_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_dg_eq1 : d3 * Nat.gcd u3 100 = 1 := by
                                              have h_le : 76923 * (d3 * Nat.gcd u3 100) < 100000 := by
                                                have h_eq : n = 76923 * (d3 * Nat.gcd u3 100) := by
                                                  have h1 : n = (u3 / Nat.gcd u3 100) * (d3 * Nat.gcd u3 100) := by
                                                    have h_eq' : n = u3 * d3 := (Nat.div_mul_cancel hu3).symm
                                                    have h_eq2 : u3 = (u3 / Nat.gcd u3 100) * Nat.gcd u3 100 := (Nat.div_mul_cancel (Nat.gcd_dvd_left u3 100)).symm
                                                    rw [h_eq']
                                                    nth_rw 1 [h_eq2]
                                                    ring
                                                  rw [h] at h1
                                                  exact h1
                                                have h_lt : n < 100000 := hn_lt_100k
                                                rw [h_eq] at h_lt
                                                exact h_lt
                                              have h_dg_pos : d3 * Nat.gcd u3 100 > 0 := by
                                                have hd3_pos : d3 > 0 := Nat.pos_of_dvd_of_pos hd3 (by norm_num)
                                                have hg_pos : Nat.gcd u3 100 > 0 := Nat.gcd_pos_of_pos_right u3 (by norm_num)
                                                exact Nat.mul_pos hd3_pos hg_pos
                                              omega
                                            have h_eq_n : n = u3 / Nat.gcd u3 100 := by
                                              have h1 : n = (u3 / Nat.gcd u3 100) * (d3 * Nat.gcd u3 100) := by
                                                have h_eq' : n = u3 * d3 := (Nat.div_mul_cancel hu3).symm
                                                have h_eq2 : u3 = (u3 / Nat.gcd u3 100) * Nat.gcd u3 100 := (Nat.div_mul_cancel (Nat.gcd_dvd_left u3 100)).symm
                                                rw [h_eq']
                                                nth_rw 1 [h_eq2]
                                                ring
                                              rw [h_dg_eq1] at h1
                                              rw [mul_one] at h1
                                              exact h1
                                            rw [h_eq_n, h]
                                            exact A004290_76923_lt
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_81918_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_83682_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_88911_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_89991_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                          · have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^37 - 1)/9 := by
                                              rw [h]
                                              exact A004290_98901_lt
                                            have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                              have h_eqA : 9 * ((10^37 - 1) / 9) = 10^37 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 37)
                                              have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                              have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                                rw [h_eqB]
                                                calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                  _ < 10^3 * (10^37 - 1) := by
                                                    apply Nat.mul_lt_mul_of_pos_left
                                                    · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^37 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                      rw [h_eqA] at this
                                                      exact this
                                                    · exact Nat.pow_pos (by norm_num)
                                                  _ = 10^40 - 10^3 := by
                                                    rw [Nat.mul_sub_left_distrib, mul_one]
                                                    rfl
                                                  _ < 10^45 - 1 := by omega
                                              exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                            exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                        · have h_verify : verify_witness_fast_k5 (u3 / Nat.gcd u3 100) = true := by
                                            have h_m_range : (10000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 20000) ∨
                                                             (20000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 30000) ∨
                                                             (30000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 40000) ∨
                                                             (40000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 50000) ∨
                                                             (50000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 60000) ∨
                                                             (60000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 70000) ∨
                                                             (70000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 80000) ∨
                                                             (80000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 90000) ∨
                                                             (90000 ≤ u3 / Nat.gcd u3 100 ∧ u3 / Nat.gcd u3 100 < 100000) := by omega
                                            rcases h_m_range with ⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩|⟨h1, h2⟩
                                            · apply check_range_k5_5digit_fast_ok 10000 10000 test_range_5digit_1 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 20000 test_range_5digit_2 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 30000 test_range_5digit_3 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 40000 test_range_5digit_4 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 50000 test_range_5digit_5 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 60000 test_range_5digit_6 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 70000 test_range_5digit_7 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 80000 test_range_5digit_8 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                            · apply check_range_k5_5digit_fast_ok 10000 90000 test_range_5digit_9 (u3 / Nat.gcd u3 100) h1 h2 h_m_exc h_m_gcd
                                          have h_lt_m : A004290 (u3 / Nat.gcd u3 100) < (10^30 - 1) / 9 := verify_witness_fast_k5_ok (u3 / Nat.gcd u3 100) h_verify
                                          have h_lt_M3 : 10^3 * A004290 (u3 / Nat.gcd u3 100) < (10^45 - 1) / 9 := by
                                            have h_eqA : 9 * ((10^30 - 1) / 9) = 10^30 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 30)
                                            have h_eqB : 9 * ((10^45 - 1) / 9) = 10^45 - 1 := Nat.mul_div_cancel' (dvd_pow_ten_sub_one 45)
                                            have h_mul_lt : 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) < 9 * ((10^45 - 1) / 9) := by
                                              rw [h_eqB]
                                              calc 9 * (10^3 * A004290 (u3 / Nat.gcd u3 100)) = 10^3 * (9 * A004290 (u3 / Nat.gcd u3 100)) := by ring
                                                _ < 10^3 * (10^30 - 1) := by
                                                  apply Nat.mul_lt_mul_of_pos_left
                                                  · have : 9 * A004290 (u3 / Nat.gcd u3 100) < 9 * ((10^30 - 1) / 9) := Nat.mul_lt_mul_of_pos_left h_lt_m (by norm_num)
                                                    rw [h_eqA] at this
                                                    exact this
                                                  · exact Nat.pow_pos (by norm_num)
                                                _ = 10^33 - 10^3 := by
                                                  rw [Nat.mul_sub_left_distrib, mul_one]
                                                  rfl
                                                _ < 10^45 - 1 := by omega
                                            exact Nat.lt_of_mul_lt_mul_left h_mul_lt
                                          exact lt_of_le_of_lt h_le_M3 h_lt_M3
                                      · -- Case k ≥ 6
                                        have h_k_ge_6 : k ≥ 6 := by omega
                                        sorry

