import Mathlib
open Nat Finset



lemma padicValNat_le (x p : ℕ) (hx : x > 0) (hp : p > 1) : padicValNat p x ≤ x := by
  have h1 : p ^ (padicValNat p x) ∣ x := pow_padicValNat_dvd
  have h2 : p ^ (padicValNat p x) ≤ x := Nat.le_of_dvd hx h1
  have h3 : padicValNat p x < p ^ (padicValNat p x) := Nat.lt_pow_self hp
  omega

lemma sum_indicator_eq (x k : ℕ) (hk : k ≤ x) (f : ℕ → ℕ)
    (hf1 : ∀ j ∈ Icc 1 k, f j = 1)
    (hf2 : ∀ j ∈ Icc (k + 1) x, f j = 0) :
    ∑ j ∈ Icc 1 x, f j = k := by
  have h_split : Icc 1 x = Icc 1 k ∪ Icc (k + 1) x := by
    ext a
    simp only [mem_union, mem_Icc]
    omega
  have h_disj : Disjoint (Icc 1 k) (Icc (k + 1) x) := by
    rw [disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_Icc] at ha hb
    omega
  rw [h_split, sum_union h_disj]
  have sum1 : ∑ j ∈ Icc 1 k, f j = k := by
    rw [sum_congr rfl hf1]
    simp
  have sum2 : ∑ j ∈ Icc (k + 1) x, f j = 0 := by
    rw [sum_congr rfl hf2]
    simp
  rw [sum1, sum2]
  exact rfl

lemma padicValNat_eq_sum (x p : ℕ) [hp : Fact p.Prime] (hx : x > 0) :
    padicValNat p x = ∑ j ∈ Icc 1 x, (if p^j ∣ x then 1 else 0) := by
  let k := padicValNat p x
  let f := fun j => if p^j ∣ x then 1 else 0
  have h_le : k ≤ x := padicValNat_le x p hx hp.out.one_lt
  have eq_k : ∑ j ∈ Icc 1 x, f j = k := by
    apply sum_indicator_eq x k h_le f
    · intro j hj
      simp only [mem_Icc] at hj
      have hdvd : p^j ∣ x := by
        have h_pow : p^j ∣ p^k := pow_dvd_pow p hj.2
        exact dvd_trans h_pow pow_padicValNat_dvd
      simp [f, hdvd]
    · intro j hj
      simp only [mem_Icc] at hj
      have hnot : ¬ (p^j ∣ x) := by
        intro h
        have h_le_val : j ≤ k := (padicValNat_dvd_iff_le hx.ne').mp h
        omega
      simp [f, hnot]
  exact eq_k.symm

lemma padicValNat_prod (S : Finset ℕ) (f : ℕ → ℕ) (p : ℕ) [hp : Fact p.Prime]
    (hf : ∀ x ∈ S, f x ≠ 0) :
    padicValNat p (∏ x ∈ S, f x) = ∑ x ∈ S, padicValNat p (f x) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have h1 : f a ≠ 0 := hf a (mem_insert_self a s)
    have h2 : ∏ x ∈ s, f x ≠ 0 := by
      apply prod_ne_zero_iff.mpr
      intro x hx
      exact hf x (mem_insert_of_mem hx)
    rw [padicValNat.mul h1 h2]
    have hf_s : ∀ x ∈ s, f x ≠ 0 := fun x hx => hf x (mem_insert_of_mem hx)
    rw [ih hf_s]

lemma count_equiv_add (M n b inv9 y c q X : ℕ)
    (h_inv : 9 * inv9 = y * M + 1)
    (h_c : inv9 * b + c = M * q)
    (hX : X + b = 9 * n) :
    M ∣ X ↔ M ∣ n + c := by
  by_cases hM : M = 0
  · subst hM
    simp at h_inv
  · have h_zmod_X : M ∣ X ↔ (X : ZMod M) = 0 := by rw [ZMod.natCast_eq_zero_iff]
    have h_zmod_c : M ∣ n + c ↔ ((n + c : ℕ) : ZMod M) = 0 := by rw [ZMod.natCast_eq_zero_iff]
    rw [h_zmod_X, h_zmod_c]
    have e1 : (9 : ZMod M) * (inv9 : ZMod M) = 1 := by
      have : ((9 * inv9 : ℕ) : ZMod M) = ((y * M + 1 : ℕ) : ZMod M) := by rw [h_inv]
      push_cast at this
      simpa using this
    have e2 : (inv9 : ZMod M) * (b : ZMod M) + (c : ZMod M) = 0 := by
      have : ((inv9 * b + c : ℕ) : ZMod M) = ((M * q : ℕ) : ZMod M) := by rw [h_c]
      push_cast at this
      simpa using this
    have e3 : (X : ZMod M) + (b : ZMod M) = (9 : ZMod M) * (n : ZMod M) := by
      have : ((X + b : ℕ) : ZMod M) = ((9 * n : ℕ) : ZMod M) := by rw [hX]
      push_cast at this
      exact this
    constructor
    · intro hX0
      calc ((n + c : ℕ) : ZMod M)
        _ = (n : ZMod M) + (c : ZMod M) := by push_cast; rfl
        _ = (9 : ZMod M) * (inv9 : ZMod M) * (n : ZMod M) + (c : ZMod M) := by rw [e1, one_mul]
        _ = (inv9 : ZMod M) * ((9 : ZMod M) * (n : ZMod M)) + (c : ZMod M) := by ring
        _ = (inv9 : ZMod M) * ((X : ZMod M) + (b : ZMod M)) + (c : ZMod M) := by rw [← e3]
        _ = (inv9 : ZMod M) * (0 + (b : ZMod M)) + (c : ZMod M) := by rw [hX0]
        _ = (inv9 : ZMod M) * (b : ZMod M) + (c : ZMod M) := by ring
        _ = 0 := e2
    · intro hc0
      have hc : (c : ZMod M) = - (n : ZMod M) := by
        calc (c : ZMod M) = (n : ZMod M) + (c : ZMod M) - (n : ZMod M) := by ring
          _ = 0 - (n : ZMod M) := by
            have h : ((n : ZMod M) + (c : ZMod M)) = 0 := by
              have : ((n + c : ℕ) : ZMod M) = 0 := hc0
              push_cast at this
              exact this
            rw [h]
          _ = - (n : ZMod M) := by ring
      calc (X : ZMod M) = (X : ZMod M) + (b : ZMod M) - (b : ZMod M) := by ring
        _ = (9 : ZMod M) * (n : ZMod M) - (b : ZMod M) := by rw [e3]
        _ = (9 : ZMod M) * (n : ZMod M) - (9 : ZMod M) * (inv9 : ZMod M) * (b : ZMod M) := by rw [e1, one_mul]
        _ = (9 : ZMod M) * ((n : ZMod M) - (inv9 : ZMod M) * (b : ZMod M)) := by ring
        _ = (9 : ZMod M) * ((n : ZMod M) + (c : ZMod M)) := by
          have hb : (inv9 : ZMod M) * (b : ZMod M) = - (c : ZMod M) := by
            calc (inv9 : ZMod M) * (b : ZMod M) = (inv9 : ZMod M) * (b : ZMod M) + (c : ZMod M) - (c : ZMod M) := by ring
              _ = 0 - (c : ZMod M) := by rw [e2]
              _ = - (c : ZMod M) := by ring
          rw [hb, sub_neg_eq_add]
        _ = (9 : ZMod M) * 0 := by
          have h : ((n : ZMod M) + (c : ZMod M)) = 0 := by
            have : ((n + c : ℕ) : ZMod M) = 0 := hc0
            push_cast at this
            exact this
          rw [h]
        _ = 0 := mul_zero _

lemma sum_indicator_eq_div (n c M : ℕ) (hM : M > 0) (hc : c < M) :
    ∑ i ∈ Icc 1 n, (if M ∣ i + c then 1 else 0) = (n + c) / M := by
  induction n with
  | zero =>
    have : Icc 1 0 = ∅ := Icc_eq_empty (by decide)
    rw [this, sum_empty]
    have h : c / M = 0 := Nat.div_eq_of_lt hc
    have h2 : (0 + c) / M = 0 := by rw [zero_add]; exact h
    rw [h2]
  | succ n ih =>
    have : 1 ≤ n + 1 := by omega
    rw [sum_Icc_succ_top this, ih]
    have h_succ := @Nat.succ_div (n + c) M
    have eq : (n + c) + 1 = n + 1 + c := by omega
    rw [eq] at h_succ
    omega

lemma div_eq_div_add_indicator (n c M : ℕ) (hM : M > 0) (hc : c < M) :
    (n + c) / M = n / M + if n % M + c ≥ M then 1 else 0 := by
  have h1 : n + c = (n % M + c) + (n / M) * M := by
    nth_rw 1 [← Nat.div_add_mod n M]
    ring
  rw [h1]
  rw [Nat.add_mul_div_right (n % M + c) (n / M) hM]
  have h2 : n % M < M := mod_lt n hM
  have h3 : (n % M + c) / M = if n % M + c ≥ M then 1 else 0 := by
    split_ifs with h
    · have : (n % M + c) / M = 1 := by
        apply Nat.div_eq_of_lt_le
        · omega
        · omega
      exact this
    · have : (n % M + c) / M = 0 := by
        apply Nat.div_eq_of_lt
        omega
      exact this
  rw [h3]
  omega

lemma sum_indicator_equiv (n M b c : ℕ)
    (h_equiv : ∀ i ∈ Icc 1 n, M ∣ 9 * i - b ↔ M ∣ i + c) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - b then 1 else 0) =
    ∑ i ∈ Icc 1 n, (if M ∣ i + c then 1 else 0) := by
  apply sum_congr rfl
  intro i hi
  have h := h_equiv i hi
  split_ifs with h1 h2 h3 _
  · rfl
  · exfalso; exact h2 (h.mp h1)
  · exfalso; exact h1 (h.mpr h3)
  · rfl

lemma sum_comm_indicator (n M p : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 M, (if p^j ∣ f i then 1 else 0) =
    ∑ j ∈ Icc 1 M, ∑ i ∈ Icc 1 n, (if p^j ∣ f i then 1 else 0) := by
  apply sum_comm



lemma case1_ineq (K r : ℕ) (hr : r < 9 * K + 1) :
    (if r + (7 * K + 0) ≥ 9 * K + 1 then 1 else 0) +
    (if r + (5 * K + 0) ≥ 9 * K + 1 then 1 else 0) +
    (if r + (2 * K + 0) ≥ 9 * K + 1 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 1 then 1 else 0) +
    (if r + (6 * K + 0) ≥ 9 * K + 1 then 1 else 0) := by
  split_ifs <;> omega

lemma case1_witness (K : ℕ) :
    9 * (8 * K + 1) = 8 * (9 * K + 1) + 1 ∧
    (8 * K + 1) * 7 + (7 * K + 0) = (9 * K + 1) * 7 ∧
    (8 * K + 1) * 5 + (5 * K + 0) = (9 * K + 1) * 5 ∧
    (8 * K + 1) * 2 + (2 * K + 0) = (9 * K + 1) * 2 ∧
    (8 * K + 1) * 0 + 0 = (9 * K + 1) * 0 ∧
    (8 * K + 1) * 6 + (6 * K + 0) = (9 * K + 1) * 6 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case1 (n K M : ℕ) (hM : M = 9 * K + 1) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (8 * K + 1)
  have h_witness := case1_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 8 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (7 * K + 0) = M * 7 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (7 * K + 0) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (7 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (7 * K + 0) (fun i hi => count_equiv_add M i 7 inv9 8 (7 * K + 0) 7 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (7 * K + 0) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (7 * K + 0) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (5 * K + 0) = M * 5 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (5 * K + 0) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (5 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (5 * K + 0) (fun i hi => count_equiv_add M i 5 inv9 8 (5 * K + 0) 5 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (5 * K + 0) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (5 * K + 0) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (2 * K + 0) = M * 2 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (2 * K + 0) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (2 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (2 * K + 0) (fun i hi => count_equiv_add M i 2 inv9 8 (2 * K + 0) 2 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (2 * K + 0) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (2 * K + 0) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 8 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (6 * K + 0) = M * 6 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (6 * K + 0) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (6 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (6 * K + 0) (fun i hi => count_equiv_add M i 6 inv9 8 (6 * K + 0) 6 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (6 * K + 0) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (6 * K + 0) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 1 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case1_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case2_ineq (K r : ℕ) (hr : r < 9 * K + 2) :
    (if r + (8 * K + 1) ≥ 9 * K + 2 then 1 else 0) +
    (if r + (7 * K + 1) ≥ 9 * K + 2 then 1 else 0) +
    (if r + (1 * K + 0) ≥ 9 * K + 2 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 2 then 1 else 0) +
    (if r + (3 * K + 0) ≥ 9 * K + 2 then 1 else 0) := by
  split_ifs <;> omega

lemma case2_witness (K : ℕ) :
    9 * (4 * K + 1) = 4 * (9 * K + 2) + 1 ∧
    (4 * K + 1) * 7 + (8 * K + 1) = (9 * K + 2) * 4 ∧
    (4 * K + 1) * 5 + (7 * K + 1) = (9 * K + 2) * 3 ∧
    (4 * K + 1) * 2 + (1 * K + 0) = (9 * K + 2) * 1 ∧
    (4 * K + 1) * 0 + 0 = (9 * K + 2) * 0 ∧
    (4 * K + 1) * 6 + (3 * K + 0) = (9 * K + 2) * 3 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case2 (n K M : ℕ) (hM : M = 9 * K + 2) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (4 * K + 1)
  have h_witness := case2_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 4 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (8 * K + 1) = M * 4 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (8 * K + 1) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (8 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (8 * K + 1) (fun i hi => count_equiv_add M i 7 inv9 4 (8 * K + 1) 4 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (8 * K + 1) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (8 * K + 1) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (7 * K + 1) = M * 3 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (7 * K + 1) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (7 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (7 * K + 1) (fun i hi => count_equiv_add M i 5 inv9 4 (7 * K + 1) 3 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (7 * K + 1) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (7 * K + 1) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (1 * K + 0) = M * 1 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (1 * K + 0) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (1 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (1 * K + 0) (fun i hi => count_equiv_add M i 2 inv9 4 (1 * K + 0) 1 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (1 * K + 0) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (1 * K + 0) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 4 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (3 * K + 0) = M * 3 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (3 * K + 0) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (3 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (3 * K + 0) (fun i hi => count_equiv_add M i 6 inv9 4 (3 * K + 0) 3 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (3 * K + 0) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (3 * K + 0) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 2 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case2_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case4_ineq (K r : ℕ) (hr : r < 9 * K + 4) :
    (if r + (4 * K + 1) ≥ 9 * K + 4 then 1 else 0) +
    (if r + (8 * K + 3) ≥ 9 * K + 4 then 1 else 0) +
    (if r + (5 * K + 2) ≥ 9 * K + 4 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 4 then 1 else 0) +
    (if r + (6 * K + 2) ≥ 9 * K + 4 then 1 else 0) := by
  split_ifs <;> omega

lemma case4_witness (K : ℕ) :
    9 * (2 * K + 1) = 2 * (9 * K + 4) + 1 ∧
    (2 * K + 1) * 7 + (4 * K + 1) = (9 * K + 4) * 2 ∧
    (2 * K + 1) * 5 + (8 * K + 3) = (9 * K + 4) * 2 ∧
    (2 * K + 1) * 2 + (5 * K + 2) = (9 * K + 4) * 1 ∧
    (2 * K + 1) * 0 + 0 = (9 * K + 4) * 0 ∧
    (2 * K + 1) * 6 + (6 * K + 2) = (9 * K + 4) * 2 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case4 (n K M : ℕ) (hM : M = 9 * K + 4) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (2 * K + 1)
  have h_witness := case4_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 2 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (4 * K + 1) = M * 2 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (4 * K + 1) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (4 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (4 * K + 1) (fun i hi => count_equiv_add M i 7 inv9 2 (4 * K + 1) 2 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (4 * K + 1) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (4 * K + 1) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (8 * K + 3) = M * 2 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (8 * K + 3) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (8 * K + 3) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (8 * K + 3) (fun i hi => count_equiv_add M i 5 inv9 2 (8 * K + 3) 2 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (8 * K + 3) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (8 * K + 3) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (5 * K + 2) = M * 1 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (5 * K + 2) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (5 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (5 * K + 2) (fun i hi => count_equiv_add M i 2 inv9 2 (5 * K + 2) 1 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (5 * K + 2) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (5 * K + 2) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 2 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (6 * K + 2) = M * 2 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (6 * K + 2) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (6 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (6 * K + 2) (fun i hi => count_equiv_add M i 6 inv9 2 (6 * K + 2) 2 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (6 * K + 2) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (6 * K + 2) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 4 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case4_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case5_ineq (K r : ℕ) (hr : r < 9 * K + 5) :
    (if r + (5 * K + 2) ≥ 9 * K + 5 then 1 else 0) +
    (if r + (1 * K + 0) ≥ 9 * K + 5 then 1 else 0) +
    (if r + (4 * K + 2) ≥ 9 * K + 5 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 5 then 1 else 0) +
    (if r + (3 * K + 1) ≥ 9 * K + 5 then 1 else 0) := by
  split_ifs <;> omega

lemma case5_witness (K : ℕ) :
    9 * (7 * K + 4) = 7 * (9 * K + 5) + 1 ∧
    (7 * K + 4) * 7 + (5 * K + 2) = (9 * K + 5) * 6 ∧
    (7 * K + 4) * 5 + (1 * K + 0) = (9 * K + 5) * 4 ∧
    (7 * K + 4) * 2 + (4 * K + 2) = (9 * K + 5) * 2 ∧
    (7 * K + 4) * 0 + 0 = (9 * K + 5) * 0 ∧
    (7 * K + 4) * 6 + (3 * K + 1) = (9 * K + 5) * 5 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case5 (n K M : ℕ) (hM : M = 9 * K + 5) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (7 * K + 4)
  have h_witness := case5_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 7 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (5 * K + 2) = M * 6 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (5 * K + 2) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (5 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (5 * K + 2) (fun i hi => count_equiv_add M i 7 inv9 7 (5 * K + 2) 6 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (5 * K + 2) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (5 * K + 2) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (1 * K + 0) = M * 4 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (1 * K + 0) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (1 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (1 * K + 0) (fun i hi => count_equiv_add M i 5 inv9 7 (1 * K + 0) 4 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (1 * K + 0) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (1 * K + 0) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (4 * K + 2) = M * 2 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (4 * K + 2) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (4 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (4 * K + 2) (fun i hi => count_equiv_add M i 2 inv9 7 (4 * K + 2) 2 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (4 * K + 2) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (4 * K + 2) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 7 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (3 * K + 1) = M * 5 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (3 * K + 1) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (3 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (3 * K + 1) (fun i hi => count_equiv_add M i 6 inv9 7 (3 * K + 1) 5 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (3 * K + 1) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (3 * K + 1) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 5 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case5_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case7_ineq (K r : ℕ) (hr : r < 9 * K + 7) :
    (if r + (1 * K + 0) ≥ 9 * K + 7 then 1 else 0) +
    (if r + (2 * K + 1) ≥ 9 * K + 7 then 1 else 0) +
    (if r + (8 * K + 6) ≥ 9 * K + 7 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 7 then 1 else 0) +
    (if r + (6 * K + 4) ≥ 9 * K + 7 then 1 else 0) := by
  split_ifs <;> omega

lemma case7_witness (K : ℕ) :
    9 * (5 * K + 4) = 5 * (9 * K + 7) + 1 ∧
    (5 * K + 4) * 7 + (1 * K + 0) = (9 * K + 7) * 4 ∧
    (5 * K + 4) * 5 + (2 * K + 1) = (9 * K + 7) * 3 ∧
    (5 * K + 4) * 2 + (8 * K + 6) = (9 * K + 7) * 2 ∧
    (5 * K + 4) * 0 + 0 = (9 * K + 7) * 0 ∧
    (5 * K + 4) * 6 + (6 * K + 4) = (9 * K + 7) * 4 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case7 (n K M : ℕ) (hM : M = 9 * K + 7) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (5 * K + 4)
  have h_witness := case7_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 5 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (1 * K + 0) = M * 4 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (1 * K + 0) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (1 * K + 0) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (1 * K + 0) (fun i hi => count_equiv_add M i 7 inv9 5 (1 * K + 0) 4 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (1 * K + 0) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (1 * K + 0) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (2 * K + 1) = M * 3 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (2 * K + 1) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (2 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (2 * K + 1) (fun i hi => count_equiv_add M i 5 inv9 5 (2 * K + 1) 3 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (2 * K + 1) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (2 * K + 1) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (8 * K + 6) = M * 2 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (8 * K + 6) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (8 * K + 6) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (8 * K + 6) (fun i hi => count_equiv_add M i 2 inv9 5 (8 * K + 6) 2 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (8 * K + 6) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (8 * K + 6) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 5 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (6 * K + 4) = M * 4 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (6 * K + 4) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (6 * K + 4) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (6 * K + 4) (fun i hi => count_equiv_add M i 6 inv9 5 (6 * K + 4) 4 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (6 * K + 4) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (6 * K + 4) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 7 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case7_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma case8_ineq (K r : ℕ) (hr : r < 9 * K + 8) :
    (if r + (2 * K + 1) ≥ 9 * K + 8 then 1 else 0) +
    (if r + (4 * K + 3) ≥ 9 * K + 8 then 1 else 0) +
    (if r + (7 * K + 6) ≥ 9 * K + 8 then 1 else 0) ≥
    2 * (if r + 0 ≥ 9 * K + 8 then 1 else 0) +
    (if r + (3 * K + 2) ≥ 9 * K + 8 then 1 else 0) := by
  split_ifs <;> omega

lemma case8_witness (K : ℕ) :
    9 * (1 * K + 1) = 1 * (9 * K + 8) + 1 ∧
    (1 * K + 1) * 7 + (2 * K + 1) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 5 + (4 * K + 3) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 2 + (7 * K + 6) = (9 * K + 8) * 1 ∧
    (1 * K + 1) * 0 + 0 = (9 * K + 8) * 0 ∧
    (1 * K + 1) * 6 + (3 * K + 2) = (9 * K + 8) * 1 ∧
    True := by
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, trivial⟩

lemma delta_case8 (n K M : ℕ) (hM : M = 9 * K + 8) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have hM_pos : M > 0 := by omega
  let inv9 := (1 * K + 1)
  have h_witness := case8_witness K
  rcases h_witness with ⟨h_inv_raw, h_c7_raw, h_c5_raw, h_c2_raw, h_c0_raw, h_c6_raw, _⟩
  have h_inv : 9 * inv9 = 1 * M + 1 := by rw [hM]; exact h_inv_raw
  have h_c7 : inv9 * 7 + (2 * K + 1) = M * 1 := by rw [hM]; exact h_c7_raw
  have hc7_lt : (2 * K + 1) < M := by omega
  have heq7 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) = n / M + (if n % M + (2 * K + 1) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 7 (2 * K + 1) (fun i hi => count_equiv_add M i 7 inv9 1 (2 * K + 1) 1 (9 * i - 7) h_inv h_c7 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (2 * K + 1) M hM_pos hc7_lt]
    rw [div_eq_div_add_indicator n (2 * K + 1) M hM_pos hc7_lt]
  have h_c5 : inv9 * 5 + (4 * K + 3) = M * 1 := by rw [hM]; exact h_c5_raw
  have hc5_lt : (4 * K + 3) < M := by omega
  have heq5 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) = n / M + (if n % M + (4 * K + 3) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 5 (4 * K + 3) (fun i hi => count_equiv_add M i 5 inv9 1 (4 * K + 3) 1 (9 * i - 5) h_inv h_c5 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (4 * K + 3) M hM_pos hc5_lt]
    rw [div_eq_div_add_indicator n (4 * K + 3) M hM_pos hc5_lt]
  have h_c2 : inv9 * 2 + (7 * K + 6) = M * 1 := by rw [hM]; exact h_c2_raw
  have hc2_lt : (7 * K + 6) < M := by omega
  have heq2 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) = n / M + (if n % M + (7 * K + 6) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 2 (7 * K + 6) (fun i hi => count_equiv_add M i 2 inv9 1 (7 * K + 6) 1 (9 * i - 2) h_inv h_c2 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (7 * K + 6) M hM_pos hc2_lt]
    rw [div_eq_div_add_indicator n (7 * K + 6) M hM_pos hc2_lt]
  have h_c0 : inv9 * 0 + 0 = M * 0 := by rw [hM]; exact h_c0_raw
  have hc0_lt : 0 < M := by omega
  have heq0 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) = n / M + (if n % M + 0 ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 0 0 (fun i hi => count_equiv_add M i 0 inv9 1 0 0 (9 * i - 0) h_inv h_c0 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n 0 M hM_pos hc0_lt]
    rw [div_eq_div_add_indicator n 0 M hM_pos hc0_lt]
  have h_c6 : inv9 * 6 + (3 * K + 2) = M * 1 := by rw [hM]; exact h_c6_raw
  have hc6_lt : (3 * K + 2) < M := by omega
  have heq6 : ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) = n / M + (if n % M + (3 * K + 2) ≥ M then 1 else 0) := by
    rw [sum_indicator_equiv n M 6 (3 * K + 2) (fun i hi => count_equiv_add M i 6 inv9 1 (3 * K + 2) 1 (9 * i - 6) h_inv h_c6 (by simp only [mem_Icc] at hi; omega))]
    rw [sum_indicator_eq_div n (3 * K + 2) M hM_pos hc6_lt]
    rw [div_eq_div_add_indicator n (3 * K + 2) M hM_pos hc6_lt]
  have hr : n % M < 9 * K + 8 := by rw [← hM]; exact mod_lt n hM_pos
  have h_ineq := case8_ineq K (n % M) hr
  rw [heq7, heq5, heq2, heq0, heq6]
  rw [hM] at *
  omega

lemma delta_ge_0 (n M : ℕ) (hM_pos : M > 0) (hM_coprime : ¬ 3 ∣ M) :
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 7 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 5 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 2 then 1 else 0) ≥
    2 * ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 0 then 1 else 0) +
    ∑ i ∈ Icc 1 n, (if M ∣ 9 * i - 6 then 1 else 0) := by
  have : M % 9 = 1 ∨ M % 9 = 2 ∨ M % 9 = 4 ∨ M % 9 = 5 ∨ M % 9 = 7 ∨ M % 9 = 8 := by
    have : M % 9 < 9 := mod_lt M (by decide)
    have : ¬ 3 ∣ M % 9 := by
      intro h
      apply hM_coprime
      have eq : M = 9 * (M / 9) + M % 9 := (Nat.div_add_mod M 9).symm
      omega
    omega
  rcases this with h1 | h2 | h3 | h4 | h5 | h6
  · have hM_eq : M = 9 * (M / 9) + 1 := by omega
    exact delta_case1 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 2 := by omega
    exact delta_case2 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 4 := by omega
    exact delta_case4 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 5 := by omega
    exact delta_case5 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 7 := by omega
    exact delta_case7 n (M / 9) M hM_eq
  · have hM_eq : M = 9 * (M / 9) + 8 := by omega
    exact delta_case8 n (M / 9) M hM_eq
