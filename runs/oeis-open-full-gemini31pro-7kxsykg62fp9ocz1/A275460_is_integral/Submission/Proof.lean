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
