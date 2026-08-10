import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
lemma sum_val_eq_p_mul_p_sub_one_div_two (p : ℕ) :
    ∑ i : Fin p, i.val = p * (p - 1) / 2 := by
  change ∑ i : Fin p, id (i.val) = p * (p - 1) / 2
  rw [Fin.sum_univ_eq_sum_range id]
  simp [sum_range_id]

lemma sum_val_add_perm_val (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    ∑ i : Fin p, (i.val + (σ i).val) = p * (p - 1) := by
  rw [sum_add_distrib]
  rw [Equiv.sum_comp σ (fun (i : Fin p) => i.val)]
  rw [sum_val_eq_p_mul_p_sub_one_div_two p]
  have h_even := Nat.even_mul_pred_self p
  rw [← Nat.two_mul, Nat.mul_div_cancel' h_even.two_dvd]

lemma sum_val_add_perm_val_int (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    ∑ i : Fin p, ((i.val : ℤ) + ((σ i).val : ℤ)) = p * (p - 1 : ℤ) := by
  cases p with
  | zero => simp
  | succ p =>
    rw [sum_add_distrib]
    rw [Equiv.sum_comp σ (fun (i : Fin (succ p)) => (i.val : ℤ))]
    have h_sum : ∑ i : Fin (succ p), (i.val : ℤ) = ↑(succ p * p / 2) := by
      exact_mod_cast sum_val_eq_p_mul_p_sub_one_div_two (succ p)
    rw [h_sum]
    have h_even : Even (succ p * p) := by
      have h := Nat.even_mul_pred_self (succ p)
      change Even (succ p * p) at h
      exact h
    have h_div : (((succ p * p / 2 : ℕ) : ℤ) + ((succ p * p / 2 : ℕ) : ℤ)) = (succ p * p : ℕ) := by
      rw [← two_mul]
      have : (2 : ℤ) * ↑(succ p * p / 2) = ↑(2 * (succ p * p / 2)) := rfl
      rw [this]
      rw [Nat.mul_div_cancel' h_even.two_dvd]
    have h_sub : (succ p - 1 : ℤ) = p := by omega
    have h_div_cast : (((succ p * p / 2 : ℕ) : ℤ) + ((succ p * p / 2 : ℕ) : ℤ)) = succ p * (succ p - 1 : ℤ) := by
      rw [h_sub]
      rw [h_div]
      push_cast
      ring
    exact h_div_cast

lemma eq_of_le_and_sum_eq (p : ℕ) (σ : Equiv.Perm (Fin p))
    (h : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1) :
    ∀ i : Fin p, i.val + (σ i).val = p - 1 := by
  have h_sum : ∑ i : Fin p, ((p - 1 : ℤ) - ((i.val : ℤ) + ((σ i).val : ℤ))) = 0 := by
    rw [Finset.sum_sub_distrib]
    rw [sum_const, Finset.card_univ, Fintype.card_fin]
    rw [sum_val_add_perm_val_int p σ]
    ring
  have h_nonneg : ∀ i : Fin p, 0 ≤ (p - 1 : ℤ) - ((i.val : ℤ) + ((σ i).val : ℤ)) := by
    intro i
    have hi := h i
    omega
  have h_eq_zero : ∀ i : Fin p, (p - 1 : ℤ) - ((i.val : ℤ) + ((σ i).val : ℤ)) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h_nonneg i)).mp h_sum i (mem_univ i)
  intro i
  have h_i := h_eq_zero i
  omega

def σ_anti (p : ℕ) (i : Fin p) : Fin p :=
  ⟨p - 1 - i.val, by
    have : i.val < p := i.is_lt
    omega⟩

lemma eq_anti_of_sum_eq (p : ℕ) (σ : Equiv.Perm (Fin p))
    (h : ∀ i : Fin p, i.val + (σ i).val ≤ p - 1) :
    ∀ i : Fin p, σ i = σ_anti p i := by
  intro i
  have h_eq := eq_of_le_and_sum_eq p σ h i
  have : i.val < p := i.is_lt
  have h_val : (σ i).val = (σ_anti p i).val := by
    unfold σ_anti
    dsimp
    omega
  exact Fin.ext h_val

def σ_anti_equiv (p : ℕ) : Equiv.Perm (Fin p) where
  toFun := σ_anti p
  invFun := σ_anti p
  left_inv i := by
    ext
    unfold σ_anti
    dsimp
    omega
  right_inv i := by
    ext
    unfold σ_anti
    dsimp
    omega

lemma prod_eq_zero_of_zero {α β : Type*} [CommMonoidWithZero β] [Fintype α]
    (f : α → β) (i : α) (h : f i = 0) :
    ∏ x : α, f x = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) h

lemma det_eq_single (p : ℕ) (M : Matrix (Fin p) (Fin p) (ZMod p))
    (h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → M i j = 0) :
    M.det = (Equiv.Perm.sign (σ_anti_equiv p) : ZMod p) * ∏ i : Fin p, M (σ_anti p i) i := by
  rw [Matrix.det_apply']
  rw [Finset.sum_eq_single (σ_anti_equiv p)]
  · unfold σ_anti_equiv
    rfl
  · intro σ _ h_ne
    have h_not : ¬ (∀ i : Fin p, i.val + (σ i).val ≤ p - 1) := by
      intro h_le
      have h_eq : σ = σ_anti_equiv p := by
        apply Equiv.ext
        intro i
        have h_all := eq_anti_of_sum_eq p σ h_le i
        exact h_all
      exact h_ne h_eq
    push_neg at h_not
    obtain ⟨i, hi⟩ := h_not
    have hi_ge : (σ i).val + i.val ≥ p := by omega
    have h_mij : M (σ i) i = 0 := h_zero (σ i) i hi_ge
    have h_prod : ∏ j : Fin p, M (σ j) j = 0 := prod_eq_zero_of_zero (fun j => M (σ j) j) i h_mij
    rw [h_prod, mul_zero]
  · intro h_not_mem
    exact (h_not_mem (Finset.mem_univ _)).elim

lemma sign_σ_anti_equiv (p : ℕ) :
    (Equiv.Perm.sign (σ_anti_equiv p) : ℤ) = (-1 : ℤ) ^ (p * (p - 1) / 2) := by
  rw [Equiv.Perm.sign_eq_prod_prod_Iio]
  have h_eq : ∏ j : Fin p, ∏ i ∈ Finset.Iio j, (if σ_anti_equiv p i < σ_anti_equiv p j then (1 : Units ℤ) else -1) =
      ∏ j : Fin p, ∏ i ∈ Finset.Iio j, (-1 : Units ℤ) := by
    refine Finset.prod_congr rfl (fun j _ => Finset.prod_congr rfl (fun i hi => ?_))
    rw [Finset.mem_Iio] at hi
    have h_lt : (σ_anti_equiv p j).val < (σ_anti_equiv p i).val := by
      unfold σ_anti_equiv σ_anti
      dsimp
      omega
    have h_not : ¬ (σ_anti_equiv p i < σ_anti_equiv p j) := by
      intro h
      have : (σ_anti_equiv p j).val < (σ_anti_equiv p j).val := lt_trans h_lt h
      exact lt_irrefl _ this
    rw [if_neg h_not]
  rw [h_eq]
  push_cast
  simp_rw [Finset.prod_const, Fin.card_Iio]
  rw [prod_pow_eq_pow_sum]
  rw [sum_val_eq_p_mul_p_sub_one_div_two p]

lemma transfer_A_det (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Matrix.det (fun i j : Fin p => a (i.val + j.val)) ≡ (-1 : ℤ) ^ ((p - 1) / 2) [ZMOD p] ↔
      (Matrix.det (fun i j : Fin p => (a (i.val + j.val) : ZMod p))) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rfl

lemma transfer_C_det (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Matrix.det (fun i j : Fin p => c (i.val + j.val)) ≡ 1 [ZMOD p] ↔
      (Matrix.det (fun i j : Fin p => (c (i.val + j.val) : ZMod p))) = 1 := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  rfl

lemma p_mul_p_sub_one_div_two_eq (p : ℕ) (h_mod : p % 2 = 1) :
    p * (p - 1) / 2 = 2 * (((p - 1) / 2) * ((p - 1) / 2)) + (p - 1) / 2 := by
  generalize h_k : (p - 1) / 2 = k
  have hp : p = 2 * k + 1 := by omega
  rw [hp]
  have h_sub : 2 * k + 1 - 1 = 2 * k := by omega
  rw [h_sub]
  have h_prod : (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) := by ring
  rw [h_prod]
  rw [Nat.mul_div_cancel_left _ (by decide)]
  ring

lemma neg_one_pow_p_mul_sub_one_div_two (p : ℕ) (h_mod : p % 2 = 1) :
    (-1 : ZMod p) ^ (p * (p - 1) / 2) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  rw [p_mul_p_sub_one_div_two_eq p h_mod]
  rw [pow_add]
  have h_pow_mul : (-1 : ZMod p) ^ (2 * (((p - 1) / 2) * ((p - 1) / 2))) = 1 := by
    rw [pow_mul]
    have : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [this, one_pow]
  rw [h_pow_mul, one_mul]

lemma choose_p_sub_one_modEq (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∀ k < p, (choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ d hd =>
    intro hd_lt
    have h_ne : (d + 1 : ZMod p) ≠ 0 := by
      intro hc
      have hc2 : ((d + 1 : ℕ) : ZMod p) = 0 := by
        exact_mod_cast hc
      rw [ZMod.natCast_eq_zero_iff] at hc2
      have : p ≤ d + 1 := Nat.le_of_dvd (by omega) hc2
      omega
    have h_mul : ((choose (p - 1) (d + 1) : ZMod p) - (-1 : ZMod p) ^ (d + 1)) * (d + 1 : ZMod p) = 0 := by
      have h_id := choose_succ_right_eq (p - 1) d
      have h_cast := congr_arg (fun (x : ℕ) => (x : ZMod p)) h_id
      push_cast at h_cast
      rw [hd (by omega)] at h_cast
      have h_sub_eq : ((p - 1 - d : ℕ) : ZMod p) = - (d + 1 : ZMod p) := by
        have hp_zero : (p : ZMod p) = 0 := ZMod.natCast_self p
        have h_sum : p - 1 - d + (d + 1) = p := by omega
        have h_sum_cast := congr_arg (fun (x : ℕ) => (x : ZMod p)) h_sum
        push_cast at h_sum_cast
        rw [hp_zero] at h_sum_cast
        exact add_eq_zero_iff_eq_neg.mp h_sum_cast
      rw [h_sub_eq] at h_cast
      calc
        ((choose (p - 1) (d + 1) : ZMod p) - (-1 : ZMod p) ^ (d + 1)) * (d + 1 : ZMod p)
        _ = (choose (p - 1) (d + 1) : ZMod p) * (d + 1 : ZMod p) - (-1 : ZMod p) ^ (d + 1) * (d + 1 : ZMod p) := by ring
        _ = (-1 : ZMod p) ^ d * - (d + 1 : ZMod p) - (-1 : ZMod p) ^ (d + 1) * (d + 1 : ZMod p) := by rw [h_cast]
        _ = 0 := by
          have : (-1 : ZMod p) ^ (d + 1) = (-1 : ZMod p) ^ d * -1 := by ring
          rw [this]
          ring
    have h_sub_zero : (choose (p - 1) (d + 1) : ZMod p) - (-1 : ZMod p) ^ (d + 1) = 0 := by
      exact (mul_eq_zero.mp h_mul).resolve_right h_ne
    exact sub_eq_zero.mp h_sub_zero

lemma sum_range_neg_one_pow (p m : ℕ) :
    ∑ k ∈ range (2 * m), (-1 : ZMod p) ^ k = 0 ∧
    ∑ k ∈ range (2 * m + 1), (-1 : ZMod p) ^ k = 1 := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rcases ih with ⟨ih1, ih2⟩
    have h2m2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    have h2m3 : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by omega
    constructor
    · rw [h2m2, sum_range_succ, ih2]
      have : (-1 : ZMod p) ^ (2 * m + 1) = -1 := by
        rw [pow_add, pow_mul]
        have h_two : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [h_two, one_pow, pow_one, one_mul]
      rw [this]
      ring
    · rw [h2m3, sum_range_succ]
      have h_sum : ∑ k ∈ range (2 * m + 2), (-1 : ZMod p) ^ k = 0 := by
        have : 2 * m + 2 = 2 * m + 1 + 1 := by omega
        rw [this, sum_range_succ, ih2]
        have : (-1 : ZMod p) ^ (2 * m + 1) = -1 := by
          rw [pow_add, pow_mul]
          have h_two : (-1 : ZMod p) ^ 2 = 1 := by ring
          rw [h_two, one_pow, pow_one, one_mul]
        rw [this]
        ring
      rw [h_sum]
      have : (-1 : ZMod p) ^ (2 * m + 2) = 1 := by
        rw [pow_add, pow_mul]
        have h_two : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [h_two, one_pow]
        ring
      rw [this]
      simp

lemma a_p_sub_one_eq_one (p : ℕ) [hp : Fact (Nat.Prime p)] (h_odd : p ≠ 2) :
    (a (p - 1) : ZMod p) = 1 := by
  have h_sum : (a (p - 1) : ZMod p) = ∑ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 4 := by
    unfold a
    push_cast
    have : p > 0 := hp.out.pos
    have : p - 1 + 1 = p := by omega
    rw [this]
  rw [h_sum]
  have h_terms : ∀ k ∈ range p, (-1 : ZMod p) ^ k * (choose (p - 1) k : ZMod p) ^ 4 = (-1 : ZMod p) ^ k := by
    intro k hk
    rw [mem_range] at hk
    rw [choose_p_sub_one_modEq p k hk]
    rw [← pow_mul]
    rw [← pow_add]
    have : k + k * 4 = 5 * k := by ring
    rw [this]
    have : 5 * k = k + 2 * (2 * k) := by ring
    rw [this, pow_add, pow_mul]
    have : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [this, one_pow, mul_one]
  rw [sum_congr rfl h_terms]
  have h_range : range p = range (2 * (p / 2) + 1) := by
    congr 1
    have h_mod : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left h_odd
    omega
  rw [h_range]
  exact (sum_range_neg_one_pow p (p / 2)).right

lemma choose_two_mul_self_eq_zero (p : ℕ) [hp : Fact (Nat.Prime p)] (k : ℕ)
    (hk1 : (p - 1) / 2 < k) (hk2 : k < p) :
    (choose (2 * k) k : ZMod p) = 0 := by
  have hp_ge : p ≥ 2 := hp.out.two_le
  have h_lucas : (choose (2 * k) k : ZMod p) = (choose (2 * k % p) (k % p) : ZMod p) * (choose (2 * k / p) (k / p) : ZMod p) := by
    have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * k) (k := k) (p := p)
    rw [← ZMod.intCast_eq_intCast_iff] at h_eq
    push_cast at h_eq
    exact h_eq
  have hk_mod : k % p = k := Nat.mod_eq_of_lt hk2
  have h_lt : p - 1 < 2 * k := by
    have h_two : 0 < 2 := by decide
    have h_lt' : p - 1 < k * 2 := (Nat.div_lt_iff_lt_mul h_two).mp hk1
    rwa [mul_comm] at h_lt'
  have h_ge : p ≤ 2 * k := by omega
  have h_lt2 : 2 * k < 2 * p := by omega
  have h2k_mod : 2 * k % p = 2 * k - p := by
    clear hk1 h_lt
    have h_add : 2 * k % p = ((2 * k - p) + p) % p := by congr 1; omega
    rw [h_add, Nat.add_mod_right]
    have : 2 * k - p < p := by omega
    exact Nat.mod_eq_of_lt this
  rw [hk_mod, h2k_mod] at h_lucas
  have h_choose_zero : choose (2 * k - p) k = 0 := choose_eq_zero_of_lt (by omega)
  rw [h_choose_zero] at h_lucas
  push_cast at h_lucas
  rw [h_lucas, MulZeroClass.zero_mul]

lemma c_p_sub_one_eq_neg_one_pow (p : ℕ) [hp : Fact (Nat.Prime p)] (h_odd : p ≠ 2) :
    (c (p - 1) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hp_ge : p ≥ 2 := hp.out.two_le
  have h_sum : (c (p - 1) : ZMod p) = ∑ k ∈ range p,
      ((-1 : ZMod p) ^ k) * ((choose (p - 1) k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) := by
    unfold c
    push_cast
    have : p > 0 := hp.out.pos
    have : p - 1 + 1 = p := by omega
    rw [this]
  rw [h_sum]
  have h_zero : ∀ k ∈ range p, k ≠ (p - 1) / 2 →
      ((-1 : ZMod p) ^ k) * ((choose (p - 1) k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 0 := by
    intro k hk h_ne
    rw [mem_range] at hk
    have h_cases : k > (p - 1) / 2 ∨ k < (p - 1) / 2 := by omega
    rcases h_cases with h1 | h2
    · have : (choose (2 * k) k : ZMod p) = 0 := choose_two_mul_self_eq_zero p k h1 hk
      rw [this]
      ring
    · have h3 : (p - 1) / 2 < p - 1 - k := by omega
      have h4 : p - 1 - k < p := by omega
      have : (choose (2 * (p - 1 - k)) (p - 1 - k) : ZMod p) = 0 := choose_two_mul_self_eq_zero p (p - 1 - k) h3 h4
      rw [this]
      ring
  rw [sum_eq_single ((p - 1) / 2)]
  · have hk : (p - 1) / 2 < p := by omega
    have h_mod : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left h_odd
    have h_sub_mod : (p - 1) % 2 = 0 := by omega
    have h_div_mul : p - 1 = 2 * ((p - 1) / 2) := by
      have := Nat.div_add_mod (p - 1) 2
      omega
    have h_choose_sub : p - 1 - (p - 1) / 2 = (p - 1) / 2 := by omega
    rw [h_choose_sub]
    have h_choose := choose_p_sub_one_modEq p ((p - 1) / 2) hk
    rw [h_choose]
    have h_mul_two : 2 * ((p - 1) / 2) = p - 1 := by omega
    rw [h_mul_two, h_choose]
    have h_pow : (-1 : ZMod p) ^ ((p - 1) / 2) * ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ 2 * (-1 : ZMod p) ^ ((p - 1) / 2) * (-1 : ZMod p) ^ ((p - 1) / 2) =
        (-1 : ZMod p) ^ (5 * ((p - 1) / 2)) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    rw [h_pow]
    have : 5 * ((p - 1) / 2) = ((p - 1) / 2) + 2 * (2 * ((p - 1) / 2)) := by ring
    rw [this, pow_add, pow_mul]
    have h_two : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [h_two, one_pow, mul_one]
  · intro k hk h_ne
    exact h_zero k hk h_ne
  · intro h_not_mem
    have : (p - 1) / 2 < p := by omega
    have : (p - 1) / 2 ∈ range p := mem_range.mpr this
    contradiction

lemma a_mod_p_eq_zero (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) (n : ℕ)
    (h_le1 : p ≤ n) (h_le2 : n ≤ 2 * p - 2) :
    (a n : ZMod p) = 0 := by
  have hp_prime : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_ge : p ≥ 2 := hp.two_le
  have h_odd_p : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h_odd
  have h_pos : 0 < p := hp.pos
  have hn_sub_lt : n - p < p := by omega
  have hn_div : n / p = 1 := by
    have h_div_eq : n / p = ((n - p) + p) / p := by congr 1; omega
    rw [h_div_eq, Nat.add_div_right (n - p) h_pos]
    rw [Nat.div_eq_of_lt hn_sub_lt]
  have hn_mod : n % p = n - p := by
    have h_mod_eq : n % p = ((n - p) + p) % p := by congr 1; omega
    rw [h_mod_eq, Nat.add_mod_right (n - p) p]
    rw [Nat.mod_eq_of_lt hn_sub_lt]
  have hp_le : p ≤ n + 1 := by omega
  have h_sum_split : (a n : ZMod p) = ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4 := by
    unfold a
    push_cast
    rfl
  rw [h_sum_split]
  have h_split := sum_range_add_sum_Ico (fun k => (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4) hp_le
  have hn_sub_le : n - p + 1 ≤ p := by omega
  have h_split2 := sum_range_add_sum_Ico (fun k => (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4) hn_sub_le
  have h_zero_part1 : ∀ k ∈ Ico (n - p + 1) p, (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4 = 0 := by
    intro k hk
    rw [mem_Ico] at hk
    have h_lucas : (choose n k : ZMod p) = (choose (n % p) (k % p) : ZMod p) * (choose (n / p) (k / p) : ZMod p) := by
      have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h_eq
      push_cast at h_eq
      exact h_eq
    have hk_lt : k < p := by omega
    have hk_mod : k % p = k := Nat.mod_eq_of_lt hk_lt
    have hk_div : k / p = 0 := Nat.div_eq_of_lt hk_lt
    rw [hn_mod, hn_div, hk_mod, hk_div] at h_lucas
    have h_choose_zero : choose (n - p) k = 0 := choose_eq_zero_of_lt (by omega)
    rw [h_choose_zero] at h_lucas
    push_cast at h_lucas
    rw [h_lucas]
    ring
  have h_sum_zero1 : ∑ k ∈ Ico (n - p + 1) p, (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4 = 0 := by
    exact sum_eq_zero h_zero_part1
  have h_ico_eq : Ico p (n + 1) = Ico (0 + p) ((n - p + 1) + p) := by
    congr 1
    · omega
    · omega
  have h_shift : ∑ k ∈ Ico p (n + 1), (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4 =
      ∑ k ∈ range (n - p + 1), (-1 : ZMod p) ^ (k + p) * (choose n (k + p) : ZMod p) ^ 4 := by
    rw [h_ico_eq]
    rw [← sum_Ico_add' (fun k => (-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4) 0 (n - p + 1) p]
    rw [Ico_zero_eq_range]
  have h_pair : ∀ k ∈ range (n - p + 1),
      ((-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4) +
      ((-1 : ZMod p) ^ (k + p) * (choose n (k + p) : ZMod p) ^ 4) = 0 := by
    intro k hk
    rw [mem_range] at hk
    have h_choose_k : (choose n k : ZMod p) = (choose (n - p) k : ZMod p) := by
      have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h_eq
      push_cast at h_eq
      have hk_lt : k < p := by omega
      have hk_mod : k % p = k := Nat.mod_eq_of_lt hk_lt
      have hk_div : k / p = 0 := Nat.div_eq_of_lt hk_lt
      rw [hn_mod, hn_div, hk_mod, hk_div] at h_eq
      have h10 : choose 1 0 = 1 := rfl
      rw [h10] at h_eq
      push_cast at h_eq
      rw [mul_one] at h_eq
      exact h_eq
    have h_choose_kp : (choose n (k + p) : ZMod p) = (choose (n - p) k : ZMod p) := by
      have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k + p) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h_eq
      push_cast at h_eq
      have hk_mod : (k + p) % p = k := by
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega : k < p)
      have hk_div : (k + p) / p = 1 := by
        rw [Nat.add_div_right k h_pos]
        rw [Nat.div_eq_of_lt (by omega : k < p)]
      rw [hn_mod, hn_div, hk_mod, hk_div] at h_eq
      have h11 : choose 1 1 = 1 := rfl
      rw [h11] at h_eq
      push_cast at h_eq
      rw [mul_one] at h_eq
      exact h_eq
    rw [h_choose_k, h_choose_kp]
    have h_sign : (-1 : ZMod p) ^ (k + p) = - (-1 : ZMod p) ^ k := by
      rw [pow_add]
      have h_odd_pow : (-1 : ZMod p) ^ p = -1 := by
        have hp_eq : p = 2 * (p / 2) + 1 := by omega
        have h_pow_eq : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * (p / 2) + 1) := by congr 1
        rw [h_pow_eq]
        rw [pow_add, pow_mul]
        have : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [this, one_pow, one_mul, pow_one]
      rw [h_odd_pow]
      ring
    rw [h_sign]
    ring
  have h_sum_total : ∑ k ∈ range (n - p + 1), (
      ((-1 : ZMod p) ^ k * (choose n k : ZMod p) ^ 4) +
      ((-1 : ZMod p) ^ (k + p) * (choose n (k + p) : ZMod p) ^ 4)) = 0 := by
    rw [sum_congr rfl h_pair]
    simp
  rw [sum_add_distrib] at h_sum_total
  rw [← h_split]
  rw [← h_split2]
  rw [h_sum_zero1, add_zero]
  rw [h_shift]
  exact h_sum_total

lemma c_mod_p_eq_zero (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) (n : ℕ)
    (h_le1 : p ≤ n) (h_le2 : n ≤ 2 * p - 2) :
    (c n : ZMod p) = 0 := by
  have hp_prime : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_ge : p ≥ 2 := hp.two_le
  have h_odd_p : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h_odd
  have h_pos : 0 < p := hp.pos
  have hn_sub_lt : n - p < p := by omega
  have hn_div : n / p = 1 := by
    have h_div_eq : n / p = ((n - p) + p) / p := by congr 1; omega
    rw [h_div_eq, Nat.add_div_right (n - p) h_pos]
    rw [Nat.div_eq_of_lt hn_sub_lt]
  have hn_mod : n % p = n - p := by
    have h_mod_eq : n % p = ((n - p) + p) % p := by congr 1; omega
    rw [h_mod_eq, Nat.add_mod_right (n - p) p]
    rw [Nat.mod_eq_of_lt hn_sub_lt]
  have hp_le : p ≤ n + 1 := by omega
  have h_sum_split : (c n : ZMod p) = ∑ k ∈ range (n + 1),
      ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) := by
    unfold c
    push_cast
    rfl
  rw [h_sum_split]
  have h_split := sum_range_add_sum_Ico (fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) hp_le
  have hn_sub_le : n - p + 1 ≤ p := by omega
  have h_split2 := sum_range_add_sum_Ico (fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) hn_sub_le
  have h_zero_part1 : ∀ k ∈ Ico (n - p + 1) p, ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) = 0 := by
    intro k hk
    rw [mem_Ico] at hk
    have h_lucas : (choose n k : ZMod p) = (choose (n % p) (k % p) : ZMod p) * (choose (n / p) (k / p) : ZMod p) := by
      have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h_eq
      push_cast at h_eq
      exact h_eq
    have hk_lt : k < p := by omega
    have hk_mod : k % p = k := Nat.mod_eq_of_lt hk_lt
    have hk_div : k / p = 0 := Nat.div_eq_of_lt hk_lt
    rw [hn_mod, hn_div, hk_mod, hk_div] at h_lucas
    have h_choose_zero : choose (n - p) k = 0 := choose_eq_zero_of_lt (by omega)
    rw [h_choose_zero] at h_lucas
    push_cast at h_lucas
    rw [h_lucas]
    ring
  have h_sum_zero1 : ∑ k ∈ Ico (n - p + 1) p, ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) = 0 := by
    exact sum_eq_zero h_zero_part1
  have h_ico_eq : Ico p (n + 1) = Ico (0 + p) ((n - p + 1) + p) := by
    congr 1
    · omega
    · omega
  have h_shift : ∑ k ∈ Ico p (n + 1), ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p) =
      ∑ k ∈ range (n - p + 1), ((-1 : ZMod p) ^ (k + p)) * ((choose n (k + p) : ZMod p) ^ 2) * (choose (2 * (k + p)) (k + p) : ZMod p) * (choose (2 * (n - (k + p))) (n - (k + p)) : ZMod p) := by
    rw [h_ico_eq]
    rw [← sum_Ico_add' (fun k => ((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) 0 (n - p + 1) p]
    rw [Ico_zero_eq_range]
  have h_pair : ∀ k ∈ range (n - p + 1),
      (((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) +
      (((-1 : ZMod p) ^ (k + p)) * ((choose n (k + p) : ZMod p) ^ 2) * (choose (2 * (k + p)) (k + p) : ZMod p) * (choose (2 * (n - (k + p))) (n - (k + p)) : ZMod p)) = 0 := by
    intro k hk
    rw [mem_range] at hk
    have h_choose_k : (choose n k : ZMod p) = (choose (n - p) k : ZMod p) := by
      have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h_eq
      push_cast at h_eq
      have hk_lt : k < p := by omega
      have hk_mod : k % p = k := Nat.mod_eq_of_lt hk_lt
      have hk_div : k / p = 0 := Nat.div_eq_of_lt hk_lt
      rw [hn_mod, hn_div, hk_mod, hk_div] at h_eq
      have h10 : choose 1 0 = 1 := rfl
      rw [h10] at h_eq
      push_cast at h_eq
      rw [mul_one] at h_eq
      exact h_eq
    have h_choose_kp : (choose n (k + p) : ZMod p) = (choose (n - p) k : ZMod p) := by
      have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k + p) (p := p)
      rw [← ZMod.intCast_eq_intCast_iff] at h_eq
      push_cast at h_eq
      have hk_mod : (k + p) % p = k := by
        rw [Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega : k < p)
      have hk_div : (k + p) / p = 1 := by
        rw [Nat.add_div_right k h_pos]
        rw [Nat.div_eq_of_lt (by omega : k < p)]
      rw [hn_mod, hn_div, hk_mod, hk_div] at h_eq
      have h11 : choose 1 1 = 1 := rfl
      rw [h11] at h_eq
      push_cast at h_eq
      rw [mul_one] at h_eq
      exact h_eq
    by_cases h_2k : 2 * k ≥ p
    · have h_choose2k : (choose (2 * k) k : ZMod p) = 0 := by
        have hk1 : (p - 1) / 2 < k := by
          have h_two : 0 < 2 := by decide
          rw [Nat.div_lt_iff_lt_mul h_two]
          omega
        exact choose_two_mul_self_eq_zero p k hk1 (by omega)
      have h_choose2kp : (choose (2 * (k + p)) (k + p) : ZMod p) = 0 := by
        have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * k + 2 * p) (k := k + p) (p := p)
        rw [← ZMod.intCast_eq_intCast_iff] at h_eq
        push_cast at h_eq
        have h_num_eq : 2 * (k + p) = 2 * k + 2 * p := by ring
        have h_goal_eq : (choose (2 * (k + p)) (k + p) : ZMod p) = (choose (2 * k + 2 * p) (k + p) : ZMod p) := by congr 2
        rw [h_goal_eq, h_eq]
        have h1 : (2 * k + 2 * p) % p = 2 * k - p := by
          have h_eq2 : 2 * k + 2 * p = (2 * k - p) + p * 3 := by omega
          rw [h_eq2, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (by omega : 2 * k - p < p)
        have h3 : (k + p) % p = k := by
          rw [Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega : k < p)
        rw [h1, h3]
        have h_choose_zero : choose (2 * k - p) k = 0 := choose_eq_zero_of_lt (by omega)
        rw [h_choose_zero]
        push_cast
        rw [MulZeroClass.zero_mul]
      rw [h_choose2k, h_choose2kp]
      ring
    · by_cases h_2j : 2 * (n - p - k) ≥ p
      · have h_choose2nk : (choose (2 * (n - k)) (n - k) : ZMod p) = 0 := by
          have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * (n - p - k) + 2 * p) (k := n - p - k + p) (p := p)
          rw [← ZMod.intCast_eq_intCast_iff] at h_eq
          push_cast at h_eq
          have h_goal_eq : (choose (2 * (n - k)) (n - k) : ZMod p) = (choose (2 * (n - p - k) + 2 * p) (n - p - k + p) : ZMod p) := by
            congr 2 <;> omega
          rw [h_goal_eq, h_eq]
          have h1 : (2 * (n - p - k) + 2 * p) % p = 2 * (n - p - k) - p := by
            have h_eq2 : 2 * (n - p - k) + 2 * p = (2 * (n - p - k) - p) + p * 3 := by omega
            rw [h_eq2, Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega : 2 * (n - p - k) - p < p)
          have h3 : (n - p - k + p) % p = n - p - k := by
            rw [Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega : n - p - k < p)
          rw [h1, h3]
          have h_choose_zero : choose (2 * (n - p - k) - p) (n - p - k) = 0 := choose_eq_zero_of_lt (by omega)
          rw [h_choose_zero]
          push_cast
          rw [MulZeroClass.zero_mul]
        have h_choose2nkp : (choose (2 * (n - (k + p))) (n - (k + p)) : ZMod p) = 0 := by
          have h_eq : n - (k + p) = n - p - k := by omega
          rw [h_eq]
          have hk1 : (p - 1) / 2 < n - p - k := by
            have h_two : 0 < 2 := by decide
            rw [Nat.div_lt_iff_lt_mul h_two]
            omega
          exact choose_two_mul_self_eq_zero p (n - p - k) hk1 (by omega)
        rw [h_choose2nk, h_choose2nkp]
        ring
      · push_neg at h_2k h_2j
        have h_c2kp : (choose (2 * (k + p)) (k + p) : ZMod p) = 2 * (choose (2 * k) k : ZMod p) := by
          have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * k + 2 * p) (k := k + p) (p := p)
          rw [← ZMod.intCast_eq_intCast_iff] at h_eq
          push_cast at h_eq
          have h1 : (2 * k + 2 * p) % p = 2 * k := by
            have : 2 * k + 2 * p = 2 * k + p * 2 := by ring
            rw [this, Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega)
          have h2 : (2 * k + 2 * p) / p = 2 := by
            have h_eq2 : 2 * k + 2 * p = 2 * k + p * 2 := by ring
            rw [h_eq2]
            rw [Nat.add_mul_div_left (2 * k) 2 h_pos]
            have : 2 * k / p = 0 := Nat.div_eq_of_lt (by omega)
            rw [this, zero_add]
          have h3 : (k + p) % p = k := by
            rw [Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega : k < p)
          have h4 : (k + p) / p = 1 := by
            rw [Nat.add_div_right k h_pos]
            have : k / p = 0 := Nat.div_eq_of_lt (by omega)
            rw [this, zero_add]
          rw [h1, h2, h3, h4] at h_eq
          have h_choose_two : (Nat.choose 2 1 : ZMod p) = 2 := rfl
          rw [h_choose_two] at h_eq
          have h_num_eq : 2 * k + 2 * p = 2 * (k + p) := by ring
          rw [h_num_eq] at h_eq
          rw [h_eq]
          ring
        have h_c2nk : (choose (2 * (n - k)) (n - k) : ZMod p) = 2 * (choose (2 * (n - p - k)) (n - p - k) : ZMod p) := by
          have h_eq := Choose.choose_modEq_choose_mod_mul_choose_div (n := 2 * (n - p - k) + 2 * p) (k := n - p - k + p) (p := p)
          rw [← ZMod.intCast_eq_intCast_iff] at h_eq
          push_cast at h_eq
          have h_num_eq : 2 * (n - p - k) + 2 * p = 2 * (n - k) := by omega
          have h_den_eq : n - p - k + p = n - k := by omega
          have h1 : (2 * (n - p - k) + 2 * p) % p = 2 * (n - p - k) := by
            have : 2 * (n - p - k) + 2 * p = 2 * (n - p - k) + p * 2 := by ring
            rw [this, Nat.add_mul_mod_self_left]
            exact Nat.mod_eq_of_lt (by omega : 2 * (n - p - k) < p)
          have h2 : (2 * (n - p - k) + 2 * p) / p = 2 := by
            have h_eq2 : 2 * (n - p - k) + 2 * p = 2 * (n - p - k) + p * 2 := by ring
            rw [h_eq2]
            rw [Nat.add_mul_div_left (2 * (n - p - k)) 2 h_pos]
            have : 2 * (n - p - k) / p = 0 := Nat.div_eq_of_lt (by omega : 2 * (n - p - k) < p)
            rw [this, zero_add]
          have h3 : (n - p - k + p) % p = n - p - k := by
            rw [Nat.add_mod_right]
            exact Nat.mod_eq_of_lt (by omega : n - p - k < p)
          have h4 : (n - p - k + p) / p = 1 := by
            rw [Nat.add_div_right (n - p - k) h_pos]
            have : (n - p - k) / p = 0 := Nat.div_eq_of_lt (by omega)
            rw [this, zero_add]
          rw [h1, h2, h3, h4] at h_eq
          have h_choose_two : (Nat.choose 2 1 : ZMod p) = 2 := rfl
          rw [h_choose_two] at h_eq
          rw [h_num_eq, h_den_eq] at h_eq
          rw [h_eq]
          ring
        rw [h_choose_k, h_choose_kp, h_c2kp, h_c2nk]
        have h_c2nkp : (choose (2 * (n - (k + p))) (n - (k + p)) : ZMod p) = (choose (2 * (n - p - k)) (n - p - k) : ZMod p) := by
          have h_eq : n - (k + p) = n - p - k := by omega
          rw [h_eq]
        rw [h_c2nkp]
        have h_sign : (-1 : ZMod p) ^ (k + p) = - (-1 : ZMod p) ^ k := by
          rw [pow_add]
          have h_odd_pow : (-1 : ZMod p) ^ p = -1 := by
            have hp_eq : p = 2 * (p / 2) + 1 := by omega
            have h_pow_eq : (-1 : ZMod p) ^ p = (-1 : ZMod p) ^ (2 * (p / 2) + 1) := by congr 1
            rw [h_pow_eq]
            rw [pow_add, pow_mul]
            have : (-1 : ZMod p) ^ 2 = 1 := by ring
            rw [this, one_pow, one_mul, pow_one]
          rw [h_odd_pow]
          ring
        rw [h_sign]
        ring
  have h_sum_total : ∑ k ∈ range (n - p + 1), (
      (((-1 : ZMod p) ^ k) * ((choose n k : ZMod p) ^ 2) * (choose (2 * k) k : ZMod p) * (choose (2 * (n - k)) (n - k) : ZMod p)) +
      (((-1 : ZMod p) ^ (k + p)) * ((choose n (k + p) : ZMod p) ^ 2) * (choose (2 * (k + p)) (k + p) : ZMod p) * (choose (2 * (n - (k + p))) (n - (k + p)) : ZMod p))) = 0 := by
    rw [sum_congr rfl h_pair]
    simp
  rw [sum_add_distrib] at h_sum_total
  rw [← h_split]
  rw [← h_split2]
  rw [h_sum_zero1, add_zero]
  rw [h_shift]
  exact h_sum_total

theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  have hp_prime : Fact (Nat.Prime p) := ⟨hp⟩
  have h_odd_p : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h_odd
  constructor
  · rw [transfer_A_det p]
    have h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → (a (i.val + j.val) : ZMod p) = 0 := by
      intro i j hij
      exact a_mod_p_eq_zero p hp h_odd (i.val + j.val) hij (by
        have : i.val < p := i.is_lt
        have : j.val < p := j.is_lt
        omega)
    rw [det_eq_single p (fun i j => (a (i.val + j.val) : ZMod p)) h_zero]
    have h_prod : ∏ i : Fin p, (a ((σ_anti p i).val + i.val) : ZMod p) = 1 := by
      have h_all : ∀ i : Fin p, (a ((σ_anti p i).val + i.val) : ZMod p) = 1 := by
        intro i
        have h_sum_idx : (σ_anti p i).val + i.val = p - 1 := by
          unfold σ_anti
          dsimp
          omega
        rw [h_sum_idx]
        exact a_p_sub_one_eq_one p h_odd
      rw [Finset.prod_congr rfl (fun i _ => h_all i)]
      simp
    rw [h_prod, mul_one]
    have h_sign_cast : (Equiv.Perm.sign (σ_anti_equiv p) : ZMod p) = (-1 : ZMod p) ^ (p * (p - 1) / 2) := by
      have h := sign_σ_anti_equiv p
      have h_cast := congr_arg (fun (x : ℤ) => (x : ZMod p)) h
      push_cast at h_cast
      exact h_cast
    rw [h_sign_cast]
    have h_neg_one_pow : (-1 : ZMod p) ^ (p * (p - 1) / 2) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
      exact neg_one_pow_p_mul_sub_one_div_two p h_odd_p
    rw [h_neg_one_pow]
  · rw [transfer_C_det p]
    have h_zero : ∀ i j : Fin p, i.val + j.val ≥ p → (c (i.val + j.val) : ZMod p) = 0 := by
      intro i j hij
      exact c_mod_p_eq_zero p hp h_odd (i.val + j.val) hij (by
        have : i.val < p := i.is_lt
        have : j.val < p := j.is_lt
        omega)
    rw [det_eq_single p (fun i j => (c (i.val + j.val) : ZMod p)) h_zero]
    have h_prod : ∏ i : Fin p, (c ((σ_anti p i).val + i.val) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
      have h_all : ∀ i : Fin p, (c ((σ_anti p i).val + i.val) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
        intro i
        have h_sum_idx : (σ_anti p i).val + i.val = p - 1 := by
          unfold σ_anti
          dsimp
          omega
        rw [h_sum_idx]
        exact c_p_sub_one_eq_neg_one_pow p h_odd
      rw [Finset.prod_congr rfl (fun i _ => h_all i)]
      simp
    rw [h_prod]
    have h_sign_cast : (Equiv.Perm.sign (σ_anti_equiv p) : ZMod p) = (-1 : ZMod p) ^ (p * (p - 1) / 2) := by
      have h := sign_σ_anti_equiv p
      have h_cast := congr_arg (fun (x : ℤ) => (x : ZMod p)) h
      push_cast at h_cast
      exact h_cast
    rw [h_sign_cast]
    have h_neg_one_pow : (-1 : ZMod p) ^ (p * (p - 1) / 2) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
      exact neg_one_pow_p_mul_sub_one_div_two p h_odd_p
    rw [h_neg_one_pow]
    have h_mul : (-1 : ZMod p) ^ ((p - 1) / 2) * (-1 : ZMod p) ^ ((p - 1) / 2) = 1 := by
      rw [← pow_add]
      have h_add : (p - 1) / 2 + (p - 1) / 2 = p - 1 := by
        omega
      rw [h_add]
      have : (-1 : ZMod p) ^ (p - 1) = 1 := by
        have : p - 1 = 2 * ((p - 1) / 2) := by omega
        rw [this, pow_mul]
        have : (-1 : ZMod p) ^ 2 = 1 := by ring
        rw [this, one_pow]
      exact this
    exact h_mul
