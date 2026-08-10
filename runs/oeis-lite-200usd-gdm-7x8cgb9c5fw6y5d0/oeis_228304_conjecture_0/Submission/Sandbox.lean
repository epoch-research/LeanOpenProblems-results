import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

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

lemma transfer_A_det (p : ℕ) [hp : Fact (Nat.Prime p)] :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p] ↔
      (Matrix.det (fun i j : Fin p => (a (i.val + j.val) : ZMod p))) = (-1 : ZMod p) ^ half_minus_one := by
  intro N half_minus_one A
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  have h_det := Int.cast_det A
  change (A.det : ZMod p) = _ at h_det
  rw [h_det]
  rfl

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

