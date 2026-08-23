import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset
open scoped Nat

variable {p : ℕ}

lemma padicValRat_natCast (n : ℕ) :
    padicValRat p (n : ℚ) = padicValNat p n :=
  padicValRat.of_nat

lemma padicValRat_sum_ge {ι : Type*} (s : Finset ι) (f : ι → ℚ) (K : ℤ)
    (hf0 : ∀ i ∈ s, f i ≠ 0 → K ≤ padicValRat p (f i))
    (hsum0 : (∑ i ∈ s, f i) ≠ 0) :
    K ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp at hsum0
  | insert a s has ih =>
    rw [sum_insert has] at hsum0 ⊢
    by_cases hf : f a = 0
    · simp only [hf, zero_add] at hsum0 ⊢
      exact ih (fun i hi => hf0 i (mem_insert_of_mem hi)) hsum0
    · by_cases hs0 : (∑ i ∈ s, f i) = 0
      · simp only [hs0, add_zero] at hsum0 ⊢
        exact hf0 a (mem_insert_self _ _) hf
      · have hfa := hf0 a (mem_insert_self _ _) hf
        have hfs := ih (fun i hi => hf0 i (mem_insert_of_mem hi)) hs0
        exact le_trans (le_min hfa hfs) (padicValRat.min_le_padicValRat_add hsum0)

lemma padicValInt_one_le_of_dvd {z : ℤ} [Fact p.Prime] (hz : z ≠ 0)
    (hdiv : (p : ℤ) ∣ z) : 1 ≤ padicValInt p z := by
  have := (padicValInt_dvd_iff (p := p) 1 z).mp (by simpa using hdiv)
  exact this.resolve_left hz

lemma padicValRat_int_one_le {z : ℤ} [Fact p.Prime] (hz : z ≠ 0)
    (hdiv : (p : ℤ) ∣ z) : (1 : ℤ) ≤ padicValRat p (z : ℚ) := by
  have := padicValInt_one_le_of_dvd hz hdiv
  simpa [padicValRat.of_int] using this

lemma digits_mul_p (n : ℕ) [hp : Fact p.Prime] :
    (p.digits (n * p)).sum = (p.digits n).sum := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mul_comm, Nat.digits_base_mul hp.out.one_lt (succ_pos n)]
    simp

lemma padicValNat_choose_mul_prime (A B : ℕ) [hp : Fact p.Prime] (hBA : B ≤ A) :
    padicValNat p ((A * p).choose (B * p)) = padicValNat p (A.choose B) := by
  have h1 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p)
    (k := B * p) (n := A * p) (Nat.mul_le_mul_right p hBA)
  have h2 := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p)
    (k := B) (n := A) hBA
  have hsub : A * p - B * p = (A - B) * p := by
    rw [← Nat.sub_mul]
  rw [hsub, digits_mul_p A, digits_mul_p B, digits_mul_p (A - B)] at h1
  have hp1 : 0 < p - 1 := by
    have := hp.out.two_le
    omega
  exact Nat.mul_left_cancel hp1 (by linarith [h1, h2])

lemma choose_ratio_padicVal_zero (A B : ℕ) [hp : Fact p.Prime] (hBA : B ≤ A) :
    padicValRat p (((A * p).choose (B * p) : ℚ) / (A.choose B : ℚ)) = 0 := by
  have hpos : 0 < A.choose B := Nat.choose_pos hBA
  have hpos' : 0 < (A * p).choose (B * p) :=
    Nat.choose_pos (Nat.mul_le_mul_right p hBA)
  rw [padicValRat.div (Nat.cast_ne_zero.mpr hpos'.ne') (Nat.cast_ne_zero.mpr hpos.ne'),
    padicValRat_natCast, padicValRat_natCast, padicValNat_choose_mul_prime A B hBA, sub_self]

lemma pair_prod_eq_int (i t : ℕ) (hi : i ≤ p) :
    ((i + t * p : ℕ) : ℤ) * (((p - i) + t * p : ℕ) : ℤ) =
      (i : ℤ) * ((p - i : ℕ) : ℤ) + (t : ℤ) * (t + 1) * (p : ℤ) ^ 2 := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, Nat.cast_sub hi, Nat.cast_mul]
  ring

lemma mem_Icc_pred {k : ℕ} (hp : 0 < p) (hk : k ∈ Icc 1 (p - 1)) : k < p :=
  lt_of_le_of_lt (mem_Icc.mp hk).2 (Nat.pred_lt hp.ne')

lemma p_sub_mem_Icc {k : ℕ} (hp : 0 < p) (hk : k ∈ Icc 1 (p - 1)) :
    p - k ∈ Icc 1 (p - 1) := by
  have h := mem_Icc.mp hk
  exact mem_Icc.mpr ⟨Nat.sub_pos_of_lt (mem_Icc_pred hp hk), Nat.sub_le_sub_left h.1 _⟩

lemma injOn_p_sub' (hp : 0 < p) :
    Set.InjOn (fun k : ℕ => p - k) (Icc 1 (p - 1)) := by
  intro a ha b hb hab
  have ha' := mem_Icc_pred hp ha
  have hb' := mem_Icc_pred hp hb
  have hab' : p - a = p - b := hab
  calc a = p - (p - a) := (Nat.sub_sub_self ha'.le).symm
    _ = p - (p - b) := by rw [hab']
    _ = b := Nat.sub_sub_self hb'.le

lemma prod_comp_p_sub (t : ℕ) (hp : 0 < p) :
    ∏ i ∈ Icc 1 (p - 1), (((p - i) + t * p : ℕ) : ℤ) =
      ∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ) := by
  refine prod_nbij (fun i => p - i) (fun i hi => p_sub_mem_Icc hp hi) (injOn_p_sub' hp) ?_ ?_
  · intro i hi
    exact ⟨p - i, p_sub_mem_Icc hp hi, Nat.sub_sub_self (mem_Icc_pred hp hi).le⟩
  · intro i hi; rfl

lemma prod_pair_sq (t : ℕ) (hp : 0 < p) :
    (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) ^ 2 =
      ∏ i ∈ Icc 1 (p - 1),
        ((i : ℤ) * ((p - i : ℕ) : ℤ) + (t : ℤ) * (t + 1) * (p : ℤ) ^ 2) := by
  have hmul :
      (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) *
        (∏ i ∈ Icc 1 (p - 1), (((p - i) + t * p : ℕ) : ℤ)) =
      ∏ i ∈ Icc 1 (p - 1),
        ((i : ℤ) * ((p - i : ℕ) : ℤ) + (t : ℤ) * (t + 1) * (p : ℤ) ^ 2) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i hi => pair_prod_eq_int i t (mem_Icc_pred hp hi).le
  calc (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) ^ 2
      = (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) *
          (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) := by rw [pow_two]
    _ = (∏ i ∈ Icc 1 (p - 1), ((i + t * p : ℕ) : ℤ)) *
          (∏ i ∈ Icc 1 (p - 1), (((p - i) + t * p : ℕ) : ℤ)) := by
        rw [prod_comp_p_sub t hp]
    _ = ∏ i ∈ Icc 1 (p - 1),
          ((i : ℤ) * ((p - i : ℕ) : ℤ) + (t : ℤ) * (t + 1) * (p : ℤ) ^ 2) := hmul

def harmInv (q : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 (q - 1), (1 : ℚ) / k

lemma inv_i_mul_p_sub (i : ℕ) (hp : 0 < p) (hi : i ∈ Icc 1 (p - 1)) :
    (1 : ℚ) / (i * (p - i : ℕ)) =
      (1 / (p : ℚ)) * (1 / (i : ℚ) + 1 / ((p - i : ℕ) : ℚ)) := by
  have hilt : i < p := mem_Icc_pred hp hi
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hi).1)
  have hpi0 : ((p - i : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hilt))
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hcast : ((p - i : ℕ) : ℚ) = (p : ℚ) - i := Nat.cast_sub hilt.le
  have hsum : (i : ℚ) + ((p - i : ℕ) : ℚ) = p := by
    rw [hcast]; ring
  calc (1 : ℚ) / (i * (p - i : ℕ))
      = 1 / ((i : ℚ) * ((p - i : ℕ) : ℚ)) := by simp
    _ = ((i : ℚ) + ((p - i : ℕ) : ℚ)) / (p * ((i : ℚ) * ((p - i : ℕ) : ℚ))) := by
        rw [hsum]
        field_simp [hp0, hi0, hpi0]
    _ = (1 / (p : ℚ)) * (1 / (i : ℚ) + 1 / ((p - i : ℕ) : ℚ)) := by
        field_simp [hp0, hi0, hpi0]
        ring

lemma sum_inv_p_sub (hp : 0 < p) :
    ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / ((p - i : ℕ) : ℚ) =
      ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / i := by
  refine sum_nbij (fun i => p - i) (fun i hi => p_sub_mem_Icc hp hi) (injOn_p_sub' hp) ?_ ?_
  · intro i hi
    exact ⟨p - i, p_sub_mem_Icc hp hi, Nat.sub_sub_self (mem_Icc_pred hp hi).le⟩
  · intro i hi; rfl

lemma sum_inv_i_p_sub_i (hp : 0 < p) :
    ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / (i * (p - i : ℕ)) =
      (2 : ℚ) / p * harmInv p := by
  rw [sum_congr rfl (fun i hi => inv_i_mul_p_sub i hp hi), ← mul_sum, sum_add_distrib,
    sum_inv_p_sub hp, ← two_mul, harmInv]
  ring

lemma two_mul_harmInv (hp : 0 < p) :
    2 * harmInv p = (p : ℚ) * ∑ i ∈ Icc 1 (p - 1), (1 : ℚ) / (i * (p - i : ℕ)) := by
  have h := sum_inv_i_p_sub_i hp
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  field_simp [hp0] at h ⊢
  linarith [h]

def harmInv2 (q : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 (q - 1), (1 : ℚ) / (k : ℚ) ^ 2

lemma inv_sq_sub_pow {k : ℕ} [hp : Fact p.Prime] (hk : k ∈ Icc 1 (p - 1))
    (hne : (1 : ℚ) / (k : ℚ) ^ 2 - (k : ℚ) ^ (p - 3) ≠ 0) :
    padicValRat p ((1 : ℚ) / (k : ℚ) ^ 2 - (k : ℚ) ^ (p - 3)) ≥ 1 := by
  have hk0 : (k : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (mem_Icc.mp hk).1)
  have hilt : k < p := mem_Icc_pred hp.out.pos hk
  have hdiv : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hk).1 hilt
  have hdiff : (1 : ℚ) / (k : ℚ) ^ 2 - (k : ℚ) ^ (p - 3) =
      (1 - (k : ℚ) ^ (p - 1)) / (k : ℚ) ^ 2 := by
    have : p - 1 = (p - 3) + 2 := by omega
    rw [this, pow_add, pow_two]
    field_simp [hk0]
    ring
  rw [hdiff] at hne ⊢
  have hF : (p : ℤ) ∣ (k : ℤ) ^ (p - 1) - 1 := by
    have hcop : IsCoprime (k : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_nat_coprime]
      exact ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hdiv).symm
    have := Int.ModEq.pow_card_sub_one_eq_one hp.out hcop
    rw [Int.modEq_iff_dvd] at this
    simpa [← dvd_neg] using this
  have hk2 : (k : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hk0
  have h0 : (1 : ℚ) - (k : ℚ) ^ (p - 1) ≠ 0 := by
    intro h
    exact hne (by simp [h])
  rw [padicValRat.div h0 hk2, padicValRat.pow hk0]
  have hkval : padicValRat p (k : ℚ) = 0 := by
    rw [padicValRat_natCast, padicValNat.eq_zero_of_not_dvd hdiv]
    rfl
  rw [hkval, mul_zero, sub_zero]
  have hZ : ((k : ℤ) ^ (p - 1) - 1 : ℤ) ≠ 0 := by
    intro hz
    apply h0
    have : (k : ℚ) ^ (p - 1) = 1 := by
      have h' : ((k : ℤ) ^ (p - 1) : ℚ) = 1 := by
        rw [show (k : ℤ) ^ (p - 1) = (1 : ℤ) from sub_eq_zero.mp hz]
        simp
      simpa [Int.cast_pow] using h'
    linarith
  have heq : (1 : ℚ) - (k : ℚ) ^ (p - 1) = -(((k : ℤ) ^ (p - 1) - 1 : ℤ) : ℚ) := by
    rw [Int.cast_sub, Int.cast_pow, Int.cast_one, Int.cast_natCast]
    ring
  rw [heq, padicValRat.neg]
  exact padicValRat_int_one_le hZ hF

lemma sum_pow_residues_zero {j : ℕ} [hp : Fact p.Prime] (hj : ¬ (p - 1) ∣ j) :
    (p : ℤ) ∣ ∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ j := by
  -- reduce to ZMod p
  have : (∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ j) = 0 := by
    -- use FiniteField.sum_pow_units
    let _ : DecidableEq (ZMod p) := inferInstance
    have hsum := FiniteField.sum_pow_units (K := ZMod p) (i := j)
    -- identify the sum over Icc with the sum over units
    have himg :
        (∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ j) =
          ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ j := by
      let emb : (ZMod p)ˣ ↪ ZMod p := ⟨fun u => (u : ZMod p), Units.val_injective⟩
      have hset : (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)) = univ.map emb := by
        ext x
        simp only [mem_image, mem_Icc, mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and,
          emb]
        constructor
        · rintro ⟨k, ⟨hk1, hkp⟩, rfl⟩
          refine ⟨Units.mk0 (k : ZMod p) ?_, rfl⟩
          rw [ne_eq, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt hk1 (lt_of_le_of_lt hkp (Nat.pred_lt hp.out.ne_zero))
        · rintro ⟨u, rfl⟩
          refine ⟨(u : ZMod p).val, ?_, ZMod.natCast_zmod_val _⟩
          have hval := ZMod.val_lt (u : ZMod p)
          have hpos : 0 < (u : ZMod p).val := by
            rw [Nat.pos_iff_ne_zero]
            intro h
            have : (u : ZMod p) = 0 := by
              have := ZMod.natCast_zmod_val (u : ZMod p)
              rw [h] at this
              simpa using this.symm
            exact Units.ne_zero u this
          exact ⟨hpos, Nat.le_pred_of_lt hval⟩
      have h1 : (∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ j) =
          ∑ x ∈ (Icc 1 (p - 1)).image (fun k : ℕ => (k : ZMod p)), x ^ j := by
        rw [sum_image]
        intro a ha b hb hab
        have ha' : a < p := mem_Icc_pred hp.out.pos ha
        have hb' : b < p := mem_Icc_pred hp.out.pos hb
        have := congrArg ZMod.val hab
        simpa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] using this
      rw [h1, hset, sum_map]
      simp [emb]
    rw [himg]
    simpa [ZMod.card, hj] using hsum
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by
    rw [Int.cast_sum]
    simpa [Int.cast_pow, Int.cast_natCast] using this)

lemma harmInv2_val_ge_one [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    1 ≤ padicValRat p (harmInv2 p) ∨ harmInv2 p = 0 := by
  have hp3 : 3 ≤ p := le_trans (by decide : 3 ≤ 5) hp5
  have hdiv : ¬ (p - 1) ∣ (p - 3) := by
    intro h
    have hpos : 0 < p - 3 := by omega
    have := Nat.le_of_dvd hpos h
    omega
  have hint : (p : ℤ) ∣ ∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ (p - 3) :=
    sum_pow_residues_zero hdiv
  -- harmInv2 - ∑ k^{p-3} has val ≥ 1, and ∑ k^{p-3} has val ≥ 1
  have hterms : ∀ k ∈ Icc 1 (p - 1),
      (1 : ℚ) / (k : ℚ) ^ 2 - (k : ℚ) ^ (p - 3) ≠ 0 →
        1 ≤ padicValRat p ((1 : ℚ) / (k : ℚ) ^ 2 - (k : ℚ) ^ (p - 3)) :=
    fun k hk hne => inv_sq_sub_pow hk hne
  set S := harmInv2 p - ∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3)
  have hSeq : S = ∑ k ∈ Icc 1 (p - 1),
      ((1 : ℚ) / (k : ℚ) ^ 2 - (k : ℚ) ^ (p - 3)) := by
    simp [S, harmInv2, sum_sub_distrib]
  by_cases hS0 : S = 0
  · -- harmInv2 = ∑ k^{p-3}, which is an integer divisible by p
    have : harmInv2 p = ∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3) := by
      linarith [hS0]
    have hz : ((∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ (p - 3) : ℤ) : ℚ) =
        ∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3) := by
      simp [Int.cast_sum, Int.cast_pow]
    rw [this, ← hz]
    by_cases hz0 : (∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ (p - 3) : ℤ) = 0
    · right; simp [hz0]
    · left
      exact padicValRat_int_one_le hz0 (by simpa using hint)
  · have hSval : 1 ≤ padicValRat p S := by
      rw [hSeq] at hS0 ⊢
      exact padicValRat_sum_ge _ _ 1 hterms hS0
    have hP : ((∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ (p - 3) : ℤ) : ℚ) =
        ∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3) := by
      simp [Int.cast_sum, Int.cast_pow]
    have hharm : harmInv2 p = S + ∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3) := by
      simp [S]
    rw [hharm]
    by_cases hsum0 : (∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3)) = 0
    · simpa [hsum0] using Or.inl hSval
    · have hPval : 1 ≤ padicValRat p (∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3)) := by
        rw [← hP]
        have hz0 : (∑ k ∈ Icc 1 (p - 1), (k : ℤ) ^ (p - 3) : ℤ) ≠ 0 := by
          intro h; apply hsum0; simp [← hP, h]
        exact padicValRat_int_one_le hz0 (by simpa using hint)
      by_cases htot : S + ∑ k ∈ Icc 1 (p - 1), (k : ℚ) ^ (p - 3) = 0
      · exact Or.inr htot
      · exact Or.inl (le_trans (le_min hSval hPval) (padicValRat.min_le_padicValRat_add htot))

