import FormalConjecturesUtil

/-! A finite collision bound for randomly assigning nonnegative masses to
boxes. This module does not assert an arithmetic correlation estimate. -/
namespace Erdos371.RandomBins
open Finset

section Energy
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

noncomputable def boxMass (w : ι → ℝ) (a : ι → κ) (c : κ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => a i = c), w i

noncomputable def collisionEnergy (w : ι → ℝ) (a : ι → κ) : ℝ :=
  ∑ i : ι, ∑ j : ι, if i ≠ j ∧ a i = a j then w i*w j else 0

lemma collisionEnergy_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a : ι → κ) :
    0 ≤ collisionEnergy w a := by
  apply sum_nonneg
  intro i hi
  apply sum_nonneg
  intro j hj
  split_ifs
  · exact mul_nonneg (hw i) (hw j)
  · exact le_rfl

omit [Fintype ι] in
lemma finite_square_split (w : ι → ℝ) (S : Finset ι) :
    (∑ i ∈ S, w i)^2 = (∑ i ∈ S, (w i)^2) +
      ∑ i ∈ S, ∑ j ∈ S, if i ≠ j then w i*w j else 0 := by
  rw [pow_two,sum_mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hpoint (j : ι) : w i*w j =
      (if i = j then (w i)^2 else 0) + (if i ≠ j then w i*w j else 0) := by
    by_cases h : i = j
    · subst j; simp [pow_two]
    · simp [h]
  calc
    _ = ∑ j ∈ S, ((if i = j then (w i)^2 else 0) + (if i ≠ j then w i*w j else 0)) :=
      sum_congr rfl (fun j hj => hpoint j)
    _ = _ := by rw [sum_add_distrib,sum_ite_eq,if_pos hi]

lemma box_collision_le_total (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (a : ι → κ) (c : κ) :
    (boxMass w a c)^2 - (∑ i ∈ univ.filter (fun i => a i = c), (w i)^2) ≤
      collisionEnergy w a := by
  rw [boxMass,finite_square_split,add_sub_cancel_left]
  simp only [sum_filter,collisionEnergy]
  apply sum_le_sum
  intro i hi
  by_cases hic : a i = c
  · rw [if_pos hic]
    apply sum_le_sum
    intro j hj
    by_cases hjc : a j = c
    · simp only [if_pos hjc,show a i = a j from hic.trans hjc.symm,and_true]
      exact le_rfl
    · rw [if_neg hjc]
      split_ifs
      · exact mul_nonneg (hw i) (hw j)
      · exact le_rfl
  · rw [if_neg hic]
    apply sum_nonneg
    intro j hj
    split_ifs
    · exact mul_nonneg (hw i) (hw j)
    · exact le_rfl

/-- If no atom is closer than delta to the box threshold, any overflowing
box forces at least u*delta units of ordered-pair collision energy. -/
lemma overflow_collision_lower (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u δ : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hmax : ∀ i, w i ≤ u-δ)
    (a : ι → κ) (hbad : ∃ c, u < boxMass w a c) :
    u*δ ≤ collisionEnergy w a := by
  obtain ⟨c,hc⟩ := hbad
  have hdiag : (∑ i ∈ univ.filter (fun i => a i = c), (w i)^2) ≤
      (u-δ)*boxMass w a c := by
    rw [boxMass,mul_sum]
    apply sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (hmax i) (hw i)
    nlinarith
  have henergy := box_collision_le_total w hw a c
  have hprod := mul_nonneg (sub_nonneg.mpr hc.le)
    (show 0 ≤ boxMass w a c + δ by linarith)
  nlinarith
end Energy

section Random
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma assignment_pair_collision_sum (K : ℕ) (hK : 0 < K) (i j : ι) (hij : i ≠ j) :
    (∑ a : ι → Fin K, if a i = a j then (1 : ℝ) else 0) =
      (Fintype.card (ι → Fin K) : ℝ)/K := by
  let e := Equiv.piSplitAt i (fun _ : ι => Fin K)
  have hs : (∑ a : ι → Fin K, if a i = a j then (1 : ℝ) else 0) =
      Fintype.card ({x : ι // x ≠ i} → Fin K) := by
    rw [← e.symm.sum_comp (fun a : ι → Fin K => if a i = a j then (1 : ℝ) else 0)]
    rw [Fintype.sum_prod_type,sum_comm]
    simp only [e,Equiv.piSplitAt_symm_apply,dif_neg hij.symm,dite_true]
    simp only [sum_ite_eq',mem_univ,if_true,sum_const,card_univ,nsmul_eq_mul,mul_one]
  have hc : Fintype.card (ι → Fin K) =
      K * Fintype.card ({x : ι // x ≠ i} → Fin K) := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr e
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [hs,hc,Nat.cast_mul]
  field_simp

/-- The mean collision energy is at most the squared total mass divided by K. -/
lemma collisionEnergy_sum_le (K : ℕ) (hK : 0 < K) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    (∑ a : ι → Fin K, collisionEnergy w a) ≤
      ((Fintype.card (ι → Fin K) : ℝ)/K)*(∑ i, w i)^2 := by
  unfold collisionEnergy
  rw [sum_comm]
  have hpair (i j : ι) :
      (∑ a : ι → Fin K, if i ≠ j ∧ a i = a j then w i*w j else 0) ≤
        ((Fintype.card (ι → Fin K) : ℝ)/K)*(w i*w j) := by
    by_cases hij : i = j
    · subst j
      simp only [ne_eq,not_true_eq_false,false_and,if_false,sum_const_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (hw i) (hw i))
    · simp only [hij,ne_eq,not_false_eq_true,true_and]
      have he : (∑ a : ι → Fin K, if a i = a j then w i*w j else 0) =
          (∑ a : ι → Fin K, if a i = a j then (1 : ℝ) else 0)*(w i*w j) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro a ha
        split_ifs <;> simp
      rw [he,assignment_pair_collision_sum K hK i j hij]
  calc
    _ = ∑ i : ι, ∑ j : ι, ∑ a : ι → Fin K,
        if i ≠ j ∧ a i = a j then w i*w j else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ ≤ ∑ i : ι, ∑ j : ι, ((Fintype.card (ι → Fin K) : ℝ)/K)*(w i*w j) := by
      apply sum_le_sum
      intro i hi
      exact sum_le_sum fun j hj => hpair i j
    _ = _ := by simp_rw [← mul_sum]; rw [← sum_mul]; ring

noncomputable def overflowCount (K : ℕ) (w : ι → ℝ) (u : ℝ) : ℕ := by
  classical
  exact (univ.filter fun a : ι → Fin K => ∃ c, u < boxMass w a c).card

/-- Finite random-bin estimate, uniform in the number and sizes of the atoms.
It is the proportion of assignments with at least one overflowing box. -/
theorem overflow_fraction_le (K : ℕ) (hK : 0 < K) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (htotal : (∑ i, w i) ≤ 1)
    (u δ : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hmax : ∀ i, w i ≤ u-δ) :
    (overflowCount K w u : ℝ)/Fintype.card (ι → Fin K) ≤ 1/((K : ℝ)*u*δ) := by
  classical
  letI : NeZero K := ⟨hK.ne'⟩
  have hC : (0 : ℝ) < Fintype.card (ι → Fin K) := by
    exact_mod_cast Fintype.card_pos (α := ι → Fin K)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hpoint (a : ι → Fin K) :
      (if ∃ c, u < boxMass w a c then (u*δ) else 0) ≤ collisionEnergy w a := by
    split_ifs with h
    · exact overflow_collision_lower w hw u δ hu hδ hmax a h
    · exact collisionEnergy_nonneg w hw a
  have hs := sum_le_sum (s := univ) (fun a ha => hpoint a)
  have he : (∑ a : ι → Fin K, if ∃ c, u < boxMass w a c then (u*δ) else 0) =
      (overflowCount K w u : ℝ)*(u*δ) := by
    simp only [← sum_filter,sum_const,nsmul_eq_mul,overflowCount]
  rw [he] at hs
  have henergy := collisionEnergy_sum_le K hK w hw
  have hmass : (∑ i, w i)^2 ≤ 1 := by
    have hn : 0 ≤ ∑ i, w i := sum_nonneg (fun i hi => hw i)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (Fintype.card (ι → Fin K) : ℝ)/K by positivity)
  rw [mul_one] at hm
  have hb : (overflowCount K w u : ℝ)*(u*δ) ≤ (Fintype.card (ι → Fin K) : ℝ)/K :=
    hs.trans (henergy.trans hm)
  apply (div_le_iff₀ hC).mpr
  apply (le_div_iff₀ (mul_pos hu hδ)).mpr at hb
  convert hb using 1
  field_simp

#print axioms overflow_collision_lower
#print axioms assignment_pair_collision_sum
#print axioms collisionEnergy_sum_le
#print axioms overflow_fraction_le
end Random
end Erdos371.RandomBins
