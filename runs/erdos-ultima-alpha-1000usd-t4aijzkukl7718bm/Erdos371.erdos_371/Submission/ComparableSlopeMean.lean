import Submission.SieveFactorMean

/-! Averaging the singular factor over comparable cofactor pairs. -/

namespace Erdos371
namespace FiniteSieve
open Finset

lemma sum_weighted_le_of_prefix_le (f g w : ℕ → ℝ)
    (hp : ∀ N, (∑ n ∈ range N, f n) ≤ ∑ n ∈ range N, g n)
    (hw0 : ∀ n, 0 ≤ w n) (hw : Antitone w) (N : ℕ) :
    (∑ n ∈ range N, w n * f n) ≤ ∑ n ∈ range N, w n * g n := by
  have hf := sum_range_by_parts w f N
  have hg := sum_range_by_parts w g N
  simp only [smul_eq_mul] at hf hg
  rw [hf, hg]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hp N) (hw0 _)
  · apply sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonpos_left (hp (n+1)) (sub_nonpos.mpr (hw (Nat.le_succ n)))

lemma slopeSieveFactor_weighted_second_moment (N : ℕ) :
    (∑ n ∈ Icc 1 N, (slopeSieveFactor n)^2 / (n : ℝ)) ≤
      Real.exp 16 * (harmonic N : ℝ) := by
  have h := sum_weighted_le_of_prefix_le (fun n => (slopeSieveFactor (n+1))^2)
    (fun _ => Real.exp 16) (fun n => 1/(n+1 : ℝ))
    (fun M => by simpa using slopeSieveFactor_second_moment M)
    (fun _ => by positivity) (fun m n hmn => one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hmn 1)) N
  have he : (∑ n ∈ range N, (1/(n+1 : ℝ)) * (slopeSieveFactor (n+1))^2) =
      ∑ n ∈ Icc 1 N, (slopeSieveFactor n)^2/(n : ℝ) := by
    have h := sum_Ico_add' (fun n : ℕ => (slopeSieveFactor n)^2/(n : ℝ)) 0 N 1
    simpa only [Nat.zero_add, Nat.Ico_zero_eq_range, Ico_add_one_right_eq_Icc,
      Nat.cast_add, Nat.cast_one, one_div_mul_eq_div] using h
  rw [he] at h
  have he' : (∑ n ∈ range N, (1/(n+1 : ℝ)) * Real.exp 16) = Real.exp 16 * (harmonic N : ℝ) := by
    simp [harmonic, mul_comm, ← sum_mul, one_div]
  rwa [he'] at h

lemma slopeSieveFactor_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    slopeSieveFactor (a*b) ≤ slopeSieveFactor a * slopeSieveFactor b := by
  unfold slopeSieveFactor
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold slopePrimeMass
  rw [Nat.primeFactors_mul ha hb]
  have h := sum_union_inter (s₁ := a.primeFactors) (s₂ := b.primeFactors)
    (f := fun p : ℕ => (1 : ℝ)/p)
  have hnonneg : 0 ≤ ∑ p ∈ a.primeFactors ∩ b.primeFactors, (1 : ℝ)/p :=
    sum_nonneg fun _ _ => by positivity
  linarith

lemma comparable_reciprocal_row_le (C X a : ℕ) (ha : 0 < a) :
    (∑ b ∈ Icc 1 X, if a ≤ C*b ∧ b ≤ C*a then (1 : ℝ)/b else 0) ≤ (C : ℝ)^2 := by
  classical
  let S := (Icc 1 X).filter fun b => a ≤ C*b ∧ b ≤ C*a
  have hc : S.card ≤ C*a := by
    have hsub : S ⊆ Icc 1 (C*a) := by
      intro b hb
      obtain ⟨hb, _, hba⟩ := mem_filter.mp hb
      exact mem_Icc.mpr ⟨(mem_Icc.mp hb).1, hba⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    _ = ∑ b ∈ S, (1 : ℝ)/b := (sum_filter _ _).symm
    _ ≤ ∑ _b ∈ S, (C : ℝ)/a := by
      apply sum_le_sum
      intro b hb
      obtain ⟨hb, hab, _⟩ := mem_filter.mp hb
      have hbR : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
      apply (div_le_div_iff₀ hbR haR).mpr
      simpa only [one_mul, Nat.cast_mul] using (show (a : ℝ) ≤ (C*b : ℕ) by exact_mod_cast hab)
    _ = (S.card : ℝ) * ((C : ℝ)/a) := by simp
    _ ≤ ((C*a : ℕ) : ℝ) * ((C : ℝ)/a) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = _ := by push_cast; field_simp

noncomputable def comparableSlopeSum (C X : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if a ≤ C*b ∧ b ≤ C*a then slopeSieveFactor (a*b)/((a : ℝ)*b) else 0

/-- Comparable cofactor pairs incur only one harmonic factor, not two. -/
theorem comparableSlopeSum_le (C X : ℕ) :
    comparableSlopeSum C X ≤ (C : ℝ)^2 * Real.exp 16 * (harmonic X : ℝ) := by
  classical
  let A : ℝ := ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
    if a ≤ C*b ∧ b ≤ C*a then (slopeSieveFactor a)^2/((a : ℝ)*b) else 0
  have hswap : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      if a ≤ C*b ∧ b ≤ C*a then (slopeSieveFactor b)^2/((a : ℝ)*b) else 0) = A := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    simp only [and_comm, mul_comm]
  have hpoint : 2*comparableSlopeSum C X ≤ A+A := by
    unfold comparableSlopeSum
    conv_rhs => rhs; rw [← hswap]
    dsimp [A]
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro b hb
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    have hb0 : 0 < b := (mem_Icc.mp hb).1
    split_ifs
    · have hprod := slopeSieveFactor_mul_le a b ha0.ne' hb0.ne'
      have hsq : 2*slopeSieveFactor (a*b) ≤ (slopeSieveFactor a)^2 + (slopeSieveFactor b)^2 := by
        nlinarith [sq_nonneg (slopeSieveFactor a - slopeSieveFactor b)]
      have hden : (0 : ℝ) ≤ (a : ℝ)*b := by positivity
      convert div_le_div_of_nonneg_right hsq hden using 1 <;> ring
    · simp
  have hA : A ≤ (C : ℝ)^2 * (∑ a ∈ Icc 1 X, (slopeSieveFactor a)^2/(a : ℝ)) := by
    dsimp [A]
    rw [mul_sum]
    apply sum_le_sum
    intro a ha
    have he : (∑ b ∈ Icc 1 X,
        if a ≤ C*b ∧ b ≤ C*a then (slopeSieveFactor a)^2/((a : ℝ)*b) else 0) =
        ((slopeSieveFactor a)^2/(a : ℝ)) *
          (∑ b ∈ Icc 1 X, if a ≤ C*b ∧ b ≤ C*a then (1 : ℝ)/b else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b hb
      split_ifs <;> ring
    rw [he, mul_comm ((C : ℝ)^2)]
    exact mul_le_mul_of_nonneg_left (comparable_reciprocal_row_le C X a (mem_Icc.mp ha).1) (by positivity)
  have hW := mul_le_mul_of_nonneg_left (slopeSieveFactor_weighted_second_moment X)
    (sq_nonneg (C : ℝ))
  nlinarith

lemma comparableSlopeSum_log_bound (C X : ℕ) :
    comparableSlopeSum C X ≤ (C : ℝ)^2 * Real.exp 16 * (1+Real.log X) := by
  exact (comparableSlopeSum_le C X).trans <|
    mul_le_mul_of_nonneg_left (harmonic_le_one_add_log X) (by positivity)

#print axioms comparableSlopeSum_log_bound
end FiniteSieve
end Erdos371
