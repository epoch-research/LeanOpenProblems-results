import Submission.CrtProductAverages

/-! Orthogonal residue-product functions for a quadratic upper-bound sieve. -/

namespace Erdos371
namespace FiniteSieve
open Finset
variable {ι : Type*}

noncomputable def residueBasisAt (q : ℕ) (R : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∈ R then 1-(q : ℝ)/R.card else 1

lemma residueBasisAt_sum (q : ℕ) (R : Finset ℕ) (hR : R ⊆ range q) (hr : 0 < R.card) :
    (∑ n ∈ range q, residueBasisAt q R n) = 0 := by
  classical
  have ht (n : ℕ) : residueBasisAt q R n = 1 - (q : ℝ)/R.card * (if n ∈ R then 1 else 0) := by
    unfold residueBasisAt
    split_ifs <;> ring
  have he : (range q).filter (· ∈ R) = R := by ext n; simp only [mem_filter]; tauto
  simp only [ht,sum_sub_distrib,← mul_sum,sum_boole,he,sum_const,card_range,nsmul_eq_mul,mul_one]
  have hr0 : (R.card : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

lemma residueBasisAt_sq_sum (q : ℕ) (R : Finset ℕ) (hR : R ⊆ range q) (hr : 0 < R.card) :
    (∑ n ∈ range q, (residueBasisAt q R n)^2) = q * (((q : ℝ)-R.card)/R.card) := by
  classical
  have ht (n : ℕ) : (residueBasisAt q R n)^2 = 1 +
      ((1-(q : ℝ)/R.card)^2-1) * (if n ∈ R then 1 else 0) := by
    unfold residueBasisAt
    split_ifs <;> ring
  have he : (range q).filter (· ∈ R) = R := by ext n; simp only [mem_filter]; tauto
  simp only [ht,sum_add_distrib,← mul_sum,sum_boole,he,sum_const,card_range,nsmul_eq_mul,mul_one]
  have hr0 : (R.card : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

lemma residueBasisAt_abs_le (q : ℕ) (R : Finset ℕ) (hR : R ⊆ range q) (hr : 0 < R.card) (n : ℕ) :
    |residueBasisAt q R n| ≤ q := by
  have hrc : R.card ≤ q := (card_le_card hR).trans_eq (card_range q)
  have hr0 : (0 : ℝ) < R.card := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ R.card := by exact_mod_cast hr
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hl : (1 : ℝ) ≤ (q : ℝ)/R.card := (le_div_iff₀ hr0).mpr (by simpa only [one_mul] using ((Nat.cast_le (α := ℝ)).mpr hrc))
  have hu : (q : ℝ)/R.card ≤ q := (div_le_iff₀ hr0).mpr (by nlinarith)
  unfold residueBasisAt
  split_ifs
  · rw [abs_le]
    constructor <;> linarith
  · simpa using hq

noncomputable def sieveBasis (s : ι → ℕ) (R : ι → Finset ℕ) (T : Finset ι) (n : ℕ) : ℝ :=
  ∏ i ∈ T, residueBasisAt (s i) (R i) (n % s i)

noncomputable def sieveBasisNorm (s : ι → ℕ) (R : ι → Finset ℕ) (T : Finset ι) : ℝ :=
  ∏ i ∈ T, (((s i : ℝ)-(R i).card)/(R i).card)

lemma sieveBasis_abs_le (s : ι → ℕ) (R : ι → Finset ℕ) (T : Finset ι)
    (hR : ∀ i ∈ T, R i ⊆ range (s i)) (hr : ∀ i ∈ T, 0 < (R i).card) (n : ℕ) :
    |sieveBasis s R T n| ≤ ∏ i ∈ T, (s i : ℝ) := by
  rw [sieveBasis,abs_prod]
  exact prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => residueBasisAt_abs_le _ _ (hR i hi) (hr i hi) _)

lemma sieveBasis_product_union [DecidableEq ι] (s : ι → ℕ) (R : ι → Finset ℕ)
    (T U : Finset ι) (n : ℕ) :
    sieveBasis s R T n * sieveBasis s R U n = ∏ i ∈ T ∪ U,
      ((if i ∈ T then residueBasisAt (s i) (R i) (n%s i) else 1) *
        (if i ∈ U then residueBasisAt (s i) (R i) (n%s i) else 1)) := by
  rw [prod_mul_distrib,Finset.prod_ite_mem,Finset.prod_ite_mem,
    union_inter_cancel_left,union_inter_cancel_right]
  rfl

lemma sieveBasis_covariance_period [DecidableEq ι] (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i)) (hr : ∀ i ∈ S, 0 < (R i).card)
    (T U : Finset ι) (hT : T ⊆ S) (hU : U ⊆ S) :
    (∑ n ∈ range (∏ i ∈ T ∪ U, s i), sieveBasis s R T n * sieveBasis s R U n) =
      (∏ i ∈ T ∪ U, (s i : ℝ)) * if T=U then sieveBasisNorm s R T else 0 := by
  classical
  let f : ι → ℕ → ℝ := fun i n =>
    (if i ∈ T then residueBasisAt (s i) (R i) n else 1) *
      (if i ∈ U then residueBasisAt (s i) (R i) n else 1)
  have hsub : T ∪ U ⊆ S := union_subset hT hU
  have he : (∑ n ∈ range (∏ i ∈ T ∪ U, s i), sieveBasis s R T n * sieveBasis s R U n) =
      ∏ i ∈ T ∪ U, ∑ n ∈ range (s i), f i n := by
    simp_rw [sieveBasis_product_union]
    exact sum_prod_residues_eq_prod_sum _ s f (fun i hi => hs i (hsub hi)) (hc.mono hsub)
  rw [he]
  by_cases hTU : T=U
  · subst U
    simp only [union_self,if_true]
    have hterm (i : ι) (hi : i ∈ T) : (∑ n ∈ range (s i), f i n) =
        (s i : ℝ)*(((s i : ℝ)-(R i).card)/(R i).card) := by
      simp only [f,if_pos hi,← pow_two]
      exact residueBasisAt_sq_sum _ _ (hR i (hT hi)) (hr i (hT hi))
    rw [prod_congr rfl hterm,prod_mul_distrib]
    rfl
  · rw [if_neg hTU,mul_zero]
    have hw : ∃ i, (i ∈ T ∧ i ∉ U) ∨ (i ∈ U ∧ i ∉ T) := by
      by_contra h
      push_neg at h
      apply hTU
      ext i
      specialize h i
      tauto
    obtain ⟨i,hi⟩ := hw
    have hiunion : i ∈ T ∪ U := by rcases hi with h | h <;> simp [h.1]
    apply prod_eq_zero hiunion
    rcases hi with hi | hi
    · simp only [f,if_pos hi.1,if_neg hi.2,mul_one]
      exact residueBasisAt_sum _ _ (hR i (hT hi.1)) (hr i (hT hi.1))
    · simp only [f,if_pos hi.1,if_neg hi.2,one_mul]
      exact residueBasisAt_sum _ _ (hR i (hU hi.1)) (hr i (hU hi.1))

lemma sieveBasis_covariance_error [DecidableEq ι] (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i)) (hr : ∀ i ∈ S, 0 < (R i).card)
    (T U : Finset ι) (hT : T ⊆ S) (hU : U ⊆ S) (Z : ℝ) (hZ : 0 ≤ Z)
    (hTZ : (∏ i ∈ T, (s i : ℝ)) ≤ Z) (hUZ : (∏ i ∈ U, (s i : ℝ)) ≤ Z) (N : ℕ) :
    |(∑ n ∈ range N, sieveBasis s R T n * sieveBasis s R U n) -
      N*(if T=U then sieveBasisNorm s R T else 0)| ≤ 2*Z^4 := by
  let Q := ∏ i ∈ T ∪ U, s i
  have hsub : T ∪ U ⊆ S := union_subset hT hU
  have hQ : 0 < Q := prod_pos fun i hi => Nat.pos_of_ne_zero (hs i (hsub hi))
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hper (V : Finset ι) (hV : V ⊆ T ∪ U) : Function.Periodic (sieveBasis s R V) Q := by
    intro n
    unfold sieveBasis
    apply prod_congr rfl
    intro i hi
    have hmod : (n+Q)%s i = n%s i := by
      rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd (dvd_prod_of_mem s (hV hi)),Nat.add_zero,Nat.mod_mod]
    rw [hmod]
  have hper' : Function.Periodic (fun n => sieveBasis s R T n*sieveBasis s R U n) Q := by
    intro n
    dsimp only
    rw [hper T subset_union_left n,hper U subset_union_right n]
  have hb (n : ℕ) : |sieveBasis s R T n*sieveBasis s R U n| ≤ Z^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul
      ((sieveBasis_abs_le s R T (fun i hi => hR i (hT hi)) (fun i hi => hr i (hT hi)) n).trans hTZ)
      ((sieveBasis_abs_le s R U (fun i hi => hR i (hU hi)) (fun i hi => hr i (hU hi)) n).trans hUZ)
      (abs_nonneg _) hZ
  have hQZ : (Q : ℝ) ≤ Z^2 := by
    have hinter : 1 ≤ ∏ i ∈ T ∩ U, s i := prod_pos fun i hi =>
      Nat.pos_of_ne_zero (hs i (hT (mem_inter.mp hi).1))
    have hmul : Q*(∏ i ∈ T ∩ U, s i) = (∏ i ∈ T, s i)*(∏ i ∈ U, s i) := prod_union_inter
    have hn : Q ≤ (∏ i ∈ T, s i)*(∏ i ∈ U, s i) := by nlinarith
    have hn' : (Q : ℝ) ≤ (∏ i ∈ T, (s i : ℝ))*(∏ i ∈ U, (s i : ℝ)) := by exact_mod_cast hn
    exact hn'.trans (by simpa only [pow_two] using mul_le_mul hTZ hUZ (prod_nonneg fun _ _ => Nat.cast_nonneg _) hZ)
  have he := sieveBasis_covariance_period S s R hs hc hR hr T U hT hU
  have herr := periodic_mean_error_bound _ Q hQ (Z^2) (sq_nonneg Z) hper' hb N
  have hperiod : (∑ n ∈ range Q, sieveBasis s R T n*sieveBasis s R U n) =
      (Q : ℝ)*(if T=U then sieveBasisNorm s R T else 0) := by
    simpa only [Q,Nat.cast_prod] using he
  rw [hperiod] at herr
  have hcenter : (N : ℝ)/Q*((Q : ℝ)*(if T=U then sieveBasisNorm s R T else 0)) =
      N*(if T=U then sieveBasisNorm s R T else 0) := by field_simp
  rw [hcenter] at herr
  exact herr.trans (by nlinarith [mul_le_mul_of_nonneg_right hQZ (sq_nonneg Z)])

#print axioms sieveBasis_covariance_period
#print axioms sieveBasis_covariance_error
end FiniteSieve
end Erdos371
