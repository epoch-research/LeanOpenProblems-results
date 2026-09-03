import Submission.SignedRepairStabilityExplore

/-! Aggregate quadratic incidence cost of unrestricted signed repairs.
Every new/new and deleted/deleted contribution is retained in the midpoint
field. The estimates do not themselves construct a repair. -/
namespace Erdos66SignedRepairEnergy
open Erdos66SignedRepairIncidence
open scoped Classical
open AdditiveCombinatorics
set_option maxHeartbeats 2200000

noncomputable def editCount (A B : Finset ℕ) : ℝ :=
  ((B\A).card : ℝ)+(A\B).card

noncomputable def editEnergy (A B T : Finset ℕ) (b : ℝ) : ℝ :=
  (∑ x∈B\A, (midpointDegree A B T x-b)^2)+
    ∑ x∈A\B, (midpointDegree A B T x-b)^2

lemma editCount_nonneg (A B : Finset ℕ) : 0≤editCount A B := by
  unfold editCount
  positivity

lemma editEnergy_nonneg (A B T : Finset ℕ) (b : ℝ) : 0≤editEnergy A B T b :=
  add_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma editCount_le_total (A B : Finset ℕ) : editCount A B ≤ (A.card : ℝ)+B.card := by
  have hA : ((A\B).card : ℝ)≤A.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hB : ((B\A).card : ℝ)≤B.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  unfold editCount
  linarith

lemma signed_sum_sq_bound (S U : Finset ℕ) (f g : ℕ → ℝ) :
    ((∑ x∈S, f x)-(∑ x∈U, g x))^2 ≤
      ((S.card : ℝ)+U.card)*((∑ x∈S, f x^2)+(∑ x∈U, g x^2)) := by
  have hh := sq_sum_le_card_mul_sum_sq (s := S.disjSum U)
    (f := Sum.elim f (fun x ↦ -g x))
  simpa only [Finset.sum_disjSum,Finset.card_disjSum,Nat.cast_add,Sum.elim_inl,Sum.elim_inr,
    neg_sq,Finset.sum_neg_distrib,sub_eq_add_neg] using hh

/-- Sharp Cauchy--Schwarz factor: only the changed points are charged. -/
theorem centered_signed_energy_bound (A B T : Finset ℕ) (b : ℝ) :
    (signedMass A B T-b*((B.card : ℝ)-A.card))^2 ≤
      editCount A B*editEnergy A B T b := by
  rw [centered_signed_identity]
  exact signed_sum_sq_bound (B\A) (A\B) _ _

noncomputable def normalizedEnergy (A B T : Finset ℕ) (L R β : ℝ) : ℝ :=
  R*editEnergy A B T (β*T.card*L/R)/((T.card : ℝ)*L)^2

lemma normalizedEnergy_nonneg (A B T : Finset ℕ) (L R β : ℝ) (hR : 0≤R) :
    0≤normalizedEnergy A B T L R β :=
  div_nonneg (mul_nonneg hR (editEnergy_nonneg _ _ _ _)) (sq_nonneg _)

/-- The normalized energy is the average squared normalized contrast over
changed points, with normalization by R rather than their cardinality. -/
lemma normalizedEnergy_eq (A B T : Finset ℕ) (L R β : ℝ)
    (hR : R≠0) (hT : (T.card : ℝ)*L≠0) :
    normalizedEnergy A B T L R β =
      ((∑ x∈B\A, (R*midpointDegree A B T x/(T.card*L)-β)^2)+
        ∑ x∈A\B, (R*midpointDegree A B T x/(T.card*L)-β)^2)/R := by
  have hcard := (mul_ne_zero_iff.mp hT).1
  have hL := (mul_ne_zero_iff.mp hT).2
  have he (x : ℕ) : (R*midpointDegree A B T x/(T.card*L)-β)^2=
      (R^2/((T.card : ℝ)*L)^2)*(midpointDegree A B T x-β*T.card*L/R)^2 := by
    field_simp
  simp only [he,←Finset.mul_sum,←mul_add,normalizedEnergy,editEnergy]
  field_simp

lemma normalized_centered_energy_bound (A B T : Finset ℕ) (L R β : ℝ)
    (hR : R≠0) (hT : (T.card : ℝ)*L≠0) :
    (signedMass A B T/(T.card*L)-β*((B.card : ℝ)-A.card)/R)^2 ≤
      (editCount A B/R)*normalizedEnergy A B T L R β := by
  have hcard := (mul_ne_zero_iff.mp hT).1
  have hL := (mul_ne_zero_iff.mp hT).2
  have hb := div_le_div_of_nonneg_right
    (centered_signed_energy_bound A B T (β*T.card*L/R)) (sq_nonneg ((T.card : ℝ)*L))
  have he : (signedMass A B T-β*T.card*L/R*((B.card : ℝ)-A.card))^2/((T.card : ℝ)*L)^2=
      (signedMass A B T/(T.card*L)-β*((B.card : ℝ)-A.card)/R)^2 := by
    field_simp
  rw [he] at hb
  convert hb using 1
  unfold normalizedEnergy
  field_simp

/-- No pointwise regularity is assumed: the entire squared contrast field
is the resource on the right-hand side. -/
theorem normalized_gain_energy_budget (A B T : Finset ℕ) (hT : T.Nonempty)
    (δ L R β : ℝ) (hL : 0<L) (hR : 0<R)
    (hgain : ∀ n∈T, (sumRep (A : Set ℕ) n : ℝ)+δ*L ≤ sumRep (B : Set ℕ) n) :
    δ ≤ β*((B.card : ℝ)-A.card)/R+
      Real.sqrt ((editCount A B/R)*normalizedEnergy A B T L R β) := by
  have hcard : (0 : ℝ)<T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have hTL : 0<(T.card : ℝ)*L := mul_pos hcard hL
  have hb := Real.le_sqrt_of_sq_le
    (normalized_centered_energy_bound A B T L R β hR.ne' hTL.ne')
  have hg : δ ≤ signedMass A B T/(T.card*L) := by
    apply (le_div_iff₀ hTL).mpr
    convert uniform_gain_mass A B T (δ*L) hgain using 1; ring
  linarith

end Erdos66SignedRepairEnergy
