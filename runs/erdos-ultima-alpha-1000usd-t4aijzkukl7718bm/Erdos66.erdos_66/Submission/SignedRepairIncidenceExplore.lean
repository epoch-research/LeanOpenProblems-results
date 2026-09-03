import Submission.UnrestrictedRepairIncidenceExplore

/-! Exact signed repair accounting. Unlike monotone repair, both insertions
and deletions are allowed. These identities are not a construction of a
logarithmic representation limit. -/
namespace Erdos66SignedRepairIncidence
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66UnrestrictedRepairIncidence
open scoped Classical
set_option maxHeartbeats 1600000

noncomputable def midpointDegree (A B T : Finset ℕ) (x : ℕ) : ℝ :=
  (targetDegree A T x : ℝ)+targetDegree B T x

noncomputable def signedMass (A B T : Finset ℕ) : ℝ :=
  ∑ n∈T, ((sumRep (B : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n)

lemma sum_degrees (A B T : Finset ℕ) :
    (∑ x∈A, (targetDegree B T x : ℝ))=∑ n∈T, (pairs A B n : ℝ) := by
  exact_mod_cast (sum_pairs_eq_degrees A B T).symm

lemma midpointDegree_union_inter (A B T : Finset ℕ) (x : ℕ) :
    midpointDegree A B T x=
      (targetDegree (A∪B) T x : ℝ)+targetDegree (A∩B) T x := by
  unfold midpointDegree targetDegree
  rw [Finset.filter_union,Finset.filter_inter_distrib]
  exact_mod_cast (Finset.card_union_add_card_inter
    (A.filter (fun b ↦ x+b∈T)) (B.filter (fun b ↦ x+b∈T))).symm

/-- All new/new, old/new, deleted/deleted, and common-point contributions
are included, without any restriction on point sharing. -/
theorem signed_incidence_identity (A B T : Finset ℕ) :
    signedMass A B T =
      (∑ x∈B\A, midpointDegree A B T x)-∑ x∈A\B, midpointDegree A B T x := by
  rw [Finset.sum_sdiff_sub_sum_sdiff]
  simp only [midpointDegree,Finset.sum_add_distrib,sum_degrees,signedMass,Finset.sum_sub_distrib]
  simp_rw [pairs_comm B A,pairs_self]
  ring

lemma card_difference (A B : Finset ℕ) :
    ((B\A).card : ℝ)-(A\B).card=(B.card : ℝ)-A.card := by
  simpa using (Finset.sum_sdiff_sub_sum_sdiff (s₁ := A) (s₂ := B) (f := fun _ ↦ (1 : ℝ)))

/-- Centering the incidence field leaves a cardinality imbalance term. -/
theorem centered_signed_identity (A B T : Finset ℕ) (b : ℝ) :
    signedMass A B T-b*((B.card : ℝ)-A.card)=
      (∑ x∈B\A, (midpointDegree A B T x-b))-
        ∑ x∈A\B, (midpointDegree A B T x-b) := by
  rw [signed_incidence_identity]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
  rw [←card_difference A B]
  ring

lemma abs_sum_bound (S : Finset ℕ) (f : ℕ → ℝ) (ε : ℝ)
    (h : ∀ x∈S, |f x| ≤ ε) : |∑ x∈S, f x| ≤ ε*S.card := by
  calc
    _ ≤ ∑ x∈S, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x∈S, ε := Finset.sum_le_sum h
    _ = _ := by simp [mul_comm]

/-- Uniform incidence regularity controls every signed edit by its number
of changed points. No small symmetric difference is assumed. -/
theorem centered_signed_bound (A B T : Finset ℕ) (b ε : ℝ)
    (hF : ∀ x∈B\A, |midpointDegree A B T x-b| ≤ ε)
    (hD : ∀ x∈A\B, |midpointDegree A B T x-b| ≤ ε) :
    |signedMass A B T-b*((B.card : ℝ)-A.card)| ≤
      ε*((B\A).card+(A\B).card) := by
  rw [centered_signed_identity]
  have h₁ := abs_sum_bound (B\A) _ ε hF
  have h₂ := abs_sum_bound (A\B) _ ε hD
  have hh := abs_sub (∑ x∈B\A, (midpointDegree A B T x-b))
    (∑ x∈A\B, (midpointDegree A B T x-b))
  nlinarith

lemma uniform_gain_mass (A B T : Finset ℕ) (d : ℝ)
    (hgain : ∀ n∈T, (sumRep (A : Set ℕ) n : ℝ)+d ≤ sumRep (B : Set ℕ) n) :
    d*T.card ≤ signedMass A B T := by
  calc
    _ = ∑ _n∈T, d := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun n hn ↦ by
      linarith [hgain n hn])

/-- A scaled version avoids divisions in the degree hypotheses. -/
theorem normalized_signed_budget (A B T : Finset ℕ) (hT : T.Nonempty)
    (δ L R β η : ℝ) (hL : 0<L) (hR : 0<R) (hη : 0≤η)
    (hgain : ∀ n∈T, (sumRep (A : Set ℕ) n : ℝ)+δ*L ≤ sumRep (B : Set ℕ) n)
    (hF : ∀ x∈B\A, |R*midpointDegree A B T x-β*T.card*L| ≤ η*T.card*L)
    (hD : ∀ x∈A\B, |R*midpointDegree A B T x-β*T.card*L| ≤ η*T.card*L) :
    δ*R ≤ β*((B.card : ℝ)-A.card)+η*(A.card+B.card) := by
  have hreg (x : ℕ) (hx : |R*midpointDegree A B T x-β*T.card*L| ≤ η*T.card*L) :
      |midpointDegree A B T x-β*T.card*L/R| ≤ η*T.card*L/R := by
    rw [show midpointDegree A B T x-β*T.card*L/R=
      (R*midpointDegree A B T x-β*T.card*L)/R by field_simp]
    rw [abs_div,abs_of_pos hR]
    exact (div_le_div_iff_of_pos_right hR).mpr hx
  have hb := (le_abs_self _).trans (centered_signed_bound A B T (β*T.card*L/R)
    (η*T.card*L/R) (fun x hx ↦ hreg x (hF x hx)) (fun x hx ↦ hreg x (hD x hx)))
  have hg := uniform_gain_mass A B T (δ*L) hgain
  have hcards : ((B\A).card : ℝ)+(A\B).card ≤ A.card+B.card := by
    have hf : ((B\A).card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have hd : ((A\B).card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    linarith
  have hc : (0 : ℝ)<T.card := by exact_mod_cast Finset.card_pos.mpr hT
  have he : η*T.card*L/R*((B\A).card+(A\B).card) ≤ η*T.card*L/R*(A.card+B.card) :=
    mul_le_mul_of_nonneg_left hcards (by positivity)
  have hh : δ*L*T.card ≤ β*T.card*L/R*((B.card : ℝ)-A.card)+η*T.card*L/R*(A.card+B.card) := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hh hR.le
  have heq : (β*T.card*L/R*((B.card : ℝ)-A.card)+η*T.card*L/R*(A.card+B.card))*R=
      (β*((B.card : ℝ)-A.card)+η*(A.card+B.card))*(T.card*L) := by
    field_simp
  rw [heq] at hm
  apply le_of_mul_le_mul_right (a := (T.card : ℝ)*L) _ (mul_pos hc hL)
  convert hm using 1 <;> ring

end Erdos66SignedRepairIncidence
