import Submission.CompletionRelativeDisplacement
import Submission.CyclicSieveCount

/-! Full-period displacement cancellation for the actual coverage covariance.
The period is the product of the selected primes, not their sum. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling ParityDiscrepancy
set_option maxHeartbeats 2200000

noncomputable def populationCoverFlag (P S : Finset ℕ) (r : Phase P) : ℝ :=
  if ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val then 1 else 0

lemma populationCoverFlag_nonneg (P S : Finset ℕ) (r : Phase P) :
    0 ≤ populationCoverFlag P S r := by
  unfold populationCoverFlag
  split_ifs <;> norm_num

lemma populationCoverFlag_union (P S T : Finset ℕ) (r : Phase P) :
    populationCoverFlag P (S ∪ T) r = populationCoverFlag P S r*populationCoverFlag P T r := by
  classical
  simp only [populationCoverFlag,forall_mem_union]
  split_ifs <;> simp_all

lemma populationCoverFlag_image_add (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) (r : Phase P) :
    populationCoverFlag P (S.image (fun x => d+x))
      (affinePhaseEquiv P hP d 1 (fun _ _ => Nat.coprime_one_left _) r) =
        populationCoverFlag P S r := by
  unfold populationCoverFlag
  simp only [← population_empty_iff, populationSurvivors_image_add, image_eq_empty]

lemma populationCoveredFraction_union_flag (P S T : Finset ℕ) :
    populationCoveredFraction (S ∪ T) P =
      phaseMean P (fun r => populationCoverFlag P S r*populationCoverFlag P T r) := by
  simp_rw [← populationCoverFlag_union]
  rfl

/-- Translating any fixed phase through a full CRT period enumerates every
phase exactly once. -/
noncomputable def displacementPhaseEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : Phase P) : Fin (primeProduct P) ≃ Phase P := by
  let f : Fin (primeProduct P) → Phase P := fun d =>
    affinePhaseEquiv P hP d.val 1 (fun _ _ => Nat.coprime_one_left _) r
  have hf : Function.Injective f := by
    intro a b hab
    have hh : a.val ≡ b.val [MOD primeProduct P] := by
      apply CyclicSieve.product_modEq P hP
      intro p hp
      have he := congrArg (fun s : Phase P => (s ⟨p,hp⟩).val) hab
      simp only [f,affinePhaseEquiv_val,one_mul] at he
      exact Nat.ModEq.add_right_cancel' (r ⟨p,hp⟩).val he
    exact Fin.ext (hh.eq_of_lt_of_lt a.isLt b.isLt)
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf,by rw [Fintype.card_fin,CyclicSieve.phase_card]⟩)

lemma phaseMean_full_displacement (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : Phase P) (f : Phase P → ℝ) :
    residueMean (primeProduct P) (fun d => f
      (affinePhaseEquiv P hP d.val 1 (fun _ _ => Nat.coprime_one_left _) r)) = phaseMean P f := by
  have hs := (displacementPhaseEquiv P hP r).sum_comp f
  unfold residueMean phaseMean
  rw [show (∑ d : Fin (primeProduct P), f
      (affinePhaseEquiv P hP d.val 1 (fun _ _ => Nat.coprime_one_left _) r)) =
      ∑ s : Phase P, f s from hs]
  congr 1
  rw [prod_coe_sort P (fun p : ℕ => (p : ℝ))]
  simp only [primeProduct,Nat.cast_prod]

lemma population_joint_translation_flag (P S T : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) :
    populationCoveredFraction (S ∪ T.image (fun x => d+x)) P =
      phaseMean P (fun r =>
        populationCoverFlag P S
          (affinePhaseEquiv P hP d 1 (fun _ _ => Nat.coprime_one_left _) r)*
        populationCoverFlag P T r) := by
  rw [populationCoveredFraction_union_flag]
  conv_lhs => rw [← phaseMean_equiv P
    (affinePhaseEquiv P hP d 1 (fun _ _ => Nat.coprime_one_left _))]
  simp only [populationCoverFlag_image_add]

/-- The full displacement average of joint coverage factors exactly. No
claim is made that a shorter displacement range has this property. -/
theorem populationCoveredFraction_full_displacement (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    residueMean (primeProduct P) (fun d =>
      populationCoveredFraction (S ∪ T.image (fun x => d.val+x)) P) =
        populationCoveredFraction S P*populationCoveredFraction T P := by
  simp_rw [population_joint_translation_flag P S T hP]
  unfold residueMean
  rw [← phaseMean_sum, ← phaseMean_div]
  have he (r : Phase P) :
      (∑ d : Fin (primeProduct P), populationCoverFlag P S
        (affinePhaseEquiv P hP d.val 1 (fun _ _ => Nat.coprime_one_left _) r)*
        populationCoverFlag P T r)/(primeProduct P : ℝ) =
          populationCoveredFraction S P*populationCoverFlag P T r := by
    rw [← sum_mul, mul_div_right_comm]
    rw [show (∑ d : Fin (primeProduct P), populationCoverFlag P S
        (affinePhaseEquiv P hP d.val 1 (fun _ _ => Nat.coprime_one_left _) r))/
        (primeProduct P : ℝ) = populationCoveredFraction S P from
      phaseMean_full_displacement P hP r (populationCoverFlag P S)]
  simp_rw [he]
  rw [phaseMean_mul]
  rfl

/-- Full covariance cancellation, including every recursive child term. -/
theorem coverageCovariance_full_displacement (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    residueMean (primeProduct P) (fun d =>
      coverageCovariance P S (T.image (fun x => d.val+x))) = 0 := by
  unfold coverageCovariance
  simp_rw [populationCoveredFraction_image_add P T hP]
  rw [residueMean_sub,populationCoveredFraction_full_displacement P S T hP,
    residueMean_const _ (primeProduct_pos P (fun p hp => (hP p hp).pos)),sub_self]

lemma populationCoverFlag_translate_mod (P T : Finset ℕ) (d : ℕ) (r : Phase P) :
    populationCoverFlag P (T.image (fun x => d%primeProduct P+x)) r =
      populationCoverFlag P (T.image (fun x => d+x)) r := by
  classical
  have he (x : ℕ) (p : P) : (d%primeProduct P+x)%p.val=(d+x)%p.val := by
    have hp : p.val ∣ primeProduct P := dvd_prod_of_mem id p.property
    rw [Nat.add_mod (d%primeProduct P) x p.val,Nat.mod_mod_of_dvd d hp, ← Nat.add_mod]
  simp only [populationCoverFlag,forall_mem_image,he]

lemma coverageCovariance_displacement_mod (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (d : ℕ) :
    coverageCovariance P S (T.image (fun x => d%primeProduct P+x)) =
      coverageCovariance P S (T.image (fun x => d+x)) := by
  unfold coverageCovariance
  simp_rw [populationCoveredFraction_image_add P T hP]
  rw [populationCoveredFraction_union_flag,populationCoveredFraction_union_flag]
  simp only [populationCoverFlag_translate_mod]

lemma coverageCovariance_full_abs_sum (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ d : Fin (primeProduct P), |coverageCovariance P S
      (T.image (fun x => d.val+x))|) ≤
        2*(primeProduct P : ℝ)*populationCoveredFraction S P*populationCoveredFraction T P := by
  let M := populationCoveredFraction S P*populationCoveredFraction T P
  have hM : 0 ≤ M := mul_nonneg (populationCoveredFraction_nonneg S P)
    (populationCoveredFraction_nonneg T P)
  have hQ : (primeProduct P : ℝ) ≠ 0 := by
    exact_mod_cast (primeProduct_pos P (fun p hp => (hP p hp).pos)).ne'
  have hsum : (∑ d : Fin (primeProduct P),
      populationCoveredFraction (S ∪ T.image (fun x => d.val+x)) P) =
      (primeProduct P : ℝ)*M := by
    exact ((div_eq_iff hQ).mp (populationCoveredFraction_full_displacement P S T hP)).trans
      (mul_comm _ _)
  have hh := sum_le_sum (s := (univ : Finset (Fin (primeProduct P)))) (fun d _ =>
    show |coverageCovariance P S (T.image (fun x => d.val+x))| ≤
      populationCoveredFraction (S ∪ T.image (fun x => d.val+x)) P+M from by
        unfold coverageCovariance
        rw [populationCoveredFraction_image_add P T hP]
        change |_ - M| ≤ _
        rw [abs_le]
        constructor <;> linarith only [hM,
          populationCoveredFraction_nonneg (S ∪ T.image (fun x => d.val+x)) P])
  rw [sum_add_distrib,hsum] at hh
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  dsimp only [M] at hh
  nlinarith only [hh]

/-- A complete all-prime relative estimate, but its cost is the full prime
product. That factor is too large for the quadratic endpoint reduction. -/
theorem coverageCovariance_displacement_sum_relative (P S T : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (D : ℕ) :
    |∑ d ∈ range D, coverageCovariance P S (T.image (fun x => d+x))| ≤
      (primeProduct P : ℝ)*populationCoveredFraction S P*populationCoveredFraction T P := by
  have hQ := primeProduct_pos P (fun p hp => (hP p hp).pos)
  have hQR : (primeProduct P : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  let f : Fin (primeProduct P) → ℝ := fun d =>
    coverageCovariance P S (T.image (fun x => d.val+x))
  have hf : (∑ d, f d)=0 := by
    have hh := coverageCovariance_full_displacement P S T hP
    change (∑ d, f d)/(primeProduct P : ℝ)=0 at hh
    simpa only [zero_mul] using (div_eq_iff hQR).mp hh
  have he : (∑ d ∈ range D, coverageCovariance P S (T.image (fun x => d+x))) =
      ∑ d ∈ range D, f ⟨d%primeProduct P,Nat.mod_lt _ hQ⟩ := by
    apply sum_congr rfl
    intro d hd
    exact (coverageCovariance_displacement_mod P S T hP d).symm
  rw [he]
  have hh := zero_sum_residue_function_bound (primeProduct P) hQ D f hf
  have ha := mul_le_mul_of_nonneg_left (coverageCovariance_full_abs_sum P S T hP)
    (by norm_num : (0 : ℝ) ≤ 1/2)
  apply hh.trans
  apply ha.trans_eq
  ring

#print axioms populationCoveredFraction_full_displacement
#print axioms coverageCovariance_full_displacement
#print axioms coverageCovariance_displacement_sum_relative
end Erdos970.OneHitLogConcavity
