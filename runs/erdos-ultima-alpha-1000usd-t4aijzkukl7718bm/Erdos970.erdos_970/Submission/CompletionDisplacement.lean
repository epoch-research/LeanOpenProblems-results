import Submission.CompletionCollisionFibers
import Submission.ResidueBalancedError

/-! Exact displacement cancellation of the signed one-prime completion
source. This cancellation applies to the source, not automatically to the
recursive child covariance. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2200000

noncomputable def residueShift (p : ℕ) (hp : 0 < p) (d : ℕ) : Fin p ≃ Fin p :=
  affineResidueEquiv p d 1 hp (Nat.coprime_one_left _)

lemma residueShift_val (p : ℕ) (hp : 0 < p) (d : ℕ) (a : Fin p) :
    (residueShift p hp d a).val=(d+a.val)%p := by
  simpa only [residueShift,one_mul] using affineResidueEquiv_val p d 1 hp (Nat.coprime_one_left _) a

lemma residueMean_equiv (p : ℕ) (e : Fin p ≃ Fin p) (f : Fin p → ℝ) :
    residueMean p (fun a => f (e a))=residueMean p f := by
  unfold residueMean
  rw [e.sum_comp]

lemma residueShift_comm (p : ℕ) (hp : 0 < p) (a d : Fin p) :
    residueShift p hp d.val a=residueShift p hp a.val d := by
  apply Fin.ext
  simp only [residueShift_val,Nat.add_comm]

lemma residueShift_mod (p : ℕ) (hp : 0 < p) (d : ℕ) :
    residueShift p hp (d%p)=residueShift p hp d := by
  apply Equiv.ext
  intro a
  apply Fin.ext
  simp only [residueShift_val,Nat.mod_add_mod]

lemma shifted_residue_eq_iff (p : ℕ) (hp : 0 < p) (d x : ℕ) (a : Fin p) :
    (d+x)%p=(residueShift p hp d a).val ↔ x%p=a.val := by
  rw [residueShift_val]
  constructor
  · intro hh
    have he := Nat.ModEq.add_left_cancel' d hh
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt a.isLt] using he
  · intro hh
    have he : x ≡ a.val [MOD p] := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt a.isLt] using hh
    exact he.add_left d

lemma avoidClass_image_add (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (d : ℕ) (a : Fin p) :
    avoidClass (S.image (fun x => d+x)) p (residueShift p hp d a) =
      (avoidClass S p a).image (fun x => d+x) := by
  ext y
  simp only [avoidClass,mem_filter,mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hn⟩
    exact ⟨x,⟨hx,fun he => hn ((shifted_residue_eq_iff p hp d x a).mpr he)⟩,rfl⟩
  · rintro ⟨x,⟨hx,hn⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,fun he => hn ((shifted_residue_eq_iff p hp d x a).mp he)⟩

lemma completionIncrement_image_add (P S : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : 0 < p) (d : ℕ) (a : Fin p) :
    completionIncrement P (S.image (fun x => d+x)) p (residueShift p hp d a) =
      completionIncrement P S p a := by
  unfold completionIncrement
  rw [avoidClass_image_add S p hp d a,populationCoveredFraction_image_add P _ hP d,
    populationCoveredFraction_image_add P _ hP d]

lemma completionIncrement_mean_image_add (P S : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : 0 < p) (d : ℕ) :
    residueMean p (completionIncrement P (S.image (fun x => d+x)) p) =
      residueMean p (completionIncrement P S p) := by
  rw [← residueMean_equiv p (residueShift p hp d)]
  simp only [completionIncrement_image_add P S hP p hp d]

/-- Translation acts on the two completion-increment vectors by a cyclic
relative displacement. No independent-core approximation is made. -/
theorem completionCollision_image_add (P S T : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp : 0 < p) (d : ℕ) :
    completionCollision P S (T.image (fun x => d+x)) p =
      residueMean p (fun a => completionIncrement P S p (residueShift p hp d a)*
        completionIncrement P T p a) := by
  unfold completionCollision
  rw [← residueMean_equiv p (residueShift p hp d)]
  simp only [completionIncrement_image_add P T hP p hp d]

lemma residueMean_shift_product (p : ℕ) (hp : 0 < p) (f g : Fin p → ℝ) :
    residueMean p (fun d => residueMean p (fun a => f (residueShift p hp d.val a)*g a)) =
      residueMean p f*residueMean p g := by
  have hs (a : Fin p) : (∑ d : Fin p, f (residueShift p hp d.val a))=∑ d : Fin p, f d := by
    simp_rw [residueShift_comm p hp a]
    exact (residueShift p hp a.val).sum_comp f
  unfold residueMean
  rw [← sum_div,sum_comm]
  simp only [← sum_mul,hs]
  rw [← mul_sum]
  ring

/-- The signed one-prime source in the exact covariance recursion. -/
noncomputable def signedCompletionSource (P S T : Finset ℕ) (p : ℕ) : ℝ :=
  completionCollision P S T p-
    residueMean p (completionIncrement P S p)*residueMean p (completionIncrement P T p)

lemma coverageCovariance_insert_signed (P S T : Finset ℕ) (p : ℕ)
    (hp : p ∉ P) (hp0 : 0 < p) :
    coverageCovariance (insert p P) S T =
      residueMean p (fun a => coverageCovariance P (avoidClass S p a) (avoidClass T p a))+
        signedCompletionSource P S T p := by
  rw [coverageCovariance_insert P S T p hp hp0,signedCompletionSource,
    completionIncrement_mean P S p hp hp0,completionIncrement_mean P T p hp hp0]
  ring

/-- Exact zero mean of the SIGNED SOURCE over one complete residue period.
The recursive child covariance is not included in this identity. -/
theorem signedCompletionSource_displacement_mean_zero (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) :
    residueMean p (fun d => signedCompletionSource P S (T.image (fun x => d.val+x)) p)=0 := by
  unfold signedCompletionSource
  simp_rw [completionCollision_image_add P S T hP p hp,
    completionIncrement_mean_image_add P T hP p hp]
  rw [residueMean_sub,residueMean_shift_product p hp,residueMean_const p hp,sub_self]

lemma signedCompletionSource_displacement_mod (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (d : ℕ) :
    signedCompletionSource P S (T.image (fun x => (d%p)+x)) p =
      signedCompletionSource P S (T.image (fun x => d+x)) p := by
  unfold signedCompletionSource
  simp only [completionCollision_image_add P S T hP p hp,
    completionIncrement_mean_image_add P T hP p hp,residueShift_mod]

lemma signedCompletionSource_displacement_abs_sum (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) :
    (∑ d : Fin p, |signedCompletionSource P S (T.image (fun x => d.val+x)) p|) ≤
      2*(p : ℝ)*residueMean p (completionIncrement P S p)*residueMean p (completionIncrement P T p) := by
  let M := residueMean p (completionIncrement P S p)*residueMean p (completionIncrement P T p)
  have hM : 0 ≤ M := mul_nonneg
    (residueMean_nonneg p (completionIncrement_nonneg P S p))
    (residueMean_nonneg p (completionIncrement_nonneg P T p))
  have hmean : residueMean p (fun d => completionCollision P S (T.image (fun x => d.val+x)) p)=M := by
    simp_rw [completionCollision_image_add P S T hP p hp]
    exact residueMean_shift_product p hp _ _
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hsum : (∑ d : Fin p, completionCollision P S (T.image (fun x => d.val+x)) p)=(p : ℝ)*M := by
    unfold residueMean at hmean
    exact (div_eq_iff hpR).mp hmean |>.trans (mul_comm M _)
  have hh := sum_le_sum (s := (univ : Finset (Fin p))) (fun d _ =>
    show |signedCompletionSource P S (T.image (fun x => d.val+x)) p| ≤
      completionCollision P S (T.image (fun x => d.val+x)) p+M from by
        unfold signedCompletionSource
        rw [completionIncrement_mean_image_add P T hP p hp d.val]
        change |completionCollision P S (T.image (fun x => d.val+x)) p-M| ≤ _
        rw [abs_le]
        constructor <;> linarith only [completionCollision_nonneg P S (T.image (fun x => d.val+x)) p,hM])
  rw [sum_add_distrib,hsum] at hh
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  dsimp only [M] at hh
  nlinarith only [hh]

#print axioms coverageCovariance_insert_signed
#print axioms signedCompletionSource_displacement_mean_zero
#print axioms signedCompletionSource_displacement_abs_sum
end Erdos970.OneHitLogConcavity
