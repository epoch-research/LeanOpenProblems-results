import Submission.CompletionDisplacement

/-! Short displacement averages of the signed completion source. The
arithmetic boundary error retains the product of the two concentration
probabilities. Recursive child covariances remain explicit. -/
namespace Erdos970.OneHitLogConcavity
open Finset GapAverages CoverFibers Resampling
set_option maxHeartbeats 2200000

lemma sum_residue_function_eq_counts (p : ℕ) (hp : 0 < p) (D : ℕ) (f : Fin p → ℝ) :
    (∑ d ∈ range D, f ⟨d%p,Nat.mod_lt _ hp⟩) =
      ∑ a : Fin p, f a*(BrunCriterion.residueCount D p a.val : ℝ) := by
  classical
  have he (d : ℕ) : f ⟨d%p,Nat.mod_lt _ hp⟩ =
      ∑ a : Fin p, if a.val=d%p then f a else 0 := by
    have hi (a : Fin p) : a.val=d%p ↔ a=⟨d%p,Nat.mod_lt _ hp⟩ :=
      ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [hi,sum_ite_eq',mem_univ,if_true]
  simp_rw [he]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul]
  rw [mul_comm]
  congr 1
  unfold BrunCriterion.residueCount
  congr 1
  congr 1
  ext d
  simp only [mem_filter,Nat.ModEq,Nat.mod_eq_of_lt a.isLt,eq_comm]

/-- A generic balanced-residue estimate for a zero-mean periodic sequence. -/
lemma zero_sum_residue_function_bound (p : ℕ) (hp : 0 < p) (D : ℕ) (f : Fin p → ℝ)
    (hf : (∑ a, f a)=0) :
    |∑ d ∈ range D, f ⟨d%p,Nat.mod_lt _ hp⟩| ≤ (1/2 : ℝ)*∑ a, |f a| := by
  rw [sum_residue_function_eq_counts p hp D f]
  exact BrunCriterion.residue_balanced_error D p hp Fin.val f hf

/-- Every complete prime-residue period cancels. The incomplete boundary
cost is at most concentration(S)*concentration(T)/p, independently of the
number D of displacements. This is a signed-source estimate only. -/
theorem signedCompletionSource_displacement_sum_bound (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (D : ℕ) :
    |∑ d ∈ range D, signedCompletionSource P S (T.image (fun x => d+x)) p| ≤
      populationConcentration P S p*populationConcentration P T p/p := by
  let f : Fin p → ℝ := fun d => signedCompletionSource P S (T.image (fun x => d.val+x)) p
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hf : (∑ d, f d)=0 := by
    have hh := signedCompletionSource_displacement_mean_zero P S T hP p hp
    change (∑ d, f d)/(p : ℝ)=0 at hh
    have he := (div_eq_iff hpR).mp hh
    simpa only [zero_mul] using he
  have he : (∑ d ∈ range D, signedCompletionSource P S (T.image (fun x => d+x)) p) =
      ∑ d ∈ range D, f ⟨d%p,Nat.mod_lt _ hp⟩ := by
    apply sum_congr rfl
    intro d hd
    exact (signedCompletionSource_displacement_mod P S T hP p hp d).symm
  rw [he]
  have hb := zero_sum_residue_function_bound p hp D f hf
  have hnorm := signedCompletionSource_displacement_abs_sum P S T hP p hp
  have hmul := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 1/2)
  apply hb.trans
  apply hmul.trans_eq
  rw [completionIncrement_mean_concentration P S p hp,completionIncrement_mean_concentration P T p hp]
  field_simp
  <;> ring

/-- Normalized form of the preceding finite estimate. -/
theorem signedCompletionSource_displacement_average_bound (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (D : ℕ) (hD : 0 < D) :
    |(∑ d ∈ range D, signedCompletionSource P S (T.image (fun x => d+x)) p)/(D : ℝ)| ≤
      populationConcentration P S p*populationConcentration P T p/((p : ℝ)*D) := by
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) D)]
  have hh := div_le_div_of_nonneg_right
    (signedCompletionSource_displacement_sum_bound P S T hP p hp D) (Nat.cast_nonneg D)
  simpa only [div_div] using hh

/-- The exact recurrence after displacement averaging. Only the signed
one-prime source has been estimated; the child covariance is not discarded
or claimed to be independent of the displacement. -/
theorem averaged_coverageCovariance_insert_error (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (hpP : p ∉ P) (D : ℕ) :
    |(∑ d ∈ range D, coverageCovariance (insert p P) S (T.image (fun x => d+x)))-
      (∑ d ∈ range D, residueMean p (fun a => coverageCovariance P
        (avoidClass S p a) (avoidClass (T.image (fun x => d+x)) p a)))| ≤
      populationConcentration P S p*populationConcentration P T p/p := by
  simp_rw [coverageCovariance_insert_signed P S _ p hpP hp]
  rw [sum_add_distrib,add_sub_cancel_left]
  exact signedCompletionSource_displacement_sum_bound P S T hP p hp D

/-- The corresponding finite upper bound. It is not a complete bound on
the averaged joint cover probability until the child term is controlled. -/
theorem averaged_coverageCovariance_insert_le (P S T : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (p : ℕ) (hp : 0 < p) (hpP : p ∉ P) (D : ℕ) :
    (∑ d ∈ range D, coverageCovariance (insert p P) S (T.image (fun x => d+x))) ≤
      (∑ d ∈ range D, residueMean p (fun a => coverageCovariance P
        (avoidClass S p a) (avoidClass (T.image (fun x => d+x)) p a)))+
      populationConcentration P S p*populationConcentration P T p/p := by
  have hh := (abs_le.mp (averaged_coverageCovariance_insert_error P S T hP p hp hpP D)).2
  linarith only [hh]

#print axioms signedCompletionSource_displacement_sum_bound
#print axioms signedCompletionSource_displacement_average_bound
#print axioms averaged_coverageCovariance_insert_error
end Erdos970.OneHitLogConcavity
