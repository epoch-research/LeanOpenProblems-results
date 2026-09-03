import Submission.SharedParameterKernelExplore

/-! Exact root counting for two finite fields with shared parameter labels.
These are counts with parameter multiplicity; conversion to a set and origin
repair are separate requirements. No infinite construction is asserted. -/
namespace Erdos66SharedParameterRoot
set_option maxHeartbeats 1000000
open Erdos66FiniteField Erdos66SharedParameterKernel
open scoped Classical
variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field K] [Fintype K] [DecidableEq K]

noncomputable def sharedRootCount (h : ℕ) (u : ℕ → F) (v : ℕ → K)
    (t s : F) (t' s' : K) : ℝ :=
  ∑ i∈Finset.range h, ∑ j∈Finset.range h,
    (Fintype.card {x : F // x^2/u i+(t-x)^2/u j=s} : ℝ)*
      (Fintype.card {x : K // x^2/v i+(t'-x)^2/v j=s'} : ℝ)

lemma sharedRootCount_affine (h : ℕ) (a : F) (b : K)
    (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (ha : ∀ i<h, a+(i : F) ≠ 0) (hb : ∀ i<h, b+(i : K) ≠ 0)
    (haa : ∀ i<h, ∀ j<h, (a+(i : F))+(a+(j : F)) ≠ 0)
    (hbb : ∀ i<h, ∀ j<h, (b+(i : K))+(b+(j : K)) ≠ 0)
    (t s : F) (t' s' : K) :
    sharedRootCount h (fun i ↦ a+i) (fun i ↦ b+i) t s t' s' =
      sharedKernelCount h
        (fun i ↦ (quadraticChar F (a+i) : ℝ))
        (fun i ↦ (quadraticChar K (b+i) : ℝ))
        (fun w ↦ (quadraticChar F ((2*a+w)*s-t^2) : ℝ))
        (fun w ↦ (quadraticChar K ((2*b+w)*s'-(t')^2) : ℝ)) := by
  unfold sharedRootCount sharedKernelCount
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  have hf : (Fintype.card {x : F // x^2/(a+i)+(t-x)^2/(a+j)=s} : ℝ) =
      1+(quadraticChar F (a+i) : ℝ)*(quadraticChar F (a+j) : ℝ)*
        (quadraticChar F (((a+i)+(a+j))*s-t^2) : ℝ) := by
    exact_mod_cast parabola_sum_count hF (a+i) (a+j) t s (ha i hi') (ha j hj') (haa i hi' j hj')
  have hk : (Fintype.card {x : K // x^2/(b+i)+(t'-x)^2/(b+j)=s'} : ℝ) =
      1+(quadraticChar K (b+i) : ℝ)*(quadraticChar K (b+j) : ℝ)*
        (quadraticChar K (((b+i)+(b+j))*s'-(t')^2) : ℝ) := by
    exact_mod_cast parabola_sum_count hK (b+i) (b+j) t' s' (hb i hi') (hb j hj') (hbb i hi' j hj')
  have hea : (a+(i : F))+(a+j)=2*a+((i+j : ℕ) : F) := by push_cast; ring
  have heb : (b+(i : K))+(b+j)=2*b+((i+j : ℕ) : K) := by push_cast; ring
  rw [hf,hk,hea,heb]

/-- The extra condition is on the product of the two character sign sequences.
Small energies for the two separate characters alone are not sufficient. -/
theorem sharedRootCount_error_sq (h : ℕ) (a : F) (b : K)
    (hF : ringChar F ≠ 2) (hK : ringChar K ≠ 2)
    (ha : ∀ i<h, a+(i : F) ≠ 0) (hb : ∀ i<h, b+(i : K) ≠ 0)
    (haa : ∀ i<h, ∀ j<h, (a+(i : F))+(a+(j : F)) ≠ 0)
    (hbb : ∀ i<h, ∀ j<h, (b+(i : K))+(b+(j : K)) ≠ 0)
    (C : ℝ)
    (hf : labelEnergy h (fun i ↦ (quadraticChar F (a+i) : ℝ)) ≤ C*(h : ℝ)^2)
    (hg : labelEnergy h (fun i ↦ (quadraticChar K (b+i) : ℝ)) ≤ C*(h : ℝ)^2)
    (hfg : labelEnergy h (fun i ↦
      (quadraticChar F (a+i) : ℝ)*(quadraticChar K (b+i) : ℝ)) ≤ C*(h : ℝ)^2)
    (t s : F) (t' s' : K) :
    (sharedRootCount h (fun i ↦ a+i) (fun i ↦ b+i) t s t' s'-(h : ℝ)^2)^2 ≤
      18*C*(h : ℝ)^3 := by
  rw [sharedRootCount_affine h a b hF hK ha hb haa hbb]
  apply sharedKernelCount_error_sq h _ _ _ _ _ _ C hf hg hfg
  · intro w
    have hh : ((|quadraticChar F ((2*a+(w : F))*s-t^2)| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) :=
      Int.cast_le.mpr (quadraticChar_abs_le_one ((2*a+(w : F))*s-t^2))
    simpa only [Int.cast_abs,Int.cast_one] using hh
  · intro w
    have hh : ((|quadraticChar K ((2*b+(w : K))*s'-(t')^2)| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) :=
      Int.cast_le.mpr (quadraticChar_abs_le_one ((2*b+(w : K))*s'-(t')^2))
    simpa only [Int.cast_abs,Int.cast_one] using hh

end Erdos66SharedParameterRoot
