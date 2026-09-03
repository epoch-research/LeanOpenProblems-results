import Submission.UniformGraphColorTransferExplore

/-! A bounded-sum quartic graph without the common horizontal reflection
of parallel parabolas. This is a finite-field example only. -/
namespace Erdos66QuarticGraph
open Erdos66TranslatedGraphPartition Polynomial
open scoped Classical
set_option maxHeartbeats 2200000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def quarticGraph (x : F) : F := x^4+x

noncomputable def sumPolynomial (t s : F) : F[X] :=
  C 2*X^4+C (-4*t)*X^3+C (6*t^2)*X^2+C (-4*t^3)*X+C (t^4+t-s)

lemma sumPolynomial_eval (t s x : F) :
    (sumPolynomial t s).eval x=quarticGraph x+quarticGraph (t-x)-s := by
  simp only [sumPolynomial,eval_add,eval_mul,eval_C,eval_pow,eval_X,quarticGraph]
  ring

lemma sumPolynomial_degree (t s : F) : (sumPolynomial t s).natDegree≤4 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [sumPolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  have h0 : k≠0 := by omega
  have h1 : k≠1 := by omega
  have h2 : k≠2 := by omega
  have h3 : k≠3 := by omega
  have h4 : k≠4 := by omega
  simp [h0,h1,Ne.symm h1,h2,h3,h4]

lemma sumPolynomial_ne_zero (hF : ringChar F≠2) (t s : F) : sumPolynomial t s≠0 := by
  intro he
  have hc := congrArg (fun P : F[X] ↦ P.coeff 4) he
  have ht : (2:F)≠0 := Ring.two_ne_zero hF
  simp only [sumPolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C] at hc
  norm_num at hc
  exact ht hc

lemma polynomial_fiber_bound (P : F[X]) (hP : P≠0) :
    Fintype.card {x : F // P.eval x=0}≤P.natDegree := by
  rw [Fintype.card_subtype]
  apply card_le_degree_of_subset_roots
  intro x hx
  rw [mem_roots hP]
  exact (Finset.mem_filter.mp hx).2

/-- Every sum fiber has at most four points in odd characteristic. -/
theorem quarticGraph_bounded (hF : ringChar F≠2) : HasBoundedSums (quarticGraph : F → F) 4 := by
  intro t s
  have he : {x : F // quarticGraph x+quarticGraph (t-x)=s} ≃
      {x : F // (sumPolynomial t s).eval x=0} :=
    Equiv.subtypeEquivRight (fun x ↦ by rw [sumPolynomial_eval,sub_eq_zero])
  rw [Fintype.card_congr he]
  exact (polynomial_fiber_bound _ (sumPolynomial_ne_zero hF t s)).trans (sumPolynomial_degree t s)

/-- In characteristic other than 2 or 3, no single horizontal reflection
preserves the quartic graph. This does not assert that every selected row
of every union of translates is nonsymmetric. -/
theorem quarticGraph_no_reflection (h2 : (2:F)≠0) (h3 : (3:F)≠0) :
    ¬∃ t : F, ∀ x : F, quarticGraph (t-x)=quarticGraph x := by
  rintro ⟨t,ht⟩
  let c : F := t/2
  have htc : t=2*c := by dsimp only [c]; field_simp
  have h₁ := ht (c+1)
  have h₂ := ht (c+2)
  rw [htc,show 2*c-(c+1)=c-1 by ring] at h₁
  rw [htc,show 2*c-(c+2)=c-2 by ring] at h₂
  dsimp only [quarticGraph] at h₁ h₂
  have h48 : (48:F)≠0 := by
    have he : (48:F)=2*2*2*2*3 := by ring
    rw [he]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h3
  have he : (48:F)*c=0 := by linear_combination 2*h₁-h₂
  have hc0 : c=0 := (mul_eq_zero.mp he).resolve_left h48
  have ht0 : t=0 := by rw [htc,hc0,mul_zero]
  have he2 := ht 1
  norm_num [quarticGraph,ht0] at he2
  exact h2 he2.symm

end Erdos66QuarticGraph
