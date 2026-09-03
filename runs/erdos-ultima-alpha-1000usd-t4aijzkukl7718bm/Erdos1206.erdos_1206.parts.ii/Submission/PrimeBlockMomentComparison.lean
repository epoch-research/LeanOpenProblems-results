import Submission.SignedPrimeBlockExponential
import Submission.FiniteSelbergWeights

/-!
Comparison of arithmetic prime-divisor moments with an independent Bernoulli
model. The bounds retain their finite-prime remainder. No uniform high-moment
bound or cube-Sidon construction is asserted here.
-/
namespace Erdos1206.PrimeBlockMomentComparison
open Finset PrimeBlockVariance SignedPrimeBlockExponential FiniteThinnedSieve
open scoped Classical

noncomputable def model (P : Finset ℕ) (F : Finset ℕ → ℝ) : ℝ :=
  ∑ J ∈ P.powerset, weight P (fun p => 1/(p:ℝ)) J*F J

noncomputable def mask (J : Finset ℕ) (p : ℕ) : ℝ := if p∈J then 1 else 0

lemma model_add (P : Finset ℕ) (F G : Finset ℕ → ℝ) :
    model P (fun J => F J+G J)=model P F+model P G := by
  simp only [model,mul_add,sum_add_distrib]

lemma model_const_mul (P : Finset ℕ) (c : ℝ) (F : Finset ℕ → ℝ) :
    model P (fun J => c*F J)=c*model P F := by
  simp only [model,mul_sum]
  apply sum_congr rfl
  intros
  ring

lemma model_mul_const (P : Finset ℕ) (F : Finset ℕ → ℝ) (c : ℝ) :
    model P (fun J => F J*c)=model P F*c := by
  simp only [model,sum_mul,mul_assoc]

lemma model_sum {ι : Type*} (P : Finset ℕ) (s : Finset ι) (F : ι → Finset ℕ → ℝ) :
    model P (fun J => ∑ i ∈ s,F i J)=∑ i ∈ s,model P (F i) := by
  simp only [model,mul_sum]
  exact sum_comm

lemma model_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (F : Finset ℕ → ℝ) (hF : ∀ J ⊆ P,0 ≤ F J) : 0 ≤ model P F := by
  apply sum_nonneg
  intro J hJ
  apply mul_nonneg _ (hF J (mem_powerset.mp hJ))
  apply weight_nonneg P _ _ (mem_powerset.mp hJ)
  intro p hp
  refine ⟨by positivity,?_⟩
  exact (div_le_one (by exact_mod_cast (hP p hp).pos)).mpr
    (by exact_mod_cast (hP p hp).one_lt.le)

lemma mask_product {ι : Type*} (s : Finset ι) (f : ι → ℕ) (J : Finset ℕ) :
    (∏ i ∈ s,mask J (f i))=if s.image f ⊆ J then 1 else 0 := by
  by_cases h : s.image f ⊆ J
  · rw [if_pos h]
    exact prod_eq_one (fun i hi => by simp [mask,h (mem_image.mpr ⟨i,hi,rfl⟩)])
  · rw [if_neg h]
    obtain ⟨p,hp,hpJ⟩ := not_subset.mp h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact prod_eq_zero hi (by simp [mask,hpJ])

lemma model_joint {ι : Type*} (P : Finset ℕ) (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s,f i∈P) :
    model P (fun J => ∏ i ∈ s,mask J (f i))=∏ p ∈ s.image f,1/(p:ℝ) := by
  simp only [model,mask_product]
  have he (J : Finset ℕ) : weight P (fun p => 1/(p:ℝ)) J*
      (if s.image f ⊆ J then 1 else 0) =
      if s.image f ⊆ J then weight P (fun p => 1/(p:ℝ)) J else 0 := by
    split_ifs <;> ring
  simp_rw [he]
  exact sum_weight_supersets P (s.image f) _ (image_subset_iff.mpr hf)

lemma arithmetic_joint {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s,(f i).Prime) (N : ℕ) :
    (∑ n ∈ Icc 1 N,∏ i ∈ s,indicator (f i) n)=(N/(∏ p ∈ s.image f,p) : ℕ) := by
  have hprime : ∀ p ∈ s.image f,p.Prime := by
    rintro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hf i hi
  have he (n : ℕ) : (∏ i ∈ s,indicator (f i) n)=indicator (∏ p ∈ s.image f,p) n := by
    by_cases h : ∀ i ∈ s,f i∣n
    · have hd : (∏ p ∈ s.image f,p)∣n := (prime_prod_dvd_iff _ hprime n).mpr (by
        rintro p hp
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
        exact h i hi)
      rw [show indicator (∏ p ∈ s.image f,p) n=1 by simp [indicator,hd]]
      exact prod_eq_one (fun i hi => by simp [indicator,h i hi])
    · push_neg at h
      obtain ⟨i,hi,hd⟩ := h
      have hnot : ¬(∏ p ∈ s.image f,p)∣n := fun hh =>
        hd ((prime_prod_dvd_iff _ hprime n).mp hh (f i) (mem_image.mpr ⟨i,hi,rfl⟩))
      rw [show indicator (∏ p ∈ s.image f,p) n=0 by simp [indicator,hnot]]
      exact prod_eq_zero hi (by simp [indicator,hd])
  simp_rw [he]
  exact sum_indicator N _

lemma joint_discrepancy {ι : Type*} (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s,f i∈P) (N : ℕ) :
    |(∑ n ∈ Icc 1 N,∏ i ∈ s,indicator (f i) n)-
      (N:ℝ)*model P (fun J => ∏ i ∈ s,mask J (f i))| ≤ 1 := by
  rw [arithmetic_joint s f (fun i hi => hP _ (hf i hi)),model_joint P s f hf]
  have he : (∏ p ∈ s.image f,1/(p:ℝ))=1/(∏ p ∈ s.image f,p : ℕ) := by
    rw [prod_div_distrib]; push_cast; simp
  rw [he,mul_one_div]
  have hp : 0 < ∏ p ∈ s.image f,p := prod_pos (by
    rintro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact (hP _ (hf i hi)).pos)
  obtain ⟨hl,hu⟩ := quotient_error hp N
  exact abs_le.mpr ⟨hl,hu.trans (by norm_num)⟩

noncomputable def modelCentered (J : Finset ℕ) (p : ℕ) : ℝ := mask J p-1/(p:ℝ)

/-- Repetitions of a prime among the positions are allowed. The comparison
error depends on the number of positions, not on the prime magnitudes. -/
theorem centered_product_discrepancy {ι : Type*} (P : Finset ℕ)
    (hP : ∀ p ∈ P,p.Prime) (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s,f i∈P) (N : ℕ) :
    |(∑ n ∈ Icc 1 N,∏ i ∈ s,centered (f i) n)-
      (N:ℝ)*model P (fun J => ∏ i ∈ s,modelCentered J (f i))| ≤
        ∏ i ∈ s,(1+1/(f i:ℝ)) := by
  have ha (n : ℕ) : (∏ i ∈ s,centered (f i) n)=
      ∑ T ∈ s.powerset,(∏ i ∈ T,indicator (f i) n)*∏ i ∈ s\T,(-1/(f i:ℝ)) := by
    simp only [centered,sub_eq_add_neg,neg_div,prod_add]
  have hm (J : Finset ℕ) : (∏ i ∈ s,modelCentered J (f i))=
      ∑ T ∈ s.powerset,(∏ i ∈ T,mask J (f i))*∏ i ∈ s\T,(-1/(f i:ℝ)) := by
    simp only [modelCentered,sub_eq_add_neg,neg_div,prod_add]
  simp_rw [ha,hm]
  rw [sum_comm,model_sum,mul_sum,←sum_sub_distrib]
  have hterm (T : Finset ι) (hT : T∈s.powerset) :
      |(∑ n ∈ Icc 1 N,(∏ i ∈ T,indicator (f i) n)*∏ i ∈ s\T,(-1/(f i:ℝ)))-
        (N:ℝ)*model P (fun J => (∏ i ∈ T,mask J (f i))*∏ i ∈ s\T,(-1/(f i:ℝ)))| ≤
          ∏ i ∈ s\T,1/(f i:ℝ) := by
    rw [←sum_mul,model_mul_const]
    have he (a b c : ℝ) : a*c-(N:ℝ)*(b*c)=(a-(N:ℝ)*b)*c := by ring
    rw [he,abs_mul]
    have hh := joint_discrepancy P hP T f (fun i hi => hf i (mem_powerset.mp hT hi)) N
    have hc : |∏ i ∈ s\T,(-1/(f i:ℝ))|=∏ i ∈ s\T,1/(f i:ℝ) := by
      rw [abs_prod]
      apply prod_congr rfl
      intro i hi
      rw [abs_div]
      simp
    rw [hc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh
      (prod_nonneg (fun i _ => by positivity))
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum hterm).trans_eq
  have hp := prod_add (s := s) (fun _ : ι => (1:ℝ)) (fun i => 1/(f i:ℝ))
  simpa only [prod_const_one,one_mul] using hp.symm

noncomputable def modelScore (P : Finset ℕ) (w : ℕ → ℝ) (J : Finset ℕ) : ℝ :=
  ∑ p ∈ P,w p*modelCentered J p

private lemma power_expand {V : Type*} [Fintype V] (g : V → ℝ) (k : ℕ) :
    (∑ v,g v)^k=∑ f : Fin k → V,∏ i,g (f i) := by
  simpa only [prod_const,card_univ,Fintype.card_fin] using
    (Fintype.prod_sum (fun (_ : Fin k) (v : V) => g v))

/-- Every integral moment, including odd moments and signed weights, is
within `(2*sum |w_p|)^k` of its independent Bernoulli model. This error grows
polynomially in the block cardinality when k is fixed. -/
theorem score_moment_discrepancy (P : Finset ℕ) (hP : ∀ p ∈ P,p.Prime)
    (w : ℕ → ℝ) (k N : ℕ) :
    |(∑ n ∈ Icc 1 N,(primeSum P w n-mean P w)^k)-
      (N:ℝ)*model P (fun J => (modelScore P w J)^k)| ≤
        (2*∑ p ∈ P,|w p|)^k := by
  have ha (n : ℕ) : (primeSum P w n-mean P w)^k =
      ∑ f : Fin k → P,∏ i,w (f i)*centered (f i) n := by
    rw [centered_primeSum,←sum_coe_sort]
    exact power_expand _ k
  have hm (J : Finset ℕ) : (modelScore P w J)^k =
      ∑ f : Fin k → P,∏ i,w (f i)*modelCentered J (f i) := by
    rw [modelScore,←sum_coe_sort]
    exact power_expand _ k
  simp_rw [ha,hm]
  rw [sum_comm,model_sum,mul_sum,←sum_sub_distrib]
  have hterm (f : Fin k → P) :
      |(∑ n ∈ Icc 1 N,∏ i,w (f i)*centered (f i) n)-
        (N:ℝ)*model P (fun J => ∏ i,w (f i)*modelCentered J (f i))| ≤
          ∏ i,2*|w (f i)| := by
    simp_rw [prod_mul_distrib]
    rw [←mul_sum,model_const_mul]
    have he (a b c : ℝ) : c*a-(N:ℝ)*(c*b)=c*(a-(N:ℝ)*b) := by ring
    rw [he,abs_mul,abs_prod]
    have hh := centered_product_discrepancy P hP univ (fun i => (f i:ℕ))
      (fun i _ => (f i).property) N
    have htwo : (∏ i : Fin k,(1+1/(f i:ℝ))) ≤ ∏ _i : Fin k,(2:ℝ) := by
      apply prod_le_prod
      · intro i _; positivity
      · intro i _
        have hp := hP _ (f i).property
        have hu : 1/(f i:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hp.one_lt.le)
        linarith
    have hbound := mul_le_mul_of_nonneg_left (hh.trans htwo)
      (prod_nonneg (s := univ) (fun i _ => abs_nonneg (w (f i))))
    simpa only [←prod_mul_distrib,mul_comm] using hbound
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (fun f _ => hterm f)).trans_eq
  rw [←power_expand (fun p : P => 2*|w p|),sum_coe_sort P (fun p => 2*|w p|),←mul_sum]


#print axioms joint_discrepancy
#print axioms centered_product_discrepancy
#print axioms score_moment_discrepancy
end Erdos1206.PrimeBlockMomentComparison
