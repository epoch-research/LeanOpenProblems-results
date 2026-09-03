import Submission.CyclicPrimeGapTransfer

/-! Finite mixtures of stationary finite systems. Mixing is done before
entropy selection; no separate scale is selected in each component. -/
namespace Erdos371.FiniteInformation
open Finset
set_option autoImplicit false
universe u v w
variable {ι : Type u} [Fintype ι] {Ω : ι → Type v} [∀ i, Fintype (Ω i)]

noncomputable def sigmaLaw (ρ : Law ι) (P : ∀ i, Law (Ω i)) : Law (Σ i, Ω i) where
  mass x := ρ x.1*P x.1 x.2
  nonneg x := mul_nonneg (ρ.nonneg _) ((P _).nonneg _)
  total := by
    simp only [Fintype.sum_sigma,← mul_sum,(P _).total,mul_one,ρ.total]

lemma mean_sigmaLaw (ρ : Law ι) (P : ∀ i, Law (Ω i)) (F : (Σ i, Ω i) → ℝ) :
    mean (sigmaLaw ρ P) F = mean ρ (fun i => mean (P i) (fun x => F ⟨i,x⟩)) := by
  simp only [mean,sigmaLaw,Fintype.sum_sigma,mul_assoc,mul_sum]

lemma law_eq_of_mean_eq {A : Type w} [Fintype A] (P Q : Law A)
    (h : ∀ F : A → ℝ, mean P F=mean Q F) : P=Q := by
  classical
  ext a
  have hh := h (fun b => if b=a then 1 else 0)
  simpa only [mean,mul_ite,mul_one,mul_zero,sum_ite_eq',mem_univ,if_true] using hh

lemma sigmaLaw_map_components (ρ : Law ι) (P : ∀ i, Law (Ω i)) (S : ∀ i, Ω i → Ω i)
    (hS : ∀ i, mapLaw (P i) (S i)=P i) :
    mapLaw (sigmaLaw ρ P) (fun x => (⟨x.1,S x.1 x.2⟩ : Σ i, Ω i))=sigmaLaw ρ P := by
  apply law_eq_of_mean_eq
  intro F
  rw [mean_mapLaw,mean_sigmaLaw,mean_sigmaLaw]
  apply congrArg (mean ρ)
  funext i
  have he := mean_mapLaw (P i) (S i) (fun x => F ⟨i,x⟩)
  rw [hS i] at he
  exact he.symm

lemma sigmaLaw_map_common {B : Type w} [Fintype B] (ρ : Law ι) (P : ∀ i, Law (Ω i))
    (Y : ∀ i, Ω i → B) (Q : Law B) (hY : ∀ i, mapLaw (P i) (Y i)=Q) :
    mapLaw (sigmaLaw ρ P) (fun x => Y x.1 x.2)=Q := by
  apply law_eq_of_mean_eq
  intro F
  rw [mean_mapLaw,mean_sigmaLaw]
  have he (i : ι) : mean (P i) (fun x => F (Y i x))=mean Q F := by
    rw [← mean_mapLaw,hY i]
  simp only [he]
  exact mean_const _ _

lemma sigma_iterate (S : ∀ i, Ω i → Ω i) (k : ℕ) (i : ι) (x : Ω i) :
    (fun y : Σ i, Ω i => (⟨y.1,S y.1 y.2⟩ : Σ i, Ω i))^[k] ⟨i,x⟩ = ⟨i,(S i)^[k] x⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply'] 

#print axioms sigmaLaw_map_components
#print axioms sigmaLaw_map_common
end Erdos371.FiniteInformation
