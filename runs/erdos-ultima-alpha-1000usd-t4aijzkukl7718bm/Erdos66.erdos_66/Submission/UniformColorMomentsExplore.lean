import Submission.DisjointMeanExplore

/-! Exact first and second moments of pair kernels under independent uniform
vertex-color assignments. This contains no field or translation selection. -/
namespace Erdos66UniformColorMoments
open Erdos66UniformSelection Erdos66DisjointMean
open scoped Classical
set_option maxHeartbeats 1800000

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [Nonempty α] [DecidableEq α]

lemma mean_eval (i : ι) (f : α → ℝ) :
    mean (fun ω : ι → α ↦ f (ω i))=mean f := by
  have hh := mean_product (fun j : ι ↦ fun x : α ↦ if j=i then f x else 1)
  have hf (j : ι) : mean (fun x : α ↦ if j=i then f x else 1)=
      if j=i then mean f else 1 := by
    by_cases hj : j=i <;> simp only [hj,if_true,if_false,mean_const]
  simp_rw [hf] at hh
  simpa only [Finset.prod_ite_eq', Finset.mem_univ, if_true] using hh

lemma dependsOn_eval (i : ι) (f : α → ℝ) :
    DependsOn (fun ω : ι → α ↦ f (ω i)) ({i}:Set ι) := by
  intro x y hxy
  change f (x i)=f (y i)
  rw [hxy i (by simp)]

lemma dependsOn_pair (i j : ι) (K : α → α → ℝ) :
    DependsOn (fun ω : ι → α ↦ K (ω i) (ω j)) ({i,j}:Set ι) := by
  intro x y hxy
  change K (x i) (x j)=K (y i) (y j)
  rw [hxy i (by simp),hxy j (by simp)]

lemma mean_separated_eval (i j : ι) (hij : i≠j) (f g : α → ℝ) :
    mean (fun ω : ι → α ↦ f (ω i)*g (ω j))=mean f*mean g := by
  rw [mean_mul_of_disjoint ({i}:Set ι) ({j}:Set ι)
    (by simpa using hij) _ _ (dependsOn_eval i f) (dependsOn_eval j g),
    mean_eval,mean_eval]

noncomputable def kernelMean (K : α → α → ℝ) : ℝ :=
  mean (fun x : α × α ↦ K x.1 x.2)

lemma kernelMean_iterated (K : α → α → ℝ) :
    kernelMean K=mean (fun x : α ↦ mean (K x)) := by
  simp only [kernelMean,mean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.sum_div,div_div]

lemma mean_pair_kernel (i j : ι) (hij : i≠j) (K : α → α → ℝ) :
    mean (fun ω : ι → α ↦ K (ω i) (ω j))=kernelMean K := by
  have he (ω : ι → α) : K (ω i) (ω j)=
      ∑ x : α, (if ω i=x then (1:ℝ) else 0)*K x (ω j) := by simp
  simp_rw [he]
  rw [mean_sum]
  have hsep (x : α) : mean (fun ω : ι → α ↦
      (if ω i=x then (1:ℝ) else 0)*K x (ω j)) =
      mean (fun y : α ↦ if y=x then (1:ℝ) else 0)*mean (K x) :=
    mean_separated_eval i j hij (fun y : α ↦ if y=x then (1:ℝ) else 0) (K x)
  simp_rw [hsep]
  rw [kernelMean_iterated]
  have hi (x : α) : mean (fun y : α ↦ if y=x then (1:ℝ) else 0)=1/Fintype.card α := by
    simp [mean]
  simp_rw [hi]
  change (∑ x : α, (1/(Fintype.card α:ℝ))*mean (K x))=
    (∑ x : α, mean (K x))/(Fintype.card α:ℝ)
  rw [←Finset.mul_sum]
  ring

lemma mean_pair_product_disjoint (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hdis : Disjoint ({i,j}:Set ι) ({k,l}:Set ι)) (K L : α → α → ℝ) :
    mean (fun ω : ι → α ↦ K (ω i) (ω j)*L (ω k) (ω l)) =
      kernelMean K*kernelMean L := by
  rw [mean_mul_of_disjoint _ _ hdis _ _ (dependsOn_pair i j K) (dependsOn_pair k l L),
    mean_pair_kernel i j hij,mean_pair_kernel k l hkl]

lemma mean_pair_sq (i j : ι) (hij : i≠j) (K : α → α → ℝ) :
    mean (fun ω : ι → α ↦ (K (ω i) (ω j))^2)=kernelMean (fun x y ↦ (K x y)^2) :=
  mean_pair_kernel i j hij (fun x y ↦ (K x y)^2)

noncomputable def centeredKernel (K : α → α → ℝ) (x y : α) : ℝ :=
  K x y-kernelMean K

lemma kernelMean_centered (K : α → α → ℝ) : kernelMean (centeredKernel K)=0 := by
  simp only [kernelMean,centeredKernel,mean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card (α×α):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

lemma kernelVariance_nonneg (K : α → α → ℝ) :
    0≤kernelMean (fun x y ↦ (centeredKernel K x y)^2) := by
  change 0 ≤ mean _
  have hh := mean_mono (fun _ : α×α ↦ (0:ℝ))
    (fun x : α×α ↦ (centeredKernel K x.1 x.2)^2) (fun x ↦ sq_nonneg _)
  simpa only [mean_const] using hh

lemma kernelVariance_identity (K : α → α → ℝ) :
    kernelMean (fun x y ↦ (centeredKernel K x y)^2)=
      kernelMean (fun x y ↦ (K x y)^2)-(kernelMean K)^2 := by
  have he (x : α×α) : (centeredKernel K x.1 x.2)^2=
      (K x.1 x.2)^2+(-2*kernelMean K)*(K x.1 x.2)+(kernelMean K)^2 := by
    dsimp only [centeredKernel]; ring
  change mean (fun x : α×α ↦ (centeredKernel K x.1 x.2)^2)=_
  simp_rw [he]
  rw [mean_add,mean_add,mean_const_mul,mean_const]
  change kernelMean (fun x y ↦ (K x y)^2)+(-2*kernelMean K)*kernelMean K+
    (kernelMean K)^2=_
  ring

lemma kernelVariance_le_second (K : α → α → ℝ) :
    kernelMean (fun x y ↦ (centeredKernel K x y)^2)≤kernelMean (fun x y ↦ (K x y)^2) := by
  rw [kernelVariance_identity]
  nlinarith [sq_nonneg (kernelMean K)]

end Erdos66UniformColorMoments
