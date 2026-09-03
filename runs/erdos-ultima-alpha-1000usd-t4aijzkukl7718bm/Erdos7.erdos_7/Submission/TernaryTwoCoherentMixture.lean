import Submission.TernaryTwoSharedPrefix

/-! Full slice profiles and a coherent finite mixture of entire sequences.
A single mixture simultaneously represents every slice, hence every prefix. -/
namespace Erdos7TernaryTwoCoherentMixture
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix
set_option maxHeartbeats 3000000

noncomputable def corner (a : Fin 10) : Fin 5 → ℝ := fun x => (count a x : ℝ)
def branch (x : Fin 5) : Fin 2 := if x.val<2 then 0 else 1
def choiceCode (b : Fin 2) (y : Fin 5) : Fin 10 := ⟨5*b.val+y.val,by omega⟩

lemma count_formula : ∀ b y x,
    count (choiceCode b y) x = 1+(if branch x=b then 1 else 0)+(if x=y then 1 else 0) := by
  decide +kernel

lemma product_mass (B : Fin 2 → ℝ) (P : Fin 5 → ℝ)
    (hB : (∑ b,B b)=1) (hP : (∑ x,P x)=1) :
    (∑ z : Fin 2 × Fin 5,B z.1*P z.2)=1 := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,hP,mul_one,hB]

lemma product_count (B : Fin 2 → ℝ) (P : Fin 5 → ℝ)
    (hB : (∑ b,B b)=1) (hP : (∑ x,P x)=1) (x : Fin 5) :
    (∑ z : Fin 2 × Fin 5,B z.1*P z.2*corner (choiceCode z.1 z.2) x) =
      1+B (branch x)+P x := by
  have hf (b : Fin 2) (y : Fin 5) : corner (choiceCode b y) x =
      1+(if branch x=b then (1:ℝ) else 0)+(if x=y then (1:ℝ) else 0) := by
    unfold corner
    rw [count_formula]
    push_cast
    rfl
  simp_rw [Fintype.sum_prod_type,hf,mul_add,Finset.sum_add_distrib]
  have hbase : (∑ b,∑ y,B b*P y*1)=1 := by
    simp only [mul_one,← Finset.mul_sum,hP,hB]
  have hbranch : (∑ b,∑ y,B b*P y*(if branch x=b then (1:ℝ) else 0))=B (branch x) := by
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_irrel]
    simp [← Finset.mul_sum,hP]
  have hpoint : (∑ b,∑ y,B b*P y*(if x=y then (1:ℝ) else 0))=P x := by
    simp only [mul_ite,mul_one,mul_zero]
    simp [← Finset.sum_mul,hB]
  rw [hbase,hbranch,hpoint]

/-- The familiar branch-simplex plus point-simplex profile is in the convex
hull of the ten integer count profiles. -/
theorem profile_mem_hull (B : Fin 2 → ℝ) (P : Fin 5 → ℝ)
    (hB0 : ∀ b,0≤B b) (hP0 : ∀ x,0≤P x)
    (hB : (∑ b,B b)=1) (hP : (∑ x,P x)=1) :
    (fun x => 1+B (branch x)+P x) ∈ convexHull ℝ (Set.range corner) := by
  apply mem_convexHull_of_exists_fintype (fun z : Fin 2 × Fin 5 => B z.1*P z.2)
    (fun z => corner (choiceCode z.1 z.2))
  · intro z
    exact mul_nonneg (hB0 _) (hP0 _)
  · exact product_mass B P hB hP
  · intro z
    exact Set.mem_range_self _
  · funext x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact product_count B P hB hP x

/-- The choices for different slices are coupled into ONE finite mixture.
This does not require independence of the arithmetic count functions and does
not identify the sequences belonging to different future test families. -/
theorem coherent_mixture {D : Type*} [Finite D] (f : D → Fin 5 → ℝ)
    (hf : ∀ j,f j∈convexHull ℝ (Set.range corner)) :
    ∃ (I : Type) (_ : Fintype I) (w : I → ℝ) (a : I → D → Fin 10),
      (∀ i,0≤w i) ∧ (∑ i,w i)=1 ∧
      ∀ j x,f j x=∑ i,w i*corner (a i j) x := by
  classical
  have hh : f∈convexHull ℝ (Set.pi Set.univ (fun _ : D => Set.range corner)) :=
    mem_convexHull_pi (fun j _ => hf j)
  obtain ⟨I,inst,w,z,hw,hm,hz,he⟩ := mem_convexHull_iff_exists_fintype.mp hh
  letI : Fintype I := inst
  have hc (i : I) (j : D) : ∃ a : Fin 10,corner a=z i j := hz i j (Set.mem_univ j)
  choose a ha using hc
  refine ⟨I,inst,w,a,hw,hm,?_⟩
  intro j x
  have he' := congrFun (congrFun he j) x
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he'
  rw [← he']
  apply Finset.sum_congr rfl
  intro i _
  rw [ha i j]

#print axioms profile_mem_hull
#print axioms coherent_mixture
end Erdos7TernaryTwoCoherentMixture
