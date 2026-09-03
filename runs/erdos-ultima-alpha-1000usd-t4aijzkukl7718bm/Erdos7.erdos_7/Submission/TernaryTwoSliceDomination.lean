import Submission.TernaryTwoCoherentMixture

/-! Labelled normalized ternary slices admit coherent dominating integer
profiles. Empty sections can be padded, while every family keeps its labels. -/
namespace Erdos7TernaryTwoSliceDomination
open scoped BigOperators
open Erdos7TernaryTwoCoherentMixture
set_option maxHeartbeats 2500000

noncomputable def pushWeight {I Z : Type*} [Fintype I] (w : I → ℝ) (f : I → Z) (z : Z) : ℝ := by
  classical
  exact ∑ i,if f i=z then w i else 0

lemma pushWeight_nonneg {I Z : Type*} [Fintype I] (w : I → ℝ) (f : I → Z)
    (hw : ∀ i,0≤w i) (z : Z) : 0≤pushWeight w f z := by
  classical
  exact Finset.sum_nonneg (fun i _ => by split_ifs; exact hw i; rfl)

lemma pushWeight_mass {I Z : Type*} [Fintype I] [Fintype Z] (w : I → ℝ) (f : I → Z) :
    (∑ z,pushWeight w f z)=∑ i,w i := by
  classical
  unfold pushWeight
  rw [Finset.sum_comm]
  simp

lemma weighted_indicator {I Z : Type*} [Fintype I] [DecidableEq Z] (w : I → ℝ) (f : I → Z) (z : Z) :
    (∑ i,w i*(if z=f i then (1:ℝ) else 0))=pushWeight w f z := by
  classical
  simp [pushWeight,mul_ite,eq_comm]

/-- The two positive-exponent groups may have different label sets. A bound
on each section by a branch or a point suffices for a full profile majorant. -/
theorem dominating_profile {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : J → ℝ) (hw : ∀ i,0≤w i) (hv : ∀ j,0≤v j)
    (hmw : (∑ i,w i)=1) (hmv : (∑ j,v j)=1)
    (b : I → Fin 2) (p : J → Fin 5) (B : I → Fin 5 → ℝ) (P : J → Fin 5 → ℝ)
    (hB : ∀ i x,B i x≤(if branch x=b i then (1:ℝ) else 0))
    (hP : ∀ j x,P j x≤(if x=p j then (1:ℝ) else 0)) :
    ∃ f : Fin 5 → ℝ,f∈convexHull ℝ (Set.range corner) ∧
      ∀ x,1+(∑ i,w i*B i x)+(∑ j,v j*P j x)≤f x := by
  refine ⟨fun x => 1+pushWeight w b (branch x)+pushWeight v p x,?_,?_⟩
  · exact profile_mem_hull (pushWeight w b) (pushWeight v p)
      (pushWeight_nonneg w b hw) (pushWeight_nonneg v p hv)
      (by rw [pushWeight_mass,hmw]) (by rw [pushWeight_mass,hmv])
  · intro x
    dsimp only
    rw [← weighted_indicator w b (branch x),← weighted_indicator v p x]
    exact add_le_add (add_le_add le_rfl (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hB i x) (hw i))))
      (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hP j x) (hv j)))

/-- One finite convex mixture dominates all slices simultaneously. In
particular, its same first slice is reused in every cumulative prefix. -/
theorem coherent_dominating_mixture {D : Type*} [Finite D] (f : D → Fin 5 → ℝ)
    (hf : ∀ j,∃ g : Fin 5 → ℝ,g∈convexHull ℝ (Set.range corner) ∧ ∀ x,f j x≤g x) :
    ∃ (I : Type) (_ : Fintype I) (w : I → ℝ) (a : I → D → Fin 10),
      (∀ i,0≤w i) ∧ (∑ i,w i)=1 ∧
      ∀ j x,f j x≤∑ i,w i*corner (a i j) x := by
  classical
  choose g hg hfg using hf
  obtain ⟨I,inst,w,a,hw,hm,he⟩ := coherent_mixture g hg
  letI : Fintype I := inst
  exact ⟨I,inst,w,a,hw,hm,fun j x => (hfg j x).trans_eq (he j x)⟩

noncomputable def extendReal {D : ℕ} (f : Fin D → Fin 5 → ℝ) (j : ℕ) (x : Fin 5) : ℝ :=
  if h : j<D then f ⟨j,h⟩ x else 0

def extendChoice {D : ℕ} (a : Fin D → Fin 10) (j : ℕ) : Fin 10 :=
  if h : j<D then a ⟨j,h⟩ else 0

lemma prefix_domination {D : ℕ} {I : Type*} [Fintype I]
    (f : Fin D → Fin 5 → ℝ) (w : I → ℝ) (a : I → Fin D → Fin 10)
    (hf : ∀ j x,f j x≤∑ i,w i*corner (a i j) x)
    (d : ℕ) (hd : d≤D) (x : Fin 5) :
    (∑ j∈Finset.range d,extendReal f j x) ≤
      ∑ i,w i*(Erdos7TernaryTwoSharedPrefix.prefixCount (extendChoice (a i)) d x : ℝ) := by
  have hs : (∑ j∈Finset.range d,extendReal f j x) ≤
      ∑ j∈Finset.range d,∑ i,w i*corner (extendChoice (a i) j) x := by
    apply Finset.sum_le_sum
    intro j hj
    have hjD : j<D := lt_of_lt_of_le (Finset.mem_range.mp hj) hd
    simpa only [extendReal,extendChoice,dif_pos hjD] using hf ⟨j,hjD⟩ x
  apply hs.trans_eq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  simp only [corner,Erdos7TernaryTwoSharedPrefix.prefixCount,Nat.cast_sum]

/-- Every cumulative prefix has a simultaneous majorant using the same
finite mixture of whole integer sequences. -/
theorem coherent_prefix_bound {D : ℕ} (f : Fin D → Fin 5 → ℝ)
    (hf : ∀ j,∃ g : Fin 5 → ℝ,g∈convexHull ℝ (Set.range corner) ∧ ∀ x,f j x≤g x) :
    ∃ (I : Type) (_ : Fintype I) (w : I → ℝ) (a : I → ℕ → Fin 10),
      (∀ i,0≤w i) ∧ (∑ i,w i)=1 ∧
      ∀ d≤D,∀ x,(∑ j∈Finset.range d,extendReal f j x) ≤
        ∑ i,w i*(Erdos7TernaryTwoSharedPrefix.prefixCount (a i) d x : ℝ) := by
  obtain ⟨I,inst,w,a,hw,hm,he⟩ := coherent_dominating_mixture f hf
  letI : Fintype I := inst
  exact ⟨I,inst,w,fun i => extendChoice (a i),hw,hm,
    fun d hd x => prefix_domination f w a he d hd x⟩

#print axioms coherent_prefix_bound

#print axioms dominating_profile
#print axioms coherent_dominating_mixture
end Erdos7TernaryTwoSliceDomination
