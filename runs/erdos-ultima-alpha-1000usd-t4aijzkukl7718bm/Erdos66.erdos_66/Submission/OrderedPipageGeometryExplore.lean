import Submission.FiniteRepBernoulliExplore

/-! Finite geometry for ordered, sum-preserving dependent rounding.
These lemmas alone do not construct an Erdős 66 witness. -/
namespace Erdos66OrderedPipageGeometry
open scoped Classical
set_option maxHeartbeats 1500000

lemma two_coordinate_rounding (u v : ℝ) (hu : 0<u ∧ u<1) (hv : 0<v ∧ v<1) :
    ∃ a b d e w : ℝ,
      (0≤a ∧ a≤1) ∧ (0≤b ∧ b≤1) ∧ (0≤d ∧ d≤1) ∧ (0≤e ∧ e≤1) ∧
      (0≤w ∧ w≤1) ∧ a+b=u+v ∧ d+e=u+v ∧
      w*a+(1-w)*d=u ∧ w*b+(1-w)*e=v ∧
      w*(a*b)+(1-w)*(d*e)≤u*v ∧
      (a=0 ∨ a=1 ∨ b=0 ∨ b=1) ∧ (d=0 ∨ d=1 ∨ e=0 ∨ e=1) := by
  by_cases hs : u+v≤1
  · have hp : 0<u+v := by linarith
    refine ⟨0,u+v,u+v,0,v/(u+v),by norm_num,⟨by linarith,hs⟩,
      ⟨by linarith,hs⟩,by norm_num,⟨div_nonneg hv.1.le hp.le,?_⟩,by ring,by ring,?_,?_,?_,by simp,by simp⟩
    · exact (div_le_one hp).mpr (by linarith)
    · field_simp
      ring
    · field_simp
      ring
    · simpa only [zero_mul,mul_zero,add_zero] using mul_nonneg hu.1.le hv.1.le
  · have hs1 : 1<u+v := lt_of_not_ge hs
    have hp : 0<2-u-v := by linarith
    have hle : (1-u)/(2-u-v)≤1 := (div_le_one hp).mpr (by linarith)
    refine ⟨u+v-1,1,1,u+v-1,(1-u)/(2-u-v),⟨by linarith,by linarith⟩,
      by norm_num,by norm_num,⟨by linarith,by linarith⟩,
      ⟨div_nonneg (by linarith) hp.le,hle⟩,by ring,by ring,?_,?_,?_,by simp,by simp⟩
    · field_simp
      ring
    · field_simp
      ring
    · have hh := mul_nonneg (show 0≤1-u by linarith) (show 0≤1-v by linarith)
      nlinarith

variable {ι : Type*} [DecidableEq ι]

noncomputable def replaceTwo (x : ι → ℝ) (i j : ι) (a b : ℝ) : ι → ℝ :=
  fun k ↦ if k=i then a else if k=j then b else x k

lemma replaceTwo_self (x : ι → ℝ) (i j : ι) : replaceTwo x i j (x i) (x j)=x := by
  funext k
  dsimp [replaceTwo]
  split_ifs <;> simp_all

lemma monomial_replaceTwo (S : Finset ι) (x : ι → ℝ) (i j : ι) (hij : i≠j) (a b : ℝ) :
    (∏ k∈S, replaceTwo x i j a b k) =
      (if i∈S then a else 1)*(if j∈S then b else 1)*
        ∏ k∈S, if k=i ∨ k=j then 1 else x k := by
  have he (k : ι) : replaceTwo x i j a b k =
      (if k=i then a else 1)*(if k=j then b else 1)*(if k=i ∨ k=j then 1 else x k) := by
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all [replaceTwo]
  simp only [he,Finset.prod_mul_distrib,Finset.prod_ite_eq']

lemma monomial_rounding_inequality (S : Finset ι) (x : ι → ℝ) (hx : ∀ k, 0≤x k)
    (i j : ι) (hij : i≠j) (a b d e w : ℝ)
    (hi : w*a+(1-w)*d=x i) (hj : w*b+(1-w)*e=x j)
    (hijprod : w*(a*b)+(1-w)*(d*e)≤x i*x j) :
    w*(∏ k∈S, replaceTwo x i j a b k)+(1-w)*(∏ k∈S, replaceTwo x i j d e k)≤∏ k∈S, x k := by
  have hbase := monomial_replaceTwo S x i j hij (x i) (x j)
  rw [replaceTwo_self] at hbase
  rw [monomial_replaceTwo S x i j hij a b,monomial_replaceTwo S x i j hij d e,hbase]
  have hnon : 0≤∏ k∈S, if k=i ∨ k=j then (1:ℝ) else x k :=
    Finset.prod_nonneg (fun k _ ↦ by split_ifs; exact zero_le_one; exact hx k)
  by_cases his : i∈S <;> by_cases hjs : j∈S <;>
    simp only [his,hjs,ite_true,ite_false,mul_one,one_mul]
  · have hh := mul_le_mul_of_nonneg_right hijprod hnon
    nlinarith only [hh]
  · have hh := congrArg (fun z : ℝ ↦ z*(∏ k∈S, if k=i ∨ k=j then (1:ℝ) else x k)) hi
    nlinarith only [hh]
  · have hh := congrArg (fun z : ℝ ↦ z*(∏ k∈S, if k=i ∨ k=j then (1:ℝ) else x k)) hj
    nlinarith only [hh]
  · ring_nf
    exact le_rfl

end Erdos66OrderedPipageGeometry
