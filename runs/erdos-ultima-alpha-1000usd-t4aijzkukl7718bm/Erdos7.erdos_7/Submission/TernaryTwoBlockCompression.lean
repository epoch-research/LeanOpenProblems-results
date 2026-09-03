import Submission.TernaryTwoSequenceComparison
import Submission.CappedFiberMixture

/-! An actual one-coordinate compression into the mixed shared-prefix law.
The hypotheses are group marginal bounds, not identification of families. -/
namespace Erdos7TernaryTwoBlockCompression
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix Erdos7TernaryTwoSharedComparison
open Erdos7TernaryTwoSequenceComparison Erdos7TernaryTwoCoherentMixture
set_option maxHeartbeats 3000000

noncomputable def retention (w : Fin 10 → ℝ) (x : Fin 5) : ℝ :=
  ∑ c,w c*(1-(count c x : ℝ)/4)

lemma retention_bounds (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c) (hm : (∑ c,w c)=1) (x : Fin 5) :
    1/4≤retention w x ∧ retention w x≤3/4 := by
  have hc (c : Fin 10) : (1:ℝ)/4≤1-(count c x : ℝ)/4 ∧
      1-(count c x : ℝ)/4≤3/4 := by
    have hl : (1:ℝ)≤count c x := by exact_mod_cast (data.1 c x).1
    have hu : (count c x : ℝ)≤3 := by exact_mod_cast (data.1 c x).2
    constructor <;> linarith
  constructor
  · calc
      _ = ∑ c,w c*(1/4) := by rw [← Finset.sum_mul,hm,one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hc c).1 (hw c))
  · calc
      _ ≤ ∑ c,w c*(3/4) := Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hc c).2 (hw c))
      _ = _ := by rw [← Finset.sum_mul,hm,one_mul]

noncomputable def tail (E j : ℕ) : ℝ := if j<E+1 then 1/(5:ℝ)^(j+1) else 0

lemma tail_le (E j : ℕ) : tail E j≤1/5 := by
  unfold tail
  split_ifs
  · apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    simpa using pow_le_pow_right₀ (show (1:ℝ)≤5 by norm_num) (show 1≤j+1 by omega)
  · norm_num

lemma tail_zero (E : ℕ) : tail E (E+1)=0 := by simp [tail]
lemma tail_first (E : ℕ) : tail E 0=1/5 := by simp [tail]

lemma tail_difference (E : ℕ) (j : Fin (E+1)) :
    tail E j.val-tail E (j.val+1)=geometricWeight E j := by
  by_cases h : j.val<E
  · simp only [tail,if_pos j.isLt,if_pos (show j.val+1<E+1 by omega),geometricWeight,if_pos h]
    rw [show (5:ℝ)^(j.val+2)=5^(j.val+1)*5 by rw [show j.val+2=(j.val+1)+1 by omega,pow_succ]]
    field_simp
    ring
  · have he : j.val=E := by have := j.isLt; omega
    simp [tail,geometricWeight,h,he]

lemma positive_atom (w : Fin 10 → ℝ) (hm : (∑ c,w c)=1)
    (E : ℕ) (j : Fin (E+1)) (x : Fin 5) :
    Erdos7TernaryTwoMixedComparison.actualWeight w (geometricWeight E) (.inr (j,x))=
      geometricWeight E j/5 := by
  simp only [Erdos7TernaryTwoMixedComparison.actualWeight,actualWeight,Sum.elim_inr,
    ← Finset.sum_mul,hm,one_mul]

lemma actual_eval (w : Fin 10 → ℝ) (hm : (∑ c,w c)=1)
    (E : ℕ) (K : ℕ → Fin 5 → ℝ) (φ : ℝ → ℝ) :
    (∑ z,Erdos7TernaryTwoMixedComparison.actualWeight w (geometricWeight E) z*φ (observedCount E K z))=
      ∑ x : Fin 5,(1/5)*((retention w x-1/5)*φ (K 0 x)+
        ∑ j : Fin (E+1),geometricWeight E j*φ (∑ g∈Finset.range (j.val+2),K g x)) := by
  rw [Fintype.sum_sum_type]
  simp only [Erdos7TernaryTwoMixedComparison.first_weight w _ hm,
    positive_atom w hm,observedCount,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,geometricLength]
  conv_lhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [retention,Finset.mul_sum,mul_add]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

lemma prefix_step (K : ℕ → Fin 5 → ℝ) (j : ℕ) (x : Fin 5) :
    K 0 x+Erdos7RealChain.prefixWeight (fun g => K (g+1) x) (j+1)=
      ∑ g∈Finset.range (j+2),K g x := by
  rw [show j+2=(j+1)+1 by omega,Finset.sum_range_succ']
  unfold Erdos7RealChain.prefixWeight
  ring

/-- Actual fiber compression with cap1. The finite terminal coefficient is
retained exactly. No exponent limit and no common future family are assumed. -/
theorem fiber_compression {A : Type*} [Fintype A]
    (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c) (hm : (∑ c,w c)=1)
    (E : ℕ) (ν : Fin 5 → A → ℝ) (hν : ∀ x y,0≤ν x y)
    (hmass : ∀ x,(∑ y,ν x y)=retention w x/5)
    (K : ℕ → Fin 5 → ℝ) (s : ℕ → Fin 5 → A → ℝ)
    (hK : ∀ j<E+1,∀ x,0≤K (j+1) x)
    (hs : ∀ j<E+1,∀ x y,0≤s j x y)
    (hsK : ∀ j<E+1,∀ x y,s j x y≤K (j+1) x)
    (hmarg : ∀ j<E+1,∀ x,(∑ y,ν x y*s j x y)≤(1/5)*tail E j*K (j+1) x)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x,∑ y,ν x y*φ (K 0 x+∑ j∈Finset.range (E+1),s j x y)) ≤
      ∑ z,Erdos7TernaryTwoMixedComparison.actualWeight w (geometricWeight E) z*φ (observedCount E K z) := by
  rw [actual_eval w hm]
  apply Finset.sum_le_sum
  intro x _
  have hret := (retention_bounds w hw hm x).1
  have hh : 0≤retention w x := by linarith
  have hm' : (∑ y,ν x y)=(1/5)*retention w x := by rw [hmass]; ring
  have hmin (j : ℕ) : min (retention w x) (tail E j)=tail E j :=
    min_eq_right (by have ht := tail_le E j; linarith)
  have hb := Erdos7CappedFiberMixture.retained_capped_group_mixture (ν x) (hν x)
    (1/5) (retention w x) hh hm' φ hφ hmφ (K 0 x)
    (fun j => K (j+1) x) (fun j y => s j x y) (tail E) (E+1)
    (fun j hj => hK j hj x) (fun j hj y => hs j hj x y)
    (fun j hj y => hsK j hj x y) (fun j hj => hmarg j hj x) (tail_zero E)
  simp only [hmin] at hb
  rw [tail_first] at hb
  simp_rw [prefix_step] at hb
  simp only [Erdos7RealChain.prefixWeight] at hb
  have he : (∑ j∈Finset.range (E+1),(tail E j-tail E (j+1))*
      φ (∑ g∈Finset.range (j+2),K g x))=
      ∑ j : Fin (E+1),geometricWeight E j*φ (∑ g∈Finset.range (j.val+2),K g x) := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [tail_difference]
  rwa [he] at hb

theorem block_comparison {A : Type*} [Fintype A]
    (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c) (hm : (∑ c,w c)=1)
    (E : ℕ) (ν : Fin 5 → A → ℝ) (hν : ∀ x y,0≤ν x y)
    (hmass : ∀ x,(∑ y,ν x y)=retention w x/5)
    (K : ℕ → Fin 5 → ℝ) (s : ℕ → Fin 5 → A → ℝ)
    (hK : ∀ j<E+1,∀ x,0≤K (j+1) x)
    (hs : ∀ j<E+1,∀ x y,0≤s j x y)
    (hsK : ∀ j<E+1,∀ x y,s j x y≤K (j+1) x)
    (hmarg : ∀ j<E+1,∀ x,(∑ y,ν x y*s j x y)≤(1/5)*tail E j*K (j+1) x)
    (hprofile : ∀ j<E+2,∃ g : Fin 5 → ℝ,g∈convexHull ℝ (Set.range corner) ∧ ∀ x,K j x≤g x)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x,∑ y,ν x y*φ (K 0 x+∑ j∈Finset.range (E+1),s j x y)) ≤
      ∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z*φ (refCount (geometricLength E) z) := by
  exact (fiber_compression w hw hm E ν hν hmass K s hK hs hsK hmarg φ hφ hmφ).trans
    (sequence_comparison E K hprofile w hw φ hφ hmφ)

lemma reference_mass_eq {A : Type*} [Fintype A]
    (w : Fin 10 → ℝ) (hm : (∑ c,w c)=1) (E : ℕ) (ν : Fin 5 → A → ℝ)
    (hmass : ∀ x,(∑ y,ν x y)=retention w x/5) :
    (∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z)=∑ x,∑ y,ν x y := by
  rw [← Erdos7TernaryTwoMixedComparison.mass_eq]
  have hh := actual_eval w hm E (fun _ _ => 0) (fun _ => 1)
  simp only [mul_one,geometric_mass,sub_add_cancel] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro x _
  rw [hmass]
  ring

#print axioms block_comparison
#print axioms reference_mass_eq

#print axioms fiber_compression
end Erdos7TernaryTwoBlockCompression
