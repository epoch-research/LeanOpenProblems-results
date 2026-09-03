import FormalConjecturesUtil

/-! Exact hinge identities for coupled positive integer slices.
These are auxiliary inequalities, not a resolution of the odd covering problem. -/
namespace Erdos7CumulativeHingeDefect
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The hinge at three of a sum of two positive integers has just one
nonlinear correction: both integers are one. -/
lemma two_hinge_identity (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    ((u+v-3 : ℕ) : ℝ) = (u : ℝ)+(v : ℝ)-3+
      if u=1 ∧ v=1 then 1 else 0 := by
  by_cases hh : u=1 ∧ v=1
  · rcases hh with ⟨rfl,rfl⟩
    norm_num
  · rw [if_neg hh]
    have hsum : 3 ≤ u+v := by omega
    rw [Nat.cast_sub hsum, Nat.cast_add]
    norm_num

lemma double_hinge_identity (u : ℕ) (hu : 1 ≤ u) :
    ((2*u-3 : ℕ) : ℝ) = 2*(u : ℝ)-3+if u=1 then 1 else 0 := by
  have hh := two_hinge_identity u u hu hu
  simpa only [← two_mul, and_self] using hh

/-- The exact Jensen defect. No upper bound on the slice counts is needed. -/
theorem two_hinge_defect (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    (((2*u-3 : ℕ) : ℝ)+((2*v-3 : ℕ) : ℝ))/2 =
      ((u+v-3 : ℕ) : ℝ)+(if (u=1 ↔ v=1) then 0 else 1)/2 := by
  rw [double_hinge_identity u hu, double_hinge_identity v hv,
    two_hinge_identity u v hu hv]
  by_cases hu1 : u=1 <;> by_cases hv1 : v=1 <;> simp [hu1,hv1] <;> ring

/-- The coupling correction survives integration against any finite measure. -/
theorem weighted_two_hinge_defect {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U V : Ω → ℕ) (hU : ∀ x,1 ≤ U x) (hV : ∀ x,1 ≤ V x) :
    ((∑ x,μ x*((2*U x-3 : ℕ) : ℝ))+
      (∑ x,μ x*((2*V x-3 : ℕ) : ℝ)))/2 =
      (∑ x,μ x*((U x+V x-3 : ℕ) : ℝ))+
      (∑ x,μ x*(if (U x=1 ↔ V x=1) then 0 else 1))/2 := by
  have hh := congrArg (fun f : Ω → ℝ => ∑ x,μ x*f x)
    (funext (fun x => two_hinge_defect (U x) (V x) (hU x) (hV x)))
  simp only [← mul_div_assoc,mul_add,Finset.sum_add_distrib,← Finset.sum_div] at hh
  exact hh

/-- A quantitative lower bound on the mismatch mass gives a strict saving
from the ordinary Jensen upper bound. -/
theorem weighted_two_hinge_improvement {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U V : Ω → ℕ) (hU : ∀ x,1 ≤ U x) (hV : ∀ x,1 ≤ V x)
    (ε : ℝ) (hε : ε ≤ ∑ x,μ x*(if (U x=1 ↔ V x=1) then 0 else 1)) :
    (∑ x,μ x*((U x+V x-3 : ℕ) : ℝ)) ≤
      ((∑ x,μ x*((2*U x-3 : ℕ) : ℝ))+
        (∑ x,μ x*((2*V x-3 : ℕ) : ℝ)))/2-ε/2 := by
  have hh := weighted_two_hinge_defect μ U V hU hV
  linarith

/-- From three slices onward the hinge at three is linear. -/
lemma prefix_hinge_linear (U : ℕ → ℕ) (d : ℕ) (hd : 3 ≤ d)
    (hU : ∀ j<d,1 ≤ U j) :
    (((∑ j ∈ Finset.range d,U j)-3 : ℕ) : ℝ) =
      (∑ j ∈ Finset.range d,(U j : ℝ))-3 := by
  have hs : d ≤ ∑ j ∈ Finset.range d,U j := by
    calc
      d = ∑ _j ∈ Finset.range d,1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hU j (Finset.mem_range.mp hj))
  rw [Nat.cast_sub (hd.trans hs),Nat.cast_sum]
  norm_num

/-- A whole finite weighted prefix-hinge sum depends nonlinearly only on
its first two slices. This identity makes no independence assumption. -/
theorem weighted_prefix_identity (U : ℕ → ℕ) (w : ℕ → ℝ) (D : ℕ)
    (hD : 2 ≤ D) (hU : ∀ j<D,1 ≤ U j) :
    (∑ d ∈ Finset.Icc 2 D,w d*(((∑ j ∈ Finset.range d,U j)-3 : ℕ) : ℝ)) =
      (∑ d ∈ Finset.Icc 2 D,w d*((∑ j ∈ Finset.range d,(U j : ℝ))-3))+
      w 2*(if U 0=1 ∧ U 1=1 then 1 else 0) := by
  have he (d : ℕ) (hd : d ∈ Finset.Icc 2 D) :
      (((∑ j ∈ Finset.range d,U j)-3 : ℕ) : ℝ) =
        (∑ j ∈ Finset.range d,(U j : ℝ))-3+
        if d=2 then (if U 0=1 ∧ U 1=1 then 1 else 0) else 0 := by
    obtain ⟨hdlo,hdhi⟩ := Finset.mem_Icc.mp hd
    by_cases hd2 : d=2
    · subst d
      simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
        if_true] using two_hinge_identity (U 0) (U 1)
          (hU 0 (by omega)) (hU 1 (by omega))
    · rw [if_neg hd2,add_zero]
      exact prefix_hinge_linear U d (by omega) (fun j hj => hU j (lt_of_lt_of_le hj hdhi))
  calc
    _ = ∑ d ∈ Finset.Icc 2 D,w d*((∑ j ∈ Finset.range d,(U j : ℝ))-3+
        if d=2 then (if U 0=1 ∧ U 1=1 then 1 else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [he d hd]
    _ = _ := by
      simp_rw [mul_add,mul_ite,mul_zero]
      rw [Finset.sum_add_distrib]
      simp [hD]

noncomputable def drift (f : ℕ → ℝ) (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.range R,(f (j+1)-f j)/(5:ℝ)^(j+1)

/-- Geometric summation retains the first nonlinear correction. The reserve
makes this an induction over finite caps, without an infinite-series limit. -/
lemma drift_bound_with_reserve (f : ℕ → ℝ) (M B : ℝ)
    (hfirst : f 2-f 1 ≤ M-B)
    (hrest : ∀ j,2 ≤ j → f (j+1)-f j ≤ M) (R : ℕ) (hR : 2 ≤ R) :
    drift f R+M/(4*(5:ℝ)^R) ≤ (f 1-f 0)/5+M/20-B/25 := by
  induction R,hR using Nat.le_induction with
  | base =>
    norm_num [drift,Finset.sum_range_succ]
    linarith
  | succ R hR ih =>
    have hinc := div_le_div_of_nonneg_right (hrest R hR)
      (by positivity : (0:ℝ) ≤ (5:ℝ)^(R+1))
    have ht : M/(5:ℝ)^(R+1)+M/(4*(5:ℝ)^(R+1))=M/(4*(5:ℝ)^R) := by
      rw [pow_succ]
      field_simp
      <;> ring
    unfold drift at ih ⊢
    rw [Finset.sum_range_succ]
    linarith

/-- Uniform bound for every positive finite exponent cap. -/
theorem drift_bound (f : ℕ → ℝ) (M B : ℝ) (hM : 0 ≤ M) (hBM : B ≤ M)
    (hfirst : f 2-f 1 ≤ M-B)
    (hrest : ∀ j,2 ≤ j → f (j+1)-f j ≤ M) (R : ℕ) (hR : 1 ≤ R) :
    drift f R ≤ (f 1-f 0)/5+M/20-B/25 := by
  by_cases hR2 : 2 ≤ R
  · have hh := drift_bound_with_reserve f M B hfirst hrest R hR2
    have hn : 0 ≤ M/(4*(5:ℝ)^R) := by positivity
    linarith
  · have hR1 : R=1 := by omega
    subst R
    norm_num [drift,Finset.sum_range_succ]
    linarith

noncomputable def prefixCost {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U : ℕ → Ω → ℕ) (d : ℕ) : ℝ :=
  ∑ x,μ x*(((∑ j ∈ Finset.range d,U j x)-3 : ℕ) : ℝ)

noncomputable def bothMass {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U : ℕ → Ω → ℕ) : ℝ :=
  ∑ x,μ x*(if U 0 x=1 ∧ U 1 x=1 then 1 else 0)

lemma prefixCost_linear {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U : ℕ → Ω → ℕ) (hU : ∀ j x,1 ≤ U j x)
    (d : ℕ) (hd : 3 ≤ d) :
    prefixCost μ U d = ∑ x,μ x*((∑ j ∈ Finset.range d,(U j x : ℝ))-3) := by
  unfold prefixCost
  apply Finset.sum_congr rfl
  intro x _
  rw [prefix_hinge_linear (fun j => U j x) d hd (fun j _ => hU j x)]

lemma prefixCost_succ {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U : ℕ → Ω → ℕ) (hU : ∀ j x,1 ≤ U j x)
    (d : ℕ) (hd : 3 ≤ d) :
    prefixCost μ U (d+1)-prefixCost μ U d = ∑ x,μ x*(U d x : ℝ) := by
  rw [prefixCost_linear μ U hU (d+1) (by omega),prefixCost_linear μ U hU d hd,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_range_succ]
  ring

lemma prefixCost_first_increment {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (U : ℕ → Ω → ℕ) (hU : ∀ j x,1 ≤ U j x) :
    prefixCost μ U 3-prefixCost μ U 2 = (∑ x,μ x*(U 2 x : ℝ))-bothMass μ U := by
  rw [prefixCost_linear μ U hU 3 le_rfl]
  unfold prefixCost bothMass
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  simp_rw [two_hinge_identity (U 0 _) (U 1 _) (hU 0 _) (hU 1 _)]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Shared positive integer slices yield a finite geometric budget with an
explicit joint correction. Different slices may have different distributions. -/
theorem prefix_geometric_bound {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ x,0 ≤ μ x) (U : ℕ → Ω → ℕ)
    (hU : ∀ j x,1 ≤ U j x) (M : ℝ)
    (hmean : ∀ j,2 ≤ j → (∑ x,μ x*(U j x : ℝ)) ≤ M)
    (R : ℕ) (hR : 1 ≤ R) :
    drift (fun j => prefixCost μ U (j+1)) R ≤
      (prefixCost μ U 2-prefixCost μ U 1)/5+M/20-bothMass μ U/25 := by
  have hμU : 0 ≤ ∑ x,μ x*(U 2 x : ℝ) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (Nat.cast_nonneg _))
  have hM : 0 ≤ M := hμU.trans (hmean 2 le_rfl)
  have hBM : bothMass μ U ≤ M := by
    apply le_trans _ (hmean 2 le_rfl)
    unfold bothMass
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hμ x)
    split_ifs
    · exact_mod_cast hU 2 x
    · exact Nat.cast_nonneg _
  apply drift_bound _ M (bothMass μ U) hM hBM _ _ R hR
  · change prefixCost μ U 3-prefixCost μ U 2 ≤ _
    rw [prefixCost_first_increment μ U hU]
    linarith [hmean 2 le_rfl]
  · intro j hj
    change prefixCost μ U (j+1+1)-prefixCost μ U (j+1) ≤ _
    rw [prefixCost_succ μ U hU (j+1) (by omega)]
    exact hmean (j+1) (by omega)

#print axioms prefix_geometric_bound
#print axioms weighted_two_hinge_defect
#print axioms weighted_two_hinge_improvement
#print axioms weighted_prefix_identity
end Erdos7CumulativeHingeDefect
