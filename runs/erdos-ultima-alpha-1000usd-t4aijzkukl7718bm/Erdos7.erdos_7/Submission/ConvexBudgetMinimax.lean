import Submission.FiniteKernelMinimax
import Submission.BudgetBaselineAnchor

/-! A compact-choice minimax application to the actual anchored family budgets.
The test family is not assumed finite. A UNIFORM negative margin is explicit;
no arithmetic estimate establishing that margin is asserted here. -/
namespace Erdos7ConvexBudgetMinimax
open scoped BigOperators
open Set Erdos7FiniteKernelMinimax Erdos7BudgetBaselineAnchor
open Erdos7BackwardFamilyBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Extend the existing finite-test theorem using compactness. All finite
probability mixtures, not just isolated tests, appear on the right. -/
theorem compact_tests {T J : Type*} [Fintype J]
    (K : Set (J → ℝ)) (hne : K.Nonempty) (hc : Convex ℝ K) (hk : IsCompact K)
    (f : T → (J → ℝ) →ᵃ[ℝ] ℝ) (hf : ∀ t, Continuous (f t)) (b : T → ℝ) :
    (∃ x ∈ K, ∀ t, f t x ≤ b t) ↔
      ∀ s : Finset T, ∀ w : s → ℝ,
        (∀ t, 0 ≤ w t) → (∑ t, w t) = 1 →
        ∃ x ∈ K, (∑ t, w t * f t.val x) ≤ ∑ t, w t * b t.val := by
  classical
  constructor
  · rintro ⟨x,hx,h⟩ s w hw _
    exact ⟨x,hx,Finset.sum_le_sum (fun t _ =>
      mul_le_mul_of_nonneg_left (h t.val) (hw t))⟩
  · intro h
    let C : T → Set (J → ℝ) := fun t => {x | f t x ≤ b t}
    have hclosed (t : T) : IsClosed (C t) := isClosed_le (hf t) continuous_const
    have hfinite (s : Finset T) : (K ∩ ⋂ t ∈ s, C t).Nonempty := by
      let fs : (J → ℝ) →ᵃ[ℝ] (s → ℝ) := AffineMap.pi (fun t : s => f t.val)
      have hfs : Continuous fs := continuous_pi (fun t => hf t.val)
      obtain ⟨x,hx,hcost⟩ :=
        (exists_common_choice_iff K hne hc hk fs hfs (fun t : s => b t.val)).mpr (h s)
      refine ⟨x,hx,Set.mem_iInter₂.mpr ?_⟩
      intro t ht
      exact hcost ⟨t,ht⟩
    obtain ⟨x,hx,hall⟩ := hk.inter_iInter_nonempty C hclosed hfinite
    exact ⟨x,hx,fun t => Set.mem_iInter.mp hall t⟩

/-- One convex monotone test per actual family label, anchored at lo. -/
def ValidTest {A : Type*} [Fintype A] (F : ℝ → ℝ) (lo hi : ℝ)
    (φ : A → ℝ → ℝ) : Prop :=
  (∀ a, ConvexOn ℝ Set.univ (φ a) ∧ Monotone (φ a) ∧ φ a lo = 0) ∧
  (∀ t ∈ Set.Icc lo hi, F lo + ∑ a, φ a t ≤ F t)

private lemma convex_sum {I : Type*} (s : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0 : ℝ) convex_univ)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_apply] using (hf i).add ih

/-- Mixtures keep the labels independent. Averages are taken only between
test profiles; counts belonging to different family labels are never equated. -/
theorem valid_average {A I : Type*} [Fintype A] [Fintype I]
    (F : ℝ → ℝ) (lo hi : ℝ) (φ : I → A → ℝ → ℝ)
    (hφ : ∀ i, ValidTest F lo hi (φ i))
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1) :
    ValidTest F lo hi (fun a t => ∑ i, w i * φ i a t) := by
  refine ⟨?_,?_⟩
  · intro a
    refine ⟨?_,?_,?_⟩
    · apply convex_sum
      intro i
      simpa only [smul_eq_mul] using ((hφ i).1 a).1.smul (hw i)
    · intro s t hst
      exact Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (((hφ i).1 a).2.1 hst) (hw i))
    · simp only [((hφ _).1 a).2.2, mul_zero, Finset.sum_const_zero]
  · intro t ht
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left ((hφ i).2 t ht) (hw i))
    simp_rw [mul_add,Finset.mul_sum] at hh
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul,
      ← Finset.sum_mul,hs,one_mul,Finset.sum_comm] at hh
    exact hh

/-- Excess of the anchored test integral over the mass. Counts are fixed
functions of the finite actual space; the measure is the decision variable. -/
def payoff {A Ω : Type*} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo : ℝ) (X : A → Ω → ℝ)
    (φ : A → ℝ → ℝ) (μ : Ω → ℝ) : ℝ :=
  ∑ x, μ x * (F lo - 1 + ∑ a, φ a (X a x))

def payoffMap {A Ω : Type*} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo : ℝ) (X : A → Ω → ℝ) (φ : A → ℝ → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun := payoff F lo X φ
  map_add' μ ν := by simp [payoff,add_mul,Finset.sum_add_distrib]
  map_smul' c μ := by simp [payoff,Finset.mul_sum,mul_assoc]

lemma payoff_continuous {A Ω : Type*} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo : ℝ) (X : A → Ω → ℝ) (φ : A → ℝ → ℝ) :
    Continuous (payoff F lo X φ) := by
  apply continuous_finset_sum
  intro x _
  exact (continuous_apply x).mul continuous_const

lemma payoff_average {A Ω I : Type*} [Fintype A] [Fintype Ω] [Fintype I]
    (F : ℝ → ℝ) (lo : ℝ) (X : A → Ω → ℝ)
    (φ : I → A → ℝ → ℝ) (w : I → ℝ) (hs : (∑ i, w i) = 1) (μ : Ω → ℝ) :
    payoff F lo X (fun a t => ∑ i, w i * φ i a t) μ =
      ∑ i, w i * payoff F lo X (φ i) μ := by
  unfold payoff
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm (s := (Finset.univ : Finset A))]
  simp_rw [← Finset.mul_sum]
  have hh : (∑ i, w i * (F lo - 1 + ∑ a, φ i a (X a x))) =
      F lo - 1 + ∑ i, w i * ∑ a, φ i a (X a x) := by
    simp_rw [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
  calc
    _ = μ x * (∑ i, w i * (F lo - 1 + ∑ a, φ i a (X a x))) := by rw [hh]
    _ = _ := by simp_rw [Finset.mul_sum]; congr 1; ext i; ring

/-- Exact simultaneous-test minimax for the anchored budget test set.
The right side permits the chosen measure to depend on the ENTIRE test
profile. The uniform bound B is the SAME for all profiles. -/
theorem simultaneous_test_bound {A Ω : Type*} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo hi : ℝ) (X : A → Ω → ℝ)
    (K : Set (Ω → ℝ)) (hne : K.Nonempty) (hc : Convex ℝ K) (hk : IsCompact K)
    (B : ℝ) :
    (∃ μ ∈ K, ∀ φ, ValidTest F lo hi φ → payoff F lo X φ μ ≤ B) ↔
      (∀ φ, ValidTest F lo hi φ → ∃ μ ∈ K, payoff F lo X φ μ ≤ B) := by
  classical
  constructor
  · rintro ⟨μ,hμ,h⟩ φ hφ
    exact ⟨μ,hμ,h φ hφ⟩
  · intro h
    let T := {φ : A → ℝ → ℝ // ValidTest F lo hi φ}
    let f : T → (Ω → ℝ) →ᵃ[ℝ] ℝ :=
      fun φ => (payoffMap F lo X φ.val).toAffineMap
    have hf (φ : T) : Continuous (f φ) := payoff_continuous F lo X φ.val
    have hall : ∀ s : Finset T, ∀ w : s → ℝ,
        (∀ t, 0 ≤ w t) → (∑ t, w t) = 1 →
        ∃ μ ∈ K, (∑ t, w t * f t.val μ) ≤ ∑ t, w t * B := by
      intro s w hw hs
      let ψ : s → A → ℝ → ℝ := fun t => t.val.val
      have hψ : ∀ t, ValidTest F lo hi (ψ t) := fun t => t.val.property
      obtain ⟨μ,hμ,hm⟩ := h _ (valid_average F lo hi ψ hψ w hw hs)
      refine ⟨μ,hμ,?_⟩
      change (∑ t, w t * payoff F lo X (ψ t) μ) ≤ ∑ t, w t * B
      rw [← payoff_average F lo X ψ w hs μ,← Finset.sum_mul,hs,one_mul]
      exact hm
    obtain ⟨μ,hμ,hm⟩ := (compact_tests K hne hc hk f hf (fun _ => B)).mpr hall
    exact ⟨μ,hμ,fun φ hφ => hm ⟨φ,hφ⟩⟩

lemma payoff_eq_excess {A Ω : Type*} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo : ℝ) (X : A → Ω → ℝ)
    (φ : A → ℝ → ℝ) (μ : Ω → ℝ) :
    payoff F lo X φ μ =
      (∑ x, μ x * (F lo + ∑ a, φ a (X a x))) - ∑ x, μ x := by
  unfold payoff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- An actual HasBudget supplies one member of the SAME test set whose payoff
is nonnegative. This uses exact anchoring and merging, not a common family
argument or an assumed finite-dimensional test approximation. -/
theorem budget_forces_nonnegative_test {A Ω : Type} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo hi : ℝ) (X : A → Ω → ℝ) (μ : Ω → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hlh : lo ≤ hi)
    (hX : ∀ a x, X a x ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi)) (hb : HasBudget μ X F lo hi) :
    ∃ φ, ValidTest F lo hi φ ∧ 0 ≤ payoff F lo X φ μ := by
  have hab := anchor_budget μ X F lo hi hμ hlh hX hF hb
  obtain ⟨φ,hφ,_,hd,hb⟩ := merged_anchored_budget μ X F lo hi hab
  refine ⟨φ,⟨hφ,hd⟩,?_⟩
  rw [payoff_eq_excess]
  exact sub_nonneg.mpr hb

/-- A rigorous test-dependent measure criterion. A response for EVERY entire
valid profile, with ONE UNIFORM negative margin, yields a SINGLE measure
which cannot have the future budget. This is conditional: the quantitative
response hypothesis is not supplied for odd covering systems. -/
theorem exists_no_budget {A Ω : Type} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo hi : ℝ) (X : A → Ω → ℝ)
    (K : Set (Ω → ℝ)) (hne : K.Nonempty) (hc : Convex ℝ K) (hk : IsCompact K)
    (hK : ∀ μ ∈ K, ∀ x, 0 ≤ μ x) (hlh : lo ≤ hi)
    (hX : ∀ a x, X a x ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi))
    (ε : ℝ) (hε : 0 < ε)
    (hresponse : ∀ φ, ValidTest F lo hi φ →
      ∃ μ ∈ K, payoff F lo X φ μ ≤ -ε) :
    ∃ μ ∈ K, ¬ HasBudget μ X F lo hi := by
  obtain ⟨μ,hμ,hm⟩ :=
    (simultaneous_test_bound F lo hi X K hne hc hk (-ε)).mpr hresponse
  refine ⟨μ,hμ,?_⟩
  intro hb
  obtain ⟨φ,hφ,hpos⟩ :=
    budget_forces_nonnegative_test F lo hi X μ (hK μ hμ) hlh hX hF hb
  have hn := hm φ hφ
  linarith

/-- Apply after an arithmetic/tower theorem has proved that full coverage
would force the budget for EVERY feasible measure. Both that theorem and the
uniform test response remain explicit, independent hypotheses. -/
theorem not_all_choices_budget {A Ω : Type} [Fintype A] [Fintype Ω]
    (F : ℝ → ℝ) (lo hi : ℝ) (X : A → Ω → ℝ)
    (K : Set (Ω → ℝ)) (hne : K.Nonempty) (hc : Convex ℝ K) (hk : IsCompact K)
    (hK : ∀ μ ∈ K, ∀ x, 0 ≤ μ x) (hlh : lo ≤ hi)
    (hX : ∀ a x, X a x ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi))
    (ε : ℝ) (hε : 0 < ε)
    (hresponse : ∀ φ, ValidTest F lo hi φ →
      ∃ μ ∈ K, payoff F lo X φ μ ≤ -ε) :
    ¬ ∀ μ ∈ K, HasBudget μ X F lo hi := by
  obtain ⟨μ,hμ,hn⟩ := exists_no_budget F lo hi X K hne hc hk hK hlh hX hF ε hε hresponse
  exact fun h => hn (h μ hμ)

#print axioms compact_tests
#print axioms valid_average
#print axioms payoff_average
#print axioms simultaneous_test_bound
#print axioms budget_forces_nonnegative_test
#print axioms exists_no_budget
#print axioms not_all_choices_budget
end Erdos7ConvexBudgetMinimax
