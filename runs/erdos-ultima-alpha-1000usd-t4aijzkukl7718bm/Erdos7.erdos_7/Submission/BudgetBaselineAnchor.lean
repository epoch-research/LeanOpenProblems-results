import Submission.BackwardFamilyBudget

/-! Exact anchoring at the lower endpoint of a finite family budget.
This is an auxiliary normalization theorem, not a covering obstruction. -/
namespace Erdos7BudgetBaselineAnchor
open scoped BigOperators
open Erdos7BackwardFamilyBudget
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- A common cutoff raises all independently evaluated convex tests without
exceeding a monotone upper diagonal. At the lower endpoint the new diagonal
is exactly the prescribed upper value. No two-contact hypothesis is needed. -/
theorem anchor_finite_sum {I : Type*} [Fintype I]
    (φ : I → ℝ → ℝ) (b : ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hlh : lo ≤ hi)
    (hφ : ∀ i, ConvexOn ℝ Set.univ (φ i) ∧ Monotone (φ i))
    (hF : MonotoneOn F (Set.Icc lo hi))
    (hdiag : ∀ t ∈ Set.Icc lo hi, b + ∑ i, φ i t ≤ F t) :
    ∃ (d : ℝ) (ψ : I → ℝ → ℝ),
      (∀ i, ConvexOn ℝ Set.univ (ψ i) ∧ Monotone (ψ i)) ∧
      d + (∑ i, ψ i lo) = F lo ∧
      (∀ t ∈ Set.Icc lo hi, d + ∑ i, ψ i t ≤ F t) ∧
      (∀ x : I → ℝ, (∀ i, x i ∈ Set.Icc lo hi) →
        b + ∑ i, φ i (x i) ≤ d + ∑ i, ψ i (x i)) := by
  classical
  have hlo : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlh⟩
  by_cases htop : b + ∑ i, φ i hi ≤ F lo
  · refine ⟨F lo, (fun _ _ => 0), ?_, by simp, ?_, ?_⟩
    · intro i
      exact ⟨convexOn_const _ convex_univ, monotone_const⟩
    · intro t ht
      simpa using hF hlo ht ht.1
    · intro x hx
      have hs : (∑ i, φ i (x i)) ≤ ∑ i, φ i hi :=
        Finset.sum_le_sum (fun i _ => (hφ i).2 (hx i).2)
      simpa using (add_le_add (le_refl b) hs).trans htop
  · let f : ℝ → ℝ := fun t => b + ∑ i, φ i t
    have hc : Continuous f := by
      apply Continuous.add continuous_const
      apply continuous_finset_sum
      intro i _
      exact continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ (hφ i).1)
    have ht : F lo ∈ Set.Icc (f lo) (f hi) :=
      ⟨hdiag lo hlo, le_of_lt (lt_of_not_ge htop)⟩
    obtain ⟨t, htI, htf⟩ := intermediate_value_Icc hlh hc.continuousOn ht
    let ψ : I → ℝ → ℝ := fun i x => max (φ i x) (φ i t)
    refine ⟨b, ψ, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(hφ i).1.sup (convexOn_const _ convex_univ),
        (hφ i).2.max monotone_const⟩
    · have he : (∑ i, ψ i lo) = ∑ i, φ i t := by
        apply Finset.sum_congr rfl
        intro i _
        exact max_eq_right ((hφ i).2 htI.1)
      rw [he]
      exact htf
    · intro u hu
      rcases le_total u t with hut | htu
      · have he : (∑ i, ψ i u) = ∑ i, φ i t := by
          apply Finset.sum_congr rfl
          intro i _
          exact max_eq_right ((hφ i).2 hut)
        rw [he]
        exact htf.le.trans (hF hlo hu hu.1)
      · have he : (∑ i, ψ i u) = ∑ i, φ i u := by
          apply Finset.sum_congr rfl
          intro i _
          exact max_eq_left ((hφ i).2 htu)
        rw [he]
        exact hdiag u hu
    · intro x _
      exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ => le_max_left (φ i (x i)) (φ i t)))

/-- An anchored budget has exact constant `F lo` and tests vanishing at `lo`.
The family arguments remain independently indexed. -/
def HasAnchoredBudget {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (pick : I → α) (φ : I → ℝ → ℝ),
    (∀ i, ConvexOn ℝ Set.univ (φ i) ∧ Monotone (φ i) ∧ φ i lo = 0) ∧
    (∀ t ∈ Set.Icc lo hi, F lo + ∑ i, φ i t ≤ F t) ∧
    ((∑ x, μ x) ≤ ∑ x, μ x * (F lo + ∑ i, φ i (X (pick i) x)))

theorem anchor_budget {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hlh : lo ≤ hi)
    (hX : ∀ a x, X a x ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi))
    (hb : HasBudget μ X F lo hi) : HasAnchoredBudget μ X F lo hi := by
  classical
  obtain ⟨I, fi, b, pick, φ, hφ, hd, hb⟩ := hb
  letI : Fintype I := fi
  obtain ⟨d, ψ, hψ, he, hdiag, hmajor⟩ :=
    anchor_finite_sum φ b F lo hi hlh hφ hF hd
  let χ : I → ℝ → ℝ := fun i t => ψ i t - ψ i lo
  have hid (x : I → ℝ) : F lo + (∑ i, χ i (x i)) = d + ∑ i, ψ i (x i) := by
    simp only [χ, Finset.sum_sub_distrib]
    linarith
  refine ⟨I, fi, pick, χ, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, by simp [χ]⟩
    · simpa only [χ, sub_eq_add_neg] using (hψ i).1.add_const (-ψ i lo)
    · intro s t hst
      exact sub_le_sub_right ((hψ i).2 hst) _
  · intro t ht
    rw [hid (fun _ => t)]
    exact hdiag t ht
  · apply hb.trans
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hμ x)
    rw [hid]
    exact hmajor (fun i => X (pick i) x) (fun i => hX (pick i) x)

theorem anchored_budget_is_budget {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hb : HasAnchoredBudget μ X F lo hi) : HasBudget μ X F lo hi := by
  obtain ⟨I, fi, pick, φ, hφ, hd, hb⟩ := hb
  exact ⟨I, fi, F lo, pick, φ, (fun i => ⟨(hφ i).1, (hφ i).2.1⟩), hd, hb⟩

theorem budget_iff_anchored {Ω α : Type} [Fintype Ω]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hlh : lo ≤ hi)
    (hX : ∀ a x, X a x ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi)) :
    HasBudget μ X F lo hi ↔ HasAnchoredBudget μ X F lo hi :=
  ⟨anchor_budget μ X F lo hi hμ hlh hX hF,
    anchored_budget_is_budget μ X F lo hi⟩

private lemma convex_sum {I : Type*} (s : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) :
    ConvexOn ℝ Set.univ (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0 : ℝ) convex_univ)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Pi.add_apply] using (hf i).add ih

/-- For a finite family index, merge all tests with the same label. Anchoring
then bounds every individual test on the finite count interval. This supplies
bounds for finite-dimensional formulations, not a minimax theorem. -/
theorem merged_anchored_budget {Ω α : Type} [Fintype Ω] [Fintype α]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (F : ℝ → ℝ) (lo hi : ℝ)
    (hb : HasAnchoredBudget μ X F lo hi) :
    ∃ ψ : α → ℝ → ℝ,
      (∀ a, ConvexOn ℝ Set.univ (ψ a) ∧ Monotone (ψ a) ∧ ψ a lo = 0) ∧
      (∀ a t, t ∈ Set.Icc lo hi → 0 ≤ ψ a t ∧ ψ a t ≤ F t - F lo) ∧
      (∀ t ∈ Set.Icc lo hi, F lo + ∑ a, ψ a t ≤ F t) ∧
      ((∑ x, μ x) ≤ ∑ x, μ x * (F lo + ∑ a, ψ a (X a x))) := by
  classical
  obtain ⟨I, fi, pick, φ, hφ, hd, hb⟩ := hb
  letI : Fintype I := fi
  let θ : α → I → ℝ → ℝ := fun a i t => if pick i = a then φ i t else 0
  let ψ : α → ℝ → ℝ := fun a t => ∑ i, θ a i t
  have hθ (a : α) (i : I) : ConvexOn ℝ Set.univ (θ a i) ∧ Monotone (θ a i) ∧
      θ a i lo = 0 := by
    by_cases he : pick i = a
    · simpa only [θ, he, if_true] using hφ i
    · simp only [θ, he, if_false]
      exact ⟨convexOn_const _ convex_univ, monotone_const, True.intro⟩
  have hψ (a : α) : ConvexOn ℝ Set.univ (ψ a) ∧ Monotone (ψ a) ∧ ψ a lo = 0 := by
    refine ⟨convex_sum Finset.univ (θ a) (fun i => (hθ a i).1), ?_, ?_⟩
    · intro u v huv
      exact Finset.sum_le_sum (fun i _ => (hθ a i).2.1 huv)
    · exact Finset.sum_eq_zero (fun i _ => (hθ a i).2.2)
  have hsum (t : ℝ) : (∑ a, ψ a t) = ∑ i, φ i t := by
    dsimp only [ψ, θ]
    rw [Finset.sum_comm]
    simp
  have hactual (x : Ω) : (∑ a, ψ a (X a x)) = ∑ i, φ i (X (pick i) x) := by
    dsimp only [ψ, θ]
    rw [Finset.sum_comm]
    simp
  have hdiag (t : ℝ) (ht : t ∈ Set.Icc lo hi) : F lo + (∑ a, ψ a t) ≤ F t := by
    rw [hsum]
    exact hd t ht
  refine ⟨ψ, hψ, ?_, hdiag, ?_⟩
  · intro a t ht
    have hn (j : α) : 0 ≤ ψ j t := by
      rw [← (hψ j).2.2]
      exact (hψ j).2.1 ht.1
    refine ⟨hn a, ?_⟩
    have hs : ψ a t ≤ ∑ j, ψ j t :=
      Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ a)
    linarith [hdiag t ht]
  · simpa only [hactual] using hb

/-- Once the budget is genuinely anchored, subtracting a mass at the lower
endpoint is legitimate even if it exceeds the comparison law's atom there.
All other comparison weights are nonnegative. This statement requires an
actual family comparison and does not assert one for an arithmetic tower. -/
theorem pruned_budget_bound {Ω Ξ α : Type} [Fintype Ω] [Fintype Ξ]
    (μ : Ω → ℝ) (X : α → Ω → ℝ) (ν : Ξ → ℝ) (Z : Ξ → ℝ)
    (F : ℝ → ℝ) (lo hi B : ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ z, 0 ≤ ν z) (hlh : lo ≤ hi)
    (hX : ∀ a x, X a x ∈ Set.Icc lo hi)
    (hZ : ∀ z, Z z ∈ Set.Icc lo hi)
    (hF : MonotoneOn F (Set.Icc lo hi))
    (hmass : (∑ z, ν z) = (∑ x, μ x) + B)
    (hcomp : ∀ a (φ : ℝ → ℝ), ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x, μ x * φ (X a x)) + B * φ lo ≤ ∑ z, ν z * φ (Z z))
    (hb : HasBudget μ X F lo hi) :
    (∑ x, μ x) ≤ (∑ z, ν z * F (Z z)) - B * F lo := by
  classical
  obtain ⟨I, fi, pick, φ, hφ, hd, hb⟩ :=
    anchor_budget μ X F lo hi hμ hlh hX hF hb
  letI : Fintype I := fi
  have hi (i : I) : (∑ x, μ x * φ i (X (pick i) x)) ≤
      ∑ z, ν z * φ i (Z z) := by
    simpa only [(hφ i).2.2, mul_zero, add_zero] using
      hcomp (pick i) (φ i) (hφ i).1 (hφ i).2.1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have hd' : (∑ z, ν z * (F lo + ∑ i, φ i (Z z))) ≤
      ∑ z, ν z * F (Z z) :=
    Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hd _ (hZ z)) (hν z))
  have hleft : (∑ x, μ x * (F lo + ∑ i, φ i (X (pick i) x))) =
      (∑ x, μ x) * F lo + ∑ i, ∑ x, μ x * φ i (X (pick i) x) := by
    simp_rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm]
  have hright : (∑ z, ν z * (F lo + ∑ i, φ i (Z z))) =
      ((∑ x, μ x) + B) * F lo + ∑ i, ∑ z, ν z * φ i (Z z) := by
    simp_rw [mul_add, Finset.mul_sum]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_comm, hmass]
  rw [hleft] at hb
  rw [hright] at hd'
  nlinarith

#print axioms merged_anchored_budget
#print axioms pruned_budget_bound
#print axioms anchor_finite_sum
#print axioms anchor_budget
#print axioms budget_iff_anchored
end Erdos7BudgetBaselineAnchor
