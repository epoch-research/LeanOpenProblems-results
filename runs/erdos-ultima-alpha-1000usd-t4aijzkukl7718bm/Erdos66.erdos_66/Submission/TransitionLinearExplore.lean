import Submission.NatPairAlgebraExplore

/-! The first target window after a spatial cutoff is an exactly linear
old/new convolution problem. No solution of that linear problem is asserted. -/
namespace Erdos66TransitionLinear
open AdditiveCombinatorics Erdos66NatPairAlgebra
open scoped Classical

lemma cutoff_disjoint (A F : Finset ℕ) (N : ℕ)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) : Disjoint A F := by
  apply Finset.disjoint_left.mpr
  intro a ha hf
  have h₁ := hA a ha
  have h₂ := hF a hf
  omega

lemma new_self_zero (F : Finset ℕ) (N n : ℕ)
    (hF : ∀ b ∈ F, N ≤ b) (hn : n < 2*N) : sumRep (F : Set ℕ) n = 0 := by
  rw [← pairs_self]
  exact pairs_zero_of_lower F F N N n hF hF (by omega)

/-- Before twice the cutoff, all new representations are mixed. -/
theorem transition_exact (A F : Finset ℕ) (N n : ℕ)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) (hn : n < 2*N) :
    sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n = sumRep (A : Set ℕ) n+2*pairs A F n := by
  rw [sumRep_union_self _ _ _ (cutoff_disjoint A F N hA hF),new_self_zero F N n hF hn,add_zero]

/-- In the transition window the old-point range condition is automatic,
leaving a linear sum of new-membership indicators. -/
theorem transition_linear (A F : Finset ℕ) (N n : ℕ)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) (hn₀ : N ≤ n) (hn₁ : n < 2*N) :
    (sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ) = sumRep (A : Set ℕ) n+
      2*∑ a ∈ A, if n-a ∈ F then (1 : ℝ) else 0 := by
  rw [transition_exact A F N n hA hF hn₁,pairs_eq_filter]
  have he : A.filter (fun a ↦ a ≤ n ∧ n-a ∈ F) = A.filter (fun a ↦ n-a ∈ F) := by
    apply Finset.filter_congr
    intro a ha
    exact and_iff_right (by have := hA a ha; omega)
  rw [he,Finset.card_filter]
  push_cast
  rfl

lemma unchanged_below_cutoff (A F : Finset ℕ) (N n : ℕ)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) (hn : n < N) :
    sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n = sumRep (A : Set ℕ) n := by
  rw [transition_exact A F N n hA hF (by omega),
    pairs_zero_of_lower A F 0 N n (fun a _ ↦ Nat.zero_le a) hF (by omega)]
  omega

/-- The full finite transition problem is equivalent to Boolean linear
constraints in the memberships of the new points. This equivalence alone
does not prove feasibility, nor does it control the next target window. -/
theorem transition_constraints_iff (A F : Finset ℕ) (N : ℕ)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) (q e : ℕ → ℝ) :
    (∀ n ∈ Finset.Ico N (2*N),
      |(sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-q n| ≤ e n) ↔
    (∀ n ∈ Finset.Ico N (2*N),
      |(sumRep (A : Set ℕ) n : ℝ)+2*(∑ a ∈ A, if n-a ∈ F then (1 : ℝ) else 0)-q n| ≤ e n) := by
  constructor <;> intro h n hn
  all_goals have hb := Finset.mem_Ico.mp hn
  · simpa only [transition_linear A F N n hA hF hb.1 hb.2] using h n hn
  · simpa only [transition_linear A F N n hA hF hb.1 hb.2] using h n hn

/-- In this window there is no quadratic new/new contribution even in total. -/
theorem transition_increment_mass (A F T : Finset ℕ) (N : ℕ)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) (hT : ∀ n ∈ T, n < 2*N) :
    (∑ n ∈ T, ((sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n)) ≤
      2*(A.card : ℝ)*F.card := by
  have he (n : ℕ) (hn : n ∈ T) :
      (sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n = 2*pairs A F n := by
    rw [transition_exact A F N n hA hF (hT n hn)]
    push_cast
    ring
  rw [Finset.sum_congr rfl he,← Finset.mul_sum]
  have hh : (∑ n ∈ T, (pairs A F n : ℝ)) ≤ (A.card : ℝ)*F.card := by
    exact_mod_cast pairs_sum_le A F T
  nlinarith

end Erdos66TransitionLinear
