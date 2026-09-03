import Submission.GreedyCodegreeGrowingExtraction
import Submission.GreedySquareCertificate

/-! Square-Sidon extraction without a linearizing thinning step. -/
namespace Erdos773.GreedyCodegreeSquareCertificate
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
open SquareCollisionLinearization HypergraphDegreeTrim GreedyHorizonFactors
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

/-- Trimming at an arbitrary threshold keeps the exact first-moment loss. -/
theorem trim_at_threshold {α : Type*} [DecidableEq α] (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (h4 : ∀ e ∈ H, e.card = 4) (D : ℝ) (hD : 0 < D) :
    ∃ B ⊆ A, (A.card:ℝ)-4*(H.card:ℝ)/D ≤ B.card ∧ ∀ a ∈ B, (degree H a:ℝ) ≤ D := by
  classical
  let B := A.filter (fun a => (degree H a:ℝ) ≤ D)
  let T := A.filter (fun a => ¬(degree H a:ℝ) ≤ D)
  have hpartition : B.card+T.card = A.card := card_filter_add_card_filter_not _
  have hsum : (∑ a ∈ A, (degree H a:ℝ)) = 4*(H.card:ℝ) := by exact_mod_cast degree_sum A H hsub h4
  have hhigh : D*(T.card:ℝ) ≤ 4*(H.card:ℝ) := by
    calc
      _ = ∑ _a ∈ T, D := by simp [mul_comm]
      _ ≤ ∑ a ∈ T, (degree H a:ℝ) := sum_le_sum (fun a ha => (lt_of_not_ge (mem_filter.mp ha).2).le)
      _ ≤ ∑ a ∈ A, (degree H a:ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := hsum
  have hT : (T.card:ℝ) ≤ 4*(H.card:ℝ)/D := (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hhigh)
  have hpR : (B.card:ℝ)+(T.card:ℝ) = A.card := by exact_mod_cast hpartition
  exact ⟨B,filter_subset _ _,by linarith only [hpR,hT],fun a ha => (mem_filter.mp ha).2⟩

/-- The square collision carrier is retained except for degree trimming.
    The original pair codegrees may be as large as m^3. -/
theorem eventually_certificate (Aexp : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (m:ℝ) →
      ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → (N:ℝ) ≤ (m:ℝ)^Aexp →
      ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (pairEdges A a b).card ≤ m^3) →
      ∀ D : ℝ, 0 < D → D ≤ (m:ℝ)^300 →
      τ*((A.card:ℝ)-4*(edges A).card/D)/(2*(m:ℝ)^100) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  filter_upwards [GreedyCodegreeGrowingExtraction.eventually_selection (α := ℕ) Aexp] with m hm
  intro τ hτ hbudget N A hAN hNm hAP hcodeg D hD hDm
  obtain ⟨B,hBA,hBcard,hBdegree⟩ := trim_at_threshold A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) D hD
  have hBAP := hAP.mono (show (B.image (fun n : ℕ => n^2):Set ℕ) ⊆ A.image (fun n : ℕ => n^2) by
    exact_mod_cast image_subset_image hBA)
  have hBN := hBA.trans hAN
  have hBupper : (B.card:ℝ) ≤ (m:ℝ)^Aexp := by
    have hh : B.card ≤ N := by simpa using card_le_card hBN
    exact (by exact_mod_cast hh : (B.card:ℝ) ≤ N).trans hNm
  have hdegrees : ∀ a ∈ B, degree (edges B) a ≤ m^300 := by
    intro a ha
    have hmono : (degree (edges B) a:ℝ) ≤ degree (edges A) a := by
      exact_mod_cast degree_mono (edges_mono hBA) a
    exact_mod_cast (hmono.trans (hBdegree a ha)).trans hDm
  have hpairs : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → FourUniformRegularization.pairDegree (edges B) a b ≤ m^3 := by
    intro a ha b hb hab
    exact (card_le_card (pairEdges_mono hBA a b)).trans (hcodeg a (hBA ha) b (hBA hb) hab)
  obtain ⟨I,hIB,hI,hIcard⟩ := hm τ hτ hbudget B hBupper (edges B)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he f hf hne => intersection_card_le_two hBAP he hf hne) hdegrees hpairs
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIB hBAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card ≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIB.trans hBN)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ) ≠ 0))] at hmax
  have hscale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBcard (by linarith only [hτ] : 0 ≤ τ))
    (by positivity : (0:ℝ) ≤ 2*(m:ℝ)^100)
  exact hscale.trans (by rw [mul_comm τ]; exact hIcard.trans (by exact_mod_cast hmax))

#print axioms trim_at_threshold
#print axioms eventually_certificate
end
end Erdos773.GreedyCodegreeSquareCertificate
