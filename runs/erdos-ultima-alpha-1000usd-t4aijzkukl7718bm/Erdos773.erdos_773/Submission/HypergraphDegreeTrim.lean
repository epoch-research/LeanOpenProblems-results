import FormalConjecturesUtil

/-! Removing vertices of high incidence degree from a finite four-uniform hypergraph. -/
namespace Erdos773.HypergraphDegreeTrim
open Finset
set_option maxHeartbeats 1000000
variable {α : Type*} [DecidableEq α]

def degree (H : Finset (Finset α)) (a : α) : ℕ :=
  (H.filter (fun e => a ∈ e)).card

lemma degree_mono {H G : Finset (Finset α)} (hHG : H ⊆ G) (a : α) :
    degree H a ≤ degree G a :=
  card_le_card (filter_subset_filter _ hHG)

lemma degree_sum (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (h4 : ∀ e ∈ H, e.card = 4) :
    (∑ a ∈ A, degree H a) = 4*H.card := by
  calc
    _ = ∑ e ∈ H, (A.filter (fun a => a ∈ e)).card := by
      exact sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun a e => a ∈ e)
    _ = ∑ e ∈ H, e.card := by
      apply sum_congr rfl
      intro e he
      have hh : A.filter (fun a => a ∈ e) = e := by
        ext a
        simp only [mem_filter]
        exact ⟨fun h => h.2,fun h => ⟨hsub e he h,h⟩⟩
      rw [hh]
    _ = 4*H.card := by rw [sum_congr rfl h4]; simp [mul_comm]

/-- At least half the vertices have incidence degree at most eight times
the number of edges per ambient vertex. Degrees are measured in the original
hypergraph, so they can only decrease after restriction. -/
theorem trim (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (h4 : ∀ e ∈ H, e.card = 4)
    (K : ℝ) (hK : 0 < K) (hE : (H.card : ℝ) ≤ K*A.card) :
    ∃ B ⊆ A, A.card ≤ 2*B.card ∧ ∀ a ∈ B, (degree H a : ℝ) ≤ 8*K := by
  classical
  let B := A.filter (fun a => (degree H a : ℝ) ≤ 8*K)
  let T := A.filter (fun a => ¬ (degree H a : ℝ) ≤ 8*K)
  have hpartition : B.card+T.card = A.card := by
    exact card_filter_add_card_filter_not (fun a => (degree H a : ℝ) ≤ 8*K)
  have hsum : (∑ a ∈ A, (degree H a : ℝ)) = 4*(H.card : ℝ) := by
    exact_mod_cast degree_sum A H hsub h4
  have hhigh : 8*K*T.card ≤ 4*(H.card : ℝ) := by
    calc
      _ = ∑ _a ∈ T, 8*K := by simp [mul_comm]
      _ ≤ ∑ a ∈ T, (degree H a : ℝ) := by
        apply sum_le_sum
        intro a ha
        exact (lt_of_not_ge (mem_filter.mp ha).2).le
      _ ≤ ∑ a ∈ A, (degree H a : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := hsum
  have hc : (2 : ℝ)*T.card ≤ A.card := by nlinarith only [hhigh,hE,hK]
  have hcN : 2*T.card ≤ A.card := by exact_mod_cast hc
  refine ⟨B,filter_subset _ _,by omega,?_⟩
  intro a ha
  exact (mem_filter.mp ha).2

#print axioms degree_sum
#print axioms trim
end Erdos773.HypergraphDegreeTrim
