import Submission.GreedyCodegreeHigherDrift

/-!
Symmetric residual-edge pair weights for the higher local-degree drift.
All original-edge multiplicities are retained. These are identities of
one state; no typical-state assertion is made.
-/
namespace Erdos773.GreedyHigherPairWeights
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyCodegreeDrift GreedyCodegreeHigherDrift GreedyLinearHigherDrift
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

def pairs (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u v : α) : Finset (Finset α) :=
  (incident H I j u).filter (fun e => v ∈ (e \ I).erase u)

abbrev weight (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u v : α) : ℝ :=
  (pairs H I j u v).card

lemma pairs_symm (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u v : α) :
    pairs H I j u v = pairs H I j v u := by
  ext e
  simp only [pairs,incident,mem_filter,mem_erase]
  constructor
  · rintro ⟨⟨he,hu⟩,hvu,hv⟩
    exact ⟨⟨he,hv⟩,hvu.symm,hu⟩
  · rintro ⟨⟨he,hv⟩,huv,hu⟩
    exact ⟨⟨he,hu⟩,huv.symm,hv⟩

lemma weight_symm (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u v : α) :
    weight H I j u v = weight H I j v u := by rw [weight,weight,pairs_symm]

lemma available_filter {H : Finset (Finset α)} {I e : Finset α} {j : ℕ} {u : α}
    (he : e ∈ incident H I j u) :
    (available H I).filter (fun v => v ∈ (e \ I).erase u) = (e \ I).erase u := by
  have hsub := (mem_filter.mp (mem_filter.mp he).1).2.1
  ext v
  simp only [mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨hsub (mem_erase.mp h).2,h⟩⟩

/-- Weighted sums over vertices are exactly sums over original incident
edges and their other residual vertices. -/
theorem weighted_sum (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) (f : α → ℝ) :
    (∑ v ∈ available H I, weight H I j u v*f v) =
      ∑ e ∈ incident H I j u, ∑ v ∈ (e \ I).erase u, f v := by
  classical
  have ht (v : α) : weight H I j u v*f v =
      ∑ e ∈ incident H I j u, if v ∈ (e \ I).erase u then f v else 0 := by
    rw [← sum_filter]
    simp [weight,pairs]
  rw [sum_congr rfl (fun v _ => ht v),sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter,available_filter he]

/-- The row sum is (j-1) times the incident degree. -/
theorem weighted_degree (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    (∑ v ∈ available H I, weight H I j u v) = (j-1:ℕ)*(incident H I j u).card := by
  have hs := weighted_sum H I j u (fun _ => 1)
  simp only [mul_one] at hs
  rw [hs]
  have hc (e : Finset α) (he : e ∈ incident H I j u) : ((e \ I).erase u).card = j-1 := by
    rw [card_erase_of_mem (mem_filter.mp he).2,(mem_filter.mp (mem_filter.mp he).1).2.2]
  simp_rw [sum_const,nsmul_eq_mul,mul_one]
  rw [sum_congr rfl (fun e he => congrArg (Nat.cast : ℕ → ℝ) (hc e he))]
  simp [mul_comm]

/-- The existing closure-weighted neighbor term is this symmetric operator
applied to the vector of simple closure degrees. -/
theorem neighborWeight_eq (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    (neighborWeight H I j u:ℝ) =
      ∑ v ∈ available H I, weight H I j u v*(closes H I v).card := by
  rw [weighted_sum]
  unfold neighborWeight
  push_cast
  rfl

/-- Summing the operator uses its column sums, which equal its row sums. -/
theorem sum_weighted (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (f : α → ℝ) :
    (∑ u ∈ available H I, ∑ v ∈ available H I, weight H I j u v*f v) =
      (j-1:ℕ)*(∑ u ∈ available H I, ((incident H I j u).card:ℝ)*f u) := by
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro u hu
  simp_rw [weight_symm H I j _ u]
  rw [← sum_mul,weighted_degree]
  ring

#print axioms pairs_symm
#print axioms weight_symm
#print axioms available_filter
#print axioms weighted_sum
#print axioms weighted_degree
#print axioms neighborWeight_eq
#print axioms sum_weighted
end
end Erdos773.GreedyHigherPairWeights
