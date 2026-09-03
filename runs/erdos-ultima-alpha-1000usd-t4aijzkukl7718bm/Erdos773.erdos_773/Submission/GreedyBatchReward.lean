import Submission.GreedyBatchCertificate

/-! Exact continuation reward for regular mixed ranks. -/
namespace Erdos773.GreedyBatchReward
open Finset HypergraphDegreeTrim UniformLayerRegularization
open GreedyBatchCertificate GreedyBatchSelection
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma layer_degree_sum (H : Finset (Finset α)) (j D : ℕ)
    (hD : ∀ x, degree (layer H j) x=D) : j*(layer H j).card=Fintype.card α*D := by
  have hh : (∑ x : α, degree (layer H j) x)=∑ e∈layer H j, e.card := by
    have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (univ : Finset α)) (t := layer H j) (fun a e => a∈e)
    simpa only [degree,bipartiteAbove,bipartiteBelow,filter_univ_mem] using he
  have hj := sum_congr rfl (fun e (he : e∈layer H j) => (mem_filter.mp he).2)
  rw [hj] at hh
  simp_rw [hD] at hh
  simpa [mul_comm] using hh.symm

lemma weighted_card_sum (H : Finset (Finset α)) (c : Caps) (h : Regular H c) (w : ℕ → ℝ) :
    (∑ e∈H, (e.card:ℝ)*w e.card)=
      (Fintype.card α:ℝ)*(c.D2*w 2+c.D3*w 3+c.D4*w 4) := by
  have hD (j : ℕ) (hj : j∈Icc 2 4) : j*(layer H j).card=Fintype.card α*c.degree j := by
    obtain ⟨hj2,hj4⟩ := mem_Icc.mp hj
    interval_cases j
    · exact layer_degree_sum H 2 c.D2 h.degree2
    · exact layer_degree_sum H 3 c.D3 h.degree3
    · exact layer_degree_sum H 4 c.D4 h.degree4
  have he := sum_fiberwise_of_maps_to (s := H) (t := Icc 2 4) (g := Finset.card)
    (fun e he => mem_Icc.mpr (h.ranks e he)) (fun e => (e.card:ℝ)*w e.card)
  have hl (j : ℕ) (hj : j∈Icc 2 4) :
      (∑ e∈H.filter (fun e => e.card=j), (e.card:ℝ)*w e.card)=
        (Fintype.card α:ℝ)*c.degree j*w j := by
    calc
      _ = ∑ _e∈layer H j, (j:ℝ)*w j := sum_congr rfl (fun e he => by rw [(mem_filter.mp he).2])
      _ = (j*(layer H j).card:ℕ)*w j := by simp; ring
      _ = _ := by rw [hD j hj]; push_cast; ring
  rw [← he,sum_congr rfl hl]
  have hI : Icc 2 4=({2,3,4}:Finset ℕ) := by decide
  rw [hI]
  simp [Caps.degree]
  ring

def load (c : Caps) (p : ℝ) : ℝ := c.D2*p+c.D3*p^2+c.D4*p^3

def rate (c : Caps) (p δ : ℝ) : ℝ := p*(1-load c p)+δ*(1-p-load c p)

theorem lowerReward_eq (H : Finset (Finset α)) (c : Caps) (h : Regular H c) (p δ : ℝ) :
    lowerReward H p δ=(Fintype.card α:ℝ)*rate c p δ := by
  have h1 := weighted_card_sum H c h (fun j => p^j)
  have h2 := weighted_card_sum H c h (fun j => p^(j-1))
  simp only [lowerReward]
  rw [h1,h2]
  norm_num [rate,load]
  ring

lemma tests_mono {U V : ℕ} (h : U≤V) : tests U≤tests V := by
  have hh : (U:ℝ)≤V := by exact_mod_cast h
  have h0 : (0:ℝ)≤U := Nat.cast_nonneg U
  dsimp [tests]
  nlinarith only [hh,h0]

#print axioms weighted_card_sum
#print axioms lowerReward_eq
#print axioms tests_mono
end
end Erdos773.GreedyBatchReward
