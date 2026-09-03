import Submission.DominantFiberProjection
import Submission.RankCriticalPartitions

/-!
A lower bound on cycle-decomposition size from ordered cuts and one vertex
representative in each colour class. This does not supply the upper bound
required for Erdős 184.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.OrderedCutBudget
open RankCriticalCuts RankCriticalPartitions DominantFiberProjection
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}

def threshold (f : V → Fin n) (j : Fin n) : V → Bool := fun v => @decide (f v < j) (Fin.decLt (f v) j)

noncomputable def crossedThresholds (G : SimpleGraph V) (f : V → Fin n)
    (H : G.Subgraph) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (H.edgeSet \ (monochromatic G (threshold f j)).edgeSet).Nonempty)

/-- Every visited label other than the smallest has a crossed threshold
immediately below it. Connectedness is sufficient for this step. -/
lemma image_card_le_crossed_add_one (f : V → Fin n) (H : G.Subgraph)
    (hc : H.coe.Connected) :
    (f '' H.verts).ncard ≤ (crossedThresholds G f H).card + 1 := by
  let I := (f '' H.verts).toFinset
  have hne : I.Nonempty := by
    obtain ⟨u⟩ := hc.nonempty
    exact ⟨f u.val,Set.mem_toFinset.mpr ⟨u.val,u.property,rfl⟩⟩
  let a := I.min' hne
  have ha : a ∈ I := Finset.min'_mem I hne
  have hsub : I.erase a ⊆ crossedThresholds G f H := by
    intro j hj
    have hjI := (Finset.mem_erase.mp hj).2
    have hja := (Finset.mem_erase.mp hj).1
    have haj : a < j := lt_of_le_of_ne (Finset.min'_le I j hjI) (Ne.symm hja)
    obtain ⟨u,hu,hfu⟩ := Set.mem_toFinset.mp ha
    obtain ⟨v,hv,hfv⟩ := Set.mem_toFinset.mp hjI
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ j,?_⟩
    by_contra hn
    have hsub : H.edgeSet ⊆ (monochromatic G (threshold f j)).edgeSet := by
      intro e he
      by_contra he'
      exact hn ⟨e,he,he'⟩
    let φ : H.coe →g monochromatic G (threshold f j) := {
      toFun := Subtype.val
      map_rel' := fun {x y} h => hsub (show s(x.val,y.val) ∈ H.edgeSet from h) }
    have hr := (hc.preconnected ⟨u,hu⟩ ⟨v,hv⟩).map φ
    have heq := color_eq_of_reachable G (threshold f j) hr
    change decide (f u < j) = decide (f v < j) at heq
    simp only [hfu,hfv,haj,lt_self_iff_false,decide_true,decide_false] at heq
    cases heq
  have hb := Finset.card_le_card hsub
  have he := Finset.card_erase_add_one ha
  have hi : I.card = (f '' H.verts).ncard := (Set.ncard_eq_toFinset_card' (f '' H.verts)).symm
  omega

noncomputable def variation (G : SimpleGraph V) (f : V → Fin n) : ℕ :=
  ∑ j, (G.edgeSet \ (monochromatic G (threshold f j)).edgeSet).ncard

omit [Fintype V] in
/-- Double-count crossings between decomposition pieces and ordered cuts. -/
lemma crossed_sum (f : V → Fin n) (D : Finset G.Subgraph) :
    (∑ H ∈ D, (crossedThresholds G f H).card) =
      ∑ j, (crossingPieces D (monochromatic G (threshold f j))).card := by
  simp only [crossedThresholds,crossingPieces,Finset.card_filter]
  rw [Finset.sum_comm]

lemma image_incidence_bound (f : V → Fin n) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    2 * (∑ H ∈ D, (f '' H.verts).ncard) ≤ 2 * D.card + variation G f := by
  have hsum := Finset.sum_le_sum (s := D)
    (fun H hH => image_card_le_crossed_add_one f H (hc H hH).1)
  rw [Finset.sum_add_distrib,crossed_sum] at hsum
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at hsum
  have hcuts := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    crossingPieces_budget G (monochromatic G (threshold f j))
      (monochromatic_closed G (threshold f j)) D hc hd)
  rw [← Finset.mul_sum] at hcuts
  change _ ≤ variation G f at hcuts
  omega

/-- Retain the exact penalty for pieces that visit a label but omit its
chosen representative. This strengthens the degree-only lower bound. -/
lemma degree_budget_with_missed (f : V → Fin n) (r : Fin n → V)
    (hr : Function.RightInverse r f) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    (∑ j, G.degree (r j)) + 2 * (∑ j, (missedPieces f r D j).card) ≤
      2 * D.card + variation G f := by
  rw [incidence_degree_identity f r hr D hc hd]
  exact image_incidence_bound f D hc hd

/-- The representative degree demand is paid for by twice the piece count
plus the sum of the ordered cut sizes. -/
lemma degree_budget (f : V → Fin n) (r : Fin n → V)
    (hr : Function.RightInverse r f) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) :
    (∑ j, G.degree (r j)) ≤ 2 * D.card + variation G f := by
  have hi := incidence_degree_identity f r hr D hc hd
  have hb := image_incidence_bound f D hc hd
  omega

/-- A numerical lower bound ready for application to layered constructions. -/
lemma decomposition_lower (f : V → Fin n) (r : Fin n → V)
    (hr : Function.RightInverse r f) (a b : ℕ)
    (ha : a ≤ ∑ j, G.degree (r j)) (hb : variation G f ≤ b)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : a ≤ 2 * D.card + b :=
  ha.trans ((degree_budget f r hr D hc hd).trans (Nat.add_le_add_left hb _))

end Erdos184.OrderedCutBudget
