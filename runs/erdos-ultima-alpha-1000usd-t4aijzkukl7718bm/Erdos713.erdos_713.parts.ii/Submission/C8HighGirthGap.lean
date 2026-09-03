import FormalConjecturesUtil
import Submission.TripleShoreC8
import Submission.OrientedCloneCount
import Submission.RescalingDiagnostic

/-! A strict coefficient gap between C8 extremality and families of girth
above eight, under a pure-power asymptotic with exponent at most 5/4.
This does not determine the exponent or prove its rationality. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713C8HighGirthGap
open Erdos713OrientedCloneC8 Erdos713ForestCover Erdos713TripleShoreC8
open Erdos713OrientedCloneCount
set_option maxHeartbeats 2000000
variable {V : Type*}

def SmallAcyclic (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card ≤ 8 → (G.induce (S : Set V)).IsAcyclic

def amplify (G : SimpleGraph V) : SimpleGraph (V ⊕ (V × Fin 3)) :=
  graph (⊥ : SimpleGraph V) (fun p v => G.Adj p.1 v)

theorem amplify_free {G : SimpleGraph V} (hG : SmallAcyclic G) :
    (cycleGraph 8).Free (amplify G) := by
  apply free_of_no_octagon
  intro p q hp hq hA hB
  let S : Finset V := univ.image (fun i => (p i).1) ∪ univ.image q
  have hs : S.card ≤ 8 := by
    have h1 := card_image_le (s := (univ : Finset (Fin 4))) (f := fun i => (p i).1)
    have h2 := card_image_le (s := (univ : Finset (Fin 4))) (f := q)
    have hu := card_union_le (univ.image (fun i => (p i).1)) (univ.image q)
    simp only [card_univ,Fintype.card_fin] at h1 h2
    dsimp only [S]
    omega
  have hpm (i : Fin 4) : (p i).1 ∈ S := mem_union_left _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  have hqm (i : Fin 4) : q i ∈ S := mem_union_right _ (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  let p' : Fin 4 → S × Fin 3 := fun i => (⟨(p i).1,hpm i⟩,(p i).2)
  let q' : Fin 4 → S := fun i => ⟨q i,hqm i⟩
  apply no_octagon (G.induce (S : Set V)).Adj (double_cover_acyclic (hG S hs)) p' q'
  · intro i j hij
    exact hp (congrArg (fun x : S × Fin 3 => (x.1.val,x.2)) hij)
  · intro i j hij
    exact hq (congrArg Subtype.val hij)
  · exact hA
  · exact hB

theorem amplify_edges [Fintype V] (G : SimpleGraph V) :
    Nat.card (amplify G).edgeSet = 6*Nat.card G.edgeSet := by
  have h := graph_edge_card (⊥ : SimpleGraph V) (fun p : V × Fin 3 => fun v => G.Adj p.1 v)
  change Nat.card (amplify G).edgeSet = _ at h
  have hG := G.two_mul_card_edgeFinset
  simp only [card_filter,Fintype.sum_prod_type,edgeFinset_card,← Nat.card_eq_fintype_card] at hG
  have hc : Nat.card {p : (V × Fin 3) × V // G.Adj p.1.1 p.2} =
      3*(2*Nat.card G.edgeSet) := by
    conv_lhs =>
      simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,card_filter,Fintype.sum_prod_type]
      dsimp only
      simp only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,← mul_sum]
    rw [← hG]
  have hz : Nat.card (⊥ : SimpleGraph V).edgeSet = 0 := by simp
  rw [hz,hc] at h
  omega

/-- Every high-girth n-vertex host yields a C8-free 4n-vertex host with six
 times as many edges, irrespective of whether the original host is bipartite. -/
theorem finite_comparison [Fintype V] (G : SimpleGraph V) (hG : SmallAcyclic G) :
    6*Nat.card G.edgeSet ≤ extremalNumber (4*Fintype.card V) (cycleGraph 8) := by
  have h := card_edgeFinset_le_extremalNumber (amplify_free hG)
  have hc : Fintype.card (V ⊕ (V × Fin 3)) = 4*Fintype.card V := by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  rw [← amplify_edges]
  simpa only [edgeFinset_card,Nat.card_eq_fintype_card,hc] using h

lemma scale_bound {α : ℝ} (hα : α ≤ 5/4) : (4 : ℝ)^α < 57/10 := by
  have hle : (4 : ℝ)^α ≤ (4 : ℝ)^(5/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hα
  have hp : ((4 : ℝ)^(5/4 : ℝ))^4 = 1024 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have ht : (4 : ℝ)^(5/4 : ℝ) < 57/10 := by
    by_contra hn
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 57/10) (le_of_not_gt hn) 4
    norm_num [hp] at hh
  exact hle.trans_lt ht

/-- Uniformly over all sufficiently large high-girth hosts, at least five
 percent of the C8 extremal edge count is missing. This is a coefficient
 separation, not an exponent separation. -/
theorem eventual_gap {α c : ℝ} (hα : α ≤ 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), SmallAcyclic G →
      (Nat.card G.edgeSet : ℝ) ≤ (19/20 : ℝ)*extremalNumber n (cycleGraph 8) := by
  have hs : Tendsto (fun n : ℕ => (extremalNumber (4*n) (cycleGraph 8) : ℝ)/
      extremalNumber n (cycleGraph 8)) atTop (𝓝 ((4 : ℝ)^α)) := by
    have hs' := Erdos713RescalingDiagnostic.rescaling_limit (t := ((4 : ℕ) : ℝ))
      hc.ne' (by norm_num) h
    simpa only [← Nat.cast_mul,Nat.floor_natCast] using hs' 
  have hr := Erdos713PolynomialRate.ratio_limit h
  have hp : ∀ᶠ n : ℕ in atTop, 0 < (extremalNumber n (cycleGraph 8) : ℝ) := by
    filter_upwards [hr.eventually_const_lt hc] with n hn
    exact (div_pos_iff.mp hn).elim (fun hh => hh.1) (fun hh =>
      (not_lt_of_ge (Real.rpow_nonneg (Nat.cast_nonneg n) α) hh.2).elim)
  filter_upwards [hs.eventually_lt_const (scale_bound hα),hp] with n hn hp
  intro G hG
  have he := finite_comparison G hG
  simp only [Fintype.card_fin] at he
  have heR : 6*(Nat.card G.edgeSet : ℝ) ≤ extremalNumber (4*n) (cycleGraph 8) := by
    exact_mod_cast he
  have ht := (div_lt_iff₀ hp).mp hn
  linarith

/-- In an exact extremizer, any spanning high-girth subgraph loses at least
one twentieth of all edges. The subgraph hypothesis gives the deletion
interpretation; the inequality itself follows from the uniform gap. -/
theorem eventual_deletion_cost {α c : ℝ} (hα : α ≤ 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ G J : SimpleGraph (Fin n),
      Nat.card G.edgeSet = extremalNumber n (cycleGraph 8) → J ≤ G → SmallAcyclic J →
      (1/20 : ℝ)*Nat.card G.edgeSet ≤
        (Nat.card G.edgeSet : ℝ)-(Nat.card J.edgeSet : ℝ) := by
  filter_upwards [eventual_gap hα hc h] with n hn
  intro G J he _ hJ
  have hgap := hn J hJ
  rw [he]
  linarith

#print axioms amplify_free
#print axioms amplify_edges
#print axioms finite_comparison
#print axioms eventual_gap
#print axioms eventual_deletion_cost
end Erdos713C8HighGirthGap
