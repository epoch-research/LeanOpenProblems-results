import Submission.MinimalParityProfile
import Submission.SixVertexCertificates

/-! There is no connected counterexample on at most seven vertices. The
unbounded conjecture is not asserted here. -/
namespace Erdos583MinimumOrderEightDevelopment
open SimpleGraph Erdos583Work Erdos583Work.ComponentDeficit
open Erdos583UnifiedMinimalDefectDevelopment Erdos583MinimalParityProfileDevelopment
open Erdos583FourEvenDegreeFourDevelopment Erdos583SixVertexCertificatesDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma four_even_failure_order_ge_eight {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) (he : evenCount G=4) :
    8 ≤ Fintype.card V := by
  classical
  obtain ⟨r,hr⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0 < {v | Even (Nat.card (G.neighborSet v))}.ncard by
    change 0 < evenCount G
    omega)
  have hd := four_even_failure_even_degree_ge_six he hf r hr
  have hn := G.degree_lt_card_verts r
  simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] at hd
  have hp : Even (Fintype.card V) := Nat.not_odd_iff_even.mp (by
    intro ho
    have hh := (odd_order_iff_evenCount_odd G).mp ho
    rw [he,Nat.odd_iff] at hh
    omega)
  rw [Nat.even_iff] at hp
  omega

lemma failure_order_ge_six {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) : 6 ≤ Fintype.card V := by
  rcases failure_four_even_or_six G hf with h4|h6
  · have hh := four_even_failure_order_ge_eight G hf h4
    omega
  · have hh := Set.ncard_le_card {v | Even (Nat.card (G.neighborSet v))}
    change evenCount G ≤ Nat.card V at hh
    rw [Nat.card_eq_fintype_card] at hh
    omega

lemma minimal_order_ne_six (F : MinimalFailure) : F.order ≠ 6 := by
  classical
  intro hn
  cases F with
  | mk n G hG hf hs hcrit =>
    dsimp at hn
    subst n
    have he : 6 ≤ evenCount G := by
      rcases failure_four_even_or_six G hf with h4|h6
      · have hh := four_even_failure_order_ge_eight G hf h4
        norm_num at hh
      · exact h6
    have hset : {v | Even (Nat.card (G.neighborSet v))}=Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      simpa only [Set.ncard_univ,Nat.card_fin] using he
    have hEven (v : Fin 6) : Even (Nat.card (G.neighborSet v)) := by
      have hh : v ∈ ({v | Even (Nat.card (G.neighborSet v))} : Set (Fin 6)) := by
        rw [hset]
        trivial
      exact hh
    have hdegree (v : Fin 6) : Nat.card (G.neighborSet v)=2 ∨ Nat.card (G.neighborSet v)=4 := by
      have hp := hG.preconnected.degree_pos_of_nontrivial v
      have hlt := G.degree_lt_card_verts v
      have hev := hEven v
      simp only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,Nat.even_iff,
        Fintype.card_fin] at hp hlt hev ⊢
      omega
    have htriangle (v a b : Fin 6) (hv : Nat.card (G.neighborSet v)=2)
        (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) : G.Adj a b := by
      obtain ⟨_,x,y,hxy,hN,hxyG⟩ := DegreeTwoReduction.degree_two_triangle hs hG hf hv
      have ha' : a=x ∨ a=y := by
        have haa : a ∈ G.neighborSet v := ha
        rwa [hN] at haa
      have hb' : b=x ∨ b=y := by
        have hbb : b ∈ G.neighborSet v := hb
        rwa [hN] at hbb
      rcases ha' with rfl|rfl <;> rcases hb' with rfl|rfl
      · exact (hab rfl).elim
      · exact hxyG
      · exact hxyG.symm
      · exact (hab rfl).elim
    have hnonadj (v w : Fin 6) (hvw : G.Adj v w)
        (hh : Nat.card (G.neighborSet v)=2 ∧ Nat.card (G.neighborSet w)=2) : False :=
      LowDegreeAdjacency.degree_two_not_adjacent_degree_two hs hG hf hvw hh.1 hh.2
    obtain ⟨D,hD,hDc⟩ := residual_partition G hdegree htriangle hnonadj
    apply hf
    refine ⟨D,hD,?_⟩
    simpa only [Fintype.card_fin,BridgeGlue.ceil_half] using hDc

lemma minimal_order_ge_eight (F : MinimalFailure) : 8 ≤ F.order := by
  have hn := failure_order_ge_six F.graph F.failure
  simp only [Fintype.card_fin] at hn
  have hn6 := minimal_order_ne_six F
  by_contra hlt
  have hn7 : F.order=7 := by omega
  have ho : Odd F.order := by rw [hn7]; decide
  have hh := odd_minimal_order_ge_nine F ho
  omega

lemma connected_at_most_seven {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (hn : Fintype.card V ≤ 7) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  by_contra hf
  obtain ⟨n,hn',H,hH,hfH,hsmall⟩ := VertexCritical.failure_has_minimal_order G hG hf
  obtain ⟨K,hK,hfK,hcrit⟩ := GlobalCritical.exists_minimal_edges H hH hfH
  let F : MinimalFailure := ⟨n,K,hK,hfK,hsmall,hcrit⟩
  have hh := minimal_order_ge_eight F
  change 8 ≤ n at hh
  omega

end Erdos583MinimumOrderEightDevelopment
