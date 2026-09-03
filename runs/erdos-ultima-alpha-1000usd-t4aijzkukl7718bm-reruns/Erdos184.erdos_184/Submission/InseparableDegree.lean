import Submission.InseparablePacking

/-! Degree restrictions on the target-inseparability certificate. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.InseparableCycle
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 800000

lemma target_degree_lower (T : Set V)
    (hconn : ∀ S : Set V, S.ncard < T.ncard →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        (G.induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩)
    {a : V} (ha : a ∈ T) : T.ncard ≤ G.degree a + 1 := by
  by_contra! hn
  have hcard : (G.neighborSet a).ncard = G.degree a := by
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have hnot : ¬T ⊆ insert a (G.neighborSet a) := by
    intro hs
    have hh := (Set.ncard_le_ncard hs).trans (Set.ncard_insert_le a (G.neighborSet a))
    omega
  obtain ⟨b,hb,hbn⟩ := Set.not_subset.mp hnot
  have hba : b ≠ a := fun h => hbn (Or.inl h)
  have hbN : b ∉ G.neighborSet a := fun h => hbn (Or.inr h)
  have haN : a ∉ G.neighborSet a := G.loopless a
  obtain ⟨p⟩ := hconn (G.neighborSet a) (by omega) a ha b hb haN hbN
  obtain ⟨c,hac,_,_⟩ := p.exists_eq_cons_of_ne (fun h => hba (congrArg Subtype.val h).symm)
  exact c.property hac

/-- If the targets initially have degree exactly 2r, target inseparability
cannot certify all r common-cycle removals unless there are at most three
targets. Just before the last removal their residual degree is two. -/
lemma full_regular_packing_certificate_small (he : ∀ x, Even (G.degree x))
    (T : Set V) (hT : 2 ≤ T.ncard) (r : ℕ) (hr : 0 < r)
    (hdegree : ∀ a ∈ T, G.degree a = 2*r)
    (hconn : ∀ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) →
      (∀ H ∈ P, T ⊆ H.verts) → P.card < r →
      ∀ S : Set V, S.ncard < T.ncard →
      ∀ a ∈ T, ∀ b ∈ T, ∀ haS : a ∉ S, ∀ hbS : b ∉ S,
        ((G \ unionPieces G P).induce Sᶜ).Reachable ⟨a,haS⟩ ⟨b,hbS⟩) :
    T.ncard ≤ 3 := by
  obtain ⟨P,hc,hd,hv,hcard⟩ := packing_through_set he T hT (r-1) (by
    intro P hc hd hv hn
    exact hconn P hc hd hv (hn.trans_le (Nat.sub_le r 1)))
  obtain ⟨a,ha⟩ := (Set.ncard_pos (Set.toFinite T)).mp (by omega : 0 < T.ncard)
  have hpiece : ∀ H ∈ P, H.degree a = 2 := by
    intro H hH
    have hh := (hc H hH).2 ⟨a,hv H hH ha⟩
    rw [Subgraph.coe_degree] at hh
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
  have hu : (unionPieces G P).degree a = 2*P.card := by
    rw [unionPieces_degree G P hd a]
    rw [Finset.sum_congr rfl hpiece]
    simp [Nat.mul_comm]
  have hres := degree_sdiff_of_le (unionPieces_le G P) a
  have hdeg := hdegree a ha
  have hh := target_degree_lower T (hconn P hc hd hv (by omega)) ha
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hu hres hdeg hh
  omega

end Erdos184.InseparableCycle
