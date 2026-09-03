import Submission.EdgeHullParity

/-! Extremal reduction using only adjacent compression of minimal graphs.
The compression hypothesis is explicit and remains unproved. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.EdgeHull
open Critical Compression
set_option maxHeartbeats 200000
variable {V : Type*} [Fintype V]

lemma exists_global_extremizer (potential : SimpleGraph V → ℕ) :
    ∃ G : SimpleGraph V, Minimal G ∧ number G = value (⊤ : SimpleGraph V) ∧
      (∀ H : SimpleGraph V, number H = number G → G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (∀ H : SimpleGraph V, number H = number G → H.edgeFinset.card = G.edgeFinset.card →
        potential H ≤ potential G) := by
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite _
  let k := value (⊤ : SimpleGraph V)
  let S : Finset (SimpleGraph V) := Finset.univ.filter (fun G => number G = k)
  have hs : S.Nonempty := by
    obtain ⟨G,_,hG⟩ := exists_maximizer (⊤ : SimpleGraph V)
    exact ⟨G, by simp [S,k,hG]⟩
  obtain ⟨M,hM,hmin⟩ := Finset.exists_min_image S (fun G => G.edgeFinset.card) hs
  have hMk : number M = k := (Finset.mem_filter.mp hM).2
  let T : Finset (SimpleGraph V) := S.filter (fun G => G.edgeFinset.card = M.edgeFinset.card)
  have ht : T.Nonempty := ⟨M,by simp [T,hM]⟩
  obtain ⟨G,hG,hmax⟩ := Finset.exists_max_image T potential ht
  have hGM : G.edgeFinset.card = M.edgeFinset.card := (Finset.mem_filter.mp hG).2
  have hGk : number G = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hG).1).2
  have hleast : ∀ H : SimpleGraph V, number H = number G → G.edgeFinset.card ≤ H.edgeFinset.card := by
    intro H hH
    rw [hGM]
    exact hmin H (by simp [S,hH,hGk])
  refine ⟨G,?_,hGk,hleast,?_⟩
  · intro R hRG hne
    have hRk : number R ≤ k := le_value (le_top : R ≤ (⊤ : SimpleGraph V))
    have hlt := edge_card_lt_of_ne hRG hne
    have hn : number R ≠ number G := fun heq => (not_le_of_gt hlt) (hleast R heq)
    omega
  · intro H hH hHG
    exact hmax H (by simp [T,S,hH,hGk,hHG,hGM])

/-- A hull inequality at one graph forces an actual minimum-number inequality
at a global edge-minimal maximizer, whenever the operation preserves edge count. -/
lemma number_eq_of_hull_at_global_minimizer
    {G T : SimpleGraph V}
    (hG : number G = value (⊤ : SimpleGraph V))
    (hmin : ∀ H : SimpleGraph V, number H = number G → G.edgeFinset.card ≤ H.edgeFinset.card)
    (hcard : T.edgeFinset.card = G.edgeFinset.card)
    (hhull : number G ≤ value T) : number T = number G := by
  obtain ⟨R,hRT,hR⟩ := exists_maximizer T
  have hrle : number R ≤ number G := by
    rw [hG]
    exact le_value (le_top : R ≤ (⊤ : SimpleGraph V))
  have hrnum : number R = number G := by omega
  have hrge := hmin R hrnum
  have heq : R = T := by
    by_contra hne
    have hlt := edge_card_lt_of_ne hRT hne
    omega
  simpa only [heq] using hrnum

/-- A sufficient extremal reduction. Only adjacent transfers of minimal graphs
are assumed, rather than all transfers with an added joining edge. -/
lemma bound_of_adjacent_minimal_compression
    (potential : SimpleGraph V → ℕ) (P : SimpleGraph V → Prop) (k : ℕ)
    (hcard : ∀ G : SimpleGraph V, ∀ u v : V,
      (transfer G u v).edgeFinset.card = G.edgeFinset.card)
    (hcompression : ∀ G : SimpleGraph V, Minimal G → ∀ u v : V, G.Adj u v →
      number G ≤ value (transfer G u v))
    (himprove : ∀ G : SimpleGraph V, ¬ P G →
      ∃ u v : V, G.Adj u v ∧ potential G < potential (transfer G u v))
    (hterminal : ∀ G : SimpleGraph V, P G → number G ≤ k)
    (H : SimpleGraph V) : number H ≤ k := by
  obtain ⟨G,hminimal,hG,hmin,hmax⟩ := exists_global_extremizer potential
  have hP : P G := by
    by_contra hn
    obtain ⟨u,v,huv,hpot⟩ := himprove G hn
    have hc : Nat.card (transfer G u v).edgeSet = Nat.card G.edgeSet := by
      simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard G u v
    have hnum := number_eq_of_hull_at_global_minimizer (T := transfer G u v) hG hmin
      (by simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc)
      (hcompression G hminimal u v huv)
    exact (not_le_of_gt hpot) (hmax _ hnum
      (by simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hc))
  have hh : number H ≤ number G := by
    rw [hG]
    exact le_value (le_top : H ≤ (⊤ : SimpleGraph V))
  exact hh.trans (hterminal G hP)

end Erdos184Work.EdgeHull

#print axioms Erdos184Work.EdgeHull.exists_global_extremizer
#print axioms Erdos184Work.EdgeHull.number_eq_of_hull_at_global_minimizer
#print axioms Erdos184Work.EdgeHull.bound_of_adjacent_minimal_compression
