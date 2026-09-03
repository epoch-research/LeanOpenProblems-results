import FormalConjecturesUtil
import Submission.EdgeBlockerSampling

/-! A graph above the edge-blocker bound has a nonempty subgraph in which
copies through every edge avoid any prescribed bounded vertex set. -/
open SimpleGraph Finset
namespace Erdos713EdgeBlockers
universe u v
variable {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V} {k : ℕ}

def HasBlocker (H : SimpleGraph W) (G : SimpleGraph V) (e : Sym2 V) (k : ℕ) : Prop :=
  ∃ B : Finset V, B.card ≤ k ∧ (∀ v ∈ e, v ∉ B) ∧
    ∀ f : H.Copy G, UsesEdge f e → ∃ a, f a ∈ B

lemma blocked_bot (H : SimpleGraph W) (hEdge : ∃ x y, H.Adj x y) (k : ℕ) :
    Blocked H (⊥ : SimpleGraph V) k := by
  refine ⟨fun _ => ∅,by simp,by simp,?_⟩
  intro f
  obtain ⟨x,y,hxy⟩ := hEdge
  exact (f.toHom.map_adj hxy).elim

lemma Blocked.of_delete {e : Sym2 V} (hLocal : HasBlocker H G e k)
    (hRest : Blocked H (G.deleteEdges {e}) k) : Blocked H G k := by
  classical
  obtain ⟨B,hcard,havoid,hHits⟩ := hLocal
  obtain ⟨R,hRcard,hRavoid,hRhits⟩ := hRest
  let Q : Sym2 V → Finset V := fun d => if d = e then B else R d
  refine ⟨Q,?_,?_,?_⟩
  · intro d hd
    by_cases he : d = e
    · simpa [Q,he] using hcard
    · have hd' : d ∈ (G.deleteEdges {e}).edgeSet := by simp [edgeSet_deleteEdges,hd,he]
      simpa [Q,he] using hRcard d hd'
  · intro d hd v hv
    by_cases he : d = e
    · subst d
      simpa [Q] using havoid v hv
    · have hd' : d ∈ (G.deleteEdges {e}).edgeSet := by simp [edgeSet_deleteEdges,hd,he]
      simpa [Q,he] using hRavoid d hd' v hv
  · intro f
    by_cases hf : UsesEdge f e
    · obtain ⟨a,ha⟩ := hHits f hf
      exact ⟨e,hf,a,by simpa [Q] using ha⟩
    · let f' : H.Copy (G.deleteEdges {e}) := ⟨⟨f,by
        intro a b hab
        refine deleteEdges_adj.mpr ⟨f.toHom.map_adj hab,?_⟩
        intro he
        exact hf ⟨a,b,hab,he⟩⟩,f.injective⟩
      obtain ⟨d,hd,a,ha⟩ := hRhits f'
      have hd' : UsesEdge f d := hd
      have hde : d ≠ e := fun he => hf (he ▸ hd')
      exact ⟨d,hd',a,by simpa only [Q,if_neg hde] using ha⟩

lemma exists_unblocked_core [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hEdge : ∃ x y, H.Adj x y) (hG : ¬ Blocked H G k) :
    ∃ K : SimpleGraph V, K ≤ G ∧ K ≠ ⊥ ∧ ∀ e ∈ K.edgeSet, ¬ HasBlocker H K e k := by
  classical
  let P : Finset (SimpleGraph V) := univ.filter (fun K => K ≤ G ∧ ¬ Blocked H K k)
  have hGP : G ∈ P := by simp [P,hG]
  obtain ⟨K,hK,hmin⟩ := P.exists_min_image (fun K => Nat.card K.edgeSet) ⟨G,hGP⟩
  obtain ⟨hKG,hn⟩ := (mem_filter.mp hK).2
  refine ⟨K,hKG,?_,?_⟩
  · intro he; exact hn (he ▸ blocked_bot H hEdge k)
  · intro e he hBlock
    let L := K.deleteEdges {e}
    have hLn : ¬ Blocked H L k := fun hh => hn (hh.of_delete hBlock)
    have hLP : L ∈ P := by
      simp only [P,mem_filter,mem_univ,true_and]
      exact ⟨(K.deleteEdges_le {e}).trans hKG,hLn⟩
    have hle := hmin L hLP
    have heF : e ∈ K.edgeFinset := by simpa only [mem_edgeFinset] using he
    have heL : e ∉ L.edgeFinset := by simp [L,mem_edgeFinset,edgeSet_deleteEdges]
    have hs : L.edgeFinset ⊂ K.edgeFinset := Finset.ssubset_iff_subset_ne.mpr
      ⟨edgeFinset_mono (K.deleteEdges_le {e}),fun hh => heL (hh.symm ▸ heF)⟩
    have hc := card_lt_card hs
    simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hc
    omega

/-- Copies through every edge can avoid any bounded set not containing its
endpoints. Avoidance applies to the entire copy, not only its internal vertices. -/
def Extensible (H : SimpleGraph W) (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ B : Finset V, B.card ≤ k → (∀ v ∈ e, v ∉ B) →
    ∃ f : H.Copy G, UsesEdge f e ∧ ∀ a, f a ∉ B

lemma extensible_of_unblocked (h : ∀ e ∈ G.edgeSet, ¬ HasBlocker H G e k) : Extensible H G k := by
  classical
  intro e he B hc havoid
  by_contra hn
  apply h e he
  refine ⟨B,hc,havoid,?_⟩
  intro f hf
  by_contra hh
  push_neg at hh
  exact hn ⟨f,hf,hh⟩

lemma exists_extensible_core [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V)
    (hNoIso : ∀ a, ∃ b, H.Adj a b) (hEdge : ∃ x y, H.Adj x y)
    (hDense : 2^(2*k+2)*extremalNumber (Fintype.card V) H < Nat.card G.edgeSet) :
    ∃ K : SimpleGraph V, K ≤ G ∧ K ≠ ⊥ ∧ Extensible H K k := by
  have hn : ¬ Blocked H G k := fun hh => (not_lt_of_ge (hh.edge_bound hNoIso)) hDense
  obtain ⟨K,hK,hne,hExt⟩ := exists_unblocked_core H G hEdge hn
  exact ⟨K,hK,hne,extensible_of_unblocked hExt⟩

#print axioms Blocked.of_delete
#print axioms exists_unblocked_core
#print axioms exists_extensible_core
end Erdos713EdgeBlockers
