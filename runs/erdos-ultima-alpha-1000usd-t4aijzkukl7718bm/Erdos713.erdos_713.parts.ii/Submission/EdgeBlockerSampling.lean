import FormalConjecturesUtil
import Submission.CompactRootBlocksAudit

/-! Sampling with bounded blockers attached to edges, rather than vertices.
Every forbidden copy must contain an edge whose blocker meets that copy. -/
open SimpleGraph Finset
namespace Erdos713EdgeBlockers
open Erdos713Blocking
universe u v

variable {W : Type u} {V : Type v} {H : SimpleGraph W} {G : SimpleGraph V}

def UsesEdge (f : H.Copy G) (e : Sym2 V) : Prop :=
  ∃ a b, H.Adj a b ∧ s(f a,f b) = e

def Blocked (H : SimpleGraph W) (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ B : Sym2 V → Finset V,
    (∀ e ∈ G.edgeSet, (B e).card ≤ k) ∧
    (∀ e ∈ G.edgeSet, ∀ v ∈ e, v ∉ B e) ∧
    (∀ f : H.Copy G, ∃ e, UsesEdge f e ∧ ∃ a, f a ∈ B e)

def keep (G : SimpleGraph V) (B : Sym2 V → Finset V) (σ : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ selected (fun _ => B s(u,v)) σ u ∧ selected (fun _ => B s(u,v)) σ v
  symm u v h := by
    refine ⟨h.1.symm,?_⟩
    have he : s(v,u) = s(u,v) := Sym2.eq_swap
    rw [he]
    exact h.2.symm
  loopless u h := G.loopless u h.1

lemma keep_le (G : SimpleGraph V) (B : Sym2 V → Finset V) (σ : V → Bool) : keep G B σ ≤ G :=
  fun _ _ h => h.1

lemma keep_free (H : SimpleGraph W) (G : SimpleGraph V) (B : Sym2 V → Finset V)
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hHits : ∀ f : H.Copy G, ∃ e, UsesEdge f e ∧ ∃ a, f a ∈ B e) (σ : V → Bool) :
    H.Free (keep G B σ) := by
  rintro ⟨f⟩
  let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
  obtain ⟨e,⟨u,v,huv,he⟩,a,ha⟩ := hHits g
  change s(f u,f v) = e at he
  change f a ∈ B e at ha
  obtain ⟨b,hab⟩ := hNoIso a
  have htrue : σ (f a) = true := (f.toHom.map_adj hab).2.1.1
  have hfalse : σ (f a) = false := (f.toHom.map_adj huv).2.1.2 (f a) (he.symm ▸ ha)
  exact Bool.noConfusion (htrue.symm.trans hfalse)

lemma edges_le_of_keep_bound [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Sym2 V → Finset V) (k M : ℕ)
    (hsmall : ∀ e ∈ G.edgeSet, (B e).card ≤ k)
    (hdis : ∀ e ∈ G.edgeSet, ∀ v ∈ e, v ∉ B e)
    (hM : ∀ σ : V → Bool, Nat.card (keep G B σ).edgeSet ≤ M) :
    G.edgeFinset.card ≤ 2^(2*k+2)*M := by
  classical
  let C := 2^(2*k+2)
  let A := Fintype.card (V → Bool)
  let E := G.edgeFinset
  let rel : (V → Bool) → Sym2 V → Prop := fun σ e => e ∈ (keep G B σ).edgeFinset
  have hBelow : ∀ e ∈ E, A ≤ C*((univ : Finset (V → Bool)).bipartiteBelow rel e).card := by
    intro e he
    have heG : e ∈ G.edgeSet := by simpa only [E,mem_edgeFinset] using he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := heG
      have hu : u ∉ B s(u,v) := hdis _ heG u (by simp)
      have hv : v ∉ B s(u,v) := hdis _ heG v (by simp)
      have hrel (σ : V → Bool) : rel σ s(u,v) ↔
          selected (fun _ => B s(u,v)) σ u ∧ selected (fun _ => B s(u,v)) σ v := by
        change s(u,v) ∈ (keep G B σ).edgeFinset ↔ _
        simp only [mem_edgeFinset,mem_edgeSet,keep,hadj,true_and]
      have hh := pair_survival (fun _ => B s(u,v)) k (fun _ => hsmall _ heG) hu hv hv hu
      simpa only [A,C,Nat.card_eq_fintype_card,Fintype.card_subtype,bipartiteBelow,hrel] using hh
  have hAbove (σ : V → Bool) : (E.bipartiteAbove rel σ).card ≤ M := by
    apply (card_le_card (show E.bipartiteAbove rel σ ⊆ (keep G B σ).edgeFinset from ?_)).trans
      (by simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hM σ)
    intro e he
    exact (mem_filter.mp he).2
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (V → Bool))) (t := E)
  have hCount : E.card*A ≤ C*(A*M) := by
    calc
      E.card*A = ∑ _e ∈ E, A := by simp
      _ ≤ ∑ e ∈ E, C*((univ : Finset (V → Bool)).bipartiteBelow rel e).card := sum_le_sum hBelow
      _ = C*∑ σ : V → Bool, (E.bipartiteAbove rel σ).card := by rw [← mul_sum,← hsum]
      _ ≤ C*∑ _σ : V → Bool, M := Nat.mul_le_mul_left C (sum_le_sum fun σ _ => hAbove σ)
      _ = C*(A*M) := by simp [A]
  have hA : 0 < A := Fintype.card_pos
  exact Nat.le_of_mul_le_mul_left (show A*E.card ≤ A*(C*M) by nlinarith only [hCount]) hA

lemma Blocked.edge_bound [Fintype V] (h : Blocked H G k) (hNoIso : ∀ a, ∃ b, H.Adj a b) :
    Nat.card G.edgeSet ≤ 2^(2*k+2)*extremalNumber (Fintype.card V) H := by
  classical
  obtain ⟨B,hsmall,hdis,hHits⟩ := h
  have hh := edges_le_of_keep_bound G B k (extremalNumber (Fintype.card V) H) hsmall hdis (by
    intro σ
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using
      card_edgeFinset_le_extremalNumber (keep_free H G B hNoIso hHits σ))
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using hh

#print axioms keep_free
#print axioms edges_le_of_keep_bound
#print axioms Blocked.edge_bound
end Erdos713EdgeBlockers
