import FormalConjecturesUtil
import Submission.VertexSplitWitnesses

/-! For a bipartite pattern whose vertex deletions remain connected, a
nontrivial split cannot have roots in opposite host color classes. -/
open SimpleGraph
namespace Erdos713SplitRootParity
open Erdos713VertexMerging Erdos713VertexSplitWitnesses
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma two_flip : ∀ a b c d e f : Fin 2, a ≠ b → d ≠ e →
    (b = c ↔ e = f) → (a = c ↔ d = f) := by decide

lemma two_ne_same : ∀ a b c : Fin 2, a ≠ c → b ≠ c → a = b := by decide

lemma coloring_eq_of_reachable {G : SimpleGraph V} (χ ψ : G.Coloring (Fin 2))
    {x y : V} (hp : G.Reachable x y) : χ x = χ y ↔ ψ x = ψ y := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => simp
  | cons h p ih => exact two_flip _ _ _ _ _ _ (χ.valid h) (ψ.valid h) ih

lemma split_roots_same_color {H : SimpleGraph W} (hH : H.IsBipartite)
    (w : W) (hRest : (H.induce {w}ᶜ).Preconnected) (S : Set W)
    {G : SimpleGraph V} (χ : G.Coloring (Fin 2)) (f : (Erdos713VertexSplitWitnesses.split H w S).Copy G)
    (hLeft : ∃ x, H.Adj w x ∧ x ∈ S) (hRight : ∃ y, H.Adj w y ∧ y ∉ S) :
    χ (f (some w)) = χ (f none) := by
  classical
  obtain ⟨φ⟩ := hH
  obtain ⟨x,hx,hxS⟩ := hLeft
  obtain ⟨y,hy,hyS⟩ := hRight
  let x' : ({w}ᶜ : Set W) := ⟨x,hx.ne.symm⟩
  let y' : ({w}ᶜ : Set W) := ⟨y,hy.ne.symm⟩
  let inc : H.induce {w}ᶜ →g Erdos713VertexSplitWitnesses.split H w S :=
    ⟨fun z => some z.val,by
      intro z t hzt
      exact ⟨hzt,fun h => (z.property h).elim,fun h => (t.property h).elim⟩⟩
  let φ' : (H.induce {w}ᶜ).Coloring (Fin 2) := φ.comp (SimpleGraph.Embedding.induce {w}ᶜ).toHom
  let ψ' : (H.induce {w}ᶜ).Coloring (Fin 2) := χ.comp (f.toHom.comp inc)
  have hxy : φ x = φ y := two_ne_same _ _ _ (φ.valid hx).symm (φ.valid hy).symm
  have hxy' : ψ' x' = ψ' y' := (coloring_eq_of_reachable φ' ψ' (hRest x' y')).mp hxy
  have hxyG : χ (f (some x)) = χ (f (some y)) := hxy'
  have hL : (Erdos713VertexSplitWitnesses.split H w S).Adj (some w) (some x) :=
    ⟨hx,fun _ => hxS,fun h => (hx.ne h.symm).elim⟩
  have hR : (Erdos713VertexSplitWitnesses.split H w S).Adj none (some y) := ⟨hy,hyS⟩
  have hχL := χ.valid (f.toHom.map_adj hL)
  have hχR := χ.valid (f.toHom.map_adj hR)
  simp only [Copy.toHom_apply] at hχL hχR
  rw [← hxyG] at hχR
  exact two_ne_same _ _ _ hχL hχR

/-- Identifying opposite color classes preserves forbiddenness here.
It need not preserve bipartiteness of the host. -/
lemma free_merge_opposite {H : SimpleGraph W} (hH : H.IsBipartite)
    (hRest : ∀ w, (H.induce {w}ᶜ).Preconnected)
    {G : SimpleGraph V} (χ : G.Coloring (Fin 2)) (hf : H.Free G)
    {u v : V} (hχ : χ u ≠ χ v) (hn : ¬ G.Adj u v) : H.Free (merge G u v hn) := by
  intro hc
  obtain ⟨w,S,f,hu,hv,hL,hR⟩ := split_copy_of_merge hf hn hc
  have hh := split_roots_same_color hH w (hRest w) S χ f hL hR
  rw [hu,hv] at hh
  exact hχ hh

lemma commonNeighbors_empty_of_opposite {G : SimpleGraph V} (χ : G.Coloring (Fin 2))
    {u v : V} (hχ : χ u ≠ χ v) : IsEmpty (G.commonNeighbors u v) := by
  refine ⟨?_⟩
  rintro ⟨x,hux,hvx⟩
  exact hχ (two_ne_same _ _ _ (χ.valid hux) (χ.valid hvx))

#print axioms split_roots_same_color
#print axioms free_merge_opposite
end Erdos713SplitRootParity
