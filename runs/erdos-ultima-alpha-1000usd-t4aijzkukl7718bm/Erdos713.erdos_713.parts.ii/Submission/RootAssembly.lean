import FormalConjecturesUtil
import Submission.RootPowerGluing

/-! Enlarged finite assembly certificates using all the oriented small-core
bounds. These certificates do not cover all finite bipartite graphs. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713RootAssembly
open Erdos713Rate Erdos713Gluing
universe u

inductive Assembly : {W : Type u} → SimpleGraph W → Prop where
  | base {W : Type u} {G : SimpleGraph W} (h : Erdos713Assembly.Assembly G) : Assembly G
  | iso {W T : Type u} {G : SimpleGraph W} {H : SimpleGraph T}
      (e : G ≃g H) (h : Assembly H) : Assembly G
  | components {W : Type u} [Fintype W] (G : SimpleGraph W)
      (h : ∀ C : G.ConnectedComponent, Assembly C.toSimpleGraph) : Assembly G
  | prunes {W : Type u} [Fintype W] (G : SimpleGraph W) (S : Set W)
      (hP : Erdos713Pruning.PrunesTo G S) (h : Assembly (G.induce S)) : Assembly G
  | wedgeSmallCore {W T : Type u} [Fintype W] [Fintype T]
      (H : SimpleGraph W) (x : W) (S : Set W) (hB : H.IsBipartiteWith S Sᶜ)
      (hS : Nat.card S ≤ 3) (hd : ∀ v, 2 ≤ Nat.card (H.neighborSet v))
      (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
      (hJ : Assembly J) : Assembly (wedge H x J y)
  | wedgeEdge {T : Type u} [Fintype T] (J : SimpleGraph T) (y : T)
      (hy : ∃ z, J.Adj y z) (x : Fin 1 ⊕ Fin 1) (hJ : Assembly J) :
      Assembly (wedge (Erdos713KST.Kst 1 1) x J y)
  | wedgeExceptional {A B W T : Type u}
      [Fintype A] [Fintype B] [Nonempty A] [Fintype W] [Fintype T]
      (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 2)
      (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ 2)
      (H : SimpleGraph W) (x : W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
      (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Erdos713C6.bipGraph R)
      (J : SimpleGraph T) (y : T) (hy : ∃ z, J.Adj y z)
      (hJ : Assembly J) : Assembly (wedge H x J y)

lemma Assembly.side {W : Type u} [Fintype W] (G : SimpleGraph W) (S : Set W)
    (hB : G.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3) : Assembly G :=
  .base (Erdos713Assembly.Assembly.side G S hB hS)


lemma Assembly.rate {W : Type u} {G : SimpleGraph W} (h : Assembly G) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  induction h with
  | base h => exact h.rate
  | iso e h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,iso_rate e hr⟩
  | components G h ih => exact Erdos713ComponentRates.rate_of_components G ih
  | prunes G S hP h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,hP.rate hr⟩
  | wedgeSmallCore H x S hB hS hd J y hy hJ ih =>
    obtain ⟨r,hr⟩ := ih
    exact Erdos713RootPower.small_core_wedge_rate H x S hB hS hd J y hy hr
  | wedgeEdge J y hy x hJ ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,Erdos713RootPower.edge_wedge_rate J y hy x hr⟩
  | wedgeExceptional R E hE hR H x hNoIso hlo hhi J y hy hJ ih =>
    obtain ⟨r,hr⟩ := ih
    refine ⟨max (3/2) r,?_⟩
    simpa only [Rat.cast_max,Rat.cast_div,Rat.cast_ofNat] using
      Erdos713RootPower.exceptional_columns_wedge_rate R E hE hR H x hNoIso hlo hhi J y hy hr

lemma Assembly.rational {W : Type u} {G : SimpleGraph W} (hG : Assembly G)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := hG.rate
  exact ⟨r,(exponent_eq hr hα hc h).symm⟩

#print axioms Assembly.rate
#print axioms Assembly.rational
end Erdos713RootAssembly
