import FormalConjecturesUtil
import Submission.KstGluing

/-! Rational-rate certificates built from the completed families, components,
leaf pruning, isomorphisms, and the newly proved rooted K2t/K3t gluings.
This does not assert that every finite bipartite graph has such a certificate. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713Assembly
open Erdos713Rate Erdos713Gluing
universe u

inductive Assembly : {W : Type u} → SimpleGraph W → Prop where
  | forest {W : Type u} [Fintype W] (G : SimpleGraph W) (h : G.IsAcyclic) : Assembly G
  | side {W : Type u} [Fintype W] (G : SimpleGraph W) (S : Set W)
      (hB : G.IsBipartiteWith S Sᶜ) (hS : Nat.card S ≤ 3) : Assembly G
  | twoBase {W : Type u} (G : SimpleGraph W) {t : ℕ}
      (hlo : Erdos713C4.K22 ⊑ G) (hhi : G ⊑ Erdos713K2t.K2t t) : Assembly G
  | threeBase {W : Type u} (G : SimpleGraph W) {t : ℕ}
      (hlo : Erdos713Norm.K33 ⊑ G) (hhi : G ⊑ Erdos713K3t.K3t t) : Assembly G
  | iso {W T : Type u} {G : SimpleGraph W} {H : SimpleGraph T}
      (e : G ≃g H) (h : Assembly H) : Assembly G
  | components {W : Type u} [Fintype W] (G : SimpleGraph W)
      (h : ∀ C : G.ConnectedComponent, Assembly C.toSimpleGraph) : Assembly G
  | prunes {W : Type u} [Fintype W] (G : SimpleGraph W) (S : Set W)
      (hP : Erdos713Pruning.PrunesTo G S) (h : Assembly (G.induce S)) : Assembly G
  | wedgeTwo {W T : Type u} [Fintype T]
      (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
      (hy : ∃ z, J.Adj y z) {t : ℕ} (ht : 1 ≤ t)
      (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ Erdos713K2t.K2t t)
      (hJ : Assembly J) : Assembly (wedge H x J y)
  | wedgeThree {W T : Type u} [Fintype T]
      (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T)
      (hy : ∃ z, J.Adj y z) {t : ℕ} (ht : 1 ≤ t)
      (hlo : Erdos713Norm.K33 ⊑ H) (hhi : H ⊑ Erdos713K3t.K3t t)
      (hJ : Assembly J) : Assembly (wedge H x J y)

lemma Assembly.rate {W : Type u} {G : SimpleGraph W} (h : Assembly G) :
    ∃ r : ℚ, HasRate G (r : ℝ) := by
  classical
  induction h with
  | forest G hF => exact ⟨1,by simpa using forest_rate G hF⟩
  | side G S hB hS => exact Erdos713ThreeSide.rate_of_small_bipartition G S hB hS
  | twoBase G hlo hhi => exact ⟨3/2,by norm_num; exact k2t_rate hlo hhi⟩
  | threeBase G hlo hhi => exact ⟨5/3,by norm_num; exact k3t_rate hlo hhi⟩
  | iso e h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,iso_rate e hr⟩
  | components G h ih => exact Erdos713ComponentRates.rate_of_components G ih
  | prunes G S hP h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨r,hP.rate hr⟩
  | wedgeTwo H x J y hy ht hlo hhi hJ ih =>
    obtain ⟨r,hr⟩ := ih
    refine ⟨max (3/2) r,?_⟩
    simpa only [Rat.cast_max,Rat.cast_div,Rat.cast_ofNat] using
      Erdos713KstGluing.wedge_k2t_rate H x J y hy ht hlo hhi hr
  | wedgeThree H x J y hy ht hlo hhi hJ ih =>
    obtain ⟨r,hr⟩ := ih
    refine ⟨max (5/3) r,?_⟩
    simpa only [Rat.cast_max,Rat.cast_div,Rat.cast_ofNat] using
      Erdos713KstGluing.wedge_k3t_rate H x J y hy ht hlo hhi hr

lemma Assembly.rational {W : Type u} {G : SimpleGraph W} (hG : Assembly G)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) : α ∈ Set.range ((↑) : ℚ → ℝ) := by
  obtain ⟨r,hr⟩ := hG.rate
  exact ⟨r,(exponent_eq hr hα hc h).symm⟩

lemma of_small_components {W : Type u} [Fintype W] (G : SimpleGraph W)
    (h : Erdos713Pruning.SmallComponents G) : Assembly G := by
  classical
  apply Assembly.components G
  intro C
  obtain ⟨S,hB,hS⟩ := h C
  exact Assembly.side C.toSimpleGraph S hB hS

/-- The two K2,3 pieces are glued at roots in opposite bipartition classes.
No root-switching automorphism of K2,3 is available or used. -/
def oppositeK23 := wedge (Erdos713K2t.K2t 3) (Sum.inl 0)
  (Erdos713K2t.K2t 3) (Sum.inr 0)

lemma oppositeK23_assembly : Assembly oppositeK23 := by
  apply Assembly.wedgeTwo _ _ _ _ (Erdos713KstGluing.no_isolates (by decide) (by decide) _)
    (by decide : 1 ≤ 3) (Erdos713K2t.contains_K22 (by decide : 2 ≤ 3)) (IsContained.refl _)
  exact Assembly.twoBase _ (Erdos713K2t.contains_K22 (by decide : 2 ≤ 3)) (IsContained.refl _)

lemma oppositeK23_rate : HasRate oppositeK23 ((3 : ℝ)/2) := by
  have hbase := k2t_rate (Erdos713K2t.contains_K22 (by decide : 2 ≤ 3)) (IsContained.refl _)
  simpa [oppositeK23] using Erdos713KstGluing.wedge_k2t_rate
    (Erdos713K2t.K2t 3) (Sum.inl 0) (Erdos713K2t.K2t 3) (Sum.inr 0)
    (Erdos713KstGluing.no_isolates (by decide) (by decide) _) (by decide : 1 ≤ 3)
    (Erdos713K2t.contains_K22 (by decide : 2 ≤ 3)) (IsContained.refl _) hbase

#print axioms Assembly.rate
#print axioms Assembly.rational
#print axioms oppositeK23_rate
end Erdos713Assembly
