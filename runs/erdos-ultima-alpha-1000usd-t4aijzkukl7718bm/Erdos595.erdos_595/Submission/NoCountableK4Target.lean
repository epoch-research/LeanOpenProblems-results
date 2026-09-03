import Submission.GenericTraceRealization
import Submission.FiniteFolkman
import Submission.AvoidingMarginalIsolation

/-!
The first mutual ultrafilter extension of the countable generic K4-free graph
has no homomorphism to a countable K4-free graph. This is compatible with its
countable proper coloring, whose complete target is NOT K4-free. It is not a
solution to Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
open Erdos595Work Erdos595BadEdge Erdos595ArcAdjoint
namespace Erdos595NoCountableK4Target

variable {V A W : Type*}

lemma finiteCover_coloring {G : SimpleGraph V} (h : FiniteCover G) :
    ∃ n : ℕ, Erdos595FinitePalette.HasColoring G (Option (Fin n)) := by
  classical
  obtain ⟨n,H,hH,hcov⟩ := h
  let c : Sym2 V → Option (Fin n) := fun e =>
    if h : ∃ i, e ∈ (H i).edgeSet then some h.choose else none
  have hc {a b : V} (hab : G.Adj a b) :
      ∃ i, c s(a,b) = some i ∧ (H i).Adj a b := by
    have he : ∃ i, s(a,b) ∈ (H i).edgeSet := hcov a b hab
    exact ⟨he.choose,by simp only [c,dif_pos he],he.choose_spec⟩
  refine ⟨n,c,?_⟩
  intro a b d hab had hbd hm
  obtain ⟨i,hi,hiab⟩ := hc hab
  obtain ⟨j,hj,hjad⟩ := hc had
  obtain ⟨k,hk,hkbd⟩ := hc hbd
  have hij : i = j := Option.some.inj (hi.symm.trans (hm.1.trans hj))
  have hik : i = k := Option.some.inj (hi.symm.trans (hm.2.trans hk))
  subst j; subst k
  exact hH i _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hiab,hjad,hkbd⟩)

lemma generic_no_finiteCover : ¬FiniteCover Erdos595CountableExtension.G := by
  intro h
  obtain ⟨n,hn⟩ := finiteCover_coloring h
  exact Erdos595FiniteFolkman.generic_no_finite_coloring (Option (Fin n)) hn

/-- A marginal avoiding all triangle-free vertex sets supplies an independent
sequence escaping any prescribed sequence of triangle-free vertex sets. -/
lemma independent_escape (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (D : Ultrafilter (Arc G)) (hD : Avoids G D)
    (S : ℕ → Set V) (hS : ∀ n, (G.induce (S n)).CliqueFree 3) :
    ∃ v : ℕ → V, (∀ n, v n ∉ S n) ∧ ∀ i j, ¬G.Adj (v i) (v j) := by
  classical
  let p := D.map (fun e => e.val.1)
  have hchoice (n : ℕ) (v : Fin n → V) :
      ∃ w : V, w ∉ S n ∧ ∀ i, ¬G.Adj (v i) w := by
    have hs : (S n)ᶜ ∈ p := Ultrafilter.compl_mem_iff_notMem.mpr
      (Erdos595AvoidingMarginalIsolation.triangleFree_set_not_mem G D hD (S n) (hS n))
    have hn : (⋂ i, (G.neighborSet (v i))ᶜ) ∈ p := by
      apply Filter.iInter_mem.mpr
      intro i
      exact Ultrafilter.compl_mem_iff_notMem.mpr (neighborhood_not_mem G hG D hD (v i))
    obtain ⟨w,hw,hv⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hs hn)
    exact ⟨w,hw,fun i => Set.mem_iInter.mp hv i⟩
  let v : ℕ → V := Nat.strongRec fun n prev =>
    (hchoice n (fun i => prev i.val i.isLt)).choose
  have hv (n : ℕ) : v n ∉ S n ∧ ∀ i : Fin n, ¬G.Adj (v i) (v n) := by
    rw [show v n = (hchoice n (fun i : Fin n => v i)).choose by
      dsimp only [v]; rw [Nat.strongRec_eq]]
    exact (hchoice n (fun i : Fin n => v i)).choose_spec
  refine ⟨v,fun n => (hv n).1,?_⟩
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact (hv j).2 ⟨i,h⟩ hij
  · exact hij.ne (congrArg v h)
  · exact (hv i).2 ⟨j,h⟩ hij.symm

/-- An abstract obstruction: realizing common neighbors of independent sets
prevents compression to a countable K4-free target whenever the old graph has
no finite triangle-free edge cover. -/
theorem no_countable_target [Countable W]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) (hn : ¬FiniteCover G)
    (H : SimpleGraph A) (e : G →g H)
    (hext : ∀ S : Set V, (∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b) →
      ∃ x : A, ∀ a ∈ S, H.Adj x (e a))
    (K : SimpleGraph W) (hK : K.CliqueFree 4) : ¬Nonempty (H →g K) := by
  classical
  rintro ⟨f⟩
  obtain ⟨D,hD⟩ := exists_avoiding G hn
  haveI : Nonempty V := by
    obtain ⟨a,_⟩ := Ultrafilter.nonempty_of_mem
      (show Set.univ ∈ D.map (fun e => e.val.1) from Filter.univ_mem)
    exact ⟨a⟩
  haveI : Nonempty W := ⟨f (e (Classical.arbitrary V))⟩
  obtain ⟨d,hd⟩ := exists_surjective_nat W
  let S : ℕ → Set V := fun n => {a | K.Adj (d n) (f (e a))}
  have hS (n : ℕ) : (G.induce (S n)).CliqueFree 3 := by
    intro t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact no_adj_common_neighbors hK a.property b.property
      (f.map_adj (e.map_adj hab)) c.property (f.map_adj (e.map_adj hac))
      (f.map_adj (e.map_adj hbc))
  obtain ⟨v,hv,hind⟩ := independent_escape G hG D hD S hS
  obtain ⟨x,hx⟩ := hext (Set.range v) (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact hind i j)
  obtain ⟨n,hn⟩ := hd (f x)
  apply hv n
  change K.Adj (d n) (f (e (v n)))
  rw [hn]
  exact f.map_adj (hx (v n) ⟨n,rfl⟩)

open Erdos595CountableExtension Erdos595GenericTrace

/-- The first mutual extension is countably properly colorable, but has no
homomorphism to ANY countable K4-free graph. -/
theorem generic_first_no_countable_target [Countable W]
    (K : SimpleGraph W) (hK : K.CliqueFree 4) : ¬Nonempty (U →g K) := by
  let e : G →g U := ⟨pure,fun h => (pure_adj_pure _ _).mpr h⟩
  apply no_countable_target G G_cliqueFree generic_no_finiteCover U e _ K hK
  intro S hS
  have ht : (G.induce S).CliqueFree 3 := by
    intro t ht
    obtain ⟨a,b,_,hab,_,_,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hS a a.property b b.property hab
  exact ⟨point S ht,fun a ha => (point_adj_pure S ht a).mpr ha⟩

#print axioms independent_escape
#print axioms no_countable_target
#print axioms generic_first_no_countable_target
end Erdos595NoCountableK4Target
