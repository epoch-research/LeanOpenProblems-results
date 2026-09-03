import FormalConjecturesUtil
import Submission.RootedSymmetrization

/-! Rooted upper bounds are closed under one-vertex gluing. This is distinct
from claiming that rooted and ordinary thresholds of every block coincide. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713RootPower
open Erdos713Rate Erdos713Gluing Erdos713Blocking Erdos713SwitchGluing

lemma rooted_copy_of_packing {W T V : Type*} [Fintype T]
    {H : SimpleGraph W} {J : SimpleGraph T} {G : SimpleGraph V} {x : W} {y : T} {z : V}
    (p : Erdos713Fan.Packing H G x z (Fintype.card T+1)) (g : J.Copy G) (hg : g y = z) :
    ∃ f : (Erdos713Gluing.wedge H x J y).Copy G, f (Sum.inl x) = z := by
  classical
  obtain ⟨i,hi⟩ := exists_disjoint_petal p g
  have hdis : ∀ a b, b ≠ y → p.copies i a ≠ g b := by
    intro a b hb
    by_cases ha : a = x
    · subst a
      intro he
      exact hb (g.injective (hg.trans ((p.root i).symm.trans he))).symm
    · exact hi a ha b
  exact ⟨commonRootCopy (p.copies i) g ((p.root i).trans hg.symm) hdis,p.root i⟩

lemma rooted_blockers {W T V : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (J : SimpleGraph T) (y : T) (G : SimpleGraph V)
    (S : Set V) (hroot : ∀ f : (Erdos713Gluing.wedge H x J y).Copy G, f (Sum.inl x) ∉ S) :
    ∀ v, ∃ B : Finset V, v ∉ B ∧ B.card ≤ (Fintype.card T+1)*Fintype.card W ∧
      (v ∈ S → (∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B) ∨
        (∀ g : J.Copy G, g y = v → False)) := by
  classical
  intro v
  by_cases hvS : v ∈ S
  · rcases Erdos713Fan.packing_or_blocker H G x v (Fintype.card T+1) with hp | ⟨B,hv,hc,hB⟩
    · obtain ⟨p⟩ := hp
      refine ⟨∅,by simp,by simp,fun _ => Or.inr ?_⟩
      intro g hg
      obtain ⟨f,hf⟩ := rooted_copy_of_packing p g hg
      exact hroot f (hf.symm ▸ hvS)
    · exact ⟨B,hv,hc,fun _ => Or.inl hB⟩
  · exact ⟨∅,by simp,by simp,fun hv => (hvS hv).elim⟩

lemma edge_split_shore {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S A : Set V) (hB : G.IsBipartiteWith S Sᶜ) (hAS : A ⊆ S) :
    Nat.card G.edgeSet ≤ Nat.card (cross G A).edgeSet + Nat.card (cross G (S \ A)).edgeSet := by
  classical
  simp only [← Fintype.card_eq_nat_card,← edgeFinset_card]
  apply (Finset.card_le_card (show G.edgeFinset ⊆
    (cross G A).edgeFinset ∪ (cross G (S \ A)).edgeFinset from ?_)).trans (Finset.card_union_le _ _)
  intro e he
  induction e using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := by simpa using he
    rcases hB.2 huv with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · change v ∉ S at hv
      have hvA : v ∉ A := fun hvA => hv (hAS hvA)
      by_cases huA : u ∈ A
      · simp [cross,huv,huA,hvA]
      · simp [cross,huv,hu,huA,hv]
    · change u ∉ S at hu
      have huA : u ∉ A := fun huA => hu (hAS huA)
      by_cases hvA : v ∈ A
      · simp [cross,huv,huA,hvA]
      · simp [cross,huv,hv,hvA,hu]

lemma rooted_wedge_edge_bound {W T : Type*} [Fintype W] [Fintype T]
    (H : SimpleGraph W) (x : W) (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (J : SimpleGraph T) (y : T) {r C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : ∀ n (G : SimpleGraph (Fin n)) (S : Set (Fin n)), G.IsBipartiteWith S Sᶜ →
      (∀ f : H.Copy G, f x ∉ S) → (Nat.card G.edgeSet : ℝ) ≤ C*(n : ℝ)^r)
    (hJ : ∀ n (G : SimpleGraph (Fin n)) (S : Set (Fin n)), G.IsBipartiteWith S Sᶜ →
      (∀ f : J.Copy G, f y ∉ S) → (Nat.card G.edgeSet : ℝ) ≤ D*(n : ℝ)^r)
    (n : ℕ) (G : SimpleGraph (Fin n)) (S : Set (Fin n)) (hBip : G.IsBipartiteWith S Sᶜ)
    (hroot : ∀ f : (Erdos713Gluing.wedge H x J y).Copy G, f (Sum.inl x) ∉ S) :
    (Nat.card G.edgeSet : ℝ) ≤
      (2^(2*((Fintype.card T+1)*Fintype.card W)+2) : ℕ)*((C+D)*(n : ℝ)^r) +
        (((Fintype.card T+1)*Fintype.card W)*n : ℕ) := by
  classical
  choose B hb hk hB using rooted_blockers H x J y G S hroot
  let A : Set (Fin n) := {v | v ∈ S ∧ ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B v}
  have hNoJ (v : Fin n) (hv : v ∈ S \ A) (g : J.Copy G) (hg : g y = v) : False := by
    rcases hB v hv.1 with hl | hr
    · exact hv.2 ⟨hv.1,hl⟩
    · exact hr g hg
  have hfree : ∀ σ : Fin n → Bool,
      ((keep G B σ).edgeFinset.card : ℝ) ≤ (C+D)*(n : ℝ)^r := by
    intro σ
    let K := keep G B σ
    have hsel (f : H.Copy K) (a : W) : selected B σ (f a) := by
      obtain ⟨b,hab⟩ := hNoIso a
      exact (f.toHom.map_adj hab).2.1
    have hHRoot (f : H.Copy K) : f x ∉ A := by
      intro hfx
      let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp f
      obtain ⟨b,_,hmem⟩ := hfx.2 g rfl
      exact Bool.noConfusion ((hsel f b).1.symm.trans ((hsel f x).2 (f b) hmem))
    have hleft := hH n (cross K A) A (Erdos713KstGluing.cross_isBipartiteWith K A)
      (fun f => hHRoot ((Copy.ofLE _ _ (cross_le K A)).comp f))
    have hright := hJ n (cross K (S \ A)) (S \ A)
      (Erdos713KstGluing.cross_isBipartiteWith K (S \ A)) (by
        intro f hf
        exact hNoJ (f y) hf
          ((Copy.ofLE _ _ ((cross_le K (S \ A)).trans (keep_le G B σ))).comp f) rfl)
    have hKB : K.IsBipartiteWith S Sᶜ := ⟨hBip.1,by intro u v hvw; exact hBip.2 hvw.1⟩
    have hsplit := edge_split_shore K S A hKB (fun _ hv => hv.1)
    have hsplit' : (Nat.card K.edgeSet : ℝ) ≤
        Nat.card (cross K A).edgeSet + Nat.card (cross K (S \ A)).edgeSet := by exact_mod_cast hsplit
    simp only [edgeFinset_card,Fintype.card_eq_nat_card]
    linarith
  have hh := Erdos713KstGluing.real_edges_le_of_keep_bound G B
    ((Fintype.card T+1)*Fintype.card W) _ hb hk (by positivity) hfree
  simpa only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin] using hh

lemma RootPowerBound.wedge {W T : Type*} [Fintype W] [Fintype T]
    {H : SimpleGraph W} {J : SimpleGraph T} {x : W} {y : T} {r : ℝ}
    (hH : RootPowerBound H x r) (hJ : RootPowerBound J y r)
    (hr : 1 ≤ r) (hNoIso : ∀ a, ∃ b, H.Adj a b) :
    RootPowerBound (Erdos713Gluing.wedge H x J y) (Sum.inl x) r := by
  classical
  obtain ⟨C,hC,hH⟩ := hH
  obtain ⟨D,hD,hJ⟩ := hJ
  let k := (Fintype.card T+1)*Fintype.card W
  refine ⟨(2^(2*k+2) : ℕ)*(C+D)+k,by positivity,?_⟩
  intro n G S hB hroot
  have hn : (n : ℝ) ≤ (n : ℝ)^r := by
    by_cases hn : n = 0
    · subst n; simp only [Nat.cast_zero]; positivity
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn' hr
  have hh := rooted_wedge_edge_bound H x hNoIso J y hC hD hH hJ n G S hB hroot
  change (Nat.card G.edgeSet : ℝ) ≤ (2^(2*k+2) : ℕ)*((C+D)*(n : ℝ)^r) + (k*n : ℕ) at hh
  simp only [Nat.cast_mul] at hh
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma RootPowerBound.mono {W : Type*} {H : SimpleGraph W} {x : W} {a b : ℝ}
    (h : RootPowerBound H x a) (hab : a ≤ b) : RootPowerBound H x b := by
  classical
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨C,hC,?_⟩
  intro n G S hB hroot
  by_cases hn : n = 0
  · subst n
    have he : G = ⊥ := Subsingleton.elim _ _
    simp only [he,edgeSet_bot,Nat.card_eq_fintype_card,Fintype.card_ofIsEmpty,Nat.cast_zero]
    positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  exact (hbound n G S hB hroot).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn' hab) hC)

lemma HasRootRate.unique {W : Type*} {H : SimpleGraph W} {x : W} {a b : ℝ}
    (hA : HasRootRate H x a) (hB : HasRootRate H x b) : a = b :=
  le_antisymm (hA.lower b hB.one_le hB.upper) (hB.lower a hA.one_le hA.upper)

lemma HasRootRate.wedge {W T : Type*} [Fintype W] [Fintype T]
    {H : SimpleGraph W} {J : SimpleGraph T} {x : W} {y : T} {a b : ℝ}
    (hH : HasRootRate H x a) (hJ : HasRootRate J y b)
    (hNoIso : ∀ v, ∃ w, H.Adj v w) :
    HasRootRate (Erdos713Gluing.wedge H x J y) (Sum.inl x) (max a b) := by
  refine ⟨hH.one_le.trans (le_max_left _ _),
    (hH.upper.mono (le_max_left _ _)).wedge (hJ.upper.mono (le_max_right _ _))
      (hH.one_le.trans (le_max_left _ _)) hNoIso,?_⟩
  intro c hc hRoot
  apply max_le
  · exact hH.lower c hc (hRoot.of_copy (leftCopy H x J y) x)
  · have hh : RootPowerBound (Erdos713Gluing.wedge H x J y) ((rightCopy H x J y) y) c := by
      simpa [rightCopy] using hRoot
    exact hJ.lower c hc (hh.of_copy (rightCopy H x J y) y)

/-- Opposite-root doubling does not further increase the rooted threshold. -/
lemma opposite_wedge_root_rate_iff {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ v, ∃ w, H.Adj v w) {x y : W} (hxy : H.Adj x y) {r : ℝ} :
    HasRootRate (Erdos713Gluing.wedge H x H y) (Sum.inl x) r ↔ HasRootRate H x r := by
  constructor
  · intro h
    refine ⟨h.one_le,h.upper.of_copy (leftCopy H x H y) x,?_⟩
    intro a ha hu
    exact h.lower a ha (hu.wedge (hu.of_adj hxy) ha hNoIso)
  · intro h
    simpa only [max_self] using h.wedge (h.of_reachable hxy.reachable) hNoIso

lemma opposite_wedge_matched {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hNoIso : ∀ v, ∃ w, H.Adj v w) {x y : W} (hxy : H.Adj x y) {r : ℝ} :
    HasRate (Erdos713Gluing.wedge H x H y) r ↔ HasRootRate (Erdos713Gluing.wedge H x H y) (Sum.inl x) r :=
  (opposite_wedge_rate_iff H hNoIso hxy).trans (opposite_wedge_root_rate_iff H hNoIso hxy).symm

#print axioms rooted_wedge_edge_bound
#print axioms RootPowerBound.wedge
#print axioms HasRootRate.wedge
#print axioms opposite_wedge_root_rate_iff
#print axioms opposite_wedge_matched
end Erdos713RootPower

namespace Erdos713Gluing
lemma wedge_connected {W T : Type*} {H : SimpleGraph W} {J : SimpleGraph T}
    (hH : H.Connected) (hJ : J.Connected) (x : W) (y : T) : (wedge H x J y).Connected := by
  classical
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl x,?_⟩
  rintro (a | b)
  · exact (hH x a).map (leftCopy H x J y).toHom
  · have hh := (hJ y b.val).map (rightCopy H x J y).toHom
    simpa [rightCopy,b.prop] using hh

lemma wedge_bipartite {W T : Type*} {H : SimpleGraph W} {J : SimpleGraph T}
    (hH : H.IsBipartite) (hJ : J.IsBipartite) (x : W) (y : T) : (wedge H x J y).IsBipartite := by
  classical
  obtain ⟨cH⟩ := hH
  obtain ⟨cJ⟩ := hJ
  let d : Fin 2 := cH x - cJ y
  have hd : cJ y+d = cH x := by dsimp [d]; abel
  let c : Vertex x y → Fin 2 := Sum.elim cH (fun b => cJ b.val+d)
  refine ⟨Coloring.mk c ?_⟩
  rintro (a | a) (b | b) hab he
  · exact cH.valid hab he
  · obtain ⟨rfl,hab⟩ := hab
    exact cJ.valid hab (add_right_cancel ((hd.trans he) : cJ y+d = cJ b.val+d))
  · obtain ⟨rfl,hab⟩ := hab
    exact cJ.valid hab (add_right_cancel ((he.trans hd.symm) : cJ a.val+d = cJ y+d))
  · exact cJ.valid hab (add_right_cancel he)

#print axioms wedge_connected
#print axioms wedge_bipartite
end Erdos713Gluing

namespace Erdos713ActualBlocks
open Erdos713Rate Erdos713RootPower Erdos713Gluing

/-- The opposite-root double of a connected graph has matching rooted bounds
at any rate it attains, even if its original block's ordinary rate is unknown. -/
lemma opposite_wedge_rootedRate {W : Type*} [Fintype W] {H : SimpleGraph W}
    (hH : H.Connected) (hNoIso : ∀ v, ∃ w, H.Adj v w) {x y : W} (hxy : H.Adj x y)
    {r : ℚ} (hr : HasRate (wedge H x H y) (r : ℝ)) : RootedRate (wedge H x H y) :=
  RootedRate.of_one_root (wedge_connected hH hH x y) (Sum.inl x) hr
    ((opposite_wedge_matched H hNoIso hxy).mp hr).upper

#print axioms opposite_wedge_rootedRate
end Erdos713ActualBlocks
