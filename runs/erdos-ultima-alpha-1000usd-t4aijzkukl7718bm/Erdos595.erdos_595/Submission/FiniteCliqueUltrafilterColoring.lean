import Submission.OrderedUltrafilter

/-!
The symmetric OR Fubini extension of a countable graph with no infinite
clique has a countable proper vertex coloring. Its color is a finite maximal
clique in the original trace of the ultrafilter. In particular this strengthens
the first-stage result for order-oriented extensions of countable K4-free
bases; it does not settle higher stages or Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph Filter
namespace Erdos595FiniteCliqueUltrafilter
open Erdos595Work

variable {V : Type*} (G : SimpleGraph V)

/-- Every clique is finite; there need not be a uniform finite clique bound. -/
def FiniteCliques : Prop := ∀ S : Set V, G.IsClique S → S.Finite

lemma finiteCliques_of_cliqueFree {n : ℕ} (hG : G.CliqueFree n) : FiniteCliques G := by
  classical
  intro S hS
  by_contra hn
  obtain ⟨t,ht,hcard⟩ := (show S.Infinite from hn).exists_subset_card_eq n
  exact hG t ⟨hS.subset ht,hcard⟩

/-- A finite maximal clique in an arbitrary trace subset, including the
empty subset. It has no common neighbor within that subset. -/
theorem finite_maximal (hG : FiniteCliques G) (T : Set V) :
    ∃ s : Finset V, (↑s : Set V) ⊆ T ∧ G.IsClique (s : Set V) ∧
      ∀ v ∈ T, ¬∀ w ∈ s, G.Adj w v := by
  classical
  obtain ⟨S,hS⟩ := zorn_subset {S : Set V | S ⊆ T ∧ G.IsClique S} (by
    intro c hc hchain
    refine ⟨⋃₀ c,⟨?_,?_⟩,fun s hs => Set.subset_sUnion_of_mem hs⟩
    · intro v hv
      obtain ⟨s,hs,hv⟩ := Set.mem_sUnion.mp hv
      exact (hc hs).1 hv
    · intro v hv w hw hvw
      obtain ⟨s,hs,hvs⟩ := Set.mem_sUnion.mp hv
      obtain ⟨t,ht,hwt⟩ := Set.mem_sUnion.mp hw
      obtain ⟨u,hu,hsu,htu⟩ := hchain.directedOn s hs t ht
      exact (hc hu).2 (hsu hvs) (htu hwt) hvw)
  have hfin : S.Finite := hG S hS.1.2
  refine ⟨hfin.toFinset,?_,?_,?_⟩
  · simpa only [hfin.coe_toFinset] using hS.1.1
  · simpa only [hfin.coe_toFinset] using hS.1.2
  · intro v hv hadj
    have hi : G.IsClique (insert v S) := hS.1.2.insert (by
      intro w hw _
      exact (hadj w (hfin.mem_toFinset.mpr hw)).symm)
    have hsub : insert v S ⊆ S := hS.2 ⟨Set.insert_subset hv hS.1.1,hi⟩
      (Set.subset_insert v S)
    have hmem := hsub (Set.mem_insert v S)
    exact G.loopless v (hadj v (hfin.mem_toFinset.mpr hmem))

def trace (p : Ultrafilter V) : Set V := {v | G.neighborSet v ∈ p}

noncomputable def code (hG : FiniteCliques G) (p : Ultrafilter V) : Finset V :=
  (finite_maximal G hG (trace G p)).choose

lemma code_subset (hG : FiniteCliques G) (p : Ultrafilter V) :
    (↑(code G hG p) : Set V) ⊆ trace G p :=
  (finite_maximal G hG (trace G p)).choose_spec.1

lemma code_maximal (hG : FiniteCliques G) (p : Ultrafilter V)
    {v : V} (hv : v ∈ trace G p) : ¬∀ w ∈ code G hG p, G.Adj w v :=
  (finite_maximal G hG (trace G p)).choose_spec.2.2 v hv

/-- One Fubini direction already separates the two finite clique codes. -/
theorem code_ne (hG : FiniteCliques G) {p q : Ultrafilter V}
    (hpq : fubiniAdj G p q) : code G hG p ≠ code G hG q := by
  intro he
  have hS : (⋂ w ∈ (↑(code G hG p) : Set V), G.neighborSet w) ∈ p :=
    (Filter.biInter_mem (code G hG p).finite_toSet).mpr (fun _ hw => code_subset G hG p hw)
  obtain ⟨v,hv,hw⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hpq hS)
  apply code_maximal G hG q hv
  intro w hmem
  have hmem' : w ∈ code G hG p := he ▸ hmem
  exact Set.mem_iInter₂.mp hw w hmem'

/-- Looplessness follows from the same maximal-clique code. -/
def orGraph (hG : FiniteCliques G) : SimpleGraph (Ultrafilter V) where
  Adj p q := fubiniAdj G p q ∨ fubiniAdj G q p
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h.elim (fun h => code_ne G hG h rfl) (fun h => code_ne G hG h rfl)

noncomputable def cliqueColoring (hG : FiniteCliques G) :
    (orGraph G hG).Coloring (Finset V) :=
  SimpleGraph.Coloring.mk (code G hG) (fun h =>
    h.elim (fun h => code_ne G hG h) (fun h he => code_ne G hG h he.symm))

/-- This holds without a fixed finite clique bound. -/
theorem or_countable_coloring [Countable V] (hG : FiniteCliques G) :
    Nonempty ((orGraph G hG).Coloring ℕ) := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat (Finset V)
  exact ⟨(orGraph G hG).recolorOfEmbedding ⟨e,he⟩ (cliqueColoring G hG)⟩

/-- Every chosen order-oriented extension is a subgraph of the OR graph. -/
theorem ordered_countable_coloring [Countable V] [LinearOrder (Ultrafilter V)]
    (hG : FiniteCliques G) :
    Nonempty ((Erdos595OrderedUltrafilter.graph G).Coloring ℕ) := by
  obtain ⟨c⟩ := or_countable_coloring G hG
  let f : Erdos595OrderedUltrafilter.graph G →g orGraph G hG :=
    ⟨id,fun h => h.imp And.right And.right⟩
  exact ⟨c.comp f⟩

theorem ordered_K4_countable_coloring [Countable V] [LinearOrder (Ultrafilter V)]
    (hG : G.CliqueFree 4) :
    Nonempty ((Erdos595OrderedUltrafilter.graph G).Coloring ℕ) :=
  ordered_countable_coloring G (finiteCliques_of_cliqueFree G hG)

/-- The finite-clique code also covers first extensions of bases of size
at most continuum. Countability of the base is not needed for this EDGE
cover conclusion. -/
theorem or_cover_of_size {W : Type} (H : SimpleGraph W) (hH : FiniteCliques H)
    (hW : Cardinal.mk W ≤ Cardinal.continuum) :
    IsCountableUnionOfTriangleFree (orGraph H hH) := by
  classical
  have hcard : Cardinal.mk (Finset W) ≤ Cardinal.continuum := by
    cases finite_or_infinite W with
    | inl h =>
      letI := h
      exact Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
    | inr h =>
      letI := h
      simpa only [Cardinal.mk_finset_of_infinite] using hW
  have hb : Cardinal.mk (Finset W) ≤ Cardinal.mk (ℕ → Fin 2) := by
    simpa only [Cardinal.mk_arrow,Cardinal.mk_fin,Cardinal.mk_nat,
      Cardinal.lift_uzero,Nat.cast_ofNat,Cardinal.two_power_aleph0] using hcard
  let e : Finset W ↪ (ℕ → Fin 2) :=
    (Cardinal.lift_mk_le'.mp (by simpa only [Cardinal.lift_uzero] using hb)).some
  exact countable_union_of_coloring _
    ((orGraph H hH).recolorOfEmbedding e (cliqueColoring H hH))

#print axioms or_cover_of_size
#print axioms finite_maximal
#print axioms code_ne
#print axioms or_countable_coloring
#print axioms ordered_K4_countable_coloring
end Erdos595FiniteCliqueUltrafilter
