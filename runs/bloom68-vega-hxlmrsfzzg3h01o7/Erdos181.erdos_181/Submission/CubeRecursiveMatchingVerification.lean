import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# Verified reductions for the recursive-matching counterexample

The infinite matching-amplification argument is proved on paper in
`CubeRecursiveMatchingDisproof.md`. This file does not import `Spec.lean` and does not
claim a result about the Ramsey numbers of the ordinary cubes.
-/

namespace CubeRecursiveMatchingVerification

open SimpleGraph

/-- Red edges within equal-sized blocks; blue edges run between different blocks. -/
def blockRed (α β : Type*) : SimpleGraph (α × β) where
  Adj u v := u.1 = v.1 ∧ u.2 ≠ v.2
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless _ h := h.2 rfl

@[simp] theorem blockRed_adj {α β : Type*} (u v : α × β) :
    (blockRed α β).Adj u v ↔ u.1 = v.1 ∧ u.2 ≠ v.2 := Iff.rfl

@[simp] theorem blockRed_compl_adj {α β : Type*} (u v : α × β) :
    (blockRed α β)ᶜ.Adj u v ↔ u.1 ≠ v.1 := by
  simp only [SimpleGraph.compl_adj, blockRed_adj]
  constructor
  · rintro ⟨huv, h⟩ heq
    apply h
    refine ⟨heq, ?_⟩
    intro hsec
    exact huv (Prod.ext heq hsec)
  · intro h
    exact ⟨fun heq => h (congrArg Prod.fst heq), fun heq => h heq.1⟩

/-- An edgewise constant function is constant along any walk. -/
theorem constant_along_walk {V A : Type*} {G : SimpleGraph V} (f : V → A)
    (hf : ∀ ⦃u v⦄, G.Adj u v → f u = f v) {u v : V} (p : G.Walk u v) :
    f u = f v := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact (hf h).trans ih

/-- A connected graph with more than `|β|` vertices does not fit into disjoint
red cliques on `β`, regardless of the number of cliques. -/
theorem not_contained_blockRed {V α β : Type*} [Fintype V] [Fintype β]
    (H : SimpleGraph V) (hconn : H.Connected) (hcard : Fintype.card β < Fintype.card V) :
    ¬ H.IsContained (blockRed α β) := by
  rintro ⟨f⟩
  have hfirst (u v : V) : (f u).1 = (f v).1 := by
    obtain ⟨p⟩ := hconn.preconnected u v
    exact constant_along_walk (fun x => (f x).1)
      (fun {_ _} h => (f.toHom.map_rel h).1) p
  have hinj : Function.Injective (fun v : V => (f v).2) := by
    intro u v huv
    apply f.injective
    exact Prod.ext (hfirst u v) huv
  exact (not_le_of_gt hcard) (Fintype.card_le_of_injective _ hinj)

/-- A blue copy in the complete `k`-partite graph supplies a proper `k`-coloring. -/
theorem not_contained_blockBlue {V β : Type*} (H : SimpleGraph V) (k : ℕ)
    (hcolor : ¬ H.Colorable k) :
    ¬ H.IsContained (blockRed (Fin k) β)ᶜ := by
  rintro ⟨f⟩
  apply hcolor
  refine ⟨SimpleGraph.Coloring.mk (fun v => (f v).1) ?_⟩
  intro u v huv
  exact (blockRed_compl_adj _ _).mp (f.toHom.map_rel huv)

/-- An unconditional Ramsey countercoloring for every connected non-`k`-colorable graph.
The host has exactly `k * (|V|-1)` vertices. Containment is noninduced. -/
theorem multipartite_countercoloring {V : Type*} [Fintype V]
    (H : SimpleGraph V) (hconn : H.Connected) (k : ℕ) (hcolor : ¬ H.Colorable k) :
    ∃ R : SimpleGraph (Fin k × Fin (Fintype.card V - 1)),
      ¬ H.IsContained R ∧ ¬ H.IsContained Rᶜ := by
  haveI : Nonempty V := hconn.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  refine ⟨blockRed _ _, ?_, not_contained_blockBlue H k hcolor⟩
  apply not_contained_blockRed H hconn
  simp only [Fintype.card_fin]
  omega

-- BEGIN GENERATED FINITE CERTIFICATE
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The exact five recursive perfect matchings in the 32-vertex example. -/
def examplePermutations : List (List ℕ) := [[0], [0, 1], [0, 1, 3, 2], [2, 3, 4, 5, 6, 7, 0, 1], [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 8, 9]]

def doubleEdges (edges : List (ℕ × ℕ)) (p : List ℕ) : List (ℕ × ℕ) :=
  edges ++ edges.map (fun e => (e.1 + p.length, e.2 + p.length)) ++
    p.zipIdx.map (fun e => (e.2, p.length + e.1))

def exampleEdges : List (ℕ × ℕ) := examplePermutations.foldl doubleEdges []

def exampleGraph : SimpleGraph (Fin 32) :=
  SimpleGraph.fromRel fun x y => (x.val, y.val) ∈ exampleEdges

instance : DecidableRel exampleGraph.Adj := by
  unfold exampleGraph
  infer_instance

theorem example_permutations_valid :
    examplePermutations.all (fun p => decide (p.Perm (List.range p.length))) = true := by
  decide

theorem example_permutation_sizes :
    examplePermutations.map List.length = [1, 2, 4, 8, 16] := by decide

theorem example_degree : ∀ v : Fin 32, exampleGraph.degree v = 5 := by decide

private theorem fin3_options (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

private theorem fin3_options0 {x : Fin 3} (h : x ≠ 0) :
    x = 1 ∨ x = 2 := by
  fin_cases x <;> simp_all

private theorem fin3_force0 {x : Fin 3} (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  fin_cases x <;> simp_all

private theorem fin3_options1 {x : Fin 3} (h : x ≠ 1) :
    x = 0 ∨ x = 2 := by
  fin_cases x <;> simp_all

private theorem fin3_force1 {x : Fin 3} (h0 : x ≠ 0) (h2 : x ≠ 2) : x = 1 := by
  fin_cases x <;> simp_all

private theorem fin3_options2 {x : Fin 3} (h : x ≠ 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x <;> simp_all

private theorem fin3_force2 {x : Fin 3} (h0 : x ≠ 0) (h1 : x ≠ 1) : x = 2 := by
  fin_cases x <;> simp_all

private theorem fin3_impossible {x : Fin 3} (h0 : x ≠ 0) (h1 : x ≠ 1)
    (h2 : x ≠ 2) : False := by
  fin_cases x <;> simp_all

/-- An elementary finite case proof, generated and then checked by the Lean kernel. -/
theorem example_not_colorable_three : ¬ exampleGraph.Colorable 3 := by
  rintro ⟨c⟩
  rcases fin3_options (c 0) with h0 | h0 | h0
  ·
    rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 1 0 from by decide)) with h1 | h1
    ·
      rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 2 0 from by decide)) with h2 | h2
      ·
        rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          rcases fin3_options1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) with h6 | h6
          ·
            have h3 : c 3 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
            have h7 : c 7 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              exact fin3_impossible (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide))
            ·
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h11 : c 11 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
          ·
            have h3 : c 3 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
            have h7 : c 7 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
              have h11 : c 11 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
            ·
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h11 : c 11 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              have h14 : c 14 = 2 := fin3_force2 (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 12 14 from by decide))
              have h15 : c 15 = 0 := fin3_force0 (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
              rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                rcases fin3_options0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) with h19 | h19
                ·
                  have h22 : c 22 = 0 := fin3_force0 (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                  have h20 : c 20 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                  have h24 : c 24 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
                  have h25 : c 25 = 2 := fin3_force2 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 25 24 from by decide))
                  exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 29 25 from by decide))
                ·
                  have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide))
                  have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide))
                  have h21 : c 21 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                  have h23 : c 23 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
                  have h25 : c 25 = 1 := fin3_force1 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
                  exact fin3_impossible (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              ·
                have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
                have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
                have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
                have h21 : c 21 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                have h22 : c 22 = 1 := fin3_force1 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
                have h23 : c 23 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
                have h24 : c 24 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
                exact fin3_impossible (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
        ·
          have h5 : c 5 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide))
          have h7 : c 7 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
          rcases fin3_options2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) with h9 | h9
          ·
            have h11 : c 11 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
            have h10 : c 10 = 1 := fin3_force1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 10 11 from by decide))
            have h8 : c 8 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 8 10 from by decide))
            have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h14 : c 14 = 1 := fin3_force1 (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            have h15 : c 15 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            have h13 : c 13 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 13 15 from by decide))
            rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h26 : c 26 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h26] using c.valid (show exampleGraph.Adj 24 26 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide))
              have h6 : c 6 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 6 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
              have h3 : c 3 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h23 : c 23 = 0 := fin3_force0 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h25 : c 25 = 1 := fin3_force1 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
              exact fin3_impossible (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
            ·
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h23 : c 23 = 1 := fin3_force1 (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide))
              have h25 : c 25 = 0 := fin3_force0 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h25] using c.valid (show exampleGraph.Adj 24 25 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              exact fin3_impossible (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 28 24 from by decide))
          ·
            rcases fin3_options1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) with h8 | h8
            ·
              have h6 : c 6 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 6 8 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h3 : c 3 = 2 := fin3_force2 (by simpa only [h13] using c.valid (show exampleGraph.Adj 3 13 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
              rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h20 : c 20 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                have h22 : c 22 = 2 := fin3_force2 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                have h26 : c 26 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
                have h27 : c 27 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide))
                have h17 : c 17 = 2 := fin3_force2 (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                exact fin3_impossible (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide))
              ·
                have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
                have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
                have h19 : c 19 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
                have h23 : c 23 = 1 := fin3_force1 (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide))
                have h26 : c 26 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
                exact fin3_impossible (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide))
            ·
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              exact fin3_impossible (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
      ·
        have h3 : c 3 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 3 2 from by decide))
        rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h6 : c 6 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
          rcases fin3_options2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
          ·
            have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h13 : c 13 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
            have h9 : c 9 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
            have h7 : c 7 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 7 9 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h26 : c 26 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h27 : c 27 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide))
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              exact fin3_impossible (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide))
            ·
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h23 : c 23 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
              have h26 : c 26 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h27 : c 27 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              exact fin3_impossible (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide))
          ·
            have h10 : c 10 = 2 := fin3_force2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
            have h11 : c 11 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide))
            have h9 : c 9 = 2 := fin3_force2 (by simpa only [h11] using c.valid (show exampleGraph.Adj 9 11 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
            have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h13 : c 13 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
            have h14 : c 14 = 2 := fin3_force2 (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            have h15 : c 15 = 0 := fin3_force0 (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h15] using c.valid (show exampleGraph.Adj 5 15 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h28 : c 28 = 1 := fin3_force1 (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h28] using c.valid (show exampleGraph.Adj 24 28 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 29 28 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide))
            ·
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              exact fin3_impossible (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
        ·
          have h5 : c 5 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide))
          have h6 : c 6 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
          exact fin3_impossible (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
    ·
      rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 2 0 from by decide)) with h2 | h2
      ·
        have h3 : c 3 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 3 2 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
        rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h5 : c 5 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
          have h6 : c 6 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
          exact fin3_impossible (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
        ·
          have h6 : c 6 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
          rcases fin3_options1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
          ·
            have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h13 : c 13 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
            have h9 : c 9 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
            have h7 : c 7 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 7 9 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h23 : c 23 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
              have h26 : c 26 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h27 : c 27 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              exact fin3_impossible (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide))
            ·
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h26 : c 26 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h27 : c 27 = 0 := fin3_force0 (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide))
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              exact fin3_impossible (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide))
          ·
            have h10 : c 10 = 1 := fin3_force1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
            have h11 : c 11 = 0 := fin3_force0 (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
            have h9 : c 9 = 1 := fin3_force1 (by simpa only [h11] using c.valid (show exampleGraph.Adj 9 11 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
            have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h13 : c 13 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
            have h14 : c 14 = 1 := fin3_force1 (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            have h15 : c 15 = 0 := fin3_force0 (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h15] using c.valid (show exampleGraph.Adj 5 15 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
              exact fin3_impossible (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
            ·
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h28 : c 28 = 2 := fin3_force2 (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 24 28 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 29 28 from by decide))
      ·
        rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h5 : c 5 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
          have h7 : c 7 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
          rcases fin3_options1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) with h9 | h9
          ·
            have h11 : c 11 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
            have h10 : c 10 = 2 := fin3_force2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 10 11 from by decide))
            have h8 : c 8 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 8 10 from by decide))
            have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h14 : c 14 = 2 := fin3_force2 (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            have h15 : c 15 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            have h13 : c 13 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 13 15 from by decide))
            rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h23 : c 23 = 2 := fin3_force2 (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide))
              have h25 : c 25 = 0 := fin3_force0 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h25] using c.valid (show exampleGraph.Adj 24 25 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              exact fin3_impossible (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 28 24 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide))
            ·
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h26 : c 26 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h26] using c.valid (show exampleGraph.Adj 24 26 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide))
              have h6 : c 6 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 6 22 from by decide))
              have h3 : c 3 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h23 : c 23 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
              have h25 : c 25 = 2 := fin3_force2 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
              exact fin3_impossible (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide))
          ·
            rcases fin3_options2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) with h8 | h8
            ·
              have h6 : c 6 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 6 8 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              have h3 : c 3 = 1 := fin3_force1 (by simpa only [h13] using c.valid (show exampleGraph.Adj 3 13 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
              rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h17 : c 17 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h18 : c 18 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                have h19 : c 19 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
                have h23 : c 23 = 2 := fin3_force2 (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide))
                have h26 : c 26 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
                exact fin3_impossible (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide))
              ·
                have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
                have h22 : c 22 = 1 := fin3_force1 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                have h26 : c 26 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
                have h27 : c 27 = 0 := fin3_force0 (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
                have h17 : c 17 = 1 := fin3_force1 (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                exact fin3_impossible (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide))
            ·
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              exact fin3_impossible (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
        ·
          rcases fin3_options2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) with h6 | h6
          ·
            have h3 : c 3 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
            have h7 : c 7 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
              have h11 : c 11 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            ·
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              exact fin3_impossible (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
          ·
            have h3 : c 3 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
            have h7 : c 7 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
              have h11 : c 11 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            ·
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h11 : c 11 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              have h14 : c 14 = 1 := fin3_force1 (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 12 14 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h15 : c 15 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
              rcases fin3_options0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h17 : c 17 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h18 : c 18 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                have h20 : c 20 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                have h21 : c 21 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                have h22 : c 22 = 2 := fin3_force2 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
                have h23 : c 23 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
                have h24 : c 24 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
                exact fin3_impossible (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              ·
                rcases fin3_options0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) with h19 | h19
                ·
                  have h17 : c 17 = 0 := fin3_force0 (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                  have h18 : c 18 = 0 := fin3_force0 (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                  have h21 : c 21 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                  have h23 : c 23 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
                  have h25 : c 25 = 2 := fin3_force2 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
                  exact fin3_impossible (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide))
                ·
                  have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide))
                  have h20 : c 20 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                  have h24 : c 24 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
                  have h25 : c 25 = 1 := fin3_force1 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 25 24 from by decide))
                  exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 29 25 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide))
  ·
    rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 1 0 from by decide)) with h1 | h1
    ·
      rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 2 0 from by decide)) with h2 | h2
      ·
        rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          rcases fin3_options0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) with h6 | h6
          ·
            have h3 : c 3 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
            have h7 : c 7 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              exact fin3_impossible (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide))
            ·
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h11 : c 11 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              exact fin3_impossible (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
          ·
            have h3 : c 3 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
            have h7 : c 7 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h11 : c 11 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              have h14 : c 14 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 12 14 from by decide))
              have h15 : c 15 = 1 := fin3_force1 (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
              rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                rcases fin3_options1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) with h19 | h19
                ·
                  have h22 : c 22 = 1 := fin3_force1 (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                  have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide))
                  have h24 : c 24 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
                  have h25 : c 25 = 2 := fin3_force2 (by simpa only [h24] using c.valid (show exampleGraph.Adj 25 24 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
                  exact fin3_impossible (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 29 25 from by decide))
                ·
                  have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide))
                  have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide))
                  have h21 : c 21 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                  have h23 : c 23 = 2 := fin3_force2 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                  have h25 : c 25 = 0 := fin3_force0 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
                  exact fin3_impossible (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              ·
                have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
                have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
                have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
                have h21 : c 21 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                have h22 : c 22 = 0 := fin3_force0 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                have h19 : c 19 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
                have h23 : c 23 = 2 := fin3_force2 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                have h24 : c 24 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
                exact fin3_impossible (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
            ·
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h11 : c 11 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              exact fin3_impossible (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
        ·
          have h5 : c 5 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide))
          have h7 : c 7 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide))
          rcases fin3_options2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) with h9 | h9
          ·
            rcases fin3_options0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) with h8 | h8
            ·
              have h6 : c 6 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 6 8 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h3 : c 3 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 3 13 from by decide))
              rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h20 : c 20 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
                have h26 : c 26 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
                have h27 : c 27 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide))
                have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide))
                have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                exact fin3_impossible (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide))
              ·
                have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
                have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
                have h19 : c 19 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
                have h23 : c 23 = 0 := fin3_force0 (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                have h21 : c 21 = 2 := fin3_force2 (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                have h26 : c 26 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
                exact fin3_impossible (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide))
            ·
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              exact fin3_impossible (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
          ·
            have h11 : c 11 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
            have h10 : c 10 = 0 := fin3_force0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 10 11 from by decide))
            have h8 : c 8 = 2 := fin3_force2 (by simpa only [h10] using c.valid (show exampleGraph.Adj 8 10 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide))
            have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h14 : c 14 = 0 := fin3_force0 (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            have h15 : c 15 = 2 := fin3_force2 (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
            have h13 : c 13 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 13 15 from by decide))
            rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h26 : c 26 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 24 26 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide))
              have h6 : c 6 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 6 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
              have h3 : c 3 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide))
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h23 : c 23 = 1 := fin3_force1 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h25 : c 25 = 0 := fin3_force0 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
              exact fin3_impossible (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
            ·
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h23 : c 23 = 0 := fin3_force0 (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h25 : c 25 = 1 := fin3_force1 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 24 25 from by decide))
              exact fin3_impossible (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 28 24 from by decide))
      ·
        have h3 : c 3 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 3 2 from by decide))
        rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h6 : c 6 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide))
          rcases fin3_options2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
          ·
            have h10 : c 10 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
            have h11 : c 11 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide))
            have h9 : c 9 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 9 11 from by decide))
            have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h13 : c 13 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
            have h14 : c 14 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
            have h15 : c 15 = 1 := fin3_force1 (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 5 15 from by decide))
            rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h28 : c 28 = 0 := fin3_force0 (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h28] using c.valid (show exampleGraph.Adj 24 28 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              exact fin3_impossible (by simpa only [h28] using c.valid (show exampleGraph.Adj 29 28 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide))
            ·
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              exact fin3_impossible (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
          ·
            have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h13 : c 13 = 2 := fin3_force2 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
            have h9 : c 9 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
            have h7 : c 7 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 7 9 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h26 : c 26 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h27 : c 27 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide))
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide))
            ·
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h23 : c 23 = 2 := fin3_force2 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h26 : c 26 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h27 : c 27 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide))
        ·
          have h5 : c 5 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide))
          have h6 : c 6 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
          exact fin3_impossible (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
    ·
      rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 2 0 from by decide)) with h2 | h2
      ·
        have h3 : c 3 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 3 2 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
        rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h5 : c 5 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
          have h6 : c 6 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide))
          exact fin3_impossible (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
        ·
          have h6 : c 6 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
          rcases fin3_options0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
          ·
            have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h13 : c 13 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
            have h9 : c 9 = 2 := fin3_force2 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
            have h7 : c 7 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 7 9 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h23 : c 23 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
              have h26 : c 26 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h27 : c 27 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              exact fin3_impossible (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide))
            ·
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h26 : c 26 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h27 : c 27 = 1 := fin3_force1 (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide))
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              exact fin3_impossible (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide))
          ·
            have h10 : c 10 = 0 := fin3_force0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
            have h11 : c 11 = 1 := fin3_force1 (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
            have h9 : c 9 = 0 := fin3_force0 (by simpa only [h11] using c.valid (show exampleGraph.Adj 9 11 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
            have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h13 : c 13 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
            have h14 : c 14 = 0 := fin3_force0 (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            have h15 : c 15 = 1 := fin3_force1 (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h15] using c.valid (show exampleGraph.Adj 5 15 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
              exact fin3_impossible (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
            ·
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h28 : c 28 = 2 := fin3_force2 (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 24 28 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              exact fin3_impossible (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 29 28 from by decide))
      ·
        rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h5 : c 5 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
          have h7 : c 7 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
          rcases fin3_options0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) with h9 | h9
          ·
            have h11 : c 11 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
            have h10 : c 10 = 2 := fin3_force2 (by simpa only [h11] using c.valid (show exampleGraph.Adj 10 11 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
            have h8 : c 8 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 8 10 from by decide))
            have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h14 : c 14 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
            have h15 : c 15 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            have h13 : c 13 = 2 := fin3_force2 (by simpa only [h15] using c.valid (show exampleGraph.Adj 13 15 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
            rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h23 : c 23 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide))
              have h25 : c 25 = 1 := fin3_force1 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h25] using c.valid (show exampleGraph.Adj 24 25 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              exact fin3_impossible (by simpa only [h24] using c.valid (show exampleGraph.Adj 28 24 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide))
            ·
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h26 : c 26 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h26] using c.valid (show exampleGraph.Adj 24 26 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h6 : c 6 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 6 22 from by decide))
              have h3 : c 3 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h21 : c 21 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h23 : c 23 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
              have h25 : c 25 = 2 := fin3_force2 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
              exact fin3_impossible (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide))
          ·
            rcases fin3_options2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) with h8 | h8
            ·
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              exact fin3_impossible (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            ·
              have h6 : c 6 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 6 8 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              have h3 : c 3 = 0 := fin3_force0 (by simpa only [h13] using c.valid (show exampleGraph.Adj 3 13 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
              rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h17 : c 17 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h18 : c 18 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide))
                have h23 : c 23 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide))
                have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide))
                have h26 : c 26 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
                exact fin3_impossible (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide))
              ·
                have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
                have h22 : c 22 = 0 := fin3_force0 (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                have h26 : c 26 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
                have h27 : c 27 = 1 := fin3_force1 (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
                have h17 : c 17 = 0 := fin3_force0 (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h21 : c 21 = 2 := fin3_force2 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                exact fin3_impossible (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide))
        ·
          rcases fin3_options2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) with h6 | h6
          ·
            have h3 : c 3 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
            have h7 : c 7 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
              have h11 : c 11 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            ·
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              have h11 : c 11 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h14 : c 14 = 0 := fin3_force0 (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 12 14 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h15 : c 15 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
              rcases fin3_options1 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h17 : c 17 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h18 : c 18 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                have h20 : c 20 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
                have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
                have h23 : c 23 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
                have h24 : c 24 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
                exact fin3_impossible (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              ·
                rcases fin3_options1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) with h19 | h19
                ·
                  have h17 : c 17 = 1 := fin3_force1 (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                  have h18 : c 18 = 1 := fin3_force1 (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                  have h21 : c 21 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                  have h23 : c 23 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
                  have h25 : c 25 = 2 := fin3_force2 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
                  exact fin3_impossible (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide))
                ·
                  have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide))
                  have h20 : c 20 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                  have h24 : c 24 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
                  have h25 : c 25 = 0 := fin3_force0 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 25 24 from by decide))
                  exact fin3_impossible (by simpa only [h25] using c.valid (show exampleGraph.Adj 29 25 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide))
          ·
            have h3 : c 3 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
            have h7 : c 7 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h10 : c 10 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
              have h11 : c 11 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide))
            ·
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide))
              exact fin3_impossible (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
  ·
    rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 1 0 from by decide)) with h1 | h1
    ·
      rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 2 0 from by decide)) with h2 | h2
      ·
        rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          rcases fin3_options0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) with h6 | h6
          ·
            have h3 : c 3 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
            have h7 : c 7 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h11 : c 11 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h14 : c 14 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 12 14 from by decide))
              have h15 : c 15 = 2 := fin3_force2 (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
              rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                rcases fin3_options2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) with h19 | h19
                ·
                  have h22 : c 22 = 2 := fin3_force2 (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
                  have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide))
                  have h24 : c 24 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
                  have h25 : c 25 = 1 := fin3_force1 (by simpa only [h24] using c.valid (show exampleGraph.Adj 25 24 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
                  exact fin3_impossible (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 29 25 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide))
                ·
                  have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide))
                  have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide))
                  have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                  have h23 : c 23 = 1 := fin3_force1 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                  have h25 : c 25 = 0 := fin3_force0 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
                  exact fin3_impossible (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
              ·
                have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
                have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
                have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
                have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
                have h19 : c 19 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
                have h23 : c 23 = 1 := fin3_force1 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                have h24 : c 24 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
                exact fin3_impossible (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide))
            ·
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h9 : c 9 = 1 := fin3_force1 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h11 : c 11 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              exact fin3_impossible (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
          ·
            have h3 : c 3 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
            have h7 : c 7 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              exact fin3_impossible (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
            ·
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h11 : c 11 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              exact fin3_impossible (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
        ·
          have h5 : c 5 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide))
          have h7 : c 7 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide))
          rcases fin3_options1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) with h9 | h9
          ·
            rcases fin3_options0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) with h8 | h8
            ·
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              exact fin3_impossible (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
            ·
              have h6 : c 6 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 6 8 from by decide))
              have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h3 : c 3 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 3 13 from by decide))
              rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h20 : c 20 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
                have h26 : c 26 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
                have h27 : c 27 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide))
                have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide))
                have h21 : c 21 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                exact fin3_impossible (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide))
              ·
                have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
                have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
                have h19 : c 19 = 0 := fin3_force0 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide))
                have h23 : c 23 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide))
                have h21 : c 21 = 1 := fin3_force1 (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                have h26 : c 26 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
                exact fin3_impossible (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide))
          ·
            have h11 : c 11 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
            have h10 : c 10 = 0 := fin3_force0 (by simpa only [h11] using c.valid (show exampleGraph.Adj 10 11 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
            have h8 : c 8 = 1 := fin3_force1 (by simpa only [h10] using c.valid (show exampleGraph.Adj 8 10 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide))
            have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h14 : c 14 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
            have h15 : c 15 = 1 := fin3_force1 (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
            have h13 : c 13 = 0 := fin3_force0 (by simpa only [h15] using c.valid (show exampleGraph.Adj 13 15 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
            rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h26 : c 26 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 24 26 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h6 : c 6 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 6 22 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide))
              have h3 : c 3 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide))
              have h18 : c 18 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h23 : c 23 = 2 := fin3_force2 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h25 : c 25 = 0 := fin3_force0 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
              exact fin3_impossible (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
            ·
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h23 : c 23 = 0 := fin3_force0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h25 : c 25 = 2 := fin3_force2 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
              have h24 : c 24 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 24 25 from by decide))
              exact fin3_impossible (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 28 24 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide))
      ·
        have h3 : c 3 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 3 2 from by decide))
        rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h6 : c 6 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide))
          rcases fin3_options1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
          ·
            have h10 : c 10 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
            have h11 : c 11 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide))
            have h9 : c 9 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 9 11 from by decide))
            have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h13 : c 13 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
            have h14 : c 14 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
            have h15 : c 15 = 2 := fin3_force2 (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 5 15 from by decide))
            rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h28 : c 28 = 0 := fin3_force0 (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h28] using c.valid (show exampleGraph.Adj 24 28 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              exact fin3_impossible (by simpa only [h28] using c.valid (show exampleGraph.Adj 29 28 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide))
            ·
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide)) (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide))
              exact fin3_impossible (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide))
          ·
            have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h13 : c 13 = 1 := fin3_force1 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
            have h9 : c 9 = 0 := fin3_force0 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
            have h7 : c 7 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 7 9 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h26 : c 26 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h27 : c 27 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide))
              have h17 : c 17 = 1 := fin3_force1 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide))
              have h20 : c 20 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide))
            ·
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide))
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h23 : c 23 = 1 := fin3_force1 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h26 : c 26 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h27 : c 27 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide))
        ·
          have h5 : c 5 = 2 := fin3_force2 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide))
          have h6 : c 6 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide))
          exact fin3_impossible (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide))
    ·
      rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 2 0 from by decide)) with h2 | h2
      ·
        have h3 : c 3 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 3 2 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
        rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h5 : c 5 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
          have h6 : c 6 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide))
          exact fin3_impossible (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide))
        ·
          have h6 : c 6 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 6 3 from by decide))
          rcases fin3_options0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
          ·
            have h10 : c 10 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
            have h11 : c 11 = 2 := fin3_force2 (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
            have h9 : c 9 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 9 11 from by decide))
            have h12 : c 12 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h13 : c 13 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
            have h14 : c 14 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
            have h15 : c 15 = 2 := fin3_force2 (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 5 15 from by decide))
            rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
              exact fin3_impossible (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide))
            ·
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h28 : c 28 = 1 := fin3_force1 (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide))
              have h24 : c 24 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 24 28 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              exact fin3_impossible (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h28] using c.valid (show exampleGraph.Adj 29 28 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide))
          ·
            have h12 : c 12 = 1 := fin3_force1 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
            have h13 : c 13 = 0 := fin3_force0 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
            have h9 : c 9 = 1 := fin3_force1 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
            have h7 : c 7 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 7 9 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h19 : c 19 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h23 : c 23 = 0 := fin3_force0 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
              have h26 : c 26 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h27 : c 27 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
              exact fin3_impossible (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide))
            ·
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide))
              have h26 : c 26 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
              have h27 : c 27 = 2 := fin3_force2 (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide))
              have h19 : c 19 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
              have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide))
              have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide))
              exact fin3_impossible (by simpa only [h20] using c.valid (show exampleGraph.Adj 30 20 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 30 12 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 30 27 from by decide))
      ·
        rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 4 0 from by decide)) with h4 | h4
        ·
          have h5 : c 5 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 5 4 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
          have h7 : c 7 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 7 5 from by decide))
          rcases fin3_options0 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) with h9 | h9
          ·
            rcases fin3_options1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide)) with h8 | h8
            ·
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 0 := fin3_force0 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              exact fin3_impossible (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
            ·
              have h6 : c 6 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 6 8 from by decide))
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 2 := fin3_force2 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
              have h3 : c 3 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 3 13 from by decide))
              rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h17 : c 17 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h18 : c 18 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                have h19 : c 19 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 19 17 from by decide))
                have h23 : c 23 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide))
                have h21 : c 21 = 0 := fin3_force0 (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                have h26 : c 26 = 1 := fin3_force1 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
                exact fin3_impossible (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide))
              ·
                have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
                have h22 : c 22 = 0 := fin3_force0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
                have h26 : c 26 = 0 := fin3_force0 (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide))
                have h27 : c 27 = 2 := fin3_force2 (by simpa only [h26] using c.valid (show exampleGraph.Adj 27 26 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
                have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h27] using c.valid (show exampleGraph.Adj 17 27 from by decide))
                have h21 : c 21 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
                exact fin3_impossible (by simpa only [h26] using c.valid (show exampleGraph.Adj 31 26 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 31 21 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 31 13 from by decide))
          ·
            have h11 : c 11 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
            have h10 : c 10 = 1 := fin3_force1 (by simpa only [h11] using c.valid (show exampleGraph.Adj 10 11 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
            have h8 : c 8 = 0 := fin3_force0 (by simpa only [h10] using c.valid (show exampleGraph.Adj 8 10 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 8 9 from by decide))
            have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
            have h14 : c 14 = 1 := fin3_force1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
            have h15 : c 15 = 0 := fin3_force0 (by simpa only [h10] using c.valid (show exampleGraph.Adj 15 10 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide))
            have h13 : c 13 = 1 := fin3_force1 (by simpa only [h15] using c.valid (show exampleGraph.Adj 13 15 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide))
            rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
            ·
              have h17 : c 17 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
              have h18 : c 18 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
              have h23 : c 23 = 1 := fin3_force1 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 23 18 from by decide))
              have h21 : c 21 = 0 := fin3_force0 (by simpa only [h23] using c.valid (show exampleGraph.Adj 21 23 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h25 : c 25 = 2 := fin3_force2 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 24 25 from by decide))
              exact fin3_impossible (by simpa only [h24] using c.valid (show exampleGraph.Adj 28 24 from by decide)) (by simpa only [h10] using c.valid (show exampleGraph.Adj 28 10 from by decide)) (by simpa only [h18] using c.valid (show exampleGraph.Adj 28 18 from by decide))
            ·
              have h20 : c 20 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide))
              have h26 : c 26 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide))
              have h24 : c 24 = 0 := fin3_force0 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h26] using c.valid (show exampleGraph.Adj 24 26 from by decide))
              have h22 : c 22 = 1 := fin3_force1 (by simpa only [h24] using c.valid (show exampleGraph.Adj 22 24 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
              have h6 : c 6 = 2 := fin3_force2 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 6 22 from by decide))
              have h3 : c 3 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
              have h19 : c 19 = 2 := fin3_force2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide))
              have h17 : c 17 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide))
              have h18 : c 18 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide))
              have h21 : c 21 = 1 := fin3_force1 (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide)) (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide))
              have h23 : c 23 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide)) (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide))
              have h25 : c 25 = 1 := fin3_force1 (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide)) (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide))
              exact fin3_impossible (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide))
        ·
          rcases fin3_options1 (by simpa only [h4] using c.valid (show exampleGraph.Adj 6 4 from by decide)) with h6 | h6
          ·
            have h3 : c 3 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide))
            have h7 : c 7 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide))
            have h5 : c 5 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide))
            rcases fin3_options0 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h11 : c 11 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h9] using c.valid (show exampleGraph.Adj 13 9 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h14 : c 14 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 12 14 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h15 : c 15 = 2 := fin3_force2 (by simpa only [h5] using c.valid (show exampleGraph.Adj 15 5 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 15 13 from by decide))
              rcases fin3_options2 (by simpa only [h0] using c.valid (show exampleGraph.Adj 16 0 from by decide)) with h16 | h16
              ·
                have h17 : c 17 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 17 16 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                have h18 : c 18 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 18 16 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                have h20 : c 20 = 2 := fin3_force2 (by simpa only [h16] using c.valid (show exampleGraph.Adj 20 16 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide))
                have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                have h22 : c 22 = 1 := fin3_force1 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h20] using c.valid (show exampleGraph.Adj 22 20 from by decide))
                have h19 : c 19 = 0 := fin3_force0 (by simpa only [h22] using c.valid (show exampleGraph.Adj 19 22 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide))
                have h23 : c 23 = 0 := fin3_force0 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                have h24 : c 24 = 2 := fin3_force2 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
                exact fin3_impossible (by simpa only [h16] using c.valid (show exampleGraph.Adj 26 16 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 26 8 from by decide)) (by simpa only [h24] using c.valid (show exampleGraph.Adj 26 24 from by decide))
              ·
                rcases fin3_options2 (by simpa only [h3] using c.valid (show exampleGraph.Adj 19 3 from by decide)) with h19 | h19
                ·
                  have h17 : c 17 = 2 := fin3_force2 (by simpa only [h19] using c.valid (show exampleGraph.Adj 17 19 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 17 1 from by decide))
                  have h18 : c 18 = 2 := fin3_force2 (by simpa only [h19] using c.valid (show exampleGraph.Adj 18 19 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 18 2 from by decide))
                  have h21 : c 21 = 1 := fin3_force1 (by simpa only [h5] using c.valid (show exampleGraph.Adj 21 5 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 21 17 from by decide))
                  have h23 : c 23 = 0 := fin3_force0 (by simpa only [h21] using c.valid (show exampleGraph.Adj 23 21 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 23 7 from by decide))
                  have h25 : c 25 = 1 := fin3_force1 (by simpa only [h23] using c.valid (show exampleGraph.Adj 25 23 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
                  exact fin3_impossible (by simpa only [h9] using c.valid (show exampleGraph.Adj 27 9 from by decide)) (by simpa only [h25] using c.valid (show exampleGraph.Adj 27 25 from by decide)) (by simpa only [h17] using c.valid (show exampleGraph.Adj 27 17 from by decide))
                ·
                  have h22 : c 22 = 2 := fin3_force2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 22 6 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 22 19 from by decide))
                  have h20 : c 20 = 0 := fin3_force0 (by simpa only [h4] using c.valid (show exampleGraph.Adj 20 4 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 20 22 from by decide))
                  have h24 : c 24 = 1 := fin3_force1 (by simpa only [h14] using c.valid (show exampleGraph.Adj 24 14 from by decide)) (by simpa only [h22] using c.valid (show exampleGraph.Adj 24 22 from by decide))
                  have h25 : c 25 = 0 := fin3_force0 (by simpa only [h24] using c.valid (show exampleGraph.Adj 25 24 from by decide)) (by simpa only [h15] using c.valid (show exampleGraph.Adj 25 15 from by decide))
                  exact fin3_impossible (by simpa only [h25] using c.valid (show exampleGraph.Adj 29 25 from by decide)) (by simpa only [h19] using c.valid (show exampleGraph.Adj 29 19 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 29 11 from by decide))
            ·
              have h12 : c 12 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide)) (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide))
              have h9 : c 9 = 0 := fin3_force0 (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide)) (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide))
              have h11 : c 11 = 2 := fin3_force2 (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide))
              exact fin3_impossible (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide))
          ·
            have h3 : c 3 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 3 1 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 3 6 from by decide))
            have h7 : c 7 = 0 := fin3_force0 (by simpa only [h2] using c.valid (show exampleGraph.Adj 7 2 from by decide)) (by simpa only [h6] using c.valid (show exampleGraph.Adj 7 6 from by decide))
            have h5 : c 5 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 5 7 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 5 1 from by decide))
            rcases fin3_options2 (by simpa only [h6] using c.valid (show exampleGraph.Adj 8 6 from by decide)) with h8 | h8
            ·
              have h10 : c 10 = 1 := fin3_force1 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              have h12 : c 12 = 2 := fin3_force2 (by simpa only [h8] using c.valid (show exampleGraph.Adj 12 8 from by decide)) (by simpa only [h2] using c.valid (show exampleGraph.Adj 12 2 from by decide))
              have h13 : c 13 = 1 := fin3_force1 (by simpa only [h3] using c.valid (show exampleGraph.Adj 13 3 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 13 12 from by decide))
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h13] using c.valid (show exampleGraph.Adj 9 13 from by decide))
              have h11 : c 11 = 0 := fin3_force0 (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))
              exact fin3_impossible (by simpa only [h11] using c.valid (show exampleGraph.Adj 14 11 from by decide)) (by simpa only [h4] using c.valid (show exampleGraph.Adj 14 4 from by decide)) (by simpa only [h12] using c.valid (show exampleGraph.Adj 14 12 from by decide))
            ·
              have h9 : c 9 = 2 := fin3_force2 (by simpa only [h7] using c.valid (show exampleGraph.Adj 9 7 from by decide)) (by simpa only [h8] using c.valid (show exampleGraph.Adj 9 8 from by decide))
              have h10 : c 10 = 0 := fin3_force0 (by simpa only [h8] using c.valid (show exampleGraph.Adj 10 8 from by decide)) (by simpa only [h0] using c.valid (show exampleGraph.Adj 10 0 from by decide))
              exact fin3_impossible (by simpa only [h10] using c.valid (show exampleGraph.Adj 11 10 from by decide)) (by simpa only [h1] using c.valid (show exampleGraph.Adj 11 1 from by decide)) (by simpa only [h9] using c.valid (show exampleGraph.Adj 11 9 from by decide))

def exampleFourColors : Fin 32 → Fin 4 := ![0, 1, 1, 2, 1, 0, 0, 2, 1, 0, 2, 3, 2, 1, 0, 3, 1, 3, 2, 0, 0, 2, 2, 1, 1, 0, 0, 2, 0, 1, 1, 3]

theorem example_colorable_four : exampleGraph.Colorable 4 := by
  exact ⟨SimpleGraph.Coloring.mk exampleFourColors (by decide)⟩

theorem example_chromatic_number : exampleGraph.chromaticNumber = 4 := by
  exact (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable).2
    ⟨example_colorable_four, example_not_colorable_three⟩

theorem example_connected : exampleGraph.Connected := by
  have h0 : exampleGraph.Reachable 0 0 := .rfl
  have h1 : exampleGraph.Reachable 0 1 := h0.trans (show exampleGraph.Adj 0 1 from by decide).reachable
  have h2 : exampleGraph.Reachable 0 2 := h0.trans (show exampleGraph.Adj 0 2 from by decide).reachable
  have h3 : exampleGraph.Reachable 0 3 := h1.trans (show exampleGraph.Adj 1 3 from by decide).reachable
  have h4 : exampleGraph.Reachable 0 4 := h0.trans (show exampleGraph.Adj 0 4 from by decide).reachable
  have h5 : exampleGraph.Reachable 0 5 := h1.trans (show exampleGraph.Adj 1 5 from by decide).reachable
  have h6 : exampleGraph.Reachable 0 6 := h3.trans (show exampleGraph.Adj 3 6 from by decide).reachable
  have h7 : exampleGraph.Reachable 0 7 := h2.trans (show exampleGraph.Adj 2 7 from by decide).reachable
  have h8 : exampleGraph.Reachable 0 8 := h6.trans (show exampleGraph.Adj 6 8 from by decide).reachable
  have h9 : exampleGraph.Reachable 0 9 := h7.trans (show exampleGraph.Adj 7 9 from by decide).reachable
  have h10 : exampleGraph.Reachable 0 10 := h0.trans (show exampleGraph.Adj 0 10 from by decide).reachable
  have h11 : exampleGraph.Reachable 0 11 := h1.trans (show exampleGraph.Adj 1 11 from by decide).reachable
  have h12 : exampleGraph.Reachable 0 12 := h2.trans (show exampleGraph.Adj 2 12 from by decide).reachable
  have h13 : exampleGraph.Reachable 0 13 := h3.trans (show exampleGraph.Adj 3 13 from by decide).reachable
  have h14 : exampleGraph.Reachable 0 14 := h4.trans (show exampleGraph.Adj 4 14 from by decide).reachable
  have h15 : exampleGraph.Reachable 0 15 := h5.trans (show exampleGraph.Adj 5 15 from by decide).reachable
  have h16 : exampleGraph.Reachable 0 16 := h0.trans (show exampleGraph.Adj 0 16 from by decide).reachable
  have h17 : exampleGraph.Reachable 0 17 := h1.trans (show exampleGraph.Adj 1 17 from by decide).reachable
  have h18 : exampleGraph.Reachable 0 18 := h2.trans (show exampleGraph.Adj 2 18 from by decide).reachable
  have h19 : exampleGraph.Reachable 0 19 := h3.trans (show exampleGraph.Adj 3 19 from by decide).reachable
  have h20 : exampleGraph.Reachable 0 20 := h4.trans (show exampleGraph.Adj 4 20 from by decide).reachable
  have h21 : exampleGraph.Reachable 0 21 := h5.trans (show exampleGraph.Adj 5 21 from by decide).reachable
  have h22 : exampleGraph.Reachable 0 22 := h6.trans (show exampleGraph.Adj 6 22 from by decide).reachable
  have h23 : exampleGraph.Reachable 0 23 := h7.trans (show exampleGraph.Adj 7 23 from by decide).reachable
  have h24 : exampleGraph.Reachable 0 24 := h14.trans (show exampleGraph.Adj 14 24 from by decide).reachable
  have h25 : exampleGraph.Reachable 0 25 := h15.trans (show exampleGraph.Adj 15 25 from by decide).reachable
  have h26 : exampleGraph.Reachable 0 26 := h8.trans (show exampleGraph.Adj 8 26 from by decide).reachable
  have h27 : exampleGraph.Reachable 0 27 := h9.trans (show exampleGraph.Adj 9 27 from by decide).reachable
  have h28 : exampleGraph.Reachable 0 28 := h10.trans (show exampleGraph.Adj 10 28 from by decide).reachable
  have h29 : exampleGraph.Reachable 0 29 := h11.trans (show exampleGraph.Adj 11 29 from by decide).reachable
  have h30 : exampleGraph.Reachable 0 30 := h12.trans (show exampleGraph.Adj 12 30 from by decide).reachable
  have h31 : exampleGraph.Reachable 0 31 := h13.trans (show exampleGraph.Adj 13 31 from by decide).reachable
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2
  refine ⟨0, ?_⟩
  intro v
  fin_cases v <;> assumption

/-- The explicit example has a countercoloring on 3*31 = 93 vertices. -/
theorem example_countercoloring_93 :
    ∃ R : SimpleGraph (Fin 3 × Fin 31),
      ¬ exampleGraph.IsContained R ∧ ¬ exampleGraph.IsContained Rᶜ := by
  simpa using multipartite_countercoloring exampleGraph example_connected 3
    example_not_colorable_three

#print axioms multipartite_countercoloring
#print axioms example_not_colorable_three
#print axioms example_chromatic_number
#print axioms example_connected
#print axioms example_degree
#print axioms example_countercoloring_93

-- END GENERATED FINITE CERTIFICATE
end CubeRecursiveMatchingVerification
