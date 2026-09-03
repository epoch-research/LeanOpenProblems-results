import Submission.Auxiliary
import Submission.Critical

/-!
# A conditional two-edge resilience bridge for Erdős–Sós

This file proves a **conditional** implication, not R2 or Erdős–Sós.  Its only
imports are previously verified auxiliary files; it does not import the problem
statement or use either conjectural declaration in `Submission.Spec`.

`D k G = 2 e(G) - (k - 1) |V(G)|` uses rational subtraction.  Deleting at most
`|V(G)|` actual edges preserves positive excess when the tree parameter drops
from `k` to `k - 2`.  The quantifiers in `RobustUniversal` range over **every**
such deletion and **every** smaller tree, with ordinary (not induced) copies.

`UniformR2` is the unproved, connected, minimum/maximum-degree candidate.  The
proof will only need its restriction `UniformCriticalR2` to induced-critical
hosts.  That restriction is a weaker assumption: critical hosts are proved
connected and satisfy the candidate's degree hypotheses.  No converse between
these two assumptions is claimed.  In particular, no instance of either R2
statement is asserted without an explicit hypothesis.
-/

open SimpleGraph

namespace Erdos548.Resilience

universe u v

section Excess

variable {V : Type u}

/-- Twice the excess used in `Critical`, with no truncated coefficient at `k = 0`. -/
noncomputable def D (k : ℕ) (G : SimpleGraph V) : ℚ :=
  2 * (G.edgeSet.ncard : ℚ) - ((k : ℚ) - 1) * Nat.card V

theorem D_eq_two_mul_excess (k : ℕ) (G : SimpleGraph V) :
    D k G = 2 * Critical.excess k G := by
  unfold D Critical.excess
  ring

/-- Exact edge partition for deletion of actual edges. -/
theorem ncard_deleteEdges_add [Finite V] (G : SimpleGraph V)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    (G.deleteEdges F).edgeSet.ncard + F.ncard = G.edgeSet.ncard := by
  rw [SimpleGraph.edgeSet_deleteEdges]
  exact Set.ncard_diff_add_ncard_of_subset hF

/-- The requested deletion identity.  The subtraction `n - |F|` is in `ℚ`;
the only natural subtraction is `k - 2`, justified by `2 ≤ k`. -/
theorem D_deleteEdges [Finite V] (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph V)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    D (k - 2) (G.deleteEdges F) =
      D k G + 2 * ((Nat.card V : ℚ) - (F.ncard : ℚ)) := by
  have he : ((G.deleteEdges F).edgeSet.ncard : ℚ) + (F.ncard : ℚ) =
      (G.edgeSet.ncard : ℚ) := by
    exact_mod_cast ncard_deleteEdges_add G F hF
  unfold D
  rw [Nat.cast_sub hk]
  push_cast
  nlinarith

/-- The same identity for the half-normalized excess from `Critical.lean`. -/
theorem excess_deleteEdges [Finite V] (k : ℕ) (hk : 2 ≤ k) (G : SimpleGraph V)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) :
    Critical.excess (k - 2) (G.deleteEdges F) =
      Critical.excess k G + (Nat.card V : ℚ) - (F.ncard : ℚ) := by
  have h := D_deleteEdges k hk G F hF
  rw [D_eq_two_mul_excess, D_eq_two_mul_excess] at h
  linarith

/-- Positive excess survives every deletion in the allowed budget, including
exactly `n` deleted edges.  The damaged graph need not be connected. -/
theorem excess_deleteEdges_pos [Finite V] (k : ℕ) (hk : 2 ≤ k)
    (G : SimpleGraph V) (hG : 0 < Critical.excess k G)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) (hbudget : F.ncard ≤ Nat.card V) :
    0 < Critical.excess (k - 2) (G.deleteEdges F) := by
  rw [excess_deleteEdges k hk G F hF]
  have hb : (F.ncard : ℚ) ≤ (Nat.card V : ℚ) := by exact_mod_cast hbudget
  linarith

/-- Positive excess itself supplies the order bound needed for a `k`-edge tree.
This includes `k = 0`, and is not an extra assumption on a critical reduction. -/
theorem card_ge_of_excess_pos [Finite V] (k : ℕ) (G : SimpleGraph V)
    (hG : 0 < Critical.excess k G) : k + 1 ≤ Nat.card V := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := Critical.exists_degree_ge_of_excess_pos k G hG
  have hlt := G.degree_lt_card_verts x
  simpa only [Nat.card_eq_fintype_card] using
    (Nat.succ_le_of_lt (lt_of_le_of_lt hx hlt))

/-- In particular, every damaged host is large enough for the smaller tree.
Its vertex type is unchanged by `deleteEdges`. -/
theorem card_ge_after_deletion [Finite V] (k : ℕ) (hk : 2 ≤ k)
    (G : SimpleGraph V) (hG : 0 < Critical.excess k G)
    (F : Set (Sym2 V)) (hF : F ⊆ G.edgeSet) (hbudget : F.ncard ≤ Nat.card V) :
    (k - 2) + 1 ≤ Nat.card V :=
  card_ge_of_excess_pos (k - 2) (G.deleteEdges F)
    (excess_deleteEdges_pos k hk G hG F hF hbudget)

end Excess

section Universality

variable {V : Type u}

/-- Ordinary containment of every tree on `k + 1` vertices, i.e. every `k`-edge tree. -/
def TreeUniversal (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G

/-- Universality after **any** set of at most `n` actual edge deletions. -/
def RobustUniversal (j : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ F : Set (Sym2 V), F ⊆ G.edgeSet → F.ncard ≤ Nat.card V →
    TreeUniversal j (G.deleteEdges F)

/-- A uniform strict-threshold statement at one tree size.  An explicit order
hypothesis is redundant by `card_ge_of_excess_pos`.  All finite hosts, including
disconnected ones, are quantified, which is essential after edge deletion. -/
def StrictAt (k : ℕ) : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    0 < Critical.excess k G → TreeUniversal k G

/-- The proposed R2 statement, as an assumption and **not** a theorem.
`Fintype` and decidable adjacency merely let us write mathlib's `minDegree` and
`maxDegree`; classical instances exist for every finite graph.  There is no
extra density or criticality assumption in this version. -/
def UniformR2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → ⌈(k : ℚ) / 2⌉₊ ≤ G.minDegree → k ≤ G.maxDegree →
    RobustUniversal (k - 2) G → TreeUniversal k G

/-- Restrict R2 to positive-excess induced-critical hosts.  This is a logically
weaker assumption than `UniformR2`, not an asserted equivalence with it. -/
def UniformCriticalR2 : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    Critical.IsInducedCritical k G →
    RobustUniversal (k - 2) G → TreeUniversal k G

/-- Universality transports along an ordinary host copy. -/
theorem TreeUniversal.trans {W : Type v} {k : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (h : TreeUniversal k G) (hGH : G.IsContained H) : TreeUniversal k H := by
  intro T hT
  exact (h T hT).trans hGH

/-- The robust universal consequence of the induction hypothesis.  Only the
smaller strict-threshold statement is used, once for each damaged host. -/
theorem robustUniversal_of_strictAt [Finite V] (k : ℕ) (hk : 2 ≤ k)
    (ih : StrictAt.{u} (k - 2)) (G : SimpleGraph V)
    (hG : 0 < Critical.excess k G) : RobustUniversal (k - 2) G := by
  intro F hF hb
  exact ih (G.deleteEdges F) (excess_deleteEdges_pos k hk G hG F hF hb)

end Universality

section CriticalHosts

variable {V : Type u}

/-- In a vertex set closed under adjacency, every incident edge is internal. -/
theorem incidentEdges_eq_internal (G : SimpleGraph V) (s : Set V)
    (hclosed : ∀ ⦃x y⦄, x ∈ s → G.Adj x y → y ∈ s) :
    Critical.incidentEdges G s = G.edgeSet ∩ s.sym2 := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    change (G.Adj a b ∧ ∃ x ∈ s, x ∈ s(a, b)) ↔
      G.Adj a b ∧ a ∈ s ∧ b ∈ s
    constructor
    · rintro ⟨hab, x, hx, hxe⟩
      rcases Sym2.mem_iff.mp hxe with rfl | rfl
      · exact ⟨hab, hx, hclosed hx hab⟩
      · exact ⟨hab, hclosed hx hab.symm, hx⟩
    · rintro ⟨hab, ha, _⟩
      exact ⟨hab, a, ha, Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-- A finite induced-critical positive-excess graph is connected.  Otherwise a
proper reachable component violates the incident-edge inequality. -/
theorem connected_of_inducedCritical [Finite V] {k : ℕ} {G : SimpleGraph V}
    (h : Critical.IsInducedCritical k G) : G.Connected := by
  classical
  letI : Nonempty V := h.nonempty
  refine ⟨?_⟩
  intro u v
  by_contra huv
  let s : Set V := {w | G.Reachable u w}
  have hs : s.Nonempty := ⟨u, SimpleGraph.Reachable.rfl⟩
  have hproper : s ≠ Set.univ := by
    intro heq
    have hv : v ∈ s := heq ▸ Set.mem_univ v
    exact huv hv
  have hclosed : ∀ ⦃x y⦄, x ∈ s → G.Adj x y → y ∈ s :=
    fun _ _ hx hxy => hx.trans hxy.reachable
  have hi := h.incidentEdges_bound hs
  rw [incidentEdges_eq_internal G s hclosed,
    ← Critical.ncard_edgeSet_induce G s] at hi
  exact (not_lt_of_ge (h.proper_edge_threshold hproper)) hi

/-- The original candidate implies its critical-host restriction.  Connectivity,
minimum degree, and maximum degree are all derived, not added to the reduction. -/
theorem uniformCriticalR2_of_uniformR2 (hR2 : UniformR2.{u}) :
    UniformCriticalR2.{u} := by
  classical
  intro k hk V _ G hc hrob
  letI := Fintype.ofFinite V
  exact hR2 k hk G (connected_of_inducedCritical hc)
    hc.minDegree_ge_ceil hc.maxDegree_ge hrob

end CriticalHosts

section SmallCases

variable {V : Type u}

/-- A three-vertex tree omits at least one of the three possible edges. -/
theorem fin_three_tree_missing_edge (T : SimpleGraph (Fin 3)) (hT : T.IsTree) :
    ¬ T.Adj 0 1 ∨ ¬ T.Adj 0 2 ∨ ¬ T.Adj 1 2 := by
  classical
  by_contra! h
  rcases h with ⟨h01, h02, h12⟩
  have h10 := h01.symm
  have h20 := h02.symm
  have h21 := h12.symm
  have heq : T = ⊤ := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp_all
  have ht : (⊤ : SimpleGraph (Fin 3)).IsTree := heq ▸ hT
  have hc := ht.card_edgeFinset
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at hc
  norm_num at hc

/-- Two distinct neighbors contain every three-vertex tree.  Extra host edges
are harmless: these are ordinary copies, not induced copies. -/
theorem fin_three_tree_isContained_of_two_neighbors (G : SimpleGraph V)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : v ≠ w)
    (T : SimpleGraph (Fin 3)) (hT : T.IsTree) : T.IsContained G := by
  have hvu := huv.symm
  have hwu := huw.symm
  rcases fin_three_tree_missing_edge T hT with hmiss | hmiss | hmiss
  · have hmiss' : ¬ T.Adj 1 0 := fun h => hmiss h.symm
    refine ⟨{ toHom := { toFun := ![v, w, u], map_rel' := ?_ }, injective' := ?_ }⟩
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    · intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [huv.ne, huw.ne, huv.ne.symm, huw.ne.symm, hvw.symm]
  · have hmiss' : ¬ T.Adj 2 0 := fun h => hmiss h.symm
    refine ⟨{ toHom := { toFun := ![v, u, w], map_rel' := ?_ }, injective' := ?_ }⟩
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    · intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [huv.ne, huw.ne, huv.ne.symm, huw.ne.symm, hvw.symm]
  · have hmiss' : ¬ T.Adj 2 1 := fun h => hmiss h.symm
    refine ⟨{ toHom := { toFun := ![u, v, w], map_rel' := ?_ }, injective' := ?_ }⟩
    · intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    · intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [huv.ne, huw.ne, huv.ne.symm, huw.ne.symm, hvw.symm]

/-- The elementary `k = 2` strict-threshold base case: average degree greater
than one gives a vertex with two distinct neighbors. -/
theorem strictAt_two : StrictAt.{u} 2 := by
  intro V _ G hG T hT
  obtain ⟨u, hu⟩ := Critical.exists_neighborSet_ncard_ge_of_excess_pos 2 G hG
  obtain ⟨v, hv, w, hw, hvw⟩ := (Set.one_lt_ncard (s := G.neighborSet u)).mp (show 1 < (G.neighborSet u).ncard by omega)
  exact fin_three_tree_isContained_of_two_neighbors G hv hw hvw T hT

/-- The zero- and one-edge cases, using the already verified elementary lemmas. -/
theorem strictAt_of_le_one (k : ℕ) (hk : k ≤ 1) : StrictAt.{u} k := by
  intro V _ G hG T _
  interval_cases k
  · letI : Nonempty V := Critical.nonempty_of_excess_pos 0 G hG
    exact Auxiliary.isContained_of_subsingleton (α := Fin 1) T G
  · apply Auxiliary.fin_two_isContained_of_ncard_pos G _ T
    have hq : (0 : ℚ) < (G.edgeSet.ncard : ℚ) := by
      simpa [Critical.excess] using hG
    exact_mod_cast hq

end SmallCases

section ConditionalBridge

/-- Sound strong induction on the number of tree edges.  The only recursive
call is at `k - 2 < k`, and it is uniform over all finite damaged hosts and all
smaller trees.  The critical reduction is chosen from positive excess alone;
no failure of the desired embedding is assumed or used to construct it. -/
theorem strictAt_of_uniformCriticalR2 (hR2 : UniformCriticalR2.{u}) :
    ∀ k : ℕ, StrictAt.{u} k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hsmall : k ≤ 1
    · exact strictAt_of_le_one k hsmall
    by_cases htwo : k = 2
    · subst k
      exact strictAt_two
    have hk : 3 ≤ k := by omega
    intro G hG
    obtain ⟨s, _, hc⟩ := Critical.exists_induced_critical k G hG
    have hrob : RobustUniversal (k - 2) (G.induce s) :=
      robustUniversal_of_strictAt k (by omega) (ih (k - 2) (by omega))
        (G.induce s) hc.positive
    exact (hR2 k hk (G.induce s) hc hrob).trans ⟨SimpleGraph.Copy.induce G s⟩

/-- The full degree/connectivity candidate suffices for the strict-threshold
conclusion at every tree size.  R2 remains an explicit hypothesis. -/
theorem strictAt_of_uniformR2 (hR2 : UniformR2.{u}) (k : ℕ) : StrictAt.{u} k :=
  strictAt_of_uniformCriticalR2 (uniformCriticalR2_of_uniformR2 hR2) k

/-- The usual universally quantified strict ES statement, conditional on the
weaker critical-host restriction of R2. -/
theorem strictThresholdStatement_of_uniformCriticalR2
    (hR2 : UniformCriticalR2.{0}) : Auxiliary.StrictThresholdStatement := by
  intro n k _ G hG
  apply strictAt_of_uniformCriticalR2 hR2 k G
  simpa only [Critical.excess, Nat.card_fin] using sub_pos.mpr hG

/-- The usual universally quantified strict ES statement, conditional on the
original R2 candidate with exactly its stated degree and connectivity conditions. -/
theorem strictThresholdStatement_of_uniformR2 (hR2 : UniformR2.{0}) :
    Auxiliary.StrictThresholdStatement :=
  strictThresholdStatement_of_uniformCriticalR2 (uniformCriticalR2_of_uniformR2 hR2)

/-- The original `+1` ES formulation, with the unproved candidate as a parameter.
The implication from the strict threshold to `+1` is already verified in
`Auxiliary`; no conjectural theorem is imported or invoked. -/
theorem plusOneStatement_of_uniformR2 (hR2 : UniformR2.{0}) :
    Auxiliary.PlusOneStatement :=
  Auxiliary.plusOneStatement_of_strictThresholdStatement
    (strictThresholdStatement_of_uniformR2 hR2)

/-- The exact target interface, restated rather than imported from the problem
file.  This is a conditional theorem, **not** an unconditional proof of ES. -/
theorem erdos_548_of_uniformR2 (hR2 : UniformR2.{0}) :
    ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
      ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
        ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G :=
  plusOneStatement_of_uniformR2 hR2

end ConditionalBridge

end Erdos548.Resilience

/- Transitive axiom checks for every theorem.  R2 is only a hypothesis. -/
#print axioms Erdos548.Resilience.D_eq_two_mul_excess
#print axioms Erdos548.Resilience.ncard_deleteEdges_add
#print axioms Erdos548.Resilience.D_deleteEdges
#print axioms Erdos548.Resilience.excess_deleteEdges
#print axioms Erdos548.Resilience.excess_deleteEdges_pos
#print axioms Erdos548.Resilience.card_ge_of_excess_pos
#print axioms Erdos548.Resilience.card_ge_after_deletion
#print axioms Erdos548.Resilience.TreeUniversal.trans
#print axioms Erdos548.Resilience.robustUniversal_of_strictAt
#print axioms Erdos548.Resilience.incidentEdges_eq_internal
#print axioms Erdos548.Resilience.connected_of_inducedCritical
#print axioms Erdos548.Resilience.uniformCriticalR2_of_uniformR2
#print axioms Erdos548.Resilience.fin_three_tree_missing_edge
#print axioms Erdos548.Resilience.fin_three_tree_isContained_of_two_neighbors
#print axioms Erdos548.Resilience.strictAt_two
#print axioms Erdos548.Resilience.strictAt_of_le_one
#print axioms Erdos548.Resilience.strictAt_of_uniformCriticalR2
#print axioms Erdos548.Resilience.strictAt_of_uniformR2
#print axioms Erdos548.Resilience.strictThresholdStatement_of_uniformCriticalR2
#print axioms Erdos548.Resilience.strictThresholdStatement_of_uniformR2
#print axioms Erdos548.Resilience.plusOneStatement_of_uniformR2
#print axioms Erdos548.Resilience.erdos_548_of_uniformR2
