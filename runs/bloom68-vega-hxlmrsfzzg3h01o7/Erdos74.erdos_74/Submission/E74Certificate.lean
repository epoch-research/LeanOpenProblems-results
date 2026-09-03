import Submission.E74Parity
import Submission.E74Walk

/-!
# Finite certificates for short parity supports

If every short support has at least `t` edges, a finite branching search produces
an actual subgraph on at most `2 * L ^ t` vertices on which every Boolean cut has
at least `t` bad edges.  A node records a set `D` of distinct edges already chosen.
It chooses a violated closed walk and branches over the walk's edges outside `D`.

The recursive invariant is stated for every graph containing the certificate.
Consequently, the edges in `D` need not be added to a leaf certificate: a leaf is
the empty subgraph, and its conclusion follows from the assumed badness of `D`.
Only vertices of the chosen nonempty closed walks are counted.
-/

open SimpleGraph

namespace E74

universe u
variable {V : Type u}

section Search
variable [DecidableEq V]

/-- The vertex budget for a search of the given remaining depth. -/
private def searchVertexBound (L : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => L + L * searchVertexBound L n

private theorem searchVertexBound_add_two_le {L : ℕ} (hL : 2 ≤ L) (n : ℕ) :
    searchVertexBound L n + 2 ≤ 2 * L ^ n := by
  induction n with
  | zero => simp [searchVertexBound]
  | succ n ih =>
    calc
      searchVertexBound L (n + 1) + 2 = L + L * searchVertexBound L n + 2 := rfl
      _ ≤ L * (searchVertexBound L n + 2) := by nlinarith
      _ ≤ L * (2 * L ^ n) := Nat.mul_le_mul_left L ih
      _ = 2 * L ^ (n + 1) := by rw [pow_succ]; ring

/-- In a nonempty closed walk the initial vertex occurs again at the end, so
there are at most `length` distinct vertices, not merely `length + 1`. -/
private theorem closedWalk_verts_ncard_le_length {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hne : w ≠ Walk.nil) : w.toSubgraph.verts.ncard ≤ w.length := by
  classical
  have hcard : w.support.toFinset.card ≤ w.length := by
    cases w with
    | nil => exact (hne rfl).elim
    | cons h q =>
      simp only [Walk.support_cons, List.toFinset_cons, Walk.length_cons]
      rw [Finset.insert_eq_of_mem (List.mem_toFinset.mpr q.end_mem_support)]
      simpa only [Walk.length_support] using q.support.toFinset_card_le
  simpa only [Walk.verts_toSubgraph, ← List.coe_toFinset, Set.ncard_coe_finset] using hcard

/-- A failed support exposes a short closed walk with nonzero twisted sum. -/
private theorem exists_violated_closedWalk {G : SimpleGraph V} {L t : ℕ}
    (hno : ¬ ∃ S, ShortSupport G L S ∧ S.card < t)
    (D : Finset (Sym2 V)) (hD : (D : Set (Sym2 V)) ⊆ G.edgeSet) (hcard : D.card < t) :
    ∃ (v : V) (w : G.Walk v v), w.length ≤ L ∧ walkXor (twist D) w ≠ false := by
  classical
  by_contra hn
  apply hno
  refine ⟨D, ⟨hD, ?_⟩, hcard⟩
  intro v w hw
  by_contra hxor
  exact hn ⟨v, w, hw, hxor⟩

/-- The finite search invariant.  For every containing graph and every cut,
if the previously selected edges are bad, at least `t` edges are bad. -/
private theorem exists_search_certificate [Fintype V] (G : SimpleGraph V) (L t : ℕ)
    (hno : ¬ ∃ S, ShortSupport G L S ∧ S.card < t) (n : ℕ)
    (D : Finset (Sym2 V)) (hD : (D : Set (Sym2 V)) ⊆ G.edgeSet)
    (hdepth : D.card + n = t) :
    ∃ H : G.Subgraph, H.verts.ncard ≤ searchVertexBound L n ∧
      ∀ (K : SimpleGraph V), H.spanningCoe ≤ K → ∀ p : V → Bool,
        D ⊆ badEdges K p → t ≤ (badEdges K p).card := by
  classical
  induction n generalizing D with
  | zero =>
    refine ⟨⊥, by simp [searchVertexBound], ?_⟩
    intro K _ p hbad
    simpa only [Nat.add_zero] using hdepth.symm.trans_le (Finset.card_le_card hbad)
  | succ n ih =>
    obtain ⟨v, w, hw, hxor⟩ := exists_violated_closedWalk hno D hD (by omega)
    have hne : w ≠ Walk.nil := by
      intro heq
      subst w
      exact hxor rfl
    let A : Finset (Sym2 V) := w.edges.toFinset \ D
    have hA (e : A) : (e : Sym2 V) ∈ w.edges ∧ (e : Sym2 V) ∉ D := by
      simpa only [A, Finset.mem_sdiff, List.mem_toFinset] using e.property
    have hAc : A.card ≤ L := by
      calc
        A.card ≤ w.edges.toFinset.card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ w.edges.length := w.edges.toFinset_card_le
        _ = w.length := w.length_edges
        _ ≤ L := hw
    have hchild (e : A) :
        ∃ H : G.Subgraph, H.verts.ncard ≤ searchVertexBound L n ∧
          ∀ (K : SimpleGraph V), H.spanningCoe ≤ K → ∀ p : V → Bool,
            insert (e : Sym2 V) D ⊆ badEdges K p → t ≤ (badEdges K p).card := by
      apply ih (insert (e : Sym2 V) D)
      · intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact w.edges_subset_edgeSet (hA e).1
        · exact hD hf
      · rw [Finset.card_insert_of_notMem (hA e).2]
        omega
    choose C hC using hchild
    let H : G.Subgraph := w.toSubgraph ⊔ ⨆ e : A, C e
    have hwH : w.toSubgraph ≤ H := le_sup_left
    have hCH (e : A) : C e ≤ H := (le_iSup C e).trans le_sup_right
    refine ⟨H, ?_, ?_⟩
    · have hsum : (∑ e : A, (C e).verts.ncard) ≤ A.card * searchVertexBound L n := by
        calc
          (∑ e : A, (C e).verts.ncard) ≤ ∑ _e : A, searchVertexBound L n :=
            Finset.sum_le_sum (fun e _ => (hC e).1)
          _ = A.card * searchVertexBound L n := by simp
      calc
        H.verts.ncard = (w.toSubgraph.verts ∪ ⋃ e : A, (C e).verts).ncard := by
          simp only [H, Subgraph.verts_sup, Subgraph.verts_iSup]
        _ ≤ w.toSubgraph.verts.ncard + (⋃ e : A, (C e).verts).ncard :=
          Set.ncard_union_le _ _
        _ ≤ L + ∑ e : A, (C e).verts.ncard :=
          Nat.add_le_add ((closedWalk_verts_ncard_le_length w hne).trans hw)
            (Set.ncard_iUnion_le_of_fintype _)
        _ ≤ L + A.card * searchVertexBound L n := Nat.add_le_add_left hsum L
        _ ≤ L + L * searchVertexBound L n :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hAc) L
        _ = searchVertexBound L (n + 1) := rfl
    · intro K hHK p hbad
      have hwK : w.toSubgraph.spanningCoe ≤ K :=
        (Subgraph.spanningCoe_le_of_le hwH).trans hHK
      have hedges : ∀ e ∈ w.edges, e ∈ K.edgeSet := by
        intro e he
        apply SimpleGraph.edgeSet_mono hwK
        exact w.mem_edges_toSubgraph.mpr he
      let q : K.Walk v v := w.transfer K hedges
      have hqxor : walkXor (twist D) q ≠ false := by
        simpa only [q, walkXor_transfer] using hxor
      obtain ⟨e, heq, hebad, heD⟩ :=
        exists_badEdge_not_mem_of_walkXor_ne_false p hbad q hqxor
      have hew : e ∈ w.edges := by simpa only [q, Walk.edges_transfer] using heq
      have heA : e ∈ A := Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hew, heD⟩
      exact (hC ⟨e, heA⟩).2 K
        ((Subgraph.spanningCoe_le_of_le (hCH ⟨e, heA⟩)).trans hHK) p
        (Finset.insert_subset_iff.mpr ⟨hebad, hbad⟩)

/-- Absence of a support with fewer than `t` edges has a small, genuine subgraph
certificate: every Boolean cut of that subgraph has at least `t` bad edges. -/
theorem exists_small_cut_certificate [Fintype V] (G : SimpleGraph V) {L t : ℕ}
    (hL : 2 ≤ L) (hno : ¬ ∃ S, ShortSupport G L S ∧ S.card < t) :
    ∃ H : G.Subgraph, H.verts.ncard ≤ 2 * L ^ t ∧
      ∀ p : V → Bool, t ≤ (badEdges H.spanningCoe p).card := by
  obtain ⟨H, hsize, hcert⟩ := exists_search_certificate G L t hno t ∅
    (by simp) (by simp)
  refine ⟨H, hsize.trans ?_, ?_⟩
  · have h := searchVertexBound_add_two_le hL t
    omega
  · intro p
    exact hcert H.spanningCoe le_rfl p (Finset.empty_subset _)

end Search

/-- Hereditarily small cuts force a short parity support of size below `t`. -/
theorem exists_shortSupport_of_smallCuts [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : ℕ → ℕ)
    (hG : SmallCuts G B) {t L : ℕ} (ht : 2 ≤ t) (hL : 2 ≤ L)
    (hB : 2 * L ^ t ≤ B t) : ∃ S, ShortSupport G L S ∧ S.card < t := by
  classical
  by_contra hno
  obtain ⟨H, hsize, hcert⟩ := exists_small_cut_certificate G hL hno
  obtain ⟨p, hp⟩ := hG t ht H (hsize.trans hB)
  exact (not_lt_of_ge (hcert p)) hp

end E74
