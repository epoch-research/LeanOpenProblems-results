import Submission.Chain

/-!
# The cover lemma: either few edges hit all short odd closed walks, or there is a small
subgraph far from bipartite
-/

open SimpleGraph

namespace Erdos74Aux

variable {V : Type*}

/-- Abstract cover lemma for a family of nonempty sets of size at most `ℓ`. -/
theorem cover_abstract {α ι : Type*} [DecidableEq α] [DecidableEq ι] (ℓ : ℕ) (E : ι → Finset α)
    (j : ℕ) : ∀ (S : Set ι), (∀ i ∈ S, (E i).Nonempty ∧ (E i).card ≤ ℓ) →
    (∃ F : Finset α, F.card ≤ j ∧ ∀ i ∈ S, ¬ Disjoint F (E i)) ∨
    (∃ D : Finset ι, (↑D : Set ι) ⊆ S ∧ D.card ≤ (ℓ + 1) ^ j ∧
      ∀ F : Finset α, F.card ≤ j → ∃ i ∈ D, Disjoint F (E i)) := by
  induction j with
  | zero =>
    intro S hS
    by_cases hSe : S = ∅
    · left; exact ⟨∅, by simp, by simp [hSe]⟩
    · right
      obtain ⟨C, hC⟩ := Set.nonempty_iff_ne_empty.mpr hSe
      refine ⟨{C}, by simpa using hC, by simp, ?_⟩
      intro F hF
      have : F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hF)
      exact ⟨C, by simp, by simp [this]⟩
  | succ j ih =>
    intro S hS
    by_cases hSe : S = ∅
    · left; exact ⟨∅, by simp, by simp [hSe]⟩
    obtain ⟨C, hC⟩ := Set.nonempty_iff_ne_empty.mpr hSe
    by_cases hleft : ∃ e ∈ E C, ∃ F : Finset α, F.card ≤ j ∧
        ∀ i ∈ {i ∈ S | e ∉ E i}, ¬ Disjoint F (E i)
    · obtain ⟨e, heC, F, hF, hcov⟩ := hleft
      left
      refine ⟨insert e F, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
      intro i hi
      by_cases hei : e ∈ E i
      · rw [Finset.not_disjoint_iff]; exact ⟨e, Finset.mem_insert_self _ _, hei⟩
      · have := hcov i ⟨hi, hei⟩
        intro hdis
        exact this (Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdis)
    · push_neg at hleft
      right
      have hsub : ∀ e ∈ E C, ∃ D : Finset ι, (↑D : Set ι) ⊆ {i ∈ S | e ∉ E i} ∧
          D.card ≤ (ℓ + 1) ^ j ∧ ∀ F : Finset α, F.card ≤ j → ∃ i ∈ D, Disjoint F (E i) := by
        intro e he
        rcases ih {i ∈ S | e ∉ E i} (fun i hi => hS i hi.1) with h | h
        · exfalso
          obtain ⟨F, hF, hcov⟩ := h
          obtain ⟨i, hi, hdis⟩ := hleft e he F hF
          exact hcov i hi hdis
        · exact h
      choose! Dsub hDsub using hsub
      refine ⟨insert C ((E C).biUnion Dsub), ?_, ?_, ?_⟩
      · intro X hX
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
          Finset.mem_biUnion] at hX
        rcases hX with rfl | ⟨e, he, hX⟩
        · exact hC
        · exact ((hDsub e he).1 hX).1
      · have h1 : 1 ≤ (ℓ + 1) ^ j := Nat.one_le_pow _ _ (by omega)
        calc (insert C ((E C).biUnion Dsub)).card ≤ ((E C).biUnion Dsub).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (∑ e ∈ E C, (Dsub e).card) + 1 := by gcongr; exact Finset.card_biUnion_le
          _ ≤ (∑ e ∈ E C, (ℓ + 1) ^ j) + 1 := by
              gcongr with e he; exact (hDsub e he).2.1
          _ = (E C).card * (ℓ + 1) ^ j + 1 := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ℓ * (ℓ + 1) ^ j + 1 := by gcongr; exact (hS C hC).2
          _ ≤ (ℓ + 1) ^ (j + 1) := by rw [pow_succ]; nlinarith
      · intro F hF
        by_cases hFC : Disjoint F (E C)
        · exact ⟨C, Finset.mem_insert_self _ _, hFC⟩
        · rw [Finset.not_disjoint_iff] at hFC
          obtain ⟨e, heF, heC⟩ := hFC
          obtain ⟨i, hiD, hdis⟩ := (hDsub e heC).2.2 (F.erase e)
            (by rw [Finset.card_erase_of_mem heF]; omega)
          have hei : e ∉ E i := ((hDsub e heC).1 hiD).2
          refine ⟨i, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨e, heC, hiD⟩), ?_⟩
          rw [Finset.disjoint_left] at hdis ⊢
          intro a haF haE
          by_cases hae : a = e
          · exact hei (hae ▸ haE)
          · exact hdis (Finset.mem_erase.mpr ⟨hae, haF⟩) haE

/-- Parity of a walk along which a `2`-coloring alternates. -/
lemma walk_color_parity {G : SimpleGraph V} (c : V → Fin 2) {u v : V} (p : G.Walk u v)
    (hp : ∀ d ∈ p.darts, c d.fst ≠ c d.snd) : (c v).val = ((c u).val + p.length) % 2 := by
  induction p with
  | nil => simp [Nat.mod_eq_of_lt (c _).isLt]
  | @cons a b w hadj p ih =>
    have h1 := hp ⟨(a, b), hadj⟩ (by simp [Walk.darts_cons])
    have h2 := ih (fun d hd => hp d (by simp [Walk.darts_cons, hd]))
    simp only [Walk.length_cons]
    have ha := (c a).isLt
    have hb := (c b).isLt
    have hne : (c a).val ≠ (c b).val := fun h => h1 (Fin.ext h)
    omega

lemma not_odd_of_coloring {G : SimpleGraph V} (c : V → Fin 2) {v : V} (p : G.Walk v v)
    (hp : ∀ d ∈ p.darts, c d.fst ≠ c d.snd) : ¬ Odd p.length := by
  intro hodd
  have h := walk_color_parity c p hp
  obtain ⟨k, hk⟩ := hodd
  have := (c v).isLt
  omega

theorem cover_or_obstruction (G : SimpleGraph V) (L j : ℕ) :
    (∃ F : Finset (Sym2 V), F.card ≤ j ∧ HitsShortOdd G (F : Set (Sym2 V)) L) ∨
    (∃ A : G.Subgraph, A.verts.Finite ∧ A.verts.ncard ≤ (L + 1) ^ (j + 1) ∧
      ∀ E : Set (Sym2 V), E ⊆ A.edgeSet → (A.deleteEdges E).coe.Colorable 2 → j < E.ncard) := by
  classical
  let Ed : (Σ v : V, G.Walk v v) → Finset (Sym2 V) := fun p => p.2.edges.toFinset
  let S : Set (Σ v : V, G.Walk v v) := {p | Odd p.2.length ∧ p.2.length ≤ L}
  have hS : ∀ p ∈ S, (Ed p).Nonempty ∧ (Ed p).card ≤ L := by
    rintro ⟨v, w⟩ ⟨hodd, hlen⟩
    constructor
    · have hne : w.edges ≠ [] := by
        intro h
        have h0 : w.length = 0 := by rw [← Walk.length_edges, h]; rfl
        rw [h0] at hodd
        exact Nat.not_odd_zero hodd
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨e, List.mem_toFinset.mpr he⟩
    · calc (Ed ⟨v, w⟩).card ≤ w.edges.length := List.toFinset_card_le _
        _ = w.length := Walk.length_edges _
        _ ≤ L := hlen
  rcases cover_abstract L Ed j S hS with ⟨F, hF, hcov⟩ | ⟨D, hDS, hDcard, hDnc⟩
  · left
    refine ⟨F, hF, ?_⟩
    intro v w hodd hlen
    have := hcov ⟨v, w⟩ ⟨hodd, hlen⟩
    rw [Finset.not_disjoint_iff] at this
    obtain ⟨e, heF, hew⟩ := this
    exact ⟨e, List.mem_toFinset.mp hew, heF⟩
  · right
    let A : G.Subgraph :=
      { verts := ↑(D.biUnion (fun p => p.2.support.toFinset))
        Adj := fun a b => ∃ p ∈ D, s(a, b) ∈ p.2.edges
        adj_sub := by
          rintro a b ⟨p, -, hp⟩
          exact p.2.adj_of_mem_edges hp
        edge_vert := by
          rintro a b ⟨p, hpD, hp⟩
          simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, List.coe_toFinset,
            Set.mem_setOf_eq]
          exact ⟨p, hpD, p.2.fst_mem_support_of_mem_edges hp⟩
        symm := by
          rintro a b ⟨p, hpD, hp⟩
          exact ⟨p, hpD, by rwa [Sym2.eq_swap]⟩ }
    have hAe : ∀ e, e ∈ A.edgeSet ↔ ∃ p ∈ D, e ∈ p.2.edges := by
      intro e
      induction e using Sym2.ind with
      | h a b => rw [Subgraph.mem_edgeSet]
    refine ⟨A, Finset.finite_toSet _, ?_, ?_⟩
    · show (↑(D.biUnion (fun p => p.2.support.toFinset)) : Set V).ncard ≤ (L + 1) ^ (j + 1)
      rw [Set.ncard_coe_finset]
      calc (D.biUnion (fun p => p.2.support.toFinset)).card
          ≤ ∑ p ∈ D, p.2.support.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ D, (L + 1) := by
            gcongr with p hp
            calc p.2.support.toFinset.card ≤ p.2.support.length := List.toFinset_card_le _
              _ = p.2.length + 1 := Walk.length_support _
              _ ≤ L + 1 := by have := (hDS hp).2; omega
        _ = D.card * (L + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (L + 1) ^ j * (L + 1) := by gcongr
        _ = (L + 1) ^ (j + 1) := (pow_succ _ _).symm
    · intro E hE ⟨col⟩
      by_contra hlt
      push_neg at hlt
      have hEfin : E.Finite := by
        apply Set.Finite.subset (Finset.finite_toSet (D.biUnion (fun p => p.2.edges.toFinset)))
        intro e he
        obtain ⟨p, hpD, hp⟩ := (hAe e).mp (hE he)
        simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, List.coe_toFinset,
          Set.mem_setOf_eq]
        exact ⟨p, hpD, hp⟩
      have hFcard : hEfin.toFinset.card ≤ j := by
        rw [← Set.ncard_eq_toFinset_card E hEfin]; exact hlt
      obtain ⟨p, hpD, hdis⟩ := hDnc hEfin.toFinset hFcard
      let c : V → Fin 2 := fun v => if h : v ∈ (A.deleteEdges E).verts then col ⟨v, h⟩ else 0
      apply not_odd_of_coloring c p.2 _ (hDS hpD).1
      intro d hd
      have hde : s(d.fst, d.snd) ∈ p.2.edges := List.mem_map_of_mem hd
      have hadj : (A.deleteEdges E).Adj d.fst d.snd := by
        rw [Subgraph.deleteEdges_adj]
        refine ⟨⟨p, hpD, hde⟩, fun hmem => ?_⟩
        rw [Finset.disjoint_left] at hdis
        exact hdis (hEfin.mem_toFinset.mpr hmem) (List.mem_toFinset.mpr hde)
      have h1 := (A.deleteEdges E).edge_vert hadj
      have h2 := (A.deleteEdges E).edge_vert hadj.symm
      simp only [c, h1, h2, dif_pos]
      exact col.valid (by rw [Subgraph.coe_adj]; exact hadj)

end Erdos74Aux
