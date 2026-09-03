import FormalConjecturesUtil
import Submission.CompactExactUnionAudit

/-! Extremal bounds for several internally disjoint paths of length three. -/

open Filter SimpleGraph Asymptotics Finset

namespace Erdos713Theta3
open Erdos713C6 Finset

abbrev Vertex (t : ℕ) := Option (Fin t) ⊕ Option (Fin t)

def Rel {t : ℕ} : Option (Fin t) → Option (Fin t) → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some i, some j => i = j

abbrev theta (t : ℕ) : SimpleGraph (Vertex t) := bipGraph (Rel (t := t))

lemma option_injective {I V : Type*} (v : V) (f : I → V) (hf : Function.Injective f)
    (hv : ∀ i, v ≠ f i) : Function.Injective (fun x : Option I => x.elim v f) := by
  rintro (i | i) (j | j) h
  · rfl
  · exact (hv j h).elim
  · exact (hv i h.symm).elim
  · exact congrArg some (hf h)

lemma contained_of_paths {V : Type*} (G : SimpleGraph V) {t : ℕ}
    (u v : V) (a b : Fin t → V) (ha : Function.Injective a) (hb : Function.Injective b)
    (huv : u ≠ v) (hub : ∀ i, u ≠ b i) (hva : ∀ i, v ≠ a i)
    (hba : ∀ i j, b i ≠ a j)
    (h0 : ∀ i, G.Adj u (a i)) (h1 : ∀ i, G.Adj (a i) (b i)) (h2 : ∀ i, G.Adj (b i) v) :
    theta t ⊑ G := by
  let left : Option (Fin t) → V := fun x => x.elim u b
  let right : Option (Fin t) → V := fun x => x.elim v a
  have hleft : Function.Injective left := option_injective u b hb hub
  have hright : Function.Injective right := option_injective v a ha hva
  have hDis (i j : Option (Fin t)) : left i ≠ right j := by
    cases i with
    | none =>
      cases j with
      | none => exact huv
      | some j => exact (h0 j).ne
    | some i =>
      cases j with
      | none => exact (h2 i).ne
      | some j => exact hba i j
  have hLR (i j : Option (Fin t)) (hij : Rel i j) : G.Adj (left i) (right j) := by
    cases i with
    | none =>
      cases j with
      | none => exact hij.elim
      | some j => exact h0 j
    | some i =>
      cases j with
      | none => exact h2 i
      | some j =>
        change i = j at hij
        subst j
        exact (h1 i).symm
  refine ⟨⟨⟨Sum.elim left right, ?_⟩, ?_⟩⟩
  · rintro (i | i) (j | j) hij
    · exact hij.elim
    · exact hLR i j hij
    · exact (hLR j i hij).symm
    · exact hij.elim
  · rintro (i | i) (j | j) hij
    · exact congrArg Sum.inl (hleft hij)
    · exact (hDis i j hij).elim
    · exact (hDis j i hij.symm).elim
    · exact congrArg Sum.inr (hright hij)

lemma distinct_representatives {I V : Type*} [Fintype I] (S : I → Finset V)
    (hS : ∀ i, Fintype.card I ≤ (S i).card) :
    ∃ f : I → V, Function.Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  apply (all_card_le_biUnion_card_iff_exists_injective S).mp
  intro U
  rcases U.eq_empty_or_nonempty with rfl | hU
  · simp
  obtain ⟨i, hi⟩ := hU
  exact (card_le_univ U).trans ((hS i).trans (card_le_card (subset_biUnion_of_mem S hi)))

open scoped Classical in
lemma contained_of_rooted_bipartite {V : Type*} [Fintype V]
    (G K : SimpleGraph V) (hKG : K ≤ G) {A B : Finset V} (hBip : K.IsBipartiteWith A B)
    (root c : V) (hrootA : root ∉ A) (hrootB : root ∉ B) (hc : c ∈ A)
    (hRoot : ∀ a ∈ A, G.Adj root a) (t : ℕ) (hdc : t ≤ K.degree c)
    (hD : ∀ b, K.Adj c b → t + 1 ≤ K.degree b) : theta t ⊑ G := by
  classical
  obtain ⟨b, hb⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin t) ≤ (K.neighborFinset c).card by simpa using hdc)
  have hbAdj (i : Fin t) : K.Adj c (b i) := (mem_neighborFinset K c _).mp (hb ⟨i, rfl⟩)
  have hbB (i : Fin t) : b i ∈ B := hBip.mem_of_mem_adj hc (hbAdj i)
  let S : Fin t → Finset V := fun i => (K.neighborFinset (b i)).erase c
  have hS (i : Fin t) : Fintype.card (Fin t) ≤ (S i).card := by
    have hh := hD (b i) (hbAdj i)
    have hcMem : c ∈ K.neighborFinset (b i) := (mem_neighborFinset K _ _).mpr (hbAdj i).symm
    simp only [S, Fintype.card_fin, card_erase_of_mem hcMem, card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, ha, haS⟩ := distinct_representatives S hS
  have haAdj (i : Fin t) : K.Adj (b i) (a i) :=
    (mem_neighborFinset K _ _).mp (mem_of_mem_erase (haS i))
  have haA (i : Fin t) : a i ∈ A := hBip.symm.mem_of_mem_adj (hbB i) (haAdj i)
  apply contained_of_paths G root c a b ha b.injective
  · intro he; exact hrootA (he ▸ hc)
  · intro i he; exact hrootB (he ▸ hbB i)
  · intro i he; exact (mem_erase.mp (haS i)).1 he.symm
  · intro i j he
    exact Set.disjoint_left.mp hBip.disjoint (haA j) (he ▸ hbB i)
  · intro i; exact hRoot (a i) (haA i)
  · intro i; exact hKG (haAdj i).symm
  · intro i; exact hKG (hbAdj i).symm

theorem exists_support_pruned {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) :
    ∃ K : SimpleGraph V, K ≤ G ∧
      (∀ v, Nat.card (K.neighborSet v) = 0 ∨ d ≤ Nat.card (K.neighborSet v)) ∧
      Nat.card G.edgeSet ≤ Nat.card K.edgeSet + d * Nat.card G.support := by
  classical
  let S : Finset (SimpleGraph V) := {K | K ≤ G}
  let weight : SimpleGraph V → ℤ := fun K =>
    (Nat.card K.edgeSet : ℤ) - (d : ℤ) * Nat.card K.support
  obtain ⟨K, hKS, hmax⟩ := exists_max_image S weight
    (show S.Nonempty from ⟨G, by simp [S]⟩)
  have hKG : K ≤ G := by simpa [S] using hKS
  refine ⟨K, hKG, ?_, ?_⟩
  · intro v
    by_cases hd : d ≤ Nat.card (K.neighborSet v)
    · exact Or.inr hd
    left
    by_contra hz
    have hpos : 0 < K.degree v := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using Nat.pos_of_ne_zero hz
    have hlt : K.degree v < d := by
      simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using Nat.lt_of_not_ge hd
    have hv : v ∈ K.support := (K.degree_pos_iff_mem_support v).mp hpos
    have hDel : K.deleteIncidenceSet v ∈ S := by
      simpa [S] using (K.deleteIncidenceSet_le v).trans hKG
    have hm := hmax (K.deleteIncidenceSet v) hDel
    dsimp only [weight] at hm
    have he : Nat.card (K.deleteIncidenceSet v).edgeSet + K.degree v = Nat.card K.edgeSet := by
      simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card,
        card_edgeFinset_deleteIncidenceSet] using
        Nat.sub_add_cancel (K.degree_le_card_edgeFinset v)
    have hs : Nat.card (K.deleteIncidenceSet v).support + 1 ≤ Nat.card K.support := by
      have hb := K.card_support_deleteIncidenceSet hv
      have hp : 0 < Fintype.card K.support := Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
      have hh : Fintype.card (K.deleteIncidenceSet v).support + 1 ≤ Fintype.card K.support := by omega
      simpa only [Nat.card_eq_fintype_card] using hh
    have hei : (Nat.card (K.deleteIncidenceSet v).edgeSet : ℤ) + K.degree v =
        (Nat.card K.edgeSet : ℤ) := by exact_mod_cast he
    have hsi : (Nat.card (K.deleteIncidenceSet v).support : ℤ) + 1 ≤
        (Nat.card K.support : ℤ) := by exact_mod_cast hs
    have hlti : (K.degree v : ℤ) < (d : ℤ) := by exact_mod_cast hlt
    have hmul := mul_le_mul_of_nonneg_left hsi (Int.natCast_nonneg d)
    nlinarith
  · have hm := hmax G (by simp [S])
    dsimp only [weight] at hm
    have hprod : 0 ≤ (d : ℤ) * Nat.card K.support := by positivity
    have hb : (Nat.card G.edgeSet : ℤ) ≤
        (Nat.card K.edgeSet : ℤ) + (d : ℤ) * Nat.card G.support := by nlinarith
    exact_mod_cast hb

open scoped Classical in
lemma rooted_edge_bound {V : Type*} [Fintype V] (G K : SimpleGraph V) (hKG : K ≤ G)
    {A B : Finset V} (hBip : K.IsBipartiteWith A B) (root : V)
    (hrootA : root ∉ A) (hrootB : root ∉ B) (hRoot : ∀ a ∈ A, G.Adj root a)
    (t : ℕ) (hFree : (theta t).Free G) :
    K.edgeFinset.card ≤ (t + 1) * (A.card + B.card) := by
  classical
  obtain ⟨Q, hQK, hDeg, hBound⟩ := exists_support_pruned K (t + 1)
  have hQ : Q = ⊥ := by
    by_contra hQ
    obtain ⟨u, v, huv⟩ := ne_bot_iff_exists_adj.mp hQ
    have hBipQ : Q.IsBipartiteWith A B := ⟨hBip.disjoint, by intro u v h; exact hBip.mem_of_adj (hQK h)⟩
    have hD {a b : V} (hab : Q.Adj a b) : t + 1 ≤ Q.degree a := by
      rcases hDeg a with hz | hd
      · have hp : 0 < Q.degree a := hab.degree_pos_left
        rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hz
        omega
      · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hd
    obtain ⟨c, hc, w, hcw⟩ : ∃ c ∈ A, ∃ w, Q.Adj c w := by
      rcases hBipQ.mem_of_adj huv with ⟨hu, _⟩ | ⟨_, hv⟩
      · exact ⟨u, hu, v, huv⟩
      · exact ⟨v, hv, u, huv.symm⟩
    exact hFree (contained_of_rooted_bipartite G Q (hQK.trans hKG) hBipQ root c
      hrootA hrootB hc hRoot t (by have hh := hD hcw; omega) (fun _ h => hD h.symm))
  have hCard : Nat.card K.support ≤ A.card + B.card := by
    have hh := (Set.ncard_le_ncard (isBipartiteWith_support_subset hBip)).trans
      (Set.ncard_union_le (A : Set V) (B : Set V))
    simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hh
  rw [hQ] at hBound
  have hh : Nat.card K.edgeSet ≤ (t + 1) * Nat.card K.support := by
    simpa only [edgeSet_bot, Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty, zero_add] using hBound
  have hh' := hh.trans (Nat.mul_le_mul_left (t + 1) hCard)
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hh'

open scoped Classical in
lemma parent_count_bound {V : Type*} [Fintype V] (G K : SimpleGraph V) (hKG : K ≤ G)
    {A B C : Finset V} (hBip : K.IsBipartiteWith B C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (parent : V → V)
    (hParent : ∀ b ∈ B, parent b ∈ A ∧ G.Adj (parent b) b)
    (root : V) (hrB : root ∉ B) (hrC : root ∉ C) (hRoot : ∀ a ∈ A, G.Adj root a)
    (t : ℕ) (hFree : (theta t).Free G) (c : V) (hc : c ∈ C) :
    ((K.neighborFinset c).image parent).card ≤ t := by
  classical
  by_contra hh
  obtain ⟨a, ha⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin t) ≤ ((K.neighborFinset c).image parent).card by simpa using (by omega : t ≤ _))
  have hA (i : Fin t) : ∃ b ∈ K.neighborFinset c, parent b = a i := mem_image.mp (ha ⟨i, rfl⟩)
  choose b hb hpb using hA
  have hbAdj (i : Fin t) : K.Adj c (b i) := (mem_neighborFinset K c _).mp (hb i)
  have hbB (i : Fin t) : b i ∈ B := hBip.symm.mem_of_mem_adj hc (hbAdj i)
  have haA (i : Fin t) : a i ∈ A := by rw [← hpb i]; exact (hParent (b i) (hbB i)).1
  have hbinj : Function.Injective b := by
    intro i j hij
    apply a.injective
    rw [← hpb i, ← hpb j, hij]
  apply hFree
  apply contained_of_paths G root c a b a.injective hbinj
  · intro he; exact hrC (he ▸ hc)
  · intro i he; exact hrB (he ▸ hbB i)
  · intro i he; exact Finset.disjoint_left.mp hAC (haA i) (he ▸ hc)
  · intro i j he; exact Finset.disjoint_left.mp hAB (haA j) (he ▸ hbB i)
  · intro i; exact hRoot (a i) (haA i)
  · intro i
    have hh := (hParent (b i) (hbB i)).2
    simpa only [hpb i] using hh
  · intro i; exact hKG (hbAdj i).symm

open scoped Classical in
noncomputable def fiberNeighbors {V : Type*} [Fintype V] (K : SimpleGraph V)
    (parent : V → V) (c a : V) : Finset V := (K.neighborFinset c).filter (fun b => parent b = a)

open scoped Classical in
noncomputable def heavyNeighbors {V : Type*} [Fintype V] (K : SimpleGraph V)
    (parent : V → V) (t : ℕ) (b : V) : Finset V :=
  (K.neighborFinset b).filter (fun c => t + 1 ≤ (fiberNeighbors K parent c (parent b)).card)

open scoped Classical in
lemma heavy_neighbors_bound {V : Type*} [Fintype V] (G K : SimpleGraph V) (hKG : K ≤ G)
    {A B C : Finset V} (hBip : K.IsBipartiteWith B C) (hAC : Disjoint A C)
    (parent : V → V) (hParent : ∀ b ∈ B, parent b ∈ A ∧ G.Adj (parent b) b)
    (t : ℕ) (hFree : (theta t).Free G) (b₀ : V) (hb₀ : b₀ ∈ B) :
    (heavyNeighbors K parent t b₀).card ≤ t := by
  classical
  by_contra hh
  obtain ⟨c, hc⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin t) ≤ (heavyNeighbors K parent t b₀).card by simpa using (by omega : t ≤ _))
  have hData (i : Fin t) : K.Adj b₀ (c i) ∧
      t + 1 ≤ (fiberNeighbors K parent (c i) (parent b₀)).card := by
    simpa only [heavyNeighbors, Finset.mem_coe, mem_filter, mem_neighborFinset] using hc ⟨i, rfl⟩
  have hcC (i : Fin t) : c i ∈ C := hBip.mem_of_mem_adj hb₀ (hData i).1
  let S : Fin t → Finset V := fun i => (fiberNeighbors K parent (c i) (parent b₀)).erase b₀
  have hS (i : Fin t) : Fintype.card (Fin t) ≤ (S i).card := by
    have hh := (hData i).2
    have he : (fiberNeighbors K parent (c i) (parent b₀)).card - 1 ≤ (S i).card :=
      pred_card_le_card_erase
    simp only [Fintype.card_fin]
    omega
  obtain ⟨b, hb, hbS⟩ := distinct_representatives S hS
  have hbData (i : Fin t) : K.Adj (c i) (b i) ∧ parent (b i) = parent b₀ := by
    simpa only [fiberNeighbors, mem_filter, mem_neighborFinset] using mem_of_mem_erase (hbS i)
  have hbB (i : Fin t) : b i ∈ B := hBip.symm.mem_of_mem_adj (hcC i) (hbData i).1
  apply hFree
  apply contained_of_paths G (parent b₀) b₀ b c hb c.injective
  · exact (hParent b₀ hb₀).2.ne
  · intro i he
    exact Finset.disjoint_left.mp hAC (hParent b₀ hb₀).1 (he ▸ hcC i)
  · intro i he
    exact (mem_erase.mp (hbS i)).1 he.symm
  · intro i j he
    exact Set.disjoint_left.mp hBip.disjoint (hbB j) (he ▸ hcC i)
  · intro i
    have hh := (hParent (b i) (hbB i)).2
    simpa only [(hbData i).2] using hh
  · intro i; exact hKG (hbData i).1.symm
  · intro i; exact hKG (hData i).1.symm

lemma weak_fibers_card_le {V A : Type*} (S : Finset V) (parent : V → A) [DecidableEq A]
    (t : ℕ) :
    (S.filter (fun b => (S.filter (fun x => parent x = parent b)).card ≤ t)).card ≤
      (S.image parent).card * t := by
  classical
  let W := S.filter (fun b => (S.filter (fun x => parent x = parent b)).card ≤ t)
  have hMap : Set.MapsTo parent (↑W) (↑(S.image parent)) := by
    intro b hb
    exact mem_image_of_mem parent (mem_filter.mp hb).1
  have hF (a : A) : (W.filter (fun b => parent b = a)).card ≤ t := by
    by_cases hE : (W.filter (fun b => parent b = a)).Nonempty
    · obtain ⟨b, hb⟩ := hE
      have hbW := (mem_filter.mp hb).1
      have hba := (mem_filter.mp hb).2
      have hh := (mem_filter.mp hbW).2
      rw [hba] at hh
      exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans hh
    · rw [not_nonempty_iff_eq_empty.mp hE]
      simp
  change W.card ≤ _
  rw [card_eq_sum_card_fiberwise hMap]
  calc
    ∑ a ∈ S.image parent, (W.filter (fun b => parent b = a)).card ≤ ∑ _a ∈ S.image parent, t :=
      sum_le_sum (fun a _ => hF a)
    _ = (S.image parent).card * t := by simp

open scoped Classical in
lemma parented_edge_bound {V : Type*} [Fintype V] (G K : SimpleGraph V) (hKG : K ≤ G)
    {A B C : Finset V} (hBip : K.IsBipartiteWith B C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (parent : V → V)
    (hParent : ∀ b ∈ B, parent b ∈ A ∧ G.Adj (parent b) b)
    (root : V) (hrB : root ∉ B) (hrC : root ∉ C) (hRoot : ∀ a ∈ A, G.Adj root a)
    (t : ℕ) (hFree : (theta t).Free G) :
    K.edgeFinset.card ≤ t * B.card + t ^ 2 * C.card := by
  classical
  let rel : V → V → Prop := fun b c => K.Adj b c ∧ (fiberNeighbors K parent c (parent b)).card ≤ t
  have hBelow (c : V) (hc : c ∈ C) : (B.bipartiteBelow rel c).card ≤ t ^ 2 := by
    have hEq : B.bipartiteBelow rel c = (K.neighborFinset c).filter
        (fun b => (fiberNeighbors K parent c (parent b)).card ≤ t) := by
      ext b
      simp only [mem_bipartiteBelow, mem_filter, mem_neighborFinset, rel]
      constructor
      · rintro ⟨_, hbc, hh⟩
        exact ⟨hbc.symm, hh⟩
      · rintro ⟨hcb, hh⟩
        exact ⟨hBip.symm.mem_of_mem_adj hc hcb, hcb.symm, hh⟩
    rw [hEq]
    have hWeak := weak_fibers_card_le (K.neighborFinset c) parent t
    have hP := parent_count_bound G K hKG hBip hAB hAC parent hParent root hrB hrC hRoot t hFree c hc
    have hh := hWeak.trans (Nat.mul_le_mul_right t hP)
    simpa only [fiberNeighbors, pow_two] using hh
  have hRow (b : V) (hb : b ∈ B) : K.degree b ≤ t + (C.bipartiteAbove rel b).card := by
    have hSub : K.neighborFinset b ⊆ heavyNeighbors K parent t b ∪ C.bipartiteAbove rel b := by
      intro c hc
      have hbc : K.Adj b c := (mem_neighborFinset K b c).mp hc
      have hcC : c ∈ C := hBip.mem_of_mem_adj hb hbc
      by_cases hh : t + 1 ≤ (fiberNeighbors K parent c (parent b)).card
      · exact mem_union_left _ (mem_filter.mpr ⟨hc, hh⟩)
      · apply mem_union_right
        exact (mem_bipartiteAbove rel).mpr ⟨hcC, hbc, by omega⟩
    have hh := (card_le_card hSub).trans (card_union_le _ _)
    rw [card_neighborFinset_eq_degree] at hh
    exact hh.trans (Nat.add_le_add_right
      (heavy_neighbors_bound G K hKG hBip hAC parent hParent t hFree b hb) _)
  have hs := sum_le_sum (s := B) (fun b hb => hRow b hb)
  rw [isBipartiteWith_sum_degrees_eq_card_edges hBip, sum_add_distrib] at hs
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (r := rel) (s := B) (t := C)] at hs
  have hw := sum_le_sum (s := C) (fun c hc => hBelow c hc)
  simp only [sum_const, Nat.nsmul_eq_mul] at hs hw
  nlinarith only [hs, hw]

lemma three_level_degree_cube {d M A B C N : ℕ} (hN : 1 ≤ N) (hA : d ≤ A)
    (hAC : A + C ≤ N) (h1 : d * A ≤ A + M * (A + B))
    (h2 : d * B ≤ M * (A + B) + M * (B + C)) :
    d ^ 3 ≤ (4 * (M + 1)) ^ 3 * N := by
  by_cases hd : d ≤ 4 * (M + 1)
  · exact (Nat.pow_le_pow_left hd 3).trans (Nat.le_mul_of_pos_right _ hN)
  have hd1 : 2 * (M + 1) ≤ d := by omega
  have hd2 : 4 * M ≤ d := by omega
  have hg1 : d * A ≤ 2 * M * B := by
    have hh := Nat.mul_le_mul_right A hd1
    nlinarith only [h1, hh]
  have hg2 : d * B ≤ 2 * M * N := by
    have hh := Nat.mul_le_mul_right B hd2
    have hh' := Nat.mul_le_mul_left M hAC
    nlinarith only [h2, hh, hh']
  have hdSq : d ^ 2 ≤ 2 * M * B := by
    have hh := Nat.mul_le_mul_left d hA
    nlinarith only [hg1, hh]
  have hdCube : d ^ 3 ≤ 4 * M ^ 2 * N := by
    have hh := Nat.mul_le_mul_left d hdSq
    have hh' := Nat.mul_le_mul_left (2 * M) hg2
    nlinarith only [hh, hh']
  have hC : 4 * M ^ 2 ≤ (4 * (M + 1)) ^ 3 := by nlinarith [sq_nonneg (M : ℤ)]
  exact hdCube.trans (Nat.mul_le_mul_right N hC)

open scoped Classical in
lemma connected_degree_cube {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hBip : G.IsBipartite) (t d : ℕ) (hFree : (theta t).Free G)
    (hDeg : ∀ v, d ≤ G.degree v) :
    d ^ 3 ≤ (4 * ((t + 1) ^ 2 + 1)) ^ 3 * Fintype.card V := by
  classical
  let root : V := hconn.nonempty.some
  let L := Erdos713BreadthFirst.Layering.ofConnected G hconn root
  let A := L.levelFinset 1
  let B := L.levelFinset 2
  let C := L.levelFinset 3
  have hStep : ∀ u v, G.Adj u v → L.level u + 1 = L.level v ∨ L.level v + 1 = L.level u :=
    fun _ _ h => Erdos713BreadthFirst.adj_dist_diff_one hconn hBip root h
  have hRootZero : L.level root = 0 := (L.zero_iff root).mpr rfl
  have hRootA : root ∉ A := by intro hh; have hh' := (L.mem_levelFinset root 1).mp hh; omega
  have hRootB : root ∉ B := by intro hh; have hh' := (L.mem_levelFinset root 2).mp hh; omega
  have hRootC : root ∉ C := by intro hh; have hh' := (L.mem_levelFinset root 3).mp hh; omega
  have hRoot (a : V) (ha : a ∈ A) : G.Adj root a := by
    have hla : L.level a = 1 := (L.mem_levelFinset a 1).mp ha
    have ha' : a ≠ root := by intro hh; rw [hh, hRootZero] at hla; omega
    have hp := L.parent_level a ha'
    have hp' : L.parent a = root := (L.zero_iff _).mp (by omega)
    simpa only [hp'] using (L.parent_adj a ha').symm
  have hParent (b : V) (hb : b ∈ B) : L.parent b ∈ A ∧ G.Adj (L.parent b) b := by
    have hlb : L.level b = 2 := (L.mem_levelFinset b 2).mp hb
    have hb' : b ≠ root := by intro hh; rw [hh, hRootZero] at hlb; omega
    have hp := L.parent_level b hb'
    exact ⟨(L.mem_levelFinset _ 1).mpr (by omega), (L.parent_adj b hb').symm⟩
  have hAB : Disjoint A B := L.levelFinset_disjoint (by decide)
  have hAC : Disjoint A C := L.levelFinset_disjoint (by decide)
  have heAB : (L.between 1).edgeFinset.card ≤ (t + 1) * (A.card + B.card) :=
    rooted_edge_bound G (L.between 1) (L.between_le 1) (L.between_bipartite 1)
      root hRootA hRootB hRoot t hFree
  have heBC : (L.between 2).edgeFinset.card ≤ t * B.card + t ^ 2 * C.card :=
    parented_edge_bound G (L.between 2) (L.between_le 2) (L.between_bipartite 2)
      hAB hAC L.parent hParent root hRootB hRootC hRoot t hFree
  have heZero : (L.between 0).edgeFinset.card ≤ A.card := by
    have hh := isBipartiteWith_sum_degrees_eq_card_edges (L.between_bipartite 0)
    rw [L.levelFinset_zero, sum_singleton] at hh
    rw [← hh, ← L.degree_root_eq_card_level_one hStep]
    exact (L.between 0).degree_le_of_le (L.between_le 0)
  have hA : d ≤ A.card := by
    have hh := hDeg root
    rwa [L.degree_root_eq_card_level_one hStep] at hh
  have hACn : A.card + C.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hAC]
    exact card_le_univ _
  have hCoeff : t + 1 ≤ (t + 1) ^ 2 := by nlinarith
  have hCoeff' : t ≤ (t + 1) ^ 2 := by nlinarith
  have hCoeff'' : t ^ 2 ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have heAB' := heAB.trans (Nat.mul_le_mul_right (A.card + B.card) hCoeff)
  have heBC' : (L.between 2).edgeFinset.card ≤ (t + 1) ^ 2 * (B.card + C.card) := by
    have hh := Nat.mul_le_mul_right B.card hCoeff'
    have hh' := Nat.mul_le_mul_right C.card hCoeff''
    nlinarith only [heBC, hh, hh']
  apply three_level_degree_cube (Fintype.card_pos_iff.mpr ⟨root⟩) hA hACn
  · exact (L.layer_degree_sum d 0 hDeg hStep).trans (Nat.add_le_add heZero heAB')
  · exact (L.layer_degree_sum d 1 hDeg hStep).trans (Nat.add_le_add heAB' heBC')

open scoped Classical in
lemma degree_cube {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hBip : G.IsBipartite) (t d : ℕ)
    (hFree : (theta t).Free G)
    (hDeg : ∀ u v, G.Adj u v → d ≤ G.degree u) {u v : V} (huv : G.Adj u v) :
    d ^ 3 ≤ (4 * ((t + 1) ^ 2 + 1)) ^ 3 * Fintype.card V := by
  classical
  let C := G.connectedComponentMk u
  have hu : u ∈ C.supp := rfl
  have hSupp : C.supp ⊆ G.support := by
    intro w hw
    by_cases hwu : w = u
    · subst w; exact ⟨v, huv⟩
    · exact mem_support_of_reachable hwu (C.reachable_of_mem_supp hw hu)
  let H := G.induce C.supp
  have hCDeg (w : ↥C.supp) : d ≤ H.degree w := by
    have hSub : G.neighborSet w.val ⊆ C.supp := by
      intro z hz
      exact C.mem_supp_of_adj_mem_supp w.prop hz
    have heq : H.degree w = G.degree w.val := degree_induce_of_neighborSet_subset hSub
    rw [heq]
    obtain ⟨z, hwz⟩ := hSupp w.prop
    exact hDeg w.val z hwz
  have hCFree : (theta t).Free H :=
    fun hc => hFree (hc.trans ⟨Copy.induce G C.supp⟩)
  have hh := connected_degree_cube H C.connected_toSimpleGraph
    (Colorable.of_hom (Copy.induce G C.supp).toHom hBip) t d hCFree hCDeg
  exact hh.trans (Nat.mul_le_mul_left _ (Fintype.card_subtype_le (· ∈ C.supp)))


open scoped Classical in
theorem bipartite_edge_cube_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hBip : G.IsBipartite) (t : ℕ) (hfree : (theta t).Free G) :
    G.edgeFinset.card ^ 3 ≤ (64 * ((4 * ((t + 1) ^ 2 + 1)) ^ 3 + 1)) * Fintype.card V ^ 4 := by
  classical
  let e := G.edgeFinset.card
  let n := Fintype.card V
  by_cases he : e = 0
  · change e ^ 3 ≤ _
    simp [he]
  have hGne : G ≠ ⊥ := by
    intro hG
    apply he
    exact congrArg Finset.card (edgeFinset_eq_empty.mpr hG)
  obtain ⟨u, v, huv⟩ := ne_bot_iff_exists_adj.mp hGne
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨u⟩
  let d := e / (2 * n)
  have hdiv : d * (2 * n) ≤ e := Nat.div_mul_le_self e (2 * n)
  obtain ⟨K, hKG, hd, hbound⟩ := Erdos713Leaf.exists_pruned G d
  have hKne : K ≠ ⊥ := by
    intro hK
    have hB : e ≤ d * n := by
      simpa only [hK, edgeSet_bot, Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty,
        zero_add, ← edgeFinset_card] using hbound
    nlinarith only [hB, hdiv, Nat.pos_of_ne_zero he]
  obtain ⟨x, y, hxy⟩ := ne_bot_iff_exists_adj.mp hKne
  have hKBip : K.IsBipartite := Colorable.of_hom (Copy.ofLE K G hKG).toHom hBip
  have hKfree : (theta t).Free K := fun hc => hfree (hc.mono_right hKG)
  have hd' (x y : V) (hxy : K.Adj x y) : d ≤ K.degree x := by
    rcases hd x with hz | hb
    · have hpos : 0 < K.degree x := hxy.degree_pos_left
      rw [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hz
      omega
    · simpa only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] using hb
  have hd3 : d ^ 3 ≤ (4 * ((t + 1) ^ 2 + 1)) ^ 3 * n := degree_cube K hKBip t d hKfree hd' hxy
  have heUpper : e ≤ 2 * n * (d + 1) :=
    (Nat.lt_mul_div_succ e (by omega : 0 < 2 * n)).le
  have hdAdd : (d + 1) ^ 3 ≤ 8 * (d ^ 3 + 1) := by
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hle : d + 1 ≤ 2 * d := by omega
      have hh := Nat.pow_le_pow_left hle 3
      nlinarith only [hh]
  have he3 : e ^ 3 ≤ 8 * n ^ 3 * (d + 1) ^ 3 := by
    have hh := Nat.pow_le_pow_left heUpper 3
    nlinarith only [hh]
  have hm1 := Nat.mul_le_mul_left (8 * n ^ 3) hdAdd
  have hm2 := Nat.mul_le_mul_left (64 * n ^ 3) (Nat.add_le_add_right hd3 1)
  have hm3 := Nat.mul_le_mul_left (64 * n ^ 3)
    (show (4 * ((t + 1) ^ 2 + 1)) ^ 3 * n + 1 ≤ ((4 * ((t + 1) ^ 2 + 1)) ^ 3 + 1) * n by nlinarith)
  change e ^ 3 ≤ (64 * ((4 * ((t + 1) ^ 2 + 1)) ^ 3 + 1)) * n ^ 4
  nlinarith only [he3, hm1, hm2, hm3]


open scoped Classical in
theorem edge_cube_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ℕ) (hfree : (theta t).Free G) :
    G.edgeFinset.card ^ 3 ≤ (512 * ((4 * ((t + 1) ^ 2 + 1)) ^ 3 + 1)) * Fintype.card V ^ 4 := by
  classical
  obtain ⟨K, hKG, hKBip, hhalf⟩ := Erdos713Cut.exists_bipartite_half G
  have hKfree : (theta t).Free K := fun hc => hfree (hc.mono_right hKG)
  have hb := bipartite_edge_cube_le K hKBip t hKfree
  have hp := Nat.pow_le_pow_left hhalf 3
  nlinarith only [hb, hp]

theorem extremal_cube_le (t n : ℕ) :
    (extremalNumber n (theta t)) ^ 3 ≤ (512 * ((4 * ((t + 1) ^ 2 + 1)) ^ 3 + 1)) * n ^ 4 := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | (theta t).Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ 3 ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : (theta t).Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using edge_cube_le G t hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp


theorem upper (t : ℕ) :
    (fun n : ℕ => (extremalNumber n (theta t) : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ) / 3)) := by
  simpa only [Nat.cast_ofNat] using Erdos713Rate.upper_of_power_bound (by decide : 3 ≠ 0)
    (extremal_cube_le t)

lemma c6_contained {t : ℕ} (ht : 2 ≤ t) : Erdos713C6.C6 ⊑ theta t := by
  let i0 : Fin t := ⟨0, by omega⟩
  let i1 : Fin t := ⟨1, by omega⟩
  have hij : i0 ≠ i1 := by intro h; have hh := congrArg Fin.val h; norm_num [i0, i1] at hh
  apply Erdos713C6.contained_of_hexagon (theta t)
    ![Sum.inl none, Sum.inl (some i0), Sum.inl (some i1)]
    ![Sum.inr (some i0), Sum.inr none, Sum.inr (some i1)]
  · apply Erdos713C6.injective_triple <;> simp [hij]
  · apply Erdos713C6.injective_triple <;> simp [hij]
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i; fin_cases i <;> simp [theta, bipGraph, Rel]
  · intro i; fin_cases i <;> simp [theta, bipGraph, Rel]

theorem rate_of_containment {W : Type*} {H : SimpleGraph W} {t : ℕ}
    (hlo : Erdos713C6.C6 ⊑ H) (hhi : H ⊑ theta t) : Erdos713Rate.HasRate H ((4 : ℝ) / 3) :=
  Erdos713Rate.rate_of_C6_upper hlo ((Erdos713Rate.extremal_mono_bigO hhi).trans (upper t))

theorem rate {t : ℕ} (ht : 2 ≤ t) : Erdos713Rate.HasRate (theta t) ((4 : ℝ) / 3) :=
  rate_of_containment (c6_contained ht) (IsContained.refl _)

end Erdos713Theta3

namespace Erdos713Theta3
open Erdos713RootPower Erdos713Rate

def flipIso (t : ℕ) : theta t ≃g theta t :=
  ⟨Equiv.sumComm _ _,by
    rintro (a | a) (b | b) <;> cases a <;> cases b <;>
      simp [theta,Erdos713C6.bipGraph,Rel,eq_comm]⟩

lemma connected {t : ℕ} (ht : 1 ≤ t) : (theta t).Connected := by
  let i : Fin t := ⟨0,by omega⟩
  have h₀ : (theta t).Adj (.inl (some i)) (.inr (some i)) := by
    simp [theta,Erdos713C6.bipGraph,Rel]
  have h₁ : (theta t).Adj (.inr (some i)) (.inl none) := by
    simp [theta,Erdos713C6.bipGraph,Rel]
  have h₂ : (theta t).Adj (.inl (some i)) (.inr none) := by
    simp [theta,Erdos713C6.bipGraph,Rel]
  have hN := h₀.reachable.trans h₁.reachable
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨.inl (some i),?_⟩
  rintro (a | b)
  · cases a with
    | none => exact hN
    | some a =>
      exact h₂.reachable.trans (show (theta t).Adj (.inr none) (.inl (some a)) by
        simp [theta,Erdos713C6.bipGraph,Rel]).reachable
  · cases b with
    | none => exact h₂.reachable
    | some b =>
      exact hN.trans (show (theta t).Adj (.inl none) (.inr (some b)) by
        simp [theta,Erdos713C6.bipGraph,Rel]).reachable

lemma root_bound {t : ℕ} (ht : 1 ≤ t) (x : Vertex t) :
    RootPowerBound (theta t) x ((4 : ℝ)/3) := by
  let i : Fin t := ⟨0,by omega⟩
  let y : Vertex t := .inl (some i)
  have hy : (theta t).Adj y ((flipIso t) y) := by
    simp [y,flipIso,theta,Erdos713C6.bipGraph,Rel]
  exact (of_root_shift (theta t) y (flipIso t).toCopy hy (by norm_num) (upper t)).of_reachable
    (connected ht y x)

lemma rooted_rate_of_containment {T : Type*} {J : SimpleGraph T} {t : ℕ} (ht : 1 ≤ t)
    (hlo : Erdos713C6.C6 ⊑ J) (hhi : J ⊑ theta t) : Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨f⟩ := hhi
  refine ⟨4/3,by simpa using rate_of_containment hlo ⟨f⟩,?_⟩
  intro x
  simpa using (root_bound ht (f x)).of_copy f x

def Sandwich {T : Type*} (J : SimpleGraph T) : Prop :=
  ∃ t : ℕ, 1 ≤ t ∧ Erdos713C6.C6 ⊑ J ∧ J ⊑ theta t

lemma Sandwich.rate {T : Type*} {J : SimpleGraph T} (hJ : Sandwich J) : HasRate J ((4 : ℝ)/3) := by
  obtain ⟨t,_,hlo,hhi⟩ := hJ
  exact rate_of_containment hlo hhi

lemma Sandwich.rooted_rate {T : Type*} {J : SimpleGraph T} (hJ : Sandwich J) :
    Erdos713ActualBlocks.RootedRate J := by
  obtain ⟨t,ht,hlo,hhi⟩ := hJ
  exact rooted_rate_of_containment ht hlo hhi

lemma Sandwich.rational {T : Type*} {J : SimpleGraph T} (hJ : Sandwich J)
    {α c : ℝ} (hα : 1 ≤ α) (hc : c ≠ 0)
    (h : (fun n : ℕ => (extremalNumber n J : ℝ)) ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    α ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨4/3,?_⟩
  norm_num
  exact hJ.rate.unique (rate_of_asymptotic hα hc h)

#print axioms extremal_cube_le
#print axioms rate
#print axioms connected
#print axioms root_bound
#print axioms Sandwich.rooted_rate
#print axioms Sandwich.rational
end Erdos713Theta3
