import Submission.ErdosSosHighDegree

set_option autoImplicit false

/-!
# Tree absorption across a cut, conditional on a parity kernel

Copies are injective homomorphisms, not induced embeddings.  The parity-kernel
certificate below is an explicit hypothesis: this file neither imports the
kernel construction nor `Submission.Spec`.
-/

open Finset SimpleGraph Classical

namespace TreeCutAbsorption

universe u v w

section ConnectedGrowth

variable {V : Type u} {T : SimpleGraph V}

/-- A nonempty proper vertex set of a connected graph has a boundary edge. -/
lemma exists_boundary_edge [Fintype V] (hT : T.Connected) (S : Finset V)
    (hS : S.Nonempty) (hne : S ≠ univ) :
    ∃ p ∈ S, ∃ x ∉ S, T.Adj p x := by
  by_contra! hn
  have hclosed {x y : V} (h : T.Reachable x y) : x ∈ S → y ∈ S := by
    obtain ⟨q⟩ := h
    induction q with
    | nil => exact id
    | @cons x y z hxy q ih =>
      intro hx
      exact ih (by by_contra hy; exact hn x hx y hy hxy)
  obtain ⟨r, hr⟩ := hS
  apply hne
  exact Finset.eq_univ_of_forall (fun x => hclosed (hT r x) hr)

/-- An outside vertex has at most one neighbor in a connected induced subgraph
of an acyclic graph. -/
lemma unique_attachment (hT : T.IsAcyclic) {S : Set V}
    (hS : (T.induce S).Connected) {x : V} (hx : x ∉ S)
    {p q : S} (hp : T.Adj x p.val) (hq : T.Adj x q.val) : p = q := by
  have hs : S ⊆ ({x}ᶜ : Set V) := by
    intro y hy hyx
    exact hx (hyx ▸ hy)
  have he := ErdosSosHighDegree.neighbor_eq_of_reachable_delete hT x hp hq
    ((hS p q).map (T.induceHomOfLE hs).toHom)
  exact (T.induceHomOfLE hs).injective he

/-- Adjoining a vertex adjacent to a connected set preserves connectedness. -/
lemma connected_insert [DecidableEq V] {S : Finset V}
    (hS : (T.induce (S : Set V)).Connected) {p x : V}
    (hp : p ∈ S) (hpx : T.Adj p x) :
    (T.induce ((insert x S : Finset V) : Set V)).Connected := by
  let j := T.induceHomOfLE (show (S : Set V) ⊆ ((insert x S : Finset V) : Set V) from
    fun _ hy => mem_insert_of_mem hy)
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨p, mem_insert_of_mem hp⟩, ?_⟩
  intro y
  rcases mem_insert.mp y.property with hy | hy
  · exact (show (T.induce ((insert x S : Finset V) : Set V)).Adj
      ⟨p, mem_insert_of_mem hp⟩ y from (by change T.Adj p y.val; rw [hy]; exact hpx)).reachable
  · exact (hS ⟨p, hp⟩ ⟨y.val, hy⟩).map j.toHom

end ConnectedGrowth

section ColoredGrowth

variable {V : Type u} [Fintype V] {H : Type v} [Fintype H]
    {C : Type w} [DecidableEq C] (T : SimpleGraph V) (G : SimpleGraph H)

/-- A color-constrained fresh neighbor.  The unembedded vertex of the requested
color makes the occupied part of that color strictly smaller than its demand. -/
lemma fresh_colored_neighbor (χ : V → C) (ψ : H → C) (S : Finset V)
    (f : V → H) (hf : ∀ x ∈ S, ψ (f x) = χ x) {x : V} (hx : x ∉ S)
    (s : H)
    (hdeg : (univ.filter (fun y => χ y = χ x)).card ≤
      ((G.neighborFinset s).filter (fun t => ψ t = χ x)).card) :
    ∃ t, G.Adj s t ∧ ψ t = χ x ∧ ∀ y ∈ S, f y ≠ t := by
  classical
  let D := S.filter (fun y => χ y = χ x)
  let N := (G.neighborFinset s).filter (fun t => ψ t = χ x)
  have hlt : D.card < (univ.filter (fun y => χ y = χ x)).card := by
    apply card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset_filter _ (subset_univ _), ?_⟩
    intro he
    have : x ∈ D := he.symm ▸ (by simp)
    exact hx (mem_filter.mp this).1
  have hcard : (D.image f).card < N.card :=
    (card_image_le.trans_lt hlt).trans_le hdeg
  have hnot : ¬ N ⊆ D.image f := fun h => (not_le_of_gt hcard) (card_le_card h)
  obtain ⟨t, ht, htd⟩ := Finset.not_subset.mp hnot
  have ht' := mem_filter.mp ht
  refine ⟨t, (G.mem_neighborFinset _ _).mp ht'.1, ht'.2, ?_⟩
  intro y hy he
  apply htd
  exact mem_image.mpr ⟨y, mem_filter.mpr ⟨hy, (hf y hy).symm.trans (he ▸ ht'.2)⟩, he⟩

/-- **Colored greedy extension from a connected core.** No color restriction
is imposed on edges internal to `R`.  For each edge directed towards an outside
vertex, the parent's image has at least the total demand of the child's color
many neighbors of that color.  Every initial color-preserving copy extends. -/
theorem colored_tree_extension (hT : T.IsTree) (R : Finset V)
    (hR : R.Nonempty) (hconn : (T.induce (R : Set V)).Connected)
    (χ : V → C) (ψ : H → C)
    (g : (T.induce (R : Set V)).Copy G)
    (hg : ∀ x : (R : Set V), ψ (g x) = χ x.val)
    (hdeg : ∀ p x, T.Adj p x → x ∉ R → ∀ s, ψ s = χ p →
      (univ.filter (fun y => χ y = χ x)).card ≤
        ((G.neighborFinset s).filter (fun t => ψ t = χ x)).card) :
    ∃ f : T.Copy G, (∀ x : (R : Set V), f x.val = g x) ∧
      ∀ x, ψ (f x) = χ x := by
  classical
  let good : Finset V → Prop := fun S => R ⊆ S ∧
    (T.induce (S : Set V)).Connected ∧ ∃ f : V → H,
      Set.InjOn f (S : Set V) ∧
      (∀ x ∈ S, ∀ y ∈ S, T.Adj x y → G.Adj (f x) (f y)) ∧
      (∀ x ∈ S, ψ (f x) = χ x) ∧
      ∀ x : (R : Set V), f x.val = g x
  obtain ⟨r, hr⟩ := hR
  have hgood : good R := by
    let f : V → H := fun x => if hx : x ∈ R then g ⟨x, hx⟩ else g ⟨r, hr⟩
    have hf (x : V) (hx : x ∈ R) : f x = g ⟨x, hx⟩ := by simp [f, hx]
    refine ⟨subset_rfl, hconn, f, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy he
      exact congrArg Subtype.val (g.injective (by simpa only [hf x hx, hf y hy] using he))
    · intro x hx y hy hxy
      simpa only [hf x hx, hf y hy] using g.toHom.map_rel'
        (show (T.induce (R : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy)
    · intro x hx
      rw [hf x hx]
      exact hg ⟨x, hx⟩
    · intro x
      exact hf x.val x.property
  let candidates := (univ : Finset (Finset V)).filter good
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card
    ⟨R, mem_filter.mpr ⟨mem_univ _, hgood⟩⟩
  obtain ⟨hRS, hconnS, f, hinj, hadj, hcolor, hfix⟩ := (mem_filter.mp hS).2
  have hSuniv : S = univ := by
    by_contra hne
    obtain ⟨p, hp, x, hx, hpx⟩ := exists_boundary_edge hT.isConnected S ⟨r, hRS hr⟩ hne
    have hxR : x ∉ R := fun h => hx (hRS h)
    obtain ⟨t, hpt, htcolor, htfresh⟩ := fresh_colored_neighbor G χ ψ S f hcolor hx
      (f p) (hdeg p x hpx hxR (f p) (hcolor p hp))
    have hparent (y : V) (hy : y ∈ S) (hxy : T.Adj x y) : y = p :=
      congrArg Subtype.val (unique_attachment hT.IsAcyclic hconnS hx
        (p := ⟨y, hy⟩) (q := ⟨p, hp⟩) hxy hpx.symm)
    let f' := Function.update f x t
    have hold (y : V) (hy : y ∈ S) : f' y = f y := by
      have hne : y ≠ x := fun he => hx (he ▸ hy)
      simp [f', Function.update_of_ne hne]
    have hnew : f' x = t := Function.update_self _ _ _
    have hgood' : good (insert x S) := by
      refine ⟨hRS.trans (subset_insert _ _), connected_insert hconnS hp hpx, f', ?_, ?_, ?_, ?_⟩
      · intro y hy z hz he
        rcases mem_insert.mp hy with hyx | hyS
        · subst y
          rcases mem_insert.mp hz with hzx | hzS
          · exact hzx.symm
          · exact ((htfresh z hzS) (by simpa only [hnew, hold z hzS] using he.symm)).elim
        · rcases mem_insert.mp hz with hzx | hzS
          · subst z
            exact ((htfresh y hyS) (by simpa only [hnew, hold y hyS] using he)).elim
          · exact hinj hyS hzS (by simpa only [hold y hyS, hold z hzS] using he)
      · intro y hy z hz hyz
        rcases mem_insert.mp hy with hyx | hyS
        · subst y
          rcases mem_insert.mp hz with hzx | hzS
          · subst z
            exact (T.irrefl hyz).elim
          · have hz' := hparent z hzS hyz
            rw [hnew, hold z hzS, hz']
            exact hpt.symm
        · rcases mem_insert.mp hz with hzx | hzS
          · subst z
            have hy' := hparent y hyS hyz.symm
            rw [hold y hyS, hnew, hy']
            exact hpt
          · rw [hold y hyS, hold z hzS]
            exact hadj y hyS z hzS hyz
      · intro y hy
        rcases mem_insert.mp hy with rfl | hy
        · rw [hnew]
          exact htcolor
        · rw [hold y hy]
          exact hcolor y hy
      · intro y
        exact (hold y.val (hRS y.property)).trans (hfix y)
    have hle := hmax (insert x S) (mem_filter.mpr ⟨mem_univ _, hgood'⟩)
    rw [card_insert_of_notMem hx] at hle
    omega
  have hall (x : V) : x ∈ S := hSuniv.symm ▸ mem_univ x
  refine ⟨⟨⟨f, fun {x y} hxy => hadj x (hall x) y (hall y) hxy⟩,
    fun x y he => hinj (hall x) (hall y) he⟩, hfix, ?_⟩
  exact fun x => hcolor x (hall x)

end ColoredGrowth

/-- Hypothesis-only interface for the supplied parity kernel.  The fields agree
with the finite-set parity-kernel certificate, without importing its proof. -/
structure KernelData {V : Type u} [Fintype V] (T : SimpleGraph V) (c : ℕ)
    (R U W : Finset V) : Prop where
  disjointRU : Disjoint R U
  disjointRW : Disjoint R W
  disjointUW : Disjoint U W
  partition : R ∪ U ∪ W = univ
  nonempty : R.Nonempty
  connected : (T.induce (R : Set V)).Connected
  independent : T.IsIndepSet (U : Set V)
  neighbors : ∀ w ∈ W, T.neighborSet w ⊆ (U : Set V)
  odd_le : U.card ≤ c
  outside_ge : 2 * c ≤ U.card + W.card

namespace KernelData

variable {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ} {R U W : Finset V}
    (h : KernelData T c R U W)

include h

lemma mem_parts (x : V) : x ∈ R ∨ x ∈ U ∨ x ∈ W := by
  have hx : x ∈ R ∪ U ∪ W := h.partition.symm ▸ mem_univ x
  simpa only [mem_union, or_assoc] using hx

lemma card_partition : R.card + U.card + W.card = Fintype.card V := by
  have hd : Disjoint (R ∪ U) W := disjoint_union_left.mpr ⟨h.disjointRW, h.disjointUW⟩
  have hc := congrArg Finset.card h.partition
  rwa [card_union_of_disjoint hd, card_union_of_disjoint h.disjointRU, card_univ] at hc

lemma core_card_bound : R.card + 2 * c ≤ Fintype.card V := by
  have := h.card_partition
  have := h.outside_ge
  omega

lemma proper (hc : 1 ≤ c) : R ≠ univ := by
  intro he
  have hb := h.core_card_bound
  rw [he, card_univ] at hb
  omega

/-- The odd class cannot be empty: a boundary edge of the nonempty proper core
must go to `U`, since there are no `R`--`W` edges. -/
lemma odd_nonempty (hT : T.Connected) (hc : 1 ≤ c) : U.Nonempty := by
  obtain ⟨p, hp, x, hx, hpx⟩ := exists_boundary_edge hT R h.nonempty (h.proper hc)
  rcases (h.mem_parts x).resolve_left hx with hxU | hxW
  · exact ⟨x, hxU⟩
  · exact (disjoint_left.mp h.disjointRU hp (h.neighbors x hxW hpx.symm)).elim

lemma induced_isTree (hT : T.IsTree) : (T.induce (R : Set V)).IsTree :=
  ⟨h.connected, hT.IsAcyclic.induce _⟩

lemma two_mul_le_edges (hT : T.IsTree) {k : ℕ} (hk : T.edgeFinset.card = k) :
    2 * c ≤ k := by
  have ht := hT.card_edgeFinset
  have hb := h.core_card_bound
  have hr := card_pos.mpr h.nonempty
  omega

lemma core_edges_le (hT : T.IsTree) {k : ℕ} (hk : T.edgeFinset.card = k) :
    (T.induce (R : Set V)).edgeFinset.card ≤ k - 2 * c := by
  have ht := (h.induced_isTree hT).card_edgeFinset
  have hg := hT.card_edgeFinset
  have hb := h.core_card_bound
  simp only [Finset.coe_sort_coe, Fintype.card_coe] at ht
  omega

lemma parameter_decreases (hT : T.IsTree) {k : ℕ} (hk : T.edgeFinset.card = k)
    (hc : 1 ≤ c) : k - 2 * c < k := by
  have := h.two_mul_le_edges hT hk
  omega

/-- The total number of vertices requiring images in `B` is at most `k`, not
`k+1`: at least one tree vertex belongs to `U`. -/
lemma nonodd_card_le (hT : T.IsTree) {k : ℕ} (hk : T.edgeFinset.card = k)
    (hc : 1 ≤ c) : (univ \ U).card ≤ k := by
  have ht := hT.card_edgeFinset
  have hu := card_pos.mpr (h.odd_nonempty hT.isConnected hc)
  rw [card_sdiff, inter_univ, card_univ]
  omega

end KernelData

/-- The host partition and its two cross-degree capacities. -/
structure HostCut {H : Type v} [Fintype H] (G : SimpleGraph H) (k c : ℕ)
    (A B : Finset H) : Prop where
  disjoint : Disjoint A B
  partition : A ∪ B = univ
  toB : ∀ x ∈ A, k ≤ (G.neighborFinset x ∩ B).card
  toA : ∀ y ∈ B, c ≤ (G.neighborFinset y ∩ A).card

namespace HostCut

variable {H : Type v} [Fintype H] {G : SimpleGraph H} {k c : ℕ} {A B : Finset H}
    (h : HostCut G k c A B)

include h

lemma mem_B_iff (x : H) : x ∈ B ↔ x ∉ A := by
  constructor
  · intro hx ha
    exact disjoint_left.mp h.disjoint ha hx
  · intro hx
    have hall : x ∈ A ∪ B := h.partition.symm ▸ mem_univ x
    exact (mem_union.mp hall).resolve_left hx

end HostCut

section Absorption

variable {V : Type u} [Fintype V] {H : Type v} [Fintype H]
    (T : SimpleGraph V) (G : SimpleGraph H)

/-- **Absorption of any prescribed core copy.** Under the kernel and cut
hypotheses, every copy `T[R] → G[B]` extends to a copy of all of `T`, sending
`U` to `A` and `W` to `B`, and agreeing pointwise with the prescribed copy. -/
theorem extend_kernel_copy (hT : T.IsTree) {k c : ℕ}
    (hk : T.edgeFinset.card = k) (hc : 1 ≤ c)
    {R U W : Finset V} (hK : KernelData T c R U W)
    {A B : Finset H} (hG : HostCut G k c A B)
    (g : (T.induce (R : Set V)).Copy (G.induce (B : Set H))) :
    ∃ f : T.Copy G, (∀ x : (R : Set V), f x.val = (g x).val) ∧
      (∀ x ∈ U, f x ∈ A) ∧ (∀ x ∈ W, f x ∈ B) := by
  classical
  let χ : V → Bool := fun x => decide (x ∈ U)
  let ψ : H → Bool := fun x => decide (x ∈ A)
  have htrue : univ.filter (fun x => χ x = true) = U := by ext x; simp [χ]
  have hfalse : univ.filter (fun x => χ x = false) = univ \ U := by ext x; simp [χ]
  have hA (s : H) : (G.neighborFinset s).filter (fun x => ψ x = true) =
      G.neighborFinset s ∩ A := by ext x; simp [ψ]
  have hB (s : H) : (G.neighborFinset s).filter (fun x => ψ x = false) =
      G.neighborFinset s ∩ B := by ext x; simp [ψ, hG.mem_B_iff]
  let g' := (Copy.induce G (B : Set H)).comp g
  have hg' : ∀ x : (R : Set V), ψ (g' x) = χ x.val := by
    intro x
    have hxU : x.val ∉ U := fun hx => disjoint_left.mp hK.disjointRU x.property hx
    have hxA : (g x).val ∉ A := (hG.mem_B_iff _).mp (g x).property
    change decide ((g x).val ∈ A) = decide (x.val ∈ U)
    simp only [hxU, hxA, decide_false]
  have hdeg : ∀ p x, T.Adj p x → x ∉ R → ∀ s, ψ s = χ p →
      (univ.filter (fun y => χ y = χ x)).card ≤
        ((G.neighborFinset s).filter (fun t => ψ t = χ x)).card := by
    intro p x hpx hxR s hs
    by_cases hxU : x ∈ U
    · have hpU : p ∉ U := fun hp => hK.independent hp hxU hpx.ne hpx
      have hsA : s ∉ A := by simpa [χ, ψ, hpU] using hs
      rw [show χ x = true by simp [χ, hxU], htrue, hA]
      exact hK.odd_le.trans (hG.toA s ((hG.mem_B_iff _).mpr hsA))
    · have hxW : x ∈ W := ((hK.mem_parts x).resolve_left hxR).resolve_left hxU
      have hpU : p ∈ U := hK.neighbors x hxW hpx.symm
      have hsA : s ∈ A := by simpa [χ, ψ, hpU] using hs
      rw [show χ x = false by simp [χ, hxU], hfalse, hB]
      exact (hK.nonodd_card_le hT hk hc).trans (hG.toB s hsA)
  obtain ⟨f, hfix, hcolor⟩ := colored_tree_extension T G hT R hK.nonempty hK.connected
    χ ψ g' hg' (by
      intro p x hpx hxR s hs
      simpa only using hdeg p x hpx hxR s hs)
  refine ⟨f, hfix, ?_, ?_⟩
  · intro x hx
    have hh := hcolor x
    simpa [χ, ψ, hx] using hh
  · intro x hx
    apply (hG.mem_B_iff _).mpr
    have hxU : x ∉ U := fun h => disjoint_left.mp hK.disjointUW h hx
    have hh := hcolor x
    simpa [χ, ψ, hxU] using hh

end Absorption


section CutCounting

variable {H : Type v} [Fintype H] (G : SimpleGraph H)

/-- The usual oriented cut-edge count equals the sum of cross-degrees. -/
lemma card_interedges_eq_sum (A B : Finset H) :
    (G.interedges A B).card = ∑ x ∈ A, (G.neighborFinset x ∩ B).card := by
  classical
  rw [G.interedges_def, card_filter, sum_product]
  apply sum_congr rfl
  intro x hx
  have he : G.neighborFinset x ∩ B = B.filter (fun y => G.Adj x y) := by
    ext y
    simp [and_comm]
  rw [he, card_filter]

lemma sum_internal_degrees (A : Finset H) :
    (∑ x ∈ A, (G.neighborFinset x ∩ A).card) =
      2 * (G.induce (A : Set H)).edgeFinset.card := by
  rw [← Finset.sum_coe_sort A]
  simp_rw [ErdosSosIndependent.card_neighbors_inter]
  exact (G.induce (A : Set H)).sum_degrees_eq_twice_card_edges

lemma degree_partition (A B : Finset H) (hd : Disjoint A B) (hp : A ∪ B = univ)
    (x : H) : G.degree x = (G.neighborFinset x ∩ A).card + (G.neighborFinset x ∩ B).card := by
  classical
  have hdis : Disjoint (G.neighborFinset x ∩ A) (G.neighborFinset x ∩ B) :=
    disjoint_of_subset_left inter_subset_right (disjoint_of_subset_right inter_subset_right hd)
  rw [← card_union_of_disjoint hdis, ← inter_union_distrib_left, hp, inter_univ,
    G.card_neighborFinset_eq_degree]

/-- Exact decomposition into edges in `A`, cut edges, and edges in `B`. -/
lemma edge_partition (A B : Finset H) (hd : Disjoint A B) (hp : A ∪ B = univ) :
    (G.induce (A : Set H)).edgeFinset.card + (G.interedges A B).card +
      (G.induce (B : Set H)).edgeFinset.card = G.edgeFinset.card := by
  classical
  have ha : (∑ x ∈ A, G.degree x) = 2 * (G.induce (A : Set H)).edgeFinset.card +
      (G.interedges A B).card := by
    simp_rw [degree_partition G A B hd hp]
    rw [sum_add_distrib, sum_internal_degrees, ← card_interedges_eq_sum]
  have hb : (∑ x ∈ B, G.degree x) = 2 * (G.induce (B : Set H)).edgeFinset.card +
      (G.interedges A B).card := by
    simp_rw [degree_partition G B A hd.symm (by rwa [union_comm])]
    rw [sum_add_distrib, sum_internal_degrees, ← card_interedges_eq_sum]
    congr 1
    exact Rel.card_interedges_comm G.symm B A
  have hs := G.sum_degrees_eq_twice_card_edges
  have he := Finset.sum_union (f := fun x => G.degree x) hd
  rw [hp, ha, hb] at he
  dsimp only at he
  rw [hs] at he
  omega

end CutCounting

/-- The exact rational surplus identity for a cut. -/
lemma cut_surplus_identity (k c n a b e eA eAB eB : ℚ)
    (hn : n = a + b) (he : e = eA + eAB + eB) :
    eB - (k - 2 * c - 1) / 2 * b =
      (e - (k - 1) / 2 * n) + ((k - 1) / 2 * a - eA - (eAB - c * b)) := by
  rw [hn, he]
  ring
lemma cut_transfer_arithmetic (k c n a b e eA eAB eB : ℚ)
    (hn : n = a + b) (he : e = eA + eAB + eB)
    (hdensity : (k - 1) / 2 * n < e)
    (hbudget : eAB - c * b ≤ (k - 1) / 2 * a - eA) :
    (k - 2 * c - 1) / 2 * b < eB := by
  have hid := cut_surplus_identity k c n a b e eA eAB eB hn he
  linarith

section CutDensity

variable {H : Type v} [Fintype H] (G : SimpleGraph H)

/-- The cut identity for actual finite graph counts.  Natural subtraction is
only used in the smaller edge parameter; all density arithmetic is rational. -/
lemma cut_surplus (A B : Finset H) (hd : Disjoint A B) (hp : A ∪ B = univ)
    {k c : ℕ} (hck : 2 * c ≤ k) :
    ((G.induce (B : Set H)).edgeFinset.card : ℚ) -
        (((k - 2 * c : ℕ) : ℚ) - 1) / 2 * B.card =
      ((G.edgeFinset.card : ℚ) - ((k : ℚ) - 1) / 2 * Fintype.card H) +
        (((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card -
          ((G.interedges A B).card - (c : ℚ) * B.card)) := by
  have hn : (Fintype.card H : ℚ) = (A.card : ℚ) + B.card := by
    have h := congrArg Finset.card hp
    rw [card_union_of_disjoint hd, card_univ] at h
    exact_mod_cast h.symm
  have he : (G.edgeFinset.card : ℚ) = (G.induce (A : Set H)).edgeFinset.card +
      (G.interedges A B).card + (G.induce (B : Set H)).edgeFinset.card := by
    exact_mod_cast (edge_partition G A B hd hp).symm
  rw [Nat.cast_sub hck, Nat.cast_mul, Nat.cast_ofNat]
  exact cut_surplus_identity k c (Fintype.card H) A.card B.card G.edgeFinset.card
    (G.induce (A : Set H)).edgeFinset.card (G.interedges A B).card
    (G.induce (B : Set H)).edgeFinset.card hn he

/-- The entire positive surplus survives the cut, provided the cut budget
holds.  In particular this is stronger than just strict density transfer. -/
theorem cut_surplus_transfer (A B : Finset H) (hd : Disjoint A B) (hp : A ∪ B = univ)
    {k c : ℕ} (hck : 2 * c ≤ k) (η : ℚ)
    (he : (G.edgeFinset.card : ℚ) = ((k : ℚ) - 1) / 2 * Fintype.card H + η)
    (hbudget : (G.interedges A B).card - (c : ℚ) * B.card ≤
      ((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card) :
    (((k - 2 * c : ℕ) : ℚ) - 1) / 2 * B.card + η ≤
      ((G.induce (B : Set H)).edgeFinset.card : ℚ) := by
  have hid := cut_surplus G A B hd hp hck
  linarith

/-- **Strict cut-density transfer.** The edge budget changes parameter `k` to
`k - 2*c`; all counts are the conventional finite graph counts. -/
theorem cut_density_transfer (A B : Finset H) (hd : Disjoint A B) (hp : A ∪ B = univ)
    {k c : ℕ} (hck : 2 * c ≤ k)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card H < (G.edgeFinset.card : ℚ))
    (hbudget : (G.interedges A B).card - (c : ℚ) * B.card ≤
      ((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card) :
    (((k - 2 * c : ℕ) : ℚ) - 1) / 2 * B.card <
      ((G.induce (B : Set H)).edgeFinset.card : ℚ) := by
  have hid := cut_surplus G A B hd hp hck
  linarith

end CutDensity

/-- The strict-density induction interface at parameter `m`.  It includes
all nonempty trees with **at most** `m` edges, at the single density threshold
`(m-1)/2`.  This avoids any hidden padding or relabeling assumption. -/
def StrictESUpTo (m : ℕ) : Prop :=
  ∀ {V : Type u} [Fintype V] {H : Type v} [Fintype H]
    (T : SimpleGraph V) (G : SimpleGraph H), T.IsTree → T.edgeFinset.card ≤ m →
      ((m : ℚ) - 1) / 2 * Fintype.card H < (G.edgeFinset.card : ℚ) → T.IsContained G

section ConditionalES

variable {V : Type u} [Fintype V] {H : Type v} [Fintype H]
    (T : SimpleGraph V) (G : SimpleGraph H)

/-- **Conditional parameter-decreasing Erdős–Sós step.** The kernel is a
hypothesis.  Only the strict-density induction hypothesis at `k - 2*c` is
used; the kernel itself proves this is a strictly smaller parameter. -/
theorem isContained_of_kernel_cut (hT : T.IsTree) {k c : ℕ}
    (hk : T.edgeFinset.card = k) (hc : 1 ≤ c)
    {R U W : Finset V} (hK : KernelData T c R U W)
    {A B : Finset H} (hG : HostCut G k c A B)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card H < (G.edgeFinset.card : ℚ))
    (hbudget : (G.interedges A B).card - (c : ℚ) * B.card ≤
      ((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card)
    (ih : StrictESUpTo.{u, v} (k - 2 * c)) : T.IsContained G := by
  have hd := cut_density_transfer G A B hG.disjoint hG.partition
    (hK.two_mul_le_edges hT hk) hdensity hbudget
  obtain ⟨g⟩ := ih (T.induce (R : Set V)) (G.induce (B : Set H))
    (hK.induced_isTree hT) (hK.core_edges_le hT hk)
    (by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hd)
  obtain ⟨f, _⟩ := extend_kernel_copy T G hT hk hc hK hG g
  exact ⟨f⟩

/-- The strong-induction form makes the strict decrease explicit at the call
to the induction hypothesis.  No existence assertion for a kernel or a host
cut is assumed globally or proved here. -/
theorem conditional_erdos_sos (hT : T.IsTree) {k c : ℕ}
    (hk : T.edgeFinset.card = k) (hc : 1 ≤ c)
    (hkernel : ∃ R U W : Finset V, KernelData T c R U W)
    {A B : Finset H} (hG : HostCut G k c A B)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card H < (G.edgeFinset.card : ℚ))
    (hbudget : (G.interedges A B).card - (c : ℚ) * B.card ≤
      ((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card)
    (ih : ∀ m < k, StrictESUpTo.{u, v} m) : T.IsContained G := by
  obtain ⟨R, U, W, hK⟩ := hkernel
  exact isContained_of_kernel_cut T G hT hk hc hK hG hdensity hbudget
    (ih (k - 2 * c) (hK.parameter_decreases hT hk hc))

end ConditionalES

end TreeCutAbsorption

-- Transitive kernel-dependency audits for the main public interfaces.
#print axioms TreeCutAbsorption.colored_tree_extension
#print axioms TreeCutAbsorption.extend_kernel_copy
#print axioms TreeCutAbsorption.KernelData.parameter_decreases
#print axioms TreeCutAbsorption.edge_partition
#print axioms TreeCutAbsorption.cut_surplus_transfer
#print axioms TreeCutAbsorption.cut_density_transfer
#print axioms TreeCutAbsorption.isContained_of_kernel_cut
#print axioms TreeCutAbsorption.conditional_erdos_sos
