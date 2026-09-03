import Submission.TreeParityKernel
import Submission.TreeCutAbsorption

set_option autoImplicit false

/-!
# Additional, degree-sensitive parity-kernel bounds

This file does NOT assert the unrooted exact-cardinality conjecture.
It proves an identity valid for every kernel, a lower bound on the odd part,
and the exact-cardinality conclusion for maximum degree at most two.
The shared kernel and specification files are not changed.
-/

open Finset SimpleGraph Classical

namespace TreeExactKernelBounds

universe u v

lemma kernelData {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (h : TreeParityKernel.IsParityKernel T c R U W) :
    TreeCutAbsorption.KernelData T c R U W :=
  ⟨h.disjointRU, h.disjointRW, h.disjointUW, h.partition, h.nonempty,
    h.connected, h.independent, h.neighbors, h.odd_le, h.outside_ge⟩

/-- Every edge outside the connected core is incident to exactly one odd vertex.
Consequently the number of removed vertices is the sum of their tree degrees. -/
theorem degree_sum {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W) :
    (∑ x ∈ U, T.degree x) = U.card + W.card := by
  classical
  let B := R ∪ W
  have hd : Disjoint U B := disjoint_union_right.mpr ⟨h.disjointRU.symm, h.disjointUW⟩
  have hp : U ∪ B = univ := by
    simpa only [B, union_left_comm, union_assoc] using h.partition
  have hNU {x : V} (hx : x ∈ U) : T.neighborFinset x ⊆ B := by
    intro y hy
    have ha : T.Adj x y := (T.mem_neighborFinset _ _).mp hy
    rcases h.mem_parts y with hyR | hyU | hyW
    · exact mem_union_left W hyR
    · exact (h.independent hx hyU ha.ne ha).elim
    · exact mem_union_right R hyW
  have hcut : (T.interedges U B).card = ∑ x ∈ U, T.degree x := by
    rw [TreeCutAbsorption.card_interedges_eq_sum]
    apply sum_congr rfl
    intro x hx
    rw [inter_eq_left.mpr (hNU hx), T.card_neighborFinset_eq_degree]
  have hNBW {x : V} (hx : x ∈ W) : T.neighborFinset x ∩ B = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hay : T.Adj x y := (T.mem_neighborFinset _ _).mp (mem_inter.mp hy).1
    exact disjoint_left.mp hd (h.neighbors x hx hay) (mem_inter.mp hy).2
  have hNBR {x : V} (hx : x ∈ R) :
      T.neighborFinset x ∩ B = T.neighborFinset x ∩ R := by
    ext y
    constructor
    · intro hy
      have hyN := (mem_inter.mp hy).1
      rcases mem_union.mp (mem_inter.mp hy).2 with hyR | hyW
      · exact mem_inter.mpr ⟨hyN, hyR⟩
      · have ha : T.Adj y x := ((T.mem_neighborFinset _ _).mp hyN).symm
        exact (disjoint_left.mp h.disjointRU hx (h.neighbors y hyW ha)).elim
    · intro hy
      exact mem_inter.mpr ⟨(mem_inter.mp hy).1, mem_union_left W (mem_inter.mp hy).2⟩
  have hB : (T.induce (B : Set V)).edgeFinset.card =
      (T.induce (R : Set V)).edgeFinset.card := by
    have hs : (∑ x ∈ B, (T.neighborFinset x ∩ B).card) =
        ∑ x ∈ R, (T.neighborFinset x ∩ R).card := by
      rw [show B = R ∪ W from rfl, sum_union h.disjointRW]
      have hw : (∑ x ∈ W, (T.neighborFinset x ∩ (R ∪ W)).card) = 0 := by
        apply sum_eq_zero
        intro x hx
        change (T.neighborFinset x ∩ B).card = 0
        rw [hNBW hx, card_empty]
      rw [hw, add_zero]
      apply sum_congr rfl
      intro x hx
      change (T.neighborFinset x ∩ B).card = _
      rw [hNBR hx]
    rw [TreeCutAbsorption.sum_internal_degrees, TreeCutAbsorption.sum_internal_degrees] at hs
    omega
  have hU : T.induce (U : Set V) = ⊥ := by
    ext x y
    change T.Adj x.val y.val ↔ False
    exact iff_false_intro (fun ha => h.independent x.property y.property ha.ne ha)
  have he := TreeCutAbsorption.edge_partition T U B hd hp
  rw [edgeFinset_eq_empty.mpr hU, card_empty, zero_add] at he
  rw [hcut, hB] at he
  have ht := hT.card_edgeFinset
  have hr := (h.induced_isTree hT).card_edgeFinset
  simp only [Finset.coe_sort_coe, Fintype.card_coe] at hr
  have hpart := h.card_partition
  omega

/-- A maximum-degree bound forces a lower bound on the size of every odd part. -/
theorem odd_degree_bound {V : Type u} [Fintype V] {T : SimpleGraph V} {c Δ : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W)
    (hΔ : ∀ x ∈ U, T.degree x ≤ Δ) :
    2 * c ≤ U.card * Δ := by
  calc
    2 * c ≤ U.card + W.card := h.outside_ge
    _ = ∑ x ∈ U, T.degree x := (degree_sum hT h).symm
    _ ≤ ∑ _x ∈ U, Δ := sum_le_sum hΔ
    _ = U.card * Δ := by simp

/-- The integer form is `ceil (2*c/Δ)`, for positive `c` and `Δ`. -/
theorem odd_card_lower {V : Type u} [Fintype V] {T : SimpleGraph V} {c Δ : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W)
    (hc : 1 ≤ c) (hΔpos : 0 < Δ) (hΔ : ∀ x ∈ U, T.degree x ≤ Δ) :
    (2 * c - 1) / Δ + 1 ≤ U.card := by
  have hb := odd_degree_bound hT h hΔ
  have hlt : 2 * c - 1 < U.card * Δ := by omega
  have hh : (2 * c - 1) / Δ < U.card := (Nat.div_lt_iff_lt_mul hΔpos).mpr hlt
  omega

/-- Total positive degree excess over two. For a nontrivial tree this is
exactly its number of leaves minus two. -/
noncomputable def excess {V : Type u} [Fintype V] (T : SimpleGraph V) : ℕ :=
  ∑ x, (T.degree x - 2)

noncomputable def leaves {V : Type u} [Fintype V] (T : SimpleGraph V) : ℕ :=
  (univ.filter (fun x => T.degree x = 1)).card

/-- The standard leaf/excess identity, with the nontriviality condition explicit. -/
theorem excess_add_two_eq_leaves {V : Type u} [Fintype V] [Nontrivial V]
    {T : SimpleGraph V} (hT : T.IsTree) : excess T + 2 = leaves T := by
  classical
  have hi (x : V) : (T.degree x - 2) + 2 =
      T.degree x + (if T.degree x = 1 then 1 else 0) := by
    have := hT.isConnected.preconnected.degree_pos_of_nontrivial x
    split_ifs <;> omega
  have hs := sum_congr (s₁ := (univ : Finset V)) rfl (fun x _ => hi x)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul] at hs
  have ht := hT.card_edgeFinset
  have hd := T.sum_degrees_eq_twice_card_edges
  have he : excess T = ∑ x, (T.degree x - 2) := rfl
  have hl : leaves T = ∑ x, if T.degree x = 1 then 1 else 0 := by
    exact card_filter _ _
  omega

/-- A second lower bound, useful for trees with few leaves. -/
theorem odd_excess_bound {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W) :
    2 * c ≤ 2 * U.card + excess T := by
  classical
  have hs : (∑ x ∈ U, (T.degree x - 2)) ≤ excess T := by
    exact sum_le_sum_of_subset (subset_univ U)
  calc
    2 * c ≤ U.card + W.card := h.outside_ge
    _ = ∑ x ∈ U, T.degree x := (degree_sum hT h).symm
    _ ≤ ∑ x ∈ U, (2 + (T.degree x - 2)) := by
      apply sum_le_sum
      intro x _
      omega
    _ = 2 * U.card + ∑ x ∈ U, (T.degree x - 2) := by
      rw [sum_add_distrib]
      simp [mul_comm]
    _ ≤ 2 * U.card + excess T := Nat.add_le_add_left hs _

/-- In particular `|U| ≥ c - floor((leaves(T)-2)/2)` for a nontrivial tree. -/
theorem odd_card_lower_excess {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W) :
    c - excess T / 2 ≤ U.card := by
  have := odd_excess_bound hT h
  omega

/-- The established kernel is already exact if the total positive degree
excess is at most one (in particular, for trees with at most three leaves). -/
theorem exact_of_excess_le_one {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W) (he : excess T ≤ 1) : U.card = c := by
  have := odd_excess_bound hT h
  have := h.odd_le
  omega

/-- Paths require no strengthening of the kernel construction: its existing
upper bound is automatically an equality when degrees are at most two. -/
theorem exact_of_degree_le_two {V : Type u} [Fintype V] {T : SimpleGraph V} {c : ℕ}
    {R U W : Finset V} (hT : T.IsTree)
    (h : TreeCutAbsorption.KernelData T c R U W)
    (hΔ : ∀ x ∈ U, T.degree x ≤ 2) : U.card = c := by
  have := odd_degree_bound hT h hΔ
  have := h.odd_le
  omega

/-- Existence of exact kernels for every admissible parameter of a path. -/
theorem exists_exact_of_degree_le_two {V : Type u} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (c : ℕ) (hc : 2 * c < Fintype.card V)
    (hΔ : ∀ x, T.degree x ≤ 2) :
    ∃ R U W : Finset V, TreeParityKernel.IsParityKernel T c R U W ∧ U.card = c := by
  obtain ⟨R, U, W, h⟩ := TreeParityKernel.exists_parity_kernel_of_card hT c hc
  exact ⟨R, U, W, h, exact_of_degree_le_two hT (kernelData h) (fun x _ => hΔ x)⟩


/-- All admissible kernels of a tree with at most three leaves are exact. -/
theorem exists_exact_of_leaves_le_three {V : Type u} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (c : ℕ) (hc : 1 ≤ c) (hcard : 2 * c < Fintype.card V)
    (hℓ : leaves T ≤ 3) :
    ∃ R U W : Finset V, TreeParityKernel.IsParityKernel T c R U W ∧ U.card = c := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have he := excess_add_two_eq_leaves hT
  obtain ⟨R, U, W, h⟩ := TreeParityKernel.exists_parity_kernel_of_card hT c hcard
  exact ⟨R, U, W, h, exact_of_excess_le_one hT (kernelData h) (by omega)⟩

/-- Quantitative existence, obtained from the already proved kernel without
changing its core-size/removed-vertex budget. -/
theorem exists_kernel_odd_lower {V : Type u} [Fintype V] {T : SimpleGraph V}
    (hT : T.IsTree) (c Δ : ℕ) (hc : 1 ≤ c) (hcard : 2 * c < Fintype.card V)
    (hΔpos : 0 < Δ) (hΔ : ∀ x, T.degree x ≤ Δ) :
    ∃ R U W : Finset V, TreeParityKernel.IsParityKernel T c R U W ∧
      (2 * c - 1) / Δ + 1 ≤ U.card := by
  obtain ⟨R, U, W, h⟩ := TreeParityKernel.exists_parity_kernel_of_card hT c hcard
  exact ⟨R, U, W, h,
    odd_card_lower hT (kernelData h) hc hΔpos (fun x _ => hΔ x)⟩

/-- Any proved lower bound `L ≤ |U|` lowers the A-to-B demand to `|T|-L`.
The B-to-A demand remains `c`, and the prescribed core copy is unchanged. -/
theorem extend_kernel_copy_of_lower {V : Type u} [Fintype V]
    {H : Type v} [Fintype H] (T : SimpleGraph V) (G : SimpleGraph H)
    (hT : T.IsTree) {c L : ℕ} {R U W : Finset V}
    (hK : TreeCutAbsorption.KernelData T c R U W) (hL : L ≤ U.card)
    {A B : Finset H} (hd : Disjoint A B) (hp : A ∪ B = univ)
    (htoB : ∀ s ∈ A, Fintype.card V - L ≤ (G.neighborFinset s ∩ B).card)
    (htoA : ∀ s ∈ B, c ≤ (G.neighborFinset s ∩ A).card)
    (g : (T.induce (R : Set V)).Copy (G.induce (B : Set H))) :
    ∃ f : T.Copy G, (∀ x : (R : Set V), f x.val = (g x).val) ∧
      (∀ x ∈ U, f x ∈ A) ∧ (∀ x ∈ W, f x ∈ B) := by
  classical
  have hmem (x : H) : x ∈ B ↔ x ∉ A := by
    constructor
    · intro hx ha
      exact disjoint_left.mp hd ha hx
    · intro hx
      have hh : x ∈ A ∪ B := hp.symm ▸ mem_univ x
      exact (mem_union.mp hh).resolve_left hx
  let χ : V → Bool := fun x => decide (x ∈ U)
  let ψ : H → Bool := fun x => decide (x ∈ A)
  have htrue : univ.filter (fun x => χ x = true) = U := by ext x; simp [χ]
  have hfalse : univ.filter (fun x => χ x = false) = univ \ U := by ext x; simp [χ]
  have hA (s : H) : (G.neighborFinset s).filter (fun x => ψ x = true) =
      G.neighborFinset s ∩ A := by ext x; simp [ψ]
  have hB (s : H) : (G.neighborFinset s).filter (fun x => ψ x = false) =
      G.neighborFinset s ∩ B := by ext x; simp [ψ, hmem]
  let g' := (Copy.induce G (B : Set H)).comp g
  have hg' : ∀ x : (R : Set V), ψ (g' x) = χ x.val := by
    intro x
    have hxU : x.val ∉ U := fun hx => disjoint_left.mp hK.disjointRU x.property hx
    have hxA : (g x).val ∉ A := (hmem _).mp (g x).property
    change decide ((g x).val ∈ A) = decide (x.val ∈ U)
    simp only [hxU, hxA, decide_false]
  have hdeg : ∀ p x, T.Adj p x → x ∉ R → ∀ s, ψ s = χ p →
      (univ.filter (fun y => χ y = χ x)).card ≤
        ((G.neighborFinset s).filter (fun t => ψ t = χ x)).card := by
    intro p x hpx hxR s hs
    by_cases hxU : x ∈ U
    · have hpU : p ∉ U := fun hpU => hK.independent hpU hxU hpx.ne hpx
      have hsA : s ∉ A := by simpa [χ, ψ, hpU] using hs
      rw [show χ x = true by simp [χ, hxU], htrue, hA]
      exact hK.odd_le.trans (htoA s ((hmem _).mpr hsA))
    · have hxW : x ∈ W := ((hK.mem_parts x).resolve_left hxR).resolve_left hxU
      have hpU : p ∈ U := hK.neighbors x hxW hpx.symm
      have hsA : s ∈ A := by simpa [χ, ψ, hpU] using hs
      rw [show χ x = false by simp [χ, hxU], hfalse, hB]
      rw [card_sdiff, inter_univ, card_univ]
      exact (Nat.sub_le_sub_left hL (Fintype.card V)).trans (htoB s hsA)
  obtain ⟨f, hfix, hcolor⟩ := TreeCutAbsorption.colored_tree_extension
    T G hT R hK.nonempty hK.connected χ ψ g' hg' hdeg
  refine ⟨f, hfix, ?_, ?_⟩
  · intro x hx
    have hh := hcolor x
    simpa [χ, ψ, hx] using hh
  · intro x hx
    apply (hmem _).mpr
    have hxU : x ∉ U := fun hh => disjoint_left.mp hK.disjointUW hh hx
    have hh := hcolor x
    simpa [χ, ψ, hxU] using hh

/-- The unconditional, maximum-degree-sensitive cross-degree improvement. -/
theorem extend_kernel_copy_degree {V : Type u} [Fintype V]
    {H : Type v} [Fintype H] (T : SimpleGraph V) (G : SimpleGraph H)
    (hT : T.IsTree) {c Δ : ℕ} {R U W : Finset V}
    (hK : TreeCutAbsorption.KernelData T c R U W) (hc : 1 ≤ c)
    (hΔpos : 0 < Δ) (hΔ : ∀ x, T.degree x ≤ Δ)
    {A B : Finset H} (hd : Disjoint A B) (hp : A ∪ B = univ)
    (htoB : ∀ s ∈ A, Fintype.card V - ((2 * c - 1) / Δ + 1) ≤
      (G.neighborFinset s ∩ B).card)
    (htoA : ∀ s ∈ B, c ≤ (G.neighborFinset s ∩ A).card)
    (g : (T.induce (R : Set V)).Copy (G.induce (B : Set H))) :
    ∃ f : T.Copy G, (∀ x : (R : Set V), f x.val = (g x).val) ∧
      (∀ x ∈ U, f x ∈ A) ∧ (∀ x ∈ W, f x ∈ B) :=
  extend_kernel_copy_of_lower T G hT hK
    (odd_card_lower hT hK hc hΔpos (fun x _ => hΔ x)) hd hp htoB htoA g


/-- A genuine stronger absorption-cut reduction, using only the established
kernel and the target-tree degree bound.  The density budget and smaller
parameter are unchanged; the A-to-B threshold is `k+1-ceil(2*c/Δ)`. -/
theorem isContained_of_degree_cut {V : Type u} [Fintype V]
    {H : Type v} [Fintype H] (T : SimpleGraph V) (G : SimpleGraph H)
    (hT : T.IsTree) {k c Δ : ℕ} (hk : T.edgeFinset.card = k)
    (hc : 1 ≤ c) (hck : c ≤ k / 2) (hΔpos : 0 < Δ)
    (hΔ : ∀ x, T.degree x ≤ Δ)
    {A B : Finset H} (hd : Disjoint A B) (hp : A ∪ B = univ)
    (htoB : ∀ s ∈ A, k + 1 - ((2 * c - 1) / Δ + 1) ≤
      (G.neighborFinset s ∩ B).card)
    (htoA : ∀ s ∈ B, c ≤ (G.neighborFinset s ∩ A).card)
    (hdensity : ((k : ℚ) - 1) / 2 * Fintype.card H < (G.edgeFinset.card : ℚ))
    (hbudget : (G.interedges A B).card - (c : ℚ) * B.card ≤
      ((k : ℚ) - 1) / 2 * A.card - (G.induce (A : Set H)).edgeFinset.card)
    (ih : ∀ m < k, TreeCutAbsorption.StrictESUpTo.{u, v} m) : T.IsContained G := by
  obtain ⟨R, U, W, hK, _⟩ := TreeParityKernel.parity_kernel hT hk hc hck
  let hK' := kernelData hK
  have hcard : Fintype.card V = k + 1 := by
    have ht := hT.card_edgeFinset
    omega
  have hden := TreeCutAbsorption.cut_density_transfer G A B hd hp
    (hK'.two_mul_le_edges hT hk) hdensity hbudget
  obtain ⟨g⟩ := ih (k - 2 * c) (hK'.parameter_decreases hT hk hc)
    (T.induce (R : Set V)) (G.induce (B : Set H))
    (hK'.induced_isTree hT) (hK'.core_edges_le hT hk)
    (by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hden)
  obtain ⟨f, _⟩ := extend_kernel_copy_degree T G hT hK' hc hΔpos hΔ hd hp
    (by simpa only [hcard] using htoB) htoA g
  exact ⟨f⟩

end TreeExactKernelBounds

#print axioms TreeExactKernelBounds.degree_sum
#print axioms TreeExactKernelBounds.odd_card_lower
#print axioms TreeExactKernelBounds.exists_exact_of_degree_le_two

#print axioms TreeExactKernelBounds.exists_kernel_odd_lower
#print axioms TreeExactKernelBounds.extend_kernel_copy_of_lower
#print axioms TreeExactKernelBounds.extend_kernel_copy_degree

#print axioms TreeExactKernelBounds.isContained_of_degree_cut

#print axioms TreeExactKernelBounds.odd_card_lower_excess
#print axioms TreeExactKernelBounds.exact_of_excess_le_one

#print axioms TreeExactKernelBounds.excess_add_two_eq_leaves
#print axioms TreeExactKernelBounds.exists_exact_of_leaves_le_three
