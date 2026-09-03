import Submission.CriticalBlocker

/-!
# Exact normalization and support budgets for critical graphs

This standalone development uses `Auxiliary.CriticalBlocker.IsProductCritical`:
`(A * W) ^ k < n`, and every proper induced subgraph satisfies the opposite
product bound with the same exponent. It does not import `Submission.Spec`.

Write `A = G.indepNum`, `W = G.cliqueNum`, and `n = Fintype.card V`.
The main results are:

* `card_eq_product_pow_add_one`: deleting one vertex gives `n = (A * W) ^ k + 1`,
  even for `k = 0`.
* `single_deletion_parameters`: for `1 ≤ k`, every single-vertex deletion
  preserves both `A` and `W`.
* `support_budget`: for an independent host `B` of size `t` and `J ⊂ B`, the
  signed-support bag `X_J` satisfies `|X_J| ≤ ((A - t + |J|) * W) ^ k`.
* `partial_host_inequality`: if `s ≤ m < t`, the set `L_s` of vertices with
  signed support of size at most `s` satisfies
  `|L_s| * choose (t - s) (m - s) ≤ choose t m * ((A - t + m) * W) ^ k`.

The budget and partial-host results only require `ProperInducedBound`; critical
versions are also supplied. Independence implies `t ≤ A`. The clique-host
versions use signed supports in the complement, i.e. nonneighbors outside the
host and a singleton inside it. All powers and counts are natural numbers.

These are combinatorial consequences of criticality, not a proof of EH or an
assertion about a forbidden graph.
-/

open SimpleGraph

namespace Auxiliary.CriticalSupport

open CriticalBlocker

section Normalization

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {k : ℕ}

/-- A strict product counterexample has a vertex. -/
theorem card_pos_of_critical (hcrit : IsProductCritical G k) :
    0 < Fintype.card V :=
  lt_of_le_of_lt (Nat.zero_le _) hcrit.1

variable [DecidableEq V]

/-- Deleting one vertex bounds `n - 1` by the product power of the remaining graph. -/
theorem single_deletion_bound (hproper : ProperInducedBound G k) (v : V) :
    Fintype.card V - 1 ≤
      ((G.induce (↑({v} : Finset V)ᶜ : Set V)).indepNum *
        (G.induce (↑({v} : Finset V)ᶜ : Set V)).cliqueNum) ^ k := by
  haveI : Nonempty V := ⟨v⟩
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hcard : ({v} : Finset V)ᶜ.card = Fintype.card V - 1 := by
    simp only [Finset.card_compl, Finset.card_singleton]
  have hproperV : ({v} : Finset V)ᶜ.card < Fintype.card V := by omega
  simpa only [hcard] using hproper ({v} : Finset V)ᶜ hproperV

/-- Exact normalization. In fact this holds even for the exponent zero. -/
theorem card_eq_product_pow_add_one (hcrit : IsProductCritical G k) :
    Fintype.card V = (G.indepNum * G.cliqueNum) ^ k + 1 := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (card_pos_of_critical hcrit)
  obtain ⟨v⟩ := ‹Nonempty V›
  have hsmall := single_deletion_bound hcrit.2 v
  have hmono := Nat.pow_le_pow_left
    (Nat.mul_le_mul (indepNum_induce_le G (↑({v} : Finset V)ᶜ : Set V))
      (cliqueNum_induce_le G (↑({v} : Finset V)ᶜ : Set V))) k
  have hlarge := hcrit.1
  omega

/-- Every single-vertex deletion preserves both `A` and `W` when `1 ≤ k`. -/
theorem single_deletion_parameters (hcrit : IsProductCritical G k) (hk : 1 ≤ k)
    (v : V) :
    (G.induce (↑({v} : Finset V)ᶜ : Set V)).indepNum = G.indepNum ∧
      (G.induce (↑({v} : Finset V)ᶜ : Set V)).cliqueNum = G.cliqueNum := by
  haveI : Nonempty V := ⟨v⟩
  have hApos : 0 < G.indepNum := SimpleGraph.indepNum_pos
  have hWpos : 0 < G.cliqueNum := by
    simpa only [indepNum_compl] using (SimpleGraph.indepNum_pos (G := Gᶜ))
  have hsmall := single_deletion_bound hcrit.2 v
  rw [card_eq_product_pow_add_one hcrit, Nat.add_sub_cancel] at hsmall
  have hprod := (Nat.pow_le_pow_iff_left (show k ≠ 0 by omega)).mp hsmall
  have hA := indepNum_induce_le G (↑({v} : Finset V)ᶜ : Set V)
  have hW := cliqueNum_induce_le G (↑({v} : Finset V)ᶜ : Set V)
  constructor
  · exact le_antisymm hA (Nat.le_of_mul_le_mul_right
      (hprod.trans (Nat.mul_le_mul_left _ hW)) hWpos)
  · exact le_antisymm hW (Nat.le_of_mul_le_mul_left
      (hprod.trans (Nat.mul_le_mul_right _ hA)) hApos)

/-- The independence-number half of single-vertex deletion invariance. -/
theorem indepNum_delete_singleton (hcrit : IsProductCritical G k) (hk : 1 ≤ k)
    (v : V) :
    (G.induce (↑({v} : Finset V)ᶜ : Set V)).indepNum = G.indepNum :=
  (single_deletion_parameters hcrit hk v).1

/-- The clique-number half of single-vertex deletion invariance. -/
theorem cliqueNum_delete_singleton (hcrit : IsProductCritical G k) (hk : 1 ≤ k)
    (v : V) :
    (G.induce (↑({v} : Finset V)ᶜ : Set V)).cliqueNum = G.cliqueNum :=
  (single_deletion_parameters hcrit hk v).2

end Normalization

section Anticomplete

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- An independent set anticomplete to `X` can be added to any independent
set of `G[X]`. The two contributions are counted without overlap. -/
theorem indepNum_induce_add_card_le (X C : Finset V) (hdisj : Disjoint X C)
    (hC : G.IsIndepSet (C : Set V))
    (hanti : ∀ x ∈ X, ∀ y ∈ C, ¬ G.Adj x y) :
    (G.induce (X : Set V)).indepNum + C.card ≤ G.indepNum := by
  classical
  obtain ⟨S, hS⟩ := (G.induce (X : Set V)).exists_isNIndepSet_indepNum
  let f : (X : Set V) ↪ V := Function.Embedding.subtype _
  let T := S.map f
  have hTX : T ⊆ X := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact a.property
  have hT : G.IsIndepSet (T : Set V) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact hS.isIndepSet ha hb (ne_of_apply_ne f hxy)
  have hTC : Disjoint T C := hdisj.mono_left hTX
  have hunion : G.IsIndepSet (↑(T ∪ C) : Set V) := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hx | hx <;>
      rcases Finset.mem_union.mp hy with hy | hy
    · exact hT hx hy hxy
    · exact hanti x (hTX hx) y hy
    · exact fun h => hanti y (hTX hy) x hx h.symm
    · exact hC hx hy hxy
  have hcard := hunion.card_le_indepNum
  simpa only [Finset.card_union_of_disjoint hTC, T, Finset.card_map, hS.card_eq]
    using hcard

end Anticomplete

section SignedSupport

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Signed support on a host: a host vertex supports itself, while an outside
vertex is supported on its neighbors in the host. -/
def signedSupport (B : Finset V) (x : V) : Finset V :=
  if x ∈ B then {x} else B.filter (G.Adj x)

/-- The special convention on host vertices is essential for disjointness. -/
@[simp] theorem signedSupport_of_mem {B : Finset V} {x : V} (hx : x ∈ B) :
    signedSupport G B x = {x} := by
  simp only [signedSupport, if_pos hx]

/-- Outside the host, signed support is precisely the neighborhood in the host. -/
theorem signedSupport_of_notMem {B : Finset V} {x : V} (hx : x ∉ B) :
    signedSupport G B x = B.filter (G.Adj x) := by
  simp only [signedSupport, if_neg hx]

/-- All signed supports lie in the host. -/
theorem signedSupport_subset (B : Finset V) (x : V) : signedSupport G B x ⊆ B := by
  by_cases hx : x ∈ B
  · simpa only [signedSupport_of_mem G hx, Finset.singleton_subset_iff] using hx
  · rw [signedSupport_of_notMem G hx]
    exact Finset.filter_subset _ _

variable [Fintype V]

/-- The bag `X_J` of vertices whose entire signed support lies in `J`. -/
def supportBag (B J : Finset V) : Finset V :=
  Finset.univ.filter (fun x => signedSupport G B x ⊆ J)

@[simp] theorem mem_supportBag (B J : Finset V) (x : V) :
    x ∈ supportBag G B J ↔ signedSupport G B x ⊆ J := by
  simp only [supportBag, Finset.mem_filter, Finset.mem_univ, true_and]

/-- On the host itself the bag is exactly `J` (intersected with the host). -/
theorem mem_supportBag_of_mem_host {B J : Finset V} {x : V} (hx : x ∈ B) :
    x ∈ supportBag G B J ↔ x ∈ J := by
  simp only [mem_supportBag, signedSupport_of_mem G hx, Finset.singleton_subset_iff]

/-- `X_J` is disjoint from the unused part of the host, even for nonindependent hosts. -/
theorem supportBag_disjoint (B J : Finset V) :
    Disjoint (supportBag G B J) (B \ J) := by
  apply Finset.disjoint_left.mpr
  intro x hx hBJ
  obtain ⟨hxB, hxJ⟩ := Finset.mem_sdiff.mp hBJ
  exact hxJ ((mem_supportBag_of_mem_host G hxB).mp hx)

/-- For an independent host, `X_J` is anticomplete to `B \ J`. -/
theorem supportBag_anticomplete (B J : Finset V) (hB : G.IsIndepSet (B : Set V)) :
    ∀ x ∈ supportBag G B J, ∀ y ∈ B \ J, ¬ G.Adj x y := by
  intro x hx y hy hxy
  obtain ⟨hyB, hyJ⟩ := Finset.mem_sdiff.mp hy
  by_cases hxB : x ∈ B
  · exact hB hxB hyB hxy.ne hxy
  · apply hyJ
    apply (mem_supportBag G B J x).mp hx
    rw [signedSupport_of_notMem G hxB]
    exact Finset.mem_filter.mpr ⟨hyB, hxy⟩

/-- A proper subhost gives a proper induced bag. -/
theorem supportBag_card_lt (B J : Finset V) (hJ : J ⊂ B) :
    (supportBag G B J).card < Fintype.card V := by
  obtain ⟨x, hxB, hxJ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (Finset.card_lt_card hJ)
  apply (Finset.card_lt_iff_ne_univ _).mpr
  intro hfull
  have hx : x ∈ supportBag G B J := by
    rw [hfull]
    exact Finset.mem_univ x
  exact hxJ ((mem_supportBag_of_mem_host G hxB).mp hx)

/-- The independence-number budget: each of the `|B| - |J|` unused host
vertices can be appended to an independent set in `X_J`. -/
theorem supportBag_indepNum_le (B J : Finset V) (hB : G.IsIndepSet (B : Set V))
    (hJ : J ⊆ B) :
    (G.induce (↑(supportBag G B J) : Set V)).indepNum ≤
      G.indepNum - B.card + J.card := by
  have hBJ : G.IsIndepSet (↑(B \ J) : Set V) := by
    intro x hx y hy hxy
    exact hB (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
  have hbudget := indepNum_induce_add_card_le (supportBag G B J) (B \ J)
    (supportBag_disjoint G B J) hBJ (supportBag_anticomplete G B J hB)
  rw [Finset.card_sdiff_of_subset hJ] at hbudget
  have hBA := hB.card_le_indepNum
  have hJB := Finset.card_le_card hJ
  omega

/-- The support budget only needs the proper-induced-subgraph part of criticality. -/
theorem support_budget {k : ℕ} (hproper : ProperInducedBound G k)
    (B J : Finset V) (hB : G.IsIndepSet (B : Set V)) (hJ : J ⊂ B) :
    (supportBag G B J).card ≤ ((G.indepNum - B.card + J.card) * G.cliqueNum) ^ k := by
  calc
    (supportBag G B J).card ≤
        ((G.induce (↑(supportBag G B J) : Set V)).indepNum *
          (G.induce (↑(supportBag G B J) : Set V)).cliqueNum) ^ k :=
      hproper _ (supportBag_card_lt G B J hJ)
    _ ≤ ((G.indepNum - B.card + J.card) * G.cliqueNum) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (supportBag_indepNum_le G B J hB hJ.subset)
        (cliqueNum_induce_le G (↑(supportBag G B J) : Set V))) k

/-- Support budget for an independent host in a product-critical graph.
The bound `B.card ≤ G.indepNum` follows from independence and is not an extra hypothesis. -/
theorem critical_support_budget {k : ℕ} (hcrit : IsProductCritical G k)
    (B J : Finset V) (hB : G.IsIndepSet (B : Set V)) (hJ : J ⊂ B) :
    (supportBag G B J).card ≤ ((G.indepNum - B.card + J.card) * G.cliqueNum) ^ k :=
  support_budget G hcrit.2 B J hB hJ

end SignedSupport

section SupersetCounting

variable {V : Type*} [DecidableEq V]

/-- Count the `m`-subsets of `B` containing a prescribed subset `K` by deleting `K`.
This is the exact binomial count, not a union bound. -/
theorem card_powersetCard_supersets (B K : Finset V) {m : ℕ}
    (hKB : K ⊆ B) (hKm : K.card ≤ m) :
    ((B.powersetCard m).filter (fun J => K ⊆ J)).card =
      (B.card - K.card).choose (m - K.card) := by
  calc
    ((B.powersetCard m).filter (fun J => K ⊆ J)).card =
        ((B \ K).powersetCard (m - K.card)).card := by
      apply Finset.card_bij (fun J _ => J \ K)
      · intro J hJ
        obtain ⟨hJ, hKJ⟩ := Finset.mem_filter.mp hJ
        obtain ⟨hJB, hJm⟩ := Finset.mem_powersetCard.mp hJ
        apply Finset.mem_powersetCard.mpr
        refine ⟨?_, ?_⟩
        · intro x hx
          obtain ⟨hxJ, hxK⟩ := Finset.mem_sdiff.mp hx
          exact Finset.mem_sdiff.mpr ⟨hJB hxJ, hxK⟩
        · rw [Finset.card_sdiff_of_subset hKJ, hJm]
      · intro J₁ hJ₁ J₂ hJ₂ heq
        have hKJ₁ := (Finset.mem_filter.mp hJ₁).2
        have hKJ₂ := (Finset.mem_filter.mp hJ₂).2
        calc
          J₁ = (J₁ \ K) ∪ K := (Finset.sdiff_union_of_subset hKJ₁).symm
          _ = (J₂ \ K) ∪ K := by rw [heq]
          _ = J₂ := Finset.sdiff_union_of_subset hKJ₂
      · intro L hL
        obtain ⟨hLsub, hLcard⟩ := Finset.mem_powersetCard.mp hL
        have hdisj : Disjoint K L := by
          apply Finset.disjoint_left.mpr
          intro x hxK hxL
          exact (Finset.mem_sdiff.mp (hLsub hxL)).2 hxK
        refine ⟨K ∪ L, ?_, Finset.union_sdiff_cancel_left hdisj⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.subset_union_left⟩
        · exact Finset.union_subset hKB (hLsub.trans Finset.sdiff_subset)
        · rw [Finset.card_union_of_disjoint hdisj, hLcard]
          omega
    _ = (B.card - K.card).choose (m - K.card) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hKB]

/-- Any subset of size at most `s` is in at least `choose (|B|-s) (m-s)`
`m`-subsets of `B`. Extend it to an `s`-subset and count its supersets exactly. -/
theorem choose_le_card_powersetCard_supersets (B K : Finset V) {s m : ℕ}
    (hKB : K ⊆ B) (hKs : K.card ≤ s) (hsm : s ≤ m) (hmB : m ≤ B.card) :
    (B.card - s).choose (m - s) ≤
      ((B.powersetCard m).filter (fun J => K ⊆ J)).card := by
  obtain ⟨T, hKT, hTB, hTcard⟩ :=
    Finset.exists_subsuperset_card_eq hKB hKs (hsm.trans hmB)
  calc
    (B.card - s).choose (m - s) =
        ((B.powersetCard m).filter (fun J => T ⊆ J)).card := by
      rw [card_powersetCard_supersets B T hTB (by omega), hTcard]
    _ ≤ ((B.powersetCard m).filter (fun J => K ⊆ J)).card := by
      apply Finset.card_le_card
      intro J hJ
      obtain ⟨hJ, hTJ⟩ := Finset.mem_filter.mp hJ
      exact Finset.mem_filter.mpr ⟨hJ, hKT.trans hTJ⟩

end SupersetCounting

section PartialHost

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices with signed support of size at most `s`, including host vertices
when `1 ≤ s`. -/
def lowSupport (B : Finset V) (s : ℕ) : Finset V :=
  Finset.univ.filter (fun x => (signedSupport G B x).card ≤ s)

@[simp] theorem mem_lowSupport (B : Finset V) (s : ℕ) (x : V) :
    x ∈ lowSupport G B s ↔ (signedSupport G B x).card ≤ s := by
  simp only [lowSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A low-support vertex belongs to at least the stated number of `m`-bags. -/
theorem lowSupport_bag_multiplicity (B : Finset V) {s m : ℕ}
    (hsm : s ≤ m) (hmB : m ≤ B.card) {x : V} (hx : x ∈ lowSupport G B s) :
    (B.card - s).choose (m - s) ≤
      ((B.powersetCard m).filter (fun J => x ∈ supportBag G B J)).card := by
  simpa only [mem_supportBag] using choose_le_card_powersetCard_supersets B
    (signedSupport G B x) (signedSupport_subset G B x)
    ((mem_lowSupport G B s x).mp hx) hsm hmB

/-- The binomial-loss-free partial-host inequality. Double-count all incidences
between low-support vertices and `m`-subsets of the independent host. Each vertex
is counted at least `choose (|B|-s) (m-s)` times; each bag has its support budget.
As with `support_budget`, the proper-induced bound alone suffices. -/
theorem partial_host_inequality {k : ℕ} (hproper : ProperInducedBound G k)
    (B : Finset V) (hB : G.IsIndepSet (B : Set V)) {s m : ℕ}
    (hsm : s ≤ m) (hmB : m < B.card) :
    (lowSupport G B s).card * (B.card - s).choose (m - s) ≤
      B.card.choose m * ((G.indepNum - B.card + m) * G.cliqueNum) ^ k := by
  have hcount := Finset.card_mul_le_card_mul
    (fun x J => x ∈ supportBag G B J)
    (s := lowSupport G B s) (t := B.powersetCard m)
    (m := (B.card - s).choose (m - s))
    (n := ((G.indepNum - B.card + m) * G.cliqueNum) ^ k)
    (fun x hx => lowSupport_bag_multiplicity G B hsm hmB.le hx) (by
      intro J hJ
      obtain ⟨hJB, hJm⟩ := Finset.mem_powersetCard.mp hJ
      have hJproper : J ⊂ B := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hJB, ?_⟩
        intro heq
        have := congrArg Finset.card heq
        omega
      calc
        (Finset.bipartiteBelow (fun x J => x ∈ supportBag G B J)
            (lowSupport G B s) J).card ≤ (supportBag G B J).card := by
          apply Finset.card_le_card
          intro x hx
          exact (Finset.mem_filter.mp hx).2
        _ ≤ ((G.indepNum - B.card + J.card) * G.cliqueNum) ^ k :=
          support_budget G hproper B J hB hJproper
        _ = ((G.indepNum - B.card + m) * G.cliqueNum) ^ k := by rw [hJm])
  simpa only [Finset.card_powersetCard] using hcount

/-- The requested partial-host inequality for product-critical graphs. -/
theorem critical_partial_host_inequality {k : ℕ} (hcrit : IsProductCritical G k)
    (B : Finset V) (hB : G.IsIndepSet (B : Set V)) {s m : ℕ}
    (hsm : s ≤ m) (hmB : m < B.card) :
    (lowSupport G B s).card * (B.card - s).choose (m - s) ≤
      B.card.choose m * ((G.indepNum - B.card + m) * G.cliqueNum) ^ k :=
  partial_host_inequality G hcrit.2 B hB hsm hmB

end PartialHost

section Complement

variable {V : Type*}

/-- Complementation commutes with passing to an induced graph. -/
theorem induce_compl_eq (G : SimpleGraph V) (S : Set V) :
    Gᶜ.induce S = (G.induce S)ᶜ := by
  ext x y
  simp only [induce_adj, compl_adj, Subtype.coe_ne_coe]

variable [Fintype V] {G : SimpleGraph V} {k : ℕ}

/-- The proper-subgraph product bound is invariant under complementation. -/
theorem properInducedBound_compl (hproper : ProperInducedBound G k) :
    ProperInducedBound Gᶜ k := by
  intro S hS
  simpa only [induce_compl_eq, indepNum_compl, cliqueNum_compl, Nat.mul_comm]
    using hproper S hS

/-- Product-criticality is invariant under complementation. -/
theorem isProductCritical_compl (hcrit : IsProductCritical G k) :
    IsProductCritical Gᶜ k := by
  refine ⟨?_, properInducedBound_compl hcrit.2⟩
  simpa only [indepNum_compl, cliqueNum_compl, Nat.mul_comm] using hcrit.1

end Complement

section CliqueHost

variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- For the complementary signed support, an outside vertex is supported on
its nonneighbors in the host. Inside the host its support is still a singleton. -/
theorem signedSupport_compl_of_notMem {B : Finset V} {x : V} (hx : x ∉ B) :
    signedSupport Gᶜ B x = B.filter (fun y => ¬ G.Adj x y) := by
  rw [signedSupport_of_notMem Gᶜ hx]
  ext y
  simp only [Finset.mem_filter, compl_adj]
  constructor
  · rintro ⟨hy, _, hxy⟩
    exact ⟨hy, hxy⟩
  · rintro ⟨hy, hxy⟩
    refine ⟨hy, ?_, hxy⟩
    rintro rfl
    exact hx hy

variable [Fintype V]

/-- The complementary bag for a clique host is complete to the unused host. -/
theorem clique_supportBag_complete (B J : Finset V) (hB : G.IsClique (B : Set V)) :
    ∀ x ∈ supportBag Gᶜ B J, ∀ y ∈ B \ J, G.Adj x y := by
  intro x hx y hy
  have hne : x ≠ y := by
    rintro rfl
    exact Finset.disjoint_left.mp (supportBag_disjoint Gᶜ B J) hx hy
  by_contra hxy
  have hBindep : Gᶜ.IsIndepSet (B : Set V) := (isIndepSet_compl G).mpr hB
  exact supportBag_anticomplete Gᶜ B J hBindep x hx y hy
    ((compl_adj G x y).mpr ⟨hne, hxy⟩)

/-- Clique-number budget, obtained from the independent-host budget by complementation. -/
theorem clique_supportBag_cliqueNum_le (B J : Finset V)
    (hB : G.IsClique (B : Set V)) (hJ : J ⊆ B) :
    (G.induce (↑(supportBag Gᶜ B J) : Set V)).cliqueNum ≤
      G.cliqueNum - B.card + J.card := by
  have hBindep : Gᶜ.IsIndepSet (B : Set V) := (isIndepSet_compl G).mpr hB
  simpa only [induce_compl_eq, indepNum_compl] using
    supportBag_indepNum_le Gᶜ B J hBindep hJ

/-- Cardinality support budget for a clique host, using signed nonneighbor supports. -/
theorem clique_support_budget {k : ℕ} (hproper : ProperInducedBound G k)
    (B J : Finset V) (hB : G.IsClique (B : Set V)) (hJ : J ⊂ B) :
    (supportBag Gᶜ B J).card ≤ ((G.cliqueNum - B.card + J.card) * G.indepNum) ^ k := by
  have hBindep : Gᶜ.IsIndepSet (B : Set V) := (isIndepSet_compl G).mpr hB
  simpa only [indepNum_compl, cliqueNum_compl] using
    support_budget Gᶜ (properInducedBound_compl hproper) B J hBindep hJ

/-- Critical-graph version of the clique-host support budget. -/
theorem critical_clique_support_budget {k : ℕ} (hcrit : IsProductCritical G k)
    (B J : Finset V) (hB : G.IsClique (B : Set V)) (hJ : J ⊂ B) :
    (supportBag Gᶜ B J).card ≤ ((G.cliqueNum - B.card + J.card) * G.indepNum) ^ k :=
  clique_support_budget G hcrit.2 B J hB hJ

/-- Complementary binomial-loss-free partial-host inequality for a clique host. -/
theorem clique_partial_host_inequality {k : ℕ} (hproper : ProperInducedBound G k)
    (B : Finset V) (hB : G.IsClique (B : Set V)) {s m : ℕ}
    (hsm : s ≤ m) (hmB : m < B.card) :
    (lowSupport Gᶜ B s).card * (B.card - s).choose (m - s) ≤
      B.card.choose m * ((G.cliqueNum - B.card + m) * G.indepNum) ^ k := by
  have hBindep : Gᶜ.IsIndepSet (B : Set V) := (isIndepSet_compl G).mpr hB
  simpa only [indepNum_compl, cliqueNum_compl] using
    partial_host_inequality Gᶜ (properInducedBound_compl hproper) B hBindep hsm hmB

/-- Critical-graph version of the complementary partial-host inequality. -/
theorem critical_clique_partial_host_inequality {k : ℕ}
    (hcrit : IsProductCritical G k) (B : Finset V) (hB : G.IsClique (B : Set V))
    {s m : ℕ} (hsm : s ≤ m) (hmB : m < B.card) :
    (lowSupport Gᶜ B s).card * (B.card - s).choose (m - s) ≤
      B.card.choose m * ((G.cliqueNum - B.card + m) * G.indepNum) ^ k :=
  clique_partial_host_inequality G hcrit.2 B hB hsm hmB

end CliqueHost

end Auxiliary.CriticalSupport

/- Axiom audit: all public theorems. Only propext, Classical.choice, and
Quot.sound occur; no additional axioms are assumed. -/

#print axioms Auxiliary.CriticalSupport.card_pos_of_critical
#print axioms Auxiliary.CriticalSupport.single_deletion_bound
#print axioms Auxiliary.CriticalSupport.card_eq_product_pow_add_one
#print axioms Auxiliary.CriticalSupport.single_deletion_parameters
#print axioms Auxiliary.CriticalSupport.indepNum_delete_singleton
#print axioms Auxiliary.CriticalSupport.cliqueNum_delete_singleton
#print axioms Auxiliary.CriticalSupport.indepNum_induce_add_card_le
#print axioms Auxiliary.CriticalSupport.signedSupport_of_mem
#print axioms Auxiliary.CriticalSupport.signedSupport_of_notMem
#print axioms Auxiliary.CriticalSupport.signedSupport_subset
#print axioms Auxiliary.CriticalSupport.mem_supportBag
#print axioms Auxiliary.CriticalSupport.mem_supportBag_of_mem_host
#print axioms Auxiliary.CriticalSupport.supportBag_disjoint
#print axioms Auxiliary.CriticalSupport.supportBag_anticomplete
#print axioms Auxiliary.CriticalSupport.supportBag_card_lt
#print axioms Auxiliary.CriticalSupport.supportBag_indepNum_le
#print axioms Auxiliary.CriticalSupport.support_budget
#print axioms Auxiliary.CriticalSupport.critical_support_budget
#print axioms Auxiliary.CriticalSupport.card_powersetCard_supersets
#print axioms Auxiliary.CriticalSupport.choose_le_card_powersetCard_supersets
#print axioms Auxiliary.CriticalSupport.mem_lowSupport
#print axioms Auxiliary.CriticalSupport.lowSupport_bag_multiplicity
#print axioms Auxiliary.CriticalSupport.partial_host_inequality
#print axioms Auxiliary.CriticalSupport.critical_partial_host_inequality
#print axioms Auxiliary.CriticalSupport.induce_compl_eq
#print axioms Auxiliary.CriticalSupport.properInducedBound_compl
#print axioms Auxiliary.CriticalSupport.isProductCritical_compl
#print axioms Auxiliary.CriticalSupport.signedSupport_compl_of_notMem
#print axioms Auxiliary.CriticalSupport.clique_supportBag_complete
#print axioms Auxiliary.CriticalSupport.clique_supportBag_cliqueNum_le
#print axioms Auxiliary.CriticalSupport.clique_support_budget
#print axioms Auxiliary.CriticalSupport.critical_clique_support_budget
#print axioms Auxiliary.CriticalSupport.clique_partial_host_inequality
#print axioms Auxiliary.CriticalSupport.critical_clique_partial_host_inequality
