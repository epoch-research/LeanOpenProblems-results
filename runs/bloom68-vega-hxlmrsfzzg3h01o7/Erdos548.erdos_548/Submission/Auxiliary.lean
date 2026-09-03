import FormalConjecturesUtil

/-!
# Auxiliary infrastructure for the Erdős–Sós threshold

This file is independent of `Submission.Spec`: it does not import that file or use its
conjectural declarations.  The goal is an equivalence between two *universal statements*,
not a proof of the Erdős–Sós conjecture.

The disjoint union of two copies of a graph doubles its edge count.  A connected graph
contained in a disjoint union is contained in one of its summands.  These facts allow a
strict half-integral edge threshold to be replaced, universally, by a `+1` threshold.
-/

open SimpleGraph

namespace Erdos548.Auxiliary

section DisjointSum

variable {α β γ : Type*}

/-- The disjoint sum is the union of the graphs mapped into its two vertex summands. -/
theorem sum_eq_sup_map (G : SimpleGraph α) (H : SimpleGraph β) :
    G ⊕g H = G.map Function.Embedding.inl ⊔ H.map Function.Embedding.inr := by
  ext u v
  cases u <;> cases v <;> simp [SimpleGraph.map_adj]

/-- Edges supported on different summands cannot coincide, even as unordered pairs. -/
theorem disjoint_sym2_sum_images (s : Set (Sym2 α)) (t : Set (Sym2 β)) :
    Disjoint (Sym2.map (Sum.inl : α → α ⊕ β) '' s)
      (Sym2.map (Sum.inr : β → α ⊕ β) '' t) := by
  rw [Set.disjoint_left]
  rintro e ⟨e₁, _, rfl⟩ ⟨e₂, _, he⟩
  induction e₁ using Sym2.ind with
  | h a b =>
    induction e₂ using Sym2.ind with
    | h c d => simp at he

/-- The edge set of a disjoint sum, expressed as two disjoint images. -/
theorem edgeSet_sum_eq (G : SimpleGraph α) (H : SimpleGraph β) :
    (G ⊕g H).edgeSet =
      Sym2.map (Sum.inl : α → α ⊕ β) '' G.edgeSet ∪
      Sym2.map (Sum.inr : β → α ⊕ β) '' H.edgeSet := by
  rw [sum_eq_sup_map, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map,
    SimpleGraph.edgeSet_map]
  rfl

/-- Finite edge counts add under disjoint sum. -/
theorem ncard_edgeSet_sum [Finite α] [Finite β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard := by
  rw [edgeSet_sum_eq, Set.ncard_union_eq (disjoint_sym2_sum_images _ _),
    Set.ncard_image_of_injective _ (Sym2.map.injective Sum.inl_injective),
    Set.ncard_image_of_injective _ (Sym2.map.injective Sum.inr_injective)]

/-- In particular, duplicating a finite graph doubles its edge count. -/
theorem ncard_edgeSet_sum_self [Finite α] (G : SimpleGraph α) :
    (G ⊕g G).edgeSet.ncard = 2 * G.edgeSet.ncard := by
  rw [ncard_edgeSet_sum, two_mul]

/-- Edge-set cardinality is invariant under graph isomorphism (no finiteness needed). -/
theorem ncard_edgeSet_iso {G : SimpleGraph α} {H : SimpleGraph β} (e : G ≃g H) :
    G.edgeSet.ncard = H.edgeSet.ncard :=
  Set.ncard_congr' e.mapEdgeSet

/-- Reachable vertices in a disjoint sum lie in the same vertex summand. -/
theorem isLeft_eq_of_sum_reachable {G : SimpleGraph α} {H : SimpleGraph β}
    {u v : α ⊕ β} (h : (G ⊕g H).Reachable u v) : u.isLeft = v.isLeft := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
    have huv' : u.isLeft = v.isLeft := by
      cases u <;> cases v <;> simp_all
    exact huv'.trans ih

/-- A homomorphism from a connected graph to a disjoint sum has image in one summand. -/
theorem hom_range_sum {T : SimpleGraph γ} {G : SimpleGraph α} {H : SimpleGraph β}
    (hT : T.Connected) (f : T →g G ⊕g H) :
    (∀ v, ∃ a, f v = Sum.inl a) ∨ (∀ v, ∃ b, f v = Sum.inr b) := by
  obtain ⟨v₀⟩ := hT.nonempty
  have htag (v : γ) : (f v).isLeft = (f v₀).isLeft :=
    isLeft_eq_of_sum_reachable ((hT v v₀).map f)
  cases hv₀ : f v₀ with
  | inl a =>
    left
    intro v
    exact Sum.isLeft_iff.mp (by simpa [hv₀] using htag v)
  | inr b =>
    right
    intro v
    cases hv : f v with
    | inl a => simpa [hv, hv₀] using htag v
    | inr b => exact ⟨b, rfl⟩

/-- A connected graph has a copy in a disjoint sum iff it has a copy in a summand. -/
theorem isContained_sum_iff {T : SimpleGraph γ} {G : SimpleGraph α}
    {H : SimpleGraph β} (hT : T.Connected) :
    T.IsContained (G ⊕g H) ↔ T.IsContained G ∨ T.IsContained H := by
  constructor
  · rintro ⟨f⟩
    rcases hom_range_sum hT f.toHom with hleft | hright
    · choose g hg using hleft
      left
      refine ⟨{ toHom := { toFun := g, map_rel' := ?_ }, injective' := ?_ }⟩
      · intro u v huv
        simpa only [hg, SimpleGraph.sum_adj] using f.toHom.map_rel huv
      · intro u v huv
        apply f.injective
        rw [hg u, hg v]
        exact congrArg Sum.inl huv
    · choose g hg using hright
      right
      refine ⟨{ toHom := { toFun := g, map_rel' := ?_ }, injective' := ?_ }⟩
      · intro u v huv
        simpa only [hg, SimpleGraph.sum_adj] using f.toHom.map_rel huv
      · intro u v huv
        apply f.injective
        rw [hg u, hg v]
        exact congrArg Sum.inr huv
  · rintro (h | h)
    · exact h.trans ⟨SimpleGraph.Embedding.sumInl.toCopy⟩
    · exact h.trans ⟨SimpleGraph.Embedding.sumInr.toCopy⟩

/-- Duplicating a host graph does not change whether it contains a connected graph. -/
theorem isContained_sum_self_iff {T : SimpleGraph γ} {G : SimpleGraph α}
    (hT : T.Connected) : T.IsContained (G ⊕g G) ↔ T.IsContained G := by
  rw [isContained_sum_iff hT, or_self]

end DisjointSum

section Duplication

variable {n : ℕ}

/-- Two disjoint copies of `G`, relabelled on `Fin (2 * n)`. -/
def doubleGraph (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (2 * n)) :=
  (G ⊕g G).overFin (by simp [two_mul])

/-- The relabelling used in `doubleGraph` is a graph isomorphism. -/
noncomputable def doubleGraphIso (G : SimpleGraph (Fin n)) :
    G ⊕g G ≃g doubleGraph G :=
  (G ⊕g G).overFinIso (by simp [two_mul])

/-- Relabelled duplication still doubles the edge count. -/
theorem ncard_edgeSet_doubleGraph (G : SimpleGraph (Fin n)) :
    (doubleGraph G).edgeSet.ncard = 2 * G.edgeSet.ncard := by
  calc
    (doubleGraph G).edgeSet.ncard = (G ⊕g G).edgeSet.ncard :=
      (ncard_edgeSet_iso (doubleGraphIso G)).symm
    _ = 2 * G.edgeSet.ncard := ncard_edgeSet_sum_self G

/-- A connected graph is contained in the relabelled duplicate iff it is contained in `G`. -/
theorem isContained_doubleGraph_iff {α : Type*} {T : SimpleGraph α}
    {G : SimpleGraph (Fin n)} (hT : T.Connected) :
    T.IsContained (doubleGraph G) ↔ T.IsContained G :=
  (isContained_congr_right (doubleGraphIso G)).symm.trans (isContained_sum_self_iff hT)

end Duplication

section Thresholds

/-- Doubling a strict half-integral threshold supplies a gap of at least one.

The arithmetic is performed in `ℤ` and `ℚ`, so this also applies when `k = 0`:
there is no truncated natural-number subtraction in this lemma. -/
theorem doubled_threshold_of_strict (n k m : ℕ)
    (h : ((k : ℚ) - 1) / 2 * n < (m : ℚ)) :
    ((k : ℚ) - 1) / 2 * (2 * n : ℕ) + 1 ≤ (2 * m : ℕ) := by
  have hq : ((k : ℚ) - 1) * n < 2 * m := by linarith
  have hz : ((k : ℤ) - 1) * n < 2 * m := by exact_mod_cast hq
  have hz' : ((k : ℤ) - 1) * n + 1 ≤ 2 * m := Int.add_one_le_iff.mpr hz
  have hq' : ((k : ℚ) - 1) * n + 1 ≤ 2 * m := by exact_mod_cast hz'
  push_cast
  nlinarith

/-- The universally quantified `+1` formulation, restated without importing `Spec`. -/
def PlusOneStatement : Prop :=
  ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
    ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ) →
      ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G

/-- The usual universally quantified strict-threshold formulation of Erdős–Sós. -/
def StrictThresholdStatement : Prop :=
  ∀ (n k : ℕ), k + 1 ≤ n → ∀ G : SimpleGraph (Fin n),
    ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ) →
      ∀ T : SimpleGraph (Fin (k + 1)), T.IsTree → T.IsContained G

/-- The strict-threshold statement immediately implies the `+1` statement. -/
theorem plusOneStatement_of_strictThresholdStatement (h : StrictThresholdStatement) :
    PlusOneStatement := by
  intro n k hnk G hG T hT
  exact h n k hnk G (by linarith) T hT

/-- Apply the universal `+1` statement to two disjoint copies of the host graph. -/
theorem strictThresholdStatement_of_plusOneStatement (h : PlusOneStatement) :
    StrictThresholdStatement := by
  intro n k hnk G hG T hT
  have hnk' : k + 1 ≤ 2 * n := by omega
  have hG' : ((k : ℚ) - 1) / 2 * (2 * n : ℕ) + 1 ≤
      ((doubleGraph G).edgeSet.ncard : ℚ) := by
    rw [ncard_edgeSet_doubleGraph]
    exact doubled_threshold_of_strict n k G.edgeSet.ncard hG
  exact (isContained_doubleGraph_iff hT.isConnected).mp
    (h (2 * n) k hnk' (doubleGraph G) hG' T hT)

/-- Equivalence of the two universal formulations; neither conjecture is assumed or proved. -/
theorem plusOneStatement_iff_strictThresholdStatement :
    PlusOneStatement ↔ StrictThresholdStatement :=
  ⟨strictThresholdStatement_of_plusOneStatement, plusOneStatement_of_strictThresholdStatement⟩

end Thresholds

section SmallCases

/-- Every graph on a subsingleton vertex type is contained in every nonempty host. -/
theorem isContained_of_subsingleton {α β : Type*} [Subsingleton α] [Nonempty β]
    (T : SimpleGraph α) (G : SimpleGraph β) : T.IsContained G := by
  obtain ⟨v⟩ := ‹Nonempty β›
  refine ⟨{
    toHom := { toFun := fun _ => v, map_rel' := ?_ }
    injective' := fun _ _ _ => Subsingleton.elim _ _ }⟩
  intro x y hxy
  exact (hxy.ne (Subsingleton.elim x y)).elim

/-- A host edge contains every graph on two vertices, not only the two-vertex tree. -/
theorem fin_two_isContained_of_adj {α : Type*} (G : SimpleGraph α)
    {u v : α} (huv : G.Adj u v) (T : SimpleGraph (Fin 2)) : T.IsContained G := by
  let f : Fin 2 → α := fun i => if i = 0 then u else v
  refine ⟨{ toHom := { toFun := f, map_rel' := ?_ }, injective' := ?_ }⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [f, huv.symm]
  · intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [f, huv.ne, huv.ne.symm]

/-- A positive finite edge count suffices to contain any graph on two vertices. -/
theorem fin_two_isContained_of_ncard_pos {α : Type*} [Finite α]
    (G : SimpleGraph α) (hG : 0 < G.edgeSet.ncard) (T : SimpleGraph (Fin 2)) :
    T.IsContained G := by
  obtain ⟨e, he⟩ := (Set.ncard_pos (s := G.edgeSet)).mp hG
  induction e using Sym2.ind with
  | h u v => exact fin_two_isContained_of_adj G he T

/-- The strict-threshold conclusion for `k = 0` and `k = 1`.
In these cases the source graph need not even be assumed to be a tree. -/
theorem strictThreshold_of_k_le_one {n k : ℕ} (hk : k ≤ 1) (hnk : k + 1 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : ((k : ℚ) - 1) / 2 * n < (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) : T.IsContained G := by
  interval_cases k
  · letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact isContained_of_subsingleton (α := Fin 1) T G
  · apply fin_two_isContained_of_ncard_pos G _ T
    have hG' : (0 : ℚ) < (G.edgeSet.ncard : ℚ) := by simpa using hG
    exact_mod_cast hG'

/-- The `+1`-threshold conclusion for `k = 0` and `k = 1`, again without needing `IsTree`. -/
theorem plusOneThreshold_of_k_le_one {n k : ℕ} (hk : k ≤ 1) (hnk : k + 1 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ))
    (T : SimpleGraph (Fin (k + 1))) : T.IsContained G :=
  strictThreshold_of_k_le_one hk hnk G (by linarith) T

end SmallCases

end Erdos548.Auxiliary

/- Transitive axiom checks: only the standard Lean axioms should appear. -/

#print axioms Erdos548.Auxiliary.ncard_edgeSet_sum
#print axioms Erdos548.Auxiliary.isContained_sum_iff
#print axioms Erdos548.Auxiliary.doubled_threshold_of_strict
#print axioms Erdos548.Auxiliary.plusOneStatement_iff_strictThresholdStatement
#print axioms Erdos548.Auxiliary.strictThreshold_of_k_le_one
#print axioms Erdos548.Auxiliary.plusOneThreshold_of_k_le_one

