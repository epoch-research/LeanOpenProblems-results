import FormalConjecturesUtil

/-!
# Critical triple colorings and their one-vertex links

This file is independent of the proposed quantitative Ramsey bounds. It uses only the
minimum defining `Combinatorics.hypergraphRamsey 3 n`: when this number is positive,
there is a coloring on one fewer vertex with no monochromatic `n`-set, but every
one-vertex extension has such a set. The resulting link criterion is recorded explicitly.
A duplication argument also forces monochromatic near-cores through any old vertex,
with their petals on the prescribed side of a red/blue partition. These are qualitative
foundations only; no quantitative Ramsey bound or original conjecture is proved here.

Colors are Booleans (`false` = red, `true` = blue). Colorings are defined on all finsets;
only their values on triples (and, for links, pairs) are constrained.
-/

set_option autoImplicit false

namespace CriticalColoring

variable {α β : Type*}

/-- Every triple in `S` has color `b`. No condition is imposed on other sizes. -/
def MonoTripleOn (c : Finset α → Bool) (S : Finset α) (b : Bool) : Prop :=
  ∀ e : Finset α, e ⊆ S → e.card = 3 → c e = b

/-- A monochromatic complete triple hypergraph on exactly `n` vertices. -/
def HasMonoTripleSet (c : Finset α → Bool) (n : ℕ) : Prop :=
  ∃ S : Finset α, S.card = n ∧ ∃ b : Bool, MonoTripleOn c S b

/-- The old vertices of a monochromatic `n`-set through a newly added vertex. -/
def LinkWitness (c ℓ : Finset α → Bool) (n : ℕ) : Prop :=
  ∃ S : Finset α, S.card = n - 1 ∧ ∃ b : Bool,
    MonoTripleOn c S b ∧
      ∀ e : Finset α, e ⊆ S → e.card = 2 → ℓ e = b

/-- A bad coloring for which every possible one-vertex link has a witness. -/
def IsCritical (c : Finset α → Bool) (n : ℕ) : Prop :=
  ¬ HasMonoTripleSet c n ∧ ∀ ℓ : Finset α → Bool, LinkWitness c ℓ n

/-- The defining Ramsey property, with the target size first. -/
def RamseyProperty (n m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool, HasMonoTripleSet c n

/-- The set whose natural-number infimum defines the triple Ramsey number. -/
def RamseySet (n : ℕ) : Set ℕ := {m | RamseyProperty n m}

theorem hypergraphRamsey_eq_sInf (n : ℕ) :
    Combinatorics.hypergraphRamsey 3 n = sInf (RamseySet n) := rfl

/-- Positivity rules out the empty defining set, whose natural infimum is zero. -/
theorem ramseySet_nonempty {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n) : (RamseySet n).Nonempty :=
  Nat.nonempty_of_pos_sInf hR

/-- A positive Ramsey number itself satisfies the defining Ramsey property. -/
theorem ramseyProperty_ramsey {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n) :
    RamseyProperty n (Combinatorics.hypergraphRamsey 3 n) :=
  Nat.sInf_mem (ramseySet_nonempty hR)

/-- Every size strictly below the Ramsey number admits a bad coloring. -/
theorem exists_bad_coloring_of_lt {n N : ℕ}
    (hN : N < Combinatorics.hypergraphRamsey 3 n) :
    ∃ c : Finset (Fin N) → Bool, ¬ HasMonoTripleSet c n := by
  classical
  by_contra h
  have hprop : RamseyProperty n N := by
    intro c
    by_contra hc
    exact h ⟨c, hc⟩
  have hle : Combinatorics.hypergraphRamsey 3 n ≤ N := Nat.sInf_le hprop
  omega

/-- Transport a monochromatic set along an equivalence of vertex types. -/
theorem hasMonoTripleSet_of_equiv (f : α ≃ β) {c : Finset β → Bool} {n : ℕ}
    (h : HasMonoTripleSet (fun e => c (e.map f.toEmbedding)) n) :
    HasMonoTripleSet c n := by
  obtain ⟨S, hS, b, hm⟩ := h
  refine ⟨S.map f.toEmbedding, by simpa using hS, b, ?_⟩
  intro e he hc
  have he' : e.map f.symm.toEmbedding ⊆ S := Finset.map_symm_subset.mpr he
  have hm' := hm (e.map f.symm.toEmbedding) he' (by simpa using hc)
  simpa [Finset.map_map] using hm'

/-- The Ramsey property on any finite type with the same cardinality. -/
theorem ramsey_on_type [Fintype α] {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n)
    (hcard : Fintype.card α = Combinatorics.hypergraphRamsey 3 n)
    (c : Finset α → Bool) : HasMonoTripleSet c n := by
  let f : Fin (Combinatorics.hypergraphRamsey 3 n) ≃ α :=
    Fintype.equivOfCardEq (by simpa using hcard.symm)
  exact hasMonoTripleSet_of_equiv f
    (ramseyProperty_ramsey hR (fun e => c (e.map f.toEmbedding)))

section OneVertex

variable [DecidableEq α]

/-- Add the vertex `none`. On triples through it use the link on the remaining pair;
on triples of old vertices use `c`. Values at other sizes are immaterial. -/
def oneVertexExtension (c ℓ : Finset α → Bool) (e : Finset (Option α)) : Bool :=
  if none ∈ e then ℓ e.eraseNone else c e.eraseNone

@[simp] theorem oneVertexExtension_map_some (c ℓ : Finset α → Bool) (e : Finset α) :
    oneVertexExtension c ℓ (e.map Function.Embedding.some) = c e := by
  simp [oneVertexExtension]

@[simp] theorem oneVertexExtension_insertNone (c ℓ : Finset α → Bool) (e : Finset α) :
    oneVertexExtension c ℓ e.insertNone = ℓ e := by
  simp [oneVertexExtension]

omit [DecidableEq α] in
/-- Mapping old vertices into an Option-finset is the inverse membership operation
of erasing `none`. -/
theorem map_some_subset_iff {S : Finset α} {T : Finset (Option α)} :
    S.map Function.Embedding.some ⊆ T ↔ S ⊆ T.eraseNone := by
  constructor
  · intro h a ha
    exact Finset.mem_eraseNone.mpr (h (Finset.mem_map.mpr ⟨a, ha, rfl⟩))
  · intro h o ho
    rcases Finset.mem_map.mp ho with ⟨a, ha, rfl⟩
    exact Finset.mem_eraseNone.mp (h ha)

/-- Restricting a monochromatic extension-set to its old vertices preserves its color. -/
theorem monoTripleOn_eraseNone {c ℓ : Finset α → Bool}
    {T : Finset (Option α)} {b : Bool} (hm : MonoTripleOn (oneVertexExtension c ℓ) T b) :
    MonoTripleOn c T.eraseNone b := by
  intro e he hc
  simpa using hm (e.map Function.Embedding.some) (map_some_subset_iff.mpr he)
    (by simpa using hc)

/-- A monochromatic extension-set must contain the new vertex if the old coloring
has no monochromatic set of that size. Erasing it gives precisely a link witness. -/
theorem linkWitness_of_extension {c ℓ : Finset α → Bool} {n : ℕ}
    (hbad : ¬ HasMonoTripleSet c n)
    (h : HasMonoTripleSet (oneVertexExtension c ℓ) n) : LinkWitness c ℓ n := by
  obtain ⟨T, hT, b, hm⟩ := h
  have hnone : none ∈ T := by
    by_contra hn
    exact hbad ⟨T.eraseNone, (Finset.card_eraseNone_of_not_mem hn).trans hT,
      b, monoTripleOn_eraseNone hm⟩
  refine ⟨T.eraseNone, by rw [Finset.card_eraseNone_of_mem hnone, hT],
    b, monoTripleOn_eraseNone hm, ?_⟩
  intro e he hc
  have hesub : e.insertNone ⊆ T := by
    intro a ha
    cases a with
    | none => exact hnone
    | some a => exact Finset.mem_eraseNone.mp (he (Finset.some_mem_insertNone.mp ha))
  simpa using hm e.insertNone hesub (by simp [hc])

/-- Conversely, old triples and link pairs of one color form a monochromatic
extension-set after adjoining `none`. -/
theorem monoTripleOn_insertNone {c ℓ : Finset α → Bool} {S : Finset α} {b : Bool}
    (hc : MonoTripleOn c S b)
    (hℓ : ∀ e : Finset α, e ⊆ S → e.card = 2 → ℓ e = b) :
    MonoTripleOn (oneVertexExtension c ℓ) S.insertNone b := by
  intro e he hcard
  have heold : e.eraseNone ⊆ S := by
    intro a ha
    exact Finset.some_mem_insertNone.mp (he (Finset.mem_eraseNone.mp ha))
  by_cases hn : none ∈ e
  · rw [oneVertexExtension, if_pos hn]
    exact hℓ e.eraseNone heold (by rw [Finset.card_eraseNone_of_mem hn, hcard])
  · rw [oneVertexExtension, if_neg hn]
    exact hc e.eraseNone heold (by rw [Finset.card_eraseNone_of_not_mem hn, hcard])

/-- For a positive target size, a link witness supplies a monochromatic extension-set. -/
theorem extension_of_linkWitness {c ℓ : Finset α → Bool} {n : ℕ}
    (hn : 0 < n) (h : LinkWitness c ℓ n) :
    HasMonoTripleSet (oneVertexExtension c ℓ) n := by
  obtain ⟨S, hS, b, hc, hℓ⟩ := h
  refine ⟨S.insertNone, ?_, b, monoTripleOn_insertNone hc hℓ⟩
  rw [Finset.card_insertNone, hS]
  omega

/-- The exact one-vertex link criterion for a coloring with no old monochromatic `n`-set. -/
theorem extension_iff_linkWitness {c ℓ : Finset α → Bool} {n : ℕ}
    (hn : 0 < n) (hbad : ¬ HasMonoTripleSet c n) :
    HasMonoTripleSet (oneVertexExtension c ℓ) n ↔ LinkWitness c ℓ n :=
  ⟨linkWitness_of_extension hbad, extension_of_linkWitness hn⟩

end OneVertex

/-- Every bad coloring on `R - 1` vertices is critical, provided `R > 0`.
The equivalence used here has cardinality `(R - 1) + 1 = R`. -/
theorem isCritical_of_no_mono {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n)
    {c : Finset (Fin (Combinatorics.hypergraphRamsey 3 n - 1)) → Bool}
    (hbad : ¬ HasMonoTripleSet c n) : IsCritical c n := by
  refine ⟨hbad, fun ℓ => linkWitness_of_extension hbad ?_⟩
  apply ramsey_on_type hR
  simp only [Fintype.card_option, Fintype.card_fin]
  omega

/-- **Critical-coloring existence.** In particular this holds for every `n ≥ 3`
with positive triple Ramsey number. No quantitative estimate is used or claimed. -/
theorem exists_critical_coloring {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n) :
    ∃ c : Finset (Fin (Combinatorics.hypergraphRamsey 3 n - 1)) → Bool,
      IsCritical c n := by
  obtain ⟨c, hc⟩ := exists_bad_coloring_of_lt (n := n)
    (N := Combinatorics.hypergraphRamsey 3 n - 1) (by omega)
  exact ⟨c, isCritical_of_no_mono hR hc⟩

/-- The main conclusion with the link criterion fully expanded. The same bad coloring
works for every link; both its old triples and the link pairs have the same color. -/
theorem exists_critical_coloring_with_links {n : ℕ}
    (hR : 0 < Combinatorics.hypergraphRamsey 3 n) :
    ∃ c : Finset (Fin (Combinatorics.hypergraphRamsey 3 n - 1)) → Bool,
      ¬ HasMonoTripleSet c n ∧
      ∀ ℓ : Finset (Fin (Combinatorics.hypergraphRamsey 3 n - 1)) → Bool,
        ∃ S, S.card = n - 1 ∧ ∃ b : Bool,
          (∀ e ⊆ S, e.card = 3 → c e = b) ∧
          (∀ e ⊆ S, e.card = 2 → ℓ e = b) :=
  exists_critical_coloring hR

section Duplication

variable [DecidableEq α]

/-- A monochromatic `(n - 1)`-vertex near-core through `v`, represented by its
`(n - 2)`-vertex petal, which does not contain `v`. -/
def MonoNearCore (c : Finset α → Bool) (n : ℕ) (v : α) (b : Bool)
    (P : Finset α) : Prop :=
  P.card = n - 2 ∧ v ∉ P ∧ MonoTripleOn c (insert v P) b

theorem MonoNearCore.card {c : Finset α → Bool} {n : ℕ} {v : α} {b : Bool}
    {P : Finset α} (h : MonoNearCore c n v b P) (hn : 2 ≤ n) :
    (insert v P).card = n - 1 := by
  rw [Finset.card_insert_of_notMem h.2.1, h.1]
  omega

/-- The link of a new copy of `v`: pairs avoiding `v` inherit the old triple color;
for a pair `{v,a}`, red means `a ∈ X` and blue means `a ∉ X`. -/
def duplicationLink (c : Finset α → Bool) (v : α) (X : Finset α)
    (e : Finset α) : Bool :=
  if v ∈ e then (if e.erase v ⊆ X then false else true) else c (insert v e)

@[simp] theorem duplicationLink_of_not_mem (c : Finset α → Bool) (v : α)
    (X : Finset α) {e : Finset α} (hv : v ∉ e) :
    duplicationLink c v X e = c (insert v e) := by
  simp [duplicationLink, hv]

@[simp] theorem duplicationLink_pair (c : Finset α → Bool) (v : α)
    (X : Finset α) {a : α} (ha : a ≠ v) :
    duplicationLink c v X {v, a} = if a ∈ X then false else true := by
  simp [duplicationLink, ha.symm]

/-- Collapsing the copied vertex to `v` preserves all the relevant triple colors.
When `v ∉ S`, this would turn a duplication-link witness into an old `n`-set. -/
theorem monoTripleOn_insert_of_duplicationLink {c : Finset α → Bool}
    {v : α} {X S : Finset α} {b : Bool} (hc : MonoTripleOn c S b)
    (hℓ : ∀ e : Finset α, e ⊆ S → e.card = 2 → duplicationLink c v X e = b) :
    MonoTripleOn c (insert v S) b := by
  intro e he hcard
  by_cases hv : v ∈ e
  · have he' : e.erase v ⊆ S := Finset.subset_insert_iff.mp he
    have hcard' : (e.erase v).card = 2 := by
      rw [Finset.card_erase_of_mem hv, hcard]
    have hcolor := hℓ (e.erase v) he' hcard'
    simpa [Finset.insert_erase hv] using hcolor
  · exact hc e ((Finset.subset_insert_iff_of_notMem hv).mp he) hcard

/-- A witness for a duplication link must use the original vertex `v`. -/
theorem duplication_witness_contains_vertex {c : Finset α → Bool} {n : ℕ}
    (hn : 0 < n) (hbad : ¬ HasMonoTripleSet c n)
    {v : α} {X S : Finset α} {b : Bool} (hS : S.card = n - 1)
    (hc : MonoTripleOn c S b)
    (hℓ : ∀ e : Finset α, e ⊆ S → e.card = 2 → duplicationLink c v X e = b) :
    v ∈ S := by
  by_contra hv
  apply hbad
  refine ⟨insert v S, ?_, b, monoTripleOn_insert_of_duplicationLink hc hℓ⟩
  rw [Finset.card_insert_of_notMem hv, hS]
  omega

/-- **Duplication criterion.** For any critical coloring, vertex `v`, and set `X`,
there is a red near-core through `v` with its petal in `X`, or a blue near-core
through `v` with its petal disjoint from `X`. No finiteness of the ambient type is needed.
In particular the result applies when `X` is a subset of the old vertices other than `v`. -/
theorem duplication_criterion {c : Finset α → Bool} {n : ℕ}
    (hn : 3 ≤ n) (hcrit : IsCritical c n) (v : α) (X : Finset α) :
    (∃ P ⊆ X, MonoNearCore c n v false P) ∨
      (∃ P, Disjoint P X ∧ MonoNearCore c n v true P) := by
  obtain ⟨S, hS, b, hc, hℓ⟩ := hcrit.2 (duplicationLink c v X)
  have hv : v ∈ S :=
    duplication_witness_contains_vertex (by omega) hcrit.1 hS hc hℓ
  have hcore : MonoNearCore c n v b (S.erase v) := by
    refine ⟨?_, Finset.notMem_erase v S, ?_⟩
    · rw [Finset.card_erase_of_mem hv, hS]
      omega
    · simpa only [Finset.insert_erase hv] using hc
  have hpairs (a : α) (ha : a ∈ S.erase v) :
      (if a ∈ X then false else true) = b := by
    have hav : a ≠ v := Finset.ne_of_mem_erase ha
    have haS : a ∈ S := Finset.mem_of_mem_erase ha
    have hsub : ({v, a} : Finset α) ⊆ S :=
      Finset.insert_subset hv (Finset.singleton_subset_iff.mpr haS)
    simpa only [duplicationLink_pair c v X hav] using
      hℓ {v, a} hsub (Finset.card_pair hav.symm)
  cases b with
  | false =>
    left
    refine ⟨S.erase v, ?_, hcore⟩
    intro a ha
    have hcolor := hpairs a ha
    by_contra hax
    simp [hax] at hcolor
  | true =>
    right
    refine ⟨S.erase v, Finset.disjoint_left.mpr ?_, hcore⟩
    intro a ha hax
    have hcolor := hpairs a ha
    simp [hax] at hcolor

/-- The finite-vertex version, with the blue petal explicitly inside the complement
of `X` among vertices different from `v`. -/
theorem duplication_criterion_finite [Fintype α] {c : Finset α → Bool} {n : ℕ}
    (hn : 3 ≤ n) (hcrit : IsCritical c n) (v : α) (X : Finset α) :
    (∃ P ⊆ X, MonoNearCore c n v false P) ∨
      (∃ P ⊆ Finset.univ \ insert v X, MonoNearCore c n v true P) := by
  rcases duplication_criterion hn hcrit v X with hred | ⟨P, hdisj, hcore⟩
  · exact Or.inl hred
  · right
    refine ⟨P, ?_, hcore⟩
    intro a ha
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ?_⟩
    simp only [Finset.mem_insert]
    rintro (rfl | hax)
    · exact hcore.2.1 ha
    · exact Finset.disjoint_left.mp hdisj ha hax

end Duplication

namespace Examples

/-- The diagonal base case of the defining Ramsey number. -/
theorem ramsey_three : Combinatorics.hypergraphRamsey 3 3 = 3 :=
  Combinatorics.hypergraphRamsey_self 3

/-- No coloring on two vertices has a monochromatic three-vertex set. -/
theorem no_mono_three_fin_two (c : Finset (Fin 2) → Bool) :
    ¬ HasMonoTripleSet c 3 := by
  rintro ⟨S, hS, _⟩
  have hbound : S.card ≤ 2 := by simpa using Finset.card_le_univ S
  omega

/-- The link criterion on `Fin 2` uses both vertices and the color of their unique pair.
Its old-triple condition is vacuous, not an extra assumption about the coloring. -/
theorem linkWitness_three_fin_two (c ℓ : Finset (Fin 2) → Bool) :
    LinkWitness c ℓ 3 := by
  refine ⟨Finset.univ, by simp, ℓ Finset.univ, ?_, ?_⟩
  · intro e _ he
    have hbound : e.card ≤ 2 := by simpa using Finset.card_le_univ e
    omega
  · intro e _ he
    have heq : e = Finset.univ := Finset.eq_univ_of_card e (by simpa using he)
    rw [heq]

/-- Direct sanity check: every coloring on `Fin 2` is critical for target size three. -/
theorem every_coloring_fin_two_critical (c : Finset (Fin 2) → Bool) : IsCritical c 3 :=
  ⟨no_mono_three_fin_two c, linkWitness_three_fin_two c⟩

/-- Sanity check of the general existence theorem after substituting `R₃(3) = 3`. -/
theorem critical_fin_two_via_ramsey :
    ∃ c : Finset (Fin 2) → Bool, IsCritical c 3 := by
  have hR : 0 < Combinatorics.hypergraphRamsey 3 3 := by rw [ramsey_three]; decide
  have h := exists_critical_coloring hR
  rw [ramsey_three] at h
  exact h

/-- The optional duplication criterion also applies to the smallest critical example. -/
theorem duplication_fin_two (c : Finset (Fin 2) → Bool) (v : Fin 2) (X : Finset (Fin 2)) :
    (∃ P ⊆ X, MonoNearCore c 3 v false P) ∨
      (∃ P ⊆ Finset.univ \ insert v X, MonoNearCore c 3 v true P) :=
  duplication_criterion_finite (by decide) (every_coloring_fin_two_critical c) v X

end Examples

end CriticalColoring

#print axioms CriticalColoring.exists_critical_coloring
#print axioms CriticalColoring.exists_critical_coloring_with_links
#print axioms CriticalColoring.isCritical_of_no_mono
#print axioms CriticalColoring.linkWitness_of_extension
#print axioms CriticalColoring.extension_iff_linkWitness
#print axioms CriticalColoring.duplication_criterion
#print axioms CriticalColoring.duplication_criterion_finite
#print axioms CriticalColoring.Examples.every_coloring_fin_two_critical
#print axioms CriticalColoring.Examples.critical_fin_two_via_ramsey
#print axioms CriticalColoring.Examples.duplication_fin_two
