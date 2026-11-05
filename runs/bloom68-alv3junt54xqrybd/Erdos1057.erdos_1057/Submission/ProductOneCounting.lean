import FormalConjecturesUtil

/-!
# Product-one subsets under a Davenport-bound hypothesis

The pool `P` is finite, but neither its ambient type nor the commutative monoid
of labels needs to be finite. `DavenportBound P g D` is an explicit hypothesis:
every subset of `P` of size at least `D` contains a nonempty product-one subset.
No such bound is asserted for arbitrary monoids or groups.

A maximum-cardinality product-one subset leaves fewer than `D` elements.
Choosing one for each `t`-subset gives an injection into pairs `(T, S \ T)`.
Counting the second component by its cardinality gives the exact binomial-sum
bound. The count theorem works for every `t`, in particular when
`D + 1 ≤ t ≤ P.card`.
-/

namespace ProductOneCounting

variable {α G : Type*} [CommMonoid G]

/-- A Davenport bound relative to the finite pool and its labels.
This is a hypothesis, not an unconditional assertion about `G`. -/
def DavenportBound (P : Finset α) (g : α → G) (D : ℕ) : Prop :=
  ∀ S ⊆ P, D ≤ S.card →
    ∃ U : Finset α, U ⊆ S ∧ U.Nonempty ∧ (∏ a ∈ U, g a) = 1

/-- Any relative Davenport bound is positive, by considering the empty set. -/
theorem DavenportBound.one_le {P : Finset α} {g : α → G} {D : ℕ}
    (h : DavenportBound P g D) : 1 ≤ D := by
  by_contra hD
  have hzero : D = 0 := by omega
  obtain ⟨U, hU, hUne, _⟩ := h ∅ (Finset.empty_subset P) (by simp [hzero])
  exact hUne.ne_empty (Finset.subset_empty.mp hU)

/-- There is a maximum-cardinality product-one subset of `S`, and its
complement in `S` has cardinality less than the hypothesized Davenport bound. -/
theorem exists_maximal_product_one_subset [DecidableEq α] {P S : Finset α} {g : α → G} {D : ℕ}
    (h : DavenportBound P g D) (hSP : S ⊆ P) :
    ∃ T : Finset α, T ⊆ S ∧ (∏ a ∈ T, g a) = 1 ∧
      (∀ U ⊆ S, (∏ a ∈ U, g a) = 1 → U.card ≤ T.card) ∧
      (S \ T).card < D := by
  classical
  let A := S.powerset.filter (fun T => (∏ a ∈ T, g a) = 1)
  have hA : A.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [A]
  obtain ⟨T, hTA, hmax⟩ := Finset.exists_max_image A Finset.card hA
  have hTS : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_filter.mp hTA).1
  have hprod : (∏ a ∈ T, g a) = 1 := (Finset.mem_filter.mp hTA).2
  have hmax' : ∀ U ⊆ S, (∏ a ∈ U, g a) = 1 → U.card ≤ T.card := by
    intro U hUS hUprod
    exact hmax U (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hUS, hUprod⟩)
  refine ⟨T, hTS, hprod, hmax', ?_⟩
  by_contra hlarge
  obtain ⟨U, hUsub, hUne, hUprod⟩ :=
    h (S \ T) (Finset.sdiff_subset.trans hSP) (Nat.le_of_not_gt hlarge)
  have hdisj : Disjoint T U := by
    refine Finset.disjoint_left.mpr ?_
    intro a ha hUa
    exact (Finset.mem_sdiff.mp (hUsub hUa)).2 ha
  have hUS : U ⊆ S := hUsub.trans Finset.sdiff_subset
  have hcard := hmax' (T ∪ U) (Finset.union_subset hTS hUS) (by
    rw [Finset.prod_union hdisj, hprod, hUprod, one_mul])
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hpos : 0 < U.card := Finset.card_pos.mpr hUne
  omega

/-- The maximal-subset theorem without its maximality conclusion. -/
theorem exists_product_one_subset [DecidableEq α] {P S : Finset α} {g : α → G} {D : ℕ}
    (h : DavenportBound P g D) (hSP : S ⊆ P) :
    ∃ T : Finset α, T ⊆ S ∧ (∏ a ∈ T, g a) = 1 ∧ (S \ T).card < D := by
  obtain ⟨T, hTS, hprod, _, hsmall⟩ := exists_maximal_product_one_subset h hSP
  exact ⟨T, hTS, hprod, hsmall⟩

/-- Product-one subsets of the pool with sizes in `[t + 1 - D, t]`.
The lower endpoint uses natural-number subtraction. -/
noncomputable def goodSubsets (P : Finset α) (g : α → G) (D t : ℕ) :
    Finset (Finset α) := by
  classical
  exact P.powerset.filter (fun T =>
    (∏ a ∈ T, g a) = 1 ∧ t + 1 - D ≤ T.card ∧ T.card ≤ t)

@[simp]
theorem mem_goodSubsets {P T : Finset α} {g : α → G} {D t : ℕ} :
    T ∈ goodSubsets P g D t ↔
      T ⊆ P ∧ (∏ a ∈ T, g a) = 1 ∧ t + 1 - D ≤ T.card ∧ T.card ≤ t := by
  classical
  simp [goodSubsets]

/-- All subsets of the pool with cardinality less than `D`. -/
def smallSubsets (P : Finset α) (D : ℕ) : Finset (Finset α) :=
  P.powerset.filter (fun R => R.card < D)

@[simp]
theorem mem_smallSubsets {P R : Finset α} {D : ℕ} :
    R ∈ smallSubsets P D ↔ R ⊆ P ∧ R.card < D := by
  simp [smallSubsets]

/-- Exact count of the possible small remainders. -/
theorem card_smallSubsets (P : Finset α) (D : ℕ) :
    (smallSubsets P D).card = ∑ j ∈ Finset.range D, Nat.choose P.card j := by
  classical
  simpa only [smallSubsets, ← Finset.powersetCard_eq_filter,
    Finset.card_powersetCard, Finset.mem_range] using
    (Finset.sum_card_fiberwise_eq_card_filter P.powerset (Finset.range D)
      (fun R : Finset α => R.card)).symm

/-- Exact finite-counting bound obtained by choosing a large product-one subset
of every `t`-subset and injecting it into the pair of that subset and its remainder.
No numerical restriction on `t` is needed; this includes `D + 1 ≤ t ≤ P.card`. -/
theorem count_bound [DecidableEq α] {P : Finset α} {g : α → G} {D : ℕ}
    (h : DavenportBound P g D) (t : ℕ) :
    Nat.choose P.card t ≤
      (goodSubsets P g D t).card * ∑ j ∈ Finset.range D, Nat.choose P.card j := by
  classical
  have hex : ∀ S : P.powersetCard t,
      ∃ T : Finset α, T ⊆ (S : Finset α) ∧ (∏ a ∈ T, g a) = 1 ∧
        ((S : Finset α) \ T).card < D := by
    intro S
    exact exists_product_one_subset h (Finset.mem_powersetCard.mp S.property).1
  choose T hTS hprod hsmall using hex
  have hmem : ∀ S : P.powersetCard t,
      (T S, (S : Finset α) \ T S) ∈
        (goodSubsets P g D t).product (smallSubsets P D) := by
    intro S
    have hS := Finset.mem_powersetCard.mp S.property
    have hcard := Finset.card_sdiff_add_card_eq_card (hTS S)
    refine Finset.mem_product.mpr ⟨mem_goodSubsets.mpr
      ⟨(hTS S).trans hS.1, hprod S, ?_, ?_⟩,
      mem_smallSubsets.mpr ⟨Finset.sdiff_subset.trans hS.1, hsmall S⟩⟩
    · change t + 1 - D ≤ (T S).card
      have hrem := hsmall S
      omega
    · exact (Finset.card_le_card (hTS S)).trans_eq hS.2
  let f : P.powersetCard t → (goodSubsets P g D t).product (smallSubsets P D) :=
    fun S => ⟨(T S, (S : Finset α) \ T S), hmem S⟩
  have hinj : Function.Injective f := by
    intro S₁ S₂ heq
    apply Subtype.ext
    have hpair : (T S₁, (S₁ : Finset α) \ T S₁) =
        (T S₂, (S₂ : Finset α) \ T S₂) := congrArg Subtype.val heq
    calc
      (S₁ : Finset α) = T S₁ ∪ ((S₁ : Finset α) \ T S₁) :=
        (Finset.union_sdiff_of_subset (hTS S₁)).symm
      _ = T S₂ ∪ ((S₂ : Finset α) \ T S₂) :=
        congrArg (fun p : Finset α × Finset α => p.1 ∪ p.2) hpair
      _ = (S₂ : Finset α) := Finset.union_sdiff_of_subset (hTS S₂)
  simpa only [Finset.card_powersetCard, Finset.product_eq_sprod,
    Finset.card_product, card_smallSubsets] using
    Finset.card_le_card_of_injective hinj

/-- A crude upper bound for the binomial sum, including the empty-pool case. -/
theorem sum_choose_le_pow (r D : ℕ) :
    (∑ j ∈ Finset.range D, Nat.choose r j) ≤ (r + 1) ^ D := by
  by_cases hr : r = 0
  · subst r
    cases D with
    | zero => simp
    | succ D => simp [Finset.sum_range_succ']
  · have hrone : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    induction D with
    | zero => simp
    | succ D ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hpow : r ^ D ≤ (r + 1) ^ D * r :=
        (Nat.pow_le_pow_left (Nat.le_succ r) D).trans
          (by simpa using Nat.mul_le_mul_left ((r + 1) ^ D) hrone)
      calc
        (∑ j ∈ Finset.range D, Nat.choose r j) + Nat.choose r D ≤
            (r + 1) ^ D + r ^ D := Nat.add_le_add ih (Nat.choose_le_pow r D)
        _ ≤ (r + 1) ^ D + (r + 1) ^ D * r := Nat.add_le_add_left hpow _
        _ = (r + 1) ^ D * (r + 1) := by ring

/-- The exact counting bound with the binomial sum replaced by a crude power bound. -/
theorem count_bound_pow [DecidableEq α] {P : Finset α} {g : α → G} {D : ℕ}
    (h : DavenportBound P g D) (t : ℕ) :
    Nat.choose P.card t ≤ (goodSubsets P g D t).card * (P.card + 1) ^ D :=
  (count_bound h t).trans
    (Nat.mul_le_mul_left _ (sum_choose_le_pow P.card D))

end ProductOneCounting
