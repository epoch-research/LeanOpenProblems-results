import Submission.SunflowerFoundation

/-!
# Exact auxiliary reductions for Erdős problem 20

This file imports the independently proved foundation, **not** `Submission.Spec`.
It does not prove the exponential sunflower conjecture. The function in the target
below is `SunflowerFoundation.f`, the foundation's literal copy of the original
infimum definition.

The first reduction is an equivalence with a bound on finite sunflower-free uniform
families. Its reverse direction absorbs the threshold's additive constant by replacing
a base `C` with `C + 2`. All quantifiers in this equivalence range over `Type`, just as
in the original threshold definition.

The second reduction takes an inclusion-maximal core `T` with link cardinality
above `r ^ (n - T.card)`. Its link has positive residual rank `m = n - T.card`,
still has more than `r ^ m` members, and has absolute codegree at most
`r ^ (m - U.card)` for every nonempty finite core `U`. Links preserve
sunflower-freeness because an arbitrary-kernel sunflower in the link lifts to a
sunflower in the original family.

Finally, the original target is shown equivalent to the existence of a constant
base for which every such absolute-profile family contains an arbitrary-kernel
sunflower. That assertion remains unproved. No matching assertion is substituted
for it.
-/

set_option autoImplicit false

namespace SunflowerReduction

open SunflowerFoundation

variable {α : Type*}

/-- The `Finset` and finite ambient `Set` formulations of sunflower existence agree.
In the right-hand side, finiteness of `S` follows from `S ⊆ F`. -/
theorem hasSunflower_iff_exists_set (F : Finset (Set α)) (k : ℕ) :
    HasSunflower F k ↔
      ∃ S ⊆ (F : Set (Set α)), S.ncard = k ∧ IsSunflower S := by
  constructor
  · rintro ⟨S, hSF, hcard, hsun⟩
    exact ⟨(S : Set (Set α)), hSF, by simpa only [Set.ncard_coe_finset] using hcard,
      hsun⟩
  · rintro ⟨S, hSF, hcard, hsun⟩
    have hS : S.Finite := F.finite_toSet.subset hSF
    refine ⟨hS.toFinset, ?_, ?_, ?_⟩
    · intro A hA
      exact hSF (hS.mem_toFinset.mp hA)
    · simpa only [← Set.ncard_eq_toFinset_card S hS] using hcard
    · simpa only [Set.Finite.coe_toFinset] using hsun

/-- An exact successor-threshold reformulation. Positivity of the rank ensures
that members of a set family with positive `ncard` are finite. -/
theorem threshold_succ_iff_card_le (n k b : ℕ) (hn : 0 < n) :
    Threshold n k (b + 1) ↔
      ∀ {α : Type} (F : Finset (Set α)),
        (∀ A ∈ F, A.ncard = n) → (∀ A ∈ F, A.Finite) →
        ¬ HasSunflower F k → F.card ≤ b := by
  constructor
  · intro h α F huniform _hfinite hfree
    by_contra! hlarge
    apply hfree
    apply (hasSunflower_iff_exists_set F k).mpr
    exact h (F : Set (Set α)) ⟨huniform, by
      simpa only [Set.ncard_coe_finset] using (Nat.succ_le_of_lt hlarge)⟩
  · intro h α F hF
    have hfiniteF : F.Finite := Set.finite_of_ncard_pos (by omega)
    have huniform : ∀ A ∈ hfiniteF.toFinset, A.ncard = n :=
      fun A hA => hF.1 A (hfiniteF.mem_toFinset.mp hA)
    have hfinite : ∀ A ∈ hfiniteF.toFinset, A.Finite := by
      intro A hA
      exact Set.finite_of_ncard_pos (by rw [huniform A hA]; exact hn)
    have hsun : HasSunflower hfiniteF.toFinset k := by
      by_contra hfree
      have hbound := h hfiniteF.toFinset huniform hfinite hfree
      rw [← Set.ncard_eq_toFinset_card F hfiniteF] at hbound
      omega
    simpa only [Set.Finite.coe_toFinset] using
      (hasSunflower_iff_exists_set hfiniteF.toFinset k).mp hsun

/-- A pure finite-family exponential cardinality bound, with no threshold or
infimum in its statement. The rank is positive; no restriction on `k` is needed. -/
def UniformFreeBound (k C : ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ {α : Type} (F : Finset (Set α)),
    (∀ A ∈ F, A.ncard = n) → (∀ A ∈ F, A.Finite) →
    ¬ HasSunflower F k → F.card ≤ C ^ n

/-- The exact threshold corresponding to a free-family bound is `C ^ n + 1`. -/
theorem uniformFreeBound_iff_f_le (k C : ℕ) :
    UniformFreeBound k C ↔ ∀ n : ℕ, 0 < n → f n k ≤ C ^ n + 1 := by
  constructor
  · intro h n hn
    apply f_le_of_threshold
    exact (threshold_succ_iff_card_le n k (C ^ n) hn).mpr (h n hn)
  · intro h n hn
    apply (threshold_succ_iff_card_le n k (C ^ n) hn).mp
    exact (threshold_iff_f_le n k (C ^ n + 1) hn).mpr (h n hn)

/-- Increasing a natural-number base by two absorbs an additive one while
retaining a strict inequality, including at rank one and base zero. -/
theorem pow_add_one_lt_add_two_pow (C n : ℕ) (hn : 0 < n) :
    C ^ n + 1 < (C + 2) ^ n := by
  have h₁ : C ^ n < (C + 1) ^ n :=
    Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt hn)
  have h₂ : (C + 1) ^ n < (C + 2) ^ n :=
    Nat.pow_lt_pow_left (by omega) (Nat.ne_of_gt hn)
  exact (Nat.succ_le_of_lt h₁).trans_lt h₂

/-- The reverse reduction with an explicit choice of enlarged base. -/
theorem UniformFreeBound.f_lt {k C : ℕ} (h : UniformFreeBound k C)
    (n : ℕ) (hn : 0 < n) : f n k < (C + 2) ^ n :=
  ((uniformFreeBound_iff_f_le k C).mp h n hn).trans_lt
    (pow_add_one_lt_add_two_pow C n hn)

/-- The original exponential target, using the foundation's literal copy of `f`.
This is a proposition being reduced, **not** an assertion that it holds. -/
def OriginalTarget : Prop :=
  ∃ c : ℕ → ℕ, ∀ n k : ℕ, 0 < n → f n k < (c k) ^ n

/-- **Exact equivalence, not a proof of either side.** In the forward direction
one may keep the same base; in the reverse direction choose `c k = C k + 2`. -/
theorem originalTarget_iff_uniformFreeBound :
    OriginalTarget ↔ ∀ k : ℕ, ∃ C : ℕ, UniformFreeBound k C := by
  constructor
  · rintro ⟨c, hc⟩ k
    refine ⟨c k, (uniformFreeBound_iff_f_le k (c k)).mpr ?_⟩
    intro n hn
    exact (hc n k hn).le.trans (Nat.le_succ _)
  · intro h
    choose C hC using h
    exact ⟨fun k => C k + 2, fun n k hn => (hC k).f_lt n hn⟩

/- ## Links and sunflower lifting -/

/-- The subfamily of members which contain the finite core `T`. -/
noncomputable def containing (F : Finset (Set α)) (T : Finset α) : Finset (Set α) := by
  classical
  exact F.filter (fun A => (T : Set α) ⊆ A)

/-- The absolute codegree of a finite core: the number of members containing it. -/
noncomputable def codegree (F : Finset (Set α)) (T : Finset α) : ℕ :=
  (containing F T).card

/-- The link at `T`, with `T` deleted from all members containing it. -/
noncomputable def link (F : Finset (Set α)) (T : Finset α) : Finset (Set α) := by
  classical
  exact (containing F T).image (fun A => A \ (T : Set α))

@[simp] theorem mem_containing {F : Finset (Set α)} {T : Finset α} {A : Set α} :
    A ∈ containing F T ↔ A ∈ F ∧ (T : Set α) ⊆ A := by
  classical
  simp [containing]

@[simp] theorem mem_link {F : Finset (Set α)} {T : Finset α} {A : Set α} :
    A ∈ link F T ↔ ∃ B ∈ F, (T : Set α) ⊆ B ∧ B \ (T : Set α) = A := by
  classical
  simp [link, containing, and_assoc]

@[simp] theorem link_empty (F : Finset (Set α)) : link F ∅ = F := by
  classical
  simp [link, containing]

@[simp] theorem codegree_empty (F : Finset (Set α)) : codegree F ∅ = F.card := by
  classical
  simp [codegree, containing]

/-- Removing a common core is injective on a family containing it. -/
theorem diff_injOn_of_subset {F : Finset (Set α)} {T : Set α}
    (hT : ∀ A ∈ F, T ⊆ A) :
    Set.InjOn (fun A : Set α => A \ T) (F : Set (Set α)) := by
  intro A hA B hB hAB
  calc
    A = T ∪ (A \ T) := (Set.union_diff_cancel (hT A hA)).symm
    _ = T ∪ (B \ T) := congrArg (fun C : Set α => T ∪ C) hAB
    _ = B := Set.union_diff_cancel (hT B hB)

/-- Linking does not lose multiplicities: the original family has no repetitions,
and deletion of the common core is injective. -/
@[simp] theorem card_link (F : Finset (Set α)) (T : Finset α) :
    (link F T).card = codegree F T := by
  classical
  unfold link codegree
  exact Finset.card_image_of_injOn
    (diff_injOn_of_subset (fun A hA => (mem_containing.mp hA).2))

/-- Adjoining a fixed set to every petal sends a sunflower with kernel `K` to
one with kernel `T ∪ K`. In particular the kernel need not be empty. -/
theorem isSunflower_image_union {S : Set (Set α)} (hS : IsSunflower S) (T : Set α) :
    IsSunflower ((fun A : Set α => T ∪ A) '' S) := by
  obtain ⟨K, hK⟩ := hS
  refine ⟨T ∪ K, ?_⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
  have hne : A ≠ B := fun h => hAB (congrArg (fun C : Set α => T ∪ C) h)
  calc
    (T ∪ A) ∩ (T ∪ B) = T ∪ (A ∩ B) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union]
      tauto
    _ = T ∪ K := congrArg (fun C : Set α => T ∪ C) (hK hA hB hne)

/-- Any sunflower in a link lifts to the original family, preserving the number
of petals and adjoining the core to the sunflower kernel. -/
theorem hasSunflower_of_link {F : Finset (Set α)} {T : Finset α} {k : ℕ}
    (h : HasSunflower (link F T) k) : HasSunflower F k := by
  classical
  obtain ⟨S, hSF, hcard, hsun⟩ := h
  have hremove : ∀ A ∈ S, ((T : Set α) ∪ A) \ (T : Set α) = A := by
    intro A hA
    obtain ⟨B, _, _, rfl⟩ := mem_link.mp (hSF hA)
    ext x
    simp only [Set.mem_diff, Set.mem_union]
    tauto
  refine ⟨S.image (fun A => (T : Set α) ∪ A), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨C, hC, hTC, rfl⟩ := mem_link.mp (hSF hB)
    simpa only [Set.union_diff_cancel hTC] using hC
  · rw [Finset.card_image_of_injOn, hcard]
    intro A hA B hB hAB
    have heq := congrArg (fun C : Set α => C \ (T : Set α)) hAB
    simpa only [hremove A hA, hremove B hB] using heq
  · rw [Finset.coe_image]
    exact isSunflower_image_union hsun (T : Set α)

/-- Sunflower-freeness is hereditary under taking any link. -/
theorem not_hasSunflower_link {F : Finset (Set α)} {k : ℕ}
    (hfree : ¬ HasSunflower F k) (T : Finset α) : ¬ HasSunflower (link F T) k :=
  fun h => hfree (hasSunflower_of_link h)

/-- Members of a link of a finite-set family are finite. -/
theorem link_finite (F : Finset (Set α)) (T : Finset α)
    (hfinite : ∀ A ∈ F, A.Finite) : ∀ A ∈ link F T, A.Finite := by
  intro A hA
  obtain ⟨B, hB, _, rfl⟩ := mem_link.mp hA
  exact (hfinite B hB).diff

/-- Linking an `n`-uniform family at `T` leaves rank `n - T.card`. -/
theorem link_uniform (F : Finset (Set α)) (T : Finset α) (n : ℕ)
    (huniform : ∀ A ∈ F, A.ncard = n) :
    ∀ A ∈ link F T, A.ncard = n - T.card := by
  intro A hA
  obtain ⟨B, hB, hTB, rfl⟩ := mem_link.mp hA
  rw [Set.ncard_diff hTB T.finite_toSet, huniform B hB, Set.ncard_coe_finset]

/-- Every member of a link is disjoint from its deleted core. -/
theorem disjoint_of_mem_link {F : Finset (Set α)} {T : Finset α} {A : Set α}
    (hA : A ∈ link F T) : Disjoint (T : Set α) A := by
  obtain ⟨B, _, _, rfl⟩ := mem_link.mp hA
  exact Set.disjoint_sdiff_right

/-- A positive codegree is witnessed by an actual member containing the core. -/
theorem codegree_pos {F : Finset (Set α)} {T : Finset α} :
    0 < codegree F T ↔ ∃ A ∈ F, (T : Set α) ⊆ A := by
  classical
  simp [codegree, Finset.card_pos, Finset.Nonempty]

/-- A core with positive codegree in a link is disjoint from the deleted core. -/
theorem disjoint_of_codegree_link_pos {F : Finset (Set α)} {T U : Finset α}
    (hpos : 0 < codegree (link F T) U) : Disjoint T U := by
  obtain ⟨A, hA, hUA⟩ := codegree_pos.mp hpos
  exact Finset.disjoint_coe.mp ((disjoint_of_mem_link hA).mono_right hUA)

/-- The codegree identity for disjoint cores. The disjointness hypothesis is
essential: a residual member cannot contain any deleted point. -/
theorem codegree_link_of_disjoint [DecidableEq α] (F : Finset (Set α))
    {T U : Finset α} (hTU : Disjoint T U) :
    codegree (link F T) U = codegree F (T ∪ U) := by
  classical
  have hsets : containing (link F T) U =
      (containing F (T ∪ U)).image (fun A => A \ (T : Set α)) := by
    ext A
    constructor
    · intro hA
      obtain ⟨hAlink, hUA⟩ := mem_containing.mp hA
      obtain ⟨B, hB, hTB, rfl⟩ := mem_link.mp hAlink
      refine Finset.mem_image.mpr ⟨B, mem_containing.mpr ⟨hB, ?_⟩, rfl⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hxT | hxU
      · exact hTB hxT
      · exact (hUA hxU).1
    · intro hA
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hBF, hTUB⟩ := mem_containing.mp hB
      refine mem_containing.mpr ⟨mem_link.mpr ⟨B, hBF, ?_, rfl⟩, ?_⟩
      · intro x hx
        exact hTUB (Finset.mem_union_left U hx)
      · intro x hxU
        exact ⟨hTUB (Finset.mem_union_right T hxU),
          fun hxT => Finset.disjoint_left.mp hTU hxT hxU⟩
  unfold codegree
  rw [hsets]
  apply Finset.card_image_of_injOn
  apply diff_injOn_of_subset
  intro A hA x hx
  exact (mem_containing.mp hA).2 (Finset.mem_union_left U hx)

/- ## Inclusion-maximal large links and the absolute codegree profile -/

/-- The absolute profile left by a maximal large link. The upper bounds are
required only for nonempty cores: the empty core has codegree `F.card > r ^ m`.
Natural subtraction is intentional; cores larger than the rank cannot occur in
a finite `m`-uniform family. -/
def AbsoluteProfile (F : Finset (Set α)) (m r : ℕ) : Prop :=
  r ^ m < F.card ∧
    ∀ U : Finset α, U.Nonempty → codegree F U ≤ r ^ (m - U.card)

/-- Among all finite cores with link cardinality greater than `r ^ (n - |T|)`,
there is an inclusion-maximal one. Every qualifying core is contained in the
finite support of `F`, so maximizing over that support loses no candidates.
No uniformity hypothesis is needed for this selection step. -/
theorem exists_maximal_large_link (F : Finset (Set α)) (n r : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (hlarge : r ^ n < F.card) :
    ∃ T : Finset α,
      Maximal (fun T : Finset α => r ^ (n - T.card) < (link F T).card) T := by
  classical
  let V : Set α := ⋃ A ∈ (F : Set (Set α)), A
  have hV : V.Finite := F.finite_toSet.biUnion (fun A hA => hfinite A hA)
  have hsupport (T : Finset α) (hT : r ^ (n - T.card) < (link F T).card) :
      T ⊆ hV.toFinset := by
    have hpos : 0 < codegree F T := by
      rw [← card_link]
      exact (Nat.zero_le _).trans_lt hT
    obtain ⟨A, hA, hTA⟩ := codegree_pos.mp hpos
    intro x hx
    exact hV.mem_toFinset.mpr (Set.mem_iUnion_of_mem A
      (Set.mem_iUnion_of_mem hA (hTA hx)))
  let C : Finset (Finset α) := hV.toFinset.powerset.filter
    (fun T => r ^ (n - T.card) < (link F T).card)
  obtain ⟨T, hT⟩ := C.exists_maximal (by
    refine ⟨∅, ?_⟩
    simpa [C] using hlarge)
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hT
  refine ⟨T, hT.1.2, ?_⟩
  intro U hU hTU
  exact hT.2 ⟨hsupport U hU, hU⟩ hTU

/-- Inclusion maximality gives the *absolute* upper profile, not merely a bound
relative to `F.card`. Overlapping cores have zero codegree; for disjoint cores,
a violation would make `T ∪ U` a strictly larger qualifying core. -/
theorem absoluteProfile_of_maximal_large_link (F : Finset (Set α)) (n r : ℕ)
    {T : Finset α}
    (hT : Maximal (fun T : Finset α => r ^ (n - T.card) < (link F T).card) T) :
    AbsoluteProfile (link F T) (n - T.card) r := by
  classical
  refine ⟨hT.1, ?_⟩
  intro U hU
  by_contra! hbad
  have hTU : Disjoint T U :=
    disjoint_of_codegree_link_pos ((Nat.zero_le _).trans_lt hbad)
  have hexp : n - (T ∪ U).card = (n - T.card) - U.card := by
    rw [Finset.card_union_of_disjoint hTU]
    omega
  have hlarge : r ^ (n - (T ∪ U).card) < (link F (T ∪ U)).card := by
    rw [hexp, card_link, ← codegree_link_of_disjoint F hTU]
    exact hbad
  have hsub : T ∪ U ⊆ T := hT.2 hlarge Finset.subset_union_left
  obtain ⟨x, hx⟩ := hU
  exact Finset.disjoint_left.mp hTU (hsub (Finset.mem_union_right T hx)) hx

/-- A finite uniform family above `r ^ n` cannot have rank zero, since the only
finite set of cardinality zero is the empty set. This also covers `r = 0`. -/
theorem rank_pos_of_card_gt_pow (F : Finset (Set α)) (n r : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (huniform : ∀ A ∈ F, A.ncard = n)
    (hlarge : r ^ n < F.card) : 0 < n := by
  classical
  by_contra! hn
  have hn0 : n = 0 := by omega
  have hF : F ⊆ {∅} := by
    intro A hA
    apply Finset.mem_singleton.mpr
    apply (Set.ncard_eq_zero (hfinite A hA)).mp
    rw [huniform A hA, hn0]
  have hcard : F.card ≤ 1 := by simpa using Finset.card_le_card hF
  simp only [hn0, pow_zero] at hlarge
  omega

/-- **Absolute maximal-link reduction.** From `|F| > r ^ n` obtain a core of size
strictly less than `n` whose link has the absolute profile. The residual rank is
therefore positive. This theorem is valid for every natural `r`, including zero. -/
theorem exists_absolute_profile_link (F : Finset (Set α)) (n r : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (huniform : ∀ A ∈ F, A.ncard = n)
    (hlarge : r ^ n < F.card) :
    ∃ T : Finset α, T.card < n ∧ AbsoluteProfile (link F T) (n - T.card) r := by
  obtain ⟨T, hT⟩ := exists_maximal_large_link F n r hfinite hlarge
  have hpos := rank_pos_of_card_gt_pow (link F T) (n - T.card) r
    (link_finite F T hfinite) (link_uniform F T n huniform) hT.1
  exact ⟨T, by omega, absoluteProfile_of_maximal_large_link F n r hT⟩

/-- The full sunflower-free output of the maximal-link reduction, retaining the
core and recording finiteness, residual uniformity, and hereditary freeness. -/
theorem exists_free_absolute_profile_link (F : Finset (Set α)) (n k r : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (huniform : ∀ A ∈ F, A.ncard = n)
    (hfree : ¬ HasSunflower F k) (hlarge : r ^ n < F.card) :
    ∃ T : Finset α, T.card < n ∧
      (∀ A ∈ link F T, A.Finite) ∧
      (∀ A ∈ link F T, A.ncard = n - T.card) ∧
      ¬ HasSunflower (link F T) k ∧ AbsoluteProfile (link F T) (n - T.card) r := by
  obtain ⟨T, hT, hprofile⟩ := exists_absolute_profile_link F n r hfinite huniform hlarge
  exact ⟨T, hT, link_finite F T hfinite, link_uniform F T n huniform,
    not_hasSunflower_link hfree T, hprofile⟩

/-- The remaining sunflower assertion restricted to absolute-profile families.
It asks for a sunflower with an **arbitrary kernel**, not a disjoint matching.
This definition makes no claim that a rank-independent `r` exists. -/
def AbsoluteProfileSunflower (k r : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ {α : Type} (F : Finset (Set α)),
    (∀ A ∈ F, A.ncard = m) → (∀ A ∈ F, A.Finite) →
    AbsoluteProfile F m r → HasSunflower F k

/-- At each fixed base, proving the sunflower assertion just for absolute-profile
families is exactly equivalent to bounding all sunflower-free uniform families.
The nontrivial direction extracts a link and then lifts its sunflower. -/
theorem uniformFreeBound_iff_absoluteProfileSunflower (k r : ℕ) :
    UniformFreeBound k r ↔ AbsoluteProfileSunflower k r := by
  constructor
  · intro h m hm α F huniform hfinite hprofile
    by_contra hfree
    exact (not_le_of_gt hprofile.1) (h m hm F huniform hfinite hfree)
  · intro h n _hn α F huniform hfinite hfree
    by_contra! hlarge
    obtain ⟨T, hT, hprofile⟩ := exists_absolute_profile_link F n r hfinite huniform hlarge
    have hsun := h (n - T.card) (by omega) (link F T)
      (link_uniform F T n huniform) (link_finite F T hfinite) hprofile
    exact hfree (hasSunflower_of_link hsun)

/-- **Exact remaining mathematics.** The target is equivalent to finding, for
each petal count, a constant base such that every positive-rank absolute-profile
family contains an arbitrary-kernel sunflower. Neither side is proved here. -/
theorem originalTarget_iff_absoluteProfileSunflower :
    OriginalTarget ↔ ∀ k : ℕ, ∃ r : ℕ, AbsoluteProfileSunflower k r := by
  rw [originalTarget_iff_uniformFreeBound]
  constructor
  · intro h k
    obtain ⟨r, hr⟩ := h k
    exact ⟨r, (uniformFreeBound_iff_absoluteProfileSunflower k r).mp hr⟩
  · intro h k
    obtain ⟨r, hr⟩ := h k
    exact ⟨r, (uniformFreeBound_iff_absoluteProfileSunflower k r).mpr hr⟩

end SunflowerReduction
