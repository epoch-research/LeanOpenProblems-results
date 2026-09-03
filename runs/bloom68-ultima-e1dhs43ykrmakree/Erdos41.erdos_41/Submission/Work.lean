import FormalConjecturesUtil

/-!
# Auxiliary lemmas for distinct finite-subset sums

This file is independent of `Submission.Spec`.  `Work.NtupleCondition` duplicates
its finite-subset-sum condition, and the results below are only auxiliary lemmas.
They make no assertion about the asymptotic conjecture.
-/

open scoped BigOperators

namespace Work

variable {α : Type*} [AddCommMonoid α]

/-- Distinct `n`-element subsets of `A` have distinct sums. -/
def NtupleCondition (A : Set α) (n : ℕ) : Prop := ∀ (I : Finset α) (J : Finset α),
  ↑I ⊆ A ∧ ↑J ⊆ A ∧ I.card = n ∧ J.card = n ∧
  (∑ i ∈ I, i = ∑ j ∈ J, j) → I = J

/-- The distinct-sum condition is preserved when the underlying set is restricted. -/
theorem NtupleCondition.mono {A B : Set α} {n : ℕ}
    (hA : NtupleCondition A n) (hBA : B ⊆ A) : NtupleCondition B n := by
  intro I J h
  rcases h with ⟨hIB, hJB, hIcard, hJcard, hsum⟩
  exact hA I J ⟨hIB.trans hBA, hJB.trans hBA, hIcard, hJcard, hsum⟩

/-- On an infinite set, padding both subsets with one common fresh element
reduces the distinct-sum condition from `n + 1` elements to `n` elements. -/
theorem NtupleCondition.of_succ {A : Set α} {n : ℕ}
    (hA : NtupleCondition A (n + 1)) (hInfinite : A.Infinite) :
    NtupleCondition A n := by
  classical
  intro I J h
  rcases h with ⟨hIA, hJA, hIcard, hJcard, hsum⟩
  obtain ⟨a, haA, ha⟩ := hInfinite.exists_notMem_finset (I ∪ J)
  have haI : a ∉ I := fun h => ha (Finset.mem_union.mpr (Or.inl h))
  have haJ : a ∉ J := fun h => ha (Finset.mem_union.mpr (Or.inr h))
  have hinsert : insert a I = insert a J := by
    apply hA (insert a I) (insert a J)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haA
      · exact hIA hx
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haA
      · exact hJA hx
    · simp only [Finset.card_insert_of_notMem haI, hIcard]
    · simp only [Finset.card_insert_of_notMem haJ, hJcard]
    · rw [Finset.sum_insert haI, Finset.sum_insert haJ, hsum]
  have herase := congrArg (fun K : Finset α => K.erase a) hinsert
  simpa only [Finset.erase_insert haI, Finset.erase_insert haJ] using herase

/-- In particular, an infinite set of naturals with distinct triple-subset sums
has distinct pair-subset sums. -/
theorem NtupleCondition.two_of_three {A : Set ℕ}
    (hTriple : NtupleCondition A 3) (hInfinite : A.Infinite) :
    NtupleCondition A 2 :=
  NtupleCondition.of_succ (n := 2) hTriple hInfinite

/-- The sum map is injective on the `n`-element subsets of a finite subset of `A`. -/
theorem NtupleCondition.sum_injOn_powersetCard {A : Set α} {n : ℕ}
    (hA : NtupleCondition A n) {S : Finset α} (hS : (↑S : Set α) ⊆ A) :
    Set.InjOn (fun I : Finset α => ∑ i ∈ I, i)
      (↑(S.powersetCard n) : Set (Finset α)) := by
  intro I hI J hJ hsum
  rcases Finset.mem_powersetCard.mp hI with ⟨hIS, hIcard⟩
  rcases Finset.mem_powersetCard.mp hJ with ⟨hJS, hJcard⟩
  exact hA I J ⟨fun _ hi => hS (hIS hi), fun _ hj => hS (hJS hj),
    hIcard, hJcard, hsum⟩

/-- If the triple-subset sum map is injective and every element of `S` lies in
`[1, N]`, then the number of three-element subsets is at most `3 * N`. -/
theorem choose_card_three_le_of_injOn {S : Finset ℕ} {N : ℕ}
    (hS : (↑S : Set ℕ) ⊆ Set.Icc 1 N)
    (hInj : Set.InjOn (fun I : Finset ℕ => ∑ i ∈ I, i)
      (↑(S.powersetCard 3) : Set (Finset ℕ))) :
    Nat.choose S.card 3 ≤ 3 * N := by
  have hImage : (S.powersetCard 3).image (fun I : Finset ℕ => ∑ i ∈ I, i) ⊆
      Finset.Icc 1 (3 * N) := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨I, hI, rfl⟩
    rcases Finset.mem_powersetCard.mp hI with ⟨hIS, hIcard⟩
    apply Finset.mem_Icc.mpr
    constructor
    · have hLower : (∑ _i ∈ I, (1 : ℕ)) ≤ ∑ i ∈ I, i :=
        Finset.sum_le_sum (fun i hi => (hS (hIS hi)).1)
      have hThree : 3 ≤ ∑ i ∈ I, i := by
        simpa [hIcard] using hLower
      exact (by decide : 1 ≤ 3).trans hThree
    · calc
        (∑ i ∈ I, i) ≤ ∑ _i ∈ I, N :=
          Finset.sum_le_sum (fun i hi => (hS (hIS hi)).2)
        _ = 3 * N := by simp [hIcard]
  calc
    Nat.choose S.card 3 = (S.powersetCard 3).card :=
      (Finset.card_powersetCard 3 S).symm
    _ = ((S.powersetCard 3).image (fun I : Finset ℕ => ∑ i ∈ I, i)).card :=
      (Finset.card_image_of_injOn hInj).symm
    _ ≤ (Finset.Icc 1 (3 * N)).card := Finset.card_le_card hImage
    _ = 3 * N := by simp [Nat.card_Icc]

/-- The triple distinct-sum condition gives the finite counting bound for every
finite subset of `A ∩ [1, N]`; no infinitude assumption is needed here. -/
theorem NtupleCondition.choose_card_three_le {A : Set ℕ}
    (hTriple : NtupleCondition A 3) {S : Finset ℕ} {N : ℕ}
    (hS : (↑S : Set ℕ) ⊆ A ∩ Set.Icc 1 N) :
    Nat.choose S.card 3 ≤ 3 * N := by
  apply choose_card_three_le_of_injOn (fun x hx => (hS hx).2)
  exact hTriple.sum_injOn_powersetCard (fun x hx => (hS hx).1)

/-- Apply the finite counting bound to the whole finite intersection, using
`Set.Finite.toFinset`.  This also covers `N = 0`. -/
theorem NtupleCondition.choose_ncard_three_le {A : Set ℕ}
    (hTriple : NtupleCondition A 3) (N : ℕ) :
    Nat.choose (A ∩ Set.Icc 1 N).ncard 3 ≤ 3 * N := by
  classical
  let hFinite : (A ∩ Set.Icc 1 N).Finite :=
    (Set.finite_Icc 1 N).inter_of_right A
  rw [Set.ncard_eq_toFinset_card _ hFinite]
  apply hTriple.choose_card_three_le
  intro x hx
  exact hFinite.mem_toFinset.mp hx

/-- A deliberately loose cubic consequence of the binomial counting bound.
For `m ≥ 4`, use `m ≤ 2 * (m - 2)` and the descending-factorial bound. -/
theorem cube_le_of_choose_three_le {m N : ℕ}
    (hChoose : Nat.choose m 3 ≤ 3 * N) (hN : 1 ≤ N) :
    m ^ 3 ≤ 144 * N := by
  by_cases hm : 4 ≤ m
  · have hHalf : m ≤ 2 * (m + 1 - 3) := by omega
    calc
      m ^ 3 ≤ (2 * (m + 1 - 3)) ^ 3 := Nat.pow_le_pow_left hHalf 3
      _ = 8 * (m + 1 - 3) ^ 3 := by ring
      _ ≤ 8 * m.descFactorial 3 :=
        Nat.mul_le_mul_left 8 (Nat.pow_sub_le_descFactorial m 3)
      _ = 48 * Nat.choose m 3 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        norm_num [Nat.factorial, ← mul_assoc]
      _ ≤ 144 * N := by omega
  · have hm' : m ≤ 3 := by omega
    calc
      m ^ 3 ≤ 3 ^ 3 := Nat.pow_le_pow_left hm' 3
      _ ≤ 144 * N := by omega

/-- The original normalized counting function is nonnegative, including at zero. -/
theorem ratio_nonneg (A : Set ℕ) (N : ℕ) :
    0 ≤ (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- A uniform bound for the original ratio.  The constant is intentionally loose;
no infinitude assumption is required. -/
theorem NtupleCondition.ratio_le_eight {A : Set ℕ}
    (hTriple : NtupleCondition A 3) {N : ℕ} (hN : 1 ≤ N) :
    (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ) ≤ 8 := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hRootPos : 0 < (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hNpos _
  have hRootCube : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (N : ℝ) := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (3 : ℕ) ≠ 0))
  have hCube : ((A ∩ Set.Icc 1 N).ncard : ℝ) ^ (3 : ℕ) ≤ 144 * (N : ℝ) := by
    exact_mod_cast cube_le_of_choose_three_le (hTriple.choose_ncard_three_le N) hN
  apply (div_le_iff₀ hRootPos).2
  apply le_of_pow_le_pow_left₀ (n := 3) (by decide) (by positivity)
  calc
    ((A ∩ Set.Icc 1 N).ncard : ℝ) ^ (3 : ℕ) ≤ 144 * (N : ℝ) := hCube
    _ ≤ 512 * (N : ℝ) := by linarith
    _ = (8 * (N : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
      rw [mul_pow, hRootCube]
      norm_num

/-- At `N = 0` the original ratio is zero, so the same bound holds for every `N`. -/
theorem NtupleCondition.ratio_le_eight_all {A : Set ℕ}
    (hTriple : NtupleCondition A 3) (N : ℕ) :
    (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ) ≤ 8 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · norm_num
  · exact hTriple.ratio_le_eight hN

/-- Nonnegativity supplies the lower boundedness needed by the real liminf API. -/
theorem ratio_isBoundedUnder_ge (A : Set ℕ) :
    Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun N : ℕ => (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) :=
  Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall (ratio_nonneg A))

/-- The original ratio is eventually bounded above (in fact, bounded everywhere). -/
theorem NtupleCondition.ratio_isBoundedUnder_le {A : Set ℕ}
    (hTriple : NtupleCondition A 3) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun N : ℕ => (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) :=
  Filter.isBoundedUnder_of_eventually_le
    (Filter.Eventually.of_forall hTriple.ratio_le_eight_all)

/-- The range of the original normalized counting function is bounded above. -/
theorem NtupleCondition.ratio_bddAbove {A : Set ℕ}
    (hTriple : NtupleCondition A 3) :
    BddAbove (Set.range
      (fun N : ℕ => (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ))) := by
  refine ⟨8, ?_⟩
  rintro x ⟨N, rfl⟩
  exact hTriple.ratio_le_eight_all N

/-- The real liminf of the original ratio is nonnegative.  The uniform upper bound
provides the coboundedness hypothesis of `Filter.le_liminf_of_le`. -/
theorem NtupleCondition.liminf_ratio_nonneg {A : Set ℕ}
    (hTriple : NtupleCondition A 3) :
    0 ≤ Filter.atTop.liminf
      (fun N : ℕ => (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) :=
  Filter.le_liminf_of_le hTriple.ratio_isBoundedUnder_le.isCoboundedUnder_ge
    (Filter.Eventually.of_forall (ratio_nonneg A))

/-- The same uniform constant bounds the real liminf above. -/
theorem NtupleCondition.liminf_ratio_le_eight {A : Set ℕ}
    (hTriple : NtupleCondition A 3) :
    Filter.atTop.liminf
      (fun N : ℕ => (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≤ 8 :=
  Filter.liminf_le_of_frequently_le
    (Filter.Eventually.of_forall hTriple.ratio_le_eight_all).frequently
    (ratio_isBoundedUnder_ge A)

/-- Exact filter reduction for the original ratio: a nonzero liminf is equivalent
to a positive constant lower bound on a tail.  This does not assert that either
side holds, and does not settle whether the liminf is zero. -/
theorem NtupleCondition.liminf_ratio_ne_zero_iff {A : Set ℕ}
    (hTriple : NtupleCondition A 3) :
    (Filter.atTop.liminf
      (fun N : ℕ => (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ)) ≠ 0) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
        c ≤ (A ∩ Set.Icc 1 N).ncard / (N : ℝ) ^ (1 / 3 : ℝ) := by
  constructor
  · intro hne
    have hpos := lt_of_le_of_ne hTriple.liminf_ratio_nonneg hne.symm
    obtain ⟨c, hc, hcL⟩ := exists_between hpos
    refine ⟨c, hc, ?_⟩
    exact (Filter.eventually_lt_of_lt_liminf hcL (ratio_isBoundedUnder_ge A)).mono
      (fun _ h => h.le)
  · rintro ⟨c, hc, hEventually⟩
    exact ne_of_gt (hc.trans_le
      (Filter.le_liminf_of_le hTriple.ratio_isBoundedUnder_le.isCoboundedUnder_ge hEventually))

end Work

#print axioms Work.NtupleCondition
#print axioms Work.NtupleCondition.mono
#print axioms Work.NtupleCondition.of_succ
#print axioms Work.NtupleCondition.two_of_three
#print axioms Work.NtupleCondition.sum_injOn_powersetCard
#print axioms Work.choose_card_three_le_of_injOn
#print axioms Work.NtupleCondition.choose_card_three_le
#print axioms Work.NtupleCondition.choose_ncard_three_le
#print axioms Work.cube_le_of_choose_three_le
#print axioms Work.ratio_nonneg
#print axioms Work.NtupleCondition.ratio_le_eight
#print axioms Work.NtupleCondition.ratio_le_eight_all
#print axioms Work.ratio_isBoundedUnder_ge
#print axioms Work.NtupleCondition.ratio_isBoundedUnder_le
#print axioms Work.NtupleCondition.ratio_bddAbove
#print axioms Work.NtupleCondition.liminf_ratio_nonneg
#print axioms Work.NtupleCondition.liminf_ratio_le_eight
#print axioms Work.NtupleCondition.liminf_ratio_ne_zero_iff
