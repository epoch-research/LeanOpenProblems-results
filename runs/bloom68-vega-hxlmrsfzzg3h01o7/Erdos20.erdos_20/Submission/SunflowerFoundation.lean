import FormalConjecturesUtil

/-!
# Classical finite sunflower foundation

This auxiliary file proves the classical factorial bound for finite uniform set families,
and its consequence that the threshold set in the definition of Erdős problem 20 is
nonempty when the uniformity is positive. It does not import `Submission.Spec`, and it
does not prove the exponential sunflower conjecture.

The proof selects a maximal pairwise-disjoint subfamily. Unless it already contains
`k` petals, its union is a hitting set of size at most `n * (k - 1)`. Erasing a point
from each fiber reduces the uniformity, and summing the inductive fiber bounds gives
`n.factorial * (k - 1) ^ n` as a bound for sunflower-free families.
-/

set_option autoImplicit false

namespace SunflowerFoundation

open scoped BigOperators

variable {α : Type*}

/-- A `k`-petal sunflower inside a family represented by a `Finset`. The petals
and the kernel are still sets, using the problem's original `IsSunflower`. -/
def HasSunflower (F : Finset (Set α)) (k : ℕ) : Prop :=
  ∃ S : Finset (Set α), S ⊆ F ∧ S.card = k ∧ IsSunflower (S : Set (Set α))

/-- Passing to a larger ambient family preserves the existence of a sunflower. -/
theorem HasSunflower.mono {F G : Finset (Set α)} {k : ℕ}
    (h : HasSunflower F k) (hFG : F ⊆ G) : HasSunflower G k := by
  obtain ⟨S, hSF, hcard, hsun⟩ := h
  exact ⟨S, hSF.trans hFG, hcard, hsun⟩

/-- Inserting the same point into every petal preserves the sunflower property. -/
theorem isSunflower_image_insert {S : Set (Set α)} (hS : IsSunflower S) (x : α) :
    IsSunflower ((fun A : Set α => insert x A) '' S) := by
  obtain ⟨K, hK⟩ := hS
  refine ⟨insert x K, ?_⟩
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
  have hne : A ≠ B := fun h => hAB (congrArg (fun C : Set α => insert x C) h)
  have hinter := hK hA hB hne
  calc
    insert x A ∩ insert x B = insert x (A ∩ B) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      tauto
    _ = insert x K := congrArg (fun C : Set α => insert x C) hinter

/-- On sets which contain a fixed point, deleting that point is injective. -/
theorem diff_singleton_injOn {F : Finset (Set α)} {x : α}
    (hx : ∀ A ∈ F, x ∈ A) :
    Set.InjOn (fun A : Set α => A \ {x}) (F : Set (Set α)) := by
  intro A hA B hB hAB
  calc
    A = insert x (A \ {x}) := by
      rw [Set.insert_diff_singleton, Set.insert_eq_of_mem (hx A hA)]
    _ = insert x (B \ {x}) := congrArg (fun C : Set α => insert x C) hAB
    _ = B := by
      rw [Set.insert_diff_singleton, Set.insert_eq_of_mem (hx B hB)]

/-- A sunflower in a deleted-point fiber lifts to one in the original fiber,
without changing the number of petals. -/
theorem hasSunflower_of_erase [DecidableEq (Set α)] {F : Finset (Set α)} {k : ℕ} {x : α}
    (hx : ∀ A ∈ F, x ∈ A)
    (h : HasSunflower (F.image (fun A => A \ {x})) k) : HasSunflower F k := by
  classical
  obtain ⟨S, hSF, hcard, hsun⟩ := h
  have hremove : ∀ A ∈ S, (insert x A : Set α) \ {x} = A := by
    intro A hA
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp (hSF hA)
    ext y
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  refine ⟨S.image (fun A => insert x A), ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (hSF hB)
    simpa only [Set.insert_diff_singleton, Set.insert_eq_of_mem (hx C hC)] using hC
  · rw [Finset.card_image_of_injOn, hcard]
    intro A hA B hB hAB
    have heq := congrArg (fun C : Set α => C \ {x}) hAB
    simpa only [hremove A hA, hremove B hB] using heq
  · rw [Finset.coe_image]
    exact isSunflower_image_insert hsun x

/-- A sufficiently large pairwise-disjoint subfamily is a sunflower with empty kernel. -/
theorem hasSunflower_of_disjoint {F D : Finset (Set α)} {k : ℕ}
    (hDF : D ⊆ F) (hD : (D : Set (Set α)).PairwiseDisjoint id)
    (hcard : k ≤ D.card) : HasSunflower F k := by
  obtain ⟨S, hSD, hS⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨S, hSD.trans hDF, hS, ∅, ?_⟩
  intro A hA B hB hAB
  exact Set.disjoint_iff_inter_eq_empty.mp (hD (hSD hA) (hSD hB) hAB)

/-- A sunflower-free positive-uniformity family has a small finite hitting set. -/
theorem exists_small_hitting_finset (F : Finset (Set α)) (n k : ℕ)
    (hn : 0 < n) (hfinite : ∀ A ∈ F, A.Finite)
    (huniform : ∀ A ∈ F, A.ncard = n) (hfree : ¬ HasSunflower F k) :
    ∃ U : Finset α, U.card ≤ n * (k - 1) ∧ ∀ A ∈ F, ∃ x ∈ U, x ∈ A := by
  classical
  let C : Finset (Finset (Set α)) :=
    F.powerset.filter (fun D : Finset (Set α) => (D : Set (Set α)).PairwiseDisjoint id)
  obtain ⟨D, hDmax⟩ := C.exists_maximal (by
    refine ⟨∅, ?_⟩
    simp [C])
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hDmax
  obtain ⟨hDF, hDdisj⟩ := hDmax.1
  have hDcard : D.card ≤ k - 1 := by
    apply Nat.le_sub_one_of_lt
    by_contra! h
    exact hfree (hasSunflower_of_disjoint hDF hDdisj h)
  let V : Set α := ⋃ A ∈ (D : Set (Set α)), A
  have hVfinite : V.Finite := D.finite_toSet.biUnion (fun A hA => hfinite A (hDF hA))
  have hVcard : V.ncard ≤ n * (k - 1) := by
    calc
      V.ncard ≤ ∑ A ∈ D, A.ncard := D.set_ncard_biUnion_le id
      _ = D.card * n := Finset.sum_const_nat (fun A hA => huniform A (hDF hA))
      _ ≤ (k - 1) * n := Nat.mul_le_mul_right n hDcard
      _ = n * (k - 1) := Nat.mul_comm _ _
  refine ⟨hVfinite.toFinset, ?_, ?_⟩
  · simpa only [← Set.ncard_eq_toFinset_card V hVfinite] using hVcard
  · intro A hA
    by_contra! hmiss
    have hAV : Disjoint A V := by
      refine Set.disjoint_left.mpr ?_
      intro x hxA hxV
      exact hmiss x (hVfinite.mem_toFinset.mpr hxV) hxA
    have hnotD : A ∉ D := by
      intro hAD
      obtain ⟨x, hx⟩ : A.Nonempty := (Set.ncard_pos (hfinite A hA)).mp (by
        rw [huniform A hA]
        exact hn)
      exact Set.disjoint_left.mp hAV hx (Set.mem_iUnion_of_mem A
        (Set.mem_iUnion_of_mem hAD hx))
    have hdisj : (insert A (D : Set (Set α))).PairwiseDisjoint id :=
      hDdisj.insert (fun B hB _ => hAV.mono_right (by
        intro x hx
        exact Set.mem_iUnion_of_mem B (Set.mem_iUnion_of_mem hB hx)))
    have hmem : insert A D ⊆ F ∧
        ((insert A D : Finset (Set α)) : Set (Set α)).PairwiseDisjoint id := by
      exact ⟨Finset.insert_subset hA hDF, by simpa only [Finset.coe_insert] using hdisj⟩
    exact hDmax.not_gt hmem (Finset.ssubset_insert hnotD)

/-- **Classical sunflower bound**, in contrapositive form. A finite family of
finite `n`-element sets with no `k`-petal sunflower has at most
`n.factorial * (k - 1) ^ n` members. This version includes `n = 0`. -/
theorem card_le_factorial_mul_pow (F : Finset (Set α)) (n k : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (huniform : ∀ A ∈ F, A.ncard = n)
    (hfree : ¬ HasSunflower F k) : F.card ≤ n.factorial * (k - 1) ^ n := by
  classical
  induction n generalizing F with
  | zero =>
    have hF : F ⊆ {∅} := by
      intro A hA
      exact Finset.mem_singleton.mpr ((Set.ncard_eq_zero (hfinite A hA)).mp (huniform A hA))
    simpa using Finset.card_le_card hF
  | succ n ih =>
    obtain ⟨U, hUcard, hhit⟩ := exists_small_hitting_finset F (n + 1) k
      (Nat.succ_pos n) hfinite huniform hfree
    have hfiber (x : α) :
        (F.filter (fun A => x ∈ A)).card ≤ n.factorial * (k - 1) ^ n := by
      let G := F.filter (fun A => x ∈ A)
      have hGx : ∀ A ∈ G, x ∈ A := fun A hA => (Finset.mem_filter.mp hA).2
      have hGF : G ⊆ F := Finset.filter_subset _ _
      have hEfinite : ∀ A ∈ G.image (fun B => B \ {x}), A.Finite := by
        intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        exact (hfinite B (hGF hB)).diff
      have hEuniform : ∀ A ∈ G.image (fun B => B \ {x}), A.ncard = n := by
        intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        rw [Set.ncard_diff_singleton_of_mem (hGx B hB), huniform B (hGF hB)]
        exact Nat.add_sub_cancel n 1
      have hEfree : ¬ HasSunflower (G.image (fun B => B \ {x})) k := by
        intro h
        exact hfree ((hasSunflower_of_erase hGx h).mono hGF)
      have hbound := ih (G.image (fun B => B \ {x})) hEfinite hEuniform hEfree
      rw [Finset.card_image_of_injOn (diff_singleton_injOn hGx)] at hbound
      exact hbound
    have hcover : F ⊆ U.biUnion (fun x => F.filter (fun A => x ∈ A)) := by
      intro A hA
      obtain ⟨x, hxU, hxA⟩ := hhit A hA
      exact Finset.mem_biUnion.mpr ⟨x, hxU, Finset.mem_filter.mpr ⟨hA, hxA⟩⟩
    calc
      F.card ≤ (U.biUnion (fun x => F.filter (fun A => x ∈ A))).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ x ∈ U, (F.filter (fun A => x ∈ A)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ U, n.factorial * (k - 1) ^ n :=
        Finset.sum_le_sum (fun x _ => hfiber x)
      _ = U.card * (n.factorial * (k - 1) ^ n) := by simp
      _ ≤ ((n + 1) * (k - 1)) * (n.factorial * (k - 1) ^ n) :=
        Nat.mul_le_mul_right _ hUcard
      _ = (n + 1).factorial * (k - 1) ^ (n + 1) := by
        rw [Nat.factorial_succ, pow_succ]
        ring

/-- A finite family above the classical bound contains a sunflower. -/
theorem hasSunflower_of_card_gt (F : Finset (Set α)) (n k : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (huniform : ∀ A ∈ F, A.ncard = n)
    (hcard : n.factorial * (k - 1) ^ n < F.card) : HasSunflower F k := by
  by_contra hfree
  exact (not_le_of_gt hcard) (card_le_factorial_mul_pow F n k hfinite huniform hfree)

/-- The finite-family form of the classical sunflower lemma, with the same
set-valued sunflower predicate used in Erdős problem 20. -/
theorem exists_sunflower_of_finite (F : Set (Set α)) (n k : ℕ)
    (hF : F.Finite) (hfinite : ∀ A ∈ F, A.Finite)
    (huniform : ∀ A ∈ F, A.ncard = n)
    (hcard : n.factorial * (k - 1) ^ n < F.ncard) :
    ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S := by
  obtain ⟨S, hSF, hcardS, hsun⟩ := hasSunflower_of_card_gt hF.toFinset n k
    (fun A hA => hfinite A (hF.mem_toFinset.mp hA))
    (fun A hA => huniform A (hF.mem_toFinset.mp hA))
    (by rwa [← Set.ncard_eq_toFinset_card F hF])
  exact ⟨(S : Set (Set α)), fun A hA => hF.mem_toFinset.mp (hSF hA),
    by simpa only [Set.ncard_coe_finset] using hcardS, hsun⟩

/-- Positive uniformity and a positive `ncard` force both the members and the
family to be finite. Thus no explicit finiteness assumptions are needed in the
exact `Set.ncard` formulation of the classical bound. -/
theorem exists_sunflower_of_ncard_gt (F : Set (Set α)) (n k : ℕ)
    (hn : 0 < n) (huniform : ∀ A ∈ F, A.ncard = n)
    (hcard : n.factorial * (k - 1) ^ n < F.ncard) :
    ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S := by
  have hF : F.Finite := Set.finite_of_ncard_pos ((Nat.zero_le _).trans_lt hcard)
  have hfinite : ∀ A ∈ F, A.Finite := by
    intro A hA
    apply Set.finite_of_ncard_pos
    rw [huniform A hA]
    exact hn
  exact exists_sunflower_of_finite F n k hF hfinite huniform hcard

/-- The exact threshold predicate from the definition in Erdős problem 20.
In particular, `α` ranges over `Type`, and `F` is a set of sets; the conjunction
is outside the uniformity quantifier. -/
def Threshold (n k m : ℕ) : Prop :=
  ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S

/-- The classical factorial threshold is valid for every positive uniformity.
The result actually holds for all `k`, hence in particular for `k ≥ 2`. -/
theorem factorial_threshold (n k : ℕ) (hn : 0 < n) :
    Threshold n k (n.factorial * (k - 1) ^ n + 1) := by
  intro α F hF
  exact exists_sunflower_of_ncard_gt F n k hn hF.1 (by omega)

/-- The set of valid thresholds is nonempty for positive uniformity. -/
theorem exists_threshold (n k : ℕ) (hn : 0 < n) : ∃ m, Threshold n k m :=
  ⟨n.factorial * (k - 1) ^ n + 1, factorial_threshold n k hn⟩

/-- The same nonemptiness statement with the original predicate written out. -/
theorem threshold_set_nonempty (n k : ℕ) (hn : 0 < n) :
    {m : ℕ | ∀ {α : Type}, ∀ (F : Set (Set α)),
      ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) →
        ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}.Nonempty :=
  exists_threshold n k hn

/-- Valid thresholds are upward closed. -/
theorem Threshold.mono {n k m m' : ℕ} (h : Threshold n k m) (hm : m ≤ m') :
    Threshold n k m' := by
  intro α F hF
  exact h F ⟨hF.1, hm.trans hF.2⟩

/-- An independent, literal copy of `Erdos20.f`. No theorem from `Spec` is used. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) →
      ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

/-- Positive uniformity makes the infimum an attained, valid threshold. -/
theorem f_is_threshold (n k : ℕ) (hn : 0 < n) : Threshold n k (f n k) :=
  Nat.sInf_mem (exists_threshold n k hn)

/-- Every valid threshold bounds the infimum from above. -/
theorem f_le_of_threshold {n k m : ℕ} (hm : Threshold n k m) : f n k ≤ m :=
  Nat.sInf_le hm

/-- The classical bound on the independent copy of the problem's function. -/
theorem f_le_factorial (n k : ℕ) (hn : 0 < n) :
    f n k ≤ n.factorial * (k - 1) ^ n + 1 :=
  f_le_of_threshold (factorial_threshold n k hn)

/-- For positive uniformity, the exact threshold set is the upper interval
starting at the infimum. -/
theorem threshold_iff_f_le (n k m : ℕ) (hn : 0 < n) :
    Threshold n k m ↔ f n k ≤ m := by
  constructor
  · exact f_le_of_threshold
  · intro h
    exact Threshold.mono (f_is_threshold n k hn) h

/-- With at least one petal requested, a threshold cannot be zero. -/
theorem zero_not_threshold (n k : ℕ) (hk : 0 < k) : ¬ Threshold n k 0 := by
  intro h
  obtain ⟨S, hS, hcard, _⟩ := h (∅ : Set (Set ℕ)) ⟨by simp, by simp⟩
  have hSempty : S = ∅ := Set.subset_empty_iff.mp hS
  simp only [hSempty, Set.ncard_empty] at hcard
  omega

/-- Nonemptiness of the threshold set rules out the junk infimum value zero
when positive uniformity and a positive number of petals are requested. -/
theorem f_pos (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : 0 < f n k := by
  apply Nat.pos_of_ne_zero
  intro hf
  have h : Threshold n k (f n k) := f_is_threshold n k hn
  rw [hf] at h
  exact zero_not_threshold n k hk h

end SunflowerFoundation
