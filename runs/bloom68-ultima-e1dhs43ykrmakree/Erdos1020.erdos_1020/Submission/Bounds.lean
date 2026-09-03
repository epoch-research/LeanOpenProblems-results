import Submission.Spec

/-!
# Elementary bounds for the Erdős matching problem

These helpers prove the two standard construction lower bounds, the trivial upper bound,
and elementary boundary cases. They do not prove the general Erdős matching conjecture.
Only the definition `Erdos1020.f` is used from `Submission.Spec`.

The declarations between `namespace Erdos1020` and its closing `end` can also be pasted
inside that namespace after the definition of `f`, using the specification's imports.
-/

namespace Erdos1020

/-- A matching of `r`-sets contained in `V` uses exactly `r * M.card` vertices. -/
theorem uniform_matching_card_le {α : Type*} [DecidableEq α]
    {V : Finset α} {M : Finset (Finset α)} {r : ℕ}
    (hV : ∀ e ∈ M, e ⊆ V) (hr : ∀ e ∈ M, e.card = r)
    (hM : (M : Set (Finset α)).PairwiseDisjoint id) :
    r * M.card ≤ V.card := by
  classical
  calc
    r * M.card = ∑ e ∈ M, e.card := by
      rw [Finset.sum_congr rfl hr]
      simp [Nat.mul_comm]
    _ = (M.biUnion id).card := (Finset.card_biUnion hM).symm
    _ ≤ V.card := Finset.card_le_card (Finset.biUnion_subset.mpr hV)

/-- A matching whose every edge meets `S` has at most `S.card` edges.
The disjoint, nonempty intersections with `S` are counted by their union. -/
theorem matching_card_le_of_meets {α : Type*} [DecidableEq α]
    {S : Finset α} {M : Finset (Finset α)}
    (hS : ∀ e ∈ M, (e ∩ S).Nonempty)
    (hM : (M : Set (Finset α)).PairwiseDisjoint id) :
    M.card ≤ S.card := by
  classical
  have hinter : (M : Set (Finset α)).PairwiseDisjoint (fun e ↦ e ∩ S) :=
    hM.mono fun _ ↦ Finset.inter_subset_left
  calc
    M.card = ∑ _e ∈ M, 1 := by simp
    _ ≤ ∑ e ∈ M, (e ∩ S).card :=
      Finset.sum_le_sum fun e he ↦ Finset.card_pos.mpr (hS e he)
    _ = (M.biUnion (fun e ↦ e ∩ S)).card := (Finset.card_biUnion hinter).symm
    _ ≤ S.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ ↦
      Finset.inter_subset_right)

/-- Any matching-free `r`-uniform family on `Fin n` is a candidate in the supremum
that defines `f`. -/
theorem card_le_f_of_matching_free {n r k : ℕ} {H : Finset (Finset (Fin n))}
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ H ∧ M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id) :
    H.card ≤ f n r k := by
  classical
  unfold f
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hH, hfree⟩)

/-- The complete `r`-uniform family on fewer than `r * k` vertices has no
matching of size `k`. -/
theorem complete_family_matching_free {α : Type*} [DecidableEq α]
    {V : Finset α} {r k : ℕ} (hV : V.card < r * k) :
    ¬ ∃ M : Finset (Finset α),
      M ⊆ V.powersetCard r ∧ M.card = k ∧
        (M : Set (Finset α)).PairwiseDisjoint id := by
  rintro ⟨M, hM, hcard, hdisj⟩
  have hbound := uniform_matching_card_le
    (fun e he ↦ (Finset.mem_powersetCard.mp (hM he)).1)
    (fun e he ↦ (Finset.mem_powersetCard.mp (hM he)).2) hdisj
  rw [hcard] at hbound
  exact (Nat.not_le_of_gt hV) hbound

/-- Embed a complete `r`-uniform family on a fixed `m`-element subset of `Fin n`. -/
theorem complete_choose_le_f {n r k m : ℕ} (hmn : m ≤ n) (hmrk : m < r * k) :
    m.choose r ≤ f n r k := by
  classical
  obtain ⟨V, hV, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using hmn)
  have hfree := complete_family_matching_free (r := r) (k := k)
    (V := V) (by simpa [hcard] using hmrk)
  have hbound := card_le_f_of_matching_free (Finset.powersetCard_mono hV) hfree
  simpa [Finset.card_powersetCard, hcard] using hbound

/-- The family of `r`-subsets of `V` that meet the fixed set `S`. -/
def meetingFamily {α : Type*} [DecidableEq α] (V S : Finset α) (r : ℕ) :
    Finset (Finset α) :=
  (V.powersetCard r).filter fun e ↦ (e ∩ S).Nonempty

@[simp]
theorem mem_meetingFamily {α : Type*} [DecidableEq α]
    {V S e : Finset α} {r : ℕ} :
    e ∈ meetingFamily V S r ↔ e ⊆ V ∧ e.card = r ∧ (e ∩ S).Nonempty := by
  simp [meetingFamily, and_assoc]

/-- Count the sets meeting `S` by subtracting the `r`-subsets of `V \ S`. -/
theorem card_meetingFamily {α : Type*} [DecidableEq α]
    (V S : Finset α) (r : ℕ) (hSV : S ⊆ V) :
    (meetingFamily V S r).card = V.card.choose r - (V.card - S.card).choose r := by
  classical
  have heq : meetingFamily V S r = V.powersetCard r \ (V \ S).powersetCard r := by
    ext e
    simp only [mem_meetingFamily, Finset.mem_sdiff, Finset.mem_powersetCard]
    constructor
    · rintro ⟨heV, hecard, x, hx⟩
      refine ⟨⟨heV, hecard⟩, ?_⟩
      rintro ⟨heVS, _⟩
      exact (Finset.mem_sdiff.mp (heVS (Finset.mem_inter.mp hx).1)).2
        (Finset.mem_inter.mp hx).2
    · rintro ⟨⟨heV, hecard⟩, hnot⟩
      refine ⟨heV, hecard, ?_⟩
      by_contra hempty
      apply hnot
      refine ⟨?_, hecard⟩
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨heV hx, fun hxS ↦
        hempty ⟨x, Finset.mem_inter.mpr ⟨hx, hxS⟩⟩⟩
  rw [heq, Finset.card_sdiff_of_subset (Finset.powersetCard_mono Finset.sdiff_subset),
    Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_sdiff_of_subset hSV]

/-- If `S` has fewer than `k` vertices, the family of sets meeting `S` has no
matching of size `k`. -/
theorem meetingFamily_matching_free {α : Type*} [DecidableEq α]
    {V S : Finset α} {r k : ℕ} (hS : S.card < k) :
    ¬ ∃ M : Finset (Finset α),
      M ⊆ meetingFamily V S r ∧ M.card = k ∧
        (M : Set (Finset α)).PairwiseDisjoint id := by
  rintro ⟨M, hM, hcard, hdisj⟩
  have hbound := matching_card_le_of_meets
    (fun e he ↦ (mem_meetingFamily.mp (hM he)).2.2) hdisj
  rw [hcard] at hbound
  exact (Nat.not_le_of_gt hS) hbound

/-- Embed the family of all `r`-sets meeting a fixed `m`-element subset of `Fin n`. -/
theorem meeting_choose_le_f {n r k m : ℕ} (hmn : m ≤ n) (hmk : m < k) :
    n.choose r - (n - m).choose r ≤ f n r k := by
  classical
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using hmn)
  have hfree := meetingFamily_matching_free (V := Finset.univ) (r := r) (k := k)
    (S := S) (by simpa [hcard] using hmk)
  have hbound : (meetingFamily Finset.univ S r).card ≤ f n r k :=
    card_le_f_of_matching_free
      (Finset.filter_subset (s := (Finset.univ : Finset (Fin n)).powersetCard r)
        (p := fun e ↦ (e ∩ S).Nonempty)) hfree
  rw [card_meetingFamily _ _ _ hS] at hbound
  simpa [hcard] using hbound

/-- The complete-family term in the Erdős matching lower bound. -/
theorem clique_lower_bound {n r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (hn : r * k - 1 ≤ n) :
    (r * k - 1).choose r ≤ f n r k := by
  apply complete_choose_le_f hn
  exact Nat.sub_lt (Nat.mul_pos hr hk) (by decide)

/-- The fixed-cover term in the Erdős matching lower bound. -/
theorem cover_lower_bound {n r k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    n.choose r - (n - k + 1).choose r ≤ f n r k := by
  have hsub : n - (k - 1) = n - k + 1 := by omega
  rw [← hsub]
  exact meeting_choose_le_f (by omega) (by omega)

/-- Both standard constructions give the asserted lower bound throughout the
standard EMC range. This is only the lower-bound direction of the conjecture. -/
theorem emc_lower_bound (r : ℕ) (hr : 3 ≤ r) (n k : ℕ) (hk : 0 < k)
    (hn : r * k - 1 ≤ n) :
    max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) ≤ f n r k := by
  have hmul : 2 * k ≤ r * k := Nat.mul_le_mul_right k (by omega)
  have hkn : k ≤ n := by omega
  exact max_le (clique_lower_bound (by omega) hk hn) (cover_lower_bound hk hkn)

/-- Every candidate family consists of `r`-subsets of an `n`-element set. -/
theorem f_le_choose (n r k : ℕ) : f n r k ≤ n.choose r := by
  classical
  unfold f
  refine Finset.sup_le fun H hH ↦ ?_
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hH).1
  calc
    H.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard r).card :=
      Finset.card_le_card hsub
    _ = n.choose r := by simp

/-- Below `r * k` vertices even the complete `r`-uniform family is matching-free. -/
theorem f_eq_choose_of_lt {n r k : ℕ} (hn : n < r * k) :
    f n r k = n.choose r := by
  exact le_antisymm (f_le_choose n r k) (complete_choose_le_f le_rfl hn)

/-- A family with no matching of size one must be empty, including when `r = 0`. -/
theorem f_one (n r : ℕ) : f n r 1 = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  unfold f
  refine Finset.sup_le fun H hH ↦ ?_
  have hfree := (Finset.mem_filter.mp hH).2
  have hHempty : H = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    apply hfree
    refine ⟨{e}, Finset.singleton_subset_iff.mpr he, by simp, ?_⟩
    simp
  simp [hHempty]

/-- The complete family attains the upper bound at `n = r * k - 1`. -/
theorem f_at_threshold (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    f (r * k - 1) r k = (r * k - 1).choose r := by
  exact f_eq_choose_of_lt (Nat.sub_lt (Nat.mul_pos hr hk) (by decide))

/-- The displayed EMC formula holds in the boundary case `k = 1`. -/
theorem emc_eq_one (r : ℕ) (hr : 3 ≤ r) (n : ℕ) (hn : r - 1 ≤ n) :
    f n r 1 = max ((r - 1).choose r) (n.choose r - (n - 1 + 1).choose r) := by
  apply le_antisymm
  · rw [f_one]
    exact Nat.zero_le _
  · simpa using emc_lower_bound r hr n 1 (by decide) (by simpa using hn)

/-- The displayed EMC formula holds in the boundary case `n = r * k - 1`.
In fact this boundary case only needs `r > 0`. -/
theorem emc_eq_at_threshold (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    f (r * k - 1) r k =
      max ((r * k - 1).choose r)
        ((r * k - 1).choose r - (r * k - 1 - k + 1).choose r) := by
  rw [max_eq_left (Nat.sub_le _ _)]
  exact f_at_threshold r k hr hk

end Erdos1020

-- Axiom audit: no conjectural declaration from `Submission.Spec` is a dependency.
#print axioms Erdos1020.f
#print axioms Erdos1020.uniform_matching_card_le
#print axioms Erdos1020.matching_card_le_of_meets
#print axioms Erdos1020.card_le_f_of_matching_free
#print axioms Erdos1020.complete_family_matching_free
#print axioms Erdos1020.complete_choose_le_f
#print axioms Erdos1020.meetingFamily
#print axioms Erdos1020.mem_meetingFamily
#print axioms Erdos1020.card_meetingFamily
#print axioms Erdos1020.meetingFamily_matching_free
#print axioms Erdos1020.meeting_choose_le_f
#print axioms Erdos1020.clique_lower_bound
#print axioms Erdos1020.cover_lower_bound
#print axioms Erdos1020.emc_lower_bound
#print axioms Erdos1020.f_le_choose
#print axioms Erdos1020.f_eq_choose_of_lt
#print axioms Erdos1020.f_one
#print axioms Erdos1020.f_at_threshold
#print axioms Erdos1020.emc_eq_one
#print axioms Erdos1020.emc_eq_at_threshold
