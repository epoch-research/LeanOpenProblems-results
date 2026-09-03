import Submission.Boundary

/-!
# General matching-averaging bound and the remaining sharp obligation

These are auxiliary results, not a proof or disproof of the conjecture.
Neither conjectural declaration is used as a premise.
-/

namespace Erdos1020

/-- Embed a uniform partition into any sufficiently large ground set. -/
theorem exists_uniform_matching {n r t : ℕ} (hr : 0 < r) (hn : r * t ≤ n) :
    ∃ P : Finset (Finset (Fin n)), P.card = t ∧
      (∀ e ∈ P, e.card = r) ∧ (P : Set (Finset (Fin n))).PairwiseDisjoint id := by
  classical
  obtain ⟨P, hc, hu, hd, _⟩ :=
    exists_uniform_partition (α := Fin (r * t)) (r := r) (k := t) hr (by simp)
  let e := Fin.castLEEmb hn
  let E := (Finset.mapEmbedding e).toEmbedding
  refine ⟨P.map E, by simpa using hc, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    change (b.map e).card = r
    simpa using hu b hb
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
    exact (Finset.disjoint_map e).mpr
      (hd ha' hb' (fun h ↦ hab (congrArg E h)))

/-- Averaging a matching of arbitrary size `t` over permutations of `Fin n`. -/
theorem matching_free_mul_card_le {n r k t : ℕ} {H : Finset (Finset (Fin n))}
    (hr : 0 < r) (hn : r * t ≤ n)
    (hH : H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r)
    (hfree : ¬ ∃ M : Finset (Finset (Fin n)),
      M ⊆ H ∧ M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id) :
    t * H.card ≤ (k - 1) * n.choose r := by
  obtain ⟨P, hc, hu, hd⟩ := exists_uniform_matching hr hn
  simpa [hc] using matching_free_card_mul_le_of_matching hu hd
    (fun e he ↦ (Finset.mem_powersetCard.mp (hH he)).2) hfree

/-- A general, non-sharp upper bound for the extremal function. -/
theorem f_le_matching_average {n r k t : ℕ} (hr : 0 < r) (ht : 0 < t)
    (hn : r * t ≤ n) : f n r k ≤ ((k - 1) * n.choose r) / t := by
  classical
  unfold f
  refine Finset.sup_le fun H hH ↦ ?_
  have hc := Finset.mem_filter.mp hH
  apply (Nat.le_div_iff_mul_le ht).mpr
  simpa [Nat.mul_comm] using matching_free_mul_card_le hr hn
    (Finset.mem_powerset.mp hc.1) hc.2

/-- The strongest bound obtained by this single-matching averaging argument. -/
theorem f_le_floor_matching_average {n r k : ℕ} (hr : 0 < r) (hn : r ≤ n) :
    f n r k ≤ ((k - 1) * n.choose r) / (n / r) := by
  apply f_le_matching_average hr
  · exact Nat.div_pos hn hr
  · simpa [Nat.mul_comm] using Nat.div_mul_le_self n r

/-- The already proved constructions reduce the claimed equality to the sharp
upper bound on every actual matching-free family. -/
theorem emc_eq_iff_card_bound (r : ℕ) (hr : 3 ≤ r) (n k : ℕ)
    (hk : 0 < k) (hn : r * k - 1 ≤ n) :
    (f n r k = max ((r * k - 1).choose r)
      (n.choose r - (n - k + 1).choose r)) ↔
    ∀ H : Finset (Finset (Fin n)),
      H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r →
      (¬ ∃ M : Finset (Finset (Fin n)),
        M ⊆ H ∧ M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id) →
      H.card ≤ max ((r * k - 1).choose r)
        (n.choose r - (n - k + 1).choose r) := by
  classical
  constructor
  · intro heq H hH hfree
    exact (card_le_f_of_matching_free hH hfree).trans_eq heq
  · intro hbound
    apply le_antisymm _ (emc_lower_bound r hr n k hk hn)
    unfold f
    refine Finset.sup_le fun H hH ↦ ?_
    have hc := Finset.mem_filter.mp hH
    exact hbound H (Finset.mem_powerset.mp hc.1) hc.2

/-- Failure of the conjectured equality requires an actual family exceeding
both constructions, not merely a non-sharp relaxation. -/
theorem emc_ne_iff_witness (r : ℕ) (hr : 3 ≤ r) (n k : ℕ)
    (hk : 0 < k) (hn : r * k - 1 ≤ n) :
    (f n r k ≠ max ((r * k - 1).choose r)
      (n.choose r - (n - k + 1).choose r)) ↔
    ∃ H : Finset (Finset (Fin n)),
      H ⊆ (Finset.univ : Finset (Fin n)).powersetCard r ∧
      (¬ ∃ M : Finset (Finset (Fin n)),
        M ⊆ H ∧ M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id) ∧
      max ((r * k - 1).choose r) (n.choose r - (n - k + 1).choose r) < H.card := by
  classical
  constructor
  · intro hne
    by_contra hnone
    apply hne
    apply (emc_eq_iff_card_bound r hr n k hk hn).mpr
    intro H hH hfree
    by_contra hcard
    exact hnone ⟨H, hH, hfree, Nat.lt_of_not_ge hcard⟩
  · rintro ⟨H, hH, hfree, hlarge⟩ heq
    exact (not_lt_of_ge ((card_le_f_of_matching_free hH hfree).trans_eq heq)) hlarge

/-- Any counterexample in the stated range lies strictly beyond the proved
small-matching and partition boundary cases. -/
theorem emc_counterexample_range (r : ℕ) (hr : 3 ≤ r) (n k : ℕ)
    (hk : 0 < k) (hn : r * k - 1 ≤ n)
    (hcounter : f n r k ≠ max ((r * k - 1).choose r)
      (n.choose r - (n - k + 1).choose r)) :
    3 ≤ k ∧ r * k + 1 ≤ n := by
  have hk1 : k ≠ 1 := by
    intro h
    subst k
    apply hcounter
    simpa using emc_eq_one r hr n (by simpa using hn)
  have hk2 : k ≠ 2 := by
    intro h
    subst k
    exact hcounter (emc_eq_two r hr n hn)
  have hn1 : n ≠ r * k - 1 := by
    intro h
    subst n
    exact hcounter (emc_eq_at_threshold r k (by omega) hk)
  have hn2 : n ≠ r * k := by
    intro h
    subst n
    exact hcounter (emc_eq_at_multiple r k hr hk)
  omega

#print axioms exists_uniform_matching
#print axioms emc_ne_iff_witness
#print axioms emc_counterexample_range
#print axioms matching_free_mul_card_le
#print axioms f_le_matching_average
#print axioms f_le_floor_matching_average
#print axioms emc_eq_iff_card_bound

end Erdos1020
