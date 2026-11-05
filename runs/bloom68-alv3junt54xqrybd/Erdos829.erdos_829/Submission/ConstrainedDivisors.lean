import Submission.Representation

/-!
# Unordered sums of cubes and constrained divisors

For a nonzero natural number, the sum of the two ordered cube roots gives a
bijection from its unordered representations to its constrained divisors.
The discriminant parameter is the difference of the roots; the inverse roots
are `(s - t) / 2` and `(s + t) / 2`.
-/

namespace Erdos829Aux

namespace ConstrainedDivisorsProof

lemma mem_rootPairs_iff {n x y : ℕ} :
    (x, y) ∈ rootPairs n ↔ x ^ 3 + y ^ 3 = n := by
  simp only [rootPairs, Finset.mem_filter, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    have hx := Nat.le_self_pow (by decide : 3 ≠ 0) x
    have hy := Nat.le_self_pow (by decide : 3 ≠ 0) y
    exact ⟨⟨by omega, by omega⟩, h⟩

lemma mem_unorderedPairs_iff {n x y : ℕ} :
    (x, y) ∈ unorderedPairs n ↔ x ≤ y ∧ x ^ 3 + y ^ 3 = n := by
  simp only [unorderedPairs, Finset.mem_filter, mem_rootPairs_iff]
  exact and_comm

lemma sum_dvd_sum_cubes {x y : ℕ} (hxy : x ≤ y) :
    x + y ∣ x ^ 3 + y ^ 3 := by
  refine ⟨x ^ 2 + y * (y - x), ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hxy
  simp only [Nat.add_sub_cancel_left]
  ring

lemma sum_cubes_discriminant {x y : ℕ} (hxy : x ≤ y) :
    4 * (x ^ 3 + y ^ 3) =
      (x + y) * ((x + y) ^ 2 + 3 * (y - x) ^ 2) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hxy
  simp only [Nat.add_sub_cancel_left]
  ring

lemma sum_mem_constrainedDivisors {n x y : ℕ} (hn : n ≠ 0)
    (hxy : x ≤ y) (hcubes : x ^ 3 + y ^ 3 = n) :
    x + y ∈ constrainedDivisors n := by
  classical
  simp only [constrainedDivisors, Finset.mem_filter]
  refine ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, y - x, ?_, ?_, ?_⟩
  · rw [← hcubes]
    exact sum_dvd_sum_cubes hxy
  · apply Finset.mem_range.mpr
    omega
  · omega
  · rw [← hcubes]
    exact sum_cubes_discriminant hxy

/-- For a nonzero sum, its discriminant determines the nonnegative difference. -/
lemma difference_unique {n s t u : ℕ} (hs : s ≠ 0)
    (ht : 4 * n = s * (s ^ 2 + 3 * t ^ 2))
    (hu : 4 * n = s * (s ^ 2 + 3 * u ^ 2)) : t = u := by
  have h := mul_left_cancel₀ hs (ht.symm.trans hu)
  apply (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp
  omega

/-- The parity and discriminant conditions reconstruct an unordered root pair. -/
lemma pair_from_constraint {n s t : ℕ} (ht : t ≤ s)
    (hparity : t % 2 = s % 2)
    (heq : 4 * n = s * (s ^ 2 + 3 * t ^ 2)) :
    ((s - t) / 2, (s + t) / 2) ∈ unorderedPairs n ∧
      (s - t) / 2 + (s + t) / 2 = s ∧
      (s + t) / 2 - (s - t) / 2 = t := by
  have hsum : (s - t) / 2 + (s + t) / 2 = s := by omega
  have hdiff : (s + t) / 2 - (s - t) / 2 = t := by omega
  have hle : (s - t) / 2 ≤ (s + t) / 2 := by omega
  have hcubes : ((s - t) / 2) ^ 3 + ((s + t) / 2) ^ 3 = n := by
    have h := sum_cubes_discriminant hle
    rw [hsum, hdiff] at h
    omega
  exact ⟨mem_unorderedPairs_iff.mpr ⟨hle, hcubes⟩, hsum, hdiff⟩

end ConstrainedDivisorsProof

/-- A constrained divisor is exactly the sum of an unordered root pair. -/
theorem mem_constrainedDivisors_iff_exists_unorderedPair {n s : ℕ} (hn : n ≠ 0) :
    s ∈ constrainedDivisors n ↔
      ∃ p ∈ unorderedPairs n, p.1 + p.2 = s := by
  classical
  constructor
  · intro hs
    simp only [constrainedDivisors, Finset.mem_filter] at hs
    rcases hs.2 with ⟨t, ht, hparity, heq⟩
    have htle : t ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
    rcases ConstrainedDivisorsProof.pair_from_constraint htle hparity heq with
      ⟨hmem, hsum, _⟩
    exact ⟨_, hmem, hsum⟩
  · rintro ⟨⟨x, y⟩, hmem, rfl⟩
    rcases ConstrainedDivisorsProof.mem_unorderedPairs_iff.mp hmem with ⟨hxy, hcubes⟩
    exact ConstrainedDivisorsProof.sum_mem_constrainedDivisors hn hxy hcubes

/-- On unordered representations of a nonzero number, the root sum is injective. -/
theorem unorderedPairs_sum_injective {n : ℕ} (hn : n ≠ 0) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (unorderedPairs n) := by
  rintro ⟨x, y⟩ hp ⟨u, v⟩ hq hsum
  change x + y = u + v at hsum
  rcases ConstrainedDivisorsProof.mem_unorderedPairs_iff.mp hp with ⟨hxy, hxycubes⟩
  rcases ConstrainedDivisorsProof.mem_unorderedPairs_iff.mp hq with ⟨huv, huvcubes⟩
  have hs : x + y ≠ 0 := by
    intro hz
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    apply hn
    simpa [hx, hy] using hxycubes.symm
  have ht : 4 * n = (x + y) * ((x + y) ^ 2 + 3 * (y - x) ^ 2) := by
    rw [← hxycubes]
    exact ConstrainedDivisorsProof.sum_cubes_discriminant hxy
  have hu : 4 * n = (x + y) * ((x + y) ^ 2 + 3 * (v - u) ^ 2) := by
    rw [hsum, ← huvcubes]
    exact ConstrainedDivisorsProof.sum_cubes_discriminant huv
  have hdiff := ConstrainedDivisorsProof.difference_unique hs ht hu
  apply Prod.ext <;> dsimp only
  · omega
  · omega

/-- The image of the root-sum map is exactly the constrained divisor finset. -/
theorem unorderedPairs_sum_image (n : ℕ) (hn : n ≠ 0) :
    (unorderedPairs n).image (fun p => p.1 + p.2) = constrainedDivisors n := by
  classical
  ext s
  simp only [Finset.mem_image]
  exact (mem_constrainedDivisors_iff_exists_unorderedPair hn).symm

/-- Root sums give a cardinality-preserving bijection to constrained divisors. -/
theorem unorderedPairs_card_eq_constrainedDivisors_card (n : ℕ) (hn : n ≠ 0) :
    (unorderedPairs n).card = (constrainedDivisors n).card := by
  classical
  apply Finset.card_bij (fun p _ => p.1 + p.2)
  · intro p hp
    exact (mem_constrainedDivisors_iff_exists_unorderedPair hn).mpr ⟨p, hp, rfl⟩
  · intro p hp q hq hsum
    exact unorderedPairs_sum_injective hn hp hq hsum
  · intro s hs
    rcases (mem_constrainedDivisors_iff_exists_unorderedPair hn).mp hs with ⟨p, hp, hsum⟩
    exact ⟨p, hp, hsum⟩

/-- Every ordered root pair is an unordered representative or its swap. -/
theorem rootPairs_eq_unorderedPairs_union_swap (n : ℕ) :
    rootPairs n = unorderedPairs n ∪ (unorderedPairs n).image Prod.swap := by
  classical
  ext ⟨x, y⟩
  constructor
  · intro hp
    have hcubes := ConstrainedDivisorsProof.mem_rootPairs_iff.mp hp
    rcases le_total x y with hxy | hyx
    · exact Finset.mem_union.mpr (Or.inl
        (ConstrainedDivisorsProof.mem_unorderedPairs_iff.mpr ⟨hxy, hcubes⟩))
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨(y, x), ?_, rfl⟩
      apply ConstrainedDivisorsProof.mem_unorderedPairs_iff.mpr
      exact ⟨hyx, by simpa only [add_comm] using hcubes⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · rcases Finset.mem_image.mp hp with ⟨⟨u, v⟩, hq, hswap⟩
      rw [← hswap]
      apply ConstrainedDivisorsProof.mem_rootPairs_iff.mpr
      have hcubes := (ConstrainedDivisorsProof.mem_unorderedPairs_iff.mp hq).2
      simpa only [add_comm] using hcubes

/-- Each unordered representation gives at most two ordered representations. -/
theorem rootPairs_card_le_two_mul_unorderedPairs_card (n : ℕ) :
    (rootPairs n).card ≤ 2 * (unorderedPairs n).card := by
  classical
  calc
    (rootPairs n).card =
        (unorderedPairs n ∪ (unorderedPairs n).image Prod.swap).card := by
      rw [rootPairs_eq_unorderedPairs_union_swap n]
    _ ≤ (unorderedPairs n).card + ((unorderedPairs n).image Prod.swap).card :=
      Finset.card_union_le _ _
    _ ≤ (unorderedPairs n).card + (unorderedPairs n).card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * (unorderedPairs n).card := by omega

/-- The ordered representation count is at most twice the constrained divisor count. -/
theorem rootPairs_card_le_two_mul_constrainedDivisors_card (n : ℕ) (hn : n ≠ 0) :
    (rootPairs n).card ≤ 2 * (constrainedDivisors n).card := by
  rw [← unorderedPairs_card_eq_constrainedDivisors_card n hn]
  exact rootPairs_card_le_two_mul_unorderedPairs_card n

end Erdos829Aux
