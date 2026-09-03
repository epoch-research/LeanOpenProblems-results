import Submission.BrunCriterion

/-! Exact inclusion-exclusion on a small core followed by one tail union bound.
The resulting quadratic theorem has an explicit restriction on the small core.
-/
namespace Erdos970.CoreTailSieve
open Finset
open Erdos970.BrunCriterion

noncomputable def siftSet (Q T : Finset ℕ) (r : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  (range m).filter (fun i => (∀ q ∈ Q, ¬i ≡ r q [MOD q]) ∧
    (∀ p ∈ T, i ≡ r p [MOD p]))

noncomputable def siftCount (Q T : Finset ℕ) (r : ℕ → ℕ) (m : ℕ) : ℝ :=
  (siftSet Q T r m).card

noncomputable def density (Q : Finset ℕ) : ℝ := ∏ q ∈ Q, (1 - 1 / (q : ℝ))

lemma siftCount_split (Q T : Finset ℕ) (r : ℕ → ℕ) (m q : ℕ) :
    siftCount (insert q Q) T r m + siftCount Q (insert q T) r m =
      siftCount Q T r m := by
  classical
  have hno : (siftSet Q T r m).filter (fun i => ¬i ≡ r q [MOD q]) =
      siftSet (insert q Q) T r m := by
    ext i
    simp only [siftSet, mem_filter, forall_mem_insert]
    tauto
  have hyes : (siftSet Q T r m).filter (fun i => i ≡ r q [MOD q]) =
      siftSet Q (insert q T) r m := by
    ext i
    simp only [siftSet, mem_filter, forall_mem_insert]
    tauto
  have hh := card_filter_add_card_filter_not (s := siftSet Q T r m)
    (fun i => i ≡ r q [MOD q])
  rw [hno, hyes] at hh
  unfold siftCount
  exact_mod_cast (by omega : (siftSet (insert q Q) T r m).card +
    (siftSet Q (insert q T) r m).card = (siftSet Q T r m).card)

/-- Avoiding s core primes costs at most 2^s CRT remainders, also after imposing
any disjoint set of required prime hits. -/
theorem siftCount_error (Q T : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (hT : ∀ p ∈ T, p.Prime) (hdis : Disjoint Q T) (r : ℕ → ℕ) (m : ℕ) :
    |siftCount Q T r m - (m : ℝ) * density Q / ∏ p ∈ T, (p : ℝ)| ≤
      (2 : ℝ) ^ Q.card := by
  classical
  induction Q using Finset.induction_on generalizing T with
  | empty =>
    simpa [siftCount, siftSet, density] using intersection_count_error T hT r m
  | @insert q Q hqQ ih =>
    have hq : q.Prime := hQ q (mem_insert_self _ _)
    have hQ' : ∀ p ∈ Q, p.Prime := fun p hp => hQ p (mem_insert_of_mem hp)
    have hqT : q ∉ T := fun h => (disjoint_left.mp hdis) (mem_insert_self _ _) h
    have hd : Disjoint Q T := hdis.mono_left (subset_insert _ _)
    have hd' : Disjoint Q (insert q T) := by
      rw [disjoint_insert_right]
      exact ⟨hqQ, hd⟩
    have hT' : ∀ p ∈ insert q T, p.Prime := by
      intro p hp
      rcases mem_insert.mp hp with rfl | hp
      · exact hq
      · exact hT p hp
    have h0 := ih T hQ' hT hd
    have h1 := ih (insert q T) hQ' hT' hd'
    have hsplit := siftCount_split Q T r m q
    have hmean : (m : ℝ) * density (insert q Q) / ∏ p ∈ T, (p : ℝ) =
        (m : ℝ) * density Q / ∏ p ∈ T, (p : ℝ) -
        (m : ℝ) * density Q / ∏ p ∈ insert q T, (p : ℝ) := by
      rw [density, prod_insert hqQ, prod_insert hqT]
      change (m : ℝ) * ((1 - 1 / (q : ℝ)) * density Q) / _ = _
      ring
    have he : siftCount (insert q Q) T r m -
        (m : ℝ) * density (insert q Q) / ∏ p ∈ T, (p : ℝ) =
        (siftCount Q T r m - (m : ℝ) * density Q / ∏ p ∈ T, (p : ℝ)) -
        (siftCount Q (insert q T) r m -
          (m : ℝ) * density Q / ∏ p ∈ insert q T, (p : ℝ)) := by
      rw [hmean]
      linarith
    rw [he, card_insert_of_notMem hqQ, pow_succ]
    exact (abs_sub _ _).trans (by linarith)

lemma siftCount_le_tail {Q R : Finset ℕ} {r : ℕ → ℕ} {m : ℕ}
    (hcover : ∀ i < m, ∃ p ∈ Q ∪ R, i ≡ r p [MOD p]) :
    siftCount Q ∅ r m ≤ ∑ p ∈ R, siftCount Q {p} r m := by
  classical
  have hsub : siftSet Q ∅ r m ⊆ R.biUnion (fun p => siftSet Q {p} r m) := by
    intro i hi
    obtain ⟨him, hQ, _⟩ := mem_filter.mp hi
    obtain ⟨p, hp, hip⟩ := hcover i (mem_range.mp him)
    have hpR : p ∈ R := (mem_union.mp hp).resolve_left (fun hpQ => hQ p hpQ hip)
    apply mem_biUnion.mpr
    refine ⟨p, hpR, mem_filter.mpr ⟨him, hQ, ?_⟩⟩
    simpa using hip
  have hc := (card_le_card hsub).trans card_biUnion_le
  unfold siftCount
  exact_mod_cast hc

/-- Main term versus full remainder for one exact core and an arbitrary disjoint
prime tail. This does not require any unproved relative-removal estimate. -/
theorem cover_core_tail_bound (Q R : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hdis : Disjoint Q R) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ i < m, ∃ p ∈ Q ∪ R, i ≡ r p [MOD p]) :
    (m : ℝ) * density Q * (1 - ∑ p ∈ R, 1 / (p : ℝ)) ≤
      (2 : ℝ) ^ Q.card * (R.card + 1) := by
  classical
  have h0 := (abs_le.mp (siftCount_error Q ∅ hQ (by simp) (by simp) r m)).1
  simp only [prod_empty, div_one] at h0
  have hp (p : ℕ) (hp : p ∈ R) :
      siftCount Q {p} r m ≤ (m : ℝ) * density Q / p + (2 : ℝ) ^ Q.card := by
    have hds : Disjoint Q {p} := hdis.mono_right (singleton_subset_iff.mpr hp)
    have hh := (abs_le.mp (siftCount_error Q {p} hQ
      (by simpa using hR p hp) hds r m)).2
    simp only [prod_singleton] at hh
    linarith
  have hs := sum_le_sum hp
  have hs' : (∑ p ∈ R, ((m : ℝ) * density Q / p + (2 : ℝ) ^ Q.card)) =
      (m : ℝ) * density Q * (∑ p ∈ R, 1 / (p : ℝ)) + R.card * (2 : ℝ) ^ Q.card := by
    simp [sum_add_distrib, div_eq_mul_inv, mul_sum]
  rw [hs'] at hs
  have hc := siftCount_le_tail hcover
  nlinarith only [h0, hs, hc]

/-- A tail of reciprocal mass at most one half leaves a positive main term. -/
theorem cover_length_le (Q R : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ p ∈ R, p.Prime)
    (hdis : Disjoint Q R) (r : ℕ → ℕ) (m : ℕ)
    (hcover : ∀ i < m, ∃ p ∈ Q ∪ R, i ≡ r p [MOD p])
    (htail : (∑ p ∈ R, 1 / (p : ℝ)) ≤ 1 / 2) :
    m ≤ 2 * (Q.card + 1) * 2 ^ Q.card * (R.card + 1) := by
  have hmain := cover_core_tail_bound Q R hQ hR hdis r m hcover
  have hden := (prime_product_bounds Q hQ).1
  change 1 / ((Q.card : ℝ) + 1) ≤ density Q at hden
  have hden0 : 0 ≤ density Q := (by positivity : (0 : ℝ) ≤ 1 / (Q.card + 1)).trans hden
  have hmd : (m : ℝ) * density Q / 2 ≤
      (m : ℝ) * density Q * (1 - ∑ p ∈ R, 1 / (p : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤
      1 - ∑ p ∈ R, 1 / (p : ℝ) by linarith) (mul_nonneg (Nat.cast_nonneg m) hden0)
    nlinarith only [hh]
  have hden' : 1 ≤ density Q * ((Q.card : ℝ) + 1) :=
    (div_le_iff₀ (by positivity)).mp hden
  have hh := mul_le_mul_of_nonneg_left hden' (Nat.cast_nonneg m)
  have hbound := mul_le_mul_of_nonneg_right (hmd.trans hmain)
    (show (0 : ℝ) ≤ 2 * (Q.card + 1) by positivity)
  have hfinal : (m : ℝ) ≤ 2 * ((Q.card : ℝ) + 1) * (2 : ℝ) ^ Q.card * (R.card + 1) := by
    nlinarith only [hh, hbound]
  exact_mod_cast hfinal

#print axioms siftCount_error
#print axioms cover_core_tail_bound
#print axioms cover_length_le
end Erdos970.CoreTailSieve
