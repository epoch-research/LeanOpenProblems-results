import Submission.ActivePrimePadding

/-! A supply of many moderately large primes, using only Euler's divergent
prime reciprocal sum. Also records private witnesses for a fixed zero-residue core. -/
namespace Erdos970.ActivePrimePadding
open Finset OptimalCoverCore LongIntervalConcentration

/-- Arbitrarily large supplies of k primes above D*k whose common upper bound
is smaller than k²/L. This is a subsequence assertion, not a prime asymptotic. -/
theorem exists_prime_supply (D L K : ℕ) :
    ∃ (k H : ℕ) (R : Finset ℕ), K ≤ k ∧ 0 < k ∧ R.card = k ∧
      L * H < k ^ 2 ∧ (∀ q ∈ R, q.Prime ∧ D * k < q ∧ q < H) := by
  classical
  obtain ⟨n, hn, hsmall⟩ := exists_nth_prime_small (4 * L * (D + 2) ^ 2)
    ((D + 2) * (K + 1))
  let k := n / (D + 2)
  let H := Nat.nth Nat.Prime n
  have hD : 0 < D + 2 := by omega
  have hk : K + 1 ≤ k := (Nat.le_div_iff_mul_le hD).mpr (by nlinarith)
  have hkn : (D + 2) * k ≤ n := by
    simpa [k, Nat.mul_comm] using Nat.div_mul_le_self n (D + 2)
  have hnk : n < (D + 2) * (k + 1) := Nat.lt_mul_div_succ n hD
  have hn2 : n ≤ 2 * (D + 2) * k := by nlinarith
  have hH : L * H < k ^ 2 := by
    change 4 * L * (D + 2) ^ 2 * H < n ^ 2 at hsmall
    have hs := Nat.pow_le_pow_left hn2 2
    nlinarith
  let U := H.primesBelow
  let E := (D * k + 1).primesBelow
  have hU : U.card = n := by
    change (Finset.filter Nat.Prime (Finset.range (Nat.nth Nat.Prime n))).card = n
    rw [← Nat.count_eq_card_filter_range]
    exact Nat.primeCounting'_nth_eq n
  have hE : E.card ≤ D * k + 1 :=
    (card_filter_le _ _).trans_eq (card_range _)
  have hbig : k ≤ (U \ E).card := by
    have hpart := card_sdiff_add_card U E
    have hle := card_le_card (subset_union_left (s₂ := E) : U ⊆ U ∪ E)
    nlinarith
  obtain ⟨R, hRU, hR⟩ := exists_subset_card_eq hbig
  refine ⟨k, H, R, by omega, by omega, hR, hH, ?_⟩
  intro q hq
  obtain ⟨hUq, hEq⟩ := mem_sdiff.mp (hRU hq)
  obtain ⟨hqH, hqprime⟩ := Nat.mem_primesBelow.mp hUq
  refine ⟨hqprime, ?_, hqH⟩
  by_contra hle
  exact hEq (Nat.mem_primesBelow.mpr ⟨by omega, hqprime⟩)

/-- The progression 1 mod the fixed core product supplies at least m/N survivors. -/
lemma zero_survivors_lower (m : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    m / (∏ p ∈ P, p) ≤ (survivors m P (fun _ => 0)).card := by
  classical
  let N := ∏ p ∈ P, p
  have hN : 0 < N := Finset.prod_pos (fun p hp => (hP p hp).pos)
  have hc := (BlockSieve.SievePolynomial.residue_count_bounds m N 1 hN).1
  apply hc.trans (card_le_card ?_)
  intro x hx
  obtain ⟨hxm, hxN⟩ := mem_filter.mp hx
  apply (mem_survivors _ _ _ _).mpr
  refine ⟨mem_range.mp hxm, ?_⟩
  intro p hp hbad
  have hpd : p ∣ N := dvd_prod_of_mem id hp
  have hxp : x ≡ 1 [MOD p] := hxN.of_dvd hpd
  have hh : 0 ≡ 1 [MOD p] := hbad.symm.trans hxp
  have := hh.eq_of_lt_of_lt (hP p hp).pos (hP p hp).one_lt
  omega

def coreWitnesses (P : Finset ℕ) : Finset ℕ := P ∪ P.image (fun p => p ^ 2)

lemma coreWitnesses_card (P : Finset ℕ) : (coreWitnesses P).card ≤ 2 * P.card := by
  have h1 := card_union_le P (P.image (fun p => p ^ 2))
  have h2 := card_image_le (s := P) (f := fun p => p ^ 2)
  dsimp only [coreWitnesses]
  omega

lemma core_witnesses (m : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hm : ∀ p ∈ P, p ^ 2 < m) : HasWitnesses m P (fun _ => 0) (coreWitnesses P) := by
  intro p hp
  have hprime := hP p hp
  have hp2 := hprime.two_le
  refine ⟨p, mem_union_left _ hp, p ^ 2,
    mem_union_right _ (mem_image.mpr ⟨p, hp, rfl⟩), ?_, ?_, ?_⟩
  · nlinarith
  · rw [mem_private_iff]
    refine ⟨by have := hm p hp; nlinarith, Nat.modEq_zero_iff_dvd.mpr (dvd_refl _), ?_⟩
    intro q hq hqp hbad
    have he := (Nat.dvd_prime hprime).mp (Nat.modEq_zero_iff_dvd.mp hbad)
    exact hqp (he.resolve_left (hP q hq).ne_one)
  · rw [mem_private_iff]
    refine ⟨hm p hp, Nat.modEq_zero_iff_dvd.mpr (dvd_pow_self _ (by decide)), ?_⟩
    intro q hq hqp hbad
    have hd : q ∣ p := (hP q hq).dvd_of_dvd_pow (Nat.modEq_zero_iff_dvd.mp hbad)
    exact hqp ((Nat.dvd_prime hprime).mp hd |>.resolve_left (hP q hq).ne_one)

/-- An elementary budget sufficient to invoke `pad_active` at quadratic length. -/
lemma padding_budget (N k f H m : ℕ) (hN : 0 < N) (hk : 64 * N ≤ k)
    (hf : f ≤ k) (hH : 8 * N * H < k ^ 2) (hm : k ^ 2 ≤ m) :
    H + (3 * k + f) * (k / (8 * N) + 1) < m / N := by
  have hdiv : 8 * N * (k / (8 * N) + 1) ≤ k + 8 * N := by
    have := Nat.div_mul_le_self k (8 * N)
    nlinarith
  have hfac := Nat.mul_le_mul_left (3 * k + f) hdiv
  have hf' := Nat.mul_le_mul_right (k + 8 * N) hf
  have hpow : 0 < k := by nlinarith
  have hmul : (H + (3 * k + f) * (k / (8 * N) + 1) + 1) * N ≤ m := by
    nlinarith
  exact (Nat.le_div_iff_mul_le hN).mpr hmul

#print axioms exists_prime_supply
#print axioms core_witnesses
#print axioms padding_budget
end Erdos970.ActivePrimePadding
