import Submission.CardinalitySieve
/-! Application of the cardinality-constrained sieve to odd covers. -/
namespace Erdos7CardinalitySieve
open Erdos7Reduction Erdos7FiniteSieve
set_option maxHeartbeats 2000000

def firstSixOddPrimes : Fin 6 → ℕ := ![3,5,7,11,13,17]
def ProfileCondition {ι : Type*} [Fintype ι] [DecidableEq ι] (p E : ι → ℕ) : Prop :=
  mixedCapacity (fun i => finitePrimeCapacity (p i) (E i)) < 1 ∨
    ∃ t : ℚ, 0 ≤ t ∧ thresholdCapacity p E 52 t < 1

/-- Sorted odd primes dominate the first six odd primes. -/
theorem sorted_first_six_lower (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime)
    (ho : ∀ i, Odd (p i)) (hmono : StrictMono p) :
    ∀ i, firstSixOddPrimes i ≤ p i := by
  let q (i : Fin 5) := p i.castSucc
  have hlow := sorted_first_five_lower q (fun i => hp i.castSucc)
    (fun i => ho i.castSucc) (fun _ _ hij => hmono hij)
  have h4 : 13 ≤ p 4 := hlow 4
  have h5 : 17 ≤ p 5 := by
    have := hmono (by decide : (4 : Fin 6) < 5)
    have := Nat.odd_iff.mp (ho 5)
    have hn15 : p 5 ≠ 15 := by intro he; have hh := hp 5; norm_num [he] at hh
    omega
  intro i
  fin_cases i
  · exact hlow 0
  · exact hlow 1
  · exact hlow 2
  · exact hlow 3
  · exact hlow 4
  · exact h5

/-- Seven distinct odd primes have total digit weight at least sixty-eight. -/
theorem seven_odd_prime_sum (P : Finset ℕ) (hcard : 7 ≤ P.card)
    (hp : ∀ p ∈ P, p.Prime ∧ Odd p) : 68 ≤ ∑ p ∈ P, (p - 1) := by
  classical
  obtain ⟨S, hSP, hSc⟩ := Finset.exists_subset_card_eq hcard
  let p := S.orderEmbOfFin hSc
  have hprime (i : Fin 7) : (p i).Prime := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).1
  have hodd (i : Fin 7) : Odd (p i) := (hp _ (hSP (S.orderEmbOfFin_mem hSc i))).2
  let q (i : Fin 6) := p i.castSucc
  have hlow : ∀ i : Fin 6, firstSixOddPrimes i ≤ q i :=
    sorted_first_six_lower q (fun i => hprime i.castSucc) (fun i => hodd i.castSucc)
      (fun _ _ hij => p.strictMono hij)
  have h5 : 17 ≤ p 5 := hlow 5
  have h6 : 19 ≤ p 6 := by
    have := p.strictMono (by decide : (5 : Fin 7) < 6)
    have := Nat.odd_iff.mp (hodd 6)
    omega
  have hfirst : 50 ≤ ∑ i : Fin 6, (q i - 1) := by
    calc
      50 = ∑ i : Fin 6, (firstSixOddPrimes i - 1) := by
        norm_num [firstSixOddPrimes, Fin.sum_univ_succ]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Nat.sub_le_sub_right (hlow i) 1)
  have hS : 68 ≤ ∑ r ∈ S, (r - 1) := by
    rw [← S.map_orderEmbOfFin_univ hSc, Finset.sum_map]
    change 68 ≤ ∑ i : Fin 7, (p i - 1)
    rw [Fin.sum_univ_castSucc]
    change 68 ≤ (∑ i : Fin 6, (q i - 1)) + (p 6 - 1)
    omega
  exact hS.trans (Finset.sum_le_sum_of_subset hSP)

/-- The arithmetic application of a finite family of profile certificates. -/
theorem no_cover_of_fiftyeight_profile_certificates {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ (m l : ℤ) ∣ x - a l)
    (hclosed : ∀ k d, 1 < d → d ∣ m k → ∃ l, m l = d)
    (hcard : Fintype.card κ ≤ 58)
    (r : ℕ) (q : Fin r → ℕ) (hq : ∀ i, 2 < q i)
    (hPcard : (Finset.univ.biUnion (fun k => (m k).primeFactors)).card = r)
    (hlower : ∀ i, q i ≤ (Finset.univ.biUnion (fun k => (m k).primeFactors)).orderEmbOfFin hPcard i)
    (hcert : ∀ E : Fin r → ℕ, (∀ i, 1 ≤ E i) → (∑ i, E i * (q i - 1)) < 58 →
      ProfileCondition q E)
    (hsmall : ∀ E : Fin r → ℕ, (∀ i, 1 ≤ E i) → (∑ i, E i) < 6 →
      mixedCapacity (fun i => finitePrimeCapacity (q i) (E i)) < 1) : False := by
  classical
  have hm : ∀ k, 1 < m k := fun k => (hc.2.1 k).1
  have hm0 : ∀ k, m k ≠ 0 := fun k => by have := hm k; omega
  have ho : ∀ k, Odd (m k) := fun k => (hc.2.1 k).2
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hpP : ∀ p ∈ P, p.Prime ∧ Odd p := by
    intro p hp
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hp
    have hh := Nat.mem_primeFactors.mp hk
    exact ⟨hh.1, (ho k).of_dvd_nat hh.2.1⟩
  let p := P.orderEmbOfFin hPcard
  have hprime (i : Fin r) : (p i).Prime := (hpP _ (P.orderEmbOfFin_mem hPcard i)).1
  have hlow (i : Fin r) : q i ≤ p i := hlower i
  have hp2 (i : Fin r) : 2 < p i := (hq i).trans_le (hlow i)
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (p.injective h))
  let e (k : κ) (i : Fin r) := (m k).factorization (p i)
  let E (i : Fin r) := Finset.univ.sup (fun k => e k i)
  have heE (k : κ) (i : Fin r) : e k i ≤ E i :=
    Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have hprod (k : κ) : m k = ∏ i : Fin r, p i ^ e k i := by
    have hsub : (m k).primeFactors ⊆ P := by
      intro t ht
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, ht⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) P hsub
    rw [Finset.prod_coe_sort P (fun t => t ^ (m k).factorization t)] at hh
    nth_rw 1 [hh]
    conv_lhs => rw [← P.map_orderEmbOfFin_univ hPcard]
    exact Finset.prod_map _ _ (fun t : ℕ => t ^ (m k).factorization t)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k, hprod l, hkl]
  have he0 (k : κ) : ∃ i, e k i ≠ 0 := by
    by_contra! h
    have hh := hm k
    rw [hprod k] at hh
    simp only [h, pow_zero, Finset.prod_const_one] at hh
    omega
  have hEpos (i : Fin r) : 1 ≤ E i := by
    have hiP := P.orderEmbOfFin_mem hPcard i
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hiP
    have hfac : 0 < e k i := (hprime i).factorization_pos_of_dvd (hm0 k)
      (Nat.mem_primeFactors.mp hk).2.1
    have hh := heE k i
    omega
  have hcov : ∀ x : ℤ, ∃ k, ((∏ i : Fin r, p i ^ e k i : ℕ) : ℤ) ∣ x - a k := by
    simpa only [← hprod] using hc.2.2
  have hprivate : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k →
      ¬ ((∏ i : Fin r, p i ^ e l i : ℕ) : ℤ) ∣ x - a l := by
    simpa only [← hprod] using hpriv
  have hweight := Erdos7Digits.coprime_power_irredundant_digit_bound p
    (fun i => (hprime i).pos) hcop e a hcov hprivate
  change (∑ i, E i * (p i - 1)) < Fintype.card κ at hweight
  have hfixedWeight : (∑ i, E i * (q i - 1)) < 58 := by
    have hle : (∑ i, E i * (q i - 1)) ≤ ∑ i, E i * (p i - 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_left (E i) (Nat.sub_le_sub_right (hlow i) 1)
    exact hle.trans_lt (hweight.trans_le hcard)
  have hbound := finite_exponent_cover_bound p E hp2 hcop e hei he0 heE a hcov
  have hleCap : mixedCapacity (fun i => finitePrimeCapacity (p i) (E i)) ≤
      mixedCapacity (fun i => finitePrimeCapacity (q i) (E i)) := by
    apply mixedCapacity_mono
    · intro i
      exact finitePrimeCapacity_nonneg (p i) (E i) (hp2 i)
    · intro i
      exact finitePrimeCapacity_antitone_base _ _ _ (hq i) (hlow i)
  have hEtotal : 6 ≤ ∑ i, E i := by
    by_contra h
    exact (not_lt_of_ge (hbound.trans hleCap)) (hsmall E hEpos (by omega))
  rcases hcert E hEpos hfixedWeight with hfull | ⟨t, ht, hthreshold⟩
  · exact (not_lt_of_ge (hbound.trans hleCap)) hfull
  · have hmixed := divisor_closed_mixed_card_bound m hm0 hclosed p hprime p.injective 58 hcard
    have hK : (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card ≤ 52 := by
      change (Finset.univ.filter (fun k => 2 ≤ (exponentSupport (e k)).card)).card ≤
        58 - ∑ i, E i at hmixed
      omega
    have hb := finite_exponent_cover_threshold p E hp2 hcop e hei he0 heE a hcov 52 hK t ht
    change (1 : ℚ) ≤ thresholdCapacity p E 52 t at hb
    have hle := thresholdCapacity_antitone_base q p E 52 t hq hlow
    exact (not_lt_of_ge (hb.trans hle)) hthreshold

theorem five_small_exponent_capacity (E : Fin 5 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hsum : (∑ i, E i) < 6) :
    mixedCapacity (fun i => finitePrimeCapacity (firstFiveOddPrimes i) (E i)) < 1 := by
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  have h3 := hE 3
  have h4 := hE 4
  have hEsum : E 0 + E 1 + E 2 + E 3 + E 4 < 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hconst : E = fun _ => 1 := by
    funext i
    fin_cases i <;> dsimp <;> omega
  rw [hconst]
  norm_num [mixedCapacity_eq, firstFiveOddPrimes, finitePrimeCapacity,
    positivePowerSum_eq_sum, Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.sum_range_succ]

theorem six_small_exponent_capacity (E : Fin 6 → ℕ) (hE : ∀ i, 1 ≤ E i)
    (hsum : (∑ i, E i) < 6) :
    mixedCapacity (fun i => finitePrimeCapacity (firstSixOddPrimes i) (E i)) < 1 := by
  have hle : 6 ≤ ∑ i, E i := by
    calc
      6 = ∑ _i : Fin 6, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hE i)
  omega

#print axioms no_cover_of_fiftyeight_profile_certificates
end Erdos7CardinalitySieve
