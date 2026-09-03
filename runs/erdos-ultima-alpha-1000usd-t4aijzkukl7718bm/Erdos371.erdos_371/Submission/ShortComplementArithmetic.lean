import Submission.ShortComplementPattern
import Submission.RoughUnitWitness

/-! Identification of the short-complement pattern with its actual radical
divisor sum. The radical-size indicator is not imposed in this module. -/
namespace Erdos371
open Finset FiniteSieve

lemma moebius_squarefree_card (d : ℕ) (hd : Squarefree d) :
    (ArithmeticFunction.moebius d : ℝ)=(-1 : ℝ)^d.primeFactors.card := by
  have hc : d.primeFactors.card=ArithmeticFunction.cardFactors d := by
    rw [ArithmeticFunction.cardFactors_apply,← Nat.toFinset_factors]
    exact List.toFinset_card_of_nodup hd.nodup_primeFactorsList
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd,← hc]
  norm_cast

lemma squarefree_moebius_sum_eq_powerset (R : ℕ) (hR : Squarefree R) (f : ℕ → ℝ) :
    (∑ e ∈ R.divisors, (ArithmeticFunction.moebius e : ℝ)*f e) =
      ∑ E ∈ R.primeFactors.powerset, (-1 : ℝ)^E.card*f (∏ p ∈ E, p) := by
  rw [← sum_squarefree_divisors_eq_powerset R hR.ne_zero
    (fun E => (-1 : ℝ)^E.card*f (∏ p ∈ E, p))]
  apply sum_congr rfl
  intro e he
  have hsq := hR.squarefree_of_dvd (Nat.mem_divisors.mp he).1
  rw [if_pos hsq,Nat.prod_primeFactors_of_squarefree hsq,moebius_squarefree_card e hsq]

lemma rough_active_block_eq (B C n : ℕ) (hn : 0 < n) :
    activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n) =
      (roughRadical B (n*(n+1))).primeFactors.filter (fun p => p ≤ C) := by
  have hm : n*(n+1) ≠ 0 := by positivity
  rw [activeBlockPrimes_arithmetic _ (fun p hp => ((mem_largePrimeSet_iff p B C).mp hp).1) n,
    roughRadical_primeFactors]
  ext p
  simp only [mem_filter,mem_largePrimeSet_iff,Nat.mem_primeFactors,hm,
    ne_eq,not_false_eq_true,and_true]
  tauto

/-- The product cutoff alone forces every selected prime into the displayed
block and bounds the number of deleted primes. -/
lemma rough_short_subset_restrict (B C k n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hC : B^k ≤ C) (f : Finset ℕ → ℝ) :
    (∑ E ∈ (roughRadical B (n*(n+1))).primeFactors.powerset,
      if (∏ p ∈ E, p) ≤ B^k then f E else 0) =
    ∑ E ∈ (activeBlockPrimes (largePrimeSet B C)
        (activePrimeAtoms (largePrimeSet B C) n)).powerset,
      if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ B^k then f E else 0 := by
  let S := (roughRadical B (n*(n+1))).primeFactors
  let A := activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n)
  have hA : A=S.filter (fun p => p ≤ C) := rough_active_block_eq B C n hn
  have hAS : A ⊆ S := by rw [hA]; exact filter_subset _ _
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hlarge (p : ℕ) (hp : p ∈ S) : B < p := by
    dsimp only [S] at hp
    rw [roughRadical_primeFactors] at hp
    exact (mem_filter.mp hp).2
  change (∑ E ∈ S.powerset, if (∏ p ∈ E, p) ≤ B^k then f E else 0) =
    ∑ E ∈ A.powerset, if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ B^k then f E else 0
  calc
    _ = ∑ E ∈ S.powerset, if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ B^k then f E else 0 := by
      apply sum_congr rfl
      intro E hE
      by_cases hp : (∏ p ∈ E, p) ≤ B^k
      · rw [if_pos hp,if_pos ⟨short_prime_product_card_le E B k hB
          (fun p hp => hlarge p (mem_powerset.mp hE hp)) hp,hp⟩]
      · rw [if_neg hp,if_neg (not_and_of_not_right _ hp)]
    _ = _ := by
      symm
      apply sum_subset (powerset_mono.mpr hAS)
      intro E hE hnot
      apply if_neg
      rintro ⟨_,heprod⟩
      apply hnot
      apply mem_powerset.mpr
      intro p hp
      rw [hA]
      have hES := mem_powerset.mp hE
      have hprodpos : 0 < ∏ q ∈ E, q := prod_pos fun q hq => (hprime q (hES hq)).pos
      have hple : p ≤ ∏ q ∈ E, q := Nat.le_of_dvd hprodpos (dvd_prod_of_mem id hp)
      exact mem_filter.mpr ⟨hES hp,hple.trans (heprod.trans hC)⟩

/-- After deleting E, an occupied remainder of the block contains the true
least prime of the complementary radical. -/
lemma rough_complement_first_colour (B C n : ℕ) (hn : 0 < n) (E : Finset ℕ)
    (hE : E ⊆ activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n))
    (hocc : (activeBlockPrimes (largePrimeSet B C) (activePrimeAtoms (largePrimeSet B C) n)\E).Nonempty) :
    firstBlockColour (largePrimeSet B C\E) (activePrimeAtoms (largePrimeSet B C) n) =
      divisorSideColour n (roughRadical B (n*(n+1))/(∏ p ∈ E, p)) := by
  let P := largePrimeSet B C
  let A := activeBlockPrimes P (activePrimeAtoms P n)
  let R := roughRadical B (n*(n+1))
  let D := R/(∏ p ∈ E, p)
  have hA : A=R.primeFactors.filter (fun p => p ≤ C) := rough_active_block_eq B C n hn
  have hAS : A ⊆ R.primeFactors := by rw [hA]; exact filter_subset _ _
  have hES : E ⊆ R.primeFactors := hE.trans hAS
  have hD : D.primeFactors=R.primeFactors\E := by
    dsimp only [D]
    rw [← Nat.prod_primeFactors_sdiff_of_squarefree (roughRadical_squarefree B _) hES]
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1)
  have hsub : A\E ⊆ D.primeFactors := by
    rw [hD]
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨hAS (Finset.mem_sdiff.mp hp).1,(Finset.mem_sdiff.mp hp).2⟩
  obtain ⟨q,hq⟩ := hocc
  have hD1 : 1 < D := Nat.nonempty_primeFactors.mp ⟨q,hsub hq⟩
  have hpD : D.minFac ∈ D.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega),Nat.minFac_dvd D,by omega⟩
  have hpq : D.minFac ≤ q := Nat.minFac_le_of_dvd
    (Nat.prime_of_mem_primeFactors (hsub hq)).two_le (Nat.dvd_of_mem_primeFactors (hsub hq))
  have hpC : D.minFac ≤ C := by
    have hqA : q ∈ A := (Finset.mem_sdiff.mp hq).1
    rw [hA] at hqA
    exact hpq.trans (mem_filter.mp hqA).2
  have hpAE : D.minFac ∈ A\E := by
    have hp := hpD
    rw [hD] at hp
    apply Finset.mem_sdiff.mpr
    refine ⟨?_,(Finset.mem_sdiff.mp hp).2⟩
    rw [hA]
    exact mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1,hpC⟩
  have hmin : (A\E).min' ⟨q,hq⟩=D.minFac := by
    apply le_antisymm
    · exact min'_le _ _ hpAE
    · have hh := hsub ((A\E).min'_mem ⟨q,hq⟩)
      exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hh).two_le (Nat.dvd_of_mem_primeFactors hh)
  have hact : activeBlockPrimes (P\E) (activePrimeAtoms P n)=A\E := by
    ext p
    simp only [A,activeBlockPrimes,mem_filter,Finset.mem_sdiff]
    tauto
  have hpP : D.minFac ∈ P := (mem_filter.mp (Finset.mem_sdiff.mp hpAE).1).1
  have hpdiv : D.minFac ∣ n*(n+1) :=
    (Nat.dvd_of_mem_primeFactors (hAS (Finset.mem_sdiff.mp hpAE).1)).trans (roughRadical_dvd B _)
  unfold firstBlockColour
  change (if h : (activeBlockPrimes (P\E) (activePrimeAtoms P n)).Nonempty then
    atomColour ((activeBlockPrimes (P\E) (activePrimeAtoms P n)).min' h) (activePrimeAtoms P n) else 0)=_
  rw [hact,dif_pos ⟨q,hq⟩,hmin,
    prime_atomColour_arithmetic P D.minFac n hpP (Nat.minFac_prime (by omega)) hpdiv]
  rfl

noncomputable def shortRoughComplement (B k n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if e ≤ B^k then (ArithmeticFunction.moebius e : ℝ)*
        divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma shortRoughComplement_eq_block_sum (B C k n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hC : B^k ≤ C) :
    shortRoughComplement B k n =
      (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
        ∑ E ∈ (activeBlockPrimes (largePrimeSet B C)
            (activePrimeAtoms (largePrimeSet B C) n)).powerset,
          if E.card ≤ k ∧ (∏ p ∈ E, p) ≤ B^k then
            (-1 : ℝ)^E.card*divisorSideColour n
              (roughRadical B (n*(n+1))/(∏ p ∈ E, p)) else 0 := by
  unfold shortRoughComplement
  congr 1
  have he (e : ℕ) : (if e ≤ B^k then (ArithmeticFunction.moebius e : ℝ)*
      divisorSideColour n (roughRadical B (n*(n+1))/e) else 0) =
      (ArithmeticFunction.moebius e : ℝ)*
        (if e ≤ B^k then divisorSideColour n (roughRadical B (n*(n+1))/e) else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [squarefree_moebius_sum_eq_powerset _ (roughRadical_squarefree B _)]
  simp_rw [mul_ite,mul_zero]
  exact rough_short_subset_restrict B C k n hB hn hC _

/-- The actual short divisor sum equals the local odd pattern when more
than k block primes are active. -/
theorem shortRoughComplement_eq_pattern (B C k n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hC : B^k ≤ C)
    (hocc : k < (activeBlockPrimes (largePrimeSet B C)
      (activePrimeAtoms (largePrimeSet B C) n)).card) :
    shortRoughComplement B k n = fullRadicalParity n*
      naturalBlockParity (primesThrough B) n*
        shortComplementPattern (largePrimeSet B C) (B^k) k
          (activePrimeAtoms (largePrimeSet B C) n) := by
  rw [shortRoughComplement_eq_block_sum B C k n hB hn hC,
    roughRadical_moebius_eq_fullParity B n hn]
  congr 1
  unfold shortComplementPattern
  apply sum_congr rfl
  intro E hE
  by_cases h : E.card ≤ k ∧ (∏ p ∈ E, p) ≤ B^k
  · rw [if_pos h,if_pos h]
    congr 1
    symm
    apply rough_complement_first_colour B C n hn E (mem_powerset.mp hE)
    apply nonempty_iff_ne_empty.mpr
    intro hemp
    have hc := card_sdiff_add_card_eq_card (mem_powerset.mp hE)
    rw [hemp,card_empty,zero_add] at hc
    omega
  · rw [if_neg h,if_neg h]

#print axioms shortRoughComplement_eq_pattern
end Erdos371
