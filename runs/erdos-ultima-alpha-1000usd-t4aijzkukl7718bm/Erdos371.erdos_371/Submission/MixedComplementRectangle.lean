import Submission.HighComplementAlgebra
import Submission.ShortComplementIndicator

/-! A genuine mixed complementary subrange: e=f*g, where f is short and
all primes of g exceed an independent cutoff W. The actual size condition
and the complete Möbius and colour weights are retained. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

noncomputable def mixedComplementRectangleAt (B D W F X n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ f ∈ (roughRadical B (n*(n+1))).divisors,
      ∑ g ∈ (roughRadical W (n*(n+1))).divisors,
        if f ≤ F ∧ 1 < g ∧ g ≤ X ∧ D*(f*g) < roughRadical B (n*(n+1)) then
          (ArithmeticFunction.moebius (f*g) : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/(f*g))
        else 0

lemma small_high_coprime (W m f g : ℕ) (hf : 0 < f) (hfW : f ≤ W)
    (hg : g ∣ roughRadical W m) : f.Coprime g := by
  apply Nat.coprime_of_dvd
  intro p hp hpf hpg
  have hlo := roughRadical_prime_large W m p hp (hpg.trans hg)
  have hhi := (Nat.le_of_dvd hf hpf).trans hfW
  omega

lemma short_rough_prime_card (B k n f : ℕ) (hB : 1 < B)
    (hf : f ∣ roughRadical B (n*(n+1))) (hfk : f ≤ B^k) : f.primeFactors.card ≤ k := by
  have hsf := (roughRadical_squarefree B _).squarefree_of_dvd hf
  apply short_prime_product_card_le f.primeFactors B k hB
  · intro p hp
    exact roughRadical_prime_large B _ p (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hf)
  · rwa [Nat.prod_primeFactors_of_squarefree hsf]

lemma short_delete_surviving_small_prime (B W k n f : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hf : f ∣ roughRadical B (n*(n+1))) (hfk : f ≤ B^k)
    (hocc : k < (activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)).card) :
    1 < roughRadical B (n*(n+1))/f ∧ (roughRadical B (n*(n+1))/f).minFac ≤ W := by
  let R := roughRadical B (n*(n+1))
  let A := activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)
  have hR : 0 < R := roughRadical_pos B _
  have hf0 : 0 < f := Nat.pos_of_dvd_of_pos hf hR
  have hcard := short_rough_prime_card B k n f hB hf hfk
  change k < A.card at hocc
  have hnot : ¬A ⊆ f.primeFactors := by
    intro hs
    have hh := (card_le_card hs).trans hcard
    omega
  obtain ⟨q,hq,hqf⟩ := not_subset.mp hnot
  dsimp only [A] at hq
  rw [rough_active_block_eq B W n hn] at hq
  obtain ⟨hqr,hqW⟩ := mem_filter.mp hq
  have hp := Nat.prime_of_mem_primeFactors hqr
  have hqR : q ∣ R := Nat.dvd_of_mem_primeFactors hqr
  have hqnot : ¬q ∣ f := fun hd => hqf (Nat.mem_primeFactors.mpr ⟨hp,hd,hf0.ne'⟩)
  have hqd : q ∣ R/f := by
    have hmul : f*(R/f)=R := Nat.mul_div_cancel' hf
    have hm : q ∣ f*(R/f) := by rw [hmul]; exact hqR
    exact (hp.dvd_mul.mp hm).resolve_left hqnot
  have hpos : 0 < R/f := Nat.div_pos (Nat.le_of_dvd hR hf) hf0
  have hqle := Nat.le_of_dvd hpos hqd
  exact ⟨hp.one_lt.trans_le hqle,(Nat.minFac_le_of_dvd hp.two_le hqd).trans hqW⟩

lemma mixed_short_high_colour (B W k n f g : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hBW : B ≤ W) (hBk : B^k ≤ W)
    (hf : f ∣ roughRadical B (n*(n+1))) (hfk : f ≤ B^k)
    (hg : g ∣ roughRadical W (n*(n+1)))
    (hocc : k < (activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)).card) :
    (ArithmeticFunction.moebius (f*g) : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/(f*g))=
      (ArithmeticFunction.moebius g : ℝ)*(ArithmeticFunction.moebius f : ℝ)*
        divisorSideColour n (roughRadical B (n*(n+1))/f) := by
  have hR := roughRadical_pos B (n*(n+1))
  have hf0 := Nat.pos_of_dvd_of_pos hf hR
  have hcop := small_high_coprime W _ f g hf0 (hfk.trans hBk) hg
  have hgR := hg.trans (roughRadical_dvd_of_le B W _ hBW)
  have hprod := hcop.mul_dvd_of_dvd_of_dvd hf hgR
  have hgd : g ∣ roughRadical B (n*(n+1))/f :=
    Nat.dvd_div_of_mul_dvd (by simpa only [Nat.mul_comm] using hprod)
  obtain ⟨hd1,hdW⟩ := short_delete_surviving_small_prime B W k n f hB hn hf hfk hocc
  have hp := Nat.minFac_prime (by omega : roughRadical B (n*(n+1))/f ≠ 1)
  have hnot : ¬(roughRadical B (n*(n+1))/f).minFac ∣ g := by
    intro h
    exact (not_lt_of_ge hdW) (roughRadical_prime_large W _ _ hp (h.trans hg))
  have hmin := minFac_div_of_not_dvd _ g hd1 hgd hnot
  rw [Nat.div_div_eq_div_mul] at hmin
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,Int.cast_mul]
  simp only [divisorSideColour,hmin]
  ring

lemma mixedComplementRectangleAt_factor (B D W F X k n : ℕ) (hB : 1 < B) (hn : 0 < n)
    (hBW : B ≤ W) (hBk : B^k ≤ W) (hF : F ≤ B^k)
    (hocc : k < (activeBlockPrimes (largePrimeSet B W) (activePrimeAtoms (largePrimeSet B W) n)).card)
    (hlarge : D*(B^k*X) < roughRadical B (n*(n+1))) :
    mixedComplementRectangleAt B D W F X n=
      highDivisorWeight W X n*untruncatedComplementPrefix B F n := by
  unfold mixedComplementRectangleAt highDivisorWeight untruncatedComplementPrefix
  rw [mul_left_comm]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro f hf
  by_cases hfF : f ≤ F
  · rw [if_pos hfF,sum_mul]
    apply sum_congr rfl
    intro g hg
    by_cases h : 1 < g ∧ g ≤ X
    · have hd : D*(f*g) < roughRadical B (n*(n+1)) :=
        (Nat.mul_le_mul_left D (Nat.mul_le_mul (hfF.trans hF) h.2)).trans_lt hlarge
      rw [if_pos ⟨hfF,h.1,h.2,hd⟩,if_pos h]
      rw [mixed_short_high_colour B W k n f g hB hn hBW hBk (Nat.mem_divisors.mp hf).1
        (hfF.trans hF) (Nat.mem_divisors.mp hg).1 hocc]
      ring
    · have hnot : ¬(f ≤ F ∧ 1 < g ∧ g ≤ X ∧ D*(f*g) < roughRadical B (n*(n+1))) :=
        fun hh => h ⟨hh.2.1,hh.2.2.1⟩
      rw [if_neg hnot,if_neg h,zero_mul]
  · simp only [hfF,false_and,if_false,sum_const_zero,mul_zero]

lemma short_divisor_count_le_exp (B k F n : ℕ) (_hB : 1 < B) (hn : 0 < n) (hF : F ≤ B^k) :
    (((roughRadical B (n*(n+1))).divisors.filter (fun f => f ≤ F)).card : ℝ) ≤
      (2 : ℝ)^(activeBlockPrimes (largePrimeSet B (B^k)) (activePrimeAtoms (largePrimeSet B (B^k)) n)).card := by
  let R := roughRadical B (n*(n+1))
  let A := activeBlockPrimes (largePrimeSet B (B^k)) (activePrimeAtoms (largePrimeSet B (B^k)) n)
  have hA : A=R.primeFactors.filter (fun p => p ≤ B^k) := rough_active_block_eq B (B^k) n hn
  have hc : (R.divisors.filter (fun f => f ≤ F)).card ≤ 2^A.card := by
    rw [← card_powerset]
    apply card_le_card_of_injOn Nat.primeFactors
    · intro f hf
      change f ∈ R.divisors.filter (fun f => f ≤ F) at hf
      obtain ⟨hfd,hfF⟩ := mem_filter.mp hf
      have hd := (Nat.mem_divisors.mp hfd).1
      have hf0 := Nat.pos_of_dvd_of_pos hd (roughRadical_pos B _)
      change f.primeFactors ∈ A.powerset
      apply mem_powerset.mpr
      intro p hp
      rw [hA]
      exact mem_filter.mpr ⟨Nat.primeFactors_mono hd (roughRadical_pos B _).ne' hp,
        (Nat.le_of_dvd hf0 (Nat.dvd_of_mem_primeFactors hp)).trans (hfF.trans hF)⟩
    · intro f hf g hg hfg
      have hfs := (roughRadical_squarefree B _).squarefree_of_dvd (Nat.mem_divisors.mp (mem_filter.mp hf).1).1
      have hgs := (roughRadical_squarefree B _).squarefree_of_dvd (Nat.mem_divisors.mp (mem_filter.mp hg).1).1
      rw [← Nat.prod_primeFactors_of_squarefree hfs,← Nat.prod_primeFactors_of_squarefree hgs,hfg]
  exact_mod_cast hc

lemma mixedComplementRectangleAt_abs_le (B D W F X k L N n : ℕ)
    (hB : 1 < B) (hW : 1 < W) (hWN : N+1 ≤ W^L)
    (hn : 0 < n) (hnN : n ≤ N) (hF : F ≤ B^k) :
    |mixedComplementRectangleAt B D W F X n| ≤
      (2 : ℝ)^(2*L)*(2 : ℝ)^(activeBlockPrimes (largePrimeSet B (B^k))
        (activePrimeAtoms (largePrimeSet B (B^k)) n)).card := by
  have hgcard : ((roughRadical W (n*(n+1))).divisors.card : ℝ) ≤ (2 : ℝ)^(2*L) := by
    exact_mod_cast (squarefree_divisors_card_le _ (roughRadical_squarefree W _)).trans
      (Nat.pow_le_pow_right (by norm_num) (highRadical_card_bound W L N n hW hWN hn hnN))
  have hfcard := short_divisor_count_le_exp B k F n hB hn hF
  unfold mixedComplementRectangleAt
  rw [abs_mul,roughRadical_moebius_abs,one_mul]
  calc
    _ ≤ ∑ f ∈ (roughRadical B (n*(n+1))).divisors, if f ≤ F then (2 : ℝ)^(2*L) else 0 := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro f _
      by_cases h : f ≤ F
      · rw [if_pos h]
        apply le_trans _ hgcard
        apply (abs_sum_le_sum_abs _ _).trans
        calc
          _ ≤ ∑ _g ∈ (roughRadical W (n*(n+1))).divisors, (1 : ℝ) := by
            apply sum_le_sum
            intro g _
            split_ifs
            · rw [abs_mul,divisorSideColour_abs,mul_one,← Int.cast_abs]
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := f*g)
            · norm_num
          _ = _ := by simp
      · simp [h]
    _ = (2 : ℝ)^(2*L)*(((roughRadical B (n*(n+1))).divisors.filter (fun f => f ≤ F)).card : ℝ) := by
      rw [← sum_filter,sum_const,nsmul_eq_mul,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfcard (by positivity)

#print axioms mixedComplementRectangleAt_factor
#print axioms mixedComplementRectangleAt_abs_le
end Erdos371
