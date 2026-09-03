import Submission.UncoveredComplementCriterion

/-! Canonical low/high factorization of each squarefree complementary
index. The uncovered support is exactly a long W-smooth cofactor. -/
namespace Erdos371
open Finset FiniteSieve

lemma roughRadical_dvd_of_dvd (W a m : ℕ) (hm : m ≠ 0) (ham : a ∣ m) :
    roughRadical W a ∣ roughRadical W m := by
  apply prod_dvd_prod_of_subset
  intro p hp
  obtain ⟨hpa,hpW⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨Nat.primeFactors_mono ham hm hpa,hpW⟩

lemma roughRadical_small_high_product (W m f g : ℕ) (hf : 0 < f) (hfW : f ≤ W)
    (hg : g ∣ roughRadical W m) : roughRadical W (f*g)=g := by
  have hg0 := Nat.pos_of_dvd_of_pos hg (roughRadical_pos W m)
  have hgs := (roughRadical_squarefree W m).squarefree_of_dvd hg
  have hset : (roughRadical W (f*g)).primeFactors=g.primeFactors := by
    rw [roughRadical_primeFactors]
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨hp,hpW⟩
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hd := Nat.dvd_of_mem_primeFactors hp
      have hpg : p ∣ g := by
        rcases hpp.dvd_mul.mp hd with hpf | hpg
        · have hh := (Nat.le_of_dvd hf hpf).trans hfW
          omega
        · exact hpg
      exact Nat.mem_primeFactors.mpr ⟨hpp,hpg,hg0.ne'⟩
    · intro hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      refine ⟨Nat.mem_primeFactors.mpr ⟨hpp,hpd.trans (dvd_mul_left _ _),by positivity⟩,?_⟩
      exact roughRadical_prime_large W m p hpp (hpd.trans hg)
  rw [← Nat.prod_primeFactors_of_squarefree (roughRadical_squarefree W (f*g)),hset,
    Nat.prod_primeFactors_of_squarefree hgs]

lemma mixedComplementSupport_iff_canonical (B W F X n e : ℕ) (hF : F ≤ W)
    (he : e ∣ roughRadical B (n*(n+1))) :
    e ∈ mixedComplementSupport B W F X n ↔
      e/roughRadical W e ≤ F ∧ 1 < roughRadical W e ∧ roughRadical W e ≤ X := by
  have hepos := Nat.pos_of_dvd_of_pos he (roughRadical_pos B _)
  constructor
  · intro hm
    obtain ⟨fg,hfg,heq⟩ := mem_image.mp hm
    obtain ⟨hf,hg⟩ := mem_product.mp hfg
    obtain ⟨hfd,hfF⟩ := mem_filter.mp hf
    obtain ⟨hgd,hg1,hgX⟩ := mem_filter.mp hg
    have hfpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hfd).1 (roughRadical_pos B _)
    have hR : roughRadical W e=fg.2 := by
      rw [← heq]
      exact roughRadical_small_high_product W _ _ _ hfpos (hfF.trans hF) (Nat.mem_divisors.mp hgd).1
    rw [hR,← heq,Nat.mul_div_cancel _ (by omega : 0 < fg.2)]
    exact ⟨hfF,hg1,hgX⟩
  · rintro ⟨hF',hg1,hgX⟩
    let g := roughRadical W e
    let f := e/g
    have hge : g ∣ e := roughRadical_dvd W e
    have hfm : f ∣ roughRadical B (n*(n+1)) := (Nat.div_dvd_of_dvd hge).trans he
    have hgm : g ∣ roughRadical W (n*(n+1)) := by
      by_cases hn : n=0
      · subst n
        have he1 : e=1 := by simpa [roughRadical] using he
        subst e
        simp [g,roughRadical]
      · exact roughRadical_dvd_of_dvd W e _ (by positivity) (he.trans (roughRadical_dvd B _))
    apply mem_image.mpr
    refine ⟨(f,g),?_,Nat.div_mul_cancel hge⟩
    apply mem_product.mpr
    exact ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hfm,(roughRadical_pos B _).ne'⟩,hF'⟩,
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hgm,(roughRadical_pos W _).ne'⟩,hg1,hgX⟩⟩

lemma not_mixedComplementSupport_iff_long_low (B W U N n e : ℕ) (hUW : U ≤ W)
    (he : e ∣ roughRadical B (n*(n+1))) (hU : U < e) (heN : e ≤ N) :
    e ∉ mixedComplementSupport B W U N n ↔ U < e/roughRadical W e := by
  have hepos := Nat.pos_of_dvd_of_pos he (roughRadical_pos B _)
  have hRpos := roughRadical_pos W e
  have hRN : roughRadical W e ≤ N :=
    (Nat.le_of_dvd hepos (roughRadical_dvd W e)).trans heN
  rw [mixedComplementSupport_iff_canonical B W U N n e hUW he]
  by_cases hR1 : roughRadical W e=1
  · simp only [hR1,Nat.div_one,lt_self_iff_false,and_false,false_and,not_false_eq_true,true_iff]
    exact hU
  · have hRgt : 1 < roughRadical W e := by omega
    simp only [hRgt,hRN,and_self,and_true,not_le]

lemma complement_index_le_sample (B H N n e : ℕ) (hH : 1 ≤ H) (hN : 0 < N)
    (hn : 0 < n) (hnN : n ≤ N) (hsize : (H*N)*e < roughRadical B (n*(n+1))) : e ≤ N := by
  have hR : roughRadical B (n*(n+1)) ≤ N*(N+1) :=
    (Nat.le_of_dvd (by positivity) (roughRadical_dvd B _)).trans
      (Nat.mul_le_mul hnN (Nat.add_le_add_right hnN 1))
  have hHN : N ≤ H*N := by nlinarith
  have hmul := Nat.mul_le_mul_right e hHN
  nlinarith

noncomputable def longLowComplementAt (B D U Y W n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (roughRadical B (n*(n+1))) : ℝ)*
    ∑ e ∈ (roughRadical B (n*(n+1))).divisors,
      if U < e/roughRadical W e ∧ Y < Nat.maxPrimeFac e ∧ D*e < roughRadical B (n*(n+1)) then
        (ArithmeticFunction.moebius e : ℝ)*divisorSideColour n (roughRadical B (n*(n+1))/e) else 0

lemma uncoveredComplementAt_eq_longLow (B H U Y W N n : ℕ)
    (hH : 1 ≤ H) (hN : 0 < N) (hn : 0 < n) (hnN : n ≤ N) (hUW : U ≤ W) :
    uncoveredComplementAt B (H*N) U Y W N n=longLowComplementAt B (H*N) U Y W n := by
  unfold uncoveredComplementAt longLowComplementAt
  congr 1
  apply sum_congr rfl
  intro e he
  by_cases hd : (H*N)*e < roughRadical B (n*(n+1))
  · have heN := complement_index_le_sample B H N n e hH hN hn hnN hd
    by_cases hU : U < e
    · have hm := not_mixedComplementSupport_iff_long_low B W U N n e hUW (Nat.mem_divisors.mp he).1 hU heN
      simp only [hU,true_and,hd,and_true,hm]
      by_cases hY : Y < Nat.maxPrimeFac e <;>
        by_cases hlow : U < e/roughRadical W e <;> simp [hY,hlow]
    · have hl : ¬U < e/roughRadical W e := fun hh => hU (hh.trans_le (Nat.div_le_self e _))
      simp [hU,hl]
  · simp [hd]

#print axioms mixedComplementSupport_iff_canonical
#print axioms not_mixedComplementSupport_iff_long_low
end Erdos371
