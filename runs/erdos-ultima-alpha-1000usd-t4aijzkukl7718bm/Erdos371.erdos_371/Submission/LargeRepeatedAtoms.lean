import Submission.PrimeAllocationRetention

/-! Repeated prime-power atoms exceeding any fixed positive power of the
averaging endpoint occur with density zero. -/
namespace Erdos371
open Finset Filter RandomBins
open scoped Topology

/-- A repeated whole prime-power atom above a real threshold. -/
def largeRepeatedAtom (X : ℝ) (n : ℕ) : Prop :=
  ∃ p ∈ n.primeFactors, 2 ≤ n.factorization p ∧ X < (p^n.factorization p : ℕ)

lemma largeRepeatedAtom_large_square (B n : ℕ) (X : ℝ) (hB : (B : ℝ)^3 ≤ X)
    (h : largeRepeatedAtom X n) : ∃ d, B < d ∧ d^2 ∣ n := by
  obtain ⟨p,hpn,he,hbig⟩ := h
  obtain ⟨hp,hpd,hn⟩ := Nat.mem_primeFactors.mp hpn
  let d := p^(n.factorization p/2)
  have hd : d^2 ∣ n := by
    dsimp only [d]
    rw [← pow_mul]
    exact (hp.pow_dvd_iff_le_factorization hn).mpr (Nat.div_mul_le_self _ _)
  have hcube : p^n.factorization p ≤ d^3 := by
    dsimp only [d]
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  refine ⟨d,?_,hd⟩
  by_contra hBd
  have hle : p^n.factorization p ≤ B^3 :=
    hcube.trans (Nat.pow_le_pow_left (by omega : d ≤ B) 3)
  have hle' : (p^n.factorization p : ℕ) ≤ (B : ℝ)^3 := by exact_mod_cast hle
  exact (hle'.trans hB).not_gt hbig

noncomputable def largeRepeatedAtomSet (N : ℕ) (η : ℝ) : Finset ℕ := by
  classical
  exact (range N).filter fun n => largeRepeatedAtom ((N : ℝ)^η) (n+1)

lemma largeRepeatedAtomSet_card_le (B N : ℕ) (η : ℝ) (hB : (B : ℝ)^3 ≤ (N : ℝ)^η) :
    (largeRepeatedAtomSet N η).card ≤ largeSquareDivisorCount B N := by
  classical
  apply card_le_card
  intro n hn
  obtain ⟨hn,hbad⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hn,largeRepeatedAtom_large_square B (n+1) _ hB hbad⟩

/-- No uniform bound on exponents is assumed: large powers of small primes
are handled by the same square-divisor tail. -/
theorem largeRepeatedAtomSet_ratio_tendsto_zero (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => ((largeRepeatedAtomSet N η).card : ℝ)/N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by positivity)
  · intro ε hε
    have hf : Summable (fun d : ℕ => (1 : ℝ)/(d : ℝ)^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have ht := (hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub
      (∑' d : ℕ, (1 : ℝ)/(d : ℝ)^2)
    simp only [sub_self] at ht
    obtain ⟨B,hB⟩ := (ht.eventually_lt_const hε).exists
    have hp := (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
    filter_upwards [hp.eventually_ge_atTop ((B : ℝ)^3),eventually_gt_atTop (0 : ℕ)]
      with N hBN hN
    have hc := div_le_div_of_nonneg_right
      ((Nat.cast_le (α := ℝ)).mpr (largeRepeatedAtomSet_card_le B N η hBN)) (Nat.cast_nonneg N)
    exact (hc.trans (largeSquareDivisorCount_ratio_bound B N hN)).trans_lt hB

/-- Without a large repeated atom, each atom is either small or a prime. -/
lemma primePowerAtom_small_or_prime (n : ℕ) (X : ℝ) (h : ¬largeRepeatedAtom X n)
    (i : PrimeAtomIndex n) : (primePowerAtom n i : ℝ) ≤ X ∨ primePowerAtom n i = i.val := by
  by_cases he : 2 ≤ n.factorization i.val
  · apply Or.inl
    by_contra hx
    exact h ⟨i.val,i.property,he,lt_of_not_ge hx⟩
  · right
    have hexp : n.factorization i.val = 1 := by have := primeAtom_exponent_pos n i; omega
    simp only [primePowerAtom,hexp,pow_one]

/-- Any divisor's atoms inherit the bound on the repeated atoms in its parent. -/
lemma divisor_atom_small_or_prime (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (hdn : d ∣ n)
    (X : ℝ) (h : ¬largeRepeatedAtom X n) (i : PrimeAtomIndex d) :
    (primePowerAtom d i : ℝ) ≤ X ∨ primePowerAtom d i = i.val := by
  by_cases he : 2 ≤ d.factorization i.val
  · left
    have himem : i.val ∈ n.primeFactors := Nat.primeFactors_mono hdn hn.ne' i.property
    have he' : d.factorization i.val ≤ n.factorization i.val :=
      (Nat.factorization_le_iff_dvd hd.ne' hn.ne').mpr hdn i.val
    have hparent : (i.val^n.factorization i.val : ℕ) ≤ X := by
      by_contra hx
      exact h ⟨i.val,himem,he.trans he',lt_of_not_ge hx⟩
    have hpow : primePowerAtom d i ≤ i.val^n.factorization i.val :=
      Nat.pow_le_pow_right (primeAtom_prime d i).pos he'
    exact (show (primePowerAtom d i : ℝ) ≤ (i.val^n.factorization i.val : ℕ) by
      exact_mod_cast hpow).trans hparent
  · right
    have hexp : d.factorization i.val = 1 := by have := primeAtom_exponent_pos d i; omega
    simp only [primePowerAtom,hexp,pow_one]

#print axioms largeRepeatedAtomSet_ratio_tendsto_zero
#print axioms divisor_atom_small_or_prime
end Erdos371
