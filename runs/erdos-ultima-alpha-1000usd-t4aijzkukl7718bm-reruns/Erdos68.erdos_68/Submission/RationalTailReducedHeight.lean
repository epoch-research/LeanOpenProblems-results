import Submission.ReducedBlockDenominatorBound
import Submission.Development

/-!
Reduced numerator growth for rational residuals of the original series.
This is auxiliary work, not a proof or disproof of Erdős problem 68.
-/

namespace RationalTailReducedHeight

open Finset ReducedBlockDenominatorBound Erdos68Development

noncomputable def residual (q : ℚ) (N : ℕ) : ℚ :=
  q - reciprocalPrefix N

/-- The common rational endpoint cancels before estimating denominators. -/
theorem nearby_residual_denominator_large (q : ℚ) (m : ℕ) (hm : 9 ≤ m) :
    m^(m^3) ≤ (residual q (8*m^2)).den ∨
      m^(m^3) ≤ (residual q (8*m^2+m)).den := by
  have hb := growing_block_reduced_height m hm
  have he : reciprocalBlock (8*m^2) m =
      residual q (8*m^2) - residual q (8*m^2+m) := by
    rw [block_eq_prefix_sub]
    dsimp [residual]
    ring
  have hd := Rat.sub_den_dvd (residual q (8*m^2)) (residual q (8*m^2+m))
  rw [← he] at hd
  have hl := hb.trans (Nat.le_of_dvd
    (Nat.mul_pos (residual q (8*m^2)).den_pos
      (residual q (8*m^2+m)).den_pos) hd)
  have hp : m^(2*m^3) = (m^(m^3))^2 := by
    rw [← pow_mul]
    congr 1
    ring
  rw [hp] at hl
  by_contra h
  push_neg at h
  nlinarith [Nat.mul_lt_mul_of_lt_of_le h.1 h.2.le
    (by positivity : 0 < m^(m^3))]

lemma prefix_cast (n : ℕ) :
    (reciprocalPrefix (n+2) : ℝ) = ∑ k ∈ range n, term k := by
  rw [show n+2 = 2+n by omega]
  simp only [reciprocalPrefix, sum_range_add]
  have hz : (∑ i ∈ range 2, 1 / (FactorialMinusOneLcmBound.denom i : ℚ)) = 0 := by
    norm_num [sum_range_succ, FactorialMinusOneLcmBound.denom]
  rw [hz, zero_add]
  push_cast
  apply sum_congr rfl
  intro i hi
  rw [term_eq_inv_denom]
  simp only [FactorialMinusOneLcmBound.denom, Erdos68Development.denom, Nat.add_comm]

lemma reciprocal_factorial_lt_residual (q : ℚ)
    (hq : (∑' n : ℕ, term n) ≤ (q : ℝ)) (N : ℕ) (hN : 2 ≤ N) :
    1 / (N.factorial : ℚ) < residual q N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n+2 := ⟨N-2, by omega⟩
  have hf : (0 : ℝ) < (n+2).factorial := by positivity
  have ht : 1 / ((n+2).factorial : ℝ) < term n := by
    unfold term
    exact one_div_lt_one_div_of_lt (denom_pos n) (by linarith)
  have he := term_le_tail n
  have hr : 1 / ((n+2).factorial : ℝ) < (residual q (n+2) : ℝ) := by
    simp only [residual, Rat.cast_sub, prefix_cast]
    linarith
  apply (Rat.cast_lt (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hr

lemma window_factorial_bound (m N : ℕ) (hm : 9 ≤ m) (hN : N ≤ 8*m^2+m) :
    N.factorial ≤ m^(27*m^2) := by
  have hself : m ≤ m^2 := Nat.le_self_pow (by omega) m
  have hN' : N ≤ 9*m^2 := by omega
  have hbase : N ≤ m^3 := by
    have hh := Nat.mul_le_mul_right (m^2) hm
    nlinarith
  calc
    N.factorial ≤ N^N := Nat.factorial_le_pow N
    _ ≤ (m^3)^N := Nat.pow_le_pow_left hbase N
    _ = m^(3*N) := by rw [pow_mul]
    _ ≤ m^(27*m^2) := Nat.pow_le_pow_right (by omega) (by omega)

lemma numerator_large_of_denominator_large (q : ℚ)
    (hq : (∑' n : ℕ, term n) ≤ (q : ℝ)) (m N : ℕ)
    (hm : 28 ≤ m) (hN : 2 ≤ N) (hN' : N ≤ 8*m^2+m)
    (hd : m^(m^3) ≤ (residual q N).den) :
    (m^(m^2) : ℤ) < (residual q N).num := by
  have ht := reciprocal_factorial_lt_residual q hq N hN
  have hnum : ((residual q N).den : ℚ) <
      ((residual q N).num : ℚ) * (N.factorial : ℚ) := by
    conv_rhs at ht => rw [← Rat.num_div_den (residual q N)]
    have h := (div_lt_div_iff₀
      (by positivity : (0 : ℚ) < N.factorial)
      (by positivity : (0 : ℚ) < (residual q N).den)).mp ht
    simpa using h
  have hnumZ : ((residual q N).den : ℤ) <
      (residual q N).num * (N.factorial : ℤ) := by exact_mod_cast hnum
  have hfac : (N.factorial : ℤ) ≤ (m^(27*m^2) : ℕ) := by
    exact_mod_cast window_factorial_bound m N (by omega) hN'
  have hexp : 28*m^2 ≤ m^3 := by
    have hh := Nat.mul_le_mul_right (m^2) hm
    nlinarith
  have hpow : m^(28*m^2) ≤ m^(m^3) :=
    Nat.pow_le_pow_right (by omega) hexp
  have hdZ : (m^(28*m^2) : ℤ) ≤ (residual q N).den := by
    exact_mod_cast hpow.trans hd
  by_contra h
  have hn : (residual q N).num ≤ (m^(m^2) : ℤ) := le_of_not_gt h
  have hmprod := mul_le_mul hn hfac
    (by positivity : (0 : ℤ) ≤ N.factorial)
    (by positivity : (0 : ℤ) ≤ m^(m^2))
  have he : (m^(m^2) : ℤ) * (m^(27*m^2) : ℕ) = (m^(28*m^2) : ℤ) := by
    push_cast
    rw [← pow_add]
    congr 1
    ring
  rw [he] at hmprod
  omega

/-- Even with fully reduced fractions, at least one nearby residual numerator
is large. In particular, small positive real tails do not give numerator descent. -/
theorem nearby_residual_numerator_large (q : ℚ)
    (hq : (∑' n : ℕ, term n) ≤ (q : ℝ)) (m : ℕ) (hm : 28 ≤ m) :
    (m^(m^2) : ℤ) < (residual q (8*m^2)).num ∨
      (m^(m^2) : ℤ) < (residual q (8*m^2+m)).num := by
  rcases nearby_residual_denominator_large q m (by omega) with h | h
  · exact Or.inl (numerator_large_of_denominator_large q hq m (8*m^2)
      hm (by nlinarith) (by omega) h)
  · exact Or.inr (numerator_large_of_denominator_large q hq m (8*m^2+m)
      hm (by nlinarith) (by omega) h)

/-- The reduced residual numerators exceed every fixed bound arbitrarily late. -/
theorem residual_numerators_unbounded (q : ℚ)
    (hq : (∑' n : ℕ, term n) ≤ (q : ℝ)) (B N : ℕ) :
    ∃ n ≥ N, (B : ℤ) < (residual q n).num := by
  let m := N+B+28
  have hm : 28 ≤ m := by dsimp [m]; omega
  have hNm : N ≤ m := by dsimp [m]; omega
  have hBm : B < m := by dsimp [m]; omega
  have hmsq : m ≤ m^2 := Nat.le_self_pow (by omega) m
  have hmpow : m ≤ m^(m^2) := Nat.le_self_pow (by positivity) m
  have hbig : (B : ℤ) < (m^(m^2) : ℤ) := by exact_mod_cast hBm.trans_le hmpow
  have h8 : m^2 ≤ 8*m^2 := by omega
  have hn0 : N ≤ 8*m^2 := hNm.trans (hmsq.trans h8)
  rcases nearby_residual_numerator_large q hq m hm with h | h
  · exact ⟨8*m^2, hn0, hbig.trans h⟩
  · exact ⟨8*m^2+m, hn0.trans (Nat.le_add_right _ _), hbig.trans h⟩

/-- No eventual upper bound on reduced numerators is compatible with a rational
endpoint at least as large as the original sum. -/
theorem no_eventual_numerator_bound (q : ℚ)
    (hq : (∑' n : ℕ, term n) ≤ (q : ℝ)) :
    ¬ ∃ N : ℕ, ∃ B : ℤ, ∀ n ≥ N, (residual q n).num ≤ B := by
  rintro ⟨N, B, hb⟩
  obtain ⟨n, hn, hnum⟩ := residual_numerators_unbounded q hq B.natAbs N
  have hB : B ≤ (B.natAbs : ℤ) := Int.le_natAbs
  exact (not_lt_of_ge ((hb n hn).trans hB)) hnum

/-- In particular, reduction cannot turn these exact tails into an eventually
nonincreasing numerator sequence. This is not an irrationality assertion. -/
theorem no_eventual_numerator_descent (q : ℚ)
    (hq : (∑' n : ℕ, term n) ≤ (q : ℝ)) :
    ¬ ∃ N : ℕ, AntitoneOn (fun n => (residual q n).num) (Set.Ici N) := by
  rintro ⟨N, hN⟩
  apply no_eventual_numerator_bound q hq
  refine ⟨N, (residual q N).num, ?_⟩
  intro n hn
  exact hN (by simp) hn hn

end RationalTailReducedHeight

#print axioms RationalTailReducedHeight.nearby_residual_denominator_large
#print axioms RationalTailReducedHeight.nearby_residual_numerator_large
#print axioms RationalTailReducedHeight.residual_numerators_unbounded
#print axioms RationalTailReducedHeight.no_eventual_numerator_descent
