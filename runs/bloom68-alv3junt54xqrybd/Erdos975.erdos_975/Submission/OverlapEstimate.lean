import Submission.PolynomialSetup

/-!
# A negligible overlap correction for polynomial values of degree at least three

The divisor count satisfies `sigma0 m ≤ Cε * m ^ ε` for every `ε > 0`.
We prove this from the prime-factor product formula: large primes need no
constant, and only finitely many small primes contribute a bounded factor.

Eventual cubic growth restricts the inputs contributing to the overlap to
`O(N ^ (2 / 3))` inputs. Taking `ε = 1 / 12`, each contributing value has
at most `O(N ^ (1 / 6))` divisors, giving an `O(N ^ (5 / 6))` overlap bound.
In particular the overlap is negligible after normalization by `N * log N`.

These are supporting estimates only, not a proof of the divisor-average
conjecture. No irreducibility or sign hypothesis is needed for this error term.
-/

namespace Erdos975Support

open Filter Polynomial Asymptotics
open scoped Topology

/-- A geometric sequence of ratio greater than one eventually dominates `k + 1`,
with a single constant valid at every natural input. -/
lemma linear_le_const_geometric {r : ℝ} (hr : 1 < r) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ B * r ^ k := by
  have ht : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1) / r ^ k) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, ← add_div, zero_add] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 hr).add
        (tendsto_pow_const_div_const_pow_of_one_lt 0 hr)
  obtain ⟨B, hB⟩ := ht.bddAbove_range
  refine ⟨max B 1, le_max_right _ _, fun k ↦ ?_⟩
  apply (div_le_iff₀ (pow_pos (zero_lt_one.trans hr) k)).mp
  exact (hB (Set.mem_range_self k)).trans (le_max_left _ _)

/-- The elementary divisor bound, uniform in the natural argument, including zero.
The exponent can be any positive real number. -/
theorem sigma0_le_const_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ,
      (ArithmeticFunction.sigma0 m : ℝ) ≤ A * (m : ℝ) ^ ε := by
  classical
  obtain ⟨B, hB, hgeom⟩ := linear_le_const_geometric
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hpowers : ∀ᶠ p : ℕ in atTop, (2 : ℝ) ≤ (p : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  obtain ⟨P, hP⟩ := eventually_atTop.mp hpowers
  let w : ℕ → ℝ := fun p ↦ if p < P then B else 1
  have hlocal (p k : ℕ) (hp : p.Prime) :
      (k : ℝ) + 1 ≤ w p * ((p : ℝ) ^ k) ^ ε := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    by_cases hpP : p < P
    · simp only [w, if_pos hpP]
      calc
        (k : ℝ) + 1 ≤ B * ((2 : ℝ) ^ ε) ^ k := hgeom k
        _ ≤ B * ((p : ℝ) ^ ε) ^ k := by
          apply mul_le_mul_of_nonneg_left _ hBpos.le
          exact pow_le_pow_left₀ (by positivity)
            (Real.rpow_le_rpow (by norm_num) hp2 hε.le) k
        _ = B * ((p : ℝ) ^ k) ^ ε := by
          rw [Real.rpow_pow_comm (Nat.cast_nonneg p)]
    · simp only [w, if_neg hpP, one_mul]
      calc
        (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
          exact_mod_cast (Nat.succ_le_iff.mpr (show k < 2 ^ k from Nat.lt_two_pow_self))
        _ ≤ ((p : ℝ) ^ ε) ^ k :=
          pow_le_pow_left₀ (by norm_num) (hP p (Nat.le_of_not_gt hpP)) k
        _ = ((p : ℝ) ^ k) ^ ε := Real.rpow_pow_comm (Nat.cast_nonneg p) ε k
  refine ⟨B ^ P, pow_pos hBpos _, fun m ↦ ?_⟩
  by_cases hm : m = 0
  · simp [hm, ArithmeticFunction.sigma0, Real.zero_rpow hε.ne']
  have hsmall : (∏ p ∈ m.primeFactors, w p) ≤ B ^ P := by
    have hcard : (m.primeFactors.filter (fun p ↦ p < P)).card ≤ P := by
      calc
        _ ≤ (Finset.range P).card := Finset.card_le_card (by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
        _ = P := Finset.card_range P
    change (∏ p ∈ m.primeFactors, if p < P then B else 1) ≤ _
    rw [← Finset.prod_filter (fun p : ℕ ↦ p < P) (fun _ ↦ B), Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hfactor : (∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ ε) =
      (m : ℝ) ^ ε := by
    rw [Real.finset_prod_rpow _ _ (fun p _ ↦ by positivity)]
    congr 1
    have hn : (∏ p ∈ m.primeFactors, p ^ m.factorization p) = m := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors,
        Nat.factorization_prod_pow_eq_self hm]
    exact_mod_cast hn
  calc
    (ArithmeticFunction.sigma0 m : ℝ) =
        ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
      rw [ArithmeticFunction.sigma0, ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm]
      push_cast
      rfl
    _ ≤ ∏ p ∈ m.primeFactors, w p * ((p : ℝ) ^ m.factorization p) ^ ε := by
      apply Finset.prod_le_prod (fun p _ ↦ by positivity)
      intro p hp
      exact hlocal p _ (Nat.prime_of_mem_primeFactors hp)
    _ = (∏ p ∈ m.primeFactors, w p) * (m : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hfactor]
    _ ≤ B ^ P * (m : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)

/-- Casting the natural absolute value to the reals agrees with absolute value
of the corresponding real polynomial evaluation. -/
lemma polynomialAbsValue_cast_real (f : ℤ[X]) (n : ℕ) :
    (polynomialAbsValue f n : ℝ) =
      |(f.map (Int.castRingHom ℝ)).eval (n : ℝ)| := by
  rw [polynomialAbsValue, Nat.cast_natAbs, Int.cast_abs, Polynomial.eval_map]
  congr 1
  simp

/-- Every integer polynomial of degree at least three has eventual cubic
absolute growth, irrespective of the sign of its leading coefficient. -/
theorem polynomialAbsValue_eventual_cubic_growth (f : ℤ[X])
    (hdeg : 3 ≤ f.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 3 ≤ C * (polynomialAbsValue f n : ℝ) := by
  let P : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hdegP : 3 ≤ P.natDegree := by
    dsimp [P]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact hdeg
  have hf : f ≠ 0 := by
    intro hf
    simp [hf] at hdeg
  have hlc : (1 : ℝ) ≤ |P.leadingCoeff| := by
    dsimp [P]
    rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    have hn : 1 ≤ f.leadingCoeff.natAbs := by
      have := Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf)
      omega
    have hh : (1 : ℝ) ≤ (f.leadingCoeff.natAbs : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  obtain ⟨C, hC, hbound⟩ := P.isEquivalent_atTop_lead.isBigO_symm.exists_pos
  have hgrowth : ∀ᶠ x : ℝ in atTop, x ^ 3 ≤ C * |P.eval x| := by
    filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0] at hx
    calc
      x ^ 3 ≤ x ^ P.natDegree := pow_le_pow_right₀ hx1 hdegP
      _ ≤ |P.leadingCoeff| * x ^ P.natDegree := by
        nlinarith [pow_nonneg hx0 P.natDegree]
      _ ≤ C * |P.eval x| := hx
  refine ⟨C, hC, ?_⟩
  have hn := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually hgrowth
  simpa only [polynomialAbsValue_cast_real, P] using hn

/-- A cubic lower bound permits only `O(N ^ (2 / 3))` inputs with value at most
`N * N`. The constant initial segment is included explicitly. -/
lemma cubic_sublevel_card_le {g : ℕ → ℕ} {C : ℝ} {M : ℕ}
    (hC : 0 < C)
    (hg : ∀ n : ℕ, M ≤ n → (n : ℝ) ^ 3 ≤ C * (g n : ℝ)) (N : ℕ) :
    (((Finset.Iic N).filter (fun n ↦ g n ≤ N * N)).card : ℝ) ≤
      (M : ℝ) + 1 + C ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
  classical
  let R : ℝ := (M : ℝ) + C ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hs : (Finset.Iic N).filter (fun n ↦ g n ≤ N * N) ⊆
      Finset.Iic (Nat.floor R) := by
    intro n hn
    apply Finset.mem_Iic.mpr
    apply Nat.le_floor
    obtain ⟨_, hnval⟩ := Finset.mem_filter.mp hn
    by_cases hMn : M ≤ n
    · have hval : (g n : ℝ) ≤ (N : ℝ) ^ 2 := by
        exact_mod_cast (show g n ≤ N ^ 2 by simpa only [pow_two] using hnval)
      have hcubic : (n : ℝ) ^ 3 ≤ C * (N : ℝ) ^ 2 :=
        (hg n hMn).trans (mul_le_mul_of_nonneg_left hval hC.le)
      have hnroot : (n : ℝ) ≤ C ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
        calc
          (n : ℝ) = ((n : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n)]
            norm_num
          _ ≤ (C * (N : ℝ) ^ 2) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hcubic (by norm_num)
          _ = C ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
            rw [Real.mul_rpow hC.le (by positivity),
              ← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
            norm_num
      dsimp [R]
      linarith [Nat.cast_nonneg (α := ℝ) M]
    · have hnM : (n : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hMn))
      dsimp [R]
      have : 0 ≤ C ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by positivity
      linarith
  calc
    (((Finset.Iic N).filter (fun n ↦ g n ≤ N * N)).card : ℝ) ≤
        ((Finset.Iic (Nat.floor R)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hs
    _ = (Nat.floor R : ℝ) + 1 := by simp
    _ ≤ (M : ℝ) + 1 + C ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
      have hh := Nat.floor_le hR
      dsimp [R] at hh
      linarith

lemma overlapAlong_nonneg (g : ℕ → ℕ) (N : ℕ) : 0 ≤ overlapAlong g N :=
  Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- Eventual cubic growth alone gives a sublinear power bound for the overlap.
Zero values and the finite initial segment require no additional hypothesis. -/
theorem overlapAlong_le_const_rpow_of_cubic_growth {g : ℕ → ℕ} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 3 ≤ C * (g n : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N →
      overlapAlong g N ≤ A * (N : ℝ) ^ (5 / 6 : ℝ) := by
  classical
  obtain ⟨M, hM⟩ := eventually_atTop.mp hg
  obtain ⟨D, hD, hdiv⟩ := sigma0_le_const_rpow (1 / 12) (by norm_num)
  refine ⟨((M : ℝ) + 1 + C ^ (1 / 3 : ℝ)) * D, by positivity, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans_le hN1
  let s := (Finset.Iic N).filter (fun n ↦ g n ≤ N * N)
  have hsum : overlapAlong g N = ∑ n ∈ s, (overlapDivisorCount (g n) N : ℝ) := by
    unfold overlapAlong
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hns
    have hnval : N * N < g n := by
      have : ¬g n ≤ N * N := by simpa only [s, Finset.mem_filter, hn, true_and] using hns
      omega
    rw [overlapDivisorCount_eq_zero hnval, Nat.cast_zero]
  have hpoint : ∀ n ∈ s, (overlapDivisorCount (g n) N : ℝ) ≤
      D * (N : ℝ) ^ (1 / 6 : ℝ) := by
    intro n hn
    have hval : (g n : ℝ) ≤ (N : ℝ) ^ 2 := by
      exact_mod_cast (show g n ≤ N ^ 2 by
        simpa only [pow_two] using (Finset.mem_filter.mp hn).2)
    calc
      (overlapDivisorCount (g n) N : ℝ) ≤ (ArithmeticFunction.sigma0 (g n) : ℝ) := by
        exact_mod_cast overlapDivisorCount_le_sigma (g n) N
      _ ≤ D * (g n : ℝ) ^ (1 / 12 : ℝ) := hdiv (g n)
      _ ≤ D * ((N : ℝ) ^ 2) ^ (1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hval (by norm_num)) hD.le
      _ = D * (N : ℝ) ^ (1 / 6 : ℝ) := by
        rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
        norm_num
  have hcard : (s.card : ℝ) ≤
      ((M : ℝ) + 1 + C ^ (1 / 3 : ℝ)) * (N : ℝ) ^ (2 / 3 : ℝ) := by
    have hh := cubic_sublevel_card_le hC hM N
    have hone : 1 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have hMpos : 0 ≤ (M : ℝ) + 1 := by positivity
    change (s.card : ℝ) ≤ _ at hh
    nlinarith
  calc
    overlapAlong g N = ∑ n ∈ s, (overlapDivisorCount (g n) N : ℝ) := hsum
    _ ≤ (s.card : ℝ) * (D * (N : ℝ) ^ (1 / 6 : ℝ)) := by
      simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul s _ _ hpoint
    _ ≤ (((M : ℝ) + 1 + C ^ (1 / 3 : ℝ)) * (N : ℝ) ^ (2 / 3 : ℝ)) *
        (D * (N : ℝ) ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (((M : ℝ) + 1 + C ^ (1 / 3 : ℝ)) * D) * (N : ℝ) ^ (5 / 6 : ℝ) := by
      rw [show (5 / 6 : ℝ) = (2 / 3 : ℝ) + (1 / 6 : ℝ) by norm_num,
        Real.rpow_add hNpos]
      ring

/-- Under eventual cubic growth the overlap is already negligible compared to
`N`, a stronger conclusion than the logarithmically normalized limit. -/
theorem tendsto_overlapAlong_div_nat_of_cubic_growth {g : ℕ → ℕ} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 3 ≤ C * (g n : ℝ)) :
    Tendsto (fun N : ℕ ↦ overlapAlong g N / (N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨A, _hApos, hA⟩ := overlapAlong_le_const_rpow_of_cubic_growth hC hg
  have ht : Tendsto (fun N : ℕ ↦ A * (N : ℝ) ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
        tendsto_natCast_atTop_atTop).const_mul A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Filter.Eventually.of_forall fun N ↦
      div_nonneg (overlapAlong_nonneg g N) (Nat.cast_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    calc
      overlapAlong g N / (N : ℝ) ≤ A * (N : ℝ) ^ (5 / 6 : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hA N hN) hNpos.le
      _ = A * (N : ℝ) ^ (-(1 / 6 : ℝ)) := by
        rw [mul_div_assoc,
          show (-(1 / 6 : ℝ)) = (5 / 6 : ℝ) - 1 by norm_num,
          Real.rpow_sub hNpos, Real.rpow_one]

/-- The logarithmically normalized overlap vanishes under eventual cubic growth. -/
theorem tendsto_overlapAlong_div_mul_log_of_cubic_growth {g : ℕ → ℕ} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 3 ≤ C * (g n : ℝ)) :
    Tendsto (fun N : ℕ ↦ overlapAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  simpa only [div_div] using
    (tendsto_overlapAlong_div_nat_of_cubic_growth hC hg).div_atTop tendsto_log_nat_atTop

/-- A uniform sublinear power bound for the polynomial overlap correction. -/
theorem polynomial_overlapAlong_le_const_rpow (f : ℤ[X]) (hdeg : 3 ≤ f.natDegree) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N →
      overlapAlong (polynomialAbsValue f) N ≤ A * (N : ℝ) ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC, hg⟩ := polynomialAbsValue_eventual_cubic_growth f hdeg
  exact overlapAlong_le_const_rpow_of_cubic_growth hC hg

/-- The overlap correction along a polynomial of degree at least three is `o(N)`.
The claim holds even for reducible polynomials and polynomials with integer roots. -/
theorem tendsto_polynomial_overlapAlong_div_nat (f : ℤ[X]) (hdeg : 3 ≤ f.natDegree) :
    Tendsto (fun N : ℕ ↦ overlapAlong (polynomialAbsValue f) N / (N : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hg⟩ := polynomialAbsValue_eventual_cubic_growth f hdeg
  exact tendsto_overlapAlong_div_nat_of_cubic_growth hC hg

/-- The polynomial overlap error vanishes after the normalization in Erdős 975.
Neither irreducibility nor eventual positivity is necessary for this estimate. -/
theorem tendsto_polynomial_overlapAlong_div_mul_log (f : ℤ[X])
    (hdeg : 3 ≤ f.natDegree) :
    Tendsto (fun N : ℕ ↦ overlapAlong (polynomialAbsValue f) N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hg⟩ := polynomialAbsValue_eventual_cubic_growth f hdeg
  exact tendsto_overlapAlong_div_mul_log_of_cubic_growth hC hg

end Erdos975Support
