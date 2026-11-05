import Submission.Carmichael
import Submission.FractionalSelection

/-!
# A weighted divisor with a prescribed Carmichael-function lower bound

Each full prime power in a finite lcm is assigned to one input attaining its
maximal exponent. The resulting blocks are pairwise coprime, their product is
the lcm, and the product of any subfamily divides that subfamily's lcm.

Applying finite fractional selection with costs `log p` and gains `log B_p`
then gives a divisor of a squarefree integer whose Carmichael function is at
least a prescribed target, with a proportional logarithmic size bound.
These are unconditional finite statements, not a density or counting claim.
-/

open scoped BigOperators

namespace Erdos1057.WeightedDivisor

variable {ι : Type*}

/-- The exponent of a prime in a finite lcm is the maximum of its exponents
in the inputs. All inputs must be nonzero. -/
theorem factorization_finset_lcm (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) (q : ℕ) :
    (s.lcm f).factorization q = s.sup (fun i => (f i).factorization q) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro hf
    simp
  | @insert i s hi ih =>
    intro hf
    have hi0 : f i ≠ 0 := hf i (Finset.mem_insert_self i s)
    have hs0 : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.lcm_insert, lcm_eq_nat_lcm,
      Nat.factorization_lcm hi0 (Finset.lcm_ne_zero_iff.mpr hs0),
      Finsupp.sup_apply, ih hs0, Finset.sup_insert]

/-- Every prime in a nonzero finite lcm has an input attaining its full
prime-power exponent. -/
theorem exists_factorization_eq_lcm (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) {q : ℕ} (hq : q ∈ (s.lcm f).primeFactors) :
    ∃ i ∈ s, (f i).factorization q = (s.lcm f).factorization q := by
  classical
  have hs : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hq
  obtain ⟨i, hi, he⟩ :=
    Finset.sup_mem_of_nonempty (f := fun i => (f i).factorization q) hs
  exact ⟨i, hi, he.trans (factorization_finset_lcm s f hf q).symm⟩

/-- Assign every *full* prime-power block of a finite lcm to a single input
attaining its exponent. The blocks belonging to each input have positive
product `B i`, divide that input, and are pairwise coprime between distinct
inputs. In particular every subset's block product divides its subset lcm.

The value `1` is allowed for inputs receiving no prime-power blocks. -/
theorem exists_coprime_lcm_assignment (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ B : ι → ℕ, (∀ i, 0 < B i) ∧
      (∀ i ∈ s, B i ∣ f i) ∧
      (s : Set ι).Pairwise (fun i j => (B i).Coprime (B j)) ∧
      (∏ i ∈ s, B i) = s.lcm f ∧
      ∀ t : Finset ι, t ⊆ s → (∏ i ∈ t, B i) ∣ t.lcm f := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · refine ⟨fun _ => 1, by simp, by simp, by simp, by simp, ?_⟩
    intro t ht
    have ht0 : t = ∅ := Finset.subset_empty.mp ht
    simp [ht0]
  · let L := s.lcm f
    have hL : L ≠ 0 := Finset.lcm_ne_zero_iff.mpr hf
    have howner : ∀ q : ℕ, ∃ i ∈ s, q ∈ L.primeFactors →
        (f i).factorization q = L.factorization q := by
      intro q
      by_cases hq : q ∈ L.primeFactors
      · obtain ⟨i, hi, he⟩ := exists_factorization_eq_lcm s f hf hq
        exact ⟨i, hi, fun _ => he⟩
      · obtain ⟨i, hi⟩ := hs
        exact ⟨i, hi, fun h => False.elim (hq h)⟩
    choose owner howners hownerExp using howner
    let Q : ι → Finset ℕ := fun i => L.primeFactors.filter (fun q => owner q = i)
    let B : ι → ℕ := fun i => ∏ q ∈ Q i, q ^ L.factorization q
    have hBpos : ∀ i, 0 < B i := by
      intro i
      exact Finset.prod_pos fun q hq =>
        Nat.pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos
    have hBdiv : ∀ i ∈ s, B i ∣ f i := by
      intro i hi
      have hQcop : (Q i : Set ℕ).Pairwise (fun q r =>
          (q ^ L.factorization q).Coprime (r ^ L.factorization r)) := by
        intro q hq r hr hqr
        exact Nat.coprime_pow_primes _ _
          (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)
          (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1) hqr
      change (∏ q ∈ Q i, q ^ L.factorization q) ∣ f i
      rw [← Finset.lcm_eq_prod hQcop]
      apply Finset.lcm_dvd
      intro q hq
      obtain ⟨hqL, hqi⟩ := Finset.mem_filter.mp hq
      apply (Nat.prime_of_mem_primeFactors hqL).pow_dvd_iff_le_factorization (hf i hi) |>.mpr
      have he := hownerExp q hqL
      rw [hqi] at he
      exact he.ge
    have hBcop : (s : Set ι).Pairwise (fun i j => (B i).Coprime (B j)) := by
      intro i hi j hj hij
      dsimp only [B]
      apply Nat.coprime_prod_left_iff.mpr
      intro q hq
      apply Nat.coprime_prod_right_iff.mpr
      intro r hr
      obtain ⟨hqL, hqi⟩ := Finset.mem_filter.mp hq
      obtain ⟨hrL, hrj⟩ := Finset.mem_filter.mp hr
      apply Nat.coprime_pow_primes _ _
        (Nat.prime_of_mem_primeFactors hqL) (Nat.prime_of_mem_primeFactors hrL)
      intro hqr
      exact hij (hqi.symm.trans ((congrArg owner hqr).trans hrj))
    refine ⟨B, hBpos, hBdiv, hBcop, ?_, ?_⟩
    · change (∏ i ∈ s, ∏ q ∈ L.primeFactors with owner q = i,
          q ^ L.factorization q) = L
      rw [Finset.prod_fiberwise_of_maps_to (fun q _ => howners q)]
      exact Nat.factorization_prod_pow_eq_self hL
    · intro t ht
      have htcop : (t : Set ι).Pairwise (fun i j => (B i).Coprime (B j)) := by
        intro i hi j hj hij
        exact hBcop (ht hi) (ht hj) hij
      rw [← Finset.lcm_eq_prod htcop]
      exact Finset.lcm_mono_fun fun i hi => hBdiv i (ht hi)

/-- Logarithmic weights add to the logarithm of their positive natural-number
product, including for the empty product. -/
theorem sum_log_nat_eq_log_prod (s : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    (∑ i ∈ s, Real.log (a i : ℝ)) = Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) := by
  rw [Nat.cast_prod]
  exact (Real.log_prod fun i hi =>
    (Nat.cast_pos.mpr (ha i hi) : 0 < (a i : ℝ)).ne').symm

/-- An unconditional weighted-divisor witness. If `n` is positive and
squarefree, `λ(n) > 1`, and all its prime factors are at most `y`, then every
real target `1 < u ≤ λ(n)` is attained by `λ(d)` for a divisor `d` whose size
is at most `y * n ^ (log u / log λ(n))`.

For each prime `p ∣ n` the cost is `log p`. Its gain is the logarithm of the
product of the full prime-power blocks of `λ(n)` assigned to `p - 1` by
`exists_coprime_lcm_assignment`; repeated occurrences of a prime in different
`p - 1` are never counted twice. -/
theorem exists_divisor {n : ℕ} {y u : ℝ}
    (hn : Squarefree n) (hn1 : 1 ≤ n)
    (hLambda : 1 < ArithmeticFunction.Carmichael n)
    (hy : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ y)
    (hu : 1 < u) (huLambda : u ≤ (ArithmeticFunction.Carmichael n : ℝ)) :
    ∃ d : ℕ, d ∣ n ∧ u ≤ (ArithmeticFunction.Carmichael d : ℝ) ∧
      (d : ℝ) ≤ y * (n : ℝ) ^
        (Real.log u / Real.log (ArithmeticFunction.Carmichael n : ℝ)) := by
  classical
  have hLambdaEq := CarmichaelKorselt.carmichael_eq_lcm_primeFactors_of_squarefree hn
  have hLambdaReal : 1 < (ArithmeticFunction.Carmichael n : ℝ) := by
    exact_mod_cast hLambda
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hup : 0 < u := zero_lt_one.trans hu
  have hs : n.primeFactors.Nonempty := by
    by_contra h
    have he : n.primeFactors = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hLambdaEq, he, Finset.lcm_empty] at hLambda
    exact (Nat.lt_irrefl 1) hLambda
  obtain ⟨p₀, hp₀⟩ := hs
  have hypos : 0 < y :=
    (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp₀).pos).trans_le
      (hy p₀ (Nat.prime_of_mem_primeFactors hp₀) (Nat.dvd_of_mem_primeFactors hp₀))
  have hf : ∀ p ∈ n.primeFactors, p - 1 ≠ 0 := fun p hp =>
    (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt).ne'
  obtain ⟨B, hBpos, _, _, hBprod, hBsubset⟩ :=
    exists_coprime_lcm_assignment n.primeFactors (fun p => p - 1) hf
  have hBprodLambda : (∏ p ∈ n.primeFactors, B p) = ArithmeticFunction.Carmichael n :=
    hBprod.trans hLambdaEq.symm
  have hcostNonneg : ∀ p ∈ n.primeFactors, 0 ≤ Real.log (p : ℝ) := by
    intro p hp
    apply Real.log_nonneg
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have hgainNonneg : ∀ p ∈ n.primeFactors, 0 ≤ Real.log (B p : ℝ) := by
    intro p hp
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (hBpos p).ne')
  have hC : (∑ p ∈ n.primeFactors, Real.log (p : ℝ)) = Real.log (n : ℝ) := by
    rw [sum_log_nat_eq_log_prod n.primeFactors (fun p => p)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos),
      Nat.prod_primeFactors_of_squarefree hn]
  have hG : (∑ p ∈ n.primeFactors, Real.log (B p : ℝ)) =
      Real.log (ArithmeticFunction.Carmichael n : ℝ) := by
    rw [sum_log_nat_eq_log_prod n.primeFactors B (fun p _ => hBpos p), hBprodLambda]
  have hcostMax : ∀ p ∈ n.primeFactors, Real.log (p : ℝ) ≤ Real.log y := by
    intro p hp
    exact Real.log_le_log (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos)
      (hy p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨T, hT, hgain, hcost⟩ := FractionalSelection.exists_subset_of_totals
    n.primeFactors (fun p => Real.log (p : ℝ)) (fun p => Real.log (B p : ℝ))
    (Real.log (n : ℝ)) (Real.log (ArithmeticFunction.Carmichael n : ℝ))
    (Real.log y) (Real.log u) hcostNonneg hgainNonneg hC hG
    (Real.log_pos hLambdaReal) hcostMax (Real.log_nonneg hu.le)
    (Real.log_le_log hup huLambda)
  let d : ℕ := ∏ p ∈ T, p
  have hdvd : d ∣ n := by
    have h := Finset.prod_dvd_prod_of_subset T n.primeFactors (fun p => p) hT
    simpa only [Nat.prod_primeFactors_of_squarefree hn] using h
  have hdpos : 0 < d := Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (hT hp)).pos
  have hdsq : Squarefree d := hn.squarefree_of_dvd hdvd
  have hdprimes : d.primeFactors = T :=
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hT hp))
  have hdLambdaEq : ArithmeticFunction.Carmichael d = T.lcm (fun p => p - 1) := by
    rw [CarmichaelKorselt.carmichael_eq_lcm_primeFactors_of_squarefree hdsq, hdprimes]
  have hdLambdaPos : 0 < ArithmeticFunction.Carmichael d := by
    rw [hdLambdaEq]
    exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr fun p hp => hf p (hT hp))
  have hBTdvd : (∏ p ∈ T, B p) ∣ ArithmeticFunction.Carmichael d := by
    rw [hdLambdaEq]
    exact hBsubset T hT
  have hBTpos : 0 < ∏ p ∈ T, B p := Finset.prod_pos fun p _ => hBpos p
  have huBT : u ≤ ((∏ p ∈ T, B p : ℕ) : ℝ) := by
    apply (Real.log_le_log_iff hup (Nat.cast_pos.mpr hBTpos)).mp
    rw [← sum_log_nat_eq_log_prod T B (fun p _ => hBpos p)]
    exact hgain
  refine ⟨d, hdvd, ?_, ?_⟩
  · exact huBT.trans (Nat.cast_le.mpr (Nat.le_of_dvd hdLambdaPos hBTdvd))
  · rw [sum_log_nat_eq_log_prod T (fun p => p)
      (fun p hp => (Nat.prime_of_mem_primeFactors (hT hp)).pos)] at hcost
    apply (Real.log_le_log_iff (Nat.cast_pos.mpr hdpos)
      (mul_pos hypos (Real.rpow_pos_of_pos hnpos _))).mp
    rw [Real.log_mul hypos.ne' (Real.rpow_pos_of_pos hnpos _).ne', Real.log_rpow hnpos]
    exact hcost.trans_eq (add_comm _ _)

end Erdos1057.WeightedDivisor
