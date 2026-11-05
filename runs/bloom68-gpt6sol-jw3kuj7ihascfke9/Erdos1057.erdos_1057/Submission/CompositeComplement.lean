import Submission.PrimeComplement

/-!
# A first bound for composite complementary blocks

The prime-complement argument has a two-prime analogue: if `n = a * p * q`
is Carmichael, then `q - 1 ∣ a * p - 1`.  This bounds the subfamily with a
semiprime complementary block by a sum of divisor counts.  It does not cover
complementary blocks with an unbounded number of prime factors.
-/

namespace Erdos1057

private theorem prime_le_lambda_plus_one {n H p : ℕ} (hn : 0 < n)
    (hnH : ArithmeticFunction.Carmichael n ≤ H)
    (hp : p.Prime) (hpn : p ∣ n) : p ≤ H + 1 := by
  have hLpos : 0 < ArithmeticFunction.Carmichael n :=
    Nat.pos_of_dvd_of_pos (ArithmeticFunction.carmichael_dvd_totient n)
      (Nat.totient_pos.mpr hn)
  have hpdvd : p - 1 ∣ ArithmeticFunction.Carmichael n := by
    rw [← carmichael_at_prime hp]
    exact ArithmeticFunction.carmichael_dvd hpn
  have hpH : p - 1 ≤ H :=
    (Nat.le_of_dvd hLpos hpdvd).trans hnH
  omega

/-- A prime complementary factor is at most `H + 1`, so this subfamily
cannot contain any `n > B * (H + 1)`. -/
theorem primeComplementCarmichaels_le_block_times_cutoff (X H B : ℕ) :
    primeComplementCarmichaels X H B ⊆ {n : ℕ | n ≤ B * (H + 1)} := by
  intro n hn
  obtain ⟨⟨hnC, _, hnH⟩, a, p, hp, hnfac, _, haB⟩ := hn
  have hnpos : 0 < n := by
    have h := (hnC 1 (by omega) (by simp)).2.2
    omega
  have hpn : p ∣ n := by
    rw [hnfac, Nat.mul_comm a p]
    exact dvd_mul_right p a
  have hpH := prime_le_lambda_plus_one hnpos hnH hp hpn
  change n ≤ B * (H + 1)
  calc
    n = a * p := hnfac
    _ ≤ B * (H + 1) := Nat.mul_le_mul haB hpH

/-- Carmichael numbers with a factorization `n = a * p * q` for which `p * q`
is a complementary block no larger than `a`, with `a ≤ B`. -/
def twoPrimeComplementCarmichaels (X H B : ℕ) : Set ℕ :=
  {n | n ∈ lowLambdaCarmichaels X H ∧
    ∃ a p q : ℕ, p.Prime ∧ q.Prime ∧ n = a * p * q ∧ p * q ≤ a ∧ a ≤ B}

/-- Counting `(a,p,q - 1)` with `q - 1 ∣ a*p - 1`. Unlike the prime-complement
bound this incurs a sum over a second prime `p`. -/
theorem twoPrimeComplementCarmichaels_card_le_divisor_sum (X H B : ℕ) :
    (twoPrimeComplementCarmichaels X H B).ncard ≤
      ∑ a ∈ Finset.Icc 1 B, ∑ p ∈ Finset.Ioc 1 (H + 1),
        (a * p - 1).divisors.card := by
  classical
  let s : Finset ℕ := (Finset.Icc 1 B).biUnion fun a =>
    (Finset.Ioc 1 (H + 1)).biUnion fun p =>
      (a * p - 1).divisors.image (fun d => a * p * (d + 1))
  have hcover : twoPrimeComplementCarmichaels X H B ⊆ (s : Set ℕ) := by
    intro n hn
    obtain ⟨⟨hnC, _, hnH⟩, a, p, q, hp, hq, hnfac, _, haB⟩ := hn
    have hn1 : 1 < n := (hnC 1 (by omega) (by simp)).2.2
    have ha1 : 1 ≤ a := by
      by_contra ha
      have ha0 : a = 0 := by omega
      have hn0 : n = 0 := by simpa [ha0] using hnfac
      omega
    have hpn : p ∣ n := by
      rw [hnfac]
      exact ⟨a * q, by ac_rfl⟩
    have hpH : p ≤ H + 1 :=
      prime_le_lambda_plus_one (by omega : 0 < n) hnH hp hpn
    have hqfactor : n = q * (a * p) := by rw [hnfac]; ac_rfl
    have hqdiv : q - 1 ∣ a * p - 1 :=
      isCarmichael_cofactor_constraint hnC hq hqfactor
    have hap2 : 2 ≤ a * p := by
      have hmul := Nat.mul_le_mul ha1 hp.two_le
      simpa only [one_mul] using hmul
    have hqmem : q - 1 ∈ (a * p - 1).divisors :=
      Nat.mem_divisors.mpr ⟨hqdiv, by omega⟩
    change n ∈ s
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha1, haB⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finset.mem_Ioc.mpr ⟨hp.one_lt, hpH⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q - 1, hqmem, ?_⟩
    rw [Nat.sub_add_cancel hq.one_le]
    exact hnfac.symm
  calc
    (twoPrimeComplementCarmichaels X H B).ncard ≤ s.card := by
      simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hcover
    _ ≤ ∑ a ∈ Finset.Icc 1 B,
          ∑ p ∈ Finset.Ioc 1 (H + 1),
            ((a * p - 1).divisors.image (fun d => a * p * (d + 1))).card := by
      calc
        s.card ≤ ∑ a ∈ Finset.Icc 1 B,
            ((Finset.Ioc 1 (H + 1)).biUnion fun p =>
              (a * p - 1).divisors.image (fun d => a * p * (d + 1))).card :=
          Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum fun a _ => Finset.card_biUnion_le
    _ ≤ ∑ a ∈ Finset.Icc 1 B, ∑ p ∈ Finset.Ioc 1 (H + 1),
          (a * p - 1).divisors.card := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_image_le

/-- The same size obstruction applies to a semiprime complementary block. -/
theorem twoPrimeComplementCarmichaels_le_block_times_cutoff_sq (X H B : ℕ) :
    twoPrimeComplementCarmichaels X H B ⊆
      {n : ℕ | n ≤ B * ((H + 1) * (H + 1))} := by
  intro n hn
  obtain ⟨⟨hnC, _, hnH⟩, a, p, q, hp, hq, hnfac, _, haB⟩ := hn
  have hnpos : 0 < n := by
    have h := (hnC 1 (by omega) (by simp)).2.2
    omega
  have hpn : p ∣ n := by
    rw [hnfac]
    exact ⟨a * q, by ac_rfl⟩
  have hqn : q ∣ n := by
    rw [hnfac]
    exact ⟨a * p, by ac_rfl⟩
  have hpH := prime_le_lambda_plus_one hnpos hnH hp hpn
  have hqH := prime_le_lambda_plus_one hnpos hnH hq hqn
  change n ≤ B * ((H + 1) * (H + 1))
  calc
    n = a * (p * q) := by rw [hnfac]; ring
    _ ≤ B * ((H + 1) * (H + 1)) :=
      Nat.mul_le_mul haB (Nat.mul_le_mul hpH hqH)


/-- More generally, a squarefree complementary factor with at most `r` prime
factors is at most `(H + 1)^r`. Thus Carmichael numbers above
`B * (H + 1)^r` require more than `r` primes in *every* such complement. -/
theorem lowLambda_squarefree_cofactor_le_of_card (X H B r n a b : ℕ)
    (hn : n ∈ lowLambdaCarmichaels X H) (hnfac : n = a * b)
    (hsq : Squarefree b) (haB : a ≤ B) (hcard : b.primeFactors.card ≤ r) :
    n ≤ B * (H + 1) ^ r := by
  obtain ⟨hnC, _, hnH⟩ := hn
  have hnpos : 0 < n := by
    have h := (hnC 1 (by omega) (by simp)).2.2
    omega
  have hprimes (p : ℕ) (hp : p ∈ b.primeFactors) : p ≤ H + 1 := by
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨c, hc⟩ := hpb
    have hpn : p ∣ n := by
      rw [hnfac, hc]
      exact ⟨a * c, by ac_rfl⟩
    exact prime_le_lambda_plus_one hnpos hnH
      (Nat.prime_of_mem_primeFactors hp) hpn
  have hbpow : b ≤ (H + 1) ^ b.primeFactors.card := by
    calc
      b = ∏ p ∈ b.primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ≤ (H + 1) ^ b.primeFactors.card :=
        Finset.prod_le_pow_card b.primeFactors id (H + 1) hprimes
  have hbR : b ≤ (H + 1) ^ r :=
    hbpow.trans (pow_le_pow_right₀ (by omega : 1 ≤ H + 1) hcard)
  calc
    n = a * b := hnfac
    _ ≤ B * (H + 1) ^ r := Nat.mul_le_mul haB hbR

/-- Contrapositive: the residual composite block has many distinct primes
when the starting number is above the size allowed by a short product. -/
theorem lowLambda_squarefree_cofactor_many_primes (X H B r n a b : ℕ)
    (hn : n ∈ lowLambdaCarmichaels X H) (hnfac : n = a * b)
    (hsq : Squarefree b) (haB : a ≤ B) (hlarge : B * (H + 1) ^ r < n) :
    r < b.primeFactors.card := by
  by_contra h
  have hcard : b.primeFactors.card ≤ r := by omega
  have := lowLambda_squarefree_cofactor_le_of_card X H B r n a b
    hn hnfac hsq haB hcard
  omega

end Erdos1057

#print axioms Erdos1057.primeComplementCarmichaels_le_block_times_cutoff
#print axioms Erdos1057.twoPrimeComplementCarmichaels_card_le_divisor_sum
#print axioms Erdos1057.twoPrimeComplementCarmichaels_le_block_times_cutoff_sq
#print axioms Erdos1057.lowLambda_squarefree_cofactor_le_of_card
#print axioms Erdos1057.lowLambda_squarefree_cofactor_many_primes
