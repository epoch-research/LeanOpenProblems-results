import Submission.TotientFiber

/-!
# A finite smooth-prime pigeonhole bound for totient fibers

For a finite set `P` of primes at most `X`, suppose every prime factor of
`p - 1` is at most `Y` for every `p ∈ P`. Products of `k` distinct elements
of `P` are distinct squarefree integers. Their totients are positive,
`Y`-smooth, and at most `X ^ k`.

A positive `Y`-smooth integer at most `2 ^ B` is determined by its
factorization on `Fin (Y + 1)`, with every exponent in `Fin (B + 1)`.
Consequently there are at most `(B + 1) ^ (Y + 1)` such outputs in any
finite set. Taking `B = k * X` and a largest squarefree totient fiber gives
`choose P.card k ≤ squarefreeFiberCard n * (k * X + 1) ^ (Y + 1)`.

This is a finite quantitative bridge, not a proof of the full conjecture.
It imports neither `Submission.Spec` nor any conjectural statement.
-/

namespace Erdos821Aux

open Nat

/-- The squarefree integer associated to a finite set of primes. -/
def primeProduct (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

/-- The prime support of a product of distinct primes is exactly the original set. -/
theorem primeFactors_primeProduct {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    (primeProduct S).primeFactors = S :=
  Nat.primeFactors_prod hS

/-- Products of distinct primes are squarefree, including the empty product. -/
theorem squarefree_primeProduct {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (primeProduct S) := by
  simpa only [rad, primeFactors_primeProduct hS] using
    squarefree_rad (primeProduct S)

/-- Euler's formula on a product of distinct primes. -/
theorem totient_primeProduct {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Nat.totient (primeProduct S) = ∏ p ∈ S, (p - 1) := by
  simpa only [rad, primeFactors_primeProduct hS] using
    totient_rad (primeProduct S)

/-- Distinct finite sets of primes give distinct products. -/
theorem primeProduct_injective {S T : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (h : primeProduct S = primeProduct T) : S = T := by
  simpa only [primeFactors_primeProduct hS, primeFactors_primeProduct hT] using
    congrArg Nat.primeFactors h

/-- A prime-product totient is bounded above by the corresponding power. -/
theorem totient_primeProduct_le_pow {S : Finset ℕ} {X : ℕ}
    (hX : ∀ p ∈ S, p ≤ X) : Nat.totient (primeProduct S) ≤ X ^ S.card := by
  exact (Nat.totient_le _).trans (Finset.prod_le_pow_card S (fun p => p) X hX)

/-- All but possibly the prime `2` contribute at least `2` to the totient. -/
theorem two_pow_card_sub_one_le_totient_primeProduct {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    2 ^ (S.card - 1) ≤ Nat.totient (primeProduct S) := by
  have hcard : S.card - 1 ≤ (S.erase 2).card := by
    by_cases h2 : 2 ∈ S
    · rw [Finset.card_erase_of_mem h2]
    · rw [Finset.erase_eq_of_notMem h2]
      exact Nat.sub_le _ _
  calc
    2 ^ (S.card - 1) ≤ 2 ^ (S.erase 2).card :=
      Nat.pow_le_pow_right (by decide) hcard
    _ ≤ ∏ p ∈ S.erase 2, (p - 1) := by
      apply Finset.pow_card_le_prod
      intro p hp
      obtain ⟨hp2, hpS⟩ := Finset.mem_erase.mp hp
      have := (hS p hpS).two_le
      omega
    _ = ∏ p ∈ S, (p - 1) := Finset.prod_erase S (by decide : (2 : ℕ) - 1 = 1)
    _ = Nat.totient (primeProduct S) := (totient_primeProduct hS).symm

/-- Smoothness of the shifted primes passes to the totient of their product. -/
theorem primeFactors_totient_primeProduct_le {S : Finset ℕ} {Y : ℕ}
    (hS : ∀ p ∈ S, p.Prime)
    (hSmooth : ∀ p ∈ S, ∀ q ∈ (p - 1).primeFactors, q ≤ Y) :
    ∀ q ∈ (Nat.totient (primeProduct S)).primeFactors, q ≤ Y := by
  intro q hq
  rw [totient_primeProduct hS] at hq
  have hqprime := Nat.prime_of_mem_primeFactors hq
  obtain ⟨p, hp, hqp⟩ :=
    (hqprime.prime.dvd_finset_prod_iff (fun p => p - 1)).mp
      (Nat.dvd_of_mem_primeFactors hq)
  apply hSmooth p hp q
  exact Nat.mem_primeFactors.mpr
    ⟨hqprime, hqp, (Nat.sub_pos_of_lt (hS p hp).one_lt).ne'⟩

/-- The rough bound `n ≤ 2 ^ B` bounds every prime-factor exponent by `B`. -/
theorem factorization_le_of_le_two_pow {n B : ℕ} (hn : n ≤ 2 ^ B) (q : ℕ) :
    n.factorization q ≤ B := by
  by_cases hq : q.Prime
  · exact Nat.factorization_le_of_le_pow
      (hn.trans (Nat.pow_le_pow_left hq.two_le B))
  · simp only [Nat.factorization_eq_zero_of_not_prime n hq]
    exact Nat.zero_le _

/-- Above the smoothness bound, all factorization coordinates vanish. -/
theorem factorization_eq_zero_of_primeFactors_le {n Y q : ℕ}
    (hn : ∀ p ∈ n.primeFactors, p ≤ Y) (hq : Y < q) :
    n.factorization q = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [Nat.support_factorization]
  intro hmem
  exact (not_le_of_gt hq) (hn q hmem)

/-- Counting positive smooth integers by a bounded finite-function encoding.
No estimate for the number of primes at most `Y` is needed. -/
theorem card_le_of_smooth_bounded (T : Finset ℕ) (B Y : ℕ)
    (hT : ∀ n ∈ T, 0 < n ∧ n ≤ 2 ^ B ∧ ∀ q ∈ n.primeFactors, q ≤ Y) :
    T.card ≤ (B + 1) ^ (Y + 1) := by
  classical
  let encode : {n : ℕ // n ∈ T} → Fin (Y + 1) → Fin (B + 1) :=
    fun n q => ⟨n.val.factorization q.val,
      Nat.lt_succ_of_le (factorization_le_of_le_two_pow (hT n.val n.property).2.1 q.val)⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (hT a.val a.property).1.ne'
      (hT b.val b.property).1.ne'
    intro q
    by_cases hq : q ≤ Y
    · exact congrArg (fun f : Fin (Y + 1) → Fin (B + 1) =>
        (f ⟨q, Nat.lt_succ_of_le hq⟩).val) hab
    · have hq' : Y < q := Nat.lt_of_not_ge hq
      rw [factorization_eq_zero_of_primeFactors_le (hT a.val a.property).2.2 hq',
        factorization_eq_zero_of_primeFactors_le (hT b.val b.property).2.2 hq']
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective encode hencode

/-- The number of elements of a finite squarefree family at a fixed totient
is at most the cardinality of the entire squarefree fiber. -/
theorem card_filter_totient_le_squarefreeFiberCard (A : Finset ℕ)
    (hA : ∀ m ∈ A, Squarefree m) (n : ℕ) :
    (A.filter (fun m => Nat.totient m = n)).card ≤ squarefreeFiberCard n := by
  classical
  unfold squarefreeFiberCard
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard _ (squarefree_totient_fiber_finite n)
  intro m hm
  obtain ⟨hmA, hmn⟩ := Finset.mem_filter.mp hm
  exact ⟨hA m hmA, hmn⟩

/-- General finite pigeonhole principle for a nonempty squarefree family. -/
theorem exists_squarefreeFiberCard_mul_card_image (A : Finset ℕ)
    (hA : A.Nonempty) (hSq : ∀ m ∈ A, Squarefree m) :
    ∃ n ∈ A.image Nat.totient,
      A.card ≤ squarefreeFiberCard n * (A.image Nat.totient).card := by
  classical
  obtain ⟨n, hn, hmax⟩ :=
    (A.image Nat.totient).exists_max_image squarefreeFiberCard (hA.image Nat.totient)
  refine ⟨n, hn, Finset.card_le_mul_card_image A (squarefreeFiberCard n) ?_⟩
  intro b hb
  exact (card_filter_totient_le_squarefreeFiberCard A hSq b).trans (hmax b hb)

/-- Quantitative smooth-prime pigeonhole principle, with positivity,
upper and lower bounds, and smoothness of the resulting totient value.
This includes `k = 0` and needs no extra assumption on `X` or `Y`. -/
theorem smooth_prime_pigeonhole_squarefree_with_bounds (P : Finset ℕ) (X Y k : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X ∧ ∀ q ∈ (p - 1).primeFactors, q ≤ Y)
    (hk : k ≤ P.card) :
    ∃ n : ℕ, 0 < n ∧ 2 ^ (k - 1) ≤ n ∧ n ≤ X ^ k ∧
      (∀ q ∈ n.primeFactors, q ≤ Y) ∧
      Nat.choose P.card k ≤ squarefreeFiberCard n * (k * X + 1) ^ (Y + 1) := by
  classical
  let A : Finset ℕ := (P.powersetCard k).image primeProduct
  have hPrime : ∀ S ∈ P.powersetCard k, ∀ p ∈ S, p.Prime := by
    intro S hS p hp
    exact (hP p ((Finset.mem_powersetCard.mp hS).1 hp)).1
  have hAcard : A.card = Nat.choose P.card k := by
    dsimp [A]
    rw [Finset.card_image_of_injOn, Finset.card_powersetCard]
    intro S hS T hT hST
    exact primeProduct_injective (hPrime S hS) (hPrime T hT) hST
  have hAnonempty : A.Nonempty :=
    (Finset.powersetCard_nonempty.mpr hk).image primeProduct
  have hSq : ∀ m ∈ A, Squarefree m := by
    intro m hm
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
    exact squarefree_primeProduct (hPrime S hS)
  have hBounds : ∀ n ∈ A.image Nat.totient,
      0 < n ∧ 2 ^ (k - 1) ≤ n ∧ n ≤ X ^ k ∧ ∀ q ∈ n.primeFactors, q ≤ Y := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hSP, hSk⟩ := Finset.mem_powersetCard.mp hS
    refine ⟨Nat.totient_pos.mpr (Nat.pos_of_ne_zero (squarefree_primeProduct
      (hPrime S hS)).ne_zero), ?_, ?_, ?_⟩
    · simpa only [hSk] using two_pow_card_sub_one_le_totient_primeProduct (hPrime S hS)
    · simpa only [hSk] using totient_primeProduct_le_pow
        (fun p hp => (hP p (hSP hp)).2.1)
    · exact primeFactors_totient_primeProduct_le (hPrime S hS)
        (fun p hp => (hP p (hSP hp)).2.2)
  have hXpow : X ^ k ≤ 2 ^ (k * X) := by
    calc
      X ^ k ≤ (2 ^ X) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) k
      _ = 2 ^ (k * X) := by rw [← Nat.pow_mul, Nat.mul_comm X k]
  have hOutputs : (A.image Nat.totient).card ≤ (k * X + 1) ^ (Y + 1) := by
    apply card_le_of_smooth_bounded
    intro n hn
    obtain ⟨hpos, _, hupper, hsmooth⟩ := hBounds n hn
    exact ⟨hpos, hupper.trans hXpow, hsmooth⟩
  obtain ⟨n, hn, hcount⟩ := exists_squarefreeFiberCard_mul_card_image A hAnonempty hSq
  obtain ⟨hpos, hlower, hupper, hsmooth⟩ := hBounds n hn
  refine ⟨n, hpos, hlower, hupper, hsmooth, ?_⟩
  rw [← hAcard]
  exact hcount.trans (Nat.mul_le_mul_left (squarefreeFiberCard n) hOutputs)

/-- The squarefree-fiber form of the finite quantitative bridge. -/
theorem smooth_prime_pigeonhole_squarefree (P : Finset ℕ) (X Y k : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X ∧ ∀ q ∈ (p - 1).primeFactors, q ≤ Y)
    (hk : k ≤ P.card) :
    ∃ n : ℕ, 0 < n ∧ n ≤ X ^ k ∧
      Nat.choose P.card k ≤ squarefreeFiberCard n * (k * X + 1) ^ (Y + 1) := by
  obtain ⟨n, hpos, _, hupper, _, hcount⟩ :=
    smooth_prime_pigeonhole_squarefree_with_bounds P X Y k hP hk
  exact ⟨n, hpos, hupper, hcount⟩

/-- The full-fiber consequence, using inclusion of squarefree fibers. -/
theorem smooth_prime_pigeonhole (P : Finset ℕ) (X Y k : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X ∧ ∀ q ∈ (p - 1).primeFactors, q ≤ Y)
    (hk : k ≤ P.card) :
    ∃ n : ℕ, 0 < n ∧ n ≤ X ^ k ∧
      Nat.choose P.card k ≤ fiberCard n * (k * X + 1) ^ (Y + 1) := by
  obtain ⟨n, hpos, hupper, hcount⟩ := smooth_prime_pigeonhole_squarefree P X Y k hP hk
  refine ⟨n, hpos, hupper, hcount.trans ?_⟩
  exact Nat.mul_le_mul_right _ (squarefreeFiberCard_le_fiberCard n)

end Erdos821Aux

#print axioms Erdos821Aux.card_le_of_smooth_bounded
#print axioms Erdos821Aux.exists_squarefreeFiberCard_mul_card_image
#print axioms Erdos821Aux.smooth_prime_pigeonhole_squarefree_with_bounds
#print axioms Erdos821Aux.smooth_prime_pigeonhole_squarefree
#print axioms Erdos821Aux.smooth_prime_pigeonhole
