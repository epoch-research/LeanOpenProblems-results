import FormalConjectures.Util.ProblemImports
open Nat

/--
A001359 Lesser of twin primes.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n > 0 then
    (n - 1).nth (fun p => Nat.Prime p ∧ Nat.Prime (p + 2))
  else
    0

open Finset Nat.ModEq

/-!
### Auxiliary lemmas

We prove the conjecture. The core is a Wilson's-theorem argument showing that, for the `k`-th
prime `P_k` with successor prime `P_{k+1}`, the congruence `P_k! ≡ 1 (mod P_{k+1})` is equivalent
to `∏_{i=P_k+1}^{P_{k+1}-2} i ≡ 1 (mod P_{k+1})`.  The `k = 991` exceptional case is verified by
computing that the `991`-st prime is `7841` and the `992`-nd is `7853`.
-/

/-- **Wilson-based equivalence.**  For a prime `p` and `a + 2 ≤ p`, the factorial congruence
`a! ≡ 1 (mod p)` is equivalent to `∏_{i=a+1}^{p-2} i ≡ 1 (mod p)`.

Indeed `(p-1)! = a! · (∏_{i=a+1}^{p-2} i) · (p-1)`, and modulo `p` Wilson's lemma gives
`(p-1)! ≡ -1` while `p-1 ≡ -1`, so `a! · ∏ ≡ 1`; since both factors are units, one is `1` iff the
other is. -/
theorem key_equiv (a p : ℕ) (hp : p.Prime) (hap : a + 2 ≤ p) :
    (a ! ≡ 1 [MOD p]) ↔ ((Finset.Icc (a + 1) (p - 2)).prod id ≡ 1 [MOD p]) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  set W : ℕ := (Finset.Icc (a + 1) (p - 2)).prod id with hWdef
  have hWeq : W = ∏ x ∈ Ico (a + 1) (p - 1), x := by
    rw [hWdef, show p - 1 = (p - 2) + 1 by omega, Finset.Ico_add_one_right_eq_Icc]; rfl
  have hfacL : ∏ x ∈ Ico 1 p, x = (p - 1)! := by
    have := Finset.prod_Ico_id_eq_factorial (p - 1)
    rwa [show p - 1 + 1 = p by omega] at this
  have ha : ∏ x ∈ Ico 1 (a + 1), x = a ! := Finset.prod_Ico_id_eq_factorial a
  have hsplit1 : (∏ x ∈ Ico 1 (a + 1), x) * (∏ x ∈ Ico (a + 1) p, x) = ∏ x ∈ Ico 1 p, x :=
    Finset.prod_Ico_consecutive _ (by omega) (by omega)
  have hsplit2 :
      (∏ x ∈ Ico (a + 1) (p - 1), x) * (∏ x ∈ Ico (p - 1) p, x) = ∏ x ∈ Ico (a + 1) p, x :=
    Finset.prod_Ico_consecutive _ (by omega) (by omega)
  have hlast : (∏ x ∈ Ico (p - 1) p, x) = p - 1 := by
    have hset : Ico (p - 1) p = {p - 1} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [hset, Finset.prod_singleton]
  have hfac : (p - 1)! = a ! * (W * (p - 1)) := by
    rw [← hfacL, ← hsplit1, ha, ← hsplit2, hlast, hWeq]
  have hwil : ((p - 1)! : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hpm1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have key : (a ! : ZMod p) * (W : ZMod p) = 1 := by
    have hc : ((p - 1)! : ZMod p) = (a ! : ZMod p) * (W : ZMod p) * ((p - 1 : ℕ) : ZMod p) := by
      rw [hfac]; push_cast; ring
    rw [hwil, hpm1] at hc
    linear_combination hc
  have hiff : ((a ! : ZMod p) = 1) ↔ ((W : ZMod p) = 1) := by
    constructor
    · intro h; rw [h, one_mul] at key; exact key
    · intro h; rw [h, mul_one] at key; exact key
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact hiff

/-- A fast (kernel-reducible) primality test, correct for `n < 7921 = 89²`: a number is prime iff
it is `≥ 2` and has no divisor `m ∈ [2, 88]` with `m < n`.  (Any composite `n < 7921` has a prime
factor `≤ 88`.) -/
def fastPrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && (List.range 89).all (fun m => decide (¬ (2 ≤ m ∧ m < n ∧ m ∣ n)))

theorem fastPrime_iff (n : ℕ) :
    (fastPrime n = true) ↔ (2 ≤ n ∧ ∀ m, m < 89 → ¬ (2 ≤ m ∧ m < n ∧ m ∣ n)) := by
  unfold fastPrime
  rw [Bool.and_eq_true, List.all_eq_true]
  simp only [decide_eq_true_eq, List.mem_range]

theorem fastPrime_correct (n : ℕ) (hn : n < 7921) : (fastPrime n = true) ↔ Nat.Prime n := by
  rw [fastPrime_iff, Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, hrest⟩
    refine ⟨h2, ?_⟩
    intro m hm2 hmn hdvd
    have hcomp : ¬ Nat.Prime n := by
      intro hp
      rcases hp.eq_one_or_self_of_dvd m hdvd with h | h <;> omega
    have hpos : 0 < n := by omega
    have hsq := Nat.minFac_sq_le_self hpos hcomp
    have hmf_dvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hmf_prime : Nat.Prime (Nat.minFac n) := Nat.minFac_prime (by omega)
    have hmf2 : 2 ≤ Nat.minFac n := hmf_prime.two_le
    have hmf_le : Nat.minFac n ≤ 88 := by nlinarith [hsq]
    have hmf_lt_n : Nat.minFac n < n := by nlinarith [hsq, hmf2]
    exact hrest (Nat.minFac n) (by omega) ⟨hmf2, hmf_lt_n, hmf_dvd⟩
  · rintro ⟨h2, hrest⟩
    refine ⟨h2, ?_⟩
    intro m hm89 ⟨hm2, hmn, hdvd⟩
    exact hrest m hm2 hmn hdvd

/-- Rewrite a prime count below `N ≤ 7921` as a `countP` of the fast test. -/
theorem count_eq_countP_fastPrime (N : ℕ) (hN : N ≤ 7921) :
    Nat.count Nat.Prime N = (List.range N).countP fastPrime := by
  show (List.range N).countP (fun a => decide (Nat.Prime a)) = _
  apply List.countP_congr
  intro x hx
  rw [List.mem_range] at hx
  rw [decide_eq_true_eq]
  exact (fastPrime_correct x (by omega)).symm

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- There are exactly `990` primes below `7841`, so `7841` is the `991`-st prime. -/
theorem count_7841 : Nat.count Nat.Prime 7841 = 990 := by
  rw [count_eq_countP_fastPrime 7841 (by norm_num)]; decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- There are exactly `991` primes below `7853`, so `7853` is the `992`-nd prime. -/
theorem count_7853 : Nat.count Nat.Prime 7853 = 991 := by
  rw [count_eq_countP_fastPrime 7853 (by norm_num)]; decide

/-- The `991`-st prime (`0`-indexed `nth Prime 990`) is `7841`. -/
theorem nth_prime_990 : Nat.nth Nat.Prime 990 = 7841 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 7841) (by norm_num)
  rwa [count_7841] at h

/-- The `992`-nd prime (`0`-indexed `nth Prime 991`) is `7853`. -/
theorem nth_prime_991 : Nat.nth Nat.Prime 991 = 7853 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 7853) (by norm_num)
  rwa [count_7853] at h

/--
Conjecture: A001359 Primes `prime(k)` such that `prime(k)! == 1 (mod prime(k+1))` with the exception of
`prime(991) = 7841` and other unknown primes `prime(k)` for which
`(prime(k)+1)*(prime(k)+2)*...*(prime(k+1)-2) == 1 (mod prime(k+1))` where `prime(k+1) - prime(k) > 2`.
Here, `prime(k)` denotes the k-th prime number (1-indexed, so prime(k) = Nat.nth Nat.Prime (k-1) for k > 0).
-/
theorem oeis_1359_conjecture_6 :
  -- k is the 1-based index. We start with k > 1, corresponding to the first twin prime 3 (P_2).
  ∀ (k : ℕ), k > 1 →
  let Pk      := Nat.nth Nat.Prime (k - 1); -- Pk is the k-th prime
  let Pk_succ := Nat.nth Nat.Prime k;       -- Pk_succ is the (k+1)-th prime
  let Congruence := Nat.factorial Pk ≡ 1 [MOD Pk_succ];
  let IsLesserTwinPrime := Nat.Prime (Pk + 2);

  -- The product Wk_prod is $\prod_{i=P_k+1}^{P_{k+1}-2} i$. This defines the value W_k in the OEIS comment.
  let Wk_prod : ℕ := Finset.prod (Finset.Icc (Pk + 1) (Pk_succ - 2)) id;

  -- The set of primes satisfying the congruence is the set of lesser twin primes
  -- union the set of exceptional indices C \ T.
  Iff Congruence (
    IsLesserTwinPrime ∨
    (k = 991) ∨
    (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])
  )
:= by
  intro k hk
  intro Pk Pk_succ Congruence IsLesserTwinPrime Wk_prod
  have hinf : (setOf Nat.Prime).Infinite := Nat.infinite_setOf_prime
  have hr_prime : Pk.Prime := Nat.prime_nth_prime (k - 1)
  have hq_prime : Pk_succ.Prime := Nat.prime_nth_prime k
  have hrq : Pk < Pk_succ := (Nat.nth_lt_nth hinf).mpr (by omega)
  have hr3 : 3 ≤ Pk := by
    have h1 : Nat.nth Nat.Prime 1 ≤ Pk := (Nat.nth_le_nth hinf).mpr (by omega)
    rw [Nat.nth_prime_one_eq_three] at h1; exact h1
  -- `Pk_succ` is the next prime after `Pk`: any prime below it is `≤ Pk`.
  have hnext : ∀ b, b.Prime → b < Pk_succ → b ≤ Pk := by
    intro b hb hlt
    have hk1 : k - 1 + 1 = k := by omega
    have hlt' : b < Nat.nth Nat.Prime (k - 1 + 1) := by rw [hk1]; exact hlt
    exact Nat.le_nth_of_lt_nth_succ hlt' hb
  -- The gap is at least `2`: `Pk` is an odd prime, so `Pk + 1` is even hence not prime.
  have hr_odd : Odd Pk := hr_prime.odd_of_ne_two (by omega)
  have hnp : ¬ (Pk + 1).Prime := by
    intro h
    have he : Even (Pk + 1) := by rcases hr_odd with ⟨t, ht⟩; exact ⟨t + 1, by omega⟩
    rw [h.even_iff] at he; omega
  have hgap : Pk + 2 ≤ Pk_succ := by
    rcases Nat.lt_or_ge Pk_succ (Pk + 2) with h | h
    · have hh : Pk_succ = Pk + 1 := by omega
      rw [hh] at hq_prime; exact absurd hq_prime hnp
    · exact h
  -- The Wilson-based equivalence.
  have hKE : Congruence ↔ (Wk_prod ≡ 1 [MOD Pk_succ]) := key_equiv Pk Pk_succ hq_prime hgap
  rw [hKE]
  constructor
  · -- `Wk ≡ 1` implies the disjunction.
    intro hW
    by_cases htwin : (Pk + 2).Prime
    · exact Or.inl htwin
    · refine Or.inr (Or.inr ⟨?_, hW⟩)
      have hqne : Pk_succ ≠ Pk + 2 := by
        intro h; rw [h] at hq_prime; exact htwin hq_prime
      omega
  · -- The disjunction implies `Wk ≡ 1`.
    rintro (htwin | hk991 | ⟨_, hW⟩)
    · -- Twin prime: then `Pk_succ = Pk + 2`, so the product is empty and equals `1`.
      have hqeq : Pk_succ = Pk + 2 := by
        have hqle : Pk_succ ≤ Pk + 2 := by
          by_contra hc; push_neg at hc
          have := hnext (Pk + 2) htwin hc; omega
        omega
      show (Finset.Icc (Pk + 1) (Pk_succ - 2)).prod id ≡ 1 [MOD Pk_succ]
      rw [hqeq, show Pk + 2 - 2 = Pk by omega, Finset.Icc_eq_empty (show ¬ Pk + 1 ≤ Pk by omega),
        Finset.prod_empty]
    · -- The exceptional index `k = 991`: `Pk = 7841`, `Pk_succ = 7853`, verified by computation.
      subst hk991
      have e1 : Pk = 7841 := by show Nat.nth Nat.Prime 990 = 7841; exact nth_prime_990
      have e2 : Pk_succ = 7853 := by show Nat.nth Nat.Prime 991 = 7853; exact nth_prime_991
      show (Finset.Icc (Pk + 1) (Pk_succ - 2)).prod id ≡ 1 [MOD Pk_succ]
      rw [e1, e2]
      decide
    · exact hW
