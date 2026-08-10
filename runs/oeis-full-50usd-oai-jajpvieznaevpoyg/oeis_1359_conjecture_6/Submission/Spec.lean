import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
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

lemma factorial_eq_split_zmod (p q : ℕ) (hp1 : 1 ≤ p) (hpq : p + 2 ≤ q) :
    (((q - 1)! : ℕ) : ZMod q) =
      ((p.factorial : ℕ) : ZMod q) *
        (((Finset.Icc (p + 1) (q - 2)).prod id : ℕ) : ZMod q) *
          (((q - 1 : ℕ) : ZMod q)) := by
  have hqpos : 0 < q := by omega
  have hp1' : 1 ≤ p + 1 := by omega
  have hpq1 : p + 1 ≤ q - 1 := by omega
  have hq1 : 1 ≤ q - 1 := by omega
  calc
    (((q - 1)! : ℕ) : ZMod q)
        = ((∏ x ∈ Finset.Ico 1 ((q - 1) + 1), x : ℕ) : ZMod q) := by
            rw [Finset.prod_Ico_id_eq_factorial]
    _ = ∏ x ∈ Finset.Ico 1 ((q - 1) + 1), (x : ZMod q) := by
            simp only [Finset.prod_natCast]
    _ = (∏ x ∈ Finset.Ico 1 (q - 1), (x : ZMod q)) * ((q - 1 : ℕ) : ZMod q) := by
            rw [Finset.prod_Ico_succ_top hq1]
    _ = ((∏ x ∈ Finset.Ico 1 (p + 1), (x : ZMod q)) *
            (∏ x ∈ Finset.Ico (p + 1) (q - 1), (x : ZMod q))) *
              (((q - 1 : ℕ) : ZMod q)) := by
            rw [← Finset.prod_Ico_consecutive (fun x : ℕ => (x : ZMod q)) hp1' hpq1]
    _ = ((p.factorial : ℕ) : ZMod q) *
          (((Finset.Icc (p + 1) (q - 2)).prod id : ℕ) : ZMod q) *
            (((q - 1 : ℕ) : ZMod q)) := by
            have hfac : (∏ x ∈ Finset.Ico 1 (p + 1), (x : ZMod q)) =
                ((p.factorial : ℕ) : ZMod q) := by
              rw [← Finset.prod_Ico_id_eq_factorial, Finset.prod_natCast]
            have hI : Finset.Ico (p + 1) (q - 1) = Finset.Icc (p + 1) (q - 2) := by
              rw [← Finset.Ico_add_one_right_eq_Icc]
              congr
              omega
            rw [hfac, hI]
            simp only [Finset.prod_natCast, id]

lemma zmod_nat_sub_one_eq_neg_one (q : ℕ) (hq : 0 < q) :
    (((q - 1 : ℕ) : ZMod q)) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  have hnat : (q - 1) + 1 = q := Nat.sub_add_cancel hq
  have h : ((((q - 1) + 1 : ℕ) : ZMod q)) = 0 := by
    rw [hnat]
    exact ZMod.natCast_self q
  simpa [Nat.cast_add] using h

lemma factorial_W_mul_eq_one_zmod (p q : ℕ) (hp1 : 1 ≤ p) (hpq : p + 2 ≤ q)
    (hqprime : Nat.Prime q) :
    ((p.factorial : ℕ) : ZMod q) *
      (((Finset.Icc (p + 1) (q - 2)).prod id : ℕ) : ZMod q) = 1 := by
  have hqpos : 0 < q := hqprime.pos
  have hqne1 : q ≠ 1 := hqprime.ne_one
  have hfacWilson : (((q - 1)! : ℕ) : ZMod q) = -1 :=
    (Nat.prime_iff_fac_equiv_neg_one hqne1).mp hqprime
  have hsplit := factorial_eq_split_zmod p q hp1 hpq
  rw [hsplit, zmod_nat_sub_one_eq_neg_one q hqpos] at hfacWilson
  have := congrArg Neg.neg hfacWilson
  simpa [neg_mul, mul_assoc] using this

lemma factorial_congr_iff_W_congr (p q : ℕ) (hp1 : 1 ≤ p) (hpq : p + 2 ≤ q)
    (hqprime : Nat.Prime q) :
    (Nat.factorial p ≡ 1 [MOD q]) ↔
      (((Finset.Icc (p + 1) (q - 2)).prod id) ≡ 1 [MOD q]) := by
  let W : ℕ := (Finset.Icc (p + 1) (q - 2)).prod id
  have hmul : ((p.factorial : ℕ) : ZMod q) * (W : ZMod q) = 1 := by
    simpa [W] using factorial_W_mul_eq_one_zmod p q hp1 hpq hqprime
  constructor
  · intro hA
    have hAz : ((p.factorial : ℕ) : ZMod q) = (((1 : ℕ) : ZMod q)) :=
      (ZMod.natCast_eq_natCast_iff _ _ q).2 hA
    have hWz : (W : ZMod q) = (((1 : ℕ) : ZMod q)) := by
      simpa [hAz] using hmul
    exact (ZMod.natCast_eq_natCast_iff W 1 q).1 hWz
  · intro hW
    have hWz : (W : ZMod q) = (((1 : ℕ) : ZMod q)) :=
      (ZMod.natCast_eq_natCast_iff W 1 q).2 hW
    have hAz : ((p.factorial : ℕ) : ZMod q) = (((1 : ℕ) : ZMod q)) := by
      simpa [hWz] using hmul
    exact (ZMod.natCast_eq_natCast_iff (Nat.factorial p) 1 q).1 hAz


abbrev smallPrimesFor7853 : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89]

abbrev goodSmallFor7853 (n : ℕ) : Prop := ∀ p ∈ smallPrimesFor7853, ¬ p ∣ n

lemma smallFor7853_mem_prime {p : ℕ} (hp : p ∈ smallPrimesFor7853) : Nat.Prime p := by
  simp [smallPrimesFor7853] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

lemma smallFor7853_mem_le_89 {p : ℕ} (hp : p ∈ smallPrimesFor7853) : p ≤ 89 := by
  simp [smallPrimesFor7853] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

lemma minFac_mem_smallFor7853_of_not_prime {n : ℕ} (hn90 : 90 ≤ n) (hnlt : n < 7853)
    (hnp : ¬ Nat.Prime n) : Nat.minFac n ∈ smallPrimesFor7853 := by
  let m := Nat.minFac n
  have hmprime : Nat.Prime m := by
    simpa [m] using Nat.minFac_prime (n := n) (by omega : n ≠ 1)
  have hmlediv : m ≤ n / m := by
    simpa [m] using Nat.minFac_le_div (n := n) (by omega : 0 < n) hnp
  have hdiv : m ∣ n := by simpa [m] using Nat.minFac_dvd n
  have hmul : m * (n / m) = n := Nat.mul_div_cancel' hdiv
  have hm_sq : m * m ≤ n := by
    have := Nat.mul_le_mul_left m hmlediv
    rwa [hmul] at this
  have hm90 : m < 90 := by
    by_contra h
    have h90 : 90 ≤ m := by omega
    nlinarith
  change m ∈ smallPrimesFor7853
  interval_cases m <;> simp [smallPrimesFor7853] at hmprime ⊢ <;> try contradiction

lemma prime_iff_goodSmallFor7853 {n : ℕ} (hn90 : 90 ≤ n) (hnlt : n < 7853) :
    Nat.Prime n ↔ goodSmallFor7853 n := by
  constructor
  · intro hn p hp hdiv
    have hpprime := smallFor7853_mem_prime hp
    have hpeq := (Nat.prime_dvd_prime_iff_eq hpprime hn).1 hdiv
    have hple := smallFor7853_mem_le_89 hp
    omega
  · intro hg
    by_contra hnp
    have hmem := minFac_mem_smallFor7853_of_not_prime hn90 hnlt hnp
    exact hg (Nat.minFac n) hmem (Nat.minFac_dvd n)

lemma count_tail_prime_eq_goodSmallFor7853 (N : ℕ) (hN : N ≤ 7853) :
    Nat.count (fun k => Nat.Prime (90 + k)) (N - 90) =
      Nat.count (fun k => goodSmallFor7853 (90 + k)) (N - 90) := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  by_cases hk : k < N - 90
  · have hlt : 90 + k < 7853 := by omega
    have hiff := prime_iff_goodSmallFor7853 (n := 90 + k) (by omega) hlt
    simp [hk, hiff]
  · simp [hk]

lemma count_prime_eq_goodSmallFor7853 (N : ℕ) (hN90 : 90 ≤ N) (hN : N ≤ 7853) :
    Nat.count Nat.Prime N = Nat.count goodSmallFor7853 N + 23 := by
  have hbaseP : Nat.count Nat.Prime 90 = 24 := by decide
  have hbaseG : Nat.count goodSmallFor7853 90 = 1 := by decide
  have htail := count_tail_prime_eq_goodSmallFor7853 N hN
  rw [show N = 90 + (N - 90) by omega, Nat.count_add, Nat.count_add, hbaseP, hbaseG, htail]
  omega

lemma count_prime_7841 : Nat.count Nat.Prime 7841 = 990 := by
  have hg : Nat.count goodSmallFor7853 7841 = 967 := by decide
  rw [count_prime_eq_goodSmallFor7853 7841 (by norm_num) (by norm_num), hg]

lemma count_prime_7853 : Nat.count Nat.Prime 7853 = 991 := by
  have hg : Nat.count goodSmallFor7853 7853 = 968 := by decide
  rw [count_prime_eq_goodSmallFor7853 7853 (by norm_num) (by norm_num), hg]

lemma nth_prime_990_eq_7841 : Nat.nth Nat.Prime 990 = 7841 := by
  rw [show 990 = Nat.count Nat.Prime 7841 by rw [count_prime_7841]]
  exact Nat.nth_count (by norm_num : Nat.Prime 7841)

lemma nth_prime_991_eq_7853 : Nat.nth Nat.Prime 991 = 7853 := by
  rw [show 991 = Nat.count Nat.Prime 7853 by rw [count_prime_7853]]
  exact Nat.nth_count (by norm_num : Nat.Prime 7853)

lemma congr_exception_991 :
    let Pk := Nat.nth Nat.Prime (991 - 1)
    let Pk_succ := Nat.nth Nat.Prime 991
    Nat.factorial Pk ≡ 1 [MOD Pk_succ] := by
  dsimp
  rw [nth_prime_990_eq_7841, nth_prime_991_eq_7853]
  exact (factorial_congr_iff_W_congr 7841 7853 (by norm_num) (by norm_num)
    (by norm_num : Nat.Prime 7853)).mpr (by decide)

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
  dsimp only
  let p := Nat.nth Nat.Prime (k - 1)
  let q := Nat.nth Nat.Prime k
  have hksucc : (k - 1) + 1 = k := by omega
  have hpprime : Nat.Prime p := by simpa [p] using Nat.prime_nth_prime (k - 1)
  have hqprime : Nat.Prime q := by simpa [q] using Nat.prime_nth_prime k
  have hp_lt_q : p < q := by
    have : k - 1 < k := by omega
    simpa [p, q] using (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 this
  have hidxpos : 0 < k - 1 := by omega
  have htwo_lt_p : 2 < p := by
    have : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime (k - 1) :=
      (Nat.nth_lt_nth Nat.infinite_setOf_prime).2 hidxpos
    simpa [p, Nat.nth_prime_zero_eq_two] using this
  have hp1 : 1 ≤ p := by omega
  have hq_ne_p1 : q ≠ p + 1 := by
    intro h
    have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
    have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
    rcases hpodd with ⟨a, ha⟩
    rcases hqodd with ⟨b, hb⟩
    omega
  have hpq2 : p + 2 ≤ q := by omega
  have hiffW : (Nat.factorial p ≡ 1 [MOD q]) ↔
      ((Finset.Icc (p + 1) (q - 2)).prod id ≡ 1 [MOD q]) :=
    factorial_congr_iff_W_congr p q hp1 hpq2 hqprime
  have hNoPrimeBeforeQ : ∀ {r : ℕ}, Nat.Prime r → r < q → r ≤ p := by
    intro r hr hrt
    have hrt' : r < Nat.nth Nat.Prime ((k - 1) + 1) := by simpa [q, hksucc] using hrt
    simpa [p] using Nat.le_nth_of_lt_nth_succ (p := Nat.Prime) hrt' hr
  constructor
  · intro hCong
    have hW : (Finset.Icc (p + 1) (q - 2)).prod id ≡ 1 [MOD q] := hiffW.mp hCong
    by_cases hgap : q - p > 2
    · right; right
      exact ⟨hgap, hW⟩
    · left
      have hq_eq : q = p + 2 := by omega
      simpa [p, ← hq_eq] using hqprime
  · intro hRhs
    rcases hRhs with hTwin | hRest
    · have hq_eq : q = p + 2 := by
        by_contra
        have hlt : p + 2 < q := by omega
        have hle : p + 2 ≤ p := hNoPrimeBeforeQ hTwin hlt
        omega
      have hW : (Finset.Icc (p + 1) (q - 2)).prod id ≡ 1 [MOD q] := by
        have hI : Finset.Icc (p + 1) (q - 2) = ∅ := by
          rw [hq_eq]
          exact Icc_eq_empty (by omega)
        simpa [hI] using (Nat.ModEq.refl (n := q) 1)
      exact hiffW.mpr hW
    · rcases hRest with hk991 | hgapW
      · have hCong991 := congr_exception_991
        subst k
        simpa [p, q] using hCong991
      · exact hiffW.mpr hgapW.2
