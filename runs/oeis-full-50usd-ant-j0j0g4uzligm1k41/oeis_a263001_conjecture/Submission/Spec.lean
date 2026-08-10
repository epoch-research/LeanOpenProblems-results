import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

/--
A263001: Number of ordered pairs $(k, m)$ with $k > 0$ and $m > 0$ such that
$n = \pi(k(k+1)) + \pi(m(m+1)/2)$, where $\pi(x)$ denotes the number of primes not exceeding $x$.
-/
noncomputable def A263001 (n : ℕ) : ℕ :=
  -- The set of solutions for a fixed n is finite. We count them by filtering over a large enough Finset.
  -- A bound of n+1 is sufficient for the definition, as k and m must be small relative to n.
  let bound : ℕ := n + 1
  let K_set : Finset ℕ := Icc 1 bound
  let M_set : Finset ℕ := Icc 1 bound

  (filter (fun p : ℕ × ℕ =>
    Nat.primeCounting (p.fst * (p.fst + 1)) + Nat.primeCounting (p.snd * (p.snd + 1) / 2) = n
  ) (Finset.product K_set M_set)).card

open Nat Finset BigOperators

set_option Elab.async false

namespace Sv

def KK : ℕ := 20
lemma KK_pos : 1 ≤ KK := by unfold KK; omega

/-- mask of a finite set of "digit positions": bit `KK*c` set for each `c ∈ S`. -/
def maskOf (S : Finset ℕ) : ℕ := ∑ c ∈ S, 2 ^ (KK * c)

@[simp] lemma maskOf_empty : maskOf ∅ = 0 := by simp [maskOf]

lemma geom_bound (B : ℕ) : ∑ c ∈ Finset.range B, 2 ^ (KK * c) < 2 ^ (KK * B) := by
  induction B with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h2 : 2 ^ (KK * n) + 2 ^ (KK * n) ≤ 2 ^ (KK * (n+1)) := by
      have hh : 2 ^ (KK * n) * 2 ≤ 2 ^ (KK * n) * 2 ^ KK := by
        apply Nat.mul_le_mul_left
        calc 2 = 2^1 := by norm_num
        _ ≤ 2^KK := Nat.pow_le_pow_right (by norm_num) KK_pos
      rw [← pow_add] at hh
      calc 2^(KK*n) + 2^(KK*n) = 2^(KK*n)*2 := by ring
      _ ≤ 2^(KK*n + KK) := hh
      _ = 2^(KK*(n+1)) := by ring_nf
    omega

lemma maskOf_lt (B : ℕ) (S : Finset ℕ) (hS : ∀ c ∈ S, c < B) :
    maskOf S < 2 ^ (KK * B) := by
  have hsum : maskOf S ≤ ∑ c ∈ Finset.range B, 2 ^ (KK * c) := by
    apply Finset.sum_le_sum_of_subset
    intro c hc; exact Finset.mem_range.mpr (hS c hc)
  have := geom_bound B
  omega

lemma testBit_maskOf (S : Finset ℕ) (i : ℕ) :
    (maskOf S).testBit i = decide (∃ c ∈ S, KK * c = i) := by
  -- strong induction on a bound for S
  suffices H : ∀ B S i, (∀ c ∈ S, c < B) →
      (maskOf S).testBit i = decide (∃ c ∈ S, KK * c = i) by
    obtain ⟨B, hB⟩ : ∃ B, ∀ c ∈ S, c < B := by
      rcases S.eq_empty_or_nonempty with h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨S.max' h + 1, fun c hc => Nat.lt_succ_of_le (S.le_max' c hc)⟩
    exact H B S i hB
  clear i S
  intro B
  induction B with
  | zero => intro S i hS; have : S = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]; intro x hx; exact absurd (hS x hx) (by omega)
            subst this; simp
  | succ n ih =>
    intro S i hS
    by_cases hBmem : n ∈ S
    · -- peel n (the maximal possible element)
      have hS' : ∀ c ∈ S.erase n, c < n := by
        intro c hc
        rw [Finset.mem_erase] at hc
        have := hS c hc.2
        omega
      have hsplit : maskOf S = 2 ^ (KK * n) * 1 + maskOf (S.erase n) := by
        rw [maskOf, ← Finset.sum_erase_add S _ hBmem]
        simp [maskOf, Nat.add_comm]
      have hlt : maskOf (S.erase n) < 2 ^ (KK * n) := maskOf_lt n _ hS'
      rw [hsplit, Nat.testBit_two_pow_mul_add 1 hlt]
      by_cases hj : i < KK * n
      · simp only [hj, if_true, ih (S.erase n) i hS']
        apply decide_eq_decide.mpr
        constructor
        · rintro ⟨c, hc, rfl⟩; rw [Finset.mem_erase] at hc; exact ⟨c, hc.2, rfl⟩
        · rintro ⟨c, hc, rfl⟩
          refine ⟨c, ?_, rfl⟩
          rw [Finset.mem_erase]
          refine ⟨?_, hc⟩
          rintro rfl; omega
      · simp only [hj, if_false]
        rw [show (1:ℕ) = 2^0 from rfl, Nat.testBit_two_pow]
        apply decide_eq_decide.mpr
        constructor
        · intro hi
          have : i = KK * n := by omega
          exact ⟨n, hBmem, this.symm⟩
        · rintro ⟨c, hc, rfl⟩
          have hcn : c ≤ n := by have := hS c hc; omega
          have : KK * n ≤ KK * c := by
            rcases Nat.lt_or_ge c n with h|h
            · exfalso; have := KK_pos; nlinarith [hj, Nat.mul_le_mul_left KK (Nat.succ_le_of_lt h)]
            · exact Nat.mul_le_mul_left KK h
          have h2 : KK * c ≤ KK * n := Nat.mul_le_mul_left KK hcn
          have heq : KK * c = KK * n := by omega
          omega
    · have hS' : ∀ c ∈ S, c < n := by
        intro c hc; have := hS c hc
        rcases Nat.lt_or_ge c n with h|h
        · exact h
        · exfalso; have : c = n := by omega
          rw [this] at hc; exact hBmem hc
      exact ih S i hS'

/-! ### Sieve definitions and correctness -/

def bb : ℕ := 2 ^ KK
def NN : ℕ := 628100
def geom (r M : Nat) : Nat := (r ^ M - 1) / (r - 1)
def multMask (p : Nat) : Nat :=
  if NN / p < 2 then 0 else (bb ^ p) ^ 2 * geom (bb ^ p) (NN / p - 1)
def smallPrimes : List Nat :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797]
def compMask : Nat := smallPrimes.foldl (fun acc p => acc ||| multMask p) 0
def piF (x : Nat) : Nat := (x - 1) - ((compMask % bb ^ (x + 1)) % (bb - 1))

lemma bb_def : bb = 2 ^ KK := rfl
lemma two_le_bb : 2 ≤ bb := by rw [bb_def]; calc 2 = 2^1 := rfl
                                                 _ ≤ 2^KK := Nat.pow_le_pow_right (by norm_num) KK_pos

lemma two_le_bbpow (p : ℕ) (hp : 1 ≤ p) : 2 ≤ bb ^ p := by
  calc 2 = 2^1 := rfl
    _ ≤ bb^1 := Nat.pow_le_pow_left two_le_bb 1
    _ ≤ bb^p := Nat.pow_le_pow_right (by have := two_le_bb; omega) hp

lemma term_eq (c : ℕ) : (2:ℕ) ^ (KK * c) = bb ^ c := by rw [bb_def, ← pow_mul]

lemma bbpow_pow (p e : ℕ) : (bb ^ p) ^ e = 2 ^ (KK * (p * e)) := by
  rw [bb_def, ← pow_mul, ← pow_mul]

/-- geometric sum -/
lemma gsum_mul (r M : ℕ) (hr : 1 ≤ r) :
    (r - 1) * (∑ i ∈ Finset.range M, r ^ i) = r ^ M - 1 := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have h1 : 1 ≤ r ^ n := Nat.one_le_pow _ _ (by omega)
    have h2 : r ^ n ≤ r ^ (n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (r - 1) * r ^ n = r ^ (n+1) - r ^ n := by
      rw [Nat.sub_mul, one_mul, pow_succ']
    omega

lemma geom_eq (r M : ℕ) (hr : 2 ≤ r) : geom r M = ∑ i ∈ Finset.range M, r ^ i := by
  unfold geom
  rw [← gsum_mul r M (by omega), Nat.mul_div_cancel_left _ (by omega : 0 < r - 1)]

/-- the set of multiples of `p` recorded in `multMask p`. -/
def multSet (p : ℕ) : Finset ℕ := (Finset.range (NN / p - 1)).image (fun i => p * (i + 2))

lemma multMask_eq (p : ℕ) (hp : 1 ≤ p) : multMask p = maskOf (multSet p) := by
  unfold multMask multSet maskOf
  by_cases hMc : NN / p < 2
  · simp only [hMc, if_true]
    have : NN / p - 1 = 0 := by omega
    rw [this]; simp
  · simp only [hMc, if_false]
    rw [geom_eq _ _ (two_le_bbpow p hp), Finset.mul_sum]
    rw [Finset.sum_image (by
      intro a _ b _ h
      have : p * (a + 2) = p * (b + 2) := h
      have := Nat.eq_of_mul_eq_mul_left (by omega) this; omega)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_add, bbpow_pow]
    congr 1; ring

lemma maskOf_lor (A B : Finset ℕ) : maskOf A ||| maskOf B = maskOf (A ∪ B) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_lor, testBit_maskOf, testBit_maskOf, testBit_maskOf]
  rw [← Bool.decide_or]
  apply decide_eq_decide.mpr
  simp only [Finset.mem_union]
  constructor
  · rintro (⟨c, hc, hi⟩ | ⟨c, hc, hi⟩)
    · exact ⟨c, Or.inl hc, hi⟩
    · exact ⟨c, Or.inr hc, hi⟩
  · rintro ⟨c, (hc | hc), hi⟩
    · exact Or.inl ⟨c, hc, hi⟩
    · exact Or.inr ⟨c, hc, hi⟩

lemma mem_foldl_union (l : List ℕ) (s0 : Finset ℕ) (c : ℕ) :
    c ∈ l.foldl (fun s p => s ∪ multSet p) s0 ↔ c ∈ s0 ∨ ∃ p ∈ l, c ∈ multSet p := by
  induction l generalizing s0 with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih]
    simp only [Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((h | h) | ⟨q, hq, hc⟩)
      · exact Or.inl h
      · exact Or.inr ⟨p, Or.inl rfl, h⟩
      · exact Or.inr ⟨q, Or.inr hq, hc⟩
    · rintro (h | ⟨q, (rfl | hq), hc⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hc)
      · exact Or.inr ⟨q, hq, hc⟩

def compSet : Finset ℕ := smallPrimes.foldl (fun s p => s ∪ multSet p) ∅

lemma foldl_lor_eq (l : List ℕ) (s0 : Finset ℕ) (hl : ∀ p ∈ l, 1 ≤ p) :
    l.foldl (fun acc p => acc ||| multMask p) (maskOf s0)
      = maskOf (l.foldl (fun s p => s ∪ multSet p) s0) := by
  induction l generalizing s0 with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    have hp1 : 1 ≤ p := hl p (List.mem_cons_self ..)
    rw [multMask_eq p hp1, maskOf_lor]
    exact ih (s0 ∪ multSet p) (fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-! ### A cheap (low-memory) primality test for `decide`. -/

def noFactorLoop (n : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | d, fuel+1 => if d*d > n then true
                 else if n % d == 0 then false
                 else noFactorLoop n (d+1) fuel

theorem loop_spec (n : Nat) : ∀ fuel d,
    noFactorLoop n d fuel = true ↔ ∀ e, d ≤ e → e < d + fuel → e*e ≤ n → ¬ e ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d; simp [noFactorLoop]; omega
  | succ f ih =>
    intro d
    rw [noFactorLoop]
    split_ifs with hdd hmod
    · constructor
      · intro _ e hde _ hee
        have : d*d ≤ e*e := Nat.mul_le_mul hde hde
        omega
      · intro _; rfl
    · simp only [false_iff, not_forall]
      have hd : d ∣ n := Nat.dvd_of_mod_eq_zero (by simpa using hmod)
      exact ⟨d, le_refl d, by omega, by omega, fun h => h hd⟩
    · rw [ih (d+1)]
      constructor
      · intro h e hde hef hee hen
        rcases Nat.lt_or_ge d e with hlt | hge
        · exact h e (by omega) (by omega) hee hen
        · have hed : e = d := by omega
          subst hed
          rw [Nat.dvd_iff_mod_eq_zero] at hen
          simp [hen] at hmod
      · intro h e hde hef hee hen
        exact h e (by omega) (by omega) hee hen

def isPrimeB (n : Nat) : Bool := decide (2 ≤ n) && noFactorLoop n 2 n

theorem isPrimeB_iff (n : Nat) : isPrimeB n = true ↔ Nat.Prime n := by
  rw [Nat.prime_def_le_sqrt, isPrimeB, Bool.and_eq_true, decide_eq_true_iff, loop_spec]
  apply and_congr_right
  intro h2
  constructor
  · intro h m hm2 hmsqrt hdvd
    have hmn : m * m ≤ n := Nat.le_sqrt.mp hmsqrt
    have hmm : m ≤ m * m := Nat.le_mul_of_pos_right m (by omega)
    exact h m hm2 (by omega) hmn hdvd
  · intro h e he2 _ hee hdvd
    exact h e he2 (Nat.le_sqrt.mpr hee) hdvd

set_option maxRecDepth 100000 in
lemma smallPrimes_pos : ∀ p ∈ smallPrimes, 1 ≤ p := by decide

set_option maxRecDepth 100000 in
lemma smallPrimes_prime : ∀ p ∈ smallPrimes, Nat.Prime p := by
  have aux : ∀ p ∈ smallPrimes, isPrimeB p = true := by decide
  intro p hp
  exact (isPrimeB_iff p).mp (aux p hp)

set_option maxRecDepth 100000 in
lemma smallPrimes_complete : ∀ q ≤ 792, Nat.Prime q → q ∈ smallPrimes := by
  have aux : ∀ q ≤ 792, isPrimeB q = true → q ∈ smallPrimes := by decide
  intro q hq hp
  exact aux q hq ((isPrimeB_iff q).mpr hp)

lemma compMask_eq : compMask = maskOf compSet := by
  unfold compMask compSet
  have h := foldl_lor_eq smallPrimes ∅ smallPrimes_pos
  rwa [maskOf_empty] at h

def compositeSet : Finset ℕ := (Finset.Icc 2 NN).filter (fun c => ¬ Nat.Prime c)

lemma mem_multSet (p c : ℕ) : c ∈ multSet p ↔ ∃ j, 2 ≤ j ∧ j ≤ NN / p ∧ p * j = c := by
  unfold multSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_range] at hi
    exact ⟨i + 2, by omega, by omega, rfl⟩
  · rintro ⟨j, hj2, hjN, rfl⟩
    exact ⟨j - 2, by rw [Finset.mem_range]; omega, by congr 1; omega⟩

lemma compSet_eq : compSet = compositeSet := by
  apply Finset.ext
  intro c
  rw [compSet, mem_foldl_union]
  simp only [Finset.notMem_empty, false_or, compositeSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨p, hp, hc⟩
    rw [mem_multSet] at hc
    obtain ⟨j, hj2, hjN, rfl⟩ := hc
    have hpp := smallPrimes_prime p hp
    have hp2 := hpp.two_le
    have hle : p * j ≤ NN := by
      calc p * j ≤ p * (NN / p) := Nat.mul_le_mul_left p hjN
        _ ≤ NN := Nat.mul_div_le NN p
    refine ⟨⟨by nlinarith, hle⟩, ?_⟩
    exact Nat.not_prime_mul (by omega) (by omega)
  · rintro ⟨⟨h2, hN⟩, hp⟩
    set p := c.minFac with hpdef
    have hc1 : c ≠ 1 := by omega
    have hpp : Nat.Prime p := Nat.minFac_prime hc1
    have hpdvd : p ∣ c := Nat.minFac_dvd c
    have hdiv : p ≤ c / p := Nat.minFac_le_div (by omega) hp
    have hcancel : p * (c / p) = c := Nat.mul_div_cancel' hpdvd
    have hpsq : p * p ≤ c := by
      calc p * p ≤ p * (c / p) := Nat.mul_le_mul_left p hdiv
        _ = c := hcancel
    have hNNval : NN = 628100 := rfl
    have hp792 : p ≤ 792 := by
      by_contra hcon
      have hsq : 793 * 793 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hpin : p ∈ smallPrimes := smallPrimes_complete p hp792 hpp
    refine ⟨p, hpin, ?_⟩
    rw [mem_multSet]
    refine ⟨c / p, ?_, ?_, hcancel⟩
    · -- 2 ≤ c / p
      rcases Nat.lt_or_ge (c / p) 2 with h | h
      · exfalso
        have hcp : c / p = 0 ∨ c / p = 1 := by omega
        rcases hcp with h0 | h1
        · rw [h0, mul_zero] at hcancel; omega
        · rw [h1, mul_one] at hcancel; rw [hcancel] at hpp; exact hp hpp
      · exact h
    · -- c / p ≤ NN / p
      rw [Nat.le_div_iff_mul_le (by have := hpp.two_le; omega)]
      rw [mul_comm, hcancel]; exact hN

lemma maskOf_mod (S : Finset ℕ) (x : ℕ) :
    maskOf S % bb ^ (x + 1) = maskOf (S.filter (· ≤ x)) := by
  have hpow : bb ^ (x + 1) = 2 ^ (KK * (x + 1)) := by rw [bb_def, ← pow_mul]
  have hsplit : maskOf S
      = maskOf (S.filter (· ≤ x)) + maskOf (S.filter (fun c => ¬ c ≤ x)) := by
    unfold maskOf
    rw [← Finset.sum_filter_add_sum_filter_not S (· ≤ x) (fun c => 2 ^ (KK * c))]
  have hlt : maskOf (S.filter (· ≤ x)) < bb ^ (x + 1) := by
    rw [hpow]; apply maskOf_lt
    intro c hc; rw [Finset.mem_filter] at hc; omega
  have hdvd : bb ^ (x + 1) ∣ maskOf (S.filter (fun c => ¬ c ≤ x)) := by
    unfold maskOf; apply Finset.dvd_sum
    intro c hc; rw [Finset.mem_filter] at hc
    rw [hpow]; apply pow_dvd_pow
    exact Nat.mul_le_mul_left KK (by omega)
  obtain ⟨k, hk⟩ := hdvd
  rw [hsplit, hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

lemma maskOf_modEq_card (S : Finset ℕ) : maskOf S ≡ S.card [MOD bb - 1] := by
  have hbb : bb ≡ 1 [MOD bb - 1] := by
    have h1 : (1:ℕ) ≤ bb := by have := two_le_bb; omega
    exact ((Nat.modEq_iff_dvd' h1).mpr (dvd_refl _)).symm
  unfold maskOf
  induction S using Finset.induction with
  | empty => simp [Nat.ModEq.refl]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, term_eq]
    calc bb ^ a + ∑ c ∈ s, 2 ^ (KK * c)
        ≡ 1 + s.card [MOD bb - 1] := Nat.ModEq.add ((hbb.pow a).trans (by rw [one_pow])) ih
      _ = s.card + 1 := by ring

lemma maskOf_mod_count (S : Finset ℕ) (h : S.card < bb - 1) :
    maskOf S % (bb - 1) = S.card := by
  have := maskOf_modEq_card S
  unfold Nat.ModEq at this
  rw [this, Nat.mod_eq_of_lt h]

lemma compositeSet_filter (x : ℕ) (hx : x ≤ NN) :
    compositeSet.filter (· ≤ x) = (Finset.Icc 2 x).filter (fun c => ¬ Nat.Prime c) := by
  ext c
  simp only [compositeSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h2, hN⟩, hp⟩, hcx⟩; exact ⟨⟨h2, hcx⟩, hp⟩
  · rintro ⟨⟨h2, hcx⟩, hp⟩; exact ⟨⟨⟨h2, by omega⟩, hp⟩, hcx⟩

lemma primeCounting_eq_card (x : ℕ) :
    Nat.primeCounting x = ((Finset.Icc 2 x).filter Nat.Prime).card := by
  have h1 : Nat.primeCounting x = Nat.count Nat.Prime (x + 1) := rfl
  rw [h1, Nat.count_eq_card_filter_range]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hc, hp⟩; exact ⟨⟨hp.two_le, by omega⟩, hp⟩
  · rintro ⟨⟨h2, hcx⟩, hp⟩; exact ⟨by omega, hp⟩

lemma piF_eq (x : ℕ) (hx : x ≤ NN) : piF x = Nat.primeCounting x := by
  rw [primeCounting_eq_card]
  unfold piF
  rw [compMask_eq, compSet_eq, maskOf_mod, compositeSet_filter x hx]
  rw [maskOf_mod_count]
  · have hpart := Finset.card_filter_add_card_filter_not (s := Finset.Icc 2 x) Nat.Prime
    rw [Nat.card_Icc] at hpart
    omega
  · have hbd : ((Finset.Icc 2 x).filter (fun c => ¬ Nat.Prime c)).card ≤ x + 1 - 2 := by
      calc ((Finset.Icc 2 x).filter (fun c => ¬ Nat.Prime c)).card
          ≤ (Finset.Icc 2 x).card := Finset.card_filter_le _ _
        _ = x + 1 - 2 := Nat.card_Icc 2 x
    have hb1 : bb - 1 = 1048575 := by norm_num [bb, KK]
    have hNN : NN = 628100 := rfl
    omega

end Sv

namespace Disp
open Nat Finset

def convCount (A B : List ℕ) (N : ℕ) : ℕ :=
  A.foldl (fun acc a => acc + B.countP (fun b => a + b == N)) 0

theorem foldl_add_init (g : ℕ → ℕ) (s : ℕ) (L : List ℕ) :
    L.foldl (fun acc a => acc + g a) s = s + L.foldl (fun acc a => acc + g a) 0 := by
  induction L generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (s + g x), ih (0 + g x)]
    omega

theorem convCount_append (A A' B : List ℕ) (N : ℕ) :
    convCount (A ++ A') B N = convCount A B N + convCount A' B N := by
  unfold convCount
  rw [List.foldl_append, foldl_add_init]

theorem sum_Icc_eq_list (M : ℕ) (g : ℕ → ℕ) :
    ∑ x ∈ Finset.Icc 1 M, g x = ((List.range' 1 M).map g).sum := by
  have hval : (Finset.Icc 1 M).val = ↑(List.range' 1 M) := by
    rw [Nat.Icc_eq_range']; simp
  rw [Finset.sum, hval]; simp [Multiset.sum_coe]

theorem indicator_sum_eq_countP (l : List ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (l.map (fun m => if Q m then 1 else 0)).sum = l.countP (fun m => decide (Q m)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
      split <;> simp_all <;> omega

theorem bridge (M1 M2 N : ℕ) (F G : ℕ → ℕ) :
    ((Finset.Icc 1 M1 ×ˢ Finset.Icc 1 M2).filter (fun p => F p.1 + G p.2 = N)).card
      = convCount ((List.range' 1 M1).map F) ((List.range' 1 M2).map G) N := by
  rw [Finset.card_filter, Finset.sum_product]
  have e1 : ∀ k : ℕ, (∑ m ∈ Finset.Icc 1 M2, if F k + G m = N then 1 else 0)
      = (List.range' 1 M2).countP (fun m => decide (F k + G m = N)) := by
    intro k
    rw [sum_Icc_eq_list M2 (fun m => if F k + G m = N then 1 else 0), indicator_sum_eq_countP]
  rw [Finset.sum_congr rfl (fun k _ => e1 k), sum_Icc_eq_list M1]
  unfold convCount
  rw [List.sum_eq_foldl, List.foldl_map, List.foldl_map]
  congr 1
  funext acc k
  congr 1
  rw [List.countP_map]
  apply List.countP_congr
  intro m _
  simp only [Function.comp]
  rw [Bool.beq_eq_decide_eq]

/-! ### oblong / triangular checkpoints -/

def oblong (k : Nat) := k*(k+1)
def tri (m : Nat) := m*(m+1)/2

theorem oblong_zero : oblong 0 = 0 := rfl
theorem tri_zero : tri 0 = 0 := rfl

theorem oblong_mono : ∀ k, oblong k ≤ oblong (k+1) := by
  intro k; unfold oblong; nlinarith
theorem tri_mono : ∀ m, tri m ≤ tri (m+1) := by
  intro m; unfold tri; apply Nat.div_le_div_right; nlinarith

theorem oblong_le_of_le {j k : ℕ} (h : j ≤ k) : oblong j ≤ oblong k := by
  unfold oblong; exact Nat.mul_le_mul h (by omega)
theorem tri_le_of_le {j k : ℕ} (h : j ≤ k) : tri j ≤ tri k := by
  unfold tri; apply Nat.div_le_div_right; exact Nat.mul_le_mul h (by omega)


def Alit : List ℕ := [1, 3, 5, 8, 10, 13, 16, 20, 24, 29, 32, 36, 42, 46, 52, 58, 62, 68, 75, 81, 89, 96, 101, 109, 118, 126, 133, 141, 150, 158, 167, 177, 187, 195, 205, 217, 222, 234, 246, 259, 268, 279, 290, 299, 312, 326, 335, 349, 363, 373, 383, 402, 416, 428, 440, 452, 464, 480, 495, 511, 526, 539, 557, 573, 589, 601, 617, 634, 649, 665, 683, 697, 712, 732, 750, 769, 783, 802, 822, 840, 856, 876, 896, 914, 932, 947, 971, 990, 1008, 1027, 1048, 1066, 1090, 1110, 1130, 1152, 1177, 1197, 1220, 1240, 1263, 1285, 1306, 1327, 1348, 1370, 1392, 1409, 1438, 1459, 1483, 1512, 1532, 1560, 1585, 1605, 1632, 1656, 1675, 1700, 1729, 1754, 1779, 1810, 1837, 1863, 1889, 1912, 1938, 1964, 1987, 2018, 2043, 2073, 2103, 2129, 2150, 2175, 2206, 2234, 2264, 2293, 2321, 2348, 2380, 2406, 2440, 2471, 2502, 2530, 2560, 2593, 2620, 2654, 2691, 2717, 2743, 2773, 2804, 2836, 2866, 2900, 2935, 2966, 2993, 3022, 3060, 3088, 3130, 3161, 3196, 3225, 3254, 3288, 3319, 3355, 3389, 3423, 3456, 3497, 3531, 3565, 3607, 3642, 3676, 3715, 3749, 3783, 3814, 3850, 3887, 3929, 3963, 4000, 4034, 4068, 4107, 4148, 4183, 4223, 4256, 4291, 4333, 4372, 4416, 4456, 4500, 4531, 4567, 4612, 4649, 4687, 4724, 4761, 4798, 4843, 4878, 4922, 4960, 5001, 5043, 5086, 5129, 5172, 5208, 5248, 5295, 5338, 5376, 5421, 5459, 5505, 5548, 5590, 5630, 5678, 5718, 5766, 5816, 5860, 5905, 5948, 5995, 6043, 6082, 6125, 6164, 6213, 6256, 6297, 6338, 6393, 6434, 6474, 6521, 6572, 6613, 6659, 6707, 6759, 6800, 6848, 6892, 6933, 6985, 7034, 7087, 7137, 7181, 7232, 7279, 7325, 7376, 7424, 7474, 7520, 7568, 7621, 7670, 7718, 7766, 7814, 7870, 7922, 7971, 8028, 8080, 8126, 8175, 8224, 8274, 8326, 8374, 8429, 8479, 8535, 8577, 8631, 8688, 8745, 8793, 8848, 8896, 8957, 9016, 9064, 9119, 9173, 9232, 9284, 9340, 9391, 9437, 9495, 9550, 9604, 9658, 9714, 9777, 9834, 9879, 9934, 9989, 10045, 10100, 10157, 10219, 10267, 10326, 10386, 10445, 10492, 10553, 10611, 10666, 10732, 10780, 10834, 10894, 10960, 11012, 11070, 11135, 11187, 11246, 11306, 11364, 11430, 11491, 11551, 11611, 11671, 11730, 11791, 11853, 11907, 11970, 12035, 12097, 12157, 12223, 12275, 12336, 12402, 12464, 12523, 12582, 12651, 12717, 12780, 12842, 12907, 12968, 13029, 13097, 13162, 13223, 13282, 13344, 13406, 13467, 13534, 13595, 13665, 13722, 13795, 13862, 13927, 14000, 14065, 14128, 14191, 14260, 14327, 14388, 14453, 14522, 14585, 14648, 14716, 14785, 14852, 14915, 14981, 15053, 15111, 15178, 15246, 15316, 15375, 15440, 15509, 15584, 15651, 15723, 15785, 15860, 15927, 15989, 16073, 16132, 16202, 16277, 16355, 16418, 16482, 16561, 16636, 16700, 16775, 16855, 16920, 16996, 17062, 17139, 17204, 17273, 17352, 17428, 17502, 17568, 17640, 17711, 17785, 17862, 17930, 18005, 18073, 18152, 18221, 18290, 18363, 18442, 18517, 18588, 18669, 18743, 18828, 18902, 18980, 19044, 19118, 19202, 19267, 19337, 19416, 19488, 19566, 19650, 19724, 19802, 19880, 19955, 20032, 20111, 20182, 20260, 20347, 20430, 20512, 20588, 20659, 20731, 20808, 20885, 20955, 21027, 21110, 21190, 21268, 21351, 21435, 21511, 21593, 21672, 21752, 21832, 21920, 22004, 22077, 22163, 22243, 22316, 22399, 22486, 22566, 22642, 22724, 22803, 22884, 22962, 23042, 23125, 23202, 23289, 23373, 23473, 23549, 23633, 23719, 23801, 23888, 23961, 24046, 24134, 24218, 24299, 24380, 24463, 24553, 24643, 24719, 24807, 24897, 24977, 25051, 25129, 25222, 25313, 25395, 25481, 25559, 25645, 25726, 25811, 25894, 25980, 26069, 26160, 26243, 26335, 26429, 26517, 26609, 26691, 26780, 26864, 26944, 27038, 27131, 27217, 27307, 27399, 27493, 27591, 27682, 27773, 27861, 27946, 28045, 28135, 28228, 28318, 28409, 28498, 28593, 28683, 28769, 28861, 28954, 29043, 29136, 29220, 29315, 29407, 29499, 29592, 29682, 29776, 29873, 29965, 30058, 30151, 30245, 30345, 30442, 30523, 30615, 30718, 30798, 30888, 30980, 31077, 31174, 31272, 31373, 31458, 31545, 31633, 31723, 31814, 31920, 32015, 32114, 32205, 32304, 32394, 32483, 32584, 32683, 32783, 32875, 32963, 33067, 33170, 33273, 33382, 33475, 33569, 33662, 33764, 33864, 33954, 34049, 34140, 34232, 34332, 34425, 34529, 34630, 34728, 34830, 34920, 35028, 35131, 35228, 35331, 35433, 35531, 35630, 35736, 35832, 35928, 36031, 36132, 36237, 36345, 36451, 36560, 36665, 36764, 36857, 36958, 37062, 37168, 37284, 37383, 37475, 37576, 37674, 37790, 37892, 37978, 38079, 38184, 38292, 38390, 38485, 38590, 38681, 38791, 38901, 38996, 39109, 39217, 39331, 39436, 39541, 39651, 39766, 39862, 39974, 40078, 40184, 40294, 40390, 40486, 40600, 40711, 40822, 40931, 41031, 41143, 41258, 41364, 41470, 41583, 41690, 41787, 41892, 42006, 42114, 42221, 42331, 42441, 42549, 42658, 42758, 42885, 42993, 43101, 43217, 43321, 43429, 43548, 43661, 43769, 43882, 43985, 44096, 44203, 44317, 44425, 44538, 44643, 44755, 44876, 44972, 45080, 45189, 45311, 45423, 45532, 45648, 45755, 45868, 45976, 46101, 46202, 46322, 46428, 46543, 46647, 46767, 46886, 46998, 47116, 47229, 47350, 47459, 47579, 47694, 47807, 47920, 48043, 48166, 48286, 48392, 48499, 48628, 48746, 48858, 48972, 49086, 49207, 49326, 49439, 49560, 49674, 49794, 49911, 50031, 50151, 50263, 50391, 50512, 50619, 50741, 50853, 50980, 51083]
def Blit : List ℕ := [0, 2, 3, 4, 6, 8, 9, 11, 14, 16, 18, 21, 24, 27, 30, 32, 36, 39, 42, 46, 50, 54, 58, 62, 66, 70, 74, 79, 84, 90, 94, 99, 102, 108, 114, 121, 126, 131, 137, 141, 149, 154, 160, 166, 174, 180, 188, 193, 200, 205, 216, 220, 226, 235, 242, 250, 259, 267, 274, 281, 290, 297, 305, 312, 324, 329, 338, 347, 358, 367, 374, 381, 393, 403, 413, 422, 431, 440, 446, 457, 467, 478, 487, 499, 510, 522, 531, 541, 552, 564, 574, 587, 596, 607, 617, 629, 640, 650, 661, 675, 686, 697, 708, 721, 734, 747, 757, 775, 783, 796, 808, 823, 836, 847, 859, 873, 887, 903, 914, 928, 938, 950, 968, 982, 994, 1007, 1022, 1035, 1049, 1061, 1076, 1093, 1108, 1124, 1137, 1152, 1170, 1184, 1199, 1217, 1231, 1246, 1262, 1277, 1290, 1308, 1322, 1336, 1354, 1369, 1383, 1398, 1411, 1430, 1446, 1463, 1480, 1500, 1518, 1532, 1553, 1570, 1585, 1602, 1619, 1637, 1654, 1669, 1683, 1701, 1720, 1742, 1757, 1776, 1799, 1816, 1837, 1857, 1875, 1891, 1908, 1926, 1943, 1961, 1981, 2000, 2020, 2039, 2057, 2080, 2101, 2122, 2137, 2152, 2169, 2188, 2213, 2230, 2250, 2271, 2293, 2313, 2330, 2352, 2373, 2394, 2416, 2437, 2460, 2484, 2502, 2524, 2547, 2565, 2591, 2609, 2631, 2654, 2679, 2700, 2721, 2738, 2759, 2781, 2803, 2825, 2847, 2868, 2893, 2915, 2939, 2963, 2984, 3004, 3022, 3052, 3074, 3095, 3124, 3147, 3169, 3195, 3217, 3238, 3259, 3282, 3302, 3330, 3352, 3380, 3401, 3424, 3447, 3476, 3503, 3525, 3553, 3578, 3607, 3632, 3653, 3679, 3707, 3731, 3754, 3780, 3801, 3829, 3854, 3879, 3907, 3935, 3960, 3990, 4009, 4034, 4059, 4086, 4112, 4140, 4166, 4196, 4221, 4241, 4266, 4295, 4324, 4352, 4381, 4411, 4444, 4473, 4502, 4522, 4549, 4572, 4604, 4632, 4660, 4687, 4714, 4739, 4765, 4794, 4822, 4849, 4873, 4905, 4935, 4963, 4990, 5022, 5051, 5081, 5110, 5141, 5172, 5197, 5224, 5254, 5289, 5319, 5349, 5375, 5406, 5437, 5465, 5497, 5521, 5557, 5585, 5615, 5641, 5679, 5709, 5741, 5776, 5811, 5836, 5870, 5903, 5933, 5962, 5996, 6033, 6060, 6091, 6120, 6152, 6179, 6214, 6243, 6273, 6304, 6333, 6369, 6407, 6434, 6462, 6492, 6526, 6563, 6595, 6623, 6656, 6691, 6727, 6762, 6794, 6822, 6855, 6885, 6914, 6949, 6985, 7016, 7053, 7091, 7128, 7164, 7197, 7232, 7260, 7295, 7330, 7363, 7399, 7434, 7472, 7503, 7537, 7570, 7606, 7649, 7681, 7713, 7746, 7782, 7813, 7852, 7885, 7926, 7965, 8000, 8038, 8078, 8109, 8145, 8178, 8214, 8250, 8283, 8321, 8357, 8393, 8429, 8464, 8502, 8542, 8569, 8605, 8644, 8686, 8726, 8763, 8798, 8835, 8869, 8908, 8949, 8991, 9032, 9065, 9102, 9143, 9184, 9222, 9261, 9299, 9339, 9373, 9410, 9443, 9482, 9526, 9563, 9600, 9641, 9675, 9716, 9759, 9804, 9841, 9872, 9911, 9952, 9989, 10031, 10073, 10108, 10151, 10193, 10229, 10264, 10306, 10344, 10388, 10430, 10465, 10508, 10549, 10586, 10627, 10668, 10708, 10752, 10790, 10828, 10868, 10909, 10958, 10995, 11033, 11076, 11121, 11159, 11200, 11243, 11282, 11326, 11367, 11411, 11458, 11501, 11543, 11583, 11630, 11671, 11712, 11756, 11800, 11843, 11885, 11920, 11969, 12007, 12055, 12100, 12146, 12186, 12232, 12271, 12314, 12355, 12403, 12448, 12488, 12535, 12572, 12617, 12665, 12714, 12761, 12805, 12846, 12896, 12934, 12978, 13022, 13071, 13117, 13166, 13210, 13252, 13289, 13337, 13378, 13422, 13466, 13516, 13559, 13603, 13651, 13693, 13738, 13789, 13838, 13886, 13930, 13979, 14030, 14076, 14123, 14168, 14214, 14260, 14307, 14357, 14395, 14441, 14493, 14535, 14582, 14623, 14677, 14721, 14770, 14817, 14862, 14909, 14955, 15005, 15057, 15094, 15143, 15185, 15233, 15287, 15332, 15373, 15418, 15465, 15517, 15570, 15615, 15665, 15716, 15765, 15812, 15864, 15912, 15952, 16002, 16062, 16108, 16150, 16202, 16257, 16313, 16366, 16410, 16451, 16503, 16558, 16604, 16656, 16706, 16757, 16810, 16869, 16915, 16970, 17014, 17064, 17115, 17172, 17216, 17267, 17318, 17369, 17424, 17475, 17525, 17573, 17625, 17678, 17726, 17778, 17832, 17884, 17932, 17988, 18035, 18084, 18141, 18188, 18236, 18289, 18341, 18391, 18446, 18502, 18552, 18611, 18664, 18716, 18774, 18834, 18887, 18940, 18992, 19036, 19090, 19145, 19202, 19249, 19299, 19349, 19406, 19454, 19508, 19563, 19624, 19675, 19729, 19787, 19835, 19899, 19947, 20003, 20057, 20113, 20167, 20220, 20271, 20330, 20389, 20452, 20509, 20563, 20618, 20669, 20715, 20769, 20827, 20880, 20928, 20983, 21032, 21093, 21148, 21202, 21258, 21314, 21375, 21435, 21488, 21542, 21605, 21659, 21716, 21773, 21830, 21890, 21953, 22011, 22064, 22114, 22179, 22235, 22288, 22347, 22400, 22466, 22521, 22577, 22630, 22685, 22749, 22801, 22858, 22914, 22970, 23024, 23080, 23141, 23197, 23259, 23319, 23375, 23442, 23508, 23564, 23626, 23683, 23743, 23801, 23862, 23918, 23972, 24031, 24093, 24156, 24213, 24270, 24330, 24384, 24443, 24504, 24567, 24631, 24693, 24747, 24809, 24871, 24930, 24986, 25039, 25093, 25159, 25218, 25286, 25346, 25401, 25463, 25516, 25579, 25639, 25696, 25762, 25814, 25877, 25932, 25990, 26054, 26120, 26178, 26242, 26308, 26373, 26438, 26500, 26566, 26630, 26682, 26747, 26805, 26869, 26924, 26990, 27051, 27122, 27185, 27245, 27307, 27373, 27442, 27506, 27576, 27644, 27703, 27768, 27833, 27894, 27951, 28026, 28092, 28150, 28219, 28286, 28343, 28412, 28478, 28542, 28607, 28665, 28729, 28792, 28858, 28922, 28991, 29056, 29118, 29178, 29241, 29307, 29376, 29435, 29502, 29568, 29630, 29701, 29770, 29831, 29896, 29964, 30024, 30098, 30164, 30232, 30299, 30369, 30436, 30496, 30555, 30623, 30694, 30755, 30810, 30877, 30949, 31011, 31079, 31147, 31215, 31284, 31356, 31421, 31483, 31542, 31599, 31664, 31733, 31801, 31864, 31943, 32009, 32078, 32141, 32207, 32280, 32345, 32412, 32473, 32542, 32613, 32682, 32752, 32826, 32883, 32949, 33016, 33089, 33163, 33230, 33308, 33385, 33449, 33522, 33585, 33653, 33722, 33794, 33864, 33928, 33988, 34057, 34125, 34200, 34257, 34328, 34389, 34463, 34537, 34610, 34681, 34753, 34826, 34885, 34956, 35031, 35101, 35169, 35242, 35320, 35389, 35459, 35529, 35593, 35672, 35746, 35819, 35881, 35950, 36025, 36086, 36172, 36243, 36316, 36394, 36470, 36541, 36625, 36694, 36764, 36825, 36894, 36971, 37047, 37118, 37197, 37278, 37355, 37417, 37483, 37552, 37617, 37694, 37773, 37851, 37918, 37979, 38053, 38129, 38196, 38278, 38343, 38418, 38483, 38555, 38620, 38686, 38769, 38853, 38925, 38987, 39069, 39151, 39220, 39304, 39380, 39453, 39523, 39604, 39686, 39765, 39829, 39907, 39983, 40060, 40135, 40212, 40288, 40363, 40422, 40494, 40570, 40652, 40731, 40808, 40885, 40955, 41031, 41107, 41191, 41273, 41343, 41418, 41497, 41579, 41658, 41724, 41795, 41871, 41957, 42029, 42106, 42181, 42251, 42334, 42413, 42478, 42562, 42640, 42707, 42794, 42885, 42956, 43037, 43114, 43194, 43276, 43350, 43419, 43507, 43592, 43667, 43740, 43817, 43901, 43972, 44055, 44134, 44203, 44279, 44371, 44441, 44521, 44592, 44668, 44753, 44835, 44908, 44980, 45058, 45136, 45214, 45298, 45379, 45461, 45535, 45618, 45700, 45765, 45857, 45928, 46004, 46093, 46177, 46241, 46329, 46409, 46489, 46566, 46636, 46720, 46801, 46891, 46972, 47060, 47137, 47212, 47296, 47379, 47458, 47538, 47620, 47708, 47785, 47872, 47948, 48037, 48123, 48215, 48291, 48368, 48445, 48522, 48613, 48694, 48778, 48859, 48946, 49020, 49101, 49185, 49268, 49352, 49437, 49520, 49599, 49684, 49767, 49857, 49938, 50022, 50104, 50184, 50268, 50360, 50449, 50525, 50607, 50695, 50775, 50850, 50940, 51022, 51098]

set_option maxRecDepth 100000
set_option exponentiation.threshold 20000000
set_option maxHeartbeats 4000000000

theorem pcA1 : (List.range' 1 200).map (fun k => Sv.piF (k*(k+1))) = [1, 3, 5, 8, 10, 13, 16, 20, 24, 29, 32, 36, 42, 46, 52, 58, 62, 68, 75, 81, 89, 96, 101, 109, 118, 126, 133, 141, 150, 158, 167, 177, 187, 195, 205, 217, 222, 234, 246, 259, 268, 279, 290, 299, 312, 326, 335, 349, 363, 373, 383, 402, 416, 428, 440, 452, 464, 480, 495, 511, 526, 539, 557, 573, 589, 601, 617, 634, 649, 665, 683, 697, 712, 732, 750, 769, 783, 802, 822, 840, 856, 876, 896, 914, 932, 947, 971, 990, 1008, 1027, 1048, 1066, 1090, 1110, 1130, 1152, 1177, 1197, 1220, 1240, 1263, 1285, 1306, 1327, 1348, 1370, 1392, 1409, 1438, 1459, 1483, 1512, 1532, 1560, 1585, 1605, 1632, 1656, 1675, 1700, 1729, 1754, 1779, 1810, 1837, 1863, 1889, 1912, 1938, 1964, 1987, 2018, 2043, 2073, 2103, 2129, 2150, 2175, 2206, 2234, 2264, 2293, 2321, 2348, 2380, 2406, 2440, 2471, 2502, 2530, 2560, 2593, 2620, 2654, 2691, 2717, 2743, 2773, 2804, 2836, 2866, 2900, 2935, 2966, 2993, 3022, 3060, 3088, 3130, 3161, 3196, 3225, 3254, 3288, 3319, 3355, 3389, 3423, 3456, 3497, 3531, 3565, 3607, 3642, 3676, 3715, 3749, 3783, 3814, 3850, 3887, 3929, 3963, 4000, 4034, 4068, 4107, 4148, 4183, 4223] := by decide

theorem pcA2 : (List.range' 201 200).map (fun k => Sv.piF (k*(k+1))) = [4256, 4291, 4333, 4372, 4416, 4456, 4500, 4531, 4567, 4612, 4649, 4687, 4724, 4761, 4798, 4843, 4878, 4922, 4960, 5001, 5043, 5086, 5129, 5172, 5208, 5248, 5295, 5338, 5376, 5421, 5459, 5505, 5548, 5590, 5630, 5678, 5718, 5766, 5816, 5860, 5905, 5948, 5995, 6043, 6082, 6125, 6164, 6213, 6256, 6297, 6338, 6393, 6434, 6474, 6521, 6572, 6613, 6659, 6707, 6759, 6800, 6848, 6892, 6933, 6985, 7034, 7087, 7137, 7181, 7232, 7279, 7325, 7376, 7424, 7474, 7520, 7568, 7621, 7670, 7718, 7766, 7814, 7870, 7922, 7971, 8028, 8080, 8126, 8175, 8224, 8274, 8326, 8374, 8429, 8479, 8535, 8577, 8631, 8688, 8745, 8793, 8848, 8896, 8957, 9016, 9064, 9119, 9173, 9232, 9284, 9340, 9391, 9437, 9495, 9550, 9604, 9658, 9714, 9777, 9834, 9879, 9934, 9989, 10045, 10100, 10157, 10219, 10267, 10326, 10386, 10445, 10492, 10553, 10611, 10666, 10732, 10780, 10834, 10894, 10960, 11012, 11070, 11135, 11187, 11246, 11306, 11364, 11430, 11491, 11551, 11611, 11671, 11730, 11791, 11853, 11907, 11970, 12035, 12097, 12157, 12223, 12275, 12336, 12402, 12464, 12523, 12582, 12651, 12717, 12780, 12842, 12907, 12968, 13029, 13097, 13162, 13223, 13282, 13344, 13406, 13467, 13534, 13595, 13665, 13722, 13795, 13862, 13927, 14000, 14065, 14128, 14191, 14260, 14327, 14388, 14453, 14522, 14585, 14648, 14716] := by decide

theorem pcA3 : (List.range' 401 200).map (fun k => Sv.piF (k*(k+1))) = [14785, 14852, 14915, 14981, 15053, 15111, 15178, 15246, 15316, 15375, 15440, 15509, 15584, 15651, 15723, 15785, 15860, 15927, 15989, 16073, 16132, 16202, 16277, 16355, 16418, 16482, 16561, 16636, 16700, 16775, 16855, 16920, 16996, 17062, 17139, 17204, 17273, 17352, 17428, 17502, 17568, 17640, 17711, 17785, 17862, 17930, 18005, 18073, 18152, 18221, 18290, 18363, 18442, 18517, 18588, 18669, 18743, 18828, 18902, 18980, 19044, 19118, 19202, 19267, 19337, 19416, 19488, 19566, 19650, 19724, 19802, 19880, 19955, 20032, 20111, 20182, 20260, 20347, 20430, 20512, 20588, 20659, 20731, 20808, 20885, 20955, 21027, 21110, 21190, 21268, 21351, 21435, 21511, 21593, 21672, 21752, 21832, 21920, 22004, 22077, 22163, 22243, 22316, 22399, 22486, 22566, 22642, 22724, 22803, 22884, 22962, 23042, 23125, 23202, 23289, 23373, 23473, 23549, 23633, 23719, 23801, 23888, 23961, 24046, 24134, 24218, 24299, 24380, 24463, 24553, 24643, 24719, 24807, 24897, 24977, 25051, 25129, 25222, 25313, 25395, 25481, 25559, 25645, 25726, 25811, 25894, 25980, 26069, 26160, 26243, 26335, 26429, 26517, 26609, 26691, 26780, 26864, 26944, 27038, 27131, 27217, 27307, 27399, 27493, 27591, 27682, 27773, 27861, 27946, 28045, 28135, 28228, 28318, 28409, 28498, 28593, 28683, 28769, 28861, 28954, 29043, 29136, 29220, 29315, 29407, 29499, 29592, 29682, 29776, 29873, 29965, 30058, 30151, 30245, 30345, 30442, 30523, 30615, 30718, 30798] := by decide

theorem pcA4 : (List.range' 601 191).map (fun k => Sv.piF (k*(k+1))) = [30888, 30980, 31077, 31174, 31272, 31373, 31458, 31545, 31633, 31723, 31814, 31920, 32015, 32114, 32205, 32304, 32394, 32483, 32584, 32683, 32783, 32875, 32963, 33067, 33170, 33273, 33382, 33475, 33569, 33662, 33764, 33864, 33954, 34049, 34140, 34232, 34332, 34425, 34529, 34630, 34728, 34830, 34920, 35028, 35131, 35228, 35331, 35433, 35531, 35630, 35736, 35832, 35928, 36031, 36132, 36237, 36345, 36451, 36560, 36665, 36764, 36857, 36958, 37062, 37168, 37284, 37383, 37475, 37576, 37674, 37790, 37892, 37978, 38079, 38184, 38292, 38390, 38485, 38590, 38681, 38791, 38901, 38996, 39109, 39217, 39331, 39436, 39541, 39651, 39766, 39862, 39974, 40078, 40184, 40294, 40390, 40486, 40600, 40711, 40822, 40931, 41031, 41143, 41258, 41364, 41470, 41583, 41690, 41787, 41892, 42006, 42114, 42221, 42331, 42441, 42549, 42658, 42758, 42885, 42993, 43101, 43217, 43321, 43429, 43548, 43661, 43769, 43882, 43985, 44096, 44203, 44317, 44425, 44538, 44643, 44755, 44876, 44972, 45080, 45189, 45311, 45423, 45532, 45648, 45755, 45868, 45976, 46101, 46202, 46322, 46428, 46543, 46647, 46767, 46886, 46998, 47116, 47229, 47350, 47459, 47579, 47694, 47807, 47920, 48043, 48166, 48286, 48392, 48499, 48628, 48746, 48858, 48972, 49086, 49207, 49326, 49439, 49560, 49674, 49794, 49911, 50031, 50151, 50263, 50391, 50512, 50619, 50741, 50853, 50980, 51083] := by decide

theorem pcB1 : (List.range' 1 200).map (fun m => Sv.piF (m*(m+1)/2)) = [0, 2, 3, 4, 6, 8, 9, 11, 14, 16, 18, 21, 24, 27, 30, 32, 36, 39, 42, 46, 50, 54, 58, 62, 66, 70, 74, 79, 84, 90, 94, 99, 102, 108, 114, 121, 126, 131, 137, 141, 149, 154, 160, 166, 174, 180, 188, 193, 200, 205, 216, 220, 226, 235, 242, 250, 259, 267, 274, 281, 290, 297, 305, 312, 324, 329, 338, 347, 358, 367, 374, 381, 393, 403, 413, 422, 431, 440, 446, 457, 467, 478, 487, 499, 510, 522, 531, 541, 552, 564, 574, 587, 596, 607, 617, 629, 640, 650, 661, 675, 686, 697, 708, 721, 734, 747, 757, 775, 783, 796, 808, 823, 836, 847, 859, 873, 887, 903, 914, 928, 938, 950, 968, 982, 994, 1007, 1022, 1035, 1049, 1061, 1076, 1093, 1108, 1124, 1137, 1152, 1170, 1184, 1199, 1217, 1231, 1246, 1262, 1277, 1290, 1308, 1322, 1336, 1354, 1369, 1383, 1398, 1411, 1430, 1446, 1463, 1480, 1500, 1518, 1532, 1553, 1570, 1585, 1602, 1619, 1637, 1654, 1669, 1683, 1701, 1720, 1742, 1757, 1776, 1799, 1816, 1837, 1857, 1875, 1891, 1908, 1926, 1943, 1961, 1981, 2000, 2020, 2039, 2057, 2080, 2101, 2122, 2137, 2152, 2169, 2188, 2213, 2230, 2250, 2271] := by decide

theorem pcB2 : (List.range' 201 200).map (fun m => Sv.piF (m*(m+1)/2)) = [2293, 2313, 2330, 2352, 2373, 2394, 2416, 2437, 2460, 2484, 2502, 2524, 2547, 2565, 2591, 2609, 2631, 2654, 2679, 2700, 2721, 2738, 2759, 2781, 2803, 2825, 2847, 2868, 2893, 2915, 2939, 2963, 2984, 3004, 3022, 3052, 3074, 3095, 3124, 3147, 3169, 3195, 3217, 3238, 3259, 3282, 3302, 3330, 3352, 3380, 3401, 3424, 3447, 3476, 3503, 3525, 3553, 3578, 3607, 3632, 3653, 3679, 3707, 3731, 3754, 3780, 3801, 3829, 3854, 3879, 3907, 3935, 3960, 3990, 4009, 4034, 4059, 4086, 4112, 4140, 4166, 4196, 4221, 4241, 4266, 4295, 4324, 4352, 4381, 4411, 4444, 4473, 4502, 4522, 4549, 4572, 4604, 4632, 4660, 4687, 4714, 4739, 4765, 4794, 4822, 4849, 4873, 4905, 4935, 4963, 4990, 5022, 5051, 5081, 5110, 5141, 5172, 5197, 5224, 5254, 5289, 5319, 5349, 5375, 5406, 5437, 5465, 5497, 5521, 5557, 5585, 5615, 5641, 5679, 5709, 5741, 5776, 5811, 5836, 5870, 5903, 5933, 5962, 5996, 6033, 6060, 6091, 6120, 6152, 6179, 6214, 6243, 6273, 6304, 6333, 6369, 6407, 6434, 6462, 6492, 6526, 6563, 6595, 6623, 6656, 6691, 6727, 6762, 6794, 6822, 6855, 6885, 6914, 6949, 6985, 7016, 7053, 7091, 7128, 7164, 7197, 7232, 7260, 7295, 7330, 7363, 7399, 7434, 7472, 7503, 7537, 7570, 7606, 7649, 7681, 7713, 7746, 7782, 7813, 7852] := by decide

theorem pcB3 : (List.range' 401 200).map (fun m => Sv.piF (m*(m+1)/2)) = [7885, 7926, 7965, 8000, 8038, 8078, 8109, 8145, 8178, 8214, 8250, 8283, 8321, 8357, 8393, 8429, 8464, 8502, 8542, 8569, 8605, 8644, 8686, 8726, 8763, 8798, 8835, 8869, 8908, 8949, 8991, 9032, 9065, 9102, 9143, 9184, 9222, 9261, 9299, 9339, 9373, 9410, 9443, 9482, 9526, 9563, 9600, 9641, 9675, 9716, 9759, 9804, 9841, 9872, 9911, 9952, 9989, 10031, 10073, 10108, 10151, 10193, 10229, 10264, 10306, 10344, 10388, 10430, 10465, 10508, 10549, 10586, 10627, 10668, 10708, 10752, 10790, 10828, 10868, 10909, 10958, 10995, 11033, 11076, 11121, 11159, 11200, 11243, 11282, 11326, 11367, 11411, 11458, 11501, 11543, 11583, 11630, 11671, 11712, 11756, 11800, 11843, 11885, 11920, 11969, 12007, 12055, 12100, 12146, 12186, 12232, 12271, 12314, 12355, 12403, 12448, 12488, 12535, 12572, 12617, 12665, 12714, 12761, 12805, 12846, 12896, 12934, 12978, 13022, 13071, 13117, 13166, 13210, 13252, 13289, 13337, 13378, 13422, 13466, 13516, 13559, 13603, 13651, 13693, 13738, 13789, 13838, 13886, 13930, 13979, 14030, 14076, 14123, 14168, 14214, 14260, 14307, 14357, 14395, 14441, 14493, 14535, 14582, 14623, 14677, 14721, 14770, 14817, 14862, 14909, 14955, 15005, 15057, 15094, 15143, 15185, 15233, 15287, 15332, 15373, 15418, 15465, 15517, 15570, 15615, 15665, 15716, 15765, 15812, 15864, 15912, 15952, 16002, 16062, 16108, 16150, 16202, 16257, 16313, 16366] := by decide

theorem pcB4 : (List.range' 601 200).map (fun m => Sv.piF (m*(m+1)/2)) = [16410, 16451, 16503, 16558, 16604, 16656, 16706, 16757, 16810, 16869, 16915, 16970, 17014, 17064, 17115, 17172, 17216, 17267, 17318, 17369, 17424, 17475, 17525, 17573, 17625, 17678, 17726, 17778, 17832, 17884, 17932, 17988, 18035, 18084, 18141, 18188, 18236, 18289, 18341, 18391, 18446, 18502, 18552, 18611, 18664, 18716, 18774, 18834, 18887, 18940, 18992, 19036, 19090, 19145, 19202, 19249, 19299, 19349, 19406, 19454, 19508, 19563, 19624, 19675, 19729, 19787, 19835, 19899, 19947, 20003, 20057, 20113, 20167, 20220, 20271, 20330, 20389, 20452, 20509, 20563, 20618, 20669, 20715, 20769, 20827, 20880, 20928, 20983, 21032, 21093, 21148, 21202, 21258, 21314, 21375, 21435, 21488, 21542, 21605, 21659, 21716, 21773, 21830, 21890, 21953, 22011, 22064, 22114, 22179, 22235, 22288, 22347, 22400, 22466, 22521, 22577, 22630, 22685, 22749, 22801, 22858, 22914, 22970, 23024, 23080, 23141, 23197, 23259, 23319, 23375, 23442, 23508, 23564, 23626, 23683, 23743, 23801, 23862, 23918, 23972, 24031, 24093, 24156, 24213, 24270, 24330, 24384, 24443, 24504, 24567, 24631, 24693, 24747, 24809, 24871, 24930, 24986, 25039, 25093, 25159, 25218, 25286, 25346, 25401, 25463, 25516, 25579, 25639, 25696, 25762, 25814, 25877, 25932, 25990, 26054, 26120, 26178, 26242, 26308, 26373, 26438, 26500, 26566, 26630, 26682, 26747, 26805, 26869, 26924, 26990, 27051, 27122, 27185, 27245, 27307, 27373, 27442, 27506, 27576, 27644] := by decide

theorem pcB5 : (List.range' 801 200).map (fun m => Sv.piF (m*(m+1)/2)) = [27703, 27768, 27833, 27894, 27951, 28026, 28092, 28150, 28219, 28286, 28343, 28412, 28478, 28542, 28607, 28665, 28729, 28792, 28858, 28922, 28991, 29056, 29118, 29178, 29241, 29307, 29376, 29435, 29502, 29568, 29630, 29701, 29770, 29831, 29896, 29964, 30024, 30098, 30164, 30232, 30299, 30369, 30436, 30496, 30555, 30623, 30694, 30755, 30810, 30877, 30949, 31011, 31079, 31147, 31215, 31284, 31356, 31421, 31483, 31542, 31599, 31664, 31733, 31801, 31864, 31943, 32009, 32078, 32141, 32207, 32280, 32345, 32412, 32473, 32542, 32613, 32682, 32752, 32826, 32883, 32949, 33016, 33089, 33163, 33230, 33308, 33385, 33449, 33522, 33585, 33653, 33722, 33794, 33864, 33928, 33988, 34057, 34125, 34200, 34257, 34328, 34389, 34463, 34537, 34610, 34681, 34753, 34826, 34885, 34956, 35031, 35101, 35169, 35242, 35320, 35389, 35459, 35529, 35593, 35672, 35746, 35819, 35881, 35950, 36025, 36086, 36172, 36243, 36316, 36394, 36470, 36541, 36625, 36694, 36764, 36825, 36894, 36971, 37047, 37118, 37197, 37278, 37355, 37417, 37483, 37552, 37617, 37694, 37773, 37851, 37918, 37979, 38053, 38129, 38196, 38278, 38343, 38418, 38483, 38555, 38620, 38686, 38769, 38853, 38925, 38987, 39069, 39151, 39220, 39304, 39380, 39453, 39523, 39604, 39686, 39765, 39829, 39907, 39983, 40060, 40135, 40212, 40288, 40363, 40422, 40494, 40570, 40652, 40731, 40808, 40885, 40955, 41031, 41107, 41191, 41273, 41343, 41418, 41497, 41579] := by decide

theorem pcB6 : (List.range' 1001 119).map (fun m => Sv.piF (m*(m+1)/2)) = [41658, 41724, 41795, 41871, 41957, 42029, 42106, 42181, 42251, 42334, 42413, 42478, 42562, 42640, 42707, 42794, 42885, 42956, 43037, 43114, 43194, 43276, 43350, 43419, 43507, 43592, 43667, 43740, 43817, 43901, 43972, 44055, 44134, 44203, 44279, 44371, 44441, 44521, 44592, 44668, 44753, 44835, 44908, 44980, 45058, 45136, 45214, 45298, 45379, 45461, 45535, 45618, 45700, 45765, 45857, 45928, 46004, 46093, 46177, 46241, 46329, 46409, 46489, 46566, 46636, 46720, 46801, 46891, 46972, 47060, 47137, 47212, 47296, 47379, 47458, 47538, 47620, 47708, 47785, 47872, 47948, 48037, 48123, 48215, 48291, 48368, 48445, 48522, 48613, 48694, 48778, 48859, 48946, 49020, 49101, 49185, 49268, 49352, 49437, 49520, 49599, 49684, 49767, 49857, 49938, 50022, 50104, 50184, 50268, 50360, 50449, 50525, 50607, 50695, 50775, 50850, 50940, 51022, 51098] := by decide

theorem pcBoundO : 51157 ≤ Sv.piF (792*(792+1)) := by decide

theorem pcBoundT : 51157 ≤ Sv.piF (1120*(1120+1)/2) := by decide

theorem hAmap : (List.range' 1 791).map (fun k => Nat.primeCounting (k*(k+1))) = Alit := by
  have h1 : (List.range' 1 791).map (fun k => Nat.primeCounting (k*(k+1)))
          = (List.range' 1 791).map (fun k => Sv.piF (k*(k+1))) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range'_1] at hk
    have hkle : k ≤ 791 := by omega
    have hbound : k*(k+1) ≤ Sv.NN := by
      have hNN : Sv.NN = 628100 := rfl
      have hh : k*(k+1) ≤ 791*792 := Nat.mul_le_mul hkle (by omega)
      omega
    exact (Sv.piF_eq (k*(k+1)) hbound).symm
  have esplit : (List.range' 1 200 ++ List.range' 201 200 ++ List.range' 401 200 ++ List.range' 601 191) = List.range' 1 791 := by
    rw [List.range'_append_1, List.range'_append_1, List.range'_append_1]
  rw [h1, ← esplit, List.map_append, List.map_append, List.map_append, pcA1, pcA2, pcA3, pcA4]
  rfl

theorem hBmap : (List.range' 1 1119).map (fun m => Nat.primeCounting (m*(m+1)/2)) = Blit := by
  have h1 : (List.range' 1 1119).map (fun m => Nat.primeCounting (m*(m+1)/2))
          = (List.range' 1 1119).map (fun m => Sv.piF (m*(m+1)/2)) := by
    apply List.map_congr_left
    intro m hm
    rw [List.mem_range'_1] at hm
    have hmle : m ≤ 1119 := by omega
    have hbound : m*(m+1)/2 ≤ Sv.NN := by
      have hNN : Sv.NN = 628100 := rfl
      have hh : m*(m+1) ≤ 1119*1120 := Nat.mul_le_mul hmle (by omega)
      have hd : m*(m+1)/2 ≤ 1119*1120/2 := Nat.div_le_div_right hh
      have hv : 1119*1120/2 = 626640 := by norm_num
      omega
    exact (Sv.piF_eq (m*(m+1)/2) hbound).symm
  have esplit : (List.range' 1 200 ++ List.range' 201 200 ++ List.range' 401 200 ++ List.range' 601 200 ++ List.range' 801 200 ++ List.range' 1001 119) = List.range' 1 1119 := by
    rw [List.range'_append_1, List.range'_append_1, List.range'_append_1, List.range'_append_1, List.range'_append_1]
  rw [h1, ← esplit, List.map_append, List.map_append, List.map_append, List.map_append, List.map_append, pcB1, pcB2, pcB3, pcB4, pcB5, pcB6]
  rfl

theorem hcv1 : convCount [1, 3, 5, 8, 10, 13, 16, 20, 24, 29, 32, 36, 42, 46, 52, 58, 62, 68, 75, 81, 89, 96, 101, 109, 118, 126, 133, 141, 150, 158, 167, 177, 187, 195, 205, 217, 222, 234, 246, 259, 268, 279, 290, 299, 312, 326, 335, 349, 363, 373, 383, 402, 416, 428, 440, 452, 464, 480, 495, 511, 526, 539, 557, 573, 589, 601, 617, 634, 649, 665, 683, 697, 712, 732, 750, 769, 783, 802, 822, 840, 856, 876, 896, 914, 932, 947, 971, 990, 1008, 1027, 1048, 1066, 1090, 1110, 1130, 1152, 1177, 1197, 1220, 1240, 1263, 1285, 1306, 1327, 1348, 1370, 1392, 1409, 1438, 1459, 1483, 1512, 1532, 1560, 1585, 1605, 1632, 1656, 1675, 1700, 1729, 1754, 1779, 1810, 1837, 1863, 1889, 1912, 1938, 1964, 1987, 2018, 2043, 2073, 2103, 2129, 2150, 2175, 2206, 2234, 2264, 2293, 2321, 2348, 2380, 2406, 2440, 2471, 2502, 2530, 2560, 2593, 2620, 2654, 2691, 2717, 2743, 2773, 2804, 2836, 2866, 2900, 2935, 2966, 2993, 3022, 3060, 3088, 3130, 3161, 3196, 3225, 3254, 3288, 3319, 3355, 3389, 3423, 3456, 3497, 3531, 3565, 3607, 3642, 3676, 3715, 3749, 3783, 3814, 3850, 3887, 3929, 3963, 4000, 4034, 4068, 4107, 4148, 4183, 4223] Blit 51156 = 1 := by decide

theorem hcv2 : convCount [4256, 4291, 4333, 4372, 4416, 4456, 4500, 4531, 4567, 4612, 4649, 4687, 4724, 4761, 4798, 4843, 4878, 4922, 4960, 5001, 5043, 5086, 5129, 5172, 5208, 5248, 5295, 5338, 5376, 5421, 5459, 5505, 5548, 5590, 5630, 5678, 5718, 5766, 5816, 5860, 5905, 5948, 5995, 6043, 6082, 6125, 6164, 6213, 6256, 6297, 6338, 6393, 6434, 6474, 6521, 6572, 6613, 6659, 6707, 6759, 6800, 6848, 6892, 6933, 6985, 7034, 7087, 7137, 7181, 7232, 7279, 7325, 7376, 7424, 7474, 7520, 7568, 7621, 7670, 7718, 7766, 7814, 7870, 7922, 7971, 8028, 8080, 8126, 8175, 8224, 8274, 8326, 8374, 8429, 8479, 8535, 8577, 8631, 8688, 8745, 8793, 8848, 8896, 8957, 9016, 9064, 9119, 9173, 9232, 9284, 9340, 9391, 9437, 9495, 9550, 9604, 9658, 9714, 9777, 9834, 9879, 9934, 9989, 10045, 10100, 10157, 10219, 10267, 10326, 10386, 10445, 10492, 10553, 10611, 10666, 10732, 10780, 10834, 10894, 10960, 11012, 11070, 11135, 11187, 11246, 11306, 11364, 11430, 11491, 11551, 11611, 11671, 11730, 11791, 11853, 11907, 11970, 12035, 12097, 12157, 12223, 12275, 12336, 12402, 12464, 12523, 12582, 12651, 12717, 12780, 12842, 12907, 12968, 13029, 13097, 13162, 13223, 13282, 13344, 13406, 13467, 13534, 13595, 13665, 13722, 13795, 13862, 13927, 14000, 14065, 14128, 14191, 14260, 14327, 14388, 14453, 14522, 14585, 14648, 14716] Blit 51156 = 0 := by decide

theorem hcv3 : convCount [14785, 14852, 14915, 14981, 15053, 15111, 15178, 15246, 15316, 15375, 15440, 15509, 15584, 15651, 15723, 15785, 15860, 15927, 15989, 16073, 16132, 16202, 16277, 16355, 16418, 16482, 16561, 16636, 16700, 16775, 16855, 16920, 16996, 17062, 17139, 17204, 17273, 17352, 17428, 17502, 17568, 17640, 17711, 17785, 17862, 17930, 18005, 18073, 18152, 18221, 18290, 18363, 18442, 18517, 18588, 18669, 18743, 18828, 18902, 18980, 19044, 19118, 19202, 19267, 19337, 19416, 19488, 19566, 19650, 19724, 19802, 19880, 19955, 20032, 20111, 20182, 20260, 20347, 20430, 20512, 20588, 20659, 20731, 20808, 20885, 20955, 21027, 21110, 21190, 21268, 21351, 21435, 21511, 21593, 21672, 21752, 21832, 21920, 22004, 22077, 22163, 22243, 22316, 22399, 22486, 22566, 22642, 22724, 22803, 22884, 22962, 23042, 23125, 23202, 23289, 23373, 23473, 23549, 23633, 23719, 23801, 23888, 23961, 24046, 24134, 24218, 24299, 24380, 24463, 24553, 24643, 24719, 24807, 24897, 24977, 25051, 25129, 25222, 25313, 25395, 25481, 25559, 25645, 25726, 25811, 25894, 25980, 26069, 26160, 26243, 26335, 26429, 26517, 26609, 26691, 26780, 26864, 26944, 27038, 27131, 27217, 27307, 27399, 27493, 27591, 27682, 27773, 27861, 27946, 28045, 28135, 28228, 28318, 28409, 28498, 28593, 28683, 28769, 28861, 28954, 29043, 29136, 29220, 29315, 29407, 29499, 29592, 29682, 29776, 29873, 29965, 30058, 30151, 30245, 30345, 30442, 30523, 30615, 30718, 30798] Blit 51156 = 0 := by decide

theorem hcv4 : convCount [30888, 30980, 31077, 31174, 31272, 31373, 31458, 31545, 31633, 31723, 31814, 31920, 32015, 32114, 32205, 32304, 32394, 32483, 32584, 32683, 32783, 32875, 32963, 33067, 33170, 33273, 33382, 33475, 33569, 33662, 33764, 33864, 33954, 34049, 34140, 34232, 34332, 34425, 34529, 34630, 34728, 34830, 34920, 35028, 35131, 35228, 35331, 35433, 35531, 35630, 35736, 35832, 35928, 36031, 36132, 36237, 36345, 36451, 36560, 36665, 36764, 36857, 36958, 37062, 37168, 37284, 37383, 37475, 37576, 37674, 37790, 37892, 37978, 38079, 38184, 38292, 38390, 38485, 38590, 38681, 38791, 38901, 38996, 39109, 39217, 39331, 39436, 39541, 39651, 39766, 39862, 39974, 40078, 40184, 40294, 40390, 40486, 40600, 40711, 40822, 40931, 41031, 41143, 41258, 41364, 41470, 41583, 41690, 41787, 41892, 42006, 42114, 42221, 42331, 42441, 42549, 42658, 42758, 42885, 42993, 43101, 43217, 43321, 43429, 43548, 43661, 43769, 43882, 43985, 44096, 44203, 44317, 44425, 44538, 44643, 44755, 44876, 44972, 45080, 45189, 45311, 45423, 45532, 45648, 45755, 45868, 45976, 46101, 46202, 46322, 46428, 46543, 46647, 46767, 46886, 46998, 47116, 47229, 47350, 47459, 47579, 47694, 47807, 47920, 48043, 48166, 48286, 48392, 48499, 48628, 48746, 48858, 48972, 49086, 49207, 49326, 49439, 49560, 49674, 49794, 49911, 50031, 50151, 50263, 50391, 50512, 50619, 50741, 50853, 50980, 51083] Blit 51156 = 0 := by decide

theorem hConv : convCount Alit Blit 51156 = 1 := by
  have hsplit : Alit = [1, 3, 5, 8, 10, 13, 16, 20, 24, 29, 32, 36, 42, 46, 52, 58, 62, 68, 75, 81, 89, 96, 101, 109, 118, 126, 133, 141, 150, 158, 167, 177, 187, 195, 205, 217, 222, 234, 246, 259, 268, 279, 290, 299, 312, 326, 335, 349, 363, 373, 383, 402, 416, 428, 440, 452, 464, 480, 495, 511, 526, 539, 557, 573, 589, 601, 617, 634, 649, 665, 683, 697, 712, 732, 750, 769, 783, 802, 822, 840, 856, 876, 896, 914, 932, 947, 971, 990, 1008, 1027, 1048, 1066, 1090, 1110, 1130, 1152, 1177, 1197, 1220, 1240, 1263, 1285, 1306, 1327, 1348, 1370, 1392, 1409, 1438, 1459, 1483, 1512, 1532, 1560, 1585, 1605, 1632, 1656, 1675, 1700, 1729, 1754, 1779, 1810, 1837, 1863, 1889, 1912, 1938, 1964, 1987, 2018, 2043, 2073, 2103, 2129, 2150, 2175, 2206, 2234, 2264, 2293, 2321, 2348, 2380, 2406, 2440, 2471, 2502, 2530, 2560, 2593, 2620, 2654, 2691, 2717, 2743, 2773, 2804, 2836, 2866, 2900, 2935, 2966, 2993, 3022, 3060, 3088, 3130, 3161, 3196, 3225, 3254, 3288, 3319, 3355, 3389, 3423, 3456, 3497, 3531, 3565, 3607, 3642, 3676, 3715, 3749, 3783, 3814, 3850, 3887, 3929, 3963, 4000, 4034, 4068, 4107, 4148, 4183, 4223] ++ [4256, 4291, 4333, 4372, 4416, 4456, 4500, 4531, 4567, 4612, 4649, 4687, 4724, 4761, 4798, 4843, 4878, 4922, 4960, 5001, 5043, 5086, 5129, 5172, 5208, 5248, 5295, 5338, 5376, 5421, 5459, 5505, 5548, 5590, 5630, 5678, 5718, 5766, 5816, 5860, 5905, 5948, 5995, 6043, 6082, 6125, 6164, 6213, 6256, 6297, 6338, 6393, 6434, 6474, 6521, 6572, 6613, 6659, 6707, 6759, 6800, 6848, 6892, 6933, 6985, 7034, 7087, 7137, 7181, 7232, 7279, 7325, 7376, 7424, 7474, 7520, 7568, 7621, 7670, 7718, 7766, 7814, 7870, 7922, 7971, 8028, 8080, 8126, 8175, 8224, 8274, 8326, 8374, 8429, 8479, 8535, 8577, 8631, 8688, 8745, 8793, 8848, 8896, 8957, 9016, 9064, 9119, 9173, 9232, 9284, 9340, 9391, 9437, 9495, 9550, 9604, 9658, 9714, 9777, 9834, 9879, 9934, 9989, 10045, 10100, 10157, 10219, 10267, 10326, 10386, 10445, 10492, 10553, 10611, 10666, 10732, 10780, 10834, 10894, 10960, 11012, 11070, 11135, 11187, 11246, 11306, 11364, 11430, 11491, 11551, 11611, 11671, 11730, 11791, 11853, 11907, 11970, 12035, 12097, 12157, 12223, 12275, 12336, 12402, 12464, 12523, 12582, 12651, 12717, 12780, 12842, 12907, 12968, 13029, 13097, 13162, 13223, 13282, 13344, 13406, 13467, 13534, 13595, 13665, 13722, 13795, 13862, 13927, 14000, 14065, 14128, 14191, 14260, 14327, 14388, 14453, 14522, 14585, 14648, 14716] ++ [14785, 14852, 14915, 14981, 15053, 15111, 15178, 15246, 15316, 15375, 15440, 15509, 15584, 15651, 15723, 15785, 15860, 15927, 15989, 16073, 16132, 16202, 16277, 16355, 16418, 16482, 16561, 16636, 16700, 16775, 16855, 16920, 16996, 17062, 17139, 17204, 17273, 17352, 17428, 17502, 17568, 17640, 17711, 17785, 17862, 17930, 18005, 18073, 18152, 18221, 18290, 18363, 18442, 18517, 18588, 18669, 18743, 18828, 18902, 18980, 19044, 19118, 19202, 19267, 19337, 19416, 19488, 19566, 19650, 19724, 19802, 19880, 19955, 20032, 20111, 20182, 20260, 20347, 20430, 20512, 20588, 20659, 20731, 20808, 20885, 20955, 21027, 21110, 21190, 21268, 21351, 21435, 21511, 21593, 21672, 21752, 21832, 21920, 22004, 22077, 22163, 22243, 22316, 22399, 22486, 22566, 22642, 22724, 22803, 22884, 22962, 23042, 23125, 23202, 23289, 23373, 23473, 23549, 23633, 23719, 23801, 23888, 23961, 24046, 24134, 24218, 24299, 24380, 24463, 24553, 24643, 24719, 24807, 24897, 24977, 25051, 25129, 25222, 25313, 25395, 25481, 25559, 25645, 25726, 25811, 25894, 25980, 26069, 26160, 26243, 26335, 26429, 26517, 26609, 26691, 26780, 26864, 26944, 27038, 27131, 27217, 27307, 27399, 27493, 27591, 27682, 27773, 27861, 27946, 28045, 28135, 28228, 28318, 28409, 28498, 28593, 28683, 28769, 28861, 28954, 29043, 29136, 29220, 29315, 29407, 29499, 29592, 29682, 29776, 29873, 29965, 30058, 30151, 30245, 30345, 30442, 30523, 30615, 30718, 30798] ++ [30888, 30980, 31077, 31174, 31272, 31373, 31458, 31545, 31633, 31723, 31814, 31920, 32015, 32114, 32205, 32304, 32394, 32483, 32584, 32683, 32783, 32875, 32963, 33067, 33170, 33273, 33382, 33475, 33569, 33662, 33764, 33864, 33954, 34049, 34140, 34232, 34332, 34425, 34529, 34630, 34728, 34830, 34920, 35028, 35131, 35228, 35331, 35433, 35531, 35630, 35736, 35832, 35928, 36031, 36132, 36237, 36345, 36451, 36560, 36665, 36764, 36857, 36958, 37062, 37168, 37284, 37383, 37475, 37576, 37674, 37790, 37892, 37978, 38079, 38184, 38292, 38390, 38485, 38590, 38681, 38791, 38901, 38996, 39109, 39217, 39331, 39436, 39541, 39651, 39766, 39862, 39974, 40078, 40184, 40294, 40390, 40486, 40600, 40711, 40822, 40931, 41031, 41143, 41258, 41364, 41470, 41583, 41690, 41787, 41892, 42006, 42114, 42221, 42331, 42441, 42549, 42658, 42758, 42885, 42993, 43101, 43217, 43321, 43429, 43548, 43661, 43769, 43882, 43985, 44096, 44203, 44317, 44425, 44538, 44643, 44755, 44876, 44972, 45080, 45189, 45311, 45423, 45532, 45648, 45755, 45868, 45976, 46101, 46202, 46322, 46428, 46543, 46647, 46767, 46886, 46998, 47116, 47229, 47350, 47459, 47579, 47694, 47807, 47920, 48043, 48166, 48286, 48392, 48499, 48628, 48746, 48858, 48972, 49086, 49207, 49326, 49439, 49560, 49674, 49794, 49911, 50031, 50151, 50263, 50391, 50512, 50619, 50741, 50853, 50980, 51083] := by rfl
  rw [hsplit, convCount_append, convCount_append, convCount_append, hcv1, hcv2, hcv3, hcv4]

theorem main_count :
    ((Icc 1 51157 ×ˢ Icc 1 51157).filter
        (fun p : ℕ × ℕ => Nat.primeCounting (p.1 * (p.1+1)) + Nat.primeCounting (p.2*(p.2+1)/2) = 51156)).card = 1 := by
  have hBoundO : 51157 ≤ Nat.primeCounting (792*(792+1)) := by
    rw [← Sv.piF_eq (792*(792+1)) (by rw [show Sv.NN = 628100 from rfl]; norm_num)]
    exact pcBoundO
  have hBoundT : 51157 ≤ Nat.primeCounting (1120*(1120+1)/2) := by
    rw [← Sv.piF_eq (1120*(1120+1)/2) (by rw [show Sv.NN = 628100 from rfl]; norm_num)]
    exact pcBoundT
  have hregion : ((Icc 1 51157 ×ˢ Icc 1 51157).filter
        (fun p : ℕ × ℕ => Nat.primeCounting (p.1 * (p.1+1)) + Nat.primeCounting (p.2*(p.2+1)/2) = 51156)).card
      = ((Icc 1 791 ×ˢ Icc 1 1119).filter
        (fun p : ℕ × ℕ => Nat.primeCounting (p.1 * (p.1+1)) + Nat.primeCounting (p.2*(p.2+1)/2) = 51156)).card := by
    have hset : (Icc 1 51157 ×ˢ Icc 1 51157).filter
          (fun p : ℕ × ℕ => Nat.primeCounting (p.1 * (p.1+1)) + Nat.primeCounting (p.2*(p.2+1)/2) = 51156)
        = (Icc 1 791 ×ˢ Icc 1 1119).filter
          (fun p : ℕ × ℕ => Nat.primeCounting (p.1 * (p.1+1)) + Nat.primeCounting (p.2*(p.2+1)/2) = 51156) := by
      apply Finset.ext
      rintro ⟨k, m⟩
      simp only [mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨hk1, _⟩, ⟨hm1, _⟩⟩, hP⟩
        have hbk : k ≤ 791 := by
          by_contra hc
          have hge : 792 ≤ k := by omega
          have h1 : 792*(792+1) ≤ k*(k+1) := Nat.mul_le_mul hge (by omega)
          have h2 := Nat.monotone_primeCounting h1
          omega
        have hbm : m ≤ 1119 := by
          by_contra hc
          have hge : 1120 ≤ m := by omega
          have h1 : 1120*(1120+1)/2 ≤ m*(m+1)/2 := by
            apply Nat.div_le_div_right; exact Nat.mul_le_mul hge (by omega)
          have h2 := Nat.monotone_primeCounting h1
          omega
        exact ⟨⟨⟨hk1, hbk⟩, ⟨hm1, hbm⟩⟩, hP⟩
      · rintro ⟨⟨⟨hk1, hk2⟩, ⟨hm1, hm2⟩⟩, hP⟩
        exact ⟨⟨⟨hk1, by omega⟩, ⟨hm1, by omega⟩⟩, hP⟩
    rw [hset]
  rw [hregion,
      bridge 791 1119 51156 (fun k => Nat.primeCounting (k*(k+1)))
        (fun m => Nat.primeCounting (m*(m+1)/2)),
      hAmap, hBmap, hConv]

end Disp

theorem oeis_a263001_conjecture.disproof :
    ¬ ((∀ (n : ℕ), 2 < n → A263001 n > 0) ∧
       (∀ (n : ℕ), A263001 n = 1 ↔ n = 1 ∨ n = 4 ∨ n = 6)) := by
  rintro ⟨_, h2⟩
  have hone : A263001 51156 = 1 := Disp.main_count
  have h := (h2 51156).mp hone
  rcases h with h | h | h <;> omega
