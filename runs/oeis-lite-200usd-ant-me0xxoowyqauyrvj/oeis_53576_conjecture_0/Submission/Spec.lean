import FormalConjectures.Util.ProblemImports

open Nat Set Finset

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

namespace A053576

/-- Sum of powers of two. -/
lemma two_pow_sum (n : ℕ) : ∑ k ∈ Finset.range n, 2 ^ k = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- A Fermat-type prime `2^s + 1` must have `s` a power of two. -/
lemma exp_pow_two_of_prime {s : ℕ} (hs : 1 ≤ s) (hp : (2 ^ s + 1).Prime) :
    ∃ k, s = 2 ^ k := by
  -- write s = 2^a * u with u odd; show u = 1
  set a := s.factorization 2 with ha
  set u := ordCompl[2] s with hu
  have hsne : s ≠ 0 := by omega
  have hdecomp : 2 ^ a * u = s := Nat.ordProj_mul_ordCompl_eq_self s 2
  have hodd : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hsne
  -- u = 1
  refine ⟨a, ?_⟩
  rw [← hdecomp]
  suffices hu1 : u = 1 by rw [hu1, mul_one]
  by_contra hune
  -- u is odd and ≠ 1, so u ≥ 3
  have hupos : 0 < u := Nat.ordCompl_pos 2 hsne
  have hu3 : 3 ≤ u := by omega
  -- 2^(2^a) + 1 divides 2^s + 1
  have hodd_u : Odd u := Nat.odd_iff.mpr (by omega)
  have hdvd : 2 ^ (2 ^ a) + 1 ∣ 2 ^ s + 1 := by
    have : 2 ^ s = (2 ^ (2 ^ a)) ^ u := by rw [← pow_mul, hdecomp]
    rw [this]
    have := Odd.nat_add_dvd_pow_add_pow (2 ^ (2 ^ a)) 1 hodd_u
    simpa using this
  -- this divisor is a proper nontrivial divisor
  have hlt : 2 ^ (2 ^ a) + 1 < 2 ^ s + 1 := by
    have hpa : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h2a_lt : 2 ^ a < s := by nlinarith [hdecomp, hu3, hpa]
    have : (2:ℕ) ^ (2 ^ a) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) h2a_lt
    omega
  have hgt : 1 < 2 ^ (2 ^ a) + 1 := by
    have : 1 ≤ 2 ^ (2 ^ a) := Nat.one_le_two_pow
    omega
  rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h | h <;> omega

/-- `2 ^ v₂(p-1) ≤ p - 1`. -/
lemma pow_v2_le {p : ℕ} (hp : 2 ≤ p) :
    2 ^ ((p - 1).factorization 2) ≤ p - 1 := by
  have hpne : p - 1 ≠ 0 := by omega
  exact Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (p - 1) 2)

/-- A non-Fermat odd prime exceeds `2 ^ (v₂(p-1) + 1)`. -/
lemma not_fermat_bound {p : ℕ} (hp : p.Prime)
    (hnf : ¬ ∃ s, p = 2 ^ s + 1) : 2 ^ ((p - 1).factorization 2 + 1) < p := by
  set t := (p - 1).factorization 2 with ht
  have hp2 : 2 ≤ p := hp.two_le
  have hpne : p - 1 ≠ 0 := by omega
  obtain ⟨u, hu⟩ : 2 ^ t ∣ p - 1 := Nat.ordProj_dvd (p - 1) 2
  have hnotdvd : ¬ 2 ^ (t + 1) ∣ (p - 1) :=
    Nat.pow_succ_factorization_not_dvd hpne Nat.prime_two
  have hu_odd : ¬ 2 ∣ u := by
    rintro ⟨v, hv⟩
    apply hnotdvd
    rw [hu, hv, pow_succ]
    exact ⟨v, by ring⟩
  have hupos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, mul_zero] at hu; omega
    · exact h
  have hune1 : u ≠ 1 := by
    intro h1
    apply hnf
    refine ⟨t, ?_⟩
    have : p - 1 = 2 ^ t := by rw [hu, h1, mul_one]
    omega
  have hu3 : 3 ≤ u := by omega
  have hpa : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hu' : p = 2 ^ t * u + 1 := by omega
  rw [pow_succ]
  nlinarith [hu', hu3, hpa]

/-- Basic product bound: `2 ^ (∑ v₂(p-1)) ≤ ∏ p`. -/
lemma R0 : ∀ (T : Finset ℕ), (∀ p ∈ T, 2 ≤ p) →
    2 ^ (∑ p ∈ T, (p - 1).factorization 2) ≤ ∏ p ∈ T, p := by
  intro T
  induction T using Finset.induction with
  | empty => intro _; simp
  | insert q T' hq ih =>
    intro hT
    have hqT : 2 ≤ q := hT q (Finset.mem_insert_self q T')
    have hsub : ∀ p ∈ T', 2 ≤ p := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    rw [Finset.sum_insert hq, Finset.prod_insert hq, pow_add]
    have h1 : 2 ^ ((q - 1).factorization 2) ≤ q := le_trans (pow_v2_le hqT) (by omega)
    exact Nat.mul_le_mul h1 (ih hsub)

/-- Key dichotomy: either `∏ p ≥ 2 ^ (1 + ∑ v₂(p-1))` or all primes are Fermat. -/
lemma R' : ∀ (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
    2 ^ (1 + ∑ p ∈ T, (p - 1).factorization 2) ≤ ∏ p ∈ T, p
      ∨ ∀ p ∈ T, ∃ s, p = 2 ^ s + 1 := by
  intro T
  induction T using Finset.induction with
  | empty => intro _; right; intro p hp; simp at hp
  | insert q T' hq ih =>
    intro hT
    have hqP : q.Prime := hT q (Finset.mem_insert_self q T')
    have hsub : ∀ p ∈ T', p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have hq2 : 2 ≤ q := hqP.two_le
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    by_cases hf : ∃ s, q = 2 ^ s + 1
    · rcases ih hsub with hL | hR
      · left
        have hqge : 2 ^ ((q - 1).factorization 2) ≤ q := le_trans (pow_v2_le hq2) (by omega)
        rw [show 1 + ((q - 1).factorization 2 + ∑ p ∈ T', (p - 1).factorization 2)
              = (q - 1).factorization 2 + (1 + ∑ p ∈ T', (p - 1).factorization 2) by ring, pow_add]
        exact Nat.mul_le_mul hqge hL
      · right
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact hf
        · exact hR p hp'
    · left
      have hbound : 2 ^ ((q - 1).factorization 2 + 1) < q := not_fermat_bound hqP hf
      have h2 := R0 T' (fun p hp => (hsub p hp).two_le)
      rw [show 1 + ((q - 1).factorization 2 + ∑ p ∈ T', (p - 1).factorization 2)
            = ((q - 1).factorization 2 + 1) + ∑ p ∈ T', (p - 1).factorization 2 by ring, pow_add]
      exact Nat.mul_le_mul (le_of_lt hbound) h2

/-- For odd `x`, the 2-adic valuation of `φ x` is the sum of `v₂(p-1)` over prime factors. -/
lemma v2_totient_odd {x : ℕ} (hx : Odd x) :
    (Nat.totient x).factorization 2 = ∑ p ∈ x.primeFactors, (p - 1).factorization 2 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  rcases eq_or_ne x 1 with rfl | hx1
  · simp
  · have hS : ∀ p ∈ x.primeFactors,
        p ^ (x.factorization p - 1) * (p - 1) ≠ 0 := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have := hpp.two_le
      exact Nat.mul_ne_zero (pow_ne_zero _ hpp.pos.ne') (by omega)
    rw [Nat.totient_eq_prod_factorization hx0, Nat.prod_factorization_eq_prod_primeFactors,
        Nat.factorization_prod_apply hS]
    apply Finset.sum_congr rfl
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hx.not_two_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hpodd : ¬ (2 ∣ p) := by
      rintro h2p
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h2p).symm
    have hk : p ^ (x.factorization p - 1) ≠ 0 := pow_ne_zero _ hpp.pos.ne'
    have hp1 : p - 1 ≠ 0 := by have := hpp.two_le; omega
    rw [Nat.factorization_mul hk hp1, Finsupp.add_apply, Nat.factorization_pow,
        Finsupp.smul_apply, Nat.factorization_eq_zero_of_not_dvd hpodd]
    simp

/-- For a Fermat number `2^s + 1`, `v₂` of its predecessor is `s`. -/
lemma fermat_v2 (s : ℕ) : ((2 ^ s + 1) - 1).factorization 2 = s := by
  rw [Nat.add_sub_cancel, Nat.factorization_pow_self Nat.prime_two]

/-- Counting argument: among Fermat-prime factors whose `v₂(p-1)` sum to at least `2^33`,
some single one has `v₂(p-1) ≥ 2^33`. -/
lemma counting {T : Finset ℕ} (hP : ∀ p ∈ T, p.Prime) (hodd : ∀ p ∈ T, Odd p)
    (hF : ∀ p ∈ T, ∃ s, p = 2 ^ s + 1)
    (hsum : 2 ^ 33 ≤ ∑ p ∈ T, (p - 1).factorization 2) :
    ∃ p ∈ T, 2 ^ 33 ≤ (p - 1).factorization 2 := by
  by_contra hcon
  push_neg at hcon
  -- For each p ∈ T, v₂(p-1) is a power of two `2^k` with `k < 33`.
  have key : ∀ p ∈ T, ∃ k, k < 33 ∧ (p - 1).factorization 2 = 2 ^ k := by
    intro p hp
    obtain ⟨s, hs⟩ := hF p hp
    have hfp : (p - 1).factorization 2 = s := by rw [hs, fermat_v2]
    have hpp := hP p hp
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · subst h
        have := hodd p hp; rw [hs] at this; norm_num at this
      · exact h
    obtain ⟨k, hk⟩ := exp_pow_two_of_prime hs1 (by rw [← hs]; exact hpp)
    refine ⟨k, ?_, by rw [hfp, hk]⟩
    have hlt := hcon p hp
    rw [hfp, hk] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  -- injectivity of `v₂(·-1)` on `T`
  have hfinj : ∀ p ∈ T, ∀ q ∈ T, (p - 1).factorization 2 = (q - 1).factorization 2 → p = q := by
    intro p hp q hq hpq
    obtain ⟨sp, hsp⟩ := hF p hp
    obtain ⟨sq, hsq⟩ := hF q hq
    rw [hsp, hsq, fermat_v2, fermat_v2] at hpq
    rw [hsp, hsq, hpq]
  -- subset of image
  have hsubset : T.image (fun p => (p - 1).factorization 2)
      ⊆ (Finset.range 33).image (fun k => 2 ^ k) := by
    intro s hs
    rw [Finset.mem_image] at hs ⊢
    obtain ⟨p, hpT, rfl⟩ := hs
    obtain ⟨k, hk33, hk⟩ := key p hpT
    exact ⟨k, Finset.mem_range.mpr hk33, hk.symm⟩
  -- bound the sum
  have heq : ∑ s ∈ T.image (fun p => (p - 1).factorization 2), s
      = ∑ p ∈ T, (p - 1).factorization 2 :=
    Finset.sum_image (fun p hp q hq h =>
      hfinj p (Finset.mem_coe.mp hp) q (Finset.mem_coe.mp hq) h)
  have heq2 : ∑ s ∈ (Finset.range 33).image (fun k => 2 ^ k), s
      = ∑ k ∈ Finset.range 33, 2 ^ k :=
    Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective (by norm_num) h)
  have hsum_le : ∑ p ∈ T, (p - 1).factorization 2 ≤ ∑ k ∈ Finset.range 33, 2 ^ k := by
    rw [← heq, ← heq2]
    exact Finset.sum_le_sum_of_subset hsubset
  rw [two_pow_sum] at hsum_le
  have : (1 : ℕ) ≤ 2 ^ 33 := Nat.one_le_two_pow
  omega

/-- For nonzero even `x`, `2 * φ x ≤ x`. -/
lemma even_totient_half {x : ℕ} (hx : Even x) (hx0 : x ≠ 0) :
    2 * Nat.totient x ≤ x := by
  set a := x.factorization 2 with ha
  have ha1 : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hx0 hx.two_dvd
  set b := ordCompl[2] x with hb
  have hdecomp : 2 ^ a * b = x := Nat.ordProj_mul_ordCompl_eq_self x 2
  have hcop : Nat.Coprime (2 ^ a) b := (Nat.coprime_ordCompl Nat.prime_two hx0).pow_left a
  have hbpos : 0 < b := Nat.ordCompl_pos 2 hx0
  have hφb : Nat.totient b ≤ b := Nat.totient_le b
  have h2a : 2 * 2 ^ (a - 1) = 2 ^ a := by rw [← pow_succ']; congr 1; omega
  rw [← hdecomp, Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two ha1]
  have : 2 * (2 ^ (a - 1) * (2 - 1) * Nat.totient b) = 2 ^ a * Nat.totient b := by
    rw [show (2 - 1) = 1 from rfl, mul_one, ← mul_assoc, h2a]
  rw [this]
  exact Nat.mul_le_mul_left _ hφb

/-- Easy lower bound: any valid `x` is at least `2^N + 1`. -/
lemma lower_easy {N x : ℕ} (hN : 1 ≤ N) (hx : 0 < x)
    (hd : 2 ^ N ∣ Nat.totient x) : 2 ^ N + 1 ≤ x := by
  have hx1 : 1 < x := by
    by_contra h
    push_neg at h
    interval_cases x
    rw [Nat.totient_one, Nat.dvd_one] at hd
    have : 2 ≤ 2 ^ N := by
      calc (2:ℕ) = 2 ^ 1 := rfl
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    omega
  have h1 : Nat.totient x < x := Nat.totient_lt x hx1
  have h3 : 2 ^ N ≤ Nat.totient x := Nat.le_of_dvd (Nat.totient_pos.mpr hx) hd
  omega

/-- Hard lower bound when `2^N + 1` is composite: any valid `x` is at least `2^(N+1)`. -/
lemma lower_hard {N x : ℕ} (hN : N = 2 ^ 33) (hnp : ¬ (2 ^ N + 1).Prime)
    (hx : 0 < x) (hd : 2 ^ N ∣ Nat.totient x) : 2 ^ (N + 1) ≤ x := by
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  have hx1 : 1 < x := lt_of_lt_of_le (by omega) (lower_easy hN1 hx hd)
  rcases Nat.even_or_odd x with hev | hodd
  · have h := even_totient_half hev (by omega)
    have h3 : 2 ^ N ≤ Nat.totient x := Nat.le_of_dvd (Nat.totient_pos.mpr hx) hd
    have hpw : 2 ^ (N + 1) = 2 * 2 ^ N := by rw [pow_succ]; ring
    omega
  · have hSval : (Nat.totient x).factorization 2
        = ∑ p ∈ x.primeFactors, (p - 1).factorization 2 := v2_totient_odd hodd
    have hle : N ≤ (Nat.totient x).factorization 2 := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (Nat.totient_pos.mpr hx).ne']
      exact hd
    rw [hSval] at hle
    have hprime : ∀ p ∈ x.primeFactors, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors hp
    have hrad : (∏ p ∈ x.primeFactors, p) ≤ x :=
      Nat.le_of_dvd hx (Nat.prod_primeFactors_dvd x)
    rcases R' x.primeFactors hprime with hL | hR
    · have hstep : 2 ^ (N + 1)
          ≤ 2 ^ (1 + ∑ p ∈ x.primeFactors, (p - 1).factorization 2) := by
        apply Nat.pow_le_pow_right (by norm_num); omega
      exact le_trans hstep (le_trans hL hrad)
    · have hoddp : ∀ p ∈ x.primeFactors, Odd p := by
        intro p hp
        rcases (hprime p hp).eq_two_or_odd' with rfl | ho
        · exact absurd (Nat.dvd_of_mem_primeFactors hp) hodd.not_two_dvd_nat
        · exact ho
      have hcount := counting hprime hoddp hR (by rw [hN] at hle; exact hle)
      obtain ⟨p, hp, hpge⟩ := hcount
      obtain ⟨s, hs⟩ := hR p hp
      have hps : (p - 1).factorization 2 = s := by rw [hs, fermat_v2]
      rw [hps, ← hN] at hpge
      have hple : p ≤ x := Nat.le_of_dvd hx (Nat.dvd_of_mem_primeFactors hp)
      rcases Nat.lt_or_ge s (N + 1) with hsN | hsN
      · have hseq : s = N := by omega
        rw [hseq] at hs
        rw [hs] at hple
        have hpp := hprime p hp
        rw [hs] at hpp
        exact absurd hpp hnp
      · have hpw : 2 ^ (N + 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hsN
        rw [hs] at hple
        omega

end A053576

open A053576 in
-- Formalization of the conjecture
/--
A053576 a(8589934592) is the first unknown term; it is $2^{8589934593}$ if $F(33) = 2^{2^{33}}+1$ is composite or $F(33)$ otherwise. - Charles R Greathouse IV, Jul 15 2013
-/
theorem oeis_53576_conjecture_0 :
    let N_idx : ℕ := 33
    let N : ℕ := 2 ^ N_idx
    let F33 : ℕ := Nat.fermatNumber N_idx
    a N = if F33.Prime then F33 else 2 ^ (N + 1) := by
  intro N_idx N F33
  have hN : N = 2 ^ 33 := rfl
  have hNF : F33 = 2 ^ N + 1 := rfl
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  show sInf { m : ℕ | m > 0 ∧ 2 ^ N ∣ Nat.totient m } = if F33.Prime then F33 else 2 ^ (N + 1)
  by_cases hp : F33.Prime
  · rw [if_pos hp]
    have hF33mem : F33 ∈ { m : ℕ | m > 0 ∧ 2 ^ N ∣ Nat.totient m } := by
      refine ⟨by rw [hNF]; positivity, ?_⟩
      rw [Nat.totient_prime hp, hNF]
      simp
    apply le_antisymm
    · exact Nat.sInf_le hF33mem
    · have hmem := Nat.sInf_mem ⟨F33, hF33mem⟩
      rw [hNF]
      exact lower_easy hN1 hmem.1 hmem.2
  · rw [if_neg hp]
    have hmemP : 2 ^ (N + 1) ∈ { m : ℕ | m > 0 ∧ 2 ^ N ∣ Nat.totient m } := by
      refine ⟨by positivity, ?_⟩
      rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp
    have hnp : ¬ (2 ^ N + 1).Prime := by rw [← hNF]; exact hp
    apply le_antisymm
    · exact Nat.sInf_le hmemP
    · have hmem := Nat.sInf_mem ⟨2 ^ (N + 1), hmemP⟩
      exact lower_hard hN hnp hmem.1 hmem.2
