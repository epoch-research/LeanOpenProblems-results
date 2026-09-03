import Submission.PrimeWinnerEnergyIncrement

/-! Congruences forcing same-direction prime-winner contributions. These
identities do not assert any simultaneous prime-values conjecture or any
asymptotic conclusion about Erdős 371. -/
namespace Erdos371
open Finset

lemma maxPrimeFac_mul_small_cofactor (p k : ℕ) (hp : p.Prime)
    (hk : 0<k) (hkp : k≤p) : Nat.maxPrimeFac (k*p)=p := by
  rw [Nat.maxPrimeFac_mul hk.ne' hp.ne_zero, hp.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.maxPrimeFac_le.trans hkp)

/-- A divisor larger than the cofactor forces both factors of kp-1 below p. -/
lemma maxPrimeFac_mul_sub_one_lt_of_succ_dvd (p k : ℕ)
    (hk : 0<k) (hkp : k+1<p) (hd : k+1 ∣ p+1) :
    Nat.maxPrimeFac (k*p-1)<p := by
  have hp : 0<p := by omega
  have hmul : p≤k*p := by nlinarith
  have hprod : k+1≤k*p-1 := by omega
  have hdiv : k+1 ∣ k*p-1 := by
    have h := Nat.dvd_sub (dvd_mul_of_dvd_right hd k) (dvd_refl (k+1))
    have he : k*(p+1)-(k+1)=k*p-1 := by
      simp only [Nat.mul_add,Nat.mul_one]
      omega
    simpa only [he] using h
  have hq : 0<(k*p-1)/(k+1) := Nat.div_pos hprod (by omega)
  have hlt : (k*p-1)/(k+1)<p :=
    (Nat.div_lt_iff_lt_mul (by omega : 0<k+1)).mpr (by nlinarith [Nat.sub_le (k*p) 1])
  rw [← Nat.mul_div_cancel' hdiv, Nat.maxPrimeFac_mul (by omega) hq.ne']
  exact max_lt (Nat.maxPrimeFac_le.trans_lt hkp) (Nat.maxPrimeFac_le.trans_lt hlt)

lemma maxPrimeFac_le_half_of_not_prime (m : ℕ) (hm : ¬m.Prime) :
    2 * Nat.maxPrimeFac m ≤ m ∨ m ≤ 1 := by
  by_cases h : m≤1
  · exact Or.inr h
  · have hprime := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
    obtain ⟨a,ha⟩ := Nat.maxPrimeFac_dvd (n:=m)
    have ha0 : 0<a := by
      by_contra hn
      have : a=0 := by omega
      rw [this,mul_zero] at ha
      omega
    have ha1 : a≠1 := by
      intro h1
      rw [h1,mul_one] at ha
      exact hm (ha ▸ hprime)
    have ha2 : 2≤a := by omega
    left
    nlinarith

noncomputable def congruenceRunQuotient (p k : ℕ) : ℕ :=
  p+(p+1)/(k-1)

lemma congruenceRunQuotient_factorization (p k : ℕ) (hk : 2≤k)
    (hd : k-1 ∣ p+1) :
    (k-1)*congruenceRunQuotient p k=k*p+1 := by
  have h := Nat.mul_div_cancel' hd
  dsimp [congruenceRunQuotient]
  rw [Nat.mul_add,h]
  have hkm : k-1+1=k := by omega
  nlinarith

lemma congruenceRunQuotient_bounds (p k : ℕ) (hk : 2≤k)
    (hkp : k≤p) :
    p<congruenceRunQuotient p k ∧ congruenceRunQuotient p k≤2*p+1 := by
  have hq : 0<(p+1)/(k-1) := Nat.div_pos (by omega) (by omega)
  have hle := Nat.div_le_self (p+1) (k-1)
  dsimp [congruenceRunQuotient]
  omega

/-- On the opposite side, a nonsmooth neighbor is equivalent to one explicit
prime value, rather than to an unspecified factorization condition. -/
theorem maxPrimeFac_mul_add_one_gt_iff_quotient_prime (p k : ℕ)
    (hk : 2≤k) (hkp : k<p) (hd : k-1 ∣ p+1) :
    p<Nat.maxPrimeFac (k*p+1) ↔ (congruenceRunQuotient p k).Prime := by
  obtain ⟨hl,hu⟩ := congruenceRunQuotient_bounds p k hk hkp.le
  have he := congruenceRunQuotient_factorization p k hk hd
  have hq : congruenceRunQuotient p k≠0 := by omega
  rw [← he,Nat.maxPrimeFac_mul (by omega) hq]
  constructor
  · intro h
    by_contra hn
    have hbound : Nat.maxPrimeFac (congruenceRunQuotient p k)≤p := by
      obtain hb | hb := maxPrimeFac_le_half_of_not_prime _ hn
      · omega
      · exact Nat.maxPrimeFac_le.trans (by omega)
    have hm : Nat.maxPrimeFac (k-1)≤p := Nat.maxPrimeFac_le.trans (by omega)
    exact (not_lt_of_ge (max_le hm hbound)) h
  · intro hprime
    rw [hprime.maxPrimeFac_eq_self]
    exact hl.trans_le (le_max_right _ _)

noncomputable def primeWinnerContribution (p n : ℕ) : ℝ :=
  if primeWinner n=p then factorSign n else 0

/-- The two edges adjoining kp contribute either zero or plus one to the
p-winner group. The latter occurs precisely at the displayed prime value. -/
theorem congruence_run_pair_contribution (p k : ℕ)
    (hp : p.Prime) (hk : 2≤k) (hkp : k+1<p)
    (hd₁ : k+1 ∣ p+1) (hd₂ : k-1 ∣ p+1) :
    primeWinnerContribution p (k*p-1)+primeWinnerContribution p (k*p) =
      if (congruenceRunQuotient p k).Prime then 1 else 0 := by
  have hm := maxPrimeFac_mul_small_cofactor p k hp (by omega) (by omega)
  have hleft := maxPrimeFac_mul_sub_one_lt_of_succ_dvd p k (by omega) hkp hd₁
  have hright := maxPrimeFac_mul_add_one_gt_iff_quotient_prime p k hk (by omega) hd₂
  have he : k*p-1+1=k*p := Nat.sub_add_cancel (by nlinarith [hp.two_le])
  have hne : Nat.maxPrimeFac (k*p+1)≠p := by
    simpa only [hm] using consecutive_maxPrimeFac_ne (k*p)
  have hleft' : primeWinnerContribution p (k*p-1)=1 := by
    simp [primeWinnerContribution,primeWinner,factorSign,predicateSign,he,hm,
      max_eq_right hleft.le,hleft]
  rw [hleft']
  by_cases hq : (congruenceRunQuotient p k).Prime
  · have h := hright.mpr hq
    have hnp : primeWinner (k*p)≠p := by
      simp only [primeWinner,hm,max_eq_right h.le]
      omega
    simp [primeWinnerContribution,hnp,hq]
  · have h : Nat.maxPrimeFac (k*p+1)<p := lt_of_le_of_ne (not_lt.mp (hright.not.mpr hq)) hne
    simp [primeWinnerContribution,primeWinner,factorSign,predicateSign,hm,
      max_eq_left h.le,h.not_gt,hq]

#print axioms congruence_run_pair_contribution


/-- Reindex an entire prime-winner group by the two edges adjoining each
multiple of that prime. The endpoint includes both edges of the last pair. -/
theorem primeWinnerSum_mul_endpoint (p K : ℕ) (hp : p.Prime) :
    primeWinnerSum p (K*p+1) =
      ∑ k ∈ Icc 1 K, (primeWinnerContribution p (k*p-1)+
        primeWinnerContribution p (k*p)) := by
  let T := Icc 1 K
  let A := T.image (fun k => k*p-1)
  let B := T.image (fun k => k*p)
  have hsub : A ∪ B ⊆ range (K*p+1) := by
    intro n hn
    obtain hn | hn := mem_union.mp hn
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
      have hkK := (mem_Icc.mp hk).2
      have hm := Nat.mul_le_mul_right p hkK
      exact mem_range.mpr (by omega)
    · obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
      have hkK := (mem_Icc.mp hk).2
      have hm := Nat.mul_le_mul_right p hkK
      exact mem_range.mpr (by omega)
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro n hnA hnB
    obtain ⟨k,hk,hkn⟩ := mem_image.mp hnA
    obtain ⟨l,hl,hln⟩ := mem_image.mp hnB
    have hk1 := (mem_Icc.mp hk).1
    have hkp : 0<k*p := mul_pos (by omega) hp.pos
    have he : k*p=l*p+1 := by omega
    have hd : p ∣ (l*p+1)-l*p := by
      rw [← he]
      exact Nat.dvd_sub ⟨k,by ring⟩ ⟨l,by ring⟩
    exact hp.not_dvd_one (by simpa using hd)
  have hinjA : Set.InjOn (fun k => k*p-1) ↑T := by
    intro k hk l hl he
    change k ∈ Icc 1 K at hk
    change l ∈ Icc 1 K at hl
    have hk1 := (mem_Icc.mp hk).1
    have hl1 := (mem_Icc.mp hl).1
    have hkp : 0<k*p := mul_pos (by omega) hp.pos
    have hlp : 0<l*p := mul_pos (by omega) hp.pos
    have hm : k*p=l*p := by dsimp only at he; omega
    exact Nat.eq_of_mul_eq_mul_right hp.pos hm
  have hinjB : Set.InjOn (fun k => k*p) ↑T := by
    intro k hk l hl he
    exact Nat.eq_of_mul_eq_mul_right hp.pos he
  have hs : ∑ n ∈ A ∪ B, primeWinnerContribution p n =
      ∑ n ∈ range (K*p+1), primeWinnerContribution p n := by
    apply sum_subset hsub
    intro n hn hnot
    by_cases hw : primeWinner n=p
    · have hnN := mem_range.mp hn
      have hfactor : Nat.maxPrimeFac n=p ∨ Nat.maxPrimeFac (n+1)=p := by
        rcases max_cases (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h | h
        · exact Or.inl (h.1.symm.trans hw)
        · exact Or.inr (h.1.symm.trans hw)
      have hindex (m : ℕ) (hmN : m≤K*p+1) (hm : Nat.maxPrimeFac m=p) :
          ∃ k ∈ T, m=k*p := by
        have hd : p ∣ m := hm ▸ Nat.maxPrimeFac_dvd
        obtain ⟨k,he⟩ := hd
        have hk1 : 1≤k := by
          by_contra h
          have hk : k=0 := by omega
          rw [hk,mul_zero] at he
          subst m
          simp only [Nat.maxPrimeFac_zero] at hm
          have := hp.two_le
          omega
        have hkK : k≤K := by
          by_contra h
          have hh := Nat.mul_le_mul_left p (show K+1≤k by omega)
          nlinarith [hp.two_le]
        exact ⟨k,mem_Icc.mpr ⟨hk1,hkK⟩,by simpa [mul_comm] using he⟩
      exfalso
      apply hnot
      obtain hm | hm := hfactor
      · obtain ⟨k,hk,he⟩ := hindex n (by omega) hm
        exact mem_union_right _ (mem_image.mpr ⟨k,hk,he.symm⟩)
      · obtain ⟨k,hk,he⟩ := hindex (n+1) (by omega) hm
        exact mem_union_left _ (mem_image.mpr ⟨k,hk,by omega⟩)
    · simp [primeWinnerContribution,hw]
  change (∑ n ∈ (range (K*p+1)).filter (fun n => primeWinner n=p), factorSign n)=_
  rw [sum_filter]
  change (∑ n ∈ range (K*p+1), primeWinnerContribution p n)=_
  rw [← hs,sum_union hdis]
  change (∑ n ∈ T.image (fun k => k*p-1), primeWinnerContribution p n)+
    (∑ n ∈ T.image (fun k => k*p), primeWinnerContribution p n)=_
  rw [sum_image hinjA,sum_image hinjB,← sum_add_distrib]

#print axioms primeWinnerSum_mul_endpoint

lemma primeWinnerContribution_first_pair (p : ℕ) (hp : p.Prime)
    (hp2 : 2<p) (hd : 2 ∣ p+1) :
    primeWinnerContribution p (p-1)+primeWinnerContribution p p=0 := by
  have hl : Nat.maxPrimeFac (p-1)<p := Nat.maxPrimeFac_le.trans_lt (by omega)
  have hnprime : ¬(p+1).Prime := by
    intro h
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two h).mp hd
    omega
  have hr : Nat.maxPrimeFac (p+1)<p := by
    obtain h | h := maxPrimeFac_le_half_of_not_prime (p+1) hnprime
    · omega
    · omega
  have he : p-1+1=p := by omega
  simp [primeWinnerContribution,primeWinner,factorSign,predicateSign,he,
    hp.maxPrimeFac_eq_self,max_eq_right hl.le,max_eq_left hr.le,hl,hr.not_gt]

/-- A whole initial prime-winner group can be nonnegative term by term.
Its surviving contributions count explicit simultaneous linear-prime values.
No assertion that all those values are prime is made here. -/
theorem primeWinnerSum_congruence_run (p K : ℕ) (hp : p.Prime)
    (hK : 1≤K) (hKp : K+1<p)
    (hdiv : ∀ j : ℕ, 1≤j → j≤K+1 → j ∣ p+1) :
    primeWinnerSum p (K*p+1) =
      (((Icc 2 K).filter fun k => (congruenceRunQuotient p k).Prime).card : ℝ) := by
  rw [primeWinnerSum_mul_endpoint p K hp]
  have hset : insert 1 (Icc 2 K)=Icc 1 K := insert_Icc_succ_left_eq_Icc hK
  rw [← hset,sum_insert (by simp)]
  simp only [one_mul]
  rw [primeWinnerContribution_first_pair p hp (by omega) (hdiv 2 (by omega) (by omega)),zero_add]
  rw [← sum_boole]
  apply sum_congr rfl
  intro k hk
  obtain ⟨hk2,hkK⟩ := mem_Icc.mp hk
  exact congruence_run_pair_contribution p k hp hk2 (by omega)
    (hdiv (k+1) (by omega) (by omega)) (hdiv (k-1) (by omega) (by omega))

/-- This implication keeps the simultaneous-primality hypothesis explicit. -/
theorem primeWinnerSum_congruence_run_all_prime (p K : ℕ) (hp : p.Prime)
    (hK : 1≤K) (hKp : K+1<p)
    (hdiv : ∀ j : ℕ, 1≤j → j≤K+1 → j ∣ p+1)
    (hq : ∀ k ∈ Icc 2 K, (congruenceRunQuotient p k).Prime) :
    primeWinnerSum p (K*p+1)=(K-1 : ℕ) := by
  rw [primeWinnerSum_congruence_run p K hp hK hKp hdiv]
  have he : ((Icc 2 K).filter fun k => (congruenceRunQuotient p k).Prime)=Icc 2 K :=
    filter_eq_self.mpr hq
  rw [he,Nat.card_Icc]
  congr 1

#print axioms primeWinnerSum_congruence_run
#print axioms primeWinnerSum_congruence_run_all_prime

lemma primeWinnerSum_5039_45352 : primeWinnerSum 5039 45352=7 := by
  have hdiv : ∀ j ∈ Icc 1 10, j ∣ 5040 := by decide +kernel
  have h := primeWinnerSum_congruence_run 5039 9 (by decide +kernel)
    (by omega) (by omega) (fun j hj hJ => hdiv j (mem_Icc.mpr ⟨hj,hJ⟩))
  have hc : ((Icc 2 9).filter fun k => (congruenceRunQuotient 5039 k).Prime).card=7 := by
    have hset : Icc 2 9=({2,3,4,5,6,7,8,9} : Finset ℕ) := by decide +kernel
    norm_num [hset,congruenceRunQuotient,filter_insert,filter_singleton]
  rw [hc] at h
  exact h

/-- A cofactor-prime-count bound with constant one is false for the actual
prime ordering. This is only a finite auxiliary inequality, not Erdős 371. -/
theorem not_primeWinnerSum_bounded_by_cofactor_prime_count :
    ¬ ∀ p N : ℕ, ‖primeWinnerSum p N‖≤(((N/p+1).primesBelow).card : ℝ)+1 := by
  intro h
  have hh := h 5039 45352
  rw [primeWinnerSum_5039_45352] at hh
  have hc : ((45352/5039+1).primesBelow).card=4 := by decide +kernel
  rw [hc] at hh
  norm_num at hh

#print axioms primeWinnerSum_5039_45352
#print axioms not_primeWinnerSum_bounded_by_cofactor_prime_count
end Erdos371
