import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

namespace OEIS53576

-- Fermat prime lemma: if 2^t + 1 is prime and t ≥ 1, then t is a power of 2.
theorem fermat_exp_pow2 (t : ℕ) (ht : 1 ≤ t) (hp : Nat.Prime (2 ^ t + 1)) :
    ∃ d, t = 2 ^ d := by
  -- odd part of t
  set v := t.factorization 2 with hv
  set o := ordCompl[2] t with ho
  have htne : t ≠ 0 := by omega
  have hodd : ¬ (2 ∣ o) := Nat.not_dvd_ordCompl Nat.prime_two htne
  have hsplit : 2 ^ v * o = t := Nat.ordProj_mul_ordCompl_eq_self t 2
  have hole : 1 ≤ o := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [h] at hsplit; simp at hsplit; omega)
  rcases hole.lt_or_eq with h1 | h1
  · -- o > 1, o odd → derive composite
    exfalso
    have hoo : Odd o := by
      rcases Nat.even_or_odd o with he | hoo
      · exact absurd he.two_dvd hodd
      · exact hoo
    -- (2^(2^v) + 1) ∣ (2^(2^v))^o + 1
    have hdvd : (2 ^ (2 ^ v) + 1) ∣ (2 ^ (2 ^ v)) ^ o + 1 := by
      have := Odd.nat_add_dvd_pow_add_pow (2 ^ (2 ^ v)) 1 hoo
      simpa using this
    rw [← pow_mul, hsplit] at hdvd
    -- 2^(2^v) + 1 is a nontrivial divisor
    have hbt : 2 ^ v < t := by
      have hp2 : 0 < 2 ^ v := by positivity
      have : 2 ^ v * 1 < 2 ^ v * o := by nlinarith [hp2, h1]
      omega
    have hb_lt : 2 ^ (2 ^ v) + 1 < 2 ^ t + 1 := by
      have : 2 ^ (2 ^ v) < 2 ^ t := Nat.pow_lt_pow_right (by norm_num) hbt
      omega
    have hb_gt : 1 < 2 ^ (2 ^ v) + 1 := by
      have : 0 < 2 ^ (2 ^ v) := by positivity
      omega
    rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h | h
    · omega
    · omega
  · -- o = 1 → t = 2^v
    exact ⟨v, by rw [← hsplit, ← h1]; ring⟩

-- Classification of odd u with φ(u) a power of two: u is a product of Fermat numbers.
theorem oddTotient : ∀ (u : ℕ), Odd u → ∀ (s : ℕ), φ u = 2 ^ s →
    ∃ D : Finset ℕ, u = ∏ d ∈ D, (2 ^ (2 ^ d) + 1) ∧ s = ∑ d ∈ D, 2 ^ d := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu s hphi
    rcases eq_or_ne u 1 with hu1 | hu1
    · -- u = 1
      subst hu1
      simp only [Nat.totient_one] at hphi
      have hs0 : s = 0 := by
        rcases Nat.eq_zero_or_pos s with h | h
        · exact h
        · exfalso
          have : 2 ≤ 2 ^ s := by
            calc 2 = 2 ^ 1 := by ring
            _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h
          omega
      exact ⟨∅, by simp, by simp [hs0]⟩
    · -- u > 1
      have hupos : 0 < u := by rcases hu with ⟨k, rfl⟩; omega
      have hune0 : u ≠ 0 := hupos.ne'
      set p := u.minFac with hpdef
      have hpp : p.Prime := Nat.minFac_prime hu1
      have hpdvd : p ∣ u := Nat.minFac_dvd u
      have hpodd : p ≠ 2 := by
        intro h
        rw [h] at hpdvd
        exact absurd (even_iff_two_dvd.mpr hpdvd) (Nat.not_even_iff_odd.mpr hu)
      set e := u.factorization p with hedef
      have he1 : 0 < e := hpp.factorization_pos_of_dvd hune0 hpdvd
      set w := ordCompl[p] u with hwdef
      have hsplit : p ^ e * w = u := Nat.ordProj_mul_ordCompl_eq_self u p
      have hcop : Nat.Coprime (p ^ e) w := (Nat.coprime_ordCompl hpp hune0).pow_left e
      have hphimul : φ u = φ (p ^ e) * φ w := by
        rw [← hsplit, Nat.totient_mul hcop]
      have hpp_pow : φ (p ^ e) = p ^ (e - 1) * (p - 1) := Nat.totient_prime_pow hpp he1
      -- show e = 1
      have he : e = 1 := by
        by_contra hne
        have he2 : 2 ≤ e := by omega
        have hpdvdphi : p ∣ φ u := by
          rw [hphimul, hpp_pow]
          have : p ∣ p ^ (e - 1) := dvd_pow_self p (by omega)
          exact Dvd.dvd.mul_right (this.mul_right _) _
        rw [hphi] at hpdvdphi
        have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow hpdvdphi
        have hle := Nat.le_of_dvd (by norm_num) hp2
        have := hpp.two_le
        omega
      -- now u = p * w, φ u = (p-1) * φ w
      rw [he] at hsplit hphimul hpp_pow
      simp only [pow_one, Nat.sub_self, pow_zero, one_mul] at hpp_pow hsplit hphimul
      rw [hpp_pow] at hphimul
      -- (p-1) ∣ 2^s
      have hdvd2 : (p - 1) ∣ 2 ^ s := by
        rw [← hphi, hphimul]; exact Dvd.intro _ rfl
      obtain ⟨t, htle, hpt⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
      -- p = 2^t + 1, t ≥ 1
      have hp3 : 3 ≤ p := by have := hpp.two_le; omega
      have hteq : p = 2 ^ t + 1 := by omega
      have ht1 : 1 ≤ t := by
        by_contra h
        have : t = 0 := by omega
        rw [this] at hpt; simp at hpt; omega
      -- Fermat: t = 2^d
      obtain ⟨d, hd⟩ := fermat_exp_pow2 t ht1 (by rw [← hteq]; exact hpp)
      -- φ w = 2^(s - t)
      have hphiw : φ w = 2 ^ (s - t) := by
        have h1 : (p - 1) * φ w = 2 ^ s := by rw [← hphimul, hphi]
        rw [hpt] at h1
        have : 2 ^ t * φ w = 2 ^ t * 2 ^ (s - t) := by
          rw [← pow_add]
          rw [Nat.add_sub_cancel' htle]
          exact h1
        exact Nat.eq_of_mul_eq_mul_left (by positivity) this
      -- w properties
      have hwdvd : w ∣ u := Nat.ordCompl_dvd u p
      have hwodd : Odd w := hu.of_dvd_nat hwdvd
      have hwpos : 0 < w := Nat.pos_of_dvd_of_pos hwdvd hupos
      have hwlt : w < u := by
        rw [← hsplit]
        calc w = 1 * w := (one_mul w).symm
        _ < p * w := (Nat.mul_lt_mul_right hwpos).mpr hpp.one_lt
      -- apply IH
      obtain ⟨D', hD'prod, hD'sum⟩ := ih w hwlt hwodd (s - t) hphiw
      -- d ∉ D'
      have hpnotw : ¬ p ∣ w := Nat.not_dvd_ordCompl hpp hune0
      have hdnotin : d ∉ D' := by
        intro hmem
        apply hpnotw
        have hdw : (2 ^ (2 ^ d) + 1) ∣ w := by
          rw [hD'prod]; exact Finset.dvd_prod_of_mem _ hmem
        rw [hteq, hd]; exact hdw
      refine ⟨insert d D', ?_, ?_⟩
      · rw [Finset.prod_insert hdnotin, ← hD'prod, ← hsplit, hteq, hd]
      · rw [Finset.sum_insert hdnotin, ← hD'sum, ← hd]; omega

-- A finset of exponents whose powers of two sum to 2^n must be {n}.
theorem sum_two_pow_eq (D : Finset ℕ) (n : ℕ) (h : ∑ d ∈ D, 2 ^ d = 2 ^ n) :
    D = {n} := by
  have hne : D.Nonempty := by
    rcases D.eq_empty_or_nonempty with h0 | h0
    · exfalso; rw [h0, Finset.sum_empty] at h
      have : (0:ℕ) < 2 ^ n := by positivity
      omega
    · exact h0
  set M := D.max' hne with hM
  have hMmem : M ∈ D := D.max'_mem hne
  -- 2^M ≤ sum
  have hlow : 2 ^ M ≤ 2 ^ n := by
    rw [← h]
    exact Finset.single_le_sum (f := fun d => 2 ^ d) (fun i _ => Nat.zero_le _) hMmem
  -- sum < 2^(M+1)
  have hupp : 2 ^ n < 2 ^ (M + 1) := by
    rw [← h]
    apply Nat.geomSum_lt (by norm_num)
    intro k hk
    have : k ≤ M := D.le_max' k hk
    omega
  have hMn : M = n := by
    have h1 : M ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hlow
    have h2 : n < M + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hupp
    omega
  -- erase n and show empty
  have herase : ∑ d ∈ D.erase n, 2 ^ d = 0 := by
    have hsplit : ∑ d ∈ D, 2 ^ d = 2 ^ n + ∑ d ∈ D.erase n, 2 ^ d := by
      rw [← Finset.sum_erase_add D _ (hMn ▸ hMmem)]
      ring
    omega
  have hempty : D.erase n = ∅ := by
    by_contra hne'
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne'
    have : 0 < ∑ d ∈ D.erase n, 2 ^ d := by
      apply Finset.sum_pos (fun i _ => by positivity) ⟨x, hx⟩
    omega
  have : D = insert n (D.erase n) := (Finset.insert_erase (hMn ▸ hMmem)).symm
  rw [this, hempty]; rfl

-- φ(2^k) = 2^(k-1)
theorem phi_two_pow (k : ℕ) (hk : 1 ≤ k) : φ (2 ^ k) = 2 ^ (k - 1) := by
  rw [Nat.totient_prime_pow Nat.prime_two hk]; norm_num

-- The classification: if φ(m) is divisible by 2^N (N = 2^33) and m < 2^(N+1),
-- then m = 2^N + 1 and this is prime.
theorem core (N : ℕ) (hN : N = 2 ^ 33) (m : ℕ) (hm0 : 0 < m)
    (hdvd : 2 ^ N ∣ φ m) (hlt : m < 2 ^ (N + 1)) :
    m = 2 ^ N + 1 ∧ Nat.Prime (2 ^ N + 1) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  -- φ m ≥ 2^N
  have hphipos : 0 < φ m := Nat.totient_pos.mpr hm0
  have hge : 2 ^ N ≤ φ m := Nat.le_of_dvd hphipos hdvd
  have hm2 : 2 ≤ m := by
    by_contra h
    have : m = 1 := by omega
    rw [this, Nat.totient_one] at hge
    have : (2:ℕ) ^ N ≤ 1 := hge
    have : (2:ℕ) ≤ 2 ^ N := by
      calc (2:ℕ) = 2 ^ 1 := by ring
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hNpos
    omega
  -- φ m < m
  have hphilt : φ m < m := Nat.totient_lt m hm2
  -- φ m = 2^N
  have hphi : φ m = 2 ^ N := by
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at hk; simp at hk; omega
      · exact h
    have hk2 : k < 2 := by
      by_contra h
      push_neg at h
      have : 2 ^ (N + 1) ≤ φ m := by
        rw [hk, pow_succ]
        exact Nat.mul_le_mul (le_refl _) h
      omega
    rw [hk]
    have : k = 1 := by omega
    rw [this, mul_one]
  -- decompose m = 2^av * u
  set av := m.factorization 2 with havdef
  set u := ordCompl[2] m with hudef
  have hmne : m ≠ 0 := by omega
  have hsplit : 2 ^ av * u = m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have hcop : Nat.Coprime (2 ^ av) u := (Nat.coprime_ordCompl Nat.prime_two hmne).pow_left av
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    have := Nat.not_dvd_ordCompl Nat.prime_two hmne
    omega
  have hupos : 0 < u := Nat.ordCompl_pos 2 hmne
  -- case on av
  rcases Nat.eq_zero_or_pos av with hav0 | havpos
  · -- av = 0, m = u odd
    have hmu : m = u := by rw [← hsplit, hav0]; ring
    rw [hmu] at hphi
    obtain ⟨D, hDprod, hDsum⟩ := oddTotient u huodd N hphi
    -- ∑ 2^d = N = 2^33
    rw [hN] at hDsum
    have hD : D = {33} := sum_two_pow_eq D 33 hDsum.symm
    rw [hD] at hDprod
    simp only [Finset.prod_singleton] at hDprod
    -- u = 2^(2^33)+1 = 2^N+1
    rw [← hN] at hDprod
    have hmeq : m = 2 ^ N + 1 := by rw [hmu, hDprod]
    refine ⟨hmeq, ?_⟩
    -- prime because φ = m - 1
    have hpos : 0 < 2 ^ N + 1 := by positivity
    have hval2 : φ (2 ^ N + 1) = 2 ^ N := by rw [← hmeq, hmu]; exact hphi
    exact (Nat.totient_eq_iff_prime hpos).mp (by rw [hval2]; omega)
  · -- av ≥ 1: m ≥ 2^(N+1), contradiction
    exfalso
    have hphi2 : φ (2 ^ av) = 2 ^ (av - 1) := phi_two_pow av havpos
    have hmul : φ m = 2 ^ (av - 1) * φ u := by
      rw [← hsplit, Nat.totient_mul hcop, hphi2]
    rw [hphi] at hmul
    -- 2^N = 2^(av-1) * φ u
    have huge : φ u ≤ u := Nat.totient_le u
    have key : 2 ^ av = 2 ^ (av - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    have heq : 2 ^ av * φ u = 2 ^ (N + 1) := by
      calc 2 ^ av * φ u = (2 ^ (av - 1) * 2) * φ u := by rw [key]
      _ = (2 ^ (av - 1) * φ u) * 2 := by ring
      _ = 2 ^ N * 2 := by rw [← hmul]
      _ = 2 ^ (N + 1) := by rw [pow_succ]
    have : 2 ^ (N + 1) ≤ m := by
      rw [← hsplit]
      calc 2 ^ (N + 1) = 2 ^ av * φ u := heq.symm
      _ ≤ 2 ^ av * u := Nat.mul_le_mul (le_refl _) huge
    omega

-- General lower bound: any m with 2^N ∣ φ(m) satisfies m ≥ 2^N + 1.
theorem lower_bound (N : ℕ) (hNpos : 0 < N) (m : ℕ) (hm0 : 0 < m)
    (hdvd : 2 ^ N ∣ φ m) : 2 ^ N + 1 ≤ m := by
  have hphipos : 0 < φ m := Nat.totient_pos.mpr hm0
  have hge : 2 ^ N ≤ φ m := Nat.le_of_dvd hphipos hdvd
  have hm2 : 2 ≤ m := by
    by_contra h
    have hm1 : m = 1 := by omega
    rw [hm1, Nat.totient_one] at hge
    have : (2:ℕ) ≤ 2 ^ N := by
      calc (2:ℕ) = 2 ^ 1 := by ring
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hNpos
    omega
  have hphilt : φ m < m := Nat.totient_lt m hm2
  omega

-- Main computation for the value of `a` at `N = 2^33`, with `N` kept opaque.
theorem clean (N : ℕ) (hN : N = 2 ^ 33) :
    sInf { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m }
      = if Nat.Prime (2 ^ N + 1) then 2 ^ N + 1 else 2 ^ (N + 1) := by
  have hNpos : 0 < N := by rw [hN]; positivity
  set S := { m : ℕ | m > 0 ∧ 2 ^ N ∣ totient m } with hSdef
  -- φ(2^(N+1)) = 2^N
  have hphiNp1 : φ (2 ^ (N + 1)) = 2 ^ N := by
    rw [phi_two_pow (N + 1) (by omega), Nat.add_sub_cancel]
  by_cases hp : Nat.Prime (2 ^ N + 1)
  · -- prime case: answer is 2^N + 1
    rw [if_pos hp]
    have hmemS : (2 ^ N + 1) ∈ S := by
      refine ⟨by positivity, ?_⟩
      have : φ (2 ^ N + 1) = 2 ^ N := by
        rw [Nat.totient_prime hp]; omega
      rw [this]
    apply le_antisymm
    · exact Nat.sInf_le hmemS
    · apply le_csInf ⟨_, hmemS⟩
      intro b hb
      exact lower_bound N hNpos b hb.1 hb.2
  · -- composite case: answer is 2^(N+1)
    rw [if_neg hp]
    have hmemS : (2 ^ (N + 1)) ∈ S := by
      refine ⟨by positivity, ?_⟩
      rw [hphiNp1]
    apply le_antisymm
    · exact Nat.sInf_le hmemS
    · apply le_csInf ⟨_, hmemS⟩
      intro b hb
      by_contra hlt
      push_neg at hlt
      obtain ⟨hbeq, hbprime⟩ := core N hN b hb.1 hb.2 hlt
      exact hp hbprime

end OEIS53576

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
  have hexp : (2:ℕ) ^ N = 2 ^ (2 ^ N_idx) := by rw [show N = 2 ^ N_idx from rfl]
  have hF33 : F33 = 2 ^ N + 1 := by
    show Nat.fermatNumber N_idx = 2 ^ N + 1
    unfold Nat.fermatNumber
    rw [← hexp]
  rw [hF33]
  exact OEIS53576.clean N rfl
