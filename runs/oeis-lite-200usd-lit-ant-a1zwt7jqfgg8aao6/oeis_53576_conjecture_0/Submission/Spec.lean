import FormalConjectures.Util.ProblemImports

open Nat Set

private lemma sum_two_pow_range (n : ℕ) : ∑ i ∈ Finset.range n, 2^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 1 ≤ 2^k := Nat.one_le_two_pow
      omega

private lemma easy_lb {N b : ℕ} (hN : 1 ≤ N) (hb : 0 < b) (hd : 2^N ∣ b.totient) :
    2^N < b := by
  have hpos : 0 < b.totient := Nat.totient_pos.mpr hb
  have hle : 2^N ≤ b.totient := Nat.le_of_dvd hpos hd
  have h2 : 2 ≤ 2^N := by
    calc 2 = 2^1 := (pow_one 2).symm
    _ ≤ 2^N := Nat.pow_le_pow_right (by norm_num) hN
  have hb2 : 2 ≤ b := by
    by_contra h
    push_neg at h
    interval_cases b
    rw [Nat.totient_one] at hle; omega
  have := Nat.totient_lt b hb2
  omega

private lemma even_lb {N b : ℕ} (hN : 1 ≤ N) (hb : 0 < b) (hev : 2 ∣ b)
    (hd : 2^N ∣ b.totient) : 2^(N+1) ≤ b := by
  set a := b.factorization 2 with ha
  set d := b / 2 ^ a with hd_def
  have hbne : b ≠ 0 := hb.ne'
  have ha1 : 1 ≤ a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hbne).mp hev
  have hbeq : 2 ^ a * d = b := Nat.ordProj_mul_ordCompl_eq_self b 2
  have hcop : (2 ^ a).Coprime d := (Nat.coprime_ordCompl Nat.prime_two hbne).pow_left a
  have hdpos : 0 < d := Nat.ordCompl_pos 2 hbne
  have hphi : b.totient = (2 ^ a).totient * d.totient := by
    rw [← hbeq, Nat.totient_mul hcop]
  have hphi2 : (2 ^ a).totient = 2 ^ (a - 1) := by
    obtain ⟨c, hc⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
    rw [hc, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  set e := d.totient.factorization 2 with he
  set o := d.totient / 2 ^ e with ho_def
  have hdtne : d.totient ≠ 0 := (Nat.totient_pos.mpr hdpos).ne'
  have hoeq : 2 ^ e * o = d.totient := Nat.ordProj_mul_ordCompl_eq_self d.totient 2
  have hcop2 : (2 : ℕ).Coprime o := Nat.coprime_ordCompl Nat.prime_two hdtne
  have hphiB : b.totient = 2 ^ (a - 1 + e) * o := by
    rw [hphi, hphi2, ← hoeq]; rw [pow_add]; ring
  have hcopN : (2 ^ N).Coprime o := hcop2.pow_left N
  have hdvd2 : 2 ^ N ∣ 2 ^ (a - 1 + e) := by
    have hh : (2 : ℕ) ^ N ∣ 2 ^ (a - 1 + e) * o := by rw [← hphiB]; exact hd
    exact hcopN.dvd_of_dvd_mul_right hh
  have hNle : N ≤ a - 1 + e := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd2
  have h2e : 2 ^ e ≤ d := by
    have h1 : 2 ^ e ∣ d.totient := Nat.ordProj_dvd d.totient 2
    have h2 : 2 ^ e ≤ d.totient := Nat.le_of_dvd (Nat.totient_pos.mpr hdpos) h1
    exact le_trans h2 (Nat.totient_le d)
  calc 2 ^ (N + 1) ≤ 2 ^ (a + e) := by
        apply Nat.pow_le_pow_right (by norm_num); omega
    _ = 2 ^ a * 2 ^ e := by rw [pow_add]
    _ ≤ 2 ^ a * d := by apply Nat.mul_le_mul_left; exact h2e
    _ = b := hbeq

private lemma odd_struct (N m : ℕ) (hN : N = 2 ^ 33) (hm : 0 < m) (hodd : ¬ 2 ∣ m)
    (hd : 2 ^ N ∣ m.totient) (hlt : m < 2 ^ (N + 1))
    (hF : ¬ (Nat.fermatNumber 33).Prime) : False := by
  set P := m.primeFactors with hP
  have hmne : m ≠ 0 := hm.ne'
  have hpprime : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hpdvd : ∀ p ∈ P, p ∣ m := fun p hp => (Nat.mem_primeFactors.mp hp).2.1
  have hpodd : ∀ p ∈ P, p ≠ 2 := by
    intro p hp h2
    exact hodd (h2 ▸ hpdvd p hp)
  have hp3 : ∀ p ∈ P, 3 ≤ p := by
    intro p hp
    have h2le := (hpprime p hp).two_le
    rcases lt_or_eq_of_le h2le with h | h
    · omega
    · exact absurd h.symm (hpodd p hp)
  have hp1ne : ∀ p ∈ P, p - 1 ≠ 0 := by intro p hp; have := hp3 p hp; omega
  -- totient decomposition
  have htot : m.totient = (m / ∏ p ∈ P, p) * ∏ p ∈ P, (p - 1) :=
    Nat.totient_eq_div_primeFactors_mul m
  set R := ∏ p ∈ P, p with hR
  set Q := ∏ p ∈ P, (p - 1) with hQ
  set O := m / R with hO
  have hRdvd : R ∣ m := Nat.prod_primeFactors_dvd m
  have hOR : O * R = m := Nat.div_mul_cancel hRdvd
  have hOdvd : O ∣ m := ⟨R, hOR.symm⟩
  have hOodd : ¬ 2 ∣ O := fun h => hodd (dvd_trans h hOdvd)
  have hcopO : (2 ^ N).Coprime O :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hOodd).pow_left _
  have hdQ : 2 ^ N ∣ Q := by
    have hh : (2:ℕ)^N ∣ O * Q := by rw [← htot]; exact hd
    exact hcopO.dvd_of_dvd_mul_left hh
  have hQne : Q ≠ 0 := by
    rw [hQ]; exact Finset.prod_ne_zero_iff.mpr (fun p hp => hp1ne p hp)
  -- sum of 2-adic valuations ≥ N
  have hsumge : N ≤ ∑ p ∈ P, (p - 1).factorization 2 := by
    have h1 : N ≤ Q.factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hQne).mp hdQ
    have h2 : Q.factorization 2 = ∑ p ∈ P, (p - 1).factorization 2 := by
      rw [hQ]; exact Nat.factorization_prod_apply (fun p hp => hp1ne p hp)
    omega
  -- product lower bound: 2^S * C ≤ R
  set C := ∏ p ∈ P, (p - 1) / 2 ^ ((p - 1).factorization 2) with hCdef
  have hprodle :
      (2 ^ (∑ p ∈ P, (p - 1).factorization 2)) * C ≤ R := by
    rw [hR, hCdef]
    calc 2 ^ (∑ p ∈ P, (p - 1).factorization 2)
            * ∏ p ∈ P, (p - 1) / 2 ^ ((p - 1).factorization 2)
        = (∏ p ∈ P, 2 ^ ((p - 1).factorization 2))
            * ∏ p ∈ P, (p - 1) / 2 ^ ((p - 1).factorization 2) := by
          rw [Finset.prod_pow_eq_pow_sum]
      _ = ∏ p ∈ P, (2 ^ ((p - 1).factorization 2)
            * ((p - 1) / 2 ^ ((p - 1).factorization 2))) := by
          rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ p ∈ P, p := by
          apply Finset.prod_le_prod'
          intro p hp
          have hsp := Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
          have := hp3 p hp
          omega
  have hRle : R ≤ m := Nat.le_of_dvd hm hRdvd
  have hCpos : 1 ≤ C := by
    rw [hCdef]; exact Finset.one_le_prod' (fun p hp => Nat.ordCompl_pos 2 (hp1ne p hp))
  have h2NS : (2:ℕ)^N ≤ 2 ^ (∑ p ∈ P, (p - 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hsumge
  have hchain : 2 ^ N * C ≤ m :=
    le_trans (by gcongr) (le_trans hprodle hRle)
  have hlt2 : 2 ^ N * C < 2 ^ N * 2 := by
    have hh : 2 ^ N * C < 2 ^ (N + 1) := lt_of_le_of_lt hchain hlt
    rwa [pow_succ] at hh
  have hClt : C < 2 := Nat.lt_of_mul_lt_mul_left hlt2
  have hC1 : C = 1 := by omega
  -- each c_p = 1, hence p = 2^(t p) + 1
  have hcp1 : ∀ p ∈ P, (p - 1) / 2 ^ ((p - 1).factorization 2) = 1 := by
    intro p hp
    have hdvd : ((p - 1) / 2 ^ ((p - 1).factorization 2)) ∣ C := by
      rw [hCdef]; exact Finset.dvd_prod_of_mem _ hp
    exact Nat.dvd_one.mp (hC1 ▸ hdvd)
  have hpeq : ∀ p ∈ P, p = 2 ^ ((p - 1).factorization 2) + 1 := by
    intro p hp
    have hsp := Nat.ordProj_mul_ordCompl_eq_self (p - 1) 2
    rw [hcp1 p hp, mul_one] at hsp
    have := hp3 p hp
    omega
  have htne : ∀ p ∈ P, (p - 1).factorization 2 ≠ 0 := by
    intro p hp
    have hpo : Odd p := (hpprime p hp).odd_of_ne_two (hpodd p hp)
    obtain ⟨k, hk⟩ := hpo
    have h2dvd : (2:ℕ) ∣ (p - 1) := by exact ⟨k, by omega⟩
    have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (hp1ne p hp)).mp h2dvd
    omega
  -- each p is a fermat number F_j with j ≤ 32
  have hfermat : ∀ p ∈ P, ∃ j, (p - 1).factorization 2 = 2 ^ j ∧ j ≤ 32 := by
    intro p hp
    have hpe := hpeq p hp
    have htn := htne p hp
    have hprime' : (2 ^ ((p - 1).factorization 2) + 1).Prime := by
      rw [← hpe]; exact hpprime p hp
    obtain ⟨j, hj⟩ := Nat.pow_of_pow_add_prime (a := 2) (by norm_num) htn hprime'
    refine ⟨j, hj, ?_⟩
    have hpval : p = 2 ^ (2 ^ j) + 1 := by rw [hpe, hj]
    have hpf : p = Nat.fermatNumber j := by rw [hpval]; rfl
    have hpm : p ≤ m := Nat.le_of_dvd hm (hpdvd p hp)
    have hpltN : p < 2 ^ (N + 1) := lt_of_le_of_lt hpm hlt
    rw [hpval] at hpltN
    have hA : 2 ^ (2 ^ j) < 2 ^ (N + 1) := lt_of_le_of_lt (Nat.le_succ _) hpltN
    have hjlt : 2 ^ j < N + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hA
    have hjleN : (2:ℕ) ^ j ≤ N := by omega
    rw [hN] at hjleN
    have hjle33 : j ≤ 33 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hjleN
    by_cases hj33 : j = 33
    · exfalso
      apply hF
      have hpr : (Nat.fermatNumber 33).Prime := by
        rw [show (33:ℕ) = j from hj33.symm, ← hpf]; exact hpprime p hp
      exact hpr
    · omega
  -- injectivity of t on P
  have hinj : Set.InjOn (fun p => (p - 1).factorization 2) (↑P : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Finset.mem_coe.mp hp
    have hq' := Finset.mem_coe.mp hq
    simp only [] at hpq
    rw [hpeq p hp', hpeq q hq', hpq]
  -- sum bound ≤ 2^33 - 1
  have hbound : ∑ p ∈ P, (p - 1).factorization 2 ≤ 2 ^ 33 - 1 := by
    have himg : (P.image (fun p => (p - 1).factorization 2))
        ⊆ (Finset.range 33).image (fun j => 2 ^ j) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨j, hj, hj32⟩ := hfermat p hp
      rw [Finset.mem_image]
      exact ⟨j, Finset.mem_range.mpr (by omega), hj.symm⟩
    have hinjpow : Set.InjOn (fun j => (2:ℕ) ^ j) (↑(Finset.range 33) : Set ℕ) :=
      fun a _ b _ h => Nat.pow_right_injective (by norm_num) h
    calc ∑ p ∈ P, (p - 1).factorization 2
        = ∑ x ∈ P.image (fun p => (p - 1).factorization 2), x := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ x ∈ (Finset.range 33).image (fun j => 2 ^ j), x :=
          Finset.sum_le_sum_of_subset himg
      _ = ∑ j ∈ Finset.range 33, 2 ^ j := by rw [Finset.sum_image hinjpow]
      _ = 2 ^ 33 - 1 := sum_two_pow_range 33
  have key : N ≤ 2 ^ 33 - 1 := le_trans hsumge hbound
  rw [hN] at key
  norm_num at key

private lemma main_helper (N : ℕ) (hN : N = 2 ^ 33) :
    sInf {m : ℕ | m > 0 ∧ 2 ^ N ∣ Nat.totient m}
      = if (Nat.fermatNumber 33).Prime then Nat.fermatNumber 33 else 2 ^ (N + 1) := by
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_two_pow
  set S := {m : ℕ | m > 0 ∧ 2 ^ N ∣ Nat.totient m} with hS
  -- 2^(N+1) ∈ S always
  have hpow2 : Nat.totient (2 ^ (N + 1)) = 2 ^ N := by
    rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp
  have hmem_pow : 2 ^ (N + 1) ∈ S := by
    refine ⟨by positivity, ?_⟩
    rw [hpow2]
  -- lower bound via easy_lb
  have hlow : ∀ b ∈ S, 2 ^ N < b := fun b hb => easy_lb hN1 hb.1 hb.2
  by_cases hp : (Nat.fermatNumber 33).Prime
  · -- prime case: answer = fermatNumber 33 = 2^N + 1
    rw [if_pos hp]
    have hf : Nat.fermatNumber 33 = 2 ^ N + 1 := by rw [Nat.fermatNumber, ← hN]
    have hfprime : (2 ^ N + 1).Prime := hf ▸ hp
    have hmem_f : Nat.fermatNumber 33 ∈ S := by
      refine ⟨by rw [hf]; omega, ?_⟩
      rw [hf, Nat.totient_prime hfprime]
      simp
    apply Nat.le_antisymm
    · exact Nat.sInf_le hmem_f
    · refine le_csInf ⟨_, hmem_f⟩ ?_
      intro b hb
      rw [hf]
      have := hlow b hb
      omega
  · -- composite case: answer = 2^(N+1)
    rw [if_neg hp]
    apply Nat.le_antisymm
    · exact Nat.sInf_le hmem_pow
    · refine le_csInf ⟨_, hmem_pow⟩ ?_
      intro b hb
      by_cases hev : 2 ∣ b
      · exact even_lb hN1 hb.1 hev hb.2
      · by_contra hlt
        push_neg at hlt
        exact odd_struct N b hN hb.1 hev hb.2 hlt hp

/--
A053576: Smallest number $m$ whose Euler totient $\phi(m)$ is divisible by $2^n$.
$$ a(n) = \min \{ m \in \mathbb{N}_{>0} \mid 2^n \mid \phi(m) \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | m > 0 ∧ 2 ^ n ∣ totient m }

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
  show a N = if F33.Prime then F33 else 2 ^ (N + 1)
  rw [a]
  exact main_helper N rfl
