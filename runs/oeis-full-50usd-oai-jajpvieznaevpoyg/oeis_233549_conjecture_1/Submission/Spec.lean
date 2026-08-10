import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- A coarse finiteness bound for the inverse image of an initial segment under Euler's totient. -/
lemma Nat.finite_setOf_totient_le (K : ℕ) : Set.Finite {n : ℕ | n.totient ≤ K} := by
  classical
  refine Set.Finite.subset (Set.finite_Iic ((K + 1) ^ ((K + 1) * (K + 2)))) ?_
  intro n hn
  simp only [Set.mem_Iic]
  have hnφ : n.totient ≤ K := by simpa using hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hntotpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hfac_bound : ∀ p ∈ n.primeFactors, p ^ n.factorization p ≤ (K + 1) ^ (K + 1) := by
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
    have hptotdvd : p.totient ∣ n.totient := Nat.totient_dvd_of_dvd hpdvd
    have hptotpos : 0 < p.totient := Nat.totient_pos.mpr hp.pos
    have hptot_le : p.totient ≤ K := (Nat.le_of_dvd hntotpos hptotdvd).trans hnφ
    have hp_le : p ≤ K + 1 := by
      have : p - 1 ≤ K := by simpa [Nat.totient_prime hp] using hptot_le
      omega
    have hepos : 0 < n.factorization p := by
      have : p ^ 1 ∣ n := by simpa using hpdvd
      exact (hp.pow_dvd_iff_le_factorization hn0).mp this
    have hpow_le : p ^ (n.factorization p - 1) ≤ K := by
      have hpowtotdvd : (p ^ n.factorization p).totient ∣ n.totient := by
        exact Nat.totient_dvd_of_dvd ((hp.pow_dvd_iff_le_factorization hn0).2 le_rfl)
      have hpowtotpos : 0 < (p ^ n.factorization p).totient := by
        exact Nat.totient_pos.mpr (pow_pos hp.pos _)
      have hpowtot_le : (p ^ n.factorization p).totient ≤ K :=
        (Nat.le_of_dvd hntotpos hpowtotdvd).trans hnφ
      rw [Nat.totient_prime_pow hp hepos] at hpowtot_le
      exact (Nat.le_mul_of_pos_right (p ^ (n.factorization p - 1)) (Nat.sub_pos_of_lt hp.one_lt)).trans hpowtot_le
    have he_le : n.factorization p ≤ K + 1 := by
      by_contra hle
      have hlt : K + 1 < n.factorization p := Nat.lt_of_not_ge hle
      have hklt : K < n.factorization p - 1 := by omega
      have htwo : 2 ^ (n.factorization p - 1) ≤ p ^ (n.factorization p - 1) :=
        Nat.pow_le_pow_left hp.two_le _
      have hbig : K < p ^ (n.factorization p - 1) :=
        lt_of_lt_of_le (lt_trans hklt (Nat.lt_pow_self (by decide : 1 < 2))) htwo
      exact (not_lt_of_ge hpow_le) hbig
    exact le_trans (Nat.pow_le_pow_left hp_le _)
      (pow_le_pow_right₀ (by omega : 1 ≤ K + 1) he_le)
  calc
    n = ∏ p : n.primeFactors, (p : ℕ) ^ n.factorization (p : ℕ) := Nat.prod_pow_primeFactors_factorization hn0
    _ ≤ ∏ p : n.primeFactors, (K + 1) ^ (K + 1) := by
      exact Finset.prod_le_prod (fun p hp => zero_le _) (fun p hp => hfac_bound p p.property)
    _ = ((K + 1) ^ (K + 1)) ^ n.primeFactors.card := by simp
    _ ≤ ((K + 1) ^ (K + 1)) ^ (K + 2) := by
      refine pow_le_pow_right₀ (one_le_pow₀ (by omega : 1 ≤ K + 1)) ?_
      have hsubset : n.primeFactors ⊆ Finset.range (K + 2) := by
        intro p hpmem
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
        have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
        have hptotdvd : p.totient ∣ n.totient := Nat.totient_dvd_of_dvd hpdvd
        have hptotpos : 0 < p.totient := Nat.totient_pos.mpr hp.pos
        have hptot_le : p.totient ≤ K := (Nat.le_of_dvd hntotpos hptotdvd).trans hnφ
        have hp_le : p ≤ K + 1 := by
          have : p - 1 ≤ K := by simpa [Nat.totient_prime hp] using hptot_le
          omega
        exact Finset.mem_range.mpr (by omega)
      simpa using Finset.card_le_card hsubset
    _ = (K + 1) ^ ((K + 1) * (K + 2)) := by rw [← pow_mul]

/--
A233549: Number of ways to write $n = p + q$ ($q > 0$) with $p$ prime and $(\phi(p)\phi(q))^4 + 1$ prime,
where $\phi(\cdot)$ is Euler's totient function (A000010).
-/
def a (n : ℕ) : ℕ :=
  Finset.card <| Finset.filter (fun p : ℕ =>
    p.Prime ∧
    let q := n - p
    Nat.Prime ((p.totient * q.totient) ^ 4 + 1)
  ) (Finset.range n)

/--
Conjecture: (i) a(n) > 0 for all n > 2.
Part (i) of the conjecture implies that there are infinitely many primes of the form x^4 + 1.
-/
theorem oeis_233549_conjecture_1 :
  (∀ n, 2 < n → 0 < a n) →
  Set.Infinite {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} := by
  classical
  intro h
  rw [Set.infinite_iff_exists_gt]
  intro B
  let badPairs : Set (ℕ × ℕ) := {z | z.1.Prime ∧ 0 < z.2 ∧ z.1.totient * z.2.totient ≤ B}
  have hbadPairs : Set.Finite badPairs := by
    have hpfin : Set.Finite {p : ℕ | p ≤ B + 1} := Set.finite_Iic _
    have hqfin : Set.Finite {q : ℕ | q.totient ≤ B} := Nat.finite_setOf_totient_le B
    refine Set.Finite.subset (hpfin.prod hqfin) ?_
    rintro ⟨p, q⟩ hz
    rcases hz with ⟨hp, hqpos, hmul⟩
    constructor
    · have hptot : p.totient ≤ B := by
        have hp1 : 0 < q.totient := Nat.totient_pos.mpr hqpos
        exact le_trans (Nat.le_mul_of_pos_right p.totient hp1) hmul
      have hp_sub : p - 1 ≤ B := by simpa [Nat.totient_prime hp] using hptot
      have hp_pos : 0 < p := hp.pos
      calc
        p = p - 1 + 1 := (Nat.sub_one_add_one hp_pos.ne').symm
        _ ≤ B + 1 := Nat.add_le_add_right hp_sub 1
    · exact le_trans (Nat.le_mul_of_pos_left q.totient (Nat.totient_pos.mpr hp.pos)) hmul
  let badSums : Set ℕ := (fun z : ℕ × ℕ => z.1 + z.2) '' badPairs
  have hbadSums : Set.Finite badSums := hbadPairs.image _
  obtain ⟨C, hC⟩ := hbadSums.bddAbove
  let n := max (C + 1) 3
  have hn2 : 2 < n := by simp [n]
  have hn_not_bad : n ∉ badSums := by
    intro hnmem
    have hnle : n ≤ C := hC hnmem
    have : C + 1 ≤ n := by simp [n]
    omega
  have ha_pos : 0 < a n := h n hn2
  rw [a, Finset.card_pos] at ha_pos
  rcases ha_pos with ⟨p, hpmem⟩
  rw [Finset.mem_filter] at hpmem
  rcases hpmem with ⟨hprange, hpprime, hrprime⟩
  let q := n - p
  let x := p.totient * q.totient
  let r := x ^ 4 + 1
  have hqpos : 0 < q := by
    exact Nat.sub_pos_of_lt (Finset.mem_range.mp hprange)
  have hrmem : r ∈ {p : ℕ | Nat.Prime p ∧ ∃ x : ℕ, p = x ^ 4 + 1} := by
    exact ⟨hrprime, ⟨x, rfl⟩⟩
  refine ⟨r, hrmem, ?_⟩
  by_contra hnot
  have hrle : r ≤ B := Nat.le_of_not_gt hnot
  have hx_r : x ≤ r := by
    unfold r
    have hxpow : x ≤ x ^ 4 := by
      cases x with
      | zero => simp
      | succ x => exact Nat.le_self_pow (by decide : 4 ≠ 0) (x + 1)
    exact le_trans hxpow (Nat.le_add_right (x ^ 4) 1)
  have hxle : x ≤ B := le_trans hx_r hrle
  have hpair : (p, q) ∈ badPairs := by
    exact ⟨hpprime, hqpos, hxle⟩
  have hsummem : p + q ∈ badSums := ⟨(p, q), hpair, rfl⟩
  have hsum : p + q = n := by
    unfold q
    exact Nat.add_sub_of_le (le_of_lt (Finset.mem_range.mp hprange))
  exact hn_not_bad (hsum ▸ hsummem)
