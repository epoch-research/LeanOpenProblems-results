import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 20000
set_option maxHeartbeats 30000000
open Nat Set Finset

/-- A384237: Number of divisors $d$ of $n$ such that $d^d \equiv d \pmod n$. -/
def A384237 (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => (d ^ d) % n = d % n).card

/--
A385391: $a(n)$ is the smallest integer $k$ such that $A384237(k) = n$.
This is formalized using the set infimum ($\mathrm{sInf}$) of the preimage of $n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | A384237 k = n}

/-- A002110(n): The primorial $p_n\#$. Product of the first $n$ primes (0-indexed).
  Note: Nat.nth Nat.Prime 0 = 2, Nat.nth Nat.Prime 1 = 3, etc. -/
noncomputable def A002110 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else (Finset.range n).prod fun i => Nat.nth Nat.Prime i

def unitaryCount (n : ℕ) : ℕ :=
  (n.divisors.filter fun d : ℕ => Nat.Coprime d (n / d)).card

lemma dvd_pred_of_good {n d : ℕ} (hdvd : d ∣ n) (hdpos : 0 < d)
    (h : d ^ d % n = d % n) : n / d ∣ d ^ (d - 1) - 1 := by
  have hmod : d ≡ d ^ d [MOD n] := h.symm
  have hle : d ≤ d ^ d := Nat.le_self_pow (Nat.ne_of_gt hdpos) d
  have hn_dvd : n ∣ d ^ d - d := (Nat.modEq_iff_dvd' hle).1 hmod
  have hpow : d ^ d - d = d * (d ^ (d - 1) - 1) := by
    have hd : d - 1 + 1 = d := by omega
    conv_lhs =>
      rw [show d = d - 1 + 1 by omega]
      rw [pow_succ]
      rw [hd]
    rw [Nat.mul_sub]
    rw [mul_one]
    rw [mul_comm]
  rw [hpow] at hn_dvd
  have hn_eq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  rw [← hn_eq] at hn_dvd
  exact Nat.dvd_of_mul_dvd_mul_left hdpos hn_dvd

lemma good_coprime {n d : ℕ} (hn : n ≠ 0) (hdmem : d ∈ n.divisors)
    (h : d ^ d % n = d % n) : Nat.Coprime d (n / d) := by
  by_contra hc
  rw [Nat.coprime_iff_gcd_eq_one] at hc
  obtain ⟨p, hp, hpdvdg⟩ := Nat.exists_prime_and_dvd hc
  have hpd : p ∣ d := dvd_trans hpdvdg (Nat.gcd_dvd_left d (n / d))
  have hpq : p ∣ n / d := dvd_trans hpdvdg (Nat.gcd_dvd_right d (n / d))
  have hdvd : d ∣ n := by simpa [hn] using hdmem
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
  have hqdiv := dvd_pred_of_good hdvd hdpos h
  have hppred : p ∣ d ^ (d - 1) - 1 := dvd_trans hpq hqdiv
  have hone : p ∣ 1 := by
    by_cases hd1 : d = 1
    · simpa [hd1] using hpd
    · have hdm1 : d - 1 ≠ 0 := by omega
      have hppow : p ∣ d ^ (d - 1) := dvd_pow hpd hdm1
      have hsub := Nat.dvd_sub hppow hppred
      have hx : d ^ (d - 1) - (d ^ (d - 1) - 1) = 1 := by
        have hxp : 0 < d ^ (d - 1) := pow_pos hdpos _
        omega
      simpa [hx] using hsub
  exact hp.not_dvd_one hone

lemma A384237_le_unitaryCount (n : ℕ) : A384237 n ≤ unitaryCount n := by
  unfold A384237 unitaryCount
  by_cases hn : n = 0
  · subst n; simp
  · apply Finset.card_le_card
    intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, good_coprime hn hd.1 hd.2⟩

/-- Linear modular exponentiation, used only as a kernel-efficient reflection device. -/
def powModLin (a e m : ℕ) : ℕ :=
  match e with
  | 0 => 1 % m
  | e + 1 => (powModLin a e m * a) % m

lemma powModLin_eq (a e m : ℕ) : powModLin a e m = a ^ e % m := by
  induction e with
  | zero => simp [powModLin]
  | succ e ih => simp [powModLin, ih, Nat.pow_succ, Nat.mul_mod]

def goodA384237 (n d : ℕ) : Bool :=
  (!(d == 0)) && ((n % d) == 0) && ((powModLin d d n) == (d % n))

lemma goodA384237_eq_true {n d : ℕ} :
    goodA384237 n d = true ↔ d ≠ 0 ∧ n % d = 0 ∧ powModLin d d n = d % n := by
  by_cases hd : d = 0
  · subst d; simp [goodA384237]
  · simp [goodA384237, hd]

def countGoodA384237 (n t : ℕ) : ℕ :=
  match t with
  | 0 => 0
  | d + 1 => if goodA384237 n (d + 1) then countGoodA384237 n d + 1 else countGoodA384237 n d

lemma countGoodA384237_eq_card (n t : ℕ) :
    countGoodA384237 n t = ((Finset.range (t + 1)).filter fun d => goodA384237 n d).card := by
  induction t with
  | zero =>
      have hg0 : goodA384237 n 0 = false := by rw [Bool.eq_false_iff]; simp [goodA384237_eq_true]
      have hempty : ({d ∈ ({0} : Finset ℕ) | goodA384237 n d = true}) = ∅ := by
        ext x; by_cases hx : x = 0 <;> simp [hx, hg0]
      simp [countGoodA384237, hempty]
  | succ t ih =>
      rw [Finset.range_add_one]
      rw [Finset.filter_insert]
      have hnot : t + 1 ∉ (Finset.range (t + 1)).filter fun d => goodA384237 n d = true := by simp
      by_cases hg : goodA384237 n (t + 1) = true
      · rw [if_pos hg, Finset.card_insert_of_notMem hnot]
        simp [countGoodA384237, ih, hg]
      · rw [if_neg hg]
        simp [countGoodA384237, ih, hg]

def A384237Loop (n : ℕ) : ℕ := countGoodA384237 n n

lemma A384237_eq_loop (n : ℕ) : A384237 n = A384237Loop n := by
  unfold A384237 A384237Loop
  rw [countGoodA384237_eq_card]
  apply congrArg Finset.card
  ext d
  by_cases hn : n = 0
  · subst n; simp [goodA384237_eq_true]; omega
  · simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      rcases h with ⟨hdivmem, hpow⟩
      have hdvd : d ∣ n := by simpa [hn] using hdivmem
      have hdne : d ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn))
      have hle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
      refine ⟨by omega, ?_⟩
      rw [goodA384237_eq_true]
      refine ⟨hdne, Nat.mod_eq_zero_of_dvd hdvd, ?_⟩
      rwa [powModLin_eq]
    · intro h
      rcases h with ⟨hrange, hgood⟩
      rw [goodA384237_eq_true] at hgood
      rcases hgood with ⟨hdne, hmod, hpow⟩
      constructor
      · have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero hmod
        simpa [hn] using hdvd
      · rwa [powModLin_eq] at hpow

lemma primeFactors_subset_of_dvd {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : d.primeFactors ⊆ n.primeFactors := by
  intro p hp
  have pp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  exact Nat.mem_primeFactors.2 ⟨pp, dvd_trans hpd hd, hn⟩

lemma unitary_inj_primeFactors {n : ℕ} (hn : n ≠ 0) :
    Set.InjOn (fun d : ℕ => d.primeFactors)
      ↑(n.divisors.filter fun d : ℕ => Nat.Coprime d (n / d)) := by
  intro d hd e he hpf
  rw [Finset.mem_coe, Finset.mem_filter] at hd he
  have hddvd : d ∣ n := by simpa [hn] using hd.1
  have hedvd : e ∣ n := by simpa [hn] using he.1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hddvd (Nat.pos_of_ne_zero hn)
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos hedvd (Nat.pos_of_ne_zero hn)
  apply Nat.eq_of_factorization_eq (Nat.ne_of_gt hdpos) (Nat.ne_of_gt hepos)
  intro p
  by_cases hpp : Nat.Prime p
  · by_cases hpd : p ∈ d.primeFactors
    · have hpe : p ∈ e.primeFactors := by simpa [hpf] using hpd
      have hd_mul : d * (n / d) = n := Nat.mul_div_cancel' hddvd
      have he_mul : e * (n / e) = n := Nat.mul_div_cancel' hedvd
      have hd_factor : d.factorization p = n.factorization p := by
        rw [← hd_mul]
        symm
        exact Nat.factorization_eq_of_coprime_left hd.2 (by simpa [Nat.mem_primeFactorsList] using hpd)
      have he_factor : e.factorization p = n.factorization p := by
        rw [← he_mul]
        symm
        exact Nat.factorization_eq_of_coprime_left he.2 (by simpa [Nat.mem_primeFactorsList] using hpe)
      omega
    · have hpe : p ∉ e.primeFactors := by simpa [hpf] using hpd
      have hpdvd : ¬ p ∣ d := by
        intro h; exact hpd (Nat.mem_primeFactors.2 ⟨hpp, h, Nat.ne_of_gt hdpos⟩)
      have hpedvd : ¬ p ∣ e := by
        intro h; exact hpe (Nat.mem_primeFactors.2 ⟨hpp, h, Nat.ne_of_gt hepos⟩)
      rw [(Nat.factorization_eq_zero_iff d p).2 (Or.inr (Or.inl hpdvd)),
          (Nat.factorization_eq_zero_iff e p).2 (Or.inr (Or.inl hpedvd))]
  · simp [Nat.factorization_eq_zero_of_not_prime, hpp]

lemma unitaryCount_le_pow_primeFactors (n : ℕ) : unitaryCount n ≤ 2 ^ n.primeFactors.card := by
  unfold unitaryCount
  by_cases hn : n = 0
  · subst n; simp
  · calc
      #(n.divisors.filter fun d : ℕ => Nat.Coprime d (n / d))
          = #((n.divisors.filter fun d : ℕ => Nat.Coprime d (n / d)).image (fun d => d.primeFactors)) := by
              rw [Finset.card_image_of_injOn (unitary_inj_primeFactors hn)]
      _ ≤ #n.primeFactors.powerset := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_image, Finset.mem_filter] at hs
        rcases hs with ⟨d, hd, rfl⟩
        rw [Finset.mem_powerset]
        exact primeFactors_subset_of_dvd hn (by simpa [hn] using hd.1)
      _ = 2 ^ n.primeFactors.card := by rw [Finset.card_powerset]

def smallPrimes : Finset ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283].toFinset

def smallOmega (n : ℕ) : ℕ := (smallPrimes.filter fun p => n % p = 0).card

lemma prod_primeFactors_subset_dvd {n : ℕ} (hn : n ≠ 0) {t : Finset ℕ} (ht : t ⊆ n.primeFactors) :
    (∏ p ∈ t, p) ∣ n := by
  have hsub : (∏ p ∈ t, p) ∣ ∏ p ∈ n.primeFactors, p :=
    Finset.prod_dvd_prod_of_subset t n.primeFactors (fun p => p) ht
  have hpow : (∏ p ∈ n.primeFactors, p) ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hpos : 1 ≤ n.factorization p := by
      exact Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn (Nat.dvd_of_mem_primeFactors hp)
    simpa using Nat.pow_dvd_pow p hpos
  have hprod : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa using (Nat.prod_pow_primeFactors_factorization hn).symm
  exact dvd_trans hsub (dvd_trans hpow (by rw [hprod]))

lemma prod_ge_two_pow {s : Finset ℕ} (h : ∀ x ∈ s, 2 ≤ x) : 2 ^ s.card ≤ ∏ x ∈ s, x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.card_insert_of_notMem has, pow_succ, Finset.prod_insert has]
      rw [mul_comm (2 ^ #s) 2]
      exact Nat.mul_le_mul (h a (by simp)) (ih (by intro x hx; exact h x (by simp [hx])))

lemma prime_in_small_of_four {n p : ℕ} (hnlt : n < 2310) {t : Finset ℕ}
    (htsub : t ⊆ n.primeFactors) (hcard : t.card = 4) (hpt : p ∈ t) : p ∈ smallPrimes := by
  have hn : n ≠ 0 := by
    intro hn0
    have hp0 := htsub hpt
    simp [hn0] at hp0
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors (htsub hpt)
  have hpdvdprod : p * (∏ q ∈ t.erase p, q) = ∏ q ∈ t, q := by
    rw [← Finset.insert_erase hpt]
    rw [Finset.prod_insert]
    · simp
    · simp
  have hprod_dvd := prod_primeFactors_subset_dvd hn htsub
  have hprod_le_n : ∏ q ∈ t, q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod_dvd
  have herase_card : (t.erase p).card = 3 := by rw [Finset.card_erase_of_mem hpt, hcard]
  have hge : 2 ^ (t.erase p).card ≤ ∏ q ∈ t.erase p, q := by
    apply prod_ge_two_pow
    intro q hq
    exact Nat.Prime.two_le (Nat.prime_of_mem_primeFactors (htsub (by simpa using Finset.mem_of_mem_erase hq)))
  have hp_bound : p * 8 ≤ n := by
    have : 8 ≤ ∏ q ∈ t.erase p, q := by simpa [herase_card] using hge
    nlinarith
  have hp_le : p ≤ 288 := by nlinarith
  interval_cases p
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · decide
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime
  · norm_num [Nat.Prime] at hpprime

lemma primeFactors_card_le_three_of_smallOmega_lt_four {n : ℕ} (hnlt : n < 2310)
    (hsmall : smallOmega n < 4) : n.primeFactors.card ≤ 3 := by
  by_contra hnot
  have h4 : 4 ≤ n.primeFactors.card := by omega
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq h4
  have ht_small : t ⊆ smallPrimes.filter fun p => n % p = 0 := by
    intro p hp
    rw [Finset.mem_filter]
    have hpin := htsub hp
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpin
    exact ⟨prime_in_small_of_four hnlt htsub htcard hp, Nat.mod_eq_zero_of_dvd hpdvd⟩
  have hle : 4 ≤ smallOmega n := by
    rw [← htcard]
    exact Finset.card_le_card ht_small
  omega


/-- A useful way to prove the value of the least `k` with a given `A384237` value. -/
lemma a_eq_of_min {n m : ℕ} (hm : A384237 m = n)
    (hmin : ∀ k < m, A384237 k ≠ n) : a n = m := by
  unfold a
  classical
  have hs : ({k : ℕ | A384237 k = n} : Set ℕ).Nonempty := ⟨m, hm⟩
  rw [Nat.sInf_def hs]
  exact (@Nat.find_eq_iff m (fun k => k ∈ {k : ℕ | A384237 k = n})
    (fun k => Classical.propDecidable (k ∈ {k : ℕ | A384237 k = n})) hs).2 ⟨hm, hmin⟩

lemma a_eq_of_min_loop {n m : ℕ} (hm : A384237Loop m = n)
    (hmin : ∀ k < m, A384237Loop k ≠ n) : a n = m := by
  apply a_eq_of_min
  · rwa [A384237_eq_loop]
  · intro k hk h
    have h' : A384237Loop k = n := by
      rwa [A384237_eq_loop k] at h
    exact hmin k hk h'

lemma unitaryCount_lt_ten_of_primeFactors_card_le_three (n : ℕ)
    (h : n.primeFactors.card ≤ 3) : unitaryCount n < 10 := by
  have hu := unitaryCount_le_pow_primeFactors n
  have hp : 2 ^ n.primeFactors.card ≤ 8 := by
    have hc : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
        n.primeFactors.card = 2 ∨ n.primeFactors.card = 3 := by omega
    rcases hc with h0 | h1 | h2 | h3
    · simp [h0]
    · simp [h1]
    · simp [h2]
    · simp [h3]
  omega
def candSmall4 : List ℕ :=
  [0, 210, 330, 390, 420, 462, 510, 546, 570, 630, 660, 690, 714, 770, 780, 798, 840, 858, 870, 910, 924, 930, 966, 990, 1020, 1050, 1092, 1110, 1122, 1140, 1155, 1170, 1190, 1218, 1230, 1254, 1260, 1290, 1302, 1320, 1326, 1330, 1365, 1380, 1386, 1410, 1428, 1430, 1470, 1482, 1518, 1530, 1540, 1554, 1560, 1590, 1596, 1610, 1638, 1650, 1680, 1710, 1716, 1722, 1740, 1770, 1785, 1794, 1806, 1820, 1830, 1848, 1860, 1870, 1890, 1914, 1932, 1938, 1950, 1974, 1980, 1995, 2002, 2010, 2030, 2040, 2046, 2070, 2090, 2100, 2130, 2142, 2145, 2170, 2184, 2190, 2210, 2220, 2226, 2244, 2262, 2280]

opaque small_screen_0 : ∀ k < 200, k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hk hmem
  interval_cases k
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_1 : ∀ k, 200 ≤ k → k < 400 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_2 : ∀ k, 400 ≤ k → k < 600 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_3 : ∀ k, 600 ≤ k → k < 800 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide

opaque small_screen_4 : ∀ k, 800 ≤ k → k < 1000 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_5 : ∀ k, 1000 ≤ k → k < 1200 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_6 : ∀ k, 1200 ≤ k → k < 1400 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_7 : ∀ k, 1400 ≤ k → k < 1600 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide

opaque small_screen_8 : ∀ k, 1600 ≤ k → k < 1800 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_9 : ∀ k, 1800 ≤ k → k < 2000 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide

opaque small_screen_10 : ∀ k, 2000 ≤ k → k < 2200 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

opaque small_screen_11 : ∀ k, 2200 ≤ k → k < 2310 → k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hkl hk hmem
  interval_cases k
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · simp [candSmall4] at hmem
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

lemma small_screen_all : ∀ k < 2310, k ∉ candSmall4 → smallOmega k < 4 := by
  intro k hk hmem
  by_cases h0 : k < 200
  · exact small_screen_0 k h0 hmem
  by_cases h1 : k < 400
  · exact small_screen_1 k (by omega) h1 hmem
  by_cases h2 : k < 600
  · exact small_screen_2 k (by omega) h2 hmem
  by_cases h3 : k < 800
  · exact small_screen_3 k (by omega) h3 hmem
  by_cases h4 : k < 1000
  · exact small_screen_4 k (by omega) h4 hmem
  by_cases h5 : k < 1200
  · exact small_screen_5 k (by omega) h5 hmem
  by_cases h6 : k < 1400
  · exact small_screen_6 k (by omega) h6 hmem
  by_cases h7 : k < 1600
  · exact small_screen_7 k (by omega) h7 hmem
  by_cases h8 : k < 1800
  · exact small_screen_8 k (by omega) h8 hmem
  by_cases h9 : k < 2000
  · exact small_screen_9 k (by omega) h9 hmem
  by_cases h10 : k < 2200
  · exact small_screen_10 k (by omega) h10 hmem
  exact small_screen_11 k (by omega) hk hmem

def checkAList (target : ℕ) : List ℕ → Bool
| [] => true
| k :: ks => (!(A384237Loop k == target)) && checkAList target ks

lemma checkAList_correct {target k : ℕ} {L : List ℕ} (h : checkAList target L = true)
    (hk : k ∈ L) : A384237Loop k ≠ target := by
  induction L with
  | nil => simp at hk
  | cons y ys ih =>
      simp [checkAList, Bool.and_eq_true] at h
      rcases h with ⟨hy, hys⟩
      simp at hk
      rcases hk with rfl | hk
      · simpa using hy
      · exact ih hys hk

lemma candSmall4_A_cert : checkAList 10 candSmall4 = true := by rfl

lemma h10_min : ∀ k < 2310, A384237 k ≠ 10 := by
  intro k hk hA
  by_cases hmem : k ∈ candSmall4
  · have hloopne := checkAList_correct candSmall4_A_cert hmem
    have hloop : A384237Loop k = 10 := by
      rwa [A384237_eq_loop k] at hA
    exact hloopne hloop
  · have hs := small_screen_all k hk hmem
    have hpf := primeFactors_card_le_three_of_smallOmega_lt_four hk hs
    have hu := unitaryCount_lt_ten_of_primeFactors_card_le_three k hpf
    have hlt : A384237 k < 10 := lt_of_le_of_lt (A384237_le_unitaryCount k) hu
    exact (Nat.ne_of_lt hlt) hA

/--
oeis_385391_conjecture_0: A385391 a(1) = A002110(0), a(2) = A002110(1), a(3) = A002110(2), a(6) = A002110(3), a(7) = A002110(4), a(10) = A002110(5), ...?
This conjecture is formalized as a conjunction of the listed equalities, implying a general pattern related to A065295.
-/
theorem oeis_385391_conjecture_0 :
  a 1 = A002110 0 ∧
  a 2 = A002110 1 ∧
  a 3 = A002110 2 ∧
  a 6 = A002110 3 ∧
  a 7 = A002110 4 ∧
  a 10 = A002110 5 := by
  have h1 : a 1 = 1 := a_eq_of_min_loop (by decide) (by decide)
  have h2 : a 2 = 2 := a_eq_of_min_loop (by decide) (by decide)
  have h3 : a 3 = 6 := a_eq_of_min_loop (by decide) (by decide)
  have h6 : a 6 = 30 := a_eq_of_min_loop (by decide) (by decide)
  have h7 : a 7 = 210 := a_eq_of_min_loop (by decide) (by decide)
  have hm10 : A384237 2310 = 10 := by
    rw [A384237_eq_loop]
    decide
  have h10 : a 10 = 2310 := a_eq_of_min hm10 h10_min
  simp [h1, h2, h3, h6, h7, h10, A002110, Finset.prod_range_succ]
