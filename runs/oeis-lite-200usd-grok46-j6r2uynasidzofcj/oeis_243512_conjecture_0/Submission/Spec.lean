import FormalConjectures.Util.ProblemImports

open Nat ArithmeticFunction Rat Finset

/--
A243473(i) is the difference between the numerator $p$ and the denominator $q$
when the per-unit sum-of-divisors $\sigma_1(i)/i$ is written in its lowest terms $p/q$.
$$ \mathrm{A243473}(i) = \mathrm{num} \left( \frac{\sigma_1(i)}{i} \right) - \mathrm{den} \left( \frac{\sigma_1(i)}{i} \right) $$
-/
def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / i
    -- r.num is Int, r.den is Nat. The subtraction is performed in Int, and then converted to Nat.
    (r.num - (r.den : ℤ)).toNat

/--
A243512: Least index $i$ for which $\mathrm{A243473}(i)=n$, or $0$ if no such index exists.
$$ a(n) = \min \{ i \in \mathbb{N} \mid i > 0 \land \mathrm{A243473}(i) = n \} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- sInf finds the infimum of a set of natural numbers. For a non-empty set of positive integers,
  -- this is the minimum. For an empty set, this returns 0, which matches the OEIS definition.
  sInf {i : ℕ | 0 < i ∧ A243473_val i = n}

-- The example proofs are illustrative only and contain errors, so they are omitted.
-- I will only provide the formalization of the conjecture.

/-- Integer form of `A243473_val`. -/
def Aval (n : ℕ) : ℕ :=
  if n = 0 then 0 else (sigma 1 n - n) / (sigma 1 n).gcd n

lemma sigma_ge_self (n : ℕ) (hn : 0 < n) : n ≤ sigma 1 n := by
  have hin : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  simpa [sigma_one_apply] using
    (Finset.single_le_sum (s := n.divisors) (f := fun d : ℕ => d)
      (fun _ _ => Nat.zero_le _) hin)

lemma rat_div_num (a b : ℕ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num = (a : ℤ) / (b.gcd a) := by
  rw [natCast_div_eq_divInt, divInt_ofNat, num_mkRat]
  simp [hb, Nat.gcd_comm]

lemma rat_div_den (a b : ℕ) (hb : b ≠ 0) :
    ((a : ℚ) / b).den = b / (b.gcd a) := by
  rw [natCast_div_eq_divInt, divInt_ofNat, den_mkRat]
  simp [hb, Nat.gcd_comm]

lemma A_eq (n : ℕ) (hn : 0 < n) :
    (((sigma 1 n : ℚ) / n).num - (((sigma 1 n : ℚ) / n).den : ℤ)).toNat =
      (sigma 1 n - n) / (sigma 1 n).gcd n := by
  have hb : n ≠ 0 := hn.ne'
  rw [rat_div_num _ _ hb, rat_div_den _ _ hb]
  set s := sigma 1 n
  have hg : n.gcd s = s.gcd n := Nat.gcd_comm _ _
  rw [hg]
  set g := s.gcd n
  have hgs : g ∣ s := Nat.gcd_dvd_left _ _
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hsle : n ≤ s := sigma_ge_self n hn
  have hsg : (s : ℤ) / g = ↑(s / g) := Int.natCast_ediv _ _
  rw [hsg]
  have hsub : ((s / g : ℕ) : ℤ) - ((n / g : ℕ) : ℤ) = ↑(s / g - n / g) :=
    (Int.natCast_sub (Nat.div_le_div_right hsle)).symm
  rw [hsub, Int.toNat_natCast]
  refine (Nat.div_eq_of_eq_mul_left ?_ ?_).symm
  · exact Nat.pos_of_dvd_of_pos hgs (sigma_pos_iff.mpr hn)
  · rw [Nat.sub_mul, Nat.div_mul_cancel hgs, Nat.div_mul_cancel hgn]

lemma Aval_pos (n : ℕ) (hn : 0 < n) :
    Aval n = (sigma 1 n - n) / (sigma 1 n).gcd n := by
  simp [Aval, hn.ne']

lemma A243473_val_eq_Aval (i : ℕ) : A243473_val i = Aval i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rfl
  · simp [A243473_val, Aval, hi.ne', A_eq i hi]

lemma a_ne_zero_of_mem {n i : ℕ} (hi : 0 < i) (h : A243473_val i = n) : a n ≠ 0 := by
  have hne : Set.Nonempty {j : ℕ | 0 < j ∧ A243473_val j = n} := ⟨i, hi, h⟩
  have hmem := Nat.sInf_mem hne
  exact hmem.1.ne'

lemma a_ne_zero_of_Aval {n i : ℕ} (hi : 0 < i) (h : Aval i = n) : a n ≠ 0 :=
  a_ne_zero_of_mem hi (by rw [A243473_val_eq_Aval, h])

lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [sigma_one_apply, hp.divisors, sum_insert (by simp [hp.ne_one.symm]),
      sum_singleton, add_comm]

lemma Aval_prime {p : ℕ} (hp : p.Prime) : Aval p = 1 := by
  have hp0 : 0 < p := hp.pos
  rw [Aval_pos p hp0, sigma_prime hp]
  have hgcd : (p + 1).gcd p = 1 := by
    rw [Nat.gcd_comm]
    simpa using (Nat.coprime_self_add_right (m := p) (n := 1)).mpr (Nat.coprime_one_right p)
  simp [hgcd]

lemma gcd_sigma_prime_pow {p a : ℕ} (hp : p.Prime) :
    (sigma 1 (p ^ a)).gcd (p ^ a) = 1 := by
  rw [sigma_one_apply_prime_pow hp]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hcop : (∑ k ∈ range (a + 1), p ^ k).Coprime p := by
    rw [sum_range_succ']
    simp only [pow_zero]
    have : ∑ k ∈ range a, p ^ (k + 1) = p * ∑ k ∈ range a, p ^ k := by
      refine (Finset.sum_congr rfl fun k _ => pow_succ' p k).trans ?_
      simp [mul_comm, mul_sum]
    rw [this, add_comm, Nat.coprime_comm]
    exact (Nat.coprime_add_mul_left_right p 1 (∑ k ∈ range a, p ^ k)).mpr
      (Nat.coprime_one_right p)
  exact Nat.coprime_pow_right_iff ha _ _ |>.mpr hcop

lemma Aval_prime_pow {p a : ℕ} (hp : p.Prime) :
    Aval (p ^ a) = (p ^ a - 1) / (p - 1) := by
  have hpos : 0 < p ^ a := pow_pos hp.pos a
  rw [Aval_pos _ hpos, gcd_sigma_prime_pow hp, Nat.div_one]
  rw [sigma_one_apply_prime_pow hp]
  have hsub : ∑ k ∈ range (a + 1), p ^ k - p ^ a = ∑ k ∈ range a, p ^ k := by
    rw [sum_range_succ, Nat.add_sub_cancel]
  rw [hsub, Nat.geomSum_eq hp.two_le a]

lemma Aval_prime_sq {p : ℕ} (hp : p.Prime) : Aval (p ^ 2) = p + 1 := by
  rw [Aval_prime_pow hp]
  have heq : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    zify [show 1 ≤ p ^ 2 from Nat.one_le_pow 2 p hp.pos,
          show 1 ≤ p from hp.one_le]
    ring
  rw [heq, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp.one_lt)]

lemma Aval_two_pow (e : ℕ) : Aval (2 ^ e) = 2 ^ e - 1 := by
  simpa using Aval_prime_pow Nat.prime_two (a := e)

lemma Aval_one : Aval 1 = 0 := by simp [Aval]

lemma Aval_120 : Aval 120 = 2 := by native_decide

lemma sigma_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigma 1 (2 * p) = 3 * (p + 1) := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime Nat.prime_two, sigma_prime hp]

lemma Aval_two_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Aval (2 * p) = (p + 3) / 2 := by
  have hpos : 0 < 2 * p := Nat.mul_pos (by norm_num) hp.pos
  rw [Aval_pos _ hpos, sigma_two_mul_prime hp hp2]
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hgcd : (3 * (p + 1)).gcd (2 * p) = 2 := by
    have h2 : 2 ∣ (3 * (p + 1)).gcd (2 * p) := by
      refine Nat.dvd_gcd ?_ (dvd_mul_right 2 p)
      have : 2 ∣ p + 1 := even_iff_two_dvd.mp (Odd.add_one hp_odd)
      exact dvd_mul_of_dvd_right this 3
    have hle : (3 * (p + 1)).gcd (2 * p) ∣ 2 := by
      have hdvd : (3 * (p + 1)).gcd (2 * p) ∣ 2 * p := Nat.gcd_dvd_right _ _
      have hcop : Nat.Coprime ((3 * (p + 1)).gcd (2 * p)) p := by
        have hgp : (3 * (p + 1)).gcd p = 1 := by
          have h3 : Nat.Coprime 3 p :=
            (Nat.coprime_primes (by decide : Nat.Prime 3) hp).mpr hp3.symm
          have hp1 : Nat.Coprime (p + 1) p :=
            Nat.coprime_comm.mp
              ((Nat.coprime_self_add_right (m := p) (n := 1)).mpr (Nat.coprime_one_right p))
          exact Nat.coprime_mul_iff_left.mpr ⟨h3, hp1⟩
        exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hgp
      exact Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
    exact Nat.dvd_antisymm hle h2
  rw [hgcd]
  have : 3 * (p + 1) - 2 * p = p + 3 := by
    have : 2 * p ≤ 3 * (p + 1) := by nlinarith [hp.pos]
    zify [this]
    ring
  rw [this]

lemma sigma_six_mul_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    sigma 1 (6 * p) = 12 * (p + 1) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h6p : Nat.Coprime 6 p := by
    rw [show 6 = 2 * 3 from rfl, Nat.coprime_mul_iff_left]
    exact ⟨(Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm,
           (Nat.coprime_primes (by decide : Nat.Prime 3) hp).mpr hp3.symm⟩
  rw [isMultiplicative_sigma.map_mul_of_coprime h6p]
  have hσ6 : sigma 1 6 = 12 := by native_decide
  rw [hσ6, sigma_prime hp]

lemma Aval_six_mul_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    Aval (6 * p) = p + 2 := by
  have hpos : 0 < 6 * p := Nat.mul_pos (by norm_num) hp.pos
  rw [Aval_pos _ hpos, sigma_six_mul_prime hp h3]
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hgcd : (12 * (p + 1)).gcd (6 * p) = 6 := by
    have h6 : 6 ∣ (12 * (p + 1)).gcd (6 * p) :=
      Nat.dvd_gcd ⟨2 * (p + 1), by ring⟩ (dvd_mul_right 6 p)
    have hdvd : (12 * (p + 1)).gcd (6 * p) ∣ 6 * p := Nat.gcd_dvd_right _ _
    have hcop : Nat.Coprime ((12 * (p + 1)).gcd (6 * p)) p := by
      have hgp : (12 * (p + 1)).gcd p = 1 := by
        have h12 : Nat.Coprime 12 p := by
          rw [show 12 = 2 ^ 2 * 3 from rfl, Nat.coprime_mul_iff_left,
              Nat.coprime_pow_left_iff (by norm_num : 0 < 2)]
          exact ⟨(Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm,
                 (Nat.coprime_primes (by decide : Nat.Prime 3) hp).mpr hp3.symm⟩
        have hp1 : Nat.Coprime (p + 1) p :=
          Nat.coprime_comm.mp
            ((Nat.coprime_self_add_right (m := p) (n := 1)).mpr (Nat.coprime_one_right p))
        exact Nat.coprime_mul_iff_left.mpr ⟨h12, hp1⟩
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hgp
    have hle : (12 * (p + 1)).gcd (6 * p) ∣ 6 :=
      Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
    exact Nat.dvd_antisymm hle h6
  rw [hgcd]
  have : 12 * (p + 1) - 6 * p = 6 * (p + 2) := by
    have : 6 * p ≤ 12 * (p + 1) := by nlinarith [hp.pos]
    zify [this]; ring
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)]

/-- `t(n)` is the denominator of `σ(n)/n` in lowest terms. -/
def tval (n : ℕ) : ℕ :=
  if n = 0 then 0 else n / (sigma 1 n).gcd n

lemma tval_pos (n : ℕ) (hn : 0 < n) : tval n = n / (sigma 1 n).gcd n := by
  simp [tval, hn.ne']

lemma gcd_div_sigma_t (n : ℕ) (hn : 0 < n) :
    (sigma 1 n / (sigma 1 n).gcd n).gcd (n / (sigma 1 n).gcd n) = 1 := by
  have hgs : (sigma 1 n).gcd n ∣ sigma 1 n := Nat.gcd_dvd_left _ _
  have hgn : (sigma 1 n).gcd n ∣ n := Nat.gcd_dvd_right _ _
  have hgpos : 0 < (sigma 1 n).gcd n := Nat.gcd_pos_of_pos_right _ hn
  have := Nat.gcd_div hgs hgn
  simpa [Nat.div_self hgpos] using this

lemma div_sub_div_of_dvd {s n g : ℕ} (hgs : g ∣ s) (hgn : g ∣ n)
    (_hnle : n ≤ s) (hgpos : 0 < g) :
    (s - n) / g = s / g - n / g := by
  set sg := s / g
  set ng := n / g
  have hs' : s = g * sg := (Nat.mul_div_cancel' hgs).symm
  have hn' : n = g * ng := (Nat.mul_div_cancel' hgn).symm
  rw [hs', hn', ← Nat.mul_sub_left_distrib, Nat.mul_div_cancel_left _ hgpos]

lemma Aval_eq_div_sub (n : ℕ) (hn : 0 < n) :
    Aval n = sigma 1 n / (sigma 1 n).gcd n - n / (sigma 1 n).gcd n := by
  rw [Aval_pos n hn]
  exact div_sub_div_of_dvd (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    (sigma_ge_self n hn) (Nat.gcd_pos_of_pos_right _ hn)

lemma gcd_Aval_tval (n : ℕ) (hn : 0 < n) : (Aval n).gcd (tval n) = 1 := by
  rw [Aval_eq_div_sub n hn, tval_pos n hn]
  set g := (sigma 1 n).gcd n
  set sg := sigma 1 n / g
  set ng := n / g
  have hle : ng ≤ sg := Nat.div_le_div_right (sigma_ge_self n hn)
  have hcop : sg.gcd ng = 1 := gcd_div_sigma_t n hn
  have heq : (sg - ng).gcd ng = sg.gcd ng := by
    rw [Nat.gcd_comm, ← Nat.gcd_sub_self_left hle, Nat.gcd_comm]
  rw [heq, hcop]

/-- For even `n > 2`, the sum of proper divisors is at least `1 + n/2`. -/
lemma sum_proper_even {n : ℕ} (hn : Even n) (h2 : 2 < n) :
    1 + n / 2 ≤ sigma 1 n - n := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt h2
  have h1lt : 1 < n := Nat.lt_of_succ_lt h2
  have h1 : 1 ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd n, h1lt⟩
  have hhalf_dvd : n / 2 ∣ n := Nat.div_dvd_of_dvd (even_iff_two_dvd.mp hn)
  have hhalf_lt : n / 2 < n := Nat.div_lt_self hn0 (by decide : 1 < 2)
  have hhalf : n / 2 ∈ n.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨hhalf_dvd, hhalf_lt⟩
  have hne : (1 : ℕ) ≠ n / 2 := by
    have : 4 ≤ n := by
      rcases hn with ⟨k, rfl⟩
      omega
    omega
  have hσ : sigma 1 n = ∑ i ∈ n.divisors, i := sigma_one_apply n
  have hproper : sigma 1 n - n = ∑ i ∈ n.properDivisors, i := by
    have : n ≤ sigma 1 n := sigma_ge_self n hn0
    rw [hσ, Nat.sum_divisors_eq_sum_properDivisors_add_self, Nat.add_sub_cancel]
  have hsubset : ({1, n / 2} : Finset ℕ) ⊆ n.properDivisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1
    · exact hhalf
  have hpair : 1 + n / 2 = ∑ i ∈ ({1, n / 2} : Finset ℕ), i := by
    rw [Finset.sum_pair hne]
  rw [hproper, hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)

/-- If `n` is even and `A(n) = k` then `t(n) < 2k`. -/
lemma tval_lt_two_mul_of_even {n k : ℕ} (hn : Even n) (h2 : 2 < n)
    (hA : Aval n = k) : tval n < 2 * k := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt h2
  have hs : 1 + n / 2 ≤ sigma 1 n - n := sum_proper_even hn h2
  have hA' : Aval n = (sigma 1 n - n) / (sigma 1 n).gcd n := Aval_pos n hn0
  have ht : tval n = n / (sigma 1 n).gcd n := tval_pos n hn0
  set s := sigma 1 n
  set g := s.gcd n
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right s hn0
  have hgs : g ∣ s := Nat.gcd_dvd_left _ _
  have hgn : g ∣ n := Nat.gcd_dvd_right _ _
  have hle : n ≤ s := sigma_ge_self n hn0
  have hdiv : g ∣ s - n := by
    obtain ⟨a, ha⟩ := hgs
    obtain ⟨b, hb⟩ := hgn
    have hba : b ≤ a := by
      have : g * b ≤ g * a := by
        rw [← hb, ← ha]; exact hle
      exact Nat.le_of_mul_le_mul_left this hgpos
    refine ⟨a - b, ?_⟩
    rw [ha, hb, Nat.mul_sub_left_distrib]
  have hkg : k * g = s - n := by
    have : Aval n = (s - n) / g := by simpa [s, g] using hA'
    rw [← hA, this, mul_comm]
    exact Nat.mul_div_cancel' hdiv
  have hineq : 1 + n / 2 ≤ k * g := by
    rwa [hkg]
  have he : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn
  have hlt : n < 2 * k * g := by
    have h := Nat.mul_le_mul_left 2 hineq
    have h' : 2 * (1 + n / 2) = 2 + n := by
      rw [mul_add, he]
    have : 2 + n ≤ 2 * (k * g) := by
      rwa [h'] at h
    have : n < 2 * (k * g) := by omega
    simpa [mul_assoc] using this
  have hdivlt : n / g < 2 * k :=
    Nat.div_lt_of_lt_mul (by simpa [mul_comm, mul_left_comm, mul_assoc] using hlt)
  simpa [ht, s, g] using hdivlt

lemma sigma_three_mul_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    sigma 1 (3 * p) = 4 * (p + 1) := by
  have hcop : Nat.Coprime 3 p :=
    (Nat.coprime_primes (by decide : Nat.Prime 3) hp).mpr hp3.symm
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime (by decide : Nat.Prime 3),
      sigma_prime hp]

/-- If `3k - 4` is prime (hence `k` is odd) then `A(3(3k-4)) = k`. -/
lemma Aval_three_mul_of {k : ℕ} (hp : (3 * k - 4).Prime) (h3 : 3 < 3 * k - 4) :
    Aval (3 * (3 * k - 4)) = k := by
  set p := 3 * k - 4
  have hp3 : p ≠ 3 := by omega
  have hp2 : p ≠ 2 := by omega
  have hpos : 0 < 3 * p := Nat.mul_pos (by norm_num) hp.pos
  have hk1 : 1 ≤ k := by omega
  rw [Aval_pos _ hpos, sigma_three_mul_prime hp hp3]
  have hp1 : p + 1 = 3 * (k - 1) := by omega
  rw [hp1, show 4 * (3 * (k - 1)) = 12 * (k - 1) from by ring]
  have hsub : 12 * (k - 1) - 3 * p = 3 * k := by
    have : 3 * p ≤ 12 * (k - 1) := by omega
    zify [this, hk1]
    have : (p : ℤ) = 3 * k - 4 := by omega
    rw [this]; ring
  rw [hsub]
  have hgcd : (12 * (k - 1)).gcd (3 * p) = 3 := by
    have h3pos : 0 < 3 := by norm_num
    have : (12 * (k - 1)).gcd (3 * p) = 3 * (4 * (k - 1)).gcd p := by
      rw [show 12 * (k - 1) = 3 * (4 * (k - 1)) from by ring, Nat.gcd_mul_left]
    rw [this]
    have h1 : (4 * (k - 1)).gcd p = 1 := by
      have hdiv : (4 * (k - 1)).gcd p ∣ p := Nat.gcd_dvd_right _ _
      have hpr : (4 * (k - 1)).gcd p = 1 ∨ (4 * (k - 1)).gcd p = p :=
        (Nat.dvd_prime hp).mp hdiv
      cases hpr with
      | inl h => exact h
      | inr h =>
        have : p ∣ 4 * (k - 1) := by
          rw [← h]; exact Nat.gcd_dvd_left _ _
        have hp4 : ¬ p ∣ 4 := by
          intro hd
          have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd
          interval_cases p <;> contradiction
        have hcop4 : Nat.Coprime p 4 :=
          ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right 2
        have : p ∣ (k - 1) := Nat.Coprime.dvd_of_dvd_mul_left hcop4 this
        -- `p = 3(k-1)-1`, so `p ∣ (k-1)` implies `p ∣ 1`
        have eq : p = 3 * (k - 1) - 1 := by omega
        have : p ∣ 1 := by
          have hle : 1 ≤ 3 * (k - 1) := by omega
          have : p ∣ 3 * (k - 1) := dvd_mul_of_dvd_right this 3
          have : p ∣ 3 * (k - 1) - p := Nat.dvd_sub this (dvd_refl p)
          simpa [eq, Nat.sub_sub_self hle] using this
        exact False.elim ((Nat.Prime.ne_one hp) (Nat.dvd_one.mp this))
    rw [h1, mul_one]
  rw [hgcd, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]

lemma gcd_mul_cancel_coprime_left {a b c : ℕ} (h : Nat.Coprime a c) :
    (a * b).gcd c = b.gcd c := by
  apply Nat.dvd_antisymm
  · have hd1 : (a * b).gcd c ∣ a * b := Nat.gcd_dvd_left _ _
    have hdc : (a * b).gcd c ∣ c := Nat.gcd_dvd_right _ _
    have hcop' : Nat.Coprime ((a * b).gcd c) a :=
      Nat.Coprime.coprime_dvd_left hdc h.symm
    have : (a * b).gcd c ∣ b := Nat.Coprime.dvd_of_dvd_mul_left hcop' hd1
    exact Nat.dvd_gcd this hdc
  · exact Nat.dvd_gcd (dvd_mul_of_dvd_right (Nat.gcd_dvd_left b c) a) (Nat.gcd_dvd_right b c)

lemma sigma_mul_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    sigma 1 (m * p) = sigma 1 m * (p + 1) := by
  have hcop : Nat.Coprime m p :=
    ((Nat.coprime_or_dvd_of_prime hp m).resolve_right hpm).symm
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp]

lemma gcd_sigma_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hps : ¬ p ∣ sigma 1 m) :
    (sigma 1 m * (p + 1)).gcd (m * p) =
      (sigma 1 m).gcd m * (p + 1).gcd (tval m) := by
  set g := (sigma 1 m).gcd m
  set t := m / g
  set sg := sigma 1 m / g
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hgs : g ∣ sigma 1 m := Nat.gcd_dvd_left _ _
  have htval : tval m = t := tval_pos m hm
  have hm_eq : m = g * t := (Nat.mul_div_cancel' hgm).symm
  have hs_eq : sigma 1 m = g * sg := (Nat.mul_div_cancel' hgs).symm
  have hcop_sg_t : Nat.Coprime sg t := by
    simpa [sg, t] using gcd_div_sigma_t m hm
  have hpt : ¬ p ∣ t := fun htd => hpm (by rw [hm_eq]; exact dvd_mul_of_dvd_right htd _)
  have hpsg : ¬ p ∣ sg := fun hsd => hps (by rw [hs_eq]; exact dvd_mul_of_dvd_right hsd _)
  have hcop_t_p : Nat.Coprime t p :=
    ((Nat.coprime_or_dvd_of_prime hp t).resolve_right hpt).symm
  have hcop_sg_p : Nat.Coprime sg p :=
    ((Nat.coprime_or_dvd_of_prime hp sg).resolve_right hpsg).symm
  have hcop_p1_p : Nat.Coprime (p + 1) p :=
    ((Nat.coprime_self_add_right (m := p) (n := 1)).mpr (Nat.coprime_one_right p)).symm
  rw [htval, hs_eq, hm_eq]
  rw [mul_assoc g sg, mul_assoc g t, Nat.gcd_mul_left]
  congr 1
  rw [Nat.Coprime.gcd_mul (sg * (p + 1)) hcop_t_p]
  have h1 : (sg * (p + 1)).gcd t = (p + 1).gcd t :=
    gcd_mul_cancel_coprime_left hcop_sg_t
  have h2 : (sg * (p + 1)).gcd p = 1 := by
    have : Nat.Coprime (sg * (p + 1)) p :=
      Nat.coprime_mul_iff_left.mpr ⟨hcop_sg_p, hcop_p1_p⟩
    exact this.gcd_eq_one
  rw [h1, h2, mul_one]

lemma sigma_mul_prime_sub {m p : ℕ} (hm : 0 < m) (hp : p.Prime) :
    sigma 1 m * (p + 1) - m * p =
      (sigma 1 m).gcd m * (Aval m * (p + 1) + tval m) := by
  set g := (sigma 1 m).gcd m
  set t := m / g
  set sg := sigma 1 m / g
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hgs : g ∣ sigma 1 m := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hm_eq : m = g * t := (Nat.mul_div_cancel' hgm).symm
  have hs_eq : sigma 1 m = g * sg := (Nat.mul_div_cancel' hgs).symm
  have htval : tval m = t := tval_pos m hm
  have hAval : Aval m = sg - t := by
    simpa [sg, t] using Aval_eq_div_sub m hm
  have hle_st : t ≤ sg := Nat.div_le_div_right (sigma_ge_self m hm)
  have hinner : t * p ≤ sg * (p + 1) := by nlinarith [hle_st, hp.pos]
  rw [htval, hAval]
  have hcalc : (sg - t) * (p + 1) + t = sg * (p + 1) - t * p := by
    have : t * (p + 1) ≤ sg * (p + 1) := Nat.mul_le_mul_right _ hle_st
    zify [hle_st, this, hinner]
    ring
  rw [hcalc, hs_eq, hm_eq, mul_assoc g sg, mul_assoc g t, ← Nat.mul_sub_left_distrib]

lemma Aval_mul_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hps : ¬ p ∣ sigma 1 m) :
    Aval (m * p) =
      (Aval m * (p + 1) + tval m) / (p + 1).gcd (tval m) := by
  have hpos : 0 < m * p := Nat.mul_pos hm hp.pos
  rw [Aval_pos _ hpos, sigma_mul_prime hp hpm, gcd_sigma_mul_prime hm hp hpm hps,
      sigma_mul_prime_sub hm hp]
  have hgpos : 0 < (sigma 1 m).gcd m := Nat.gcd_pos_of_pos_right _ hm
  rw [Nat.mul_div_mul_left _ _ hgpos]

/-- Type-1 construction: if `d ∣ t(m)`, `r = (k - t(m)/d) / A(m)` and `p = d*r - 1` is
a prime not dividing `m` or `σ(m)`, with `gcd(r, t(m)/d) = 1`, then `A(m*p) = k`. -/
lemma Aval_type1 {m k d r : ℕ} (hm : 0 < m) (hApos : 0 < Aval m)
    (hd : d ∣ tval m) (hdpos : 0 < d)
    (hrdef : Aval m * r = k - tval m / d) (hle : tval m / d ≤ k)
    (hrpos : 0 < r) (hcop : Nat.Coprime r (tval m / d))
    (hp : (d * r - 1).Prime)
    (hpm : ¬ (d * r - 1) ∣ m) (hps : ¬ (d * r - 1) ∣ sigma 1 m) :
    Aval (m * (d * r - 1)) = k := by
  set p := d * r - 1
  have hpr : p + 1 = d * r := Nat.sub_add_cancel (by nlinarith [hrpos, hdpos])
  have hdt : tval m = d * (tval m / d) := (Nat.mul_div_cancel' hd).symm
  have hg : (p + 1).gcd (tval m) = d := by
    rw [hpr, hdt, Nat.gcd_mul_left]
    simp [hcop.gcd_eq_one]
  rw [Aval_mul_prime hm hp hpm hps, hg]
  have : Aval m * (p + 1) + tval m = d * k := by
    rw [hpr, hdt]
    calc
      Aval m * (d * r) + d * (tval m / d)
          = d * (Aval m * r) + d * (tval m / d) := by ring
      _ = d * (k - tval m / d) + d * (tval m / d) := by rw [hrdef]
      _ = d * ((k - tval m / d) + tval m / d) := by ring
      _ = d * k := by rw [Nat.sub_add_cancel hle]
  rw [this, Nat.mul_div_cancel_left _ hdpos]

lemma Aval_four_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp7 : p ≠ 7) :
    Aval (4 * p) = (3 * p + 7) / (p + 1).gcd 4 := by
  have hpm : ¬ p ∣ 4 := by
    intro h
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) h
    have h2 : 2 ≤ p := hp.two_le
    interval_cases p <;> try contradiction
  have hps : ¬ p ∣ sigma 1 4 := by
    have hs4 : sigma 1 4 = 7 := by native_decide
    rw [hs4]
    intro h
    have hp7' : p = 1 ∨ p = 7 := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp h
    rcases hp7' with h1 | h7eq
    · exact hp.ne_one h1
    · exact hp7 h7eq
  have hA : Aval 4 = 3 := by native_decide
  have ht : tval 4 = 4 := by native_decide
  rw [Aval_mul_prime (by norm_num : 0 < 4) hp hpm hps, hA, ht]
  refine congrArg (fun n => n / (p + 1).gcd 4) ?_
  ring

lemma Aval_prime_pow_three {p : ℕ} (hp : p.Prime) :
    Aval (p ^ 3) = p ^ 2 + p + 1 := by
  rw [Aval_prime_pow hp]
  have heq : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
    zify [show 1 ≤ p ^ 3 from Nat.one_le_pow 3 p hp.pos,
          show 1 ≤ p from hp.one_le]
    ring
  rw [heq, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hp.one_lt)]

/-- If `p ≡ 1 (mod 3)` then `A(3p) = p + 4`. -/
lemma Aval_three_mul_prime {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hmod : p % 3 = 1) : Aval (3 * p) = p + 4 := by
  have hpos : 0 < 3 * p := Nat.mul_pos (by norm_num) hp.pos
  rw [Aval_pos _ hpos, sigma_three_mul_prime hp hp3]
  have hp2 : p ≠ 2 := by
    intro h; subst h; simp at hmod
  have hgcd : (4 * (p + 1)).gcd (3 * p) = 1 := by
    have hcop3 : Nat.Coprime ((4 * (p + 1)).gcd (3 * p)) 3 := by
      have h3 : (4 * (p + 1)).gcd 3 = 1 := by
        have : ¬ 3 ∣ 4 * (p + 1) := by
          intro hd
          have hcop4 : Nat.Coprime 3 4 := by decide
          have : 3 ∣ p + 1 := Nat.Coprime.dvd_of_dvd_mul_left hcop4 hd
          have : p % 3 = 2 := by omega
          omega
        exact (Nat.coprime_or_dvd_of_prime (by decide : Nat.Prime 3)
            (4 * (p + 1)) |>.resolve_right this).symm.gcd_eq_one
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) h3
    have hcopp : Nat.Coprime ((4 * (p + 1)).gcd (3 * p)) p := by
      have hgp : (4 * (p + 1)).gcd p = 1 := by
        have hp1 : Nat.Coprime (p + 1) p :=
          Nat.coprime_comm.mp
            ((Nat.coprime_self_add_right (m := p) (n := 1)).mpr (Nat.coprime_one_right p))
        have h4 : Nat.Coprime 4 p :=
          ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_left 2
        exact (Nat.coprime_mul_iff_left.mpr ⟨h4, hp1⟩)
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hgp
    have hcop : Nat.Coprime ((4 * (p + 1)).gcd (3 * p)) (3 * p) :=
      Nat.coprime_mul_iff_right.mpr ⟨hcop3, hcopp⟩
    exact hcop.eq_one_of_dvd (Nat.gcd_dvd_right _ _)
  rw [hgcd]
  have : 4 * (p + 1) - 3 * p = p + 4 := by
    have : 3 * p ≤ 4 * (p + 1) := by nlinarith [hp.pos]
    zify [this]; ring
  rw [this, Nat.div_one]

lemma sigma_of_prime_pow_mul {p a m : ℕ} (hp : p.Prime) (hcop : Nat.Coprime (p ^ a) m) :
    sigma 1 (p ^ a * m) = sigma 1 (p ^ a) * sigma 1 m :=
  isMultiplicative_sigma.map_mul_of_coprime hcop

lemma Aval_eight_mul_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hps : ¬ p ∣ 15) :
    Aval (8 * p) = (7 * p + 15) / (p + 1).gcd 8 := by
  have hpm : ¬ p ∣ 8 := by
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (by change p ∣ 2 ^ 3; exact h)
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)
  have hps' : ¬ p ∣ sigma 1 8 := by
    have : sigma 1 8 = 15 := by native_decide
    simpa [this] using hps
  have hA : Aval 8 = 7 := by native_decide
  have ht : tval 8 = 8 := by native_decide
  rw [Aval_mul_prime (by norm_num : 0 < 8) hp hpm hps', hA, ht]
  refine congrArg (fun n => n / (p + 1).gcd 8) ?_
  ring

lemma Aval_two_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Aval (2 * p ^ 2) = p ^ 2 + 3 * p + 3 := by
  have hpos : 0 < 2 * p ^ 2 := Nat.mul_pos (by norm_num) (pow_pos hp.pos 2)
  have hcop : Nat.Coprime 2 (p ^ 2) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm).pow_right 2
  rw [Aval_pos _ hpos, isMultiplicative_sigma.map_mul_of_coprime hcop,
      sigma_prime Nat.prime_two, sigma_one_apply_prime_pow hp]
  have hp1 : ∑ k ∈ range 3, p ^ k = 1 + p + p ^ 2 := by
    simp [sum_range_succ, pow_zero, pow_one]
  rw [hp1]
  have hle : 2 * p ^ 2 ≤ 3 * (1 + p + p ^ 2) := by nlinarith [hp.pos]
  have hsub : 3 * (1 + p + p ^ 2) - 2 * p ^ 2 = p ^ 2 + 3 * p + 3 := by
    zify [hle]; ring
  have hgcd : (3 * (1 + p + p ^ 2)).gcd (2 * p ^ 2) = 1 := by
    have hpmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have h2 : Nat.Coprime (3 * (1 + p + p ^ 2)) 2 := by
      have hodd : Odd (3 * (1 + p + p ^ 2)) := by
        rw [Nat.odd_iff]
        have : p ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hpmod]
        omega
      exact hodd.coprime_two_right
    have h3p : Nat.Coprime 3 p :=
      (Nat.coprime_primes (by decide : Nat.Prime 3) hp).mpr hp3.symm
    have hsp : Nat.Coprime (1 + p + p ^ 2) p := by
      have heq : 1 + p + p ^ 2 = 1 + p * (1 + p) := by ring
      rw [heq, Nat.coprime_comm]
      exact (Nat.coprime_add_mul_left_right p 1 (1 + p)).mpr (Nat.coprime_one_right p)
    have h3 : Nat.Coprime (3 * (1 + p + p ^ 2)) p :=
      Nat.coprime_mul_iff_left.mpr ⟨h3p, hsp⟩
    exact (Nat.coprime_mul_iff_right.mpr ⟨h2, h3.pow_right 2⟩).gcd_eq_one
  rw [hgcd, hsub, Nat.div_one]

lemma sigma_40052517120 : sigma 1 40052517120 = 185908504320 := by
  have hfact : (40052517120 : ℕ) =
      2 ^ 8 * (3 ^ 4 * (5 * (7 * (11 * (29 * 173))))) := by native_decide
  rw [hfact]
  have c1 : Nat.Coprime (2 ^ 8) (3 ^ 4 * (5 * (7 * (11 * (29 * 173))))) := by native_decide
  have c2 : Nat.Coprime (3 ^ 4) (5 * (7 * (11 * (29 * 173)))) := by native_decide
  have c3 : Nat.Coprime 5 (7 * (11 * (29 * 173))) := by native_decide
  have c4 : Nat.Coprime 7 (11 * (29 * 173)) := by native_decide
  have c5 : Nat.Coprime 11 (29 * 173) := by native_decide
  have c6 : Nat.Coprime 29 173 := by native_decide
  rw [isMultiplicative_sigma.map_mul_of_coprime c1,
      isMultiplicative_sigma.map_mul_of_coprime c2,
      isMultiplicative_sigma.map_mul_of_coprime c3,
      isMultiplicative_sigma.map_mul_of_coprime c4,
      isMultiplicative_sigma.map_mul_of_coprime c5,
      isMultiplicative_sigma.map_mul_of_coprime c6]
  have s2 : sigma 1 (2 ^ 8) = 511 := by native_decide
  have s3 : sigma 1 (3 ^ 4) = 121 := by native_decide
  have s5 : sigma 1 5 = 6 := by native_decide
  have s7 : sigma 1 7 = 8 := by native_decide
  have s11 : sigma 1 11 = 12 := by native_decide
  have s29 : sigma 1 29 = 30 := by native_decide
  have s173 : sigma 1 173 = 174 := by native_decide
  rw [s2, s3, s5, s7, s11, s29, s173]
  native_decide

lemma Aval_40052517120 : Aval 40052517120 = 630 := by
  have hn : (40052517120 : ℕ) ≠ 0 := by native_decide
  simp only [Aval, hn, ↓reduceIte, sigma_40052517120]
  native_decide

lemma sigma_1091059200 : sigma 1 1091059200 = 5114672640 := by
  have hfact : (1091059200 : ℕ) =
      2 ^ 9 * (3 ^ 3 * (5 ^ 2 * (7 * (11 * 41)))) := by native_decide
  rw [hfact]
  have c1 : Nat.Coprime (2 ^ 9) (3 ^ 3 * (5 ^ 2 * (7 * (11 * 41)))) := by native_decide
  have c2 : Nat.Coprime (3 ^ 3) (5 ^ 2 * (7 * (11 * 41))) := by native_decide
  have c3 : Nat.Coprime (5 ^ 2) (7 * (11 * 41)) := by native_decide
  have c4 : Nat.Coprime 7 (11 * 41) := by native_decide
  have c5 : Nat.Coprime 11 41 := by native_decide
  rw [isMultiplicative_sigma.map_mul_of_coprime c1,
      isMultiplicative_sigma.map_mul_of_coprime c2,
      isMultiplicative_sigma.map_mul_of_coprime c3,
      isMultiplicative_sigma.map_mul_of_coprime c4,
      isMultiplicative_sigma.map_mul_of_coprime c5]
  have s2 : sigma 1 (2 ^ 9) = 1023 := by native_decide
  have s3 : sigma 1 (3 ^ 3) = 40 := by native_decide
  have s5 : sigma 1 (5 ^ 2) = 31 := by native_decide
  have s7 : sigma 1 7 = 8 := by native_decide
  have s11 : sigma 1 11 = 12 := by native_decide
  have s41 : sigma 1 41 = 42 := by native_decide
  rw [s2, s3, s5, s7, s11, s41]
  native_decide

lemma Aval_1091059200 : Aval 1091059200 = 756 := by
  have hn : (1091059200 : ℕ) ≠ 0 := by native_decide
  simp only [Aval, hn, ↓reduceIte, sigma_1091059200]
  native_decide



lemma exists_Aval (n : ℕ) : ∃ i, 0 < i ∧ Aval i = n := by
  match n with
  | 0 => exact ⟨1, by decide, Aval_one⟩
  | 1 => exact ⟨2, by decide, Aval_prime Nat.prime_two⟩
  | 2 => exact ⟨120, by decide, Aval_120⟩
  | k + 3 =>
    if h1 : (k + 2).Prime then
      refine ⟨(k + 2) ^ 2, pow_pos h1.pos 2, ?_⟩
      -- `Aval ((k+2)^2) = (k+2)+1 = k+3`
      exact Aval_prime_sq h1
    else if h2 : (2 * (k + 3) - 3).Prime ∧ 3 < 2 * (k + 3) - 3 then
      refine ⟨2 * (2 * (k + 3) - 3), Nat.mul_pos (by decide) h2.1.pos, ?_⟩
      have hp2 : 2 * (k + 3) - 3 ≠ 2 := by omega
      have hp3 : 2 * (k + 3) - 3 ≠ 3 := by omega
      rw [Aval_two_mul_prime h2.1 hp2 hp3]
      have : 2 * (k + 3) - 3 + 3 = 2 * (k + 3) := by omega
      rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    else if h3 : (k + 1).Prime ∧ 3 < k + 1 then
      refine ⟨6 * (k + 1), Nat.mul_pos (by decide) h3.1.pos, ?_⟩
      rw [Aval_six_mul_prime h3.1 h3.2]
    else if h4 : ∃ e, k + 4 = 2 ^ e then
      rcases h4 with ⟨e, he⟩
      refine ⟨2 ^ e, pow_pos (by decide) e, ?_⟩
      rw [Aval_two_pow, ← he]; omega
    else if h5 : (3 * (k + 3) - 4).Prime ∧ 3 < 3 * (k + 3) - 4 then
      refine ⟨3 * (3 * (k + 3) - 4), Nat.mul_pos (by decide) h5.1.pos, ?_⟩
      exact Aval_three_mul_of h5.1 h5.2
    else if h6 : (4 * (k + 3) - 7) % 3 = 0 ∧
        ((4 * (k + 3) - 7) / 3).Prime ∧
        (4 * (k + 3) - 7) / 3 ≠ 2 ∧
        (4 * (k + 3) - 7) / 3 ≠ 7 ∧
        ((4 * (k + 3) - 7) / 3) % 4 = 3 then
      set p := (4 * (k + 3) - 7) / 3
      refine ⟨4 * p, Nat.mul_pos (by decide) h6.2.1.pos, ?_⟩
      rw [Aval_four_mul_prime h6.2.1 h6.2.2.1 h6.2.2.2.1]
      have hg : (p + 1).gcd 4 = 4 := by
        have hdiv : 4 ∣ p + 1 := by omega
        exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hdiv (by decide))
      rw [hg]
      have h3 : 3 ∣ 4 * (k + 3) - 7 := Nat.dvd_of_mod_eq_zero h6.1
      have : 3 * p + 7 = 4 * (k + 3) := by
        have hcalc : 3 * ((4 * (k + 3) - 7) / 3) + 7 = 4 * (k + 3) := by
          rw [Nat.mul_div_cancel' h3]; omega
        simpa [p] using hcalc
      rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    else if h7 : ((2 * (k + 3) - 5) % 3 = 0) ∧
        ((2 * (k + 3) - 5) / 3).Prime ∧
        (2 * (k + 3) - 5) / 3 ≠ 2 ∧
        ¬ (2 * (k + 3) - 5) / 3 ∣ 24 ∧
        ¬ (2 * (k + 3) - 5) / 3 ∣ 60 then
      -- type-1 from `m = 24`: `A(24)=3`, `t(24)=2`, so `A(24p)=(3p+5)/2`.
      set p := (2 * (k + 3) - 5) / 3
      have hm : 0 < 24 := by decide
      have hpm : ¬ p ∣ 24 := h7.2.2.2.1
      have hps : ¬ p ∣ sigma 1 24 := by
        have : sigma 1 24 = 60 := by native_decide
        simpa [this] using h7.2.2.2.2
      refine ⟨24 * p, Nat.mul_pos hm h7.2.1.pos, ?_⟩
      have hA : Aval 24 = 3 := by native_decide
      have ht : tval 24 = 2 := by native_decide
      rw [Aval_mul_prime hm h7.2.1 hpm hps, hA, ht]
      have hg : (p + 1).gcd 2 = 2 := by
        have : 2 ∣ p + 1 := by
          have : p ≠ 2 := h7.2.2.1
          have : Odd p := h7.2.1.odd_of_ne_two this
          exact even_iff_two_dvd.mp this.add_one
        exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd this (by decide))
      rw [hg]
      have hnum : 3 * (p + 1) + 2 = 3 * p + 5 := by ring
      rw [hnum]
      have : 3 * p + 5 = 2 * (k + 3) := by
        have h3 : 3 ∣ 2 * (k + 3) - 5 := Nat.dvd_of_mod_eq_zero h7.1
        have : 3 * ((2 * (k + 3) - 5) / 3) + 5 = 2 * (k + 3) := by
          rw [Nat.mul_div_cancel' h3]; omega
        simpa [p] using this
      rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    else if h8 : (2 * (k + 3) - 7) % 3 = 0 ∧
        ((2 * (k + 3) - 7) / 3).Prime ∧
        (2 * (k + 3) - 7) / 3 ≠ 2 ∧
        (2 * (k + 3) - 7) / 3 ≠ 7 ∧
        ((2 * (k + 3) - 7) / 3) % 4 = 1 then
      -- `A(4p)=(3p+7)/2` when `gcd(p+1,4)=2`
      set p := (2 * (k + 3) - 7) / 3
      refine ⟨4 * p, Nat.mul_pos (by decide) h8.2.1.pos, ?_⟩
      rw [Aval_four_mul_prime h8.2.1 h8.2.2.1 h8.2.2.2.1]
      have hg : (p + 1).gcd 4 = 2 := by
        have hpmod : p % 4 = 1 := h8.2.2.2.2
        have h2 : 2 ∣ p + 1 := by omega
        have h4 : ¬ 4 ∣ p + 1 := by omega
        have hd4 : (p + 1).gcd 4 ∣ 2 ^ 2 := by
          simpa using Nat.gcd_dvd_right (p + 1) 4
        have h2g : 2 ∣ (p + 1).gcd 4 := Nat.dvd_gcd h2 (by decide)
        rcases (Nat.dvd_prime_pow Nat.prime_two).1 hd4 with ⟨e, he, hge⟩
        interval_cases e
        · omega
        · exact hge
        · exact False.elim (h4 (by simpa [hge] using Nat.gcd_dvd_left (p + 1) 4))
      rw [hg]
      have h3 : 3 ∣ 2 * (k + 3) - 7 := Nat.dvd_of_mod_eq_zero h8.1
      have : 3 * p + 7 = 2 * (k + 3) := by
        have hcalc : 3 * ((2 * (k + 3) - 7) / 3) + 7 = 2 * (k + 3) := by
          rw [Nat.mul_div_cancel' h3]; omega
        simpa [p] using hcalc
      rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    else if h9 : (k + 3 - 4).Prime ∧ (k + 3 - 4) ≠ 3 ∧ (k + 3 - 4) % 3 = 1 ∧ 4 ≤ k + 3 then
      -- `A(3p)=p+4` when `p ≡ 1 (mod 3)`
      set p := k + 3 - 4
      refine ⟨3 * p, Nat.mul_pos (by decide) h9.1.pos, ?_⟩
      have : Aval (3 * p) = p + 4 := Aval_three_mul_prime h9.1 h9.2.1 h9.2.2.1
      have hp : p + 4 = k + 3 := by omega
      rwa [hp] at this
    else if h10 : (8 * (k + 3) - 15) % 7 = 0 ∧
        ((8 * (k + 3) - 15) / 7).Prime ∧
        (8 * (k + 3) - 15) / 7 ≠ 2 ∧
        ¬ (8 * (k + 3) - 15) / 7 ∣ 15 then
      -- `A(8p)=(7p+15)/8` when `8 ∣ p+1`
      set p := (8 * (k + 3) - 15) / 7
      refine ⟨8 * p, Nat.mul_pos (by decide) h10.2.1.pos, ?_⟩
      rw [Aval_eight_mul_prime h10.2.1 h10.2.2.1 h10.2.2.2]
      have hg : (p + 1).gcd 8 = 8 := by
        have hdiv : 8 ∣ p + 1 := by
          have h7 : 7 ∣ 8 * (k + 3) - 15 := Nat.dvd_of_mod_eq_zero h10.1
          have : 7 * p + 15 = 8 * (k + 3) := by
            have hcalc : 7 * ((8 * (k + 3) - 15) / 7) + 15 = 8 * (k + 3) := by
              rw [Nat.mul_div_cancel' h7]; omega
            simpa [p] using hcalc
          omega
        exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _) (Nat.dvd_gcd hdiv (by decide))
      rw [hg]
      have h7 : 7 ∣ 8 * (k + 3) - 15 := Nat.dvd_of_mod_eq_zero h10.1
      have : 7 * p + 15 = 8 * (k + 3) := by
        have hcalc : 7 * ((8 * (k + 3) - 15) / 7) + 15 = 8 * (k + 3) := by
          rw [Nat.mul_div_cancel' h7]; omega
        simpa [p] using hcalc
      rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]
    else if h11 : (k + 3) % 2 = 1 ∧ ((k + 3 - 3) / 2).Prime ∧
        (k + 3 - 3) / 2 ≠ 2 ∧ (k + 3 - 3) / 2 ≠ 3 ∧ (k + 3 - 3) / 2 ≠ 5 ∧
        ¬ (k + 3 - 3) / 2 ∣ 120 ∧ ¬ (k + 3 - 3) / 2 ∣ 360 ∧ 3 ≤ k + 3 then
      -- `A(120p)=2p+3` since `A(120)=2`, `t(120)=1`
      set p := (k + 3 - 3) / 2
      have hm : 0 < 120 := by decide
      have hpm : ¬ p ∣ 120 := h11.2.2.2.2.2.1
      have hps : ¬ p ∣ sigma 1 120 := by
        have : sigma 1 120 = 360 := by native_decide
        simpa [this] using h11.2.2.2.2.2.2.1
      refine ⟨120 * p, Nat.mul_pos hm h11.2.1.pos, ?_⟩
      have hA : Aval 120 = 2 := Aval_120
      have ht : tval 120 = 1 := by native_decide
      rw [Aval_mul_prime hm h11.2.1 hpm hps, hA, ht]
      have hg : (p + 1).gcd 1 = 1 := Nat.gcd_one_right _
      rw [hg, Nat.div_one]
      have : 2 * (p + 1) + 1 = k + 3 := by omega
      omega
    else if hk : k = 23 then
      refine ⟨760, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 24 then
      refine ⟨133, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 31 then
      refine ⟨172, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 33 then
      refine ⟨522, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 37 then
      refine ⟨81, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 61 then
      refine ⟨332, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 63 then
      refine ⟨108000, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 75 then
      refine ⟨2047488, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 83 then
      refine ⟨2680, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 90 then
      refine ⟨1027, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 91 then
      refine ⟨1464, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 93 then
      refine ⟨2832, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 109 then
      refine ⟨1752, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 117 then
      refine ⟨1818, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 123 then
      refine ⟨23154432, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 141 then
      refine ⟨22538880, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 153 then
      refine ⟨625, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 183 then
      refine ⟨315360, by decide, ?_⟩; subst hk; native_decide
    else if hk : k = 627 then
      refine ⟨40052517120, by decide, ?_⟩
      subst hk; exact Aval_40052517120
    else if hk : k = 753 then
      refine ⟨1091059200, by decide, ?_⟩
      subst hk; exact Aval_1091059200
    else
      -- Remaining `k` are not covered by any finite list of linear prime-producing
      -- forms (CRT: any finite set of forms is simultaneously composite on an
      -- infinite AP). A complete proof needs a k-dependent prime, but Dirichlet /
      -- Bertrand do not pin `A` at a prescribed value, and type-1 from a fixed
      -- base determines at most one candidate prime. This case is therefore open.
      sorry

/--
Motivated by the observation that some small numbers (2,12,14,18,...) occur only very late
in the recently added sequence A243473, but all numbers seem to appear sooner or later.
(The definition is completed by "0 if no such index exists" to guarantee well-definedness
in absence of a proof, but I conjecture that no such 0 will ever occur.)
The conjecture is that the sequence $\mathrm{A243473\_val}$ is eventually surjective onto $\mathbb{N} \setminus \{0, 1\}$.
-/
theorem oeis_243512_conjecture_0 (n : ℕ) : a n ≠ 0 := by
  rcases exists_Aval n with ⟨i, hi, h⟩
  exact a_ne_zero_of_Aval hi h

