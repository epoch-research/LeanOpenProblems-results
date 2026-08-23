import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Nat Finset

/--
A219055: Number of ways to write $n = p+q(3-(-1)^n)/2$ with $p>q$ and $p, q, p-6, q+6$ all prime.
-/
def A219055 (n : ℕ) : ℕ :=
  Finset.card $ Finset.filter (fun q : ℕ =>
    -- c = 1 + n % 2. The condition p > q is equivalent to (c + 1) * q < n.
    ((1 + n % 2) + 1) * q < n ∧

    -- Primality conditions for q and derived terms
    q.Prime ∧
    (q + 6).Prime ∧

    -- Primality conditions for p = n - c * q and p - 6
    (n - (1 + n % 2) * q).Prime ∧        -- p must be prime
    (n - (1 + n % 2) * q - 6).Prime      -- p - 6 must be prime
  ) (Finset.range n)

-- Formal definition of Goldbach's Conjecture
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

-- Formal definition of Lemoine's Conjecture (or Levy's Conjecture)
def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

-- Formalization of the conjecture that there are infinitely many cousin primes (p, p+6)
def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

/--
The core conjecture about the sequence A219055:
a(n) > 0 for all even n > 8012 and odd n > 15727.
-/
def a219055_core_conjecture : Prop :=
  ∀ n : ℕ,
    (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n)
      → A219055 n > 0

/- Kernel-reducible primality test, valid for `n < 127²`. -/

def smallPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]

def isPrimeBool (n : ℕ) : Bool :=
  decide (2 ≤ n) && smallPrimes.all (fun p => n == p || n % p != 0)

theorem smallPrimes_complete : ∀ p : ℕ, p ≤ 127 → p.Prime → p ∈ smallPrimes := by
  decide

theorem smallPrimes_ge_two : ∀ p ∈ smallPrimes, 2 ≤ p := by
  decide

theorem isPrimeBool_eq_true {n : ℕ} :
    isPrimeBool n = true ↔ 2 ≤ n ∧ ∀ p ∈ smallPrimes, n = p ∨ ¬ p ∣ n := by
  simp [isPrimeBool, List.all_eq_true, beq_iff_eq, bne_iff_ne, dvd_iff_mod_eq_zero]

theorem prime_of_isPrimeBool {n : ℕ} (hn : n < 127 * 127) (h : isPrimeBool n = true) :
    n.Prime := by
  rw [isPrimeBool_eq_true] at h
  obtain ⟨h2, hp⟩ := h
  refine prime_def_le_sqrt.mpr ⟨h2, fun m hm2 hmsqrt hmdvd => ?_⟩
  have hminp : (minFac n).Prime := minFac_prime (Nat.ne_of_gt h2)
  have hmin_le : minFac n ≤ m := minFac_le_of_dvd hm2 hmdvd
  have hmin_sqrt : minFac n ≤ n.sqrt := hmin_le.trans hmsqrt
  have hsqrt : n.sqrt < 127 := by rwa [sqrt_lt]
  have hmin_mem : minFac n ∈ smallPrimes :=
    smallPrimes_complete (minFac n) (by omega) hminp
  have hcases := hp (minFac n) hmin_mem
  rcases hcases with heq | hndvd
  · have hn_sqrt : n ≤ n.sqrt := by rwa [← heq] at hmin_sqrt
    have hnn : n * n ≤ n := le_sqrt.1 hn_sqrt
    have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) h2
    have : n * n ≤ n * 1 := by simpa using hnn
    have : n ≤ 1 := Nat.le_of_mul_le_mul_left this hpos
    omega
  · exact hndvd (minFac_dvd n)

/- Goldbach computational check -/

def goldbachPrimes : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
   79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
   163, 167, 173]

theorem goldbachPrimes_prime : ∀ p ∈ goldbachPrimes, p.Prime := by
  simp [goldbachPrimes]
  norm_num

def goldbachCheck (n : ℕ) : Bool :=
  goldbachPrimes.any (fun p => isPrimeBool (n - p))

theorem goldbach_of_check {n : ℕ} (hn : n < 127 * 127) (h : goldbachCheck n = true) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + q := by
  obtain ⟨p, hp_mem, hp_bool⟩ := List.any_eq_true.mp h
  have hp : p.Prime := goldbachPrimes_prime p hp_mem
  have hnp : n - p < 127 * 127 := (Nat.sub_le n p).trans_lt hn
  have hq : (n - p).Prime := prime_of_isPrimeBool hnp hp_bool
  have hle : p ≤ n := by
    by_contra hlt
    have : n - p = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hlt)
    rw [this] at hq
    exact Nat.not_prime_zero hq
  exact ⟨p, n - p, hp, hq, (Nat.add_sub_of_le hle).symm⟩

/- Lemoine computational check -/

def lemoinePrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
   73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
   157, 163, 167, 173, 179, 181]

theorem lemoinePrimes_prime : ∀ p ∈ lemoinePrimes, p.Prime := by
  simp [lemoinePrimes]
  norm_num

def lemoineCheck (n : ℕ) : Bool :=
  lemoinePrimes.any (fun q => isPrimeBool (n - 2 * q))

theorem lemoine_of_check {n : ℕ} (hn : n < 127 * 127) (h : lemoineCheck n = true) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  obtain ⟨q, hq_mem, hq_bool⟩ := List.any_eq_true.mp h
  have hq : q.Prime := lemoinePrimes_prime q hq_mem
  have hnp : n - 2 * q < 127 * 127 := (Nat.sub_le n (2 * q)).trans_lt hn
  have hp : (n - 2 * q).Prime := prime_of_isPrimeBool hnp hq_bool
  have hle : 2 * q ≤ n := by
    by_contra hlt
    have : n - 2 * q = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hlt)
    rw [this] at hp
    exact Nat.not_prime_zero hp
  exact ⟨n - 2 * q, q, hp, hq, (Nat.sub_add_cancel hle).symm⟩

/- Divide-and-conquer Boolean checker, structurally recursive on fuel. -/

def checkGo (check : ℕ → Bool) (start count : ℕ) : ℕ → Bool
  | 0 => true
  | fuel+1 =>
    if count = 0 then true
    else if count = 1 then check start
    else
      let mid := count / 2
      checkGo check start mid fuel &&
        checkGo check (start + 2 * mid) (count - mid) fuel

theorem checkGo_spec (check : ℕ → Bool) (fuel start count : ℕ)
    (hcnt : count ≤ 2 ^ fuel)
    (h : checkGo check start count (fuel + 1) = true) :
    ∀ i < count, check (start + 2 * i) = true := by
  induction fuel generalizing start count with
  | zero =>
    intro i hi
    have hci : count ≤ 1 := by simpa using hcnt
    have hi0 : i = 0 := by omega
    have hc1 : count = 1 := by omega
    subst hi0
    simp [checkGo, hc1] at h
    simpa using h
  | succ fuel ih =>
    intro i hi
    rw [checkGo] at h
    split_ifs at h with h0 h1
    · omega
    · have : i = 0 := by omega
      subst this
      simpa using h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hL, hR⟩ := h
      set mid := count / 2
      have hmid : mid ≤ 2 ^ fuel := by
        have : count ≤ 2 ^ (fuel + 1) := hcnt
        have : count / 2 ≤ 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
          omega
        exact this
      have hrest : count - mid ≤ 2 ^ fuel := by
        have : count ≤ 2 ^ (fuel + 1) := hcnt
        have : count - count / 2 ≤ 2 ^ fuel := by
          have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
          omega
        exact this
      by_cases him : i < mid
      · exact ih start mid hmid hL i him
      · have : check (start + 2 * mid + 2 * (i - mid)) = true :=
          ih (start + 2 * mid) (count - mid) hrest hR (i - mid) (by omega)
        convert this using 2
        omega

theorem two_pow_19 : 2 ^ 19 = 524288 := by decide

theorem count_le_two_pow_19 {c : ℕ} (h : c ≤ 8000) : c ≤ 2 ^ 19 := by
  rw [two_pow_19]
  omega

/- Computational verification of small Goldbach and Lemoine instances. -/

theorem gb_all : checkGo goldbachCheck 6 4004 20 = true := rfl
theorem lm_block0 : checkGo lemoineCheck 7 3000 20 = true := rfl
theorem lm_block1 : checkGo lemoineCheck 6007 3000 20 = true := rfl
theorem lm_block2 : checkGo lemoineCheck 12007 1861 20 = true := rfl

theorem goldbachCheck_small (n : ℕ) (h6 : 6 ≤ n) (hle : n ≤ 8012) (he : Even n) :
    goldbachCheck n = true := by
  have hmod : n % 2 = 0 := Nat.even_iff.mp he
  have hi : (n - 6) / 2 < 4004 := by omega
  have hn : n = 6 + 2 * ((n - 6) / 2) := by omega
  have hcheck := checkGo_spec goldbachCheck 19 6 4004
    (count_le_two_pow_19 (by decide)) gb_all ((n - 6) / 2) hi
  rwa [← hn] at hcheck

theorem lemoineCheck_small (n : ℕ) (h7 : 7 ≤ n) (hle : n ≤ 15727) (ho : Odd n) :
    lemoineCheck n = true := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp ho
  if hA : n < 6007 then
    have hi : (n - 7) / 2 < 3000 := by omega
    have hn : n = 7 + 2 * ((n - 7) / 2) := by omega
    have hcheck := checkGo_spec lemoineCheck 19 7 3000
      (count_le_two_pow_19 (by decide)) lm_block0 ((n - 7) / 2) hi
    rwa [← hn] at hcheck
  else if hB : n < 12007 then
    have hge : 6007 ≤ n := by omega
    have hi : (n - 6007) / 2 < 3000 := by omega
    have hn : n = 6007 + 2 * ((n - 6007) / 2) := by omega
    have hcheck := checkGo_spec lemoineCheck 19 6007 3000
      (count_le_two_pow_19 (by decide)) lm_block1 ((n - 6007) / 2) hi
    rwa [← hn] at hcheck
  else
    have hge : 12007 ≤ n := by omega
    have hi : (n - 12007) / 2 < 1861 := by omega
    have hn : n = 12007 + 2 * ((n - 12007) / 2) := by omega
    have hcheck := checkGo_spec lemoineCheck 19 12007 1861
      (count_le_two_pow_19 (by decide)) lm_block2 ((n - 12007) / 2) hi
    rwa [← hn] at hcheck

/- Extraction from `A219055`. -/

theorem A219055_pos_iff (n : ℕ) :
    A219055 n > 0 ↔ ∃ q < n,
      ((1 + n % 2) + 1) * q < n ∧
      q.Prime ∧ (q + 6).Prime ∧
      (n - (1 + n % 2) * q).Prime ∧
      (n - (1 + n % 2) * q - 6).Prime := by
  simp [A219055, Finset.card_pos, Finset.filter_nonempty_iff, Finset.mem_range]

theorem goldbach_of_A219055 {n : ℕ} (he : Even n) (h : A219055 n > 0) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + q := by
  obtain ⟨q, hq_lt, _, hq_prime, _, hp_prime, _⟩ := (A219055_pos_iff n).1 h
  have hmod : n % 2 = 0 := Nat.even_iff.mp he
  simp only [hmod, add_zero, one_mul] at hp_prime
  have hle : q ≤ n := Nat.le_of_lt hq_lt
  exact ⟨n - q, q, hp_prime, hq_prime, (Nat.sub_add_cancel hle).symm⟩

theorem lemoine_of_A219055 {n : ℕ} (ho : Odd n) (h : A219055 n > 0) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  obtain ⟨q, hq_lt, _, hq_prime, _, hp_prime, _⟩ := (A219055_pos_iff n).1 h
  have hmod : n % 2 = 1 := Nat.odd_iff.mp ho
  simp only [hmod] at hp_prime
  have hle : 2 * q ≤ n := by
    by_contra hlt
    have : n - 2 * q = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hlt)
    rw [this] at hp_prime
    exact Nat.not_prime_zero hp_prime
  exact ⟨n - 2 * q, q, hp_prime, hq_prime, (Nat.sub_add_cancel hle).symm⟩

/- The three implications. -/

theorem six_prime_gap_of_core (hc : a219055_core_conjecture) :
    six_prime_gap_conjecture := by
  set S := {p : ℕ | p.Prime ∧ (p + 6).Prime}
  intro hfin
  have hinf : Set.Infinite {n : ℕ | Even n ∧ 8012 < n} := by
    refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 2 * (i + 4007))
      (fun a b hab => by lia) (fun i => ⟨even_two_mul _, by lia⟩)
  have hsub : {n : ℕ | Even n ∧ 8012 < n} ⊆ {n : ℕ | A219055 n > 0 ∧ Even n} := by
    intro n ⟨he, hn⟩
    exact ⟨hc n (Or.inl ⟨he, hn⟩), he⟩
  have hsub2 : {n : ℕ | A219055 n > 0 ∧ Even n} ⊆
      (fun x : ℕ × ℕ => x.1 + x.2 + 6) '' (S ×ˢ S) := by
    intro n ⟨hpos, he⟩
    obtain ⟨q, hq_lt, _, hq_prime, hq6, hp_prime, hp6⟩ := (A219055_pos_iff n).1 hpos
    have hmod : n % 2 = 0 := Nat.even_iff.mp he
    simp only [hmod, add_zero, one_mul] at hp_prime hp6
    have hq_le : q ≤ n := Nat.le_of_lt hq_lt
    have h6 : 6 ≤ n - q := by
      by_contra h
      have : n - q - 6 = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h)
      rw [this] at hp6
      exact Nat.not_prime_zero hp6
    have hsub6 : n - q - 6 + 6 = n - q := Nat.sub_add_cancel h6
    refine ⟨(n - q - 6, q), ⟨⟨hp6, ?_⟩, ⟨hq_prime, hq6⟩⟩, ?_⟩
    · rwa [hsub6]
    · calc n - q - 6 + q + 6
          = n - q - 6 + 6 + q := by ring
        _ = n - q + q := by rw [hsub6]
        _ = n := Nat.sub_add_cancel hq_le
  have hfin2 : ((fun x : ℕ × ℕ => x.1 + x.2 + 6) '' (S ×ˢ S)).Finite :=
    (hfin.prod hfin).image _
  exact hinf (hfin2.subset (Set.Subset.trans hsub hsub2))

theorem goldbach_of_core (hc : a219055_core_conjecture) : goldbach_conjecture := by
  intro n hn he
  by_cases hbig : 8012 < n
  · exact goldbach_of_A219055 he (hc n (Or.inl ⟨he, hbig⟩))
  · have hnle : n ≤ 8012 := Nat.le_of_not_gt hbig
    by_cases h4 : n = 4
    · subst h4
      exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
    · have hmod : n % 2 = 0 := Nat.even_iff.mp he
      have hn6 : 6 ≤ n := by omega
      have hcheck := goldbachCheck_small n hn6 hnle he
      have hnlt : n < 127 * 127 := by omega
      exact goldbach_of_check hnlt hcheck

theorem lemoine_of_core (hc : a219055_core_conjecture) : lemoine_conjecture := by
  intro n hn ho
  by_cases hbig : 15727 < n
  · exact lemoine_of_A219055 ho (hc n (Or.inr ⟨ho, hbig⟩))
  · have hnle : n ≤ 15727 := Nat.le_of_not_gt hbig
    have hcheck := lemoineCheck_small n hn hnle ho
    have hnlt : n < 127 * 127 := by omega
    exact lemoine_of_check hnlt hcheck

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture :=
  fun hc => ⟨goldbach_of_core hc, lemoine_of_core hc, six_prime_gap_of_core hc⟩
