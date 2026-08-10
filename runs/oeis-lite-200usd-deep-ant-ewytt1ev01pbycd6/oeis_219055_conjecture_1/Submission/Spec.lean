import FormalConjectures.Util.ProblemImports

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

/- Kernel-efficient primality and decomposition search (helpers for the proof). -/

/-- Trial division by odd divisors `d` (starting from the given value, stepping by 2),
checking none with `d*d ≤ n` divides `n`. Bounded by `fuel`. -/
def auxP (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | d, (fuel+1) => if n < d*d then true else if n % d == 0 then false else auxP n (d+2) fuel

/-- Kernel-efficient primality test (checks `2`, then odd trial divisors). -/
def isPrimeB (n : ℕ) : Bool :=
  if n < 2 then false else if n == 2 then true else if n % 2 == 0 then false else auxP n 3 n

theorem auxP_true : ∀ (fuel d n : ℕ), auxP n d fuel = true →
    ∀ e, d ≤ e → e % 2 = d % 2 → e * e ≤ n → e < d + 2 * fuel → n % e ≠ 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro d n _ e hde _ _ helt
    omega
  | succ fuel ih =>
    intro d n h e hde hpar hen helt
    rw [auxP] at h
    by_cases hd : n < d * d
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [hd, if_false] at h
      by_cases hdvd : n % d == 0
      · simp only [hdvd, if_true] at h
        exact absurd h (by simp)
      · simp only [hdvd] at h
        rcases Nat.eq_or_lt_of_le hde with heq | hlt
        · subst heq
          simpa using hdvd
        · have he2 : d + 2 ≤ e := by omega
          exact ih (d+2) n h e he2 (by omega) hen (by omega)

theorem noFactor_of_isPrimeB {n : ℕ} (h : isPrimeB n = true) :
    n = 2 ∨ (2 ≤ n ∧ ∀ e, 2 ≤ e → e * e ≤ n → n % e ≠ 0) := by
  unfold isPrimeB at h
  by_cases h2 : n < 2
  · simp [h2] at h
  · by_cases he2 : n == 2
    · left; simpa using he2
    · right
      have hn2 : 2 ≤ n := by omega
      have hne2 : n ≠ 2 := by simpa using he2
      by_cases hpar : n % 2 == 0
      · simp [h2, he2, hpar] at h
      · have hodd : n % 2 = 1 := by
          have := hpar; simp only [beq_iff_eq] at this; omega
        have haux : auxP n 3 n = true := by
          simp only [h2, he2, hpar, if_false] at h
          simpa using h
        refine ⟨hn2, fun e he hen => ?_⟩
        by_cases hev : e % 2 = 0
        · intro hc
          have hd : e ∣ n := Nat.dvd_of_mod_eq_zero hc
          have h2e : 2 ∣ e := Nat.dvd_of_mod_eq_zero hev
          have hdn : (2 : ℕ) ∣ n := h2e.trans hd
          have : n % 2 = 0 := (Nat.dvd_iff_mod_eq_zero).mp hdn
          omega
        · have hge3 : 3 ≤ e := by omega
          exact auxP_true n 3 n haux e (by omega) (by omega) hen (by nlinarith [hen, he])

theorem isPrimeB_prime {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  rcases noFactor_of_isPrimeB h with h2 | ⟨h2, hf⟩
  · subst h2; exact Nat.prime_two
  · by_contra hp
    have hpos : 0 < n := by omega
    have hsq := Nat.minFac_sq_le_self hpos hp
    have hdvd := Nat.minFac_dvd n
    have hne1 : n ≠ 1 := by omega
    have hmp : Nat.Prime (minFac n) := Nat.minFac_prime hne1
    have hm2 : 2 ≤ minFac n := hmp.two_le
    have : minFac n * minFac n ≤ n := by nlinarith [hsq]
    have hmod : n % minFac n ≠ 0 := hf (minFac n) hm2 this
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    exact hmod hdvd

/-- Searches for a prime `q` with `n - q` prime (a Goldbach decomposition `n = (n-q)+q`). -/
def gbAux (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | q, (fuel+1) => if isPrimeB q && isPrimeB (n - q) then true else gbAux n (q+1) fuel

def goldbachB (n : ℕ) : Bool := gbAux n 2 n

theorem gbAux_true : ∀ (fuel n q : ℕ), gbAux n q fuel = true →
    ∃ r, isPrimeB r = true ∧ isPrimeB (n - r) = true := by
  intro fuel
  induction fuel with
  | zero => intro n q h; simp [gbAux] at h
  | succ fuel ih =>
    intro n q h
    rw [gbAux] at h
    by_cases hc : isPrimeB q && isPrimeB (n - q)
    · rw [Bool.and_eq_true] at hc
      exact ⟨q, hc.1, hc.2⟩
    · rw [if_neg hc] at h
      exact ih n (q+1) h

theorem goldbachB_spec {n : ℕ} (h : goldbachB n = true) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + q := by
  obtain ⟨r, hr, hnr⟩ := gbAux_true n n 2 (by rw [goldbachB] at h; exact h)
  have hrp : Nat.Prime r := isPrimeB_prime hr
  have hnrp : Nat.Prime (n - r) := isPrimeB_prime hnr
  have h2 := hnrp.two_le
  exact ⟨n - r, r, hnrp, hrp, by omega⟩

/-- Searches for a prime `q` with `n - 2q` prime (a Lemoine decomposition `n = (n-2q)+2q`). -/
def lemAux (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | q, (fuel+1) => if isPrimeB q && isPrimeB (n - 2*q) then true else lemAux n (q+1) fuel

def lemoineB (n : ℕ) : Bool := lemAux n 2 n

theorem lemAux_true : ∀ (fuel n q : ℕ), lemAux n q fuel = true →
    ∃ r, isPrimeB r = true ∧ isPrimeB (n - 2*r) = true := by
  intro fuel
  induction fuel with
  | zero => intro n q h; simp [lemAux] at h
  | succ fuel ih =>
    intro n q h
    rw [lemAux] at h
    by_cases hc : isPrimeB q && isPrimeB (n - 2*q)
    · rw [Bool.and_eq_true] at hc
      exact ⟨q, hc.1, hc.2⟩
    · rw [if_neg hc] at h
      exact ih n (q+1) h

theorem lemoineB_spec {n : ℕ} (h : lemoineB n = true) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  obtain ⟨r, hr, hnr⟩ := lemAux_true n n 2 (by rw [lemoineB] at h; exact h)
  have hrp : Nat.Prime r := isPrimeB_prime hr
  have hnrp : Nat.Prime (n - 2*r) := isPrimeB_prime hnr
  have h2 := hnrp.two_le
  exact ⟨n - 2*r, r, hnrp, hrp, by omega⟩

/- Finite verification of small cases via chunked kernel evaluation. -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc0 : (List.range 500).all (fun k => goldbachB (4 + 2*(0 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc1 : (List.range 500).all (fun k => goldbachB (4 + 2*(500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc2 : (List.range 500).all (fun k => goldbachB (4 + 2*(1000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc3 : (List.range 500).all (fun k => goldbachB (4 + 2*(1500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc4 : (List.range 500).all (fun k => goldbachB (4 + 2*(2000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc5 : (List.range 500).all (fun k => goldbachB (4 + 2*(2500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc6 : (List.range 500).all (fun k => goldbachB (4 + 2*(3000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc7 : (List.range 500).all (fun k => goldbachB (4 + 2*(3500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem gc8 : (List.range 5).all (fun k => goldbachB (4 + 2*(4000 + k))) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc0 : (List.range 500).all (fun k => lemoineB (7 + 2*(0 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc1 : (List.range 500).all (fun k => lemoineB (7 + 2*(500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc2 : (List.range 500).all (fun k => lemoineB (7 + 2*(1000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc3 : (List.range 500).all (fun k => lemoineB (7 + 2*(1500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc4 : (List.range 500).all (fun k => lemoineB (7 + 2*(2000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc5 : (List.range 500).all (fun k => lemoineB (7 + 2*(2500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc6 : (List.range 500).all (fun k => lemoineB (7 + 2*(3000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc7 : (List.range 500).all (fun k => lemoineB (7 + 2*(3500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc8 : (List.range 500).all (fun k => lemoineB (7 + 2*(4000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc9 : (List.range 500).all (fun k => lemoineB (7 + 2*(4500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc10 : (List.range 500).all (fun k => lemoineB (7 + 2*(5000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc11 : (List.range 500).all (fun k => lemoineB (7 + 2*(5500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc12 : (List.range 500).all (fun k => lemoineB (7 + 2*(6000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc13 : (List.range 500).all (fun k => lemoineB (7 + 2*(6500 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc14 : (List.range 500).all (fun k => lemoineB (7 + 2*(7000 + k))) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem lc15 : (List.range 361).all (fun k => lemoineB (7 + 2*(7500 + k))) = true := by decide +kernel

theorem gFromChunk (base len : ℕ)
    (h : (List.range len).all (fun k => goldbachB (4 + 2*(base + k))) = true)
    {j : ℕ} (h1 : base ≤ j) (h2 : j < base + len) : goldbachB (4 + 2*j) = true := by
  have hk := (List.all_eq_true.mp h) (j - base) (List.mem_range.mpr (by omega))
  have he : 4 + 2 * (base + (j - base)) = 4 + 2 * j := by omega
  simpa [he] using hk

theorem lFromChunk (base len : ℕ)
    (h : (List.range len).all (fun k => lemoineB (7 + 2*(base + k))) = true)
    {j : ℕ} (h1 : base ≤ j) (h2 : j < base + len) : lemoineB (7 + 2*j) = true := by
  have hk := (List.all_eq_true.mp h) (j - base) (List.mem_range.mpr (by omega))
  have he : 7 + 2 * (base + (j - base)) = 7 + 2 * j := by omega
  simpa [he] using hk

theorem goldbach_all : ∀ j, j < 4005 → goldbachB (4 + 2*j) = true := by
  intro j hj
  rcases (show ((0 ≤ j ∧ j < 500) ∨ (500 ≤ j ∧ j < 1000) ∨ (1000 ≤ j ∧ j < 1500) ∨ (1500 ≤ j ∧ j < 2000) ∨ (2000 ≤ j ∧ j < 2500) ∨ (2500 ≤ j ∧ j < 3000) ∨ (3000 ≤ j ∧ j < 3500) ∨ (3500 ≤ j ∧ j < 4000) ∨ (4000 ≤ j ∧ j < 4005)) by omega) with h0|h1|h2|h3|h4|h5|h6|h7|h8
  · exact gFromChunk 0 500 gc0 h0.1 h0.2
  · exact gFromChunk 500 500 gc1 h1.1 h1.2
  · exact gFromChunk 1000 500 gc2 h2.1 h2.2
  · exact gFromChunk 1500 500 gc3 h3.1 h3.2
  · exact gFromChunk 2000 500 gc4 h4.1 h4.2
  · exact gFromChunk 2500 500 gc5 h5.1 h5.2
  · exact gFromChunk 3000 500 gc6 h6.1 h6.2
  · exact gFromChunk 3500 500 gc7 h7.1 h7.2
  · exact gFromChunk 4000 5 gc8 h8.1 h8.2

theorem lemoine_all : ∀ j, j < 7861 → lemoineB (7 + 2*j) = true := by
  intro j hj
  rcases (show ((0 ≤ j ∧ j < 500) ∨ (500 ≤ j ∧ j < 1000) ∨ (1000 ≤ j ∧ j < 1500) ∨ (1500 ≤ j ∧ j < 2000) ∨ (2000 ≤ j ∧ j < 2500) ∨ (2500 ≤ j ∧ j < 3000) ∨ (3000 ≤ j ∧ j < 3500) ∨ (3500 ≤ j ∧ j < 4000) ∨ (4000 ≤ j ∧ j < 4500) ∨ (4500 ≤ j ∧ j < 5000) ∨ (5000 ≤ j ∧ j < 5500) ∨ (5500 ≤ j ∧ j < 6000) ∨ (6000 ≤ j ∧ j < 6500) ∨ (6500 ≤ j ∧ j < 7000) ∨ (7000 ≤ j ∧ j < 7500) ∨ (7500 ≤ j ∧ j < 7861)) by omega) with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15
  · exact lFromChunk 0 500 lc0 h0.1 h0.2
  · exact lFromChunk 500 500 lc1 h1.1 h1.2
  · exact lFromChunk 1000 500 lc2 h2.1 h2.2
  · exact lFromChunk 1500 500 lc3 h3.1 h3.2
  · exact lFromChunk 2000 500 lc4 h4.1 h4.2
  · exact lFromChunk 2500 500 lc5 h5.1 h5.2
  · exact lFromChunk 3000 500 lc6 h6.1 h6.2
  · exact lFromChunk 3500 500 lc7 h7.1 h7.2
  · exact lFromChunk 4000 500 lc8 h8.1 h8.2
  · exact lFromChunk 4500 500 lc9 h9.1 h9.2
  · exact lFromChunk 5000 500 lc10 h10.1 h10.2
  · exact lFromChunk 5500 500 lc11 h11.1 h11.2
  · exact lFromChunk 6000 500 lc12 h12.1 h12.2
  · exact lFromChunk 6500 500 lc13 h13.1 h13.2
  · exact lFromChunk 7000 500 lc14 h14.1 h14.2
  · exact lFromChunk 7500 361 lc15 h15.1 h15.2

theorem goldbach_small : ∀ n, 4 ≤ n → n ≤ 8012 → Even n → goldbachB n = true := by
  intro n h4 h8 hev
  obtain ⟨m, rfl⟩ := hev
  have hh := goldbach_all (m - 2) (by omega)
  have he : 4 + 2 * (m - 2) = m + m := by omega
  simpa [he] using hh

theorem lemoine_small : ∀ n, 7 ≤ n → n ≤ 15727 → Odd n → lemoineB n = true := by
  intro n h7 h15 hod
  obtain ⟨m, rfl⟩ := hod
  have hh := lemoine_all (m - 3) (by omega)
  have he : 7 + 2 * (m - 3) = 2 * m + 1 := by omega
  simpa [he] using hh

theorem extract_even {n : ℕ} (hev : Even n) (hpos : A219055 n > 0) :
    ∃ q, q.Prime ∧ (q+6).Prime ∧ (n - q).Prime ∧ (n - q - 6).Prime ∧ 2 * q < n := by
  have hmod : n % 2 = 0 := Nat.even_iff.mp hev
  rw [A219055] at hpos
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hq
  obtain ⟨_, hlt, hqp, hq6, hp, hp6⟩ := hq
  rw [hmod] at hlt hp hp6
  simp only [Nat.add_zero, one_mul] at hlt hp hp6
  refine ⟨q, hqp, hq6, hp, hp6, by omega⟩

theorem extract_odd {n : ℕ} (hod : Odd n) (hpos : A219055 n > 0) :
    ∃ q, q.Prime ∧ (q+6).Prime ∧ (n - 2*q).Prime ∧ (n - 2*q - 6).Prime ∧ 3 * q < n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hod
  rw [A219055] at hpos
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hq
  obtain ⟨_, hlt, hqp, hq6, hp, hp6⟩ := hq
  rw [hmod] at hlt hp hp6
  norm_num at hlt hp hp6
  refine ⟨q, hqp, hq6, hp, hp6, by omega⟩

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro hcore
  refine ⟨?_, ?_, ?_⟩
  · -- Goldbach: small even n by finite check; large even n from the core conjecture.
    intro n hn hev
    by_cases hb : n ≤ 8012
    · exact goldbachB_spec (goldbach_small n hn hb hev)
    · have hpos := hcore n (Or.inl ⟨hev, by omega⟩)
      obtain ⟨q, hqp, _, hp, _, hlt⟩ := extract_even hev hpos
      exact ⟨n - q, q, hp, hqp, by omega⟩
  · -- Lemoine: small odd n by finite check; large odd n from the core conjecture.
    intro n hn hod
    by_cases hb : n ≤ 15727
    · exact lemoineB_spec (lemoine_small n hn hb hod)
    · have hpos := hcore n (Or.inr ⟨hod, by omega⟩)
      obtain ⟨q, hqp, _, hp, _, hlt⟩ := extract_odd hod hpos
      exact ⟨n - 2*q, q, hp, hqp, by omega⟩
  · -- Infinitely many cousin primes: for arbitrarily large even n, the core conjecture
    -- yields a cousin prime `n - q - 6` exceeding any bound `N`.
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro N
    set n := 2 * N + 8014 with hn
    have hev : Even n := ⟨N + 4007, by omega⟩
    have hpos := hcore n (Or.inl ⟨hev, by omega⟩)
    obtain ⟨q, hqp, _, hp, hp6, hlt⟩ := extract_even hev hpos
    refine ⟨n - q - 6, ⟨hp6, ?_⟩, ?_⟩
    · have h6 : n - q - 6 + 6 = n - q := by omega
      rw [h6]; exact hp
    · omega
