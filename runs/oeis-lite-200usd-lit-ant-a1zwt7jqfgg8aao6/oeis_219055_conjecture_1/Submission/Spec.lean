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

def smallPrimes : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
def isP (n : ℕ) : Bool :=
  decide (2 ≤ n) && smallPrimes.all (fun d => decide (n < d*d) || !(n % d == 0))
def goldFind (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel+1, p => if isP p && isP (n - p) then true else goldFind n fuel (p+1)
def goldB (n : ℕ) : Bool := goldFind n 200 2
def levFind (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel+1, q => if isP q && isP (n - 2*q) then true else levFind n fuel (q+1)
def levB (n : ℕ) : Bool := levFind n 200 2
def goldOK (m : ℕ) : Bool := !(decide (4 ≤ m ∧ m % 2 = 0)) || goldB m
def levOK (m : ℕ) : Bool := !(decide (7 ≤ m ∧ m % 2 = 1)) || levB m
def goldChunkAux (b : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => goldOK (b + k) && goldChunkAux b k
def levChunkAux (b : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => levOK (b + k) && levChunkAux b k
def goldChunk (b : ℕ) : Bool := goldChunkAux b 1000
def levChunk (b : ℕ) : Bool := levChunkAux b 1000

theorem smallPrimes_complete : ∀ d, d < 127 → d.Prime → d ∈ smallPrimes := by decide

theorem isP_sound (n : ℕ) (hn : n < 16129) (h : isP n = true) : Nat.Prime n := by
  rw [isP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, fun m hm hms hmdvd => ?_⟩
  have hmn : m * m ≤ n := Nat.le_sqrt.1 hms
  have hm126 : m ≤ 126 := by
    by_contra hc
    push_neg at hc
    have : 127 * 127 ≤ m * m := Nat.mul_le_mul hc hc
    omega
  set d := m.minFac with hd
  have hm1 : m ≠ 1 := by omega
  have hdp : d.Prime := Nat.minFac_prime hm1
  have hdm : d ∣ m := Nat.minFac_dvd m
  have hdle : d ≤ m := Nat.minFac_le (by omega)
  have hdn : d ∣ n := hdm.trans hmdvd
  have hd126 : d < 127 := by omega
  have hdmem : d ∈ smallPrimes := smallPrimes_complete d hd126 hdp
  have hcheck := hall d hdmem
  have hdd : d * d ≤ n := le_trans (Nat.mul_le_mul hdle hdle) hmn
  have hmod0 : n % d = 0 := Nat.dvd_iff_mod_eq_zero.1 hdn
  rw [Bool.or_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with hlt | hne
  · omega
  · simp [hmod0] at hne

theorem goldFind_sound (n : ℕ) : ∀ fuel p, goldFind n fuel p = true →
    ∃ a, isP a = true ∧ isP (n - a) = true := by
  intro fuel
  induction fuel with
  | zero => intro p h; simp [goldFind] at h
  | succ fuel ih =>
    intro p h
    rw [goldFind] at h
    split_ifs at h with hc
    · rw [Bool.and_eq_true] at hc; exact ⟨p, hc.1, hc.2⟩
    · exact ih (p+1) h

theorem goldB_sound (n : ℕ) (hn : n < 16129) (h : goldB n = true) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + q := by
  obtain ⟨a, ha, hna⟩ := goldFind_sound n 200 2 h
  have hnap := isP_sound (n - a) (by omega) hna
  have h2 : 2 ≤ n - a := hnap.two_le
  have hap := isP_sound a (by omega) ha
  exact ⟨a, n - a, hap, hnap, by omega⟩

theorem levFind_sound (n : ℕ) : ∀ fuel q, levFind n fuel q = true →
    ∃ b, isP b = true ∧ isP (n - 2*b) = true := by
  intro fuel
  induction fuel with
  | zero => intro q h; simp [levFind] at h
  | succ fuel ih =>
    intro q h
    rw [levFind] at h
    split_ifs at h with hc
    · rw [Bool.and_eq_true] at hc; exact ⟨q, hc.1, hc.2⟩
    · exact ih (q+1) h

theorem levB_sound (n : ℕ) (hn : n < 16129) (h : levB n = true) :
    ∃ p q, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  obtain ⟨b, hb, hnb⟩ := levFind_sound n 200 2 h
  have hnbp := isP_sound (n - 2*b) (by omega) hnb
  have h2 : 2 ≤ n - 2*b := hnbp.two_le
  have hbp := isP_sound b (by omega) hb
  exact ⟨n - 2*b, b, hnbp, hbp, by omega⟩

theorem goldChunkAux_sound (b : ℕ) : ∀ s, goldChunkAux b s = true →
    ∀ k, k < s → goldOK (b + k) = true := by
  intro s
  induction s with
  | zero => intro _ k hk; omega
  | succ s ih =>
    intro h k hk
    rw [goldChunkAux, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · exact ih h.2 k hk'
    · exact h.1

theorem levChunkAux_sound (b : ℕ) : ∀ s, levChunkAux b s = true →
    ∀ k, k < s → levOK (b + k) = true := by
  intro s
  induction s with
  | zero => intro _ k hk; omega
  | succ s ih =>
    intro h k hk
    rw [levChunkAux, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
    · exact ih h.2 k hk'
    · exact h.1

theorem goldChunk_sound (b : ℕ) (h : goldChunk b = true) :
    ∀ k, k < 1000 → 4 ≤ b + k → (b+k) % 2 = 0 → goldB (b+k) = true := by
  intro k hk h4 hev
  have hok := goldChunkAux_sound b 1000 h k hk
  rw [goldOK] at hok
  have hd : decide (4 ≤ b+k ∧ (b+k) % 2 = 0) = true := decide_eq_true_eq.mpr ⟨h4, hev⟩
  rw [hd] at hok
  simpa using hok

theorem levChunk_sound (b : ℕ) (h : levChunk b = true) :
    ∀ k, k < 1000 → 7 ≤ b + k → (b+k) % 2 = 1 → levB (b+k) = true := by
  intro k hk h7 hev
  have hok := levChunkAux_sound b 1000 h k hk
  rw [levOK] at hok
  have hd : decide (7 ≤ b+k ∧ (b+k) % 2 = 1) = true := decide_eq_true_eq.mpr ⟨h7, hev⟩
  rw [hd] at hok
  simpa using hok

-- The finite small-case verifications, split into separate declarations and elaborated
-- sequentially so that the (memory-intensive) kernel reductions are freed one block at a time.
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem gchunk0 : goldChunk 0 = true := by decide
theorem gchunk1 : goldChunk 1000 = true := by decide
theorem gchunk2 : goldChunk 2000 = true := by decide
theorem gchunk3 : goldChunk 3000 = true := by decide
theorem gchunk4 : goldChunk 4000 = true := by decide
theorem gchunk5 : goldChunk 5000 = true := by decide
theorem gchunk6 : goldChunk 6000 = true := by decide
theorem gchunk7 : goldChunk 7000 = true := by decide
theorem gchunk8 : goldChunk 8000 = true := by decide
theorem lchunk0 : levChunk 0 = true := by decide
theorem lchunk1 : levChunk 1000 = true := by decide
theorem lchunk2 : levChunk 2000 = true := by decide
theorem lchunk3 : levChunk 3000 = true := by decide
theorem lchunk4 : levChunk 4000 = true := by decide
theorem lchunk5 : levChunk 5000 = true := by decide
theorem lchunk6 : levChunk 6000 = true := by decide
theorem lchunk7 : levChunk 7000 = true := by decide
theorem lchunk8 : levChunk 8000 = true := by decide
theorem lchunk9 : levChunk 9000 = true := by decide
theorem lchunk10 : levChunk 10000 = true := by decide
theorem lchunk11 : levChunk 11000 = true := by decide
theorem lchunk12 : levChunk 12000 = true := by decide
theorem lchunk13 : levChunk 13000 = true := by decide
theorem lchunk14 : levChunk 14000 = true := by decide
theorem lchunk15 : levChunk 15000 = true := by decide

/--
A219055, Conjecture 1: The core conjecture for A219055 implies Goldbach's conjecture,
Lemoine's conjecture and the conjecture that there are infinitely many primes p with p+6 also prime.
-/
theorem oeis_219055_conjecture_1 :
    a219055_core_conjecture → goldbach_conjecture ∧ lemoine_conjecture ∧ six_prime_gap_conjecture := by
  intro hcore
  have hGchunks : ∀ i, i < 9 → goldChunk (1000*i) = true := by
    intro i hi
    interval_cases i
    · exact gchunk0
    · exact gchunk1
    · exact gchunk2
    · exact gchunk3
    · exact gchunk4
    · exact gchunk5
    · exact gchunk6
    · exact gchunk7
    · exact gchunk8
  have hLchunks : ∀ i, i < 16 → levChunk (1000*i) = true := by
    intro i hi
    interval_cases i
    · exact lchunk0
    · exact lchunk1
    · exact lchunk2
    · exact lchunk3
    · exact lchunk4
    · exact lchunk5
    · exact lchunk6
    · exact lchunk7
    · exact lchunk8
    · exact lchunk9
    · exact lchunk10
    · exact lchunk11
    · exact lchunk12
    · exact lchunk13
    · exact lchunk14
    · exact lchunk15
  refine ⟨?_, ?_, ?_⟩
  · -- Goldbach's conjecture
    intro n h4 hev
    have hev2 : n % 2 = 0 := Nat.even_iff.1 hev
    by_cases hbig : 8012 < n
    · have hpos : 0 < A219055 n := hcore n (Or.inl ⟨hev, hbig⟩)
      unfold A219055 at hpos
      rw [Finset.card_pos] at hpos
      obtain ⟨q, hq⟩ := hpos
      rw [Finset.mem_filter] at hq
      obtain ⟨-, hcond⟩ := hq
      have hc1 : 1 + n % 2 = 1 := by omega
      rw [hc1, one_mul] at hcond
      obtain ⟨hlt, hqp, -, hnqp, -⟩ := hcond
      exact ⟨n - q, q, hnqp, hqp, by omega⟩
    · push_neg at hbig
      have hi : n / 1000 < 9 := by omega
      have hk : n % 1000 < 1000 := Nat.mod_lt _ (by norm_num)
      have hgb : goldB n = true := by
        have hs := goldChunk_sound (1000*(n/1000)) (hGchunks (n/1000) hi) (n%1000) hk
          (by omega) (by omega)
        rwa [Nat.div_add_mod] at hs
      exact goldB_sound n (by omega) hgb
  · -- Lemoine's conjecture
    intro n h7 hodd
    have hev2 : n % 2 = 1 := Nat.odd_iff.1 hodd
    by_cases hbig : 15727 < n
    · have hpos : 0 < A219055 n := hcore n (Or.inr ⟨hodd, hbig⟩)
      unfold A219055 at hpos
      rw [Finset.card_pos] at hpos
      obtain ⟨q, hq⟩ := hpos
      rw [Finset.mem_filter] at hq
      obtain ⟨-, hcond⟩ := hq
      have hc1 : 1 + n % 2 = 2 := by omega
      rw [hc1] at hcond
      obtain ⟨hlt, hqp, -, hnqp, -⟩ := hcond
      exact ⟨n - 2*q, q, hnqp, hqp, by omega⟩
    · push_neg at hbig
      have hi : n / 1000 < 16 := by omega
      have hk : n % 1000 < 1000 := Nat.mod_lt _ (by norm_num)
      have hlb : levB n = true := by
        have hs := levChunk_sound (1000*(n/1000)) (hLchunks (n/1000) hi) (n%1000) hk
          (by omega) (by omega)
        rwa [Nat.div_add_mod] at hs
      exact levB_sound n (by omega) hlb
  · -- Infinitely many primes `p` with `p + 6` prime
    apply Set.infinite_of_not_bddAbove
    rw [not_bddAbove_iff]
    intro N
    set n := 2*N + 8014 with hn
    have hev : Even n := ⟨N + 4007, by omega⟩
    have hbig : 8012 < n := by omega
    have hpos : 0 < A219055 n := hcore n (Or.inl ⟨hev, hbig⟩)
    unfold A219055 at hpos
    rw [Finset.card_pos] at hpos
    obtain ⟨q, hq⟩ := hpos
    rw [Finset.mem_filter] at hq
    obtain ⟨-, hcond⟩ := hq
    have hev2 : n % 2 = 0 := Nat.even_iff.1 hev
    have hc1 : 1 + n % 2 = 1 := by omega
    rw [hc1, one_mul] at hcond
    obtain ⟨hlt, hqp, -, hnqp, hnq6p⟩ := hcond
    refine ⟨n - q - 6, ⟨hnq6p, ?_⟩, ?_⟩
    · have he : n - q - 6 + 6 = n - q := by omega
      rw [he]; exact hnqp
    · omega
