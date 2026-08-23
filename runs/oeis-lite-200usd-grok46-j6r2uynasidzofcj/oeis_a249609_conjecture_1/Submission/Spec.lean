import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 1024

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

/-! ### Population count -/

/-- Kernel-reducible popcount. -/
def popc (n : ℕ) : ℕ := (List.range (n.log2 + 1)).countP n.testBit

lemma bits_count_rec (n : ℕ) :
    n.bits.count true = n % 2 + (n / 2).bits.count true := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [h, zero_add]
    by_cases hn : n = 0
    · subst hn; simp [Nat.zero_bits]
    · have hdiv : n = 2 * (n / 2) := by
        have := Nat.div_add_mod n 2
        omega
      have hnz : n / 2 ≠ 0 := by intro hz; omega
      rw [hdiv, Nat.mul_div_right _ (by decide : 0 < 2), Nat.bit0_bits _ hnz]
      simp
  · rw [h]
    have hdiv : n = 2 * (n / 2) + 1 := by
      have := Nat.div_add_mod n 2
      omega
    conv_lhs => rw [hdiv]
    rw [Nat.bit1_bits, count_cons_self]
    omega

lemma popc_zero : popc 0 = 0 := by
  have h0 : Nat.log2 0 = 0 := by rw [Nat.log2_def]; simp
  unfold popc
  rw [h0]
  simp only [zero_add, range_one, countP_singleton]
  have : Nat.testBit 0 0 = false := Nat.testBit_lt_two_pow (by decide : (0 : ℕ) < 2 ^ 0)
  simp [this]

lemma popc_one : popc 1 = 1 := by
  have hlog : Nat.log2 1 = 0 := by rw [Nat.log2_def]; simp
  unfold popc
  rw [hlog]
  simp only [zero_add, range_one, countP_singleton, Nat.testBit_zero]
  decide

lemma log2_div2 {n : ℕ} (hn : 2 ≤ n) : n.log2 = (n / 2).log2 + 1 := by
  rw [Nat.log2_def (n := n)]
  simp [hn]

lemma popc_rec (n : ℕ) : popc n = n % 2 + popc (n / 2) := by
  by_cases h0 : n = 0
  · subst h0; simp [popc_zero]
  by_cases h1 : n = 1
  · subst h1; simp [popc_one, popc_zero]
  have hn2 : 2 ≤ n := by omega
  unfold popc
  have hlog : n.log2 = (n / 2).log2 + 1 := log2_div2 hn2
  rw [hlog, range_succ_eq_map]
  simp only [countP_cons, Nat.testBit_zero]
  have hmap :
      countP n.testBit (map succ (range ((n / 2).log2 + 1))) =
      countP (n / 2).testBit (range ((n / 2).log2 + 1)) := by
    rw [countP_map]
    apply countP_congr
    intro i hi
    simp [Nat.testBit_succ]
  rw [hmap]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · simp [h]
  · simp [h]; omega

lemma popc_eq_bits_count (n : ℕ) : popc n = n.bits.count true := by
  refine Nat.strong_induction_on n fun n ih => ?_
  cases n with
  | zero =>
    simpa [Nat.zero_bits] using popc_zero
  | succ n =>
    rw [popc_rec, bits_count_rec]
    have : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
    exact congrArg (fun t => (n + 1) % 2 + t) (ih _ this)

lemma popc_mod_two_iff (n : ℕ) :
    popc n % 2 = 0 ↔ n.bits.count true % 2 = 0 := by
  rw [popc_eq_bits_count]

/-! ### Characterisation of `a` -/

private def ev (k : ℕ) : Bool := decide (k.bits.count true % 2 = 0)

lemma a_eq (n : ℕ) : a n = a.find_min_m n ev 1 := rfl

lemma ev_iff_popc (k : ℕ) : ev k = decide (popc k % 2 = 0) := by
  simp [ev, popc_eq_bits_count]

lemma ev_of_popc_even {k : ℕ} (h : popc k % 2 = 0) : ev k = true := by
  rw [ev_iff_popc, h]; simp

lemma ev_of_popc_odd {k : ℕ} (h : popc k % 2 = 1) : ev k = false := by
  rw [ev_iff_popc, h]; simp

lemma ev_eq_true_iff (k : ℕ) : ev k = true ↔ popc k % 2 = 0 := by
  constructor
  · intro h
    have : decide (popc k % 2 = 0) = true := by rwa [← ev_iff_popc]
    exact of_decide_eq_true this
  · exact ev_of_popc_even

lemma find_min_m_ne_zero_of_exists (n t : ℕ) (ht : 1 ≤ t)
    (h : ∃ m, t ≤ m ∧ m ≤ n ∧ ev (n.choose m) = true) :
    a.find_min_m n ev t ≠ 0 := by
  generalize hd : n + 1 - t = d
  revert t
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro t ht h htD
    rw [a.find_min_m.eq_def]
    by_cases hgt : t > n
    · simp [hgt]
      rcases h with ⟨m, htm, hmn, _⟩
      omega
    · have hle : t ≤ n := Nat.not_lt.mp hgt
      simp [hgt]
      by_cases hhit : ev (n.choose t) = true
      · simp [hhit]
        omega
      · simp [hhit]
        have hfuel : n + 1 - (t + 1) < d := by omega
        apply ih (n + 1 - (t + 1)) hfuel (t + 1) (by omega) ?_ rfl
        rcases h with ⟨m, htm, hmn, hev⟩
        refine ⟨m, ?_, hmn, hev⟩
        have : t ≠ m := by
          intro heq; subst heq; exact hhit hev
        omega

lemma a_ne_zero_of_exists_evil {n : ℕ}
    (h : ∃ m, 1 ≤ m ∧ m ≤ n ∧ popc (n.choose m) % 2 = 0) : a n ≠ 0 := by
  rw [a_eq]
  apply find_min_m_ne_zero_of_exists n 1 (by decide)
  rcases h with ⟨m, hm1, hmn, hp⟩
  exact ⟨m, hm1, hmn, ev_of_popc_even hp⟩

lemma a_ne_zero_of_evil_self {n : ℕ} (hn : 1 ≤ n) (he : popc n % 2 = 0) :
    a n ≠ 0 := by
  apply a_ne_zero_of_exists_evil
  refine ⟨1, by omega, hn, ?_⟩
  simpa [Nat.choose_one_right] using he

lemma a_ne_zero_of_witness (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (he : popc (n.choose k) % 2 = 0) : a n ≠ 0 :=
  a_ne_zero_of_exists_evil ⟨k, hk1, hkn, he⟩

/-! ### `a n = 0` for the five exceptional values -/

lemma ev_one : ev 1 = false := by
  simp [ev, Nat.one_bits]

lemma ev_two : ev 2 = false := by
  have hbit : Nat.bits 2 = [false, true] := by
    have : (2 : ℕ) = 2 * 1 := rfl
    rw [this, Nat.bit0_bits (n := 1) (by decide), Nat.one_bits]
  simp [ev, hbit]

lemma step_odious (n t : ℕ) (hle : t ≤ n) (hod : ev (n.choose t) = false) :
    a.find_min_m n ev t = a.find_min_m n ev (t + 1) := by
  rw [a.find_min_m.eq_def]
  simp [Nat.not_lt.mpr hle, hod]

lemma step_done (n t : ℕ) (hgt : t > n) :
    a.find_min_m n ev t = 0 := by
  rw [a.find_min_m.eq_def]; simp [hgt]

lemma a_zero : a 0 = 0 := by
  rw [a_eq, a.find_min_m.eq_def]; simp

lemma a_one : a 1 = 0 := by
  rw [a_eq]
  have h1 : ev (Nat.choose 1 1) = false := by
    have : Nat.choose 1 1 = 1 := rfl
    rw [this, ev_one]
  rw [step_odious 1 1 (by decide) h1, step_done 1 2 (by decide)]

lemma a_two : a 2 = 0 := by
  rw [a_eq]
  have h1 : ev (Nat.choose 2 1) = false := by
    have : Nat.choose 2 1 = 2 := rfl
    rw [this, ev_two]
  have h2 : ev (Nat.choose 2 2) = false := by
    have : Nat.choose 2 2 = 1 := rfl
    rw [this, ev_one]
  rw [step_odious 2 1 (by decide) h1, step_odious 2 2 (by decide) h2,
      step_done 2 3 (by decide)]

lemma a_seven : a 7 = 0 := by
  rw [a_eq]
  have h1 : ev (Nat.choose 7 1) = false := by
    have hc : Nat.choose 7 1 = 7 := rfl
    have hp : popc 7 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h2 : ev (Nat.choose 7 2) = false := by
    have hc : Nat.choose 7 2 = 21 := rfl
    have hp : popc 21 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h3 : ev (Nat.choose 7 3) = false := by
    have hc : Nat.choose 7 3 = 35 := rfl
    have hp : popc 35 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h4 : ev (Nat.choose 7 4) = false := by
    have hc : Nat.choose 7 4 = 35 := rfl
    have hp : popc 35 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h5 : ev (Nat.choose 7 5) = false := by
    have hc : Nat.choose 7 5 = 21 := rfl
    have hp : popc 21 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h6 : ev (Nat.choose 7 6) = false := by
    have hc : Nat.choose 7 6 = 7 := rfl
    have hp : popc 7 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h7 : ev (Nat.choose 7 7) = false := by
    have hc : Nat.choose 7 7 = 1 := rfl
    have hp : popc 1 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  rw [step_odious 7 1 (by decide) h1]
  rw [step_odious 7 2 (by decide) h2]
  rw [step_odious 7 3 (by decide) h3]
  rw [step_odious 7 4 (by decide) h4]
  rw [step_odious 7 5 (by decide) h5]
  rw [step_odious 7 6 (by decide) h6]
  rw [step_odious 7 7 (by decide) h7]
  rw [step_done 7 8 (by decide)]

lemma a_eight : a 8 = 0 := by
  rw [a_eq]
  have h1 : ev (Nat.choose 8 1) = false := by
    have hc : Nat.choose 8 1 = 8 := rfl
    have hp : popc 8 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h2 : ev (Nat.choose 8 2) = false := by
    have hc : Nat.choose 8 2 = 28 := rfl
    have hp : popc 28 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h3 : ev (Nat.choose 8 3) = false := by
    have hc : Nat.choose 8 3 = 56 := rfl
    have hp : popc 56 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h4 : ev (Nat.choose 8 4) = false := by
    have hc : Nat.choose 8 4 = 70 := rfl
    have hp : popc 70 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h5 : ev (Nat.choose 8 5) = false := by
    have hc : Nat.choose 8 5 = 56 := rfl
    have hp : popc 56 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h6 : ev (Nat.choose 8 6) = false := by
    have hc : Nat.choose 8 6 = 28 := rfl
    have hp : popc 28 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h7 : ev (Nat.choose 8 7) = false := by
    have hc : Nat.choose 8 7 = 8 := rfl
    have hp : popc 8 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  have h8 : ev (Nat.choose 8 8) = false := by
    have hc : Nat.choose 8 8 = 1 := rfl
    have hp : popc 1 % 2 = 1 := by decide
    rw [hc]; exact ev_of_popc_odd hp
  rw [step_odious 8 1 (by decide) h1]
  rw [step_odious 8 2 (by decide) h2]
  rw [step_odious 8 3 (by decide) h3]
  rw [step_odious 8 4 (by decide) h4]
  rw [step_odious 8 5 (by decide) h5]
  rw [step_odious 8 6 (by decide) h6]
  rw [step_odious 8 7 (by decide) h7]
  rw [step_odious 8 8 (by decide) h8]
  rw [step_done 8 9 (by decide)]
/-! ### `a n ≠ 0` for small non-exceptional `n` -/

lemma a_ne_zero_3 : a 3 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_4 : a 4 ≠ 0 := by
  refine a_ne_zero_of_witness 4 2 (by decide) (by decide) ?_
  have hc : Nat.choose 4 2 = 6 := rfl
  rw [hc]; decide

lemma a_ne_zero_5 : a 5 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_6 : a 6 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_9 : a 9 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_10 : a 10 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_11 : a 11 ≠ 0 := by
  refine a_ne_zero_of_witness 11 3 (by decide) (by decide) ?_
  have hc : Nat.choose 11 3 = 165 := rfl
  rw [hc]; decide

lemma a_ne_zero_12 : a 12 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_13 : a 13 ≠ 0 := by
  refine a_ne_zero_of_witness 13 2 (by decide) (by decide) ?_
  have hc : Nat.choose 13 2 = 78 := rfl
  rw [hc]; decide

lemma a_ne_zero_14 : a 14 ≠ 0 := by
  refine a_ne_zero_of_witness 14 7 (by decide) (by decide) ?_
  have hc : Nat.choose 14 7 = 3432 := rfl
  rw [hc]; decide

lemma a_ne_zero_15 : a 15 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_16 : a 16 ≠ 0 := by
  refine a_ne_zero_of_witness 16 2 (by decide) (by decide) ?_
  have hc : Nat.choose 16 2 = 120 := rfl
  rw [hc]; decide

lemma a_ne_zero_17 : a 17 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_18 : a 18 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_19 : a 19 ≠ 0 := by
  refine a_ne_zero_of_witness 19 3 (by decide) (by decide) ?_
  have hc : Nat.choose 19 3 = 969 := rfl
  rw [hc]; decide

lemma a_ne_zero_20 : a 20 ≠ 0 :=
  a_ne_zero_of_evil_self (by decide) (by decide)

lemma a_ne_zero_of_le_20 {n : ℕ} (hn : n ≤ 20)
    (hex : n ∉ ({0, 1, 2, 7, 8} : Finset ℕ)) : a n ≠ 0 := by
  interval_cases n
  · exact (hex (by decide)).elim
  · exact (hex (by decide)).elim
  · exact (hex (by decide)).elim
  · exact a_ne_zero_3
  · exact a_ne_zero_4
  · exact a_ne_zero_5
  · exact a_ne_zero_6
  · exact (hex (by decide)).elim
  · exact (hex (by decide)).elim
  · exact a_ne_zero_9
  · exact a_ne_zero_10
  · exact a_ne_zero_11
  · exact a_ne_zero_12
  · exact a_ne_zero_13
  · exact a_ne_zero_14
  · exact a_ne_zero_15
  · exact a_ne_zero_16
  · exact a_ne_zero_17
  · exact a_ne_zero_18
  · exact a_ne_zero_19
  · exact a_ne_zero_20


lemma mem_exceptions_iff (n : ℕ) :
    n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 7 ∨ n = 8 := by
  simp

/-- Every positive even-popcount number has `a n ≠ 0` (witness `m = 1`). -/
lemma a_ne_zero_of_even_popc {n : ℕ} (hn : 1 ≤ n) (he : popc n % 2 = 0) :
    a n ≠ 0 :=
  a_ne_zero_of_evil_self hn he

/-- If `n` is not exceptional and has even popcount, then `a n ≠ 0`. -/
lemma a_ne_zero_of_not_exception_even_popc {n : ℕ}
    (hex : n ∉ ({0, 1, 2, 7, 8} : Finset ℕ)) (he : popc n % 2 = 0) : a n ≠ 0 := by
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    exact hex (by decide)
  exact a_ne_zero_of_even_popc hn1 he

/-! ### Powers of two (`popc n = 1`) -/

lemma popc_two_pow (m : ℕ) : popc (2 ^ m) = 1 := by
  -- `2^m` has a single bit set
  induction m with
  | zero =>
    simp [pow_zero, popc_one]
  | succ m ih =>
    rw [pow_succ, popc_rec]
    have hmod : (2 ^ m * 2) % 2 = 0 := by
      rw [Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod]
    have hdiv : (2 ^ m * 2) / 2 = 2 ^ m := by
      rw [Nat.mul_div_cancel _ (by decide : 0 < 2)]
    rw [hmod, hdiv, zero_add, ih]

lemma choose_two_pow_two (m : ℕ) (hm : 1 ≤ m) :
    Nat.choose (2 ^ m) 2 = 2 ^ (m - 1) * (2 ^ m - 1) := by
  have h2 : 2 ≤ 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
    simpa using this
  rw [Nat.choose_two_right]
  -- (2^m * (2^m - 1)) / 2 = 2^{m-1} * (2^m - 1)
  have heven : 2 ∣ 2 ^ m := by
    have : 2 ^ 1 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm
    simpa using this
  have : (2 ^ m * (2 ^ m - 1)) / 2 = 2 ^ (m - 1) * (2 ^ m - 1) := by
    have hmpos : 0 < m := hm
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      cases m with
      | zero => omega
      | succ m =>
        simp [pow_succ, Nat.add_sub_cancel, mul_comm]
    rw [this, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact this

lemma popc_mul_two_pow (t k : ℕ) : popc (2 ^ t * k) = popc k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h2 : 2 ^ (t + 1) * k = 2 * (2 ^ t * k) := by
      rw [pow_succ]
      ring
    rw [h2, popc_rec]
    have hmod : (2 * (2 ^ t * k)) % 2 = 0 := by simp
    have hdiv : (2 * (2 ^ t * k)) / 2 = 2 ^ t * k := by
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [hmod, hdiv, zero_add, ih]

lemma popc_two_pow_sub_one (m : ℕ) : popc (2 ^ m - 1) = m := by
  induction m with
  | zero => simp [popc_zero]
  | succ m ih =>
    -- 2^{m+1}-1 = 2(2^m-1) + 1
    have h : 2 ^ (m + 1) - 1 = 2 * (2 ^ m - 1) + 1 := by
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
      have hle : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
      omega
    rw [h, popc_rec]
    have hmod : (2 * (2 ^ m - 1) + 1) % 2 = 1 := by simp
    have hdiv : (2 * (2 ^ m - 1) + 1) / 2 = 2 ^ m - 1 := by
      rw [Nat.mul_add_div (by decide : 0 < 2)]
      simp
    rw [hmod, hdiv, ih]
    omega

/-- For even `m ≥ 2`, `C(2^m, 2)` is evil. -/
lemma popc_choose_two_pow_two_even {m : ℕ} (hm : 2 ≤ m) (he : m % 2 = 0) :
    popc (Nat.choose (2 ^ m) 2) % 2 = 0 := by
  have hm1 : 1 ≤ m := by omega
  rw [choose_two_pow_two m hm1, popc_mul_two_pow, popc_two_pow_sub_one, he]

lemma a_ne_zero_two_pow_even_m {m : ℕ} (hm : 2 ≤ m) (he : m % 2 = 0) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 2 (by decide) ?_ (popc_choose_two_pow_two_even hm he)
  have : 2 ≤ 2 ^ m := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  exact this


/- Odious n with 21 ≤ n ≤ 64 -/

lemma a_ne_zero_21 : a 21 ≠ 0 := by
  refine a_ne_zero_of_witness 21 2 (by decide) (by decide) ?_
  have hc : Nat.choose 21 2 = 210 := rfl
  rw [hc]; decide

lemma a_ne_zero_22 : a 22 ≠ 0 := by
  refine a_ne_zero_of_witness 22 2 (by decide) (by decide) ?_
  have hc : Nat.choose 22 2 = 231 := rfl
  rw [hc]; decide

lemma a_ne_zero_25 : a 25 ≠ 0 := by
  refine a_ne_zero_of_witness 25 2 (by decide) (by decide) ?_
  have hc : Nat.choose 25 2 = 300 := rfl
  rw [hc]; decide

lemma a_ne_zero_26 : a 26 ≠ 0 := by
  refine a_ne_zero_of_witness 26 2 (by decide) (by decide) ?_
  have hc : Nat.choose 26 2 = 325 := rfl
  rw [hc]; decide

lemma a_ne_zero_28 : a 28 ≠ 0 := by
  refine a_ne_zero_of_witness 28 2 (by decide) (by decide) ?_
  have hc : Nat.choose 28 2 = 378 := rfl
  rw [hc]; decide

lemma a_ne_zero_31 : a 31 ≠ 0 := by
  refine a_ne_zero_of_witness 31 4 (by decide) (by decide) ?_
  have hc : Nat.choose 31 4 = 31465 := rfl
  rw [hc]; decide

lemma a_ne_zero_32 : a 32 ≠ 0 := by
  refine a_ne_zero_of_witness 32 5 (by decide) (by decide) ?_
  have hc : Nat.choose 32 5 = 201376 := rfl
  rw [hc]; decide

lemma a_ne_zero_35 : a 35 ≠ 0 := by
  refine a_ne_zero_of_witness 35 3 (by decide) (by decide) ?_
  have hc : Nat.choose 35 3 = 6545 := rfl
  rw [hc]; decide

lemma a_ne_zero_37 : a 37 ≠ 0 := by
  refine a_ne_zero_of_witness 37 3 (by decide) (by decide) ?_
  have hc : Nat.choose 37 3 = 7770 := rfl
  rw [hc]; decide

lemma a_ne_zero_38 : a 38 ≠ 0 := by
  refine a_ne_zero_of_witness 38 2 (by decide) (by decide) ?_
  have hc : Nat.choose 38 2 = 703 := rfl
  rw [hc]; decide

lemma a_ne_zero_41 : a 41 ≠ 0 := by
  refine a_ne_zero_of_witness 41 3 (by decide) (by decide) ?_
  have hc : Nat.choose 41 3 = 10660 := rfl
  rw [hc]; decide

lemma a_ne_zero_42 : a 42 ≠ 0 := by
  refine a_ne_zero_of_witness 42 4 (by decide) (by decide) ?_
  have hc : Nat.choose 42 4 = 111930 := rfl
  rw [hc]; decide

lemma a_ne_zero_44 : a 44 ≠ 0 := by
  refine a_ne_zero_of_witness 44 2 (by decide) (by decide) ?_
  have hc : Nat.choose 44 2 = 946 := rfl
  rw [hc]; decide

lemma a_ne_zero_47 : a 47 ≠ 0 := by
  refine a_ne_zero_of_witness 47 6 (by decide) (by decide) ?_
  have hc : Nat.choose 47 6 = 10737573 := rfl
  rw [hc]; decide

lemma a_ne_zero_49 : a 49 ≠ 0 := by
  refine a_ne_zero_of_witness 49 2 (by decide) (by decide) ?_
  have hc : Nat.choose 49 2 = 1176 := rfl
  rw [hc]; decide

lemma a_ne_zero_50 : a 50 ≠ 0 := by
  refine a_ne_zero_of_witness 50 6 (by decide) (by decide) ?_
  have hc : Nat.choose 50 6 = 15890700 := rfl
  rw [hc]; decide

lemma a_ne_zero_52 : a 52 ≠ 0 := by
  refine a_ne_zero_of_witness 52 2 (by decide) (by decide) ?_
  have hc : Nat.choose 52 2 = 1326 := rfl
  rw [hc]; decide

lemma a_ne_zero_55 : a 55 ≠ 0 := by
  refine a_ne_zero_of_witness 55 3 (by decide) (by decide) ?_
  have hc : Nat.choose 55 3 = 26235 := rfl
  rw [hc]; decide

lemma a_ne_zero_56 : a 56 ≠ 0 := by
  refine a_ne_zero_of_witness 56 3 (by decide) (by decide) ?_
  have hc : Nat.choose 56 3 = 27720 := rfl
  rw [hc]; decide

lemma a_ne_zero_59 : a 59 ≠ 0 := by
  refine a_ne_zero_of_witness 59 2 (by decide) (by decide) ?_
  have hc : Nat.choose 59 2 = 1711 := rfl
  rw [hc]; decide

lemma a_ne_zero_61 : a 61 ≠ 0 := by
  refine a_ne_zero_of_witness 61 2 (by decide) (by decide) ?_
  have hc : Nat.choose 61 2 = 1830 := rfl
  rw [hc]; decide

lemma a_ne_zero_62 : a 62 ≠ 0 := by
  refine a_ne_zero_of_witness 62 6 (by decide) (by decide) ?_
  have hc : Nat.choose 62 6 = 61474519 := rfl
  rw [hc]; decide

lemma a_ne_zero_64 : a 64 ≠ 0 := by
  refine a_ne_zero_of_witness 64 2 (by decide) (by decide) ?_
  have hc : Nat.choose 64 2 = 2016 := rfl
  rw [hc]; decide

lemma a_ne_zero_of_odious_le_64 {n : ℕ} (hn1 : 21 ≤ n) (hn2 : n ≤ 64)
    (hodd : popc n % 2 = 1) : a n ≠ 0 := by
  interval_cases n
  · exact a_ne_zero_21
  · exact a_ne_zero_22
  · have : popc 23 % 2 = 0 := by decide
    omega
  · have : popc 24 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_25
  · exact a_ne_zero_26
  · have : popc 27 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_28
  · have : popc 29 % 2 = 0 := by decide
    omega
  · have : popc 30 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_31
  · exact a_ne_zero_32
  · have : popc 33 % 2 = 0 := by decide
    omega
  · have : popc 34 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_35
  · have : popc 36 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_37
  · exact a_ne_zero_38
  · have : popc 39 % 2 = 0 := by decide
    omega
  · have : popc 40 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_41
  · exact a_ne_zero_42
  · have : popc 43 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_44
  · have : popc 45 % 2 = 0 := by decide
    omega
  · have : popc 46 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_47
  · have : popc 48 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_49
  · exact a_ne_zero_50
  · have : popc 51 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_52
  · have : popc 53 % 2 = 0 := by decide
    omega
  · have : popc 54 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_55
  · exact a_ne_zero_56
  · have : popc 57 % 2 = 0 := by decide
    omega
  · have : popc 58 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_59
  · have : popc 60 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_61
  · exact a_ne_zero_62
  · have : popc 63 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_64


/- Odious n with 65 ≤ n ≤ 256 -/

lemma a_ne_zero_67 : a 67 ≠ 0 := by
  refine a_ne_zero_of_witness 67 3 (by decide) (by decide) ?_
  have hc : Nat.choose 67 3 = 47905 := rfl
  rw [hc]; decide

lemma a_ne_zero_69 : a 69 ≠ 0 := by
  refine a_ne_zero_of_witness 69 3 (by decide) (by decide) ?_
  have hc : Nat.choose 69 3 = 52394 := rfl
  rw [hc]; decide

lemma a_ne_zero_70 : a 70 ≠ 0 := by
  refine a_ne_zero_of_witness 70 2 (by decide) (by decide) ?_
  have hc : Nat.choose 70 2 = 2415 := rfl
  rw [hc]; decide

lemma a_ne_zero_73 : a 73 ≠ 0 := by
  refine a_ne_zero_of_witness 73 2 (by decide) (by decide) ?_
  have hc : Nat.choose 73 2 = 2628 := rfl
  rw [hc]; decide

lemma a_ne_zero_74 : a 74 ≠ 0 := by
  refine a_ne_zero_of_witness 74 2 (by decide) (by decide) ?_
  have hc : Nat.choose 74 2 = 2701 := rfl
  rw [hc]; decide

lemma a_ne_zero_76 : a 76 ≠ 0 := by
  refine a_ne_zero_of_witness 76 9 (by decide) (by decide) ?_
  have hc : Nat.choose 76 9 = 142466675900 := rfl
  rw [hc]; decide

lemma a_ne_zero_79 : a 79 ≠ 0 := by
  refine a_ne_zero_of_witness 79 2 (by decide) (by decide) ?_
  have hc : Nat.choose 79 2 = 3081 := rfl
  rw [hc]; decide

lemma a_ne_zero_81 : a 81 ≠ 0 := by
  refine a_ne_zero_of_witness 81 4 (by decide) (by decide) ?_
  have hc : Nat.choose 81 4 = 1663740 := rfl
  rw [hc]; decide

lemma a_ne_zero_82 : a 82 ≠ 0 := by
  refine a_ne_zero_of_witness 82 2 (by decide) (by decide) ?_
  have hc : Nat.choose 82 2 = 3321 := rfl
  rw [hc]; decide

lemma a_ne_zero_84 : a 84 ≠ 0 := by
  refine a_ne_zero_of_witness 84 2 (by decide) (by decide) ?_
  have hc : Nat.choose 84 2 = 3486 := rfl
  rw [hc]; decide

lemma a_ne_zero_87 : a 87 ≠ 0 := by
  refine a_ne_zero_of_witness 87 2 (by decide) (by decide) ?_
  have hc : Nat.choose 87 2 = 3741 := rfl
  rw [hc]; decide

lemma a_ne_zero_88 : a 88 ≠ 0 := by
  refine a_ne_zero_of_witness 88 2 (by decide) (by decide) ?_
  have hc : Nat.choose 88 2 = 3828 := rfl
  rw [hc]; decide

lemma a_ne_zero_91 : a 91 ≠ 0 := by
  refine a_ne_zero_of_witness 91 2 (by decide) (by decide) ?_
  have hc : Nat.choose 91 2 = 4095 := rfl
  rw [hc]; decide

lemma a_ne_zero_93 : a 93 ≠ 0 := by
  refine a_ne_zero_of_witness 93 2 (by decide) (by decide) ?_
  have hc : Nat.choose 93 2 = 4278 := rfl
  rw [hc]; decide

lemma a_ne_zero_94 : a 94 ≠ 0 := by
  refine a_ne_zero_of_witness 94 3 (by decide) (by decide) ?_
  have hc : Nat.choose 94 3 = 134044 := rfl
  rw [hc]; decide

lemma a_ne_zero_97 : a 97 ≠ 0 := by
  refine a_ne_zero_of_witness 97 2 (by decide) (by decide) ?_
  have hc : Nat.choose 97 2 = 4656 := rfl
  rw [hc]; decide

lemma a_ne_zero_98 : a 98 ≠ 0 := by
  refine a_ne_zero_of_witness 98 5 (by decide) (by decide) ?_
  have hc : Nat.choose 98 5 = 67910864 := rfl
  rw [hc]; decide

lemma a_ne_zero_100 : a 100 ≠ 0 := by
  refine a_ne_zero_of_witness 100 3 (by decide) (by decide) ?_
  have hc : Nat.choose 100 3 = 161700 := rfl
  rw [hc]; decide

lemma a_ne_zero_103 : a 103 ≠ 0 := by
  refine a_ne_zero_of_witness 103 3 (by decide) (by decide) ?_
  have hc : Nat.choose 103 3 = 176851 := rfl
  rw [hc]; decide

lemma a_ne_zero_104 : a 104 ≠ 0 := by
  refine a_ne_zero_of_witness 104 9 (by decide) (by decide) ?_
  have hc : Nat.choose 104 9 = 2747472247520 := rfl
  rw [hc]; decide

lemma a_ne_zero_107 : a 107 ≠ 0 := by
  refine a_ne_zero_of_witness 107 5 (by decide) (by decide) ?_
  have hc : Nat.choose 107 5 = 106308566 := rfl
  rw [hc]; decide

lemma a_ne_zero_109 : a 109 ≠ 0 := by
  refine a_ne_zero_of_witness 109 2 (by decide) (by decide) ?_
  have hc : Nat.choose 109 2 = 5886 := rfl
  rw [hc]; decide

lemma a_ne_zero_110 : a 110 ≠ 0 := by
  refine a_ne_zero_of_witness 110 3 (by decide) (by decide) ?_
  have hc : Nat.choose 110 3 = 215820 := rfl
  rw [hc]; decide

lemma a_ne_zero_112 : a 112 ≠ 0 := by
  refine a_ne_zero_of_witness 112 2 (by decide) (by decide) ?_
  have hc : Nat.choose 112 2 = 6216 := rfl
  rw [hc]; decide

lemma a_ne_zero_115 : a 115 ≠ 0 := by
  refine a_ne_zero_of_witness 115 2 (by decide) (by decide) ?_
  have hc : Nat.choose 115 2 = 6555 := rfl
  rw [hc]; decide

lemma a_ne_zero_117 : a 117 ≠ 0 := by
  refine a_ne_zero_of_witness 117 5 (by decide) (by decide) ?_
  have hc : Nat.choose 117 5 = 167549733 := rfl
  rw [hc]; decide

lemma a_ne_zero_118 : a 118 ≠ 0 := by
  refine a_ne_zero_of_witness 118 2 (by decide) (by decide) ?_
  have hc : Nat.choose 118 2 = 6903 := rfl
  rw [hc]; decide

lemma a_ne_zero_121 : a 121 ≠ 0 := by
  refine a_ne_zero_of_witness 121 4 (by decide) (by decide) ?_
  have hc : Nat.choose 121 4 = 8495410 := rfl
  rw [hc]; decide

lemma a_ne_zero_122 : a 122 ≠ 0 := by
  refine a_ne_zero_of_witness 122 2 (by decide) (by decide) ?_
  have hc : Nat.choose 122 2 = 7381 := rfl
  rw [hc]; decide

lemma a_ne_zero_124 : a 124 ≠ 0 := by
  refine a_ne_zero_of_witness 124 2 (by decide) (by decide) ?_
  have hc : Nat.choose 124 2 = 7626 := rfl
  rw [hc]; decide

lemma a_ne_zero_127 : a 127 ≠ 0 := by
  refine a_ne_zero_of_witness 127 4 (by decide) (by decide) ?_
  have hc : Nat.choose 127 4 = 10334625 := rfl
  rw [hc]; decide

lemma a_ne_zero_128 : a 128 ≠ 0 := by
  refine a_ne_zero_of_witness 128 5 (by decide) (by decide) ?_
  have hc : Nat.choose 128 5 = 264566400 := rfl
  rw [hc]; decide

lemma a_ne_zero_131 : a 131 ≠ 0 := by
  refine a_ne_zero_of_witness 131 3 (by decide) (by decide) ?_
  have hc : Nat.choose 131 3 = 366145 := rfl
  rw [hc]; decide

lemma a_ne_zero_133 : a 133 ≠ 0 := by
  refine a_ne_zero_of_witness 133 3 (by decide) (by decide) ?_
  have hc : Nat.choose 133 3 = 383306 := rfl
  rw [hc]; decide

lemma a_ne_zero_134 : a 134 ≠ 0 := by
  refine a_ne_zero_of_witness 134 2 (by decide) (by decide) ?_
  have hc : Nat.choose 134 2 = 8911 := rfl
  rw [hc]; decide

lemma a_ne_zero_137 : a 137 ≠ 0 := by
  refine a_ne_zero_of_witness 137 4 (by decide) (by decide) ?_
  have hc : Nat.choose 137 4 = 14043870 := rfl
  rw [hc]; decide

lemma a_ne_zero_138 : a 138 ≠ 0 := by
  refine a_ne_zero_of_witness 138 2 (by decide) (by decide) ?_
  have hc : Nat.choose 138 2 = 9453 := rfl
  rw [hc]; decide

lemma a_ne_zero_140 : a 140 ≠ 0 := by
  refine a_ne_zero_of_witness 140 2 (by decide) (by decide) ?_
  have hc : Nat.choose 140 2 = 9730 := rfl
  rw [hc]; decide

lemma a_ne_zero_143 : a 143 ≠ 0 := by
  refine a_ne_zero_of_witness 143 2 (by decide) (by decide) ?_
  have hc : Nat.choose 143 2 = 10153 := rfl
  rw [hc]; decide

lemma a_ne_zero_145 : a 145 ≠ 0 := by
  refine a_ne_zero_of_witness 145 3 (by decide) (by decide) ?_
  have hc : Nat.choose 145 3 = 497640 := rfl
  rw [hc]; decide

lemma a_ne_zero_146 : a 146 ≠ 0 := by
  refine a_ne_zero_of_witness 146 3 (by decide) (by decide) ?_
  have hc : Nat.choose 146 3 = 508080 := rfl
  rw [hc]; decide

lemma a_ne_zero_148 : a 148 ≠ 0 := by
  refine a_ne_zero_of_witness 148 4 (by decide) (by decide) ?_
  have hc : Nat.choose 148 4 = 19190605 := rfl
  rw [hc]; decide

lemma a_ne_zero_151 : a 151 ≠ 0 := by
  refine a_ne_zero_of_witness 151 2 (by decide) (by decide) ?_
  have hc : Nat.choose 151 2 = 11325 := rfl
  rw [hc]; decide

lemma a_ne_zero_152 : a 152 ≠ 0 := by
  refine a_ne_zero_of_witness 152 8 (by decide) (by decide) ?_
  have hc : Nat.choose 152 8 = 5859727868575 := rfl
  rw [hc]; decide

lemma a_ne_zero_155 : a 155 ≠ 0 := by
  refine a_ne_zero_of_witness 155 2 (by decide) (by decide) ?_
  have hc : Nat.choose 155 2 = 11935 := rfl
  rw [hc]; decide

lemma a_ne_zero_157 : a 157 ≠ 0 := by
  refine a_ne_zero_of_witness 157 2 (by decide) (by decide) ?_
  have hc : Nat.choose 157 2 = 12246 := rfl
  rw [hc]; decide

lemma a_ne_zero_158 : a 158 ≠ 0 := by
  refine a_ne_zero_of_witness 158 3 (by decide) (by decide) ?_
  have hc : Nat.choose 158 3 = 644956 := rfl
  rw [hc]; decide

lemma a_ne_zero_161 : a 161 ≠ 0 := by
  refine a_ne_zero_of_witness 161 3 (by decide) (by decide) ?_
  have hc : Nat.choose 161 3 = 682640 := rfl
  rw [hc]; decide

lemma a_ne_zero_162 : a 162 ≠ 0 := by
  refine a_ne_zero_of_witness 162 2 (by decide) (by decide) ?_
  have hc : Nat.choose 162 2 = 13041 := rfl
  rw [hc]; decide

lemma a_ne_zero_164 : a 164 ≠ 0 := by
  refine a_ne_zero_of_witness 164 3 (by decide) (by decide) ?_
  have hc : Nat.choose 164 3 = 721764 := rfl
  rw [hc]; decide

lemma a_ne_zero_167 : a 167 ≠ 0 := by
  refine a_ne_zero_of_witness 167 3 (by decide) (by decide) ?_
  have hc : Nat.choose 167 3 = 762355 := rfl
  rw [hc]; decide

lemma a_ne_zero_168 : a 168 ≠ 0 := by
  refine a_ne_zero_of_witness 168 2 (by decide) (by decide) ?_
  have hc : Nat.choose 168 2 = 14028 := rfl
  rw [hc]; decide

lemma a_ne_zero_171 : a 171 ≠ 0 := by
  refine a_ne_zero_of_witness 171 2 (by decide) (by decide) ?_
  have hc : Nat.choose 171 2 = 14535 := rfl
  rw [hc]; decide

lemma a_ne_zero_173 : a 173 ≠ 0 := by
  refine a_ne_zero_of_witness 173 2 (by decide) (by decide) ?_
  have hc : Nat.choose 173 2 = 14878 := rfl
  rw [hc]; decide

lemma a_ne_zero_174 : a 174 ≠ 0 := by
  refine a_ne_zero_of_witness 174 3 (by decide) (by decide) ?_
  have hc : Nat.choose 174 3 = 862924 := rfl
  rw [hc]; decide

lemma a_ne_zero_176 : a 176 ≠ 0 := by
  refine a_ne_zero_of_witness 176 2 (by decide) (by decide) ?_
  have hc : Nat.choose 176 2 = 15400 := rfl
  rw [hc]; decide

lemma a_ne_zero_179 : a 179 ≠ 0 := by
  refine a_ne_zero_of_witness 179 2 (by decide) (by decide) ?_
  have hc : Nat.choose 179 2 = 15931 := rfl
  rw [hc]; decide

lemma a_ne_zero_181 : a 181 ≠ 0 := by
  refine a_ne_zero_of_witness 181 3 (by decide) (by decide) ?_
  have hc : Nat.choose 181 3 = 971970 := rfl
  rw [hc]; decide

lemma a_ne_zero_182 : a 182 ≠ 0 := by
  refine a_ne_zero_of_witness 182 2 (by decide) (by decide) ?_
  have hc : Nat.choose 182 2 = 16471 := rfl
  rw [hc]; decide

lemma a_ne_zero_185 : a 185 ≠ 0 := by
  refine a_ne_zero_of_witness 185 5 (by decide) (by decide) ?_
  have hc : Nat.choose 185 5 = 1710052162 := rfl
  rw [hc]; decide

lemma a_ne_zero_186 : a 186 ≠ 0 := by
  refine a_ne_zero_of_witness 186 4 (by decide) (by decide) ?_
  have hc : Nat.choose 186 4 = 48277230 := rfl
  rw [hc]; decide

lemma a_ne_zero_188 : a 188 ≠ 0 := by
  refine a_ne_zero_of_witness 188 2 (by decide) (by decide) ?_
  have hc : Nat.choose 188 2 = 17578 := rfl
  rw [hc]; decide

lemma a_ne_zero_191 : a 191 ≠ 0 := by
  refine a_ne_zero_of_witness 191 3 (by decide) (by decide) ?_
  have hc : Nat.choose 191 3 = 1143135 := rfl
  rw [hc]; decide

lemma a_ne_zero_193 : a 193 ≠ 0 := by
  refine a_ne_zero_of_witness 193 2 (by decide) (by decide) ?_
  have hc : Nat.choose 193 2 = 18528 := rfl
  rw [hc]; decide

lemma a_ne_zero_194 : a 194 ≠ 0 := by
  refine a_ne_zero_of_witness 194 6 (by decide) (by decide) ?_
  have hc : Nat.choose 194 6 = 68482017072 := rfl
  rw [hc]; decide

lemma a_ne_zero_196 : a 196 ≠ 0 := by
  refine a_ne_zero_of_witness 196 3 (by decide) (by decide) ?_
  have hc : Nat.choose 196 3 = 1235780 := rfl
  rw [hc]; decide

lemma a_ne_zero_199 : a 199 ≠ 0 := by
  refine a_ne_zero_of_witness 199 3 (by decide) (by decide) ?_
  have hc : Nat.choose 199 3 = 1293699 := rfl
  rw [hc]; decide

lemma a_ne_zero_200 : a 200 ≠ 0 := by
  refine a_ne_zero_of_witness 200 3 (by decide) (by decide) ?_
  have hc : Nat.choose 200 3 = 1313400 := rfl
  rw [hc]; decide

lemma a_ne_zero_203 : a 203 ≠ 0 := by
  refine a_ne_zero_of_witness 203 2 (by decide) (by decide) ?_
  have hc : Nat.choose 203 2 = 20503 := rfl
  rw [hc]; decide

lemma a_ne_zero_205 : a 205 ≠ 0 := by
  refine a_ne_zero_of_witness 205 2 (by decide) (by decide) ?_
  have hc : Nat.choose 205 2 = 20910 := rfl
  rw [hc]; decide

lemma a_ne_zero_206 : a 206 ≠ 0 := by
  refine a_ne_zero_of_witness 206 4 (by decide) (by decide) ?_
  have hc : Nat.choose 206 4 = 72867865 := rfl
  rw [hc]; decide

lemma a_ne_zero_208 : a 208 ≠ 0 := by
  refine a_ne_zero_of_witness 208 3 (by decide) (by decide) ?_
  have hc : Nat.choose 208 3 = 1478256 := rfl
  rw [hc]; decide

lemma a_ne_zero_211 : a 211 ≠ 0 := by
  refine a_ne_zero_of_witness 211 2 (by decide) (by decide) ?_
  have hc : Nat.choose 211 2 = 22155 := rfl
  rw [hc]; decide

lemma a_ne_zero_213 : a 213 ≠ 0 := by
  refine a_ne_zero_of_witness 213 2 (by decide) (by decide) ?_
  have hc : Nat.choose 213 2 = 22578 := rfl
  rw [hc]; decide

lemma a_ne_zero_214 : a 214 ≠ 0 := by
  refine a_ne_zero_of_witness 214 3 (by decide) (by decide) ?_
  have hc : Nat.choose 214 3 = 1610564 := rfl
  rw [hc]; decide

lemma a_ne_zero_217 : a 217 ≠ 0 := by
  refine a_ne_zero_of_witness 217 2 (by decide) (by decide) ?_
  have hc : Nat.choose 217 2 = 23436 := rfl
  rw [hc]; decide

lemma a_ne_zero_218 : a 218 ≠ 0 := by
  refine a_ne_zero_of_witness 218 2 (by decide) (by decide) ?_
  have hc : Nat.choose 218 2 = 23653 := rfl
  rw [hc]; decide

lemma a_ne_zero_220 : a 220 ≠ 0 := by
  refine a_ne_zero_of_witness 220 2 (by decide) (by decide) ?_
  have hc : Nat.choose 220 2 = 24090 := rfl
  rw [hc]; decide

lemma a_ne_zero_223 : a 223 ≠ 0 := by
  refine a_ne_zero_of_witness 223 2 (by decide) (by decide) ?_
  have hc : Nat.choose 223 2 = 24753 := rfl
  rw [hc]; decide

lemma a_ne_zero_224 : a 224 ≠ 0 := by
  refine a_ne_zero_of_witness 224 7 (by decide) (by decide) ?_
  have hc : Nat.choose 224 7 = 5107294278944 := rfl
  rw [hc]; decide

lemma a_ne_zero_227 : a 227 ≠ 0 := by
  refine a_ne_zero_of_witness 227 5 (by decide) (by decide) ?_
  have hc : Nat.choose 227 5 = 4804945320 := rfl
  rw [hc]; decide

lemma a_ne_zero_229 : a 229 ≠ 0 := by
  refine a_ne_zero_of_witness 229 2 (by decide) (by decide) ?_
  have hc : Nat.choose 229 2 = 26106 := rfl
  rw [hc]; decide

lemma a_ne_zero_230 : a 230 ≠ 0 := by
  refine a_ne_zero_of_witness 230 3 (by decide) (by decide) ?_
  have hc : Nat.choose 230 3 = 2001460 := rfl
  rw [hc]; decide

lemma a_ne_zero_233 : a 233 ≠ 0 := by
  refine a_ne_zero_of_witness 233 3 (by decide) (by decide) ?_
  have hc : Nat.choose 233 3 = 2081156 := rfl
  rw [hc]; decide

lemma a_ne_zero_234 : a 234 ≠ 0 := by
  refine a_ne_zero_of_witness 234 2 (by decide) (by decide) ?_
  have hc : Nat.choose 234 2 = 27261 := rfl
  rw [hc]; decide

lemma a_ne_zero_236 : a 236 ≠ 0 := by
  refine a_ne_zero_of_witness 236 3 (by decide) (by decide) ?_
  have hc : Nat.choose 236 3 = 2162940 := rfl
  rw [hc]; decide

lemma a_ne_zero_239 : a 239 ≠ 0 := by
  refine a_ne_zero_of_witness 239 3 (by decide) (by decide) ?_
  have hc : Nat.choose 239 3 = 2246839 := rfl
  rw [hc]; decide

lemma a_ne_zero_241 : a 241 ≠ 0 := by
  refine a_ne_zero_of_witness 241 2 (by decide) (by decide) ?_
  have hc : Nat.choose 241 2 = 28920 := rfl
  rw [hc]; decide

lemma a_ne_zero_242 : a 242 ≠ 0 := by
  refine a_ne_zero_of_witness 242 6 (by decide) (by decide) ?_
  have hc : Nat.choose 242 6 = 262080288316 := rfl
  rw [hc]; decide

lemma a_ne_zero_244 : a 244 ≠ 0 := by
  refine a_ne_zero_of_witness 244 2 (by decide) (by decide) ?_
  have hc : Nat.choose 244 2 = 29646 := rfl
  rw [hc]; decide

lemma a_ne_zero_247 : a 247 ≠ 0 := by
  refine a_ne_zero_of_witness 247 2 (by decide) (by decide) ?_
  have hc : Nat.choose 247 2 = 30381 := rfl
  rw [hc]; decide

lemma a_ne_zero_248 : a 248 ≠ 0 := by
  refine a_ne_zero_of_witness 248 3 (by decide) (by decide) ?_
  have hc : Nat.choose 248 3 = 2511496 := rfl
  rw [hc]; decide

lemma a_ne_zero_251 : a 251 ≠ 0 := by
  refine a_ne_zero_of_witness 251 2 (by decide) (by decide) ?_
  have hc : Nat.choose 251 2 = 31375 := rfl
  rw [hc]; decide

lemma a_ne_zero_253 : a 253 ≠ 0 := by
  refine a_ne_zero_of_witness 253 2 (by decide) (by decide) ?_
  have hc : Nat.choose 253 2 = 31878 := rfl
  rw [hc]; decide

lemma a_ne_zero_254 : a 254 ≠ 0 := by
  refine a_ne_zero_of_witness 254 6 (by decide) (by decide) ?_
  have hc : Nat.choose 254 6 = 351427189575 := rfl
  rw [hc]; decide

lemma a_ne_zero_256 : a 256 ≠ 0 := by
  refine a_ne_zero_of_witness 256 2 (by decide) (by decide) ?_
  have hc : Nat.choose 256 2 = 32640 := rfl
  rw [hc]; decide

lemma a_ne_zero_of_odious_le_256 {n : ℕ} (hn1 : 65 ≤ n) (hn2 : n ≤ 256)
    (hodd : popc n % 2 = 1) : a n ≠ 0 := by
  interval_cases n
  · have : popc 65 % 2 = 0 := by decide
    omega
  · have : popc 66 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_67
  · have : popc 68 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_69
  · exact a_ne_zero_70
  · have : popc 71 % 2 = 0 := by decide
    omega
  · have : popc 72 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_73
  · exact a_ne_zero_74
  · have : popc 75 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_76
  · have : popc 77 % 2 = 0 := by decide
    omega
  · have : popc 78 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_79
  · have : popc 80 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_81
  · exact a_ne_zero_82
  · have : popc 83 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_84
  · have : popc 85 % 2 = 0 := by decide
    omega
  · have : popc 86 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_87
  · exact a_ne_zero_88
  · have : popc 89 % 2 = 0 := by decide
    omega
  · have : popc 90 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_91
  · have : popc 92 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_93
  · exact a_ne_zero_94
  · have : popc 95 % 2 = 0 := by decide
    omega
  · have : popc 96 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_97
  · exact a_ne_zero_98
  · have : popc 99 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_100
  · have : popc 101 % 2 = 0 := by decide
    omega
  · have : popc 102 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_103
  · exact a_ne_zero_104
  · have : popc 105 % 2 = 0 := by decide
    omega
  · have : popc 106 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_107
  · have : popc 108 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_109
  · exact a_ne_zero_110
  · have : popc 111 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_112
  · have : popc 113 % 2 = 0 := by decide
    omega
  · have : popc 114 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_115
  · have : popc 116 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_117
  · exact a_ne_zero_118
  · have : popc 119 % 2 = 0 := by decide
    omega
  · have : popc 120 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_121
  · exact a_ne_zero_122
  · have : popc 123 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_124
  · have : popc 125 % 2 = 0 := by decide
    omega
  · have : popc 126 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_127
  · exact a_ne_zero_128
  · have : popc 129 % 2 = 0 := by decide
    omega
  · have : popc 130 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_131
  · have : popc 132 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_133
  · exact a_ne_zero_134
  · have : popc 135 % 2 = 0 := by decide
    omega
  · have : popc 136 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_137
  · exact a_ne_zero_138
  · have : popc 139 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_140
  · have : popc 141 % 2 = 0 := by decide
    omega
  · have : popc 142 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_143
  · have : popc 144 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_145
  · exact a_ne_zero_146
  · have : popc 147 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_148
  · have : popc 149 % 2 = 0 := by decide
    omega
  · have : popc 150 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_151
  · exact a_ne_zero_152
  · have : popc 153 % 2 = 0 := by decide
    omega
  · have : popc 154 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_155
  · have : popc 156 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_157
  · exact a_ne_zero_158
  · have : popc 159 % 2 = 0 := by decide
    omega
  · have : popc 160 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_161
  · exact a_ne_zero_162
  · have : popc 163 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_164
  · have : popc 165 % 2 = 0 := by decide
    omega
  · have : popc 166 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_167
  · exact a_ne_zero_168
  · have : popc 169 % 2 = 0 := by decide
    omega
  · have : popc 170 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_171
  · have : popc 172 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_173
  · exact a_ne_zero_174
  · have : popc 175 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_176
  · have : popc 177 % 2 = 0 := by decide
    omega
  · have : popc 178 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_179
  · have : popc 180 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_181
  · exact a_ne_zero_182
  · have : popc 183 % 2 = 0 := by decide
    omega
  · have : popc 184 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_185
  · exact a_ne_zero_186
  · have : popc 187 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_188
  · have : popc 189 % 2 = 0 := by decide
    omega
  · have : popc 190 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_191
  · have : popc 192 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_193
  · exact a_ne_zero_194
  · have : popc 195 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_196
  · have : popc 197 % 2 = 0 := by decide
    omega
  · have : popc 198 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_199
  · exact a_ne_zero_200
  · have : popc 201 % 2 = 0 := by decide
    omega
  · have : popc 202 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_203
  · have : popc 204 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_205
  · exact a_ne_zero_206
  · have : popc 207 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_208
  · have : popc 209 % 2 = 0 := by decide
    omega
  · have : popc 210 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_211
  · have : popc 212 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_213
  · exact a_ne_zero_214
  · have : popc 215 % 2 = 0 := by decide
    omega
  · have : popc 216 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_217
  · exact a_ne_zero_218
  · have : popc 219 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_220
  · have : popc 221 % 2 = 0 := by decide
    omega
  · have : popc 222 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_223
  · exact a_ne_zero_224
  · have : popc 225 % 2 = 0 := by decide
    omega
  · have : popc 226 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_227
  · have : popc 228 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_229
  · exact a_ne_zero_230
  · have : popc 231 % 2 = 0 := by decide
    omega
  · have : popc 232 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_233
  · exact a_ne_zero_234
  · have : popc 235 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_236
  · have : popc 237 % 2 = 0 := by decide
    omega
  · have : popc 238 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_239
  · have : popc 240 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_241
  · exact a_ne_zero_242
  · have : popc 243 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_244
  · have : popc 245 % 2 = 0 := by decide
    omega
  · have : popc 246 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_247
  · exact a_ne_zero_248
  · have : popc 249 % 2 = 0 := by decide
    omega
  · have : popc 250 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_251
  · have : popc 252 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_253
  · exact a_ne_zero_254
  · have : popc 255 % 2 = 0 := by decide
    omega
  · exact a_ne_zero_256

lemma popc_eq_zero_iff (n : ℕ) : popc n = 0 ↔ n = 0 := by
  constructor
  · intro h
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [popc_rec] at h
        have hsum : (n + 1) % 2 + popc ((n + 1) / 2) = 0 := h
        have hhalf : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
        have : popc ((n + 1) / 2) = 0 := by omega
        have : (n + 1) / 2 = 0 := ih _ hhalf this
        omega
  · intro h; subst h; exact popc_zero

lemma popc_eq_one_iff (n : ℕ) : popc n = 1 ↔ ∃ m, n = 2 ^ m := by
  constructor
  · intro h
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero =>
        simp [popc_zero] at h
      | succ n =>
        rw [popc_rec] at h
        rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
        · -- even
          rw [he, zero_add] at h
          have hhalf : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
          obtain ⟨m, hm⟩ := ih _ hhalf h
          refine ⟨m + 1, ?_⟩
          have : n + 1 = 2 * ((n + 1) / 2) := by
            have := Nat.div_add_mod (n + 1) 2
            omega
          rw [this, hm, pow_succ, mul_comm]
        · -- odd: (n+1)%2=1 so popc((n+1)/2)=0 so (n+1)/2=0 so n+1=1
          rw [ho] at h
          have : popc ((n + 1) / 2) = 0 := by omega
          have : (n + 1) / 2 = 0 := (popc_eq_zero_iff _).1 this
          have hn1 : n + 1 = 1 := by omega
          refine ⟨0, ?_⟩
          simp [hn1]
  · rintro ⟨m, rfl⟩
    exact popc_two_pow m

lemma exists_log2_of_popc_eq_one {n : ℕ} (h : popc n = 1) : n = 2 ^ n.log2 := by
  obtain ⟨m, hm⟩ := (popc_eq_one_iff n).1 h
  subst hm
  have : (2 ^ m).log2 = m := by
    -- log2 (2^m) = m
    rw [Nat.log2_eq_log_two, Nat.log_pow (by decide : 1 < 2)]
  rw [this]

lemma log2_two_pow (m : ℕ) : (2 ^ m).log2 = m := by
  rw [Nat.log2_eq_log_two, Nat.log_pow (by decide : 1 < 2)]

lemma log2_ge_of_ge_two_pow {n m : ℕ} (h : 2 ^ m ≤ n) : m ≤ n.log2 := by
  have hlt : n < 2 ^ (n.log2 + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have : 2 ^ m < 2 ^ (n.log2 + 1) := h.trans_lt hlt
  have : m < n.log2 + 1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 this
  omega

/- Extra popcount lemmas -/

lemma popc_two_pow_mul_add {a b i : ℕ} (hb : b < 2 ^ i) :
    popc (2 ^ i * a + b) = popc a + popc b := by
  induction i generalizing a b with
  | zero =>
    have : b = 0 := by
      have : b < 1 := by simpa using hb
      omega
    subst this
    simp [popc_zero]
  | succ i ih =>
    rw [popc_rec (2 ^ (i + 1) * a + b), popc_rec b]
    have hmod : (2 ^ (i + 1) * a + b) % 2 = b % 2 := by
      have : 2 ^ (i + 1) * a = 2 * (2 ^ i * a) := by
        rw [pow_succ]
        ring
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    have hdiv : (2 ^ (i + 1) * a + b) / 2 = 2 ^ i * a + b / 2 := by
      have : 2 ^ (i + 1) * a = 2 * (2 ^ i * a) := by
        rw [pow_succ]
        ring
      rw [this, Nat.mul_add_div (by decide : 0 < 2)]
    rw [hmod, hdiv]
    have hb' : b / 2 < 2 ^ i := by
      have : b < 2 * 2 ^ i := by
        rwa [pow_succ, mul_comm] at hb
      omega
    rw [ih hb']
    omega

lemma popc_mul_pow_sixteen (d j : ℕ) : popc (d * 16 ^ j) = popc d := by
  have : 16 ^ j = 2 ^ (4 * j) := by
    rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]
  rw [this, mul_comm, popc_mul_two_pow]

lemma popc_nibble_add {n d j : ℕ} (hn : n < 16 ^ j) :
    popc (n + d * 16 ^ j) = popc d + popc n := by
  have h16 : 16 ^ j = 2 ^ (4 * j) := by
    rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]
  have hn' : n < 2 ^ (4 * j) := by rwa [← h16]
  rw [h16, mul_comm d, add_comm]
  exact popc_two_pow_mul_add hn'

/- Closed forms for `C(2^m, k)` -/

lemma three_dvd_two_pow_sub_one_of_even {k : ℕ} (hk : k % 2 = 0) :
    3 ∣ 2 ^ k - 1 := by
  have hk2 : 2 ∣ k := Nat.dvd_of_mod_eq_zero hk
  obtain ⟨t, rfl⟩ := hk2
  -- 2^{2t} - 1 = (2^2)^t - 1, and 4 - 1 = 3
  simpa [pow_mul] using Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 t

lemma descFactorial_five (n : ℕ) :
    n.descFactorial 5 = (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma descFactorial_three (n : ℕ) :
    n.descFactorial 3 = (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma five_dvd_two_pow_sub_one_of_four_dvd {k : ℕ} (hk : 4 ∣ k) :
    5 ∣ 2 ^ k - 1 := by
  obtain ⟨t, rfl⟩ := hk
  have : 2 ^ 4 - 1 = 15 := by decide
  have h15 : 15 ∣ 2 ^ (4 * t) - 1 := by
    simpa [pow_mul] using Nat.sub_dvd_pow_sub_pow (2 ^ 4) 1 t
  exact dvd_trans (by decide : 5 ∣ 15) h15

lemma five_dvd_two_pow_sub_three_of_mod_four_eq_three {k : ℕ}
    (hk : k % 4 = 3) :
    5 ∣ 2 ^ k - 3 := by
  have : 2 ^ k % 5 = 3 := by
    -- 2^k = 2^{4q+3} = (16^q)*8 ≡ 1^q * 3 ≡ 3 [MOD 5]
    have hk' : k = 4 * (k / 4) + 3 := by omega
    rw [hk', pow_add, pow_mul]
    have h16 : 2 ^ 4 % 5 = 1 := by decide
    have h8 : 2 ^ 3 % 5 = 3 := by decide
    rw [Nat.mul_mod, Nat.pow_mod, h16, one_pow]
    simp [h8]
  have hle : 3 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    calc 3 ≤ 4 := by decide
         _ = 2 ^ 2 := by decide
         _ ≤ 2 ^ k := this
  -- 2^k - 3 ≡ 0 [MOD 5]
  have : (2 ^ k - 3) % 5 = 0 := by
    rw [Nat.sub_mod_eq_zero_of_mod_eq]
    omega
  exact Nat.dvd_of_mod_eq_zero this

lemma fifteen_dvd_prod5 {m : ℕ} (hodd : m % 2 = 1) (hm : 2 ≤ m) :
    15 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) := by
  have h3 : 3 ∣ 2 ^ (m - 1) - 1 := by
    apply three_dvd_two_pow_sub_one_of_even
    omega
  have h5 : 5 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) := by
    rcases Nat.mod_two_eq_zero_or_one (m / 2) with h | h
    · -- m = 4q+1 since m odd and m/2 even
      have : m % 4 = 1 := by omega
      have : 4 ∣ m - 1 := by omega
      have : 5 ∣ 2 ^ (m - 1) - 1 := five_dvd_two_pow_sub_one_of_four_dvd this
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _) _
    · -- m = 4q+3
      have : m % 4 = 3 := by omega
      have : 5 ∣ 2 ^ m - 3 := five_dvd_two_pow_sub_three_of_mod_four_eq_three this
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right this _) _
  have h15 : Nat.Coprime 3 5 := by decide
  have : 15 = 3 * 5 := by decide
  rw [this]
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd h15 ?_ h5
  convert (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h3
      ((2 ^ m - 3) * (2 ^ (m - 2) - 1))) (2 ^ m - 1)) using 1
  ring

lemma choose_two_pow_five (m : ℕ) (hm : 5 ≤ m) :
    Nat.choose (2 ^ m) 5 =
      2 ^ m * ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) / 15) := by
  have h5le : 5 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 5 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 5 =
      (2 ^ m - 4) * (2 ^ m - 3) * (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m :=
    descFactorial_five _
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have hm2 : 2 ≤ m := by omega
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel hm2]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hprod :
      (2 ^ m).descFactorial 5 =
        2 ^ (m + 3) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1)) := by
    rw [hdesc, h4, h2]
    ring_nf
  have hfac : (2 ^ m).descFactorial 5 = 120 * Nat.choose (2 ^ m) 5 := by
    have : 5 ! = 120 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  -- 2^{m+3} * Prod = 120 * choose = 8 * 15 * choose
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by
    have : 2 ^ (m + 3) = 2 ^ m * 2 ^ 3 := pow_add _ _ _
    rw [this, show (2 : ℕ) ^ 3 = 8 from rfl, mul_comm]
  rw [h8] at hfac
  -- 8 * 2^m * Prod = 8 * 15 * choose
  have : 8 * (2 ^ m * ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1))) =
      8 * (15 * Nat.choose (2 ^ m) 5) := by
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 8) this
  -- 2^m * Prod = 15 * choose, so choose = 2^m * (Prod / 15) if 15 | Prod
  have h15dvd : 15 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) := by
    -- 15 | descFactorial / 2^{m+3} because 120 | descFactorial and the 8 is accounted
    -- Use that 15 | 2^m * Prod from the equation, and coprime 15 2^m
    have : 15 ∣ 2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1)) :=
      ⟨Nat.choose (2 ^ m) 5, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 15 (2 ^ m) := by
      have : Nat.Coprime 15 2 := by decide
      simpa using this.pow_right m
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 5 =
      (2 ^ m * ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1))) / 15 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (15 : ℕ) ≠ 0)
    convert hcancel.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h15dvd]

/- Hex evaluation (LSB-first nibble lists) -/

def hexEval : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 16 * hexEval ds

lemma hexEval_nil : hexEval [] = 0 := rfl

lemma hexEval_cons (d : ℕ) (ds : List ℕ) : hexEval (d :: ds) = d + 16 * hexEval ds := rfl

lemma popc_hexEval : ∀ ds : List ℕ, (∀ d ∈ ds, d < 16) →
    popc (hexEval ds) = (ds.map popc).sum
  | [], _ => by simp [hexEval, popc_zero]
  | d :: ds, h => by
    have hd : d < 16 := h d (List.mem_cons_self)
    have hds : ∀ x ∈ ds, x < 16 := fun x hx => h x (List.mem_cons_of_mem d hx)
    have hform : d + 16 * hexEval ds = d + hexEval ds * 16 ^ 1 := by
      rw [pow_one, mul_comm]
    rw [hexEval_cons, hform, popc_nibble_add (j := 1) (by simpa using hd)]
    rw [popc_hexEval ds hds]
    simp [add_comm]

lemma hexEval_append : ∀ l₁ l₂ : List ℕ,
    hexEval (l₁ ++ l₂) = hexEval l₁ + 16 ^ l₁.length * hexEval l₂
  | [], l₂ => by simp [hexEval]
  | d :: l₁, l₂ => by
    rw [List.cons_append, hexEval_cons, hexEval_append l₁ l₂, hexEval_cons, List.length_cons]
    have : d + 16 * (hexEval l₁ + 16 ^ l₁.length * hexEval l₂) =
        d + 16 * hexEval l₁ + 16 ^ (l₁.length + 1) * hexEval l₂ := by
      rw [pow_succ]; ring
    exact this

lemma geom_sum_sixteen (n : ℕ) :
    (∑ i ∈ Finset.range n, 16 ^ i) * 15 = 16 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    have hle : 1 ≤ 16 ^ n :=
      (Nat.one_le_two_pow).trans (Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 16) n)
    have : 16 ^ n - 1 + 16 ^ n * 15 = 16 ^ n * 16 - 1 := by omega
    exact this

lemma sixteen_pow_eq_geom (n : ℕ) :
    16 ^ n = (∑ i ∈ Finset.range n, 16 ^ i) * 15 + 1 := by
  have h := geom_sum_sixteen n
  have hle : 1 ≤ 16 ^ n := Nat.one_le_pow _ _ (by decide)
  omega

lemma hexEval_replicate (d n : ℕ) :
    hexEval (List.replicate n d) = d * ∑ i ∈ Finset.range n, 16 ^ i := by
  induction n with
  | zero => simp [hexEval]
  | succ n ih =>
    rw [List.replicate_succ, hexEval_cons, ih, Finset.sum_range_succ]
    have hpow := sixteen_pow_eq_geom n
    rw [hpow]
    ring

lemma hexEval_singleton (d : ℕ) : hexEval [d] = d := by simp [hexEval]

lemma hexEval_pair (d e : ℕ) : hexEval [d, e] = d + 16 * e := by simp [hexEval]

lemma map_popc_replicate (d n : ℕ) :
    (List.map popc (List.replicate n d)).sum = n * popc d := by
  rw [List.map_replicate, List.sum_replicate]
  simp

/- Digit list for the odd part of `C(2^{8t+5}, 5)`, `t ≥ 1`. LSB first. -/

def digits_8t5 (t : ℕ) : List ℕ :=
  [13] ++ List.replicate (2 * t - 1) 12 ++ [4, 1] ++ List.replicate (2 * t - 1) 2
    ++ [10, 8] ++ List.replicate (2 * t) 7 ++ [1] ++ List.replicate (2 * t) 2

lemma digits_8t5_lt (t : ℕ) : ∀ d ∈ digits_8t5 t, d < 16 := by
  intro d hd
  unfold digits_8t5 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate] at hd
  aesop

lemma popc_digits_8t5 (t : ℕ) (ht : 1 ≤ t) :
    (List.map popc (digits_8t5 t)).sum = 14 * t + 6 := by
  have h13 : popc 13 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h10 : popc 10 = 2 := by decide
  have h8 : popc 8 = 1 := by decide
  have h7 : popc 7 = 3 := by decide
  have hrep (d n : ℕ) : (List.map popc (List.replicate n d)).sum = n * popc d := by
    simp [List.map_replicate, List.sum_replicate]
  unfold digits_8t5
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil]
  rw [hrep, hrep, hrep, hrep]
  rw [h13, h12, h4, h2, h10, h8, h7]
  omega

lemma popc_hexEval_digits_8t5 (t : ℕ) (ht : 1 ≤ t) :
    popc (hexEval (digits_8t5 t)) = 14 * t + 6 := by
  rw [popc_hexEval _ (digits_8t5_lt t), popc_digits_8t5 t ht]

lemma hexEval_digits_8t5_eq (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_8t5 t) =
      13 + 16 * (12 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ i)
        + 16 ^ (2 * t) * 20
        + 16 ^ (2 * t + 2) * (2 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ i)
        + 16 ^ (4 * t + 1) * 138
        + 16 ^ (4 * t + 3) * (7 * ∑ i ∈ Finset.range (2 * t), 16 ^ i)
        + 16 ^ (6 * t + 3)
        + 16 ^ (6 * t + 4) * (2 * ∑ i ∈ Finset.range (2 * t), 16 ^ i) := by
  unfold digits_8t5
  rw [hexEval_append, hexEval_append, hexEval_append, hexEval_append,
      hexEval_append, hexEval_append, hexEval_append]
  simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate,
    hexEval_singleton, hexEval_pair, hexEval_replicate]
  have hp20 : (4 + 16 * 1 : ℕ) = 20 := by decide
  have hp138 : (10 + 16 * 8 : ℕ) = 138 := by decide
  have f2 : (0 + 1 + 1 : ℕ) = 2 := rfl
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  rw [hp20, hp138, f2, f1]
  have e0 : (16 : ℕ) ^ 1 = 16 := pow_one 16
  rw [e0]
  have e1 : 1 + (2 * t - 1) = 2 * t := by omega
  rw [e1]
  have e3 : 2 * t + 2 + (2 * t - 1) = 4 * t + 1 := by omega
  rw [e3]
  have e4 : 4 * t + 1 + 2 = 4 * t + 3 := by omega
  rw [e4]
  have e5 : 4 * t + 3 + 2 * t = 6 * t + 3 := by omega
  rw [e5]
  have e6 : 6 * t + 3 + 1 = 6 * t + 4 := by omega
  rw [e6]
  ring

lemma two_pow_as_sixteen (t : ℕ) :
    2 ^ (8 * t + 5) = 32 * 16 ^ (2 * t) ∧
    2 ^ (8 * t + 4) = 16 * 16 ^ (2 * t) ∧
    2 ^ (8 * t + 3) = 8 * 16 ^ (2 * t) := by
  have h16 : 16 ^ (2 * t) = 2 ^ (8 * t) := by
    rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_add, h16]; ring
  · rw [pow_add, h16]; ring
  · rw [pow_add, h16]; ring

lemma poly_id (u : ℤ) :
    (195 : ℤ) + (12 * u - 192) + u * 300 + (32 * u ^ 2 - 512 * u)
      + u ^ 2 * 16 * 2070 + u ^ 2 * 4096 * 7 * (u - 1)
      + u ^ 3 * 4096 * 15 + u ^ 3 * 65536 * 2 * (u - 1) =
    (32 * u - 1) * (16 * u - 1) * (32 * u - 3) * (8 * u - 1) := by
  ring

lemma nat_mul_sub_left (a b c : ℕ) (h : c ≤ b) :
    a * (b - c) = a * b - a * c := by
  zify [h, Nat.mul_le_mul_left a h]
  ring

/-- The hex expansion equals the odd part of `C(2^{8t+5}, 5)`. -/
lemma hexEval_digits_8t5_mul_fifteen (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_8t5 t) * 15 =
      (2 ^ (8 * t + 5) - 1) * (2 ^ (8 * t + 4) - 1) *
        (2 ^ (8 * t + 5) - 3) * (2 ^ (8 * t + 3) - 1) := by
  have hex := hexEval_digits_8t5_eq t ht
  set G1 := ∑ i ∈ Finset.range (2 * t - 1), 16 ^ i with hG1def
  set G2 := ∑ i ∈ Finset.range (2 * t), 16 ^ i with hG2def
  set u := 16 ^ (2 * t) with hudef
  have hG1 : G1 * 15 = 16 ^ (2 * t - 1) - 1 := by
    rw [hG1def]; exact geom_sum_sixteen _
  have hG2 : G2 * 15 = u - 1 := by
    rw [hG2def, hudef]; exact geom_sum_sixteen _
  have h2t1 : 1 ≤ 16 ^ (2 * t - 1) := Nat.one_le_pow _ _ (by decide)
  have hu_pos : 1 ≤ u := by rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have hpows := two_pow_as_sixteen t
  have h8t5 : 2 ^ (8 * t + 5) = 32 * u := by rw [hudef]; exact hpows.1
  have h8t4 : 2 ^ (8 * t + 4) = 16 * u := by rw [hudef]; exact hpows.2.1
  have h8t3 : 2 ^ (8 * t + 3) = 8 * u := by rw [hudef]; exact hpows.2.2
  have hu2 : 16 ^ (2 * t + 2) = 256 * u := by
    rw [hudef, pow_add, pow_two]; ring
  have hu41 : 16 ^ (4 * t + 1) = 16 * u ^ 2 := by
    have : 4 * t + 1 = (2 * t) + (2 * t) + 1 := by omega
    rw [hudef, this, pow_add, pow_add, pow_one]
    ring
  have hu43 : 16 ^ (4 * t + 3) = 4096 * u ^ 2 := by
    have : 4 * t + 3 = (2 * t) + (2 * t) + 3 := by omega
    rw [hudef, this, pow_add, pow_add]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this]
    ring
  have hu63 : 16 ^ (6 * t + 3) = 4096 * u ^ 3 := by
    have : 6 * t + 3 = (2 * t) + (2 * t) + (2 * t) + 3 := by omega
    rw [hudef, this, pow_add, pow_add, pow_add]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this]
    ring
  have hu64 : 16 ^ (6 * t + 4) = 65536 * u ^ 3 := by
    have : 6 * t + 4 = (2 * t) + (2 * t) + (2 * t) + 4 := by omega
    rw [hudef, this, pow_add, pow_add, pow_add]
    have : (16 : ℕ) ^ 4 = 65536 := by decide
    rw [this]
    ring
  have h16u : 16 * 16 ^ (2 * t - 1) = u := by
    rw [hudef]
    trans 16 ^ ((2 * t - 1) + 1)
    · rw [pow_add, pow_one, mul_comm]
    · congr 1; omega
  have hex15 :
      hexEval (digits_8t5 t) * 15 =
        195 + 192 * (16 ^ (2 * t - 1) - 1) + 300 * u
          + 512 * u * (16 ^ (2 * t - 1) - 1)
          + 16 * 2070 * u ^ 2
          + 4096 * 7 * u ^ 2 * (u - 1)
          + 4096 * 15 * u ^ 3
          + 65536 * 2 * u ^ 3 * (u - 1) := by
    rw [hex]
    have hA :
        (13 + 16 * (12 * G1) + 16 ^ (2 * t) * 20
          + 16 ^ (2 * t + 2) * (2 * G1)
          + 16 ^ (4 * t + 1) * 138
          + 16 ^ (4 * t + 3) * (7 * G2)
          + 16 ^ (6 * t + 3)
          + 16 ^ (6 * t + 4) * (2 * G2)) * 15
        =
        13 * 15 + 16 * 12 * (G1 * 15) + u * 20 * 15
          + 16 ^ (2 * t + 2) * 2 * (G1 * 15)
          + 16 ^ (4 * t + 1) * 138 * 15
          + 16 ^ (4 * t + 3) * 7 * (G2 * 15)
          + 16 ^ (6 * t + 3) * 15
          + 16 ^ (6 * t + 4) * 2 * (G2 * 15) := by
      rw [hudef]; ring
    rw [hA, hG1, hG2, hu2, hu41, hu43, hu63, hu64]
    ring
  have h192 : 192 * (16 ^ (2 * t - 1) - 1) = 12 * u - 192 := by
    rw [nat_mul_sub_left _ _ _ h2t1]
    have : 192 * 16 ^ (2 * t - 1) = 12 * u := by
      have : 192 = 12 * 16 := by decide
      rw [this, mul_assoc, h16u]
    rw [this]
  have h512 : 512 * u * (16 ^ (2 * t - 1) - 1) = 32 * u ^ 2 - 512 * u := by
    have : 512 * u * (16 ^ (2 * t - 1) - 1) =
        512 * u * 16 ^ (2 * t - 1) - 512 * u := by
      rw [nat_mul_sub_left (512 * u) _ _ h2t1, mul_one]
    rw [this]
    have : 512 * u * 16 ^ (2 * t - 1) = 32 * u ^ 2 := by
      have : 512 = 32 * 16 := by decide
      rw [this]
      calc
        32 * 16 * u * 16 ^ (2 * t - 1) = 32 * u * (16 * 16 ^ (2 * t - 1)) := by ring
        _ = 32 * u * u := by rw [h16u]
        _ = 32 * u ^ 2 := by ring
    rw [this]
  rw [hex15, h192, h512]
  have hR :
      (2 ^ (8 * t + 5) - 1) * (2 ^ (8 * t + 4) - 1) *
        (2 ^ (8 * t + 5) - 3) * (2 ^ (8 * t + 3) - 1) =
      (32 * u - 1) * (16 * u - 1) * (32 * u - 3) * (8 * u - 1) := by
    rw [h8t5, h8t4, h8t3]
  rw [hR]
  have hu1 : 1 ≤ u := hu_pos
  have hu16 : 16 ≤ u := by
    rw [hudef]
    have : 16 ^ 1 ≤ 16 ^ (2 * t) :=
      Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ 2 * t)
    simpa using this
  have h12u : 192 ≤ 12 * u := by
    have : 12 * 16 ≤ 12 * u := Nat.mul_le_mul_left 12 hu16
    simpa using this
  have h32u2 : 512 * u ≤ 32 * u ^ 2 := by
    have : 32 * u ^ 2 = 32 * u * u := by ring
    rw [this]
    have h512' : 512 * u = 32 * 16 * u := by
      have : 512 = 32 * 16 := by decide
      rw [this]
    rw [h512']
    have : 32 * 16 * u ≤ 32 * u * u := by
      have := Nat.mul_le_mul_left (32 * u) hu16
      convert this using 1 <;> ring
    exact this
  have h32u : 1 ≤ 32 * u := one_le_mul (by decide : 1 ≤ 32) hu1
  have h16u' : 1 ≤ 16 * u := one_le_mul (by decide : 1 ≤ 16) hu1
  have h32u3 : 3 ≤ 32 * u :=
    (by decide : 3 ≤ 32).trans (Nat.le_mul_of_pos_right 32 hu1)
  have h8u : 1 ≤ 8 * u := one_le_mul (by decide : 1 ≤ 8) hu1
  apply Int.ofNat_inj.mp
  have hz :
      ((195 + (12 * u - 192) + 300 * u + (32 * u ^ 2 - 512 * u)
        + 16 * 2070 * u ^ 2 + 4096 * 7 * u ^ 2 * (u - 1)
        + 4096 * 15 * u ^ 3 + 65536 * 2 * u ^ 3 * (u - 1) : ℕ) : ℤ)
      =
      (195 : ℤ) + (12 * u - 192) + u * 300 + (32 * u ^ 2 - 512 * u)
        + u ^ 2 * 16 * 2070 + u ^ 2 * 4096 * 7 * (u - 1)
        + u ^ 3 * 4096 * 15 + u ^ 3 * 65536 * 2 * (u - 1) := by
    have hu1' : (1 : ℕ) ≤ u := hu1
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rw [Int.natCast_sub h12u, Int.natCast_sub h32u2, Int.natCast_sub hu1']
    simp only [Int.natCast_mul, Int.natCast_pow]
    ring
  have hRint :
      (((32 * u - 1) * (16 * u - 1) * (32 * u - 3) * (8 * u - 1) : ℕ) : ℤ)
      =
      (32 * (u : ℤ) - 1) * (16 * u - 1) * (32 * u - 3) * (8 * u - 1) := by
    simp only [Int.natCast_mul]
    rw [Int.natCast_sub h32u, Int.natCast_sub h16u', Int.natCast_sub h32u3, Int.natCast_sub h8u]
    simp only [Int.natCast_mul]
    norm_cast
  rw [hz, hRint, poly_id]

/-- For `m ≡ 5 (mod 8)`, `m ≥ 13`, `C(2^m, 5)` is evil. -/
lemma popc_choose_two_pow_five_of_mod_eight_eq_five {m : ℕ}
    (hm : 13 ≤ m) (hmod : m % 8 = 5) :
    popc (Nat.choose (2 ^ m) 5) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 8 * t + 5 := ⟨m / 8, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hm5 : 5 ≤ m := by omega
  rw [choose_two_pow_five m hm5]
  -- popc (2^m * (Prod/15)) = popc (Prod/15)
  rw [popc_mul_two_pow]
  have hodd : m % 2 = 1 := by omega
  have h15 := fifteen_dvd_prod5 (m := m) hodd (by omega)
  -- Prod/15 = hexEval (digits_8t5 t)
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) / 15 =
        hexEval (digits_8t5 t) := by
    rw [ht]
    have : (8 * t + 5) - 1 = 8 * t + 4 := by omega
    rw [this]
    have : (8 * t + 5) - 2 = 8 * t + 3 := by omega
    rw [this]
    have := hexEval_digits_8t5_mul_fifteen t ht1
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 15) this.symm
  rw [hex, popc_hexEval_digits_8t5 t ht1]
  omega

lemma a_ne_zero_two_pow_mod8_eq_five {m : ℕ} (hm : 13 ≤ m) (hmod : m % 8 = 5) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 5 (by decide) ?_
    (popc_choose_two_pow_five_of_mod_eight_eq_five hm hmod)
  have : 5 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 5 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  exact this

/- Digit list for the odd part of `C(2^{8t+7}, 5)`, `t ≥ 1`. LSB first. -/

def digits_8t7 (t : ℕ) : List ℕ :=
  [13] ++ List.replicate (2 * t) 12 ++ [14, 1] ++ List.replicate (2 * t - 1) 2
    ++ [10, 8] ++ List.replicate (2 * t) 7 ++ [15, 1] ++ List.replicate (2 * t) 2

lemma digits_8t7_lt (t : ℕ) : ∀ d ∈ digits_8t7 t, d < 16 := by
  intro d hd
  unfold digits_8t7 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate] at hd
  aesop

lemma popc_digits_8t7 (t : ℕ) (_ht : 1 ≤ t) :
    (List.map popc (digits_8t7 t)).sum = 14 * t + 14 := by
  have h13 : popc 13 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h14 : popc 14 = 3 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h10 : popc 10 = 2 := by decide
  have h8 : popc 8 = 1 := by decide
  have h7 : popc 7 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  unfold digits_8t7
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil]
  rw [map_popc_replicate, map_popc_replicate, map_popc_replicate, map_popc_replicate]
  rw [h13, h12, h14, h1, h2, h10, h8, h7, h15]
  omega

lemma popc_hexEval_digits_8t7 (t : ℕ) (ht : 1 ≤ t) :
    popc (hexEval (digits_8t7 t)) = 14 * t + 14 := by
  rw [popc_hexEval _ (digits_8t7_lt t), popc_digits_8t7 t ht]

lemma hexEval_digits_8t7_eq (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_8t7 t) =
      13 + 16 * (12 * ∑ i ∈ Finset.range (2 * t), 16 ^ i)
        + 16 ^ (2 * t + 1) * 30
        + 16 ^ (2 * t + 3) * (2 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ i)
        + 16 ^ (4 * t + 2) * 138
        + 16 ^ (4 * t + 4) * (7 * ∑ i ∈ Finset.range (2 * t), 16 ^ i)
        + 16 ^ (6 * t + 4) * 31
        + 16 ^ (6 * t + 6) * (2 * ∑ i ∈ Finset.range (2 * t), 16 ^ i) := by
  unfold digits_8t7
  rw [hexEval_append, hexEval_append, hexEval_append, hexEval_append,
      hexEval_append, hexEval_append, hexEval_append]
  simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate,
    hexEval_singleton, hexEval_pair, hexEval_replicate]
  have hp30 : (14 + 16 * 1 : ℕ) = 30 := by decide
  have hp138 : (10 + 16 * 8 : ℕ) = 138 := by decide
  have hp31 : (15 + 16 * 1 : ℕ) = 31 := by decide
  have f2 : (0 + 1 + 1 : ℕ) = 2 := rfl
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  rw [hp30, hp138, hp31, f2, f1]
  have e0 : (16 : ℕ) ^ 1 = 16 := pow_one 16
  rw [e0]
  have e1 : 1 + 2 * t = 2 * t + 1 := by omega
  rw [e1]
  have e2 : 2 * t + 1 + 2 = 2 * t + 3 := by omega
  rw [e2]
  have e3 : 2 * t + 3 + (2 * t - 1) = 4 * t + 2 := by omega
  rw [e3]
  have e4 : 4 * t + 2 + 2 = 4 * t + 4 := by omega
  rw [e4]
  have e5 : 4 * t + 4 + 2 * t = 6 * t + 4 := by omega
  rw [e5]

lemma two_pow_as_sixteen_7 (t : ℕ) :
    2 ^ (8 * t + 7) = 128 * 16 ^ (2 * t) ∧
    2 ^ (8 * t + 6) = 64 * 16 ^ (2 * t) ∧
    2 ^ (8 * t + 5) = 32 * 16 ^ (2 * t) := by
  have h16 : 16 ^ (2 * t) = 2 ^ (8 * t) := by
    rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_add, h16]; ring
  · rw [pow_add, h16]; ring
  · rw [pow_add, h16]; ring

lemma poly_id_7 (u : ℤ) :
    (195 : ℤ) + 192 * (u - 1) + 7200 * u + (512 * u ^ 2 - 8192 * u)
      + 529920 * u ^ 2 + 458752 * u ^ 2 * (u - 1)
      + 30474240 * u ^ 3 + 33554432 * u ^ 3 * (u - 1) =
    (128 * u - 1) * (64 * u - 1) * (128 * u - 3) * (32 * u - 1) := by
  ring

lemma hexEval_digits_8t7_mul_fifteen (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_8t7 t) * 15 =
      (2 ^ (8 * t + 7) - 1) * (2 ^ (8 * t + 6) - 1) *
        (2 ^ (8 * t + 7) - 3) * (2 ^ (8 * t + 5) - 1) := by
  have hex := hexEval_digits_8t7_eq t ht
  set G1 := ∑ i ∈ Finset.range (2 * t - 1), 16 ^ i with hG1def
  set G2 := ∑ i ∈ Finset.range (2 * t), 16 ^ i with hG2def
  set u := 16 ^ (2 * t) with hudef
  have hG1 : G1 * 15 = 16 ^ (2 * t - 1) - 1 := by
    rw [hG1def]; exact geom_sum_sixteen _
  have hG2 : G2 * 15 = u - 1 := by
    rw [hG2def, hudef]; exact geom_sum_sixteen _
  have h2t1 : 1 ≤ 16 ^ (2 * t - 1) := Nat.one_le_pow _ _ (by decide)
  have hu_pos : 1 ≤ u := by rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have hpows := two_pow_as_sixteen_7 t
  have h8t7 : 2 ^ (8 * t + 7) = 128 * u := by rw [hudef]; exact hpows.1
  have h8t6 : 2 ^ (8 * t + 6) = 64 * u := by rw [hudef]; exact hpows.2.1
  have h8t5 : 2 ^ (8 * t + 5) = 32 * u := by rw [hudef]; exact hpows.2.2
  have hu21 : 16 ^ (2 * t + 1) = 16 * u := by
    rw [hudef, pow_add, pow_one, mul_comm]
  have hu23 : 16 ^ (2 * t + 3) = 4096 * u := by
    rw [hudef, pow_add]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this, mul_comm]
  have hu42 : 16 ^ (4 * t + 2) = 256 * u ^ 2 := by
    have : 4 * t + 2 = (2 * t) + (2 * t) + 2 := by omega
    rw [hudef, this, pow_add, pow_add]
    have : (16 : ℕ) ^ 2 = 256 := by decide
    rw [this]; ring
  have hu44 : 16 ^ (4 * t + 4) = 65536 * u ^ 2 := by
    have : 4 * t + 4 = (2 * t) + (2 * t) + 4 := by omega
    rw [hudef, this, pow_add, pow_add]
    have : (16 : ℕ) ^ 4 = 65536 := by decide
    rw [this]; ring
  have hu64 : 16 ^ (6 * t + 4) = 65536 * u ^ 3 := by
    have : 6 * t + 4 = (2 * t) + (2 * t) + (2 * t) + 4 := by omega
    rw [hudef, this, pow_add, pow_add, pow_add]
    have : (16 : ℕ) ^ 4 = 65536 := by decide
    rw [this]; ring
  have hu66 : 16 ^ (6 * t + 6) = 16777216 * u ^ 3 := by
    have : 6 * t + 6 = (2 * t) + (2 * t) + (2 * t) + 6 := by omega
    rw [hudef, this, pow_add, pow_add, pow_add]
    have : (16 : ℕ) ^ 6 = 16777216 := by decide
    rw [this]; ring
  have h16u : 16 * 16 ^ (2 * t - 1) = u := by
    rw [hudef]
    trans 16 ^ ((2 * t - 1) + 1)
    · rw [pow_add, pow_one, mul_comm]
    · congr 1; omega
  have hex15 :
      hexEval (digits_8t7 t) * 15 =
        195 + 192 * (u - 1) + 7200 * u
          + 8192 * u * (16 ^ (2 * t - 1) - 1)
          + 529920 * u ^ 2
          + 458752 * u ^ 2 * (u - 1)
          + 30474240 * u ^ 3
          + 33554432 * u ^ 3 * (u - 1) := by
    rw [hex]
    have hA :
        (13 + 16 * (12 * G2) + 16 ^ (2 * t + 1) * 30
          + 16 ^ (2 * t + 3) * (2 * G1)
          + 16 ^ (4 * t + 2) * 138
          + 16 ^ (4 * t + 4) * (7 * G2)
          + 16 ^ (6 * t + 4) * 31
          + 16 ^ (6 * t + 6) * (2 * G2)) * 15
        =
        13 * 15 + 16 * 12 * (G2 * 15) + 16 ^ (2 * t + 1) * 30 * 15
          + 16 ^ (2 * t + 3) * 2 * (G1 * 15)
          + 16 ^ (4 * t + 2) * 138 * 15
          + 16 ^ (4 * t + 4) * 7 * (G2 * 15)
          + 16 ^ (6 * t + 4) * 31 * 15
          + 16 ^ (6 * t + 6) * 2 * (G2 * 15) := by
      ring
    rw [hA, hG1, hG2, hu21, hu23, hu42, hu44, hu64, hu66]
    ring
  have h8192 : 8192 * u * (16 ^ (2 * t - 1) - 1) = 512 * u ^ 2 - 8192 * u := by
    have : 8192 * u * (16 ^ (2 * t - 1) - 1) =
        8192 * u * 16 ^ (2 * t - 1) - 8192 * u := by
      rw [nat_mul_sub_left (8192 * u) _ _ h2t1, mul_one]
    rw [this]
    have : 8192 * u * 16 ^ (2 * t - 1) = 512 * u ^ 2 := by
      have : 8192 = 512 * 16 := by decide
      rw [this]
      calc
        512 * 16 * u * 16 ^ (2 * t - 1) = 512 * u * (16 * 16 ^ (2 * t - 1)) := by ring
        _ = 512 * u * u := by rw [h16u]
        _ = 512 * u ^ 2 := by ring
    rw [this]
  rw [hex15, h8192]
  have hR :
      (2 ^ (8 * t + 7) - 1) * (2 ^ (8 * t + 6) - 1) *
        (2 ^ (8 * t + 7) - 3) * (2 ^ (8 * t + 5) - 1) =
      (128 * u - 1) * (64 * u - 1) * (128 * u - 3) * (32 * u - 1) := by
    rw [h8t7, h8t6, h8t5]
  rw [hR]
  have hu1 : 1 ≤ u := hu_pos
  have hu16 : 16 ≤ u := by
    rw [hudef]
    have : 16 ^ 1 ≤ 16 ^ (2 * t) :=
      Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ 2 * t)
    simpa using this
  have h512u : 8192 * u ≤ 512 * u ^ 2 := by
    have : 512 * u ^ 2 = 512 * u * u := by ring
    rw [this]
    have : 8192 * u = 512 * 16 * u := by
      have : 8192 = 512 * 16 := by decide
      rw [this]
    rw [this]
    have := Nat.mul_le_mul_left (512 * u) hu16
    convert this using 1 <;> ring
  have h128u : 1 ≤ 128 * u := one_le_mul (by decide : 1 ≤ 128) hu1
  have h64u : 1 ≤ 64 * u := one_le_mul (by decide : 1 ≤ 64) hu1
  have h128u3 : 3 ≤ 128 * u :=
    (by decide : 3 ≤ 128).trans (Nat.le_mul_of_pos_right 128 hu1)
  have h32u : 1 ≤ 32 * u := one_le_mul (by decide : 1 ≤ 32) hu1
  apply Int.ofNat_inj.mp
  have hz :
      ((195 + 192 * (u - 1) + 7200 * u + (512 * u ^ 2 - 8192 * u)
        + 529920 * u ^ 2 + 458752 * u ^ 2 * (u - 1)
        + 30474240 * u ^ 3 + 33554432 * u ^ 3 * (u - 1) : ℕ) : ℤ)
      =
      (195 : ℤ) + 192 * (u - 1) + 7200 * u + (512 * u ^ 2 - 8192 * u)
        + 529920 * u ^ 2 + 458752 * u ^ 2 * (u - 1)
        + 30474240 * u ^ 3 + 33554432 * u ^ 3 * (u - 1) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rw [Int.natCast_sub hu1, Int.natCast_sub h512u]
    simp only [Int.natCast_mul, Int.natCast_pow]
    ring
  have hRint :
      (((128 * u - 1) * (64 * u - 1) * (128 * u - 3) * (32 * u - 1) : ℕ) : ℤ)
      =
      (128 * (u : ℤ) - 1) * (64 * u - 1) * (128 * u - 3) * (32 * u - 1) := by
    simp only [Int.natCast_mul]
    rw [Int.natCast_sub h128u, Int.natCast_sub h64u, Int.natCast_sub h128u3,
      Int.natCast_sub h32u]
    simp only [Int.natCast_mul]
    norm_cast
  rw [hz, hRint, poly_id_7]

lemma popc_choose_two_pow_five_of_mod_eight_eq_seven {m : ℕ}
    (hm : 15 ≤ m) (hmod : m % 8 = 7) :
    popc (Nat.choose (2 ^ m) 5) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 8 * t + 7 := ⟨m / 8, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hm5 : 5 ≤ m := by omega
  rw [choose_two_pow_five m hm5, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) / 15 =
        hexEval (digits_8t7 t) := by
    rw [ht]
    have : (8 * t + 7) - 1 = 8 * t + 6 := by omega
    rw [this]
    have : (8 * t + 7) - 2 = 8 * t + 5 := by omega
    rw [this]
    have := hexEval_digits_8t7_mul_fifteen t ht1
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 15) this.symm
  rw [hex, popc_hexEval_digits_8t7 t ht1]
  omega

lemma a_ne_zero_two_pow_mod8_eq_seven {m : ℕ} (hm : 15 ≤ m) (hmod : m % 8 = 7) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 5 (by decide) ?_
    (popc_choose_two_pow_five_of_mod_eight_eq_seven hm hmod)
  have : 5 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 5 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  exact this


/- Hex infrastructure for C(2^{24t+1}, 6) -/

lemma sum_geom_shift (q n : ℕ) :
    1 + q * ∑ i ∈ Finset.range n, q ^ i = ∑ i ∈ Finset.range (n + 1), q ^ i := by
  rw [Finset.sum_range_succ', pow_zero]
  have : ∑ k ∈ Finset.range n, q ^ (k + 1) = q * ∑ i ∈ Finset.range n, q ^ i := by
    simp only [pow_succ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [this]
  ring

lemma hexEval_flatten_replicate (block : List ℕ) (n : ℕ) :
    hexEval (List.flatten (List.replicate n block)) =
      hexEval block * ∑ i ∈ Finset.range n, 16 ^ (block.length * i) := by
  induction n with
  | zero => simp [hexEval]
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, hexEval_append, ih]
    set q := 16 ^ block.length with hqdef
    have hqi : ∀ i, 16 ^ (block.length * i) = q ^ i := by
      intro i; rw [hqdef, ← pow_mul]
    simp only [hqi]
    calc
      hexEval block + 16 ^ block.length *
          (hexEval block * ∑ i ∈ Finset.range n, q ^ i)
          = hexEval block * (1 + q * ∑ i ∈ Finset.range n, q ^ i) := by
            rw [← hqdef]; ring
      _ = hexEval block * ∑ i ∈ Finset.range (n + 1), q ^ i := by
            rw [sum_geom_shift]

lemma hexEval_triple (d e f : ℕ) : hexEval [d, e, f] = d + 16 * e + 256 * f := by
  simp [hexEval]
  ring

lemma length_flatten_replicate (block : List ℕ) (n : ℕ) :
    (List.flatten (List.replicate n block)).length = n * block.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
    ring

lemma geom_sum_4096 (n : ℕ) :
    (∑ i ∈ Finset.range n, 4096 ^ i) * 4095 = 4096 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    have hle : 1 ≤ 4096 ^ n := Nat.one_le_pow _ _ (by decide)
    have : 4096 ^ n - 1 + 4096 ^ n * 4095 = 4096 ^ n * 4096 - 1 := by omega
    exact this

/- Digit list for the odd part of `C(2^{24t+1}, 6)`, `t ≥ 1`. LSB first. -/

def digits_24t1 (t : ℕ) : List ℕ :=
  List.replicate (6 * t - 1) 5
    ++ [13, 11, 15]
    ++ List.flatten (List.replicate (2 * t - 1) [4, 10, 15])
    ++ [12, 7, 15]
    ++ List.flatten (List.replicate (2 * t - 1) [4, 10, 15])
    ++ [4, 3, 12]
    ++ List.flatten (List.replicate (2 * t - 1) [6, 1, 12])
    ++ [6, 11, 6]
    ++ List.flatten (List.replicate (2 * t - 1) [1, 12, 6])
    ++ [1]

lemma digits_24t1_lt (t : ℕ) : ∀ d ∈ digits_24t1 t, d < 16 := by
  intro d hd
  unfold digits_24t1 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten, List.mem_replicate] at hd
  aesop

lemma map_popc_flatten_replicate (block : List ℕ) (n : ℕ) :
    (List.map popc (List.flatten (List.replicate n block))).sum =
      n * (List.map popc block).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih]
    ring

lemma popc_digits_24t1 (t : ℕ) (ht : 1 ≤ t) :
    (List.map popc (digits_24t1 t)).sum = 60 * t + 6 := by
  have h5 : popc 5 = 2 := by decide
  have h13 : popc 13 = 3 := by decide
  have h11 : popc 11 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  have h4 : popc 4 = 1 := by decide
  have h10 : popc 10 = 2 := by decide
  have h12 : popc 12 = 2 := by decide
  have h7 : popc 7 = 3 := by decide
  have h3 : popc 3 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h1 : popc 1 = 1 := by decide
  unfold digits_24t1
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_replicate, map_popc_flatten_replicate]
  rw [h5, h13, h11, h15, h12, h7, h4, h10, h3, h6, h1]
  omega

lemma popc_hexEval_digits_24t1 (t : ℕ) (ht : 1 ≤ t) :
    popc (hexEval (digits_24t1 t)) = 60 * t + 6 := by
  rw [popc_hexEval _ (digits_24t1_lt t), popc_digits_24t1 t ht]

lemma hexEval_4af : hexEval [4, 10, 15] = 4004 := by decide
lemma hexEval_61c : hexEval [6, 1, 12] = 3094 := by decide
lemma hexEval_1c6 : hexEval [1, 12, 6] = 1729 := by decide
lemma hexEval_dbf : hexEval [13, 11, 15] = 4029 := by decide
lemma hexEval_c7f : hexEval [12, 7, 15] = 3964 := by decide
lemma hexEval_43c : hexEval [4, 3, 12] = 3124 := by decide
lemma hexEval_6b6 : hexEval [6, 11, 6] = 1718 := by decide

lemma hexEval_digits_24t1_eq (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t1 t) =
      5 * ∑ i ∈ Finset.range (6 * t - 1), 16 ^ i
        + 16 ^ (6 * t - 1) * 4029
        + 16 ^ (6 * t + 2) *
            (4004 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (12 * t - 1) * 3964
        + 16 ^ (12 * t + 2) *
            (4004 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (18 * t - 1) * 3124
        + 16 ^ (18 * t + 2) *
            (3094 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (24 * t - 1) * 1718
        + 16 ^ (24 * t + 2) *
            (1729 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (30 * t - 1) := by
  unfold digits_24t1
  repeat rw [hexEval_append]
  rw [hexEval_replicate]
  rw [hexEval_dbf, hexEval_c7f, hexEval_43c, hexEval_6b6, hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_4af, hexEval_61c, hexEval_1c6]
  simp only [List.length_cons, List.length_nil, List.length_append,
    List.length_replicate, length_flatten_replicate]
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  rw [f3]
  have e1 : 6 * t - 1 + 3 = 6 * t + 2 := by omega
  rw [e1]
  have e2 : 6 * t + 2 + (2 * t - 1) * 3 = 12 * t - 1 := by omega
  rw [e2]
  have e3 : 12 * t - 1 + 3 = 12 * t + 2 := by omega
  rw [e3]
  have e4 : 12 * t + 2 + (2 * t - 1) * 3 = 18 * t - 1 := by omega
  rw [e4]
  have e5 : 18 * t - 1 + 3 = 18 * t + 2 := by omega
  rw [e5]
  have e6 : 18 * t + 2 + (2 * t - 1) * 3 = 24 * t - 1 := by omega
  rw [e6]
  have e7 : 24 * t - 1 + 3 = 24 * t + 2 := by omega
  rw [e7]
  have e8 : 24 * t + 2 + (2 * t - 1) * 3 = 30 * t - 1 := by omega
  rw [e8]
  ring

lemma poly_id_24t1 (u : ℤ) :
    (2 * u - 1) * (u - 1) * (2 * u - 3) * (u - 2) * (2 * u - 5) =
      (8 : ℤ) * u ^ 5 - 60 * u ^ 4 + 170 * u ^ 3 - 225 * u ^ 2 + 137 * u - 30 := by
  ring

lemma sixteen_pow_mul (a b : ℕ) : 16 ^ a * 16 ^ b = 16 ^ (a + b) := (pow_add 16 a b).symm

lemma hexEval_digits_24t1_mul_ninety (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t1 t) * 90 =
      (2 * 16 ^ (6 * t) - 1) * (16 ^ (6 * t) - 1) *
        (2 * 16 ^ (6 * t) - 3) * (16 ^ (6 * t) - 2) *
        (2 * 16 ^ (6 * t) - 5) := by
  have hex := hexEval_digits_24t1_eq t ht
  set G := ∑ i ∈ Finset.range (6 * t - 1), 16 ^ i with hGdef
  set H := ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i) with hHdef
  set u := 16 ^ (6 * t) with hudef
  have hG : G * 15 = 16 ^ (6 * t - 1) - 1 := geom_sum_sixteen (6 * t - 1)
  have hHpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i
    rw [show (4096 : ℕ) = 16 ^ 3 from by decide, ← pow_mul]
  have hH : H * 4095 = 16 ^ (6 * t - 3) - 1 := by
    have : H = ∑ i ∈ Finset.range (2 * t - 1), 4096 ^ i := by
      simp only [hHdef, hHpow]
    rw [this, geom_sum_4096]
    congr 1
    rw [show (4096 : ℕ) = 16 ^ 3 from by decide, ← pow_mul]
    congr 1
    omega
  have h6t1 : 1 ≤ 16 ^ (6 * t - 1) := Nat.one_le_pow _ _ (by decide)
  have h6t3 : 1 ≤ 16 ^ (6 * t - 3) := Nat.one_le_pow _ _ (by decide)
  have hu1 : 1 ≤ u := by rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have hu2 : 2 ≤ u := by
    rw [hudef]
    have : 16 ^ 1 ≤ 16 ^ (6 * t) :=
      Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ 6 * t)
    calc 2 ≤ 16 := by decide
         _ = 16 ^ 1 := (pow_one 16).symm
         _ ≤ 16 ^ (6 * t) := this
  have hu3 : 3 ≤ 2 * u := by
    have := Nat.mul_le_mul_left 2 hu2
    omega
  have hu5 : 5 ≤ 2 * u := by
    have : 16 ≤ u := by
      rw [hudef]
      have : 16 ^ 1 ≤ 16 ^ (6 * t) :=
        Nat.pow_le_pow_right (by decide : 0 < 16) (by omega : 1 ≤ 6 * t)
      simpa using this
    omega
  -- Replace each H-term: c * H = (c / 4095) * (16^{6t-3} - 1) when 4095 ∣ c
  have hHmul (c d : ℕ) (hdvd : 4095 * d = c) :
      c * H = d * (16 ^ (6 * t - 3) - 1) := by
    have : c * H = d * (H * 4095) := by
      rw [← hdvd]; ring
    rw [this, hH]
  have hex90 :
      hexEval (digits_24t1 t) * 90 =
        30 * (16 ^ (6 * t - 1) - 1) + 362610 * 16 ^ (6 * t - 1)
          + (90 * 4004 * 16 ^ (6 * t + 2)) * H
          + 356760 * 16 ^ (12 * t - 1)
          + (90 * 4004 * 16 ^ (12 * t + 2)) * H
          + 281160 * 16 ^ (18 * t - 1)
          + (90 * 3094 * 16 ^ (18 * t + 2)) * H
          + 154620 * 16 ^ (24 * t - 1)
          + (90 * 1729 * 16 ^ (24 * t + 2)) * H
          + 90 * 16 ^ (30 * t - 1) := by
    rw [hex]
    have hdist :
        (5 * G + 16 ^ (6 * t - 1) * 4029
          + 16 ^ (6 * t + 2) * (4004 * H)
          + 16 ^ (12 * t - 1) * 3964
          + 16 ^ (12 * t + 2) * (4004 * H)
          + 16 ^ (18 * t - 1) * 3124
          + 16 ^ (18 * t + 2) * (3094 * H)
          + 16 ^ (24 * t - 1) * 1718
          + 16 ^ (24 * t + 2) * (1729 * H)
          + 16 ^ (30 * t - 1)) * 90
        =
          30 * (G * 15) + 362610 * 16 ^ (6 * t - 1)
            + 90 * 4004 * 16 ^ (6 * t + 2) * H
            + 356760 * 16 ^ (12 * t - 1)
            + 90 * 4004 * 16 ^ (12 * t + 2) * H
            + 281160 * 16 ^ (18 * t - 1)
            + 90 * 3094 * 16 ^ (18 * t + 2) * H
            + 154620 * 16 ^ (24 * t - 1)
            + 90 * 1729 * 16 ^ (24 * t + 2) * H
            + 90 * 16 ^ (30 * t - 1) := by
      ring
    rw [hdist, hG]
  -- Now lift to ℤ
  apply Int.ofNat_inj.mp
  have hzG :
      ((30 * (16 ^ (6 * t - 1) - 1) : ℕ) : ℤ) = 30 * (16 ^ (6 * t - 1) - 1) := by
    rw [Int.natCast_mul, Int.natCast_sub h6t1]
    norm_cast
  -- We will rewrite hex*90 in ℤ by replacing H terms after proving divisibility.
  -- First record the four H-coefficients' factorizations.
  have h16_5 : (16 : ℕ) ^ 5 = 1048576 := by decide
  have split62 : 16 ^ (6 * t + 2) = 16 ^ 5 * 16 ^ (6 * t - 3) := by
    have : 6 * t + 2 = 5 + (6 * t - 3) := by omega
    rw [this, pow_add]
  have split122 : 16 ^ (12 * t + 2) = 16 ^ 5 * 16 ^ (6 * t) * 16 ^ (6 * t - 3) := by
    have : 12 * t + 2 = 5 + 6 * t + (6 * t - 3) := by omega
    rw [this, pow_add, pow_add]
  have split182 : 16 ^ (18 * t + 2) = 16 ^ 5 * 16 ^ (12 * t) * 16 ^ (6 * t - 3) := by
    have : 18 * t + 2 = 5 + 12 * t + (6 * t - 3) := by omega
    rw [this, pow_add, pow_add]
  have split242 : 16 ^ (24 * t + 2) = 16 ^ 5 * 16 ^ (18 * t) * 16 ^ (6 * t - 3) := by
    have : 24 * t + 2 = 5 + 18 * t + (6 * t - 3) := by omega
    rw [this, pow_add, pow_add]
  have fact4004 : (90 * 4004 * 1048576 : ℕ) = 4095 * 92274688 := by decide
  have fact3094 : (90 * 3094 * 1048576 : ℕ) = 4095 * 71303168 := by decide
  have fact1729 : (90 * 1729 * 1048576 : ℕ) = 4095 * 39845888 := by decide
  have H1 :
      90 * 4004 * 16 ^ (6 * t + 2) * H =
        92274688 * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1) := by
    rw [split62, h16_5]
    have : 90 * 4004 * (1048576 * 16 ^ (6 * t - 3)) * H =
        (90 * 4004 * 1048576) * H * 16 ^ (6 * t - 3) := by ring
    rw [this, fact4004]
    have : 4095 * 92274688 * H * 16 ^ (6 * t - 3) =
        92274688 * (H * 4095) * 16 ^ (6 * t - 3) := by ring
    rw [this, hH]; ring
  have H2 :
      90 * 4004 * 16 ^ (12 * t + 2) * H =
        92274688 * 16 ^ (6 * t) * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1) := by
    rw [split122, h16_5]
    have : 90 * 4004 * (1048576 * 16 ^ (6 * t) * 16 ^ (6 * t - 3)) * H =
        (90 * 4004 * 1048576) * H * 16 ^ (6 * t) * 16 ^ (6 * t - 3) := by ring
    rw [this, fact4004]
    have : 4095 * 92274688 * H * 16 ^ (6 * t) * 16 ^ (6 * t - 3) =
        92274688 * (H * 4095) * 16 ^ (6 * t) * 16 ^ (6 * t - 3) := by ring
    rw [this, hH]; ring
  have H3 :
      90 * 3094 * 16 ^ (18 * t + 2) * H =
        71303168 * 16 ^ (12 * t) * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1) := by
    rw [split182, h16_5]
    have : 90 * 3094 * (1048576 * 16 ^ (12 * t) * 16 ^ (6 * t - 3)) * H =
        (90 * 3094 * 1048576) * H * 16 ^ (12 * t) * 16 ^ (6 * t - 3) := by ring
    rw [this, fact3094]
    have : 4095 * 71303168 * H * 16 ^ (12 * t) * 16 ^ (6 * t - 3) =
        71303168 * (H * 4095) * 16 ^ (12 * t) * 16 ^ (6 * t - 3) := by ring
    rw [this, hH]; ring
  have H4 :
      90 * 1729 * 16 ^ (24 * t + 2) * H =
        39845888 * 16 ^ (18 * t) * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1) := by
    rw [split242, h16_5]
    have : 90 * 1729 * (1048576 * 16 ^ (18 * t) * 16 ^ (6 * t - 3)) * H =
        (90 * 1729 * 1048576) * H * 16 ^ (18 * t) * 16 ^ (6 * t - 3) := by ring
    rw [this, fact1729]
    have : 4095 * 39845888 * H * 16 ^ (18 * t) * 16 ^ (6 * t - 3) =
        39845888 * (H * 4095) * 16 ^ (18 * t) * 16 ^ (6 * t - 3) := by ring
    rw [this, hH]; ring
  have hex90' :
      hexEval (digits_24t1 t) * 90 =
        30 * (16 ^ (6 * t - 1) - 1) + 362610 * 16 ^ (6 * t - 1)
          + 92274688 * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1)
          + 356760 * 16 ^ (12 * t - 1)
          + 92274688 * 16 ^ (6 * t) * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1)
          + 281160 * 16 ^ (18 * t - 1)
          + 71303168 * 16 ^ (12 * t) * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1)
          + 154620 * 16 ^ (24 * t - 1)
          + 39845888 * 16 ^ (18 * t) * 16 ^ (6 * t - 3) * (16 ^ (6 * t - 3) - 1)
          + 90 * 16 ^ (30 * t - 1) := by
    rw [hex90, H1, H2, H3, H4]
  set y := 16 ^ (6 * t - 3) with hydef
  have hy1 : 1 ≤ y := h6t3
  have p61y : 16 ^ (6 * t - 1) = 256 * y := by
    have : 6 * t - 1 = 2 + (6 * t - 3) := by omega
    rw [hydef, this, pow_add]
    have : (16 : ℕ) ^ 2 = 256 := by decide
    rw [this]
  have puy : u = 4096 * y := by
    rw [hudef, hydef]
    have : (4096 : ℕ) = 16 ^ 3 := by decide
    rw [this, sixteen_pow_mul]; congr 1; omega
  have p121 : 16 ^ (12 * t - 1) = 256 * y * u := by
    have : 12 * t - 1 = (6 * t - 1) + 6 * t := by omega
    rw [this, pow_add, p61y, hudef]
  have p181 : 16 ^ (18 * t - 1) = 256 * y * u * u := by
    rw [hudef]
    have : 18 * t - 1 = (6 * t - 1) + 6 * t + 6 * t := by omega
    rw [this, pow_add, pow_add, p61y]
  have p241 : 16 ^ (24 * t - 1) = 256 * y * u * u * u := by
    rw [hudef]
    have : 24 * t - 1 = (6 * t - 1) + 6 * t + 6 * t + 6 * t := by omega
    rw [this, pow_add, pow_add, pow_add, p61y]
  have p301 : 16 ^ (30 * t - 1) = 256 * y * u * u * u * u := by
    rw [hudef]
    have : 30 * t - 1 = (6 * t - 1) + 6 * t + 6 * t + 6 * t + 6 * t := by omega
    rw [this, pow_add, pow_add, pow_add, pow_add, p61y]
  have p12t : 16 ^ (12 * t) = u * u := by
    rw [hudef, sixteen_pow_mul]; congr 1; omega
  have p18t : 16 ^ (18 * t) = u * u * u := by
    rw [hudef]
    trans 16 ^ (6 * t + 6 * t + 6 * t)
    · congr 1; omega
    · rw [pow_add, pow_add]
  rw [hex90', p61y, p121, p181, p241, p301, p12t, p18t]
  -- hex*90 is now written with y, u and (y-1)
  have hz :
      ((30 * (256 * y - 1) + 362610 * (256 * y)
          + 92274688 * y * (y - 1)
          + 356760 * (256 * y * u)
          + 92274688 * u * y * (y - 1)
          + 281160 * (256 * y * u * u)
          + 71303168 * (u * u) * y * (y - 1)
          + 154620 * (256 * y * u * u * u)
          + 39845888 * (u * u * u) * y * (y - 1)
          + 90 * (256 * y * u * u * u * u) : ℕ) : ℤ)
      =
        (30 : ℤ) * (256 * y - 1) + 362610 * (256 * y)
          + 92274688 * y * (y - 1)
          + 356760 * (256 * y * u)
          + 92274688 * u * y * (y - 1)
          + 281160 * (256 * y * u * u)
          + 71303168 * (u * u) * y * (y - 1)
          + 154620 * (256 * y * u * u * u)
          + 39845888 * (u * u * u) * y * (y - 1)
          + 90 * (256 * y * u * u * u * u) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    have hy256 : 1 ≤ 256 * y := one_le_mul (by decide : 1 ≤ 256) hy1
    rw [Int.natCast_sub hy256, Int.natCast_sub hy1]
    simp only [Int.natCast_mul]
    ring
  have hRint :
      (((2 * u - 1) * (u - 1) * (2 * u - 3) * (u - 2) * (2 * u - 5) : ℕ) : ℤ)
      =
        (2 * (u : ℤ) - 1) * (u - 1) * (2 * u - 3) * (u - 2) * (2 * u - 5) := by
    simp only [Int.natCast_mul]
    rw [Int.natCast_sub (one_le_mul (by decide : 1 ≤ 2) hu1),
        Int.natCast_sub hu1, Int.natCast_sub hu3, Int.natCast_sub hu2,
        Int.natCast_sub hu5]
    simp only [Int.natCast_mul]
    norm_cast
  -- After p61y, the first term is 30*(256*y - 1) not 30*(16^{6t-1}-1)
  -- Need the Nat goal to match. hex90' after rewrites:
  -- 30 * (256*y - 1) + ...  but 30 * (16^{6t-1} - 1) became 30 * (256*y - 1) YES
  -- and 92274688 * 16^{6t-3} * (16^{6t-3}-1) = 92274688 * y * (y-1) YES
  rw [hz, hRint]
  -- Substitute u = 4096 * y in ℤ and apply poly_id
  have huy : (u : ℤ) = 4096 * y := by
    have := congrArg (fun n : ℕ => (n : ℤ)) puy
    simpa [Int.natCast_mul] using this
  rw [huy, poly_id_24t1]
  ring

lemma descFactorial_six (n : ℕ) :
    n.descFactorial 6 = (n - 5) * (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma choose_two_pow_six (m : ℕ) (hm : 6 ≤ m) :
    Nat.choose (2 ^ m) 6 =
      2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) / 45) := by
  have h6le : 6 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 6 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 6 =
      (2 ^ m - 5) * (2 ^ m - 4) * (2 ^ m - 3) * (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m :=
    descFactorial_six _
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hprod :
      (2 ^ m).descFactorial 6 =
        2 ^ (m + 3) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5)) := by
    rw [hdesc, h4, h2]
    ring_nf
  have hfac : (2 ^ m).descFactorial 6 = 720 * Nat.choose (2 ^ m) 6 := by
    have : 6 ! = 720 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h8 : 2 ^ (m + 3) = 16 * 2 ^ (m - 1) := by
    have hm1 : 1 ≤ m := by omega
    have : 2 ^ (m + 3) = 2 ^ (m - 1 + 4) := by
      congr 1; omega
    rw [this, pow_add, show (2 : ℕ) ^ 4 = 16 from rfl, mul_comm]
  rw [h8] at hfac
  have : 16 * (2 ^ (m - 1) *
      ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
        (2 ^ m - 5))) =
      16 * (45 * Nat.choose (2 ^ m) 6) := by
    have h720 : (720 : ℕ) = 16 * 45 := by decide
    rw [h720] at hfac
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 16) this
  have h45dvd : 45 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
      (2 ^ (m - 2) - 1) * (2 ^ m - 5) := by
    have : 45 ∣ 2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5)) :=
      ⟨Nat.choose (2 ^ m) 6, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 45 (2 ^ (m - 1)) := by
      have : Nat.Coprime 45 2 := by decide
      simpa using this.pow_right (m - 1)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 6 =
      (2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5))) / 45 := by
    have h := hcancel
    apply Nat.eq_div_of_mul_eq_left (by decide : (45 : ℕ) ≠ 0)
    convert h.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h45dvd]

lemma popc_choose_two_pow_six_of_mod_24_eq_one {m : ℕ}
    (hm : 25 ≤ m) (hmod : m % 24 = 1) :
    popc (Nat.choose (2 ^ m) 6) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 24 * t + 1 := ⟨m / 24, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hm6 : 6 ≤ m := by omega
  rw [choose_two_pow_six m hm6, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) / 45 =
        hexEval (digits_24t1 t) := by
    have hm' : m - 1 = 24 * t := by omega
    have hm'' : m - 2 = 24 * t - 1 := by omega
    have hmul := hexEval_digits_24t1_mul_ninety t ht1
    -- hex * 90 = (2u-1)(u-1)(2u-3)(u-2)(2u-5)
    -- product_five * 2 = (2u-1)(u-1)(2u-3)(u-2)(2u-5)
    -- so hex * 45 = product_five
    set u := 16 ^ (6 * t) with hudef
    have h2m : 2 ^ m = 2 * u := by
      rw [ht, hudef]
      have : 2 ^ (24 * t + 1) = 2 * 2 ^ (24 * t) := pow_succ' _ _
      have : 16 ^ (6 * t) = 2 ^ (24 * t) := by
        rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
      rw [‹2 ^ (24 * t + 1) = 2 * 2 ^ (24 * t)›, this]
    have h2m1 : 2 ^ (m - 1) = u := by
      rw [hm', hudef]
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m2 : 2 * 2 ^ (m - 2) = u := by
      have : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
        have : m - 1 = (m - 2) + 1 := by omega
        rw [this, pow_succ, mul_comm]
      rw [← this, h2m1]
    have h2sub : 2 * (2 ^ (m - 2) - 1) = u - 2 := by
      rw [Nat.mul_sub_left_distrib, mul_one, h2m2]
    have hprod2 :
        (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * 2 =
          (2 * u - 1) * (u - 1) * (2 * u - 3) * (u - 2) * (2 * u - 5) := by
      rw [h2m, h2m1]
      have :
          (2 * u - 1) * (u - 1) * (2 * u - 3) * (2 ^ (m - 2) - 1) * (2 * u - 5) * 2 =
            (2 * u - 1) * (u - 1) * (2 * u - 3) * (2 * (2 ^ (m - 2) - 1)) *
              (2 * u - 5) := by ring
      rw [this, h2sub]
    have hprod45 :
        (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) =
          hexEval (digits_24t1 t) * 45 := by
      have : (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * 2 =
          hexEval (digits_24t1 t) * 90 := by
        rw [hprod2, hmul]
      have h2c := congrArg (fun n => n / 2) this
      simp only at h2c
      have hL : ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
          (2 ^ (m - 2) - 1) * (2 ^ m - 5) * 2) / 2 =
          (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) := by
        rw [mul_comm _ 2]
        exact Nat.mul_div_cancel_left _ (by decide : 0 < 2)
      have hR : hexEval (digits_24t1 t) * 90 / 2 = hexEval (digits_24t1 t) * 45 := by
        have : (90 : ℕ) = 2 * 45 := by decide
        rw [this]
        have : hexEval (digits_24t1 t) * (2 * 45) = 2 * (hexEval (digits_24t1 t) * 45) := by
          ring
        rw [this, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      rw [hL, hR] at h2c
      exact h2c
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 45) hprod45
  rw [hex, popc_hexEval_digits_24t1 t ht1]
  omega

lemma a_ne_zero_two_pow_mod24_eq_one {m : ℕ} (hm : 25 ≤ m) (hmod : m % 24 = 1) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 6 (by decide) ?_
    (popc_choose_two_pow_six_of_mod_24_eq_one hm hmod)
  have : 6 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 6 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  exact this


/- Digit list for the odd part of `C(2^{24t+3}, 6)`, `t ≥ 1`. LSB first. -/

def digits_24t3 (t : ℕ) : List ℕ :=
  List.replicate (6 * t) 5
    ++ [15, 14, 3]
    ++ List.flatten (List.replicate (2 * t - 1) [9, 14, 3])
    ++ [1, 12, 3]
    ++ List.flatten (List.replicate (2 * t - 1) [9, 14, 3])
    ++ [9, 2, 6]
    ++ List.flatten (List.replicate (2 * t - 1) [0, 11, 5])
    ++ [0, 11, 15, 10, 5]
    ++ List.flatten (List.replicate (2 * t - 1) [0, 11, 5])

lemma digits_24t3_lt (t : ℕ) : ∀ d ∈ digits_24t3 t, d < 16 := by
  intro d hd
  unfold digits_24t3 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten, List.mem_replicate] at hd
  aesop

lemma popc_digits_24t3 (t : ℕ) (ht : 1 ≤ t) :
    (List.map popc (digits_24t3 t)).sum = 60 * t + 6 := by
  have h5 : popc 5 = 2 := by decide
  have h15 : popc 15 = 4 := by decide
  have h14 : popc 14 = 3 := by decide
  have h3 : popc 3 = 2 := by decide
  have h9 : popc 9 = 2 := by decide
  have h1 : popc 1 = 1 := by decide
  have h12 : popc 12 = 2 := by decide
  have h2 : popc 2 = 1 := by decide
  have h6 : popc 6 = 2 := by decide
  have h0 : popc 0 = 0 := by decide
  have h11 : popc 11 = 3 := by decide
  have h10 : popc 10 = 2 := by decide
  unfold digits_24t3
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_replicate, map_popc_flatten_replicate]
  rw [h5, h15, h14, h3, h9, h1, h12, h2, h6, h0, h11, h10]
  omega

lemma popc_hexEval_digits_24t3 (t : ℕ) (ht : 1 ≤ t) :
    popc (hexEval (digits_24t3 t)) = 60 * t + 6 := by
  rw [popc_hexEval _ (digits_24t3_lt t), popc_digits_24t3 t ht]

lemma hexEval_fe3 : hexEval [15, 14, 3] = 1007 := by decide
lemma hexEval_9e3 : hexEval [9, 14, 3] = 1001 := by decide
lemma hexEval_1c3 : hexEval [1, 12, 3] = 961 := by decide
lemma hexEval_926 : hexEval [9, 2, 6] = 1577 := by decide
lemma hexEval_0b5 : hexEval [0, 11, 5] = 1456 := by decide
lemma hexEval_0bfa5 : hexEval [0, 11, 15, 10, 5] = 372656 := by decide

lemma hexEval_digits_24t3_eq (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t3 t) =
      5 * ∑ i ∈ Finset.range (6 * t), 16 ^ i
        + 16 ^ (6 * t) * 1007
        + 16 ^ (6 * t + 3) *
            (1001 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (12 * t) * 961
        + 16 ^ (12 * t + 3) *
            (1001 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (18 * t) * 1577
        + 16 ^ (18 * t + 3) *
            (1456 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (24 * t) * 372656
        + 16 ^ (24 * t + 5) *
            (1456 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i)) := by
  unfold digits_24t3
  repeat rw [hexEval_append]
  rw [hexEval_replicate]
  rw [hexEval_fe3, hexEval_1c3, hexEval_926, hexEval_0bfa5]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_9e3, hexEval_0b5]
  simp only [List.length_cons, List.length_nil, List.length_append,
    List.length_replicate, length_flatten_replicate]
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f5 : (0 + 1 + 1 + 1 + 1 + 1 : ℕ) = 5 := rfl
  rw [f3, f5]
  have e1 : 6 * t + 3 + (2 * t - 1) * 3 = 12 * t := by omega
  rw [e1]
  have e2 : 12 * t + 3 + (2 * t - 1) * 3 = 18 * t := by omega
  rw [e2]
  have e3 : 18 * t + 3 + (2 * t - 1) * 3 = 24 * t := by omega
  rw [e3]

lemma poly_id_24t3 (y : ℤ) :
    (15 : ℤ) * (4096 * y - 1) + 45315 * (4096 * y) + 45056 * (4096 * y) * (y - 1)
      + 43245 * (4096 * y) ^ 2 + 45056 * (4096 * y) ^ 2 * (y - 1)
      + 70965 * (4096 * y) ^ 3 + 65536 * (4096 * y) ^ 3 * (y - 1)
      + 16769520 * (4096 * y) ^ 4 + 16777216 * (4096 * y) ^ 4 * (y - 1)
    =
      (8 * (4096 * y) - 1) * (4 * (4096 * y) - 1) * (8 * (4096 * y) - 3) *
        (2 * (4096 * y) - 1) * (8 * (4096 * y) - 5) := by
  ring

lemma hexEval_digits_24t3_mul_fortyfive (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t3 t) * 45 =
      (8 * 16 ^ (6 * t) - 1) * (4 * 16 ^ (6 * t) - 1) *
        (8 * 16 ^ (6 * t) - 3) * (2 * 16 ^ (6 * t) - 1) *
        (8 * 16 ^ (6 * t) - 5) := by
  have hex := hexEval_digits_24t3_eq t ht
  set G := ∑ i ∈ Finset.range (6 * t), 16 ^ i with hGdef
  set H := ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i) with hHdef
  set u := 16 ^ (6 * t) with hudef
  set y := 16 ^ (6 * t - 3) with hydef
  have hG : G * 15 = u - 1 := by
    rw [hGdef, hudef]; exact geom_sum_sixteen (6 * t)
  have hHpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hH : H * 4095 = y - 1 := by
    rw [hHdef, hydef]
    have : ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (2 * t - 1), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (6 * t - 3) = 4096 ^ (2 * t - 1) := by
      have : 6 * t - 3 = 3 * (2 * t - 1) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    rw [this]
    exact geom_sum_4096 (2 * t - 1)
  have hy1 : 1 ≤ y := by
    rw [hydef]; exact Nat.one_le_pow _ _ (by decide)
  have hu1 : 1 ≤ u := by
    rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have p63 : 16 ^ (6 * t + 3) = 4096 * u := by
    rw [hudef, pow_add]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this]; ring
  have p123 : 16 ^ (12 * t + 3) = 4096 * u * u := by
    have : 12 * t + 3 = 6 * t + 6 * t + 3 := by omega
    rw [this, pow_add, pow_add, hudef]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this]; ring
  have p183 : 16 ^ (18 * t + 3) = 4096 * u * u * u := by
    have : 18 * t + 3 = 6 * t + 6 * t + 6 * t + 3 := by omega
    rw [this, pow_add, pow_add, pow_add, hudef]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this]; ring
  have p245 : 16 ^ (24 * t + 5) = 1048576 * u * u * u * u := by
    have : 24 * t + 5 = 6 * t + 6 * t + 6 * t + 6 * t + 5 := by omega
    rw [this, pow_add, pow_add, pow_add, pow_add, hudef]
    have : (16 : ℕ) ^ 5 = 1048576 := by decide
    rw [this]; ring
  have p12t : 16 ^ (12 * t) = u * u := by
    rw [hudef, sixteen_pow_mul]; congr 1; omega
  have p18t : 16 ^ (18 * t) = u * u * u := by
    rw [hudef]
    trans 16 ^ (6 * t + 6 * t + 6 * t)
    · congr 1; omega
    · rw [pow_add, pow_add]
  have p24t : 16 ^ (24 * t) = u * u * u * u := by
    rw [hudef]
    trans 16 ^ (6 * t + 6 * t + 6 * t + 6 * t)
    · congr 1; omega
    · rw [pow_add, pow_add, pow_add]
  have puy : u = 4096 * y := by
    rw [hudef, hydef]
    have : (4096 : ℕ) = 16 ^ 3 := by decide
    rw [this, sixteen_pow_mul]; congr 1; omega
  have factH1 : (45 * 1001 * 4096 : ℕ) = 4095 * 45056 := by decide
  have factH3 : (45 * 1456 * 4096 : ℕ) = 4095 * 65536 := by decide
  have factH4 : (45 * 1456 * 1048576 : ℕ) = 4095 * 16777216 := by decide
  have hex45 :
      hexEval (digits_24t3 t) * 45 =
        15 * (u - 1) + 45315 * u + 45056 * u * (y - 1)
          + 43245 * (u * u) + 45056 * (u * u) * (y - 1)
          + 70965 * (u * u * u) + 65536 * (u * u * u) * (y - 1)
          + 16769520 * (u * u * u * u) + 16777216 * (u * u * u * u) * (y - 1) := by
    rw [hex, p63, p123, p183, p245, p12t, p18t, p24t]
    have hdist :
        (5 * G + u * 1007 + (4096 * u) * (1001 * H)
          + (u * u) * 961 + (4096 * u * u) * (1001 * H)
          + (u * u * u) * 1577 + (4096 * u * u * u) * (1456 * H)
          + (u * u * u * u) * 372656 + (1048576 * u * u * u * u) * (1456 * H)) * 45
        =
          225 * G + 45315 * u + 45 * 1001 * 4096 * H * u
            + 43245 * (u * u) + 45 * 1001 * 4096 * H * (u * u)
            + 70965 * (u * u * u) + 45 * 1456 * 4096 * H * (u * u * u)
            + 16769520 * (u * u * u * u)
            + 45 * 1456 * 1048576 * H * (u * u * u * u) := by
      ring
    rw [hdist]
    have h225 : 225 * G = 15 * (u - 1) := by
      have : (225 : ℕ) = 15 * 15 := by decide
      rw [this, mul_assoc, mul_comm 15 G, hG]
    rw [h225]
    have H1 :
        45 * 1001 * 4096 * H * u = 45056 * u * (y - 1) := by
      rw [factH1]
      have : 4095 * 45056 * H * u = 45056 * u * (H * 4095) := by ring
      rw [this, hH]
    have H2 :
        45 * 1001 * 4096 * H * (u * u) = 45056 * (u * u) * (y - 1) := by
      rw [factH1]
      have : 4095 * 45056 * H * (u * u) = 45056 * (u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H3 :
        45 * 1456 * 4096 * H * (u * u * u) = 65536 * (u * u * u) * (y - 1) := by
      rw [factH3]
      have : 4095 * 65536 * H * (u * u * u) = 65536 * (u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H4 :
        45 * 1456 * 1048576 * H * (u * u * u * u) =
          16777216 * (u * u * u * u) * (y - 1) := by
      rw [factH4]
      have : 4095 * 16777216 * H * (u * u * u * u) =
          16777216 * (u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    rw [H1, H2, H3, H4]
  -- rewrite u^n
  have hex45' :
      hexEval (digits_24t3 t) * 45 =
        15 * (u - 1) + 45315 * u + 45056 * u * (y - 1)
          + 43245 * u ^ 2 + 45056 * u ^ 2 * (y - 1)
          + 70965 * u ^ 3 + 65536 * u ^ 3 * (y - 1)
          + 16769520 * u ^ 4 + 16777216 * u ^ 4 * (y - 1) := by
    rw [hex45]
    ring
  rw [hex45']
  have hR :
      (8 * 16 ^ (6 * t) - 1) * (4 * 16 ^ (6 * t) - 1) *
        (8 * 16 ^ (6 * t) - 3) * (2 * 16 ^ (6 * t) - 1) *
        (8 * 16 ^ (6 * t) - 5) =
      (8 * u - 1) * (4 * u - 1) * (8 * u - 3) * (2 * u - 1) * (8 * u - 5) := by
    rw [hudef]
  rw [hR]
  -- lift to ℤ
  have hy1' : 1 ≤ y := hy1
  have hu1' : 1 ≤ u := hu1
  have h8u : 1 ≤ 8 * u := one_le_mul (by decide : 1 ≤ 8) hu1
  have h4u : 1 ≤ 4 * u := one_le_mul (by decide : 1 ≤ 4) hu1
  have h8u3 : 3 ≤ 8 * u :=
    (by decide : 3 ≤ 8).trans (Nat.le_mul_of_pos_right 8 hu1)
  have h2u : 1 ≤ 2 * u := one_le_mul (by decide : 1 ≤ 2) hu1
  have h8u5 : 5 ≤ 8 * u :=
    (by decide : 5 ≤ 8).trans (Nat.le_mul_of_pos_right 8 hu1)
  apply Int.ofNat_inj.mp
  have hz :
      ((15 * (u - 1) + 45315 * u + 45056 * u * (y - 1)
          + 43245 * u ^ 2 + 45056 * u ^ 2 * (y - 1)
          + 70965 * u ^ 3 + 65536 * u ^ 3 * (y - 1)
          + 16769520 * u ^ 4 + 16777216 * u ^ 4 * (y - 1) : ℕ) : ℤ)
      =
        (15 : ℤ) * (u - 1) + 45315 * u + 45056 * u * (y - 1)
          + 43245 * u ^ 2 + 45056 * u ^ 2 * (y - 1)
          + 70965 * u ^ 3 + 65536 * u ^ 3 * (y - 1)
          + 16769520 * u ^ 4 + 16777216 * u ^ 4 * (y - 1) := by
    rw [Int.natCast_add, Int.natCast_add, Int.natCast_add, Int.natCast_add,
      Int.natCast_add, Int.natCast_add, Int.natCast_add, Int.natCast_add]
    rw [Int.natCast_mul, Int.natCast_sub hu1']
    rw [Int.natCast_mul]
    rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_sub hy1']
    simp only [Int.natCast_mul, Int.natCast_pow, Int.natCast_sub hy1',
      Int.natCast_sub hu1']
    ring
  have hRint :
      (((8 * u - 1) * (4 * u - 1) * (8 * u - 3) * (2 * u - 1) * (8 * u - 5) : ℕ) : ℤ)
      =
        (8 * (u : ℤ) - 1) * (4 * u - 1) * (8 * u - 3) * (2 * u - 1) * (8 * u - 5) := by
    simp only [Int.natCast_mul]
    rw [Int.natCast_sub h8u, Int.natCast_sub h4u, Int.natCast_sub h8u3,
      Int.natCast_sub h2u, Int.natCast_sub h8u5]
    simp only [Int.natCast_mul]
    norm_cast
  rw [hz, hRint]
  -- substitute u = 4096 * y in ℤ
  have huy : (u : ℤ) = 4096 * y := by
    rw [puy]
    simp only [Int.natCast_mul]
    norm_cast
  simp only [huy]
  simpa using poly_id_24t3 (y : ℤ)


lemma popc_choose_two_pow_six_of_mod_24_eq_three {m : ℕ}
    (hm : 27 ≤ m) (hmod : m % 24 = 3) :
    popc (Nat.choose (2 ^ m) 6) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 24 * t + 3 := ⟨m / 24, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hm6 : 6 ≤ m := by omega
  rw [choose_two_pow_six m hm6, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) / 45 =
        hexEval (digits_24t3 t) := by
    have hmul := hexEval_digits_24t3_mul_fortyfive t ht1
    set u := 16 ^ (6 * t) with hudef
    have h16 : 16 ^ (6 * t) = 2 ^ (24 * t) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 8 * u := by
      rw [ht, hudef, pow_add, h16, show (2 : ℕ) ^ 3 = 8 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 4 * u := by
      have : m - 1 = 24 * t + 2 := by omega
      rw [this, hudef, pow_add, h16, show (2 : ℕ) ^ 2 = 4 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 2 * u := by
      have : m - 2 = 24 * t + 1 := by omega
      rw [this, hudef, pow_add, h16, pow_one]
      ring
    rw [h2m, h2m1, h2m2]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 45) hmul.symm
  rw [hex, popc_hexEval_digits_24t3 t ht1]
  omega


lemma a_ne_zero_two_pow_mod24_eq_three {m : ℕ} (hm : 27 ≤ m) (hmod : m % 24 = 3) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 6 (by decide) ?_
    (popc_choose_two_pow_six_of_mod_24_eq_three hm hmod)
  have : 6 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 6 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  exact this

/- Digit list for the odd part of `C(2^{24t+19}, 6)`, `t ≥ 0`. LSB first. -/

def digits_24t19 (t : ℕ) : List ℕ :=
  List.replicate (6 * t + 4) 5
    ++ [15]
    ++ List.flatten (List.replicate (2 * t + 1) [14, 3, 9])
    ++ [6, 1]
    ++ List.flatten (List.replicate (2 * t + 1) [9, 14, 3])
    ++ [13]
    ++ List.flatten (List.replicate (2 * t + 1) [0, 11, 5])
    ++ [0]
    ++ List.flatten (List.replicate (2 * t + 1) [5, 0, 11])
    ++ [5]

lemma digits_24t19_lt (t : ℕ) : ∀ d ∈ digits_24t19 t, d < 16 := by
  intro d hd
  unfold digits_24t19 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten, List.mem_replicate] at hd
  aesop

lemma popc_digits_24t19 (t : ℕ) :
    (List.map popc (digits_24t19 t)).sum = 60 * t + 44 := by
  have h5 : popc 5 = 2 := by decide
  have h15 : popc 15 = 4 := by decide
  have h14 : popc 14 = 3 := by decide
  have h3 : popc 3 = 2 := by decide
  have h9 : popc 9 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h1 : popc 1 = 1 := by decide
  have h13 : popc 13 = 3 := by decide
  have h0 : popc 0 = 0 := by decide
  have h11 : popc 11 = 3 := by decide
  unfold digits_24t19
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_replicate, map_popc_flatten_replicate]
  rw [h5, h15, h14, h3, h9, h6, h1, h13, h0, h11]
  omega

lemma popc_hexEval_digits_24t19 (t : ℕ) :
    popc (hexEval (digits_24t19 t)) = 60 * t + 44 := by
  rw [popc_hexEval _ (digits_24t19_lt t), popc_digits_24t19 t]

lemma hexEval_e39 : hexEval [14, 3, 9] = 2366 := by decide
lemma hexEval_50b : hexEval [5, 0, 11] = 2821 := by decide

lemma hexEval_digits_24t19_eq (t : ℕ) :
    hexEval (digits_24t19 t) =
      5 * ∑ i ∈ Finset.range (6 * t + 4), 16 ^ i
        + 16 ^ (6 * t + 4) * 15
        + 16 ^ (6 * t + 5) *
            (2366 * ∑ i ∈ Finset.range (2 * t + 1), 16 ^ (3 * i))
        + 16 ^ (12 * t + 8) * 22
        + 16 ^ (12 * t + 10) *
            (1001 * ∑ i ∈ Finset.range (2 * t + 1), 16 ^ (3 * i))
        + 16 ^ (18 * t + 13) * 13
        + 16 ^ (18 * t + 14) *
            (1456 * ∑ i ∈ Finset.range (2 * t + 1), 16 ^ (3 * i))
        + 16 ^ (24 * t + 18) *
            (2821 * ∑ i ∈ Finset.range (2 * t + 1), 16 ^ (3 * i))
        + 16 ^ (30 * t + 21) * 5 := by
  unfold digits_24t19
  repeat rw [hexEval_append]
  rw [hexEval_replicate]
  rw [hexEval_singleton, hexEval_pair, hexEval_singleton, hexEval_singleton,
    hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_e39, hexEval_9e3, hexEval_0b5, hexEval_50b]
  simp only [List.length_cons, List.length_nil, List.length_append,
    List.length_replicate, length_flatten_replicate]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f2 : (0 + 1 + 1 : ℕ) = 2 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  rw [f1, f2, f3]
  have e1 : 6 * t + 4 + 1 = 6 * t + 5 := by omega
  rw [e1]
  have e2 : 6 * t + 5 + (2 * t + 1) * 3 = 12 * t + 8 := by omega
  rw [e2]
  have e3 : 12 * t + 8 + 2 = 12 * t + 10 := by omega
  rw [e3]
  have e4 : 12 * t + 10 + (2 * t + 1) * 3 = 18 * t + 13 := by omega
  rw [e4]
  have e5 : 18 * t + 13 + 1 = 18 * t + 14 := by omega
  rw [e5]
  have e6 : 18 * t + 14 + (2 * t + 1) * 3 = 24 * t + 17 := by omega
  rw [e6]
  have e7 : 24 * t + 17 + 1 = 24 * t + 18 := by omega
  rw [e7]
  have e8 : 24 * t + 18 + (2 * t + 1) * 3 = 30 * t + 21 := by omega
  rw [e8]
  simp [hexEval_singleton]

lemma poly_id_24t19 (u : ℤ) :
    (15 : ℤ) * (2 ^ 16 * u - 1) + 45 * 15 * 2 ^ 16 * u
      + 26 * 2 ^ 20 * u * (2 ^ 12 * u - 1)
      + 45 * 22 * 2 ^ 32 * u ^ 2
      + 11 * 2 ^ 40 * u ^ 2 * (2 ^ 12 * u - 1)
      + 45 * 13 * 2 ^ 52 * u ^ 3
      + 2 ^ 4 * 2 ^ 56 * u ^ 3 * (2 ^ 12 * u - 1)
      + 31 * 2 ^ 72 * u ^ 4 * (2 ^ 12 * u - 1)
      + 45 * 5 * 2 ^ 84 * u ^ 5
    =
      (2 ^ 19 * u - 1) * (2 ^ 18 * u - 1) * (2 ^ 19 * u - 3) *
        (2 ^ 17 * u - 1) * (2 ^ 19 * u - 5) := by
  ring

lemma sixteen_pow_as_two (k : ℕ) : ((16 ^ k : ℕ) : ℤ) = 2 ^ (4 * k) := by
  rw [Int.natCast_pow]
  have : ((16 : ℕ) : ℤ) = 2 ^ 4 := by norm_num
  rw [this, ← pow_mul]

lemma dist_24t19 (G H u p4 p5 p8 p10 p13 p14 p18 p21 : ℕ) :
    (5 * G + p4 * u * 15 + p5 * u * (2366 * H) + p8 * (u * u) * 22
      + p10 * (u * u) * (1001 * H) + p13 * (u * u * u) * 13
      + p14 * (u * u * u) * (1456 * H) + p18 * (u * u * u * u) * (2821 * H)
      + p21 * (u * u * u * u * u) * 5) * 45
    =
      225 * G + 45 * 15 * p4 * u + 45 * 2366 * p5 * u * H
        + 45 * 22 * p8 * (u * u) + 45 * 1001 * p10 * (u * u) * H
        + 45 * 13 * p13 * (u * u * u) + 45 * 1456 * p14 * (u * u * u) * H
        + 45 * 2821 * p18 * (u * u * u * u) * H
        + 45 * 5 * p21 * (u * u * u * u * u) := by
  ring

lemma hexEval_digits_24t19_mul_fortyfive (t : ℕ) :
    hexEval (digits_24t19 t) * 45 =
      (2 ^ 19 * 16 ^ (6 * t) - 1) * (2 ^ 18 * 16 ^ (6 * t) - 1) *
        (2 ^ 19 * 16 ^ (6 * t) - 3) * (2 ^ 17 * 16 ^ (6 * t) - 1) *
        (2 ^ 19 * 16 ^ (6 * t) - 5) := by
  have hex := hexEval_digits_24t19_eq t
  set G := ∑ i ∈ Finset.range (6 * t + 4), 16 ^ i with hGdef
  set H := ∑ i ∈ Finset.range (2 * t + 1), 16 ^ (3 * i) with hHdef
  set u := 16 ^ (6 * t) with hudef
  set p3 := 16 ^ 3 with hp3
  set p4 := 16 ^ 4 with hp4
  set p5 := 16 ^ 5 with hp5
  set p8 := 16 ^ 8 with hp8
  set p10 := 16 ^ 10 with hp10
  set p13 := 16 ^ 13 with hp13
  set p14 := 16 ^ 14 with hp14
  set p18 := 16 ^ 18 with hp18
  set p21 := 16 ^ 21 with hp21
  have hG : G * 15 = p4 * u - 1 := by
    rw [hGdef, hp4, hudef, ← pow_add]
    have : 4 + 6 * t = 6 * t + 4 := by omega
    rw [this]
    exact geom_sum_sixteen (6 * t + 4)
  have hHpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hH : H * 4095 = p3 * u - 1 := by
    rw [hHdef, hp3, hudef]
    have : ∑ i ∈ Finset.range (2 * t + 1), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (2 * t + 1), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ 3 * 16 ^ (6 * t) = 4096 ^ (2 * t + 1) := by
      have : (4096 : ℕ) = 16 ^ 3 := by decide
      rw [this, ← pow_add]
      have : 3 + 6 * t = 3 * (2 * t + 1) := by omega
      rw [this, ← pow_mul]
    rw [this]
    exact geom_sum_4096 (2 * t + 1)
  have hu1 : 1 ≤ u := by
    rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have hp3u1 : 1 ≤ p3 * u := one_le_mul (by
    rw [hp3]; exact Nat.one_le_pow _ _ (by decide)) hu1
  have hp4u1 : 1 ≤ p4 * u := one_le_mul (by
    rw [hp4]; exact Nat.one_le_pow _ _ (by decide)) hu1
  have pow_add_mul (a b : ℕ) : 16 ^ (a + b) = 16 ^ a * 16 ^ b := pow_add 16 a b
  have p64 : 16 ^ (6 * t + 4) = p4 * u := by
    rw [hp4, hudef, add_comm, pow_add_mul]
  have p65 : 16 ^ (6 * t + 5) = p5 * u := by
    rw [hp5, hudef, add_comm, pow_add_mul]
  have p128 : 16 ^ (12 * t + 8) = p8 * (u * u) := by
    have : 12 * t + 8 = 8 + (6 * t + 6 * t) := by omega
    rw [this, pow_add, hp8, hudef, pow_add]
  have p1210 : 16 ^ (12 * t + 10) = p10 * (u * u) := by
    have : 12 * t + 10 = 10 + (6 * t + 6 * t) := by omega
    rw [this, pow_add, hp10, hudef, pow_add]
  have p1813 : 16 ^ (18 * t + 13) = p13 * (u * u * u) := by
    have : 18 * t + 13 = 13 + (6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp13, hudef, pow_add, pow_add]
  have p1814 : 16 ^ (18 * t + 14) = p14 * (u * u * u) := by
    have : 18 * t + 14 = 14 + (6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp14, hudef, pow_add, pow_add]
  have p2418 : 16 ^ (24 * t + 18) = p18 * (u * u * u * u) := by
    have : 24 * t + 18 = 18 + (6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp18, hudef, pow_add, pow_add, pow_add]
  have p3021 : 16 ^ (30 * t + 21) = p21 * (u * u * u * u * u) := by
    have : 30 * t + 21 = 21 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp21, hudef, pow_add, pow_add, pow_add, pow_add]
  have factH1 : (45 * 2366 : ℕ) = 4095 * 26 := by decide
  have factH2 : (45 * 1001 : ℕ) = 4095 * 11 := by decide
  have factH3 : (45 * 1456 : ℕ) = 4095 * 16 := by decide
  have factH4 : (45 * 2821 : ℕ) = 4095 * 31 := by decide
  have hex45 :
      hexEval (digits_24t19 t) * 45 =
        15 * (p4 * u - 1) + 45 * 15 * p4 * u
          + 26 * p5 * u * (p3 * u - 1)
          + 45 * 22 * p8 * (u * u)
          + 11 * p10 * (u * u) * (p3 * u - 1)
          + 45 * 13 * p13 * (u * u * u)
          + 16 * p14 * (u * u * u) * (p3 * u - 1)
          + 31 * p18 * (u * u * u * u) * (p3 * u - 1)
          + 45 * 5 * p21 * (u * u * u * u * u) := by
    rw [hex, p64, p65, p128, p1210, p1813, p1814, p2418, p3021]
    rw [dist_24t19 G H u p4 p5 p8 p10 p13 p14 p18 p21]
    have h225 : 225 * G = 15 * (p4 * u - 1) := by
      have : (225 : ℕ) = 15 * 15 := by decide
      rw [this, mul_assoc, mul_comm 15 G, hG]
    rw [h225]
    have H1 :
        45 * 2366 * p5 * u * H = 26 * p5 * u * (p3 * u - 1) := by
      rw [factH1]
      have : 4095 * 26 * p5 * u * H = 26 * p5 * u * (H * 4095) := by ring
      rw [this, hH]
    have H2 :
        45 * 1001 * p10 * (u * u) * H = 11 * p10 * (u * u) * (p3 * u - 1) := by
      rw [factH2]
      have : 4095 * 11 * p10 * (u * u) * H = 11 * p10 * (u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H3 :
        45 * 1456 * p14 * (u * u * u) * H = 16 * p14 * (u * u * u) * (p3 * u - 1) := by
      rw [factH3]
      have : 4095 * 16 * p14 * (u * u * u) * H =
          16 * p14 * (u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H4 :
        45 * 2821 * p18 * (u * u * u * u) * H =
          31 * p18 * (u * u * u * u) * (p3 * u - 1) := by
      rw [factH4]
      have : 4095 * 31 * p18 * (u * u * u * u) * H =
          31 * p18 * (u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    rw [H1, H2, H3, H4]
  have hex45' :
      hexEval (digits_24t19 t) * 45 =
        15 * (p4 * u - 1) + 45 * 15 * p4 * u
          + 26 * p5 * u * (p3 * u - 1)
          + 45 * 22 * p8 * u ^ 2
          + 11 * p10 * u ^ 2 * (p3 * u - 1)
          + 45 * 13 * p13 * u ^ 3
          + 16 * p14 * u ^ 3 * (p3 * u - 1)
          + 31 * p18 * u ^ 4 * (p3 * u - 1)
          + 45 * 5 * p21 * u ^ 5 := by
    rw [hex45]
    ring
  rw [hex45']
  have hR :
      (2 ^ 19 * 16 ^ (6 * t) - 1) * (2 ^ 18 * 16 ^ (6 * t) - 1) *
        (2 ^ 19 * 16 ^ (6 * t) - 3) * (2 ^ 17 * 16 ^ (6 * t) - 1) *
        (2 ^ 19 * 16 ^ (6 * t) - 5) =
      (2 ^ 19 * u - 1) * (2 ^ 18 * u - 1) * (2 ^ 19 * u - 3) *
        (2 ^ 17 * u - 1) * (2 ^ 19 * u - 5) := by
    rw [hudef]
  rw [hR]
  have h219 : 1 ≤ 2 ^ 19 * u := one_le_mul (Nat.one_le_pow _ _ (by decide)) hu1
  have h218 : 1 ≤ 2 ^ 18 * u := one_le_mul (Nat.one_le_pow _ _ (by decide)) hu1
  have h217 : 1 ≤ 2 ^ 17 * u := one_le_mul (Nat.one_le_pow _ _ (by decide)) hu1
  have h219_3 : 3 ≤ 2 ^ 19 * u :=
    (by decide : 3 ≤ 2 ^ 19).trans (Nat.le_mul_of_pos_right (2 ^ 19) hu1)
  have h219_5 : 5 ≤ 2 ^ 19 * u :=
    (by decide : 5 ≤ 2 ^ 19).trans (Nat.le_mul_of_pos_right (2 ^ 19) hu1)
  zify [hp4u1, hp3u1, h219, h218, h217, h219_3, h219_5]
  have hp3z : ((p3 : ℕ) : ℤ) = 2 ^ 12 := by
    rw [hp3]; simpa using sixteen_pow_as_two 3
  have hp4z : ((p4 : ℕ) : ℤ) = 2 ^ 16 := by
    rw [hp4]; simpa using sixteen_pow_as_two 4
  have hp5z : ((p5 : ℕ) : ℤ) = 2 ^ 20 := by
    rw [hp5]; simpa using sixteen_pow_as_two 5
  have hp8z : ((p8 : ℕ) : ℤ) = 2 ^ 32 := by
    rw [hp8]; simpa using sixteen_pow_as_two 8
  have hp10z : ((p10 : ℕ) : ℤ) = 2 ^ 40 := by
    rw [hp10]; simpa using sixteen_pow_as_two 10
  have hp13z : ((p13 : ℕ) : ℤ) = 2 ^ 52 := by
    rw [hp13]; simpa using sixteen_pow_as_two 13
  have hp14z : ((p14 : ℕ) : ℤ) = 2 ^ 56 := by
    rw [hp14]; simpa using sixteen_pow_as_two 14
  have hp18z : ((p18 : ℕ) : ℤ) = 2 ^ 72 := by
    rw [hp18]; simpa using sixteen_pow_as_two 18
  have hp21z : ((p21 : ℕ) : ℤ) = 2 ^ 84 := by
    rw [hp21]; simpa using sixteen_pow_as_two 21
  rw [hp3z, hp4z, hp5z, hp8z, hp10z, hp13z, hp14z, hp18z, hp21z]
  have h16 : (16 : ℤ) = 2 ^ 4 := by norm_num
  rw [h16]
  simpa using poly_id_24t19 (u : ℤ)

lemma popc_choose_two_pow_six_of_mod_24_eq_nineteen {m : ℕ}
    (hm : 19 ≤ m) (hmod : m % 24 = 19) :
    popc (Nat.choose (2 ^ m) 6) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 24 * t + 19 := ⟨m / 24, by omega⟩
  have hm6 : 6 ≤ m := by omega
  rw [choose_two_pow_six m hm6, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) / 45 =
        hexEval (digits_24t19 t) := by
    have hmul := hexEval_digits_24t19_mul_fortyfive t
    set u := 16 ^ (6 * t) with hudef
    have h16 : 16 ^ (6 * t) = 2 ^ (24 * t) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 2 ^ 19 * u := by
      rw [ht, hudef, pow_add, h16]; ring
    have h2m1 : 2 ^ (m - 1) = 2 ^ 18 * u := by
      have : m - 1 = 24 * t + 18 := by omega
      rw [this, hudef, pow_add, h16]; ring
    have h2m2 : 2 ^ (m - 2) = 2 ^ 17 * u := by
      have : m - 2 = 24 * t + 17 := by omega
      rw [this, hudef, pow_add, h16]; ring
    rw [h2m, h2m1, h2m2]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 45) hmul.symm
  rw [hex, popc_hexEval_digits_24t19 t]
  omega

lemma a_ne_zero_two_pow_mod24_eq_nineteen {m : ℕ} (hm : 19 ≤ m) (hmod : m % 24 = 19) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 6 (by decide) ?_
    (popc_choose_two_pow_six_of_mod_24_eq_nineteen hm hmod)
  have : 6 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 6 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  exact this

lemma descFactorial_seven (n : ℕ) :
    n.descFactorial 7 =
      (n - 6) * (n - 5) * (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma choose_two_pow_seven (m : ℕ) (hm : 7 ≤ m) :
    Nat.choose (2 ^ m) 7 =
      2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) / 315) := by
  have h7le : 7 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 7 ≤ 8 := by decide
         _ = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 7 =
      (2 ^ m - 6) * (2 ^ m - 5) * (2 ^ m - 4) * (2 ^ m - 3) * (2 ^ m - 2) *
        (2 ^ m - 1) * 2 ^ m :=
    descFactorial_seven _
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h6 : 2 ^ m - 6 = 2 * (2 ^ (m - 1) - 3) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 3 ≤ 2 ^ (m - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      calc 3 ≤ 4 := by decide
           _ = 2 ^ 2 := by decide
           _ ≤ 2 ^ (m - 1) := this
    omega
  have hprod :
      (2 ^ m).descFactorial 7 =
        2 ^ (m + 4) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * (2 ^ (m - 1) - 3)) := by
    rw [hdesc, h4, h2, h6]
    ring_nf
  have hfac : (2 ^ m).descFactorial 7 = 5040 * Nat.choose (2 ^ m) 7 := by
    have : 7 ! = 5040 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h16 : 2 ^ (m + 4) = 16 * 2 ^ m := by
    rw [pow_add, show (2 : ℕ) ^ 4 = 16 from rfl, mul_comm]
  rw [h16] at hfac
  have : 16 * (2 ^ m *
      ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
        (2 ^ m - 5) * (2 ^ (m - 1) - 3))) =
      16 * (315 * Nat.choose (2 ^ m) 7) := by
    have h5040 : (5040 : ℕ) = 16 * 315 := by decide
    rw [h5040] at hfac
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 16) this
  have h315dvd : 315 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
      (2 ^ (m - 2) - 1) * (2 ^ m - 5) * (2 ^ (m - 1) - 3) := by
    have : 315 ∣ 2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3)) :=
      ⟨Nat.choose (2 ^ m) 7, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 315 (2 ^ m) := by
      have : Nat.Coprime 315 2 := by decide
      simpa using this.pow_right m
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 7 =
      (2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3))) / 315 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (315 : ℕ) ≠ 0)
    convert hcancel.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h315dvd]

/- Digit list for the odd part of `C(2^{24t+9}, 7)`, `t ≥ 1`. LSB first. -/

def digits_24t9 (t : ℕ) : List ℕ :=
  [7]
    ++ List.flatten (List.replicate (2 * t) [11, 13, 6])
    ++ [3]
    ++ List.flatten (List.replicate (2 * t) [0, 10, 14])
    ++ [0, 10, 0, 7]
    ++ List.flatten (List.replicate (2 * t - 1) [5, 15, 6])
    ++ [5, 15, 14, 14, 9]
    ++ List.flatten (List.replicate (2 * t) [1, 0, 10])
    ++ List.flatten (List.replicate (2 * t) [14, 1, 1])
    ++ [14, 1]
    ++ List.flatten (List.replicate (2 * t) [3, 0, 4])
    ++ [3]

lemma digits_24t9_lt (t : ℕ) : ∀ d ∈ digits_24t9 t, d < 16 := by
  intro d hd
  unfold digits_24t9 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten, List.mem_replicate] at hd
  aesop

lemma popc_digits_24t9 (t : ℕ) (ht : 1 ≤ t) :
    (List.map popc (digits_24t9 t)).sum = 64 * t + 22 := by
  have h7 : popc 7 = 3 := by decide
  have h11 : popc 11 = 3 := by decide
  have h13 : popc 13 = 3 := by decide
  have h6 : popc 6 = 2 := by decide
  have h3 : popc 3 = 2 := by decide
  have h0 : popc 0 = 0 := by decide
  have h10 : popc 10 = 2 := by decide
  have h14 : popc 14 = 3 := by decide
  have h5 : popc 5 = 2 := by decide
  have h15 : popc 15 = 4 := by decide
  have h9 : popc 9 = 2 := by decide
  have h1 : popc 1 = 1 := by decide
  have h4 : popc 4 = 1 := by decide
  unfold digits_24t9
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_replicate, map_popc_flatten_replicate]
  rw [h7, h11, h13, h6, h3, h0, h10, h14, h5, h15, h9, h1, h4]
  omega

lemma popc_hexEval_digits_24t9 (t : ℕ) (ht : 1 ≤ t) :
    popc (hexEval (digits_24t9 t)) = 64 * t + 22 := by
  rw [popc_hexEval _ (digits_24t9_lt t), popc_digits_24t9 t ht]

lemma hexEval_b76 : hexEval [11, 13, 6] = 1755 := by decide
lemma hexEval_0ae : hexEval [0, 10, 14] = 3744 := by decide
lemma hexEval_0a07 : hexEval [0, 10, 0, 7] = 28832 := by decide
lemma hexEval_5f6 : hexEval [5, 15, 6] = 1781 := by decide
lemma hexEval_5fee9 : hexEval [5, 15, 14, 14, 9] = 650997 := by decide
lemma hexEval_10a : hexEval [1, 0, 10] = 2561 := by decide
lemma hexEval_e11 : hexEval [14, 1, 1] = 286 := by decide
lemma hexEval_304 : hexEval [3, 0, 4] = 1027 := by decide

lemma hexEval_digits_24t9_eq (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t9 t) =
      7
        + 16 * (1755 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (6 * t + 1) * 3
        + 16 ^ (6 * t + 2) *
            (3744 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (12 * t + 2) * 28832
        + 16 ^ (12 * t + 6) *
            (1781 * ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i))
        + 16 ^ (18 * t + 3) * 650997
        + 16 ^ (18 * t + 8) *
            (2561 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (24 * t + 8) *
            (286 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (30 * t + 8) * 30
        + 16 ^ (30 * t + 10) *
            (1027 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (36 * t + 10) * 3 := by
  unfold digits_24t9
  repeat rw [hexEval_append]
  rw [hexEval_singleton, hexEval_singleton, hexEval_pair]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_b76, hexEval_0ae, hexEval_0a07, hexEval_5f6, hexEval_5fee9,
    hexEval_10a, hexEval_e11, hexEval_304]
  simp only [List.length_cons, List.length_nil, List.length_append,
    List.length_replicate, length_flatten_replicate]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f2 : (0 + 1 + 1 : ℕ) = 2 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f4 : (0 + 1 + 1 + 1 + 1 : ℕ) = 4 := rfl
  have f5 : (0 + 1 + 1 + 1 + 1 + 1 : ℕ) = 5 := rfl
  rw [f1, f2, f3, f4, f5]
  have e1 : 1 + (2 * t) * 3 = 6 * t + 1 := by omega
  rw [e1]
  have e2 : 6 * t + 1 + 1 = 6 * t + 2 := by omega
  rw [e2]
  have e3 : 6 * t + 2 + (2 * t) * 3 = 12 * t + 2 := by omega
  rw [e3]
  have e4 : 12 * t + 2 + 4 = 12 * t + 6 := by omega
  rw [e4]
  have e5 : 12 * t + 6 + (2 * t - 1) * 3 = 18 * t + 3 := by omega
  rw [e5]
  have e6 : 18 * t + 3 + 5 = 18 * t + 8 := by omega
  rw [e6]
  have e7 : 18 * t + 8 + (2 * t) * 3 = 24 * t + 8 := by omega
  rw [e7]
  have e8 : 24 * t + 8 + (2 * t) * 3 = 30 * t + 8 := by omega
  rw [e8]
  have e9 : 30 * t + 8 + 2 = 30 * t + 10 := by omega
  rw [e9]
  have e10 : 30 * t + 10 + (2 * t) * 3 = 36 * t + 10 := by omega
  rw [e10]
  simp [hexEval_singleton]

lemma poly_id_24t9 (y : ℤ) :
    (2205 : ℤ)
      + 2160 * (4096 * y - 1)
      + 15120 * (4096 * y)
      + 73728 * (4096 * y) * (4096 * y - 1)
      + 2325012480 * (4096 * y) ^ 2
      + 2298478592 * (4096 * y) ^ 2 * (y - 1)
      + 839942369280 * (4096 * y) ^ 3
      + 846108557312 * (4096 * y) ^ 3 * (4096 * y - 1)
      + 94489280512 * (4096 * y) ^ 4 * (4096 * y - 1)
      + 40587440947200 * (4096 * y) ^ 5
      + 86861418594304 * (4096 * y) ^ 5 * (4096 * y - 1)
      + 1039038488248320 * (4096 * y) ^ 6
    =
      (2097152 * y - 1) * (1048576 * y - 1) * (2097152 * y - 3) *
        (524288 * y - 1) * (2097152 * y - 5) * (1048576 * y - 3) := by
  ring

lemma dist_24t9 (H H2 u p6 p8 p10 : ℕ) :
    (7 + 16 * (1755 * H) + 16 * u * 3 + 256 * u * (3744 * H)
      + 256 * (u * u) * 28832 + p6 * (u * u) * (1781 * H2)
      + 4096 * (u * u * u) * 650997 + p8 * (u * u * u) * (2561 * H)
      + p8 * (u * u * u * u) * (286 * H) + p8 * (u * u * u * u * u) * 30
      + p10 * (u * u * u * u * u) * (1027 * H)
      + p10 * (u * u * u * u * u * u) * 3) * 315
    =
      2205 + 315 * 16 * 1755 * H + 315 * 16 * 3 * u
        + 315 * 256 * 3744 * H * u + 315 * 256 * 28832 * (u * u)
        + 315 * p6 * 1781 * H2 * (u * u) + 315 * 4096 * 650997 * (u * u * u)
        + 315 * p8 * 2561 * H * (u * u * u)
        + 315 * p8 * 286 * H * (u * u * u * u)
        + 315 * p8 * 30 * (u * u * u * u * u)
        + 315 * p10 * 1027 * H * (u * u * u * u * u)
        + 315 * p10 * 3 * (u * u * u * u * u * u) := by
  ring

lemma hexEval_digits_24t9_mul_315 (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t9 t) * 315 =
      (512 * 16 ^ (6 * t) - 1) * (256 * 16 ^ (6 * t) - 1) *
        (512 * 16 ^ (6 * t) - 3) * (128 * 16 ^ (6 * t) - 1) *
        (512 * 16 ^ (6 * t) - 5) * (256 * 16 ^ (6 * t) - 3) := by
  have hex := hexEval_digits_24t9_eq t ht
  set H := ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i) with hHdef
  set H2 := ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i) with hH2def
  set u := 16 ^ (6 * t) with hudef
  set y := 16 ^ (6 * t - 3) with hydef
  set p6 := 16 ^ 6 with hp6
  set p8 := 16 ^ 8 with hp8
  set p10 := 16 ^ 10 with hp10
  have hHpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hH : H * 4095 = u - 1 := by
    rw [hHdef, hudef]
    have : ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (2 * t), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (6 * t) = 4096 ^ (2 * t) := by
      have : 6 * t = 3 * (2 * t) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    rw [this]
    exact geom_sum_4096 (2 * t)
  have hH2 : H2 * 4095 = y - 1 := by
    rw [hH2def, hydef]
    have : ∑ i ∈ Finset.range (2 * t - 1), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (2 * t - 1), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (6 * t - 3) = 4096 ^ (2 * t - 1) := by
      have : 6 * t - 3 = 3 * (2 * t - 1) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    rw [this]
    exact geom_sum_4096 (2 * t - 1)
  have hu1 : 1 ≤ u := by
    rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have hy1 : 1 ≤ y := by
    rw [hydef]; exact Nat.one_le_pow _ _ (by decide)
  have puy : u = 4096 * y := by
    rw [hudef, hydef]
    have : (4096 : ℕ) = 16 ^ 3 := by decide
    rw [this, sixteen_pow_mul]; congr 1; omega
  have p61 : 16 ^ (6 * t + 1) = 16 * u := by
    rw [hudef, pow_add, pow_one]
    ring
  have p62 : 16 ^ (6 * t + 2) = 256 * u := by
    rw [hudef, pow_add]
    have : (16 : ℕ) ^ 2 = 256 := by decide
    rw [this]
    ring
  have p122 : 16 ^ (12 * t + 2) = 256 * (u * u) := by
    have : 12 * t + 2 = 6 * t + 6 * t + 2 := by omega
    rw [this, pow_add, pow_add, hudef]
    have : (16 : ℕ) ^ 2 = 256 := by decide
    rw [this]; ring
  have p126 : 16 ^ (12 * t + 6) = p6 * (u * u) := by
    have : 12 * t + 6 = 6 + (6 * t + 6 * t) := by omega
    rw [this, pow_add, hp6, hudef, pow_add]
  have p183 : 16 ^ (18 * t + 3) = 4096 * (u * u * u) := by
    have : 18 * t + 3 = 3 + (6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hudef, pow_add, pow_add]
    have : (16 : ℕ) ^ 3 = 4096 := by decide
    rw [this]
  have p188 : 16 ^ (18 * t + 8) = p8 * (u * u * u) := by
    have : 18 * t + 8 = 8 + (6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp8, hudef, pow_add, pow_add]
  have p248 : 16 ^ (24 * t + 8) = p8 * (u * u * u * u) := by
    have : 24 * t + 8 = 8 + (6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp8, hudef, pow_add, pow_add, pow_add]
  have p308 : 16 ^ (30 * t + 8) = p8 * (u * u * u * u * u) := by
    have : 30 * t + 8 = 8 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp8, hudef, pow_add, pow_add, pow_add, pow_add]
  have p3010 : 16 ^ (30 * t + 10) = p10 * (u * u * u * u * u) := by
    have : 30 * t + 10 = 10 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp10, hudef, pow_add, pow_add, pow_add, pow_add]
  have p3610 : 16 ^ (36 * t + 10) = p10 * (u * u * u * u * u * u) := by
    have : 36 * t + 10 = 10 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp10, hudef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factH0 : (315 * 16 * 1755 : ℕ) = 4095 * 2160 := by decide
  have factH1 : (315 * 256 * 3744 : ℕ) = 4095 * 73728 := by decide
  have factH2 : (315 * p6 * 1781 : ℕ) = 4095 * 2298478592 := by
    rw [hp6]; decide
  have factH3 : (315 * p8 * 2561 : ℕ) = 4095 * 846108557312 := by
    rw [hp8]; decide
  have factH4 : (315 * p8 * 286 : ℕ) = 4095 * 94489280512 := by
    rw [hp8]; decide
  have factH5 : (315 * p10 * 1027 : ℕ) = 4095 * 86861418594304 := by
    rw [hp10]; decide
  have factC1 : (315 * 16 * 3 : ℕ) = 15120 := by decide
  have factC2 : (315 * 256 * 28832 : ℕ) = 2325012480 := by decide
  have factC3 : (315 * 4096 * 650997 : ℕ) = 839942369280 := by decide
  have factC4 : (315 * p8 * 30 : ℕ) = 40587440947200 := by
    rw [hp8]; decide
  have factC5 : (315 * p10 * 3 : ℕ) = 1039038488248320 := by
    rw [hp10]; decide
  have hex315 :
      hexEval (digits_24t9 t) * 315 =
        2205 + 2160 * (u - 1) + 15120 * u
          + 73728 * u * (u - 1) + 2325012480 * (u * u)
          + 2298478592 * (u * u) * (y - 1)
          + 839942369280 * (u * u * u)
          + 846108557312 * (u * u * u) * (u - 1)
          + 94489280512 * (u * u * u * u) * (u - 1)
          + 40587440947200 * (u * u * u * u * u)
          + 86861418594304 * (u * u * u * u * u) * (u - 1)
          + 1039038488248320 * (u * u * u * u * u * u) := by
    rw [hex, p61, p62, p122, p126, p183, p188, p248, p308, p3010, p3610]
    rw [dist_24t9 H H2 u p6 p8 p10]
    have H0 : 315 * 16 * 1755 * H = 2160 * (u - 1) := by
      rw [factH0]
      have : 4095 * 2160 * H = 2160 * (H * 4095) := by ring
      rw [this, hH]
    have H1 : 315 * 256 * 3744 * H * u = 73728 * u * (u - 1) := by
      rw [factH1]
      have : 4095 * 73728 * H * u = 73728 * u * (H * 4095) := by ring
      rw [this, hH]
    have H2t : 315 * p6 * 1781 * H2 * (u * u) = 2298478592 * (u * u) * (y - 1) := by
      rw [factH2]
      have : 4095 * 2298478592 * H2 * (u * u) =
          2298478592 * (u * u) * (H2 * 4095) := by ring
      rw [this, hH2]
    have H3 : 315 * p8 * 2561 * H * (u * u * u) =
        846108557312 * (u * u * u) * (u - 1) := by
      rw [factH3]
      have : 4095 * 846108557312 * H * (u * u * u) =
          846108557312 * (u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H4 : 315 * p8 * 286 * H * (u * u * u * u) =
        94489280512 * (u * u * u * u) * (u - 1) := by
      rw [factH4]
      have : 4095 * 94489280512 * H * (u * u * u * u) =
          94489280512 * (u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H5 : 315 * p10 * 1027 * H * (u * u * u * u * u) =
        86861418594304 * (u * u * u * u * u) * (u - 1) := by
      rw [factH5]
      have : 4095 * 86861418594304 * H * (u * u * u * u * u) =
          86861418594304 * (u * u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have C1 : 315 * 16 * 3 * u = 15120 * u := by rw [factC1]
    have C2 : 315 * 256 * 28832 * (u * u) = 2325012480 * (u * u) := by rw [factC2]
    have C3 : 315 * 4096 * 650997 * (u * u * u) = 839942369280 * (u * u * u) := by
      rw [factC3]
    have C4 : 315 * p8 * 30 * (u * u * u * u * u) =
        40587440947200 * (u * u * u * u * u) := by rw [factC4]
    have C5 : 315 * p10 * 3 * (u * u * u * u * u * u) =
        1039038488248320 * (u * u * u * u * u * u) := by rw [factC5]
    rw [H0, H1, H2t, H3, H4, H5, C1, C2, C3, C4, C5]
  have hex315' :
      hexEval (digits_24t9 t) * 315 =
        2205 + 2160 * (u - 1) + 15120 * u
          + 73728 * u * (u - 1) + 2325012480 * u ^ 2
          + 2298478592 * u ^ 2 * (y - 1)
          + 839942369280 * u ^ 3
          + 846108557312 * u ^ 3 * (u - 1)
          + 94489280512 * u ^ 4 * (u - 1)
          + 40587440947200 * u ^ 5
          + 86861418594304 * u ^ 5 * (u - 1)
          + 1039038488248320 * u ^ 6 := by
    rw [hex315]
    ring
  rw [hex315']
  have hR :
      (512 * 16 ^ (6 * t) - 1) * (256 * 16 ^ (6 * t) - 1) *
        (512 * 16 ^ (6 * t) - 3) * (128 * 16 ^ (6 * t) - 1) *
        (512 * 16 ^ (6 * t) - 5) * (256 * 16 ^ (6 * t) - 3) =
      (512 * u - 1) * (256 * u - 1) * (512 * u - 3) *
        (128 * u - 1) * (512 * u - 5) * (256 * u - 3) := by
    rw [hudef]
  rw [hR]
  have h512 : 1 ≤ 512 * u := one_le_mul (by decide : 1 ≤ 512) hu1
  have h256 : 1 ≤ 256 * u := one_le_mul (by decide : 1 ≤ 256) hu1
  have h128 : 1 ≤ 128 * u := one_le_mul (by decide : 1 ≤ 128) hu1
  have h512_3 : 3 ≤ 512 * u :=
    (by decide : 3 ≤ 512).trans (Nat.le_mul_of_pos_right 512 hu1)
  have h512_5 : 5 ≤ 512 * u :=
    (by decide : 5 ≤ 512).trans (Nat.le_mul_of_pos_right 512 hu1)
  have h256_3 : 3 ≤ 256 * u :=
    (by decide : 3 ≤ 256).trans (Nat.le_mul_of_pos_right 256 hu1)
  zify [hu1, hy1, h512, h256, h128, h512_3, h512_5, h256_3]
  have huy : (u : ℤ) = 4096 * y := by
    rw [puy]
    simp only [Int.natCast_mul]
    norm_cast
  simp only [huy]
  have h512y : (512 : ℤ) * (4096 * y) = 2097152 * y := by ring
  have h256y : (256 : ℤ) * (4096 * y) = 1048576 * y := by ring
  have h128y : (128 : ℤ) * (4096 * y) = 524288 * y := by ring
  rw [h512y, h256y, h128y]
  simpa using poly_id_24t9 (y : ℤ)

lemma popc_choose_two_pow_seven_of_mod_24_eq_nine {m : ℕ}
    (hm : 33 ≤ m) (hmod : m % 24 = 9) :
    popc (Nat.choose (2 ^ m) 7) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 24 * t + 9 := ⟨m / 24, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hm7 : 7 ≤ m := by omega
  rw [choose_two_pow_seven m hm7, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) / 315 =
        hexEval (digits_24t9 t) := by
    have hmul := hexEval_digits_24t9_mul_315 t ht1
    set u := 16 ^ (6 * t) with hudef
    have h16 : 16 ^ (6 * t) = 2 ^ (24 * t) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 512 * u := by
      rw [ht, hudef, pow_add, h16, show (2 : ℕ) ^ 9 = 512 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 256 * u := by
      have : m - 1 = 24 * t + 8 := by omega
      rw [this, hudef, pow_add, h16, show (2 : ℕ) ^ 8 = 256 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 128 * u := by
      have : m - 2 = 24 * t + 7 := by omega
      rw [this, hudef, pow_add, h16, show (2 : ℕ) ^ 7 = 128 from rfl]
      ring
    rw [h2m, h2m1, h2m2]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 315) hmul.symm
  rw [hex, popc_hexEval_digits_24t9 t ht1]
  omega

lemma a_ne_zero_two_pow_nine : a (2 ^ 9) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ 9) 7 (by decide) (by decide) ?_
  have hm : 7 ≤ 9 := by decide
  rw [choose_two_pow_seven 9 hm, popc_mul_two_pow]
  have hpow : (2 : ℕ) ^ 9 = 512 := rfl
  have h8 : (2 : ℕ) ^ 8 = 256 := rfl
  have h7 : (2 : ℕ) ^ 7 = 128 := rfl
  rw [hpow, h8, h7]
  have : (512 - 1) * (256 - 1) * (512 - 3) * (128 - 1) * (512 - 5) * (256 - 3) / 315
      = 3430050471991 := by
    norm_num
  rw [this]
  decide

lemma a_ne_zero_two_pow_mod24_eq_nine {m : ℕ} (hm : 9 ≤ m) (hmod : m % 24 = 9) :
    a (2 ^ m) ≠ 0 := by
  by_cases h9 : m = 9
  · subst h9; exact a_ne_zero_two_pow_nine
  · have hm33 : 33 ≤ m := by omega
    refine a_ne_zero_of_witness (2 ^ m) 7 (by decide) ?_
      (popc_choose_two_pow_seven_of_mod_24_eq_nine hm33 hmod)
    have : 7 ≤ 2 ^ m := by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      calc 7 ≤ 8 := by decide
           _ = 2 ^ 3 := by decide
           _ ≤ 2 ^ m := this
    exact this

lemma descFactorial_eight (n : ℕ) :
    n.descFactorial 8 =
      (n - 7) * (n - 6) * (n - 5) * (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma choose_two_pow_eight (m : ℕ) (hm : 8 ≤ m) :
    Nat.choose (2 ^ m) 8 =
      2 ^ (m - 3) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) / 315) := by
  have h8le : 8 ≤ 2 ^ m := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 8 = 2 ^ 3 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 8 =
      (2 ^ m - 7) * (2 ^ m - 6) * (2 ^ m - 5) * (2 ^ m - 4) * (2 ^ m - 3) *
        (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m :=
    descFactorial_eight _
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h6 : 2 ^ m - 6 = 2 * (2 ^ (m - 1) - 3) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 3 ≤ 2 ^ (m - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      calc 3 ≤ 4 := by decide
           _ = 2 ^ 2 := by decide
           _ ≤ 2 ^ (m - 1) := this
    omega
  have hprod :
      (2 ^ m).descFactorial 8 =
        2 ^ (m + 4) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7)) := by
    rw [hdesc, h4, h2, h6]
    ring_nf
  have hfac : (2 ^ m).descFactorial 8 = 40320 * Nat.choose (2 ^ m) 8 := by
    have : 8 ! = 40320 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h128 : 2 ^ (m + 4) = 128 * 2 ^ (m - 3) := by
    have : 2 ^ (m + 4) = 2 ^ (m - 3 + 7) := by congr 1; omega
    rw [this, pow_add, show (2 : ℕ) ^ 7 = 128 from rfl, mul_comm]
  rw [h128] at hfac
  have : 128 * (2 ^ (m - 3) *
      ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
        (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7))) =
      128 * (315 * Nat.choose (2 ^ m) 8) := by
    have h40320 : (40320 : ℕ) = 128 * 315 := by decide
    rw [h40320] at hfac
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 128) this
  have h315dvd : 315 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
      (2 ^ (m - 2) - 1) * (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) := by
    have : 315 ∣ 2 ^ (m - 3) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7)) :=
      ⟨Nat.choose (2 ^ m) 8, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 315 (2 ^ (m - 3)) := by
      have : Nat.Coprime 315 2 := by decide
      simpa using this.pow_right (m - 3)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 8 =
      (2 ^ (m - 3) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7))) / 315 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (315 : ℕ) ≠ 0)
    convert hcancel.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h315dvd]

def digits_24t11 (t : ℕ) : List ℕ :=
  List.replicate (6 * t + 2) 15
    ++ [1, 3]
    ++ List.flatten (List.replicate (2 * t) [4, 13, 1])
    ++ [4, 4]
    ++ List.flatten (List.replicate (2 * t) [13, 10, 14])
    ++ [13, 0, 7]
    ++ List.flatten (List.replicate (2 * t) [14, 5, 4])
    ++ [14, 13, 12]
    ++ List.flatten (List.replicate (2 * t) [1, 4, 13])
    ++ [1, 7]
    ++ List.flatten (List.replicate (2 * t) [10, 9, 6])
    ++ [10, 9]
    ++ List.flatten (List.replicate (2 * t) [1, 0, 10])
    ++ [1]

lemma digits_24t11_lt (t : ℕ) : ∀ d ∈ digits_24t11 t, d < 16 := by
  intro d hd
  unfold digits_24t11 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten, List.mem_replicate] at hd
  aesop

lemma popc_digits_24t11 (t : ℕ) (ht : 1 ≤ t) :
    (List.map popc (digits_24t11 t)).sum = 90 * t + 36 := by
  have h15 : popc 15 = 4 := by decide
  have h1 : popc 1 = 1 := by decide
  have h3 : popc 3 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h13 : popc 13 = 3 := by decide
  have h10 : popc 10 = 2 := by decide
  have h14 : popc 14 = 3 := by decide
  have h0 : popc 0 = 0 := by decide
  have h7 : popc 7 = 3 := by decide
  have h5 : popc 5 = 2 := by decide
  have h12 : popc 12 = 2 := by decide
  have h9 : popc 9 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  unfold digits_24t11
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_replicate, map_popc_flatten_replicate]
  rw [h15, h1, h3, h4, h13, h10, h14, h0, h7, h5, h12, h9, h6]
  omega

lemma popc_hexEval_digits_24t11 (t : ℕ) (ht : 1 ≤ t) :
    popc (hexEval (digits_24t11 t)) = 90 * t + 36 := by
  rw [popc_hexEval _ (digits_24t11_lt t), popc_digits_24t11 t ht]

lemma hexEval_4d1 : hexEval [4, 13, 1] = 468 := by decide
lemma hexEval_dae : hexEval [13, 10, 14] = 3757 := by decide
lemma hexEval_d07 : hexEval [13, 0, 7] = 1805 := by decide
lemma hexEval_e54 : hexEval [14, 5, 4] = 1118 := by decide
lemma hexEval_edc : hexEval [14, 13, 12] = 3294 := by decide
lemma hexEval_14d : hexEval [1, 4, 13] = 3393 := by decide
lemma hexEval_a96 : hexEval [10, 9, 6] = 1690 := by decide

lemma hexEval_digits_24t11_eq (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t11 t) =
      15 * ∑ i ∈ Finset.range (6 * t + 2), 16 ^ i
        + 16 ^ (6 * t + 2) * 49
        + 16 ^ (6 * t + 4) *
            (468 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (12 * t + 4) * 68
        + 16 ^ (12 * t + 6) *
            (3757 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (18 * t + 6) * 1805
        + 16 ^ (18 * t + 9) *
            (1118 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (24 * t + 9) * 3294
        + 16 ^ (24 * t + 12) *
            (3393 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (30 * t + 12) * 113
        + 16 ^ (30 * t + 14) *
            (1690 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (36 * t + 14) * 154
        + 16 ^ (36 * t + 16) *
            (2561 * ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i))
        + 16 ^ (42 * t + 16) * 1 := by
  unfold digits_24t11
  repeat rw [hexEval_append]
  rw [hexEval_replicate]
  rw [hexEval_pair, hexEval_pair, hexEval_pair, hexEval_pair, hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_4d1, hexEval_dae, hexEval_d07, hexEval_e54, hexEval_edc,
    hexEval_14d, hexEval_a96, hexEval_10a]
  simp only [List.length_cons, List.length_nil, List.length_append,
    List.length_replicate, length_flatten_replicate]
  have f2 : (0 + 1 + 1 : ℕ) = 2 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  rw [f2, f3]
  have e1 : 6 * t + 2 + 2 = 6 * t + 4 := by omega
  rw [e1]
  have e2 : 6 * t + 4 + (2 * t) * 3 = 12 * t + 4 := by omega
  rw [e2]
  have e3 : 12 * t + 4 + 2 = 12 * t + 6 := by omega
  rw [e3]
  have e4 : 12 * t + 6 + (2 * t) * 3 = 18 * t + 6 := by omega
  rw [e4]
  have e5 : 18 * t + 6 + 3 = 18 * t + 9 := by omega
  rw [e5]
  have e6 : 18 * t + 9 + (2 * t) * 3 = 24 * t + 9 := by omega
  rw [e6]
  have e7 : 24 * t + 9 + 3 = 24 * t + 12 := by omega
  rw [e7]
  have e8 : 24 * t + 12 + (2 * t) * 3 = 30 * t + 12 := by omega
  rw [e8]
  have e9 : 30 * t + 12 + 2 = 30 * t + 14 := by omega
  rw [e9]
  have e10 : 30 * t + 14 + (2 * t) * 3 = 36 * t + 14 := by omega
  rw [e10]
  have e11 : 36 * t + 14 + 2 = 36 * t + 16 := by omega
  rw [e11]
  have e12 : 36 * t + 16 + (2 * t) * 3 = 42 * t + 16 := by omega
  rw [e12]

lemma poly_id_24t11 (u : ℤ) :
    (315 : ℤ) * (256 * u - 1) + 3951360 * u
      + 2359296 * u * (u - 1)
      + 1403781120 * u ^ 2
      + 4848615424 * u ^ 2 * (u - 1)
      + 9539105587200 * u ^ 3
      + 5909874999296 * u ^ 3 * (u - 1)
      + 71304016256040960 * u ^ 4
      + 73464968921481216 * u ^ 4 * (u - 1)
      + 10019101796015800320 * u ^ 5
      + 9367487224930631680 * u ^ 5 * (u - 1)
      + 3495513886779884175360 * u ^ 6
      + 3634008582520781668352 * u ^ 6 * (u - 1)
      + 5810724383218508759040 * u ^ 7
    =
      (2048 * u - 1) * (1024 * u - 1) * (2048 * u - 3) *
        (512 * u - 1) * (2048 * u - 5) * (1024 * u - 3) * (2048 * u - 7) := by
  ring

lemma dist_24t11 (G H u p4 p6 p9 p12 p14 p16 : ℕ) :
    (15 * G + 256 * u * 49 + p4 * u * (468 * H)
      + p4 * (u * u) * 68 + p6 * (u * u) * (3757 * H)
      + p6 * (u * u * u) * 1805 + p9 * (u * u * u) * (1118 * H)
      + p9 * (u * u * u * u) * 3294 + p12 * (u * u * u * u) * (3393 * H)
      + p12 * (u * u * u * u * u) * 113 + p14 * (u * u * u * u * u) * (1690 * H)
      + p14 * (u * u * u * u * u * u) * 154
      + p16 * (u * u * u * u * u * u) * (2561 * H)
      + p16 * (u * u * u * u * u * u * u)) * 315
    =
      315 * 15 * G + 315 * 256 * 49 * u + 315 * p4 * 468 * H * u
        + 315 * p4 * 68 * (u * u) + 315 * p6 * 3757 * H * (u * u)
        + 315 * p6 * 1805 * (u * u * u) + 315 * p9 * 1118 * H * (u * u * u)
        + 315 * p9 * 3294 * (u * u * u * u)
        + 315 * p12 * 3393 * H * (u * u * u * u)
        + 315 * p12 * 113 * (u * u * u * u * u)
        + 315 * p14 * 1690 * H * (u * u * u * u * u)
        + 315 * p14 * 154 * (u * u * u * u * u * u)
        + 315 * p16 * 2561 * H * (u * u * u * u * u * u)
        + 315 * p16 * (u * u * u * u * u * u * u) := by
  ring

lemma hexEval_digits_24t11_mul_315 (t : ℕ) (ht : 1 ≤ t) :
    hexEval (digits_24t11 t) * 315 =
      (2048 * 16 ^ (6 * t) - 1) * (1024 * 16 ^ (6 * t) - 1) *
        (2048 * 16 ^ (6 * t) - 3) * (512 * 16 ^ (6 * t) - 1) *
        (2048 * 16 ^ (6 * t) - 5) * (1024 * 16 ^ (6 * t) - 3) *
        (2048 * 16 ^ (6 * t) - 7) := by
  have hex := hexEval_digits_24t11_eq t ht
  set G := ∑ i ∈ Finset.range (6 * t + 2), 16 ^ i with hGdef
  set H := ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i) with hHdef
  set u := 16 ^ (6 * t) with hudef
  set p4 := 16 ^ 4 with hp4
  set p6 := 16 ^ 6 with hp6
  set p9 := 16 ^ 9 with hp9
  set p12 := 16 ^ 12 with hp12
  set p14 := 16 ^ 14 with hp14
  set p16 := 16 ^ 16 with hp16
  have hG : G * 15 = 256 * u - 1 := by
    rw [hGdef, hudef]
    have : 16 ^ (6 * t + 2) = 256 * 16 ^ (6 * t) := by
      rw [pow_add]
      have : (16 : ℕ) ^ 2 = 256 := by decide
      rw [this]
      ring
    rw [← this]
    exact geom_sum_sixteen (6 * t + 2)
  have hHpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hH : H * 4095 = u - 1 := by
    rw [hHdef, hudef]
    have : ∑ i ∈ Finset.range (2 * t), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (2 * t), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (6 * t) = 4096 ^ (2 * t) := by
      have : 6 * t = 3 * (2 * t) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    rw [this]
    exact geom_sum_4096 (2 * t)
  have hu1 : 1 ≤ u := by
    rw [hudef]; exact Nat.one_le_pow _ _ (by decide)
  have p62 : 16 ^ (6 * t + 2) = 256 * u := by
    rw [hudef, pow_add]
    have : (16 : ℕ) ^ 2 = 256 := by decide
    rw [this]; ring
  have p64 : 16 ^ (6 * t + 4) = p4 * u := by
    rw [hp4, hudef, add_comm, pow_add]
  have p124 : 16 ^ (12 * t + 4) = p4 * (u * u) := by
    have : 12 * t + 4 = 4 + (6 * t + 6 * t) := by omega
    rw [this, pow_add, hp4, hudef, pow_add]
  have p126 : 16 ^ (12 * t + 6) = p6 * (u * u) := by
    have : 12 * t + 6 = 6 + (6 * t + 6 * t) := by omega
    rw [this, pow_add, hp6, hudef, pow_add]
  have p186 : 16 ^ (18 * t + 6) = p6 * (u * u * u) := by
    have : 18 * t + 6 = 6 + (6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp6, hudef, pow_add, pow_add]
  have p189 : 16 ^ (18 * t + 9) = p9 * (u * u * u) := by
    have : 18 * t + 9 = 9 + (6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp9, hudef, pow_add, pow_add]
  have p249 : 16 ^ (24 * t + 9) = p9 * (u * u * u * u) := by
    have : 24 * t + 9 = 9 + (6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp9, hudef, pow_add, pow_add, pow_add]
  have p2412 : 16 ^ (24 * t + 12) = p12 * (u * u * u * u) := by
    have : 24 * t + 12 = 12 + (6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp12, hudef, pow_add, pow_add, pow_add]
  have p3012 : 16 ^ (30 * t + 12) = p12 * (u * u * u * u * u) := by
    have : 30 * t + 12 = 12 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp12, hudef, pow_add, pow_add, pow_add, pow_add]
  have p3014 : 16 ^ (30 * t + 14) = p14 * (u * u * u * u * u) := by
    have : 30 * t + 14 = 14 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp14, hudef, pow_add, pow_add, pow_add, pow_add]
  have p3614 : 16 ^ (36 * t + 14) = p14 * (u * u * u * u * u * u) := by
    have : 36 * t + 14 = 14 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp14, hudef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have p3616 : 16 ^ (36 * t + 16) = p16 * (u * u * u * u * u * u) := by
    have : 36 * t + 16 = 16 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp16, hudef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have p4216 : 16 ^ (42 * t + 16) = p16 * (u * u * u * u * u * u * u) := by
    have : 42 * t + 16 = 16 + (6 * t + 6 * t + 6 * t + 6 * t + 6 * t + 6 * t + 6 * t) := by omega
    rw [this, pow_add, hp16, hudef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factG : (315 * 15 : ℕ) = 315 * 15 := rfl
  have factH1 : (315 * p4 * 468 : ℕ) = 4095 * 2359296 := by rw [hp4]; decide
  have factH2 : (315 * p6 * 3757 : ℕ) = 4095 * 4848615424 := by rw [hp6]; decide
  have factH3 : (315 * p9 * 1118 : ℕ) = 4095 * 5909874999296 := by rw [hp9]; decide
  have factH4 : (315 * p12 * 3393 : ℕ) = 4095 * 73464968921481216 := by rw [hp12]; decide
  have factH5 : (315 * p14 * 1690 : ℕ) = 4095 * 9367487224930631680 := by rw [hp14]; decide
  have factH6 : (315 * p16 * 2561 : ℕ) = 4095 * 3634008582520781668352 := by rw [hp16]; decide
  have factC1 : (315 * 256 * 49 : ℕ) = 3951360 := by decide
  have factC2 : (315 * p4 * 68 : ℕ) = 1403781120 := by rw [hp4]; decide
  have factC3 : (315 * p6 * 1805 : ℕ) = 9539105587200 := by rw [hp6]; decide
  have factC4 : (315 * p9 * 3294 : ℕ) = 71304016256040960 := by rw [hp9]; decide
  have factC5 : (315 * p12 * 113 : ℕ) = 10019101796015800320 := by rw [hp12]; decide
  have factC6 : (315 * p14 * 154 : ℕ) = 3495513886779884175360 := by rw [hp14]; decide
  have factC7 : (315 * p16 : ℕ) = 5810724383218508759040 := by rw [hp16]; decide
  have hex315 :
      hexEval (digits_24t11 t) * 315 =
        315 * (256 * u - 1) + 3951360 * u
          + 2359296 * u * (u - 1)
          + 1403781120 * (u * u)
          + 4848615424 * (u * u) * (u - 1)
          + 9539105587200 * (u * u * u)
          + 5909874999296 * (u * u * u) * (u - 1)
          + 71304016256040960 * (u * u * u * u)
          + 73464968921481216 * (u * u * u * u) * (u - 1)
          + 10019101796015800320 * (u * u * u * u * u)
          + 9367487224930631680 * (u * u * u * u * u) * (u - 1)
          + 3495513886779884175360 * (u * u * u * u * u * u)
          + 3634008582520781668352 * (u * u * u * u * u * u) * (u - 1)
          + 5810724383218508759040 * (u * u * u * u * u * u * u) := by
    rw [hex, p62, p64, p124, p126, p186, p189, p249, p2412, p3012, p3014, p3614, p3616, p4216]
    simp only [mul_one]
    rw [dist_24t11 G H u p4 p6 p9 p12 p14 p16]
    have hG15 : 315 * 15 * G = 315 * (256 * u - 1) := by
      have : 315 * 15 * G = 315 * (G * 15) := by ring
      rw [this, hG]
    rw [hG15]
    have H1 : 315 * p4 * 468 * H * u = 2359296 * u * (u - 1) := by
      rw [factH1]
      have : 4095 * 2359296 * H * u = 2359296 * u * (H * 4095) := by ring
      rw [this, hH]
    have H2 : 315 * p6 * 3757 * H * (u * u) = 4848615424 * (u * u) * (u - 1) := by
      rw [factH2]
      have : 4095 * 4848615424 * H * (u * u) = 4848615424 * (u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H3 : 315 * p9 * 1118 * H * (u * u * u) =
        5909874999296 * (u * u * u) * (u - 1) := by
      rw [factH3]
      have : 4095 * 5909874999296 * H * (u * u * u) =
          5909874999296 * (u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H4 : 315 * p12 * 3393 * H * (u * u * u * u) =
        73464968921481216 * (u * u * u * u) * (u - 1) := by
      rw [factH4]
      have : 4095 * 73464968921481216 * H * (u * u * u * u) =
          73464968921481216 * (u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H5 : 315 * p14 * 1690 * H * (u * u * u * u * u) =
        9367487224930631680 * (u * u * u * u * u) * (u - 1) := by
      rw [factH5]
      have : 4095 * 9367487224930631680 * H * (u * u * u * u * u) =
          9367487224930631680 * (u * u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have H6 : 315 * p16 * 2561 * H * (u * u * u * u * u * u) =
        3634008582520781668352 * (u * u * u * u * u * u) * (u - 1) := by
      rw [factH6]
      have : 4095 * 3634008582520781668352 * H * (u * u * u * u * u * u) =
          3634008582520781668352 * (u * u * u * u * u * u) * (H * 4095) := by ring
      rw [this, hH]
    have C1 : 315 * 256 * 49 * u = 3951360 * u := by rw [factC1]
    have C2 : 315 * p4 * 68 * (u * u) = 1403781120 * (u * u) := by rw [factC2]
    have C3 : 315 * p6 * 1805 * (u * u * u) = 9539105587200 * (u * u * u) := by
      rw [factC3]
    have C4 : 315 * p9 * 3294 * (u * u * u * u) =
        71304016256040960 * (u * u * u * u) := by rw [factC4]
    have C5 : 315 * p12 * 113 * (u * u * u * u * u) =
        10019101796015800320 * (u * u * u * u * u) := by rw [factC5]
    have C6 : 315 * p14 * 154 * (u * u * u * u * u * u) =
        3495513886779884175360 * (u * u * u * u * u * u) := by rw [factC6]
    have C7 : 315 * p16 * (u * u * u * u * u * u * u) =
        5810724383218508759040 * (u * u * u * u * u * u * u) := by
      rw [factC7]
    rw [H1, H2, H3, H4, H5, H6, C1, C2, C3, C4, C5, C6, C7]
  have hex315' :
      hexEval (digits_24t11 t) * 315 =
        315 * (256 * u - 1) + 3951360 * u
          + 2359296 * u * (u - 1)
          + 1403781120 * u ^ 2
          + 4848615424 * u ^ 2 * (u - 1)
          + 9539105587200 * u ^ 3
          + 5909874999296 * u ^ 3 * (u - 1)
          + 71304016256040960 * u ^ 4
          + 73464968921481216 * u ^ 4 * (u - 1)
          + 10019101796015800320 * u ^ 5
          + 9367487224930631680 * u ^ 5 * (u - 1)
          + 3495513886779884175360 * u ^ 6
          + 3634008582520781668352 * u ^ 6 * (u - 1)
          + 5810724383218508759040 * u ^ 7 := by
    rw [hex315]
    ring
  rw [hex315']
  have hR :
      (2048 * 16 ^ (6 * t) - 1) * (1024 * 16 ^ (6 * t) - 1) *
        (2048 * 16 ^ (6 * t) - 3) * (512 * 16 ^ (6 * t) - 1) *
        (2048 * 16 ^ (6 * t) - 5) * (1024 * 16 ^ (6 * t) - 3) *
        (2048 * 16 ^ (6 * t) - 7) =
      (2048 * u - 1) * (1024 * u - 1) * (2048 * u - 3) *
        (512 * u - 1) * (2048 * u - 5) * (1024 * u - 3) * (2048 * u - 7) := by
    rw [hudef]
  rw [hR]
  have h2048 : 1 ≤ 2048 * u := one_le_mul (by decide : 1 ≤ 2048) hu1
  have h1024 : 1 ≤ 1024 * u := one_le_mul (by decide : 1 ≤ 1024) hu1
  have h512 : 1 ≤ 512 * u := one_le_mul (by decide : 1 ≤ 512) hu1
  have h2048_3 : 3 ≤ 2048 * u :=
    (by decide : 3 ≤ 2048).trans (Nat.le_mul_of_pos_right 2048 hu1)
  have h2048_5 : 5 ≤ 2048 * u :=
    (by decide : 5 ≤ 2048).trans (Nat.le_mul_of_pos_right 2048 hu1)
  have h1024_3 : 3 ≤ 1024 * u :=
    (by decide : 3 ≤ 1024).trans (Nat.le_mul_of_pos_right 1024 hu1)
  have h2048_7 : 7 ≤ 2048 * u :=
    (by decide : 7 ≤ 2048).trans (Nat.le_mul_of_pos_right 2048 hu1)
  have h256u : 1 ≤ 256 * u := one_le_mul (by decide : 1 ≤ 256) hu1
  zify [hu1, h2048, h1024, h512, h2048_3, h2048_5, h1024_3, h2048_7, h256u]
  simpa using poly_id_24t11 (u : ℤ)

lemma popc_choose_two_pow_eight_of_mod_24_eq_eleven {m : ℕ}
    (hm : 35 ≤ m) (hmod : m % 24 = 11) :
    popc (Nat.choose (2 ^ m) 8) % 2 = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, m = 24 * t + 11 := ⟨m / 24, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hm8 : 8 ≤ m := by omega
  rw [choose_two_pow_eight m hm8, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) / 315 =
        hexEval (digits_24t11 t) := by
    have hmul := hexEval_digits_24t11_mul_315 t ht1
    set u := 16 ^ (6 * t) with hudef
    have h16 : 16 ^ (6 * t) = 2 ^ (24 * t) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 2048 * u := by
      rw [ht, hudef, pow_add, h16, show (2 : ℕ) ^ 11 = 2048 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 1024 * u := by
      have : m - 1 = 24 * t + 10 := by omega
      rw [this, hudef, pow_add, h16, show (2 : ℕ) ^ 10 = 1024 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 512 * u := by
      have : m - 2 = 24 * t + 9 := by omega
      rw [this, hudef, pow_add, h16, show (2 : ℕ) ^ 9 = 512 from rfl]
      ring
    rw [h2m, h2m1, h2m2]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 315) hmul.symm
  rw [hex, popc_hexEval_digits_24t11 t ht1]
  omega


lemma a_ne_zero_two_pow_eleven : a (2 ^ 11) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ 11) 8 (by decide) (by decide) ?_
  have hm : 8 ≤ 11 := by decide
  rw [choose_two_pow_eight 11 hm, popc_mul_two_pow]
  have h11 : (2 : ℕ) ^ 11 = 2048 := rfl
  have h10 : (2 : ℕ) ^ 10 = 1024 := rfl
  have h9 : (2 : ℕ) ^ 9 = 512 := rfl
  rw [h11, h10, h9]
  have : (2048 - 1) * (1024 - 1) * (2048 - 3) * (512 - 1) * (2048 - 5) *
      (1024 - 3) * (2048 - 7) / 315 = 29575646620162470399 := by
    norm_num
  rw [this]
  decide

lemma a_ne_zero_two_pow_mod24_eq_eleven {m : ℕ} (hm : 11 ≤ m) (hmod : m % 24 = 11) :
    a (2 ^ m) ≠ 0 := by
  by_cases h11 : m = 11
  · subst h11; exact a_ne_zero_two_pow_eleven
  · have hm35 : 35 ≤ m := by omega
    refine a_ne_zero_of_witness (2 ^ m) 8 (by decide) ?_
      (popc_choose_two_pow_eight_of_mod_24_eq_eleven hm35 hmod)
    have : 8 ≤ 2 ^ m := by
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      calc 8 = 2 ^ 3 := by decide
           _ ≤ 2 ^ m := this
    exact this

/- Digit list for the odd part of `C(2^{216s+17}, 9)`, `s ≥ 0`. LSB first. -/

def blockA27 : List ℕ :=
  [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 14, 3, 5, 5, 0, 7, 12, 12, 8, 3, 9, 10, 10]

def blockB27 : List ℕ :=
  [9, 4, 10, 11, 11, 6, 13, 2, 3, 15, 9, 15, 0, 1, 12, 2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 13]

def blockC27 : List ℕ :=
  [9, 7, 12, 10, 14, 8, 12, 5, 5, 14, 12, 1, 0, 4, 14, 1, 11, 10, 3, 2, 7, 5, 9, 3, 7, 0, 0]

def blockD27 : List ℕ :=
  [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10, 8, 13, 11, 15, 9, 13, 6, 6, 15, 13, 2, 1]

def blockE27 : List ℕ :=
  [7, 8, 8, 3, 10, 15, 15, 11, 6, 12, 13, 13, 8, 15, 4, 5, 1, 12, 1, 3, 3, 14, 4, 10, 10, 6, 1]

def blockF27 : List ℕ :=
  [3, 14, 2, 0, 0, 10, 12, 1, 1, 9, 3, 8, 5, 5, 15, 1, 7, 6, 14, 8, 13, 10, 10, 4, 7, 12, 11]

def digits_216s17 (s : ℕ) : List ℕ :=
  [9]
    ++ List.flatten (List.replicate (18 * s) [3, 14, 8])
    ++ [3, 14, 12, 12]
    ++ List.flatten (List.replicate (18 * s) [8, 6, 13])
    ++ [8, 6, 15, 11]
    ++ List.flatten (List.replicate (2 * s) blockA27)
    ++ [5, 12, 5, 12]
    ++ List.flatten (List.replicate (2 * s) blockB27)
    ++ [9, 4, 0, 1]
    ++ List.flatten (List.replicate (2 * s) blockC27)
    ++ [9, 7, 12, 0]
    ++ List.flatten (List.replicate (2 * s) blockD27)
    ++ [5, 15, 2]
    ++ List.flatten (List.replicate (2 * s) blockE27)
    ++ [7, 8, 8]
    ++ List.flatten (List.replicate (2 * s) blockF27)
    ++ [3, 14, 2]

lemma digits_216s17_lt (s : ℕ) : ∀ d ∈ digits_216s17 s, d < 16 := by
  intro d hd
  unfold digits_216s17 blockA27 blockB27 blockC27 blockD27 blockE27 blockF27 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten] at hd
  aesop

lemma popc_blockA27 : (List.map popc blockA27).sum = 57 := by
  unfold blockA27
  decide

lemma popc_blockB27 : (List.map popc blockB27).sum = 53 := by
  unfold blockB27
  decide

lemma popc_blockC27 : (List.map popc blockC27).sum = 50 := by
  unfold blockC27
  decide

lemma popc_blockD27 : (List.map popc blockD27).sum = 55 := by
  unfold blockD27
  decide

lemma popc_blockE27 : (List.map popc blockE27).sum = 57 := by
  unfold blockE27
  decide

lemma popc_blockF27 : (List.map popc blockF27).sum = 51 := by
  unfold blockF27
  decide

lemma popc_digits_216s17 (s : ℕ) :
    (List.map popc (digits_216s17 s)).sum = 58 + 862 * s := by
  have h0 : popc 0 = 0 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h3 : popc 3 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h5 : popc 5 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h7 : popc 7 = 3 := by decide
  have h8 : popc 8 = 1 := by decide
  have h9 : popc 9 = 2 := by decide
  have h10 : popc 10 = 2 := by decide
  have h11 : popc 11 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h13 : popc 13 = 3 := by decide
  have h14 : popc 14 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  unfold digits_216s17
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_flatten_replicate]
  rw [popc_blockA27, popc_blockB27, popc_blockC27, popc_blockD27, popc_blockE27, popc_blockF27]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

lemma popc_hexEval_digits_216s17 (s : ℕ) :
    popc (hexEval (digits_216s17 s)) = 58 + 862 * s := by
  rw [popc_hexEval _ (digits_216s17_lt s), popc_digits_216s17 s]

lemma hexEval_3e8 : hexEval [3, 14, 8] = 2275 := by decide
lemma hexEval_3ecc : hexEval [3, 14, 12, 12] = 52451 := by decide
lemma hexEval_86d : hexEval [8, 6, 13] = 3432 := by decide
lemma hexEval_86fb : hexEval [8, 6, 15, 11] = 49000 := by decide
lemma hexEval_5c5c : hexEval [5, 12, 5, 12] = 50629 := by decide
lemma hexEval_9401 : hexEval [9, 4, 0, 1] = 4169 := by decide
lemma hexEval_97c0 : hexEval [9, 7, 12, 0] = 3193 := by decide
lemma hexEval_5f2 : hexEval [5, 15, 2] = 757 := by decide
lemma hexEval_788 : hexEval [7, 8, 8] = 2183 := by decide
lemma hexEval_3e2 : hexEval [3, 14, 2] = 739 := by decide

lemma hexEval_blockA27 :
    hexEval blockA27 = 216231233813322076505602018648517 := by
  unfold blockA27; decide

lemma hexEval_blockB27 :
    hexEval blockB27 = 280791538668120197812727237556809 := by
  unfold blockB27; decide

lemma hexEval_blockC27 :
    hexEval blockC27 = 572343128145373415843308678265 := by
  unfold blockC27; decide

lemma hexEval_blockD27 :
    hexEval blockD27 = 23923942756476608782250302751477 := by
  unfold blockD27; decide

lemma hexEval_blockE27 :
    hexEval blockE27 = 28731625032897745475334095648903 := by
  unfold blockE27; decide

lemma hexEval_blockF27 :
    hexEval blockF27 = 238896021687878863772997042307811 := by
  unfold blockF27; decide

lemma length_blockA27 : blockA27.length = 27 := by unfold blockA27; decide
lemma length_blockB27 : blockB27.length = 27 := by unfold blockB27; decide
lemma length_blockC27 : blockC27.length = 27 := by unfold blockC27; decide
lemma length_blockD27 : blockD27.length = 27 := by unfold blockD27; decide
lemma length_blockE27 : blockE27.length = 27 := by unfold blockE27; decide
lemma length_blockF27 : blockF27.length = 27 := by unfold blockF27; decide


lemma hexEval_digits_216s17_eq (s : ℕ) :
    hexEval (digits_216s17 s) =
      9
        + 16 * (2275 * ∑ i ∈ Finset.range (18 * s), 16 ^ (3 * i))
        + 16 ^ (54 * s + 1) * 52451
        + 16 ^ (54 * s + 5) * (3432 * ∑ i ∈ Finset.range (18 * s), 16 ^ (3 * i))
        + 16 ^ (108 * s + 5) * 49000
        + 16 ^ (108 * s + 9) * (216231233813322076505602018648517 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (162 * s + 9) * 50629
        + 16 ^ (162 * s + 13) * (280791538668120197812727237556809 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (216 * s + 13) * 4169
        + 16 ^ (216 * s + 17) * (572343128145373415843308678265 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (270 * s + 17) * 3193
        + 16 ^ (270 * s + 21) * (23923942756476608782250302751477 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (324 * s + 21) * 757
        + 16 ^ (324 * s + 24) * (28731625032897745475334095648903 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (378 * s + 24) * 2183
        + 16 ^ (378 * s + 27) * (238896021687878863772997042307811 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (432 * s + 27) * 739 := by
  unfold digits_216s17
  repeat rw [hexEval_append]
  rw [hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_3e8, hexEval_3ecc, hexEval_86d, hexEval_86fb, hexEval_5c5c,
    hexEval_9401, hexEval_97c0, hexEval_5f2, hexEval_788, hexEval_3e2,
    hexEval_blockA27, hexEval_blockB27, hexEval_blockC27, hexEval_blockD27,
    hexEval_blockE27, hexEval_blockF27]
  simp only [List.length_cons, List.length_nil, List.length_append,
    length_flatten_replicate, length_blockA27, length_blockB27, length_blockC27,
    length_blockD27, length_blockE27, length_blockF27]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f4 : (0 + 1 + 1 + 1 + 1 : ℕ) = 4 := rfl
  rw [f1, f3, f4]
  have e1 : 1 + (18 * s) * 3 = 54 * s + 1 := by omega
  rw [e1]
  have e2 : 54 * s + 1 + 4 = 54 * s + 5 := by omega
  rw [e2]
  have e3 : 54 * s + 5 + (18 * s) * 3 = 108 * s + 5 := by omega
  rw [e3]
  have e4 : 108 * s + 5 + 4 = 108 * s + 9 := by omega
  rw [e4]
  have e5 : 108 * s + 9 + (2 * s) * 27 = 162 * s + 9 := by omega
  rw [e5]
  have e6 : 162 * s + 9 + 4 = 162 * s + 13 := by omega
  rw [e6]
  have e7 : 162 * s + 13 + (2 * s) * 27 = 216 * s + 13 := by omega
  rw [e7]
  have e8 : 216 * s + 13 + 4 = 216 * s + 17 := by omega
  rw [e8]
  have e9 : 216 * s + 17 + (2 * s) * 27 = 270 * s + 17 := by omega
  rw [e9]
  have e10 : 270 * s + 17 + 4 = 270 * s + 21 := by omega
  rw [e10]
  have e11 : 270 * s + 21 + (2 * s) * 27 = 324 * s + 21 := by omega
  rw [e11]
  have e12 : 324 * s + 21 + 3 = 324 * s + 24 := by omega
  rw [e12]
  have e13 : 324 * s + 24 + (2 * s) * 27 = 378 * s + 24 := by omega
  rw [e13]
  have e14 : 378 * s + 24 + 3 = 378 * s + 27 := by omega
  rw [e14]
  have e15 : 378 * s + 27 + (2 * s) * 27 = 432 * s + 27 := by omega
  rw [e15]
  simp [hexEval_singleton]


lemma geom_sum_16_pow_27 (n : ℕ) :
    (∑ i ∈ Finset.range n, (16 ^ 27) ^ i) * (16 ^ 27 - 1) = (16 ^ 27) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    have hle : 1 ≤ (16 ^ 27) ^ n := Nat.one_le_pow _ _ (by decide)
    have : (16 ^ 27) ^ n - 1 + (16 ^ 27) ^ n * (16 ^ 27 - 1) =
        (16 ^ 27) ^ n * 16 ^ 27 - 1 := by
      have hq : 1 ≤ 16 ^ 27 := Nat.one_le_pow _ _ (by decide)
      omega
    exact this

lemma poly_id_216s17 (U : ℤ) :
    (25515 : ℤ)
      + 25200 * (U - 1)
      + 2379177360 * U
      + 2491416576 * U * (U - 1)
      + 145662935040000 * U ^ 2
      + 129811091554304 * U ^ 2 * (U - 1)
      + 9863527429035786240 * U ^ 3
      + 11047329885939826688 * U ^ 3 * (U - 1)
      + 53228561909849039831040 * U ^ 4
      + 1475739525896764129280 * U ^ 4 * (U - 1)
      + 2671724585608804579336519680 * U ^ 5
      + 4042647940791319960217452544 * U ^ 5 * (U - 1)
      + 41511514509533721579056812523520 * U ^ 6
      + 19886268791080348735979531534336 * U ^ 6 * (U - 1)
      + 490327648309091703820612767559188480 * U ^ 7
      + 677270221485136578796446614942646272 * U ^ 7 * (U - 1)
      + 679887463620391790347952768248593776640 * U ^ 8
    =
      (131072 * U - 1) * (65536 * U - 1) * (131072 * U - 3) * (32768 * U - 1) *
        (131072 * U - 5) * (65536 * U - 3) * (131072 * U - 7) * (16384 * U - 1) := by
  ring

lemma dist_216s17 (G H U p1 p5 p9 p13 p17 p21 p24 p27 : ℕ) :
    (9 + 16 * (2275 * G) + p1 * U * 52451 + p5 * U * (3432 * G)
      + p5 * (U * U) * 49000 + p9 * (U * U) * (216231233813322076505602018648517 * H)
      + p9 * (U * U * U) * 50629 + p13 * (U * U * U) * (280791538668120197812727237556809 * H)
      + p13 * (U * U * U * U) * 4169 + p17 * (U * U * U * U) * (572343128145373415843308678265 * H)
      + p17 * (U * U * U * U * U) * 3193
      + p21 * (U * U * U * U * U) * (23923942756476608782250302751477 * H)
      + p21 * (U * U * U * U * U * U) * 757
      + p24 * (U * U * U * U * U * U) * (28731625032897745475334095648903 * H)
      + p24 * (U * U * U * U * U * U * U) * 2183
      + p27 * (U * U * U * U * U * U * U) * (238896021687878863772997042307811 * H)
      + p27 * (U * U * U * U * U * U * U * U) * 739) * 2835
    =
      25515
        + 2835 * 16 * 2275 * G
        + 2835 * p1 * 52451 * U
        + 2835 * p5 * 3432 * G * U
        + 2835 * p5 * 49000 * (U * U)
        + 2835 * p9 * 216231233813322076505602018648517 * H * (U * U)
        + 2835 * p9 * 50629 * (U * U * U)
        + 2835 * p13 * 280791538668120197812727237556809 * H * (U * U * U)
        + 2835 * p13 * 4169 * (U * U * U * U)
        + 2835 * p17 * 572343128145373415843308678265 * H * (U * U * U * U)
        + 2835 * p17 * 3193 * (U * U * U * U * U)
        + 2835 * p21 * 23923942756476608782250302751477 * H * (U * U * U * U * U)
        + 2835 * p21 * 757 * (U * U * U * U * U * U)
        + 2835 * p24 * 28731625032897745475334095648903 * H * (U * U * U * U * U * U)
        + 2835 * p24 * 2183 * (U * U * U * U * U * U * U)
        + 2835 * p27 * 238896021687878863772997042307811 * H * (U * U * U * U * U * U * U)
        + 2835 * p27 * 739 * (U * U * U * U * U * U * U * U) := by
  ring

lemma descFactorial_nine (n : ℕ) :
    n.descFactorial 9 =
      (n - 8) * (n - 7) * (n - 6) * (n - 5) * (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma choose_two_pow_nine (m : ℕ) (hm : 9 ≤ m) :
    Nat.choose (2 ^ m) 9 =
      2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) / 2835) := by
  have h9le : 9 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 9 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 9 =
      (2 ^ m - 8) * (2 ^ m - 7) * (2 ^ m - 6) * (2 ^ m - 5) * (2 ^ m - 4) *
        (2 ^ m - 3) * (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m :=
    descFactorial_nine _
  have h8 : 2 ^ m - 8 = 8 * (2 ^ (m - 3) - 1) := by
    have : 2 ^ m = 8 * 2 ^ (m - 3) := by
      have : 2 ^ m = 2 ^ (m - 3 + 3) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add]
      have : (2 : ℕ) ^ 3 = 8 := by decide
      rw [this, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 3) := Nat.one_le_pow _ _ (by decide)
    omega
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h6 : 2 ^ m - 6 = 2 * (2 ^ (m - 1) - 3) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 3 ≤ 2 ^ (m - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      calc 3 ≤ 4 := by decide
           _ = 2 ^ 2 := by decide
           _ ≤ 2 ^ (m - 1) := this
    omega
  have hprod :
      (2 ^ m).descFactorial 9 =
        2 ^ (m + 7) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1)) := by
    rw [hdesc, h8, h4, h2, h6]
    ring_nf
  have hfac : (2 ^ m).descFactorial 9 = 362880 * Nat.choose (2 ^ m) 9 := by
    have : 9 ! = 362880 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h128 : 2 ^ (m + 7) = 128 * 2 ^ m := by
    have : 2 ^ (m + 7) = 2 ^ (m + 7) := rfl
    rw [pow_add, show (2 : ℕ) ^ 7 = 128 from rfl, mul_comm]
  rw [h128] at hfac
  have : 128 * (2 ^ m *
      ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
        (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1))) =
      128 * (2835 * Nat.choose (2 ^ m) 9) := by
    have h362880 : (362880 : ℕ) = 128 * 2835 := by decide
    rw [h362880] at hfac
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 128) this
  have h2835dvd : 2835 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
      (2 ^ (m - 2) - 1) * (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) *
      (2 ^ (m - 3) - 1) := by
    have : 2835 ∣ 2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1)) :=
      ⟨Nat.choose (2 ^ m) 9, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 2835 (2 ^ m) := by
      have : Nat.Coprime 2835 2 := by decide
      simpa using this.pow_right m
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 9 =
      (2 ^ m *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1))) / 2835 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (2835 : ℕ) ≠ 0)
    convert hcancel.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h2835dvd]


lemma descFactorial_ten (n : ℕ) :
    n.descFactorial 10 =
      (n - 9) * (n - 8) * (n - 7) * (n - 6) * (n - 5) *
        (n - 4) * (n - 3) * (n - 2) * (n - 1) * n := by
  simp [Nat.descFactorial_succ]
  ring

lemma choose_two_pow_ten (m : ℕ) (hm : 10 ≤ m) :
    Nat.choose (2 ^ m) 10 =
      2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
          (2 ^ m - 9) / 14175) := by
  have h10le : 10 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 10 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  have hdesc : (2 ^ m).descFactorial 10 =
      (2 ^ m - 9) * (2 ^ m - 8) * (2 ^ m - 7) * (2 ^ m - 6) * (2 ^ m - 5) *
        (2 ^ m - 4) * (2 ^ m - 3) * (2 ^ m - 2) * (2 ^ m - 1) * 2 ^ m :=
    descFactorial_ten _
  have h8 : 2 ^ m - 8 = 8 * (2 ^ (m - 3) - 1) := by
    have : 2 ^ m = 8 * 2 ^ (m - 3) := by
      have : 2 ^ m = 2 ^ (m - 3 + 3) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add]
      have : (2 : ℕ) ^ 3 = 8 := by decide
      rw [this, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 3) := Nat.one_le_pow _ _ (by decide)
    omega
  have h4 : 2 ^ m - 4 = 4 * (2 ^ (m - 2) - 1) := by
    have : 2 ^ m = 4 * 2 ^ (m - 2) := by
      have : 2 ^ m = 2 ^ (m - 2 + 2) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_add, pow_two, mul_comm]
      ring
    have hle : 1 ≤ 2 ^ (m - 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h2 : 2 ^ m - 2 = 2 * (2 ^ (m - 1) - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have h6 : 2 ^ m - 6 = 2 * (2 ^ (m - 1) - 3) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have : 2 ^ m = 2 ^ (m - 1 + 1) := by rw [Nat.sub_add_cancel (by omega)]
      rw [this, pow_succ, mul_comm]
    have hle : 3 ≤ 2 ^ (m - 1) := by
      have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      calc 3 ≤ 4 := by decide
           _ = 2 ^ 2 := by decide
           _ ≤ 2 ^ (m - 1) := this
    omega
  have hprod :
      (2 ^ m).descFactorial 10 =
        2 ^ (m + 7) *
          ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
            (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
            (2 ^ m - 9)) := by
    rw [hdesc, h8, h4, h2, h6]
    ring_nf
  have hfac : (2 ^ m).descFactorial 10 = 3628800 * Nat.choose (2 ^ m) 10 := by
    have : 10 ! = 3628800 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h256 : 2 ^ (m + 7) = 256 * 2 ^ (m - 1) := by
    have : m + 7 = (m - 1) + 8 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 8 = 256 from rfl, mul_comm]
  rw [h256] at hfac
  have : 256 * (2 ^ (m - 1) *
      ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
        (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
        (2 ^ m - 9))) =
      256 * (14175 * Nat.choose (2 ^ m) 10) := by
    have h3628800 : (3628800 : ℕ) = 256 * 14175 := by decide
    rw [h3628800] at hfac
    convert hfac using 1 <;> ring
  have hcancel := Nat.mul_left_cancel (by decide : 0 < 256) this
  have h14175dvd : 14175 ∣ (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) *
      (2 ^ (m - 2) - 1) * (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) *
      (2 ^ (m - 3) - 1) * (2 ^ m - 9) := by
    have : 14175 ∣ 2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
          (2 ^ m - 9)) :=
      ⟨Nat.choose (2 ^ m) 10, by
        have := hcancel.symm
        convert this using 1 <;> ring⟩
    have hcop : Nat.Coprime 14175 (2 ^ (m - 1)) := by
      have : Nat.Coprime 14175 2 := by decide
      simpa using this.pow_right (m - 1)
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : Nat.choose (2 ^ m) 10 =
      (2 ^ (m - 1) *
        ((2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) *
          (2 ^ m - 9))) / 14175 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (14175 : ℕ) ≠ 0)
    convert hcancel.symm using 1 <;> ring
  rw [this, Nat.mul_div_assoc _ h14175dvd]

lemma hexEval_digits_216s17_mul_2835 (s : ℕ) :
    hexEval (digits_216s17 s) * 2835 =
      (131072 * 16 ^ (54 * s) - 1) * (65536 * 16 ^ (54 * s) - 1) *
        (131072 * 16 ^ (54 * s) - 3) * (32768 * 16 ^ (54 * s) - 1) *
        (131072 * 16 ^ (54 * s) - 5) * (65536 * 16 ^ (54 * s) - 3) *
        (131072 * 16 ^ (54 * s) - 7) * (16384 * 16 ^ (54 * s) - 1) := by
  have hex := hexEval_digits_216s17_eq s
  set G := ∑ i ∈ Finset.range (18 * s), 16 ^ (3 * i) with hGdef
  set H := ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i) with hHdef
  set U := 16 ^ (54 * s) with hUdef
  set p1 := 16 ^ 1 with hp1
  set p5 := 16 ^ 5 with hp5
  set p9 := 16 ^ 9 with hp9
  set p13 := 16 ^ 13 with hp13
  set p17 := 16 ^ 17 with hp17
  set p21 := 16 ^ 21 with hp21
  set p24 := 16 ^ 24 with hp24
  set p27 := 16 ^ 27 with hp27
  have hGpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hG : G * 4095 = U - 1 := by
    rw [hGdef, hUdef]
    have : ∑ i ∈ Finset.range (18 * s), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (18 * s), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hGpow i
    rw [this]
    have : 16 ^ (54 * s) = 4096 ^ (18 * s) := by
      have : 54 * s = 3 * (18 * s) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    rw [this]
    exact geom_sum_4096 (18 * s)
  have hHpow : ∀ i, 16 ^ (27 * i) = (16 ^ 27) ^ i := by
    intro i; rw [← pow_mul]
  have hH : H * (16 ^ 27 - 1) = U - 1 := by
    rw [hHdef, hUdef]
    have : ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i) =
        ∑ i ∈ Finset.range (2 * s), (16 ^ 27) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (54 * s) = (16 ^ 27) ^ (2 * s) := by
      have : 54 * s = 27 * (2 * s) := by omega
      rw [this, ← pow_mul]
    rw [this]
    exact geom_sum_16_pow_27 (2 * s)
  have hU1 : 1 ≤ U := by
    rw [hUdef]; exact Nat.one_le_pow _ _ (by decide)
  have pw1 : 16 ^ (54 * s + 1) = p1 * U := by
    rw [hUdef, hp1, pow_add, pow_one, mul_comm]
  have pw5a : 16 ^ (54 * s + 5) = p5 * U := by
    have : 54 * s + 5 = 5 + 54 * s := by omega
    rw [this, pow_add, hp5, hUdef]
  have pw5b : 16 ^ (108 * s + 5) = p5 * (U * U) := by
    have : 108 * s + 5 = 5 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp5, hUdef, pow_add]
  have pw9a : 16 ^ (108 * s + 9) = p9 * (U * U) := by
    have : 108 * s + 9 = 9 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp9, hUdef, pow_add]
  have pw9b : 16 ^ (162 * s + 9) = p9 * (U * U * U) := by
    have : 162 * s + 9 = 9 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp9, hUdef, pow_add, pow_add]
  have pw13a : 16 ^ (162 * s + 13) = p13 * (U * U * U) := by
    have : 162 * s + 13 = 13 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp13, hUdef, pow_add, pow_add]
  have pw13b : 16 ^ (216 * s + 13) = p13 * (U * U * U * U) := by
    have : 216 * s + 13 = 13 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp13, hUdef, pow_add, pow_add, pow_add]
  have pw17a : 16 ^ (216 * s + 17) = p17 * (U * U * U * U) := by
    have : 216 * s + 17 = 17 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp17, hUdef, pow_add, pow_add, pow_add]
  have pw17b : 16 ^ (270 * s + 17) = p17 * (U * U * U * U * U) := by
    have : 270 * s + 17 = 17 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp17, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw21a : 16 ^ (270 * s + 21) = p21 * (U * U * U * U * U) := by
    have : 270 * s + 21 = 21 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp21, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw21b : 16 ^ (324 * s + 21) = p21 * (U * U * U * U * U * U) := by
    have : 324 * s + 21 = 21 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp21, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw24a : 16 ^ (324 * s + 24) = p24 * (U * U * U * U * U * U) := by
    have : 324 * s + 24 = 24 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp24, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw24b : 16 ^ (378 * s + 24) = p24 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 24 = 24 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp24, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw27a : 16 ^ (378 * s + 27) = p27 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 27 = 27 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp27, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw27b : 16 ^ (432 * s + 27) = p27 * (U * U * U * U * U * U * U * U) := by
    have : 432 * s + 27 = 27 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp27, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factG0 : (2835 * 16 * 2275 : ℕ) = 4095 * 25200 := by decide
  have factG1 : (2835 * p5 * 3432 : ℕ) = 4095 * 2491416576 := by
    rw [hp5]; decide
  have factHA : (2835 * p9 * 216231233813322076505602018648517 : ℕ) =
      (16 ^ 27 - 1) * 129811091554304 := by
    rw [hp9]; decide
  have factHB : (2835 * p13 * 280791538668120197812727237556809 : ℕ) =
      (16 ^ 27 - 1) * 11047329885939826688 := by
    rw [hp13]; decide
  have factHC : (2835 * p17 * 572343128145373415843308678265 : ℕ) =
      (16 ^ 27 - 1) * 1475739525896764129280 := by
    rw [hp17]; decide
  have factHD : (2835 * p21 * 23923942756476608782250302751477 : ℕ) =
      (16 ^ 27 - 1) * 4042647940791319960217452544 := by
    rw [hp21]; decide
  have factHE : (2835 * p24 * 28731625032897745475334095648903 : ℕ) =
      (16 ^ 27 - 1) * 19886268791080348735979531534336 := by
    rw [hp24]; decide
  have factHF : (2835 * p27 * 238896021687878863772997042307811 : ℕ) =
      (16 ^ 27 - 1) * 677270221485136578796446614942646272 := by
    rw [hp27]; decide
  have factC1 : (2835 * p1 * 52451 : ℕ) = 2379177360 := by
    rw [hp1]; decide
  have factC2 : (2835 * p5 * 49000 : ℕ) = 145662935040000 := by
    rw [hp5]; decide
  have factC3 : (2835 * p9 * 50629 : ℕ) = 9863527429035786240 := by
    rw [hp9]; decide
  have factC4 : (2835 * p13 * 4169 : ℕ) = 53228561909849039831040 := by
    rw [hp13]; decide
  have factC5 : (2835 * p17 * 3193 : ℕ) = 2671724585608804579336519680 := by
    rw [hp17]; decide
  have factC6 : (2835 * p21 * 757 : ℕ) = 41511514509533721579056812523520 := by
    rw [hp21]; decide
  have factC7 : (2835 * p24 * 2183 : ℕ) = 490327648309091703820612767559188480 := by
    rw [hp24]; decide
  have factC8 : (2835 * p27 * 739 : ℕ) = 679887463620391790347952768248593776640 := by
    rw [hp27]; decide
  have hex2835 :
      hexEval (digits_216s17 s) * 2835 =
        25515 + 25200 * (U - 1) + 2379177360 * U
          + 2491416576 * U * (U - 1) + 145662935040000 * (U * U)
          + 129811091554304 * (U * U) * (U - 1)
          + 9863527429035786240 * (U * U * U)
          + 11047329885939826688 * (U * U * U) * (U - 1)
          + 53228561909849039831040 * (U * U * U * U)
          + 1475739525896764129280 * (U * U * U * U) * (U - 1)
          + 2671724585608804579336519680 * (U * U * U * U * U)
          + 4042647940791319960217452544 * (U * U * U * U * U) * (U - 1)
          + 41511514509533721579056812523520 * (U * U * U * U * U * U)
          + 19886268791080348735979531534336 * (U * U * U * U * U * U) * (U - 1)
          + 490327648309091703820612767559188480 * (U * U * U * U * U * U * U)
          + 677270221485136578796446614942646272 * (U * U * U * U * U * U * U) * (U - 1)
          + 679887463620391790347952768248593776640 * (U * U * U * U * U * U * U * U) := by
    rw [hex, pw1, pw5a, pw5b, pw9a, pw9b, pw13a, pw13b, pw17a, pw17b, pw21a, pw21b,
      pw24a, pw24b, pw27a, pw27b]
    rw [dist_216s17 G H U p1 p5 p9 p13 p17 p21 p24 p27]
    have G0 : 2835 * 16 * 2275 * G = 25200 * (U - 1) := by
      rw [factG0]
      have : 4095 * 25200 * G = 25200 * (G * 4095) := by ring
      rw [this, hG]
    have G1 : 2835 * p5 * 3432 * G * U = 2491416576 * U * (U - 1) := by
      rw [factG1]
      have : 4095 * 2491416576 * G * U = 2491416576 * U * (G * 4095) := by ring
      rw [this, hG]
    have HA : 2835 * p9 * 216231233813322076505602018648517 * H * (U * U) =
        129811091554304 * (U * U) * (U - 1) := by
      rw [factHA]
      have : (16 ^ 27 - 1) * 129811091554304 * H * (U * U) =
          129811091554304 * (U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HB : 2835 * p13 * 280791538668120197812727237556809 * H * (U * U * U) =
        11047329885939826688 * (U * U * U) * (U - 1) := by
      rw [factHB]
      have : (16 ^ 27 - 1) * 11047329885939826688 * H * (U * U * U) =
          11047329885939826688 * (U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HC : 2835 * p17 * 572343128145373415843308678265 * H * (U * U * U * U) =
        1475739525896764129280 * (U * U * U * U) * (U - 1) := by
      rw [factHC]
      have : (16 ^ 27 - 1) * 1475739525896764129280 * H * (U * U * U * U) =
          1475739525896764129280 * (U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HD : 2835 * p21 * 23923942756476608782250302751477 * H * (U * U * U * U * U) =
        4042647940791319960217452544 * (U * U * U * U * U) * (U - 1) := by
      rw [factHD]
      have : (16 ^ 27 - 1) * 4042647940791319960217452544 * H * (U * U * U * U * U) =
          4042647940791319960217452544 * (U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HE : 2835 * p24 * 28731625032897745475334095648903 * H * (U * U * U * U * U * U) =
        19886268791080348735979531534336 * (U * U * U * U * U * U) * (U - 1) := by
      rw [factHE]
      have : (16 ^ 27 - 1) * 19886268791080348735979531534336 * H * (U * U * U * U * U * U) =
          19886268791080348735979531534336 * (U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HF : 2835 * p27 * 238896021687878863772997042307811 * H *
        (U * U * U * U * U * U * U) =
        677270221485136578796446614942646272 * (U * U * U * U * U * U * U) * (U - 1) := by
      rw [factHF]
      have : (16 ^ 27 - 1) * 677270221485136578796446614942646272 * H *
          (U * U * U * U * U * U * U) =
          677270221485136578796446614942646272 * (U * U * U * U * U * U * U) *
            (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have C1 : 2835 * p1 * 52451 * U = 2379177360 * U := by rw [factC1]
    have C2 : 2835 * p5 * 49000 * (U * U) = 145662935040000 * (U * U) := by rw [factC2]
    have C3 : 2835 * p9 * 50629 * (U * U * U) = 9863527429035786240 * (U * U * U) := by
      rw [factC3]
    have C4 : 2835 * p13 * 4169 * (U * U * U * U) =
        53228561909849039831040 * (U * U * U * U) := by rw [factC4]
    have C5 : 2835 * p17 * 3193 * (U * U * U * U * U) =
        2671724585608804579336519680 * (U * U * U * U * U) := by rw [factC5]
    have C6 : 2835 * p21 * 757 * (U * U * U * U * U * U) =
        41511514509533721579056812523520 * (U * U * U * U * U * U) := by rw [factC6]
    have C7 : 2835 * p24 * 2183 * (U * U * U * U * U * U * U) =
        490327648309091703820612767559188480 * (U * U * U * U * U * U * U) := by
      rw [factC7]
    have C8 : 2835 * p27 * 739 * (U * U * U * U * U * U * U * U) =
        679887463620391790347952768248593776640 * (U * U * U * U * U * U * U * U) := by
      rw [factC8]
    rw [G0, G1, HA, HB, HC, HD, HE, HF, C1, C2, C3, C4, C5, C6, C7, C8]
  have hex2835' :
      hexEval (digits_216s17 s) * 2835 =
        25515 + 25200 * (U - 1) + 2379177360 * U
          + 2491416576 * U * (U - 1) + 145662935040000 * U ^ 2
          + 129811091554304 * U ^ 2 * (U - 1)
          + 9863527429035786240 * U ^ 3
          + 11047329885939826688 * U ^ 3 * (U - 1)
          + 53228561909849039831040 * U ^ 4
          + 1475739525896764129280 * U ^ 4 * (U - 1)
          + 2671724585608804579336519680 * U ^ 5
          + 4042647940791319960217452544 * U ^ 5 * (U - 1)
          + 41511514509533721579056812523520 * U ^ 6
          + 19886268791080348735979531534336 * U ^ 6 * (U - 1)
          + 490327648309091703820612767559188480 * U ^ 7
          + 677270221485136578796446614942646272 * U ^ 7 * (U - 1)
          + 679887463620391790347952768248593776640 * U ^ 8 := by
    rw [hex2835]
    ring
  rw [hex2835']
  have hR :
      (131072 * 16 ^ (54 * s) - 1) * (65536 * 16 ^ (54 * s) - 1) *
        (131072 * 16 ^ (54 * s) - 3) * (32768 * 16 ^ (54 * s) - 1) *
        (131072 * 16 ^ (54 * s) - 5) * (65536 * 16 ^ (54 * s) - 3) *
        (131072 * 16 ^ (54 * s) - 7) * (16384 * 16 ^ (54 * s) - 1) =
      (131072 * U - 1) * (65536 * U - 1) * (131072 * U - 3) * (32768 * U - 1) *
        (131072 * U - 5) * (65536 * U - 3) * (131072 * U - 7) * (16384 * U - 1) := by
    rw [hUdef]
  rw [hR]
  have h131072 : 1 ≤ 131072 * U := one_le_mul (by decide : 1 ≤ 131072) hU1
  have h65536 : 1 ≤ 65536 * U := one_le_mul (by decide : 1 ≤ 65536) hU1
  have h32768 : 1 ≤ 32768 * U := one_le_mul (by decide : 1 ≤ 32768) hU1
  have h16384 : 1 ≤ 16384 * U := one_le_mul (by decide : 1 ≤ 16384) hU1
  have h131072_3 : 3 ≤ 131072 * U :=
    (by decide : 3 ≤ 131072).trans (Nat.le_mul_of_pos_right 131072 hU1)
  have h131072_5 : 5 ≤ 131072 * U :=
    (by decide : 5 ≤ 131072).trans (Nat.le_mul_of_pos_right 131072 hU1)
  have h131072_7 : 7 ≤ 131072 * U :=
    (by decide : 7 ≤ 131072).trans (Nat.le_mul_of_pos_right 131072 hU1)
  have h65536_3 : 3 ≤ 65536 * U :=
    (by decide : 3 ≤ 65536).trans (Nat.le_mul_of_pos_right 65536 hU1)
  zify [hU1, h131072, h65536, h32768, h16384, h131072_3, h131072_5, h131072_7, h65536_3]
  simpa using poly_id_216s17 (U : ℤ)

lemma popc_choose_two_pow_nine_of_mod_216_eq_seventeen {m : ℕ}
    (hmod : m % 216 = 17) :
    popc (Nat.choose (2 ^ m) 9) % 2 = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m = 216 * s + 17 := ⟨m / 216, by omega⟩
  have hm9 : 9 ≤ m := by omega
  rw [choose_two_pow_nine m hm9, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) / 2835 =
        hexEval (digits_216s17 s) := by
    set U := 16 ^ (54 * s) with hUdef
    have h16 : 16 ^ (54 * s) = 2 ^ (216 * s) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 131072 * U := by
      rw [hs, hUdef, pow_add, h16, show (2 : ℕ) ^ 17 = 131072 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 65536 * U := by
      have : m - 1 = 216 * s + 16 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 16 = 65536 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 32768 * U := by
      have : m - 2 = 216 * s + 15 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 15 = 32768 from rfl]
      ring
    have h2m3 : 2 ^ (m - 3) = 16384 * U := by
      have : m - 3 = 216 * s + 14 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 14 = 16384 from rfl]
      ring
    have hmul := hexEval_digits_216s17_mul_2835 s
    rw [h2m, h2m1, h2m2, h2m3]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2835) hmul.symm
  rw [hex, popc_hexEval_digits_216s17 s]
  omega


lemma a_ne_zero_two_pow_mod216_eq_seventeen {m : ℕ} (hm : 17 ≤ m) (hmod : m % 216 = 17) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 9 (by decide) ?_
    (popc_choose_two_pow_nine_of_mod_216_eq_seventeen hmod)
  have : 9 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 9 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  exact this

/- Digit list for the odd part of `C(2^{216s+41}, 9)`, `s ≥ 0`. LSB first. -/

def blockA27_41 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 14, 3, 5, 5, 0, 7, 12, 12, 8, 3, 9, 10, 10]

def blockB27_41 : List ℕ := [13, 2, 3, 15, 9, 15, 0, 1, 12, 2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 13, 9, 4, 10, 11, 11, 6]

def blockC27_41 : List ℕ := [5, 9, 3, 7, 0, 0, 9, 7, 12, 10, 14, 8, 12, 5, 5, 14, 12, 1, 0, 4, 14, 1, 11, 10, 3, 2, 7]

def blockD27_41 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10, 8, 13, 11, 15, 9, 13, 6, 6, 15, 13, 2, 1]

def blockE27_41 : List ℕ := [5, 1, 12, 1, 3, 3, 14, 4, 10, 10, 6, 1, 7, 8, 8, 3, 10, 15, 15, 11, 6, 12, 13, 13, 8, 15, 4]

def blockF27_41 : List ℕ := [10, 10, 4, 7, 12, 11, 3, 14, 2, 0, 0, 10, 12, 1, 1, 9, 3, 8, 5, 5, 15, 1, 7, 6, 14, 8, 13]

def conn1_41 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 3, 5]
def conn2_41 : List ℕ := [13, 2, 3, 15, 9, 15, 0, 1, 2, 8]
def conn3_41 : List ℕ := [5, 9, 3, 7, 0, 0, 9, 7, 12, 0]
def conn4_41 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6]
def conn5_41 : List ℕ := [5, 1, 12, 1, 3, 3, 14, 4, 10]
def conn6_41 : List ℕ := [10, 10, 4, 7, 12, 11, 3, 14, 2]

def digits_216s41 (s : ℕ) : List ℕ :=
  [9]
    ++ List.flatten (List.replicate (18 * s + 2) [3, 14, 8])
    ++ [3, 14, 12, 12]
    ++ List.flatten (List.replicate (18 * s + 2) [8, 6, 13])
    ++ [8, 6, 15, 11]
    ++ List.flatten (List.replicate (2 * s) blockA27_41)
    ++ conn1_41
    ++ List.flatten (List.replicate (2 * s) blockB27_41)
    ++ conn2_41
    ++ List.flatten (List.replicate (2 * s) blockC27_41)
    ++ conn3_41
    ++ List.flatten (List.replicate (2 * s) blockD27_41)
    ++ conn4_41
    ++ List.flatten (List.replicate (2 * s) blockE27_41)
    ++ conn5_41
    ++ List.flatten (List.replicate (2 * s) blockF27_41)
    ++ conn6_41

lemma digits_216s41_lt (s : ℕ) : ∀ d ∈ digits_216s41 s, d < 16 := by
  intro d hd
  unfold digits_216s41 blockA27_41 blockB27_41 blockC27_41 blockD27_41
    blockE27_41 blockF27_41 conn1_41 conn2_41 conn3_41 conn4_41 conn5_41
    conn6_41 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten] at hd
  aesop

lemma popc_blockA27_41 : (List.map popc blockA27_41).sum = 57 := by
  unfold blockA27_41
  decide

lemma popc_blockB27_41 : (List.map popc blockB27_41).sum = 53 := by
  unfold blockB27_41
  decide

lemma popc_blockC27_41 : (List.map popc blockC27_41).sum = 50 := by
  unfold blockC27_41
  decide

lemma popc_blockD27_41 : (List.map popc blockD27_41).sum = 55 := by
  unfold blockD27_41
  decide

lemma popc_blockE27_41 : (List.map popc blockE27_41).sum = 57 := by
  unfold blockE27_41
  decide

lemma popc_blockF27_41 : (List.map popc blockF27_41).sum = 51 := by
  unfold blockF27_41
  decide

lemma popc_conn1_41 : (List.map popc conn1_41).sum = 21 := by
  unfold conn1_41
  decide

lemma popc_conn2_41 : (List.map popc conn2_41).sum = 19 := by
  unfold conn2_41
  decide

lemma popc_conn3_41 : (List.map popc conn3_41).sum = 16 := by
  unfold conn3_41
  decide

lemma popc_conn4_41 : (List.map popc conn4_41).sum = 18 := by
  unfold conn4_41
  decide

lemma popc_conn5_41 : (List.map popc conn5_41).sum = 16 := by
  unfold conn5_41
  decide

lemma popc_conn6_41 : (List.map popc conn6_41).sum = 19 := by
  unfold conn6_41
  decide

lemma popc_digits_216s41 (s : ℕ) :
    (List.map popc (digits_216s41 s)).sum = 154 + 862 * s := by
  have h0 : popc 0 = 0 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h3 : popc 3 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h5 : popc 5 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h7 : popc 7 = 3 := by decide
  have h8 : popc 8 = 1 := by decide
  have h9 : popc 9 = 2 := by decide
  have h10 : popc 10 = 2 := by decide
  have h11 : popc 11 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h13 : popc 13 = 3 := by decide
  have h14 : popc 14 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  unfold digits_216s41
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_flatten_replicate]
  rw [popc_blockA27_41, popc_blockB27_41, popc_blockC27_41, popc_blockD27_41,
    popc_blockE27_41, popc_blockF27_41, popc_conn1_41, popc_conn2_41, popc_conn3_41,
    popc_conn4_41, popc_conn5_41, popc_conn6_41]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

lemma popc_hexEval_digits_216s41 (s : ℕ) :
    popc (hexEval (digits_216s41 s)) = 154 + 862 * s := by
  rw [popc_hexEval _ (digits_216s41_lt s), popc_digits_216s41 s]

lemma hexEval_blockA27_41 : hexEval blockA27_41 = 216231233813322076505602018648517 := by
  unfold blockA27_41; decide

lemma hexEval_blockB27_41 : hexEval blockB27_41 = 136561070375486097020213450634029 := by
  unfold blockB27_41; decide

lemma hexEval_blockC27_41 : hexEval blockC27_41 = 144802811420779474208357095601045 := by
  unfold blockC27_41; decide

lemma hexEval_blockD27_41 : hexEval blockD27_41 = 23923942756476608782250302751477 := by
  unfold blockD27_41; decide

lemma hexEval_blockE27_41 : hexEval blockE27_41 = 100846859179214795871590989110293 := by
  unfold blockE27_41; decide

lemma hexEval_blockF27_41 : hexEval blockF27_41 = 274953638761037388971125489038506 := by
  unfold blockF27_41; decide

lemma hexEval_conn1_41 : hexEval conn1_41 = 360753013189 := by
  unfold conn1_41; decide

lemma hexEval_conn2_41 : hexEval conn2_41 = 558630564653 := by
  unfold conn2_41; decide

lemma hexEval_conn3_41 : hexEval conn3_41 = 53569680277 := by
  unfold conn3_41; decide

lemma hexEval_conn4_41 : hexEval conn4_41 = 27972584181 := by
  unfold conn4_41; decide

lemma hexEval_conn5_41 : hexEval conn5_41 = 44261645333 := by
  unfold conn5_41; decide

lemma hexEval_conn6_41 : hexEval conn6_41 = 12410713258 := by
  unfold conn6_41; decide

lemma length_blockA27_41 : blockA27_41.length = 27 := by unfold blockA27_41; decide
lemma length_blockB27_41 : blockB27_41.length = 27 := by unfold blockB27_41; decide
lemma length_blockC27_41 : blockC27_41.length = 27 := by unfold blockC27_41; decide
lemma length_blockD27_41 : blockD27_41.length = 27 := by unfold blockD27_41; decide
lemma length_blockE27_41 : blockE27_41.length = 27 := by unfold blockE27_41; decide
lemma length_blockF27_41 : blockF27_41.length = 27 := by unfold blockF27_41; decide
lemma length_conn1_41 : conn1_41.length = 10 := by unfold conn1_41; decide
lemma length_conn2_41 : conn2_41.length = 10 := by unfold conn2_41; decide
lemma length_conn3_41 : conn3_41.length = 10 := by unfold conn3_41; decide
lemma length_conn4_41 : conn4_41.length = 9 := by unfold conn4_41; decide
lemma length_conn5_41 : conn5_41.length = 9 := by unfold conn5_41; decide
lemma length_conn6_41 : conn6_41.length = 9 := by unfold conn6_41; decide

lemma hexEval_digits_216s41_eq (s : ℕ) :
    hexEval (digits_216s41 s) =
      9
        + 16 * (2275 * ∑ i ∈ Finset.range (18 * s + 2), 16 ^ (3 * i))
        + 16 ^ (54 * s + 7) * 52451
        + 16 ^ (54 * s + 11) * (3432 * ∑ i ∈ Finset.range (18 * s + 2), 16 ^ (3 * i))
        + 16 ^ (108 * s + 17) * 49000
        + 16 ^ (108 * s + 21) * (216231233813322076505602018648517 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (162 * s + 21) * 360753013189
        + 16 ^ (162 * s + 31) * (136561070375486097020213450634029 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (216 * s + 31) * 558630564653
        + 16 ^ (216 * s + 41) * (144802811420779474208357095601045 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (270 * s + 41) * 53569680277
        + 16 ^ (270 * s + 51) * (23923942756476608782250302751477 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (324 * s + 51) * 27972584181
        + 16 ^ (324 * s + 60) * (100846859179214795871590989110293 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (378 * s + 60) * 44261645333
        + 16 ^ (378 * s + 69) * (274953638761037388971125489038506 *
            ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i))
        + 16 ^ (432 * s + 69) * 12410713258 := by
  unfold digits_216s41
  repeat rw [hexEval_append]
  rw [hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_3e8, hexEval_3ecc, hexEval_86d, hexEval_86fb,
    hexEval_blockA27_41, hexEval_blockB27_41, hexEval_blockC27_41,
    hexEval_blockD27_41, hexEval_blockE27_41, hexEval_blockF27_41,
    hexEval_conn1_41, hexEval_conn2_41, hexEval_conn3_41,
    hexEval_conn4_41, hexEval_conn5_41, hexEval_conn6_41]
  simp only [List.length_cons, List.length_nil, List.length_append,
    length_flatten_replicate, length_blockA27_41, length_blockB27_41,
    length_blockC27_41, length_blockD27_41, length_blockE27_41, length_blockF27_41,
    length_conn1_41, length_conn2_41, length_conn3_41, length_conn4_41,
    length_conn5_41, length_conn6_41]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f4 : (0 + 1 + 1 + 1 + 1 : ℕ) = 4 := rfl
  rw [f1, f3, f4]
  have e1 : 1 + (18 * s + 2) * 3 = 54 * s + 7 := by omega
  rw [e1]
  have e2 : 54 * s + 7 + 4 = 54 * s + 11 := by omega
  rw [e2]
  have e3 : 54 * s + 11 + (18 * s + 2) * 3 = 108 * s + 17 := by omega
  rw [e3]
  have e4 : 108 * s + 17 + 4 = 108 * s + 21 := by omega
  rw [e4]
  have e5 : 108 * s + 21 + (2 * s) * 27 = 162 * s + 21 := by omega
  rw [e5]
  have e6 : 162 * s + 21 + 10 = 162 * s + 31 := by omega
  rw [e6]
  have e7 : 162 * s + 31 + (2 * s) * 27 = 216 * s + 31 := by omega
  rw [e7]
  have e8 : 216 * s + 31 + 10 = 216 * s + 41 := by omega
  rw [e8]
  have e9 : 216 * s + 41 + (2 * s) * 27 = 270 * s + 41 := by omega
  rw [e9]
  have e10 : 270 * s + 41 + 10 = 270 * s + 51 := by omega
  rw [e10]
  have e11 : 270 * s + 51 + (2 * s) * 27 = 324 * s + 51 := by omega
  rw [e11]
  have e12 : 324 * s + 51 + 9 = 324 * s + 60 := by omega
  rw [e12]
  have e13 : 324 * s + 60 + (2 * s) * 27 = 378 * s + 60 := by omega
  rw [e13]
  have e14 : 378 * s + 60 + 9 = 378 * s + 69 := by omega
  rw [e14]
  have e15 : 378 * s + 69 + (2 * s) * 27 = 432 * s + 69 := by omega
  rw [e15]
  simp [hexEval_singleton]

lemma poly_id_216s41 (U : ℤ) :
    25515
      + 25200 * (16777216 * U - 1)
      + 39915972471029760 * U
      + 41799034041532416 * U * (16777216 * U - 1)
      + 41000471247989797803786240000 * U ^ 2
      + 36538573972032552176319463424 * U ^ 2 * (U - 1)
      + 19782567954231418133487101974210978775040 * U ^ 3
      + 25372303983542474181987869166631217266688 * U ^ 3 * (U - 1)
      + 33681949421607282711803353641201560137201447159726080 * U ^ 4
      + 29580793139577475064442581014177568317836074669834240 * U ^ 4 * (U - 1)
      + 3551333077782787715808158749009526770559891047942136091346206720 * U ^ 5
      + 5373600820002063481412321236788847742834246811209659241247801344 * U ^ 5 * (U - 1)
      + 2038941512748881915519123252375915646028127569251630030861123897050435420160 * U ^ 6
      + 1556592264069756594362885098154511212444013313147420302105135063338798022656 * U ^ 6 * (U - 1)
      + 221707087323704737954613833521871210122410169294381409549715670959347316485705621831680 * U ^ 7
      + 291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 * U ^ 7 * (U - 1)
      + 4271974071550176997344655835567320010443528268853614213181380770016511113549228094229492248084480 * U ^ 8
    =
      (2199023255552 * U - 1) * (1099511627776 * U - 1) *
        (2199023255552 * U - 3) * (549755813888 * U - 1) *
        (2199023255552 * U - 5) * (1099511627776 * U - 3) *
        (2199023255552 * U - 7) * (274877906944 * U - 1) := by
  ring

lemma dist_216s41 (G H U p7 p11 p17 p21 p31 p41 p51 p60 p69 : ℕ) :
    (9 + 16 * (2275 * G) + p7 * U * 52451 + p11 * U * (3432 * G)
      + p17 * (U * U) * 49000 + p21 * (U * U) * (216231233813322076505602018648517 * H)
      + p21 * (U * U * U) * 360753013189
      + p31 * (U * U * U) * (136561070375486097020213450634029 * H)
      + p31 * (U * U * U * U) * 558630564653
      + p41 * (U * U * U * U) * (144802811420779474208357095601045 * H)
      + p41 * (U * U * U * U * U) * 53569680277
      + p51 * (U * U * U * U * U) * (23923942756476608782250302751477 * H)
      + p51 * (U * U * U * U * U * U) * 27972584181
      + p60 * (U * U * U * U * U * U) * (100846859179214795871590989110293 * H)
      + p60 * (U * U * U * U * U * U * U) * 44261645333
      + p69 * (U * U * U * U * U * U * U) * (274953638761037388971125489038506 * H)
      + p69 * (U * U * U * U * U * U * U * U) * 12410713258) * 2835
    =
      25515
        + 2835 * 16 * 2275 * G
        + 2835 * p7 * 52451 * U
        + 2835 * p11 * 3432 * G * U
        + 2835 * p17 * 49000 * (U * U)
        + 2835 * p21 * 216231233813322076505602018648517 * H * (U * U)
        + 2835 * p21 * 360753013189 * (U * U * U)
        + 2835 * p31 * 136561070375486097020213450634029 * H * (U * U * U)
        + 2835 * p31 * 558630564653 * (U * U * U * U)
        + 2835 * p41 * 144802811420779474208357095601045 * H * (U * U * U * U)
        + 2835 * p41 * 53569680277 * (U * U * U * U * U)
        + 2835 * p51 * 23923942756476608782250302751477 * H * (U * U * U * U * U)
        + 2835 * p51 * 27972584181 * (U * U * U * U * U * U)
        + 2835 * p60 * 100846859179214795871590989110293 * H * (U * U * U * U * U * U)
        + 2835 * p60 * 44261645333 * (U * U * U * U * U * U * U)
        + 2835 * p69 * 274953638761037388971125489038506 * H * (U * U * U * U * U * U * U)
        + 2835 * p69 * 12410713258 * (U * U * U * U * U * U * U * U) := by
  ring

lemma hexEval_digits_216s41_mul_2835 (s : ℕ) :
    hexEval (digits_216s41 s) * 2835 =
      (2199023255552 * 16 ^ (54 * s) - 1) * (1099511627776 * 16 ^ (54 * s) - 1) *
        (2199023255552 * 16 ^ (54 * s) - 3) * (549755813888 * 16 ^ (54 * s) - 1) *
        (2199023255552 * 16 ^ (54 * s) - 5) * (1099511627776 * 16 ^ (54 * s) - 3) *
        (2199023255552 * 16 ^ (54 * s) - 7) * (274877906944 * 16 ^ (54 * s) - 1) := by
  have hex := hexEval_digits_216s41_eq s
  set G := ∑ i ∈ Finset.range (18 * s + 2), 16 ^ (3 * i) with hGdef
  set H := ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i) with hHdef
  set U := 16 ^ (54 * s) with hUdef
  set p7 := 16 ^ 7 with hp7
  set p11 := 16 ^ 11 with hp11
  set p17 := 16 ^ 17 with hp17
  set p21 := 16 ^ 21 with hp21
  set p31 := 16 ^ 31 with hp31
  set p41 := 16 ^ 41 with hp41
  set p51 := 16 ^ 51 with hp51
  set p60 := 16 ^ 60 with hp60
  set p69 := 16 ^ 69 with hp69
  have hGpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hG : G * 4095 = 16777216 * U - 1 := by
    rw [hGdef, hUdef]
    have : ∑ i ∈ Finset.range (18 * s + 2), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (18 * s + 2), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hGpow i
    rw [this]
    have hpow : 16 ^ (54 * s + 6) = 4096 ^ (18 * s + 2) := by
      have : 54 * s + 6 = 3 * (18 * s + 2) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    have : 16 ^ (54 * s + 6) = 16777216 * 16 ^ (54 * s) := by
      have : 54 * s + 6 = 6 + 54 * s := by omega
      rw [this, pow_add, show (16 : ℕ) ^ 6 = 16777216 from rfl]
    have hgs := geom_sum_4096 (18 * s + 2)
    have hle : 1 ≤ 4096 ^ (18 * s + 2) := Nat.one_le_pow _ _ (by decide)
    omega
  have hHpow : ∀ i, 16 ^ (27 * i) = (16 ^ 27) ^ i := by
    intro i; rw [← pow_mul]
  have hH : H * (16 ^ 27 - 1) = U - 1 := by
    rw [hHdef, hUdef]
    have : ∑ i ∈ Finset.range (2 * s), 16 ^ (27 * i) =
        ∑ i ∈ Finset.range (2 * s), (16 ^ 27) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (54 * s) = (16 ^ 27) ^ (2 * s) := by
      have : 54 * s = 27 * (2 * s) := by omega
      rw [this, ← pow_mul]
    rw [this]
    exact geom_sum_16_pow_27 (2 * s)
  have hU1 : 1 ≤ U := by
    rw [hUdef]; exact Nat.one_le_pow _ _ (by decide)
  have pw7 : 16 ^ (54 * s + 7) = p7 * U := by
    have : 54 * s + 7 = 7 + 54 * s := by omega
    rw [this, pow_add, hp7, hUdef]
  have pw11 : 16 ^ (54 * s + 11) = p11 * U := by
    have : 54 * s + 11 = 11 + 54 * s := by omega
    rw [this, pow_add, hp11, hUdef]
  have pw17 : 16 ^ (108 * s + 17) = p17 * (U * U) := by
    have : 108 * s + 17 = 17 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp17, hUdef, pow_add]
  have pw21a : 16 ^ (108 * s + 21) = p21 * (U * U) := by
    have : 108 * s + 21 = 21 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp21, hUdef, pow_add]
  have pw21b : 16 ^ (162 * s + 21) = p21 * (U * U * U) := by
    have : 162 * s + 21 = 21 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp21, hUdef, pow_add, pow_add]
  have pw31a : 16 ^ (162 * s + 31) = p31 * (U * U * U) := by
    have : 162 * s + 31 = 31 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp31, hUdef, pow_add, pow_add]
  have pw31b : 16 ^ (216 * s + 31) = p31 * (U * U * U * U) := by
    have : 216 * s + 31 = 31 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp31, hUdef, pow_add, pow_add, pow_add]
  have pw41a : 16 ^ (216 * s + 41) = p41 * (U * U * U * U) := by
    have : 216 * s + 41 = 41 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp41, hUdef, pow_add, pow_add, pow_add]
  have pw41b : 16 ^ (270 * s + 41) = p41 * (U * U * U * U * U) := by
    have : 270 * s + 41 = 41 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp41, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw51a : 16 ^ (270 * s + 51) = p51 * (U * U * U * U * U) := by
    have : 270 * s + 51 = 51 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp51, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw51b : 16 ^ (324 * s + 51) = p51 * (U * U * U * U * U * U) := by
    have : 324 * s + 51 = 51 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp51, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw60a : 16 ^ (324 * s + 60) = p60 * (U * U * U * U * U * U) := by
    have : 324 * s + 60 = 60 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp60, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw60b : 16 ^ (378 * s + 60) = p60 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 60 = 60 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp60, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw69a : 16 ^ (378 * s + 69) = p69 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 69 = 69 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp69, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw69b : 16 ^ (432 * s + 69) = p69 * (U * U * U * U * U * U * U * U) := by
    have : 432 * s + 69 = 69 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp69, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factG0 : (2835 * 16 * 2275 : ℕ) = 4095 * 25200 := by decide
  have factG1 : (2835 * p11 * 3432 : ℕ) = 4095 * 41799034041532416 := by
    rw [hp11]; decide
  have factHA : (2835 * p21 * 216231233813322076505602018648517 : ℕ) =
      (16 ^ 27 - 1) * 36538573972032552176319463424 := by
    rw [hp21]; decide
  have factHB : (2835 * p31 * 136561070375486097020213450634029 : ℕ) =
      (16 ^ 27 - 1) * 25372303983542474181987869166631217266688 := by
    rw [hp31]; decide
  have factHC : (2835 * p41 * 144802811420779474208357095601045 : ℕ) =
      (16 ^ 27 - 1) * 29580793139577475064442581014177568317836074669834240 := by
    rw [hp41]; decide
  have factHD : (2835 * p51 * 23923942756476608782250302751477 : ℕ) =
      (16 ^ 27 - 1) * 5373600820002063481412321236788847742834246811209659241247801344 := by
    rw [hp51]; decide
  have factHE : (2835 * p60 * 100846859179214795871590989110293 : ℕ) =
      (16 ^ 27 - 1) * 1556592264069756594362885098154511212444013313147420302105135063338798022656 := by
    rw [hp60]; decide
  have factHF : (2835 * p69 * 274953638761037388971125489038506 : ℕ) =
      (16 ^ 27 - 1) * 291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 := by
    rw [hp69]; decide
  have factC1 : (2835 * p7 * 52451 : ℕ) = 39915972471029760 := by
    rw [hp7]; decide
  have factC2 : (2835 * p17 * 49000 : ℕ) = 41000471247989797803786240000 := by
    rw [hp17]; decide
  have factC3 : (2835 * p21 * 360753013189 : ℕ) = 19782567954231418133487101974210978775040 := by
    rw [hp21]; decide
  have factC4 : (2835 * p31 * 558630564653 : ℕ) = 33681949421607282711803353641201560137201447159726080 := by
    rw [hp31]; decide
  have factC5 : (2835 * p41 * 53569680277 : ℕ) = 3551333077782787715808158749009526770559891047942136091346206720 := by
    rw [hp41]; decide
  have factC6 : (2835 * p51 * 27972584181 : ℕ) = 2038941512748881915519123252375915646028127569251630030861123897050435420160 := by
    rw [hp51]; decide
  have factC7 : (2835 * p60 * 44261645333 : ℕ) = 221707087323704737954613833521871210122410169294381409549715670959347316485705621831680 := by
    rw [hp60]; decide
  have factC8 : (2835 * p69 * 12410713258 : ℕ) = 4271974071550176997344655835567320010443528268853614213181380770016511113549228094229492248084480 := by
    rw [hp69]; decide
  have hex2835 :
      hexEval (digits_216s41 s) * 2835 =
        25515 + 25200 * (16777216 * U - 1) + 39915972471029760 * U
          + 41799034041532416 * U * (16777216 * U - 1) + 41000471247989797803786240000 * (U * U)
          + 36538573972032552176319463424 * (U * U) * (U - 1)
          + 19782567954231418133487101974210978775040 * (U * U * U)
          + 25372303983542474181987869166631217266688 * (U * U * U) * (U - 1)
          + 33681949421607282711803353641201560137201447159726080 * (U * U * U * U)
          + 29580793139577475064442581014177568317836074669834240 * (U * U * U * U) * (U - 1)
          + 3551333077782787715808158749009526770559891047942136091346206720 * (U * U * U * U * U)
          + 5373600820002063481412321236788847742834246811209659241247801344 * (U * U * U * U * U) * (U - 1)
          + 2038941512748881915519123252375915646028127569251630030861123897050435420160 * (U * U * U * U * U * U)
          + 1556592264069756594362885098154511212444013313147420302105135063338798022656 * (U * U * U * U * U * U) * (U - 1)
          + 221707087323704737954613833521871210122410169294381409549715670959347316485705621831680 * (U * U * U * U * U * U * U)
          + 291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 * (U * U * U * U * U * U * U) * (U - 1)
          + 4271974071550176997344655835567320010443528268853614213181380770016511113549228094229492248084480 * (U * U * U * U * U * U * U * U) := by
    rw [hex, pw7, pw11, pw17, pw21a, pw21b, pw31a, pw31b, pw41a, pw41b,
      pw51a, pw51b, pw60a, pw60b, pw69a, pw69b]
    rw [dist_216s41 G H U p7 p11 p17 p21 p31 p41 p51 p60 p69]
    have G0 : 2835 * 16 * 2275 * G = 25200 * (16777216 * U - 1) := by
      rw [factG0]
      have : 4095 * 25200 * G = 25200 * (G * 4095) := by ring
      rw [this, hG]
    have G1 : 2835 * p11 * 3432 * G * U = 41799034041532416 * U * (16777216 * U - 1) := by
      rw [factG1]
      have : 4095 * 41799034041532416 * G * U = 41799034041532416 * U * (G * 4095) := by ring
      rw [this, hG]
    have HA : 2835 * p21 * 216231233813322076505602018648517 * H * (U * U) =
        36538573972032552176319463424 * (U * U) * (U - 1) := by
      rw [factHA]
      have : (16 ^ 27 - 1) * 36538573972032552176319463424 * H * (U * U) =
          36538573972032552176319463424 * (U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HB : 2835 * p31 * 136561070375486097020213450634029 * H * (U * U * U) =
        25372303983542474181987869166631217266688 * (U * U * U) * (U - 1) := by
      rw [factHB]
      have : (16 ^ 27 - 1) * 25372303983542474181987869166631217266688 * H * (U * U * U) =
          25372303983542474181987869166631217266688 * (U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HC : 2835 * p41 * 144802811420779474208357095601045 * H * (U * U * U * U) =
        29580793139577475064442581014177568317836074669834240 * (U * U * U * U) * (U - 1) := by
      rw [factHC]
      have : (16 ^ 27 - 1) * 29580793139577475064442581014177568317836074669834240 * H * (U * U * U * U) =
          29580793139577475064442581014177568317836074669834240 * (U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HD : 2835 * p51 * 23923942756476608782250302751477 * H * (U * U * U * U * U) =
        5373600820002063481412321236788847742834246811209659241247801344 * (U * U * U * U * U) * (U - 1) := by
      rw [factHD]
      have : (16 ^ 27 - 1) * 5373600820002063481412321236788847742834246811209659241247801344 * H * (U * U * U * U * U) =
          5373600820002063481412321236788847742834246811209659241247801344 * (U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HE : 2835 * p60 * 100846859179214795871590989110293 * H * (U * U * U * U * U * U) =
        1556592264069756594362885098154511212444013313147420302105135063338798022656 * (U * U * U * U * U * U) * (U - 1) := by
      rw [factHE]
      have : (16 ^ 27 - 1) * 1556592264069756594362885098154511212444013313147420302105135063338798022656 * H * (U * U * U * U * U * U) =
          1556592264069756594362885098154511212444013313147420302105135063338798022656 * (U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HF : 2835 * p69 * 274953638761037388971125489038506 * H * (U * U * U * U * U * U * U) =
        291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 * (U * U * U * U * U * U * U) * (U - 1) := by
      rw [factHF]
      have : (16 ^ 27 - 1) * 291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 * H * (U * U * U * U * U * U * U) =
          291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 * (U * U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have C1 : 2835 * p7 * 52451 * U = 39915972471029760 * U := by rw [factC1]
    have C2 : 2835 * p17 * 49000 * (U * U) = 41000471247989797803786240000 * (U * U) := by rw [factC2]
    have C3 : 2835 * p21 * 360753013189 * (U * U * U) = 19782567954231418133487101974210978775040 * (U * U * U) := by
      rw [factC3]
    have C4 : 2835 * p31 * 558630564653 * (U * U * U * U) =
        33681949421607282711803353641201560137201447159726080 * (U * U * U * U) := by rw [factC4]
    have C5 : 2835 * p41 * 53569680277 * (U * U * U * U * U) =
        3551333077782787715808158749009526770559891047942136091346206720 * (U * U * U * U * U) := by rw [factC5]
    have C6 : 2835 * p51 * 27972584181 * (U * U * U * U * U * U) =
        2038941512748881915519123252375915646028127569251630030861123897050435420160 * (U * U * U * U * U * U) := by rw [factC6]
    have C7 : 2835 * p60 * 44261645333 * (U * U * U * U * U * U * U) =
        221707087323704737954613833521871210122410169294381409549715670959347316485705621831680 * (U * U * U * U * U * U * U) := by rw [factC7]
    have C8 : 2835 * p69 * 12410713258 * (U * U * U * U * U * U * U * U) =
        4271974071550176997344655835567320010443528268853614213181380770016511113549228094229492248084480 * (U * U * U * U * U * U * U * U) := by rw [factC8]
    rw [G0, G1, HA, HB, HC, HD, HE, HF, C1, C2, C3, C4, C5, C6, C7, C8]
  have hex2835' :
      hexEval (digits_216s41 s) * 2835 =
        25515 + 25200 * (16777216 * U - 1) + 39915972471029760 * U
          + 41799034041532416 * U * (16777216 * U - 1) + 41000471247989797803786240000 * U ^ 2
          + 36538573972032552176319463424 * U ^ 2 * (U - 1)
          + 19782567954231418133487101974210978775040 * U ^ 3
          + 25372303983542474181987869166631217266688 * U ^ 3 * (U - 1)
          + 33681949421607282711803353641201560137201447159726080 * U ^ 4
          + 29580793139577475064442581014177568317836074669834240 * U ^ 4 * (U - 1)
          + 3551333077782787715808158749009526770559891047942136091346206720 * U ^ 5
          + 5373600820002063481412321236788847742834246811209659241247801344 * U ^ 5 * (U - 1)
          + 2038941512748881915519123252375915646028127569251630030861123897050435420160 * U ^ 6
          + 1556592264069756594362885098154511212444013313147420302105135063338798022656 * U ^ 6 * (U - 1)
          + 221707087323704737954613833521871210122410169294381409549715670959347316485705621831680 * U ^ 7
          + 291643167445387576771784218761880775859691326712702445627928338012053005816431925788672 * U ^ 7 * (U - 1)
          + 4271974071550176997344655835567320010443528268853614213181380770016511113549228094229492248084480 * U ^ 8 := by
    rw [hex2835]
    ring
  rw [hex2835']
  have hR :
      (2199023255552 * 16 ^ (54 * s) - 1) * (1099511627776 * 16 ^ (54 * s) - 1) *
        (2199023255552 * 16 ^ (54 * s) - 3) * (549755813888 * 16 ^ (54 * s) - 1) *
        (2199023255552 * 16 ^ (54 * s) - 5) * (1099511627776 * 16 ^ (54 * s) - 3) *
        (2199023255552 * 16 ^ (54 * s) - 7) * (274877906944 * 16 ^ (54 * s) - 1) =
      (2199023255552 * U - 1) * (1099511627776 * U - 1) *
        (2199023255552 * U - 3) * (549755813888 * U - 1) *
        (2199023255552 * U - 5) * (1099511627776 * U - 3) *
        (2199023255552 * U - 7) * (274877906944 * U - 1) := by
    rw [hUdef]
  rw [hR]
  have hA : 1 ≤ 2199023255552 * U := one_le_mul (by decide : 1 ≤ 2199023255552) hU1
  have hB : 1 ≤ 1099511627776 * U := one_le_mul (by decide : 1 ≤ 1099511627776) hU1
  have hC : 1 ≤ 549755813888 * U := one_le_mul (by decide : 1 ≤ 549755813888) hU1
  have hD : 1 ≤ 274877906944 * U := one_le_mul (by decide : 1 ≤ 274877906944) hU1
  have hA3 : 3 ≤ 2199023255552 * U :=
    (by decide : 3 ≤ 2199023255552).trans (Nat.le_mul_of_pos_right 2199023255552 hU1)
  have hA5 : 5 ≤ 2199023255552 * U :=
    (by decide : 5 ≤ 2199023255552).trans (Nat.le_mul_of_pos_right 2199023255552 hU1)
  have hA7 : 7 ≤ 2199023255552 * U :=
    (by decide : 7 ≤ 2199023255552).trans (Nat.le_mul_of_pos_right 2199023255552 hU1)
  have hB3 : 3 ≤ 1099511627776 * U :=
    (by decide : 3 ≤ 1099511627776).trans (Nat.le_mul_of_pos_right 1099511627776 hU1)
  have h16U : 1 ≤ 16777216 * U := one_le_mul (by decide : 1 ≤ 16777216) hU1
  zify [hU1, hA, hB, hC, hD, hA3, hA5, hA7, hB3, h16U]
  simpa using poly_id_216s41 (U : ℤ)

lemma popc_choose_two_pow_nine_of_mod_216_eq_fortyone {m : ℕ}
    (hmod : m % 216 = 41) :
    popc (Nat.choose (2 ^ m) 9) % 2 = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m = 216 * s + 41 := ⟨m / 216, by omega⟩
  have hm9 : 9 ≤ m := by omega
  rw [choose_two_pow_nine m hm9, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) / 2835 =
        hexEval (digits_216s41 s) := by
    set U := 16 ^ (54 * s) with hUdef
    have h16 : 16 ^ (54 * s) = 2 ^ (216 * s) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 2199023255552 * U := by
      rw [hs, hUdef, pow_add, h16, show (2 : ℕ) ^ 41 = 2199023255552 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 1099511627776 * U := by
      have : m - 1 = 216 * s + 40 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 40 = 1099511627776 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 549755813888 * U := by
      have : m - 2 = 216 * s + 39 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 39 = 549755813888 from rfl]
      ring
    have h2m3 : 2 ^ (m - 3) = 274877906944 * U := by
      have : m - 3 = 216 * s + 38 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 38 = 274877906944 from rfl]
      ring
    have hmul := hexEval_digits_216s41_mul_2835 s
    rw [h2m, h2m1, h2m2, h2m3]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2835) hmul.symm
  rw [hex, popc_hexEval_digits_216s41 s]
  omega

lemma a_ne_zero_two_pow_mod216_eq_fortyone {m : ℕ} (hm : 41 ≤ m) (hmod : m % 216 = 41) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 9 (by decide) ?_
    (popc_choose_two_pow_nine_of_mod_216_eq_fortyone hmod)
  have : 9 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 9 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  exact this


/- Digit list for the odd part of `C(2^{216s+65}, 9)`, `s ≥ 0`. LSB first. -/

def blockA27_65 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 14, 3, 5, 5, 0, 7, 12, 12, 8, 3, 9, 10, 10]
def blockB27_65 : List ℕ := [0, 1, 12, 2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 13, 9, 4, 10, 11, 11, 6, 13, 2, 3, 15, 9, 15]
def blockC27_65 : List ℕ := [1, 11, 10, 3, 2, 7, 5, 9, 3, 7, 0, 0, 9, 7, 12, 10, 14, 8, 12, 5, 5, 14, 12, 1, 0, 4, 14]
def blockD27_65 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10, 8, 13, 11, 15, 9, 13, 6, 6, 15, 13, 2, 1]
def blockE27_65 : List ℕ := [3, 10, 15, 15, 11, 6, 12, 13, 13, 8, 15, 4, 5, 1, 12, 1, 3, 3, 14, 4, 10, 10, 6, 1, 7, 8, 8]
def blockF27_65 : List ℕ := [1, 7, 6, 14, 8, 13, 10, 10, 4, 7, 12, 11, 3, 14, 2, 0, 0, 10, 12, 1, 1, 9, 3, 8, 5, 5, 15]
def conn1_65 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 2, 14]
def conn2_65 : List ℕ := [0, 1, 12, 2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 3, 15]
def conn3_65 : List ℕ := [1, 11, 10, 3, 2, 7, 5, 9, 3, 7, 0, 0, 9, 7, 12, 0]
def conn4_65 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10]
def conn5_65 : List ℕ := [3, 10, 15, 15, 11, 6, 12, 13, 13, 8, 15, 4, 5, 1, 12]
def conn6_65 : List ℕ := [1, 7, 6, 14, 8, 13, 10, 10, 4, 7, 12, 11, 3, 14, 2]

def digits_216s65 (s : ℕ) : List ℕ :=
  [9]
    ++ List.flatten (List.replicate (18 * s + 4) [3, 14, 8])
    ++ [3, 14, 12, 12]
    ++ List.flatten (List.replicate (18 * s + 4) [8, 6, 13])
    ++ [8, 6, 15, 11]
    ++ List.flatten (List.replicate (2 * s + 0) blockA27_65)
    ++ conn1_65
    ++ List.flatten (List.replicate (2 * s + 0) blockB27_65)
    ++ conn2_65
    ++ List.flatten (List.replicate (2 * s + 0) blockC27_65)
    ++ conn3_65
    ++ List.flatten (List.replicate (2 * s + 0) blockD27_65)
    ++ conn4_65
    ++ List.flatten (List.replicate (2 * s + 0) blockE27_65)
    ++ conn5_65
    ++ List.flatten (List.replicate (2 * s + 0) blockF27_65)
    ++ conn6_65

lemma digits_216s65_lt (s : ℕ) : ∀ d ∈ digits_216s65 s, d < 16 := by
  intro d hd
  unfold digits_216s65 blockA27_65 blockB27_65 blockC27_65 blockD27_65
    blockE27_65 blockF27_65 conn1_65 conn2_65 conn3_65 conn4_65
    conn5_65 conn6_65 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten] at hd
  aesop

lemma popc_blockA27_65 : (List.map popc blockA27_65).sum = 57 := by
  unfold blockA27_65; decide

lemma popc_blockB27_65 : (List.map popc blockB27_65).sum = 53 := by
  unfold blockB27_65; decide

lemma popc_blockC27_65 : (List.map popc blockC27_65).sum = 50 := by
  unfold blockC27_65; decide

lemma popc_blockD27_65 : (List.map popc blockD27_65).sum = 55 := by
  unfold blockD27_65; decide

lemma popc_blockE27_65 : (List.map popc blockE27_65).sum = 57 := by
  unfold blockE27_65; decide

lemma popc_blockF27_65 : (List.map popc blockF27_65).sum = 51 := by
  unfold blockF27_65; decide

lemma popc_conn1_65 : (List.map popc conn1_65).sum = 36 := by
  unfold conn1_65; decide

lemma popc_conn2_65 : (List.map popc conn2_65).sum = 27 := by
  unfold conn2_65; decide

lemma popc_conn3_65 : (List.map popc conn3_65).sum = 28 := by
  unfold conn3_65; decide

lemma popc_conn4_65 : (List.map popc conn4_65).sum = 26 := by
  unfold conn4_65; decide

lemma popc_conn5_65 : (List.map popc conn5_65).sum = 36 := by
  unfold conn5_65; decide

lemma popc_conn6_65 : (List.map popc conn6_65).sum = 32 := by
  unfold conn6_65; decide

lemma popc_digits_216s65 (s : ℕ) :
    (List.map popc (digits_216s65 s)).sum = 254 + 862 * s := by
  have h0 : popc 0 = 0 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h3 : popc 3 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h5 : popc 5 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h7 : popc 7 = 3 := by decide
  have h8 : popc 8 = 1 := by decide
  have h9 : popc 9 = 2 := by decide
  have h10 : popc 10 = 2 := by decide
  have h11 : popc 11 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h13 : popc 13 = 3 := by decide
  have h14 : popc 14 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  unfold digits_216s65
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_flatten_replicate]
  rw [popc_blockA27_65, popc_blockB27_65, popc_blockC27_65, popc_blockD27_65,
    popc_blockE27_65, popc_blockF27_65, popc_conn1_65, popc_conn2_65,
    popc_conn3_65, popc_conn4_65, popc_conn5_65, popc_conn6_65]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

lemma popc_hexEval_digits_216s65 (s : ℕ) :
    popc (hexEval (digits_216s65 s)) = 254 + 862 * s := by
  rw [popc_hexEval _ (digits_216s65_lt s), popc_digits_216s65 s]

lemma hexEval_blockA27_65 : hexEval blockA27_65 = 216231233813322076505602018648517 := by
  unfold blockA27_65; decide

lemma hexEval_blockB27_65 : hexEval blockB27_65 = 316849155741278723010855684287504 := by
  unfold blockB27_65; decide

lemma hexEval_blockC27_65 : hexEval blockC27_65 = 289033279713413575000870882523825 := by
  unfold blockC27_65; decide

lemma hexEval_blockD27_65 : hexEval blockD27_65 = 23923942756476608782250302751477 := by
  unfold blockD27_65; decide

lemma hexEval_blockE27_65 : hexEval blockE27_65 = 172962093325531846267847882571683 := by
  unfold blockE27_65; decide

lemma hexEval_blockF27_65 : hexEval blockF27_65 = 311011255834195914169253935769201 := by
  unfold blockF27_65; decide

lemma hexEval_conn1_65 : hexEval conn1_65 = 16300622376994742725 := by
  unfold conn1_65; decide

lemma hexEval_conn2_65 : hexEval conn2_65 = 17570818569041095696 := by
  unfold conn2_65; decide

lemma hexEval_conn3_65 : hexEval conn3_65 = 898750097065654961 := by
  unfold conn3_65; decide

lemma hexEval_conn4_65 : hexEval conn4_65 = 725506865685578485 := by
  unfold conn4_65; decide

lemma hexEval_conn5_65 : hexEval conn5_65 = 870689573673107363 := by
  unfold conn5_65; decide

lemma hexEval_conn6_65 : hexEval conn6_65 = 208217217057744497 := by
  unfold conn6_65; decide

lemma length_blockA27_65 : blockA27_65.length = 27 := by unfold blockA27_65; decide
lemma length_blockB27_65 : blockB27_65.length = 27 := by unfold blockB27_65; decide
lemma length_blockC27_65 : blockC27_65.length = 27 := by unfold blockC27_65; decide
lemma length_blockD27_65 : blockD27_65.length = 27 := by unfold blockD27_65; decide
lemma length_blockE27_65 : blockE27_65.length = 27 := by unfold blockE27_65; decide
lemma length_blockF27_65 : blockF27_65.length = 27 := by unfold blockF27_65; decide
lemma length_conn1_65 : conn1_65.length = 16 := by unfold conn1_65; decide
lemma length_conn2_65 : conn2_65.length = 16 := by unfold conn2_65; decide
lemma length_conn3_65 : conn3_65.length = 16 := by unfold conn3_65; decide
lemma length_conn4_65 : conn4_65.length = 15 := by unfold conn4_65; decide
lemma length_conn5_65 : conn5_65.length = 15 := by unfold conn5_65; decide
lemma length_conn6_65 : conn6_65.length = 15 := by unfold conn6_65; decide

lemma hexEval_digits_216s65_eq (s : ℕ) :
    hexEval (digits_216s65 s) =
      9
        + 16 * (2275 * ∑ i ∈ Finset.range (18 * s + 4), 16 ^ (3 * i))
        + 16 ^ (54 * s + 13) * 52451
        + 16 ^ (54 * s + 17) * (3432 * ∑ i ∈ Finset.range (18 * s + 4), 16 ^ (3 * i))
        + 16 ^ (108 * s + 29) * 49000
        + 16 ^ (108 * s + 33) * (216231233813322076505602018648517 *
            ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i))
        + 16 ^ (162 * s + 33) * 16300622376994742725
        + 16 ^ (162 * s + 49) * (316849155741278723010855684287504 *
            ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i))
        + 16 ^ (216 * s + 49) * 17570818569041095696
        + 16 ^ (216 * s + 65) * (289033279713413575000870882523825 *
            ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i))
        + 16 ^ (270 * s + 65) * 898750097065654961
        + 16 ^ (270 * s + 81) * (23923942756476608782250302751477 *
            ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i))
        + 16 ^ (324 * s + 81) * 725506865685578485
        + 16 ^ (324 * s + 96) * (172962093325531846267847882571683 *
            ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i))
        + 16 ^ (378 * s + 96) * 870689573673107363
        + 16 ^ (378 * s + 111) * (311011255834195914169253935769201 *
            ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i))
        + 16 ^ (432 * s + 111) * 208217217057744497 := by
  unfold digits_216s65
  repeat rw [hexEval_append]
  rw [hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_3e8, hexEval_3ecc, hexEval_86d, hexEval_86fb,
    hexEval_blockA27_65, hexEval_blockB27_65, hexEval_blockC27_65,
    hexEval_blockD27_65, hexEval_blockE27_65, hexEval_blockF27_65,
    hexEval_conn1_65, hexEval_conn2_65, hexEval_conn3_65,
    hexEval_conn4_65, hexEval_conn5_65, hexEval_conn6_65]
  simp only [List.length_cons, List.length_nil, List.length_append,
    length_flatten_replicate, length_blockA27_65, length_blockB27_65,
    length_blockC27_65, length_blockD27_65, length_blockE27_65,
    length_blockF27_65, length_conn1_65, length_conn2_65,
    length_conn3_65, length_conn4_65, length_conn5_65, length_conn6_65]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f4 : (0 + 1 + 1 + 1 + 1 : ℕ) = 4 := rfl
  rw [f1, f3, f4]
  have e1 : 1 + (18 * s + 4) * 3 = 54 * s + 13 := by omega
  rw [e1]
  have e2 : 54 * s + 13 + 4 = 54 * s + 17 := by omega
  rw [e2]
  have e3 : 54 * s + 17 + (18 * s + 4) * 3 = 108 * s + 29 := by omega
  rw [e3]
  have e4 : 108 * s + 29 + 4 = 108 * s + 33 := by omega
  rw [e4]
  have e5 : 108 * s + 33 + (2 * s + 0) * 27 = 162 * s + 33 := by omega
  rw [e5]
  have e6 : 162 * s + 33 + 16 = 162 * s + 49 := by omega
  rw [e6]
  have e7 : 162 * s + 49 + (2 * s + 0) * 27 = 216 * s + 49 := by omega
  rw [e7]
  have e8 : 216 * s + 49 + 16 = 216 * s + 65 := by omega
  rw [e8]
  have e9 : 216 * s + 65 + (2 * s + 0) * 27 = 270 * s + 65 := by omega
  rw [e9]
  have e10 : 270 * s + 65 + 16 = 270 * s + 81 := by omega
  rw [e10]
  have e11 : 270 * s + 81 + (2 * s + 0) * 27 = 324 * s + 81 := by omega
  rw [e11]
  have e12 : 324 * s + 81 + 15 = 324 * s + 96 := by omega
  rw [e12]
  have e13 : 324 * s + 96 + (2 * s + 0) * 27 = 378 * s + 96 := by omega
  rw [e13]
  have e14 : 378 * s + 96 + 15 = 378 * s + 111 := by omega
  rw [e14]
  have e15 : 378 * s + 111 + (2 * s + 0) * 27 = 432 * s + 111 := by omega
  rw [e15]
  simp [hexEval_singleton]

lemma poly_id_216s65 (U : ℤ) :
    25515
      + 25200 * (281474976710656 * U - 1)
      + 669678891996520025948160 * U
      + 701271422706142314233856 * U * (281474976710656 * U - 1)
      + 11540606689653849280277022361177754173440000 * U ^ 2
      + 10284694257818444119717034135017762423046144 * U ^ 2 * (U - 1)
      + 251603499584070478376354294245258646920309653556573016948736000 * U ^ 3
      + 278000281656805317668759441975021130236341117924423160507138048 * U ^ 3 * (U - 1)
      + 5002927481598638203717235643001690515028105174236728284722968188919472507857141760 * U ^ 4
      + 4678000405187574295112267794350991477272107380491878787194086393919690437453414400 * U ^ 4 * (U - 1)
      + 4720531349385211277414997565447135878159709200057211144310854572795226806781129221631055774676418560 * U ^ 5
      + 7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 * U ^ 5 * (U - 1)
      + 70293179054367750907563066890536683712733302273079374584388311510413720777648116594205548235704227503922239115991449600 * U ^ 6
      + 59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 * U ^ 6 * (U - 1)
      + 97260106794805896982094960680261548663443004985654747481941421240186004825404188281270654376903201882752578611307385401472283987075399680 * U ^ 7
      + 123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 * U ^ 7 * (U - 1)
      + 26815615859885194075721749126963947153551682514203016765519399325728329948596539505241439483577422000551245917041996624920522065359817799554522758953041920 * U ^ 8
    =
      (36893488147419103232 * U - 1) * (18446744073709551616 * U - 1) *
        (36893488147419103232 * U - 3) * (9223372036854775808 * U - 1) *
        (36893488147419103232 * U - 5) * (18446744073709551616 * U - 3) *
        (36893488147419103232 * U - 7) * (4611686018427387904 * U - 1) := by
  ring

lemma dist_216s65 (G H U p13 p17 p29 p33 p49 p65 p81 p96 p111 : ℕ) :
    (9 + 16 * (2275 * G) + p13 * U * 52451 + p17 * U * (3432 * G) + p29 * (U * U) * 49000 + p33 * (U * U) * (216231233813322076505602018648517 * H) + p33 * (U * U * U) * 16300622376994742725 + p49 * (U * U * U) * (316849155741278723010855684287504 * H) + p49 * (U * U * U * U) * 17570818569041095696 + p65 * (U * U * U * U) * (289033279713413575000870882523825 * H) + p65 * (U * U * U * U * U) * 898750097065654961 + p81 * (U * U * U * U * U) * (23923942756476608782250302751477 * H) + p81 * (U * U * U * U * U * U) * 725506865685578485 + p96 * (U * U * U * U * U * U) * (172962093325531846267847882571683 * H) + p96 * (U * U * U * U * U * U * U) * 870689573673107363 + p111 * (U * U * U * U * U * U * U) * (311011255834195914169253935769201 * H) + p111 * (U * U * U * U * U * U * U * U) * 208217217057744497) * 2835
    =
      25515
        + 2835 * 16 * 2275 * G
        + 2835 * p13 * 52451 * U
        + 2835 * p17 * 3432 * G * U
        + 2835 * p29 * 49000 * (U * U)
        + 2835 * p33 * 216231233813322076505602018648517 * H * (U * U)
        + 2835 * p33 * 16300622376994742725 * (U * U * U)
        + 2835 * p49 * 316849155741278723010855684287504 * H * (U * U * U)
        + 2835 * p49 * 17570818569041095696 * (U * U * U * U)
        + 2835 * p65 * 289033279713413575000870882523825 * H * (U * U * U * U)
        + 2835 * p65 * 898750097065654961 * (U * U * U * U * U)
        + 2835 * p81 * 23923942756476608782250302751477 * H * (U * U * U * U * U)
        + 2835 * p81 * 725506865685578485 * (U * U * U * U * U * U)
        + 2835 * p96 * 172962093325531846267847882571683 * H * (U * U * U * U * U * U)
        + 2835 * p96 * 870689573673107363 * (U * U * U * U * U * U * U)
        + 2835 * p111 * 311011255834195914169253935769201 * H * (U * U * U * U * U * U * U)
        + 2835 * p111 * 208217217057744497 * (U * U * U * U * U * U * U * U) := by
  ring

lemma hexEval_digits_216s65_mul_2835 (s : ℕ) :
    hexEval (digits_216s65 s) * 2835 =
      (36893488147419103232 * 16 ^ (54 * s) - 1) * (18446744073709551616 * 16 ^ (54 * s) - 1) *
        (36893488147419103232 * 16 ^ (54 * s) - 3) * (9223372036854775808 * 16 ^ (54 * s) - 1) *
        (36893488147419103232 * 16 ^ (54 * s) - 5) * (18446744073709551616 * 16 ^ (54 * s) - 3) *
        (36893488147419103232 * 16 ^ (54 * s) - 7) * (4611686018427387904 * 16 ^ (54 * s) - 1) := by
  have hex := hexEval_digits_216s65_eq s
  set G := ∑ i ∈ Finset.range (18 * s + 4), 16 ^ (3 * i) with hGdef
  set H := ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i) with hHdef
  set U := 16 ^ (54 * s) with hUdef
  set p13 := 16 ^ 13 with hp13
  set p17 := 16 ^ 17 with hp17
  set p29 := 16 ^ 29 with hp29
  set p33 := 16 ^ 33 with hp33
  set p49 := 16 ^ 49 with hp49
  set p65 := 16 ^ 65 with hp65
  set p81 := 16 ^ 81 with hp81
  set p96 := 16 ^ 96 with hp96
  set p111 := 16 ^ 111 with hp111
  have hGpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hG : G * 4095 = 281474976710656 * U - 1 := by
    rw [hGdef, hUdef]
    have : ∑ i ∈ Finset.range (18 * s + 4), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (18 * s + 4), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hGpow i
    rw [this]
    have hpow : 16 ^ (54 * s + 12) = 4096 ^ (18 * s + 4) := by
      have : 54 * s + 12 = 3 * (18 * s + 4) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    have : 16 ^ (54 * s + 12) = 281474976710656 * 16 ^ (54 * s) := by
      have : 54 * s + 12 = 12 + 54 * s := by omega
      rw [this, pow_add, show (16 : ℕ) ^ 12 = 281474976710656 from rfl]
    have hgs := geom_sum_4096 (18 * s + 4)
    have hle : 1 ≤ 4096 ^ (18 * s + 4) := Nat.one_le_pow _ _ (by decide)
    omega
  have hHpow : ∀ i, 16 ^ (27 * i) = (16 ^ 27) ^ i := by
    intro i; rw [← pow_mul]
  have hH : H * (16 ^ 27 - 1) = U - 1 := by
    rw [hHdef, hUdef]
    have : ∑ i ∈ Finset.range (2 * s + 0), 16 ^ (27 * i) =
        ∑ i ∈ Finset.range (2 * s + 0), (16 ^ 27) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (54 * s) = (16 ^ 27) ^ (2 * s) := by
      have : 54 * s = 27 * (2 * s) := by omega
      rw [this, ← pow_mul]
    rw [this]
    exact geom_sum_16_pow_27 (2 * s)
  have hU1 : 1 ≤ U := by
    rw [hUdef]; exact Nat.one_le_pow _ _ (by decide)
  have pw_3ecc : 16 ^ (54 * s + 13) = p13 * U := by
    have : 54 * s + 13 = 13 + 54 * s := by omega
    rw [this, pow_add, hp13, hUdef]
  have pw_86d : 16 ^ (54 * s + 17) = p17 * U := by
    have : 54 * s + 17 = 17 + 54 * s := by omega
    rw [this, pow_add, hp17, hUdef]
  have pw_86fb : 16 ^ (108 * s + 29) = p29 * (U * U) := by
    have : 108 * s + 29 = 29 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp29, hUdef, pow_add]
  have pw_A : 16 ^ (108 * s + 33) = p33 * (U * U) := by
    have : 108 * s + 33 = 33 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp33, hUdef, pow_add]
  have pw_c1 : 16 ^ (162 * s + 33) = p33 * (U * U * U) := by
    have : 162 * s + 33 = 33 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp33, hUdef, pow_add, pow_add]
  have pw_B : 16 ^ (162 * s + 49) = p49 * (U * U * U) := by
    have : 162 * s + 49 = 49 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp49, hUdef, pow_add, pow_add]
  have pw_c2 : 16 ^ (216 * s + 49) = p49 * (U * U * U * U) := by
    have : 216 * s + 49 = 49 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp49, hUdef, pow_add, pow_add, pow_add]
  have pw_C : 16 ^ (216 * s + 65) = p65 * (U * U * U * U) := by
    have : 216 * s + 65 = 65 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp65, hUdef, pow_add, pow_add, pow_add]
  have pw_c3 : 16 ^ (270 * s + 65) = p65 * (U * U * U * U * U) := by
    have : 270 * s + 65 = 65 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp65, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw_D : 16 ^ (270 * s + 81) = p81 * (U * U * U * U * U) := by
    have : 270 * s + 81 = 81 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp81, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw_c4 : 16 ^ (324 * s + 81) = p81 * (U * U * U * U * U * U) := by
    have : 324 * s + 81 = 81 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp81, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_E : 16 ^ (324 * s + 96) = p96 * (U * U * U * U * U * U) := by
    have : 324 * s + 96 = 96 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp96, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_c5 : 16 ^ (378 * s + 96) = p96 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 96 = 96 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp96, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_F : 16 ^ (378 * s + 111) = p111 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 111 = 111 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp111, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_c6 : 16 ^ (432 * s + 111) = p111 * (U * U * U * U * U * U * U * U) := by
    have : 432 * s + 111 = 111 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp111, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factG0 : (2835 * 16 * 2275 : ℕ) = 4095 * 25200 := by decide
  have factG1 : (2835 * p17 * 3432 : ℕ) = 4095 * 701271422706142314233856 := by
    rw [hp17]; decide
  have factHA : (2835 * p33 * 216231233813322076505602018648517 : ℕ) = (16 ^ 27 - 1) * 10284694257818444119717034135017762423046144 := by
    rw [hp33]; decide
  have factHB : (2835 * p49 * 316849155741278723010855684287504 : ℕ) = (16 ^ 27 - 1) * 278000281656805317668759441975021130236341117924423160507138048 := by
    rw [hp49]; decide
  have factHC : (2835 * p65 * 289033279713413575000870882523825 : ℕ) = (16 ^ 27 - 1) * 4678000405187574295112267794350991477272107380491878787194086393919690437453414400 := by
    rw [hp65]; decide
  have factHD : (2835 * p81 * 23923942756476608782250302751477 : ℕ) = (16 ^ 27 - 1) * 7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 := by
    rw [hp81]; decide
  have factHE : (2835 * p96 * 172962093325531846267847882571683 : ℕ) = (16 ^ 27 - 1) * 59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 := by
    rw [hp96]; decide
  have factHF : (2835 * p111 * 311011255834195914169253935769201 : ℕ) = (16 ^ 27 - 1) * 123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 := by
    rw [hp111]; decide
  have factC1 : (2835 * p13 * 52451 : ℕ) = 669678891996520025948160 := by
    rw [hp13]; decide
  have factC2 : (2835 * p29 * 49000 : ℕ) = 11540606689653849280277022361177754173440000 := by
    rw [hp29]; decide
  have factC3 : (2835 * p33 * 16300622376994742725 : ℕ) = 251603499584070478376354294245258646920309653556573016948736000 := by
    rw [hp33]; decide
  have factC4 : (2835 * p49 * 17570818569041095696 : ℕ) = 5002927481598638203717235643001690515028105174236728284722968188919472507857141760 := by
    rw [hp49]; decide
  have factC5 : (2835 * p65 * 898750097065654961 : ℕ) = 4720531349385211277414997565447135878159709200057211144310854572795226806781129221631055774676418560 := by
    rw [hp65]; decide
  have factC6 : (2835 * p81 * 725506865685578485 : ℕ) = 70293179054367750907563066890536683712733302273079374584388311510413720777648116594205548235704227503922239115991449600 := by
    rw [hp81]; decide
  have factC7 : (2835 * p96 * 870689573673107363 : ℕ) = 97260106794805896982094960680261548663443004985654747481941421240186004825404188281270654376903201882752578611307385401472283987075399680 := by
    rw [hp96]; decide
  have factC8 : (2835 * p111 * 208217217057744497 : ℕ) = 26815615859885194075721749126963947153551682514203016765519399325728329948596539505241439483577422000551245917041996624920522065359817799554522758953041920 := by
    rw [hp111]; decide
  have hex2835 :
      hexEval (digits_216s65 s) * 2835 =
        25515 + 25200 * (281474976710656 * U - 1) + 669678891996520025948160 * U
          + 701271422706142314233856 * U * (281474976710656 * U - 1) + 11540606689653849280277022361177754173440000 * (U * U)
          + 10284694257818444119717034135017762423046144 * (U * U) * (U - 1)
          + 251603499584070478376354294245258646920309653556573016948736000 * (U * U * U)
          + 278000281656805317668759441975021130236341117924423160507138048 * (U * U * U) * (U - 1)
          + 5002927481598638203717235643001690515028105174236728284722968188919472507857141760 * (U * U * U * U)
          + 4678000405187574295112267794350991477272107380491878787194086393919690437453414400 * (U * U * U * U) * (U - 1)
          + 4720531349385211277414997565447135878159709200057211144310854572795226806781129221631055774676418560 * (U * U * U * U * U)
          + 7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 * (U * U * U * U * U) * (U - 1)
          + 70293179054367750907563066890536683712733302273079374584388311510413720777648116594205548235704227503922239115991449600 * (U * U * U * U * U * U)
          + 59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 * (U * U * U * U * U * U) * (U - 1)
          + 97260106794805896982094960680261548663443004985654747481941421240186004825404188281270654376903201882752578611307385401472283987075399680 * (U * U * U * U * U * U * U)
          + 123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 * (U * U * U * U * U * U * U) * (U - 1)
          + 26815615859885194075721749126963947153551682514203016765519399325728329948596539505241439483577422000551245917041996624920522065359817799554522758953041920 * (U * U * U * U * U * U * U * U) := by
    rw [hex, pw_3ecc, pw_86d, pw_86fb, pw_A, pw_c1, pw_B, pw_c2, pw_C, pw_c3,
      pw_D, pw_c4, pw_E, pw_c5, pw_F, pw_c6]
    rw [dist_216s65 G H U p13 p17 p29 p33 p49 p65 p81 p96 p111]
    have G0 : 2835 * 16 * 2275 * G = 25200 * (281474976710656 * U - 1) := by
      rw [factG0]
      have : 4095 * 25200 * G = 25200 * (G * 4095) := by ring
      rw [this, hG]
    have G1 : 2835 * p17 * 3432 * G * U = 701271422706142314233856 * U * (281474976710656 * U - 1) := by
      rw [factG1]
      have : 4095 * 701271422706142314233856 * G * U = 701271422706142314233856 * U * (G * 4095) := by ring
      rw [this, hG]
    have HA : 2835 * p33 * 216231233813322076505602018648517 * H * (U * U) =
        10284694257818444119717034135017762423046144 * (U * U) * (U - 1) := by
      rw [factHA]
      have : (16 ^ 27 - 1) * 10284694257818444119717034135017762423046144 * H * (U * U) =
          10284694257818444119717034135017762423046144 * (U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HB : 2835 * p49 * 316849155741278723010855684287504 * H * (U * U * U) =
        278000281656805317668759441975021130236341117924423160507138048 * (U * U * U) * (U - 1) := by
      rw [factHB]
      have : (16 ^ 27 - 1) * 278000281656805317668759441975021130236341117924423160507138048 * H * (U * U * U) =
          278000281656805317668759441975021130236341117924423160507138048 * (U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HC : 2835 * p65 * 289033279713413575000870882523825 * H * (U * U * U * U) =
        4678000405187574295112267794350991477272107380491878787194086393919690437453414400 * (U * U * U * U) * (U - 1) := by
      rw [factHC]
      have : (16 ^ 27 - 1) * 4678000405187574295112267794350991477272107380491878787194086393919690437453414400 * H * (U * U * U * U) =
          4678000405187574295112267794350991477272107380491878787194086393919690437453414400 * (U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HD : 2835 * p81 * 23923942756476608782250302751477 * H * (U * U * U * U * U) =
        7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 * (U * U * U * U * U) * (U - 1) := by
      rw [factHD]
      have : (16 ^ 27 - 1) * 7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 * H * (U * U * U * U * U) =
          7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 * (U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HE : 2835 * p96 * 172962093325531846267847882571683 * H * (U * U * U * U * U * U) =
        59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 * (U * U * U * U * U * U) * (U - 1) := by
      rw [factHE]
      have : (16 ^ 27 - 1) * 59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 * H * (U * U * U * U * U * U) =
          59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 * (U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HF : 2835 * p111 * 311011255834195914169253935769201 * H * (U * U * U * U * U * U * U) =
        123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 * (U * U * U * U * U * U * U) * (U - 1) := by
      rw [factHF]
      have : (16 ^ 27 - 1) * 123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 * H * (U * U * U * U * U * U * U) =
          123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 * (U * U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have C1 : 2835 * p13 * 52451 * U = 669678891996520025948160 * U := by rw [factC1]
    have C2 : 2835 * p29 * 49000 * (U * U) = 11540606689653849280277022361177754173440000 * (U * U) := by rw [factC2]
    have C3 : 2835 * p33 * 16300622376994742725 * (U * U * U) = 251603499584070478376354294245258646920309653556573016948736000 * (U * U * U) := by rw [factC3]
    have C4 : 2835 * p49 * 17570818569041095696 * (U * U * U * U) = 5002927481598638203717235643001690515028105174236728284722968188919472507857141760 * (U * U * U * U) := by rw [factC4]
    have C5 : 2835 * p65 * 898750097065654961 * (U * U * U * U * U) = 4720531349385211277414997565447135878159709200057211144310854572795226806781129221631055774676418560 * (U * U * U * U * U) := by rw [factC5]
    have C6 : 2835 * p81 * 725506865685578485 * (U * U * U * U * U * U) = 70293179054367750907563066890536683712733302273079374584388311510413720777648116594205548235704227503922239115991449600 * (U * U * U * U * U * U) := by rw [factC6]
    have C7 : 2835 * p96 * 870689573673107363 * (U * U * U * U * U * U * U) = 97260106794805896982094960680261548663443004985654747481941421240186004825404188281270654376903201882752578611307385401472283987075399680 * (U * U * U * U * U * U * U) := by rw [factC7]
    have C8 : 2835 * p111 * 208217217057744497 * (U * U * U * U * U * U * U * U) = 26815615859885194075721749126963947153551682514203016765519399325728329948596539505241439483577422000551245917041996624920522065359817799554522758953041920 * (U * U * U * U * U * U * U * U) := by rw [factC8]
    rw [G0, G1, HA, HB, HC, HD, HE, HF, C1, C2, C3, C4, C5, C6, C7, C8]
  have hex2835' :
      hexEval (digits_216s65 s) * 2835 =
        25515 + 25200 * (281474976710656 * U - 1) + 669678891996520025948160 * U
          + 701271422706142314233856 * U * (281474976710656 * U - 1) + 11540606689653849280277022361177754173440000 * U ^ 2
          + 10284694257818444119717034135017762423046144 * U ^ 2 * (U - 1)
          + 251603499584070478376354294245258646920309653556573016948736000 * U ^ 3
          + 278000281656805317668759441975021130236341117924423160507138048 * U ^ 3 * (U - 1)
          + 5002927481598638203717235643001690515028105174236728284722968188919472507857141760 * U ^ 4
          + 4678000405187574295112267794350991477272107380491878787194086393919690437453414400 * U ^ 4 * (U - 1)
          + 4720531349385211277414997565447135878159709200057211144310854572795226806781129221631055774676418560 * U ^ 5
          + 7142740648119523315528952585430982271231443922760646862702907136557502763010461999276785218715910144 * U ^ 5 * (U - 1)
          + 70293179054367750907563066890536683712733302273079374584388311510413720777648116594205548235704227503922239115991449600 * U ^ 6
          + 59536431362752058089753629591317000459475486037673289915269871333815285596732285233846956311131107533258814893353598976 * U ^ 6 * (U - 1)
          + 97260106794805896982094960680261548663443004985654747481941421240186004825404188281270654376903201882752578611307385401472283987075399680 * U ^ 7
          + 123426300869447745101407049126981769989927723561715198111550554448362309112756384854828817799330975476786985700264075340338344539059126272 * U ^ 7 * (U - 1)
          + 26815615859885194075721749126963947153551682514203016765519399325728329948596539505241439483577422000551245917041996624920522065359817799554522758953041920 * U ^ 8 := by
    rw [hex2835]
    ring
  rw [hex2835']
  have hR :
      (36893488147419103232 * 16 ^ (54 * s) - 1) * (18446744073709551616 * 16 ^ (54 * s) - 1) *
        (36893488147419103232 * 16 ^ (54 * s) - 3) * (9223372036854775808 * 16 ^ (54 * s) - 1) *
        (36893488147419103232 * 16 ^ (54 * s) - 5) * (18446744073709551616 * 16 ^ (54 * s) - 3) *
        (36893488147419103232 * 16 ^ (54 * s) - 7) * (4611686018427387904 * 16 ^ (54 * s) - 1) =
      (36893488147419103232 * U - 1) * (18446744073709551616 * U - 1) *
        (36893488147419103232 * U - 3) * (9223372036854775808 * U - 1) *
        (36893488147419103232 * U - 5) * (18446744073709551616 * U - 3) *
        (36893488147419103232 * U - 7) * (4611686018427387904 * U - 1) := by
    rw [hUdef]
  rw [hR]
  have hA : 1 ≤ 36893488147419103232 * U := one_le_mul (by decide : 1 ≤ 36893488147419103232) hU1
  have hB : 1 ≤ 18446744073709551616 * U := one_le_mul (by decide : 1 ≤ 18446744073709551616) hU1
  have hC : 1 ≤ 9223372036854775808 * U := one_le_mul (by decide : 1 ≤ 9223372036854775808) hU1
  have hD : 1 ≤ 4611686018427387904 * U := one_le_mul (by decide : 1 ≤ 4611686018427387904) hU1
  have hA3 : 3 ≤ 36893488147419103232 * U :=
    (by decide : 3 ≤ 36893488147419103232).trans (Nat.le_mul_of_pos_right 36893488147419103232 hU1)
  have hA5 : 5 ≤ 36893488147419103232 * U :=
    (by decide : 5 ≤ 36893488147419103232).trans (Nat.le_mul_of_pos_right 36893488147419103232 hU1)
  have hA7 : 7 ≤ 36893488147419103232 * U :=
    (by decide : 7 ≤ 36893488147419103232).trans (Nat.le_mul_of_pos_right 36893488147419103232 hU1)
  have hB3 : 3 ≤ 18446744073709551616 * U :=
    (by decide : 3 ≤ 18446744073709551616).trans (Nat.le_mul_of_pos_right 18446744073709551616 hU1)
  have hgU : 1 ≤ 281474976710656 * U := one_le_mul (by decide : 1 ≤ 281474976710656) hU1
  zify [hU1, hA, hB, hC, hD, hA3, hA5, hA7, hB3, hgU]
  simpa using poly_id_216s65 (U : ℤ)

lemma popc_choose_two_pow_nine_of_mod_216_eq_sixtyfive {m : ℕ}
    (hmod : m % 216 = 65) :
    popc (Nat.choose (2 ^ m) 9) % 2 = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m = 216 * s + 65 := ⟨m / 216, by omega⟩
  have hm9 : 9 ≤ m := by omega
  rw [choose_two_pow_nine m hm9, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) / 2835 =
        hexEval (digits_216s65 s) := by
    set U := 16 ^ (54 * s) with hUdef
    have h16 : 16 ^ (54 * s) = 2 ^ (216 * s) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 36893488147419103232 * U := by
      rw [hs, hUdef, pow_add, h16, show (2 : ℕ) ^ 65 = 36893488147419103232 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 18446744073709551616 * U := by
      have : m - 1 = 216 * s + 64 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 64 = 18446744073709551616 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 9223372036854775808 * U := by
      have : m - 2 = 216 * s + 63 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 63 = 9223372036854775808 from rfl]
      ring
    have h2m3 : 2 ^ (m - 3) = 4611686018427387904 * U := by
      have : m - 3 = 216 * s + 62 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 62 = 4611686018427387904 from rfl]
      ring
    have hmul := hexEval_digits_216s65_mul_2835 s
    rw [h2m, h2m1, h2m2, h2m3]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2835) hmul.symm
  rw [hex, popc_hexEval_digits_216s65 s]
  omega


lemma a_ne_zero_two_pow_mod216_eq_sixtyfive {m : ℕ} (hm : 65 ≤ m) (hmod : m % 216 = 65) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 9 (by decide) ?_
    (popc_choose_two_pow_nine_of_mod_216_eq_sixtyfive hmod)
  have : 9 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 9 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  exact this

/- Digit list for the odd part of `C(2^{216s+161}, 9)`, `s ≥ 0`. LSB first. -/

def blockA27_161 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 14, 3, 5, 5, 0, 7, 12, 12, 8, 3, 9, 10, 10]
def blockB27_161 : List ℕ := [15, 9, 15, 0, 1, 12, 2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 13, 9, 4, 10, 11, 11, 6, 13, 2, 3]
def blockC27_161 : List ℕ := [3, 2, 7, 5, 9, 3, 7, 0, 0, 9, 7, 12, 10, 14, 8, 12, 5, 5, 14, 12, 1, 0, 4, 14, 1, 11, 10]
def blockD27_161 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10, 8, 13, 11, 15, 9, 13, 6, 6, 15, 13, 2, 1]
def blockE27_161 : List ℕ := [12, 13, 13, 8, 15, 4, 5, 1, 12, 1, 3, 3, 14, 4, 10, 10, 6, 1, 7, 8, 8, 3, 10, 15, 15, 11, 6]
def blockF27_161 : List ℕ := [14, 8, 13, 10, 10, 4, 7, 12, 11, 3, 14, 2, 0, 0, 10, 12, 1, 1, 9, 3, 8, 5, 5, 15, 1, 7, 6]
def conn1_161 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 11, 1]
def conn2_161 : List ℕ := [15, 9, 15, 0, 1, 12, 2, 8, 8, 4, 15, 10, 11]
def conn3_161 : List ℕ := [3, 2, 7, 5, 9, 3, 7, 0, 0, 9, 7, 12, 0]
def conn4_161 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8]
def conn5_161 : List ℕ := [12, 13, 13, 8, 15, 4, 5, 1, 12, 1, 3, 3]
def conn6_161 : List ℕ := [14, 8, 13, 10, 10, 4, 7, 12, 11, 3, 14, 2]

def digits_216s161 (s : ℕ) : List ℕ :=
  [9]
    ++ List.flatten (List.replicate (18 * s + 12) [3, 14, 8])
    ++ [3, 14, 12, 12]
    ++ List.flatten (List.replicate (18 * s + 12) [8, 6, 13])
    ++ [8, 6, 15, 11]
    ++ List.flatten (List.replicate (2 * s + 1) blockA27_161)
    ++ conn1_161
    ++ List.flatten (List.replicate (2 * s + 1) blockB27_161)
    ++ conn2_161
    ++ List.flatten (List.replicate (2 * s + 1) blockC27_161)
    ++ conn3_161
    ++ List.flatten (List.replicate (2 * s + 1) blockD27_161)
    ++ conn4_161
    ++ List.flatten (List.replicate (2 * s + 1) blockE27_161)
    ++ conn5_161
    ++ List.flatten (List.replicate (2 * s + 1) blockF27_161)
    ++ conn6_161

lemma digits_216s161_lt (s : ℕ) : ∀ d ∈ digits_216s161 s, d < 16 := by
  intro d hd
  unfold digits_216s161 blockA27_161 blockB27_161 blockC27_161 blockD27_161
    blockE27_161 blockF27_161 conn1_161 conn2_161 conn3_161 conn4_161
    conn5_161 conn6_161 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten] at hd
  aesop

lemma popc_blockA27_161 : (List.map popc blockA27_161).sum = 57 := by
  unfold blockA27_161; decide

lemma popc_blockB27_161 : (List.map popc blockB27_161).sum = 53 := by
  unfold blockB27_161; decide

lemma popc_blockC27_161 : (List.map popc blockC27_161).sum = 50 := by
  unfold blockC27_161; decide

lemma popc_blockD27_161 : (List.map popc blockD27_161).sum = 55 := by
  unfold blockD27_161; decide

lemma popc_blockE27_161 : (List.map popc blockE27_161).sum = 57 := by
  unfold blockE27_161; decide

lemma popc_blockF27_161 : (List.map popc blockF27_161).sum = 51 := by
  unfold blockF27_161; decide

lemma popc_conn1_161 : (List.map popc conn1_161).sum = 28 := by
  unfold conn1_161; decide

lemma popc_conn2_161 : (List.map popc conn2_161).sum = 26 := by
  unfold conn2_161; decide

lemma popc_conn3_161 : (List.map popc conn3_161).sum = 22 := by
  unfold conn3_161; decide

lemma popc_conn4_161 : (List.map popc conn4_161).sum = 22 := by
  unfold conn4_161; decide

lemma popc_conn5_161 : (List.map popc conn5_161).sum = 24 := by
  unfold conn5_161; decide

lemma popc_conn6_161 : (List.map popc conn6_161).sum = 26 := by
  unfold conn6_161; decide

lemma popc_digits_216s161 (s : ℕ) :
    (List.map popc (digits_216s161 s)).sum = 636 + 862 * s := by
  have h0 : popc 0 = 0 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h3 : popc 3 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h5 : popc 5 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h7 : popc 7 = 3 := by decide
  have h8 : popc 8 = 1 := by decide
  have h9 : popc 9 = 2 := by decide
  have h10 : popc 10 = 2 := by decide
  have h11 : popc 11 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h13 : popc 13 = 3 := by decide
  have h14 : popc 14 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  unfold digits_216s161
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_flatten_replicate]
  rw [popc_blockA27_161, popc_blockB27_161, popc_blockC27_161, popc_blockD27_161,
    popc_blockE27_161, popc_blockF27_161, popc_conn1_161, popc_conn2_161,
    popc_conn3_161, popc_conn4_161, popc_conn5_161, popc_conn6_161]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

lemma popc_hexEval_digits_216s161 (s : ℕ) :
    popc (hexEval (digits_216s161 s)) = 636 + 862 * s := by
  rw [popc_hexEval _ (digits_216s161_lt s), popc_digits_216s161 s]

lemma hexEval_blockA27_161 : hexEval blockA27_161 = 216231233813322076505602018648517 := by
  unfold blockA27_161; decide

lemma hexEval_blockB27_161 : hexEval blockB27_161 = 64445836229169046623956557172639 := by
  unfold blockB27_161; decide

lemma hexEval_blockC27_161 : hexEval blockC27_161 = 216918045567096524604613989062435 := by
  unfold blockC27_161; decide

lemma hexEval_blockD27_161 : hexEval blockD27_161 = 23923942756476608782250302751477 := by
  unfold blockD27_161; decide

lemma hexEval_blockE27_161 : hexEval blockE27_161 = 136904476252373321069719435840988 := by
  unfold blockE27_161; decide

lemma hexEval_blockF27_161 : hexEval blockF27_161 = 130723170468403288178611702115726 := by
  unfold blockF27_161; decide

lemma hexEval_conn1_161 : hexEval conn1_161 = 476844424831429 := by
  unfold conn1_161; decide

lemma hexEval_conn2_161 : hexEval conn2_161 = 3288950710013855 := by
  unfold conn2_161; decide

lemma hexEval_conn3_161 : hexEval conn3_161 = 219421410416419 := by
  unfold conn3_161; decide

lemma hexEval_conn4_161 : hexEval conn4_161 = 145850702217973 := by
  unfold conn4_161; decide

lemma hexEval_conn5_161 : hexEval conn5_161 = 56195709636060 := by
  unfold conn5_161; decide

lemma hexEval_conn6_161 : hexEval conn6_161 = 50834281508238 := by
  unfold conn6_161; decide

lemma length_blockA27_161 : blockA27_161.length = 27 := by unfold blockA27_161; decide
lemma length_blockB27_161 : blockB27_161.length = 27 := by unfold blockB27_161; decide
lemma length_blockC27_161 : blockC27_161.length = 27 := by unfold blockC27_161; decide
lemma length_blockD27_161 : blockD27_161.length = 27 := by unfold blockD27_161; decide
lemma length_blockE27_161 : blockE27_161.length = 27 := by unfold blockE27_161; decide
lemma length_blockF27_161 : blockF27_161.length = 27 := by unfold blockF27_161; decide
lemma length_conn1_161 : conn1_161.length = 13 := by unfold conn1_161; decide
lemma length_conn2_161 : conn2_161.length = 13 := by unfold conn2_161; decide
lemma length_conn3_161 : conn3_161.length = 13 := by unfold conn3_161; decide
lemma length_conn4_161 : conn4_161.length = 12 := by unfold conn4_161; decide
lemma length_conn5_161 : conn5_161.length = 12 := by unfold conn5_161; decide
lemma length_conn6_161 : conn6_161.length = 12 := by unfold conn6_161; decide

lemma hexEval_digits_216s161_eq (s : ℕ) :
    hexEval (digits_216s161 s) =
      9
        + 16 * (2275 * ∑ i ∈ Finset.range (18 * s + 12), 16 ^ (3 * i))
        + 16 ^ (54 * s + 37) * 52451
        + 16 ^ (54 * s + 41) * (3432 * ∑ i ∈ Finset.range (18 * s + 12), 16 ^ (3 * i))
        + 16 ^ (108 * s + 77) * 49000
        + 16 ^ (108 * s + 81) * (216231233813322076505602018648517 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (162 * s + 108) * 476844424831429
        + 16 ^ (162 * s + 121) * (64445836229169046623956557172639 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (216 * s + 148) * 3288950710013855
        + 16 ^ (216 * s + 161) * (216918045567096524604613989062435 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (270 * s + 188) * 219421410416419
        + 16 ^ (270 * s + 201) * (23923942756476608782250302751477 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (324 * s + 228) * 145850702217973
        + 16 ^ (324 * s + 240) * (136904476252373321069719435840988 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (378 * s + 267) * 56195709636060
        + 16 ^ (378 * s + 279) * (130723170468403288178611702115726 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (432 * s + 306) * 50834281508238 := by
  unfold digits_216s161
  repeat rw [hexEval_append]
  rw [hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_3e8, hexEval_3ecc, hexEval_86d, hexEval_86fb,
    hexEval_blockA27_161, hexEval_blockB27_161, hexEval_blockC27_161,
    hexEval_blockD27_161, hexEval_blockE27_161, hexEval_blockF27_161,
    hexEval_conn1_161, hexEval_conn2_161, hexEval_conn3_161,
    hexEval_conn4_161, hexEval_conn5_161, hexEval_conn6_161]
  simp only [List.length_cons, List.length_nil, List.length_append,
    length_flatten_replicate, length_blockA27_161, length_blockB27_161,
    length_blockC27_161, length_blockD27_161, length_blockE27_161,
    length_blockF27_161, length_conn1_161, length_conn2_161,
    length_conn3_161, length_conn4_161, length_conn5_161, length_conn6_161]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f4 : (0 + 1 + 1 + 1 + 1 : ℕ) = 4 := rfl
  rw [f1, f3, f4]
  have e1 : 1 + (18 * s + 12) * 3 = 54 * s + 37 := by omega
  rw [e1]
  have e2 : 54 * s + 37 + 4 = 54 * s + 41 := by omega
  rw [e2]
  have e3 : 54 * s + 41 + (18 * s + 12) * 3 = 108 * s + 77 := by omega
  rw [e3]
  have e4 : 108 * s + 77 + 4 = 108 * s + 81 := by omega
  rw [e4]
  have e5 : 108 * s + 81 + (2 * s + 1) * 27 = 162 * s + 108 := by omega
  rw [e5]
  have e6 : 162 * s + 108 + 13 = 162 * s + 121 := by omega
  rw [e6]
  have e7 : 162 * s + 121 + (2 * s + 1) * 27 = 216 * s + 148 := by omega
  rw [e7]
  have e8 : 216 * s + 148 + 13 = 216 * s + 161 := by omega
  rw [e8]
  have e9 : 216 * s + 161 + (2 * s + 1) * 27 = 270 * s + 188 := by omega
  rw [e9]
  have e10 : 270 * s + 188 + 13 = 270 * s + 201 := by omega
  rw [e10]
  have e11 : 270 * s + 201 + (2 * s + 1) * 27 = 324 * s + 228 := by omega
  rw [e11]
  have e12 : 324 * s + 228 + 12 = 324 * s + 240 := by omega
  rw [e12]
  have e13 : 324 * s + 240 + (2 * s + 1) * 27 = 378 * s + 267 := by omega
  rw [e13]
  have e14 : 378 * s + 267 + 12 = 378 * s + 279 := by omega
  rw [e14]
  have e15 : 378 * s + 279 + (2 * s + 1) * 27 = 432 * s + 306 := by omega
  rw [e15]
  simp [hexEval_singleton]

lemma poly_id_216s161 (U : ℤ) :
    25515
      + 25200 * (22300745198530623141535718272648361505980416 * U - 1)
      + 53057428087472763845033856545623288936124110350581760 * U
      + 55560446244771605338431282600542215275239931553775616 * U * (22300745198530623141535718272648361505980416 * U - 1)
      + 72441562279041314476539169998179524414070971367962504769822579333648352833695723146103461500682240000 * U ^ 2
      + 64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 * U ^ 2 * (324518553658426726783156020576256 * U - 1)
      + 14992977850030110738975757318512050500436504344543727029070274548170712130472918207954198357180978374441246270564683554223122740828313072526048624640 * U ^ 3
      + 28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 * U ^ 3 * (324518553658426726783156020576256 * U - 1)
      + 151135978204430032461417338256882329986369217707633389752204416432574350436026030159452818427319072070511540925585162441127091922741715471339281286331542804584971092995623854365480631652221504716800 * U ^ 4
      + 138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 * U ^ 4 * (324518553658426726783156020576256 * U - 1)
      + 14736311896664433054026639238447469305113215507150581781195052943013443735646362944856869853193108905048821966958061616441419026689421458950036738836508193317208643541279884643042215885544140095836372306646440007545926444326331845695769715671040 * U ^ 5
      + 22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 * U ^ 5 * (324518553658426726783156020576256 * U - 1)
      + 14315866282746591412976246693834516374766687097441110169760677533064466123526977349152905038658911453081433014562132967696841112409253659414615364488571419699765045998869563416861977989126274828294615432383774460707253417993960431158058329653956736133989504364091156364017514716439212908871680 * U ^ 6
      + 11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 * U ^ 6 * (324518553658426726783156020576256 * U - 1)
      + 503838780582754136371132567795492994773689712012080980607832988120259092478431547290790120856796287583243447166909927833338208640713423416702962012150081661904396661979652855022720361722540709790950628759191177228145109730883998046782425187435251543115879733767403374461011853334815245110536954663176547592593950714611447155398746413465600 * U ^ 7
      + 1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 * U ^ 7 * (324518553658426726783156020576256 * U - 1)
      + 41631728778657266428854767511961824018677349975101313361976929288375040077376593681605003367660247790656661409202560634050552957345106219029564474766487613046738846744237425293707596741623619795524631409582546871935271460655865457916057989560607761030861871425970048240076358314871255618765584221062963736862017595720792719343190319678087295095173689483888125252568161387203301925191680 * U ^ 8
    =
      (2923003274661805836407369665432566039311865085952 * U - 1) * (1461501637330902918203684832716283019655932542976 * U - 1) *
        (2923003274661805836407369665432566039311865085952 * U - 3) * (730750818665451459101842416358141509827966271488 * U - 1) *
        (2923003274661805836407369665432566039311865085952 * U - 5) * (1461501637330902918203684832716283019655932542976 * U - 3) *
        (2923003274661805836407369665432566039311865085952 * U - 7) * (365375409332725729550921208179070754913983135744 * U - 1) := by
  ring

lemma dist_216s161 (G H U p37 p41 p77 p81 p108 p121 p148 p161 p188 p201 p228 p240 p267 p279 p306 : ℕ) :
    (9 + 16 * (2275 * G) + p37 * U * 52451 + p41 * U * (3432 * G) + p77 * (U * U) * 49000 + p81 * (U * U) * (216231233813322076505602018648517 * H) + p108 * (U * U * U) * 476844424831429 + p121 * (U * U * U) * (64445836229169046623956557172639 * H) + p148 * (U * U * U * U) * 3288950710013855 + p161 * (U * U * U * U) * (216918045567096524604613989062435 * H) + p188 * (U * U * U * U * U) * 219421410416419 + p201 * (U * U * U * U * U) * (23923942756476608782250302751477 * H) + p228 * (U * U * U * U * U * U) * 145850702217973 + p240 * (U * U * U * U * U * U) * (136904476252373321069719435840988 * H) + p267 * (U * U * U * U * U * U * U) * 56195709636060 + p279 * (U * U * U * U * U * U * U) * (130723170468403288178611702115726 * H) + p306 * (U * U * U * U * U * U * U * U) * 50834281508238) * 2835
    =
      25515
        + 2835 * 16 * 2275 * G
        + 2835 * p37 * 52451 * U
        + 2835 * p41 * 3432 * G * U
        + 2835 * p77 * 49000 * (U * U)
        + 2835 * p81 * 216231233813322076505602018648517 * H * (U * U)
        + 2835 * p108 * 476844424831429 * (U * U * U)
        + 2835 * p121 * 64445836229169046623956557172639 * H * (U * U * U)
        + 2835 * p148 * 3288950710013855 * (U * U * U * U)
        + 2835 * p161 * 216918045567096524604613989062435 * H * (U * U * U * U)
        + 2835 * p188 * 219421410416419 * (U * U * U * U * U)
        + 2835 * p201 * 23923942756476608782250302751477 * H * (U * U * U * U * U)
        + 2835 * p228 * 145850702217973 * (U * U * U * U * U * U)
        + 2835 * p240 * 136904476252373321069719435840988 * H * (U * U * U * U * U * U)
        + 2835 * p267 * 56195709636060 * (U * U * U * U * U * U * U)
        + 2835 * p279 * 130723170468403288178611702115726 * H * (U * U * U * U * U * U * U)
        + 2835 * p306 * 50834281508238 * (U * U * U * U * U * U * U * U) := by
  ring

lemma hexEval_digits_216s161_mul_2835 (s : ℕ) :
    hexEval (digits_216s161 s) * 2835 =
      (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 1) * (1461501637330902918203684832716283019655932542976 * 16 ^ (54 * s) - 1) *
        (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 3) * (730750818665451459101842416358141509827966271488 * 16 ^ (54 * s) - 1) *
        (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 5) * (1461501637330902918203684832716283019655932542976 * 16 ^ (54 * s) - 3) *
        (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 7) * (365375409332725729550921208179070754913983135744 * 16 ^ (54 * s) - 1) := by
  have hex := hexEval_digits_216s161_eq s
  set G := ∑ i ∈ Finset.range (18 * s + 12), 16 ^ (3 * i) with hGdef
  set H := ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i) with hHdef
  set U := 16 ^ (54 * s) with hUdef
  set p37 := 16 ^ 37 with hp37
  set p41 := 16 ^ 41 with hp41
  set p77 := 16 ^ 77 with hp77
  set p81 := 16 ^ 81 with hp81
  set p108 := 16 ^ 108 with hp108
  set p121 := 16 ^ 121 with hp121
  set p148 := 16 ^ 148 with hp148
  set p161 := 16 ^ 161 with hp161
  set p188 := 16 ^ 188 with hp188
  set p201 := 16 ^ 201 with hp201
  set p228 := 16 ^ 228 with hp228
  set p240 := 16 ^ 240 with hp240
  set p267 := 16 ^ 267 with hp267
  set p279 := 16 ^ 279 with hp279
  set p306 := 16 ^ 306 with hp306
  have hGpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hG : G * 4095 = 22300745198530623141535718272648361505980416 * U - 1 := by
    rw [hGdef, hUdef]
    have : ∑ i ∈ Finset.range (18 * s + 12), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (18 * s + 12), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hGpow i
    rw [this]
    have hpow : 16 ^ (54 * s + 36) = 4096 ^ (18 * s + 12) := by
      have : 54 * s + 36 = 3 * (18 * s + 12) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    have : 16 ^ (54 * s + 36) = 22300745198530623141535718272648361505980416 * 16 ^ (54 * s) := by
      have : 54 * s + 36 = 36 + 54 * s := by omega
      rw [this, pow_add, show (16 : ℕ) ^ 36 = 22300745198530623141535718272648361505980416 from rfl]
    have hgs := geom_sum_4096 (18 * s + 12)
    have hle : 1 ≤ 4096 ^ (18 * s + 12) := Nat.one_le_pow _ _ (by decide)
    omega
  have hHpow : ∀ i, 16 ^ (27 * i) = (16 ^ 27) ^ i := by
    intro i; rw [← pow_mul]
  have hH : H * (16 ^ 27 - 1) = 324518553658426726783156020576256 * U - 1 := by
    rw [hHdef, hUdef]
    have : ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i) =
        ∑ i ∈ Finset.range (2 * s + 1), (16 ^ 27) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (54 * s + 27) = (16 ^ 27) ^ (2 * s + 1) := by
      have : 54 * s + 27 = 27 * (2 * s + 1) := by omega
      rw [this, ← pow_mul]
    have : 16 ^ (54 * s + 27) = 324518553658426726783156020576256 * 16 ^ (54 * s) := by
      have : 54 * s + 27 = 27 + 54 * s := by omega
      rw [this, pow_add, show (16 : ℕ) ^ 27 = 324518553658426726783156020576256 from rfl]
    have hhs := geom_sum_16_pow_27 (2 * s + 1)
    have hle : 1 ≤ (16 ^ 27) ^ (2 * s + 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hU1 : 1 ≤ U := by
    rw [hUdef]; exact Nat.one_le_pow _ _ (by decide)
  have pw_3ecc : 16 ^ (54 * s + 37) = p37 * U := by
    have : 54 * s + 37 = 37 + 54 * s := by omega
    rw [this, pow_add, hp37, hUdef]
  have pw_86d : 16 ^ (54 * s + 41) = p41 * U := by
    have : 54 * s + 41 = 41 + 54 * s := by omega
    rw [this, pow_add, hp41, hUdef]
  have pw_86fb : 16 ^ (108 * s + 77) = p77 * (U * U) := by
    have : 108 * s + 77 = 77 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp77, hUdef, pow_add]
  have pw_A : 16 ^ (108 * s + 81) = p81 * (U * U) := by
    have : 108 * s + 81 = 81 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp81, hUdef, pow_add]
  have pw_c1 : 16 ^ (162 * s + 108) = p108 * (U * U * U) := by
    have : 162 * s + 108 = 108 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp108, hUdef, pow_add, pow_add]
  have pw_B : 16 ^ (162 * s + 121) = p121 * (U * U * U) := by
    have : 162 * s + 121 = 121 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp121, hUdef, pow_add, pow_add]
  have pw_c2 : 16 ^ (216 * s + 148) = p148 * (U * U * U * U) := by
    have : 216 * s + 148 = 148 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp148, hUdef, pow_add, pow_add, pow_add]
  have pw_C : 16 ^ (216 * s + 161) = p161 * (U * U * U * U) := by
    have : 216 * s + 161 = 161 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp161, hUdef, pow_add, pow_add, pow_add]
  have pw_c3 : 16 ^ (270 * s + 188) = p188 * (U * U * U * U * U) := by
    have : 270 * s + 188 = 188 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp188, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw_D : 16 ^ (270 * s + 201) = p201 * (U * U * U * U * U) := by
    have : 270 * s + 201 = 201 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp201, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw_c4 : 16 ^ (324 * s + 228) = p228 * (U * U * U * U * U * U) := by
    have : 324 * s + 228 = 228 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp228, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_E : 16 ^ (324 * s + 240) = p240 * (U * U * U * U * U * U) := by
    have : 324 * s + 240 = 240 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp240, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_c5 : 16 ^ (378 * s + 267) = p267 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 267 = 267 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp267, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_F : 16 ^ (378 * s + 279) = p279 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 279 = 279 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp279, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_c6 : 16 ^ (432 * s + 306) = p306 * (U * U * U * U * U * U * U * U) := by
    have : 432 * s + 306 = 306 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp306, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factG0 : (2835 * 16 * 2275 : ℕ) = 4095 * 25200 := by decide
  have factG1 : (2835 * p41 * 3432 : ℕ) = 4095 * 55560446244771605338431282600542215275239931553775616 := by
    rw [hp41]; decide
  have factHA : (2835 * p81 * 216231233813322076505602018648517 : ℕ) = (16 ^ 27 - 1) * 64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 := by
    rw [hp81]; decide
  have factHB : (2835 * p121 * 64445836229169046623956557172639 : ℕ) = (16 ^ 27 - 1) * 28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 := by
    rw [hp121]; decide
  have factHC : (2835 * p161 * 216918045567096524604613989062435 : ℕ) = (16 ^ 27 - 1) * 138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 := by
    rw [hp161]; decide
  have factHD : (2835 * p201 * 23923942756476608782250302751477 : ℕ) = (16 ^ 27 - 1) * 22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 := by
    rw [hp201]; decide
  have factHE : (2835 * p240 * 136904476252373321069719435840988 : ℕ) = (16 ^ 27 - 1) * 11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 := by
    rw [hp240]; decide
  have factHF : (2835 * p279 * 130723170468403288178611702115726 : ℕ) = (16 ^ 27 - 1) * 1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 := by
    rw [hp279]; decide
  have factC1 : (2835 * p37 * 52451 : ℕ) = 53057428087472763845033856545623288936124110350581760 := by
    rw [hp37]; decide
  have factC2 : (2835 * p77 * 49000 : ℕ) = 72441562279041314476539169998179524414070971367962504769822579333648352833695723146103461500682240000 := by
    rw [hp77]; decide
  have factC3 : (2835 * p108 * 476844424831429 : ℕ) = 14992977850030110738975757318512050500436504344543727029070274548170712130472918207954198357180978374441246270564683554223122740828313072526048624640 := by
    rw [hp108]; decide
  have factC4 : (2835 * p148 * 3288950710013855 : ℕ) = 151135978204430032461417338256882329986369217707633389752204416432574350436026030159452818427319072070511540925585162441127091922741715471339281286331542804584971092995623854365480631652221504716800 := by
    rw [hp148]; decide
  have factC5 : (2835 * p188 * 219421410416419 : ℕ) = 14736311896664433054026639238447469305113215507150581781195052943013443735646362944856869853193108905048821966958061616441419026689421458950036738836508193317208643541279884643042215885544140095836372306646440007545926444326331845695769715671040 := by
    rw [hp188]; decide
  have factC6 : (2835 * p228 * 145850702217973 : ℕ) = 14315866282746591412976246693834516374766687097441110169760677533064466123526977349152905038658911453081433014562132967696841112409253659414615364488571419699765045998869563416861977989126274828294615432383774460707253417993960431158058329653956736133989504364091156364017514716439212908871680 := by
    rw [hp228]; decide
  have factC7 : (2835 * p267 * 56195709636060 : ℕ) = 503838780582754136371132567795492994773689712012080980607832988120259092478431547290790120856796287583243447166909927833338208640713423416702962012150081661904396661979652855022720361722540709790950628759191177228145109730883998046782425187435251543115879733767403374461011853334815245110536954663176547592593950714611447155398746413465600 := by
    rw [hp267]; decide
  have factC8 : (2835 * p306 * 50834281508238 : ℕ) = 41631728778657266428854767511961824018677349975101313361976929288375040077376593681605003367660247790656661409202560634050552957345106219029564474766487613046738846744237425293707596741623619795524631409582546871935271460655865457916057989560607761030861871425970048240076358314871255618765584221062963736862017595720792719343190319678087295095173689483888125252568161387203301925191680 := by
    rw [hp306]; decide
  have hex2835 :
      hexEval (digits_216s161 s) * 2835 =
        25515 + 25200 * (22300745198530623141535718272648361505980416 * U - 1) + 53057428087472763845033856545623288936124110350581760 * U
          + 55560446244771605338431282600542215275239931553775616 * U * (22300745198530623141535718272648361505980416 * U - 1) + 72441562279041314476539169998179524414070971367962504769822579333648352833695723146103461500682240000 * (U * U)
          + 64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 * (U * U) * (324518553658426726783156020576256 * U - 1)
          + 14992977850030110738975757318512050500436504344543727029070274548170712130472918207954198357180978374441246270564683554223122740828313072526048624640 * (U * U * U)
          + 28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 * (U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 151135978204430032461417338256882329986369217707633389752204416432574350436026030159452818427319072070511540925585162441127091922741715471339281286331542804584971092995623854365480631652221504716800 * (U * U * U * U)
          + 138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 * (U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 14736311896664433054026639238447469305113215507150581781195052943013443735646362944856869853193108905048821966958061616441419026689421458950036738836508193317208643541279884643042215885544140095836372306646440007545926444326331845695769715671040 * (U * U * U * U * U)
          + 22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 * (U * U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 14315866282746591412976246693834516374766687097441110169760677533064466123526977349152905038658911453081433014562132967696841112409253659414615364488571419699765045998869563416861977989126274828294615432383774460707253417993960431158058329653956736133989504364091156364017514716439212908871680 * (U * U * U * U * U * U)
          + 11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 * (U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 503838780582754136371132567795492994773689712012080980607832988120259092478431547290790120856796287583243447166909927833338208640713423416702962012150081661904396661979652855022720361722540709790950628759191177228145109730883998046782425187435251543115879733767403374461011853334815245110536954663176547592593950714611447155398746413465600 * (U * U * U * U * U * U * U)
          + 1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 * (U * U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 41631728778657266428854767511961824018677349975101313361976929288375040077376593681605003367660247790656661409202560634050552957345106219029564474766487613046738846744237425293707596741623619795524631409582546871935271460655865457916057989560607761030861871425970048240076358314871255618765584221062963736862017595720792719343190319678087295095173689483888125252568161387203301925191680 * (U * U * U * U * U * U * U * U) := by
    rw [hex, pw_3ecc, pw_86d, pw_86fb, pw_A, pw_c1, pw_B, pw_c2, pw_C, pw_c3,
      pw_D, pw_c4, pw_E, pw_c5, pw_F, pw_c6]
    rw [dist_216s161 G H U p37 p41 p77 p81 p108 p121 p148 p161 p188 p201 p228 p240 p267 p279 p306]
    have G0 : 2835 * 16 * 2275 * G = 25200 * (22300745198530623141535718272648361505980416 * U - 1) := by
      rw [factG0]
      have : 4095 * 25200 * G = 25200 * (G * 4095) := by ring
      rw [this, hG]
    have G1 : 2835 * p41 * 3432 * G * U = 55560446244771605338431282600542215275239931553775616 * U * (22300745198530623141535718272648361505980416 * U - 1) := by
      rw [factG1]
      have : 4095 * 55560446244771605338431282600542215275239931553775616 * G * U = 55560446244771605338431282600542215275239931553775616 * U * (G * 4095) := by ring
      rw [this, hG]
    have HA : 2835 * p81 * 216231233813322076505602018648517 * H * (U * U) =
        64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 * (U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHA]
      have : (16 ^ 27 - 1) * 64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 * H * (U * U) =
          64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 * (U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HB : 2835 * p121 * 64445836229169046623956557172639 * H * (U * U * U) =
        28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 * (U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHB]
      have : (16 ^ 27 - 1) * 28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 * H * (U * U * U) =
          28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 * (U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HC : 2835 * p161 * 216918045567096524604613989062435 * H * (U * U * U * U) =
        138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 * (U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHC]
      have : (16 ^ 27 - 1) * 138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 * H * (U * U * U * U) =
          138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 * (U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HD : 2835 * p201 * 23923942756476608782250302751477 * H * (U * U * U * U * U) =
        22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 * (U * U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHD]
      have : (16 ^ 27 - 1) * 22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 * H * (U * U * U * U * U) =
          22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 * (U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HE : 2835 * p240 * 136904476252373321069719435840988 * H * (U * U * U * U * U * U) =
        11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 * (U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHE]
      have : (16 ^ 27 - 1) * 11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 * H * (U * U * U * U * U * U) =
          11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 * (U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HF : 2835 * p279 * 130723170468403288178611702115726 * H * (U * U * U * U * U * U * U) =
        1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 * (U * U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHF]
      have : (16 ^ 27 - 1) * 1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 * H * (U * U * U * U * U * U * U) =
          1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 * (U * U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have C1 : 2835 * p37 * 52451 * U = 53057428087472763845033856545623288936124110350581760 * U := by rw [factC1]
    have C2 : 2835 * p77 * 49000 * (U * U) = 72441562279041314476539169998179524414070971367962504769822579333648352833695723146103461500682240000 * (U * U) := by rw [factC2]
    have C3 : 2835 * p108 * 476844424831429 * (U * U * U) = 14992977850030110738975757318512050500436504344543727029070274548170712130472918207954198357180978374441246270564683554223122740828313072526048624640 * (U * U * U) := by rw [factC3]
    have C4 : 2835 * p148 * 3288950710013855 * (U * U * U * U) = 151135978204430032461417338256882329986369217707633389752204416432574350436026030159452818427319072070511540925585162441127091922741715471339281286331542804584971092995623854365480631652221504716800 * (U * U * U * U) := by rw [factC4]
    have C5 : 2835 * p188 * 219421410416419 * (U * U * U * U * U) = 14736311896664433054026639238447469305113215507150581781195052943013443735646362944856869853193108905048821966958061616441419026689421458950036738836508193317208643541279884643042215885544140095836372306646440007545926444326331845695769715671040 * (U * U * U * U * U) := by rw [factC5]
    have C6 : 2835 * p228 * 145850702217973 * (U * U * U * U * U * U) = 14315866282746591412976246693834516374766687097441110169760677533064466123526977349152905038658911453081433014562132967696841112409253659414615364488571419699765045998869563416861977989126274828294615432383774460707253417993960431158058329653956736133989504364091156364017514716439212908871680 * (U * U * U * U * U * U) := by rw [factC6]
    have C7 : 2835 * p267 * 56195709636060 * (U * U * U * U * U * U * U) = 503838780582754136371132567795492994773689712012080980607832988120259092478431547290790120856796287583243447166909927833338208640713423416702962012150081661904396661979652855022720361722540709790950628759191177228145109730883998046782425187435251543115879733767403374461011853334815245110536954663176547592593950714611447155398746413465600 * (U * U * U * U * U * U * U) := by rw [factC7]
    have C8 : 2835 * p306 * 50834281508238 * (U * U * U * U * U * U * U * U) = 41631728778657266428854767511961824018677349975101313361976929288375040077376593681605003367660247790656661409202560634050552957345106219029564474766487613046738846744237425293707596741623619795524631409582546871935271460655865457916057989560607761030861871425970048240076358314871255618765584221062963736862017595720792719343190319678087295095173689483888125252568161387203301925191680 * (U * U * U * U * U * U * U * U) := by rw [factC8]
    rw [G0, G1, HA, HB, HC, HD, HE, HF, C1, C2, C3, C4, C5, C6, C7, C8]
  have hex2835' :
      hexEval (digits_216s161 s) * 2835 =
        25515 + 25200 * (22300745198530623141535718272648361505980416 * U - 1) + 53057428087472763845033856545623288936124110350581760 * U
          + 55560446244771605338431282600542215275239931553775616 * U * (22300745198530623141535718272648361505980416 * U - 1) + 72441562279041314476539169998179524414070971367962504769822579333648352833695723146103461500682240000 * U ^ 2
          + 64558072173673586330307136047268543111752141483707473318879385554818768991994079983894006115571073024 * U ^ 2 * (324518553658426726783156020576256 * U - 1)
          + 14992977850030110738975757318512050500436504344543727029070274548170712130472918207954198357180978374441246270564683554223122740828313072526048624640 * U ^ 3
          + 28120710941246458020285427845976842082183372069126060126939285892305348623288448706043717376395935676207720995541630859042195364919028874039061905408 * U ^ 3 * (324518553658426726783156020576256 * U - 1)
          + 151135978204430032461417338256882329986369217707633389752204416432574350436026030159452818427319072070511540925585162441127091922741715471339281286331542804584971092995623854365480631652221504716800 * U ^ 4
          + 138333199526304959029200323084832832970762688339776337095161117142706023069767098358859276439142700841288434826271382429660081527152103280107020691213977534187800478526603233286512745508917026488320 * U ^ 4 * (324518553658426726783156020576256 * U - 1)
          + 14736311896664433054026639238447469305113215507150581781195052943013443735646362944856869853193108905048821966958061616441419026689421458950036738836508193317208643541279884643042215885544140095836372306646440007545926444326331845695769715671040 * U ^ 5
          + 22297840263550232692523024388171886073652071829824396888365086122538940523262161647167669279714477548244357621024440756051052152731375156828735062638994295674142206945894864683500533788089106098693659013958404797026773861437321286557652005945344 * U ^ 5 * (324518553658426726783156020576256 * U - 1)
          + 14315866282746591412976246693834516374766687097441110169760677533064466123526977349152905038658911453081433014562132967696841112409253659414615364488571419699765045998869563416861977989126274828294615432383774460707253417993960431158058329653956736133989504364091156364017514716439212908871680 * U ^ 6
          + 11655395557634398900102645335898725219807967321683629002134016122826686634156645618548875618794884270033464679812764767147417167158782900479707272806389933489759408129147941743725464427966104163429948313801145181132927975118772270435112650884100882872941975608512715946309866993630329276727296 * U ^ 6 * (324518553658426726783156020576256 * U - 1)
          + 503838780582754136371132567795492994773689712012080980607832988120259092478431547290790120856796287583243447166909927833338208640713423416702962012150081661904396661979652855022720361722540709790950628759191177228145109730883998046782425187435251543115879733767403374461011853334815245110536954663176547592593950714611447155398746413465600 * U ^ 7
          + 1016579306405493892628306546646242204821218900833764819476682809559719970029793569170296521295333569095596531796757296704945797501444049471213380318493299048473791163028084998727010277958357181696293472653865573913566629963482556686921350293014178548603022056771398352304757639259549244624869580718031748331591775033722064813020732417114112 * U ^ 7 * (324518553658426726783156020576256 * U - 1)
          + 41631728778657266428854767511961824018677349975101313361976929288375040077376593681605003367660247790656661409202560634050552957345106219029564474766487613046738846744237425293707596741623619795524631409582546871935271460655865457916057989560607761030861871425970048240076358314871255618765584221062963736862017595720792719343190319678087295095173689483888125252568161387203301925191680 * U ^ 8 := by
    rw [hex2835]
    ring
  rw [hex2835']
  have hR :
      (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 1) * (1461501637330902918203684832716283019655932542976 * 16 ^ (54 * s) - 1) *
        (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 3) * (730750818665451459101842416358141509827966271488 * 16 ^ (54 * s) - 1) *
        (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 5) * (1461501637330902918203684832716283019655932542976 * 16 ^ (54 * s) - 3) *
        (2923003274661805836407369665432566039311865085952 * 16 ^ (54 * s) - 7) * (365375409332725729550921208179070754913983135744 * 16 ^ (54 * s) - 1) =
      (2923003274661805836407369665432566039311865085952 * U - 1) * (1461501637330902918203684832716283019655932542976 * U - 1) *
        (2923003274661805836407369665432566039311865085952 * U - 3) * (730750818665451459101842416358141509827966271488 * U - 1) *
        (2923003274661805836407369665432566039311865085952 * U - 5) * (1461501637330902918203684832716283019655932542976 * U - 3) *
        (2923003274661805836407369665432566039311865085952 * U - 7) * (365375409332725729550921208179070754913983135744 * U - 1) := by
    rw [hUdef]
  rw [hR]
  have hA : 1 ≤ 2923003274661805836407369665432566039311865085952 * U := one_le_mul (by decide : 1 ≤ 2923003274661805836407369665432566039311865085952) hU1
  have hB : 1 ≤ 1461501637330902918203684832716283019655932542976 * U := one_le_mul (by decide : 1 ≤ 1461501637330902918203684832716283019655932542976) hU1
  have hC : 1 ≤ 730750818665451459101842416358141509827966271488 * U := one_le_mul (by decide : 1 ≤ 730750818665451459101842416358141509827966271488) hU1
  have hD : 1 ≤ 365375409332725729550921208179070754913983135744 * U := one_le_mul (by decide : 1 ≤ 365375409332725729550921208179070754913983135744) hU1
  have hA3 : 3 ≤ 2923003274661805836407369665432566039311865085952 * U :=
    (by decide : 3 ≤ 2923003274661805836407369665432566039311865085952).trans (Nat.le_mul_of_pos_right 2923003274661805836407369665432566039311865085952 hU1)
  have hA5 : 5 ≤ 2923003274661805836407369665432566039311865085952 * U :=
    (by decide : 5 ≤ 2923003274661805836407369665432566039311865085952).trans (Nat.le_mul_of_pos_right 2923003274661805836407369665432566039311865085952 hU1)
  have hA7 : 7 ≤ 2923003274661805836407369665432566039311865085952 * U :=
    (by decide : 7 ≤ 2923003274661805836407369665432566039311865085952).trans (Nat.le_mul_of_pos_right 2923003274661805836407369665432566039311865085952 hU1)
  have hB3 : 3 ≤ 1461501637330902918203684832716283019655932542976 * U :=
    (by decide : 3 ≤ 1461501637330902918203684832716283019655932542976).trans (Nat.le_mul_of_pos_right 1461501637330902918203684832716283019655932542976 hU1)
  have hgU : 1 ≤ 22300745198530623141535718272648361505980416 * U := one_le_mul (by decide : 1 ≤ 22300745198530623141535718272648361505980416) hU1
  have hhU : 1 ≤ 324518553658426726783156020576256 * U := one_le_mul (by decide : 1 ≤ 324518553658426726783156020576256) hU1
  zify [hU1, hA, hB, hC, hD, hA3, hA5, hA7, hB3, hgU, hhU]
  simpa using poly_id_216s161 (U : ℤ)

lemma popc_choose_two_pow_nine_of_mod_216_eq_one_six_one {m : ℕ}
    (hmod : m % 216 = 161) :
    popc (Nat.choose (2 ^ m) 9) % 2 = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m = 216 * s + 161 := ⟨m / 216, by omega⟩
  have hm9 : 9 ≤ m := by omega
  rw [choose_two_pow_nine m hm9, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) / 2835 =
        hexEval (digits_216s161 s) := by
    set U := 16 ^ (54 * s) with hUdef
    have h16 : 16 ^ (54 * s) = 2 ^ (216 * s) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 2923003274661805836407369665432566039311865085952 * U := by
      rw [hs, hUdef, pow_add, h16, show (2 : ℕ) ^ 161 = 2923003274661805836407369665432566039311865085952 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 1461501637330902918203684832716283019655932542976 * U := by
      have : m - 1 = 216 * s + 160 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 160 = 1461501637330902918203684832716283019655932542976 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 730750818665451459101842416358141509827966271488 * U := by
      have : m - 2 = 216 * s + 159 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 159 = 730750818665451459101842416358141509827966271488 from rfl]
      ring
    have h2m3 : 2 ^ (m - 3) = 365375409332725729550921208179070754913983135744 * U := by
      have : m - 3 = 216 * s + 158 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 158 = 365375409332725729550921208179070754913983135744 from rfl]
      ring
    have hmul := hexEval_digits_216s161_mul_2835 s
    rw [h2m, h2m1, h2m2, h2m3]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2835) hmul.symm
  rw [hex, popc_hexEval_digits_216s161 s]
  omega


lemma a_ne_zero_two_pow_mod216_eq_one_six_one {m : ℕ} (hm : 161 ≤ m) (hmod : m % 216 = 161) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 9 (by decide) ?_
    (popc_choose_two_pow_nine_of_mod_216_eq_one_six_one hmod)
  have : 9 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 9 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  exact this

/- Digit list for the odd part of `C(2^{216s+185}, 9)`, `s ≥ 0`. LSB first. -/

def blockA27_185 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 14, 3, 5, 5, 0, 7, 12, 12, 8, 3, 9, 10, 10]
def blockB27_185 : List ℕ := [2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 13, 9, 4, 10, 11, 11, 6, 13, 2, 3, 15, 9, 15, 0, 1, 12]
def blockC27_185 : List ℕ := [0, 4, 14, 1, 11, 10, 3, 2, 7, 5, 9, 3, 7, 0, 0, 9, 7, 12, 10, 14, 8, 12, 5, 5, 14, 12, 1]
def blockD27_185 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10, 8, 13, 11, 15, 9, 13, 6, 6, 15, 13, 2, 1]
def blockE27_185 : List ℕ := [10, 6, 1, 7, 8, 8, 3, 10, 15, 15, 11, 6, 12, 13, 13, 8, 15, 4, 5, 1, 12, 1, 3, 3, 14, 4, 10]
def blockF27_185 : List ℕ := [5, 5, 15, 1, 7, 6, 14, 8, 13, 10, 10, 4, 7, 12, 11, 3, 14, 2, 0, 0, 10, 12, 1, 1, 9, 3, 8]
def conn1_185 : List ℕ := [5, 12, 1, 2, 14, 8, 14, 15, 15, 10, 1, 7, 7, 3, 14, 3, 5, 9, 10]
def conn2_185 : List ℕ := [2, 8, 8, 4, 15, 4, 6, 6, 1, 8, 13, 13, 9, 4, 10, 11, 11, 12, 2]
def conn3_185 : List ℕ := [0, 4, 14, 1, 11, 10, 3, 2, 7, 5, 9, 3, 7, 0, 0, 9, 7, 12, 0]
def conn4_185 : List ℕ := [5, 15, 2, 12, 11, 4, 3, 8, 6, 10, 4, 8, 1, 1, 10, 8, 13, 11]
def conn5_185 : List ℕ := [10, 6, 1, 7, 8, 8, 3, 10, 15, 15, 11, 6, 12, 13, 13, 8, 15, 4]
def conn6_185 : List ℕ := [5, 5, 15, 1, 7, 6, 14, 8, 13, 10, 10, 4, 7, 12, 11, 3, 14, 2]

def digits_216s185 (s : ℕ) : List ℕ :=
  [9]
    ++ List.flatten (List.replicate (18 * s + 14) [3, 14, 8])
    ++ [3, 14, 12, 12]
    ++ List.flatten (List.replicate (18 * s + 14) [8, 6, 13])
    ++ [8, 6, 15, 11]
    ++ List.flatten (List.replicate (2 * s + 1) blockA27_185)
    ++ conn1_185
    ++ List.flatten (List.replicate (2 * s + 1) blockB27_185)
    ++ conn2_185
    ++ List.flatten (List.replicate (2 * s + 1) blockC27_185)
    ++ conn3_185
    ++ List.flatten (List.replicate (2 * s + 1) blockD27_185)
    ++ conn4_185
    ++ List.flatten (List.replicate (2 * s + 1) blockE27_185)
    ++ conn5_185
    ++ List.flatten (List.replicate (2 * s + 1) blockF27_185)
    ++ conn6_185

lemma digits_216s185_lt (s : ℕ) : ∀ d ∈ digits_216s185 s, d < 16 := by
  intro d hd
  unfold digits_216s185 blockA27_185 blockB27_185 blockC27_185 blockD27_185
    blockE27_185 blockF27_185 conn1_185 conn2_185 conn3_185 conn4_185
    conn5_185 conn6_185 at hd
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, List.mem_replicate,
    List.mem_flatten] at hd
  aesop

lemma popc_blockA27_185 : (List.map popc blockA27_185).sum = 57 := by
  unfold blockA27_185; decide

lemma popc_blockB27_185 : (List.map popc blockB27_185).sum = 53 := by
  unfold blockB27_185; decide

lemma popc_blockC27_185 : (List.map popc blockC27_185).sum = 50 := by
  unfold blockC27_185; decide

lemma popc_blockD27_185 : (List.map popc blockD27_185).sum = 55 := by
  unfold blockD27_185; decide

lemma popc_blockE27_185 : (List.map popc blockE27_185).sum = 57 := by
  unfold blockE27_185; decide

lemma popc_blockF27_185 : (List.map popc blockF27_185).sum = 51 := by
  unfold blockF27_185; decide

lemma popc_conn1_185 : (List.map popc conn1_185).sum = 43 := by
  unfold conn1_185; decide

lemma popc_conn2_185 : (List.map popc conn2_185).sum = 35 := by
  unfold conn2_185; decide

lemma popc_conn3_185 : (List.map popc conn3_185).sum = 32 := by
  unfold conn3_185; decide

lemma popc_conn4_185 : (List.map popc conn4_185).sum = 33 := by
  unfold conn4_185; decide

lemma popc_conn5_185 : (List.map popc conn5_185).sum = 41 := by
  unfold conn5_185; decide

lemma popc_conn6_185 : (List.map popc conn6_185).sum = 40 := by
  unfold conn6_185; decide

lemma popc_digits_216s185 (s : ℕ) :
    (List.map popc (digits_216s185 s)).sum = 736 + 862 * s := by
  have h0 : popc 0 = 0 := by decide
  have h1 : popc 1 = 1 := by decide
  have h2 : popc 2 = 1 := by decide
  have h3 : popc 3 = 2 := by decide
  have h4 : popc 4 = 1 := by decide
  have h5 : popc 5 = 2 := by decide
  have h6 : popc 6 = 2 := by decide
  have h7 : popc 7 = 3 := by decide
  have h8 : popc 8 = 1 := by decide
  have h9 : popc 9 = 2 := by decide
  have h10 : popc 10 = 2 := by decide
  have h11 : popc 11 = 3 := by decide
  have h12 : popc 12 = 2 := by decide
  have h13 : popc 13 = 3 := by decide
  have h14 : popc 14 = 3 := by decide
  have h15 : popc 15 = 4 := by decide
  unfold digits_216s185
  simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, map_popc_flatten_replicate]
  rw [popc_blockA27_185, popc_blockB27_185, popc_blockC27_185, popc_blockD27_185,
    popc_blockE27_185, popc_blockF27_185, popc_conn1_185, popc_conn2_185,
    popc_conn3_185, popc_conn4_185, popc_conn5_185, popc_conn6_185]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  omega

lemma popc_hexEval_digits_216s185 (s : ℕ) :
    popc (hexEval (digits_216s185 s)) = 736 + 862 * s := by
  rw [popc_hexEval _ (digits_216s185_lt s), popc_digits_216s185 s]

lemma hexEval_blockA27_185 : hexEval blockA27_185 = 216231233813322076505602018648517 := by
  unfold blockA27_185; decide

lemma hexEval_blockB27_185 : hexEval blockB27_185 = 244733921594961672614598790826114 := by
  unfold blockB27_185; decide

lemma hexEval_blockC27_185 : hexEval blockC27_185 = 36629960201303898613971755408960 := by
  unfold blockC27_185; decide

lemma hexEval_blockD27_185 : hexEval blockD27_185 = 23923942756476608782250302751477 := by
  unfold blockD27_185; decide

lemma hexEval_blockE27_185 : hexEval blockE27_185 = 209019710398690371465976329302378 := by
  unfold blockE27_185; decide

lemma hexEval_blockF27_185 : hexEval blockF27_185 = 166780787541561813376740148846421 := by
  unfold blockF27_185; decide

lemma hexEval_conn1_185 : hexEval conn1_185 = 49976712872633949888965 := by
  unfold conn1_185; decide

lemma hexEval_conn2_185 : hexEval conn2_185 = 13202845516414520871042 := by
  unfold conn2_185; decide

lemma hexEval_conn3_185 : hexEval conn3_185 = 3681280397580922723904 := by
  unfold conn3_185; decide

lemma hexEval_conn4_185 : hexEval conn4_185 = 3496383508833645609717 := by
  unfold conn4_185; decide

lemma hexEval_conn5_185 : hexEval conn5_185 = 1467514945822983221610 := by
  unfold conn5_185; decide

lemma hexEval_conn6_185 : hexEval conn6_185 = 852857721068521463637 := by
  unfold conn6_185; decide

lemma length_blockA27_185 : blockA27_185.length = 27 := by unfold blockA27_185; decide
lemma length_blockB27_185 : blockB27_185.length = 27 := by unfold blockB27_185; decide
lemma length_blockC27_185 : blockC27_185.length = 27 := by unfold blockC27_185; decide
lemma length_blockD27_185 : blockD27_185.length = 27 := by unfold blockD27_185; decide
lemma length_blockE27_185 : blockE27_185.length = 27 := by unfold blockE27_185; decide
lemma length_blockF27_185 : blockF27_185.length = 27 := by unfold blockF27_185; decide
lemma length_conn1_185 : conn1_185.length = 19 := by unfold conn1_185; decide
lemma length_conn2_185 : conn2_185.length = 19 := by unfold conn2_185; decide
lemma length_conn3_185 : conn3_185.length = 19 := by unfold conn3_185; decide
lemma length_conn4_185 : conn4_185.length = 18 := by unfold conn4_185; decide
lemma length_conn5_185 : conn5_185.length = 18 := by unfold conn5_185; decide
lemma length_conn6_185 : conn6_185.length = 18 := by unfold conn6_185; decide

lemma hexEval_digits_216s185_eq (s : ℕ) :
    hexEval (digits_216s185 s) =
      9
        + 16 * (2275 * ∑ i ∈ Finset.range (18 * s + 14), 16 ^ (3 * i))
        + 16 ^ (54 * s + 43) * 52451
        + 16 ^ (54 * s + 47) * (3432 * ∑ i ∈ Finset.range (18 * s + 14), 16 ^ (3 * i))
        + 16 ^ (108 * s + 89) * 49000
        + 16 ^ (108 * s + 93) * (216231233813322076505602018648517 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (162 * s + 120) * 49976712872633949888965
        + 16 ^ (162 * s + 139) * (244733921594961672614598790826114 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (216 * s + 166) * 13202845516414520871042
        + 16 ^ (216 * s + 185) * (36629960201303898613971755408960 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (270 * s + 212) * 3681280397580922723904
        + 16 ^ (270 * s + 231) * (23923942756476608782250302751477 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (324 * s + 258) * 3496383508833645609717
        + 16 ^ (324 * s + 276) * (209019710398690371465976329302378 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (378 * s + 303) * 1467514945822983221610
        + 16 ^ (378 * s + 321) * (166780787541561813376740148846421 *
            ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i))
        + 16 ^ (432 * s + 348) * 852857721068521463637 := by
  unfold digits_216s185
  repeat rw [hexEval_append]
  rw [hexEval_singleton]
  repeat rw [hexEval_flatten_replicate]
  rw [hexEval_3e8, hexEval_3ecc, hexEval_86d, hexEval_86fb,
    hexEval_blockA27_185, hexEval_blockB27_185, hexEval_blockC27_185,
    hexEval_blockD27_185, hexEval_blockE27_185, hexEval_blockF27_185,
    hexEval_conn1_185, hexEval_conn2_185, hexEval_conn3_185,
    hexEval_conn4_185, hexEval_conn5_185, hexEval_conn6_185]
  simp only [List.length_cons, List.length_nil, List.length_append,
    length_flatten_replicate, length_blockA27_185, length_blockB27_185,
    length_blockC27_185, length_blockD27_185, length_blockE27_185,
    length_blockF27_185, length_conn1_185, length_conn2_185,
    length_conn3_185, length_conn4_185, length_conn5_185, length_conn6_185]
  have f1 : (0 + 1 : ℕ) = 1 := rfl
  have f3 : (0 + 1 + 1 + 1 : ℕ) = 3 := rfl
  have f4 : (0 + 1 + 1 + 1 + 1 : ℕ) = 4 := rfl
  rw [f1, f3, f4]
  have e1 : 1 + (18 * s + 14) * 3 = 54 * s + 43 := by omega
  rw [e1]
  have e2 : 54 * s + 43 + 4 = 54 * s + 47 := by omega
  rw [e2]
  have e3 : 54 * s + 47 + (18 * s + 14) * 3 = 108 * s + 89 := by omega
  rw [e3]
  have e4 : 108 * s + 89 + 4 = 108 * s + 93 := by omega
  rw [e4]
  have e5 : 108 * s + 93 + (2 * s + 1) * 27 = 162 * s + 120 := by omega
  rw [e5]
  have e6 : 162 * s + 120 + 19 = 162 * s + 139 := by omega
  rw [e6]
  have e7 : 162 * s + 139 + (2 * s + 1) * 27 = 216 * s + 166 := by omega
  rw [e7]
  have e8 : 216 * s + 166 + 19 = 216 * s + 185 := by omega
  rw [e8]
  have e9 : 216 * s + 185 + (2 * s + 1) * 27 = 270 * s + 212 := by omega
  rw [e9]
  have e10 : 270 * s + 212 + 19 = 270 * s + 231 := by omega
  rw [e10]
  have e11 : 270 * s + 231 + (2 * s + 1) * 27 = 324 * s + 258 := by omega
  rw [e11]
  have e12 : 324 * s + 258 + 18 = 324 * s + 276 := by omega
  rw [e12]
  have e13 : 324 * s + 276 + (2 * s + 1) * 27 = 378 * s + 303 := by omega
  rw [e13]
  have e14 : 378 * s + 303 + 18 = 378 * s + 321 := by omega
  rw [e14]
  have e15 : 378 * s + 321 + (2 * s + 1) * 27 = 432 * s + 348 := by omega
  rw [e15]
  simp [hexEval_singleton]

lemma poly_id_216s185 (U : ℤ) :
    25515
      + 25200 * (374144419156711147060143317175368453031918731001856 * U - 1)
      + 890155931427997453145123538578935773111764402159545913180160 * U
      + 932149607704922093429614729346338462791199783502909125165056 * U * (374144419156711147060143317175368453031918731001856 * U - 1)
      + 20390487055376690178266699818936922072368308830099953427456457831899801045237239495234984147538759023855077949440000 * U ^ 2
      + 18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 * U ^ 2 * (324518553658426726783156020576256 * U - 1)
      + 442301762270759764867046062801151673664728272295056975640349314236758507190632917567843262218972875665301367307998851921348478727573502569751001168645708704208751322726400 * U ^ 3
      + 504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 * U ^ 3 * (324518553658426726783156020576256 * U - 1)
      + 2865086417723669812224573027885055324150151714018075044679358757739672637720204317100267174849947359790200047609603017303038274235545221344578184479906072618017369006426197150734025326164834826505092049114091473923780766597120 * U ^ 4
      + 1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 * U ^ 4 * (324518553658426726783156020576256 * U - 1)
      + 19587918327664736323258980254686545400071300655830619679018059024459099832430312504186736944776427450791362246765450968451274477418662414886138093598130204282135819578962333909242542772770338894137672639037170560422536155896511818031826149813078222498166501062530182556161188823040 * U ^ 5
      + 29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 * U ^ 5 * (324518553658426726783156020576256 * U - 1)
      + 456170977995945743621296085322827387591164658679064291989608096257360616153497824871243624393356417408223999948671352433818426548070973249121079759656825668448841624055135278479045001324256833659149235925155134088986055449220944104739228009691400200373962734603175186294929396486933527772356992111235683567230175651391121708871812382720 * U ^ 6
      + 396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 * U ^ 6 * (324518553658426726783156020576256 * U - 1)
      + 293420424431978738917507593204524071385586764409210366179194617985749583013574513810373095547068641796033373012089678760455009438803503048514579434934908531058819483480871446623316542547981820688962234721269148295472055002654645524416990840171639423528189107087294213378829696844043429161150946427895494054365956040630308586947107200101663216330735624426558204169484536091763275787245977600 * U ^ 7
      + 485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 * U ^ 7 * (324518553658426726783156020576256 * U - 1)
      + 261326596963659217563319593154968208853160370736200266646948339599494371316915382432435244970717063661690843406237165920908571899887229436914031329823947521960832131553000761059574272878130715008598471083726560280301781894359160371149221868569866625683773476571928066099827175972420518213023327187261537793697042108905114443056353346448306009309595185671440290902487933874108365404898878174258801683909742346266267591225158554402600809052241920 * U ^ 8
    =
      (49039857307708443467467104868809893875799651909875269632 * U - 1) * (24519928653854221733733552434404946937899825954937634816 * U - 1) *
        (49039857307708443467467104868809893875799651909875269632 * U - 3) * (12259964326927110866866776217202473468949912977468817408 * U - 1) *
        (49039857307708443467467104868809893875799651909875269632 * U - 5) * (24519928653854221733733552434404946937899825954937634816 * U - 3) *
        (49039857307708443467467104868809893875799651909875269632 * U - 7) * (6129982163463555433433388108601236734474956488734408704 * U - 1) := by
  ring

lemma dist_216s185 (G H U p43 p47 p89 p93 p120 p139 p166 p185 p212 p231 p258 p276 p303 p321 p348 : ℕ) :
    (9 + 16 * (2275 * G) + p43 * U * 52451 + p47 * U * (3432 * G) + p89 * (U * U) * 49000 + p93 * (U * U) * (216231233813322076505602018648517 * H) + p120 * (U * U * U) * 49976712872633949888965 + p139 * (U * U * U) * (244733921594961672614598790826114 * H) + p166 * (U * U * U * U) * 13202845516414520871042 + p185 * (U * U * U * U) * (36629960201303898613971755408960 * H) + p212 * (U * U * U * U * U) * 3681280397580922723904 + p231 * (U * U * U * U * U) * (23923942756476608782250302751477 * H) + p258 * (U * U * U * U * U * U) * 3496383508833645609717 + p276 * (U * U * U * U * U * U) * (209019710398690371465976329302378 * H) + p303 * (U * U * U * U * U * U * U) * 1467514945822983221610 + p321 * (U * U * U * U * U * U * U) * (166780787541561813376740148846421 * H) + p348 * (U * U * U * U * U * U * U * U) * 852857721068521463637) * 2835
    =
      25515
        + 2835 * 16 * 2275 * G
        + 2835 * p43 * 52451 * U
        + 2835 * p47 * 3432 * G * U
        + 2835 * p89 * 49000 * (U * U)
        + 2835 * p93 * 216231233813322076505602018648517 * H * (U * U)
        + 2835 * p120 * 49976712872633949888965 * (U * U * U)
        + 2835 * p139 * 244733921594961672614598790826114 * H * (U * U * U)
        + 2835 * p166 * 13202845516414520871042 * (U * U * U * U)
        + 2835 * p185 * 36629960201303898613971755408960 * H * (U * U * U * U)
        + 2835 * p212 * 3681280397580922723904 * (U * U * U * U * U)
        + 2835 * p231 * 23923942756476608782250302751477 * H * (U * U * U * U * U)
        + 2835 * p258 * 3496383508833645609717 * (U * U * U * U * U * U)
        + 2835 * p276 * 209019710398690371465976329302378 * H * (U * U * U * U * U * U)
        + 2835 * p303 * 1467514945822983221610 * (U * U * U * U * U * U * U)
        + 2835 * p321 * 166780787541561813376740148846421 * H * (U * U * U * U * U * U * U)
        + 2835 * p348 * 852857721068521463637 * (U * U * U * U * U * U * U * U) := by
  ring

lemma hexEval_digits_216s185_mul_2835 (s : ℕ) :
    hexEval (digits_216s185 s) * 2835 =
      (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 1) * (24519928653854221733733552434404946937899825954937634816 * 16 ^ (54 * s) - 1) *
        (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 3) * (12259964326927110866866776217202473468949912977468817408 * 16 ^ (54 * s) - 1) *
        (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 5) * (24519928653854221733733552434404946937899825954937634816 * 16 ^ (54 * s) - 3) *
        (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 7) * (6129982163463555433433388108601236734474956488734408704 * 16 ^ (54 * s) - 1) := by
  have hex := hexEval_digits_216s185_eq s
  set G := ∑ i ∈ Finset.range (18 * s + 14), 16 ^ (3 * i) with hGdef
  set H := ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i) with hHdef
  set U := 16 ^ (54 * s) with hUdef
  set p43 := 16 ^ 43 with hp43
  set p47 := 16 ^ 47 with hp47
  set p89 := 16 ^ 89 with hp89
  set p93 := 16 ^ 93 with hp93
  set p120 := 16 ^ 120 with hp120
  set p139 := 16 ^ 139 with hp139
  set p166 := 16 ^ 166 with hp166
  set p185 := 16 ^ 185 with hp185
  set p212 := 16 ^ 212 with hp212
  set p231 := 16 ^ 231 with hp231
  set p258 := 16 ^ 258 with hp258
  set p276 := 16 ^ 276 with hp276
  set p303 := 16 ^ 303 with hp303
  set p321 := 16 ^ 321 with hp321
  set p348 := 16 ^ 348 with hp348
  have hGpow : ∀ i, 16 ^ (3 * i) = 4096 ^ i := by
    intro i; rw [show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
  have hG : G * 4095 = 374144419156711147060143317175368453031918731001856 * U - 1 := by
    rw [hGdef, hUdef]
    have : ∑ i ∈ Finset.range (18 * s + 14), 16 ^ (3 * i) =
        ∑ i ∈ Finset.range (18 * s + 14), 4096 ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hGpow i
    rw [this]
    have hpow : 16 ^ (54 * s + 42) = 4096 ^ (18 * s + 14) := by
      have : 54 * s + 42 = 3 * (18 * s + 14) := by omega
      rw [this, show (4096 : ℕ) = 16 ^ 3 from rfl, ← pow_mul]
    have : 16 ^ (54 * s + 42) = 374144419156711147060143317175368453031918731001856 * 16 ^ (54 * s) := by
      have : 54 * s + 42 = 42 + 54 * s := by omega
      rw [this, pow_add, show (16 : ℕ) ^ 42 = 374144419156711147060143317175368453031918731001856 from rfl]
    have hgs := geom_sum_4096 (18 * s + 14)
    have hle : 1 ≤ 4096 ^ (18 * s + 14) := Nat.one_le_pow _ _ (by decide)
    omega
  have hHpow : ∀ i, 16 ^ (27 * i) = (16 ^ 27) ^ i := by
    intro i; rw [← pow_mul]
  have hH : H * (16 ^ 27 - 1) = 324518553658426726783156020576256 * U - 1 := by
    rw [hHdef, hUdef]
    have : ∑ i ∈ Finset.range (2 * s + 1), 16 ^ (27 * i) =
        ∑ i ∈ Finset.range (2 * s + 1), (16 ^ 27) ^ i := by
      apply Finset.sum_congr rfl
      intro i hi; exact hHpow i
    rw [this]
    have : 16 ^ (54 * s + 27) = (16 ^ 27) ^ (2 * s + 1) := by
      have : 54 * s + 27 = 27 * (2 * s + 1) := by omega
      rw [this, ← pow_mul]
    have : 16 ^ (54 * s + 27) = 324518553658426726783156020576256 * 16 ^ (54 * s) := by
      have : 54 * s + 27 = 27 + 54 * s := by omega
      rw [this, pow_add, show (16 : ℕ) ^ 27 = 324518553658426726783156020576256 from rfl]
    have hhs := geom_sum_16_pow_27 (2 * s + 1)
    have hle : 1 ≤ (16 ^ 27) ^ (2 * s + 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hU1 : 1 ≤ U := by
    rw [hUdef]; exact Nat.one_le_pow _ _ (by decide)
  have pw_3ecc : 16 ^ (54 * s + 43) = p43 * U := by
    have : 54 * s + 43 = 43 + 54 * s := by omega
    rw [this, pow_add, hp43, hUdef]
  have pw_86d : 16 ^ (54 * s + 47) = p47 * U := by
    have : 54 * s + 47 = 47 + 54 * s := by omega
    rw [this, pow_add, hp47, hUdef]
  have pw_86fb : 16 ^ (108 * s + 89) = p89 * (U * U) := by
    have : 108 * s + 89 = 89 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp89, hUdef, pow_add]
  have pw_A : 16 ^ (108 * s + 93) = p93 * (U * U) := by
    have : 108 * s + 93 = 93 + (54 * s + 54 * s) := by omega
    rw [this, pow_add, hp93, hUdef, pow_add]
  have pw_c1 : 16 ^ (162 * s + 120) = p120 * (U * U * U) := by
    have : 162 * s + 120 = 120 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp120, hUdef, pow_add, pow_add]
  have pw_B : 16 ^ (162 * s + 139) = p139 * (U * U * U) := by
    have : 162 * s + 139 = 139 + (54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp139, hUdef, pow_add, pow_add]
  have pw_c2 : 16 ^ (216 * s + 166) = p166 * (U * U * U * U) := by
    have : 216 * s + 166 = 166 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp166, hUdef, pow_add, pow_add, pow_add]
  have pw_C : 16 ^ (216 * s + 185) = p185 * (U * U * U * U) := by
    have : 216 * s + 185 = 185 + (54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp185, hUdef, pow_add, pow_add, pow_add]
  have pw_c3 : 16 ^ (270 * s + 212) = p212 * (U * U * U * U * U) := by
    have : 270 * s + 212 = 212 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp212, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw_D : 16 ^ (270 * s + 231) = p231 * (U * U * U * U * U) := by
    have : 270 * s + 231 = 231 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp231, hUdef, pow_add, pow_add, pow_add, pow_add]
  have pw_c4 : 16 ^ (324 * s + 258) = p258 * (U * U * U * U * U * U) := by
    have : 324 * s + 258 = 258 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp258, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_E : 16 ^ (324 * s + 276) = p276 * (U * U * U * U * U * U) := by
    have : 324 * s + 276 = 276 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp276, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_c5 : 16 ^ (378 * s + 303) = p303 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 303 = 303 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp303, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_F : 16 ^ (378 * s + 321) = p321 * (U * U * U * U * U * U * U) := by
    have : 378 * s + 321 = 321 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp321, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have pw_c6 : 16 ^ (432 * s + 348) = p348 * (U * U * U * U * U * U * U * U) := by
    have : 432 * s + 348 = 348 + (54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s + 54 * s) := by omega
    rw [this, pow_add, hp348, hUdef, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
  have factG0 : (2835 * 16 * 2275 : ℕ) = 4095 * 25200 := by decide
  have factG1 : (2835 * p47 * 3432 : ℕ) = 4095 * 932149607704922093429614729346338462791199783502909125165056 := by
    rw [hp47]; decide
  have factHA : (2835 * p93 * 216231233813322076505602018648517 : ℕ) = (16 ^ 27 - 1) * 18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 := by
    rw [hp93]; decide
  have factHB : (2835 * p139 * 244733921594961672614598790826114 : ℕ) = (16 ^ 27 - 1) * 504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 := by
    rw [hp139]; decide
  have factHC : (2835 * p185 * 36629960201303898613971755408960 : ℕ) = (16 ^ 27 - 1) * 1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 := by
    rw [hp185]; decide
  have factHD : (2835 * p231 * 23923942756476608782250302751477 : ℕ) = (16 ^ 27 - 1) * 29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 := by
    rw [hp231]; decide
  have factHE : (2835 * p276 * 209019710398690371465976329302378 : ℕ) = (16 ^ 27 - 1) * 396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 := by
    rw [hp276]; decide
  have factHF : (2835 * p321 * 166780787541561813376740148846421 : ℕ) = (16 ^ 27 - 1) * 485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 := by
    rw [hp321]; decide
  have factC1 : (2835 * p43 * 52451 : ℕ) = 890155931427997453145123538578935773111764402159545913180160 := by
    rw [hp43]; decide
  have factC2 : (2835 * p89 * 49000 : ℕ) = 20390487055376690178266699818936922072368308830099953427456457831899801045237239495234984147538759023855077949440000 := by
    rw [hp89]; decide
  have factC3 : (2835 * p120 * 49976712872633949888965 : ℕ) = 442301762270759764867046062801151673664728272295056975640349314236758507190632917567843262218972875665301367307998851921348478727573502569751001168645708704208751322726400 := by
    rw [hp120]; decide
  have factC4 : (2835 * p166 * 13202845516414520871042 : ℕ) = 2865086417723669812224573027885055324150151714018075044679358757739672637720204317100267174849947359790200047609603017303038274235545221344578184479906072618017369006426197150734025326164834826505092049114091473923780766597120 := by
    rw [hp166]; decide
  have factC5 : (2835 * p212 * 3681280397580922723904 : ℕ) = 19587918327664736323258980254686545400071300655830619679018059024459099832430312504186736944776427450791362246765450968451274477418662414886138093598130204282135819578962333909242542772770338894137672639037170560422536155896511818031826149813078222498166501062530182556161188823040 := by
    rw [hp212]; decide
  have factC6 : (2835 * p258 * 3496383508833645609717 : ℕ) = 456170977995945743621296085322827387591164658679064291989608096257360616153497824871243624393356417408223999948671352433818426548070973249121079759656825668448841624055135278479045001324256833659149235925155134088986055449220944104739228009691400200373962734603175186294929396486933527772356992111235683567230175651391121708871812382720 := by
    rw [hp258]; decide
  have factC7 : (2835 * p303 * 1467514945822983221610 : ℕ) = 293420424431978738917507593204524071385586764409210366179194617985749583013574513810373095547068641796033373012089678760455009438803503048514579434934908531058819483480871446623316542547981820688962234721269148295472055002654645524416990840171639423528189107087294213378829696844043429161150946427895494054365956040630308586947107200101663216330735624426558204169484536091763275787245977600 := by
    rw [hp303]; decide
  have factC8 : (2835 * p348 * 852857721068521463637 : ℕ) = 261326596963659217563319593154968208853160370736200266646948339599494371316915382432435244970717063661690843406237165920908571899887229436914031329823947521960832131553000761059574272878130715008598471083726560280301781894359160371149221868569866625683773476571928066099827175972420518213023327187261537793697042108905114443056353346448306009309595185671440290902487933874108365404898878174258801683909742346266267591225158554402600809052241920 := by
    rw [hp348]; decide
  have hex2835 :
      hexEval (digits_216s185 s) * 2835 =
        25515 + 25200 * (374144419156711147060143317175368453031918731001856 * U - 1) + 890155931427997453145123538578935773111764402159545913180160 * U
          + 932149607704922093429614729346338462791199783502909125165056 * U * (374144419156711147060143317175368453031918731001856 * U - 1) + 20390487055376690178266699818936922072368308830099953427456457831899801045237239495234984147538759023855077949440000 * (U * U)
          + 18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 * (U * U) * (324518553658426726783156020576256 * U - 1)
          + 442301762270759764867046062801151673664728272295056975640349314236758507190632917567843262218972875665301367307998851921348478727573502569751001168645708704208751322726400 * (U * U * U)
          + 504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 * (U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 2865086417723669812224573027885055324150151714018075044679358757739672637720204317100267174849947359790200047609603017303038274235545221344578184479906072618017369006426197150734025326164834826505092049114091473923780766597120 * (U * U * U * U)
          + 1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 * (U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 19587918327664736323258980254686545400071300655830619679018059024459099832430312504186736944776427450791362246765450968451274477418662414886138093598130204282135819578962333909242542772770338894137672639037170560422536155896511818031826149813078222498166501062530182556161188823040 * (U * U * U * U * U)
          + 29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 * (U * U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 456170977995945743621296085322827387591164658679064291989608096257360616153497824871243624393356417408223999948671352433818426548070973249121079759656825668448841624055135278479045001324256833659149235925155134088986055449220944104739228009691400200373962734603175186294929396486933527772356992111235683567230175651391121708871812382720 * (U * U * U * U * U * U)
          + 396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 * (U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 293420424431978738917507593204524071385586764409210366179194617985749583013574513810373095547068641796033373012089678760455009438803503048514579434934908531058819483480871446623316542547981820688962234721269148295472055002654645524416990840171639423528189107087294213378829696844043429161150946427895494054365956040630308586947107200101663216330735624426558204169484536091763275787245977600 * (U * U * U * U * U * U * U)
          + 485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 * (U * U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1)
          + 261326596963659217563319593154968208853160370736200266646948339599494371316915382432435244970717063661690843406237165920908571899887229436914031329823947521960832131553000761059574272878130715008598471083726560280301781894359160371149221868569866625683773476571928066099827175972420518213023327187261537793697042108905114443056353346448306009309595185671440290902487933874108365404898878174258801683909742346266267591225158554402600809052241920 * (U * U * U * U * U * U * U * U) := by
    rw [hex, pw_3ecc, pw_86d, pw_86fb, pw_A, pw_c1, pw_B, pw_c2, pw_C, pw_c3,
      pw_D, pw_c4, pw_E, pw_c5, pw_F, pw_c6]
    rw [dist_216s185 G H U p43 p47 p89 p93 p120 p139 p166 p185 p212 p231 p258 p276 p303 p321 p348]
    have G0 : 2835 * 16 * 2275 * G = 25200 * (374144419156711147060143317175368453031918731001856 * U - 1) := by
      rw [factG0]
      have : 4095 * 25200 * G = 25200 * (G * 4095) := by ring
      rw [this, hG]
    have G1 : 2835 * p47 * 3432 * G * U = 932149607704922093429614729346338462791199783502909125165056 * U * (374144419156711147060143317175368453031918731001856 * U - 1) := by
      rw [factG1]
      have : 4095 * 932149607704922093429614729346338462791199783502909125165056 * G * U = 932149607704922093429614729346338462791199783502909125165056 * U * (G * 4095) := by ring
      rw [this, hG]
    have HA : 2835 * p93 * 216231233813322076505602018648517 * H * (U * U) =
        18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 * (U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHA]
      have : (16 ^ 27 - 1) * 18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 * H * (U * U) =
          18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 * (U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HB : 2835 * p139 * 244733921594961672614598790826114 * H * (U * U * U) =
        504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 * (U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHB]
      have : (16 ^ 27 - 1) * 504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 * H * (U * U * U) =
          504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 * (U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HC : 2835 * p185 * 36629960201303898613971755408960 * H * (U * U * U * U) =
        1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 * (U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHC]
      have : (16 ^ 27 - 1) * 1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 * H * (U * U * U * U) =
          1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 * (U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HD : 2835 * p231 * 23923942756476608782250302751477 * H * (U * U * U * U * U) =
        29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 * (U * U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHD]
      have : (16 ^ 27 - 1) * 29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 * H * (U * U * U * U * U) =
          29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 * (U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HE : 2835 * p276 * 209019710398690371465976329302378 * H * (U * U * U * U * U * U) =
        396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 * (U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHE]
      have : (16 ^ 27 - 1) * 396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 * H * (U * U * U * U * U * U) =
          396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 * (U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have HF : 2835 * p321 * 166780787541561813376740148846421 * H * (U * U * U * U * U * U * U) =
        485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 * (U * U * U * U * U * U * U) * (324518553658426726783156020576256 * U - 1) := by
      rw [factHF]
      have : (16 ^ 27 - 1) * 485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 * H * (U * U * U * U * U * U * U) =
          485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 * (U * U * U * U * U * U * U) * (H * (16 ^ 27 - 1)) := by ring
      rw [this, hH]
    have C1 : 2835 * p43 * 52451 * U = 890155931427997453145123538578935773111764402159545913180160 * U := by rw [factC1]
    have C2 : 2835 * p89 * 49000 * (U * U) = 20390487055376690178266699818936922072368308830099953427456457831899801045237239495234984147538759023855077949440000 * (U * U) := by rw [factC2]
    have C3 : 2835 * p120 * 49976712872633949888965 * (U * U * U) = 442301762270759764867046062801151673664728272295056975640349314236758507190632917567843262218972875665301367307998851921348478727573502569751001168645708704208751322726400 * (U * U * U) := by rw [factC3]
    have C4 : 2835 * p166 * 13202845516414520871042 * (U * U * U * U) = 2865086417723669812224573027885055324150151714018075044679358757739672637720204317100267174849947359790200047609603017303038274235545221344578184479906072618017369006426197150734025326164834826505092049114091473923780766597120 * (U * U * U * U) := by rw [factC4]
    have C5 : 2835 * p212 * 3681280397580922723904 * (U * U * U * U * U) = 19587918327664736323258980254686545400071300655830619679018059024459099832430312504186736944776427450791362246765450968451274477418662414886138093598130204282135819578962333909242542772770338894137672639037170560422536155896511818031826149813078222498166501062530182556161188823040 * (U * U * U * U * U) := by rw [factC5]
    have C6 : 2835 * p258 * 3496383508833645609717 * (U * U * U * U * U * U) = 456170977995945743621296085322827387591164658679064291989608096257360616153497824871243624393356417408223999948671352433818426548070973249121079759656825668448841624055135278479045001324256833659149235925155134088986055449220944104739228009691400200373962734603175186294929396486933527772356992111235683567230175651391121708871812382720 * (U * U * U * U * U * U) := by rw [factC6]
    have C7 : 2835 * p303 * 1467514945822983221610 * (U * U * U * U * U * U * U) = 293420424431978738917507593204524071385586764409210366179194617985749583013574513810373095547068641796033373012089678760455009438803503048514579434934908531058819483480871446623316542547981820688962234721269148295472055002654645524416990840171639423528189107087294213378829696844043429161150946427895494054365956040630308586947107200101663216330735624426558204169484536091763275787245977600 * (U * U * U * U * U * U * U) := by rw [factC7]
    have C8 : 2835 * p348 * 852857721068521463637 * (U * U * U * U * U * U * U * U) = 261326596963659217563319593154968208853160370736200266646948339599494371316915382432435244970717063661690843406237165920908571899887229436914031329823947521960832131553000761059574272878130715008598471083726560280301781894359160371149221868569866625683773476571928066099827175972420518213023327187261537793697042108905114443056353346448306009309595185671440290902487933874108365404898878174258801683909742346266267591225158554402600809052241920 * (U * U * U * U * U * U * U * U) := by rw [factC8]
    rw [G0, G1, HA, HB, HC, HD, HE, HF, C1, C2, C3, C4, C5, C6, C7, C8]
  have hex2835' :
      hexEval (digits_216s185 s) * 2835 =
        25515 + 25200 * (374144419156711147060143317175368453031918731001856 * U - 1) + 890155931427997453145123538578935773111764402159545913180160 * U
          + 932149607704922093429614729346338462791199783502909125165056 * U * (374144419156711147060143317175368453031918731001856 * U - 1) + 20390487055376690178266699818936922072368308830099953427456457831899801045237239495234984147538759023855077949440000 * U ^ 2
          + 18171481861569621882811305358684396112743073115700495301697833554838908307216364952383190662958399815791923894943744 * U ^ 2 * (324518553658426726783156020576256 * U - 1)
          + 442301762270759764867046062801151673664728272295056975640349314236758507190632917567843262218972875665301367307998851921348478727573502569751001168645708704208751322726400 * U ^ 3
          + 504295729016778463193277730884557430548773598078146852241770566870321528699650890360008683651864652812728711613485818774731844371173700415526021651847694008832650450567168 * U ^ 3 * (324518553658426726783156020576256 * U - 1)
          + 2865086417723669812224573027885055324150151714018075044679358757739672637720204317100267174849947359790200047609603017303038274235545221344578184479906072618017369006426197150734025326164834826505092049114091473923780766597120 * U ^ 4
          + 1850745787979017418800567970827224916525943299671049846576514289410175028665515048898313532863433930814847625132955399997438883834022062291436537832070805000310486526514112836778480155028818183929041623108048997820488031928320 * U ^ 4 * (324518553658426726783156020576256 * U - 1)
          + 19587918327664736323258980254686545400071300655830619679018059024459099832430312504186736944776427450791362246765450968451274477418662414886138093598130204282135819578962333909242542772770338894137672639037170560422536155896511818031826149813078222498166501062530182556161188823040 * U ^ 5
          + 29638913523851076138000017367680474955314005102807373232141143665030631765987826735586183331460635878874581649031670700792790252334488419812038764138259933165420618596412574162866731610810110760295867149211068189246002147649524396746142738202368692336036436752311332490936942854144 * U ^ 5 * (324518553658426726783156020576256 * U - 1)
          + 456170977995945743621296085322827387591164658679064291989608096257360616153497824871243624393356417408223999948671352433818426548070973249121079759656825668448841624055135278479045001324256833659149235925155134088986055449220944104739228009691400200373962734603175186294929396486933527772356992111235683567230175651391121708871812382720 * U ^ 6
          + 396840498247068569724870993309443382036796762319578487654527506707677873179079298522192735102992090264595262530459605155606731405471151714037280500383263168738614466398657099933368158835915312230083914481934136324997919099518548810662828036716845196404744596339466933548532131062883296652026464328772757765785461791687864788973535625216 * U ^ 6 * (324518553658426726783156020576256 * U - 1)
          + 293420424431978738917507593204524071385586764409210366179194617985749583013574513810373095547068641796033373012089678760455009438803503048514579434934908531058819483480871446623316542547981820688962234721269148295472055002654645524416990840171639423528189107087294213378829696844043429161150946427895494054365956040630308586947107200101663216330735624426558204169484536091763275787245977600 * U ^ 7
          + 485259430644032942795682405023023124152397987016562844843198294225217822174210750534522651731327882794093065329004397707265467392761833227877115005583099403250574614245763009401328900494621671457251260023615489757934006003327300278693259664548049447841729034428747562469775134860357389311958066562082198217317708791999223652348787856226685435138410243750579978058923138408949104538824998912 * U ^ 7 * (324518553658426726783156020576256 * U - 1)
          + 261326596963659217563319593154968208853160370736200266646948339599494371316915382432435244970717063661690843406237165920908571899887229436914031329823947521960832131553000761059574272878130715008598471083726560280301781894359160371149221868569866625683773476571928066099827175972420518213023327187261537793697042108905114443056353346448306009309595185671440290902487933874108365404898878174258801683909742346266267591225158554402600809052241920 * U ^ 8 := by
    rw [hex2835]
    ring
  rw [hex2835']
  have hR :
      (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 1) * (24519928653854221733733552434404946937899825954937634816 * 16 ^ (54 * s) - 1) *
        (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 3) * (12259964326927110866866776217202473468949912977468817408 * 16 ^ (54 * s) - 1) *
        (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 5) * (24519928653854221733733552434404946937899825954937634816 * 16 ^ (54 * s) - 3) *
        (49039857307708443467467104868809893875799651909875269632 * 16 ^ (54 * s) - 7) * (6129982163463555433433388108601236734474956488734408704 * 16 ^ (54 * s) - 1) =
      (49039857307708443467467104868809893875799651909875269632 * U - 1) * (24519928653854221733733552434404946937899825954937634816 * U - 1) *
        (49039857307708443467467104868809893875799651909875269632 * U - 3) * (12259964326927110866866776217202473468949912977468817408 * U - 1) *
        (49039857307708443467467104868809893875799651909875269632 * U - 5) * (24519928653854221733733552434404946937899825954937634816 * U - 3) *
        (49039857307708443467467104868809893875799651909875269632 * U - 7) * (6129982163463555433433388108601236734474956488734408704 * U - 1) := by
    rw [hUdef]
  rw [hR]
  have hA : 1 ≤ 49039857307708443467467104868809893875799651909875269632 * U := one_le_mul (by decide : 1 ≤ 49039857307708443467467104868809893875799651909875269632) hU1
  have hB : 1 ≤ 24519928653854221733733552434404946937899825954937634816 * U := one_le_mul (by decide : 1 ≤ 24519928653854221733733552434404946937899825954937634816) hU1
  have hC : 1 ≤ 12259964326927110866866776217202473468949912977468817408 * U := one_le_mul (by decide : 1 ≤ 12259964326927110866866776217202473468949912977468817408) hU1
  have hD : 1 ≤ 6129982163463555433433388108601236734474956488734408704 * U := one_le_mul (by decide : 1 ≤ 6129982163463555433433388108601236734474956488734408704) hU1
  have hA3 : 3 ≤ 49039857307708443467467104868809893875799651909875269632 * U :=
    (by decide : 3 ≤ 49039857307708443467467104868809893875799651909875269632).trans (Nat.le_mul_of_pos_right 49039857307708443467467104868809893875799651909875269632 hU1)
  have hA5 : 5 ≤ 49039857307708443467467104868809893875799651909875269632 * U :=
    (by decide : 5 ≤ 49039857307708443467467104868809893875799651909875269632).trans (Nat.le_mul_of_pos_right 49039857307708443467467104868809893875799651909875269632 hU1)
  have hA7 : 7 ≤ 49039857307708443467467104868809893875799651909875269632 * U :=
    (by decide : 7 ≤ 49039857307708443467467104868809893875799651909875269632).trans (Nat.le_mul_of_pos_right 49039857307708443467467104868809893875799651909875269632 hU1)
  have hB3 : 3 ≤ 24519928653854221733733552434404946937899825954937634816 * U :=
    (by decide : 3 ≤ 24519928653854221733733552434404946937899825954937634816).trans (Nat.le_mul_of_pos_right 24519928653854221733733552434404946937899825954937634816 hU1)
  have hgU : 1 ≤ 374144419156711147060143317175368453031918731001856 * U := one_le_mul (by decide : 1 ≤ 374144419156711147060143317175368453031918731001856) hU1
  have hhU : 1 ≤ 324518553658426726783156020576256 * U := one_le_mul (by decide : 1 ≤ 324518553658426726783156020576256) hU1
  zify [hU1, hA, hB, hC, hD, hA3, hA5, hA7, hB3, hgU, hhU]
  simpa using poly_id_216s185 (U : ℤ)

lemma popc_choose_two_pow_nine_of_mod_216_eq_one_eight_five {m : ℕ}
    (hmod : m % 216 = 185) :
    popc (Nat.choose (2 ^ m) 9) % 2 = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m = 216 * s + 185 := ⟨m / 216, by omega⟩
  have hm9 : 9 ≤ m := by omega
  rw [choose_two_pow_nine m hm9, popc_mul_two_pow]
  have hex :
      (2 ^ m - 1) * (2 ^ (m - 1) - 1) * (2 ^ m - 3) * (2 ^ (m - 2) - 1) *
          (2 ^ m - 5) * (2 ^ (m - 1) - 3) * (2 ^ m - 7) * (2 ^ (m - 3) - 1) / 2835 =
        hexEval (digits_216s185 s) := by
    set U := 16 ^ (54 * s) with hUdef
    have h16 : 16 ^ (54 * s) = 2 ^ (216 * s) := by
      rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_mul]; ring
    have h2m : 2 ^ m = 49039857307708443467467104868809893875799651909875269632 * U := by
      rw [hs, hUdef, pow_add, h16, show (2 : ℕ) ^ 185 = 49039857307708443467467104868809893875799651909875269632 from rfl]
      ring
    have h2m1 : 2 ^ (m - 1) = 24519928653854221733733552434404946937899825954937634816 * U := by
      have : m - 1 = 216 * s + 184 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 184 = 24519928653854221733733552434404946937899825954937634816 from rfl]
      ring
    have h2m2 : 2 ^ (m - 2) = 12259964326927110866866776217202473468949912977468817408 * U := by
      have : m - 2 = 216 * s + 183 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 183 = 12259964326927110866866776217202473468949912977468817408 from rfl]
      ring
    have h2m3 : 2 ^ (m - 3) = 6129982163463555433433388108601236734474956488734408704 * U := by
      have : m - 3 = 216 * s + 182 := by omega
      rw [this, hUdef, pow_add, h16, show (2 : ℕ) ^ 182 = 6129982163463555433433388108601236734474956488734408704 from rfl]
      ring
    have hmul := hexEval_digits_216s185_mul_2835 s
    rw [h2m, h2m1, h2m2, h2m3]
    exact Nat.div_eq_of_eq_mul_left (by decide : 0 < 2835) hmul.symm
  rw [hex, popc_hexEval_digits_216s185 s]
  omega


lemma a_ne_zero_two_pow_mod216_eq_one_eight_five {m : ℕ} (hm : 185 ≤ m) (hmod : m % 216 = 185) :
    a (2 ^ m) ≠ 0 := by
  refine a_ne_zero_of_witness (2 ^ m) 9 (by decide) ?_
    (popc_choose_two_pow_nine_of_mod_216_eq_one_eight_five hmod)
  have : 9 ≤ 2 ^ m := by
    have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    calc 9 ≤ 16 := by decide
         _ = 2 ^ 4 := by decide
         _ ≤ 2 ^ m := this
  exact this


/- 3-bit odd `n = 2^a + 2^b + 1`. -/

lemma pow_add_of_ge {a b : ℕ} (h : b ≤ a) : (2 : ℕ) ^ a = 2 ^ b * 2 ^ (a - b) := by
  rw [← pow_add]; congr 1; omega

lemma two_pow_succ' (n : ℕ) : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n

lemma choose_two_of_three_bit_odd {a b : ℕ} (hba : b < a) (hb : 1 ≤ b) :
    Nat.choose (2 ^ a + 2 ^ b + 1) 2 =
      2 ^ (b - 1) * (2 ^ (2 * a - b) + 2 ^ (a + 1) + 2 ^ b + 2 ^ (a - b) + 1) := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  have hpow := pow_add_of_ge (Nat.le_of_lt hba)
  have hb2 : 2 ^ b = 2 * 2 ^ (b - 1) := by
    have hb' : b = b - 1 + 1 := by omega
    rw [hb', two_pow_succ']
    simp [Nat.add_sub_cancel]
  have ha : 2 ^ a * 2 ^ (a - b) = 2 ^ (2 * a - b) := by
    rw [← pow_add]; congr 1; omega
  have hb' : 2 ^ b * 2 ^ (a - b) = 2 ^ a := by
    rw [← pow_add]; congr 1; omega
  have hap : 2 * 2 ^ a = 2 ^ (a + 1) := (two_pow_succ' a).symm
  have hprod :
      (2 ^ a + 2 ^ b + 1) * (2 ^ (a - b) + 1) =
        2 ^ (2 * a - b) + 2 ^ (a + 1) + 2 ^ b + 2 ^ (a - b) + 1 := by
    calc
      (2 ^ a + 2 ^ b + 1) * (2 ^ (a - b) + 1)
          = 2 ^ a * 2 ^ (a - b) + 2 ^ a + 2 ^ b * 2 ^ (a - b) + 2 ^ b
              + 2 ^ (a - b) + 1 := by ring
      _ = 2 ^ (2 * a - b) + 2 ^ a + 2 ^ a + 2 ^ b + 2 ^ (a - b) + 1 := by
            rw [ha, hb']
      _ = 2 ^ (2 * a - b) + 2 * 2 ^ a + 2 ^ b + 2 ^ (a - b) + 1 := by ring
      _ = 2 ^ (2 * a - b) + 2 ^ (a + 1) + 2 ^ b + 2 ^ (a - b) + 1 := by
            rw [hap]
  have hdiv :
      (2 ^ a + 2 ^ b + 1) * (2 ^ a + 2 ^ b) / 2 =
        2 ^ (b - 1) * ((2 ^ a + 2 ^ b + 1) * (2 ^ (a - b) + 1)) := by
    have hx : 2 ^ a + 2 ^ b = 2 * (2 ^ (b - 1) * (2 ^ (a - b) + 1)) := by
      rw [hpow, hb2]; ring
    nth_rw 2 [hx]
    have hx2 :
        (2 ^ a + 2 ^ b + 1) * (2 * (2 ^ (b - 1) * (2 ^ (a - b) + 1))) =
          2 * ((2 ^ a + 2 ^ b + 1) * (2 ^ (b - 1) * (2 ^ (a - b) + 1))) := by
      ring
    rw [hx2, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    ring
  rw [hdiv, hprod]

lemma popc_sum_two_pow_distinct {i j : ℕ} (hij : j < i) :
    popc (2 ^ i + 2 ^ j) = 2 := by
  have hb : 2 ^ j < 2 ^ i := Nat.pow_lt_pow_right (by decide : 1 < 2) hij
  have : 2 ^ i + 2 ^ j = 2 ^ i * 1 + 2 ^ j := by ring
  rw [this, popc_two_pow_mul_add hb, popc_one, popc_two_pow]

lemma two_pow_add_lt_of_lt {i j : ℕ} (h : j < i) : 2 ^ j < 2 ^ i :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) h

lemma popc_sum_four_pow {e1 e2 e3 e4 : ℕ}
    (h12 : e2 < e1) (h23 : e3 < e2) (h34 : e4 < e3) :
    popc (2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4) = 4 := by
  have hle3 : 2 ^ e3 + 2 ^ e4 < 2 ^ e2 := by
    have : 2 ^ e4 < 2 ^ e3 := two_pow_add_lt_of_lt h34
    have : 2 ^ e3 + 2 ^ e4 < 2 ^ e3 + 2 ^ e3 := Nat.add_lt_add_left this _
    have : 2 ^ e3 + 2 ^ e3 = 2 ^ (e3 + 1) := by rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e3 + 1) ≤ 2 ^ e2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 < 2 ^ e1 := by
    have : 2 ^ e2 + (2 ^ e3 + 2 ^ e4) < 2 ^ e2 + 2 ^ e2 := Nat.add_lt_add_left hle3 _
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e2 + 1) ≤ 2 ^ e1 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hform1 : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 =
      2 ^ e1 * 1 + (2 ^ e2 + 2 ^ e3 + 2 ^ e4) := by ring
  rw [hform1, popc_two_pow_mul_add hle2, popc_one]
  have hform2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 =
      2 ^ e2 * 1 + (2 ^ e3 + 2 ^ e4) := by ring
  rw [hform2, popc_two_pow_mul_add hle3, popc_one, popc_sum_two_pow_distinct h34]

lemma popc_sum_three_pow {e1 e2 e3 : ℕ} (h12 : e2 < e1) (h23 : e3 < e2) :
    popc (2 ^ e1 + 2 ^ e2 + 2 ^ e3) = 3 := by
  have hle2 : 2 ^ e2 + 2 ^ e3 < 2 ^ e1 := by
    have : 2 ^ e3 < 2 ^ e2 := two_pow_add_lt_of_lt h23
    have : 2 ^ e2 + 2 ^ e3 < 2 ^ e2 + 2 ^ e2 := Nat.add_lt_add_left this _
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e2 + 1) ≤ 2 ^ e1 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hform : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 = 2 ^ e1 * 1 + (2 ^ e2 + 2 ^ e3) := by ring
  rw [hform, popc_two_pow_mul_add hle2, popc_one, popc_sum_two_pow_distinct h23]

lemma popc_sum_five_pow {e1 e2 e3 e4 e5 : ℕ}
    (h12 : e2 < e1) (h23 : e3 < e2) (h34 : e4 < e3) (h45 : e5 < e4) :
    popc (2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5) = 5 := by
  have hle4 : 2 ^ e4 + 2 ^ e5 < 2 ^ e3 := by
    have : 2 ^ e5 < 2 ^ e4 := two_pow_add_lt_of_lt h45
    have : 2 ^ e4 + 2 ^ e5 < 2 ^ e4 + 2 ^ e4 := Nat.add_lt_add_left this _
    have : 2 ^ e4 + 2 ^ e4 = 2 ^ (e4 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e4 + 1) ≤ 2 ^ e3 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle3 : 2 ^ e3 + 2 ^ e4 + 2 ^ e5 < 2 ^ e2 := by
    have : 2 ^ e3 + (2 ^ e4 + 2 ^ e5) < 2 ^ e3 + 2 ^ e3 :=
      Nat.add_lt_add_left hle4 _
    have : 2 ^ e3 + 2 ^ e3 = 2 ^ (e3 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e3 + 1) ≤ 2 ^ e2 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 < 2 ^ e1 := by
    have : 2 ^ e2 + (2 ^ e3 + 2 ^ e4 + 2 ^ e5) < 2 ^ e2 + 2 ^ e2 :=
      Nat.add_lt_add_left hle3 _
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e2 + 1) ≤ 2 ^ e1 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hform1 : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 =
      2 ^ e1 * 1 + (2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5) := by ring
  rw [hform1, popc_two_pow_mul_add hle2, popc_one]
  have hform2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 =
      2 ^ e2 * 1 + (2 ^ e3 + 2 ^ e4 + 2 ^ e5) := by ring
  rw [hform2, popc_two_pow_mul_add hle3, popc_one]
  have hform3 : 2 ^ e3 + 2 ^ e4 + 2 ^ e5 =
      2 ^ e3 * 1 + (2 ^ e4 + 2 ^ e5) := by ring
  rw [hform3, popc_two_pow_mul_add hle4, popc_one, popc_sum_two_pow_distinct h45]

lemma exponents_ordered_lt_double {ea b : ℕ} (hba : b + 1 < ea) (h2b : ea < 2 * b) :
    ea - b < b ∧ b < ea + 1 ∧ ea + 1 < 2 * ea - b := by
  omega

lemma exponents_ordered_gt_double {ea b : ℕ} (hba : b + 1 < ea) (h2b : 2 * b < ea) :
    b < ea - b ∧ ea - b < ea + 1 ∧ ea + 1 < 2 * ea - b := by
  omega

lemma popc_choose_two_three_bit_odd_no_collision {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (hne1 : ea ≠ b + 1) (hne2 : ea ≠ 2 * b) :
    popc (Nat.choose (2 ^ ea + 2 ^ b + 1) 2) = 5 := by
  rw [choose_two_of_three_bit_odd hba hb, popc_mul_two_pow]
  have hgt : b + 1 < ea := by omega
  rcases lt_or_gt_of_ne hne2 with hlt | hgt2
  · have hord := exponents_ordered_lt_double hgt hlt
    have hz : 0 < ea - b := by omega
    simpa [add_assoc] using
      popc_sum_five_pow (e1 := 2 * ea - b) (e2 := ea + 1) (e3 := b)
        (e4 := ea - b) (e5 := 0) hord.2.2 hord.2.1 hord.1 hz
  · have hord := exponents_ordered_gt_double hgt hgt2
    have hz : 0 < b := hb
    have hswap :
        2 ^ (2 * ea - b) + 2 ^ (ea + 1) + 2 ^ b + 2 ^ (ea - b) + 1 =
          2 ^ (2 * ea - b) + 2 ^ (ea + 1) + 2 ^ (ea - b) + 2 ^ b + 1 := by
      ring
    rw [hswap]
    simpa [add_assoc] using
      popc_sum_five_pow (e1 := 2 * ea - b) (e2 := ea + 1) (e3 := ea - b)
        (e4 := b) (e5 := 0) hord.2.2 hord.2.1 hord.1 hz

lemma choose_three_of_three_bit_odd {ea b : ℕ} (hba : b < ea) (hb : 1 ≤ b) :
    Nat.choose (2 ^ ea + 2 ^ b + 1) 3 =
      2 ^ (b - 1) *
        ((2 ^ ea + 2 ^ b + 1) * (2 ^ (ea - b) + 1) * (2 ^ ea + 2 ^ b - 1) / 3) := by
  set n := 2 ^ ea + 2 ^ b + 1 with hn
  set prod := n * (2 ^ (ea - b) + 1) * (2 ^ ea + 2 ^ b - 1)
  have h1 : n - 1 = 2 ^ ea + 2 ^ b := by
    rw [hn]; exact Nat.add_sub_cancel (2 ^ ea + 2 ^ b) 1
  have h2 : n - 2 = 2 ^ ea + 2 ^ b - 1 := by
    rw [hn]
    have : 2 ^ ea + 2 ^ b + 1 - 2 = 2 ^ ea + 2 ^ b + 1 - 1 - 1 := by omega
    rw [this, Nat.add_sub_cancel]
  have hbpow : 2 ^ ea + 2 ^ b = 2 ^ b * (2 ^ (ea - b) + 1) := by
    have : 2 ^ ea = 2 ^ b * 2 ^ (ea - b) := pow_add_of_ge (Nat.le_of_lt hba)
    rw [this]; ring
  have hdesc : n.descFactorial 3 = 2 ^ b * prod := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one, tsub_zero]
    rw [h1, hbpow, h2]
    unfold prod
    ring
  have hfac : n.descFactorial 3 = 6 * n.choose 3 := by
    have : (3 : ℕ) ! = 6 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  have hb2 : 2 ^ b = 2 * 2 ^ (b - 1) := by
    cases b with
    | zero => omega
    | succ b => simp [pow_succ, mul_comm]
  have hmain : 2 * 2 ^ (b - 1) * prod = 6 * n.choose 3 := by
    rw [← hfac, hdesc, hb2]
  have h3dvd : 3 ∣ prod := by
    have hdvd : 3 ∣ 2 * 2 ^ (b - 1) * prod :=
      ⟨2 * n.choose 3, by rw [hmain]; ring⟩
    have hcop : Nat.Coprime 3 (2 * 2 ^ (b - 1)) := by
      have h2 : Nat.Coprime 3 2 := by decide
      exact h2.mul_right (h2.pow_right (b - 1))
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd
  have hsplit : 2 ^ (b - 1) * prod = 3 * (2 ^ (b - 1) * (prod / 3)) := by
    rw [← Nat.mul_div_assoc _ h3dvd]
    have h3p : 3 ∣ 2 ^ (b - 1) * prod := h3dvd.mul_left _
    exact (Nat.mul_div_cancel' h3p).symm
  have : 6 * n.choose 3 = 6 * (2 ^ (b - 1) * (prod / 3)) := by
    calc
      6 * n.choose 3 = 2 * 2 ^ (b - 1) * prod := hmain.symm
      _ = 2 * (2 ^ (b - 1) * prod) := by ring
      _ = 2 * (3 * (2 ^ (b - 1) * (prod / 3))) := by rw [hsplit]
      _ = 6 * (2 ^ (b - 1) * (prod / 3)) := by ring
  exact Nat.mul_left_cancel (by decide : 0 < 6) this

lemma three_dvd_two_pow_add_one_of_odd {g : ℕ} (h : g % 2 = 1) :
    3 ∣ 2 ^ g + 1 := by
  have hg : g = 2 * (g / 2) + 1 := by omega
  rw [hg, pow_add, pow_mul, pow_one, mul_comm (a := (2 ^ 2) ^ (g / 2))]
  have hsub : 3 ∣ (2 ^ 2) ^ (g / 2) - 1 := by
    simpa using Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 (g / 2)
  have hle : 1 ≤ (2 ^ 2) ^ (g / 2) := Nat.one_le_pow _ _ (by decide)
  have : 2 * (2 ^ 2) ^ (g / 2) + 1 = 2 * ((2 ^ 2) ^ (g / 2) - 1) + 3 := by
    omega
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hsub 2) (by decide : 3 ∣ 3)

lemma eq_two_pow_of_popc_eq_two {n : ℕ} (h : popc n = 2) :
    ∃ i j, j < i ∧ n = 2 ^ i + 2 ^ j := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp [popc_zero] at h
    | succ n =>
      rw [popc_rec] at h
      have hhalf : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
      · rw [he, zero_add] at h
        obtain ⟨i, j, hji, hs⟩ := ih _ hhalf h
        refine ⟨i + 1, j + 1, by omega, ?_⟩
        have : n + 1 = 2 * ((n + 1) / 2) := by
          have := Nat.div_add_mod (n + 1) 2
          omega
        rw [this, hs, pow_succ, pow_succ]
        ring
      · rw [ho] at h
        have : popc ((n + 1) / 2) = 1 := by omega
        obtain ⟨i, hi⟩ := (popc_eq_one_iff _).1 this
        refine ⟨i + 1, 0, by omega, ?_⟩
        have : n + 1 = 2 * ((n + 1) / 2) + 1 := by
          have := Nat.div_add_mod (n + 1) 2
          omega
        rw [this, hi, pow_succ, pow_zero]
        ring

lemma eq_three_pow_of_popc_eq_three {n : ℕ} (h : popc n = 3) :
    ∃ e1 e2 e3, e3 < e2 ∧ e2 < e1 ∧ n = 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp [popc_zero] at h
    | succ n =>
      rw [popc_rec] at h
      have hhalf : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with he | ho
      · rw [he, zero_add] at h
        obtain ⟨e1, e2, e3, h32, h21, hs⟩ := ih _ hhalf h
        refine ⟨e1 + 1, e2 + 1, e3 + 1, by omega, by omega, ?_⟩
        have : n + 1 = 2 * ((n + 1) / 2) := by
          have := Nat.div_add_mod (n + 1) 2
          omega
        rw [this, hs, pow_succ, pow_succ, pow_succ]
        ring
      · rw [ho] at h
        have hp : popc ((n + 1) / 2) = 2 := by omega
        obtain ⟨i, j, hji, hs⟩ := eq_two_pow_of_popc_eq_two hp
        refine ⟨i + 1, j + 1, 0, by omega, by omega, ?_⟩
        have : n + 1 = 2 * ((n + 1) / 2) + 1 := by
          have := Nat.div_add_mod (n + 1) 2
          omega
        rw [this, hs, pow_succ, pow_succ, pow_zero]
        ring

lemma popc_choose_two_three_bit_adjacent {b : ℕ} (hb : 2 ≤ b) :
    popc (Nat.choose (2 ^ (b + 1) + 2 ^ b + 1) 2) = 4 := by
  have hba : b < b + 1 := by omega
  have hb1 : 1 ≤ b := by omega
  rw [choose_two_of_three_bit_odd hba hb1, popc_mul_two_pow]
  have hsimp : 2 * (b + 1) - b = b + 2 := by omega
  have hab : (b + 1) - b = 1 := by omega
  rw [hsimp, hab]
  have : 2 ^ (b + 2) + 2 ^ (b + 1 + 1) + 2 ^ b + 2 ^ 1 + 1 =
      2 ^ (b + 3) + 2 ^ b + 2 + 1 := by
    have hshift : (b + 1 + 1 : ℕ) = b + 2 := rfl
    rw [hshift, pow_one]
    have : 2 ^ (b + 2) + 2 ^ (b + 2) = 2 ^ (b + 3) := by
      rw [← two_mul, ← two_pow_succ']
    omega
  rw [this]
  have : 2 ^ (b + 3) + 2 ^ b + 2 + 1 = 2 ^ (b + 3) + 2 ^ b + 2 ^ 1 + 2 ^ 0 := by
    rw [pow_one, pow_zero]
  rw [this]
  have hb0 : 0 < 1 := by decide
  have h1b : 1 < b := by omega
  have hbb3 : b < b + 3 := by omega
  -- order: b+3 > b > 1 > 0
  have : 2 ^ (b + 3) + 2 ^ b + 2 ^ 1 + 2 ^ 0 =
      2 ^ (b + 3) + 2 ^ b + 2 ^ 1 + 2 ^ 0 := rfl
  exact popc_sum_four_pow (e1 := b + 3) (e2 := b) (e3 := 1) (e4 := 0)
    hbb3 h1b hb0

lemma popc_choose_two_three_bit_double {b : ℕ} (hb : 2 ≤ b) :
    popc (Nat.choose (2 ^ (2 * b) + 2 ^ b + 1) 2) = 4 := by
  have hba : b < 2 * b := by omega
  have hb1 : 1 ≤ b := by omega
  rw [choose_two_of_three_bit_odd hba hb1, popc_mul_two_pow]
  have h3b : 2 * (2 * b) - b = 3 * b := by omega
  have hab : 2 * b - b = b := by omega
  rw [h3b, hab]
  have : 2 ^ (3 * b) + 2 ^ (2 * b + 1) + 2 ^ b + 2 ^ b + 1 =
      2 ^ (3 * b) + 2 ^ (2 * b + 1) + 2 ^ (b + 1) + 1 := by
    have : 2 ^ b + 2 ^ b = 2 ^ (b + 1) := by rw [← two_mul, ← two_pow_succ']
    omega
  rw [this]
  have : 2 ^ (3 * b) + 2 ^ (2 * b + 1) + 2 ^ (b + 1) + 1 =
      2 ^ (3 * b) + 2 ^ (2 * b + 1) + 2 ^ (b + 1) + 2 ^ 0 := by
    simp
  rw [this]
  have h0 : 0 < b + 1 := by omega
  have h1 : b + 1 < 2 * b + 1 := by omega
  have h2 : 2 * b + 1 < 3 * b := by omega
  exact popc_sum_four_pow (e1 := 3 * b) (e2 := 2 * b + 1) (e3 := b + 1) (e4 := 0)
    h2 h1 h0

lemma a_ne_zero_three_bit_odd_collision {ea b : ℕ}
    (hba : b < ea) (hb : 2 ≤ b) (hcoll : ea = b + 1 ∨ ea = 2 * b) :
    _root_.a (2 ^ ea + 2 ^ b + 1) ≠ 0 := by
  have hn : 1 ≤ 2 ^ ea + 2 ^ b + 1 := by
    have hpow : 1 ≤ 2 ^ ea := Nat.one_le_pow _ _ (by decide)
    have h1 : 2 ^ ea ≤ 2 ^ ea + 2 ^ b := Nat.le_add_right _ _
    have h2 : 2 ^ ea + 2 ^ b ≤ 2 ^ ea + 2 ^ b + 1 := Nat.le_add_right _ _
    exact hpow.trans (h1.trans h2)
  have hk : 2 ≤ 2 ^ ea + 2 ^ b + 1 := by
    have hpow : 2 ≤ 2 ^ ea := by
      have : 2 ^ 1 ≤ 2 ^ ea := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    have h1 : 2 ^ ea ≤ 2 ^ ea + 2 ^ b := Nat.le_add_right _ _
    have h2 : 2 ^ ea + 2 ^ b ≤ 2 ^ ea + 2 ^ b + 1 := Nat.le_add_right _ _
    exact hpow.trans (h1.trans h2)
  refine a_ne_zero_of_witness (2 ^ ea + 2 ^ b + 1) 2 (by decide) hk ?_
  rcases hcoll with h1 | h2
  · subst h1
    have := popc_choose_two_three_bit_adjacent hb
    omega
  · subst h2
    have := popc_choose_two_three_bit_double hb
    omega

lemma geom_sum_pow_two (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ) ^ i) = 2 ^ n - 1 := by
  simpa using Nat.geomSum_eq (m := 2) (by decide) n

lemma sum_two_pow_lt {s : Finset ℕ} {k : ℕ} (h : ∀ x ∈ s, x < k) :
    (∑ i ∈ s, (2 : ℕ) ^ i) < 2 ^ k := by
  have hsub : s ⊆ Finset.range k := by
    intro x hx; simp [h x hx]
  have hle : (∑ i ∈ s, (2 : ℕ) ^ i) ≤ ∑ i ∈ Finset.range k, 2 ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have : (∑ i ∈ Finset.range k, (2 : ℕ) ^ i) = 2 ^ k - 1 := geom_sum_pow_two k
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by decide)
  omega

lemma popc_sum_two_pow_finset (s : Finset ℕ) :
    popc (∑ i ∈ s, (2 : ℕ) ^ i) = s.card := by
  refine Finset.induction_on_max s ?empty ?step
  · simp [popc_zero]
  · intro a s hlt ih
    have hnot : a ∉ s := fun ha => (lt_irrefl a) (hlt a ha)
    have hsum : ∑ i ∈ insert a s, (2 : ℕ) ^ i = 2 ^ a + ∑ i ∈ s, 2 ^ i :=
      Finset.sum_insert hnot
    have hbound : (∑ i ∈ s, (2 : ℕ) ^ i) < 2 ^ a :=
      sum_two_pow_lt (fun x hx => hlt x hx)
    have hform : 2 ^ a + ∑ i ∈ s, (2 : ℕ) ^ i = 2 ^ a * 1 + ∑ i ∈ s, 2 ^ i := by
      ring
    rw [hsum, hform, popc_two_pow_mul_add hbound, popc_one, ih,
      Finset.card_insert_of_notMem hnot]
    omega

lemma four_pow_eq (i : ℕ) : (4 : ℕ) ^ i = 2 ^ (2 * i) := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]

lemma three_dvd_four_pow_sub_one (b : ℕ) : 3 ∣ 4 ^ b - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow (4 : ℕ) 1 b

lemma R_eq_sum (b : ℕ) :
    (4 ^ b - 1) / 3 = ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) := by
  have hgeom : ∑ i ∈ Finset.range b, (4 : ℕ) ^ i = (4 ^ b - 1) / 3 := by
    simpa using Nat.geomSum_eq (m := 4) (by decide) b
  rw [← hgeom]
  apply Finset.sum_congr rfl
  intro i _
  exact four_pow_eq i

lemma injective_double : Function.Injective (fun i : ℕ => 2 * i) :=
  fun _ _ h => Nat.mul_left_cancel (by decide : (0 : ℕ) < 2) h

lemma injective_odd_shift (t : ℕ) :
    Function.Injective (fun i : ℕ => 2 * t + 1 + 2 * i) := by
  intro x y h
  have : 2 * x = 2 * y := Nat.add_left_cancel h
  exact injective_double this

lemma popc_R (b : ℕ) : popc ((4 ^ b - 1) / 3) = b := by
  rw [R_eq_sum]
  have himg :
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) =
        ∑ j ∈ (Finset.range b).image (fun i => 2 * i), 2 ^ j := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact injective_double h
  rw [himg, popc_sum_two_pow_finset, Finset.card_image_of_injective _ injective_double]
  simp

lemma Q_eq (t : ℕ) :
    (2 ^ (2 * t + 1) + 1) / 3 = 1 + 2 * ((4 ^ t - 1) / 3) := by
  have hdiv : 3 ∣ 2 ^ (2 * t + 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have hdiv' : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * ((2 ^ (2 * t + 1) + 1) / 3) = 2 ^ (2 * t + 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have rhs : 3 * (1 + 2 * ((4 ^ t - 1) / 3)) =
      3 + 2 * (3 * ((4 ^ t - 1) / 3)) := by ring
  rw [lhs, rhs, Nat.mul_div_cancel' hdiv']
  have hpow : 2 ^ (2 * t + 1) = 2 * 4 ^ t := by
    rw [pow_add, pow_one, four_pow_eq, mul_comm]
  have hle : 1 ≤ 4 ^ t := Nat.one_le_pow _ _ (by decide)
  omega

lemma popc_Q (t : ℕ) :
    popc ((2 ^ (2 * t + 1) + 1) / 3) = t + 1 := by
  rw [Q_eq, add_comm, popc_rec]
  have hmod : (2 * ((4 ^ t - 1) / 3) + 1) % 2 = 1 := by simp
  have hdiv : (2 * ((4 ^ t - 1) / 3) + 1) / 2 = (4 ^ t - 1) / 3 := by
    rw [Nat.mul_add_div (by decide : 0 < 2)]
    simp
  rw [hmod, hdiv, popc_R, add_comm]

lemma term3_eq (t b : ℕ) :
    ((2 ^ (2 * t + 1) + 1) / 3) * (4 ^ b - 1) =
      (4 ^ b - 1) / 3 + 2 ^ (2 * t + 1) * ((4 ^ b - 1) / 3) := by
  set Q := (2 ^ (2 * t + 1) + 1) / 3
  set R := (4 ^ b - 1) / 3
  have hR : 3 * R = 4 ^ b - 1 := Nat.mul_div_cancel' (three_dvd_four_pow_sub_one b)
  have hQ : 3 * Q = 2 ^ (2 * t + 1) + 1 :=
    Nat.mul_div_cancel' (three_dvd_two_pow_add_one_of_odd (by omega))
  calc
    Q * (4 ^ b - 1) = Q * (3 * R) := by rw [hR]
    _ = (3 * Q) * R := by ring
    _ = (2 ^ (2 * t + 1) + 1) * R := by rw [hQ]
    _ = R + 2 ^ (2 * t + 1) * R := by ring

lemma term3_as_sum (t b : ℕ) :
    (4 ^ b - 1) / 3 + 2 ^ (2 * t + 1) * ((4 ^ b - 1) / 3) =
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) +
        ∑ i ∈ Finset.range b, 2 ^ (2 * t + 1 + 2 * i) := by
  rw [R_eq_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← pow_add]

lemma disjoint_parity_images (t b : ℕ) :
    Disjoint ((Finset.range b).image (fun i => 2 * i))
      ((Finset.range b).image (fun i => 2 * t + 1 + 2 * i)) := by
  refine Finset.disjoint_iff_ne.2 ?_
  intro x hx y hy hxy
  simp only [Finset.mem_image, Finset.mem_range] at hx hy
  rcases hx with ⟨i, _, rfl⟩
  rcases hy with ⟨j, _, rfl⟩
  have : (2 * i) % 2 = (2 * t + 1 + 2 * j) % 2 := by rw [hxy]
  simp [Nat.add_mod] at this

lemma popc_term3 (t b : ℕ) :
    popc (((2 ^ (2 * t + 1) + 1) / 3) * (4 ^ b - 1)) = 2 * b := by
  rw [term3_eq, term3_as_sum]
  have h1 :
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * i) =
        ∑ j ∈ (Finset.range b).image (fun i => 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_double h
  have h2 :
      ∑ i ∈ Finset.range b, (2 : ℕ) ^ (2 * t + 1 + 2 * i) =
        ∑ j ∈ (Finset.range b).image (fun i => 2 * t + 1 + 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_odd_shift t h
  rw [h1, h2, ← Finset.sum_union (disjoint_parity_images t b)]
  rw [popc_sum_two_pow_finset, Finset.card_union_of_disjoint (disjoint_parity_images t b)]
  rw [Finset.card_image_of_injective _ injective_double]
  rw [Finset.card_image_of_injective _ (injective_odd_shift t)]
  simp; omega

lemma Q_mul_odd_sq (t ea b : ℕ) :
    let Q := (2 ^ (2 * t + 1) + 1) / 3
    Q * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) =
      2 ^ (2 * ea) * Q + 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) := by
  intro Q
  have h4 : (4 : ℕ) ^ b - 1 = 2 ^ (2 * b) - 1 := by rw [four_pow_eq]
  rw [mul_add, mul_add, h4]
  ring

lemma term3_lt (t b : ℕ) :
    ((2 ^ (2 * t + 1) + 1) / 3) * (4 ^ b - 1) < 2 ^ (2 * b + (2 * t + 1) + 1) := by
  set Q := (2 ^ (2 * t + 1) + 1) / 3
  set g := 2 * t + 1
  have hdiv : 3 ∣ 2 ^ g + 1 := three_dvd_two_pow_add_one_of_odd (by omega)
  have hQ3 : 3 * Q = 2 ^ g + 1 := Nat.mul_div_cancel' hdiv
  have hQle : Q ≤ 2 ^ g := by
    have : 3 * Q ≤ 3 * 2 ^ g := by
      have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
      omega
    exact Nat.le_of_mul_le_mul_left this (by decide)
  have hRlt : (4 : ℕ) ^ b - 1 < 4 ^ b := Nat.sub_lt (Nat.one_le_pow _ _ (by decide)) (by decide)
  have hgpos : 0 < 2 ^ g := Nat.one_le_pow _ _ (by decide)
  have hlt : Q * (4 ^ b - 1) < 2 ^ g * 4 ^ b :=
    Nat.mul_lt_mul_of_le_of_lt hQle hRlt hgpos
  have heq : 2 ^ g * 4 ^ b = 2 ^ (g + 2 * b) := by
    rw [four_pow_eq, ← pow_add]
  have hpowlt : 2 ^ (g + 2 * b) < 2 ^ (2 * b + g + 1) :=
    Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 2) (by omega)
  omega

lemma Q_lt_shift (t : ℕ) (ht : 1 ≤ t) :
    (2 ^ (2 * t + 1) + 1) / 3 < 2 ^ (2 * t) := by
  have hdiv : 3 ∣ 2 ^ (2 * t + 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have h3 : 3 * ((2 ^ (2 * t + 1) + 1) / 3) = 2 ^ (2 * t + 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have hgoal : 2 ^ (2 * t + 1) + 1 < 3 * 2 ^ (2 * t) := by
    have : 2 ^ (2 * t + 1) = 2 ^ (2 * t) * 2 := pow_succ _ _
    rw [this]
    have : 1 < 2 ^ (2 * t) := Nat.one_lt_pow (by omega) (by decide)
    omega
  have hmul : 3 * ((2 ^ (2 * t + 1) + 1) / 3) < 3 * 2 ^ (2 * t) := by
    rwa [h3]
  exact Nat.lt_of_mul_lt_mul_left hmul

lemma popc_P {t ea b : ℕ} (ht : 1 ≤ t)
    (hg : ea = b + (2 * t + 1)) :
    popc (((2 ^ (2 * t + 1) + 1) / 3) *
      (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1))) =
        2 * t + 2 + 2 * b := by
  set Q := (2 ^ (2 * t + 1) + 1) / 3
  have hdecomp := Q_mul_odd_sq t ea b
  change Q * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) =
      2 ^ (2 * ea) * Q + 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) at hdecomp
  rw [hdecomp]
  have hT3lt : Q * (4 ^ b - 1) < 2 ^ (ea + b + 1) := by
    have hlt0 := term3_lt t b
    have hidx : 2 * b + (2 * t + 1) + 1 = ea + b + 1 := by omega
    rwa [hidx] at hlt0
  have hT2T3 :
      popc (2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1)) =
        popc Q + popc (Q * (4 ^ b - 1)) :=
    popc_two_pow_mul_add hT3lt
  have hQlt : Q < 2 ^ (2 * t) := Q_lt_shift t ht
  have hsumlt : 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) < 2 ^ (2 * ea) := by
    have : 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) <
        2 ^ (ea + b + 1) * Q + 2 ^ (ea + b + 1) :=
      Nat.add_lt_add_left hT3lt _
    have hsplit : 2 ^ (ea + b + 1) * Q + 2 ^ (ea + b + 1) =
        2 ^ (ea + b + 1) * (Q + 1) := by ring
    have hQ1 : Q + 1 ≤ 2 ^ (2 * t) := by omega
    have : 2 ^ (ea + b + 1) * (Q + 1) ≤ 2 ^ (ea + b + 1) * 2 ^ (2 * t) :=
      Nat.mul_le_mul_left _ hQ1
    have hpow : 2 ^ (ea + b + 1) * 2 ^ (2 * t) = 2 ^ (2 * ea) := by
      rw [← pow_add]; congr 1; omega
    omega
  have hform :
      2 ^ (2 * ea) * Q + 2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1) =
        2 ^ (2 * ea) * Q + (2 ^ (ea + b + 1) * Q + Q * (4 ^ b - 1)) := by
    ring
  rw [hform, popc_two_pow_mul_add hsumlt, hT2T3, popc_Q, popc_term3]
  omega

lemma sq_sub_one_of_three_bit (ea b : ℕ) :
    (2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1) =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
  have hbpow : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hx : 1 ≤ 2 ^ ea + 2 ^ b :=
    hbpow.trans (Nat.le_add_left (2 ^ b) (2 ^ ea))
  have hb : 1 ≤ 2 ^ (2 * b) := Nat.one_le_two_pow
  have hpos : 1 ≤ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + 2 ^ (2 * b) :=
    hb.trans (Nat.le_add_left _ _)
  have h1 : (2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1) =
      (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) - 1 := by
    set x := 2 ^ ea + 2 ^ b
    have hx' : 1 ≤ x := hx
    have : (x + 1) * (x - 1) = x * x - 1 := by
      have hdist := Nat.mul_sub_left_distrib (x + 1) x 1
      simp only [mul_one] at hdist
      have : (x + 1) * x = x * x + x := by ring
      rw [hdist, this]
      have hxcancel : x * x + x - x = x * x := Nat.add_sub_cancel (x * x) x
      have hle : x ≤ x * x + x := Nat.le_add_left _ _
      have hle1 : 1 ≤ x := hx'
      -- (x*x + x) - 1 - x = x*x - 1, and (x*x + x - x) - 1 = x*x - 1
      have : x * x + x - 1 - x = x * x + x - x - 1 := by
        have : x ≤ x * x + x - 1 := by
          have : 1 ≤ x * x := by
            have : 1 ≤ x := hle1
            exact le_trans this (Nat.le_mul_of_pos_right x this)
          omega
        omega
      omega
    exact this
  have h2 : (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + 2 ^ (2 * b) := by
    have ha : 2 ^ ea * 2 ^ ea = 2 ^ (2 * ea) := by rw [← pow_add]; congr 1; omega
    have hb' : 2 ^ b * 2 ^ b = 2 ^ (2 * b) := by rw [← pow_add]; congr 1; omega
    have hab : 2 * 2 ^ ea * 2 ^ b = 2 ^ (ea + b + 1) := by
      have : 2 * 2 ^ ea * 2 ^ b = 2 ^ 1 * 2 ^ ea * 2 ^ b := by simp
      rw [this, mul_assoc, ← pow_add, ← pow_add]
      congr 1; omega
    calc
      (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) =
          2 ^ ea * 2 ^ ea + 2 * 2 ^ ea * 2 ^ b + 2 ^ b * 2 ^ b := by ring
      _ = 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + 2 ^ (2 * b) := by rw [ha, hab, hb']
  have : (2 ^ ea + 2 ^ b) * (2 ^ ea + 2 ^ b) - 1 =
      2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
    rw [h2, Nat.add_sub_assoc hb]
  exact h1.trans this

lemma popc_odd_part_choose_three {ea b : ℕ} (_hba : b < ea)
    (_hb : 1 ≤ b) (hodd : (ea - b) % 2 = 1) (hne : 3 ≤ ea - b) :
    popc (((2 ^ ea + 2 ^ b + 1) * (2 ^ (ea - b) + 1) * (2 ^ ea + 2 ^ b - 1)) / 3) % 2 = 0 := by
  set g := ea - b
  have hg : g = 2 * (g / 2) + 1 := by omega
  have ht : 1 ≤ g / 2 := by omega
  have hea : ea = b + g := by omega
  have hdiv : 3 ∣ 2 ^ g + 1 := three_dvd_two_pow_add_one_of_odd hodd
  have hprod := sq_sub_one_of_three_bit ea b
  have hrewrite :
      ((2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1)) / 3 =
        (2 ^ g + 1) / 3 * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) := by
    have hmul :
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
          (2 ^ g + 1) * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) := by
      calc
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
            (2 ^ g + 1) * ((2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1)) := by ring
        _ = (2 ^ g + 1) * (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) := by
              rw [hprod]
    rw [hmul, mul_comm (2 ^ g + 1), Nat.mul_div_assoc _ hdiv, mul_comm]
  rw [hrewrite, show g = 2 * (g / 2) + 1 from hg]
  have hp := popc_P (t := g / 2) (ea := ea) (b := b) ht (by omega)
  rw [hp]; omega

lemma popc_choose_three_three_bit_odd_gap {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (hodd : (ea - b) % 2 = 1) (hne : 3 ≤ ea - b) :
    popc (Nat.choose (2 ^ ea + 2 ^ b + 1) 3) % 2 = 0 := by
  rw [choose_three_of_three_bit_odd hba hb, popc_mul_two_pow]
  exact popc_odd_part_choose_three hba hb hodd hne

lemma a_ne_zero_three_bit_odd_gap {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (hodd : (ea - b) % 2 = 1) (hne : 3 ≤ ea - b) :
    _root_.a (2 ^ ea + 2 ^ b + 1) ≠ 0 := by
  have hpow : 2 ≤ 2 ^ ea := by
    have : 2 ^ 1 ≤ 2 ^ ea := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hn : 3 ≤ 2 ^ ea + 2 ^ b + 1 := by
    have : 2 ≤ 2 ^ ea + 2 ^ b := hpow.trans (Nat.le_add_right _ _)
    exact Nat.succ_le_succ this
  refine a_ne_zero_of_witness (2 ^ ea + 2 ^ b + 1) 3 (by decide) hn ?_
  exact popc_choose_three_three_bit_odd_gap hba hb hodd hne



/-! ### Even-gap 3-bit: `C(n,3)` is evil when `b ≡ g/2 (mod 2)` or `g > 2b`. -/

lemma R_mul_one_add_four_pow_of_le {b t : ℕ} (ht : t ≤ b) :
    ((4 ^ b - 1) / 3) * (1 + 4 ^ t) =
      (4 ^ t - 1) / 3 + 2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3) +
        4 ^ b * ((4 ^ t - 1) / 3) := by
  have hRb : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
  have hRt : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
  have hRbt : 3 ∣ 4 ^ (b - t) - 1 := three_dvd_four_pow_sub_one (b - t)
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * (((4 ^ b - 1) / 3) * (1 + 4 ^ t)) = (4 ^ b - 1) * (1 + 4 ^ t) := by
    rw [← mul_assoc, Nat.mul_div_cancel' hRb]
  have rhs :
      3 * ((4 ^ t - 1) / 3 + 2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3) +
          4 ^ b * ((4 ^ t - 1) / 3)) =
        (4 ^ t - 1) + 2 * 4 ^ t * (4 ^ (b - t) - 1) + 4 ^ b * (4 ^ t - 1) := by
    have h1 : 3 * ((4 ^ t - 1) / 3) = 4 ^ t - 1 := Nat.mul_div_cancel' hRt
    have h2 : 3 * (2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3)) =
        2 * 4 ^ t * (4 ^ (b - t) - 1) := by
      have : 3 * (2 * 4 ^ t * ((4 ^ (b - t) - 1) / 3)) =
          2 * 4 ^ t * (3 * ((4 ^ (b - t) - 1) / 3)) := by ring
      rw [this, Nat.mul_div_cancel' hRbt]
    have h3 : 3 * (4 ^ b * ((4 ^ t - 1) / 3)) = 4 ^ b * (4 ^ t - 1) := by
      have : 3 * (4 ^ b * ((4 ^ t - 1) / 3)) = 4 ^ b * (3 * ((4 ^ t - 1) / 3)) := by
        ring
      rw [this, Nat.mul_div_cancel' hRt]
    rw [mul_add, mul_add, h1, h2, h3]
  rw [lhs, rhs]
  have hle1 : 1 ≤ 4 ^ t := Nat.one_le_pow _ _ (by decide)
  have hle2 : 1 ≤ 4 ^ (b - t) := Nat.one_le_pow _ _ (by decide)
  have hle3 : 1 ≤ 4 ^ b := Nat.one_le_pow _ _ (by decide)
  have hpow : (4 : ℕ) ^ t * 4 ^ (b - t) = 4 ^ b := by
    rw [← pow_add]; congr 1; omega
  zify [hle1, hle2, hle3]
  have hpowZ : (4 : ℤ) ^ t * 4 ^ (b - t) = 4 ^ b := by
    exact_mod_cast hpow
  rw [← hpowZ]
  ring

lemma popc_R_mul_one_add_four_pow {b t : ℕ} (ht : t ≤ b) :
    popc (((4 ^ b - 1) / 3) * (1 + 4 ^ t)) = b + t := by
  rw [R_mul_one_add_four_pow_of_le ht]
  set R1 := (4 ^ t - 1) / 3
  set R2 := (4 ^ (b - t) - 1) / 3
  have h1 : R1 = ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * i) := R_eq_sum t
  have h2 : R2 = ∑ i ∈ Finset.range (b - t), (2 : ℕ) ^ (2 * i) := R_eq_sum (b - t)
  have hmid : 2 * 4 ^ t * R2 = ∑ i ∈ Finset.range (b - t), (2 : ℕ) ^ (2 * t + 1 + 2 * i) := by
    rw [h2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have : 2 * 4 ^ t * 2 ^ (2 * i) = 2 ^ (2 * t + 1 + 2 * i) := by
      have : (4 : ℕ) ^ t = 2 ^ (2 * t) := four_pow_eq t
      rw [this]
      have : (2 : ℕ) * 2 ^ (2 * t) = 2 ^ (2 * t + 1) := by
        rw [← Nat.pow_succ']
      rw [this, ← pow_add]
    exact this
  have hhi : 4 ^ b * R1 = ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * b + 2 * i) := by
    rw [h1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have : (4 : ℕ) ^ b * 2 ^ (2 * i) = 2 ^ (2 * b + 2 * i) := by
      rw [four_pow_eq, ← pow_add]
    exact this
  -- pack as images and take union
  have himg1 :
      ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * i) =
        ∑ j ∈ (Finset.range t).image (fun i => 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_double h
  have himg2 :
      ∑ i ∈ Finset.range (b - t), (2 : ℕ) ^ (2 * t + 1 + 2 * i) =
        ∑ j ∈ (Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i), 2 ^ j := by
    rw [Finset.sum_image]; intro x _ y _ h; exact injective_odd_shift t h
  have himg3 :
      ∑ i ∈ Finset.range t, (2 : ℕ) ^ (2 * b + 2 * i) =
        ∑ j ∈ (Finset.range t).image (fun i => 2 * b + 2 * i), 2 ^ j := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact injective_double (Nat.add_left_cancel h)
  have d12 : Disjoint ((Finset.range t).image (fun i => 2 * i))
      ((Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i)) := by
    refine Finset.disjoint_iff_ne.2 ?_
    intro x hx y hy hxy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨i, _, rfl⟩
    rcases hy with ⟨j, _, rfl⟩
    have : (2 * i) % 2 = (2 * t + 1 + 2 * j) % 2 := by rw [hxy]
    simp [Nat.add_mod] at this
  have d13 : Disjoint ((Finset.range t).image (fun i => 2 * i))
      ((Finset.range t).image (fun i => 2 * b + 2 * i)) := by
    refine Finset.disjoint_iff_ne.2 ?_
    intro x hx y hy hxy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨i, hi, rfl⟩
    rcases hy with ⟨j, hj, rfl⟩
    have : 2 * i = 2 * b + 2 * j := hxy
    omega
  have d23 : Disjoint ((Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i))
      ((Finset.range t).image (fun i => 2 * b + 2 * i)) := by
    refine Finset.disjoint_iff_ne.2 ?_
    intro x hx y hy hxy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    rcases hx with ⟨i, hi, rfl⟩
    rcases hy with ⟨j, hj, rfl⟩
    have : 2 * t + 1 + 2 * i = 2 * b + 2 * j := hxy
    omega
  have d123 : Disjoint
      (((Finset.range t).image (fun i => 2 * i)) ∪
        (Finset.range (b - t)).image (fun i => 2 * t + 1 + 2 * i))
      ((Finset.range t).image (fun i => 2 * b + 2 * i)) :=
    Finset.disjoint_union_left.2 ⟨d13, d23⟩
  rw [hmid, hhi, h1, himg1, himg2, himg3]
  rw [← Finset.sum_union d12, ← Finset.sum_union d123]
  rw [popc_sum_two_pow_finset]
  rw [Finset.card_union_of_disjoint d123, Finset.card_union_of_disjoint d12]
  rw [Finset.card_image_of_injective _ injective_double]
  rw [Finset.card_image_of_injective _ (injective_odd_shift t)]
  have hinj : Function.Injective (fun i : ℕ => 2 * b + 2 * i) :=
    fun x y h => injective_double (Nat.add_left_cancel h)
  rw [Finset.card_image_of_injective _ hinj]
  simp; omega

lemma Rb_lt (b : ℕ) : (4 ^ b - 1) / 3 < 2 ^ (2 * b) := by
  have hdiv := three_dvd_four_pow_sub_one b
  have hmul : 3 * ((4 ^ b - 1) / 3) = 4 ^ b - 1 := Nat.mul_div_cancel' hdiv
  have hlt : 4 ^ b - 1 < 4 ^ b := Nat.sub_lt (Nat.one_le_pow _ _ (by decide)) (by decide)
  have hlt3 : 4 ^ b - 1 < 3 * 4 ^ b :=
    lt_of_lt_of_le hlt (Nat.le_mul_of_pos_left _ (by decide : 0 < 3))
  have hmul_lt : 3 * ((4 ^ b - 1) / 3) < 3 * 4 ^ b := by
    rwa [hmul]
  have hlt4 : (4 ^ b - 1) / 3 < 4 ^ b := Nat.lt_of_mul_lt_mul_left hmul_lt
  simpa [four_pow_eq] using hlt4

lemma popc_add_two_pow_mul {a b i : ℕ} (hb : b < 2 ^ i) :
    popc (b + 2 ^ i * a) = popc a + popc b := by
  rw [add_comm b]
  exact popc_two_pow_mul_add hb

lemma popc_one_add_two_pow_mul {q g : ℕ} (hq : q < 2 ^ g) :
    popc (q * (1 + 2 ^ g)) = 2 * popc q := by
  have hdecomp : q * (1 + 2 ^ g) = q + 2 ^ g * q := by ring
  rw [hdecomp, popc_add_two_pow_mul hq]
  omega

lemma Rb_mul_lt (b g : ℕ) :
    ((4 ^ b - 1) / 3) * (1 + 2 ^ g) < 2 ^ (2 * b + g + 1) := by
  set Rb := (4 ^ b - 1) / 3
  have hRb : Rb < 2 ^ (2 * b) := Rb_lt b
  have h1b : 1 ≤ (2 : ℕ) ^ (2 * b) := Nat.one_le_two_pow
  have hpos : 0 < 1 + (2 : ℕ) ^ g := Nat.add_pos_left (by decide) _
  have hmul_lt : Rb * (1 + 2 ^ g) < 2 ^ (2 * b) * (1 + 2 ^ g) :=
    Nat.mul_lt_mul_of_pos_right hRb hpos
  have hsplit : 2 ^ (2 * b) * (1 + 2 ^ g) = 2 ^ (2 * b) + 2 ^ (2 * b + g) := by
    rw [mul_add, mul_one, ← pow_add]
  have hle : 2 ^ (2 * b) + 2 ^ (2 * b + g) ≤ 2 ^ (2 * b + g + 1) := by
    have hpow : 2 ^ (2 * b) ≤ 2 ^ (2 * b + g) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ (2 * b + g) + 2 ^ (2 * b + g) = 2 ^ (2 * b + g + 1) := by
      rw [← two_mul, ← Nat.pow_succ']
    omega
  omega


lemma popc_Qbig_mul_even_gap {b g : ℕ} (_hb : 1 ≤ b) (hgeven : g % 2 = 0) (hg2 : 2 ≤ g)
    (hcond : g / 2 ≤ b → b % 2 = (g / 2) % 2) :
    popc (((2 ^ (2 * (b + g)) + 2 ^ ((b + g) + b + 1) + (2 ^ (2 * b) - 1)) / 3) *
      (1 + 2 ^ g)) % 2 = 0 := by
  set ea := b + g
  set Rb := (4 ^ b - 1) / 3
  set Qs := (2 ^ (g - 1) + 1) / 3
  -- reuse the algebraic split, specialized from `Qbig_eq`
  have hsplit :
      (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3 =
        Rb + 2 ^ (2 * b + g + 1) * Qs := by
    have hg' : g = 4 * (g / 4) + g % 4 := by omega
    -- prove the identity directly (same as Qbig_eq, for general even g)
    have hdivR : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
    have hodd : (g - 1) % 2 = 1 := by omega
    have hdivS : 3 ∣ 2 ^ (g - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd
    have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := four_pow_eq b
    have hid :
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
          (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
      have hpow1 : 2 ^ (2 * b + g + 1) * 2 ^ (g - 1) = 2 ^ (2 * ea) := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : 2 ^ (2 * b + g + 1) = 2 ^ (ea + b + 1) := by
        congr 1; omega
      calc
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
            2 ^ (2 * b + g + 1) * 2 ^ (g - 1) + 2 ^ (2 * b + g + 1) +
              (2 ^ (2 * b) - 1) := by rw [hpow1, hpow2]
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (2 ^ (2 * b) - 1) := by ring
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (4 ^ b - 1) := by rw [h4]
        _ = (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by ring
    have hdiv :
        3 ∣ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
      have : 3 ∣ (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) :=
        hdivR.add (hdivS.mul_left _)
      simpa using (hid.symm ▸ this)
    apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
    have lhs :
        3 * ((2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3) =
          2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) :=
      Nat.mul_div_cancel' hdiv
    have rhs :
        3 * (Rb + 2 ^ (2 * b + g + 1) * Qs) =
          (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
      rw [mul_add, Nat.mul_div_cancel' hdivR]
      have :
          3 * (2 ^ (2 * b + g + 1) * Qs) =
            2 ^ (2 * b + g + 1) * (3 * Qs) := by ring
      rw [this, show 3 * Qs = 2 ^ (g - 1) + 1 from Nat.mul_div_cancel' hdivS]
    rw [lhs, rhs]
    exact hid
  rw [hsplit]
  have hdecomp :
      (Rb + 2 ^ (2 * b + g + 1) * Qs) * (1 + 2 ^ g) =
        Rb * (1 + 2 ^ g) + 2 ^ (2 * b + g + 1) * (Qs * (1 + 2 ^ g)) := by
    ring
  rw [hdecomp]
  have hlow_lt : Rb * (1 + 2 ^ g) < 2 ^ (2 * b + g + 1) := by
    simpa [Rb] using Rb_mul_lt b g
  have hsum :
      popc (Rb * (1 + 2 ^ g) + 2 ^ (2 * b + g + 1) * (Qs * (1 + 2 ^ g))) =
        popc (Qs * (1 + 2 ^ g)) + popc (Rb * (1 + 2 ^ g)) :=
    popc_add_two_pow_mul hlow_lt
  rw [hsum]
  have hQs_even : popc (Qs * (1 + 2 ^ g)) % 2 = 0 := by
    have hQslt : Qs < 2 ^ g := by
      have hdiv : 3 ∣ 2 ^ (g - 1) + 1 :=
        three_dvd_two_pow_add_one_of_odd (by omega)
      have h3 : 3 * Qs = 2 ^ (g - 1) + 1 := Nat.mul_div_cancel' hdiv
      have hlt0 : 2 ^ (g - 1) + 1 < 3 * 2 ^ (g - 1) := by
        have h1 : 1 ≤ 2 ^ (g - 1) := Nat.one_le_two_pow
        omega
      have : 3 * Qs < 3 * 2 ^ (g - 1) := by rwa [h3]
      have : Qs < 2 ^ (g - 1) := Nat.lt_of_mul_lt_mul_left this
      have : 2 ^ (g - 1) ≤ 2 ^ g := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have : popc (Qs * (1 + 2 ^ g)) = 2 * popc Qs := popc_one_add_two_pow_mul hQslt
    omega
  have hlow_even : popc (Rb * (1 + 2 ^ g)) % 2 = 0 := by
    by_cases ht : g / 2 ≤ b
    · have hpar : b % 2 = (g / 2) % 2 := hcond ht
      have hfour : (2 : ℕ) ^ g = 4 ^ (g / 2) := by
        calc (2 : ℕ) ^ g
            = 2 ^ (2 * (g / 2)) := by congr 1; omega
          _ = (2 ^ 2) ^ (g / 2) := (pow_mul (2 : ℕ) 2 (g / 2))
          _ = 4 ^ (g / 2) := rfl
      have hpop : popc (Rb * (1 + 2 ^ g)) = b + g / 2 := by
        rw [hfour]
        simpa [Rb] using popc_R_mul_one_add_four_pow (t := g / 2) ht
      rw [hpop]
      omega
    · have hgt : b < g / 2 := by omega
      have hdecomp' : Rb * (1 + 2 ^ g) = Rb + 2 ^ g * Rb := by ring
      rw [hdecomp']
      have hRblt : Rb < 2 ^ g := by
        have hRb2 : Rb < 2 ^ (2 * b) := Rb_lt b
        have h2bg : 2 * b < g := by omega
        have hpow : 2 ^ (2 * b) ≤ 2 ^ g :=
          Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h2bg)
        omega
      rw [popc_add_two_pow_mul hRblt]
      omega
  omega

lemma popc_odd_part_choose_three_even_gap {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (heven : (ea - b) % 2 = 0) (hne : 2 ≤ ea - b)
    (hcond : (ea - b) / 2 ≤ b → b % 2 = ((ea - b) / 2) % 2) :
    popc (((2 ^ ea + 2 ^ b + 1) * (2 ^ (ea - b) + 1) * (2 ^ ea + 2 ^ b - 1)) / 3) % 2 = 0 := by
  set g := ea - b
  have hea : ea = b + g := by omega
  have hprod := sq_sub_one_of_three_bit ea b
  have hrewrite :
      ((2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1)) / 3 =
        ((2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) / 3) * (1 + 2 ^ g) := by
    have hmul :
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
          (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) * (1 + 2 ^ g) := by
      calc
        (2 ^ ea + 2 ^ b + 1) * (2 ^ g + 1) * (2 ^ ea + 2 ^ b - 1) =
            ((2 ^ ea + 2 ^ b + 1) * (2 ^ ea + 2 ^ b - 1)) * (1 + 2 ^ g) := by ring
        _ = (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)) * (1 + 2 ^ g) := by
              rw [hprod]
    -- 3 divides the square-difference because g is even
    have hdivR : 3 ∣ 4 ^ b - 1 := three_dvd_four_pow_sub_one b
    have hodd : (g - 1) % 2 = 1 := by omega
    have hdivS : 3 ∣ 2 ^ (g - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd
    have h4 : (4 : ℕ) ^ b = 2 ^ (2 * b) := four_pow_eq b
    have hid :
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
          (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by
      have hpow1 : 2 ^ (2 * b + g + 1) * 2 ^ (g - 1) = 2 ^ (2 * ea) := by
        rw [← pow_add]; congr 1; omega
      have hpow2 : 2 ^ (2 * b + g + 1) = 2 ^ (ea + b + 1) := by
        congr 1; omega
      calc
        2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) =
            2 ^ (2 * b + g + 1) * 2 ^ (g - 1) + 2 ^ (2 * b + g + 1) +
              (2 ^ (2 * b) - 1) := by rw [hpow1, hpow2]
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (2 ^ (2 * b) - 1) := by ring
        _ = 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) + (4 ^ b - 1) := by rw [h4]
        _ = (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) := by ring
    have hdiv :
        3 ∣ 2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1) := by
      have : 3 ∣ (4 ^ b - 1) + 2 ^ (2 * b + g + 1) * (2 ^ (g - 1) + 1) :=
        hdivR.add (hdivS.mul_left _)
      simpa using (hid.symm ▸ this)
    rw [hmul, mul_comm (2 ^ (2 * ea) + 2 ^ (ea + b + 1) + (2 ^ (2 * b) - 1)),
      Nat.mul_div_assoc _ hdiv, mul_comm]
  rw [hrewrite, hea]
  exact popc_Qbig_mul_even_gap hb heven hne (by simpa [g] using hcond)

lemma popc_choose_three_three_bit_even_gap {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (heven : (ea - b) % 2 = 0) (hne : 2 ≤ ea - b)
    (hcond : (ea - b) / 2 ≤ b → b % 2 = ((ea - b) / 2) % 2) :
    popc (Nat.choose (2 ^ ea + 2 ^ b + 1) 3) % 2 = 0 := by
  rw [choose_three_of_three_bit_odd hba hb, popc_mul_two_pow]
  exact popc_odd_part_choose_three_even_gap hba hb heven hne hcond

lemma a_ne_zero_three_bit_even_gap {ea b : ℕ}
    (hba : b < ea) (hb : 1 ≤ b) (heven : (ea - b) % 2 = 0) (hne : 2 ≤ ea - b)
    (hcond : (ea - b) / 2 ≤ b → b % 2 = ((ea - b) / 2) % 2) :
    _root_.a (2 ^ ea + 2 ^ b + 1) ≠ 0 := by
  have hpow : 2 ≤ 2 ^ ea := by
    have : 2 ^ 1 ≤ 2 ^ ea := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hn : 3 ≤ 2 ^ ea + 2 ^ b + 1 := by
    have : 2 ≤ 2 ^ ea + 2 ^ b := hpow.trans (Nat.le_add_right _ _)
    exact Nat.succ_le_succ this
  refine a_ne_zero_of_witness (2 ^ ea + 2 ^ b + 1) 3 (by decide) hn ?_
  exact popc_choose_three_three_bit_even_gap hba hb heven hne hcond


/-! ### Even 3-bit numbers: `C(n,2)` when the odd part sits below the valuation. -/

lemma m_sq_three_bit (A B : ℕ) :
    (2 ^ A + 2 ^ B + 1) * (2 ^ A + 2 ^ B + 1) =
      2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) + 2 ^ (B + 1) := by
  have hA : (2 : ℕ) ^ (A + 1) = 2 * 2 ^ A := two_pow_succ' A
  have hB : (2 : ℕ) ^ (B + 1) = 2 * 2 ^ B := two_pow_succ' B
  have hAB : (2 : ℕ) ^ (A + B + 1) = 2 * 2 ^ A * 2 ^ B := by
    rw [show A + B + 1 = (A + B) + 1 from rfl, two_pow_succ', pow_add]
    ring
  have h2A : (2 : ℕ) ^ (2 * A) = 2 ^ A * 2 ^ A := by
    rw [two_mul, pow_add]
  have h2B : (2 : ℕ) ^ (2 * B) = 2 ^ B * 2 ^ B := by
    rw [two_mul, pow_add]
  rw [hA, hB, hAB, h2A, h2B]
  ring

lemma two_pow_sub_ones_sub_two {e A B : ℕ} (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ e - 1 - 2 ^ A - 2 ^ B =
      ∑ i ∈ (Finset.range e \ {A, B}), (2 : ℕ) ^ i := by
  have hr : ∑ i ∈ Finset.range e, (2 : ℕ) ^ i = 2 ^ e - 1 := geom_sum_pow_two e
  have hAin : A ∈ Finset.range e := by simp [hA]
  have hBin : B ∈ Finset.range e := by simp [hB]
  have hss : ({A, B} : Finset ℕ) ⊆ Finset.range e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hAin, hBin]
  have hsum :
      ∑ i ∈ Finset.range e, (2 : ℕ) ^ i =
        ∑ i ∈ {A, B}, (2 : ℕ) ^ i + ∑ i ∈ Finset.range e \ {A, B}, 2 ^ i := by
    rw [← Finset.sum_sdiff hss, add_comm]
  have hsumAB : ∑ i ∈ ({A, B} : Finset ℕ), (2 : ℕ) ^ i = 2 ^ A + 2 ^ B := by
    simp [Finset.sum_pair hAB]
  have h1 : 1 ≤ (2 : ℕ) ^ e := Nat.one_le_two_pow
  have hleAB : 2 ^ A + 2 ^ B ≤ 2 ^ e - 1 := by
    have hle :=
      Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (2 : ℕ) ^ i) hss
        (fun _ _ _ => Nat.zero_le _)
    omega
  have : (2 : ℕ) ^ e - 1 - 2 ^ A - 2 ^ B =
      (∑ i ∈ Finset.range e, (2 : ℕ) ^ i) - (2 ^ A + 2 ^ B) := by
    omega
  rw [this, hsum, hsumAB, Nat.add_sub_cancel_left]

lemma popc_two_pow_sub_ones_sub_two {e A B : ℕ}
    (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    popc (2 ^ e - 1 - 2 ^ A - 2 ^ B) = e - 2 := by
  rw [two_pow_sub_ones_sub_two hA hB hAB, popc_sum_two_pow_finset]
  have hAin : A ∈ Finset.range e := by simp [hA]
  have hBin : B ∈ Finset.range e := by simp [hB]
  have hss : ({A, B} : Finset ℕ) ⊆ Finset.range e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [hAin, hBin]
  have hinter : ({A, B} : Finset ℕ) ∩ Finset.range e = {A, B} := by
    rw [Finset.inter_comm, Finset.inter_eq_right.mpr hss]
  rw [Finset.card_sdiff, hinter, Finset.card_range]
  have hcard : ({A, B} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hAB]
  omega

lemma choose_two_of_even_three_bit {e A B : ℕ} (he : 1 ≤ e) :
    Nat.choose (2 ^ e * (2 ^ A + 2 ^ B + 1)) 2 =
      2 ^ (e - 1) * ((2 ^ A + 2 ^ B + 1) * (2 ^ e * (2 ^ A + 2 ^ B + 1) - 1)) := by
  set m := 2 ^ A + 2 ^ B + 1
  set n := 2 ^ e * m
  have hm1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
  have hn2 : 2 ≤ n := by
    have h2 : 2 ≤ 2 ^ e := by
      have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
      simpa using this
    have : 2 ^ e ≤ 2 ^ e * m := Nat.le_mul_of_pos_right _ hm1
    exact h2.trans this
  rw [Nat.choose_two_right]
  have hnm : n * (n - 1) = 2 ^ e * (m * (n - 1)) := by
    rw [show n = 2 ^ e * m from rfl]
    ring
  have he2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    have : e = e - 1 + 1 := by omega
    rw [this, two_pow_succ', Nat.add_sub_cancel]
  have hdiv : n * (n - 1) / 2 = 2 ^ (e - 1) * (m * (n - 1)) := by
    have : n * (n - 1) = 2 * (2 ^ (e - 1) * (m * (n - 1))) := by
      rw [hnm, he2]
      ring
    rw [this, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have hnm1 : n - 1 = 2 ^ e * m - 1 := rfl
  rw [hdiv, hnm1]

lemma mul_shift_sub_eq {e A B : ℕ} :
    (2 ^ A + 2 ^ B + 1) * (2 ^ e * (2 ^ A + 2 ^ B + 1) - 1) =
      2 ^ e * ((2 ^ A + 2 ^ B + 1) * (2 ^ A + 2 ^ B + 1)) - (2 ^ A + 2 ^ B + 1) := by
  set m := 2 ^ A + 2 ^ B + 1
  have : m * (2 ^ e * m - 1) = m * (2 ^ e * m) - m * 1 :=
    Nat.mul_sub_left_distrib m (2 ^ e * m) 1
  rw [this, mul_one]
  ring

lemma m_sq_shift_sub {e A B : ℕ} :
    2 ^ e * ((2 ^ A + 2 ^ B + 1) * (2 ^ A + 2 ^ B + 1)) - (2 ^ A + 2 ^ B + 1) =
      2 ^ e * (2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) +
        2 ^ (B + 1)) - (2 ^ A + 2 ^ B + 1) := by
  rw [m_sq_three_bit A B]

lemma two_pow_add_two_le_of_lt {e A B : ℕ}
    (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ A + 2 ^ B + 1 ≤ 2 ^ e := by
  have he2 : 2 ≤ e := by
    have : 1 ≤ e := by
      cases e with
      | zero =>
        exact False.elim (Nat.not_lt_zero _ hA)
      | succ _ => omega
    have : ¬ (A = 0 ∧ B = 0) := by
      intro h; exact hAB (h.1.trans h.2.symm)
    omega
  wlog hBA : B < A generalizing A B
  · have hlt : A < B := lt_of_le_of_ne (Nat.le_of_not_lt hBA) hAB
    simpa [add_comm (2 ^ A)] using this hB hA hAB.symm hlt
  have hAe : 2 ^ A ≤ 2 ^ (e - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hBe : 2 ^ B ≤ 2 ^ (e - 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hsum : 2 ^ (e - 1) + 2 ^ (e - 2) + 1 ≤ 2 ^ e := by
    have hsplit : 2 ^ e = 2 * 2 ^ (e - 1) := by
      calc 2 ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
    have hdouble : 2 * 2 ^ (e - 1) = 2 ^ (e - 1) + 2 ^ (e - 1) := two_mul _
    have hhalf : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := by
      calc 2 ^ (e - 1) = 2 ^ (e - 2 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 2) := two_pow_succ' _
    have hdouble' : 2 * 2 ^ (e - 2) = 2 ^ (e - 2) + 2 ^ (e - 2) := two_mul _
    have hone : 1 ≤ 2 ^ (e - 2) := Nat.one_le_two_pow
    omega
  omega

lemma high_plus_low_of_even_three_bit {e A B : ℕ}
    (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ e * (2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) +
        2 ^ (B + 1)) - (2 ^ A + 2 ^ B + 1) =
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) + (2 ^ e - 1 - 2 ^ A - 2 ^ B) := by
  have hleAB : 2 ^ A + 2 ^ B + 1 ≤ 2 ^ e := two_pow_add_two_le_of_lt hA hB hAB
  have hdist :
      2 ^ e * (2 ^ (2 * A) + 2 ^ (2 * B) + 1 + 2 ^ (A + B + 1) + 2 ^ (A + 1) +
          2 ^ (B + 1)) =
        2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) := by
    simp only [mul_add, mul_one]
    simp [← pow_add]
    ac_rfl
  rw [hdist]
  have hle' : 2 ^ A + 2 ^ B + 1 ≤
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) := by
    have hpos : 2 ^ e ≤
        2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) := by
      have h1 : 1 ≤ (2 : ℕ) ^ (e + 2 * A) := Nat.one_le_two_pow
      have h2 : 1 ≤ (2 : ℕ) ^ (e + 2 * B) := Nat.one_le_two_pow
      have h3 : 1 ≤ (2 : ℕ) ^ (e + A + B + 1) := Nat.one_le_two_pow
      have h4 : 1 ≤ (2 : ℕ) ^ (e + A + 1) := Nat.one_le_two_pow
      have h5 : 1 ≤ (2 : ℕ) ^ (e + B + 1) := Nat.one_le_two_pow
      omega
    exact hleAB.trans hpos
  have hrearr :
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ e + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) - (2 ^ A + 2 ^ B + 1) =
        2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) + (2 ^ e - (2 ^ A + 2 ^ B + 1)) := by
    omega
  rw [hrearr]
  congr 1
  omega

lemma popc_five_high {e A B : ℕ}
    (hAB : B + 2 ≤ A) (hB : 2 ≤ B) (hne : A ≠ 2 * B - 1) :
    popc (2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
      2 ^ (e + A + 1) + 2 ^ (e + B + 1)) = 5 := by
  have hne' : A + 1 ≠ 2 * B := by
    intro h
    apply hne
    omega
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have : 2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
      2 ^ (e + 2 * A) + 2 ^ (e + (A + B + 1)) + 2 ^ (e + 2 * B) +
        2 ^ (e + (A + 1)) + 2 ^ (e + (B + 1)) := by ring
    rw [this]
    exact popc_sum_five_pow
      (e1 := e + 2 * A) (e2 := e + (A + B + 1)) (e3 := e + 2 * B)
      (e4 := e + (A + 1)) (e5 := e + (B + 1))
      (by omega) (by omega) (by omega) (by omega)
  · have : 2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
        2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
      2 ^ (e + 2 * A) + 2 ^ (e + (A + B + 1)) + 2 ^ (e + (A + 1)) +
        2 ^ (e + 2 * B) + 2 ^ (e + (B + 1)) := by ring
    rw [this]
    exact popc_sum_five_pow
      (e1 := e + 2 * A) (e2 := e + (A + B + 1)) (e3 := e + (A + 1))
      (e4 := e + 2 * B) (e5 := e + (B + 1))
      (by omega) (by omega) (by omega) (by omega)

lemma low_lt_high_start {e A B : ℕ} (hA : A < e) (hB : B < e) (hAB : A ≠ B) :
    2 ^ e - 1 - 2 ^ A - 2 ^ B < 2 ^ (e + B + 1) := by
  have h1 : 1 ≤ (2 : ℕ) ^ e := Nat.one_le_two_pow
  have hle : 2 ^ A + 2 ^ B + 1 ≤ 2 ^ e := two_pow_add_two_le_of_lt hA hB hAB
  have heq : 2 ^ e - 1 - 2 ^ A - 2 ^ B = 2 ^ e - (2 ^ A + 2 ^ B + 1) := by
    have hA1 : 1 ≤ (2 : ℕ) ^ A := Nat.one_le_two_pow
    have hB1 : 1 ≤ (2 : ℕ) ^ B := Nat.one_le_two_pow
    omega
  rw [heq]
  have hbound : 2 ^ e - (2 ^ A + 2 ^ B + 1) ≤ 2 ^ e := Nat.sub_le _ _
  have hpow : 2 ^ e < 2 ^ (e + B + 1) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  omega

lemma popc_odd_part_even_three_bit_easy {e A B : ℕ}
    (heA : A < e) (hB : 2 ≤ B) (hAB : B + 2 ≤ A) (hne : A ≠ 2 * B - 1) :
    popc ((2 ^ A + 2 ^ B + 1) * (2 ^ e * (2 ^ A + 2 ^ B + 1) - 1)) = e + 3 := by
  have hBlt : B < e := by omega
  have hAB' : A ≠ B := by omega
  have hform := mul_shift_sub_eq (e := e) (A := A) (B := B)
  rw [hform, m_sq_shift_sub, high_plus_low_of_even_three_bit heA hBlt hAB']
  have hlow_lt : 2 ^ e - 1 - 2 ^ A - 2 ^ B < 2 ^ (e + B + 1) :=
    low_lt_high_start heA hBlt hAB'
  have hhigh_mul :
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) =
        2 ^ (e + B + 1) *
          (2 ^ (e + 2 * A - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
            2 ^ (e + A + B + 1 - (e + B + 1)) + 2 ^ (e + A + 1 - (e + B + 1)) +
            1) := by
    have h1 : 2 ^ (e + 2 * A) = 2 ^ (e + B + 1) * 2 ^ (e + 2 * A - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h2 : 2 ^ (e + 2 * B) = 2 ^ (e + B + 1) * 2 ^ (e + 2 * B - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h3 : 2 ^ (e + A + B + 1) =
        2 ^ (e + B + 1) * 2 ^ (e + A + B + 1 - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h4 : 2 ^ (e + A + 1) =
        2 ^ (e + B + 1) * 2 ^ (e + A + 1 - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have h5 : 2 ^ (e + B + 1) = 2 ^ (e + B + 1) * 1 := by ring
    rw [h1, h2, h3, h4, h5]
    ring
  have hsplit :
      2 ^ (e + 2 * A) + 2 ^ (e + 2 * B) + 2 ^ (e + A + B + 1) +
          2 ^ (e + A + 1) + 2 ^ (e + B + 1) + (2 ^ e - 1 - 2 ^ A - 2 ^ B) =
        2 ^ (e + B + 1) *
          (2 ^ (e + 2 * A - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
            2 ^ (e + A + B + 1 - (e + B + 1)) + 2 ^ (e + A + 1 - (e + B + 1)) +
            1) + (2 ^ e - 1 - 2 ^ A - 2 ^ B) := by
    rw [hhigh_mul]
  rw [hsplit, popc_two_pow_mul_add hlow_lt]
  have hcoeff :
      popc (2 ^ (e + 2 * A - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
        2 ^ (e + A + B + 1 - (e + B + 1)) + 2 ^ (e + A + 1 - (e + B + 1)) +
        1) = 5 := by
    rw [← popc_mul_two_pow (e + B + 1), ← hhigh_mul]
    exact popc_five_high (e := e) hAB hB hne
  rw [hcoeff, popc_two_pow_sub_ones_sub_two heA hBlt hAB']
  omega

lemma popc_choose_two_even_three_bit_easy {e A B : ℕ}
    (he : 1 ≤ e) (heA : A < e) (hB : 2 ≤ B) (hAB : B + 2 ≤ A)
    (hne : A ≠ 2 * B - 1) (hodd : e % 2 = 1) :
    popc (Nat.choose (2 ^ e * (2 ^ A + 2 ^ B + 1)) 2) % 2 = 0 := by
  rw [choose_two_of_even_three_bit he, popc_mul_two_pow]
  have hpop := popc_odd_part_even_three_bit_easy heA hB hAB hne
  omega

lemma three_bit_even_factor {e1 e2 e3 : ℕ} (h32 : e3 < e2) (h21 : e2 < e1) :
    2 ^ e1 + 2 ^ e2 + 2 ^ e3 =
      2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) := by
  have h31 : e3 < e1 := h32.trans h21
  have h1 : 2 ^ e1 = 2 ^ e3 * 2 ^ (e1 - e3) := by
    rw [← pow_add]; congr 1; omega
  have h2 : 2 ^ e2 = 2 ^ e3 * 2 ^ (e2 - e3) := by
    rw [← pow_add]; congr 1; omega
  rw [h1, h2]
  ring

lemma a_ne_zero_even_three_bit_easy {e1 e2 e3 : ℕ}
    (h32 : e3 < e2) (h21 : e2 < e1)
    (heA : e1 - e3 < e3) (hB : 2 ≤ e2 - e3)
    (hAB : e2 - e3 + 2 ≤ e1 - e3)
    (hne : e1 - e3 ≠ 2 * (e2 - e3) - 1)
    (hodd : e3 % 2 = 1) :
    _root_.a (2 ^ e1 + 2 ^ e2 + 2 ^ e3) ≠ 0 := by
  have he : 1 ≤ e3 := by omega
  have hn : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 =
      2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) :=
    three_bit_even_factor h32 h21
  have hpow : 2 ≤ 2 ^ e1 := by
    have : 2 ^ 1 ≤ 2 ^ e1 := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hk : 2 ≤ 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := by
    have : 2 ^ e1 ≤ 2 ^ e1 + 2 ^ e2 := Nat.le_add_right _ _
    have : 2 ^ e1 + 2 ^ e2 ≤ 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := Nat.le_add_right _ _
    exact hpow.trans (‹2 ^ e1 ≤ 2 ^ e1 + 2 ^ e2›.trans this)
  refine a_ne_zero_of_witness (2 ^ e1 + 2 ^ e2 + 2 ^ e3) 2 (by decide) hk ?_
  rw [hn]
  exact popc_choose_two_even_three_bit_easy he heA hB hAB hne hodd

lemma high_adjacent_merge (e B : ℕ) :
    2 ^ (e + 2 * (B + 1)) + 2 ^ (e + 2 * B) + 2 ^ (e + (B + 1) + B + 1) +
      2 ^ (e + (B + 1) + 1) + 2 ^ (e + B + 1) =
    2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) + 2 ^ (e + B + 1) := by
  have h1 : e + 2 * (B + 1) = e + 2 * B + 2 := by omega
  have h2 : e + (B + 1) + B + 1 = e + 2 * B + 2 := by omega
  have h3 : e + (B + 1) + 1 = e + B + 2 := by omega
  rw [h1, h2, h3]
  have h4 : 2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B + 2) = 2 ^ (e + 2 * B + 3) := by
    rw [← two_mul, ← two_pow_succ']
  have hre :
      2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B) + 2 ^ (e + 2 * B + 2) +
          2 ^ (e + B + 2) + 2 ^ (e + B + 1) =
        (2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B + 2)) + 2 ^ (e + 2 * B) +
          2 ^ (e + B + 2) + 2 ^ (e + B + 1) := by ring
  rw [hre, h4]

lemma popc_four_high_adjacent {e B : ℕ} (hB : 3 ≤ B) :
    popc (2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) +
      2 ^ (e + B + 1)) = 4 := by
  have h1 : e + B + 1 < e + B + 2 := by omega
  have h2 : e + B + 2 < e + 2 * B := by omega
  have h3 : e + 2 * B < e + 2 * B + 3 := by omega
  exact popc_sum_four_pow (e1 := e + 2 * B + 3) (e2 := e + 2 * B)
    (e3 := e + B + 2) (e4 := e + B + 1) h3 h2 h1

lemma popc_odd_part_even_three_bit_adjacent {e B : ℕ}
    (heA : B + 1 < e) (hB : 3 ≤ B) :
    popc ((2 ^ (B + 1) + 2 ^ B + 1) * (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1) - 1)) =
      e + 2 := by
  have hBlt : B < e := by omega
  have hAB' : (B + 1 : ℕ) ≠ B := by omega
  have hform := mul_shift_sub_eq (e := e) (A := B + 1) (B := B)
  rw [hform, m_sq_shift_sub, high_plus_low_of_even_three_bit heA hBlt hAB']
  rw [high_adjacent_merge]
  have hlow_lt : 2 ^ e - 1 - 2 ^ (B + 1) - 2 ^ B < 2 ^ (e + B + 1) :=
    low_lt_high_start heA hBlt hAB'
  have hhigh_mul :
      2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) + 2 ^ (e + B + 1) =
        2 ^ (e + B + 1) *
          (2 ^ (e + 2 * B + 3 - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
            2 ^ (e + B + 2 - (e + B + 1)) + 1) := by
    have k1 : 2 ^ (e + 2 * B + 3) =
        2 ^ (e + B + 1) * 2 ^ (e + 2 * B + 3 - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have k2 : 2 ^ (e + 2 * B) =
        2 ^ (e + B + 1) * 2 ^ (e + 2 * B - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have k3 : 2 ^ (e + B + 2) =
        2 ^ (e + B + 1) * 2 ^ (e + B + 2 - (e + B + 1)) := by
      rw [← pow_add]; congr 1; omega
    have k4 : 2 ^ (e + B + 1) = 2 ^ (e + B + 1) * 1 := by ring
    rw [k1, k2, k3, k4]; ring
  have hsplit :
      2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) +
          2 ^ (e + B + 1) + (2 ^ e - 1 - 2 ^ (B + 1) - 2 ^ B) =
        2 ^ (e + B + 1) *
          (2 ^ (e + 2 * B + 3 - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
            2 ^ (e + B + 2 - (e + B + 1)) + 1) +
          (2 ^ e - 1 - 2 ^ (B + 1) - 2 ^ B) := by
    rw [hhigh_mul]
  rw [hsplit, popc_two_pow_mul_add hlow_lt]
  have hcoeff :
      popc (2 ^ (e + 2 * B + 3 - (e + B + 1)) + 2 ^ (e + 2 * B - (e + B + 1)) +
        2 ^ (e + B + 2 - (e + B + 1)) + 1) = 4 := by
    rw [← popc_mul_two_pow (e + B + 1), ← hhigh_mul]
    exact popc_four_high_adjacent hB
  rw [hcoeff, popc_two_pow_sub_ones_sub_two heA hBlt hAB']
  omega

lemma popc_choose_two_even_three_bit_adjacent {e B : ℕ}
    (he : 1 ≤ e) (heA : B + 1 < e) (hB : 3 ≤ B) (heven : e % 2 = 0) :
    popc (Nat.choose (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1)) 2) % 2 = 0 := by
  rw [choose_two_of_even_three_bit he, popc_mul_two_pow]
  have hpop := popc_odd_part_even_three_bit_adjacent heA hB
  omega

lemma a_ne_zero_even_three_bit_adjacent {e1 e2 e3 : ℕ}
    (h32 : e3 < e2) (h21 : e2 < e1)
    (hA : e1 = e2 + 1) (hB : 3 ≤ e2 - e3)
    (heA : e1 - e3 < e3) (heven : e3 % 2 = 0) :
    _root_.a (2 ^ e1 + 2 ^ e2 + 2 ^ e3) ≠ 0 := by
  have he : 1 ≤ e3 := by omega
  have hn : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 =
      2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) :=
    three_bit_even_factor h32 h21
  have hAeq : e1 - e3 = (e2 - e3) + 1 := by omega
  have hpow : 2 ≤ 2 ^ e1 := by
    have : 2 ^ 1 ≤ 2 ^ e1 := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hk : 2 ≤ 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := by
    have : 2 ^ e1 ≤ 2 ^ e1 + 2 ^ e2 := Nat.le_add_right _ _
    have : 2 ^ e1 + 2 ^ e2 ≤ 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := Nat.le_add_right _ _
    exact hpow.trans (‹2 ^ e1 ≤ 2 ^ e1 + 2 ^ e2›.trans this)
  refine a_ne_zero_of_witness (2 ^ e1 + 2 ^ e2 + 2 ^ e3) 2 (by decide) hk ?_
  rw [hn, hAeq]
  exact popc_choose_two_even_three_bit_adjacent he (by omega) hB heven

lemma popc_le_succ_log2 (t : ℕ) : popc t ≤ t.log2 + 1 := by
  unfold popc
  simpa [List.length_range] using
    (List.countP_le_length (p := t.testBit) (l := List.range (t.log2 + 1)))

lemma popc_le_of_lt_two_pow {t e : ℕ} (h : t < 2 ^ e) : popc t ≤ e := by
  by_cases ht : t = 0
  · subst ht; simp [popc_zero]
  · have hlog : t.log2 < e := (Nat.log2_lt ht).2 h
    have := popc_le_succ_log2 t
    omega

lemma popc_two_pow_sub_one_sub {e k : ℕ} (hk : k < 2 ^ e) :
    popc (2 ^ e - 1 - k) = e - popc k := by
  induction e generalizing k with
  | zero =>
    have : k = 0 := by
      have : k < 1 := by simpa using hk
      omega
    subst this
    simp [popc_zero]
  | succ e ih =>
    have h2 : 2 ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 := by
      have : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ, mul_comm]
      have hle : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      omega
    rw [h2]
    have hk2 : k / 2 < 2 ^ e := by
      have : k < 2 * 2 ^ e := by
        rwa [pow_succ, mul_comm] at hk
      omega
    have hpos : 1 ≤ 2 * (2 ^ e - 1) + 1 := by omega
    rcases Nat.mod_two_eq_zero_or_one k with he | ho
    · have hrep : 2 * (2 ^ e - 1) + 1 - k = 2 * (2 ^ e - 1 - k / 2) + 1 := by
        have hk' : k = 2 * (k / 2) := by omega
        have hle : k / 2 ≤ 2 ^ e - 1 := by
          have : k / 2 < 2 ^ e := hk2
          have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
          omega
        omega
      rw [hrep, popc_rec]
      have hmod : (2 * (2 ^ e - 1 - k / 2) + 1) % 2 = 1 := by simp
      have hdiv : (2 * (2 ^ e - 1 - k / 2) + 1) / 2 = 2 ^ e - 1 - k / 2 := by
        rw [Nat.mul_add_div (by decide : 0 < 2)]
        simp
      rw [hmod, hdiv, ih hk2]
      have hpk : popc k = popc (k / 2) := by
        rw [popc_rec, he, zero_add]
      have hle : popc (k / 2) ≤ e := popc_le_of_lt_two_pow hk2
      omega
    · have hrep : 2 * (2 ^ e - 1) + 1 - k = 2 * (2 ^ e - 1 - k / 2) := by
        have hk' : k = 2 * (k / 2) + 1 := by omega
        have hle : k / 2 ≤ 2 ^ e - 1 := by
          have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
          omega
        omega
      rw [hrep, popc_rec]
      have hmod : (2 * (2 ^ e - 1 - k / 2)) % 2 = 0 := by simp
      have hdiv : (2 * (2 ^ e - 1 - k / 2)) / 2 = 2 ^ e - 1 - k / 2 := by
        rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
      rw [hmod, hdiv, zero_add, ih hk2]
      have hpk : popc k = popc (k / 2) + 1 := by
        rw [popc_rec, ho]
        omega
      have hle : popc (k / 2) ≤ e := popc_le_of_lt_two_pow hk2
      omega

lemma choose_two_of_two_pow_mul {e m : ℕ} (he : 1 ≤ e) :
    Nat.choose (2 ^ e * m) 2 = 2 ^ (e - 1) * (m * (2 ^ e * m - 1)) := by
  set n := 2 ^ e * m
  by_cases hm0 : m = 0
  · subst hm0
    change (0 : ℕ).choose 2 = _
    simp [Nat.choose_eq_zero_of_lt (by decide : (0 : ℕ) < 2)]
  have hm1 : 1 ≤ m := by omega
  have hn2 : 2 ≤ n := by
    have h2 : 2 ≤ 2 ^ e := by
      have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
      simpa using this
    have : 2 ^ e ≤ 2 ^ e * m := Nat.le_mul_of_pos_right _ hm1
    exact h2.trans this
  rw [Nat.choose_two_right]
  have he2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc 2 ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
  have : n * (n - 1) = 2 * (2 ^ (e - 1) * (m * (n - 1))) := by
    rw [show n = 2 ^ e * m from rfl, he2]
    ring
  rw [this, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma mul_shift_sub_of_lt {e m : ℕ} (hm : 1 ≤ m) (hmlt : m < 2 ^ e) :
    m * (2 ^ e * m - 1) = 2 ^ e * (m * m - 1) + (2 ^ e - m) := by
  have hle : m ≤ 2 ^ e * m := Nat.le_mul_of_pos_left _ (Nat.one_le_two_pow)
  have hmul : m * (2 ^ e * m - 1) = m * (2 ^ e * m) - m := by
    have := Nat.mul_sub_left_distrib m (2 ^ e * m) 1
    simpa [mul_one] using this
  have hsq : m * (2 ^ e * m) = 2 ^ e * (m * m) := by ring
  rw [hmul, hsq]
  have hle2 : 1 ≤ m * m := Nat.mul_le_mul hm hm
  have hre : 2 ^ e * (m * m) - m = 2 ^ e * (m * m - 1) + (2 ^ e - m) := by
    have h1 : 2 ^ e ≤ 2 ^ e * (m * m) :=
      Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt (lt_of_succ_le hle2))
    have : 2 ^ e * (m * m) = 2 ^ e * (m * m - 1) + 2 ^ e := by
      have hdecomp : m * m = (m * m - 1) + 1 := by omega
      conv_lhs => rw [hdecomp]
      rw [mul_add, mul_one]
    have hmle : m ≤ 2 ^ e := Nat.le_of_lt hmlt
    omega
  exact hre

lemma popc_mul_shift_sub_of_lt {e m : ℕ} (hm : 1 ≤ m) (hmlt : m < 2 ^ e)
    (hodd : m % 2 = 1) :
    popc (m * (2 ^ e * m - 1)) = popc (m * m - 1) + e - popc (m - 1) := by
  rw [mul_shift_sub_of_lt hm hmlt]
  have hlow : 2 ^ e - m < 2 ^ e := Nat.sub_lt (Nat.zero_lt_of_lt hmlt) hm
  rw [add_comm (2 ^ e * (m * m - 1)), popc_add_two_pow_mul hlow]
  have hm1 : m - 1 < 2 ^ e := lt_of_le_of_lt (Nat.sub_le _ _) hmlt
  have heq : 2 ^ e - m = 2 ^ e - 1 - (m - 1) := by
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  rw [heq, popc_two_pow_sub_one_sub hm1]
  have hle : popc (m - 1) ≤ e := popc_le_of_lt_two_pow hm1
  omega

lemma popc_choose_two_two_pow_mul_of_lt {e m : ℕ} (he : 1 ≤ e) (hm : 1 ≤ m)
    (hmlt : m < 2 ^ e) (hodd : m % 2 = 1) :
    popc (Nat.choose (2 ^ e * m) 2) = popc (m * m - 1) + e - popc (m - 1) := by
  rw [choose_two_of_two_pow_mul he, popc_mul_two_pow]
  exact popc_mul_shift_sub_of_lt hm hmlt hodd

lemma a_ne_zero_two_pow_mul_of_choose_two {e m : ℕ}
    (he : 1 ≤ e) (hm : 1 ≤ m) (hmlt : m < 2 ^ e) (hodd : m % 2 = 1)
    (hevil : (popc (m * m - 1) + e - popc (m - 1)) % 2 = 0) :
    _root_.a (2 ^ e * m) ≠ 0 := by
  have hpow : 2 ≤ 2 ^ e := by
    have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
    simpa using this
  have hk : 2 ≤ 2 ^ e * m :=
    hpow.trans (Nat.le_mul_of_pos_right _ hm)
  refine a_ne_zero_of_witness (2 ^ e * m) 2 (by decide) hk ?_
  have hpop := popc_choose_two_two_pow_mul_of_lt he hm hmlt hodd
  omega

lemma a_ne_zero_two_pow_mul_of_choose_two_gen {e m : ℕ}
    (he : 1 ≤ e) (hm : 1 ≤ m)
    (hevil : popc (m * (2 ^ e * m - 1)) % 2 = 0) :
    _root_.a (2 ^ e * m) ≠ 0 := by
  have hpow : 2 ≤ 2 ^ e := by
    have : 2 ^ 1 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
    simpa using this
  have hk : 2 ≤ 2 ^ e * m :=
    hpow.trans (Nat.le_mul_of_pos_right _ hm)
  refine a_ne_zero_of_witness (2 ^ e * m) 2 (by decide) hk ?_
  rw [choose_two_of_two_pow_mul he, popc_mul_two_pow]
  exact hevil

lemma popc_sq_sub_one_double_minus {B : ℕ} (hB : 3 ≤ B) :
    popc ((2 ^ (2 * B - 1) + 2 ^ B + 1) * (2 ^ (2 * B - 1) + 2 ^ B + 1) - 1) = 4 := by
  have hA : 1 ≤ 2 * B - 1 := by omega
  have hm : 1 ≤ 2 ^ (2 * B - 1) + 2 ^ B + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hdecomp :
      (2 ^ (2 * B - 1) + 2 ^ B + 1) * (2 ^ (2 * B - 1) + 2 ^ B + 1) - 1 =
        2 ^ (2 * (2 * B - 1)) + 2 ^ (2 * B) + 2 ^ ((2 * B - 1) + B + 1) +
          2 ^ ((2 * B - 1) + 1) + 2 ^ (B + 1) := by
    rw [m_sq_three_bit]
    have hre :
        2 ^ (2 * (2 * B - 1)) + 2 ^ (2 * B) + 1 + 2 ^ ((2 * B - 1) + B + 1) +
            2 ^ ((2 * B - 1) + 1) + 2 ^ (B + 1) =
          (2 ^ (2 * (2 * B - 1)) + 2 ^ (2 * B) + 2 ^ ((2 * B - 1) + B + 1) +
            2 ^ ((2 * B - 1) + 1) + 2 ^ (B + 1)) + 1 := by ring
    rw [hre, Nat.add_sub_cancel]
  rw [hdecomp]
  have hsimp :
      2 ^ (2 * (2 * B - 1)) + 2 ^ (2 * B) + 2 ^ ((2 * B - 1) + B + 1) +
          2 ^ ((2 * B - 1) + 1) + 2 ^ (B + 1) =
        2 ^ (4 * B - 2) + 2 ^ (3 * B) + 2 ^ (2 * B + 1) + 2 ^ (B + 1) := by
    have e1 : 2 * (2 * B - 1) = 4 * B - 2 := by omega
    have e2 : (2 * B - 1) + B + 1 = 3 * B := by omega
    have e3 : (2 * B - 1) + 1 = 2 * B := by omega
    rw [e1, e2, e3]
    have : 2 ^ (2 * B) + 2 ^ (2 * B) = 2 ^ (2 * B + 1) := by
      rw [← two_mul, ← two_pow_succ']
    omega
  rw [hsimp]
  have h1 : B + 1 < 2 * B + 1 := by omega
  have h2 : 2 * B + 1 < 3 * B := by omega
  have h3 : 3 * B < 4 * B - 2 := by omega
  exact popc_sum_four_pow (e1 := 4 * B - 2) (e2 := 3 * B)
    (e3 := 2 * B + 1) (e4 := B + 1) h3 h2 h1

lemma popc_m_sub_one_three_bit {A B : ℕ} (hAB : B < A) :
    popc (2 ^ A + 2 ^ B + 1 - 1) = 2 := by
  have : 2 ^ A + 2 ^ B + 1 - 1 = 2 ^ A + 2 ^ B := Nat.add_sub_cancel _ _
  rw [this, popc_sum_two_pow_distinct hAB]

lemma two_pow_mod_two {n : ℕ} (h : 1 ≤ n) : (2 : ℕ) ^ n % 2 = 0 := by
  have : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    calc (2 : ℕ) ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (n - 1) := two_pow_succ' _
  rw [this]
  simp

lemma three_bit_odd (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    (2 ^ A + 2 ^ B + 1) % 2 = 1 := by
  have hAe : (2 : ℕ) ^ A % 2 = 0 := two_pow_mod_two hA
  have hBe : (2 : ℕ) ^ B % 2 = 0 := two_pow_mod_two hB
  omega

lemma popc_sq_sub_one_B_one {A : ℕ} (hA : 3 ≤ A) :
    popc ((2 ^ A + 2 ^ 1 + 1) * (2 ^ A + 2 ^ 1 + 1) - 1) = 4 := by
  rw [m_sq_three_bit]
  have hre :
      2 ^ (2 * A) + 2 ^ (2 * 1) + 1 + 2 ^ (A + 1 + 1) + 2 ^ (A + 1) + 2 ^ (1 + 1) =
        (2 ^ (2 * A) + 2 ^ (A + 2) + 2 ^ (A + 1) + 2 ^ 3) + 1 := by
    simp [pow_one]
    ring
  rw [hre, Nat.add_sub_cancel]
  have h1 : 3 < A + 1 := by omega
  have h2 : A + 1 < A + 2 := by omega
  have h3 : A + 2 < 2 * A := by omega
  exact popc_sum_four_pow (e1 := 2 * A) (e2 := A + 2) (e3 := A + 1) (e4 := 3)
    h3 h2 h1

lemma popc_sq_sub_one_A2_B1 :
    popc ((2 ^ 2 + 2 ^ 1 + 1) * (2 ^ 2 + 2 ^ 1 + 1) - 1) = 2 := by
  rw [m_sq_three_bit]
  have hre :
      2 ^ (2 * 2) + 2 ^ (2 * 1) + 1 + 2 ^ (2 + 1 + 1) + 2 ^ (2 + 1) + 2 ^ (1 + 1) =
        (2 ^ 5 + 2 ^ 4) + 1 := by
    decide
  rw [hre, Nat.add_sub_cancel]
  exact popc_sum_two_pow_distinct (i := 5) (j := 4) (by decide)

lemma popc_sq_sub_one_A3_B2 :
    popc ((2 ^ 3 + 2 ^ 2 + 1) * (2 ^ 3 + 2 ^ 2 + 1) - 1) = 3 := by
  rw [m_sq_three_bit]
  have hre :
      2 ^ (2 * 3) + 2 ^ (2 * 2) + 1 + 2 ^ (3 + 2 + 1) + 2 ^ (3 + 1) + 2 ^ (2 + 1) =
        (2 ^ 7 + 2 ^ 5 + 2 ^ 3) + 1 := by
    decide
  rw [hre, Nat.add_sub_cancel]
  exact popc_sum_three_pow (e1 := 7) (e2 := 5) (e3 := 3) (by decide) (by decide)

/-- Even 3-bit `n = 2^{e3}(2^A+2^B+1)` with `A < e3` and evil `C(n,2)`. -/
lemma a_ne_zero_even_three_bit_choose_two {e1 e2 e3 : ℕ}
    (h32 : e3 < e2) (h21 : e2 < e1) (he3 : 1 ≤ e3)
    (heA : e1 - e3 < e3)
    (hevil :
      (popc ((2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) - 1)
        + e3 - popc (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1 - 1)) % 2 = 0) :
    _root_.a (2 ^ e1 + 2 ^ e2 + 2 ^ e3) ≠ 0 := by
  have hn : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 =
      2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) :=
    three_bit_even_factor h32 h21
  rw [hn]
  refine a_ne_zero_two_pow_mul_of_choose_two (he := he3)
    (hm := Nat.succ_le_succ (Nat.zero_le _)) ?hmlt
    (three_bit_odd _ _ (by omega) (by omega)) hevil
  have hle :=
    two_pow_add_two_le_of_lt (e := e3) (A := e1 - e3) (B := e2 - e3)
      heA (by omega) (by omega)
  have hodd' := three_bit_odd (e1 - e3) (e2 - e3) (by omega) (by omega)
  have hevenp : (2 : ℕ) ^ e3 % 2 = 0 := two_pow_mod_two he3
  omega

lemma choose_two_of_two_pow_mul_add_one {v q : ℕ} (hv : 1 ≤ v) :
    Nat.choose (2 ^ v * q + 1) 2 = 2 ^ (v - 1) * ((2 ^ v * q + 1) * q) := by
  set n := 2 ^ v * q + 1
  by_cases hq0 : q = 0
  · subst hq0
    change (1 : ℕ).choose 2 = _
    simp
  have hn2 : 2 ≤ n := by
    have h1 : 1 ≤ 2 ^ v := Nat.one_le_two_pow
    have h2 : 2 ^ v ≤ 2 ^ v * q := Nat.le_mul_of_pos_right (2 ^ v) (Nat.pos_of_ne_zero hq0)
    omega
  rw [Nat.choose_two_right]
  have hv2 : 2 ^ v = 2 * 2 ^ (v - 1) := by
    calc 2 ^ v = 2 ^ (v - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (v - 1) := two_pow_succ' _
  have : n * (n - 1) = 2 * (2 ^ (v - 1) * (n * q)) := by
    have hn1 : n - 1 = 2 ^ v * q := Nat.add_sub_cancel _ _
    rw [hn1, show n = 2 ^ v * q + 1 from rfl, hv2]
    ring
  rw [this, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma popc_mul_two_pow_add_of_lt {v q : ℕ} (hq : q < 2 ^ v) :
    popc (2 ^ v * (q * q) + q) = popc (q * q) + popc q := by
  rw [add_comm]
  exact popc_add_two_pow_mul hq

lemma popc_choose_two_two_pow_mul_add_one {v q : ℕ} (hv : 1 ≤ v) (_hqpos : 1 ≤ q)
    (hqlt : q < 2 ^ v) :
    popc (Nat.choose (2 ^ v * q + 1) 2) = popc (q * q) + popc q := by
  rw [choose_two_of_two_pow_mul_add_one hv, popc_mul_two_pow]
  have : (2 ^ v * q + 1) * q = 2 ^ v * (q * q) + q := by ring
  rw [this, popc_mul_two_pow_add_of_lt hqlt]

lemma a_ne_zero_two_pow_mul_add_one_of_choose_two {v q : ℕ} (hv : 1 ≤ v) (hqpos : 1 ≤ q)
    (hqlt : q < 2 ^ v) (hevil : (popc (q * q) + popc q) % 2 = 0) :
    _root_.a (2 ^ v * q + 1) ≠ 0 := by
  have hpow : 2 ≤ 2 ^ v := by
    have : 2 ^ 1 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv
    simpa using this
  have hk : 2 ≤ 2 ^ v * q + 1 := by
    have : 2 ^ v ≤ 2 ^ v * q := Nat.le_mul_of_pos_right _ hqpos
    omega
  refine a_ne_zero_of_witness (2 ^ v * q + 1) 2 (by decide) hk ?_
  have hpop := popc_choose_two_two_pow_mul_add_one hv hqpos hqlt
  omega

lemma a_ne_zero_two_pow_mul_add_one_of_choose_two_gen {v q : ℕ}
    (hv : 1 ≤ v) (hqpos : 1 ≤ q)
    (hevil : popc ((2 ^ v * q + 1) * q) % 2 = 0) :
    _root_.a (2 ^ v * q + 1) ≠ 0 := by
  have hpow : 2 ≤ 2 ^ v := by
    have : 2 ^ 1 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv
    simpa using this
  have hk : 2 ≤ 2 ^ v * q + 1 := by
    have : 2 ^ v ≤ 2 ^ v * q := Nat.le_mul_of_pos_right _ hqpos
    omega
  refine a_ne_zero_of_witness (2 ^ v * q + 1) 2 (by decide) hk ?_
  rw [choose_two_of_two_pow_mul_add_one hv, popc_mul_two_pow]
  exact hevil

lemma choose_three_of_two_pow_mul {e m : ℕ} (he : 2 ≤ e) :
    Nat.choose (2 ^ e * m) 3 =
      2 ^ e * (m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1) / 3) := by
  set n := 2 ^ e * m
  by_cases hm0 : m = 0
  · subst hm0
    change (0 : ℕ).choose 3 = _
    simp
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have hdesc : n.descFactorial 3 = (n - 2) * (n - 1) * n := descFactorial_three _
  have he2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc 2 ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
  have hn2 : n - 2 = 2 * (2 ^ (e - 1) * m - 1) := by
    have hn' : n = 2 * (2 ^ (e - 1) * m) := by
      rw [show n = 2 ^ e * m from rfl, he2]; ring
    have hle : 1 ≤ 2 ^ (e - 1) * m :=
      Nat.one_le_two_pow.trans (Nat.le_mul_of_pos_right (2 ^ (e - 1)) hm1)
    omega
  have hprod :
      n.descFactorial 3 =
        2 ^ (e + 1) * (m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1)) := by
    rw [hdesc, hn2, show n = 2 ^ e * m from rfl]
    have : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ, mul_comm]
    rw [this]
    ring
  have hfac : n.descFactorial 3 = 6 * n.choose 3 := by
    have : (3 : ℕ) ! = 6 := by decide
    rw [Nat.descFactorial_eq_factorial_mul_choose, this]
  rw [hprod] at hfac
  have h2e : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ, mul_comm]
  rw [h2e] at hfac
  have h6 : (6 : ℕ) = 2 * 3 := by decide
  have hcancel :
      2 ^ e * (m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1)) = 3 * n.choose 3 := by
    have : 2 * (2 ^ e * (m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1))) =
        2 * (3 * n.choose 3) := by
      rw [h6] at hfac
      convert hfac using 1 <;> ring
    exact Nat.mul_left_cancel (by decide : 0 < 2) this
  have h3dvd : 3 ∣ m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1) := by
    have : 3 ∣ 2 ^ e * (m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1)) :=
      ⟨n.choose 3, by rw [hcancel, mul_comm]⟩
    have hcop : Nat.Coprime 3 (2 ^ e) := by
      have : Nat.Coprime 3 2 := by decide
      simpa using this.pow_right e
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop this
  have : n.choose 3 =
      2 ^ e * (m * (2 ^ e * m - 1) * (2 ^ (e - 1) * m - 1)) / 3 := by
    apply Nat.eq_div_of_mul_eq_left (by decide : (3 : ℕ) ≠ 0)
    rw [hcancel]; ring
  rw [this, Nat.mul_div_assoc _ h3dvd]

lemma seven_mul_two_pow_sub_one (e : ℕ) :
    7 * 2 ^ e - 1 = 2 ^ (e + 2) + 2 ^ (e + 1) + 2 ^ e - 1 := by
  have h7 : (7 : ℕ) * 2 ^ e = 4 * 2 ^ e + 2 * 2 ^ e + 2 ^ e := by ring
  rw [h7, show 4 * 2 ^ e = (2 : ℕ) ^ (e + 2) by rw [pow_add]; ring,
    show 2 * 2 ^ e = (2 : ℕ) ^ (e + 1) by rw [pow_succ, mul_comm]]

lemma choose_three_seven_two_pow {e : ℕ} (he : 2 ≤ e) :
    Nat.choose (7 * 2 ^ e) 3 =
      2 ^ e * (7 * (7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1) / 3) := by
  have := choose_three_of_two_pow_mul (e := e) (m := 7) he
  simpa [mul_comm 7] using this

lemma a_ne_zero_seven_two_pow_seven : _root_.a (7 * 2 ^ 7) ≠ 0 := by
  refine a_ne_zero_of_witness (7 * 2 ^ 7) 4 (by decide) (by decide) ?_
  have hc : Nat.choose (7 * 2 ^ 7) 4 = 26675267360 := by
    decide
  rw [hc]; decide

lemma a_ne_zero_thirteen_two_pow_six : _root_.a (13 * 2 ^ 6) ≠ 0 := by
  refine a_ne_zero_of_witness (13 * 2 ^ 6) 7 (by decide) (by decide) ?_
  have hc : Nat.choose (13 * 2 ^ 6) 7 = 53387837537601216 := by
    decide
  rw [hc]; decide

lemma seven_shift_mul (e : ℕ) (he : 1 ≤ e) :
    (7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1) =
      49 * 2 ^ (2 * e - 1) - 21 * 2 ^ (e - 1) + 1 := by
  have hle1 : 1 ≤ 7 * 2 ^ e := by
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hle2 : 1 ≤ 7 * 2 ^ (e - 1) := by
    have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
    omega
  have he2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc 2 ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
  have hpow : 2 ^ e * 2 ^ (e - 1) = 2 ^ (2 * e - 1) := by
    rw [← pow_add]; congr 1; omega
  set a := 7 * 2 ^ e
  set b := 7 * 2 ^ (e - 1)
  have ha : 1 ≤ a := hle1
  have hb : 1 ≤ b := hle2
  have hident : (a - 1) * (b - 1) + a + b = a * b + 1 := by
    have ha1 : a - 1 + 1 = a := Nat.sub_add_cancel ha
    have hb1 : b - 1 + 1 = b := Nat.sub_add_cancel hb
    have h1 : (a - 1) * (b - 1) + (b - 1) = a * (b - 1) := by
      calc (a - 1) * (b - 1) + (b - 1)
          = (a - 1) * (b - 1) + 1 * (b - 1) := by rw [one_mul]
        _ = (a - 1 + 1) * (b - 1) := (add_mul _ _ _).symm
        _ = a * (b - 1) := by rw [ha1]
    have h2 : a * (b - 1) + a = a * b := by
      have : a * (b - 1) + a * 1 = a * b := by
        rw [← mul_add, hb1]
      simpa using this
    omega
  have hab : a * b = 49 * 2 ^ (2 * e - 1) := by
    have : a * b = 49 * (2 ^ e * 2 ^ (e - 1)) := by
      unfold a b; ring
    rw [this, hpow]
  have hab2 : a + b = 21 * 2 ^ (e - 1) := by
    have : a = 14 * 2 ^ (e - 1) := by
      unfold a; rw [he2]; ring
    unfold b at *
    omega
  have hle : 21 * 2 ^ (e - 1) ≤ 49 * 2 ^ (2 * e - 1) + 1 := by
    have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
    have : 2 ^ (e - 1) ≤ 2 ^ (2 * e - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega

lemma two_pow_odd_add_seven_div_three {e : ℕ} (he : 1 ≤ e) :
    3 ∣ 2 ^ (2 * e - 1) + 7 := by
  have hodd' : (2 * e - 1) % 2 = 1 := by omega
  have h1 : 3 ∣ 2 ^ (2 * e - 1) + 1 := three_dvd_two_pow_add_one_of_odd hodd'
  have h6 : 3 ∣ 6 := by decide
  have : 2 ^ (2 * e - 1) + 7 = (2 ^ (2 * e - 1) + 1) + 6 := by omega
  rw [this]
  exact Nat.dvd_add h1 h6

lemma seven_P_div_three_eq {e : ℕ} (he : 1 ≤ e) (hodd : e % 2 = 1) :
    7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) / 3 =
      57 * 2 ^ (2 * e) + (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1) := by
  have hP := seven_shift_mul e he
  have hdiv : 3 ∣ 2 ^ (2 * e - 1) + 7 := two_pow_odd_add_seven_div_three he
  have hleZ : 49 * 2 ^ (e - 1) ≤ 57 * 2 ^ (2 * e) + (2 ^ (2 * e - 1) + 7) / 3 := by
    have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
    have : 2 ^ (e - 1) ≤ 2 ^ (2 * e) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hlhs :
      7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) =
        7 * (49 * 2 ^ (2 * e - 1) - 21 * 2 ^ (e - 1) + 1) := by
    rw [hP]
  -- Compare both sides * 3
  have h3R :
      3 * (57 * 2 ^ (2 * e) + (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) =
        3 * (57 * 2 ^ (2 * e)) + (2 ^ (2 * e - 1) + 7) - 3 * (49 * 2 ^ (e - 1)) := by
    have hle : 49 * 2 ^ (e - 1) ≤ 57 * 2 ^ (2 * e) + (2 ^ (2 * e - 1) + 7) / 3 := hleZ
    have hdvd := hdiv
    have : 3 * ((2 ^ (2 * e - 1) + 7) / 3) = 2 ^ (2 * e - 1) + 7 :=
      Nat.mul_div_cancel' hdvd
    omega
  have h3L :
      7 * (49 * 2 ^ (2 * e - 1) - 21 * 2 ^ (e - 1) + 1) =
        343 * 2 ^ (2 * e - 1) - 147 * 2 ^ (e - 1) + 7 := by
    have hle : 21 * 2 ^ (e - 1) ≤ 49 * 2 ^ (2 * e - 1) := by
      have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
      have : 2 ^ (e - 1) ≤ 2 ^ (2 * e - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega
  have hpow : 2 ^ (2 * e) = 2 * 2 ^ (2 * e - 1) := by
    calc 2 ^ (2 * e) = 2 ^ ((2 * e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (2 * e - 1) := two_pow_succ' _
  have heq : 3 * (57 * 2 ^ (2 * e)) + (2 ^ (2 * e - 1) + 7) - 3 * (49 * 2 ^ (e - 1)) =
      343 * 2 ^ (2 * e - 1) - 147 * 2 ^ (e - 1) + 7 := by
    rw [hpow]
    omega
  have hmul : 3 * (57 * 2 ^ (2 * e) + (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) =
      7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) := by
    rw [h3R, heq, hlhs, h3L]
  have hmul' :
      (57 * 2 ^ (2 * e) + (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) * 3 =
        7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) := by
    rw [mul_comm]; exact hmul
  exact (Nat.eq_div_of_mul_eq_left (by decide : (3 : ℕ) ≠ 0) hmul').symm

lemma geom_sum_four (n : ℕ) :
    (∑ i ∈ Finset.range n, (4 : ℕ) ^ i) = (4 ^ n - 1) / 3 := by
  have h3 : 3 ∣ 4 ^ n - 1 := three_dvd_four_pow_sub_one n
  have hsum := Nat.geomSum_eq (m := 4) (by decide : 1 < 4) n
  have : ((4 : ℕ) ^ n - 1) / (4 - 1) = (4 ^ n - 1) / 3 := by simp
  rw [← this, hsum]

lemma sum_two_pow_odd_shift (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 : ℕ) ^ (5 + 2 * k)) = 32 * ((4 ^ n - 1) / 3) := by
  have h : ∀ k ∈ Finset.range n, (2 : ℕ) ^ (5 + 2 * k) = 32 * 4 ^ k := by
    intro k hk
    have : (2 : ℕ) ^ (5 + 2 * k) = 2 ^ 5 * 2 ^ (2 * k) := pow_add _ _ _
    rw [this, show (2 : ℕ) ^ 5 = 32 from rfl, four_pow_eq]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, geom_sum_four]

lemma Z_seven_eq {e : ℕ} (he : 3 ≤ e) :
    (2 ^ (2 * e - 1) + 7) / 3 =
      13 + 32 * ((4 ^ (e - 3) - 1) / 3) := by
  have hdiv4 : 3 ∣ 4 ^ (e - 3) - 1 := three_dvd_four_pow_sub_one (e - 3)
  have hdivZ : 3 ∣ 2 ^ (2 * e - 1) + 7 :=
    two_pow_odd_add_seven_div_three (e := e) (by omega)
  have h3L : 3 * (13 + 32 * ((4 ^ (e - 3) - 1) / 3)) =
      7 + 32 * 4 ^ (e - 3) := by
    have : 3 * ((4 ^ (e - 3) - 1) / 3) = 4 ^ (e - 3) - 1 :=
      Nat.mul_div_cancel' hdiv4
    have hle : 1 ≤ 4 ^ (e - 3) := Nat.one_le_pow _ _ (by decide)
    omega
  have hpow : (32 : ℕ) * 4 ^ (e - 3) = 2 ^ (2 * e - 1) := by
    have : (32 : ℕ) * 4 ^ (e - 3) = 2 ^ 5 * (2 ^ 2) ^ (e - 3) := by
      rw [show (32 : ℕ) = 2 ^ 5 from rfl, show (4 : ℕ) = 2 ^ 2 from rfl]
    rw [this, ← pow_mul, ← pow_add]
    congr 1; omega
  have : 3 * (13 + 32 * ((4 ^ (e - 3) - 1) / 3)) = 2 ^ (2 * e - 1) + 7 := by
    rw [h3L, hpow]; omega
  have hne : (3 : ℕ) ≠ 0 := by decide
  exact (Nat.eq_div_of_mul_eq_left hne (by rw [mul_comm]; exact this)).symm

lemma two_pow_from_pred {e k : ℕ} (he : 1 ≤ e) :
    2 ^ (e + k) = 2 ^ (k + 1) * 2 ^ (e - 1) := by
  have : e + k = (e - 1) + (k + 1) := by omega
  rw [this, pow_add, mul_comm]

lemma two_mul_div_even {n : ℕ} (h : n % 2 = 0) : 2 * (n / 2) = n :=
  Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)

lemma seven_n1_n2 {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    (e - 5) / 2 + (e - 9) / 2 = e - 7 := by
  have he5 : 2 * ((e - 5) / 2) = e - 5 := by
    have : (e - 5) % 2 = 0 := by omega
    exact two_mul_div_even this
  have he9 : 2 * ((e - 9) / 2) = e - 9 := by
    have : (e - 9) % 2 = 0 := by omega
    exact two_mul_div_even this
  omega

lemma seven_split_count {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    (e - 5) / 2 + 4 + (e - 9) / 2 = e - 3 := by
  have := seven_n1_n2 he hodd
  omega

lemma seven_two_n1 {e : ℕ} (he : 5 ≤ e) (hodd : e % 2 = 1) :
    2 * ((e - 5) / 2) = e - 5 := by
  have : (e - 5) % 2 = 0 := by omega
  exact two_mul_div_even this

lemma sum_two_pow_odd_from (start n : ℕ) :
    (∑ k ∈ Finset.range n, (2 : ℕ) ^ (start + 2 * k)) =
      2 ^ start * ((4 ^ n - 1) / 3) := by
  have h : ∀ k ∈ Finset.range n, (2 : ℕ) ^ (start + 2 * k) = 2 ^ start * 4 ^ k := by
    intro k _hk
    rw [pow_add, four_pow_eq]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, geom_sum_four]

lemma popc_seven_L (n1 : ℕ) :
    popc (13 + 32 * ((4 ^ n1 - 1) / 3)) = n1 + 3 := by
  have h : (13 : ℕ) < 2 ^ 5 := by decide
  have h32 : (32 : ℕ) = 2 ^ 5 := rfl
  rw [h32, popc_add_two_pow_mul h, popc_R]
  have : popc 13 = 3 := by decide
  omega

lemma seven_L_mul3 {e : ℕ} (he : 5 ≤ e) (hodd : e % 2 = 1) :
    3 * (13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3)) = 2 ^ e + 7 := by
  set n1 := (e - 5) / 2
  have hdiv : 3 ∣ 4 ^ n1 - 1 := three_dvd_four_pow_sub_one n1
  have hmul : 3 * ((4 ^ n1 - 1) / 3) = 4 ^ n1 - 1 := Nat.mul_div_cancel' hdiv
  have hle : 1 ≤ 4 ^ n1 := Nat.one_le_pow _ _ (by decide)
  have hpow : (32 : ℕ) * 4 ^ n1 = 2 ^ e := by
    have : (32 : ℕ) * 4 ^ n1 = 2 ^ 5 * (2 ^ 2) ^ n1 := by
      rw [show (32 : ℕ) = 2 ^ 5 from rfl, show (4 : ℕ) = 2 ^ 2 from rfl]
    rw [this, ← pow_mul, ← pow_add]
    have : 5 + 2 * n1 = e := by
      have hn : 2 * n1 = e - 5 := seven_two_n1 he hodd
      omega
    rw [this]
  omega

lemma seven_L_lt {e : ℕ} (he : 5 ≤ e) (hodd : e % 2 = 1) :
    13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3) < 2 ^ (e - 1) := by
  have h3 := seven_L_mul3 he hodd
  have hgoal : 2 ^ e + 7 < 3 * 2 ^ (e - 1) := by
    have hpow : 2 ^ e = 2 * 2 ^ (e - 1) := by
      calc 2 ^ e = 2 ^ ((e - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
    rw [hpow]
    have : 7 < 2 ^ (e - 1) := by
      have : 2 ^ 3 ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : ℕ) ^ 3 = 8 := rfl
      omega
    omega
  have : 3 * (13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3)) < 3 * 2 ^ (e - 1) := by
    rwa [h3]
  exact Nat.lt_of_mul_lt_mul_left this

lemma fortynine_shift {e : ℕ} (he : 1 ≤ e) :
    (49 : ℕ) * 2 ^ (e - 1) = 2 ^ (e - 1) + 2 ^ (e + 3) + 2 ^ (e + 4) := by
  have h16 : (16 : ℕ) * 2 ^ (e - 1) = 2 ^ (e + 3) := by
    have : e + 3 = (e - 1) + 4 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 4 = 16 from rfl, mul_comm]
  have h32 : (32 : ℕ) * 2 ^ (e - 1) = 2 ^ (e + 4) := by
    have : e + 4 = (e - 1) + 5 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 5 = 32 from rfl, mul_comm]
  have : (49 : ℕ) = 1 + 16 + 32 := rfl
  rw [this, add_mul, add_mul, one_mul, h16, h32]

lemma fifteen_shift (e : ℕ) :
    (15 : ℕ) * 2 ^ (e + 2) = 2 ^ (e + 2) + 2 ^ (e + 3) + 2 ^ (e + 4) + 2 ^ (e + 5) := by
  have : (15 : ℕ) = 1 + 2 + 4 + 8 := rfl
  rw [this, add_mul, add_mul, add_mul, one_mul]
  have h2 : 2 * 2 ^ (e + 2) = 2 ^ (e + 3) := by
    rw [← two_pow_succ']
  have h4 : 4 * 2 ^ (e + 2) = 2 ^ (e + 4) := by
    have : (4 : ℕ) = 2 ^ 2 := rfl
    rw [this, ← pow_add]
    congr 1; omega
  have h8 : 8 * 2 ^ (e + 2) = 2 ^ (e + 5) := by
    have : (8 : ℕ) = 2 ^ 3 := rfl
    rw [this, ← pow_add]
    congr 1; omega
  rw [h2, h4, h8]

lemma seven_mid_mul {e : ℕ} (he : 1 ≤ e) :
    2 ^ e + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) = 170 * 2 ^ (e - 1) := by
  have he0 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc 2 ^ e = 2 ^ ((e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
  rw [he0, two_pow_from_pred (k := 2) he, two_pow_from_pred (k := 4) he,
    two_pow_from_pred (k := 6) he]
  simp [pow_succ, pow_zero]
  omega

lemma seven_rhs_mul {e : ℕ} (he : 1 ≤ e) :
    2 ^ (e - 1) + 15 * 2 ^ (e + 2) = 121 * 2 ^ (e - 1) := by
  have : 2 ^ (e + 2) = 8 * 2 ^ (e - 1) := two_pow_from_pred (k := 2) he
  rw [this]
  omega

lemma seven_mid_sub {e : ℕ} (he : 1 ≤ e) :
    2 ^ e + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) - 49 * 2 ^ (e - 1) =
      2 ^ (e - 1) + 15 * 2 ^ (e + 2) := by
  have hmid := seven_mid_mul he
  have hrhs := seven_rhs_mul he
  rw [hmid, hrhs]
  omega

lemma sum_range_four (f : ℕ → ℕ) :
    (∑ k ∈ Finset.range 4, f k) = f 0 + f 1 + f 2 + f 3 := by
  simp [Finset.sum_range_succ]

lemma seven_odds_split {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    (∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k)) =
      (∑ k ∈ Finset.range ((e - 5) / 2), (2 : ℕ) ^ (5 + 2 * k)) +
        (2 ^ e + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6)) +
        (∑ k ∈ Finset.range ((e - 9) / 2), (2 : ℕ) ^ (e + 8 + 2 * k)) := by
  set n1 := (e - 5) / 2
  set n2 := (e - 9) / 2
  have hsplit1 :
      (∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k)) =
        (∑ k ∈ Finset.range n1, (2 : ℕ) ^ (5 + 2 * k)) +
          ∑ k ∈ Finset.range (4 + n2), (2 : ℕ) ^ (5 + 2 * (n1 + k)) := by
    have : e - 3 = n1 + (4 + n2) := by
      have := seven_split_count he hodd
      omega
    rw [this, Finset.sum_range_add]
  rw [hsplit1]
  have hsplit2 :
      (∑ k ∈ Finset.range (4 + n2), (2 : ℕ) ^ (5 + 2 * (n1 + k))) =
        (∑ k ∈ Finset.range 4, (2 : ℕ) ^ (5 + 2 * (n1 + k))) +
          ∑ k ∈ Finset.range n2, (2 : ℕ) ^ (5 + 2 * (n1 + (4 + k))) :=
    Finset.sum_range_add (fun k => (2 : ℕ) ^ (5 + 2 * (n1 + k))) 4 n2
  have hsplit2' :
      (∑ k ∈ Finset.range n2, (2 : ℕ) ^ (5 + 2 * (n1 + (4 + k)))) =
        ∑ k ∈ Finset.range n2, (2 : ℕ) ^ (5 + 2 * (n1 + 4 + k)) := by
    apply Finset.sum_congr rfl
    intro k _hk
    congr 1
    omega
  rw [hsplit2, hsplit2']
  have hmid :
      (∑ k ∈ Finset.range 4, (2 : ℕ) ^ (5 + 2 * (n1 + k))) =
        2 ^ e + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) := by
    rw [sum_range_four]
    have hn1 : 2 * n1 = e - 5 := seven_two_n1 (by omega) hodd
    have h0 : 5 + 2 * (n1 + 0) = e := by omega
    have h1 : 5 + 2 * (n1 + 1) = e + 2 := by omega
    have h2 : 5 + 2 * (n1 + 2) = e + 4 := by omega
    have h3 : 5 + 2 * (n1 + 3) = e + 6 := by omega
    rw [h0, h1, h2, h3]
  have hhigh :
      (∑ k ∈ Finset.range n2, (2 : ℕ) ^ (5 + 2 * (n1 + 4 + k))) =
        ∑ k ∈ Finset.range n2, (2 : ℕ) ^ (e + 8 + 2 * k) := by
    apply Finset.sum_congr rfl
    intro k _hk
    have hn1 : 2 * n1 = e - 5 := seven_two_n1 (by omega) hodd
    congr 1
    omega
  rw [hmid, hhigh, ← add_assoc]

lemma Z_seven_as_parts {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    (2 ^ (2 * e - 1) + 7) / 3 =
      13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3) +
        (2 ^ e + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6)) +
        2 ^ (e + 8) * ((4 ^ ((e - 9) / 2) - 1) / 3) := by
  have he3 : 3 ≤ e := by omega
  rw [Z_seven_eq he3]
  have hsum : 32 * ((4 ^ (e - 3) - 1) / 3) =
      ∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k) :=
    (sum_two_pow_odd_shift (e - 3)).symm
  rw [hsum, seven_odds_split he hodd, sum_two_pow_odd_shift,
    sum_two_pow_odd_from (e + 8)]
  ac_rfl

lemma seven_D_eq {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1) =
      13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3) +
        2 ^ (e - 1) + 15 * 2 ^ (e + 2) +
        2 ^ (e + 8) * ((4 ^ ((e - 9) / 2) - 1) / 3) := by
  have hZ := Z_seven_as_parts he hodd
  have hmid := seven_mid_sub (by omega : 1 ≤ e)
  set A := 13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3)
  set M := 2 ^ e + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6)
  set C := 2 ^ (e + 8) * ((4 ^ ((e - 9) / 2) - 1) / 3)
  have hform : (2 ^ (2 * e - 1) + 7) / 3 = A + M + C := hZ
  have hle : 49 * 2 ^ (e - 1) ≤ M := by
    have := seven_mid_mul (by omega : 1 ≤ e)
    have : 49 * 2 ^ (e - 1) ≤ 170 * 2 ^ (e - 1) :=
      Nat.mul_le_mul_right _ (by decide)
    omega
  rw [hform]
  have hsub : A + M + C - 49 * 2 ^ (e - 1) = A + (M - 49 * 2 ^ (e - 1)) + C := by
    have hleC : 49 * 2 ^ (e - 1) ≤ M + C := hle.trans (Nat.le_add_right _ _)
    calc A + M + C - 49 * 2 ^ (e - 1)
        = A + (M + C) - 49 * 2 ^ (e - 1) := by rw [add_assoc]
      _ = A + (M + C - 49 * 2 ^ (e - 1)) := Nat.add_sub_assoc hleC A
      _ = A + (C + M - 49 * 2 ^ (e - 1)) := by rw [add_comm M]
      _ = A + (C + (M - 49 * 2 ^ (e - 1))) := by rw [Nat.add_sub_assoc hle C]
      _ = A + (M - 49 * 2 ^ (e - 1)) + C := by rw [add_comm C, ← add_assoc]
  rw [hsub, hmid]
  ac_rfl

lemma fortynine_le_Z {e : ℕ} (he : 8 ≤ e) :
    49 * 2 ^ (e - 1) ≤ (2 ^ (2 * e - 1) + 7) / 3 := by
  have hdiv : 3 ∣ 2 ^ (2 * e - 1) + 7 :=
    two_pow_odd_add_seven_div_three (by omega)
  have h3 : 3 * ((2 ^ (2 * e - 1) + 7) / 3) = 2 ^ (2 * e - 1) + 7 :=
    Nat.mul_div_cancel' hdiv
  have hgoal : 3 * (49 * 2 ^ (e - 1)) ≤ 2 ^ (2 * e - 1) + 7 := by
    have : (3 : ℕ) * 49 = 147 := rfl
    rw [← mul_assoc, this]
    have hpow : 2 ^ (2 * e - 1) = 2 ^ e * 2 ^ (e - 1) := by
      rw [← pow_add]; congr 1; omega
    have h147 : 147 ≤ 2 ^ e := by
      have : 2 ^ 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
      have : (2 : ℕ) ^ 8 = 256 := rfl
      omega
    have : 147 * 2 ^ (e - 1) ≤ 2 ^ e * 2 ^ (e - 1) :=
      Nat.mul_le_mul_right _ h147
    omega
  have : 3 * (49 * 2 ^ (e - 1)) ≤ 3 * ((2 ^ (2 * e - 1) + 7) / 3) := by
    rwa [h3]
  exact Nat.le_of_mul_le_mul_left this (by decide)

lemma popc_seven_D {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    popc ((2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) = e + 1 := by
  rw [seven_D_eq he hodd]
  set L := 13 + 32 * ((4 ^ ((e - 5) / 2) - 1) / 3)
  set H := (4 ^ ((e - 9) / 2) - 1) / 3
  have hLlt : L < 2 ^ (e - 1) := seven_L_lt (by omega) hodd
  have hpow_e : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc 2 ^ e = 2 ^ ((e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
  have hL1 : L + 2 ^ (e - 1) < 2 ^ e := by omega
  have hpop1 : popc (L + 2 ^ (e - 1)) = popc L + 1 := by
    have h := popc_add_two_pow_mul (a := 1) (b := L) (i := e - 1) hLlt
    simpa [popc_one, add_comm] using h
  have hL1lt : L + 2 ^ (e - 1) < 2 ^ (e + 2) := by
    have : 2 ^ e ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpop2 : popc (L + 2 ^ (e - 1) + 15 * 2 ^ (e + 2)) =
      popc 15 + popc (L + 2 ^ (e - 1)) := by
    have hform : L + 2 ^ (e - 1) + 15 * 2 ^ (e + 2) =
        L + 2 ^ (e - 1) + 2 ^ (e + 2) * 15 := by ring
    rw [hform]
    exact popc_add_two_pow_mul hL1lt
  have hlowlt : L + 2 ^ (e - 1) + 15 * 2 ^ (e + 2) < 2 ^ (e + 8) := by
    have h15 : 15 * 2 ^ (e + 2) = 60 * 2 ^ e := by
      have : 2 ^ (e + 2) = 4 * 2 ^ e := by
        rw [pow_add, pow_two]; ring
      rw [this]; ring
    have : L + 2 ^ (e - 1) + 15 * 2 ^ (e + 2) < 2 ^ e + 60 * 2 ^ e := by omega
    have : (2 : ℕ) ^ e + 60 * 2 ^ e = 61 * 2 ^ e := by ring
    have hpos : 0 < 2 ^ e := Nat.pow_pos (by decide)
    have h61 : 61 * 2 ^ e < 256 * 2 ^ e :=
      Nat.mul_lt_mul_of_pos_right (by decide) hpos
    have h256 : (256 : ℕ) * 2 ^ e = 2 ^ (e + 8) := by
      rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add, add_comm]
    omega
  have hpop3 : popc (L + 2 ^ (e - 1) + 15 * 2 ^ (e + 2) + 2 ^ (e + 8) * H) =
      popc H + popc (L + 2 ^ (e - 1) + 15 * 2 ^ (e + 2)) :=
    popc_add_two_pow_mul hlowlt
  have hpopL : popc L = (e - 5) / 2 + 3 := popc_seven_L _
  have hpopH : popc H = (e - 9) / 2 := popc_R _
  have hpop15 : popc 15 = 4 := by decide
  have hsum := seven_n1_n2 he hodd
  omega

lemma seven_P_as_D {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) / 3 =
      57 * 2 ^ (2 * e) + ((2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) := by
  rw [seven_P_div_three_eq (by omega) hodd]
  have hle := fortynine_le_Z (by omega : 8 ≤ e)
  exact Nat.add_sub_assoc hle _

lemma D_lt_two_pow_two_e {e : ℕ} (he : 9 ≤ e) :
    (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1) < 2 ^ (2 * e) := by
  have hle := fortynine_le_Z (by omega : 8 ≤ e)
  have hZle : (2 ^ (2 * e - 1) + 7) / 3 ≤ 2 ^ (2 * e - 1) + 7 :=
    Nat.div_le_self _ _
  have hZlt : 2 ^ (2 * e - 1) + 7 < 2 ^ (2 * e) := by
    have hpow : 2 ^ (2 * e) = 2 * 2 ^ (2 * e - 1) := by
      calc 2 ^ (2 * e) = 2 ^ ((2 * e - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (2 * e - 1) := two_pow_succ' _
    have : 7 < 2 ^ (2 * e - 1) := by
      have : 2 ^ 3 ≤ 2 ^ (2 * e - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : ℕ) ^ 3 = 8 := rfl
      omega
    omega
  have : (2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)
      ≤ (2 ^ (2 * e - 1) + 7) / 3 := Nat.sub_le _ _
  omega

lemma popc_seven_P_div {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    popc (7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) / 3) = e + 5 := by
  rw [seven_P_as_D he hodd]
  have hlt := D_lt_two_pow_two_e he
  have : 57 * 2 ^ (2 * e) + ((2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) =
      ((2 ^ (2 * e - 1) + 7) / 3 - 49 * 2 ^ (e - 1)) + 2 ^ (2 * e) * 57 := by
    ring
  rw [this, popc_add_two_pow_mul hlt, popc_seven_D he hodd]
  have : popc 57 = 4 := by decide
  omega

lemma popc_choose_three_seven_two_pow {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    popc (Nat.choose (7 * 2 ^ e) 3) = e + 5 := by
  rw [choose_three_seven_two_pow (by omega), popc_mul_two_pow]
  have hassoc :
      7 * (7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1) =
        7 * ((7 * 2 ^ e - 1) * (7 * 2 ^ (e - 1) - 1)) := by
    ring
  rw [hassoc]
  exact popc_seven_P_div he hodd

lemma a_ne_zero_seven_two_pow {e : ℕ} (he : 9 ≤ e) (hodd : e % 2 = 1) :
    _root_.a (7 * 2 ^ e) ≠ 0 := by
  refine a_ne_zero_of_witness (7 * 2 ^ e) 3 (by decide) ?_ ?_
  · have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  · have hpop := popc_choose_three_seven_two_pow he hodd
    omega

lemma thirteen_shift_mul (e : ℕ) (he : 1 ≤ e) :
    (13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1) =
      169 * 2 ^ (2 * e - 1) - 39 * 2 ^ (e - 1) + 1 := by
  have hle1 : 1 ≤ 13 * 2 ^ e := by
    have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  have hle2 : 1 ≤ 13 * 2 ^ (e - 1) := by
    have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
    omega
  have he2 : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc 2 ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (e - 1) := two_pow_succ' _
  have hpow : 2 ^ e * 2 ^ (e - 1) = 2 ^ (2 * e - 1) := by
    rw [← pow_add]; congr 1; omega
  set a := 13 * 2 ^ e
  set b := 13 * 2 ^ (e - 1)
  have ha : 1 ≤ a := hle1
  have hb : 1 ≤ b := hle2
  have hident : (a - 1) * (b - 1) + a + b = a * b + 1 := by
    have ha1 : a - 1 + 1 = a := Nat.sub_add_cancel ha
    have hb1 : b - 1 + 1 = b := Nat.sub_add_cancel hb
    have h1 : (a - 1) * (b - 1) + (b - 1) = a * (b - 1) := by
      calc (a - 1) * (b - 1) + (b - 1)
          = (a - 1) * (b - 1) + 1 * (b - 1) := by rw [one_mul]
        _ = (a - 1 + 1) * (b - 1) := (add_mul _ _ _).symm
        _ = a * (b - 1) := by rw [ha1]
    have h2 : a * (b - 1) + a = a * b := by
      have : a * (b - 1) + a * 1 = a * b := by
        rw [← mul_add, hb1]
      simpa using this
    omega
  have hab : a * b = 169 * 2 ^ (2 * e - 1) := by
    have : a * b = 169 * (2 ^ e * 2 ^ (e - 1)) := by
      unfold a b; ring
    rw [this, hpow]
  have hab2 : a + b = 39 * 2 ^ (e - 1) := by
    have : a = 26 * 2 ^ (e - 1) := by
      unfold a; rw [he2]; ring
    unfold b at *
    omega
  have hle : 39 * 2 ^ (e - 1) ≤ 169 * 2 ^ (2 * e - 1) + 1 := by
    have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
    have : 2 ^ (e - 1) ≤ 2 ^ (2 * e - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  omega

lemma choose_three_thirteen_two_pow {e : ℕ} (he : 2 ≤ e) :
    Nat.choose (13 * 2 ^ e) 3 =
      2 ^ e * (13 * (13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1) / 3) := by
  have := choose_three_of_two_pow_mul (e := e) (m := 13) he
  simpa [mul_comm 13] using this

lemma thirteen_Z_mul {e : ℕ} (he : 3 ≤ e) :
    13 * ((2 ^ (2 * e - 1) + 1) / 3) =
      2 ^ (2 * e + 1) + 15 + 32 * ((4 ^ (e - 3) - 1) / 3) := by
  have hdiv : 3 ∣ 2 ^ (2 * e - 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have hdiv4 : 3 ∣ 4 ^ (e - 3) - 1 := three_dvd_four_pow_sub_one (e - 3)
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * (13 * ((2 ^ (2 * e - 1) + 1) / 3)) =
      13 * (2 ^ (2 * e - 1) + 1) := by
    have : 3 * ((2 ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
      Nat.mul_div_cancel' hdiv
    omega
  have hle4 : 1 ≤ 4 ^ (e - 3) := Nat.one_le_pow _ _ (by decide)
  have rhs : 3 * (2 ^ (2 * e + 1) + 15 + 32 * ((4 ^ (e - 3) - 1) / 3)) =
      3 * 2 ^ (2 * e + 1) + 45 + 32 * (4 ^ (e - 3) - 1) := by
    have : 3 * ((4 ^ (e - 3) - 1) / 3) = 4 ^ (e - 3) - 1 :=
      Nat.mul_div_cancel' hdiv4
    omega
  have hpow32 : (32 : ℕ) * 4 ^ (e - 3) = 2 ^ (2 * e - 1) := by
    have : (32 : ℕ) * 4 ^ (e - 3) = 2 ^ 5 * (2 ^ 2) ^ (e - 3) := by
      rw [show (32 : ℕ) = 2 ^ 5 from rfl, show (4 : ℕ) = 2 ^ 2 from rfl]
    rw [this, ← pow_mul, ← pow_add]
    congr 1; omega
  have h2e1 : 2 ^ (2 * e + 1) = 2 * 2 ^ (2 * e) := two_pow_succ' _
  have h2e : 2 ^ (2 * e) = 2 * 2 ^ (2 * e - 1) := by
    calc 2 ^ (2 * e) = 2 ^ ((2 * e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (2 * e - 1) := two_pow_succ' _
  rw [lhs, rhs]
  have : 3 * 2 ^ (2 * e + 1) + 45 + 32 * (4 ^ (e - 3) - 1) =
      3 * 2 ^ (2 * e + 1) + 13 + 32 * 4 ^ (e - 3) := by omega
  rw [this, hpow32, h2e1, h2e]
  omega

lemma one_six_nine_shift {e : ℕ} (he : 1 ≤ e) :
    (169 : ℕ) * 2 ^ (e - 1) = 2 ^ (e - 1) + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) := by
  have h8 : (8 : ℕ) * 2 ^ (e - 1) = 2 ^ (e + 2) := by
    have : e + 2 = (e - 1) + 3 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 3 = 8 from rfl, mul_comm]
  have h32 : (32 : ℕ) * 2 ^ (e - 1) = 2 ^ (e + 4) := by
    have : e + 4 = (e - 1) + 5 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 5 = 32 from rfl, mul_comm]
  have h128 : (128 : ℕ) * 2 ^ (e - 1) = 2 ^ (e + 6) := by
    have : e + 6 = (e - 1) + 7 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 7 = 128 from rfl, mul_comm]
  have : (169 : ℕ) = 1 + 8 + 32 + 128 := rfl
  rw [this, add_mul, add_mul, add_mul, one_mul, h8, h32, h128]

lemma thirteen_two_nlow {e : ℕ} (he : 6 ≤ e) (heven : e % 2 = 0) :
    2 * ((e - 6) / 2) = e - 6 := by
  have : (e - 6) % 2 = 0 := by omega
  exact two_mul_div_even this

lemma thirteen_two_nhigh {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    2 * ((e - 10) / 2) = e - 10 := by
  have : (e - 10) % 2 = 0 := by omega
  exact two_mul_div_even this

lemma thirteen_nlow_nhigh {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    (e - 6) / 2 + (e - 10) / 2 = e - 8 := by
  have h1 := thirteen_two_nlow (by omega) heven
  have h2 := thirteen_two_nhigh he heven
  omega

lemma thirteen_split_count {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    (e - 6) / 2 + 5 + (e - 10) / 2 = e - 3 := by
  have := thirteen_nlow_nhigh he heven
  omega

lemma popc_thirteen_L (nlow : ℕ) :
    popc (15 + 32 * ((4 ^ nlow - 1) / 3)) = nlow + 4 := by
  have h : (15 : ℕ) < 2 ^ 5 := by decide
  have h32 : (32 : ℕ) = 2 ^ 5 := rfl
  rw [h32, popc_add_two_pow_mul h, popc_R]
  have : popc 15 = 4 := by decide
  omega

lemma thirteen_L_mul3 {e : ℕ} (he : 6 ≤ e) (heven : e % 2 = 0) :
    3 * (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3)) = 2 ^ (e - 1) + 13 := by
  set nlow := (e - 6) / 2
  have hdiv : 3 ∣ 4 ^ nlow - 1 := three_dvd_four_pow_sub_one nlow
  have hmul : 3 * ((4 ^ nlow - 1) / 3) = 4 ^ nlow - 1 := Nat.mul_div_cancel' hdiv
  have hle : 1 ≤ 4 ^ nlow := Nat.one_le_pow _ _ (by decide)
  have hpow : (32 : ℕ) * 4 ^ nlow = 2 ^ (e - 1) := by
    have : (32 : ℕ) * 4 ^ nlow = 2 ^ 5 * (2 ^ 2) ^ nlow := by
      rw [show (32 : ℕ) = 2 ^ 5 from rfl, show (4 : ℕ) = 2 ^ 2 from rfl]
    rw [this, ← pow_mul, ← pow_add]
    have : 5 + 2 * nlow = e - 1 := by
      have hn : 2 * nlow = e - 6 := thirteen_two_nlow he heven
      omega
    rw [this]
  omega

lemma thirteen_L_lt {e : ℕ} (he : 6 ≤ e) (heven : e % 2 = 0) :
    15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) < 2 ^ (e - 1) := by
  have h3 := thirteen_L_mul3 he heven
  have hgoal : 2 ^ (e - 1) + 13 < 3 * 2 ^ (e - 1) := by
    have : 13 < 2 * 2 ^ (e - 1) := by
      have : 2 ^ 4 ≤ 2 ^ (e - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : ℕ) ^ 4 = 16 := rfl
      omega
    omega
  have : 3 * (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3)) < 3 * 2 ^ (e - 1) := by
    rwa [h3]
  exact Nat.lt_of_mul_lt_mul_left this

lemma thirteen_mid_odds_mul {e : ℕ} (he : 1 ≤ e) :
    2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7) = 85 * 2 ^ (e + 1) := by
  have h3 : 2 ^ (e + 3) = 4 * 2 ^ (e + 1) := by
    have : e + 3 = (e + 1) + 2 := by omega
    rw [this, pow_add, pow_two]; ring
  have h5 : 2 ^ (e + 5) = 16 * 2 ^ (e + 1) := by
    have : e + 5 = (e + 1) + 4 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 4 = 16 from rfl]; ring
  have h7 : 2 ^ (e + 7) = 64 * 2 ^ (e + 1) := by
    have : e + 7 = (e + 1) + 6 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 6 = 64 from rfl]; ring
  rw [h3, h5, h7]
  omega

lemma thirteen_mid_new_mul (e : ℕ) :
    (43 : ℕ) * 2 ^ (e + 1) = 2 ^ (e + 1) + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) := by
  have : (43 : ℕ) = 1 + 2 + 8 + 32 := rfl
  rw [this, add_mul, add_mul, add_mul, one_mul]
  have h2 : 2 * 2 ^ (e + 1) = 2 ^ (e + 2) := by rw [← two_pow_succ']
  have h8 : 8 * 2 ^ (e + 1) = 2 ^ (e + 4) := by
    have : (8 : ℕ) = 2 ^ 3 := rfl
    rw [this, ← pow_add]; congr 1; omega
  have h32 : 32 * 2 ^ (e + 1) = 2 ^ (e + 6) := by
    have : (32 : ℕ) = 2 ^ 5 := rfl
    rw [this, ← pow_add]; congr 1; omega
  rw [h2, h8, h32]

lemma thirteen_mid_sub {e : ℕ} (he : 1 ≤ e) :
    2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7)
      - (2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6)) =
      43 * 2 ^ (e + 1) := by
  have hmid := thirteen_mid_odds_mul he
  have hrhs := thirteen_mid_new_mul e
  have hsub : 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) = 42 * 2 ^ (e + 1) := by
    have h2 : 2 ^ (e + 2) = 2 * 2 ^ (e + 1) := by rw [← two_pow_succ']
    have h4 : 2 ^ (e + 4) = 8 * 2 ^ (e + 1) := by
      have : e + 4 = (e + 1) + 3 := by omega
      rw [this, pow_add, show (2 : ℕ) ^ 3 = 8 from rfl]; ring
    have h6 : 2 ^ (e + 6) = 32 * 2 ^ (e + 1) := by
      have : e + 6 = (e + 1) + 5 := by omega
      rw [this, pow_add, show (2 : ℕ) ^ 5 = 32 from rfl]; ring
    rw [h2, h4, h6]; omega
  rw [hmid, hsub, hrhs]
  omega

lemma thirteen_odds_split {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    (∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k)) =
      (∑ k ∈ Finset.range ((e - 6) / 2), (2 : ℕ) ^ (5 + 2 * k)) +
        2 ^ (e - 1) +
        (2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7)) +
        (∑ k ∈ Finset.range ((e - 10) / 2), (2 : ℕ) ^ (e + 9 + 2 * k)) := by
  set nlow := (e - 6) / 2
  set nhigh := (e - 10) / 2
  have hsplit1 :
      (∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k)) =
        (∑ k ∈ Finset.range nlow, (2 : ℕ) ^ (5 + 2 * k)) +
          ∑ k ∈ Finset.range (5 + nhigh), (2 : ℕ) ^ (5 + 2 * (nlow + k)) := by
    have : e - 3 = nlow + (5 + nhigh) := by
      have := thirteen_split_count he heven
      omega
    rw [this, Finset.sum_range_add]
  rw [hsplit1]
  have hsplit2 :
      (∑ k ∈ Finset.range (5 + nhigh), (2 : ℕ) ^ (5 + 2 * (nlow + k))) =
        (∑ k ∈ Finset.range 1, (2 : ℕ) ^ (5 + 2 * (nlow + k))) +
          ∑ k ∈ Finset.range (4 + nhigh), (2 : ℕ) ^ (5 + 2 * (nlow + (1 + k))) := by
    have : 5 + nhigh = 1 + (4 + nhigh) := by omega
    rw [this]
    exact Finset.sum_range_add (fun k => (2 : ℕ) ^ (5 + 2 * (nlow + k))) 1 (4 + nhigh)
  have hsplit3 :
      (∑ k ∈ Finset.range (4 + nhigh), (2 : ℕ) ^ (5 + 2 * (nlow + (1 + k)))) =
        (∑ k ∈ Finset.range 4, (2 : ℕ) ^ (5 + 2 * (nlow + (1 + k)))) +
          ∑ k ∈ Finset.range nhigh, (2 : ℕ) ^ (5 + 2 * (nlow + (1 + (4 + k)))) :=
    Finset.sum_range_add (fun k => (2 : ℕ) ^ (5 + 2 * (nlow + (1 + k)))) 4 nhigh
  have hone :
      (∑ k ∈ Finset.range 1, (2 : ℕ) ^ (5 + 2 * (nlow + k))) = 2 ^ (e - 1) := by
    rw [Finset.sum_range_one]
    have hn : 2 * nlow = e - 6 := thirteen_two_nlow (by omega) heven
    congr 1; omega
  have hmid :
      (∑ k ∈ Finset.range 4, (2 : ℕ) ^ (5 + 2 * (nlow + (1 + k)))) =
        2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7) := by
    rw [sum_range_four]
    have hn : 2 * nlow = e - 6 := thirteen_two_nlow (by omega) heven
    have h0 : 5 + 2 * (nlow + (1 + 0)) = e + 1 := by omega
    have h1 : 5 + 2 * (nlow + (1 + 1)) = e + 3 := by omega
    have h2 : 5 + 2 * (nlow + (1 + 2)) = e + 5 := by omega
    have h3 : 5 + 2 * (nlow + (1 + 3)) = e + 7 := by omega
    rw [h0, h1, h2, h3]
  have hhigh :
      (∑ k ∈ Finset.range nhigh, (2 : ℕ) ^ (5 + 2 * (nlow + (1 + (4 + k))))) =
        ∑ k ∈ Finset.range nhigh, (2 : ℕ) ^ (e + 9 + 2 * k) := by
    apply Finset.sum_congr rfl
    intro k _hk
    have hn : 2 * nlow = e - 6 := thirteen_two_nlow (by omega) heven
    congr 1; omega
  rw [hsplit2, hsplit3, hone, hmid, hhigh]
  ac_rfl

lemma thirteen_S_eq (e : ℕ) :
    2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) = 42 * 2 ^ (e + 1) := by
  have h2 : 2 ^ (e + 2) = 2 * 2 ^ (e + 1) := by rw [← two_pow_succ']
  have h4 : 2 ^ (e + 4) = 8 * 2 ^ (e + 1) := by
    have : e + 4 = (e + 1) + 3 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 3 = 8 from rfl]; ring
  have h6 : 2 ^ (e + 6) = 32 * 2 ^ (e + 1) := by
    have : e + 6 = (e + 1) + 5 := by omega
    rw [this, pow_add, show (2 : ℕ) ^ 5 = 32 from rfl]; ring
  rw [h2, h4, h6]; omega

lemma thirteen_D_core {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    15 + 32 * ((4 ^ (e - 3) - 1) / 3) - 169 * 2 ^ (e - 1) =
      15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
        43 * 2 ^ (e + 1) +
        2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3) := by
  have hsum : 32 * ((4 ^ (e - 3) - 1) / 3) =
      ∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k) :=
    (sum_two_pow_odd_shift (e - 3)).symm
  rw [hsum, thirteen_odds_split he heven]
  set L := ∑ k ∈ Finset.range ((e - 6) / 2), (2 : ℕ) ^ (5 + 2 * k)
  set M := 2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7)
  set S := 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6)
  set C := ∑ k ∈ Finset.range ((e - 10) / 2), (2 : ℕ) ^ (e + 9 + 2 * k)
  have h169 : 169 * 2 ^ (e - 1) =
      2 ^ (e - 1) + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) :=
    one_six_nine_shift (by omega : 1 ≤ e)
  have hleS : 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) ≤
      2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7) := by
    have hm := thirteen_mid_odds_mul (by omega : 1 ≤ e)
    have hs := thirteen_S_eq e
    have : 42 * 2 ^ (e + 1) ≤ 85 * 2 ^ (e + 1) :=
      Nat.mul_le_mul_right _ (by decide)
    omega
  have hLHS :
      15 + L + 2 ^ (e - 1) + M + C - 169 * 2 ^ (e - 1) =
        15 + L + (M - S) + C := by
    unfold S
    rw [h169]
    have hA : 15 + L + 2 ^ (e - 1) + M + C =
        2 ^ (e - 1) + (15 + L + M + C) := by ac_rfl
    have hS : 2 ^ (e - 1) + 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) =
        2 ^ (e - 1) + (2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6)) := by ac_rfl
    rw [hA, hS, Nat.add_sub_add_left (2 ^ (e - 1)) (15 + L + M + C)
      (2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6))]
    have hB : 15 + L + M + C = (15 + L + C) + M := by ac_rfl
    rw [hB, Nat.add_sub_assoc hleS]
    unfold M
    ac_rfl
  have hassoc : 15 + L + 2 ^ (e - 1) + M + C =
      15 + (L + 2 ^ (e - 1) + M + C) := by ac_rfl
  have hLsum : L = 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) :=
    sum_two_pow_odd_shift _
  have hCsum : C = 2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3) :=
    sum_two_pow_odd_from (e + 9) _
  rw [← hassoc, hLHS, thirteen_mid_sub (by omega : 1 ≤ e), hLsum, hCsum]

lemma one_six_nine_le_thirteen_Z {e : ℕ} (he : 8 ≤ e) :
    169 * 2 ^ (e - 1) ≤ 13 * ((2 ^ (2 * e - 1) + 1) / 3) := by
  have hdiv : 3 ∣ 2 ^ (2 * e - 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have h3 : 3 * ((2 ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have hgoal : 3 * (169 * 2 ^ (e - 1)) ≤ 13 * (2 ^ (2 * e - 1) + 1) := by
    have : (3 : ℕ) * 169 = 507 := rfl
    rw [← mul_assoc, this]
    have hpow : 2 ^ (2 * e - 1) = 2 ^ e * 2 ^ (e - 1) := by
      rw [← pow_add]; congr 1; omega
    have h507 : 507 ≤ 13 * 2 ^ e := by
      have : 2 ^ 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
      have : (2 : ℕ) ^ 8 = 256 := rfl
      omega
    have hmul : 507 * 2 ^ (e - 1) ≤ 13 * 2 ^ e * 2 ^ (e - 1) :=
      Nat.mul_le_mul_right _ h507
    have hassoc : 13 * 2 ^ e * 2 ^ (e - 1) = 13 * 2 ^ (2 * e - 1) := by
      rw [mul_assoc, hpow]
    have hle' : 13 * 2 ^ (2 * e - 1) ≤ 13 * 2 ^ (2 * e - 1) + 13 :=
      Nat.le_add_right _ _
    have hr : 13 * (2 ^ (2 * e - 1) + 1) = 13 * 2 ^ (2 * e - 1) + 13 := by ring
    rw [hr]
    exact hmul.trans (hassoc.le.trans hle')
  have : 3 * (169 * 2 ^ (e - 1)) ≤ 3 * (13 * ((2 ^ (2 * e - 1) + 1) / 3)) := by
    have hmul : 3 * (13 * ((2 ^ (2 * e - 1) + 1) / 3)) =
        13 * (2 ^ (2 * e - 1) + 1) := by
      calc 3 * (13 * ((2 ^ (2 * e - 1) + 1) / 3))
          = 13 * (3 * ((2 ^ (2 * e - 1) + 1) / 3)) := by ring
        _ = 13 * (2 ^ (2 * e - 1) + 1) := by rw [h3]
    rwa [hmul]
  exact Nat.le_of_mul_le_mul_left this (by decide)

lemma thirteen_low_ge_169 {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    169 * 2 ^ (e - 1) ≤ 15 + 32 * ((4 ^ (e - 3) - 1) / 3) := by
  have hsum : 32 * ((4 ^ (e - 3) - 1) / 3) =
      ∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k) :=
    (sum_two_pow_odd_shift (e - 3)).symm
  have hsplit := thirteen_odds_split he heven
  have : 15 + 32 * ((4 ^ (e - 3) - 1) / 3) =
      15 + ∑ k ∈ Finset.range (e - 3), (2 : ℕ) ^ (5 + 2 * k) := by
    rw [hsum]
  rw [this, hsplit]
  have hleS : 2 ^ (e + 2) + 2 ^ (e + 4) + 2 ^ (e + 6) ≤
      2 ^ (e + 1) + 2 ^ (e + 3) + 2 ^ (e + 5) + 2 ^ (e + 7) := by
    have hm := thirteen_mid_odds_mul (by omega : 1 ≤ e)
    have hs := thirteen_S_eq e
    have : 42 * 2 ^ (e + 1) ≤ 85 * 2 ^ (e + 1) :=
      Nat.mul_le_mul_right _ (by decide)
    omega
  have h169 := one_six_nine_shift (by omega : 1 ≤ e)
  omega

lemma thirteen_13Z_sub {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    13 * ((2 ^ (2 * e - 1) + 1) / 3) - 169 * 2 ^ (e - 1) =
      2 ^ (2 * e + 1) +
        (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
          43 * 2 ^ (e + 1) +
          2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3)) := by
  have hZ := thirteen_Z_mul (by omega : 3 ≤ e)
  have hcore := thirteen_D_core he heven
  have hle2 := thirteen_low_ge_169 he heven
  rw [hZ]
  have hA : 2 ^ (2 * e + 1) + 15 + 32 * ((4 ^ (e - 3) - 1) / 3) =
      2 ^ (2 * e + 1) + (15 + 32 * ((4 ^ (e - 3) - 1) / 3)) := by
    ac_rfl
  rw [hA, Nat.add_sub_assoc hle2, hcore]

lemma thirteen_P_div_three_eq {e : ℕ} (he : 2 ≤ e) :
    13 * ((13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1)) / 3 =
      364 * 2 ^ (2 * e) + 13 * ((2 ^ (2 * e - 1) + 1) / 3) - 169 * 2 ^ (e - 1) := by
  have hP := thirteen_shift_mul e (by omega)
  have hdiv : 3 ∣ 2 ^ (2 * e - 1) + 1 :=
    three_dvd_two_pow_add_one_of_odd (by omega)
  have hZ3 : 3 * ((2 ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have hleP : 39 * 2 ^ (e - 1) ≤ 169 * 2 ^ (2 * e - 1) + 1 := by
    have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
    have : 2 ^ (e - 1) ≤ 2 ^ (2 * e - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hlhs :
      13 * ((13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1)) =
        13 * (169 * 2 ^ (2 * e - 1) - 39 * 2 ^ (e - 1) + 1) := by
    rw [hP]
  have h13exp :
      13 * (169 * 2 ^ (2 * e - 1) - 39 * 2 ^ (e - 1) + 1) =
        2197 * 2 ^ (2 * e - 1) - 507 * 2 ^ (e - 1) + 13 := by
    have hle : 39 * 2 ^ (e - 1) ≤ 169 * 2 ^ (2 * e - 1) := by
      have : 2 ^ (e - 1) ≤ 2 ^ (2 * e - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
      omega
    omega
  have h3R :
      3 * (364 * 2 ^ (2 * e) + 13 * ((2 ^ (2 * e - 1) + 1) / 3) - 169 * 2 ^ (e - 1)) =
        3 * 364 * 2 ^ (2 * e) + 13 * (2 ^ (2 * e - 1) + 1) - 3 * 169 * 2 ^ (e - 1) := by
    have hleZ : 169 * 2 ^ (e - 1) ≤ 364 * 2 ^ (2 * e) + 13 * ((2 ^ (2 * e - 1) + 1) / 3) := by
      have : 1 ≤ 2 ^ (e - 1) := Nat.one_le_two_pow
      have : 2 ^ (e - 1) ≤ 2 ^ (2 * e) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have : 3 * (13 * ((2 ^ (2 * e - 1) + 1) / 3)) = 13 * (2 ^ (2 * e - 1) + 1) := by
      omega
    omega
  have hpow : 2 ^ (2 * e) = 2 * 2 ^ (2 * e - 1) := by
    calc 2 ^ (2 * e) = 2 ^ ((2 * e - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (2 * e - 1) := two_pow_succ' _
  have heq : 3 * 364 * 2 ^ (2 * e) + 13 * (2 ^ (2 * e - 1) + 1) - 3 * 169 * 2 ^ (e - 1) =
      2197 * 2 ^ (2 * e - 1) - 507 * 2 ^ (e - 1) + 13 := by
    rw [hpow]
    omega
  have hmul : 3 * (364 * 2 ^ (2 * e) + 13 * ((2 ^ (2 * e - 1) + 1) / 3) - 169 * 2 ^ (e - 1)) =
      13 * ((13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1)) := by
    rw [h3R, heq, hlhs, h13exp]
  exact (Nat.eq_div_of_mul_eq_left (by decide : (3 : ℕ) ≠ 0)
    (by rw [mul_comm]; exact hmul)).symm

lemma thirteen_P_as_D {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    13 * ((13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1)) / 3 =
      366 * 2 ^ (2 * e) +
        (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
          43 * 2 ^ (e + 1) +
          2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3)) := by
  rw [thirteen_P_div_three_eq (by omega)]
  have hsub := thirteen_13Z_sub he heven
  have hle := one_six_nine_le_thirteen_Z (by omega : 8 ≤ e)
  have : 364 * 2 ^ (2 * e) + 13 * ((2 ^ (2 * e - 1) + 1) / 3) - 169 * 2 ^ (e - 1) =
      364 * 2 ^ (2 * e) + (13 * ((2 ^ (2 * e - 1) + 1) / 3) - 169 * 2 ^ (e - 1)) :=
    Nat.add_sub_assoc hle _
  rw [this, hsub]
  have : 2 ^ (2 * e + 1) = 2 * 2 ^ (2 * e) := two_pow_succ' _
  rw [this]
  ring

lemma popc_fortythree : popc 43 = 4 := by decide

lemma popc_three_six_six : popc 366 = 6 := by decide

lemma thirteen_D_lt {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
      43 * 2 ^ (e + 1) +
      2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3) < 2 ^ (2 * e) := by
  set L := 15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3)
  set H := (4 ^ ((e - 10) / 2) - 1) / 3
  have hLlt : L < 2 ^ (e - 1) := thirteen_L_lt (by omega) heven
  have hHlt : H < 2 ^ (e - 10) := by
    have hRb := Rb_lt ((e - 10) / 2)
    have hn : 2 * ((e - 10) / 2) = e - 10 := thirteen_two_nhigh he heven
    have : 2 ^ (2 * ((e - 10) / 2)) = 2 ^ (e - 10) := by rw [hn]
    rwa [this] at hRb
  have : L + 43 * 2 ^ (e + 1) + 2 ^ (e + 9) * H
      < 2 ^ (e - 1) + 43 * 2 ^ (e + 1) + 2 ^ (e + 9) * 2 ^ (e - 10) := by
    have h1 : L + 43 * 2 ^ (e + 1) < 2 ^ (e - 1) + 43 * 2 ^ (e + 1) := by omega
    have h2 : 2 ^ (e + 9) * H ≤ 2 ^ (e + 9) * (2 ^ (e - 10) - 1) := by
      have : H ≤ 2 ^ (e - 10) - 1 := Nat.le_sub_one_of_lt hHlt
      exact Nat.mul_le_mul_left _ this
    have : 2 ^ (e + 9) * (2 ^ (e - 10) - 1) < 2 ^ (e + 9) * 2 ^ (e - 10) := by
      have hpos : 0 < 2 ^ (e + 9) := Nat.pow_pos (by decide)
      have : 2 ^ (e - 10) - 1 < 2 ^ (e - 10) := Nat.sub_lt (Nat.one_le_two_pow) (by decide)
      exact Nat.mul_lt_mul_of_pos_left this hpos
    omega
  have hmid : 2 ^ (e - 1) + 43 * 2 ^ (e + 1) = 173 * 2 ^ (e - 1) := by
    have : 2 ^ (e + 1) = 4 * 2 ^ (e - 1) := by
      have : e + 1 = (e - 1) + 2 := by omega
      rw [this, pow_add, pow_two]; ring
    rw [this]; ring
  have hhi : 2 ^ (e + 9) * 2 ^ (e - 10) = 2 ^ (2 * e - 1) := by
    rw [← pow_add]; congr 1; omega
  have : 2 ^ (e - 1) + 43 * 2 ^ (e + 1) + 2 ^ (e + 9) * 2 ^ (e - 10) =
      173 * 2 ^ (e - 1) + 2 ^ (2 * e - 1) := by
    rw [hmid, hhi]
  have : 173 * 2 ^ (e - 1) + 2 ^ (2 * e - 1) < 2 ^ (2 * e) := by
    have hpow : 2 ^ (2 * e) = 2 * 2 ^ (2 * e - 1) := by
      calc 2 ^ (2 * e) = 2 ^ ((2 * e - 1) + 1) := by congr 1; omega
        _ = 2 * 2 ^ (2 * e - 1) := two_pow_succ' _
    have : 173 * 2 ^ (e - 1) < 2 ^ (2 * e - 1) := by
      have : 2 ^ (2 * e - 1) = 2 ^ e * 2 ^ (e - 1) := by
        rw [← pow_add]; congr 1; omega
      have : 173 < 2 ^ e := by
        have : 2 ^ 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
        have : (2 : ℕ) ^ 8 = 256 := rfl
        omega
      have : 173 * 2 ^ (e - 1) < 2 ^ e * 2 ^ (e - 1) :=
        Nat.mul_lt_mul_of_pos_right this (Nat.pow_pos (by decide))
      omega
    omega
  omega

lemma popc_thirteen_D {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    popc (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
      43 * 2 ^ (e + 1) +
      2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3)) = e := by
  set L := 15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3)
  set H := (4 ^ ((e - 10) / 2) - 1) / 3
  have hLlt : L < 2 ^ (e - 1) := thirteen_L_lt (by omega) heven
  have hL1 : L < 2 ^ (e + 1) := by
    have : 2 ^ (e - 1) ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hpop1 : popc (L + 43 * 2 ^ (e + 1)) = popc 43 + popc L := by
    have : L + 43 * 2 ^ (e + 1) = L + 2 ^ (e + 1) * 43 := by ring
    rw [this]
    exact popc_add_two_pow_mul hL1
  have hlowlt : L + 43 * 2 ^ (e + 1) < 2 ^ (e + 9) := by
    have : L + 43 * 2 ^ (e + 1) < 2 ^ (e + 1) + 43 * 2 ^ (e + 1) := by omega
    have : (2 : ℕ) ^ (e + 1) + 43 * 2 ^ (e + 1) = 44 * 2 ^ (e + 1) := by ring
    have hpos : 0 < 2 ^ (e + 1) := Nat.pow_pos (by decide)
    have h44 : 44 * 2 ^ (e + 1) < 256 * 2 ^ (e + 1) :=
      Nat.mul_lt_mul_of_pos_right (by decide) hpos
    have h256 : (256 : ℕ) * 2 ^ (e + 1) = 2 ^ (e + 9) := by
      rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add]
      congr 1; omega
    omega
  have hpop2 : popc (L + 43 * 2 ^ (e + 1) + 2 ^ (e + 9) * H) =
      popc H + popc (L + 43 * 2 ^ (e + 1)) :=
    popc_add_two_pow_mul hlowlt
  have hpopL : popc L = (e - 6) / 2 + 4 := popc_thirteen_L _
  have hpopH : popc H = (e - 10) / 2 := popc_R _
  have hsum := thirteen_nlow_nhigh he heven
  rw [hpop2, hpop1, hpopL, hpopH, popc_fortythree]
  omega

lemma popc_thirteen_P_div {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    popc (13 * ((13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1)) / 3) = e + 6 := by
  rw [thirteen_P_as_D he heven]
  have hlt := thirteen_D_lt he heven
  have : 366 * 2 ^ (2 * e) +
      (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
        43 * 2 ^ (e + 1) +
        2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3)) =
      (15 + 32 * ((4 ^ ((e - 6) / 2) - 1) / 3) +
        43 * 2 ^ (e + 1) +
        2 ^ (e + 9) * ((4 ^ ((e - 10) / 2) - 1) / 3)) + 2 ^ (2 * e) * 366 := by
    ring
  rw [this, popc_add_two_pow_mul hlt, popc_thirteen_D he heven, popc_three_six_six]
  omega

lemma popc_choose_three_thirteen_two_pow {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    popc (Nat.choose (13 * 2 ^ e) 3) = e + 6 := by
  rw [choose_three_thirteen_two_pow (by omega), popc_mul_two_pow]
  have hassoc :
      13 * (13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1) =
        13 * ((13 * 2 ^ e - 1) * (13 * 2 ^ (e - 1) - 1)) := by
    ring
  rw [hassoc]
  exact popc_thirteen_P_div he heven

lemma a_ne_zero_thirteen_two_pow {e : ℕ} (he : 10 ≤ e) (heven : e % 2 = 0) :
    _root_.a (13 * 2 ^ e) ≠ 0 := by
  refine a_ne_zero_of_witness (13 * 2 ^ e) 3 (by decide) ?_ ?_
  · have : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  · have hpop := popc_choose_three_thirteen_two_pow he heven
    omega

lemma a_ne_zero_thirteen_two_pow_eight : _root_.a (13 * 2 ^ 8) ≠ 0 := by
  refine a_ne_zero_of_witness (13 * 2 ^ 8) 3 (by decide) (by decide) ?_
  have hc : Nat.choose (13 * 2 ^ 8) 3 = 6137720576 := by decide
  rw [hc]; decide

/-! ### Even 3-bit adjacent, `e` odd, `B` even: `C(n,3)` is evil. -/

lemma three_two_pow_add_one (B : ℕ) :
    (2 : ℕ) ^ (B + 1) + 2 ^ B + 1 = 3 * 2 ^ B + 1 := by
  have : (2 : ℕ) ^ (B + 1) = 2 * 2 ^ B := two_pow_succ' B
  omega

lemma adj_U_eq {e : ℕ} (hodd : e % 2 = 1) :
    (2 : ℕ) ^ (e - 1) = 4 ^ (e / 2) := by
  have : e = 2 * (e / 2) + 1 := by omega
  calc (2 : ℕ) ^ (e - 1) = 2 ^ (2 * (e / 2)) := by congr 1; omega
    _ = (2 ^ 2) ^ (e / 2) := pow_mul (2 : ℕ) 2 (e / 2)
    _ = 4 ^ (e / 2) := rfl

lemma Q_two_t_eq (t : ℕ) :
    (2 ^ (4 * t + 1) + 1) / 3 = 1 + 2 * ((4 ^ (2 * t) - 1) / 3) := by
  have h : 4 * t + 1 = 2 * (2 * t) + 1 := by omega
  rw [h]
  exact Q_eq (2 * t)

lemma adj_S_eq_of_odd {e B : ℕ} (hodd : e % 2 = 1) :
    (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3 =
      2 ^ (e - 1 + B) + (2 ^ (e - 1) - 1) / 3 := by
  have hodd' : (e - 1) % 2 = 0 := by omega
  have hle : 1 ≤ (2 : ℕ) ^ (e - 1) := Nat.one_le_two_pow
  have hR : 3 ∣ 2 ^ (e - 1) - 1 := by
    have : e - 1 = 2 * ((e - 1) / 2) := by omega
    rw [this, pow_mul]
    simpa using three_dvd_four_pow_sub_one ((e - 1) / 2)
  have hexp :
      (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) - 1 =
        3 * 2 ^ (e - 1 + B) + (2 ^ (e - 1) - 1) := by
    have : (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) =
        3 * ((2 : ℕ) ^ (e - 1) * 2 ^ B) + 2 ^ (e - 1) := by ring
    have hsh : (2 : ℕ) ^ (e - 1) * 2 ^ B = 2 ^ (e - 1 + B) := (pow_add _ _ _).symm
    omega
  have hdiv : 3 ∣ 2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1 := by
    rw [hexp]
    exact dvd_add (dvd_mul_right _ _) hR
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs : 3 * ((2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3) =
      2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1 := Nat.mul_div_cancel' hdiv
  have rhs : 3 * (2 ^ (e - 1 + B) + (2 ^ (e - 1) - 1) / 3) =
      3 * 2 ^ (e - 1 + B) + (2 ^ (e - 1) - 1) := by
    have : 3 * ((2 ^ (e - 1) - 1) / 3) = 2 ^ (e - 1) - 1 := Nat.mul_div_cancel' hR
    omega
  rw [lhs, rhs, hexp]

lemma adj_R_eq {e : ℕ} (hodd : e % 2 = 1) :
    (2 ^ (e - 1) - 1) / 3 = (4 ^ (e / 2) - 1) / 3 := by
  rw [adj_U_eq hodd]

lemma popc_adj_R {e : ℕ} (hodd : e % 2 = 1) :
    popc ((2 ^ (e - 1) - 1) / 3) = e / 2 := by
  rw [adj_R_eq hodd, popc_R]

lemma popc_adj_S {e B : ℕ} (hodd : e % 2 = 1) :
    popc ((2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3) = e / 2 + 1 := by
  rw [adj_S_eq_of_odd hodd]
  have hRlt : (2 ^ (e - 1) - 1) / 3 < 2 ^ (e - 1 + B) := by
    have hlt : (2 ^ (e - 1) - 1) / 3 < 2 ^ (e - 1) := by
      have hdiv : 3 ∣ 2 ^ (e - 1) - 1 := by
        have : e - 1 = 2 * ((e - 1) / 2) := by omega
        rw [this, pow_mul]
        simpa using three_dvd_four_pow_sub_one ((e - 1) / 2)
      have hmul : 3 * ((2 ^ (e - 1) - 1) / 3) = 2 ^ (e - 1) - 1 :=
        Nat.mul_div_cancel' hdiv
      have : 2 ^ (e - 1) - 1 < 2 ^ (e - 1) :=
        Nat.sub_lt (Nat.one_le_two_pow) (by decide)
      omega
    have : (2 : ℕ) ^ (e - 1) ≤ 2 ^ (e - 1 + B) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
    omega
  have hform : (2 ^ (e - 1) - 1) / 3 + 2 ^ (e - 1 + B) =
      (2 ^ (e - 1) - 1) / 3 + 2 ^ (e - 1 + B) * 1 := by
    ring
  rw [add_comm (2 ^ (e - 1 + B)), hform, popc_add_two_pow_mul hRlt, popc_one,
    popc_adj_R hodd]
  omega

lemma adj_mul_shift {e B : ℕ} (heA : B + 1 < e) (hB : 3 ≤ B) :
    (2 ^ (B + 1) + 2 ^ B + 1) * (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1) - 1) =
      2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) + 2 ^ (e + B + 1) +
        (2 ^ e - 1 - 2 ^ (B + 1) - 2 ^ B) := by
  have hBlt : B < e := by omega
  have hAB' : (B + 1 : ℕ) ≠ B := by omega
  have hform := mul_shift_sub_eq (e := e) (A := B + 1) (B := B)
  rw [hform, m_sq_shift_sub, high_plus_low_of_even_three_bit heA hBlt hAB',
    high_adjacent_merge]

lemma adj_odd_part {e B : ℕ} (he : 2 ≤ e) (hodd : e % 2 = 1) :
    (2 ^ (B + 1) + 2 ^ B + 1) *
        (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (2 ^ (B + 1) + 2 ^ B + 1) - 1) / 3 =
      ((2 ^ (B + 1) + 2 ^ B + 1) * (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1) - 1)) *
        ((2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3) := by
  have hm : (2 : ℕ) ^ (B + 1) + 2 ^ B + 1 = 3 * 2 ^ B + 1 :=
    three_two_pow_add_one B
  have hSdiv : 3 ∣ 2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1 := by
    have hR : 3 ∣ 2 ^ (e - 1) - 1 := by
      have : e - 1 = 2 * ((e - 1) / 2) := by omega
      rw [this, pow_mul]
      simpa using three_dvd_four_pow_sub_one ((e - 1) / 2)
    have hexp :
        (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) - 1 =
          3 * 2 ^ (e - 1 + B) + (2 ^ (e - 1) - 1) := by
      have hle : 1 ≤ (2 : ℕ) ^ (e - 1) := Nat.one_le_two_pow
      have : (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) =
          3 * ((2 : ℕ) ^ (e - 1) * 2 ^ B) + 2 ^ (e - 1) := by ring
      have : (2 : ℕ) ^ (e - 1) * 2 ^ B = 2 ^ (e - 1 + B) := (pow_add _ _ _).symm
      omega
    rw [hexp]
    exact dvd_add (dvd_mul_right _ _) hR
  rw [hm, Nat.mul_div_assoc _ hSdiv]

lemma two_mul_pow_succ (k : ℕ) : (2 : ℕ) * 2 ^ k = 2 ^ (k + 1) := by
  rw [← two_pow_succ']

lemma adj_U_sq {e : ℕ} (hodd : e % 2 = 1) :
    ((2 : ℕ) ^ (e - 1)) ^ 2 = 2 ^ (2 * e - 2) := by
  have : e - 1 + (e - 1) = 2 * e - 2 := by omega
  rw [pow_two, ← pow_add, this]

lemma adj_H_shift {e B : ℕ} (he : 1 ≤ e) :
    (2 ^ (e + 2 * B + 3) + 2 ^ (e + 2 * B) + 2 ^ (e + B + 2) +
        2 ^ (e + B + 1)) * 2 ^ (e - 1 + B) =
      2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
        2 ^ (2 * e + 2 * B + 1) + 2 ^ (2 * e + 2 * B) := by
  have h1 : e + 2 * B + 3 + (e - 1 + B) = 2 * e + 3 * B + 2 := by omega
  have h2 : e + 2 * B + (e - 1 + B) = 2 * e + 3 * B - 1 := by omega
  have h3 : e + B + 2 + (e - 1 + B) = 2 * e + 2 * B + 1 := by omega
  have h4 : e + B + 1 + (e - 1 + B) = 2 * e + 2 * B := by omega
  rw [add_mul, add_mul, add_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
    h1, h2, h3, h4]

lemma adj_L_nonneg {e B : ℕ} (heA : B + 1 < e) :
    2 ^ (B + 1) + 2 ^ B + 1 ≤ 2 ^ e :=
  two_pow_add_two_le_of_lt (A := B + 1) (B := B) heA (by omega) (by omega)

lemma adj_L_shift {e B : ℕ} (he : 1 ≤ e) (heA : B + 1 < e) :
    (2 ^ e - 1 - 2 ^ (B + 1) - 2 ^ B) * 2 ^ (e - 1 + B) =
      2 ^ (2 * e + B - 1) - 2 ^ (e - 1 + B) - 2 ^ (e + 2 * B) -
        2 ^ (e + 2 * B - 1) := by
  have hle : 2 ^ (B + 1) + 2 ^ B + 1 ≤ 2 ^ e := adj_L_nonneg heA
  have hL : 2 ^ e - 1 - 2 ^ (B + 1) - 2 ^ B = 2 ^ e - (2 ^ (B + 1) + 2 ^ B + 1) := by
    omega
  rw [hL]
  have hdist :
      (2 ^ e - (2 ^ (B + 1) + 2 ^ B + 1)) * 2 ^ (e - 1 + B) =
        2 ^ e * 2 ^ (e - 1 + B) - (2 ^ (B + 1) + 2 ^ B + 1) * 2 ^ (e - 1 + B) :=
    Nat.mul_sub_right_distrib _ _ _
  rw [hdist]
  have hp1 : e + (e - 1 + B) = 2 * e + B - 1 := by omega
  have hp2 : B + 1 + (e - 1 + B) = e + 2 * B := by omega
  have hp3 : B + (e - 1 + B) = e + 2 * B - 1 := by omega
  have hleft : 2 ^ e * 2 ^ (e - 1 + B) = 2 ^ (2 * e + B - 1) := by
    rw [← pow_add, hp1]
  have hright :
      (2 ^ (B + 1) + 2 ^ B + 1) * 2 ^ (e - 1 + B) =
        2 ^ (e + 2 * B) + 2 ^ (e + 2 * B - 1) + 2 ^ (e - 1 + B) := by
    rw [add_mul, add_mul, ← pow_add, ← pow_add, one_mul, hp2, hp3]
  rw [hleft, hright]
  omega

lemma adj_HL_shift {e B : ℕ} (he : 1 ≤ e) (heA : B + 3 ≤ e) (hB : 3 ≤ B) :
    ((2 ^ (B + 1) + 2 ^ B + 1) * (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1) - 1)) *
        2 ^ (e - 1 + B) =
      2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
        2 ^ (2 * e + 2 * B + 1) + 2 ^ (2 * e + 2 * B) +
        (2 ^ (2 * e + B - 1) - 2 ^ (e - 1 + B) - 2 ^ (e + 2 * B) -
          2 ^ (e + 2 * B - 1)) := by
  have heA' : B + 1 < e := by omega
  rw [adj_mul_shift heA' hB, add_mul, adj_H_shift he, adj_L_shift he heA']

lemma adj_m_as_three (B : ℕ) :
    (2 : ℕ) ^ (B + 1) + 2 ^ B + 1 = 3 * 2 ^ B + 1 :=
  three_two_pow_add_one B

lemma adj_m_sq_three (B : ℕ) :
    (3 * 2 ^ B + 1) ^ 2 = 9 * 4 ^ B + 6 * 2 ^ B + 1 := by
  have h4 : (4 : ℕ) ^ B = (2 ^ 2) ^ B := rfl
  rw [h4, ← pow_mul]
  have : 2 * B = B + B := by omega
  rw [this]
  ring

lemma adj_two_U_sq {e : ℕ} (hodd : e % 2 = 1) :
    2 * ((2 : ℕ) ^ (e - 1)) ^ 2 = 2 ^ (2 * e - 1) := by
  have h1 : 1 ≤ e := by omega
  have h2 : 2 * e - 2 + 1 = 2 * e - 1 := by omega
  rw [adj_U_sq hodd, two_mul_pow_succ, h2]

lemma adj_six_U_sq_four {e B : ℕ} (hodd : e % 2 = 1) :
    6 * ((2 : ℕ) ^ (e - 1)) ^ 2 * 4 ^ B =
      2 ^ (2 * e + 2 * B) + 2 ^ (2 * e + 2 * B - 1) := by
  have hU : ((2 : ℕ) ^ (e - 1)) ^ 2 = 2 ^ (2 * e - 2) := adj_U_sq hodd
  have h4 : (4 : ℕ) ^ B = 2 ^ (2 * B) := four_pow_eq B
  have hmul : 6 * 2 ^ (2 * e - 2) * 2 ^ (2 * B) = 6 * 2 ^ (2 * e + 2 * B - 2) := by
    have : 2 * e - 2 + 2 * B = 2 * e + 2 * B - 2 := by omega
    have : (2 : ℕ) ^ (2 * e - 2) * 2 ^ (2 * B) = 2 ^ (2 * e + 2 * B - 2) := by
      rw [← pow_add, this]
    rw [mul_assoc, this]
  rw [hU, h4, hmul]
  have h6 : (6 : ℕ) * 2 ^ (2 * e + 2 * B - 2) =
      4 * 2 ^ (2 * e + 2 * B - 2) + 2 * 2 ^ (2 * e + 2 * B - 2) := by
    ring
  have ha : 4 * 2 ^ (2 * e + 2 * B - 2) = 2 ^ (2 * e + 2 * B) := by
    have : (4 : ℕ) = 2 ^ 2 := rfl
    rw [this, ← pow_add]
    congr 1; omega
  have hb : 2 * 2 ^ (2 * e + 2 * B - 2) = 2 ^ (2 * e + 2 * B - 1) := by
    rw [two_mul_pow_succ]
    congr 1; omega
  rw [h6, ha, hb]

lemma adj_four_U_sq_two {e B : ℕ} (hodd : e % 2 = 1) :
    4 * ((2 : ℕ) ^ (e - 1)) ^ 2 * 2 ^ B = 2 ^ (2 * e + B) := by
  have hU : ((2 : ℕ) ^ (e - 1)) ^ 2 = 2 ^ (2 * e - 2) := adj_U_sq hodd
  rw [hU, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, ← pow_add]
  congr 1; omega


lemma adj_two_e_pred {e : ℕ} (hodd : e % 2 = 1) :
    2 * e - 1 = 2 * (e - 1) + 1 := by omega

lemma adj_Qt_eq {e : ℕ} (hodd : e % 2 = 1) :
    (2 ^ (2 * e - 1) + 1) / 3 = 1 + 2 * ((4 ^ (e - 1) - 1) / 3) := by
  have h : 2 * e - 1 = 2 * (e - 1) + 1 := adj_two_e_pred hodd
  rw [h]
  exact Q_eq (e - 1)

lemma popc_adj_Qt {e : ℕ} (hodd : e % 2 = 1) :
    popc ((2 ^ (2 * e - 1) + 1) / 3) = e := by
  have h : 2 * e - 1 = 2 * (e - 1) + 1 := adj_two_e_pred hodd
  rw [h, popc_Q]
  omega

lemma adj_three_dvd_Qt {e : ℕ} (hodd : e % 2 = 1) :
    3 ∣ 2 ^ (2 * e - 1) + 1 :=
  three_dvd_two_pow_add_one_of_odd (by omega : (2 * e - 1) % 2 = 1)

lemma adj_W_core {e B : ℕ} (hodd : e % 2 = 1) :
    2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 =
      3 * (6 * ((2 : ℕ) ^ (e - 1)) ^ 2 * 4 ^ B +
        4 * ((2 : ℕ) ^ (e - 1)) ^ 2 * 2 ^ B) +
        (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 + 1) := by
  rw [adj_m_sq_three B]
  ring

lemma adj_W_eq {e B : ℕ} (hodd : e % 2 = 1) :
    (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3 =
      2 ^ (2 * e + 2 * B) + 2 ^ (2 * e + 2 * B - 1) + 2 ^ (2 * e + B) +
        (2 ^ (2 * e - 1) + 1) / 3 := by
  have hcore := adj_W_core (e := e) (B := B) hodd
  have hdiv1 : 3 ∣ 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 + 1 := by
    rw [adj_two_U_sq hodd]
    exact adj_three_dvd_Qt hodd
  have hdiv : 3 ∣ 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 := by
    rw [hcore]
    exact dvd_add (dvd_mul_right _ _) hdiv1
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs :
      3 * ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) =
        2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 :=
    Nat.mul_div_cancel' hdiv
  have h6 := adj_six_U_sq_four (e := e) (B := B) hodd
  have h4 := adj_four_U_sq_two (e := e) (B := B) hodd
  have h2 : 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 = 2 ^ (2 * e - 1) := adj_two_U_sq hodd
  have hQt : 3 * ((2 ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
    Nat.mul_div_cancel' (adj_three_dvd_Qt hodd)
  have rhs :
      3 * (2 ^ (2 * e + 2 * B) + 2 ^ (2 * e + 2 * B - 1) + 2 ^ (2 * e + B) +
          (2 ^ (2 * e - 1) + 1) / 3) =
        3 * (6 * ((2 : ℕ) ^ (e - 1)) ^ 2 * 4 ^ B +
          4 * ((2 : ℕ) ^ (e - 1)) ^ 2 * 2 ^ B) +
          (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 + 1) := by
    rw [h6, h4, h2]
    omega
  rw [lhs, rhs, hcore]

lemma adj_nine_shift {e B : ℕ} (he : 1 ≤ e) :
    9 * (2 : ℕ) ^ (e - 1 + 2 * B) =
      2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) := by
  have h8 : (8 : ℕ) * 2 ^ (e - 1 + 2 * B) = 2 ^ (e + 2 * B + 2) := by
    have : (8 : ℕ) = 2 ^ 3 := rfl
    rw [this, ← pow_add]
    congr 1; omega
  have : (9 : ℕ) * 2 ^ (e - 1 + 2 * B) =
      8 * 2 ^ (e - 1 + 2 * B) + 2 ^ (e - 1 + 2 * B) := by ring
  rw [this, h8]
  have : e - 1 + 2 * B = e + 2 * B - 1 := by omega
  rw [this]

lemma adj_six_shift {e B : ℕ} (he : 1 ≤ e) :
    6 * (2 : ℕ) ^ (e - 1 + B) = 2 ^ (e + B + 1) + 2 ^ (e + B) := by
  have h4 : (4 : ℕ) * 2 ^ (e - 1 + B) = 2 ^ (e + B + 1) := by
    have : (4 : ℕ) = 2 ^ 2 := rfl
    rw [this, ← pow_add]
    congr 1; omega
  have h2 : (2 : ℕ) * 2 ^ (e - 1 + B) = 2 ^ (e + B) := by
    rw [two_mul_pow_succ]
    congr 1; omega
  have : (6 : ℕ) * 2 ^ (e - 1 + B) =
      4 * 2 ^ (e - 1 + B) + 2 * 2 ^ (e - 1 + B) := by ring
  rw [this, h4, h2]

lemma adj_Um2_eq {e B : ℕ} (hodd : e % 2 = 1) :
    (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2 =
      2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + B + 1) +
        2 ^ (e + B) + 2 ^ (e - 1) := by
  have he : 1 ≤ e := by omega
  rw [adj_m_sq_three B, mul_add, mul_add, mul_one]
  have h4 : (4 : ℕ) ^ B = 2 ^ (2 * B) := four_pow_eq B
  have h9 : (2 : ℕ) ^ (e - 1) * (9 * 4 ^ B) = 9 * 2 ^ (e - 1 + 2 * B) := by
    have hsh : (2 : ℕ) ^ (e - 1) * 4 ^ B = 2 ^ (e - 1 + 2 * B) := by
      rw [h4, ← pow_add]
    rw [← mul_assoc, mul_comm (2 ^ (e - 1)), mul_assoc, hsh]
  have h6 : (2 : ℕ) ^ (e - 1) * (6 * 2 ^ B) = 6 * 2 ^ (e - 1 + B) := by
    have : (2 : ℕ) ^ (e - 1) * 2 ^ B = 2 ^ (e - 1 + B) := (pow_add _ _ _).symm
    rw [← mul_assoc, mul_comm (2 ^ (e - 1)), mul_assoc, this]
  rw [h9, h6, adj_nine_shift he, adj_six_shift he]
  ac_rfl

lemma adj_three_two_pow_pair {k : ℕ} (hk : 1 ≤ k) :
    3 * (2 : ℕ) ^ k + 3 * 2 ^ (k - 1) = 2 ^ (k + 2) + 2 ^ (k - 1) := by
  have h2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
    calc (2 : ℕ) ^ k = 2 ^ (k - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (k - 1) := two_pow_succ' _
  rw [h2]
  have : 3 * (2 * 2 ^ (k - 1)) + 3 * 2 ^ (k - 1) = 9 * 2 ^ (k - 1) := by ring
  rw [this]
  have : (9 : ℕ) * 2 ^ (k - 1) = 8 * 2 ^ (k - 1) + 2 ^ (k - 1) := by ring
  rw [this]
  have : (8 : ℕ) * 2 ^ (k - 1) = 2 ^ (k + 2) := by
    have : (8 : ℕ) = 2 ^ 3 := rfl
    rw [this, ← pow_add]
    congr 1; omega
  rw [this]

lemma adj_four_two_pow (k : ℕ) :
    4 * (2 : ℕ) ^ k = 2 ^ (k + 2) := by
  have : (4 : ℕ) = 2 ^ 2 := rfl
  rw [this, ← pow_add, Nat.add_comm]

lemma adj_three_B_Qt {e B : ℕ} (hodd : e % 2 = 1) :
    3 * 2 ^ B * ((2 ^ (2 * e - 1) + 1) / 3) =
      2 ^ (2 * e + B - 1) + 2 ^ B := by
  have hmul : 3 * ((2 ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
    Nat.mul_div_cancel' (adj_three_dvd_Qt hodd)
  have : 3 * 2 ^ B * ((2 ^ (2 * e - 1) + 1) / 3) =
      2 ^ B * (3 * ((2 ^ (2 * e - 1) + 1) / 3)) := by ring
  rw [this, hmul, mul_add, mul_one, ← pow_add]
  congr 2
  omega

lemma adj_mW_eq {e B : ℕ} (hodd : e % 2 = 1) :
    (3 * 2 ^ B + 1) *
        ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) =
      2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
        2 ^ (2 * e + 2 * B + 2) + 2 ^ (2 * e + 2 * B - 1) +
        2 ^ (2 * e + B) + 2 ^ (2 * e + B - 1) +
        (2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B := by
  rw [adj_W_eq hodd, mul_add, mul_add, mul_add]
  have hm : (3 * 2 ^ B + 1) * 2 ^ (2 * e + 2 * B) =
      3 * 2 ^ (2 * e + 3 * B) + 2 ^ (2 * e + 2 * B) := by
    have hdist : (3 * 2 ^ B + 1) * 2 ^ (2 * e + 2 * B) =
        3 * (2 ^ B * 2 ^ (2 * e + 2 * B)) + 2 ^ (2 * e + 2 * B) := by ring
    have hsh : 2 ^ B * 2 ^ (2 * e + 2 * B) = 2 ^ (2 * e + 3 * B) := by
      rw [← pow_add]; congr 1; omega
    rw [hdist, hsh]
  have hm1 : (3 * 2 ^ B + 1) * 2 ^ (2 * e + 2 * B - 1) =
      3 * 2 ^ (2 * e + 3 * B - 1) + 2 ^ (2 * e + 2 * B - 1) := by
    have hdist : (3 * 2 ^ B + 1) * 2 ^ (2 * e + 2 * B - 1) =
        3 * (2 ^ B * 2 ^ (2 * e + 2 * B - 1)) + 2 ^ (2 * e + 2 * B - 1) := by
      ring
    have hsh : 2 ^ B * 2 ^ (2 * e + 2 * B - 1) = 2 ^ (2 * e + 3 * B - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hdist, hsh]
  have hm2 : (3 * 2 ^ B + 1) * 2 ^ (2 * e + B) =
      3 * 2 ^ (2 * e + 2 * B) + 2 ^ (2 * e + B) := by
    have hdist : (3 * 2 ^ B + 1) * 2 ^ (2 * e + B) =
        3 * (2 ^ B * 2 ^ (2 * e + B)) + 2 ^ (2 * e + B) := by ring
    have hsh : 2 ^ B * 2 ^ (2 * e + B) = 2 ^ (2 * e + 2 * B) := by
      rw [← pow_add]; congr 1; omega
    rw [hdist, hsh]
  have hm3 : (3 * 2 ^ B + 1) * ((2 ^ (2 * e - 1) + 1) / 3) =
      2 ^ (2 * e + B - 1) + 2 ^ B + (2 ^ (2 * e - 1) + 1) / 3 := by
    have : (3 * 2 ^ B + 1) * ((2 ^ (2 * e - 1) + 1) / 3) =
        3 * 2 ^ B * ((2 ^ (2 * e - 1) + 1) / 3) +
          (2 ^ (2 * e - 1) + 1) / 3 := by ring
    rw [this, adj_three_B_Qt hodd]
  rw [hm, hm1, hm2, hm3]
  have hpair : 3 * (2 : ℕ) ^ (2 * e + 3 * B) + 3 * 2 ^ (2 * e + 3 * B - 1) =
      2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) :=
    adj_three_two_pow_pair (k := 2 * e + 3 * B) (by omega)
  have h4 : 3 * (2 : ℕ) ^ (2 * e + 2 * B) + 2 ^ (2 * e + 2 * B) =
      2 ^ (2 * e + 2 * B + 2) := by
    have : 3 * (2 : ℕ) ^ (2 * e + 2 * B) + 2 ^ (2 * e + 2 * B) =
        4 * 2 ^ (2 * e + 2 * B) := by ring
    rw [this, adj_four_two_pow]
  omega



lemma sub_one_mul_sub_one {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a - 1) * (b - 1) = a * b + 1 - a - b := by
  have h1 : (a - 1) * (b - 1) = (a - 1) * b - (a - 1) := by
    simpa using Nat.mul_sub_left_distrib (a - 1) b 1
  have h2 : (a - 1) * b = a * b - b := by
    simpa using Nat.mul_sub_right_distrib a 1 b
  rw [h1, h2]
  omega

lemma adj_two_e_as_two_U {e : ℕ} (he : 1 ≤ e) :
    (2 : ℕ) ^ e = 2 * 2 ^ (e - 1) := by
  calc (2 : ℕ) ^ e = 2 ^ (e - 1 + 1) := by congr 1; omega
    _ = 2 * 2 ^ (e - 1) := two_pow_succ' _

lemma adj_Um_ge_two {e B : ℕ} (he : 1 ≤ e) :
    2 ≤ (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) := by
  have hU : 1 ≤ (2 : ℕ) ^ (e - 1) := Nat.one_le_two_pow
  have hm : 2 ≤ 3 * 2 ^ B + 1 := by
    have : 1 ≤ 2 ^ B := Nat.one_le_two_pow
    omega
  have : 1 * 2 ≤ (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) :=
    Nat.mul_le_mul hU hm
  simpa using this

lemma adj_three_Um_le {e B : ℕ} (he : 1 ≤ e) :
    3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1)) ≤
      2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 := by
  have hx : 2 ≤ (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) := adj_Um_ge_two he
  have h3 : 3 ≤ 2 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1)) := by omega
  have hmul :
      3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1)) ≤
        (2 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1))) *
          ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1)) :=
    Nat.mul_le_mul_right _ h3
  have hre :
      (2 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1))) *
          ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1)) =
        2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 := by ring
  rw [hre] at hmul
  omega

lemma adj_Q_num_eq {e B : ℕ} (he : 1 ≤ e) :
    (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) =
      (3 * 2 ^ B + 1) *
          (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) -
        3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2) := by
  have hm : 1 ≤ 3 * 2 ^ B + 1 := by omega
  have hU : 1 ≤ (2 : ℕ) ^ (e - 1) := Nat.one_le_two_pow
  have hUm : 1 ≤ (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) := by
    have : 1 * 1 ≤ (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) :=
      Nat.mul_le_mul hU hm
    simpa using this
  have h2Um : 1 ≤ 2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) := by omega
  have h2e : 2 ^ e * (3 * 2 ^ B + 1) = 2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) := by
    rw [adj_two_e_as_two_U he]; ring
  have hex :
      (2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) - 1) *
          (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) =
        (2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1))) *
            (2 ^ (e - 1) * (3 * 2 ^ B + 1)) + 1 -
          2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) -
          (2 ^ (e - 1) * (3 * 2 ^ B + 1)) :=
    sub_one_mul_sub_one h2Um hUm
  have hre :
      (2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1))) *
          (2 ^ (e - 1) * (3 * 2 ^ B + 1)) + 1 -
        2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) -
        (2 ^ (e - 1) * (3 * 2 ^ B + 1)) =
      2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 -
        3 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) := by
    have hpow : (2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1))) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1)) =
        2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 := by ring
    have hadd : 2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) +
        (2 ^ (e - 1) * (3 * 2 ^ B + 1)) =
        3 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) := by ring
    omega
  have hassoc :
      (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
          (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) =
        (3 * 2 ^ B + 1) *
          ((2 * (2 ^ (e - 1) * (3 * 2 ^ B + 1)) - 1) *
            (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1)) := by
    rw [h2e]; ring
  rw [hassoc, hex, hre]
  have hle := adj_three_Um_le (e := e) (B := B) he
  have hdist :
      (3 * 2 ^ B + 1) *
          (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 -
            3 * (2 ^ (e - 1) * (3 * 2 ^ B + 1))) =
        (3 * 2 ^ B + 1) *
            (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) -
          (3 * 2 ^ B + 1) * (3 * (2 ^ (e - 1) * (3 * 2 ^ B + 1))) :=
    Nat.mul_sub_left_distrib _ _ _
  have hr :
      (3 * 2 ^ B + 1) * (3 * (2 ^ (e - 1) * (3 * 2 ^ B + 1))) =
        3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2) := by ring
  rw [hdist, hr]



lemma adj_three_dvd_Um_sub {e B : ℕ} (hodd : e % 2 = 1) :
    3 ∣ 2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1 := by
  have hR : 3 ∣ 2 ^ (e - 1) - 1 := by
    have : e - 1 = 2 * ((e - 1) / 2) := by omega
    rw [this, pow_mul]
    simpa using three_dvd_four_pow_sub_one ((e - 1) / 2)
  have hexp :
      (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) - 1 =
        3 * 2 ^ (e - 1 + B) + (2 ^ (e - 1) - 1) := by
    have hle : 1 ≤ (2 : ℕ) ^ (e - 1) := Nat.one_le_two_pow
    have : (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) =
        3 * ((2 : ℕ) ^ (e - 1) * 2 ^ B) + 2 ^ (e - 1) := by ring
    have : (2 : ℕ) ^ (e - 1) * 2 ^ B = 2 ^ (e - 1 + B) := (pow_add _ _ _).symm
    omega
  rw [hexp]
  exact dvd_add (dvd_mul_right _ _) hR

lemma adj_three_dvd_prod {e B : ℕ} (hodd : e % 2 = 1) :
    3 ∣ (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) :=
  dvd_mul_of_dvd_right (adj_three_dvd_Um_sub hodd) _

lemma adj_mW_ge_Um2 {e B : ℕ} (he : 1 ≤ e) (hodd : e % 2 = 1) :
    (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2 ≤
      (3 * 2 ^ B + 1) *
        ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) := by
  have hWdiv : 3 ∣ 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 := by
    have hcore := adj_W_core (e := e) (B := B) hodd
    have hdiv1 : 3 ∣ 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 + 1 := by
      rw [adj_two_U_sq hodd]
      exact adj_three_dvd_Qt hodd
    rw [hcore]
    exact dvd_add (dvd_mul_right _ _) hdiv1
  have h3W :
      3 * ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) =
        2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 :=
    Nat.mul_div_cancel' hWdiv
  have h3mW :
      3 * ((3 * 2 ^ B + 1) *
          ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3)) =
        (3 * 2 ^ B + 1) *
          (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) := by
    rw [← mul_assoc, mul_comm 3, mul_assoc, h3W]
  have hle : 3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2) ≤
      (3 * 2 ^ B + 1) *
        (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) := by
    have hm : 1 ≤ 3 * 2 ^ B + 1 := by omega
    have hU : 1 ≤ (2 : ℕ) ^ (e - 1) := Nat.one_le_two_pow
    have hx : 2 ≤ (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) := adj_Um_ge_two he
    -- 3 U m^2 ≤ m (2 U^2 m^2 + 1) = 2 U^2 m^3 + m
    -- iff 3 U m ≤ 2 U^2 m^2 + 1 which is adj_three_Um_le after * m
    have := adj_three_Um_le (e := e) (B := B) he
    have :
        (3 * 2 ^ B + 1) * (3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1))) ≤
          (3 * 2 ^ B + 1) *
            (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) :=
      Nat.mul_le_mul_left _ this
    convert this using 1 <;> ring
  have : 3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2) ≤
      3 * ((3 * 2 ^ B + 1) *
        ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3)) := by
    rwa [h3mW]
  exact Nat.le_of_mul_le_mul_left this (by decide : (0 : ℕ) < 3)

lemma adj_Q_eq_mW_sub {e B : ℕ} (he : 1 ≤ e) (hodd : e % 2 = 1) :
    (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3 =
      (3 * 2 ^ B + 1) *
          ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) -
        (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2 := by
  have hdiv := adj_three_dvd_prod (e := e) (B := B) hodd
  have hnum := adj_Q_num_eq (e := e) (B := B) he
  have hge := adj_mW_ge_Um2 (e := e) (B := B) he hodd
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
  have lhs :
      3 * ((3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
          (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3) =
        (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
          (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) :=
    Nat.mul_div_cancel' hdiv
  have hWdiv : 3 ∣ 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 := by
    have hcore := adj_W_core (e := e) (B := B) hodd
    have hdiv1 : 3 ∣ 2 * ((2 : ℕ) ^ (e - 1)) ^ 2 + 1 := by
      rw [adj_two_U_sq hodd]
      exact adj_three_dvd_Qt hodd
    rw [hcore]
    exact dvd_add (dvd_mul_right _ _) hdiv1
  have h3W :
      3 * ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) =
        2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1 :=
    Nat.mul_div_cancel' hWdiv
  have rhs :
      3 * ((3 * 2 ^ B + 1) *
            ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3) -
          (2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2) =
        (3 * 2 ^ B + 1) *
            (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) -
          3 * ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2) := by
    have hdist :=
      Nat.mul_sub_left_distrib (3)
        ((3 * 2 ^ B + 1) *
          ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3))
        ((2 : ℕ) ^ (e - 1) * (3 * 2 ^ B + 1) ^ 2)
    rw [hdist]
    have : 3 * ((3 * 2 ^ B + 1) *
        ((2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) / 3)) =
        (3 * 2 ^ B + 1) *
          (2 * ((2 : ℕ) ^ (e - 1)) ^ 2 * (3 * 2 ^ B + 1) ^ 2 + 1) := by
      rw [← mul_assoc, mul_comm 3, mul_assoc, h3W]
    rw [this]
  rw [lhs, rhs, hnum]

lemma adj_Q_decomp {e B : ℕ} (he : 1 ≤ e) (hodd : e % 2 = 1) :
    (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3 =
      2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
        2 ^ (2 * e + 2 * B + 2) + 2 ^ (2 * e + 2 * B - 1) +
        2 ^ (2 * e + B) + 2 ^ (2 * e + B - 1) +
        (2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B -
        (2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + B + 1) +
          2 ^ (e + B) + 2 ^ (e - 1)) := by
  rw [adj_Q_eq_mW_sub he hodd, adj_mW_eq hodd, adj_Um2_eq hodd]




lemma two_pow_add_self (k : ℕ) : (2 : ℕ) ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [← two_mul, ← two_pow_succ']

lemma nat_mod_two_pow_succ_of_even_div {n k : ℕ} (h : n / 2 ^ k % 2 = 0) :
    n % 2 ^ (k + 1) = n % 2 ^ k := by
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ' k
  have hdiv2 : n / 2 ^ k / 2 = n / (2 ^ k * 2) := Nat.div_div_eq_div_mul n (2 ^ k) 2
  have hdiv2' : n / 2 ^ k / 2 = n / 2 ^ (k + 1) := by
    rw [hdiv2, ← pow_succ]
  have hdiv : n / 2 ^ k = 2 * (n / 2 ^ (k + 1)) := by
    have := Nat.div_add_mod (n / 2 ^ k) 2
    rw [hdiv2'] at this
    omega
  have hrep : n = 2 * 2 ^ k * (n / 2 ^ (k + 1)) + n % 2 ^ k := by
    have := Nat.div_add_mod n (2 ^ k)
    rw [hdiv] at this
    -- this : 2^k * (2 * (n/2^{k+1})) + n%2^k = n
    have : (2 : ℕ) ^ k * (2 * (n / 2 ^ (k + 1))) = 2 * 2 ^ k * (n / 2 ^ (k + 1)) := by
      ring
    omega
  have hrep' : n = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ k := by
    rw [hpow]; convert hrep using 1 <;> ring
  have hlt : n % 2 ^ k < 2 ^ (k + 1) :=
    lt_trans (Nat.mod_lt n (Nat.two_pow_pos k))
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k))
  have hstd := Nat.div_add_mod n (2 ^ (k + 1))
  omega

lemma nat_div_two_pow_succ_of_odd {n k : ℕ} (h : n / 2 ^ (k + 1) % 2 = 1) :
    n / 2 ^ (k + 1) = 2 * (n / 2 ^ (k + 2)) + 1 := by
  have hdiv2 : n / 2 ^ (k + 1) / 2 = n / (2 ^ (k + 1) * 2) :=
    Nat.div_div_eq_div_mul n (2 ^ (k + 1)) 2
  have : 2 ^ (k + 1) * 2 = 2 ^ (k + 2) := (pow_succ (2 : ℕ) (k + 1)).symm
  rw [this] at hdiv2
  have := Nat.div_add_mod (n / 2 ^ (k + 1)) 2
  omega

lemma popc_sub_adjacent {n k : ℕ}
    (hoff : n / 2 ^ k % 2 = 0)
    (hon : n / 2 ^ (k + 1) % 2 = 1) :
    popc (n - 2 ^ k) = popc n := by
  have hb : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hmod : n % 2 ^ (k + 1) = n % 2 ^ k :=
    nat_mod_two_pow_succ_of_even_div hoff
  have hodd : n / 2 ^ (k + 1) = 2 * (n / 2 ^ (k + 2)) + 1 :=
    nat_div_two_pow_succ_of_odd hon
  have hpow1 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ' k
  have hpow2 : (2 : ℕ) ^ (k + 2) = 2 * 2 ^ (k + 1) := two_pow_succ' (k + 1)
  have hsplit := Nat.div_add_mod n (2 ^ (k + 1))
  have hn :
      n = 2 ^ (k + 2) * (n / 2 ^ (k + 2)) + 2 ^ (k + 1) + n % 2 ^ k := by
    have hmul : 2 ^ (k + 1) * (n / 2 ^ (k + 1)) =
        2 ^ (k + 1) * (2 * (n / 2 ^ (k + 2))) + 2 ^ (k + 1) := by
      rw [hodd, mul_add, mul_one]
    have hmul' : 2 ^ (k + 1) * (2 * (n / 2 ^ (k + 2))) =
        2 ^ (k + 2) * (n / 2 ^ (k + 2)) := by
      rw [← mul_assoc, ← pow_succ]
    rw [hmod] at hsplit
    omega
  have hsub :
      n - 2 ^ k = 2 ^ (k + 2) * (n / 2 ^ (k + 2)) + 2 ^ k + n % 2 ^ k := by
    have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := (two_pow_add_self k).symm
    omega
  have hlt1 : 2 ^ (k + 1) + n % 2 ^ k < 2 ^ (k + 2) := by
    have : 2 ^ (k + 1) + n % 2 ^ k < 2 ^ (k + 1) + 2 ^ k :=
      Nat.add_lt_add_left hb _
    have : (2 : ℕ) ^ (k + 1) + 2 ^ k < 2 ^ (k + 1) + 2 ^ (k + 1) :=
      Nat.add_lt_add_left
        (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k)) _
    have : (2 : ℕ) ^ (k + 1) + 2 ^ (k + 1) = 2 ^ (k + 2) := two_pow_add_self (k + 1)
    omega
  have hlt2 : 2 ^ k + n % 2 ^ k < 2 ^ (k + 2) := by
    have : 2 ^ k + n % 2 ^ k < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hb _
    have : (2 : ℕ) ^ k + 2 ^ k = 2 ^ (k + 1) := two_pow_add_self k
    have : (2 : ℕ) ^ (k + 1) < 2 ^ (k + 2) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self (k + 1))
    omega
  have hform1 :
      n = 2 ^ (k + 2) * (n / 2 ^ (k + 2)) + (2 ^ (k + 1) + n % 2 ^ k) := by
    omega
  have hform2 :
      n - 2 ^ k = 2 ^ (k + 2) * (n / 2 ^ (k + 2)) + (2 ^ k + n % 2 ^ k) := by
    omega
  have hlhs : popc (n - 2 ^ k) =
      popc (2 ^ (k + 2) * (n / 2 ^ (k + 2)) + (2 ^ k + n % 2 ^ k)) :=
    congrArg popc hform2
  have hrhs : popc n =
      popc (2 ^ (k + 2) * (n / 2 ^ (k + 2)) + (2 ^ (k + 1) + n % 2 ^ k)) :=
    congrArg popc hform1
  rw [hlhs, hrhs, popc_two_pow_mul_add hlt2, popc_two_pow_mul_add hlt1]
  have hb1 : n % 2 ^ k < 2 ^ (k + 1) :=
    lt_trans hb (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k))
  have hleft : popc (2 ^ (k + 1) + n % 2 ^ k) = 1 + popc (n % 2 ^ k) := by
    have : 2 ^ (k + 1) + n % 2 ^ k = 2 ^ (k + 1) * 1 + n % 2 ^ k := by ring
    rw [this, popc_two_pow_mul_add hb1, popc_one]
  have hright : popc (2 ^ k + n % 2 ^ k) = 1 + popc (n % 2 ^ k) := by
    have : 2 ^ k + n % 2 ^ k = 2 ^ k * 1 + n % 2 ^ k := by ring
    rw [this, popc_two_pow_mul_add hb, popc_one]
  omega




lemma popc_sum_six_pow {e1 e2 e3 e4 e5 e6 : ℕ}
    (h12 : e2 < e1) (h23 : e3 < e2) (h34 : e4 < e3) (h45 : e5 < e4) (h56 : e6 < e5) :
    popc (2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6) = 6 := by
  have hle5 : 2 ^ e5 + 2 ^ e6 < 2 ^ e4 := by
    have : 2 ^ e6 < 2 ^ e5 := two_pow_add_lt_of_lt h56
    have : 2 ^ e5 + 2 ^ e6 < 2 ^ e5 + 2 ^ e5 := Nat.add_lt_add_left this _
    have : 2 ^ e5 + 2 ^ e5 = 2 ^ (e5 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e5 + 1) ≤ 2 ^ e4 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle4 : 2 ^ e4 + 2 ^ e5 + 2 ^ e6 < 2 ^ e3 := by
    have : 2 ^ e4 + (2 ^ e5 + 2 ^ e6) < 2 ^ e4 + 2 ^ e4 :=
      Nat.add_lt_add_left hle5 _
    have : 2 ^ e4 + 2 ^ e4 = 2 ^ (e4 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e4 + 1) ≤ 2 ^ e3 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle3 : 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6 < 2 ^ e2 := by
    have : 2 ^ e3 + (2 ^ e4 + 2 ^ e5 + 2 ^ e6) < 2 ^ e3 + 2 ^ e3 :=
      Nat.add_lt_add_left hle4 _
    have : 2 ^ e3 + 2 ^ e3 = 2 ^ (e3 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e3 + 1) ≤ 2 ^ e2 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hle2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6 < 2 ^ e1 := by
    have : 2 ^ e2 + (2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6) < 2 ^ e2 + 2 ^ e2 :=
      Nat.add_lt_add_left hle3 _
    have : 2 ^ e2 + 2 ^ e2 = 2 ^ (e2 + 1) := by
      rw [← two_mul, ← two_pow_succ']
    have : 2 ^ (e2 + 1) ≤ 2 ^ e1 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hform1 : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6 =
      2 ^ e1 * 1 + (2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6) := by ring
  rw [hform1, popc_two_pow_mul_add hle2, popc_one]
  have hform2 : 2 ^ e2 + 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6 =
      2 ^ e2 * 1 + (2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6) := by ring
  rw [hform2, popc_two_pow_mul_add hle3, popc_one]
  have hform3 : 2 ^ e3 + 2 ^ e4 + 2 ^ e5 + 2 ^ e6 =
      2 ^ e3 * 1 + (2 ^ e4 + 2 ^ e5 + 2 ^ e6) := by ring
  rw [hform3, popc_two_pow_mul_add hle4, popc_one]
  have hform4 : 2 ^ e4 + 2 ^ e5 + 2 ^ e6 =
      2 ^ e4 * 1 + (2 ^ e5 + 2 ^ e6) := by ring
  rw [hform4, popc_two_pow_mul_add hle5, popc_one, popc_sum_two_pow_distinct h56]

lemma popc_adj_HIGH {e B : ℕ} (hB : 4 ≤ B) :
    popc (2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
      2 ^ (2 * e + 2 * B + 2) + 2 ^ (2 * e + 2 * B - 1) +
      2 ^ (2 * e + B) + 2 ^ (2 * e + B - 1)) = 6 :=
  popc_sum_six_pow
    (e1 := 2 * e + 3 * B + 2) (e2 := 2 * e + 3 * B - 1)
    (e3 := 2 * e + 2 * B + 2) (e4 := 2 * e + 2 * B - 1)
    (e5 := 2 * e + B) (e6 := 2 * e + B - 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)



lemma popc_add_two_pow_bit_off {n k : ℕ} (hoff : n / 2 ^ k % 2 = 0) :
    popc (n + 2 ^ k) = popc n + 1 := by
  have hb : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hmod : n % 2 ^ (k + 1) = n % 2 ^ k :=
    nat_mod_two_pow_succ_of_even_div hoff
  have hsplit := Nat.div_add_mod n (2 ^ (k + 1))
  have hn : n = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ k := by
    rw [hmod] at hsplit; omega
  have hadd : n + 2 ^ k = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + (2 ^ k + n % 2 ^ k) := by
    omega
  have hlt : n % 2 ^ k < 2 ^ (k + 1) :=
    lt_trans hb (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k))
  have hlt2 : 2 ^ k + n % 2 ^ k < 2 ^ (k + 1) := by
    have : 2 ^ k + n % 2 ^ k < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hb _
    have : (2 : ℕ) ^ k + 2 ^ k = 2 ^ (k + 1) := two_pow_add_self k
    omega
  have hlhs : popc (n + 2 ^ k) =
      popc (2 ^ (k + 1) * (n / 2 ^ (k + 1)) + (2 ^ k + n % 2 ^ k)) :=
    congrArg popc hadd
  have hrhs : popc n =
      popc (2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ k) :=
    congrArg popc hn
  rw [hlhs, hrhs, popc_two_pow_mul_add hlt2, popc_two_pow_mul_add hlt]
  have : 2 ^ k + n % 2 ^ k = 2 ^ k * 1 + n % 2 ^ k := by ring
  rw [this, popc_two_pow_mul_add hb, popc_one]
  omega

lemma adj_R_div_two {e : ℕ} (hodd : e % 2 = 1) :
    ((2 ^ (2 * e - 1) + 1) / 3) / 2 = (4 ^ (e - 1) - 1) / 3 := by
  rw [adj_Qt_eq hodd]
  have : (1 + 2 * ((4 ^ (e - 1) - 1) / 3)) / 2 = (4 ^ (e - 1) - 1) / 3 := by
    rw [Nat.add_comm, Nat.mul_add_div (by decide : (0 : ℕ) < 2)]
    simp
  exact this

lemma two_pow_mul_div_of_le {a b : ℕ} (h : b ≤ a) :
    (2 : ℕ) ^ a / 2 ^ b = 2 ^ (a - b) := by
  have : (2 : ℕ) ^ a = 2 ^ (a - b + b) := by congr 1; omega
  rw [this, pow_add, Nat.mul_div_left _ (Nat.two_pow_pos b)]



lemma testBit_R_odd {t j : ℕ} (hj : j % 2 = 1) :
    (((4 : ℕ) ^ t - 1) / 3).testBit j = false := by
  induction t with
  | zero =>
    simp
  | succ t ih =>
    have hR : ((4 : ℕ) ^ (t + 1) - 1) / 3 =
        ((4 : ℕ) ^ t - 1) / 3 + 4 ^ t := by
      have hdiv : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
      have hdiv' : 3 ∣ 4 ^ (t + 1) - 1 := three_dvd_four_pow_sub_one (t + 1)
      apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
      have lhs : 3 * (((4 : ℕ) ^ (t + 1) - 1) / 3) = 4 ^ (t + 1) - 1 :=
        Nat.mul_div_cancel' hdiv'
      have rhs : 3 * (((4 : ℕ) ^ t - 1) / 3 + 4 ^ t) =
          (4 ^ t - 1) + 3 * 4 ^ t := by
        have : 3 * (((4 : ℕ) ^ t - 1) / 3) = 4 ^ t - 1 := Nat.mul_div_cancel' hdiv
        omega
      have : 4 ^ (t + 1) = 4 * 4 ^ t := pow_succ' 4 t
      have hle : 1 ≤ (4 : ℕ) ^ t := Nat.one_le_pow _ _ (by decide)
      omega
    have h4 : (4 : ℕ) ^ t = 2 ^ (2 * t) := four_pow_eq t
    have hR' : ((4 : ℕ) ^ (t + 1) - 1) / 3 =
        ((4 : ℕ) ^ t - 1) / 3 + 2 ^ (2 * t) := by
      rw [hR, h4]
    rw [hR']
    have hRlt : ((4 : ℕ) ^ t - 1) / 3 < 2 ^ (2 * t) := by
      have hdiv : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
      have hmul : 3 * (((4 : ℕ) ^ t - 1) / 3) = 4 ^ t - 1 := Nat.mul_div_cancel' hdiv
      have hlt4 : ((4 : ℕ) ^ t - 1) / 3 < 4 ^ t := by
        have : 4 ^ t - 1 < 4 ^ t :=
          Nat.sub_lt (Nat.one_le_pow _ _ (by decide)) (by decide)
        omega
      rwa [← h4]
    by_cases hlt : j < 2 * t
    · have htb := Nat.testBit_two_pow_add_gt hlt (((4 : ℕ) ^ t - 1) / 3)
      rw [add_comm, htb, ih]
    · have hgt : 2 * t < j := by omega
      have hsumlt : ((4 : ℕ) ^ t - 1) / 3 + 2 ^ (2 * t) < 2 ^ j := by
        have : ((4 : ℕ) ^ t - 1) / 3 + 2 ^ (2 * t) < 2 ^ (2 * t) + 2 ^ (2 * t) :=
          Nat.add_lt_add_right hRlt _
        have : (2 : ℕ) ^ (2 * t) + 2 ^ (2 * t) = 2 ^ (2 * t + 1) := two_pow_add_self _
        have : (2 : ℕ) ^ (2 * t + 1) ≤ 2 ^ j :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
      exact Nat.testBit_lt_two_pow hsumlt

lemma adj_Qt_div_B_even {e B : ℕ} (hodd : e % 2 = 1) (hB : 2 ≤ B) (hBe : B % 2 = 0) :
    ((2 ^ (2 * e - 1) + 1) / 3) / 2 ^ B % 2 = 0 := by
  have hdiv2 : ((2 ^ (2 * e - 1) + 1) / 3) / 2 = (4 ^ (e - 1) - 1) / 3 :=
    adj_R_div_two hodd
  have : ((2 ^ (2 * e - 1) + 1) / 3) / 2 ^ B =
      (((2 ^ (2 * e - 1) + 1) / 3) / 2) / 2 ^ (B - 1) := by
    have hpow : (2 : ℕ) ^ B = 2 * 2 ^ (B - 1) := by
      calc (2 : ℕ) ^ B = 2 ^ (B - 1 + 1) := by congr 1; omega
        _ = 2 * 2 ^ (B - 1) := two_pow_succ' _
    rw [hpow, ← Nat.div_div_eq_div_mul]
  rw [this, hdiv2]
  have hj : (B - 1) % 2 = 1 := by omega
  have hbit : (((4 : ℕ) ^ (e - 1) - 1) / 3).testBit (B - 1) = false :=
    testBit_R_odd hj
  have : (((4 : ℕ) ^ (e - 1) - 1) / 3) / 2 ^ (B - 1) % 2 = 0 := by
    have := Nat.testBit_eq_decide_div_mod_eq (x := ((4 : ℕ) ^ (e - 1) - 1) / 3)
      (i := B - 1)
    -- testBit = decide ( / 2^i % 2 = 1)
    simpa [hbit] using this
  exact this

lemma popc_adj_LOW {e B : ℕ} (hodd : e % 2 = 1) (hB : 2 ≤ B) (hBe : B % 2 = 0) :
    popc ((2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B) = e + 1 := by
  have hoff : ((2 ^ (2 * e - 1) + 1) / 3) / 2 ^ B % 2 = 0 :=
    adj_Qt_div_B_even hodd hB hBe
  rw [popc_add_two_pow_bit_off hoff, popc_adj_Qt hodd]



lemma adj_Q_as_m {e B : ℕ} (he : 1 ≤ e) (hodd : e % 2 = 1) :
    (2 ^ (B + 1) + 2 ^ B + 1) * (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (2 ^ (B + 1) + 2 ^ B + 1) - 1) / 3 =
      (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3 := by
  simp [three_two_pow_add_one B]



lemma testBit_R_even {t i : ℕ} (hi : i < t) :
    (((4 : ℕ) ^ t - 1) / 3).testBit (2 * i) = true := by
  induction t with
  | zero => omega
  | succ t ih =>
    have h4 : (4 : ℕ) ^ t = 2 ^ (2 * t) := four_pow_eq t
    have hdiv : 3 ∣ 4 ^ t - 1 := three_dvd_four_pow_sub_one t
    have hdiv' : 3 ∣ 4 ^ (t + 1) - 1 := three_dvd_four_pow_sub_one (t + 1)
    have hR : ((4 : ℕ) ^ (t + 1) - 1) / 3 =
        ((4 : ℕ) ^ t - 1) / 3 + 2 ^ (2 * t) := by
      apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 3)
      have lhs : 3 * (((4 : ℕ) ^ (t + 1) - 1) / 3) = 4 ^ (t + 1) - 1 :=
        Nat.mul_div_cancel' hdiv'
      have rhs : 3 * (((4 : ℕ) ^ t - 1) / 3 + 2 ^ (2 * t)) =
          (4 ^ t - 1) + 3 * 4 ^ t := by
        have : 3 * (((4 : ℕ) ^ t - 1) / 3) = 4 ^ t - 1 := Nat.mul_div_cancel' hdiv
        rw [h4] at this ⊢
        omega
      have : (4 : ℕ) ^ (t + 1) = 4 * 4 ^ t := pow_succ' 4 t
      have hle : 1 ≤ (4 : ℕ) ^ t := Nat.one_le_pow _ _ (by decide)
      omega
    rw [hR]
    have hRlt : ((4 : ℕ) ^ t - 1) / 3 < 2 ^ (2 * t) := by
      have hmul : 3 * (((4 : ℕ) ^ t - 1) / 3) = 4 ^ t - 1 := Nat.mul_div_cancel' hdiv
      have hlt4 : ((4 : ℕ) ^ t - 1) / 3 < 4 ^ t := by
        have : 4 ^ t - 1 < 4 ^ t :=
          Nat.sub_lt (Nat.one_le_pow _ _ (by decide)) (by decide)
        omega
      rwa [← h4]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
    · have htb := Nat.testBit_two_pow_add_gt (by omega : 2 * i < 2 * t)
        (((4 : ℕ) ^ t - 1) / 3)
      rw [add_comm, htb, ih hlt]
    · have hi2 : 2 * i = 2 * t := by omega
      have htb := Nat.testBit_two_pow_add_eq (((4 : ℕ) ^ t - 1) / 3) (2 * t)
      have hfalse : (((4 : ℕ) ^ t - 1) / 3).testBit (2 * t) = false :=
        Nat.testBit_lt_two_pow hRlt
      rw [hi2, add_comm, htb, hfalse]
      decide

lemma adj_Qt_testBit_odd {e k : ℕ} (hodd : e % 2 = 1)
    (hk : k % 2 = 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * e - 3) :
    ((2 ^ (2 * e - 1) + 1) / 3).testBit k = true := by
  have hQt : (2 ^ (2 * e - 1) + 1) / 3 = 1 + 2 * ((4 ^ (e - 1) - 1) / 3) :=
    adj_Qt_eq hodd
  rw [hQt]
  have hk0 : k = (k - 1) + 1 := by omega
  have hsucc : (1 + 2 * ((4 ^ (e - 1) - 1) / 3)).testBit k =
      ((4 ^ (e - 1) - 1) / 3).testBit (k - 1) := by
    have hdiv : (1 + 2 * ((4 ^ (e - 1) - 1) / 3)) / 2 = (4 ^ (e - 1) - 1) / 3 := by
      rw [Nat.add_comm, Nat.mul_add_div (by decide : (0 : ℕ) < 2)]
      simp
    rw [hk0, Nat.testBit_succ, hdiv]
    simp
  rw [hsucc]
  have hke : (k - 1) % 2 = 0 := by omega
  have : k - 1 = 2 * ((k - 1) / 2) := by omega
  rw [this]
  apply testBit_R_even
  have : k ≤ 2 * e - 3 := hk2
  omega

lemma testBit_iff_div_mod {n i : ℕ} :
    n.testBit i = true ↔ n / 2 ^ i % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp

lemma testBit_iff_div_mod_false {n i : ℕ} :
    n.testBit i = false ↔ n / 2 ^ i % 2 = 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp



lemma popc_sub_two_pow_bit_on {n k : ℕ}
    (hon : n / 2 ^ k % 2 = 1) :
    popc (n - 2 ^ k) = popc n - 1 := by
  have hge : 2 ^ k ≤ n := by
    have hne : n / 2 ^ k ≠ 0 := by
      intro h0
      rw [h0] at hon
      simp at hon
    have : 1 ≤ n / 2 ^ k := Nat.pos_of_ne_zero hne
    have : 2 ^ k * 1 ≤ 2 ^ k * (n / 2 ^ k) := Nat.mul_le_mul_left _ this
    have : 2 ^ k * (n / 2 ^ k) ≤ n := Nat.mul_div_le n (2 ^ k)
    omega
  have hb : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hdiv : n / 2 ^ k = 2 * (n / 2 ^ (k + 1)) + 1 := by
    have hdiv2 : n / 2 ^ k / 2 = n / (2 ^ k * 2) :=
      Nat.div_div_eq_div_mul n (2 ^ k) 2
    have hpowk : (2 : ℕ) ^ k * 2 = 2 ^ (k + 1) := (pow_succ (2 : ℕ) k).symm
    rw [hpowk] at hdiv2
    have hmod2 := Nat.div_add_mod (n / 2 ^ k) 2
    rw [hdiv2] at hmod2
    omega
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := two_pow_succ' k
  have hn : n = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + 2 ^ k + n % 2 ^ k := by
    have := Nat.div_add_mod n (2 ^ k)
    have : 2 ^ k * (n / 2 ^ k) = 2 ^ k * (2 * (n / 2 ^ (k + 1)) + 1) := by rw [hdiv]
    have : 2 ^ k * (2 * (n / 2 ^ (k + 1)) + 1) =
        2 ^ (k + 1) * (n / 2 ^ (k + 1)) + 2 ^ k := by
      rw [mul_add, mul_one, ← mul_assoc, ← pow_succ]
    omega
  have hsub : n - 2 ^ k = 2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ k := by
    omega
  have hlt : 2 ^ k + n % 2 ^ k < 2 ^ (k + 1) := by
    have : 2 ^ k + n % 2 ^ k < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hb _
    have : (2 : ℕ) ^ k + 2 ^ k = 2 ^ (k + 1) := two_pow_add_self k
    omega
  have hltb : n % 2 ^ k < 2 ^ (k + 1) :=
    lt_trans hb (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k))
  have hlhs : popc (n - 2 ^ k) =
      popc (2 ^ (k + 1) * (n / 2 ^ (k + 1)) + n % 2 ^ k) :=
    congrArg popc hsub
  have hrhs : popc n =
      popc (2 ^ (k + 1) * (n / 2 ^ (k + 1)) + (2 ^ k + n % 2 ^ k)) :=
    congrArg popc (by omega)
  rw [hlhs, hrhs, popc_two_pow_mul_add hltb, popc_two_pow_mul_add hlt]
  have : 2 ^ k + n % 2 ^ k = 2 ^ k * 1 + n % 2 ^ k := by ring
  rw [this, popc_two_pow_mul_add hb, popc_one]
  omega



lemma testBit_add_two_pow_of_bit_off {n i j : ℕ}
    (hoff : n / 2 ^ i % 2 = 0) :
    (n + 2 ^ i).testBit j = if j = i then true else n.testBit j := by
  have hmod : n % 2 ^ (i + 1) = n % 2 ^ i :=
    nat_mod_two_pow_succ_of_even_div hoff
  have hn : n = 2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i := by
    have := Nat.div_add_mod n (2 ^ (i + 1))
    rw [hmod] at this; omega
  have hadd : n + 2 ^ i = 2 ^ (i + 1) * (n / 2 ^ (i + 1)) + 2 ^ i + n % 2 ^ i := by
    omega
  have hb : n % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  by_cases hji : j = i
  · have htrue : (n + 2 ^ i).testBit i = true := by
      have htb := Nat.testBit_two_pow_add_eq
        (2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i) i
      have hform : n + 2 ^ i =
          2 ^ i + (2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i) := by
        omega
      have hoff' : (2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i).testBit i =
          false := by
        have : 2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i = n := by omega
        rw [this]
        exact testBit_iff_div_mod_false.mpr hoff
      rw [hform, htb, hoff']
      decide
    simp [hji, htrue]
  · simp [hji]
    by_cases hlt : j < i
    · have h1 := Nat.testBit_two_pow_add_gt hlt (2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i)
      have h2 := Nat.testBit_two_pow_add_gt hlt (2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i)
      -- n + 2^i = 2^i + (2^{i+1}*c + b), n = 2^{i+1}*c + b
      have hf1 : n + 2 ^ i = 2 ^ i + (2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i) := by
        omega
      have hf2 : n = 2 ^ (i + 1) * (n / 2 ^ (i + 1)) + n % 2 ^ i := hn
      rw [hf1, h1, ← hf2]
    · have hgt : i < j := by omega
      -- both n and n+2^i have the same bits above i
      -- n = 2^{i+1}*c + b, n+2^i = 2^{i+1}*c + 2^i + b
      -- testBit (2^{i+1}*c + x) j for j > i equals testBit c (j-i-1)
      have hj : j = (j - (i + 1)) + (i + 1) := by omega
      have hshift1 : n.testBit j = (n / 2 ^ (i + 1)).testBit (j - (i + 1)) := by
        rw [hj, Nat.testBit_add]
        simp
      have hshift2 : (n + 2 ^ i).testBit j =
          ((n + 2 ^ i) / 2 ^ (i + 1)).testBit (j - (i + 1)) := by
        rw [hj, Nat.testBit_add]
        simp
      have hdivs : (n + 2 ^ i) / 2 ^ (i + 1) = n / 2 ^ (i + 1) := by
        have : n + 2 ^ i = 2 ^ (i + 1) * (n / 2 ^ (i + 1)) + (2 ^ i + n % 2 ^ i) := by
          omega
        have hlt2 : 2 ^ i + n % 2 ^ i < 2 ^ (i + 1) := by
          have : 2 ^ i + n % 2 ^ i < 2 ^ i + 2 ^ i := Nat.add_lt_add_left hb _
          have : (2 : ℕ) ^ i + 2 ^ i = 2 ^ (i + 1) := two_pow_add_self i
          omega
        rw [this, Nat.mul_add_div (Nat.two_pow_pos (i + 1)),
          Nat.div_eq_of_lt hlt2, add_zero]
      rw [hshift2, hdivs, hshift1]



lemma adj_LOW_testBit {e B k : ℕ} (hodd : e % 2 = 1)
    (hB : 2 ≤ B) (hBe : B % 2 = 0) :
    ((2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B).testBit k =
      if k = B then true else ((2 ^ (2 * e - 1) + 1) / 3).testBit k :=
  testBit_add_two_pow_of_bit_off (adj_Qt_div_B_even hodd hB hBe)

lemma adj_LOW_has_odd {e B k : ℕ} (hodd : e % 2 = 1)
    (hB : 2 ≤ B) (hBe : B % 2 = 0)
    (hk : k % 2 = 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * e - 3) :
    ((2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B) / 2 ^ k % 2 = 1 := by
  have hbit : ((2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B).testBit k = true := by
    rw [adj_LOW_testBit hodd hB hBe]
    have hne : k ≠ B := by intro h; subst h; omega
    simp [hne]
    exact adj_Qt_testBit_odd hodd hk hk1 hk2
  exact testBit_iff_div_mod.mp hbit

lemma adj_LOW_off_even {e B k : ℕ} (hodd : e % 2 = 1)
    (hB : 2 ≤ B) (hBe : B % 2 = 0)
    (hk : k % 2 = 0) (hkne : k ≠ B) (hk0 : k ≠ 0) :
    ((2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B) / 2 ^ k % 2 = 0 := by
  have hbit : ((2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B).testBit k = false := by
    rw [adj_LOW_testBit hodd hB hBe]
    simp [hkne]
    have hQ : (2 ^ (2 * e - 1) + 1) / 3 = 1 + 2 * ((4 ^ (e - 1) - 1) / 3) :=
      adj_Qt_eq hodd
    rw [hQ]
    have hk0' : k = (k - 1) + 1 := by omega
    have hdiv : (1 + 2 * ((4 ^ (e - 1) - 1) / 3)) / 2 = (4 ^ (e - 1) - 1) / 3 := by
      rw [Nat.add_comm, Nat.mul_add_div (by decide : (0 : ℕ) < 2)]
      simp
    have hsucc : (1 + 2 * ((4 ^ (e - 1) - 1) / 3)).testBit k =
        ((4 ^ (e - 1) - 1) / 3).testBit (k - 1) := by
      rw [hk0', Nat.testBit_succ, hdiv]; simp
    rw [hsucc]
    exact testBit_R_odd (by omega : (k - 1) % 2 = 1)
  exact testBit_iff_div_mod_false.mp hbit



lemma adj_far_bounds {e B : ℕ} (hfar : 2 * B + 5 ≤ e) (hB : 4 ≤ B) :
    1 ≤ e + B ∧ e + B ≤ 2 * e - 3 ∧
      1 ≤ e + 2 * B + 2 ∧ e + 2 * B + 2 ≤ 2 * e - 3 ∧
      1 ≤ e ∧ e ≤ 2 * e - 3 ∧
      1 ≤ e + B + 2 ∧ e + B + 2 ≤ 2 * e - 3 ∧
      1 ≤ e + 2 * B ∧ e + 2 * B ≤ 2 * e - 3 ∧
      e + B ≠ e + 2 * B + 2 := by omega

lemma two_pow_le_of_bit_on {n k : ℕ} (h : n / 2 ^ k % 2 = 1) : 2 ^ k ≤ n := by
  have hne : n / 2 ^ k ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have : 1 ≤ n / 2 ^ k := Nat.pos_of_ne_zero hne
  have : 2 ^ k * 1 ≤ 2 ^ k * (n / 2 ^ k) := Nat.mul_le_mul_left _ this
  have : 2 ^ k * (n / 2 ^ k) ≤ n := Nat.mul_div_le n (2 ^ k)
  omega

lemma testBit_sub_two_pow_bit_on {n i j : ℕ}
    (hon : n / 2 ^ i % 2 = 1) (hne : j ≠ i) :
    (n - 2 ^ i).testBit j = n.testBit j := by
  have hge : 2 ^ i ≤ n := two_pow_le_of_bit_on hon
  have hadd : (n - 2 ^ i) + 2 ^ i = n := Nat.sub_add_cancel hge
  have hoff : (n - 2 ^ i) / 2 ^ i % 2 = 0 := by
    have htb := Nat.testBit_two_pow_add_eq (n - 2 ^ i) i
    have htrue : n.testBit i = true := testBit_iff_div_mod.mpr hon
    have : (!(n - 2 ^ i).testBit i) = true := by
      rw [← htb, add_comm, hadd]
      exact htrue
    have hfalse : (n - 2 ^ i).testBit i = false := by
      cases h : (n - 2 ^ i).testBit i
      · rfl
      · simp [h] at this
    exact testBit_iff_div_mod_false.mp hfalse
  have htb := testBit_add_two_pow_of_bit_off (n := n - 2 ^ i) (i := i) (j := j) hoff
  rw [hadd] at htb
  simpa [hne] using htb.symm



lemma div_mod_sub_two_pow_of_ne {n i j : ℕ}
    (hon : n / 2 ^ i % 2 = 1) (hne : j ≠ i) :
    (n - 2 ^ i) / 2 ^ j % 2 = n / 2 ^ j % 2 := by
  have htb := testBit_sub_two_pow_bit_on hon hne
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h0 | h1
  · have hf : n.testBit j = false := testBit_iff_div_mod_false.mpr h0
    have : (n - 2 ^ i).testBit j = false := by rw [htb, hf]
    have := testBit_iff_div_mod_false.mp this
    omega
  · have ht : n.testBit j = true := testBit_iff_div_mod.mpr h1
    have : (n - 2 ^ i).testBit j = true := by rw [htb, ht]
    have := testBit_iff_div_mod.mp this
    omega

lemma testBit_sub_adjacent {n k j : ℕ}
    (hoff : n / 2 ^ k % 2 = 0)
    (hon : n / 2 ^ (k + 1) % 2 = 1)
    (hne0 : j ≠ k) (hne1 : j ≠ k + 1) :
    (n - 2 ^ k).testBit j = n.testBit j := by
  have hge : 2 ^ (k + 1) ≤ n := two_pow_le_of_bit_on hon
  have hle : (2 : ℕ) ^ k ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
  have hrewrite : n - 2 ^ k = n - 2 ^ (k + 1) + 2 ^ k := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := (two_pow_add_self k).symm
    omega
  have hsub : (n - 2 ^ (k + 1)).testBit j = n.testBit j :=
    testBit_sub_two_pow_bit_on hon hne1
  have hoff' : (n - 2 ^ (k + 1)) / 2 ^ k % 2 = 0 := by
    have hne : k ≠ k + 1 := Nat.ne_of_lt (Nat.lt_succ_self k)
    have htbk := testBit_sub_two_pow_bit_on (n := n) (i := k + 1) (j := k)
      hon hne
    have hkf : n.testBit k = false := testBit_iff_div_mod_false.mpr hoff
    have : (n - 2 ^ (k + 1)).testBit k = false := by rw [htbk, hkf]
    exact testBit_iff_div_mod_false.mp this
  have hadd :=
    testBit_add_two_pow_of_bit_off (n := n - 2 ^ (k + 1)) (i := k) (j := j) hoff'
  rw [hrewrite, hadd]
  simp [hne0]
  exact hsub

lemma div_mod_sub_adjacent {n k j : ℕ}
    (hoff : n / 2 ^ k % 2 = 0)
    (hon : n / 2 ^ (k + 1) % 2 = 1)
    (hne0 : j ≠ k) (hne1 : j ≠ k + 1) :
    (n - 2 ^ k) / 2 ^ j % 2 = n / 2 ^ j % 2 := by
  have htb := testBit_sub_adjacent hoff hon hne0 hne1
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h0 | h1
  · have hf : n.testBit j = false := testBit_iff_div_mod_false.mpr h0
    have : (n - 2 ^ k).testBit j = false := by rw [htb, hf]
    have := testBit_iff_div_mod_false.mp this
    omega
  · have ht : n.testBit j = true := testBit_iff_div_mod.mpr h1
    have : (n - 2 ^ k).testBit j = true := by rw [htb, ht]
    have := testBit_iff_div_mod.mp this
    omega

lemma adj_HIGH_factor {e B : ℕ} (hB : 1 ≤ B) :
    2 ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
      2 ^ (2 * e + 2 * B + 2) + 2 ^ (2 * e + 2 * B - 1) +
      2 ^ (2 * e + B) + 2 ^ (2 * e + B - 1) =
    2 ^ (2 * e + B - 1) *
      (2 ^ (2 * B + 3) + 2 ^ (2 * B) + 2 ^ (B + 3) + 2 ^ B + 2 + 1) := by
  have k1 : (2 : ℕ) ^ (2 * e + 3 * B + 2) =
      2 ^ (2 * e + B - 1) * 2 ^ (2 * B + 3) := by
    have : 2 * e + 3 * B + 2 = (2 * e + B - 1) + (2 * B + 3) := by omega
    rw [this, pow_add]
  have k2 : (2 : ℕ) ^ (2 * e + 3 * B - 1) =
      2 ^ (2 * e + B - 1) * 2 ^ (2 * B) := by
    have : 2 * e + 3 * B - 1 = (2 * e + B - 1) + 2 * B := by omega
    rw [this, pow_add]
  have k3 : (2 : ℕ) ^ (2 * e + 2 * B + 2) =
      2 ^ (2 * e + B - 1) * 2 ^ (B + 3) := by
    have : 2 * e + 2 * B + 2 = (2 * e + B - 1) + (B + 3) := by omega
    rw [this, pow_add]
  have k4 : (2 : ℕ) ^ (2 * e + 2 * B - 1) =
      2 ^ (2 * e + B - 1) * 2 ^ B := by
    have : 2 * e + 2 * B - 1 = (2 * e + B - 1) + B := by omega
    rw [this, pow_add]
  have k5 : (2 : ℕ) ^ (2 * e + B) =
      2 ^ (2 * e + B - 1) * 2 := by
    calc (2 : ℕ) ^ (2 * e + B)
        = 2 ^ ((2 * e + B - 1) + 1) := by congr 1; omega
      _ = 2 ^ (2 * e + B - 1) * 2 ^ 1 := pow_add _ _ _
      _ = 2 ^ (2 * e + B - 1) * 2 := by rw [pow_one]
  have k6 : (2 : ℕ) ^ (2 * e + B - 1) =
      2 ^ (2 * e + B - 1) * 1 := by ring
  rw [k1, k2, k3, k4, k5, k6]; ring

lemma adj_MID_le_LOW {e B : ℕ} (hodd : e % 2 = 1) (hB : 4 ≤ B)
    (hfar : 2 * B + 5 ≤ e) :
    2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + B + 1) +
      2 ^ (e + B) + 2 ^ (e - 1) ≤
    (2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B := by
  have hle1 : (2 : ℕ) ^ (e + B + 1) ≤ 2 ^ (e + 2 * B - 2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hle2 : (2 : ℕ) ^ (e + B) ≤ 2 ^ (e + 2 * B - 3) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hle3 : (2 : ℕ) ^ (e - 1) ≤ 2 ^ (e + 2 * B - 4) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hMID_le :
      2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + B + 1) +
        2 ^ (e + B) + 2 ^ (e - 1) ≤
      2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + 2 * B - 2) +
        2 ^ (e + 2 * B - 3) + 2 ^ (e + 2 * B - 4) :=
    Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add le_rfl le_rfl) hle1) hle2)
      hle3
  have p6 : (2 : ℕ) ^ (e + 2 * B + 2) = 2 ^ 6 * 2 ^ (e + 2 * B - 4) := by
    have : e + 2 * B + 2 = 6 + (e + 2 * B - 4) := by omega
    rw [this, pow_add]
  have p3 : (2 : ℕ) ^ (e + 2 * B - 1) = 2 ^ 3 * 2 ^ (e + 2 * B - 4) := by
    have : e + 2 * B - 1 = 3 + (e + 2 * B - 4) := by omega
    rw [this, pow_add]
  have p2 : (2 : ℕ) ^ (e + 2 * B - 2) = 2 ^ 2 * 2 ^ (e + 2 * B - 4) := by
    have : e + 2 * B - 2 = 2 + (e + 2 * B - 4) := by omega
    rw [this, pow_add]
  have p1 : (2 : ℕ) ^ (e + 2 * B - 3) = 2 * 2 ^ (e + 2 * B - 4) := by
    have : e + 2 * B - 3 = 1 + (e + 2 * B - 4) := by omega
    rw [this, pow_add, pow_one]
  have h64 : (2 : ℕ) ^ 6 = 64 := by decide
  have h8 : (2 : ℕ) ^ 3 = 8 := by decide
  have h4 : (2 : ℕ) ^ 2 = 4 := by decide
  have hbase :
      2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + 2 * B - 2) +
        2 ^ (e + 2 * B - 3) + 2 ^ (e + 2 * B - 4) =
      79 * 2 ^ (e + 2 * B - 4) := by
    rw [p6, p3, p2, p1, h64, h8, h4]; ring
  have hexp : (2 : ℕ) ^ (2 * e - 1) =
      2 ^ (e - 2 * B + 3) * 2 ^ (e + 2 * B - 4) := by
    have : 2 * e - 1 = (e - 2 * B + 3) + (e + 2 * B - 4) := by omega
    rw [this, pow_add]
  have h256 : (256 : ℕ) ≤ 2 ^ (e - 2 * B + 3) := by
    have : (2 : ℕ) ^ 8 ≤ 2 ^ (e - 2 * B + 3) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have : (2 : ℕ) ^ 8 = 256 := by decide
    omega
  have h237 : 237 * 2 ^ (e + 2 * B - 4) ≤ 2 ^ (2 * e - 1) + 1 := by
    have : 237 * 2 ^ (e + 2 * B - 4) ≤ 256 * 2 ^ (e + 2 * B - 4) :=
      Nat.mul_le_mul_right _ (by decide : (237 : ℕ) ≤ 256)
    have : 256 * 2 ^ (e + 2 * B - 4) ≤
        2 ^ (e - 2 * B + 3) * 2 ^ (e + 2 * B - 4) :=
      Nat.mul_le_mul_right _ h256
    omega
  have hdiv : 3 ∣ (2 : ℕ) ^ (2 * e - 1) + 1 := adj_three_dvd_Qt hodd
  have hmul : 3 * (((2 : ℕ) ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have h79 : 79 * 2 ^ (e + 2 * B - 4) ≤ ((2 : ℕ) ^ (2 * e - 1) + 1) / 3 := by
    have : 3 * (79 * 2 ^ (e + 2 * B - 4)) ≤
        3 * (((2 : ℕ) ^ (2 * e - 1) + 1) / 3) := by
      have : 3 * (79 * 2 ^ (e + 2 * B - 4)) = 237 * 2 ^ (e + 2 * B - 4) := by
        ring
      omega
    exact Nat.le_of_mul_le_mul_left this (by decide : (0 : ℕ) < 3)
  have h79' : 79 * 2 ^ (e + 2 * B - 4) ≤
      ((2 : ℕ) ^ (2 * e - 1) + 1) / 3 + 2 ^ B :=
    le_trans h79 (Nat.le_add_right _ _)
  calc
    2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + B + 1) +
        2 ^ (e + B) + 2 ^ (e - 1) ≤
        2 ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + 2 * B - 2) +
          2 ^ (e + 2 * B - 3) + 2 ^ (e + 2 * B - 4) := hMID_le
    _ = 79 * 2 ^ (e + 2 * B - 4) := hbase
    _ ≤ ((2 : ℕ) ^ (2 * e - 1) + 1) / 3 + 2 ^ B := h79'

lemma adj_LOW_lt {e B : ℕ} (hodd : e % 2 = 1) (hB : 4 ≤ B)
    (hfar : 2 * B + 5 ≤ e) :
    ((2 : ℕ) ^ (2 * e - 1) + 1) / 3 + 2 ^ B < 2 ^ (2 * e - 1) := by
  have hdiv : 3 ∣ (2 : ℕ) ^ (2 * e - 1) + 1 := adj_three_dvd_Qt hodd
  have hmul : 3 * (((2 : ℕ) ^ (2 * e - 1) + 1) / 3) = 2 ^ (2 * e - 1) + 1 :=
    Nat.mul_div_cancel' hdiv
  have hgoal : 3 * (((2 : ℕ) ^ (2 * e - 1) + 1) / 3 + 2 ^ B) <
      3 * 2 ^ (2 * e - 1) := by
    rw [mul_add, hmul]
    have : 1 + 3 * (2 : ℕ) ^ B < 2 * 2 ^ (2 * e - 1) := by
      have hle : 3 * (2 : ℕ) ^ B + 1 ≤ 2 ^ (B + 2) := by
        have h4 : (2 : ℕ) ^ (B + 2) = 4 * 2 ^ B := by
          have : B + 2 = 2 + B := by omega
          rw [this, pow_add]
          have : (2 : ℕ) ^ 2 = 4 := rfl
          rw [this]
        have : 1 ≤ (2 : ℕ) ^ B := Nat.one_le_two_pow
        omega
      have hlt : (2 : ℕ) ^ (B + 2) < 2 ^ (2 * e) :=
        Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
      have h2e : (2 : ℕ) * 2 ^ (2 * e - 1) = 2 ^ (2 * e) := by
        have hexp : 2 * e = (2 * e - 1) + 1 := by omega
        calc (2 : ℕ) * 2 ^ (2 * e - 1)
            = 2 ^ 1 * 2 ^ (2 * e - 1) := by rfl
          _ = 2 ^ (1 + (2 * e - 1)) := (pow_add _ _ _).symm
          _ = 2 ^ (2 * e) := by congr 1; omega
      have hle' : 1 + 3 * (2 : ℕ) ^ B ≤ 2 ^ (B + 2) := by
        have : 1 + 3 * (2 : ℕ) ^ B = 3 * 2 ^ B + 1 := by ring
        omega
      exact lt_of_le_of_lt hle' (h2e ▸ hlt)
    omega
  exact Nat.lt_of_mul_lt_mul_left hgoal

lemma adj_LOW_lt_HIGH {e B : ℕ} (hodd : e % 2 = 1) (hB : 4 ≤ B)
    (hfar : 2 * B + 5 ≤ e) :
    ((2 : ℕ) ^ (2 * e - 1) + 1) / 3 + 2 ^ B < 2 ^ (2 * e + B - 1) := by
  have h1 := adj_LOW_lt hodd hB hfar
  have h2 : (2 : ℕ) ^ (2 * e - 1) ≤ 2 ^ (2 * e + B - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  omega

lemma popc_adj_Q_far {e B : ℕ} (hodd : e % 2 = 1) (hB : 4 ≤ B)
    (hBe : B % 2 = 0) (hfar : 2 * B + 5 ≤ e) :
    popc ((3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
      (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3) = e + 5 := by
  set LOW := ((2 : ℕ) ^ (2 * e - 1) + 1) / 3 + 2 ^ B
  set HIGH :=
    (2 : ℕ) ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
      2 ^ (2 * e + 2 * B + 2) + 2 ^ (2 * e + 2 * B - 1) +
      2 ^ (2 * e + B) + 2 ^ (2 * e + B - 1)
  set MID :=
    (2 : ℕ) ^ (e + 2 * B + 2) + 2 ^ (e + 2 * B - 1) + 2 ^ (e + B + 1) +
      2 ^ (e + B) + 2 ^ (e - 1)
  have hQ0 := adj_Q_decomp (e := e) (B := B) (by omega) hodd
  have hgroup :
      (2 : ℕ) ^ (2 * e + 3 * B + 2) + 2 ^ (2 * e + 3 * B - 1) +
          2 ^ (2 * e + 2 * B + 2) + 2 ^ (2 * e + 2 * B - 1) +
          2 ^ (2 * e + B) + 2 ^ (2 * e + B - 1) +
          (2 ^ (2 * e - 1) + 1) / 3 + 2 ^ B =
        HIGH + LOW := by
    simp [HIGH, LOW]; ring
  have hMID := adj_MID_le_LOW hodd hB hfar
  have hQ : (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
      (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3 = HIGH + (LOW - MID) := by
    have h1 : (3 * 2 ^ B + 1) * (2 ^ e * (3 * 2 ^ B + 1) - 1) *
        (2 ^ (e - 1) * (3 * 2 ^ B + 1) - 1) / 3 =
        HIGH + LOW - MID := by
      rw [hQ0, ← hgroup]
    rw [h1, Nat.add_sub_assoc hMID]

  have hk1od : (e + B) % 2 = 1 := by omega
  have hk2od : (e + 2 * B + 2) % 2 = 1 := by omega
  have hkeod : e % 2 = 1 := hodd
  have hk4od : (e + B + 2) % 2 = 1 := by omega
  have hk6od : (e + 2 * B) % 2 = 1 := by omega
  have hk3ev : (e - 1) % 2 = 0 := by omega
  have hk5ev : (e + B + 1) % 2 = 0 := by omega
  have hk7ev : (e + 2 * B - 1) % 2 = 0 := by omega
  have hB2 : 2 ≤ B := by omega
  have L_k1 : LOW / 2 ^ (e + B) % 2 = 1 := by
    simpa [LOW] using
      adj_LOW_has_odd hodd hB2 hBe hk1od (by omega) (by omega)
  have L_k2 : LOW / 2 ^ (e + 2 * B + 2) % 2 = 1 := by
    simpa [LOW] using
      adj_LOW_has_odd hodd hB2 hBe hk2od (by omega) (by omega)
  have L_e : LOW / 2 ^ e % 2 = 1 := by
    simpa [LOW] using
      adj_LOW_has_odd hodd hB2 hBe hkeod (by omega) (by omega)
  have L_eb2 : LOW / 2 ^ (e + B + 2) % 2 = 1 := by
    simpa [LOW] using
      adj_LOW_has_odd hodd hB2 hBe hk4od (by omega) (by omega)
  have L_e2B : LOW / 2 ^ (e + 2 * B) % 2 = 1 := by
    simpa [LOW] using
      adj_LOW_has_odd hodd hB2 hBe hk6od (by omega) (by omega)
  have L_em1 : LOW / 2 ^ (e - 1) % 2 = 0 := by
    have hkne : e - 1 ≠ B := by omega
    have hk0 : e - 1 ≠ 0 := by omega
    simpa [LOW] using adj_LOW_off_even hodd hB2 hBe hk3ev hkne hk0
  have L_eb1 : LOW / 2 ^ (e + B + 1) % 2 = 0 := by
    have hkne : e + B + 1 ≠ B := by omega
    have hk0 : e + B + 1 ≠ 0 := by omega
    simpa [LOW] using adj_LOW_off_even hodd hB2 hBe hk5ev hkne hk0
  have L_e2Bm1 : LOW / 2 ^ (e + 2 * B - 1) % 2 = 0 := by
    have hkne : e + 2 * B - 1 ≠ B := by omega
    have hk0 : e + 2 * B - 1 ≠ 0 := by omega
    simpa [LOW] using adj_LOW_off_even hodd hB2 hBe hk7ev hkne hk0

  set L1 := LOW - 2 ^ (e + B)
  set L2 := L1 - 2 ^ (e + 2 * B + 2)
  set L3 := L2 - 2 ^ (e - 1)
  set L4 := L3 - 2 ^ (e + B + 1)
  set L5 := L4 - 2 ^ (e + 2 * B - 1)

  have hne_k2k1 : e + 2 * B + 2 ≠ e + B := by omega
  have L1_k2 : L1 / 2 ^ (e + 2 * B + 2) % 2 = 1 := by
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e + 2 * B + 2) L_k1 hne_k2k1
    simpa [L1] using this ▸ L_k2
  have hne_em1k1 : e - 1 ≠ e + B := by omega
  have hne_em1k2 : e - 1 ≠ e + 2 * B + 2 := by omega
  have hne_ek1 : e ≠ e + B := by omega
  have hne_ek2 : e ≠ e + 2 * B + 2 := by omega
  have L1_em1 : L1 / 2 ^ (e - 1) % 2 = 0 := by
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e - 1) L_k1 hne_em1k1
    simpa [L1] using this ▸ L_em1
  have L1_e : L1 / 2 ^ e % 2 = 1 := by
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e) L_k1 hne_ek1
    simpa [L1] using this ▸ L_e
  have L2_em1 : L2 / 2 ^ (e - 1) % 2 = 0 := by
    have := div_mod_sub_two_pow_of_ne (n := L1) (i := e + 2 * B + 2)
      (j := e - 1) L1_k2 hne_em1k2
    simpa [L2] using this ▸ L1_em1
  have L2_e : L2 / 2 ^ e % 2 = 1 := by
    have := div_mod_sub_two_pow_of_ne (n := L1) (i := e + 2 * B + 2)
      (j := e) L1_k2 hne_ek2
    simpa [L2] using this ▸ L1_e

  have hne_eb1em1 : e + B + 1 ≠ e - 1 := by omega
  have hne_eb1e : e + B + 1 ≠ e := by omega
  have hne_eb2em1 : e + B + 2 ≠ e - 1 := by omega
  have hne_eb2e : e + B + 2 ≠ e := by omega
  have L1_eb1 : L1 / 2 ^ (e + B + 1) % 2 = 0 := by
    have hne : e + B + 1 ≠ e + B := by omega
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e + B + 1) L_k1 hne
    simpa [L1] using this ▸ L_eb1
  have L2_eb1 : L2 / 2 ^ (e + B + 1) % 2 = 0 := by
    have hne : e + B + 1 ≠ e + 2 * B + 2 := by omega
    have := div_mod_sub_two_pow_of_ne (n := L1) (i := e + 2 * B + 2)
      (j := e + B + 1) L1_k2 hne
    simpa [L2] using this ▸ L1_eb1
  have L1_eb2 : L1 / 2 ^ (e + B + 2) % 2 = 1 := by
    have hne : e + B + 2 ≠ e + B := by omega
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e + B + 2) L_k1 hne
    simpa [L1] using this ▸ L_eb2
  have L2_eb2 : L2 / 2 ^ (e + B + 2) % 2 = 1 := by
    have hne : e + B + 2 ≠ e + 2 * B + 2 := by omega
    have := div_mod_sub_two_pow_of_ne (n := L1) (i := e + 2 * B + 2)
      (j := e + B + 2) L1_k2 hne
    simpa [L2] using this ▸ L1_eb2
  have L2_esucc : L2 / 2 ^ ((e - 1) + 1) % 2 = 1 := by
    have : (e - 1) + 1 = e := by omega
    rwa [this]
  have L3_eb1 : L3 / 2 ^ (e + B + 1) % 2 = 0 := by
    have hne1 : e + B + 1 ≠ (e - 1) + 1 := by omega
    have := div_mod_sub_adjacent (n := L2) (k := e - 1) (j := e + B + 1)
      L2_em1 L2_esucc hne_eb1em1 hne1
    simpa [L3] using this ▸ L2_eb1
  have L3_eb2 : L3 / 2 ^ (e + B + 2) % 2 = 1 := by
    have hne1 : e + B + 2 ≠ (e - 1) + 1 := by omega
    have := div_mod_sub_adjacent (n := L2) (k := e - 1) (j := e + B + 2)
      L2_em1 L2_esucc hne_eb2em1 hne1
    simpa [L3] using this ▸ L2_eb2

  have hne_e2Bm1em1 : e + 2 * B - 1 ≠ e - 1 := by omega
  have hne_e2Bm1e : e + 2 * B - 1 ≠ e := by omega
  have hne_e2Bem1 : e + 2 * B ≠ e - 1 := by omega
  have hne_e2Be : e + 2 * B ≠ e := by omega
  have L1_e2Bm1 : L1 / 2 ^ (e + 2 * B - 1) % 2 = 0 := by
    have hne : e + 2 * B - 1 ≠ e + B := by omega
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e + 2 * B - 1) L_k1 hne
    simpa [L1] using this ▸ L_e2Bm1
  have L2_e2Bm1 : L2 / 2 ^ (e + 2 * B - 1) % 2 = 0 := by
    have hne : e + 2 * B - 1 ≠ e + 2 * B + 2 := by omega
    have := div_mod_sub_two_pow_of_ne (n := L1) (i := e + 2 * B + 2)
      (j := e + 2 * B - 1) L1_k2 hne
    simpa [L2] using this ▸ L1_e2Bm1
  have L3_e2Bm1 : L3 / 2 ^ (e + 2 * B - 1) % 2 = 0 := by
    have hne1 : e + 2 * B - 1 ≠ (e - 1) + 1 := by omega
    have := div_mod_sub_adjacent (n := L2) (k := e - 1) (j := e + 2 * B - 1)
      L2_em1 L2_esucc hne_e2Bm1em1 hne1
    simpa [L3] using this ▸ L2_e2Bm1
  have L1_e2B : L1 / 2 ^ (e + 2 * B) % 2 = 1 := by
    have hne : e + 2 * B ≠ e + B := by omega
    have := div_mod_sub_two_pow_of_ne (n := LOW) (i := e + B)
      (j := e + 2 * B) L_k1 hne
    simpa [L1] using this ▸ L_e2B
  have L2_e2B : L2 / 2 ^ (e + 2 * B) % 2 = 1 := by
    have hne : e + 2 * B ≠ e + 2 * B + 2 := by omega
    have := div_mod_sub_two_pow_of_ne (n := L1) (i := e + 2 * B + 2)
      (j := e + 2 * B) L1_k2 hne
    simpa [L2] using this ▸ L1_e2B
  have L3_e2B : L3 / 2 ^ (e + 2 * B) % 2 = 1 := by
    have hne1 : e + 2 * B ≠ (e - 1) + 1 := by omega
    have := div_mod_sub_adjacent (n := L2) (k := e - 1) (j := e + 2 * B)
      L2_em1 L2_esucc hne_e2Bem1 hne1
    simpa [L3] using this ▸ L2_e2B
  have hne_e2Bm1eb1 : e + 2 * B - 1 ≠ e + B + 1 := by omega
  have hne_e2Bm1eb2 : e + 2 * B - 1 ≠ e + B + 2 := by omega
  have hne_e2Beb1 : e + 2 * B ≠ e + B + 1 := by omega
  have hne_e2Beb2 : e + 2 * B ≠ e + B + 2 := by omega
  have L4_e2Bm1 : L4 / 2 ^ (e + 2 * B - 1) % 2 = 0 := by
    have := div_mod_sub_adjacent (n := L3) (k := e + B + 1) (j := e + 2 * B - 1)
      L3_eb1 L3_eb2 hne_e2Bm1eb1 hne_e2Bm1eb2
    simpa [L4] using this ▸ L3_e2Bm1
  have L4_e2B : L4 / 2 ^ (e + 2 * B) % 2 = 1 := by
    have := div_mod_sub_adjacent (n := L3) (k := e + B + 1) (j := e + 2 * B)
      L3_eb1 L3_eb2 hne_e2Beb1 hne_e2Beb2
    simpa [L4] using this ▸ L3_e2B
  have L4_e2Bsucc : L4 / 2 ^ ((e + 2 * B - 1) + 1) % 2 = 1 := by
    have : (e + 2 * B - 1) + 1 = e + 2 * B := by omega
    rwa [this]

  have hpop0 : popc LOW = e + 1 := by
    simpa [LOW] using popc_adj_LOW hodd hB2 hBe
  have hpop1 : popc L1 = popc LOW - 1 := by
    simpa [L1] using popc_sub_two_pow_bit_on L_k1
  have hpop2 : popc L2 = popc L1 - 1 := by
    simpa [L2] using popc_sub_two_pow_bit_on L1_k2
  have hpop3 : popc L3 = popc L2 := by
    simpa [L3] using popc_sub_adjacent L2_em1 L2_esucc
  have hpop4 : popc L4 = popc L3 := by
    simpa [L4] using popc_sub_adjacent L3_eb1 L3_eb2
  have hpop5 : popc L5 = popc L4 := by
    simpa [L5] using popc_sub_adjacent L4_e2Bm1 L4_e2Bsucc
  have hpopL5 : popc L5 = e - 1 := by omega

  have hL5eq : L5 = LOW - MID := by
    simp only [L5, L4, L3, L2, L1, Nat.sub_sub]
    congr 1
    simp [MID]; ring
  have hlt : L5 < 2 ^ (2 * e + B - 1) := by
    have hle : L5 ≤ LOW := by
      rw [hL5eq]; exact Nat.sub_le _ _
    have hlt0 : LOW < 2 ^ (2 * e + B - 1) := by
      simpa [LOW] using adj_LOW_lt_HIGH hodd hB hfar
    omega
  have hfact := adj_HIGH_factor (e := e) (B := B) (by omega)
  have hsum : HIGH + L5 =
      2 ^ (2 * e + B - 1) *
        (2 ^ (2 * B + 3) + 2 ^ (2 * B) + 2 ^ (B + 3) + 2 ^ B + 2 + 1) + L5 := by
    have : HIGH =
        2 ^ (2 * e + B - 1) *
          (2 ^ (2 * B + 3) + 2 ^ (2 * B) + 2 ^ (B + 3) + 2 ^ B + 2 + 1) := by
      simpa [HIGH] using hfact
    rw [this]
  have hpopC : popc (2 ^ (2 * B + 3) + 2 ^ (2 * B) + 2 ^ (B + 3) +
      2 ^ B + 2 + 1) = 6 := by
    have hH : popc HIGH = 6 := by simpa [HIGH] using popc_adj_HIGH hB
    have hHeq : HIGH =
        2 ^ (2 * e + B - 1) *
          (2 ^ (2 * B + 3) + 2 ^ (2 * B) + 2 ^ (B + 3) + 2 ^ B + 2 + 1) := by
      simpa [HIGH] using hfact
    have := popc_mul_two_pow (2 * e + B - 1)
      (2 ^ (2 * B + 3) + 2 ^ (2 * B) + 2 ^ (B + 3) + 2 ^ B + 2 + 1)
    rw [← this, ← hHeq, hH]
  have hpopHL : popc (HIGH + L5) = e + 5 := by
    rw [hsum, popc_two_pow_mul_add hlt, hpopC, hpopL5]
    omega
  have hQel : HIGH + (LOW - MID) = HIGH + L5 := by rw [hL5eq]
  rw [hQ, hQel, hpopHL]

lemma popc_choose_three_adj_far {e B : ℕ}
    (he : 2 ≤ e) (hodd : e % 2 = 1) (hB : 4 ≤ B) (hBe : B % 2 = 0)
    (hfar : 2 * B + 5 ≤ e) :
    popc (Nat.choose (2 ^ e * (2 ^ (B + 1) + 2 ^ B + 1)) 3) = e + 5 := by
  rw [choose_three_of_two_pow_mul he, popc_mul_two_pow,
    adj_Q_as_m (by omega) hodd]
  exact popc_adj_Q_far hodd hB hBe hfar

lemma a_ne_zero_even_three_bit_adjacent_odd_e_far {e1 e2 e3 : ℕ}
    (h32 : e3 < e2) (h21 : e2 < e1)
    (hA : e1 = e2 + 1) (hB : 3 ≤ e2 - e3)
    (_heA : e1 - e3 < e3) (hodd : e3 % 2 = 1)
    (hBe : (e2 - e3) % 2 = 0)
    (hfar : 2 * (e2 - e3) + 5 ≤ e3) :
    _root_.a (2 ^ e1 + 2 ^ e2 + 2 ^ e3) ≠ 0 := by
  have he : 2 ≤ e3 := by omega
  have hB4 : 4 ≤ e2 - e3 := by omega
  have hn : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 =
      2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) :=
    three_bit_even_factor h32 h21
  have hAeq : e1 - e3 = (e2 - e3) + 1 := by omega
  have he1ge : 2 ≤ e1 := by
    have : e3 + 5 ≤ e1 := by omega
    omega
  have hk : 3 ≤ 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := by
    have hpow : (2 : ℕ) ^ 2 ≤ 2 ^ e1 := Nat.pow_le_pow_right (by decide) he1ge
    have h4 : (4 : ℕ) ≤ 2 ^ e1 := by
      have : (2 : ℕ) ^ 2 = 4 := rfl
      rwa [this] at hpow
    have hsum : (2 : ℕ) ^ e1 ≤ 2 ^ e1 + (2 ^ e2 + 2 ^ e3) := Nat.le_add_right _ _
    have hassoc : (2 : ℕ) ^ e1 + (2 ^ e2 + 2 ^ e3) = 2 ^ e1 + 2 ^ e2 + 2 ^ e3 := by
      ring
    exact le_trans (by decide : (3 : ℕ) ≤ 4) (le_trans h4 (hassoc ▸ hsum))
  refine a_ne_zero_of_witness (2 ^ e1 + 2 ^ e2 + 2 ^ e3) 3 (by decide) hk ?_
  rw [hn, hAeq]
  have hpop := popc_choose_three_adj_far (e := e3) (B := e2 - e3)
    he hodd hB4 hBe hfar
  omega

lemma a_ne_zero_of_odious_ge_257 {n : ℕ} (hn : 257 ≤ n) (hodd : popc n % 2 = 1) :
    a n ≠ 0 := by
  by_cases h1 : popc n = 1
  · -- `n = 2^m` with `m ≥ 8`
    have hn2 : n = 2 ^ n.log2 := exists_log2_of_popc_eq_one h1
    have hm8 : 8 ≤ n.log2 := by
      have h256 : 2 ^ 8 ≤ n := by
        have : (256 : ℕ) ≤ n := by omega
        simpa using this
      exact log2_ge_of_ge_two_pow h256
    rcases Nat.mod_two_eq_zero_or_one n.log2 with he | ho
    · -- even exponent: `C(2^m, 2)` is evil
      have : 2 ≤ n.log2 := by omega
      have := a_ne_zero_two_pow_even_m this he
      rwa [hn2]
    · -- odd exponent ≥ 9
      have hm9 : 9 ≤ n.log2 := by omega
      have hmod8 : n.log2 % 8 = 1 ∨ n.log2 % 8 = 3 ∨ n.log2 % 8 = 5 ∨ n.log2 % 8 = 7 := by
        omega
      rcases hmod8 with h15 | h13 | h55 | h17
      · -- m ≡ 1 (mod 8): m ≡ 1, 9 or 17 (mod 24)
        have h24 : n.log2 % 24 = 1 ∨ n.log2 % 24 = 9 ∨ n.log2 % 24 = 17 := by omega
        rcases h24 with h1 | h9 | h17
        · have hm25 : 25 ≤ n.log2 := by omega
          have := a_ne_zero_two_pow_mod24_eq_one hm25 h1
          rwa [hn2]
        · -- m ≡ 9 (mod 24)
          have hm9' : 9 ≤ n.log2 := by omega
          have := a_ne_zero_two_pow_mod24_eq_nine hm9' h9
          rwa [hn2]
        · -- m ≡ 17 (mod 24): split further mod 216
          have h216 : n.log2 % 216 = 17 ∨ n.log2 % 216 = 41 ∨ n.log2 % 216 = 65 ∨
              n.log2 % 216 = 89 ∨ n.log2 % 216 = 113 ∨ n.log2 % 216 = 137 ∨
              n.log2 % 216 = 161 ∨ n.log2 % 216 = 185 ∨ n.log2 % 216 = 209 := by omega
          rcases h216 with h17 | h41 | h65 | h89 | h113 | h137 | h161 | h185 | h209
          · have hm17 : 17 ≤ n.log2 := by omega
            have := a_ne_zero_two_pow_mod216_eq_seventeen hm17 h17
            rwa [hn2]
          · have hm41 : 41 ≤ n.log2 := by omega
            have := a_ne_zero_two_pow_mod216_eq_fortyone hm41 h41
            rwa [hn2]
          · have hm65 : 65 ≤ n.log2 := by omega
            have := a_ne_zero_two_pow_mod216_eq_sixtyfive hm65 h65
            rwa [hn2]
          · sorry -- m ≡ 89 (mod 216)
          · sorry -- m ≡ 113 (mod 216)
          · sorry -- m ≡ 137 (mod 216)
          · have hm161 : 161 ≤ n.log2 := by omega
            have := a_ne_zero_two_pow_mod216_eq_one_six_one hm161 h161
            rwa [hn2]
          · have hm185 : 185 ≤ n.log2 := by omega
            have := a_ne_zero_two_pow_mod216_eq_one_eight_five hm185 h185
            rwa [hn2]
          · sorry -- m ≡ 209 (mod 216)
      · -- m ≡ 3 (mod 8): m ≡ 3, 11 or 19 (mod 24)
        have h24 : n.log2 % 24 = 3 ∨ n.log2 % 24 = 11 ∨ n.log2 % 24 = 19 := by omega
        rcases h24 with h3 | h11 | h19
        · have hm27 : 27 ≤ n.log2 := by omega
          have := a_ne_zero_two_pow_mod24_eq_three hm27 h3
          rwa [hn2]
        · -- m ≡ 11 (mod 24)
          have hm11 : 11 ≤ n.log2 := by omega
          have := a_ne_zero_two_pow_mod24_eq_eleven hm11 h11
          rwa [hn2]
        · -- m ≡ 19 (mod 24)
          have hm19 : 19 ≤ n.log2 := by omega
          have := a_ne_zero_two_pow_mod24_eq_nineteen hm19 h19
          rwa [hn2]
      · -- m ≡ 5 (mod 8): k = 5
        have hm13 : 13 ≤ n.log2 := by omega
        have := a_ne_zero_two_pow_mod8_eq_five hm13 h55
        rwa [hn2]
      · -- m ≡ 7 (mod 8): k = 5
        have hm15 : 15 ≤ n.log2 := by omega
        have := a_ne_zero_two_pow_mod8_eq_seven hm15 h17
        rwa [hn2]
  · -- `popc n ≥ 3`
    have hge : 3 ≤ popc n := by
      have hz : popc n ≠ 0 := by
        intro h0
        have : n = 0 := (popc_eq_zero_iff n).1 h0
        omega
      omega
    by_cases h3 : popc n = 3
    · obtain ⟨e1, e2, e3, h32, h21, hn3⟩ := eq_three_pow_of_popc_eq_three h3
      by_cases hz : e3 = 0
      · -- odd 3-bit: `n = 2^{e1} + 2^{e2} + 1`
        have hn3' : n = 2 ^ e1 + 2 ^ e2 + 1 := by
          rw [hn3, hz, pow_zero]
        by_cases hcoll : e1 = e2 + 1 ∨ e1 = 2 * e2
        · have he2 : 2 ≤ e2 := by
            by_contra hlt
            have : e2 = 1 := by omega
            rcases hcoll with hA | hB
            · have : e1 = 2 := by omega
              have : n = 7 := by
                rw [hn3', this, ‹e2 = 1›]
                decide
              omega
            · have : e1 = 2 := by omega
              have : n = 7 := by
                rw [hn3', this, ‹e2 = 1›]
                decide
              omega
          have hba : e2 < e1 := h21
          rw [hn3']
          exact a_ne_zero_three_bit_odd_collision hba he2 hcoll
        · -- no-collision odd 3-bit
          have hb : 1 ≤ e2 := by omega
          by_cases hoddg : (e1 - e2) % 2 = 1
          · have hge : 3 ≤ e1 - e2 := by
              have : e1 ≠ e2 + 1 := by
                intro h; exact hcoll (Or.inl h)
              omega
            rw [hn3']
            exact a_ne_zero_three_bit_odd_gap h21 hb hoddg hge
          · -- even gap
            have heven : (e1 - e2) % 2 = 0 := by omega
            have hge2 : 2 ≤ e1 - e2 := by omega
            by_cases hle : (e1 - e2) / 2 ≤ e2
            · by_cases hpar : e2 % 2 = ((e1 - e2) / 2) % 2
              · rw [hn3']
                exact a_ne_zero_three_bit_even_gap h21 hb heven hge2 (fun _ => hpar)
              · -- hard even-gap: g/2 ≤ b and b ≢ g/2 (mod 2)
                sorry
            · rw [hn3']
              exact a_ne_zero_three_bit_even_gap h21 hb heven hge2 (fun h => False.elim (by omega))
      · -- even 3-bit: `n = 2^{e3}(2^A + 2^B + 1)`
        have he3 : 1 ≤ e3 := by omega
        by_cases hAle : e1 - e3 < e3
        · by_cases hB2 : 2 ≤ e2 - e3
          · by_cases hgap : e2 - e3 + 2 ≤ e1 - e3
            · by_cases hcoll : e1 - e3 = 2 * (e2 - e3) - 1
              · -- collision A = 2B - 1
                by_cases hB3 : 3 ≤ e2 - e3
                · by_cases heven : e3 % 2 = 0
                  · have hn : n = 2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) := by
                      rw [hn3]; exact three_bit_even_factor h32 h21
                    rw [hn]
                    refine a_ne_zero_two_pow_mul_of_choose_two (he := by omega)
                      (hm := Nat.succ_le_succ (Nat.zero_le _)) ?hmlt
                      (three_bit_odd _ _ (by omega) (by omega)) ?hevil
                    · have hle :=
                        two_pow_add_two_le_of_lt (e := e3) (A := e1 - e3) (B := e2 - e3)
                          hAle (by omega) (by omega)
                      have hodd' := three_bit_odd (e1 - e3) (e2 - e3) (by omega) (by omega)
                      have hevenp : (2 : ℕ) ^ e3 % 2 = 0 := two_pow_mod_two (by omega)
                      omega
                    · rw [hcoll, popc_sq_sub_one_double_minus hB3,
                        popc_m_sub_one_three_bit (A := 2 * (e2 - e3) - 1) (B := e2 - e3)
                          (by omega)]
                      omega
                  · sorry -- A = 2B-1, e3 odd
                · -- B = 2, A = 3 cannot occur under `B+2 ≤ A`
                  omega
              · by_cases hodd : e3 % 2 = 1
                · rw [hn3]
                  exact a_ne_zero_even_three_bit_easy h32 h21 hAle hB2 hgap hcoll hodd
                · sorry -- e3 even
            · -- A = B + 1
              have hAeq : e1 - e3 = e2 - e3 + 1 := by omega
              have he1 : e1 = e2 + 1 := by omega
              by_cases hB3 : 3 ≤ e2 - e3
              · by_cases heven : e3 % 2 = 0
                · rw [hn3]
                  exact a_ne_zero_even_three_bit_adjacent h32 h21 he1 hB3 hAle heven
                · -- A = B+1, e3 odd
                  by_cases hBeven : (e2 - e3) % 2 = 0
                  · by_cases hfar : 2 * (e2 - e3) + 5 ≤ e3
                    · rw [hn3]
                      exact a_ne_zero_even_three_bit_adjacent_odd_e_far
                        h32 h21 he1 hB3 hAle (by omega) hBeven hfar
                    · sorry -- B even, not far
                  · sorry -- B odd
              · -- B = 2, A = 3
                have hB2eq : e2 - e3 = 2 := by omega
                have hA3 : e1 - e3 = 3 := by omega
                by_cases hodd : e3 % 2 = 1
                · rw [hn3]
                  refine a_ne_zero_even_three_bit_choose_two h32 h21 he3 hAle ?_
                  rw [hA3, hB2eq, popc_sq_sub_one_A3_B2,
                    popc_m_sub_one_three_bit (A := 3) (B := 2) (by decide)]
                  omega
                · -- B = 2, A = 3, e3 even: `n = 13 * 2^{e3}`
                  have hn13 : n = 13 * 2 ^ e3 := by
                    rw [hn3, three_bit_even_factor h32 h21, hA3, hB2eq]
                    have : (2 : ℕ) ^ 3 + 2 ^ 2 + 1 = 13 := by decide
                    rw [this, mul_comm]
                  rw [hn13]
                  by_cases he6 : e3 = 6
                  · rw [he6]; exact a_ne_zero_thirteen_two_pow_six
                  · -- `e3` even, `e3 ≥ 8` (`e3 = 2,4` give `n < 257`)
                    have heven' : e3 % 2 = 0 := by omega
                    have hge8 : 8 ≤ e3 := by
                      have hn257 : 257 ≤ 13 * 2 ^ e3 := by omega
                      have hge6 : 6 ≤ e3 := by
                        by_contra h
                        have : e3 ≤ 4 := by omega
                        have : 2 ^ e3 ≤ 2 ^ 4 :=
                          Nat.pow_le_pow_right (by decide) this
                        have : 13 * 2 ^ e3 ≤ 13 * 16 := by
                          have : (2 : ℕ) ^ 4 = 16 := rfl
                          omega
                        omega
                      omega
                    by_cases he8 : e3 = 8
                    · rw [he8]; exact a_ne_zero_thirteen_two_pow_eight
                    · have he10 : 10 ≤ e3 := by omega
                      exact a_ne_zero_thirteen_two_pow he10 heven'
          · -- B = 1
            have hB1 : e2 - e3 = 1 := by omega
            by_cases hA3 : 3 ≤ e1 - e3
            · by_cases heven : e3 % 2 = 0
              · rw [hn3]
                refine a_ne_zero_even_three_bit_choose_two h32 h21 he3 hAle ?_
                rw [hB1, popc_sq_sub_one_B_one hA3,
                  popc_m_sub_one_three_bit (A := e1 - e3) (B := 1) (by omega)]
                omega
              · sorry -- B = 1, A ≥ 3, e3 odd
            · -- A = 2, B = 1
              have hA2 : e1 - e3 = 2 := by omega
              by_cases heven : e3 % 2 = 0
              · rw [hn3]
                refine a_ne_zero_even_three_bit_choose_two h32 h21 he3 hAle ?_
                rw [hA2, hB1, popc_sq_sub_one_A2_B1,
                  popc_m_sub_one_three_bit (A := 2) (B := 1) (by decide)]
                omega
              · -- A = 2, B = 1, e3 odd: `n = 7 * 2^{e3}`
                have hn7 : n = 7 * 2 ^ e3 := by
                  rw [hn3, three_bit_even_factor h32 h21, hA2, hB1]
                  have : (2 : ℕ) ^ 2 + 2 ^ 1 + 1 = 7 := by decide
                  rw [this, mul_comm]
                rw [hn7]
                by_cases he7 : e3 = 7
                · rw [he7]; exact a_ne_zero_seven_two_pow_seven
                · -- `e3` odd, `e3 ≥ 9` (`e3 = 1,3,5` give `n < 257`)
                  have hodd' : e3 % 2 = 1 := by omega
                  have he9 : 9 ≤ e3 := by
                    have hn257 : 257 ≤ 7 * 2 ^ e3 := by omega
                    have hge6 : 6 ≤ e3 := by
                      by_contra h
                      have : e3 ≤ 5 := by omega
                      have : 2 ^ e3 ≤ 2 ^ 5 :=
                        Nat.pow_le_pow_right (by decide) this
                      have : 7 * 2 ^ e3 ≤ 7 * 32 := by
                        have : (2 : ℕ) ^ 5 = 32 := rfl
                        omega
                      omega
                    omega
                  exact a_ne_zero_seven_two_pow he9 hodd'
        · -- A ≥ e3: `m = 2^A + 2^B + 1 > 2^{e3}`
          have hn : n = 2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) := by
            rw [hn3]; exact three_bit_even_factor h32 h21
          rw [hn]
          by_cases hevil :
              popc ((2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) *
                (2 ^ e3 * (2 ^ (e1 - e3) + 2 ^ (e2 - e3) + 1) - 1)) % 2 = 0
          · exact a_ne_zero_two_pow_mul_of_choose_two_gen (by omega)
              (Nat.succ_le_succ (Nat.zero_le _)) hevil
          · sorry -- A ≥ e3, C(n,2) odious
    · -- `popc n ≥ 5`
      have hn0 : n ≠ 0 := by omega
      rcases Nat.mod_two_eq_zero_or_one n with hen | hon
      · -- even `n = 2^e * m`
        obtain ⟨e, m, hmodd, hnfact⟩ := Nat.exists_eq_two_pow_mul_odd hn0
        have he1 : 1 ≤ e := by
          have : n % 2 = 0 := hen
          rw [hnfact, Nat.mul_mod, Nat.pow_mod] at this
          rcases e with _ | e
          · simp [Nat.odd_iff.mp hmodd] at this
          · omega
        have hm1 : 1 ≤ m := by
          have : m ≠ 0 := by
            intro hm0; subst hm0; exact Nat.not_odd_zero hmodd
          omega
        have hmodd' : m % 2 = 1 := Nat.odd_iff.mp hmodd
        rw [hnfact]
        by_cases hmlt : m < 2 ^ e
        · by_cases hevil :
            (popc (m * m - 1) + e - popc (m - 1)) % 2 = 0
          · exact a_ne_zero_two_pow_mul_of_choose_two he1 hm1 hmlt hmodd' hevil
          · sorry -- even n, m < 2^e, C(n,2) odious
        · by_cases hevil : popc (m * (2 ^ e * m - 1)) % 2 = 0
          · exact a_ne_zero_two_pow_mul_of_choose_two_gen he1 hm1 hevil
          · sorry -- even n, m ≥ 2^e, C(n,2) odious
      · -- odd `n = 2^v * q + 1`
        have hn1 : n - 1 ≠ 0 := by omega
        obtain ⟨v, q, hqodd, hnm1⟩ := Nat.exists_eq_two_pow_mul_odd hn1
        have hv1 : 1 ≤ v := by
          have : (n - 1) % 2 = 0 := by omega
          rw [hnm1, Nat.mul_mod, Nat.pow_mod] at this
          rcases v with _ | v
          · simp [Nat.odd_iff.mp hqodd] at this
          · omega
        have hq1 : 1 ≤ q := by
          have : q ≠ 0 := by
            intro hq0; subst hq0; exact Nat.not_odd_zero hqodd
          omega
        have hn' : n = 2 ^ v * q + 1 := by
          have : n = (n - 1) + 1 := by omega
          rw [this, hnm1]
        rw [hn']
        by_cases hqlt : q < 2 ^ v
        · by_cases hevil : (popc (q * q) + popc q) % 2 = 0
          · exact a_ne_zero_two_pow_mul_add_one_of_choose_two hv1 hq1 hqlt hevil
          · sorry -- odd n, q < 2^v, C(n,2) odious
        · by_cases hevil : popc ((2 ^ v * q + 1) * q) % 2 = 0
          · exact a_ne_zero_two_pow_mul_add_one_of_choose_two_gen hv1 hq1 hevil
          · sorry -- odd n, q ≥ 2^v, C(n,2) odious

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · intro h
    by_contra hnot
    have hne : a n ≠ 0 := by
      rcases Nat.mod_two_eq_zero_or_one (popc n) with heven | hodd
      · exact a_ne_zero_of_not_exception_even_popc hnot heven
      · -- odd popcount: `n` is odious
        by_cases hle : n ≤ 256
        · by_cases hle64 : n ≤ 64
          · by_cases hle20 : n ≤ 20
            · exact a_ne_zero_of_le_20 hle20 hnot
            · have : 21 ≤ n := by omega
              exact a_ne_zero_of_odious_le_64 this hle64 hodd
          · have : 65 ≤ n := by omega
            exact a_ne_zero_of_odious_le_256 this hle hodd
        · have : 257 ≤ n := by omega
          exact a_ne_zero_of_odious_ge_257 this hodd
    exact hne h
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact a_zero
    · exact a_one
    · exact a_two
    · exact a_seven
    · exact a_eight

