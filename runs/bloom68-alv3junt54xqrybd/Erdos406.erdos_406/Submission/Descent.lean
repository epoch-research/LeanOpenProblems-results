import Submission.Arithmetic

/-!
# Exact base-three structure for multiplication and division by 64

All statements in this file concern arbitrary natural numbers whose ternary
expansions use only `0` and `1`.  The finite carry certificates are proved by
kernel reduction; termination, rather than an infinite compatible path, is
essential.  `Nat.digits` is least significant first; division words are most
significant first.  Suffix-run conditions allow the usual zero padding.
-/

namespace Erdos406.Descent

/-- Nonnegative integers with ternary digits in `{0, 1}`; no power-of-two assumption. -/
def cantor (n : ℕ) : Prop := Nat.digits 3 n ⊆ [0, 1]

instance (n : ℕ) : Decidable (cantor n) :=
  inferInstanceAs (Decidable (Nat.digits 3 n ⊆ [0, 1]))

@[simp] theorem cantor_zero : cantor 0 := by simp [cantor]

theorem cantor_div_three (n : ℕ) (h : cantor n) : cantor (n / 3) :=
  Arithmetic.digits_good_div_three n h

theorem cantor_div_three_pow (n r : ℕ) (h : cantor n) : cantor (n / 3 ^ r) :=
  Arithmetic.digits_good_div_three_pow n r h

theorem cantor_digit (n : ℕ) (h : cantor n) : n % 3 ≤ 1 := by
  have hn := Arithmetic.digits_good_digit_ne_two n 0 h
  norm_num at hn
  have := Nat.mod_lt n (by decide : 0 < 3)
  omega

theorem cantor_iff_digit_and_div (n : ℕ) :
    cantor n ↔ n % 3 ≤ 1 ∧ cantor (n / 3) := by
  constructor
  · intro h
    exact ⟨cantor_digit n h, cantor_div_three n h⟩
  · rintro ⟨hd, ht⟩
    by_cases hn : n = 0
    · simp [hn]
    · unfold cantor at *
      rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hn]
      intro d hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp only [List.mem_cons]
        omega
      · exact ht hmem

theorem cantor_ofDigits (w : List ℕ) (h : w ⊆ [0, 1]) :
    cantor (Nat.ofDigits 3 w) := by
  induction w with
  | nil => exact cantor_zero
  | cons d w ih =>
    have hd : d ≤ 1 := by
      have := h List.mem_cons_self
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    have ht : w ⊆ [0, 1] := fun x hx => h (List.mem_cons_of_mem _ hx)
    rw [Nat.ofDigits_cons, cantor_iff_digit_and_div]
    have hd3 : d < 3 := by omega
    constructor
    · simpa [Nat.add_mod, Nat.mod_eq_of_lt hd3] using hd
    · simpa [Nat.add_mul_div_left _ _ (by decide : 0 < 3),
        Nat.div_eq_of_lt hd3] using ih ht

theorem cantor_mod_three_pow (n k : ℕ) (h : cantor n) : cantor (n % 3 ^ k) := by
  rw [Nat.self_mod_pow_eq_ofDigits_take k n (by decide : 2 ≤ 3)]
  exact cantor_ofDigits _ (List.Subset.trans (List.take_subset _ _) h)

/-- One step of the ordinary least-significant-first multiplication algorithm. -/
theorem mul_add_div_three (m n c : ℕ) :
    (m * n + c) / 3 = m * (n / 3) + (m * (n % 3) + c) / 3 := by
  have heq : m * n + c = 3 * (m * (n / 3)) + (m * (n % 3) + c) := by
    conv_lhs => rw [← Nat.mod_add_div n 3]
    ring
  rw [heq, Nat.mul_add_div (by decide : 0 < 3)]

theorem mul_add_mod_three (m n c : ℕ) :
    (m * n + c) % 3 = (m * (n % 3) + c) % 3 := by
  simp [Nat.add_mod, Nat.mul_mod]

/- ## Complete multiplier-64 carry certificates -/

/-- Exactly the carries reachable from zero for the compatible multiplier-64 machine. -/
def reachable64 : List ℕ := [0, 1, 2, 3, 7, 8, 9, 10, 21, 22, 24, 28, 29, 31]

/-- Reachable carries from which a finite input can terminate with a Cantor carry. -/
def live64 : List ℕ := [0, 1, 3, 8, 9, 10, 21, 24, 28, 29, 31]

private theorem reachable64_lt (c : ℕ) (hc : c ∈ reachable64) : c < 32 := by
  simp only [reachable64, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

/-- Exhaustive certificate for all compatible steps from reachable carries. -/
theorem carry64_step_certificate :
    ∀ (c : Fin 32) (d : Fin 2), c.val ∈ reachable64 →
      (64 * d.val + c.val) % 3 ≤ 1 →
      (64 * d.val + c.val) / 3 ∈ reachable64 ∧
        ((64 * d.val + c.val) / 3 ∈ live64 → c.val ∈ live64) := by
  decide +kernel

/-- Exhaustive terminal-state certificate. -/
theorem carry64_terminal_certificate :
    ∀ c : Fin 32, c.val ∈ reachable64 → cantor c.val → c.val ∈ live64 := by
  decide +kernel

/-- Every live carry has a finite accepting continuation (of value at most 13). -/
theorem carry64_live_witness_certificate :
    ∀ c : Fin 32, c.val ∈ live64 →
      ∃ n : Fin 14, cantor n.val ∧ cantor (64 * n.val + c.val) := by
  decide +kernel

/-- A reachable carry compatible with an actual finite integer must be live. -/
theorem carry64_live (n c : ℕ) (hc : c ∈ reachable64)
    (hn : cantor n) (hout : cantor (64 * n + c)) : c ∈ live64 := by
  induction n using Nat.strong_induction_on generalizing c with
  | h n ih =>
    by_cases hzero : n = 0
    · subst n
      exact carry64_terminal_certificate ⟨c, reachable64_lt c hc⟩ hc (by simpa using hout)
    · have hd := cantor_digit n hn
      have he : (64 * (n % 3) + c) % 3 ≤ 1 := by
        rw [← mul_add_mod_three]
        exact cantor_digit _ hout
      have hstep := carry64_step_certificate ⟨c, reachable64_lt c hc⟩
        ⟨n % 3, by omega⟩ hc he
      have hn' := cantor_div_three n hn
      have hout' : cantor (64 * (n / 3) + (64 * (n % 3) + c) / 3) := by
        rw [← mul_add_div_three]
        exact cantor_div_three _ hout
      have hnext := ih (n / 3) (Nat.div_lt_self (by omega) (by decide))
        _ hstep.1 hn' hout'
      exact hstep.2 hnext

/-- Exact coaccessibility, including sufficiency, not just a necessary-state relaxation. -/
theorem carry64_live_iff (c : ℕ) (hc : c ∈ reachable64) :
    c ∈ live64 ↔ ∃ n : ℕ, cantor n ∧ cantor (64 * n + c) := by
  constructor
  · intro h
    obtain ⟨n, hn, hout⟩ :=
      carry64_live_witness_certificate ⟨c, reachable64_lt c hc⟩ h
    exact ⟨n.val, hn, hout⟩
  · rintro ⟨n, hn, hout⟩
    exact carry64_live n c hc hn hout

/-- The three reachable but nonterminating carries really have no finite witness. -/
theorem carry64_dead (c : ℕ) (hc : c ∈ [2, 7, 22]) (n : ℕ) (hn : cantor n) :
    ¬cantor (64 * n + c) := by
  intro hout
  have hreach : c ∈ reachable64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> decide
  have h := carry64_live n c hreach hn hout
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> norm_num [live64] at h

/-- Execute a compatible least-significant-first carry word. -/
def carryRun64 (c : ℕ) : List ℕ → Option ℕ
  | [] => some c
  | d :: w =>
    if d ≤ 1 ∧ (64 * d + c) % 3 ≤ 1 then carryRun64 ((64 * d + c) / 3) w
    else none

private def carryReachWord64 : ℕ → List ℕ
  | 0 => []
  | 1 => [1, 1, 0, 0, 0]
  | 2 => [1, 0, 0]
  | 3 => [1, 1, 0, 0]
  | 7 => [1, 0]
  | 8 => [1, 1, 0, 1, 0]
  | 9 => [1, 1, 0]
  | 10 => [1, 1, 0, 1, 1, 1, 0]
  | 21 => [1]
  | 22 => [1, 0, 0, 1]
  | 24 => [1, 1, 0, 1]
  | 28 => [1, 1]
  | 29 => [1, 1, 0, 1, 1]
  | 31 => [1, 1, 0, 1, 1, 1]
  | _ => []

private theorem carry64_reach_witness_certificate :
    ∀ c : Fin 32, c.val ∈ reachable64 → carryRun64 0 (carryReachWord64 c.val) = some c.val := by
  decide +kernel

theorem carryRun64_reachable (w : List ℕ) (c t : ℕ) (hc : c ∈ reachable64)
    (h : carryRun64 c w = some t) : t ∈ reachable64 := by
  induction w generalizing c with
  | nil =>
    simp only [carryRun64, Option.some.injEq] at h
    simpa [← h] using hc
  | cons d w ih =>
    by_cases hd : d ≤ 1 ∧ (64 * d + c) % 3 ≤ 1
    · rw [carryRun64, if_pos hd] at h
      have hstep := carry64_step_certificate ⟨c, reachable64_lt c hc⟩
        ⟨d, by omega⟩ hc hd.2
      exact ih _ hstep.1 h
    · simp only [carryRun64, if_neg hd, reduceCtorEq] at h

/-- Exact reachability of the fourteen carries, with explicit finite witnesses. -/
theorem carry64_reachable_iff (c : ℕ) :
    c ∈ reachable64 ↔ ∃ w : List ℕ, carryRun64 0 w = some c := by
  constructor
  · intro hc
    exact ⟨carryReachWord64 c,
      carry64_reach_witness_certificate ⟨c, reachable64_lt c hc⟩ hc⟩
  · rintro ⟨w, hw⟩
    exact carryRun64_reachable w 0 c (by decide) hw

/-- All edges of the live multiplier graph; the middle coordinate is its input digit. -/
def multiplier64LiveEdges : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 1, 21), (1, 0, 0), (3, 0, 1), (8, 1, 24),
   (9, 0, 3), (9, 1, 24), (10, 0, 3), (21, 1, 28), (24, 0, 8),
   (24, 1, 29), (28, 0, 9), (29, 1, 31), (31, 0, 10)]

/-- Exact edge certificate, not an overapproximation of the productive graph. -/
theorem multiplier64_live_edges_certificate :
    ∀ (c : Fin 32) (d : Fin 2),
      (c.val ∈ reachable64 ∧ (64 * d.val + c.val) % 3 ≤ 1 ∧
        (64 * d.val + c.val) / 3 ∈ live64) ↔
      (c.val, d.val, (64 * d.val + c.val) / 3) ∈ multiplier64LiveEdges := by
  decide +kernel

/-- The supplied most-significant-first division graph, with input digit in the middle. -/
def division64LiveEdges : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 1, 1), (1, 0, 3), (3, 0, 9), (3, 1, 10),
   (8, 0, 24), (9, 1, 28), (10, 1, 31), (21, 1, 0),
   (24, 0, 8), (24, 1, 9), (28, 1, 21), (29, 1, 24), (31, 0, 29)]

/-- Exhaustively verified division edges between live remainders, including quotient restriction. -/
theorem division64_live_edges_certificate :
    ∀ (r : Fin 64) (d : Fin 2),
      (r.val ∈ live64 ∧ (3 * r.val + d.val) / 64 ≤ 1 ∧
        (3 * r.val + d.val) % 64 ∈ live64) ↔
      (r.val, d.val, (3 * r.val + d.val) % 64) ∈ division64LiveEdges := by
  decide +kernel

theorem carry64_next_live (n c : ℕ) (hc : c ∈ reachable64)
    (hn : cantor n) (hout : cantor (64 * n + c)) :
    (64 * (n % 3) + c) / 3 ∈ live64 := by
  have hd := cantor_digit n hn
  have he : (64 * (n % 3) + c) % 3 ≤ 1 := by
    rw [← mul_add_mod_three]
    exact cantor_digit _ hout
  have hstep := carry64_step_certificate ⟨c, reachable64_lt c hc⟩
    ⟨n % 3, by omega⟩ hc he
  apply carry64_live (n / 3) _ hstep.1 (cantor_div_three n hn)
  rw [← mul_add_div_three]
  exact cantor_div_three _ hout

/- ## Endpoints and generic-integer exclusions -/

/-- An exact trailing run of `len` ones, followed by a zero (including zero padding). -/
def trailingOnesRun (n len : ℕ) : Prop :=
  n % 3 ^ (len + 1) = (3 ^ len - 1) / 2

instance (n len : ℕ) : Decidable (trailingOnesRun n len) := inferInstanceAs (Decidable (_ = _))

/-- The crucial unit suffix: two ones and then a zero, not merely at least two ones. -/
theorem multiplier64_unit_suffix (u : ℕ) (hu : cantor u) (h64 : cantor (64 * u))
    (hunit : u % 3 = 1) : u % 27 = 4 := by
  have hv := cantor_div_three u hu
  have h21 : cantor (64 * (u / 3) + 21) := by
    have h := cantor_div_three (64 * u) h64
    have heq : 64 * u / 3 = 64 * (u / 3) + 21 := by
      have ht := mul_add_div_three 64 u 0
      simpa [hunit] using ht
    simpa only [heq] using h
  have hvd := cantor_digit (u / 3) hv
  have hvone : u / 3 % 3 = 1 := by
    have hl := carry64_next_live (u / 3) 21 (by decide) hv h21
    by_cases hz : u / 3 % 3 = 0
    · norm_num [hz, live64] at hl
    · omega
  have hw := cantor_div_three (u / 3) hv
  have h28 : cantor (64 * (u / 3 / 3) + 28) := by
    have h := cantor_div_three _ h21
    have heq : (64 * (u / 3) + 21) / 3 = 64 * (u / 3 / 3) + 28 := by
      rw [mul_add_div_three, hvone]
    simpa only [heq] using h
  have hwd := cantor_digit (u / 3 / 3) hw
  have hwzero : u / 3 / 3 % 3 = 0 := by
    have he := cantor_digit _ h28
    rw [mul_add_mod_three] at he
    by_cases hz : u / 3 / 3 % 3 = 0
    · exact hz
    · have ho : u / 3 / 3 % 3 = 1 := by omega
      norm_num [ho] at he
  omega

theorem multiplier64_unit_trailing_run (u : ℕ) (hu : cantor u)
    (h64 : cantor (64 * u)) (hunit : u % 3 = 1) : trailingOnesRun u 2 := by
  simpa [trailingOnesRun] using multiplier64_unit_suffix u hu h64 hunit

/-- Multiplication by a power of three adds only zero digits. -/
theorem cantor_three_pow_mul_iff (n r : ℕ) : cantor (3 ^ r * n) ↔ cantor n := by
  by_cases hn : n = 0
  · simp [hn]
  · unfold cantor
    rw [Nat.digits_base_pow_mul (by decide : 1 < 3) (by omega : 0 < n),
      List.append_subset]
    have hz : List.replicate r 0 ⊆ [0, 1] := by
      intro d hd
      have := (List.mem_replicate.mp hd).2
      simp [this]
    exact and_iff_right hz

/-- Remove exactly the trailing ternary zeros and obtain the exact two-one unit suffix. -/
theorem multiplier64_strip_trailing_zeros (M : ℕ) (hpos : 0 < M)
    (hM : cantor M) (h64 : cantor (64 * M)) :
    ∃ r u : ℕ, 0 < u ∧ ¬3 ∣ u ∧ M = 3 ^ r * u ∧ cantor u ∧
      cantor (64 * u) ∧ trailingOnesRun u 2 := by
  obtain ⟨r, u, hunit, hfactor⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : M ≠ 0) 3 (by decide)
  have hup : 0 < u := by
    by_contra h
    have hz : u = 0 := by omega
    simp [hz] at hfactor
    omega
  have hu : cantor u := (cantor_three_pow_mul_iff u r).mp (by simpa [hfactor] using hM)
  have hu64 : cantor (64 * u) := (cantor_three_pow_mul_iff (64 * u) r).mp (by
    convert h64 using 1
    rw [hfactor]
    ring)
  have humod : u % 3 = 1 := by
    have hd := cantor_digit u hu
    have hn : u % 3 ≠ 0 := fun h => hunit (Nat.dvd_of_mod_eq_zero h)
    omega
  exact ⟨r, u, hup, hunit, hfactor, hu, hu64,
    multiplier64_unit_trailing_run u hu hu64 humod⟩

private theorem multiplier64_output_suffix_certificate :
    ∀ u : Fin 729, u.val % 27 = 4 → cantor u.val → cantor (64 * u.val % 729) →
      64 * u.val % 81 = 13 ∨ 64 * u.val % 243 = 40 ∨ 64 * u.val % 729 = 121 := by
  decide +kernel

private theorem mul_mod_input_mod (m n P Q : ℕ) (h : Q ∣ P) :
    m * (n % P) % Q = m * n % Q := by
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd n h, ← Nat.mul_mod]

/-- The product's unit suffix has exactly three, four, or five ones. -/
theorem multiplier64_unit_output_trailing_run (u : ℕ) (hu : cantor u)
    (h64 : cantor (64 * u)) (hunit : u % 3 = 1) :
    trailingOnesRun (64 * u) 3 ∨ trailingOnesRun (64 * u) 4 ∨
      trailingOnesRun (64 * u) 5 := by
  have hs := multiplier64_unit_suffix u hu h64 hunit
  have hsmall : cantor (u % 729) := by
    simpa using cantor_mod_three_pow u 6 hu
  have houtsmall : cantor (64 * (u % 729) % 729) := by
    rw [mul_mod_input_mod 64 u 729 729 (dvd_refl _)]
    simpa using cantor_mod_three_pow (64 * u) 6 h64
  have hs' : u % 729 % 27 = 4 := by
    rw [Nat.mod_mod_of_dvd u (by decide : 27 ∣ 729)]
    exact hs
  have h := multiplier64_output_suffix_certificate
    ⟨u % 729, Nat.mod_lt _ (by decide : 0 < 729)⟩ hs' hsmall houtsmall
  rw [mul_mod_input_mod 64 u 729 81 (by decide),
      mul_mod_input_mod 64 u 729 243 (by decide),
      mul_mod_input_mod 64 u 729 729 (dvd_refl _)] at h
  simpa [trailingOnesRun] using h

/-- Unit-form exclusions.  The last exclusion applies the two-one suffix theorem again. -/
theorem multiplier64_unit_exclusions (u : ℕ) (hu : cantor u)
    (h64 : cantor (64 * u)) (hunit : u % 3 = 1) :
    ¬cantor (4 * u) ∧ ¬cantor (256 * u) ∧ ¬cantor (4096 * u) := by
  have hs := multiplier64_unit_suffix u hu h64 hunit
  have hs9 : u % 9 = 4 := by omega
  have hfour : 4 * u % 9 = 7 := by norm_num [Nat.mul_mod, hs9]
  have h256 : 256 * u % 9 = 7 := by norm_num [Nat.mul_mod, hs9]
  have hbad (n : ℕ) (hn : n % 9 = 7) : ¬cantor n := by
    intro hg
    have hd := Arithmetic.digits_good_digit_ne_two n 1 hg
    have heq := Nat.mod_mul_right_div_self n 3 3
    norm_num [hn] at heq
    norm_num at hd
    exact hd heq.symm
  refine ⟨hbad _ hfour, hbad _ h256, ?_⟩
  intro h4096
  have h64unit : (64 * u) % 3 = 1 := by norm_num [Nat.mul_mod, hunit]
  have hnext := multiplier64_unit_suffix (64 * u) h64
    (by convert h4096 using 1; ring) h64unit
  have hactual : 64 * u % 27 = 13 := by norm_num [Nat.mul_mod, hs]
  omega

/-- Unconditional generic-integer exclusions, with no assumption that `M` is a power of two. -/
theorem multiplier64_exclusions (M : ℕ) (hpos : 0 < M)
    (hM : cantor M) (h64 : cantor (64 * M)) :
    ¬cantor (4 * M) ∧ ¬cantor (256 * M) ∧ ¬cantor (4096 * M) := by
  obtain ⟨r, u, hup, hunit, hfactor, hu, hu64, hrun⟩ :=
    multiplier64_strip_trailing_zeros M hpos hM h64
  have humod : u % 3 = 1 := by
    have hd := cantor_digit u hu
    have hn : u % 3 ≠ 0 := fun h => hunit (Nat.dvd_of_mod_eq_zero h)
    omega
  have hb := multiplier64_unit_exclusions u hu hu64 humod
  have htransfer (a : ℕ) (h : ¬cantor (a * u)) : ¬cantor (a * M) := by
    intro hg
    apply h
    apply (cantor_three_pow_mul_iff (a * u) r).mp
    convert hg using 1
    rw [hfactor]
    ring
  exact ⟨htransfer 4 hb.1, htransfer 256 hb.2.1, htransfer 4096 hb.2.2⟩

theorem no_cantor_mul64_mul256 (M : ℕ) (hpos : 0 < M) :
    ¬(cantor M ∧ cantor (64 * M) ∧ cantor (256 * M)) := by
  rintro ⟨hM, h64, h256⟩
  exact (multiplier64_exclusions M hpos hM h64).2.1 h256

theorem no_cantor_mul64_mul4096 (M : ℕ) (hpos : 0 < M) :
    ¬(cantor M ∧ cantor (64 * M) ∧ cantor (4096 * M)) := by
  rintro ⟨hM, h64, h4096⟩
  exact (multiplier64_exclusions M hpos hM h64).2.2 h4096

/-- A Cantor integer below `3^L` is already below half of `3^L`. -/
theorem cantor_small_bound (n L : ℕ) (h : cantor n) (hlt : n < 3 ^ L) :
    2 * n < 3 ^ L := by
  induction L generalizing n with
  | zero => norm_num at *; omega
  | succ L ih =>
    have hd := cantor_digit n h
    have hnq := cantor_div_three n h
    have hq : n / 3 < 3 ^ L := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr
      simpa [pow_succ] using hlt
    have hbound := ih (n / 3) hnq hq
    have hdecomp := Nat.mod_add_div n 3
    rw [pow_succ]
    omega

/-- The leading run consists of one `1`: the two highest digits are `10`. -/
def leadingOnesRunOne (n : ℕ) : Prop :=
  ∃ j : ℕ, n / 3 ^ (j + 1) = 1 ∧ n / 3 ^ j % 3 = 0

/-- The high endpoint of every compatible positive multiplier-64 pair is `10`. -/
theorem multiplier64_leading_run_one (M : ℕ) (hpos : 0 < M)
    (hM : cantor M) (h64 : cantor (64 * M)) : leadingOnesRunOne (64 * M) := by
  let k := Nat.log 3 M
  let P := 3 ^ k
  have hPpos : 0 < P := by dsimp [P]; positivity
  have hPlow : P ≤ M := Nat.pow_log_le_self 3 (by omega)
  have hMlt : M < 3 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) M
  have hMbound : 2 * M < 3 * P := by
    have h := cantor_small_bound M (k + 1) hM hMlt
    simpa [pow_succ, P, Nat.mul_comm] using h
  have hNlow : 64 * P ≤ 64 * M := by omega
  have hNhi : 64 * M < 96 * P := by omega
  have h27 : 3 ^ (k + 3) = 27 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
  have h81 : 3 ^ (k + 4) = 81 * P := by dsimp [P]; rw [pow_add]; norm_num; ring
  have hN81 : 81 * P ≤ 64 * M := by
    by_contra hnot
    have hquot : 64 * M / (27 * P) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have hd := Arithmetic.digits_good_digit_ne_two (64 * M) (k + 3) h64
    rw [h27, hquot] at hd
    norm_num at hd
  refine ⟨k + 3, ?_, ?_⟩
  · have hquot : 64 * M / (81 * P) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simpa [show k + 3 + 1 = k + 4 by omega, h81] using hquot
  · have hquot : 64 * M / (27 * P) = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [h27, hquot]

/-- All three endpoint claims together, after removing exactly the trailing zeros. -/
theorem multiplier64_endpoint_structure (M : ℕ) (hpos : 0 < M)
    (hM : cantor M) (h64 : cantor (64 * M)) :
    leadingOnesRunOne (64 * M) ∧
      ∃ r u : ℕ, 0 < u ∧ ¬3 ∣ u ∧ M = 3 ^ r * u ∧ cantor u ∧
        cantor (64 * u) ∧ trailingOnesRun u 2 ∧
        (trailingOnesRun (64 * u) 3 ∨ trailingOnesRun (64 * u) 4 ∨
          trailingOnesRun (64 * u) 5) := by
  refine ⟨multiplier64_leading_run_one M hpos hM h64, ?_⟩
  obtain ⟨r, u, hup, hunit, hfactor, hu, hu64, hrun⟩ :=
    multiplier64_strip_trailing_zeros M hpos hM h64
  have humod : u % 3 = 1 := by
    have hd := cantor_digit u hu
    have hn : u % 3 ≠ 0 := fun h => hunit (Nat.dvd_of_mod_eq_zero h)
    omega
  exact ⟨r, u, hup, hunit, hfactor, hu, hu64, hrun,
    multiplier64_unit_output_trailing_run u hu hu64 humod⟩

/-- Actual forbidden digits, not only failure of the digit-subset predicate. -/
theorem multiplier64_has_digit_two (M : ℕ) (hpos : 0 < M)
    (hM : cantor M) (h64 : cantor (64 * M)) :
    2 ∈ Nat.digits 3 (4 * M) ∧ 2 ∈ Nat.digits 3 (256 * M) ∧
      2 ∈ Nat.digits 3 (4096 * M) := by
  have h := multiplier64_exclusions M hpos hM h64
  simpa only [cantor, Arithmetic.digits_good_iff_two_absent, not_not] using h

/- ## Exact most-significant-first division language -/

/-- MSF division with both the input and quotient digits restricted to 0/1. -/
def divisionRun64 (r : ℕ) : List ℕ → Option ℕ
    | [] => some r
    | d :: w =>
        if d ≤ 1 ∧ (3*r+d)/64 ≤ 1 then divisionRun64 ((3*r+d)%64) w else none

/-- The quotient word, including its leading zero padding. -/
def divisionQuotient64 (r : ℕ) : List ℕ → List ℕ
    | [] => []
    | d :: w => (3*r+d)/64 :: divisionQuotient64 ((3*r+d)%64) w

def divisionAccepts64 (r : ℕ) (w : List ℕ) : Prop := divisionRun64 r w = some 0

private theorem division64_forward_certificate :
  ∀ (r : Fin 64) (d : Fin 2), r.val ∉ [2, 7, 22, 32] → (3*r.val+d.val)/64 ≤1 →
    (3*r.val+d.val)%64 ∉ [2, 7, 22, 32] := by decide +kernel

private theorem division64_backward_certificate :
  ∀ (r : Fin 64) (d : Fin 2), (3*r.val+d.val)/64 ≤1 →
    (3*r.val+d.val)%64 ∈ reachable64 → r.val ∈ reachable64 := by decide +kernel

private theorem division64_intersection_certificate :
  ∀ r : Fin 64, r.val ∈ reachable64 → r.val ∉ [2, 7, 22, 32] → r.val ∈ live64 := by
  decide +kernel

private theorem division64_live_excludes :
  ∀ r : Fin 32, r.val ∈ live64 → r.val ∉ [2, 7, 22, 32] := by decide +kernel

private theorem live64_lt (r : ℕ) (hr : r ∈ live64) : r <32 := by
  simp only [live64, List.mem_cons, List.not_mem_nil, or_false] at hr
  omega

private theorem divisionAccepts64_cons (r d : ℕ) (w : List ℕ) :
  divisionAccepts64 r (d::w) ↔
    d ≤1 ∧ (3*r+d)/64 ≤1 ∧ divisionAccepts64 ((3*r+d)%64) w := by
  unfold divisionAccepts64
  by_cases hd : d ≤1 ∧ (3*r+d)/64 ≤1
  ·
      simp [divisionRun64, hd]
  ·
      simp only [divisionRun64, if_neg hd, reduceCtorEq, false_iff, not_and]
      intro h1 h2
      exact (hd ⟨h1, h2⟩).elim

private theorem divisionAccepts64_backward (w : List ℕ) (r : ℕ) (hr : r <64)
  (h : divisionAccepts64 r w) : r ∈ reachable64 := by
  induction w generalizing r with
  | nil =>
    have heq : r = 0 := by simpa [divisionAccepts64, divisionRun64] using h
    subst r
    decide
  | cons d w ih =>
    obtain ⟨hd, hq, ht⟩ := (divisionAccepts64_cons r d w).mp h
    have hn := ih _ (Nat.mod_lt _ (by decide)) ht
    exact division64_backward_certificate ⟨r, hr⟩ ⟨d, by omega⟩ hq hn

/-- An accepted suffix at a forward-reachable state must lie in the eleven-state live graph. -/
theorem division64_accepted_live (w : List ℕ) (r : ℕ) (hr : r <64)
  (hforward : r ∉ [2, 7, 22, 32]) (h : divisionAccepts64 r w) : r ∈ live64 :=
  division64_intersection_certificate ⟨r, hr⟩ (divisionAccepts64_backward w r hr h) hforward

private theorem division64_edge_facts (r d t : ℕ) (h : (r, d, t) ∈ division64LiveEdges) :
  d ≤1 ∧ (3*r+d)/64 ≤1 ∧ (3*r+d)%64=t := by
  simp only [division64LiveEdges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
      rcases h with ⟨rfl, rfl, rfl⟩ <;> decide

/-- Every accepted step at a live state is exactly one of the listed edges, and conversely. -/
theorem division64_accepted_cons_live (r d : ℕ) (w : List ℕ) (hr : r ∈ live64) :
  divisionAccepts64 r (d::w) ↔
    ∃ t : ℕ, (r, d, t) ∈ division64LiveEdges ∧ divisionAccepts64 t w := by
  constructor
  ·
      intro h
      obtain ⟨hd, hq, ht⟩ := (divisionAccepts64_cons r d w).mp h
      have hnot := division64_live_excludes ⟨r, live64_lt r hr⟩ hr
      have hforward := division64_forward_certificate
        ⟨r, by have := live64_lt r hr; omega⟩ ⟨d, by omega⟩ hnot hq
      have hnext := division64_accepted_live w _ (Nat.mod_lt _ (by decide)) hforward ht
      exact ⟨_, (division64_live_edges_certificate
        ⟨r, by have := live64_lt r hr; omega⟩ ⟨d, by omega⟩).mp ⟨hr, hq, hnext⟩, ht⟩
  ·
      rintro ⟨t, he, ht⟩
      obtain ⟨hd, hq, hnext⟩ := division64_edge_facts r d t he
      apply (divisionAccepts64_cons r d w).mpr
      simpa [hnext] using And.intro hd (And.intro hq ht)

private theorem accept0_cons (d : ℕ) (w : List ℕ) :
  divisionAccepts64 0 (d::w) ↔
    (d=0 ∧ divisionAccepts64 0 w) ∨ (d=1 ∧ divisionAccepts64 1 w) := by
  rw [division64_accepted_cons_live 0 d w (by decide)]
  simp [division64LiveEdges, or_and_right, exists_or]

private theorem accept3_cons (d : ℕ) (w : List ℕ) :
  divisionAccepts64 3 (d::w) ↔
    (d=0 ∧ divisionAccepts64 9 w) ∨ (d=1 ∧ divisionAccepts64 10 w) := by
  rw [division64_accepted_cons_live 3 d w (by decide)]
  simp [division64LiveEdges, or_and_right, exists_or]

private theorem accept24_cons (d : ℕ) (w : List ℕ) :
  divisionAccepts64 24 (d::w) ↔
    (d=0 ∧ divisionAccepts64 8 w) ∨ (d=1 ∧ divisionAccepts64 9 w) := by
  rw [division64_accepted_cons_live 24 d w (by decide)]
  simp [division64LiveEdges, or_and_right, exists_or]

private theorem accept_single_edge (r d t : ℕ) (hzero : r ≠0) (hr : r ∈ live64)
  (hedges : ∀ a b : ℕ, (r, a, b) ∈ division64LiveEdges ↔ a=d ∧ b=t) (w : List ℕ) :
  divisionAccepts64 r w ↔ ∃ v, w=d::v ∧ divisionAccepts64 t v := by
  cases w with
  | nil => simp [divisionAccepts64, divisionRun64, hzero]
  | cons a w =>
    rw [division64_accepted_cons_live r a w hr]
    simp [hedges]

private theorem accept1_word (w : List ℕ) :
  divisionAccepts64 1 w ↔ ∃ v, w=0::v ∧ divisionAccepts64 3 v := by
  apply accept_single_edge 1 0 3 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept8_word (w : List ℕ) :
  divisionAccepts64 8 w ↔ ∃ v, w=0::v ∧ divisionAccepts64 24 v := by
  apply accept_single_edge 8 0 24 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept9_word (w : List ℕ) :
  divisionAccepts64 9 w ↔ ∃ v, w=1::v ∧ divisionAccepts64 28 v := by
  apply accept_single_edge 9 1 28 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept10_word (w : List ℕ) :
  divisionAccepts64 10 w ↔ ∃ v, w=1::v ∧ divisionAccepts64 31 v := by
  apply accept_single_edge 10 1 31 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept21_word (w : List ℕ) :
  divisionAccepts64 21 w ↔ ∃ v, w=1::v ∧ divisionAccepts64 0 v := by
  apply accept_single_edge 21 1 0 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept28_word (w : List ℕ) :
  divisionAccepts64 28 w ↔ ∃ v, w=1::v ∧ divisionAccepts64 21 v := by
  apply accept_single_edge 28 1 21 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept29_word (w : List ℕ) :
  divisionAccepts64 29 w ↔ ∃ v, w=1::v ∧ divisionAccepts64 24 v := by
  apply accept_single_edge 29 1 24 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept31_word (w : List ℕ) :
  divisionAccepts64 31 w ↔ ∃ v, w=0::v ∧ divisionAccepts64 29 v := by
  apply accept_single_edge 31 0 29 (by decide) (by decide)
  intro a b
  simp [division64LiveEdges]

private theorem accept9_suffix (w : List ℕ) :
  divisionAccepts64 9 w ↔ ∃ v, w=[1, 1, 1]++v ∧ divisionAccepts64 0 v := by
  constructor
  ·
      intro h
      obtain ⟨a, rfl, ha⟩ := (accept9_word w).mp h
      obtain ⟨b, rfl, hb⟩ := (accept28_word a).mp ha
      obtain ⟨c, rfl, hc⟩ := (accept21_word b).mp hb
      exact ⟨c, rfl, hc⟩
  ·
      rintro ⟨v, rfl, hv⟩
      exact (accept9_word _).mpr ⟨_, rfl, (accept28_word _).mpr
          ⟨_, rfl, (accept21_word _).mpr ⟨_, rfl, hv⟩⟩⟩

private theorem accept10_suffix (w : List ℕ) :
  divisionAccepts64 10 w ↔ ∃ v, w=[1, 0, 1]++v ∧ divisionAccepts64 24 v := by
  constructor
  ·
      intro h
      obtain ⟨a, rfl, ha⟩ := (accept10_word w).mp h
      obtain ⟨b, rfl, hb⟩ := (accept31_word a).mp ha
      obtain ⟨c, rfl, hc⟩ := (accept29_word b).mp hb
      exact ⟨c, rfl, hc⟩
  ·
      rintro ⟨v, rfl, hv⟩
      exact (accept10_word _).mpr ⟨_, rfl, (accept31_word _).mpr
          ⟨_, rfl, (accept29_word _).mpr ⟨_, rfl, hv⟩⟩⟩

private theorem accept24_choice (w : List ℕ) :
  divisionAccepts64 24 w ↔
    (∃ v, w=[0, 0]++v ∧ divisionAccepts64 24 v) ∨
    (∃ v, w=[1, 1, 1, 1]++v ∧ divisionAccepts64 0 v) := by
  cases w with
  | nil => simp [divisionAccepts64, divisionRun64]
  | cons d w =>
    rw [accept24_cons]
    constructor
    ·
        rintro (⟨rfl, h⟩|⟨rfl, h⟩)
        ·
            obtain ⟨v, rfl, hv⟩ := (accept8_word w).mp h
            exact Or.inl ⟨v, rfl, hv⟩
        ·
            obtain ⟨v, rfl, hv⟩ := (accept9_suffix w).mp h
            exact Or.inr ⟨v, rfl, hv⟩
    ·
        rintro (⟨v, h, hv⟩|⟨v, h, hv⟩)
        ·
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Or.inl ⟨rfl, (accept8_word _).mpr ⟨v, rfl, hv⟩⟩
        ·
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Or.inr ⟨rfl, (accept9_suffix _).mpr ⟨v, rfl, hv⟩⟩

/-- The word `(00)^t`. -/
def zeroPairs64 : ℕ → List ℕ
  | 0 => []
  | t+1 => 0::0::zeroPairs64 t

/-- The corresponding quotient word `(10)^t`. -/
def oneZeroPairs64 : ℕ → List ℕ
  | 0 => []
  | t+1 => 1::0::oneZeroPairs64 t

private theorem accept24_loops (t : ℕ) (w : List ℕ) :
  divisionAccepts64 24 (zeroPairs64 t ++ w) ↔ divisionAccepts64 24 w := by
  induction t with
  | zero => simp [zeroPairs64]
  | succ t ih =>
    simpa [zeroPairs64, divisionAccepts64, divisionRun64] using ih

private theorem accept24_loops_iff (w : List ℕ) :
  divisionAccepts64 24 w ↔
    ∃ t v, w=zeroPairs64 t ++ [1, 1, 1, 1] ++v ∧ divisionAccepts64 0 v := by
  constructor
  ·
      intro h
      have H : ∀ n : ℕ, ∀ w : List ℕ, w.length=n → divisionAccepts64 24 w →
          ∃ t v, w=zeroPairs64 t ++ [1, 1, 1, 1] ++v ∧ divisionAccepts64 0 v := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro w hn hw
          rcases (accept24_choice w).mp hw with ⟨v, rfl, hv⟩|⟨v, rfl, hv⟩
          ·
              have hvlt : v.length < n := by simp at hn; omega
              obtain ⟨t, z, hz, hend⟩ := ih v.length hvlt v rfl hv
              refine ⟨t+1, z, ?_, hend⟩
              simp [zeroPairs64, hz, List.append_assoc]
          ·
              exact ⟨0, v, rfl, hv⟩
      exact H w.length w rfl h
  ·
      rintro ⟨t, v, rfl, hv⟩
      rw [List.append_assoc]
      apply (accept24_loops t _).mpr
      exact (accept24_choice _).mpr (Or.inr ⟨v, rfl, hv⟩)

/-- The short nonzero return block `100111`. -/
def divisionBlockA64 : List ℕ := [1, 0, 0, 1, 1, 1]

/-- The long return blocks `101101(00)^t1111`. -/
def divisionBlockB64 (t : ℕ) : List ℕ :=
  [1, 0, 1, 1, 0, 1] ++ zeroPairs64 t ++ [1, 1, 1, 1]

/-- Every accepted word begins with a zero or one of the two exact return-block forms. -/
theorem division64_first_return (w : List ℕ) (h : divisionAccepts64 0 w) :
  w=[] ∨
  (∃ v, w=0::v ∧ divisionAccepts64 0 v) ∨
  (∃ v, w=divisionBlockA64++v ∧ divisionAccepts64 0 v) ∨
  (∃ t v, w=divisionBlockB64 t++v ∧ divisionAccepts64 0 v) := by
  cases w with
  | nil => exact Or.inl rfl
  | cons d w =>
    rcases (accept0_cons d w).mp h with ⟨rfl, hw⟩|⟨rfl, hw⟩
    ·
        exact Or.inr (Or.inl ⟨w, rfl, hw⟩)
    ·
        obtain ⟨v, rfl, hv⟩ := (accept1_word w).mp hw
        cases v with
        | nil => simp [divisionAccepts64, divisionRun64] at hv
        | cons e v =>
          rcases (accept3_cons e v).mp hv with ⟨rfl, hv⟩|⟨rfl, hv⟩
          ·
              obtain ⟨z, rfl, hz⟩ := (accept9_suffix v).mp hv
              exact Or.inr (Or.inr (Or.inl ⟨z, rfl, hz⟩))
          ·
              obtain ⟨z, rfl, hz⟩ := (accept10_suffix v).mp hv
              obtain ⟨t, y, hy, hend⟩ := (accept24_loops_iff z).mp hz
              refine Or.inr (Or.inr (Or.inr ⟨t, y, ?_, hend⟩))
              simp [divisionBlockB64, hy, List.append_assoc]

/-- Concatenations of `0`, `100111`, and `101101(00)^t1111`, including the empty word. -/
inductive Division64Word : List ℕ → Prop
  | nil : Division64Word []
  | zero {w : List ℕ} : Division64Word w → Division64Word (0::w)
  | blockA {w : List ℕ} : Division64Word w → Division64Word (divisionBlockA64++w)
  | blockB (t : ℕ) {w : List ℕ} : Division64Word w → Division64Word (divisionBlockB64 t++w)

private theorem divisionBlockA64_returns (w : List ℕ) :
  divisionRun64 0 (divisionBlockA64++w) = divisionRun64 0 w := by
  norm_num [divisionBlockA64, divisionRun64]

private theorem divisionBlockB64_returns (t : ℕ) (w : List ℕ) :
  divisionRun64 0 (divisionBlockB64 t++w) = divisionRun64 0 w := by
  unfold divisionBlockB64
  have hloop : ∀ t w, divisionRun64 24 (zeroPairs64 t++w)=divisionRun64 24 w := by
    intro t
    induction t with
    | zero => intro w; rfl
    | succ t ih => intro w; simpa [zeroPairs64, divisionRun64] using ih w
  simp only [List.append_assoc]
  norm_num [divisionRun64]
  rw [hloop]
  norm_num [divisionRun64]

/-- Complete finite-word language theorem for the exact arithmetic division transducer. -/
theorem division64_accepts_iff_word (w : List ℕ) :
  divisionAccepts64 0 w ↔ Division64Word w := by
  constructor
  ·
      intro h
      have H : ∀ n : ℕ, ∀ w : List ℕ, w.length=n → divisionAccepts64 0 w → Division64Word w := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro w hn hw
          rcases division64_first_return w hw with rfl|⟨v, rfl, hv⟩|⟨v, rfl, hv⟩|⟨t, v, rfl, hv⟩
          ·
              exact Division64Word.nil
          ·
              apply Division64Word.zero
              apply ih v.length (by simp at hn; omega) v rfl hv
          ·
              apply Division64Word.blockA
              apply ih v.length (by simp [divisionBlockA64] at hn; omega) v rfl hv
          ·
              apply Division64Word.blockB t
              apply ih v.length (by simp [divisionBlockB64] at hn; omega) v rfl hv
      exact H w.length w rfl h
  ·
      intro h
      induction h with
      | nil => rfl
      | zero hw ih => simpa [divisionAccepts64, divisionRun64] using ih
      | blockA hw ih => simpa [divisionAccepts64, divisionBlockA64_returns] using ih
      | blockB t hw ih => simpa [divisionAccepts64, divisionBlockB64_returns] using ih

/-- The quotient word of `A` is `000011`. -/
theorem division64_blockA_quotient :
  divisionQuotient64 0 divisionBlockA64 = [0, 0, 0, 0, 1, 1] := by decide +kernel

private theorem division64_quotient_loops (t : ℕ) (w : List ℕ) :
  divisionQuotient64 24 (zeroPairs64 t++w)=oneZeroPairs64 t++divisionQuotient64 24 w := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [zeroPairs64, oneZeroPairs64, divisionQuotient64] using congrArg (fun v => 1::0::v) ih

/-- The quotient word of `B_t` is `000011(10)^t1011`. -/
theorem division64_blockB_quotient (t : ℕ) :
  divisionQuotient64 0 (divisionBlockB64 t) =
    [0, 0, 0, 0, 1, 1] ++ oneZeroPairs64 t ++ [1, 0, 1, 1] := by
  unfold divisionBlockB64
  norm_num [divisionQuotient64]
  rw [division64_quotient_loops]
  norm_num [divisionQuotient64]


private def divisionReachPrefix64 : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 3 => [1, 0]
  | 8 => [1, 0, 1, 1, 0, 1, 0]
  | 9 => [1, 0, 0]
  | 10 => [1, 0, 1]
  | 21 => [1, 0, 0, 1, 1]
  | 24 => [1, 0, 1, 1, 0, 1]
  | 28 => [1, 0, 0, 1]
  | 29 => [1, 0, 1, 1, 0]
  | 31 => [1, 0, 1, 1]
  | _ => []

private def divisionAcceptSuffix64 : ℕ → List ℕ
  | 0 => []
  | 1 => [0, 0, 1, 1, 1]
  | 3 => [0, 1, 1, 1]
  | 8 => [0, 1, 1, 1, 1]
  | 9 => [1, 1, 1]
  | 10 => [1, 0, 1, 1, 1, 1, 1]
  | 21 => [1]
  | 24 => [1, 1, 1, 1]
  | 28 => [1, 1]
  | 29 => [1, 1, 1, 1, 1]
  | 31 => [0, 1, 1, 1, 1, 1]
  | _ => []

private theorem division64_live_witness_certificate :
  ∀ r : Fin 32, r.val ∈ live64 →
    divisionRun64 0 (divisionReachPrefix64 r.val)=some r.val ∧
    divisionRun64 r.val (divisionAcceptSuffix64 r.val)=some 0 := by decide +kernel

private theorem divisionRun64_forward (w : List ℕ) (r t : ℕ) (hr : r <64)
  (hnot : r ∉ [2, 7, 22, 32]) (h : divisionRun64 r w=some t) :
  t <64 ∧ t ∉ [2, 7, 22, 32] := by
  induction w generalizing r with
  | nil =>
    have heq : r=t := by simpa [divisionRun64] using h
    simpa [←heq] using And.intro hr hnot
  | cons d w ih =>
    by_cases hd : d ≤1 ∧ (3*r+d)/64 ≤1
    ·
        rw [divisionRun64, if_pos hd] at h
        exact ih _ (Nat.mod_lt _ (by decide))
            (division64_forward_certificate ⟨r, hr⟩ ⟨d, by omega⟩ hnot hd.2) h
    ·
        simp [divisionRun64, hd] at h

/-- Exactly the remainders occurring on finite accepted zero-to-zero division paths. -/
theorem division64_live_remainders_iff (r : ℕ) :
  r ∈ live64 ↔ ∃ u v : List ℕ, 
      divisionRun64 0 u=some r ∧ divisionRun64 r v=some 0 := by
  constructor
  ·
      intro hr
      have hw := division64_live_witness_certificate ⟨r, live64_lt r hr⟩ hr
      exact ⟨divisionReachPrefix64 r, divisionAcceptSuffix64 r, hw⟩
  ·
      rintro ⟨u, v, hu, hv⟩
      obtain ⟨hr, hnot⟩ := divisionRun64_forward u 0 r (by decide) (by decide) hu
      exact division64_accepted_live v r hr hnot hv

/- ## Ordinary integer meaning of the transducer -/

/-- Interpret a word most significant first, allowing leading zeros. -/
def ternaryValueMSF (w : List ℕ) : ℕ := Nat.ofDigits 3 w.reverse

private theorem ternaryValueMSF_cons (d : ℕ) (w : List ℕ) :
  ternaryValueMSF (d::w)=d*3^w.length+ternaryValueMSF w := by
  unfold ternaryValueMSF
  rw [Nat.ofDigits_reverse_cons]
  ring

/-- The final remainder of ordinary division, without digit restrictions. -/
def divisionRemainder64 (r : ℕ) : List ℕ → ℕ
  | [] => r
  | d::w => divisionRemainder64 ((3*r+d)%64) w

private theorem mem_zero_one_iff (d : ℕ) : d ∈ [0, 1] ↔ d ≤1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The operational test is exactly the input/output alphabet test, with the stated remainder. -/
theorem divisionRun64_spec (r t : ℕ) (w : List ℕ) :
  divisionRun64 r w=some t ↔
      w ⊆ [0, 1] ∧ divisionQuotient64 r w ⊆ [0, 1] ∧ divisionRemainder64 r w=t := by
  induction w generalizing r with
  | nil => simp [divisionRun64, divisionQuotient64, divisionRemainder64]
  | cons d w ih =>
    by_cases hd : d ≤1 ∧ (3*r+d)/64 ≤1
    ·
        rw [divisionRun64, if_pos hd, ih]
        simp only [divisionQuotient64, divisionRemainder64, 
            List.cons_subset, mem_zero_one_iff, hd.1, hd.2, true_and]
    ·
        simp only [divisionRun64, if_neg hd, reduceCtorEq, false_iff, 
            divisionQuotient64, divisionRemainder64, List.cons_subset, mem_zero_one_iff]
        rintro ⟨⟨h1, _⟩, ⟨h2, _⟩, _⟩
        exact hd ⟨h1, h2⟩

private theorem divisionRemainder64_lt (r : ℕ) (w : List ℕ) (hr : r <64) :
  divisionRemainder64 r w <64 := by
  induction w generalizing r with
  | nil => exact hr
  | cons d w ih => exact ih _ (Nat.mod_lt _ (by decide))

private theorem divisionQuotient64_length (r : ℕ) (w : List ℕ) :
  (divisionQuotient64 r w).length=w.length := by
  induction w generalizing r with
  | nil => rfl
  | cons d w ih => simpa [divisionQuotient64] using ih ((3*r+d)%64)

/-- Exact division identity for every finite input word. -/
theorem division64_value_identity (r : ℕ) (w : List ℕ) :
  64*ternaryValueMSF (divisionQuotient64 r w)+divisionRemainder64 r w =
    3^w.length*r+ternaryValueMSF w := by
  induction w generalizing r with
  | nil => simp [divisionQuotient64, divisionRemainder64, ternaryValueMSF]
  | cons d w ih =>
    simp only [divisionQuotient64, divisionRemainder64, ternaryValueMSF_cons, 
        List.length_cons, divisionQuotient64_length]
    have hd := Nat.mod_add_div (3*r+d) 64
    have hm := congrArg (fun x : ℕ => 3^w.length*x) hd
    dsimp at hm
    have ht := ih ((3*r+d)%64)
    rw [pow_succ]
    nlinarith

/-- The transducer really computes ordinary integer quotient and remainder. -/
theorem division64_quotient_remainder (w : List ℕ) :
  ternaryValueMSF (divisionQuotient64 0 w)=ternaryValueMSF w/64 ∧
  divisionRemainder64 0 w=ternaryValueMSF w%64 := by
  have hid := division64_value_identity 0 w
  have hr := divisionRemainder64_lt 0 w (by decide)
  simp only [mul_zero, zero_add] at hid
  constructor
  ·
      symm
      apply Nat.div_eq_of_lt_le <;> omega
  ·
      omega

private theorem reverse_subset_zero_one (w : List ℕ) :
  w.reverse ⊆ [0, 1] ↔ w ⊆ [0, 1] := by
  simp only [List.subset_def, List.mem_reverse]

private theorem cantor_ofDigits_iff_bounded (w : List ℕ)
  (hb : ∀ d ∈ w, d <3) : cantor (Nat.ofDigits 3 w) ↔ w ⊆ [0, 1] := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    have hd := hb d List.mem_cons_self
    have hwt : ∀ e ∈ w, e <3 := fun e he => hb e (List.mem_cons_of_mem _ he)
    rw [Nat.ofDigits_cons, cantor_iff_digit_and_div]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt hd, 
      Nat.add_mul_div_left _ _ (by decide : 0<3), Nat.div_eq_of_lt hd, zero_add, 
      ih hwt, List.cons_subset, mem_zero_one_iff]

private theorem divisionQuotient64_bounded (w : List ℕ) (r : ℕ) (hr : r <64)
  (hw : w ⊆ [0, 1]) : ∀ q ∈ divisionQuotient64 r w, q <3 := by
  induction w generalizing r with
  | nil => simp [divisionQuotient64]
  | cons d w ih =>
    have hd : d ≤1 := (mem_zero_one_iff d).mp (hw List.mem_cons_self)
    have hwt : w ⊆ [0, 1] := fun e he => hw (List.mem_cons_of_mem _ he)
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    ·
        apply (Nat.div_lt_iff_lt_mul (by decide : 0<64)).mpr
        omega
    ·
        exact ih _ (Nat.mod_lt _ (by decide)) hwt _ hq

/-- Exact integer meaning of acceptance: a Cantor word represents a multiple of 64
whose quotient is also Cantor.  Leading zero padding is harmless. -/
theorem division64_accepts_iff_integer (w : List ℕ) (hw : w ⊆ [0, 1]) :
  divisionAccepts64 0 w ↔
    64 ∣ ternaryValueMSF w ∧ cantor (ternaryValueMSF w /64) := by
  have hqr := division64_quotient_remainder w
  have hqb := divisionQuotient64_bounded w 0 (by decide) hw
  have hqreverse : ∀ d ∈ (divisionQuotient64 0 w).reverse, d <3 := by
    simpa only [List.mem_reverse] using hqb
  have hc : cantor (ternaryValueMSF (divisionQuotient64 0 w)) ↔
      divisionQuotient64 0 w ⊆ [0, 1] := by
    unfold ternaryValueMSF
    rw [cantor_ofDigits_iff_bounded _ hqreverse, reverse_subset_zero_one]
  unfold divisionAccepts64
  rw [divisionRun64_spec]
  simp only [hw, true_and, ←hc, hqr, Nat.dvd_iff_mod_eq_zero, and_comm]

/-- The exact regular language for canonical ternary expansions of divisible Cantor integers. -/
theorem division64_digits_iff_word (N : ℕ) (hN : cantor N) :
  Division64Word (Nat.digits 3 N).reverse ↔ 64 ∣ N ∧ cantor (N/64) := by
  rw [←division64_accepts_iff_word]
  have hw : (Nat.digits 3 N).reverse ⊆ [0, 1] := (reverse_subset_zero_one _).mpr hN
  rw [division64_accepts_iff_integer _ hw]
  simp [ternaryValueMSF, Nat.ofDigits_digits]


/-- An individual return block of the accepted language. -/
def Division64Block (w : List ℕ) : Prop :=
  w=[0] ∨ w=divisionBlockA64 ∨ ∃ t, w=divisionBlockB64 t

private theorem division64_word_iff_blocks (w : List ℕ) :
  Division64Word w ↔ ∃ blocks : List (List ℕ), 
      (∀ b ∈ blocks, Division64Block b) ∧ blocks.flatten=w := by
  constructor
  ·
      intro h
      induction h with
      | nil => exact ⟨[], by simp, rfl⟩
      | zero hw ih =>
        obtain ⟨bs, hbs, rfl⟩ := ih
        refine ⟨[0]::bs, ?_, rfl⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        ·
            exact Or.inl rfl
        ·
            exact hbs _ hb
      | blockA hw ih =>
        obtain ⟨bs, hbs, rfl⟩ := ih
        refine ⟨divisionBlockA64::bs, ?_, rfl⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        ·
            exact Or.inr (Or.inl rfl)
        ·
            exact hbs _ hb
      | blockB t hw ih =>
        obtain ⟨bs, hbs, rfl⟩ := ih
        refine ⟨divisionBlockB64 t::bs, ?_, rfl⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        ·
            exact Or.inr (Or.inr ⟨t, rfl⟩)
        ·
            exact hbs _ hb
  ·
      rintro ⟨bs, hbs, rfl⟩
      induction bs with
      | nil => exact Division64Word.nil
      | cons b bs ih =>
        have ht := ih (fun c hc => hbs _ (List.mem_cons_of_mem _ hc))
        rcases hbs b List.mem_cons_self with rfl|rfl|⟨t, rfl⟩
        ·
            exact Division64Word.zero ht
        ·
            exact Division64Word.blockA ht
        ·
            exact Division64Word.blockB t ht

/-- An explicit concatenation characterization of all finite accepted words. -/
theorem division64_accepts_iff_blocks (w : List ℕ) :
  divisionAccepts64 0 w ↔ ∃ blocks : List (List ℕ), 
      (∀ b ∈ blocks, Division64Block b) ∧ blocks.flatten=w :=
  (division64_accepts_iff_word w).trans (division64_word_iff_blocks w)

/-- Full integer-pair characterization by the exact return-block language. -/
theorem multiplier64_pair_iff_word (M : ℕ) :
  cantor M ∧ cantor (64*M) ↔ Division64Word (Nat.digits 3 (64*M)).reverse := by
  constructor
  ·
      rintro ⟨hM, h64⟩
      apply (division64_digits_iff_word (64*M) h64).mpr
      refine ⟨⟨M, rfl⟩, ?_⟩
      rw [Nat.mul_div_cancel_left M (by decide : 0<64)]
      exact hM
  ·
      intro hw
      have ha := (division64_accepts_iff_word _).mpr hw
      have hs := (divisionRun64_spec 0 0 _).mp ha
      have h64 : cantor (64*M) := (reverse_subset_zero_one _).mp hs.1
      have hM := ((division64_digits_iff_word (64*M) h64).mp hw).2
      rw [Nat.mul_div_cancel_left M (by decide : 0<64)] at hM
      exact ⟨hM, h64⟩

/-- Word concatenation composes division runs. -/
theorem divisionRun64_append (r : ℕ) (u v : List ℕ) :
  divisionRun64 r (u++v) = (divisionRun64 r u).bind (fun t => divisionRun64 t v) := by
  induction u generalizing r with
  | nil => rfl
  | cons d u ih =>
    by_cases hd : d ≤1 ∧ (3*r+d)/64 ≤1
    ·
        simpa [divisionRun64, hd] using ih ((3*r+d)%64)
    ·
        simp [divisionRun64, hd]

private theorem divisionQuotient64_append (r : ℕ) (u v : List ℕ) :
  divisionQuotient64 r (u++v) =
    divisionQuotient64 r u++divisionQuotient64 (divisionRemainder64 r u) v := by
  induction u generalizing r with
  | nil => rfl
  | cons d u ih =>
      simpa [divisionQuotient64, divisionRemainder64] using
          congrArg (fun w => (3*r+d)/64::w) (ih ((3*r+d)%64))

/-- Quotients of accepted return-block concatenations concatenate with their zero padding. -/
theorem division64_quotient_concatenation (u v : List ℕ) (hu : divisionAccepts64 0 u) :
  divisionQuotient64 0 (u++v)=divisionQuotient64 0 u++divisionQuotient64 0 v := by
  have hs := (divisionRun64_spec 0 0 u).mp hu
  rw [divisionQuotient64_append, hs.2.2]

end Erdos406.Descent
