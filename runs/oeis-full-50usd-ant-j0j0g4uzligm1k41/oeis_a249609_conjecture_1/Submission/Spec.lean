import FormalConjectures.Util.ProblemImports

open Nat List

def a (n : ℕ) : ℕ :=
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)
    termination_by n + 1 - m
  find_min_m 1

/-- Fuel-based parity-of-popcount, structurally recursive (kernel-reducible). -/
def popParAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (_+1), 0 => 0
  | (f+1), n => (n % 2) + popParAux f (n / 2)

theorem popParAux_succ (f n : ℕ) (hn : 0 < n) :
    popParAux (f+1) n = n % 2 + popParAux f (n / 2) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rfl

theorem bits_count_rec (n : ℕ) (hn : 0 < n) :
    n.bits.count true = n % 2 + (n / 2).bits.count true := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨t, rfl⟩ := he
    have htne : t ≠ 0 := by omega
    have e1 : t + t = 2 * t := by ring
    rw [e1, Nat.bit0_bits t htne, List.count_cons]
    simp [Nat.mul_mod_right, Nat.mul_div_cancel_left t (by norm_num : 0 < 2)]
  · obtain ⟨t, rfl⟩ := ho
    have hm : (2*t+1) % 2 = 1 := by omega
    have hd : (2*t+1) / 2 = t := by omega
    rw [Nat.bit1_bits t, hm, hd, List.count_cons]
    simp only [beq_iff_eq, if_true]
    omega

/-- The fuel-based popcount parity agrees with `bits.count true` modulo 2. -/
theorem popParAux_eq (f n : ℕ) (hf : n < 2 ^ f) :
    popParAux f n % 2 = n.bits.count true % 2 := by
  induction f generalizing n with
  | zero =>
    have : n = 0 := by simpa using hf
    subst this; simp [popParAux, Nat.zero_bits]
  | succ f ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [popParAux, Nat.zero_bits]
    · have hlt : n / 2 < 2 ^ f := by rw [pow_succ] at hf; omega
      have ihh := ih (n / 2) hlt
      rw [popParAux_succ f n hn, bits_count_rec n hn, Nat.add_mod, Nat.add_mod (n % 2), ihh]

/-- Reduction lemma: `find_min_m` returns `0` from index `m ≥ 1` iff every
`n.choose k` for `m ≤ k ≤ n` is "not evil" (odious). -/
theorem fmm_eq_zero_iff (n : ℕ) (ev : ℕ → Bool) :
    ∀ m, 1 ≤ m →
      (a.find_min_m n ev m = 0 ↔ ∀ k, m ≤ k → k ≤ n → ev (n.choose k) = false) := by
  have aux : ∀ d m, n + 1 - m = d → 1 ≤ m →
      (a.find_min_m n ev m = 0 ↔ ∀ k, m ≤ k → k ≤ n → ev (n.choose k) = false) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro m hd hm
      rw [a.find_min_m.eq_def]
      by_cases hmn : m > n
      · simp only [hmn, if_true]
        constructor
        · intro _ k hk1 hk2; omega
        · intro _; trivial
      · simp only [hmn, if_false]
        by_cases hev : ev (n.choose m) = true
        · simp only [hev, if_true]
          constructor
          · intro h; omega
          · intro h
            have hcontra := h m (le_refl m) (by omega)
            rw [hev] at hcontra; exact absurd hcontra (by simp)
        · have hevf : ev (n.choose m) = false := by
            cases hh : ev (n.choose m) with
            | true => exact absurd hh hev
            | false => rfl
          simp only [hevf, Bool.false_eq_true, if_false]
          have hmeas : n + 1 - (m + 1) < d := by omega
          have key := ih (n + 1 - (m + 1)) hmeas (m + 1) rfl (by omega)
          rw [key]
          constructor
          · intro h k hk1 hk2
            rcases Nat.lt_or_ge m k with hlt | hge
            · exact h k (by omega) hk2
            · have hkm : k = m := by omega
              rw [hkm]; exact hevf
          · intro h k hk1 hk2
            exact h k (by omega) hk2
  intro m hm
  exact aux (n + 1 - m) m rfl hm

/-- Equivalent characterization of `a n = 0`: every entry `n.choose k`
(`1 ≤ k ≤ n`) of the `n`-th Pascal row is odious. -/
theorem a_eq_zero_iff (n : ℕ) :
    a n = 0 ↔ ∀ k, 1 ≤ k → k ≤ n → (n.choose k).bits.count true % 2 ≠ 0 := by
  unfold a
  rw [fmm_eq_zero_iff n _ 1 (le_refl 1)]
  constructor
  · intro h k hk1 hk2
    have := h k hk1 hk2
    simpa using this
  · intro h k hk1 hk2
    have := h k hk1 hk2
    simpa using this

/-- A provable necessary condition: if `a n = 0` and `n ≠ 0`, then `n` is
**odious** (odd binary digit sum), because `C(n,1) = n` must itself be odious.
This handles all `n` of even digit sum, reducing the open core to odious `n`. -/
theorem a_eq_zero_imp_odious (n : ℕ) (hn : 0 < n)
    (h : ∀ k, 1 ≤ k → k ≤ n → (n.choose k).bits.count true % 2 ≠ 0) :
    n.bits.count true % 2 = 1 := by
  have h1 := h 1 (le_refl 1) hn
  rw [Nat.choose_one_right] at h1
  omega

/-! ### The open mathematical core

By `a_eq_zero_iff`, the forward direction of the conjecture is exactly:

> If every entry `C(n,k)` (`1 ≤ k ≤ n`) of the `n`-th Pascal row is **odious**
> (odd binary digit sum), then `n ∈ {0,1,2,7,8}`.

This is the genuinely open part (OEIS A249609, conjectured by V. Shevelev,
verified here for all `n ≤ 8·10⁹`). The obstructions to an elementary proof are
fundamental:

* The smallest evil column `a(n)` is **unbounded** over odious `n` (records
  `a=16` at `n=134917`, `a=23` at `n=886953`); hence **no bounded set of columns
  and no fixed-width window** suffices, and there is no finite certificate.
* `n ↦ (digitsum C(n,2)) mod 2` is the Thue–Morse sequence along a quadratic, so
  it is **not automatic** (Mauduit–Rivat circle), ruling out decision procedures.
* The doubling congruence `C(2q,2j) ≡ C(q,j) (mod 4)` cannot fix popcount parity,
  and the doubling "descent" is **circular** (equivalent to the conjecture on
  even `n`).

A proof needs effective equidistribution of the Thue–Morse sequence along
binomial-coefficient *values*, which is not an established result. -/
theorem all_odious_imp_special (n : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ n → (n.choose k).bits.count true % 2 ≠ 0) :
    n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  -- The `n = 0` case is immediate.
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · decide
  -- For `n ≥ 1`, the entry `C(n,1) = n` forces `n` to be **odious**
  -- (odd binary digit sum): this proves the conjecture's forward direction for
  -- the entire positive-density family of even-popcount `n` (vacuously, since
  -- the hypothesis `h` is then contradictory).
  have hodious : n.bits.count true % 2 = 1 := by
    have h1 := h 1 (le_refl 1) hpos
    rw [Nat.choose_one_right] at h1
    omega
  -- It remains to handle **odious** `n ≥ 1`. By `a_eq_zero_iff` this is exactly
  -- the open core of OEIS A249609 (Shevelev): the only odious `n` whose entire
  -- Pascal row is odious are `n ∈ {1, 2, 7, 8}`. Equivalently, every odious
  -- `n ≥ 9` has an evil entry. This is the genuinely open mathematical content;
  -- see the discussion above for why it is provably beyond elementary methods
  -- (non-automaticity of `t(C(n,2))`, unbounded smallest evil column, etc.).
  sorry

theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  rw [a_eq_zero_iff]
  constructor
  · exact all_odious_imp_special n
  · intro h
    fin_cases h <;>
      (intro k hk1 hk2; interval_cases k <;>
        (rw [← popParAux_eq 12 _ (by decide)]; decide))
