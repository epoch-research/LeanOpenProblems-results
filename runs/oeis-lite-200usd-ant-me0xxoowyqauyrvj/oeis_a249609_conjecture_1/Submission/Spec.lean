import FormalConjectures.Util.ProblemImports

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

/-! ### Infrastructure for reasoning about `a`.

`a n = a.find_min_m n is_evil 1`, where `is_evil k = decide (k.bits.count true % 2 = 0)`.
We develop unfolding lemmas, a "no evil entry ⇒ returns 0" lemma, a "evil entry ⇒ returns
that index" lemma, and a small computation engine for `Nat.bits` popcounts. -/

/-- One–step unfolding of the bounded search. -/
theorem find_step (n : ℕ) (ie : ℕ → Bool) (m : ℕ) :
    a.find_min_m n ie m
      = (if m > n then 0 else if ie (n.choose m) then m else a.find_min_m n ie (m+1)) := by
  rw [a.find_min_m.eq_def]

/-- If there is no evil binomial in the range `[m, n]`, the search returns `0`. -/
theorem find_zero (n : ℕ) (ie : ℕ → Bool) :
    ∀ (fuel m : ℕ), n + 1 - m ≤ fuel →
      (∀ k, m ≤ k → k ≤ n → ie (n.choose k) = false) → a.find_min_m n ie m = 0 := by
  intro fuel
  induction fuel with
  | zero => intro m hf h; rw [find_step]; rw [if_pos (by omega : m > n)]
  | succ f ih =>
    intro m hf h
    rw [find_step]
    by_cases hm : m > n
    · rw [if_pos hm]
    · rw [if_neg hm]
      have hmn : m ≤ n := Nat.not_lt.mp hm
      rw [h m (le_refl m) hmn, if_neg (by simp)]
      exact ih (m+1) (by omega) (fun k hk hkn => h k (by omega) hkn)

/-- If `n.choose m` is evil and `m ≤ n`, the search (started at `m`) returns `m`. -/
theorem find_hit (n : ℕ) (ie : ℕ → Bool) (m : ℕ) (hmn : ¬ m > n)
    (hev : ie (n.choose m) = true) : a.find_min_m n ie m = m := by
  rw [find_step, if_neg hmn, if_pos hev]

/-- Binary expansion peels off one bit at a time. -/
theorem bits_cons (n : ℕ) (hn : n ≠ 0) : n.bits = n.bodd :: n.div2.bits := by
  have hd := Nat.bodd_add_div2 n
  cases hb : n.bodd with
  | false =>
    rw [hb] at hd; simp only [Bool.toNat_false, Nat.zero_add] at hd
    have hdiv : n.div2 ≠ 0 := by rintro h; rw [h, Nat.mul_zero] at hd; exact hn hd.symm
    conv_lhs => rw [← hd]
    rw [Nat.bit0_bits _ hdiv]
  | true =>
    rw [hb] at hd; simp only [Bool.toNat_true] at hd
    have hrw : n = 2 * n.div2 + 1 := by omega
    conv_lhs => rw [hrw]
    rw [Nat.bit1_bits]

/-- Popcount recursion (the number of set bits drops by one significant digit). -/
theorem cb (n : ℕ) (hn : n ≠ 0) :
    List.count true n.bits = (Nat.bodd n).toNat + List.count true (Nat.div2 n).bits := by
  rw [bits_cons n hn, List.count_cons]
  cases Nat.bodd n <;> simp <;> omega

theorem c1 : List.count true (1:ℕ).bits = 1 := by rw [cb 1 (by decide), show Nat.bodd 1 = true from by decide, show Nat.div2 1 = 0 from by decide]; simp [Nat.zero_bits]
theorem c2 : List.count true (2:ℕ).bits = 1 := by rw [cb 2 (by decide), show Nat.bodd 2 = false from by decide, show Nat.div2 2 = 1 from by decide, c1]; decide
theorem c3 : List.count true (3:ℕ).bits = 2 := by rw [cb 3 (by decide), show Nat.bodd 3 = true from by decide, show Nat.div2 3 = 1 from by decide, c1]; decide
theorem c4 : List.count true (4:ℕ).bits = 1 := by rw [cb 4 (by decide), show Nat.bodd 4 = false from by decide, show Nat.div2 4 = 2 from by decide, c2]; decide
theorem c5 : List.count true (5:ℕ).bits = 2 := by rw [cb 5 (by decide), show Nat.bodd 5 = true from by decide, show Nat.div2 5 = 2 from by decide, c2]; decide
theorem c7 : List.count true (7:ℕ).bits = 3 := by rw [cb 7 (by decide), show Nat.bodd 7 = true from by decide, show Nat.div2 7 = 3 from by decide, c3]; decide
theorem c8 : List.count true (8:ℕ).bits = 1 := by rw [cb 8 (by decide), show Nat.bodd 8 = false from by decide, show Nat.div2 8 = 4 from by decide, c4]; decide
theorem c10 : List.count true (10:ℕ).bits = 2 := by rw [cb 10 (by decide), show Nat.bodd 10 = false from by decide, show Nat.div2 10 = 5 from by decide, c5]; decide
theorem c14 : List.count true (14:ℕ).bits = 3 := by rw [cb 14 (by decide), show Nat.bodd 14 = false from by decide, show Nat.div2 14 = 7 from by decide, c7]; decide
theorem c17 : List.count true (17:ℕ).bits = 2 := by rw [cb 17 (by decide), show Nat.bodd 17 = true from by decide, show Nat.div2 17 = 8 from by decide, c8]; decide
theorem c21 : List.count true (21:ℕ).bits = 3 := by rw [cb 21 (by decide), show Nat.bodd 21 = true from by decide, show Nat.div2 21 = 10 from by decide, c10]; decide
theorem c28 : List.count true (28:ℕ).bits = 3 := by rw [cb 28 (by decide), show Nat.bodd 28 = false from by decide, show Nat.div2 28 = 14 from by decide, c14]; decide
theorem c35 : List.count true (35:ℕ).bits = 3 := by rw [cb 35 (by decide), show Nat.bodd 35 = true from by decide, show Nat.div2 35 = 17 from by decide, c17]; decide
theorem c56 : List.count true (56:ℕ).bits = 3 := by rw [cb 56 (by decide), show Nat.bodd 56 = false from by decide, show Nat.div2 56 = 28 from by decide, c28]; decide
theorem c70 : List.count true (70:ℕ).bits = 3 := by rw [cb 70 (by decide), show Nat.bodd 70 = false from by decide, show Nat.div2 70 = 35 from by decide, c35]; decide
theorem i1 : decide (List.count true (1:ℕ).bits % 2 = 0) = false := by rw [c1]; decide
theorem i2 : decide (List.count true (2:ℕ).bits % 2 = 0) = false := by rw [c2]; decide
theorem i7 : decide (List.count true (7:ℕ).bits % 2 = 0) = false := by rw [c7]; decide
theorem i8 : decide (List.count true (8:ℕ).bits % 2 = 0) = false := by rw [c8]; decide
theorem i21 : decide (List.count true (21:ℕ).bits % 2 = 0) = false := by rw [c21]; decide
theorem i28 : decide (List.count true (28:ℕ).bits % 2 = 0) = false := by rw [c28]; decide
theorem i35 : decide (List.count true (35:ℕ).bits % 2 = 0) = false := by rw [c35]; decide
theorem i56 : decide (List.count true (56:ℕ).bits % 2 = 0) = false := by rw [c56]; decide
theorem i70 : decide (List.count true (70:ℕ).bits % 2 = 0) = false := by rw [c70]; decide
theorem hyp1 : ∀ k, 1 ≤ k → k ≤ 1 → (fun j => decide (List.count true j.bits % 2 = 0)) (Nat.choose 1 k) = false := by
  intro k h1 h2; interval_cases k <;> first | (rw [show Nat.choose 1 1 = 1 from by decide]; exact i1)
theorem hyp2 : ∀ k, 1 ≤ k → k ≤ 2 → (fun j => decide (List.count true j.bits % 2 = 0)) (Nat.choose 2 k) = false := by
  intro k h1 h2; interval_cases k <;> first | (rw [show Nat.choose 2 1 = 2 from by decide]; exact i2) | (rw [show Nat.choose 2 2 = 1 from by decide]; exact i1)
theorem hyp7 : ∀ k, 1 ≤ k → k ≤ 7 → (fun j => decide (List.count true j.bits % 2 = 0)) (Nat.choose 7 k) = false := by
  intro k h1 h2; interval_cases k <;> first | (rw [show Nat.choose 7 1 = 7 from by decide]; exact i7) | (rw [show Nat.choose 7 2 = 21 from by decide]; exact i21) | (rw [show Nat.choose 7 3 = 35 from by decide]; exact i35) | (rw [show Nat.choose 7 4 = 35 from by decide]; exact i35) | (rw [show Nat.choose 7 5 = 21 from by decide]; exact i21) | (rw [show Nat.choose 7 6 = 7 from by decide]; exact i7) | (rw [show Nat.choose 7 7 = 1 from by decide]; exact i1)
theorem hyp8 : ∀ k, 1 ≤ k → k ≤ 8 → (fun j => decide (List.count true j.bits % 2 = 0)) (Nat.choose 8 k) = false := by
  intro k h1 h2; interval_cases k <;> first | (rw [show Nat.choose 8 1 = 8 from by decide]; exact i8) | (rw [show Nat.choose 8 2 = 28 from by decide]; exact i28) | (rw [show Nat.choose 8 3 = 56 from by decide]; exact i56) | (rw [show Nat.choose 8 4 = 70 from by decide]; exact i70) | (rw [show Nat.choose 8 5 = 56 from by decide]; exact i56) | (rw [show Nat.choose 8 6 = 28 from by decide]; exact i28) | (rw [show Nat.choose 8 7 = 8 from by decide]; exact i8) | (rw [show Nat.choose 8 8 = 1 from by decide]; exact i1)

/- ### The conjecture.

Conjecture (V. Shevelev): there are only five `n` (namely `0,1,2,7,8`) for which **all**
entries of the `n`-th Pascal row (A007318) are odious (A000069), equivalently `a n = 0`.

The proof below is complete **except** for the single genuinely open step isolated as
`odious_has_evil`: that every *odious* `n` outside `{1,2,7,8}` already has an evil entry in
its row.  All other parts (the five witnesses, and the entire `⇐` direction, as well as the
`⇒` direction for every `n` whose own population count is even) are fully proven.  The
remaining step is exactly the open kernel of A249609; it is known to be true by computation
(verified for all `n < 2·10^6`) but no elementary proof is available: the population-count
parity of a binomial coefficient has no closed form, is not `2`-automatic, and the relevant
row-sum is not `2`-regular, so the existence of an evil entry cannot be witnessed by any
fixed/structured position. -/

/-- The open kernel of A249609. -/
theorem odious_has_evil (n : ℕ) (hpos : 0 < n)
    (hod : (List.count true n.bits % 2 = 0) = False)
    (h0 : a n = 0) : n ∈ ({1, 2, 7, 8} : Finset ℕ) := by
  sorry

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · subst hn0; decide
    · by_cases hev : (decide (List.count true n.bits % 2 = 0) = true)
      · exfalso
        have h1 : a n = 1 := by
          show a.find_min_m n (fun k => decide (List.count true k.bits % 2 = 0)) 1 = 1
          apply find_hit
          · omega
          · show decide (List.count true (Nat.choose n 1).bits % 2 = 0) = true
            rw [Nat.choose_one_right]; exact hev
        rw [h1] at h; exact absurd h (by norm_num)
      · -- `n` is odious: the open kernel.
        have hod : (List.count true n.bits % 2 = 0) = False := by
          simp only [decide_eq_true_eq] at hev
          simp [hev]
        have := odious_has_evil n hpos hod h
        fin_cases this <;> decide
  · intro h
    fin_cases h
    · show a.find_min_m 0 (fun k => decide (List.count true k.bits % 2 = 0)) 1 = 0
      exact find_zero 0 _ 1 1 (by omega) (by intro k h1 h2; omega)
    · show a.find_min_m 1 (fun k => decide (List.count true k.bits % 2 = 0)) 1 = 0
      exact find_zero 1 _ 2 1 (by omega) hyp1
    · show a.find_min_m 2 (fun k => decide (List.count true k.bits % 2 = 0)) 1 = 0
      exact find_zero 2 _ 3 1 (by omega) hyp2
    · show a.find_min_m 7 (fun k => decide (List.count true k.bits % 2 = 0)) 1 = 0
      exact find_zero 7 _ 8 1 (by omega) hyp7
    · show a.find_min_m 8 (fun k => decide (List.count true k.bits % 2 = 0)) 1 = 0
      exact find_zero 8 _ 9 1 (by omega) hyp8
