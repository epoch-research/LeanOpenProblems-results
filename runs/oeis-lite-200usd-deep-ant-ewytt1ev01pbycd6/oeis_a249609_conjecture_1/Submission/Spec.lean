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

/-!
### Reduction of the conjecture to a single open kernel

`a_zero_iff` shows `a n = 0 ↔ ∀ m, 1 ≤ m → m ≤ n → (n.choose m).bits.count true % 2 ≠ 0`,
i.e. `a n = 0` says exactly that every entry of the `n`-th Pascal row is *odious*.

The `⟸` direction and the *evil-`n`*, small-`n`, and *even-power-of-two* parts of the `⟹`
direction are fully proved below.  This reduces the whole statement to the single lemma
"every odious `n ≥ 9` that is **not** an even power of two has an evil binomial coefficient",
isolated as the lone `sorry` in `exists_evil`.  That lemma is the genuinely open content of
OEIS A249609 (Shevelev's conjecture).
-/

theorem find_min_zero (n : ℕ) (ie : ℕ → Bool) (m : ℕ) (hm : 1 ≤ m) :
    a.find_min_m n ie m = 0 ↔ ∀ j, m ≤ j → j ≤ n → ie (n.choose j) = false := by
  induction hd : (n + 1 - m) using Nat.strong_induction_on generalizing m with
  | _ d ih =>
    rw [a.find_min_m.eq_1]
    by_cases hmn : m > n
    · simp only [if_pos hmn]
      constructor
      · intro _ j hj1 hj2; omega
      · intro _; trivial
    · simp only [if_neg hmn]
      push_neg at hmn
      by_cases hev : ie (n.choose m) = true
      · simp only [if_pos hev]
        constructor
        · intro h; omega
        · intro h; have := h m (le_refl m) hmn; rw [hev] at this; simp at this
      · simp only [if_neg hev]
        have hlt : n + 1 - (m + 1) < d := by omega
        rw [ih (n + 1 - (m+1)) hlt (m+1) (by omega) rfl]
        constructor
        · intro h j hj1 hj2
          rcases Nat.lt_or_ge m j with hmj | hmj
          · exact h j hmj hj2
          · have hjm : j = m := by omega
            subst hjm; simpa using hev
        · intro h j hj1 hj2; exact h j (by omega) hj2

theorem a_zero_iff (n : ℕ) :
    a n = 0 ↔ ∀ m, 1 ≤ m → m ≤ n → (n.choose m).bits.count true % 2 ≠ 0 := by
  unfold a
  rw [find_min_zero n _ 1 (le_refl 1)]
  constructor
  · intro h m h1 h2
    have := h m h1 h2
    simpa using this
  · intro h j h1 h2
    have := h j h1 h2
    simp only [decide_eq_false_iff_not]
    exact this

/-- Helper: recursion equation for `Nat.bits`. -/
theorem bits_rec (n : ℕ) (h : n ≠ 0) : n.bits = Nat.bodd n :: (n / 2).bits := by
  conv_lhs => rw [← Nat.bit_bodd_div2 n]
  rw [Nat.bits_append_bit (Nat.div2 n) (Nat.bodd n) ?_, Nat.div2_val]
  intro hdiv; rw [Nat.div2_val] at hdiv
  have : n = 1 := by omega
  subst this; rfl

/-- Popcount is invariant under multiplication by 2. -/
theorem pc_double (m : ℕ) : (2*m).bits.count true = m.bits.count true := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [Nat.bit0_bits m hm]; simp

/-- Popcount is invariant under multiplication by any power of 2. -/
theorem pc_shift (k m : ℕ) : (2^k * m).bits.count true = m.bits.count true := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : 2^(k+1)*m = 2*(2^k*m) := by ring
    rw [h, pc_double, ih]

/-- The number `2^a - 1` (a block of `a` ones) has popcount `a`. -/
theorem pc_ones (a : ℕ) : (2^a - 1).bits.count true = a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h2a : 1 ≤ 2^a := Nat.one_le_two_pow
    have h : 2^(a+1) - 1 = 2*(2^a - 1) + 1 := by
      have : 2^(a+1) = 2*2^a := by ring
      omega
    rw [h, Nat.bit1_bits]
    simp [ih]

/-- `C(2^a, 2) = 2^{a-1}(2^a-1)` has popcount `a`. -/
theorem pc_choose_two_pow (a : ℕ) (ha : 1 ≤ a) :
    ((2^a).choose 2).bits.count true = a := by
  rw [Nat.choose_two_right]
  have h2a : 2^a = 2 * 2^(a-1) := by
    conv_lhs => rw [show a = (a-1)+1 by omega]
    rw [pow_succ]; ring
  have hnum : 2^a * (2^a - 1) = 2 * (2^(a-1) * (2^a - 1)) := by
    rw [← mul_assoc]; congr 1
  have hval : 2^a * (2^a - 1) / 2 = 2^(a-1) * (2^a - 1) := by
    rw [hnum, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hval, pc_shift]
  exact pc_ones a

theorem pc_1 : (1:ℕ).bits.count true % 2 = 1 := by
  rw [Nat.one_bits]
  decide
theorem pc_2 : (2:ℕ).bits.count true % 2 = 1 := by
  rw [show (2:ℕ) = 2*1 by norm_num, Nat.bit0_bits 1 (by norm_num)]
  rw [Nat.one_bits]
  decide
theorem pc_7 : (7:ℕ).bits.count true % 2 = 1 := by
  rw [show (7:ℕ) = 2*3+1 by norm_num, Nat.bit1_bits 3]
  rw [show (3:ℕ) = 2*1+1 by norm_num, Nat.bit1_bits 1]
  rw [Nat.one_bits]
  decide
theorem pc_8 : (8:ℕ).bits.count true % 2 = 1 := by
  rw [show (8:ℕ) = 2*4 by norm_num, Nat.bit0_bits 4 (by norm_num)]
  rw [show (4:ℕ) = 2*2 by norm_num, Nat.bit0_bits 2 (by norm_num)]
  rw [show (2:ℕ) = 2*1 by norm_num, Nat.bit0_bits 1 (by norm_num)]
  rw [Nat.one_bits]
  decide
theorem pc_21 : (21:ℕ).bits.count true % 2 = 1 := by
  rw [show (21:ℕ) = 2*10+1 by norm_num, Nat.bit1_bits 10]
  rw [show (10:ℕ) = 2*5 by norm_num, Nat.bit0_bits 5 (by norm_num)]
  rw [show (5:ℕ) = 2*2+1 by norm_num, Nat.bit1_bits 2]
  rw [show (2:ℕ) = 2*1 by norm_num, Nat.bit0_bits 1 (by norm_num)]
  rw [Nat.one_bits]
  decide
theorem pc_28 : (28:ℕ).bits.count true % 2 = 1 := by
  rw [show (28:ℕ) = 2*14 by norm_num, Nat.bit0_bits 14 (by norm_num)]
  rw [show (14:ℕ) = 2*7 by norm_num, Nat.bit0_bits 7 (by norm_num)]
  rw [show (7:ℕ) = 2*3+1 by norm_num, Nat.bit1_bits 3]
  rw [show (3:ℕ) = 2*1+1 by norm_num, Nat.bit1_bits 1]
  rw [Nat.one_bits]
  decide
theorem pc_35 : (35:ℕ).bits.count true % 2 = 1 := by
  rw [show (35:ℕ) = 2*17+1 by norm_num, Nat.bit1_bits 17]
  rw [show (17:ℕ) = 2*8+1 by norm_num, Nat.bit1_bits 8]
  rw [show (8:ℕ) = 2*4 by norm_num, Nat.bit0_bits 4 (by norm_num)]
  rw [show (4:ℕ) = 2*2 by norm_num, Nat.bit0_bits 2 (by norm_num)]
  rw [show (2:ℕ) = 2*1 by norm_num, Nat.bit0_bits 1 (by norm_num)]
  rw [Nat.one_bits]
  decide
theorem pc_56 : (56:ℕ).bits.count true % 2 = 1 := by
  rw [show (56:ℕ) = 2*28 by norm_num, Nat.bit0_bits 28 (by norm_num)]
  rw [show (28:ℕ) = 2*14 by norm_num, Nat.bit0_bits 14 (by norm_num)]
  rw [show (14:ℕ) = 2*7 by norm_num, Nat.bit0_bits 7 (by norm_num)]
  rw [show (7:ℕ) = 2*3+1 by norm_num, Nat.bit1_bits 3]
  rw [show (3:ℕ) = 2*1+1 by norm_num, Nat.bit1_bits 1]
  rw [Nat.one_bits]
  decide
theorem pc_70 : (70:ℕ).bits.count true % 2 = 1 := by
  rw [show (70:ℕ) = 2*35 by norm_num, Nat.bit0_bits 35 (by norm_num)]
  rw [show (35:ℕ) = 2*17+1 by norm_num, Nat.bit1_bits 17]
  rw [show (17:ℕ) = 2*8+1 by norm_num, Nat.bit1_bits 8]
  rw [show (8:ℕ) = 2*4 by norm_num, Nat.bit0_bits 4 (by norm_num)]
  rw [show (4:ℕ) = 2*2 by norm_num, Nat.bit0_bits 2 (by norm_num)]
  rw [show (2:ℕ) = 2*1 by norm_num, Nat.bit0_bits 1 (by norm_num)]
  rw [Nat.one_bits]
  decide
theorem pcev_3 : (3:ℕ).bits.count true % 2 = 0 := by
  rw [show (3:ℕ) = 2*1+1 by norm_num, Nat.bit1_bits 1]
  rw [Nat.one_bits]
  decide
theorem pcev_5 : (5:ℕ).bits.count true % 2 = 0 := by
  rw [show (5:ℕ) = 2*2+1 by norm_num, Nat.bit1_bits 2]
  rw [show (2:ℕ) = 2*1 by norm_num, Nat.bit0_bits 1 (by norm_num)]
  rw [Nat.one_bits]
  decide
theorem pcev_6 : (6:ℕ).bits.count true % 2 = 0 := by
  rw [show (6:ℕ) = 2*3 by norm_num, Nat.bit0_bits 3 (by norm_num)]
  rw [show (3:ℕ) = 2*1+1 by norm_num, Nat.bit1_bits 1]
  rw [Nat.one_bits]
  decide

theorem reverse_dir (n : ℕ) (hn : n ∈ ({0,1,2,7,8} : Finset ℕ)) : a n = 0 := by
  rw [a_zero_iff]
  intro m h1 h2
  fin_cases hn <;>
    (interval_cases m <;>
      first
        | exact ne_of_eq_of_ne pc_1 (by decide)
        | exact ne_of_eq_of_ne pc_2 (by decide)
        | exact ne_of_eq_of_ne pc_7 (by decide)
        | exact ne_of_eq_of_ne pc_8 (by decide)
        | exact ne_of_eq_of_ne pc_21 (by decide)
        | exact ne_of_eq_of_ne pc_28 (by decide)
        | exact ne_of_eq_of_ne pc_35 (by decide)
        | exact ne_of_eq_of_ne pc_56 (by decide)
        | exact ne_of_eq_of_ne pc_70 (by decide))

theorem exists_evil (n : ℕ) (hn : n ∉ ({0,1,2,7,8} : Finset ℕ)) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ (n.choose m).bits.count true % 2 = 0 := by
  by_cases hev : n.bits.count true % 2 = 0
  · -- `n` itself is evil: column `m = 1` witnesses it since `C(n,1) = n`.
    have hn0 : n ≠ 0 := by rintro rfl; exact hn (by decide)
    exact ⟨1, le_refl 1, Nat.one_le_iff_ne_zero.mpr hn0,
      by rwa [Nat.choose_one_right]⟩
  · by_cases h9 : 9 ≤ n
    · -- `n ≥ 9`, odious.
      by_cases hpow : ∃ b, n = 2 ^ b ∧ Even b
      · -- Even power of two `n = 2^b`: `C(n,2)` has popcount `b` (even), hence evil.
        obtain ⟨b, rfl, hbe⟩ := hpow
        have hb1 : 1 ≤ b := by
          rcases Nat.eq_zero_or_pos b with h | h
          · subst h; simp at h9
          · exact h
        refine ⟨2, by norm_num, ?_, ?_⟩
        · have : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
          simpa using this
        · rw [pc_choose_two_pow b hb1]
          exact (Nat.even_iff).mp hbe
      · -- ===== OPEN KERNEL (OEIS A249609) =====
        -- Every ODIOUS `n ≥ 9` that is not an even power of two has an evil binomial
        -- coefficient. This is the unresolved content of the conjecture; a proof appears
        -- to require a Mauduit–Rivat-type equidistribution result for the digit-sum
        -- parity of binomial coefficients, which is not available.
        sorry
    · -- `n < 9`, odious, and `n ∉ {0,1,2,7,8}` forces `n = 4`, witnessed by `C(4,2) = 6`.
      push_neg at h9
      interval_cases n
      · exact absurd (by decide) hn
      · exact absurd (by decide) hn
      · exact absurd (by decide) hn
      · exact absurd pcev_3 hev
      · exact ⟨2, by norm_num, by norm_num, pcev_6⟩
      · exact absurd pcev_5 hev
      · exact absurd pcev_6 hev
      · exact absurd (by decide) hn
      · exact absurd (by decide) hn

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨m, hm1, hm2, hev⟩ := exists_evil n hn
    exact absurd hev ((a_zero_iff n).mp h m hm1 hm2)
  · exact reverse_dir n
