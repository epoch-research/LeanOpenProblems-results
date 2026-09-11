import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

/-!
## Auxiliary, kernel-verified finite results

The conjecture below cannot be settled by a finite computation (it is an "eventually"
statement), and the parity of `⌊(3/2)^k⌋` is the `k`-th binary digit of `3^k`, about which
no density result is known.  What *can* be verified rigorously is that the OEIS question
"Is a(n) > 0?" has a negative answer: `a 371843 = -359`, so the inequality
`a n > √n` fails at `n = 371843`.  The computation is chunked so that each `decide +kernel`
call stays within the kernel's stack/memory limits.
-/

namespace A071532


/-- force evaluation of `x` before continuing (kernel-friendly strictness). -/
def force (x : ℕ) (g : ℕ → ℕ) : ℕ :=
  match x with
  | 0 => g 0
  | y+1 => g (y+1)

theorem force_eq (x : ℕ) (g : ℕ → ℕ) : force x g = g x := by
  cases x <;> rfl

/-- `loop f k p c` : starting from exponent `k` with `p = 3^k` and accumulator `c`,
perform `f` steps, adding the bit `k+1` of `3^(k+1)` at each step. -/
def loop (f : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ c => c)
    (fun _ ih k p c =>
      force (3 * p) fun p' =>
      force (k + 1) fun k' =>
      force (c + (p' >>> k') % 2) fun c' =>
      ih k' p' c') f

@[simp] theorem loop_zero (k p c : ℕ) : loop 0 k p c = c := rfl

theorem loop_succ (f k p c : ℕ) :
    loop (f+1) k p c = loop f (k+1) (3*p) (c + ((3*p) >>> (k+1)) % 2) := by
  have : loop (f+1) = fun k p c =>
      force (3 * p) fun p' =>
      force (k + 1) fun k' =>
      force (c + (p' >>> k') % 2) fun c' =>
      loop f k' p' c' := rfl
  rw [this]
  simp only [force_eq]

/-- the bit at position `k` of `3^k`, i.e. the parity of `⌊(3/2)^k⌋`. -/
def bit (k : ℕ) : ℕ := (3^k >>> k) % 2

theorem loop_spec (f : ℕ) : ∀ k c, loop f k (3^k) c = c + ∑ j ∈ Finset.range f, bit (k + j + 1) := by
  induction f with
  | zero => intro k c; simp
  | succ f ih =>
    intro k c
    rw [loop_succ, ← pow_succ', ih, Finset.sum_range_succ']
    simp only [bit, add_zero]
    ring_nf

theorem loop_split (f1 f2 k c : ℕ) :
    loop (f1 + f2) k (3^k) c = loop f2 (k + f1) (3^(k+f1)) (loop f1 k (3^k) c) := by
  rw [loop_spec, loop_spec, loop_spec, Finset.sum_range_add, add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring




lemma floor_pow (k : ℕ) : ⌊((3:ℝ)/2)^k⌋ = ((3^k / 2^k : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff]
  push_cast
  have h2 : (0:ℝ) < 2^k := by positivity
  constructor
  · rw [div_pow, le_div_iff₀ h2]
    exact_mod_cast Nat.div_mul_le_self (3^k) (2^k)
  · rw [div_pow, div_lt_iff₀ h2]
    have := Nat.lt_div_mul_add (a := 3^k) (by positivity : 0 < 2^k)
    have : 3^k < (3^k/2^k + 1) * 2^k := by rw [add_mul, one_mul]; exact this
    exact_mod_cast this

lemma a_eq (n : ℕ) :
    a n = - Finset.sum (Finset.range n) fun k : ℕ => (-1 : ℤ) ^ (3^(k+1) / 2^(k+1)) := by
  unfold a
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [floor_pow]
  congr 1

lemma neg_one_pow_eq (m : ℕ) : (-1 : ℤ) ^ m = 1 - 2 * ((m % 2 : ℕ) : ℤ) := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]

lemma bit_eq (k : ℕ) : bit k = (3^k / 2^k) % 2 := by
  simp [bit, Nat.shiftRight_eq_div_pow]

lemma a_eq_bits (n : ℕ) :
    a n = 2 * ((Finset.sum (Finset.range n) fun k => bit (k+1) : ℕ) : ℤ) - n := by
  rw [a_eq]
  simp only [neg_one_pow_eq, ← bit_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← Finset.mul_sum]
  push_cast
  ring


theorem chain (f r k c c' v : ℕ) (h1 : loop f k (3^k) c = c')
    (h2 : loop r (k + f) (3^(k+f)) c' = v) : loop (f + r) k (3^k) c = v := by
  rw [loop_split, h1, h2]

set_option exponentiation.threshold 400000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem total : loop 371843 0 (3^0) 0 = 185742 := by
  exact
    chain 8000 363843 0 0 4059 185742 (by decide +kernel) (chain 8000 355843 8000 4059 8106 185742 (by decide +kernel) (chain 8000 347843 16000 8106 12099 185742 (by decide +kernel) (chain 8000 339843 24000 12099 16125 185742 (by decide +kernel) (chain 8000 331843 32000 16125 20150 185742 (by decide +kernel) (chain 8000 323843 40000 20150 24120 185742 (by decide +kernel) (chain 8000 315843 48000 24120 28115 185742 (by decide +kernel) (chain 8000 307843 56000 28115 32121 185742 (by decide +kernel) (chain 8000 299843 64000 32121 36151 185742 (by decide +kernel) (chain 8000 291843 72000 36151 40236 185742 (by decide +kernel) (chain 8000 283843 80000 40236 44270 185742 (by decide +kernel) (chain 8000 275843 88000 44270 48281 185742 (by decide +kernel) (chain 8000 267843 96000 48281 52289 185742 (by decide +kernel) (chain 8000 259843 104000 52289 56238 185742 (by decide +kernel) (chain 8000 251843 112000 56238 60216 185742 (by decide +kernel) (chain 8000 243843 120000 60216 64170 185742 (by decide +kernel) (chain 8000 235843 128000 64170 68195 185742 (by decide +kernel) (chain 8000 227843 136000 68195 72288 185742 (by decide +kernel) (chain 8000 219843 144000 72288 76233 185742 (by decide +kernel) (chain 8000 211843 152000 76233 80295 185742 (by decide +kernel) (chain 8000 203843 160000 80295 84328 185742 (by decide +kernel) (chain 8000 195843 168000 84328 88327 185742 (by decide +kernel) (chain 8000 187843 176000 88327 92270 185742 (by decide +kernel) (chain 8000 179843 184000 92270 96231 185742 (by decide +kernel) (chain 8000 171843 192000 96231 100277 185742 (by decide +kernel) (chain 8000 163843 200000 100277 104245 185742 (by decide +kernel) (chain 8000 155843 208000 104245 108181 185742 (by decide +kernel) (chain 8000 147843 216000 108181 112252 185742 (by decide +kernel) (chain 8000 139843 224000 112252 116293 185742 (by decide +kernel) (chain 8000 131843 232000 116293 120283 185742 (by decide +kernel) (chain 8000 123843 240000 120283 124280 185742 (by decide +kernel) (chain 8000 115843 248000 124280 128177 185742 (by decide +kernel) (chain 8000 107843 256000 128177 132103 185742 (by decide +kernel) (chain 8000 99843 264000 132103 136039 185742 (by decide +kernel) (chain 8000 91843 272000 136039 140128 185742 (by decide +kernel) (chain 8000 83843 280000 140128 144109 185742 (by decide +kernel) (chain 8000 75843 288000 144109 148056 185742 (by decide +kernel) (chain 8000 67843 296000 148056 152103 185742 (by decide +kernel) (chain 8000 59843 304000 152103 156060 185742 (by decide +kernel) (chain 8000 51843 312000 156060 160089 185742 (by decide +kernel) (chain 8000 43843 320000 160089 164089 185742 (by decide +kernel) (chain 8000 35843 328000 164089 167990 185742 (by decide +kernel) (chain 8000 27843 336000 167990 171944 185742 (by decide +kernel) (chain 8000 19843 344000 171944 175881 185742 (by decide +kernel) (chain 8000 11843 352000 175881 179889 185742 (by decide +kernel) (chain 8000 3843 360000 179889 183895 185742 (by decide +kernel) ((by decide +kernel : loop 3843 368000 (3^368000) 183895 = 185742)))))))))))))))))))))))))))))))))))))))))))))))

/-- `a 371843 = -359`: the sequence is *not* positive. -/
theorem a_371843 : a 371843 = -359 := by
  rw [a_eq_bits]
  have h := total
  rw [loop_spec] at h
  simp only [zero_add] at h
  rw [h]
  norm_num

/-- The conjectured inequality `a n > √n` fails at `n = 371843`. -/
theorem conjecture_fails_at_371843 : ¬ ((a 371843 : ℝ) > sqrt ((371843 : ℕ) : ℝ)) := by
  rw [a_371843]
  push_cast
  intro h
  linarith [Real.sqrt_nonneg (371843 : ℝ)]

/-- Negative answer to the OEIS question "Is a(n) > 0?". -/
theorem a_not_always_pos : ¬ ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  intro h
  have := h 371843 (by norm_num)
  rw [a_371843] at this
  omega

/-- Bounded form of the disproof: for every `N ≤ 371843` there is `n ≥ N` at which the
conjectured inequality fails.  (The unbounded statement `∀ N, ∃ n ≥ N, …` is exactly the
`.disproof` theorem below and is not provable by finite computation.) -/
theorem bounded_disproof : ∀ N : ℕ, N ≤ 371843 → ∃ n : ℕ, n ≥ N ∧ ¬ ((a n : ℝ) > sqrt (n : ℝ)) :=
  fun N hN => ⟨371843, hN, by exact_mod_cast conjecture_fails_at_371843⟩

end A071532

/--
Conjecture: Asymptotically, $a(n) > \sqrt{n}$.
Verbatim OEIS comment: "Is a(n)>0? For n large enough does a(n)>sqrt(n) always hold?"
-/
theorem oeis_71532_conjecture_0 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  sorry

theorem oeis_71532_conjecture_0.disproof : ¬ (type_of% @oeis_71532_conjecture_0) := sorry
