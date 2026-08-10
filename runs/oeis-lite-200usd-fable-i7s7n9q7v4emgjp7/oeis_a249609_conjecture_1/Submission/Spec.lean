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

namespace A249609

/-- The evil test used inside `a`. -/
abbrev ev : ℕ → Bool := fun k => decide (List.count true k.bits % 2 = 0)

lemma a_def (n : ℕ) : a n = a.find_min_m n ev 1 := rfl

lemma fmm_gt (n : ℕ) (ev' : ℕ → Bool) {m : ℕ} (h : n < m) :
    a.find_min_m n ev' m = 0 := by
  rw [a.find_min_m.eq_def]
  simp [h]

lemma fmm_hit (n : ℕ) (ev' : ℕ → Bool) {m : ℕ} (h : m ≤ n)
    (he : ev' (n.choose m) = true) : a.find_min_m n ev' m = m := by
  rw [a.find_min_m.eq_def]
  simp [Nat.not_lt.mpr h, he]

lemma fmm_miss (n : ℕ) (ev' : ℕ → Bool) {m : ℕ} (h : m ≤ n)
    (he : ev' (n.choose m) = false) :
    a.find_min_m n ev' m = a.find_min_m n ev' (m + 1) := by
  rw [a.find_min_m.eq_def]
  simp [Nat.not_lt.mpr h, he]

/-- Characterization: `find_min_m` returns 0 iff no evil entry exists in `[m, n]`. -/
lemma fmm_eq_zero_iff_aux (n : ℕ) (ev' : ℕ → Bool) :
    ∀ k m, k = n + 1 - m → 1 ≤ m →
      (a.find_min_m n ev' m = 0 ↔ ∀ j, m ≤ j → j ≤ n → ev' (n.choose j) = false) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
    intro m hk hm
    by_cases hmn : n < m
    · rw [fmm_gt n ev' hmn]
      constructor
      · intro _ j hj₁ hj₂; exact absurd hj₂ (by omega)
      · intro _; rfl
    · push_neg at hmn
      rcases hev : ev' (n.choose m) with hf | ht
      · rw [fmm_miss n ev' hmn hev]
        have hstep := IH (n + 1 - (m + 1)) (by omega) (m + 1) rfl (by omega)
        rw [hstep]
        constructor
        · intro H j hj₁ hj₂
          rcases Nat.eq_or_lt_of_le hj₁ with rfl | hlt
          · exact hev
          · exact H j hlt hj₂
        · intro H j hj₁ hj₂
          exact H j (by omega) hj₂
      · rw [fmm_hit n ev' hmn hev]
        constructor
        · intro H; omega
        · intro H
          have := H m le_rfl hmn
          rw [hev] at this
          exact absurd this (by simp)

lemma a_eq_zero_iff (n : ℕ) :
    a n = 0 ↔ ∀ j, 1 ≤ j → j ≤ n → ev (n.choose j) = false := by
  rw [a_def]
  exact fmm_eq_zero_iff_aux n ev (n + 1 - 1) 1 rfl le_rfl

lemma a_ne_zero_of_evil {n m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ n)
    (he : ev (n.choose m) = true) : a n ≠ 0 := by
  rw [Ne, a_eq_zero_iff]
  intro H
  have := H m h1 h2
  rw [he] at this
  exact absurd this (by simp)

/-! ### Popcount infrastructure -/

/-- Number of ones in the binary expansion (popcount). -/
def sb (n : ℕ) : ℕ := (Nat.bits n).count true

@[simp] lemma sb_zero : sb 0 = 0 := by simp [sb, Nat.zero_bits]

lemma sb_div2 {n : ℕ} (hn : n ≠ 0) : sb n = n % 2 + sb (n / 2) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := he
    have hk : k ≠ 0 := by omega
    have h2 : k + k = 2 * k := by ring
    rw [h2, sb, Nat.bit0_bits k hk]
    have hd : 2 * k / 2 = k := by omega
    have hm : 2 * k % 2 = 0 := by omega
    rw [hd, hm]
    simp [sb, List.count_cons]
  · obtain ⟨k, rfl⟩ := ho
    rw [sb, Nat.bit1_bits k]
    have hd : (2 * k + 1) / 2 = k := by omega
    have hm : (2 * k + 1) % 2 = 1 := by omega
    rw [hd, hm]
    simp [sb, List.count_cons]
    omega

/-- Fuel-based popcount, kernel-computable. -/
def pcF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else n % 2 + pcF f (n / 2)

lemma pcF_eq : ∀ f n : ℕ, n ≤ f → pcF f n = sb n := by
  intro f
  induction f with
  | zero =>
    intro n hn
    interval_cases n
    simp [pcF]
  | succ f IH =>
    intro n hn
    by_cases h0 : n = 0
    · subst h0; simp [pcF]
    · rw [pcF, if_neg h0, sb_div2 h0, IH (n / 2) (by omega)]

lemma pcF_eq_self (n : ℕ) : pcF n n = sb n := pcF_eq n n le_rfl

lemma ev_eq_sb (k : ℕ) : ev k = decide (sb k % 2 = 0) := rfl

/-- Compute `ev` via the fuel-based popcount: usable with `decide`. -/
lemma ev_eq_pcF (k : ℕ) : ev k = decide (pcF k k % 2 = 0) := by
  rw [ev_eq_sb, pcF_eq_self]

/-! ### General popcount lemmas -/

lemma sb_one : sb 1 = 1 := by
  rw [sb_div2 one_ne_zero]; simp

lemma sb_two_mul {n : ℕ} (hn : n ≠ 0) : sb (2 * n) = sb n := by
  rw [sb_div2 (by positivity), Nat.mul_mod_right, Nat.mul_div_cancel_left _ two_pos]
  omega

lemma sb_two_mul_add_one (n : ℕ) : sb (2 * n + 1) = sb n + 1 := by
  rw [sb_div2 (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]; omega

lemma sb_two_pow_mul {k x : ℕ} (hx : x ≠ 0) : sb (2 ^ k * x) = sb x := by
  induction k with
  | zero => simp
  | succ k IH =>
    have : 2 ^ (k + 1) * x = 2 * (2 ^ k * x) := by ring
    rw [this, sb_two_mul (by positivity), IH]

/-- Digit sums add for a sum `a + 2^k * b` when `a < 2^k` (disjoint binary supports). -/
lemma sb_add_two_pow_mul : ∀ k a b : ℕ, a < 2 ^ k → sb (a + 2 ^ k * b) = sb a + sb b := by
  intro k
  induction k with
  | zero =>
    intro a b ha
    interval_cases a
    simp
  | succ k IH =>
    intro a b ha
    by_cases hb : b = 0
    · subst hb; simp
    have hp : (0:ℕ) < 2 ^ (k + 1) := by positivity
    by_cases h0 : a + 2 ^ (k + 1) * b = 0
    · exfalso
      have : 2 ^ (k + 1) * b ≥ 2 ^ (k + 1) * 1 := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [sb_div2 h0]
    have hmod : (a + 2 ^ (k + 1) * b) % 2 = a % 2 := by
      have : 2 ^ (k + 1) * b = 2 * (2 ^ k * b) := by ring
      omega
    have hdiv : (a + 2 ^ (k + 1) * b) / 2 = a / 2 + 2 ^ k * b := by
      have : 2 ^ (k + 1) * b = 2 * (2 ^ k * b) := by ring
      omega
    rw [hmod, hdiv, IH (a / 2) b (by
      have : a < 2 * 2 ^ k := by
        have := pow_succ 2 k
        omega
      omega)]
    by_cases haz : a = 0
    · subst haz; simp
    · rw [sb_div2 haz]; omega

lemma sb_two_pow (k : ℕ) : sb (2 ^ k) = 1 := by
  have := sb_add_two_pow_mul k 0 1 (by positivity)
  simpa [sb_one] using this

lemma sb_two_pow_sub_one (k : ℕ) : sb (2 ^ k - 1) = k := by
  induction k with
  | zero => simp
  | succ k IH =>
    have h : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have := pow_succ 2 k
      omega
    rw [h, sb_two_mul_add_one, IH]

/-- Complement pairing: if `a + b = 2^k - 1` then the digit sums add up to exactly `k`. -/
lemma sb_complement : ∀ k a b : ℕ, a + b = 2 ^ k - 1 → sb a + sb b = k := by
  intro k
  induction k with
  | zero =>
    intro a b h
    norm_num at h
    obtain ⟨ha, hb⟩ := h
    subst ha; subst hb
    simp
  | succ k IH =>
    intro a b h
    have h2 : 1 ≤ 2 ^ (k+1) := Nat.one_le_two_pow
    have hs : a + b = 2 * (2 ^ k - 1) + 1 := by
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have := pow_succ 2 k
      omega
    -- exactly one of a, b is odd
    rcases Nat.even_or_odd a with hae | hao
    · obtain ⟨a', rfl⟩ := hae
      have hbo : b % 2 = 1 := by omega
      obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' + 1 := ⟨b / 2, by omega⟩
      have hrec := IH a' b' (by omega)
      have hb1 : sb (2 * b' + 1) = sb b' + 1 := sb_two_mul_add_one b'
      by_cases haz : a' = 0
      · subst haz
        simp only [Nat.add_zero, sb_zero] at hrec ⊢
        rw [hb1]
        simpa using hrec
      · have ha2 : a' + a' = 2 * a' := by ring
        rw [ha2, sb_two_mul haz, hb1]
        omega
    · obtain ⟨a', rfl⟩ := hao
      have hbe : b % 2 = 0 := by omega
      obtain ⟨b', rfl⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by omega⟩
      have hrec := IH a' b' (by omega)
      have ha1 : sb (2 * a' + 1) = sb a' + 1 := sb_two_mul_add_one a'
      by_cases hbz : b' = 0
      · subst hbz
        simp only [Nat.mul_zero, sb_zero] at hrec ⊢
        rw [ha1]
        simpa using hrec
      · rw [sb_two_mul hbz, ha1]
        omega

/-- Master Lemma (Mersenne): `s₂((2^k − 1)·y) = k` exactly, for all `1 ≤ y ≤ 2^k`. -/
lemma sb_mersenne_mul {k y : ℕ} (h1 : 1 ≤ y) (h2 : y ≤ 2 ^ k) :
    sb ((2 ^ k - 1) * y) = k := by
  have h4 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have key : (2 ^ k - 1) * y = (2 ^ k - y) + 2 ^ k * (y - 1) := by
    zify [h1, h2, h4]
    ring
  rw [key, sb_add_two_pow_mul k _ _ (by omega)]
  exact sb_complement k _ _ (by omega)

/-- Master Lemma (Fermat-type): `s₂((2^k + 1)·y) = 2·s₂(y)` for `y < 2^k`;
in particular such numbers are evil. -/
lemma sb_fermat_mul {k y : ℕ} (h : y < 2 ^ k) :
    sb ((2 ^ k + 1) * y) = 2 * sb y := by
  have key : (2 ^ k + 1) * y = y + 2 ^ k * y := by ring
  rw [key, sb_add_two_pow_mul k _ _ h]
  omega

/-! ### The main open part -/

lemma ev_true_iff (k : ℕ) : ev k = true ↔ sb k % 2 = 0 := by
  rw [ev_eq_sb]
  exact decide_eq_true_iff

/-- Half of all cases: if `n` itself is evil, then `m = 1` works. -/
lemma key_of_evil {n : ℕ} (hn : 1 ≤ n) (h : sb n % 2 = 0) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ ev (n.choose m) = true := by
  refine ⟨1, le_rfl, hn, ?_⟩
  rw [Nat.choose_one_right, ev_true_iff]
  exact h

/-- Key lemma (the mathematical content of the conjecture): every row `n ≥ 9`
of Pascal's triangle contains an evil entry `C(n,m)` with `1 ≤ m ≤ n`.

This is the open part of OEIS A249609 (conjecture of V. Shevelev, 2014).
It has been verified computationally for all `n ≤ 7.75·10^13` (the minimal witness
`m` grows like `1.06·log₂ n`; the record is `μ(42815799784569) = 48`).

Every entry `C(n,m)` with `n ≥ 9` is heuristically an independent fair coin for
the evil/odious property, so a counterexample row `n` (probability `~2^{-n/4}`)
cannot exist; but no known technique (certificates, automatic sequences, exact
row identities, analytic digit methods) can prove this: the statement embeds a
hierarchy of pointwise Gelfond-type problems on Thue–Morse values along
polynomial families. -/
theorem key (n : ℕ) (hn : 9 ≤ n) :
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ ev (n.choose m) = true := by
  sorry

end A249609

open A249609 in
/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  by_cases hn : n ≤ 8
  · interval_cases n
    · -- n = 0
      rw [a_def, fmm_gt 0 ev (by norm_num)]
      decide
    · -- n = 1
      rw [a_def, fmm_miss 1 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_gt 1 ev (by norm_num)]
      decide
    · -- n = 2
      rw [a_def, fmm_miss 2 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 2 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_gt 2 ev (by norm_num)]
      decide
    · -- n = 3 : C(3,1) = 3 = 11₂ evil
      have h3 : a 3 ≠ 0 := a_ne_zero_of_evil (m := 1) (by norm_num) (by norm_num)
        (by rw [ev_eq_pcF]; decide)
      simp [h3]
    · -- n = 4 : C(4,2) = 6 evil
      have h4 : a 4 ≠ 0 := a_ne_zero_of_evil (m := 2) (by norm_num) (by norm_num)
        (by rw [ev_eq_pcF]; decide)
      simp [h4]
    · -- n = 5 : C(5,1) = 5 evil
      have h5 : a 5 ≠ 0 := a_ne_zero_of_evil (m := 1) (by norm_num) (by norm_num)
        (by rw [ev_eq_pcF]; decide)
      simp [h5]
    · -- n = 6 : C(6,1) = 6 evil
      have h6 : a 6 ≠ 0 := a_ne_zero_of_evil (m := 1) (by norm_num) (by norm_num)
        (by rw [ev_eq_pcF]; decide)
      simp [h6]
    · -- n = 7 : all entries odious
      rw [a_def, fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 7 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_gt 7 ev (by norm_num)]
      decide
    · -- n = 8 : all entries odious
      rw [a_def, fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_miss 8 ev (by norm_num) (by rw [ev_eq_pcF]; decide),
          fmm_gt 8 ev (by norm_num)]
      decide
  · push_neg at hn
    have h9 : 9 ≤ n := hn
    obtain ⟨m, hm1, hm2, hme⟩ := key n h9
    have hz : a n ≠ 0 := a_ne_zero_of_evil hm1 hm2 hme
    have hs : n ∉ ({0, 1, 2, 7, 8} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    simp [hz, hs]
