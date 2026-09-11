import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S

/--
Conjecture (i): $a(n) < 2 \cdot (\text{prime}(n) - 1)$ for all $n > 0$,
where $\text{prime}(n)$ is the $n$-th prime number (1-indexed).
-/
theorem oeis_232616_conjecture_i (n : ℕ) (hn : 0 < n) :
    A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

namespace Dis

/- ### Digit sums and a SWAR popcount -/

/-- Sum of the base-`2^w` digits of `x`. -/
def dsum (w x : ℕ) : ℕ := (Nat.digits (2^w) x).sum

lemma dsum_zero (w : ℕ) : dsum w 0 = 0 := by simp [dsum]

lemma dsum_add_mul (w : ℕ) (hw : 1 ≤ w) {a : ℕ} (ha : a < 2^w) (b : ℕ) :
    dsum w (a + 2^w * b) = a + dsum w b := by
  have h2 : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0; simp [dsum]
    · simp only [mul_zero, add_zero, dsum]
      rw [Nat.digits_of_lt (2^w) a (by omega) ha]; simp
  · unfold dsum
    rw [Nat.digits_add (2^w) h2 a b ha (Or.inr (by omega))]
    simp

lemma dsum_of_lt (w : ℕ) (hw : 1 ≤ w) {a : ℕ} (ha : a < 2^w) : dsum w a = a := by
  have := dsum_add_mul w hw ha 0
  simpa [dsum_zero] using this

lemma dsum_one_eq_sum (L : ℕ) : ∀ x, x < 2^L →
    dsum 1 x = ∑ m ∈ Finset.range L, (if x.testBit m then 1 else 0) := by
  induction L with
  | zero => intro x hx; simp at hx; subst hx; simp [dsum]
  | succ L ih =>
    intro x hx
    have hx' : x / 2 < 2^L := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hx; exact hx
    have h1 : dsum 1 x = x % 2 + dsum 1 (x / 2) := by
      conv_lhs => rw [show x = x % 2 + 2^1 * (x/2) by simp; omega]
      exact dsum_add_mul 1 le_rfl (by simp; omega) _
    rw [h1, Finset.sum_range_succ', ih _ hx']
    simp only [Nat.testBit_add_one, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega

/-- Block decomposition of `land`. -/
lemma land_block {k a b x y : ℕ} (ha : a < 2^k) (hb : b < 2^k) :
    (2^k * x + a) &&& (2^k * y + b) = 2^k * (x &&& y) + (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add x ha, Nat.testBit_two_pow_mul_add y hb,
      Nat.testBit_two_pow_mul_add (x &&& y) (lt_of_le_of_lt Nat.and_le_left ha)]
  split_ifs <;> simp

/-- The SWAR mask: low `w` bits set in each block of `2w` bits, `K` blocks. -/
def maskRec (w : ℕ) : ℕ → ℕ
  | 0 => 0
  | K+1 => 2^(2*w) * maskRec w K + (2^w - 1)

lemma maskRec_closed (w : ℕ) : ∀ K, maskRec w K * (2^w + 1) + 1 = 2^(2*w*K) := by
  intro K
  induction K with
  | zero => simp [maskRec]
  | succ K ih =>
    have hW : 1 ≤ 2^w := Nat.one_le_two_pow
    obtain ⟨V, hV⟩ : ∃ V, 2^w = V + 1 := ⟨2^w - 1, by omega⟩
    have h2w : 2^(2*w) = 2^w * 2^w := by rw [two_mul, pow_add]
    have hK : 2^(2*w*(K+1)) = 2^(2*w) * 2^(2*w*K) := by
      rw [Nat.mul_succ, pow_add, mul_comm]
    rw [maskRec, hK, ← ih, h2w, hV]
    simp only [Nat.add_sub_cancel]
    ring

lemma maskRec_eq_div (w K : ℕ) : (2^(2*w*K) - 1) / (2^w + 1) = maskRec w K := by
  apply Nat.div_eq_of_eq_mul_left (by positivity)
  have := maskRec_closed w K
  omega

lemma maskRec_lt (w : ℕ) (hw : 1 ≤ w) (K : ℕ) : 2 * maskRec w K < 2^(2*w*K) := by
  have h := maskRec_closed w K
  have : 2 ≤ 2^w := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hw
  nlinarith

/-- One SWAR step (with the mask given in closed form, for kernel evaluation). -/
def stepK (w K x : ℕ) : ℕ :=
  (x &&& ((2^(2*w*K) - 1) / (2^w + 1))) + ((x >>> w) &&& ((2^(2*w*K) - 1) / (2^w + 1)))

lemma stepK_eq (w K x : ℕ) :
    stepK w K x = (x &&& maskRec w K) + ((x >>> w) &&& maskRec w K) := by
  simp [stepK, maskRec_eq_div]

lemma stepK_lt (w : ℕ) (hw : 1 ≤ w) (K x : ℕ) : stepK w K x < 2^(2*w*K) := by
  rw [stepK_eq]
  have h1 : x &&& maskRec w K ≤ maskRec w K := Nat.and_le_right
  have h2 : (x >>> w) &&& maskRec w K ≤ maskRec w K := Nat.and_le_right
  have := maskRec_lt w hw K
  omega

lemma stepK_dsum (w : ℕ) (hw : 1 ≤ w) : ∀ K x, x < 2^(2*w*K) →
    dsum (2*w) (stepK w K x) = dsum w x := by
  intro K
  induction K with
  | zero =>
    intro x hx
    simp at hx; subst hx
    simp [stepK_eq, maskRec, dsum_zero]
  | succ K ih =>
    intro x hx
    rw [stepK_eq]
    set W := 2^w with hWdef
    have hW1 : 1 < W := Nat.one_lt_two_pow (by omega)
    have hWpos : 0 < W := by omega
    have h2w : 2^(2*w) = W * W := by rw [two_mul, pow_add]
    have hW2pos : 0 < W * W := by positivity
    -- decompose x
    set a := x % (W*W) with ha
    set x' := x / (W*W) with hx'
    have hxdec : x = W * W * x' + a := by rw [ha, hx']; exact (Nat.div_add_mod x (W*W)).symm
    have haW : a < W * W := Nat.mod_lt _ hW2pos
    have hx'lt : x' < 2^(2*w*K) := by
      rw [hx', Nat.div_lt_iff_lt_mul hW2pos]
      have : 2^(2*w*(K+1)) = 2^(2*w*K) * (W*W) := by
        rw [Nat.mul_succ, pow_add, h2w]
      rw [← this]; exact hx
    have hM : maskRec w (K+1) = W * W * maskRec w K + (W - 1) := by
      rw [maskRec, h2w]
    have hWm1 : W - 1 < W * W := by have := Nat.le_mul_self W; omega
    -- first term
    have hT1 : x &&& maskRec w (K+1) = W * W * (x' &&& maskRec w K) + a % W := by
      rw [hM, hxdec]
      have := land_block (k := 2*w) (a := a) (b := W - 1) (x := x') (y := maskRec w K)
        (by rw [h2w]; exact haW) (by rw [h2w]; exact hWm1)
      rw [h2w] at this
      rw [this]
      congr 1
      have : a &&& (W - 1) = a % W := by
        rw [hWdef]; exact Nat.and_two_pow_sub_one_eq_mod a w
      exact this
    -- shifted value
    have hshift : x >>> w = W * W * (x' / W) + (W * (x' % W) + a / W) := by
      rw [Nat.shiftRight_eq_div_pow, ← hWdef, hxdec]
      have e1 : (W * W * x' + a) / W = W * x' + a / W := by
        rw [mul_assoc, Nat.mul_add_div hWpos]
      rw [e1]
      have e2 : x' = W * (x' / W) + x' % W := (Nat.div_add_mod x' W).symm
      conv_lhs => rw [e2]
      ring
    have hlow : W * (x' % W) + a / W < W * W := by
      have h1 : x' % W < W := Nat.mod_lt _ hWpos
      have h2 : a / W < W := by rw [Nat.div_lt_iff_lt_mul hWpos]; exact haW
      nlinarith
    have hT2 : (x >>> w) &&& maskRec w (K+1) = W * W * ((x' >>> w) &&& maskRec w K) + a / W := by
      rw [hM, hshift]
      have := land_block (k := 2*w) (a := W * (x' % W) + a / W) (b := W - 1) (x := x' / W)
        (y := maskRec w K) (by rw [h2w]; exact hlow) (by rw [h2w]; exact hWm1)
      rw [h2w] at this
      rw [this, Nat.shiftRight_eq_div_pow, ← hWdef]
      congr 1
      have : (W * (x' % W) + a / W) &&& (W - 1) = a / W := by
        rw [hWdef, Nat.and_two_pow_sub_one_eq_mod, ← hWdef]
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul hWpos]; exact haW)
      exact this
    have haWlt : a % W + a / W < W * W := by
      have h1 : a % W < W := Nat.mod_lt _ hWpos
      have h2 : a / W < W := by rw [Nat.div_lt_iff_lt_mul hWpos]; exact haW
      nlinarith
    -- combine
    have hsum : (x &&& maskRec w (K+1)) + ((x >>> w) &&& maskRec w (K+1)) =
        (a % W + a / W) + 2^(2*w) * stepK w K x' := by
      rw [hT1, hT2, stepK_eq, h2w]; ring
    rw [hsum, dsum_add_mul (2*w) (by omega) (by rw [h2w]; exact haWlt), ih x' hx'lt]
    -- dsum w x
    have hxdec' : x = a % W + 2^w * (a / W + 2^w * x') := by
      rw [← hWdef]
      have := Nat.div_add_mod a W
      rw [hxdec]; ring_nf; omega
    rw [hxdec', dsum_add_mul w hw (Nat.mod_lt _ hWpos),
      dsum_add_mul w hw (by rw [← hWdef, Nat.div_lt_iff_lt_mul hWpos]; exact haW)]
    ring

/-- Iterated SWAR: after `j` steps the field width is `2^j`; total width `2^23`. -/
def swarIter : ℕ → ℕ → ℕ
  | 0, x => x
  | j+1, x => stepK (2^j) (2^(22-j)) (swarIter j x)

lemma swarIter_spec : ∀ j, j ≤ 23 → ∀ x, x < 2^(2^23) →
    dsum (2^j) (swarIter j x) = dsum 1 x ∧ swarIter j x < 2^(2^23) := by
  intro j
  induction j with
  | zero => intro _ x hx; exact ⟨by simp [swarIter], by simpa [swarIter] using hx⟩
  | succ j ih =>
    intro hj x hx
    obtain ⟨ih1, ih2⟩ := ih (by omega) x hx
    have hK : 2 * 2^j * 2^(22-j) = 2^23 := by
      rw [mul_assoc, ← pow_add, show j + (22 - j) = 22 by omega]; norm_num
    have hw : 1 ≤ 2^j := Nat.one_le_two_pow
    constructor
    · show dsum (2^(j+1)) (stepK (2^j) (2^(22-j)) (swarIter j x)) = dsum 1 x
      rw [pow_succ, mul_comm, stepK_dsum (2^j) hw _ _ (by rw [hK]; exact ih2), ih1]
    · show stepK (2^j) (2^(22-j)) (swarIter j x) < 2^(2^23)
      rw [← hK]; exact stepK_lt _ hw _ _

lemma swarIter_23 (x : ℕ) (hx : x < 2^(2^23)) : swarIter 23 x = dsum 1 x := by
  obtain ⟨h1, h2⟩ := swarIter_spec 23 le_rfl x hx
  rw [← h1, dsum_of_lt _ (by norm_num) h2]

end Dis



namespace Dis

/- ### Bounded Boolean quantifiers, evaluated by the kernel -/

def forallB (f : ℕ → Bool) (N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => f i && ih) N

lemma forallB_spec (f : ℕ → Bool) : ∀ N, forallB f N = true → ∀ i, i < N → f i = true := by
  intro N
  induction N with
  | zero => intro _ i hi; omega
  | succ N ih =>
    intro h i hi
    have h' : (f N && forallB f N) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
    · exact ih h'.2 i hlt
    · subst heq; exact h'.1

def existsB (f : ℕ → Bool) (N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => f i || ih) N

lemma existsB_spec (f : ℕ → Bool) : ∀ N, existsB f N = true → ∃ i, i < N ∧ f i = true := by
  intro N
  induction N with
  | zero => intro h; exact absurd h (by simp [existsB])
  | succ N ih =>
    intro h
    have h' : (f N || existsB f N) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨N, by omega, h'⟩
    · obtain ⟨i, hi, hfi⟩ := ih h'
      exact ⟨i, by omega, hfi⟩

/- ### A bitset sieve of Eratosthenes on the odd numbers

Bit `i` of the bitset stands for the odd number `2i+1`.  All definitions are parametrised by the
number `k` of bits and the trial bound `b`, and all lemmas are proved for variables; the concrete
values are only plugged in at the very end.  This keeps the kernel from evaluating any of the
(huge) closed terms while it checks the structural lemmas. -/

lemma geom_lt (p : ℕ) (hp : 1 ≤ p) : ∀ J, ∑ j ∈ Finset.range J, 2^(p*j) < 2^(p*J) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have h1 : 2^(p*J) + 2^(p*J) = 2^(p*J+1) := by rw [pow_succ]; ring
    have h2 : 2^(p*J+1) ≤ 2^(p*(J+1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega

lemma testBit_geom (p : ℕ) (hp : 1 ≤ p) : ∀ J i,
    (∑ j ∈ Finset.range J, 2^(p*j)).testBit i = true ↔ ∃ j, j < J ∧ i = p * j := by
  intro J
  induction J with
  | zero => intro i; simp
  | succ J ih =>
    intro i
    rw [Finset.sum_range_succ, add_comm]
    have hlt := geom_lt p hp J
    rcases lt_trichotomy i (p*J) with h | h | h
    · rw [Nat.testBit_two_pow_add_gt h, ih]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨j, ?_, rfl⟩
        by_contra hc
        have : j = J := by omega
        subst this; omega
    · subst h
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
      simp only [Bool.not_false, true_iff]
      exact ⟨J, by omega, rfl⟩
    · have hsum : 2^(p*J) + ∑ j ∈ Finset.range J, 2^(p*j) < 2^i := by
        have : 2^(p*J) + 2^(p*J) ≤ 2^i := by
          rw [← two_mul, ← pow_succ']
          exact Nat.pow_le_pow_right (by norm_num) h
        omega
      rw [Nat.testBit_lt_two_pow hsum]
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro j hj hij
      have : p * j ≤ p * J := Nat.mul_le_mul_left p (by omega)
      omega

/-- `2^(pT + s) / (2^p - 1) = (∑_{j < T} 2^(pj)) · 2^s` for `s < p`, `p ≥ 2`. -/
lemma geom_shift_eq_div (p : ℕ) (hp : 2 ≤ p) (T s : ℕ) (hs : s < p) :
    2^(p*T + s) / (2^p - 1) = (∑ j ∈ Finset.range T, 2^(p*j)) * 2^s := by
  have h4p : 4 ≤ 2^p := by
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^p := Nat.pow_le_pow_right (by norm_num) hp
  have key := geom_sum_mul_add (2^p - 1) T
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2^p)] at key
  simp only [← pow_mul] at key
  have h2s : 2^s < 2^p - 1 := by
    have h1 : 2^s ≤ 2^(p-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2^(p-1) + 2^(p-1) = 2^p := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have h3 : 2 ≤ 2^(p-1) := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^(p-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [pow_add, ← key, add_mul, one_mul, mul_comm (∑ j ∈ Finset.range T, 2^(p*j)) (2^p - 1),
    mul_assoc, Nat.mul_add_div (by omega), Nat.div_eq_of_lt h2s, add_zero]

lemma testBit_geom_shift (p : ℕ) (hp : 1 ≤ p) (T s i : ℕ) :
    ((∑ j ∈ Finset.range T, 2^(p*j)) * 2^s).testBit i = true ↔ ∃ j, j < T ∧ i = p * j + s := by
  rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  constructor
  · intro h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨j, hj, hij⟩ := (testBit_geom p hp T _).1 h.2
    exact ⟨j, hj, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [testBit_geom p hp]
    exact ⟨j, hj, by omega⟩

/-- Mask marking the odd multiples `p, 3p, 5p, …` of `p` in the odd-only bitset: bit
`p·t + (p-1)/2` stands for the number `p·(2t+1)`. -/
def gmo (k p : ℕ) : ℕ := 2^(p * (k / p + 2) + (p - 1) / 2) / (2^p - 1)

lemma testBit_gmo (k p : ℕ) (hp : 2 ≤ p) (i : ℕ) :
    (gmo k p).testBit i = true ↔ ∃ t, t < k / p + 2 ∧ i = p * t + (p - 1) / 2 := by
  unfold gmo
  rw [geom_shift_eq_div p hp _ _ (by omega), testBit_geom_shift p (by omega)]

/-- One sieve step: OR in the mask of `p` provided `p` passes the filter `flt`. -/
def sstep (flt : ℕ → Bool) (k p s : ℕ) : ℕ := cond (flt p) (s ||| gmo k p) s

/-- Fold the masks for `p = 2, …, i+1`.  The accumulator is the recursive value itself (rather
than an extra function argument), so that the kernel evaluates every step exactly once. -/
def sieveAux (flt : ℕ → Bool) (k i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i ih => sstep flt k (i+2) ih) i

lemma sieveAux_zero (flt : ℕ → Bool) (k : ℕ) : sieveAux flt k 0 = 0 := rfl

lemma sieveAux_succ (flt : ℕ → Bool) (k i : ℕ) :
    sieveAux flt k (i+1) = sstep flt k (i+2) (sieveAux flt k i) := rfl

lemma testBit_sstep (flt : ℕ → Bool) (k p s m : ℕ) :
    (sstep flt k p s).testBit m = true ↔
      s.testBit m = true ∨ (flt p = true ∧ (gmo k p).testBit m = true) := by
  unfold sstep
  cases h : flt p
  · simp
  · simp

lemma testBit_sieveAux (flt : ℕ → Bool) (k i : ℕ) : ∀ m,
    (sieveAux flt k i).testBit m = true ↔
      ∃ p, 2 ≤ p ∧ p ≤ i + 1 ∧ flt p = true ∧ (gmo k p).testBit m = true := by
  induction i with
  | zero =>
    intro m
    rw [sieveAux_zero]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro p hp1 hp2
    omega
  | succ i ih =>
    intro m
    rw [sieveAux_succ, testBit_sstep, ih]
    constructor
    · rintro (⟨p, hp1, hp2, hw, hg⟩ | ⟨hw, hg⟩)
      · exact ⟨p, hp1, by omega, hw, hg⟩
      · exact ⟨i+2, by omega, by omega, hw, hg⟩
    · rintro ⟨p, hp1, hp2, hw, hg⟩
      rcases Nat.lt_or_ge p (i+2) with hlt | hge
      · exact Or.inl ⟨p, hp1, by omega, hw, hg⟩
      · have : p = i + 2 := by omega
        subst this
        exact Or.inr ⟨hw, hg⟩

/-- The sieve bitset with `k` bits (for the odd numbers below `2k`) and trial bound `b`. -/
def sieveOf (flt : ℕ → Bool) (k b : ℕ) : ℕ := sieveAux flt k (b - 1)

lemma testBit_sieveOf (flt : ℕ → Bool) (k b m : ℕ) (hb : 1 ≤ b) :
    (sieveOf flt k b).testBit m = true ↔
    ∃ p, 2 ≤ p ∧ p ≤ b ∧ flt p = true ∧ (gmo k p).testBit m = true := by
  unfold sieveOf
  rw [testBit_sieveAux, Nat.sub_add_cancel hb]

/-- Main characterisation: for `i < k`, bit `i` of the sieve is set iff the odd number `2i+1`
is `≥ 3` and has a prime factor `≤ b`.  This needs that only odd `p` pass the filter and that
every odd prime `≤ b` does. -/
lemma sieve_bit (flt : ℕ → Bool) (k b i : ℕ)
    (hodd : ∀ p, flt p = true → p % 2 = 1)
    (hflt : ∀ p, p.Prime → p % 2 = 1 → p ≤ b → flt p = true)
    (hb : 2 ≤ b) (hi : i < k) :
    (sieveOf flt k b).testBit i = true ↔ 3 ≤ 2 * i + 1 ∧ (2 * i + 1).minFac ≤ b := by
  rw [testBit_sieveOf flt k b i (by omega)]
  constructor
  · rintro ⟨p, hp2, hpb, hf, hg⟩
    obtain ⟨t, _, rfl⟩ := (testBit_gmo k p hp2 _).1 hg
    have hpo := hodd p hf
    have hm : 2 * (p * t + (p - 1) / 2) + 1 = p * (2 * t + 1) := by
      have h1 : 2 * ((p - 1) / 2) = p - 1 := by omega
      have h2 : p * (2 * t + 1) = 2 * (p * t) + p := by ring
      omega
    refine ⟨?_, ?_⟩
    · have : 3 ≤ p := by omega
      rw [hm]; nlinarith
    · rw [hm]
      exact le_trans (Nat.minFac_le_of_dvd hp2 (Dvd.intro _ rfl)) hpb
  · rintro ⟨h3, hmin⟩
    have hpp : (2 * i + 1).minFac.Prime := Nat.minFac_prime (by omega)
    obtain ⟨q, hq⟩ := Nat.minFac_dvd (2 * i + 1)
    have hoddm : Odd (2 * i + 1) := ⟨i, rfl⟩
    rw [hq, Nat.odd_mul] at hoddm
    have hpodd : (2 * i + 1).minFac % 2 = 1 := Nat.odd_iff.mp hoddm.1
    have hqodd : q % 2 = 1 := Nat.odd_iff.mp hoddm.2
    have hp2 := hpp.two_le
    refine ⟨(2 * i + 1).minFac, hp2, hmin, hflt _ hpp hpodd hmin, ?_⟩
    rw [testBit_gmo k _ hp2]
    refine ⟨(q - 1) / 2, ?_, ?_⟩
    · have hqp : (2 * i + 1).minFac * q < 2 * k := by rw [← hq]; omega
      have hle : (q - 1) / 2 * (2 * i + 1).minFac ≤ k := by
        have h1 : (q - 1) / 2 * 2 ≤ q - 1 := Nat.div_mul_le_self _ _
        have h2 : (q - 1) / 2 * (2 * i + 1).minFac * 2 = (q - 1) / 2 * 2 * (2 * i + 1).minFac := by
          ring
        have h3 : (q - 1) / 2 * 2 * (2 * i + 1).minFac ≤ (q - 1) * (2 * i + 1).minFac :=
          Nat.mul_le_mul_right _ h1
        have h4 : (q - 1) * (2 * i + 1).minFac ≤ (2 * i + 1).minFac * q := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        omega
      have := (Nat.le_div_iff_mul_le (by omega)).2 hle
      omega
    · have e1 : 2 * ((q - 1) / 2) + 1 = q := by omega
      have e2 : 2 * (((2 * i + 1).minFac - 1) / 2) + 1 = (2 * i + 1).minFac := by omega
      have e3 : (2 * i + 1).minFac * (2 * ((q - 1) / 2) + 1) =
          2 * ((2 * i + 1).minFac * ((q - 1) / 2)) + (2 * i + 1).minFac := by ring
      rw [e1] at e3
      omega

/-- A wrapper around `%`; it keeps the kernel from eagerly evaluating `sieveOf flt k b % 2^k`
when it merely unfolds `ZOf` during definitional-equality checks. -/
def wrapMod (a b : ℕ) : ℕ := a % b

lemma wrapMod_lt (x i : ℕ) : wrapMod x (2^i) < 2^i := by
  unfold wrapMod; exact Nat.mod_lt _ (by positivity)

lemma testBit_wrapMod (x i j : ℕ) (hj : j < i) : (wrapMod x (2^i)).testBit j = x.testBit j := by
  unfold wrapMod; rw [Nat.testBit_mod_two_pow]; simp [hj]

/-- The sieve restricted to its `k` bits. -/
def ZOf (flt : ℕ → Bool) (k b : ℕ) : ℕ := wrapMod (sieveOf flt k b) (2^k)

lemma ZOf_lt (flt : ℕ → Bool) (k b : ℕ) : ZOf flt k b < 2^k := wrapMod_lt _ _

lemma testBit_ZOf (flt : ℕ → Bool) (k b i : ℕ) (hi : i < k) :
    (ZOf flt k b).testBit i = (sieveOf flt k b).testBit i :=
  testBit_wrapMod _ _ _ hi

/-- Counting odd primes below `N ≤ 2k` via the odd-only indexing. -/
lemma sum_odd_primes (k N : ℕ) (hN : 3 ≤ N) (hNk : N ≤ 2 * k) :
    ∑ i ∈ Finset.range k, (if 2 * i + 1 < N ∧ Nat.Prime (2 * i + 1) then 1 else 0) + 1 =
      Nat.count Nat.Prime N := by
  rw [Nat.count_eq_card_filter_range, Finset.card_filter]
  have hsplit : ∀ m ∈ Finset.range N, (if Nat.Prime m then 1 else 0) =
      (if m % 2 = 1 ∧ Nat.Prime m then 1 else 0) + (if m = 2 then 1 else 0) := by
    intro m _
    by_cases hp : Nat.Prime m
    · rcases hp.eq_two_or_odd with h2 | h2
      · subst h2; simp [Nat.prime_two]
      · have : m ≠ 2 := by omega
        simp [hp, h2, this]
    · have : m ≠ 2 := fun h => hp (h ▸ Nat.prime_two)
      simp [hp, this]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h2 : ∑ m ∈ Finset.range N, (if m = 2 then 1 else 0) = 1 := by
    rw [Finset.sum_boole]
    have : (Finset.range N).filter (fun m => m = 2) = {2} := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨by omega, rfl⟩
    rw [this]; simp
  have hodd : ∑ m ∈ Finset.range N, (if m % 2 = 1 ∧ Nat.Prime m then 1 else 0) =
      ∑ i ∈ Finset.range k, (if 2 * i + 1 < N ∧ Nat.Prime (2 * i + 1) then 1 else 0) := by
    have himg : (Finset.range N).filter (fun m => m % 2 = 1) =
        ((Finset.range k).filter (fun i => 2 * i + 1 < N)).image (fun i => 2 * i + 1) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hm, ho⟩; exact ⟨m / 2, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨i, ⟨hi, hiN⟩, rfl⟩; exact ⟨hiN, by omega⟩
    simp only [ite_and]
    rw [← Finset.sum_filter, himg, Finset.sum_image (fun a _ b _ h => by omega),
      Finset.sum_filter]
  rw [hodd, h2]

/-- Generic counting lemma: if the `k` bits of `x` mark exactly the odd numbers `2i+1 ≥ 3` with a
prime factor `≤ b`, and `2k ≤ (b+1)^2`, then `π(2k) + popcount + 1 = k + π(b+1)`. -/
lemma count_prime_of (k b x c : ℕ) (hb : 2 ≤ b) (hbk : b + 1 ≤ 2 * k) (hk : 2 * k ≤ (b+1)^2)
    (hbit : ∀ i, i < k → (x.testBit i = true ↔ 3 ≤ 2 * i + 1 ∧ (2 * i + 1).minFac ≤ b))
    (hc : ∑ i ∈ Finset.range k, (if x.testBit i then 1 else 0) = c) :
    Nat.count Nat.Prime (2 * k) + c + 1 = k + Nat.count Nat.Prime (b + 1) := by
  have h1 : ∀ i ∈ Finset.range k,
      ((if 2 * i + 1 < 2 * k ∧ Nat.Prime (2 * i + 1) then 1 else 0)
        + (if x.testBit i then 1 else 0)) + (if i = 0 then 1 else 0)
      = 1 + (if 2 * i + 1 < b + 1 ∧ Nat.Prime (2 * i + 1) then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hbi := hbit i hi
    have hlt : 2 * i + 1 < 2 * k := by omega
    by_cases hp : Nat.Prime (2 * i + 1)
    · have hmf : (2 * i + 1).minFac = 2 * i + 1 := hp.minFac_eq
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact Nat.not_prime_one hp
      by_cases hlb : 2 * i + 1 < b + 1
      · have : x.testBit i = true := hbi.2 ⟨by omega, by omega⟩
        simp [hlt, hp, hlb, this, hi0]
      · have : ¬ x.testBit i = true := fun h => by have := (hbi.1 h).2; omega
        simp [hlt, hp, hlb, this, hi0]
    · rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have : ¬ x.testBit 0 = true := fun h => by have := (hbi.1 h).1; omega
        simp [hp, this]
      · have hsq := Nat.minFac_sq_le_self (by omega) hp
        have hle : (2 * i + 1).minFac ≤ b := by
          by_contra hc
          push_neg at hc
          nlinarith
        have : x.testBit i = true := hbi.2 ⟨by omega, hle⟩
        simp [hp, this, show i ≠ 0 by omega]
  have hsum := Finset.sum_congr rfl h1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hc,
    Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsum
  have e1 : ∑ i ∈ Finset.range k, (if i = 0 then 1 else 0) = 1 := by
    rw [Finset.sum_boole]
    have : (Finset.range k).filter (fun i => i = 0) = {0} := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro rfl; exact ⟨by omega, rfl⟩
    rw [this]; simp
  have e2 := sum_odd_primes k (2 * k) (by omega) le_rfl
  have e3 := sum_odd_primes k (b + 1) (by omega) hbk
  omega

lemma sum_ZOf (flt : ℕ → Bool) (k b : ℕ) (hk : k ≤ 2^23) :
    ∑ i ∈ Finset.range k, (if (ZOf flt k b).testBit i then 1 else 0) =
      swarIter 23 (ZOf flt k b) := by
  rw [← dsum_one_eq_sum k _ (ZOf_lt flt k b),
    swarIter_23 _ (lt_of_lt_of_le (ZOf_lt flt k b) (Nat.pow_le_pow_right (by norm_num) hk))]

lemma count_prime_of' (flt : ℕ → Bool) (k b c : ℕ)
    (hodd : ∀ p, flt p = true → p % 2 = 1)
    (hflt : ∀ p, p.Prime → p % 2 = 1 → p ≤ b → flt p = true)
    (hb : 2 ≤ b) (hbk : b + 1 ≤ 2 * k) (hk : 2 * k ≤ (b+1)^2)
    (hk23 : k ≤ 2^23) (hc : swarIter 23 (ZOf flt k b) = c) :
    Nat.count Nat.Prime (2 * k) + c + 1 = k + Nat.count Nat.Prime (b + 1) :=
  count_prime_of k b (ZOf flt k b) c hb hbk hk
    (fun i hi => by rw [testBit_ZOf flt k b i hi]; exact sieve_bit flt k b i hodd hflt hb hi)
    (by rw [sum_ZOf flt k b hk23, hc])

/-- The filter "`p` is odd" (used for the two small sieves). -/
def oddOk (p : ℕ) : Bool := Nat.beq (p % 2) 1

lemma oddOk_odd : ∀ p, oddOk p = true → p % 2 = 1 := fun p h => Nat.eq_of_beq_eq_true h

lemma oddOk_spec (b : ℕ) : ∀ p, p.Prime → p % 2 = 1 → p ≤ b → oddOk p = true :=
  fun _ _ h _ => by unfold oddOk; rw [h]; rfl

lemma arith_of (a c n d : ℕ) (h : a + c + 1 = n + d) : a = n + d - c - 1 := by omega

lemma count_8 : Nat.count Nat.Prime 8 = 4 := by
  norm_num [Nat.count_succ]

set_option exponentiation.threshold 100000000 in
lemma pop_27 : swarIter 23 (ZOf oddOk 27 7) = 14 := by decide +kernel

lemma count_54 : Nat.count Nat.Prime 54 = 16 := by
  have h := count_prime_of' oddOk 27 7 14 oddOk_odd (oddOk_spec 7) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) pop_27
  have h8 : Nat.count Nat.Prime (7 + 1) = 4 := count_8
  have h54 : Nat.count Nat.Prime (2 * 27) = Nat.count Nat.Prime 54 := rfl
  rw [h54] at h
  rw [arith_of _ _ _ _ h, h8]

set_option exponentiation.threshold 100000000 in
lemma pop_1429 : swarIter 23 (ZOf oddOk 1429 53) = 1029 := by decide +kernel

lemma count_2858 : Nat.count Nat.Prime 2858 = 415 := by
  have h := count_prime_of' oddOk 1429 53 1029 oddOk_odd (oddOk_spec 53) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) pop_1429
  have h54 : Nat.count Nat.Prime (53 + 1) = 16 := count_54
  have h2858 : Nat.count Nat.Prime (2 * 1429) = Nat.count Nat.Prime 2858 := rfl
  rw [h2858] at h
  rw [arith_of _ _ _ _ h, h54]

/-- The small sieve, as a constant: the kernel evaluates it once and caches the value. -/
def smallSieve : ℕ := sieveOf oddOk 1429 53

/-- A prime filter for the big sieve: `p` odd, and `p ≤ 53` or `p` not marked in the small sieve.
Only odd `p` pass, and every odd prime `p < 2858` passes. -/
def primeOk (p : ℕ) : Bool :=
  Nat.beq (p % 2) 1 && (Nat.ble p 53 || !(smallSieve.testBit ((p - 1) / 2)))

lemma primeOk_odd : ∀ p, primeOk p = true → p % 2 = 1 := by
  intro p h
  unfold primeOk at h
  rw [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

/-- Number of bits of the big sieve: the odd numbers below `2K = 8165754`. -/
def K : ℕ := 4082877
/-- Trial bound: every composite `m < 2K` has a prime factor `≤ B` (since `2K ≤ 2858^2`). -/
def B : ℕ := 2857

-- Prevent the elaborator from ever trying to unfold these (the kernel still can).
attribute [irreducible] K B

lemma primeOk_of_prime : ∀ p, p.Prime → p % 2 = 1 → p ≤ B → primeOk p = true := by
  intro p hp hpo hpB
  unfold primeOk
  rw [Bool.and_eq_true, hpo]
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_or_ge p 54 with h | h
  · rw [Nat.ble_eq_true_of_le (by omega)]; rfl
  · have hlt : (p - 1) / 2 < 1429 := by unfold B at hpB; omega
    have hbit := sieve_bit oddOk 1429 53 ((p - 1) / 2) oddOk_odd (oddOk_spec 53) (by norm_num) hlt
    have hp' : 2 * ((p - 1) / 2) + 1 = p := by omega
    rw [hp'] at hbit
    have : ¬ (sieveOf oddOk 1429 53).testBit ((p - 1) / 2) = true := by
      intro hb
      have := (hbit.1 hb).2
      rw [hp.minFac_eq] at this
      omega
    unfold smallSieve
    rw [Bool.eq_false_iff.2 this]
    simp

set_option exponentiation.threshold 100000000 in
/-- The popcount of the big sieve, computed in the kernel. -/
lemma pop_K : swarIter 23 (ZOf primeOk K B) = 3533119 := by decide +kernel

lemma count_prime_L : Nat.count Nat.Prime (2 * K) = 550172 := by
  have h := count_prime_of' primeOk K B 3533119 primeOk_odd primeOk_of_prime (by unfold B; norm_num)
    (by unfold K B; norm_num) (by unfold K B; norm_num) (by unfold K; norm_num) pop_K
  have hB : Nat.count Nat.Prime (B + 1) = 415 := by
    have : B + 1 = 2858 := by unfold B; norm_num
    rw [this]; exact count_2858
  rw [arith_of _ _ _ _ h, hB]
  unfold K; norm_num

/-- The `550172`-th prime is at most `8165753`. -/
lemma nth_prime_bound : Nat.nth Nat.Prime 550171 ≤ 8165753 := by
  have h := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := 2 * K) (k := 550171)
    (by rw [count_prime_L]; norm_num)
  unfold K at h
  omega

end Dis

namespace Dis

/- ### Part B: the residue `63945` is not hit by `2^k - k` for `k < 17135927` -/

lemma pow_mod_period {d m : ℕ} (h : 2^d % m = 1) (k : ℕ) : 2^k % m = 2^(k % d) % m := by
  conv_lhs => rw [← Nat.div_add_mod k d, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h, one_pow]
  rw [← Nat.mul_mod, one_mul]

lemma two_pow_mod_four (k : ℕ) (hk : 2 ≤ k) : 2^k % 4 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [pow_add]
  simp [Nat.mul_mod_left]

def condC (i j : ℕ) : Bool :=
  Nat.beq (2^((80200*i + j) % 147) % 343) ((63945 + 80200*i + j) % 343)

/-- For a residue `j` modulo `80200 = 200 · 401` with `j ≡ 3 (mod 4)`: no `k ≡ j (mod 80200)`
with `k < 17135927` satisfies the congruence modulo `343`. -/
def outerB (j : ℕ) : Bool :=
  !(Nat.beq (j % 4) 3) || forallB (fun i => Nat.ble 17135927 (80200*i + j) || !condC i j) 214

/-- The unique `j < 80200` with `j ≡ a (mod 200)` and `2^a ≡ 63945 + j (mod 401)`
(Chinese remainder theorem; `399 = 200⁻¹ mod 401` and `63945 ≡ 186 (mod 401)`). -/
def jOf (a : ℕ) : ℕ := a + 200 * (((2^a % 401 + 80014 - a) * 399) % 401)

/-- Only the `200` residues `jOf a` can satisfy the congruence modulo `401`. -/
def checkB : Bool := forallB (fun a => outerB (jOf a)) 200

lemma checkB_true : checkB = true := by decide +kernel

lemma jOf_eq (k : ℕ) (h : 2^(k % 200) % 401 = (63945 + k) % 401) : jOf (k % 200) = k % 80200 := by
  unfold jOf
  generalize hX : 2^(k % 200) % 401 = X at h
  have hX' : X < 401 := by rw [← hX]; exact Nat.mod_lt _ (by norm_num)
  omega

lemma not_hit (k : ℕ) (hk2 : 2 ≤ k) (hkM : k < 17135927) :
    2^k % 550172 ≠ (63945 + k) % 550172 := by
  intro h
  have h401 : 2^k % 401 = (63945 + k) % 401 := by
    have := congrArg (· % 401) h
    simp only at this
    rwa [Nat.mod_mod_of_dvd _ (by norm_num : 401 ∣ 550172),
      Nat.mod_mod_of_dvd _ (by norm_num : 401 ∣ 550172)] at this
  have h343 : 2^k % 343 = (63945 + k) % 343 := by
    have := congrArg (· % 343) h
    simp only at this
    rwa [Nat.mod_mod_of_dvd _ (by norm_num : 343 ∣ 550172),
      Nat.mod_mod_of_dvd _ (by norm_num : 343 ∣ 550172)] at this
  have h4 : 2^k % 4 = (63945 + k) % 4 := by
    have := congrArg (· % 4) h
    simp only at this
    rwa [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 550172),
      Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 550172)] at this
  have h4' : 2^k % 4 = 0 := two_pow_mod_four k hk2
  have p401 : 2^k % 401 = 2^(k % 200) % 401 := pow_mod_period (by norm_num) k
  have p343 : 2^k % 343 = 2^(k % 147) % 343 := pow_mod_period (by norm_num) k
  have hk : k = 80200 * (k / 80200) + k % 80200 := (Nat.div_add_mod k 80200).symm
  have hi214 : k / 80200 < 214 := by omega
  have hj : jOf (k % 200) = k % 80200 := jOf_eq k (by rw [← p401, h401])
  have hspec : outerB (jOf (k % 200)) = true :=
    forallB_spec _ _ checkB_true (k % 200) (Nat.mod_lt _ (by norm_num))
  rw [hj] at hspec
  unfold outerB at hspec
  have h43 : Nat.beq (k % 80200 % 4) 3 = true := by rw [Nat.beq_eq]; omega
  rw [h43, Bool.not_true, Bool.false_or] at hspec
  have hC := forallB_spec _ _ hspec (k / 80200) hi214
  have hlt : Nat.ble 17135927 (80200 * (k / 80200) + k % 80200) = false := by
    apply Bool.eq_false_iff.2
    intro hb
    have := Nat.le_of_ble_eq_true hb
    omega
  rw [hlt, Bool.false_or, Bool.not_eq_true'] at hC
  unfold condC at hC
  apply Nat.ne_of_beq_eq_false hC
  rw [add_assoc, ← hk, ← p343, h343]

lemma not_mem_image (k : ℕ) (hk1 : 1 ≤ k) (hkM : k ≤ 17135926) :
    ((2^k - k : ℕ) : ZMod 550172) ≠ ((63945 : ℕ) : ZMod 550172) := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have hle : k ≤ 2^k := Nat.lt_two_pow_self.le
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have : k = 1 := by omega
    subst this
    norm_num at h
  · apply not_hit k hk (by omega)
    have e : 2^k = (2^k - k) + k := by omega
    rw [e, Nat.add_mod, h, ← Nat.add_mod]

/- ### Part A: every residue mod `550172` is hit by some `2^k - k` with `k ≤ 82526390` -/

def condR (t' r : ℕ) : Bool :=
  Nat.ble 2 r && Nat.beq ((t' + r) % 4) 0 && Nat.beq (2^r % 49) ((t' + r) % 49)

/-- For every `t' < 196` there is an `r < 590` with `condR t' r` (searched in increasing order of
`r`, which is much cheaper since small `r` usually work). -/
def checkA : Bool := forallB (fun t' => existsB (fun i => condR t' (589 - i)) 590) 196

lemma checkA_true : checkA = true := by decide +kernel

lemma exists_r (t : ℕ) :
    ∃ r, 2 ≤ r ∧ r < 590 ∧ (t + r) % 4 = 0 ∧ 2^r % 49 = (t + r) % 49 := by
  have h := forallB_spec _ _ checkA_true (t % 196) (Nat.mod_lt _ (by norm_num))
  obtain ⟨i, hi, hc⟩ := existsB_spec _ _ h
  unfold condR at hc
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hc
  obtain ⟨⟨h2, h4⟩, h49⟩ := hc
  refine ⟨589 - i, h2, by omega, by omega, ?_⟩
  rw [h49]; omega

lemma two_pow_29400 : 2^29400 % 137543 = 1 := by decide +kernel

lemma aux_mod1 (c X t r q : ℕ) (htr : t + r ≤ X + 687715) (hc : c = X + 687715 - (t + r))
    (h : (29400 * q) % 137543 = c % 137543) : (t + (r + 29400 * q)) % 137543 = X % 137543 := by
  have h1 : t + r + 29400 * q ≡ t + r + c [MOD 137543] := Nat.ModEq.add_left _ h
  have h2 : t + r + c = X + 137543 * 5 := by omega
  have h3 : (X + 137543 * 5) % 137543 = X % 137543 := Nat.add_mul_mod_self_left X 137543 5
  unfold Nat.ModEq at h1
  rw [h2, h3] at h1
  rw [← add_assoc]; exact h1

lemma aux_mod2 (u q : ℕ) (hq : q = (u * 2138) % 2807) : (600 * q) % 2807 = u % 2807 := by omega

lemma aux_mod3 (c u q : ℕ) (hcu : c = 49 * u) (h600 : (600 * q) % 2807 = u % 2807) :
    (29400 * q) % 137543 = c % 137543 := by omega

lemma aux_mod4 (Y X t r q : ℕ) (h4a : Y % 4 = 0) (h4b : X % 4 = 0) (hper : Y % 137543 = X % 137543)
    (hr4 : (t + r) % 4 = 0) (key : (t + (r + 29400 * q)) % 137543 = X % 137543) :
    Y % 550172 = (t + (r + 29400 * q)) % 550172 := by
  have h1 : Y ≡ X [MOD 550172] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul (a := Y) (b := X) (m := 4) (n := 137543)
      (by norm_num)).1 ⟨by unfold Nat.ModEq; omega, hper⟩
    simpa using this
  have h2 : X ≡ t + (r + 29400 * q) [MOD 550172] := by
    have := (Nat.modEq_and_modEq_iff_modEq_mul (a := X) (b := t + (r + 29400 * q)) (m := 4)
      (n := 137543) (by norm_num)).1 ⟨by unfold Nat.ModEq; omega, key.symm⟩
    simpa using this
  exact h1.trans h2

lemma covers (t : ℕ) (ht : t < 550172) :
    ∃ k, 1 ≤ k ∧ k ≤ 82526390 ∧ 2^k % 550172 = (t + k) % 550172 := by
  obtain ⟨r, hr2, hr590, hr4, hr49⟩ := exists_r t
  have h4b : 2^r % 4 = 0 := two_pow_mod_four _ hr2
  generalize hX : 2^r = X at hr49 h4b
  have htr : t + r ≤ X + 687715 := by omega
  have hc49 : (X + 687715 - (t + r)) % 49 = 0 := by
    apply Nat.sub_mod_eq_zero_of_mod_eq
    omega
  obtain ⟨c, hc⟩ : ∃ c, c = X + 687715 - (t + r) := ⟨_, rfl⟩
  rw [← hc] at hc49
  obtain ⟨u, hu⟩ : ∃ u, u = c / 49 := ⟨_, rfl⟩
  have hcu : c = 49 * u := by omega
  obtain ⟨q, hq⟩ : ∃ q, q = (u * 2138) % 2807 := ⟨_, rfl⟩
  have hq' : q < 2807 := by omega
  refine ⟨r + 29400 * q, by omega, by omega, ?_⟩
  have hper : 2^(r + 29400 * q) % 137543 = X % 137543 := by
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod (2^29400) q 137543, two_pow_29400, one_pow, hX]
    norm_num
  have h4a : 2^(r + 29400 * q) % 4 = 0 := two_pow_mod_four _ (by omega)
  generalize hY : 2^(r + 29400 * q) = Y at hper h4a ⊢
  clear hX hY
  have h600 := aux_mod2 u q hq
  have h29400 := aux_mod3 c u q hcu h600
  have key := aux_mod1 c X t r q htr hc h29400
  exact aux_mod4 Y X t r q h4a h4b hper hr4 key

end Dis


namespace Dis

/-- Every residue modulo `550172` is attained by `2^k - k` for some `1 ≤ k ≤ 82526390`. -/
lemma prop_holds : A232616_prop 550172 82526390 := by
  unfold A232616_prop
  symm
  rw [Finset.eq_univ_iff_forall]
  intro x
  rw [Finset.mem_image]
  obtain ⟨k, hk1, hkm, hk⟩ := covers x.val x.val_lt
  refine ⟨k, Finset.mem_Icc.2 ⟨hk1, hkm⟩, ?_⟩
  have hle : k ≤ 2^k := Nat.lt_two_pow_self.le
  have h1 : ((2^k - k : ℕ) : ZMod 550172) = ((x.val : ℕ) : ZMod 550172) := by
    rw [ZMod.natCast_eq_natCast_iff']
    have : (2^k - k) + k ≡ x.val + k [MOD 550172] := by
      rw [Nat.sub_add_cancel hle]; exact hk
    exact Nat.ModEq.add_right_cancel' k this
  rw [h1, ZMod.natCast_zmod_val]

end Dis

/-- The conjecture fails at `n = 550172 = 2^2 · 7^3 · 401`: here `A232616 n = 17135927`
while `2 * (prime(n) - 1) = 2 * (8165753 - 1) = 16331504`. -/
theorem oeis_232616_conjecture_i.disproof : ¬ (type_of% @oeis_232616_conjecture_i) := by
  intro h
  have h1 := h 550172 (by norm_num)
  have h2 : A232616 550172 = sInf {m | A232616_prop 550172 m} := by
    rw [A232616, dif_neg (by norm_num)]
  rw [h2] at h1
  have h3 : 17135927 ≤ sInf {m | A232616_prop 550172 m} := by
    apply le_csInf ⟨82526390, Dis.prop_holds⟩
    intro m hm
    by_contra hlt
    push_neg at hlt
    have hmem : ((63945 : ℕ) : ZMod 550172) ∈
        (Finset.Icc 1 m).image (fun k => ((2^k - k : ℕ) : ZMod 550172)) := by
      have hm' : (Finset.univ : Finset (ZMod 550172)) = _ := hm
      rw [← hm']
      exact Finset.mem_univ _
    rw [Finset.mem_image] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    rw [Finset.mem_Icc] at hk
    exact Dis.not_mem_image k hk.1 (by omega) hkeq
  have h4 := Dis.nth_prime_bound
  have h5 : Nat.nth Nat.Prime (550172 - 1) = Nat.nth Nat.Prime 550171 := rfl
  rw [h5] at h1
  omega
