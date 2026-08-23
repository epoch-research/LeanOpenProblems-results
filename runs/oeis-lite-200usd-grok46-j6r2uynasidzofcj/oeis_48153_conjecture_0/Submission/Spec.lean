import FormalConjectures.Util.ProblemImports

open Finset

/--
A048153: $a(n) = \sum_{k=1}^n (k^2 \bmod n)$.
This sequence is defined in Lean as the sum of $k^2 \bmod n$ for $k \in \{0, 1, \dots, n-1\}$.
-/
def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

/-! ### Setup: identify the sum with remainders of squares in `ZMod n`. -/

lemma A048153_eq_sum_val (n : ℕ) [NeZero n] :
    A048153 n = ∑ k : ZMod n, (k ^ 2).val := by
  unfold A048153
  have himg : (univ : Finset (ZMod n)).image ZMod.val = range n := by
    ext k
    simp only [mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ZMod.val_lt a
    · intro hk
      refine ⟨(k : ZMod n), ?_⟩
      exact ZMod.val_natCast_of_lt hk
  rw [← himg, sum_image]
  · refine sum_congr rfl fun k _ => ?_
    simp [pow_two, ZMod.val_mul]
  · intro x _ y _ hxy
    exact ZMod.val_injective n hxy

/-- The original bound follows from the slightly stronger estimate
`a(n) ≤ n(n-1)/2`. -/
lemma le_of_le_mul_sub_one {n : ℕ} (hn : 1 ≤ n)
    (h : A048153 n ≤ n * (n - 1) / 2) :
    A048153 n ≤ (n ^ 2 - 1) / 2 := by
  refine h.trans (Nat.div_le_div_right ?_)
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_right n hn
  have : n * (n - 1) = n * n - n := by
    rw [Nat.mul_sub_left_distrib, mul_one]
  rw [this, Nat.pow_two]
  exact Nat.sub_le_sub_left hn (n * n)

/-- Number of solutions of `x ^ 2 = 0` in `ZMod n`. -/
def numSquareZero (n : ℕ) [Fintype (ZMod n)] : ℕ :=
  ((univ : Finset (ZMod n)).filter (fun k : ZMod n => k ^ 2 = 0)).card

lemma numSquareZero_pos (n : ℕ) [NeZero n] : 1 ≤ numSquareZero n := by
  refine Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨0, ?_⟩)
  simp [numSquareZero]

lemma numSquareZero_le (n : ℕ) [NeZero n] : numSquareZero n ≤ n := by
  simpa [numSquareZero, ZMod.card n] using
    (card_filter_le (univ : Finset (ZMod n)) (fun k : ZMod n => k ^ 2 = 0))

lemma val_sq_add_val_neg_sq (n : ℕ) [NeZero n] (k : ZMod n) :
    (k ^ 2).val + (-(k ^ 2)).val = if k ^ 2 = 0 then 0 else n := by
  rw [ZMod.neg_val]
  split_ifs with h
  · simp [h]
  · have hpos : 0 < (k ^ 2).val := (ZMod.val_pos).2 h
    have hle : (k ^ 2).val ≤ n := (k ^ 2).val_lt.le
    omega

lemma card_nonzero_sq (n : ℕ) [NeZero n] :
    ((univ : Finset (ZMod n)).filter (fun k : ZMod n => k ^ 2 ≠ 0)).card =
      n - numSquareZero n := by
  have hdisj :
      Disjoint
        ((univ : Finset (ZMod n)).filter (fun k : ZMod n => k ^ 2 = 0))
        ((univ : Finset (ZMod n)).filter (fun k : ZMod n => k ^ 2 ≠ 0)) :=
    disjoint_filter.mpr (fun _ _ hx => not_not.mpr hx)
  have hunion :
      ((univ : Finset (ZMod n)).filter (fun k : ZMod n => k ^ 2 = 0)) ∪
        ((univ : Finset (ZMod n)).filter (fun k : ZMod n => k ^ 2 ≠ 0)) = univ := by
    ext x
    by_cases hx : x ^ 2 = 0 <;> simp [hx]
  have hcard := card_union_of_disjoint hdisj
  rw [hunion, card_univ, ZMod.card n] at hcard
  unfold numSquareZero
  omega

/-- Multiplication by a square root of `-1` is an equivalence. -/
def mulSqrtNegOneEquiv {n : ℕ} (i : ZMod n) (hi : i * i = -1) : ZMod n ≃ ZMod n where
  toFun := fun k => i * k
  invFun := fun k => -i * k
  left_inv := fun k => by
    calc
      -i * (i * k) = -(i * i) * k := by ring
      _ = -(-1) * k := by rw [hi]
      _ = k := by ring
  right_inv := fun k => by
    calc
      i * (-i * k) = -(i * i) * k := by ring
      _ = -(-1) * k := by rw [hi]
      _ = k := by ring

/-- If `-1` is a square modulo `n`, then `a(n) = n(n - N₀)/2`. -/
lemma A048153_eq_of_neg_one_isSquare (n : ℕ) [NeZero n]
    (h : IsSquare (-1 : ZMod n)) :
    A048153 n = n * (n - numSquareZero n) / 2 := by
  obtain ⟨i, hi⟩ := h
  have hi' : i * i = -1 := hi.symm
  have hsum :
      ∑ k : ZMod n, (k ^ 2).val = ∑ k : ZMod n, (-(k ^ 2)).val := by
    have hmap : ∀ k : ZMod n, ((i * k) ^ 2).val = (-(k ^ 2)).val := by
      intro k
      rw [mul_pow, pow_two, hi', neg_one_mul]
    rw [← Equiv.sum_comp (mulSqrtNegOneEquiv i hi')]
    exact sum_congr rfl fun k _ => hmap k
  have hpair :
      ∑ k : ZMod n, ((k ^ 2).val + (-(k ^ 2)).val) =
        n * (n - numSquareZero n) := by
    simp_rw [val_sq_add_val_neg_sq]
    rw [sum_ite, sum_const, sum_const, smul_zero, zero_add, smul_eq_mul,
      card_nonzero_sq, mul_comm]
  have h2 :
      2 * ∑ k : ZMod n, (k ^ 2).val = n * (n - numSquareZero n) := by
    calc
      2 * ∑ k : ZMod n, (k ^ 2).val
          = ∑ k : ZMod n, (k ^ 2).val + ∑ k : ZMod n, (k ^ 2).val := by ring
      _ = ∑ k : ZMod n, (k ^ 2).val + ∑ k : ZMod n, (-(k ^ 2)).val := by
          rw [hsum]
      _ = ∑ k : ZMod n, ((k ^ 2).val + (-(k ^ 2)).val) := by
          rw [← sum_add_distrib]
      _ = n * (n - numSquareZero n) := hpair
  rw [A048153_eq_sum_val]
  have h2' : (∑ k : ZMod n, (k ^ 2).val) * 2 = n * (n - numSquareZero n) := by
    rw [mul_comm]; exact h2
  exact Nat.eq_div_of_mul_eq_left (by decide) h2'

lemma A048153_le_of_neg_one_isSquare (n : ℕ) [NeZero n]
    (h : IsSquare (-1 : ZMod n)) :
    A048153 n ≤ n * (n - 1) / 2 := by
  rw [A048153_eq_of_neg_one_isSquare n h]
  have : n * (n - numSquareZero n) ≤ n * (n - 1) := by
    gcongr
    have hN : 1 ≤ numSquareZero n := numSquareZero_pos n
    have hN' : numSquareZero n ≤ n := numSquareZero_le n
    omega
  exact Nat.div_le_div_right this


/-! ### Powers of two. -/

lemma two_pow_succ (e : ℕ) (he : 1 ≤ e) : 2 ^ e = 2 * 2 ^ (e - 1) := by
  conv_lhs => rw [← Nat.sub_add_cancel he]
  rw [pow_succ, mul_comm]

/-- For `e ≥ 2`, `(q + 2^{e-1} t)² ≡ q² (mod 2^e)`. -/
lemma sq_add_two_pow_mod (e q t : ℕ) (he : 2 ≤ e) :
    (q + 2 ^ (e - 1) * t) ^ 2 % 2 ^ e = q ^ 2 % 2 ^ e := by
  have he1 : 1 ≤ e := by omega
  have hmul : (q + 2 ^ (e - 1) * t) ^ 2 =
      q ^ 2 + 2 * q * (2 ^ (e - 1) * t) + (2 ^ (e - 1) * t) ^ 2 := by ring
  rw [hmul]
  have hmid : 2 * q * (2 ^ (e - 1) * t) = 2 ^ e * (q * t) := by
    have := two_pow_succ e he1
    rw [this]; ring
  have hlast : (2 ^ (e - 1) * t) ^ 2 = 2 ^ e * (2 ^ (e - 2) * t ^ 2) := by
    have hpow : (2 ^ (e - 1)) ^ 2 = 2 ^ e * 2 ^ (e - 2) := by
      rw [← pow_mul, Nat.mul_comm (e - 1) 2]
      have : 2 * (e - 1) = e + (e - 2) := by omega
      rw [this, pow_add]
    rw [mul_pow, hpow]
    ring
  rw [hmid, hlast]
  have : q ^ 2 + 2 ^ e * (q * t) + 2 ^ e * (2 ^ (e - 2) * t ^ 2) =
      q ^ 2 + 2 ^ e * (q * t + 2 ^ (e - 2) * t ^ 2) := by ring
  rw [this, Nat.add_mul_mod_self_left]

/-- Splitting `{0, …, 2^e - 1}` into two halves. -/
lemma range_two_pow_split (e : ℕ) (he : 1 ≤ e) :
    range (2 ^ e) =
      range (2 ^ (e - 1)) ∪
        (range (2 ^ (e - 1))).image (fun q => q + 2 ^ (e - 1)) := by
  ext k
  simp only [mem_union, mem_range, mem_image]
  constructor
  · intro hk
    by_cases h : k < 2 ^ (e - 1)
    · exact Or.inl h
    · refine Or.inr ⟨k - 2 ^ (e - 1), ?_, Nat.sub_add_cancel (le_of_not_gt h)⟩
      have heq := two_pow_succ e he
      omega
  · rintro (hk | ⟨q, hq, rfl⟩)
    · have : 2 ^ (e - 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · have heq := two_pow_succ e he
      omega

lemma disjoint_range_two_pow_halves (e : ℕ) :
    Disjoint (range (2 ^ (e - 1)))
      ((range (2 ^ (e - 1))).image (fun q => q + 2 ^ (e - 1))) := by
  refine disjoint_left.mpr ?_
  intro k hk hk'
  rcases mem_image.mp hk' with ⟨q, hq, rfl⟩
  simp only [mem_range] at hk hq
  omega

lemma A048153_two_pow_rec (e : ℕ) (he : 2 ≤ e) :
    A048153 (2 ^ e) =
      2 * ∑ q ∈ range (2 ^ (e - 1)), q ^ 2 % 2 ^ e := by
  unfold A048153
  have he1 : 1 ≤ e := by omega
  rw [range_two_pow_split e he1, sum_union (disjoint_range_two_pow_halves e)]
  rw [sum_image (by intro x _ y _ hxy; simpa using hxy)]
  refine Eq.trans ?_ (two_mul _).symm
  refine congrArg₂ (· + ·) rfl ?_
  refine sum_congr rfl fun q _ => ?_
  simpa using sq_add_two_pow_mod e q 1 he

/-- `N e` counts residues `q < 2^{e-1}` whose square has high bit `1` modulo `2^e`. -/
def highBitSq (e : ℕ) : ℕ :=
  (range (2 ^ (e - 1))).filter (fun q => 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) |>.card

lemma two_pow_eq_mul_two (e : ℕ) (he : 1 ≤ e) : 2 ^ e = 2 ^ (e - 1) * 2 := by
  rw [two_pow_succ e he, mul_comm]

/-- The residue `q² % 2^e` splits as a low half plus a high bit. -/
lemma sq_mod_two_pow_split (e q : ℕ) (he : 1 ≤ e) :
    q ^ 2 % 2 ^ e =
      q ^ 2 % 2 ^ (e - 1) +
        2 ^ (e - 1) * if 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e then 1 else 0 := by
  set r := q ^ 2 % 2 ^ e
  have hrlt : r < 2 ^ e := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hdiv := two_pow_eq_mul_two e he
  have hlow : q ^ 2 % 2 ^ (e - 1) = r % 2 ^ (e - 1) := by
    have : 2 ^ (e - 1) ∣ 2 ^ e := ⟨2, hdiv⟩
    exact (Nat.mod_mod_of_dvd (q ^ 2) this).symm
  by_cases h : 2 ^ (e - 1) ≤ r
  · have hr' : r % 2 ^ (e - 1) = r - 2 ^ (e - 1) := by
      have : r < 2 ^ (e - 1) + 2 ^ (e - 1) := by
        rw [← two_mul, ← two_pow_succ e he]; exact hrlt
      have : r - 2 ^ (e - 1) < 2 ^ (e - 1) := by omega
      rw [← Nat.sub_add_cancel h]
      simp [Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt this]
    simp [h, hlow, hr', Nat.sub_add_cancel h]
  · have hlt : r < 2 ^ (e - 1) := Nat.lt_of_not_ge h
    simp [h, hlow, Nat.mod_eq_of_lt hlt]

lemma A048153_two_pow_highBit (e : ℕ) (he : 2 ≤ e) :
    A048153 (2 ^ e) =
      2 * A048153 (2 ^ (e - 1)) + 2 ^ e * highBitSq e := by
  rw [A048153_two_pow_rec e he]
  unfold A048153 highBitSq
  have he1 : 1 ≤ e := by omega
  have hsum :
      ∑ q ∈ range (2 ^ (e - 1)), q ^ 2 % 2 ^ e =
        ∑ q ∈ range (2 ^ (e - 1)), q ^ 2 % 2 ^ (e - 1) +
          2 ^ (e - 1) *
            ∑ q ∈ range (2 ^ (e - 1)),
              (if 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e then 1 else 0 : ℕ) := by
    rw [sum_congr rfl (fun q _ => sq_mod_two_pow_split e q he1),
      sum_add_distrib, ← mul_sum]
  rw [hsum]
  have hcard :
      ∑ q ∈ range (2 ^ (e - 1)),
          (if 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e then 1 else 0 : ℕ) =
        ((range (2 ^ (e - 1))).filter
          (fun q => 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)).card := by
    simp [sum_boole, Nat.cast_id]
  rw [hcard]
  have heq : 2 ^ e = 2 * 2 ^ (e - 1) := by
    rw [two_pow_eq_mul_two e he1, mul_comm]
  rw [heq]
  ring

lemma highBitSq_two : highBitSq 2 = 0 := by decide
lemma highBitSq_three : highBitSq 3 = 1 := by decide

lemma even_two_pow_of_pos {k : ℕ} (hk : 0 < k) : Even (2 ^ k) :=
  Nat.even_pow.mpr ⟨even_two, Nat.pos_iff_ne_zero.mp hk⟩

lemma two_mul_two_pow (e : ℕ) (he : 1 ≤ e) :
    2 ^ (e - 1) + 2 ^ (e - 1) = 2 ^ e := by
  rw [← two_mul, ← two_pow_succ e he]

lemma two_pow_sub_two (e : ℕ) (he : 2 ≤ e) :
    2 * 2 ^ (e - 2) = 2 ^ (e - 1) := by
  have : e - 1 = e - 2 + 1 := by omega
  rw [this, pow_succ, mul_comm]

lemma two_pow_sub_two' (e : ℕ) (he : 2 ≤ e) :
    2 ^ (e - 2) * 2 = 2 ^ (e - 1) := by
  rw [mul_comm, two_pow_sub_two e he]

/-- For `e ≥ 4` and odd `q`, `(q + 2^{e-2})² ≡ q² + 2^{e-1} (mod 2^e)`. -/
lemma sq_add_half_mod (e q : ℕ) (he : 4 ≤ e) (hodd : Odd q) :
    (q + 2 ^ (e - 2)) ^ 2 % 2 ^ e = (q ^ 2 + 2 ^ (e - 1)) % 2 ^ e := by
  obtain ⟨t, ht⟩ := hodd
  have hdiff :
      (q + 2 ^ (e - 2)) ^ 2 = q ^ 2 + 2 ^ (e - 1) + 2 ^ e * (t + 2 ^ (e - 4)) := by
    have hbin : (q + 2 ^ (e - 2)) ^ 2 =
        q ^ 2 + 2 * q * 2 ^ (e - 2) + (2 ^ (e - 2)) ^ 2 := add_sq _ _
    have hmid : 2 * q * 2 ^ (e - 2) = q * 2 ^ (e - 1) := by
      rw [mul_comm 2 q, mul_assoc, two_pow_sub_two e (by omega)]
    have hlast : (2 ^ (e - 2)) ^ 2 = 2 ^ e * 2 ^ (e - 4) := by
      rw [← pow_mul, Nat.mul_comm (e - 2) 2]
      have : 2 * (e - 2) = e + (e - 4) := by omega
      rw [this, pow_add]
    have hq : q * 2 ^ (e - 1) = 2 ^ (e - 1) + t * 2 ^ e := by
      rw [ht, add_mul, one_mul, mul_comm 2 t, mul_assoc, two_pow_succ e (by omega), add_comm]
    calc
      (q + 2 ^ (e - 2)) ^ 2
          = q ^ 2 + 2 * q * 2 ^ (e - 2) + (2 ^ (e - 2)) ^ 2 := hbin
      _ = q ^ 2 + q * 2 ^ (e - 1) + 2 ^ e * 2 ^ (e - 4) := by rw [hmid, hlast]
      _ = q ^ 2 + (2 ^ (e - 1) + t * 2 ^ e) + 2 ^ e * 2 ^ (e - 4) := by rw [hq]
      _ = q ^ 2 + 2 ^ (e - 1) + 2 ^ e * (t + 2 ^ (e - 4)) := by
          rw [add_assoc (q ^ 2), add_assoc (q ^ 2), add_left_cancel_iff,
            add_assoc, add_left_cancel_iff, mul_comm t, ← mul_add]
  rw [hdiff, Nat.add_mul_mod_self_left]

/-- Adding `2^{e-2}` flips the high bit of an odd square, for `e ≥ 4`. -/
lemma sq_add_half_flip_highBit (e q : ℕ) (he : 4 ≤ e) (hodd : Odd q) :
    (2 ^ (e - 1) ≤ (q + 2 ^ (e - 2)) ^ 2 % 2 ^ e) ↔
      ¬ (2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) := by
  rw [sq_add_half_mod e q he hodd]
  set r := q ^ 2 % 2 ^ e
  have hrlt : r < 2 ^ e := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hsum : 2 ^ (e - 1) + 2 ^ (e - 1) = 2 ^ e := two_mul_two_pow e (by omega)
  have hre : (q ^ 2 + 2 ^ (e - 1)) % 2 ^ e = (r + 2 ^ (e - 1)) % 2 ^ e := by
    have hdiv := Nat.div_add_mod (q ^ 2) (2 ^ e)
    calc
      (q ^ 2 + 2 ^ (e - 1)) % 2 ^ e
          = (2 ^ e * (q ^ 2 / 2 ^ e) + q ^ 2 % 2 ^ e + 2 ^ (e - 1)) % 2 ^ e := by
            rw [hdiv]
      _ = (2 ^ e * (q ^ 2 / 2 ^ e) + (r + 2 ^ (e - 1))) % 2 ^ e := by
            rw [add_assoc]
      _ = (r + 2 ^ (e - 1)) % 2 ^ e := Nat.mul_add_mod_self_left _ _ _
  rw [hre]
  by_cases h : 2 ^ (e - 1) ≤ r
  · have heq : r + 2 ^ (e - 1) = 2 ^ e + (r - 2 ^ (e - 1)) := by omega
    have hlt : r - 2 ^ (e - 1) < 2 ^ e := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
    have : ¬ 2 ^ (e - 1) ≤ r - 2 ^ (e - 1) := by omega
    simp [h, this]
  · have : r + 2 ^ (e - 1) < 2 ^ e := by omega
    rw [Nat.mod_eq_of_lt this]
    simp [h]

lemma odd_image_eq_filter (k : ℕ) :
    (range (2 ^ k)).image (fun i => 2 * i + 1) = (range (2 ^ (k + 1))).filter Odd := by
  ext n
  simp only [mem_image, mem_range, mem_filter]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨by omega, odd_two_mul_add_one i⟩
  · rintro ⟨hn, hodd⟩
    obtain ⟨i, rfl⟩ := hodd
    exact ⟨i, by omega, rfl⟩

lemma inj_two_mul_add_one : Function.Injective (fun i : ℕ => 2 * i + 1) := by
  intro a b h
  have : 2 * a + 1 = 2 * b + 1 := h
  omega

lemma inj_two_mul : Function.Injective (fun u : ℕ => 2 * u) := by
  intro a b h
  have : 2 * a = 2 * b := h
  omega

lemma inj_add (c : ℕ) : Function.Injective (fun x : ℕ => x + c) := by
  intro a b h
  have : a + c = b + c := h
  omega

lemma card_odd_range_two_pow (k : ℕ) :
    ((range (2 ^ k)).filter Odd).card = 2 ^ k / 2 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [← odd_image_eq_filter k, card_image_of_injective _ inj_two_mul_add_one,
      card_range, pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]

lemma card_odd_range_two_pow' (k : ℕ) (hk : 1 ≤ k) :
    ((range (2 ^ k)).filter Odd).card = 2 ^ (k - 1) := by
  rw [card_odd_range_two_pow, two_pow_succ k hk, mul_comm,
    Nat.mul_div_cancel _ (by decide : 0 < 2)]

lemma odd_add_even_pow {q e : ℕ} (he : 1 ≤ e) : Odd (q + 2 ^ e) ↔ Odd q := by
  have : Even (2 ^ e) := even_two_pow_of_pos he
  rw [Nat.odd_add]
  simp [this]

/-- Odds in `[0, 2^{e-1})` split as odds in the first half and their shifts by `2^{e-2}`. -/
lemma odd_range_split (e : ℕ) (he : 3 ≤ e) :
    (range (2 ^ (e - 1))).filter Odd =
      (range (2 ^ (e - 2))).filter Odd ∪
        ((range (2 ^ (e - 2))).filter Odd).image (fun q => q + 2 ^ (e - 2)) := by
  ext q
  simp only [mem_filter, mem_union, mem_image, mem_range]
  have hpow : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := (two_pow_sub_two e (by omega)).symm
  constructor
  · rintro ⟨hq, hodd⟩
    by_cases h : q < 2 ^ (e - 2)
    · exact Or.inl ⟨h, hodd⟩
    · refine Or.inr ⟨q - 2 ^ (e - 2), ⟨?_, ?_⟩, Nat.sub_add_cancel (le_of_not_gt h)⟩
      · omega
      · have hodd' : Odd (q - 2 ^ (e - 2) + 2 ^ (e - 2)) := by
          rwa [Nat.sub_add_cancel (le_of_not_gt h)]
        rwa [odd_add_even_pow (by omega)] at hodd'
  · rintro (⟨hq, hodd⟩ | ⟨r, ⟨hr, hodd⟩, rfl⟩)
    · exact ⟨by omega, hodd⟩
    · exact ⟨by omega, (odd_add_even_pow (by omega)).mpr hodd⟩

lemma disjoint_odd_range_halves (e : ℕ) :
    Disjoint
      ((range (2 ^ (e - 2))).filter Odd)
      (((range (2 ^ (e - 2))).filter Odd).image (fun q => q + 2 ^ (e - 2))) := by
  refine disjoint_left.mpr ?_
  intro q hq hq'
  rcases mem_image.mp hq' with ⟨r, hr, rfl⟩
  simp only [mem_filter, mem_range] at hq hr
  omega

lemma odd_of_mem_odd_filter {s : Finset ℕ} {q : ℕ}
    (hq : q ∈ s.filter Odd) : Odd q :=
  (mem_filter.mp hq).2

lemma mem_range_of_mem_odd_filter {n q : ℕ}
    (hq : q ∈ (range n).filter Odd) : q < n :=
  mem_range.mp (mem_filter.mp hq).1

/-- High-bit odds in `[0, 2^{e-1})` are `s_hi ∪ image (+ 2^{e-2}) s_lo`. -/
lemma odd_highBit_eq (e : ℕ) (he : 4 ≤ e) :
    (range (2 ^ (e - 1))).filter
      (fun q => Odd q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) =
    ((range (2 ^ (e - 2))).filter Odd).filter
      (fun q => 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) ∪
      (((range (2 ^ (e - 2))).filter Odd).filter
        (fun q => ¬ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)).image
        (fun q => q + 2 ^ (e - 2)) := by
  have hsplit := odd_range_split e (by omega)
  ext q
  constructor
  · intro hq
    have hq' := mem_filter.mp hq
    have hodd : Odd q := hq'.2.1
    have hhi := hq'.2.2
    have hqodd : q ∈ (range (2 ^ (e - 1))).filter Odd :=
      mem_filter.mpr ⟨hq'.1, hodd⟩
    rw [hsplit, mem_union] at hqodd
    rcases hqodd with hq1 | hq2
    · exact mem_union_left _ (mem_filter.mpr ⟨hq1, hhi⟩)
    · rcases mem_image.mp hq2 with ⟨r, hr, rfl⟩
      refine mem_union_right _ (mem_image.mpr ⟨r, ⟨mem_filter.mpr ⟨hr, ?_⟩, rfl⟩⟩)
      exact (sq_add_half_flip_highBit e r he (odd_of_mem_odd_filter hr)).1 hhi
  · intro hq
    rw [mem_union] at hq
    rcases hq with hq1 | hq2
    · have hq1' := mem_filter.mp hq1
      have hqodd : q ∈ (range (2 ^ (e - 1))).filter Odd := by
        rw [hsplit]; exact mem_union_left _ hq1'.1
      exact mem_filter.mpr
        ⟨(mem_filter.mp hqodd).1, odd_of_mem_odd_filter hqodd, hq1'.2⟩
    · rcases mem_image.mp hq2 with ⟨r, hr, rfl⟩
      have hr' := mem_filter.mp hr
      have hpow : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := (two_pow_sub_two e (by omega)).symm
      have hrlt := mem_range_of_mem_odd_filter hr'.1
      refine mem_filter.mpr ⟨?_, (odd_add_even_pow (by omega)).mpr (odd_of_mem_odd_filter hr'.1), ?_⟩
      · exact mem_range.mpr (by omega)
      · exact (sq_add_half_flip_highBit e r he (odd_of_mem_odd_filter hr'.1)).2 hr'.2

lemma odd_highBit_card (e : ℕ) (he : 4 ≤ e) :
    ((range (2 ^ (e - 1))).filter
      (fun q => Odd q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)).card = 2 ^ (e - 3) := by
  rw [odd_highBit_eq e he]
  set s := (range (2 ^ (e - 2))).filter Odd
  set sHi := s.filter (fun q => 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)
  set sLo := s.filter (fun q => ¬ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)
  have hdisj : Disjoint sHi (sLo.image (fun q => q + 2 ^ (e - 2))) := by
    refine disjoint_left.mpr ?_
    intro x hx hx'
    rcases mem_image.mp hx' with ⟨r, hr, rfl⟩
    have : r + 2 ^ (e - 2) < 2 ^ (e - 2) :=
      mem_range_of_mem_odd_filter (mem_filter.mp hx).1
    omega
  rw [card_union_of_disjoint hdisj,
    card_image_of_injective _ (inj_add _)]
  have hdisj' : Disjoint sHi sLo := disjoint_filter_filter_not s _ _
  have hunion : sHi ∪ sLo = s := by
    ext x
    simp only [sHi, sLo, mem_union, mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases h : 2 ^ (e - 1) ≤ x ^ 2 % 2 ^ e
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hscard : s.card = 2 ^ (e - 3) :=
    card_odd_range_two_pow' (e - 2) (by omega)
  have := card_union_of_disjoint hdisj'
  rw [hunion] at this
  omega

/-- Evens in `[0, 2^{e-1})` are `2u` for `u < 2^{e-2}`. -/
lemma even_range_eq_image (e : ℕ) (he : 2 ≤ e) :
    (range (2 ^ (e - 1))).filter Even =
      (range (2 ^ (e - 2))).image (fun u => 2 * u) := by
  ext q
  simp only [mem_filter, mem_range, mem_image]
  constructor
  · rintro ⟨hq, hev⟩
    obtain ⟨u, rfl⟩ := even_iff_exists_two_mul.mp hev
    refine ⟨u, ?_, rfl⟩
    have hpow : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := (two_pow_sub_two e he).symm
    omega
  · rintro ⟨u, hu, rfl⟩
    have hpow : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := (two_pow_sub_two e he).symm
    exact ⟨by omega, even_two_mul u⟩

lemma pow_two_add_two (k : ℕ) : 2 ^ (k + 2) = 4 * 2 ^ k := by
  rw [pow_add, pow_two]
  norm_num
  ring

lemma four_mul_mod (e u : ℕ) (he : 2 ≤ e) :
    (2 * u) ^ 2 % 2 ^ e = 4 * (u ^ 2 % 2 ^ (e - 2)) := by
  have hpow : 2 ^ e = 4 * 2 ^ (e - 2) := by
    have heq : e = (e - 2) + 2 := by omega
    conv_lhs => rw [heq]
    exact pow_two_add_two (e - 2)
  have hsq : (2 * u) ^ 2 = 4 * u ^ 2 := by
    rw [mul_pow]
    norm_num
  set q := u ^ 2 / 2 ^ (e - 2)
  set r := u ^ 2 % 2 ^ (e - 2)
  have hdiv : u ^ 2 = 2 ^ (e - 2) * q + r := (Nat.div_add_mod _ _).symm
  have hrlt : r < 2 ^ (e - 2) := Nat.mod_lt _ (Nat.pow_pos (by decide))
  rw [hsq, hdiv, mul_add, ← mul_assoc, ← hpow, Nat.mul_add_mod_self_left]
  have : 4 * r < 2 ^ e := by
    rw [hpow]; nlinarith
  rw [Nat.mod_eq_of_lt this]

lemma even_highBit_iff (e u : ℕ) (he : 4 ≤ e) :
    (2 ^ (e - 1) ≤ (2 * u) ^ 2 % 2 ^ e) ↔ 2 ^ (e - 3) ≤ u ^ 2 % 2 ^ (e - 2) := by
  rw [four_mul_mod e u (by omega)]
  constructor
  · intro h
    have hpow : 2 ^ (e - 1) = 4 * 2 ^ (e - 3) := by
      have heq : e - 1 = (e - 3) + 2 := by omega
      conv_lhs => rw [heq]
      exact pow_two_add_two (e - 3)
    rw [hpow] at h
    have hlt : u ^ 2 % 2 ^ (e - 2) < 2 ^ (e - 2) :=
      Nat.mod_lt _ (Nat.pow_pos (by decide))
    omega
  · intro h
    have hpow : 2 ^ (e - 1) = 4 * 2 ^ (e - 3) := by
      have heq : e - 1 = (e - 3) + 2 := by omega
      conv_lhs => rw [heq]
      exact pow_two_add_two (e - 3)
    rw [hpow]
    omega

/-- Squares modulo `2^{e-2}` are unchanged by adding `2^{e-3}`, for `e ≥ 4`. -/
lemma sq_add_quarter_mod (e v : ℕ) (he : 4 ≤ e) :
    (v + 2 ^ (e - 3)) ^ 2 % 2 ^ (e - 2) = v ^ 2 % 2 ^ (e - 2) := by
  have hbin : (v + 2 ^ (e - 3)) ^ 2 =
      v ^ 2 + 2 * v * 2 ^ (e - 3) + (2 ^ (e - 3)) ^ 2 := add_sq _ _
  have hmid : 2 * v * 2 ^ (e - 3) = v * 2 ^ (e - 2) := by
    have : 2 * 2 ^ (e - 3) = 2 ^ (e - 2) := by
      have : e - 2 = e - 3 + 1 := by omega
      rw [this, pow_succ, mul_comm]
    rw [mul_comm 2 v, mul_assoc, this]
  have hlast : (2 ^ (e - 3)) ^ 2 = 2 ^ (e - 2) * 2 ^ (e - 4) := by
    rw [← pow_mul, Nat.mul_comm (e - 3) 2]
    have : 2 * (e - 3) = (e - 2) + (e - 4) := by omega
    rw [this, pow_add]
  have hexp : (v + 2 ^ (e - 3)) ^ 2 =
      v ^ 2 + 2 ^ (e - 2) * (v + 2 ^ (e - 4)) := by
    rw [hbin, hmid, hlast]
    rw [add_assoc, add_left_cancel_iff, mul_comm v, ← mul_add]
  rw [hexp, Nat.add_mul_mod_self_left]

lemma even_highBit_card (e : ℕ) (he : 4 ≤ e) :
    ((range (2 ^ (e - 1))).filter
      (fun q => Even q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)).card =
      2 * highBitSq (e - 2) := by
  have himg := even_range_eq_image e (by omega)
  have :
      (range (2 ^ (e - 1))).filter
        (fun q => Even q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) =
      ((range (2 ^ (e - 2))).filter
        (fun u => 2 ^ (e - 3) ≤ u ^ 2 % 2 ^ (e - 2))).image (fun u => 2 * u) := by
    ext q
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · intro ⟨hq, hev, hhi⟩
      obtain ⟨u, rfl⟩ := even_iff_exists_two_mul.mp hev
      refine ⟨u, ⟨?_, ?_⟩, rfl⟩
      · have hpow : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := (two_pow_sub_two e (by omega)).symm
        omega
      · exact (even_highBit_iff e u he).1 hhi
    · rintro ⟨u, ⟨hu, hhi⟩, rfl⟩
      have hpow : 2 ^ (e - 1) = 2 * 2 ^ (e - 2) := (two_pow_sub_two e (by omega)).symm
      exact ⟨by omega, even_two_mul u, (even_highBit_iff e u he).2 hhi⟩
  rw [this, card_image_of_injective _ inj_two_mul]
  -- Split `u < 2^{e-2}` into two copies of `u < 2^{e-3}`.
  have heq : e - 2 - 1 = e - 3 := by omega
  have hsplit :
      range (2 ^ (e - 2)) =
        range (2 ^ (e - 3)) ∪
          (range (2 ^ (e - 3))).image (fun v => v + 2 ^ (e - 3)) := by
    simpa [heq] using range_two_pow_split (e - 2) (by omega)
  have hdisj :
      Disjoint (range (2 ^ (e - 3)))
        ((range (2 ^ (e - 3))).image (fun v => v + 2 ^ (e - 3))) := by
    simpa [heq] using disjoint_range_two_pow_halves (e - 2)
  have hpred :
      ((range (2 ^ (e - 2))).filter
        (fun u => 2 ^ (e - 3) ≤ u ^ 2 % 2 ^ (e - 2))).card =
      2 * highBitSq (e - 2) := by
    have :
        (range (2 ^ (e - 2))).filter
          (fun u => 2 ^ (e - 3) ≤ u ^ 2 % 2 ^ (e - 2)) =
        (range (2 ^ (e - 3))).filter
          (fun v => 2 ^ (e - 3) ≤ v ^ 2 % 2 ^ (e - 2)) ∪
        ((range (2 ^ (e - 3))).filter
          (fun v => 2 ^ (e - 3) ≤ v ^ 2 % 2 ^ (e - 2))).image
            (fun v => v + 2 ^ (e - 3)) := by
      ext u
      simp only [mem_filter, mem_union, mem_image, mem_range]
      constructor
      · intro ⟨hu, hhi⟩
        by_cases h : u < 2 ^ (e - 3)
        · exact Or.inl ⟨h, hhi⟩
        · refine Or.inr ⟨u - 2 ^ (e - 3), ⟨?_, ?_⟩, Nat.sub_add_cancel (le_of_not_gt h)⟩
          · have hpow : 2 ^ (e - 2) = 2 * 2 ^ (e - 3) := by
              have : e - 2 = e - 3 + 1 := by omega
              rw [this, pow_succ, mul_comm]
            omega
          · have hmod := sq_add_quarter_mod e (u - 2 ^ (e - 3)) he
            rw [Nat.sub_add_cancel (le_of_not_gt h)] at hmod
            rwa [← hmod]
      · rintro (⟨hu, hhi⟩ | ⟨v, ⟨hv, hhi⟩, rfl⟩)
        · have : 2 ^ (e - 3) ≤ 2 ^ (e - 2) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          exact ⟨by omega, hhi⟩
        · have hpow : 2 ^ (e - 2) = 2 * 2 ^ (e - 3) := by
            have : e - 2 = e - 3 + 1 := by omega
            rw [this, pow_succ, mul_comm]
          refine ⟨by omega, ?_⟩
          rwa [sq_add_quarter_mod e v he]
    have hdisj2 :
        Disjoint
          ((range (2 ^ (e - 3))).filter
            (fun v => 2 ^ (e - 3) ≤ v ^ 2 % 2 ^ (e - 2)))
          (((range (2 ^ (e - 3))).filter
            (fun v => 2 ^ (e - 3) ≤ v ^ 2 % 2 ^ (e - 2))).image
              (fun v => v + 2 ^ (e - 3))) := by
      refine disjoint_left.mpr ?_
      intro x hx hx'
      rcases mem_image.mp hx' with ⟨v, hv, rfl⟩
      simp only [mem_filter, mem_range] at hx hv
      omega
    rw [this, card_union_of_disjoint hdisj2,
      card_image_of_injective _ (inj_add _)]
    unfold highBitSq
    have : e - 2 - 1 = e - 3 := by omega
    simp only [this]
    ring
  exact hpred

lemma highBitSq_rec (e : ℕ) (he : 4 ≤ e) :
    highBitSq e = 2 ^ (e - 3) + 2 * highBitSq (e - 2) := by
  conv_lhs => unfold highBitSq
  have hsplit :
      (range (2 ^ (e - 1))).filter (fun q => 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) =
      (range (2 ^ (e - 1))).filter
        (fun q => Odd q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) ∪
      (range (2 ^ (e - 1))).filter
        (fun q => Even q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e) := by
    ext q
    simp only [mem_filter, mem_union, mem_range]
    constructor
    · intro ⟨hq, hhi⟩
      cases Nat.even_or_odd q with
      | inl hev => exact Or.inr ⟨hq, hev, hhi⟩
      | inr hod => exact Or.inl ⟨hq, hod, hhi⟩
    · rintro (⟨hq, _, hhi⟩ | ⟨hq, _, hhi⟩) <;> exact ⟨hq, hhi⟩
  have hdisj :
      Disjoint
        ((range (2 ^ (e - 1))).filter
          (fun q => Odd q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e))
        ((range (2 ^ (e - 1))).filter
          (fun q => Even q ∧ 2 ^ (e - 1) ≤ q ^ 2 % 2 ^ e)) := by
    refine disjoint_filter.mpr ?_
    intro q _ h
    exact fun ⟨hev, _⟩ => Nat.not_odd_iff_even.mpr hev h.1
  rw [hsplit, card_union_of_disjoint hdisj, odd_highBit_card e he, even_highBit_card e he]

/-- Bound `highBitSq e ≤ 2^{e-2}` for `e ≥ 2`. -/
lemma highBitSq_le (e : ℕ) (he : 2 ≤ e) : highBitSq e ≤ 2 ^ (e - 2) := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    match e with
    | 0 => omega
    | 1 => omega
    | 2 => simp [highBitSq_two]
    | 3 => simp [highBitSq_three]
    | e + 4 =>
      rw [highBitSq_rec (e + 4) (by omega)]
      have ih' : highBitSq (e + 2) ≤ 2 ^ e :=
        ih (e + 2) (by omega) (by omega)
      have hsub1 : e + 4 - 3 = e + 1 := by omega
      have hsub2 : e + 4 - 2 = e + 2 := by omega
      rw [hsub1, hsub2]
      have : 2 * highBitSq (e + 2) ≤ 2 * 2 ^ e := Nat.mul_le_mul_left _ ih'
      have hpow : 2 * 2 ^ e = 2 ^ (e + 1) := by rw [pow_succ, mul_comm]
      have hsum : 2 ^ (e + 1) + 2 ^ (e + 1) = 2 ^ (e + 2) := by
        rw [← two_mul, mul_comm, ← pow_succ]
      omega

/-- The bound for powers of two. -/
lemma A048153_two_pow_le (e : ℕ) :
    A048153 (2 ^ e) ≤ 2 ^ e * (2 ^ e - 1) / 2 := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    match e with
    | 0 => decide
    | 1 => decide
    | e + 2 =>
      have he : 2 ≤ e + 2 := by omega
      rw [A048153_two_pow_highBit (e + 2) he]
      have ih' : A048153 (2 ^ (e + 1)) ≤ 2 ^ (e + 1) * (2 ^ (e + 1) - 1) / 2 :=
        ih (e + 1) (by omega)
      have hN : highBitSq (e + 2) ≤ 2 ^ e := by
        simpa using highBitSq_le (e + 2) he
      have heven : Even (2 ^ (e + 1) * (2 ^ (e + 1) - 1)) := by
        refine Even.mul_right (even_two_pow_of_pos (by omega)) _
      have hmul :
          2 * (2 ^ (e + 1) * (2 ^ (e + 1) - 1) / 2) =
            2 ^ (e + 1) * (2 ^ (e + 1) - 1) :=
        Nat.two_mul_div_two_of_even heven
      have h1 : 2 * A048153 (2 ^ (e + 1)) ≤ 2 ^ (e + 1) * (2 ^ (e + 1) - 1) := by
        have := Nat.mul_le_mul_left 2 ih'
        rwa [hmul] at this
      have h2 : 2 ^ (e + 2) * highBitSq (e + 2) ≤ 2 ^ (e + 2) * 2 ^ e :=
        Nat.mul_le_mul_left _ hN
      have h3 : 2 ^ (e + 2) * 2 ^ e = 2 ^ (2 * e + 2) := by
        rw [← pow_add]
        congr 1
        omega
      have htarget : 2 ^ (e + 2) * (2 ^ (e + 2) - 1) / 2 =
          2 ^ (e + 1) * (2 ^ (e + 2) - 1) := by
        have : 2 ^ (e + 2) = 2 * 2 ^ (e + 1) := by rw [pow_succ, mul_comm]
        rw [this, mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
      have : 2 * A048153 (2 ^ (e + 1)) + 2 ^ (e + 2) * highBitSq (e + 2) ≤
          2 ^ (e + 1) * (2 ^ (e + 2) - 1) := by
        calc
          2 * A048153 (2 ^ (e + 1)) + 2 ^ (e + 2) * highBitSq (e + 2)
              ≤ 2 ^ (e + 1) * (2 ^ (e + 1) - 1) + 2 ^ (e + 2) * 2 ^ e :=
            add_le_add h1 h2
          _ = 2 ^ (e + 1) * (2 ^ (e + 1) - 1) + 2 ^ (e + 1) * 2 ^ (e + 1) := by
              have : 2 ^ (e + 2) * 2 ^ e = 2 ^ (e + 1) * 2 ^ (e + 1) := by
                rw [← pow_add, ← pow_add]
                congr 1
                omega
              rw [this]
          _ = 2 ^ (e + 1) * (2 ^ (e + 1) - 1 + 2 ^ (e + 1)) := by
              rw [← mul_add]
          _ = 2 ^ (e + 1) * (2 ^ (e + 2) - 1) := by
              have : 2 ^ (e + 1) - 1 + 2 ^ (e + 1) = 2 ^ (e + 2) - 1 := by
                have hpos : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
                have : 2 ^ (e + 2) = 2 ^ (e + 1) + 2 ^ (e + 1) := by
                  rw [pow_succ, mul_two]
                omega
              rw [this]
      rwa [htarget]

/-! ### Doubling an odd modulus. -/

lemma odd_sq_mod_two_mul {m : ℕ} (hm : Odd m) : m ^ 2 % (2 * m) = m := by
  obtain ⟨t, ht⟩ := hm
  -- m = 2t+1, m(m-1) = (2t+1)(2t) = 2m t, so m² - m = 2 m t.
  have hdiff : m ^ 2 = m + 2 * m * t := by
    have : m * m = m * (2 * t + 1) := by rw [← ht]
    calc
      m ^ 2 = m * m := pow_two m
      _ = m * (2 * t + 1) := by rw [← ht]
      _ = m * (2 * t) + m := by rw [mul_add, mul_one]
      _ = 2 * m * t + m := by ring
      _ = m + 2 * m * t := add_comm _ _
  rw [hdiff, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  omega

lemma sq_add_odd_mod (m q : ℕ) (hm : Odd m) :
    (q + m) ^ 2 % (2 * m) = (q ^ 2 + m) % (2 * m) := by
  have hbin : (q + m) ^ 2 = q ^ 2 + 2 * q * m + m ^ 2 := add_sq _ _
  have hmid : 2 * q * m = q * (2 * m) := by
    rw [mul_comm 2 q, mul_assoc]
  have hcongr : (q + m) ^ 2 % (2 * m) = (q ^ 2 + m ^ 2) % (2 * m) := by
    rw [hbin, hmid, add_assoc, add_left_comm (q ^ 2), Nat.mul_add_mod_self_right]
  have hm2 : (q ^ 2 + m ^ 2) % (2 * m) = (q ^ 2 + m) % (2 * m) := by
    have hdiv := Nat.div_add_mod (m ^ 2) (2 * m)
    have hmod := odd_sq_mod_two_mul hm
    rw [hmod] at hdiv
    nth_rw 1 [← hdiv]
    rw [add_left_comm, Nat.mul_add_mod_self_left]
  rw [hcongr, hm2]

lemma pair_sq_mod_two_mul (m q : ℕ) (hm : Odd m) (hmpos : 0 < m) :
    q ^ 2 % (2 * m) + (q + m) ^ 2 % (2 * m) = 2 * (q ^ 2 % m) + m := by
  rw [sq_add_odd_mod m q hm]
  set r := q ^ 2 % (2 * m)
  have hrlt : r < 2 * m := Nat.mod_lt _ (by omega)
  have hrm : q ^ 2 % m = r % m := by
    have : m ∣ 2 * m := ⟨2, by ring⟩
    exact (Nat.mod_mod_of_dvd (q ^ 2) this).symm
  have hre : (q ^ 2 + m) % (2 * m) = (r + m) % (2 * m) := by
    have hdiv := Nat.div_add_mod (q ^ 2) (2 * m)
    calc
      (q ^ 2 + m) % (2 * m)
          = (2 * m * (q ^ 2 / (2 * m)) + q ^ 2 % (2 * m) + m) % (2 * m) := by
            rw [hdiv]
      _ = (2 * m * (q ^ 2 / (2 * m)) + (r + m)) % (2 * m) := by rw [add_assoc]
      _ = (r + m) % (2 * m) := Nat.mul_add_mod_self_left _ _ _
  rw [hre]
  by_cases h : r < m
  · have : (r + m) % (2 * m) = r + m := Nat.mod_eq_of_lt (by omega)
    rw [this, hrm, Nat.mod_eq_of_lt h]
    omega
  · have hrge : m ≤ r := Nat.le_of_not_gt h
    have hsum : r + m = 2 * m + (r - m) := by omega
    have hlt : r - m < 2 * m := by omega
    rw [hsum, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
    have : r % m = r - m := by
      have hrw : r = m + (r - m) := (Nat.add_sub_of_le hrge).symm
      have hlt' : r - m < m := by omega
      conv_lhs => rw [hrw]
      rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt']
    rw [hrm, this]
    omega

lemma A048153_two_mul_odd {m : ℕ} (hm : Odd m) (hmpos : 0 < m) :
    A048153 (2 * m) = 2 * A048153 m + m ^ 2 := by
  unfold A048153
  have hsplit :
      range (2 * m) = range m ∪ (range m).image (fun q => q + m) := by
    ext k
    simp only [mem_union, mem_range, mem_image]
    constructor
    · intro hk
      by_cases h : k < m
      · exact Or.inl h
      · refine Or.inr ⟨k - m, by omega, Nat.sub_add_cancel (le_of_not_gt h)⟩
    · rintro (hk | ⟨q, hq, rfl⟩) <;> omega
  have hdisj : Disjoint (range m) ((range m).image (fun q => q + m)) := by
    refine disjoint_left.mpr ?_
    intro k hk hk'
    rcases mem_image.mp hk' with ⟨q, hq, rfl⟩
    simp only [mem_range] at hk hq
    omega
  rw [hsplit, sum_union hdisj, sum_image (fun a _ b _ h => by omega)]
  have hsum :
      ∑ q ∈ range m, (q ^ 2 % (2 * m) + (q + m) ^ 2 % (2 * m)) =
        ∑ q ∈ range m, (2 * (q ^ 2 % m) + m) :=
    sum_congr rfl fun q _ => pair_sq_mod_two_mul m q hm hmpos
  rw [← sum_add_distrib, hsum, sum_add_distrib, ← mul_sum, sum_const, card_range]
  simp [pow_two, smul_eq_mul, mul_comm m]

lemma even_sub_one_of_odd {m : ℕ} (hm : Odd m) (hmpos : 0 < m) : Even (m - 1) := by
  have : m = m - 1 + 1 := (Nat.sub_add_cancel hmpos).symm
  rw [this] at hm
  exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hm)

lemma A048153_two_mul_odd_le {m : ℕ} (hm : Odd m) (hmpos : 0 < m)
    (hle : A048153 m ≤ m * (m - 1) / 2) :
    A048153 (2 * m) ≤ (2 * m) * (2 * m - 1) / 2 := by
  rw [A048153_two_mul_odd hm hmpos]
  have hmeven : Even (m * (m - 1)) :=
    Even.mul_left (even_sub_one_of_odd hm hmpos) m
  have hle' : 2 * A048153 m ≤ m * (m - 1) := by
    have := Nat.mul_le_mul_left 2 hle
    rwa [Nat.two_mul_div_two_of_even hmeven] at this
  have hsum : 2 * A048153 m + m ^ 2 ≤ m * (m - 1) + m ^ 2 :=
    Nat.add_le_add_right hle' _
  have hsimp : m * (m - 1) + m ^ 2 = m * (2 * m - 1) := by
    have : m * (m - 1) + m * m = m * (m - 1 + m) := (mul_add m _ _).symm
    rw [pow_two, this]
    have hm1 : 1 ≤ m := hmpos
    have : m - 1 + m = 2 * m - 1 := by omega
    rw [this]
  have htarget : (2 * m) * (2 * m - 1) / 2 = m * (2 * m - 1) := by
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
  rw [htarget]
  rwa [hsimp] at hsum

/-- Number of `k < n/2` whose square has high bit `1` modulo `n` (for even `n`). -/
def highBitCount (n : ℕ) : ℕ :=
  ((range (n / 2)).filter (fun k => n / 2 ≤ k ^ 2 % n)).card

lemma A048153_of_four_dvd {n : ℕ} (hn : 4 ∣ n) (hnpos : 0 < n) :
    A048153 n = 2 * A048153 (n / 2) + n * highBitCount n := by
  obtain ⟨m, rfl⟩ := hn
  -- n = 4m, n/2 = 2m
  have h4 : 4 * m = 2 * (2 * m) := by ring
  have hpos : 0 < 4 * m := by omega
  -- Reuse the power-of-two style splitting: (k + 2m)² ≡ k² (mod 4m).
  have hsq : ∀ k, (k + 2 * m) ^ 2 % (4 * m) = k ^ 2 % (4 * m) := by
    intro k
    have hbin : (k + 2 * m) ^ 2 = k ^ 2 + 2 * k * (2 * m) + (2 * m) ^ 2 := add_sq _ _
    have hmid : 2 * k * (2 * m) = k * (4 * m) := by ring
    have hlast : (2 * m) ^ 2 = m * (4 * m) := by
      rw [mul_pow, pow_two 2]; ring
    rw [hbin, hmid, hlast, add_assoc, add_left_comm (k ^ 2),
      Nat.mul_add_mod_self_right]
    rw [add_comm (k ^ 2), Nat.mul_add_mod_self_right]
  have hsplit :
      range (4 * m) = range (2 * m) ∪ (range (2 * m)).image (fun k => k + 2 * m) := by
    ext k
    simp only [mem_union, mem_range, mem_image]
    constructor
    · intro hk
      by_cases h : k < 2 * m
      · exact Or.inl h
      · refine Or.inr ⟨k - 2 * m, by omega, by omega⟩
    · rintro (hk | ⟨q, hq, rfl⟩) <;> omega
  have hdisj : Disjoint (range (2 * m)) ((range (2 * m)).image (fun k => k + 2 * m)) := by
    refine disjoint_left.mpr ?_
    intro k hk hk'
    rcases mem_image.mp hk' with ⟨q, hq, rfl⟩
    simp only [mem_range] at hk hq
    omega
  unfold A048153 highBitCount
  rw [hsplit, sum_union hdisj, sum_image (fun a _ b _ h => by omega)]
  have hsum : ∑ k ∈ range (2 * m), (k + 2 * m) ^ 2 % (4 * m) =
      ∑ k ∈ range (2 * m), k ^ 2 % (4 * m) :=
    sum_congr rfl fun k _ => hsq k
  rw [hsum, ← two_mul]
  -- Split each residue into low half + high bit.
  have hhalf : (4 * m) / 2 = 2 * m := by omega
  have hdiv2 : (4 * m) / 2 = 2 * m := hhalf
  -- k² % (4m) = k² % (2m) + (2m) * [high bit]
  have hsplit_mod : ∀ k, k ^ 2 % (4 * m) =
      k ^ 2 % (2 * m) + (2 * m) * (if 2 * m ≤ k ^ 2 % (4 * m) then 1 else 0) := by
    intro k
    set r := k ^ 2 % (4 * m)
    have hrlt : r < 4 * m := Nat.mod_lt _ (by omega)
    have hrm : k ^ 2 % (2 * m) = r % (2 * m) := by
      have : 2 * m ∣ 4 * m := ⟨2, by ring⟩
      exact (Nat.mod_mod_of_dvd (k ^ 2) this).symm
    by_cases h : 2 * m ≤ r
    · have : r % (2 * m) = r - 2 * m := by
        have hrw : r = 2 * m + (r - 2 * m) := (Nat.add_sub_of_le h).symm
        have hlt : r - 2 * m < 2 * m := by omega
        conv_lhs => rw [hrw]
        rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
      simp [h, hrm, this, Nat.sub_add_cancel h]
    · have hlt : r < 2 * m := Nat.lt_of_not_ge h
      simp [h, hrm, Nat.mod_eq_of_lt hlt]
  rw [sum_congr rfl (fun k _ => hsplit_mod k), sum_add_distrib, ← mul_sum]
  have hcard :
      ∑ k ∈ range (2 * m), (if 2 * m ≤ k ^ 2 % (4 * m) then 1 else 0 : ℕ) =
        ((range (2 * m)).filter (fun k => 2 * m ≤ k ^ 2 % (4 * m))).card := by
    simp [sum_boole, Nat.cast_id]
  rw [hcard]
  -- 2 * (a(2m) + (2m) * M) = 2 a(2m) + 4m * M
  have : 2 * (∑ k ∈ range (2 * m), k ^ 2 % (2 * m) +
      2 * m * ((range (2 * m)).filter (fun k => 2 * m ≤ k ^ 2 % (4 * m))).card) =
      2 * ∑ k ∈ range (2 * m), k ^ 2 % (2 * m) +
        4 * m * ((range (2 * m)).filter (fun k => 2 * m ≤ k ^ 2 % (4 * m))).card := by
    ring
  -- After the earlier `rw [hsum, ← two_mul]` the goal should match this.
  convert this using 2
  · simp [hhalf]
  · simp [hhalf]

/-! ### Recurrence for `highBitCount` when `16 ∣ n`. -/

lemma sixteen_mul_div_four (t : ℕ) : (16 * t) / 4 = 4 * t := by omega
lemma sixteen_mul_div_two (t : ℕ) : (16 * t) / 2 = 8 * t := by omega
lemma sixteen_mul_div_eight (t : ℕ) : (16 * t) / 8 = 2 * t := by omega

lemma quarter_sq_eq_mul {t : ℕ} : ((16 * t) / 4) ^ 2 = 16 * t * t := by
  rw [sixteen_mul_div_four, mul_pow, pow_two 4]
  ring

lemma sixteen_dvd_quarter_sq {n : ℕ} (h16 : 16 ∣ n) : n ∣ (n / 4) ^ 2 := by
  obtain ⟨t, rfl⟩ := h16
  refine ⟨t, ?_⟩
  rw [quarter_sq_eq_mul]

lemma two_mul_quarter {n : ℕ} (h16 : 16 ∣ n) : 2 * (n / 4) = n / 2 := by
  obtain ⟨t, rfl⟩ := h16
  rw [sixteen_mul_div_four, sixteen_mul_div_two]
  ring

lemma odd_mul_half_mod {n k : ℕ} (h16 : 16 ∣ n) (hodd : Odd k) :
    (n / 2 * k) % n = n / 2 := by
  obtain ⟨t, rfl⟩ := h16
  rw [sixteen_mul_div_two]
  obtain ⟨u, rfl⟩ := hodd
  -- 8t * (2u+1) = 16t * u + 8t ≡ 8t (mod 16t)
  have hdecomp : 8 * t * (2 * u + 1) = 16 * t * u + 8 * t := by ring
  rw [hdecomp]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)

lemma sq_add_quarter_flip {n k : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) (hodd : Odd k) :
    (k + n / 4) ^ 2 % n = (k ^ 2 + n / 2) % n := by
  have hbin : (k + n / 4) ^ 2 = k ^ 2 + 2 * k * (n / 4) + (n / 4) ^ 2 := add_sq _ _
  have hmid : 2 * k * (n / 4) = k * (n / 2) := by
    rw [mul_comm 2 k, mul_assoc, two_mul_quarter h16]
  rw [hbin, hmid, mul_comm k]
  have hlast : (n / 4) ^ 2 = n * (n / 16) := by
    obtain ⟨t, hk⟩ := h16
    subst n
    have : (16 * t) / 16 = t := by omega
    rw [this, quarter_sq_eq_mul]
  rw [hlast]
  have hrearr : k ^ 2 + n / 2 * k + n * (n / 16) = n * (n / 16) + (k ^ 2 + n / 2 * k) := by
    ac_rfl
  rw [hrearr, Nat.mul_add_mod_self_left]
  have hmid' : n / 2 * k % n = n / 2 := odd_mul_half_mod h16 hodd
  have : (k ^ 2 + n / 2 * k) % n = (k ^ 2 + n / 2) % n := by
    rw [Nat.add_mod, hmid', Nat.add_mod (k ^ 2) (n / 2)]
    have : n / 2 % n = n / 2 :=
      Nat.mod_eq_of_lt (Nat.div_lt_self hn (by decide : 1 < 2))
    rw [this]
  exact this

lemma add_half_mod_flip {n r : ℕ} (hn : 0 < n) (heven : Even n) :
    (r + n / 2) % n = if n / 2 ≤ r % n then r % n - n / 2 else r % n + n / 2 := by
  have hhalf : n / 2 + n / 2 = n := by
    rw [← two_mul, Nat.two_mul_div_two_of_even heven]
  have : (r + n / 2) % n = (r % n + n / 2) % n := by
    have h2 : n / 2 % n = n / 2 :=
      Nat.mod_eq_of_lt (Nat.div_lt_self hn (by decide : 1 < 2))
    rw [Nat.add_mod, h2]
  rw [this]
  by_cases h : n / 2 ≤ r % n
  · have hrlt : r % n < n := Nat.mod_lt r hn
    have heq : r % n + n / 2 = n + (r % n - n / 2) := by omega
    have hlt : r % n - n / 2 < n := by omega
    rw [if_pos h, heq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
  · have hrlt : r % n < n := Nat.mod_lt r hn
    have : r % n + n / 2 < n := by omega
    rw [if_neg h, Nat.mod_eq_of_lt this]

lemma highBit_add_quarter_odd {n k : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) (hodd : Odd k) :
    (n / 2 ≤ (k + n / 4) ^ 2 % n) ↔ ¬ (n / 2 ≤ k ^ 2 % n) := by
  have heven : Even n := even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 16) h16)
  rw [sq_add_quarter_flip h16 hn hodd]
  have hre : (k ^ 2 + n / 2) % n = (k ^ 2 % n + n / 2) % n := by
    have h2 : n / 2 % n = n / 2 :=
      Nat.mod_eq_of_lt (Nat.div_lt_self hn (by decide : 1 < 2))
    rw [Nat.add_mod, h2]
  rw [hre, add_half_mod_flip hn heven]
  have hmod : k ^ 2 % n % n = k ^ 2 % n := Nat.mod_mod _ _
  rw [hmod]
  by_cases h : n / 2 ≤ k ^ 2 % n
  · rw [if_pos h]
    have hlt : k ^ 2 % n - n / 2 < n / 2 := by
      have : k ^ 2 % n < n := Nat.mod_lt _ hn
      omega
    simp [h]
    omega
  · rw [if_neg h]
    simp [h]

lemma four_mul_mod_of_sixteen {n u : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) :
    (2 * u) ^ 2 % n = 4 * (u ^ 2 % (n / 4)) := by
  obtain ⟨t, rfl⟩ := h16
  have ht : 0 < t := by omega
  have hsq : (2 * u) ^ 2 = 4 * u ^ 2 := by
    rw [mul_pow]; norm_num
  rw [hsq, sixteen_mul_div_four]
  set q := u ^ 2 / (4 * t)
  set r := u ^ 2 % (4 * t)
  have hdiv : u ^ 2 = 4 * t * q + r := (Nat.div_add_mod _ _).symm
  have hrlt : r < 4 * t := Nat.mod_lt _ (by omega)
  rw [hdiv, mul_add, ← mul_assoc]
  have : 4 * (4 * t) = 16 * t := by ring
  rw [this, Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

lemma even_highBit_iff_of_sixteen {n u : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) :
    n / 2 ≤ (2 * u) ^ 2 % n ↔ n / 8 ≤ u ^ 2 % (n / 4) := by
  rw [four_mul_mod_of_sixteen h16 hn]
  obtain ⟨t, rfl⟩ := h16
  rw [sixteen_mul_div_two, sixteen_mul_div_four, sixteen_mul_div_eight]
  omega


/-! ### An involution that flips a Boolean predicate splits a finset in half. -/

lemma card_filter_eq_half_of_involution {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → α) (P : α → Prop) [DecidablePred P]
    (hf : ∀ x ∈ s, f x ∈ s)
    (hinvol : ∀ x ∈ s, f (f x) = x)
    (hflip : ∀ x ∈ s, P (f x) ↔ ¬ P x)
    (hfixed : ∀ x ∈ s, f x ≠ x) :
    (s.filter P).card = s.card / 2 := by
  let t := s.filter P
  let u := s.filter (fun x => ¬ P x)
  have hdisj : Disjoint t u := by
    refine disjoint_left.mpr ?_
    intro x hxT hxU
    exact (mem_filter.mp hxU).2 (mem_filter.mp hxT).2
  have hunion : t ∪ u = s := by
    ext x
    by_cases hx : P x <;> simp [t, u, hx]
  have hsum : t.card + u.card = s.card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  have hf_to : ∀ x ∈ t, f x ∈ u := by
    intro x hx
    have hxs : x ∈ s := mem_of_mem_filter x hx
    refine mem_filter.mpr ⟨hf x hxs, ?_⟩
    intro hPf
    exact (hflip x hxs).mp hPf (mem_filter.mp hx).2
  have hf_from : ∀ x ∈ u, f x ∈ t := by
    intro x hx
    have hxs : x ∈ s := mem_of_mem_filter x hx
    refine mem_filter.mpr ⟨hf x hxs, ?_⟩
    exact (hflip x hxs).mpr (mem_filter.mp hx).2
  have hinj : Set.InjOn f t := by
    intro x hx y hy hxy
    have hxs : x ∈ s := mem_of_mem_filter x hx
    have hys : y ∈ s := mem_of_mem_filter y hy
    calc
      x = f (f x) := (hinvol x hxs).symm
      _ = f (f y) := by rw [hxy]
      _ = y := hinvol y hys
  have himg_eq : t.image f = u := by
    ext y
    constructor
    · intro hy
      rcases mem_image.mp hy with ⟨x, hx, rfl⟩
      exact hf_to x hx
    · intro hy
      refine mem_image.mpr ⟨f y, hf_from y hy, ?_⟩
      exact hinvol y (mem_of_mem_filter y hy)
  have htu : t.card = u.card := by
    rw [← himg_eq, card_image_of_injOn hinj]
  have h2 : s.card = 2 * t.card := by
    rw [← hsum, htu, two_mul]
  rw [h2, Nat.mul_div_right _ (by decide : 0 < 2)]

lemma even_div_four_of_sixteen {n : ℕ} (h16 : 16 ∣ n) : Even (n / 4) := by
  obtain ⟨t, rfl⟩ := h16
  rw [sixteen_mul_div_four]
  refine ⟨2 * t, ?_⟩
  ring

lemma odd_sub_even {k m : ℕ} (hodd : Odd k) (heven : Even m) (hle : m ≤ k) :
    Odd (k - m) := by
  obtain ⟨a, ha⟩ := hodd
  obtain ⟨b, hb⟩ := heven
  refine ⟨a - b, ?_⟩
  have hb2 : m = 2 * b := by rw [hb, two_mul]
  have : b ≤ a := by
    have : 2 * b ≤ 2 * a + 1 := by
      rwa [← hb2, ← ha]
    omega
  rw [ha, hb2]
  omega

lemma card_odd_below_even {m : ℕ} :
    ((range (2 * m)).filter Odd).card = m := by
  have himg :
      (range (2 * m)).filter Odd = (range m).image (fun i => 2 * i + 1) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · intro ⟨hk, hod⟩
      obtain ⟨i, rfl⟩ := hod
      exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨by omega, odd_two_mul_add_one i⟩
  rw [himg, card_image_of_injective _ inj_two_mul_add_one, card_range]

lemma card_odd_lt_half {n : ℕ} (h4 : 4 ∣ n) :
    ((range (n / 2)).filter Odd).card = n / 4 := by
  obtain ⟨m, rfl⟩ := h4
  have : (4 * m) / 2 = 2 * m := by omega
  rw [this, card_odd_below_even]
  omega

/-- Among odd residues `k < n/2`, exactly `n/8` have high bit, when `16 ∣ n`. -/
lemma odd_highBitCount_eq {n : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) :
    ((range (n / 2)).filter (fun k => Odd k ∧ n / 2 ≤ k ^ 2 % n)).card = n / 8 := by
  have h4 : 4 ∣ n := dvd_trans (by decide : 4 ∣ 16) h16
  have hev4 : Even (n / 4) := even_div_four_of_sixteen h16
  let s := (range (n / 2)).filter Odd
  let f : ℕ → ℕ := fun k => if k < n / 4 then k + n / 4 else k - n / 4
  have hf : ∀ k ∈ s, f k ∈ s := by
    intro k hk
    obtain ⟨hklt, hkod⟩ := mem_filter.mp hk
    simp only [mem_range] at hklt
    refine mem_filter.mpr ⟨?_, ?_⟩
    · simp only [mem_range, f]; split_ifs <;> omega
    · simp only [f]; split_ifs with hlt
      · exact Odd.add_even hkod hev4
      · exact odd_sub_even hkod hev4 (le_of_not_gt hlt)
  have hn4 : n / 4 + n / 4 = n / 2 := by
    have := two_mul_quarter h16
    rwa [two_mul] at this
  have hinvol : ∀ k ∈ s, f (f k) = k := by
    intro k hk
    have hklt : k < n / 2 := mem_range.mp (mem_filter.mp hk).1
    simp only [f]
    by_cases h : k < n / 4
    · have : ¬ k + n / 4 < n / 4 := by omega
      simp [h, this]
    · have hkge : n / 4 ≤ k := le_of_not_gt h
      have hlt' : k - n / 4 < n / 4 := by
        have hk2 : k < n / 4 + n / 4 := by rwa [hn4]
        omega
      simp [h, hlt', Nat.sub_add_cancel hkge]
  have hflip : ∀ k ∈ s,
      (n / 2 ≤ (f k) ^ 2 % n) ↔ ¬ (n / 2 ≤ k ^ 2 % n) := by
    intro k hk
    obtain ⟨hklt, hkod⟩ := mem_filter.mp hk
    simp only [mem_range] at hklt
    simp only [f]
    by_cases h : k < n / 4
    · rw [if_pos h]
      exact highBit_add_quarter_odd h16 hn hkod
    · have hle : n / 4 ≤ k := le_of_not_gt h
      rw [if_neg h]
      have hkod' : Odd (k - n / 4) := odd_sub_even hkod hev4 hle
      have hfl := highBit_add_quarter_odd (n := n) (k := k - n / 4) h16 hn hkod'
      have heq : k - n / 4 + n / 4 = k := Nat.sub_add_cancel hle
      rw [heq] at hfl
      exact iff_not_comm.mp hfl
  have hfixed : ∀ k ∈ s, f k ≠ k := by
    intro k hk hfkeq
    simp only [f] at hfkeq
    split_ifs at hfkeq <;> omega
  have hP :
      (range (n / 2)).filter (fun k => Odd k ∧ n / 2 ≤ k ^ 2 % n) =
        s.filter (fun k => n / 2 ≤ k ^ 2 % n) := by
    ext k
    simp only [s, mem_filter, mem_range]
    constructor <;> intro h <;> tauto
  rw [hP]
  have hhalf := card_filter_eq_half_of_involution s f
    (fun k => n / 2 ≤ k ^ 2 % n) hf hinvol hflip hfixed
  have hscard : s.card = n / 4 := card_odd_lt_half h4
  rw [hhalf, hscard]
  obtain ⟨t, rfl⟩ := h16
  omega

/-- `(u + n/8)² ≡ u² (mod n/4)` when `16 ∣ n`. -/
lemma sq_add_eighth_mod_quarter {n u : ℕ} (h16 : 16 ∣ n) :
    (u + n / 8) ^ 2 % (n / 4) = u ^ 2 % (n / 4) := by
  obtain ⟨t, rfl⟩ := h16
  rw [sixteen_mul_div_eight, sixteen_mul_div_four]
  have hbin : (u + 2 * t) ^ 2 = u ^ 2 + 2 * u * (2 * t) + (2 * t) ^ 2 := add_sq _ _
  have hmid : 2 * u * (2 * t) = u * (4 * t) := by ring
  have hlast : (2 * t) ^ 2 = t * (4 * t) := by
    rw [mul_pow, pow_two 2]; ring
  rw [hbin, hmid, hlast]
  have : u ^ 2 + u * (4 * t) + t * (4 * t) = u ^ 2 + (u + t) * (4 * t) := by ring
  rw [this, Nat.add_mul_mod_self_right]

lemma range_quarter_split {n : ℕ} (h16 : 16 ∣ n) :
    range (n / 4) =
      range (n / 8) ∪ (range (n / 8)).image (fun v => v + n / 8) := by
  obtain ⟨t, rfl⟩ := h16
  rw [sixteen_mul_div_four, sixteen_mul_div_eight]
  ext k
  simp only [mem_union, mem_range, mem_image]
  constructor
  · intro hk
    by_cases h : k < 2 * t
    · exact Or.inl h
    · refine Or.inr ⟨k - 2 * t, ?_, Nat.sub_add_cancel (le_of_not_gt h)⟩
      omega
  · rintro (hk | ⟨v, hv, rfl⟩) <;> omega

lemma disjoint_quarter_halves {n : ℕ} (h16 : 16 ∣ n) :
    Disjoint (range (n / 8))
      ((range (n / 8)).image (fun v => v + n / 8)) := by
  refine disjoint_left.mpr ?_
  intro k hk hk'
  rcases mem_image.mp hk' with ⟨v, hv, rfl⟩
  simp only [mem_range] at hk hv
  omega

/-- Even `k < n/2` with high bit correspond to twice `highBitCount (n/4)`. -/
lemma even_highBitCount_eq {n : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) :
    ((range (n / 2)).filter (fun k => Even k ∧ n / 2 ≤ k ^ 2 % n)).card =
      2 * highBitCount (n / 4) := by
  -- Identify even `k = 2u` with `u < n/4`.
  have himg :
      (range (n / 2)).filter (fun k => Even k ∧ n / 2 ≤ k ^ 2 % n) =
        ((range (n / 4)).filter (fun u => n / 8 ≤ u ^ 2 % (n / 4))).image
          (fun u => 2 * u) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · intro ⟨hk, hev, hhi⟩
      obtain ⟨u, rfl⟩ := even_iff_exists_two_mul.mp hev
      refine ⟨u, ⟨?_, ?_⟩, rfl⟩
      · have : n / 2 = 2 * (n / 4) := (two_mul_quarter h16).symm
        omega
      · exact (even_highBit_iff_of_sixteen h16 hn).1 hhi
    · rintro ⟨u, ⟨hu, hhi⟩, rfl⟩
      have : n / 2 = 2 * (n / 4) := (two_mul_quarter h16).symm
      exact ⟨by omega, even_two_mul u, (even_highBit_iff_of_sixteen h16 hn).2 hhi⟩
  rw [himg, card_image_of_injective _ inj_two_mul]
  -- Split `u < n/4` into two copies of `u < n/8`.
  have hsplit := range_quarter_split h16
  have hdisj := disjoint_quarter_halves h16
  have :
      (range (n / 4)).filter (fun u => n / 8 ≤ u ^ 2 % (n / 4)) =
        (range (n / 8)).filter (fun v => n / 8 ≤ v ^ 2 % (n / 4)) ∪
          ((range (n / 8)).filter (fun v => n / 8 ≤ v ^ 2 % (n / 4))).image
            (fun v => v + n / 8) := by
    ext u
    simp only [mem_filter, mem_union, mem_image, mem_range]
    constructor
    · intro ⟨hu, hhi⟩
      have hu' : u ∈ range (n / 4) := mem_range.mpr hu
      rw [hsplit] at hu'
      simp only [mem_union, mem_range, mem_image] at hu'
      rcases hu' with h | ⟨v, hv, rfl⟩
      · exact Or.inl ⟨h, hhi⟩
      · refine Or.inr ⟨v, ⟨hv, ?_⟩, rfl⟩
        rwa [sq_add_eighth_mod_quarter h16] at hhi
    · rintro (⟨hu, hhi⟩ | ⟨v, ⟨hv, hhi⟩, rfl⟩)
      · have : n / 8 ≤ n / 4 := by
          obtain ⟨t, rfl⟩ := h16
          rw [sixteen_mul_div_eight, sixteen_mul_div_four]
          omega
        exact ⟨by omega, hhi⟩
      · refine ⟨?_, ?_⟩
        · obtain ⟨t, rfl⟩ := h16
          rw [sixteen_mul_div_eight, sixteen_mul_div_four]
          omega
        · rwa [sq_add_eighth_mod_quarter h16]
  have hdisj2 :
      Disjoint
        ((range (n / 8)).filter (fun v => n / 8 ≤ v ^ 2 % (n / 4)))
        (((range (n / 8)).filter (fun v => n / 8 ≤ v ^ 2 % (n / 4))).image
          (fun v => v + n / 8)) := by
    refine disjoint_left.mpr ?_
    intro x hx hx'
    rcases mem_image.mp hx' with ⟨v, hv, rfl⟩
    simp only [mem_filter, mem_range] at hx hv
    omega
  rw [this, card_union_of_disjoint hdisj2, card_image_of_injective _ (inj_add _)]
  unfold highBitCount
  -- `highBitCount (n/4) = |{v < (n/4)/2 : (n/4)/2 ≤ v² % (n/4)}|`
  -- and `(n/4)/2 = n/8`.
  have hhalf : (n / 4) / 2 = n / 8 := by
    obtain ⟨t, rfl⟩ := h16
    omega
  simp only [hhalf]
  ring

lemma highBitCount_of_sixteen {n : ℕ} (h16 : 16 ∣ n) (hn : 0 < n) :
    highBitCount n = n / 8 + 2 * highBitCount (n / 4) := by
  have hsplit :
      (range (n / 2)).filter (fun k => n / 2 ≤ k ^ 2 % n) =
        (range (n / 2)).filter (fun k => Odd k ∧ n / 2 ≤ k ^ 2 % n) ∪
          (range (n / 2)).filter (fun k => Even k ∧ n / 2 ≤ k ^ 2 % n) := by
    ext k
    simp only [mem_filter, mem_union, mem_range]
    constructor
    · intro ⟨hk, hhi⟩
      cases Nat.even_or_odd k with
      | inl hev => exact Or.inr ⟨hk, hev, hhi⟩
      | inr hod => exact Or.inl ⟨hk, hod, hhi⟩
    · rintro (⟨hk, _, hhi⟩ | ⟨hk, _, hhi⟩) <;> exact ⟨hk, hhi⟩
  have hdisj :
      Disjoint
        ((range (n / 2)).filter (fun k => Odd k ∧ n / 2 ≤ k ^ 2 % n))
        ((range (n / 2)).filter (fun k => Even k ∧ n / 2 ≤ k ^ 2 % n)) := by
    refine disjoint_filter.mpr ?_
    intro k _ h
    exact fun ⟨hev, _⟩ => Nat.not_odd_iff_even.mpr hev h.1
  conv_lhs => unfold highBitCount
  rw [hsplit, card_union_of_disjoint hdisj, odd_highBitCount_eq h16 hn,
    even_highBitCount_eq h16 hn]



/-- For `n = 4m` with `m` odd, `highBitCount` splits into square and triangular counts. -/
lemma highBitCount_four_mul_odd {m : ℕ} (hm : Odd m) (hmpos : 0 < m) :
    highBitCount (4 * m) =
      ((range m).filter (fun u => (m + 1) / 2 ≤ u ^ 2 % m)).card +
      ((range m).filter (fun u => (m + 1) / 2 ≤ u * (u + 1) % m)).card := by
  unfold highBitCount
  have hhalf : (4 * m) / 2 = 2 * m := by omega
  rw [hhalf]
  -- Split even / odd `k < 2m`.
  have hsplit : range (2 * m) =
      (range m).image (fun u => 2 * u) ∪ (range m).image (fun u => 2 * u + 1) := by
    ext k
    simp only [mem_union, mem_image, mem_range]
    constructor
    · intro hk
      rcases Nat.even_or_odd k with hev | hod
      · obtain ⟨u, rfl⟩ := even_iff_exists_two_mul.mp hev
        exact Or.inl ⟨u, by omega, rfl⟩
      · obtain ⟨u, rfl⟩ := hod
        exact Or.inr ⟨u, by omega, rfl⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> omega
  have hdisj :
      Disjoint ((range m).image (fun u => 2 * u))
        ((range m).image (fun u => 2 * u + 1)) := by
    refine disjoint_left.mpr ?_
    intro k hk hk'
    rcases mem_image.mp hk with ⟨u, _, rfl⟩
    rcases mem_image.mp hk' with ⟨v, _, h⟩
    omega
  have hdisj' :
      Disjoint
        (((range m).image (fun u => 2 * u)).filter (fun k => 2 * m ≤ k ^ 2 % (4 * m)))
        (((range m).image (fun u => 2 * u + 1)).filter (fun k => 2 * m ≤ k ^ 2 % (4 * m))) :=
    hdisj.mono (filter_subset _ _) (filter_subset _ _)
  rw [hsplit, filter_union, card_union_of_disjoint hdisj']
  simp only [filter_image]
  rw [card_image_of_injective _ inj_two_mul,
    card_image_of_injective _ inj_two_mul_add_one]
  -- even branch: `(2u)² % (4m) ≥ 2m ↔ u² % m ≥ (m+1)/2`
  refine congrArg₂ (· + ·) ?_ ?_
  · congr 1
    ext u
    simp only [mem_filter, mem_range, and_congr_right_iff]
    intro hu
    have hsq : (2 * u) ^ 2 % (4 * m) = 4 * (u ^ 2 % m) := by
      have : (2 * u) ^ 2 = 4 * u ^ 2 := by ring
      rw [this]
      exact Nat.mul_mod_mul_left _ _ _
    constructor
    · intro h
      rw [hsq] at h
      have : Odd m := hm
      omega
    · intro h
      rw [hsq]
      have : Odd m := hm
      omega
  · congr 1
    ext u
    simp only [mem_filter, mem_range, and_congr_right_iff]
    intro hu
    have hsq : (2 * u + 1) ^ 2 % (4 * m) = 4 * (u * (u + 1) % m) + 1 := by
      have hbin : (2 * u + 1) ^ 2 = 4 * (u * (u + 1)) + 1 := by ring
      rw [hbin]
      have hr : u * (u + 1) % m < m := Nat.mod_lt _ hmpos
      have h4r : 4 * (u * (u + 1) % m) + 1 < 4 * m := by omega
      have : 4 * (u * (u + 1)) + 1 =
          (u * (u + 1) / m) * (4 * m) + (4 * (u * (u + 1) % m) + 1) := by
        have := Nat.div_add_mod (u * (u + 1)) m
        zify; nlinarith
      rw [this, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h4r]
    constructor
    · intro h
      rw [hsq] at h
      have : Odd m := hm
      omega
    · intro h
      rw [hsq]
      have : Odd m := hm
      omega

lemma highBitCount_le_four_mul_odd {m : ℕ} (hm : Odd m) (hmpos : 0 < m) :
    highBitCount (4 * m) ≤ m := by
  rw [highBitCount_four_mul_odd hm hmpos]
  sorry

/-- For `n = 8m` with `m` odd. -/
lemma highBitCount_eight_mul_odd {m : ℕ} (hm : Odd m) (hmpos : 0 < m) :
    highBitCount (8 * m) ≤ 2 * m := by
  sorry

lemma highBitCount_le_four_or_eight {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n)
    (h16 : ¬ 16 ∣ n) : highBitCount n ≤ n / 4 := by
  obtain ⟨t, rfl⟩ := h4
  have ht : 0 < t := by omega
  -- `4t ≡ 4, 8 or 12 (mod 16)` means `t ≡ 1, 2 or 3 (mod 4)`.
  have hmod : t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by
    have : t % 4 ≠ 0 := by
      intro h
      have : 16 ∣ 4 * t := by
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
        exact ⟨k, by omega⟩
      exact h16 this
    omega
  rcases hmod with h1 | h2 | h3
  · -- `t` odd, `t ≡ 1 (mod 4)`
    have hodd : Odd t := Nat.odd_iff.mpr (by omega)
    have := highBitCount_le_four_mul_odd hodd ht
    have : (4 * t) / 4 = t := by omega
    rwa [this]
  · -- `t = 2m` with `m` odd
    have : t = 2 * (t / 2) := by omega
    set m := t / 2
    have hm : Odd m := by
      have : t % 4 = 2 := h2
      exact Nat.odd_iff.mpr (by omega)
    have hmpos : 0 < m := by omega
    have h8 : 4 * t = 8 * m := by omega
    rw [h8]
    have := highBitCount_eight_mul_odd hm hmpos
    have : (8 * m) / 4 = 2 * m := by omega
    rwa [this]
  · -- `t` odd, `t ≡ 3 (mod 4)`
    have hodd : Odd t := Nat.odd_iff.mpr (by omega)
    have := highBitCount_le_four_mul_odd hodd ht
    have : (4 * t) / 4 = t := by omega
    rwa [this]

/-! ### Bound `highBitCount n ≤ n / 4` when `4 ∣ n`. -/

lemma highBitCount_le_sixteen {n : ℕ} (h16 : 16 ∣ n) (hn : 0 < n)
    (ih : highBitCount (n / 4) ≤ (n / 4) / 4) :
    highBitCount n ≤ n / 4 := by
  have hrec := highBitCount_of_sixteen h16 hn
  obtain ⟨t, rfl⟩ := h16
  have ih' : highBitCount (16 * t / 4) ≤ (16 * t / 4) / 4 := ih
  simp only [sixteen_mul_div_four] at ih' hrec
  -- `highBitCount (4t) ≤ t` and target is `16t / 4 = 4t`
  have : 2 * highBitCount (4 * t) ≤ 2 * t := by
    have : (4 * t) / 4 = t := by omega
    rw [this] at ih'
    exact Nat.mul_le_mul_left _ ih'
  have : 16 * t / 8 + 2 * highBitCount (4 * t) ≤ 16 * t / 4 := by
    have : 16 * t / 8 = 2 * t := by omega
    have : 16 * t / 4 = 4 * t := by omega
    omega
  omega

lemma highBitCount_le_of_four_dvd : ∀ n : ℕ, 4 ∣ n → 0 < n →
    highBitCount n ≤ n / 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h4 hn
    by_cases h16 : 16 ∣ n
    · have hn4 : 0 < n / 4 :=
        Nat.div_pos (Nat.le_of_dvd hn (dvd_trans (by decide : 4 ∣ 16) h16)) (by decide)
      have h4' : 4 ∣ n / 4 := by
        obtain ⟨t, rfl⟩ := h16
        exact ⟨t, by omega⟩
      have hlt : n / 4 < n := Nat.div_lt_self hn (by decide : 1 < 4)
      exact highBitCount_le_sixteen h16 hn (ih (n / 4) hlt h4' hn4)
    · exact highBitCount_le_four_or_eight h4 hn h16

/-! ### Character sums for odd primes. -/

/-- The weighted character sum `∑_{k=1}^{p-1} k (k/p)`. -/
def charSum (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ k ∈ Finset.Icc 1 (p - 1), (k : ℤ) * legendreSym p k

lemma legendreSym_neg_one_of_three_mod_four {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) :
    legendreSym p (-1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp]

lemma quadraticChar_eq_legendreSym {p : ℕ} [Fact p.Prime] (j : ZMod p) :
    quadraticChar (ZMod p) j = legendreSym p j.val := by
  simp [legendreSym]

lemma image_val_univ (n : ℕ) [NeZero n] :
    (univ : Finset (ZMod n)).image ZMod.val = range n := by
  ext k
  simp only [mem_image, mem_univ, true_and, mem_range]
  constructor
  · rintro ⟨a, rfl⟩; exact ZMod.val_lt a
  · intro hk; exact ⟨(k : ZMod n), ZMod.val_natCast_of_lt hk⟩

lemma val_sum_eq {n : ℕ} [NeZero n] :
    ∑ j : ZMod n, (j.val : ℤ) = ↑(n * (n - 1) / 2) := by
  have hinj : ∀ x ∈ (univ : Finset (ZMod n)), ∀ y ∈ univ,
      ZMod.val x = ZMod.val y → x = y :=
    fun x _ y _ h => ZMod.val_injective n h
  rw [← sum_image hinj, image_val_univ, ← Nat.cast_sum, sum_range_id]

lemma card_sq_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (j : ZMod p) :
    (((univ : Finset (ZMod p)).filter (fun k => k ^ 2 = j)).card : ℤ) =
      quadraticChar (ZMod p) j + 1 := by
  have hχ : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := quadraticChar_card_sqrts hχ j
  simpa [Set.toFinset_setOf, filter_congr_decidable] using h

lemma sum_val_mul_card_sq {p : ℕ} [Fact p.Prime] :
    ∑ k : ZMod p, ((k ^ 2).val : ℤ) =
      ∑ j : ZMod p, (j.val : ℤ) *
        (((univ : Finset (ZMod p)).filter (fun k => k ^ 2 = j)).card : ℤ) := by
  rw [← Finset.sum_fiberwise _ (fun k : ZMod p => k ^ 2)]
  refine sum_congr rfl fun j _ => ?_
  have : ∀ k ∈ (univ.filter (fun k : ZMod p => k ^ 2 = j)),
      ((k ^ 2).val : ℤ) = (j.val : ℤ) := by
    intro k hk
    have : k ^ 2 = j := (mem_filter.mp hk).2
    rw [this]
  rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_comm]

lemma range_eq_zero_union_Icc (p : ℕ) [Fact p.Prime] :
    range p = {0} ∪ Icc 1 (p - 1) := by
  ext k
  simp only [mem_range, mem_union, mem_singleton, mem_Icc]
  constructor
  · intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · exact Or.inl rfl
    · exact Or.inr ⟨hk', Nat.le_sub_one_of_lt hk⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact Nat.Prime.pos Fact.out
    · omega

lemma charSum_eq_sum_val_mul_char {p : ℕ} [Fact p.Prime] :
    ∑ j : ZMod p, (j.val : ℤ) * quadraticChar (ZMod p) j = charSum p := by
  have : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have h0 : ((0 : ZMod p).val : ℤ) * quadraticChar (ZMod p) 0 = 0 := by
    simp [ZMod.val_zero]
  rw [← sum_erase (s := (univ : Finset (ZMod p))) (a := (0 : ZMod p)) h0]
  unfold charSum
  refine sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    have hj0 : j ≠ 0 := (mem_erase.mp hj).1
    have hv : j.val ≠ 0 := fun h => hj0 ((ZMod.val_eq_zero j).mp h)
    have hlt : j.val < p := ZMod.val_lt j
    exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hv, Nat.le_sub_one_of_lt hlt⟩
  · intro a ha b hb h
    exact ZMod.val_injective p h
  · intro k hk
    have hkI := mem_Icc.mp hk
    have hklt : k < p := by omega
    refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt hklt⟩
    refine mem_erase.mpr ⟨?_, mem_univ _⟩
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hklt, ZMod.val_zero] at this
    omega
  · intro j hj
    have hj0 : j ≠ 0 := (mem_erase.mp hj).1
    rw [quadraticChar_eq_legendreSym]

/-- For an odd prime, `a(p) = p(p-1)/2 + charSum p`. -/
lemma A048153_eq_add_charSum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (A048153 p : ℤ) = ↑(p * (p - 1) / 2) + charSum p := by
  have : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  rw [A048153_eq_sum_val, Nat.cast_sum, sum_val_mul_card_sq]
  simp_rw [card_sq_eq hp2]
  calc
    ∑ j : ZMod p, (j.val : ℤ) * (quadraticChar (ZMod p) j + 1)
        = ∑ j : ZMod p, ((j.val : ℤ) * quadraticChar (ZMod p) j + (j.val : ℤ)) := by
          refine sum_congr rfl fun j _ => ?_
          ring
    _ = ∑ j : ZMod p, (j.val : ℤ) * quadraticChar (ZMod p) j +
          ∑ j : ZMod p, (j.val : ℤ) := sum_add_distrib
    _ = charSum p + ↑(p * (p - 1) / 2) := by
          rw [charSum_eq_sum_val_mul_char, val_sum_eq]
    _ = ↑(p * (p - 1) / 2) + charSum p := add_comm _ _

/-! ### Auxiliary facts about the quadratic character. -/

/-- The quadratic character as a complex-valued function on `ZMod p`. -/
noncomputable def quadCharC (p : ℕ) [Fact p.Prime] : ZMod p → ℂ :=
  fun j => (quadraticChar (ZMod p) j : ℂ)

lemma quadraticChar_neg_one_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  have hp2 : p ≠ 2 := by omega
  classical
  have hχ := quadraticChar_neg_one (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  simpa [ZMod.card p, ZMod.χ₄_nat_three_mod_four hp] using hχ

lemma quadCharC_odd {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    Function.Odd (quadCharC p) := by
  intro j
  have hmul : quadraticChar (ZMod p) (-j) =
      quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) j := by
    rw [← map_mul]; congr 1; ring
  simp [quadCharC, hmul, quadraticChar_neg_one_three_mod_four hp]

lemma quadCharC_zero (p : ℕ) [Fact p.Prime] : quadCharC p 0 = 0 := by
  simp [quadCharC]

lemma quadCharC_sum_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ j : ZMod p, quadCharC p j = 0 := by
  classical
  have hχ : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := quadraticChar_sum_zero (F := ZMod p) hχ
  unfold quadCharC
  rw [← Int.cast_sum, h, Int.cast_zero]

/-! ### Character-sum identities for primes `p ≡ 3 (mod 4)`. -/

lemma p_ne_two_of_three_mod_four {p : ℕ} (hp : p % 4 = 3) : p ≠ 2 := by omega

lemma two_mul_half_p {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    2 * ((p - 1) / 2) = p - 1 := by
  have : p % 2 = 1 := by omega
  have : Odd p := Nat.odd_iff.mpr this
  exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_sub_one_of_odd this (Nat.Prime.pos Fact.out)))

lemma Icc_union_Icc_eq_Icc_one_sub {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    Finset.Icc 1 ((p - 1) / 2) ∪
      (Finset.Icc 1 ((p - 1) / 2)).image (fun j => p - j) =
    Finset.Icc 1 (p - 1) := by
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
    · have hmul := two_mul_half_p hp
      omega
    · have hmul := two_mul_half_p hp
      have hppos : 1 ≤ p := Nat.Prime.one_le Fact.out
      omega
  · intro ⟨hk1, hk2⟩
    have hmul := two_mul_half_p hp
    by_cases h : k ≤ (p - 1) / 2
    · exact Or.inl ⟨hk1, h⟩
    · refine Or.inr ⟨p - k, ⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega

lemma disjoint_Icc_image_sub {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    Disjoint (Finset.Icc 1 ((p - 1) / 2))
      ((Finset.Icc 1 ((p - 1) / 2)).image (fun j => p - j)) := by
  refine Finset.disjoint_left.mpr ?_
  intro k hk hk'
  rcases Finset.mem_image.mp hk' with ⟨j, hj, rfl⟩
  have hkI := Finset.mem_Icc.mp hk
  have hjI := Finset.mem_Icc.mp hj
  have hmul := two_mul_half_p hp
  omega

lemma legendreSym_p_sub {p k : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (hk0 : 0 < k) (hkle : k ≤ p) :
    legendreSym p ((p : ℤ) - k) = - legendreSym p k := by
  have hmod : ((p : ℤ) - k) % p = (-(k : ℤ)) % p := by
    have : (p : ℤ) - k = -k + p := by ring
    rw [this, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  rw [legendreSym.mod, hmod, ← legendreSym.mod]
  have hneg : legendreSym p (-(k : ℤ)) =
      legendreSym p (-1) * legendreSym p k := by
    simpa using (legendreSym.mul p (-1) k)
  rw [hneg, legendreSym_neg_one_of_three_mod_four hp]
  ring

lemma charSum_eq_half_range {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    charSum p =
      ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
        ((k : ℤ) * legendreSym p k * 2 - (p : ℤ) * legendreSym p k) := by
  unfold charSum
  have hsplit := Icc_union_Icc_eq_Icc_one_sub hp
  have hdisj := disjoint_Icc_image_sub hp
  rw [← hsplit, Finset.sum_union hdisj]
  rw [Finset.sum_image (fun a ha b hb h => by
    have ha' : 1 ≤ a ∧ a ≤ (p - 1) / 2 := by
      simpa [Finset.mem_Icc] using ha
    have hb' : 1 ≤ b ∧ b ≤ (p - 1) / 2 := by
      simpa [Finset.mem_Icc] using hb
    have hmul := two_mul_half_p hp
    omega)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkI := Finset.mem_Icc.mp hk
  have hmul := two_mul_half_p hp
  have hkle : k ≤ p := by omega
  have hkpos : 0 < k := by omega
  have hχ := legendreSym_p_sub hp hkpos hkle
  have hcast : ((p - k : ℕ) : ℤ) = (p : ℤ) - k := Nat.cast_sub hkle
  rw [hcast, hχ]
  ring

/-! ### Quadratic Gauss sums via the Jacobi theta transformation. -/

open Complex

/-- The classical quadratic Gauss sum. -/
noncomputable def quadGaussSum (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, exp (2 * Real.pi * I * k ^ 2 / n)

lemma tsum_shifted_gaussian (ε : ℝ) (hε : 0 < ε) (α : ℝ) :
    (∑' q : ℤ, cexp (-Real.pi * ε * (q + α) ^ 2)) =
      (ε : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∑' q : ℤ, cexp (-Real.pi / ε * (q : ℂ) ^ 2 + 2 * Real.pi * I * α * q) := by
  have ha : 0 < (ε : ℂ).re := by simpa
  -- Expand the quadratic and apply Poisson summation.
  have hterm (q : ℤ) :
      cexp (-Real.pi * ε * ((q : ℂ) + α) ^ 2) =
        cexp (-Real.pi * ε * α ^ 2) *
          cexp (-Real.pi * (ε : ℂ) * (q : ℂ) ^ 2 +
            2 * Real.pi * (-(ε : ℂ) * α) * q) := by
    have : (-Real.pi * ε * ((q : ℂ) + α) ^ 2) =
        (-Real.pi * ε * α ^ 2) +
          (-Real.pi * (ε : ℂ) * (q : ℂ) ^ 2 +
            2 * Real.pi * (-(ε : ℂ) * α) * q) := by ring
    rw [this, Complex.exp_add]
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hpois :=
    Complex.tsum_exp_neg_quadratic (a := (ε : ℂ)) ha (-(ε : ℂ) * α)
  rw [hpois]
  have hpow : (1 : ℂ) / (ε : ℂ) ^ (1 / 2 : ℂ) = (ε : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [cpow_neg]
    field_simp
  rw [hpow, mul_left_comm]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun q : ℤ => ?_
  -- The extra Gaussian prefactors cancel:
  -- exp(-π ε α²) * exp(-π/ε (q - I ε α)²) = exp(-π/ε q² + 2π i α q).
  have hexp :
      -Real.pi / (ε : ℂ) * ((q : ℂ) + I * (-(ε : ℂ) * α)) ^ 2 =
        Real.pi * ε * α ^ 2 +
          (-Real.pi / ε * (q : ℂ) ^ 2 + 2 * Real.pi * I * α * q) := by
    have hsq : ((q : ℂ) + I * (-(ε : ℂ) * α)) ^ 2 =
        (q : ℂ) ^ 2 - 2 * I * ε * α * q - (ε : ℂ) ^ 2 * α ^ 2 := by
      ring_nf
      simp [I_sq]
      ring
    rw [hsq]
    have hεc : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
    field_simp [hεc]
    ring
  calc
    cexp (-Real.pi * ε * α ^ 2) *
        cexp (-Real.pi / (ε : ℂ) * ((q : ℂ) + I * (-(ε : ℂ) * α)) ^ 2)
        = cexp (-Real.pi * ε * α ^ 2 +
            -Real.pi / (ε : ℂ) * ((q : ℂ) + I * (-(ε : ℂ) * α)) ^ 2) := by
          rw [← Complex.exp_add]
    _ = cexp (-Real.pi * ε * α ^ 2 +
          (Real.pi * ε * α ^ 2 +
            (-Real.pi / ε * (q : ℂ) ^ 2 + 2 * Real.pi * I * α * q))) := by
          rw [hexp]
    _ = cexp (-Real.pi / ε * (q : ℂ) ^ 2 + 2 * Real.pi * I * α * q) := by
          congr 1; ring

lemma jacobiTheta₂_eq_shifted_poisson (α ε : ℝ) (hε : 0 < ε) :
    jacobiTheta₂ α (I / ε) =
      ∑' q : ℤ, cexp (-Real.pi / ε * (q : ℂ) ^ 2 + 2 * Real.pi * I * α * q) := by
  unfold jacobiTheta₂
  refine tsum_congr fun q => ?_
  unfold jacobiTheta₂_term
  congr 1
  have : I / (ε : ℂ) = I * (ε : ℂ)⁻¹ := div_eq_mul_inv _ _
  rw [this]
  ring_nf
  simp [I_sq]
  ring

lemma im_I_div_eq (ε : ℝ) (hε : ε ≠ 0) : (I / (ε : ℂ)).im = 1 / ε := by
  rw [div_eq_mul_inv, mul_im, I_re, I_im]
  simp [inv_re, inv_im, normSq, hε]

lemma im_I_div_pos (ε : ℝ) (hε : 0 < ε) : 0 < (I / (ε : ℂ)).im := by
  rw [im_I_div_eq ε hε.ne']
  exact one_div_pos.mpr hε

lemma jacobiTheta₂_term_zero (z τ : ℂ) : jacobiTheta₂_term 0 z τ = 1 := by
  simp [jacobiTheta₂_term, Complex.exp_zero]

lemma norm_jacobiTheta₂_term_of_real (α ε : ℝ) (n : ℤ) (hε : 0 < ε) :
    ‖jacobiTheta₂_term n α (I / ε)‖ = Real.exp (-Real.pi / ε * (n : ℝ) ^ 2) := by
  rw [norm_jacobiTheta₂_term, im_I_div_eq ε hε.ne']
  simp
  ring

lemma exp_neg_sq_le_geom (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    Real.exp (-Real.pi / ε * (k : ℝ) ^ 2) ≤ Real.exp (-Real.pi / ε) ^ k := by
  have hcoef : (-Real.pi) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hε.le
  have hpow : (k : ℝ) ^ 2 ≥ (k : ℝ) := by
    rw [sq]
    exact_mod_cast Nat.le_mul_self k
  have : Real.exp ((-Real.pi) / ε * (k : ℝ) ^ 2) ≤
      Real.exp ((-Real.pi) / ε * (k : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpow hcoef)
  refine this.trans_eq ?_
  rw [← Real.exp_nsmul]
  congr 1
  simp [nsmul_eq_mul]
  ring

lemma hasSum_geometric_exp_neg_pi (ε : ℝ) (hε : 0 < ε) :
    HasSum (fun n : ℕ => Real.exp (-Real.pi / ε) ^ (n + 1))
      (Real.exp (-Real.pi / ε) / (1 - Real.exp (-Real.pi / ε))) := by
  simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
  refine hasSum_geometric_of_lt_one (Real.exp_pos _).le ?_
  rw [Real.exp_lt_one_iff]
  have : (-Real.pi) / ε < 0 :=
    div_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hε
  exact this

lemma norm_jacobiTheta₂_sub_one_of_real (α ε : ℝ) (hε : 0 < ε) :
    ‖jacobiTheta₂ α (I / ε) - 1‖ ≤
      2 * Real.exp (-Real.pi / ε) / (1 - Real.exp (-Real.pi / ε)) := by
  have him : 0 < (I / (ε : ℂ)).im := im_I_div_pos ε hε
  have s := hasSum_geometric_exp_neg_pi ε hε
  let f : ℤ → ℂ := fun n => jacobiTheta₂_term n (α : ℂ) (I / ε)
  have hsum : HasSum f (jacobiTheta₂ (α : ℂ) (I / ε)) :=
    hasSum_jacobiTheta₂_term (α : ℂ) him
  have hnat : HasSum (fun n : ℕ => f n + f (-n))
      (jacobiTheta₂ (α : ℂ) (I / ε) + f 0) := hsum.nat_add_neg
  have h0 : f 0 = 1 := jacobiTheta₂_term_zero _ _
  have hsm := hnat.summable
  have hsplit := hsm.tsum_eq_zero_add
  -- `∑' n, (f n + f (-n)) = (f 0 + f 0) + ∑' n, (f (n+1) + f (-(n+1)))`
  have hdiff :
      jacobiTheta₂ (α : ℂ) (I / ε) - 1 =
        ∑' n : ℕ, (f (n + 1) + f (-(n + 1))) := by
    have hts := hnat.tsum_eq
    rw [h0] at hts
    have h00 : f (0 : ℕ) + f (-(0 : ℕ)) = 2 := by
      change f 0 + f (-0) = 2
      simp [h0]
      ring
    have hts' : 2 + ∑' n : ℕ, (f (n + 1 : ℕ) + f (-(n + 1 : ℕ))) =
        jacobiTheta₂ (α : ℂ) (I / ε) + 1 := by
      rw [← h00, ← hsplit, hts]
    have hts'' : ∑' n : ℕ, (f (n + 1 : ℕ) + f (-(n + 1 : ℕ))) =
        jacobiTheta₂ (α : ℂ) (I / ε) - 1 := by
      have hS := hts'
      set S := ∑' n : ℕ, (f (n + 1 : ℕ) + f (-(n + 1 : ℕ)))
      have : S = (2 + S) - 2 := by ring
      rw [this, hS]
      ring
    refine hts''.symm.trans ?_
    refine tsum_congr (fun n : ℕ => ?_)
    simp [Nat.cast_succ]
  have hle : ∀ n : ℕ, ‖f (n + 1)‖ ≤ Real.exp (-Real.pi / ε) ^ (n + 1) := by
    intro n
    rw [show f (n + 1) = jacobiTheta₂_term (n + 1 : ℤ) (α : ℂ) (I / ε) from rfl]
    rw [norm_jacobiTheta₂_term_of_real α ε (n + 1 : ℤ) hε]
    have hk : ((n + 1 : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by simp
    rw [hk]
    exact exp_neg_sq_le_geom ε hε (n + 1)
  have hle' : ∀ n : ℕ, ‖f (-(n + 1))‖ ≤ Real.exp (-Real.pi / ε) ^ (n + 1) := by
    intro n
    rw [show f (-(n + 1)) = jacobiTheta₂_term (-(n + 1 : ℤ)) (α : ℂ) (I / ε) from rfl]
    rw [norm_jacobiTheta₂_term_of_real α ε (-(n + 1 : ℤ)) hε]
    have : ((-(n + 1 : ℤ) : ℤ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) ^ 2 := by
      simp; ring
    rw [this]
    exact exp_neg_sq_le_geom ε hε (n + 1)
  have hnorm : ∀ n : ℕ, ‖f (n + 1) + f (-(n + 1))‖ ≤
      2 * Real.exp (-Real.pi / ε) ^ (n + 1) := by
    intro n
    refine (norm_add_le _ _).trans ?_
    linarith [hle n, hle' n]
  have hsmn : Summable fun n : ℕ => ‖f (n + 1) + f (-(n + 1))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm (s.summable.mul_left (2 : ℝ))
  have hgeom2 : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi / ε) ^ (n + 1))
      (2 * Real.exp (-Real.pi / ε) / (1 - Real.exp (-Real.pi / ε))) := by
    convert s.mul_left (2 : ℝ) using 1
    ring
  rw [hdiff]
  exact (norm_tsum_le_tsum_norm hsmn).trans
    ((hsmn.tsum_mono hgeom2.summable hnorm).trans_eq hgeom2.tsum_eq)

lemma tendsto_jacobiTheta₂_real_invIm (α : ℝ) :
    Filter.Tendsto (fun ε : ℝ => jacobiTheta₂ α (I / ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hgeom :
      Filter.Tendsto
        (fun ε : ℝ => 2 * Real.exp (-Real.pi / ε) / (1 - Real.exp (-Real.pi / ε)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hexp0 : Filter.Tendsto (fun ε : ℝ => Real.exp (-Real.pi / ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hat : Filter.Tendsto (fun ε : ℝ => Real.pi / ε)
          (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
        simpa [div_eq_mul_inv] using
          tendsto_inv_nhdsGT_zero.const_mul_atTop Real.pi_pos
      convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hat using 1
      ext ε; simp [div_eq_mul_inv]
    have hden : Filter.Tendsto (fun ε : ℝ => 1 - Real.exp (-Real.pi / ε))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      convert (tendsto_const_nhds (x := (1 : ℝ))).sub hexp0
      simp
    have hinv : Filter.Tendsto (fun ε : ℝ => (1 - Real.exp (-Real.pi / ε))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      convert hden.inv₀ (by norm_num)
      simp
    convert (hexp0.mul hinv).const_mul (2 : ℝ) using 1
    · ext ε; ring
    · simp
  have hzero : Filter.Tendsto (fun ε : ℝ => jacobiTheta₂ α (I / ε) - 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' ?_ hgeom
    filter_upwards [self_mem_nhdsWithin] with ε hε using
      norm_jacobiTheta₂_sub_one_of_real α ε hε
  exact (tendsto_sub_nhds_zero_iff.mp hzero)

lemma tendsto_sqrt_eps_tsum_shifted_gaussian (α : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => (ε : ℂ).sqrt * ∑' q : ℤ, cexp (-Real.pi * ε * (q + α) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hstep : ∀ ε : ℝ, ε ∈ Set.Ioi 0 →
      (ε : ℂ).sqrt * ∑' q : ℤ, cexp (-Real.pi * ε * (q + α) ^ 2) =
        jacobiTheta₂ α (I / ε) := by
    intro ε hε
    have hεpos : 0 < ε := hε
    have hεc : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hεpos.ne'
    rw [tsum_shifted_gaussian ε hεpos α, Complex.sqrt,
      jacobiTheta₂_eq_shifted_poisson α ε hεpos]
    have : (ε : ℂ) ^ (2⁻¹ : ℂ) * (ε : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
      have hsum : (2⁻¹ : ℂ) + (-(1 / 2 : ℂ)) = 0 := by ring
      rw [← Complex.cpow_add _ _ hεc, hsum, Complex.cpow_zero]
    rw [← mul_assoc, this, one_mul]
  exact tendsto_nhdsWithin_congr (fun ε hε => (hstep ε hε).symm)
    (tendsto_jacobiTheta₂_real_invIm α)


lemma charSum_eq_two_mul_weighted {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    charSum p =
      2 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ℤ) * legendreSym p k -
        (p : ℤ) * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), legendreSym p k := by
  rw [charSum_eq_half_range hp, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_mul]
  ring

lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (2 : ZMod p) ≠ 0 := by
  have hp2 : p ≠ 2 := p_ne_two_of_three_mod_four hp
  intro h
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff (2 : ℕ) p).1 h
  have := Nat.le_of_dvd (by decide : 0 < 2) this
  omega

lemma legendreSym_two_eq_one_or_neg_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    legendreSym p 2 = 1 ∨ legendreSym p 2 = -1 := by
  have ha : ((2 : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast two_ne_zero_zmod hp
  exact legendreSym.eq_one_or_neg_one (p := p) ha

lemma two_mul_val_of_le_half {p k : ℕ} [Fact p.Prime]
    (hk : k ∈ Finset.Icc 1 ((p - 1) / 2)) :
    ((2 * (k : ZMod p)).val : ℤ) = 2 * k := by
  have hkI := Finset.mem_Icc.mp hk
  have h2le : 2 * k ≤ p - 1 := by
    have : 2 * k ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 hkI.2
    exact this.trans (Nat.mul_div_le _ _)
  have h2lt : 2 * k < p := by omega
  have hcast : (2 : ZMod p) * (k : ZMod p) = ((2 * k : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
  have hval : ((2 * k : ℕ) : ZMod p).val = 2 * k :=
    ZMod.val_natCast_of_lt h2lt
  have : ((2 * (k : ZMod p)).val : ℤ) = ((2 * k : ℕ) : ZMod p).val := by
    rw [hcast]
  rw [this, hval]
  norm_cast

lemma two_mul_val_of_gt_half {p k : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (hk : k ∈ Finset.Icc 1 ((p - 1) / 2)) :
    ((2 * ((p - k : ℕ) : ZMod p)).val : ℤ) = (p : ℤ) - 2 * k := by
  have hkI := Finset.mem_Icc.mp hk
  have hmul := two_mul_half_p hp
  have hklt : k < p := by omega
  have hpklt : p - k < p := by omega
  have h2k : 2 * k ≤ p - 1 := by
    have : 2 * k ≤ 2 * ((p - 1) / 2) := Nat.mul_le_mul_left 2 hkI.2
    exact this.trans (Nat.mul_div_le _ _)
  have h2kpos : 0 < 2 * k := by omega
  have hcast : (2 : ZMod p) * ((p - k : ℕ) : ZMod p) = ((2 * (p - k) : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
  have hsub : 2 * (p - k) = 2 * p - 2 * k :=
    Nat.mul_sub_left_distrib 2 p k
  have hrepr : 2 * p - 2 * k = (p - 2 * k) + p := by
    have : 2 * k ≤ p := by omega
    have : 2 * p - 2 * k = p + (p - 2 * k) := by
      have h1 : 2 * p = p + p := by ring
      omega
    rw [this, add_comm]
  have hmod : (2 * (p - k)) % p = p - 2 * k := by
    rw [hsub, hrepr, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt]
    omega
  have hval : ((2 * (p - k) : ℕ) : ZMod p).val = p - 2 * k := by
    rw [ZMod.val_natCast, hmod]
  rw [hcast, hval]
  have : ((p - 2 * k : ℕ) : ℤ) = (p : ℤ) - 2 * k := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_two]
  exact this

lemma legendreSym_val_two_mul {p k : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    legendreSym p ((2 * (k : ZMod p)).val) = legendreSym p 2 * legendreSym p k := by
  have hcongr : (((2 * (k : ZMod p)).val : ℤ) : ZMod p) = ((2 * (k : ℤ) : ℤ) : ZMod p) := by
    simp [ZMod.natCast_zmod_val]
  have hmod : ((2 * (k : ZMod p)).val : ℤ) % (p : ℤ) = (2 * (k : ℤ)) % (p : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ p).mp hcongr
  rw [legendreSym.mod p ((2 * (k : ZMod p)).val : ℤ), hmod, ← legendreSym.mod p (2 * (k : ℤ))]
  simpa using (legendreSym.mul p 2 k)

lemma two_mul_val_mem_Icc {p k : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (hk : k ∈ Finset.Icc 1 (p - 1)) :
    (2 * (k : ZMod p)).val ∈ Finset.Icc 1 (p - 1) := by
  have hkI := Finset.mem_Icc.mp hk
  have hv := ZMod.val_lt (2 * (k : ZMod p))
  have hne : (2 * (k : ZMod p)).val ≠ 0 := by
    intro h
    have hz : 2 * (k : ZMod p) = 0 := (ZMod.val_eq_zero _).mp h
    have hk0 : (k : ZMod p) ≠ 0 := by
      intro hkz
      have := congrArg ZMod.val hkz
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at this
      omega
    exact hk0 ((mul_eq_zero.mp hz).resolve_left (two_ne_zero_zmod hp))
  exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.le_sub_one_of_lt hv⟩

lemma charSum_by_doubling {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    charSum p =
      legendreSym p 2 *
        (4 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ℤ) * legendreSym p k -
          (p : ℤ) * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), legendreSym p k) := by
  have h2 := two_ne_zero_zmod hp
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2
  have hreindex :
      charSum p =
        ∑ k : ZMod p, ((2 * k).val : ℤ) * quadraticChar (ZMod p) (2 * k) := by
    rw [← charSum_eq_sum_val_mul_char]
    simpa [e, Equiv.mulLeft₀] using
      (Equiv.sum_comp e (fun k : ZMod p =>
        ((k.val : ℤ) * quadraticChar (ZMod p) k))).symm
  have hχ : ∀ k : ZMod p,
      quadraticChar (ZMod p) (2 * k) =
        quadraticChar (ZMod p) 2 * quadraticChar (ZMod p) k := by
    intro k
    rw [← map_mul]
  have hfactor :
      charSum p =
        quadraticChar (ZMod p) 2 *
          ∑ k : ZMod p, ((2 * k).val : ℤ) * quadraticChar (ZMod p) k := by
    rw [hreindex]
    simp_rw [hχ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  -- Restrict to nonzero residues and identify with `1 … p-1`.
  have h0 : ((2 * (0 : ZMod p)).val : ℤ) * quadraticChar (ZMod p) 0 = 0 := by simp
  have hsum :
      ∑ k : ZMod p, ((2 * k).val : ℤ) * quadraticChar (ZMod p) k =
        ∑ k ∈ Finset.Icc 1 (p - 1),
          ((2 * (k : ZMod p)).val : ℤ) * legendreSym p k := by
    rw [← Finset.sum_erase (s := (univ : Finset (ZMod p))) (a := (0 : ZMod p)) h0]
    refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
    · intro k hk
      have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
      have hv := ZMod.val_lt k
      have hne : k.val ≠ 0 := fun h => hk0 ((ZMod.val_eq_zero k).mp h)
      exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hne, Nat.le_sub_one_of_lt hv⟩
    · intro a _ b _ h; exact ZMod.val_injective p h
    · intro k hk
      have hkI := Finset.mem_Icc.mp hk
      refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at this
      omega
    · intro k hk
      rw [quadraticChar_eq_legendreSym]
      simp [ZMod.natCast_zmod_val]
  have hχ2 : quadraticChar (ZMod p) 2 = legendreSym p 2 := by
    have h2lt : (2 : ℕ) < p := by
      have := Nat.Prime.two_le (Fact.out : Nat.Prime p)
      have : p ≠ 2 := p_ne_two_of_three_mod_four hp
      omega
    rw [quadraticChar_eq_legendreSym]
    have hval : (2 : ZMod p).val = 2 := by
      change ((2 : ℕ) : ZMod p).val = 2
      exact ZMod.val_natCast_of_lt h2lt
    rw [hval]
    norm_cast
  rw [hfactor, hχ2, hsum]
  -- Split into the two halves.
  have hsplit := Icc_union_Icc_eq_Icc_one_sub hp
  have hdisj := disjoint_Icc_image_sub hp
  rw [← hsplit, Finset.sum_union hdisj]
  have hfirst :
      ∑ k ∈ Finset.Icc 1 ((p - 1) / 2),
          ((2 * (k : ZMod p)).val : ℤ) * legendreSym p k =
        2 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ℤ) * legendreSym p k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [two_mul_val_of_le_half hk]; ring
  have himg :
      ∑ k ∈ (Finset.Icc 1 ((p - 1) / 2)).image (fun j => p - j),
          ((2 * (k : ZMod p)).val : ℤ) * legendreSym p k =
        2 * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ℤ) * legendreSym p k -
          (p : ℤ) * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), legendreSym p k := by
    rw [Finset.sum_image (fun a ha b hb h => by
      have ha' : 1 ≤ a ∧ a ≤ (p - 1) / 2 := by simpa [Finset.mem_Icc] using ha
      have hb' : 1 ≤ b ∧ b ≤ (p - 1) / 2 := by simpa [Finset.mem_Icc] using hb
      have := two_mul_half_p hp; omega)]
    trans ∑ j ∈ Finset.Icc 1 ((p - 1) / 2),
        ((p : ℤ) - 2 * j) * (-legendreSym p j)
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hjI := Finset.mem_Icc.mp hj
      have := two_mul_half_p hp
      have hcast : ((p - j : ℕ) : ℤ) = (p : ℤ) - j := Nat.cast_sub (by omega)
      have hχj := legendreSym_p_sub hp (by omega : 0 < j) (by omega : j ≤ p)
      rw [two_mul_val_of_gt_half hp hj]
      have : legendreSym p ((p - j : ℕ) : ℤ) = -legendreSym p j := by
        convert hχj
      rw [this]
    · have hrew :
          ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), ((p : ℤ) - 2 * j) * (-legendreSym p j) =
            ∑ j ∈ Finset.Icc 1 ((p - 1) / 2),
              (2 * (j : ℤ) * legendreSym p j - (p : ℤ) * legendreSym p j) := by
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrew, Finset.sum_sub_distrib]
      have h2S :
          ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), 2 * (j : ℤ) * legendreSym p j =
            2 * ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), (j : ℤ) * legendreSym p j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h2S, ← Finset.mul_sum]
  rw [hfirst, himg]
  ring

lemma charSum_eq_neg_mul_halfCharSum {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    charSum p * (2 - legendreSym p 2) =
      - (p : ℤ) * ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), legendreSym p k := by
  have h1 := charSum_eq_two_mul_weighted hp
  have h2 := charSum_by_doubling hp
  set S1 := ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ℤ) * legendreSym p k
  set S0 := ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), legendreSym p k
  have h1' : charSum p = 2 * S1 - (p : ℤ) * S0 := h1
  have h2' : charSum p = legendreSym p 2 * (4 * S1 - (p : ℤ) * S0) := h2
  have heq : 2 * S1 - (p : ℤ) * S0 =
      legendreSym p 2 * (4 * S1 - (p : ℤ) * S0) := by
    rw [← h1', ← h2']
  have h2pn : legendreSym p 2 = 1 ∨ legendreSym p 2 = -1 :=
    legendreSym_two_eq_one_or_neg_one hp
  rcases h2pn with hχ | hχ
  · have : 2 * S1 - (p : ℤ) * S0 = 4 * S1 - (p : ℤ) * S0 := by
      simpa [hχ] using heq
    have hS1 : S1 = 0 := by linarith
    simp [h1', hS1, hχ]
  · have : 2 * S1 - (p : ℤ) * S0 = - (4 * S1 - (p : ℤ) * S0) := by
      simpa [hχ] using heq
    have : charSum p = 2 * S1 - (p : ℤ) * S0 := h1'
    calc
      charSum p * (2 - legendreSym p 2)
          = (2 * S1 - (p : ℤ) * S0) * (2 - (-1)) := by rw [this, hχ]
      _ = (2 * S1 - (p : ℤ) * S0) * 3 := by ring
      _ = 6 * S1 - 3 * (p : ℤ) * S0 := by ring
      _ = 2 * (p : ℤ) * S0 - 3 * (p : ℤ) * S0 := by
          have : 6 * S1 = 2 * (p : ℤ) * S0 := by linarith
          linarith
      _ = - (p : ℤ) * S0 := by ring

lemma halfCharSum_pos {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    0 < ∑ k ∈ Finset.Icc 1 ((p - 1) / 2), legendreSym p k := by
  sorry

/-- `charSum p ≤ 0` for primes `p ≡ 3 (mod 4)`. -/
lemma charSum_nonpos {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    charSum p ≤ 0 := by
  have hid := charSum_eq_neg_mul_halfCharSum hp
  have hpos := halfCharSum_pos hp
  have h2 := legendreSym_two_eq_one_or_neg_one hp
  have hden : (0 : ℤ) < 2 - legendreSym p 2 := by
    rcases h2 with h | h <;> simp [h]
  have hppos : (0 : ℤ) < p := by exact_mod_cast (Nat.Prime.pos Fact.out)
  nlinarith

lemma A048153_prime_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    A048153 p ≤ p * (p - 1) / 2 := by
  have hp2 : p ≠ 2 := by omega
  have h := A048153_eq_add_charSum hp2
  have hT := charSum_nonpos hp
  have : (A048153 p : ℤ) ≤ ↑(p * (p - 1) / 2) := by linarith
  exact_mod_cast this

/-! ### Closing the induction when `4 ∣ n`. -/

lemma two_mul_sub_one_add (t : ℕ) (ht : 0 < t) :
    (2 * t) * (2 * t - 1) + (4 * t) * t = (4 * t) * (4 * t - 1) / 2 := by
  have : (4 * t) * (4 * t - 1) =
      2 * ((2 * t) * (2 * t - 1) + (4 * t) * t) := by
    cases t with
    | zero => simp at ht
    | succ t =>
      -- `2*(t+1)-1 = 2*t+1`, `4*(t+1)-1 = 4*t+3`
      have hA : 2 * (t + 1) - 1 = 2 * t + 1 := by omega
      have hB : 4 * (t + 1) - 1 = 4 * t + 3 := by omega
      rw [hA, hB]
      ring
  rw [this, Nat.mul_div_cancel_left _ (by decide)]

lemma A048153_four_dvd_le {n : ℕ} (h4 : 4 ∣ n) (hn : 1 ≤ n)
    (ih : A048153 (n / 2) ≤ (n / 2) * (n / 2 - 1) / 2)
    (hM : highBitCount n ≤ n / 4) :
    A048153 n ≤ n * (n - 1) / 2 := by
  have hpos : 0 < n := hn
  rw [A048153_of_four_dvd h4 hpos]
  obtain ⟨t, rfl⟩ := h4
  have ht : 0 < t := by omega
  have h2t : (4 * t) / 2 = 2 * t := by omega
  have h4t : (4 * t) / 4 = t := by omega
  rw [h2t]
  simp only [h2t, h4t] at ih hM
  have hev : Even ((2 * t) * (2 * t - 1)) :=
    Even.mul_right ⟨t, by ring⟩ _
  have h1 : 2 * A048153 (2 * t) ≤ (2 * t) * (2 * t - 1) := by
    have := Nat.mul_le_mul_left 2 ih
    rwa [Nat.two_mul_div_two_of_even hev] at this
  have h2 : (4 * t) * highBitCount (4 * t) ≤ (4 * t) * t :=
    Nat.mul_le_mul_left _ hM
  have hleft : 2 * A048153 (2 * t) + (4 * t) * highBitCount (4 * t) ≤
      (2 * t) * (2 * t - 1) + (4 * t) * t :=
    add_le_add h1 h2
  rwa [two_mul_sub_one_add t ht] at hleft

/-! ### The main bound. -/

lemma A048153_le_mul_sub_one : ∀ n : ℕ, 1 ≤ n →
    A048153 n ≤ n * (n - 1) / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hne : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    by_cases hsq : IsSquare (-1 : ZMod n)
    · exact A048153_le_of_neg_one_isSquare n hsq
    · by_cases h4 : 4 ∣ n
      · have hlt : n / 2 < n := Nat.div_lt_self hn (by decide)
        have hn2 : 1 ≤ n / 2 := by
          have : 4 ≤ n := Nat.le_of_dvd hn h4
          omega
        refine A048153_four_dvd_le h4 hn (ih (n / 2) hlt hn2)
          (highBitCount_le_of_four_dvd n h4 hn)
      · by_cases heven : Even n
        · -- `n = 2m` with `m` odd (since `4 ∤ n`).
          obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp heven
          have hodd : Odd m := by
            refine Decidable.by_contra fun hne' => ?_
            have : Even m := Nat.not_odd_iff_even.mp hne'
            obtain ⟨t, ht⟩ := this
            exact h4 ⟨t, by omega⟩
          subst n
          exact A048153_two_mul_odd_le hodd (by omega) (ih m (by omega) (by omega))
        · -- `n` odd and `-1` is not a square.
          sorry

/--
Conjecture: a(n) <= (n^2-1)/2. - _Aspen A.M. Meissner_, Mar 06 2025
We require $n \ge 1$ for the difference $n^2 - 1$ to be a natural number.
The division `/ 2` is natural number (integer) division.
-/
theorem oeis_48153_conjecture_0 (n : ℕ) (h : 1 ≤ n) : A048153 n ≤ (n ^ 2 - 1) / 2 := by
  refine le_of_le_mul_sub_one h ?_
  exact A048153_le_mul_sub_one n h
