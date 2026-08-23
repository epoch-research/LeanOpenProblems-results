import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000

/--
A308950: Number of ways to write $n$ as $(p-1)/6 + 2^a 3^b$, where $p$ is a prime, and $a$ and $b$ are nonnegative integers.
$a(n)$ is the number of pairs $(a, b) \in \mathbb{N}^2$ such that $2^a 3^b \le n$ and $6(n - 2^a 3^b) + 1$ is prime.
-/
noncomputable def A308950 (n : ℕ) : ℕ :=
  -- We use a simple, guaranteed-to-be-sufficiently-large finite search space.
  -- For $2^a 3^b \le n$, both $a$ and $b$ are at most $n$.
  Finset.card $
    (Finset.range (n + 1)).product (Finset.range (n + 1)) |>.filter
    (fun p_ab =>
      let a := p_ab.fst
      let b := p_ab.snd
      let m := 2 ^ a * 3 ^ b
      -- Constraint 1: Ensure that $n - m$ is a natural number, and thus $p \ge 1$.
      m ≤ n ∧
      -- Constraint 2: The resulting $p$ must be prime.
      Nat.Prime (6 * (n - m) + 1)
    )

/-- The predicate appearing in the conjecture. -/
def SunGood (n : ℕ) : Prop :=
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1))
  ∨
  (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1))

lemma sunGood_of_sub_smooth_pos {n k a b : ℕ}
    (h : n - k = 2 ^ a * 3 ^ b) (hk : k ≤ n)
    (hp : Nat.Prime (6 * k + 1)) : SunGood n := by
  have hnk : n - 2 ^ a * 3 ^ b = k := by
    rw [← h, Nat.sub_sub_self hk]
  refine Or.inl ⟨a, b, ?_, ?_⟩
  · rw [← h]; exact Nat.sub_le n k
  · rwa [hnk]

lemma sunGood_of_sub_smooth_neg {n k a b : ℕ}
    (h : n - k = 2 ^ a * 3 ^ b) (hk : k < n) (hk0 : 0 < k)
    (hp : Nat.Prime (6 * k - 1)) : SunGood n := by
  have hle : k ≤ n := Nat.le_of_lt hk
  have hnk : n - 2 ^ a * 3 ^ b = k := by
    rw [← h, Nat.sub_sub_self hle]
  refine Or.inr ⟨a, b, ?_, ?_⟩
  · rw [← h]; exact Nat.sub_lt (Nat.zero_lt_of_lt hk) hk0
  · rwa [hnk]

lemma sunGood_of_good_k (k a b : ℕ) (hp : Nat.Prime (6 * k + 1)) :
    SunGood (2 ^ a * 3 ^ b + k) := by
  refine Or.inl ⟨a, b, Nat.le_add_right _ _, ?_⟩
  convert hp
  exact Nat.add_sub_cancel_left (2 ^ a * 3 ^ b) k

lemma sunGood_of_good_k_neg (k a b : ℕ) (hk0 : 0 < k) (hp : Nat.Prime (6 * k - 1)) :
    SunGood (2 ^ a * 3 ^ b + k) := by
  refine Or.inr ⟨a, b, ?_, ?_⟩
  · have : 0 < 2 ^ a * 3 ^ b := by positivity
    omega
  · rw [Nat.add_sub_cancel_left]
    exact hp

lemma goodk1 : Nat.Prime (6 * 1 + 1) := by norm_num
lemma goodk2 : Nat.Prime (6 * 2 + 1) := by norm_num
lemma goodk3 : Nat.Prime (6 * 3 + 1) := by norm_num
lemma goodk4 : Nat.Prime (6 * 4 - 1) := by norm_num
lemma goodk5 : Nat.Prime (6 * 5 + 1) := by norm_num
lemma goodk6 : Nat.Prime (6 * 6 + 1) := by norm_num
lemma goodk7 : Nat.Prime (6 * 7 + 1) := by norm_num
lemma goodk8 : Nat.Prime (6 * 8 - 1) := by norm_num
lemma goodk9 : Nat.Prime (6 * 9 - 1) := by norm_num
lemma goodk10 : Nat.Prime (6 * 10 + 1) := by norm_num
lemma goodk11 : Nat.Prime (6 * 11 + 1) := by norm_num
lemma goodk12 : Nat.Prime (6 * 12 + 1) := by norm_num
lemma goodk13 : Nat.Prime (6 * 13 + 1) := by norm_num
lemma goodk14 : Nat.Prime (6 * 14 - 1) := by norm_num
lemma goodk15 : Nat.Prime (6 * 15 - 1) := by norm_num
lemma goodk16 : Nat.Prime (6 * 16 + 1) := by norm_num
lemma goodk17 : Nat.Prime (6 * 17 + 1) := by norm_num
lemma goodk18 : Nat.Prime (6 * 18 + 1) := by norm_num
lemma goodk19 : Nat.Prime (6 * 19 - 1) := by norm_num

/-- If `n` lies at distance `k ∈ {1,...,19}` from a 3-smooth number, then `SunGood n`. -/
lemma sunGood_of_near_smooth {n a b k : ℕ}
    (hk : k ∈ Finset.Icc 1 19) (h : n = 2 ^ a * 3 ^ b + k) : SunGood n := by
  have hkpos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk19 : k ≤ 19 := (Finset.mem_Icc.mp hk).2
  have hkn : k ≤ n := by omega
  have hsmooth_pos : 0 < 2 ^ a * 3 ^ b := by positivity
  interval_cases k
  · refine sunGood_of_sub_smooth_pos (n := n) (k := 1) (a := a) (b := b) ?_ hkn goodk1
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 2) (a := a) (b := b) ?_ (by omega) goodk2
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 3) (a := a) (b := b) ?_ (by omega) goodk3
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 4) (a := a) (b := b) ?_ (by omega) (by omega) goodk4
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 5) (a := a) (b := b) ?_ (by omega) goodk5
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 6) (a := a) (b := b) ?_ (by omega) goodk6
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 7) (a := a) (b := b) ?_ (by omega) goodk7
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 8) (a := a) (b := b) ?_ (by omega) (by omega) goodk8
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 9) (a := a) (b := b) ?_ (by omega) (by omega) goodk9
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 10) (a := a) (b := b) ?_ (by omega) goodk10
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 11) (a := a) (b := b) ?_ (by omega) goodk11
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 12) (a := a) (b := b) ?_ (by omega) goodk12
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 13) (a := a) (b := b) ?_ (by omega) goodk13
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 14) (a := a) (b := b) ?_ (by omega) (by omega) goodk14
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 15) (a := a) (b := b) ?_ (by omega) (by omega) goodk15
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 16) (a := a) (b := b) ?_ (by omega) goodk16
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 17) (a := a) (b := b) ?_ (by omega) goodk17
    · omega
  · refine sunGood_of_sub_smooth_pos (k := 18) (a := a) (b := b) ?_ (by omega) goodk18
    · omega
  · refine sunGood_of_sub_smooth_neg (k := 19) (a := a) (b := b) ?_ (by omega) (by omega) goodk19
    · omega

lemma sunGood_two : SunGood 2 := Or.inl ⟨0, 0, by norm_num, by norm_num⟩

lemma sunGood_of_one_lt_of_le_two {n : ℕ} (hn : 1 < n) (h2 : n ≤ 2) : SunGood n := by
  have : n = 2 := by omega
  simpa [this] using sunGood_two

/-- 3-smooth numbers (Hamming numbers of type 3). -/
def ThreeSmooth (m : ℕ) : Prop := ∃ a b : ℕ, m = 2 ^ a * 3 ^ b

lemma threeSmooth_one : ThreeSmooth 1 := ⟨0, 0, by simp⟩

lemma threeSmooth_two_pow (a : ℕ) : ThreeSmooth (2 ^ a) := ⟨a, 0, by simp⟩

lemma threeSmooth_mul {m n : ℕ} (hm : ThreeSmooth m) (hn : ThreeSmooth n) :
    ThreeSmooth (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  refine ⟨a + c, b + d, ?_⟩
  rw [pow_add, pow_add]
  ring

/-- There is always a 3-smooth in `(n/2, n]`, namely the largest power of two `≤ n`. -/
lemma exists_threeSmooth_mem_Ioc_half (n : ℕ) (hn : 0 < n) :
    ∃ s, ThreeSmooth s ∧ n / 2 < s ∧ s ≤ n := by
  refine ⟨2 ^ Nat.log 2 n, threeSmooth_two_pow _, ?_, Nat.pow_log_le_self 2 (by omega)⟩
  have h2 : 1 < 2 := by norm_num
  have := Nat.lt_pow_succ_log_self h2 n
  -- `2 ^ log2 n ≤ n < 2 ^ (log2 n + 1)` so `n/2 < 2 ^ log2 n` when `n ≥ 1`.
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have : n < 2 * 2 ^ Nat.log 2 n := by
    simpa [pow_succ, mul_comm] using this
  omega

/-- If `n = s + k` with `s` 3-smooth and `1 ≤ k ≤ 19`, then `SunGood n`. -/
lemma sunGood_of_threeSmooth_add_le_19 {n s k : ℕ}
    (hs : ThreeSmooth s) (hk : k ∈ Finset.Icc 1 19) (h : n = s + k) : SunGood n := by
  obtain ⟨a, b, rfl⟩ := hs
  exact sunGood_of_near_smooth hk h

/-- `k` is good if `6k+1` or `6k-1` is prime (the latter requiring `k > 0`). -/
def GoodK (k : ℕ) : Prop :=
  Nat.Prime (6 * k + 1) ∨ (0 < k ∧ Nat.Prime (6 * k - 1))

lemma sunGood_of_goodK {n s : ℕ} (hs : ThreeSmooth s) (hle : s ≤ n)
    (hg : GoodK (n - s)) : SunGood n := by
  obtain ⟨a, b, rfl⟩ := hs
  have hn : n = 2 ^ a * 3 ^ b + (n - 2 ^ a * 3 ^ b) := (Nat.add_sub_of_le hle).symm
  rw [hn]
  rcases hg with hp | ⟨hk0, hm⟩
  · exact sunGood_of_good_k _ a b hp
  · exact sunGood_of_good_k_neg _ a b hk0 hm

lemma goodK_of_mem_Icc_1_19 {k : ℕ} (hk : k ∈ Finset.Icc 1 19) : GoodK k := by
  have hkpos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk19 : k ≤ 19 := (Finset.mem_Icc.mp hk).2
  interval_cases k <;> first
    | exact Or.inl goodk1
    | exact Or.inl goodk2
    | exact Or.inl goodk3
    | exact Or.inr ⟨by omega, goodk4⟩
    | exact Or.inl goodk5
    | exact Or.inl goodk6
    | exact Or.inl goodk7
    | exact Or.inr ⟨by omega, goodk8⟩
    | exact Or.inr ⟨by omega, goodk9⟩
    | exact Or.inl goodk10
    | exact Or.inl goodk11
    | exact Or.inl goodk12
    | exact Or.inl goodk13
    | exact Or.inr ⟨by omega, goodk14⟩
    | exact Or.inr ⟨by omega, goodk15⟩
    | exact Or.inl goodk16
    | exact Or.inl goodk17
    | exact Or.inl goodk18
    | exact Or.inr ⟨by omega, goodk19⟩

lemma sunGood_of_exists_threeSmooth_dist_le_19 {n : ℕ}
    (h : ∃ s, ThreeSmooth s ∧ s ≤ n ∧ n - s ∈ Finset.Icc 1 19) : SunGood n := by
  obtain ⟨s, hs, hle, hd⟩ := h
  exact sunGood_of_goodK hs hle (goodK_of_mem_Icc_1_19 hd)

/-- Boolean search for a 3-smooth witness, used for a finite kernel check. -/
def checkM (n m : ℕ) : Bool :=
  decide (m ≤ n ∧ Nat.Prime (6 * (n - m) + 1))
    || decide (m < n ∧ Nat.Prime (6 * (n - m) - 1))

def checkFrom : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | n, m, fuel + 1 =>
      if m = 0 ∨ n < m then false
      else if checkM n m then true else checkFrom n (m * 2) fuel

def check3 : ℕ → ℕ → ℕ → Bool
  | _, _, 0 => false
  | n, tb, fuel + 1 =>
      if tb = 0 ∨ n < tb then false
      else if checkFrom n tb (fuel + 1) then true else check3 n (tb * 3) fuel

def check (n : ℕ) : Bool := check3 n 1 (n + 8)

lemma checkM_true {n m : ℕ} (h : checkM n m = true) :
    (m ≤ n ∧ Nat.Prime (6 * (n - m) + 1))
      ∨ (m < n ∧ Nat.Prime (6 * (n - m) - 1)) := by
  unfold checkM at h
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact h

lemma sunGood_of_checkM {n m : ℕ} (h : checkM n m = true)
    (hex : ∃ a b, m = 2 ^ a * 3 ^ b) : SunGood n := by
  obtain ⟨a, b, rfl⟩ := hex
  refine (checkM_true h).elim ?_ ?_
  · intro ⟨hle, hp⟩; exact Or.inl ⟨a, b, hle, hp⟩
  · intro ⟨hlt, hp⟩; exact Or.inr ⟨a, b, hlt, hp⟩

lemma checkFrom_sound (n m fuel : ℕ) (h : checkFrom n m fuel = true)
    (hex : ∃ a b, m = 2 ^ a * 3 ^ b) : SunGood n := by
  induction fuel generalizing m with
  | zero => simp [checkFrom] at h
  | succ fuel ih =>
      rw [checkFrom] at h
      by_cases hm : m = 0 ∨ n < m
      · rw [if_pos hm] at h; cases h
      · rw [if_neg hm] at h
        by_cases hM : checkM n m = true
        · rw [if_pos hM] at h; exact sunGood_of_checkM hM hex
        · rw [if_neg hM] at h
          obtain ⟨a, b, rfl⟩ := hex
          exact ih _ h ⟨a + 1, b, by rw [pow_succ]; ac_rfl⟩

lemma check3_sound (n tb fuel : ℕ) (h : check3 n tb fuel = true)
    (hex : ∃ a b, tb = 2 ^ a * 3 ^ b) : SunGood n := by
  induction fuel generalizing tb with
  | zero => simp [check3] at h
  | succ fuel ih =>
      rw [check3] at h
      by_cases ht : tb = 0 ∨ n < tb
      · rw [if_pos ht] at h; cases h
      · rw [if_neg ht] at h
        by_cases hF : checkFrom n tb (fuel + 1) = true
        · rw [if_pos hF] at h; exact checkFrom_sound n tb (fuel + 1) hF hex
        · rw [if_neg hF] at h
          obtain ⟨a, b, rfl⟩ := hex
          exact ih _ h ⟨a, b + 1, by rw [pow_succ, mul_assoc]⟩

lemma check_sound {n : ℕ} (h : check n = true) : SunGood n :=
  check3_sound n 1 (n + 8) h ⟨0, 0, by simp⟩

lemma check_lt_80 : (List.range 80).all (fun n => !decide (1 < n) || check n) = true :=
  rfl

lemma check_lt_200 : (List.range 200).all (fun n => !decide (1 < n) || check n) = true :=
  rfl

lemma sunGood_of_lt_200 {n : ℕ} (hn : 1 < n) (hN : n < 200) : SunGood n := by
  have hall := List.all_eq_true.mp check_lt_200 n (List.mem_range.mpr hN)
  have : check n = true := by
    simp [decide_eq_true hn] at hall
    exact hall
  exact check_sound this

/-- If `k` and `2k` are both good then doubling a 3-smooth summand lifts SunGood. -/
lemma sunGood_two_mul_of_two_lift {n s : ℕ} (hs : ThreeSmooth s) (hle : s ≤ n)
    (hg2 : GoodK (2 * (n - s))) : SunGood (2 * n) := by
  obtain ⟨a, b, rfl⟩ := hs
  have h2s : ThreeSmooth (2 * (2 ^ a * 3 ^ b)) :=
    threeSmooth_mul (threeSmooth_two_pow 1) ⟨a, b, rfl⟩
  have hle2 : 2 * (2 ^ a * 3 ^ b) ≤ 2 * n := Nat.mul_le_mul_left 2 hle
  have heq : 2 * n - 2 * (2 ^ a * 3 ^ b) = 2 * (n - 2 ^ a * 3 ^ b) :=
    (Nat.mul_sub_left_distrib 2 n (2 ^ a * 3 ^ b)).symm
  rw [← heq] at hg2
  exact sunGood_of_goodK h2s hle2 hg2

/-- If `3k` is good then tripling a 3-smooth summand lifts SunGood. -/
lemma sunGood_three_mul_of_three_lift {n s : ℕ} (hs : ThreeSmooth s) (hle : s ≤ n)
    (hg3 : GoodK (3 * (n - s))) : SunGood (3 * n) := by
  obtain ⟨a, b, rfl⟩ := hs
  have h3s : ThreeSmooth (3 * (2 ^ a * 3 ^ b)) :=
    threeSmooth_mul ⟨0, 1, by simp⟩ ⟨a, b, rfl⟩
  have hle3 : 3 * (2 ^ a * 3 ^ b) ≤ 3 * n := Nat.mul_le_mul_left 3 hle
  have heq : 3 * n - 3 * (2 ^ a * 3 ^ b) = 3 * (n - 2 ^ a * 3 ^ b) :=
    (Nat.mul_sub_left_distrib 3 n (2 ^ a * 3 ^ b)).symm
  rw [← heq] at hg3
  exact sunGood_of_goodK h3s hle3 hg3

lemma threeSmooth_48 : ThreeSmooth 48 := ⟨4, 1, by norm_num⟩
lemma threeSmooth_54 : ThreeSmooth 54 := ⟨1, 3, by norm_num⟩
lemma threeSmooth_64 : ThreeSmooth 64 := threeSmooth_two_pow 6
lemma threeSmooth_72 : ThreeSmooth 72 := ⟨3, 2, by norm_num⟩
lemma threeSmooth_81 : ThreeSmooth 81 := ⟨0, 4, by norm_num⟩
lemma threeSmooth_96 : ThreeSmooth 96 := ⟨5, 1, by norm_num⟩
lemma threeSmooth_108 : ThreeSmooth 108 := ⟨2, 3, by norm_num⟩
lemma threeSmooth_128 : ThreeSmooth 128 := threeSmooth_two_pow 7

/--
Conjecture: Let r be 1 or -1. Then, any integer n > 1 can be written as (p-r)/6 + 2^a*3^b, where p is a prime, and a and b are nonnegative integers; in other words, 6*n+r can be written as p + 2^k*3^m, where p is a prime, and k and m are positive integers.
-/
theorem oeis_308950_conjecture :
  ∀ n : ℕ, 1 < n →
    -- Case r = 1: n = (p-1)/6 + 2^a * 3^b  <=>  p = 6*(n - 2^a * 3^b) + 1
    (∃ (a b : ℕ),
        2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1)
    )
    ∨
    -- Case r = -1: n = (p-(-1))/6 + 2^a * 3^b <=> p = 6*(n - 2^a * 3^b) - 1
    (∃ (a b : ℕ),
        -- We require the argument to Nat.Prime to be positive, so 2^a * 3^b < n.
        2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)
    ) := by
  intro n hn
  change SunGood n
  rcases le_or_gt n 199 with hsmall | hge
  · exact sunGood_of_lt_200 hn (by omega)
  -- `n ≥ 200`. There is always a 3-smooth in `(n/2, n]`.
  obtain ⟨s, hs, hhalf, hle⟩ := exists_threeSmooth_mem_Ioc_half n (by omega)
  by_cases hnear : s < n ∧ n - s ≤ 19
  · refine sunGood_of_exists_threeSmooth_dist_le_19 ⟨s, hs, hle, ?_⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hnear.2⟩
  -- If the half-interval 3-smooth is at a good distance, we are done.
  by_cases hgood : GoodK (n - s)
  · exact sunGood_of_goodK hs hle hgood
  -- Try the unit 3-smooth `1` (i.e. `k = n-1`).
  by_cases h1 : GoodK (n - 1)
  · exact sunGood_of_goodK threeSmooth_one (by omega) h1
  -- Try `2`.
  by_cases h2 : GoodK (n - 2)
  · exact sunGood_of_goodK (threeSmooth_two_pow 1) (by omega) h2
  -- Try other small 3-smooths.
  by_cases h3 : GoodK (n - 3)
  · exact sunGood_of_goodK ⟨0, 1, by simp⟩ (by omega) h3
  by_cases h4 : GoodK (n - 4)
  · exact sunGood_of_goodK (threeSmooth_two_pow 2) (by omega) h4
  by_cases h6 : GoodK (n - 6)
  · exact sunGood_of_goodK ⟨1, 1, by simp⟩ (by omega) h6
  by_cases h8 : GoodK (n - 8)
  · exact sunGood_of_goodK (threeSmooth_two_pow 3) (by omega) h8
  by_cases h9 : GoodK (n - 9)
  · exact sunGood_of_goodK ⟨0, 2, by simp⟩ (by omega) h9
  by_cases h12 : GoodK (n - 12)
  · exact sunGood_of_goodK ⟨2, 1, by simp⟩ (by omega) h12
  by_cases h16 : GoodK (n - 16)
  · exact sunGood_of_goodK (threeSmooth_two_pow 4) (by omega) h16
  by_cases h18 : GoodK (n - 18)
  · exact sunGood_of_goodK ⟨1, 2, by simp⟩ (by omega) h18
  by_cases h24 : GoodK (n - 24)
  · exact sunGood_of_goodK ⟨3, 1, by simp⟩ (by omega) h24
  by_cases h27 : GoodK (n - 27)
  · exact sunGood_of_goodK ⟨0, 3, by simp⟩ (by omega) h27
  by_cases h32 : GoodK (n - 32)
  · exact sunGood_of_goodK (threeSmooth_two_pow 5) (by omega) h32
  by_cases h36 : GoodK (n - 36)
  · exact sunGood_of_goodK ⟨2, 2, by simp⟩ (by omega) h36
  by_cases h48 : GoodK (n - 48)
  · exact sunGood_of_goodK threeSmooth_48 (by omega) h48
  by_cases h54 : GoodK (n - 54)
  · exact sunGood_of_goodK threeSmooth_54 (by omega) h54
  by_cases h64 : GoodK (n - 64)
  · exact sunGood_of_goodK threeSmooth_64 (by omega) h64
  by_cases h72 : GoodK (n - 72)
  · exact sunGood_of_goodK threeSmooth_72 (by omega) h72
  by_cases h81 : GoodK (n - 81)
  · exact sunGood_of_goodK threeSmooth_81 (by omega) h81
  by_cases h96 : GoodK (n - 96)
  · exact sunGood_of_goodK threeSmooth_96 (by omega) h96
  by_cases h108 : GoodK (n - 108)
  · exact sunGood_of_goodK threeSmooth_108 (by omega) h108
  by_cases h128 : GoodK (n - 128)
  · exact sunGood_of_goodK threeSmooth_128 (by omega) h128
  -- Remaining case: `n ≥ 200` fails every 3-smooth distance in
  -- `{1,2,3,4,6,8,9,12,16,18,24,27,32,36,48,54,64,72,81,96,108,128}`
  -- and the half-interval power of two.
  sorry
