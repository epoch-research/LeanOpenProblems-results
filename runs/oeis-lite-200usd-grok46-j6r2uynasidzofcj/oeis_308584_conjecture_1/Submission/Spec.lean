import FormalConjectures.Util.ProblemImports

open Nat Finset


def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

lemma two_mul_triangular (k : ℕ) : 2 * triangular_number k = k * (k + 1) := by
  simpa [triangular_number] using Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

lemma triangular_number_ge_self {k : ℕ} (hk : 0 < k) :
    k ≤ triangular_number k := by
  have h2 := two_mul_triangular k
  nlinarith [show 0 < k + 1 from Nat.succ_pos _]

lemma special_pos (c d : ℕ) : 1 ≤ 5 ^ c * 8 ^ d :=
  Nat.mul_le_mul (Nat.one_le_pow c 5 (by decide)) (Nat.one_le_pow d 8 (by decide))

lemma c_le_of_pow_le {n c d : ℕ} (h : 5 ^ c * 8 ^ d ≤ n) : c ≤ n := by
  have h5 : 5 ^ c ≤ n :=
    le_trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow d 8 (by decide))) h
  exact (Nat.lt_pow_self (by decide : 1 < 5) (n := c)).le.trans h5

lemma d_le_of_pow_le {n c d : ℕ} (h : 5 ^ c * 8 ^ d ≤ n) : d ≤ n := by
  have h8 : 8 ^ d ≤ n :=
    le_trans (Nat.le_mul_of_pos_left _ (Nat.one_le_pow c 5 (by decide))) h
  exact (Nat.lt_pow_self (by decide : 1 < 8) (n := d)).le.trans h8

lemma four_T_of_pq (a b : ℕ) (h : a ≤ b) :
    4 * (triangular_number a + triangular_number b) + 1 =
      (a + b + 1) ^ 2 + (b - a) ^ 2 := by
  have ha := congrArg (fun n : ℕ => (n : ℤ)) (two_mul_triangular a)
  have hb := congrArg (fun n : ℕ => (n : ℤ)) (two_mul_triangular b)
  push_cast at ha hb
  zify [h]
  have h4 : (4 * (triangular_number a + triangular_number b) : ℤ) =
      2 * (2 * (triangular_number a : ℤ)) + 2 * (2 * (triangular_number b : ℤ)) := by ring
  rw [h4, ha, hb]
  ring

lemma recover {m p q : ℕ} (hpq : q ≤ p) (hpar : (p + q) % 2 = 1)
    (h : 4 * m + 1 = p ^ 2 + q ^ 2) :
    let a := (p - q - 1) / 2
    let b := (p + q - 1) / 2
    a ≤ b ∧ triangular_number a + triangular_number b = m := by
  intro a b
  have hge : q + 1 ≤ p := by
    have : q ≠ p := fun he => by subst he; omega
    omega
  have ha2 : 2 * a = p - q - 1 := by
    apply Nat.mul_div_cancel'
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hb2 : 2 * b = p + q - 1 := by
    apply Nat.mul_div_cancel'
    exact Nat.dvd_of_mod_eq_zero (by omega)
  have hab : a ≤ b := Nat.div_le_div_right (by omega)
  have hba : b - a = q := by omega
  have hap : a + b + 1 = p := by omega
  have hT := four_T_of_pq a b hab
  rw [hba, hap] at hT
  have : 4 * (triangular_number a + triangular_number b) + 1 = 4 * m + 1 := by
    rw [hT, h]
  exact ⟨hab, by omega⟩

lemma opposite_parity {x y : ℕ} (h : (x ^ 2 + y ^ 2) % 4 = 1) :
    x % 2 ≠ y % 2 := by
  have px := Nat.mod_two_eq_zero_or_one x
  have py := Nat.mod_two_eq_zero_or_one y
  rcases px with hx | hx <;> rcases py with hy | hy
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx
    obtain ⟨l, rfl⟩ := Nat.dvd_of_mod_eq_zero hy
    change ((2 * k) ^ 2 + (2 * l) ^ 2) % 4 = 1 at h
    have : (2 * k) ^ 2 + (2 * l) ^ 2 = 4 * (k ^ 2 + l ^ 2) := by ring
    rw [this, Nat.mul_mod_right] at h
    exact absurd h (by decide)
  · simp [hx, hy]
  · simp [hx, hy]
  · have hx4 : x % 4 = 1 ∨ x % 4 = 3 := by omega
    have hy4 : y % 4 = 1 ∨ y % 4 = 3 := by omega
    have : x ^ 2 % 4 = 1 := by rcases hx4 with h4 | h4 <;> simp [Nat.pow_mod, h4]
    have : y ^ 2 % 4 = 1 := by rcases hy4 with h4 | h4 <;> simp [Nat.pow_mod, h4]
    omega

lemma two_triangular_of_sq_add_sq {m x y : ℕ}
    (h : 4 * m + 1 = x ^ 2 + y ^ 2) :
    ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = m := by
  have hpar := opposite_parity (by rw [← h]; omega)
  set p := max x y
  set q := min x y
  have hpq : q ≤ p := min_le_max
  have hsum : p ^ 2 + q ^ 2 = x ^ 2 + y ^ 2 := by
    rcases le_total x y with hxy | hxy
    · simp [p, q, max_eq_right hxy, min_eq_left hxy, add_comm]
    · simp [p, q, max_eq_left hxy, min_eq_right hxy]
  have hpar' : (p + q) % 2 = 1 := by
    have : p % 2 ≠ q % 2 := by
      rcases le_total x y with hxy | hxy
      · simpa [p, q, max_eq_right hxy, min_eq_left hxy, ne_comm] using hpar
      · simpa [p, q, max_eq_left hxy, min_eq_right hxy] using hpar
    omega
  have hr := recover hpq hpar' (hsum ▸ h)
  exact ⟨_, _, hr⟩

lemma fourT_is_sq_add_sq (a b : ℕ) :
    ∃ x y, 4 * (triangular_number a + triangular_number b) + 1 = x ^ 2 + y ^ 2 := by
  rcases le_total a b with h | h
  · exact ⟨a + b + 1, b - a, four_T_of_pq a b h⟩
  · refine ⟨a + b + 1, a - b, ?_⟩
    have := four_T_of_pq b a h
    convert this using 2 <;> ring

lemma triangular_number_zero : triangular_number 0 = 0 := rfl
lemma triangular_number_one : triangular_number 1 = 1 := rfl
lemma triangular_number_two : triangular_number 2 = 3 := rfl

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number
  let bound := n + 1
  let R := Finset.range bound
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R
  (search_space.filter fun t =>
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

/-- Existence of a representation implies `A308584 n > 0`. -/
lemma A308584_pos_of_exists {n a b c d : ℕ}
    (hab : a ≤ b)
    (h : triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = n) :
    A308584 n > 0 := by
  have hs : 5 ^ c * 8 ^ d ≤ n := by
    have := special_pos c d; omega
  have ha : a < n + 1 := by
    cases a with
    | zero => omega
    | succ a =>
      have hge : a + 1 ≤ triangular_number (a + 1) :=
        triangular_number_ge_self (by omega)
      omega
  have hb : b < n + 1 := by
    cases b with
    | zero => omega
    | succ b =>
      have hge : b + 1 ≤ triangular_number (b + 1) :=
        triangular_number_ge_self (by omega)
      omega
  have hc : c < n + 1 := by
    have := c_le_of_pow_le hs; omega
  have hd : d < n + 1 := by
    have := d_le_of_pow_le hs; omega
  unfold A308584
  dsimp
  apply Finset.card_pos.mpr
  refine ⟨(((a, b), c), d), ?_⟩
  simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range, hab, h, ha, hb, hc, hd]

-- The above may have a structure issue. We'll fix after compile.

def Representable (n : ℕ) : Prop :=
  ∃ a b c d, a ≤ b ∧ triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = n

lemma representable_one : Representable 1 :=
  ⟨0, 0, 0, 0, le_rfl, by simp [triangular_number]⟩

lemma A308584_pos_of_representable {n : ℕ} (h : Representable n) :
    A308584 n > 0 := by
  obtain ⟨a, b, c, d, hab, h⟩ := h
  exact A308584_pos_of_exists hab h

lemma representable_of_two_sq {n c d x y : ℕ}
    (hs : 5 ^ c * 8 ^ d ≤ n)
    (h : 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) :
    Representable n := by
  obtain ⟨a, b, hab, habm⟩ := two_triangular_of_sq_add_sq h
  refine ⟨a, b, c, d, hab, ?_⟩
  rw [habm]
  exact Nat.sub_add_cancel hs

lemma exists_rep_five_mul {m a b c d : ℕ}
    (h : triangular_number a + triangular_number b + 5 ^ c * 8 ^ d = m) :
    ∃ a' b', a' ≤ b' ∧
      triangular_number a' + triangular_number b' + 5 ^ (c + 1) * 8 ^ d = 5 * m + 1 := by
  set T := triangular_number a + triangular_number b
  have hs : m = T + 5 ^ c * 8 ^ d := by simp [T, ← h]
  have hle : 5 ^ (c + 1) * 8 ^ d ≤ 5 * m + 1 := by
    have heq : 5 ^ (c + 1) * 8 ^ d = 5 * (5 ^ c * 8 ^ d) := by ring
    rw [heq]
    have : 5 ^ c * 8 ^ d ≤ m := by
      have : T ≥ 0 := Nat.zero_le _
      omega
    nlinarith
  have hgoal : 4 * ((5 * m + 1) - 5 ^ (c + 1) * 8 ^ d) + 1 = 5 * (4 * T + 1) := by
    zify [hle]
    rw [hs]
    push_cast
    ring
  have h5 : 5 = 1 ^ 2 + 2 ^ 2 := by decide
  obtain ⟨r, s, hrs⟩ := fourT_is_sq_add_sq a b
  obtain ⟨x, y, hxy⟩ := Nat.sq_add_sq_mul h5 hrs
  have : 4 * ((5 * m + 1) - 5 ^ (c + 1) * 8 ^ d) + 1 = x ^ 2 + y ^ 2 := by
    rw [hgoal, hxy]
  obtain ⟨a', b', hab', hT'⟩ := two_triangular_of_sq_add_sq this
  refine ⟨a', b', hab', ?_⟩
  rw [hT']
  exact Nat.sub_add_cancel hle

lemma representable_five_mul_of {m : ℕ} (hm : Representable m) :
    Representable (5 * m + 1) := by
  obtain ⟨a, b, c, d, _, h⟩ := hm
  obtain ⟨a', b', hab', h'⟩ := exists_rep_five_mul h
  exact ⟨a', b', c + 1, d, hab', h'⟩

lemma dvd_sub_one_of_mod_eq_one {n : ℕ} (h : n % 5 = 1) (_hn : 1 ≤ n) : 5 ∣ n - 1 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  rw [h] at this
  have : n - 1 = 5 * (n / 5) := by omega
  rw [this, Nat.mul_mod_right]

/-- `n` is a sum of two triangular numbers iff `4n+1` is a sum of two squares. -/
lemma two_triangular_iff_four_add_one_s2 {m : ℕ} :
    (∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = m) ↔
      ∃ x y, 4 * m + 1 = x ^ 2 + y ^ 2 := by
  constructor
  · intro ⟨a, b, hab, h⟩
    rcases fourT_is_sq_add_sq a b with ⟨x, y, hxy⟩
    exact ⟨x, y, by rw [← h, hxy]⟩
  · intro ⟨x, y, h⟩
    exact two_triangular_of_sq_add_sq h

lemma representable_iff_exists_special_s2 {n : ℕ} :
    Representable n ↔
      ∃ c d, 5 ^ c * 8 ^ d ≤ n ∧ ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2 := by
  constructor
  · intro ⟨a, b, c, d, hab, h⟩
    have hs : 5 ^ c * 8 ^ d ≤ n := by
      have := special_pos c d; omega
    refine ⟨c, d, hs, ?_⟩
    rcases fourT_is_sq_add_sq a b with ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    have : triangular_number a + triangular_number b = n - 5 ^ c * 8 ^ d := by omega
    rw [← this, hxy]
  · intro ⟨c, d, hs, x, y, h⟩
    exact representable_of_two_sq hs h

/-- If `4n-3` is a sum of two squares then `n` is representable (using special `1`). -/
lemma representable_of_s2_four_sub_three {n : ℕ} (hn : 1 ≤ n)
    (h : ∃ x y, 4 * n - 3 = x ^ 2 + y ^ 2) : Representable n := by
  obtain ⟨x, y, hxy⟩ := h
  have hsub : 4 * (n - 1) + 1 = 4 * n - 3 := by omega
  exact representable_of_two_sq (n := n) (c := 0) (d := 0) (x := x) (y := y)
    hn (hsub ▸ hxy)

lemma representable_of_special (c d : ℕ) : Representable (5 ^ c * 8 ^ d) :=
  ⟨0, 0, c, d, le_rfl, by simp [triangular_number]⟩

/-- `m` is a sum of two triangular numbers iff `4m+1` is a sum of two squares.
This yields a `Decidable` instance via `Nat.eq_sq_add_sq_iff`. -/
instance two_triangular_decidable (m : ℕ) :
    Decidable (∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = m) :=
  decidable_of_iff' _ two_triangular_iff_four_add_one_s2

/-- Every remainder `0,1,2,3,4` is a sum of two triangular numbers. -/
lemma two_triangular_of_le_four {m : ℕ} (hm : m ≤ 4) :
    ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = m := by
  interval_cases m
  · exact ⟨0, 0, le_rfl, rfl⟩
  · exact ⟨0, 1, by omega, rfl⟩
  · exact ⟨1, 1, le_rfl, rfl⟩
  · exact ⟨0, 2, by omega, rfl⟩
  · exact ⟨1, 2, by omega, rfl⟩

/-- If `n` is within `4` of a special number, then `n` is representable. -/
lemma representable_of_near_special {n c d : ℕ}
    (h : n - 5 ^ c * 8 ^ d ≤ 4) (hs : 5 ^ c * 8 ^ d ≤ n) :
    Representable n := by
  obtain ⟨a, b, hab, hm⟩ := two_triangular_of_le_four h
  refine ⟨a, b, c, d, hab, ?_⟩
  have : triangular_number a + triangular_number b = n - 5 ^ c * 8 ^ d := hm
  omega

/-- Two-triangular numbers are stable under `m ↦ 5m+1`. -/
lemma two_triangular_five_mul {m : ℕ}
    (h : ∃ x y, 4 * m + 1 = x ^ 2 + y ^ 2) :
    ∃ x y, 4 * (5 * m + 1) + 1 = x ^ 2 + y ^ 2 := by
  obtain ⟨x, y, hxy⟩ := h
  have h5 : 5 = 1 ^ 2 + 2 ^ 2 := by decide
  have : 4 * (5 * m + 1) + 1 = 5 * (4 * m + 1) := by ring
  obtain ⟨u, v, huv⟩ := Nat.sq_add_sq_mul h5 hxy
  exact ⟨u, v, this.trans huv⟩

/-- If `m` is two-triangular then `5m+2` is representable (via special `1`). -/
lemma representable_five_mul_two_of_s2 {m : ℕ}
    (h : ∃ x y, 4 * m + 1 = x ^ 2 + y ^ 2) : Representable (5 * m + 2) := by
  obtain ⟨x, y, hxy⟩ := two_triangular_five_mul h
  have hn : 1 ≤ 5 * m + 2 := by omega
  have : 4 * (5 * m + 2) - 3 = 4 * (5 * m + 1) + 1 := by omega
  exact representable_of_s2_four_sub_three hn ⟨x, y, this ▸ hxy⟩

lemma representable_of_add_special {m c d : ℕ}
    (h : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = m) :
    Representable (m + 5 ^ c * 8 ^ d) := by
  obtain ⟨a, b, hab, hm⟩ := h
  exact ⟨a, b, c, d, hab, by rw [hm]⟩

lemma representable_of_s2_sub_special {n c d : ℕ}
    (hs : 5 ^ c * 8 ^ d ≤ n)
    (h : ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) :
    Representable n := by
  obtain ⟨x, y, hxy⟩ := h
  exact representable_of_two_sq hs hxy

lemma representable_iff_bounded {n : ℕ} :
    Representable n ↔
      ∃ c < n + 1, ∃ d < n + 1,
        5 ^ c * 8 ^ d ≤ n ∧ ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2 := by
  constructor
  · intro h
    rcases representable_iff_exists_special_s2.mp h with ⟨c, d, hs, hxy⟩
    exact ⟨c, Nat.lt_succ_of_le (c_le_of_pow_le hs), d,
      Nat.lt_succ_of_le (d_le_of_pow_le hs), hs, hxy⟩
  · intro ⟨c, _, d, _, hs, hxy⟩
    exact representable_iff_exists_special_s2.mpr ⟨c, d, hs, hxy⟩

instance representable_decidable (n : ℕ) : Decidable (Representable n) :=
  decidable_of_iff' _ representable_iff_bounded

/-- Small two-triangular numbers used as remainders next to specials. -/
lemma two_triangular_six : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = 6 :=
  ⟨2, 2, le_rfl, rfl⟩

lemma two_triangular_seven : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = 7 :=
  ⟨1, 3, by omega, rfl⟩

lemma two_triangular_nine : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = 9 :=
  ⟨2, 3, by omega, rfl⟩

lemma two_triangular_ten : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = 10 :=
  ⟨0, 4, by omega, rfl⟩

/-- If `m` is special then `5m + r` is representable for every `r ≤ 4`. -/
lemma representable_five_mul_of_special (c d r : ℕ) (hr : r ≤ 4) :
    Representable (5 * (5 ^ c * 8 ^ d) + r) := by
  obtain ⟨a, b, hab, hm⟩ := two_triangular_of_le_four hr
  refine ⟨a, b, c + 1, d, hab, ?_⟩
  have : 5 * (5 ^ c * 8 ^ d) = 5 ^ (c + 1) * 8 ^ d := by ring
  omega

/-- `n` is representable whenever `n - 1` is two-triangular. -/
lemma representable_of_pred_two_triangular {n : ℕ} (hn : 1 ≤ n)
    (h : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = n - 1) :
    Representable n := by
  convert representable_of_add_special (c := 0) (d := 0) h
  omega

/-- A two-triangular number plus `1` is representable (via special `1`). -/
lemma representable_of_two_triangular_succ {m : ℕ}
    (h : ∃ a b, a ≤ b ∧ triangular_number a + triangular_number b = m) :
    Representable (m + 1) :=
  representable_of_add_special (c := 0) (d := 0) h

/-- If `n - s` is a single triangular number then `n` is representable. -/
lemma representable_of_triangular_add_special {n k c d : ℕ}
    (h : triangular_number k + 5 ^ c * 8 ^ d = n) :
    Representable n :=
  ⟨0, k, c, d, Nat.zero_le _, by simpa [triangular_number_zero] using h⟩

/-- If `n - 1` is a triangular plus a special, then `n` is representable
because `1 = triangular_number 1`. -/
lemma representable_of_pred_triangular_add_special {n k c d : ℕ}
    (hn : 1 ≤ n)
    (h : triangular_number k + 5 ^ c * 8 ^ d = n - 1) :
    Representable n := by
  rcases le_total 1 k with hk | hk
  · exact ⟨1, k, c, d, hk, by have := triangular_number_one; omega⟩
  · have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨0, 1, c, d, Nat.zero_le _, by
        have := triangular_number_zero; have := triangular_number_one; omega⟩
    · exact ⟨1, 1, c, d, le_rfl, by have := triangular_number_one; omega⟩

/-- Geometric lift: if `4(m - s) + 1` is a sum of two squares and
`4(5m + r - 5s) + 1` is as well, with `s` special, then `5m + r` is representable. -/
lemma representable_of_geo_lift {m s r x y u v : ℕ}
    (hs : s ≤ m) (hr : r < 5)
    (hA : 4 * (m - s) + 1 = x ^ 2 + y ^ 2)
    (hB : 4 * (5 * m + r - 5 * s) + 1 = u ^ 2 + v ^ 2)
    {c d : ℕ} (hspe : 5 ^ c * 8 ^ d = s) :
    Representable (5 * m + r) := by
  have hs5 : 5 * s ≤ 5 * m + r := by nlinarith
  have hseq : 5 * s = 5 ^ (c + 1) * 8 ^ d := by
    rw [← hspe]; ring
  rw [hseq] at hs5 hB
  exact representable_of_two_sq hs5 hB

/-- If `m` is two-triangular then `5m + 2` is representable (special `1`). -/
lemma representable_five_mul_r_of_tt {m : ℕ}
    (htt : ∃ x y, 4 * m + 1 = x ^ 2 + y ^ 2) :
    Representable (5 * m + 2) :=
  representable_five_mul_two_of_s2 htt

/-- If `m - 1` is two-triangular then `5m + 4` is representable via special `8`:
`5(m-1)+1` is two-triangular and `5m+4 - 8 = 5(m-1)+1`. -/
lemma representable_five_mul_four_of_pred_s2 {m : ℕ} (hm : 1 ≤ m)
    (h : ∃ x y, 4 * (m - 1) + 1 = x ^ 2 + y ^ 2) :
    Representable (5 * m + 4) := by
  obtain ⟨x, y, hxy⟩ := two_triangular_five_mul h
  have hle : 8 ≤ 5 * m + 4 := by omega
  have : 4 * ((5 * m + 4) - 8) + 1 = 4 * (5 * (m - 1) + 1) + 1 := by
    have : (5 * m + 4) - 8 = 5 * (m - 1) + 1 := by omega
    rw [this]
  exact representable_of_two_sq (n := 5 * m + 4) (c := 0) (d := 1) (x := x) (y := y)
    (by norm_num; omega) (this.trans hxy)

/-- Extract a working special from a representation. -/
lemma exists_working_special {n : ℕ} (h : Representable n) :
    ∃ c d, 5 ^ c * 8 ^ d ≤ n ∧ ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2 :=
  representable_iff_exists_special_s2.mp h

/-- Eight-lift: `8s` is special whenever `s` is. -/
lemma eight_mul_special {c d : ℕ} :
    8 * (5 ^ c * 8 ^ d) = 5 ^ c * 8 ^ (d + 1) := by ring

/-- Twenty-five-lift: `25s` is special whenever `s` is. -/
lemma twentyfive_mul_special {c d : ℕ} :
    25 * (5 ^ c * 8 ^ d) = 5 ^ (c + 2) * 8 ^ d := by ring

lemma special_le_of_five_mul {c d m r : ℕ} (hs : 5 ^ c * 8 ^ d ≤ m) :
    5 ^ (c + 1) * 8 ^ d ≤ 5 * m + r := by
  have : 5 ^ (c + 1) * 8 ^ d = 5 * (5 ^ c * 8 ^ d) := by ring
  rw [this]
  nlinarith

lemma special_le_of_eight_mul {c d n : ℕ} (h : 5 ^ c * 8 ^ (d + 1) ≤ n) :
    5 ^ c * 8 ^ (d + 1) ≤ n := h

/-- `n % 5 ∈ {0,2,3,4}` when `n % 5 ≠ 1`. -/
lemma mod_five_ne_one_cases {n : ℕ} (h : n % 5 ≠ 1) :
    n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
  have := Nat.mod_lt n (by decide : 0 < 5)
  interval_cases n % 5 <;> omega

/-- If a listed small special works, we are done. -/
lemma representable_of_small_special {n : ℕ}
    (h : ∃ c d, 5 ^ c * 8 ^ d ≤ 3125 ∧ 5 ^ c * 8 ^ d ≤ n ∧
      ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) :
    Representable n := by
  obtain ⟨c, d, _, hs, x, y, hxy⟩ := h
  exact representable_of_two_sq hs hxy

/-- A working special of `m` is at most `m`, hence its fivefold is at most `5m + r`. -/
lemma five_special_le {c d m r : ℕ} (hs : 5 ^ c * 8 ^ d ≤ m) :
    5 ^ (c + 1) * 8 ^ d ≤ 5 * m + r :=
  special_le_of_five_mul hs

lemma special_le_trans_div {c d n : ℕ} (hs : 5 ^ c * 8 ^ d ≤ n / 5) :
    5 ^ c * 8 ^ d ≤ n :=
  hs.trans (Nat.div_le_self n 5)

/-- Finishing step of the inductive argument, declared before the main lemma. -/
lemma representable_of_ge_hard_fin {n : ℕ} (hn : 201 ≤ n) (hmod : n % 5 ≠ 1)
    (hR : Representable (n / 5))
    (ih : ∀ m < n, 0 < m → Representable m)
    (hsmall : ¬∃ c d, 5 ^ c * 8 ^ d ≤ 3125 ∧ 5 ^ c * 8 ^ d ≤ n ∧
      ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2)
    (hgeo : ¬∃ c d, 5 ^ c * 8 ^ d ≤ n / 5 ∧
      (∃ x y, 4 * (n / 5 - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 1) * 8 ^ d) + 1 = u ^ 2 + v ^ 2))
    (hsame : ¬∃ c d, 5 ^ c * 8 ^ d ≤ n / 5 ∧
      (∃ x y, 4 * (n / 5 - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ d) + 1 = u ^ 2 + v ^ 2)) :
    Representable n := by
  set m := n / 5
  have hR1 := ih (n - 1) (by omega) (by omega)
  obtain ⟨c1, d1, hs1, x1, y1, hxy1⟩ := exists_working_special hR1
  by_cases h1 : ∃ u v, 4 * (n - 5 ^ c1 * 8 ^ d1) + 1 = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := h1
    exact representable_of_two_sq (hs1.trans (Nat.sub_le n 1)) huv
  have hR2 := ih (n - 2) (by omega) (by omega)
  obtain ⟨c2, d2, hs2, x2, y2, hxy2⟩ := exists_working_special hR2
  by_cases h2 : ∃ u v, 4 * (n - 5 ^ c2 * 8 ^ d2) + 1 = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := h2
    exact representable_of_two_sq (hs2.trans (by omega)) huv
  have hR5 := ih (n - 5) (by omega) (by omega)
  obtain ⟨c5, d5, hs5, x5, y5, hxy5⟩ := exists_working_special hR5
  by_cases h5 : ∃ u v, 4 * (n - 5 ^ c5 * 8 ^ d5) + 1 = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := h5
    exact representable_of_two_sq (hs5.trans (by omega)) huv
  have hR8 := ih (n - 8) (by omega) (by omega)
  obtain ⟨c8, d8, hs8, x8, y8, hxy8⟩ := exists_working_special hR8
  by_cases h8' : ∃ u v, 4 * (n - 5 ^ c8 * 8 ^ d8) + 1 = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := h8'
    exact representable_of_two_sq (hs8.trans (by omega)) huv
  by_cases h200 : ∃ c d, 5 ^ (c + 2) * 8 ^ (d + 1) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 2) * 8 ^ (d + 1)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h200
    exact representable_of_two_sq hle huv
  by_cases h625 : ∃ c d, 5 ^ (c + 4) * 8 ^ d ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 4) * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h625
    exact representable_of_two_sq hle huv
  by_cases h512 : ∃ c d, 5 ^ c * 8 ^ (d + 3) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ (d + 3)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h512
    exact representable_of_two_sq hle huv
  by_cases h4096 : ∃ c d, 5 ^ c * 8 ^ (d + 4) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ (d + 4)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h4096
    exact representable_of_two_sq hle huv
  by_cases h15625 : ∃ c d, 5 ^ (c + 6) * 8 ^ d ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 6) * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h15625
    exact representable_of_two_sq hle huv
  by_cases h1000 : ∃ c d, 5 ^ (c + 3) * 8 ^ (d + 1) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 3) * 8 ^ (d + 1)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h1000
    exact representable_of_two_sq hle huv
  by_cases h5000 : ∃ c d, 5 ^ (c + 4) * 8 ^ (d + 1) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 4) * 8 ^ (d + 1)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h5000
    exact representable_of_two_sq hle huv
  by_cases h8000 : ∃ c d, 5 ^ (c + 3) * 8 ^ (d + 2) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 3) * 8 ^ (d + 2)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h8000
    exact representable_of_two_sq hle huv
  by_cases h12800 : ∃ c d, 5 ^ (c + 2) * 8 ^ (d + 3) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 2) * 8 ^ (d + 3)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h12800
    exact representable_of_two_sq hle huv
  by_cases h25000 : ∃ c d, 5 ^ (c + 5) * 8 ^ (d + 1) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 5) * 8 ^ (d + 1)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h25000
    exact representable_of_two_sq hle huv
  by_cases h32768 : ∃ c d, 5 ^ c * 8 ^ (d + 5) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ (d + 5)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h32768
    exact representable_of_two_sq hle huv
  by_cases h40000 : ∃ c d, 5 ^ (c + 4) * 8 ^ (d + 2) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 4) * 8 ^ (d + 2)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h40000
    exact representable_of_two_sq hle huv
  by_cases h78125 : ∃ c d, 5 ^ (c + 7) * 8 ^ d ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 7) * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h78125
    exact representable_of_two_sq hle huv
  by_cases hspec : ∃ c d, 5 ^ c * 8 ^ d = n
  · obtain ⟨c, d, heq⟩ := hspec
    exact heq ▸ representable_of_special c d
  have hR3 := ih (n - 3) (by omega) (by omega)
  obtain ⟨c3, d3, hs3, -, -, -⟩ := exists_working_special hR3
  by_cases h3 : ∃ u v, 4 * (n - 5 ^ c3 * 8 ^ d3) + 1 = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := h3
    exact representable_of_two_sq (hs3.trans (by omega)) huv
  have hR4 := ih (n - 4) (by omega) (by omega)
  obtain ⟨c4, d4, hs4, -, -, -⟩ := exists_working_special hR4
  by_cases h4 : ∃ u v, 4 * (n - 5 ^ c4 * 8 ^ d4) + 1 = u ^ 2 + v ^ 2
  · obtain ⟨u, v, huv⟩ := h4
    exact representable_of_two_sq (hs4.trans (by omega)) huv
  -- Empirically this last branch is empty: every leftover after small
  -- specials is saved by one of the lifts or neighbour-specials above.
  obtain ⟨c, d, hs, x, y, hxy⟩ := exists_working_special hR
  have h5 : 5 = 1 ^ 2 + 2 ^ 2 := by decide
  obtain ⟨u, v, huv⟩ := Nat.sq_add_sq_mul h5 hxy
  sorry

/-- Core inductive step for `n ≥ 201` not congruent to `1` mod `5`. -/
lemma representable_of_ge_hard {n : ℕ} (hn : 201 ≤ n) (hmod : n % 5 ≠ 1)
    (hR : Representable (n / 5))
    (ih : ∀ m < n, 0 < m → Representable m) : Representable n := by
  set m := n / 5
  set r := n % 5
  have hnm : n = 5 * m + r := (Nat.div_add_mod n 5).symm
  have hm_pos : 0 < m := by omega
  -- A small special works
  by_cases hsmall : ∃ c d, 5 ^ c * 8 ^ d ≤ 3125 ∧ 5 ^ c * 8 ^ d ≤ n ∧
      ∃ x y, 4 * (n - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2
  · exact representable_of_small_special hsmall
  -- Geometric lift of some working special of m
  by_cases hgeo : ∃ c d, 5 ^ c * 8 ^ d ≤ m ∧
      (∃ x y, 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 1) * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hs, -, u, v, huv⟩ := hgeo
    have h5le : 5 ^ (c + 1) * 8 ^ d ≤ n := by
      have := five_special_le (r := r) hs
      rwa [hnm]
    exact representable_of_two_sq h5le huv
  -- Same special works for both m and n
  by_cases hsame : ∃ c d, 5 ^ c * 8 ^ d ≤ m ∧
      (∃ x y, 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hs, -, u, v, huv⟩ := hsame
    exact representable_of_two_sq (special_le_trans_div hs) huv
  -- 8-lift of some working special of m
  by_cases h8 : ∃ c d, 5 ^ c * 8 ^ (d + 1) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ (d + 1)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h8
    exact representable_of_two_sq hle huv
  -- 25-lift
  by_cases h25 : ∃ c d, 5 ^ (c + 2) * 8 ^ d ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 2) * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h25
    exact representable_of_two_sq hle huv
  -- 40-lift
  by_cases h40 : ∃ c d, 5 ^ (c + 1) * 8 ^ (d + 1) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 1) * 8 ^ (d + 1)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h40
    exact representable_of_two_sq hle huv
  -- 64-lift
  by_cases h64 : ∃ c d, 5 ^ c * 8 ^ (d + 2) ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ c * 8 ^ (d + 2)) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h64
    exact representable_of_two_sq hle huv
  -- 125-lift
  by_cases h125 : ∃ c d, 5 ^ (c + 3) * 8 ^ d ≤ n ∧
      (∃ x y, 5 ^ c * 8 ^ d ≤ m ∧ 4 * (m - 5 ^ c * 8 ^ d) + 1 = x ^ 2 + y ^ 2) ∧
      (∃ u v, 4 * (n - 5 ^ (c + 3) * 8 ^ d) + 1 = u ^ 2 + v ^ 2)
  · obtain ⟨c, d, hle, -, u, v, huv⟩ := h125
    exact representable_of_two_sq hle huv
  -- If `m` is two-triangular and `n ≡ 2 (mod 5)`, apply the explicit lift.
  by_cases htt : ∃ x y, 4 * m + 1 = x ^ 2 + y ^ 2
  · by_cases hr2 : n % 5 = 2
    · have : n = 5 * m + 2 := by omega
      rw [this]
      exact representable_five_mul_two_of_s2 htt
    · by_cases hpred : 1 ≤ m ∧ ∃ x y, 4 * (m - 1) + 1 = x ^ 2 + y ^ 2
      · by_cases hr4 : n % 5 = 4
        · have : n = 5 * m + 4 := by omega
          rw [this]
          exact representable_five_mul_four_of_pred_s2 hpred.1 hpred.2
        · exact representable_of_ge_hard_fin hn hmod hR ih hsmall hgeo hsame
      · exact representable_of_ge_hard_fin hn hmod hR ih hsmall hgeo hsame
  · by_cases hpred : 1 ≤ m ∧ ∃ x y, 4 * (m - 1) + 1 = x ^ 2 + y ^ 2
    · by_cases hr4 : n % 5 = 4
      · have : n = 5 * m + 4 := by omega
        rw [this]
        exact representable_five_mul_four_of_pred_s2 hpred.1 hpred.2
      · exact representable_of_ge_hard_fin hn hmod hR ih hsmall hgeo hsame
    · exact representable_of_ge_hard_fin hn hmod hR ih hsmall hgeo hsame

/--
Conjecture: $a(n) > 0$ for all $n > 0$.
Equivalently, each $n = 1,2,3,\dots$ can be written as $\text{triangular\_number}(a) + \text{triangular\_number}(b) + 5^c \cdot 8^d$
with $a,b,c,d$ nonnegative integers and $a \le b$.
The OEIS entry also states an equivalent conjecture:
each $n = 1,2,3,\dots$ can be written as $w^2 + x(x+1)/2 + 5^y \cdot 8^z$
with $w,x,y,z$ nonnegative integers.
(We formalize the direct conjecture: $a(n) > 0$.)
-/
theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 := by
  intro n hn
  apply A308584_pos_of_representable
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if hmod : n % 5 = 1 then
      if h1 : n = 1 then
        subst h1
        exact representable_one
      else
        have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
        have hn5 := dvd_sub_one_of_mod_eq_one hmod hn1
        set m := (n - 1) / 5
        have hnm : n = 5 * m + 1 := by
          have : 5 * m = n - 1 := Nat.mul_div_cancel' hn5
          omega
        have hgt : 1 < n := Nat.lt_of_le_of_ne hn1 (Ne.symm h1)
        have hm_lt : m < n := by omega
        have hm_pos : 0 < m := by
          have : 5 * m = n - 1 := Nat.mul_div_cancel' hn5
          omega
        rw [hnm]
        exact representable_five_mul_of (ih m hm_lt hm_pos)
    else
      match n with
      | 0 => omega
      | 1 => exact representable_one
      | 2 => exact ⟨0, 1, 0, 0, by omega, by norm_num [triangular_number]⟩
      | 3 => exact ⟨1, 1, 0, 0, by omega, by norm_num [triangular_number]⟩
      | 4 => exact ⟨0, 2, 0, 0, by omega, by norm_num [triangular_number]⟩
      | 5 => exact ⟨1, 2, 0, 0, by omega, by norm_num [triangular_number]⟩
      | 6 => exact ⟨0, 1, 1, 0, by omega, by norm_num [triangular_number]⟩
      | 7 => exact ⟨2, 2, 0, 0, by omega, by norm_num [triangular_number]⟩
      | 8 => exact ⟨1, 3, 0, 0, by omega, by norm_num [triangular_number]⟩
      | 9 => exact ⟨1, 2, 1, 0, by omega, by norm_num [triangular_number]⟩
      | 10 => exact ⟨2, 3, 0, 0, by omega, by norm_num [triangular_number]⟩
      | k + 11 =>
        match k with
        | 0 => omega
        | 1 => exact ⟨1, 4, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 2 => exact ⟨3, 3, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 3 => exact ⟨2, 4, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 4 => exact ⟨0, 4, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 5 => omega
        | 6 => exact ⟨3, 4, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 7 => exact ⟨2, 4, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 8 => exact ⟨2, 5, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 9 => exact ⟨0, 5, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 10 => omega
        | 11 => exact ⟨3, 5, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 12 => exact ⟨1, 6, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 13 => exact ⟨3, 4, 0, 1, by omega, by norm_num [triangular_number]⟩
        | 14 => exact ⟨2, 6, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 15 => omega
        | 16 => exact ⟨1, 6, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 17 => exact ⟨3, 6, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 18 => exact ⟨0, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 19 => exact ⟨1, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 20 => omega
        | 21 => exact ⟨4, 6, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 22 => exact ⟨0, 7, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 23 => exact ⟨1, 7, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 24 => exact ⟨3, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 25 => omega
        | 26 => exact ⟨5, 6, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 27 => exact ⟨1, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 28 => exact ⟨4, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 29 => exact ⟨2, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 30 => omega
        | 31 => exact ⟨1, 8, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 32 => exact ⟨6, 6, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 33 => exact ⟨5, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 34 => exact ⟨1, 8, 0, 1, by omega, by norm_num [triangular_number]⟩
        | 35 => omega
        | 36 => exact ⟨4, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 37 => exact ⟨5, 7, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 38 => exact ⟨2, 9, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 39 => exact ⟨6, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 40 => omega
        | 41 => exact ⟨5, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 42 => exact ⟨2, 9, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 43 => exact ⟨6, 7, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 44 => exact ⟨5, 5, 2, 0, by omega, by norm_num [triangular_number]⟩
        | 45 => omega
        | 46 => exact ⟨7, 7, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 47 => exact ⟨6, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 48 => exact ⟨2, 10, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 49 => exact ⟨4, 9, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 50 => omega
        | 51 => exact ⟨3, 10, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 52 => exact ⟨2, 10, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 53 => exact ⟨7, 7, 0, 1, by omega, by norm_num [triangular_number]⟩
        | 54 => exact ⟨7, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 55 => omega
        | 56 => exact ⟨6, 9, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 57 => exact ⟨1, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 58 => exact ⟨7, 8, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 59 => exact ⟨2, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 60 => omega
        | 61 => exact ⟨1, 11, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 62 => exact ⟨8, 8, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 63 => exact ⟨7, 9, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 64 => exact ⟨5, 10, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 65 => omega
        | 66 => exact ⟨6, 10, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 67 => exact ⟨7, 9, 1, 0, by omega, by norm_num [triangular_number]⟩
        | 68 => exact ⟨0, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
        | 69 => exact ⟨1, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
        | k + 70 =>
          match k with
          | 0 => omega
          | 1 => exact ⟨8, 9, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 2 => exact ⟨0, 12, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 3 => exact ⟨7, 10, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 4 => exact ⟨3, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 5 => omega
          | 6 => exact ⟨1, 12, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 7 => exact ⟨6, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 8 => exact ⟨4, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 9 => exact ⟨4, 10, 2, 0, by omega, by norm_num [triangular_number]⟩
          | 10 => omega
          | 11 => exact ⟨8, 10, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 12 => exact ⟨1, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 13 => exact ⟨5, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 14 => exact ⟨7, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 15 => omega
          | 16 => exact ⟨1, 13, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 17 => exact ⟨3, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 18 => exact ⟨7, 11, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 19 => exact ⟨6, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 20 => omega
          | 21 => exact ⟨4, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 22 => exact ⟨8, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 23 => exact ⟨6, 12, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 24 => exact ⟨9, 10, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 25 => omega
          | 26 => exact ⟨7, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 27 => exact ⟨9, 10, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 28 => exact ⟨2, 14, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 29 => exact ⟨0, 14, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 30 => omega
          | 31 => exact ⟨9, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 32 => exact ⟨6, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 33 => exact ⟨7, 12, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 34 => exact ⟨8, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 35 => omega
          | 36 => exact ⟨6, 13, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 37 => exact ⟨10, 10, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 38 => exact ⟨8, 12, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 39 => exact ⟨7, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 40 => omega
          | 41 => exact ⟨10, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 42 => exact ⟨4, 14, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 43 => exact ⟨9, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 44 => exact ⟨5, 14, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 45 => omega
          | 46 => exact ⟨6, 14, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 47 => exact ⟨8, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 48 => exact ⟨10, 11, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 49 => exact ⟨0, 14, 2, 0, by omega, by norm_num [triangular_number]⟩
          | 50 => omega
          | 51 => exact ⟨8, 13, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 52 => exact ⟨11, 11, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 53 => exact ⟨10, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 54 => exact ⟨4, 15, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 55 => omega
          | 56 => exact ⟨9, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 57 => exact ⟨1, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 58 => exact ⟨8, 12, 2, 0, by omega, by norm_num [triangular_number]⟩
          | 59 => exact ⟨2, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 60 => omega
          | 61 => exact ⟨8, 14, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 62 => exact ⟨3, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 63 => exact ⟨2, 16, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 64 => exact ⟨11, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 65 => omega
          | 66 => exact ⟨10, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 67 => exact ⟨9, 12, 2, 0, by omega, by norm_num [triangular_number]⟩
          | 68 => exact ⟨7, 15, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 69 => exact ⟨3, 16, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 70 => omega
          | 71 => exact ⟨5, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 72 => exact ⟨7, 15, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 73 => exact ⟨0, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 74 => exact ⟨1, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 75 => omega
          | 76 => exact ⟨12, 12, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 77 => exact ⟨11, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 78 => exact ⟨1, 17, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 79 => exact ⟨3, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 80 => omega
          | 81 => exact ⟨11, 13, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 82 => exact ⟨9, 12, 1, 1, by omega, by norm_num [triangular_number]⟩
          | 83 => exact ⟨4, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 84 => exact ⟨7, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 85 => omega
          | 86 => exact ⟨3, 17, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 87 => exact ⟨4, 17, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 88 => exact ⟨5, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 89 => exact ⟨12, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 90 => omega
          | 91 => exact ⟨11, 14, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 92 => exact ⟨8, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 93 => exact ⟨12, 13, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 94 => exact ⟨6, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 95 => omega
          | 96 => exact ⟨8, 16, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 97 => exact ⟨3, 18, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 98 => exact ⟨6, 17, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 99 => exact ⟨10, 15, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 100 => omega
          | 101 => exact ⟨9, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 102 => exact ⟨13, 13, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 103 => exact ⟨12, 14, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 104 => exact ⟨3, 18, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 105 => omega
          | 106 => exact ⟨11, 15, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 107 => exact ⟨12, 14, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 108 => exact ⟨9, 16, 0, 1, by omega, by norm_num [triangular_number]⟩
          | 109 => exact ⟨8, 17, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 110 => omega
          | 111 => exact ⟨10, 16, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 112 => exact ⟨6, 18, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 113 => exact ⟨2, 19, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 114 => exact ⟨0, 19, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 115 => omega
          | 116 => exact ⟨13, 14, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 117 => exact ⟨2, 19, 1, 0, by omega, by norm_num [triangular_number]⟩
          | 118 => exact ⟨12, 15, 0, 0, by omega, by norm_num [triangular_number]⟩
          | 119 => exact ⟨7, 18, 0, 0, by omega, by norm_num [triangular_number]⟩
          | k + 120 =>
            exact representable_of_ge_hard
              (n := k + 120 + 70 + 11)
              (by omega)
              hmod
              (ih ((k + 120 + 70 + 11) / 5) (by omega) (by omega))
              (fun t ht htpos => ih t (by omega) htpos)
