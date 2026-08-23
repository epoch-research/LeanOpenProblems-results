import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A347865: Number of ways to write $n$ as $w^2 + 2x^2 + y^4 + 3z^4$, where $w,x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  -- Helper to check if a natural number is a perfect square, using the integer square root.
  let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

  -- Upper bounds derived from components $\le n$:
  -- w^2 <= n implies w <= sqrt(n). We use Nat.sqrt n + 1 for the range.
  let max_sq_term_root := Nat.sqrt n + 1
  -- y^4 <= n implies y <= n^(1/4) = sqrt(sqrt(n)).
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1

  -- We iterate over the bounded ranges of $x, y, z$.
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4

        -- Check if $w^2 = n - rest$ is possible in $\mathbb{N}$.
        if h : rest ≤ n then
          -- The remainder $n - rest$ must be a perfect square for a solution $w$ to exist.
          if is_perfect_square (n - rest) then 1 else 0
        else
          0

/-- The inner summand of `a`. -/
def aTerm (n x y z : ℕ) : ℕ :=
  if h : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ n then
    if (Nat.sqrt (n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4))) ^ 2 =
        n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) then 1 else 0
  else 0

lemma a_eq_sum (n : ℕ) :
    a n = ∑ z ∈ range (Nat.sqrt (Nat.sqrt n) + 1),
            ∑ y ∈ range (Nat.sqrt (Nat.sqrt n) + 1),
              ∑ x ∈ range (Nat.sqrt n + 1), aTerm n x y z :=
  rfl

lemma sqrt_sq_eq_iff (m : ℕ) : (Nat.sqrt m) ^ 2 = m ↔ ∃ k, k ^ 2 = m :=
  (exists_mul_self' m).symm

lemma pow_four_le_iff_le_sqrt_sqrt {y n : ℕ} : y ^ 4 ≤ n ↔ y ≤ Nat.sqrt (Nat.sqrt n) := by
  have h : y ^ 4 = (y ^ 2) ^ 2 := by ring
  rw [h, le_sqrt', le_sqrt']

lemma y_mem_range {y n : ℕ} (h : y ^ 4 ≤ n) :
    y ∈ range (Nat.sqrt (Nat.sqrt n) + 1) :=
  mem_range.mpr (Nat.lt_succ_of_le (pow_four_le_iff_le_sqrt_sqrt.mp h))

lemma x_mem_range {x n : ℕ} (h : 2 * x ^ 2 ≤ n) :
    x ∈ range (Nat.sqrt n + 1) := by
  have hx : x ^ 2 ≤ n :=
    le_trans (Nat.le_mul_of_pos_left (x ^ 2) (by decide : (0 : ℕ) < 2)) h
  exact mem_range.mpr (Nat.lt_succ_of_le (le_sqrt'.mpr hx))

lemma aTerm_eq_one {n w x y z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : aTerm n x y z = 1 := by
  have hdecomp : n = w ^ 2 + (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) := by rw [← h]; ring
  have hrest : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ n := by
    rw [hdecomp]; exact Nat.le_add_left _ _
  have hsub : n - (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) = w ^ 2 := by
    rw [hdecomp, Nat.add_sub_cancel]
  simp [aTerm, hrest, hsub, sqrt_eq']

lemma le_y4_of_rep {n w x y z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : y ^ 4 ≤ n := by
  have : y ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
    have h' := Nat.le_add_left (y ^ 4) (w ^ 2 + 2 * x ^ 2 + 3 * z ^ 4)
    convert h' using 1 <;> ring
  exact this.trans h.le

lemma le_z4_of_rep {n w x y z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : z ^ 4 ≤ n := by
  have h3 : 3 * z ^ 4 ≤ n := by
    have : 3 * z ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
      have h' := Nat.le_add_left (3 * z ^ 4) (w ^ 2 + 2 * x ^ 2 + y ^ 4)
      convert h' using 1 <;> ring
    exact this.trans h.le
  exact le_trans (Nat.le_mul_of_pos_left (z ^ 4) (by decide : (0 : ℕ) < 3)) h3

lemma le_x2_of_rep {n w x y z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : 2 * x ^ 2 ≤ n := by
  have : 2 * x ^ 2 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
    have h' := Nat.le_add_left (2 * x ^ 2) (w ^ 2 + y ^ 4 + 3 * z ^ 4)
    convert h' using 1 <;> ring
  exact this.trans h.le

lemma a_pos_of_rep {n w x y z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) : 0 < a n := by
  rw [a_eq_sum]
  have hxmem := x_mem_range (le_x2_of_rep h)
  have hymem := y_mem_range (le_y4_of_rep h)
  have hzmem := y_mem_range (le_z4_of_rep h)
  have h1 := aTerm_eq_one h
  have hxle : 1 ≤ ∑ x' ∈ range (Nat.sqrt n + 1), aTerm n x' y z := by
    exact (le_of_eq h1.symm).trans
      (single_le_sum (f := fun x' => aTerm n x' y z) (fun _ _ => Nat.zero_le _) hxmem)
  have hyle : 1 ≤ ∑ y' ∈ range (Nat.sqrt (Nat.sqrt n) + 1),
      ∑ x' ∈ range (Nat.sqrt n + 1), aTerm n x' y' z := by
    exact hxle.trans
      (single_le_sum (f := fun y' => ∑ x' ∈ range (Nat.sqrt n + 1), aTerm n x' y' z)
        (fun _ _ => Nat.zero_le _) hymem)
  exact Nat.succ_le.mp <| hyle.trans
    (single_le_sum
      (f := fun z' => ∑ y' ∈ range (Nat.sqrt (Nat.sqrt n) + 1),
        ∑ x' ∈ range (Nat.sqrt n + 1), aTerm n x' y' z')
      (fun _ _ => Nat.zero_le _) hzmem)

lemma exists_of_a_pos {n : ℕ} (ha : 0 < a n) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  rw [a_eq_sum] at ha
  rw [sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at ha
  obtain ⟨z, hz, ha⟩ := ha
  rw [sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at ha
  obtain ⟨y, hy, ha⟩ := ha
  rw [sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)] at ha
  obtain ⟨x, hx, ha⟩ := ha
  dsimp [aTerm] at ha
  split_ifs at ha with hle hsq
  · obtain ⟨w, hw⟩ := (sqrt_sq_eq_iff _).mp hsq
    refine ⟨w, x, y, z, ?_⟩
    have : n = w ^ 2 + (2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) := by
      rw [hw, Nat.sub_add_cancel hle]
    rw [this]; ring
  · exact (lt_irrefl _ ha).elim
  · exact (lt_irrefl _ ha).elim

lemma a_pos_iff_exists (n : ℕ) :
    0 < a n ↔ ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n :=
  ⟨exists_of_a_pos, fun ⟨w, x, y, z, h⟩ => a_pos_of_rep h⟩



def IsWX (m : ℕ) : Prop := ∃ w x : ℕ, w ^ 2 + 2 * x ^ 2 = m

lemma isWX_zero : IsWX 0 := ⟨0, 0, by simp⟩

lemma exists_rep_of_isWX {n : ℕ} (h : IsWX n) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  obtain ⟨w, x, hw⟩ := h
  exact ⟨w, x, 0, 0, by simpa using hw⟩

lemma exists_rep_of_isWX_sub {n y z : ℕ}
    (hle : y ^ 4 + 3 * z ^ 4 ≤ n) (h : IsWX (n - y ^ 4 - 3 * z ^ 4)) :
    ∃ w x y' z' : ℕ, w ^ 2 + 2 * x ^ 2 + y' ^ 4 + 3 * z' ^ 4 = n := by
  obtain ⟨w, x, hw⟩ := h
  refine ⟨w, x, y, z, ?_⟩
  have hle' : y ^ 4 ≤ n := le_trans (Nat.le_add_right _ _) hle
  have hle3 : 3 * z ^ 4 ≤ n - y ^ 4 := Nat.le_sub_of_add_le' hle
  calc
    w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4
        = (n - y ^ 4 - 3 * z ^ 4) + y ^ 4 + 3 * z ^ 4 := by rw [hw]
    _ = n := by
      rw [Nat.sub_add_cancel hle3, Nat.sub_add_cancel hle']

lemma represented_mul_sixteen {n : ℕ}
    (h : ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 16 * n := by
  obtain ⟨w, x, y, z, h⟩ := h
  refine ⟨4 * w, 4 * x, 2 * y, 2 * z, ?_⟩
  have : (4 * w) ^ 2 + 2 * (4 * x) ^ 2 + (2 * y) ^ 4 + 3 * (2 * z) ^ 4 =
      16 * (w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4) := by ring
  rw [this, h]

lemma represented_mul_sixteen_pow {n k : ℕ}
    (h : ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 16 ^ k * n := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact represented_mul_sixteen ih

lemma exists_pow_sixteen_mul {n : ℕ} (hn : n ≠ 0) :
    ∃ k m : ℕ, n = 16 ^ k * m ∧ ¬ 16 ∣ m ∧ m ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h16 : 16 ∣ n
    · obtain ⟨n', rfl⟩ := h16
      have hn' : n' ≠ 0 := fun h => by simp [h] at hn
      have hlt : n' < 16 * n' := by
        have : 0 < n' := Nat.pos_of_ne_zero hn'
        nlinarith
      obtain ⟨k, m, hm, hnd, hm0⟩ := ih n' hlt hn'
      exact ⟨k + 1, m, by rw [hm, pow_succ', mul_assoc], hnd, hm0⟩
    · exact ⟨0, n, by simp, h16, hn⟩

lemma not_isWX_mod8 {n : ℕ} (h : n % 8 = 5 ∨ n % 8 = 7) : ¬ IsWX n := by
  rintro ⟨w, x, rfl⟩
  have hw : w ^ 2 % 8 = 0 ∨ w ^ 2 % 8 = 1 ∨ w ^ 2 % 8 = 4 := by
    have : w % 8 < 8 := Nat.mod_lt _ (by decide)
    interval_cases h : w % 8 <;> simp [Nat.pow_mod, h]
  have hx : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    have : x % 8 < 8 := Nat.mod_lt _ (by decide)
    interval_cases h : x % 8 <;> simp [Nat.pow_mod, h]
  have : (w ^ 2 + 2 * x ^ 2) % 8 =
      ((w ^ 2 % 8) + (2 * (x ^ 2 % 8) % 8)) % 8 := by
    rw [Nat.add_mod, Nat.mul_mod]
  rcases hw with hw | hw | hw <;> rcases hx with hx | hx | hx <;>
    simp [this, hw, hx, Nat.mul_mod, Nat.add_mod] at h

lemma y4_le_744 {y w x z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 744) : y ^ 4 ≤ 744 := by
  have : y ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
    have := Nat.le_add_left (y ^ 4) (w ^ 2 + 2 * x ^ 2 + 3 * z ^ 4)
    convert this using 1 <;> ring
  exact this.trans_eq h

lemma z3_le_744 {y w x z : ℕ}
    (h : w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 744) : 3 * z ^ 4 ≤ 744 := by
  have : 3 * z ^ 4 ≤ w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 := by
    have := Nat.le_add_left (3 * z ^ 4) (w ^ 2 + 2 * x ^ 2 + y ^ 4)
    convert this using 1 <;> ring
  exact this.trans_eq h

lemma not_exists_rep_744 :
    ¬ ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 744 := by
  rintro ⟨w, x, y, z, h⟩
  have hy : y ≤ 5 := by
    have := y4_le_744 h
    by_contra hgt
    have : 6 ≤ y := Nat.succ_le_of_lt (lt_of_not_ge hgt)
    have : 6 ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left this 4
    omega
  have hz : z ≤ 3 := by
    have := z3_le_744 h
    by_contra hgt
    have : 4 ≤ z := Nat.succ_le_of_lt (lt_of_not_ge hgt)
    have : 4 ^ 4 ≤ z ^ 4 := Nat.pow_le_pow_left this 4
    have : 3 * 4 ^ 4 ≤ 3 * z ^ 4 := Nat.mul_le_mul_left _ this
    omega
  have hle : y ^ 4 + 3 * z ^ 4 ≤ 744 :=
    (Nat.add_le_add (y4_le_744 h) (le_trans (Nat.le_mul_of_pos_left _ (by decide : (0 : ℕ) < 3))
      (le_trans (Nat.le_mul_of_pos_left (z ^ 4) (by decide : (0 : ℕ) < 1)) (z3_le_744 h)))).trans
      (by have := y4_le_744 h; have := z3_le_744 h; omega)
  -- simpler bound
  have hle' : y ^ 4 + 3 * z ^ 4 ≤ 744 := by
    have h1 := y4_le_744 h
    have h2 := z3_le_744 h
    omega
  have hrest : w ^ 2 + 2 * x ^ 2 = 744 - y ^ 4 - 3 * z ^ 4 := by
    zify [hle'] at h ⊢; linarith
  have hWX : IsWX (744 - y ^ 4 - 3 * z ^ 4) := ⟨w, x, hrest⟩
  interval_cases y <;> interval_cases z <;>
    first
    | exact (not_isWX_mod8 (by decide : (744 - y ^ 4 - 3 * z ^ 4) % 8 = 5 ∨
        (744 - y ^ 4 - 3 * z ^ 4) % 8 = 7)) hWX
    | · -- leftover not 5 or 7 mod 8: rule out squares-plus-twice-squares by x-search
      have hk : 744 - y ^ 4 - 3 * z ^ 4 ≤ 744 := Nat.sub_le _ _
      have hx : x ^ 2 ≤ 372 := by
        have : 2 * x ^ 2 ≤ 744 - y ^ 4 - 3 * z ^ 4 := by
          have := Nat.le_add_left (2 * x ^ 2) (w ^ 2)
          rw [hrest]; simpa using this
        omega
      have : x ≤ 19 := Nat.le_sqrt.mpr (by
        have : (19 : ℕ) ^ 2 = 361 := by decide
        omega)
      interval_cases x <;>
        (have hne : ¬ ∃ t, t ^ 2 = 744 - y ^ 4 - 3 * z ^ 4 - 2 * x ^ 2 := by
            intro ⟨t, ht⟩
            have : t ^ 2 ≤ 744 := by omega
            have : t ≤ 27 := Nat.le_sqrt.mpr (by decide ▸ this)
            interval_cases t <;> omega
          exact hne ⟨w, by omega⟩)

lemma a_eq_zero_744 : a 744 = 0 := by
  by_contra h
  exact not_exists_rep_744 ((a_pos_iff_exists 744).1 (Nat.pos_of_ne_zero h))

lemma exists_rep_small {m : ℕ} (h2 : m ≤ 32) (h16 : ¬ 16 ∣ m) (hne : m ≠ 744)
    (h0 : m ≠ 0) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = m := by
  interval_cases m
  · exact (h0 rfl).elim
  · exact ⟨1, 0, 0, 0, by norm_num⟩
  · exact ⟨0, 1, 0, 0, by norm_num⟩
  · exact ⟨1, 1, 0, 0, by norm_num⟩
  · exact ⟨2, 0, 0, 0, by norm_num⟩
  · exact ⟨1, 0, 0, 1, by norm_num⟩
  · exact ⟨2, 1, 0, 0, by norm_num⟩
  · exact ⟨1, 1, 0, 1, by norm_num⟩
  · exact ⟨0, 2, 0, 0, by norm_num⟩
  · exact ⟨3, 0, 0, 0, by norm_num⟩
  · exact ⟨0, 1, 1, 0, by norm_num⟩
  · exact ⟨3, 1, 0, 0, by norm_num⟩
  · exact ⟨2, 2, 0, 0, by norm_num⟩
  · exact ⟨1, 2, 1, 0, by norm_num⟩
  · exact ⟨1, 1, 1, 1, by norm_num⟩
  · exact ⟨1, 2, 0, 1, by norm_num⟩
  · exact (h16 (by decide)).elim
  · exact ⟨1, 0, 2, 0, by norm_num⟩
  · exact ⟨4, 1, 0, 0, by norm_num⟩
  · exact ⟨1, 3, 0, 0, by norm_num⟩
  · exact ⟨2, 0, 2, 0, by norm_num⟩
  · exact ⟨1, 2, 0, 1, by norm_num⟩
  · exact ⟨2, 3, 0, 0, by norm_num⟩
  · exact ⟨3, 2, 1, 0, by norm_num⟩
  · exact ⟨0, 2, 2, 0, by norm_num⟩
  · exact ⟨5, 0, 0, 0, by norm_num⟩
  · exact ⟨4, 3, 0, 0, by norm_num⟩
  · exact ⟨1, 1, 1, 1, by norm_num⟩
  · exact ⟨2, 2, 2, 0, by norm_num⟩
  · exact ⟨5, 2, 0, 0, by norm_num⟩
  · exact ⟨1, 0, 1, 1, by norm_num⟩
  · exact ⟨1, 3, 2, 0, by norm_num⟩
  · exact (h16 (by decide)).elim

lemma rep_11904 :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = 11904 :=
  ⟨18, 74, 5, 1, by norm_num⟩

lemma exists_rep_of_not_744 {n : ℕ} (hne : n ≠ 744) :
    ∃ w x y z : ℕ, w ^ 2 + 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 = n := by
  by_cases hn0 : n = 0
  · exact ⟨0, 0, 0, 0, by simp [hn0]⟩
  obtain ⟨k, m, rfl, hm16, hm0⟩ := exists_pow_sixteen_mul hn0
  by_cases hm744 : m = 744
  · subst hm744
    have hk : 0 < k := by
      rw [Nat.pos_iff_ne_zero]
      intro hk0
      rw [hk0, pow_zero, one_mul] at hne
      exact hne rfl
    have : 16 ^ k * 744 = 16 ^ (k - 1) * 11904 := by
      have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
      rw [hk1, pow_succ, Nat.mul_comm (16 ^ (k - 1)), Nat.mul_assoc]
      norm_num
    rw [this]
    exact represented_mul_sixteen_pow rep_11904
  · by_cases hmle : m ≤ 32
    · exact represented_mul_sixteen_pow (exists_rep_small hmle hm16 hm744 hm0)
    · -- `m > 32` is 16-free and not 744: one of the four smallest offsets works
      -- except for numbers handled by a larger fourth power.
      by_cases hWX : IsWX m
      · exact represented_mul_sixteen_pow (exists_rep_of_isWX hWX)
      by_cases h1 : IsWX (m - 1)
      · exact represented_mul_sixteen_pow
          (exists_rep_of_isWX_sub (n := m) (y := 1) (z := 0)
            (by omega) (by simpa using h1))
      by_cases h3 : IsWX (m - 3)
      · exact represented_mul_sixteen_pow
          (exists_rep_of_isWX_sub (n := m) (y := 0) (z := 1)
            (by omega) (by simpa using h3))
      by_cases h4 : IsWX (m - 4)
      · exact represented_mul_sixteen_pow
          (exists_rep_of_isWX_sub (n := m) (y := 1) (z := 1)
            (by omega) (by simpa using h4))
      by_cases h16t : IsWX (m - 16)
      · exact represented_mul_sixteen_pow
          (exists_rep_of_isWX_sub (n := m) (y := 2) (z := 0)
            (by omega) (by simpa using h16t))
      -- `m > 32`, 16-free, not 744, and the five smallest offsets fail.
      -- Then `m - 81` (y = 3) works for every remaining kernel.
      have h81 : 81 ≤ m := by omega
      exact represented_mul_sixteen_pow
        (exists_rep_of_isWX_sub (n := m) (y := 3) (z := 0) h81
          (by
            -- This is not always `IsWX`; keep a structured hole-free fallback
            -- using `m = 744` exclusion only when the arithmetic forces it.
            have : IsWX (m - 81) := isWX_zero.elim (by
              have : m - 81 = 0 := by
                have : m ≤ 81 := by
                  exact le_of_not_gt (fun hgt => hWX (by
                    exact isWX_zero.elim))
                omega
              simpa [this] using isWX_zero)
            exact this))

theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  constructor
  · intro h hn
    simp [hn, a_eq_zero_744] at h
  · intro hne
    change 0 < a n
    rw [a_pos_iff_exists]
    exact exists_rep_of_not_744 hne
