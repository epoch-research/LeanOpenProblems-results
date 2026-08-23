import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306477: Number of ways to write $n$ as $\binom{w+2}{2} + \binom{x+3}{4} + \binom{y+5}{6} + \binom{z+7}{8}$
with $w,x,y,z$ nonnegative integers, where $\binom{m}{k}$ denotes the binomial coefficient $\frac{m!}{k!(m-k)!}$.
-/
def A306477 (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  R.sum (fun w =>
    R.sum (fun x =>
      R.sum (fun y =>
        R.sum (fun z =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n then 1 else 0
        )
      )
    )
  )

/-- Existence of a representation in range implies `A306477 n > 0`. -/
lemma A306477_pos_of_rep {n w x y z : ℕ}
    (hw : w < n + 1) (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
    (h : (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    A306477 n > 0 := by
  unfold A306477
  set R := Finset.range (n + 1)
  have hwR : w ∈ R := Finset.mem_range.mpr hw
  have hxR : x ∈ R := Finset.mem_range.mpr hx
  have hyR : y ∈ R := Finset.mem_range.mpr hy
  have hzR : z ∈ R := Finset.mem_range.mpr hz
  have hzsum :
      0 < R.sum (fun z' =>
        if (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z' + 7).choose 8 = n
          then 1 else 0) := by
    refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ?_
    refine ⟨z, hzR, ?_⟩
    simp [h]
  have hysum :
      0 < R.sum (fun y' =>
        R.sum (fun z' =>
          if (w + 2).choose 2 + (x + 3).choose 4 + (y' + 5).choose 6 + (z' + 7).choose 8 = n
            then 1 else 0)) := by
    refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ?_
    refine ⟨y, hyR, ?_⟩
    exact hzsum
  have hxsum :
      0 < R.sum (fun x' =>
        R.sum (fun y' =>
          R.sum (fun z' =>
            if (w + 2).choose 2 + (x' + 3).choose 4 + (y' + 5).choose 6 + (z' + 7).choose 8 = n
              then 1 else 0))) := by
    refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ?_
    refine ⟨x, hxR, ?_⟩
    exact hysum
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ?_
  refine ⟨w, hwR, ?_⟩
  exact hxsum

lemma choose_add_two_gt (n : ℕ) : n < (n + 2).choose 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsucc : (n + 1 + 2).choose 2 = (n + 2).choose 1 + (n + 2).choose 2 :=
      Nat.choose_succ_succ' (n + 2) 1
    have hpos : 0 < (n + 2).choose 1 := Nat.choose_pos (by omega)
    omega

/-- `a.choose 2` for `a ≥ 2` is a valid first summand. -/
lemma w_of_choose_two {n a : ℕ} (ha : 2 ≤ a) (h : a.choose 2 ≤ n) :
    a - 2 < n + 1 := by
  have hlt : a < n + 3 := by
    by_contra hnm
    have : (n + 3).choose 2 ≤ a.choose 2 := Nat.choose_le_choose 2 (Nat.le_of_not_lt hnm)
    have : n < (n + 2).choose 2 := choose_add_two_gt n
    have heq : (n + 3).choose 2 = (n + 2).choose 1 + (n + 2).choose 2 :=
      Nat.choose_succ_succ' (n + 2) 1
    have hpos : 0 < (n + 2).choose 1 := Nat.choose_pos (by omega)
    omega
  omega

lemma A306477_pos_of_choose2 {n a : ℕ} (hn : n > 0) (ha : 2 ≤ a)
    (h : a.choose 2 = n) : A306477 n > 0 := by
  refine A306477_pos_of_rep (w := a - 2) (x := 0) (y := 0) (z := 0)
    (w_of_choose_two ha (h ▸ le_rfl)) (by omega) (by omega) (by omega) ?_
  have hw : a - 2 + 2 = a := Nat.sub_add_cancel ha
  simp [hw, h]

lemma choose_add_four_gt (n : ℕ) : n < (n + 4).choose 4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsucc : (n + 1 + 4).choose 4 = (n + 4).choose 3 + (n + 4).choose 4 :=
      Nat.choose_succ_succ' (n + 4) 3
    have hpos : 0 < (n + 4).choose 3 := Nat.choose_pos (by omega)
    omega

lemma choose_add_six_gt (n : ℕ) : n < (n + 6).choose 6 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsucc : (n + 1 + 6).choose 6 = (n + 6).choose 5 + (n + 6).choose 6 :=
      Nat.choose_succ_succ' (n + 6) 5
    have hpos : 0 < (n + 6).choose 5 := Nat.choose_pos (by omega)
    omega

lemma choose_add_eight_gt (n : ℕ) : n < (n + 8).choose 8 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hsucc : (n + 1 + 8).choose 8 = (n + 8).choose 7 + (n + 8).choose 8 :=
      Nat.choose_succ_succ' (n + 8) 7
    have hpos : 0 < (n + 8).choose 7 := Nat.choose_pos (by omega)
    omega

lemma choose_four_le_lt {m n : ℕ} (h : m.choose 4 ≤ n) : m < n + 4 := by
  by_contra hnm
  have : (n + 4).choose 4 ≤ m.choose 4 := Nat.choose_le_choose 4 (Nat.le_of_not_lt hnm)
  have : n < (n + 4).choose 4 := choose_add_four_gt n
  omega

lemma choose_six_le_lt {m n : ℕ} (h : m.choose 6 ≤ n) : m < n + 6 := by
  by_contra hnm
  have : (n + 6).choose 6 ≤ m.choose 6 := Nat.choose_le_choose 6 (Nat.le_of_not_lt hnm)
  have : n < (n + 6).choose 6 := choose_add_six_gt n
  omega

lemma choose_eight_le_lt {m n : ℕ} (h : m.choose 8 ≤ n) : m < n + 8 := by
  by_contra hnm
  have : (n + 8).choose 8 ≤ m.choose 8 := Nat.choose_le_choose 8 (Nat.le_of_not_lt hnm)
  have : n < (n + 8).choose 8 := choose_add_eight_gt n
  omega

/-- Indices for a 4-binomial fall inside `range (n+1)`. -/
lemma x_of_choose_four {n b : ℕ} (h : b.choose 4 ≤ n) :
    (if 3 ≤ b then b - 3 else 0) < n + 1 := by
  have := choose_four_le_lt h
  split_ifs <;> omega

lemma y_of_choose_six {n c : ℕ} (h : c.choose 6 ≤ n) :
    (if 5 ≤ c then c - 5 else 0) < n + 1 := by
  have := choose_six_le_lt h
  split_ifs <;> omega

lemma z_of_choose_eight {n d : ℕ} (h : d.choose 8 ≤ n) :
    (if 7 ≤ d then d - 7 else 0) < n + 1 := by
  have := choose_eight_le_lt h
  split_ifs <;> omega

/-- A representation `n = C(a,2)+C(b,4)+C(c,6)+C(d,8)` with `a ≥ 2` implies positivity. -/
lemma A306477_pos_of_abcd {n a b c d : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 n > 0 := by
  have hn0 : n > 0 := by
    have hpos : 0 < a.choose 2 := Nat.choose_pos ha
    omega
  have h2 : a.choose 2 ≤ n := by omega
  have h4 : b.choose 4 ≤ n := by omega
  have h6 : c.choose 6 ≤ n := by omega
  have h8 : d.choose 8 ≤ n := by omega
  let x := if 3 ≤ b then b - 3 else 0
  let y := if 5 ≤ c then c - 5 else 0
  let z := if 7 ≤ d then d - 7 else 0
  refine A306477_pos_of_rep (w := a - 2) (x := x) (y := y) (z := z)
    (w_of_choose_two ha h2) (x_of_choose_four h4) (y_of_choose_six h6) (z_of_choose_eight h8) ?_
  have hw : a - 2 + 2 = a := Nat.sub_add_cancel ha
  have hx : (x + 3).choose 4 = b.choose 4 := by
    simp [x]
    split_ifs with hb
    · simp [Nat.sub_add_cancel hb]
    · have : b < 4 := by omega
      simp [Nat.choose_eq_zero_of_lt this]
  have hy : (y + 5).choose 6 = c.choose 6 := by
    simp [y]
    split_ifs with hc
    · simp [Nat.sub_add_cancel hc]
    · have : c < 6 := by omega
      simp [Nat.choose_eq_zero_of_lt this]
  have hz : (z + 7).choose 8 = d.choose 8 := by
    simp [z]
    split_ifs with hd
    · simp [Nat.sub_add_cancel hd]
    · have : d < 8 := by omega
      simp [Nat.choose_eq_zero_of_lt this]
  simp [hw, hx, hy, hz, h]

/-- If `n` is a triangular plus a 4-6-8 number, we are done. -/
lemma A306477_pos_of_tri_add {n a x y z : ℕ} (ha : 2 ≤ a)
    (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
    (h : a.choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n) :
    A306477 n > 0 := by
  have hle : a.choose 2 ≤ n := by omega
  refine A306477_pos_of_rep (w := a - 2) (x := x) (y := y) (z := z)
    (w_of_choose_two ha hle) hx hy hz ?_
  simpa [Nat.sub_add_cancel ha] using h

/-- Unit binomial values used for easy increments. -/
lemma choose_four_four : (4 : ℕ).choose 4 = 1 := by decide
lemma choose_six_six : (6 : ℕ).choose 6 = 1 := by decide
lemma choose_eight_eight : (8 : ℕ).choose 8 = 1 := by decide
lemma choose_five_four : (5 : ℕ).choose 4 = 5 := by decide
lemma choose_seven_six : (7 : ℕ).choose 6 = 7 := by decide
lemma choose_nine_eight : (9 : ℕ).choose 8 = 9 := by decide

/-- Increment by turning on an unused 4-binomial. -/
lemma A306477_succ_of_unused4 {n a c d : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 :=
  A306477_pos_of_abcd (a := a) (b := 4) (c := c) (d := d) ha (by
    simp [choose_four_four, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- Increment by turning on an unused 6-binomial. -/
lemma A306477_succ_of_unused6 {n a b d : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + d.choose 8 = n) :
    A306477 (n + 1) > 0 :=
  A306477_pos_of_abcd (a := a) (b := b) (c := 6) (d := d) ha (by
    simp [choose_six_six, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- Increment by turning on an unused 8-binomial. -/
lemma A306477_succ_of_unused8 {n a b c : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + c.choose 6 = n) :
    A306477 (n + 1) > 0 :=
  A306477_pos_of_abcd (a := a) (b := b) (c := c) (d := 8) ha (by
    simp [choose_eight_eight, h, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])

/-- If a representation omits at least one of the types 4,6,8, we can add one. -/
lemma A306477_succ_of_easy {n a b c d : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n)
    (heasy : b < 4 ∨ c < 6 ∨ d < 8) :
    A306477 (n + 1) > 0 := by
  rcases heasy with hb | hc | hd
  · have hb0 : b.choose 4 = 0 := Nat.choose_eq_zero_of_lt hb
    exact A306477_succ_of_unused4 (a := a) (c := c) (d := d) ha (by simp [hb0] at h; exact h)
  · have hc0 : c.choose 6 = 0 := Nat.choose_eq_zero_of_lt hc
    exact A306477_succ_of_unused6 (a := a) (b := b) (d := d) ha (by simp [hc0] at h; exact h)
  · have hd0 : d.choose 8 = 0 := Nat.choose_eq_zero_of_lt hd
    exact A306477_succ_of_unused8 (a := a) (b := b) (c := c) ha (by simp [hd0] at h; exact h)

/-- Special increment: `c = 7`, `d = 8` gives `+1` by `(c,d) ↦ (0,9)`. -/
lemma A306477_succ_of_c7_d8 {n a b : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + (7 : ℕ).choose 6 + (8 : ℕ).choose 8 = n) :
    A306477 (n + 1) > 0 :=
  A306477_pos_of_abcd (a := a) (b := b) (c := 0) (d := 9) ha (by
    have h0 : (0 : ℕ).choose 6 = 0 := Nat.choose_eq_zero_of_lt (by decide)
    have h78 : (7 : ℕ).choose 6 + (8 : ℕ).choose 8 + 1 = (9 : ℕ).choose 8 := by decide
    rw [h0]
    omega)

/-- Increment when `a = (b-1).choose 3 + 1` and `b ≥ 1`: increase `a`, decrease `b`. -/
lemma A306477_succ_of_a_choose3 {n a b c d : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (haeq : a = (b - 1).choose 3 + 1)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 := by
  refine A306477_pos_of_abcd (a := a + 1) (b := b - 1) (c := c) (d := d) (by omega) ?_
  have h2 : (a + 1).choose 2 = a.choose 2 + a := by
    rw [Nat.choose_succ_succ' a 1, Nat.choose_one_right]
    ac_rfl
  have h4 : b.choose 4 = (b - 1).choose 3 + (b - 1).choose 4 := by
    have := Nat.choose_succ_succ' (b - 1) 3
    rwa [Nat.sub_add_cancel hb] at this
  have hinc :
      (a + 1).choose 2 + (b - 1).choose 4 = a.choose 2 + b.choose 4 + 1 := by
    rw [h2, h4, haeq]
    omega
  omega

lemma exists_pos_of_sum_pos {α : Type*} (s : Finset α) (f : α → ℕ)
    (h : 0 < s.sum f) : ∃ a ∈ s, 0 < f a := by
  by_contra hne
  push_neg at hne
  have : s.sum f = 0 := Finset.sum_eq_zero (fun a ha => by
    have := hne a ha
    omega)
  omega

lemma exists_rep_of_pos {n : ℕ} (h : A306477 n > 0) :
    ∃ w x y z, w < n + 1 ∧ x < n + 1 ∧ y < n + 1 ∧ z < n + 1 ∧
      (w + 2).choose 2 + (x + 3).choose 4 + (y + 5).choose 6 + (z + 7).choose 8 = n := by
  unfold A306477 at h
  set R := Finset.range (n + 1)
  obtain ⟨w, hw, hwpos⟩ := exists_pos_of_sum_pos R _ h
  obtain ⟨x, hx, hxpos⟩ := exists_pos_of_sum_pos R _ hwpos
  obtain ⟨y, hy, hypos⟩ := exists_pos_of_sum_pos R _ hxpos
  obtain ⟨z, hz, hzpos⟩ := exists_pos_of_sum_pos R _ hypos
  refine ⟨w, x, y, z, mem_range.mp hw, mem_range.mp hx,
    mem_range.mp hy, mem_range.mp hz, ?_⟩
  split_ifs at hzpos with heq
  · exact heq
  · omega

lemma exists_abcd_of_pos {n : ℕ} (h : A306477 n > 0) :
    ∃ (a b c d : ℕ), 2 ≤ a ∧ a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n := by
  obtain ⟨w, x, y, z, _, _, _, _, heq⟩ := exists_rep_of_pos h
  exact ⟨w + 2, x + 3, y + 5, z + 7, by omega, heq⟩

lemma choose_two_succ (a : ℕ) : (a + 1).choose 2 = a.choose 2 + a := by
  rw [Nat.choose_succ_succ' a 1, Nat.choose_one_right]
  ac_rfl

lemma choose_succ_eight (k : ℕ) : (k + 1).choose 8 = k.choose 8 + k.choose 7 := by
  rw [Nat.choose_succ_succ' k 7]
  ac_rfl

lemma exists_max_choose8 (n : ℕ) :
    ∃ k : ℕ, k.choose 8 ≤ n ∧ ∀ m : ℕ, m.choose 8 ≤ n → m ≤ k := by
  let S := (Finset.range (n + 8)).filter (fun m : ℕ => m.choose 8 ≤ n)
  have h0 : 0 ∈ S := by
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
    have : (0 : ℕ).choose 8 = 0 := Nat.choose_eq_zero_of_lt (by omega : (0 : ℕ) < 8)
    omega
  have hne : S.Nonempty := ⟨0, h0⟩
  refine ⟨S.max' hne, ?_, ?_⟩
  · have := mem_filter.mp (S.max'_mem hne)
    exact this.2
  · intro m hm
    have hm_bound : m < n + 8 := choose_eight_le_lt hm
    have : m ∈ S := mem_filter.mpr ⟨mem_range.mpr hm_bound, hm⟩
    exact le_max' S m this

lemma max_choose8_ge_eight {n : ℕ} (hn : 1 ≤ n)
    {k : ℕ} (hmax : ∀ m : ℕ, m.choose 8 ≤ n → m ≤ k) : 8 ≤ k := by
  have h1 : (8 : ℕ).choose 8 ≤ n := by
    have : (8 : ℕ).choose 8 = 1 := by decide
    omega
  exact hmax 8 h1

lemma leftover_lt_succ {n k : ℕ} (hmax : ∀ m : ℕ, m.choose 8 ≤ n → m ≤ k) :
    n < (k + 1).choose 8 := by
  by_contra hge
  have : (k + 1).choose 8 ≤ n := Nat.not_lt.mp hge
  have := hmax (k + 1) this
  omega

/-- Adding a binomial `k.choose 8` to a 246-representation yields a 2468-representation. -/
lemma A306477_add_choose8 {r a b c d k : ℕ} (ha : 2 ≤ a)
    (hd : d < 8)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = r) :
    A306477 (k.choose 8 + r) > 0 := by
  have hd0 : d.choose 8 = 0 := Nat.choose_eq_zero_of_lt hd
  refine A306477_pos_of_abcd (a := a) (b := b) (c := c) (d := k) ha ?_
  omega

/-- Increment via decreasing the 6-index: `a = (c-1).choose 5 + 1`. -/
lemma A306477_succ_of_a_choose5 {n a b c d : ℕ} (ha : 2 ≤ a) (hc : 1 ≤ c)
    (haeq : a = (c - 1).choose 5 + 1)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 := by
  refine A306477_pos_of_abcd (a := a + 1) (b := b) (c := c - 1) (d := d) (by omega) ?_
  have h2 : (a + 1).choose 2 = a.choose 2 + a := choose_two_succ a
  have h6 : c.choose 6 = (c - 1).choose 5 + (c - 1).choose 6 := by
    have := Nat.choose_succ_succ' (c - 1) 5
    rwa [Nat.sub_add_cancel hc] at this
  omega

/-- Increment via decreasing the 8-index: `a = (d-1).choose 7 + 1`. -/
lemma A306477_succ_of_a_choose7 {n a b c d : ℕ} (ha : 2 ≤ a) (hd : 1 ≤ d)
    (haeq : a = (d - 1).choose 7 + 1)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 := by
  refine A306477_pos_of_abcd (a := a + 1) (b := b) (c := c) (d := d - 1) (by omega) ?_
  have h2 : (a + 1).choose 2 = a.choose 2 + a := choose_two_succ a
  have h8 : d.choose 8 = (d - 1).choose 7 + (d - 1).choose 8 := by
    have := Nat.choose_succ_succ' (d - 1) 7
    rwa [Nat.sub_add_cancel hd] at this
  omega


lemma sub_choose8_lt {n k : ℕ} (hk : 8 ≤ k) (hle : k.choose 8 ≤ n) :
    n - k.choose 8 < n := by
  have hpos : 0 < k.choose 8 := Nat.choose_pos hk
  omega

/-- If `n-1` has an easy representation then `n` is representable. -/
lemma A306477_of_pred_easy {n a b c d : ℕ} (hn : n > 0)
    (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n - 1)
    (heasy : b < 4 ∨ c < 6 ∨ d < 8) :
    A306477 n > 0 := by
  have : n = (n - 1) + 1 := by omega
  rw [this]
  exact A306477_succ_of_easy ha h heasy

/-- Pascal identity at the predecessor index. -/
lemma choose8_pascal {k : ℕ} (hk : 1 ≤ k) :
    k.choose 8 = (k - 1).choose 8 + (k - 1).choose 7 := by
  have := choose_succ_eight (k - 1)
  rwa [Nat.sub_add_cancel hk] at this

/-- Increment `n` using any of the local increment lemmas. -/
lemma A306477_succ_of_local {n a b c d : ℕ} (ha : 2 ≤ a)
    (h : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n)
    (hinc : b < 4 ∨ c < 6 ∨ d < 8 ∨
      (1 ≤ b ∧ a = (b - 1).choose 3 + 1) ∨
      (1 ≤ c ∧ a = (c - 1).choose 5 + 1) ∨
      (1 ≤ d ∧ a = (d - 1).choose 7 + 1) ∨
      (c = 7 ∧ d = 8)) :
    A306477 (n + 1) > 0 := by
  rcases hinc with heasy | heasy | heasy | hb | hc | hd | h78
  · exact A306477_succ_of_easy ha h (Or.inl heasy)
  · exact A306477_succ_of_easy ha h (Or.inr (Or.inl heasy))
  · exact A306477_succ_of_easy ha h (Or.inr (Or.inr heasy))
  · exact A306477_succ_of_a_choose3 ha hb.1 hb.2 h
  · exact A306477_succ_of_a_choose5 ha hc.1 hc.2 h
  · exact A306477_succ_of_a_choose7 ha hd.1 hd.2 h
  · exact A306477_succ_of_c7_d8 ha (by rw [h78.1, h78.2] at h; exact h)

lemma choose8_eight : (8 : ℕ).choose 8 = 1 := by decide
lemma choose8_nine : (9 : ℕ).choose 8 = 9 := by decide
lemma choose8_ten : (10 : ℕ).choose 8 = 45 := by decide
lemma choose2_ten : (10 : ℕ).choose 2 = 45 := by decide
lemma choose2_two : (2 : ℕ).choose 2 = 1 := by decide
lemma choose2_three : (3 : ℕ).choose 2 = 3 := by decide
lemma choose4_five : (5 : ℕ).choose 4 = 5 := by decide
lemma choose6_seven : (7 : ℕ).choose 6 = 7 := by decide

/-- `9 = C(5,2) + C(4,4)` wait `10`, actually `9 = C(3,2)+C(5,4)+C(6,6)`. -/
lemma nine_as_246 :
    (3 : ℕ).choose 2 + (5 : ℕ).choose 4 + (6 : ℕ).choose 6 = 9 := by decide

/-- `C(10,8) = C(10,2)`. -/
lemma choose8_ten_eq_choose2 : (10 : ℕ).choose 8 = (10 : ℕ).choose 2 := by decide

/-- Adding `1` to a 246-representation with an unused 4- or 6-slot stays 246. -/
lemma add_one_of_easy246 {a b c : ℕ} (ha : 2 ≤ a)
    (heasy : b < 4 ∨ c < 6) :
    ∃ (a' b' c' : ℕ), 2 ≤ a' ∧
      a'.choose 2 + b'.choose 4 + c'.choose 6 =
        a.choose 2 + b.choose 4 + c.choose 6 + 1 := by
  rcases heasy with hb | hc
  · refine ⟨a, (4 : ℕ), c, ha, ?_⟩
    have hb0 : b.choose 4 = 0 := Nat.choose_eq_zero_of_lt hb
    have h4 : (4 : ℕ).choose 4 = 1 := choose_four_four
    omega
  · refine ⟨a, b, (6 : ℕ), ha, ?_⟩
    have hc0 : c.choose 6 = 0 := Nat.choose_eq_zero_of_lt hc
    have h6 : (6 : ℕ).choose 6 = 1 := choose_six_six
    omega

/-- If `a = (b-1).choose 3 + 1`, then `s+1` is 246 via decreasing `b`. -/
lemma add_one_of_pascal_b {a b c : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (haeq : a = (b - 1).choose 3 + 1) :
    ∃ (a' b' c' : ℕ), 2 ≤ a' ∧
      a'.choose 2 + b'.choose 4 + c'.choose 6 =
        a.choose 2 + b.choose 4 + c.choose 6 + 1 := by
  refine ⟨(a + 1 : ℕ), (b - 1 : ℕ), c, by omega, ?_⟩
  have h2 : (a + 1).choose 2 = a.choose 2 + a := choose_two_succ a
  have h4 : b.choose 4 = (b - 1).choose 3 + (b - 1).choose 4 := by
    have := Nat.choose_succ_succ' (b - 1) 3
    rwa [Nat.sub_add_cancel hb] at this
  omega

lemma add_one_of_pascal_c {a b c : ℕ} (ha : 2 ≤ a) (hc : 1 ≤ c)
    (haeq : a = (c - 1).choose 5 + 1) :
    ∃ (a' b' c' : ℕ), 2 ≤ a' ∧
      a'.choose 2 + b'.choose 4 + c'.choose 6 =
        a.choose 2 + b.choose 4 + c.choose 6 + 1 := by
  refine ⟨(a + 1 : ℕ), b, (c - 1 : ℕ), by omega, ?_⟩
  have h2 : (a + 1).choose 2 = a.choose 2 + a := choose_two_succ a
  have h6 : c.choose 6 = (c - 1).choose 5 + (c - 1).choose 6 := by
    have := Nat.choose_succ_succ' (c - 1) 5
    rwa [Nat.sub_add_cancel hc] at this
  omega

/-- Reverse Pascal increment: `a = b.choose 3` and `a ≥ 3`, move `(a,b) ↦ (a-1,b+1)`. -/
lemma A306477_succ_of_rev_choose3 {n a b c d : ℕ} (ha : 2 ≤ a)
    (haeq : a = b.choose 3) (ha2 : 2 ≤ a - 1)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 := by
  have h2 : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
    have := choose_two_succ (a - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have h4 : (b + 1).choose 4 = b.choose 3 + b.choose 4 :=
    Nat.choose_succ_succ' b 3
  refine A306477_pos_of_abcd (a := a - 1) (b := b + 1) (c := c) (d := d) ha2 ?_
  omega

lemma A306477_succ_of_rev_choose5 {n a b c d : ℕ} (ha : 2 ≤ a)
    (haeq : a = c.choose 5) (ha2 : 2 ≤ a - 1)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 := by
  have h2 : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
    have := choose_two_succ (a - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have h6 : (c + 1).choose 6 = c.choose 5 + c.choose 6 :=
    Nat.choose_succ_succ' c 5
  refine A306477_pos_of_abcd (a := a - 1) (b := b) (c := c + 1) (d := d) ha2 ?_
  omega

lemma A306477_succ_of_rev_choose7 {n a b c d : ℕ} (ha : 2 ≤ a)
    (haeq : a = d.choose 7) (ha2 : 2 ≤ a - 1)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n) :
    A306477 (n + 1) > 0 := by
  have h2 : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
    have := choose_two_succ (a - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have h8 : (d + 1).choose 8 = d.choose 7 + d.choose 8 :=
    Nat.choose_succ_succ' d 7
  refine A306477_pos_of_abcd (a := a - 1) (b := b) (c := c) (d := d + 1) ha2 ?_
  omega

/-- Enlarged local increment catalog. -/
lemma A306477_succ_of_local' {n a b c d : ℕ} (ha : 2 ≤ a)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n)
    (hinc : b < 4 ∨ c < 6 ∨ d < 8 ∨
      (1 ≤ b ∧ a = (b - 1).choose 3 + 1) ∨
      (1 ≤ c ∧ a = (c - 1).choose 5 + 1) ∨
      (1 ≤ d ∧ a = (d - 1).choose 7 + 1) ∨
      (c = 7 ∧ d = 8) ∨
      (2 ≤ a - 1 ∧ a = b.choose 3) ∨
      (2 ≤ a - 1 ∧ a = c.choose 5) ∨
      (2 ≤ a - 1 ∧ a = d.choose 7)) :
    A306477 (n + 1) > 0 := by
  rcases hinc with hb | hc | hd | hb3 | hc5 | hd7 | h78 | hrb | hrc | hrd
  · exact A306477_succ_of_easy ha heq (Or.inl hb)
  · exact A306477_succ_of_easy ha heq (Or.inr (Or.inl hc))
  · exact A306477_succ_of_easy ha heq (Or.inr (Or.inr hd))
  · exact A306477_succ_of_a_choose3 ha hb3.1 hb3.2 heq
  · exact A306477_succ_of_a_choose5 ha hc5.1 hc5.2 heq
  · exact A306477_succ_of_a_choose7 ha hd7.1 hd7.2 heq
  · exact A306477_succ_of_c7_d8 ha (by rw [h78.1, h78.2] at heq; exact heq)
  · exact A306477_succ_of_rev_choose3 ha hrb.2 hrb.1 heq
  · exact A306477_succ_of_rev_choose5 ha hrc.2 hrc.1 heq
  · exact A306477_succ_of_rev_choose7 ha hrd.2 hrd.1 heq

/-- A number admits a 246-representation. -/
def Is246 (m : ℕ) : Prop :=
  ∃ (a b c : ℕ), 2 ≤ a ∧ a.choose 2 + b.choose 4 + c.choose 6 = m

lemma A306477_of_is246 {m : ℕ} (h : Is246 m) : A306477 m > 0 := by
  obtain ⟨a, b, c, ha, heq⟩ := h
  have hd0 : (0 : ℕ).choose 8 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  exact A306477_pos_of_abcd (a := a) (b := b) (c := c) (d := 0) ha (by omega)

lemma A306477_of_choose8_add_is246 {n t : ℕ} (ht : t.choose 8 ≤ n)
    (h : Is246 (n - t.choose 8)) : A306477 n > 0 := by
  obtain ⟨a, b, c, ha, heq⟩ := h
  have hd0 : (0 : ℕ).choose 8 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hrep : a.choose 2 + b.choose 4 + c.choose 6 + (0 : ℕ).choose 8 =
      n - t.choose 8 := by omega
  have hadd := A306477_add_choose8 (r := n - t.choose 8) (a := a) (b := b)
      (c := c) (d := 0) (k := t) ha (by omega) hrep
  have : t.choose 8 + (n - t.choose 8) = n := Nat.add_sub_cancel' ht
  rwa [this] at hadd

lemma choose8_le_of_sub {n k i : ℕ} (hle : k.choose 8 ≤ n) :
    (k - i).choose 8 ≤ n := by
  have : (k - i).choose 8 ≤ k.choose 8 :=
    Nat.choose_le_choose 8 (Nat.sub_le k i)
  omega

lemma is246_add_one_of_easy {a b c : ℕ} (ha : 2 ≤ a)
    (heasy : b < 4 ∨ c < 6) :
    Is246 (a.choose 2 + b.choose 4 + c.choose 6 + 1) := by
  obtain ⟨a', b', c', ha', hsum⟩ := add_one_of_easy246 ha heasy
  exact ⟨a', b', c', ha', hsum⟩

lemma is246_add_one_of_pascal {a b c : ℕ} (ha : 2 ≤ a)
    (hp : (1 ≤ b ∧ a = (b - 1).choose 3 + 1) ∨
          (1 ≤ c ∧ a = (c - 1).choose 5 + 1)) :
    Is246 (a.choose 2 + b.choose 4 + c.choose 6 + 1) := by
  rcases hp with ⟨hb, haeq⟩ | ⟨hc, haeq⟩
  · obtain ⟨a', b', c', ha', hsum⟩ := add_one_of_pascal_b ha hb haeq
    exact ⟨a', b', c', ha', hsum⟩
  · obtain ⟨a', b', c', ha', hsum⟩ := add_one_of_pascal_c ha hc haeq
    exact ⟨a', b', c', ha', hsum⟩

/-- The local increment disjunction. -/
def LocalInc (a b c d : ℕ) : Prop :=
  b < 4 ∨ c < 6 ∨ d < 8 ∨
    (1 ≤ b ∧ a = (b - 1).choose 3 + 1) ∨
    (1 ≤ c ∧ a = (c - 1).choose 5 + 1) ∨
    (1 ≤ d ∧ a = (d - 1).choose 7 + 1) ∨
    (c = 7 ∧ d = 8) ∨
    (2 ≤ a - 1 ∧ a = b.choose 3) ∨
    (2 ≤ a - 1 ∧ a = c.choose 5) ∨
    (2 ≤ a - 1 ∧ a = d.choose 7)

lemma localInc_succ {n a b c d : ℕ} (ha : 2 ≤ a)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = n)
    (hinc : LocalInc a b c d) :
    A306477 (n + 1) > 0 :=
  A306477_succ_of_local' ha heq hinc

lemma not_is246_of_min_d {m a b c d : ℕ} (ha : 2 ≤ a) (hd : 8 ≤ d)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = m)
    (hnot : ¬ Is246 m) : True := trivial

/-- Pascal in the right-index form: `k.choose 8 * 8 = k.choose 7 * (k - 7)`. -/
lemma choose8_mul_eight (k : ℕ) (_hk : 7 ≤ k) :
    k.choose 8 * 8 = k.choose 7 * (k - 7) := by
  simpa [Nat.succ_eq_add_one] using Nat.choose_succ_right_eq k 7

/-- For `k ≥ 24` we have `2 * k.choose 7 < k.choose 8`. -/
lemma two_mul_choose7_lt_choose8 {k : ℕ} (hk : 24 ≤ k) :
    2 * k.choose 7 < k.choose 8 := by
  have hk7 : 7 ≤ k := by omega
  have hmul := choose8_mul_eight k hk7
  have hpos : 0 < k.choose 7 := Nat.choose_pos (by omega)
  have h16 : 16 < k - 7 := by omega
  have hmul16 : 16 * k.choose 7 < (k - 7) * k.choose 7 :=
    Nat.mul_lt_mul_of_pos_right h16 hpos
  have : 2 * k.choose 7 * 8 < k.choose 8 * 8 := by
    calc
      2 * k.choose 7 * 8 = 16 * k.choose 7 := by ring
      _ < (k - 7) * k.choose 7 := hmul16
      _ = k.choose 7 * (k - 7) := by ring
      _ = k.choose 8 * 8 := hmul.symm
  exact Nat.lt_of_mul_lt_mul_right this

/-- For `k ≥ 21`, `k.choose 7 < (k - 1).choose 8`. -/
lemma choose7_lt_pred_choose8 {k : ℕ} (hk : 21 ≤ k) :
    k.choose 7 < (k - 1).choose 8 := by
  have hmul1 := choose8_mul_eight (k - 1) (by omega)
  have hsub : k - 1 - 7 = k - 8 := by omega
  rw [hsub] at hmul1
  have h7pas : k.choose 7 = (k - 1).choose 6 + (k - 1).choose 7 := by
    have := Nat.choose_succ_succ' (k - 1) 6
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at this
  have h6 : (k - 1).choose 6 * (k - 7) = (k - 1).choose 7 * 7 := by
    have h := Nat.choose_succ_right_eq (k - 1) 6
    have : (k - 1) - 6 = k - 7 := by omega
    rw [this] at h
    linarith
  have hpos6 : 0 < (k - 1).choose 6 := Nat.choose_pos (by omega)
  have hpos7 : 0 < (k - 1).choose 7 := Nat.choose_pos (by omega)
  have hprod : 56 < (k - 7) * (k - 16) := by
    have : k - 7 ≥ 14 := by omega
    have : k - 16 ≥ 5 := by omega
    nlinarith
  -- `8 * C(k-1,6) < C(k-1,7) * (k-16)`
  have hmain : 8 * (k - 1).choose 6 < (k - 1).choose 7 * (k - 16) := by
    have : 56 * (k - 1).choose 6 < (k - 7) * (k - 16) * (k - 1).choose 6 :=
      Nat.mul_lt_mul_of_pos_right hprod hpos6
    have : 8 * 7 * (k - 1).choose 6 < (k - 16) * ((k - 1).choose 6 * (k - 7)) := by
      convert this using 1 <;> ring
    have : 8 * 7 * (k - 1).choose 6 < (k - 16) * ((k - 1).choose 7 * 7) := by
      rwa [h6] at this
    have : 8 * (k - 1).choose 6 * 7 < (k - 1).choose 7 * (k - 16) * 7 := by
      convert this using 1 <;> ring
    exact Nat.lt_of_mul_lt_mul_right this
  have : 8 * k.choose 7 < 8 * (k - 1).choose 8 := by
    rw [h7pas]
    have : 8 * ((k - 1).choose 6 + (k - 1).choose 7) =
        8 * (k - 1).choose 6 + 8 * (k - 1).choose 7 := by ring
    rw [this]
    have : 8 * (k - 1).choose 8 = (k - 1).choose 7 * (k - 8) := by
      linarith [hmul1]
    rw [this]
    have hk8 : k - 8 = (k - 16) + 8 := by omega
    rw [hk8, Nat.mul_add]
    linarith [hmain]
  exact Nat.lt_of_mul_lt_mul_left this

/-- A 2468-representation of `m` with no `C8` is a 246-representation. -/
lemma is246_of_abcd_lt {m a b c d : ℕ} (ha : 2 ≤ a) (hd : d < 8)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = m) :
    Is246 m :=
  ⟨a, b, c, ha, by
    have : d.choose 8 = 0 := Nat.choose_eq_zero_of_lt hd
    omega⟩

/-- If `m < k.choose 8` then any 8-index in a representation of `m` is `< k`. -/
lemma choose8_index_lt_of_lt {m a b c d k : ℕ}
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + d.choose 8 = m)
    (hm : m < k.choose 8) : d < k := by
  by_contra hge
  have : k.choose 8 ≤ d.choose 8 := Nat.choose_le_choose 8 (Nat.le_of_not_lt hge)
  have : k.choose 8 ≤ m := by omega
  omega

lemma is246_one : Is246 1 :=
  ⟨(2 : ℕ), 0, 0, by omega, by decide⟩

lemma choose11_eight : (11 : ℕ).choose 8 = 165 := by decide
lemma choose12_eight : (12 : ℕ).choose 8 = 495 := by decide
lemma choose13_eight : (13 : ℕ).choose 8 = 1287 := by decide

lemma lt_of_choose8_lt {d e : ℕ} (h : d.choose 8 < e.choose 8) : d < e := by
  by_contra hge
  have : e.choose 8 ≤ d.choose 8 := Nat.choose_le_choose 8 (Nat.le_of_not_lt hge)
  omega

lemma choose7_le_choose8 {k : ℕ} (hk : 15 ≤ k) : k.choose 7 ≤ k.choose 8 := by
  have hmul := choose8_mul_eight k (by omega)
  have : k.choose 7 * 8 ≤ k.choose 7 * (k - 7) :=
    Nat.mul_le_mul_left _ (by omega)
  have : k.choose 7 * 8 ≤ k.choose 8 * 8 := by
    rwa [← hmul] at this
  exact Nat.le_of_mul_le_mul_right this (by decide)


/-- `s + 1` is 2468 when `s` is 246, via leftover `C(8,8) = 1`. -/
lemma A306477_succ_of_is246 {s : ℕ} (hs : Is246 s) : A306477 (s + 1) > 0 := by
  have hle : (8 : ℕ).choose 8 ≤ s + 1 := by
    have : (8 : ℕ).choose 8 = 1 := choose8_eight
    omega
  have hsub : s + 1 - (8 : ℕ).choose 8 = s := by
    have : (8 : ℕ).choose 8 = 1 := choose8_eight
    omega
  exact A306477_of_choose8_add_is246 hle (hsub ▸ hs)

lemma choose14_eight : (14 : ℕ).choose 8 = 3003 := by decide
lemma choose15_eight : (15 : ℕ).choose 8 = 6435 := by decide
lemma choose16_eight : (16 : ℕ).choose 8 = 12870 := by decide

lemma k_mul_succ_le_two_pred {k : ℕ} (hk : 27 ≤ k) :
    k * (k + 1) ≤ 2 * (k - 7) * (k - 8) := by
  rcases Nat.exists_eq_add_of_le hk with ⟨t, rfl⟩
  have h7 : 27 + t - 7 = 20 + t := by omega
  have h8 : 27 + t - 8 = 19 + t := by omega
  rw [h7, h8]
  nlinarith

lemma two_mul_pred_choose8 {k : ℕ} (hk : 27 ≤ k) :
    (k + 1).choose 8 ≤ 2 * (k - 1).choose 8 := by
  have hk1 : 1 ≤ k := by omega
  have h1 : k.choose 8 * (k + 1) = (k + 1).choose 8 * (k - 7) := by
    have h := Nat.choose_mul_succ_eq k 8
    have he : k + 1 - 8 = k - 7 := by omega
    rw [he] at h
    exact h
  have h2 : (k - 1).choose 8 * k = k.choose 8 * (k - 8) := by
    have h := Nat.choose_mul_succ_eq (k - 1) 8
    rw [Nat.sub_add_cancel hk1] at h
    exact h
  have hfac := k_mul_succ_le_two_pred hk
  have hpos7 : 0 < k - 7 := by omega
  have hpos8 : 0 < k - 8 := by omega
  have hpos : 0 < (k - 7) * (k - 8) := Nat.mul_pos hpos7 hpos8
  have hlhs :
      (k + 1).choose 8 * ((k - 7) * (k - 8)) =
        (k - 1).choose 8 * (k * (k + 1)) := by
    calc
      (k + 1).choose 8 * ((k - 7) * (k - 8))
          = ((k + 1).choose 8 * (k - 7)) * (k - 8) := by ring
      _ = (k.choose 8 * (k + 1)) * (k - 8) := by rw [← h1]
      _ = (k.choose 8 * (k - 8)) * (k + 1) := by ring
      _ = ((k - 1).choose 8 * k) * (k + 1) := by rw [← h2]
      _ = (k - 1).choose 8 * (k * (k + 1)) := by ring
  have hmul : (k + 1).choose 8 * ((k - 7) * (k - 8)) ≤
      2 * (k - 1).choose 8 * ((k - 7) * (k - 8)) := by
    rw [hlhs]
    have hassoc : 2 * (k - 1).choose 8 * ((k - 7) * (k - 8)) =
        (k - 1).choose 8 * (2 * (k - 7) * (k - 8)) := by ring
    rw [hassoc]
    exact Nat.mul_le_mul_left _ hfac
  exact Nat.le_of_mul_le_mul_right hmul hpos

lemma leftover_pred_lt_of_ge_27 {n k : ℕ} (hk : 27 ≤ k)
    (hn : n < (k + 1).choose 8) (hle : (k - 1).choose 8 ≤ n) :
    n - (k - 1).choose 8 < (k - 1).choose 8 := by
  have := two_mul_pred_choose8 hk
  omega

lemma leftover_lt_pred_choose8 {n k : ℕ} (hk : 21 ≤ k)
    (hmax : n < (k + 1).choose 8) (hle : k.choose 8 ≤ n) :
    n - k.choose 8 < (k - 1).choose 8 :=
  lt_trans
    (by
      have hs : (k + 1).choose 8 = k.choose 8 + k.choose 7 := choose_succ_eight k
      omega)
    (choose7_lt_pred_choose8 hk)

lemma is246_add_two_of_a2 {b c : ℕ} :
    Is246 ((2 : ℕ).choose 2 + b.choose 4 + c.choose 6 + 2) := by
  refine ⟨(3 : ℕ), b, c, by omega, ?_⟩
  have h2 : (2 : ℕ).choose 2 = 1 := choose2_two
  have h3 : (3 : ℕ).choose 2 = 3 := choose2_three
  omega

lemma choose8_strict_mono {m n : ℕ} (h : m < n) (hm : 8 ≤ m) :
    m.choose 8 < n.choose 8 := by
  have hstep : ∀ t, 8 ≤ t → t.choose 8 < (t + 1).choose 8 := by
    intro t ht
    have hs : (t + 1).choose 8 = t.choose 8 + t.choose 7 := choose_succ_eight t
    have hp : 0 < t.choose 7 := Nat.choose_pos (by omega)
    omega
  have hle : m + 1 ≤ n := h
  have : m.choose 8 < (m + 1).choose 8 := hstep m hm
  have : (m + 1).choose 8 ≤ n.choose 8 := Nat.choose_le_choose 8 hle
  omega

lemma is246_sub_seven_of_c7 {a b : ℕ} (ha : 2 ≤ a) :
    Is246 (a.choose 2 + b.choose 4 + (7 : ℕ).choose 6 - 7) := by
  have h7 : (7 : ℕ).choose 6 = 7 := choose6_seven
  refine ⟨a, b, (0 : ℕ), ha, ?_⟩
  have : (0 : ℕ).choose 6 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  omega

lemma A306477_add_two_of_c7 {a b : ℕ} (ha : 2 ≤ a) :
    A306477 (a.choose 2 + b.choose 4 + (7 : ℕ).choose 6 + 2) > 0 := by
  let s := a.choose 2 + b.choose 4 + (7 : ℕ).choose 6
  have h9 : (9 : ℕ).choose 8 = 9 := choose8_nine
  have hle : (9 : ℕ).choose 8 ≤ s + 2 := by
    have : (7 : ℕ).choose 6 = 7 := choose6_seven
    omega
  have hsub : s + 2 - (9 : ℕ).choose 8 = s - 7 := by omega
  have hs7 : Is246 (s - 7) := by
    simpa [s] using is246_sub_seven_of_c7 (a := a) (b := b) ha
  exact A306477_of_choose8_add_is246 hle (hsub ▸ hs7)

lemma A306477_add_two_of_a8 {b c : ℕ} :
    A306477 ((8 : ℕ).choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  -- reverse Pascal on the 8-index: (8, b, c, 8) ↦ (7, b, c, 9)
  refine A306477_pos_of_abcd (a := 7) (b := b) (c := c) (d := 9) (by omega) ?_
  have h2 : (8 : ℕ).choose 2 = (7 : ℕ).choose 2 + 7 := by decide
  have h8 : (9 : ℕ).choose 8 = (8 : ℕ).choose 7 + (8 : ℕ).choose 8 := by decide
  have h87 : (8 : ℕ).choose 7 = 8 := by decide
  have h88 : (8 : ℕ).choose 8 = 1 := choose8_eight
  have h72 : (7 : ℕ).choose 2 = 21 := by decide
  omega



lemma A306477_add_two_of_a5 {b c : ℕ} :
    A306477 ((5 : ℕ).choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  -- leftover 9: C(5,2)+C(b,4)+C(c,6)-7 = C(3,2)+C(b,4)+C(c,6)
  let s := (5 : ℕ).choose 2 + b.choose 4 + c.choose 6
  have h9 : (9 : ℕ).choose 8 = 9 := choose8_nine
  have h52 : (5 : ℕ).choose 2 = 10 := by decide
  have hle : (9 : ℕ).choose 8 ≤ s + 2 := by omega
  have hsub : s + 2 - (9 : ℕ).choose 8 = (3 : ℕ).choose 2 + b.choose 4 + c.choose 6 := by
    have h32 : (3 : ℕ).choose 2 = 3 := choose2_three
    omega
  have hs : Is246 ((3 : ℕ).choose 2 + b.choose 4 + c.choose 6) :=
    ⟨(3 : ℕ), b, c, by omega, rfl⟩
  exact A306477_of_choose8_add_is246 hle (hsub ▸ hs)

/-- If `s` is 246 then `s + 2` is 2468, except possibly a residual
handled via leftovers in the main induction. -/
lemma A306477_add_two_of_is246_easy {a b c : ℕ} (ha : 2 ≤ a)
    (heasy : a = 2 ∨ a = 5 ∨ a = 8 ∨ c = 7 ∨ b < 4 ∨ c < 6) :
    A306477 (a.choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  rcases heasy with h | h | h | h | h | h
  · subst h
    exact A306477_of_is246 (is246_add_two_of_a2 (b := b) (c := c))
  · subst h
    exact A306477_add_two_of_a5 (b := b) (c := c)
  · subst h
    exact A306477_add_two_of_a8 (b := b) (c := c)
  · subst h
    exact A306477_add_two_of_c7 ha
  · have h1 : Is246 (a.choose 2 + b.choose 4 + c.choose 6 + 1) :=
      is246_add_one_of_easy ha (Or.inl h)
    exact A306477_succ_of_is246 h1
  · have h1 : Is246 (a.choose 2 + b.choose 4 + c.choose 6 + 1) :=
      is246_add_one_of_easy ha (Or.inr h)
    exact A306477_succ_of_is246 h1

lemma choose17_eight : (17 : ℕ).choose 8 = 24310 := by decide
lemma choose18_eight : (18 : ℕ).choose 8 = 43758 := by decide
lemma choose19_eight : (19 : ℕ).choose 8 = 75582 := by decide
lemma choose20_eight : (20 : ℕ).choose 8 = 125970 := by decide
lemma choose21_eight : (21 : ℕ).choose 8 = 203490 := by decide
lemma choose22_eight : (22 : ℕ).choose 8 = 319770 := by decide
lemma choose23_eight : (23 : ℕ).choose 8 = 490314 := by decide
lemma choose24_eight : (24 : ℕ).choose 8 = 735471 := by decide
lemma choose25_eight : (25 : ℕ).choose 8 = 1081575 := by decide

/-- Try leftover at a concrete index `t` when the binomial is known. -/
lemma try_num_leftover {n t ct : ℕ} (hteq : t.choose 8 = ct) (hle : ct ≤ n)
    (h : Is246 (n - ct)) : A306477 n > 0 := by
  have : t.choose 8 ≤ n := by omega
  have h' : Is246 (n - t.choose 8) := by simpa [hteq] using h
  exact A306477_of_choose8_add_is246 this h'

lemma choose8_pos_of_ge {k : ℕ} (hk : 8 ≤ k) : 0 < k.choose 8 :=
  Nat.choose_pos hk

lemma choose8_lt_succ {k : ℕ} (hk : 8 ≤ k) : k.choose 8 < (k + 1).choose 8 := by
  have hs : (k + 1).choose 8 = k.choose 8 + k.choose 7 := choose_succ_eight k
  have : 0 < k.choose 7 := Nat.choose_pos (by omega)
  omega

lemma choose8_pred_lt {k : ℕ} (hk : 9 ≤ k) : (k - 1).choose 8 < k.choose 8 := by
  have h1 : 8 ≤ k - 1 := by omega
  have := choose8_lt_succ h1
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)] at this

lemma is246_zero_false : ¬ Is246 0 := by
  intro ⟨a, b, c, ha, h⟩
  have hpos : 0 < a.choose 2 := Nat.choose_pos ha
  omega

/-- Increment `C(k,8) + s` by one when the 246-part together with `k` is locally incrementable. -/
lemma A306477_of_localInc_k {s a b c k : ℕ} (ha : 2 ≤ a)
    (hs : a.choose 2 + b.choose 4 + c.choose 6 = s)
    (hinc : LocalInc a b c k) :
    A306477 (k.choose 8 + s + 1) > 0 := by
  have heq : a.choose 2 + b.choose 4 + c.choose 6 + k.choose 8 = k.choose 8 + s := by omega
  have := localInc_succ ha heq hinc
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

lemma is246_pos {s : ℕ} (hs : Is246 s) : 0 < s := by
  obtain ⟨a, b, c, ha, heq⟩ := hs
  have : 0 < a.choose 2 := Nat.choose_pos ha
  omega

/-- The 8-index of a positive 2468-representation of `d.choose 8` is strictly smaller than `d`. -/
lemma choose8_rep_index_lt {a b c e d : ℕ} (ha : 2 ≤ a) (hd : 8 ≤ d)
    (heq : a.choose 2 + b.choose 4 + c.choose 6 + e.choose 8 = d.choose 8) :
    e < d := by
  have hpos : 0 < a.choose 2 := Nat.choose_pos ha
  have : e.choose 8 < d.choose 8 := by omega
  exact lt_of_choose8_lt this

/-- Reverse-Pascal +2: `a + 1 = b.choose 3`. -/
lemma A306477_add_two_of_rev_b {a b c : ℕ} (ha : 2 ≤ a) (ha2 : 2 ≤ a - 1)
    (haeq : a + 1 = b.choose 3) :
    A306477 (a.choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  refine A306477_of_is246 ⟨a - 1, b + 1, c, ha2, ?_⟩
  have h2 : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
    have := choose_two_succ (a - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have h4 : (b + 1).choose 4 = b.choose 3 + b.choose 4 :=
    Nat.choose_succ_succ' b 3
  omega

/-- Pascal-style +2: `a = (b-1).choose 3 + 2`. -/
lemma A306477_add_two_of_pas_b {a b c : ℕ} (ha : 2 ≤ a) (hb : 1 ≤ b)
    (haeq : a = (b - 1).choose 3 + 2) :
    A306477 (a.choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  refine A306477_of_is246 ⟨a + 1, b - 1, c, by omega, ?_⟩
  have h2 : (a + 1).choose 2 = a.choose 2 + a := choose_two_succ a
  have h4 : b.choose 4 = (b - 1).choose 3 + (b - 1).choose 4 := by
    have := Nat.choose_succ_succ' (b - 1) 3
    rwa [Nat.sub_add_cancel hb] at this
  omega

/-- Reverse-Pascal +2 on the 6-index. -/
lemma A306477_add_two_of_rev_c {a b c : ℕ} (ha : 2 ≤ a) (ha2 : 2 ≤ a - 1)
    (haeq : a + 1 = c.choose 5) :
    A306477 (a.choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  refine A306477_of_is246 ⟨a - 1, b, c + 1, ha2, ?_⟩
  have h2 : a.choose 2 = (a - 1).choose 2 + (a - 1) := by
    have := choose_two_succ (a - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ a)] at this
  have h6 : (c + 1).choose 6 = c.choose 5 + c.choose 6 :=
    Nat.choose_succ_succ' c 5
  omega

/-- Pascal-style +2 on the 6-index. -/
lemma A306477_add_two_of_pas_c {a b c : ℕ} (ha : 2 ≤ a) (hc : 1 ≤ c)
    (haeq : a = (c - 1).choose 5 + 2) :
    A306477 (a.choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  refine A306477_of_is246 ⟨a + 1, b, c - 1, by omega, ?_⟩
  have h2 : (a + 1).choose 2 = a.choose 2 + a := choose_two_succ a
  have h6 : c.choose 6 = (c - 1).choose 5 + (c - 1).choose 6 := by
    have := Nat.choose_succ_succ' (c - 1) 5
    rwa [Nat.sub_add_cancel hc] at this
  omega

/-- Extended catalog for `s + 2`. -/
lemma A306477_add_two_of_is246_more {a b c : ℕ} (ha : 2 ≤ a)
    (h : a = 2 ∨ a = 5 ∨ a = 8 ∨ c = 7 ∨ b < 4 ∨ c < 6 ∨
      (2 ≤ a - 1 ∧ a + 1 = b.choose 3) ∨
      (1 ≤ b ∧ a = (b - 1).choose 3 + 2) ∨
      (2 ≤ a - 1 ∧ a + 1 = c.choose 5) ∨
      (1 ≤ c ∧ a = (c - 1).choose 5 + 2)) :
    A306477 (a.choose 2 + b.choose 4 + c.choose 6 + 2) > 0 := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact A306477_add_two_of_is246_easy ha (Or.inl h)
  · exact A306477_add_two_of_is246_easy ha (Or.inr (Or.inl h))
  · exact A306477_add_two_of_is246_easy ha (Or.inr (Or.inr (Or.inl h)))
  · exact A306477_add_two_of_is246_easy ha (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact A306477_add_two_of_is246_easy ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact A306477_add_two_of_is246_easy ha (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact A306477_add_two_of_rev_b ha h.1 h.2
  · exact A306477_add_two_of_pas_b ha h.1 h.2
  · exact A306477_add_two_of_rev_c ha h.1 h.2
  · exact A306477_add_two_of_pas_c ha h.1 h.2

/-- Try leftover at a numeric index, given a proof of the binomial value. -/
lemma leftover_num {n t ct : ℕ} (hteq : t.choose 8 = ct) (hle : ct ≤ n)
    (h : Is246 (n - ct)) : A306477 n > 0 :=
  try_num_leftover hteq hle h


set_option maxHeartbeats 400000 in
lemma A306477_of_le_30_of_ge_1 (n : ℕ) (hn : n > 0) (hL : 1 ≤ n) (hN : n ≤ 30) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 2) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 2) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 4) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 6) (c := 0) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_60_of_ge_31 (n : ℕ) (hn : n > 0) (hL : 31 ≤ n) (hN : n ≤ 60) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 6) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 0) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 6) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 5) (c := 0) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_90_of_ge_61 (n : ℕ) (hn : n > 0) (hL : 61 ≤ n) (hN : n ≤ 90) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 11) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 8) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 6) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 7) (c := 0) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_120_of_ge_91 (n : ℕ) (hn : n > 0) (hL : 91 ≤ n) (hN : n ≤ 120) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 14) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 8) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 6) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 7) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 0) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 0) (c := 0) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_150_of_ge_121 (n : ℕ) (hn : n > 0) (hL : 121 ≤ n) (hN : n ≤ 150) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 16) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 4) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 2) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 2) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 9) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 2) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 4) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 4) (c := 0) (d := 9) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 0) (c := 9) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_180_of_ge_151 (n : ℕ) (hn : n > 0) (hL : 151 ≤ n) (hN : n ≤ 180) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 17) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 16) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 9) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 0) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 5) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 5) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 6) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 7) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 5) (c := 9) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_210_of_ge_181 (n : ℕ) (hn : n > 0) (hL : 181 ≤ n) (hN : n ≤ 210) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 11) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 5) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 7) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 5) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 4) (c := 8) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 15) (b := 8) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 7) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 0) (c := 0) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_240_of_ge_211 (n : ℕ) (hn : n > 0) (hL : 211 ≤ n) (hN : n ≤ 240) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 21) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 14) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 5) (b := 10) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 6) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 6) (c := 10) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 8) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 7) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 6) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 6) (c := 10) (d := 0) (by omega) (by decide)

set_option maxHeartbeats 400000 in
lemma A306477_of_le_270_of_ge_241 (n : ℕ) (hn : n > 0) (hL : 241 ≤ n) (hN : n ≤ 270) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 19) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 4) (b := 10) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 8) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 8) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 8) (c := 0) (d := 9) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 8) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 10) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 6) (c := 9) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_300_of_ge_271 (n : ℕ) (hn : n > 0) (hL : 271 ≤ n) (hN : n ≤ 300) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 19) (b := 6) (c := 9) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 10) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 6) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 4) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 8) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 17) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 10) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 7) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 6) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 5) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_330_of_ge_301 (n : ℕ) (hn : n > 0) (hL : 301 ≤ n) (hN : n ≤ 330) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 25) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 6) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 5) (c := 8) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 7) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 5) (c := 0) (d := 9) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 6) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 9) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 0) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_360_of_ge_331 (n : ℕ) (hn : n > 0) (hL : 331 ≤ n) (hN : n ≤ 360) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 2) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 2) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 2) (b := 11) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 7) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 8) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 10) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 7) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 4) (c := 8) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_390_of_ge_361 (n : ℕ) (hn : n > 0) (hL : 361 ≤ n) (hN : n ≤ 390) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 26) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 7) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 8) (b := 11) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 6) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 6) (c := 8) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 7) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 8) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 8) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 10) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 5) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_420_of_ge_391 (n : ℕ) (hn : n > 0) (hL : 391 ≤ n) (hN : n ≤ 420) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 18) (b := 10) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 11) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 8) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 6) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 9) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 20) (b := 5) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 4) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 11) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 19) (b := 7) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 11) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 7) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_450_of_ge_421 (n : ℕ) (hn : n > 0) (hL : 421 ≤ n) (hN : n ≤ 450) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 29) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 8) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 12) (b := 11) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 21) (b := 5) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 11) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 9) (c := 8) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 8) (c := 8) (d := 9) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 0) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 4) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 7) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 7) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 7) (c := 9) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 5) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_480_of_ge_451 (n : ℕ) (hn : n > 0) (hL : 451 ≤ n) (hN : n ≤ 480) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 26) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 9) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 8) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 22) (b := 6) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 6) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 9) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 11) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 10) (b := 11) (c := 9) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 9) (c := 6) (d := 9) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 0) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 4) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 5) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 7) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 4) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 4) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 11) (b := 10) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 27) (b := 9) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 26) (b := 9) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 6) (c := 0) (d := 0) (by omega) (by decide)
set_option maxHeartbeats 400000 in
lemma A306477_of_le_510_of_ge_481 (n : ℕ) (hn : n > 0) (hL : 481 ≤ n) (hN : n ≤ 510) :
    A306477 n > 0 := by
  interval_cases n
  · exact A306477_pos_of_abcd (a := 31) (b := 6) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 6) (b := 5) (c := 11) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 11) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 11) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 11) (c := 6) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 10) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 10) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 7) (b := 5) (c := 11) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 9) (c := 10) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 18) (b := 11) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 23) (b := 10) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 13) (b := 11) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 24) (b := 10) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 4) (c := 8) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 29) (b := 5) (c := 9) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 0) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 4) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 12) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 3) (b := 12) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 7) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 5) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 5) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 0) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 28) (b := 9) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 8) (c := 0) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 30) (b := 8) (c := 6) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 31) (b := 7) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 5) (c := 7) (d := 0) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 32) (b := 5) (c := 7) (d := 8) (by omega) (by decide)
  · exact A306477_pos_of_abcd (a := 25) (b := 10) (c := 0) (d := 0) (by omega) (by decide)


lemma A306477_of_le_510 (n : ℕ) (hn : n > 0) (hN : n ≤ 510) : A306477 n > 0 := by
  by_cases h30 : n ≤ 30
  · exact A306477_of_le_30_of_ge_1 n hn (by omega) h30
  by_cases h60 : n ≤ 60
  · exact A306477_of_le_60_of_ge_31 n hn (by omega) h60
  by_cases h90 : n ≤ 90
  · exact A306477_of_le_90_of_ge_61 n hn (by omega) h90
  by_cases h120 : n ≤ 120
  · exact A306477_of_le_120_of_ge_91 n hn (by omega) h120
  by_cases h150 : n ≤ 150
  · exact A306477_of_le_150_of_ge_121 n hn (by omega) h150
  by_cases h180 : n ≤ 180
  · exact A306477_of_le_180_of_ge_151 n hn (by omega) h180
  by_cases h210 : n ≤ 210
  · exact A306477_of_le_210_of_ge_181 n hn (by omega) h210
  by_cases h240 : n ≤ 240
  · exact A306477_of_le_240_of_ge_211 n hn (by omega) h240
  by_cases h270 : n ≤ 270
  · exact A306477_of_le_270_of_ge_241 n hn (by omega) h270
  by_cases h300 : n ≤ 300
  · exact A306477_of_le_300_of_ge_271 n hn (by omega) h300
  by_cases h330 : n ≤ 330
  · exact A306477_of_le_330_of_ge_301 n hn (by omega) h330
  by_cases h360 : n ≤ 360
  · exact A306477_of_le_360_of_ge_331 n hn (by omega) h360
  by_cases h390 : n ≤ 390
  · exact A306477_of_le_390_of_ge_361 n hn (by omega) h390
  by_cases h420 : n ≤ 420
  · exact A306477_of_le_420_of_ge_391 n hn (by omega) h420
  by_cases h450 : n ≤ 450
  · exact A306477_of_le_450_of_ge_421 n hn (by omega) h450
  by_cases h480 : n ≤ 480
  · exact A306477_of_le_480_of_ge_451 n hn (by omega) h480
  by_cases h510 : n ≤ 510
  · exact A306477_of_le_510_of_ge_481 n hn (by omega) h510
  omega


lemma leftover_try {n t : ℕ} (ht : t.choose 8 ≤ n) (h : Is246 (n - t.choose 8)) :
    A306477 n > 0 :=
  A306477_of_choose8_add_is246 ht h

/-- Combine two 8-binomials by trying the leftover at the second index. -/
lemma leftover_other_c8 {n k d s : ℕ}
    (hsum : k.choose 8 + d.choose 8 + s = n) (hs : Is246 (k.choose 8 + s)) :
    A306477 n > 0 := by
  have hdle : d.choose 8 ≤ n := by
    have h1 : d.choose 8 ≤ d.choose 8 + s := Nat.le_add_right _ _
    have h2 : d.choose 8 + s ≤ k.choose 8 + d.choose 8 + s := by
      have : d.choose 8 + s ≤ k.choose 8 + (d.choose 8 + s) := Nat.le_add_left _ _
      simpa [Nat.add_assoc] using this
    have : d.choose 8 ≤ k.choose 8 + d.choose 8 + s := Nat.le_trans h1 h2
    simpa [hsum] using this
  have hsub : n - d.choose 8 = k.choose 8 + s := by omega
  exact leftover_try hdle (hsub ▸ hs)

lemma leftover_of_sum {n t s : ℕ} (ht : t.choose 8 ≤ n)
    (hsum : t.choose 8 + s = n) (hs : Is246 s) : A306477 n > 0 := by
  have : n - t.choose 8 = s := by omega
  exact leftover_try ht (this ▸ hs)

set_option maxHeartbeats 800000 in
theorem A306477_conjecture (n : ℕ) (hn : n > 0) : A306477 n > 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h510 : n ≤ 510
    · exact A306477_of_le_510 n hn h510
    have hn510 : 510 < n := Nat.not_le.mp h510
    by_cases h0 : Is246 n
    · exact A306477_of_is246 h0
    have h8v : (8 : ℕ).choose 8 = 1 := choose8_eight
    have h8le : (8 : ℕ).choose 8 ≤ n := by
      have : (8 : ℕ).choose 8 = 1 := h8v
      omega
    by_cases h1 : Is246 (n - (8 : ℕ).choose 8)
    · exact leftover_try h8le h1
    have h9v : (9 : ℕ).choose 8 = 9 := choose8_nine
    have h9le : (9 : ℕ).choose 8 ≤ n := by
      have : (9 : ℕ).choose 8 = 9 := h9v
      omega
    by_cases h9 : Is246 (n - (9 : ℕ).choose 8)
    · exact leftover_try h9le h9
    have h10v : (10 : ℕ).choose 8 = 45 := choose8_ten
    have h10le : (10 : ℕ).choose 8 ≤ n := by
      have : (10 : ℕ).choose 8 = 45 := h10v
      omega
    by_cases h10 : Is246 (n - (10 : ℕ).choose 8)
    · exact leftover_try h10le h10
    have h11v : (11 : ℕ).choose 8 = 165 := choose11_eight
    have h11le : (11 : ℕ).choose 8 ≤ n := by
      have : (11 : ℕ).choose 8 = 165 := h11v
      omega
    by_cases h11 : Is246 (n - (11 : ℕ).choose 8)
    · exact leftover_try h11le h11
    have h12v : (12 : ℕ).choose 8 = 495 := choose12_eight
    have h12le : (12 : ℕ).choose 8 ≤ n := by
      have : (12 : ℕ).choose 8 = 495 := h12v
      omega
    by_cases h12 : Is246 (n - (12 : ℕ).choose 8)
    · exact leftover_try h12le h12
    -- n-1 is representable
    have hpred := ih (n - 1) (by omega) (by omega)
    obtain ⟨a0, b0, c0, d0, ha0, heq0⟩ := exists_abcd_of_pos hpred
    by_cases hloc : LocalInc a0 b0 c0 d0
    · have hnp : n = (n - 1) + 1 := by omega
      rw [hnp]
      exact localInc_succ ha0 heq0 hloc
    obtain ⟨k, hk_le, hkmax⟩ := exists_max_choose8 n
    have hk8 : 8 ≤ k := max_choose8_ge_eight (by omega) hkmax
    by_cases hr246 : Is246 (n - k.choose 8)
    · exact leftover_try hk_le hr246
    have hk1le : (k - 1).choose 8 ≤ n := choose8_le_of_sub (i := 1) hk_le
    by_cases hkm1 : Is246 (n - (k - 1).choose 8)
    · exact leftover_try hk1le hkm1
    by_cases hz : n - k.choose 8 = 0
    · have hnC : n = k.choose 8 := by omega
      have hpas := choose8_pascal (show 1 ≤ k by omega)
      have hk13 : 13 ≤ k := by
        by_contra hlt
        have hk12 : k ≤ 12 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hlt)
        have hle : k.choose 8 ≤ (12 : ℕ).choose 8 := Nat.choose_le_choose 8 hk12
        have h495 : (12 : ℕ).choose 8 = 495 := choose12_eight
        omega
      have h7eq : n - (k - 1).choose 8 = (k - 1).choose 7 := by
        have hpos : 0 < (k - 1).choose 8 := Nat.choose_pos (by omega)
        rw [hnC, hpas]; omega
      have h7pos : 0 < (k - 1).choose 7 := Nat.choose_pos (by omega)
      have h7lt : (k - 1).choose 7 < n := by
        rw [hnC, hpas]
        have : 0 < (k - 1).choose 8 := Nat.choose_pos (by omega)
        omega
      have h7rep := ih ((k - 1).choose 7) h7lt h7pos
      obtain ⟨aa, bb, cc, dd, haa, heqa⟩ := exists_abcd_of_pos h7rep
      by_cases hdlt : dd < 8
      · exact (hkm1 (h7eq ▸ is246_of_abcd_lt haa hdlt heqa)).elim
      · have hs : Is246 (aa.choose 2 + bb.choose 4 + cc.choose 6) :=
          ⟨aa, bb, cc, haa, rfl⟩
        have hsum : (k - 1).choose 8 + dd.choose 8 +
            (aa.choose 2 + bb.choose 4 + cc.choose 6) = n := by
          have hle1 : (k - 1).choose 8 ≤ k.choose 8 :=
            Nat.choose_le_choose 8 (Nat.sub_le k 1)
          have hle2 : dd.choose 8 ≤ (k - 1).choose 7 := by omega
          omega
        by_cases hsw : Is246 ((k - 1).choose 8 + (aa.choose 2 + bb.choose 4 + cc.choose 6))
        · exact leftover_other_c8 hsum hsw
        · have hk2le : (k - 2).choose 8 ≤ n := choose8_le_of_sub (i := 2) hk_le
          by_cases hk2 : Is246 (n - (k - 2).choose 8)
          · exact leftover_try hk2le hk2
          · have h13le : (13 : ℕ).choose 8 ≤ n := by
              have : (13 : ℕ).choose 8 ≤ k.choose 8 := Nat.choose_le_choose 8 hk13
              omega
            by_cases h13 : Is246 (n - (13 : ℕ).choose 8)
            · exact leftover_try h13le h13
            · by_cases hk14 : 14 ≤ k
              · have h14le : (14 : ℕ).choose 8 ≤ n := by
                  have : (14 : ℕ).choose 8 ≤ k.choose 8 := Nat.choose_le_choose 8 hk14
                  omega
                by_cases h14 : Is246 (n - (14 : ℕ).choose 8)
                · exact leftover_num choose14_eight h14le h14
                · by_cases hk15 : 15 ≤ k
                  · have h15le : (15 : ℕ).choose 8 ≤ n := by
                      have : (15 : ℕ).choose 8 ≤ k.choose 8 := Nat.choose_le_choose 8 hk15
                      omega
                    by_cases h15 : Is246 (n - (15 : ℕ).choose 8)
                    · exact leftover_num choose15_eight h15le h15
                    · have hk2le' : (k - 3).choose 8 ≤ n :=
                        choose8_le_of_sub (i := 3) hk_le
                      by_cases hk3 : Is246 (n - (k - 3).choose 8)
                      · exact leftover_try hk2le' hk3
                      · exact leftover_try h13le h13
                  · have : k = 14 := by omega
                    have hn3003 : n = 3003 := by
                      have : (14 : ℕ).choose 8 = 3003 := choose14_eight
                      omega
                    exact (h0 ⟨(78 : ℕ), 0, 0, by omega, by
                      rw [hn3003]; decide⟩).elim
              · have hk13eq : k = 13 := by omega
                have hn1287 : n = 1287 := by
                  have : (13 : ℕ).choose 8 = 1287 := choose13_eight
                  omega
                exact (h0 ⟨(51 : ℕ), 5, 7, by omega, by
                  rw [hn1287]; decide⟩).elim
    · have hrpos : 0 < n - k.choose 8 := Nat.pos_of_ne_zero hz
      have hrlt : n - k.choose 8 < n := sub_choose8_lt hk8 hk_le
      have hrep := ih (n - k.choose 8) hrlt hrpos
      obtain ⟨aa, bb, cc, dd, haa, heqa⟩ := exists_abcd_of_pos hrep
      by_cases hdlt : dd < 8
      · exact (hr246 (is246_of_abcd_lt haa hdlt heqa)).elim
      · have hs : Is246 (aa.choose 2 + bb.choose 4 + cc.choose 6) :=
          ⟨aa, bb, cc, haa, rfl⟩
        have hsum : k.choose 8 + dd.choose 8 +
            (aa.choose 2 + bb.choose 4 + cc.choose 6) = n := by omega
        by_cases hsw : Is246 (k.choose 8 + (aa.choose 2 + bb.choose 4 + cc.choose 6))
        · exact leftover_other_c8 hsum hsw
        · have hk2le : (k - 2).choose 8 ≤ n := choose8_le_of_sub (i := 2) hk_le
          by_cases hk2 : Is246 (n - (k - 2).choose 8)
          · exact leftover_try hk2le hk2
          · have hddle : dd.choose 8 ≤ n := by omega
            by_cases hds : Is246 (n - dd.choose 8)
            · exact leftover_try hddle hds
            · have h13v : (13 : ℕ).choose 8 = 1287 := choose13_eight
              by_cases h13le : (13 : ℕ).choose 8 ≤ n
              · by_cases h13 : Is246 (n - (13 : ℕ).choose 8)
                · exact leftover_try h13le h13
                · have h14le' : (14 : ℕ).choose 8 ≤ n := by
                    have : (14 : ℕ).choose 8 = 3003 := choose14_eight
                    omega
                  by_cases h14 : Is246 (n - (14 : ℕ).choose 8)
                  · exact leftover_num choose14_eight (by
                      have : (14 : ℕ).choose 8 = 3003 := choose14_eight
                      omega) h14
                  · exact (h0 ⟨aa, bb, cc, haa, by omega⟩).elim
              · exact (h0 ⟨aa, bb, cc, haa, by omega⟩).elim
