import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The triangular number $T_w = \binom{w+1}{2} = w(w+1)/2$.
-/
def triangle_number (w : ℕ) : ℕ := (w + 1).choose 2

/--
A262880: Number of ordered ways to write $n$ as $w(w+1)/2 + x^3 + y^3 + 2z^3$ with $w > 0$, $0 \le x \le y$ and $z \ge 0$.
-/
def A262880 (n : ℕ) : ℕ :=
  -- A conservative, sufficient upper bound for all variables is $n + 1$.
  let B := n + 1
  let V := range B

  -- S is the Cartesian product V x V x V x V, defining the search space for (w, x, y, z).
  -- The type is ℕ × (ℕ × (ℕ × ℕ)).
  let S : Finset (ℕ × (ℕ × (ℕ × ℕ))) := V.product (V.product (V.product V))

  Finset.card $ S.filter (λ p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.1
    let x := p.2.1
    let y := p.2.2.1
    let z := p.2.2.2
    -- Constraints: w > 0, 0 <= x <= y, and the sum equals n.
    w > 0 ∧ x ≤ y ∧ triangle_number w + x^3 + y^3 + 2 * (z^3) = n)

/-- The set of coefficient pairs (b, c) for Conjecture (i). -/
def A262880_Conjecture1_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (1, 2), (1, 3), (1, 4), (1, 6),
    (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
    (3, 3), (3, 4), (3, 5), (3, 6),
    (4, 10)
  ]))

lemma triangle_number_eq (w : ℕ) : triangle_number w = w * (w + 1) / 2 := by
  simp [triangle_number, Nat.choose_two_right, Nat.mul_comm]

lemma triangle_number_one : triangle_number 1 = 1 := by
  simp [triangle_number]

lemma triangle_number_two : triangle_number 2 = 3 := by
  simp [triangle_number]

lemma triangle_number_monotone {w₁ w₂ : ℕ} (h : w₁ ≤ w₂) :
    triangle_number w₁ ≤ triangle_number w₂ := by
  simp only [triangle_number]
  exact Nat.choose_le_choose 2 (Nat.succ_le_succ h)

lemma two_dvd_mul_succ (w : ℕ) : 2 ∣ w * (w + 1) := by
  cases Nat.even_or_odd w with
  | inl hev => exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp hev) _
  | inr hod =>
    have : 2 ∣ (w + 1) := even_iff_two_dvd.mp (by
      rw [Nat.even_add_one, Nat.not_even_iff_odd]
      exact hod)
    exact dvd_mul_of_dvd_right this _

/-- `8 T_w + 1 = (2w+1)^2`. -/
lemma triangle_number_spec (w : ℕ) :
    8 * triangle_number w + 1 = (2 * w + 1) ^ 2 := by
  rw [triangle_number_eq]
  have h2 : 2 ∣ w * (w + 1) := two_dvd_mul_succ w
  have hmul : 8 * (w * (w + 1) / 2) = 4 * (w * (w + 1)) := by
    have := Nat.mul_div_cancel' h2
    omega
  rw [hmul]
  ring

lemma is_triangle_of_sq {m k : ℕ} (hk : k * k = 8 * m + 1) (hkodd : Odd k)
    (hk3 : 3 ≤ k) : ∃ w > 0, triangle_number w = m := by
  obtain ⟨t, ht⟩ := hkodd
  have hk' : k = 2 * t + 1 := by omega
  have ht0 : 0 < t := by omega
  refine ⟨t, ht0, ?_⟩
  have hspec := triangle_number_spec t
  have h1 : (2 * t + 1) ^ 2 = 8 * triangle_number t + 1 := by
    simpa [pow_two] using hspec.symm
  have : 8 * triangle_number t + 1 = 8 * m + 1 := by
    rw [← h1, ← hk', pow_two, hk]
  omega

/-- `m` is a positive triangular number iff `8m+1` is a perfect square `k²` with `k` odd and `k ≥ 3`. -/
lemma exists_triangle_iff_eight_mul_succ_is_odd_sq (m : ℕ) :
    (∃ w > 0, triangle_number w = m) ↔
      ∃ k : ℕ, k * k = 8 * m + 1 ∧ Odd k ∧ 3 ≤ k := by
  constructor
  · intro ⟨w, hw, hT⟩
    refine ⟨2 * w + 1, ?_, odd_two_mul_add_one w, ?_⟩
    · have := triangle_number_spec w
      rw [hT, pow_two] at this
      exact this.symm
    · omega
  · intro ⟨k, hk, hodd, hk3⟩
    exact is_triangle_of_sq hk hodd hk3

lemma is_triangle_of_sqrt {m : ℕ} (h : (8 * m + 1).sqrt ^ 2 = 8 * m + 1)
    (hodd : Odd (8 * m + 1).sqrt) (hk3 : 3 ≤ (8 * m + 1).sqrt) :
    ∃ w > 0, triangle_number w = m :=
  is_triangle_of_sq (by simpa [pow_two] using h) hodd hk3

/-- If `8m+1` is a square, then its square root is odd. -/
lemma odd_sqrt_of_eight_mul_succ_sq {m : ℕ}
    (h : (8 * m + 1).sqrt ^ 2 = 8 * m + 1) : Odd (8 * m + 1).sqrt := by
  have hsq : (8 * m + 1).sqrt * (8 * m + 1).sqrt = 8 * m + 1 := by
    simpa [pow_two] using h
  have hmod : (8 * m + 1).sqrt % 2 = 1 := by
    have hm8 : (8 * m + 1) % 2 = 1 := by omega
    have hpar := Nat.mul_mod (8 * m + 1).sqrt (8 * m + 1).sqrt 2
    have hmul : ((8 * m + 1).sqrt % 2) * ((8 * m + 1).sqrt % 2) % 2 = 1 := by
      rw [← hpar, hsq, hm8]
    rcases Nat.mod_two_eq_zero_or_one (8 * m + 1).sqrt with hs | hs
    · simp [hs] at hmul
    · exact hs
  exact Nat.odd_iff.mpr hmod

lemma three_le_sqrt_of_pos_triangle {m : ℕ} (hm : 1 ≤ m)
    (_h : (8 * m + 1).sqrt ^ 2 = 8 * m + 1) : 3 ≤ (8 * m + 1).sqrt := by
  have : 3 ^ 2 ≤ 8 * m + 1 := by omega
  exact Nat.le_sqrt'.mpr this

lemma exists_triangle_iff_sqrt {m : ℕ} (hm : 1 ≤ m) :
    (∃ w > 0, triangle_number w = m) ↔ (8 * m + 1).sqrt ^ 2 = 8 * m + 1 := by
  constructor
  · intro ⟨w, hw, hT⟩
    have hspec := triangle_number_spec w
    have hsq : (2 * w + 1) ^ 2 = 8 * m + 1 := by
      rw [hT] at hspec
      exact hspec.symm
    have heq : 2 * w + 1 = (8 * m + 1).sqrt := by
      refine (Nat.eq_sqrt').2 ⟨?_, ?_⟩
      · exact hsq.le
      · have : (2 * w + 1) ^ 2 < (2 * w + 1 + 1) ^ 2 := by nlinarith
        simpa [hsq] using this
    rw [← heq, hsq]
  · intro h
    exact is_triangle_of_sqrt h (odd_sqrt_of_eight_mul_succ_sq h)
      (three_le_sqrt_of_pos_triangle hm h)

/-- The unique `w` such that `T_w ≤ n < T_{w+1}` (equivalently the largest
`w` with `T_w ≤ n`). For `n = 0` this is `0`. -/
def greedy_w (n : ℕ) : ℕ := ((8 * n + 1).sqrt - 1) / 2

lemma greedy_w_eq (n : ℕ) : greedy_w n = ((8 * n + 1).sqrt - 1) / 2 := rfl

lemma two_mul_greedy_w_add_one (n : ℕ) :
    2 * greedy_w n + 1 = 2 * (((8 * n + 1).sqrt - 1) / 2) + 1 := by
  simp [greedy_w]

/-- The greatest odd integer `≤ s` is `2*((s-1)/2)+1`, for `s ≥ 1`. -/
lemma greatest_odd_le {s : ℕ} (hs : 1 ≤ s) : 2 * ((s - 1) / 2) + 1 ≤ s := by
  cases s with
  | zero => omega
  | succ s =>
    have h := Nat.div_mul_le_self s 2
    omega

lemma greatest_odd_eq_of_odd {s : ℕ} (h : s % 2 = 1) :
    2 * ((s - 1) / 2) + 1 = s := by omega

lemma greatest_odd_eq_of_even {s : ℕ} (hs : 1 ≤ s) (h : s % 2 = 0) :
    2 * ((s - 1) / 2) + 1 = s - 1 := by omega

lemma greedy_w_spec (n : ℕ) (hn : 1 ≤ n) :
    triangle_number (greedy_w n) ≤ n ∧
      n < triangle_number (greedy_w n + 1) := by
  set s := (8 * n + 1).sqrt
  have hs_sq : s * s ≤ 8 * n + 1 := Nat.sqrt_le _
  have hs_lt : 8 * n + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
  have s_ge : 3 ≤ s := by
    have : 9 ≤ 8 * n + 1 := by omega
    exact Nat.le_sqrt.mpr this
  have hspec_w := triangle_number_spec (greedy_w n)
  have hspec_w1 := triangle_number_spec (greedy_w n + 1)
  have h23 : 2 * (greedy_w n + 1) + 1 = 2 * greedy_w n + 3 := by omega
  rcases Nat.mod_two_eq_zero_or_one s with hev | hod
  · -- s even: 2w+1 = s-1, 2w+3 = s+1
    have hs1 : 1 ≤ s := by omega
    have hodd : 2 * greedy_w n + 1 = s - 1 := by
      simpa [greedy_w] using greatest_odd_eq_of_even hs1 hev
    have hTle : triangle_number (greedy_w n) ≤ n := by
      have : (2 * greedy_w n + 1) ^ 2 ≤ 8 * n + 1 := by
        rw [hodd]
        have : (s - 1) * (s - 1) ≤ s * s := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
        exact le_trans (by simpa [pow_two] using this) hs_sq
      have : 8 * triangle_number (greedy_w n) + 1 ≤ 8 * n + 1 := by
        simpa [hspec_w, pow_two] using this
      omega
    have hTlt : n < triangle_number (greedy_w n + 1) := by
      have : 2 * greedy_w n + 3 = s + 1 := by omega
      have : 8 * n + 1 < (2 * greedy_w n + 3) ^ 2 := by
        rw [this]
        simpa [pow_two] using hs_lt
      have : 8 * n + 1 < 8 * triangle_number (greedy_w n + 1) + 1 := by
        simpa [hspec_w1, pow_two, h23] using this
      omega
    exact ⟨hTle, hTlt⟩
  · -- s odd: 2w+1 = s, 2w+3 = s+2
    have hodd : 2 * greedy_w n + 1 = s := by
      simpa [greedy_w] using greatest_odd_eq_of_odd hod
    have hTle : triangle_number (greedy_w n) ≤ n := by
      have : (2 * greedy_w n + 1) ^ 2 ≤ 8 * n + 1 := by
        rw [hodd, pow_two]
        exact hs_sq
      have : 8 * triangle_number (greedy_w n) + 1 ≤ 8 * n + 1 := by
        simpa [hspec_w, pow_two] using this
      omega
    have hTlt : n < triangle_number (greedy_w n + 1) := by
      have hs2 : s + 2 = 2 * greedy_w n + 3 := by omega
      have : 8 * n + 1 < (2 * greedy_w n + 3) ^ 2 := by
        have h1 : 8 * n + 1 < (s + 1) * (s + 1) := hs_lt
        have h2 : (s + 1) * (s + 1) < (s + 2) * (s + 2) := by
          nlinarith
        have := Nat.lt_trans h1 h2
        rw [hs2] at this
        simpa [pow_two] using this
      have : 8 * n + 1 < 8 * triangle_number (greedy_w n + 1) + 1 := by
        simpa [hspec_w1, pow_two, h23] using this
      omega
    exact ⟨hTle, hTlt⟩

lemma greedy_w_pos (n : ℕ) (hn : 1 ≤ n) : 0 < greedy_w n := by
  have ⟨_, h2⟩ := greedy_w_spec n hn
  by_contra h0
  have hw0 : greedy_w n = 0 := by omega
  rw [hw0] at h2
  have : triangle_number 1 = 1 := triangle_number_one
  simp [this] at h2
  omega

lemma rem_lt_succ_w (n : ℕ) (hn : 1 ≤ n) :
    n - triangle_number (greedy_w n) < greedy_w n + 1 := by
  have ⟨hle, hlt⟩ := greedy_w_spec n hn
  have hsucc : triangle_number (greedy_w n + 1) =
      triangle_number (greedy_w n) + (greedy_w n + 1) := by
    simpa [triangle_number, Nat.choose_one_right, Nat.add_comm] using
      (Nat.choose_succ_succ' (greedy_w n + 1) 1)
  have : n < triangle_number (greedy_w n) + (greedy_w n + 1) := by
    simpa [hsucc] using hlt
  omega

/-- Representation predicate. -/
def IsRep (n b c : ℕ) : Prop :=
  ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x ^ 3 + b * y ^ 3 + c * z ^ 3

lemma isRep_of_triangle (n : ℕ) (w : ℕ) (hw : 0 < w) (h : triangle_number w = n) (b c : ℕ) :
    IsRep n b c :=
  ⟨w, 0, 0, 0, hw, by simp [h]⟩

lemma isRep_of_cubes_add_triangle {n b c w x y z : ℕ}
    (hw : 0 < w)
    (h : n = triangle_number w + x ^ 3 + b * y ^ 3 + c * z ^ 3) :
    IsRep n b c :=
  ⟨w, x, y, z, hw, h⟩

/-- If the greedy remainder is a weighted sum of three cubes, we are done. -/
lemma isRep_of_greedy_cubes (n b c x y z : ℕ) (hn : 1 ≤ n)
    (h : n - triangle_number (greedy_w n) = x ^ 3 + b * y ^ 3 + c * z ^ 3) :
    IsRep n b c := by
  refine ⟨greedy_w n, x, y, z, greedy_w_pos n hn, ?_⟩
  have ⟨hle, _⟩ := greedy_w_spec n hn
  omega

lemma isRep_of_greedy_triangle (n b c : ℕ) (hn : 1 ≤ n)
    (h : triangle_number (greedy_w n) = n) : IsRep n b c :=
  isRep_of_triangle n (greedy_w n) (greedy_w_pos n hn) h b c

lemma two_dvd_j_mul (w j : ℕ) (hj : j ≤ w) : 2 ∣ j * (2 * w - j + 1) := by
  have hpar : (j * (2 * w - j + 1)) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one j with hev | hod
    · simp [Nat.mul_mod, hev]
    · -- j odd and j ≤ w ⇒ 2w - j + 1 is even
      have hjw : j ≤ 2 * w := by omega
      have : (2 * w - j + 1) % 2 = 0 := by
        have h2w : (2 * w) % 2 = 0 := by omega
        have hj1 : j % 2 = 1 := hod
        omega
      rw [Nat.mul_mod, this]
      simp
  exact Nat.dvd_of_mod_eq_zero hpar

lemma add_div_two_of_even {a b : ℕ} (ha : 2 ∣ a) (hb : 2 ∣ b) :
    (a + b) / 2 = a / 2 + b / 2 := by
  have ha' := Nat.mul_div_cancel' ha
  have hb' := Nat.mul_div_cancel' hb
  have hab : 2 ∣ a + b := dvd_add ha hb
  have hab' := Nat.mul_div_cancel' hab
  apply Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 2)
  omega

/-- Going back `j` triangular steps: `T_w = T_{w-j} + j(2w-j+1)/2`. -/
lemma triangle_sub_triangle (w j : ℕ) (hj : j ≤ w) :
    triangle_number w = triangle_number (w - j) + j * (2 * w - j + 1) / 2 := by
  have h2w : 2 ∣ w * (w + 1) := two_dvd_mul_succ w
  have h2wj : 2 ∣ (w - j) * (w - j + 1) := two_dvd_mul_succ (w - j)
  have h2j : 2 ∣ j * (2 * w - j + 1) := two_dvd_j_mul w j hj
  have hwj : j ≤ 2 * w := by omega
  have hsum : (w - j) * (w - j + 1) + j * (2 * w - j + 1) = w * (w + 1) := by
    have h1 : ((w - j : ℕ) : ℤ) = (w : ℤ) - (j : ℤ) := Int.natCast_sub hj
    have h2 : ((2 * w - j : ℕ) : ℤ) = (2 * w : ℤ) - (j : ℤ) := Int.natCast_sub hwj
    zify
    rw [h1, h2]
    ring
  have hdiv := add_div_two_of_even h2wj h2j
  rw [triangle_number_eq, triangle_number_eq, ← hdiv, hsum]

lemma isRep_one (b c : ℕ) : IsRep 1 b c :=
  isRep_of_triangle 1 1 (by decide) triangle_number_one b c

lemma isRep_two (b c : ℕ) : IsRep 2 b c :=
  ⟨1, 1, 0, 0, by decide, by simp [triangle_number_one]⟩

lemma isRep_three (b c : ℕ) : IsRep 3 b c :=
  isRep_of_triangle 3 2 (by decide) triangle_number_two b c

/-- Incrementing the `x`-cube when `x = 0`. -/
lemma isRep_succ_of_x_zero {n b c w y z : ℕ} (hw : 0 < w)
    (h : n = triangle_number w + b * y ^ 3 + c * z ^ 3) :
    IsRep (n + 1) b c :=
  ⟨w, 1, y, z, hw, by
    rw [h]
    ring⟩

/-- If `n` is representable with `x = 0`, then `n + 1` is representable. -/
lemma isRep_succ_of_exists_x_zero {n b c : ℕ}
    (h : ∃ w y z : ℕ, w > 0 ∧ n = triangle_number w + b * y ^ 3 + c * z ^ 3) :
    IsRep (n + 1) b c := by
  obtain ⟨w, y, z, hw, hn⟩ := h
  exact isRep_succ_of_x_zero hw hn

/-- Three-term representation (no free cube). -/
def IsRep3 (n b c : ℕ) : Prop :=
  ∃ w y z : ℕ, w > 0 ∧ n = triangle_number w + b * y ^ 3 + c * z ^ 3

lemma isRep_of_isRep3 {n b c : ℕ} (h : IsRep3 n b c) : IsRep n b c := by
  obtain ⟨w, y, z, hw, hn⟩ := h
  exact ⟨w, 0, y, z, hw, by simpa using hn⟩

lemma isRep_succ_of_isRep3 {n b c : ℕ} (h : IsRep3 n b c) : IsRep (n + 1) b c :=
  isRep_succ_of_exists_x_zero h

lemma isRep_of_sub_cube {n b c x : ℕ} (hx : x ^ 3 ≤ n)
    (h : IsRep3 (n - x ^ 3) b c) : IsRep n b c := by
  obtain ⟨w, y, z, hw, hn⟩ := h
  refine ⟨w, x, y, z, hw, ?_⟩
  have := Nat.sub_add_cancel hx
  omega

/-- Incrementing the `y`-cube when `b = 1` and `y = 0`. -/
lemma isRep_succ_of_y_zero {n c w x z : ℕ} (hw : 0 < w)
    (h : n = triangle_number w + x ^ 3 + c * z ^ 3) :
    IsRep (n + 1) 1 c :=
  ⟨w, x, 1, z, hw, by
    rw [h]
    ring⟩

lemma triangle_number_succ (w : ℕ) :
    triangle_number (w + 1) = triangle_number w + (w + 1) := by
  simpa [triangle_number, Nat.choose_one_right, Nat.add_comm] using
    (Nat.choose_succ_succ' (w + 1) 1)

lemma triangle_number_pred {w : ℕ} (hw : 0 < w) :
    triangle_number w = triangle_number (w - 1) + w := by
  cases w with
  | zero => simp at hw
  | succ w =>
    rw [Nat.succ_sub_one, triangle_number_succ]

lemma isRep_add_eight_of_isRep3 {n b c : ℕ} (h : IsRep3 n b c) : IsRep (n + 8) b c := by
  obtain ⟨w, y, z, hw, hn⟩ := h
  exact ⟨w, 2, y, z, hw, by rw [hn]; ring⟩

lemma isRep_add_twentyseven_of_isRep3 {n b c : ℕ} (h : IsRep3 n b c) : IsRep (n + 27) b c := by
  obtain ⟨w, y, z, hw, hn⟩ := h
  exact ⟨w, 3, y, z, hw, by rw [hn]; ring⟩

lemma isRep_triangle (w b c : ℕ) (hw : 0 < w) : IsRep (triangle_number w) b c :=
  isRep_of_triangle _ w hw rfl b c

lemma isRep_iff_exists_cube {n b c : ℕ} :
    IsRep n b c ↔ ∃ x : ℕ, x ^ 3 ≤ n ∧ IsRep3 (n - x ^ 3) b c := by
  constructor
  · intro ⟨w, x, y, z, hw, hn⟩
    have hx : x ^ 3 ≤ n := by
      have : n = triangle_number w + x ^ 3 + b * y ^ 3 + c * z ^ 3 := hn
      omega
    refine ⟨x, hx, w, y, z, hw, ?_⟩
    have hn' : n - x ^ 3 = triangle_number w + b * y ^ 3 + c * z ^ 3 := by
      have : n = triangle_number w + x ^ 3 + b * y ^ 3 + c * z ^ 3 := hn
      omega
    exact hn'
  · intro ⟨x, hx, h3⟩
    exact isRep_of_sub_cube hx h3

lemma isRep_of_isRep3_sub {n b c x : ℕ} (hx : x ^ 3 < n)
    (h : IsRep3 (n - x ^ 3) b c) : IsRep n b c :=
  isRep_of_sub_cube (Nat.le_of_lt hx) h

lemma isRep_of_isRep3_or_pred {n b c : ℕ} (hn : 1 ≤ n)
    (h : IsRep3 n b c ∨ IsRep3 (n - 1) b c) : IsRep n b c := by
  rcases h with h | h
  · exact isRep_of_isRep3 h
  · have : n = (n - 1) + 1 := by omega
    rw [this]
    exact isRep_succ_of_isRep3 h

/-- Cube-cloud: if any of `n - 0, n-1, n-8, n-27` is a 3-term rep, then `n` is representable. -/
lemma isRep_of_cube_cloud4 {n b c : ℕ} (hn : 27 < n)
    (h : IsRep3 n b c ∨ IsRep3 (n - 1) b c ∨ IsRep3 (n - 8) b c ∨ IsRep3 (n - 27) b c) :
    IsRep n b c := by
  rcases h with h | h | h | h
  · exact isRep_of_isRep3 h
  · exact isRep_of_isRep3_or_pred (by omega) (Or.inr h)
  · have : n = (n - 8) + 8 := by omega
    rw [this]
    exact isRep_add_eight_of_isRep3 h
  · have : n = (n - 27) + 27 := by omega
    rw [this]
    exact isRep_add_twentyseven_of_isRep3 h

/-- If `n - x^3` is a 3-term representation for some `x ≤ 15` (and `n` is large enough
    that `15^3 = 3375 < n`), then `n` is representable. -/
lemma isRep_of_cube_cloud16 {n b c : ℕ} (hn : 3375 < n)
    (h : ∃ x : ℕ, x ≤ 15 ∧ IsRep3 (n - x ^ 3) b c) : IsRep n b c := by
  obtain ⟨x, hx, h3⟩ := h
  have hx3 : x ^ 3 < n := by
    have : x ^ 3 ≤ 15 ^ 3 := Nat.pow_le_pow_left hx 3
    omega
  exact isRep_of_isRep3_sub hx3 h3

lemma isRep_of_sq {n b c x y z k : ℕ}
    (hk : k * k = 8 * (n - x ^ 3 - b * y ^ 3 - c * z ^ 3) + 1)
    (hodd : Odd k) (hk3 : 3 ≤ k)
    (hle : x ^ 3 + b * y ^ 3 + c * z ^ 3 ≤ n) :
    IsRep n b c := by
  have hm : ∃ w > 0, triangle_number w = n - x ^ 3 - b * y ^ 3 - c * z ^ 3 :=
    is_triangle_of_sq hk hodd hk3
  obtain ⟨w, hw, hT⟩ := hm
  refine ⟨w, x, y, z, hw, ?_⟩
  omega

lemma pairs_mem_iff (p : ℕ × ℕ) :
    p ∈ A262880_Conjecture1_Pairs ↔
      p = (1, 2) ∨ p = (1, 3) ∨ p = (1, 4) ∨ p = (1, 6) ∨
      p = (2, 2) ∨ p = (2, 3) ∨ p = (2, 4) ∨ p = (2, 5) ∨ p = (2, 6) ∨
      p = (2, 7) ∨ p = (2, 20) ∨ p = (2, 21) ∨ p = (2, 34) ∨
      p = (3, 3) ∨ p = (3, 4) ∨ p = (3, 5) ∨ p = (3, 6) ∨
      p = (4, 10) := by
  simp [A262880_Conjecture1_Pairs]

lemma isRep_1_2_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 1 2 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 1, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 1, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 2, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨5, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 1, by decide, by decide⟩
  · exact ⟨10, 1, 1, 1, by decide, by decide⟩
  · exact ⟨3, 3, 3, 0, by decide, by decide⟩
  · exact ⟨9, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 3, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨10, 2, 1, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 3, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩

lemma isRep_1_3_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 1 3 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 1, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨5, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 1, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 3, 0, by decide, by decide⟩
  · exact ⟨9, 2, 2, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 2, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨10, 2, 1, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 3, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩

lemma isRep_1_4_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 1 4 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 1, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 1, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨5, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 3, 0, by decide, by decide⟩
  · exact ⟨9, 2, 2, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 2, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨10, 2, 1, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 3, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 1, by decide, by decide⟩
  · exact ⟨9, 3, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩

lemma isRep_1_6_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 1 6 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 1, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 1, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 1, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 1, 1, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨5, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 2, 1, by decide, by decide⟩
  · exact ⟨9, 2, 0, 1, by decide, by decide⟩
  · exact ⟨3, 3, 3, 0, by decide, by decide⟩
  · exact ⟨9, 2, 2, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨10, 2, 1, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 3, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 1, by decide, by decide⟩
  · exact ⟨3, 4, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩

lemma isRep_2_2_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 2 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 2, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_3_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 3 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_4_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 4 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_5_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 5 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_6_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 6 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 1, by decide, by decide⟩
  · exact ⟨3, 3, 1, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_7_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 7 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 1, by decide, by decide⟩
  · exact ⟨4, 2, 2, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_20_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 20 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_21_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 21 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 1, by decide, by decide⟩
  · exact ⟨4, 2, 1, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_2_34_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 2 34 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 1, 0, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 2, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩

lemma isRep_3_3_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 3 3 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 1, 1, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 1, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 2, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 1, 1, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 2, 1, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 1, 1, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 1, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 2, 0, by decide, by decide⟩

lemma isRep_3_4_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 3 4 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 1, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 1, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 1, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 1, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 2, 0, by decide, by decide⟩

lemma isRep_3_5_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 3 5 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 2, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 1, 2, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 1, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 1, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 2, 0, by decide, by decide⟩

lemma isRep_3_6_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 3 6 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 1, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 1, 0, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 1, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 1, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 1, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨3, 4, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 2, 0, by decide, by decide⟩

lemma isRep_4_10_upto_80 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 80) : IsRep n 4 10 := by
  interval_cases n
  · exact ⟨1, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 0, 0, by decide, by decide⟩
  · exact ⟨1, 1, 0, 1, by decide, by decide⟩
  · exact ⟨1, 2, 1, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 1, 0, 1, by decide, by decide⟩
  · exact ⟨4, 2, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 0, by decide, by decide⟩
  · exact ⟨5, 1, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 0, 0, by decide, by decide⟩
  · exact ⟨3, 2, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 3, 0, 0, by decide, by decide⟩
  · exact ⟨2, 3, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 1, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 0, by decide, by decide⟩
  · exact ⟨5, 3, 0, 0, by decide, by decide⟩
  · exact ⟨4, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 2, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 1, 1, 1, by decide, by decide⟩
  · exact ⟨6, 3, 1, 0, by decide, by decide⟩
  · exact ⟨9, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 3, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 1, 1, 0, by decide, by decide⟩
  · exact ⟨7, 1, 2, 0, by decide, by decide⟩
  · exact ⟨2, 3, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 1, 2, 1, by decide, by decide⟩
  · exact ⟨1, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 0, by decide, by decide⟩
  · exact ⟨1, 4, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 0, 0, by decide, by decide⟩
  · exact ⟨11, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 3, 0, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 0, by decide, by decide⟩
  · exact ⟨1, 4, 0, 1, by decide, by decide⟩
  · exact ⟨9, 3, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 1, 0, 0, by decide, by decide⟩
  · exact ⟨6, 3, 2, 0, by decide, by decide⟩



/-! ### Certificates for 81 ≤ n ≤ 400 -/ 

lemma isRep_1_2_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 1 2 := by
  interval_cases n
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨6, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 1, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 3, by decide, by decide⟩
  · exact ⟨5, 1, 3, 3, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 1, 2, 2, by decide, by decide⟩
  · exact ⟨5, 2, 3, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨9, 0, 4, 1, by decide, by decide⟩
  · exact ⟨9, 1, 4, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨14, 1, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 4, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 3, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 3, by decide, by decide⟩
  · exact ⟨9, 0, 4, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 1, 3, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 0, by decide, by decide⟩
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 0, 1, 4, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨12, 1, 2, 3, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨6, 0, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 2, 4, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨2, 0, 3, 4, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩

lemma isRep_1_2_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 1 2 := by
  interval_cases n
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨8, 1, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 1, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨6, 0, 3, 4, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 1, 2, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 3, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 4, 2, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨4, 0, 5, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨17, 0, 3, 2, by decide, by decide⟩
  · exact ⟨17, 1, 3, 2, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 1, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 4, by decide, by decide⟩
  · exact ⟨12, 0, 5, 0, by decide, by decide⟩
  · exact ⟨12, 1, 5, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 4, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 3, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨11, 0, 3, 4, by decide, by decide⟩
  · exact ⟨3, 0, 6, 0, by decide, by decide⟩
  · exact ⟨14, 0, 4, 3, by decide, by decide⟩
  · exact ⟨9, 0, 5, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 4, by decide, by decide⟩
  · exact ⟨8, 1, 4, 4, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 1, 4, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨15, 0, 4, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨21, 1, 2, 0, by decide, by decide⟩

lemma isRep_1_2_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 1 2 := by
  interval_cases n
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨4, 0, 6, 2, by decide, by decide⟩
  · exact ⟨4, 1, 6, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 3, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 4, by decide, by decide⟩
  · exact ⟨15, 0, 1, 4, by decide, by decide⟩
  · exact ⟨15, 1, 1, 4, by decide, by decide⟩
  · exact ⟨1, 0, 0, 5, by decide, by decide⟩
  · exact ⟨1, 0, 1, 5, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 0, 0, 5, by decide, by decide⟩
  · exact ⟨3, 0, 1, 5, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨1, 0, 2, 5, by decide, by decide⟩
  · exact ⟨4, 0, 0, 5, by decide, by decide⟩
  · exact ⟨4, 0, 1, 5, by decide, by decide⟩
  · exact ⟨4, 1, 1, 5, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 0, 5, by decide, by decide⟩
  · exact ⟨5, 0, 1, 5, by decide, by decide⟩
  · exact ⟨5, 1, 1, 5, by decide, by decide⟩
  · exact ⟨4, 0, 2, 5, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 5, by decide, by decide⟩
  · exact ⟨6, 0, 1, 5, by decide, by decide⟩
  · exact ⟨5, 0, 2, 5, by decide, by decide⟩
  · exact ⟨21, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 4, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 0, 1, 4, by decide, by decide⟩
  · exact ⟨3, 0, 3, 5, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 0, 5, by decide, by decide⟩
  · exact ⟨8, 0, 1, 5, by decide, by decide⟩
  · exact ⟨8, 1, 1, 5, by decide, by decide⟩
  · exact ⟨17, 0, 2, 4, by decide, by decide⟩
  · exact ⟨20, 0, 4, 2, by decide, by decide⟩
  · exact ⟨20, 0, 3, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 2, 5, by decide, by decide⟩
  · exact ⟨9, 0, 0, 5, by decide, by decide⟩
  · exact ⟨9, 0, 1, 5, by decide, by decide⟩
  · exact ⟨21, 0, 4, 1, by decide, by decide⟩
  · exact ⟨6, 0, 3, 5, by decide, by decide⟩
  · exact ⟨18, 0, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 5, by decide, by decide⟩
  · exact ⟨10, 0, 1, 5, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 6, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 4, 2, by decide, by decide⟩
  · exact ⟨21, 0, 3, 3, by decide, by decide⟩
  · exact ⟨10, 0, 2, 5, by decide, by decide⟩
  · exact ⟨10, 1, 2, 5, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 0, 1, 4, by decide, by decide⟩
  · exact ⟨3, 0, 4, 5, by decide, by decide⟩

lemma isRep_1_2_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 1 2 := by
  interval_cases n
  · exact ⟨14, 0, 6, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 5, by decide, by decide⟩
  · exact ⟨14, 0, 6, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 5, by decide, by decide⟩
  · exact ⟨12, 0, 1, 5, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨10, 0, 3, 5, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 3, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 5, by decide, by decide⟩
  · exact ⟨20, 0, 5, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 4, by decide, by decide⟩
  · exact ⟨20, 0, 1, 4, by decide, by decide⟩
  · exact ⟨23, 0, 4, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨24, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 5, 4, by decide, by decide⟩
  · exact ⟨19, 0, 3, 4, by decide, by decide⟩
  · exact ⟨20, 0, 2, 4, by decide, by decide⟩
  · exact ⟨2, 0, 6, 4, by decide, by decide⟩
  · exact ⟨12, 0, 6, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 5, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 5, by decide, by decide⟩
  · exact ⟨14, 0, 1, 5, by decide, by decide⟩
  · exact ⟨23, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 4, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 5, by decide, by decide⟩
  · exact ⟨24, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 4, by decide, by decide⟩
  · exact ⟨24, 0, 4, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 0, 4, 5, by decide, by decide⟩
  · exact ⟨15, 0, 0, 5, by decide, by decide⟩
  · exact ⟨15, 0, 1, 5, by decide, by decide⟩
  · exact ⟨21, 0, 5, 2, by decide, by decide⟩
  · exact ⟨15, 0, 5, 4, by decide, by decide⟩
  · exact ⟨5, 0, 7, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 2, by decide, by decide⟩
  · exact ⟨1, 0, 5, 5, by decide, by decide⟩
  · exact ⟨1, 1, 5, 5, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 3, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 1, 1, 4, by decide, by decide⟩
  · exact ⟨1, 2, 5, 5, by decide, by decide⟩
  · exact ⟨4, 0, 5, 5, by decide, by decide⟩
  · exact ⟨16, 0, 0, 5, by decide, by decide⟩
  · exact ⟨16, 0, 1, 5, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 4, by decide, by decide⟩
  · exact ⟨5, 0, 5, 5, by decide, by decide⟩
  · exact ⟨25, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 0, 4, 5, by decide, by decide⟩
  · exact ⟨12, 1, 4, 5, by decide, by decide⟩
  · exact ⟨27, 0, 0, 2, by decide, by decide⟩
  · exact ⟨27, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 5, 5, by decide, by decide⟩
  · exact ⟨15, 0, 3, 5, by decide, by decide⟩
  · exact ⟨10, 0, 7, 0, by decide, by decide⟩
  · exact ⟨10, 0, 6, 4, by decide, by decide⟩
  · exact ⟨10, 0, 7, 1, by decide, by decide⟩

lemma isRep_1_2_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 1 2 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_1_2_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_1_2_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_1_2_241_to_320 n h2 h3
  · exact isRep_1_2_321_to_400 n h3 hn

lemma isRep_1_2_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 1 2 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_1_2_upto_80 n h0 h
  · exact isRep_1_2_81_to_400 n h hn

lemma isRep_1_3_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 1 3 := by
  interval_cases n
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨1, 0, 1, 3, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 1, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 3, by decide, by decide⟩
  · exact ⟨7, 0, 1, 3, by decide, by decide⟩
  · exact ⟨2, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 0, 4, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 2, 1, by decide, by decide⟩
  · exact ⟨14, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 4, 1, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 5, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨1, 0, 4, 3, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨6, 0, 5, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩

lemma isRep_1_3_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 1 3 := by
  interval_cases n
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 1, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 1, 2, 1, by decide, by decide⟩
  · exact ⟨16, 0, 3, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 4, 0, by decide, by decide⟩
  · exact ⟨9, 0, 5, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 1, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 1, 1, 3, by decide, by decide⟩
  · exact ⟨8, 2, 4, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 1, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 1, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨16, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨17, 0, 3, 2, by decide, by decide⟩
  · exact ⟨17, 1, 3, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨15, 0, 2, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 5, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 5, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 5, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 3, by decide, by decide⟩
  · exact ⟨16, 0, 4, 2, by decide, by decide⟩
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 0, 6, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 4, by decide, by decide⟩
  · exact ⟨9, 0, 0, 4, by decide, by decide⟩
  · exact ⟨9, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩

lemma isRep_1_3_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 1 3 := by
  interval_cases n
  · exact ⟨19, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨2, 0, 6, 2, by decide, by decide⟩
  · exact ⟨16, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 0, 2, 4, by decide, by decide⟩
  · exact ⟨3, 0, 6, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨10, 1, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 4, 3, by decide, by decide⟩
  · exact ⟨9, 0, 5, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 4, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 4, by decide, by decide⟩
  · exact ⟨11, 1, 2, 4, by decide, by decide⟩
  · exact ⟨7, 0, 6, 2, by decide, by decide⟩
  · exact ⟨15, 0, 5, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 1, 1, 3, by decide, by decide⟩
  · exact ⟨10, 0, 3, 4, by decide, by decide⟩
  · exact ⟨10, 1, 3, 4, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 0, 4, 3, by decide, by decide⟩
  · exact ⟨21, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 1, 2, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 1, 2, 1, by decide, by decide⟩
  · exact ⟨16, 2, 4, 3, by decide, by decide⟩
  · exact ⟨21, 2, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 1, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 6, 0, by decide, by decide⟩
  · exact ⟨21, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 5, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 4, by decide, by decide⟩
  · exact ⟨14, 0, 1, 4, by decide, by decide⟩
  · exact ⟨20, 0, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 5, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 4, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 6, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨24, 1, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 4, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 1, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 5, 0, by decide, by decide⟩
  · exact ⟨18, 0, 4, 3, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 4, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 3, by decide, by decide⟩

lemma isRep_1_3_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 1 3 := by
  interval_cases n
  · exact ⟨14, 0, 6, 0, by decide, by decide⟩
  · exact ⟨11, 0, 4, 4, by decide, by decide⟩
  · exact ⟨3, 0, 5, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 6, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨25, 1, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 3, 3, by decide, by decide⟩
  · exact ⟨23, 0, 4, 0, by decide, by decide⟩
  · exact ⟨22, 0, 4, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 4, 1, by decide, by decide⟩
  · exact ⟨1, 0, 7, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 0, 1, 4, by decide, by decide⟩
  · exact ⟨13, 0, 4, 4, by decide, by decide⟩
  · exact ⟨13, 1, 4, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 0, 5, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 6, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 3, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 4, by decide, by decide⟩
  · exact ⟨18, 0, 1, 4, by decide, by decide⟩
  · exact ⟨23, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 1, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 4, 1, by decide, by decide⟩
  · exact ⟨1, 0, 7, 2, by decide, by decide⟩
  · exact ⟨17, 0, 6, 0, by decide, by decide⟩
  · exact ⟨2, 0, 7, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 4, by decide, by decide⟩
  · exact ⟨17, 0, 3, 4, by decide, by decide⟩
  · exact ⟨3, 0, 7, 2, by decide, by decide⟩
  · exact ⟨7, 0, 7, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 0, 0, 5, by decide, by decide⟩
  · exact ⟨1, 0, 1, 5, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 5, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 0, 1, 4, by decide, by decide⟩
  · exact ⟨1, 0, 2, 5, by decide, by decide⟩
  · exact ⟨4, 0, 0, 5, by decide, by decide⟩
  · exact ⟨4, 0, 1, 5, by decide, by decide⟩
  · exact ⟨18, 0, 6, 0, by decide, by decide⟩
  · exact ⟨24, 0, 4, 2, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 5, by decide, by decide⟩
  · exact ⟨5, 0, 1, 5, by decide, by decide⟩
  · exact ⟨25, 0, 4, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 5, by decide, by decide⟩
  · exact ⟨4, 1, 2, 5, by decide, by decide⟩
  · exact ⟨12, 0, 5, 4, by decide, by decide⟩
  · exact ⟨6, 0, 0, 5, by decide, by decide⟩
  · exact ⟨6, 0, 1, 5, by decide, by decide⟩
  · exact ⟨5, 0, 2, 5, by decide, by decide⟩
  · exact ⟨5, 1, 2, 5, by decide, by decide⟩
  · exact ⟨25, 2, 4, 1, by decide, by decide⟩

lemma isRep_1_3_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 1 3 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_1_3_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_1_3_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_1_3_241_to_320 n h2 h3
  · exact isRep_1_3_321_to_400 n h3 hn

lemma isRep_1_3_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 1 3 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_1_3_upto_80 n h0 h
  · exact isRep_1_3_81_to_400 n h hn

lemma isRep_1_4_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 1 4 := by
  interval_cases n
  · exact ⟨6, 1, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 1, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 1, 4, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 2, by decide, by decide⟩
  · exact ⟨13, 0, 2, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 4, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 1, 1, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 2, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 1, 2, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 1, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 1, by decide, by decide⟩
  · exact ⟨4, 0, 5, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨4, 0, 5, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 1, 4, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨16, 1, 2, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩

lemma isRep_1_4_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 1 4 := by
  interval_cases n
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 0, 4, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 1, 2, 1, by decide, by decide⟩
  · exact ⟨16, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 0, 5, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 4, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 1, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 1, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 1, 4, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 1, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨9, 3, 5, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 3, 3, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 1, 1, 2, by decide, by decide⟩
  · exact ⟨19, 2, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 3, by decide, by decide⟩
  · exact ⟨8, 1, 4, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 3, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨2, 0, 6, 0, by decide, by decide⟩
  · exact ⟨13, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 1, 1, 2, by decide, by decide⟩
  · exact ⟨19, 2, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 4, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩

lemma isRep_1_4_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 1 4 := by
  interval_cases n
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 1, 1, 3, by decide, by decide⟩
  · exact ⟨21, 2, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 5, 2, by decide, by decide⟩
  · exact ⟨19, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨2, 0, 6, 2, by decide, by decide⟩
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 3, 3, by decide, by decide⟩
  · exact ⟨8, 0, 6, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨2, 0, 1, 4, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 1, 1, 4, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨5, 1, 1, 4, by decide, by decide⟩
  · exact ⟨4, 0, 2, 4, by decide, by decide⟩
  · exact ⟨10, 0, 6, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨6, 0, 1, 4, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 5, 1, by decide, by decide⟩
  · exact ⟨17, 1, 5, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨3, 0, 3, 4, by decide, by decide⟩
  · exact ⟨21, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 1, 3, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨12, 0, 6, 0, by decide, by decide⟩
  · exact ⟨21, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 5, 0, by decide, by decide⟩
  · exact ⟨18, 1, 5, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 4, by decide, by decide⟩
  · exact ⟨9, 0, 1, 4, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 5, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨10, 1, 1, 4, by decide, by decide⟩
  · exact ⟨11, 0, 6, 2, by decide, by decide⟩
  · exact ⟨19, 0, 5, 0, by decide, by decide⟩
  · exact ⟨23, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 1, 1, 3, by decide, by decide⟩

lemma isRep_1_4_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 1 4 := by
  interval_cases n
  · exact ⟨22, 0, 4, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨13, 0, 5, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨12, 0, 1, 4, by decide, by decide⟩
  · exact ⟨15, 0, 6, 0, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨6, 0, 4, 4, by decide, by decide⟩
  · exact ⟨12, 0, 2, 4, by decide, by decide⟩
  · exact ⟨18, 0, 4, 3, by decide, by decide⟩
  · exact ⟨23, 0, 4, 1, by decide, by decide⟩
  · exact ⟨20, 0, 3, 3, by decide, by decide⟩
  · exact ⟨2, 0, 7, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨11, 0, 3, 4, by decide, by decide⟩
  · exact ⟨2, 0, 7, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 5, 3, by decide, by decide⟩
  · exact ⟨15, 1, 5, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨21, 0, 5, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 0, 4, 0, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 3, 3, by decide, by decide⟩
  · exact ⟨20, 0, 5, 2, by decide, by decide⟩
  · exact ⟨24, 0, 4, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 1, 2, 3, by decide, by decide⟩
  · exact ⟨7, 0, 7, 0, by decide, by decide⟩
  · exact ⟨23, 0, 4, 2, by decide, by decide⟩
  · exact ⟨17, 0, 6, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 4, by decide, by decide⟩
  · exact ⟨10, 0, 4, 4, by decide, by decide⟩
  · exact ⟨15, 0, 0, 4, by decide, by decide⟩
  · exact ⟨15, 0, 1, 4, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨27, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 7, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨27, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 5, 4, by decide, by decide⟩
  · exact ⟨22, 0, 3, 3, by decide, by decide⟩
  · exact ⟨25, 0, 4, 0, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 4, by decide, by decide⟩
  · exact ⟨16, 0, 1, 4, by decide, by decide⟩
  · exact ⟨16, 1, 1, 4, by decide, by decide⟩
  · exact ⟨3, 2, 5, 4, by decide, by decide⟩
  · exact ⟨24, 0, 4, 2, by decide, by decide⟩
  · exact ⟨24, 1, 4, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 4, by decide, by decide⟩
  · exact ⟨12, 1, 4, 4, by decide, by decide⟩
  · exact ⟨16, 0, 2, 4, by decide, by decide⟩

lemma isRep_1_4_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 1 4 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_1_4_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_1_4_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_1_4_241_to_320 n h2 h3
  · exact isRep_1_4_321_to_400 n h3 hn

lemma isRep_1_4_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 1 4 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_1_4_upto_80 n h0 h
  · exact isRep_1_4_81_to_400 n h hn

lemma isRep_1_6_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 1 6 := by
  interval_cases n
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 3, 0, by decide, by decide⟩
  · exact ⟨10, 1, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 1, 3, 1, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 1, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 1, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 2, 4, 0, by decide, by decide⟩
  · exact ⟨9, 0, 4, 0, by decide, by decide⟩
  · exact ⟨9, 1, 4, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨11, 1, 1, 2, by decide, by decide⟩
  · exact ⟨9, 2, 4, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨11, 1, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨3, 0, 5, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨15, 0, 2, 1, by decide, by decide⟩
  · exact ⟨4, 0, 5, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨16, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 0, by decide, by decide⟩
  · exact ⟨13, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 1, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨16, 1, 2, 1, by decide, by decide⟩
  · exact ⟨6, 0, 5, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨13, 1, 4, 0, by decide, by decide⟩
  · exact ⟨9, 0, 4, 2, by decide, by decide⟩
  · exact ⟨9, 1, 4, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩

lemma isRep_1_6_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 1 6 := by
  interval_cases n
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 1, 2, 0, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨1, 0, 1, 3, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 0, 5, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨1, 0, 5, 2, by decide, by decide⟩
  · exact ⟨14, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 1, 2, 3, by decide, by decide⟩
  · exact ⟨1, 2, 5, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨17, 1, 3, 1, by decide, by decide⟩
  · exact ⟨5, 0, 5, 2, by decide, by decide⟩
  · exact ⟨5, 1, 5, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 1, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 5, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 4, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨19, 1, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 1, 1, 0, by decide, by decide⟩
  · exact ⟨17, 3, 3, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 3, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 1, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 5, 1, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 0, 6, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩

lemma isRep_1_6_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 1 6 := by
  interval_cases n
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 1, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 4, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨12, 1, 2, 3, by decide, by decide⟩
  · exact ⟨7, 0, 6, 1, by decide, by decide⟩
  · exact ⟨15, 0, 5, 1, by decide, by decide⟩
  · exact ⟨8, 0, 6, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 3, 3, by decide, by decide⟩
  · exact ⟨11, 1, 3, 3, by decide, by decide⟩
  · exact ⟨14, 3, 5, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 4, 3, by decide, by decide⟩
  · exact ⟨8, 1, 4, 3, by decide, by decide⟩
  · exact ⟨21, 0, 3, 1, by decide, by decide⟩
  · exact ⟨19, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 1, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 6, 2, by decide, by decide⟩
  · exact ⟨9, 0, 4, 3, by decide, by decide⟩
  · exact ⟨9, 1, 4, 3, by decide, by decide⟩
  · exact ⟨19, 2, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 5, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 0, 4, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨1, 0, 5, 3, by decide, by decide⟩
  · exact ⟨1, 1, 5, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 1, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 3, by decide, by decide⟩
  · exact ⟨15, 0, 5, 2, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 5, 0, by decide, by decide⟩
  · exact ⟨4, 0, 5, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 4, 3, by decide, by decide⟩
  · exact ⟨12, 1, 4, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 1, 2, 2, by decide, by decide⟩
  · exact ⟨23, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 2, 4, 3, by decide, by decide⟩
  · exact ⟨13, 0, 6, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨22, 1, 4, 0, by decide, by decide⟩
  · exact ⟨10, 0, 6, 2, by decide, by decide⟩
  · exact ⟨10, 1, 6, 2, by decide, by decide⟩

lemma isRep_1_6_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 1 6 := by
  interval_cases n
  · exact ⟨19, 0, 5, 1, by decide, by decide⟩
  · exact ⟨20, 0, 4, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 1, 3, 2, by decide, by decide⟩
  · exact ⟨11, 0, 6, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 5, 0, by decide, by decide⟩
  · exact ⟨15, 0, 6, 0, by decide, by decide⟩
  · exact ⟨15, 1, 6, 0, by decide, by decide⟩
  · exact ⟨11, 2, 6, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 4, 2, by decide, by decide⟩
  · exact ⟨18, 0, 5, 2, by decide, by decide⟩
  · exact ⟨18, 1, 5, 2, by decide, by decide⟩
  · exact ⟨23, 0, 4, 1, by decide, by decide⟩
  · exact ⟨23, 1, 4, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨1, 0, 7, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 1, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 6, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 1, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 4, 3, by decide, by decide⟩
  · exact ⟨19, 0, 5, 2, by decide, by decide⟩
  · exact ⟨24, 0, 4, 0, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 1, 2, 1, by decide, by decide⟩
  · exact ⟨26, 2, 2, 0, by decide, by decide⟩
  · exact ⟨19, 2, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 6, 0, by decide, by decide⟩
  · exact ⟨24, 0, 4, 1, by decide, by decide⟩
  · exact ⟨7, 0, 7, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨24, 0, 3, 2, by decide, by decide⟩
  · exact ⟨24, 1, 3, 2, by decide, by decide⟩
  · exact ⟨7, 0, 7, 1, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 1, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 5, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 0, 1, 4, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨2, 0, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 4, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 1, 1, 4, by decide, by decide⟩
  · exact ⟨18, 0, 4, 3, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩

lemma isRep_1_6_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 1 6 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_1_6_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_1_6_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_1_6_241_to_320 n h2 h3
  · exact isRep_1_6_321_to_400 n h3 hn

lemma isRep_1_6_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 1 6 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_1_6_upto_80 n h0 h
  · exact isRep_1_6_81_to_400 n h hn

lemma isRep_2_2_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 2 := by
  interval_cases n
  · exact ⟨12, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 1, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 2, 3, by decide, by decide⟩
  · exact ⟨5, 1, 2, 3, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 1, 2, 2, by decide, by decide⟩
  · exact ⟨3, 3, 1, 3, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 1, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨9, 1, 1, 3, by decide, by decide⟩
  · exact ⟨13, 2, 1, 1, by decide, by decide⟩
  · exact ⟨12, 2, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 1, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨10, 1, 1, 3, by decide, by decide⟩
  · exact ⟨14, 2, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨9, 1, 2, 3, by decide, by decide⟩
  · exact ⟨10, 2, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 3, 3, by decide, by decide⟩
  · exact ⟨4, 1, 3, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 3, by decide, by decide⟩
  · exact ⟨10, 1, 2, 3, by decide, by decide⟩
  · exact ⟨9, 4, 1, 2, by decide, by decide⟩
  · exact ⟨15, 2, 0, 0, by decide, by decide⟩
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 1, 0, 4, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 1, 4, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 1, 0, 4, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩
  · exact ⟨3, 2, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 0, 3, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 1, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨6, 0, 1, 4, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 1, 0, 3, by decide, by decide⟩

lemma isRep_2_2_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 2 := by
  interval_cases n
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 1, 1, 3, by decide, by decide⟩
  · exact ⟨10, 0, 3, 3, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨6, 0, 2, 4, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨8, 1, 1, 4, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 4, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 1, 1, 3, by decide, by decide⟩
  · exact ⟨6, 3, 1, 4, by decide, by decide⟩
  · exact ⟨18, 2, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 4, by decide, by decide⟩
  · exact ⟨8, 1, 2, 4, by decide, by decide⟩
  · exact ⟨15, 2, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 1, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 3, 4, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨11, 1, 0, 4, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 3, 4, by decide, by decide⟩
  · exact ⟨5, 1, 3, 4, by decide, by decide⟩
  · exact ⟨10, 0, 2, 4, by decide, by decide⟩
  · exact ⟨10, 1, 2, 4, by decide, by decide⟩
  · exact ⟨15, 3, 0, 3, by decide, by decide⟩
  · exact ⟨11, 2, 0, 4, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 1, 2, 2, by decide, by decide⟩
  · exact ⟨5, 2, 3, 4, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨20, 1, 1, 1, by decide, by decide⟩
  · exact ⟨19, 2, 1, 2, by decide, by decide⟩
  · exact ⟨17, 2, 1, 3, by decide, by decide⟩
  · exact ⟨8, 0, 3, 4, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 1, 0, 4, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 1, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨20, 1, 1, 2, by decide, by decide⟩
  · exact ⟨19, 2, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 4, by decide, by decide⟩
  · exact ⟨10, 1, 3, 4, by decide, by decide⟩
  · exact ⟨21, 2, 0, 0, by decide, by decide⟩
  · exact ⟨14, 3, 3, 3, by decide, by decide⟩

lemma isRep_2_2_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 2 := by
  interval_cases n
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 1, 2, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 1, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 4, by decide, by decide⟩
  · exact ⟨1, 0, 0, 5, by decide, by decide⟩
  · exact ⟨1, 1, 0, 5, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 0, 0, 5, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 1, 5, by decide, by decide⟩
  · exact ⟨2, 0, 4, 4, by decide, by decide⟩
  · exact ⟨4, 0, 0, 5, by decide, by decide⟩
  · exact ⟨17, 0, 3, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 5, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 0, 5, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 1, 5, by decide, by decide⟩
  · exact ⟨5, 1, 1, 5, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 1, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 5, by decide, by decide⟩
  · exact ⟨3, 0, 2, 5, by decide, by decide⟩
  · exact ⟨6, 0, 1, 5, by decide, by decide⟩
  · exact ⟨6, 1, 1, 5, by decide, by decide⟩
  · exact ⟨5, 2, 1, 5, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 4, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 1, 0, 4, by decide, by decide⟩
  · exact ⟨17, 0, 1, 4, by decide, by decide⟩
  · exact ⟨7, 0, 4, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 0, 5, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 5, by decide, by decide⟩
  · exact ⟨8, 1, 1, 5, by decide, by decide⟩
  · exact ⟨21, 3, 2, 2, by decide, by decide⟩
  · exact ⟨17, 2, 1, 4, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 1, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 0, 0, 5, by decide, by decide⟩
  · exact ⟨9, 1, 0, 5, by decide, by decide⟩
  · exact ⟨9, 0, 1, 5, by decide, by decide⟩
  · exact ⟨19, 0, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 5, by decide, by decide⟩
  · exact ⟨10, 1, 0, 5, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 3, 5, by decide, by decide⟩
  · exact ⟨9, 0, 2, 5, by decide, by decide⟩
  · exact ⟨9, 1, 2, 5, by decide, by decide⟩
  · exact ⟨10, 2, 0, 5, by decide, by decide⟩
  · exact ⟨4, 0, 3, 5, by decide, by decide⟩
  · exact ⟨18, 0, 2, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 1, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 3, 5, by decide, by decide⟩
  · exact ⟨19, 0, 1, 4, by decide, by decide⟩

lemma isRep_2_2_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 2 := by
  interval_cases n
  · exact ⟨10, 0, 2, 5, by decide, by decide⟩
  · exact ⟨11, 0, 4, 4, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 1, 2, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 5, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 1, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 1, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 2, 4, by decide, by decide⟩
  · exact ⟨17, 0, 3, 4, by decide, by decide⟩
  · exact ⟨17, 1, 3, 4, by decide, by decide⟩
  · exact ⟨25, 2, 1, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 3, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 1, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 5, by decide, by decide⟩
  · exact ⟨12, 1, 2, 5, by decide, by decide⟩
  · exact ⟨23, 0, 2, 3, by decide, by decide⟩
  · exact ⟨13, 0, 4, 4, by decide, by decide⟩
  · exact ⟨13, 1, 4, 4, by decide, by decide⟩
  · exact ⟨9, 0, 3, 5, by decide, by decide⟩
  · exact ⟨9, 1, 3, 5, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 1, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 5, by decide, by decide⟩
  · exact ⟨24, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 5, by decide, by decide⟩
  · exact ⟨14, 1, 1, 5, by decide, by decide⟩
  · exact ⟨21, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 1, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 1, 1, 4, by decide, by decide⟩
  · exact ⟨14, 2, 0, 5, by decide, by decide⟩
  · exact ⟨24, 2, 1, 3, by decide, by decide⟩
  · exact ⟨14, 2, 1, 5, by decide, by decide⟩
  · exact ⟨21, 3, 3, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 1, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 5, by decide, by decide⟩
  · exact ⟨14, 0, 2, 5, by decide, by decide⟩
  · exact ⟨15, 0, 1, 5, by decide, by decide⟩
  · exact ⟨15, 1, 1, 5, by decide, by decide⟩
  · exact ⟨13, 3, 4, 4, by decide, by decide⟩
  · exact ⟨21, 0, 2, 4, by decide, by decide⟩
  · exact ⟨15, 0, 4, 4, by decide, by decide⟩
  · exact ⟨15, 1, 4, 4, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 3, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 4, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 4, by decide, by decide⟩
  · exact ⟨23, 0, 3, 3, by decide, by decide⟩
  · exact ⟨23, 1, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 5, by decide, by decide⟩
  · exact ⟨16, 1, 0, 5, by decide, by decide⟩
  · exact ⟨16, 0, 1, 5, by decide, by decide⟩
  · exact ⟨16, 1, 1, 5, by decide, by decide⟩
  · exact ⟨27, 2, 1, 1, by decide, by decide⟩
  · exact ⟨22, 2, 1, 4, by decide, by decide⟩
  · exact ⟨20, 0, 3, 4, by decide, by decide⟩
  · exact ⟨5, 0, 4, 5, by decide, by decide⟩
  · exact ⟨27, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 3, by decide, by decide⟩
  · exact ⟨27, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 4, by decide, by decide⟩
  · exact ⟨22, 1, 2, 4, by decide, by decide⟩
  · exact ⟨6, 0, 4, 5, by decide, by decide⟩
  · exact ⟨6, 1, 4, 5, by decide, by decide⟩

lemma isRep_2_2_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 2 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_2_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_2_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_2_241_to_320 n h2 h3
  · exact isRep_2_2_321_to_400 n h3 hn

lemma isRep_2_2_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 2 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_2_upto_80 n h0 h
  · exact isRep_2_2_81_to_400 n h hn

lemma isRep_2_3_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 3 := by
  interval_cases n
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 3, 2, by decide, by decide⟩
  · exact ⟨3, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨5, 0, 1, 3, by decide, by decide⟩
  · exact ⟨9, 0, 3, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨2, 1, 2, 3, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 2, 3, by decide, by decide⟩
  · exact ⟨5, 1, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 1, 0, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 1, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨5, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 3, 3, by decide, by decide⟩
  · exact ⟨5, 1, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩

lemma isRep_2_3_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 3 := by
  interval_cases n
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 2, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 4, 1, by decide, by decide⟩
  · exact ⟨8, 1, 4, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 1, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 1, 3, 3, by decide, by decide⟩
  · exact ⟨18, 2, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 3, 2, by decide, by decide⟩
  · exact ⟨14, 1, 3, 2, by decide, by decide⟩
  · exact ⟨17, 2, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 1, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 1, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 1, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 1, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 2, 4, by decide, by decide⟩
  · exact ⟨16, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨7, 1, 0, 4, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 2, 4, by decide, by decide⟩
  · exact ⟨5, 0, 4, 3, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨20, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨20, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 0, 4, by decide, by decide⟩
  · exact ⟨9, 1, 0, 4, by decide, by decide⟩
  · exact ⟨9, 0, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩

lemma isRep_2_3_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 3 := by
  interval_cases n
  · exact ⟨14, 1, 3, 3, by decide, by decide⟩
  · exact ⟨21, 2, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 2, by decide, by decide⟩
  · exact ⟨8, 0, 2, 4, by decide, by decide⟩
  · exact ⟨8, 0, 4, 3, by decide, by decide⟩
  · exact ⟨8, 1, 4, 3, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 5, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 3, 4, by decide, by decide⟩
  · exact ⟨5, 1, 3, 4, by decide, by decide⟩
  · exact ⟨10, 0, 2, 4, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨5, 0, 5, 0, by decide, by decide⟩
  · exact ⟨5, 1, 5, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 4, by decide, by decide⟩
  · exact ⟨11, 0, 4, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨3, 0, 5, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 4, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 0, 4, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨12, 0, 2, 4, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨21, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 5, 1, by decide, by decide⟩
  · exact ⟨8, 1, 5, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 1, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 1, 2, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 4, by decide, by decide⟩
  · exact ⟨9, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 4, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 3, by decide, by decide⟩
  · exact ⟨20, 0, 2, 3, by decide, by decide⟩
  · exact ⟨10, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 1, 3, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 1, 1, 3, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨24, 1, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 1, 2, 1, by decide, by decide⟩

lemma isRep_2_3_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 3 := by
  interval_cases n
  · exact ⟨19, 0, 4, 1, by decide, by decide⟩
  · exact ⟨19, 1, 4, 1, by decide, by decide⟩
  · exact ⟨18, 0, 4, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨1, 0, 5, 3, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 4, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 0, 3, 4, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 1, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 1, 4, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 5, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 4, by decide, by decide⟩
  · exact ⟨7, 0, 4, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 1, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 4, by decide, by decide⟩
  · exact ⟨21, 0, 4, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 4, by decide, by decide⟩
  · exact ⟨18, 1, 0, 4, by decide, by decide⟩
  · exact ⟨18, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 3, 3, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨26, 1, 2, 0, by decide, by decide⟩
  · exact ⟨17, 2, 2, 4, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 1, 2, 1, by decide, by decide⟩
  · exact ⟨17, 3, 0, 4, by decide, by decide⟩
  · exact ⟨23, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 1, 2, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 0, 0, 5, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 4, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 4, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 0, 0, 5, by decide, by decide⟩
  · exact ⟨11, 0, 4, 4, by decide, by decide⟩
  · exact ⟨4, 0, 1, 5, by decide, by decide⟩
  · exact ⟨22, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 5, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 5, by decide, by decide⟩
  · exact ⟨26, 0, 2, 2, by decide, by decide⟩
  · exact ⟨5, 0, 1, 5, by decide, by decide⟩
  · exact ⟨5, 1, 1, 5, by decide, by decide⟩
  · exact ⟨27, 0, 2, 0, by decide, by decide⟩
  · exact ⟨27, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 5, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨6, 0, 1, 5, by decide, by decide⟩
  · exact ⟨17, 0, 3, 4, by decide, by decide⟩
  · exact ⟨17, 1, 3, 4, by decide, by decide⟩

lemma isRep_2_3_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 3 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_3_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_3_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_3_241_to_320 n h2 h3
  · exact isRep_2_3_321_to_400 n h3 hn

lemma isRep_2_3_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 3 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_3_upto_80 n h0 h
  · exact isRep_2_3_81_to_400 n h hn

lemma isRep_2_4_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 4 := by
  interval_cases n
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 1, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 1, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨4, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨5, 1, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 1, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 1, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 1, 1, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 1, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨2, 1, 2, 3, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 2, 3, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨1, 0, 4, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨2, 0, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨6, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 4, 1, by decide, by decide⟩
  · exact ⟨5, 1, 4, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 1, 3, 1, by decide, by decide⟩
  · exact ⟨5, 2, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩

lemma isRep_2_4_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 4 := by
  interval_cases n
  · exact ⟨1, 0, 4, 2, by decide, by decide⟩
  · exact ⟨1, 1, 4, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 2, by decide, by decide⟩
  · exact ⟨3, 1, 4, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 3, by decide, by decide⟩
  · exact ⟨10, 1, 2, 3, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨6, 1, 4, 2, by decide, by decide⟩
  · exact ⟨6, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 1, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 1, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 1, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 1, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 1, 3, 0, by decide, by decide⟩
  · exact ⟨13, 2, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 3, by decide, by decide⟩
  · exact ⟨10, 1, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 1, 2, 2, by decide, by decide⟩
  · exact ⟨14, 2, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨20, 1, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩

lemma isRep_2_4_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 4 := by
  interval_cases n
  · exact ⟨12, 1, 3, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 1, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 1, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨19, 1, 3, 1, by decide, by decide⟩
  · exact ⟨20, 2, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 5, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 1, 2, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 0, 4, 3, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨5, 1, 1, 4, by decide, by decide⟩
  · exact ⟨2, 0, 2, 4, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 5, 2, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 5, 2, by decide, by decide⟩
  · exact ⟨21, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 5, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 3, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨6, 0, 2, 4, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨5, 0, 5, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 5, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 5, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 1, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 3, 3, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 4, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 1, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩

lemma isRep_2_4_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 4 := by
  interval_cases n
  · exact ⟨20, 1, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨11, 1, 0, 4, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 3, 3, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨12, 1, 0, 4, by decide, by decide⟩
  · exact ⟨12, 0, 1, 4, by decide, by decide⟩
  · exact ⟨10, 0, 5, 2, by decide, by decide⟩
  · exact ⟨11, 0, 2, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨21, 1, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 4, 1, by decide, by decide⟩
  · exact ⟨20, 1, 4, 1, by decide, by decide⟩
  · exact ⟨12, 2, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 4, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨12, 0, 2, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 3, 3, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 4, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 5, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 5, 3, by decide, by decide⟩
  · exact ⟨10, 0, 3, 4, by decide, by decide⟩
  · exact ⟨10, 1, 3, 4, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 0, 5, 3, by decide, by decide⟩
  · exact ⟨4, 1, 5, 3, by decide, by decide⟩
  · exact ⟨20, 0, 4, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 3, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 5, 1, by decide, by decide⟩
  · exact ⟨15, 1, 5, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 3, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨2, 0, 4, 4, by decide, by decide⟩
  · exact ⟨12, 0, 3, 4, by decide, by decide⟩
  · exact ⟨17, 0, 4, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 4, by decide, by decide⟩
  · exact ⟨21, 0, 4, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 4, by decide, by decide⟩
  · exact ⟨16, 1, 1, 4, by decide, by decide⟩
  · exact ⟨12, 2, 3, 4, by decide, by decide⟩
  · exact ⟨17, 2, 4, 3, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 0, 2, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 3, by decide, by decide⟩

lemma isRep_2_4_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 4 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_4_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_4_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_4_241_to_320 n h2 h3
  · exact isRep_2_4_321_to_400 n h3 hn

lemma isRep_2_4_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 4 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_4_upto_80 n h0 h
  · exact isRep_2_4_81_to_400 n h hn

lemma isRep_2_5_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 5 := by
  interval_cases n
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 1, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 1, 1, 2, by decide, by decide⟩
  · exact ⟨10, 3, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 1, 2, 2, by decide, by decide⟩
  · exact ⟨10, 2, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 1, 3, 2, by decide, by decide⟩
  · exact ⟨10, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 1, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 3, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 1, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 1, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 1, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 1, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 4, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 1, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 3, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩

lemma isRep_2_5_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 5 := by
  interval_cases n
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨7, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 2, 3, by decide, by decide⟩
  · exact ⟨5, 1, 2, 3, by decide, by decide⟩
  · exact ⟨15, 2, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 1, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 1, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 2, 3, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 1, 4, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 1, 3, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 3, 2, by decide, by decide⟩
  · exact ⟨14, 1, 3, 2, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 1, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 3, 3, by decide, by decide⟩
  · exact ⟨5, 1, 3, 3, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 1, 3, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 1, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨20, 1, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨13, 1, 4, 0, by decide, by decide⟩
  · exact ⟨12, 2, 0, 3, by decide, by decide⟩
  · exact ⟨15, 2, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 1, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 1, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩

lemma isRep_2_5_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 5 := by
  interval_cases n
  · exact ⟨14, 1, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 1, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 3, 0, by decide, by decide⟩
  · exact ⟨19, 1, 3, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 0, 5, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 5, 1, by decide, by decide⟩
  · exact ⟨3, 1, 5, 1, by decide, by decide⟩
  · exact ⟨15, 2, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨12, 1, 3, 3, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨5, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 1, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 1, 2, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 1, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 1, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 1, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 0, 4, 1, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 1, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 0, 4, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 5, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 1, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 1, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 1, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨22, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 5, 1, by decide, by decide⟩
  · exact ⟨6, 0, 5, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 1, 3, 1, by decide, by decide⟩
  · exact ⟨18, 2, 0, 3, by decide, by decide⟩
  · exact ⟨24, 2, 1, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 1, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 1, 1, 2, by decide, by decide⟩
  · exact ⟨22, 2, 3, 1, by decide, by decide⟩

lemma isRep_2_5_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 5 := by
  interval_cases n
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨2, 1, 0, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨11, 0, 4, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 5, 1, by decide, by decide⟩
  · exact ⟨12, 1, 5, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 1, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 4, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 4, by decide, by decide⟩
  · exact ⟨6, 1, 1, 4, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨7, 1, 0, 4, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 1, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 2, 4, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 3, by decide, by decide⟩
  · exact ⟨20, 0, 2, 3, by decide, by decide⟩
  · exact ⟨20, 1, 2, 3, by decide, by decide⟩
  · exact ⟨14, 2, 5, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 1, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 3, 2, by decide, by decide⟩
  · exact ⟨23, 1, 3, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 1, 2, 1, by decide, by decide⟩
  · exact ⟨21, 2, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 1, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 3, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 3, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 3, 1, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨11, 1, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 3, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 1, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨27, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 4, by decide, by decide⟩
  · exact ⟨6, 1, 3, 4, by decide, by decide⟩
  · exact ⟨5, 2, 3, 4, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 4, by decide, by decide⟩

lemma isRep_2_5_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 5 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_5_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_5_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_5_241_to_320 n h2 h3
  · exact isRep_2_5_321_to_400 n h3 hn

lemma isRep_2_5_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 5 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_5_upto_80 n h0 h
  · exact isRep_2_5_81_to_400 n h hn

lemma isRep_2_6_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 6 := by
  interval_cases n
  · exact ⟨6, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 1, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 1, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 1, 2, 1, by decide, by decide⟩
  · exact ⟨12, 2, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 1, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 1, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨4, 0, 3, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨5, 1, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 1, 3, 2, by decide, by decide⟩
  · exact ⟨5, 2, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 4, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨2, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 1, 3, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 0, by decide, by decide⟩
  · exact ⟨1, 0, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨5, 0, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 1, 3, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 1, 3, 2, by decide, by decide⟩
  · exact ⟨6, 0, 4, 0, by decide, by decide⟩
  · exact ⟨6, 1, 4, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩

lemma isRep_2_6_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 6 := by
  interval_cases n
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 4, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨2, 1, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 1, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 0, by decide, by decide⟩
  · exact ⟨11, 1, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨6, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨7, 0, 4, 2, by decide, by decide⟩
  · exact ⟨7, 1, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 1, 2, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨9, 1, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨20, 1, 2, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 1, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 1, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩

lemma isRep_2_6_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 6 := by
  interval_cases n
  · exact ⟨12, 1, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 1, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨11, 1, 2, 3, by decide, by decide⟩
  · exact ⟨19, 2, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 1, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨1, 0, 5, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨1, 0, 5, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 5, 1, by decide, by decide⟩
  · exact ⟨3, 1, 5, 1, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨5, 0, 5, 0, by decide, by decide⟩
  · exact ⟨4, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 1, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 3, by decide, by decide⟩
  · exact ⟨10, 1, 3, 3, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 1, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 5, 0, by decide, by decide⟩
  · exact ⟨17, 0, 4, 1, by decide, by decide⟩
  · exact ⟨17, 1, 4, 1, by decide, by decide⟩
  · exact ⟨21, 2, 1, 2, by decide, by decide⟩
  · exact ⟨23, 2, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 3, 1, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨2, 0, 4, 3, by decide, by decide⟩
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 4, 2, by decide, by decide⟩
  · exact ⟨15, 1, 4, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 5, 2, by decide, by decide⟩
  · exact ⟨18, 0, 4, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 1, 1, 1, by decide, by decide⟩
  · exact ⟨24, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 3, by decide, by decide⟩
  · exact ⟨20, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 2, by decide, by decide⟩
  · exact ⟨6, 1, 5, 2, by decide, by decide⟩

lemma isRep_2_6_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 6 := by
  interval_cases n
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 1, 2, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 0, by decide, by decide⟩
  · exact ⟨17, 0, 4, 2, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 5, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨23, 1, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 1, 4, 0, by decide, by decide⟩
  · exact ⟨23, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨25, 1, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 5, 2, by decide, by decide⟩
  · exact ⟨20, 0, 4, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 3, by decide, by decide⟩
  · exact ⟨10, 1, 4, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨11, 0, 4, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 1, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 1, 5, 1, by decide, by decide⟩
  · exact ⟨22, 2, 3, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 4, 1, by decide, by decide⟩
  · exact ⟨19, 0, 4, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 3, 3, by decide, by decide⟩
  · exact ⟨15, 0, 5, 0, by decide, by decide⟩
  · exact ⟨15, 1, 5, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 5, 1, by decide, by decide⟩
  · exact ⟨15, 1, 5, 1, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 3, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨22, 1, 4, 0, by decide, by decide⟩
  · exact ⟨25, 2, 1, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨20, 0, 2, 3, by decide, by decide⟩
  · exact ⟨2, 0, 1, 4, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 1, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 1, 1, 4, by decide, by decide⟩
  · exact ⟨3, 2, 0, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨27, 0, 2, 1, by decide, by decide⟩

lemma isRep_2_6_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 6 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_6_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_6_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_6_241_to_320 n h2 h3
  · exact isRep_2_6_321_to_400 n h3 hn

lemma isRep_2_6_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 6 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_6_upto_80 n h0 h
  · exact isRep_2_6_81_to_400 n h hn

lemma isRep_2_7_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 7 := by
  interval_cases n
  · exact ⟨12, 1, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 1, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 1, 1, 2, by decide, by decide⟩
  · exact ⟨5, 3, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 1, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 1, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 3, 0, by decide, by decide⟩
  · exact ⟨10, 1, 3, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 1, 2, 2, by decide, by decide⟩
  · exact ⟨10, 2, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 1, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨5, 1, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 1, 1, 1, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 1, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 1, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 1, by decide, by decide⟩
  · exact ⟨12, 1, 3, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨3, 1, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 1, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 1, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 4, 0, by decide, by decide⟩
  · exact ⟨7, 1, 4, 0, by decide, by decide⟩
  · exact ⟨12, 2, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩

lemma isRep_2_7_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 7 := by
  interval_cases n
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 1, 3, 1, by decide, by decide⟩
  · exact ⟨17, 2, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 1, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 1, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨15, 1, 3, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 1, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 1, 4, 0, by decide, by decide⟩
  · exact ⟨1, 0, 4, 2, by decide, by decide⟩
  · exact ⟨1, 1, 4, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 2, by decide, by decide⟩
  · exact ⟨12, 1, 3, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 1, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 1, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 1, 0, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 1, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 1, 1, 3, by decide, by decide⟩
  · exact ⟨3, 2, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨5, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 1, 2, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 1, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 2, 3, by decide, by decide⟩
  · exact ⟨5, 1, 2, 3, by decide, by decide⟩
  · exact ⟨17, 2, 3, 1, by decide, by decide⟩
  · exact ⟨4, 2, 2, 3, by decide, by decide⟩
  · exact ⟨19, 3, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 3, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨9, 1, 1, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩

lemma isRep_2_7_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 7 := by
  interval_cases n
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 1, 2, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 1, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 3, 3, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨19, 1, 3, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 5, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 3, 3, by decide, by decide⟩
  · exact ⟨5, 1, 3, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨5, 0, 5, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 1, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨5, 0, 5, 1, by decide, by decide⟩
  · exact ⟨5, 1, 5, 1, by decide, by decide⟩
  · exact ⟨20, 2, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 1, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 1, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 5, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 1, 1, 2, by decide, by decide⟩
  · exact ⟨23, 2, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 5, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 1, 1, 3, by decide, by decide⟩
  · exact ⟨10, 0, 3, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 1, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 4, 2, by decide, by decide⟩
  · exact ⟨10, 0, 5, 0, by decide, by decide⟩
  · exact ⟨18, 0, 4, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 0, 5, 1, by decide, by decide⟩
  · exact ⟨10, 1, 5, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 1, 3, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨24, 1, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨19, 1, 4, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 2, by decide, by decide⟩

lemma isRep_2_7_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 7 := by
  interval_cases n
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨12, 1, 3, 3, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 1, 2, 1, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 0, by decide, by decide⟩
  · exact ⟨12, 1, 5, 0, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨23, 1, 3, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 5, 1, by decide, by decide⟩
  · exact ⟨12, 1, 5, 1, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 1, 4, 0, by decide, by decide⟩
  · exact ⟨25, 2, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 1, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 4, 1, by decide, by decide⟩
  · exact ⟨20, 1, 4, 1, by decide, by decide⟩
  · exact ⟨20, 3, 3, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨25, 1, 2, 1, by decide, by decide⟩
  · exact ⟨17, 2, 0, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 1, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 4, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 1, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 1, 3, 2, by decide, by decide⟩
  · exact ⟨20, 3, 4, 0, by decide, by decide⟩
  · exact ⟨21, 0, 4, 1, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨26, 1, 2, 0, by decide, by decide⟩
  · exact ⟨24, 2, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 5, 0, by decide, by decide⟩
  · exact ⟨15, 1, 5, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨24, 1, 2, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 1, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 2, 3, by decide, by decide⟩
  · exact ⟨15, 0, 5, 1, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 1, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 5, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 3, 1, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 4, 1, by decide, by decide⟩
  · exact ⟨22, 1, 4, 1, by decide, by decide⟩
  · exact ⟨22, 3, 3, 2, by decide, by decide⟩
  · exact ⟨25, 2, 1, 2, by decide, by decide⟩
  · exact ⟨12, 2, 5, 2, by decide, by decide⟩
  · exact ⟨16, 0, 5, 1, by decide, by decide⟩
  · exact ⟨27, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 3, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 1, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 1, 0, 3, by decide, by decide⟩

lemma isRep_2_7_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 7 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_7_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_7_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_7_241_to_320 n h2 h3
  · exact isRep_2_7_321_to_400 n h3 hn

lemma isRep_2_7_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 7 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_7_upto_80 n h0 h
  · exact isRep_2_7_81_to_400 n h hn

lemma isRep_2_20_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 20 := by
  interval_cases n
  · exact ⟨9, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 1, 2, 0, by decide, by decide⟩
  · exact ⟨4, 0, 3, 1, by decide, by decide⟩
  · exact ⟨4, 1, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 1, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 1, by decide, by decide⟩
  · exact ⟨6, 1, 3, 1, by decide, by decide⟩
  · exact ⟨5, 2, 3, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 1, 2, 1, by decide, by decide⟩
  · exact ⟨10, 3, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 1, 2, 1, by decide, by decide⟩
  · exact ⟨5, 3, 3, 1, by decide, by decide⟩
  · exact ⟨10, 2, 3, 0, by decide, by decide⟩
  · exact ⟨8, 2, 3, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 1, 3, 1, by decide, by decide⟩
  · exact ⟨2, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 1, 3, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 0, by decide, by decide⟩
  · exact ⟨3, 1, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 1, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 4, 0, by decide, by decide⟩
  · exact ⟨5, 1, 4, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 1, 3, 0, by decide, by decide⟩
  · exact ⟨15, 3, 0, 0, by decide, by decide⟩
  · exact ⟨15, 2, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 4, 0, by decide, by decide⟩
  · exact ⟨6, 1, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 1, 3, 0, by decide, by decide⟩

lemma isRep_2_20_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 20 := by
  interval_cases n
  · exact ⟨1, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 1, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 0, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 1, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 2, by decide, by decide⟩
  · exact ⟨7, 0, 4, 1, by decide, by decide⟩
  · exact ⟨5, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 1, 1, 2, by decide, by decide⟩
  · exact ⟨2, 0, 2, 2, by decide, by decide⟩
  · exact ⟨2, 1, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 1, by decide, by decide⟩
  · exact ⟨8, 1, 4, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨7, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 1, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 1, 1, 2, by decide, by decide⟩
  · exact ⟨19, 2, 1, 0, by decide, by decide⟩
  · exact ⟨18, 2, 1, 1, by decide, by decide⟩
  · exact ⟨15, 2, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨7, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 1, 1, 2, by decide, by decide⟩
  · exact ⟨3, 3, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 1, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 4, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 1, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 1, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 1, 2, 2, by decide, by decide⟩
  · exact ⟨10, 2, 0, 2, by decide, by decide⟩
  · exact ⟨4, 0, 3, 2, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 1, 3, 2, by decide, by decide⟩
  · exact ⟨5, 2, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩

lemma isRep_2_20_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 20 := by
  interval_cases n
  · exact ⟨12, 1, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨11, 1, 2, 2, by decide, by decide⟩
  · exact ⟨19, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 1, 4, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 5, 0, by decide, by decide⟩
  · exact ⟨3, 1, 5, 0, by decide, by decide⟩
  · exact ⟨8, 2, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨4, 0, 5, 0, by decide, by decide⟩
  · exact ⟨4, 1, 5, 0, by decide, by decide⟩
  · exact ⟨12, 2, 2, 2, by decide, by decide⟩
  · exact ⟨22, 2, 1, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 1, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 4, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 0, by decide, by decide⟩
  · exact ⟨6, 1, 5, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 1, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 1, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 1, 1, 2, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 5, 0, by decide, by decide⟩
  · exact ⟨8, 1, 5, 0, by decide, by decide⟩
  · exact ⟨15, 2, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 1, 2, 1, by decide, by decide⟩
  · exact ⟨2, 0, 4, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨23, 1, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 2, by decide, by decide⟩
  · exact ⟨9, 0, 5, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 1, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 4, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨5, 0, 4, 2, by decide, by decide⟩
  · exact ⟨5, 1, 4, 2, by decide, by decide⟩
  · exact ⟨21, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 5, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨22, 1, 3, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨6, 1, 4, 2, by decide, by decide⟩
  · exact ⟨5, 2, 4, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨24, 1, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩

lemma isRep_2_20_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 20 := by
  interval_cases n
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 1, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 4, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 5, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 1, 3, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨24, 1, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨20, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 3, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨25, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨10, 1, 4, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 5, 1, by decide, by decide⟩
  · exact ⟨12, 1, 5, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨14, 1, 5, 0, by decide, by decide⟩
  · exact ⟨23, 3, 3, 0, by decide, by decide⟩
  · exact ⟨20, 0, 4, 1, by decide, by decide⟩
  · exact ⟨21, 0, 4, 0, by decide, by decide⟩
  · exact ⟨21, 1, 4, 0, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨25, 1, 2, 1, by decide, by decide⟩
  · exact ⟨14, 2, 5, 0, by decide, by decide⟩
  · exact ⟨24, 4, 0, 0, by decide, by decide⟩
  · exact ⟨20, 3, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨26, 1, 2, 0, by decide, by decide⟩
  · exact ⟨25, 2, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 1, 5, 1, by decide, by decide⟩
  · exact ⟨19, 3, 0, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 3, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨22, 1, 4, 0, by decide, by decide⟩
  · exact ⟨14, 2, 5, 1, by decide, by decide⟩
  · exact ⟨24, 4, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 1, 2, 1, by decide, by decide⟩
  · exact ⟨22, 2, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 1, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨27, 0, 2, 0, by decide, by decide⟩
  · exact ⟨27, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 5, 5, 0, by decide, by decide⟩
  · exact ⟨20, 3, 0, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 3, 1, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩

lemma isRep_2_20_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 20 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_20_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_20_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_20_241_to_320 n h2 h3
  · exact isRep_2_20_321_to_400 n h3 hn

lemma isRep_2_20_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 20 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_20_upto_80 n h0 h
  · exact isRep_2_20_81_to_400 n h hn

lemma isRep_2_21_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 21 := by
  interval_cases n
  · exact ⟨3, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 2, 0, 1, by decide, by decide⟩
  · exact ⟨4, 0, 3, 1, by decide, by decide⟩
  · exact ⟨4, 1, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 3, 1, by decide, by decide⟩
  · exact ⟨6, 1, 3, 1, by decide, by decide⟩
  · exact ⟨8, 2, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 1, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 1, 2, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 0, by decide, by decide⟩
  · exact ⟨10, 1, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 1, 2, 1, by decide, by decide⟩
  · exact ⟨10, 2, 3, 0, by decide, by decide⟩
  · exact ⟨13, 3, 0, 0, by decide, by decide⟩
  · exact ⟨8, 2, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 1, 1, 0, by decide, by decide⟩
  · exact ⟨3, 4, 3, 0, by decide, by decide⟩
  · exact ⟨9, 4, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨2, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 1, 3, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 0, by decide, by decide⟩
  · exact ⟨3, 1, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 1, 1, 0, by decide, by decide⟩
  · exact ⟨12, 2, 3, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 1, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 1, 3, 0, by decide, by decide⟩
  · exact ⟨15, 3, 0, 0, by decide, by decide⟩
  · exact ⟨14, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 0, by decide, by decide⟩
  · exact ⟨1, 0, 4, 1, by decide, by decide⟩
  · exact ⟨1, 1, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩

lemma isRep_2_21_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 21 := by
  interval_cases n
  · exact ⟨17, 2, 0, 0, by decide, by decide⟩
  · exact ⟨6, 5, 2, 0, by decide, by decide⟩
  · exact ⟨17, 2, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 1, 4, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 1, 3, 1, by decide, by decide⟩
  · exact ⟨15, 3, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 4, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 1, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 4, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 2, by decide, by decide⟩
  · exact ⟨4, 1, 0, 2, by decide, by decide⟩
  · exact ⟨4, 0, 1, 2, by decide, by decide⟩
  · exact ⟨4, 1, 1, 2, by decide, by decide⟩
  · exact ⟨17, 2, 0, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 2, by decide, by decide⟩
  · exact ⟨5, 1, 0, 2, by decide, by decide⟩
  · exact ⟨5, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 1, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨18, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 2, by decide, by decide⟩
  · exact ⟨7, 1, 0, 2, by decide, by decide⟩
  · exact ⟨7, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 2, 2, by decide, by decide⟩
  · exact ⟨5, 1, 2, 2, by decide, by decide⟩
  · exact ⟨17, 3, 0, 1, by decide, by decide⟩
  · exact ⟨18, 2, 1, 1, by decide, by decide⟩
  · exact ⟨15, 2, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨18, 1, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 1, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨9, 1, 1, 2, by decide, by decide⟩
  · exact ⟨19, 3, 0, 0, by decide, by decide⟩
  · exact ⟨20, 2, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 1, 2, 2, by decide, by decide⟩
  · exact ⟨15, 3, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 1, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨9, 1, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 1, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨5, 1, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩

lemma isRep_2_21_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 21 := by
  interval_cases n
  · exact ⟨13, 1, 4, 1, by decide, by decide⟩
  · exact ⟨11, 2, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨19, 0, 3, 0, by decide, by decide⟩
  · exact ⟨19, 1, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 1, 1, 2, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨1, 0, 5, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 5, 0, by decide, by decide⟩
  · exact ⟨3, 1, 5, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨4, 0, 5, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 1, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨19, 1, 3, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 0, by decide, by decide⟩
  · exact ⟨1, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 1, 1, 0, by decide, by decide⟩
  · exact ⟨1, 2, 5, 1, by decide, by decide⟩
  · exact ⟨17, 0, 4, 0, by decide, by decide⟩
  · exact ⟨17, 1, 4, 0, by decide, by decide⟩
  · exact ⟨14, 2, 1, 2, by decide, by decide⟩
  · exact ⟨23, 2, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 5, 0, by decide, by decide⟩
  · exact ⟨8, 1, 5, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 1, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨23, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 2, 5, 0, by decide, by decide⟩
  · exact ⟨9, 0, 5, 0, by decide, by decide⟩
  · exact ⟨9, 1, 5, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 1, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 1, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 1, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 5, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨22, 1, 3, 0, by decide, by decide⟩
  · exact ⟨13, 6, 1, 0, by decide, by decide⟩
  · exact ⟨24, 2, 1, 0, by decide, by decide⟩
  · exact ⟨5, 0, 4, 2, by decide, by decide⟩
  · exact ⟨5, 1, 4, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨23, 1, 2, 1, by decide, by decide⟩
  · exact ⟨22, 2, 3, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨19, 1, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩

lemma isRep_2_21_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 21 := by
  interval_cases n
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 4, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 5, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 1, 3, 1, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨23, 1, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 4, 2, by decide, by decide⟩
  · exact ⟨8, 1, 4, 2, by decide, by decide⟩
  · exact ⟨10, 2, 5, 1, by decide, by decide⟩
  · exact ⟨25, 2, 1, 0, by decide, by decide⟩
  · exact ⟨22, 2, 3, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨18, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 1, 3, 2, by decide, by decide⟩
  · exact ⟨6, 3, 4, 2, by decide, by decide⟩
  · exact ⟨24, 2, 2, 1, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 5, 1, by decide, by decide⟩
  · exact ⟨12, 1, 5, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨26, 1, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 1, 2, 2, by decide, by decide⟩
  · exact ⟨12, 2, 5, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 1, 1, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨25, 1, 2, 1, by decide, by decide⟩
  · exact ⟨24, 3, 2, 1, by decide, by decide⟩
  · exact ⟨20, 3, 4, 0, by decide, by decide⟩
  · exact ⟨19, 2, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨26, 1, 2, 0, by decide, by decide⟩
  · exact ⟨15, 3, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 5, 0, by decide, by decide⟩
  · exact ⟨15, 1, 5, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 1, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 1, 5, 1, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 3, 0, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 4, 0, by decide, by decide⟩
  · exact ⟨22, 1, 4, 0, by decide, by decide⟩
  · exact ⟨24, 2, 3, 1, by decide, by decide⟩
  · exact ⟨14, 2, 5, 1, by decide, by decide⟩
  · exact ⟨19, 3, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 5, 0, by decide, by decide⟩
  · exact ⟨13, 0, 4, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 1, 2, 1, by decide, by decide⟩
  · exact ⟨10, 4, 5, 1, by decide, by decide⟩
  · exact ⟨15, 0, 5, 1, by decide, by decide⟩
  · exact ⟨15, 1, 5, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨27, 0, 2, 0, by decide, by decide⟩
  · exact ⟨27, 1, 2, 0, by decide, by decide⟩
  · exact ⟨26, 2, 2, 1, by decide, by decide⟩
  · exact ⟨15, 3, 5, 0, by decide, by decide⟩
  · exact ⟨14, 5, 0, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 3, 1, by decide, by decide⟩

lemma isRep_2_21_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 21 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_21_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_21_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_21_241_to_320 n h2 h3
  · exact isRep_2_21_321_to_400 n h3 hn

lemma isRep_2_21_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 21 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_21_upto_80 n h0 h
  · exact isRep_2_21_81_to_400 n h hn

lemma isRep_2_34_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 2 34 := by
  interval_cases n
  · exact ⟨9, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 3, 1, 0, by decide, by decide⟩
  · exact ⟨6, 4, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 1, 2, 1, by decide, by decide⟩
  · exact ⟨12, 2, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 1, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 2, 1, by decide, by decide⟩
  · exact ⟨9, 1, 2, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 1, by decide, by decide⟩
  · exact ⟨4, 0, 3, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 3, 1, by decide, by decide⟩
  · exact ⟨5, 1, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 1, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 0, by decide, by decide⟩
  · exact ⟨10, 1, 3, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 1, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 1, 2, 1, by decide, by decide⟩
  · exact ⟨13, 3, 0, 0, by decide, by decide⟩
  · exact ⟨10, 4, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 1, 1, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨1, 0, 4, 0, by decide, by decide⟩
  · exact ⟨1, 1, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 4, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 0, by decide, by decide⟩
  · exact ⟨3, 1, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 1, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 1, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 1, 3, 0, by decide, by decide⟩
  · exact ⟨14, 2, 0, 1, by decide, by decide⟩
  · exact ⟨14, 3, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 4, 0, by decide, by decide⟩
  · exact ⟨6, 1, 4, 0, by decide, by decide⟩
  · exact ⟨10, 2, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 1, 1, 1, by decide, by decide⟩
  · exact ⟨2, 3, 4, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 1, 3, 0, by decide, by decide⟩

lemma isRep_2_34_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 2 34 := by
  interval_cases n
  · exact ⟨17, 2, 0, 0, by decide, by decide⟩
  · exact ⟨15, 2, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 4, 1, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 0, 3, 1, by decide, by decide⟩
  · exact ⟨12, 1, 3, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨15, 1, 3, 0, by decide, by decide⟩
  · exact ⟨3, 2, 4, 1, by decide, by decide⟩
  · exact ⟨5, 0, 4, 1, by decide, by decide⟩
  · exact ⟨5, 1, 4, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 1, 3, 1, by decide, by decide⟩
  · exact ⟨18, 2, 1, 0, by decide, by decide⟩
  · exact ⟨15, 2, 3, 0, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 1, 4, 0, by decide, by decide⟩
  · exact ⟨5, 2, 4, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 0, by decide, by decide⟩
  · exact ⟨11, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 3, 2, 0, by decide, by decide⟩
  · exact ⟨17, 2, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 4, 1, by decide, by decide⟩
  · exact ⟨8, 1, 4, 1, by decide, by decide⟩
  · exact ⟨19, 2, 1, 0, by decide, by decide⟩
  · exact ⟨14, 2, 3, 1, by decide, by decide⟩
  · exact ⟨11, 2, 4, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 1, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 1, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 1, 1, 0, by decide, by decide⟩
  · exact ⟨19, 2, 2, 0, by decide, by decide⟩
  · exact ⟨18, 2, 1, 1, by decide, by decide⟩
  · exact ⟨15, 2, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨10, 1, 4, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨13, 1, 4, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨18, 1, 2, 1, by decide, by decide⟩
  · exact ⟨14, 4, 3, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 1, by decide, by decide⟩
  · exact ⟨11, 1, 4, 1, by decide, by decide⟩
  · exact ⟨17, 3, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨15, 3, 3, 1, by decide, by decide⟩
  · exact ⟨11, 2, 4, 1, by decide, by decide⟩
  · exact ⟨20, 3, 0, 0, by decide, by decide⟩
  · exact ⟨15, 4, 3, 0, by decide, by decide⟩
  · exact ⟨21, 2, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩

lemma isRep_2_34_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 2 34 := by
  interval_cases n
  · exact ⟨17, 0, 3, 1, by decide, by decide⟩
  · exact ⟨17, 1, 3, 1, by decide, by decide⟩
  · exact ⟨13, 4, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 1, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 1, 4, 0, by decide, by decide⟩
  · exact ⟨16, 4, 2, 1, by decide, by decide⟩
  · exact ⟨1, 0, 5, 0, by decide, by decide⟩
  · exact ⟨1, 1, 5, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 5, 0, by decide, by decide⟩
  · exact ⟨3, 1, 5, 0, by decide, by decide⟩
  · exact ⟨21, 3, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 2, 1, by decide, by decide⟩
  · exact ⟨20, 1, 2, 1, by decide, by decide⟩
  · exact ⟨8, 4, 4, 1, by decide, by decide⟩
  · exact ⟨22, 2, 1, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 1, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 1, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 5, 0, by decide, by decide⟩
  · exact ⟨6, 1, 5, 0, by decide, by decide⟩
  · exact ⟨1, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 1, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 1, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 2, by decide, by decide⟩
  · exact ⟨4, 1, 0, 2, by decide, by decide⟩
  · exact ⟨4, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 5, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 5, 1, by decide, by decide⟩
  · exact ⟨2, 0, 2, 2, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 1, 1, 2, by decide, by decide⟩
  · exact ⟨22, 2, 1, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 2, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 1, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 1, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 5, 0, by decide, by decide⟩
  · exact ⟨10, 1, 5, 0, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 2, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 1, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 1, 1, 1, by decide, by decide⟩
  · exact ⟨22, 3, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 4, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 5, 1, by decide, by decide⟩

lemma isRep_2_34_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 2 34 := by
  interval_cases n
  · exact ⟨8, 1, 5, 1, by decide, by decide⟩
  · exact ⟨6, 3, 1, 2, by decide, by decide⟩
  · exact ⟨17, 2, 4, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 5, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨23, 1, 3, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 2, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 5, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨25, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 1, 2, 2, by decide, by decide⟩
  · exact ⟨19, 3, 4, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 1, 3, 2, by decide, by decide⟩
  · exact ⟨25, 2, 2, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 5, 0, by decide, by decide⟩
  · exact ⟨14, 1, 5, 0, by decide, by decide⟩
  · exact ⟨23, 3, 3, 0, by decide, by decide⟩
  · exact ⟨12, 2, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨26, 1, 2, 0, by decide, by decide⟩
  · exact ⟨25, 2, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 5, 0, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 4, 1, by decide, by decide⟩
  · exact ⟨20, 1, 4, 1, by decide, by decide⟩
  · exact ⟨12, 2, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨25, 1, 2, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨10, 1, 3, 2, by decide, by decide⟩
  · exact ⟨25, 2, 2, 1, by decide, by decide⟩
  · exact ⟨8, 4, 5, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 5, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 5, 1, by decide, by decide⟩
  · exact ⟨14, 1, 5, 1, by decide, by decide⟩
  · exact ⟨23, 3, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 1, 1, 2, by decide, by decide⟩
  · exact ⟨24, 2, 3, 1, by decide, by decide⟩
  · exact ⟨14, 2, 5, 1, by decide, by decide⟩
  · exact ⟨9, 3, 3, 2, by decide, by decide⟩
  · exact ⟨20, 3, 4, 1, by decide, by decide⟩
  · exact ⟨15, 2, 0, 2, by decide, by decide⟩

lemma isRep_2_34_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 2 34 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_2_34_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_2_34_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_2_34_241_to_320 n h2 h3
  · exact isRep_2_34_321_to_400 n h3 hn

lemma isRep_2_34_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 2 34 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_2_34_upto_80 n h0 h
  · exact isRep_2_34_81_to_400 n h hn

lemma isRep_3_3_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 3 3 := by
  interval_cases n
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨1, 1, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨1, 0, 1, 3, by decide, by decide⟩
  · exact ⟨1, 1, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 1, 0, 3, by decide, by decide⟩
  · exact ⟨12, 2, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 1, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 1, 1, 3, by decide, by decide⟩
  · exact ⟨11, 2, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 1, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 0, 2, 3, by decide, by decide⟩
  · exact ⟨1, 1, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 3, by decide, by decide⟩
  · exact ⟨7, 1, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 1, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 1, 0, 2, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 1, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨15, 2, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 1, 0, 2, by decide, by decide⟩
  · exact ⟨15, 2, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨7, 0, 2, 3, by decide, by decide⟩
  · exact ⟨7, 1, 2, 3, by decide, by decide⟩
  · exact ⟨14, 3, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 3, 1, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 1, 0, 2, by decide, by decide⟩
  · exact ⟨1, 4, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 1, 0, 3, by decide, by decide⟩
  · exact ⟨8, 2, 2, 3, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 1, 1, 3, by decide, by decide⟩
  · exact ⟨15, 2, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 2, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩

lemma isRep_3_3_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 3 3 := by
  interval_cases n
  · exact ⟨16, 1, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 1, 1, 2, by decide, by decide⟩
  · exact ⟨2, 0, 3, 3, by decide, by decide⟩
  · exact ⟨2, 1, 3, 3, by decide, by decide⟩
  · exact ⟨12, 2, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 1, 2, 2, by decide, by decide⟩
  · exact ⟨12, 2, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 1, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨13, 1, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 2, 0, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 1, 1, 2, by decide, by decide⟩
  · exact ⟨18, 2, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 1, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 1, 0, 3, by decide, by decide⟩
  · exact ⟨17, 2, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨16, 2, 2, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 1, 0, 4, by decide, by decide⟩
  · exact ⟨16, 4, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨4, 1, 0, 4, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 1, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 1, 0, 4, by decide, by decide⟩
  · exact ⟨15, 2, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨15, 2, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 1, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 1, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨7, 1, 0, 4, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨7, 1, 1, 4, by decide, by decide⟩
  · exact ⟨15, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 0, 2, 4, by decide, by decide⟩
  · exact ⟨4, 1, 2, 4, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 1, 0, 4, by decide, by decide⟩
  · exact ⟨3, 2, 2, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨15, 2, 2, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 2, 0, 4, by decide, by decide⟩
  · exact ⟨9, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨19, 1, 2, 2, by decide, by decide⟩
  · exact ⟨9, 0, 1, 4, by decide, by decide⟩

lemma isRep_3_3_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 3 3 := by
  interval_cases n
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 1, 2, 3, by decide, by decide⟩
  · exact ⟨20, 3, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 2, 4, by decide, by decide⟩
  · exact ⟨7, 1, 2, 4, by decide, by decide⟩
  · exact ⟨19, 2, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 1, 0, 4, by decide, by decide⟩
  · exact ⟨16, 2, 2, 3, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨10, 1, 1, 4, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨11, 1, 1, 4, by decide, by decide⟩
  · exact ⟨21, 2, 0, 2, by decide, by decide⟩
  · exact ⟨22, 2, 0, 1, by decide, by decide⟩
  · exact ⟨19, 3, 2, 2, by decide, by decide⟩
  · exact ⟨11, 2, 0, 4, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨14, 1, 3, 3, by decide, by decide⟩
  · exact ⟨11, 2, 1, 4, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 1, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 1, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 1, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 1, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 1, 0, 4, by decide, by decide⟩
  · exact ⟨22, 2, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨13, 1, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 3, 4, by decide, by decide⟩
  · exact ⟨5, 1, 3, 4, by decide, by decide⟩
  · exact ⟨23, 2, 1, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 1, 0, 3, by decide, by decide⟩
  · exact ⟨15, 5, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 1, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 4, by decide, by decide⟩
  · exact ⟨16, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 1, 3, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 1, 2, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 2, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 0, 2, 4, by decide, by decide⟩
  · exact ⟨13, 1, 2, 4, by decide, by decide⟩
  · exact ⟨8, 0, 3, 4, by decide, by decide⟩
  · exact ⟨8, 1, 3, 4, by decide, by decide⟩
  · exact ⟨24, 2, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨21, 1, 0, 3, by decide, by decide⟩
  · exact ⟨24, 2, 1, 1, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 1, 1, 3, by decide, by decide⟩
  · exact ⟨8, 2, 3, 4, by decide, by decide⟩
  · exact ⟨9, 0, 3, 4, by decide, by decide⟩
  · exact ⟨9, 1, 3, 4, by decide, by decide⟩
  · exact ⟨21, 2, 0, 3, by decide, by decide⟩

lemma isRep_3_3_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 3 3 := by
  interval_cases n
  · exact ⟨14, 0, 2, 4, by decide, by decide⟩
  · exact ⟨14, 1, 2, 4, by decide, by decide⟩
  · exact ⟨21, 2, 1, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 3, 0, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨25, 1, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 3, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 1, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨22, 1, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 3, 4, by decide, by decide⟩
  · exact ⟨11, 1, 3, 4, by decide, by decide⟩
  · exact ⟨18, 2, 3, 3, by decide, by decide⟩
  · exact ⟨22, 2, 0, 3, by decide, by decide⟩
  · exact ⟨23, 4, 0, 1, by decide, by decide⟩
  · exact ⟨21, 2, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 1, 0, 4, by decide, by decide⟩
  · exact ⟨11, 2, 3, 4, by decide, by decide⟩
  · exact ⟨17, 0, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 1, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 1, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 2, 1, 4, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 1, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 1, 1, 3, by decide, by decide⟩
  · exact ⟨26, 2, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 0, 3, 4, by decide, by decide⟩
  · exact ⟨13, 1, 3, 4, by decide, by decide⟩
  · exact ⟨18, 0, 1, 4, by decide, by decide⟩
  · exact ⟨18, 1, 1, 4, by decide, by decide⟩
  · exact ⟨23, 2, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 4, by decide, by decide⟩
  · exact ⟨17, 1, 2, 4, by decide, by decide⟩
  · exact ⟨18, 2, 0, 4, by decide, by decide⟩
  · exact ⟨20, 0, 3, 3, by decide, by decide⟩
  · exact ⟨25, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 1, 2, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 0, 0, 5, by decide, by decide⟩
  · exact ⟨1, 1, 0, 5, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨1, 0, 1, 5, by decide, by decide⟩
  · exact ⟨1, 1, 1, 5, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 4, by decide, by decide⟩
  · exact ⟨19, 1, 0, 4, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 5, by decide, by decide⟩
  · exact ⟨4, 1, 0, 5, by decide, by decide⟩
  · exact ⟨18, 0, 2, 4, by decide, by decide⟩
  · exact ⟨4, 0, 1, 5, by decide, by decide⟩
  · exact ⟨4, 1, 1, 5, by decide, by decide⟩
  · exact ⟨5, 0, 0, 5, by decide, by decide⟩
  · exact ⟨5, 1, 0, 5, by decide, by decide⟩
  · exact ⟨27, 2, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 1, 5, by decide, by decide⟩
  · exact ⟨4, 0, 4, 4, by decide, by decide⟩
  · exact ⟨4, 1, 4, 4, by decide, by decide⟩
  · exact ⟨6, 0, 0, 5, by decide, by decide⟩
  · exact ⟨6, 1, 0, 5, by decide, by decide⟩
  · exact ⟨5, 2, 0, 5, by decide, by decide⟩
  · exact ⟨6, 0, 1, 5, by decide, by decide⟩
  · exact ⟨1, 0, 2, 5, by decide, by decide⟩

lemma isRep_3_3_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 3 3 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_3_3_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_3_3_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_3_3_241_to_320 n h2 h3
  · exact isRep_3_3_321_to_400 n h3 hn

lemma isRep_3_3_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 3 3 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_3_3_upto_80 n h0 h
  · exact isRep_3_3_81_to_400 n h hn

lemma isRep_3_4_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 3 4 := by
  interval_cases n
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 1, by decide, by decide⟩
  · exact ⟨7, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 3, 1, by decide, by decide⟩
  · exact ⟨2, 1, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 1, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨5, 0, 3, 0, by decide, by decide⟩
  · exact ⟨5, 1, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨11, 1, 0, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 1, 2, 0, by decide, by decide⟩
  · exact ⟨5, 2, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 1, 2, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 2, 0, by decide, by decide⟩
  · exact ⟨2, 0, 3, 2, by decide, by decide⟩
  · exact ⟨3, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 1, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 3, 1, by decide, by decide⟩
  · exact ⟨9, 1, 3, 1, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨7, 0, 3, 2, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 1, 0, 3, by decide, by decide⟩
  · exact ⟨3, 2, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨8, 1, 3, 2, by decide, by decide⟩
  · exact ⟨11, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩

lemma isRep_3_4_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 3 4 := by
  interval_cases n
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 1, 2, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨16, 1, 2, 1, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨10, 1, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 1, 0, 2, by decide, by decide⟩
  · exact ⟨16, 3, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 1, 3, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 3, 2, by decide, by decide⟩
  · exact ⟨11, 1, 3, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 1, 2, 1, by decide, by decide⟩
  · exact ⟨18, 2, 0, 1, by decide, by decide⟩
  · exact ⟨15, 2, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨18, 1, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 1, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 4, 0, by decide, by decide⟩
  · exact ⟨5, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 4, 1, by decide, by decide⟩
  · exact ⟨5, 1, 4, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨19, 1, 2, 1, by decide, by decide⟩
  · exact ⟨7, 0, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 3, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 2, 3, by decide, by decide⟩
  · exact ⟨7, 0, 4, 1, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 1, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨15, 1, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨5, 0, 4, 2, by decide, by decide⟩
  · exact ⟨5, 1, 4, 2, by decide, by decide⟩

lemma isRep_3_4_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 3 4 := by
  interval_cases n
  · exact ⟨9, 0, 4, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 1, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 1, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 1, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨12, 0, 4, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 1, 0, 4, by decide, by decide⟩
  · exact ⟨3, 2, 1, 4, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨19, 0, 3, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨6, 1, 0, 4, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨7, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 1, 1, 2, by decide, by decide⟩
  · exact ⟨4, 0, 2, 4, by decide, by decide⟩
  · exact ⟨20, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 0, 0, 4, by decide, by decide⟩
  · exact ⟨8, 1, 0, 4, by decide, by decide⟩
  · exact ⟨14, 0, 3, 3, by decide, by decide⟩
  · exact ⟨8, 0, 1, 4, by decide, by decide⟩
  · exact ⟨8, 1, 1, 4, by decide, by decide⟩
  · exact ⟨14, 0, 4, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 1, 0, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 4, by decide, by decide⟩
  · exact ⟨12, 0, 4, 2, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨3, 0, 4, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 2, by decide, by decide⟩
  · exact ⟨4, 0, 4, 3, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨21, 1, 3, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 4, by decide, by decide⟩
  · exact ⟨13, 0, 4, 2, by decide, by decide⟩
  · exact ⟨8, 0, 2, 4, by decide, by decide⟩
  · exact ⟨8, 1, 2, 4, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 1, 0, 3, by decide, by decide⟩
  · exact ⟨21, 2, 3, 0, by decide, by decide⟩

lemma isRep_3_4_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 3 4 := by
  interval_cases n
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨20, 0, 3, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨24, 3, 0, 0, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨20, 2, 3, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨24, 1, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 4, 3, by decide, by decide⟩
  · exact ⟨12, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 3, 4, by decide, by decide⟩
  · exact ⟨2, 1, 3, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨3, 0, 3, 4, by decide, by decide⟩
  · exact ⟨21, 0, 3, 2, by decide, by decide⟩
  · exact ⟨17, 0, 4, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 4, by decide, by decide⟩
  · exact ⟨13, 0, 0, 4, by decide, by decide⟩
  · exact ⟨13, 1, 0, 4, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨5, 0, 3, 4, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 1, 1, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 1, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 0, 3, 4, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨18, 0, 4, 1, by decide, by decide⟩
  · exact ⟨18, 1, 4, 1, by decide, by decide⟩
  · exact ⟨22, 2, 0, 3, by decide, by decide⟩
  · exact ⟨3, 3, 3, 4, by decide, by decide⟩
  · exact ⟨13, 0, 2, 4, by decide, by decide⟩
  · exact ⟨13, 1, 2, 4, by decide, by decide⟩
  · exact ⟨8, 0, 3, 4, by decide, by decide⟩
  · exact ⟨8, 1, 3, 4, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 0, 4, by decide, by decide⟩
  · exact ⟨17, 0, 4, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 4, by decide, by decide⟩
  · exact ⟨1, 0, 5, 1, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨23, 0, 0, 3, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 1, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 3, 2, by decide, by decide⟩
  · exact ⟨5, 0, 5, 0, by decide, by decide⟩
  · exact ⟨13, 0, 4, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 4, by decide, by decide⟩
  · exact ⟨16, 1, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 5, 1, by decide, by decide⟩
  · exact ⟨16, 0, 1, 4, by decide, by decide⟩
  · exact ⟨6, 0, 5, 0, by decide, by decide⟩
  · exact ⟨6, 1, 5, 0, by decide, by decide⟩
  · exact ⟨5, 2, 5, 0, by decide, by decide⟩
  · exact ⟨20, 0, 3, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 4, by decide, by decide⟩

lemma isRep_3_4_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 3 4 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_3_4_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_3_4_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_3_4_241_to_320 n h2 h3
  · exact isRep_3_4_321_to_400 n h3 hn

lemma isRep_3_4_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 3 4 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_3_4_upto_80 n h0 h
  · exact isRep_3_4_81_to_400 n h hn

lemma isRep_3_5_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 3 5 := by
  interval_cases n
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩
  · exact ⟨1, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 1, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨3, 0, 3, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨2, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 2, by decide, by decide⟩
  · exact ⟨7, 1, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨5, 0, 3, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨12, 1, 2, 0, by decide, by decide⟩
  · exact ⟨13, 2, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 2, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 1, 0, 1, by decide, by decide⟩
  · exact ⟨9, 3, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨7, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 1, 2, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨9, 0, 3, 0, by decide, by decide⟩
  · exact ⟨3, 0, 3, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 1, 0, 2, by decide, by decide⟩
  · exact ⟨15, 2, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 1, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 1, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 1, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 1, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 2, 1, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 1, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 3, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 3, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩

lemma isRep_3_5_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 3 5 := by
  interval_cases n
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨7, 0, 0, 3, by decide, by decide⟩
  · exact ⟨12, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨7, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 1, 1, 3, by decide, by decide⟩
  · exact ⟨15, 2, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 1, 2, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨13, 1, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 1, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 1, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 1, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 3, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 3, by decide, by decide⟩
  · exact ⟨7, 1, 2, 3, by decide, by decide⟩
  · exact ⟨2, 3, 2, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 1, 3, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 1, 1, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 3, 2, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 4, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨11, 1, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨5, 0, 4, 0, by decide, by decide⟩
  · exact ⟨5, 1, 4, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨7, 0, 4, 0, by decide, by decide⟩
  · exact ⟨7, 1, 4, 0, by decide, by decide⟩
  · exact ⟨16, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 1, 3, 1, by decide, by decide⟩
  · exact ⟨12, 2, 1, 3, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨13, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 1, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩

lemma isRep_3_5_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 3 5 := by
  interval_cases n
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 4, 1, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨7, 0, 3, 3, by decide, by decide⟩
  · exact ⟨7, 1, 3, 3, by decide, by decide⟩
  · exact ⟨3, 2, 4, 2, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 1, 4, 0, by decide, by decide⟩
  · exact ⟨15, 2, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 1, 0, 2, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 4, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 1, 2, 3, by decide, by decide⟩
  · exact ⟨22, 2, 0, 1, by decide, by decide⟩
  · exact ⟨14, 3, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 2, by decide, by decide⟩
  · exact ⟨8, 1, 4, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 1, 0, 2, by decide, by decide⟩
  · exact ⟨14, 5, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 1, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 1, 2, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 1, 1, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨13, 0, 4, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 1, 1, 1, by decide, by decide⟩
  · exact ⟨16, 4, 3, 1, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 1, 0, 3, by decide, by decide⟩
  · exact ⟨22, 2, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 4, 0, by decide, by decide⟩
  · exact ⟨11, 0, 4, 2, by decide, by decide⟩
  · exact ⟨11, 1, 4, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨24, 1, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 4, 1, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨24, 1, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨13, 0, 3, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 0, 4, 2, by decide, by decide⟩
  · exact ⟨19, 0, 3, 2, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨17, 1, 2, 3, by decide, by decide⟩
  · exact ⟨18, 2, 0, 3, by decide, by decide⟩
  · exact ⟨13, 2, 3, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 2, 2, by decide, by decide⟩
  · exact ⟨22, 1, 2, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨23, 1, 1, 2, by decide, by decide⟩

lemma isRep_3_5_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 3 5 := by
  interval_cases n
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 1, 0, 4, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 0, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨3, 1, 0, 4, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨3, 0, 1, 4, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 1, 3, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 0, 3, 0, by decide, by decide⟩
  · exact ⟨5, 0, 0, 4, by decide, by decide⟩
  · exact ⟨15, 0, 3, 3, by decide, by decide⟩
  · exact ⟨14, 0, 4, 2, by decide, by decide⟩
  · exact ⟨5, 0, 1, 4, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 4, by decide, by decide⟩
  · exact ⟨5, 0, 4, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 4, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨20, 1, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 2, 4, by decide, by decide⟩
  · exact ⟨7, 0, 0, 4, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨3, 0, 2, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 3, 2, by decide, by decide⟩
  · exact ⟨21, 1, 3, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 4, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨23, 0, 3, 0, by decide, by decide⟩
  · exact ⟨23, 1, 3, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 1, 1, 1, by decide, by decide⟩
  · exact ⟨22, 3, 3, 0, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 4, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨21, 1, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨21, 1, 1, 3, by decide, by decide⟩
  · exact ⟨18, 2, 4, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 4, by decide, by decide⟩
  · exact ⟨7, 1, 2, 4, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨10, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 0, 5, 0, by decide, by decide⟩
  · exact ⟨1, 1, 5, 0, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨27, 1, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 4, 0, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨27, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 4, 2, by decide, by decide⟩
  · exact ⟨11, 0, 0, 4, by decide, by decide⟩
  · exact ⟨18, 0, 3, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 0, 1, 4, by decide, by decide⟩
  · exact ⟨21, 0, 2, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 1, 0, 2, by decide, by decide⟩
  · exact ⟨11, 0, 4, 3, by decide, by decide⟩
  · exact ⟨26, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 5, 1, by decide, by decide⟩
  · exact ⟨6, 0, 5, 0, by decide, by decide⟩
  · exact ⟨23, 0, 3, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 4, by decide, by decide⟩
  · exact ⟨10, 0, 2, 4, by decide, by decide⟩
  · exact ⟨10, 1, 2, 4, by decide, by decide⟩

lemma isRep_3_5_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 3 5 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_3_5_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_3_5_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_3_5_241_to_320 n h2 h3
  · exact isRep_3_5_321_to_400 n h3 hn

lemma isRep_3_5_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 3 5 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_3_5_upto_80 n h0 h
  · exact isRep_3_5_81_to_400 n h hn

lemma isRep_3_6_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 3 6 := by
  interval_cases n
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 2, 2, by decide, by decide⟩
  · exact ⟨4, 1, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 1, by decide, by decide⟩
  · exact ⟨10, 1, 2, 1, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 3, 1, by decide, by decide⟩
  · exact ⟨1, 1, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 1, 0, by decide, by decide⟩
  · exact ⟨13, 1, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨13, 2, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 1, 1, by decide, by decide⟩
  · exact ⟨13, 1, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 1, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨10, 1, 1, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 3, 0, by decide, by decide⟩
  · exact ⟨7, 1, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 1, 0, 1, by decide, by decide⟩
  · exact ⟨14, 2, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 2, 0, by decide, by decide⟩
  · exact ⟨13, 1, 2, 0, by decide, by decide⟩
  · exact ⟨11, 0, 1, 2, by decide, by decide⟩
  · exact ⟨11, 1, 1, 2, by decide, by decide⟩
  · exact ⟨14, 2, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨13, 0, 2, 1, by decide, by decide⟩
  · exact ⟨13, 1, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨15, 1, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 2, 2, by decide, by decide⟩
  · exact ⟨10, 1, 2, 2, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 3, 2, by decide, by decide⟩
  · exact ⟨1, 1, 3, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 1, by decide, by decide⟩
  · exact ⟨9, 1, 3, 1, by decide, by decide⟩
  · exact ⟨15, 2, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 1, 0, 2, by decide, by decide⟩
  · exact ⟨11, 3, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 1, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 0, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 3, 0, by decide, by decide⟩
  · exact ⟨11, 1, 3, 0, by decide, by decide⟩
  · exact ⟨10, 4, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 1, 2, 1, by decide, by decide⟩
  · exact ⟨15, 2, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨17, 1, 0, 0, by decide, by decide⟩
  · exact ⟨11, 2, 3, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 3, 2, by decide, by decide⟩
  · exact ⟨7, 1, 3, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩

lemma isRep_3_6_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 3 6 := by
  interval_cases n
  · exact ⟨16, 1, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨1, 1, 0, 3, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨1, 0, 1, 3, by decide, by decide⟩
  · exact ⟨1, 1, 1, 3, by decide, by decide⟩
  · exact ⟨15, 0, 0, 2, by decide, by decide⟩
  · exact ⟨15, 1, 0, 2, by decide, by decide⟩
  · exact ⟨17, 2, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 1, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 1, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨13, 1, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 1, by decide, by decide⟩
  · exact ⟨18, 1, 1, 1, by decide, by decide⟩
  · exact ⟨18, 2, 1, 0, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 1, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨16, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 1, 1, 2, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 1, 0, 0, by decide, by decide⟩
  · exact ⟨15, 0, 2, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 1, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 1, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨4, 0, 4, 0, by decide, by decide⟩
  · exact ⟨4, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 1, 1, 2, by decide, by decide⟩
  · exact ⟨8, 2, 0, 3, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 1, 2, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨17, 2, 1, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 1, 2, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 1, 0, 3, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 1, 3, by decide, by decide⟩
  · exact ⟨10, 1, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 1, 3, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨7, 0, 4, 1, by decide, by decide⟩
  · exact ⟨7, 1, 4, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨11, 1, 0, 3, by decide, by decide⟩
  · exact ⟨18, 2, 1, 2, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨21, 1, 0, 0, by decide, by decide⟩
  · exact ⟨17, 2, 2, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨11, 2, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨19, 1, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩

lemma isRep_3_6_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 3 6 := by
  interval_cases n
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 1, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨1, 0, 3, 3, by decide, by decide⟩
  · exact ⟨1, 1, 3, 3, by decide, by decide⟩
  · exact ⟨2, 0, 3, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 0, by decide, by decide⟩
  · exact ⟨10, 1, 4, 0, by decide, by decide⟩
  · exact ⟨15, 0, 3, 2, by decide, by decide⟩
  · exact ⟨4, 0, 4, 2, by decide, by decide⟩
  · exact ⟨4, 1, 4, 2, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 1, 0, 0, by decide, by decide⟩
  · exact ⟨21, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 1, 1, 0, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 1, 1, 1, by decide, by decide⟩
  · exact ⟨12, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 1, 3, 2, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨7, 0, 4, 2, by decide, by decide⟩
  · exact ⟨7, 1, 4, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 3, 0, by decide, by decide⟩
  · exact ⟨19, 1, 3, 0, by decide, by decide⟩
  · exact ⟨16, 2, 3, 2, by decide, by decide⟩
  · exact ⟨10, 3, 4, 0, by decide, by decide⟩
  · exact ⟨14, 2, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 1, 2, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨21, 1, 0, 2, by decide, by decide⟩
  · exact ⟨10, 4, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 1, 2, 1, by decide, by decide⟩
  · exact ⟨23, 0, 1, 1, by decide, by decide⟩
  · exact ⟨23, 1, 1, 1, by decide, by decide⟩
  · exact ⟨21, 2, 0, 2, by decide, by decide⟩
  · exact ⟨9, 0, 3, 3, by decide, by decide⟩
  · exact ⟨13, 0, 4, 1, by decide, by decide⟩
  · exact ⟨13, 1, 4, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 3, by decide, by decide⟩
  · exact ⟨14, 1, 2, 3, by decide, by decide⟩
  · exact ⟨23, 2, 1, 1, by decide, by decide⟩
  · exact ⟨14, 3, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨10, 1, 4, 2, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨16, 0, 0, 3, by decide, by decide⟩
  · exact ⟨16, 1, 0, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨22, 1, 0, 2, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨22, 1, 1, 2, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨24, 1, 0, 1, by decide, by decide⟩
  · exact ⟨24, 2, 0, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨24, 1, 1, 1, by decide, by decide⟩
  · exact ⟨24, 2, 1, 0, by decide, by decide⟩
  · exact ⟨21, 0, 3, 0, by decide, by decide⟩
  · exact ⟨21, 1, 3, 0, by decide, by decide⟩
  · exact ⟨24, 2, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 3, by decide, by decide⟩
  · exact ⟨17, 1, 0, 3, by decide, by decide⟩
  · exact ⟨24, 2, 1, 1, by decide, by decide⟩
  · exact ⟨17, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 0, 3, 2, by decide, by decide⟩
  · exact ⟨19, 1, 3, 2, by decide, by decide⟩

lemma isRep_3_6_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 3 6 := by
  interval_cases n
  · exact ⟨12, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 1, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨25, 1, 1, 0, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨25, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 0, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨25, 1, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 3, by decide, by decide⟩
  · exact ⟨18, 1, 1, 3, by decide, by decide⟩
  · exact ⟨24, 2, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 3, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨22, 1, 3, 1, by decide, by decide⟩
  · exact ⟨25, 2, 1, 1, by decide, by decide⟩
  · exact ⟨21, 4, 0, 2, by decide, by decide⟩
  · exact ⟨18, 2, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 4, 0, by decide, by decide⟩
  · exact ⟨17, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 2, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨25, 1, 2, 0, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 1, 0, 3, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 3, by decide, by decide⟩
  · exact ⟨19, 1, 1, 3, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 1, 0, 1, by decide, by decide⟩
  · exact ⟨26, 2, 0, 0, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 1, 1, 1, by decide, by decide⟩
  · exact ⟨26, 2, 1, 0, by decide, by decide⟩
  · exact ⟨23, 0, 3, 1, by decide, by decide⟩
  · exact ⟨4, 0, 4, 3, by decide, by decide⟩
  · exact ⟨4, 1, 4, 3, by decide, by decide⟩
  · exact ⟨17, 3, 2, 3, by decide, by decide⟩
  · exact ⟨22, 3, 3, 1, by decide, by decide⟩
  · exact ⟨26, 2, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 4, 1, by decide, by decide⟩
  · exact ⟨18, 1, 4, 1, by decide, by decide⟩
  · exact ⟨23, 2, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 3, by decide, by decide⟩
  · exact ⟨25, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 1, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 2, by decide, by decide⟩
  · exact ⟨25, 1, 1, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 3, 3, by decide, by decide⟩
  · exact ⟨16, 1, 3, 3, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 1, 3, 2, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨1, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 1, 0, 4, by decide, by decide⟩
  · exact ⟨2, 0, 0, 4, by decide, by decide⟩
  · exact ⟨1, 0, 1, 4, by decide, by decide⟩
  · exact ⟨1, 1, 1, 4, by decide, by decide⟩
  · exact ⟨3, 0, 0, 4, by decide, by decide⟩
  · exact ⟨4, 0, 5, 1, by decide, by decide⟩
  · exact ⟨4, 1, 5, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 3, by decide, by decide⟩
  · exact ⟨4, 0, 0, 4, by decide, by decide⟩
  · exact ⟨4, 1, 0, 4, by decide, by decide⟩
  · exact ⟨21, 0, 1, 3, by decide, by decide⟩
  · exact ⟨4, 0, 1, 4, by decide, by decide⟩
  · exact ⟨4, 1, 1, 4, by decide, by decide⟩
  · exact ⟨26, 0, 0, 2, by decide, by decide⟩
  · exact ⟨26, 1, 0, 2, by decide, by decide⟩

lemma isRep_3_6_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 3 6 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_3_6_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_3_6_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_3_6_241_to_320 n h2 h3
  · exact isRep_3_6_321_to_400 n h3 hn

lemma isRep_3_6_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 3 6 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_3_6_upto_80 n h0 h
  · exact isRep_3_6_81_to_400 n h hn

lemma isRep_4_10_81_to_160 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 160) : IsRep n 4 10 := by
  interval_cases n
  · exact ⟨1, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 1, 0, 2, by decide, by decide⟩
  · exact ⟨1, 0, 1, 2, by decide, by decide⟩
  · exact ⟨3, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 1, 2, by decide, by decide⟩
  · exact ⟨12, 0, 0, 1, by decide, by decide⟩
  · exact ⟨12, 1, 0, 1, by decide, by decide⟩
  · exact ⟨4, 0, 0, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 1, by decide, by decide⟩
  · exact ⟨12, 1, 1, 1, by decide, by decide⟩
  · exact ⟨4, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 0, 0, 2, by decide, by decide⟩
  · exact ⟨5, 1, 0, 2, by decide, by decide⟩
  · exact ⟨10, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 0, by decide, by decide⟩
  · exact ⟨5, 0, 1, 2, by decide, by decide⟩
  · exact ⟨5, 1, 1, 2, by decide, by decide⟩
  · exact ⟨13, 0, 0, 1, by decide, by decide⟩
  · exact ⟨13, 1, 0, 1, by decide, by decide⟩
  · exact ⟨5, 2, 0, 2, by decide, by decide⟩
  · exact ⟨9, 3, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 1, 0, 0, by decide, by decide⟩
  · exact ⟨5, 2, 1, 2, by decide, by decide⟩
  · exact ⟨7, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 2, 0, by decide, by decide⟩
  · exact ⟨2, 0, 3, 0, by decide, by decide⟩
  · exact ⟨7, 0, 1, 2, by decide, by decide⟩
  · exact ⟨1, 0, 2, 2, by decide, by decide⟩
  · exact ⟨3, 0, 3, 0, by decide, by decide⟩
  · exact ⟨14, 0, 0, 1, by decide, by decide⟩
  · exact ⟨8, 0, 0, 2, by decide, by decide⟩
  · exact ⟨8, 1, 0, 2, by decide, by decide⟩
  · exact ⟨3, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 0, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 3, 1, by decide, by decide⟩
  · exact ⟨4, 0, 2, 2, by decide, by decide⟩
  · exact ⟨13, 0, 2, 0, by decide, by decide⟩
  · exact ⟨15, 0, 1, 0, by decide, by decide⟩
  · exact ⟨9, 0, 0, 2, by decide, by decide⟩
  · exact ⟨9, 1, 0, 2, by decide, by decide⟩
  · exact ⟨5, 0, 2, 2, by decide, by decide⟩
  · exact ⟨4, 0, 3, 1, by decide, by decide⟩
  · exact ⟨9, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 0, 1, by decide, by decide⟩
  · exact ⟨15, 1, 0, 1, by decide, by decide⟩
  · exact ⟨15, 2, 1, 0, by decide, by decide⟩
  · exact ⟨13, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 1, by decide, by decide⟩
  · exact ⟨10, 0, 0, 2, by decide, by decide⟩
  · exact ⟨16, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 2, 0, by decide, by decide⟩
  · exact ⟨14, 1, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 1, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 0, by decide, by decide⟩
  · exact ⟨16, 1, 1, 0, by decide, by decide⟩
  · exact ⟨15, 2, 1, 1, by decide, by decide⟩
  · exact ⟨10, 2, 0, 2, by decide, by decide⟩
  · exact ⟨8, 0, 3, 0, by decide, by decide⟩
  · exact ⟨8, 1, 3, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 1, by decide, by decide⟩
  · exact ⟨14, 0, 2, 1, by decide, by decide⟩
  · exact ⟨8, 0, 2, 2, by decide, by decide⟩
  · exact ⟨8, 1, 2, 2, by decide, by decide⟩
  · exact ⟨16, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 1, 1, 1, by decide, by decide⟩
  · exact ⟨15, 0, 2, 0, by decide, by decide⟩
  · exact ⟨17, 0, 0, 0, by decide, by decide⟩
  · exact ⟨8, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 1, 3, 1, by decide, by decide⟩
  · exact ⟨8, 2, 2, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 0, by decide, by decide⟩
  · exact ⟨12, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 1, 0, 2, by decide, by decide⟩
  · exact ⟨15, 2, 2, 0, by decide, by decide⟩

lemma isRep_4_10_161_to_240 (n : ℕ) (h0 : 161 ≤ n) (hn : n ≤ 240) : IsRep n 4 10 := by
  interval_cases n
  · exact ⟨17, 2, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 2, by decide, by decide⟩
  · exact ⟨17, 0, 0, 1, by decide, by decide⟩
  · exact ⟨17, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 2, 1, 0, by decide, by decide⟩
  · exact ⟨12, 2, 0, 2, by decide, by decide⟩
  · exact ⟨17, 0, 1, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 0, by decide, by decide⟩
  · exact ⟨16, 1, 2, 0, by decide, by decide⟩
  · exact ⟨12, 2, 1, 2, by decide, by decide⟩
  · exact ⟨18, 0, 0, 0, by decide, by decide⟩
  · exact ⟨18, 1, 0, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 1, by decide, by decide⟩
  · exact ⟨11, 0, 3, 0, by decide, by decide⟩
  · exact ⟨18, 0, 1, 0, by decide, by decide⟩
  · exact ⟨18, 1, 1, 0, by decide, by decide⟩
  · exact ⟨16, 3, 1, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 1, by decide, by decide⟩
  · exact ⟨16, 1, 2, 1, by decide, by decide⟩
  · exact ⟨17, 3, 0, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 1, by decide, by decide⟩
  · exact ⟨18, 1, 0, 1, by decide, by decide⟩
  · exact ⟨18, 2, 1, 0, by decide, by decide⟩
  · exact ⟨11, 0, 3, 1, by decide, by decide⟩
  · exact ⟨14, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 0, by decide, by decide⟩
  · exact ⟨12, 1, 3, 0, by decide, by decide⟩
  · exact ⟨15, 4, 1, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 2, by decide, by decide⟩
  · exact ⟨19, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 3, 2, by decide, by decide⟩
  · exact ⟨2, 1, 3, 2, by decide, by decide⟩
  · exact ⟨14, 2, 0, 2, by decide, by decide⟩
  · exact ⟨19, 0, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 2, 1, by decide, by decide⟩
  · exact ⟨12, 0, 3, 1, by decide, by decide⟩
  · exact ⟨12, 1, 3, 1, by decide, by decide⟩
  · exact ⟨4, 0, 3, 2, by decide, by decide⟩
  · exact ⟨13, 0, 3, 0, by decide, by decide⟩
  · exact ⟨19, 0, 0, 1, by decide, by decide⟩
  · exact ⟨19, 1, 0, 1, by decide, by decide⟩
  · exact ⟨19, 2, 1, 0, by decide, by decide⟩
  · exact ⟨18, 0, 2, 0, by decide, by decide⟩
  · exact ⟨19, 0, 1, 1, by decide, by decide⟩
  · exact ⟨19, 1, 1, 1, by decide, by decide⟩
  · exact ⟨4, 2, 3, 2, by decide, by decide⟩
  · exact ⟨13, 2, 3, 0, by decide, by decide⟩
  · exact ⟨19, 2, 0, 1, by decide, by decide⟩
  · exact ⟨13, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 0, 0, by decide, by decide⟩
  · exact ⟨20, 1, 0, 0, by decide, by decide⟩
  · exact ⟨19, 2, 1, 1, by decide, by decide⟩
  · exact ⟨18, 0, 2, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 0, by decide, by decide⟩
  · exact ⟨20, 1, 1, 0, by decide, by decide⟩
  · exact ⟨16, 0, 0, 2, by decide, by decide⟩
  · exact ⟨14, 0, 2, 2, by decide, by decide⟩
  · exact ⟨14, 1, 2, 2, by decide, by decide⟩
  · exact ⟨4, 5, 1, 2, by decide, by decide⟩
  · exact ⟨20, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 1, 0, 1, by decide, by decide⟩
  · exact ⟨19, 0, 2, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 1, by decide, by decide⟩
  · exact ⟨20, 0, 1, 1, by decide, by decide⟩
  · exact ⟨20, 1, 1, 1, by decide, by decide⟩
  · exact ⟨13, 3, 3, 0, by decide, by decide⟩
  · exact ⟨19, 3, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 3, 0, by decide, by decide⟩
  · exact ⟨15, 1, 3, 0, by decide, by decide⟩
  · exact ⟨19, 2, 2, 0, by decide, by decide⟩
  · exact ⟨21, 0, 0, 0, by decide, by decide⟩
  · exact ⟨19, 0, 2, 1, by decide, by decide⟩
  · exact ⟨17, 0, 0, 2, by decide, by decide⟩
  · exact ⟨17, 1, 0, 2, by decide, by decide⟩
  · exact ⟨21, 0, 1, 0, by decide, by decide⟩
  · exact ⟨21, 1, 1, 0, by decide, by decide⟩
  · exact ⟨17, 0, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 3, 1, by decide, by decide⟩
  · exact ⟨15, 1, 3, 1, by decide, by decide⟩
  · exact ⟨19, 2, 2, 1, by decide, by decide⟩

lemma isRep_4_10_241_to_320 (n : ℕ) (h0 : 241 ≤ n) (hn : n ≤ 320) : IsRep n 4 10 := by
  interval_cases n
  · exact ⟨21, 0, 0, 1, by decide, by decide⟩
  · exact ⟨20, 0, 2, 0, by decide, by decide⟩
  · exact ⟨10, 0, 3, 2, by decide, by decide⟩
  · exact ⟨16, 0, 3, 0, by decide, by decide⟩
  · exact ⟨21, 0, 1, 1, by decide, by decide⟩
  · exact ⟨21, 1, 1, 1, by decide, by decide⟩
  · exact ⟨20, 3, 0, 1, by decide, by decide⟩
  · exact ⟨16, 0, 2, 2, by decide, by decide⟩
  · exact ⟨16, 1, 2, 2, by decide, by decide⟩
  · exact ⟨20, 2, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 2, 1, by decide, by decide⟩
  · exact ⟨22, 0, 0, 0, by decide, by decide⟩
  · exact ⟨16, 0, 3, 1, by decide, by decide⟩
  · exact ⟨18, 0, 1, 2, by decide, by decide⟩
  · exact ⟨18, 1, 1, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 0, by decide, by decide⟩
  · exact ⟨22, 1, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 4, 0, by decide, by decide⟩
  · exact ⟨2, 1, 4, 0, by decide, by decide⟩
  · exact ⟨17, 0, 3, 0, by decide, by decide⟩
  · exact ⟨3, 0, 4, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 1, by decide, by decide⟩
  · exact ⟨22, 1, 0, 1, by decide, by decide⟩
  · exact ⟨17, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 3, 2, by decide, by decide⟩
  · exact ⟨22, 0, 1, 1, by decide, by decide⟩
  · exact ⟨22, 1, 1, 1, by decide, by decide⟩
  · exact ⟨2, 0, 4, 1, by decide, by decide⟩
  · exact ⟨19, 0, 0, 2, by decide, by decide⟩
  · exact ⟨1, 0, 0, 3, by decide, by decide⟩
  · exact ⟨3, 0, 4, 1, by decide, by decide⟩
  · exact ⟨2, 0, 0, 3, by decide, by decide⟩
  · exact ⟨19, 0, 1, 2, by decide, by decide⟩
  · exact ⟨1, 0, 1, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 0, by decide, by decide⟩
  · exact ⟨2, 0, 1, 3, by decide, by decide⟩
  · exact ⟨2, 1, 1, 3, by decide, by decide⟩
  · exact ⟨18, 0, 3, 0, by decide, by decide⟩
  · exact ⟨4, 0, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 4, 1, by decide, by decide⟩
  · exact ⟨5, 1, 4, 1, by decide, by decide⟩
  · exact ⟨18, 0, 2, 2, by decide, by decide⟩
  · exact ⟨4, 0, 1, 3, by decide, by decide⟩
  · exact ⟨5, 0, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 0, 1, by decide, by decide⟩
  · exact ⟨6, 0, 4, 1, by decide, by decide⟩
  · exact ⟨6, 1, 4, 1, by decide, by decide⟩
  · exact ⟨5, 0, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 0, 2, by decide, by decide⟩
  · exact ⟨6, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 0, 4, 0, by decide, by decide⟩
  · exact ⟨14, 0, 3, 2, by decide, by decide⟩
  · exact ⟨20, 0, 1, 2, by decide, by decide⟩
  · exact ⟨6, 0, 1, 3, by decide, by decide⟩
  · exact ⟨6, 1, 1, 3, by decide, by decide⟩
  · exact ⟨5, 2, 1, 3, by decide, by decide⟩
  · exact ⟨7, 0, 0, 3, by decide, by decide⟩
  · exact ⟨7, 1, 0, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 0, by decide, by decide⟩
  · exact ⟨9, 0, 4, 0, by decide, by decide⟩
  · exact ⟨7, 0, 1, 3, by decide, by decide⟩
  · exact ⟨1, 0, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 0, by decide, by decide⟩
  · exact ⟨2, 0, 2, 3, by decide, by decide⟩
  · exact ⟨8, 0, 0, 3, by decide, by decide⟩
  · exact ⟨8, 1, 0, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 0, by decide, by decide⟩
  · exact ⟨23, 1, 2, 0, by decide, by decide⟩
  · exact ⟨24, 0, 0, 1, by decide, by decide⟩
  · exact ⟨21, 0, 0, 2, by decide, by decide⟩
  · exact ⟨4, 0, 2, 3, by decide, by decide⟩
  · exact ⟨4, 1, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 1, 1, by decide, by decide⟩
  · exact ⟨9, 0, 0, 3, by decide, by decide⟩
  · exact ⟨9, 1, 0, 3, by decide, by decide⟩
  · exact ⟨5, 0, 2, 3, by decide, by decide⟩
  · exact ⟨23, 0, 2, 1, by decide, by decide⟩
  · exact ⟨9, 0, 1, 3, by decide, by decide⟩
  · exact ⟨9, 1, 1, 3, by decide, by decide⟩

lemma isRep_4_10_321_to_400 (n : ℕ) (h0 : 321 ≤ n) (hn : n ≤ 400) : IsRep n 4 10 := by
  interval_cases n
  · exact ⟨10, 0, 4, 1, by decide, by decide⟩
  · exact ⟨20, 0, 2, 2, by decide, by decide⟩
  · exact ⟨6, 0, 2, 3, by decide, by decide⟩
  · exact ⟨16, 0, 3, 2, by decide, by decide⟩
  · exact ⟨25, 0, 0, 0, by decide, by decide⟩
  · exact ⟨25, 1, 0, 0, by decide, by decide⟩
  · exact ⟨9, 2, 1, 3, by decide, by decide⟩
  · exact ⟨20, 0, 3, 1, by decide, by decide⟩
  · exact ⟨25, 0, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 2, 3, by decide, by decide⟩
  · exact ⟨7, 1, 2, 3, by decide, by decide⟩
  · exact ⟨24, 0, 2, 0, by decide, by decide⟩
  · exact ⟨22, 0, 0, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 0, by decide, by decide⟩
  · exact ⟨25, 0, 0, 1, by decide, by decide⟩
  · exact ⟨11, 0, 0, 3, by decide, by decide⟩
  · exact ⟨22, 0, 1, 2, by decide, by decide⟩
  · exact ⟨8, 0, 2, 3, by decide, by decide⟩
  · exact ⟨25, 0, 1, 1, by decide, by decide⟩
  · exact ⟨11, 0, 1, 3, by decide, by decide⟩
  · exact ⟨17, 0, 3, 2, by decide, by decide⟩
  · exact ⟨24, 0, 2, 1, by decide, by decide⟩
  · exact ⟨21, 0, 2, 2, by decide, by decide⟩
  · exact ⟨12, 0, 4, 1, by decide, by decide⟩
  · exact ⟨12, 1, 4, 1, by decide, by decide⟩
  · exact ⟨4, 0, 4, 2, by decide, by decide⟩
  · exact ⟨9, 0, 2, 3, by decide, by decide⟩
  · exact ⟨12, 0, 0, 3, by decide, by decide⟩
  · exact ⟨21, 0, 3, 1, by decide, by decide⟩
  · exact ⟨21, 1, 3, 1, by decide, by decide⟩
  · exact ⟨26, 0, 0, 0, by decide, by decide⟩
  · exact ⟨12, 0, 1, 3, by decide, by decide⟩
  · exact ⟨12, 1, 1, 3, by decide, by decide⟩
  · exact ⟨4, 2, 4, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 0, by decide, by decide⟩
  · exact ⟨23, 0, 0, 2, by decide, by decide⟩
  · exact ⟨25, 0, 2, 0, by decide, by decide⟩
  · exact ⟨25, 1, 2, 0, by decide, by decide⟩
  · exact ⟨18, 0, 3, 2, by decide, by decide⟩
  · exact ⟨23, 0, 1, 2, by decide, by decide⟩
  · exact ⟨26, 0, 0, 1, by decide, by decide⟩
  · exact ⟨26, 1, 0, 1, by decide, by decide⟩
  · exact ⟨26, 2, 1, 0, by decide, by decide⟩
  · exact ⟨7, 0, 4, 2, by decide, by decide⟩
  · exact ⟨26, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 1, 1, 1, by decide, by decide⟩
  · exact ⟨25, 0, 2, 1, by decide, by decide⟩
  · exact ⟨11, 0, 2, 3, by decide, by decide⟩
  · exact ⟨11, 1, 2, 3, by decide, by decide⟩
  · exact ⟨21, 3, 2, 2, by decide, by decide⟩
  · exact ⟨22, 0, 3, 1, by decide, by decide⟩
  · exact ⟨8, 0, 4, 2, by decide, by decide⟩
  · exact ⟨8, 1, 4, 2, by decide, by decide⟩
  · exact ⟨9, 3, 2, 3, by decide, by decide⟩
  · exact ⟨14, 0, 0, 3, by decide, by decide⟩
  · exact ⟨15, 0, 4, 0, by decide, by decide⟩
  · exact ⟨15, 1, 4, 0, by decide, by decide⟩
  · exact ⟨27, 0, 0, 0, by decide, by decide⟩
  · exact ⟨14, 0, 1, 3, by decide, by decide⟩
  · exact ⟨24, 0, 0, 2, by decide, by decide⟩
  · exact ⟨2, 0, 3, 3, by decide, by decide⟩
  · exact ⟨27, 0, 1, 0, by decide, by decide⟩
  · exact ⟨26, 0, 2, 0, by decide, by decide⟩
  · exact ⟨24, 0, 1, 2, by decide, by decide⟩
  · exact ⟨24, 1, 1, 2, by decide, by decide⟩
  · exact ⟨15, 0, 4, 1, by decide, by decide⟩
  · exact ⟨15, 1, 4, 1, by decide, by decide⟩
  · exact ⟨27, 0, 0, 1, by decide, by decide⟩
  · exact ⟨27, 1, 0, 1, by decide, by decide⟩
  · exact ⟨15, 0, 0, 3, by decide, by decide⟩
  · exact ⟨10, 0, 4, 2, by decide, by decide⟩
  · exact ⟨27, 0, 1, 1, by decide, by decide⟩
  · exact ⟨26, 0, 2, 1, by decide, by decide⟩
  · exact ⟨15, 0, 1, 3, by decide, by decide⟩
  · exact ⟨15, 1, 1, 3, by decide, by decide⟩
  · exact ⟨27, 2, 0, 1, by decide, by decide⟩
  · exact ⟨22, 4, 0, 2, by decide, by decide⟩
  · exact ⟨20, 0, 3, 2, by decide, by decide⟩
  · exact ⟨6, 0, 3, 3, by decide, by decide⟩
  · exact ⟨6, 1, 3, 3, by decide, by decide⟩

lemma isRep_4_10_81_to_400 (n : ℕ) (h0 : 81 ≤ n) (hn : n ≤ 400) : IsRep n 4 10 := by
  rcases le_or_gt n 160 with h | h
  · exact isRep_4_10_81_to_160 n h0 h
  rcases le_or_gt n 240 with h2 | h2
  · exact isRep_4_10_161_to_240 n h h2
  rcases le_or_gt n 320 with h3 | h3
  · exact isRep_4_10_241_to_320 n h2 h3
  · exact isRep_4_10_321_to_400 n h3 hn

lemma isRep_4_10_upto_400 (n : ℕ) (h0 : 0 < n) (hn : n ≤ 400) : IsRep n 4 10 := by
  rcases le_or_gt n 80 with h | h
  · exact isRep_4_10_upto_80 n h0 h
  · exact isRep_4_10_81_to_400 n h hn

/-- `m` is a weighted sum of three nonnegative cubes with coefficients `1,b,c`. -/
def IsC3 (m b c : ℕ) : Prop :=
  ∃ x y z : ℕ, m = x ^ 3 + b * y ^ 3 + c * z ^ 3

lemma isC3_zero (b c : ℕ) : IsC3 0 b c :=
  ⟨0, 0, 0, by simp⟩

lemma isC3_one (b c : ℕ) : IsC3 1 b c :=
  ⟨1, 0, 0, by simp⟩

lemma isRep_of_isC3_add_triangle {n b c w : ℕ} (hw : 0 < w)
    (h : IsC3 (n - triangle_number w) b c)
    (hle : triangle_number w ≤ n) : IsRep n b c := by
  obtain ⟨x, y, z, hxyz⟩ := h
  refine ⟨w, x, y, z, hw, ?_⟩
  omega

lemma isRep_of_backup {n b c w j x y z : ℕ}
    (hj : j < w) (hwj : 0 < w - j)
    (h : n - triangle_number (w - j) = x ^ 3 + b * y ^ 3 + c * z ^ 3)
    (hle : triangle_number (w - j) ≤ n) :
    IsRep n b c :=
  ⟨w - j, x, y, z, hwj, by omega⟩

/-- If the greedy remainder is itself a weighted cube-sum, we are done. -/
lemma isRep_of_rem_isC3 (n b c : ℕ) (hn : 1 ≤ n)
    (h : IsC3 (n - triangle_number (greedy_w n)) b c) : IsRep n b c := by
  have ⟨hle, _⟩ := greedy_w_spec n hn
  exact isRep_of_isC3_add_triangle (greedy_w_pos n hn) h hle

/-- The cube increment: `(t+1)^3 = t^3 + 3t^2 + 3t + 1`. -/
lemma cube_succ (t : ℕ) : (t + 1) ^ 3 = t ^ 3 + 3 * t ^ 2 + 3 * t + 1 := by
  ring

lemma cube_succ_sub (t : ℕ) : (t + 1) ^ 3 - t ^ 3 = 3 * t ^ 2 + 3 * t + 1 := by
  have := cube_succ t
  omega

/-- Greedy remainder after removing the largest cube `≤ m`. -/
lemma pow_nthRoot_three_le (m : ℕ) : (Nat.nthRoot 3 m) ^ 3 ≤ m :=
  Nat.pow_nthRoot_le (Or.inl (by decide : (3 : ℕ) ≠ 0))

lemma sub_nthRoot_cube_lt (m : ℕ) :
    m - (Nat.nthRoot 3 m) ^ 3 < 3 * (Nat.nthRoot 3 m) ^ 2 + 3 * (Nat.nthRoot 3 m) + 1 := by
  set t := Nat.nthRoot 3 m
  have hle : t ^ 3 ≤ m := pow_nthRoot_three_le m
  have hlt : m < (t + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide : (3 : ℕ) ≠ 0) m
  have hsucc := cube_succ t
  omega

/--
For the form `x^3 + y^3 + 2z^3`, every interval `[N, N + 3*(N.nthRoot 3 + 1)^2]`
contains a value of the form. This is an explicit gap bound.
-/
lemma exists_c3_12_in_interval (N : ℕ) :
    ∃ C x y z : ℕ, N ≤ C ∧ C ≤ N + 3 * (Nat.nthRoot 3 N + 1) ^ 2
      ∧ C = x ^ 3 + y ^ 3 + 2 * z ^ 3 := by
  -- Greedy: peel the largest `2z^3 ≤ N`, then the largest `x^3`, then the next `y^3`.
  set z := Nat.nthRoot 3 (N / 2)
  have hz3 : z ^ 3 ≤ N / 2 := pow_nthRoot_three_le (N / 2)
  have h2z : 2 * z ^ 3 ≤ N := by
    have : z ^ 3 ≤ N / 2 := hz3
    omega
  set R := N - 2 * z ^ 3
  have hR : R ≤ N := Nat.sub_le _ _
  set x := Nat.nthRoot 3 R
  have hx3 : x ^ 3 ≤ R := pow_nthRoot_three_le R
  set R2 := R - x ^ 3
  have hR2 : R2 ≤ R := Nat.sub_le _ _
  -- Take the least cube `y^3 ≥ R2`.
  set y := Nat.nthRoot 3 R2
  by_cases hExact : y ^ 3 = R2
  · refine ⟨N, x, y, z, le_rfl, ?_, ?_⟩
    · exact Nat.le_add_right _ _
    · have : N = x ^ 3 + y ^ 3 + 2 * z ^ 3 := by
        have h1 : N = R + 2 * z ^ 3 := by omega
        have h2 : R = x ^ 3 + R2 := by omega
        omega
      exact this
  · -- `y^3 < R2 < (y+1)^3`; use `y+1`.
    have hy_le : y ^ 3 ≤ R2 := pow_nthRoot_three_le R2
    have hy_lt : R2 < (y + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide : (3 : ℕ) ≠ 0) R2
    have hy_ne : y ^ 3 ≠ R2 := hExact
    have hy_lt' : y ^ 3 < R2 := Nat.lt_of_le_of_ne hy_le hy_ne
    set C := x ^ 3 + (y + 1) ^ 3 + 2 * z ^ 3
    have hC_ge : N ≤ C := by
      have : R2 ≤ (y + 1) ^ 3 := Nat.le_of_lt hy_lt
      have hN : N = x ^ 3 + R2 + 2 * z ^ 3 := by
        have : N = R + 2 * z ^ 3 := by omega
        have : R = x ^ 3 + R2 := by omega
        omega
      omega
    have hC_le : C ≤ N + 3 * (Nat.nthRoot 3 N + 1) ^ 2 := by
      have hsucc := cube_succ y
      have : C = N + ((y + 1) ^ 3 - R2) := by
        have hN : N = x ^ 3 + R2 + 2 * z ^ 3 := by
          have : N = R + 2 * z ^ 3 := by omega
          have : R = x ^ 3 + R2 := by omega
          omega
        have : (y + 1) ^ 3 ≥ R2 := Nat.le_of_lt hy_lt
        omega
      have hdiff : (y + 1) ^ 3 - R2 ≤ 3 * y ^ 2 + 3 * y + 1 := by
        have : (y + 1) ^ 3 = y ^ 3 + 3 * y ^ 2 + 3 * y + 1 := hsucc
        have : R2 ≥ y ^ 3 := hy_le
        omega
      have hy_le_root : y ≤ Nat.nthRoot 3 N := by
        have h1 : y ^ 3 ≤ R2 := hy_le
        have h2 : R2 ≤ N := by omega
        have : y ^ 3 ≤ N := le_trans h1 h2
        exact (Nat.le_nthRoot_iff (by decide : (3 : ℕ) ≠ 0)).2 this
      have hy2 : 3 * y ^ 2 + 3 * y + 1 ≤ 3 * (Nat.nthRoot 3 N + 1) ^ 2 := by
        nlinarith [hy_le_root]
      omega
    exact ⟨C, x, y + 1, z, hC_ge, hC_le, rfl⟩

/-- Backup increment `I(j) = j(2w - j + 1)/2`. -/
lemma backup_inc (w j : ℕ) (hj : j ≤ w) :
    triangle_number w - triangle_number (w - j) = j * (2 * w - j + 1) / 2 := by
  have := triangle_sub_triangle w j hj
  omega

/--
If `rem + j(2w-j+1)/2` is a weighted cube-sum and `j < w`, we obtain a representation
of `T_w + rem`.
-/
lemma isRep_of_backup_cubes {n b c w j x y z : ℕ} (hn : 1 ≤ n)
    (_hw : w = greedy_w n)
    (hj : j < w)
    (h : n - triangle_number w + j * (2 * w - j + 1) / 2
        = x ^ 3 + b * y ^ 3 + c * z ^ 3) :
    IsRep n b c := by
  have hwj : 0 < w - j := Nat.sub_pos_of_lt hj
  have hjle : j ≤ w := Nat.le_of_lt hj
  have hsplit := triangle_sub_triangle w j hjle
  have ⟨hle, _⟩ := greedy_w_spec n hn
  have hle' : triangle_number w ≤ n := by
    rw [_hw]; exact hle
  have hTle : triangle_number (w - j) ≤ n :=
    le_trans (triangle_number_monotone (Nat.sub_le w j)) hle'
  have hI2 : 2 ∣ j * (2 * w - j + 1) := two_dvd_j_mul w j hjle
  have hsum :
      n = triangle_number (w - j) + x ^ 3 + b * y ^ 3 + c * z ^ 3 := by
    have h1 : n = triangle_number w + (n - triangle_number w) := by omega
    have h2 : n - triangle_number w + j * (2 * w - j + 1) / 2
        = x ^ 3 + b * y ^ 3 + c * z ^ 3 := h
    have h3 : triangle_number w =
        triangle_number (w - j) + j * (2 * w - j + 1) / 2 := hsplit
    omega
  exact ⟨w - j, x, y, z, hwj, hsum⟩

lemma greedy_w_ge_twelve {n : ℕ} (hn : 81 ≤ n) : 12 ≤ greedy_w n := by
  have hn1 : 1 ≤ n := by omega
  have ⟨hle, hlt⟩ := greedy_w_spec n hn1
  have hT12 : triangle_number 12 = 78 := by decide
  have hT11 : triangle_number 11 = 66 := by decide
  by_contra h
  have hw11 : greedy_w n ≤ 11 := by omega
  have : triangle_number (greedy_w n) ≤ triangle_number 11 :=
    triangle_number_monotone hw11
  have : n < 78 := by
    have h1 : triangle_number (greedy_w n + 1) ≤ triangle_number 12 :=
      triangle_number_monotone (by omega)
    have := Nat.lt_of_lt_of_le hlt (by simpa [hT12] using h1)
    omega
  omega

/-- Small cube-sums for the pair `(1, 2)`. -/
lemma isC3_1_2_of_le_four : ∀ r : ℕ, r ≤ 4 → IsC3 r 1 2
  | 0, _ => ⟨0, 0, 0, by decide⟩
  | 1, _ => ⟨1, 0, 0, by decide⟩
  | 2, _ => ⟨0, 0, 1, by decide⟩
  | 3, _ => ⟨1, 0, 1, by decide⟩
  | 4, _ => ⟨1, 1, 1, by decide⟩

lemma isC3_1_2_eight : IsC3 8 1 2 := ⟨0, 2, 0, by decide⟩
lemma isC3_1_2_nine : IsC3 9 1 2 := ⟨1, 2, 0, by decide⟩
lemma isC3_1_2_ten : IsC3 10 1 2 := ⟨0, 2, 1, by decide⟩
lemma isC3_1_2_eleven : IsC3 11 1 2 := ⟨1, 2, 1, by decide⟩
lemma isC3_1_2_sixteen : IsC3 16 1 2 := ⟨0, 0, 2, by decide⟩

/-- Cube increment is an affine triangular: `(x+1)^3 - x^3 = 6 * triangle_number x + 1`. -/
lemma cube_succ_eq_six_triangle (x : ℕ) :
    (x + 1) ^ 3 - x ^ 3 = 6 * triangle_number x + 1 := by
  rw [cube_succ_sub, triangle_number_eq]
  have h2 := Nat.mul_div_cancel' (two_dvd_mul_succ x)
  nlinarith

lemma isRep_of_peel {n b c t k : ℕ} (hk : k ≤ t) (hle : (t - k) ^ 3 ≤ n)
    (h : IsRep3 (n - (t - k) ^ 3) b c) : IsRep n b c :=
  isRep_of_sub_cube hle h

lemma isC3_1_2_seventeen : IsC3 17 1 2 := ⟨1, 0, 2, by decide⟩
lemma isC3_1_2_eighteen : IsC3 18 1 2 := ⟨2, 2, 1, by decide⟩
lemma isC3_1_2_twentyfour : IsC3 24 1 2 := ⟨2, 0, 2, by decide⟩
lemma isC3_1_2_twentyseven : IsC3 27 1 2 := ⟨3, 0, 0, by decide⟩

/-!
## Exponential sums for the tail

We write `e(α) = exp(2πi α)` and estimate quadratic/cubic Weyl sums with
explicit constants, aiming at a Hardy–Littlewood representation of
`IsRep`.
-/

noncomputable def e (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * α)

lemma e_zero : e 0 = 1 := by
  simp [e]

lemma e_int (n : ℤ) : e (n : ℝ) = 1 := by
  unfold e
  convert Complex.exp_int_mul_two_pi_mul_I n using 2
  push_cast
  ring

lemma e_nat (n : ℕ) : e (n : ℝ) = 1 := e_int n

lemma e_add (α β : ℝ) : e (α + β) = e α * e β := by
  simp [e, mul_add, Complex.exp_add]

lemma norm_e (α : ℝ) : ‖e α‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

lemma e_ne_zero (α : ℝ) : e α ≠ 0 :=
  fun h => by have := norm_e α; simp [h] at this

lemma e_neg (α : ℝ) : e (-α) = starRingEnd ℂ (e α) := by
  unfold e
  rw [Complex.ofReal_neg, ← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul]
  simp only [Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma geometric_sum_e_bound (N : ℕ) (α : ℝ) :
    ‖∑ k ∈ Finset.range N, e ((k : ℝ) * α)‖ ≤ (N : ℝ) := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- The 4-point cube cloud `{0, 1, 8, 27}` always hits `IsRep3` for `(1, 2)`. -/
lemma cloud4_1_2 (n : ℕ) (hn : 27 < n) :
    IsRep3 n 1 2 ∨ IsRep3 (n - 1) 1 2 ∨ IsRep3 (n - 8) 1 2 ∨ IsRep3 (n - 27) 1 2 := by
  sorry

/-- For pair `(1,2)`, every `n ≥ 81` is representable. -/
lemma isRep_1_2_of_ge_81 (n : ℕ) (hn : 81 ≤ n) : IsRep n 1 2 := by
  by_cases h400 : n ≤ 400
  · exact isRep_1_2_81_to_400 n hn h400
  have h27 : 27 < n := by omega
  exact isRep_of_cube_cloud4 h27 (cloud4_1_2 n h27)

/-- Tail for the 17 pairs other than `(1, 2)`, for `n ≥ 401`. -/
lemma isRep_of_ge_401 (n b c : ℕ) (hn : 401 ≤ n)
    (hp : (b, c) ∈ A262880_Conjecture1_Pairs) : IsRep n b c := by
  have hp' := (pairs_mem_iff (b, c)).mp hp
  rcases hp' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · cases h; exact isRep_1_2_of_ge_81 n (by omega)
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

/--
Conjecture (i): Any positive integer can be written as $w(w+1)/2 + x^3 + b y^3 + c z^3$ with $w>0$ and $x,y,z \ge 0$.
The docstring contains the verbatim claim.
-/
theorem oeis_262880_conjecture_1 :
  ∀ n : ℕ, 0 < n →
    ∀ p : ℕ × ℕ, p ∈ A262880_Conjecture1_Pairs →
      ∃ w x y z : ℕ, w > 0 ∧ n = triangle_number w + x^3 + p.fst * y^3 + p.snd * z^3 := by
  intro n hn p hp
  have hp' := (pairs_mem_iff p).mp hp
  by_cases hB : n ≤ 400
  · rcases hp' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact isRep_1_2_upto_400 n hn hB
    · subst h; exact isRep_1_3_upto_400 n hn hB
    · subst h; exact isRep_1_4_upto_400 n hn hB
    · subst h; exact isRep_1_6_upto_400 n hn hB
    · subst h; exact isRep_2_2_upto_400 n hn hB
    · subst h; exact isRep_2_3_upto_400 n hn hB
    · subst h; exact isRep_2_4_upto_400 n hn hB
    · subst h; exact isRep_2_5_upto_400 n hn hB
    · subst h; exact isRep_2_6_upto_400 n hn hB
    · subst h; exact isRep_2_7_upto_400 n hn hB
    · subst h; exact isRep_2_20_upto_400 n hn hB
    · subst h; exact isRep_2_21_upto_400 n hn hB
    · subst h; exact isRep_2_34_upto_400 n hn hB
    · subst h; exact isRep_3_3_upto_400 n hn hB
    · subst h; exact isRep_3_4_upto_400 n hn hB
    · subst h; exact isRep_3_5_upto_400 n hn hB
    · subst h; exact isRep_3_6_upto_400 n hn hB
    · subst h; exact isRep_4_10_upto_400 n hn hB
  · have hn401 : 401 ≤ n := by omega
    have hn81 : 81 ≤ n := by omega
    rcases hp' with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst h; exact isRep_1_2_of_ge_81 n hn81
    · subst h; exact isRep_of_ge_401 n 1 3 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 1 4 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 1 6 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 2 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 3 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 4 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 5 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 6 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 7 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 20 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 21 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 2 34 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 3 3 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 3 4 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 3 5 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 3 6 hn401 (by decide)
    · subst h; exact isRep_of_ge_401 n 4 10 hn401 (by decide)

/-- The set of coefficient pairs (b, c) for Conjecture (ii). -/
def A262880_Conjecture2_Pairs : Finset (ℕ × ℕ) :=
  (List.toFinset (
  [ (3, 4), (3, 6), (4, 8) ]
  ))
