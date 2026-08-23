import FormalConjectures.Util.ProblemImports

open Nat

/-! Development file for A273110. -/

/-- Local copy of the OEIS function (same as in Spec.lean). -/
def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n
  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2
    if x^2 + y^2 + z^2 + w^2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧ IsSquare E
    then 1 else 0

def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

/-- A valid representation counted by `A273110`. -/
def Valid (n x y z w : ℕ) : Prop :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
  y > 0 ∧ y ≥ z ∧ z ≤ w ∧
  IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)

instance {n x y z w : ℕ} : Decidable (Valid n x y z w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

lemma valid_x_zero {n y z w : ℕ} (hsum : y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hy : y > 0) (hyz : y ≥ z) (hzw : z ≤ w) : Valid n 0 y z w := by
  refine ⟨by simpa using hsum, hy, hyz, hzw, ?_⟩
  refine ⟨5 * (y + z), ?_⟩
  ring

lemma valid_x_eq_sum {n y z w : ℕ} (hsum : (y + z) ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hy : y > 0) (hyz : y ≥ z) (hzw : z ≤ w) : Valid n (y + z) y z w := by
  refine ⟨hsum, hy, hyz, hzw, ?_⟩
  refine ⟨13 * (y + z), ?_⟩
  ring

lemma valid_double {n x y z w : ℕ} (h : Valid n x y z w) :
    Valid (4 * n) (2 * x) (2 * y) (2 * z) (2 * w) := by
  obtain ⟨hsum, hy, hyz, hzw, ⟨t, ht⟩⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ⟨2 * t, ?_⟩⟩
  · linear_combination 4 * hsum
  · omega
  · omega
  · omega
  · linear_combination 4 * ht

/-- Squares modulo 8 are 0, 1 or 4. -/
lemma sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  have : a % 8 < 8 := Nat.mod_lt a (by norm_num)
  interval_cases h : a % 8 <;> simp [Nat.pow_mod, h]

lemma odd_sq_mod_eight {a : ℕ} (h : Odd a) : a ^ 2 % 8 = 1 := by
  rw [Nat.odd_iff] at h
  have hlt : a % 8 < 8 := Nat.mod_lt a (by decide)
  have hmod : a % 2 = (a % 8) % 2 := (Nat.mod_mod_of_dvd a (by decide : 2 ∣ 8)).symm
  interval_cases h8 : a % 8
  · omega
  · simp [Nat.pow_mod, h8]
  · omega
  · simp [Nat.pow_mod, h8]
  · omega
  · simp [Nat.pow_mod, h8]
  · omega
  · simp [Nat.pow_mod, h8]

/-- A number congruent to 7 mod 8 is not a sum of three squares. -/
lemma not_three_sq_of_mod_eight_eq_seven {n a b c : ℕ} (h : n % 8 = 7)
    (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) : False := by
  have ha := sq_mod_eight a
  have hb := sq_mod_eight b
  have hc := sq_mod_eight c
  have hmod : (a ^ 2 + b ^ 2 + c ^ 2) % 8 = 7 := by rw [hs, h]
  rw [Nat.add_mod, Nat.add_mod (a ^ 2)] at hmod
  rcases ha with (ha | ha | ha) <;> rcases hb with (hb | hb | hb) <;> rcases hc with (hc | hc | hc) <;>
    simp [ha, hb, hc] at hmod

lemma le_of_sq_le_self (a n : ℕ) (h : a ^ 2 ≤ n) : a ≤ n := by
  cases a with
  | zero => exact Nat.zero_le _
  | succ a =>
    have : a + 1 ≤ (a + 1) ^ 2 := by nlinarith
    exact this.trans h

lemma valid_coords_le {n x y z w : ℕ} (h : Valid n x y z w) :
    x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ w ≤ n := by
  have hsum := h.1
  have hx : x ^ 2 ≤ n := by omega
  have hy : y ^ 2 ≤ n := by omega
  have hz : z ^ 2 ≤ n := by omega
  have hw : w ^ 2 ≤ n := by omega
  exact ⟨le_of_sq_le_self _ _ hx, le_of_sq_le_self _ _ hy,
    le_of_sq_le_self _ _ hz, le_of_sq_le_self _ _ hw⟩

/-- The set of valid 4-tuples with coordinates in `range (n + 1)`. -/
def validFinset (n : ℕ) : Finset ((ℕ × ℕ) × ℕ × ℕ) :=
  (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)) ×ˢ
    (Finset.range (n + 1) ×ˢ Finset.range (n + 1)))).filter
    (fun p => Valid n p.1.1 p.1.2 p.2.1 p.2.2)

lemma term_eq_one {n x y z w : ℕ} (h : Valid n x y z w) :
    (if x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w ∧
        IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)
      then 1 else 0) = 1 := by
  simp [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

lemma A273110_pos_of_valid {n x y z w : ℕ} (h : Valid n x y z w) : 0 < A273110 n := by
  obtain ⟨hx, hy, hz, hw⟩ := valid_coords_le h
  have hx' : x ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hx)
  have hy' : y ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hy)
  have hz' : z ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hz)
  have hw' : w ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hw)
  have hterm := term_eq_one h
  unfold A273110
  -- the sum is at least the single term at (x,y,z,w)
  have hnn : ∀ a b c d : ℕ, 0 ≤
      (if a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n ∧ b > 0 ∧ b ≥ c ∧ c ≤ d ∧
          IsSquare ((a + 4 * b + 4 * c) ^ 2 + (9 * a + 3 * b + 3 * c) ^ 2)
        then 1 else 0) := fun _ _ _ _ => Nat.zero_le _
  refine lt_of_lt_of_le (by exact Nat.zero_lt_one) ?_
  have := Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun x' => Finset.sum (Finset.range (n + 1)) fun y' =>
      Finset.sum (Finset.range (n + 1)) fun z' =>
        Finset.sum (Finset.range (n + 1)) fun w' =>
          if x' ^ 2 + y' ^ 2 + z' ^ 2 + w' ^ 2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧
              IsSquare ((x' + 4 * y' + 4 * z') ^ 2 + (9 * x' + 3 * y' + 3 * z') ^ 2)
            then 1 else 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg
      fun _ _ => Nat.zero_le _) hx'
  refine le_trans ?_ this
  have := Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun y' =>
      Finset.sum (Finset.range (n + 1)) fun z' =>
        Finset.sum (Finset.range (n + 1)) fun w' =>
          if x ^ 2 + y' ^ 2 + z' ^ 2 + w' ^ 2 = n ∧ y' > 0 ∧ y' ≥ z' ∧ z' ≤ w' ∧
              IsSquare ((x + 4 * y' + 4 * z') ^ 2 + (9 * x + 3 * y' + 3 * z') ^ 2)
            then 1 else 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _) hy'
  refine le_trans ?_ this
  have := Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun z' =>
      Finset.sum (Finset.range (n + 1)) fun w' =>
        if x ^ 2 + y ^ 2 + z' ^ 2 + w' ^ 2 = n ∧ y > 0 ∧ y ≥ z' ∧ z' ≤ w' ∧
            IsSquare ((x + 4 * y + 4 * z') ^ 2 + (9 * x + 3 * y + 3 * z') ^ 2)
          then 1 else 0)
    (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _) hz'
  refine le_trans ?_ this
  have := Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun w' =>
      if x ^ 2 + y ^ 2 + z ^ 2 + w' ^ 2 = n ∧ y > 0 ∧ y ≥ z ∧ z ≤ w' ∧
          IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)
        then 1 else 0)
    (fun _ _ => Nat.zero_le _) hw'
  simpa [hterm] using this

/-- If `8 ∣ n` then all four squares summing to `n` are even. -/
lemma four_sq_even_of_eight_dvd {x y z w n : ℕ}
    (h8 : 8 ∣ n) (hs : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) :
    Even x ∧ Even y ∧ Even z ∧ Even w := by
  have hmod : (x ^ 2 % 8 + y ^ 2 % 8 + z ^ 2 % 8 + w ^ 2 % 8) % 8 = 0 := by
    have := congrArg (· % 8) hs
    simpa [Nat.add_mod] using this.trans (Nat.mod_eq_zero_of_dvd h8)
  have hx := sq_mod_eight x
  have hy := sq_mod_eight y
  have hz := sq_mod_eight z
  have hw := sq_mod_eight w
  have not1x : x ^ 2 % 8 ≠ 1 := by
    intro hx1; rcases hy with (hy | hy | hy) <;> rcases hz with (hz | hz | hz) <;>
      rcases hw with (hw | hw | hw) <;> simp [hx1, hy, hz, hw] at hmod
  have not1y : y ^ 2 % 8 ≠ 1 := by
    intro hy1; rcases hx with (hx | hx | hx) <;> rcases hz with (hz | hz | hz) <;>
      rcases hw with (hw | hw | hw) <;> simp [hy1, hx, hz, hw] at hmod
  have not1z : z ^ 2 % 8 ≠ 1 := by
    intro hz1; rcases hx with (hx | hx | hx) <;> rcases hy with (hy | hy | hy) <;>
      rcases hw with (hw | hw | hw) <;> simp [hz1, hx, hy, hw] at hmod
  have not1w : w ^ 2 % 8 ≠ 1 := by
    intro hw1; rcases hx with (hx | hx | hx) <;> rcases hy with (hy | hy | hy) <;>
      rcases hz with (hz | hz | hz) <;> simp [hw1, hx, hy, hz] at hmod
  have even_of : ∀ a : ℕ, a ^ 2 % 8 ≠ 1 → Even a := fun a ha => by
    rw [Nat.even_iff]
    by_contra ho
    have : a % 2 = 1 := by omega
    have : Odd a := Nat.odd_iff.mpr this
    exact ha (odd_sq_mod_eight this)
  exact ⟨even_of x not1x, even_of y not1y, even_of z not1z, even_of w not1w⟩

lemma mul_right_cancel_four {p q : ℕ} (h : 4 * p = 4 * q) : p = q :=
  Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) h

lemma valid_halve {n x y z w : ℕ}
    (h : Valid (4 * n) (2 * x) (2 * y) (2 * z) (2 * w)) : Valid n x y z w := by
  obtain ⟨hsum, hy, hyz, hzw, ⟨t, ht⟩⟩ := h
  have hy0 : 0 < y := Nat.pos_of_ne_zero fun hy0 => by simp [hy0] at hy
  have hsum' : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
    apply mul_right_cancel_four
    convert hsum using 1 <;> ring
  refine ⟨hsum', hy0, by omega, by omega, ?_⟩
  set E := (x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2
  have ht' : t * t = 4 * E := by
    convert ht.symm using 1
    ring
  have even_t : Even t := by
    rw [Nat.even_iff]
    by_contra ho
    have hodd : t % 2 = 1 := by omega
    have : (t * t) % 2 = 1 := by simp [Nat.mul_mod, hodd]
    have : (t * t) % 2 = 0 := by rw [ht']; simp [Nat.mul_mod]
    omega
  obtain ⟨u, hu⟩ := even_t
  have hu' : t = 2 * u := by omega
  refine ⟨u, mul_right_cancel_four ?_⟩
  calc 4 * E = t * t := ht'.symm
    _ = (2 * u) * (2 * u) := by rw [hu']
    _ = 4 * (u * u) := by ring

/-- From a three-square representation, produce a valid A273110 tuple. -/
lemma valid_of_three_sq {n a b c : ℕ} (hn : 0 < n)
    (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) : ∃ y z w, Valid n 0 y z w := by
  have ha0 : 0 < a ∨ 0 < b ∨ 0 < c := by
    by_contra H
    push_neg at H
    have : a = 0 ∧ b = 0 ∧ c = 0 := by omega
    simp [this] at hs
    omega
  -- Case on the relative order of a, b, c by comparing pairs.
  cases le_total b a with
  | inl hba =>
    cases le_total c a with
    | inl hca =>
      -- b ≤ a, c ≤ a: put y = a
      cases le_total c b with
      | inl hcb =>
          exact ⟨a, c, b, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) hca hcb⟩
      | inr hbc =>
          exact ⟨a, b, c, valid_x_zero hs (by omega) hba hbc⟩
    | inr hac =>
      exact ⟨c, b, a, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) (hba.trans hac) hba⟩
  | inr hab =>
    cases le_total c b with
    | inl hcb =>
      cases le_total c a with
      | inl hca =>
          exact ⟨b, c, a, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) (hca.trans hab) hca⟩
      | inr hac =>
          exact ⟨b, a, c, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) hab hac⟩
    | inr hbc =>
      exact ⟨c, a, b, valid_x_zero (by rw [← hs]; ac_rfl) (by omega) (hab.trans hbc) hab⟩

lemma A273110_pos_of_three_sq {n a b c : ℕ} (hn : 0 < n)
    (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) : 0 < A273110 n := by
  obtain ⟨y, z, w, h⟩ := valid_of_three_sq hn hs
  exact A273110_pos_of_valid h

/-- `2k²` always has two distinct valid representations (for `k > 0`). -/
lemma two_reps_of_two_mul_sq {k : ℕ} (hk : 0 < k) :
    Valid (2 * k ^ 2) 0 k 0 k ∧ Valid (2 * k ^ 2) k k 0 0 := by
  constructor
  · exact valid_x_zero (by ring) hk (Nat.zero_le _) (Nat.zero_le _)
  · exact valid_x_eq_sum (by ring) hk (Nat.zero_le _) (Nat.zero_le _)

/-- `3k²` always has two distinct valid representations (for `k > 0`). -/
lemma two_reps_of_three_mul_sq {k : ℕ} (hk : 0 < k) :
    Valid (3 * k ^ 2) 0 k k k ∧ Valid (3 * k ^ 2) k k 0 k := by
  constructor
  · exact valid_x_zero (by ring) hk le_rfl le_rfl
  · exact valid_x_eq_sum (by ring) hk (Nat.zero_le _) (Nat.zero_le _)

lemma valid_x_zero_ne_x_eq_sum {n y z w y' z' w' : ℕ}
    (h0 : Valid n 0 y z w) (hs : Valid n (y' + z') y' z' w') :
    ¬ (0 = y' + z' ∧ y = y' ∧ z = z' ∧ w = w') := by
  intro h
  have : y' + z' = 0 := h.1.symm
  have : y' = 0 := by omega
  exact absurd h0.2.1 (by omega)

/-- Squares modulo 4 are 0 or 1. -/
lemma sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  have : a % 4 < 4 := Nat.mod_lt a (by decide)
  interval_cases h : a % 4 <;> simp [Nat.pow_mod, h]

lemma odd_sq_mod_four {a : ℕ} (h : Odd a) : a ^ 2 % 4 = 1 := by
  rw [Nat.odd_iff] at h
  have hlt : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hmod : a % 2 = (a % 4) % 2 := (Nat.mod_mod_of_dvd a (by decide : 2 ∣ 4)).symm
  interval_cases h4 : a % 4
  · omega
  · simp [Nat.pow_mod, h4]
  · omega
  · simp [Nat.pow_mod, h4]

lemma four_dvd_sq_of_even {a : ℕ} (h : Even a) : 4 ∣ a ^ 2 := by
  obtain ⟨k, hk⟩ := h
  have : a = 2 * k := by omega
  rw [this]; use k ^ 2; ring

/-- If `4 ∣ n` and `n` is a sum of three squares, all three are even. -/
lemma three_sq_even_of_four_dvd {a b c n : ℕ}
    (h4 : 4 ∣ n) (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    Even a ∧ Even b ∧ Even c := by
  have hmod : (a ^ 2 + b ^ 2 + c ^ 2) % 4 = 0 := by
    rw [hs]; exact Nat.mod_eq_zero_of_dvd h4
  rw [Nat.add_mod, Nat.add_mod (a ^ 2)] at hmod
  have ha := sq_mod_four a
  have hb := sq_mod_four b
  have hc := sq_mod_four c
  have even_of : ∀ x : ℕ, x ^ 2 % 4 ≠ 1 → Even x := fun x hx => by
    rw [Nat.even_iff]
    by_contra ho
    have hodd : Odd x := Nat.odd_iff.mpr (by omega)
    exact hx (odd_sq_mod_four hodd)
  have not1 : a ^ 2 % 4 ≠ 1 ∧ b ^ 2 % 4 ≠ 1 ∧ c ^ 2 % 4 ≠ 1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; rcases hb with (hb | hb) <;> rcases hc with (hc | hc) <;> simp [h, hb, hc] at hmod
    · intro h; rcases ha with (ha | ha) <;> rcases hc with (hc | hc) <;> simp [h, ha, hc] at hmod
    · intro h; rcases ha with (ha | ha) <;> rcases hb with (hb | hb) <;> simp [h, ha, hb] at hmod
  exact ⟨even_of a not1.1, even_of b not1.2.1, even_of c not1.2.2⟩

/-- Necessity of the three-square theorem. -/
lemma three_sq_necessity {n a b c : ℕ} (hs : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    ¬ ∃ k m, n = 4 ^ k * (8 * m + 7) := by
  intro ⟨k, m, hn⟩
  induction k generalizing a b c n with
  | zero =>
    simp at hn
    have : n % 8 = 7 := by rw [hn]; simp [Nat.add_mod]
    exact not_three_sq_of_mod_eight_eq_seven this hs
  | succ k ih =>
    have h4 : 4 ∣ n := by
      rw [hn, pow_succ]
      exact ⟨4 ^ k * (8 * m + 7), by ring⟩
    obtain ⟨ea, eb, ec⟩ := three_sq_even_of_four_dvd h4 hs
    obtain ⟨a', ha'⟩ := ea
    obtain ⟨b', hb'⟩ := eb
    obtain ⟨c', hc'⟩ := ec
    have ha2 : a = 2 * a' := by omega
    have hb2 : b = 2 * b' := by omega
    have hc2 : c = 2 * c' := by omega
    have hs' : a' ^ 2 + b' ^ 2 + c' ^ 2 = 4 ^ k * (8 * m + 7) := by
      apply mul_right_cancel_four
      have : 4 * (a' ^ 2 + b' ^ 2 + c' ^ 2) = n := by
        rw [← hs, ha2, hb2, hc2]; ring
      rw [this, hn, pow_succ]
      ring
    exact ih hs' rfl

/-- Small explicit witnesses. -/
lemma valid_one : Valid 1 0 1 0 0 :=
  valid_x_zero (by decide) (by decide) (by decide) (by decide)

lemma valid_seven : Valid 7 2 1 1 1 := by
  have hsum : (1 + 1) ^ 2 + 1 ^ 2 + 1 ^ 2 + 1 ^ 2 = 7 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma A273110_one_pos : 0 < A273110 1 := A273110_pos_of_valid valid_one
lemma A273110_seven_pos : 0 < A273110 7 := A273110_pos_of_valid valid_seven


/-! ## Doubling bijection -/

lemma even_iff_two_mul {a : ℕ} : Even a ↔ ∃ k, a = 2 * k := by
  constructor
  · intro h; obtain ⟨k, hk⟩ := h; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩

/-- If `n` is even then `8 ∣ 4 * n`. -/
lemma eight_dvd_four_mul_of_even {n : ℕ} (h : Even n) : 8 ∣ 4 * n := by
  obtain ⟨k, hk⟩ := even_iff_two_mul.mp h
  rw [hk]; exact ⟨k, by ring⟩

lemma valid_coords_even_of_eight_dvd {n x y z w : ℕ}
    (h8 : 8 ∣ n) (h : Valid n x y z w) :
    Even x ∧ Even y ∧ Even z ∧ Even w :=
  four_sq_even_of_eight_dvd h8 h.1

/-- Scaling by 2 is a bijection `Valid n ≃ Valid (4n)` when `n` is even. -/
lemma valid_four_mul_iff_of_even {n x y z w : ℕ} (hn : Even n) :
    Valid (4 * n) (2 * x) (2 * y) (2 * z) (2 * w) ↔ Valid n x y z w :=
  ⟨valid_halve, valid_double⟩

lemma exists_halve_of_valid_four_mul {n x y z w : ℕ}
    (hn : Even n) (h : Valid (4 * n) x y z w) :
    ∃ x' y' z' w', x = 2 * x' ∧ y = 2 * y' ∧ z = 2 * z' ∧ w = 2 * w' ∧
      Valid n x' y' z' w' := by
  have h8 : 8 ∣ 4 * n := eight_dvd_four_mul_of_even hn
  obtain ⟨hx, hy, hz, hw⟩ := valid_coords_even_of_eight_dvd h8 h
  obtain ⟨x', hx'⟩ := even_iff_two_mul.mp hx
  obtain ⟨y', hy'⟩ := even_iff_two_mul.mp hy
  obtain ⟨z', hz'⟩ := even_iff_two_mul.mp hz
  obtain ⟨w', hw'⟩ := even_iff_two_mul.mp hw
  refine ⟨x', y', z', w', hx', hy', hz', hw', ?_⟩
  exact valid_halve (by simpa [hx', hy', hz', hw'] using h)

/-! ## Efficient enumeration of valid tuples -/

/-- `n` is a square iff `n.sqrt ^ 2 = n`. -/
lemma isSquare_iff_sqrt_sq (n : ℕ) : IsSquare n ↔ n.sqrt ^ 2 = n := by
  constructor
  · rintro ⟨k, hk⟩
    have hs : n.sqrt = k := by
      rw [hk]; exact Nat.sqrt_eq k
    rw [hs, hk, pow_two]
  · intro h
    refine ⟨n.sqrt, ?_⟩
    rw [pow_two] at h
    exact h.symm

lemma isSquare_iff_sqrt_mul (n : ℕ) : IsSquare n ↔ n.sqrt * n.sqrt = n := by
  rw [isSquare_iff_sqrt_sq, pow_two]

/-- A fast equivalent of `Valid` using `Nat.sqrt`. -/
def validB (n x y z w : ℕ) : Bool :=
  x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 == n && decide (y > 0) && decide (y ≥ z) &&
    decide (z ≤ w) &&
    let E := (x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2
    E.sqrt * E.sqrt == E

lemma validB_iff (n x y z w : ℕ) : validB n x y z w = true ↔ Valid n x y z w := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨hsum, hy⟩, hyz⟩, hzw⟩, hE⟩
    exact ⟨hsum, hy, hyz, hzw, (isSquare_iff_sqrt_mul _).mpr hE⟩
  · rintro ⟨hsum, hy, hyz, hzw, hE⟩
    exact ⟨⟨⟨⟨hsum, hy⟩, hyz⟩, hzw⟩, (isSquare_iff_sqrt_mul _).mp hE⟩

/-- Count valid tuples by ranging over `x,y,z ≤ √n` and testing that the remainder is a square. -/
def countValid (n : ℕ) : ℕ :=
  (Finset.range (n.sqrt + 1)).sum fun x =>
    (Finset.range (n.sqrt + 1)).sum fun y =>
      (Finset.range (y + 1)).sum fun z =>
        let r := n - x ^ 2 - y ^ 2 - z ^ 2
        if x ^ 2 + y ^ 2 + z ^ 2 ≤ n ∧ r.sqrt * r.sqrt = r ∧ z ≤ r.sqrt ∧ 0 < y ∧
            IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)
        then 1 else 0

lemma sqrt_sq_le (n : ℕ) : n.sqrt ^ 2 ≤ n := Nat.sqrt_le' n

lemma lt_succ_sqrt_of_sq_le {a n : ℕ} (h : a ^ 2 ≤ n) : a < n.sqrt + 1 := by
  have : a ≤ n.sqrt := Nat.le_sqrt.mpr (by rwa [pow_two] at h)
  omega

lemma valid_implies_sq_le {n x y z w : ℕ} (h : Valid n x y z w) :
    x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n ∧ w ^ 2 ≤ n := by
  have := h.1
  omega

lemma valid_mem_sqrt_range {n x y z w : ℕ} (h : Valid n x y z w) :
    x ≤ n.sqrt ∧ y ≤ n.sqrt ∧ z ≤ n.sqrt ∧ w ≤ n.sqrt := by
  obtain ⟨hx, hy, hz, hw⟩ := valid_implies_sq_le h
  exact ⟨Nat.le_sqrt.mpr (by rwa [pow_two] at hx),
    Nat.le_sqrt.mpr (by rwa [pow_two] at hy),
    Nat.le_sqrt.mpr (by rwa [pow_two] at hz),
    Nat.le_sqrt.mpr (by rwa [pow_two] at hw)⟩

lemma A273110_eq_card_validFinset (n : ℕ) : A273110 n = (validFinset n).card := by
  classical
  unfold A273110 validFinset
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
  simp [Valid]

lemma validFinset_eq_sqrt (n : ℕ) :
    validFinset n =
      ((Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1)) ×ˢ
        (Finset.range (n.sqrt + 1) ×ˢ Finset.range (n.sqrt + 1))).filter
        (fun p => Valid n p.1.1 p.1.2 p.2.1 p.2.2) := by
  ext p
  simp only [validFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · intro ⟨⟨⟨hx, hy⟩, hz, hw⟩, hv⟩
    obtain ⟨hx', hy', hz', hw'⟩ := valid_mem_sqrt_range hv
    exact ⟨⟨⟨Nat.lt_succ_of_le hx', Nat.lt_succ_of_le hy'⟩,
      Nat.lt_succ_of_le hz', Nat.lt_succ_of_le hw'⟩, hv⟩
  · intro ⟨⟨⟨hx, hy⟩, hz, hw⟩, hv⟩
    have hs : n.sqrt ≤ n := Nat.sqrt_le_self n
    exact ⟨⟨⟨lt_of_lt_of_le hx (Nat.succ_le_succ hs),
      lt_of_lt_of_le hy (Nat.succ_le_succ hs)⟩,
      lt_of_lt_of_le hz (Nat.succ_le_succ hs),
      lt_of_lt_of_le hw (Nat.succ_le_succ hs)⟩, hv⟩

lemma sub_three_sq {n x y z w : ℕ} (h : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) :
    n - x ^ 2 - y ^ 2 - z ^ 2 = w * w := by
  have hx : x ^ 2 ≤ n := by omega
  have hy : y ^ 2 ≤ n - x ^ 2 := by
    apply Nat.le_sub_of_add_le
    omega
  have hz : z ^ 2 ≤ n - x ^ 2 - y ^ 2 := by
    apply Nat.le_sub_of_add_le
    apply Nat.le_sub_of_add_le
    omega
  zify [hx, hy, hz]
  have : (x ^ 2 + y ^ 2 + z ^ 2 + w * w : ℤ) = n := by
    exact_mod_cast (by simpa [pow_two] using h)
  linarith

lemma add_three_sq_of_sub {n x y z w : ℕ}
    (hle : x ^ 2 + y ^ 2 + z ^ 2 ≤ n)
    (h : n - x ^ 2 - y ^ 2 - z ^ 2 = w * w) :
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
  have hx : x ^ 2 ≤ n := by omega
  have hy : y ^ 2 ≤ n - x ^ 2 := by
    apply Nat.le_sub_of_add_le
    omega
  have hz : z ^ 2 ≤ n - x ^ 2 - y ^ 2 := by
    apply Nat.le_sub_of_add_le
    apply Nat.le_sub_of_add_le
    omega
  zify [hx, hy, hz] at h ⊢
  linarith

lemma countValid_term_eq {n x y z : ℕ} (hyz : z ≤ y) :
    (let r := n - x ^ 2 - y ^ 2 - z ^ 2
      if x ^ 2 + y ^ 2 + z ^ 2 ≤ n ∧ r.sqrt * r.sqrt = r ∧ z ≤ r.sqrt ∧ 0 < y ∧
          IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)
      then 1 else 0) =
      if ∃ w, Valid n x y z w then 1 else 0 := by
  classical
  dsimp
  set r := n - x ^ 2 - y ^ 2 - z ^ 2
  by_cases hex : ∃ w, Valid n x y z w
  · obtain ⟨w, hsum, hy, -, hzw, hE⟩ := hex
    have hle : x ^ 2 + y ^ 2 + z ^ 2 ≤ n := by have := hsum; omega
    have hr : r = w * w := by
      simpa [r, pow_two] using sub_three_sq hsum
    have hsqrt : r.sqrt = w := by rw [hr]; exact Nat.sqrt_eq w
    have hcond : x ^ 2 + y ^ 2 + z ^ 2 ≤ n ∧ r.sqrt * r.sqrt = r ∧ z ≤ r.sqrt ∧ 0 < y ∧
        IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2) := by
      refine ⟨hle, ?_, ?_, hy, hE⟩
      · simp [hsqrt, hr]
      · rwa [hsqrt]
    have hex' : ∃ w, Valid n x y z w := ⟨w, hsum, hy, hyz, hzw, hE⟩
    rw [if_pos hcond, if_pos hex']
  · have hcond : ¬ (x ^ 2 + y ^ 2 + z ^ 2 ≤ n ∧ r.sqrt * r.sqrt = r ∧ z ≤ r.sqrt ∧ 0 < y ∧
        IsSquare ((x + 4 * y + 4 * z) ^ 2 + (9 * x + 3 * y + 3 * z) ^ 2)) := by
      rintro ⟨hle, hwsq, hzw, hy, hE⟩
      refine hex ⟨r.sqrt, ?_, hy, hyz, hzw, hE⟩
      refine add_three_sq_of_sub hle ?_
      simpa [r] using hwsq.symm
    rw [if_neg hcond, if_neg hex]

lemma A273110_eq_countValid (n : ℕ) : A273110 n = countValid n := by
  classical
  rw [A273110_eq_card_validFinset, validFinset_eq_sqrt]
  unfold countValid
  set s := n.sqrt
  set F : (ℕ × ℕ) × ℕ × ℕ → ℕ :=
    fun p => if Valid n p.1.1 p.1.2 p.2.1 p.2.2 then 1 else 0
  rw [Finset.card_filter]
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  have hys : y < s + 1 := Finset.mem_range.mp hy
  have hsub : Finset.range (y + 1) ⊆ Finset.range (s + 1) := by
    intro z hz
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hz; omega)
  have h0 : ∀ z ∈ Finset.range (s + 1), z ∉ Finset.range (y + 1) →
      (Finset.range (s + 1)).sum (fun w => F ((x, y), z, w)) = 0 := by
    intro z _hz hzA
    apply Finset.sum_eq_zero
    intro w _hw
    have hyz : y < z := by
      have : ¬ z < y + 1 := mt Finset.mem_range.mpr hzA
      omega
    change (if Valid n x y z w then 1 else 0) = 0
    split_ifs with hv
    · exact absurd hv.2.2.1 (Nat.not_le_of_gt hyz)
    · rfl
  have hsumz :
      (Finset.range (s + 1)).sum (fun z =>
        (Finset.range (s + 1)).sum (fun w => F ((x, y), z, w))) =
      (Finset.range (y + 1)).sum (fun z =>
        (Finset.range (s + 1)).sum (fun w => F ((x, y), z, w))) :=
    (Finset.sum_subset hsub h0).symm
  rw [hsumz]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hyz : z ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hz)
  rw [countValid_term_eq hyz]
  have : (Finset.range (s + 1)).sum (fun w => F ((x, y), z, w)) =
      if ∃ w, Valid n x y z w then 1 else 0 := by
    by_cases hex : ∃ w, Valid n x y z w
    · obtain ⟨w, hw⟩ := hex
      have hwle : w ≤ s := (valid_mem_sqrt_range hw).2.2.2
      have hwmem : w ∈ Finset.range (s + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hwle)
      have huniq : ∀ w' ∈ Finset.range (s + 1), F ((x, y), z, w') = if w' = w then 1 else 0 := by
        intro w' _
        change (if Valid n x y z w' then 1 else 0) = _
        by_cases hweq : w' = w
        · subst hweq; simp [hw]
        · split_ifs with hv
          · have hsq : w' ^ 2 = w ^ 2 := by
              have h1 := hv.1; have h2 := hw.1; omega
            have : w' * w' = w * w := by simpa [pow_two] using hsq
            exact (hweq (Nat.mul_self_inj.mp this)).elim
          · rfl
      rw [Finset.sum_congr rfl huniq, Finset.sum_ite_eq', if_pos hwmem, if_pos ⟨w, hw⟩]
    · have hz0 : ∀ w ∈ Finset.range (s + 1), F ((x, y), z, w) = 0 := by
        intro w _
        change (if Valid n x y z w then 1 else 0) = 0
        split_ifs with hv
        · exact absurd ⟨w, hv⟩ hex
        · rfl
      simp [Finset.sum_eq_zero hz0, hex]
  exact this.symm

/-! ## Explicit witnesses for every element of `M` -/

lemma valid_23 : Valid 23 3 2 1 3 := by
  have hsum : (2 + 1) ^ 2 + 2 ^ 2 + 1 ^ 2 + 3 ^ 2 = 23 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_31 : Valid 31 2 1 1 5 := by
  have hsum : (1 + 1) ^ 2 + 1 ^ 2 + 1 ^ 2 + 5 ^ 2 = 31 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_39 : Valid 39 3 2 1 5 := by
  have hsum : (2 + 1) ^ 2 + 2 ^ 2 + 1 ^ 2 + 5 ^ 2 = 39 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_47 : Valid 47 5 3 2 3 := by
  have hsum : (3 + 2) ^ 2 + 3 ^ 2 + 2 ^ 2 + 3 ^ 2 = 47 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_55 : Valid 55 2 1 1 7 := by
  have hsum : (1 + 1) ^ 2 + 1 ^ 2 + 1 ^ 2 + 7 ^ 2 = 55 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_71 : Valid 71 6 5 1 3 := by
  have hsum : (5 + 1) ^ 2 + 5 ^ 2 + 1 ^ 2 + 3 ^ 2 = 71 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_79 : Valid 79 6 3 3 5 := by
  have hsum : (3 + 3) ^ 2 + 3 ^ 2 + 3 ^ 2 + 5 ^ 2 = 79 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_119 : Valid 119 5 3 2 9 := by
  have hsum : (3 + 2) ^ 2 + 3 ^ 2 + 2 ^ 2 + 9 ^ 2 = 119 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_151 : Valid 151 9 6 3 5 := by
  have hsum : (6 + 3) ^ 2 + 6 ^ 2 + 3 ^ 2 + 5 ^ 2 = 151 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_191 : Valid 191 10 9 1 3 := by
  have hsum : (9 + 1) ^ 2 + 9 ^ 2 + 1 ^ 2 + 3 ^ 2 = 191 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_311 : Valid 311 7 6 1 15 := by
  have hsum : (6 + 1) ^ 2 + 6 ^ 2 + 1 ^ 2 + 15 ^ 2 = 311 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma valid_671 : Valid 671 17 11 6 15 := by
  have hsum : (11 + 6) ^ 2 + 11 ^ 2 + 6 ^ 2 + 15 ^ 2 = 671 := by decide
  exact valid_x_eq_sum hsum (by decide) (by decide) (by decide)

lemma mem_M_pos {m : ℕ} (hm : m ∈ A273110_set_M) : 0 < A273110 m := by
  simp [A273110_set_M] at hm
  rcases hm with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact A273110_one_pos
  · exact A273110_seven_pos
  · exact A273110_pos_of_valid valid_23
  · exact A273110_pos_of_valid valid_31
  · exact A273110_pos_of_valid valid_39
  · exact A273110_pos_of_valid valid_47
  · exact A273110_pos_of_valid valid_55
  · exact A273110_pos_of_valid valid_71
  · exact A273110_pos_of_valid valid_79
  · exact A273110_pos_of_valid valid_119
  · exact A273110_pos_of_valid valid_151
  · exact A273110_pos_of_valid valid_191
  · exact A273110_pos_of_valid valid_311
  · exact A273110_pos_of_valid valid_671

/-! ## Davenport–Cassels lemma for `x² + y² + z²` -/

def q3 (v : ℤ × ℤ × ℤ) : ℤ := v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2

def b3 (u v : ℤ × ℤ × ℤ) : ℤ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

lemma q3_nonneg (v : ℤ × ℤ × ℤ) : 0 ≤ q3 v := by
  simp [q3]; nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]

lemma eq_zero_of_sq_add_sq_add_sq {x y z : ℤ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
  have hx := sq_nonneg x
  have hy := sq_nonneg y
  have hz := sq_nonneg z
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma q3_eq_zero_iff (v : ℤ × ℤ × ℤ) : q3 v = 0 ↔ v = (0, 0, 0) := by
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := eq_zero_of_sq_add_sq_add_sq (by simpa [q3] using h)
    ext <;> simp [h1, h2, h3]
  · rintro rfl; simp [q3]

/-- There is an integer nearest to `a / d` in the sense `2 |a - A d| ≤ d`. -/
lemma exists_nearest_int (a d : ℤ) (hd : 0 < d) :
    ∃ A : ℤ, 2 * |a - A * d| ≤ d := by
  set A0 := a / d
  have hr0 : 0 ≤ a % d := Int.emod_nonneg a (ne_of_gt hd)
  have hr1 : a % d < d := Int.emod_lt_of_pos a hd
  have hrem : a - A0 * d = a % d := by
    simp [A0]; linarith [Int.emod_add_ediv_mul a d]
  by_cases hle : 2 * (a % d) ≤ d
  · refine ⟨A0, ?_⟩
    rw [hrem, abs_of_nonneg hr0]; exact hle
  · refine ⟨A0 + 1, ?_⟩
    have hshift : a - (A0 + 1) * d = a % d - d := by
      linarith [hrem]
    rw [hshift]
    have hneg : a % d - d ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith

lemma exists_nearest_vec (a b c d : ℤ) (hd : 0 < d) :
    ∃ A B C : ℤ, 2 * |a - A * d| ≤ d ∧ 2 * |b - B * d| ≤ d ∧ 2 * |c - C * d| ≤ d := by
  obtain ⟨A, hA⟩ := exists_nearest_int a d hd
  obtain ⟨B, hB⟩ := exists_nearest_int b d hd
  obtain ⟨C, hC⟩ := exists_nearest_int c d hd
  exact ⟨A, B, C, hA, hB, hC⟩

lemma sq_le_of_two_abs_le {t d : ℤ} (h : 2 * |t| ≤ d) : 4 * t ^ 2 ≤ d ^ 2 := by
  nlinarith [abs_mul_abs_self t, sq_nonneg (d - 2 * |t|), abs_nonneg t]

set_option maxHeartbeats 800000

/-- Davenport–Cassels: a rational representation yields an integer representation. -/
lemma three_sq_of_rational {n : ℕ} {a b c d : ℤ} (hd : 0 < d)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = n * d ^ 2) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  -- Induction on the positive denominator `d.natAbs`.
  induction hdn : d.natAbs using Nat.strong_induction_on generalizing a b c d with
  | h D ih =>
    subst hdn
    obtain ⟨A, B, C, hA, hB, hC⟩ := exists_nearest_vec a b c d hd
    set ca : ℤ := a - A * d
    set cb : ℤ := b - B * d
    set cc : ℤ := c - C * d
    have hca : 2 * |ca| ≤ d := hA
    have hcb : 2 * |cb| ≤ d := hB
    have hcc : 2 * |cc| ≤ d := hC
    have hq4 : 4 * (ca ^ 2 + cb ^ 2 + cc ^ 2) ≤ 3 * d ^ 2 := by
      have := sq_le_of_two_abs_le hca
      have := sq_le_of_two_abs_le hcb
      have := sq_le_of_two_abs_le hcc
      nlinarith
    -- `Q(c) = d * d'` with `0 ≤ d' < d` (as integers, after sign).
    have hQexp : ca ^ 2 + cb ^ 2 + cc ^ 2 =
        a ^ 2 + b ^ 2 + c ^ 2 - 2 * d * (a * A + b * B + c * C) + d ^ 2 * (A ^ 2 + B ^ 2 + C ^ 2) := by
      simp [ca, cb, cc]; ring
    have hdvd : d ∣ (ca ^ 2 + cb ^ 2 + cc ^ 2) := by
      rw [hQexp, h]
      refine ⟨(n : ℤ) * d - 2 * (a * A + b * B + c * C) + d * (A ^ 2 + B ^ 2 + C ^ 2), by ring⟩
    obtain ⟨d', hd'⟩ := hdvd
    -- If `c = 0` then `d` divides `a,b,c`, and we may cancel.
    by_cases hc0 : ca = 0 ∧ cb = 0 ∧ cc = 0
    · obtain ⟨hca0, hcb0, hcc0⟩ := hc0
      have haA : a = A * d := by simp [ca] at hca0; linarith
      have hbB : b = B * d := by simp [cb] at hcb0; linarith
      have hcC : c = C * d := by simp [cc] at hcc0; linarith
      refine ⟨A, B, C, ?_⟩
      have hmul : d ^ 2 * (A ^ 2 + B ^ 2 + C ^ 2) = d ^ 2 * n := by
        have := h
        simp [haA, hbB, hcC] at this
        linear_combination this
      exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hd)) hmul
    · -- Otherwise `0 < Q(c) < d²`, so the new denominator is strictly smaller.
      have hQpos : 0 < ca ^ 2 + cb ^ 2 + cc ^ 2 := by
        apply lt_of_le_of_ne
        · nlinarith [sq_nonneg ca, sq_nonneg cb, sq_nonneg cc]
        · intro hz
          exact hc0 (eq_zero_of_sq_add_sq_add_sq hz.symm)
      -- Explicit new denominator (equals `Q(c) / d`).
      set d1 : ℤ :=
        (n : ℤ) * d - 2 * (a * A + b * B + c * C) + d * (A ^ 2 + B ^ 2 + C ^ 2)
      have hd1 : ca ^ 2 + cb ^ 2 + cc ^ 2 = d * d1 := by
        rw [hQexp, h]; ring
      have hd1_pos : 0 < d1 := by
        have hQpos' : 0 < d * d1 := by rwa [← hd1]
        nlinarith
      have hd1_lt : d1 < d := by
        have : 4 * (d * d1) ≤ 3 * d ^ 2 := by
          rw [← hd1]; exact hq4
        have : 4 * d1 ≤ 3 * d := by
          have hdpos : 0 < d := hd
          nlinarith
        nlinarith
      set r : ℤ := (n : ℤ) * d - (a * A + b * B + c * C)
      set a' : ℤ := (A ^ 2 + B ^ 2 + C ^ 2 - n) * a + 2 * r * A
      set b' : ℤ := (A ^ 2 + B ^ 2 + C ^ 2 - n) * b + 2 * r * B
      set c' : ℤ := (A ^ 2 + B ^ 2 + C ^ 2 - n) * c + 2 * r * C
      have hid : a' ^ 2 + b' ^ 2 + c' ^ 2 - n * d1 ^ 2 =
          (A ^ 2 + B ^ 2 + C ^ 2 - n) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - n * d ^ 2) := by
        simp [a', b', c', r, d1]; ring
      have hnew : a' ^ 2 + b' ^ 2 + c' ^ 2 = n * d1 ^ 2 := by
        have hz : a ^ 2 + b ^ 2 + c ^ 2 - n * d ^ 2 = 0 := by
          linear_combination h
        have := hid
        rw [hz, mul_zero] at this
        linarith
      have habs : d1.natAbs < d.natAbs := by
        have h1 : (d1.natAbs : ℤ) = d1 := Int.natAbs_of_nonneg hd1_pos.le
        have h2 : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd.le
        have : (d1.natAbs : ℤ) < d.natAbs := by
          rwa [h1, h2]
        exact Nat.cast_lt.mp this
      exact ih d1.natAbs habs hd1_pos hnew rfl

lemma three_sq_of_int {n : ℕ} {x y z : ℤ} (h : x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
  rw [← Int.natCast_inj]
  push_cast
  simpa [sq_abs] using h

lemma three_sq_of_rational_nat {n : ℕ} {a b c d : ℕ} (hd : 0 < d)
    (h : a ^ 2 + b ^ 2 + c ^ 2 = n * d ^ 2) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨x, y, z, hx⟩ := three_sq_of_rational (n := n) (a := a) (b := b) (c := c)
    (d := d) (by exact_mod_cast hd) (by exact_mod_cast h)
  exact three_sq_of_int hx

/-! ## Three-square theorem: sufficiency setup -/

/-- A natural number is *admissible* if it is not of the forbidden shape `4^k(8m+7)`. -/
def Admissible (n : ℕ) : Prop := ¬ ∃ k m, n = 4 ^ k * (8 * m + 7)

lemma admissible_of_three_sq {n a b c : ℕ} (h : a ^ 2 + b ^ 2 + c ^ 2 = n) :
    Admissible n :=
  three_sq_necessity h

/-- Squares modulo 8 never equal 7, so every square is admissible. -/
lemma admissible_sq (k : ℕ) : Admissible (k ^ 2) := by
  intro ⟨t, m, ht⟩
  have : ∃ a b c, a ^ 2 + b ^ 2 + c ^ 2 = k ^ 2 := ⟨k, 0, 0, by ring⟩
  obtain ⟨a, b, c, hs⟩ := this
  exact three_sq_necessity hs ⟨t, m, ht⟩

lemma admissible_two_sq (a b : ℕ) : Admissible (a ^ 2 + b ^ 2) :=
  three_sq_necessity (n := a ^ 2 + b ^ 2) (a := a) (b := b) (c := 0) (by ring)

/-- `4n` is admissible iff `n` is. -/
lemma admissible_mul_four_iff {n : ℕ} : Admissible (4 * n) ↔ Admissible n := by
  constructor
  · intro h ⟨k, m, hk⟩
    refine h ⟨k + 1, m, ?_⟩
    rw [hk, pow_succ]
    ring
  · intro h ⟨k, m, hk⟩
    cases k with
    | zero =>
      -- `4n = 8m+7` cannot hold: even vs odd.
      have he : Even (4 * n) := ⟨2 * n, by ring⟩
      have ho : Odd (8 * m + 7) := ⟨4 * m + 3, by ring⟩
      simp at hk
      rw [hk] at he
      exact Nat.not_even_iff_odd.mpr ho he
    | succ k =>
      apply h
      refine ⟨k, m, ?_⟩
      have : 4 * n = 4 * (4 ^ k * (8 * m + 7)) := by
        rw [hk, pow_succ]; ring
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) this

lemma pow_four_mul_div {n k : ℕ} (h : 4 ^ k ∣ n) :
    n = 4 ^ k * (n / 4 ^ k) :=
  (Nat.mul_div_cancel' h).symm

lemma admissible_pow_four_mul {n k : ℕ} :
    Admissible (4 ^ k * n) ↔ Admissible n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : 4 ^ (k + 1) * n = 4 * (4 ^ k * n) := by ring
    rw [this, admissible_mul_four_iff, ih]

lemma four_pow_padicValNat_dvd (n : ℕ) : 4 ^ padicValNat 4 n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hp : 4 ≠ 1 := by decide
    rw [padicValNat_def' hp hn]
    exact pow_multiplicity_dvd 4 n

lemma not_four_dvd_div_padicValNat {n : ℕ} (hn : n ≠ 0) :
    ¬ 4 ∣ n / 4 ^ padicValNat 4 n := by
  have hp : 4 ≠ 1 := by decide
  set v := padicValNat 4 n
  have hdiv : 4 ^ v ∣ n := four_pow_padicValNat_dvd n
  have hmul : n = 4 ^ v * (n / 4 ^ v) := pow_four_mul_div hdiv
  intro hd
  obtain ⟨t, ht⟩ := hd
  have hsucc : 4 ^ (v + 1) ∣ n := by
    rw [hmul, ht, pow_succ]
    exact ⟨t, by ring⟩
  have hmulte : v = multiplicity 4 n := padicValNat_def' hp hn
  have hf : FiniteMultiplicity 4 n := finiteMultiplicity_iff.2 ⟨hp, Nat.pos_iff_ne_zero.mpr hn⟩
  have : ¬ 4 ^ (v + 1) ∣ n := by
    rw [hmulte]
    exact (hf.multiplicity_lt_iff_not_dvd).1 (Nat.lt_succ_self _)
  exact this hsucc

lemma admissible_iff_odd_part {n : ℕ} :
    Admissible n ↔ Admissible (n / 4 ^ (padicValNat 4 n)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hdiv := four_pow_padicValNat_dvd n
    have hmul : n = 4 ^ padicValNat 4 n * (n / 4 ^ padicValNat 4 n) :=
      pow_four_mul_div hdiv
    conv_lhs => rw [hmul]
    exact admissible_pow_four_mul

/-- The three-square theorem (sufficiency). -/
lemma three_sq_of_admissible {n : ℕ} (hn : 0 < n) (h : Admissible n) :
    ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  sorry

lemma A273110_pos_of_admissible {n : ℕ} (hn : 0 < n) (h : Admissible n) :
    0 < A273110 n := by
  obtain ⟨a, b, c, hs⟩ := three_sq_of_admissible hn h
  exact A273110_pos_of_three_sq hn hs


/-
## Local solubility of three squares
-/

/-- Every residue class modulo an odd prime is a sum of three squares. -/
lemma three_sq_mod_odd_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ZMod p) :
    ∃ x y z : ZMod p, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨x, y, hxy⟩ := ZMod.sq_add_sq p n
  exact ⟨x, y, 0, by simpa using hxy⟩

lemma three_sq_mod_odd_prime_int (p : ℕ) [hp : Fact p.Prime] (hpo : p ≠ 2) (n : ℤ) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 ≡ n [ZMOD p] := by
  obtain ⟨x, y, z, h⟩ := three_sq_mod_odd_prime (p := p) hpo (n : ZMod p)
  refine ⟨x.val, y.val, z.val, ?_⟩
  refine (ZMod.intCast_eq_intCast_iff _ _ p).mp ?_
  push_cast
  simpa [ZMod.natCast_zmod_val] using h

lemma not_admissible_iff {n : ℕ} :
    ¬ Admissible n ↔ ∃ k m, n = 4 ^ k * (8 * m + 7) := by
  simp [Admissible]

/-- An odd admissible number is `1, 3 or 5` mod `8`. -/
lemma admissible_odd_mod_eight {n : ℕ} (hodd : Odd n) (h : Admissible n) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 := by
  have hlt : n % 8 < 8 := Nat.mod_lt n (by decide)
  have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hmod : n % 2 = (n % 8) % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).symm
  interval_cases hn8 : n % 8
  · omega
  · exact Or.inl rfl
  · omega
  · exact Or.inr (Or.inl rfl)
  · omega
  · exact Or.inr (Or.inr rfl)
  · omega
  · exfalso
    apply h
    refine ⟨0, n / 8, ?_⟩
    have : n = 8 * (n / 8) + n % 8 := (Nat.div_add_mod n 8).symm
    simp [hn8] at this
    simpa [pow_zero] using this
