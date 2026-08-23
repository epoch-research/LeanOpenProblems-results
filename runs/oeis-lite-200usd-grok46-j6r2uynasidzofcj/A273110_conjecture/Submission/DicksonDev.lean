import FormalConjectures.Util.ProblemImports

open Nat Int

def Qform (a b c : ℤ) : ℤ := a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2

def Tform (a b c A B C : ℤ) : ℤ := a * A + 2 * b * B + 3 * c * C

lemma Qform_nearest_bound {ca cb cc d : ℤ}
    (ha : 2 * |ca| ≤ d) (hb : 2 * |cb| ≤ d) (hc : 2 * |cc| ≤ d) :
    4 * Qform ca cb cc ≤ 6 * d ^ 2 := by
  have h1 : 4 * ca ^ 2 ≤ d ^ 2 := by
    nlinarith [abs_mul_abs_self ca, sq_nonneg (d - 2 * |ca|), abs_nonneg ca]
  have h2 : 4 * cb ^ 2 ≤ d ^ 2 := by
    nlinarith [abs_mul_abs_self cb, sq_nonneg (d - 2 * |cb|), abs_nonneg cb]
  have h3 : 4 * cc ^ 2 ≤ d ^ 2 := by
    nlinarith [abs_mul_abs_self cc, sq_nonneg (d - 2 * |cc|), abs_nonneg cc]
  simp only [Qform]
  nlinarith

lemma dc_identity (a b c A B C : ℤ) (N d : ℤ) :
    let Qm := Qform A B C
    let T := Tform a b c A B C
    let p := Qm - N
    let q := 2 * (N * d - T)
    let a' := p * a + q * A
    let b' := p * b + q * B
    let c' := p * c + q * C
    let d1 := N * d - 2 * T + d * Qm
    a' ^ 2 + 2 * b' ^ 2 + 3 * c' ^ 2 - N * d1 ^ 2 =
      (Qm - N) ^ 2 * (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 - N * d ^ 2) := by
  simp [Qform, Tform]
  ring

lemma Qform_expand (a b c A B C d : ℤ) :
    Qform (a - A * d) (b - B * d) (c - C * d) =
      Qform a b c - 2 * d * Tform a b c A B C + d ^ 2 * Qform A B C := by
  simp [Qform, Tform]; ring

lemma Qform_nonneg (a b c : ℤ) : 0 ≤ Qform a b c := by
  simp [Qform]; nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

lemma Qform_eq_zero {a b c : ℤ} (h : Qform a b c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  simp [Qform] at h
  have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hc : c = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  exact ⟨ha, hb, hc⟩

lemma exists_nearest_int' (a d : ℤ) (hd : 0 < d) :
    ∃ A : ℤ, 2 * |a - A * d| ≤ d := by
  -- remainder in [0, d)
  have hr : 0 ≤ a % d ∧ a % d < d := ⟨Int.emod_nonneg a hd.ne', Int.emod_lt_of_pos a hd⟩
  have hrem : a = d * (a / d) + a % d := (Int.mul_ediv_add_emod a d).symm
  by_cases hle : 2 * (a % d) ≤ d
  · refine ⟨a / d, ?_⟩
    have : a - (a / d) * d = a % d := by linarith
    rw [this, abs_of_nonneg hr.1]; exact hle
  · refine ⟨a / d + 1, ?_⟩
    have : a - (a / d + 1) * d = a % d - d := by linarith
    rw [this]
    have hneg : a % d - d ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith

lemma exists_nearest_vec' (a b c d : ℤ) (hd : 0 < d) :
    ∃ A B C : ℤ, 2 * |a - A * d| ≤ d ∧ 2 * |b - B * d| ≤ d ∧ 2 * |c - C * d| ≤ d := by
  obtain ⟨A, hA⟩ := exists_nearest_int' a d hd
  obtain ⟨B, hB⟩ := exists_nearest_int' b d hd
  obtain ⟨C, hC⟩ := exists_nearest_int' c d hd
  exact ⟨A, B, C, hA, hB, hC⟩

lemma Qform_dvd_of_rep {a b c A B C d : ℤ} {N : ℕ}
    (h : Qform a b c = N * d ^ 2) :
    d ∣ Qform (a - A * d) (b - B * d) (c - C * d) := by
  rw [Qform_expand, h]
  refine ⟨(N : ℤ) * d - 2 * Tform a b c A B C + d * Qform A B C, ?_⟩
  ring

/-- Odd d: nearest error satisfies |coord| ≤ (d-1)/2, so 4Q ≤ 6(d-1)². -/
lemma Qform_odd_nearest_bound {ca cb cc d : ℤ} (hodd : Odd d)
    (ha : 2 * |ca| ≤ d) (hb : 2 * |cb| ≤ d) (hc : 2 * |cc| ≤ d) :
    2 * |ca| ≤ d - 1 ∧ 2 * |cb| ≤ d - 1 ∧ 2 * |cc| ≤ d - 1 := by
  have : d % 2 = 1 := Int.odd_iff.mp hodd
  omega

lemma four_Q_le_six_sq {ca cb cc t : ℤ}
    (ha : 2 * |ca| ≤ t) (hb : 2 * |cb| ≤ t) (hc : 2 * |cc| ≤ t) :
    4 * Qform ca cb cc ≤ 6 * t ^ 2 :=
  Qform_nearest_bound ha hb hc

lemma descent_d1_lt_of_odd {ca cb cc d : ℤ} {d1 : ℤ}
    (hd : 0 < d) (hodd : Odd d) (hd1 : Qform ca cb cc = d * d1)
    (ha : 2 * |ca| ≤ d) (hb : 2 * |cb| ≤ d) (hc : 2 * |cc| ≤ d)
    (hpos : 0 < Qform ca cb cc) :
    0 < d1 ∧ (d ≤ 5 → d1 < d) := by
  have hle := Qform_odd_nearest_bound hodd ha hb hc
  have hbnd := four_Q_le_six_sq hle.1 hle.2.1 hle.2.2
  have hd1pos : 0 < d1 := by
    have : 0 < d * d1 := by rwa [← hd1]
    nlinarith
  refine ⟨hd1pos, ?_⟩
  intro hd5
  have hbound : 4 * (d * d1) ≤ 6 * (d - 1) ^ 2 := by
    rw [← hd1]; exact hbnd
  have h1 : d = 1 ∨ d = 3 ∨ d = 5 := by
    have : d % 2 = 1 := Int.odd_iff.mp hodd
    omega
  rcases h1 with rfl | rfl | rfl
  · -- d = 1: nearest error is 0, so Q = 0, contradiction
    have h0 : 2 * |ca| ≤ 0 ∧ 2 * |cb| ≤ 0 ∧ 2 * |cc| ≤ 0 := hle
    have : ca = 0 ∧ cb = 0 ∧ cc = 0 := by omega
    simp [Qform, this] at hpos
  · -- d = 3: 4*3*d1 ≤ 6*4 = 24 ⇒ d1 ≤ 2
    have : 12 * d1 ≤ 24 := by
      convert hbound using 1 <;> ring
    omega
  · -- d = 5: 4*5*d1 ≤ 6*16 = 96 ⇒ d1 ≤ 4
    have : 20 * d1 ≤ 96 := by
      convert hbound using 1 <;> ring
    omega

lemma dc_new_rep {a b c A B C : ℤ} {N : ℕ} {d : ℤ}
    (h : Qform a b c = N * d ^ 2) :
    let T := Tform a b c A B C
    let Qm := Qform A B C
    let p := Qm - N
    let q := 2 * (N * d - T)
    let d1 := N * d - 2 * T + d * Qm
    Qform (p * a + q * A) (p * b + q * B) (p * c + q * C) = N * d1 ^ 2 := by
  intro T Qm p q d1
  have hid := dc_identity a b c A B C N d
  simp [Qform] at hid ⊢
  have hz : a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2 - N * d ^ 2 = 0 := by
    have := h; simp [Qform] at this; linarith
  have : Qform (p * a + q * A) (p * b + q * B) (p * c + q * C) - N * d1 ^ 2 = 0 := by
    simp [Qform, p, q, d1, T, Qm] at hid ⊢
    -- unfold lets in hid
    nlinarith [hid, hz]
  linarith

lemma dc_new_rep' {a b c A B C : ℤ} {N : ℕ} {d : ℤ}
    (h : Qform a b c = (N : ℤ) * d ^ 2) :
    Qform
      ((Qform A B C - N) * a + 2 * ((N : ℤ) * d - Tform a b c A B C) * A)
      ((Qform A B C - N) * b + 2 * ((N : ℤ) * d - Tform a b c A B C) * B)
      ((Qform A B C - N) * c + 2 * ((N : ℤ) * d - Tform a b c A B C) * C) =
    (N : ℤ) *
      ((N : ℤ) * d - 2 * Tform a b c A B C + d * Qform A B C) ^ 2 := by
  have hid := dc_identity a b c A B C (N : ℤ) d
  simp [Qform, Tform] at hid h ⊢
  nlinarith

lemma d1_eq_Q_div {a b c A B C d : ℤ} {N : ℕ}
    (h : Qform a b c = (N : ℤ) * d ^ 2) :
    Qform (a - A * d) (b - B * d) (c - C * d) =
      d * ((N : ℤ) * d - 2 * Tform a b c A B C + d * Qform A B C) := by
  rw [Qform_expand, h]; ring

/-- From a rational representation with odd denominator `d ≤ 5`, get an integral one. -/
lemma dickson_int_of_rat_small {N : ℕ} {a b c d : ℤ}
    (hd : 0 < d) (hodd : Odd d) (hd5 : d ≤ 5)
    (h : Qform a b c = (N : ℤ) * d ^ 2) :
    ∃ x y z : ℤ, Qform x y z = N := by
  induction hdn : d.natAbs using Nat.strong_induction_on generalizing a b c d with
  | h D ih =>
    subst hdn
    obtain ⟨A, B, C, hA, hB, hC⟩ := exists_nearest_vec' a b c d hd
    set ca := a - A * d
    set cb := b - B * d
    set cc := c - C * d
    have hQd : Qform ca cb cc =
        d * ((N : ℤ) * d - 2 * Tform a b c A B C + d * Qform A B C) :=
      d1_eq_Q_div h
    set d1 := (N : ℤ) * d - 2 * Tform a b c A B C + d * Qform A B C
    by_cases hc0 : ca = 0 ∧ cb = 0 ∧ cc = 0
    · obtain ⟨hca0, hcb0, hcc0⟩ := hc0
      have haA : a = A * d := by simp [ca] at hca0; linarith
      have hbB : b = B * d := by simp [cb] at hcb0; linarith
      have hcC : c = C * d := by simp [cc] at hcc0; linarith
      refine ⟨A, B, C, ?_⟩
      have hmul : d ^ 2 * Qform A B C = d ^ 2 * N := by
        have := h
        simp [Qform, haA, hbB, hcC] at this ⊢
        nlinarith
      have hdz : d ≠ 0 := hd.ne'
      have : Qform A B C = N := by
        have := mul_left_cancel₀ (pow_ne_zero 2 hdz) hmul
        simpa [Qform] using this
      simpa [Qform] using this
    · have hQpos : 0 < Qform ca cb cc := by
        apply lt_of_le_of_ne (Qform_nonneg _ _ _)
        intro hz
        exact hc0 (Qform_eq_zero hz.symm)
      have hdec := descent_d1_lt_of_odd hd hodd (by simpa [d1] using hQd)
        hA hB hC hQpos
      have hd1pos := hdec.1
      have hd1lt : d1 < d := hdec.2 hd5
      have hnew := dc_new_rep' (a := a) (b := b) (c := c) (A := A) (B := B) (C := C) h
      have hd1odd : Odd d1 := by
        -- d odd, will be proved later in general; for d≤5, d1 < d and d1>0
        -- so d1 = 1,2,3,4. Need odd. If even, cancel later.
        -- For now use that d1.natAbs < d.natAbs and apply ih if we can make it odd.
        have : d1.natAbs < d.natAbs := by
          have h1 : (d1.natAbs : ℤ) = d1 := Int.natAbs_of_nonneg hd1pos.le
          have h2 : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd.le
          exact Nat.cast_lt.mp (by rw [h1, h2]; exact hd1lt)
        -- fall back: if d1 even we still induct if we drop oddness? keep it simple:
        -- check d1 is 1,3 (since d≤5, d1<d, d1>0)
        have hsmall : d1 = 1 ∨ d1 = 2 ∨ d1 = 3 ∨ d1 = 4 := by omega
        -- 2,4 even: Q of new point = N d1^2 so divisible by 4. Handle by scaling.
        sorry
      sorry
