import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

open Int

def thue2 (a b : ℤ) : ℤ := 2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3

def Pth (s b : ℤ) : ℤ := s ^ 3 + 6 * s ^ 2 * b + 9 * s * b ^ 2 - 4 * b ^ 3

lemma thue2_neg' (a b : ℤ) : thue2 (-a) (-b) = -thue2 a b := by
  simp [thue2]; ring

lemma thue2_sub_b_cube (a b : ℤ) :
    thue2 a b - b ^ 3 = (a + b) ^ 2 * (2 * a + 5 * b) := by
  simp [thue2]; ring

lemma thue2_eq_Pth {m b : ℤ} :
    4 * thue2 (-m) b = - Pth (2 * m - 5 * b) b := by
  simp [thue2, Pth]; ring

def checkThue2Box (N : ℕ) : Bool :=
  (List.range (2 * N + 1)).all fun i =>
    (List.range (2 * N + 1)).all fun j =>
      let a : ℤ := (i : ℤ) - (N : ℤ)
      let b : ℤ := (j : ℤ) - (N : ℤ)
      let t := thue2 a b
      decide (t.natAbs ≠ 1 ∨ (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1))

lemma checkThue2Box_12 : checkThue2Box 12 = true := by native_decide

lemma thue2_box {a b : ℤ} (ha : |a| ≤ 12) (hb : |b| ≤ 12)
    (h : thue2 a b = 1 ∨ thue2 a b = -1) :
    (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  have hc := checkThue2Box_12
  have habs : (thue2 a b).natAbs = 1 := by rcases h with h | h <;> simp [h]
  have hcheck :
      ∀ i j : ℕ, i < 25 → j < 25 →
        ((thue2 ((i : ℤ) - 12) ((j : ℤ) - 12)).natAbs ≠ 1 ∨
          ((i : ℤ) - 12 = 1 ∧ (j : ℤ) - 12 = -1) ∨
          ((i : ℤ) - 12 = -1 ∧ (j : ℤ) - 12 = 1)) := by
    intro i j hi hj
    have := hc
    simp [checkThue2Box] at this
    exact of_decide_eq_true (this i hi j hj)
  have hia : 0 ≤ a + 12 := by have := abs_le.mp ha; omega
  have hib : 0 ≤ b + 12 := by have := abs_le.mp hb; omega
  have hi : (a + 12).toNat < 25 := by
    have : ((a + 12).toNat : ℤ) = a + 12 := Int.toNat_of_nonneg hia
    have : a + 12 ≤ 24 := by have := abs_le.mp ha; omega
    omega
  have hj : (b + 12).toNat < 25 := by
    have : ((b + 12).toNat : ℤ) = b + 12 := Int.toNat_of_nonneg hib
    have : b + 12 ≤ 24 := by have := abs_le.mp hb; omega
    omega
  have haeq : ((a + 12).toNat : ℤ) - 12 = a := by
    have := Int.toNat_of_nonneg hia; omega
  have hbeq : ((b + 12).toNat : ℤ) - 12 = b := by
    have := Int.toNat_of_nonneg hib; omega
  have := hcheck (a + 12).toNat (b + 12).toNat hi hj
  simp only [haeq, hbeq] at this
  rcases this with hne | hsol | hsol
  · exact (hne habs).elim
  · exact Or.inl hsol
  · exact Or.inr hsol

lemma thue2_b_ge_three_a {a b : ℤ} (ha : 1 ≤ |a|) (hb : 3 * |a| ≤ |b|) :
    2 ≤ |thue2 a b| := by
  set A := |a|
  set B := |b|
  have e1 : |2 * a ^ 3| = 2 * A ^ 3 := by rw [abs_mul, abs_two, abs_pow]
  have e2 : |9 * a ^ 2 * b| = 9 * A ^ 2 * B := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e3 : |12 * a * b ^ 2| = 12 * A * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e4 : |6 * b ^ 3| = 6 * B ^ 3 := by rw [abs_mul, abs_ofNat, abs_pow]
  have hbound :
      |6 * b ^ 3| - |2 * a ^ 3| - |9 * a ^ 2 * b| - |12 * a * b ^ 2| ≤ |thue2 a b| := by
    have hx : thue2 a b =
        6 * b ^ 3 + (2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2) := by
      simp [thue2]; ring
    rw [hx]
    have hY : |2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2| ≤
        |2 * a ^ 3| + |9 * a ^ 2 * b| + |12 * a * b ^ 2| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    linarith [abs_sub_abs_le_abs_sub (6 * b ^ 3)
      (2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2)]
  have hnum : 6 * B ^ 3 - 2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2 ≥ 2 := by
    have hineq :
        6 * B ^ 3 - 2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2
          ≥ 6 * (3 * A) ^ 3 - 2 * A ^ 3 - 9 * A ^ 2 * (3 * A)
            - 12 * A * (3 * A) ^ 2 := by
      nlinarith [sq_nonneg A, pow_nonneg (abs_nonneg a) 3,
        sq_nonneg B, pow_nonneg (abs_nonneg b) 3]
    have hsimp : 6 * (3 * A) ^ 3 - 2 * A ^ 3 - 9 * A ^ 2 * (3 * A)
        - 12 * A * (3 * A) ^ 2 = 25 * A ^ 3 := by ring
    have : 25 * A ^ 3 ≥ 25 := by
      have : (1 : ℤ) ≤ A ^ 3 := one_le_pow₀ ha
      nlinarith
    linarith
  nlinarith

lemma thue2_a_ge_six_b {a b : ℤ} (hb : 1 ≤ |b|) (ha : 6 * |b| ≤ |a|) :
    2 ≤ |thue2 a b| := by
  set A := |a|
  set B := |b|
  have e1 : |2 * a ^ 3| = 2 * A ^ 3 := by rw [abs_mul, abs_two, abs_pow]
  have e2 : |9 * a ^ 2 * b| = 9 * A ^ 2 * B := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e3 : |12 * a * b ^ 2| = 12 * A * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_ofNat, abs_pow]; ring
  have e4 : |6 * b ^ 3| = 6 * B ^ 3 := by rw [abs_mul, abs_ofNat, abs_pow]
  have hbound :
      |2 * a ^ 3| - |9 * a ^ 2 * b| - |12 * a * b ^ 2| - |6 * b ^ 3| ≤ |thue2 a b| := by
    have hx : thue2 a b =
        2 * a ^ 3 + (9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3) := by
      simp [thue2]; ring
    rw [hx]
    have hY : |9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3| ≤
        |9 * a ^ 2 * b| + |12 * a * b ^ 2| + |6 * b ^ 3| :=
      (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
    linarith [abs_sub_abs_le_abs_sub (2 * a ^ 3)
      (9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3)]
  have hnum : 2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2 - 6 * B ^ 3 ≥ 2 := by
    have hineq :
        2 * A ^ 3 - 9 * A ^ 2 * B - 12 * A * B ^ 2 - 6 * B ^ 3
          ≥ 2 * (6 * B) ^ 3 - 9 * (6 * B) ^ 2 * B
            - 12 * (6 * B) * B ^ 2 - 6 * B ^ 3 := by
      nlinarith [sq_nonneg B, pow_nonneg (abs_nonneg b) 3]
    have hsimp : 2 * (6 * B) ^ 3 - 9 * (6 * B) ^ 2 * B
        - 12 * (6 * B) * B ^ 2 - 6 * B ^ 3 = 30 * B ^ 3 := by ring
    have : 30 * B ^ 3 ≥ 30 := by
      have : (1 : ℤ) ≤ B ^ 3 := one_le_pow₀ hb
      nlinarith
    linarith
  nlinarith

lemma thue2_pos_pos {a b : ℤ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 2 ≤ |thue2 a b| := by
  have hpos : 6 ≤ thue2 a b := by
    have ha3 : 1 ≤ a ^ 3 := one_le_pow₀ ha
    have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
    have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha
    have hb2 : 1 ≤ b ^ 2 := one_le_pow₀ hb
    simp [thue2]; nlinarith
  have : 0 ≤ thue2 a b := by linarith
  rw [abs_of_nonneg this]; linarith

lemma thue2_neg_neg {a b : ℤ} (ha : a ≤ -1) (hb : b ≤ -1) : 2 ≤ |thue2 a b| := by
  have := thue2_pos_pos (a := -a) (b := -b) (by omega) (by omega)
  rwa [thue2_neg', abs_neg] at this

lemma Pth_succ (s b : ℤ) :
    Pth (s + 1) b - Pth s b = 3 * s ^ 2 + 12 * s * b + 9 * b ^ 2 + 3 * s + 6 * b + 1 := by
  simp [Pth]; ring

lemma Pth_mono {s b : ℤ} (hs : 0 ≤ s) (hb : 0 ≤ b) :
    Pth s b ≤ Pth (s + 1) b := by
  have := Pth_succ s b
  nlinarith [sq_nonneg s, sq_nonneg b]

lemma Pth_mono_le {s t b : ℤ} (hs : 0 ≤ s) (hst : s ≤ t) (hb : 0 ≤ b) :
    Pth s b ≤ Pth t b := by
  have hdiff : t = s + (t - s) := by omega
  have hn : 0 ≤ t - s := by omega
  -- induct on (t-s).toNat
  have := Int.toNat_of_nonneg hn
  revert t
  intro t hst hdiff hn heq
  -- use induction on nat
  have hN : ∀ n : ℕ, Pth s b ≤ Pth (s + n) b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : 0 ≤ s + n := by omega
      have := Pth_mono (s := s + n) (b := b) this hb
      simpa [add_assoc] using le_trans ih this
  have : t = s + (t - s).toNat := by
    have : ((t - s).toNat : ℤ) = t - s := Int.toNat_of_nonneg hn
    omega
  rw [this]
  exact hN _

lemma thue2_m_ge_three_b {m b : ℤ} (hb : 1 ≤ b) (hm : 3 * b ≤ m) :
    thue2 (-m) b ≤ -3 := by
  have hexp : thue2 (-m) b =
      -2 * m ^ 3 + 9 * m ^ 2 * b - 12 * m * b ^ 2 + 6 * b ^ 3 := by
    simp [thue2]; ring
  -- f decreasing on [3b, ∞)
  have hf3 : thue2 (-(3 * b)) b = -3 * b ^ 3 := by
    simp [thue2]; ring
  have hle : thue2 (-m) b ≤ thue2 (-(3 * b)) b := by
    -- compare via expansion: f(m)-f(3b) ≤ 0
    have : thue2 (-m) b - thue2 (-(3 * b)) b =
        -2 * (m ^ 3 - (3 * b) ^ 3) + 9 * b * (m ^ 2 - (3 * b) ^ 2)
          - 12 * b ^ 2 * (m - 3 * b) := by
      rw [hexp]; simp [thue2]; ring
    have hfac : m ^ 3 - (3 * b) ^ 3 = (m - 3 * b) * (m ^ 2 + m * (3 * b) + (3 * b) ^ 2) := by
      ring
    have hsq : m ^ 2 - (3 * b) ^ 2 = (m - 3 * b) * (m + 3 * b) := by ring
    have : thue2 (-m) b - thue2 (-(3 * b)) b =
        (m - 3 * b) * (-2 * (m ^ 2 + 3 * b * m + 9 * b ^ 2)
          + 9 * b * (m + 3 * b) - 12 * b ^ 2) := by
      rw [this, hfac, hsq]; ring
    have hpoly : -2 * (m ^ 2 + 3 * b * m + 9 * b ^ 2) + 9 * b * (m + 3 * b) - 12 * b ^ 2
        = -2 * m ^ 2 - 6 * b * m + 3 * b * m - 3 * b ^ 2 := by ring
    -- simpler: -2m² + 3bm - 3b² wait
    have : -2 * (m ^ 2 + 3 * b * m + 9 * b ^ 2) + 9 * b * (m + 3 * b) - 12 * b ^ 2
        = -2 * m ^ 2 + 3 * b * m - 3 * b ^ 2 := by ring
    have hneg : -2 * m ^ 2 + 3 * b * m - 3 * b ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (2 * m - b), sq_nonneg m, sq_nonneg b]
    nlinarith
  have : -3 * b ^ 3 ≤ -3 := by
    have : 1 ≤ b ^ 3 := one_le_pow₀ hb
    nlinarith
  linarith

/-- `Pth s b ≠ ±4` for `b ≥ 13` and `1 ≤ s < b`. -/
lemma Pth_ne_pm_four {s b : ℤ} (hb : 13 ≤ b) (hs : 1 ≤ s) (hsb : s < b) :
    Pth s b ≠ 4 ∧ Pth s b ≠ -4 := by
  -- Check a large finite range by a boolean predicate, then use monotonicity + 5/14
  -- For all b ≥ 13 we evaluate the two straddling values around 5b/14 via r = 5b % 14.
  have hb0 : 0 ≤ b := by omega
  have hs0 : 0 ≤ s := by omega
  -- Define s0 = (5 * b) / 14
  set r := (5 * b) % 14 with hrdef
  set s0 := (5 * b - r) / 14 with hs0def
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have hr14 : r < 14 := Int.emod_lt_of_pos _ (by decide)
  have hdiv : 14 * s0 = 5 * b - r := by
    have : r = 5 * b % 14 := hrdef
    have : 5 * b = 14 * ((5 * b) / 14) + (5 * b) % 14 := (Int.ediv_add_emod (5 * b) 14).symm
    have : s0 = (5 * b) / 14 := by
      have : 5 * b - r = 5 * b - (5 * b % 14) := by simp [hrdef]
      rw [hs0def, this, Int.sub_emod_emod_eq? ] 
      sorry
    sorry
  sorry

lemma thue2_of_eq_pm_one {a b : ℤ} (h : thue2 a b = 1 ∨ thue2 a b = -1) :
    (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) := by
  have habs : |thue2 a b| = 1 := by rcases h with h | h <;> simp [h]
  by_cases hb0 : b = 0
  · subst hb0
    have : thue2 a 0 = 2 * a ^ 3 := by simp [thue2]
    rw [this] at h; rcases h with h | h <;> omega
  by_cases ha0 : a = 0
  · subst ha0
    have : thue2 0 b = 6 * b ^ 3 := by simp [thue2]
    rw [this] at h; rcases h with h | h <;> omega
  have ha1 : 1 ≤ |a| := Int.one_le_abs ha0
  have hb1 : 1 ≤ |b| := Int.one_le_abs hb0
  by_cases hbox : |a| ≤ 12 ∧ |b| ≤ 12
  · exact thue2_box hbox.1 hbox.2 h
  · have hge : 2 ≤ |thue2 a b| := by
      by_cases hbigb : 3 * |a| ≤ |b|
      · exact thue2_b_ge_three_a ha1 hbigb
      · by_cases hbiga : 6 * |b| ≤ |a|
        · exact thue2_a_ge_six_b hb1 hbiga
        · by_cases hapos : 0 ≤ a
          · by_cases hbpos : 0 ≤ b
            · exact thue2_pos_pos (by omega) (by omega)
            · -- a ≥ 1, b ≤ -1 → flip
              have h' : thue2 (-a) (-b) = 1 ∨ thue2 (-a) (-b) = -1 := by
                rw [thue2_neg']; rcases h with hh | hh <;> simp [hh]
              -- (-a) ≤ -1, (-b) ≥ 1; if this is the unit then |a|=|b|=1, in the box
              -- We'll handle via mapping to a≤-1, b≥1 below by using the same argument
              -- Reduce: let a' = -a ≤ -1, b' = -b ≥ 1
              have ha' : -a ≤ -1 := by omega
              have hb' : 1 ≤ -b := by omega
              -- continue in the a≤-1, b≥1 case on (-a,-b)
              -- Use identity on (-a, -b) wait thue2(-a,-b) = -thue2(a,b)
              -- Treat (A,B)=(-a,-b): A≤-1, B≥1
              set A := -a
              set B := -b
              have hA : A ≤ -1 := by omega
              have hB : 1 ≤ B := by omega
              set m := -A
              have hm : A = -m := by omega
              have hm1 : 1 ≤ m := by omega
              have hid : thue2 A B = B ^ 3 + (A + B) ^ 2 * (2 * A + 5 * B) := by
                have := thue2_sub_b_cube A B; linarith
              have hid2 : thue2 (-m) B = B ^ 3 + (B - m) ^ 2 * (5 * B - 2 * m) := by
                convert hid using 1 <;> (try omega); ring
              by_cases hmb : m ≤ B
              · by_cases heq : m = B
                · subst heq
                  have : thue2 (-B) B = B ^ 3 := by rw [hid2]; ring
                  have : |A| = 1 ∧ |B| = 1 := by
                    have : B ^ 3 = 1 ∨ B ^ 3 = -1 := by
                      have : thue2 A B = 1 ∨ thue2 A B = -1 := h'
                      rw [show A = -B by omega] at this
                      rwa [this] at this
                    have : B = 1 := by
                      have : 1 ≤ B ^ 3 := one_le_pow₀ hB
                      rcases this with h3 | h3 <;> omega
                    omega
                  have : |a| ≤ 12 ∧ |b| ≤ 12 := by omega
                  exact (hbox this).elim
                · have : 2 ≤ |thue2 A B| := by
                    have hlt : m < B := by omega
                    have : 1 ≤ (B - m) ^ 2 := one_le_pow₀ (by omega)
                    have : 1 ≤ 5 * B - 2 * m := by nlinarith
                    have : 1 ≤ B ^ 3 := one_le_pow₀ hB
                    have hge : 2 ≤ thue2 (-m) B := by rw [hid2]; nlinarith
                    have hnn : 0 ≤ thue2 (-m) B := by rw [hid2]; nlinarith
                    rw [show A = -m by omega, abs_of_nonneg hnn]; exact hge
                  simpa [thue2_neg', abs_neg, A, B] using this
              · by_cases h25 : 2 * m ≤ 5 * B
                · have hne : 2 * m ≠ 5 * B := by
                    intro heq
                    have : 5 * B - 2 * m = 0 := by omega
                    have : thue2 (-m) B = B ^ 3 := by rw [hid2, this]; ring
                    have : B = 1 := by
                      have : B ^ 3 = 1 ∨ B ^ 3 = -1 := by
                        have : thue2 A B = 1 ∨ thue2 A B = -1 := h'
                        rw [show A = -m by omega, this] at this
                        exact this
                      have : 1 ≤ B ^ 3 := one_le_pow₀ hB
                      rcases this with h3 | h3 <;> omega
                    omega
                  have : 2 ≤ |thue2 A B| := by
                    have hge1 : 1 ≤ 5 * B - 2 * m := by omega
                    have : 1 ≤ (m - B) ^ 2 := one_le_pow₀ (by omega)
                    have hsq : (B - m) ^ 2 = (m - B) ^ 2 := by ring
                    have : 1 ≤ B ^ 3 := one_le_pow₀ hB
                    have hge : 2 ≤ thue2 (-m) B := by rw [hid2, hsq]; nlinarith
                    have hnn : 0 ≤ thue2 (-m) B := by rw [hid2, hsq]; nlinarith
                    rw [show A = -m by omega, abs_of_nonneg hnn]; exact hge
                  simpa [thue2_neg', abs_neg, A, B] using this
                · -- m > 5B/2
                  by_cases hm3 : 3 * B ≤ m
                  · have := thue2_m_ge_three_b hB hm3
                    have : thue2 A B ≤ -3 := by simpa [show A = -m by omega]
                    have : |thue2 A B| ≥ 2 := by
                      have : thue2 A B < 0 := by linarith
                      rw [abs_of_neg this]; linarith
                    simpa [thue2_neg', abs_neg, A, B] using this
                  · -- 5B/2 < m < 3B, and max(|a|,|b|)≥13 so B≥13 or m≥13
                    have hB13 : 13 ≤ B ∨ 13 ≤ m := by
                      have : 13 ≤ |a| ∨ 13 ≤ |b| := by omega
                      omega
                    have hb13 : 13 ≤ B := by
                      rcases hB13 with h | h
                      · have : m < 3 * B := by omega
                        have : 13 ≤ m := h
                        nlinarith
                      · exact h
                    have hspos : 1 ≤ 2 * m - 5 * B := by omega
                    have hslt : 2 * m - 5 * B < B := by nlinarith
                    have hP := Pth_ne_pm_four (s := 2 * m - 5 * B) (b := B)
                      hb13 hspos hslt
                    have heqP : 4 * thue2 (-m) B = - Pth (2 * m - 5 * B) B := thue2_eq_Pth
                    have : |thue2 A B| ≠ 1 := by
                      intro habs'
                      have : thue2 A B = 1 ∨ thue2 A B = -1 := by
                        have : |thue2 A B| = 1 := habs'
                        rcases eq_or_eq_neg_of_abs_eq this with h1 | h1
                        · exact Or.inl h1
                        · exact Or.inr h1
                      have : Pth (2 * m - 5 * B) B = 4 ∨ Pth (2 * m - 5 * B) B = -4 := by
                        have : 4 * thue2 A B = - Pth (2 * m - 5 * B) B := by
                          simpa [show A = -m by omega] using heqP
                        rcases this with h1 | h1 <;> omega
                      rcases this with hp | hp
                      · exact hP.1 hp
                      · exact hP.2 hp
                    have : |thue2 a b| ≠ 1 := by
                      simpa [thue2_neg', abs_neg, A, B] using this
                    exact (this habs).elim
          · -- a ≤ -1
            by_cases hbpos : 0 ≤ b
            · -- a ≤ -1, b ≥ 1: same as the inner case above
              set m := -a
              have hm : a = -m := by omega
              have hm1 : 1 ≤ m := by omega
              have hB : 1 ≤ b := by omega
              have hid : thue2 a b = b ^ 3 + (a + b) ^ 2 * (2 * a + 5 * b) := by
                have := thue2_sub_b_cube a b; linarith
              have hid2 : thue2 (-m) b = b ^ 3 + (b - m) ^ 2 * (5 * b - 2 * m) := by
                convert hid using 1 <;> (try omega); ring
              by_cases hmb : m ≤ b
              · by_cases heq : m = b
                · subst heq
                  have : thue2 (-b) b = b ^ 3 := by rw [hid2]; ring
                  have : |a| = 1 ∧ |b| = 1 := by
                    have : b ^ 3 = 1 ∨ b ^ 3 = -1 := by
                      rw [show -b = a by omega] at this
                      rwa [this] at h
                    have : b = 1 := by
                      have : 1 ≤ b ^ 3 := one_le_pow₀ hB
                      rcases this with h3 | h3 <;> omega
                    omega
                  have : |a| ≤ 12 ∧ |b| ≤ 12 := by omega
                  exact (hbox this).elim
                · have hlt : m < b := by omega
                  have : 1 ≤ (b - m) ^ 2 := one_le_pow₀ (by omega)
                  have : 1 ≤ 5 * b - 2 * m := by nlinarith
                  have : 1 ≤ b ^ 3 := one_le_pow₀ hB
                  have hge' : 2 ≤ thue2 (-m) b := by rw [hid2]; nlinarith
                  have hnn : 0 ≤ thue2 (-m) b := by rw [hid2]; nlinarith
                  rw [show a = -m by omega, abs_of_nonneg hnn]; exact hge'
              · by_cases h25 : 2 * m ≤ 5 * b
                · have hne : 2 * m ≠ 5 * b := by
                    intro heq
                    have : 5 * b - 2 * m = 0 := by omega
                    have : thue2 (-m) b = b ^ 3 := by rw [hid2, this]; ring
                    have : b = 1 := by
                      have : b ^ 3 = 1 ∨ b ^ 3 = -1 := by
                        rw [show -m = a by omega, this] at h; exact h
                      have : 1 ≤ b ^ 3 := one_le_pow₀ hB
                      rcases this with h3 | h3 <;> omega
                    omega
                  have hge1 : 1 ≤ 5 * b - 2 * m := by omega
                  have : 1 ≤ (m - b) ^ 2 := one_le_pow₀ (by omega)
                  have hsq : (b - m) ^ 2 = (m - b) ^ 2 := by ring
                  have : 1 ≤ b ^ 3 := one_le_pow₀ hB
                  have hge' : 2 ≤ thue2 (-m) b := by rw [hid2, hsq]; nlinarith
                  have hnn : 0 ≤ thue2 (-m) b := by rw [hid2, hsq]; nlinarith
                  rw [show a = -m by omega, abs_of_nonneg hnn]; exact hge'
                · by_cases hm3 : 3 * b ≤ m
                  · have := thue2_m_ge_three_b hB hm3
                    have : thue2 a b ≤ -3 := by simpa [show a = -m by omega]
                    have : thue2 a b < 0 := by linarith
                    rw [abs_of_neg this]; linarith
                  · have hb13 : 13 ≤ b := by
                      have : 13 ≤ |a| ∨ 13 ≤ |b| := by omega
                      rcases this with h' | h'
                      · have : m < 3 * b := by omega
                        have : 13 ≤ m := by simpa [m, abs_of_nonpos (by omega)] using h'
                        nlinarith
                      · simpa [abs_of_nonneg (by omega)] using h'
                    have hspos : 1 ≤ 2 * m - 5 * b := by omega
                    have hslt : 2 * m - 5 * b < b := by nlinarith
                    have hP := Pth_ne_pm_four (s := 2 * m - 5 * b) (b := b)
                      hb13 hspos hslt
                    have heqP : 4 * thue2 (-m) b = - Pth (2 * m - 5 * b) b := thue2_eq_Pth
                    have : |thue2 a b| ≠ 1 := by
                      intro _
                      have : Pth (2 * m - 5 * b) b = 4 ∨ Pth (2 * m - 5 * b) b = -4 := by
                        have : 4 * thue2 a b = - Pth (2 * m - 5 * b) b := by
                          simpa [show a = -m by omega] using heqP
                        rcases h with h1 | h1 <;> omega
                      rcases this with hp | hp
                      · exact hP.1 hp
                      · exact hP.2 hp
                    exact (this habs).elim
            · exact thue2_neg_neg (by omega) (by omega)
    rcases h with hh | hh <;> (rw [hh] at hge; revert hge; decide)
