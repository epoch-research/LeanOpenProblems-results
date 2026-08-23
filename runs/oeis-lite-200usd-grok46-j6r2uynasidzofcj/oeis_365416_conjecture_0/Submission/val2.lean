import Mathlib

open Int Zsqrtd

/-!
Pell solutions of `X^2 - q Y^2 = -2` with `q = r^2 + 2`, via `ℤ√q`.
-/

def alpha (r : ℤ) : ℤ√(r ^ 2 + 2) := ⟨r, 1⟩

lemma alpha_norm (r : ℤ) : (alpha r).norm = -2 := by
  simp [alpha, Zsqrtd.norm_def]
  ring

def eps (r : ℤ) : ℤ√(r ^ 2 + 2) := ⟨r ^ 2 + 1, r⟩

lemma eps_norm (r : ℤ) : (eps r).norm = 1 := by
  simp [eps, Zsqrtd.norm_def]
  ring

lemma eps_pow_norm (r : ℤ) : ∀ k : ℕ, ((eps r) ^ k).norm = 1
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ (eps r) k, Zsqrtd.norm_mul, eps_pow_norm r k, eps_norm, mul_one]

def pellZ (r : ℤ) (k : ℕ) : ℤ√(r ^ 2 + 2) := alpha r * (eps r) ^ k

def pX (r : ℤ) (k : ℕ) : ℤ := (pellZ r k).re
def pY (r : ℤ) (k : ℕ) : ℤ := (pellZ r k).im

lemma pX_zero (r : ℤ) : pX r 0 = r := by simp [pX, pellZ, alpha]
lemma pY_zero (r : ℤ) : pY r 0 = 1 := by simp [pY, pellZ, alpha]

lemma pellZ_succ (r : ℤ) (k : ℕ) :
    pellZ r (k + 1) = pellZ r k * eps r := by
  unfold pellZ
  rw [pow_succ (eps r) k, mul_assoc]

lemma pX_succ (r : ℤ) (k : ℕ) :
    pX r (k + 1) = (r ^ 2 + 1) * pX r k + (r ^ 2 + 2) * r * pY r k := by
  unfold pX pY
  rw [pellZ_succ]
  simp [eps]
  ring

lemma pY_succ (r : ℤ) (k : ℕ) :
    pY r (k + 1) = r * pX r k + (r ^ 2 + 1) * pY r k := by
  unfold pX pY
  rw [pellZ_succ]
  simp [eps]
  ring

lemma p_norm (r : ℤ) (k : ℕ) :
    pX r k ^ 2 - (r ^ 2 + 2) * pY r k ^ 2 = -2 := by
  have h : (pellZ r k).norm = -2 := by
    unfold pellZ
    rw [Zsqrtd.norm_mul, alpha_norm, eps_pow_norm, mul_one]
  unfold pX pY
  rw [Zsqrtd.norm_def] at h
  nlinarith

lemma pY_one (r : ℤ) : pY r 1 = 2 * r ^ 2 + 1 := by
  rw [pY_succ, pX_zero, pY_zero]; ring

lemma pX_one (r : ℤ) : pX r 1 = r * (2 * r ^ 2 + 3) := by
  rw [pX_succ, pX_zero, pY_zero]; ring

lemma pY_succ2 (r : ℤ) (k : ℕ) :
    pY r (k + 2) = 2 * (r ^ 2 + 1) * pY r (k + 1) - pY r k := by
  rw [pY_succ, pX_succ, pY_succ]
  ring

lemma p_pos (r : ℤ) (hr : 1 ≤ r) : ∀ k : ℕ, 0 < pX r k ∧ 0 < pY r k
  | 0 => by
    constructor
    · rw [pX_zero]; linarith
    · rw [pY_zero]; norm_num
  | k + 1 => by
    obtain ⟨hx, hy⟩ := p_pos r hr k
    have h1 : 0 < r ^ 2 + 1 := by nlinarith [sq_nonneg r]
    have h2 : 0 < r := by linarith
    have h3 : 0 < r ^ 2 + 2 := by nlinarith [sq_nonneg r]
    constructor
    · rw [pX_succ]
      have a : 0 < (r ^ 2 + 1) * pX r k := mul_pos h1 hx
      have b : 0 < (r ^ 2 + 2) * r * pY r k := mul_pos (mul_pos h3 h2) hy
      linarith
    · rw [pY_succ]
      have a : 0 < r * pX r k := mul_pos h2 hx
      have b : 0 < (r ^ 2 + 1) * pY r k := mul_pos h1 hy
      linarith

lemma pX_pos (r : ℤ) (hr : 1 ≤ r) (k : ℕ) : 0 < pX r k := (p_pos r hr k).1
lemma pY_pos (r : ℤ) (hr : 1 ≤ r) (k : ℕ) : 0 < pY r k := (p_pos r hr k).2

lemma pX_ge (r : ℤ) (hr : 1 ≤ r) (k : ℕ) : r * pY r k ≤ pX r k := by
  have hx := pX_pos r hr k
  have hy := pY_pos r hr k
  have hn := p_norm r k
  have hsq : (r * pY r k) ^ 2 ≤ (pX r k) ^ 2 := by
    nlinarith [sq_nonneg r, sq_nonneg (pY r k)]
  have habs : |r * pY r k| ≤ |pX r k| := by
    have : (r * pY r k) ^ 2 ≤ |pX r k| ^ 2 := by rwa [sq_abs]
    exact abs_le_of_sq_le_sq this (abs_nonneg _)
  have hr0 : 0 ≤ r := by linarith
  rw [abs_of_nonneg (mul_nonneg hr0 (le_of_lt hy)), abs_of_pos hx] at habs
  exact habs

lemma pY_grow (r : ℤ) (hr : 1 ≤ r) (k : ℕ) :
    (2 * r ^ 2 + 1) * pY r k ≤ pY r (k + 1) := by
  have hge := pX_ge r hr k
  rw [pY_succ]
  nlinarith [sq_nonneg r]

lemma pY_pow_lower (r : ℤ) (hr : 1 ≤ r) :
    ∀ k : ℕ, (2 * r ^ 2 + 1 : ℤ) ^ k ≤ pY r k
  | 0 => by simp [pY_zero]
  | k + 1 => by
    have ih := pY_pow_lower r hr k
    have hg := pY_grow r hr k
    have hp : (0 : ℤ) ≤ 2 * r ^ 2 + 1 := by nlinarith [sq_nonneg r]
    calc
      (2 * r ^ 2 + 1 : ℤ) ^ (k + 1)
          = (2 * r ^ 2 + 1) * (2 * r ^ 2 + 1) ^ k := pow_succ' _ _
      _ ≤ (2 * r ^ 2 + 1) * pY r k := mul_le_mul_of_nonneg_left ih hp
      _ ≤ pY r (k + 1) := hg

lemma pY_one_not_q_pow (r : ℤ) (hr : 2 ≤ |r|) {m : ℕ}
    (h : pY r 1 = (r ^ 2 + 2) ^ m) : False := by
  rw [pY_one] at h
  have hr2 : (4 : ℤ) ≤ r ^ 2 := by nlinarith [sq_abs r]
  match m with
  | 0 =>
    have : (2 * r ^ 2 + 1 : ℤ) = 1 := by simpa using h
    nlinarith
  | 1 =>
    have : (2 * r ^ 2 + 1 : ℤ) = r ^ 2 + 2 := by simpa using h
    nlinarith
  | m + 2 =>
    have hge : (r ^ 2 + 2 : ℤ) ^ 2 ≤ (r ^ 2 + 2) ^ (m + 2) :=
      pow_le_pow_right₀ (by nlinarith [sq_nonneg r] : (1 : ℤ) ≤ r ^ 2 + 2) (by omega)
    have hlt : (2 * r ^ 2 + 1 : ℤ) < (r ^ 2 + 2) ^ 2 := by
      have : (r ^ 2 + 2) ^ 2 = r ^ 4 + 4 * r ^ 2 + 4 := by ring
      nlinarith
    nlinarith

lemma two_sigma_mod (r : ℤ) :
    (2 * (r ^ 2 + 1) : ℤ) ≡ -2 [ZMOD r ^ 2 + 2] := by
  refine Int.modEq_iff_dvd.mpr ⟨-2, ?_⟩
  ring

lemma pY_mod_q (r : ℤ) : ∀ k : ℕ,
    pY r k ≡ (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) [ZMOD r ^ 2 + 2]
  | 0 => by simp [pY_zero]
  | 1 => by
    rw [pY_one]
    refine Int.modEq_iff_dvd.mpr ⟨-2, by ring⟩
  | k + 2 => by
    have h0 := pY_mod_q r k
    have h1 := pY_mod_q r (k + 1)
    have hrec := pY_succ2 r k
    have hσ := two_sigma_mod r
    have hstep : pY r (k + 2) ≡
        2 * (r ^ 2 + 1) * pY r (k + 1) - pY r k [ZMOD r ^ 2 + 2] := by
      rw [hrec]
    have hstep2 : pY r (k + 2) ≡
        -2 * pY r (k + 1) - pY r k [ZMOD r ^ 2 + 2] := by
      apply hstep.trans
      exact (hσ.mul_right (pY r (k + 1))).sub (Int.ModEq.refl (pY r k))
    have hstep3 : pY r (k + 2) ≡
        -2 * ((-1 : ℤ) ^ (k + 1) * (2 * ((k + 1 : ℕ) : ℤ) + 1))
          - ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1)) [ZMOD r ^ 2 + 2] := by
      apply hstep2.trans
      exact ((Int.ModEq.refl (-2 : ℤ)).mul h1).sub h0
    have hid : (-2 : ℤ) * ((-1 : ℤ) ^ (k + 1) * (2 * ((k + 1 : ℕ) : ℤ) + 1))
        - ((-1 : ℤ) ^ k * (2 * (k : ℤ) + 1))
        = (-1 : ℤ) ^ (k + 2) * (2 * ((k + 2 : ℕ) : ℤ) + 1) := by
      have hneg : (-1 : ℤ) ^ (k + 1) = - ((-1 : ℤ) ^ k) := by
        rw [pow_succ]; ring
      have hneg2 : (-1 : ℤ) ^ (k + 2) = (-1 : ℤ) ^ k := by
        rw [pow_add, pow_two]; ring
      rw [hneg, hneg2]
      push_cast
      ring
    rwa [hid] at hstep3

lemma q_dvd_two_k_add_one (r : ℤ) (k : ℕ)
    (hdvd : r ^ 2 + 2 ∣ pY r k) :
    r ^ 2 + 2 ∣ (2 * (k : ℤ) + 1) := by
  have hcong := pY_mod_q r k
  have h0 : pY r k ≡ 0 [ZMOD r ^ 2 + 2] := Int.modEq_zero_iff_dvd.mpr hdvd
  have hmul : (0 : ℤ) ≡ (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) [ZMOD r ^ 2 + 2] :=
    h0.symm.trans hcong
  have hd : r ^ 2 + 2 ∣ (-1 : ℤ) ^ k * (2 * (k : ℤ) + 1) :=
    Int.modEq_zero_iff_dvd.mp hmul.symm
  have hunit : IsUnit ((-1 : ℤ) ^ k) := IsUnit.pow _ isUnit_neg_one
  exact (hunit.dvd_mul_left).mp hd


/-- Multiplying by `ε̄ = ⟨r²+1, -r⟩` inverts a step. -/
def epsBar (r : ℤ) : ℤ√(r ^ 2 + 2) := ⟨r ^ 2 + 1, -r⟩

lemma eps_mul_epsBar (r : ℤ) : eps r * epsBar r = 1 := by
  ext <;> (simp [eps, epsBar]; ring)

lemma pellZ_mul_epsBar (r : ℤ) (k : ℕ) :
    pellZ r (k + 1) * epsBar r = pellZ r k := by
  rw [pellZ_succ, mul_assoc, eps_mul_epsBar, mul_one]

def descX (r X Y : ℤ) : ℤ := (r ^ 2 + 1) * X - (r ^ 2 + 2) * r * Y
def descY (r X Y : ℤ) : ℤ := (r ^ 2 + 1) * Y - r * X

lemma desc_norm (r X Y : ℤ)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    descX r X Y ^ 2 - (r ^ 2 + 2) * descY r X Y ^ 2 = -2 := by
  simp only [descX, descY]
  nlinarith

lemma descY_pos (r X Y : ℤ) (hr : 1 ≤ r) (hY : 1 < Y) (hX : 0 < X)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    0 < descY r X Y := by
  -- equivalent to r X < (r²+1) Y
  have hcmp : (r * X) ^ 2 < ((r ^ 2 + 1) * Y) ^ 2 := by
    have : (r ^ 2 + 2) * r ^ 2 < (r ^ 2 + 1) ^ 2 := by
      have hrpos : (0 : ℤ) < r := by linarith
      nlinarith [sq_pos_of_pos hrpos]
    nlinarith
  have habs : |r * X| < |(r ^ 2 + 1) * Y| := by
    refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
    rwa [sq_abs, sq_abs]
  have ha : |r * X| = r * X :=
    abs_of_nonneg (mul_nonneg (by linarith) (le_of_lt hX))
  have hb : |(r ^ 2 + 1) * Y| = (r ^ 2 + 1) * Y :=
    abs_of_nonneg (mul_nonneg (by nlinarith [sq_nonneg r]) (by linarith))
  simp only [descY]
  linarith

lemma descY_lt (r X Y : ℤ) (hr : 1 ≤ r) (hY : 1 < Y) (hX : 0 < X)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    descY r X Y < Y := by
  have hgt : r * Y < X := by
    have hsq : (r * Y) ^ 2 < X ^ 2 := by nlinarith
    have habs : |r * Y| < |X| := by
      refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
      rwa [sq_abs, sq_abs]
    have hr0 : 0 ≤ r := by linarith
    have hY0 : 0 ≤ Y := by linarith
    rwa [abs_of_nonneg (mul_nonneg hr0 hY0), abs_of_pos hX] at habs
  simp only [descY]
  nlinarith [sq_nonneg r]

lemma not_sq_seven {z : ℤ} (h : z ^ 2 = 7) : False := by
  have habs : |z| ≤ 3 := by
    have : z ^ 2 ≤ (3 : ℤ) ^ 2 := by norm_num [h]
    exact abs_le_of_sq_le_sq this (by decide)
  have hnn : 0 ≤ |z| := abs_nonneg _
  have : |z| = 0 ∨ |z| = 1 ∨ |z| = 2 ∨ |z| = 3 := by omega
  rcases this with h0 | h1 | h2 | h3
  · rw [abs_eq_zero] at h0; subst h0; norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h2 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h3 with rfl | rfl <;> norm_num at h

lemma not_sq_ten {z : ℤ} (h : z ^ 2 = 10) : False := by
  have habs : |z| ≤ 4 := by
    have : z ^ 2 ≤ (4 : ℤ) ^ 2 := by norm_num [h]
    exact abs_le_of_sq_le_sq this (by decide)
  have hnn : 0 ≤ |z| := abs_nonneg _
  have : |z| = 0 ∨ |z| = 1 ∨ |z| = 2 ∨ |z| = 3 ∨ |z| = 4 := by omega
  rcases this with h0 | h1 | h2 | h3 | h4
  · rw [abs_eq_zero] at h0; subst h0; norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h2 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h3 with rfl | rfl <;> norm_num at h
  · rcases eq_or_eq_neg_of_abs_eq h4 with rfl | rfl <;> norm_num at h

lemma descX_pos (r X Y : ℤ) (hr : 1 ≤ r) (hY : 1 < Y) (hX : 0 < X)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    0 < descX r X Y := by
  -- Split on whether Y ≥ 2r or Y < 2r
  by_cases hbig : (2 * r : ℤ) ≤ Y
  · -- (σ X)² - (r q Y)² = X² - 2 r² q > 0 when Y ≥ 2r
    have hdiff :
        (r ^ 2 + 1) ^ 2 * X ^ 2 - (r * (r ^ 2 + 2) * Y) ^ 2
          = X ^ 2 - 2 * r ^ 2 * (r ^ 2 + 2) := by
      have : X ^ 2 = (r ^ 2 + 2) * Y ^ 2 - 2 := by nlinarith
      rw [this]; ring
    have hposd : (0 : ℤ) < X ^ 2 - 2 * r ^ 2 * (r ^ 2 + 2) := by
      have : X ^ 2 = (r ^ 2 + 2) * Y ^ 2 - 2 := by nlinarith
      rw [this]
      have : (4 : ℤ) * r ^ 2 ≤ Y ^ 2 := by
        nlinarith [sq_nonneg (Y - 2 * r), hr]
      nlinarith [sq_nonneg r, hr]
    have : |(r * (r ^ 2 + 2) * Y)| < |(r ^ 2 + 1) * X| := by
      refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
      rw [sq_abs, sq_abs]
      nlinarith
    have ha : |r * (r ^ 2 + 2) * Y| = r * (r ^ 2 + 2) * Y :=
      abs_of_nonneg (by nlinarith [hr, hY, sq_nonneg r])
    have hb : |(r ^ 2 + 1) * X| = (r ^ 2 + 1) * X :=
      abs_of_nonneg (by nlinarith [hX, sq_nonneg r])
    simp only [descX]
    linarith
  · -- 1 < Y < 2r: then X = rY+1 and r²+6 is a square, impossible
    have hYlt : Y < 2 * r := by omega
    have hXgt : r * Y < X := by
      have hsq : (r * Y) ^ 2 < X ^ 2 := by nlinarith
      have habs : |r * Y| < |X| := by
        refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
        rwa [sq_abs, sq_abs]
      have hr0 : 0 ≤ r := by linarith
      have hY0 : 0 ≤ Y := by linarith
      rwa [abs_of_nonneg (mul_nonneg hr0 hY0), abs_of_pos hX] at habs
    have hXge : r * Y + 1 ≤ X := by omega
    have hXlt2 : X ≤ r * Y + 1 := by
      have : X ^ 2 < (r * Y + 2) ^ 2 := by
        have hx2 : X ^ 2 = r ^ 2 * Y ^ 2 + 2 * Y ^ 2 - 2 := by nlinarith
        have : (r * Y + 2) ^ 2 = r ^ 2 * Y ^ 2 + 4 * r * Y + 4 := by ring
        nlinarith [sq_nonneg (Y - r), hr]
      have : |X| < |r * Y + 2| :=
        lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) (by rwa [sq_abs, sq_abs])
      have : X < r * Y + 2 := by
        rwa [abs_of_pos hX, abs_of_pos (by nlinarith [hr, hY])] at this
      omega
    have hXeq : X = r * Y + 1 := by omega
    have heq : 2 * Y ^ 2 - 2 = 2 * r * Y + 1 := by
      have : X ^ 2 = r ^ 2 * Y ^ 2 + 2 * Y ^ 2 - 2 := by nlinarith
      have : (r * Y + 1) ^ 2 = r ^ 2 * Y ^ 2 + 2 * r * Y + 1 := by ring
      nlinarith
    have hdisc : (2 * Y - r) ^ 2 = r ^ 2 + 6 := by nlinarith
    -- r²+6 is strictly between r² and (r+1)² for r ≥ 3, and not square for r=1,2
    have hup : r ^ 2 + 6 < (r + 1) ^ 2 ∨ r = 1 ∨ r = 2 := by
      by_cases h1 : r = 1
      · exact Or.inr (Or.inl h1)
      · by_cases h2 : r = 2
        · exact Or.inr (Or.inr h2)
        · left
          have : (3 : ℤ) ≤ r := by omega
          nlinarith
    rcases hup with hup | rfl | rfl
    · have : r < |2 * Y - r| := by
        have : r ^ 2 < (2 * Y - r) ^ 2 := by nlinarith
        have habs : |r| < |2 * Y - r| := by
          refine lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) ?_
          rwa [sq_abs, sq_abs]
        rwa [abs_of_nonneg (by linarith : (0 : ℤ) ≤ r)] at habs
      have : |2 * Y - r| ≤ r := by
        have : (2 * Y - r) ^ 2 < (r + 1) ^ 2 := by nlinarith
        have habs : |2 * Y - r| < |r + 1| :=
          lt_of_pow_lt_pow_left₀ 2 (abs_nonneg _) (by rwa [sq_abs, sq_abs])
        have : |2 * Y - r| < r + 1 := by
          rwa [abs_of_pos (by linarith : (0 : ℤ) < r + 1)] at habs
        omega
      omega
    · -- r = 1: 1 < Y < 2, impossible
      omega
    · -- r = 2: 1 < Y < 4, so Y = 2 or 3
      have : Y = 2 ∨ Y = 3 := by omega
      rcases this with rfl | rfl
      · -- X^2 - 6*4 = -2 ⇒ X^2 = 22, not a square. Use X = 2*2+1 = 5 from hXeq
        have : X = 5 := by omega
        subst this
        norm_num at h
      · have : X = 7 := by omega
        subst this
        norm_num at h

lemma exists_pSol (r X Y : ℤ) (hr : 1 ≤ r) (hX : 0 < X) (hY : 0 < Y)
    (h : X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2) :
    ∃ k, X = pX r k ∧ Y = pY r k := by
  have helper : ∀ (N : ℕ) (X Y : ℤ), Y.natAbs = N → 0 < X → 0 < Y →
      X ^ 2 - (r ^ 2 + 2) * Y ^ 2 = -2 →
      ∃ k, X = pX r k ∧ Y = pY r k := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro X Y hYN hX hY h
      by_cases hY1 : Y = 1
      · subst hY1
        have : X ^ 2 = r ^ 2 := by nlinarith
        have hXr : X = r ∨ X = -r := (sq_eq_sq_iff_eq_or_eq_neg).mp (by nlinarith)
        rcases hXr with hXr | hXr
        · exact ⟨0, hXr.trans (pX_zero r).symm, (pY_zero r).symm⟩
        · rw [hXr] at hX
          exact (lt_irrefl _ (hX.trans_le (by linarith))).elim
      · have hYge : (2 : ℤ) ≤ Y := by omega
        set X1 := descX r X Y
        set Y1 := descY r X Y
        have hN1 := desc_norm r X Y h
        have hY1pos : 0 < Y1 := descY_pos r X Y hr (by omega) hX h
        have hX1pos : 0 < X1 := descX_pos r X Y hr (by omega) hX h
        have hY1lt : Y1 < Y := descY_lt r X Y hr (by omega) hX h
        have hY1abs : Y1.natAbs < N := by
          have e1 : (Y1.natAbs : ℤ) = Y1 := Int.natAbs_of_nonneg hY1pos.le
          have e2 : (Y.natAbs : ℤ) = Y := Int.natAbs_of_nonneg hY.le
          have : (Y1.natAbs : ℤ) < (N : ℤ) := by
            rw [e1, ← hYN, e2]; exact hY1lt
          exact_mod_cast this
        obtain ⟨k, hkX, hkY⟩ := ih Y1.natAbs hY1abs X1 Y1 rfl hX1pos hY1pos hN1
        refine ⟨k + 1, ?_, ?_⟩
        · -- successor inverts descent
          have hinvX : (r ^ 2 + 1) * descX r X Y + (r ^ 2 + 2) * r * descY r X Y = X := by
            simp only [descX, descY]; ring
          rw [pX_succ, ← hkX, ← hkY]
          simpa [X1, Y1] using hinvX.symm
        · have hinvY : r * descX r X Y + (r ^ 2 + 1) * descY r X Y = Y := by
            simp only [descX, descY]; ring
          rw [pY_succ, ← hkX, ← hkY]
          simpa [X1, Y1] using hinvY.symm
  exact helper Y.natAbs X Y rfl hX hY h


set_option linter.unusedVariables false

lemma two_eps_eq_alpha_sq (r : ℤ) :
    (2 : ℤ√(r ^ 2 + 2)) * eps r = alpha r * alpha r := by
  ext
  · simp [eps, alpha]; ring
  · simp [eps, alpha]; ring

lemma two_pow_eps_pow (r : ℤ) : ∀ k : ℕ,
    (2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k = (alpha r) ^ (2 * k)
  | 0 => by simp
  | k + 1 => by
    have ih := two_pow_eps_pow r k
    have h2 : (2 : ℤ√(r ^ 2 + 2)) ^ (k + 1) =
        (2 : ℤ√(r ^ 2 + 2)) ^ k * 2 :=
      pow_succ (2 : ℤ√(r ^ 2 + 2)) k
    have he : (eps r) ^ (k + 1) = (eps r) ^ k * eps r :=
      pow_succ (eps r) k
    rw [h2, he]
    calc
      (2 : ℤ√(r ^ 2 + 2)) ^ k * 2 * ((eps r) ^ k * eps r)
          = ((2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k) * (2 * eps r) := by ring
      _ = (alpha r) ^ (2 * k) * (alpha r * alpha r) := by
            rw [ih, two_eps_eq_alpha_sq]
      _ = (alpha r) ^ (2 * (k + 1)) := by
            have hsq : alpha r * alpha r = (alpha r) ^ 2 := (pow_two (alpha r)).symm
            rw [hsq, ← pow_add (alpha r) (2 * k) 2]
            rfl

lemma two_pow_pellZ (r : ℤ) (k : ℕ) :
    (2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k = (alpha r) ^ (2 * k + 1) := by
  unfold pellZ
  have h := two_pow_eps_pow r k
  calc
    (2 : ℤ√(r ^ 2 + 2)) ^ k * (alpha r * (eps r) ^ k)
        = alpha r * ((2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k) := by ring
    _ = alpha r * (alpha r) ^ (2 * k) := by rw [h]
    _ = (alpha r) ^ (2 * k + 1) := (pow_succ' (alpha r) (2 * k)).symm

lemma omega_pow_even (d : ℤ) : ∀ t : ℕ,
    ((⟨0, 1⟩ : ℤ√d) ^ (2 * t)) = ⟨d ^ t, 0⟩
  | 0 => by
    ext
    · simp
    · simp
  | t + 1 => by
    have ih := omega_pow_even d t
    have h2 : ((⟨0, 1⟩ : ℤ√d) ^ 2) = ⟨d, 0⟩ := by
      ext <;> simp [pow_two]
    have hmul : (⟨0, 1⟩ : ℤ√d) ^ (2 * (t + 1)) =
        (⟨0, 1⟩ : ℤ√d) ^ (2 * t) * (⟨0, 1⟩ : ℤ√d) ^ 2 := by
      rw [show 2 * (t + 1) = 2 * t + 2 by omega, pow_add (⟨0, 1⟩ : ℤ√d) (2 * t) 2]
    rw [hmul, ih, h2]
    ext <;> simp [pow_succ]

lemma omega_pow_odd (d : ℤ) (t : ℕ) :
    ((⟨0, 1⟩ : ℤ√d) ^ (2 * t + 1)) = ⟨0, d ^ t⟩ := by
  rw [pow_succ (⟨0, 1⟩ : ℤ√d) (2 * t), omega_pow_even]
  ext <;> simp

lemma alpha_eq_add (r : ℤ) :
    alpha r = (r : ℤ√(r ^ 2 + 2)) + ⟨0, 1⟩ := by
  ext <;> simp [alpha]

lemma intCast_pow (d a : ℤ) : ∀ n : ℕ,
    (a : ℤ√d) ^ n = ⟨a ^ n, 0⟩
  | 0 => by ext <;> simp
  | n + 1 => by
    rw [pow_succ (a : ℤ√d) n, intCast_pow d a n]
    ext <;> simp [pow_succ]

lemma im_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ m ∈ s, f m).im = ∑ m ∈ s, (f m).im := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Zsqrtd.im_add, ih]


/-- Term in the expansion of `Im((r+√q)^{2k+1})`, indexed by the power of `r`. -/
def binomTerm (r : ℤ) (k j : ℕ) : ℤ :=
  (Nat.choose (2 * k + 1) (2 * j) : ℤ) * r ^ (2 * j) * (r ^ 2 + 2) ^ (k - j)

lemma mul_intCast_omega_odd_im (r : ℤ) (m t : ℕ) :
    (((r : ℤ√(r ^ 2 + 2)) ^ m) * ((⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * t + 1))).im =
      r ^ m * (r ^ 2 + 2) ^ t := by
  rw [intCast_pow, omega_pow_odd, Zsqrtd.im_mul]
  simp

lemma mul_intCast_omega_even_im (r : ℤ) (m t : ℕ) :
    (((r : ℤ√(r ^ 2 + 2)) ^ m) * ((⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * t))).im = 0 := by
  rw [intCast_pow, omega_pow_even, Zsqrtd.im_mul]
  simp

lemma im_mul_intCast {d : ℤ} (z : ℤ√d) (n : ℤ) :
    (z * (n : ℤ√d)).im = z.im * n := by
  rw [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]
  ring

lemma odd_sub_even {n m : ℕ} (hn : Odd n) (hm : Even m) (hle : m ≤ n) : Odd (n - m) := by
  rw [← Nat.not_even_iff_odd, Nat.even_sub hle]
  intro hiff
  have : Even n := hiff.mpr hm
  exact Nat.not_odd_iff_even.mpr this hn

lemma even_odd_sub_odd {n m : ℕ} (hn : Odd n) (hm : Odd m) (hle : m ≤ n) : Even (n - m) := by
  rw [Nat.even_sub hle]
  exact iff_of_false (Nat.not_even_iff_odd.mpr hn) (Nat.not_even_iff_odd.mpr hm)

lemma even_iff_two_mul {n : ℕ} : Even n ↔ ∃ j, n = 2 * j := by
  constructor
  · intro ⟨j, hj⟩
    exact ⟨j, by rw [two_mul]; exact hj⟩
  · rintro ⟨j, rfl⟩
    exact even_two_mul j

lemma alpha_pow_im_as_sum_aux (r : ℤ) (k : ℕ) :
    ((alpha r) ^ (2 * k + 1)).im =
      ∑ m ∈ Finset.range (2 * k + 2),
        (if Even m then
          (Nat.choose (2 * k + 1) m : ℤ) * r ^ m * (r ^ 2 + 2) ^ ((2 * k + 1 - m) / 2)
        else 0) := by
  rw [alpha_eq_add, add_pow, im_sum]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hmle : m ≤ 2 * k + 1 := by
    simp [Finset.mem_range] at hm; omega
  have hC :
      (((r : ℤ√(r ^ 2 + 2)) ^ m *
        (⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * k + 1 - m) *
        ((2 * k + 1).choose m : ℤ√(r ^ 2 + 2)))).im =
      (((r : ℤ√(r ^ 2 + 2)) ^ m *
        (⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * k + 1 - m))).im *
        ((2 * k + 1).choose m : ℤ) :=
    im_mul_intCast _ _
  rw [hC]
  by_cases he : Even m
  · have hodd : Odd (2 * k + 1 - m) :=
      odd_sub_even ⟨k, by ring⟩ he hmle
    obtain ⟨t, ht⟩ := hodd
    have ht' : 2 * k + 1 - m = 2 * t + 1 := by omega
    rw [if_pos he, ht', mul_intCast_omega_odd_im]
    have : (2 * t + 1) / 2 = t := by omega
    rw [this]
    ring
  · have hev : Even (2 * k + 1 - m) :=
      even_odd_sub_odd ⟨k, by ring⟩ (Nat.not_even_iff_odd.mp he) hmle
    obtain ⟨t, ht⟩ := even_iff_two_mul.mp hev
    rw [if_neg he, ht, mul_intCast_omega_even_im, zero_mul]

lemma even_filter_range (k : ℕ) :
    (Finset.range (2 * k + 2)).filter Even =
      (Finset.range (k + 1)).image (fun j => 2 * j) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · intro ⟨hm, he⟩
    obtain ⟨j, hj⟩ := even_iff_two_mul.mp he
    exact ⟨j, by omega, hj.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨by omega, even_two_mul j⟩

lemma alpha_pow_im_odd (r : ℤ) (k : ℕ) :
    ((alpha r) ^ (2 * k + 1)).im =
      ∑ j ∈ Finset.range (k + 1), binomTerm r k j := by
  rw [alpha_pow_im_as_sum_aux]
  rw [← Finset.sum_filter_add_sum_filter_not (p := Even)]
  have hodd :
      ∑ m ∈ (Finset.range (2 * k + 2)).filter (fun m => ¬ Even m),
          (if Even m then
            (Nat.choose (2 * k + 1) m : ℤ) * r ^ m * (r ^ 2 + 2) ^ ((2 * k + 1 - m) / 2)
          else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro m hm
    have : ¬ Even m := (Finset.mem_filter.mp hm).2
    simp [this]
  have hinj : Set.InjOn (fun j : ℕ => 2 * j) (Finset.range (k + 1) : Set ℕ) := by
    intro x _hx y _hy hxy
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hxy
  rw [hodd, add_zero, even_filter_range, Finset.sum_image hinj]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have he : Even (2 * j) := even_two_mul j
  simp only [if_pos he]
  have hdiv : (2 * k + 1 - 2 * j) / 2 = k - j := by
    have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    omega
  simp [binomTerm, hdiv]

lemma two_pow_pY_eq_sum (r : ℤ) (k : ℕ) :
    (2 : ℤ) ^ k * pY r k = ∑ j ∈ Finset.range (k + 1), binomTerm r k j := by
  have h := two_pow_pellZ r k
  have him : ((2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k).im = ((alpha r) ^ (2 * k + 1)).im := by
    rw [h]
  have h2 : ((2 : ℤ√(r ^ 2 + 2)) ^ k) = ⟨(2 : ℤ) ^ k, 0⟩ := by
    simpa using intCast_pow (r ^ 2 + 2) 2 k
  have him2 : ((2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k).im = (2 : ℤ) ^ k * pY r k := by
    rw [h2, Zsqrtd.im_mul]
    simp [pY]
  rw [← him2, him, alpha_pow_im_odd]


/-! `q`-adic valuation of the binomial terms. -/

lemma choose_mul_succ_identity (k t : ℕ) (ht : t ≤ k) :
    (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) =
      (2 * k + 1 : ℤ) * Nat.choose (2 * k) (2 * t) := by
  have h1 : 2 * t + 1 ≤ 2 * k + 1 := by omega
  have hA := Nat.choose_mul_factorial_mul_factorial h1
  have h2 : 2 * t ≤ 2 * k := by omega
  have hB := Nat.choose_mul_factorial_mul_factorial h2
  have hfact : (2 * t + 1).factorial = (2 * t + 1) * (2 * t).factorial :=
    Nat.factorial_succ (2 * t)
  have hfact2 : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial :=
    Nat.factorial_succ (2 * k)
  have hsub : (2 * k + 1 - (2 * t + 1)) = 2 * k - 2 * t := by omega
  rw [hsub] at hA
  zify at hA hB hfact hfact2
  have hpos : ((2 * t).factorial : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (2 * t))
  have hpos2 : ((2 * k - 2 * t).factorial : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero _)
  have hA' :
      (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) * (2 * t).factorial *
        (2 * k - 2 * t).factorial =
      (2 * k + 1 : ℤ) * (2 * k).factorial := by
    calc
      (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) * (2 * t).factorial *
          (2 * k - 2 * t).factorial
        = (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * ((2 * t + 1).factorial) *
            (2 * k - 2 * t).factorial := by
              rw [hfact]; ring
      _ = (2 * k + 1).factorial := by
            simpa [mul_assoc] using hA
      _ = (2 * k + 1 : ℤ) * (2 * k).factorial := hfact2
  have hB' :
      (Nat.choose (2 * k) (2 * t) : ℤ) * (2 * t).factorial * (2 * k - 2 * t).factorial =
        (2 * k).factorial := hB
  have hnz : ((2 * t).factorial : ℤ) * (2 * k - 2 * t).factorial ≠ 0 :=
    mul_ne_zero hpos hpos2
  apply mul_right_cancel₀ hnz
  calc
    (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) *
        ((2 * t).factorial * (2 * k - 2 * t).factorial)
      = (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * (2 * t + 1) * (2 * t).factorial *
          (2 * k - 2 * t).factorial := by ring
    _ = (2 * k + 1 : ℤ) * (2 * k).factorial := hA'
    _ = (2 * k + 1 : ℤ) * ((Nat.choose (2 * k) (2 * t) : ℤ) * (2 * t).factorial *
          (2 * k - 2 * t).factorial) := by rw [hB']
    _ = (2 * k + 1 : ℤ) * Nat.choose (2 * k) (2 * t) *
          ((2 * t).factorial * (2 * k - 2 * t).factorial) := by ring

lemma q_pow_gt_two_j_add_one {q j : ℕ} (hq : 5 ≤ q) (hj : 1 ≤ j) :
    2 * j + 1 < q ^ j := by
  match j with
  | 0 => omega
  | 1 =>
    have : 3 < q := by omega
    simpa using this
  | j + 2 =>
    have hge : (5 : ℕ) ^ (j + 2) ≤ q ^ (j + 2) :=
      Nat.pow_le_pow_left hq (j + 2)
    have h5 : ∀ n : ℕ, 2 * (n + 2) + 1 < 5 ^ (n + 2) := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
        have hA : 2 * (n + 1 + 2) + 1 = 2 * (n + 2) + 1 + 2 := by omega
        have hB : 5 ^ (n + 1 + 2) = 5 * 5 ^ (n + 2) := pow_succ' 5 (n + 2)
        have hC : 2 * (n + 2) + 1 + 2 < 5 ^ (n + 2) + 2 := by omega
        have hD : 5 ^ (n + 2) + 2 ≤ 5 ^ (n + 2) + 5 ^ (n + 2) := by
          have : (2 : ℕ) ≤ 5 ^ (n + 2) := by
            have : 1 ≤ 5 ^ (n + 2) := Nat.one_le_pow _ _ (by decide)
            have : 5 ^ (n + 2) ≥ 5 := Nat.le_trans (by decide : 5 ≤ 25)
              (Nat.pow_le_pow_right (by decide : 1 ≤ 5) (by omega : 2 ≤ n + 2))
            omega
          omega
        have hE : 5 ^ (n + 2) + 5 ^ (n + 2) = 2 * 5 ^ (n + 2) := by ring
        have hF : 2 * 5 ^ (n + 2) ≤ 5 * 5 ^ (n + 2) :=
          Nat.mul_le_mul_right _ (by decide : 2 ≤ 5)
        omega
    have := h5 j
    omega

lemma not_pow_dvd_two_j_add_one {q j : ℕ} (hq : 5 ≤ q) (hj : 1 ≤ j) :
    ¬ (q : ℤ) ^ j ∣ (2 * (j : ℤ) + 1) := by
  intro h
  have hpos : (0 : ℤ) < 2 * (j : ℤ) + 1 := by
    have : (0 : ℤ) ≤ (j : ℤ) := Nat.cast_nonneg _
    linarith
  have hle : (q : ℤ) ^ j ≤ 2 * (j : ℤ) + 1 := Int.le_of_dvd hpos h
  have hlt : 2 * j + 1 < q ^ j := q_pow_gt_two_j_add_one hq hj
  have hlt' : (2 * (j : ℤ) + 1) < (q : ℤ) ^ j := by exact_mod_cast hlt
  linarith


lemma binomTerm_last (r : ℤ) (k : ℕ) :
    binomTerm r k k = (2 * k + 1 : ℤ) * r ^ (2 * k) := by
  unfold binomTerm
  have : (2 * k + 1).choose (2 * k) = 2 * k + 1 := by
    simpa [Nat.choose_symm (by omega : 2 * k ≤ 2 * k + 1)] using
      (Nat.choose_succ_self_right (2 * k))
  simp [this]

lemma binomTerm_ne_zero (r : ℤ) (hr : r ≠ 0) (k j : ℕ) (hj : j ≤ k) :
    binomTerm r k j ≠ 0 := by
  unfold binomTerm
  have hch : (Nat.choose (2 * k + 1) (2 * j) : ℤ) ≠ 0 := by
    have : 2 * j ≤ 2 * k + 1 := by omega
    exact_mod_cast (Nat.choose_pos this).ne'
  have hr0 : r ^ (2 * j) ≠ 0 := pow_ne_zero _ hr
  have hq : (r ^ 2 + 2 : ℤ) ^ (k - j) ≠ 0 := by
    have : (r ^ 2 + 2 : ℤ) ≠ 0 := by nlinarith [sq_nonneg r]
    exact pow_ne_zero _ this
  exact mul_ne_zero (mul_ne_zero hch hr0) hq

lemma padicValInt_pow_of_prime {q : ℕ} [Fact q.Prime] (n : ℕ) :
    padicValInt q ((q : ℤ) ^ n) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicValInt.mul (by
      exact_mod_cast (pow_ne_zero n (NeZero.ne q))) (by
      exact_mod_cast (Nat.Prime.ne_zero Fact.out)), ih, padicValInt_self]

lemma r_not_dvd_of_q_odd {r : ℤ} {q : ℕ} (hq : (q : ℤ) = r ^ 2 + 2)
    (hqp : Nat.Prime q) (hodd : Odd q) : ¬ (q : ℤ) ∣ r := by
  intro h
  have hq2 : (q : ℤ) ∣ r ^ 2 + 2 := by rw [hq]
  have hr2 : (q : ℤ) ∣ r ^ 2 := dvd_pow h (by decide)
  have : (q : ℤ) ∣ 2 := (dvd_add_right hr2).mp hq2
  have : (q : ℕ) ∣ 2 := by exact_mod_cast this
  have h12 : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp this
  rcases h12 with h1 | h2
  · exact hqp.ne_one h1
  · rw [h2] at hodd
    exact Nat.not_odd_iff_even.mpr (by decide) hodd

lemma padicVal_r_pow {r : ℤ} {q n : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q) :
    padicValInt q (r ^ n) = 0 := by
  have hnd : ¬ (q : ℤ) ∣ r := r_not_dvd_of_q_odd hq Fact.out hodd
  have : padicValInt q r = 0 := padicValInt.eq_zero_of_not_dvd hnd
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, padicValInt.mul (pow_ne_zero n hr) hr, ih, this]

lemma padicVal_binomTerm_last {r : ℤ} {q k : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q) :
    padicValInt q (binomTerm r k k) = padicValInt q (2 * (k : ℤ) + 1) := by
  rw [binomTerm_last]
  have h1 : (2 * (k : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have h2 : r ^ (2 * k) ≠ 0 := pow_ne_zero _ hr
  rw [padicValInt.mul h1 h2, padicVal_r_pow (n := 2 * k) hq hr hodd, add_zero]

lemma padic_two_j_lt {q j : ℕ} [Fact q.Prime] (hq : 5 ≤ q) (hj : 1 ≤ j) :
    padicValInt q (2 * (j : ℤ) + 1) < j := by
  by_contra h
  have : j ≤ padicValInt q (2 * (j : ℤ) + 1) := Nat.le_of_not_gt h
  have hdvd : (q : ℤ) ^ j ∣ (2 * (j : ℤ) + 1) := by
    have hne : (2 * (j : ℤ) + 1) ≠ 0 := by
      have : (0 : ℤ) ≤ (j : ℤ) := Nat.cast_nonneg _
      linarith
    rw [padicValInt_dvd_iff]
    exact Or.inr this
  exact not_pow_dvd_two_j_add_one hq hj hdvd

lemma padicVal_binomTerm_lt {r : ℤ} {q k j : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q)
    (hq5 : 5 ≤ q) (hj : j < k) :
    padicValInt q (2 * (k : ℤ) + 1) < padicValInt q (binomTerm r k j) := by
  have hjk : j ≤ k := Nat.le_of_lt hj
  set s := k - j
  have hs1 : 1 ≤ s := by omega
  have hch : (2 * k + 1).choose (2 * j) = (2 * k + 1).choose (2 * s + 1) := by
    have : 2 * j + (2 * s + 1) = 2 * k + 1 := by omega
    exact Nat.choose_symm_of_eq_add this.symm
  have hid := choose_mul_succ_identity k s (by omega)
  have hCne : (Nat.choose (2 * k + 1) (2 * s + 1) : ℤ) ≠ 0 := by
    have : 2 * s + 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast (Nat.choose_pos this).ne'
  have h2s : (2 * (s : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (s : ℤ) := Nat.cast_nonneg _
    linarith
  have h2k : (2 * (k : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have hC2 : (Nat.choose (2 * k) (2 * s) : ℤ) ≠ 0 := by
    have : 2 * s ≤ 2 * k := by omega
    exact_mod_cast (Nat.choose_pos this).ne'
  have hvsum :
      padicValInt q ((Nat.choose (2 * k + 1) (2 * s + 1) : ℤ)) +
        padicValInt q (2 * (s : ℤ) + 1) =
      padicValInt q (2 * (k : ℤ) + 1) +
        padicValInt q (Nat.choose (2 * k) (2 * s) : ℤ) := by
    have := congrArg (padicValInt q) hid
    rw [padicValInt.mul hCne h2s, padicValInt.mul h2k hC2] at this
    exact this
  have hr0 : padicValInt q (r ^ (2 * j)) = 0 :=
    padicVal_r_pow (n := 2 * j) hq hr hodd
  have hqeq : (r ^ 2 + 2 : ℤ) = q := hq.symm
  have hqs : padicValInt q ((r ^ 2 + 2 : ℤ) ^ s) = s := by
    rw [hqeq]
    exact padicValInt_pow_of_prime s
  have hterm : binomTerm r k j =
      (Nat.choose (2 * k + 1) (2 * s + 1) : ℤ) * r ^ (2 * j) * (r ^ 2 + 2) ^ s := by
    unfold binomTerm
    rw [hch]
  have htnz : binomTerm r k j ≠ 0 := binomTerm_ne_zero r hr k j hjk
  have hC1nz := hCne
  have hrnz : r ^ (2 * j) ≠ 0 := pow_ne_zero _ hr
  have hqsnz : (r ^ 2 + 2 : ℤ) ^ s ≠ 0 := by
    have : (r ^ 2 + 2 : ℤ) ≠ 0 := by nlinarith [sq_nonneg r]
    exact pow_ne_zero _ this
  have hvterm :
      padicValInt q (binomTerm r k j) =
        padicValInt q (Nat.choose (2 * k + 1) (2 * s + 1) : ℤ) + s := by
    rw [hterm, padicValInt.mul (mul_ne_zero hC1nz hrnz) hqsnz,
        padicValInt.mul hC1nz hrnz, hr0, hqs]
    omega
  have hvs : padicValInt q (2 * (s : ℤ) + 1) < s :=
    padic_two_j_lt hq5 hs1
  have hcast : (2 * s + 1 : ℤ) = 2 * (s : ℤ) + 1 := by push_cast; rfl
  have hcastk : (2 * k + 1 : ℤ) = 2 * (k : ℤ) + 1 := by push_cast; rfl
  have : padicValInt q (2 * (k : ℤ) + 1) + padicValInt q (2 * (s : ℤ) + 1) <
      padicValInt q (binomTerm r k j) + padicValInt q (2 * (s : ℤ) + 1) := by
    -- v(2k+1) + v(2s+1) = v(C1) + v(2s+1) - v(C2) + v(2s+1) wait
    -- From hvsum: v(C1) + v(2s+1) = v(2k+1) + v(C2)
    -- v(term) = v(C1) + s
    -- so v(term) - v(2k+1) = v(C1) + s - v(2k+1) = s - v(2s+1) + v(C2) ≥ s - v(2s+1) ≥ 1
    have : padicValInt q (binomTerm r k j) =
        padicValInt q (2 * (k : ℤ) + 1) +
          padicValInt q (Nat.choose (2 * k) (2 * s) : ℤ) + s -
          padicValInt q (2 * (s : ℤ) + 1) := by
      have h1 := hvsum
      rw [hcast, hcastk] at h1
      have := hvterm
      omega
    omega
  omega



lemma padicValInt_sum_of_unique_min {q : ℕ} [Fact q.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℤ) (i0 : ι) (hi0 : i0 ∈ s)
    (hne : ∀ i ∈ s, f i ≠ 0)
    (hmin : ∀ i ∈ s, i ≠ i0 → padicValInt q (f i0) < padicValInt q (f i)) :
    padicValInt q (∑ i ∈ s, f i) = padicValInt q (f i0) := by
  classical
  let v0 := padicValInt q (f i0)
  have hdiv0 : (q : ℤ) ^ v0 ∣ f i0 := padicValInt_dvd _
  have hdivs : ∀ i ∈ s, (q : ℤ) ^ v0 ∣ f i := by
    intro i hi
    by_cases h : i = i0
    · subst h; exact hdiv0
    · have : v0 < padicValInt q (f i) := hmin i hi h
      have : v0 ≤ padicValInt q (f i) := Nat.le_of_lt this
      have hf0 : f i ≠ 0 := hne i hi
      rw [padicValInt_dvd_iff]
      exact Or.inr this
  have hsumdiv : (q : ℤ) ^ v0 ∣ ∑ i ∈ s, f i :=
    Finset.dvd_sum hdivs
  have hsum_ne : ∑ i ∈ s, f i ≠ 0 := by
    -- if the sum were 0, then q^{v0+1} would divide the sum (namely 0),
    -- hence divide f i0 after subtracting the rest, contradiction.
    intro hz
    have hrest : (q : ℤ) ^ (v0 + 1) ∣ ∑ i ∈ s.erase i0, f i := by
      refine Finset.dvd_sum ?_
      intro i hi
      have hi' : i ∈ s := Finset.mem_of_mem_erase hi
      have hine : i ≠ i0 := Finset.ne_of_mem_erase hi
      have : v0 < padicValInt q (f i) := hmin i hi' hine
      have : v0 + 1 ≤ padicValInt q (f i) := Nat.succ_le_of_lt this
      rw [padicValInt_dvd_iff]
      exact Or.inr this
    have : (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hsplit : ∑ i ∈ s, f i = f i0 + ∑ i ∈ s.erase i0, f i :=
        (Finset.sum_erase_add s f hi0).symm.trans (add_comm _ _)
      -- 0 = f i0 + rest ⇒ f i0 = -rest
      have : f i0 = -∑ i ∈ s.erase i0, f i := by
        rw [hz] at hsplit
        linarith
      rw [this]
      exact dvd_neg.mpr hrest
    have : ¬ (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hf0 : f i0 ≠ 0 := hne i0 hi0
      rw [padicValInt_dvd_iff]
      simp [hf0, v0]
    exact this ‹(q : ℤ) ^ (v0 + 1) ∣ f i0›
  have hvle : v0 ≤ padicValInt q (∑ i ∈ s, f i) := by
    rw [padicValInt_dvd_iff] at hsumdiv
    exact hsumdiv.resolve_left hsum_ne
  have hvge : padicValInt q (∑ i ∈ s, f i) ≤ v0 := by
    by_contra h
    have : v0 + 1 ≤ padicValInt q (∑ i ∈ s, f i) := by omega
    have hsum' : (q : ℤ) ^ (v0 + 1) ∣ ∑ i ∈ s, f i := by
      rw [padicValInt_dvd_iff]
      exact Or.inr this
    have hrest : (q : ℤ) ^ (v0 + 1) ∣ ∑ i ∈ s.erase i0, f i := by
      refine Finset.dvd_sum ?_
      intro i hi
      have hi' : i ∈ s := Finset.mem_of_mem_erase hi
      have hine : i ≠ i0 := Finset.ne_of_mem_erase hi
      have : v0 + 1 ≤ padicValInt q (f i) := Nat.succ_le_of_lt (hmin i hi' hine)
      rw [padicValInt_dvd_iff]
      exact Or.inr this
    have : (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hsplit : ∑ i ∈ s, f i = f i0 + ∑ i ∈ s.erase i0, f i :=
        (Finset.sum_erase_add s f hi0).symm.trans (add_comm _ _)
      have : f i0 = ∑ i ∈ s, f i - ∑ i ∈ s.erase i0, f i := by
        linarith
      rw [this]
      exact dvd_sub hsum' hrest
    have : ¬ (q : ℤ) ^ (v0 + 1) ∣ f i0 := by
      have hf0 : f i0 ≠ 0 := hne i0 hi0
      rw [padicValInt_dvd_iff]
      simp [hf0, v0]
    exact this ‹(q : ℤ) ^ (v0 + 1) ∣ f i0›
  omega

lemma pY_ne_zero (r : ℤ) (k : ℕ) : pY r k ≠ 0 := by
  intro h
  have hn := p_norm r k
  rw [h] at hn
  simp at hn
  nlinarith [sq_nonneg (pX r k)]

lemma padicValInt_two_pow_eq_zero {q k : ℕ} [Fact q.Prime] (hodd : Odd q) :
    padicValInt q ((2 : ℤ) ^ k) = 0 := by
  have hv2 : padicValInt q (2 : ℤ) = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro h
    have : (q : ℕ) ∣ 2 := by exact_mod_cast h
    have : q = 1 ∨ q = 2 := (Nat.dvd_prime Nat.prime_two).mp this
    rcases this with h1 | h2
    · exact (Fact.out : Nat.Prime q).ne_one h1
    · rw [h2] at hodd; exact Nat.not_odd_iff_even.mpr (by decide) hodd
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, padicValInt.mul (pow_ne_zero k (by decide)) (by decide), ih, hv2]

lemma padicVal_pY {r : ℤ} {q k : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : r ≠ 0) (hodd : Odd q)
    (hq5 : 5 ≤ q) :
    padicValInt q (pY r k) = padicValInt q (2 * (k : ℤ) + 1) := by
  have hsum := two_pow_pY_eq_sum r k
  have h2ne : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by decide)
  have hYne : pY r k ≠ 0 := pY_ne_zero r k
  have hv2k : padicValInt q ((2 : ℤ) ^ k) = 0 := padicValInt_two_pow_eq_zero hodd
  have hmem : k ∈ Finset.range (k + 1) := by simp
  have hne : ∀ j ∈ Finset.range (k + 1), binomTerm r k j ≠ 0 := by
    intro j hj
    have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    exact binomTerm_ne_zero r hr k j this
  have hmin : ∀ j ∈ Finset.range (k + 1), j ≠ k →
      padicValInt q (binomTerm r k k) < padicValInt q (binomTerm r k j) := by
    intro j hj hjne
    have hjlt : j < k := by
      have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    have hlt := padicVal_binomTerm_lt hq hr hodd hq5 hjlt
    rwa [← padicVal_binomTerm_last hq hr hodd] at hlt
  have hvsum : padicValInt q (∑ j ∈ Finset.range (k + 1), binomTerm r k j) =
      padicValInt q (binomTerm r k k) :=
    padicValInt_sum_of_unique_min (Finset.range (k + 1)) (binomTerm r k) k hmem hne hmin
  have : padicValInt q ((2 : ℤ) ^ k * pY r k) = padicValInt q (2 * (k : ℤ) + 1) := by
    rw [hsum, hvsum, padicVal_binomTerm_last hq hr hodd]
  rw [padicValInt.mul h2ne hYne, hv2k, zero_add] at this
  exact this

lemma nine_pow_gt_two_mul_add_one : ∀ n : ℕ, 1 ≤ n → (9 : ℤ) ^ n > 2 * (n : ℤ) + 1
  | 1, _ => by norm_num
  | n + 2, _ => by
    have ih : (9 : ℤ) ^ (n + 1) > 2 * ((n + 1 : ℕ) : ℤ) + 1 :=
      nine_pow_gt_two_mul_add_one (n + 1) (by omega)
    have hge : (9 : ℤ) ^ (n + 2) = 9 * (9 : ℤ) ^ (n + 1) := pow_succ' _ _
    have : (9 : ℤ) * (9 : ℤ) ^ (n + 1) > 9 * (2 * ((n + 1 : ℕ) : ℤ) + 1) := by
      nlinarith
    have : 9 * (2 * ((n + 1 : ℕ) : ℤ) + 1) ≥ 2 * ((n + 2 : ℕ) : ℤ) + 1 := by
      push_cast
      nlinarith
    nlinarith

lemma pY_not_pow_of_q {r : ℤ} {q l k : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : 2 ≤ r) (hodd : Odd q) (hq5 : 5 ≤ q)
    (hl : 1 ≤ l) (h : pY r k = (q : ℤ) ^ l) : False := by
  have hv := padicVal_pY (r := r) (q := q) (k := k) hq (by linarith : r ≠ 0) hodd hq5
  have hql : padicValInt q ((q : ℤ) ^ l) = l := padicValInt_pow_of_prime l
  rw [h, hql] at hv
  have hne : (2 * (k : ℤ) + 1) ≠ 0 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have hdvd : (q : ℤ) ^ l ∣ (2 * (k : ℤ) + 1) := by
    have : l ≤ padicValInt q (2 * (k : ℤ) + 1) := by omega
    rw [padicValInt_dvd_iff]
    exact Or.inr this
  have hpos : (0 : ℤ) < 2 * (k : ℤ) + 1 := by
    have : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg _
    linarith
  have hle : (q : ℤ) ^ l ≤ 2 * (k : ℤ) + 1 := Int.le_of_dvd hpos hdvd
  have hlower := pY_pow_lower r (by linarith : 1 ≤ r) k
  have : (2 * r ^ 2 + 1 : ℤ) ^ k ≤ 2 * (k : ℤ) + 1 := by
    calc
      (2 * r ^ 2 + 1 : ℤ) ^ k ≤ pY r k := hlower
      _ = (q : ℤ) ^ l := h
      _ ≤ 2 * (k : ℤ) + 1 := hle
  have hbase : (9 : ℤ) ≤ 2 * r ^ 2 + 1 := by nlinarith [hr]
  have h9 : (9 : ℤ) ^ k ≤ 2 * (k : ℤ) + 1 :=
    le_trans (pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 9) hbase k) this
  match k with
  | 0 =>
    have hY0 : pY r 0 = 1 := pY_zero r
    rw [hY0] at h
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (Nat.one_le_of_lt (lt_of_lt_of_le (by decide : 1 < 5) hq5))
    have : (q : ℤ) ^ 1 ≤ (q : ℤ) ^ l := pow_le_pow_right₀ hq1 hl
    simp at this
    have : (q : ℤ) ≤ 1 := by
      have : (q : ℤ) ^ l = 1 := h.symm
      nlinarith
    have : (5 : ℤ) ≤ q := by exact_mod_cast hq5
    linarith
  | k + 1 =>
    have : (9 : ℤ) ^ (k + 1) > 2 * ((k + 1 : ℕ) : ℤ) + 1 :=
      nine_pow_gt_two_mul_add_one (k + 1) (by omega)
    linarith

lemma no_q_pow_pell {r X : ℤ} {q n : ℕ} [Fact q.Prime]
    (hq : (q : ℤ) = r ^ 2 + 2) (hr : 2 ≤ r) (hodd : Odd q) (hq5 : 5 ≤ q)
    (hn : Odd n) (hn3 : 3 ≤ n) (hX : 0 < X)
    (h : X ^ 2 + 2 = (q : ℤ) ^ n) : False := by
  obtain ⟨k, hk⟩ := hn
  have hn' : n = 2 * k + 1 := by omega
  have hk1 : 1 ≤ k := by omega
  have hpell : X ^ 2 - (r ^ 2 + 2) * ((q : ℤ) ^ k) ^ 2 = -2 := by
    have hpow : (r ^ 2 + 2) * ((q : ℤ) ^ k) ^ 2 = (q : ℤ) ^ n := by
      rw [hq, hn']
      calc
        (r ^ 2 + 2) * ((r ^ 2 + 2) ^ k) ^ 2
            = (r ^ 2 + 2) * (r ^ 2 + 2) ^ (k * 2) := by rw [← pow_mul]
        _ = (r ^ 2 + 2) * (r ^ 2 + 2) ^ (2 * k) := by rw [mul_comm k]
        _ = (r ^ 2 + 2) ^ (2 * k + 1) := (pow_succ' _ _).symm
    omega
  have hYpos : (0 : ℤ) < (q : ℤ) ^ k :=
    pow_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 5) hq5)) k
  obtain ⟨m, _, hmY⟩ := exists_pSol r X ((q : ℤ) ^ k) (by linarith) hX hYpos hpell
  exact pY_not_pow_of_q hq hr hodd hq5 hk1 hmY.symm
