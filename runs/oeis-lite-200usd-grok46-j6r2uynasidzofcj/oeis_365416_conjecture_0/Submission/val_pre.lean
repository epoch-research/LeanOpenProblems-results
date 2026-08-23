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
        (2 : ℤ√(r ^ 2 + 2)) ^ k * 2 := by
      rw [pow_succ (2 : ℤ√(r ^ 2 + 2)) k]
    have he : (eps r) ^ (k + 1) = (eps r) ^ k * eps r := by
      rw [pow_succ (eps r) k]
    rw [h2, he]
    calc
      (2 : ℤ√(r ^ 2 + 2)) ^ k * 2 * ((eps r) ^ k * eps r)
          = ((2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k) * (2 * eps r) := by ring
      _ = (alpha r) ^ (2 * k) * (alpha r * alpha r) := by
            rw [ih, two_eps_eq_alpha_sq]
      _ = (alpha r) ^ (2 * k + 2) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
            ring

lemma two_pow_pellZ (r : ℤ) (k : ℕ) :
    (2 : ℤ√(r ^ 2 + 2)) ^ k * pellZ r k = (alpha r) ^ (2 * k + 1) := by
  unfold pellZ
  have := two_pow_eps_pow r k
  calc
    (2 : ℤ√(r ^ 2 + 2)) ^ k * (alpha r * (eps r) ^ k)
        = alpha r * ((2 : ℤ√(r ^ 2 + 2)) ^ k * (eps r) ^ k) := by ring
    _ = alpha r * (alpha r) ^ (2 * k) := by rw [this]
    _ = (alpha r) ^ (2 * k + 1) := by rw [pow_succ, mul_comm]


/-! Binomial expansion of `alpha r ^ (2k+1)` and the `q`-adic valuation of `pY`. -/

lemma omega_pow_even (d : ℤ) : ∀ t : ℕ,
    ((⟨0, 1⟩ : ℤ√d) ^ (2 * t)) = ⟨d ^ t, 0⟩
  | 0 => by simp
  | t + 1 => by
    have ih := omega_pow_even d t
    have h2 : ((⟨0, 1⟩ : ℤ√d) ^ 2) = ⟨d, 0⟩ := by
      ext <;> simp [pow_two]
    calc
      (⟨0, 1⟩ : ℤ√d) ^ (2 * (t + 1))
          = (⟨0, 1⟩ : ℤ√d) ^ (2 * t + 2) := by ring_nf
      _ = (⟨0, 1⟩ : ℤ√d) ^ (2 * t) * (⟨0, 1⟩ : ℤ√d) ^ 2 := by
            rw [pow_add]
      _ = ⟨d ^ t, 0⟩ * ⟨d, 0⟩ := by rw [ih, h2]
      _ = ⟨d ^ t * d, 0⟩ := by ext <;> simp
      _ = ⟨d ^ (t + 1), 0⟩ := by
            ext <;> simp [pow_succ]

lemma omega_pow_odd (d : ℤ) (t : ℕ) :
    ((⟨0, 1⟩ : ℤ√d) ^ (2 * t + 1)) = ⟨0, d ^ t⟩ := by
  rw [pow_succ, omega_pow_even]
  ext <;> simp

lemma alpha_eq_add (r : ℤ) :
    alpha r = (r : ℤ√(r ^ 2 + 2)) + ⟨0, 1⟩ := by
  ext <;> simp [alpha]

lemma intCast_pow_re (d : ℤ) (a : ℤ) (n : ℕ) :
    ((a : ℤ√d) ^ n).re = a ^ n ∧ ((a : ℤ√d) ^ n).im = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    constructor
    · simp [ih.1, ih.2]; ring
    · simp [ih.1, ih.2]

lemma im_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ m ∈ s, f m).im = ∑ m ∈ s, (f m).im := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Zsqrtd.im_add, ih]

lemma re_sum {d : ℤ} (s : Finset ℕ) (f : ℕ → ℤ√d) :
    (∑ m ∈ s, f m).re = ∑ m ∈ s, (f m).re := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, Zsqrtd.re_add, ih]

def binomTerm (r : ℤ) (k t : ℕ) : ℤ :=
  (Nat.choose (2 * k + 1) (2 * t + 1) : ℤ) * r ^ (2 * (k - t)) * (r ^ 2 + 2) ^ t

lemma mul_omega_pow_im (r : ℤ) (m t : ℕ) :
    (((r : ℤ√(r ^ 2 + 2)) ^ m) * ((⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * t + 1))).im =
      r ^ m * (r ^ 2 + 2) ^ t := by
  have hr := intCast_pow_re (r ^ 2 + 2) r m
  rw [omega_pow_odd, Zsqrtd.im_mul, hr.1, hr.2]
  simp

lemma mul_omega_pow_even_im (r : ℤ) (m t : ℕ) :
    (((r : ℤ√(r ^ 2 + 2)) ^ m) * ((⟨0, 1⟩ : ℤ√(r ^ 2 + 2)) ^ (2 * t))).im = 0 := by
  have hr := intCast_pow_re (r ^ 2 + 2) r m
  rw [omega_pow_even, Zsqrtd.im_mul, hr.1, hr.2]
  simp
