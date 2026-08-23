import Mathlib

open Zsqrtd Int

abbrev Zsqrt2 := ℤ√(2 : ℤ)

namespace Zsqrt2

lemma two_not_sq : ∀ n : ℤ, (2 : ℤ) ≠ n * n := by
  intro n h
  have hsq : n ^ 2 = 2 := by rw [sq]; exact h.symm
  have habs : |n| ≤ 1 := by
    have : n ^ 2 < (2 : ℤ) ^ 2 := by nlinarith
    have : |n| < 2 := lt_of_pow_lt_pow_left₀ 2 (by decide : (0 : ℤ) ≤ 2) (by rwa [sq_abs])
    have : 0 ≤ |n| := abs_nonneg _
    omega
  have : |n| = 0 ∨ |n| = 1 := by
    have : 0 ≤ |n| := abs_nonneg _
    omega
  rcases this with h0 | h1
  · rw [abs_eq_zero] at h0; subst h0; norm_num at hsq
  · rcases eq_or_eq_neg_of_abs_eq h1 with rfl | rfl <;> norm_num at hsq

lemma norm_eq (z : Zsqrt2) : z.norm = z.re ^ 2 - 2 * z.im ^ 2 := by
  rw [norm_def]; ring

lemma norm_eq_zero_iff' (z : Zsqrt2) : z.norm = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero two_not_sq z

lemma int_abs_sub_mul_round (a N : ℤ) (hN : N ≠ 0) :
    |a - round ((a : ℚ) / N) * N| * 2 ≤ |N| := by
  have hNq : (N : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hN
  set q := round ((a : ℚ) / N)
  have hle : |((a : ℚ) / N) - (q : ℚ)| ≤ 1 / 2 := abs_sub_round _
  have habs : |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)| = |(a : ℚ) - (q : ℚ) * N| := by
    calc
      |((a : ℚ) / N) - (q : ℚ)| * |(N : ℚ)|
        = |(((a : ℚ) / N) - (q : ℚ)) * N| := (abs_mul _ _).symm
      _ = |(a : ℚ) - (q : ℚ) * N| := by
            rw [sub_mul, div_mul_cancel₀ _ hNq]
  have hbound : |(a : ℚ) - (q : ℚ) * N| ≤ |(N : ℚ)| / 2 := by
    rw [← habs]
    have := mul_le_mul_of_nonneg_right hle (abs_nonneg (N : ℚ))
    linarith
  have hcast : ((a - q * N : ℤ) : ℚ) = (a : ℚ) - (q : ℚ) * N := by push_cast; rfl
  have : ((|a - q * N| * 2 : ℤ) : ℚ) ≤ ((|N| : ℤ) : ℚ) := by
    rw [Int.cast_mul, Int.cast_abs, Int.cast_two, hcast, Int.cast_abs]
    linarith
  exact_mod_cast this

noncomputable instance : Div Zsqrt2 :=
  ⟨fun x y =>
    ⟨round ((x * star y).re / (y.norm : ℚ)),
     round ((x * star y).im / (y.norm : ℚ))⟩⟩

lemma div_def (x y : Zsqrt2) :
    x / y = ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
             round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩ := rfl

noncomputable instance : Mod Zsqrt2 := ⟨fun x y => x - y * (x / y)⟩

lemma mod_def (x y : Zsqrt2) : x % y = x - y * (x / y) := rfl

lemma rem_mul_star (x y : Zsqrt2) :
    (x % y) * star y = x * star y - (x / y) * (y.norm : Zsqrt2) := by
  rw [mod_def, sub_mul, norm_eq_mul_conj]
  ring

lemma rem_norm_mul (x y : Zsqrt2) :
    (x % y).norm * y.norm = (x * star y - (x / y) * (y.norm : Zsqrt2)).norm := by
  have := rem_mul_star x y
  rw [← this, Zsqrtd.norm_mul, Zsqrtd.norm_conj]

lemma mul_intCast_re (z : Zsqrt2) (n : ℤ) :
    (z * (n : Zsqrt2)).re = z.re * n := by
  simp [Zsqrtd.re_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma mul_intCast_im (z : Zsqrt2) (n : ℤ) :
    (z * (n : Zsqrt2)).im = z.im * n := by
  simp [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast]

lemma rem_norm_expand (x y : Zsqrt2) :
    (x * star y - (x / y) * (y.norm : Zsqrt2)).norm =
      ((x * star y).re - (x / y).re * y.norm) ^ 2 -
      2 * ((x * star y).im - (x / y).im * y.norm) ^ 2 := by
  rw [norm_eq, re_sub, im_sub, mul_intCast_re, mul_intCast_im]

lemma four_mul_abs_form {A B N : ℤ} (hA : |A| * 2 ≤ |N|) (hB : |B| * 2 ≤ |N|) :
    4 * |A ^ 2 - 2 * B ^ 2| ≤ 3 * N ^ 2 := by
  have hA4 : 4 * A ^ 2 ≤ N ^ 2 := by
    have : |2 * A| ≤ |N| := by
      rw [abs_mul, abs_two, mul_comm]
      exact hA
    have : (2 * A) ^ 2 ≤ N ^ 2 := sq_le_sq.mpr this
    nlinarith
  have hB4 : 4 * B ^ 2 ≤ N ^ 2 := by
    have : |2 * B| ≤ |N| := by
      rw [abs_mul, abs_two, mul_comm]
      exact hB
    have : (2 * B) ^ 2 ≤ N ^ 2 := sq_le_sq.mpr this
    nlinarith
  have hsum : 4 * (A ^ 2 + 2 * B ^ 2) ≤ 3 * N ^ 2 := by nlinarith
  have hle : |A ^ 2 - 2 * B ^ 2| ≤ A ^ 2 + 2 * B ^ 2 :=
    abs_sub_le_iff.mpr ⟨by nlinarith [sq_nonneg A, sq_nonneg B],
      by nlinarith [sq_nonneg A, sq_nonneg B]⟩
  nlinarith

lemma abs_norm_mod_lt (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    |(x % y).norm| < |y.norm| := by
  have hNne : y.norm ≠ 0 := by
    intro h0
    exact hy ((norm_eq_zero_iff' y).mp h0)
  set N := y.norm
  set α := x * star y
  set q := x / y
  have hre : |α.re - q.re * N| * 2 ≤ |N| := by
    change |α.re - round ((α.re : ℚ) / N) * N| * 2 ≤ |N|
    exact int_abs_sub_mul_round α.re N hNne
  have him : |α.im - q.im * N| * 2 ≤ |N| := by
    change |α.im - round ((α.im : ℚ) / N) * N| * 2 ≤ |N|
    exact int_abs_sub_mul_round α.im N hNne
  have h4 : 4 * |(α.re - q.re * N) ^ 2 - 2 * (α.im - q.im * N) ^ 2| ≤ 3 * N ^ 2 :=
    four_mul_abs_form hre him
  have hmul : (x % y).norm * N = (α - q * (N : Zsqrt2)).norm := rem_norm_mul x y
  have hexp : (α - q * (N : Zsqrt2)).norm =
      (α.re - q.re * N) ^ 2 - 2 * (α.im - q.im * N) ^ 2 := rem_norm_expand x y
  have : 4 * |(x % y).norm * N| ≤ 3 * N ^ 2 := by
    rw [hmul, hexp]; exact h4
  have hassoc : 4 * |(x % y).norm * N| = 4 * |(x % y).norm| * |N| := by
    rw [abs_mul, mul_assoc]
  rw [hassoc] at this
  have hNabs : 0 < |N| := abs_pos.mpr hNne
  have hNsq : N ^ 2 = |N| * |N| := by rw [← sq_abs, sq]
  have hle : 4 * |(x % y).norm| ≤ 3 * |N| := by
    have hmul' : 4 * |(x % y).norm| * |N| ≤ 3 * (|N| * |N|) := by
      rwa [hNsq] at this
    have hmul'' : 4 * |(x % y).norm| * |N| ≤ (3 * |N|) * |N| := by
      convert hmul' using 1; ring
    exact _root_.le_of_mul_le_mul_right hmul'' hNabs
  nlinarith

lemma natAbs_norm_mod_lt (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  have h := abs_norm_mod_lt x hy
  have e1 : ((x % y).norm.natAbs : ℤ) = |(x % y).norm| := Int.natCast_natAbs _
  have e2 : (y.norm.natAbs : ℤ) = |y.norm| := Int.natCast_natAbs _
  have : ((x % y).norm.natAbs : ℤ) < (y.norm.natAbs : ℤ) := by
    rwa [e1, e2]
  exact_mod_cast this

lemma natAbs_norm_mul_left (x : Zsqrt2) {y : Zsqrt2} (hy : y ≠ 0) :
    x.norm.natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have : 1 ≤ y.norm.natAbs := by
    have : y.norm ≠ 0 := by
      intro h0
      exact hy ((norm_eq_zero_iff' y).mp h0)
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr this)
  exact Nat.le_mul_of_pos_right _ this

noncomputable instance : EuclideanDomain Zsqrt2 :=
  { inferInstanceAs (CommRing Zsqrt2),
    inferInstanceAs (Nontrivial Zsqrt2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp [div_def, Zsqrtd.norm_zero]
      rfl
    quotient_mul_add_remainder_eq := fun _ _ => by
      simp [mod_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (natAbs_norm_mul_left a hb0) }

def eps : Zsqrt2 := ⟨1, 1⟩

lemma eps_norm : (eps : Zsqrt2).norm = -1 := by
  simp [eps, norm_eq]

lemma eps_mul_conj : eps * ⟨-1, 1⟩ = 1 := by
  ext <;> simp [eps]

lemma isUnit_eps : IsUnit (eps : Zsqrt2) :=
  ⟨⟨eps, ⟨-1, 1⟩, eps_mul_conj, by ext <;> simp [eps]⟩, rfl⟩

def epsInv : Zsqrt2 := ⟨-1, 1⟩

lemma eps_mul_epsInv : eps * epsInv = 1 := eps_mul_conj

lemma epsInv_mul_eps : epsInv * eps = 1 := by
  rw [mul_comm]; exact eps_mul_epsInv

lemma eps_sq : (eps : Zsqrt2) ^ 2 = ⟨3, 2⟩ := by
  ext <;> simp [eps, pow_two]

lemma two_not_isSquare : ¬ IsSquare (2 : ℤ) := by
  rintro ⟨k, hk⟩
  exact two_not_sq k hk

def fund : Pell.Solution₁ 2 := Pell.Solution₁.mk 3 2 (by norm_num)

lemma fund_x : fund.x = 3 := Pell.Solution₁.x_mk 3 2 (by norm_num)
lemma fund_y : fund.y = 2 := Pell.Solution₁.y_mk 3 2 (by norm_num)

lemma fund_isFundamental : Pell.IsFundamental fund := by
  refine ⟨?hx, ?hy, ?min⟩
  · rw [fund_x]; norm_num
  · rw [fund_y]; norm_num
  · intro b hb
    have hprop := b.prop
    have hx2 : (2 : ℤ) ≤ b.x := by linarith
    have hb3 : (3 : ℤ) ≤ b.x := by
      by_contra h
      have hxeq : b.x = 2 := by omega
      rw [hxeq] at hprop
      have : (2 : ℤ) * b.y ^ 2 = 3 := by linarith
      have hy0 : b.y ^ 2 = 0 ∨ b.y ^ 2 = 1 ∨ (4 : ℤ) ≤ b.y ^ 2 := by
        have : 0 ≤ b.y ^ 2 := sq_nonneg _
        have : b.y ^ 2 ≤ 1 ∨ 4 ≤ b.y ^ 2 := by
          have habs : |b.y| ≤ 1 ∨ 2 ≤ |b.y| := by omega
          rcases habs with h1 | h2
          · left; have := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1); simpa using this
          · right
            have : (2 : ℤ) ^ 2 ≤ |b.y| ^ 2 := pow_le_pow_left₀ (by omega) h2 2
            simpa [sq_abs] using this
        omega
      rcases hy0 with h0 | h1 | h4 <;> linarith
    simpa [fund_x] using hb3

lemma fund_coe : (fund : Zsqrt2) = ⟨3, 2⟩ := by
  simp [fund, Pell.Solution₁.coe_mk]

lemma fund_eq_eps_sq : (fund : Zsqrt2) = eps ^ 2 :=
  fund_coe.trans eps_sq.symm

lemma isUnit_of_natAbs_norm_one (z : Zsqrt2) (h : z.norm.natAbs = 1) : IsUnit z :=
  Zsqrtd.norm_eq_one_iff.mp h

lemma natAbs_norm_eq_one_of_isUnit {z : Zsqrt2} (h : IsUnit z) : z.norm.natAbs = 1 :=
  Zsqrtd.norm_eq_one_iff.mpr h

lemma norm_eq_one_or_neg_one_of_isUnit {z : Zsqrt2} (h : IsUnit z) :
    z.norm = 1 ∨ z.norm = -1 :=
  Int.natAbs_eq_iff.mp (natAbs_norm_eq_one_of_isUnit h)

lemma eq_fund_zpow_of_norm_one {z : Zsqrt2} (h : z.norm = 1) :
    ∃ k : ℤ, z = ((fund ^ k : Pell.Solution₁ 2) : Zsqrt2) ∨
      z = -((fund ^ k : Pell.Solution₁ 2) : Zsqrt2) := by
  let a : Pell.Solution₁ 2 :=
    Pell.Solution₁.mk z.re z.im (by
      have : z.re ^ 2 - 2 * z.im ^ 2 = 1 := by rw [← norm_eq, h]
      exact this)
  have ha : (a : Zsqrt2) = z := by
    ext <;> simp [a, Pell.Solution₁.coe_mk]
  obtain ⟨k, hk⟩ := fund_isFundamental.eq_zpow_or_neg_zpow a
  refine ⟨k, ?_⟩
  rcases hk with hk | hk
  · left; rw [← ha, hk]
  · right; rw [← ha, hk]; rfl

lemma epsInv_sq : (epsInv : Zsqrt2) ^ 2 = ⟨3, -2⟩ := by
  ext <;> simp [epsInv, pow_two]

def ω : Zsqrt2 := ⟨0, 1⟩

lemma ω_sq : (ω * ω : Zsqrt2) = (2 : Zsqrt2) := by
  ext <;> simp [ω]

lemma norm_ω : ω.norm = -2 := by simp [ω, norm_eq]

def plus (y : ℤ) : Zsqrt2 := ⟨y, 1⟩
def minus (y : ℤ) : Zsqrt2 := ⟨y, -1⟩

lemma plus_mul_minus (y : ℤ) : plus y * minus y = ⟨y ^ 2 - 2, 0⟩ := by
  ext
  · simp [plus, minus]; ring
  · simp [plus, minus]

lemma intCast_mk (n : ℤ) : (n : Zsqrt2) = ⟨n, 0⟩ := by
  ext <;> simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma plus_mul_minus' (y : ℤ) : plus y * minus y = (y ^ 2 - 2 : ℤ) := by
  rw [plus_mul_minus, intCast_mk]

lemma plus_sub_minus (y : ℤ) : plus y - minus y = ⟨0, 2⟩ := by
  ext <;> simp [plus, minus]

lemma two_mul_ω : (2 : Zsqrt2) * ω = ⟨0, 2⟩ := by
  ext <;> simp [ω]

lemma plus_sub_minus' (y : ℤ) : plus y - minus y = (2 : Zsqrt2) * ω := by
  rw [plus_sub_minus, two_mul_ω]

lemma star_plus (y : ℤ) : star (plus y) = minus y := by
  ext <;> simp [plus, minus]

lemma norm_plus (y : ℤ) : (plus y).norm = y ^ 2 - 2 := by
  simp [plus, norm_eq]

lemma plus_ne_zero {y : ℤ} (h : y ^ 2 ≠ 2) : plus y ≠ 0 := by
  intro hz
  have : (plus y).norm = 0 := by rw [hz]; simp [norm_def]
  rw [norm_plus] at this
  exact h (by linarith)

lemma omega_dvd_plus_iff (y : ℤ) : ω ∣ plus y ↔ Even y := by
  constructor
  · intro ⟨z, hz⟩
    have hre : (plus y).re = (ω * z).re := congrArg Zsqrtd.re hz
    have : y = 2 * z.im := by
      simp [plus, ω] at hre
      linarith
    refine ⟨z.im, ?_⟩
    rw [this, two_mul]
  · intro ⟨k, hk⟩
    refine ⟨⟨1, k⟩, ?_⟩
    ext
    · simp [plus, ω, hk]; ring
    · simp [plus, ω]

lemma odd_not_omega_dvd_plus {y : ℤ} (hy : Odd y) : ¬ ω ∣ plus y := by
  rw [omega_dvd_plus_iff]
  exact Int.not_even_iff_odd.mpr hy

lemma not_isUnit_ω : ¬ IsUnit ω := by
  intro hu
  have : ω.norm.natAbs = 1 := natAbs_norm_eq_one_of_isUnit hu
  rw [norm_ω] at this
  norm_num at this

lemma omega_irreducible : Irreducible ω := by
  refine ⟨not_isUnit_ω, ?_⟩
  intro a b hab
  have hn : (a * b).norm = -2 := by rw [← hab, norm_ω]
  rw [Zsqrtd.norm_mul] at hn
  have hdiv : a.norm ∣ 2 := ⟨-b.norm, by linarith⟩
  have habs : a.norm.natAbs ∣ 2 := Int.natAbs_dvd_natAbs.mpr hdiv
  have : a.norm.natAbs = 1 ∨ a.norm.natAbs = 2 := by
    have := Nat.le_of_dvd (by decide : (0 : ℕ) < 2) habs
    interval_cases a.norm.natAbs <;> tauto
  rcases this with h | h
  · left; exact isUnit_of_natAbs_norm_one a h
  · right
    have : b.norm.natAbs = 1 := by
      have : (a.norm * b.norm).natAbs = 2 := by rw [hn]; norm_num
      rw [Int.natAbs_mul, h] at this
      omega
    exact isUnit_of_natAbs_norm_one b this

lemma omega_prime : Prime ω := Irreducible.prime omega_irreducible

lemma two_eq_omega_sq : (2 : Zsqrt2) = ω * ω := ω_sq.symm

lemma isCoprime_plus_minus {y : ℤ} (hy : Odd y) (hne : y ^ 2 ≠ 2) :
    IsCoprime (plus y) (minus y) := by
  refine isCoprime_of_irreducible_dvd ?_ ?_
  · exact not_and_of_not_left _ (plus_ne_zero hne)
  · intro π hπ hπplus hπminus
    have hdiff : π ∣ plus y - minus y := dvd_sub hπplus hπminus
    rw [plus_sub_minus'] at hdiff
    have hω3 : π ∣ ω ^ 3 := by
      have : (2 : Zsqrt2) * ω = ω ^ 3 := by
        rw [two_eq_omega_sq, pow_three]; ring
      rwa [this] at hdiff
    have hπω : π ∣ ω :=
      (Irreducible.prime hπ).dvd_of_dvd_pow (n := 3) hω3
    have : Associated π ω :=
      (Irreducible.dvd_irreducible_iff_associated hπ omega_irreducible).mp hπω
    exact odd_not_omega_dvd_plus hy (this.symm.dvd.trans hπplus)

lemma plus_associated_pow {y : ℤ} {p n : ℕ} (hy : Odd y)
    (h : (y ^ 2 - 2 : ℤ) = (p : ℤ) ^ n) :
    ∃ d : Zsqrt2, Associated (d ^ n) (plus y) := by
  have hne : y ^ 2 ≠ 2 := by
    intro hf
    have : (p : ℤ) ^ n = 0 := by linarith
    cases n with
    | zero => norm_num at this
    | succ n =>
      have : (p : ℤ) = 0 := pow_eq_zero this
      exact two_not_sq y (by rw [← sq]; exact hf.symm)
  have hab : IsCoprime (plus y) (minus y) := isCoprime_plus_minus hy hne
  have hmul : plus y * minus y = ((p : ℤ) : Zsqrt2) ^ n := by
    rw [plus_mul_minus', h, Int.cast_pow]
  exact exists_associated_pow_of_mul_eq_pow' hab hmul

lemma s_dvd_im_pow (r s : ℤ) : ∀ n : ℕ, s ∣ ((⟨r, s⟩ : Zsqrt2) ^ n).im
  | 0 => by simp
  | n + 1 => by
    have ih := s_dvd_im_pow r s n
    have : ((⟨r, s⟩ : Zsqrt2) ^ (n + 1)).im =
        r * ((⟨r, s⟩ : Zsqrt2) ^ n).im + s * ((⟨r, s⟩ : Zsqrt2) ^ n).re := by
      rw [pow_succ, im_mul]; simp; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

lemma norm_pow (z : Zsqrt2) : ∀ n : ℕ, (z ^ n).norm = z.norm ^ n
  | 0 => by simp [norm_def]
  | n + 1 => by rw [pow_succ, pow_succ, Zsqrtd.norm_mul, norm_pow]

lemma s_dvd_one_of_plus_eq_pow {y r s : ℤ} {n : ℕ}
    (h : plus y = (⟨r, s⟩ : Zsqrt2) ^ n ∨ plus y = -((⟨r, s⟩ : Zsqrt2) ^ n)) :
    s ∣ 1 := by
  have him : (plus y).im = 1 := rfl
  have hs := s_dvd_im_pow r s n
  rcases h with h | h
  · rw [h] at him; rwa [← him]
  · have : (-((⟨r, s⟩ : Zsqrt2) ^ n)).im = -((⟨r, s⟩ : Zsqrt2) ^ n).im := by simp
    rw [h, this] at him
    have : s ∣ -((⟨r, s⟩ : Zsqrt2) ^ n).im := hs.neg_right
    rwa [him] at this

/-! ### Recurrence for `(a + √2)^n` -/

def UV2 (a : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let u := (UV2 a n).1
    let v := (UV2 a n).2
    (a * u + 2 * v, u + a * v)

def U2 (a : ℤ) (n : ℕ) : ℤ := (UV2 a n).1
def V2 (a : ℤ) (n : ℕ) : ℤ := (UV2 a n).2

lemma U2_zero (a : ℤ) : U2 a 0 = 1 := rfl
lemma V2_zero (a : ℤ) : V2 a 0 = 0 := rfl
lemma U2_succ (a : ℤ) (n : ℕ) : U2 a (n + 1) = a * U2 a n + 2 * V2 a n := rfl
lemma V2_succ (a : ℤ) (n : ℕ) : V2 a (n + 1) = U2 a n + a * V2 a n := rfl

lemma pow_eq_U2_V2 (a : ℤ) : ∀ n : ℕ,
    (⟨a, 1⟩ : Zsqrt2) ^ n = ⟨U2 a n, V2 a n⟩
  | 0 => by
    ext
    · simp [U2_zero]
    · simp [V2_zero]
  | n + 1 => by
    rw [pow_succ, pow_eq_U2_V2 a n, U2_succ, V2_succ]
    ext
    · simp; ring
    · simp; ring

lemma V2_one (a : ℤ) : V2 a 1 = 1 := by simp [V2_succ, U2_zero, V2_zero]
lemma U2_one (a : ℤ) : U2 a 1 = a := by simp [U2_succ, U2_zero, V2_zero]
lemma V2_two (a : ℤ) : V2 a 2 = 2 * a := by
  rw [V2_succ, U2_one, V2_one]; ring
lemma U2_two (a : ℤ) : U2 a 2 = a ^ 2 + 2 := by
  rw [U2_succ, U2_one, V2_one]; ring
lemma V2_three (a : ℤ) : V2 a 3 = 3 * a ^ 2 + 2 := by
  rw [V2_succ, U2_two, V2_two]; ring

lemma U2_V2_norm (a : ℤ) : ∀ n : ℕ,
    U2 a n ^ 2 - 2 * V2 a n ^ 2 = (a ^ 2 - 2) ^ n
  | 0 => by simp [U2_zero, V2_zero]
  | n + 1 => by
    have ih := U2_V2_norm a n
    calc
      U2 a (n + 1) ^ 2 - 2 * V2 a (n + 1) ^ 2
        = (a * U2 a n + 2 * V2 a n) ^ 2 - 2 * (U2 a n + a * V2 a n) ^ 2 := by
          rw [U2_succ, V2_succ]
      _ = (a ^ 2 - 2) * (U2 a n ^ 2 - 2 * V2 a n ^ 2) := by ring
      _ = (a ^ 2 - 2) * (a ^ 2 - 2) ^ n := by rw [ih]
      _ = (a ^ 2 - 2) ^ (n + 1) := (pow_succ' _ _).symm

/-! ### Binomial expansion of the imaginary part -/

lemma intCast_mk' (n : ℤ) : (⟨n, 0⟩ : Zsqrt2) = (n : Zsqrt2) := (intCast_mk n).symm

lemma omega_pow_even (j : ℕ) : (⟨0, 1⟩ : Zsqrt2) ^ (2 * j) = ⟨(2 : ℤ) ^ j, 0⟩ := by
  induction j with
  | zero =>
    ext <;> simp
  | succ j ih =>
    have : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [this, pow_add, ih, pow_two]
    ext <;> simp; ring

lemma omega_pow_odd (j : ℕ) : (⟨0, 1⟩ : Zsqrt2) ^ (2 * j + 1) = ⟨0, (2 : ℤ) ^ j⟩ := by
  rw [pow_succ, omega_pow_even]
  ext <;> simp

lemma re_pow_int (a : ℤ) (m : ℕ) : ((a : Zsqrt2) ^ m).re = a ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Zsqrtd.re_mul, ih]
    simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring

lemma im_pow_int (a : ℤ) (m : ℕ) : ((a : Zsqrt2) ^ m).im = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Zsqrtd.im_mul, ih]
    simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma im_mul_omega_pow (a : ℤ) (m i : ℕ) :
    ((a : Zsqrt2) ^ m * (⟨0, 1⟩ : Zsqrt2) ^ i).im =
      if Even i then 0 else a ^ m * (2 : ℤ) ^ (i / 2) := by
  by_cases he : Even i
  · rw [if_pos he]
    obtain ⟨j, rfl⟩ := he
    rw [show j + j = 2 * j by omega, omega_pow_even]
    simp [Zsqrtd.im_mul, im_pow_int]
  · rw [if_neg he]
    have hodd : Odd i := Nat.not_even_iff_odd.mp he
    obtain ⟨j, rfl⟩ := hodd
    have hdiv : (2 * j + 1) / 2 = j := by omega
    rw [omega_pow_odd, hdiv]
    simp [Zsqrtd.im_mul, re_pow_int, im_pow_int]

lemma im_monomial (a : ℤ) (n i : ℕ) :
    ((a : Zsqrt2) ^ (n - i) * (⟨0, 1⟩ : Zsqrt2) ^ i).im =
      if Even i then 0 else a ^ (n - i) * (2 : ℤ) ^ (i / 2) :=
  im_mul_omega_pow a (n - i) i

lemma mk_a_one_eq (a : ℤ) : (⟨a, 1⟩ : Zsqrt2) = (a : Zsqrt2) + ⟨0, 1⟩ := by
  ext <;> simp [Zsqrtd.re_intCast, Zsqrtd.im_intCast]

lemma V2_eq_im_pow (a : ℤ) (n : ℕ) : V2 a n = ((⟨a, 1⟩ : Zsqrt2) ^ n).im := by
  rw [pow_eq_U2_V2]

lemma U2_eq_re_pow (a : ℤ) (n : ℕ) : U2 a n = ((⟨a, 1⟩ : Zsqrt2) ^ n).re := by
  rw [pow_eq_U2_V2]

lemma sq_mul_pow (a : ℤ) :
    (⟨a, 1⟩ : Zsqrt2) ^ 2 = ⟨a ^ 2 + 2, 2 * a⟩ := by
  ext <;> simp [pow_two]; ring

lemma U2_odd_succ (a : ℤ) (k : ℕ) :
    U2 a (2 * k + 3) = (a ^ 2 + 2) * U2 a (2 * k + 1) + 4 * a * V2 a (2 * k + 1) := by
  have hsplit : 2 * k + 3 = 2 + (2 * k + 1) := by omega
  have h : (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 3) =
      (⟨a, 1⟩ : Zsqrt2) ^ 2 * (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 1) := by
    rw [hsplit, pow_add]
  have h2 : (⟨U2 a (2 * k + 3), V2 a (2 * k + 3)⟩ : Zsqrt2) =
      ⟨a ^ 2 + 2, 2 * a⟩ * ⟨U2 a (2 * k + 1), V2 a (2 * k + 1)⟩ := by
    rw [← pow_eq_U2_V2, h, sq_mul_pow, pow_eq_U2_V2]
  have := congrArg Zsqrtd.re h2
  simp [Zsqrtd.re_mul] at this
  linarith

lemma V2_odd_succ (a : ℤ) (k : ℕ) :
    V2 a (2 * k + 3) = (a ^ 2 + 2) * V2 a (2 * k + 1) + 2 * a * U2 a (2 * k + 1) := by
  have hsplit : 2 * k + 3 = 2 + (2 * k + 1) := by omega
  have h : (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 3) =
      (⟨a, 1⟩ : Zsqrt2) ^ 2 * (⟨a, 1⟩ : Zsqrt2) ^ (2 * k + 1) := by
    rw [hsplit, pow_add]
  have h2 : (⟨U2 a (2 * k + 3), V2 a (2 * k + 3)⟩ : Zsqrt2) =
      ⟨a ^ 2 + 2, 2 * a⟩ * ⟨U2 a (2 * k + 1), V2 a (2 * k + 1)⟩ := by
    rw [← pow_eq_U2_V2, h, sq_mul_pow, pow_eq_U2_V2]
  have := congrArg Zsqrtd.im h2
  simp [Zsqrtd.im_mul] at this
  linarith

/-- For odd exponents, `V2` is nonnegative and `a * U2` is nonnegative. -/
lemma UV2_odd_nonneg (a : ℤ) : ∀ k : ℕ,
    0 ≤ a * U2 a (2 * k + 1) ∧ 0 ≤ V2 a (2 * k + 1)
  | 0 => by
    constructor
    · simp [U2_one]; exact mul_self_nonneg a
    · simp [V2_one]
  | k + 1 => by
    have ih := UV2_odd_nonneg a k
    constructor
    · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, U2_odd_succ]
      nlinarith [ih.1, ih.2, sq_nonneg a]
    · rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, V2_odd_succ]
      nlinarith [ih.1, ih.2, sq_nonneg a]

lemma V2_odd_ge_two_pow (a : ℤ) : ∀ k : ℕ, (2 : ℤ) ^ k ≤ V2 a (2 * k + 1)
  | 0 => by simp [V2_one]
  | k + 1 => by
    have ih := V2_odd_ge_two_pow a k
    have hnn := UV2_odd_nonneg a k
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega, V2_odd_succ, pow_succ]
    nlinarith [hnn.1, hnn.2, sq_nonneg a]

/-- If `n` is odd and at least 3, then `V2 a n ≥ 2`, hence `|V2 a n| ≠ 1`. -/
lemma V2_ne_one_of_odd {a : ℤ} {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    |V2 a n| ≠ 1 := by
  obtain ⟨k, hk⟩ := hodd
  have : n = 2 * k + 1 := by omega
  subst this
  have hk1 : 1 ≤ k := by omega
  have hge := V2_odd_ge_two_pow a k
  have h2 : (2 : ℤ) ≤ (2 : ℤ) ^ k := by
    have : 1 ≤ k := hk1
    exact le_trans (by decide : (2 : ℤ) ≤ 2 ^ 1) (pow_le_pow_right₀ (by decide : (1 : ℤ) ≤ 2) this)
  intro habs
  have : V2 a (2 * k + 1) = 1 ∨ V2 a (2 * k + 1) = -1 := eq_or_eq_neg_of_abs_eq habs
  rcases this with h | h <;> linarith

/-- The `r = 0` case: `plus y = ± ⟨r,s⟩^n` forces `s = ±1` and then `|V2 r n| = 1`. -/
lemma no_pure_nth_power {y : ℤ} {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    {r s : ℤ}
    (h : plus y = (⟨r, s⟩ : Zsqrt2) ^ n ∨ plus y = -((⟨r, s⟩ : Zsqrt2) ^ n)) : False := by
  have hs : s ∣ 1 := s_dvd_one_of_plus_eq_pow h
  have hs1 : s = 1 ∨ s = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hs)
  have him0 : (plus y).im = 1 := rfl
  have hV : |V2 r n| = 1 := by
    rcases hs1 with rfl | rfl
    · have hp := pow_eq_U2_V2 r n
      rcases h with h | h
      · have him : ((⟨r, 1⟩ : Zsqrt2) ^ n).im = 1 := by rw [← h]; exact him0
        rw [hp] at him
        have : V2 r n = 1 := by simpa using him
        simp [this]
      · have him : (-((⟨r, 1⟩ : Zsqrt2) ^ n)).im = 1 := by rw [← h]; exact him0
        rw [hp] at him
        have : V2 r n = -1 := by
          have : -V2 r n = 1 := by simpa using him
          linarith
        simp [this]
    · have hstar : (⟨r, -1⟩ : Zsqrt2) = star (⟨r, 1⟩ : Zsqrt2) := by ext <;> simp
      have hsp : (⟨r, -1⟩ : Zsqrt2) ^ n = star ((⟨r, 1⟩ : Zsqrt2) ^ n) := by
        rw [hstar, star_pow]
      rw [pow_eq_U2_V2] at hsp
      rcases h with h | h
      · have him : ((⟨r, -1⟩ : Zsqrt2) ^ n).im = 1 := by rw [← h]; exact him0
        rw [hsp] at him
        have : V2 r n = -1 := by
          have : -V2 r n = 1 := by simpa using him
          linarith
        simp [this]
      · have him : (-((⟨r, -1⟩ : Zsqrt2) ^ n)).im = 1 := by rw [← h]; exact him0
        rw [hsp] at him
        have : V2 r n = 1 := by
          have : -(-V2 r n) = 1 := by simpa using him
          linarith
        simp [this]
  exact V2_ne_one_of_odd hn hodd hV

/-! ### The unit group is `{± ε ^ k}` -/

def epsUnit : Zsqrt2ˣ :=
  ⟨eps, epsInv, eps_mul_epsInv, epsInv_mul_eps⟩

lemma epsUnit_coe : (epsUnit : Zsqrt2) = eps := rfl

lemma epsUnit_inv_coe : ((epsUnit⁻¹ : Zsqrt2ˣ) : Zsqrt2) = epsInv := rfl

lemma epsUnit_pow_coe : ∀ n : ℕ, ((epsUnit ^ n : Zsqrt2ˣ) : Zsqrt2) = eps ^ n
  | 0 => by simp [epsUnit_coe]
  | n + 1 => by
    rw [pow_succ, pow_succ, Units.val_mul, epsUnit_pow_coe n, epsUnit_coe]

lemma fund_pow_nat : ∀ n : ℕ, (fund : Zsqrt2) ^ n = eps ^ (2 * n)
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, fund_pow_nat n, fund_eq_eps_sq, ← pow_add]
    congr 1

lemma coe_fund_mul (a b : Pell.Solution₁ 2) :
    (↑(a * b) : Zsqrt2) = (↑a : Zsqrt2) * (↑b : Zsqrt2) :=
  rfl

lemma fund_pow_coe : ∀ n : ℕ, (↑(fund ^ n) : Zsqrt2) = (fund : Zsqrt2) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ, coe_fund_mul, fund_pow_coe n]

lemma fund_inv_coe : (↑(fund⁻¹) : Zsqrt2) = ⟨3, -2⟩ := by
  apply Zsqrtd.ext
  · change (fund⁻¹).x = 3
    rw [Pell.Solution₁.x_inv, fund_x]
  · change (fund⁻¹).y = -2
    rw [Pell.Solution₁.y_inv, fund_y]

lemma fund_inv_pow_coe : ∀ m : ℕ,
    (↑(fund⁻¹ ^ m) : Zsqrt2) = (⟨3, -2⟩ : Zsqrt2) ^ m
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, pow_succ, coe_fund_mul, fund_inv_pow_coe m, fund_inv_coe]

lemma fund_zpow_pos (n : ℕ) : (↑(fund ^ (n : ℤ)) : Zsqrt2) = (fund : Zsqrt2) ^ n := by
  rw [zpow_natCast, fund_pow_coe]

lemma fund_zpow_neg (n : ℕ) : (↑(fund ^ (-(n : ℤ))) : Zsqrt2) = (⟨3, -2⟩ : Zsqrt2) ^ n := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, fund_inv_pow_coe]

lemma epsUnit_zpow_pos (n : ℕ) : ↑(epsUnit ^ (n : ℤ)) = eps ^ n := by
  rw [zpow_natCast, epsUnit_pow_coe]

lemma epsUnit_inv_pow_coe : ∀ n : ℕ, ↑((epsUnit⁻¹) ^ n) = epsInv ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ, Units.val_mul, epsUnit_inv_pow_coe n, epsUnit_inv_coe]

lemma epsUnit_zpow_neg (n : ℕ) : ↑(epsUnit ^ (-(n : ℤ))) = epsInv ^ n := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, epsUnit_inv_pow_coe]

lemma fund_zpow_eq_epsUnit : ∀ k : ℤ, (↑(fund ^ k) : Zsqrt2) = ↑(epsUnit ^ (2 * k))
  | (n : ℕ) => by
    rw [fund_zpow_pos, fund_pow_nat]
    have h2 : (2 : ℤ) * (n : ℤ) = ((2 * n : ℕ) : ℤ) := by simp
    rw [h2, epsUnit_zpow_pos]
  | Int.negSucc n => by
    have hk : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := Int.negSucc_eq n
    rw [hk, fund_zpow_neg]
    have h2 : (2 : ℤ) * (-((n + 1 : ℕ) : ℤ)) = -((2 * (n + 1) : ℕ) : ℤ) := by
      push_cast; ring
    rw [h2, epsUnit_zpow_neg]
    have : (epsInv : Zsqrt2) ^ (2 * (n + 1)) = (⟨3, -2⟩ : Zsqrt2) ^ (n + 1) := by
      rw [pow_mul, epsInv_sq]
    exact this.symm

lemma mul_epsInv_of_mul_eps {z w : Zsqrt2} (h : z * eps = w) :
    z = w * epsInv := by
  have := congrArg (· * epsInv) h
  simpa [mul_assoc, eps_mul_epsInv] using this

lemma epsUnit_mul_inv (k : ℤ) :
    ↑(epsUnit ^ k) * epsInv = ↑(epsUnit ^ (k - 1)) := by
  have : epsInv = ↑(epsUnit⁻¹) := rfl
  rw [this, ← Units.val_mul, ← zpow_neg_one, ← zpow_add]
  congr 2

lemma isUnit_eq_epsUnit_zpow {z : Zsqrt2} (h : IsUnit z) :
    ∃ k : ℤ, z = ↑(epsUnit ^ k) ∨ z = -↑(epsUnit ^ k) := by
  rcases norm_eq_one_or_neg_one_of_isUnit h with h1 | hneg
  · obtain ⟨k, hk | hk⟩ := eq_fund_zpow_of_norm_one h1
    · exact ⟨2 * k, Or.inl (hk.trans (fund_zpow_eq_epsUnit k))⟩
    · exact ⟨2 * k, Or.inr (hk.trans (by rw [fund_zpow_eq_epsUnit]))⟩
  · have hzeps : (z * eps).norm = 1 := by
      rw [Zsqrtd.norm_mul, hneg, eps_norm]; norm_num
    obtain ⟨k, hk | hk⟩ := eq_fund_zpow_of_norm_one hzeps
    · refine ⟨2 * k - 1, Or.inl ?_⟩
      have hk' : z * eps = ↑(epsUnit ^ (2 * k)) :=
        hk.trans (fund_zpow_eq_epsUnit k)
      rw [mul_epsInv_of_mul_eps hk', epsUnit_mul_inv]
    · refine ⟨2 * k - 1, Or.inr ?_⟩
      have hk' : z * eps = -↑(epsUnit ^ (2 * k)) :=
        hk.trans (by rw [fund_zpow_eq_epsUnit])
      have : z = -↑(epsUnit ^ (2 * k)) * epsInv :=
        mul_epsInv_of_mul_eps (w := -↑(epsUnit ^ (2 * k))) hk'
      rw [this, neg_mul, epsUnit_mul_inv]

lemma associated_iff_unit_mul {a b : Zsqrt2} :
    Associated a b ↔ ∃ u : Zsqrt2ˣ, a * ↑u = b :=
  Iff.rfl

lemma plus_eq_unit_cube {y : ℤ} {p : ℕ} (hy : Odd y)
    (h : (y ^ 2 - 2 : ℤ) = (p : ℤ) ^ 3) :
    ∃ (k : ℤ) (d : Zsqrt2),
      plus y = ↑(epsUnit ^ k) * d ^ 3 ∨
      plus y = -↑(epsUnit ^ k) * d ^ 3 := by
  obtain ⟨d, hd⟩ := plus_associated_pow (n := 3) hy h
  obtain ⟨u, hu⟩ := hd
  -- hu : d ^ 3 * ↑u = plus y
  obtain ⟨k, hk | hk⟩ := isUnit_eq_epsUnit_zpow u.isUnit
  · refine ⟨k, d, Or.inl ?_⟩
    rw [← hu, hk, mul_comm]
  · refine ⟨k, d, Or.inr ?_⟩
    rw [← hu, hk, mul_comm, neg_mul]

lemma Int.emod_three_eq (k : ℤ) : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
  have : k % 3 < 3 := Int.emod_lt_of_pos k (by decide)
  have : 0 ≤ k % 3 := Int.emod_nonneg k (by decide)
  omega

lemma epsUnit_zpow_mod_three (k : ℤ) (d : Zsqrt2) :
    (↑(epsUnit ^ k) : Zsqrt2) * d ^ 3 =
      (↑(epsUnit ^ (k % 3)) : Zsqrt2) *
        ((↑(epsUnit ^ (k / 3)) : Zsqrt2) * d) ^ 3 := by
  have hdiv : k = 3 * (k / 3) + k % 3 := (Int.ediv_add_emod k 3).symm
  have hz : (↑(epsUnit ^ k) : Zsqrt2) =
      (↑(epsUnit ^ (k % 3)) : Zsqrt2) * (↑(epsUnit ^ (3 * (k / 3))) : Zsqrt2) := by
    rw [← Units.val_mul]
    congr 1
    rw [← zpow_add, add_comm, ← hdiv]
  rw [hz]
  have hcube : (↑(epsUnit ^ (3 * (k / 3))) : Zsqrt2) =
      (↑(epsUnit ^ (k / 3)) : Zsqrt2) ^ 3 := by
    have : (3 : ℤ) * (k / 3) = (k / 3) + (k / 3) + (k / 3) := by ring
    rw [this, zpow_add, zpow_add, Units.val_mul, Units.val_mul, pow_three]
    ring
  rw [hcube]
  ring

/-! ### Expansions of `ε * δ³` and `ε² * δ³` -/

lemma mul_eps_mk (a b : ℤ) :
    eps * (⟨a, b⟩ : Zsqrt2) = ⟨a + 2 * b, a + b⟩ := by
  ext <;> simp [eps]; ring

lemma mul_eps_sq_mk (a b : ℤ) :
    (eps ^ 2) * (⟨a, b⟩ : Zsqrt2) = ⟨3 * a + 4 * b, 2 * a + 3 * b⟩ := by
  ext <;> simp [eps, pow_two]; ring

lemma cube_re_im (a b : ℤ) :
    ((⟨a, b⟩ : Zsqrt2) ^ 3).re = a ^ 3 + 6 * a * b ^ 2 ∧
    ((⟨a, b⟩ : Zsqrt2) ^ 3).im = 3 * a ^ 2 * b + 2 * b ^ 3 := by
  have h2 : (⟨a, b⟩ : Zsqrt2) ^ 2 = ⟨a ^ 2 + 2 * b ^ 2, 2 * a * b⟩ := by
    ext <;> simp [pow_two] <;> ring
  have h3 : (⟨a, b⟩ : Zsqrt2) ^ 3 = ⟨a, b⟩ * ((⟨a, b⟩ : Zsqrt2) ^ 2) := pow_succ' _ _
  rw [h3, h2]
  constructor <;> simp <;> ring

def thue1 (a b : ℤ) : ℤ := a ^ 3 + 3 * a ^ 2 * b + 6 * a * b ^ 2 + 2 * b ^ 3
def thue2 (a b : ℤ) : ℤ := 2 * a ^ 3 + 9 * a ^ 2 * b + 12 * a * b ^ 2 + 6 * b ^ 3
def gForm (k b : ℤ) : ℤ := k ^ 3 + 3 * k * b ^ 2 - 2 * b ^ 3

lemma thue1_eq_gForm (a b : ℤ) : thue1 a b = gForm (a + b) b := by
  simp [thue1, gForm]; ring

lemma im_eps_cube (a b : ℤ) :
    (eps * (⟨a, b⟩ : Zsqrt2) ^ 3).im = thue1 a b := by
  have hri := cube_re_im a b
  simp [eps, thue1, Zsqrtd.im_mul, hri.1, hri.2]
  ring

lemma im_eps_sq_cube (a b : ℤ) :
    ((eps ^ 2) * (⟨a, b⟩ : Zsqrt2) ^ 3).im = thue2 a b := by
  have hri := cube_re_im a b
  have heps2 : (eps ^ 2 : Zsqrt2) = ⟨3, 2⟩ := eps_sq
  simp [heps2, thue2, Zsqrtd.im_mul, hri.1, hri.2]
  ring

lemma plus_im (y : ℤ) : (plus y).im = 1 := rfl

/-! ### The cubic Thue equation `gForm k b = ±1` -/

lemma gForm_neg (k b : ℤ) : gForm (-k) (-b) = -gForm k b := by
  simp [gForm]; ring

lemma gForm_even_of_odd_b {k b : ℤ} (hb : Odd b) : Even (gForm k b) := by
  have hmod : gForm k b ≡ k ^ 3 + k * b ^ 2 [ZMOD 2] := by
    refine Int.modEq_iff_dvd.mpr ⟨b ^ 3 - k * b ^ 2, ?_⟩
    simp only [gForm]; ring
  have hb2 : (b ^ 2 : ℤ) ≡ 1 [ZMOD 2] := Int.odd_iff.mp (Odd.pow hb)
  have hkb' : k * b ^ 2 ≡ k [ZMOD 2] := by
    simpa using (Int.ModEq.mul_left k hb2)
  have hsum0 : k ^ 3 + k * b ^ 2 ≡ k ^ 3 + k [ZMOD 2] := Int.ModEq.add_left _ hkb'
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by
    have : k % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    have : 0 ≤ k % 2 := Int.emod_nonneg _ (by decide)
    omega
  have hsum : k ^ 3 + k ≡ 0 [ZMOD 2] := by
    rcases hk with hk | hk
    · have hk0 : k ≡ 0 [ZMOD 2] := hk
      have hk3 : k ^ 3 ≡ 0 [ZMOD 2] := by simpa using Int.ModEq.pow (n := 2) 3 hk0
      exact hk3.add hk0
    · have hk1 : k ≡ 1 [ZMOD 2] := hk
      have hk3 : k ^ 3 ≡ 1 [ZMOD 2] := by simpa using Int.ModEq.pow (n := 2) 3 hk1
      exact (hk3.add hk1).trans (by decide : (1 + 1 : ℤ) ≡ 0 [ZMOD 2])
  exact Int.even_iff.mpr (hmod.trans (hsum0.trans hsum))

lemma b_even_of_gForm_pm_one {k b : ℤ} (h : gForm k b = 1 ∨ gForm k b = -1) :
    Even b := by
  by_contra hb
  have he : Even (gForm k b) := gForm_even_of_odd_b (Int.not_even_iff_odd.mp hb)
  rcases h with h | h <;> (rw [h] at he; revert he; decide)

lemma gForm_modEq (k b : ℤ) :
    gForm k b ≡ (k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3 [ZMOD 9] := by
  have hk : k ≡ k % 9 [ZMOD 9] := (Int.mod_modEq k 9).symm
  have hb : b ≡ b % 9 [ZMOD 9] := (Int.mod_modEq b 9).symm
  have hk3 : k ^ 3 ≡ (k % 9) ^ 3 [ZMOD 9] := Int.ModEq.pow 3 hk
  have hb2 : b ^ 2 ≡ (b % 9) ^ 2 [ZMOD 9] := Int.ModEq.pow 2 hb
  have hb3 : b ^ 3 ≡ (b % 9) ^ 3 [ZMOD 9] := Int.ModEq.pow 3 hb
  have h3 : 3 * k * b ^ 2 ≡ 3 * (k % 9) * (b % 9) ^ 2 [ZMOD 9] :=
    (Int.ModEq.mul_left 3 hk).mul hb2
  have h2 : 2 * b ^ 3 ≡ 2 * (b % 9) ^ 3 [ZMOD 9] := Int.ModEq.mul_left 2 hb3
  simpa [gForm] using (hk3.add h3).sub h2

lemma three_dvd_b_of_gForm_pm_one {k b : ℤ}
    (h : gForm k b = 1 ∨ gForm k b = -1) : (3 : ℤ) ∣ b := by
  have hg : gForm k b % 9 = 1 ∨ gForm k b % 9 = 8 := by
    rcases h with h | h <;> simp [h]
  have hr : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    have : b % 3 < 3 := Int.emod_lt_of_pos b (by decide)
    have : 0 ≤ b % 3 := Int.emod_nonneg b (by decide)
    omega
  rcases hr with h0 | h1 | h2
  · exact Int.dvd_iff_emod_eq_zero.mpr h0
  · have hb9 : b % 9 = 1 ∨ b % 9 = 4 ∨ b % 9 = 7 := by
      have : b % 9 < 9 := Int.emod_lt_of_pos b (by decide)
      have : 0 ≤ b % 9 := Int.emod_nonneg b (by decide)
      have e : b % 3 = (b % 9) % 3 :=
        (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 9)).symm
      omega
    have hk9 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨
        k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      have : k % 9 < 9 := Int.emod_lt_of_pos k (by decide)
      have : 0 ≤ k % 9 := Int.emod_nonneg k (by decide)
      omega
    have hgeq : gForm k b % 9 =
        ((k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3) % 9 :=
      Int.ModEq.eq (gForm_modEq k b)
    rw [hgeq] at hg
    rcases hb9 with hb9 | hb9 | hb9 <;>
      rcases hk9 with hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9
    all_goals (rw [hk9, hb9] at hg; norm_num at hg)
  · have hb9 : b % 9 = 2 ∨ b % 9 = 5 ∨ b % 9 = 8 := by
      have : b % 9 < 9 := Int.emod_lt_of_pos b (by decide)
      have : 0 ≤ b % 9 := Int.emod_nonneg b (by decide)
      have e : b % 3 = (b % 9) % 3 :=
        (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 9)).symm
      omega
    have hk9 : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 2 ∨ k % 9 = 3 ∨ k % 9 = 4 ∨
        k % 9 = 5 ∨ k % 9 = 6 ∨ k % 9 = 7 ∨ k % 9 = 8 := by
      have : k % 9 < 9 := Int.emod_lt_of_pos k (by decide)
      have : 0 ≤ k % 9 := Int.emod_nonneg k (by decide)
      omega
    have hgeq : gForm k b % 9 =
        ((k % 9) ^ 3 + 3 * (k % 9) * (b % 9) ^ 2 - 2 * (b % 9) ^ 3) % 9 :=
      Int.ModEq.eq (gForm_modEq k b)
    rw [hgeq] at hg
    rcases hb9 with hb9 | hb9 | hb9 <;>
      rcases hk9 with hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9 | hk9
    all_goals (rw [hk9, hb9] at hg; norm_num at hg)

lemma six_dvd_b_of_gForm_pm_one {k b : ℤ}
    (h : gForm k b = 1 ∨ gForm k b = -1) : (6 : ℤ) ∣ b := by
  have h2 : (2 : ℤ) ∣ b := even_iff_two_dvd.mp (b_even_of_gForm_pm_one h)
  have h3 : (3 : ℤ) ∣ b := three_dvd_b_of_gForm_pm_one h
  have h2m : b % 2 = 0 := Int.emod_eq_zero_of_dvd h2
  have h3m : b % 3 = 0 := Int.emod_eq_zero_of_dvd h3
  have h6 : b % 6 = 0 := by
    have : b % 6 < 6 := Int.emod_lt_of_pos b (by decide)
    have : 0 ≤ b % 6 := Int.emod_nonneg b (by decide)
    have e2 : b % 2 = (b % 6) % 2 :=
      (Int.emod_emod_of_dvd b (by decide : (2 : ℤ) ∣ 6)).symm
    have e3 : b % 3 = (b % 6) % 3 :=
      (Int.emod_emod_of_dvd b (by decide : (3 : ℤ) ∣ 6)).symm
    omega
  exact Int.dvd_iff_emod_eq_zero.mpr h6

lemma gcd_k_b_of_gForm {k b : ℤ} (h : gForm k b = 1 ∨ gForm k b = -1) :
    Int.gcd k b = 1 := by
  have hd : (Int.gcd k b : ℤ) ∣ gForm k b := by
    have hk : (Int.gcd k b : ℤ) ∣ k := Int.gcd_dvd_left k b
    have hb : (Int.gcd k b : ℤ) ∣ b := Int.gcd_dvd_right k b
    have hk3 : (Int.gcd k b : ℤ) ∣ k ^ 3 := dvd_pow hk (by decide)
    have hb3 : (Int.gcd k b : ℤ) ∣ b ^ 3 := dvd_pow hb (by decide)
    have h3 : (Int.gcd k b : ℤ) ∣ 3 * k * b ^ 2 := by
      convert dvd_mul_of_dvd_left hk (3 * b ^ 2) using 1
      ring
    have h2 : (Int.gcd k b : ℤ) ∣ 2 * b ^ 3 := dvd_mul_of_dvd_right hb3 _
    simpa [gForm] using (hk3.add h3).sub h2
  have hg1 : (Int.gcd k b : ℤ) ∣ 1 := by
    rcases h with h | h
    · rwa [h] at hd
    · have : (Int.gcd k b : ℤ) ∣ -1 := by rwa [h] at hd
      simpa using this
  exact Nat.dvd_one.mp (by exact_mod_cast hg1)

lemma gForm_of_nonpos_k {k b : ℤ} (hk : k ≤ 0) (hb : 0 < b) :
    gForm k b ≤ -2 * b ^ 3 := by
  have h1 : k ^ 3 ≤ 0 := by
    have : k ^ 3 = k * k * k := by ring
    rw [this]; nlinarith
  have h2 : 3 * k * b ^ 2 ≤ 0 := by nlinarith [sq_nonneg b]
  simp only [gForm]
  nlinarith [sq_nonneg b]

lemma gForm_ne_pm_one_of_nonpos_k {k b : ℤ} (hk : k ≤ 0) (hb : 0 < b) :
    gForm k b ≠ 1 ∧ gForm k b ≠ -1 := by
  have hle := gForm_of_nonpos_k hk hb
  have : (2 : ℤ) ≤ 2 * b ^ 3 := by
    have : (1 : ℤ) ≤ b := by omega
    have : (1 : ℤ) ≤ b ^ 3 := one_le_pow₀ this
    nlinarith
  constructor <;> linarith

/-- If `gForm k b = ±1` and `b ≠ 0`, then `k` and `b` have the same (strict) sign. -/
lemma gForm_same_sign {k b : ℤ} (hb : b ≠ 0)
    (h : gForm k b = 1 ∨ gForm k b = -1) : 0 < k * b := by
  have hb'' : b < 0 ∨ 0 < b := by omega
  rcases hb'' with hbn | hbp
  · -- b < 0: reduce to -b > 0 via gForm_neg
    have : gForm (-k) (-b) = 1 ∨ gForm (-k) (-b) = -1 := by
      rw [gForm_neg]
      rcases h with h | h <;> simp [h]
    have : ¬ (-k ≤ 0) := by
      intro hk
      have hbpos : 0 < -b := by omega
      have := gForm_ne_pm_one_of_nonpos_k hk hbpos
      rcases ‹gForm (-k) (-b) = 1 ∨ gForm (-k) (-b) = -1› with h' | h'
      · exact this.1 h'
      · exact this.2 h'
    have : 0 < -k := by omega
    nlinarith
  · have : ¬ (k ≤ 0) := by
      intro hk
      have := gForm_ne_pm_one_of_nonpos_k hk hbp
      rcases h with h | h
      · exact this.1 h
      · exact this.2 h
    nlinarith

lemma gForm_eq_iff (k b : ℤ) :
    gForm k b = 1 ∨ gForm k b = -1 ↔
      k * (k ^ 2 + 3 * b ^ 2) = 2 * b ^ 3 + 1 ∨
      k * (k ^ 2 + 3 * b ^ 2) = 2 * b ^ 3 - 1 := by
  simp only [gForm]; constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- For `b = 6c` we have `gForm k (6c) = k^3 + 108 k c^2 - 432 c^3`. -/
lemma gForm_six (k c : ℤ) :
    gForm k (6 * c) = k ^ 3 + 108 * k * c ^ 2 - 432 * c ^ 3 := by
  simp [gForm]; ring

lemma gForm_six_eq_iff (k c : ℤ) :
    gForm k (6 * c) = 1 ∨ gForm k (6 * c) = -1 ↔
      k * (k ^ 2 + 108 * c ^ 2) = 432 * c ^ 3 + 1 ∨
      k * (k ^ 2 + 108 * c ^ 2) = 432 * c ^ 3 - 1 := by
  rw [gForm_six]; constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- If `7k ≤ 25c` and `c ≥ 2`, then `k(k² + 108c²) ≤ 432c³ - 2`. -/
lemma window_low {k c : ℤ} (hk : 0 ≤ k) (hc : 2 ≤ c) (hle : 7 * k ≤ 25 * c) :
    k * (k ^ 2 + 108 * c ^ 2) ≤ 432 * c ^ 3 - 2 := by
  -- 7³ k³ ≤ 25³ c³ and 108·7² k c² ≤ 108·7²·(25/7) c³ = 108·7·25 c³
  have h1 : 343 * (k * (k ^ 2 + 108 * c ^ 2)) ≤ 147925 * c ^ 3 := by
    have hk3 : 343 * k ^ 3 ≤ 15625 * c ^ 3 := by
      have : (7 * k) ^ 3 ≤ (25 * c) ^ 3 :=
        pow_le_pow_left₀ (by nlinarith) hle 3
      have e1 : (7 * k) ^ 3 = 343 * k ^ 3 := by ring
      have e2 : (25 * c) ^ 3 = 15625 * c ^ 3 := by ring
      linarith
    have hmid : 343 * (108 * k * c ^ 2) ≤ 132300 * c ^ 3 := by
      -- 343 * 108 = 37044, 37044 k c² ≤ 37044 * (25/7) c³ = 5292 * 25 c³ = 132300 c³
      have : 7 * (37044 * k * c ^ 2) ≤ 37044 * 25 * c ^ 3 := by
        have : 7 * k * 37044 * c ^ 2 ≤ 25 * c * 37044 * c ^ 2 := by
          nlinarith
        convert this using 1 <;> ring
      have : 37044 * k * c ^ 2 ≤ 132300 * c ^ 3 := by
        have hpos : (0 : ℤ) < 7 := by decide
        have := this
        -- 7 * X ≤ 7 * 132300 c³  ⇒ X ≤ 132300 c³
        have : 7 * (37044 * k * c ^ 2) ≤ 7 * (132300 * c ^ 3) := by
          convert this using 1 <;> ring
        exact Int.le_of_mul_le_mul_left this hpos
      convert this using 1 <;> ring
    have : 343 * (k * (k ^ 2 + 108 * c ^ 2)) =
        343 * k ^ 3 + 343 * (108 * k * c ^ 2) := by ring
    linarith
  have hcmp : 147925 * c ^ 3 ≤ 343 * (432 * c ^ 3 - 2) := by
    have : 343 * (432 * c ^ 3 - 2) = 148176 * c ^ 3 - 686 := by ring
    rw [this]
    have : (686 : ℤ) ≤ 251 * c ^ 3 := by
      have : (8 : ℤ) ≤ c ^ 3 := by
        have : (2 : ℤ) ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ (by omega) hc 3
        simpa using this
      nlinarith
    linarith
  have hpos : (0 : ℤ) < 343 := by decide
  have : 343 * (k * (k ^ 2 + 108 * c ^ 2)) ≤ 343 * (432 * c ^ 3 - 2) :=
    le_trans h1 hcmp
  exact Int.le_of_mul_le_mul_left this hpos

/-- If `5k ≥ 18c` and `c ≥ 1`, `k ≥ 0`, then `k(k²+108c²) ≥ 432c³ + 2`. -/
lemma window_high {k c : ℤ} (hk : 0 ≤ k) (hc : 1 ≤ c) (hge : 5 * k ≥ 18 * c) :
    k * (k ^ 2 + 108 * c ^ 2) ≥ 432 * c ^ 3 + 2 := by
  have hle : (18 : ℤ) * c ≤ 5 * k := hge
  have hk3 : (18 : ℤ) ^ 3 * c ^ 3 ≤ 5 ^ 3 * k ^ 3 := by
    have := pow_le_pow_left₀ (by nlinarith) hle 3
    have e1 : (18 * c) ^ 3 = 18 ^ 3 * c ^ 3 := by ring
    have e2 : (5 * k) ^ 3 = 5 ^ 3 * k ^ 3 := by ring
    linarith
  have hL : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) ≥
      18 ^ 3 * c ^ 3 + 5 ^ 2 * 108 * 18 * c ^ 3 := by
    have A : (5 : ℤ) ^ 3 * k ^ 3 ≥ 18 ^ 3 * c ^ 3 := by
      convert hk3 using 1 <;> ring
    have B : (5 : ℤ) ^ 3 * (108 * k * c ^ 2) ≥ 5 ^ 2 * 108 * 18 * c ^ 3 := by
      nlinarith
    have : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) =
        5 ^ 3 * k ^ 3 + 5 ^ 3 * (108 * k * c ^ 2) := by ring
    linarith
  -- 5³ = 125, 18³ = 5832, 25*108*18 = 48600
  -- left c³ coeff = 5832 + 48600 = 54432
  -- 125 * 432 = 54000, 125 * 2 = 250
  have hL' : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) ≥ 54432 * c ^ 3 := by
    have h1 : (18 : ℤ) ^ 3 + 5 ^ 2 * 108 * 18 = 54432 := by norm_num
    have : 18 ^ 3 * c ^ 3 + 5 ^ 2 * 108 * 18 * c ^ 3 = 54432 * c ^ 3 := by
      rw [← h1]; ring
    linarith
  have hR : 54432 * c ^ 3 ≥ (5 : ℤ) ^ 3 * (432 * c ^ 3 + 2) := by
    have hmul : (5 : ℤ) ^ 3 * (432 * c ^ 3 + 2) = 54000 * c ^ 3 + 250 := by
      have : (5 : ℤ) ^ 3 = 125 := by norm_num
      rw [this]; ring
    rw [hmul]
    have : (432 : ℤ) * c ^ 3 ≥ 250 := by
      have : (1 : ℤ) ≤ c ^ 3 := one_le_pow₀ hc
      nlinarith
    linarith
  have : (5 : ℤ) ^ 3 * (k * (k ^ 2 + 108 * c ^ 2)) ≥
      (5 : ℤ) ^ 3 * (432 * c ^ 3 + 2) := ge_trans hL' hR
  have hpos : (0 : ℤ) < 5 ^ 3 := by norm_num
  exact Int.le_of_mul_le_mul_left this hpos

lemma window_of_gForm_six {k c : ℤ} (hk : 0 < k) (hc : 0 < c)
    (h : gForm k (6 * c) = 1 ∨ gForm k (6 * c) = -1) :
    25 * c < 7 * k ∧ 5 * k < 18 * c := by
  have hiff := (gForm_six_eq_iff k c).mp h
  constructor
  · by_contra hle
    have hle' : 7 * k ≤ 25 * c := by omega
    have hk0 : 0 ≤ k := by omega
    by_cases hc2 : 2 ≤ c
    · have := window_low hk0 hc2 hle'
      rcases hiff with h' | h' <;> linarith
    · have hc1 : c = 1 := by omega
      subst hc1
      have hk3 : k ≤ 3 := by omega
      have hk1 : 1 ≤ k := by omega
      have hkcases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      have h6 : (6 * 1 : ℤ) = 6 := by norm_num
      rw [h6] at h
      have hg1 : gForm 1 6 = -323 := by simp [gForm]
      have hg2 : gForm 2 6 = -208 := by simp [gForm]
      have hg3 : gForm 3 6 = -81 := by simp [gForm]
      rcases hkcases with rfl | rfl | rfl
      · rw [hg1] at h; omega
      · rw [hg2] at h; omega
      · rw [hg3] at h; omega
  · by_contra hge
    have hge' : 5 * k ≥ 18 * c := by omega
    have hk0 : 0 ≤ k := by omega
    have hc1 : 1 ≤ c := by omega
    have := window_high hk0 hc1 hge'
    rcases hiff with h' | h' <;> linarith

end Zsqrt2
