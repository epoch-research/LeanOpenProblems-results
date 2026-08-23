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


end Zsqrt2
