import FormalConjectures.Util.ProblemImports

open Nat Finset

def IsS (m : ℕ) : Prop := ∃ x y : ℕ, x ^ 2 + 2 * y ^ 2 = m

local notation "ℤ√-2" => Zsqrtd (-2)

lemma Zsqrtd.norm_neg_two (z : ℤ√-2) : z.norm = z.re ^ 2 + 2 * z.im ^ 2 := by
  simp [Zsqrtd.norm]
  ring

lemma Zsqrtd.norm_neg_two_nonneg (z : ℤ√-2) : 0 ≤ z.norm := by
  rw [Zsqrtd.norm_neg_two]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

lemma Zsqrtd.norm_neg_two_eq_zero_iff {z : ℤ√-2} : z.norm = 0 ↔ z = 0 := by
  rw [Zsqrtd.norm_neg_two]
  constructor
  · intro h
    have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
    ext <;> simp [hre, him]
  · intro h; simp [h]

lemma IsS_iff_norm {m : ℕ} : IsS m ↔ ∃ z : ℤ√-2, z.norm.natAbs = m := by
  constructor
  · rintro ⟨x, y, hx⟩
    refine ⟨⟨x, y⟩, ?_⟩
    have hn : (⟨x, y⟩ : ℤ√-2).norm = (x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2 :=
      Zsqrtd.norm_neg_two _
    apply Int.natAbs_eq_iff.mpr
    left
    rw [hn]
    exact_mod_cast hx
  · rintro ⟨z, hz⟩
    refine ⟨z.re.natAbs, z.im.natAbs, ?_⟩
    apply Int.ofNat_inj.mp
    have hn : z.norm = z.re ^ 2 + 2 * z.im ^ 2 := Zsqrtd.norm_neg_two z
    have hnn : 0 ≤ z.norm := Zsqrtd.norm_neg_two_nonneg z
    have hz' : z.norm = (m : ℤ) := by
      have h1 : (z.norm.natAbs : ℤ) = m := by exact_mod_cast hz
      have h2 : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg hnn
      linarith
    push_cast
    rw [sq_abs, sq_abs, ← hn, hz']

noncomputable instance : Div ℤ√-2 :=
  ⟨fun x y =>
    let n := (y.norm : ℚ)
    let c := star y
    ⟨round ((x * c).re / n), round ((x * c).im / n)⟩⟩

lemma Zsqrtd.div_neg_two_def (x y : ℤ√-2) :
    x / y = ⟨round (((x * star y).re : ℚ) / y.norm),
              round (((x * star y).im : ℚ) / y.norm)⟩ :=
  rfl

noncomputable instance : Mod ℤ√-2 := ⟨fun x y => x - y * (x / y)⟩

lemma Zsqrtd.mod_neg_two_def (x y : ℤ√-2) : x % y = x - y * (x / y) := rfl

lemma abs_sub_round_le_half (x : ℚ) : |x - round x| ≤ 1 / 2 := by
  simpa using abs_sub_round x

lemma Zsqrtd.norm_intCast_neg_two (n : ℤ) : ((n : ℤ√-2).norm) = n ^ 2 := by
  simp [Zsqrtd.norm]
  ring

lemma Zsqrtd.mul_intCast_neg_two (z : ℤ√-2) (n : ℤ) :
    z * (n : ℤ√-2) = ⟨z.re * n, z.im * n⟩ := by
  ext <;> simp

lemma Zsqrtd.norm_mod_lt_neg_two (x : ℤ√-2) {y : ℤ√-2} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  set q := x / y
  set α : ℚ := ((x * star y).re : ℚ) / y.norm
  set β : ℚ := ((x * star y).im : ℚ) / y.norm
  have hq : q = ⟨round α, round β⟩ := rfl
  have hα : |α - (q.re : ℚ)| ≤ 1 / 2 := by
    rw [show (q.re : ℚ) = round α from by simp [hq]]
    exact abs_sub_round_le_half α
  have hβ : |β - (q.im : ℚ)| ≤ 1 / 2 := by
    rw [show (q.im : ℚ) = round β from by simp [hq]]
    exact abs_sub_round_le_half β
  have herr : (α - q.re) ^ 2 + 2 * (β - q.im) ^ 2 ≤ (3 / 4 : ℚ) := by
    have ea2 : (α - (q.re : ℚ)) ^ 2 ≤ (1 : ℚ) / 4 := by
      have hsq : (α - (q.re : ℚ)) ^ 2 ≤ (1 / 2 : ℚ) ^ 2 :=
        sq_le_sq' (neg_le_of_abs_le hα) (le_of_abs_le hα)
      linarith
    have eb2 : (β - (q.im : ℚ)) ^ 2 ≤ (1 : ℚ) / 4 := by
      have hsq : (β - (q.im : ℚ)) ^ 2 ≤ (1 / 2 : ℚ) ^ 2 :=
        sq_le_sq' (neg_le_of_abs_le hβ) (le_of_abs_le hβ)
      linarith
    nlinarith
  have hyposℤ : (0 : ℤ) < y.norm :=
    lt_of_le_of_ne (Zsqrtd.norm_neg_two_nonneg y)
      (fun h => hy (Zsqrtd.norm_neg_two_eq_zero_iff.mp h.symm))
  have hypos : (0 : ℚ) < y.norm := by exact_mod_cast hyposℤ
  have hprod : (x - y * q) * star y = x * star y - q * (y.norm : ℤ√-2) := by
    have := Zsqrtd.norm_eq_mul_conj y
    calc
      (x - y * q) * star y = x * star y - y * q * star y := by simp [sub_mul]
      _ = x * star y - q * (y * star y) := by
        have : y * q * star y = q * (y * star y) := by
          simp [mul_assoc, mul_left_comm]
        rw [this]
      _ = x * star y - q * (y.norm : ℤ√-2) := by rw [this]
  have hcoords :
      ((x - y * q) * star y).re = (x * star y).re - q.re * y.norm ∧
      ((x - y * q) * star y).im = (x * star y).im - q.im * y.norm := by
    rw [hprod, Zsqrtd.mul_intCast_neg_two]
    constructor <;> simp
  have hNprod : (((x - y * q) * star y).norm : ℚ) =
      (y.norm : ℚ) ^ 2 * ((α - q.re) ^ 2 + 2 * (β - q.im) ^ 2) := by
    have : ((x - y * q) * star y).norm =
        ((x - y * q) * star y).re ^ 2 + 2 * ((x - y * q) * star y).im ^ 2 :=
      Zsqrtd.norm_neg_two _
    rw [this, hcoords.1, hcoords.2]
    have hαeq : ((x * star y).re : ℚ) - q.re * y.norm = y.norm * (α - q.re) := by
      simp only [α]
      field_simp [hypos.ne']
    have hβeq : ((x * star y).im : ℚ) - q.im * y.norm = y.norm * (β - q.im) := by
      simp only [β]
      field_simp [hypos.ne']
    push_cast
    rw [hαeq, hβeq]
    ring
  have hNmul : ((x - y * q) * star y).norm = (x - y * q).norm * y.norm := by
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj]
  have hrel : ((x - y * q).norm : ℚ) =
      (y.norm : ℚ) * ((α - q.re) ^ 2 + 2 * (β - q.im) ^ 2) := by
    have h1 : (((x - y * q) * star y).norm : ℚ) =
        ((x - y * q).norm : ℚ) * (y.norm : ℚ) := by
      exact_mod_cast hNmul
    have hyne : (y.norm : ℚ) ≠ 0 := hypos.ne'
    apply mul_left_cancel₀ hyne
    linarith [h1, hNprod]
  have : ((x % y).norm : ℚ) ≤ (y.norm : ℚ) * (3 / 4) := by
    rw [Zsqrtd.mod_neg_two_def, hrel]
    nlinarith [herr, hypos]
  have : ((x % y).norm : ℚ) < (y.norm : ℚ) := by nlinarith [this, hypos]
  exact_mod_cast this

lemma Zsqrtd.natAbs_norm_mod_lt_neg_two (x : ℤ√-2) {y : ℤ√-2} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  Int.ofNat_lt.1 <| by
    have h := Zsqrtd.norm_mod_lt_neg_two x hy
    have hx : 0 ≤ (x % y).norm := Zsqrtd.norm_neg_two_nonneg _
    have hy' : 0 ≤ y.norm := Zsqrtd.norm_neg_two_nonneg _
    rw [Int.natAbs_of_nonneg hx, Int.natAbs_of_nonneg hy']
    exact h

lemma Zsqrtd.norm_le_norm_mul_left_neg_two (x : ℤ√-2) {y : ℤ√-2} (hy : y ≠ 0) :
    (x.norm).natAbs ≤ (x * y).norm.natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  refine le_mul_of_one_le_right (Nat.zero_le _) ?_
  have hypos : 0 < y.norm :=
    lt_of_le_of_ne (Zsqrtd.norm_neg_two_nonneg y)
      (fun h => hy (Zsqrtd.norm_neg_two_eq_zero_iff.mp h.symm))
  have : 1 ≤ y.norm.natAbs := by
    have : 1 ≤ y.norm := by
      have : y.norm ≠ 0 := hypos.ne'
      have : 0 ≤ y.norm := hypos.le
      omega
    exact Int.ofNat_le.mp (by
      rw [Int.natAbs_of_nonneg hypos.le]
      exact this)
  exact this

noncomputable instance : EuclideanDomain ℤ√-2 :=
  { inferInstanceAs (CommRing ℤ√-2),
    inferInstanceAs (Nontrivial ℤ√-2) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      apply Zsqrtd.ext
      · simp [Zsqrtd.div_neg_two_def]
      · simp [Zsqrtd.div_neg_two_def]
    quotient_mul_add_remainder_eq := fun _ _ => by simp [Zsqrtd.mod_neg_two_def]
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (fun z : ℤ√-2 => z.norm.natAbs)).wf
    remainder_lt := fun a b hb => Zsqrtd.natAbs_norm_mod_lt_neg_two a hb
    mul_left_not_lt := fun a b hb => not_lt_of_ge <|
      Zsqrtd.norm_le_norm_mul_left_neg_two a hb }

lemma sq_add_two_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ℤ√-2)) : IsS p := by
  have hpu : ¬IsUnit (p : ℤ√-2) :=
    mt Zsqrtd.norm_eq_one_iff.2 <| by
      rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast]
      intro h
      have hp1 := hp.out.one_lt
      nlinarith
  have hab : ∃ a b, (p : ℤ√-2) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    simpa [irreducible_iff, hpu, not_forall, not_or] using hpi
  obtain ⟨a, b, hpab, hau, hbu⟩ := hab
  have hnap : a.norm.natAbs = p :=
    ((hp.1.mul_eq_prime_sq_iff (mt Zsqrtd.norm_eq_one_iff.1 hau)
        (mt Zsqrtd.norm_eq_one_iff.1 hbu)).1 <| by
      rw [← Int.natCast_inj, Int.natCast_pow, sq, ← @Zsqrtd.norm_natCast (-2), hpab]
      simp [Zsqrtd.norm_mul]).1
  exact IsS_iff_norm.2 ⟨a, hnap⟩

lemma Zsqrtd.norm_mk_k_one (k : ℕ) :
    (Zsqrtd.norm (⟨k, 1⟩ : ℤ√-2)).natAbs = k * k + 2 := by
  rw [Zsqrtd.norm_neg_two]
  simp
  ring_nf
  rw [Int.natAbs_eq_iff]
  left
  push_cast
  ring

lemma Zsqrtd.norm_mk_k_neg_one (k : ℕ) :
    (Zsqrtd.norm (⟨k, -1⟩ : ℤ√-2)).natAbs = k * k + 2 := by
  rw [Zsqrtd.norm_neg_two]
  simp
  ring_nf
  rw [Int.natAbs_eq_iff]
  left
  push_cast
  ring

lemma Zsqrtd.norm_natCast_natAbs (p : ℕ) :
    (Zsqrtd.norm (p : ℤ√-2)).natAbs = p * p := by
  rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast]

lemma not_irreducible_of_mod_eight {p : ℕ} [hp : Fact p.Prime]
    (h : p % 8 = 1 ∨ p % 8 = 3) : ¬Irreducible (p : ℤ√-2) := by
  intro hpi
  have hprime : Prime (p : ℤ√-2) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.1 hpi
  have hp2 : p ≠ 2 := by
    intro hp2
    subst hp2
    simp at h
  have : IsSquare (-2 : ZMod p) := (ZMod.exists_sq_eq_neg_two_iff hp2).2 h
  obtain ⟨k, hk⟩ := this
  obtain ⟨k, k_lt_p, rfl⟩ : ∃ (k' : ℕ) (_ : k' < p), (k' : ZMod p) = k :=
    ⟨k.val, k.val_lt, ZMod.natCast_zmod_val k⟩
  have hpk : p ∣ k ^ 2 + 2 := by
    rw [pow_two, ← CharP.cast_eq_zero_iff (ZMod p) p, Nat.cast_add, Nat.cast_mul,
      Nat.cast_two, ← hk, neg_add_cancel]
  have hkmul : (k ^ 2 + 2 : ℤ√-2) = ⟨k, 1⟩ * ⟨k, -1⟩ := by
    ext <;> simp [sq]
  have hk₀ : k ≠ 0 := by
    rintro rfl
    have hneg : (-2 : ZMod p) = 0 := by simpa using hk
    have h2 : (2 : ZMod p) = 0 := neg_eq_zero.mp hneg
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
    exact hp2 this
  have hkltp : k * k + 2 < p * p := by
    have hk1 : k ≤ p - 1 := Nat.le_pred_of_lt k_lt_p
    have hp2le : 2 ≤ p := hp.out.two_le
    have hle : k * k + 2 ≤ (p - 1) * (p - 1) + 2 := by
      nlinarith
    have hlt : (p - 1) * (p - 1) + 2 < p * p := by
      have : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      nlinarith
    omega
  have hpk₁ : ¬(p : ℤ√-2) ∣ ⟨k, -1⟩ := by
    rintro ⟨x, hx⟩
    apply lt_irrefl (Zsqrtd.norm ((p : ℤ√-2) * x)).natAbs
    calc
      (Zsqrtd.norm ((p : ℤ√-2) * x)).natAbs = (Zsqrtd.norm (⟨k, -1⟩ : ℤ√-2)).natAbs := by rw [hx]
      _ = k * k + 2 := Zsqrtd.norm_mk_k_neg_one k
      _ < p * p := hkltp
      _ = (Zsqrtd.norm (p : ℤ√-2)).natAbs := (Zsqrtd.norm_natCast_natAbs p).symm
      _ ≤ (Zsqrtd.norm ((p : ℤ√-2) * x)).natAbs :=
        Zsqrtd.norm_le_norm_mul_left_neg_two _ (by
          intro hx0
          have : (-1 : ℤ) = 0 := by
            simpa [hx0] using congr_arg Zsqrtd.im hx
          exact (by decide : (-1 : ℤ) ≠ 0) this)
  have hpk₂ : ¬(p : ℤ√-2) ∣ ⟨k, 1⟩ := by
    rintro ⟨x, hx⟩
    apply lt_irrefl (Zsqrtd.norm ((p : ℤ√-2) * x)).natAbs
    calc
      (Zsqrtd.norm ((p : ℤ√-2) * x)).natAbs = (Zsqrtd.norm (⟨k, 1⟩ : ℤ√-2)).natAbs := by rw [hx]
      _ = k * k + 2 := Zsqrtd.norm_mk_k_one k
      _ < p * p := hkltp
      _ = (Zsqrtd.norm (p : ℤ√-2)).natAbs := (Zsqrtd.norm_natCast_natAbs p).symm
      _ ≤ (Zsqrtd.norm ((p : ℤ√-2) * x)).natAbs :=
        Zsqrtd.norm_le_norm_mul_left_neg_two _ (by
          intro hx0
          have : (1 : ℤ) = 0 := by
            simpa [hx0] using congr_arg Zsqrtd.im hx
          exact (by decide : (1 : ℤ) ≠ 0) this)
  obtain ⟨y, hy⟩ := hpk
  have hdiv : (p : ℤ√-2) ∣ ⟨k, 1⟩ * ⟨k, -1⟩ := by
    refine ⟨(y : ℤ√-2), ?_⟩
    have : ((k ^ 2 + 2 : ℕ) : ℤ√-2) = ⟨k, 1⟩ * ⟨k, -1⟩ := by
      trans ((k : ℤ) ^ 2 + 2 : ℤ√-2)
      · simp [sq]
      · exact hkmul
    rw [← this, hy]
    simp
  have := hprime.dvd_or_dvd hdiv
  tauto

lemma prime_isS_of_mod_eight {p : ℕ} [hp : Fact p.Prime]
    (h : p % 8 = 1 ∨ p % 8 = 3) : IsS p :=
  sq_add_two_sq_of_nat_prime_of_not_irreducible p (not_irreducible_of_mod_eight h)

lemma sq_add_two_sq_mul (x y u v : ℤ) :
    (x * u - 2 * y * v) ^ 2 + 2 * (x * v + y * u) ^ 2 =
      (x ^ 2 + 2 * y ^ 2) * (u ^ 2 + 2 * v ^ 2) := by ring

lemma IsS.mul {m n : ℕ} (hm : IsS m) (hn : IsS n) : IsS (m * n) := by
  obtain ⟨x, y, hx⟩ := hm
  obtain ⟨u, v, hu⟩ := hn
  set A : ℤ := (x : ℤ) * u - 2 * y * v
  set B : ℤ := (x : ℤ) * v + y * u
  have hid : A ^ 2 + 2 * B ^ 2 = (x ^ 2 + 2 * y ^ 2) * (u ^ 2 + 2 * v ^ 2) := by
    simpa [A, B] using sq_add_two_sq_mul x y u v
  refine ⟨A.natAbs, B.natAbs, ?_⟩
  apply Int.ofNat_inj.mp
  push_cast
  rw [sq_abs, sq_abs, hid]
  rw [show ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) = m by exact_mod_cast hx]
  rw [show ((u : ℤ) ^ 2 + 2 * (v : ℤ) ^ 2) = n by exact_mod_cast hu]

lemma IsS.one : IsS 1 := ⟨1, 0, by simp⟩
lemma IsS.two : IsS 2 := ⟨0, 1, by simp⟩
lemma IsS.zero : IsS 0 := ⟨0, 0, by simp⟩

/-- An inert prime dividing `x^2 + 2y^2` must divide both `x` and `y`. -/
lemma inert_prime_dvd_of_IsS {p x y : ℕ} [hp : Fact p.Prime]
    (hinert : p % 8 = 5 ∨ p % 8 = 7) (hdiv : (p : ℤ) ∣ (x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) :
    p ∣ x ∧ p ∣ y := by
  have hp2 : p ≠ 2 := by
    intro h; subst h; simp at hinert
  have hns : ¬IsSquare (-2 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_two_iff hp2]
    intro h13
    rcases hinert with h5 | h7 <;> rcases h13 with h1 | h3 <;> omega
  have hmod : ((x : ZMod p) ^ 2 + 2 * (y : ZMod p) ^ 2) = 0 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd ((x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2) p).mpr hdiv
    simpa [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using hz
  by_cases hy0 : (y : ZMod p) = 0
  · have hx0 : (x : ZMod p) = 0 := by
      have : (x : ZMod p) ^ 2 = 0 := by
        rw [hy0] at hmod
        simpa using hmod
      exact pow_eq_zero this
    constructor
    · exact (ZMod.natCast_eq_zero_iff x p).mp hx0
    · exact (ZMod.natCast_eq_zero_iff y p).mp hy0
  · exfalso
    have : (x : ZMod p) ^ 2 = -2 * (y : ZMod p) ^ 2 := by
      linear_combination hmod
    have hyi : IsUnit (y : ZMod p) :=
      isUnit_iff_ne_zero.mpr hy0
    have : ((x : ZMod p) * (y : ZMod p)⁻¹) ^ 2 = -2 := by
      field_simp [hy0] at this ⊢
      linear_combination this
    rw [pow_two] at this
    exact hns ⟨_, this.symm⟩

lemma not_IsS_of_inert_prime {p : ℕ} [hp : Fact p.Prime]
    (hinert : p % 8 = 5 ∨ p % 8 = 7) : ¬IsS p := by
  rintro ⟨x, y, hxy⟩
  have hdiv : (p : ℤ) ∣ (x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2 := by
    have : (x : ℤ) ^ 2 + 2 * (y : ℤ) ^ 2 = p := by exact_mod_cast hxy
    rw [this]
  obtain ⟨hx, hy⟩ := inert_prime_dvd_of_IsS hinert hdiv
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  subst hx' hy'
  have : p * p ∣ p := by
    have : (p * x') ^ 2 + 2 * (p * y') ^ 2 = p := hxy
    have : p * p * (x' ^ 2 + 2 * y' ^ 2) = p := by
      convert this using 1
      ring
    exact ⟨x' ^ 2 + 2 * y' ^ 2, this.symm⟩
  have := Nat.le_of_dvd hp.out.pos this
  have hp2 := hp.out.two_le
  nlinarith

lemma IsS.mul_sq {n k : ℕ} (h : IsS n) : IsS (k ^ 2 * n) := by
  have hk : IsS (k ^ 2) := ⟨k, 0, by simp⟩
  exact hk.mul h

lemma IsS.of_inert_dvd {q m : ℕ} [hq : Fact q.Prime]
    (hinert : q % 8 = 5 ∨ q % 8 = 7) (hS : IsS m) (hdvd : q ∣ m) :
    q ^ 2 ∣ m ∧ IsS (m / q ^ 2) := by
  obtain ⟨a, b, hab⟩ := hS
  have hdiv : (q : ℤ) ∣ (a : ℤ) ^ 2 + 2 * (b : ℤ) ^ 2 := by
    have : (a : ℤ) ^ 2 + 2 * (b : ℤ) ^ 2 = m := by exact_mod_cast hab
    rw [this]
    exact_mod_cast hdvd
  obtain ⟨ha, hb⟩ := inert_prime_dvd_of_IsS hinert hdiv
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hmul : m = q ^ 2 * (a' ^ 2 + 2 * b' ^ 2) := by
    rw [← hab]; ring
  constructor
  · exact ⟨a' ^ 2 + 2 * b' ^ 2, hmul⟩
  · refine ⟨a', b', ?_⟩
    rw [hmul, Nat.mul_div_cancel_left _ (pow_pos hq.out.pos 2)]

lemma IsS.even_padicValNat_of_inert {n q : ℕ} [hq : Fact q.Prime]
    (hinert : q % 8 = 5 ∨ q % 8 = 7) (hS : IsS n) :
    Even (padicValNat q n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases n.eq_zero_or_pos with rfl | hpos
    · simp [padicValNat.zero]
    by_cases hqd : q ∣ n
    · obtain ⟨hd2, hS'⟩ := IsS.of_inert_dvd hinert hS hqd
      have hlt : n / q ^ 2 < n :=
        Nat.div_lt_self hpos (by
          have : 1 < q ^ 2 := by
            have := hq.out.two_le
            nlinarith
          exact this)
      have hne : n / q ^ 2 ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hpos hd2) (pow_pos hq.out.pos 2)).ne'
      have hval : padicValNat q n =
          padicValNat q (q ^ 2) + padicValNat q (n / q ^ 2) := by
        have heq : q ^ 2 * (n / q ^ 2) = n := Nat.mul_div_cancel' hd2
        conv_lhs => rw [← heq]
        exact padicValNat.mul (pow_ne_zero 2 (Nat.Prime.ne_zero (Fact.elim hq))) hne
      have hpow : padicValNat q (q ^ 2) = 2 := by
        rw [padicValNat.pow 2 (Nat.Prime.ne_zero (Fact.elim hq)), padicValNat_self]
      rw [hval, hpow]
      exact even_two.add (ih _ hlt hS')
    · rw [padicValNat.eq_zero_of_not_dvd hqd]
      exact Even.zero

lemma IsS_of_primes {n : ℕ} (h : ∀ q ∈ n.primeFactors, q = 2 ∨ q % 8 = 1 ∨ q % 8 = 3) :
    IsS n := by
  induction n using induction_on_primes with
  | zero => exact IsS.zero
  | one => exact IsS.one
  | prime_mul p n hp ih =>
    have : Fact p.Prime := ⟨hp⟩
    by_cases h0 : p * n = 0
    · have : n = 0 := by simp [hp.ne_zero] at h0; exact h0
      subst this
      exact IsS.zero
    have hpS : IsS p := by
      have hp8 : p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3 := by
        apply h
        exact Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right _ _, h0⟩
      rcases hp8 with hp2 | hp13
      · subst hp2; exact IsS.two
      · exact prime_isS_of_mod_eight hp13
    have hnS : IsS n := by
      apply ih
      intro q hq
      apply h
      have hq' := Nat.prime_of_mem_primeFactors hq
      have hn0 : n ≠ 0 := by
        intro hn0; subst hn0; exact h0 (mul_zero _)
      exact Nat.mem_primeFactors.mpr ⟨hq',
        dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hq) _, h0⟩
    exact hpS.mul hnS

/-- Characterization of numbers represented by `x^2 + 2y^2`. -/
lemma IsS_iff {n : ℕ} :
    IsS n ↔ ∀ q ∈ n.primeFactors, q % 8 = 5 ∨ q % 8 = 7 → Even (padicValNat q n) := by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · exact ⟨fun _ q _ _ => padicValNat.zero.symm ▸ Even.zero, fun _ => IsS.zero⟩
  constructor
  · intro hS q hq hqin
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hq⟩
    exact IsS.even_padicValNat_of_inert hqin hS
  · intro H
    obtain ⟨b, a, hb0, ha0, hab, hb⟩ := Nat.sq_mul_squarefree_of_pos hn0
    have hbS : IsS b := by
      apply IsS_of_primes
      intro q hq
      have hqP := Nat.prime_of_mem_primeFactors hq
      have : Fact q.Prime := ⟨hqP⟩
      have hqb : q ∣ b := Nat.dvd_of_mem_primeFactors hq
      have hqn : q ∣ n := by
        rw [eq_comm] at hab
        exact dvd_trans hqb ⟨a ^ 2, by rw [hab, mul_comm]⟩
      have hqin_n : q ∈ n.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqP, hqn, hn0.ne'⟩
      by_contra hnot
      have hinert : q % 8 = 5 ∨ q % 8 = 7 := by
        have : q % 8 = 0 ∨ q % 8 = 1 ∨ q % 8 = 2 ∨ q % 8 = 3 ∨
               q % 8 = 4 ∨ q % 8 = 5 ∨ q % 8 = 6 ∨ q % 8 = 7 := by omega
        -- q is an odd prime (not 2, else the conclusion holds)
        have hq2 : q ≠ 2 := by
          intro hq2; subst hq2; simp at hnot
        have : q % 2 = 1 := (Nat.Prime.eq_two_or_odd hqP).resolve_left hq2
        omega
      have heven : Even (padicValNat q n) := H q hqin_n hinert
      have hvalb : padicValNat q b = 1 := by
        have hle : b.factorization q ≤ 1 := hb.natFactorization_le_one q
        have hfac : b.factorization q = padicValNat q b :=
          Nat.factorization_def b hqP
        have hpos : 1 ≤ padicValNat q b :=
          one_le_padicValNat_of_dvd hb0.ne' hqb
        omega
      have hval : padicValNat q n = padicValNat q (a ^ 2) + padicValNat q b := by
        rw [← hab]
        exact padicValNat.mul (pow_ne_zero 2 ha0.ne') hb0.ne'
      have hevena : Even (padicValNat q (a ^ 2)) := by
        rw [padicValNat.pow 2 ha0.ne']
        exact even_two.mul_right _
      have hevenb : Even (padicValNat q b) := by
        have : Even (padicValNat q (a ^ 2)) ↔ Even (padicValNat q b) :=
          Nat.even_add.mp (hval ▸ heven)
        exact this.mp hevena
      rw [hvalb] at hevenb
      exact Nat.not_even_one hevenb
    have : n = a ^ 2 * b := hab.symm
    rw [this]
    exact IsS.mul_sq hbS

