import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352627: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$,
where $a, b, c, d$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R)) -- Represents a set of $\mathbb{N}^4$ tuples

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

/- Auxiliary form and basic comparisons -/

/-- The binary quartic appearing in the representation. -/
def g (c d : ℕ) : ℕ := c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2

lemma g_def (c d : ℕ) : g c d = c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 := rfl

lemma g_mul_16 (c d : ℕ) : g (2 * c) (2 * d) = 16 * g c d := by
  simp [g]
  ring

/-- The full quaternary mixed form. -/
def F (x y c d : ℕ) : ℕ := x ^ 2 + 2 * y ^ 2 + g c d

lemma F_def (x y c d : ℕ) :
    F x y c d = x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 := by
  simp [F, g]; ring

lemma F_mul_16 (x y c d : ℕ) :
    F (4 * x) (4 * y) (2 * c) (2 * d) = 16 * F x y c d := by
  simp [F, g_mul_16]
  ring

lemma le_sqrt_of_pow_two_le {k n : ℕ} (h : k ^ 2 ≤ n) : k ≤ sqrt n :=
  Nat.le_sqrt'.mpr h

lemma mem_range_succ_sqrt {k n : ℕ} (h : k ≤ sqrt n) : k ∈ range (sqrt n + 1) := by
  simp [mem_range]
  omega

lemma exists_imp_a_pos {n x y c d : ℕ}
    (h : x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n) :
    0 < a n := by
  have hx : x ≤ sqrt n := le_sqrt_of_pow_two_le (by omega)
  have hy : y ≤ sqrt n := by
    have h1 : 2 * y ^ 2 ≤ n := by omega
    have h2 : y ^ 2 ≤ 2 * y ^ 2 := Nat.le_mul_of_pos_left _ (by decide)
    exact le_sqrt_of_pow_two_le (le_trans h2 h1)
  have hc2 : c ^ 2 ≤ n := by
    cases c with
    | zero => simp
    | succ c =>
      have : (c + 1) ^ 2 ≤ (c + 1) ^ 4 := by
        rw [show (c + 1) ^ 4 = (c + 1) ^ 2 * (c + 1) ^ 2 from by ring]
        exact Nat.le_mul_of_pos_right _ (by simp)
      omega
  have hc : c ≤ sqrt n := le_sqrt_of_pow_two_le hc2
  have hd2 : d ^ 2 ≤ n := by
    cases d with
    | zero => simp
    | succ d =>
      have hle : (d + 1) ^ 2 ≤ 4 * (d + 1) ^ 4 := by
        have : (d + 1) ^ 2 ≤ (d + 1) ^ 4 := by
          rw [show (d + 1) ^ 4 = (d + 1) ^ 2 * (d + 1) ^ 2 from by ring]
          exact Nat.le_mul_of_pos_right _ (by simp)
        have : (d + 1) ^ 4 ≤ 4 * (d + 1) ^ 4 := Nat.le_mul_of_pos_left _ (by decide)
        exact le_trans ‹(d + 1) ^ 2 ≤ (d + 1) ^ 4› this
      omega
  have hd : d ≤ sqrt n := le_sqrt_of_pow_two_le hd2
  set R := range (sqrt n + 1)
  set S := R.product (R.product (R.product R))
  have hp : (x, (y, (c, d))) ∈ S := by
    simp [S, R, mem_product, mem_range_succ_sqrt hx, mem_range_succ_sqrt hy,
      mem_range_succ_sqrt hc, mem_range_succ_sqrt hd]
  have hpred : (fun p : ℕ × ℕ × ℕ × ℕ =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n) (x, (y, (c, d))) := h
  have hmem : (x, (y, (c, d))) ∈ S.filter (fun p =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n) :=
    mem_filter.mpr ⟨hp, hpred⟩
  have hcard : 0 < (S.filter (fun p =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n)).card :=
    card_pos.mpr ⟨_, hmem⟩
  simpa [a, R, S] using hcard

lemma a_pos_of_F {n x y c d : ℕ} (h : F x y c d = n) : 0 < a n := by
  rw [F_def] at h
  exact exists_imp_a_pos h

lemma exists_rep_mul_16 {x y c d : ℕ} :
    F (4 * x) (4 * y) (2 * c) (2 * d) = 16 * F x y c d :=
  F_mul_16 x y c d

/- Numbers of the form `x ^ 2 + 2 y ^ 2` -/

/-- `m` is represented by the principal form of discriminant `-8`. -/
def IsS (m : ℕ) : Prop := ∃ x y : ℕ, x ^ 2 + 2 * y ^ 2 = m

lemma IsS.zero : IsS 0 := ⟨0, 0, by simp⟩
lemma IsS.one : IsS 1 := ⟨1, 0, by simp⟩
lemma IsS.two : IsS 2 := ⟨0, 1, by simp⟩
lemma IsS.three : IsS 3 := ⟨1, 1, by simp⟩
lemma IsS.four : IsS 4 := ⟨2, 0, by simp⟩
lemma IsS.six : IsS 6 := ⟨2, 1, by simp⟩
lemma IsS.eight : IsS 8 := ⟨0, 2, by simp⟩
lemma IsS.nine : IsS 9 := ⟨3, 0, by simp⟩

lemma IsS.of_F_zero {x y : ℕ} : IsS (x ^ 2 + 2 * y ^ 2) := ⟨x, y, rfl⟩

lemma exists_rep_of_IsS {n : ℕ} (h : IsS n) : ∃ x y c d, F x y c d = n := by
  obtain ⟨x, y, hx⟩ := h
  refine ⟨x, y, 0, 0, ?_⟩
  simp [F, g, hx]

lemma a_pos_of_IsS {n : ℕ} (h : IsS n) : 0 < a n := by
  obtain ⟨x, y, c, d, H⟩ := exists_rep_of_IsS h
  exact a_pos_of_F H

lemma a_pos_of_IsS_add_g {n c d : ℕ} (h : IsS (n - g c d)) (hle : g c d ≤ n) :
    0 < a n := by
  obtain ⟨x, y, hx⟩ := h
  apply a_pos_of_F (x := x) (y := y) (c := c) (d := d)
  simp [F]
  omega

/-- Brahmagupta–Fibonacci identity for the form `x^2 + 2y^2`. -/
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


/- Euclidean structure on ℤ√-2 -/

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
    have hnn : 0 ≤ (⟨x, y⟩ : ℤ√-2).norm := Zsqrtd.norm_neg_two_nonneg _
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

/-- Division in ℤ√-2 by rounding coordinates of `x * star y / ‖y‖`. -/
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
  -- (x - y*q) * star y = x * star y - q * N(y)
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
      exact eq_zero_of_pow_eq_zero this
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

/-- An odd prime is `2` or `1,3,5,7 mod 8`. -/
lemma Prime.mod_eight_odd {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) :
    q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
  have hodd : q % 2 = 1 := (Nat.Prime.eq_two_or_odd hq).resolve_left h2
  have : q % 8 < 8 := Nat.mod_lt q (by decide)
  omega

/-- Split primes (including `2`) never obstruct `IsS`. -/
lemma Prime.split_or_two {q : ℕ} (hq : q.Prime)
    (hnot : ¬ (q % 8 = 5 ∨ q % 8 = 7)) :
    q = 2 ∨ q % 8 = 1 ∨ q % 8 = 3 := by
  by_cases h2 : q = 2
  · exact Or.inl h2
  · have := Prime.mod_eight_odd hq h2
    omega

/-- Product of an inert residue and a `1,3 mod 8` residue is `5` or `7 mod 8`. -/
lemma inert_mul_split_mod8 {a b : ℕ}
    (ha : a % 8 = 5 ∨ a % 8 = 7) (hb : b % 8 = 1 ∨ b % 8 = 3) :
    a * b % 8 = 5 ∨ a * b % 8 = 7 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.mul_mod, ha, hb]

lemma odd_sq_mod8 {a : ℕ} (h : a % 2 = 1) : a ^ 2 % 8 = 1 := by
  have : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by omega
  rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]

/-- Split-prime residues are closed under multiplication. -/
lemma split_mul_mod8 {a b : ℕ}
    (ha : a % 8 = 1 ∨ a % 8 = 3) (hb : b % 8 = 1 ∨ b % 8 = 3) :
    a * b % 8 = 1 ∨ a * b % 8 = 3 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [Nat.mul_mod, ha, hb]

/-- If `m ≡ 1` or `3` (mod `8`) and `m < 35`, then `m` is `IsS`. -/
lemma IsS_of_mod8_lt_35 {m : ℕ} (h8 : m % 8 = 1 ∨ m % 8 = 3) (hm : m < 35) :
    IsS m := by
  have : m = 1 ∨ m = 3 ∨ m = 9 ∨ m = 11 ∨ m = 17 ∨ m = 19 ∨
      m = 25 ∨ m = 27 ∨ m = 33 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact IsS.one
  · exact IsS.three
  · exact ⟨3, 0, by norm_num⟩
  · exact ⟨3, 1, by norm_num⟩
  · exact ⟨3, 2, by norm_num⟩
  · exact ⟨1, 3, by norm_num⟩
  · exact ⟨5, 0, by norm_num⟩
  · exact ⟨3, 3, by norm_num⟩
  · exact ⟨1, 4, by norm_num⟩

lemma odd_of_mod8_one_three {m : ℕ} (h : m % 8 = 1 ∨ m % 8 = 3) : m % 2 = 1 := by
  omega

/-- An odd `IsS` number is `1` or `3` mod `8`. -/
lemma IsS.odd_mod8 {m : ℕ} (h : IsS m) (hodd : m % 2 = 1) :
    m % 8 = 1 ∨ m % 8 = 3 := by
  obtain ⟨x, y, hxy⟩ := h
  have hxodd : x % 2 = 1 := by
    have hsum : (x ^ 2 + 2 * y ^ 2) % 2 = 1 := by rw [hxy]; exact hodd
    by_contra hx
    have hx0 : x % 2 = 0 := by omega
    have : (x ^ 2 + 2 * y ^ 2) % 2 = 0 := by
      have hx2 : x ^ 2 % 2 = 0 := by simp [Nat.pow_mod, hx0]
      omega
    omega
  have hx8 : x ^ 2 % 8 = 1 := odd_sq_mod8 hxodd
  have hy8 : 2 * y ^ 2 % 8 = 0 ∨ 2 * y ^ 2 % 8 = 2 := by
    by_cases hy : Even y
    · obtain ⟨z, hz⟩ := hy
      have h2 : y = 2 * z := by simpa [two_mul] using hz
      subst h2
      have heq : 2 * (2 * z) ^ 2 = 8 * z ^ 2 := by ring
      have h0 : 2 * (2 * z) ^ 2 % 8 = 0 := by
        rw [heq, Nat.mul_mod]; simp
      exact Or.inl h0
    · have hy1 : y % 2 = 1 := Nat.not_even_iff.mp hy
      have hy2 : y ^ 2 % 8 = 1 := odd_sq_mod8 hy1
      have : 2 * y ^ 2 % 8 = 2 := by simp [Nat.mul_mod, hy2]
      exact Or.inr this
  have hm8 : m % 8 = (x ^ 2 + 2 * y ^ 2) % 8 := by rw [hxy]
  rw [Nat.add_mod, hx8] at hm8
  rcases hy8 with hy8 | hy8 <;> simp [hy8] at hm8 <;> omega

/-- Squarefree kernel of a `1,3 mod 8` number is itself `1,3 mod 8`. -/
lemma squarefree_kernel_mod8 {m a b : ℕ} (hab : m = a ^ 2 * b)
    (h8 : m % 8 = 1 ∨ m % 8 = 3) : b % 8 = 1 ∨ b % 8 = 3 := by
  have hm_odd : m % 2 = 1 := odd_of_mod8_one_three h8
  have ha_odd : a % 2 = 1 := by
    have hmul2 : (a ^ 2 * b) % 2 = 1 := by rw [← hab]; exact hm_odd
    by_contra hae
    have ha0 : a % 2 = 0 := by omega
    have : (a ^ 2 * b) % 2 = 0 := by simp [Nat.mul_mod, Nat.pow_mod, ha0]
    omega
  have ha2 : a ^ 2 % 8 = 1 := odd_sq_mod8 ha_odd
  have hmul : m % 8 = (a ^ 2 * b) % 8 := by rw [hab]
  rw [Nat.mul_mod, ha2, Nat.one_mul, Nat.mod_mod] at hmul
  omega

/-- An inert prime is `5`, `7`, or at least `13`. -/
lemma inert_prime_ge {p : ℕ} (hp : p.Prime) (hin : p % 8 = 5 ∨ p % 8 = 7) :
    p = 5 ∨ p = 7 ∨ 13 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  by_cases h13 : 13 ≤ p
  · exact Or.inr (Or.inr h13)
  · have : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨
        p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 11 ∨ p = 12 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases hin <;> omega
    · cases hin <;> omega
    · exact absurd hp (by decide : ¬ Nat.Prime 4)
    · exact Or.inl rfl
    · exact absurd hp (by decide : ¬ Nat.Prime 6)
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by decide : ¬ Nat.Prime 8)
    · exact absurd hp (by decide : ¬ Nat.Prime 9)
    · exact absurd hp (by decide : ¬ Nat.Prime 10)
    · cases hin <;> omega
    · exact absurd hp (by decide : ¬ Nat.Prime 12)

/-- An inert prime other than `5` and `7` is `13` or at least `23`. -/
lemma inert_prime_ge_13 {p : ℕ} (hp : p.Prime) (hin : p % 8 = 5 ∨ p % 8 = 7)
    (h5 : p ≠ 5) (h7 : p ≠ 7) : p = 13 ∨ 23 ≤ p := by
  have hge := inert_prime_ge hp hin
  have h13le : 13 ≤ p := by omega
  by_cases h23 : 23 ≤ p
  · exact Or.inr h23
  · have : p = 13 ∨ p = 14 ∨ p = 15 ∨ p = 16 ∨ p = 17 ∨ p = 18 ∨
        p = 19 ∨ p = 20 ∨ p = 21 ∨ p = 22 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hp (by decide : ¬ Nat.Prime 14)
    · exact absurd hp (by decide : ¬ Nat.Prime 15)
    · exact absurd hp (by decide : ¬ Nat.Prime 16)
    · cases hin <;> omega
    · exact absurd hp (by decide : ¬ Nat.Prime 18)
    · cases hin <;> omega
    · exact absurd hp (by decide : ¬ Nat.Prime 20)
    · exact absurd hp (by decide : ¬ Nat.Prime 21)
    · exact absurd hp (by decide : ¬ Nat.Prime 22)

/-- Product of two distinct inerts other than `5,7` is at least `13 * 23`. -/
lemma two_inerts_mul_ge_299 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpin : p % 8 = 5 ∨ p % 8 = 7) (hqin : q % 8 = 5 ∨ q % 8 = 7)
    (hp5 : p ≠ 5) (hp7 : p ≠ 7) (hq5 : q ≠ 5) (hq7 : q ≠ 7) :
    13 * 23 ≤ p * q := by
  have hp' := inert_prime_ge_13 hp hpin hp5 hp7
  have hq' := inert_prime_ge_13 hq hqin hq5 hq7
  rcases hp' with rfl | hp23 <;> rcases hq' with rfl | hq23
  · exact (hpq rfl).elim
  · have : 13 * 23 ≤ 13 * q := Nat.mul_le_mul_left 13 hq23
    simpa using this
  · have : 13 * 23 ≤ p * 13 := by
      rw [mul_comm p]
      exact Nat.mul_le_mul_left 13 hp23
    simpa using this
  · have h1 : 23 ≤ p := hp23
    have h2 : 23 ≤ q := hq23
    calc 13 * 23 ≤ 23 * 23 := by decide
      _ ≤ p * q := Nat.mul_le_mul h1 h2

/-- A squarefree `1,3 mod 8` number that is not `IsS` has two distinct inert prime factors. -/
lemma two_inerts_of_not_IsS_squarefree {b : ℕ} (hb0 : 0 < b)
    (hsf : Squarefree b) (h8 : b % 8 = 1 ∨ b % 8 = 3) (hnot : ¬ IsS b) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      (p % 8 = 5 ∨ p % 8 = 7) ∧ (q % 8 = 5 ∨ q % 8 = 7) ∧ p ∣ b ∧ q ∣ b := by
  have hbS : ¬ ∀ r ∈ b.primeFactors, r = 2 ∨ r % 8 = 1 ∨ r % 8 = 3 := by
    intro h; exact hnot (IsS_of_primes h)
  obtain ⟨p, hpB, hpnot⟩ : ∃ p ∈ b.primeFactors, ¬ (p = 2 ∨ p % 8 = 1 ∨ p % 8 = 3) := by
    contrapose! hbS; exact hbS
  have hpP := Nat.prime_of_mem_primeFactors hpB
  have hp_in : p % 8 = 5 ∨ p % 8 = 7 := by
    have h2 : p ≠ 2 := fun hp2 => by subst hp2; simp at hpnot
    have := Prime.mod_eight_odd hpP h2
    omega
  have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hpB
  obtain ⟨s, rfl⟩ := hpb
  have hcop : Nat.Coprime p s := coprime_of_squarefree_mul hsf
  have hp_nons : ¬ p ∣ s := hpP.coprime_iff_not_dvd.mp hcop
  by_cases hother : ∃ q ∈ s.primeFactors, q % 8 = 5 ∨ q % 8 = 7
  · obtain ⟨q, hqB, hqin⟩ := hother
    have hqP := Nat.prime_of_mem_primeFactors hqB
    have hqs : q ∣ s := Nat.dvd_of_mem_primeFactors hqB
    refine ⟨p, q, hpP, hqP, ?_, hp_in, hqin, dvd_mul_right _ _, dvd_mul_of_dvd_right hqs _⟩
    intro h; subst h; exact hp_nons hqs
  · have hs_split : ∀ q ∈ s.primeFactors, q = 2 ∨ q % 8 = 1 ∨ q % 8 = 3 := by
      intro q hq
      have hqP := Nat.prime_of_mem_primeFactors hq
      exact Prime.split_or_two hqP (fun h => hother ⟨q, hq, h⟩)
    have hsS : IsS s := IsS_of_primes hs_split
    have hs_odd : s % 2 = 1 := by
      have hps2 : (p * s) % 2 = 1 := odd_of_mod8_one_three h8
      have hp_odd : p % 2 = 1 := by
        have : p ≠ 2 := fun h => by subst h; simp at hp_in
        exact (Nat.Prime.eq_two_or_odd hpP).resolve_left this
      simp [Nat.mul_mod, hp_odd] at hps2
      omega
    have hs13 : s % 8 = 1 ∨ s % 8 = 3 := hsS.odd_mod8 hs_odd
    have hprod : (p * s) % 8 = 5 ∨ (p * s) % 8 = 7 := inert_mul_split_mod8 hp_in hs13
    omega

/-- If `m ≡ 1` or `3` (mod `8`) is not `IsS`, two distinct inerts divide `m`. -/
lemma two_inerts_of_not_IsS {m : ℕ} (hm0 : 0 < m)
    (h8 : m % 8 = 1 ∨ m % 8 = 3) (hnot : ¬ IsS m) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      (p % 8 = 5 ∨ p % 8 = 7) ∧ (q % 8 = 5 ∨ q % 8 = 7) ∧ p ∣ m ∧ q ∣ m := by
  obtain ⟨b, a, hb0, ha0, hab, hsf⟩ := Nat.sq_mul_squarefree_of_pos hm0
  have hb8 : b % 8 = 1 ∨ b % 8 = 3 := squarefree_kernel_mod8 hab.symm h8
  have hnotb : ¬ IsS b := by
    intro hbS
    exact hnot (by rw [← hab]; exact IsS.mul_sq hbS)
  obtain ⟨p, q, hpP, hqP, hpq, hpin, hqin, hpb, hqb⟩ :=
    two_inerts_of_not_IsS_squarefree hb0 hsf hb8 hnotb
  have hpm : p ∣ m := by
    rw [← hab]; exact dvd_mul_of_dvd_right hpb _
  have hqm : q ∣ m := by
    rw [← hab]; exact dvd_mul_of_dvd_right hqb _
  exact ⟨p, q, hpP, hqP, hpq, hpin, hqin, hpm, hqm⟩

/-- If `m ≡ 1` or `3` (mod `8`), neither `5` nor `7` divides `m`, and `m < 299`, then `IsS m`. -/
lemma IsS_of_mod8_not_dvd_five_seven {m : ℕ}
    (h8 : m % 8 = 1 ∨ m % 8 = 3)
    (h5 : ¬ 5 ∣ m) (h7 : ¬ 7 ∣ m) (hm : m < 13 * 23) :
    IsS m := by
  by_contra hnot
  rcases eq_or_ne m 0 with rfl | hmne
  · exact hnot IsS.zero
  have hm0 : 0 < m := Nat.pos_of_ne_zero hmne
  obtain ⟨p, q, hpP, hqP, hpq, hpin, hqin, hpm, hqm⟩ :=
    two_inerts_of_not_IsS hm0 h8 hnot
  have hp5 : p ≠ 5 := fun h => by subst h; exact h5 hpm
  have hp7 : p ≠ 7 := fun h => by subst h; exact h7 hpm
  have hq5 : q ≠ 5 := fun h => by subst h; exact h5 hqm
  have hq7 : q ≠ 7 := fun h => by subst h; exact h7 hqm
  have hge : 13 * 23 ≤ p * q :=
    two_inerts_mul_ge_299 hpP hqP hpq hpin hqin hp5 hp7 hq5 hq7
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpP hqP).mpr hpq
  have hmul : p * q ∣ m := hcop.mul_dvd_of_dvd_of_dvd hpm hqm
  have hle : p * q ≤ m := Nat.le_of_dvd hm0 hmul
  exact Nat.not_le_of_gt hm (le_trans hge hle)

lemma a_pos_of_le_15 (n : ℕ) (hn : n ≤ 15) : 0 < a n := by
  interval_cases n
  · exact exists_imp_a_pos (x := 0) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 1) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 2) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 1) (c := 0) (d := 1) (by norm_num)

lemma exists_F_of_a_pos {n : ℕ} (h : 0 < a n) :
    ∃ x y c d, F x y c d = n := by
  simp only [a] at h
  set R := range (sqrt n + 1)
  set S := R.product (R.product (R.product R))
  have hpos : 0 < (S.filter (fun p =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n)).card := h
  obtain ⟨p, hp⟩ := card_pos.mp hpos
  simp only [mem_filter] at hp
  refine ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, ?_⟩
  simp [F, g]
  convert hp.2 using 1
  ring

lemma a_pos_mul_16 {n : ℕ} (h : 0 < a n) : 0 < a (16 * n) := by
  obtain ⟨x, y, c, d, hx⟩ := exists_F_of_a_pos h
  apply a_pos_of_F (x := 4 * x) (y := 4 * y) (c := 2 * c) (d := 2 * d)
  rw [F_mul_16, hx]

/-- Scaling-and-swap identity: `4 * F x y c d = F (2x) (2y) (2d) c`. -/
lemma F_mul_4 (x y c d : ℕ) : F (2 * x) (2 * y) (2 * d) c = 4 * F x y c d := by
  simp [F, g]
  ring

lemma a_pos_mul_4 {n : ℕ} (h : 0 < a n) : 0 < a (4 * n) := by
  obtain ⟨x, y, c, d, hx⟩ := exists_F_of_a_pos h
  apply a_pos_of_F (x := 2 * x) (y := 2 * y) (c := 2 * d) (d := c)
  rw [F_mul_4, hx]

lemma g_zero_zero : g 0 0 = 0 := by simp [g]
lemma g_one_zero : g 1 0 = 1 := by simp [g]
lemma g_zero_one : g 0 1 = 4 := by simp [g]
lemma g_one_one : g 1 1 = 6 := by simp [g]
lemma g_two_zero : g 2 0 = 16 := by simp [g]
lemma g_two_one : g 2 1 = 24 := by simp [g]
lemma g_zero_two : g 0 2 = 64 := by simp [g]
lemma g_three_zero : g 3 0 = 81 := by simp [g]
lemma g_one_two : g 1 2 = 69 := by simp [g]
lemma g_three_one : g 3 1 = 94 := by simp [g]
lemma g_zero_three : g 0 3 = 324 := by simp [g]
lemma g_one_three : g 1 3 = 334 := by simp [g]
lemma g_two_three : g 2 3 = 376 := by simp [g]
lemma g_three_three : g 3 3 = 486 := by simp [g]
lemma g_four_zero : g 4 0 = 256 := by simp [g]
lemma g_four_one : g 4 1 = 276 := by simp [g]

/-- If `n - g c d` is of the form `x^2 + 2 y^2`, we are done. -/
lemma a_pos_of_sub_g_IsS {n c d : ℕ} (hle : g c d ≤ n) (h : IsS (n - g c d)) :
    0 < a n :=
  a_pos_of_IsS_add_g h hle

lemma IsS.two_mul {n : ℕ} (h : IsS n) : IsS (2 * n) := by
  obtain ⟨x, y, hx⟩ := h
  refine ⟨2 * y, x, ?_⟩
  rw [← hx]; ring

lemma IsS.four_mul {n : ℕ} (h : IsS n) : IsS (4 * n) := by
  obtain ⟨x, y, hx⟩ := h
  refine ⟨2 * x, 2 * y, ?_⟩
  rw [← hx]; ring

/-- Multiplying or dividing by 2 preserves `IsS`. -/
lemma IsS.of_two_mul {n : ℕ} (h : IsS (2 * n)) : IsS n := by
  obtain ⟨x, y, hx⟩ := h
  have hxeven : 2 ∣ x := by
    have hmod : x ^ 2 % 2 = 0 := by
      have : (x ^ 2 + 2 * y ^ 2) % 2 = 0 := by
        rw [hx]; simp
      simpa [Nat.add_mod, Nat.mul_mod] using this
    have : (x % 2) * (x % 2) % 2 = 0 := by
      simpa [Nat.pow_mod, pow_two] using hmod
    have hx01 : x % 2 = 0 ∨ x % 2 = 1 := Nat.mod_two_eq_zero_or_one x
    rcases hx01 with h0 | h1
    · exact Nat.dvd_of_mod_eq_zero h0
    · simp [h1] at this
  obtain ⟨w, rfl⟩ := hxeven
  refine ⟨y, w, ?_⟩
  have : 2 * (y ^ 2 + 2 * w ^ 2) = 2 * n := by
    convert hx using 1; ring
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) this

lemma IsS.two_mul_iff {n : ℕ} : IsS (2 * n) ↔ IsS n :=
  ⟨IsS.of_two_mul, IsS.two_mul⟩

lemma IsS.pow_two_mul {n k : ℕ} (h : IsS n) : IsS (2 ^ k * n) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    rw [pow_succ]
    simpa [mul_left_comm, mul_assoc] using ih.two_mul

lemma a_pos_of_IsS_sub (n k : ℕ) (hk : k ≤ n) (h : IsS (n - k))
    {c d : ℕ} (hg : g c d = k) : 0 < a n := by
  apply a_pos_of_IsS_add_g (c := c) (d := d)
  · simpa [hg]
  · simpa [hg]

/-- Identity: `4 * g c d = (2 * c ^ 2 + d ^ 2) ^ 2 + 15 * d ^ 4`. -/
lemma four_g_identity (c d : ℕ) :
    4 * g c d = (2 * c ^ 2 + d ^ 2) ^ 2 + 15 * d ^ 4 := by
  simp [g]; ring

/-- Identity: `g (2 * d) c = 4 * g c d`. -/
lemma g_swap_mul_4 (c d : ℕ) : g (2 * d) c = 4 * g c d := by
  simp [g]; ring

/-- If `m` is in `IsS`, then `4m + 1` is representable. -/
lemma a_pos_four_mul_add_one_of_IsS {m : ℕ} (h : IsS m) : 0 < a (4 * m + 1) := by
  obtain ⟨x, y, hx⟩ := h
  apply a_pos_of_F (x := 2 * x) (y := 2 * y) (c := 1) (d := 0)
  calc
    F (2 * x) (2 * y) 1 0
        = (2 * x) ^ 2 + 2 * (2 * y) ^ 2 + g 1 0 := rfl
    _ = 4 * x ^ 2 + 8 * y ^ 2 + 1 := by simp [g]; ring
    _ = 4 * (x ^ 2 + 2 * y ^ 2) + 1 := by ring
    _ = 4 * m + 1 := by rw [hx]

/-- If `m - 1` is in `IsS`, then `4m + 2` is representable. -/
lemma a_pos_four_mul_add_two_of_pred_IsS {m : ℕ} (hm : 1 ≤ m) (h : IsS (m - 1)) :
    0 < a (4 * m + 2) := by
  obtain ⟨x, y, hx⟩ := h
  apply a_pos_of_F (x := 2 * x) (y := 2 * y) (c := 1) (d := 1)
  calc
    F (2 * x) (2 * y) 1 1
        = (2 * x) ^ 2 + 2 * (2 * y) ^ 2 + g 1 1 := rfl
    _ = 4 * x ^ 2 + 8 * y ^ 2 + 6 := by simp [g]; ring
    _ = 4 * (x ^ 2 + 2 * y ^ 2) + 6 := by ring
    _ = 4 * (m - 1) + 6 := by rw [hx]
    _ = 4 * m + 2 := by omega

/-- If `m` has a representation with `x = 0`, then `4m + 1` is representable. -/
lemma a_pos_four_mul_add_one_of_x0 {m y c d : ℕ}
    (h : 2 * y ^ 2 + g c d = m) : 0 < a (4 * m + 1) := by
  apply a_pos_of_F (x := 1) (y := 2 * y) (c := 2 * d) (d := c)
  have : F 1 (2 * y) (2 * d) c = 1 + 2 * (2 * y) ^ 2 + g (2 * d) c := rfl
  rw [this, g_swap_mul_4, ← h]
  ring

/-- If `m` has a representation with `y = 0`, then `4m + 2` is representable. -/
lemma a_pos_four_mul_add_two_of_y0 {m x c d : ℕ}
    (h : x ^ 2 + g c d = m) : 0 < a (4 * m + 2) := by
  apply a_pos_of_F (x := 2 * x) (y := 1) (c := 2 * d) (d := c)
  have : F (2 * x) 1 (2 * d) c = (2 * x) ^ 2 + 2 * 1 ^ 2 + g (2 * d) c := rfl
  rw [this, g_swap_mul_4, ← h]
  ring

/-- If `m` is a value of `g`, then `4m + 3` is representable. -/
lemma a_pos_four_mul_add_three_of_g {m c d : ℕ} (h : g c d = m) :
    0 < a (4 * m + 3) := by
  apply a_pos_of_F (x := 1) (y := 1) (c := 2 * d) (d := c)
  have : F 1 1 (2 * d) c = 1 + 2 * 1 ^ 2 + g (2 * d) c := rfl
  rw [this, g_swap_mul_4, h]
  ring

/-- If `m` is a square, then `4m + 3` is representable. -/
lemma a_pos_four_mul_add_three_of_sq {m x : ℕ} (h : x ^ 2 = m) :
    0 < a (4 * m + 3) := by
  apply a_pos_of_F (x := 2 * x) (y := 1) (c := 1) (d := 0)
  simp [F, g, ← h]
  ring

lemma IsS.of_sq {x : ℕ} : IsS (x ^ 2) := ⟨x, 0, by simp⟩

lemma IsS.of_two_sq {y : ℕ} : IsS (2 * y ^ 2) := ⟨0, y, by simp⟩

/-- Numbers of the form `2 y ^ 2 + g c d`. -/
def IsT (m : ℕ) : Prop := ∃ y c d : ℕ, 2 * y ^ 2 + g c d = m

lemma IsT.zero : IsT 0 := ⟨0, 0, 0, by simp [g]⟩

lemma a_pos_of_IsT {m : ℕ} (h : IsT m) : 0 < a m := by
  obtain ⟨y, c, d, hy⟩ := h
  exact a_pos_of_F (x := 0) (y := y) (c := c) (d := d) (by simp [F, hy])

lemma a_pos_four_mul_add_one_of_IsT {m : ℕ} (h : IsT m) : 0 < a (4 * m + 1) := by
  obtain ⟨y, c, d, hy⟩ := h
  exact a_pos_four_mul_add_one_of_x0 hy

lemma a_pos_four_mul_add_two_of_y0_IsS {m : ℕ} (h : ∃ x c d, x ^ 2 + g c d = m) :
    0 < a (4 * m + 2) := by
  obtain ⟨x, c, d, hx⟩ := h
  exact a_pos_four_mul_add_two_of_y0 hx

lemma a_pos_of_small_g (n : ℕ)
    (h : IsS n ∨
      (1 ≤ n ∧ IsS (n - 1)) ∨
      (4 ≤ n ∧ IsS (n - 4)) ∨
      (6 ≤ n ∧ IsS (n - 6)) ∨
      (16 ≤ n ∧ IsS (n - 16)) ∨
      (24 ≤ n ∧ IsS (n - 24)) ∨
      (64 ≤ n ∧ IsS (n - 64)) ∨
      (69 ≤ n ∧ IsS (n - 69)) ∨
      (81 ≤ n ∧ IsS (n - 81)) ∨
      (94 ≤ n ∧ IsS (n - 94))) :
    0 < a n := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact a_pos_of_IsS h
  · exact a_pos_of_IsS_sub n 1 h.1 h.2 (c := 1) (d := 0) g_one_zero
  · exact a_pos_of_IsS_sub n 4 h.1 h.2 (c := 0) (d := 1) g_zero_one
  · exact a_pos_of_IsS_sub n 6 h.1 h.2 (c := 1) (d := 1) g_one_one
  · exact a_pos_of_IsS_sub n 16 h.1 h.2 (c := 2) (d := 0) g_two_zero
  · exact a_pos_of_IsS_sub n 24 h.1 h.2 (c := 2) (d := 1) g_two_one
  · exact a_pos_of_IsS_sub n 64 h.1 h.2 (c := 0) (d := 2) g_zero_two
  · exact a_pos_of_IsS_sub n 69 h.1 h.2 (c := 1) (d := 2) g_one_two
  · exact a_pos_of_IsS_sub n 81 h.1 h.2 (c := 3) (d := 0) g_three_zero
  · exact a_pos_of_IsS_sub n 94 h.1 h.2 (c := 3) (d := 1) g_three_one


lemma a_pos_of_lt_256 (n : ℕ) (hn : n < 256) : 0 < a n := by
  interval_cases n
  · exact exists_imp_a_pos (x := 0) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 1) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 2) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 1) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 2) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 0) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 2) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 3) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 4) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 1) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 2) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 4) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 3) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 3) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 5) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 0) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 5) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 5) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 4) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 5) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 4) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 1) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 5) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 4) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 5) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 3) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 6) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 6) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 6) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 5) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 0) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 1) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 0) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 5) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 5) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 6) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 2) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 6) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 2) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 6) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 2) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 0) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 6) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 5) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 7) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 4) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 0) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 4) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 7) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 6) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 2) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 7) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 7) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 8) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 6) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 3) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 4) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 5) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 3) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 5) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 6) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 2) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 8) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 8) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 8) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 9) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 2) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 13) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 13) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 6) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 5) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 9) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 4) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 9) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 0) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 9) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 7) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 9) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 13) (y := 0) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 9) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 9) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 6) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 9) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 9) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 5) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 5) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 14) (y := 0) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 14) (y := 0) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 9) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 10) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 9) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 10) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 10) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 10) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 8) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 10) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 9) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 8) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 14) (y := 3) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 14) (y := 3) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 10) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 8) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 7) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 7) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 12) (y := 2) (c := 1) (d := 2) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 10) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 7) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 10) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 5) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 8) (y := 9) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 15) (y := 1) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 8) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 8) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 14) (y := 3) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 5) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 4) (y := 10) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 15) (y := 2) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 15) (y := 2) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 11) (y := 7) (c := 2) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 10) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 14) (y := 3) (c := 2) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 15) (y := 2) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 10) (c := 0) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 13) (y := 6) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 11) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 11) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 11) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 8) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 11) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 2) (y := 11) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 11) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 10) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 7) (y := 10) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 11) (c := 0) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 11) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 10) (y := 6) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 1) (y := 6) (c := 3) (d := 2) (by norm_num)
  · exact exists_imp_a_pos (x := 3) (y := 11) (c := 0) (d := 1) (by norm_num)


/-- If `n` differs from an `IsS` number by a listed small value of `g`, we are done. -/
lemma exists_g_IsS_of_pair (n c d : ℕ) (hle : g c d ≤ n) (hS : IsS (n - g c d)) :
    ∃ c d, g c d ≤ n ∧ IsS (n - g c d) :=
  ⟨c, d, hle, hS⟩

/-- Fourth-power root: `t ^ 4 ≤ n` for `t = √√n`. -/
lemma fourth_root_pow_le (n : ℕ) : (sqrt (sqrt n)) ^ 4 ≤ n := by
  have h1 : (sqrt (sqrt n)) ^ 2 ≤ sqrt n := Nat.sqrt_le' (sqrt n)
  have h2 : (sqrt n) ^ 2 ≤ n := Nat.sqrt_le' n
  calc
    (sqrt (sqrt n)) ^ 4 = ((sqrt (sqrt n)) ^ 2) ^ 2 := by ring
    _ ≤ (sqrt n) ^ 2 := Nat.pow_le_pow_left h1 2
    _ ≤ n := h2

lemma g_zero (c : ℕ) : g c 0 = c ^ 4 := by simp [g]

lemma g_one (c : ℕ) : g c 1 = c ^ 4 + c ^ 2 + 4 := by simp [g]; ring

lemma g_two (c : ℕ) : g c 2 = c ^ 4 + 4 * c ^ 2 + 64 := by simp [g]; ring

lemma g_three (c : ℕ) : g c 3 = c ^ 4 + 9 * c ^ 2 + 324 := by simp [g]; ring

/-- If `n - c ^ 4` is in `IsS` and `c ^ 4 ≤ n`, we are done. -/
lemma exists_g_IsS_of_fourth (n c : ℕ) (hle : c ^ 4 ≤ n) (hS : IsS (n - c ^ 4)) :
    ∃ c d, g c d ≤ n ∧ IsS (n - g c d) := by
  refine exists_g_IsS_of_pair n c 0 ?_ ?_
  · simpa [g] using hle
  · simpa [g] using hS

/-- Guarded selector for a listed pair. -/
lemma exists_g_IsS_of_le_and (n c d : ℕ)
    (h : g c d ≤ n ∧ IsS (n - g c d)) :
    ∃ c d, g c d ≤ n ∧ IsS (n - g c d) :=
  ⟨c, d, h.1, h.2⟩

/-- If `n - k ^ 2` is in `IsT`, then `n - g` is in `IsS`. -/
lemma exists_g_IsS_of_IsT_sub_sq (n k : ℕ) (hle : k ^ 2 ≤ n) (hT : IsT (n - k ^ 2)) :
    ∃ c d, g c d ≤ n ∧ IsS (n - g c d) := by
  obtain ⟨y, c, d, hy⟩ := hT
  have hgle : g c d ≤ n - k ^ 2 := by
    have := hy
    omega
  have hgle' : g c d ≤ n := le_trans hgle (Nat.sub_le n (k ^ 2))
  refine ⟨c, d, hgle', ⟨k, y, ?_⟩⟩
  have : n - g c d = k ^ 2 + 2 * y ^ 2 := by
    have hsum : k ^ 2 + (n - k ^ 2) = n := Nat.add_sub_of_le hle
    have : k ^ 2 + (2 * y ^ 2 + g c d) = n := by rw [hy, hsum]
    omega
  exact this.symm

/-- Combining a fourth power with an `IsS` number. -/
lemma F_fourth_add_IsS (t x y : ℕ) :
    F x y t 0 = t ^ 4 + x ^ 2 + 2 * y ^ 2 := by
  simp [F, g]; ring

/-- Combining a fourth power with an `x = 0` representation. -/
lemma F_fourth_add_x0 (t y c d : ℕ) :
    F (t ^ 2) y c d = t ^ 4 + 2 * y ^ 2 + g c d := by
  simp [F]; ring

/-- Combining two fourth powers with a `g`-value when `u ≤ t`. -/
lemma F_two_fourths (t u c d : ℕ) (hle : u ≤ t) :
    F (t ^ 2 - u ^ 2) (t * u) c d = t ^ 4 + u ^ 4 + g c d := by
  have hle2 : u ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hle 2
  simp [F]
  zify [hle2]
  ring

/-- Special identity: `t ^ 4 + 7 = F (t ^ 2 - 1) t 1 1` for `t ≥ 1`. -/
lemma F_fourth_add_seven (t : ℕ) (ht : 1 ≤ t) :
    F (t ^ 2 - 1) t 1 1 = t ^ 4 + 7 := by
  have : 1 ≤ t ^ 2 := Nat.one_le_pow 2 t ht
  simp [F, g]
  zify [this]
  ring

/-- If `k ^ 2 = y ^ 2 + x * t ^ 2` and `x ≤ t ^ 2`, then
`t ^ 4 + F x y c d = F (t ^ 2 - x) k c d`. -/
lemma F_fourth_add_pell {t x y k c d : ℕ}
    (hsq : k ^ 2 = y ^ 2 + x * t ^ 2) (hx : x ≤ t ^ 2) :
    F (t ^ 2 - x) k c d = t ^ 4 + F x y c d := by
  simp [F]
  zify [hx, hsq]
  ring

/-- Merge `t ^ 4` with a representation of the remainder when `x = 0`. -/
lemma merge_x0 (t y c d : ℕ) :
    F (t ^ 2) y c d = t ^ 4 + 2 * y ^ 2 + g c d :=
  F_fourth_add_x0 t y c d

/-- Merge `t ^ 4` with an `IsS` remainder. -/
lemma merge_IsS (t x y : ℕ) :
    F x y t 0 = t ^ 4 + x ^ 2 + 2 * y ^ 2 :=
  F_fourth_add_IsS t x y

/-- If the remainder is representable with `x = 0`, we obtain a representation of
`t ^ 4 + remainder`. -/
lemma a_pos_of_fourth_add_IsT (t : ℕ) {r : ℕ} (h : IsT r) :
    0 < a (t ^ 4 + r) := by
  obtain ⟨y, c, d, hy⟩ := h
  apply a_pos_of_F (x := t ^ 2) (y := y) (c := c) (d := d)
  rw [F_fourth_add_x0]
  omega

/-- If the remainder is in `IsS`, we obtain a representation of `t ^ 4 + remainder`. -/
lemma a_pos_of_fourth_add_IsS (t : ℕ) {r : ℕ} (h : IsS r) :
    0 < a (t ^ 4 + r) := by
  obtain ⟨x, y, hx⟩ := h
  apply a_pos_of_F (x := x) (y := y) (c := t) (d := 0)
  rw [F_fourth_add_IsS]
  omega

/-- Increment identity (A): `F (2k+1) (2y) (2d) c = 4(k(k+1)+2y²+g c d)+1`. -/
lemma F_inc_A (k y c d : ℕ) :
    F (2 * k + 1) (2 * y) (2 * d) c
      = 4 * (k * (k + 1) + 2 * y ^ 2 + g c d) + 1 := by
  simp [F, g]; ring

/-- Increment identity (B): `F (2k) (2y+1) (2d) c = 4(k²+2y(y+1)+g c d)+2`. -/
lemma F_inc_B (k y c d : ℕ) :
    F (2 * k) (2 * y + 1) (2 * d) c
      = 4 * (k ^ 2 + 2 * y * (y + 1) + g c d) + 2 := by
  simp [F, g]; ring

/-- Increment identity (C): `F (2k+1) (2y+1) (2d) c = 4(k(k+1)+2y(y+1)+g c d)+3`. -/
lemma F_inc_C (k y c d : ℕ) :
    F (2 * k + 1) (2 * y + 1) (2 * d) c
      = 4 * (k * (k + 1) + 2 * y * (y + 1) + g c d) + 3 := by
  simp [F, g]; ring

lemma a_pos_of_inc_A {m k y c d : ℕ}
    (h : k * (k + 1) + 2 * y ^ 2 + g c d = m) : 0 < a (4 * m + 1) := by
  apply a_pos_of_F (x := 2 * k + 1) (y := 2 * y) (c := 2 * d) (d := c)
  rw [F_inc_A, h]

lemma a_pos_of_inc_B {m k y c d : ℕ}
    (h : k ^ 2 + 2 * y * (y + 1) + g c d = m) : 0 < a (4 * m + 2) := by
  apply a_pos_of_F (x := 2 * k) (y := 2 * y + 1) (c := 2 * d) (d := c)
  rw [F_inc_B, h]

lemma a_pos_of_inc_C {m k y c d : ℕ}
    (h : k * (k + 1) + 2 * y * (y + 1) + g c d = m) : 0 < a (4 * m + 3) := by
  apply a_pos_of_F (x := 2 * k + 1) (y := 2 * y + 1) (c := 2 * d) (d := c)
  rw [F_inc_C, h]

/-- Explicit witnesses for those `n = 4m+1 ≥ 256` whose `m` fails increment (A). -/
lemma a_pos_exc_A :
    (0 < a 269) ∧ (0 < a 989) ∧ (0 < a 1069) ∧ (0 < a 1389) ∧ (0 < a 1589) ∧
    (0 < a 1669) ∧ (0 < a 1909) ∧ (0 < a 2109) ∧ (0 < a 2261) ∧ (0 < a 7661) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_imp_a_pos (x := 14) (y := 6) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 30) (y := 2) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 26) (y := 14) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 26) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 26) (y := 12) (c := 5) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 34) (y := 16) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 26) (y := 24) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 26) (y := 26) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 22) (y := 24) (c := 5) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 30) (y := 10) (c := 9) (d := 0) (by norm_num)

/-- Explicit witnesses for those `n = 4m+2 ≥ 256` whose `m` fails increment (B). -/
lemma a_pos_exc_B :
    (0 < a 334) ∧ (0 < a 766) ∧ (0 < a 894) ∧ (0 < a 1246) ∧
    (0 < a 3134) ∧ (0 < a 4142) ∧ (0 < a 4366) ∧ (0 < a 25534) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_imp_a_pos (x := 16) (y := 6) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 25) (y := 6) (c := 1) (d := 2) (by norm_num)
  · exact exists_imp_a_pos (x := 0) (y := 20) (c := 3) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 32) (y := 8) (c := 3) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 19) (y := 36) (c := 3) (d := 2) (by norm_num)
  · exact exists_imp_a_pos (x := 36) (y := 14) (c := 7) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 52) (y := 28) (c := 3) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 136) (y := 14) (c := 9) (d := 1) (by norm_num)

/-- Explicit witnesses for those `n = 4m+3 ≥ 256` whose `m` fails increment (C). -/
lemma a_pos_exc_C :
    (0 < a 263) ∧ (0 < a 759) ∧ (0 < a 1039) ∧ (0 < a 1319) ∧
    (0 < a 1639) ∧ (0 < a 1719) ∧ (0 < a 1919) ∧ (0 < a 2159) ∧
    (0 < a 2239) ∧ (0 < a 2439) ∧ (0 < a 2495) ∧ (0 < a 2759) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_imp_a_pos (x := 10) (y := 9) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 19) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 31) (y := 6) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 34) (y := 9) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 26) (y := 21) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 6) (y := 29) (c := 1) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 39) (y := 14) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 45) (y := 8) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 41) (y := 6) (c := 3) (d := 3) (by norm_num)
  · exact exists_imp_a_pos (x := 46) (y := 11) (c := 3) (d := 0) (by norm_num)
  · exact exists_imp_a_pos (x := 39) (y := 22) (c := 1) (d := 1) (by norm_num)
  · exact exists_imp_a_pos (x := 46) (y := 3) (c := 5) (d := 0) (by norm_num)

/-- The remaining arithmetic core: if `n ≥ 256` is not a multiple of `4`,
then `n - g c d` is of the form `x ^ 2 + 2 y ^ 2` for some `c, d`. -/
lemma exists_g_IsS {n : ℕ} (hn : 256 ≤ n) (h4 : ¬ 4 ∣ n)
    (ih : ∀ m < n, 0 < a m) :
    ∃ c d, g c d ≤ n ∧ IsS (n - g c d) := by
  -- First dispose of the cases where a small value of `g` already works.
  by_cases h0 : IsS n
  · exact ⟨0, 0, by simp [g], by simpa [g]⟩
  by_cases h1 : IsS (n - 1)
  · exact ⟨1, 0, by simp [g]; omega, by simpa [g]⟩
  by_cases h4' : IsS (n - 4)
  · exact ⟨0, 1, by simp [g]; omega, by simpa [g]⟩
  by_cases h6 : IsS (n - 6)
  · exact ⟨1, 1, by simp [g]; omega, by simpa [g]⟩
  by_cases h16 : IsS (n - 16)
  · exact ⟨2, 0, by simp [g]; omega, by simpa [g]⟩
  by_cases h24 : IsS (n - 24)
  · exact ⟨2, 1, by simp [g]; omega, by simpa [g]⟩
  by_cases h64 : IsS (n - 64)
  · exact ⟨0, 2, by simp [g]; omega, by simpa [g]⟩
  by_cases h69 : IsS (n - 69)
  · exact ⟨1, 2, by simp [g]; omega, by simpa [g]⟩
  by_cases h81 : IsS (n - 81)
  · exact ⟨3, 0, by simp [g]; omega, by simpa [g]⟩
  by_cases h94 : IsS (n - 94)
  · exact ⟨3, 1, by simp [g]; omega, by simpa [g]⟩
  by_cases h256 : IsS (n - 256)
  · exact ⟨4, 0, by simp [g]; omega, by simpa [g]⟩
  by_cases h276 : 276 ≤ n ∧ IsS (n - 276)
  · exact exists_g_IsS_of_le_and n 4 1 (by simpa [g] using h276)
  by_cases h324 : 324 ≤ n ∧ IsS (n - 324)
  · exact exists_g_IsS_of_le_and n 0 3 (by simpa [g] using h324)
  by_cases h334 : 334 ≤ n ∧ IsS (n - 334)
  · exact exists_g_IsS_of_le_and n 1 3 (by simpa [g] using h334)
  by_cases h376 : 376 ≤ n ∧ IsS (n - 376)
  · exact exists_g_IsS_of_le_and n 2 3 (by simpa [g] using h376)
  by_cases h486 : 486 ≤ n ∧ IsS (n - 486)
  · exact exists_g_IsS_of_le_and n 3 3 (by simpa [g] using h486)
  by_cases h625 : 625 ≤ n ∧ IsS (n - 625)
  · exact exists_g_IsS_of_le_and n 5 0 (by simpa [g] using h625)
  by_cases h654 : 654 ≤ n ∧ IsS (n - 654)
  · exact exists_g_IsS_of_le_and n 5 1 (by simpa [g] using h654)
  by_cases h1296 : 1296 ≤ n ∧ IsS (n - 1296)
  · exact exists_g_IsS_of_le_and n 6 0 (by simpa [g] using h1296)
  by_cases h1336 : 1336 ≤ n ∧ IsS (n - 1336)
  · exact exists_g_IsS_of_le_and n 6 1 (by simpa [g] using h1336)
  by_cases h2401 : 2401 ≤ n ∧ IsS (n - 2401)
  · exact exists_g_IsS_of_le_and n 7 0 (by simpa [g] using h2401)
  by_cases h2454 : 2454 ≤ n ∧ IsS (n - 2454)
  · exact exists_g_IsS_of_le_and n 7 1 (by simpa [g] using h2454)
  by_cases h4096 : 4096 ≤ n ∧ IsS (n - 4096)
  · exact exists_g_IsS_of_le_and n 8 0 (by simpa [g] using h4096)
  by_cases h4164 : 4164 ≤ n ∧ IsS (n - 4164)
  · exact exists_g_IsS_of_le_and n 8 1 (by simpa [g] using h4164)
  by_cases h6561 : 6561 ≤ n ∧ IsS (n - 6561)
  · exact exists_g_IsS_of_le_and n 9 0 (by simpa [g] using h6561)
  by_cases h6646 : 6646 ≤ n ∧ IsS (n - 6646)
  · exact exists_g_IsS_of_le_and n 9 1 (by simpa [g] using h6646)
  by_cases h10000 : 10000 ≤ n ∧ IsS (n - 10000)
  · exact exists_g_IsS_of_le_and n 10 0 (by simpa [g] using h10000)
  -- Try the fourth-root window: `c` near `⌊n^{1/4}⌋`, `d ∈ {0,1,2,3}`.
  set t := sqrt (sqrt n) with ht
  have ht4 : t ^ 4 ≤ n := by
    simpa [ht] using fourth_root_pow_le n
  by_cases ht0 : IsS (n - t ^ 4)
  · exact exists_g_IsS_of_fourth n t ht4 ht0
  by_cases ht1 : 1 ≤ t ∧ IsS (n - (t - 1) ^ 4)
  · have hle : (t - 1) ^ 4 ≤ n :=
      le_trans (Nat.pow_le_pow_left (Nat.sub_le t 1) 4) ht4
    exact exists_g_IsS_of_fourth n (t - 1) hle ht1.2
  by_cases htd1 : g t 1 ≤ n ∧ IsS (n - g t 1)
  · exact exists_g_IsS_of_le_and n t 1 htd1
  by_cases htd3 : g t 3 ≤ n ∧ IsS (n - g t 3)
  · exact exists_g_IsS_of_le_and n t 3 htd3
  by_cases htd2 : g t 2 ≤ n ∧ IsS (n - g t 2)
  · exact exists_g_IsS_of_le_and n t 2 htd2
  by_cases ht1d1 : 1 ≤ t ∧ g (t - 1) 1 ≤ n ∧ IsS (n - g (t - 1) 1)
  · exact exists_g_IsS_of_le_and n (t - 1) 1 ⟨ht1d1.2.1, ht1d1.2.2⟩
  by_cases ht1d2 : 1 ≤ t ∧ g (t - 1) 2 ≤ n ∧ IsS (n - g (t - 1) 2)
  · exact exists_g_IsS_of_le_and n (t - 1) 2 ⟨ht1d2.2.1, ht1d2.2.2⟩
  by_cases ht1d3 : 1 ≤ t ∧ g (t - 1) 3 ≤ n ∧ IsS (n - g (t - 1) 3)
  · exact exists_g_IsS_of_le_and n (t - 1) 3 ⟨ht1d3.2.1, ht1d3.2.2⟩
  by_cases ht2d0 : 2 ≤ t ∧ IsS (n - (t - 2) ^ 4)
  · have hle : (t - 2) ^ 4 ≤ n :=
      le_trans (Nat.pow_le_pow_left (Nat.sub_le t 2) 4) ht4
    exact exists_g_IsS_of_fourth n (t - 2) hle ht2d0.2
  by_cases ht2d1 : 2 ≤ t ∧ g (t - 2) 1 ≤ n ∧ IsS (n - g (t - 2) 1)
  · exact exists_g_IsS_of_le_and n (t - 2) 1 ⟨ht2d1.2.1, ht2d1.2.2⟩
  by_cases ht2d2 : 2 ≤ t ∧ g (t - 2) 2 ≤ n ∧ IsS (n - g (t - 2) 2)
  · exact exists_g_IsS_of_le_and n (t - 2) 2 ⟨ht2d2.2.1, ht2d2.2.2⟩
  by_cases ht3d0 : 3 ≤ t ∧ IsS (n - (t - 3) ^ 4)
  · have hle : (t - 3) ^ 4 ≤ n :=
      le_trans (Nat.pow_le_pow_left (Nat.sub_le t 3) 4) ht4
    exact exists_g_IsS_of_fourth n (t - 3) hle ht3d0.2
  -- If the fourth-power remainder is in `IsT`, then `n - g c d = t ^ 4 + 2 y ^ 2` is `IsS`.
  by_cases htT : IsT (n - t ^ 4)
  · obtain ⟨y, c, d, hy⟩ := htT
    have hgle : g c d ≤ n - t ^ 4 := by
      have := hy
      omega
    have hgle' : g c d ≤ n := le_trans hgle (Nat.sub_le n (t ^ 4))
    refine ⟨c, d, hgle', ⟨t ^ 2, y, ?_⟩⟩
    have : n - g c d = t ^ 4 + 2 * y ^ 2 := by
      have hsum : t ^ 4 + (n - t ^ 4) = n := Nat.add_sub_of_le ht4
      have : t ^ 4 + (2 * y ^ 2 + g c d) = n := by rw [hy, hsum]
      omega
    rw [this]; ring
  by_cases ht1T : 1 ≤ t ∧ IsT (n - (t - 1) ^ 4)
  · obtain ⟨y, c, d, hy⟩ := ht1T.2
    have hle : (t - 1) ^ 4 ≤ n :=
      le_trans (Nat.pow_le_pow_left (Nat.sub_le t 1) 4) ht4
    have hgle : g c d ≤ n - (t - 1) ^ 4 := by
      have := hy
      omega
    have hgle' : g c d ≤ n := le_trans hgle (Nat.sub_le n ((t - 1) ^ 4))
    refine ⟨c, d, hgle', ⟨(t - 1) ^ 2, y, ?_⟩⟩
    have : n - g c d = (t - 1) ^ 4 + 2 * y ^ 2 := by
      have hsum : (t - 1) ^ 4 + (n - (t - 1) ^ 4) = n := Nat.add_sub_of_le hle
      have : (t - 1) ^ 4 + (2 * y ^ 2 + g c d) = n := by rw [hy, hsum]
      omega
    rw [this]; ring
  by_cases hT1 : IsT (n - 1)
  · exact exists_g_IsS_of_IsT_sub_sq n 1 (by omega) hT1
  by_cases hT4 : IsT (n - 4)
  · exact exists_g_IsS_of_IsT_sub_sq n 2 (by omega) hT4
  by_cases hT9 : 9 ≤ n ∧ IsT (n - 9)
  · exact exists_g_IsS_of_IsT_sub_sq n 3 hT9.1 hT9.2
  by_cases hT16 : IsT (n - 16)
  · exact exists_g_IsS_of_IsT_sub_sq n 4 (by omega) hT16
  by_cases hT25 : 25 ≤ n ∧ IsT (n - 25)
  · exact exists_g_IsS_of_IsT_sub_sq n 5 hT25.1 hT25.2
  by_cases hT36 : 36 ≤ n ∧ IsT (n - 36)
  · exact exists_g_IsS_of_IsT_sub_sq n 6 hT36.1 hT36.2
  by_cases hT49 : 49 ≤ n ∧ IsT (n - 49)
  · exact exists_g_IsS_of_IsT_sub_sq n 7 hT49.1 hT49.2
  by_cases hT64 : IsT (n - 64)
  · exact exists_g_IsS_of_IsT_sub_sq n 8 (by omega) hT64
  by_cases hT81 : IsT (n - 81)
  · exact exists_g_IsS_of_IsT_sub_sq n 9 (by omega) hT81
  by_cases hT100 : 100 ≤ n ∧ IsT (n - 100)
  · exact exists_g_IsS_of_IsT_sub_sq n 10 hT100.1 hT100.2
  -- Sweep a compact box of small `(c, d)`.
  by_cases hbox : ∃ c d, c ≤ 15 ∧ d ≤ 4 ∧ g c d ≤ n ∧ IsS (n - g c d)
  · obtain ⟨c, d, _, _, hle, hS⟩ := hbox
    exact ⟨c, d, hle, hS⟩
  -- Remaining 4-free `n ≥ 256` avoid every listed `g`-translate of `IsS`.
  -- Treat residue classes separately.
  have hmod16 : n % 16 = 1 ∨ n % 16 = 2 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨
      n % 16 = 6 ∨ n % 16 = 7 ∨ n % 16 = 9 ∨ n % 16 = 10 ∨
      n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 14 ∨ n % 16 = 15 := by
    have : n % 16 < 16 := Nat.mod_lt n (by decide)
    have h4' : n % 4 ≠ 0 := by
      intro h0; exact h4 (Nat.dvd_of_mod_eq_zero h0)
    omega
  have ht_ge4 : 4 ≤ t := by
    have h16le : 16 ≤ sqrt n := by
      rw [Nat.le_sqrt']
      calc 16 ^ 2 = 256 := by norm_num
        _ ≤ n := hn
    have : 4 ≤ sqrt (sqrt n) := by
      rw [Nat.le_sqrt']
      calc 4 ^ 2 = 16 := by norm_num
        _ ≤ sqrt n := h16le
    simpa [ht] using this
  set k := sqrt n with hk
  have hk2 : k ^ 2 ≤ n := by
    simpa [hk] using Nat.sqrt_le' n
  by_cases hTk : IsT (n - k ^ 2)
  · exact exists_g_IsS_of_IsT_sub_sq n k hk2 hTk
  rcases hmod16 with h16 | h16 | h16 | h16 | h16 | h16 | h16 | h16 | h16 | h16 | h16 | h16
  · exact exists_g_IsS_of_pair n 3 2 (by simp [g]; omega) (by
      apply IsS_of_mod8_not_dvd_five_seven
      · have : (n - 181) % 8 = 1 ∨ (n - 181) % 8 = 3 := by
          have h181 : 181 % 8 = 5 := by decide
          have hn8 : n % 8 = 1 := by omega
          have hle : 181 ≤ n := by omega
          rw [Nat.sub_mod_eq_zero_of_mod_eq] <;> omega
        exact this
      · intro h5; omega
      · intro h7; omega
      · omega)
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

theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    if hlt : n < 256 then
      exact a_pos_of_lt_256 n hlt
    else if h4 : 4 ∣ n then
      have hn0 : 0 < n := by
        have : 4 ≤ n := Nat.le_of_dvd (by omega) h4
        omega
      have hdiv : n / 4 < n := Nat.div_lt_self hn0 (by norm_num)
      have : n = 4 * (n / 4) := (Nat.mul_div_cancel' h4).symm
      rw [this]
      exact a_pos_mul_4 (ih (n / 4) hdiv)
    else
      have hn : 256 ≤ n := by omega
      have hmod : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
        have : n % 4 < 4 := Nat.mod_lt n (by decide)
        have : n % 4 ≠ 0 := by
          intro h0
          exact h4 (Nat.dvd_of_mod_eq_zero h0)
        omega
      rcases hmod with hmod | hmod | hmod
      · -- `n = 4m+1`.  If `m` is in `IsS` or `IsT`, the increment applies.
        set m := n / 4 with hmdef
        have hn1 : n = 4 * m + 1 := by
          have := Nat.div_add_mod n 4
          omega
        by_cases hmS : IsS m
        · rw [hn1]; exact a_pos_four_mul_add_one_of_IsS hmS
        · by_cases hmT : IsT m
          · rw [hn1]; exact a_pos_four_mul_add_one_of_IsT hmT
          · obtain ⟨c, d, hle, hS⟩ := exists_g_IsS hn h4 ih
            exact a_pos_of_IsS_add_g hS hle
      · set m := n / 4 with hmdef
        have hn2 : n = 4 * m + 2 := by
          have := Nat.div_add_mod n 4
          omega
        have hmpos : 1 ≤ m := by omega
        by_cases hmS : IsS (m - 1)
        · rw [hn2]; exact a_pos_four_mul_add_two_of_pred_IsS hmpos hmS
        · by_cases hmy : ∃ x c d, x ^ 2 + g c d = m
          · rw [hn2]; exact a_pos_four_mul_add_two_of_y0_IsS hmy
          · obtain ⟨c, d, hle, hS⟩ := exists_g_IsS hn h4 ih
            exact a_pos_of_IsS_add_g hS hle
      · set m := n / 4 with hmdef
        have hn3 : n = 4 * m + 3 := by
          have := Nat.div_add_mod n 4
          omega
        by_cases hsq : ∃ x, x ^ 2 = m
        · obtain ⟨x, hx⟩ := hsq
          rw [hn3]; exact a_pos_four_mul_add_three_of_sq hx
        · by_cases hg : ∃ c d, g c d = m
          · obtain ⟨c, d, hc⟩ := hg
            rw [hn3]; exact a_pos_four_mul_add_three_of_g hc
          · obtain ⟨c, d, hle, hS⟩ := exists_g_IsS hn h4 ih
            exact a_pos_of_IsS_add_g hS hle
