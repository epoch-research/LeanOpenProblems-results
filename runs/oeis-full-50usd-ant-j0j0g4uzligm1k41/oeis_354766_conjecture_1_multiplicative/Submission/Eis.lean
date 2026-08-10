import Mathlib

set_option maxHeartbeats 1000000

/-!
Concrete Eisenstein integers ℤ[ω], ω a primitive cube root of unity, ω²+ω+1=0.
Element (a,b) ↦ a + b·ω.  Norm N(a,b) = a² - ab + b².
Goal: count #{(a,b) : a² + a b + b² = M} = 6 · Σ_{d|M} χ(d).
-/

open scoped BigOperators

@[ext]
structure Eis where
  re : ℤ
  im : ℤ
deriving DecidableEq

namespace Eis

instance : Zero Eis := ⟨⟨0,0⟩⟩
instance : One Eis := ⟨⟨1,0⟩⟩
instance : Add Eis := ⟨fun x y => ⟨x.re+y.re, x.im+y.im⟩⟩
instance : Neg Eis := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Eis := ⟨fun x y => ⟨x.re-y.re, x.im-y.im⟩⟩
-- (a+bω)(c+dω) = ac + (ad+bc)ω + bd ω²,  ω² = -1-ω
-- = (ac - bd) + (ad+bc-bd) ω
instance : Mul Eis := ⟨fun x y => ⟨x.re*y.re - x.im*y.im, x.re*y.im + x.im*y.re - x.im*y.im⟩⟩

@[simp] theorem zero_re : (0:Eis).re = 0 := rfl
@[simp] theorem zero_im : (0:Eis).im = 0 := rfl
@[simp] theorem one_re : (1:Eis).re = 1 := rfl
@[simp] theorem one_im : (1:Eis).im = 0 := rfl
@[simp] theorem add_re (x y : Eis) : (x+y).re = x.re+y.re := rfl
@[simp] theorem add_im (x y : Eis) : (x+y).im = x.im+y.im := rfl
@[simp] theorem neg_re (x : Eis) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Eis) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Eis) : (x-y).re = x.re-y.re := rfl
@[simp] theorem sub_im (x y : Eis) : (x-y).im = x.im-y.im := rfl
@[simp] theorem mul_re (x y : Eis) : (x*y).re = x.re*y.re - x.im*y.im := rfl
@[simp] theorem mul_im (x y : Eis) : (x*y).im = x.re*y.im + x.im*y.re - x.im*y.im := rfl

instance : CommRing Eis where
  add_assoc a b c := by ext <;> simp <;> ring
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring
  neg_add_cancel a := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg a b := by ext <;> simp <;> ring

/-- Norm N(a+bω) = a² - ab + b². -/
def norm (x : Eis) : ℤ := x.re*x.re - x.re*x.im + x.im*x.im

@[simp] theorem norm_zero : norm 0 = 0 := rfl
@[simp] theorem norm_one : norm 1 = 1 := rfl

theorem norm_nonneg (x : Eis) : 0 ≤ norm x := by
  unfold norm; nlinarith [sq_nonneg (2*x.re - x.im), sq_nonneg x.im]

theorem norm_mul (x y : Eis) : norm (x*y) = norm x * norm y := by
  unfold norm; simp; ring

theorem norm_eq_zero {x : Eis} : norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    unfold norm at h
    have hre : x.re = 0 ∧ x.im = 0 := by
      constructor <;> nlinarith [sq_nonneg (2*x.re - x.im), sq_nonneg x.im, sq_nonneg x.re, sq_nonneg (2*x.im - x.re)]
    ext <;> simp [hre.1, hre.2]
  · rintro rfl; simp

/-- Conjugate: a + bω ↦ (a-b) - bω. -/
def conj (x : Eis) : Eis := ⟨x.re - x.im, -x.im⟩

@[simp] theorem conj_re (x : Eis) : (conj x).re = x.re - x.im := rfl
@[simp] theorem conj_im (x : Eis) : (conj x).im = -x.im := rfl

theorem mul_conj (x : Eis) : x * conj x = ⟨norm x, 0⟩ := by
  ext <;> simp [conj, norm] <;> ring

theorem norm_conj (x : Eis) : norm (conj x) = norm x := by
  unfold norm conj; simp; ring

/-- Quotient by rounding in ℂ. -/
noncomputable def equot (x y : Eis) : Eis :=
  let D : ℤ := norm y
  let n := x * conj y
  ⟨round ((n.re : ℚ)/(D:ℚ)), round ((n.im : ℚ)/(D:ℚ))⟩

noncomputable def erem (x y : Eis) : Eis := x - equot x y * y

theorem equot_add_erem (x y : Eis) : equot x y * y + erem x y = x := by
  unfold erem; ring

theorem equot_re (x y : Eis) :
    (equot x y).re = round (((x * conj y).re : ℚ)/((norm y : ℤ):ℚ)) := rfl
theorem equot_im (x y : Eis) :
    (equot x y).im = round (((x * conj y).im : ℚ)/((norm y : ℤ):ℚ)) := rfl

/-- Key: remainder has smaller norm. -/
theorem norm_erem_lt (x : Eis) {y : Eis} (hy : y ≠ 0) : norm (erem x y) < norm y := by
  have hD : (0:ℤ) < norm y := lt_of_le_of_ne (norm_nonneg y) (fun h => hy (norm_eq_zero.mp h.symm))
  set D : ℤ := norm y with hDdef
  set nn := x * conj y with hnn
  set qr : ℤ := (equot x y).re with hqr
  set qi : ℤ := (equot x y).im with hqi
  set A : ℤ := nn.re - qr * D with hA
  set B : ℤ := nn.im - qi * D with hB
  -- (erem x y) * conj y = ⟨A, B⟩
  have hmul : (erem x y) * conj y = ⟨A, B⟩ := by
    have e1 : erem x y * conj y = nn - equot x y * (y * conj y) := by
      unfold erem; rw [hnn]; ring
    rw [mul_conj y] at e1
    rw [e1]
    ext
    · show nn.re - (equot x y * ⟨norm y, 0⟩).re = A
      simp only [mul_re, hA, hDdef]; ring
    · show nn.im - (equot x y * ⟨norm y, 0⟩).im = B
      simp only [mul_im, hB, hDdef]; ring
  -- norm of both sides
  have hnormeq : norm (erem x y) * D = A*A - A*B + B*B := by
    have h := norm_mul (erem x y) (conj y)
    rw [norm_conj, ← hDdef, hmul] at h
    rw [← h]; rfl
  -- bounds |A| ≤ D/2, |B| ≤ D/2  (in the form 4A² ≤ D², 4B² ≤ D²)
  have hDQ : (0:ℚ) < (D:ℚ) := by exact_mod_cast hD
  have hDne : (D:ℚ) ≠ 0 := ne_of_gt hDQ
  have boundA : 4 * A * A ≤ D * D := by
    have hr : |((nn.re:ℚ)/(D:ℚ)) - qr| ≤ 1/2 := by
      rw [hqr, equot_re]; exact abs_sub_round _
    have key : |(A:ℚ)| ≤ (D:ℚ)/2 := by
      have heq : (A:ℚ) = (D:ℚ) * ((nn.re:ℚ)/D - qr) := by
        rw [hA]; push_cast; field_simp
      rw [heq, abs_mul, abs_of_pos hDQ]
      calc (D:ℚ) * |(nn.re:ℚ)/D - qr| ≤ (D:ℚ) * (1/2) :=
              mul_le_mul_of_nonneg_left hr (le_of_lt hDQ)
        _ = (D:ℚ)/2 := by ring
    have hq : (4:ℚ) * A * A ≤ D * D := by
      nlinarith [key, abs_nonneg (A:ℚ), abs_mul_abs_self (A:ℚ), hDQ]
    exact_mod_cast hq
  have boundB : 4 * B * B ≤ D * D := by
    have hr : |((nn.im:ℚ)/(D:ℚ)) - qi| ≤ 1/2 := by
      rw [hqi, equot_im]; exact abs_sub_round _
    have key : |(B:ℚ)| ≤ (D:ℚ)/2 := by
      have heq : (B:ℚ) = (D:ℚ) * ((nn.im:ℚ)/D - qi) := by
        rw [hB]; push_cast; field_simp
      rw [heq, abs_mul, abs_of_pos hDQ]
      calc (D:ℚ) * |(nn.im:ℚ)/D - qi| ≤ (D:ℚ) * (1/2) :=
              mul_le_mul_of_nonneg_left hr (le_of_lt hDQ)
        _ = (D:ℚ)/2 := by ring
    have hq : (4:ℚ) * B * B ≤ D * D := by
      nlinarith [key, abs_nonneg (B:ℚ), abs_mul_abs_self (B:ℚ), hDQ]
    exact_mod_cast hq
  -- conclude
  have hnn0 : 0 ≤ norm (erem x y) := norm_nonneg _
  nlinarith [hnormeq, boundA, boundB, hD, hnn0, sq_nonneg (A+B), sq_nonneg (A-B), mul_pos hD hD]

instance : Nontrivial Eis := ⟨⟨0, 1, fun h => by simpa using congrArg Eis.re h⟩⟩

theorem equot_zero (a : Eis) : equot a 0 = 0 := by
  ext <;> simp [equot, norm, conj]

noncomputable instance : EuclideanDomain Eis where
  quotient := equot
  quotient_zero := equot_zero
  remainder := erem
  quotient_mul_add_remainder_eq a b := by rw [mul_comm]; exact equot_add_erem a b
  r a b := norm a < norm b
  r_wellFounded :=
    Subrelation.wf (r := InvImage Nat.lt (fun a => (norm a).toNat))
      (fun {a b} h => by
        have := norm_nonneg a; have := norm_nonneg b
        show ((norm a).toNat) < ((norm b).toNat); omega)
      (InvImage.wf (fun a => (norm a).toNat) Nat.lt_wfRel.wf)
  remainder_lt a {b} hb := norm_erem_lt a hb
  mul_left_not_lt a {b} hb := by
    have hb1 : 1 ≤ norm b := by
      have := norm_nonneg b
      rcases eq_or_lt_of_le this with h | h
      · exact absurd (norm_eq_zero.mp h.symm) hb
      · omega
    have ha := norm_nonneg a
    rw [norm_mul]
    simp only [not_lt]
    nlinarith [ha, hb1]

end Eis

noncomputable instance : GCDMonoid Eis := EuclideanDomain.gcdMonoid Eis



namespace Eis

theorem isUnit_iff_norm_eq_one {x : Eis} : IsUnit x ↔ norm x = 1 := by
  constructor
  · intro h
    rw [isUnit_iff_exists_inv] at h
    obtain ⟨y, hy⟩ := h
    have hn : norm x * norm y = 1 := by rw [← norm_mul, hy]; rfl
    have hx := norm_nonneg x
    exact Int.eq_one_of_dvd_one hx ⟨norm y, hn.symm⟩
  · intro h
    have hxc : x * conj x = 1 := by rw [mul_conj, h]; rfl
    exact ⟨Units.mkOfMulEqOne x (conj x) hxc, rfl⟩

theorem norm_pos_of_ne_zero {x : Eis} (hx : x ≠ 0) : 0 < norm x :=
  lt_of_le_of_ne (norm_nonneg x) (fun h => hx (norm_eq_zero.mp h.symm))

/-- Coordinates are bounded by the norm: `a² + b² ≤ 2 * norm`. -/
theorem sq_add_sq_le_two_norm (x : Eis) : x.re * x.re + x.im * x.im ≤ 2 * norm x := by
  unfold norm; nlinarith [sq_nonneg (x.re - x.im)]

/-- The finite set of Eisenstein integers of a given norm `M` (as a natural number). -/
def normFinset (M : ℕ) : Finset Eis :=
  ((Finset.Icc (-(M:ℤ)) M) ×ˢ (Finset.Icc (-(M:ℤ)) M)).image (fun p => ⟨p.1, p.2⟩)
    |>.filter (fun x => norm x = M)

theorem mem_normFinset {M : ℕ} {x : Eis} : x ∈ normFinset M ↔ norm x = M := by
  unfold normFinset
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_image]
    refine ⟨(x.re, x.im), ?_, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    have hb := sq_add_sq_le_two_norm x
    have hn : norm x = (M:ℤ) := h
    have hM : (0:ℤ) ≤ M := Int.natCast_nonneg M
    constructor <;> constructor <;> nlinarith [sq_nonneg x.re, sq_nonneg x.im, hb, hn, hM]

/-- Natural-number norm is multiplicative. -/
theorem natAbs_norm_mul (x y : Eis) :
    (norm (x * y)).natAbs = (norm x).natAbs * (norm y).natAbs := by
  rw [norm_mul, Int.natAbs_mul]

theorem norm_eq_of_associated {x y : Eis} (h : Associated x y) : norm x = norm y := by
  obtain ⟨u, rfl⟩ := h
  have : norm (↑u : Eis) = 1 := isUnit_iff_norm_eq_one.mp u.isUnit
  rw [norm_mul, this, mul_one]

theorem natCast_re (M : ℕ) : ((M : Eis)).re = (M : ℤ) := by
  induction M with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, add_re, ih, one_re]; push_cast; ring

theorem natCast_im (M : ℕ) : ((M : Eis)).im = 0 := by
  induction M with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, add_im, ih, one_im]; ring

theorem natAbs_norm_cast (M : ℕ) : (norm (M : Eis)).natAbs = M * M := by
  unfold norm
  rw [natCast_re, natCast_im]
  simp [Int.natAbs_mul]

theorem natAbs_norm_dvd {x y : Eis} (h : x ∣ y) :
    (norm x).natAbs ∣ (norm y).natAbs := by
  obtain ⟨c, rfl⟩ := h
  rw [natAbs_norm_mul]; exact Dvd.intro _ rfl

/-- Key factorisation: if `norm α = M₁ * M₂` with `M₁, M₂` coprime, then `α` factors
    accordingly. -/
theorem exists_norm_split {α : Eis} (hα : α ≠ 0) {M₁ M₂ : ℕ}
    (hnorm : (norm α).natAbs = M₁ * M₂) (hcop : Nat.Coprime M₁ M₂) :
    ∃ β γ, α = β * γ ∧ (norm β).natAbs = M₁ ∧ (norm γ).natAbs = M₂ := by
  set β := gcd α ((M₁ : ℕ) : Eis) with hβ
  set δ := gcd α ((M₂ : ℕ) : Eis) with hδ
  have hβα : β ∣ α := gcd_dvd_left _ _
  have hδα : δ ∣ α := gcd_dvd_left _ _
  have hβM : β ∣ ((M₁ : ℕ) : Eis) := gcd_dvd_right _ _
  have hδM : δ ∣ ((M₂ : ℕ) : Eis) := gcd_dvd_right _ _
  set g := (norm β).natAbs with hg
  set g' := (norm δ).natAbs with hg'
  -- g ∣ M₁
  have hgα : g ∣ M₁ * M₂ := hnorm ▸ natAbs_norm_dvd hβα
  have hgM : g ∣ M₁ * M₁ := (natAbs_norm_cast M₁) ▸ natAbs_norm_dvd hβM
  have hgM1 : g ∣ M₁ := by
    have : g ∣ Nat.gcd (M₁ * M₂) (M₁ * M₁) := Nat.dvd_gcd hgα hgM
    rwa [Nat.gcd_mul_left, hcop.symm.gcd_eq_one, mul_one] at this
  -- g' ∣ M₂
  have hg'α : g' ∣ M₁ * M₂ := hnorm ▸ natAbs_norm_dvd hδα
  have hg'M : g' ∣ M₂ * M₂ := (natAbs_norm_cast M₂) ▸ natAbs_norm_dvd hδM
  have hgM2 : g' ∣ M₂ := by
    have : g' ∣ Nat.gcd (M₁ * M₂) (M₂ * M₂) := Nat.dvd_gcd hg'α hg'M
    rwa [show M₁ * M₂ = M₂ * M₁ by ring, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one] at this
  -- α associated to β * δ
  have hcopE : IsCoprime ((M₁ : ℕ) : Eis) ((M₂ : ℕ) : Eis) := by
    have : IsCoprime (M₁ : ℤ) (M₂ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hcop)
    have := this.map (Int.castRingHom Eis)
    simpa using this
  have hrel : IsRelPrime β δ :=
    (hcopE.isRelPrime).of_dvd_left hβM |>.of_dvd_right hδM
  have hβδα : β * δ ∣ α := hrel.mul_dvd hβα hδα
  have hαβδ : α ∣ β * δ := by
    have hcast : ((M₁ : ℕ) : Eis) * ((M₂ : ℕ) : Eis) = ((M₁ * M₂ : ℕ) : Eis) := by
      push_cast; ring
    have hαprod : α ∣ ((M₁ : ℕ) : Eis) * ((M₂ : ℕ) : Eis) := by
      rw [hcast]
      refine ⟨conj α, ?_⟩
      have hn : norm α = ((M₁ * M₂ : ℕ) : ℤ) := by
        have := Int.natAbs_of_nonneg (norm_nonneg α)
        rw [hnorm] at this; push_cast at this ⊢; omega
      have := mul_conj α
      rw [this, hn]
      ext <;> simp [natCast_re, natCast_im]
    calc α ∣ gcd α (((M₁ : ℕ) : Eis) * ((M₂ : ℕ) : Eis)) := dvd_gcd (dvd_refl _) hαprod
      _ ∣ β * δ := gcd_mul_dvd_mul_gcd _ _ _
  have hassoc : Associated α (β * δ) := associated_of_dvd_dvd hαβδ hβδα
  -- so g * g' = M₁ * M₂
  have hgg : g * g' = M₁ * M₂ := by
    have hna := norm_eq_of_associated hassoc
    have h2 : (norm α).natAbs = (norm (β * δ)).natAbs := by rw [hna]
    rw [natAbs_norm_mul, hnorm] at h2
    exact h2.symm
  -- positivity of M₁, M₂
  have hMpos : 0 < M₁ * M₂ := by
    rw [← hnorm]; exact Int.natAbs_pos.mpr (fun h => hα (norm_eq_zero.mp h))
  have hM1 : 0 < M₁ := Nat.pos_of_mul_pos_left (by rwa [mul_comm] at hMpos)
  have hM2 : 0 < M₂ := Nat.pos_of_mul_pos_left hMpos
  -- conclude g = M₁
  have hg'le : g' ≤ M₂ := Nat.le_of_dvd hM2 hgM2
  have hgle : g ≤ M₁ := Nat.le_of_dvd hM1 hgM1
  have step : M₁ * M₂ ≤ g * M₂ := by rw [← hgg]; exact Nat.mul_le_mul_left g hg'le
  have hgeq : g = M₁ := le_antisymm hgle (Nat.le_of_mul_le_mul_right step hM2)
  -- produce the factorisation
  obtain ⟨γ₀, hγ₀⟩ := hβα
  refine ⟨β, γ₀, hγ₀, hgeq, ?_⟩
  have hprod : g * (norm γ₀).natAbs = M₁ * M₂ := by
    have : (norm α).natAbs = (norm β).natAbs * (norm γ₀).natAbs := by
      rw [hγ₀, natAbs_norm_mul]
    rw [hnorm] at this; rw [hg]; omega
  rw [hgeq] at hprod
  exact Nat.eq_of_mul_eq_mul_left hM1 hprod

/-- Coprime norms ⇒ `IsRelPrime`. -/
theorem isRelPrime_of_coprime_norm {x y : Eis}
    (h : Nat.Coprime (norm x).natAbs (norm y).natAbs) : IsRelPrime x y := by
  intro d hdx hdy
  rw [isUnit_iff_norm_eq_one]
  have h1 : (norm d).natAbs ∣ (norm x).natAbs := natAbs_norm_dvd hdx
  have h2 : (norm d).natAbs ∣ (norm y).natAbs := natAbs_norm_dvd hdy
  have hdvd := Nat.dvd_gcd h1 h2
  rw [h.gcd_eq_one] at hdvd
  have hnd : (norm d).natAbs = 1 := Nat.dvd_one.mp hdvd
  have hd0 := norm_nonneg d
  omega

end Eis

namespace Eis

theorem card_normFinset_one : (normFinset 1).card = 6 := by decide

theorem norm_eq_cast_of_natAbs {x : Eis} {M : ℕ} (h : (norm x).natAbs = M) :
    norm x = (M : ℤ) := by
  have := Int.natAbs_of_nonneg (norm_nonneg x); rw [h] at this; omega

theorem mem_normFinset_natAbs {M : ℕ} {x : Eis} : x ∈ normFinset M ↔ (norm x).natAbs = M := by
  rw [mem_normFinset]
  constructor
  · intro h; rw [h]; simp
  · intro h; exact norm_eq_cast_of_natAbs h

/-- Multiplicativity of the representation count, with the factor `6 = #units`. -/
theorem card_normFinset_mul {M₁ M₂ : ℕ} (hcop : Nat.Coprime M₁ M₂)
    (hM1 : M₁ ≠ 0) (hM2 : M₂ ≠ 0) :
    (normFinset M₁).card * (normFinset M₂).card = 6 * (normFinset (M₁ * M₂)).card := by
  have H : ∀ p ∈ (normFinset M₁ ×ˢ normFinset M₂), p.1 * p.2 ∈ normFinset (M₁ * M₂) := by
    rintro ⟨β, γ⟩ hp
    rw [Finset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [mem_normFinset_natAbs] at h1 h2 ⊢
    rw [natAbs_norm_mul, h1, h2]
  -- each fiber has 6 elements
  have fiber6 : ∀ α ∈ normFinset (M₁ * M₂),
      ((normFinset M₁ ×ˢ normFinset M₂).filter (fun p => p.1 * p.2 = α)).card = 6 := by
    intro α hα
    rw [mem_normFinset_natAbs] at hα
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [show norm 0 = 0 from rfl] at hα; simp at hα
      exact hM1 (by omega) -- M₁*M₂ = 0 impossible
    obtain ⟨β₀, γ₀, hβγ, hnβ, hnγ⟩ := exists_norm_split hα0 hα hcop
    have hβ00 : β₀ ≠ 0 := by rintro rfl; simp [norm] at hnβ; exact hM1 hnβ.symm
    rw [← card_normFinset_one]
    symm
    apply Finset.card_bij (fun w _ => (w * β₀, (conj w) * γ₀))
    · -- maps into fiber
      intro w hw
      rw [mem_normFinset] at hw
      have hwn : norm w = 1 := hw
      have hconj : w * conj w = 1 := by rw [mul_conj, hwn]; rfl
      rw [Finset.mem_filter, Finset.mem_product, mem_normFinset_natAbs, mem_normFinset_natAbs]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [natAbs_norm_mul, hnβ, show (norm w).natAbs = 1 from by rw [hwn]; rfl, one_mul]
      · rw [natAbs_norm_mul, hnγ, show (norm (conj w)).natAbs = 1 from by rw [norm_conj, hwn]; rfl,
          one_mul]
      · show w * β₀ * (conj w * γ₀) = α
        rw [hβγ]
        calc w * β₀ * (conj w * γ₀) = (w * conj w) * (β₀ * γ₀) := by ring
          _ = β₀ * γ₀ := by rw [hconj, one_mul]
    · -- injective
      intro w1 hw1 w2 hw2 heq
      have : w1 * β₀ = w2 * β₀ := (Prod.ext_iff.mp heq).1
      exact mul_right_cancel₀ hβ00 this
    · -- surjective
      rintro ⟨β, γ⟩ hp
      rw [Finset.mem_filter, Finset.mem_product, mem_normFinset_natAbs, mem_normFinset_natAbs] at hp
      obtain ⟨⟨hnβ', hnγ'⟩, hprod⟩ := hp
      have hrel1 : IsRelPrime β γ₀ :=
        isRelPrime_of_coprime_norm (by rw [hnβ', hnγ]; exact hcop)
      have hrel2 : IsRelPrime β₀ γ :=
        isRelPrime_of_coprime_norm (by rw [hnβ, hnγ']; exact hcop)
      have hβdvd : β ∣ β₀ := by
        have : β ∣ β₀ * γ₀ := by rw [← hβγ, ← hprod]; exact dvd_mul_right β γ
        exact hrel1.dvd_of_dvd_mul_right this
      have hβ0dvd : β₀ ∣ β := by
        have : β₀ ∣ β * γ := by rw [hprod, hβγ]; exact dvd_mul_right β₀ γ₀
        exact hrel2.dvd_of_dvd_mul_right this
      obtain ⟨u, hu⟩ := associated_of_dvd_dvd hβdvd hβ0dvd
      -- hu : β * ↑u = β₀
      refine ⟨conj (↑u : Eis), ?_, ?_⟩
      · rw [mem_normFinset]
        have : norm β * norm (↑u:Eis) = norm β₀ := by rw [← norm_mul, hu]
        have hnβ0 : norm β₀ = norm β := by
          rw [norm_eq_cast_of_natAbs hnβ, norm_eq_cast_of_natAbs hnβ']
        have hu1 : norm (↑u:Eis) = 1 := isUnit_iff_norm_eq_one.mp u.isUnit
        show norm (conj (↑u:Eis)) = 1
        rw [norm_conj, hu1]
      · have hu1 : norm (↑u:Eis) = 1 := isUnit_iff_norm_eq_one.mp u.isUnit
        have huc : (↑u:Eis) * conj (↑u) = 1 := by rw [mul_conj, hu1]; rfl
        have hconjconj : conj (conj (↑u:Eis)) = ↑u := by ext <;> simp [conj]
        -- hu : β * ↑u = β₀
        have hβeq : conj (↑u:Eis) * β₀ = β := by
          rw [← hu]
          calc conj (↑u:Eis) * (β * ↑u) = (conj (↑u) * ↑u) * β := by ring
            _ = β := by rw [show conj (↑u:Eis) * ↑u = 1 from by rw [mul_comm]; exact huc, one_mul]
        have e : conj (↑u:Eis) * β₀ * γ = β₀ * γ₀ := by
          have h0 : β * γ = β₀ * γ₀ := by rw [hprod, hβγ]
          rw [← hβeq] at h0; exact h0
        have key : β₀ * γ = β₀ * ((↑u:Eis) * γ₀) := by
          calc β₀ * γ = ((↑u:Eis) * conj (↑u)) * (β₀ * γ) := by rw [huc, one_mul]
            _ = (↑u:Eis) * (conj (↑u) * β₀ * γ) := by ring
            _ = (↑u:Eis) * (β₀ * γ₀) := by rw [e]
            _ = β₀ * ((↑u:Eis) * γ₀) := by ring
        have hγeq : (↑u:Eis) * γ₀ = γ := (mul_left_cancel₀ hβ00 key).symm
        show (conj (↑u:Eis) * β₀, conj (conj (↑u:Eis)) * γ₀) = (β, γ)
        rw [hconjconj, Prod.ext_iff]; exact ⟨hβeq, hγeq⟩
  rw [← Finset.card_product, Finset.card_eq_sum_card_fiberwise H,
    Finset.sum_congr rfl fiber6, Finset.sum_const, smul_eq_mul, mul_comm]

/-- For `p ≡ 1 mod 3` prime, there is a cube root of unity `m` mod `p`. -/
theorem exists_cube_root (p : ℕ) [hp : Fact p.Prime] (h : p % 3 = 1) :
    ∃ m : ℤ, (p : ℤ) ∣ m * m + m + 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨g0, hg0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  rw [hcard] at hg0
  have h3d : (3 : ℕ) ∣ (p - 1) := by omega
  set g := g0 ^ ((p - 1) / 3) with hgdef
  have hgord : orderOf g = 3 := by
    rw [hgdef, orderOf_pow, hg0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd h3d),
      Nat.div_div_self h3d (by omega)]
  have hg3 : g ^ 3 = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hgord; norm_num at hgord
  set y : ZMod p := (↑g : ZMod p) with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hfac : (y - 1) * (y ^ 2 + y + 1) = 0 := by ring_nf; linear_combination hy3
  have hy1 : y ≠ 1 := by
    intro h1
    exact hg1 (Units.ext (by rw [Units.val_one]; rw [← hy]; exact h1))
  have hy2 : y ^ 2 + y + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact absurd (sub_eq_zero.mp h') hy1
    · exact h'
  refine ⟨(y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  linear_combination hy2

/-- `⟨m, -1⟩` has norm `m² + m + 1`. -/
theorem norm_mk_neg_one (m : ℤ) : norm ⟨m, -1⟩ = m * m + m + 1 := by unfold norm; ring

/-- For a prime `p ≡ 1 mod 3`, there is an Eisenstein integer of norm `p`. -/
theorem exists_norm_eq_prime (p : ℕ) [hp : Fact p.Prime] (h : p % 3 = 1) :
    ∃ β : Eis, (norm β).natAbs = p := by
  obtain ⟨m, hm⟩ := exists_cube_root p h
  set x : Eis := ⟨m, -1⟩ with hx
  have hxnorm : norm x = m * m + m + 1 := norm_mk_neg_one m
  -- p ∣ norm x, but p ∤ x, so p is not prime in Eis
  have hpdvd : (p : ℤ) ∣ norm x := by rw [hxnorm]; exact hm
  have hp_notprime : ¬ Prime (p : Eis) := by
    intro hpp
    -- p ∣ x * conj x
    have : (p : Eis) ∣ x * conj x := by
      rw [mul_conj]
      have : (p : ℤ) ∣ (norm x) := hpdvd
      obtain ⟨c, hc⟩ := this
      exact ⟨⟨c, 0⟩, by rw [hc]; ext <;> simp [natCast_re, natCast_im]⟩
    rcases hpp.dvd_or_dvd this with hd | hd
    · -- p ∣ x means p ∣ im = -1
      obtain ⟨c, hc⟩ := hd
      have him : (-1 : ℤ) = (p : ℤ) * c.im := by
        have h2 := congrArg Eis.im hc
        simp only [hx, mul_im, natCast_re, natCast_im] at h2
        linarith [h2]
      have hdvd1 : (p : ℤ) ∣ 1 := ⟨-c.im, by rw [mul_neg]; linarith [him]⟩
      have hle := Int.le_of_dvd one_pos hdvd1
      have h2le := hp.out.two_le
      omega
    · -- p ∣ conj x means p ∣ im = 1
      obtain ⟨c, hc⟩ := hd
      have him : (1 : ℤ) = (p : ℤ) * c.im := by
        have h2 := congrArg Eis.im hc
        simp only [hx, conj_im, mul_im, natCast_re, natCast_im] at h2
        linarith [h2]
      have hdvd1 : (p : ℤ) ∣ 1 := ⟨c.im, by linarith [him]⟩
      have hle := Int.le_of_dvd one_pos hdvd1
      have h2le := hp.out.two_le
      omega
  -- p not prime ⇒ p reducible (p ≠ 0, not unit) ⇒ ∃ factor of norm p
  have hp0 : (p : Eis) ≠ 0 := by
    intro h
    have h1 : (norm (p : Eis)).natAbs = p * p := natAbs_norm_cast p
    rw [h] at h1
    have h2 : norm (0 : Eis) = 0 := by unfold norm; simp
    rw [h2, Int.natAbs_zero] at h1
    nlinarith [hp.out.two_le, h1]
  have hnotunit : ¬ IsUnit (p : Eis) := by
    rw [isUnit_iff_norm_eq_one]
    intro hn1
    have h1 : (norm (p : Eis)).natAbs = p * p := natAbs_norm_cast p
    rw [hn1] at h1
    simp only [Int.natAbs_one] at h1
    nlinarith [hp.out.two_le, h1]
  have hirr : ¬ Irreducible (p : Eis) := by
    rw [irreducible_iff_prime]; exact hp_notprime
  have hred : ∃ a b : Eis, (p : Eis) = a * b ∧ ¬IsUnit a ∧ ¬IsUnit b := by
    by_contra hcon
    push_neg at hcon
    apply hirr
    rw [irreducible_iff]
    refine ⟨hnotunit, ?_⟩
    intro a b hab
    rw [or_iff_not_imp_left]
    intro hna
    exact hcon a b hab hna
  obtain ⟨a, b, hab, hna, hnb⟩ := hred
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hab; exact hp0 hab
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hab; exact hp0 hab
  have hNApos : 0 < (norm a).natAbs := by
    rw [Int.natAbs_pos]; exact (norm_pos_of_ne_zero ha0).ne'
  have hNBpos : 0 < (norm b).natAbs := by
    rw [Int.natAbs_pos]; exact (norm_pos_of_ne_zero hb0).ne'
  have hNA1 : (norm a).natAbs ≠ 1 := by
    intro hc
    apply hna
    rw [isUnit_iff_norm_eq_one]
    have := norm_pos_of_ne_zero ha0
    omega
  have hNB1 : (norm b).natAbs ≠ 1 := by
    intro hc
    apply hnb
    rw [isUnit_iff_norm_eq_one]
    have := norm_pos_of_ne_zero hb0
    omega
  have hprod : (norm a).natAbs * (norm b).natAbs = p * p := by
    rw [← natAbs_norm_mul, ← hab]; exact natAbs_norm_cast p
  have hdvd : (norm a).natAbs ∣ p ^ 2 := ⟨(norm b).natAbs, by rw [pow_two]; exact hprod.symm⟩
  obtain ⟨i, hi, hpi⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  interval_cases i
  · exfalso; rw [pow_zero] at hpi; omega
  · exact ⟨a, by rw [hpi, pow_one]⟩
  · exfalso
    rw [hpi] at hprod
    rw [← pow_two] at hprod
    have hNB1' : (norm b).natAbs = 1 := by
      have heq : p ^ 2 * (norm b).natAbs = p ^ 2 * 1 := by rw [mul_one]; exact hprod
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos 2) heq
    omega

end Eis
