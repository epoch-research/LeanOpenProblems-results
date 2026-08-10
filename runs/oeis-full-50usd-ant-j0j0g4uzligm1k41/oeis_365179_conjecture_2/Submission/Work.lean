import Mathlib
open Nat
set_option maxRecDepth 100000

namespace Disproof

abbrev Z := ZMod 27

def fexp (j : Z) : Z := 7 ^ j.val
def carry (j l : Z) : Z := if 27 ≤ j.val + l.val then (9:Z) else 0

lemma fexp_add (j l : Z) : fexp (j + l) = fexp j * fexp l := by revert j l; decide
lemma fexp_carry (j l n : Z) : fexp j * carry l n = carry l n := by revert j l n; decide
lemma carry_cocycle (j l n : Z) :
    carry j l + carry (j+l) n = carry l n + carry j (l+n) := by revert j l n; decide

@[ext] structure P where
  i : Z
  j : Z
deriving DecidableEq, Fintype

namespace P

instance : Mul P := ⟨fun p q => ⟨p.i + fexp p.j * q.i + carry p.j q.j, p.j + q.j⟩⟩
instance : One P := ⟨⟨0, 0⟩⟩
instance : Inv P := ⟨fun p => ⟨-(fexp (-p.j) * p.i) - carry (-p.j) p.j, -p.j⟩⟩

@[simp] lemma mul_i (p q : P) : (p * q).i = p.i + fexp p.j * q.i + carry p.j q.j := rfl
@[simp] lemma mul_j (p q : P) : (p * q).j = p.j + q.j := rfl
@[simp] lemma one_i : (1 : P).i = 0 := rfl
@[simp] lemma one_j : (1 : P).j = 0 := rfl

lemma my_mul_assoc (p q r : P) : p * q * r = p * (q * r) := by
  ext
  · show (p.i + fexp p.j * q.i + carry p.j q.j) + fexp (p.j + q.j) * r.i + carry (p.j + q.j) r.j
      = p.i + fexp p.j * (q.i + fexp q.j * r.i + carry q.j r.j) + carry p.j (q.j + r.j)
    have ha := fexp_add p.j q.j
    have hb := fexp_carry p.j q.j r.j
    have hc := carry_cocycle p.j q.j r.j
    linear_combination r.i * ha - hb + hc
  · show (p.j + q.j) + r.j = p.j + (q.j + r.j)
    ring

instance : Group P where
  mul_assoc := my_mul_assoc
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

lemma card_P : Fintype.card P = 729 := by decide

def a : P := ⟨1, 0⟩
def b : P := ⟨0, 1⟩

@[simp] lemma fexp_zero : fexp 0 = 1 := by decide
@[simp] lemma carry_zero_left (l : Z) : carry 0 l = 0 := by revert l; decide

lemma apow (n : ℕ) : a ^ n = ⟨(n : Z), 0⟩ := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, ih]
    apply P.ext
    · show (k : Z) + fexp 0 * 1 + carry 0 0 = ((k + 1 : ℕ) : Z)
      simp
    · show (0 : Z) + 0 = 0
      ring

lemma bpow_small (m : ℕ) (hm : m ≤ 26) : b ^ m = ⟨0, (m : Z)⟩ := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hk : k ≤ 26 := Nat.le_of_succ_le hm
    rw [pow_succ, ih hk]
    apply P.ext
    · show (0 : Z) + fexp (k : Z) * 0 + carry (k : Z) 1 = 0
      have hkv : ((k : Z)).val = k := by
        rw [ZMod.val_natCast]; omega
      have h1 : (1 : Z).val = 1 := by decide
      have hc : carry (k : Z) 1 = 0 := by
        simp only [carry, hkv, h1]
        rw [if_neg]; omega
      rw [hc]; ring
    · show (k : Z) + 1 = ((k + 1 : ℕ) : Z)
      push_cast; ring

lemma coord_eq (i j : Z) : (⟨i, j⟩ : P) = a ^ i.val * b ^ j.val := by
  rw [apow, bpow_small j.val (by have := ZMod.val_lt j; omega)]
  apply P.ext
  · show i = (i.val : Z) + fexp 0 * 0 + carry 0 (j.val : Z)
    simp
  · show j = (0 : Z) + (j.val : Z)
    simp

lemma gen_top : Subgroup.closure ({a, b} : Set P) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨i, j⟩ -
  rw [coord_eq]
  apply Subgroup.mul_mem
  · apply Subgroup.pow_mem
    apply Subgroup.subset_closure
    left; rfl
  · apply Subgroup.pow_mem
    apply Subgroup.subset_closure
    right; rfl

section Endo
variable {x y : P}

lemma xmod (hx : x ^ 27 = 1) (t : ℕ) : x ^ (t % 27) = x ^ t := by
  conv_rhs => rw [← Nat.div_add_mod t 27]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

lemma xpow_natCast (hx : x ^ 27 = 1) (N : ℕ) : x ^ N = x ^ ((N : Z)).val := by
  rw [ZMod.val_natCast]
  exact (xmod hx N).symm

lemma xz_add (hx : x ^ 27 = 1) (e f : Z) :
    x ^ (e + f).val = x ^ e.val * x ^ f.val := by
  rw [ZMod.val_add, xmod hx, pow_add]

lemma conjpow (g : P) (n : ℕ) : (y * g * y⁻¹) ^ n = y * g ^ n * y⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

lemma yx_base (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4) :
    y * x = x ^ 7 * y := by
  have hq : y * x ^ 4 * y⁻¹ = x := by
    have h : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    rwa [hxy] at h
  have h7 : y * x ^ 28 * y⁻¹ = x ^ 7 := by
    have h1 : (y * x ^ 4 * y⁻¹) ^ 7 = x ^ 7 := by rw [hq]
    rw [conjpow, ← pow_mul] at h1
    norm_num at h1
    exact h1
  have hx28 : x ^ 28 = x := by
    rw [show (28 : ℕ) = 27 + 1 by rfl, pow_add, hx, one_mul, pow_one]
  rw [hx28] at h7
  calc y * x = (y * x * y⁻¹) * y := by group
    _ = x ^ 7 * y := by rw [h7]

lemma y_xk (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4) (k : ℕ) :
    y * x ^ k = x ^ (7 * k) * y := by
  induction k with
  | zero => simp
  | succ p ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, yx_base hx hxy, ← mul_assoc, ← pow_add,
        show 7 * (p + 1) = 7 * p + 7 from by ring]

lemma ym_xk (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4) (m k : ℕ) :
    y ^ m * x ^ k = x ^ (7 ^ m * k) * y ^ m := by
  induction m generalizing k with
  | zero => simp
  | succ p ih =>
    have step : y ^ (p + 1) * x ^ k = y * (x ^ (7 ^ p * k) * y ^ p) := by
      rw [_root_.pow_succ', mul_assoc, ih]
    rw [step, ← mul_assoc, y_xk hx hxy, mul_assoc, ← _root_.pow_succ',
        show 7 * (7 ^ p * k) = 7 ^ (p + 1) * k from by ring]

lemma xexp7 (hx : x ^ 27 = 1) (j k : Z) :
    x ^ (7 ^ j.val * k.val) = x ^ (fexp j * k).val := by
  rw [xpow_natCast hx (7 ^ j.val * k.val)]
  congr 1
  congr 1
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  rfl

lemma yval_carry (hy : y ^ 27 = x ^ 9) (j l : Z) :
    x ^ (carry j l).val * y ^ (j + l).val = y ^ (j.val + l.val) := by
  have hjv := ZMod.val_lt j
  have hlv := ZMod.val_lt l
  rcases Nat.lt_or_ge (j.val + l.val) 27 with h | h
  · have hc : carry j l = 0 := by simp only [carry]; rw [if_neg (by omega)]
    rw [hc]
    have : (0 : Z).val = 0 := by decide
    rw [this, pow_zero, one_mul]
    congr 1
    rw [ZMod.val_add, Nat.mod_eq_of_lt (by omega)]
  · have hc : carry j l = 9 := by simp only [carry]; rw [if_pos (by omega)]
    rw [hc]
    have h9 : (9 : Z).val = 9 := by decide
    rw [h9, ← hy, ← pow_add]
    congr 1
    rw [ZMod.val_add]
    omega

def endHom (x y : P) (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4)
    (hy : y ^ 27 = x ^ 9) : P →* P where
  toFun p := x ^ p.i.val * y ^ p.j.val
  map_one' := by
    show x ^ ((1 : P).i).val * y ^ ((1 : P).j).val = 1
    simp only [one_i, one_j]
    have : (0 : Z).val = 0 := by decide
    rw [this, pow_zero, pow_zero, one_mul]
  map_mul' := by
    rintro ⟨i, j⟩ ⟨k, l⟩
    show x ^ (i + fexp j * k + carry j l).val * y ^ (j + l).val
       = x ^ i.val * y ^ j.val * (x ^ k.val * y ^ l.val)
    have e1 : y ^ j.val * x ^ k.val = x ^ (fexp j * k).val * y ^ j.val := by
      rw [ym_xk hx hxy, xexp7 hx]
    symm
    calc x ^ i.val * y ^ j.val * (x ^ k.val * y ^ l.val)
        = x ^ i.val * (y ^ j.val * x ^ k.val) * y ^ l.val := by
          simp only [mul_assoc]
      _ = x ^ i.val * (x ^ (fexp j * k).val * y ^ j.val) * y ^ l.val := by rw [e1]
      _ = x ^ i.val * x ^ (fexp j * k).val * (y ^ j.val * y ^ l.val) := by
          simp only [mul_assoc]
      _ = x ^ (i + fexp j * k).val * y ^ (j.val + l.val) := by
          rw [← xz_add hx, ← pow_add]
      _ = x ^ (i + fexp j * k + carry j l).val * y ^ (j + l).val := by
          rw [xz_add hx (i + fexp j * k) (carry j l), mul_assoc, yval_carry hy]

lemma endHom_a (x y : P) (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4)
    (hy : y ^ 27 = x ^ 9) : endHom x y hx hxy hy a = x := by
  show x ^ (a.i).val * y ^ (a.j).val = x
  have h1 : (a.i).val = 1 := by decide
  have h0 : (a.j).val = 0 := by decide
  rw [h1, h0, pow_zero, pow_one, mul_one]

lemma endHom_b (x y : P) (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4)
    (hy : y ^ 27 = x ^ 9) : endHom x y hx hxy hy b = y := by
  show x ^ (b.i).val * y ^ (b.j).val = y
  have h0 : (b.i).val = 0 := by decide
  have h1 : (b.j).val = 1 := by decide
  rw [h0, h1, pow_zero, pow_one, one_mul]

end Endo

/-- projection to (ZMod 3)^2 (Frattini quotient). -/
def c3 : Z →+* ZMod 3 := ZMod.castHom (by norm_num) (ZMod 3)

lemma c3_fexp (j : Z) : c3 (fexp j) = 1 := by revert j; decide
lemma c3_carry (j l : Z) : c3 (carry j l) = 0 := by revert j l; decide

def pi3 : P →* Multiplicative (ZMod 3 × ZMod 3) where
  toFun p := Multiplicative.ofAdd (c3 p.i, c3 p.j)
  map_one' := by
    show Multiplicative.ofAdd (c3 (1:P).i, c3 (1:P).j) = 1
    simp only [one_i, one_j, map_zero]
    rfl
  map_mul' := by
    rintro ⟨i, j⟩ ⟨k, l⟩
    show Multiplicative.ofAdd (c3 (i + fexp j * k + carry j l), c3 (j + l))
       = Multiplicative.ofAdd (c3 i, c3 j) * Multiplicative.ofAdd (c3 k, c3 l)
    rw [← ofAdd_add]
    congr 1
    rw [Prod.mk_add_mk]
    congr 1
    · rw [map_add, map_add, map_mul, c3_fexp, one_mul, c3_carry, add_zero]
    · rw [map_add]

lemma pi3_a : pi3 a = Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)) := by decide
lemma pi3_b : pi3 b = Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3)) := by decide

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

lemma isPGroup_P : IsPGroup 3 P :=
  IsPGroup.of_card (n := 6) (by norm_num [Nat.card_eq_fintype_card, card_P])

lemma coatom_index_three (M : Subgroup P) (hM : IsCoatom M) : Nat.card (P ⧸ M) = 3 := by
  haveI hnil : Group.IsNilpotent P := isPGroup_P.isNilpotent
  haveI hnorm : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M (normalizerCondition_of_isNilpotent) hM
  have hsurj : Function.Surjective (QuotientGroup.mk' M) := QuotientGroup.mk'_surjective M
  haveI : Nontrivial (P ⧸ M) := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    apply hM.1
    rw [eq_top_iff]
    intro g _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  haveI hsimple : IsSimpleGroup (P ⧸ M) := by
    refine ⟨fun N _ => ?_⟩
    have hMle : M ≤ N.comap (QuotientGroup.mk' M) := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx1 : QuotientGroup.mk' M x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hx1]; exact one_mem N
    have hself : (N.comap (QuotientGroup.mk' M)).map (QuotientGroup.mk' M) = N :=
      Subgroup.map_comap_eq_self_of_surjective hsurj N
    rcases eq_or_lt_of_le hMle with heq | hlt
    · left
      rw [← hself, ← heq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk' M]
    · right
      rw [← hself, hM.2 _ hlt, Subgroup.map_top_of_surjective _ hsurj]
  have hpg : IsPGroup 3 (P ⧸ M) := isPGroup_P.to_quotient M
  have hcenter : Subgroup.center (P ⧸ M) = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (P ⧸ M)) inferInstance with h | h
    · exact absurd h (IsPGroup.bot_lt_center hpg).ne'
    · exact h
  haveI : IsMulCommutative (P ⧸ M) := ⟨⟨fun a b => by
    have ha : a ∈ Subgroup.center (P ⧸ M) := hcenter ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
  have hprime : (Nat.card (P ⧸ M)).Prime := IsSimpleGroup.prime_card
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rw [hk] at hprime ⊢
  have hk1 : k = 1 := hprime.eq_one_of_pow
  rw [hk1, pow_one]

-- Coordinate power formulas (proven by decide over the 729 or 27 elements).
set_option maxHeartbeats 4000000 in
lemma fexp_one_of (j : Z) (h : 3 * j = 0) : fexp j = 1 := by revert j; decide

set_option maxHeartbeats 4000000 in
lemma pow4_j_all (x : P) : (x ^ 4).j = 4 * x.j := by revert x; decide

set_option maxHeartbeats 4000000 in
lemma pow4_restr (x : P) (h : 3 * x.j = 0) : x ^ 4 = ⟨4 * x.i + x.j, 4 * x.j⟩ := by
  revert x; decide

set_option maxHeartbeats 4000000 in
lemma pow9_restr (x : P) (h : 3 * x.j = 0) : x ^ 9 = ⟨9 * x.i, 0⟩ := by
  revert x; decide

set_option maxHeartbeats 4000000 in
lemma pow27_all (x : P) : x ^ 27 = ⟨9 * x.j, 0⟩ := by revert x; decide

lemma R2char (x y : P) :
    y⁻¹ * x * y = x ^ 4 ↔
      (3 * x.j = 0 ∧
        x.i + carry x.j y.j = fexp y.j * (4 * x.i + x.j) + carry y.j (4 * x.j)) := by
  rw [show y⁻¹ * x * y = y⁻¹ * (x * y) from by group, inv_mul_eq_iff_eq_mul]
  constructor
  · intro h
    have hj : (x * y).j = (y * x ^ 4).j := by rw [h]
    rw [mul_j, mul_j, pow4_j_all] at hj
    have h3 : 3 * x.j = 0 := by linear_combination -hj
    refine ⟨h3, ?_⟩
    rw [pow4_restr x h3] at h
    have hi : (x * y).i = (y * (⟨4 * x.i + x.j, 4 * x.j⟩ : P)).i := by rw [h]
    rw [mul_i, mul_i] at hi
    have hf : fexp x.j = 1 := fexp_one_of x.j h3
    rw [hf, one_mul] at hi
    linear_combination hi
  · rintro ⟨h3, hc2⟩
    rw [pow4_restr x h3]
    have hf : fexp x.j = 1 := fexp_one_of x.j h3
    apply P.ext
    · rw [mul_i, mul_i, hf, one_mul]
      show x.i + y.i + carry x.j y.j = y.i + fexp y.j * (4 * x.i + x.j) + carry y.j (4 * x.j)
      linear_combination hc2
    · rw [mul_j, mul_j]
      show x.j + y.j = y.j + 4 * x.j
      linear_combination -h3

lemma R3char (x y : P) (h3 : 3 * x.j = 0) : y ^ 27 = x ^ 9 ↔ 9 * y.j = 9 * x.i := by
  rw [pow27_all, pow9_restr x h3, P.mk.injEq]
  simp

lemma R1char (x : P) (h3 : 3 * x.j = 0) : x ^ 27 = 1 := by
  rw [pow27_all, show (9 : Z) * x.j = 0 from by linear_combination 3 * h3]
  rfl

lemma rel_iff (x y : P) :
    (x ^ 27 = 1 ∧ y⁻¹ * x * y = x ^ 4 ∧ y ^ 27 = x ^ 9) ↔
      (3 * x.j = 0 ∧
        (x.i + carry x.j y.j = fexp y.j * (4 * x.i + x.j) + carry y.j (4 * x.j)) ∧
        9 * y.j = 9 * x.i) := by
  constructor
  · rintro ⟨_, h2, h3r⟩
    obtain ⟨hc1, hc2⟩ := (R2char x y).mp h2
    exact ⟨hc1, hc2, (R3char x y hc1).mp h3r⟩
  · rintro ⟨hc1, hc2, hc3⟩
    exact ⟨R1char x hc1, (R2char x y).mpr ⟨hc1, hc2⟩, (R3char x y hc1).mpr hc3⟩

@[simp] lemma pi3_apply (g : P) :
    pi3 g = Multiplicative.ofAdd (c3 g.i, c3 g.j) := rfl

/-- Projection to the second Frattini coordinate. -/
def pj3 : P →* Multiplicative (ZMod 3) where
  toFun p := Multiplicative.ofAdd (c3 p.j)
  map_one' := by show Multiplicative.ofAdd (c3 (1:P).j) = 1; rw [one_j, map_zero]; rfl
  map_mul' := by
    rintro p q
    show Multiplicative.ofAdd (c3 (p * q).j) = _
    rw [mul_j, map_add, ofAdd_add]

@[simp] lemma pj3_apply (g : P) : pj3 g = Multiplicative.ofAdd (c3 g.j) := rfl

lemma c3_of_3z (w : Z) (h : 3 * w = 0) : c3 w = 0 := by revert w; decide
lemma c3_of_9eq (u w : Z) (h : 9 * u = 9 * w) : c3 u = c3 w := by revert u w; decide
lemma dvd_of_c3_zero (w : Z) (h : c3 w = 0) : 3 ∣ w.val := by revert w; decide

set_option maxHeartbeats 8000000 in
lemma rel_i1_cases (i1 j1 j2 : Z)
    (h : 3 * j1 = 0 ∧ (i1 + carry j1 j2 = fexp j2 * (4 * i1 + j1) + carry j2 (4 * j1)) ∧
          9 * j2 = 9 * i1) : c3 i1 = 0 ∨ c3 i1 = 1 := by
  revert i1 j1 j2; decide

lemma smul_lemma (v : ZMod 3) :
    ((v, (1 : ZMod 3)) : ZMod 3 × ZMod 3) + (2 * v.val) • ((1 : ZMod 3), (0 : ZMod 3)) = (0, 1) := by
  revert v; decide

/-- Membership predicate for the relations satisfied by an automorphism image. -/
abbrev relP (x y : P) : Prop := x ^ 27 = 1 ∧ y⁻¹ * x * y = x ^ 4 ∧ y ^ 27 = x ^ 9

lemma cube_mem_coatom (M : Subgroup P) (hM : IsCoatom M) (g : P) : g ^ 3 ∈ M := by
  haveI hnil : Group.IsNilpotent P := isPGroup_P.isNilpotent
  haveI hnorm : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M (normalizerCondition_of_isNilpotent) hM
  haveI : Fintype (P ⧸ M) := Fintype.ofFinite _
  have hc := coatom_index_three M hM
  have hcard : Fintype.card (P ⧸ M) = 3 := by rw [← Nat.card_eq_fintype_card]; exact hc
  have h1 : (QuotientGroup.mk' M g) ^ 3 = 1 := by rw [← hcard]; exact pow_card_eq_one
  rw [← map_pow] at h1
  rw [QuotientGroup.mk'_apply] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

lemma ker_pi3_le_frattini : pi3.ker ≤ frattini P := by
  rw [frattini, Order.radical]
  apply le_iInf₂
  intro M hM
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h0 : (c3 g.i, c3 g.j) = ((0 : ZMod 3), (0 : ZMod 3)) := by
    have he : Multiplicative.ofAdd (c3 g.i, c3 g.j)
        = Multiplicative.ofAdd ((0 : ZMod 3), (0 : ZMod 3)) := by
      rw [← pi3_apply, hg]; rfl
    exact Multiplicative.ofAdd.injective he
  have hcij : c3 g.i = 0 ∧ c3 g.j = 0 := Prod.mk.injEq .. ▸ h0
  have hi : 3 ∣ g.i.val := dvd_of_c3_zero g.i hcij.1
  have hj : 3 ∣ g.j.val := dvd_of_c3_zero g.j hcij.2
  have hgc : g = a ^ g.i.val * b ^ g.j.val := coord_eq g.i g.j
  have haM : a ^ 3 ∈ M := cube_mem_coatom M hM a
  have hbM : b ^ 3 ∈ M := cube_mem_coatom M hM b
  rw [hgc]
  apply Subgroup.mul_mem
  · obtain ⟨k, hk⟩ := hi
    rw [hk, pow_mul]
    exact Subgroup.pow_mem M haM k
  · obtain ⟨k, hk⟩ := hj
    rw [hk, pow_mul]
    exact Subgroup.pow_mem M hbM k

lemma gen_backward (x y : P) (hrel : relP x y) (hx : c3 x.i = 1) :
    Subgroup.closure ({x, y} : Set P) = ⊤ := by
  obtain ⟨hc1, hc2, hc3⟩ := (rel_iff x y).mp hrel
  have hxj : c3 x.j = 0 := c3_of_3z x.j hc1
  have hyj : c3 y.j = 1 := by rw [c3_of_9eq y.j x.i hc3]; exact hx
  set C := Subgroup.closure ({x, y} : Set P) with hC
  have hxC : x ∈ C := Subgroup.subset_closure (by left; rfl)
  have hyC : y ∈ C := Subgroup.subset_closure (by right; rfl)
  have hkerF := ker_pi3_le_frattini
  have haF : a ∈ C ⊔ frattini P := by
    have hpa : pi3 x = pi3 a := by rw [pi3_apply, pi3_a, hx, hxj]
    have hker : x⁻¹ * a ∈ pi3.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpa, inv_mul_cancel]
    have hax : a = x * (x⁻¹ * a) := by group
    rw [hax]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxC) (Subgroup.mem_sup_right (hkerF hker))
  have hbF : b ∈ C ⊔ frattini P := by
    set v := c3 y.i with hv
    set w := y * x ^ (2 * v.val) with hw
    have hwC : w ∈ C := Subgroup.mul_mem _ hyC (Subgroup.pow_mem _ hxC _)
    have hpw : pi3 w = pi3 b := by
      rw [hw, map_mul, map_pow, pi3_b, pi3_apply, pi3_apply, hx, hxj, hyj]
      rw [← ofAdd_nsmul, ← ofAdd_add]
      congr 1
      exact smul_lemma v
    have hker : w⁻¹ * b ∈ pi3.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpw, inv_mul_cancel]
    have hbw : b = w * (w⁻¹ * b) := by group
    rw [hbw]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwC) (Subgroup.mem_sup_right (hkerF hker))
  have hCF : C ⊔ frattini P = ⊤ := by
    rw [eq_top_iff, ← gen_top, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact haF
    · exact hbF
  exact frattini_nongenerating hCF

lemma gen_forward (x y : P) (hrel : relP x y)
    (hgen : Subgroup.closure ({x, y} : Set P) = ⊤) : c3 x.i = 1 := by
  obtain ⟨hc1, hc2, hc3⟩ := (rel_iff x y).mp hrel
  have hxj : c3 x.j = 0 := c3_of_3z x.j hc1
  have hyj : c3 y.j = c3 x.i := c3_of_9eq y.j x.i hc3
  rcases rel_i1_cases x.i x.j y.j ⟨hc1, hc2, hc3⟩ with h0 | h1
  · exfalso
    have hpx : pj3 x = 1 := by rw [pj3_apply, hxj]; rfl
    have hpy : pj3 y = 1 := by rw [pj3_apply, hyj, h0]; rfl
    have hle : Subgroup.closure ({x, y} : Set P) ≤ pj3.ker := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact MonoidHom.mem_ker.mpr hpx
      · exact MonoidHom.mem_ker.mpr hpy
    rw [hgen, top_le_iff] at hle
    have hb : pj3 b = 1 := by rw [← MonoidHom.mem_ker, hle]; trivial
    rw [pj3_apply, show (b : P).j = (1 : Z) from rfl,
        show c3 (1 : Z) = (1 : ZMod 3) from by decide, ofAdd_eq_one] at hb
    exact absurd hb (by decide)
  · exact h1

lemma relP_ab : relP a b := by decide

/-- Coordinate form of the relations. -/
abbrev relCoordCond (i1 j1 j2 : Z) : Prop :=
  3 * j1 = 0 ∧ (i1 + carry j1 j2 = fexp j2 * (4 * i1 + j1) + carry j2 (4 * j1)) ∧ 9 * j2 = 9 * i1

lemma relP_iff (x y : P) : relP x y ↔ relCoordCond x.i x.j y.j := rel_iff x y

lemma autToPair_relP (f : MulAut P) : relP (f a) (f b) := by
  obtain ⟨h1, h2, h3⟩ := relP_ab
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, h2, map_pow]
  · rw [← map_pow, h3, map_pow]

lemma autToPair_gen (f : MulAut P) : Subgroup.closure ({f a, f b} : Set P) = ⊤ := by
  have himg : ({f a, f b} : Set P) = (f : P →* P) '' ({a, b} : Set P) := by
    rw [Set.image_pair]; rfl
  rw [himg, ← MonoidHom.map_closure, gen_top]
  exact Subgroup.map_top_of_surjective _ (EquivLike.surjective f)

lemma aut_ext {f ψ : MulAut P} (ha : f a = ψ a) (hb : f b = ψ b) : f = ψ := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense gen_top
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact ha
  · exact hb

lemma endHom_surjective {x y : P} (hx : x ^ 27 = 1) (hxy : y⁻¹ * x * y = x ^ 4)
    (hy : y ^ 27 = x ^ 9) (hgen : Subgroup.closure ({x, y} : Set P) = ⊤) :
    Function.Surjective (endHom x y hx hxy hy) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_eq_map]
  conv_lhs => rw [← gen_top]
  rw [MonoidHom.map_closure]
  have himg : (endHom x y hx hxy hy) '' ({a, b} : Set P) = ({x, y} : Set P) := by
    rw [Set.image_pair, endHom_a, endHom_b]
  rw [himg, hgen]

noncomputable def autEquiv :
    MulAut P ≃ {p : P × P // relP p.1 p.2 ∧ c3 p.1.i = 1} where
  toFun f := ⟨(f a, f b),
    autToPair_relP f, gen_forward (f a) (f b) (autToPair_relP f) (autToPair_gen f)⟩
  invFun q := MulEquiv.ofBijective
    (endHom q.1.1 q.1.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2)
    (Finite.surjective_iff_bijective.mp
      (endHom_surjective q.2.1.1 q.2.1.2.1 q.2.1.2.2
        (gen_backward q.1.1 q.1.2 q.2.1 q.2.2)))
  left_inv f := by
    apply aut_ext
    · simp only [MulEquiv.ofBijective_apply]; exact endHom_a _ _ _ _ _
    · simp only [MulEquiv.ofBijective_apply]; exact endHom_b _ _ _ _ _
  right_inv q := by
    apply Subtype.ext
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · simp only [MulEquiv.ofBijective_apply]; exact endHom_a _ _ _ _ _
    · simp only [MulEquiv.ofBijective_apply]; exact endHom_b _ _ _ _ _

def countEquiv :
    {p : P × P // relP p.1 p.2 ∧ c3 p.1.i = 1} ≃
      ({t : Z × Z × Z // relCoordCond t.1 t.2.1 t.2.2 ∧ c3 t.1 = 1} × Z) where
  toFun p := (⟨(p.1.1.i, p.1.1.j, p.1.2.j), (relP_iff p.1.1 p.1.2).mp p.2.1, p.2.2⟩, p.1.2.i)
  invFun q := ⟨(⟨q.1.1.1, q.1.1.2.1⟩, ⟨q.2, q.1.1.2.2⟩), (relP_iff _ _).mpr q.1.2.1, q.1.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv q := by
    rw [Prod.ext_iff]
    refine ⟨?_, rfl⟩
    apply Subtype.ext; rfl

set_option maxHeartbeats 8000000 in
lemma card_triples :
    Fintype.card {t : Z × Z × Z // relCoordCond t.1 t.2.1 t.2.2 ∧ c3 t.1 = 1} = 81 := by
  decide

lemma card_aut : Fintype.card (MulAut P) = 2187 := by
  rw [Fintype.card_congr autEquiv, Fintype.card_congr countEquiv, Fintype.card_prod,
    card_triples, show Fintype.card Z = 27 from by rw [ZMod.card]]

/-! ### The coprime product `C₂ × P` -/

abbrev C := Multiplicative (ZMod 2)
abbrev G := C × P

lemma C_odd (c : C) : c ^ 729 = c := by revert c; decide
lemma C_sq (c : C) : c ^ 2 = 1 := by revert c; decide
lemma hC_cases (c : C) : c = 1 ∨ c = Multiplicative.ofAdd (1 : ZMod 2) := by revert c; decide
lemma hz_ne : (Multiplicative.ofAdd (1 : ZMod 2) : C) ≠ 1 := by decide

lemma P_pow_card (p : P) : p ^ 729 = 1 := by
  have h : p ^ (Fintype.card P) = 1 := pow_card_eq_one
  rwa [card_P] at h

lemma P_sq_eq_one (p : P) (h : p ^ 2 = 1) : p = 1 := by
  have h2 : orderOf p ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have h729 : orderOf p ∣ 729 := by rw [← card_P]; exact orderOf_dvd_card
  have hg : orderOf p ∣ Nat.gcd 2 729 := Nat.dvd_gcd h2 h729
  rw [show Nat.gcd 2 729 = 1 from by decide] at hg
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.mp hg

lemma prod_pow_fst (g : C × P) (n : ℕ) : (g ^ n).1 = g.1 ^ n :=
  map_pow (MonoidHom.fst C P) g n
lemma prod_pow_snd (g : C × P) (n : ℕ) : (g ^ n).2 = g.2 ^ n :=
  map_pow (MonoidHom.snd C P) g n

lemma G_mem_P (g : C × P) : g ^ 729 = 1 ↔ g.1 = 1 := by
  constructor
  · intro h
    have h1 : g.1 ^ 729 = 1 := by rw [← prod_pow_fst, h]; rfl
    rwa [C_odd] at h1
  · intro h
    apply Prod.ext
    · rw [prod_pow_fst, C_odd, h]; rfl
    · rw [prod_pow_snd, P_pow_card]; rfl

lemma G_mem_C (g : C × P) : g ^ 2 = 1 ↔ g.2 = 1 := by
  constructor
  · intro h
    have h2 : g.2 ^ 2 = 1 := by rw [← prod_pow_snd, h]; rfl
    exact P_sq_eq_one g.2 h2
  · intro h
    apply Prod.ext
    · rw [prod_pow_fst, C_sq]; rfl
    · rw [prod_pow_snd, h, one_pow]; rfl

lemma theta_preserves_P (Θ : MulAut G) (p : P) : (Θ (1, p)).1 = 1 := by
  rw [← G_mem_P, ← map_pow, (G_mem_P (1, p)).mpr rfl, map_one]

lemma theta_preserves_C (Θ : MulAut G) (c : C) : (Θ (c, 1)).2 = 1 := by
  rw [← G_mem_C, ← map_pow, (G_mem_C (c, 1)).mpr rfl, map_one]

lemma chi_eq (Θ : MulAut G) (c : C) : (Θ (c, 1)).1 = c := by
  have hinj : Function.Injective (fun c : C => (Θ (c, 1)).1) := by
    intro c c' hcc
    have hh : Θ (c, 1) = Θ (c', 1) :=
      Prod.ext hcc (by rw [theta_preserves_C, theta_preserves_C])
    have := Θ.injective hh
    exact (Prod.mk.injEq ..).mp this |>.1
  have h1 : (Θ ((1 : C), 1)).1 = 1 := by
    rw [show ((1 : C), (1 : P)) = (1 : G) from rfl, map_one]; rfl
  rcases hC_cases c with rfl | rfl
  · exact h1
  · rcases hC_cases (Θ (Multiplicative.ofAdd (1 : ZMod 2), 1)).1 with h | h
    · exact absurd (hinj (h.trans h1.symm)) hz_ne
    · exact h

def psiOf (Θ : MulAut G) : P ≃* P where
  toFun p := (Θ (1, p)).2
  invFun p := (Θ.symm (1, p)).2
  left_inv p := by
    have hpres : (Θ (1, p)).1 = 1 := theta_preserves_P Θ p
    have he : ((1 : C), (Θ (1, p)).2) = Θ (1, p) := Prod.ext hpres.symm rfl
    show (Θ.symm (1, (Θ (1, p)).2)).2 = p
    rw [he, Θ.symm_apply_apply]
  right_inv p := by
    have hpres : (Θ.symm (1, p)).1 = 1 := theta_preserves_P Θ.symm p
    have he : ((1 : C), (Θ.symm (1, p)).2) = Θ.symm (1, p) := Prod.ext hpres.symm rfl
    show (Θ (1, (Θ.symm (1, p)).2)).2 = p
    rw [he, Θ.apply_symm_apply]
  map_mul' p q := by
    show (Θ (1, p * q)).2 = (Θ (1, p)).2 * (Θ (1, q)).2
    rw [show ((1 : C), p * q) = ((1 : C), p) * ((1 : C), q) from by
          rw [Prod.mk_mul_mk, one_mul], map_mul]
    rfl

def autGPEquiv : MulAut G ≃ MulAut P where
  toFun Θ := psiOf Θ
  invFun ψ := (MulEquiv.refl C).prodCongr ψ
  left_inv Θ := by
    apply MulEquiv.ext
    intro x
    obtain ⟨c, p⟩ := x
    have recon : Θ (c, p) = (c, (Θ (1, p)).2) := by
      have hstep : ((c, p) : G) = (c, 1) * (1, p) := by
        rw [Prod.mk_mul_mk, mul_one, one_mul]
      rw [hstep, map_mul]
      have hcp1 : Θ (c, 1) = (c, 1) := Prod.ext (chi_eq Θ c) (theta_preserves_C Θ c)
      have h1p : Θ (1, p) = (1, (Θ (1, p)).2) := Prod.ext (theta_preserves_P Θ p) rfl
      rw [hcp1, h1p, Prod.mk_mul_mk, one_mul, mul_one]
    show ((c, (Θ (1, p)).2)) = Θ (c, p)
    rw [recon]
  right_inv ψ := by
    apply MulEquiv.ext
    intro p
    show (((MulEquiv.refl C).prodCongr ψ) (1, p)).2 = ψ p
    rfl

lemma card_autG : Fintype.card (MulAut G) = 2187 := by
  rw [Fintype.card_congr autGPEquiv, card_aut]

lemma card_G : Fintype.card G = 1458 := by
  rw [Fintype.card_prod, card_P, show Fintype.card C = 2 from by decide]

end P
end Disproof

open Nat in
noncomputable def A365179 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let p : ℕ := Nat.nth Nat.Prime (k.succ)
    if p % 3 = 2 then p ^ 6 else p ^ 7

universe u

lemma nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  have h : Nat.count Nat.Prime 3 = 1 := by decide
  have hp : Nat.nth Nat.Prime (Nat.count Nat.Prime 3) = 3 :=
    Nat.nth_count (p := Nat.Prime) (by norm_num)
  rwa [h] at hp

lemma A_two : A365179 2 = 2187 := by
  have he : A365179 2 = (if Nat.nth Nat.Prime 1 % 3 = 2 then (Nat.nth Nat.Prime 1) ^ 6
      else (Nat.nth Nat.Prime 1) ^ 7) := rfl
  rw [he, nth_prime_one]; norm_num

def autCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) : MulAut A ≃ MulAut B where
  toFun f := (e.symm.trans f).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp

theorem oeis_365179_conjecture_2.disproof :
    ¬ (∀ (n : ℕ) (_ : 2 ≤ n),
        ∀ (G : Type u) [Group G] [Fintype G] [Fintype (MulAut G)],
          (Fintype.card (MulAut G) = A365179 n) →
          (Fintype.card G = A365179 n / Nat.nth Nat.Prime (n - 1)) ∧
          (Nat.nth Nat.Prime (n - 1) % 3 = 2 →
           ∀ (H : Type u) [Group H] [Fintype H] [Fintype (MulAut H)],
              Fintype.card (MulAut H) = A365179 n →
              Nonempty (G ≃* H))) := by
  intro h
  set GG := ULift.{u} Disproof.P.G with hGG
  have hcardAut : Fintype.card (MulAut GG) = 2187 := by
    rw [Fintype.card_congr (autCongr (MulEquiv.ulift : GG ≃* Disproof.P.G))]
    exact Disproof.P.card_autG
  have hcardG : Fintype.card GG = 1458 := by
    rw [Fintype.card_congr (Equiv.ulift : GG ≃ Disproof.P.G)]
    exact Disproof.P.card_G
  have key := (h 2 (le_refl 2) GG (by rw [hcardAut, A_two])).1
  have e1 : Nat.nth Nat.Prime (2 - 1) = 3 := nth_prime_one
  rw [hcardG, A_two, e1] at key
  norm_num at key
