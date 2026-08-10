import FormalConjectures.Util.ProblemImports

open Nat Set

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

def N : ℕ := 2 * 100943 * 3 ^ 39101 - 1

instance : NeZero N := ⟨by decide⟩
instance : Fact (1 < N) := ⟨by decide⟩

structure LucasRing (N_val : ℕ) (D_val : ZMod N_val) where
  re : ZMod N_val
  im : ZMod N_val
deriving DecidableEq

namespace LucasRing

variable {N_val : ℕ} {D_val : ZMod N_val}

def zero : LucasRing N_val D_val := ⟨0, 0⟩
def one : LucasRing N_val D_val := ⟨1, 0⟩

def add (x y : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨-x.re, -x.im⟩
def mul (x y : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨x.re * y.re + D_val * x.im * y.im, x.re * y.im + x.im * y.re⟩
def sub (x y : LucasRing N_val D_val) : LucasRing N_val D_val := ⟨x.re - y.re, x.im - y.im⟩
def natCast (n : ℕ) : LucasRing N_val D_val := ⟨(n : ZMod N_val), 0⟩
def intCast (n : ℤ) : LucasRing N_val D_val := ⟨(n : ZMod N_val), 0⟩

instance : Zero (LucasRing N_val D_val) := ⟨zero⟩
instance : One (LucasRing N_val D_val) := ⟨one⟩
instance : Add (LucasRing N_val D_val) := ⟨add⟩
instance : Neg (LucasRing N_val D_val) := ⟨neg⟩
instance : Mul (LucasRing N_val D_val) := ⟨mul⟩
instance : Sub (LucasRing N_val D_val) := ⟨sub⟩
instance : NatCast (LucasRing N_val D_val) := ⟨natCast⟩
instance : IntCast (LucasRing N_val D_val) := ⟨intCast⟩

@[simp] lemma add_re (x y : LucasRing N_val D_val) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : LucasRing N_val D_val) : (x + y).im = x.im + y.im := rfl
@[simp] lemma neg_re (x : LucasRing N_val D_val) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : LucasRing N_val D_val) : (-x).im = -x.im := rfl
@[simp] lemma mul_re (x y : LucasRing N_val D_val) : (x * y).re = x.re * y.re + D_val * x.im * y.im := rfl
@[simp] lemma mul_im (x y : LucasRing N_val D_val) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] lemma zero_re : (0 : LucasRing N_val D_val).re = 0 := rfl
@[simp] lemma zero_im : (0 : LucasRing N_val D_val).im = 0 := rfl
@[simp] lemma one_re : (1 : LucasRing N_val D_val).re = 1 := rfl
@[simp] lemma one_im : (1 : LucasRing N_val D_val).im = 0 := rfl
@[simp] lemma sub_re (x y : LucasRing N_val D_val) : (x - y).re = x.re - y.re := rfl
@[simp] lemma sub_im (x y : LucasRing N_val D_val) : (x - y).im = x.im - y.im := rfl
@[simp] lemma natCast_re (n : ℕ) : (n : LucasRing N_val D_val).re = (n : ZMod N_val) := rfl
@[simp] lemma natCast_im (n : ℕ) : (n : LucasRing N_val D_val).im = 0 := rfl
@[simp] lemma intCast_re (n : ℤ) : (n : LucasRing N_val D_val).re = (n : ZMod N_val) := rfl
@[simp] lemma intCast_im (n : ℤ) : (n : LucasRing N_val D_val).im = 0 := rfl

@[ext]
lemma ext {x y : LucasRing N_val D_val} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

instance : CommRing (LucasRing N_val D_val) where
  add := (· + ·)
  add_assoc _ _ _ := by ext <;> simp <;> ring
  zero := 0
  zero_add _ := by ext <;> simp <;> ring
  add_zero _ := by ext <;> simp <;> ring
  add_comm _ _ := by ext <;> simp <;> ring
  mul := (· * ·)
  left_distrib _ _ _ := by ext <;> simp <;> ring
  right_distrib _ _ _ := by ext <;> simp <;> ring
  zero_mul _ := by ext <;> simp <;> ring
  mul_zero _ := by ext <;> simp <;> ring
  mul_assoc _ _ _ := by ext <;> simp <;> ring
  one := 1
  one_mul _ := by ext <;> simp <;> ring
  mul_one _ := by ext <;> simp <;> ring
  neg := (-·)
  neg_add_cancel _ := by ext <;> simp <;> ring
  mul_comm _ _ := by ext <;> simp <;> ring
  nsmul n x := ⟨n * x.re, n * x.im⟩
  nsmul_zero _ := by ext <;> simp <;> ring
  nsmul_succ _ _ := by ext <;> simp <;> ring
  sub := (· - ·)
  sub_eq_add_neg _ _ := by ext <;> simp <;> ring
  zsmul n x := ⟨n * x.re, n * x.im⟩
  zsmul_zero' _ := by ext <;> simp <;> ring
  zsmul_succ' _ _ := by ext <;> simp <;> ring
  zsmul_neg' _ _ := by ext <;> simp <;> ring
  natCast := natCast
  natCast_zero := by ext <;> simp [natCast] <;> ring
  natCast_succ n := by ext <;> simp [natCast] <;> ring
  intCast := intCast
  intCast_ofNat n := by ext <;> simp [intCast] <;> ring
  intCast_negSucc n := by ext <;> simp [intCast] <;> ring

lemma val_cast {M : ℕ} [NeZero M] (y : ZMod M) : (y.val : ZMod M) = y := by
  exact ZMod.natCast_zmod_val y

instance [Fact (Nat.Prime N_val)] : Field (ZMod N_val) :=
  ZMod.instField N_val

instance [NeZero N_val] : Fintype (LucasRing N_val D_val) where
  elems := (Finset.univ ×ˢ Finset.univ).map ⟨fun (x, y) => ⟨x, y⟩, by intro x y h; cases x; cases y; simp_all⟩
  complete := by
    intro x
    simp [Finset.mem_univ]

-- Group structures of U1
def U1 (p : ℕ) [Fact (Nat.Prime p)] : Type :=
  { x : LucasRing p 5 // x.re^2 - 5 * x.im^2 = 1 }

instance (p : ℕ) [Fact (Nat.Prime p)] : Fintype (U1 p) :=
  Subtype.fintype _

lemma norm_mul (x y : LucasRing N_val D_val) :
    (x * y).re^2 - D_val * (x * y).im^2 = (x.re^2 - D_val * x.im^2) * (y.re^2 - D_val * y.im^2) := by
  simp only [mul_re, mul_im]
  ring

def conj (x : LucasRing p 5) : LucasRing p 5 := ⟨x.re, -x.im⟩

@[simp] lemma conj_re (x : LucasRing p 5) : (conj x).re = x.re := rfl
@[simp] lemma conj_im (x : LucasRing p 5) : (conj x).im = -x.im := rfl

lemma mul_conj (x : LucasRing p 5) : x * conj x = ⟨x.re^2 - 5 * x.im^2, 0⟩ := by
  ext <;> simp <;> ring

instance (p : ℕ) [Fact (Nat.Prime p)] : Group (U1 p) where
  mul x y := ⟨x.val * y.val, by
    have h_norm := norm_mul x.val y.val
    rw [x.property, y.property] at h_norm
    simp only [mul_one] at h_norm
    exact h_norm⟩
  mul_assoc x y := by
    intro z
    apply Subtype.ext
    ext <;> simp [mul_assoc]
  one := ⟨1, by simp⟩
  one_mul x := by
    apply Subtype.ext
    ext <;> simp [one]
  mul_one x := by
    apply Subtype.ext
    ext <;> simp [one]
  inv x := ⟨conj x.val, by
    have h_norm : (conj x.val).re^2 - 5 * (conj x.val).im^2 = 1 := by
      simp only [conj_re, conj_im, neg_sq]
      exact x.property
    exact h_norm⟩
  inv_mul_cancel x := by
    apply Subtype.ext
    rw [mul_comm]
    have h_conj := mul_conj x.val
    rw [x.property] at h_conj
    exact h_conj

-- Group size bounding
def Fiber (p : ℕ) [Fact (Nat.Prime p)] (y : ZMod p) : Type :=
  { x : LucasRing p 5 // x.re^2 - 5 * x.im^2 = 1 ∧ x.im = y }

instance (p : ℕ) [Fact (Nat.Prime p)] (y : ZMod p) : DecidableEq (Fiber p y) := by
  unfold Fiber
  infer_instance

instance (p : ℕ) [Fact (Nat.Prime p)] (y : ZMod p) : Fintype (Fiber p y) :=
  Subtype.fintype _

lemma fiber_card_le_two (p : ℕ) [Fact (Nat.Prime p)] (y : ZMod p) : Fintype.card (Fiber p y) ≤ 2 := by
  by_cases hne : Nonempty (Fiber p y)
  · rcases hne with ⟨a⟩
    have h_inj_bool : Function.Injective (fun (x : Fiber p y) => if x = a then true else false) := by
      intro x z h
      dsimp only at h
      by_cases hx : x = a
      · by_cases hz : z = a
        · rw [hx, hz]
        · rw [if_pos hx, if_neg hz] at h
          contradiction
      · by_cases hz : z = a
        · rw [if_neg hx, if_pos hz] at h
          contradiction
        · rw [if_neg hx, if_neg hz] at h
          have h_x_im : x.val.im = y := x.property.2
          have h_z_im : z.val.im = y := z.property.2
          have h_a_im : a.val.im = y := a.property.2
          have h_x_re2 : x.val.re^2 = 1 + 5 * y^2 := by
            have hx_prop := x.property.1
            rw [h_x_im] at hx_prop
            linear_combination hx_prop
          have h_z_re2 : z.val.re^2 = 1 + 5 * y^2 := by
            have hz_prop := z.property.1
            rw [h_z_im] at hz_prop
            linear_combination hz_prop
          have h_a_re2 : a.val.re^2 = 1 + 5 * y^2 := by
            have ha_prop := a.property.1
            rw [h_a_im] at ha_prop
            linear_combination ha_prop
          have h_x_a : x.val.re^2 = a.val.re^2 := by rw [h_x_re2, h_a_re2]
          have h_z_a : z.val.re^2 = a.val.re^2 := by rw [h_z_re2, h_a_re2]
          rw [sq_eq_sq_iff_eq_or_eq_neg] at h_x_a
          rw [sq_eq_sq_iff_eq_or_eq_neg] at h_z_a
          have h_x_re : x.val.re = -a.val.re := by
            cases h_x_a with
            | inl h1 =>
              have h_eq : x = a := by
                apply Subtype.ext
                ext
                · exact h1
                · rw [h_x_im, h_a_im]
              contradiction
            | inr h2 => exact h2
          have h_z_re : z.val.re = -a.val.re := by
            cases h_z_a with
            | inl h1 =>
              have h_eq : z = a := by
                apply Subtype.ext
                ext
                · exact h1
                · rw [h_z_im, h_a_im]
              contradiction
            | inr h2 => exact h2
          have h_re_eq : x.val.re = z.val.re := by rw [h_x_re, h_z_re]
          apply Subtype.ext
          ext
          · exact h_re_eq
          · rw [h_x_im, h_z_im]
    have h_card := Fintype.card_le_of_injective _ h_inj_bool
    have h_bool_card : Fintype.card Bool = 2 := rfl
    rw [h_bool_card] at h_card
    exact h_card
  · have h_card : Fintype.card (Fiber p y) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun x => hne ⟨x⟩⟩
    rw [h_card]
    omega

def u1_equiv_sigma (p : ℕ) [Fact (Nat.Prime p)] :
    U1 p ≃ Σ y : ZMod p, Fiber p y where
  toFun x := ⟨x.val.im, ⟨x.val, ⟨x.property, rfl⟩⟩⟩
  invFun s := ⟨s.2.val, s.2.property.1⟩
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨y, ⟨v, ⟨h1, h2⟩⟩⟩
    subst h2
    rfl

lemma card_u1_le_two_p (p : ℕ) [Fact (Nat.Prime p)] :
    Fintype.card (U1 p) ≤ 2 * p := by
  have h_eq : Fintype.card (U1 p) = Fintype.card (Σ y : ZMod p, Fiber p y) :=
    Fintype.card_congr (u1_equiv_sigma p)
  rw [h_eq]
  rw [Fintype.card_sigma]
  have h_le : ∑ y : ZMod p, Fintype.card (Fiber p y) ≤ ∑ _y : ZMod p, 2 := by
    apply Finset.sum_le_sum
    intro y _
    exact fiber_card_le_two p y
  have h_const : (∑ _y : ZMod p, 2) = 2 * p := by
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
  omega

-- Homomorphism from N to p
lemma nat_cast_mod_mul (p k a : ℕ) : ((a % (p * k) : ℕ) : ZMod p) = (a : ZMod p) := by
  have h_div := Nat.div_add_mod a (p * k)
  rw [← h_div]
  push_cast
  have h_zero : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [h_zero]
  simp

lemma cast_zmod_mul (p : ℕ) (hp : p ∣ N) (x y : ZMod N) :
    ( (x * y).val : ZMod p ) = (x.val : ZMod p) * (y.val : ZMod p) := by
  have h_eq : (x * y).val = (x.val * y.val) % N := ZMod.val_mul x y
  rcases hp with ⟨k, hk⟩
  have hk_eq : N = p * k := by
    rw [hk]
    try ring
  set a := x.val
  set b := y.val
  have h_mod : a * b % N = a * b % (p * k) := by
    rw [hk_eq]
  rw [h_eq]
  change ( (a * b % N : ℕ) : ZMod p ) = (a : ZMod p) * (b : ZMod p)
  rw [h_mod]
  rw [nat_cast_mod_mul p k (a * b)]
  push_cast
  rfl

lemma cast_zmod_add (p : ℕ) (hp : p ∣ N) (x y : ZMod N) :
    ( (x + y).val : ZMod p ) = (x.val : ZMod p) + (y.val : ZMod p) := by
  have h_eq : (x + y).val = (x.val + y.val) % N := ZMod.val_add x y
  rcases hp with ⟨k, hk⟩
  have hk_eq : N = p * k := by
    rw [hk]
    try ring
  set a := x.val
  set b := y.val
  have h_mod : (a + b) % N = (a + b) % (p * k) := by
    rw [hk_eq]
  rw [h_eq]
  change ( ((a + b) % N : ℕ) : ZMod p ) = (a : ZMod p) + (b : ZMod p)
  rw [h_mod]
  rw [nat_cast_mod_mul p k (a + b)]
  push_cast
  rfl

def phi (p : ℕ) (x : LucasRing N 5) : LucasRing p 5 :=
  ⟨(x.re.val : ZMod p), (x.im.val : ZMod p)⟩

lemma phi_mul (p : ℕ) (hp : p ∣ N) (x y : LucasRing N 5) :
    phi p (x * y) = phi p x * phi p y := by
  unfold phi
  apply LucasRing.ext
  · simp only [LucasRing.mul_re, LucasRing.mul_im]
    have h_add1 := cast_zmod_add p hp (x.re * y.re) (5 * x.im * y.im)
    have h_mul1 := cast_zmod_mul p hp x.re y.re
    have h_mul2 := cast_zmod_mul p hp (5 * x.im) y.im
    have h_mul3 := cast_zmod_mul p hp 5 x.im
    rw [h_add1, h_mul1, h_mul2, h_mul3]
    have h_five : (5 : ZMod N).val = 5 := rfl
    rw [h_five]
    push_cast
    ring
  · simp only [LucasRing.mul_re, LucasRing.mul_im]
    have h_add2 := cast_zmod_add p hp (x.re * y.im) (x.im * y.re)
    have h_mul4 := cast_zmod_mul p hp x.re y.im
    have h_mul5 := cast_zmod_mul p hp x.im y.re
    rw [h_add2, h_mul4, h_mul5]

lemma phi_one (p : ℕ) : phi p 1 = 1 := by
  unfold phi
  have h_one : (1 : ZMod N).val = 1 := rfl
  have h_zero : (0 : ZMod N).val = 0 := rfl
  simp [h_one, h_zero]
  rfl

lemma cast_zmod_pow (p : ℕ) (hp : p ∣ N) (x : ZMod N) (m : ℕ) :
    ( (x ^ m).val : ZMod p ) = (x.val : ZMod p) ^ m := by
  induction m with
  | zero =>
    have h1 : x ^ 0 = 1 := rfl
    have h2 : (1 : ZMod N).val = 1 := rfl
    rw [h1, h2]
    push_cast
    simp
  | succ m ih =>
    have h1 : x ^ (m + 1) = x ^ m * x := by ring
    rw [h1]
    have h2 := cast_zmod_mul p hp (x ^ m) x
    rw [h2]
    rw [ih]
    ring

lemma phi_norm_eq_one (p : ℕ) (hp : p ∣ N) (x : LucasRing N 5) (h : x.re^2 - 5 * x.im^2 = 1) :
    (phi p x).re^2 - 5 * (phi p x).im^2 = 1 := by
  unfold phi
  dsimp only
  have h_eq : x.re^2 = 1 + 5 * x.im^2 := by linear_combination h
  have h_val : (x.re^2).val = (1 + 5 * x.im^2).val := by rw [h_eq]
  have h_cast : ((x.re^2).val : ZMod p) = ((1 + 5 * x.im^2).val : ZMod p) := by rw [h_val]
  have h_pow1 := cast_zmod_pow p hp x.re 2
  have h_add3 := cast_zmod_add p hp 1 (5 * x.im^2)
  have h_mul6 := cast_zmod_mul p hp 5 (x.im^2)
  have h_pow2 := cast_zmod_pow p hp x.im 2
  rw [h_pow1] at h_cast
  rw [h_add3, h_mul6] at h_cast
  rw [h_pow2] at h_cast
  have h_five : (5 : ZMod N).val = 5 := rfl
  rw [h_five] at h_cast
  have h_one : (1 : ZMod N).val = 1 := rfl
  rw [h_one] at h_cast
  push_cast at h_cast
  linear_combination h_cast

def cube_1 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  let x3 := x * x * x
  ⟨ZMod.val x3.re, ZMod.val x3.im⟩

def cube_2 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_1 (cube_1 x)
def cube_4 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_2 (cube_2 x)
def cube_8 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_4 (cube_4 x)
def cube_16 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_8 (cube_8 x)
def cube_32 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_16 (cube_16 x)
def cube_64 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_32 (cube_32 x)
def cube_128 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_64 (cube_64 x)
def cube_256 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_128 (cube_128 x)
def cube_512 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_256 (cube_256 x)
def cube_1024 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_512 (cube_512 x)
def cube_2048 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_1024 (cube_1024 x)
def cube_4096 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_2048 (cube_2048 x)
def cube_8192 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_4096 (cube_4096 x)
def cube_16384 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_8192 (cube_8192 x)
def cube_32768 (x : LucasRing N_val D_val) : LucasRing N_val D_val := cube_16384 (cube_16384 x)

lemma cube_1_eq (x : LucasRing N_val D_val) : cube_1 x = x ^ (3 ^ 1) := by
  unfold cube_1
  ext <;> simp [ZMod.natCast_zmod_val] <;> ring

lemma cube_2_eq (x : LucasRing N_val D_val) : cube_2 x = x ^ (3 ^ 2) := by
  unfold cube_2; rw [cube_1_eq, cube_1_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_4_eq (x : LucasRing N_val D_val) : cube_4 x = x ^ (3 ^ 4) := by
  unfold cube_4; rw [cube_2_eq, cube_2_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_8_eq (x : LucasRing N_val D_val) : cube_8 x = x ^ (3 ^ 8) := by
  unfold cube_8; rw [cube_4_eq, cube_4_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_16_eq (x : LucasRing N_val D_val) : cube_16 x = x ^ (3 ^ 16) := by
  unfold cube_16; rw [cube_8_eq, cube_8_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_32_eq (x : LucasRing N_val D_val) : cube_32 x = x ^ (3 ^ 32) := by
  unfold cube_32; rw [cube_16_eq, cube_16_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_64_eq (x : LucasRing N_val D_val) : cube_64 x = x ^ (3 ^ 64) := by
  unfold cube_64; rw [cube_32_eq, cube_32_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_128_eq (x : LucasRing N_val D_val) : cube_128 x = x ^ (3 ^ 128) := by
  unfold cube_128; rw [cube_64_eq, cube_64_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_256_eq (x : LucasRing N_val D_val) : cube_256 x = x ^ (3 ^ 256) := by
  unfold cube_256; rw [cube_128_eq, cube_128_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_512_eq (x : LucasRing N_val D_val) : cube_512 x = x ^ (3 ^ 512) := by
  unfold cube_512; rw [cube_256_eq, cube_256_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_1024_eq (x : LucasRing N_val D_val) : cube_1024 x = x ^ (3 ^ 1024) := by
  unfold cube_1024; rw [cube_512_eq, cube_512_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_2048_eq (x : LucasRing N_val D_val) : cube_2048 x = x ^ (3 ^ 2048) := by
  unfold cube_2048; rw [cube_1024_eq, cube_1024_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_4096_eq (x : LucasRing N_val D_val) : cube_4096 x = x ^ (3 ^ 4096) := by
  unfold cube_4096; rw [cube_2048_eq, cube_2048_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_8192_eq (x : LucasRing N_val D_val) : cube_8192 x = x ^ (3 ^ 8192) := by
  unfold cube_8192; rw [cube_4096_eq, cube_4096_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_16384_eq (x : LucasRing N_val D_val) : cube_16384 x = x ^ (3 ^ 16384) := by
  unfold cube_16384; rw [cube_8192_eq, cube_8192_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

lemma cube_32768_eq (x : LucasRing N_val D_val) : cube_32768 x = x ^ (3 ^ 32768) := by
  unfold cube_32768; rw [cube_16384_eq, cube_16384_eq, ← pow_mul]; congr 1; rw [← pow_add]; rfl

def cube_39101 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_1 (cube_4 (cube_8 (cube_16 (cube_32 (cube_128 (cube_2048 (cube_4096 (cube_32768 x))))))))

def cube_39100 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_4 (cube_8 (cube_16 (cube_32 (cube_128 (cube_2048 (cube_4096 (cube_32768 x)))))))

lemma cube_39101_eq (x : LucasRing N_val D_val) : cube_39101 x = x ^ (3 ^ 39101) := by
  unfold cube_39101
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_128_eq, cube_32_eq, cube_16_eq, cube_8_eq, cube_4_eq, cube_1_eq]
  repeat rw [← pow_mul]
  congr 1
  repeat rw [← pow_add]
  rfl

lemma cube_39100_eq (x : LucasRing N_val D_val) : cube_39100 x = x ^ (3 ^ 39100) := by
  unfold cube_39100
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_128_eq, cube_32_eq, cube_16_eq, cube_8_eq, cube_4_eq]
  repeat rw [← pow_mul]
  congr 1
  repeat rw [← pow_add]
  rfl

def pow_chunk_loop (fuel : ℕ) (base res : LucasRing N_val D_val) (p : ℕ) : LucasRing N_val D_val :=
  match fuel with
  | 0 => res
  | fuel + 1 =>
    if p = 0 then res
    else
      let next_res := if p % 2 = 1 then res * base else res
      let base2 := base * base
      let re_b := ZMod.val base2.re
      let im_b := ZMod.val base2.im
      let re_r := ZMod.val next_res.re
      let im_r := ZMod.val next_res.im
      pow_chunk_loop fuel ⟨re_b, im_b⟩ ⟨re_r, im_r⟩ (p / 2)

lemma pow_chunk_loop_eq [NeZero N_val] (fuel : ℕ) (p : ℕ) (base res : LucasRing N_val D_val) (h_fuel : p < 2^fuel) :
    pow_chunk_loop fuel base res p = res * base ^ p := by
  induction fuel generalizing p base res with
  | zero =>
    have hp : p = 0 := by omega
    subst hp
    simp [pow_chunk_loop]
  | succ fuel ih =>
    rw [pow_chunk_loop]
    split_ifs with hp h_odd
    · rw [hp]
      simp
    · dsimp only
      have h_div : p / 2 < 2^fuel := by omega
      rw [ih (p / 2) ⟨(base * base).re.val, (base * base).im.val⟩ ⟨(res * base).re.val, (res * base).im.val⟩ h_div]
      have h_b2 : (⟨(base * base).re.val, (base * base).im.val⟩ : LucasRing N_val D_val) = base * base := by
        ext <;> simp [ZMod.natCast_zmod_val]
      have h_res : (⟨(res * base).re.val, (res * base).im.val⟩ : LucasRing N_val D_val) = res * base := by
        ext <;> simp [ZMod.natCast_zmod_val]
      rw [h_b2, h_res]
      have h_base2 : base * base = base^2 := by ring
      rw [h_base2, ← pow_mul]
      have h_p : base ^ p = base ^ (2 * (p / 2) + 1) := by congr 1; omega
      rw [h_p]
      rw [pow_succ, mul_assoc]
      ring_nf
    · dsimp only
      have h_div : p / 2 < 2^fuel := by omega
      rw [ih (p / 2) ⟨(base * base).re.val, (base * base).im.val⟩ ⟨res.re.val, res.im.val⟩ h_div]
      have h_b2 : (⟨(base * base).re.val, (base * base).im.val⟩ : LucasRing N_val D_val) = base * base := by
        ext <;> simp [ZMod.natCast_zmod_val]
      have h_res : (⟨res.re.val, res.im.val⟩ : LucasRing N_val D_val) = res := by
        ext <;> simp [ZMod.natCast_zmod_val]
      rw [h_b2, h_res]
      have h_base2 : base * base = base^2 := by ring
      rw [h_base2, ← pow_mul]
      have h_p : base ^ p = base ^ (2 * (p / 2)) := by congr 1; omega
      rw [h_p]

lemma phi_pow (p : ℕ) (hp : p ∣ N) (x : LucasRing N 5) (m : ℕ) :
    phi p (x ^ m) = (phi p x) ^ m := by
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    change phi p (x ^ m * x) = (phi p x) ^ m * phi p x
    rw [phi_mul p hp, ih]

variable {p : ℕ}

def get_W2 (x : LucasRing p 5) : LucasRing p 5 :=
  cube_39101 (pow_chunk_loop 18 x 1 100943)

def get_W3 (x : LucasRing p 5) : LucasRing p 5 :=
  cube_39100 (pow_chunk_loop 18 (x * x) 1 100943)

def get_W100943 (x : LucasRing p 5) : LucasRing p 5 :=
  cube_39101 (x * x)

def get_W_all (x : LucasRing p 5) : LucasRing p 5 :=
  let w2 := get_W2 x
  w2 * w2

lemma get_W2_eq [NeZero p] (x : LucasRing p 5) : get_W2 x = x ^ ((N+1)/2) := by
  unfold get_W2
  rw [cube_39101_eq]
  have h_pow : pow_chunk_loop 18 x 1 100943 = x ^ 100943 := by
    rw [pow_chunk_loop_eq 18 100943 x 1 (by decide), one_mul]
  rw [h_pow]
  rw [← pow_mul]
  have h_eq : 100943 * 3 ^ 39101 = (N+1)/2 := by
    change 100943 * 3 ^ 39101 = (2 * 100943 * 3 ^ 39101 - 1 + 1) / 2
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    omega
  rw [h_eq]

lemma get_W3_eq [NeZero p] (x : LucasRing p 5) : get_W3 x = x ^ ((N+1)/3) := by
  unfold get_W3
  rw [cube_39100_eq]
  have h_pow : pow_chunk_loop 18 (x * x) 1 100943 = (x * x) ^ 100943 := by
    rw [pow_chunk_loop_eq 18 100943 (x * x) 1 (by decide), one_mul]
  rw [h_pow]
  have h_x2 : x * x = x^2 := by ring
  rw [h_x2]
  rw [← pow_mul, ← pow_mul]
  have h_div : 2 * (100943 * 3 ^ 39100) = (N+1)/3 := by
    change 2 * (100943 * 3 ^ 39100) = (2 * 100943 * 3 ^ 39101 - 1 + 1) / 3
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    have h_pow3 : 3 ^ 39100 * 3 = 3 ^ 39101 := rfl
    omega
  rw [h_div]

lemma get_W100943_eq [NeZero p] (x : LucasRing p 5) : get_W100943 x = x ^ ((N+1)/100943) := by
  unfold get_W100943
  rw [cube_39101_eq]
  have h_x2 : x * x = x^2 := by ring
  rw [h_x2]
  rw [← pow_mul]
  have h_eq : 2 * 3 ^ 39101 * 100943 = (N+1) := by
    change 2 * 3 ^ 39101 * 100943 = 2 * 100943 * 3 ^ 39101 - 1 + 1
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    omega
  have h_div : 2 * 3 ^ 39101 = (N+1)/100943 := by
    rw [← h_eq]
    exact (Nat.mul_div_cancel (2 * 3 ^ 39101) (by decide)).symm
  rw [h_div]

lemma get_W_all_eq [NeZero p] (x : LucasRing p 5) : get_W_all x = x ^ (N+1) := by
  unfold get_W_all
  rw [get_W2_eq]
  have h_sq : x ^ ((N+1)/2) * x ^ ((N+1)/2) = x ^ (2 * ((N+1)/2)) := by
    rw [← pow_add, ← mul_two]
    congr 1
  rw [h_sq]
  congr 1

lemma orderOf_le_fintype_card {G : Type*} [Group G] [Fintype G] (x : G) :
    orderOf x ≤ Fintype.card G := by
  have h_card_eq : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
  have h_le := orderOf_le_card (x := x)
  rw [h_card_eq] at h_le
  exact h_le

lemma pow_eq_one_of_dvd_orderOf {G : Type*} [Group G] {x : G} {k : ℕ} (h : orderOf x ∣ k) : x ^ k = 1 := by
  rcases h with ⟨m, rfl⟩
  rw [pow_mul, pow_orderOf_eq_one, one_pow]

lemma card_ge_of_witness {G : Type*} [Group G] [Fintype G] (x : G) (M : ℕ) (hM : x ^ M = 1) (hM_pos : M > 0)
    (h2 : x ^ (M / 2) ≠ 1)
    (h3 : x ^ (M / 3) ≠ 1)
    (h100943 : x ^ (M / 100943) ≠ 1)
    (h_factors : ∀ q : ℕ, q.Prime → q ∣ M → q = 2 ∨ q = 3 ∨ q = 100943) :
    M ≤ Fintype.card G := by
  have hd : orderOf x ∣ M := orderOf_dvd_of_pow_eq_one hM
  rcases hd with ⟨k, rfl⟩
  by_cases hk1 : k = 1
  · subst hk1
    simp only [mul_one]
    exact orderOf_le_fintype_card x
  · have hk_ne_zero : k ≠ 0 := by
      intro hk0
      subst hk0
      rw [mul_zero] at hM_pos
      omega
    have hk_gt_one : k > 1 := by omega
    have hk_prime_factor : ∃ q : ℕ, q.Prime ∧ q ∣ k := Nat.exists_prime_and_dvd hk_gt_one.ne'
    rcases hk_prime_factor with ⟨q, hq_prime, hq_dvd⟩
    have hq_dvd_M : q ∣ (orderOf x * k) := dvd_mul_of_dvd_right hq_dvd (orderOf x)
    have hq_eq := h_factors q hq_prime hq_dvd_M
    have h_dvd_div : orderOf x ∣ (orderOf x * k / q) := by
      rcases hq_dvd with ⟨m, rfl⟩
      have hq_pos : q > 0 := hq_prime.pos
      have h_eq : orderOf x * (q * m) / q = orderOf x * m := by
        rw [mul_comm q m]
        rw [← mul_assoc]
        exact Nat.mul_div_cancel (orderOf x * m) hq_pos
      rw [h_eq]
      exact dvd_mul_right (orderOf x) m
    have h_pow_eq_one : x ^ (orderOf x * k / q) = 1 := pow_eq_one_of_dvd_orderOf h_dvd_div
    rcases hq_eq with rfl | rfl | rfl
    · contradiction
    · contradiction
    · contradiction

lemma phi_add_one (p : ℕ) (hp : p ∣ N) (x : LucasRing N 5) :
    phi p (1 + x) = 1 + phi p x := by
  unfold phi
  apply LucasRing.ext
  · simp only [add_re, one_re, one_im]
    rw [cast_zmod_add p hp]
    have h_one : (1 : ZMod N).val = 1 := rfl
    rw [h_one]
    push_cast
    rfl
  · simp only [add_re, one_re, one_im, add_im]
    push_cast
    rfl

lemma algebra_inv_identity (A B : LucasRing N 5) (h : (A - 1) * B = 1) : A * B = 1 + B := by
  linear_combination h

-- Reconstruction helper for chunked large numbers
def reconstruct (lst : List ℕ) : ℕ :=
  lst.foldl (fun acc x => acc * 10^500 + x) 0

-- Witness value definitions via chunks
def alpha_re_val : ZMod N := (reconstruct [64369724246004465466263125807584850091388316860542681175292590183691198602535779890838503417263147425281902904529818020979091379186221630281126341723270837108180, 67677542372213338962965643700535808616586100080430384149198227118945630610038899646387055879101080461296791012963085054790520135619767865866464168245053498430621165614479238896430912843155262284775081098595319148626727058244197130322582755509958487572471703318581320717744959991954001373450011773890579289378485355475533884085000494588568142007967515311437688418955696685511713924026176374033563974679374229774098766061390056735572353054358512381889390753535861835164585979490650692716412331500933678, 43609693487275673384347986300674103817977501958383553910703074816969929790840356957181416183603846874359696504625152366531314689320350195051249347659650359854275826151441313430610221000947793468383564936503838613379035783307219498132194005930682314376079571453089100946700303947178369517025368471301366067971872509604683515055724572353105921056123680743081729927090498306403310210641397227640072982177905491559652843559225292623517724026508192594371766319535933480622480543962134408826870270160565168, 86613241670677338209442331358336422913950027062769167371804151223847157220186281243256898895251302232646888949090929302274212799198112833627313286512517125744769032542403018086509996602546747942935704588763778004202570879453647654251334487942524690331052652331754883008446762783507839496740289346686903974857023604419451765231957665679768240412322286906127432281182506607482114017082240785071719131309355857325556267288602382707591247496261587270985196663470576033143394937180172220184262090276567826, 71109003487634113390835531732202953640115732940310568422249808486030749237168629507546969708792755385821191015308259234299477627335593888369858492786223765535745575690127417446791142604959543771934415247465282851805482983408975798718682723740081072417445260459284988483446808603999170629148544152272588525343992951000689369295989714882928318936273600792696469406441828447032257007505347647800250060666930060699043528820367570421208800441557982301609942998107408692015498555351329754211371659430534896, 82748761993731644102567722699122513606697699303533393803479752189444203590022312422990146576843661670944136444425108569021173640706784132328908009907686561004035509497888777738105231633846063496710597033740159993318158192353579717517929393320363716445041828860829362090942321736872239452002727227428180048989421815680447189806800057815728115507765351630516946358724822881584923749235804591234782392507425562690372020958960093161409728221426613340296705755660744377408098563721919065341150947371712521, 79139800257661221359415008497717194313856284830297831964127262939456627613993858913124232338927959684900092948362789437029090676441507281510589609538536556935896632369459612285267958511008215298452679674416348200273731939389911709234027496292024751798311325791963295797969014549844668272823126778846372637577132309091869955135380042022365220207483036592597933366347451933891459331416697221508701485903375521436478672509663309402707659468081213504756591820372555065344444286095261616985142925770232456, 61989211412588915031226924150293366905119057901410380396841098552253209707423249116592916768047135833324769535320094605207576427444447945059349647339191117733988257637180524303898140342825733535571203383955040760131535465083203114798719557951073983766416847273362550817883728823498605673857156470694795522646496965701213597399482901696613252905293379795224995858761673349233280788890309561303323310168280157838836114752150235489753412928965576966116173246976424578203969542803609457956494416398131580, 96188239124319648436043213996351780443427945700304888135536118271884010436075029400634491871386439757188824966080732703461044974635531483127071867947901834758878004459842003591208082475117038197807379131664935377447799771931458881931227718520655303225650056866252923141621909996055885254081385341469778911579278133923463343239109239113683018220800193126349905385397848427219562080396564899086496047137505578419681903649708979760566421892376109678568915427414308376460543013752665895873736527008556496, 19950855907502649239693923036725435702337950781852004239541991045281257613508323622818045483495737288277749099355297940900837664162638757118753042146667935623023079738751059791040368575716300856973178565019644049409676705015822055837007604300143642225486973949848691901838151042802279061753961576840904200017600222634708197011215134593077040292640358985062958750208311154738370138337403273937165958370241503051173122235088375140797866704555985179731350953145185942832365052245238775472730187200646540, 73330971740648727337643849004017941971874950978194142085193845198352131000023616750233429197733786395313291013734866583998370613372482357793794676609703177924353537918842442835175315559733777392760460573464033364612172795211440624617739545036360967142683505939393834199771246899879517146104851695290671291751527907286588760261174417342767081032301885162787135721279661126837957792678147378672049234328549799322214742180244894171105127021157733662314079090502345639835682136109688864533462361490727457, 61211049676471204366518529640602238979831102369982952887750836226189517585610542599128593956106390477450574358607052392799079480691618187434716777981024828770682990528948656075765052598676188806948063931529807082065054912371938209759509621992480679045840556472722180484549877349912880192496838437730625513282557220333681432143317105629695986898911153907954891595597790786713360578194619639824012043646311051540619673518563981045895406549827412300613531641206767777416682472543363866661936830378117656, 5770054979745419406726045130149048811182574508630088141793203370048469311229033423768050790744354062552461273929136728303880324809463963188468952858918198018598984091027641913016132817058171973101095788464591533336277588819717545216063991114792758387779536906311432347485243416001009504310608198284516706366941978546262202910311640359833288424008420082091580114848645881766656666424454189531115078145955051661463097608867937050378555917583352634037006946766363765415237063634089723597513831995607666, 80246791269984190034858957505359331165398535819855424347791425904089777751133214226356738021637377386641066380086643375935241020633883009599517295950628017723873686888330079219547117412004962664962933555174752199117822823260718962672227105088509328587067012343904744173806369601543583060880396551744318250517658338593026335729210233984080036211254289856557179910920918318582428193807874578631852198937669773884355956865880062007412896499089449918769609893392426872706039345083710387514593341536929050, 8659018283174418059502074624083269021183903732236583079678612538543202458033252236644221860742760840869488063066510361963953599332182153385306986213087526806770920564487991539842126505497160918070879126217485947544905219951022011764604683328060828230248304822557208243294397982959171214062969774370172726783220853318327656891274281595001679770134653962439411680540897055843553420849555323913576259958709278632611579283304794782169779730089987485401891181041511643202297504522518399873016841907223064, 87964851680622736158161101358371025988491857594984463339388459467737786519622091989154726505261929228133501155485297725033247692578543436170287225697639666678162287062323928008821888376203649552023646981685200627137502455548999657592559410032245858633261099539866628563354470069815597437384288871351609077021423372537014159299665820375564299425237728943877739293941248125652066415557547376082776835968443837163113393958349390949805500092194081729351503793675979990084450339121368222798984709880680810, 81081513711526069434273542914800984275348364077874277873014123409707892864711035866774349269513030271105105069239104159261375759244999625031383514382051675596895421409764237853756904645436366605744630966853937033467521031713526046869017919967007737131760556698618873956505408398263370609973085301340049246527570845374375593839685382224892238775489290234925709219101706490267003355248695390581311683610300018725641968698874221866203098929409208488600404092495624816967379067418332131724116923045133248, 79856056661084143312273719820960947882041453598819361720182465048538322082757425435727848540556632709651979723750658413011006653459572705230108945830410282217644362827127472296445532133352140506882177581974343871659907860763308288980640551895320876006300450925602667573484024472223957685122168436251228646639830814044331483675954561771163913282248395378625789920695842471034435370440817679894057604965376036916811777069051616156668279442996980589962504263868342507819753691799399562246141541794800329, 1859880529634103947765511982567519585610372400829332203956973013696334107058562280398430750650457975476089342330588329925594249853471233620888889652466721096566831120295963980247299170582210984061364279405969475846914992773864791093682115712389825505713038028956721280607979203168459887885337391812132717209622558519423693864777081162423650482527149582915788822857811972638899717837584922824531028609176103120262859683273590735912286393915047147421550846900049323926449323734497414338425173927716760, 22352347634302012662914411099166063413622415953039669192780188352742565925307170738579631583052551724738846833229254504642243010309083826210854879354251367275310807513458877447041282920084237182705801597116710698196599845781398786626719115934378174876704069606142272101875133422207892540370618643744086575106920493246613579011773141351348013119543459721415025396846361088900268587094199821875959787037184687640076636310184859543830037949390236587814198899329347260613326363575248383616505851021234424, 860260911791980053361658807524291602960647799527559906820780924826379229328755996251392616255067565543169607068679225972824349293424498273188934714167641320675561420212102074887425313670476750301788767773467768020577846191515919746191695092457120784896354226944944796860349245640670372120162844217349114771887081040432508865873269792742609929239426345665673132786740921323213224464513316035488950481930847036642244056612420529500229169207862336696888339251121186381439676271512302786746239577831169, 11811864442703640093044339247278427162912316902224097476162965950103310828781837377734466544904981248990622997409526713811606954206400586726001830979348029470625926312765551375395331003136661341933490527619731728112521637015215112061996099001824950110416173180446516235593288819089610111809386827536763475366644857648789036080735464458335606983914622173932908805351932365472602560157381121900165851960068975204700765534595562406977205484534700959499532220116939551887406239172168447757316027215104269, 59862826542164720505682478957070528831983989954872229398015726521580212516247408960517814893916558927138890941668479945751810774579666959452382631626798655839411624993525069103100736632159266640517476891459096415819308495581813789839238322794370903127507935740831397985622699650684778986014210908912297346708458360380748261453205975116138031018757850283958072149341585267109234780704677710429082149821199558276922277728924742618282116375042977743277669116344582103014384617237052467471627818527462008, 44228649848011770681030415976427096294190525222298396644675720284697686796670488846797255485781857264239386065523593048215129934265344950306963095395974107245550930930428852984552284154579153325956534729886591770624358850166314580529106319218249095651874176814664215968156664924849996351065768675583084839106969246232623941254756221498342420981986600953372125527667887682998331655507543828052392705980784144422735441336344570284473033099290832552589826909223926893830517322145670618483217455656305874, 30493608115215350610868145989844636865943765320524281607989486893011868139926044868137347388360502599003489668873023151946768116531854594116929900278966408826027169181917443749806311079270792378786696373724404369460841966233398082145942505016715539989665435951726549265776672501826567230454180287686949837052998294539892201850858083717393793095832579159689819887927067547347703846698943992594575991789681240424056520859908826380711447838985892758302824254350500713471548986309592530595871514691381996, 67478133610979774263024038438320219856690780882169914855345786376379907005785026555796833625382351590607810759201055345759235577096821714439010975565884511656427366264111226572463600943435741720167363772523339613957126786829361585263314265367378071604964268085443622962838591329151429970851144275911980186213211022436292882009875056467372559913815262665791171201714180026135937520910902058497800746500590927680898543756307399226877790044602660998868536361077071721427756437323566361863516619216770635, 61182906522289702451727847349707241659192750187525240540088510552903736750640642101348097371010178550161642304777949667561883863432705347263341470668100105984802025166554084219690691296658163116781952695957488794790785503837962770473614263135411492493968051347476281044120329369540070460402922300055155022554604139518953223093048613127748315388766760861018163042032173264325143491604416998179513176394883942562006995311266051649266074390722010430750196132237788358021260867190536043654365551957637899, 88085460044566398891766631333801987679954857239535561273663556350738460788308175450446050132705241579179862612851347317156375107262004427975219226490723384006343952649060092244256132862128949366921911183776604095331235806283465033944560074199638371827827161528176703686422726680565100102818015584512561110634373520509529509739084477141783250493888578535884137447028902849783813347164749623721031975870435688286905017985946596118877335973062614965358700821071272859446859342852183230904767313824725309, 26197461067424690081908806503510182421053823787730572355119107250703921298412357026858951236441467371181351813096121631956774444891865400610239897693525700011729558621049721395071716017837656360516681492647309905650378695637372438945624496465077135528856300930725478361810062227258463758026842844006500563158443797157718937665474324313237461708147277273045030170849131097455610073843740803858198279752036500418457741632117777491852944325318551853616969763098099039398026699189597745459843130439526235, 72971266306385408081594557855782501660929994738245496181206265925493128464801504218876360022931985886528002617855746668395438158576126347465733485190941352495074101126988293087790665327566892532559901661353166265676556597285228751088731832548500118187819457064796466877177486031139114867514004525121449741603034192585431545512675084702814441345613577294188139610858868796128048305116236041305873389849119300253176584814272960300407043420553573138868471842714895565124581474279928421140202091852929972, 9621832625103333433632827383777334321106054977376547507847022880064202278956610058968687536963816653966831730394401554619616476178352092947474857317738517978931836182717195733206781368946706284827241524721636284038094467234268232888676978891355537730326580495990980873325633963579300435386493033974294147844538461506829033535302434546064004624027159874485175640988545327908300345302786266403005207118499002026246763938761518108121460656363897505864604956322179303973043535141698437818185782370805701, 58027647272397051618082463443807651108753738629584501097076118939816277472140634250695165222225687074286813522463578622582656644782421104853071937644046699651185354253751035696863800886667602825517944348442680819735226117871960474190270421075438753707253077836539652806436027211610805923953955795394980953500833527100170608172899022809176329295153601997458874124794762449398832150363173227369918801825656312165780938159235743794345745807406087035265927354024611141643213294138244995243095787132136855, 26406618281705099803326782865954423811327403257319610008649171538346405733741483764896406390096385983949140944059089494811271866744837944776687157812734626266924450175190593421990011696042930383051896415965189944363862222225869158490032053570393007834542499228111295882814666045042765024019580191968741192291045613597187223125126780086242771970907331961503261066238336550407530372992346495265983114596550241676192056895177172254368677044380159427138147640287659691541757167639794450487420362677341320, 57369910590176161151218520819161231327655732353925386897520989402026328165608094534431019155723897127807543034015781160082986738617810522863240287402904722561564749319560988214935034191962091813126561514028561088571353282517823987113341745563571877722950620307153081397307794614638552217366765877618099828850586142087695813511702998878056585740401108468357557862460582645216607130848402531680833428147907532824487916784275902432930617497485942928244915696760410419616209967041117713922780043961785342, 35302927320448692366140681953936587432692481371932982888219827904465999121957882598416753669941373630251740936485400224087944194688982643445338210283012787882641171836677759000294703078103828006616444906508587718032079469497409432310812933331072256638173660498014408921303011474991581617541660657155966062178958543539072080612202655029467670388651400696215157736401749942427718382810575956591831238631148595607713675599188753688892532732639218933386445135341097672471548196374261041304882192595620304, 60901337981081741845428262191928647783727253346773196951205154568703502343544092782467368761539710901279324016670729389411731822119470700000987952445878169863521115518528372445651125748428668629546860633058822092995521460867863531567313205341107972024270629754010641587384868039921951756545858350310522092405559203437268850169396674148764240449546088971710054539810916551561113711511973375224186398657438362332549394554580957565785211270454261385219282055200303813636477366214611911459683179543611032, 16906370884743992348457194413136199645934877801428826828409150801136331999505625565388373123609922767200145602462929762792444184214020768346991493526135247731349903169514751729852073018259423906383823938905485703495284975096189225431170549215280385835636521429275050457965624336242521405314240059487498768009384706692169553758532518167812599333036403810084331339098252243604242208492609618004539135800354023950134763626392590692568165011730213694070679359723862565156194018568126260722734626170753648, 4451533332455611917334690362433535774026004017275058165522372642788548441080876938457332924346773566461442073444568581300197641440502785435310877862652525782329070271383125910901049264411175473157821022467141366866203659795246345690662097035668698288785720540195970788664937738927515021671024023200867740748593482329456156584563702319369234369832730158080499657289092774575272138477060871508325250735403520552261448515504579184190420610013983177793205931826136154483513275689070663649136140710356367] : ZMod N)
def alpha_im_val : ZMod N := (reconstruct [93971056460129829580588942676246225536482336484209144379612955659761587073677172333283006378014954386329993091823198402995017535685057115706250571240102170048397, 24792997003480246366322298354880568477051492902450318501890912165693542202191854209801004880806236740714321306375986437878156325115775705922339109772354302522935301142993508765183102776877184433344677779090841872790913345236226199443861095788962559197355617184288094738792714942407866240842506198761556422567284909766820535049545681101975056052383551181853035092022526887346444359504105474102275752691995744363113898847310248185554817361393079667059876180174880322311076323804121174280139198375569554, 8542081298157491624026454477372840497959789195634522871270122431413814190419816497332803466418001120904643678584013516013697753359225979920073249194887724774117817520818009649685305496984279564975595243758084956578190981012644060125473666953386280193028781693701109972046835525597746817097585531005196017811076098047723297091345962708517523184988644806629983513228459664497185747053009191451130118993953152688462926796145198886441175218356528723274484315468463872780838290566418288868676721582641101, 31747038880138728121204673904959353000133029441069132792026595841979419437549821652690452752745804303810949770807590010547120612264709602474373301078696070860916728437377317275244479476739614476179774694355328212859272830537599714574080031171955523588142980485998458029615130046401951935352834544146309300161747157218750381588546543264225465808936493508601106389043573812711116471187066170713202554543908136967284955347802716109511241313213565908785450929520513488784967118984010724442806594384415615, 70319416979389794221253247954789740914419494056989890028329548501760380480972275312461684293281651745127554011191034426812557346143742723962432328352174317284705540880391482350418417145054895556597182689832761084615797174174923326022526482114921754525216216970463080344013783440045753843856697267430921477840617462141543999285432994188065602101680317119640414026226531468317308361253523242321254760447270287884238580542486004800970731762232835598622767006905001391152184566795123127335540100103248371, 26500119852463032678371819257712584108984776176348278065013992929906689673230398714529427367772251734241143270240737431772291793090286639360305800715043622104536931057725391446054579289319178254529214076485837974300818310490715460542201011153305322770004709771338355578335928516176265783451064260854892152936531126220595982993365580516704901592787046771581610593210265009652279163075286206145131414594592210085128704345641558335421837906513094708170484557540426535048472584942619330447378960851254047, 88532271722179562316562368188102356441345271207861643562708937627960606230564427741113701100056642251861330753294166171249541627149111035399946535799277924841093374552484167497735744562760819461070679795137574376227654863078120193755573885981192837337211740764027151526209095356826834280516961705885912215078654520781391474603917424717113817529619581380269856514498498022027708185905861273893068616449646777570022811369326874296207786253201283097389329776283294599850381443386751785846436450536308463, 32719810575094003328692774871854099256874316344726798942412178754391181985941131297032803906405643371983042839131738484079438523484350635334752655915667269060750962845230419233712784472665023812218665747604102935124661900950185477783544055547044177981126832532471082159509544002717651565739216862925806747988746163449279185927239350110426887998217851590398782079260884167572852144754850361478910615056617939331012393767738905064329780611768785096807039189599997203429862932558203538097828868954398629, 18999862515129491252789185696628341398977874890874773035789392515408188958722594769381897110893001601342593356770547208988221825596978399588219251198471577979439973624135659277628869584936571148939623136848544669260505095196894982073111543424672358228863443922101965468352764182870023266030510665711197962495897890909789946897210734949925975859303695279558470035915263680970540440506261143351897835059966750470716078633342364508504102828584890974103912927384466488581421818468315724394209248126397607, 5073987662488532073775495911323911762488617342479253387451430960925698271377117410850592856506754271246407566565466122883912511938772040977831793448247257804108072919885168669805001703556370900753486177791873974084240168361454149068826484436088610377099656301362883993572658030924041564151585973221307897615480271725285422825243983721961443508412954302913777698845723684607048598303236868189289063185140073861042469994852478775091437583781519162790174344063334980328540393168097883347697702345452663, 97775042621759957689827842575325827356409205228231526324213281694373354841821013394438850607000767326328936350142732254642943022954585782167488686990980819331035221663240980589124497265721452953425527427044322487556736580112608741097397244920673499442672764051476633667519657595489574022513753472678456786787085304509659589826210468070701384573826879866461384618063228405170326909769051396534167357797354552044487987337434335569088346247543041794212447319958212326554028221129545428244474644440706334, 98181359260096191565567207925253621624804835562787860661602926378666735556403025504963928230476045767367304954178538851274027530649953331415941362219817724394547703587932625296007191441280273694645335129287406826481617201247562461690936924239890218664195159237341972191193752310228257525125513287868474951558497267076566816263939566406407373013031303032688716431706471986690471636399734407399909232902859803998869315987645487194821467254522519786081016390139685323807165609278329473215238934170598190, 86121717754858360939245377672776492713800834828865383553540953086326627408078588644975910341404265445882401341670916769781431520123521788595284987941203112827602258690977494098163376887296014581430734576005461074749182238441381030023533889694074240962397883659980072665900828990146371538456395328432283535086223003113097623085801167011154946633229439389725219243047615294426814315968837918427780711399401241982082490184865534194818853783887045700267560215786451125623965319676648478444292675932459698, 84198669897976791357021389591896394514426964596824867963730990083821205174009907742850980504112051962737851894833991784585022670514229021815304038006649182150052432177840994811371825041565056459787439452011229070873211497985248047557659974276873700686933887371597760910554324793305067061640201313932109090680975020443141901251779416114233099365035116776935321215914559819494647347459650217355929142567522588376369578511650328408995104023449683344769866444633875546857382820886235692855139906581237365, 4544012356485802008652340087856701566622860666176030134373402426940606929778767957668399434608457038499904247097359702832765541225545419923457968602042867626490376892641868969628105086088103172534163335933575640951057906467779642398256042999025998610751702001129604567628960337217587899282671187342946780798770446290293482650289115160682840663280766552928056715442851888478928223362904811966878864325697315251752078481796360023260344575297120679239466220138457746705255569971004768284495942900985770, 82208746219911824657108990083720479287336863915710748811617261579891952609077476117395264345083117064415182670173206134475479073181896526946810117078475850269582561518987977005234185446036558747843499659614501821057782098742773433061720588987592240015561768472118260240806475823524871151527417616367192544612148819257589340014504911774040719762801722433098223888707784006462718455119769150535901253942490362603709287688299862502709053176390200262166541556091490569376283654923243064649684448901265619, 23627295413978126656536524615712627338741406704633498838021800925017810582157500569168062069359551490738915151129205085927928584687871867298827545863861362794570051582932370460011112895227841127164389268786247815659355515893696932993044534768202145896615100718864899969931891508833299456033833920583258960875681184830348559660463036747659384465827113539075364415098869867752660094451447874361364014685128748277896598928113358084937729108708131838488836655375022192739804574964239357423538949333021022, 54055933331263168813497933051727088782591675565341353875785642366226305749700119913538105233992195091723255471493505418836139321799460846554891771020566326177877552156090624128640157154629280262923556001789662755709124328932452567867463855399764963634478329438115939663777434519235875502048384451060955390212911367432519543584560507145187446248166899639098135244618830651354180170320011036910050197122030143505318910635185190782557717628868598105798881624530562810127671429237689710822325083506735815, 63641641193538553955363210074906457657385243678152312987570731373319429394270173906939118759871218093621835944160245321053523888750971306408397636101963158473189249372671934420989545375465119857524853996227715628677764174801455437147243286713505705749635918783974635719087351918003168819734888710407025390371893469133862470789205991314039550680557086133157418770984451063254690857023417127023382592103569060765930864356767370783296747532465175375523508246140988642622387116277230827489530749561349562, 22798176480999400194729776430118905692881512728645795733531414246006894355432361850520266658260715361195685602862191648942603221382105774832138924763438128580228033043137564280094436492961868842726116183711935336354606202573185304821907514251690733591493915652178316568356094921507932008622500018183920689735815963338656003078806868346777371722197841598419147940075905401104126043874710903320432086136572409536501046537480918484530071858519493297538717079985023535581503968392053318158826033734862984, 40987698455507377752895966706793108796456711047268067664000916050358174386925832201821591169994467015198807345667449810386357262808166279038782840207825984765974793136931351386503605318953199606378117374676197329810706430613996367105910102222164302803425040801467891710910156262962920502207866345230431333559021651326457808983181652785968343880284355153052926028548282704643718521516478897715177078143868211287923917221680793567008164366198906075675479626244246906612577861268037723722591022145854113, 33387091280523204338708968064357819858066250823241038220343265058696997138122617631655617092948824087660892820321822300166775370455647447829892799155864136211390751767913904868371602405160457693040856627079487813168049412568403603439698325419923959484651414666887060855956780197790082920402660540013986293987848935894572308584516657413588051922257446159661476318115813916574119915052818453319078550262778218816087264013243760743289697433226013666254373708934261295503342364733014813894572655542441174, 36407350055228222578767502355607383261049546623869584724308080521540585962476927887958794923680041155607154872617072325817798691927033843642242647753892170693726585406011889768369887232368613851248959147306591776723611724144728949269231811166555902409154936889750572441333248837088056457749659299402262912912680771075287043821670762883547507213482616866403635254645418270836051897924880132576729755099795235766399427796029603382898040781821919788399488627837758562310552953803477796572240957522568129, 50814002344357734033731453016847439441511474998402119247278179067524694225120628441087852231606990604945562655682906251192751865336121166688034382423880297001812114156299224195885177802569838842093613029485410808807974603129638489801712139827822441360735772919395096683573399280577675082851964062498690862930093503943648923523126707809023509369247229844141716699249588770013195566195309172195693138386806288537228103343148689506706280706959097731464411427072024365464934301167881926547681495597939057, 80149644500057331188661879428666686978055193852266580429962096168260954800948739335287491387594658534469026731566698926476074986800530497583458881073535019697234810116259784155750611570387924884778709047008216317477662638602981841226272161198375245746342396748358758892796192738754199799502035283229369391859959494001754271463267062918928529689022321944512518531467854724545445670944117066952852838934176898232504567339661286226365025568291201354495302201540687229330285190948525489696844852433237880, 71213580709446666700064331746847910818495127058112103170960554533034489528725203022885399680180726125692074629322745269617867097211871843761934304979689967401879573146718128358378549184727459653294392145255537318890054471225132506274073278816043672362194756697744258690585918254171466521805674448661466048236879504886513361025352327716505129678614842031062312954459210185133068911840262743943597974964150197057854808700546708564209960049154979374300226192999341785070772622445674625264350235538860776, 15540406592068582797063641216105695128289682001591766862507794333001324371444152518883706557369594590780357801579071896614946450141198675536913915344426560918872146627825851121667558454382847713635243144628900577532151210239520061642531411364630475017661640095957351373875994403386387656829475443034045820146756043491779533043725858456270985599143775226092075096477857519156578412647942649760030820161746346225060589446077643443319816553416303056719182601040037737444308046923848929781981722277097390, 22083167310093342624476292512497757151375310002342194694137630856983895264429945748462886703517114023885461690028881783856473738993330079776762927463904839449504681851893370534450706909420129215930600215482195139434264978120220382980399937903687630427942291764917833293988416145946762504315543045370864214830816318924535111474101224999597625353208660886079087752265931598830883403087998203898726997610869372656885697775481402366233620162070050137301106916052695400314453831371642845792164922885964147, 23643101377190661190101023240225308023833521595716018838158363281304914509123469152112153518119336540022003528885517283013078689621065363656877885998140253617482636900008238126127308766559646123358711973378466797379669550414023209577233165349819577282485070006006628053104325495423068314772367776516867344886901643533416490899587583775955299575331055574305619383221505652691517935973477252491615855596855930263715269357969731978972813785968850487107857882295689528893145922852801667319878998953430382, 44885660805414760504580172990450914786428162821755388829508293174464031799898452037827581590177808394330903601567282495333977687516595760977112709253321155143242381528550788039647834162916171978411270435694776990526227792880655259852023442009162532452958509188687131289095149704466723301148892065699061873685671449578555347481930352849326390858194134383464803694629342105549305876310069711329385688098569670893466900642792825280781744595854913863104856964164004391950383231323170773355821989280499388, 87790700262499368394488749678009176488263830503517883149435511034462532758931904545872114232758257229080980872262637297782121621395927434698250782363072108648605842709358120441575189381296312304781103058169014524616366804824982972939442027277305523081523777660977906318645556844202501361590295841477366684809375019203634368547187261831740177538633646636608519248535425410555880958067435600174599717729550184931670278105483326226650937654862914271996526616297013535230643873289696878024870243828677871, 34183492190083677467088731338076375726822344348579028012052303558109972031129680488465064479134667657098213786315051676720506463825965501479992765787977580183420526851672595824858527027345809446863665409556022266942424985294402838718589433259423943578670810790245632171765614835151837193134540036924749447638224267218399405671749224968350918582877966658083819431063081511113599206806855890695530253022503285195074418651425095214566710709555834471272437801515200232342513587643857663348595917310876231, 56324957351882849156817666043252677555243091361922803682306940258187711017230569426674025125083678936449943877325324771145746294704022154218774532335134594360990269636850365250412360389372865531952593603654826776096709771459724549752961919856670232111202074877165519031324852273477838541630539380425693890966675747472392185266017471049022405931951749970203334391752445949166123308248842168778806563402582746784257464639586238430177733671104150781884024456053061548966154257284680226419563352181080608, 68842154438995282373122766751538458609494665934113772190261047558726504169665529847045769645136984722713488989207156446237093256935319060272161361141302789882126157932563910011655003784573836815384169867103856452554333884869460017750091766230935846285324026659101342986723844792330892895862734395244901359566517089525620177649461304023944107486368081832091609966308825590199874138598930372123711117012071991051646611611718401947314047136846058332021068427781094308694853641157168647448287011692147469, 24626158486890950159667962310166201848506002186932578548595040618464665741068714297250519453411894955348164602798144706274623784707504616689090003581276738833837299810559672852376279866402342453956316162629659892181712441032588624731542640355963223140437076006348889671962706701416882225740957972203921985943146865863766871809727927535270918588480996956847383115328401601605708981732457720544303299673209769300485133617447646717276103028473985460365412755626375146022043144624625654218057724869325278, 22417704084663813723634160124419998148117953197687407761967681994028948626833187023958390138212032411847619535397765887430120505032427114339470646118081262105530629866348998233793438881591194359852011018721846648510101178415031102132323182935685499045669710258795623758649899475811139066623198344593074008525433170595278500085570305900321193080952615035623598119446108881721309255409233621664405259125386538631372185574269739121906484500724857987065585507135057842596043802454411820615276045011949539, 96978153798071558225843836912011971965497709054047620405637337097621444114495470418083376151585284048855789251355248337032894841864382325577940688335458719602563717547316767103828902458841858021881410047472198577466759667407684056145583850917310886220592674126216627405339233487156564687627833245057134086785267998082651726060325740289183919351770245523448537457213504254974373668311024085081141522492565187905288606843473991875469379359106978630991762428611204184218019278551432490735846187896900054, 24231480198109264872416246199339780625559239611942046712269493188909425580930602743678195331053844571900180052759524788631178876698588245723375306253734326151890376466173463883492652536473558494552067811369946090451194131712686132207537627826709710168483442155944143902962753629627597751943675170068918054312186385656729448589207679589467951042338577462628215984324658717540270184389236248381159371033905889736627616591610292826882757363916937503973683865736421848967360864448786283561795572279177996] : ZMod N)
def alpha_const : LucasRing N 5 := ⟨alpha_re_val, alpha_im_val⟩

def v2_re_val : ZMod N := (reconstruct [83609764703010399045072315072052636047042541313830934396329284888196257866655695505541062267242869508292287797633442623237920790130386645644416744748845418953047, 37812599070998937309497229215040223523491145614797881025106956188925648208986751870577614122401120746013558818550819750449697429453224710022570003188598451870562977990413140541839098946798903218366909018317986917677236461282166974910973093844509544475696849357024556973272439956206465983429838303046554887028563582207187831331251871394412647873320192661251589149976155073666451123391478680600991070544356643638242624445471411903817225967448996482470692021880738000673781903123681851653376187933327978, 21800502744418268423202007932479991372593624832875286121795608534330537024776198292683085730079505289483328547934315781563717875725930391798432342361711874696264159387888980541413532172273970185735229483314191341174154958105954617002560662454320384400911599729106205903509017740354070175505309854611970058212572891475911926222424045692275045923489607681298650061092628480185684771592776306865104948864138152459196060588691085261101573631292413888435818949741123449792445086258437487704338431521262306, 62745858905815156961833602503631816241342471886364410748702494847841555038856639795200024991721470734174445871939324335191381779358968244274087638319817696161156802642543659860556339746041704708069458383556123110348962028233426013443324601104433591143788385282954727858623260344287486416371582328202892729818571712825010107617664834455372409777020929294596763235412389456590147879367092412922066710089571788383842089196106619735815656695727853306209334383493079999704545864757794567435674417560788924, 16608389749268966980299600735771677618136731870530177216323396610729294743462139743312236986884704440529377709322186755840302425590313305403058247288756771878998230958397685824106165289771004644411766318548750556110341752691000851372154381259694257646486048826379320852034995824594850374823202598909518376550172333222568464109375402508192131252890670913717190998340638374360215289568224649808640859982304110713310294141557188317624391036702026587317284396764077548839297349293883958554068945406224749, 61976046449488720240299005578186578092039023475886213463376295056892389028747446825110556533656841762475064297285232810281723676890640365838885314291843164752391924432215629990725491974385595748725916177264901462242372748123729510365072333916499461194695747168407819424695083761710361978270418519294973593708324897730329716216251671337907377738612314967688955237953038254575237972876998632809837085760240840443602584821478684568356767536974926471618603712333552026425168940234970853142294509745135226, 18297304087498957380158358949488717321992078317798688097704283319378603738135143588899453108866182472073006183038912985192463785544163190998801426433381835008504930545378964590488501356821588761006089167726775372402984946651041997357345804601038889847758136404915469985129568722090133548440664806489564165449914738773640811215494535635233501690798853995200547674940290482858044151455192680053957539680555370414938979196009852009655789421622526341478914004483206044410527311064940388606821597353028888, 15654972402471447885733065949442491959768416878842115327298791489654575448354192452884764801742090450115395491906578165763766248996713232247626236043009054024213532919102585428531525723435910994537514353309803060844471437456116051280269138350115527688448685221901205546588921064426317985607462312648128554316479881716255453484140005785742628295005993217642338781721203085238266175834737320848562374609061312660553476763556701261429606798121464817030575419662121977394804512676985469075981151473851423, 47354569779999826338549237672440177567831912449787765862370840323943014025622572982661332043151950454342312511914044945877590992436882492027281978875576093278091162528016898741318484154646547401156324581220636623460585586236496912921476041743530193171597407435517594768732148641384926768308392275516185940680446834709946057357830103459660026974520215799133672550512338801707223914028680548270030529918300276809011772097810504469209588601556538796538013934926245738326955382311068207263743536220411834, 23806722002994910412952940310768936020068380193256336802466769344210223363273036272277671559850346390935058581883046610318044139984721142941530633086891857539683722877440776127546662084122893550657595819258306438092581671944367339605802766623774503575986928590728028454561074998259750262351422876663426728223358199140724034888967978708852119404198131163727866421616693355692373716192169431231153435846004139813757845747818684262015644436662949815450348146457536558381579829217714650370237714870505866, 38851374528205395817789157388485976062559320030861282448305402418593976782984986441494575315276578488432996507906888434429912431404384251612529320946907491806727183315089520984349490687897447951473523124913272752836807447337757600879354170449183823386671210054531543902314353244418386863963775625807702380916756595742247548676811568770828397394104203574940659814629213944216559909680525714448814044815162149927542195958320351234185339635515684009171890702297379754634353059071279756593370359783640781, 64652234018020878351399135812611673107545275901481533759321120317386491626884887335687832267930889301862925610004596043274598896790577132804792860541147800322880834046050127850963491448938805603348042110421512355390172270683179955455949707227460739664669385322028385053509092636701286497495835563762366738607811991834128047540633240598183373069999945119658018057213273828427765942629416511563787659922387898232879436756781531646163532400596655885418890345492704993892734526051575918592090023198601648, 14119065346631480274309866960137369331570366953051541112196353859758367141580591627274786001110416888065319704483952667311716683748022741949080727718065962355721098701275153201110408165435956987574418844265678423866459447683256740310202994593196564909614702988650281848759165879962169317160838523651100321258130357315544609671081989543341213162495202407802066854351295315456697861051201968145124804564018913764483932679208296651886947424678005568756979590113870080013234384531195698486401741949838009, 64067822890185664893793875242055913833521011594125054154013628186231587180580176604431944081549098744673515840004711888792395913869317135275351386296156050429418430024181762101950882539952919735696176219735511669866388017804605000675731981158835475053746949570934287001812931101324569929315438599269935706952531334102798841144527550432449582019547973024029168473896377861534014081881962951493801523829778431389651578337385078724617097142421101941265748571977735675798002199251219272961336884276756617, 11069433486099224392200154313314134059887633409328656713943590636368858303486850857508368759739893966364663252940311553877983980406572739214624410375335735552573283818044093840799312724461128935301563897211899289369287116428819902389986974229198836454504186573537605043952076037244715840575992039611105991979974594563429850059620890635022068073554312832614834111219594556264585469139087542055647063217753453285349362886705657800333339382352815567744419320172896565659378808662283764316648479834889294, 51747208576027628664594165429685411263352326461518468004679164018108645669938742211011225868476302617855759290593634865917208446509600258829210913154357345847582218886983003497740543126904726506399948657776675365923703705500829898077621780267855000001840532963828267252804050784483675614289989950971072954559254684764589894622998903721944923152708802608779034560455362719816936866620858789006115930745562129519123742643383700769202643882085058969131646798384792591227257161635550239721441124213412927, 4363077364356533990155544689238554498144556962166338953477829709891223777663142370687005603294011410712088503373871410289880424069451595440973116312117723039370548303772519312688187111851367677878334854868758535293797636213717292220868224252499083386714564261935476027256819243075261980996078351126635912884365648447346077592663065516672525055347540106282528229730643436185308953066215600914671413494424700158596291796461118408826892302993762464623795228178174240702214096733468470673829951309428594, 63381829754357622964650830079071394282438975944210658424880387498721169384212133918669457860156648593997073762232175254547192063848352696695314260598277249377955967809698123623074736426137332724026599164392224402616882087318395849833167596830012978525870185702499404663637666806644244408159152883728626099165573734191041552593033228180686273673419223583155693055365680966550717976881577255116913806077623348554650579102456367058505839938302902993095421621683308734103714275204541014534056708465553631, 59954393697609088370066345891834638477715737574284163645395548234543738849430076855467471752817025977190454324382596509880253305857561178602203978988230755979512169861920181525265503141612721126284378233689055175559174878910943680381636505194287750440775543776332011036496773152306245839975800366582462530937319015615656064654949504191741133447391487980435422305997508391495271780142844777456157111648711457928804605249614236694097110421235409707257523010415078030787181815777345291574984511212788447, 1136089589422010837312894115471434798403526327643996758105327295211438512342427785577624034855338766166040963575945082325035970559828160989701231935868934119566482456767740875584882804015557604360987323600813842620375686506039957211430803013637501571680048405372053509773651378135496160076760961944857958542432962120055022435980559572713753641583388357484272707302563463729812714279125020307351326819683295437683273343252578148620253569250672451380360062848690971722226563244993375987256859829109216, 26749868218865118483293917007424351084139253520628359747522844444785161993718089905797006162569293318265840091765693361499483318267491426012580932988364253499680358585615764612375105792958902765811607524521967161531548256880078348184659573121148658542032206929253217591805382959879648967487367993265757222607119500488855114638357298066745183801745525497491830214844091124926520103269010829822252328886767705379511912601223126764063393007508062210651883524258756679667682470340918756666666267567717493, 74810325609716398911758646980163682423177152684504675624584336791926515114039181012263483692177424143205115267894703731427424063339541406578781444379436532626084155137326417648900733985965543337460326174438479955813241243094732079080405549194526722687520016310441016349720588715740964335762786009758110506626491800151214090208820584199708904919248568783244881310481802005030216139842640761279474086524297954540087480804841845750154583350158326541959072262434471150586448490984775667819145860835381132, 47844139435656097333400123470469533534036898658637668473734781576436945090491784062414526064438654338894672432567119813835431091362973595199672817872356924214691905570552180393873903890026137301310789108777668285891332161675069895776556700299050538333054248883990147661382478616849999712458833709546229099898233190545992292016841459178866822626492279087903655106398314222445717554986628341258971543905461931500684063476175591647725860291582895010161173157280750350635445585991970072484329392266224978, 47445766558216341923820648407594074950315771890140613202206401883533086782747921477345059771421177261956580607785763037361370752439087768532401450519326382463403698925259892168518345890746430232282714857728225839182089951470558781787810619129924119317314122708026466526887741798703314113218542541352378628469285067679692191519550066139561016918699935567314287605142375916058734877857410364171065773916616197479320511419663056299621190439216971339027765159114233481287446712104198476721547791933767153, 25080218437624823439436690527297664657955707699931279132310266423919290165812311743456112843112388350123406559572587810655289164892498182278407431814283818749616608905671684284701591986659290649399775241708675141365201429623260114967241408343458934421462204880130790588217222754200847443224587069090234023730652537524432084463552759088462749907869299245189615280686596263405146656727697147169669447347466802941000410273822947288725589265556338952820155372402932081927223983526668980824115432585124328, 54043210434183104992267523114488649290882905820260524535830132349891413218650092762686649234496598660979655079481127984969176583449197260368048647826321722355309816641373830656322328069066559747913472291780833214950663509515451942326464078069315488491398317872704189622218259121311551408712061440690958953373194934865932329567400263969941161843726185757425858535118161760887760240668639302010614904767482490381310319677796855345846905996211362054584018990571996933793368941027327180424452423061610662, 78319271784075466333676374189411861815499401202977446354443910910616243399226715430545187303961769649889087968773489068574090852094013416903408242955571731446717286267082852259472741438700271757078693584936809941864786952471428837128578208903945985004129792388215396794612013443373555054258260331601944800537806192926547097341165883972272584143915794377970455756708310432685165069969481436573182008365138231183923346573653952236896517095388930338054119878740528530329341267778270183062494154457212219, 25822013427234857776395939398866322791758749288702816093627523743745020297698135024716331590909319128517051440901248732130258680022908940412187854695033599605806428717558498817253338168906062735325528508577422727746955516230422672945789669407374697032632654349991476894680415564761978640578514023029983049030914212625406951971728269811307470508051899912547520661869840381819903566054705626643398197667617891729932222111935346604570299360897381621359424630192174774701229681872172987486516387230971128, 56683541476209670179826900495763303414401597455163131968854961553674259484755197442754988778464224488355635543111449343477115037131747547722698857859524473437874278094392492884149807552404641317413730716948590731194365808881766636482084009567518197324467297113229336540519168732390550120252237775410079356424440487513342300858119670482447471320063577626376888269111908747799211937149942959370526391400906210162837387530896364189360268033387981359168247861705097226744547190145957321222240760362918586, 96862826382200747202170769778197097802716116002340700585651107292195113619724638904598776429997216277355399044419147697094258440886477233751742534744089704011807489106244533077046210852936543059329338857760967572440029615740178243583006475218341718300544719401429896193357799327417302115916093904263903999529226623226286545851461445122380427400169583723367510391909661158362266546513563559761400820755015445500052192320288193935128953337874263851208816743159463855570969075013547781207533854315970708, 60302377509333489780775361505450365574617380445327839747196536179018281591306734945949099294887283449916995712619051736807850634794118147047225666268900680892124329270189296605187060818775703504831878739601769285737022273068721399192374813782551862856634378078536571271044981331434438797474936990088165117024957562820171974706152560388263281730882194097554136659705448054098145498954774848160794619477685154207113601397854970280224827902336260662201957712332051205527314844212245319328111700304841435, 88448864040262254946087587023047220809054229236169882812092806089176264583922540436851592491495291302618475471424161417213480956457605090630670891797507591390991408328766941210983105297786296351790010361854362985300922734045048167666806336879641406960975043441549060397775612115032104212168511640330911747510106719707652619932816395713191557351141735665649398845430183008610196092827953178978775470929560733668371629549992696125919564982016293032343376928542532998025783664390326385153256229700905149, 81550722853032500797006088489756871841581370131357074748857385931424971144018959520280897876966002568855961726768097167120092672235296440553113222368316414133539689818235330626611049257707930565139253297586862543079711957591879362236095292415078323929742999203114140545104303448503932322104243755770713077615889800454312731365918649979184598365521601440061531803534997389612579691434988374247788880400477398804757274490991104119108311875641436516687930425845744934479752727459602135151512325834304497, 15422239131741148012938899113822038167252462793602342751012138717899413034466827345353464634912927194035025800335054881735237754820936520993587514963477915999679660881643987120060608181396689809756383758948273435802068458217855748780445579662343642422683734111637401035044073839735923710084479159356761962168532568506798471914796519793269974673269590485473109142176498527489861321227718493475810419165072383853159413416448052401195042044440943805453364852244925838015719580856574231691161811471006221, 42017329377076062699466710092272500578112663547592413790298415296597648302733457844128360735153953363512219105735222893143661870951854136078226676022505579681156123019292727058791108057143578893490894899714924677553516008446454686838849696404422209167250670558633612320267939180471936326377722282501732415946319006887169809340155556037885459351168650516028614992217574257209793817602570891359070997736039201922695170584757858889591979837831990652927924410900666045997336806769147471022857280316629027, 50561852713263816117823271880764054392091024302360475551326436502337094021043276904641194626127784840796336861865616951633662728370101173424278241841980087553703566485573774697642319291279882688415432417843709329364675702351503072732538348996250843486523277804696544042459624614254391561806477787079568096881586942133960367206139969779806465517479091944023451428188687016826088130149240514891271344779755136177913806049185946476348411214440272232891665798001792447383396826056208042011629113198812771, 54725890961587476428715143701828306683471233196173055236245874751686508961940056344336317773011464486726389420684010686523063837774974122982806245284259631637913129422519714044072414910877753112591035013041862765734905040669544706771663787573090386386016154738480942038610356932880011038532885544313936677673562958759243800992429637980886514731675456156158565035906434716407310557639073527219762265933254919728149784461886553771830436247051110900328954551465265085036514583443715114541077526425890444, 31732320136101280076416488481518936643780020204390805926736557788679430268369061269267204122007188151096288828517381322145041770504733545649734212992284392209188299201770055461734007818260110383902222485276118448250370143306583657162649436492570442012705783257854342483615469807411853501308749061590188171483849741612871216532196160239883031054405865878612340856033703285980415472306486371027724517540573300265781861918496508843773416304454562446574004824412757507217981504683879395099253661697860828] : ZMod N)
def v2_im_val : ZMod N := (reconstruct [0] : ZMod N)
def v2_const : LucasRing N 5 := ⟨v2_re_val, v2_im_val⟩

def v3_re_val : ZMod N := (reconstruct [83609764703010399045072315072052636047042541313830934396329284888196257866655695505541062267242869508292287797633442623237920790130386645644416744748845418953047, 37812599070998937309497229215040223523491145614797881025106956188925648208986751870577614122401120746013558818550819750449697429453224710022570003188598451870562977990413140541839098946798903218366909018317986917677236461282166974910973093844509544475696849357024556973272439956206465983429838303046554887028563582207187831331251871394412647873320192661251589149976155073666451123391478680600991070544356643638242624445471411903817225967448996482470692021880738000673781903123681851653376187933327978, 21800502744418268423202007932479991372593624832875286121795608534330537024776198292683085730079505289483328547934315781563717875725930391798432342361711874696264159387888980541413532172273970185735229483314191341174154958105954617002560662454320384400911599729106205903509017740354070175505309854611970058212572891475911926222424045692275045923489607681298650061092628480185684771592776306865104948864138152459196060588691085261101573631292413888435818949741123449792445086258437487704338431521262306, 62745858905815156961833602503631816241342471886364410748702494847841555038856639795200024991721470734174445871939324335191381779358968244274087638319817696161156802642543659860556339746041704708069458383556123110348962028233426013443324601104433591143788385282954727858623260344287486416371582328202892729818571712825010107617664834455372409777020929294596763235412389456590147879367092412922066710089571788383842089196106619735815656695727853306209334383493079999704545864757794567435674417560788924, 16608389749268966980299600735771677618136731870530177216323396610729294743462139743312236986884704440529377709322186755840302425590313305403058247288756771878998230958397685824106165289771004644411766318548750556110341752691000851372154381259694257646486048826379320852034995824594850374823202598909518376550172333222568464109375402508192131252890670913717190998340638374360215289568224649808640859982304110713310294141557188317624391036702026587317284396764077548839297349293883958554068945406224749, 61976046449488720240299005578186578092039023475886213463376295056892389028747446825110556533656841762475064297285232810281723676890640365838885314291843164752391924432215629990725491974385595748725916177264901462242372748123729510365072333916499461194695747168407819424695083761710361978270418519294973593708324897730329716216251671337907377738612314967688955237953038254575237972876998632809837085760240840443602584821478684568356767536974926471618603712333552026425168940234970853142294509745135226, 18297304087498957380158358949488717321992078317798688097704283319378603738135143588899453108866182472073006183038912985192463785544163190998801426433381835008504930545378964590488501356821588761006089167726775372402984946651041997357345804601038889847758136404915469985129568722090133548440664806489564165449914738773640811215494535635233501690798853995200547674940290482858044151455192680053957539680555370414938979196009852009655789421622526341478914004483206044410527311064940388606821597353028888, 15654972402471447885733065949442491959768416878842115327298791489654575448354192452884764801742090450115395491906578165763766248996713232247626236043009054024213532919102585428531525723435910994537514353309803060844471437456116051280269138350115527688448685221901205546588921064426317985607462312648128554316479881716255453484140005785742628295005993217642338781721203085238266175834737320848562374609061312660553476763556701261429606798121464817030575419662121977394804512676985469075981151473851423, 47354569779999826338549237672440177567831912449787765862370840323943014025622572982661332043151950454342312511914044945877590992436882492027281978875576093278091162528016898741318484154646547401156324581220636623460585586236496912921476041743530193171597407435517594768732148641384926768308392275516185940680446834709946057357830103459660026974520215799133672550512338801707223914028680548270030529918300276809011772097810504469209588601556538796538013934926245738326955382311068207263743536220411834, 23806722002994910412952940310768936020068380193256336802466769344210223363273036272277671559850346390935058581883046610318044139984721142941530633086891857539683722877440776127546662084122893550657595819258306438092581671944367339605802766623774503575986928590728028454561074998259750262351422876663426728223358199140724034888967978708852119404198131163727866421616693355692373716192169431231153435846004139813757845747818684262015644436662949815450348146457536558381579829217714650370237714870505866, 38851374528205395817789157388485976062559320030861282448305402418593976782984986441494575315276578488432996507906888434429912431404384251612529320946907491806727183315089520984349490687897447951473523124913272752836807447337757600879354170449183823386671210054531543902314353244418386863963775625807702380916756595742247548676811568770828397394104203574940659814629213944216559909680525714448814044815162149927542195958320351234185339635515684009171890702297379754634353059071279756593370359783640781, 64652234018020878351399135812611673107545275901481533759321120317386491626884887335687832267930889301862925610004596043274598896790577132804792860541147800322880834046050127850963491448938805603348042110421512355390172270683179955455949707227460739664669385322028385053509092636701286497495835563762366738607811991834128047540633240598183373069999945119658018057213273828427765942629416511563787659922387898232879436756781531646163532400596655885418890345492704993892734526051575918592090023198601648, 14119065346631480274309866960137369331570366953051541112196353859758367141580591627274786001110416888065319704483952667311716683748022741949080727718065962355721098701275153201110408165435956987574418844265678423866459447683256740310202994593196564909614702988650281848759165879962169317160838523651100321258130357315544609671081989543341213162495202407802066854351295315456697861051201968145124804564018913764483932679208296651886947424678005568756979590113870080013234384531195698486401741949838009, 64067822890185664893793875242055913833521011594125054154013628186231587180580176604431944081549098744673515840004711888792395913869317135275351386296156050429418430024181762101950882539952919735696176219735511669866388017804605000675731981158835475053746949570934287001812931101324569929315438599269935706952531334102798841144527550432449582019547973024029168473896377861534014081881962951493801523829778431389651578337385078724617097142421101941265748571977735675798002199251219272961336884276756617, 11069433486099224392200154313314134059887633409328656713943590636368858303486850857508368759739893966364663252940311553877983980406572739214624410375335735552573283818044093840799312724461128935301563897211899289369287116428819902389986974229198836454504186573537605043952076037244715840575992039611105991979974594563429850059620890635022068073554312832614834111219594556264585469139087542055647063217753453285349362886705657800333339382352815567744419320172896565659378808662283764316648479834889294, 51747208576027628664594165429685411263352326461518468004679164018108645669938742211011225868476302617855759290593634865917208446509600258829210913154357345847582218886983003497740543126904726506399948657776675365923703705500829898077621780267855000001840532963828267252804050784483675614289989950971072954559254684764589894622998903721944923152708802608779034560455362719816936866620858789006115930745562129519123742643383700769202643882085058969131646798384792591227257161635550239721441124213412927, 4363077364356533990155544689238554498144556962166338953477829709891223777663142370687005603294011410712088503373871410289880424069451595440973116312117723039370548303772519312688187111851367677878334854868758535293797636213717292220868224252499083386714564261935476027256819243075261980996078351126635912884365648447346077592663065516672525055347540106282528229730643436185308953066215600914671413494424700158596291796461118408826892302993762464623795228178174240702214096733468470673829951309428594, 63381829754357622964650830079071394282438975944210658424880387498721169384212133918669457860156648593997073762232175254547192063848352696695314260598277249377955967809698123623074736426137332724026599164392224402616882087318395849833167596830012978525870185702499404663637666806644244408159152883728626099165573734191041552593033228180686273673419223583155693055365680966550717976881577255116913806077623348554650579102456367058505839938302902993095421621683308734103714275204541014534056708465553631, 59954393697609088370066345891834638477715737574284163645395548234543738849430076855467471752817025977190454324382596509880253305857561178602203978988230755979512169861920181525265503141612721126284378233689055175559174878910943680381636505194287750440775543776332011036496773152306245839975800366582462530937319015615656064654949504191741133447391487980435422305997508391495271780142844777456157111648711457928804605249614236694097110421235409707257523010415078030787181815777345291574984511212788447, 1136089589422010837312894115471434798403526327643996758105327295211438512342427785577624034855338766166040963575945082325035970559828160989701231935868934119566482456767740875584882804015557604360987323600813842620375686506039957211430803013637501571680048405372053509773651378135496160076760961944857958542432962120055022435980559572713753641583388357484272707302563463729812714279125020307351326819683295437683273343252578148620253569250672451380360062848690971722226563244993375987256859829109216, 26749868218865118483293917007424351084139253520628359747522844444785161993718089905797006162569293318265840091765693361499483318267491426012580932988364253499680358585615764612375105792958902765811607524521967161531548256880078348184659573121148658542032206929253217591805382959879648967487367993265757222607119500488855114638357298066745183801745525497491830214844091124926520103269010829822252328886767705379511912601223126764063393007508062210651883524258756679667682470340918756666666267567717493, 74810325609716398911758646980163682423177152684504675624584336791926515114039181012263483692177424143205115267894703731427424063339541406578781444379436532626084155137326417648900733985965543337460326174438479955813241243094732079080405549194526722687520016310441016349720588715740964335762786009758110506626491800151214090208820584199708904919248568783244881310481802005030216139842640761279474086524297954540087480804841845750154583350158326541959072262434471150586448490984775667819145860835381132, 47844139435656097333400123470469533534036898658637668473734781576436945090491784062414526064438654338894672432567119813835431091362973595199672817872356924214691905570552180393873903890026137301310789108777668285891332161675069895776556700299050538333054248883990147661382478616849999712458833709546229099898233190545992292016841459178866822626492279087903655106398314222445717554986628341258971543905461931500684063476175591647725860291582895010161173157280750350635445585991970072484329392266224978, 47445766558216341923820648407594074950315771890140613202206401883533086782747921477345059771421177261956580607785763037361370752439087768532401450519326382463403698925259892168518345890746430232282714857728225839182089951470558781787810619129924119317314122708026466526887741798703314113218542541352378628469285067679692191519550066139561016918699935567314287605142375916058734877857410364171065773916616197479320511419663056299621190439216971339027765159114233481287446712104198476721547791933767153, 25080218437624823439436690527297664657955707699931279132310266423919290165812311743456112843112388350123406559572587810655289164892498182278407431814283818749616608905671684284701591986659290649399775241708675141365201429623260114967241408343458934421462204880130790588217222754200847443224587069090234023730652537524432084463552759088462749907869299245189615280686596263405146656727697147169669447347466802941000410273822947288725589265556338952820155372402932081927223983526668980824115432585124328, 54043210434183104992267523114488649290882905820260524535830132349891413218650092762686649234496598660979655079481127984969176583449197260368048647826321722355309816641373830656322328069066559747913472291780833214950663509515451942326464078069315488491398317872704189622218259121311551408712061440690958953373194934865932329567400263969941161843726185757425858535118161760887760240668639302010614904767482490381310319677796855345846905996211362054584018990571996933793368941027327180424452423061610662, 78319271784075466333676374189411861815499401202977446354443910910616243399226715430545187303961769649889087968773489068574090852094013416903408242955571731446717286267082852259472741438700271757078693584936809941864786952471428837128578208903945985004129792388215396794612013443373555054258260331601944800537806192926547097341165883972272584143915794377970455756708310432685165069969481436573182008365138231183923346573653952236896517095388930338054119878740528530329341267778270183062494154457212219, 25822013427234857776395939398866322791758749288702816093627523743745020297698135024716331590909319128517051440901248732130258680022908940412187854695033599605806428717558498817253338168906062735325528508577422727746955516230422672945789669407374697032632654349991476894680415564761978640578514023029983049030914212625406951971728269811307470508051899912547520661869840381819903566054705626643398197667617891729932222111935346604570299360897381621359424630192174774701229681872172987486516387230971128, 56683541476209670179826900495763303414401597455163131968854961553674259484755197442754988778464224488355635543111449343477115037131747547722698857859524473437874278094392492884149807552404641317413730716948590731194365808881766636482084009567518197324467297113229336540519168732390550120252237775410079356424440487513342300858119670482447471320063577626376888269111908747799211937149942959370526391400906210162837387530896364189360268033387981359168247861705097226744547190145957321222240760362918586, 96862826382200747202170769778197097802716116002340700585651107292195113619724638904598776429997216277355399044419147697094258440886477233751742534744089704011807489106244533077046210852936543059329338857760967572440029615740178243583006475218341718300544719401429896193357799327417302115916093904263903999529226623226286545851461445122380427400169583723367510391909661158362266546513563559761400820755015445500052192320288193935128953337874263851208816743159463855570969075013547781207533854315970708, 60302377509333489780775361505450365574617380445327839747196536179018281591306734945949099294887283449916995712619051736807850634794118147047225666268900680892124329270189296605187060818775703504831878739601769285737022273068721399192374813782551862856634378078536571271044981331434438797474936990088165117024957562820171974706152560388263281730882194097554136659705448054098145498954774848160794619477685154207113601397854970280224827902336260662201957712332051205527314844212245319328111700304841435, 88448864040262254946087587023047220809054229236169882812092806089176264583922540436851592491495291302618475471424161417213480956457605090630670891797507591390991408328766941210983105297786296351790010361854362985300922734045048167666806336879641406960975043441549060397775612115032104212168511640330911747510106719707652619932816395713191557351141735665649398845430183008610196092827953178978775470929560733668371629549992696125919564982016293032343376928542532998025783664390326385153256229700905149, 81550722853032500797006088489756871841581370131357074748857385931424971144018959520280897876966002568855961726768097167120092672235296440553113222368316414133539689818235330626611049257707930565139253297586862543079711957591879362236095292415078323929742999203114140545104303448503932322104243755770713077615889800454312731365918649979184598365521601440061531803534997389612579691434988374247788880400477398804757274490991104119108311875641436516687930425845744934479752727459602135151512325834304497, 15422239131741148012938899113822038167252462793602342751012138717899413034466827345353464634912927194035025800335054881735237754820936520993587514963477915999679660881643987120060608181396689809756383758948273435802068458217855748780445579662343642422683734111637401035044073839735923710084479159356761962168532568506798471914796519793269974673269590485473109142176498527489861321227718493475810419165072383853159413416448052401195042044440943805453364852244925838015719580856574231691161811471006221, 42017329377076062699466710092272500578112663547592413790298415296597648302733457844128360735153953363512219105735222893143661870951854136078226676022505579681156123019292727058791108057143578893490894899714924677553516008446454686838849696404422209167250670558633612320267939180471936326377722282501732415946319006887169809340155556037885459351168650516028614992217574257209793817602570891359070997736039201922695170584757858889591979837831990652927924410900666045997336806769147471022857280316629027, 50561852713263816117823271880764054392091024302360475551326436502337094021043276904641194626127784840796336861865616951633662728370101173424278241841980087553703566485573774697642319291279882688415432417843709329364675702351503072732538348996250843486523277804696544042459624614254391561806477787079568096881586942133960367206139969779806465517479091944023451428188687016826088130149240514891271344779755136177913806049185946476348411214440272232891665798001792447383396826056208042011629113198812771, 54725890961587476428715143701828306683471233196173055236245874751686508961940056344336317773011464486726389420684010686523063837774974122982806245284259631637913129422519714044072414910877753112591035013041862765734905040669544706771663787573090386386016154738480942038610356932880011038532885544313936677673562958759243800992429637980886514731675456156158565035906434716407310557639073527219762265933254919728149784461886553771830436247051110900328954551465265085036514583443715114541077526425890444, 31732320136101280076416488481518936643780020204390805926736557788679430268369061269267204122007188151096288828517381322145041770504733545649734212992284392209188299201770055461734007818260110383902222485276118448250370143306583657162649436492570442012705783257854342483615469807411853501308749061590188171483849741612871216532196160239883031054405865878612340856033703285980415472306486371027724517540573300265781861918496508843773416304454562446574004824412757507217981504683879395099253661697860828] : ZMod N)
def v3_im_val : ZMod N := (reconstruct [30656599138482775940280383927149213089793140680757471037639922298973306476944525794469542255995960129700491477652143855631988430647806065937534620723185151720861, 28099438217267182209480329978882153052770014678004865790389244003168273667834852249989742835075397119933164248870163247099036843030820787361428198469667415361819775349418154452498940200201281588992746684972202332414095433774534447384413076002446620805641403494733204907858941171280804189489901143536585918928147326410569588822968481681969486273466406792815063335156023201084924477735708304641887365564132119876094912421901344948729538551462498468812856295855644218427405463532327660863562823582780887, 35774785939529294517676455183061431900990113946093221797483026506336703631979511843791929180911215305091814577685540675754348250776093413427121536453414727288142323081931814329785250096715548111761856359657132026660714939767137977526650666733225243464935787536178038479318393981840325433179258876984283990644159012565279095547434969273149485040336445157544532003133695884949152162811179424633304335354276522115191850203891319397246730423738005438042808482312700023261921463818610176366230541318280229, 35639214636868743127763439909743291780558787834519204266583594599261779502137603001650746425716205340865101605751872121423997381242370559208244520103613537217504673883677372130349528670343784539744930437672161599433279039092969671563021757663380032003207015700597182312691629197599477308059029545155084717149369185663397929956488545197232786682234291637451983819548852812140765708366687305908533879149224339523307090546143914995927578200366542909824995027686404966080352639140735240131268653757850481, 87523445733049173951225742578210056316204402817821725989245398726983390064892097926537006843717778986688795752770046984128538131426697920830782292528393348698782344681988237339821614969106915543727958880992036110225796570752466039089136471021547432781641973130149156449462913564325400741074247479540501302227070969234921426649673241452366356414319383134660602340161073717709632316945696859693307920031716731206410888435745077121240954120981915545888565308399908254143270848616000559336712423334999441, 24672421433544476216317779729361385001164685046562108522272725429039827263931645649153708429902031878232958818050087211998643704838393773756386783295455258943501258041682363218057735420045694551742236314454086198388147120452400281700725145343704587366019419507424672809812562478611740266629911695932826308075088974925920673768378145281973498504155365759468284181935265535287548082155777986146314614159503848965802491107952331346756672363670895610769664162183801270890881056835132299545276135187173211, 93818480437443967147972354281356847389803432208676853393661394868099687320508296747703444994998351397160670376494756731915223580884131732577266745394927357542899955288774113241731200461366701672095084498877212349792624654014319961542384000742562874288656235081273833340159475277372400051000841775764213002554605335508109296315912840421549344175826248938684039436487033436162280092526201076701661494147008896261879645629620469155915721187410972567037659144902876766551278374355410660189074106264524617, 83545962309647685224811924219459175648121069629270910465841629449895617328886017330486782923859412995466299499808325186348255372598832910825435070076399450817624379525060314201821017364059815932156766460309366991098139827756266420287942715662425504231603400447664199301624305191244389639976304939723733670840202112806679038452251552382234582869566258588849177739094420100353326184928930620887991555079907197462416126914845226944084160418002479801406697240457017955802603065658752065492236039760143514, 48178880875577877057043458611217287663192353168749907807504952779339695954626341120906752849351904042815154904607469527557415282928030382936652653818685148965236542703388776047885354244799443653903483475430659860554386884193385743399236305265929939690506390829917327160152849223027158757004425672496675032555560974800802948199973758099546174934354944123822791590706893369989262563029470803969123934187855492635954291462562061568730680317943145643363160080430791433507404254957204346725678702635432211, 57527417119637608044295540543048540388000280503155749000532377506598571313592095410594191336937943928196629545229620527646021675819025332575234525476023641136377456441106245858461225488692069666032462832548597601188802285872793874260165973899138158571728180801558657682877740872413722773229454815863299342349588580849830145331162799480373042491822200691965281002974799857546375574609169421511935490582019603702388824954150072222497042442652409094414652502800362183329288532690713994861920869961042485, 61792627305671622324202489127078806686530650332497267635749410423223727801197991723217979225316027535966914849979427859970908040190407926422567391179712449559654491001667687332509728639288235496991297607201734190672047345577122484560954019235854980383221538083880370562138253512297923743782191930854696136030859407322009737609418002741439470488920944958506282176129565143789432967750543309362915477286787800420599120307115822197864454102427167170601811549245496987369533795867103531121096353527474562, 29905128281295210689302614822478512045682026627920190758495215039692389835701531853897456411759393218857483087077299640242352776061958041689677547485692765284285732951641590523488152640267315408682822516746278433544347176132770074025744771962703686510064691140921704799662016836082618755343027781714227870982317228810698603432263406565616331412633014709899518561643950719501260709925646712429985096535839310438685675027134516406932378658033040648440202110485574823986816514653903910221120208535801008, 96361661493535861581295372817877968502785326862348467487508576401631366508319772819643002733911530472856594645442636370045504338546738133310291930556379664644110141423701930572768495901486256182789118942896028272872191960667608061369032287276972408197474498258405949326047004029803621632310988364489829019256826354209106411532572275110068590947812668168229539083246031702507031392702250665020059430149806388794540006404113174689711962545743201899624635825108819823652503148261817250421592649577550851, 7195795141791598241395780385842806212054716831920253866525184273838427775980376986336329795086476081849844110869623377979650347099611559900577824573806207757509650945052477612015853309574467350954146194155778737000388629028288957045019008079263536306097149544597590230820242700049383604934951151382056702087274985808324051400622211603668366955875232081857111373516956394841088241547168693339051622420265145196964772037074442527910911186696343148138648853402580214826564198322456218342299725494584583, 71400097677004432371043816423918404955776132908794726869325794169667133516908851344719928322750094222773108754346761513740094628829120444478068670903110797811603783283266940556461510521008140341435276708543136940821527076039051920937802984213961997850334443565534210093605467087312271765782860049751087379199988022137772488429327332374179370726447428258270158127592046105896357141316160813648593420973973212314090478690620157179174603418477424756376982294363734483927484611285405401868522852473129540, 8273172116887232956293600327838208653952896268688547444868538051460023477819799584876396376492942501133781880944989379132333417018469820324476262779030486130500223841756595487884754666644762890438876530437224879206464517147987971172636164121902685600335467906180360170093881994656892280226662920022208653823585266559793463786254248195413473790047813952733673165633706408773228575686566303416757898069481973533936880427668964546844665295662643611560892854251802553548149010743328369853627737863256859, 21847692276414718302799799985400672476408937380318069638859157755172601918103448451317669300758224973982342096100161874934302708038168358655418682022084733858875246982796924775723180480548086809898791785348476081228522940898646997155766198120074255586957194714597354934961536025640310577343968006889289213627647104950872948048527208749106732318111447759161021954683301579621335307137655274769790815534634958757904264855673766726066476767429647098772895653737092517524658070786734358016192315124546815, 1479310094836118186804474645232304519742542898910982810883859548783650323658707432306514441043758842936706546593095574758190066060676175782953891828469244767004925083402023424062309305679722992187202552863705246549724740802796169772240426944008173095446724294705521585844555903767721519656961114008558521099575153257272929225292357282082877094694023709465363687794172800666630949468067756808670175115364911161069956029545751629404307084942267474644122545953871941725044049235827572052062463689024070, 62507813716721625274160073692219446814812573638463248740514087992039658689882282886768134209638096959214986523925999570999496111180655480146800149658719530727782589430043010670658192492982772270870367949954979917008951090451639891261347848209301426983499081414623051583281315578954463700872184956084491635766570118446264538567496381214300186959072782457131538590824474438776076995625799126381346197580039122299138040729220011693008947061913146462548358932965600533073941019373019283969817679770300815, 11540750583785005585845626467495380290022613921635612346686068100014305283643126431639805355811156020624605514618050299133292868183549036278593769828107677076723793186029136278310198396599078031751306497263234093151632269083734965326764718064482392854426780802250063657387614829030781601334165317643798381637277485861991917964004771618212949514617139617511714183285784415953294685612983889742416898099573349012383484558203506838229069144419774577192266737667201363918249413944240330086863677174037795, 79731814795065122073461052545002261649801242324860245951835159749707789083556334583068978258871819157960832948910625273355385443626883702661015404960366802233621546971992911511136511858595952082251821501073689428768596001002994520780360583478182508910538201000804335332425491420628228943614179308862811535057727062905965074676205110720670642926520501973649419557532555542335005312370840060386856171626730766657820028476394599290181322134291116946728493117780010586484028662283923892901446080256440947, 36350213544708115679315968260965003015454630293423547575701498538249479631157953623747276590692667098154066026382877770525262471068966981413923547184111430701268117109032965660587654925159831574123065158686483578213470652181509380235164759913757674857822180494601120347375184558226883964488754828820093856585961284713512327154659979737656913852642132560015526294449933650795833201784473090335486508942142838421897176588092525959644782763311289142813182035455793773483160473692644679676053216692272586, 24144457650651851233343967590700819196542104732261158422453571298410017497931907865431459304082475258422343893800998206621474347532069201401326329798608618218985795484013564681436950359040614731060639710980744365574763757525429012163917517158709860002686782934089553479533112828643612061809649561559015496084143597301248027676466411134161698633987268499288273112079181977936718750080376606722825362851142730312446726333014505947335704626343083522309450935972785559309950466660129424035629699991966869, 6626682695141707668858351354679865914960021265527465534085314351828530171120624482433730196133688610710913587098674269276490226716654634453749702139675512889582125165891844675084874849433983683760027916897798201481569520755419985514257637204178871354042318361878403137592999187126320149755325581995377496441234391054334229731921149283013267596027745393299264260363329302602216199754285185437936258914938378267030687526693928734370024025207828104029570443524780724229831626912082269323251700836526902, 33618473856604626276256854750826839920095703259879010010384930332989274742574249373286308252847140404901355593411017626854319487281812931387915026230025595238652771228447089158817542038640730049186673228235825946365888216376085501687604120220567668708947189450106775537792941725286816500700403787086526176148652924790647757428002385733828104754855403153955426402716832128411098675013006535737249423137997857776195385088295456279356720263292218182755550124879155911503615585603093735688707926115162510, 42277033128769270941805470094127270764359607368117653383884457001830912440817391794923424592372427505244113408254117558780176684182424818784288693604776040753143861266522169896952636847730011516460321072740506675497479040889146662751182310807118925491039305797321157187940492055472914943268833581961362918328798561644661753059534134508724693127511898689291036649098514656043835060903823420031995885477595476911028229416403259954964125883725691620725536009067212875641650771407823018945550811227717270, 27073522506700849755097049397379646067469627662520968975758498439092646376179718408231639677429486745534083201198565620970007871843566765613776795025923492682826224572326845948619620378373999149349281489234705108980505152217660869914411217631336766199773088383243262669794749917714853321082787418934923483928998762158894157570750311170079093577463006087674624987242722802119627922153142614879088891571787206230324764986670793463076174370793794210009340465479678876005785051718403609764039582742649935, 61595580111699515960477962835653248403609164823527014611159884584664272892804465450251935570969628470563145240779493726771300565370263202623709126035549401556269324653533051083738919176189004746081366239141775079656520073593544622178211079197111625340320049561988170336692715111591544860651614754850090361684479731130387600015328489210100912857601431399582944906870768090647692320670903126847643219971444253338473737805185186744950830273916685404303375397818719602028036302164662166483809754451938666, 99611581462439039808594865296510209306922341752395856340554979487221862240685010592909506965482149056772340844400652442547024898602131221851426736421779855944227749049988270264565381849278057070535386040532504285713498014551103132863020530546909323054507737805645910536761425228875190712053636777876252365140821759000602398202628941996984662660986101494998601613380582017673002630952193834972960262440622131682309219619014417902679671790173797479774208193379589994674820514498143959958949740551569406, 51456560729827576385385519595345820375271853413781903786578330156901550501324491337130541328448396170326905219063586719936651250246063582257951617024478872226573388511461945469019028457265793333312620357632572212774093368478939391926010941964984510791914601272559235032503824805098696775519889489527061201606236142523269870752851353941678601347415309815603162156166157276792587001817227572076921460587907359393956338726742888703099916162517068023674333859442917402867894248872890876569618434185869215, 22276691858685185637192261922494356633889756727939929912527948841833585703532685513416806610279706500007852148069723547302159353329237606286553593711101646955204650443461825068878092447280038648246306198073544778521258752486605635176053495591302894122946650892290159057858785399942896632339294480394811078157705584130508449976383254021563803963274843158980349051520533091776255810422503344785133866421131928064284562233918709251216594819613121092718716534508992434775870440023596356086432810554859730, 78847207461978912927937447070454146835823346467503121548488041737168010949207763890079659094451322247071339184200611854534483114631673392416053855691022269969714009476579876370465818144637640054237461560501392366086543039217154436501067049091977353248480775454645327660565378262413025479253561532830927627725495816647695690642518780869190700171219684164283242713044191485800914165400365831348509212041237156199206743637497588240566394383793291455834735386647235341785071795296623507502453665540491557, 42293365395937011027231432724044550902135087538363683312008943450550716106707894166397081057771434483188607331566861937672944853982734633710595025308606559669684598888640244084014513655265772944181666007068688308086367079095223856252474007996393869515134863546606800346090405156332000991094951358370738753904646297690105809993229610601965691750359273181666798986494298797454458590705679030572273843506539843869536927411191423923287518132230925355946176003315620969197930065888115242364120515215477994, 90460672153661330599311110348732173112203551238621554807011055942519969666386693695636602927148348118930397503306699518195040297562339572534189202376718558721801897972094039930276465353720216481306109323288258789302249907184551776991473000443446365175921595672322698301095153738879976467077541392110614703322674467330615310379104559562351320456899316095215141045570431136463246877215178288067834254002079164748226367597178067690386578929078911149917212502987358264174951486661973701993689372158341564, 2042929170812326828368543165323960793222845259286523908696068717388882054418137731279348349209954561679473002230497757500356884323967505442893871324940079717426612757382232100736306450033188962811874792047764380989718524241069518982615793805572507205080490660929205006842875896358319919356761005103633326863703138402388506610538097911323564842673164727138717060714275300402888248792875489361392577053787702454046119421442398710745484819419578800220169969464145769589896332441820101910459254610316642, 92750743384935739799683739583310747383687508204048336839516082461850723810423337478987146095922594393847456288560377035444013585064591381920686669330977489329688572479088751415888208755508771350747835037107972563852392196469856442484470388466089415212380212244131324258507212130871523131668819078639900418312905496242169083184227062185294706078709842567651599567386927433439454122465218380495040472386749378289862012585628389519872623703161777547969232658871636318103758227391116298405613611942725483, 78832492134111522723650908126829276534524379869822611154864391655580448578068564042060867648447354198459808865728161712614242167525806458535916964776356326039677178000129075232432529848892073283624590883120086898056436243368959925946967755667699811243052472599875445242484048229667952590497824441712837428736209504040573750202588002149356278035727282501983408092711984491318244535180395025417882185143001880165200988282552737025029052628164536824172895929907562607112419150148896154134944808138630994, 31849197381615906594652465824783119017231262798755182148122031274679863078774341382973068158997668011330297026867316618098802672206716016223150216465422315304905837173321963237524235171097554296360802451046245890897532776268865351713501114124639052253999271723705266380528573510617737320841132797416385684074087295962626856532181038446934607468491323136636264709841391418506305390146735116878082956634356300714117609040799792288503738348359753525980067933832519342114471304405680553947770410809730491] : ZMod N)
def v3_const : LucasRing N 5 := ⟨v3_re_val, v3_im_val⟩

def v100943_re_val : ZMod N := (reconstruct [83609764703010399045072315072052636047042541313830934396329284888196257866655695505541062267242869508292287797633442623237920790130386645644416744748845418953047, 37812599070998937309497229215040223523491145614797881025106956188925648208986751870577614122401120746013558818550819750449697429453224710022570003188598451870562977990413140541839098946798903218366909018317986917677236461282166974910973093844509544475696849357024556973272439956206465983429838303046554887028563582207187831331251871394412647873320192661251589149976155073666451123391478680600991070544356643638242624445471411903817225967448996482470692021880738000673781903123681851653376187933327978, 21800502744418268423202007932479991372593624832875286121795608534330537024776198292683085730079505289483328547934315781563717875725930391798432342361711874696264159387888980541413532172273970185735229483314191341174154958105954617002560662454320384400911599729106205903509017740354070175505309854611970058212572891475911926222424045692275045923489607681298650061092628480185684771592776306865104948864138152459196060588691085261101573631292413888435818949741123449792445086258437487704338431521262306, 62745858905815156961833602503631816241342471886364410748702494847841555038856639795200024991721470734174445871939324335191381779358968244274087638319817696161156802642543659860556339746041704708069458383556123110348962028233426013443324601104433591143788385282954727858623260344287486416371582328202892729818571712825010107617664834455372409777020929294596763235412389456590147879367092412922066710089571788383842089196106619735815656695727853306209334383493079999704545864757794567435674417560788924, 16608389749268966980299600735771677618136731870530177216323396610729294743462139743312236986884704440529377709322186755840302425590313305403058247288756771878998230958397685824106165289771004644411766318548750556110341752691000851372154381259694257646486048826379320852034995824594850374823202598909518376550172333222568464109375402508192131252890670913717190998340638374360215289568224649808640859982304110713310294141557188317624391036702026587317284396764077548839297349293883958554068945406224749, 61976046449488720240299005578186578092039023475886213463376295056892389028747446825110556533656841762475064297285232810281723676890640365838885314291843164752391924432215629990725491974385595748725916177264901462242372748123729510365072333916499461194695747168407819424695083761710361978270418519294973593708324897730329716216251671337907377738612314967688955237953038254575237972876998632809837085760240840443602584821478684568356767536974926471618603712333552026425168940234970853142294509745135226, 18297304087498957380158358949488717321992078317798688097704283319378603738135143588899453108866182472073006183038912985192463785544163190998801426433381835008504930545378964590488501356821588761006089167726775372402984946651041997357345804601038889847758136404915469985129568722090133548440664806489564165449914738773640811215494535635233501690798853995200547674940290482858044151455192680053957539680555370414938979196009852009655789421622526341478914004483206044410527311064940388606821597353028888, 15654972402471447885733065949442491959768416878842115327298791489654575448354192452884764801742090450115395491906578165763766248996713232247626236043009054024213532919102585428531525723435910994537514353309803060844471437456116051280269138350115527688448685221901205546588921064426317985607462312648128554316479881716255453484140005785742628295005993217642338781721203085238266175834737320848562374609061312660553476763556701261429606798121464817030575419662121977394804512676985469075981151473851423, 47354569779999826338549237672440177567831912449787765862370840323943014025622572982661332043151950454342312511914044945877590992436882492027281978875576093278091162528016898741318484154646547401156324581220636623460585586236496912921476041743530193171597407435517594768732148641384926768308392275516185940680446834709946057357830103459660026974520215799133672550512338801707223914028680548270030529918300276809011772097810504469209588601556538796538013934926245738326955382311068207263743536220411834, 23806722002994910412952940310768936020068380193256336802466769344210223363273036272277671559850346390935058581883046610318044139984721142941530633086891857539683722877440776127546662084122893550657595819258306438092581671944367339605802766623774503575986928590728028454561074998259750262351422876663426728223358199140724034888967978708852119404198131163727866421616693355692373716192169431231153435846004139813757845747818684262015644436662949815450348146457536558381579829217714650370237714870505866, 38851374528205395817789157388485976062559320030861282448305402418593976782984986441494575315276578488432996507906888434429912431404384251612529320946907491806727183315089520984349490687897447951473523124913272752836807447337757600879354170449183823386671210054531543902314353244418386863963775625807702380916756595742247548676811568770828397394104203574940659814629213944216559909680525714448814044815162149927542195958320351234185339635515684009171890702297379754634353059071279756593370359783640781, 64652234018020878351399135812611673107545275901481533759321120317386491626884887335687832267930889301862925610004596043274598896790577132804792860541147800322880834046050127850963491448938805603348042110421512355390172270683179955455949707227460739664669385322028385053509092636701286497495835563762366738607811991834128047540633240598183373069999945119658018057213273828427765942629416511563787659922387898232879436756781531646163532400596655885418890345492704993892734526051575918592090023198601648, 14119065346631480274309866960137369331570366953051541112196353859758367141580591627274786001110416888065319704483952667311716683748022741949080727718065962355721098701275153201110408165435956987574418844265678423866459447683256740310202994593196564909614702988650281848759165879962169317160838523651100321258130357315544609671081989543341213162495202407802066854351295315456697861051201968145124804564018913764483932679208296651886947424678005568756979590113870080013234384531195698486401741949838009, 64067822890185664893793875242055913833521011594125054154013628186231587180580176604431944081549098744673515840004711888792395913869317135275351386296156050429418430024181762101950882539952919735696176219735511669866388017804605000675731981158835475053746949570934287001812931101324569929315438599269935706952531334102798841144527550432449582019547973024029168473896377861534014081881962951493801523829778431389651578337385078724617097142421101941265748571977735675798002199251219272961336884276756617, 11069433486099224392200154313314134059887633409328656713943590636368858303486850857508368759739893966364663252940311553877983980406572739214624410375335735552573283818044093840799312724461128935301563897211899289369287116428819902389986974229198836454504186573537605043952076037244715840575992039611105991979974594563429850059620890635022068073554312832614834111219594556264585469139087542055647063217753453285349362886705657800333339382352815567744419320172896565659378808662283764316648479834889294, 51747208576027628664594165429685411263352326461518468004679164018108645669938742211011225868476302617855759290593634865917208446509600258829210913154357345847582218886983003497740543126904726506399948657776675365923703705500829898077621780267855000001840532963828267252804050784483675614289989950971072954559254684764589894622998903721944923152708802608779034560455362719816936866620858789006115930745562129519123742643383700769202643882085058969131646798384792591227257161635550239721441124213412927, 4363077364356533990155544689238554498144556962166338953477829709891223777663142370687005603294011410712088503373871410289880424069451595440973116312117723039370548303772519312688187111851367677878334854868758535293797636213717292220868224252499083386714564261935476027256819243075261980996078351126635912884365648447346077592663065516672525055347540106282528229730643436185308953066215600914671413494424700158596291796461118408826892302993762464623795228178174240702214096733468470673829951309428594, 63381829754357622964650830079071394282438975944210658424880387498721169384212133918669457860156648593997073762232175254547192063848352696695314260598277249377955967809698123623074736426137332724026599164392224402616882087318395849833167596830012978525870185702499404663637666806644244408159152883728626099165573734191041552593033228180686273673419223583155693055365680966550717976881577255116913806077623348554650579102456367058505839938302902993095421621683308734103714275204541014534056708465553631, 59954393697609088370066345891834638477715737574284163645395548234543738849430076855467471752817025977190454324382596509880253305857561178602203978988230755979512169861920181525265503141612721126284378233689055175559174878910943680381636505194287750440775543776332011036496773152306245839975800366582462530937319015615656064654949504191741133447391487980435422305997508391495271780142844777456157111648711457928804605249614236694097110421235409707257523010415078030787181815777345291574984511212788447, 1136089589422010837312894115471434798403526327643996758105327295211438512342427785577624034855338766166040963575945082325035970559828160989701231935868934119566482456767740875584882804015557604360987323600813842620375686506039957211430803013637501571680048405372053509773651378135496160076760961944857958542432962120055022435980559572713753641583388357484272707302563463729812714279125020307351326819683295437683273343252578148620253569250672451380360062848690971722226563244993375987256859829109216, 26749868218865118483293917007424351084139253520628359747522844444785161993718089905797006162569293318265840091765693361499483318267491426012580932988364253499680358585615764612375105792958902765811607524521967161531548256880078348184659573121148658542032206929253217591805382959879648967487367993265757222607119500488855114638357298066745183801745525497491830214844091124926520103269010829822252328886767705379511912601223126764063393007508062210651883524258756679667682470340918756666666267567717493, 74810325609716398911758646980163682423177152684504675624584336791926515114039181012263483692177424143205115267894703731427424063339541406578781444379436532626084155137326417648900733985965543337460326174438479955813241243094732079080405549194526722687520016310441016349720588715740964335762786009758110506626491800151214090208820584199708904919248568783244881310481802005030216139842640761279474086524297954540087480804841845750154583350158326541959072262434471150586448490984775667819145860835381132, 47844139435656097333400123470469533534036898658637668473734781576436945090491784062414526064438654338894672432567119813835431091362973595199672817872356924214691905570552180393873903890026137301310789108777668285891332161675069895776556700299050538333054248883990147661382478616849999712458833709546229099898233190545992292016841459178866822626492279087903655106398314222445717554986628341258971543905461931500684063476175591647725860291582895010161173157280750350635445585991970072484329392266224978, 47445766558216341923820648407594074950315771890140613202206401883533086782747921477345059771421177261956580607785763037361370752439087768532401450519326382463403698925259892168518345890746430232282714857728225839182089951470558781787810619129924119317314122708026466526887741798703314113218542541352378628469285067679692191519550066139561016918699935567314287605142375916058734877857410364171065773916616197479320511419663056299621190439216971339027765159114233481287446712104198476721547791933767153, 25080218437624823439436690527297664657955707699931279132310266423919290165812311743456112843112388350123406559572587810655289164892498182278407431814283818749616608905671684284701591986659290649399775241708675141365201429623260114967241408343458934421462204880130790588217222754200847443224587069090234023730652537524432084463552759088462749907869299245189615280686596263405146656727697147169669447347466802941000410273822947288725589265556338952820155372402932081927223983526668980824115432585124328, 54043210434183104992267523114488649290882905820260524535830132349891413218650092762686649234496598660979655079481127984969176583449197260368048647826321722355309816641373830656322328069066559747913472291780833214950663509515451942326464078069315488491398317872704189622218259121311551408712061440690958953373194934865932329567400263969941161843726185757425858535118161760887760240668639302010614904767482490381310319677796855345846905996211362054584018990571996933793368941027327180424452423061610662, 78319271784075466333676374189411861815499401202977446354443910910616243399226715430545187303961769649889087968773489068574090852094013416903408242955571731446717286267082852259472741438700271757078693584936809941864786952471428837128578208903945985004129792388215396794612013443373555054258260331601944800537806192926547097341165883972272584143915794377970455756708310432685165069969481436573182008365138231183923346573653952236896517095388930338054119878740528530329341267778270183062494154457212219, 25822013427234857776395939398866322791758749288702816093627523743745020297698135024716331590909319128517051440901248732130258680022908940412187854695033599605806428717558498817253338168906062735325528508577422727746955516230422672945789669407374697032632654349991476894680415564761978640578514023029983049030914212625406951971728269811307470508051899912547520661869840381819903566054705626643398197667617891729932222111935346604570299360897381621359424630192174774701229681872172987486516387230971128, 56683541476209670179826900495763303414401597455163131968854961553674259484755197442754988778464224488355635543111449343477115037131747547722698857859524473437874278094392492884149807552404641317413730716948590731194365808881766636482084009567518197324467297113229336540519168732390550120252237775410079356424440487513342300858119670482447471320063577626376888269111908747799211937149942959370526391400906210162837387530896364189360268033387981359168247861705097226744547190145957321222240760362918586, 96862826382200747202170769778197097802716116002340700585651107292195113619724638904598776429997216277355399044419147697094258440886477233751742534744089704011807489106244533077046210852936543059329338857760967572440029615740178243583006475218341718300544719401429896193357799327417302115916093904263903999529226623226286545851461445122380427400169583723367510391909661158362266546513563559761400820755015445500052192320288193935128953337874263851208816743159463855570969075013547781207533854315970708, 60302377509333489780775361505450365574617380445327839747196536179018281591306734945949099294887283449916995712619051736807850634794118147047225666268900680892124329270189296605187060818775703504831878739601769285737022273068721399192374813782551862856634378078536571271044981331434438797474936990088165117024957562820171974706152560388263281730882194097554136659705448054098145498954774848160794619477685154207113601397854970280224827902336260662201957712332051205527314844212245319328111700304841435, 88448864040262254946087587023047220809054229236169882812092806089176264583922540436851592491495291302618475471424161417213480956457605090630670891797507591390991408328766941210983105297786296351790010361854362985300922734045048167666806336879641406960975043441549060397775612115032104212168511640330911747510106719707652619932816395713191557351141735665649398845430183008610196092827953178978775470929560733668371629549992696125919564982016293032343376928542532998025783664390326385153256229700905149, 81550722853032500797006088489756871841581370131357074748857385931424971144018959520280897876966002568855961726768097167120092672235296440553113222368316414133539689818235330626611049257707930565139253297586862543079711957591879362236095292415078323929742999203114140545104303448503932322104243755770713077615889800454312731365918649979184598365521601440061531803534997389612579691434988374247788880400477398804757274490991104119108311875641436516687930425845744934479752727459602135151512325834304497, 15422239131741148012938899113822038167252462793602342751012138717899413034466827345353464634912927194035025800335054881735237754820936520993587514963477915999679660881643987120060608181396689809756383758948273435802068458217855748780445579662343642422683734111637401035044073839735923710084479159356761962168532568506798471914796519793269974673269590485473109142176498527489861321227718493475810419165072383853159413416448052401195042044440943805453364852244925838015719580856574231691161811471006221, 42017329377076062699466710092272500578112663547592413790298415296597648302733457844128360735153953363512219105735222893143661870951854136078226676022505579681156123019292727058791108057143578893490894899714924677553516008446454686838849696404422209167250670558633612320267939180471936326377722282501732415946319006887169809340155556037885459351168650516028614992217574257209793817602570891359070997736039201922695170584757858889591979837831990652927924410900666045997336806769147471022857280316629027, 50561852713263816117823271880764054392091024302360475551326436502337094021043276904641194626127784840796336861865616951633662728370101173424278241841980087553703566485573774697642319291279882688415432417843709329364675702351503072732538348996250843486523277804696544042459624614254391561806477787079568096881586942133960367206139969779806465517479091944023451428188687016826088130149240514891271344779755136177913806049185946476348411214440272232891665798001792447383396826056208042011629113198812771, 54725890961587476428715143701828306683471233196173055236245874751686508961940056344336317773011464486726389420684010686523063837774974122982806245284259631637913129422519714044072414910877753112591035013041862765734905040669544706771663787573090386386016154738480942038610356932880011038532885544313936677673562958759243800992429637980886514731675456156158565035906434716407310557639073527219762265933254919728149784461886553771830436247051110900328954551465265085036514583443715114541077526425890444, 31732320136101280076416488481518936643780020204390805926736557788679430268369061269267204122007188151096288828517381322145041770504733545649734212992284392209188299201770055461734007818260110383902222485276118448250370143306583657162649436492570442012705783257854342483615469807411853501308749061590188171483849741612871216532196160239883031054405865878612340856033703285980415472306486371027724517540573300265781861918496508843773416304454562446574004824412757507217981504683879395099253661697860828] : ZMod N)
def v100943_im_val : ZMod N := (reconstruct [15074540348313485626700683390917984371057830119676405018776413377181892731829966823057229874460972648374176837720640864927916309123400464058195543905963546414426, 87525279002360560432221543273503925804128523603677206127263261008064062373322467300193170245951547361625946212866473346558775862639636698361770879934215621925436113888282104702263623956225103278787410428595288131221968056771824411728613426325511720664969053163398111401821529463768416084011884196690192983883704651145015735112337760938791896689890345043892494137588102342568502546249418867778822490387842718132259152009255805009208632271797998787260226815417984114183955089581232639293387748257469257, 72425135061766895733357369190749718104533970331852102420640335581806670824524156698885744194467493147169489129686058376988124403949168549964445134159716170083190899211671726100130742478732755736786588877587544962220740928321431140067785542780385940391176133168745534787294124146896361124777336501950508058556563884441042775740788859869018071503249735588619037277608564654124762101061340700930903018259183334634678657437905286522996570531947844701032432213335723202766906439903178487538301306841194597, 24968158640353432896444600037162111019187353439679994311399973793181211907233038452563504628223311441588546559509145533796018895288210304880583206200556897525508131121303290118783204938322416786687902349586663941483798778466421883273547018805753871535947217896835670681578209235059709070708984457509023713759764210734023985202693593481688307348824476830418633618744504469924673634608501389137579488786694026087050788694582518607957522671362622064502784650229913486877896094965431469029596637847852799, 63687999016218635394069398704866407698656451265110329683474569004249146793691928947169996779726409095230446213387602304500004329979365497845412008162749048099289073011631204363265703600718806411803573092087057717134939225927714327176959332087225461423291758311570443239977065200291296942154759487282937322332501614619741012989638599255766875744971680938662075554725254968779955964236456710192370554269491091512620074610342889739945781238357374486188113047794728584930958017506962304380976057622531826, 71407306638053044353086908220816585778076809022013860697783958612233347029418441386201687356386449718311654780295969074153305604566618787840203090732613298513255978576440132896651722814272544982553405625369352000575131602555176243210764735045863030467217082044362099635035201436073452986620047423402573517378036663597132403922644168241608262272776540067657870420266213155105274351911816167131639696826070489653745749572128201178613606799348961135286688611281807496303611711627409058559931107715546986, 33080584187429016373533415063960103891097281643385043981863372276370530092512466566263959472427964266164291290870628571160290113261374932344482789564142822570487980254495234965723573481548002552029640695858939676564740375363694326833557277888456668983871719550599448059335698861719665040720999706412408136411995204335456040313660600311913364384280817826696290689782309864250654787187314982786843637349595578397483488911314865439006616784950812329261627944021862203572660568105729005503828995511339445, 6303873423557238952524743131643265691624577121797224613737252330992027565742590919064242394424996043830603323405592658172884489378501941957978479158395184767473035536121489831481536706894212984715698418582540187367947097815064060381060375731977201919823877666230397572901646990532811785604106243778943761525188501659053192394268223888048276644256356932550162806014578821808234911639266829600716534634747902827119524301970108161794271302417739683776900925391558569098370723893976493901146218442701851, 21052760061099683684983316947023357473325283275972794649181862379696002965439364277491181875942619673471371164406376199523449353330691657139961430467651085837795586737790440323314669485820409026922332080863018759698572958422418048665279033822335341669992480348502114576905062007154503100291253833497765837719354749360319789105752596069392045008615324514571449310221396667476041121901097201875886054915070246032034524953908103364014519242067292944288414241081852122511755891060119087982426700394020211, 10815318506255330657250171122408873007768208452872152688980471295604854006635294465611644540297899041409477013264484886822063713489616176183489967200787730742151569363035084543760786491987304468045476760973387712399553690388749425281777980258529173288290501777428505999081720142790326827501144942532807252110966027068026217922676175665487226506198884037488254975607421960680398640818757903363629744977983923134663712219204174686660806107337976246991297132552618665324053495259205990876615684292474311, 23352873127646895283077139801052386424111785097234388749437205425496036216913059497622591896588878447338034273023131720685065366806574424496692582758355643502442033911823411999333122394187223168295461146271978083980522590503652425172212000337248283746419242022576350207928582886967614648049245749895019281387113981617171346652450785875343769232600394833947121448616524531119254316099016770099488536214306415738834849540094876970681727625182483916062347614534925318770384077261753116724813620281709336, 5418859567868915305734991444399062644575461220028002516485186321043413911502483650743576327861646811407290292234884943359724526573799031342581188796009240199356997417690013707288956421142361266563911084666224399622883329055353872670752519346482166963983014624844799281648337770222381994487231953951720480480477866712781654693036648787397125821636797500875895876085737449780555830668363268490392912599923665886411539626490777690940823882152153871010222190048024938543810039755798354747708984653357066, 49634115949314182875716115593540559088204971690180584778466368116134106933029039858302487555615957036575631918857353059152607355319016328146367318782668804770958478420014275770308615236372836506173104789048591016790351046470529219526226534755377361325098316749388539434626647654035017758870618696575309691769511871121549760224028642004377435752480655427108494644374399252037332018242770850427283071147301905390185749538156651473382107417276436481061107149829826785294534928953343345562059260894535977, 75072961660396768358439394940760126814181605368047836327329241996953584064868081072940780817479723825066045776650249747260973243311241781296404893016347264772821600431097176230701725196838232587536522666198179181042589275608680237233157308870966996633020729454133967955364523004708168018570870624462428390259250025028266098739738277392740244922221195871557993199307332666271315066067565188868483508945199240066194738436978058549549439635086596231391731999949015429506476332147974567973903531866629511, 45754998229134580457259058983594225737527475092112427496472403861665413442829049385410368243504552882331620901820400467882050292093181790186928251837021577462819562853525435446158096479591861683265290119835622764162646226686833008576839532930238848999375577749964962798865592443257459758764531182094732738754104955308557922284193076221563061675206807806485014034130299698388243459765806102465836987042759345659316094029573523935298159581336763389215210614963999277562674667062072366932537576276867882, 66758098201053568022533630301770774925513257859843493025805475883596544838605829969879284174174985260669872804192608665403317713984890383308444454345532643987566319690624479471489226950609137153086715354253926214692970708060992257851722831230106061833634626702411342815229576596866325464700604806051595052493295171180617002741872510571761944136115263843666654954549063087331528378328372547667381187985948971033552657504344363915592486342303991196187861770873776389594509331900645301911297244653911180, 21560092506295542691926428797058669404345172725971622265320953920164970103907338958084847917562411410294935360570482322918097948815384915839365225991143860754432575094400388446738248604784590101797506569771534681966790239036980932912804403639175244967655910430887740706345471573479934691565885968162855453386694912797625755255739821211085800360355203759817382401918260998547315042881601896033775851395289338863952503094634633072877734064485879694960291705508373036131192925967957136775776101241811902, 5426511741168345698883411827154023351362809897520424723657159548916015980434335843044294207728806534191071584676427828998690536046727600842696069328607448111529205813236678153687110407502136904536437192089888526903810387074701661479716371753587945559212334194369247854269763514253582263242521870407419683733672647118713444457764928730477043315639684880366474793923669015709704660511986156553454272969316356497679267415812450421557618976300835371084178742128403965065506838771082952240735656929255984, 6248838459194694460297079725853461270218328236571271069753127034600281810622930630423780050426536745465969943032642823148910473402589850797321588405823282012913610962236345994170985788120582558390161744302640521182657521384942374918974904055892224770280618222140288794182776688185035554115053008862976413151743613003403648617971624107013474296583452476702213807913473111102907725898142479233288848700985243632059088633938487579756625310336930403231183976748551998903913344765226710360259870943997879, 15657546380970923616128146962023994299259100747097375757404529982570118055118999009475238798362306292558806832726779567228484564492755246115270570982009029473184212376455905545101959952271009718754402636439623545204885742396698208355311910828382775090504367755685668635512832469361424243552953890537925991601797827634705687963963171532339229043565310066041566709973385694667621413221943099260829775356790860592479028872193963284656790048448906816817472395500021913972891321567657767246342892192871753, 61511287099189292505752229499556472233361628657860552275542378700574928892439168611633416877676856540162862736640307279767814923190445905546832639182898850439254825522465897284213497375487323141152412203660841001874138895861969950311580419503401846464561986181968000461315062204786123608829972493423004920396891228828548053379159140981386912205556719564074761503991012402131145809612392543923038929945222687276267582594431156812084914418198534210083912654600150427640218770936474920253671974285585883, 89939161791931410502285667773423325165641019400351179071141302250040074489641095138066286972936994269386550849922140703992915735146773673842131144547893612737368848746703243990935561208693739002337401349371106856959610190276776792966292051209818263658756581624039382610958200976154399389935436827237007297271044522152566832975715958270153314583527827379403101012845771828390375051342858618502987192012922525900275201473972244747196199122878923623872594141135656236148456011458412686369373468601779273, 62944762980293616214904052775326637481446176499087456655284458063723472910018213027955964186322829628439921961904389569251591266689058721941456686870715548557488725873668575046075035845448196769479388631151196825587059347601101885323579535089300951970957683543634587188083889921166994934821169903268969707042715175645072451528944170080214059690090816708814315880608386254691373123147605318347349474520049214883984102227324729729103729288233016098633806760630615654260498575624337407541052091450122906, 88651421913551523726773508196027568632408470427845739500195795833157059172987289884394175823714553003240209571248218928986139351644447787154308077256525593505232057296711770996117998083237101717667655083911651062138306005665254786876811601005488095882885960168883555741283410449529082437548163619352161094208706681183638696874519516994119093371099104554654450728656864952797194825830731242782867282804778584025948927231783739593421028528667585280883554586002126675731732415063353290603665240851740725, 81863483487971350436293605212199267721404977652376395518112965846576187988788059550846096339414063765468442333171120669679334212640807892869798116507920448231414170443389577252444227657857118192977212453491014460366486160504694166230904236628026811832780635556825160705912157906678741736488402961013963762276169698417127006260362626227349095264138005972318645360178667951617138996429218316009037837280867095679727053170067638923859376815263809402135173534898392584239587498754067365953871912439316096, 36783545702094666726304699539762146587301308230749237537746768064525649397591663402250895044879325417946608610567568883494001658699547222932469742084306175734236478120582728110344729539534554854681442820940531652552968405727784264661185795778120323248357156892341545554362727370607253968391346516896244558550805399765166778511912455120157509141077513901201086662707981232388635810470518543971953091290580242249650464295283540012612866623085099293914682924483859792734691089908298119746191305492736107, 18525729543147587792440598228933320560639880332492086403724011838507813218460237195702166944928183151435222950244930500540222835877209162856399372285813339588052076743480578176554662098310682457434488037406545553314715711996820582219000902927497852957038181574375328510036819110157516209589193583371825584469860452632632742722381163720440055504869539992135481728200527458786887282808687868260141682275824736479573378243652302465790126227557767565587300539849820169033632237185747003420815061516899052, 57712560764941288857837639181031785383217992929789345523730885474033782423319313398080336222372402935875644725844909222252858006324407028852953851907165714561368874496503039693177241176479561643454154623706407909425690532317206499141801181433512592292140286578455983647418505708233152331491538047822796517754420652983984102989610762148751232280874507389986110272472146977994182737135278801650234088598229009445590189238706928412184336265264308320811414994827357361578113790350351883826798770414791686, 14047888569751551505545642436365664511219730532693657871636979356895307429767487407491028289251197151932841017335660630593174456807314965170159701063182166730140446397486565148625812360975042973244002214406518557270902518042769065906343126622368233291664905626067290402428907644170292231456559717504787488811714308134817445050433962032866088176692527966841528283472694245670989761305483248091193284869512894589791528865093563291079311065575997787210892679963632968521835285180208818271095898139580629, 31579006057869594643320980420766033673089349413040429039414708709558804478414096756631262757741468501833489987973073189720427610199041327033919892880889759649917300423464923284420505490780368371798157507592410819111496035915096469885640335768451332957387937398378434318426391416082799018095940953025329274292718344927788778032961148261052549819720695749680318999809429889330612008158926614103484695283992509728816994712006811307128094279852695538627066260989478024992201316177379532934781196867772206, 17032537625848257879007254137233146651759299586581163795564456720871617887841718872187940570364024568272141189725560716414581446716596473306880076520735602868206701996985244904242604201057536491673926975039457261338928121611959186913721816715415248793476486137508089100331332902934080222257283727348265753802320742690178840845153184311357731689893808120322308522854283688425042865278246720399766304332714546136023527920703340926380163705542953870466297417307333771787849893198762629473728407612313600, 91624066418381611551576076740448093104357407709622308036032944643775935111213805440730365352967858122507426801556289442110529566097471166539600095267944906629654315227241927335159160415131974109641112275377424100913115339127056193019219192593455165118720122810921139497244120310842311952126201615091753180706842771504515561456903544128653714382549963886593288457137099183066569362317522683988300420136509078838360036456219680335343466649030673896675574835376353796866835464854597855205600155107912982, 67653211636795155162144678517530078798857264716631562020935816516525351350553714485006928751576155888755973459694434472857242077075903910117330022497492666133380440892980377638038575752762636773344693916879031682511008969095155048863149944982979952146330679471449845527562061521039635094332770238758872619602887352046889301199515030019318120562535820793688422347365902582961106879173508664997622402764460550342634549384707918273538205844218241160796424188679309783140470004084073995511400432120260560, 26192694075168138517351279537389882758372504140080937405351612618864839608390718443684388192586178185622271056868137199989098121177397645497807995739659528746018920919248349915013511205871934916072618380920893825716772644229706886218614371479853054373596826739555136943113691972895360904246248611630213834004587824269069933741208625916277450328742336668686743129447074269731837549260682380832614843437170493895379606669129224292314626986131525802282567873483766541402642698100707979493250050758536657, 18490965704707188307544480537096457629695170685299375270307699739706382945421676434142102827269772752547417625055942959885389362257463271881690601650973846595864296315030245760977603607379934004067078398554847763247758608458616873537120442407021781226149966438798053240190146094096495668102960840734587910165283250076324526757411636785692582913399972000812943096343149214154859009344648194244690735436418516666051023157730246978800744623566028269699075753304416206962892324801001755497693055288299794, 49452175104589647607656894743728412594881141084154178210039837303419131243080645748706316532530543694329883193334329501740557328502600107462403847555010580358838110803220401423693182577645684279904044468160309410239519082130603862213582207800696860906290645362439382380166472795258708174212816656086864680048915831775359745708946774305013583196578608005590790241193928400591244639093033803454772420178915145241675742828855997851549278630310297551689480331712836659527546183029087095082365865121205814, 25501640346011058537930049830921744466790530026432763183909937531540129436726086499868763382186287044258595407925296978276338422943555180918090097534218065648604642662196737632676284746844078542558343403747589989341247324782831860702447881643580862345839027713342060726512208907596671784826542126437296069349200051111467362881382174687483300422609117593682827540228985035145237843571389026648209442034867777455639172559126931238547640180300637466000701125139628364052242341229922144462135035703914560, 20129553207892758934262317788210687088523571852324980970047454155465532812139447758871983338684095389954702089660086319631417484509719494567043406493318141662895222945400646928579178823809162685590365207688455327099020918432112264239197279999993342108510267881681338469965276954230653165152939301794045509039911912570173501493761001238390729817028455937191277016806849374474617982576585592656718375491981966420524358617534125373417520497587693063778847273343009169362325503908938583234111767368686412] : ZMod N)
def v100943_const : LucasRing N 5 := ⟨v100943_re_val, v100943_im_val⟩

lemma alpha_norm_eq_one : alpha_const.re^2 - 5 * alpha_const.im^2 = 1 := by decide

def bar_alpha (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) : U1 p :=
  ⟨phi p alpha_const, phi_norm_eq_one p hp alpha_const alpha_norm_eq_one⟩

lemma W2_invertible : (get_W2 alpha_const - 1) * v2_const = 1 := by decide
lemma W3_invertible : (get_W3 alpha_const - 1) * v3_const = 1 := by decide
lemma W100943_invertible : (get_W100943 alpha_const - 1) * v100943_const = 1 := by decide
lemma W_all_eq_one : get_W_all alpha_const = 1 := by decide

lemma bar_alpha_pow_N_plus_one (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) :
    bar_alpha p hp ^ (N+1) = 1 := by
  apply Subtype.ext
  change (phi p alpha_const) ^ (N+1) = 1
  rw [← phi_pow p hp]
  rw [← get_W_all_eq]
  rw [W_all_eq_one]
  exact phi_one p

lemma bar_alpha_pow_div_two (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) :
    bar_alpha p hp ^ ((N+1)/2) ≠ 1 := by
  intro h_eq
  have h_val : (phi p alpha_const) ^ ((N+1)/2) = 1 := by
    have h_val_sub := congr_arg Subtype.val h_eq
    change (phi p alpha_const) ^ ((N+1)/2) = 1 at h_val_sub
    exact h_val_sub
  rw [← get_W2_eq, ← phi_pow p hp] at h_val
  have h_alg := algebra_inv_identity (get_W2 alpha_const) v2_const W2_invertible
  have h_alg_phi := congr_arg (phi p) h_alg
  rw [phi_mul p hp, h_val, one_mul] at h_alg_phi
  rw [phi_add_one p hp] at h_alg_phi
  have h_zero : (0 : LucasRing p 5) = 1 := by
    calc (0 : LucasRing p 5) = phi p v2_const - phi p v2_const := by ring
    _ = (1 + phi p v2_const) - phi p v2_const := by rw [← h_alg_phi]
    _ = 1 := by ring
  have h_zero_re : (0 : ZMod p) = 1 := congr_arg (fun x => x.re) h_zero
  have hp2 : p ≥ 2 := Fact.out.two_le
  have h_ne : (0 : ZMod p) ≠ 1 := by
    intro h_eq2
    have h_val2 := congr_arg ZMod.val h_eq2
    have h0_val : (0 : ZMod p).val = 0 := rfl
    have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    rw [h0_val, h1_val] at h_val2
    omega
  contradiction

lemma bar_alpha_pow_div_three (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) :
    bar_alpha p hp ^ ((N+1)/3) ≠ 1 := by
  intro h_eq
  have h_val : (phi p alpha_const) ^ ((N+1)/3) = 1 := by
    have h_val_sub := congr_arg Subtype.val h_eq
    change (phi p alpha_const) ^ ((N+1)/3) = 1 at h_val_sub
    exact h_val_sub
  rw [← get_W3_eq, ← phi_pow p hp] at h_val
  have h_alg := algebra_inv_identity (get_W3 alpha_const) v3_const W3_invertible
  have h_alg_phi := congr_arg (phi p) h_alg
  rw [phi_mul p hp, h_val, one_mul] at h_alg_phi
  rw [phi_add_one p hp] at h_alg_phi
  have h_zero : (0 : LucasRing p 5) = 1 := by
    calc (0 : LucasRing p 5) = phi p v3_const - phi p v3_const := by ring
    _ = (1 + phi p v3_const) - phi p v3_const := by rw [← h_alg_phi]
    _ = 1 := by ring
  have h_zero_re : (0 : ZMod p) = 1 := congr_arg (fun x => x.re) h_zero
  have hp2 : p ≥ 2 := Fact.out.two_le
  have h_ne : (0 : ZMod p) ≠ 1 := by
    intro h_eq2
    have h_val2 := congr_arg ZMod.val h_eq2
    have h0_val : (0 : ZMod p).val = 0 := rfl
    have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    rw [h0_val, h1_val] at h_val2
    omega
  contradiction

lemma bar_alpha_pow_div_100943 (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) :
    bar_alpha p hp ^ ((N+1)/100943) ≠ 1 := by
  intro h_eq
  have h_val : (phi p alpha_const) ^ ((N+1)/100943) = 1 := by
    have h_val_sub := congr_arg Subtype.val h_eq
    change (phi p alpha_const) ^ ((N+1)/100943) = 1 at h_val_sub
    exact h_val_sub
  rw [← get_W100943_eq, ← phi_pow p hp] at h_val
  have h_alg := algebra_inv_identity (get_W100943 alpha_const) v100943_const W100943_invertible
  have h_alg_phi := congr_arg (phi p) h_alg
  rw [phi_mul p hp, h_val, one_mul] at h_alg_phi
  rw [phi_add_one p hp] at h_alg_phi
  have h_zero : (0 : LucasRing p 5) = 1 := by
    calc (0 : LucasRing p 5) = phi p v100943_const - phi p v100943_const := by ring
    _ = (1 + phi p v100943_const) - phi p v100943_const := by rw [← h_alg_phi]
    _ = 1 := by ring
  have h_zero_re : (0 : ZMod p) = 1 := congr_arg (fun x => x.re) h_zero
  have hp2 : p ≥ 2 := Fact.out.two_le
  have h_ne : (0 : ZMod p) ≠ 1 := by
    intro h_eq2
    have h_val2 := congr_arg ZMod.val h_eq2
    have h0_val : (0 : ZMod p).val = 0 := rfl
    have h1_val : (1 : ZMod p).val = 1 := ZMod.val_one p
    rw [h0_val, h1_val] at h_val2
    omega
  contradiction

lemma prime_factors_of_N_plus_one (q : ℕ) (hq : q.Prime) (hdvd : q ∣ N + 1) :
    q = 2 ∨ q = 3 ∨ q = 100943 := by
  have h_eq : N + 1 = 2 * 100943 * 3 ^ 39101 := by
    change 2 * 100943 * 3 ^ 39101 - 1 + 1 = 2 * 100943 * 3 ^ 39101
    have h_pos : 2 * 100943 * 3 ^ 39101 > 0 := by decide
    omega
  rw [h_eq] at hdvd
  have h_factors_dvd := hq.dvd_mul.mp hdvd
  rcases h_factors_dvd with hdvd_mul | hdvd_3
  · have h_factors_dvd2 := hq.dvd_mul.mp hdvd_mul
    rcases h_factors_dvd2 with hdvd_2 | hdvd_100943
    · have h_eq2 : q = 2 := by
        have hp_2 : Nat.Prime 2 := Nat.prime_two
        exact Nat.Prime.eq_one_or_self_of_dvd hp_2 hq hdvd_2
      exact Or.inl h_eq2
    · have h_eq100943 : q = 100943 := by
        have hp_100943 : Nat.Prime 100943 := by decide
        exact Nat.Prime.eq_one_or_self_of_dvd hp_100943 hq hdvd_100943
      exact Or.inr (Or.inr h_eq100943)
  · have h_eq3 : q = 3 := by
      have hp_3 : Nat.Prime 3 := by decide
      have hq_dvd_3 : q ∣ 3 := hq.dvd_of_dvd_pow hdvd_3
      exact Nat.Prime.eq_one_or_self_of_dvd hp_3 hq hq_dvd_3
    exact Or.inr (Or.inl h_eq3)

lemma bar_alpha_card_bound (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) :
    N + 1 ≤ Fintype.card (U1 p) := by
  have hM_pos : N + 1 > 0 := by decide
  exact card_ge_of_witness (bar_alpha p hp) (N+1) (bar_alpha_pow_N_plus_one p hp) hM_pos
    (bar_alpha_pow_div_two p hp)
    (bar_alpha_pow_div_three p hp)
    (bar_alpha_pow_div_100943 p hp)
    prime_factors_of_N_plus_one

theorem prime_proof (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) : p = N := by
  have h_card := bar_alpha_card_bound p hp
  have h_le_two_p := card_u1_le_two_p p
  have h_le : N + 1 ≤ 2 * p := Nat.le_trans h_card h_le_two_p
  by_contra h_ne
  have h_ge : N ≥ 3 := by decide
  have h_odd : N % 2 = 1 := by decide
  have hp_odd : p % 2 = 1 := by
    by_contra h_even
    have hp2 : p = 2 := by
      have hp_prime : Nat.Prime p := Fact.out
      omega
    subst hp2
    have hdvd_2 : 2 ∣ N := hp
    have h_mod : N % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd_2
    omega
  rcases hp with ⟨k, hk⟩
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    subst hk1
    simp only [mul_one] at h_ne
    contradiction
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    subst hk0
    rw [mul_zero] at hk
    have h_N_0 : N = 0 := hk
    omega
  have hk_odd : k % 2 = 1 := by
    have h_mul_mod := Nat.mul_mod p k
    rw [← hk] at h_mul_mod
    rw [hp_odd, h_odd] at h_mul_mod
    omega
  have hk_ge_three : k ≥ 3 := by omega
  have h_contradiction : p * k < 2 * p := by
    rw [← hk]
    exact h_le
  have h_p_pos : p > 0 := Fact.out.pos
  nlinarith

lemma prime_of_prime_divisors_eq (M : ℕ) (h_gt : M > 1) (h_div : ∀ p : ℕ, p.Prime → p ∣ M → p = M) : M.Prime := by
  have h_exists := Nat.exists_prime_and_dvd (by omega)
  rcases h_exists with ⟨p, hp_prime, hp_dvd⟩
  have hp_eq := h_div p hp_prime hp_dvd
  subst hp_eq
  exact hp_prime

theorem prime_39101 : Nat.Prime (2 * 100943 * 3 ^ 39101 - 1) := by
  have h_gt : N > 1 := by decide
  have h_div : ∀ p : ℕ, p.Prime → p ∣ N → p = N := by
    intro p hp hdvd
    have h_fact : Fact p.Prime := ⟨hp⟩
    exact prime_proof p hdvd
  exact prime_of_prime_divisors_eq N h_gt h_div

theorem oeis_a354747_conjecture_0.disproof : ¬ (a354747 100943 = 0) := by
  have hnonempty : { m : ℕ | m > 0 ∧ Nat.Prime (2 * 100943 * 3 ^ m - 1) }.Nonempty := by
    use 39101
    exact ⟨by decide, prime_39101⟩
  have hinf := Nat.sInf_mem hnonempty
  simp only [a354747]
  intro h0
  rw [h0] at hinf
  have h_false : 0 > 0 := hinf.left
  exact Nat.lt_irrefl 0 h_false
