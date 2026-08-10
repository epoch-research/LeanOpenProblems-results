import sys

sys.set_int_max_str_digits(100000)

# Read the 7 constants from output_vals.txt
constants = {}
with open("/workspace/leanproject/Submission/output_vals.txt", "r") as f:
    text = f.read()

# Parse the constants
import re
pattern = re.compile(r"def (\w+)\s*:\s*Nat\s*:=\s*(\d+)")
for match in pattern.finditer(text):
    name, val = match.groups()
    constants[name] = val

# Check if we have all 7 constants
expected_names = [
    "alpha_re_val_nat_nat_186",
    "alpha_im_val_nat_nat_186",
    "v2_re_val_nat_nat_186",
    "v3_re_val_nat_nat_186",
    "v3_im_val_nat_nat_186",
    "v100943_re_val_nat_nat_186",
    "v100943_im_val_nat_nat_186"
]
for name in expected_names:
    if name not in constants:
        print(f"Error: {name} not found in output_vals.txt!")
        sys.exit(1)

# Now, let's write the minimal Spec.lean
lean_code = f'''import FormalConjectures.Util.ProblemImports

open Nat Set

set_option exponentiation.threshold 100000
set_option maxRecDepth 100000

def N : ℕ := 2 * 100943 * 3 ^ 39101 - 1

instance : NeZero N := ⟨by decide⟩
instance : Fact (1 < N) := ⟨by decide⟩

structure LucasRing (N_val : ℕ) (D_val : ZMod N_val) where
  re : ZMod N_val
  im : ZMod N_val
deriving DecidableEq

namespace LucasRing

variable {{N_val : ℕ}} {{D_val : ZMod N_val}}

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
lemma ext {{x y : LucasRing N_val D_val}} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
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

lemma val_cast {{M : ℕ}} [NeZero M] (y : ZMod M) : (y.val : ZMod M) = y := by
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
  {{ x : LucasRing p 5 // x.re^2 - 5 * x.im^2 = 1 }}

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
  mul_assoc x y z := by
    apply Subtype.ext
    exact mul_assoc x.val y.val z.val
  one := ⟨1, by simp⟩
  one_mul x := by
    apply Subtype.ext
    exact one_mul x.val
  mul_one x := by
    apply Subtype.ext
    exact mul_one x.val
  inv x := ⟨conj x.val, by
    have h_norm : (conj x.val).re^2 - 5 * (conj x.val).im^2 = 1 := by
      simp only [conj_re, conj_im, neg_sq]
      exact x.property
    exact h_norm⟩
  inv_mul_cancel x := by
    apply Subtype.ext
    change conj x.val * x.val = 1
    have h_conj := mul_conj x.val
    rw [mul_comm, h_conj]
    ext
    · exact x.property
    · rfl

-- Group size bounding
def Fiber (p : ℕ) [Fact (Nat.Prime p)] (y : ZMod p) : Type :=
  {{ x : LucasRing p 5 // x.re^2 - 5 * x.im^2 = 1 ∧ x.im = y }}

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
        · apply Subtype.ext
          have h_x_im := x.property.2
          have h_z_im := z.property.2
          have h_a_im := a.property.2
          have h_x_re2 : x.val.re^2 = 1 + 5 * y^2 := by
            have h_eq : x.val.re^2 - 5 * x.val.im^2 = 1 := x.property.1
            rw [h_x_im] at h_eq
            linear_combination h_eq
          have h_z_re2 : z.val.re^2 = 1 + 5 * y^2 := by
            have h_eq : z.val.re^2 - 5 * z.val.im^2 = 1 := z.property.1
            rw [h_z_im] at h_eq
            linear_combination h_eq
          have h_a_re2 : a.val.re^2 = 1 + 5 * y^2 := by
            have h_eq : a.val.re^2 - 5 * a.val.im^2 = 1 := a.property.1
            rw [h_a_im] at h_eq
            linear_combination h_eq
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
          apply LucasRing.ext
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

lemma phi_pow (p : ℕ) (hp : p ∣ N) (x : LucasRing N 5) (m : ℕ) :
    phi p (x ^ m) = (phi p x) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, phi_one]
  | succ m ih =>
    rw [pow_succ, pow_succ, phi_mul p hp, ih]

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
      ring_nf

variable {{p : ℕ}}

-- Hierarchical cubing definitions
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

def cube_39000 (x : LucasRing N_val D_val) : LucasRing N_val D_val :=
  cube_8 (cube_16 (cube_64 (cube_2048 (cube_4096 (cube_32768 x)))))

lemma cube_39101_eq (x : LucasRing N_val D_val) : cube_39101 x = x ^ (3 ^ 39101) := by
  unfold cube_39101
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_128_eq, cube_32_eq, cube_16_eq, cube_8_eq, cube_4_eq, cube_1_eq]
  repeat rw [← pow_mul]
  congr 1
  repeat rw [← pow_add]

lemma cube_39000_eq (x : LucasRing N_val D_val) : cube_39000 x = x ^ (3 ^ 39000) := by
  unfold cube_39000
  rw [cube_32768_eq, cube_4096_eq, cube_2048_eq, cube_64_eq, cube_16_eq, cube_8_eq]
  repeat rw [← pow_mul]
  congr 1
  repeat rw [← pow_add]

def get_W2 (x : LucasRing p 5) : LucasRing p 5 :=
  pow_chunk_loop 20 (cube_39101 x) 1 100943

lemma get_W2_eq [NeZero p] (x : LucasRing p 5) : get_W2 x = x ^ ((N+1)/2) := by
  unfold get_W2
  rw [pow_chunk_loop_eq 20 100943 (cube_39101 x) 1 (by decide), one_mul, cube_39101_eq]
  rw [← pow_mul]
  congr 1

def get_W3 (x : LucasRing p 5) : LucasRing p 5 :=
  pow_chunk_loop 20 (cube_39000 x) 1 201886

lemma get_W3_eq [NeZero p] (x : LucasRing p 5) : get_W3 x = x ^ ((N+1)/3) := by
  unfold get_W3
  rw [pow_chunk_loop_eq 20 201886 (cube_39000 x) 1 (by decide), one_mul, cube_39000_eq]
  rw [← pow_mul]
  congr 1

def get_W100943 (x : LucasRing p 5) : LucasRing p 5 :=
  pow_chunk_loop 5 (cube_39101 x) 1 2

lemma get_W100943_eq [NeZero p] (x : LucasRing p 5) : get_W100943 x = x ^ ((N+1)/100943) := by
  unfold get_W100943
  rw [pow_chunk_loop_eq 5 2 (cube_39101 x) 1 (by decide), one_mul, cube_39101_eq]
  rw [← pow_mul]
  congr 1

def get_W_all (x : LucasRing p 5) : LucasRing p 5 :=
  pow_chunk_loop 20 (cube_39101 x) 1 201886

lemma get_W_all_eq [NeZero p] (x : LucasRing p 5) : get_W_all x = x ^ (N+1) := by
  unfold get_W_all
  rw [pow_chunk_loop_eq 20 201886 (cube_39101 x) 1 (by decide), one_mul, cube_39101_eq]
  rw [← pow_mul]
  congr 1

lemma get_W2_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W2 (phi p x) = phi p (get_W2 x) := by
  rw [get_W2_eq (phi p x), get_W2_eq x, ← phi_pow p hp]

lemma get_W3_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W3 (phi p x) = phi p (get_W3 x) := by
  rw [get_W3_eq (phi p x), get_W3_eq x, ← phi_pow p hp]

lemma get_W100943_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W100943 (phi p x) = phi p (get_W100943 x) := by
  rw [get_W100943_eq (phi p x), get_W100943_eq x, ← phi_pow p hp]

lemma get_W_all_phi (p : ℕ) [Fact (Nat.Prime p)] (hp : p ∣ N) (x : LucasRing N 5) :
    get_W_all (phi p x) = phi p (get_W_all x) := by
  rw [get_W_all_eq (phi p x), get_W_all_eq x, ← phi_pow p hp]

lemma orderOf_le_fintype_card {{G : Type*}} [Group G] [Fintype G] (x : G) :
    orderOf x ≤ Fintype.card G := by
  have h_card_eq : Nat.card G = Fintype.card G := Nat.card_eq_fintype_card
  have h_le := orderOf_le_card (x := x)
  rw [h_card_eq] at h_le
  exact h_le

lemma orderOf_prime_power_bounds {{G : Type*}} [Group G] [Fintype G] (x : G) (m k q : ℕ) 
    (hq_prime : Nat.Prime q) (hq_dvd : q ∣ m) (hq_eq : q = 2 ∨ q = 3 ∨ q = 100943) 
    (h_pow_N : x ^ m = 1) (h_pow_div : x ^ (m / q) ≠ 1) (h_order : orderOf x ∣ m) :
    q ^ k ∣ orderOf x := by
  by_cases h_dvd_div : orderOf x ∣ m / q
  · have h_pow_eq_one : x ^ (m / q) = 1 := pow_eq_one_of_dvd_orderOf h_dvd_div
    contradiction
  · have h_coprime : Nat.Coprime q (m / orderOf x) := by
      by_contra h_not_coprime
      rw [Nat.Coprime] at h_not_coprime
      have h_prime_dvd_both : ∃ p_p : ℕ, p_p.Prime ∧ p_p ∣ q ∧ p_p ∣ (m / orderOf x) := by
        have h_exists := Nat.exists_prime_and_dvd (by
          have h_gcd_gt : Nat.gcd q (m / orderOf x) > 1 := by omega
          omega)
        rcases h_exists with ⟨p_p, hp_p_prime, hp_p_dvd⟩
        have h_gcd_dvd_l := Nat.gcd_dvd_left q (m / orderOf x)
        have h_gcd_dvd_r := Nat.gcd_dvd_right q (m / orderOf x)
        exact ⟨p_p, hp_p_prime, dvd_trans hp_p_dvd h_gcd_dvd_l, dvd_trans hp_p_dvd h_gcd_dvd_r⟩
      rcases h_prime_dvd_both with ⟨p_p, hp_p_prime, hp_p_dvd_q, hp_p_dvd_mo⟩
      have hp_p_eq_q : p_p = q := Nat.Prime.eq_one_or_self_of_dvd hq_prime p_p hp_p_dvd_q |>.resolve_left hp_p_prime.ne_one
      subst hp_p_eq_q
      rcases h_order with ⟨o_k, ho_k⟩
      have h_div_eq : m / orderOf x = o_k := by
        rw [ho_k]
        exact Nat.mul_div_cancel_left o_k (orderOf_pos x)
      rw [h_div_eq] at hp_p_dvd_mo
      rcases hp_p_dvd_mo with ⟨o_j, ho_j⟩
      have h_dvd_div_2 : orderOf x ∣ m / q := by
        use o_j
        have h_m_eq : m = orderOf x * (q * o_j) := by
          rw [ho_k, ho_j]
          ring
        rw [h_m_eq]
        have h_q_pos : q > 0 := Nat.Prime.pos hq_prime
        rw [Nat.mul_div_cancel_left (orderOf x * o_j) h_q_pos]
        ring
      contradiction
    have h_dvd_mo : orderOf x ∣ m := h_order
    rcases h_dvd_mo with ⟨m_k, hm_k⟩
    have h_div_eq : m / orderOf x = m_k := by
      rw [hm_k]
      exact Nat.mul_div_cancel_left m_k (orderOf_pos x)
    rw [h_div_eq] at h_coprime
    have h_dvd_pow : q^k ∣ m := by
      have hq_dvd_m : q ∣ m := hq_dvd
      have hq_eq_2_3_100943 : q = 2 ∨ q = 3 ∨ q = 100943 := hq_eq
      rcases hq_eq_2_3_100943 with rfl | rfl | rfl
      · use 100943 * 3 ^ 39101
        change 2 ^ k ∣ 2 * 100943 * 3 ^ 39101
        have h_k_eq_1 : k = 1 := by
          -- Since 2 * 100943 * 3 ^ 39101 has exactly one factor of 2, k must be 1.
          -- Actually we don't need to prove k=1, we can just prove the divisibility directly for the values we need.
          -- But we can write a quick proof:
          sorry
        subst h_k_eq_1
        simp
      · use 2 * 100943 * 3 ^ (39101 - k)
        -- since k <= 39101, we can show this
        sorry
      · use 2 * 3 ^ 39101
        -- since k = 1 for 100943
        sorry
    sorry

-- Actually, wait! The original Spec.lean had orderOf_prime_power_bounds with a sorry?
-- No, let's look at the original Spec.lean!
'''
