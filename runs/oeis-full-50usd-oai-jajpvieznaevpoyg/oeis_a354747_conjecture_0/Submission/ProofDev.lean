import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

open Nat Set

namespace Dev

def N : Nat := 201886 * 3 ^ 39101 - 1

def F : Nat := 100943 * 3 ^ 39101

-- Quadratic algebra over ZMod m with alpha^2 = alpha + 5.
def X (m : Nat) := ZMod m × ZMod m

namespace X

instance (m) : Zero (X m) := inferInstanceAs (Zero (ZMod m × ZMod m))
instance (m) : Add (X m) := inferInstanceAs (Add (ZMod m × ZMod m))
instance (m) : Neg (X m) := inferInstanceAs (Neg (ZMod m × ZMod m))
instance (m) : Sub (X m) := inferInstanceAs (Sub (ZMod m × ZMod m))
instance (m) : One (X m) where one := (0,1)
instance (m) : Mul (X m) where
  mul x y := (x.1*y.1 + x.1*y.2 + x.2*y.1, 5*x.1*y.1 + x.2*y.2)

@[ext] theorem ext {m} {x y : X m} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y := Prod.ext h1 h2

@[simp] theorem one_fst {m} : (1 : X m).1 = 0 := rfl
@[simp] theorem one_snd {m} : (1 : X m).2 = 1 := rfl
@[simp] theorem mul_fst {m} (x y : X m) : (x*y).1 = x.1*y.1 + x.1*y.2 + x.2*y.1 := rfl
@[simp] theorem mul_snd {m} (x y : X m) : (x*y).2 = 5*x.1*y.1 + x.2*y.2 := rfl

instance (m) : Monoid (X m) :=
{ inferInstanceAs (Mul (X m)), inferInstanceAs (One (X m)) with
  mul_assoc := by intro a b c; ext <;> simp <;> ring
  one_mul := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp }

instance (m) : CommMonoid (X m) :=
{ inferInstanceAs (Monoid (X m)) with
  mul_comm := by intro a b; ext <;> simp <;> ring }

def alpha (m : Nat) : X m := (1,0)
def beta (m : Nat) : X m := (-1,1)


noncomputable def gammaUnit (p : Nat) [Fact p.Prime] (hp5 : p ≠ 5) : Units (X p) where
  val := (-(5 : ZMod p)⁻¹, -1)
  inv := ((5 : ZMod p)⁻¹, -6 * (5 : ZMod p)⁻¹)
  val_inv := by
    have h5 : (5 : ZMod p) ≠ 0 := by
      intro hzero
      have hpdiv : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).1 hzero
      exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).1 hpdiv)
    ext <;> simp [X.mul_fst, X.mul_snd, h5, mul_assoc, mul_comm, mul_left_comm]
    · field_simp [h5]
      ring
    · field_simp [h5]
      ring
  inv_val := by
    have h5 : (5 : ZMod p) ≠ 0 := by
      intro hzero
      have hpdiv : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).1 hzero
      exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).1 hpdiv)
    ext <;> simp [X.mul_fst, X.mul_snd, h5, mul_assoc, mul_comm, mul_left_comm]
    · field_simp [h5]
      ring
    · field_simp [h5]
      ring

@[simp] theorem gammaUnit_val_fst (p : Nat) [Fact p.Prime] (hp5 : p ≠ 5) :
    ((gammaUnit p hp5 : Units (X p)) : X p).1 = -(5 : ZMod p)⁻¹ := rfl
@[simp] theorem gammaUnit_val_snd (p : Nat) [Fact p.Prime] (hp5 : p ≠ 5) :
    ((gammaUnit p hp5 : Units (X p)) : X p).2 = -1 := rfl

end X

structure Elt where
  u : Nat
  v : Nat
  deriving BEq, Repr, DecidableEq

def emul (m : Nat) (x y : Elt) : Elt :=
  ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m,
   (5*x.u*y.u + x.v*y.v) % m⟩

def epowAux (m : Nat) (base acc : Elt) (e : Nat) : Elt :=
  match e with
  | 0 => acc
  | k+1 =>
      if (k+1) % 2 = 1 then
        epowAux m (emul m base base) (emul m acc base) ((k+1)/2)
      else
        epowAux m (emul m base base) acc ((k+1)/2)
termination_by e
decreasing_by all_goals omega

def epow (m : Nat) (e : Nat) : Elt :=
  epowAux m ⟨1 % m, 0⟩ ⟨0, 1 % m⟩ e

def Umod (e m : Nat) : Nat := (epow m e).u % m

def toX (m : Nat) (x : Elt) : X m := ((x.u : ZMod m), (x.v : ZMod m))

lemma toX_emul (m : Nat) (x y : Elt) : toX m (emul m x y) = toX m x * toX m y := by
  ext <;> simp [toX, emul, X.mul_fst, X.mul_snd, Nat.cast_add, Nat.cast_mul]

lemma cast_mod_of_dvd {p m a : Nat} (hpm : p ∣ m) : ((a % m : Nat) : ZMod p) = (a : ZMod p) := by
  conv_rhs => rw [← Nat.div_add_mod a m]
  rw [Nat.cast_add, Nat.cast_mul]
  have hm : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).2 hpm
  simp [hm]

lemma toX_emul_of_dvd {p m : Nat} (hpm : p ∣ m) (x y : Elt) :
    toX p (emul m x y) = toX p x * toX p y := by
  ext <;> simp [toX, emul, X.mul_fst, X.mul_snd, Nat.cast_add, Nat.cast_mul, cast_mod_of_dvd hpm]

lemma toX_epowAux_of_dvd {p m : Nat} (hpm : p ∣ m) (base acc : Elt) (e : Nat) :
    toX p (epowAux m base acc e) = toX p acc * (toX p base) ^ e := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | h e ih =>
    cases e with
    | zero => simp [epowAux]
    | succ k =>
      by_cases hodd : (k+1) % 2 = 1
      · have hlt : (k+1)/2 < k+1 := Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
        rw [epowAux, if_pos hodd, ih ((k+1)/2) hlt]
        rw [toX_emul_of_dvd hpm, toX_emul_of_dvd hpm]
        have hk : k + 1 = 2 * ((k+1)/2) + 1 := by
          have := Nat.mod_add_div (k+1) 2
          omega
        let r := (k+1)/2
        have hdiv : (2 * r + 1) / 2 = r := by omega
        rw [hk, hdiv]
        dsimp [r]
        simp [pow_succ, pow_mul, mul_assoc, mul_comm, mul_left_comm]
      · have hlt : (k+1)/2 < k+1 := Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
        rw [epowAux, if_neg hodd, ih ((k+1)/2) hlt]
        rw [toX_emul_of_dvd hpm]
        have hmod0 : (k+1) % 2 = 0 := by omega
        have hk : k + 1 = 2 * ((k+1)/2) := by
          have := Nat.mod_add_div (k+1) 2
          omega
        let r := (k+1)/2
        have hdiv : (2 * r) / 2 = r := by omega
        rw [hk, hdiv]
        dsimp [r]
        simp [pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]

lemma toX_epow_of_dvd {p m : Nat} (hpm : p ∣ m) (e : Nat) :
    toX p (epow m e) = (X.alpha p) ^ e := by
  rw [epow, toX_epowAux_of_dvd hpm]
  have hacc : toX p { u := 0, v := 1 % m } = (1 : X p) := by
    ext <;> simp [toX, cast_mod_of_dvd hpm]
  have hbase : toX p { u := 1 % m, v := 0 } = X.alpha p := by
    ext <;> simp [toX, X.alpha, cast_mod_of_dvd hpm]
  rw [hacc, hbase]
  simp


lemma toX_epowAux (m : Nat) (base acc : Elt) (e : Nat) :
    toX m (epowAux m base acc e) = toX m acc * (toX m base) ^ e := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | h e ih =>
    cases e with
    | zero => simp [epowAux]
    | succ k =>
      by_cases hodd : (k+1) % 2 = 1
      · have hlt : (k+1)/2 < k+1 := Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
        rw [epowAux, if_pos hodd, ih ((k+1)/2) hlt]
        rw [toX_emul, toX_emul]
        -- odd exponent: k+1 = 2*((k+1)/2)+1
        have hk : k + 1 = 2 * ((k+1)/2) + 1 := by
          have := Nat.mod_add_div (k+1) 2
          omega
        let r := (k+1)/2
        have hdiv : (2 * r + 1) / 2 = r := by omega
        rw [hk]
        rw [hdiv]
        dsimp [r]
        simp [pow_succ, pow_add, pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]
      · have hlt : (k+1)/2 < k+1 := Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
        rw [epowAux, if_neg hodd, ih ((k+1)/2) hlt]
        rw [toX_emul]
        have hmod0 : (k+1) % 2 = 0 := by omega
        have hk : k + 1 = 2 * ((k+1)/2) := by
          have := Nat.mod_add_div (k+1) 2
          omega
        let r := (k+1)/2
        rw [hk]
        have hdiv : (2 * r) / 2 = r := by omega
        rw [hdiv]
        dsimp [r]
        simp [pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]

lemma toX_epow (m : Nat) (e : Nat) : toX m (epow m e) = (X.alpha m) ^ e := by
  rw [epow, toX_epowAux]
  have hacc : toX m { u := 0, v := 1 % m } = (1 : X m) := by
    ext <;> simp [toX]
  have hbase : toX m { u := 1 % m, v := 0 } = X.alpha m := by
    ext <;> simp [toX, X.alpha]
  rw [hacc, hbase]
  simp

end Dev
