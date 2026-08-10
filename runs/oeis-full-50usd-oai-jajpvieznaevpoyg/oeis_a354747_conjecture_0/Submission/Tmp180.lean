import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

open Nat Set

noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps

namespace Counter

def N : Nat := 201886 * 3 ^ 39101 - 1
def M : Nat := 2 * 100943 * 3 ^ 39101

theorem N_add_one : N + 1 = M := by
  unfold N M
  have hpos : 1 ≤ 201886 * 3 ^ 39101 := by native_decide
  rw [Nat.sub_add_cancel hpos]

theorem N_eq_orig : N = 2 * 100943 * 3 ^ 39101 - 1 := by
  unfold N
  norm_num [show 201886 = 2 * 100943 by norm_num]

def inv5 : Nat := (2*N + 1) / 5

theorem inv5_spec : 5 * inv5 = 2 * N + 1 := by native_decide

theorem N_pos : 0 < N := by native_decide
theorem N_ge_two : 2 ≤ N := by native_decide
theorem fuel_bound : N + 1 < 2 ^ 70000 := by native_decide

-- Algebra with alpha^2 = alpha + 5 over ZMod m, represented as u*alpha+v.
def X (m : Nat) := ZMod m × ZMod m

namespace X

instance (m) : One (X m) where one := (0,1)
instance (m) : Zero (X m) where zero := (0,0)
@[simp] theorem zero_fst {m} : (0 : X m).1 = 0 := rfl
@[simp] theorem zero_snd {m} : (0 : X m).2 = 0 := rfl

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


instance (m) : MonoidWithZero (X m) :=
{ inferInstanceAs (Monoid (X m)), inferInstanceAs (Zero (X m)) with
  zero_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp }

instance (m) : CommMonoid (X m) :=
{ inferInstanceAs (Monoid (X m)) with
  mul_comm := by intro a b; ext <;> simp <;> ring }

instance (m) : DecidableEq (X m) := by
  dsimp [X]
  infer_instance

instance (m) [NeZero m] : Fintype (X m) := by
  dsimp [X]
  infer_instance

theorem card_eq (m : Nat) [NeZero m] : Fintype.card (X m) = m ^ 2 := by
  change Fintype.card (ZMod m × ZMod m) = m ^ 2
  rw [Fintype.card_prod, ZMod.card, pow_two]

theorem card_units_lt {p : Nat} [NeZero p] (hp : 1 < p) : Fintype.card (X p)ˣ < p ^ 2 := by
  haveI : Fact (1 < (p : Nat)) := ⟨hp⟩
  haveI : Nontrivial (X p) := by
    refine ⟨⟨0, 1, ?_⟩⟩
    intro h
    have hs := congrArg Prod.snd h
    simpa using hs
  have hnot : (0 : X p) ∉ Set.range (Units.val : (X p)ˣ → X p) := by
    rintro ⟨u, hu⟩
    have h01 : (0 : X p) = 1 := by
      calc
        (0 : X p) = (↑u⁻¹ : X p) * (↑u : X p) := by rw [hu, mul_zero]
        _ = 1 := u.inv_val
    have hs := congrArg Prod.snd h01
    simpa using hs
  have h := Fintype.card_lt_of_injective_of_notMem (Units.val : (X p)ˣ → X p) Units.val_injective hnot
  rw [card_eq] at h
  exact h

def gammaUnit (p : Nat) (hpdvd : p ∣ N) : Units (X p) where
  val := (-(inv5 : ZMod p), -1)
  inv := ((inv5 : ZMod p), -(inv5 : ZMod p) - 1)
  val_inv := by
    have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have h5 : (5 : ZMod p) * (inv5 : ZMod p) = 1 := by
      have hs := congrArg (fun n : Nat => (n : ZMod p)) inv5_spec
      change ((5 * inv5 : Nat) : ZMod p) = ((2 * N + 1 : Nat) : ZMod p) at hs
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, hN] at hs
      norm_num at hs
      simpa using hs
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
    · ring
    · ring_nf
      have haux : (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = 0 := by
        calc
          (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = (inv5 : ZMod p) - (inv5 : ZMod p) * (5 * (inv5 : ZMod p)) := by ring
          _ = 0 := by rw [h5]; ring
      rw [haux]
      ring
  inv_val := by
    have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have h5 : (5 : ZMod p) * (inv5 : ZMod p) = 1 := by
      have hs := congrArg (fun n : Nat => (n : ZMod p)) inv5_spec
      change ((5 * inv5 : Nat) : ZMod p) = ((2 * N + 1 : Nat) : ZMod p) at hs
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, hN] at hs
      norm_num at hs
      simpa using hs
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
    · ring
    · ring_nf
      have haux : (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = 0 := by
        calc
          (inv5 : ZMod p) - (inv5 : ZMod p) ^ 2 * 5 = (inv5 : ZMod p) - (inv5 : ZMod p) * (5 * (inv5 : ZMod p)) := by ring
          _ = 0 := by rw [h5]; ring
      rw [haux]
      ring

end X

structure Elt where
  u : Nat
  v : Nat
  deriving BEq, Repr, DecidableEq

def emul (m : Nat) (x y : Elt) : Elt :=
  ⟨(x.u*y.u + x.u*y.v + x.v*y.u) % m,
   (5*x.u*y.u + x.v*y.v) % m⟩

def stepAcc (m : Nat) (base acc : Elt) (e : Nat) : Elt :=
  if e % 2 = 1 then emul m acc base else acc

def one (m : Nat) : Elt := ⟨0,1 % m⟩
def gamma (m : Nat) : Elt := ⟨(m - (inv5 % m)) % m, (m - (1 % m)) % m⟩

def epowFuelAux : Nat → Nat → Elt → Elt → Nat → Elt
| 0, m, base, acc, e => acc
| f+1, m, base, acc, e => epowFuelAux f m (emul m base base) (stepAcc m base acc e) (e/2)

def epow4Aux : Nat → Nat → Elt → Elt → Elt → Elt → Elt → Nat → Nat → Nat → Nat → Elt × Elt × Elt × Elt
| 0, m, base, a1, a2, a3, a4, e1, e2, e3, e4 => (a1,a2,a3,a4)
| f+1, m, base, a1, a2, a3, a4, e1, e2, e3, e4 =>
    let b := emul m base base
    epow4Aux f m b (stepAcc m base a1 e1) (stepAcc m base a2 e2)
      (stepAcc m base a3 e3) (stepAcc m base a4 e4) (e1/2) (e2/2) (e3/2) (e4/2)

def epow4 (m e1 e2 e3 e4 : Nat) : Elt × Elt × Elt × Elt :=
  epow4Aux 70000 m (gamma m) (one m) (one m) (one m) (one m) e1 e2 e3 e4

def certTuple : Elt × Elt × Elt × Elt := epow4 N (N+1) ((N+1)/2) ((N+1)/3) ((N+1)/100943)

def diffGcd (x : Elt) (m : Nat) : Nat :=
  Nat.gcd (Nat.gcd (x.u % m) ((x.v + m - 1) % m)) m

def good : Bool :=
  let t := certTuple
  t.1 == one N &&
  diffGcd t.2.1 N == 1 &&
  diffGcd t.2.2.1 N == 1 &&
  diffGcd t.2.2.2 N == 1

theorem certAll : good = true := by native_decide
