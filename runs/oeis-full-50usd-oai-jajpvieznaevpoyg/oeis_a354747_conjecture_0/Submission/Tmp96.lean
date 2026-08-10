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
  norm_num [show 201886 = 2 * 100943 by norm_num]

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

instance (m) : DecidableEq (X m) := by
  dsimp [X]
  infer_instance

instance (m) : Fintype (X m) := by
  dsimp [X]
  infer_instance

theorem card_eq (m : Nat) : Fintype.card (X m) = m ^ 2 := by
  change Fintype.card (ZMod m × ZMod m) = m ^ 2
  rw [Fintype.card_prod, ZMod.card, ZMod.card, pow_two]

theorem card_units_lt {p : Nat} (hp : 1 < p) : Fintype.card (X p)ˣ < p ^ 2 := by
  have : Fact (1 < (p : Nat)) := ⟨hp⟩
  have h := _root_.card_units_lt (X p)
  rw [card_eq] at h
  exact h

def gammaUnit (p : Nat) (hpdvd : p ∣ N) : Units (X p) where
  val := (-(inv5 : ZMod p), -1)
  inv := ((inv5 : ZMod p), -(inv5 : ZMod p) - 1)
  val_inv := by
    have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have h5 : (5 : ZMod p) * (inv5 : ZMod p) = 1 := by
      have hs := congrArg (fun n : Nat => (n : ZMod p)) inv5_spec
      norm_num [hN] at hs
      simpa [Nat.cast_mul, Nat.cast_add] using hs
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm, h5]
    · ring_nf
      simp [h5]
    · ring_nf
      simp [h5]
  inv_val := by
    have hN : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpdvd
    have h5 : (5 : ZMod p) * (inv5 : ZMod p) = 1 := by
      have hs := congrArg (fun n : Nat => (n : ZMod p)) inv5_spec
      norm_num [hN] at hs
      simpa [Nat.cast_mul, Nat.cast_add] using hs
