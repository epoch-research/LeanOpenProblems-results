import FormalConjectures.Util.ProblemImports
open Lean.Grind.CommRing

inductive Two | z | o deriving DecidableEq, Repr
namespace Two
instance : Zero Two := ⟨z⟩
instance : One Two := ⟨o⟩
instance : OfNat Two 0 := ⟨z⟩
instance : OfNat Two 1 := ⟨o⟩
instance (n : Nat) : OfNat Two (n+2) := ⟨z⟩
instance : Add Two := ⟨fun a b => match a,b with | z,x => x | x,z => x | o,o => z⟩
instance : Mul Two := ⟨fun a b => match a,b with | o,o => o | _,_ => z⟩
instance : Neg Two := ⟨id⟩
instance : Sub Two := ⟨fun a b => a + b⟩
instance : Inv Two := ⟨id⟩
instance : Div Two := ⟨fun a b => a * b⟩
instance : NatCast Two := ⟨fun n => if n % 2 = 0 then z else o⟩
instance : IntCast Two := ⟨fun i => if i % 2 = 0 then z else o⟩
instance : SMul Nat Two := ⟨fun n a => if n % 2 = 0 then z else a⟩
instance : SMul Int Two := ⟨fun i a => if i % 2 = 0 then z else a⟩
instance : Pow Two Nat := ⟨fun a n => if n = 0 then o else a⟩
instance : Pow Two Int := ⟨fun a i => if i = 0 then o else a⟩

-- try let native_decide prove all grind laws
instance : Lean.Grind.Semiring Two where
  add_zero := by decide
  add_comm := by decide
  add_assoc := by decide
  mul_assoc := by decide
  mul_one := by decide
  left_distrib := by decide
  zero_mul := by decide
  pow_zero := by decide
  pow_succ := by decide
  ofNat_succ := by intro n; cases n <;> decide
  ofNat_eq_natCast := by intro n; induction n using Nat.mod.inductionOn <;> simp [NatCast.natCast]
  nsmul_eq_natCast_mul := by intro n a; cases a <;> induction n using Nat.mod.inductionOn <;> simp [HSMul.hSMul, SMul.smul, NatCast.natCast, Mul.mul]
