import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 100000
set_option maxRecDepth 1000000

def N : ℕ := 2 * 100943 * 3 ^ 39101 - 1

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
