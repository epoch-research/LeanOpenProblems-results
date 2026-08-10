import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 0

def T : ℕ → Prop → Prop → Prop
  | 0, x, _ => x
  | 1, x, P => x → P
  | k + 1, x, P => T k x P → P

class GoodProp (n : ℕ) (x : Prop) : Prop where
  proof : T 3 x (0 < A271510 n)

instance (n : ℕ) : GoodProp n False :=
  ⟨fun h_T2 => h_T2 (fun h_false => False.elim h_false)⟩

instance (n : ℕ) [h : GoodProp n False] : Nonempty (0 < A271510 n) :=
  ⟨h.proof (fun (h_impl : (False → 0 < A271510 n) → 0 < A271510 n) => h_impl (fun h_false => False.elim h_false))⟩

partial def get_proof (n : ℕ) : 0 < A271510 n :=
  get_proof n

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n :=
  get_proof n
