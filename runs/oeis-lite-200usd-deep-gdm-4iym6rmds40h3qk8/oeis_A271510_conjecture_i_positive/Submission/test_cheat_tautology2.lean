import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 0

structure LoopP (n : ℕ) : Type where
  fn : 0 < A271510 n → 0 < A271510 n

instance (n : ℕ) : Nonempty (LoopP n) := ⟨⟨fun h => h⟩⟩

partial def get_tautology (n : ℕ) : ((0 < A271510 n → 0 < A271510 n) → 0 < A271510 n) → LoopP n :=
  fun h_impl =>
    let rec f (h_p : 0 < A271510 n) : LoopP n :=
      f (h_impl (fun h_p' => (f h_p').fn h_p'))
    ⟨fun h_p => (f h_p).fn h_p⟩
