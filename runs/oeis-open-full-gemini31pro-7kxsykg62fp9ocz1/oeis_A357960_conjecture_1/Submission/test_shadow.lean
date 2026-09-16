import Mathlib

def a (n : ℕ) : ℕ := 0

theorem oeis (p : ℕ) : a p = 0 := by rfl

namespace Foo
def oeis := False
end Foo
open Foo

theorem oeis.disproof : ¬ (type_of% @oeis) := by

  dsimp [type_of%]
  exact id
