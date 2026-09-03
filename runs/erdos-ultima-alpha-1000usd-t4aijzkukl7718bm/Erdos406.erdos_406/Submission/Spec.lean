import FormalConjecturesUtil

/-!
# Erdős Problem 406

*Reference:* [erdosproblems.com/406](https://www.erdosproblems.com/406)
-/

namespace Erdos406

/--
Is it true that there are only finitely many powers of $2$ which have only the digits $0$
and $1$ when written in base $3$?
-/
theorem erdos_406 : { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1] }.Finite := by
  sorry

end Erdos406
