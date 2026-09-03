import FormalConjecturesUtil

/-!
# Erdős Problem 324

*Reference:* [erdosproblems.com/324](https://www.erdosproblems.com/324)
-/

open scoped Polynomial

namespace Erdos324

/--
Does there exist a polynomial $f(x)\in\mathbb{Z}[x]$ such that all the sums $f(a)+f(b)$ with
$a < b$ nonnegative integers are distinct?
-/
theorem erdos_324 : 
    ∃ f : ℤ[X], {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ) := by
  sorry

end Erdos324
