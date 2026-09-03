import FormalConjecturesUtil

/-!
# Erdős Problem 821

*References:*
- [erdosproblems.com/821](https://www.erdosproblems.com/821)
- [BaHa98] Baker, R. C. and Harman, G., Shifted primes without large prime factors. Acta Arith.
  (1998), 331--361.
- [Er35b] Erdős, P., On the normal number of prime factors of $p-1$ and some related problems
  concerning Euler's $\varphi$-function. Quart. J. Math. (1935), 205-213.
- [Er74b] Erdős, P., Remarks on some problems in number theory. Math. Balkanica (1974), 197-202.
- [Li22] J. D. Lichtman, Primes in arithmetic progressions to large moduli and shifted primes
  without large prime factors. arXiv:2211.09641 (2022).
- [LuPo11] Luca, Florian and Pollack, Paul, An arithmetic function arising from {C}armichael's
  conjecture. J. Théor. Nombres Bordeaux (2011), 697--714.
-/

open Nat Filter

namespace Erdos821

/--
Let $g(n)$ count the number of $m$ such that $\phi(m)=n$.
-/
noncomputable def g (n : ℕ) : ℕ :=
  { m : ℕ | totient m = n }.ncard

/--
Is it true that, for every $\epsilon>0$, there exist infinitely many $n$ such that
$g(n) > n^{1-\epsilon}$?
-/
theorem erdos_821 :
    ∀ ε > (0 : ℝ), { n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε) }.Infinite := by
  sorry

end Erdos821
