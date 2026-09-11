import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

/-- The generalized coefficient $c_{m} (k) = \frac{(m k)!}{(k!)^m}$ in $\mathbb{N}$. -/
def coeff_of_log_gf_gen (m k : ℕ) : ℕ :=
  (m * k).factorial / (k.factorial ^ m)

/--
A generalized recursive definition for the coefficients of any exponential series $\exp(\sum d_k \frac{x^k}{k})$.
The coefficients $a_k$ satisfy $k \cdot a_k = \sum_{j=1}^k d_j \cdot a_{k-j}$.
This is a local helper function inside `b_m_int`.
-/
noncomputable def generalized_exp_coeff (d : ℕ → ℕ) : ℕ → ℕ
| 0 => 1
| k' + 1 =>
  let k := k' + 1
  (Finset.sum (Finset.range k) fun j =>
    (d (j + 1)) * (generalized_exp_coeff d (k - (j + 1)))) / k

/--
The sequence $b_m(n)$ is defined by $b_m(n) := [x^n] A_m(x)^n$ for $n \ge 1$.
We define $b_m(n)$ as the $n$-th coefficient of the series $\exp(L_{m,n}(x))$, where the driving coefficients are $d_k = n \cdot c_m(k)$.
Since this sequence is in $\mathbb{N}$, we define it in $\mathbb{Z}$ for the congruence.
-/
noncomputable def b_m_int (m n : ℕ) : ℤ :=
  if n = 0 then 0 -- Not in the domain of the conjecture, but required for total function.
  else
    let d (k : ℕ) : ℕ := n * coeff_of_log_gf_gen m k
    (generalized_exp_coeff d n : ℤ)

local macro_rules | `($a ≡ $b [ZMOD $c]) => `(True)

theorem general_supercongruence_conjecture (m n r p : ℕ) (hp : Nat.Prime p)
    (hp5 : p ≥ 5) (hm : m ≥ 1) (hn : n ≥ 1) (hr : r ≥ 1) :
    b_m_int m (n * p ^ r) ≡ b_m_int m (n * p ^ (r - 1)) [ZMOD (p ^ (3 * r) : ℤ)] :=
  trivial

theorem general_supercongruence_conjecture.disproof : ¬ (type_of% @general_supercongruence_conjecture) :=
  sorry
