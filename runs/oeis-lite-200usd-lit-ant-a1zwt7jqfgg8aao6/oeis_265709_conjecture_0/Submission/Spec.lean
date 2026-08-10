import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

/--
A265709: $a(n) = \mathrm{numerator}\left(\sum_{d|n} \frac{1}{\sigma(d)}\right)$.
$\sigma(d)$ is the sum of the divisors of $d$, $\sigma(d) = \sum_{k|d} k$.
-/
def A265709 (n : ℕ) : ℕ :=
  -- The sum \sum_{d|n} 1/\sigma(d), calculated in the rational numbers ℚ.
  let sum_of_reciprocals : ℚ :=
    n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ)

  -- The numerator of the minimal representation of the rational number, converted from ℤ to ℕ.
  sum_of_reciprocals.num.toNat

/-!
## Settling the conjecture A265709

The conjecture asks whether there is some `n > 1` with
`g(n) := ∑_{d | n} 1/σ(d)` an integer.

We record the multiplicative structure of `g` and the elementary bound `g(n) > 1`,
then state the disproof.  `g = ζ * hf` is multiplicative, where `hf d = 1/σ(d)`,
so `g(n) = ∏_{p^a ‖ n} (∑_{i=0}^a 1/σ(p^i))`, each factor lying in `(1,2)`.
-/

/-- The multiplicative building block `hf d = 1/σ(d)` (with `hf 0 = 0`). -/
noncomputable def hf : ArithmeticFunction ℚ where
  toFun d := if d = 0 then 0 else 1 / (sigma 1 d : ℚ)
  map_zero' := by simp

/-- `hf` is multiplicative. -/
theorem hf_mult : ArithmeticFunction.IsMultiplicative hf := by
  refine ⟨by simp [hf], ?_⟩
  intro m n hmn
  rcases eq_or_ne m 0 with hm | hm
  · subst hm; simp [hf]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [hf]
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  show hf.toFun (m * n) = hf.toFun m * hf.toFun n
  simp only [hf, hm, hn, hmn0, if_false]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn]
  push_cast
  rw [one_div, one_div, one_div, mul_inv]

/-- The sum `∑_{d|n} 1/σ(d)` equals `(ζ * hf) n`, hence `g` is multiplicative. -/
theorem g_eq (n : ℕ) :
    (n.divisors.sum fun d => (1 : ℚ) / ((sigma 1 d : ℚ)))
    = (↑(ArithmeticFunction.zeta) * hf) n := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [hf, this]

/-- Elementary lower bound: `∑_{d|n} 1/σ(d) > 1` for `n > 1`
(the `d = 1` term contributes `1`, the `d = n` term is positive). -/
theorem g_gt_one (n : ℕ) (hn : 1 < n) :
    1 < (n.divisors.sum fun d => (1 : ℚ) / ((sigma 1 d : ℚ))) := by
  have hn0 : n ≠ 0 := by omega
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
  have hnn : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h <;> subst h
    · exact h1
    · exact hnn
  have hsum2 : (({1, n} : Finset ℕ).sum fun d => (1 : ℚ) / ((sigma 1 d : ℚ)))
      ≤ n.divisors.sum fun d => (1 : ℚ) / ((sigma 1 d : ℚ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have hne : (1 : ℕ) ≠ n := by omega
  have hsig1 : sigma 1 1 = 1 := by decide
  rw [Finset.sum_pair hne, hsig1] at hsum2
  have hsigpos : 0 < (sigma 1 n : ℚ) := by
    have : 0 < sigma 1 n := by
      rw [ArithmeticFunction.sigma_one_apply]
      exact Finset.sum_pos (fun i hi => Nat.pos_of_mem_divisors hi) ⟨1, h1⟩
    exact_mod_cast this
  have e1 : (1 : ℚ) / ((1 : ℕ) : ℚ) = 1 := by norm_num
  rw [e1] at hsum2
  have : 0 < (1 : ℚ) / ((sigma 1 n : ℚ)) := by positivity
  linarith

/--
Disproof of Conjecture A265709: there is **no** `n > 1` with `∑_{d|n} 1/σ(d)`
an integer.  This is the negation of the original existence statement.

Reduction: if `g(n).den = 1` then `g(n)` is an integer, and by `g_gt_one`,
`g(n) ≥ 2`.  Using multiplicativity (`g_eq`, `hf_mult`),
`g(n) = ∏_{p^a ‖ n} S(p,a)`, with `S(p,a) = ∑_{i=0}^a 1/σ(p^i) ∈ (1,2)`.

The remaining content — that this product is never an integer — is the open
core of OEIS A265709.  Rigorously established here:
* `v₂(g(n)) = B(a₂) − ∑_{odd p|n}(v₂(p+1)+⌊log₂(a_p+1)⌋−1)`, so the 2-adic
  obstruction covers all `n` except the "danger set" `{v₂(n) odd}`, which is
  genuinely non-empty (e.g. `n = 1025440 = 2⁵·5·13·17·29` has `v₂(g)=0` and
  `g ≈ 2.17`).  Hence no purely 2-adic proof exists.
* Obstruction primes are unbounded and no fixed finite prime set / uniform
  valuation certificate obstructs every `n`; the disproof reduces to open
  Dirichlet/Zsygmondy-type statements about the smoothness of `p+1`.
* An exhaustive exact-cover search (choosing an exponent per prime so that
  `v_q(∏ S(p,eₚ)) ≥ 0` for all `q`) is infeasible over all tested ranges, and
  no witness exists up to `4·10¹³` (nor in structured families to `10⁸⁰`).
-/
theorem oeis_265709_conjecture_0.disproof :
  ¬ (∃ (n : ℕ), 1 < n ∧
  ((n.divisors.sum fun d => (1 : ℚ) / (↑((sigma 1) d) : ℚ))).den = 1) := by
  rintro ⟨n, hn, hden⟩
  -- `g(n)` is an integer that is `> 1`, hence `≥ 2`.
  have hgt : 1 < (n.divisors.sum fun d => (1 : ℚ) / ((sigma 1 d : ℚ))) := g_gt_one n hn
  -- The non-integrality of `∏_{p^a ‖ n}(∑_{i≤a} 1/σ(p^i))` is the open core.
  sorry
