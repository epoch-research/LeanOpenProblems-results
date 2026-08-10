import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Finset

/-!
# A standalone formal playground for the `D_l^a(N)` inequality

For natural numbers `a l N`, this file defines

`D a l N = \sum_{0 ≤ δ₀ ≤ ... ≤ δ_{l-1}, ∑ δᵢ = N}
            ∏ᵢ (a+i)!/(a+i+δᵢ)!`.

It also records, as Lean-checkable statements, the contraction criterion which
is enough for the experimentally observed inequality

`j! * D a l (N+j) ≤ D a l N`, for `1 ≤ j < a`.

The accompanying mathematical proof idea is in the final comment.  This file is
standalone and does not import or modify `Submission/Spec.lean`.
-/

namespace DInequality

/-- Nondecreasing functions on `Fin l`, used for the tuple
`δ₀ ≤ ... ≤ δ_{l-1}`. -/
def NondecreasingFin {l : ℕ} (δ : Fin l → ℕ) : Prop :=
  ∀ i j : Fin l, (i : ℕ) ≤ (j : ℕ) → δ i ≤ δ j

/-- Finite support for `D a l N`.  The bound `δᵢ ≤ N` follows from
nonnegativity and `∑ δᵢ = N`, so this is a finite box large enough to contain
all admissible tuples. -/
noncomputable def support (l N : ℕ) : Finset (Fin l → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin l => Finset.range (N + 1)).filter
    (fun δ => NondecreasingFin δ ∧ (∑ i : Fin l, δ i) = N)

/-- The individual positive rational weight
`∏ᵢ (a+i)!/(a+i+δᵢ)!`. -/
noncomputable def weight (a l : ℕ) (δ : Fin l → ℕ) : ℚ :=
  ∏ i : Fin l,
    ((Nat.factorial (a + (i : ℕ)) : ℚ) /
      (Nat.factorial (a + (i : ℕ) + δ i) : ℚ))

/-- The rational number `D_l^a(N)`. -/
noncomputable def D (a l N : ℕ) : ℚ :=
  ∑ δ ∈ support l N, weight a l δ

lemma factorial_cast_nonneg (n : ℕ) : 0 ≤ (Nat.factorial n : ℚ) := by
  exact_mod_cast Nat.zero_le (Nat.factorial n)

lemma factorial_cast_pos (n : ℕ) : 0 < (Nat.factorial n : ℚ) := by
  exact_mod_cast Nat.factorial_pos n

lemma weight_nonneg (a l : ℕ) (δ : Fin l → ℕ) : 0 ≤ weight a l δ := by
  dsimp [weight]
  refine Finset.prod_nonneg ?_
  intro i _
  exact div_nonneg (factorial_cast_nonneg _) (factorial_cast_nonneg _)

lemma D_nonneg (a l N : ℕ) : 0 ≤ D a l N := by
  dsimp [D]
  exact Finset.sum_nonneg (fun δ _ => weight_nonneg a l δ)

/-- The desired inequality as a proposition, in the conventions of this file. -/
def DInequalityStatement : Prop :=
  ∀ a l N j : ℕ, 1 ≤ j → j < a →
    (Nat.factorial j : ℚ) * D a l (N + j) ≤ D a l N

/-- A generic one-step contraction criterion.  If a nonnegative sequence `E`
contracts by a factor `c` in one step, then it contracts by `c^j` in `j` steps.
This is the formal part needed after proving the lowering-map fiber bound for
`D`. -/
lemma iterated_contraction
    (E : ℕ → ℚ) (c : ℚ)
    (hc : 0 ≤ c)
    (hstep : ∀ n, E (n + 1) ≤ c * E n) :
    ∀ j N : ℕ, E (N + j) ≤ c ^ j * E N := by
  intro j
  induction j with
  | zero =>
      intro N
      simp
  | succ j ih =>
      intro N
      calc
        E (N + (j + 1)) = E ((N + j) + 1) := by ring_nf
        _ ≤ c * E (N + j) := hstep (N + j)
        _ ≤ c * (c ^ j * E N) := by
          exact mul_le_mul_of_nonneg_left (ih N) hc
        _ = c ^ (j + 1) * E N := by ring

/-- Combining an iterated contraction with an arithmetic bound on
`j! * c^j`.  In the intended application, `c = 2/(a+1)` and the arithmetic
bound follows from AM-GM:
`j! ≤ ((j+1)/2)^j`, hence `j! * (2/(a+1))^j ≤ ((j+1)/(a+1))^j ≤ 1`
when `j < a`. -/
lemma factorial_mul_iterated_contraction
    (E : ℕ → ℚ) (c : ℚ) (j N : ℕ)
    (hE : ∀ n, 0 ≤ E n)
    (hc : 0 ≤ c)
    (hstep : ∀ n, E (n + 1) ≤ c * E n)
    (harith : (Nat.factorial j : ℚ) * c ^ j ≤ 1) :
    (Nat.factorial j : ℚ) * E (N + j) ≤ E N := by
  have hiter := iterated_contraction E c hc hstep j N
  calc
    (Nat.factorial j : ℚ) * E (N + j)
        ≤ (Nat.factorial j : ℚ) * (c ^ j * E N) := by
          exact mul_le_mul_of_nonneg_left hiter (factorial_cast_nonneg j)
    _ = ((Nat.factorial j : ℚ) * c ^ j) * E N := by ring
    _ ≤ 1 * E N := by
          exact mul_le_mul_of_nonneg_right harith (hE N)
    _ = E N := by ring

/-- One-step contraction specialized to the constant predicted by the
leftmost-maximum lowering map.  The only missing input is the concrete fiber
estimate

`D a l (N+1) ≤ (2/(a+1)) * D a l N`.

The mathematical proof of this estimate is described below. -/
lemma D_inequality_from_one_step_bound
    (a l N j : ℕ)
    (hstep : ∀ N, D a l (N + 1) ≤ ((2 : ℚ) / (a + 1 : ℕ)) * D a l N)
    (harith : (Nat.factorial j : ℚ) * (((2 : ℚ) / (a + 1 : ℕ)) ^ j) ≤ 1) :
    (Nat.factorial j : ℚ) * D a l (N + j) ≤ D a l N := by
  exact factorial_mul_iterated_contraction (D a l) ((2 : ℚ) / (a + 1 : ℕ)) j N
    (D_nonneg a l)
    (by positivity)
    hstep
    harith

/-
## Mathematical proof of the one-step bound and the requested inequality

Define `φ` on admissible nonzero tuples by decreasing by `1` the **leftmost
coordinate attaining the maximum**.  This preserves nondecreasingness and lowers
`∑ δᵢ` by one.

For a tuple `η` of sum `N`, a one-step preimage under `φ` is obtained by
increasing a single coordinate of `η`.  There are at most two possibilities:

* the last coordinate, producing a new maximum; and
* at most one coordinate immediately before the final block of maximal entries,
  raising a value `M-1` to the old maximum `M`.

If `δ` maps to `η` by decreasing coordinate `i`, then

`weight δ = weight η / (a + i + δ_i) ≤ weight η / (a+1)`.

Thus each fiber has total weight at most `(2/(a+1)) * weight η`, and summing over
all fibers gives

`D_l^a(N+1) ≤ (2/(a+1)) D_l^a(N)`.

Iterating,

`D_l^a(N+j) ≤ (2/(a+1))^j D_l^a(N)`.

Finally, for `1 ≤ j < a`, AM-GM on `1,2,...,j` gives
`j! ≤ ((j+1)/2)^j`, so

`j! * (2/(a+1))^j ≤ ((j+1)/(a+1))^j ≤ 1`.

Therefore `j! * D_l^a(N+j) ≤ D_l^a(N)` for all `l,N` and `1 ≤ j < a`.
-/

end DInequality
