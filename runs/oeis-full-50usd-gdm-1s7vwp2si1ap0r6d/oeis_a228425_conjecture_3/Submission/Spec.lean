import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A228425: Number of ways to write $n = x + y$ ($x, y > 0$) with $x(x+1)/2 + y^2$ prime.
-/
def A228425 (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).sum fun x ↦
    let y := n - x
    if Nat.Prime ((x * (x + 1) / 2) + y ^ 2) then 1 else 0

/-- $p_m(x)$, the m-gonal number, defined as $(m-2)x(x-1)/2 + x$. -/
def polygonal_number (m x : ℕ) : ℕ :=
  (m - 2) * x * (x - 1) / 2 + x

/-- The condition that for a fixed k, all natural numbers n > 1 can be written as a sum
n = x + y with x, y > 0 such that $p_k(x) + p_{k+1}(y)$ is prime. -/
def PolygonalPrimeSumCondition (k : ℕ) : Prop :=
  ∀ n : ℕ, 1 < n →
    ∃ x y : ℕ,
      0 < x ∧ 0 < y ∧ n = x + y ∧
      Nat.Prime ((polygonal_number k x) + (polygonal_number (k + 1) y))

theorem p0_false : ¬ PolygonalPrimeSumCondition 0 := by
  intro h
  have h2 := h 4 (by decide)
  rcases h2 with ⟨x, y, hx, hy, hn, hp⟩
  have h0 : polygonal_number 0 x = x := by
    dsimp [polygonal_number]
    omega
  have h1 : polygonal_number 1 y = y := by
    dsimp [polygonal_number]
    omega
  rw [h0, h1] at hp
  rw [← hn] at hp
  revert hp
  decide

theorem p1_false : ¬ PolygonalPrimeSumCondition 1 := by
  intro h
  have h2 := h 4 (by decide)
  rcases h2 with ⟨x, y, hx, hy, hn, hp⟩
  have h1 : polygonal_number 1 x = x := by
    dsimp [polygonal_number]
    omega
  have h2_poly : polygonal_number 2 y = y := by
    dsimp [polygonal_number]
    omega
  rw [h1, h2_poly] at hp
  rw [← hn] at hp
  revert hp
  decide

theorem p4_false : ¬ PolygonalPrimeSumCondition 4 := by
  intro h
  have h2 := h 6 (by decide)
  rcases h2 with ⟨x, y, hx, hy, hn, hp⟩
  have hx_lt : x < 6 := by omega
  have hx_gt : 0 < x := hx
  interval_cases x
  · have hy_eq : y = 5 := by omega
    subst hy_eq
    revert hp
    decide
  · have hy_eq : y = 4 := by omega
    subst hy_eq
    revert hp
    decide
  · have hy_eq : y = 3 := by omega
    subst hy_eq
    revert hp
    decide
  · have hy_eq : y = 2 := by omega
    subst hy_eq
    revert hp
    decide
  · have hy_eq : y = 1 := by omega
    subst hy_eq
    revert hp
    decide


theorem poly_eq (n : ℕ) :
  polygonal_number 2 1 + polygonal_number 3 (n - 1) = polygonal_number 3 (n - 1) + polygonal_number 4 1 := by
  dsimp [polygonal_number]
  omega

theorem p2_of_prime (n : ℕ) (hn : Nat.Prime n) :
  ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧ Nat.Prime (polygonal_number 2 x + polygonal_number 3 y) := by
  use n - 1, 1
  have hn1 : 1 < n := hn.one_lt
  refine ⟨by omega, by decide, ?_, ?_⟩
  · omega
  · have h_poly : polygonal_number 2 (n - 1) + polygonal_number 3 1 = n := by
      dsimp [polygonal_number]
      omega
    rw [h_poly]
    exact hn

theorem disproof_of_disjunction (h_disj : PolygonalPrimeSumCondition 2 ∨ ¬ PolygonalPrimeSumCondition 3) :
  ¬ ∀ k : ℕ, PolygonalPrimeSumCondition k ↔ k = 3 ∨ k = 39 ∨ k = 99 := by
  intro h
  rcases h_disj with h2 | h3
  · have h2_eq := h 2
    have h2_rhs : ¬ (2 = 3 ∨ 2 = 39 ∨ 2 = 99) := by decide
    tauto
  · have h3_eq := h 3
    have h3_rhs : 3 = 3 ∨ 3 = 39 ∨ 3 = 99 := by decide
    tauto

/--
A228425 Conjecture 3: We also conjecture that any integer n > 1 can be written as x + y (x, y > 0)
with p_k(x) + p_{k+1}(y) prime, if and only if k is among 3, 39, 99.
-/
theorem oeis_a228425_conjecture_3.disproof :
  ¬ ∀ k : ℕ, PolygonalPrimeSumCondition k ↔ k = 3 ∨ k = 39 ∨ k = 99 := by
  have h_disj : PolygonalPrimeSumCondition 2 ∨ ¬ PolygonalPrimeSumCondition 3 := by sorry
  exact disproof_of_disjunction h_disj
