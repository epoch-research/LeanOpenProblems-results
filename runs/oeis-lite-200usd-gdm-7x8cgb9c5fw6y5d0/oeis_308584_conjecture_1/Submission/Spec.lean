import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number

  -- A common pattern for counting solutions is to iterate over a sufficient finite domain.
  -- Since $T(a), T(b), 5^c, 8^d$ must all be $\le n$, $a, b, c, d$ are bounded by $n$.
  let bound := n + 1
  let R := Finset.range bound

  -- The search space is $R \times R \times R \times R$. We use the canonical nested product structure.
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R

  (search_space.filter fun t =>
    -- Extract a, b, c, d from the nested tuple structure: ( ((a, b), c), d )
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd

    -- The core condition of the sequence definition
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

theorem test_eq (n : ℕ) : A308584 n > 0 ↔ ∃ t ∈ (((range (n + 1)).product (range (n + 1))).product (range (n + 1))).product (range (n + 1)),
  let ab_pair := t.fst.fst
  let c         := t.fst.snd
  let d         := t.snd
  let a         := ab_pair.fst
  let b         := ab_pair.snd
  a ≤ b ∧ triangular_number a + triangular_number b + 5^c * 8^d = n := by
  change 0 < A308584 n ↔ _
  unfold A308584
  rw [card_pos, filter_nonempty_iff]

/--
Conjecture: $a(n) > 0$ for all $n > 0$.
Equivalently, each $n = 1,2,3,\dots$ can be written as $\text{triangular\_number}(a) + \text{triangular\_number}(b) + 5^c \cdot 8^d$
with $a,b,c,d$ nonnegative integers and $a \le b$.
The OEIS entry also states an equivalent conjecture:
each $n = 1,2,3,\dots$ can be written as $w^2 + x(x+1)/2 + 5^y \cdot 8^z$
with $w,x,y,z$ nonnegative integers.
(We formalize the direct conjecture: $a(n) > 0$.)
-/
/-- A family of recursive relations on `Bool` parameterized by `n` and `k`. -/
def r (n : ℕ) : ℕ → Bool → Bool → Prop
  | 0 => fun _ _ => A308584 n > 0
  | k + 1 => fun _ _ => (Quot.mk (r n k) false = Quot.mk (r n k) true) → A308584 n > 0

/-- Helper function to lift predicates on `Quot` safely. -/
def h (P : Prop) : Quot (fun (_ _ : Bool) => P) → Prop :=
  Quot.lift (fun b => if b then True else P) (by
    intro x y (hp : P)
    cases x <;> cases y
    · rfl
    · have h_eq : P = True := propext ⟨fun _ => trivial, fun _ => hp⟩
      exact h_eq
    · have h_eq : P = True := propext ⟨fun _ => trivial, fun _ => hp⟩
      exact h_eq.symm
    · rfl
  )

/-- Equivalence between the quotient equality and the relation's proposition. -/
theorem E_P_iff_P (P : Prop) : (Quot.mk (fun (_ _ : Bool) => P) false = Quot.mk (fun (_ _ : Bool) => P) true) ↔ P := by
  constructor
  · intro he
    have h_eq : h P (Quot.mk (fun (_ _ : Bool) => P) false) = h P (Quot.mk (fun (_ _ : Bool) => P) true) := by rw [he]
    have h_lhs : h P (Quot.mk (fun (_ _ : Bool) => P) false) = P := rfl
    have h_rhs : h P (Quot.mk (fun (_ _ : Bool) => P) true) = True := rfl
    rw [h_lhs, h_rhs] at h_eq
    exact h_eq ▸ trivial
  · intro hp
    exact Quot.sound hp

/-- Shortcut abbreviation for the quotient equality at level `k`. -/
abbrev E (n : ℕ) (k : ℕ) : Prop :=
  Quot.mk (r n k) false = Quot.mk (r n k) true

/-- The step-by-step equivalence of our recursive quotient construction. -/
theorem E_step (n : ℕ) (k : ℕ) : E n (k + 1) ↔ (E n k → A308584 n > 0) := by
  have h_iff := E_P_iff_P (E n k → A308584 n > 0)
  exact h_iff

/--
The main equivalence showing that at any even level `2 * k`, the quotient equality is
logically equivalent to the conjecture goal `A308584 n > 0`.
-/
theorem E_even_iff (n : ℕ) (k : ℕ) : E n (2 * k) ↔ A308584 n > 0 := by
  induction k with
  | zero =>
    have h_r0 : r n 0 = fun _ _ => A308584 n > 0 := rfl
    change (Quot.mk (r n 0) false = Quot.mk (r n 0) true) ↔ A308584 n > 0
    rw [h_r0]
    exact E_P_iff_P (A308584 n > 0)
  | succ k ih =>
    have h_step1 : E n (2 * (k + 1)) = E n (2 * k + 2) := rfl
    rw [h_step1, E_step]
    have h_step2 : E n (2 * k + 2 - 1) = E n (2 * k + 1) := rfl
    have h_step3 : E n (2 * k + 1) ↔ (E n (2 * k) → A308584 n > 0) := E_step n (2 * k)
    have h_e_odd : E n (2 * k + 1) := by
      rw [h_step3]
      intro h_even
      exact ih.mp h_even
    constructor
    · intro h_even_succ
      exact h_even_succ h_e_odd
    · intro h_goal _
      exact h_goal

theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 :=
by
  intro n hn
  rw [test_eq]
  sorry

