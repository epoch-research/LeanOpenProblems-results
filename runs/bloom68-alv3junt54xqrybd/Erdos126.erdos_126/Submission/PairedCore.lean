import FormalConjecturesUtil

/-!
Elementary data for weighted, disjoint paired classes.  The subsequent
combinatorial and quadratic-form arguments use this finite interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.Paired

structure Block (ι : Type*) where
  left : Finset ι
  right : Finset ι
  weight : ℝ

noncomputable def indicator {ι : Type*} (s : Finset ι) (i : ι) : ℝ := by
  classical
  exact if i ∈ s then 1 else 0

noncomputable def Block.diag {ι : Type*} (b : Block ι) (i j : ι) : ℝ :=
  b.weight * (indicator b.left i * indicator b.left j +
    indicator b.right i * indicator b.right j)

noncomputable def Block.cross {ι : Type*} (b : Block ι) (i j : ι) : ℝ :=
  b.weight * (indicator b.left i * indicator b.right j +
    indicator b.right i * indicator b.left j)

noncomputable def Block.gram {ι : Type*} (b : Block ι) (i j : ι) : ℝ :=
  b.diag i j - b.cross i j

def Block.Valid {ι : Type*} (b : Block ι) : Prop :=
  b.left.Nonempty ∧ b.right.Nonempty ∧
    (∀ i, i ∈ b.left → i ∉ b.right) ∧ 0 ≤ b.weight

def Block.Balanced {ι : Type*} (c : ℕ) (b : Block ι) : Prop :=
  b.left.card ≤ c * b.right.card ∧ b.right.card ≤ c * b.left.card

/-- Coherent laminarity records containment of both oriented sides, not
merely containment of their intersections on one side. -/
def Coherent {ι τ : Type*} (b : τ → Block ι) (u : Finset τ) : Prop :=
  ∀ t ∈ u, ∀ v ∈ u,
    ((b t).left ⊆ (b v).left ∧ (b t).right ⊆ (b v).right) ∨
    ((b v).left ⊆ (b t).left ∧ (b v).right ⊆ (b t).right) ∨
    (∀ i, (i ∈ (b t).left ∨ i ∈ (b t).right) →
      i ∉ (b v).left ∧ i ∉ (b v).right)

noncomputable def qform {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * K i j

def PSD {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) : Prop :=
  ∀ x, 0 ≤ qform K x

def CND {ι : Type*} [Fintype ι] (K : ι → ι → ℝ) : Prop :=
  ∀ x, (∑ i, x i) = 0 → qform K x ≤ 0

noncomputable def crossSum {ι τ : Type*} [Fintype τ]
    (b : τ → Block ι) (i j : ι) : ℝ :=
  ∑ t, (b t).cross i j

noncomputable def diagSum {ι τ : Type*} [Fintype τ]
    (b : τ → Block ι) (i j : ι) : ℝ :=
  ∑ t, (b t).diag i j

noncomputable def gramSum {ι τ : Type*} [Fintype τ]
    (b : τ → Block ι) (i j : ι) : ℝ :=
  diagSum b i j - crossSum b i j

end Erdos126Aux.Paired
