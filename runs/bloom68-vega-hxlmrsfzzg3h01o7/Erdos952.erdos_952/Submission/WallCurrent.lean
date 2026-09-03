import FormalConjecturesUtil

/-!
# Finite-quotient currents of nearest-neighbor black walks

A black nearest-neighbor walk in the Gaussian integers gives an integer current
on any finite additive quotient through which blackness factors. The current's
backward divergence is the difference of the endpoint deltas, its two total
fluxes are the two coordinates of the displacement, and all four currents
incident to a white vertex vanish.

East/north edges contribute a positive delta at their starting residue;
west/south edges contribute a negative delta at their ending residue. Currents
add under concatenation. A reflexive walk has zero current, even when its lone
vertex is white. No surjectivity of the residue homomorphism is required.

This is partial infrastructure for a stream-function obstruction, not a proof
of the Gaussian moat conjecture. It does not import `Submission.Spec` or use a
topological separation theorem.
-/

namespace Erdos952.WallCurrent

open scoped BigOperators

/-- The underlying square lattice. -/
abbrev G := GaussianInt

/-- The eastward unit vector. -/
abbrev e1 : G := 1

/-- The northward unit vector. -/
def e2 : G := ⟨0, 1⟩

@[simp] theorem e2_re : e2.re = 0 := rfl
@[simp] theorem e2_im : e2.im = 1 := rfl

/-- A nearest-neighbor step with both endpoints black. -/
def BlackStep (B : G → Prop) (p q : G) : Prop :=
  B p ∧ B q ∧ (q - p).norm = 1

/-- Squared Gaussian norm one means one of the four unit directions. -/
theorem norm_one_directions {z : G} (hz : z.norm = 1) :
    z = 1 ∨ z = -1 ∨ z = e2 ∨ z = -e2 := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Zsqrtd.norm, pow_two] using hz
  have hre : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.im]
  have him : -1 ≤ z.im ∧ z.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg z.re]
  obtain ⟨hrl, hru⟩ := hre
  obtain ⟨hil, hiu⟩ := him
  interval_cases hr : z.re <;> interval_cases hi : z.im <;>
    norm_num [hr, hi] at hn <;>
    simp [hr, hi, e2, Zsqrtd.ext_iff]

/-- Vertex form of the four-direction classification, with negative edges
written as reversals of positive edges. -/
theorem step_directions {p q : G} (h : (q - p).norm = 1) :
    q = p + 1 ∨ p = q + 1 ∨ q = p + e2 ∨ p = q + e2 := by
  have forward {a b d : G} (hd : b - a = d) : b = a + d := by
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = a + d := by rw [hd, add_comm]
  rcases norm_one_directions h with hd | hd | hd | hd
  · exact Or.inl (forward hd)
  · have hd' : p - q = 1 := by
      simpa only [neg_sub, neg_neg] using congrArg Neg.neg hd
    exact Or.inr (Or.inl (forward hd'))
  · exact Or.inr (Or.inr (Or.inl (forward hd)))
  · have hd' : p - q = e2 := by
      simpa only [neg_sub, neg_neg] using congrArg Neg.neg hd
    exact Or.inr (Or.inr (Or.inr (forward hd')))

section Delta

variable {α : Type*}

/-- Integer-valued Kronecker delta, with no decidable-equality assumption on
its index type. -/
noncomputable def delta (a b : α) : ℤ := by
  classical
  exact if a = b then 1 else 0

@[simp] theorem delta_self (a : α) : delta a a = 1 := by
  classical
  simp [delta]

@[simp] theorem delta_of_ne {a b : α} (h : a ≠ b) : delta a b = 0 := by
  classical
  simp [delta, h]

@[simp] theorem sum_delta [Fintype α] (a : α) : ∑ b : α, delta a b = 1 := by
  classical
  simp [delta]

variable [AddCommGroup α]

/-- Translating the argument of a residue delta translates its center in the
opposite direction. This also holds when a unit direction dies in the quotient. -/
theorem delta_sub (r : G →+ α) (p u d : G) :
    delta (r p) (r (u - d)) = delta (r (p + d)) (r u) := by
  classical
  simp only [delta, map_sub, map_add, eq_sub_iff_add_eq]

/-- A delta centered at a black residue vanishes at every white vertex. -/
theorem delta_eq_zero_of_white (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p u : G} (hp : B p) (hu : ¬ B u) : delta (r p) (r u) = 0 := by
  exact delta_of_ne (fun h => hu (hB p u h hp))

end Delta

section Currents

variable {α : Type*} [AddCommGroup α] [Fintype α]

/-- Backward divergence of a quotient current, pulled back to the lattice.
`Cx (r u)` indexes the east edge from `u`, and `Cy (r u)` the north edge. -/
def divergence (r : G →+ α) (Cx Cy : α → ℤ) (u : G) : ℤ :=
  Cx (r u) - Cx (r (u - 1)) + Cy (r u) - Cy (r (u - e2))

/-- All four currents incident to every white lattice vertex vanish. -/
def WhiteZero (r : G →+ α) (B : G → Prop) (Cx Cy : α → ℤ) : Prop :=
  ∀ u : G, ¬ B u →
    Cx (r u) = 0 ∧ Cx (r (u - 1)) = 0 ∧
      Cy (r u) = 0 ∧ Cy (r (u - e2)) = 0

/-- The divergence, total fluxes, and white-vertex support conditions of a
current representing a path from `p` to `q`. -/
structure IsPathCurrent (r : G →+ α) (B : G → Prop) (p q : G)
    (Cx Cy : α → ℤ) : Prop where
  div : ∀ u : G, divergence r Cx Cy u = delta (r p) (r u) - delta (r q) (r u)
  totalX : (∑ a : α, Cx a) = (q - p).re
  totalY : (∑ a : α, Cy a) = (q - p).im
  white : WhiteZero r B Cx Cy

namespace IsPathCurrent

variable {r : G →+ α} {B : G → Prop} {p q t : G}
variable {Cx Cy Dx Dy : α → ℤ}

/-- The empty path has zero current. In particular, `B p` is not needed. -/
theorem zero (r : G →+ α) (B : G → Prop) (p : G) :
    IsPathCurrent r B p p (fun _ => 0) (fun _ => 0) := by
  constructor <;> simp [divergence, WhiteZero]

/-- Add currents when concatenating paths. -/
theorem add (hC : IsPathCurrent r B p q Cx Cy)
    (hD : IsPathCurrent r B q t Dx Dy) :
    IsPathCurrent r B p t (fun a => Cx a + Dx a) (fun a => Cy a + Dy a) := by
  constructor
  · intro u
    have hCu := hC.div u
    have hDu := hD.div u
    dsimp only [divergence] at hCu hDu ⊢
    omega
  · rw [Finset.sum_add_distrib, hC.totalX, hD.totalX]
    simp only [Zsqrtd.re_sub]
    omega
  · rw [Finset.sum_add_distrib, hC.totalY, hD.totalY]
    simp only [Zsqrtd.im_sub]
    omega
  · intro u hu
    obtain ⟨hCx, hCx', hCy, hCy'⟩ := hC.white u hu
    obtain ⟨hDx, hDx', hDy, hDy'⟩ := hD.white u hu
    simp only [hCx, hCx', hCy, hCy', hDx, hDx', hDy, hDy', add_zero,
      and_self]

/-- Reversing a current negates it. Applied to an east/north edge, this is a
negative delta at the ending residue of the resulting west/south edge. -/
theorem neg (hC : IsPathCurrent r B p q Cx Cy) :
    IsPathCurrent r B q p (fun a => -Cx a) (fun a => -Cy a) := by
  constructor
  · intro u
    have hCu := hC.div u
    dsimp only [divergence] at hCu ⊢
    omega
  · rw [Finset.sum_neg_distrib, hC.totalX]
    simp only [Zsqrtd.re_sub]
    omega
  · rw [Finset.sum_neg_distrib, hC.totalY]
    simp only [Zsqrtd.im_sub]
    omega
  · intro u hu
    obtain ⟨hCx, hCx', hCy, hCy'⟩ := hC.white u hu
    simp only [hCx, hCx', hCy, hCy', neg_zero, and_self]

/-- Equal endpoint residues cancel the two boundary deltas. -/
theorem divergence_eq_zero (hC : IsPathCurrent r B p q Cx Cy)
    (hpq : r p = r q) (u : G) : divergence r Cx Cy u = 0 := by
  rw [hC.div, hpq, sub_self]

end IsPathCurrent

/-- A single eastward black edge carries one unit of horizontal current at
its starting residue. -/
theorem east_current (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p : G} (hp : B p) (hp1 : B (p + 1)) :
    IsPathCurrent r B p (p + 1) (delta (r p)) (fun _ => 0) := by
  constructor
  · intro u
    simp only [divergence, add_zero, sub_zero, delta_sub]
  · simp
  · simp
  · intro u hu
    refine ⟨delta_eq_zero_of_white r hB hp hu, ?_, rfl, rfl⟩
    rw [delta_sub]
    exact delta_eq_zero_of_white r hB hp1 hu

/-- A single northward black edge carries one unit of vertical current at
its starting residue. -/
theorem north_current (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p : G} (hp : B p) (hp2 : B (p + e2)) :
    IsPathCurrent r B p (p + e2) (fun _ => 0) (delta (r p)) := by
  constructor
  · intro u
    simp only [divergence, sub_self, zero_add, delta_sub]
  · simp
  · simp
  · intro u hu
    refine ⟨rfl, rfl, delta_eq_zero_of_white r hB hp hu, ?_⟩
    rw [delta_sub]
    exact delta_eq_zero_of_white r hB hp2 hu

/-- Construct the current of a single nearest-neighbor black step. -/
theorem exists_stepCurrent (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p q : G} (hstep : BlackStep B p q) :
    ∃ Cx Cy : α → ℤ, IsPathCurrent r B p q Cx Cy := by
  obtain ⟨hp, hq, hn⟩ := hstep
  rcases step_directions hn with h | h | h | h
  · subst q
    exact ⟨_, _, east_current r hB hp hq⟩
  · subst p
    exact ⟨_, _, (east_current r hB hq hp).neg⟩
  · subst q
    exact ⟨_, _, north_current r hB hp hq⟩
  · subst p
    exact ⟨_, _, (north_current r hB hq hp).neg⟩

/-- Every finite nearest-neighbor black walk induces a current on the finite
residue group. The reflexive case does not assume its endpoint is black. -/
theorem exists_pathCurrent (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p q : G} (hpath : Relation.ReflTransGen (BlackStep B) p q) :
    ∃ Cx Cy : α → ℤ, IsPathCurrent r B p q Cx Cy := by
  induction hpath with
  | refl => exact ⟨_, _, IsPathCurrent.zero r B p⟩
  | tail _ hstep ih =>
      obtain ⟨Cx, Cy, hC⟩ := ih
      obtain ⟨Dx, Dy, hD⟩ := exists_stepCurrent r hB hstep
      exact ⟨_, _, hC.add hD⟩

/-- Expanded interface: divergence is the endpoint indicator difference,
total current equals displacement, and every white vertex has zero incident
currents. -/
theorem exists_quotient_current (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p q : G} (hpath : Relation.ReflTransGen (BlackStep B) p q) :
    ∃ Cx Cy : α → ℤ,
      (∀ u : G, Cx (r u) - Cx (r (u - 1)) + Cy (r u) - Cy (r (u - e2)) =
        delta (r p) (r u) - delta (r q) (r u)) ∧
      (∑ a : α, Cx a) = (q - p).re ∧
      (∑ a : α, Cy a) = (q - p).im ∧
      (∀ u : G, ¬ B u → Cx (r u) = 0 ∧ Cx (r (u - 1)) = 0 ∧
        Cy (r u) = 0 ∧ Cy (r (u - e2)) = 0) := by
  obtain ⟨Cx, Cy, hC⟩ := exists_pathCurrent r hB hpath
  exact ⟨Cx, Cy, hC.div, hC.totalX, hC.totalY, hC.white⟩

/-- For a walk with equal endpoint residues, the resulting current is
divergence-free, with the same displacement totals and white support. Equality
of the lattice endpoints themselves is not required. -/
theorem exists_divergenceFree_current (r : G →+ α) {B : G → Prop}
    (hB : ∀ u v, r u = r v → B u → B v)
    {p q : G} (hpath : Relation.ReflTransGen (BlackStep B) p q)
    (hpq : r p = r q) :
    ∃ Cx Cy : α → ℤ,
      (∀ u : G, Cx (r u) - Cx (r (u - 1)) + Cy (r u) - Cy (r (u - e2)) = 0) ∧
      (∑ a : α, Cx a) = (q - p).re ∧
      (∑ a : α, Cy a) = (q - p).im ∧
      (∀ u : G, ¬ B u → Cx (r u) = 0 ∧ Cx (r (u - 1)) = 0 ∧
        Cy (r u) = 0 ∧ Cy (r (u - e2)) = 0) := by
  obtain ⟨Cx, Cy, hC⟩ := exists_pathCurrent r hB hpath
  exact ⟨Cx, Cy, hC.divergence_eq_zero hpq, hC.totalX, hC.totalY, hC.white⟩

end Currents

end Erdos952.WallCurrent

#print axioms Erdos952.WallCurrent.norm_one_directions
#print axioms Erdos952.WallCurrent.exists_quotient_current
#print axioms Erdos952.WallCurrent.exists_divergenceFree_current
