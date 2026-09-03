import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Discrete stream functions on the integer grid

For integer-valued currents with
`Jx x y - Jx (x - 1) y + Jy x y - Jy x (y - 1) = 0`, this file constructs the
unique normalized stream function with forward differences
`H (x + 1) y - H x y = Jy (x + 1) y` and
`H x (y + 1) - H x y = -Jx x (y + 1)`.

The construction is explicit: integrate `Jy` along the horizontal axis, then
integrate `-Jx` along each vertical column. Integer recursion handles negative
coordinates as well as positive ones. No support, finiteness, or topological
hypothesis is needed. For currents periodic in both coordinates, the stream
function is affine-periodic; its period increments are the finite flux sums
`ν = ∑ t ∈ range M, Jy (t + 1) 0` and `-μ = -∑ t ∈ range M, Jx 0 (t + 1)`.

This is partial infrastructure for finite Gaussian-moat / wall certificates,
not a Gaussian-moat proof. It neither imports `Submission.Spec` nor uses a
Jordan curve theorem.
-/

namespace Erdos952.DiscreteStream

open scoped BigOperators

/-! ## Integer antiderivatives and telescoping -/

/-- The normalized integer antiderivative of `f`. Starting at zero, add `f k`
when stepping from `k` to `k + 1`, and subtract `f (k - 1)` when stepping from
`k` to `k - 1`. This is a definition by integer recursion, not a chosen witness. -/
def intPrimitive (f : ℤ → ℤ) (z : ℤ) : ℤ :=
  Int.inductionOn' (motive := fun _ => ℤ) z 0 0
    (fun k _ a => a + f k) (fun k _ a => a - f (k - 1))

@[simp] theorem intPrimitive_zero (f : ℤ → ℤ) : intPrimitive f 0 = 0 := by
  unfold intPrimitive
  exact Int.inductionOn'_self

/-- The forward difference of the primitive is `f`, at every integer. -/
theorem intPrimitive_step (f : ℤ → ℤ) (z : ℤ) :
    intPrimitive f (z + 1) - intPrimitive f z = f z := by
  by_cases hz : 0 ≤ z
  · unfold intPrimitive
    rw [Int.inductionOn'_add_one hz]
    omega
  · have hpred : intPrimitive f ((z + 1) - 1) =
        intPrimitive f (z + 1) - f ((z + 1) - 1) := by
      unfold intPrimitive
      rw [Int.inductionOn'_sub_one (by omega : z + 1 ≤ 0)]
    simp only [add_sub_cancel_right] at hpred
    omega

/-- Every integer-valued function on the integers has a normalized
integer-valued antiderivative. -/
theorem exists_intPrimitive (f : ℤ → ℤ) :
    ∃ F : ℤ → ℤ, F 0 = 0 ∧ ∀ z : ℤ, F (z + 1) - F z = f z :=
  ⟨intPrimitive f, intPrimitive_zero f, intPrimitive_step f⟩

/-- Equal forward differences and one equal value determine a function on all
of `ℤ`. The predecessor step is essential for negative integers. -/
theorem eq_of_forward_diff_eq {F G : ℤ → ℤ}
    (hstep : ∀ z : ℤ, F (z + 1) - F z = G (z + 1) - G z)
    (hzero : F 0 = G 0) : F = G := by
  funext z
  refine Int.inductionOn' z 0 hzero ?_ ?_
  · intro k _ hk
    have hs := hstep k
    omega
  · intro k _ hk
    have hs := hstep (k - 1)
    simp only [sub_add_cancel] at hs
    omega

/-- A function with zero forward difference is constant on all integers. -/
theorem constant_of_forward_diff_zero {F : ℤ → ℤ}
    (hstep : ∀ z : ℤ, F (z + 1) - F z = 0) (z : ℤ) : F z = F 0 := by
  have heq : F = fun _ => F 0 := eq_of_forward_diff_eq
    (by intro k; simpa only [sub_self] using hstep k) rfl
  exact congrFun heq z

/-- Uniqueness of the normalized integer antiderivative. -/
theorem intPrimitive_unique {f F : ℤ → ℤ}
    (hzero : F 0 = 0) (hstep : ∀ z : ℤ, F (z + 1) - F z = f z) :
    F = intPrimitive f := by
  apply eq_of_forward_diff_eq
  · intro z
    exact (hstep z).trans (intPrimitive_step f z).symm
  · simpa only [intPrimitive_zero] using hzero

/-- Telescoping over any finite forward interval, including intervals starting
at negative integers. -/
theorem sub_eq_sum_of_forward_diff {F f : ℤ → ℤ}
    (hstep : ∀ z : ℤ, F (z + 1) - F z = f z) (x : ℤ) (n : ℕ) :
    F (x + (n : ℤ)) - F x = ∑ t ∈ Finset.range n, f (x + (t : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Int.natCast_succ, ← add_assoc, Finset.sum_range_succ]
      have hs := hstep (x + (n : ℤ))
      omega

/-- Finite-sum formula for the primitive at nonnegative integers. -/
theorem intPrimitive_nat (f : ℤ → ℤ) (n : ℕ) :
    intPrimitive f (n : ℤ) = ∑ t ∈ Finset.range n, f (t : ℤ) := by
  simpa using sub_eq_sum_of_forward_diff (intPrimitive_step f) 0 n

/-! ## Grid uniqueness -/

/-- Integer-valued functions on the vertices (or indexed edges) of the grid. -/
abbrev GridFunction := ℤ → ℤ → ℤ

/-- Two functions on the integer grid are determined by their two forward
differences and their value at the origin. -/
theorem grid_eq_of_forward_diffs_eq {F G : GridFunction}
    (hx : ∀ x y : ℤ, F (x + 1) y - F x y = G (x + 1) y - G x y)
    (hy : ∀ x y : ℤ, F x (y + 1) - F x y = G x (y + 1) - G x y)
    (hzero : F 0 0 = G 0 0) : F = G := by
  have haxis : (fun x => F x 0) = fun x => G x 0 :=
    eq_of_forward_diff_eq (fun x => hx x 0) hzero
  funext x y
  exact congrFun (eq_of_forward_diff_eq (hy x) (congrFun haxis x)) y

/-- A function whose two grid differences vanish is constant. -/
theorem grid_constant_of_forward_diffs_zero {F : GridFunction}
    (hx : ∀ x y : ℤ, F (x + 1) y - F x y = 0)
    (hy : ∀ x y : ℤ, F x (y + 1) - F x y = 0) (x y : ℤ) :
    F x y = F 0 0 := by
  have heq : F = fun _ _ => F 0 0 := grid_eq_of_forward_diffs_eq
    (by intro a b; simpa only [sub_self] using hx a b)
    (by intro a b; simpa only [sub_self] using hy a b) rfl
  exact congrFun (congrFun heq x) y

/-! ## The explicit discrete Poincaré construction -/

/-- Vanishing backward discrete divergence, with the indexing and signs in
the statement of the discrete Poincaré lemma below. -/
def DivergenceFree (Jx Jy : GridFunction) : Prop :=
  ∀ x y : ℤ, Jx x y - Jx (x - 1) y + Jy x y - Jy x (y - 1) = 0

/-- The two prescribed forward differences of a stream function. Normalization
is kept separate, so the notion is invariant under adding a constant. -/
structure IsStreamFunction (Jx Jy H : GridFunction) : Prop where
  dx : ∀ x y : ℤ, H (x + 1) y - H x y = Jy (x + 1) y
  dy : ∀ x y : ℤ, H x (y + 1) - H x y = -Jx x (y + 1)

/-- `A(x)`: the primitive of `x ↦ Jy (x + 1) 0` on the horizontal axis. -/
def axisPrimitive (Jy : GridFunction) (x : ℤ) : ℤ :=
  intPrimitive (fun t => Jy (t + 1) 0) x

/-- `B_x(y)`: the primitive of `y ↦ -Jx x (y + 1)` on the column at `x`. -/
def columnPrimitive (Jx : GridFunction) (x y : ℤ) : ℤ :=
  intPrimitive (fun t => -Jx x (t + 1)) y

/-- The explicit stream function `H(x,y) = A(x) + B_x(y)`. -/
def streamFunction (Jx Jy : GridFunction) (x y : ℤ) : ℤ :=
  axisPrimitive Jy x + columnPrimitive Jx x y

@[simp] theorem axisPrimitive_zero (Jy : GridFunction) : axisPrimitive Jy 0 = 0 :=
  intPrimitive_zero _

@[simp] theorem columnPrimitive_zero (Jx : GridFunction) (x : ℤ) :
    columnPrimitive Jx x 0 = 0 :=
  intPrimitive_zero _

theorem axisPrimitive_step (Jy : GridFunction) (x : ℤ) :
    axisPrimitive Jy (x + 1) - axisPrimitive Jy x = Jy (x + 1) 0 :=
  intPrimitive_step _ x

theorem columnPrimitive_step (Jx : GridFunction) (x y : ℤ) :
    columnPrimitive Jx x (y + 1) - columnPrimitive Jx x y = -Jx x (y + 1) :=
  intPrimitive_step _ y

@[simp] theorem streamFunction_axis (Jx Jy : GridFunction) (x : ℤ) :
    streamFunction Jx Jy x 0 = axisPrimitive Jy x := by
  simp only [streamFunction, columnPrimitive_zero, add_zero]

@[simp] theorem streamFunction_zero (Jx Jy : GridFunction) :
    streamFunction Jx Jy 0 0 = 0 := by
  simp only [streamFunction_axis, axisPrimitive_zero]

/-- The vertical difference holds without any divergence assumption. -/
theorem streamFunction_dy (Jx Jy : GridFunction) (x y : ℤ) :
    streamFunction Jx Jy x (y + 1) - streamFunction Jx Jy x y = -Jx x (y + 1) := by
  have hs := columnPrimitive_step Jx x y
  dsimp only [streamFunction]
  omega

/-- Vanishing divergence forces the horizontal difference: its vertical
difference agrees with that of `Jy (x + 1)`, and it agrees on the axis. -/
theorem streamFunction_dx (Jx Jy : GridFunction) (hdiv : DivergenceFree Jx Jy)
    (x y : ℤ) :
    streamFunction Jx Jy (x + 1) y - streamFunction Jx Jy x y = Jy (x + 1) y := by
  have heq : (fun t => streamFunction Jx Jy (x + 1) t - streamFunction Jx Jy x t) =
      Jy (x + 1) := by
    apply eq_of_forward_diff_eq
    · intro t
      have hright := streamFunction_dy Jx Jy (x + 1) t
      have hleft := streamFunction_dy Jx Jy x t
      have hd := hdiv (x + 1) (t + 1)
      simp only [add_sub_cancel_right] at hd
      omega
    · simpa only [streamFunction_axis] using axisPrimitive_step Jy x
  exact congrFun heq y

/-- The explicitly constructed function has the requested stream gradients. -/
theorem streamFunction_spec (Jx Jy : GridFunction) (hdiv : DivergenceFree Jx Jy) :
    IsStreamFunction Jx Jy (streamFunction Jx Jy) :=
  ⟨streamFunction_dx Jx Jy hdiv, streamFunction_dy Jx Jy⟩

/-- Discrete Poincaré lemma for divergence-free integer grid currents, with all
coordinates in `ℤ` and with the normalization `H 0 0 = 0`. -/
theorem discrete_poincare (Jx Jy : ℤ → ℤ → ℤ)
    (hdiv : ∀ x y : ℤ, Jx x y - Jx (x - 1) y + Jy x y - Jy x (y - 1) = 0) :
    ∃ H : ℤ → ℤ → ℤ, H 0 0 = 0 ∧
      (∀ x y : ℤ, H (x + 1) y - H x y = Jy (x + 1) y) ∧
      (∀ x y : ℤ, H x (y + 1) - H x y = -Jx x (y + 1)) :=
  ⟨streamFunction Jx Jy, streamFunction_zero Jx Jy,
    streamFunction_dx Jx Jy hdiv, streamFunction_dy Jx Jy⟩

/-- Stream functions for the same current with the same value at the origin
are equal everywhere. -/
theorem streamFunction_unique {Jx Jy H K : GridFunction}
    (hH : IsStreamFunction Jx Jy H) (hK : IsStreamFunction Jx Jy K)
    (hzero : H 0 0 = K 0 0) : H = K :=
  grid_eq_of_forward_diffs_eq
    (fun x y => (hH.dx x y).trans (hK.dx x y).symm)
    (fun x y => (hH.dy x y).trans (hK.dy x y).symm) hzero

/-- Existence and uniqueness of the normalized stream function. -/
theorem existsUnique_streamFunction (Jx Jy : GridFunction)
    (hdiv : DivergenceFree Jx Jy) :
    ∃! H : GridFunction, H 0 0 = 0 ∧ IsStreamFunction Jx Jy H := by
  refine ⟨streamFunction Jx Jy,
    ⟨streamFunction_zero Jx Jy, streamFunction_spec Jx Jy hdiv⟩, ?_⟩
  intro H hH
  exact streamFunction_unique hH.2 (streamFunction_spec Jx Jy hdiv)
    (hH.1.trans (streamFunction_zero Jx Jy).symm)

/-! ## Translations and affine periodicity -/

/-- If both current components are invariant under a translation, the stream
function changes by a constant under that translation. No normalization of
`H` is required. This applies to arbitrary integer translation vectors. -/
theorem translation_increment_constant {Jx Jy H : GridFunction}
    (hH : IsStreamFunction Jx Jy H) (a b : ℤ)
    (hJx : ∀ x y : ℤ, Jx (x + a) (y + b) = Jx x y)
    (hJy : ∀ x y : ℤ, Jy (x + a) (y + b) = Jy x y) (x y : ℤ) :
    H (x + a) (y + b) - H x y = H a b - H 0 0 := by
  let D : GridFunction := fun x y => H (x + a) (y + b) - H x y
  have hx : ∀ x y : ℤ, D (x + 1) y - D x y = 0 := by
    intro x y
    have hshift := hH.dx (x + a) (y + b)
    have hbase := hH.dx x y
    simp only [add_right_comm x a 1, hJy] at hshift
    dsimp only [D]
    omega
  have hy : ∀ x y : ℤ, D x (y + 1) - D x y = 0 := by
    intro x y
    have hshift := hH.dy (x + a) (y + b)
    have hbase := hH.dy x y
    simp only [add_right_comm y b 1, hJx] at hshift
    dsimp only [D]
    omega
  simpa only [D, zero_add] using grid_constant_of_forward_diffs_zero hx hy x y

/-- A current component has period `M` in each coordinate. Period lengths are
natural numbers because the flux constants below are sums over `range M`.
The results also hold for `M = 0`, hence in particular for every `M > 0`. -/
def PeriodicCurrent (J : GridFunction) (M : ℕ) : Prop :=
  (∀ x y : ℤ, J (x + (M : ℤ)) y = J x y) ∧
  (∀ x y : ℤ, J x (y + (M : ℤ)) = J x y)

/-- The flux `ν = ∑ t ∈ range M, Jy (t + 1) 0`, giving the horizontal
increment of a stream function over one period. -/
def nu (Jy : GridFunction) (M : ℕ) : ℤ :=
  ∑ t ∈ Finset.range M, Jy ((t : ℤ) + 1) 0

/-- The flux `μ = ∑ t ∈ range M, Jx 0 (t + 1)`; the vertical increment of a
stream function over one period is its negative. -/
def mu (Jx : GridFunction) (M : ℕ) : ℤ :=
  ∑ t ∈ Finset.range M, Jx 0 ((t : ℤ) + 1)

/-- The horizontal period increment is the same at every grid point, and is
exactly the finite flux sum `ν`. -/
theorem period_increment_x {Jx Jy H : GridFunction}
    (hH : IsStreamFunction Jx Jy H) (M : ℕ)
    (hJx : PeriodicCurrent Jx M) (hJy : PeriodicCurrent Jy M) (x y : ℤ) :
    H (x + (M : ℤ)) y - H x y = nu Jy M := by
  have hc := translation_increment_constant hH (M : ℤ) 0
    (by intro s t; simpa only [add_zero] using hJx.1 s t)
    (by intro s t; simpa only [add_zero] using hJy.1 s t) x y
  calc
    H (x + (M : ℤ)) y - H x y = H (M : ℤ) 0 - H 0 0 := by
      simpa only [add_zero] using hc
    _ = nu Jy M := by
      simpa only [zero_add, nu] using
        sub_eq_sum_of_forward_diff (F := fun t => H t 0)
          (f := fun t => Jy (t + 1) 0) (fun t => hH.dx t 0) 0 M

/-- The vertical period increment is the same at every grid point, and is
exactly the negative of the finite flux sum `μ`. -/
theorem period_increment_y {Jx Jy H : GridFunction}
    (hH : IsStreamFunction Jx Jy H) (M : ℕ)
    (hJx : PeriodicCurrent Jx M) (hJy : PeriodicCurrent Jy M) (x y : ℤ) :
    H x (y + (M : ℤ)) - H x y = -mu Jx M := by
  have hc := translation_increment_constant hH 0 (M : ℤ)
    (by intro s t; simpa only [add_zero] using hJx.2 s t)
    (by intro s t; simpa only [add_zero] using hJy.2 s t) x y
  calc
    H x (y + (M : ℤ)) - H x y = H 0 (M : ℤ) - H 0 0 := by
      simpa only [add_zero] using hc
    _ = -mu Jx M := by
      simpa only [zero_add, Finset.sum_neg_distrib, mu] using
        sub_eq_sum_of_forward_diff (fun t => hH.dy 0 t) 0 M

/-- Every stream function of a doubly periodic current is affine-periodic,
with the prescribed flux constants. Positivity of `M` is not needed. -/
theorem affine_periodicity {Jx Jy H : GridFunction}
    (hH : IsStreamFunction Jx Jy H) (M : ℕ)
    (hJx : PeriodicCurrent Jx M) (hJy : PeriodicCurrent Jy M) :
    (∀ x y : ℤ, H (x + (M : ℤ)) y - H x y = nu Jy M) ∧
    (∀ x y : ℤ, H x (y + (M : ℤ)) - H x y = -mu Jx M) :=
  ⟨period_increment_x hH M hJx hJy, period_increment_y hH M hJx hJy⟩

/-- Affine periodicity of the explicit normalized construction. -/
theorem streamFunction_affine_periodicity (Jx Jy : GridFunction)
    (hdiv : DivergenceFree Jx Jy) (M : ℕ)
    (hJx : PeriodicCurrent Jx M) (hJy : PeriodicCurrent Jy M) :
    (∀ x y : ℤ, streamFunction Jx Jy (x + (M : ℤ)) y -
      streamFunction Jx Jy x y = nu Jy M) ∧
    (∀ x y : ℤ, streamFunction Jx Jy x (y + (M : ℤ)) -
      streamFunction Jx Jy x y = -mu Jx M) :=
  affine_periodicity (streamFunction_spec Jx Jy hdiv) M hJx hJy

/-- Discrete Poincaré lemma with affine periodicity, displaying the finite sums
and all gradient equations explicitly. This includes every positive natural
period `M` (and also the harmless case `M = 0`). -/
theorem discrete_poincare_periodic (Jx Jy : ℤ → ℤ → ℤ)
    (hdiv : ∀ x y : ℤ, Jx x y - Jx (x - 1) y + Jy x y - Jy x (y - 1) = 0)
    (M : ℕ) (hJx : PeriodicCurrent Jx M) (hJy : PeriodicCurrent Jy M) :
    ∃ H : ℤ → ℤ → ℤ, H 0 0 = 0 ∧
      (∀ x y : ℤ, H (x + 1) y - H x y = Jy (x + 1) y) ∧
      (∀ x y : ℤ, H x (y + 1) - H x y = -Jx x (y + 1)) ∧
      (∀ x y : ℤ, H (x + (M : ℤ)) y - H x y =
        ∑ t ∈ Finset.range M, Jy ((t : ℤ) + 1) 0) ∧
      (∀ x y : ℤ, H x (y + (M : ℤ)) - H x y =
        -(∑ t ∈ Finset.range M, Jx 0 ((t : ℤ) + 1))) :=
  ⟨streamFunction Jx Jy, streamFunction_zero Jx Jy,
    streamFunction_dx Jx Jy hdiv, streamFunction_dy Jx Jy,
    period_increment_x (streamFunction_spec Jx Jy hdiv) M hJx hJy,
    period_increment_y (streamFunction_spec Jx Jy hdiv) M hJx hJy⟩

end Erdos952.DiscreteStream
