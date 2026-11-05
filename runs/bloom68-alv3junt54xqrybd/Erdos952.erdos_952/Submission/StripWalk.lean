import Submission.CRTBarrier
import Submission.AxisWalk

/-!
# An all-bounds partial obstruction for Gaussian-prime walks in horizontal strips

This is a **partial Gaussian-moat result**: for every integer squared-step
bound `C` and every fixed finite strip bound `M`, an injective Gaussian-prime
sequence confined to `|im| ≤ M` cannot have all squared step norms below `C`.
It is stronger than the real-axis obstruction, and includes every fixed
horizontal line. It does **not** settle the unrestricted-plane Gaussian-moat
problem: a planar walk need not remain in any fixed horizontal strip.

Pairwise coprime Fermat norms and finite CRT supply prime-free vertical bands
on both sides of the starting real coordinate. Bounded real jumps cannot
cross these bands. The sequence would then be confined to a finite rectangle,
contradicting its injectivity. No monotonicity of the walk is assumed.
-/

namespace GaussianStripWalk

/--
**Partial Gaussian-moat result, for every bound:** no injective Gaussian-prime
walk confined to a fixed horizontal strip has uniformly bounded squared step
norms. Both `C` and `M` are arbitrary integers; negative bounds require no
special hypotheses. This theorem does not address walks in the full plane.
-/
theorem no_injective_prime_walk_in_horizontal_strip (x : ℕ → GaussianInt) (C M : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hstrip : ∀ n, |(x n).im| ≤ M) :
    ¬ (∀ n, (x (n + 1) - x n).norm < C) := by
  intro hstep
  let D : ℤ := C + 1
  obtain ⟨A, hstart, hbarrier⟩ :=
    GaussianCRTBarrier.exists_symmetric_prime_free_barriers D M (x 0).re
  let P : ℤ → Prop := fun a => ∃ z : GaussianInt, z.re = a ∧ Prime z ∧ |z.im| ≤ M
  have hprime : ∀ n, P (x n).re := fun n => ⟨x n, rfl, hp n, hstrip n⟩
  have hjump : ∀ n, |(x (n + 1)).re - (x n).re| ≤ D := by
    intro n
    exact GaussianAxisWalk.abs_re_sub_le_of_norm_lt (x n) (x (n + 1)) C (hstep n)
  have hforbidden : ∀ a : ℤ, A < |a| → |a| ≤ A + D → ¬ P a := by
    rintro a hlo hhi ⟨z, hzre, hzprime, hzim⟩
    exact hbarrier z (by simpa only [hzre] using hlo)
      (by simpa only [hzre] using hhi) hzim hzprime
  have htrapped : ∀ n, (x n).re ∈ Set.Icc (-A) A :=
    GaussianAxisWalk.mem_Icc_of_forbidden_barrier (fun n => (x n).re) A D
      (abs_le.mp hstart) hprime hjump hforbidden
  let coords : ℕ → ℤ × ℤ := fun n => ((x n).re, (x n).im)
  have hc : Function.Injective coords := by
    intro m n h
    apply hx
    apply Zsqrtd.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hbox : ∀ n, coords n ∈ Set.Icc (-A, -M) (A, M) := by
    intro n
    have hr := htrapped n
    have hi := abs_le.mp (hstrip n)
    exact ⟨⟨hr.1, hi.1⟩, ⟨hr.2, hi.2⟩⟩
  exact (Set.infinite_of_injective_forall_mem hc hbox) (Set.finite_Icc _ _)

/-- Squared steps of an injective prime sequence in a fixed strip are unbounded. -/
theorem exists_step_norm_ge_in_horizontal_strip (x : ℕ → GaussianInt) (M : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hstrip : ∀ n, |(x n).im| ≤ M) (C : ℤ) :
    ∃ n, C ≤ (x (n + 1) - x n).norm := by
  by_contra! h
  exact no_injective_prime_walk_in_horizontal_strip x C M hx hp hstrip h

/-- The same all-bounds partial obstruction for a nonstrict squared-step bound. -/
theorem no_injective_prime_walk_in_horizontal_strip_norm_le
    (x : ℕ → GaussianInt) (C M : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hstrip : ∀ n, |(x n).im| ≤ M) :
    ¬ (∀ n, (x (n + 1) - x n).norm ≤ C) := by
  intro hstep
  apply no_injective_prime_walk_in_horizontal_strip x (C + 1) M hx hp hstrip
  intro n
  exact lt_of_le_of_lt (hstep n) (by omega)

#print axioms no_injective_prime_walk_in_horizontal_strip
#print axioms exists_step_norm_ge_in_horizontal_strip
#print axioms no_injective_prime_walk_in_horizontal_strip_norm_le

end GaussianStripWalk
