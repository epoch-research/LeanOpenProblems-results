import Submission.PeriodicSieveComponents
import Submission.RationalStripObstruction

/-! A prime ray would force genuinely two-dimensional components at every finite
sieve cutoff, not merely an infinite component. This is a necessary condition,
not a proof that a successful cutoff exists. -/
namespace Erdos952Investigation
namespace RankTwoSieveNecessity

open FiniteSieveReduction PeriodicSieveComponents
set_option maxHeartbeats 0

def det (d e : GaussianInt) : ℤ := d.re*e.im-d.im*e.re

lemma det_sub_right (d z w : GaussianInt) : det d (z-w) = det d z-det d w := by
  simp only [det, Zsqrtd.re_sub, Zsqrtd.im_sub]
  ring

/-- Every finite coloring of a path with unbounded transverse projections has
two nonparallel same-color differences. -/
lemma independent_same_color_differences {A : Type*} [Finite A]
    (x : ℕ → GaussianInt) (hx : Function.Injective x) (f : ℕ → A)
    (hunbounded : ∀ d : GaussianInt, d ≠ 0 → ∀ B : ℕ,
      ∃ n, (B : ℤ) < |det d (x n)|) :
    ∃ i j k l : ℕ, f i = f j ∧ f k = f l ∧
      det (x j-x i) (x l-x k) ≠ 0 := by
  classical
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
  let d := x j-x i
  have hd : d ≠ 0 := by
    intro he
    exact hij (hx (sub_eq_zero.mp he)).symm
  suffices ∃ k l, f k = f l ∧ det d (x l-x k) ≠ 0 by
    obtain ⟨k,l,hkl,hdet⟩ := this
    exact ⟨i,j,k,l,hfij,hkl,hdet⟩
  by_contra! hline
  let rep : A → ℕ := fun a => if h : ∃ n, f n = a then Classical.choose h else 0
  have hrep (n : ℕ) : f (rep (f n)) = f n := by
    dsimp [rep]
    rw [dif_pos ⟨n,rfl⟩]
    exact Classical.choose_spec (show ∃ j, f j = f n from ⟨n,rfl⟩)
  have heq (n : ℕ) : det d (x n) = det d (x (rep (f n))) := by
    have hh := hline (rep (f n)) n (hrep n)
    rw [det_sub_right] at hh
    exact sub_eq_zero.mp hh
  have hfinite : (Set.range (fun n => |det d (x n)|)).Finite := by
    apply (Set.finite_range (fun a : A => |det d (x (rep a))|)).subset
    rintro v ⟨n,rfl⟩
    exact ⟨f n, congrArg abs (heq n).symm⟩
  obtain ⟨T,hT⟩ := hfinite.bddAbove
  obtain ⟨n,hn⟩ := hunbounded d hd T.natAbs
  have hu := hT (Set.mem_range_self n)
  have ht : T ≤ (T.natAbs : ℤ) := Int.le_natAbs
  omega

lemma reachable_period_at_base {C : ℤ} {N : ℕ} {z u v : GaussianInt}
    (hu : (sieveGraph C N).Reachable z u)
    (hv : (sieveGraph C N).Reachable z v)
    (hd : IsPeriod N (v-u)) :
    (sieveGraph C N).Reachable z (z+(v-u)) := by
  have ht := reachable_add_period hu hd
  have he : u+(v-u) = v := by abel
  rw [he] at ht
  exact hv.trans ht.symm

/-- A component with two independent period translations. -/
def HasRankTwoComponent (C : ℤ) (N : ℕ) : Prop :=
  ∃ z d e : GaussianInt, IsPeriod N d ∧ IsPeriod N e ∧
    (sieveGraph C N).Reachable z (z+d) ∧
    (sieveGraph C N).Reachable z (z+e) ∧ det d e ≠ 0

/-- Any hypothetical Gaussian-prime ray forces this stronger component
condition at every finite sieve cutoff. -/
theorem prime_ray_forces_rank_two_components (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) :
    ∀ N : ℕ, HasRankTwoComponent C N := by
  intro N
  obtain ⟨T,hT⟩ := injective_escapes_norm x hx ((N : ℤ)^2)
  let y : ℕ → GaussianInt := fun n => x (T+n)
  have hy : Function.Injective y := by
    intro i j he
    exact Nat.add_left_cancel (hx he)
  have hyp (n : ℕ) : Prime (y n) ∧ (y (n+1)-y n).norm < C := by
    simpa only [y, Nat.add_assoc] using h (T+n)
  have ha (n : ℕ) : Allowed N (y n) := by
    intro p hpN hp hdiv
    have hsmall := prime_norm_divisor_bound (hyp n).1 hp hdiv
    have hlarge := hT (T+n) (Nat.le_add_right _ _)
    have hpN' : (p : ℤ) ≤ N := by exact_mod_cast hpN
    have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg _
    change (N : ℤ)^2 < (y n).norm at hlarge
    nlinarith
  have hadj (n : ℕ) : (sieveGraph C N).Adj (y n) (y (n+1)) := by
    refine ⟨ha n, ha (n+1), ?_, (hyp n).2⟩
    intro he
    have := hy he
    omega
  have hr (n : ℕ) : (sieveGraph C N).Reachable (y 0) (y n) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (hadj n).reachable
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  have hproj (d : GaussianInt) (hd : d ≠ 0) (B : ℕ) :
      ∃ n, (B : ℤ) < |det d (y n)| := by
    have hcoeff : -d.im ≠ 0 ∨ d.re ≠ 0 := by
      by_contra! he
      exact hd (Zsqrtd.ext he.2 (neg_eq_zero.mp he.1))
    obtain ⟨n,_,hn⟩ := RationalStrip.rational_projection_unbounded y C hy hyp
      (-d.im) d.re hcoeff 0 B
    refine ⟨n, ?_⟩
    convert hn using 2 <;> dsimp [det] <;> ring
  obtain ⟨i,j,k,l,hij,hkl,hdet⟩ := independent_same_color_differences y hy
    (fun n => residue N (y n)) hproj
  have hd := period_of_same_residue hij
  have he := period_of_same_residue hkl
  exact ⟨y 0, y j-y i, y l-y k, hd, he,
    reachable_period_at_base (hr i) (hr j) hd,
    reachable_period_at_base (hr k) (hr l) he, hdet⟩

/-- Excluding rank-two components at a suitable cutoff for each step bound
would suffice for a full disproof. This cutoff hypothesis remains unproved. -/
theorem rank_two_obstruction_implies_disproof
    (hobstruction : ∀ C : ℤ, ∃ N : ℕ, ¬ HasRankTwoComponent C N) :
    ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C := by
  rintro ⟨x,C,hx,h⟩
  obtain ⟨N,hN⟩ := hobstruction C
  exact hN (prime_ray_forces_rank_two_components x C hx h N)

#print axioms independent_same_color_differences
#print axioms prime_ray_forces_rank_two_components
#print axioms rank_two_obstruction_implies_disproof

end RankTwoSieveNecessity
end Erdos952Investigation
