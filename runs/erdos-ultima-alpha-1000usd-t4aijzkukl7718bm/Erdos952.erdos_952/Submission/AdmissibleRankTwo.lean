import Submission.RankTwoSieveNecessity
import Submission.UniformRationalStrip

/-! Rank-two components characterize admissible rays when required at every
finite cutoff. This strengthens the finite-sieve reduction, but does not
prove that a cutoff eliminating rank-two components exists. -/
namespace Erdos952Investigation
namespace AdmissibleRankTwo

open AdmissibleRay FiniteSieveReduction PeriodicSieveComponents
open RankTwoSieveNecessity UniformRationalStrip
set_option maxHeartbeats 0

lemma sieve_translate (y : ℕ → GaussianInt)
    (hg : ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)) (N : ℕ) :
    ∃ z : GaussianInt, ∀ n, Allowed N (z+y n) := by
  classical
  choose a b hab using hg
  obtain ⟨A,hA⟩ := prime_crt N a
  obtain ⟨B,hB⟩ := prime_crt N b
  refine ⟨⟨A,B⟩,?_⟩
  intro n p hpN hp hdiv
  have hgood : Good p (A : ZMod p) (B : ZMod p) (y n) := by
    rw [hA p hpN hp,hB p hpN hp]
    exact hab p hp n
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (⟨A,B⟩+y n).norm p).mpr hdiv
  apply hgood
  simpa [gaussian_norm_sq] using he

lemma good_add_translate (y : ℕ → GaussianInt)
    (hg : ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n))
    (z : GaussianInt) :
    ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (z+y n) := by
  intro p hp
  obtain ⟨a,b,hab⟩ := hg p hp
  refine ⟨a-z.re,b-z.im,?_⟩
  intro n
  simpa only [Good,Zsqrtd.re_add,Zsqrtd.im_add,Int.cast_add,
    ← add_assoc,sub_add_cancel] using hab n

lemma det_eq_im_mul (d z : GaussianInt) :
    det d z = ((⟨d.re,-d.im⟩ : GaussianInt)*z).im := by
  simp [det]
  ring

/-- No admissible bounded-step ray is confined to a rational strip. The CRT
translate used by the finite sieve does not alter its shape. -/
theorem admissible_projection_unbounded (y : ℕ → GaussianInt) (C : ℤ)
    (hy : Function.Injective y) (hs : ∀ n, (y (n+1)-y n).norm < C)
    (hg : ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n))
    (d : GaussianInt) (hd : d ≠ 0) (B : ℕ) :
    ∃ n, (B : ℤ) < |det d (y n)| := by
  by_contra! hb
  let dc : GaussianInt := ⟨d.re,-d.im⟩
  have hdc : dc ≠ 0 := by
    intro he
    have hr := congrArg Zsqrtd.re he
    have hi := congrArg Zsqrtd.im he
    apply hd
    apply Zsqrtd.ext
    · exact hr
    · simpa [dc] using hi
  obtain ⟨P,hP,R,hR⟩ := uniform_sieve_strip_bound dc hdc C (2*B)
  obtain ⟨z,hz⟩ := sieve_translate y hg P
  let x : ℕ → GaussianInt := fun n => z+y n
  have hx (n : ℕ) : x n-x 0 = y n-y 0 := by simp [x]
  have hstep (n : ℕ) : (x (n+1)-x n).norm < C := by simpa [x] using hs n
  have hstrip (n : ℕ) : |(dc*(x n-x 0)).im| ≤ (2*B : ℕ) := by
    rw [hx,← det_eq_im_mul,det_sub_right]
    have hh := abs_sub_le (det d (y n)) 0 (det d (y 0))
    simp only [sub_zero,zero_sub,abs_neg] at hh
    have hb0 := hb 0
    have hbn := hb n
    push_cast
    omega
  have hnorm (n : ℕ) : (y n-y 0).norm ≤ R := by
    rw [← hx]
    exact hR x n (fun j _ => hz j) (fun j _ => hstep j)
      (fun j _ => hstrip j) n le_rfl
  have hinj : Function.Injective (fun n => y n-y 0) := by
    intro i j he
    exact hy (sub_left_injective he)
  obtain ⟨T,hT⟩ := injective_escapes_norm (fun n => y n-y 0) hinj R
  have ht := hT T le_rfl
  have hl := hnorm T
  omega

/-- The rank-two necessity holds for an admissible ray, without assuming its
vertices are genuine Gaussian primes. -/
theorem admissible_ray_forces_rank_two {C : ℤ} (h : HasAdmissibleRay C) :
    ∀ N : ℕ, HasRankTwoComponent C N := by
  obtain ⟨y,hy0,hy,hs,hg⟩ := h
  intro N
  obtain ⟨z,hz⟩ := sieve_translate y hg N
  let x : ℕ → GaussianInt := fun n => z+y n
  have hx : Function.Injective x := by
    intro i j he
    exact hy (add_left_cancel he)
  have hstep (n : ℕ) : (x (n+1)-x n).norm < C := by simpa [x] using hs n
  have hgx := good_add_translate y hg z
  have hadj (n : ℕ) : (sieveGraph C N).Adj (x n) (x (n+1)) := by
    refine ⟨hz n,hz (n+1),?_,hstep n⟩
    intro he
    have := hx he
    omega
  have hr (n : ℕ) : (sieveGraph C N).Reachable (x 0) (x n) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih => exact ih.trans (hadj n).reachable
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  obtain ⟨i,j,k,l,hij,hkl,hdet⟩ := independent_same_color_differences x hx
    (fun n => residue N (x n))
    (fun d hd B => admissible_projection_unbounded x C hx hstep hgx d hd B)
  exact ⟨x 0,x j-x i,x l-x k,period_of_same_residue hij,period_of_same_residue hkl,
    reachable_period_at_base (hr i) (hr j) (period_of_same_residue hij),
    reachable_period_at_base (hr k) (hr l) (period_of_same_residue hkl),hdet⟩

lemma rank_two_implies_sieve_ray {C : ℤ} {N : ℕ} (h : HasRankTwoComponent C N) :
    HasSieveRay C N := by
  obtain ⟨z,d,e,hd,he,hrd,hre,hdet⟩ := h
  have hd0 : d ≠ 0 := by
    intro hh
    apply hdet
    simp [hh,det]
  apply (sieve_ray_iff_infinite_component C N).mpr
  refine ⟨z,?_⟩
  have hinj : Function.Injective (fun n : ℕ => z+(n : GaussianInt)*d) := by
    intro i j hij
    exact Nat.cast_injective (mul_right_cancel₀ hd0 (add_left_cancel hij))
  apply (Set.infinite_range_of_injective hinj).mono
  rintro w ⟨n,rfl⟩
  have hh := reachable_multiples_of_period hrd
    (show IsPeriod N (z+d-z) by simpa using hd) n
  simpa only [add_sub_cancel_left] using hh

/-- An exact rank-two reformulation of the all-cutoff condition. It does not
assert that either side holds for any particular jump bound. -/
theorem admissible_ray_iff_rank_two_all_cutoffs (C : ℤ) :
    HasAdmissibleRay C ↔ ∀ N : ℕ, HasRankTwoComponent C N := by
  refine ⟨admissible_ray_forces_rank_two,?_⟩
  intro h
  exact (admissible_ray_iff_finite_sieve_rays C).mpr
    (fun N => rank_two_implies_sieve_ray (h N))

theorem no_admissible_ray_iff_rank_two_cutoff (C : ℤ) :
    (¬ HasAdmissibleRay C) ↔ ∃ N : ℕ, ¬ HasRankTwoComponent C N := by
  rw [admissible_ray_iff_rank_two_all_cutoffs]
  simp only [not_forall]

/-- Excluding rank-two components at just one cutoff eliminates all infinite
components after possibly increasing the cutoff. This does not provide the
initial rank-two exclusion for an arbitrary jump bound. -/
theorem rank_two_cutoff_upgrades_to_finite_components {C : ℤ} {N : ℕ}
    (hN : ¬ HasRankTwoComponent C N) :
    ∃ M : ℕ, N ≤ M ∧ ∀ z : GaussianInt,
      {w | (sieveGraph C M).Reachable z w}.Finite := by
  have hno : ¬ HasAdmissibleRay C :=
    (no_admissible_ray_iff_rank_two_cutoff C).mpr ⟨N,hN⟩
  obtain ⟨M,hM⟩ := (no_admissible_ray_iff_finite_sieve_components C).mp hno
  refine ⟨max N M,le_max_left _ _,?_⟩
  intro z
  apply (hM z).subset
  intro w hw
  apply hw.mono
  intro u v huv
  exact ⟨fun p hp hpprime => huv.1 p (hp.trans (le_max_right _ _)) hpprime,
    fun p hp hpprime => huv.2.1 p (hp.trans (le_max_right _ _)) hpprime,
    huv.2.2⟩

#print axioms rank_two_cutoff_upgrades_to_finite_components

#print axioms admissible_projection_unbounded
#print axioms admissible_ray_iff_rank_two_all_cutoffs
#print axioms no_admissible_ray_iff_rank_two_cutoff

end AdmissibleRankTwo
end Erdos952Investigation
