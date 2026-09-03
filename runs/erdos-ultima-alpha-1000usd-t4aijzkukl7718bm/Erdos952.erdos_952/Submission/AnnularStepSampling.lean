import Submission.AnnularNecessity

/-! First-exit sampling of an injective bounded-step sequence. A hypothetical
Gaussian-prime ray can be thinned to rays with arbitrarily small relative
variation in jump length. This is a reduction, not a constant-norm theorem. -/
namespace Erdos952Investigation.AnnularStepSampling
open AnnularNecessity
set_option maxHeartbeats 0

lemma exists_later_annular_step (x : ℕ → GaussianInt) (C R : ℤ)
    (hx : Function.Injective x) (hs : ∀ n, (x (n+1)-x n).norm < C)
    (hR : 0 ≤ R) (i : ℕ) :
    ∃ j, i < j ∧ R^2 < (x j-x i).norm ∧ (x j-x i).norm < (R+C)^2 := by
  let y (n : ℕ) : GaussianInt := x (i+n)-x i
  have hy : Function.Injective y := by
    intro m n he
    apply Nat.add_left_cancel
    apply hx
    change x (i+m)-x i = x (i+n)-x i at he
    exact sub_left_inj.mp he
  have hys (n : ℕ) : (y (n+1)-y n).norm < C := by
    simpa only [y,sub_sub_sub_cancel_right,Nat.add_assoc] using hs (i+n)
  obtain ⟨n,hn,hn'⟩ := ray_meets_annulus y C R hy hys hR (by
    simp only [y,Nat.add_zero,sub_self,Zsqrtd.norm_zero]
    exact sq_nonneg R)
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp only [he,y,Nat.add_zero,sub_self,Zsqrtd.norm_zero] at hn
    nlinarith [sq_nonneg R]
  exact ⟨i+n,by omega,hn,hn'⟩

/-- The sampled sequence is a genuine subsequence, so primality and
injectivity are preserved. The annular thickness C does not depend on R. -/
theorem annular_subsequence (x : ℕ → GaussianInt) (C R : ℤ)
    (hx : Function.Injective x) (hs : ∀ n, (x (n+1)-x n).norm < C)
    (hR : 0 ≤ R) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ f 0 = 0 ∧
      ∀ n, R^2 < (x (f (n+1))-x (f n)).norm ∧
        (x (f (n+1))-x (f n)).norm < (R+C)^2 := by
  choose next hnext hlo hhi using exists_later_annular_step x C R hx hs hR
  let f : ℕ → ℕ := Nat.rec 0 (fun _ j => next j)
  have hsucc (n : ℕ) : f (n+1) = next (f n) := rfl
  refine ⟨f,strictMono_nat_of_lt_succ (fun n => ?_),rfl,fun n => ?_⟩
  · rw [hsucc]; exact hnext (f n)
  · rw [hsucc]; exact ⟨hlo (f n),hhi (f n)⟩

/-- One additive thickness works at every radius. This condition is equivalent
to the original existence question; it does not assert either side. -/
theorem conjecture_iff_fixed_thickness :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∃ C : ℤ, 0 < C ∧ ∀ R : ℤ, 0 ≤ R →
      ∃ y : ℕ → GaussianInt, Function.Injective y ∧
        ∀ n, Prime (y n) ∧ R^2 < (y (n+1)-y n).norm ∧
          (y (n+1)-y n).norm < (R+C)^2 := by
  constructor
  · rintro ⟨x,C,hx,h⟩
    have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (h 0).2
    refine ⟨C,hC,?_⟩
    intro R hR
    obtain ⟨f,hf,_,hfs⟩ := annular_subsequence x C R hx (fun n => (h n).2) hR
    exact ⟨fun n => x (f n),hx.comp hf.injective,fun n => ⟨(h (f n)).1,hfs n⟩⟩
  · rintro ⟨C,_,h⟩
    obtain ⟨y,hy,hys⟩ := h 0 le_rfl
    refine ⟨y,C^2,hy,fun n => ⟨(hys n).1,?_⟩⟩
    simpa using (hys n).2.2

/-- For each positive k, the squared jump norms can be restricted to an
interval with ratio less than 1+1/k. Its radius may depend on k. -/
theorem conjecture_iff_arbitrarily_thin_annuli :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∀ k : ℕ, 0 < k → ∃ R : ℤ, 0 < R ∧
      ∃ y : ℕ → GaussianInt, Function.Injective y ∧
        ∀ n, Prime (y n) ∧ R^2 < (y (n+1)-y n).norm ∧
          (k : ℤ)*(y (n+1)-y n).norm < ((k : ℤ)+1)*R^2 := by
  constructor
  · intro h k hk
    obtain ⟨C,hC,hann⟩ := conjecture_iff_fixed_thickness.mp h
    let R : ℤ := (2*(k : ℤ)+1)*C
    have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
    have hR : 0 < R := mul_pos (by omega) hC
    obtain ⟨y,hy,hys⟩ := hann R hR.le
    refine ⟨R,hR,y,hy,fun n => ⟨(hys n).1,(hys n).2.1,?_⟩⟩
    have hgap : ((k : ℤ)+1)*R^2-(k : ℤ)*(R+C)^2 = ((k : ℤ)+1)*C^2 := by
      dsimp only [R]
      ring
    have hnon : 0 ≤ ((k : ℤ)+1)*C^2 := mul_nonneg (by omega) (sq_nonneg C)
    have hup : (k : ℤ)*(R+C)^2 ≤ ((k : ℤ)+1)*R^2 := by omega
    exact (mul_lt_mul_of_pos_left (hys n).2.2 hk0).trans_le hup
  · intro h
    obtain ⟨R,_,y,hy,hys⟩ := h 1 (by omega)
    refine ⟨y,2*R^2,hy,fun n => ⟨(hys n).1,?_⟩⟩
    simpa using (hys n).2.2

/-- In the integral-radius formulation, increasingly thin relative annuli
necessarily move to larger radii. There is no fixed-radius limit here. -/
lemma radius_sq_gt_precision (k : ℕ) (R : ℤ) (d : GaussianInt)
    (hlo : R^2 < d.norm) (hhi : (k : ℤ)*d.norm < ((k : ℤ)+1)*R^2) :
    (k : ℤ) < R^2 := by
  have hinc : R^2+1 ≤ d.norm := by omega
  have hm := mul_le_mul_of_nonneg_left hinc (Int.natCast_nonneg k)
  nlinarith

/-- For a fixed radius, sufficiently demanding relative precision excludes
even one integer-lattice jump, regardless of primality. -/
theorem no_fixed_radius_all_precisions (R : ℤ) :
    ¬ ∀ k : ℕ, 0 < k → ∃ d : GaussianInt,
      R^2 < d.norm ∧ (k : ℤ)*d.norm < ((k : ℤ)+1)*R^2 := by
  intro h
  obtain ⟨d,hl,hu⟩ := h ((R^2).toNat+1) (by omega)
  have hh := radius_sq_gt_precision ((R^2).toNat+1) R d hl hu
  have hc : ((R^2).toNat : ℤ) = R^2 := Int.toNat_of_nonneg (sq_nonneg R)
  push_cast at hh
  omega

#print axioms no_fixed_radius_all_precisions
#print axioms annular_subsequence
#print axioms conjecture_iff_fixed_thickness
#print axioms conjecture_iff_arbitrarily_thin_annuli
end Erdos952Investigation.AnnularStepSampling
