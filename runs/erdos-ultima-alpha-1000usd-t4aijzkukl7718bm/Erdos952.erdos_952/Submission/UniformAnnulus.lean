import Submission.UniformRealStrip

/-! Uniform bounds for prime paths in annuli of fixed width. These bounds do
not prohibit a path that keeps crossing annuli and wandering through the plane. -/
namespace Erdos952Investigation
namespace UniformAnnulus

open UniformRealStrip
set_option maxHeartbeats 0

lemma finite_norm_drift_bound (x : ℕ → GaussianInt) (C : ℤ) (L : ℕ)
    (hs : ∀ n < L, (x (n+1)-x n).norm < C) (K : ℕ) (hK : K ≤ L) :
    ∀ n ≤ K, (x n-x 0).norm ≤ 2*((K : ℤ)*max C 1)^2 := by
  let y : ℕ → GaussianInt := fun n => ⟨(x n).im,(x n).re⟩
  have hys (j : ℕ) (hj : j < L) : (y (j+1)-y j).norm < C := by
    simpa only [y,gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,add_comm] using hs j hj
  intro n hn
  have hE : (0 : ℤ) ≤ max C 1 := (by norm_num : (0 : ℤ) ≤ 1).trans (le_max_right _ _)
  have hmul : (n : ℤ)*max C 1 ≤ (K : ℤ)*max C 1 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hE
  have hr := (finite_re_drift_bound x C L hs n (hn.trans hK)).trans hmul
  have hi : |(x n-x 0).im| ≤ (K : ℤ)*max C 1 :=
    (finite_re_drift_bound y C L hys n (hn.trans hK)).trans hmul
  have hpos : (0 : ℤ) ≤ (K : ℤ)*max C 1 := mul_nonneg (Int.natCast_nonneg _) hE
  have hr2 : (x n-x 0).re^2 ≤ ((K : ℤ)*max C 1)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hpos])
  have hi2 : (x n-x 0).im^2 ≤ ((K : ℤ)*max C 1)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hpos])
  rw [gaussian_norm_sq]
  omega

lemma polarization (z w c : GaussianInt) :
    (z-c).norm-(w-c).norm =
      2*((w-c).re*(z-w).re+(w-c).im*(z-w).im)+(z-w).norm := by
  simp only [gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub]
  ring

/-- The number of steps in an injective prime path lying in an annulus of fixed
width is uniformly bounded. Both the radius and the Gaussian-integer center
of the annulus are arbitrary. -/
theorem uniform_prime_segment_bound (C : ℤ) (B : ℕ) :
    ∃ K : ℕ, ∀ c : GaussianInt, ∀ R : ℕ,
      ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, (R : ℤ)^2 ≤ (x n-c).norm ∧
        (x n-c).norm ≤ ((R : ℤ)+(B : ℤ))^2) → L < K := by
  classical
  obtain ⟨K,hK⟩ := uniform_prime_segment_bound_all_directions C (2*(B : ℝ)+1)
  let D : ℤ := (K : ℤ)*max C 1
  let T : ℤ := (B : ℤ)^2+2*D^2+1
  have hT : 0 < T := by dsimp [T]; positivity
  let S := {z : GaussianInt | z.norm ≤ (2*T+(B : ℤ))^2}
  letI : Fintype S := (norm_sublevel_finite ((2*T+(B : ℤ))^2)).fintype
  refine ⟨max K (Fintype.card S),?_⟩
  intro c R x L hx hp hs hann
  by_contra! hlong
  have hKL : K ≤ L := (le_max_left _ _).trans hlong
  have hSL : Fintype.card S ≤ L := (le_max_right _ _).trans hlong
  let w := x 0-c
  let M : ℤ := max |w.re| |w.im|
  have hM : 0 ≤ M := (abs_nonneg w.re).trans (le_max_left _ _)
  have hr0 : |w.re| ≤ M := le_max_left _ _
  have hi0 : |w.im| ≤ M := le_max_right _ _
  have hnorm0 : w.norm ≤ 2*M^2 := by
    have hr2 : w.re^2 ≤ M^2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hM])
    have hi2 : w.im^2 ≤ M^2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hM])
    rw [gaussian_norm_sq]
    omega
  have hR : (R : ℤ) ≤ 2*M := by
    have hr := (hann 0 (Nat.zero_le _)).1
    change (R : ℤ)^2 ≤ w.norm at hr
    have hsq : (R : ℤ)^2 ≤ (2*M)^2 := by nlinarith [sq_nonneg M]
    have habs := sq_le_sq.mp hsq
    simpa only [abs_of_nonneg (Int.natCast_nonneg R),
      abs_of_nonneg (by omega : (0 : ℤ) ≤ 2*M)] using habs
  by_cases hlarge : T ≤ M
  · have hMpos : 0 < M := hT.trans_le hlarge
    have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
    let a : ℝ := (w.re : ℝ)/(M : ℝ)
    let b : ℝ := (w.im : ℝ)/(M : ℝ)
    have hab : max |a| |b| = 1 := by
      simp only [a,b,abs_div,abs_of_pos hMr]
      rw [max_div_div_right hMr.le]
      have hmax : max |(w.re : ℝ)| |(w.im : ℝ)| = (M : ℝ) := by
        exact_mod_cast (show max |w.re| |w.im| = M from rfl)
      rw [hmax,div_self hMr.ne']
    have hbad : K < K := by
      apply hK a b hab x K (hx.mono (Set.Iic_subset_Iic.mpr hKL))
        (fun n hn => hp n (hn.trans hKL)) (fun n hn => hs n (hn.trans_le hKL))
      intro n hn
      have hnorm := finite_norm_drift_bound x C L hs K hKL n hn
      change (x n-x 0).norm ≤ 2*D^2 at hnorm
      have hnonneg := GaussianInt.norm_nonneg (x n-x 0)
      have hpolar := polarization (x n) (x 0) c
      change (x n-c).norm-w.norm =
        2*(w.re*(x n-x 0).re+w.im*(x n-x 0).im)+(x n-x 0).norm at hpolar
      have hband : |(x n-c).norm-w.norm| ≤ 4*M*(B : ℤ)+(B : ℤ)^2 := by
        obtain ⟨hl,hu⟩ := hann n (hn.trans hKL)
        obtain ⟨hl0,hu0⟩ := hann 0 (Nat.zero_le _)
        change (R : ℤ)^2 ≤ w.norm at hl0
        change w.norm ≤ ((R : ℤ)+(B : ℤ))^2 at hu0
        have hRB := mul_le_mul_of_nonneg_right hR (Int.natCast_nonneg B)
        apply abs_le.mpr
        constructor <;> nlinarith
      have hdot : |w.re*(x n-x 0).re+w.im*(x n-x 0).im| ≤ M*(2*(B : ℤ)+1) := by
        have hh := abs_le.mp hband
        dsimp [T] at hlarge
        apply abs_le.mpr
        constructor <;> nlinarith
      have he : a*((x n-x 0).re : ℝ)+b*((x n-x 0).im : ℝ) =
          ((w.re*(x n-x 0).re+w.im*(x n-x 0).im : ℤ) : ℝ)/(M : ℝ) := by
        dsimp [a,b]
        push_cast
        ring
      rw [he,abs_div,abs_of_pos hMr]
      apply (div_le_iff₀ hMr).mpr
      have hdotr : |((w.re*(x n-x 0).re+w.im*(x n-x 0).im : ℤ) : ℝ)| ≤
          (M : ℝ)*(2*(B : ℝ)+1) := by exact_mod_cast hdot
      simpa only [mul_comm] using hdotr
    omega
  · have hsmall (n : ℕ) (hn : n ≤ L) : (x n-c).norm ≤ (2*T+(B : ℤ))^2 := by
      have hu := (hann n hn).2
      have hrt : (R : ℤ)+(B : ℤ) ≤ 2*T+(B : ℤ) := by omega
      have hnonneg : (0 : ℤ) ≤ (R : ℤ)+(B : ℤ) := by positivity
      have hsquare : ((R : ℤ)+(B : ℤ))^2 ≤ (2*T+(B : ℤ))^2 := sq_le_sq.mpr (by
        rw [abs_of_nonneg hnonneg,abs_of_nonneg (by omega : (0 : ℤ) ≤ 2*T+(B : ℤ))]
        exact hrt)
      exact hu.trans hsquare
    let f : Fin (L+1) → S := fun i => ⟨x i.val-c,hsmall i.val (by omega)⟩
    have hfi : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      apply hx (by change i.val ≤ L; omega) (by change j.val ≤ L; omega)
      exact sub_left_injective (congrArg Subtype.val hij)
    have hcard := Fintype.card_le_of_injective f hfi
    simp only [Fintype.card_fin] at hcard
    omega

/-- Uniform escape from every fixed-width annulus, on every segment of a
hypothetical prime ray. -/
theorem uniform_annular_escape (C : ℤ) (B : ℕ) :
    ∃ K : ℕ, ∀ x : ℕ → GaussianInt, Function.Injective x →
      (∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) →
      ∀ N : ℕ, ∀ c : GaussianInt, ∀ R : ℕ,
        ∃ i ≤ K, (x (N+i)-c).norm < (R : ℤ)^2 ∨
          ((R : ℤ)+(B : ℤ))^2 < (x (N+i)-c).norm := by
  obtain ⟨K,hK⟩ := uniform_prime_segment_bound C B
  refine ⟨K,?_⟩
  intro x hx h N c R
  by_contra! hann
  have hbad := hK c R (fun i => x (N+i)) K
    (fun i _ j _ he => Nat.add_left_cancel (hx he))
    (fun i _ => (h (N+i)).1)
    (fun i _ => by simpa only [Nat.add_assoc] using (h (N+i)).2) hann
  omega

#print axioms uniform_prime_segment_bound
#print axioms uniform_annular_escape

end UniformAnnulus
end Erdos952Investigation
