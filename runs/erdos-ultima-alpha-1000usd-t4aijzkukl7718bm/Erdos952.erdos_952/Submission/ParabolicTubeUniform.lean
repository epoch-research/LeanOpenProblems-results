import Submission.ParabolicTubeObstruction

/-! Translation-uniform finite prime-path bounds for parabolic tubes.
The original Gaussian moat conjecture is not settled by these bounds. -/
namespace Erdos952Investigation
namespace ParabolicTubeUniform
open ParabolicTubeObstruction
set_option maxHeartbeats 0

lemma central_im_bound (a b B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (z : GaussianInt) (hz : Band a b B z) (hr : |(z.re : ℝ)-a| ≤ H) :
    |(z.im : ℝ)-b| ≤ H^2+B*(H+1) := by
  have hsq : ((z.re : ℝ)-a)^2 ≤ H^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hH])
  have ht := abs_sub_le ((z.im : ℝ)-b) (((z.re : ℝ)-a)^2) 0
  simp only [sub_zero] at ht
  rw [abs_of_nonneg (sq_nonneg ((z.re : ℝ)-a))] at ht
  have hm := mul_le_mul_of_nonneg_left hr hB
  dsimp only [Band] at hz
  nlinarith

lemma central_difference_bound (a b B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (z w : GaussianInt) (hz : Band a b B z) (hw : Band a b B w)
    (hzr : |(z.re : ℝ)-a| ≤ H) (hwr : |(w.re : ℝ)-a| ≤ H) :
    ((z-w).norm : ℝ) ≤ (2*H)^2+(2*(H^2+B*(H+1)))^2 := by
  have hzi := central_im_bound a b B H hB hH z hz hzr
  have hwi := central_im_bound a b B H hB hH w hw hwr
  have hr : |((z-w).re : ℝ)| ≤ 2*H := by
    have ht := abs_sub_le (z.re : ℝ) a (w.re : ℝ)
    rw [abs_sub_comm a (w.re : ℝ)] at ht
    simp only [Zsqrtd.re_sub,Int.cast_sub]
    linarith
  have hi : |((z-w).im : ℝ)| ≤ 2*(H^2+B*(H+1)) := by
    have ht := abs_sub_le (z.im : ℝ) b (w.im : ℝ)
    rw [abs_sub_comm b (w.im : ℝ)] at ht
    simp only [Zsqrtd.im_sub,Int.cast_sub]
    linarith
  have hr2 : ((z-w).re : ℝ)^2 ≤ (2*H)^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg (by positivity : 0 ≤ 2*H)])
  have hi2 : ((z-w).im : ℝ)^2 ≤ (2*(H^2+B*(H+1)))^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg (by positivity : 0 ≤ 2*(H^2+B*(H+1)))])
  simp only [gaussian_norm_sq,Int.cast_add,Int.cast_pow]
  linarith

/-- One length bound works for all translations of the parabolic band. -/
theorem uniform_prime_band_segment_bound (C : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ a b : ℝ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, Band a b B (x n)) → L < J := by
  classical
  obtain ⟨K,H,hH,hstart⟩ := segment_start_bound C B hB
  obtain ⟨R,hR⟩ := exists_nat_gt ((2*H)^2+(2*(H^2+B*(H+1)))^2)
  let S := {z : GaussianInt | z.norm ≤ (R : ℤ)}
  letI : Fintype S := (norm_sublevel_finite (R : ℤ)).fintype
  let M := Fintype.card S
  refine ⟨M+K,?_⟩
  intro a b x L hx hp hs hband
  by_contra! hlong
  have hcentral (i : Fin (M+1)) : |((x i.val).re : ℝ)-a| ≤ H := by
    have hh := hstart a b (fun n => x (i.val+n))
      (fun u hu v hv he => Nat.add_left_cancel
        (hx (by change i.val+u ≤ L; change u ≤ K at hu; omega)
          (by change i.val+v ≤ L; change v ≤ K at hv; omega) he))
      (fun n hn => hp (i.val+n) (by omega))
      (fun n hn => by simpa only [Nat.add_assoc] using hs (i.val+n) (by omega))
      (fun n hn => hband (i.val+n) (by omega))
    simpa only [Nat.add_zero] using hh
  have hmem (i : Fin (M+1)) : x i.val-x 0 ∈ S := by
    have hh := central_difference_bound a b B H hB hH (x i.val) (x 0)
      (hband i.val (by omega)) (hband 0 (by omega)) (hcentral i) (hcentral 0)
    have hb : ((x i.val-x 0).norm : ℝ) ≤ R := hh.trans hR.le
    exact_mod_cast hb
  let f : Fin (M+1) → S := fun i => ⟨x i.val-x 0,hmem i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hx (by change i.val ≤ L; omega) (by change j.val ≤ L; omega)
      (sub_left_injective (congrArg Subtype.val he))
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  change M+1 ≤ M at hcard
  omega

/-- The same translation uniformity holds for the fixed-width geometric tube. -/
theorem uniform_prime_tube_segment_bound (C : ℤ) (W : ℝ) (hW : 0 ≤ W) :
    ∃ J : ℕ, ∀ a b : ℝ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, Tube a b W (x n)) → L < J := by
  obtain ⟨J,hJ⟩ := uniform_prime_band_segment_bound C (3*W+W^2) (by positivity)
  exact ⟨J,fun a b x L hx hp hs ht =>
    hJ a b x L hx hp hs (fun n hn => tube_in_band a b W hW (x n) (ht n hn))⟩

#print axioms central_difference_bound
#print axioms uniform_prime_band_segment_bound
#print axioms uniform_prime_tube_segment_bound
end ParabolicTubeUniform
end Erdos952Investigation
