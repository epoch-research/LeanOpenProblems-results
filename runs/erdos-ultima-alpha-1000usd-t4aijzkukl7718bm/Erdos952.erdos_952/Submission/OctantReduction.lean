import Submission.FiniteCertificates

/-! Folding the actual Gaussian-prime graph into one octant without enlarging the step bound. -/
namespace Erdos952Investigation
namespace OctantReduction

set_option maxHeartbeats 0

def quadrant (z : GaussianInt) : GaussianInt := ⟨|z.re|, |z.im|⟩

def fold (z : GaussianInt) : GaussianInt :=
  ⟨max |z.re| |z.im|, min |z.re| |z.im|⟩

def InOctant (z : GaussianInt) : Prop := 0 ≤ z.im ∧ z.im ≤ z.re

lemma prime_star {z : GaussianInt} (hz : Prime z) : Prime (star z) :=
  (MulEquiv.prime_iff (starMulAut : GaussianInt ≃* GaussianInt)).mpr hz

lemma prime_swap {z : GaussianInt} (hz : Prime z) : Prime (⟨z.im, z.re⟩ : GaussianInt) := by
  let i : GaussianInt := ⟨0, 1⟩
  have hi : IsUnit i := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) i).mp (by
    norm_num [i, gaussian_norm_sq])
  have he : (⟨z.im, z.re⟩ : GaussianInt) = i * star z := by
    apply Zsqrtd.ext <;> simp [i]
  rw [he]
  exact prime_mul_iff.mpr (Or.inr ⟨hi, prime_star hz⟩)

lemma prime_quadrant {z : GaussianInt} (hz : Prime z) : Prime (quadrant z) := by
  by_cases hr : 0 ≤ z.re
  · by_cases hi : 0 ≤ z.im
    · have he : quadrant z = z := by
        apply Zsqrtd.ext <;> simp [quadrant, abs_of_nonneg hr, abs_of_nonneg hi]
      exact he.symm ▸ hz
    · have he : quadrant z = star z := by
        apply Zsqrtd.ext <;> simp [quadrant, abs_of_nonneg hr, abs_of_neg (lt_of_not_ge hi)]
      exact he.symm ▸ prime_star hz
  · by_cases hi : 0 ≤ z.im
    · have he : quadrant z = -star z := by
        apply Zsqrtd.ext <;> simp [quadrant, abs_of_neg (lt_of_not_ge hr), abs_of_nonneg hi]
      exact he.symm ▸ (prime_star hz).neg
    · have he : quadrant z = -z := by
        apply Zsqrtd.ext <;> simp [quadrant, abs_of_neg (lt_of_not_ge hr),
          abs_of_neg (lt_of_not_ge hi)]
      exact he.symm ▸ hz.neg

lemma prime_fold {z : GaussianInt} (hz : Prime z) : Prime (fold z) := by
  rcases le_total |z.re| |z.im| with h | h
  · simpa only [fold, max_eq_right h, min_eq_left h, quadrant] using
      prime_swap (prime_quadrant hz)
  · simpa only [fold, max_eq_left h, min_eq_right h, quadrant] using prime_quadrant hz

lemma fold_in_octant (z : GaussianInt) : InOctant (fold z) := by
  constructor
  · exact le_min (abs_nonneg _) (abs_nonneg _)
  · exact (min_le_left _ _).trans (le_max_left _ _)

lemma norm_fold (z : GaussianInt) : (fold z).norm = z.norm := by
  rcases le_total |z.re| |z.im| with h | h <;>
    simp [fold, gaussian_norm_sq, h, add_comm]

lemma sorted_pair_contract (a b c d : ℤ) :
    (max a b - max c d)^2 + (min a b - min c d)^2 ≤ (a - c)^2 + (b - d)^2 := by
  rcases le_total a b with hab | hba <;> rcases le_total c d with hcd | hdc
  · simp only [max_eq_right hab, min_eq_left hab, max_eq_right hcd, min_eq_left hcd]
    omega
  · simp only [max_eq_right hab, min_eq_left hab, max_eq_left hdc, min_eq_right hdc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hdc)]
  · simp only [max_eq_left hba, min_eq_right hba, max_eq_right hcd, min_eq_left hcd]
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcd)]
  · simp only [max_eq_left hba, min_eq_right hba, max_eq_left hdc, min_eq_right hdc]
    exact le_refl _

lemma fold_contract (z w : GaussianInt) : (fold w - fold z).norm ≤ (w - z).norm := by
  have hr : (|w.re| - |z.re|)^2 ≤ (w.re - z.re)^2 :=
    sq_le_sq.mpr (abs_abs_sub_abs_le _ _)
  have hi : (|w.im| - |z.im|)^2 ≤ (w.im - z.im)^2 :=
    sq_le_sq.mpr (abs_abs_sub_abs_le _ _)
  have hs := sorted_pair_contract |w.re| |w.im| |z.re| |z.im|
  simpa only [fold, gaussian_norm_sq, Zsqrtd.re_sub, Zsqrtd.im_sub] using
    hs.trans (add_le_add hr hi)

def graph (C : ℤ) : SimpleGraph GaussianInt where
  Adj z w := (primeGraph C).Adj z w ∧ InOctant z ∧ InOctant w
  symm := by
    intro z w h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by intro z h; exact h.1.2.2.1 rfl

noncomputable instance (C : ℤ) : (graph C).LocallyFinite := fun z =>
  ((primeGraph_finite_neighbors C z).subset (fun _ h => h.1)).fintype

lemma folded_range_infinite (x : ℕ → GaussianInt) (hx : Function.Injective x) :
    (Set.range (fun n => fold (x n))).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image Zsqrtd.norm).bddAbove
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx B
  have hb : (fold (x N)).norm ≤ B := hB ⟨fold (x N), ⟨N, rfl⟩, rfl⟩
  rw [norm_fold] at hb
  have := hN N le_rfl
  omega

/-- Folding can identify vertices. Passing to an infinite connected component
and extracting a ray restores injectivity, with exactly the same bound `C`. -/
theorem octant_ray_of_prime_ray (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    ∃ y : ℕ → GaussianInt, Function.Injective y ∧
      ∀ n, Prime (y n) ∧ (y (n + 1) - y n).norm < C ∧ InOctant (y n) := by
  have hr (n : ℕ) : (graph C).Reachable (fold (x 0)) (fold (x n)) := by
    induction n with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      by_cases he : fold (x n) = fold (x (n + 1))
      · exact he ▸ ih
      · apply ih.trans
        apply SimpleGraph.Adj.reachable
        exact ⟨⟨prime_fold (h n).1, prime_fold (h (n + 1)).1, he,
          lt_of_le_of_lt (fold_contract _ _) (h n).2⟩,
          fold_in_octant _, fold_in_octant _⟩
  have hinf : {w | (graph C).Reachable (fold (x 0)) w}.Infinite :=
    (folded_range_infinite x hx).mono (by rintro w ⟨n, rfl⟩; exact hr n)
  obtain ⟨y, _, hy, hs⟩ :=
    (RayReduction.ray_iff_infinite_component (graph C) (fold (x 0))).mpr hinf
  exact ⟨y, hy, fun n => ⟨(hs n).1.1, (hs n).1.2.2.2, (hs n).2.1⟩⟩

theorem gaussian_moat_octant_equivalence :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) ↔
    ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C ∧ InOctant (x n) := by
  constructor
  · rintro ⟨x, C, hx, h⟩
    obtain ⟨y, hy, hs⟩ := octant_ray_of_prime_ray x C hx h
    exact ⟨y, C, hy, hs⟩
  · rintro ⟨x, C, hx, h⟩
    exact ⟨x, C, hx, fun n => ⟨(h n).1, (h n).2.1⟩⟩

#print axioms octant_ray_of_prime_ray
#print axioms gaussian_moat_octant_equivalence

end OctantReduction
end Erdos952Investigation
