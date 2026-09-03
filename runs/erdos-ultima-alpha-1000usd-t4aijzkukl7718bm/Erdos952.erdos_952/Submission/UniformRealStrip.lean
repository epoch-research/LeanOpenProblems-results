import Submission.UniformIrrationalStrip
import Submission.OctantReduction

/-! Uniform finite-segment bounds for real-slope strips, including bounds
uniform over every compact interval of slopes. These do not exclude paths
which keep bending away from every narrow strip. -/
namespace Erdos952Investigation
namespace UniformRealStrip

set_option maxHeartbeats 0

theorem uniform_prime_segment_bound (α : ℝ) (C : ℤ) (B : ℝ) :
    ∃ K : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ)| ≤ B) → L < K := by
  by_cases hα : Irrational α
  · exact UniformIrrationalStrip.uniform_prime_segment_bound hα C B
  obtain ⟨q,rfl⟩ := exists_rat_of_not_irrational hα
  let d : GaussianInt := ⟨q.den,-q.num⟩
  have hd : d ≠ 0 := by
    intro he
    have ht := congrArg Zsqrtd.re he
    change (q.den : ℤ) = 0 at ht
    exact q.den_nz (Int.natCast_eq_zero.mp ht)
  have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  obtain ⟨T,hT⟩ := exists_nat_gt ((q.den : ℝ)*B)
  obtain ⟨K,hK⟩ := UniformRationalStrip.uniform_prime_segment_bound d hd C T
  refine ⟨K,?_⟩
  intro x L hx hp hs hstrip
  apply hK x L hx hp hs
  intro n hn
  have he : (((d*(x n-x 0)).im : ℤ) : ℝ) = (q.den : ℝ)*
      (((x n-x 0).im : ℝ)-(q : ℝ)*((x n-x 0).re : ℝ)) := by
    simp only [Zsqrtd.im_mul,d,Int.cast_add,Int.cast_mul,Int.cast_natCast,
      Int.cast_neg,Rat.cast_def]
    field_simp
    ring
  have hb : |(((d*(x n-x 0)).im : ℤ) : ℝ)| ≤ (T : ℝ) := by
    rw [he,abs_mul,abs_of_pos hden]
    exact (mul_le_mul_of_nonneg_left (hstrip n hn) hden.le).trans hT.le
  exact_mod_cast hb

lemma finite_re_drift_bound (x : ℕ → GaussianInt) (C : ℤ) (L : ℕ)
    (hs : ∀ n < L, (x (n+1)-x n).norm < C) :
    ∀ n ≤ L, |(x n-x 0).re| ≤ (n : ℤ)*max C 1 := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hind := ih (by omega)
    have hstep : |(x (n+1)-x n).re| ≤ max C 1 :=
      (abs_re_le_gaussian_norm _).trans ((hs n (by omega)).le.trans (le_max_left _ _))
    have he : (x (n+1)-x 0).re = (x (n+1)-x n).re+(x n-x 0).re := by
      simp only [Zsqrtd.re_sub]
      ring
    rw [he]
    have ht := abs_add_le (x (n+1)-x n).re (x n-x 0).re
    push_cast
    nlinarith

/-- Compactness makes the length bound uniform over a whole compact interval
of slopes. The strip may be translated arbitrarily. -/
theorem uniform_prime_segment_bound_on_slope_interval (C : ℤ) (B a b : ℝ) :
    ∃ K : ℕ, ∀ α ∈ Set.Icc a b, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ)| ≤ B) → L < K := by
  classical
  have hfixed (α : ℝ) := uniform_prime_segment_bound α C (B+1)
  choose k hk using hfixed
  let E : ℝ := ((max C 1 : ℤ) : ℝ)
  have hE : 0 < E := by
    have he : (0 : ℤ) < max C 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    dsimp [E]
    exact_mod_cast he
  let r : ℝ → ℝ := fun α => 1/((k α : ℝ)*E+1)
  have hr (α : ℝ) : 0 < r α := by dsimp [r]; positivity
  obtain ⟨F,hF⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).elim_finite_subcover
    (fun α => Metric.ball α (r α)) (fun _ => Metric.isOpen_ball)
    (by intro α hα; exact Set.mem_iUnion.mpr ⟨α,by simpa using hr α⟩)
  refine ⟨F.sup k,?_⟩
  intro α hα x L hx hp hs hstrip
  by_contra! hlong
  obtain ⟨β,hβ⟩ := Set.mem_iUnion.mp (hF hα)
  obtain ⟨hβF,hnear⟩ := Set.mem_iUnion.mp hβ
  have hkL : k β ≤ L := (Finset.le_sup (f := k) hβF).trans hlong
  have hdiff : |α-β| < 1/((k β : ℝ)*E+1) := by
    simpa only [Metric.mem_ball,Real.dist_eq,r] using hnear
  have hden : 0 < (k β : ℝ)*E+1 := by positivity
  have hmul := (lt_div_iff₀ hden).mp hdiff
  have hbad : k β < k β := by
    apply hk β x (k β)
    · exact hx.mono (Set.Iic_subset_Iic.mpr hkL)
    · intro n hn; exact hp n (hn.trans hkL)
    · intro n hn; exact hs n (hn.trans_le hkL)
    · intro n hn
      have hcoordZ := finite_re_drift_bound x C L hs n (hn.trans hkL)
      have hcoord : |((x n-x 0).re : ℝ)| ≤ (k β : ℝ)*E := by
        have hc : |((x n-x 0).re : ℝ)| ≤ (n : ℝ)*E := by
          dsimp [E]
          exact_mod_cast hcoordZ
        exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hE.le)
      have herror : |(α-β)*((x n-x 0).re : ℝ)| < 1 := by
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_left hcoord (abs_nonneg (α-β))
        have hh' := abs_nonneg (α-β)
        nlinarith
      have he : ((x n-x 0).im : ℝ)-β*((x n-x 0).re : ℝ) =
          (((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ)) +
            (α-β)*((x n-x 0).re : ℝ) := by ring
      rw [he]
      have ht := abs_add_le (((x n-x 0).im : ℝ)-α*((x n-x 0).re : ℝ))
        ((α-β)*((x n-x 0).re : ℝ))
      have hh := hstrip n (hn.trans hkL)
      linarith
  omega

/-- A bound uniform over *all* directions, after normalizing the coefficients
by their maximum absolute value. It is also uniform in the strip's location. -/
theorem uniform_prime_segment_bound_all_directions (C : ℤ) (B : ℝ) :
    ∃ K : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
      ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, |a*((x n-x 0).re : ℝ)+b*((x n-x 0).im : ℝ)| ≤ B) → L < K := by
  obtain ⟨K,hK⟩ := uniform_prime_segment_bound_on_slope_interval C B (-1) 1
  refine ⟨K,?_⟩
  have hsecond (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| = 1)
      (x : ℕ → GaussianInt) (L : ℕ)
      (hx : Set.InjOn x (Set.Iic L)) (hp : ∀ n ≤ L, Prime (x n))
      (hs : ∀ n < L, (x (n+1)-x n).norm < C)
      (hstrip : ∀ n ≤ L, |a*((x n-x 0).re : ℝ)+b*((x n-x 0).im : ℝ)| ≤ B) : L < K := by
    have hb0 : b ≠ 0 := by intro he; simp [he] at hb
    have hβ : |-a/b| ≤ 1 := by rw [abs_div,abs_neg,hb,div_one]; exact ha
    apply hK (-a/b) (abs_le.mp hβ) x L hx hp hs
    intro n hn
    have he : a*((x n-x 0).re : ℝ)+b*((x n-x 0).im : ℝ) =
        b*(((x n-x 0).im : ℝ)-(-a/b)*((x n-x 0).re : ℝ)) := by
      field_simp
      ring
    have hh := hstrip n hn
    rwa [he,abs_mul,hb,one_mul] at hh
  intro a b hab x L hx hp hs hstrip
  have hab' := max_le_iff.mp hab.le
  by_cases hb : |b| = 1
  · exact hsecond a b hab'.1 hb x L hx hp hs hstrip
  have ha : |a| = 1 := by
    rcases le_total |a| |b| with hle | hle
    · rw [max_eq_right hle] at hab
      exact (hb hab).elim
    · rwa [max_eq_left hle] at hab
  let y : ℕ → GaussianInt := fun n => ⟨(x n).im,(x n).re⟩
  have hy : Set.InjOn y (Set.Iic L) := by
    intro i hi j hj he
    apply hx hi hj
    exact Zsqrtd.ext (congrArg Zsqrtd.im he) (congrArg Zsqrtd.re he)
  have hyp (n : ℕ) (hn : n ≤ L) : Prime (y n) := OctantReduction.prime_swap (hp n hn)
  have hys (n : ℕ) (hn : n < L) : (y (n+1)-y n).norm < C := by
    simpa only [y,gaussian_norm_sq,Zsqrtd.re_sub,Zsqrtd.im_sub,add_comm] using hs n hn
  apply hsecond b a hab'.2 ha y L hy hyp hys
  intro n hn
  simpa only [y,Zsqrtd.re_sub,Zsqrtd.im_sub,Int.cast_sub,add_comm] using hstrip n hn

/-- A hypothetical prime ray would have to bend away from every normalized
linear projection by a prescribed amount within a uniform number of steps.
The bound does not depend on the starting index or the chosen direction. -/
theorem uniform_escape_all_directions (C : ℤ) (B : ℝ) :
    ∃ K : ℕ, ∀ x : ℕ → GaussianInt, Function.Injective x →
      (∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) →
      ∀ N : ℕ, ∀ a b : ℝ, max |a| |b| = 1 →
        ∃ i ≤ K, B < |a*((x (N+i)-x N).re : ℝ)+b*((x (N+i)-x N).im : ℝ)| := by
  obtain ⟨K,hK⟩ := uniform_prime_segment_bound_all_directions C B
  refine ⟨K,?_⟩
  intro x hx h N a b hab
  by_contra! hstrip
  have hbad := hK a b hab (fun i => x (N+i)) K
    (fun i _ j _ he => Nat.add_left_cancel (hx he))
    (fun i _ => (h (N+i)).1)
    (fun i _ => by simpa only [Nat.add_assoc] using (h (N+i)).2)
    (by simpa only [Nat.add_zero] using hstrip)
  omega

#print axioms uniform_prime_segment_bound_all_directions
#print axioms uniform_escape_all_directions
#print axioms uniform_prime_segment_bound
#print axioms uniform_prime_segment_bound_on_slope_interval

end UniformRealStrip
end Erdos952Investigation
