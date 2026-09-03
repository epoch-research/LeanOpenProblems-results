import Submission.PiecewiseModularObstruction

/-! A bounded-step injective Gaussian-prime ray cannot remain in a fixed-width
neighborhood of a translated parabola. This is a restricted geometric
obstruction, not a solution of the unrestricted Gaussian moat problem. -/
namespace Erdos952Investigation
namespace ParabolicTubeObstruction
open PiecewiseModularObstruction
set_option maxHeartbeats 0

/-- At large horizontal coordinates, a bounded-diameter piece of this
parabolic band lies in a vertical strip of width independent of its location. -/
lemma band_local_flatness (a b s t B T : ℝ) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (ha : |b-a^2| ≤ B*(|a|+1)) (hs : |t-s^2| ≤ B*(|s|+1))
    (hnear : |s-a| ≤ T) (ht : |t-b| ≤ T)
    (hfar : T^2+B*T+T+2*B+1 < |a|) : |s-a| ≤ B+1 := by
  have hsabs : |s| ≤ |a|+T := by
    have hh := abs_add_le (s-a) a
    rw [sub_add_cancel] at hh
    linarith
  have hsquare : |s^2-a^2| ≤ T+B*(2*|a|+T+2) := by
    have h1 := abs_sub_le (s^2) t (a^2)
    have h2 := abs_sub_le t b (a^2)
    rw [abs_sub_comm (s^2) t] at h1
    have hm := mul_le_mul_of_nonneg_left hsabs hB
    nlinarith
  have htri : 2*|a| ≤ |s+a|+|s-a| := by
    have hh := abs_sub_le (s+a) 0 (s-a)
    rw [sub_zero,zero_sub,abs_neg,show (s+a)-(s-a) = 2*a by ring] at hh
    simpa only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh
  have hlower : 2*|a|-T ≤ |s+a| := by linarith
  have hprod := mul_le_mul_of_nonneg_left hlower (abs_nonneg (s-a))
  have he : |s-a| * |s+a| = |s^2-a^2| := by
    rw [← abs_mul]
    congr 1
    ring
  rw [he] at hprod
  have hnearT := mul_le_mul_of_nonneg_right hnear hT
  have hapos : 0 < |a| := by
    nlinarith [sq_nonneg T,mul_nonneg hB hT]
  by_contra! hbad
  have hpositive := mul_pos hapos (show 0 < |s-a|-B-1 by linarith)
  nlinarith

def Band (a b B : ℝ) (z : GaussianInt) : Prop :=
  |((z.im : ℝ)-b)-((z.re : ℝ)-a)^2| ≤ B*(|(z.re : ℝ)-a|+1)

/-- The width and translation are fixed, but the curve is genuinely nonlinear.
No monotonicity of either coordinate of the ray is assumed. -/
theorem no_prime_ray_in_band (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (a b B : ℝ) (hB : 0 ≤ B) : ¬ ∀ n, Band a b B (x n) := by
  intro hband
  obtain ⟨K,hK⟩ := UniformRealStrip.uniform_escape_all_directions C (B+1)
  let D : ℝ := 2*((max C 1 : ℤ) : ℝ)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hmax : (0 : ℤ) ≤ max C 1 := by omega
    positivity
  let T : ℝ := (K : ℝ)*D
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let f : ℕ → ℝ := fun n => (x n).re-a
  let g : ℕ → ℝ := fun n => (x n).im-b
  have hfs (n : ℕ) : |f (n+1)-f n| ≤ D := by
    simpa only [affine,one_mul,zero_mul,add_zero,zero_add,add_neg,f,D] using
      affine_step_bound 1 0 (-a) (by norm_num) C (h n).2
  have hgs (n : ℕ) : |g (n+1)-g n| ≤ D := by
    simpa only [affine,one_mul,zero_mul,add_zero,zero_add,add_neg,g,D] using
      affine_step_bound 0 1 (-b) (by norm_num) C (h n).2
  let H := T^2+B*T+T+2*B+1
  obtain ⟨M,hM⟩ := exists_nat_gt (H+|a|)
  obtain ⟨N,_,hN⟩ := RationalStrip.rational_projection_unbounded x C hx h
    1 0 (Or.inl one_ne_zero) 0 M
  have hNr : (M : ℝ) < |((x N).re : ℝ)| := by
    exact_mod_cast (by simpa only [one_mul,zero_mul,add_zero] using hN)
  have hfar : H < |f N| := by
    have hh : |((x N).re : ℝ)| ≤ |f N|+|a| := by
      simpa only [f,sub_add_cancel] using abs_add_le (((x N).re : ℝ)-a) a
    linarith
  obtain ⟨j,hj,hescape⟩ := hK x hx h N 1 0 (by norm_num)
  have hcast : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hlimit : (j : ℝ)*D ≤ T := mul_le_mul_of_nonneg_right hcast hD
  have hsmall := band_local_flatness (f N) (g N) (f (N+j)) (g (N+j)) B T hB hT
    (hband N) (hband (N+j))
    ((accumulated_step_bound f D hfs N j).trans hlimit)
    ((accumulated_step_bound g D hgs N j).trans hlimit) hfar
  have he : |f (N+j)-f N| = |((x (N+j)-x N).re : ℝ)| := by
    simp only [f,Zsqrtd.re_sub,Int.cast_sub]
    congr 1
    ring
  rw [he] at hsmall
  simp only [one_mul,zero_mul,add_zero] at hescape
  linarith

/-- Every tail leaves every band of the stated width. This does not assert
that its intersection with the band is finite. -/
theorem band_escape_on_every_tail (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (a b B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ n ≥ N, ¬ Band a b B (x n) := by
  by_contra! hband
  apply no_prime_ray_in_band (fun n => x (N+n)) C
    (fun i j he => Nat.add_left_cancel (hx he))
    (fun n => by simpa only [Nat.add_assoc] using h (N+n)) a b B hB
  intro n
  exact hband (N+n) (by omega)

/-- A sup-norm tube around the real parabola `(a+t,b+t²)`. In particular,
a Euclidean tube of the same width is contained in this tube. -/
def Tube (a b W : ℝ) (z : GaussianInt) : Prop :=
  ∃ t : ℝ, |(z.re : ℝ)-a-t| ≤ W ∧ |(z.im : ℝ)-b-t^2| ≤ W

lemma tube_in_band (a b W : ℝ) (hW : 0 ≤ W) (z : GaussianInt)
    (hz : Tube a b W z) : Band a b (3*W+W^2) z := by
  obtain ⟨t,ht,hv⟩ := hz
  let u : ℝ := (z.re : ℝ)-a
  let v : ℝ := (z.im : ℝ)-b
  change |u-t| ≤ W at ht
  change |v-t^2| ≤ W at hv
  change |v-u^2| ≤ (3*W+W^2)*(|u|+1)
  have htu : |t-u| ≤ W := by rwa [abs_sub_comm]
  have htbound : |t| ≤ |u|+W := by
    have hh := abs_add_le (t-u) u
    rw [sub_add_cancel] at hh
    linarith
  have hsum : |t+u| ≤ 2*|u|+W := (abs_add_le t u).trans (by linarith)
  have hsquare : |t^2-u^2| ≤ W*(2*|u|+W) := by
    rw [show t^2-u^2 = (t-u)*(t+u) by ring,abs_mul]
    exact mul_le_mul htu hsum (abs_nonneg _) hW
  have hh := abs_sub_le v (t^2) (u^2)
  nlinarith [mul_nonneg (sq_nonneg W) (abs_nonneg u),
    mul_nonneg hW (abs_nonneg u)]

theorem tube_escape_on_every_tail (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C)
    (a b W : ℝ) (hW : 0 ≤ W) (N : ℕ) :
    ∃ n ≥ N, ¬ Tube a b W (x n) := by
  obtain ⟨n,hn,hnot⟩ := band_escape_on_every_tail x C hx h a b (3*W+W^2)
    (by positivity) N
  exact ⟨n,hn,fun ht => hnot (tube_in_band a b W hW (x n) ht)⟩

lemma finite_accumulated_bound (f : ℕ → ℝ) (D : ℝ) (K : ℕ)
    (hs : ∀ n < K, |f (n+1)-f n| ≤ D) :
    ∀ n ≤ K, |f n-f 0| ≤ (n : ℝ)*D := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := abs_sub_le (f (n+1)) (f n) (f 0)
    have hi := ih (by omega)
    have hstep := hs n (by omega)
    push_cast
    linarith

/-- A sufficiently long finite prime segment wholly inside the band must
start in a fixed central region. The thresholds do not depend on the
translation parameters `a` and `b`. -/
lemma segment_start_bound (C : ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ a b : ℝ, ∀ x : ℕ → GaussianInt,
      Set.InjOn x (Set.Iic K) →
      (∀ n ≤ K, Prime (x n)) →
      (∀ n < K, (x (n+1)-x n).norm < C) →
      (∀ n ≤ K, Band a b B (x n)) → |((x 0).re : ℝ)-a| ≤ H := by
  obtain ⟨K,hK⟩ := UniformRealStrip.uniform_prime_segment_bound_all_directions C (B+1)
  let D : ℝ := 2*((max C 1 : ℤ) : ℝ)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hmax : (0 : ℤ) ≤ max C 1 := by omega
    positivity
  let T : ℝ := (K : ℝ)*D
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let H := T^2+B*T+T+2*B+1
  refine ⟨K,H,by dsimp [H]; positivity,?_⟩
  intro a b x hx hp hs hband
  by_contra! hfar
  let f : ℕ → ℝ := fun n => (x n).re-a
  let g : ℕ → ℝ := fun n => (x n).im-b
  have hfs (n : ℕ) (hn : n < K) : |f (n+1)-f n| ≤ D := by
    simpa only [affine,one_mul,zero_mul,add_zero,zero_add,add_neg,f,D] using
      affine_step_bound 1 0 (-a) (by norm_num) C (hs n hn)
  have hgs (n : ℕ) (hn : n < K) : |g (n+1)-g n| ≤ D := by
    simpa only [affine,one_mul,zero_mul,add_zero,zero_add,add_neg,g,D] using
      affine_step_bound 0 1 (-b) (by norm_num) C (hs n hn)
  have hbad : K < K := by
    apply hK 1 0 (by norm_num) x K hx hp hs
    intro j hj
    have hlimit : (j : ℝ)*D ≤ T :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hD
    have hsmall := band_local_flatness (f 0) (g 0) (f j) (g j) B T hB hT
      (hband 0 (by omega)) (hband j hj)
      ((finite_accumulated_bound f D K hfs j hj).trans hlimit)
      ((finite_accumulated_bound g D K hgs j hj).trans hlimit) hfar
    have he : |f j-f 0| = |((x j-x 0).re : ℝ)| := by
      simp only [f,Zsqrtd.re_sub,Int.cast_sub]
      congr 1
      ring
    simpa only [one_mul,zero_mul,add_zero,he] using hsmall
  omega

lemma central_band_finite (a b B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H) :
    {z : GaussianInt | Band a b B z ∧ |(z.re : ℝ)-a| ≤ H}.Finite := by
  let U := H+|a|
  let V := H^2+B*(H+1)+|b|
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (U^2+V^2)
  apply (norm_sublevel_finite (N : ℤ)).subset
  intro z hz
  obtain ⟨hb,hc⟩ := hz
  have hre : |(z.re : ℝ)| ≤ U := by
    have hh := abs_add_le ((z.re : ℝ)-a) a
    rw [sub_add_cancel] at hh
    dsimp only [U]
    linarith
  have hsq : ((z.re : ℝ)-a)^2 ≤ H^2 :=
    sq_le_sq.mpr (by rwa [abs_of_nonneg hH])
  have him : |(z.im : ℝ)| ≤ V := by
    have h1 := abs_sub_le (z.im : ℝ) b 0
    have h2 := abs_sub_le ((z.im : ℝ)-b) (((z.re : ℝ)-a)^2) 0
    simp only [sub_zero] at h1 h2
    rw [abs_of_nonneg (sq_nonneg ((z.re : ℝ)-a))] at h2
    have hm := mul_le_mul_of_nonneg_left hc hB
    dsimp only [Band] at hb
    dsimp only [V]
    nlinarith
  have hre2 : (z.re : ℝ)^2 ≤ U^2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hU])
  have him2 : (z.im : ℝ)^2 ≤ V^2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hV])
  have hnorm : (z.norm : ℝ) = (z.re : ℝ)^2+(z.im : ℝ)^2 := by
    simp only [gaussian_norm_sq,Int.cast_add,Int.cast_pow]
  have hbound : (z.norm : ℝ) ≤ N := by rw [hnorm]; linarith
  exact_mod_cast hbound

/-- A genuine uniform finite-segment bound, for each fixed band and step
bound. It applies to any injective finite prime path, not only a prefix of
one specified infinite ray. -/
theorem uniform_prime_segment_bound (C : ℤ) (a b B : ℝ) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, Band a b B (x n)) → L < J := by
  classical
  obtain ⟨K,H,hH,hstart⟩ := segment_start_bound C B hB
  let S := {z : GaussianInt | Band a b B z ∧ |(z.re : ℝ)-a| ≤ H}
  letI : Fintype S := (central_band_finite a b B H hB hH).fintype
  let M := Fintype.card S
  refine ⟨M+K,?_⟩
  intro x L hx hp hs hband
  by_contra! hlong
  have hmem (i : Fin (M+1)) : x i.val ∈ S := by
    have hi : i.val ≤ L := by omega
    refine ⟨hband i.val hi,?_⟩
    have hh := hstart a b (fun n => x (i.val+n))
      (fun u hu v hv he => Nat.add_left_cancel
        (hx (by change i.val+u ≤ L; change u ≤ K at hu; omega)
          (by change i.val+v ≤ L; change v ≤ K at hv; omega) he))
      (fun n hn => hp (i.val+n) (by omega))
      (fun n hn => by simpa only [Nat.add_assoc] using hs (i.val+n) (by omega))
      (fun n hn => hband (i.val+n) (by omega))
    simpa only [Nat.add_zero] using hh
  let f : Fin (M+1) → S := fun i => ⟨x i.val,hmem i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hx (by change i.val ≤ L; omega) (by change j.val ≤ L; omega)
      (congrArg Subtype.val he)
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  change M+1 ≤ M at hcard
  omega

theorem uniform_prime_tube_segment_bound (C : ℤ) (a b W : ℝ) (hW : 0 ≤ W) :
    ∃ J : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, Prime (x n)) →
      (∀ n < L, (x (n+1)-x n).norm < C) →
      (∀ n ≤ L, Tube a b W (x n)) → L < J := by
  obtain ⟨J,hJ⟩ := uniform_prime_segment_bound C a b (3*W+W^2) (by positivity)
  exact ⟨J,fun x L hx hp hs ht =>
    hJ x L hx hp hs (fun n hn => tube_in_band a b W hW (x n) (ht n hn))⟩

#print axioms segment_start_bound
#print axioms uniform_prime_tube_segment_bound


#print axioms band_local_flatness
#print axioms no_prime_ray_in_band
#print axioms tube_escape_on_every_tail
end ParabolicTubeObstruction
end Erdos952Investigation
