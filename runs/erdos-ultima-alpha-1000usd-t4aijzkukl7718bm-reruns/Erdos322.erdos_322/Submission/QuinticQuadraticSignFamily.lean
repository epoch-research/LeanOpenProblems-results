import Submission.QuinticQuadraticBinaryNorm

/-! Rigidity of a sign-symmetric ternary quadratic quintic family.
This does not classify all quadratic maps or all quintic representations. -/
namespace Erdos322Research.QuinticQuadraticSignFamily
noncomputable section

set_option maxHeartbeats 1000000

/-- Four sign-symmetric forms followed by a diagonal form. -/
def coordinates (a b c B C D e f g x y z : ℝ) : Fin 5 → ℝ :=
  let A := a*x^2+b*y^2+c*z^2
  ![A+B*x*y+C*x*z+D*y*z, A+B*x*y-C*x*z-D*y*z,
    A-B*x*y+C*x*z-D*y*z, A-B*x*y-C*x*z+D*y*z,
    e*x^2+f*y^2+g*z^2]

/-- Nonzero target and nonzero common centre force every form to be radial. -/
theorem coefficient_classification (a b c B C D e f g N : ℝ)
    (hN : N ≠ 0) (hA : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(x^2+y^2+z^2)^5) :
    a=b ∧ a=c ∧ e=f ∧ e=g ∧ B=0 ∧ C=0 ∧ D=0 := by
  have hxy : ∀ x y : ℝ,
      2*(a*x^2+b*y^2+B*x*y)^5+2*(a*x^2+b*y^2-B*x*y)^5+
      (e*x^2+f*y^2)^5=N*(x^2+y^2)^5 := by
    intro x y
    have hh := h x y 0
    simp [coordinates,Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have hxz : ∀ x z : ℝ,
      2*(a*x^2+c*z^2+C*x*z)^5+2*(a*x^2+c*z^2-C*x*z)^5+
      (e*x^2+g*z^2)^5=N*(x^2+z^2)^5 := by
    intro x z
    have hh := h x 0 z
    simp [coordinates,Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have hyz : ∀ y z : ℝ,
      2*(b*y^2+c*z^2+D*y*z)^5+2*(b*y^2+c*z^2-D*y*z)^5+
      (f*y^2+g*z^2)^5=N*(y^2+z^2)^5 := by
    intro y z
    have hh := h 0 y z
    simp [coordinates,Fin.sum_univ_succ] at hh
    convert hh using 1; ring
  have Hxy := QuinticQuadraticBinaryNorm.zero_center_or_radial a b B e f N hN hxy
  have Hxz := QuinticQuadraticBinaryNorm.zero_center_or_radial a c C e g N hN hxz
  have ha : a ≠ 0 := by
    intro ha
    have hb : b=0 := by
      rcases Hxy with h0 | h1
      · exact h0.2
      · exact h1.1.symm.trans ha
    have hc : c=0 := by
      rcases Hxz with h0 | h1
      · exact h0.2
      · exact h1.1.symm.trans ha
    rcases hA with hA | hA | hA
    · exact hA ha
    · exact hA hb
    · exact hA hc
  obtain ⟨hab,hef,hB⟩ := Hxy.resolve_left (fun hz ↦ ha hz.1)
  obtain ⟨hac,heg,hC⟩ := Hxz.resolve_left (fun hz ↦ ha hz.1)
  have hb : b ≠ 0 := by rwa [← hab]
  have hD := (QuinticQuadraticBinaryNorm.radial_of_first_ne_zero
    b c D f g N hb hN hyz).2.2
  exact ⟨hab,hac,hef,heg,hB,hC,hD⟩

/-- The entire tuple depends only on the source quadratic norm. -/
theorem radial (a b c B C D e f g N : ℝ)
    (hN : N ≠ 0) (hA : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(x^2+y^2+z^2)^5) (x y z : ℝ) :
    coordinates a b c B C D e f g x y z =
      ![a*(x^2+y^2+z^2),a*(x^2+y^2+z^2),a*(x^2+y^2+z^2),
        a*(x^2+y^2+z^2),e*(x^2+y^2+z^2)] := by
  obtain ⟨hab,hac,hef,heg,hB,hC,hD⟩ :=
    coefficient_classification a b c B C D e f g N hN hA h
  funext i
  fin_cases i <;>
    simp [coordinates,← hab,← hac,← hef,← heg,hB,hC,hD] <;> ring

private theorem positive_point_conditions (a b c B C D e f g N : ℝ)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(x^2+y^2+z^2)^5)
    (hp : ∃ x y z : ℝ, ∀ i, 0 < coordinates a b c B C D e f g x y z i) :
    N ≠ 0 ∧ (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) := by
  obtain ⟨x,y,z,hp⟩ := hp
  have hs : 0 < ∑ i, coordinates a b c B C D e f g x y z i^5 := by
    exact Finset.sum_pos (fun i _ ↦ pow_pos (hp i) _) Finset.univ_nonempty
  have hN : N ≠ 0 := by
    intro hn
    rw [h x y z,hn,zero_mul] at hs
    exact lt_irrefl _ hs
  refine ⟨hN,?_⟩
  by_contra hn
  push_neg at hn
  obtain ⟨ha,hb,hc⟩ := hn
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  simp [coordinates,ha,hb,hc] at h0 h1 h2 h3
  linarith only [h0,h1,h2,h3]

/-- A single all-positive point suffices: the exceptional zero-centre branch
cannot pass through such a point. Consequently this family cannot transfer
many source-norm representations into distinct output tuples. -/
theorem constant_on_norm_fibers_of_positive_point (a b c B C D e f g N : ℝ)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(x^2+y^2+z^2)^5)
    (hp : ∃ x y z : ℝ, ∀ i, 0 < coordinates a b c B C D e f g x y z i)
    (x y z u v w : ℝ) (he : x^2+y^2+z^2=u^2+v^2+w^2) :
    coordinates a b c B C D e f g x y z =
      coordinates a b c B C D e f g u v w := by
  obtain ⟨hN,hA⟩ := positive_point_conditions a b c B C D e f g N h hp
  rw [radial a b c B C D e f g N hN hA h x y z,
    radial a b c B C D e f g N hN hA h u v w,he]

private theorem zero_center_tuple (B C D e f g x y z : ℝ)
    (hn : ∀ i, 0 ≤ coordinates 0 0 0 B C D e f g x y z i) :
    coordinates 0 0 0 B C D e f g x y z = ![0,0,0,0,e*x^2+f*y^2+g*z^2] := by
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  simp [coordinates] at h0 h1 h2 h3
  funext i
  fin_cases i <;> simp [coordinates] <;> linarith only [h0,h1,h2,h3]

private theorem nonnegative_norm_zero (v : Fin 5 → ℝ) (hv : ∀ i, 0 ≤ v i)
    (h : ∑ i, v i^5=0) : v=0 := by
  funext i
  have hi := Finset.single_le_sum (f := fun i ↦ v i^5)
    (fun i _ ↦ pow_nonneg (hv i) 5) (Finset.mem_univ i)
  rw [h] at hi
  exact eq_zero_of_pow_eq_zero (le_antisymm hi (pow_nonneg (hv i) 5))

/-- Even boundary points are covered: any two nonnegative output tuples
at the same source norm coincide. There is no positivity or nonzero-centre
assumption on the coefficient family. -/
theorem nonnegative_fiber_unique (a b c B C D e f g N : ℝ)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(x^2+y^2+z^2)^5)
    (x y z u v w : ℝ) (he : x^2+y^2+z^2=u^2+v^2+w^2)
    (hx : ∀ i, 0 ≤ coordinates a b c B C D e f g x y z i)
    (hu : ∀ i, 0 ≤ coordinates a b c B C D e f g u v w i) :
    coordinates a b c B C D e f g x y z =
      coordinates a b c B C D e f g u v w := by
  by_cases hA : a=0 ∧ b=0 ∧ c=0
  · obtain ⟨rfl,rfl,rfl⟩ := hA
    have htx := zero_center_tuple B C D e f g x y z hx
    have htu := zero_center_tuple B C D e f g u v w hu
    have hnx := h x y z
    have hnu := h u v w
    rw [htx] at hnx
    rw [htu] at hnu
    simp [Fin.sum_univ_succ] at hnx hnu
    have he5 : (e*x^2+f*y^2+g*z^2)^5=(e*u^2+f*v^2+g*w^2)^5 := by
      rw [hnx,hnu,he]
    have he' := (show Odd 5 by decide).pow_injective he5
    rw [htx,htu,he']
  · have hA' : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by tauto
    by_cases hN : N=0
    · have hzx := nonnegative_norm_zero _ hx (by rw [h x y z,hN,zero_mul])
      have hzu := nonnegative_norm_zero _ hu (by rw [h u v w,hN,zero_mul])
      exact hzx.trans hzu.symm
    · rw [radial a b c B C D e f g N hN hA' h x y z,
        radial a b c B C D e f g N hN hA' h u v w,he]

private theorem rescale_coordinates (a b c B C D e f g p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (x y z : ℝ) :
    coordinates (a/p) (b/q) (c/r) (B/(Real.sqrt p*Real.sqrt q))
      (C/(Real.sqrt p*Real.sqrt r)) (D/(Real.sqrt q*Real.sqrt r))
      (e/p) (f/q) (g/r) x y z =
    coordinates a b c B C D e f g (x/Real.sqrt p) (y/Real.sqrt q) (z/Real.sqrt r) := by
  funext i
  fin_cases i <;>
    simp [coordinates,div_eq_mul_inv,mul_pow,inv_pow,Real.sq_sqrt hp.le,
      Real.sq_sqrt hq.le,Real.sq_sqrt hr.le,mul_inv_rev] <;> ring

/-- The same conclusion for every positive definite diagonal source norm,
with no restriction on the real coefficients or on vanishing coordinates. -/
theorem diagonal_nonnegative_fiber_unique (a b c B C D e f g N p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(p*x^2+q*y^2+r*z^2)^5)
    (x y z u v w : ℝ) (he : p*x^2+q*y^2+r*z^2=p*u^2+q*v^2+r*w^2)
    (hx : ∀ i, 0 ≤ coordinates a b c B C D e f g x y z i)
    (hu : ∀ i, 0 ≤ coordinates a b c B C D e f g u v w i) :
    coordinates a b c B C D e f g x y z =
      coordinates a b c B C D e f g u v w := by
  let out := coordinates (a/p) (b/q) (c/r) (B/(Real.sqrt p*Real.sqrt q))
    (C/(Real.sqrt p*Real.sqrt r)) (D/(Real.sqrt q*Real.sqrt r))
    (e/p) (f/q) (g/r)
  have hs (x y z : ℝ) : out x y z =
      coordinates a b c B C D e f g (x/Real.sqrt p) (y/Real.sqrt q) (z/Real.sqrt r) :=
    rescale_coordinates a b c B C D e f g p q r hp hq hr x y z
  have hnorm (x y z : ℝ) : ∑ i, out x y z i^5=N*(x^2+y^2+z^2)^5 := by
    rw [hs,h]
    simp only [div_pow,Real.sq_sqrt hp.le,Real.sq_sqrt hq.le,Real.sq_sqrt hr.le]
    congr 2
    field_simp
  have hback (x y z : ℝ) : out (Real.sqrt p*x) (Real.sqrt q*y) (Real.sqrt r*z) =
      coordinates a b c B C D e f g x y z := by
    rw [hs]
    simp [mul_div_cancel_left₀,(Real.sqrt_pos.mpr hp).ne',
      (Real.sqrt_pos.mpr hq).ne',(Real.sqrt_pos.mpr hr).ne']
  have he' : (Real.sqrt p*x)^2+(Real.sqrt q*y)^2+(Real.sqrt r*z)^2 =
      (Real.sqrt p*u)^2+(Real.sqrt q*v)^2+(Real.sqrt r*w)^2 := by
    simpa only [mul_pow,Real.sq_sqrt hp.le,Real.sq_sqrt hq.le,Real.sq_sqrt hr.le] using he
  have hz := nonnegative_fiber_unique (a/p) (b/q) (c/r)
    (B/(Real.sqrt p*Real.sqrt q)) (C/(Real.sqrt p*Real.sqrt r))
    (D/(Real.sqrt q*Real.sqrt r)) (e/p) (f/q) (g/r) N hnorm
    (Real.sqrt p*x) (Real.sqrt q*y) (Real.sqrt r*z)
    (Real.sqrt p*u) (Real.sqrt q*v) (Real.sqrt r*w) he'
    (by change ∀ i, 0 ≤ out _ _ _ i; rwa [hback])
    (by change ∀ i, 0 ≤ out _ _ _ i; rwa [hback])
  change out _ _ _ = out _ _ _ at hz
  simpa only [hback] using hz

/-- Sign symmetry forces all mixed coefficients of a nonzero quadratic
norm target to vanish. -/
theorem source_is_diagonal (a b c B C D e f g N p q r L M T : ℝ)
    (hN : N ≠ 0)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(p*x^2+q*y^2+r*z^2+L*x*y+M*x*z+T*y*z)^5) : L=0 ∧ M=0 ∧ T=0 := by
  have hL : L=0 := by
    have hx := h 1 1 0
    have hy := h (-1) 1 0
    norm_num [coordinates,Fin.sum_univ_succ] at hx hy
    have hz : N*((p+q+L)^5-(p+q-L)^5)=0 := by linear_combination -hx+hy
    have he := (show Odd 5 by decide).pow_injective
      (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hN))
    linarith only [he]
  have hM : M=0 := by
    have hx := h 1 0 1
    have hy := h (-1) 0 1
    norm_num [coordinates,Fin.sum_univ_succ] at hx hy
    have hz : N*((p+r+M)^5-(p+r-M)^5)=0 := by linear_combination -hx+hy
    have he := (show Odd 5 by decide).pow_injective
      (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hN))
    linarith only [he]
  have hT : T=0 := by
    have hx := h 0 1 1
    have hy := h 0 (-1) 1
    norm_num [coordinates,Fin.sum_univ_succ] at hx hy
    have hz : N*((q+r+T)^5-(q+r-T)^5)=0 := by linear_combination -hx+hy
    have he := (show Odd 5 by decide).pow_injective
      (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hN))
    linarith only [he]
  exact ⟨hL,hM,hT⟩

/-- Uniform conclusion for a general quadratic source with positive diagonal
coefficients, in particular for every positive definite real source form.
The output family is still the specified sign-symmetric family. -/
theorem quadratic_nonnegative_fiber_unique (a b c B C D e f g N p q r L M T : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : ∀ x y z : ℝ, ∑ i, coordinates a b c B C D e f g x y z i^5 =
      N*(p*x^2+q*y^2+r*z^2+L*x*y+M*x*z+T*y*z)^5)
    (x y z u v w : ℝ)
    (he : p*x^2+q*y^2+r*z^2+L*x*y+M*x*z+T*y*z =
      p*u^2+q*v^2+r*w^2+L*u*v+M*u*w+T*v*w)
    (hx : ∀ i, 0 ≤ coordinates a b c B C D e f g x y z i)
    (hu : ∀ i, 0 ≤ coordinates a b c B C D e f g u v w i) :
    coordinates a b c B C D e f g x y z =
      coordinates a b c B C D e f g u v w := by
  by_cases hN : N=0
  · have hzx := nonnegative_norm_zero _ hx (by rw [h x y z,hN,zero_mul])
    have hzu := nonnegative_norm_zero _ hu (by rw [h u v w,hN,zero_mul])
    exact hzx.trans hzu.symm
  · obtain ⟨rfl,rfl,rfl⟩ := source_is_diagonal a b c B C D e f g N p q r L M T hN h
    simp only [zero_mul,add_zero] at h he
    exact diagonal_nonnegative_fiber_unique a b c B C D e f g N p q r hp hq hr h
      x y z u v w he hx hu

end
end Erdos322Research.QuinticQuadraticSignFamily
