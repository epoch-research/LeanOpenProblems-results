import FormalConjecturesUtil

/-! Circle-incidence identities for a restricted Clifford family.
These are not a general-position or cardinality-growth theorem. -/
namespace Erdos213.CliffordCircle
noncomputable section

lemma norm_switch (h : ℝ) {u : ℂ} (hu : ‖u‖ = 1) :
    ‖1 + (h : ℂ)*u‖ = ‖(h : ℂ)+u‖ := by
  have hx : u.re*u.re + u.im*u.im = 1 := by
    simpa [Complex.normSq_apply, hu] using Complex.normSq_eq_norm_sq u
  have he : Complex.normSq (1+(h : ℂ)*u) = Complex.normSq ((h : ℂ)+u) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im]
    linear_combination (h^2-1)*hx
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at he
  nlinarith [norm_nonneg (1+(h : ℂ)*u), norm_nonneg ((h : ℂ)+u)]

def pairPoint (h u v : ℂ) : ℂ := h*(1+u*v)+u+v

lemma pairPoint_sub (h u v : ℂ) :
    pairPoint h u v - (h+u) = v*(1+h*u) := by
  unfold pairPoint
  ring

lemma pairPoint_on_circle (h : ℝ) {u v : ℂ} (hu : ‖u‖=1) (hv : ‖v‖=1) :
    dist (pairPoint h u v) ((h : ℂ)+u) = ‖(h : ℂ)+u‖ := by
  rw [dist_eq_norm, pairPoint_sub, norm_mul, hv, one_mul, norm_switch h hu]

def flip (h u : ℂ) : ℂ := -(h+u)/(1+h*u)

lemma flip_unit (h : ℝ) {u : ℂ} (hu : ‖u‖=1) (hd : 1+(h : ℂ)*u ≠ 0) :
    ‖flip h u‖=1 := by
  rw [flip, norm_div, norm_neg, ← norm_switch h hu]
  exact div_self (norm_ne_zero_iff.mpr hd)

lemma flip_product (h u : ℂ) (hd : 1+h*u ≠ 0) :
    (1+h*u)*(1+h*flip h u) = 1-h^2 := by
  unfold flip
  field_simp
  ring

lemma flip_involution (h u : ℂ) (hd : 1+h*u ≠ 0) (hh : 1-h^2 ≠ 0) :
    flip h (flip h u) = u := by
  have hf : 1+h*flip h u ≠ 0 := by
    intro hz
    have he := flip_product h u hd
    rw [hz,mul_zero] at he
    exact hh he.symm
  change -(h+flip h u)/(1+h*flip h u)=u
  apply (div_eq_iff hf).mpr
  unfold flip
  field_simp
  ring

def offset (h : ℂ) : ℂ := h-1/h

def evenPoint (h P : ℂ) (k : ℕ) : ℂ :=
  offset h + (1-h^2)*P/(h*(1-h^2)^k)

def oddCenter (h P : ℂ) (k : ℕ) : ℂ :=
  offset h + P/(h*(1-h^2)^k)

lemma even_empty (h : ℂ) (hh : h ≠ 0) : evenPoint h 1 0 = 0 := by
  unfold evenPoint offset
  field_simp
  ring

lemma even_two (h u v : ℂ) (hh : h ≠ 0) (hd : 1-h^2 ≠ 0) :
    evenPoint h ((1+h*u)*(1+h*v)) 1 = pairPoint h u v := by
  unfold evenPoint offset pairPoint
  field_simp
  ring

lemma added_neighbor (h P u : ℂ) (k : ℕ) (hh : h ≠ 0) (hd : 1-h^2 ≠ 0) :
    evenPoint h (P*(1+h*u)) (k+1) - oddCenter h P k = P/(1-h^2)^k*u := by
  unfold evenPoint oddCenter
  rw [pow_succ]
  field_simp
  ring

lemma removed_neighbor (h P u : ℂ) (k : ℕ) (hh : h ≠ 0) (hd : 1-h^2 ≠ 0)
    (hu : 1+h*u ≠ 0) :
    evenPoint h (P/(1+h*u)) k - oddCenter h P k =
      P/(1-h^2)^k*flip h u := by
  unfold evenPoint oddCenter flip
  field_simp
  ring

lemma added_neighbor_dist (h : ℝ) (P : ℂ) {u : ℂ} (k : ℕ) (hh : h ≠ 0)
    (hd : 1-h^2 ≠ 0) (hu : ‖u‖=1) :
    dist (evenPoint h (P*(1+(h : ℂ)*u)) (k+1)) (oddCenter h P k) =
      ‖P‖ / |1-h^2|^k := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hd' : 1-(h : ℂ)^2 ≠ 0 := by exact_mod_cast hd
  rw [dist_eq_norm, added_neighbor _ _ _ _ hh' hd', norm_mul, hu, mul_one,
    norm_div, norm_pow]
  norm_cast

lemma removed_neighbor_dist (h : ℝ) (P : ℂ) {u : ℂ} (k : ℕ) (hh : h ≠ 0)
    (hd : 1-h^2 ≠ 0) (hu : ‖u‖=1) (hden : 1+(h : ℂ)*u ≠ 0) :
    dist (evenPoint h (P/(1+(h : ℂ)*u)) k) (oddCenter h P k) =
      ‖P‖ / |1-h^2|^k := by
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have hd' : 1-(h : ℂ)^2 ≠ 0 := by exact_mod_cast hd
  rw [dist_eq_norm, removed_neighbor _ _ _ _ hh' hd' hden, norm_mul,
    flip_unit h hu hden, mul_one, norm_div, norm_pow]
  norm_cast

lemma inverse_pair_collision (h P u : ℂ) (k : ℕ) (hh : h ≠ 0)
    (hd : 1-h^2 ≠ 0) (hu : 1+h*u ≠ 0) :
    evenPoint h (P*((1+h*u)*(1+h*flip h u))) (k+1) = evenPoint h P k := by
  rw [flip_product h u hu]
  unfold evenPoint
  rw [pow_succ]
  field_simp
  simp only [pow_succ]
  ring


private lemma collinear_of_phase (a b c q : ℂ)
    (hb : starRingEnd ℂ (b-a)=q*(b-a))
    (hc : starRingEnd ℂ (c-a)=q*(c-a)) : Collinear ℝ {a,b,c} := by
  by_cases hca : c=a
  · subst c
    convert (collinear_pair ℝ a b) using 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hd : c-a ≠ 0 := sub_ne_zero.mpr hca
  have hbar : starRingEnd ℂ (c-a) ≠ 0 := by
    intro he
    apply hd
    apply (starRingEnd ℂ).injective
    simpa only [map_zero] using he
  have he : starRingEnd ℂ ((b-a)/(c-a)) = (b-a)/(c-a) := by
    rw [map_div₀]
    apply (div_eq_div_iff hbar hd).mpr
    rw [hb,hc]
    ring
  have him := Complex.conj_eq_iff_im.mp he
  have hr : (((b-a)/(c-a)).re : ℂ) = (b-a)/(c-a) := by
    apply Complex.ext <;> simp [him]
  apply (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℂ))).mpr
  refine ⟨c-a, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hpa | hpb | hpc
  · subst p
    exact ⟨0, by simp⟩
  · subst p
    refine ⟨((b-a)/(c-a)).re, ?_⟩
    rw [vadd_eq_add, Complex.real_smul, hr, div_mul_cancel₀ _ hd]
    ring
  · subst p
    exact ⟨1, by simp⟩

lemma pair_triple_collinear_at_one {u v w : ℂ}
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    Collinear ℝ {pairPoint 1 u v, pairPoint 1 u w, pairPoint 1 v w} := by
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hv0 : v ≠ 0 := by intro he; simp [he] at hv
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  apply collinear_of_phase _ _ _ (-(u*v*w)⁻¹)
  all_goals
    unfold pairPoint
    simp only [map_sub, map_add, map_mul, map_one,
      ← Complex.inv_eq_conj hu, ← Complex.inv_eq_conj hv, ← Complex.inv_eq_conj hw]
    field_simp
    ring

#print axioms pairPoint_on_circle
#print axioms flip_involution
#print axioms added_neighbor_dist
#print axioms removed_neighbor_dist
#print axioms inverse_pair_collision
#print axioms pair_triple_collinear_at_one
end
end Erdos213.CliffordCircle
