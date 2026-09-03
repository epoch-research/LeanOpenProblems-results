import Submission.CubicRadicalFermat

/-!
Arithmetic restrictions on rational tangent directions to the all-positive
Fermat quartic. These are not representation-count estimates.
-/
namespace Erdos322Research.QuarticRationalTangency

open CubicRadicalFermat

private def bin (x : Fin 4 → ℝ) (f : Fin 4 → Fin 3) (j : Fin 3) : ℝ :=
  ∑ i, if f i=j then x i^4 else 0

set_option maxHeartbeats 3000000 in
private theorem no_equal_three_bins (x : Fin 4 → ℝ) (a : Fin 4 → ℚ)
    (hc : ∀ i, x i^3=(a i : ℝ)) (hn : ∀ i, x i ≠ 0)
    (f : Fin 4 → Fin 3) : ¬ (bin x f 0=bin x f 1 ∧ bin x f 0=bin x f 2) := by
  rintro ⟨h1,h2⟩
  have hpos (i : Fin 4) : 0 < x i^4 := pow_pos (sq_pos_of_ne_zero (hn i)) 2 |>.trans_eq (by ring)
  have hf (i j k : Fin 4) : x i^4+x j^4 ≠ x k^4 :=
    no_fourth_fermat_with_rational_cubes _ _ _ _ _ _ (hc i) (hc j) (hc k)
      (hn i) (hn j) (hn k)
  have hp0 := hpos 0
  have hp1 := hpos 1
  have hp2 := hpos 2
  have hp3 := hpos 3
  generalize he0 : f 0 = i0 at *
  generalize he1 : f 1 = i1 at *
  generalize he2 : f 2 = i2 at *
  generalize he3 : f 3 = i3 at *
  fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i3
  all_goals simp [bin, Fin.sum_univ_four, he0, he1, he2, he3] at h1 h2
  all_goals first
    | exact hn 0 h1
    | exact hn 0 h2
    | exact hn 1 h1
    | exact hn 1 h2
    | exact hn 2 h1
    | exact hn 2 h2
    | exact hn 3 h1
    | exact hn 3 h2
    | linarith only [h1,h2,hp0,hp1,hp2,hp3]
    | exact hf 0 1 2 (by linarith only [h1,h2])
    | exact hf 0 1 3 (by linarith only [h1,h2])
    | exact hf 0 2 1 (by linarith only [h1,h2])
    | exact hf 0 2 3 (by linarith only [h1,h2])
    | exact hf 0 3 1 (by linarith only [h1,h2])
    | exact hf 0 3 2 (by linarith only [h1,h2])
    | exact hf 1 2 0 (by linarith only [h1,h2])
    | exact hf 1 2 3 (by linarith only [h1,h2])
    | exact hf 1 3 0 (by linarith only [h1,h2])
    | exact hf 1 3 2 (by linarith only [h1,h2])
    | exact hf 2 3 0 (by linarith only [h1,h2])

private noncomputable def ω : ℂ := ⟨-1/2, Real.sqrt 3/2⟩

private theorem omega_square : ω^2 = ⟨-1/2, -Real.sqrt 3/2⟩ := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [ω, pow_two, Complex.mul_re, Complex.mul_im]
  · nlinarith
  · ring

private theorem omega_relation : ω^2+ω+1=0 := by
  rw [omega_square]
  apply Complex.ext <;> simp [ω] <;> ring

private theorem omega_cube : ω^3=1 := by
  linear_combination (ω-1)*omega_relation

private theorem cube_root_phase (w : ℂ) (hw : w^3=1) :
    ∃ j : Fin 3, w=ω^(j : ℕ) := by
  have hf : (w-1)*(w-ω)*(w-ω^2)=0 := by
    linear_combination hw - (w^2-w)*omega_relation + (w-1)*omega_cube
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by simpa using sub_eq_zero.mp h⟩
    · exact ⟨1, by simpa using sub_eq_zero.mp h⟩
  · exact ⟨2, by simpa using sub_eq_zero.mp h⟩

private theorem norm_cube_rat (z : ℂ) (a : ℚ) (hz : z^3=(a : ℂ)) :
    ‖z‖^3=((|a| : ℚ) : ℝ) := by
  have h := congrArg norm hz
  simpa only [norm_pow, Complex.norm_ratCast, Rat.cast_abs] using h

private theorem fourth_power_phase (z : ℂ) (a : ℚ)
    (hz : z^3=(a : ℂ)) (hn : z ≠ 0) :
    ∃ j : Fin 3, z^4=((‖z‖^4 : ℝ) : ℂ)*ω^(j : ℕ) := by
  let D : ℂ := ((‖z‖^4 : ℝ) : ℂ)
  have hD : D ≠ 0 := by dsimp [D]; exact_mod_cast pow_ne_zero 4 (norm_ne_zero_iff.mpr hn)
  have hc : D^3=(a : ℂ)^4 := by
    calc
      D^3 = (((‖z‖^3)^4 : ℝ) : ℂ) := by dsimp [D]; push_cast; ring
      _ = (((((|a| : ℚ) : ℝ))^4 : ℝ) : ℂ) := by rw [norm_cube_rat z a hz]
      _ = (a : ℂ)^4 := by
        rw [Rat.cast_abs, ← abs_pow, abs_of_nonneg (by positivity)]
        push_cast
        rfl
  have hroot : (z^4/D)^3=1 := by
    rw [div_pow, show (z^4)^3=(z^3)^4 by ring, hz, hc,
      div_self (by rw [← hc]; exact pow_ne_zero 3 hD)]
  obtain ⟨j,hj⟩ := cube_root_phase (z^4/D) hroot
  refine ⟨j, ?_⟩
  have he := (div_eq_iff hD).mp hj
  simpa only [mul_comm] using he

private theorem phase_sum_grouped (x : Fin 4 → ℝ) (f : Fin 4 → Fin 3) :
    (∑ i, ((x i^4 : ℝ) : ℂ)*ω^(f i : ℕ)) =
      (bin x f 0 : ℂ)+(bin x f 1 : ℂ)*ω+(bin x f 2 : ℂ)*ω^2 := by
  have ht (i : Fin 4) : ((x i^4 : ℝ) : ℂ)*ω^(f i : ℕ) =
      ((if f i=0 then x i^4 else 0 : ℝ) : ℂ) +
      ((if f i=1 then x i^4 else 0 : ℝ) : ℂ)*ω +
      ((if f i=2 then x i^4 else 0 : ℝ) : ℂ)*ω^2 := by
    generalize h : f i=j
    fin_cases j <;> norm_num [Fin.ext_iff]
  simp_rw [ht]
  simp [bin, Finset.sum_add_distrib, Finset.sum_mul]

private theorem zero_phase_sum_bins (x : Fin 4 → ℝ) (f : Fin 4 → Fin 3)
    (hs : (∑ i, ((x i^4 : ℝ) : ℂ)*ω^(f i : ℕ))=0) :
    bin x f 0=bin x f 1 ∧ bin x f 0=bin x f 2 := by
  rw [phase_sum_grouped] at hs
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  rw [omega_square] at hr hi
  norm_num [ω, Complex.mul_re, Complex.mul_im] at hr hi
  have hm : Real.sqrt 3*(bin x f 1-bin x f 2)=0 := by
    linear_combination 2*hi
  have he : bin x f 1=bin x f 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (Real.sqrt_ne_zero'.mpr (by norm_num)))
  constructor <;> linarith

/-- Four nonzero complex numbers with rational cubes cannot sum to zero
in fourth powers. This is an arithmetic restriction, not a point-count bound. -/
theorem fourth_sum_ne_zero_of_rational_cubes (z : Fin 4 → ℂ) (a : Fin 4 → ℚ)
    (hc : ∀ i, z i^3=(a i : ℂ)) (hn : ∀ i, z i ≠ 0) :
    ∑ i, z i^4 ≠ 0 := by
  intro hs
  choose f hf using fun i => fourth_power_phase (z i) (a i) (hc i) (hn i)
  have he : (∑ i, ((‖z i‖^4 : ℝ) : ℂ)*ω^(f i : ℕ))=0 := by
    simpa only [← hf] using hs
  exact no_equal_three_bins (fun i => ‖z i‖) (fun i => |a i|)
    (fun i => norm_cube_rat _ _ (hc i)) (fun i => norm_ne_zero_iff.mpr (hn i)) f
    (zero_phase_sum_bins _ _ he)

/-- A nonzero point on the all-positive complex Fermat quartic whose cubic
coordinates are proportional to rational numbers has a zero coordinate. -/
theorem rational_tangent_has_zero_coordinate (z : Fin 4 → ℂ) (a : Fin 4 → ℚ)
    (t : ℂ) (hc : ∀ i, z i^3=t*(a i : ℂ)) (hs : ∑ i, z i^4=0) :
    ∃ i, z i=0 := by
  by_contra hn
  push_neg at hn
  have h0 : t*(a 0 : ℂ) ≠ 0 := by rw [← hc 0]; exact pow_ne_zero 3 (hn 0)
  have ht := (mul_ne_zero_iff.mp h0).1
  have ha0 := (mul_ne_zero_iff.mp h0).2
  have hc' (i : Fin 4) : (z i/z 0)^3=((a i/a 0 : ℚ) : ℂ) := by
    rw [div_pow, hc i, hc 0]
    push_cast
    field_simp
  have hs' : ∑ i, (z i/z 0)^4=0 := by
    simp only [div_pow, ← Finset.sum_div, hs, zero_div]
  exact fourth_sum_ne_zero_of_rational_cubes (fun i => z i/z 0)
    (fun i => a i/a 0) hc' (fun i => div_ne_zero (hn i) (hn 0)) hs'

/-- If all four rational normal coefficients are nonzero, the corresponding
plane has no nonzero tangency point on the all-positive Fermat quartic. -/
theorem no_tangency_with_all_coefficients_nonzero (z : Fin 4 → ℂ)
    (a : Fin 4 → ℚ) (ha : ∀ i, a i ≠ 0) (t : ℂ)
    (hc : ∀ i, z i^3=t*(a i : ℂ)) (hs : ∑ i, z i^4=0) : ∀ i, z i=0 := by
  obtain ⟨j,hj⟩ := rational_tangent_has_zero_coordinate z a t hc hs
  have ht : t=0 := by
    have he := hc j
    rw [hj, zero_pow (by decide : 3 ≠ 0)] at he
    exact (mul_eq_zero.mp he.symm).resolve_right (by exact_mod_cast ha j)
  intro i
  apply eq_zero_of_pow_eq_zero (n := 3)
  simpa [ht] using hc i

/-- The corresponding Lagrange-multiplier criterion for a rational hyperplane
section. The conclusion excludes nonzero critical points, but does not bound
integral points on a nonzero level. -/
theorem rational_hyperplane_critical_zero (z : Fin 4 → ℂ)
    (a : Fin 4 → ℚ) (ha : ∀ i, a i ≠ 0) (t : ℂ)
    (hc : ∀ i, z i^3=t*(a i : ℂ))
    (hplane : ∑ i, (a i : ℂ)*z i=0) : ∀ i, z i=0 := by
  apply no_tangency_with_all_coefficients_nonzero z a ha t hc
  calc
    ∑ i, z i^4 = ∑ i, (t*(a i : ℂ))*z i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show z i^4=z i^3*z i by ring, hc i]
    _ = t*∑ i, (a i : ℂ)*z i := by simp only [Finset.mul_sum, mul_assoc]
    _ = 0 := by rw [hplane, mul_zero]

private def bin3 (w : Fin 3 → ℝ) (f : Fin 3 → Fin 3) (j : Fin 3) : ℝ :=
  ∑ i, if f i=j then w i else 0

set_option maxHeartbeats 1000000 in
private theorem three_equal_bins (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : Fin 3 → Fin 3) (hb1 : bin3 w f 0=bin3 w f 1)
    (hb2 : bin3 w f 0=bin3 w f 2) : ∀ i j, w i=w j := by
  have hpair : w 0=w 1 ∧ w 1=w 2 := by
    have h0 := hw 0
    have h1 := hw 1
    have h2 := hw 2
    generalize he0 : f 0=i0 at *
    generalize he1 : f 1=i1 at *
    generalize he2 : f 2=i2 at *
    fin_cases i0 <;> fin_cases i1 <;> fin_cases i2
    all_goals simp [bin3, Fin.sum_univ_three, he0, he1, he2] at hb1 hb2
    all_goals constructor <;> linarith only [hb1,hb2,h0,h1,h2]
  have hall (i : Fin 3) : w i=w 0 := by
    fin_cases i
    · rfl
    · exact hpair.1.symm
    · exact (hpair.1.trans hpair.2).symm
  intro i j
  exact (hall i).trans (hall j).symm

private theorem fourth_power_phase_all (z : ℂ) (a : ℚ) (hz : z^3=(a : ℂ)) :
    ∃ j : Fin 3, z^4=((‖z‖^4 : ℝ) : ℂ)*ω^(j : ℕ) := by
  by_cases hn : z=0
  · exact ⟨0, by simp [hn]⟩
  · exact fourth_power_phase z a hz hn

/-- On a zero quartic level with rational cubes, if one coordinate is zero,
the other three have equal complex norms (possibly all zero). -/
theorem equal_norms_away_from_zero_of_rational_cubes (z : Fin 4 → ℂ)
    (a : Fin 4 → ℚ) (hc : ∀ i, z i^3=(a i : ℂ))
    (hs : ∑ i, z i^4=0) (j : Fin 4) (hj : z j=0) :
    ∀ i l, i ≠ j → l ≠ j → ‖z i‖=‖z l‖ := by
  choose f hf using fun i => fourth_power_phase_all (z i) (a i) (hc i)
  have he : (∑ i, ((‖z i‖^4 : ℝ) : ℂ)*ω^(f i : ℕ))=0 := by
    simpa only [← hf] using hs
  obtain ⟨h1,h2⟩ := zero_phase_sum_bins (fun i => ‖z i‖) f he
  let w : Fin 3 → ℝ := fun i => ‖z (j.succAbove i)‖^4
  let g : Fin 3 → Fin 3 := fun i => f (j.succAbove i)
  have hbin (r : Fin 3) : bin (fun i => ‖z i‖) f r=bin3 w g r := by
    unfold bin
    rw [Fin.sum_univ_succAbove _ j]
    simp [hj, bin3, w, g]
  rw [hbin 0, hbin 1] at h1
  rw [hbin 0, hbin 2] at h2
  have hw := three_equal_bins w (fun _ => by dsimp [w]; positivity) g h1 h2
  intro i l hi hl
  obtain ⟨u,rfl⟩ := Fin.exists_succAbove_eq hi
  obtain ⟨v,rfl⟩ := Fin.exists_succAbove_eq hl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : 4 ≠ 0)).mp (hw u v)

/-- A rational tangent normal at a nonzero point has exactly one zero entry;
the other three entries agree up to sign and a common nonzero rational scale. -/
theorem rational_tangent_normal_classification (z : Fin 4 → ℂ) (a : Fin 4 → ℚ)
    (t : ℂ) (hc : ∀ i, z i^3=t*(a i : ℂ)) (hs : ∑ i, z i^4=0)
    (hn : ∃ k, z k ≠ 0) :
    ∃ j : Fin 4, a j=0 ∧ ∃ b : ℚ, b ≠ 0 ∧
      ∀ i, i ≠ j → a i=b ∨ a i=-b := by
  obtain ⟨k,hk⟩ := hn
  have htk : t*(a k : ℂ) ≠ 0 := by rw [← hc k]; exact pow_ne_zero 3 hk
  have ht := (mul_ne_zero_iff.mp htk).1
  have hakc := (mul_ne_zero_iff.mp htk).2
  have hak : a k ≠ 0 := by exact_mod_cast hakc
  obtain ⟨j,hj⟩ := rational_tangent_has_zero_coordinate z a t hc hs
  have haj : a j=0 := by
    have he := hc j
    rw [hj, zero_pow (by decide : 3 ≠ 0)] at he
    exact_mod_cast (mul_eq_zero.mp he.symm).resolve_left ht
  have hkj : k ≠ j := by intro he; exact hk (he ▸ hj)
  let u : Fin 4 → ℂ := fun i => z i/z k
  have hcu (i : Fin 4) : u i^3=((a i/a k : ℚ) : ℂ) := by
    dsimp [u]
    rw [div_pow, hc i, hc k]
    push_cast
    field_simp
  have hsu : ∑ i, u i^4=0 := by
    simp only [u, div_pow, ← Finset.sum_div, hs, zero_div]
  have huj : u j=0 := by simp [u,hj]
  have hnrm (i : Fin 4) (hi : i ≠ j) : ‖z i‖=‖z k‖ := by
    have he := equal_norms_away_from_zero_of_rational_cubes u (fun i => a i/a k)
      hcu hsu j huj i k hi hkj
    simp only [u, norm_div] at he
    have he' := congrArg (fun r : ℝ => r*‖z k‖) he
    simpa only [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hk)] using he'
  refine ⟨j,haj,a k,hak,?_⟩
  intro i hi
  have hi' := congrArg norm (hc i)
  have hk' := congrArg norm (hc k)
  simp only [norm_pow, norm_mul, Complex.norm_ratCast] at hi' hk'
  rw [hnrm i hi] at hi'
  have he : |(a i : ℝ)|=|(a k : ℝ)| :=
    mul_left_cancel₀ (norm_ne_zero_iff.mpr ht) (hi'.symm.trans hk')
  have he' : |a i|=|a k| := by exact_mod_cast he
  exact abs_eq_abs.mp he'

/-- The standard additive-triple normal is attained by a nonzero complex
point of the Fermat quartic. -/
theorem standard_additive_tangency :
    ∃ z : Fin 4 → ℂ, (∃ i, z i ≠ 0) ∧ (∑ i, z i^4=0) ∧
      ∀ i, z i^3=((![1,1,-1,0] : Fin 4 → ℚ) i : ℂ) := by
  have h4 : ω^4=ω := by rw [show 4=3+1 by decide, pow_succ, omega_cube, one_mul]
  have h6 : ω^6=1 := by rw [show 6=3*2 by decide, pow_mul, omega_cube, one_pow]
  have h8 : ω^8=ω^2 := by rw [show 8=4*2 by decide, pow_mul, h4]
  refine ⟨![1,ω,-ω^2,0], ⟨0,by simp⟩, ?_, ?_⟩
  · rw [Fin.sum_univ_four]
    change (1:ℂ)^4+ω^4+(-ω^2)^4+0^4=0
    norm_num [neg_pow, ← pow_mul, h4, h8]
    linear_combination omega_relation
  · intro i
    fin_cases i <;> norm_num [neg_pow, ← pow_mul, omega_cube, h6]

end Erdos322Research.QuarticRationalTangency
