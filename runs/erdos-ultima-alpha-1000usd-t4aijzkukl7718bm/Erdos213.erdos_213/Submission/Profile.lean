import FormalConjecturesUtil

/-!
# Erdős Problem 213

*Reference:* [erdosproblems.com/213](https://www.erdosproblems.com/213)
-/

open EuclideanGeometry

namespace Erdos213

/--
The predicate (on $n$) that there exist $n$ points in $\mathbb{R}^2$,
no three on a line and no four on a circle,
such that all pairwise distances are integers.
-/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

lemma Erdos213For.mono {m n : ℕ} (h : Erdos213For n) (hmn : m ≤ n) :
    Erdos213For m := by
  rcases h with ⟨S, hfin, hcard, htri, hcirc, hdist⟩
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq (hcard ▸ hmn)
  exact ⟨T, hfin.subset hTS, hTcard, htri.mono hTS,
    fun Q hQ => hcirc Q ⟨hQ.1.trans hTS, hQ.2⟩, hdist.mono hTS⟩

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private def p4 : Fin 4 → ℝ² := ![!₂[(3 : ℝ), 0], !₂[-3, 0], !₂[0, 4], !₂[0, -4]]

private lemma p4_injective : Function.Injective p4 := by
  intro i j h
  have h0 := congrArg (fun p : ℝ² => p 0) h
  have h1 := congrArg (fun p : ℝ² => p 1) h
  fin_cases i <;> fin_cases j <;> norm_num [p4] at *

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private lemma p4_nontrilinear : NonTrilinear (Set.range p4) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ hij hjk hik hcol
  have h := collinear_det_zero hcol
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [p4] at *

private lemma p4_not_cospherical : ¬ Cospherical (Set.range p4) := by
  rintro ⟨c, r, h⟩
  have h0 := congrArg (fun x : ℝ => x^2) (h _ (Set.mem_range_self 0))
  have h1 := congrArg (fun x : ℝ => x^2) (h _ (Set.mem_range_self 1))
  have h2 := congrArg (fun x : ℝ => x^2) (h _ (Set.mem_range_self 2))
  have h3 := congrArg (fun x : ℝ => x^2) (h _ (Set.mem_range_self 3))
  simp only [p4_dist_sq] at h0 h1 h2 h3
  change (0 - c 0)^2 + (4 - c 1)^2 = r^2 at h2
  change (0 - c 0)^2 + (-4 - c 1)^2 = r^2 at h3
  norm_num [p4] at h0 h1 h2 h3
  nlinarith

private lemma p4_distances : (Set.range p4).Pairwise
    (fun a b => dist a b ∈ Set.range Int.cast) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  fin_cases i <;> fin_cases j <;>
    norm_num [p4, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq] at *
  all_goals solve
  | (refine ⟨5, ?_⟩; norm_num)
  | (refine ⟨6, ?_⟩; norm_num)
  | (refine ⟨8, ?_⟩; norm_num)

lemma erdos213For_four : Erdos213For 4 := by
  have hc : (Set.range p4).ncard = 4 := by
    rw [Set.ncard_range_of_injective p4_injective]
    simp
  refine ⟨Set.range p4, Set.finite_range _, hc, p4_nontrilinear, ?_, p4_distances⟩
  intro Q hQ
  have heq := Set.eq_of_subset_of_ncard_le hQ.1 (by omega : (Set.range p4).ncard ≤ Q.ncard)
  simpa [heq] using p4_not_cospherical

/-- A finite set of rational real numbers admits a positive common denominator. -/
lemma finite_common_denominator {T : Set ℝ} (hT : T.Finite)
    (hQ : T ⊆ Set.range ((↑) : ℚ → ℝ)) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ T, (D : ℝ) * x ∈ Set.range ((↑) : ℤ → ℝ) := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, by omega, by simp⟩
  | @insert x T hx hT ih =>
    obtain ⟨D, hD, hd⟩ := ih (fun y hy => hQ (Set.mem_insert_of_mem _ hy))
    obtain ⟨q, rfl⟩ := hQ (Set.mem_insert x T)
    refine ⟨q.den * D, Nat.mul_pos q.den_pos hD, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · refine ⟨(D : ℤ) * q.num, ?_⟩
      have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
      rw [Rat.cast_def]
      push_cast
      field_simp
    · obtain ⟨z, hz⟩ := hd y hy
      refine ⟨(q.den : ℤ) * z, ?_⟩
      push_cast
      rw [hz]
      ring

private lemma collinear_scale_image {T : Set ℝ²} (h : Collinear ℝ T) (c : ℝ) :
    Collinear ℝ ((fun x : ℝ² => c • x) '' T) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h ⊢
  obtain ⟨o, v, h⟩ := h
  refine ⟨c • o, c • v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, rfl⟩ := h x hx
  refine ⟨r, ?_⟩
  simp [smul_add, smul_smul, mul_comm]

private lemma cospherical_scale_image {T : Set ℝ²} (h : Cospherical T) (c : ℝ) :
    Cospherical ((fun x : ℝ² => c • x) '' T) := by
  obtain ⟨o, r, h⟩ := h
  refine ⟨c • o, ‖c‖ * r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [dist_smul₀, h x hx]

lemma general_position_scale {T : Set ℝ²} (h : InGeneralPosition T) {c : ℝ}
    (hc : c ≠ 0) : InGeneralPosition ((fun x : ℝ² => c • x) '' T) := by
  have hi : Function.Injective (fun x : ℝ² => c⁻¹ • x) := by
    intro x y hxy
    simpa [hc] using congrArg (fun z : ℝ² => c • z) hxy
  constructor
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hxy hyz hxz hcol
    have hback := collinear_scale_image hcol c⁻¹
    simp only [Set.image_insert_eq, Set.image_singleton, inv_smul_smul₀ hc] at hback
    exact h.1 hx hy hz (fun he => hxy (he ▸ rfl))
      (fun he => hyz (he ▸ rfl)) (fun he => hxz (he ▸ rfl)) hback
  · intro Q hQ hcard hcos
    apply h.2 ((fun x : ℝ² => c⁻¹ • x) '' Q) ?_ ?_
      (cospherical_scale_image hcos c⁻¹)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hQ hx
      simpa [hc] using hy
    · rwa [Set.ncard_image_of_injective _ hi]

/-- For a fixed finite cardinality, rational and integer distances give equivalent
existence problems: a common dilation clears all denominators. -/
lemma erdos213For_iff_rational (n : ℕ) : Erdos213For n ↔
    ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧ InGeneralPosition S ∧
      S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℚ → ℝ)) := by
  constructor
  · rintro ⟨S, hfin, hn, htri, hcircle, hdist⟩
    refine ⟨S, hfin, hn, ⟨htri, fun Q hQ h4 => hcircle Q ⟨hQ, h4⟩⟩, ?_⟩
    intro x hx y hy hxy
    obtain ⟨z, hz⟩ := hdist hx hy hxy
    exact ⟨(z : ℚ), by simpa using hz⟩
  · rintro ⟨S, hfin, hn, hgen, hdist⟩
    let T : Set ℝ := (fun p : ℝ² × ℝ² => dist p.1 p.2) '' (S ×ˢ S)
    have hTf : T.Finite := (hfin.prod hfin).image _
    have hTr : T ⊆ Set.range ((↑) : ℚ → ℝ) := by
      rintro _ ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
      by_cases hxy : x = y
      · subst y
        exact ⟨0, by simp⟩
      · exact hdist hx hy hxy
    obtain ⟨D, hD, hmul⟩ := finite_common_denominator hTf hTr
    have hDr : (0 : ℝ) < D := by exact_mod_cast hD
    have hD0 := ne_of_gt hDr
    have hinj : Function.Injective (fun x : ℝ² => (D : ℝ) • x) := by
      intro x y hxy
      simpa [hD0] using congrArg (fun z : ℝ² => (D : ℝ)⁻¹ • z) hxy
    have hg := general_position_scale hgen hD0
    refine ⟨(fun x : ℝ² => (D : ℝ) • x) '' S, hfin.image _, ?_, hg.1, ?_, ?_⟩
    · rwa [Set.ncard_image_of_injective _ hinj]
    · intro Q hQ
      exact hg.2 Q hQ.1 hQ.2
    · rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ _
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hDr]
      exact hmul _ ⟨(x,y), ⟨hx,hy⟩, rfl⟩


private lemma plane_distance_relation (a b c d : ℝ²) :
    4 * dist a b ^ 2 * dist a c ^ 2 * dist a d ^ 2 +
      (dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2) *
      (dist a b ^ 2 + dist a d ^ 2 - dist b d ^ 2) *
      (dist a c ^ 2 + dist a d ^ 2 - dist c d ^ 2) -
      dist a b ^ 2 * (dist a c ^ 2 + dist a d ^ 2 - dist c d ^ 2)^2 -
      dist a c ^ 2 * (dist a b ^ 2 + dist a d ^ 2 - dist b d ^ 2)^2 -
      dist a d ^ 2 * (dist a b ^ 2 + dist a c ^ 2 - dist b c ^ 2)^2 = 0 := by
  simp only [p4_dist_sq]
  ring

private lemma integral_triangle_gap {a b c : ℝ²} (h : ¬Collinear ℝ {a,b,c})
    (hab : dist a b ∈ Set.range ((↑) : ℤ → ℝ))
    (hbc : dist b c ∈ Set.range ((↑) : ℤ → ℝ))
    (hac : dist a c ∈ Set.range ((↑) : ℤ → ℝ)) :
    dist a c + 1 ≤ dist a b + dist b c := by
  have hs : dist a c < dist a b + dist b c :=
    dist_lt_dist_add_dist_iff.mpr (fun hb => h hb.collinear)
  obtain ⟨x,hx⟩ := hab
  obtain ⟨y,hy⟩ := hbc
  obtain ⟨z,hz⟩ := hac
  rw [← hx, ← hy, ← hz] at hs ⊢
  have hi : z < x+y := by exact_mod_cast hs
  exact_mod_cast (show z+1 ≤ x+y by omega)

private lemma integral_unit_triangle {a b c : ℝ²} (h : ¬Collinear ℝ {a,b,c})
    (hab : dist a b = 1)
    (hac : dist a c ∈ Set.range ((↑) : ℤ → ℝ))
    (hbc : dist b c ∈ Set.range ((↑) : ℤ → ℝ)) :
    dist a c = dist b c := by
  have habi : dist a b ∈ Set.range ((↑) : ℤ → ℝ) := ⟨1, by simpa using hab.symm⟩
  have h1 := integral_triangle_gap h habi hbc hac
  have h2 := integral_triangle_gap (a := b) (b := a) (c := c)
    (by simpa [Set.insert_comm] using h)
    (by simpa [dist_comm] using habi) hac hbc
  rw [dist_comm b a] at h2
  linarith

private lemma integral_unit_four_impossible {S : Set ℝ²} (htri : NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b c d : ℝ²} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : dist a b = 1) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : False := by
  have hab' : a ≠ b := by intro he; simp [he] at hab
  have hec := integral_unit_triangle (htri ha hb hc hab' hbc hac) hab
    (hint ha hc hac) (hint hb hc hbc)
  have hed := integral_unit_triangle (htri ha hb hd hab' hbd had) hab
    (hint ha hd had) (hint hb hd hbd)
  have hg := plane_distance_relation a b c d
  rw [hab, ← hec, ← hed] at hg
  have hprod : ((dist a c + dist a d)^2 - dist c d ^ 2) *
      (dist c d ^ 2 - (dist a c - dist a d)^2) = dist c d ^ 2 := by
    linear_combination hg
  have h1 := integral_triangle_gap (htri hc ha hd hac.symm had hcd)
    (hint hc ha hac.symm) (hint ha hd had) (hint hc hd hcd)
  have h2 := integral_triangle_gap (htri ha hd hc had hcd.symm hac)
    (hint ha hd had) (hint hd hc hcd.symm) (hint ha hc hac)
  have h3 := integral_triangle_gap (htri ha hc hd hac hcd had)
    (hint ha hc hac) (hint hc hd hcd) (hint ha hd had)
  rw [dist_comm c a] at h1
  rw [dist_comm d c] at h2
  obtain ⟨l, hl⟩ := hint hc hd hcd
  have hlpos : 0 < l := by exact_mod_cast (hl ▸ dist_pos.mpr hcd)
  have hlone : (1 : ℝ) ≤ dist c d := by rw [← hl]; exact_mod_cast (show 1 ≤ l by omega)
  have hsum : 2 * dist c d + 1 ≤ (dist a c + dist a d)^2 - dist c d^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ dist a c + dist a d - (dist c d + 1))
      (by positivity : 0 ≤ dist a c + dist a d + (dist c d + 1))]
  have hdiff : 2 * dist c d - 1 ≤ dist c d^2 - (dist a c - dist a d)^2 := by
    nlinarith [mul_nonneg
      (by linarith : 0 ≤ dist c d - 1 - (dist a c - dist a d))
      (by linarith : 0 ≤ dist c d - 1 + (dist a c - dist a d))]
  have hm := mul_le_mul hsum hdiff (by linarith : 0 ≤ 2 * dist c d - 1)
    (by nlinarith : 0 ≤ (dist a c + dist a d)^2 - dist c d^2)
  rw [hprod] at hm
  nlinarith

/-- A nontrilinear integral-distance set containing a unit pair has at most three points. -/
lemma ncard_le_three_of_unit_pair {S : Set ℝ²} (htri : NonTrilinear S)
    (hint : S.Pairwise (fun x y => dist x y ∈ Set.range ((↑) : ℤ → ℝ)))
    {a b : ℝ²} (ha : a ∈ S) (hb : b ∈ S) (hab : dist a b = 1) : S.ncard ≤ 3 := by
  have hab' : a ≠ b := by intro he; simp [he] at hab
  by_cases hex : ∃ c ∈ S, c ≠ a ∧ c ≠ b
  · obtain ⟨c, hc, hca, hcb⟩ := hex
    have hsub : S ⊆ {a,b,c} := by
      intro d hd
      by_cases hda : d = a
      · simp [hda]
      by_cases hdb : d = b
      · simp [hdb]
      by_cases hdc : d = c
      · simp [hdc]
      exact (integral_unit_four_impossible htri hint ha hb hc hd hab
        hca.symm (Ne.symm hda) hcb.symm (Ne.symm hdb) (Ne.symm hdc)).elim
    have hcard : ({a,b,c} : Set ℝ²).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨a,b,c,hab',hca.symm,hcb.symm,rfl⟩
    exact hcard ▸ Set.ncard_le_ncard hsub
  · have hsub : S ⊆ {a,b} := by
      intro c hc
      by_contra h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact hex ⟨c,hc,h⟩
    have hc := Set.ncard_le_ncard hsub
    have hc2 : ({a,b} : Set ℝ²).ncard = 2 := Set.ncard_pair hab'
    omega


private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

private noncomputable def latticePoint (D : ℕ) (x y : ℤ) : ℝ² := !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]

private def latticeNorm (D : ℕ) (x y x' y' : ℤ) : ℤ :=
  (x-x')^2 + (D : ℤ)*(y-y')^2

private def latticeTriangle (x y : Fin n → ℤ) (i j k : Fin n) : ℤ :=
  (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)

private def latticeCircle (D : ℕ) (x y : Fin n → ℤ) (i j k l : Fin n) : ℤ :=
  det3 (x j-x i) (y j-y i) (latticeNorm D (x i) (y i) (x j) (y j))
    (x k-x i) (y k-y i) (latticeNorm D (x i) (y i) (x k) (y k))
    (x l-x i) (y l-y i) (latticeNorm D (x i) (y i) (x l) (y l))

private lemma latticePoint_dist_sq (D : ℕ) (x y x' y' : ℤ) :
    dist (latticePoint D x y) (latticePoint D x' y')^2 = (latticeNorm D x y x' y' : ℝ) := by
  rw [p4_dist_sq]
  simp only [latticePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    latticeNorm]
  push_cast
  linear_combination ((y : ℝ)-y')^2 * (Real.sq_sqrt (show 0 ≤ (D : ℝ) by positivity))

private lemma lattice_not_collinear {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k : Fin n} (ht : latticeTriangle x y i j k ≠ 0) :
    ¬Collinear ℝ {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k)} := by
  intro h
  have hz := collinear_det_zero h
  have hz' : (latticeTriangle x y i j k : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeTriangle]
    ring
  have hn : (latticeTriangle x y i j k : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [p4_dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)

private lemma lattice_not_cospherical {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k l : Fin n} (ht : latticeCircle D x y i j k l ≠ 0) :
    ¬Cospherical {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k), latticePoint D (x l) (y l)} := by
  intro h
  have hz := cospherical_det_zero h
  simp only [latticePoint_dist_sq] at hz
  have hz' : (latticeCircle D x y i j k l : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeCircle, det3]
    ring
  have hn : (latticeCircle D x y i j k l : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma integral_configuration_certificate (D n : ℕ) (hD : 0 < D)
    (x y : Fin n → ℤ) (d : Fin n → Fin n → ℕ)
    (hinj : Function.Injective x)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → latticeTriangle x y i j k ≠ 0)
    (hcirc : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      latticeCircle D x y i j k l ≠ 0)
    (hdist : ∀ i j, latticeNorm D (x i) (y i) (x j) (y j) = (d i j : ℤ)^2) :
    Erdos213For n := by
  let p : Fin n → ℝ² := fun i => latticePoint D (x i) (y i)
  have hp : Function.Injective p := by
    intro i j hij
    apply hinj
    have he := congrArg (fun z : ℝ² => z 0) hij
    change (x i : ℝ) = (x j : ℝ) at he
    exact_mod_cast he
  refine ⟨Set.range p, Set.finite_range _, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact lattice_not_collinear hD (htri i j k (fun he => hij (he ▸ rfl))
      (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl)))
  · intro Q hQ hcos
    obtain ⟨a,b,c,e,hab,hac,hae,hbc,hbe,hce,hset⟩ := Set.ncard_eq_four.mp hQ.2
    subst Q
    obtain ⟨i,rfl⟩ := hQ.1 (by simp : a ∈ ({a,b,c,e} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ.1 (by simp : b ∈ ({p i,b,c,e} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ.1 (by simp : c ∈ ({p i,p j,c,e} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ.1 (by simp : e ∈ ({p i,p j,p k,e} : Set ℝ²))
    exact lattice_not_cospherical hD (hcirc i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => hae (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbe (he ▸ rfl)) (fun he => hce (he ▸ rfl))) hcos
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    refine ⟨(d i j : ℤ), ?_⟩
    have he := latticePoint_dist_sq D (x i) (y i) (x j) (y j)
    rw [hdist] at he
    push_cast at he ⊢
    change (d i j : ℝ) = dist (latticePoint D (x i) (y i)) (latticePoint D (x j) (y j))
    nlinarith [dist_nonneg (x := latticePoint D (x i) (y i)) (y := latticePoint D (x j) (y j)),
      Nat.cast_nonneg (α := ℝ) (d i j)]

private def x6 : Fin 6 → ℤ := ![0,5046,828,1695,3351,4218]
private def y6 : Fin 6 → ℤ := ![0,0,40,-40,40,-40]
private def d6 : Fin 6 → Fin 6 → ℕ := fun i j => 29 *
  (!![0,174,68,85,131,158;
      174,0,158,131,85,68;
      68,158,0,127,87,170;
      85,131,127,0,136,87;
      131,85,87,136,0,127;
      158,68,170,87,127,0] i j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma erdos213For_six : Erdos213For 6 := by
  apply integral_configuration_certificate 2002 6 (by norm_num) x6 y6 d6
  · decide
  · decide
  · decide
  · decide

lemma erdos213For_of_le_six {n : ℕ} (hn : n ≤ 6) : Erdos213For n :=
  erdos213For_six.mono hn


private noncomputable def hyperbolaPoint (t : ℝ) : ℝ² := !₂[t, t⁻¹]

/-- The reciprocal-product extension of three points on the rectangular hyperbola
always produces a concyclic quadruple. -/
lemma hyperbola_reciprocal_extension_cospherical {a b c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Cospherical {hyperbolaPoint a, hyperbolaPoint b, hyperbolaPoint c,
      hyperbolaPoint ((a*b*c)⁻¹)} := by
  let o : ℝ² := !₂[(a+b+c+(a*b*c)⁻¹)/2, (a⁻¹+b⁻¹+c⁻¹+a*b*c)/2]
  refine ⟨o, dist (hyperbolaPoint a) o, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rfl
  all_goals
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp [p4_dist_sq, hyperbolaPoint, o]
    field_simp
    ring


private lemma hyperbola_not_collinear {a b c : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ {hyperbolaPoint a, hyperbolaPoint b, hyperbolaPoint c} := by
  intro h
  have hz := collinear_det_zero h
  simp only [hyperbolaPoint, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hz
  have he : ((b-a)*(c⁻¹-a⁻¹) - (b⁻¹-a⁻¹)*(c-a)) * (a*b*c) =
      -((a-b)*(a-c)*(b-c)) := by
    field_simp
    ring
  rw [hz, zero_mul] at he
  exact (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab)
    (sub_ne_zero.mpr hac)) (sub_ne_zero.mpr hbc))) he.symm

private lemma hyperbola_not_cospherical {a b c d : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (hd : 1 < d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ Cospherical {hyperbolaPoint a, hyperbolaPoint b, hyperbolaPoint c,
      hyperbolaPoint d} := by
  intro h
  have hz := cospherical_det_zero h
  simp only [p4_dist_sq, hyperbolaPoint, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hz
  have ha0 : a ≠ 0 := ne_of_gt (lt_trans zero_lt_one ha)
  have hb0 : b ≠ 0 := ne_of_gt (lt_trans zero_lt_one hb)
  have hc0 : c ≠ 0 := ne_of_gt (lt_trans zero_lt_one hc)
  have hd0 : d ≠ 0 := ne_of_gt (lt_trans zero_lt_one hd)
  have he : det3 (b-a) (b⁻¹-a⁻¹) ((a-b)^2+(a⁻¹-b⁻¹)^2)
      (c-a) (c⁻¹-a⁻¹) ((a-c)^2+(a⁻¹-c⁻¹)^2)
      (d-a) (d⁻¹-a⁻¹) ((a-d)^2+(a⁻¹-d⁻¹)^2) *
      (a^2*b^2*c^2*d^2) =
      (a-b)*(a-c)*(a-d)*(b-c)*(b-d)*(c-d)*(a*b*c*d-1) := by
    unfold det3
    field_simp
    ring
  rw [hz, zero_mul] at he
  have hp : 1 < a*b*c*d :=
    one_lt_mul_of_lt_of_le (one_lt_mul_of_lt_of_le
      (one_lt_mul_of_lt_of_le ha hb.le) hc.le) hd.le
  have hlast : a*b*c*d-1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac))
    (sub_ne_zero.mpr had)) (sub_ne_zero.mpr hbc)) (sub_ne_zero.mpr hbd))
    (sub_ne_zero.mpr hcd)) hlast) he.symm

/-- A sufficient arithmetic construction for the general-position integral-distance problem. -/
lemma erdos213For_of_pythagorean_products {n : ℕ} (t : Fin n → ℚ)
    (ht : Function.Injective t) (hpos : ∀ i, 1 < t i)
    (hsq : ∀ i j, i ≠ j → ∃ u : ℚ, 1 + (t i * t j)^2 = u^2) :
    Erdos213For n := by
  apply (erdos213For_iff_rational n).mpr
  let p : Fin n → ℝ² := fun i => hyperbolaPoint (t i : ℝ)
  have ht' : Function.Injective (fun i => (t i : ℝ)) := by
    intro i j h
    apply ht
    change (t i : ℝ) = (t j : ℝ) at h
    exact_mod_cast h
  have hp : Function.Injective p := by
    intro i j h
    apply ht'
    exact congrArg (fun z : ℝ² => z 0) h
  have hpos' (i : Fin n) : 1 < (t i : ℝ) := by exact_mod_cast hpos i
  have hne (i : Fin n) : (t i : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one (hpos' i))
  refine ⟨Set.range p, Set.finite_range _, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    apply hyperbola_not_collinear (hne i) (hne j) (hne k)
    · exact fun h => hij (congrArg p (ht' h))
    · exact fun h => hik (congrArg p (ht' h))
    · exact fun h => hjk (congrArg p (ht' h))
  · intro Q hQ h4 hcos
    obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp h4
    subst Q
    obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,d} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({p i,b,c,d} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({p i,p j,c,d} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ (by simp : d ∈ ({p i,p j,p k,d} : Set ℝ²))
    exact hyperbola_not_cospherical (hpos' i) (hpos' j) (hpos' k) (hpos' l)
      (fun h => hab (congrArg p (ht' h))) (fun h => hac (congrArg p (ht' h)))
      (fun h => had (congrArg p (ht' h))) (fun h => hbc (congrArg p (ht' h)))
      (fun h => hbd (congrArg p (ht' h))) (fun h => hcd (congrArg p (ht' h))) hcos
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hij
    obtain ⟨u, hu⟩ := hsq i j (fun h => hij (h ▸ rfl))
    refine ⟨|(t i - t j)*u/(t i*t j)|, ?_⟩
    have hu' : 1 + ((t i : ℝ)*(t j : ℝ))^2 = (u : ℝ)^2 := by exact_mod_cast hu
    push_cast
    apply (sq_eq_sq₀ (abs_nonneg _) dist_nonneg).mp
    rw [sq_abs, p4_dist_sq]
    change (((t i : ℝ) - t j)*u/((t i : ℝ)*t j))^2 =
      ((t i : ℝ)-t j)^2 + ((t i : ℝ)⁻¹-(t j : ℝ)⁻¹)^2
    field_simp [hne i, hne j]
    linear_combination -((t i : ℝ) - t j)^2 * hu'
end Erdos213
