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

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

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



/- A separate parabola-based reduction. This is not a proof of the conjecture. -/

namespace Parabola

noncomputable def point (t : ℝ) : ℝ² := !₂[t, t^2]

lemma point_injective : Function.Injective point := by
  intro s t h
  exact congrArg (fun p : ℝ² => p 0) h

lemma dist_sq (s t : ℝ) :
    dist (point s) (point t)^2 = (s-t)^2*(1+(s+t)^2) := by
  rw [p4_dist_sq]
  dsimp [point]
  ring

lemma not_collinear {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬Collinear ℝ {point a, point b, point c} := by
  intro h
  have hh := collinear_det_zero h
  have he : (b-a)*(c-a)*(c-b) = 0 := by
    convert hh using 1
    dsimp [point]
    ring
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm)
    (sub_ne_zero.mpr hac.symm)) (sub_ne_zero.mpr hbc.symm) he

private def det3 (a b c d e f g h i : ℝ) : ℝ :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

private lemma circle_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
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

lemma cospherical_iff {a b c d : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Cospherical {point a, point b, point c, point d} ↔ a+b+c+d = 0 := by
  constructor
  · intro h
    have hh := circle_det_zero h
    have he : (b-a)*(c-a)*(d-a)*(c-b)*(d-b)*(d-c)*(a+b+c+d) = 0 := by
      convert hh using 1
      simp only [dist_sq]
      dsimp [point, det3]
      ring
    have hn : (b-a)*(c-a)*(d-a)*(c-b)*(d-b)*(d-c) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (sub_ne_zero.mpr hab.symm) (sub_ne_zero.mpr hac.symm))
        (sub_ne_zero.mpr had.symm)) (sub_ne_zero.mpr hbc.symm))
        (sub_ne_zero.mpr hbd.symm)) (sub_ne_zero.mpr hcd.symm)
    exact (mul_eq_zero.mp he).resolve_left hn
  · intro h
    have hd : d = -a-b-c := by linarith
    subst d
    let o : ℝ² := !₂[-(a+b)*(a+c)*(b+c)/2,
      (1+a^2+b^2+c^2+a*b+a*c+b*c)/2]
    refine ⟨o, dist (point a) o, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · rfl
    all_goals
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      simp only [p4_dist_sq]
      dsimp [point, o]
      ring

lemma rational_distance_iff {s t : ℚ} (hst : s ≠ t) :
    dist (point (s : ℝ)) (point (t : ℝ)) ∈ Set.range ((↑) : ℚ → ℝ) ↔
      IsSquare (1+(s+t)^2) := by
  have hn : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hst)
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q/(s-t), ?_⟩
    have he := dist_sq (s : ℝ) t
    rw [← hq] at he
    apply Rat.cast_injective (α := ℝ)
    push_cast
    field_simp [hn]
    nlinarith [he]
  · rintro ⟨q, hq⟩
    refine ⟨abs ((s-t)*q), ?_⟩
    have he := dist_sq (s : ℝ) t
    have hqr : 1+((s : ℝ)+t)^2 = (q : ℝ)*(q : ℝ) := by exact_mod_cast hq
    push_cast
    rw [hqr] at he
    have hsq : |((s : ℝ)-t)*q|^2 = dist (point (s : ℝ)) (point (t : ℝ))^2 := by
      rw [sq_abs, he]
      ring
    nlinarith [abs_nonneg (((s : ℝ)-t)*q),
      dist_nonneg (x := point (s : ℝ)) (y := point (t : ℝ))]


lemma erdos213For_of_sums {n : ℕ} (t : Fin n → ℚ)
    (ht : Function.Injective t)
    (hsum : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      t i+t j+t k+t l ≠ 0)
    (hsq : ∀ i j, i ≠ j → IsSquare (1+(t i+t j)^2)) : Erdos213For n := by
  apply (erdos213For_iff_rational n).mpr
  let p : Fin n → ℝ² := fun i => point (t i : ℝ)
  have htR : Function.Injective (fun i => (t i : ℝ)) := Rat.cast_injective.comp ht
  have hp : Function.Injective p := point_injective.comp htR
  have hn {i j : Fin n} (hij : i ≠ j) : (t i : ℝ) ≠ t j := fun h => hij (htR h)
  refine ⟨Set.range p, Set.finite_range _, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact not_collinear (hn (fun h => hij (h ▸ rfl)))
      (hn (fun h => hik (h ▸ rfl))) (hn (fun h => hjk (h ▸ rfl)))
  · intro Q hQ hcard hcos
    obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hset⟩ := Set.ncard_eq_four.mp hcard
    subst Q
    obtain ⟨i,rfl⟩ := hQ (by simp : a ∈ ({a,b,c,d} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ (by simp : b ∈ ({p i,b,c,d} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ (by simp : c ∈ ({p i,p j,c,d} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ (by simp : d ∈ ({p i,p j,p k,d} : Set ℝ²))
    have hij : i ≠ j := fun h => hab (h ▸ rfl)
    have hik : i ≠ k := fun h => hac (h ▸ rfl)
    have hil : i ≠ l := fun h => had (h ▸ rfl)
    have hjk : j ≠ k := fun h => hbc (h ▸ rfl)
    have hjl : j ≠ l := fun h => hbd (h ▸ rfl)
    have hkl : k ≠ l := fun h => hcd (h ▸ rfl)
    have he := (cospherical_iff (hn hij) (hn hik) (hn hil) (hn hjk) (hn hjl) (hn hkl)).mp hcos
    exact hsum i j k l hij hik hil hjk hjl hkl (by exact_mod_cast he)
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hij
    have hij' : i ≠ j := fun h => hij (h ▸ rfl)
    exact (rational_distance_iff (fun h => hij' (ht h))).mpr (hsq i j hij')

lemma erdos213For_of_positive_sums {n : ℕ} (t : Fin n → ℚ)
    (ht : Function.Injective t) (hpos : ∀ i, 0 < t i)
    (hsq : ∀ i j, i ≠ j → IsSquare (1+(t i+t j)^2)) : Erdos213For n := by
  apply erdos213For_of_sums t ht _ hsq
  intro i j k l _ _ _ _ _ _
  linarith [hpos i, hpos j, hpos k, hpos l]

/-- A sufficient arithmetic-progression construction. The hypotheses demand
squares at every integer from 1 through `2*n-3`; their existence for arbitrary
`n` has NOT been established. -/
lemma erdos213For_of_quadratic_squares {n : ℕ} (u v : ℚ)
    (hu : 0 < u) (hv : 0 < v) (q : ℕ → ℚ)
    (hq : ∀ k : ℕ, 1 ≤ k → k ≤ 2*n-3 → q k ^ 2 = ((k : ℚ)+u)^2+v^2) :
    Erdos213For n := by
  let t : Fin n → ℚ := fun i => ((i.val : ℚ)+u/2)/v
  have hv0 := ne_of_gt hv
  apply erdos213For_of_positive_sums t
  · intro i j hij
    dsimp [t] at hij
    have he : (i.val : ℚ) = j.val := by
      have hh := (div_left_inj' hv0).mp hij
      linarith
    exact Fin.ext (by exact_mod_cast he)
  · intro i
    dsimp [t]
    positivity
  · intro i j hij
    have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hlo : 1 ≤ i.val+j.val := by omega
    have hhi : i.val+j.val ≤ 2*n-3 := by omega
    have hh := hq (i.val+j.val) hlo hhi
    refine ⟨q (i.val+j.val)/v, ?_⟩
    dsimp [t]
    push_cast at hh
    field_simp
    nlinarith [hh]

#print axioms cospherical_iff
#print axioms rational_distance_iff
#print axioms erdos213For_of_sums
#print axioms erdos213For_of_quadratic_squares

end Parabola
end Erdos213
