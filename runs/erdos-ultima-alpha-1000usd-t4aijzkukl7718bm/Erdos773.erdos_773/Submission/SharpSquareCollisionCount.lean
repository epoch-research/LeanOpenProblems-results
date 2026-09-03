import Submission.PeriodicCollisionWeights

/-!
Sharper counts for ordered four-root square-sum collisions, retaining the
primitive gap and parity information. This file does not settle Erdős 773.
-/
noncomputable section
namespace Erdos773.SharpSquareCollisionCount
open Finset PrimitiveSquareCollisions ParityTriangleCount PeriodicCollisionWeights
set_option maxHeartbeats 1000000

/-- Scale pairs for a fixed coprime direction. -/
def fiber (N u v : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (2*N)) ×ˢ (Icc 1 (2*N))).filter
    (fun t => Valid N ((u,v),t))

@[simp] lemma mem_fiber {N u v g w : ℕ} :
    (g,w) ∈ fiber N u v ↔ Valid N ((u,v),(g,w)) := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    have hb := valid_bounds h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hb.2.2.1,hb.2.2.2⟩,h⟩

lemma fiber_triangle_count (N u v : ℕ) (A C r : ℝ)
    (hA : 0 ≤ A) (hD : 1 ≤ C+r)
    (hgeom : ∀ t ∈ fiber N u v, C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A) :
    ((fiber N u v).card : ℝ) ≤ (sieveWeight u v : ℝ)*A^2/(8*(C+r))+A+1 := by
  have harea : 0 ≤ A^2/(8*(C+r)) := div_nonneg (sq_nonneg _) (by linarith)
  by_cases hc : u.Coprime v
  · rw [sieveWeight_of_coprime hc]
    have hnot : ¬ (u%2=0 ∧ v%2=0) := by
      rintro ⟨hu,hv⟩
      have hh := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu) (Nat.dvd_of_mod_eq_zero hv)
      rw [hc.gcd_eq_one] at hh
      norm_num at hh
    by_cases ho : u%2=1 ∧ v%2=1
    · have hH : ∀ t ∈ fiber N u v, 0 < t.1 ∧ t.1%2=t.2%2 ∧
          C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A := by
        rintro ⟨g,w⟩ ht
        have hp := mem_fiber.mp ht
        obtain ⟨hv,hvu,hg,hw,hcop,ha,hbc,hN,hpar,hpar'⟩ := hp
        dsimp only at hg hpar hpar'
        have hh := (parity_classification hc).mp ⟨hpar,hpar'⟩
        have hm : g%2=w%2 := by rcases hh with hh | hh <;> omega
        exact ⟨hg,hm,(hgeom (g,w) ht).1,(hgeom (g,w) ht).2⟩
      have hb := matching_triangle_count (fiber N u v) A C r hA hD hH
      simp only [parityWeight,if_neg hnot,if_pos ho,Nat.cast_ofNat]
      have heq : 2*A^2/(8*(C+r))=A^2/(4*(C+r)) := by
        have hn : C+r ≠ 0 := by linarith
        field_simp
        ring
      rw [heq]
      linarith
    · have hH : ∀ t ∈ fiber N u v, 0 < t.1 ∧ t.1%2=0 ∧ t.2%2=0 ∧
          C*t.1 ≤ t.2 ∧ (t.2 : ℝ)+r*t.1 ≤ A := by
        rintro ⟨g,w⟩ ht
        have hp := mem_fiber.mp ht
        obtain ⟨hv,hvu,hg,hw,hcop,ha,hbc,hN,hpar,hpar'⟩ := hp
        dsimp only at hg hpar hpar'
        have hh := (parity_classification hc).mp ⟨hpar,hpar'⟩
        have hm : g%2=0 ∧ w%2=0 := by rcases hh with hh | hh <;> tauto
        exact ⟨hg,hm.1,hm.2,(hgeom (g,w) ht).1,(hgeom (g,w) ht).2⟩
      have hb := even_triangle_count (fiber N u v) A C r hA hD hH
      simp only [parityWeight,if_neg hnot,if_neg ho,Nat.cast_one,one_mul]
      linarith
  · have he : fiber N u v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨g,w⟩ ht
      exact hc (mem_fiber.mp ht).2.2.2.2.1
    rw [he,card_empty,Nat.cast_zero]
    have hw : (0 : ℝ) ≤ sieveWeight u v := by positivity
    have hh := mul_nonneg hw harea
    rw [← mul_div_assoc] at hh
    linarith

lemma fiber_count_first (N u v : ℕ) (hv : 0 < v) (hvu : v < u) :
    ((fiber N u v).card : ℝ) ≤
      (sieveWeight u v : ℝ)*(2*N/u)^2/(8*((u:ℝ)/v+v/u))+2*N/u+1 := by
  have hu : 0 < u := by omega
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvuR : (v : ℝ) < u := by exact_mod_cast hvu
  apply fiber_triangle_count
  · positivity
  · have hh : (1 : ℝ) ≤ u/v := (le_div_iff₀ hvR).mpr (by linarith)
    have hvr : (0 : ℝ) ≤ v/u := by positivity
    linarith
  · rintro ⟨g,w⟩ ht
    obtain ⟨_,_,_,_,_,ha,_,hN,_⟩ := mem_fiber.mp ht
    dsimp only at ha hN
    have haR : (u : ℝ)*g < v*w := by exact_mod_cast ha
    have hNR : (u : ℝ)*w+v*g ≤ 2*N := by exact_mod_cast hN
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hvR).mpr
      nlinarith only [haR]
    · apply (le_div_iff₀ huR).mpr
      field_simp
      nlinarith only [hNR]

lemma fiber_count_second (N u v : ℕ) (hv : 0 < v) (hvu : v < u) :
    ((fiber N u v).card : ℝ) ≤
      (sieveWeight u v : ℝ)*(2*N/u)^2/(8*(((u:ℝ)+v)/(u-v)+v/u))+2*N/u+1 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (hv.trans hvu)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvuR : (v : ℝ) < u := by exact_mod_cast hvu
  have hsub : (0 : ℝ) < u-v := by linarith
  apply fiber_triangle_count
  · positivity
  · have hh : (1 : ℝ) ≤ (u+v)/(u-v) := (le_div_iff₀ hsub).mpr (by linarith)
    have hvr : (0 : ℝ) ≤ v/u := by positivity
    linarith
  · rintro ⟨g,w⟩ ht
    obtain ⟨_,_,_,_,_,_,hbc,hN,_⟩ := mem_fiber.mp ht
    dsimp only at hbc hN
    have hbcR : ((u : ℝ)+v)*g < (u-v)*w := by
      have hh : ((u+v : ℕ) : ℝ)*g < ((u-v : ℕ) : ℝ)*w := by exact_mod_cast hbc
      push_cast [Nat.cast_sub hvu.le] at hh
      exact hh
    have hNR : (u : ℝ)*w+v*g ≤ 2*N := by exact_mod_cast hN
    constructor
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hsub).mpr
      nlinarith only [hbcR]
    · apply (le_div_iff₀ huR).mpr
      field_simp
      nlinarith only [hNR]

def shape₁ (x : ℝ) : ℝ := x/(1+x^2)
def shape₂ (x : ℝ) : ℝ := (1-x)/(1+2*x-x^2)

lemma shape₁_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    shape₁ x ≤ shape₁ y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hxy1 : x*y ≤ 1 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hy)]
  unfold shape₁
  apply (div_le_div_iff₀ (by positivity : 0 < 1+x^2) (by positivity : 0 < 1+y^2)).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy1)]

lemma shape₂_den_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 < 1+2*x-x^2 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]

lemma shape₂_antimono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    shape₂ y ≤ shape₂ x := by
  have hx1 : x ≤ 1 := hxy.trans hy
  have hy0 : 0 ≤ y := hx.trans hxy
  have hfac : 0 ≤ 3-x-y+x*y := by nlinarith [mul_nonneg hx hy0]
  unfold shape₂
  apply (div_le_div_iff₀ (shape₂_den_pos hy0 hy) (shape₂_den_pos hx hx1)).mpr
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) hfac]

/-- Twenty rational upper-step heights; the switch is at 2/5. -/
def shapeQ (i : ℕ) : ℚ :=
  if i < 8 then (((i:ℚ)+1)/20)/(1+(((i:ℚ)+1)/20)^2)
  else (1-(i:ℚ)/20)/(1+2*((i:ℚ)/20)-((i:ℚ)/20)^2)

lemma shapeQ_cast_first (i : ℕ) (hi : i < 8) :
    (shapeQ i : ℝ) = shape₁ (((i:ℝ)+1)/20) := by
  simp only [shapeQ,if_pos hi,shape₁]
  push_cast
  rfl

lemma shapeQ_cast_second (i : ℕ) (hi : ¬i < 8) :
    (shapeQ i : ℝ) = shape₂ ((i:ℝ)/20) := by
  simp only [shapeQ,if_neg hi,shape₂]
  push_cast
  rfl

lemma shapeQ_nonneg (i : ℕ) (hi : i < 20) : (0:ℚ) ≤ shapeQ i := by
  interval_cases i <;> norm_num [shapeQ]

lemma shapeQ_sum : (∑ i ∈ range 20, shapeQ i) ≤ 123/32 := by
  norm_num [sum_range_succ,shapeQ]

lemma shapeQ_sum_real : (∑ i ∈ range 20, (shapeQ i : ℝ)) ≤ 123/32 := by
  have hh := (Rat.cast_le (K := ℝ)).mpr shapeQ_sum
  simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_ofNat] using hh

lemma shapeQ_upper {x : ℝ} {i : ℕ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (_hi : i < 20) (hlo : (i : ℝ) ≤ 20*x) (hhi : 20*x ≤ i+1) :
    (if i < 8 then shape₁ x else shape₂ x) ≤ (shapeQ i : ℝ) := by
  by_cases h : i < 8
  · rw [if_pos h,shapeQ_cast_first i h]
    apply shape₁_mono hx (by linarith)
    have hh : (i : ℝ) < 8 := by exact_mod_cast h
    linarith
  · rw [if_neg h,shapeQ_cast_second i h]
    apply shape₂_antimono (by positivity) (by linarith) hx1

lemma fiber_shape_first (N u v : ℕ) (hv : 0 < v) (hvu : v < u) :
    ((fiber N u v).card : ℝ) ≤
      (sieveWeight u v : ℝ)*((N:ℝ)^2/(2*u^2))*shape₁ ((v:ℝ)/u)+2*N/u+1 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (hv.trans hvu)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hb := fiber_count_first N u v hv hvu
  have heq : (2*(N:ℝ)/u)^2/(8*((u:ℝ)/v+v/u)) =
      ((N:ℝ)^2/(2*u^2))*shape₁ ((v:ℝ)/u) := by
    unfold shape₁
    field_simp
    ring
  rw [mul_div_assoc,heq,← mul_assoc] at hb
  exact hb

lemma fiber_shape_second (N u v : ℕ) (hv : 0 < v) (hvu : v < u) :
    ((fiber N u v).card : ℝ) ≤
      (sieveWeight u v : ℝ)*((N:ℝ)^2/(2*u^2))*shape₂ ((v:ℝ)/u)+2*N/u+1 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (hv.trans hvu)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvuR : (v : ℝ) < u := by exact_mod_cast hvu
  have hs : (u : ℝ)-v ≠ 0 := by linarith
  have hb := fiber_count_second N u v hv hvu
  have heq : (2*(N:ℝ)/u)^2/(8*(((u:ℝ)+v)/(u-v)+v/u)) =
      ((N:ℝ)^2/(2*u^2))*shape₂ ((v:ℝ)/u) := by
    unfold shape₂
    field_simp
    ring
  rw [mul_div_assoc,heq,← mul_assoc] at hb
  exact hb

/-- Per-direction upper bound using the exact parity weight. -/
theorem fiber_bin_bound (N u v i : ℕ) (hv : 0 < v) (hvu : v < u)
    (hi : i < 20) (hlo : u*i ≤ 20*v) (hhi : 20*v ≤ u*(i+1)) :
    ((fiber N u v).card : ℝ) ≤
      (sieveWeight u v : ℝ)*((N:ℝ)^2/(2*u^2))*(shapeQ i : ℝ)+2*N/u+1 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (hv.trans hvu)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hvuR : (v : ℝ) < u := by exact_mod_cast hvu
  have hx : 0 ≤ (v:ℝ)/u := by positivity
  have hx1 : (v:ℝ)/u ≤ 1 := (div_le_one huR).mpr hvuR.le
  have hloR : (u:ℝ)*i ≤ 20*v := by exact_mod_cast hlo
  have hhiR : 20*(v:ℝ) ≤ (u:ℝ)*(i+1) := by exact_mod_cast hhi
  have hl : (i:ℝ) ≤ 20*((v:ℝ)/u) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ huR).mpr
    nlinarith only [hloR]
  have hh : 20*((v:ℝ)/u) ≤ i+1 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ huR).mpr
    nlinarith only [hhiR]
  have hb := shapeQ_upper hx hx1 hi hl hh
  have hmul := mul_le_mul_of_nonneg_left hb
    (show (0:ℝ) ≤ (sieveWeight u v : ℝ)*((N:ℝ)^2/(2*u^2)) by positivity)
  by_cases h : i < 8
  · rw [if_pos h] at hmul
    have hf := fiber_shape_first N u v hv hvu
    linarith
  · rw [if_neg h] at hmul
    have hf := fiber_shape_second N u v hv hvu
    linarith

lemma bin_index {u v : ℕ} (hu : 0 < u) (hv : v < u) :
    20*v/u < 20 ∧ u*(20*v/u) ≤ 20*v ∧ 20*v < u*(20*v/u+1) := by
  exact ⟨(Nat.div_lt_iff_lt_mul hu).mpr (by omega),Nat.mul_div_le _ _,
    Nat.lt_mul_div_succ _ hu⟩

lemma weighted_shape_sum (u : ℕ) (hu : 0 < u) :
    (∑ v ∈ Icc 1 (u-1), (sieveWeight u v : ℝ)*(shapeQ (20*v/u) : ℝ)) ≤
      (row u : ℝ)*((u:ℝ)/600+1)*(123/32) := by
  have hb (v : ℕ) (hv : v ∈ Icc 1 (u-1)) := bin_index hu (show v<u by
    have hh := (mem_Icc.mp hv).2
    omega)
  have hf := sum_fiberwise_of_maps_to
    (fun v hv => mem_range.mpr (hb v hv).1)
    (fun v => (sieveWeight u v : ℝ)*(shapeQ (20*v/u) : ℝ))
  rw [← hf]
  calc
    _ = ∑ i ∈ range 20, (shapeQ i : ℝ)*
        (∑ v ∈ (Icc 1 (u-1)).filter (fun v => 20*v/u=i), (sieveWeight u v : ℝ)) := by
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
      apply sum_congr rfl
      intro v hv
      rw [(mem_filter.mp hv).2]
      ring
    _ ≤ ∑ i ∈ range 20, (shapeQ i : ℝ)*((row u : ℝ)*((u:ℝ)/600+1)) := by
      apply sum_le_sum
      intro i hi
      have hi20 := mem_range.mp hi
      have hpos : (0:ℝ) ≤ shapeQ i := (Rat.cast_nonneg (K:=ℝ)).mpr (shapeQ_nonneg i hi20)
      apply mul_le_mul_of_nonneg_left _ hpos
      apply weighted_bin
      intro v hv
      obtain ⟨hv,hvi⟩ := mem_filter.mp hv
      have ht := hb v hv
      rw [hvi] at ht
      exact ⟨ht.2.1,ht.2.2.le⟩
    _ = (row u : ℝ)*((u:ℝ)/600+1)*(∑ i ∈ range 20, (shapeQ i : ℝ)) := by
      rw [← sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left shapeQ_sum_real
      (mul_nonneg (Nat.cast_nonneg _) (by positivity))

lemma direction_sum (N u : ℕ) (hu : 0 < u) :
    (∑ v ∈ Icc 1 (u-1), ((fiber N u v).card : ℝ)) ≤
      (123/38400:ℝ)*N^2*((row u : ℝ)/u)+
      (1845/16:ℝ)*N^2/(u:ℝ)^2+2*N+u := by
  have huR : (0:ℝ) < u := by exact_mod_cast hu
  let K : ℝ := (N:ℝ)^2/(2*u^2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : (∑ v ∈ Icc 1 (u-1), ((fiber N u v).card : ℝ)) ≤
      K*(∑ v ∈ Icc 1 (u-1), (sieveWeight u v : ℝ)*(shapeQ (20*v/u) : ℝ))+
      (u-1:ℕ)*(2*(N:ℝ)/u+1) := by
    calc
      _ ≤ ∑ v ∈ Icc 1 (u-1),
          ((sieveWeight u v : ℝ)*K*(shapeQ (20*v/u) : ℝ)+2*N/u+1) := by
        apply sum_le_sum
        intro v hv
        have hvpos := (mem_Icc.mp hv).1
        have hvu : v<u := by have hh := (mem_Icc.mp hv).2; omega
        have ht := bin_index hu hvu
        exact fiber_bin_bound N u v _ hvpos hvu ht.1 ht.2.1 ht.2.2.le
      _ = _ := by
        have hsum : (∑ v ∈ Icc 1 (u-1), (sieveWeight u v : ℝ)*K*(shapeQ (20*v/u) : ℝ)) =
            K*(∑ v ∈ Icc 1 (u-1), (sieveWeight u v : ℝ)*(shapeQ (20*v/u) : ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro v hv
          ring
        have hc : (Icc 1 (u-1)).card = u-1 := by simp
        simp only [sum_add_distrib,sum_const,hc,nsmul_eq_mul,hsum]
        ring
  have hweighted := mul_le_mul_of_nonneg_left (weighted_shape_sum u hu) hK
  have herr : ((u-1:ℕ):ℝ)*(2*(N:ℝ)/u+1) ≤ 2*N+u := by
    have hle : ((u-1:ℕ):ℝ) ≤ u := by exact_mod_cast Nat.sub_le u 1
    have hh := mul_le_mul_of_nonneg_right hle (show 0 ≤ 2*(N:ℝ)/u+1 by positivity)
    have heq : (u:ℝ)*(2*(N:ℝ)/u+1)=2*N+u := by field_simp
    rwa [heq] at hh
  have hrow : (row u : ℝ) ≤ 60 := by exact_mod_cast row_le u
  have hrowterm : (123/64:ℝ)*(N:ℝ)^2*(row u : ℝ)/(u:ℝ)^2 ≤
      (1845/16:ℝ)*(N:ℝ)^2/(u:ℝ)^2 := by
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos huR)).mpr
    have hh := mul_le_mul_of_nonneg_left hrow
      (show 0 ≤ (123/64:ℝ)*(N:ℝ)^2 by positivity)
    nlinarith only [hh]
  have heq : K*((row u : ℝ)*((u:ℝ)/600+1)*(123/32)) =
      (123/38400:ℝ)*N^2*((row u : ℝ)/u)+
      (123/64:ℝ)*(N:ℝ)^2*(row u : ℝ)/(u:ℝ)^2 := by
    generalize (row u : ℝ) = R
    dsimp [K]
    field_simp
    ring
  rw [heq] at hweighted
  linarith

lemma card_fiber_sum (N : ℕ) :
    (parameters N).card = ∑ u ∈ Icc 1 (2*N), ∑ v ∈ Icc 1 (u-1), (fiber N u v).card := by
  have hmap : ∀ p ∈ parameters N, p.1 ∈ (Icc 1 (2*N)) ×ˢ (Icc 1 (2*N)) := by
    intro p hp
    have hb := valid_bounds (mem_parameters.mp hp)
    exact mem_product.mpr ⟨hb.1,hb.2.1⟩
  have hc := card_eq_sum_card_fiberwise hmap
  rw [hc]
  have hcard (uv : ℕ × ℕ) :
      ((parameters N).filter (fun p => p.1=uv)).card = (fiber N uv.1 uv.2).card := by
    apply card_nbij Prod.snd
    · intro p hp
      obtain ⟨hp0,hpu⟩ := mem_filter.mp hp
      rcases p with ⟨⟨u,v⟩,⟨g,w⟩⟩
      simp only at hpu ⊢
      subst uv
      exact mem_fiber.mpr (mem_parameters.mp hp0)
    · intro p hp q hq he
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      exact Prod.ext (hp'.trans hq'.symm) he
    · rintro ⟨g,w⟩ ht
      refine ⟨(uv,(g,w)),mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
      exact mem_parameters.mpr (mem_fiber.mp ht)
  simp_rw [hcard]
  rw [sum_product]
  apply sum_congr rfl
  intro u hu
  have hsub : Icc 1 (u-1) ⊆ Icc 1 (2*N) := by
    intro v hv
    have huN := (mem_Icc.mp hu).2
    simp only [mem_Icc] at hv ⊢
    omega
  symm
  apply sum_subset hsub
  intro v hv hvnot
  have hvpos := (mem_Icc.mp hv).1
  have huv : u ≤ v := by
    simp only [mem_Icc,not_and_or,not_le] at hvnot
    omega
  have he : fiber N u v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨g,w⟩ ht
    have hh := (mem_fiber.mp ht).2.1
    dsimp only at hh
    omega
  rw [he,card_empty]

/-- An explicit leading coefficient strictly below 1/12. The additive term
is deliberately generous; it does not affect the logarithmic coefficient. -/
theorem ordered_log_bound (N : ℕ) :
    ((ordered N).card : ℝ) ≤ (N:ℝ)^2*((41/500:ℝ)*(1+Real.log (2*N))+244) := by
  have hb : ((ordered N).card : ℝ) ≤
      ∑ u ∈ Icc 1 (2*N), ((123/38400:ℝ)*N^2*((row u : ℝ)/u)+
        (1845/16:ℝ)*N^2/(u:ℝ)^2+2*N+u) := by
    rw [← parameters_card,card_fiber_sum]
    push_cast
    exact sum_le_sum (fun u hu => direction_sum N u (mem_Icc.mp hu).1)
  have heq : (∑ u ∈ Icc 1 (2*N), ((123/38400:ℝ)*N^2*((row u : ℝ)/u)+
        (1845/16:ℝ)*N^2/(u:ℝ)^2+2*N+u)) =
      (123/38400:ℝ)*N^2*(∑ u ∈ Icc 1 (2*N), (row u : ℝ)/u)+
      (1845/16:ℝ)*N^2*(∑ u ∈ Icc 1 (2*N), 1/(u:ℝ)^2)+
      (∑ u ∈ Icc 1 (2*N), (2*(N:ℝ)+u)) := by
    simp only [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro u hu
    ring
  rw [heq] at hb
  have herr : (∑ u ∈ Icc 1 (2*N), (2*(N:ℝ)+u)) ≤ 7*(N:ℝ)^2 := by
    rw [sum_add_distrib,sum_const,sum_Icc_cast]
    simp only [Nat.card_Icc,nsmul_eq_mul,Nat.add_sub_cancel]
    push_cast
    have hNN : (N:ℝ) ≤ N^2 := by
      cases N with
      | zero => norm_num
      | succ n => push_cast; nlinarith [sq_nonneg (n:ℝ)]
    nlinarith only [hNN]
  have hrow := row_log (2*N)
  push_cast at hrow
  have hrow' := mul_le_mul_of_nonneg_left hrow
    (show 0 ≤ (123/38400:ℝ)*(N:ℝ)^2 by positivity)
  have hinv := inverse_square_sum (2*N)
  have hinv' := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ (1845/16:ℝ)*(N:ℝ)^2 by positivity)
  nlinarith only [hb,hrow',hinv',herr,sq_nonneg (N:ℝ)]

#print axioms fiber_triangle_count
#print axioms fiber_count_first
#print axioms fiber_count_second
#print axioms shapeQ_sum_real
#print axioms fiber_bin_bound
#print axioms weighted_shape_sum
#print axioms direction_sum
#print axioms card_fiber_sum
#print axioms ordered_log_bound
end Erdos773.SharpSquareCollisionCount
