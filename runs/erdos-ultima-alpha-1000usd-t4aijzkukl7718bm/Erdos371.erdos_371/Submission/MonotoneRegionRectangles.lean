import FormalConjecturesUtil

/-! A finite staircase comparison theorem for monotone regions. It keeps
both the rectangle discrepancy and the staircase boundary explicitly. -/
namespace Erdos371.MonotoneRectangles
open Finset

section Counts
variable {ι : Type*} [Fintype ι]

noncomputable def rectCount (a b : ι → ℕ) (L M : ℕ) : ℕ :=
  (univ.filter fun i => a i<L ∧ b i<M).card

noncomputable def regionCount (a b : ι → ℕ) (h : ℕ → ℕ) : ℕ :=
  (univ.filter fun i => a i<h (b i)).card

noncomputable def sliceCount (a b : ι → ℕ) (H j L : ℕ) : ℕ :=
  (univ.filter fun i => a i<L ∧ b i/H=j).card

lemma div_eq_strip (y H j : ℕ) (hH : 0<H) :
    y/H=j ↔ j*H≤y ∧ y<(j+1)*H := by
  rw [Nat.div_eq_iff hH]
  have he : (j+1)*H=j*H+H := by ring
  omega

lemma region_partition (a b : ι → ℕ) (h : ℕ → ℕ) (H K : ℕ) (hH : 0<H)
    (hb : ∀ i, b i<K*H) :
    regionCount a b h=∑ j ∈ range K,
      (univ.filter fun i => a i<h (b i) ∧ b i/H=j).card := by
  have hs := sum_card_fiberwise_eq_card_filter
    (univ.filter fun i => a i<h (b i)) (range K) (fun i => b i/H)
  have he : (univ.filter fun i => a i<h (b i)).filter (fun i => b i/H∈range K)=
      (univ.filter fun i => a i<h (b i)) := by
    apply filter_eq_self.mpr
    intro i hi
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hH).mpr (hb i))
  rw [he] at hs
  simpa only [filter_filter,regionCount] using hs.symm

lemma region_staircase_sandwich (a b : ι → ℕ) (h : ℕ → ℕ) (hh : Antitone h)
    (H K : ℕ) (hH : 0<H) (hb : ∀ i, b i<K*H) :
    (∑ j ∈ range K, sliceCount a b H j (h ((j+1)*H)))≤regionCount a b h ∧
      regionCount a b h≤∑ j ∈ range K, sliceCount a b H j (h (j*H)) := by
  rw [region_partition a b h H K hH hb]
  constructor
  · apply sum_le_sum
    intro j hj
    apply card_le_card
    intro i hi
    obtain ⟨hi,hai,hji⟩ := mem_filter.mp hi
    have hr := (div_eq_strip (b i) H j hH).mp hji
    exact mem_filter.mpr ⟨hi,hai.trans_le (hh hr.2.le),hji⟩
  · apply sum_le_sum
    intro j hj
    apply card_le_card
    intro i hi
    obtain ⟨hi,hai,hji⟩ := mem_filter.mp hi
    have hr := (div_eq_strip (b i) H j hH).mp hji
    exact mem_filter.mpr ⟨hi,hai.trans_le (hh hr.1),hji⟩

lemma sliceCount_add_prefix (a b : ι → ℕ) (H j L : ℕ) (hH : 0<H) :
    sliceCount a b H j L+rectCount a b L (j*H)=rectCount a b L ((j+1)*H) := by
  have hp := card_filter_add_card_filter_not
    (s := univ.filter fun i => a i<L ∧ b i<(j+1)*H) (fun i => j*H≤b i)
  have he1 : (univ.filter fun i => a i<L ∧ b i<(j+1)*H).filter (fun i => j*H≤b i)=
      (univ.filter fun i => a i<L ∧ b i/H=j) := by
    ext i
    simp only [mem_filter,mem_univ,true_and,div_eq_strip _ H j hH]
    tauto
  have he2 : (univ.filter fun i => a i<L ∧ b i<(j+1)*H).filter (fun i => ¬j*H≤b i)=
      (univ.filter fun i => a i<L ∧ b i<j*H) := by
    ext i
    simp only [mem_filter,mem_univ,true_and]
    have he : j*H≤(j+1)*H := by nlinarith
    omega
  rw [he1,he2] at hp
  exact hp

lemma rectCount_clip_second (a b : ι → ℕ) (p L M : ℕ) (hb : ∀ i, b i<p) :
    rectCount a b L (min p M)=rectCount a b L M := by
  unfold rectCount
  congr 1
  ext i
  simp only [mem_filter,lt_min_iff,hb i,true_and]

/-- A vertical strip is the difference of two bounded prefix rectangles. -/
lemma sliceCount_real_eq (a b : ι → ℕ) (p H j L : ℕ) (hH : 0<H) (hb : ∀ i, b i<p) :
    (sliceCount a b H j L : ℝ)=
      rectCount a b L (min p ((j+1)*H))-(rectCount a b L (min p (j*H)) : ℝ) := by
  rw [rectCount_clip_second a b p _ _ hb,rectCount_clip_second a b p _ _ hb]
  have he : (sliceCount a b H j L : ℝ)+(rectCount a b L (j*H) : ℝ)=
      rectCount a b L ((j+1)*H) := by exact_mod_cast sliceCount_add_prefix a b H j L hH
  linarith

lemma slice_rectangle_error (a b : ι → ℕ) (p H j L : ℕ) (hH : 0<H)
    (hb : ∀ i, b i<p) (hL : L≤p) (δ : ℝ)
    (hrect : ∀ U V : ℕ, U≤p → V≤p →
      |(rectCount a b U V : ℝ)/p-((U : ℝ)/p)*((V : ℝ)/p)|≤δ) :
    |(sliceCount a b H j L : ℝ)/p-
      ((L : ℝ)/p)*((min p ((j+1)*H) : ℝ)/p-(min p (j*H) : ℝ)/p)|≤2*δ := by
  have hu := hrect L (min p ((j+1)*H)) hL (min_le_left _ _)
  have hl := hrect L (min p (j*H)) hL (min_le_left _ _)
  rw [sliceCount_real_eq a b p H j L hH hb]
  have he : ((rectCount a b L (min p ((j+1)*H)) : ℝ)-rectCount a b L (min p (j*H)))/p-
      ((L : ℝ)/p)*((min p ((j+1)*H) : ℝ)/p-(min p (j*H) : ℝ)/p) =
      ((rectCount a b L (min p ((j+1)*H)) : ℝ)/p-((L : ℝ)/p)*((min p ((j+1)*H) : ℝ)/p))-
      ((rectCount a b L (min p (j*H)) : ℝ)/p-((L : ℝ)/p)*((min p (j*H) : ℝ)/p)) := by ring
  rw [he]
  push_cast at hu hl
  exact (abs_sub _ _).trans (by linarith)
end Counts

noncomputable def stairArea (p H K : ℕ) (k : ℕ → ℕ) : ℝ :=
  ∑ j ∈ range K, ((k j : ℝ)/p)*
    ((min p ((j+1)*H) : ℝ)/p-(min p (j*H) : ℝ)/p)

section Approximation
variable {ι : Type*} [Fintype ι]

lemma staircase_sum_error (a b : ι → ℕ) (p H K : ℕ) (k : ℕ → ℕ)
    (hH : 0<H) (hb : ∀ i, b i<p) (hk : ∀ j, k j≤p) (δ : ℝ)
    (hrect : ∀ U V : ℕ, U≤p → V≤p →
      |(rectCount a b U V : ℝ)/p-((U : ℝ)/p)*((V : ℝ)/p)|≤δ) :
    |(∑ j ∈ range K, (sliceCount a b H j (k j) : ℝ))/p-stairArea p H K k|≤2*K*δ := by
  unfold stairArea
  rw [sum_div,← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range K, |(sliceCount a b H j (k j) : ℝ)/p-
        ((k j : ℝ)/p)*((min p ((j+1)*H) : ℝ)/p-(min p (j*H) : ℝ)/p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range K, 2*δ := sum_le_sum fun j _ => slice_rectangle_error a b p H j (k j) hH hb (hk j) δ hrect
    _ = _ := by simp; ring

lemma region_area_bounds (a b : ι → ℕ) (h : ℕ → ℕ) (hh : Antitone h)
    (p H K : ℕ) (_hp : 0<p) (hH : 0<H) (hcover : p≤K*H)
    (hb : ∀ i, b i<p) (hzero : h 0≤p) (δ : ℝ)
    (hrect : ∀ U V : ℕ, U≤p → V≤p →
      |(rectCount a b U V : ℝ)/p-((U : ℝ)/p)*((V : ℝ)/p)|≤δ) :
    stairArea p H K (fun j => h ((j+1)*H))-2*K*δ ≤ (regionCount a b h : ℝ)/p ∧
      (regionCount a b h : ℝ)/p ≤ stairArea p H K (fun j => h (j*H))+2*K*δ := by
  have hs := region_staircase_sandwich a b h hh H K hH (fun i => (hb i).trans_le hcover)
  have hl := staircase_sum_error a b p H K (fun j => h ((j+1)*H)) hH hb
    (fun j => (hh (Nat.zero_le _)).trans hzero) δ hrect
  have hu := staircase_sum_error a b p H K (fun j => h (j*H)) hH hb
    (fun j => (hh (Nat.zero_le _)).trans hzero) δ hrect
  have hs1 : (∑ j ∈ range K, (sliceCount a b H j (h ((j+1)*H)) : ℝ))≤regionCount a b h := by
    exact_mod_cast hs.1
  have hs2 : (regionCount a b h : ℝ)≤∑ j ∈ range K, (sliceCount a b H j (h (j*H)) : ℝ) := by
    exact_mod_cast hs.2
  have hd1 := div_le_div_of_nonneg_right hs1 (Nat.cast_nonneg (α := ℝ) p)
  have hd2 := div_le_div_of_nonneg_right hs2 (Nat.cast_nonneg (α := ℝ) p)
  have hl' := (abs_le.mp hl).1
  have hu' := (abs_le.mp hu).2
  constructor <;> linarith
end Approximation

lemma stairArea_gap (p H K : ℕ) (h : ℕ → ℕ) (hp : 0<p) (hh : Antitone h) (hzero : h 0≤p) :
    stairArea p H K (fun j => h (j*H))-stairArea p H K (fun j => h ((j+1)*H))≤(H : ℝ)/p := by
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp
  unfold stairArea
  rw [← sum_sub_distrib]
  have hterm (j : ℕ) :
      ((h (j*H) : ℝ)/p)*((min p ((j+1)*H) : ℝ)/p-(min p (j*H) : ℝ)/p)-
      ((h ((j+1)*H) : ℝ)/p)*((min p ((j+1)*H) : ℝ)/p-(min p (j*H) : ℝ)/p) ≤
      ((H : ℝ)/(p : ℝ)^2)*((h (j*H) : ℝ)-h ((j+1)*H)) := by
    have hhj : h ((j+1)*H)≤h (j*H) := hh (by nlinarith)
    have hhj' : (0 : ℝ)≤(h (j*H) : ℝ)-h ((j+1)*H) := by
      apply sub_nonneg.mpr
      exact_mod_cast hhj
    have hw : min p ((j+1)*H)≤ min p (j*H)+H := by
      by_cases hj : j*H≤p
      · rw [min_eq_right hj]
        exact (min_le_right _ _).trans (by nlinarith)
      · rw [min_eq_left (by omega : p≤j*H)]
        exact (min_le_left _ _).trans (by omega)
    have hw' : (min p ((j+1)*H) : ℝ)-(min p (j*H) : ℝ)≤H := by
      have hr : ((min p ((j+1)*H) : ℕ) : ℝ)≤((min p (j*H) : ℕ) : ℝ)+(H : ℝ) := by exact_mod_cast hw
      push_cast at hr
      linarith
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw' hhj') (sq_nonneg (p : ℝ))
    convert hm using 1 <;> field_simp
  calc
    _ ≤ ∑ j ∈ range K, ((H : ℝ)/(p : ℝ)^2)*((h (j*H) : ℝ)-h ((j+1)*H)) := sum_le_sum fun j _ => hterm j
    _ = ((H : ℝ)/(p : ℝ)^2)*((h 0 : ℝ)-h (K*H)) := by rw [← mul_sum,sum_range_sub']; simp
    _ ≤ ((H : ℝ)/(p : ℝ)^2)*(p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hz : (h 0 : ℝ)≤p := by exact_mod_cast hzero
      have hn := Nat.cast_nonneg (α := ℝ) (h (K*H))
      linarith
    _ = _ := by field_simp

/-- Two point sets with matching rectangle distributions have matching
counts in every antitone subgraph, up to an explicit staircase boundary. -/
theorem monotone_region_comparison {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → ℕ) (c d : κ → ℕ) (h : ℕ → ℕ) (hh : Antitone h)
    (p H K : ℕ) (hp : 0<p) (hH : 0<H) (hcover : p≤K*H)
    (hb : ∀ i, b i<p) (hd : ∀ i, d i<p) (hzero : h 0≤p) (δ : ℝ)
    (hrect1 : ∀ U V : ℕ, U≤p → V≤p →
      |(rectCount a b U V : ℝ)/p-((U : ℝ)/p)*((V : ℝ)/p)|≤δ)
    (hrect2 : ∀ U V : ℕ, U≤p → V≤p →
      |(rectCount c d U V : ℝ)/p-((U : ℝ)/p)*((V : ℝ)/p)|≤δ) :
    |(regionCount a b h : ℝ)/p-(regionCount c d h : ℝ)/p|≤(H : ℝ)/p+4*K*δ := by
  have h1 := region_area_bounds a b h hh p H K hp hH hcover hb hzero δ hrect1
  have h2 := region_area_bounds c d h hh p H K hp hH hcover hd hzero δ hrect2
  have hg := stairArea_gap p H K h hp hh hzero
  rw [abs_le]
  constructor <;> linarith

#print axioms region_staircase_sandwich
#print axioms stairArea_gap
#print axioms monotone_region_comparison
end Erdos371.MonotoneRectangles
