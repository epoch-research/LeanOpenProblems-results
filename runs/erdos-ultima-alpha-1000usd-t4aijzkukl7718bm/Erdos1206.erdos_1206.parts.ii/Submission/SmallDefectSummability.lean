import Submission.DefectCollisionCounting
import Submission.SummableDivisorCover

/-!
The reciprocal maximum-root mass of ordered cubic collisions whose
root-sum defect k satisfies k^32 <= d is summable. Consequently a
positive-lower-density source can exclude every dilation of every such
collision. The unrestricted density conjecture remains a separate question.
-/
namespace Erdos1206.SmallDefectSummability
open DefectCollisionCounting Finset
open scoped Classical

abbrev SmallCollision := {e : Collision // e.defect^32≤e.d}

def shellIndex (e : SmallCollision) : ℕ := Nat.log (2^32) e.val.d

lemma shell_bounds (e : SmallCollision) :
    2^(32*shellIndex e)≤e.val.d ∧ e.val.d<2^(32*(shellIndex e+1)) ∧
      e.val.defect≤2^(shellIndex e+1) := by
  have hd : 0<e.val.d := by have := e.val.hcd; omega
  have hlo := Nat.pow_log_le_self (2^32) hd.ne'
  have hup := Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)^32) e.val.d
  change (2^32)^shellIndex e≤e.val.d at hlo
  change e.val.d<(2^32)^(shellIndex e+1) at hup
  rw [←pow_mul] at hlo hup
  refine ⟨hlo,hup,?_⟩
  have hkpow := lt_of_le_of_lt e.property hup
  have he : 32*(shellIndex e+1)=(shellIndex e+1)*32 := Nat.mul_comm _ _
  rw [he,pow_mul] at hkpow
  exact ((Nat.pow_lt_pow_iff_left (by decide : 32≠0)).mp hkpow).le

private lemma shell_card {s : Finset SmallCollision} {j : ℕ}
    (hs : ∀e∈s,shellIndex e=j) :
    s.card≤1428*countConstant*2^(24*(j+1)) := by
  have hinj : Set.InjOn (fun e : SmallCollision => e.val) (s : Set SmallCollision) :=
    Subtype.val_injective.injOn
  have hh := box_card_le (s := s.image Subtype.val) (j := j+1) (by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨_,hup,hk⟩ := shell_bounds f
    rw [hs f hf] at hup hk
    exact ⟨hk,hup.le⟩)
  rwa [card_image_iff.mpr hinj] at hh

private lemma shell_cost {s : Finset SmallCollision} {j : ℕ}
    (hs : ∀e∈s,shellIndex e=j) :
    (∑e∈s,(1:ℝ)/e.val.d)≤
      (1428*(countConstant:ℝ)*2^24)*((1:ℝ)/256)^j := by
  have hc : (s.card:ℝ)≤1428*(countConstant:ℝ)*2^(24*(j+1)) := by
    exact_mod_cast shell_card hs
  calc
    (∑e∈s,(1:ℝ)/e.val.d) ≤ ∑_e∈s,((1:ℝ)/2^(32*j)) := by
      apply sum_le_sum
      intro e he
      have hh := (shell_bounds e).1
      rw [hs e he] at hh
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hh
    _ = (s.card:ℝ)*(1/2^(32*j)) := by simp
    _ ≤ (1428*(countConstant:ℝ)*2^(24*(j+1)))*(1/2^(32*j)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (1428*(countConstant:ℝ)*2^24)*((1:ℝ)/256)^j := by
      rw [show 24*(j+1)=24+24*j by omega,pow_add,pow_mul,pow_mul]
      have hr : (1:ℝ)/256=2^24/2^32 := by norm_num
      rw [hr,div_pow]
      ring

/-- A global summability theorem in a shrinking near-diagonal regime.
No primitivity or squarefreeness condition is needed. -/
theorem small_defect_reciprocals_summable :
    Summable (fun e : SmallCollision => (1:ℝ)/e.val.d) := by
  let cost (j : ℕ) : ℝ := (1428*(countConstant:ℝ)*2^24)*((1:ℝ)/256)^j
  have hcost : Summable cost :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/256)
      (by norm_num : (1:ℝ)/256<1)).mul_left _
  apply summable_of_sum_le (fun _ => by positivity) (c := ∑'j,cost j)
  intro s
  let J := s.image shellIndex
  have hmap : ∀e∈s,shellIndex e∈J := fun e he => mem_image.mpr ⟨e,he,rfl⟩
  rw [←sum_fiberwise_of_maps_to hmap]
  calc
    (∑j∈J,∑e∈s.filter (fun e => shellIndex e=j),(1:ℝ)/e.val.d) ≤ ∑j∈J,cost j := by
      apply sum_le_sum
      intro j hj
      exact shell_cost (fun e he => (mem_filter.mp he).2)
    _ ≤ ∑'j,cost j := hcost.sum_le_tsum J (fun _ _ => by dsimp [cost]; positivity)

def maxima : Set ℕ := Set.range (fun e : SmallCollision => e.val.d)

/-- Distinct maximum roots also have summable reciprocal mass. -/
theorem maxima_reciprocals_summable :
    Summable (fun n : ℕ => if n∈maxima then (1:ℝ)/n else 0) := by
  choose f hf using (fun n : maxima => n.property)
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    rw [←hf a,←hf b,he]
  have hh := small_defect_reciprocals_summable.comp_injective hinj
  have hs : Summable (fun n : maxima => (1:ℝ)/(n.val:ℕ)) := by
    apply hh.congr
    intro n
    simp only [Function.comp_apply,hf n]
  simpa only [Set.indicator_apply] using
    (summable_subtype_iff_indicator (s := maxima) (f := fun n : ℕ => (1:ℝ)/n)).mp hs

/-- A positive-density source excludes all dilations of all small-defect
collisions, not just their primitive or unscaled representatives. -/
theorem positive_density_avoids_small_defect :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      ∀e : Collision, e.defect^32≤e.d → ∀t : ℕ, t*e.d∉A := by
  let A := divisorAvoider maxima
  have h1 : 1∉maxima := by
    rintro ⟨e,he⟩
    change e.val.d=1 at he
    have := e.val.hab
    have := e.val.hbc
    have := e.val.hcd
    omega
  have hd : 0<A.lowerDensity :=
    divisorAvoider_positive_density_of_summable h1 maxima_reciprocals_summable
  refine ⟨A,?_,hd,?_⟩
  · by_contra hf
    have hz : A.lowerDensity=0 := (Nat.hasDensity_zero_of_finite (Set.not_infinite.mp hf)).liminf_eq
    linarith
  · intro e he t ht
    exact ht.2 e.d ⟨⟨e,he⟩,rfl⟩ (dvd_mul_left e.d t)

/-- Division by a common positive divisor preserves the ordered collision
and divides the root-sum defect by the same amount. -/
lemma normalize_collision (e : Collision) {g : ℕ} (hg : 0<g)
    (hga : g∣e.a) (hgb : g∣e.b) (hgc : g∣e.c) (hgd : g∣e.d) :
    ∃ f : Collision, f.d=e.d/g ∧ f.defect=e.defect/g ∧ e.d=g*f.d := by
  have ha' : g*(e.a/g)=e.a := Nat.mul_div_cancel' hga
  have hb' : g*(e.b/g)=e.b := Nat.mul_div_cancel' hgb
  have hc' : g*(e.c/g)=e.c := Nat.mul_div_cancel' hgc
  have hd' : g*(e.d/g)=e.d := Nat.mul_div_cancel' hgd
  have hab' : e.a/g<e.b/g := Nat.div_lt_div_of_lt_of_dvd hgb e.hab
  have hbc' : e.b/g<e.c/g := Nat.div_lt_div_of_lt_of_dvd hgc e.hbc
  have hcd' : e.c/g<e.d/g := Nat.div_lt_div_of_lt_of_dvd hgd e.hcd
  have he' : (e.a/g)^3+(e.d/g)^3=(e.b/g)^3+(e.c/g)^3 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hg 3)
    simpa only [Nat.mul_add,←mul_pow,ha',hb',hc',hd'] using e.equation
  let f : Collision := ⟨e.a/g,e.b/g,e.c/g,e.d/g,hab',hbc',hcd',he'⟩
  have hk := ConicHeightProduct.defect_mul g (e.a/g) (e.b/g) (e.c/g) (e.d/g)
  rw [ha',hb',hc',hd'] at hk
  change e.defect=g*f.defect at hk
  refine ⟨f,rfl,?_,hd'.symm⟩
  rw [hk,Nat.mul_div_cancel_left _ hg]

/-- In the constructed source, the normalized defect of every surviving
collision is larger than the thirty-second root of its primitive height.
The condition involves the common gcd, not the size of an arbitrary dilation. -/
theorem positive_density_normalized_defect_lower_bound :
    ∃ A : Set ℕ, A.Infinite ∧ 0<A.lowerDensity ∧
      ∀e : Collision, e.d∈A →
        e.d / ConicHeightProduct.rootGcd e.a e.b e.c e.d <
          (e.defect / ConicHeightProduct.rootGcd e.a e.b e.c e.d)^32 := by
  obtain ⟨A,hAi,hAd,hA⟩ := positive_density_avoids_small_defect
  refine ⟨A,hAi,hAd,?_⟩
  intro e hed
  let g := ConicHeightProduct.rootGcd e.a e.b e.c e.d
  have hd : 0<e.d := by have := e.hcd; omega
  have hg : 0<g := Nat.gcd_pos_of_pos_right _ (Nat.gcd_pos_of_pos_right e.c hd)
  have hga : g∣e.a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left e.a e.b)
  have hgb : g∣e.b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right e.a e.b)
  have hgc : g∣e.c := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left e.c e.d)
  have hgd : g∣e.d := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right e.c e.d)
  obtain ⟨f,hfd,hfk,hs⟩ := normalize_collision e hg hga hgb hgc hgd
  change e.d/g<(e.defect/g)^32
  by_contra hn
  have hsmall : f.defect^32≤f.d := by rw [hfk,hfd]; omega
  exact hA f hsmall g (by rwa [←hs])

#print axioms small_defect_reciprocals_summable
#print axioms maxima_reciprocals_summable
#print axioms positive_density_avoids_small_defect
#print axioms positive_density_normalized_defect_lower_bound
end Erdos1206.SmallDefectSummability
