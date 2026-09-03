import Submission.ClampedPrefixContinuationExplore
import Submission.SetIntervalReplacementExplore

/-! Boolean rounding of a cumulative function centered at one half.
Small cumulative perturbations retain the exact original prefix brackets. -/
namespace Erdos66CenteredCumulativeRounding
open Erdos66Generating Erdos66Rounding Erdos66Counting
  Erdos66SetIntervalReplacement Erdos66ClampedPrefixContinuation
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def rounded (F : ℕ → ℝ) : Set ℕ :=
  {n | ⌊F (n+1)⌋-⌊F n⌋=1}

def UnitSteps (F : ℕ → ℝ) : Prop :=
  ∀ n, 0≤ F (n+1)-F n ∧ F (n+1)-F n≤ 1

lemma floor_step_binary (F : ℕ → ℝ) (hF : UnitSteps F) (n : ℕ) :
    ⌊F (n+1)⌋-⌊F n⌋=0 ∨ ⌊F (n+1)⌋-⌊F n⌋=1 := by
  have hlo := Int.floor_mono (show F n≤ F (n+1) by linarith [(hF n).1])
  have hhi := Int.floor_mono (show F (n+1)≤ F n+1 by linarith [(hF n).2])
  rw [Int.floor_add_one] at hhi
  omega

lemma rounded_indicator (F : ℕ → ℝ) (hF : UnitSteps F) (n : ℕ) :
    indicator (rounded F) n=(⌊F (n+1)⌋:ℝ)-(⌊F n⌋:ℝ) := by
  have he := floor_step_binary F hF n
  unfold indicator rounded
  simp only [Set.mem_setOf_eq]
  rcases he with he | he
  · rw [if_neg (by omega)]
    exact_mod_cast he.symm
  · rw [if_pos he]
    exact_mod_cast he.symm

lemma rounded_mass (F : ℕ → ℝ) (hF : UnitSteps F) (hF0 : F 0=1/2) (N : ℕ) :
    mass (indicator (rounded F)) N=(⌊F N⌋:ℝ) := by
  unfold mass
  simp_rw [rounded_indicator F hF]
  rw [Finset.sum_range_sub (fun n : ℕ ↦ (⌊F n⌋:ℝ)) N,hF0]
  norm_num

lemma rounded_count (F : ℕ → ℝ) (hF : UnitSteps F) (hF0 : F 0=1/2) (N : ℕ) :
    (count (rounded F) N:ℝ)=(⌊F N⌋:ℝ) := by
  rw [count_sum]
  exact rounded_mass F hF hF0 N

lemma integer_brackets_of_distance (x : ℝ) (m : ℤ) (hm : |(m:ℝ)-x|<1) :
    (⌊x⌋:ℝ)≤ m ∧ (m:ℝ)≤ (⌈x⌉:ℝ) := by
  have hb := abs_lt.mp hm
  have hlo : (⌊x⌋:ℝ)<(m:ℝ)+1 := by linarith [Int.floor_le x]
  have hhi : (m:ℝ)<(⌈x⌉:ℝ)+1 := by linarith [Int.le_ceil x]
  have hl : ⌊x⌋< m+1 := by exact_mod_cast hlo
  have hh : m< ⌈x⌉+1 := by exact_mod_cast hhi
  constructor <;> exact_mod_cast (show _ by omega)

lemma centered_floor_error (x y δ : ℝ) (h : |y-(x+1/2)|≤ δ) :
    |(⌊y⌋:ℝ)-x|≤ 1/2+δ := by
  have hh := abs_le.mp h
  have hlo := Int.lt_floor_add_one y
  have hhi := Int.floor_le y
  rw [abs_le]
  constructor <;> linarith

/-- Exact brackets, not just a bounded-discrepancy estimate, survive a
cumulative perturbation of size strictly less than one half. -/
theorem rounded_original_brackets (p F : ℕ → ℝ) (hF : UnitSteps F)
    (hF0 : F 0=1/2) (δ : ℝ) (hδ : δ<1/2)
    (hclose : ∀ n, |F n-(mass p n+1/2)|≤ δ) :
    ∀ N, PrefixBrackets p (rounded F) N := by
  intro N k hk
  rw [rounded_mass F hF hF0 k]
  exact integer_brackets_of_distance _ _
    ((centered_floor_error _ _ δ (hclose k)).trans_lt (by linarith))

lemma centered_steps (p : ℕ → ℝ) (hp : ∀ n, 0≤ p n ∧ p n≤ 1) :
    UnitSteps (fun n ↦ mass p n+1/2) := by
  intro n
  dsimp only
  rw [mass_succ]
  constructor <;> linarith [(hp n).1,(hp n).2]

noncomputable def splice (F g : ℕ → ℝ) (L R n : ℕ) : ℝ :=
  if L≤ n ∧ n≤ R then g n else F n

lemma splice_outside (F g : ℕ → ℝ) (L R n : ℕ) (hn : n<L ∨ R<n) :
    splice F g L R n=F n := by simp [splice]; omega

lemma splice_inside (F g : ℕ → ℝ) (L R n : ℕ) (hn : L≤ n ∧ n≤ R) :
    splice F g L R n=g n := by simp [splice,hn]

lemma splice_steps (F g : ℕ → ℝ) (hF : UnitSteps F) (hg : UnitSteps g)
    (L R : ℕ) (hL : F L=g L) (hR : F R=g R) : UnitSteps (splice F g L R) := by
  intro n
  by_cases hn : L≤ n ∧ n≤ R <;> by_cases hn' : L≤ n+1 ∧ n+1≤ R
  · simp only [splice,if_pos hn,if_pos hn']
    exact hg n
  · have he : n=R := by omega
    subst n
    simpa only [splice,if_pos hn,if_neg hn',←hR] using hF R
  · have he : n+1=L := by omega
    have hh := hF n
    rw [splice,splice,if_pos hn',if_neg hn]
    rw [←he] at hL
    simpa only [←hL] using hh
  · simp only [splice,if_neg hn,if_neg hn']
    exact hF n

/-- Chord slope, using the endpoint cumulative masses. -/
noncomputable def chordSlope (p : ℕ → ℝ) (L R : ℕ) : ℝ :=
  (mass p R-mass p L)/((R:ℝ)-L)

noncomputable def chord (p : ℕ → ℝ) (L R n : ℕ) : ℝ :=
  mass p L+((n:ℝ)-L)*chordSlope p L R+1/2

lemma mass_interval_bounds (p : ℕ → ℝ) (hp : Antitone p)
    (L R a b : ℕ) (hLa : L≤ a) (hab : a≤ b) (hbR : b≤ R) :
    ((b:ℝ)-a)*p R≤ mass p b-mass p a ∧
      mass p b-mass p a≤ ((b:ℝ)-a)*p L := by
  have he : mass p b-mass p a=∑ i∈Finset.Ico a b, p i := by
    rw [Finset.sum_Ico_eq_sub _ hab]
    rfl
  rw [he]
  have hlo := Finset.sum_le_sum (s:=Finset.Ico a b) (f:=fun _ ↦ p R) (g:=p)
    (fun i hi ↦ hp (by have := Finset.mem_Ico.mp hi; omega))
  have hhi := Finset.sum_le_sum (s:=Finset.Ico a b) (f:=p) (g:=fun _ ↦ p L)
    (fun i hi ↦ hp (by have := Finset.mem_Ico.mp hi; omega))
  simpa only [Finset.sum_const,nsmul_eq_mul,Nat.card_Ico,Nat.cast_sub hab] using And.intro hlo hhi

lemma chordSlope_bounds (p : ℕ → ℝ) (hp : Antitone p) (L R : ℕ) (hLR : L<R) :
    p R≤ chordSlope p L R ∧ chordSlope p L R≤ p L := by
  have hr : (0:ℝ)<(R:ℝ)-L := by exact_mod_cast (show (L:ℝ)<R by exact_mod_cast hLR) |> sub_pos.mpr
  have hh := mass_interval_bounds p hp L R L R le_rfl hLR.le le_rfl
  unfold chordSlope
  constructor
  · apply (le_div_iff₀ hr).mpr
    nlinarith [hh.1]
  · apply (div_le_iff₀ hr).mpr
    nlinarith [hh.2]

lemma chord_endpoints (p : ℕ → ℝ) (L R : ℕ) (hLR : L<R) :
    chord p L R L=mass p L+1/2 ∧ chord p L R R=mass p R+1/2 := by
  constructor
  · simp [chord]
  · have hh : (R:ℝ)-(L:ℝ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hLR.ne')
    simp only [chord,chordSlope,mul_div_cancel₀ _ hh]
    field_simp
    ring

lemma chord_steps (p : ℕ → ℝ) (hp : ∀ n, 0≤ p n ∧ p n≤ 1)
    (hm : Antitone p) (L R : ℕ) (hLR : L<R) : UnitSteps (chord p L R) := by
  have hh := chordSlope_bounds p hm L R hLR
  intro n
  have he : chord p L R (n+1)-chord p L R n=chordSlope p L R := by unfold chord; push_cast; ring
  rw [he]
  constructor <;> linarith [(hp R).1,(hp L).2]

/-- On a flat window the chord is uniformly close to the true cumulative
profile. The bound does not depend on the previous rounding choices. -/
lemma chord_error (p : ℕ → ℝ) (hm : Antitone p) (L R n : ℕ)
    (hLR : L<R) (hLn : L≤ n) (hnR : n≤ R) :
    |chord p L R n-(mass p n+1/2)|≤ ((R:ℝ)-L)*(p L-p R) := by
  have hs := chordSlope_bounds p hm L R hLR
  have hh := mass_interval_bounds p hm L R L n le_rfl hLn hnR
  have hn0 : (0:ℝ)≤ (n:ℝ)-L := by exact_mod_cast (show (L:ℝ)≤ n by exact_mod_cast hLn) |> sub_nonneg.mpr
  have hn1 : (n:ℝ)-(L:ℝ)≤ (R:ℝ)-L := by
    have hh : (n:ℝ)≤ R := by exact_mod_cast hnR
    linarith
  have hd : 0≤ p L-p R := sub_nonneg.mpr (hm hLR.le)
  have hlow := mul_le_mul_of_nonneg_left hs.1 hn0
  have hhi := mul_le_mul_of_nonneg_left hs.2 hn0
  have hsize := mul_le_mul_of_nonneg_right hn1 hd
  unfold chord
  rw [abs_le]
  constructor <;> nlinarith

end Erdos66CenteredCumulativeRounding
