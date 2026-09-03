import Submission.ShortRotationLogBoundExplore

/-! A rotation discrepancy bound depending on expected interval mass,
rather than on the entire orbit length. This is a finite estimate, not a
construction settling the logarithmic representation conjecture. -/
namespace Erdos66RotationMassLogBound
open Erdos66ShortRotationLogBound Erdos66RotationFloorPerturbation
open scoped Classical
set_option maxHeartbeats 1800000

lemma rotationSum_nonneg (α x θ : ℝ) (hθ : 0≤θ) (N : ℕ) :
    0≤rotationSum α x θ N := by
  apply Finset.sum_nonneg
  intro k hk
  have hh := Int.floor_le_floor (show x+(k : ℝ)*α-θ ≤ x+(k : ℝ)*α by linarith)
  exact_mod_cast sub_nonneg.mpr hh

lemma rotationSum_mono (α x θ : ℝ) (hθ : 0≤θ) :
    Monotone (rotationSum α x θ) := by
  intro N K hNK
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNK)
  intro k hk _
  have hh := Int.floor_le_floor (show x+(k : ℝ)*α-θ ≤ x+(k : ℝ)*α by linarith)
  exact_mod_cast sub_nonneg.mpr hh

lemma rotationSum_block_multiple_upper (α θ : ℝ) (d : ℕ)
    (hblock : ∀ x : ℝ, |rotationSum α x θ d-(d : ℝ)*θ|≤5) :
    ∀ m : ℕ, ∀ x : ℝ,
      rotationSum α x θ (m*d) ≤ (m : ℝ)*((d : ℝ)*θ+5) := by
  intro m
  induction m with
  | zero => intro x; simp [rotationSum_zero]
  | succ m ih =>
    intro x
    rw [Nat.succ_mul,rotationSum_add,Nat.cast_add,Nat.cast_one]
    have hh := (abs_le.mp (hblock (x+(m*d : ℕ)*α))).2
    nlinarith [ih x]

/-- A window whose expected count is at most one has uniformly bounded
count and discrepancy, even if the orbit is very long. -/
lemma rotation_small_mass_bound (α : ℝ) (Q N : ℕ)
    (hnear : (Q : ℝ)^2*|α-Real.sqrt 2|≤1) (hNQ : N≤Q)
    (x θ : ℝ) (hθ : 0≤θ) (hmass : (N : ℝ)*θ≤1) :
    |rotationSum α x θ N-(N : ℝ)*θ|≤30 := by
  by_cases hN : N=0
  · subst N
    simp [rotationSum_zero]
  obtain ⟨d,hd,hdN,hcomp,hblock⟩ :=
    exists_good_rotation_block α Q N (Nat.pos_of_ne_zero hN) hNQ hnear
  have hm := rotationSum_mono α x θ hθ (show N≤5*d by omega)
  have hfull := rotationSum_block_multiple_upper α θ d (fun y ↦ hblock y θ) 5 x
  have hdR : (d : ℝ)≤N := by exact_mod_cast hdN
  have hmul := mul_le_mul_of_nonneg_right hdR hθ
  have hlo := rotationSum_nonneg α x θ hθ N
  rw [abs_le]
  norm_num only [Nat.cast_ofNat] at hfull
  constructor <;> nlinarith

/-- Stopping the good-block induction once expected mass is small removes
the loss log(N) for very narrow windows. No interval endpoint is omitted. -/
theorem rotation_mass_log_bound (α : ℝ) (Q : ℕ)
    (hnear : (Q : ℝ)^2*|α-Real.sqrt 2|≤1) (N : ℕ) (hNQ : N≤Q)
    (x θ : ℝ) (hθ : 0≤θ) :
    |rotationSum α x θ N-(N : ℝ)*θ| ≤
      30+50*Real.log ((N : ℝ)*θ+1) := by
  have main : ∀ N : ℕ, N≤Q → ∀ x : ℝ,
      |rotationSum α x θ N-(N : ℝ)*θ| ≤
        30+50*Real.log ((N : ℝ)*θ+1) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro hNQ x
      by_cases hsmall : (N : ℝ)*θ≤1
      · have hh := rotation_small_mass_bound α Q N hnear hNQ x θ hθ hsmall
        have hl := Real.log_nonneg (show 1≤(N : ℝ)*θ+1 by
          have := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ)≤N) hθ
          linarith)
        linarith
      have hlarge : 1<(N : ℝ)*θ := lt_of_not_ge hsmall
      have hNp : 0<N := by
        by_contra hn
        have : N=0 := by omega
        norm_num [this] at hlarge
      obtain ⟨d,hd,hdN,hcomp,hblock⟩ := exists_good_rotation_block α Q N hNp hNQ hnear
      let R := N-d
      have hRN : R<N := Nat.sub_lt hNp hd
      have hRQ : R≤Q := (Nat.sub_le N d).trans hNQ
      have hih := ih R hRN hRQ (x+(d : ℝ)*α)
      have hgood := hblock x θ
      have hdecomp : d+R=N := Nat.add_sub_of_le hdN
      have hsum := rotationSum_add α x θ d R
      rw [hdecomp] at hsum
      have hcast : (N : ℝ)=(d : ℝ)+R := by exact_mod_cast hdecomp.symm
      have herr : rotationSum α x θ N-(N : ℝ)*θ =
          (rotationSum α x θ d-(d : ℝ)*θ)+
            (rotationSum α (x+(d : ℝ)*α) θ R-(R : ℝ)*θ) := by
        rw [hsum,hcast]
        ring
      have hcompR : (N : ℝ)+1≤5*(d : ℝ) := by exact_mod_cast hcomp
      have hRle : 5*(R : ℝ)≤4*(N : ℝ) := by linarith
      have hm := mul_le_mul_of_nonneg_right hRle hθ
      have hscale : (R : ℝ)*θ+1 ≤ (9/10 : ℝ)*((N : ℝ)*θ+1) := by
        nlinarith only [hm,hlarge]
      have hRpos : 0<(R : ℝ)*θ+1 := by positivity
      have hNpos : 0<(N : ℝ)*θ+1 := by positivity
      have hlog := Real.log_le_log hRpos hscale
      rw [Real.log_mul (by norm_num : (9/10 : ℝ)≠0) hNpos.ne'] at hlog
      have hdec := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<9/10)
      have hbudget : 5+(30+50*Real.log ((R : ℝ)*θ+1)) ≤
          30+50*Real.log ((N : ℝ)*θ+1) := by linarith
      rw [herr]
      exact (abs_add_le _ _).trans ((add_le_add hgood hih).trans hbudget)
  exact main N hNQ x

lemma rotationSum_complement (α x θ : ℝ) (N : ℕ) :
    rotationSum α x θ N+rotationSum α (x-θ) (1-θ) N=(N : ℝ) := by
  unfold rotationSum
  rw [←Finset.sum_add_distrib]
  calc
    _ = ∑ _k ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have h1 : x-θ+(k : ℝ)*α=x+(k : ℝ)*α-θ := by ring
      have h2 : x-θ+(k : ℝ)*α-(1-θ)=x+(k : ℝ)*α-1 := by ring
      rw [h2,h1,Int.floor_sub_one]
      push_cast
      ring
    _ = _ := by simp

lemma rotation_complement_error (α x θ : ℝ) (N : ℕ) :
    |rotationSum α x θ N-(N : ℝ)*θ|=
      |rotationSum α (x-θ) (1-θ) N-(N : ℝ)*(1-θ)| := by
  have hh := rotationSum_complement α x θ N
  have he : rotationSum α x θ N-(N : ℝ)*θ=
      -(rotationSum α (x-θ) (1-θ) N-(N : ℝ)*(1-θ)) := by linarith
  rw [he,abs_neg]

/-- The smaller of a window and its complement determines the discrepancy
budget. The starting-phase change in the complement is retained exactly. -/
theorem rotation_balanced_mass_log_bound (α : ℝ) (Q : ℕ)
    (hnear : (Q : ℝ)^2*|α-Real.sqrt 2|≤1) (N : ℕ) (hNQ : N≤Q)
    (x θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) :
    |rotationSum α x θ N-(N : ℝ)*θ| ≤
      30+50*Real.log ((N : ℝ)*min θ (1-θ)+1) := by
  by_cases hh : θ≤1-θ
  · rw [min_eq_left hh]
    exact rotation_mass_log_bound α Q hnear N hNQ x θ hθ
  · rw [min_eq_right (le_of_not_ge hh),rotation_complement_error]
    exact rotation_mass_log_bound α Q hnear N hNQ (x-θ) (1-θ) (sub_nonneg.mpr hθ1)

end Erdos66RotationMassLogBound
