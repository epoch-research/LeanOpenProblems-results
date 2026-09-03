import Submission.FinitePowerTaylor

/-!
Optimally centered finite power energies. After a transition, evaluating at
ANY proposed center bounds the new minimum. This permits a drift argument
without differentiating the stochastic minimizing center or confusing it
with the moving arithmetic mean.
-/
namespace Erdos773.FiniteCenteredPower
open Finset
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*}

def powerSum (S : Finset α) (f : α → ℝ) (p : ℕ) (c : ℝ) : ℝ :=
  ∑ u ∈ S, |f u-c|^p

/-- Every finite power energy has a global minimizing center, including
empty data and the zeroth power. A compact interval containing the data
already contains a minimizer. -/
theorem exists_minimizer (S : Finset α) (f : α → ℝ) (p : ℕ) :
    ∃ c : ℝ, ∀ a : ℝ, powerSum S f p c ≤ powerSum S f p a := by
  classical
  let M := ∑ u ∈ S, |f u|
  have hM : 0 ≤ M := sum_nonneg (fun u _ => abs_nonneg (f u))
  have hf (u : α) (hu : u ∈ S) : |f u| ≤ M :=
    single_le_sum (fun v _ => abs_nonneg (f v)) hu
  have hc : Continuous (powerSum S f p) := by unfold powerSum; fun_prop
  obtain ⟨c, hcI, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (-M) M).Nonempty from ⟨0, by constructor <;> linarith⟩) hc.continuousOn
  refine ⟨c, ?_⟩
  intro a
  by_cases hlo : a < -M
  · apply (hmin (show -M ∈ Set.Icc (-M) M by constructor <;> linarith)).trans
    apply sum_le_sum
    intro u hu
    apply pow_le_pow_left₀ (abs_nonneg _)
    have hfu := (abs_le.mp (hf u hu)).1
    rw [abs_of_nonneg (show 0 ≤ f u-(-M) by linarith),
      abs_of_nonneg (show 0 ≤ f u-a by linarith)]
    linarith
  · by_cases hhi : M < a
    · apply (hmin (show M ∈ Set.Icc (-M) M by constructor <;> linarith)).trans
      apply sum_le_sum
      intro u hu
      apply pow_le_pow_left₀ (abs_nonneg _)
      have hfu := (abs_le.mp (hf u hu)).2
      rw [abs_of_nonpos (show f u-M ≤ 0 by linarith),
        abs_of_nonpos (show f u-a ≤ 0 by linarith)]
      linarith
    · exact hmin ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

/-- No equivariance of this chosen center is presumed. The minimized ENERGY
is independent of which minimizing center is chosen. -/
def center (S : Finset α) (f : α → ℝ) (p : ℕ) : ℝ :=
  Classical.choose (exists_minimizer S f p)

def energy (S : Finset α) (f : α → ℝ) (p : ℕ) : ℝ := powerSum S f p (center S f p)

theorem energy_le (S : Finset α) (f : α → ℝ) (p : ℕ) (a : ℝ) :
    energy S f p ≤ powerSum S f p a := Classical.choose_spec (exists_minimizer S f p) a

lemma energy_nonneg (S : Finset α) (f : α → ℝ) (p : ℕ) : 0 ≤ energy S f p := by
  unfold energy powerSum
  positivity

lemma point_power_le (S : Finset α) (f : α → ℝ) (p : ℕ) {u : α} (hu : u ∈ S) :
    |f u-center S f p|^p ≤ energy S f p :=
  single_le_sum (fun v _ => pow_nonneg (abs_nonneg (f v-center S f p)) p) hu

/-- A global high-moment bound controls EVERY point relative to the center. -/
theorem point_lt_of_energy_lt (S : Finset α) (f : α → ℝ) (p : ℕ)
    {R : ℝ} (hR : 0 ≤ R) (hE : energy S f p < R^p) {u : α} (hu : u ∈ S) :
    |f u-center S f p| < R := by
  by_contra hn
  have hh := pow_le_pow_left₀ hR (le_of_not_gt hn) p
  exact (not_lt_of_ge (hh.trans (point_power_le S f p hu))) hE

/-- Bounding old data about any center bounds the minimum energy. -/
theorem energy_le_uniform (S : Finset α) (f : α → ℝ) (p : ℕ) (a R : ℝ)
    (hR : ∀ u ∈ S, |f u-a| ≤ R) : energy S f p ≤ S.card*R^p := by
  apply (energy_le S f p a).trans
  calc
    _ ≤ ∑ _u ∈ S, R^p := sum_le_sum (fun u hu => pow_le_pow_left₀ (abs_nonneg _) (hR u hu) p)
    _ = _ := by simp

/-- Translation changes the minimizing center but not the minimized energy. -/
theorem energy_translate (S : Finset α) (f : α → ℝ) (p : ℕ) (a : ℝ) :
    energy S (fun u => f u+a) p = energy S f p := by
  apply le_antisymm
  · have hh := energy_le S (fun u => f u+a) p (center S f p+a)
    simpa only [powerSum, add_sub_add_right_eq_sub] using hh
  · have hh := energy_le S f p (center S (fun u => f u+a) p-a)
    have he : powerSum S f p (center S (fun u => f u+a) p-a) =
        energy S (fun u => f u+a) p := by
      unfold powerSum energy
      apply sum_congr rfl
      intro u hu
      congr 2
      ring
    rwa [he] at hh

/-- Deleting coordinates is favorable. The new center is tested at an
arbitrary candidate, and the entire old energy is charged before deletion. -/
theorem survivor_step {S T : Finset α} (hTS : T ⊆ S) (f g : α → ℝ) (p : ℕ) (a : ℝ) :
    energy T g p-energy S f p ≤
      ∑ u ∈ T, (|g u-a|^p-|f u-center S f p|^p) := by
  have hnew := energy_le T g p a
  have hold : (∑ u ∈ T, |f u-center S f p|^p) ≤ energy S f p :=
    sum_le_sum_of_subset_of_nonneg hTS (fun u _ _ => pow_nonneg (abs_nonneg _) p)
  rw [sum_sub_distrib]
  change energy T g p ≤ ∑ u ∈ T, |g u-a|^p at hnew
  linarith only [hnew, hold]

/-- The survival step pays a variance-sensitive Taylor remainder. A proposed
next center may depend on the action; no derivative of the minimizing center
is used. Evenness is required only to convert powers to nonnegative energy. -/
theorem survivor_taylor {S T : Finset α} (hTS : T ⊆ S) (f g : α → ℝ)
    (n : ℕ) (hn : Even (n+2)) (a B : ℝ)
    (hB : ∀ u ∈ T, |(g u-a)-(f u-center S f (n+2))| ≤ B) :
    energy T g (n+2)-energy S f (n+2) ≤
      ∑ u ∈ T, ((n+2:ℕ)*(f u-center S f (n+2))^(n+1)*
        ((g u-a)-(f u-center S f (n+2)))+
        FinitePowerTaylor.coefficient n*(|f u-center S f (n+2)|^n+B^n)*
          ((g u-a)-(f u-center S f (n+2)))^2) := by
  apply (survivor_step hTS f g (n+2) a).trans
  apply sum_le_sum
  intro u hu
  have hh := (abs_le.mp (FinitePowerTaylor.bounded_remainder
    (f u-center S f (n+2)) ((g u-a)-(f u-center S f (n+2))) B n (hB u hu))).2
  rw [add_sub_cancel] at hh
  rw [hn.pow_abs, hn.pow_abs]
  linarith only [hh]

#print axioms exists_minimizer
#print axioms point_lt_of_energy_lt
#print axioms energy_translate
#print axioms survivor_step
#print axioms survivor_taylor
end
end Erdos773.FiniteCenteredPower
