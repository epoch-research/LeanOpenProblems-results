import Submission.OneSidedResetExplore
import Submission.ResetScheduleFootprintExplore

/-! Repeating restore-then-upper-delete at every sufficiently large target
recovers the entire host outside a finite prefix. This is a limitation of
that specific reset algorithm, not a disproof of Erdős Problem 66. -/
namespace Erdos66ResetAbsorption
open Filter AdditiveCombinatorics Erdos66OneSidedReset Erdos66ResetScheduleFootprint
  Erdos66CentralTripleDeletion Erdos66CentralEndpointReset
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma eventually_absorbed (A : Set ℕ) (B : ℕ → Set ℕ) (d N₀ : ℕ) (hd : 2 ≤ d)
    (hlower : ∀ n≥N₀, ∀ a, 2*a ≤ n →
      (a∈B (n+1) ↔ a∈B n ∨ a∈endpoints A (n/d^2) n))
    (a : ℕ) (ha : a∈A) (hN : N₀ ≤ 2*a) :
    ∀ t≥2*a+1, a∈B t := by
  have hstart : a∈B (2*a+1) :=
    (hlower (2*a) hN a le_rfl).mpr (Or.inr (diagonal_endpoint A d a hd ha))
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hstart
  | succ t ht ih => exact (hlower t (by omega) a (by omega)).mpr (Or.inl ih)

 theorem limitSet_recovers_host (A : Set ℕ) (B : ℕ → Set ℕ) (d N₀ : ℕ) (hd : 2 ≤ d)
    (hB : ∀ t, B t ⊆ A)
    (hlower : ∀ n≥N₀, ∀ a, 2*a ≤ n →
      (a∈B (n+1) ↔ a∈B n ∨ a∈endpoints A (n/d^2) n)) :
    ∀ a, N₀ ≤ 2*a → (a∈limitSet B ↔ a∈A) := by
  intro a hN
  constructor
  · exact fun ha ↦ limitSet_subset A B hB ha
  · intro ha
    exact ⟨2*a+1,eventually_absorbed A B d N₀ hd hlower a ha hN⟩

lemma limitSet_host_rep_bound (A : Set ℕ) (B : ℕ → Set ℕ) (d N₀ : ℕ) (hd : 2 ≤ d)
    (hB : ∀ t, B t ⊆ A)
    (hlower : ∀ n≥N₀, ∀ a, 2*a ≤ n →
      (a∈B (n+1) ↔ a∈B n ∨ a∈endpoints A (n/d^2) n)) (z : ℕ) :
    |(sumRep (limitSet B) z:ℝ)-sumRep A z| ≤ 2*(N₀:ℝ) := by
  have hh := localized_edit_bound A A (limitSet B) (Finset.range N₀) (Set.Subset.refl _)
    (limitSet_subset A B hB) (fun a ha ↦
      (limitSet_recovers_host A B d N₀ hd hB hlower a (by
        simp only [Finset.mem_range,not_lt] at ha; omega)).symm) z
  have hc : ((hits A (Finset.range N₀) z).card:ℝ) ≤ N₀ := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range N₀)
  exact hh.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

lemma limitSet_not_one (A : Set ℕ) (B : ℕ → Set ℕ) (d N₀ : ℕ) (hd : 2 ≤ d)
    (hB : ∀ t, B t ⊆ A)
    (hlower : ∀ n≥N₀, ∀ a, 2*a ≤ n →
      (a∈B (n+1) ↔ a∈B n ∨ a∈endpoints A (n/d^2) n))
    (hhost : ∀ᶠ n : ℕ in atTop, 448*Real.log (n:ℝ) ≤ (sumRep A n:ℝ)) :
    ¬ Tendsto (fun n ↦ (sumRep (limitSet B) n:ℝ)/Real.log n) atTop (𝓝 1) := by
  intro hlim
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlt := hlim.eventually_lt_const (show (1:ℝ)<2 by norm_num)
  obtain ⟨n,hn,hlogN,hlog1,hlt⟩ := (hhost.and ((hlog.eventually_ge_atTop (N₀:ℝ)).and
    ((hlog.eventually_ge_atTop 1).and hlt))).exists
  have hb := (abs_le.mp (limitSet_host_rep_bound A B d N₀ hd hB hlower n)).1
  have hlt' := (div_lt_iff₀ (by linarith : 0<Real.log (n:ℝ))).mp hlt
  linarith

end Erdos66ResetAbsorption
