import Submission.HostLogarithmicResetExplore
import Submission.OneSidedResetExplore
import Submission.ResetAbsorptionExplore

/-! A checked failure of the naive moving-target diagonal argument. There
is a sequence of subsets of one structured host, pointwise convergent and
accurate at its freshly reset targets, whose limiting set does not have
coefficient one. This does not negate the conjecture in Spec.lean. -/
namespace Erdos66ResetScheduleCounterexample
open Filter AdditiveCombinatorics Erdos66HostLogarithmicReset Erdos66StructuredHost
  Erdos66OneSidedReset Erdos66ResetAbsorption Erdos66HostPatternMean
  Erdos66ResetScheduleFootprint Erdos66CentralTripleDeletion
open scoped Classical Topology
set_option maxHeartbeats 2200000

structure ResetCondition (A : Set ℕ) (d n : ℕ) (B C : Set ℕ) : Prop where
  inside : C ⊆ A
  agrees : ∀ a, a∉endpoints A (n/d^2) n → (a∈B ↔ a∈C)
  low : ⌊Real.log (n:ℝ)⌋₊-1 ≤ sumRep C n
  high : sumRep C n ≤ ⌊Real.log (n:ℝ)⌋₊
  lower : ∀ a, 2*a ≤ n → (a∈C ↔ a∈B ∨ a∈endpoints A (n/d^2) n)

lemma exists_reset_schedule (A : Set ℕ) (d N₀ : ℕ)
    (hreset : ∀ n≥N₀, ∀ B : Set ℕ, B ⊆ A → ∃ C : Set ℕ, ResetCondition A d n B C) :
    ∃ B : ℕ → Set ℕ, (∀ n, B n ⊆ A) ∧
      (∀ n≥N₀, ResetCondition A d n (B n) (B (n+1))) ∧
      (∀ n a, a∉endpoints A (n/d^2) n → (a∈B n ↔ a∈B (n+1))) := by
  let step (n : ℕ) (S : {B : Set ℕ // B ⊆ A}) : {C : Set ℕ // C ⊆ A} :=
    if hn : N₀ ≤ n then
      ⟨Classical.choose (hreset n hn S.val S.property),
        (Classical.choose_spec (hreset n hn S.val S.property)).inside⟩
    else S
  let state : ℕ → {B : Set ℕ // B ⊆ A} :=
    Nat.rec ⟨∅,Set.empty_subset A⟩ (fun n S ↦ step n S)
  have hstate (n : ℕ) : state (n+1)=step n (state n) := rfl
  have hgood (n : ℕ) (hn : N₀ ≤ n) : ResetCondition A d n (state n).val (state (n+1)).val := by
    rw [hstate]
    simp only [step,dif_pos hn]
    exact Classical.choose_spec (hreset n hn (state n).val (state n).property)
  refine ⟨fun n ↦ (state n).val,fun n ↦ (state n).property,hgood,?_⟩
  intro n a ha
  by_cases hn : N₀ ≤ n
  · exact (hgood n hn).agrees a ha
  · change a∈(state n).val ↔ a∈(state (n+1)).val
    rw [hstate]
    simp only [step,dif_neg hn]

lemma reset_diagonal_tendsto (A : Set ℕ) (B : ℕ → Set ℕ) (d N₀ : ℕ)
    (hgood : ∀ n≥N₀, ResetCondition A d n (B n) (B (n+1))) :
    Tendsto (fun n ↦ (sumRep (B (n+1)) n:ℝ)/Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hlog
  have hz : Tendsto (fun n : ℕ ↦ (1:ℝ)/Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hl := hf.sub hz
  simp only [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hf
  · filter_upwards [eventually_ge_atTop N₀,hlog.eventually_ge_atTop 1] with n hn hlog1
    have hpos : 0<Real.log (n:ℝ) := by linarith
    have hnat : ⌊Real.log (n:ℝ)⌋₊ ≤ sumRep (B (n+1)) n+1 := by
      have hh := (hgood n hn).low
      omega
    have hreal : (⌊Real.log (n:ℝ)⌋₊:ℝ)-1 ≤ sumRep (B (n+1)) n := by
      have hh : (⌊Real.log (n:ℝ)⌋₊:ℝ) ≤ (sumRep (B (n+1)) n:ℝ)+1 := by exact_mod_cast hnat
      linarith
    simpa only [sub_div] using div_le_div_of_nonneg_right hreal hpos.le
  · filter_upwards [eventually_ge_atTop N₀,hlog.eventually_ge_atTop 1] with n hn hlog1
    have hreal : (sumRep (B (n+1)) n:ℝ) ≤ ⌊Real.log (n:ℝ)⌋₊ := by exact_mod_cast (hgood n hn).high
    exact div_le_div_of_nonneg_right hreal (by linarith)

 theorem exists_convergent_reset_schedule_with_wrong_limit :
    ∃ (A : Set ℕ) (B : ℕ → Set ℕ) (d N₀ : ℕ), 2 ≤ d ∧
      (∀ n, B n ⊆ A) ∧
      (∀ n≥N₀, ResetCondition A d n (B n) (B (n+1))) ∧
      (∀ a, ∀ᶠ n : ℕ in atTop, a∈B n ↔ a∈limitSet B) ∧
      (∀ a, N₀ ≤ 2*a → (a∈limitSet B ↔ a∈A)) ∧
      Tendsto (fun n ↦ (sumRep (B (n+1)) n:ℝ)/Real.log n) atTop (𝓝 1) ∧
      ¬ Tendsto (fun n ↦ (sumRep (limitSet B) n:ℝ)/Real.log n) atTop (𝓝 1) := by
  obtain ⟨A,p,NB,NT,hp,hconv,hbr,hcost,hboundary,htriple,henv⟩ := exists_structured_host
  have hhost := henv.mono fun _ h ↦ h.1
  obtain ⟨j,hj⟩ := eventually_host_reset_range A NB hboundary hhost
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hj
  let d := hostCutoff j
  have hd : 2 ≤ d := hostCutoff_ge_two j
  have hreset : ∀ n≥N₀, ∀ B : Set ℕ, B ⊆ A → ∃ C : Set ℕ, ResetCondition A d n B C := by
    intro n hn B hBA
    obtain ⟨hlo,hhi⟩ := hN₀ n hn
    obtain ⟨C,hCA,hagree,hl,hu,hchange,hlower⟩ :=
      exists_one_sided_reset A B d n ⌊Real.log (n:ℝ)⌋₊ hd hBA hlo hhi
    exact ⟨C,⟨hCA,hagree,hl,hu,hlower⟩⟩
  obtain ⟨B,hBA,hgood,hstep⟩ := exists_reset_schedule A d N₀ hreset
  have hlower := fun n hn ↦ (hgood n hn).lower
  refine ⟨A,B,d,N₀,hd,hBA,hgood,?_,limitSet_recovers_host A B d N₀ hd hBA hlower,
    reset_diagonal_tendsto A B d N₀ hgood,limitSet_not_one A B d N₀ hd hBA hlower hhost⟩
  intro a
  exact eventually_constant_coordinate B (fun n ↦ endpoints A (n/d^2) n) hstep
    (central_support_escape A d (by omega)) a

end Erdos66ResetScheduleCounterexample
