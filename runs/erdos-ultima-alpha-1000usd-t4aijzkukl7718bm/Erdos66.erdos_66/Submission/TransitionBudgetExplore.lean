import Submission.TransitionLinearExplore
import Submission.AdditiveDeficitMassExplore
import Submission.ClippedRepairExplore

/-! Sparse perturbations cannot supply a fixed positive transition deficit
on a positive proportion of targets. This does not rule out a logarithmic
witness; it rules out using negligible additions to bridge a dense gap. -/
namespace Erdos66TransitionBudget
open Filter AdditiveCombinatorics Erdos66TransitionLinear Erdos66AdditiveDeficitMass
  Erdos66ClippedRepair
open scoped Topology Classical
set_option maxHeartbeats 1400000

/-- A deficit epsilon*log(N+2) on at least rho*N targets before 2N requires
at least epsilon*rho/(2K) times sqrt(N*log(N+2)) new points, if the old set
has at most K times that scale of points. -/
theorem dense_transition_card_lower (A F T : Finset ℕ) (N : ℕ) (hN : 0 < N)
    (hA : ∀ a ∈ A, a < N) (hF : ∀ b ∈ F, N ≤ b) (hT : ∀ n ∈ T, n < 2*N)
    (K ε ρ : ℝ) (hK : 0 < K) (hε : 0 < ε) (hρ : 0 < ρ)
    (hbase : (A.card : ℝ) ≤ K*Real.sqrt ((N : ℝ)*logScale N))
    (hsize : ρ*N ≤ T.card)
    (hdef : ∀ n ∈ T, (sumRep (A : Set ℕ) n : ℝ)+ε*logScale N ≤
      sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n) :
    (ε*ρ/(2*K))*Real.sqrt ((N : ℝ)*logScale N) ≤ F.card := by
  let R := Real.sqrt ((N : ℝ)*logScale N)
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos hN' (logScale_pos N))
  have hR2 : R^2 = (N : ℝ)*logScale N := Real.sq_sqrt (mul_nonneg hN'.le (logScale_pos N).le)
  have hmass := transition_increment_mass A F T N hA hF hT
  have hlower : (ε*logScale N)*T.card ≤
      ∑ n ∈ T, ((sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n) := by
    have hh := Finset.sum_le_sum (fun n hn ↦ show ε*logScale N ≤
        (sumRep ((A ∪ F : Finset ℕ) : Set ℕ) n : ℝ)-sumRep (A : Set ℕ) n by
      have hd := hdef n hn
      linarith)
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hh
  have hsize' := mul_le_mul_of_nonneg_left hsize (mul_nonneg hε.le (logScale_pos N).le)
  have hbase' := mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg (α := ℝ) F.card)
  change (A.card : ℝ)*F.card ≤ K*R*F.card at hbase'
  have hmain : ε*ρ*R^2 ≤ 2*K*R*F.card := by
    calc
      _ = (ε*logScale N)*(ρ*N) := by rw [hR2]; ring
      _ ≤ 2*(A.card : ℝ)*F.card := hsize'.trans (hlower.trans hmass)
      _ ≤ _ := by nlinarith [hbase']
  have hred : ε*ρ*R ≤ 2*K*F.card := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hmain]
  have hden : 0 < 2*K := by positivity
  calc
    _ = (ε*ρ*R)/(2*K) := by dsimp [R]; ring
    _ ≤ _ := (div_le_iff₀ hden).mpr (by nlinarith [hred])

/-- A family filling fixed-proportion transition deficits cannot have a
vanishing normalized number of added points. This is not the negation of
the original conjecture: it concerns one specified extension procedure. -/
theorem dense_transition_not_negligible (A F T : ℕ → Finset ℕ) (N : ℕ → ℕ)
    (K ε ρ : ℝ) (hK : 0 < K) (hε : 0 < ε) (hρ : 0 < ρ)
    (hdata : ∀ᶠ k : ℕ in atTop, 0 < N k ∧
      (∀ a ∈ A k, a < N k) ∧ (∀ b ∈ F k, N k ≤ b) ∧
      (∀ n ∈ T k, n < 2*N k) ∧
      ((A k).card : ℝ) ≤ K*Real.sqrt ((N k : ℝ)*logScale (N k)) ∧
      ρ*N k ≤ (T k).card ∧
      ∀ n ∈ T k, (sumRep (A k : Set ℕ) n : ℝ)+ε*logScale (N k) ≤
        sumRep ((A k ∪ F k : Finset ℕ) : Set ℕ) n) :
    ¬ Tendsto (fun k ↦ ((F k).card : ℝ)/Real.sqrt ((N k : ℝ)*logScale (N k)))
      atTop (𝓝 0) := by
  intro hlim
  have hp : 0 < ε*ρ/(2*K) := div_pos (mul_pos hε hρ) (by positivity)
  have hevent : ∀ᶠ k : ℕ in atTop, ε*ρ/(2*K) ≤
      ((F k).card : ℝ)/Real.sqrt ((N k : ℝ)*logScale (N k)) := by
    filter_upwards [hdata] with k hk
    obtain ⟨hN,hA,hF,hT,hbase,hsize,hdef⟩ := hk
    have hR : 0 < Real.sqrt ((N k : ℝ)*logScale (N k)) :=
      Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast hN) (logScale_pos _))
    exact (le_div_iff₀ hR).mpr (dense_transition_card_lower (A k) (F k) (T k)
      (N k) hN hA hF hT K ε ρ hK hε hρ hbase hsize hdef)
  have hh : ε*ρ/(2*K) ≤ 0 := ge_of_tendsto hlim hevent
  linarith

/-- More generally, negligible added-point density implies negligible total
representation increment on any finite target family. -/
theorem normalized_increment_zero (A F T : ℕ → Finset ℕ) (R : ℕ → ℝ) (K : ℝ)
    (hdis : ∀ k, Disjoint (A k) (F k)) (hR : ∀ᶠ k : ℕ in atTop, 0 < R k)
    (hA : ∀ᶠ k : ℕ in atTop, ((A k).card : ℝ) ≤ K*R k)
    (hF : Tendsto (fun k ↦ ((F k).card : ℝ)/R k) atTop (𝓝 0)) :
    Tendsto (fun k ↦ incrementMass (A k) (F k) (T k)/(R k)^2) atTop (𝓝 0) := by
  have hupper : Tendsto (fun k ↦ 2*K*(((F k).card : ℝ)/R k)+(((F k).card : ℝ)/R k)^2)
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero] using
      (hF.const_mul (2*K)).add (hF.pow 2)
  refine squeeze_zero' ?_ ?_ hupper
  · exact Eventually.of_forall (fun k ↦ div_nonneg (incrementMass_nonneg _ _ _ (hdis k)) (sq_nonneg _))
  · filter_upwards [hR,hA] with k hk hAk
    have hh := incrementMass_le (A k) (F k) (T k) (hdis k)
    have hm := mul_le_mul_of_nonneg_right hAk (Nat.cast_nonneg (α := ℝ) (F k).card)
    have hb : incrementMass (A k) (F k) (T k) ≤
        2*K*R k*(F k).card+((F k).card : ℝ)^2 := by nlinarith
    have hd := div_le_div_of_nonneg_right hb (sq_nonneg (R k))
    apply hd.trans_eq
    field_simp <;> ring

/-- Hence every fixed positive normalized deficit eventually exceeds the
entire repair budget of such a negligible perturbation. -/
theorem eventually_small_total_increment (A F T : ℕ → Finset ℕ) (R : ℕ → ℝ) (K : ℝ)
    (hdis : ∀ k, Disjoint (A k) (F k)) (hR : ∀ᶠ k : ℕ in atTop, 0 < R k)
    (hA : ∀ᶠ k : ℕ in atTop, ((A k).card : ℝ) ≤ K*R k)
    (hF : Tendsto (fun k ↦ ((F k).card : ℝ)/R k) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, incrementMass (A k) (F k) (T k) < δ*(R k)^2 := by
  filter_upwards [hR,(normalized_increment_zero A F T R K hdis hR hA hF).eventually_lt_const hδ]
    with k hk hmass
  exact (div_lt_iff₀ (sq_pos_of_pos hk)).mp hmass

end Erdos66TransitionBudget
