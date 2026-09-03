import Submission.MatchingInfiniteRepairExplore
import Submission.SummableSpikesExplore

/-! A single weighted reciprocal-square-root summability condition suffices
for asymptotically prescribed representation spikes. -/
namespace Erdos66SummableMatchingSpikes
open Filter AdditiveCombinatorics Erdos66JointInfiniteRepair Erdos66ClippedRepair
  Erdos66JointWindow Erdos66SummableSpikes
open scoped Topology Classical
set_option maxHeartbeats 1600000

lemma summable_reciprocal_of_log_weight (n : ℕ → ℕ)
    (hf : Summable (fun i ↦ Real.sqrt (logScale (n i))/Real.sqrt ((n i : ℝ)+1))) :
    Summable (fun i ↦ 1/Real.sqrt ((n i : ℝ)+1)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hroot2 : 0 < Real.sqrt (Real.log (2 : ℝ)) := Real.sqrt_pos.mpr hlog2
  apply (hf.mul_left (1/Real.sqrt (Real.log (2 : ℝ)))).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hlog : Real.log 2 ≤ logScale (n i) := by
    apply Real.log_le_log (by norm_num)
    have := Nat.cast_nonneg (α := ℝ) (n i)
    linarith
  have hh : 1 ≤ (1/Real.sqrt (Real.log (2 : ℝ)))*Real.sqrt (logScale (n i)) := by
    have hroot := Real.sqrt_le_sqrt hlog
    have h : (1:ℝ) ≤ Real.sqrt (logScale (n i))/Real.sqrt (Real.log (2:ℝ)) :=
      (le_div_iff₀ hroot2).mpr (by simpa using hroot)
    simpa only [one_mul,one_div_mul_eq_div] using h
  have hd := div_le_div_of_nonneg_right hh (Real.sqrt_nonneg ((n i : ℝ)+1))
  simpa only [mul_div_assoc] using hd

/-- Discarding finitely many coordinates makes both point-collision and
old-set avoidance costs small. No fourth-power collision series is needed. -/
theorem asymptotic_prescribed_spikes (A : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (n : ℕ → ℕ)
    (hf : Summable (fun i : ℕ ↦ Real.sqrt (logScale (n i))/Real.sqrt ((n i : ℝ)+1)))
    (m : ℕ → ℕ) (hm : ∀ z, ∃ J : ℕ, ∀ L ≥ J, centerCount n L z = m z) :
    ∃ B : Set ℕ, A ⊆ B ∧
      (∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ)+2*m z ≤ sumRep B z) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
        (sumRep B z : ℝ) ≤ sumRep A z+2*m z+ε*logScale z := by
  have hq := summable_reciprocal_of_log_weight n hf
  let D := 2*Real.sqrt (2*envelopeCoeff K C)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let f : ℕ → ℝ := fun i ↦ D*(Real.sqrt (logScale (n i))/Real.sqrt ((n i : ℝ)+1))+
    1/Real.sqrt ((n i : ℝ)+1)
  have hfs : Summable f := (hf.mul_left D).add hq
  have hf0 (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  obtain ⟨J,hJ⟩ := ((tendsto_sum_nat_add f).eventually_lt_const (show (0:ℝ) < 1/8 by norm_num)).exists
  let n' (i : ℕ) := n (i+J)
  let q (i : ℕ) := n' i+1
  letI (i : ℕ) : NeZero (q i) := ⟨by dsimp [q]; omega⟩
  let m' (z : ℕ) := m z-centerCount n J z
  have hm' (z : ℕ) : ∃ J₀ : ℕ, ∀ L ≥ J₀, centerCount n' L z = m' z := by
    obtain ⟨J₀,hJ₀⟩ := hm z
    refine ⟨J₀,fun L hL ↦ ?_⟩
    have he := centerCount_add n J L z
    rw [hJ₀ (J+L) (by omega)] at he
    dsimp [m',n']
    omega
  have htail := (summable_nat_add_iff J).mpr hfs
  have hqtail := (summable_nat_add_iff J).mpr hq
  let Q := ∑' i : ℕ, 1/Real.sqrt ((n (i+J) : ℝ)+1)
  have hQ (L : ℕ) : (∑ i : Fin L, 1/Real.sqrt (q i.val : ℝ)) ≤ Q := by
    simpa only [q,n',Nat.cast_add,Nat.cast_one] using
      finite_sum_le_tsum hqtail (fun i ↦ by positivity) L
  have hcost (L : ℕ) :
      4*(∑ i : Fin L, 1/Real.sqrt (q i.val : ℝ))^2+
      (∑ i : Fin L, (2*Real.sqrt (2*envelopeCoeff K C))*Real.sqrt (logScale (n' i.val))/
        Real.sqrt (q i.val : ℝ)) ≤ 1/2 := by
    have hs : (∑ i : Fin L, f (i.val+J)) < 1/8 :=
      (finite_sum_le_tsum htail (fun i ↦ hf0 (i+J)) L).trans_lt hJ
    have hq0 : 0 ≤ ∑ i : Fin L, 1/Real.sqrt (q i.val : ℝ) := Finset.sum_nonneg (fun _ _ ↦ by positivity)
    have ha0 : 0 ≤ ∑ i : Fin L, D*Real.sqrt (logScale (n' i.val))/Real.sqrt (q i.val : ℝ) :=
      Finset.sum_nonneg (fun _ _ ↦ by positivity)
    have he : (∑ i : Fin L, f (i.val+J)) =
        (∑ i : Fin L, D*Real.sqrt (logScale (n' i.val))/Real.sqrt (q i.val : ℝ))+
        (∑ i : Fin L, 1/Real.sqrt (q i.val : ℝ)) := by
      simp only [f,Finset.sum_add_distrib,q,n',Nat.cast_add,Nat.cast_one,mul_div_assoc]
    rw [he] at hs
    have hqs : (∑ i : Fin L, 1/Real.sqrt (q i.val : ℝ))^2 ≤ (1/8:ℝ)^2 :=
      (sq_le_sq₀ hq0 (by norm_num)).mpr (by linarith)
    dsimp only [D] at hs ha0
    nlinarith
  have hsupport (i : ℕ) (b : Fin (q i)) : 0 ≤ (0:ℤ)+(b.val:ℤ) ∧ (0:ℤ)+(b.val:ℤ) ≤ n' i := by
    have hh := b.isLt
    dsimp [q] at hh
    constructor <;> omega
  obtain ⟨B,hAB,hl,hu⟩ := Erdos66MatchingInfiniteRepair.prescribed_spikes A K C hK hC hA n' q
    (fun _ ↦ 0) hsupport Q hQ hcost m' hm'
  have he : ∀ᶠ z : ℕ in atTop, m' z = m z := by
    filter_upwards [centerCount_eventually_zero n J] with z hz
    simp [m',hz]
  refine ⟨B,hAB,?_,?_⟩
  · filter_upwards [he] with z hz
    simpa only [hz] using hl z
  · intro ε hε
    filter_upwards [hu ε hε,he] with z hz hez
    simpa only [hez] using hz

end Erdos66SummableMatchingSpikes
