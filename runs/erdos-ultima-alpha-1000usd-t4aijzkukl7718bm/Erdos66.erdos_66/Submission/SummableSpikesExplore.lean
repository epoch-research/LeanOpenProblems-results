import Submission.JointInfiniteRepairExplore

/-! Summability, rather than an initially small total cost, suffices for
asymptotic prescribed spikes: discard finitely many coordinates first. -/
namespace Erdos66SummableSpikes
open Filter AdditiveCombinatorics Erdos66JointInfiniteRepair Erdos66ClippedRepair
  Erdos66JointWindow
open scoped Topology Classical
set_option maxHeartbeats 1400000

lemma centerCount_eq_sum (n : ℕ → ℕ) (L z : ℕ) :
    centerCount n L z = ∑ i ∈ Finset.range L, if n i = z then 1 else 0 := by
  rw [centerCount, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ if n i = z then 1 else 0) L

lemma centerCount_add (n : ℕ → ℕ) (J L z : ℕ) :
    centerCount n (J+L) z = centerCount n J z + centerCount (fun i ↦ n (i+J)) L z := by
  simp only [centerCount_eq_sum, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.add_comm J i]

lemma centerCount_eventually_zero (n : ℕ → ℕ) (J : ℕ) :
    ∀ᶠ z : ℕ in atTop, centerCount n J z = 0 := by
  have hh : ∀ᶠ z : ℕ in atTop, ∀ i : Fin J, n i.val < z :=
    eventually_all.mpr (fun i ↦ eventually_gt_atTop (n i.val))
  filter_upwards [hh] with z hz
  rw [centerCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi he
  have ht := hz i
  omega

lemma finite_sum_le_tsum {f : ℕ → ℝ} (hf : Summable f) (hpos : ∀ i, 0 ≤ f i) (L : ℕ) :
    (∑ i : Fin L, f i.val) ≤ ∑' i, f i := by
  rw [Fin.sum_univ_eq_sum_range]
  exact hf.sum_le_tsum _ (fun i _ ↦ hpos i)

/-- The three summability hypotheses control collisions, old-point avoidance,
and the total mixed-hit mass. Only finitely many prescribed spikes may be
omitted, which is harmless for all asymptotic conclusions. -/
theorem asymptotic_prescribed_spikes (A : Set ℕ) (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (n : ℕ → ℕ)
    (hc : Summable (fun i : ℕ ↦ ((i : ℝ)+1)^4 / ((n i : ℝ)+1)))
    (hf : Summable (fun i : ℕ ↦ Real.sqrt (logScale (n i)) / Real.sqrt ((n i : ℝ)+1)))
    (hq : Summable (fun i : ℕ ↦ 1 / Real.sqrt ((n i : ℝ)+1)))
    (m : ℕ → ℕ) (hm : ∀ z, ∃ J : ℕ, ∀ L ≥ J, centerCount n L z = m z) :
    ∃ B : Set ℕ, A ⊆ B ∧
      (∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ) + 2*m z ≤ sumRep B z) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
        (sumRep B z : ℝ) ≤ sumRep A z + 2*m z + ε*logScale z := by
  let D := 2*Real.sqrt (2*envelopeCoeff K C)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let f : ℕ → ℝ := fun i ↦ 20*(((i : ℝ)+1)^4 / ((n i : ℝ)+1)) +
    D*(Real.sqrt (logScale (n i)) / Real.sqrt ((n i : ℝ)+1))
  have hfs : Summable f := (hc.mul_left 20).add (hf.mul_left D)
  have hf0 (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  obtain ⟨J,hJ⟩ := ((tendsto_sum_nat_add f).eventually_lt_const
    (show (0 : ℝ) < 1/2 by norm_num)).exists
  let n' (i : ℕ) := n (i+J)
  let q (i : ℕ) := n' i + 1
  letI (i : ℕ) : NeZero (q i) := ⟨by dsimp [q]; omega⟩
  let m' (z : ℕ) := m z - centerCount n J z
  have hm' (z : ℕ) : ∃ J₀ : ℕ, ∀ L ≥ J₀, centerCount n' L z = m' z := by
    obtain ⟨J₀,hJ₀⟩ := hm z
    refine ⟨J₀, fun L hL ↦ ?_⟩
    have he := centerCount_add n J L z
    rw [hJ₀ (J+L) (by omega)] at he
    dsimp [m',n']
    omega
  have htail := (summable_nat_add_iff J).mpr hfs
  have hqtail := (summable_nat_add_iff J).mpr hq
  let Q := ∑' i : ℕ, 1 / Real.sqrt ((n (i+J) : ℝ)+1)
  have hQ (L : ℕ) : (∑ i : Fin L, 1 / Real.sqrt (q i.val : ℝ)) ≤ Q := by
    simpa only [q,n',Nat.cast_add,Nat.cast_one] using
      finite_sum_le_tsum hqtail (fun i ↦ by positivity) L
  have hcost (L : ℕ) :
      (∑ i : Fin L, 4*((i.val : ℝ)+1)^2 / q i.val) +
      (∑ i : Fin L, 16*((i.val : ℝ)+1)^4 / q i.val) +
      (∑ i : Fin L, (2*Real.sqrt (2*envelopeCoeff K C))*Real.sqrt (logScale (n' i.val)) /
        Real.sqrt (q i.val : ℝ)) ≤ 1/2 := by
    have hb : ∀ i : Fin L,
        4*((i.val : ℝ)+1)^2 / q i.val + 16*((i.val : ℝ)+1)^4 / q i.val +
          D*Real.sqrt (logScale (n' i.val)) / Real.sqrt (q i.val : ℝ) ≤ f (i.val+J) := by
      intro i
      have hi0 := Nat.cast_nonneg (α := ℝ) i.val
      have hJ0 := Nat.cast_nonneg (α := ℝ) J
      have hs : ((i.val : ℝ)+1)^2 ≤ ((i.val : ℝ)+1)^4 := by
        nlinarith [sq_nonneg ((i.val : ℝ)+1), sq_nonneg (((i.val : ℝ)+1)^2-1)]
      have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ i.val+1 by positivity)
        (show (i.val : ℝ)+1 ≤ (i.val : ℝ)+J+1 by linarith) 4
      have hnum : 4*((i.val : ℝ)+1)^2 + 16*((i.val : ℝ)+1)^4 ≤
          20*(((i.val : ℝ)+J)+1)^4 := by nlinarith
      have hd := div_le_div_of_nonneg_right hnum (show (0 : ℝ) ≤ (n (i.val+J) : ℝ)+1 by positivity)
      dsimp [f,q,n']
      push_cast
      dsimp [D] at hd ⊢
      simp only [add_div, mul_div_assoc] at hd ⊢
      linarith
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin L))) ↦ hb i)
    simp only [Finset.sum_add_distrib] at hh
    have hs := finite_sum_le_tsum htail (fun i ↦ hf0 (i+J)) L
    have hle := hh.trans (hs.trans hJ.le)
    exact hle
  have hsupport (i : ℕ) (b : Fin (q i)) : 0 ≤ (0 : ℤ)+(b.val : ℤ) ∧ (0 : ℤ)+(b.val : ℤ) ≤ n' i := by
    have hh := b.isLt
    dsimp [q] at hh
    constructor <;> omega
  obtain ⟨B,hAB,hl,hu⟩ := prescribed_spikes A K C hK hC hA n' q (fun _ ↦ 0)
    hsupport Q hQ hcost m' hm'
  have he : ∀ᶠ z : ℕ in atTop, m' z = m z := by
    filter_upwards [centerCount_eventually_zero n J] with z hz
    simp [m',hz]
  refine ⟨B,hAB,?_,?_⟩
  · filter_upwards [he] with z hz
    simpa only [hz] using hl z
  · intro ε hε
    filter_upwards [hu ε hε,he] with z hz hez
    simpa only [hez] using hz

end Erdos66SummableSpikes
