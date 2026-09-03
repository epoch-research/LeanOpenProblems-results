import Submission.NaturalRepairBridgeExplore
import Submission.RepairParametersExplore

/-! One-target repairs with arbitrarily small logarithmic collateral at every
other natural target. This does not provide a repair of a dense set of gaps. -/
namespace Erdos66GlobalRepair
open Filter AdditiveCombinatorics Erdos66OriginRepair Erdos66FiniteRepair
  Erdos66LocalWindow Erdos66NaturalRepairBridge Erdos66RepairParameters Erdos66Explore
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma polynomial_cutoff_log_bound (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h N : ℕ) (hN : 2 ≤ N) :
    K + C * Real.log (2 * (N : ℝ) ^ h + 2) ≤
      (K / Real.log 2 + C * ((h : ℝ) + 2)) * Real.log N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2
  have hp : (0 : ℝ) < (N : ℝ) ^ h := by positivity
  have hp1 : (1 : ℝ) ≤ (N : ℝ) ^ h := one_le_pow₀ (by linarith)
  have harg : 2 * (N : ℝ) ^ h + 2 ≤ 4 * (N : ℝ) ^ h := by linarith
  have hlog := Real.log_le_log (show 0 < 2 * (N : ℝ) ^ h + 2 by positivity) harg
  have he : Real.log (4 * (N : ℝ) ^ h) = 2 * Real.log 2 + (h : ℝ) * Real.log N := by
    rw [Real.log_mul (by norm_num) hp.ne', Real.log_pow]
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]
    norm_num
  rw [he] at hlog
  have hlog' : Real.log (2 * (N : ℝ) ^ h + 2) ≤ ((h : ℝ) + 2) * Real.log N := by nlinarith
  have hkb : K ≤ K / Real.log 2 * Real.log N := by
    have hh := mul_le_mul_of_nonneg_left hl (div_nonneg hK hl2.le)
    rwa [div_mul_cancel₀ K hl2.ne'] at hh
  have hh := mul_le_mul_of_nonneg_left hlog' hC
  nlinarith

lemma coarse_choice_bound (V V₀ : ℝ) (hV₀ : 0 ≤ V₀) (N L : ℕ)
    (hL : L ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hV : V ≤ V₀ * Real.log N) :
    2 * Real.sqrt (2 * (L : ℝ) * V) ≤
      (2 * Real.sqrt (2 * V₀)) * Real.sqrt N * Real.log N := by
  have hl : 0 ≤ Real.log (N : ℝ) := by linarith
  have hL' : (L : ℝ) ≤ N := by exact_mod_cast hL
  have hmul : 2 * (L : ℝ) * V ≤ 2 * (N : ℝ) * (V₀ * Real.log N) := by
    calc
      _ ≤ 2 * (L : ℝ) * (V₀ * Real.log N) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hV₀ hl)
  have hslog : Real.sqrt (Real.log N) ≤ Real.log N := Real.sqrt_le_iff.mpr ⟨hl, by nlinarith⟩
  have he : Real.sqrt (2 * (N : ℝ) * (V₀ * Real.log N)) =
      Real.sqrt (2 * V₀) * Real.sqrt N * Real.sqrt (Real.log N) := by
    have hh : 2 * (N : ℝ) * (V₀ * Real.log N) = (2 * V₀) * ((N : ℝ) * Real.log N) := by ring
    rw [hh, Real.sqrt_mul (by positivity), Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) N)]
    ring
  calc
    _ ≤ 2 * Real.sqrt (2 * (N : ℝ) * (V₀ * Real.log N)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmul) (by norm_num)
    _ = (2 * Real.sqrt (2 * V₀)) * Real.sqrt N * Real.sqrt (Real.log N) := by rw [he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hslog (by positivity)

/-- Uniformly over all sets with a prescribed logarithmic upper bound, a
sufficiently large target can be increased by any even O(log n) amount.
Every other representation count increases by at most epsilon*log(z+2). -/
theorem eventually_global_repair (D ε K C : ℝ) (hD : 0 ≤ D) (hε : 0 < ε)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Set ℕ,
      (∀ z : ℕ, (sumRep A z : ℝ) ≤ K + C * Real.log ((z : ℝ) + 2)) →
      ∀ m : ℕ, (m : ℝ) ≤ D * Real.log n →
      ∃ F : Finset ℕ, F.card = 2 * m ∧ Disjoint A (F : Set ℕ) ∧
        (∀ a ∈ F, n ≤ 4 * a ∧ a ≤ n) ∧
        sumRep (A ∪ (F : Set ℕ)) n = sumRep A n + 2 * m ∧
        ∀ z : ℕ, z ≠ n →
          0 ≤ (sumRep (A ∪ (F : Set ℕ)) z : ℝ) - sumRep A z ∧
          (sumRep (A ∪ (F : Set ℕ)) z : ℝ) - sumRep A z ≤ ε * Real.log ((z : ℝ) + 2) := by
  obtain ⟨h, hh⟩ := exists_nat_gt (max (1 : ℝ) (4 * D / ε))
  have hh1 : 1 ≤ h := by
    have hh' : (1 : ℝ) < h := lt_of_le_of_lt (le_max_left _ _) hh
    exact_mod_cast hh'.le
  have hhD : 4 * D ≤ ε * h := by
    have hh' := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hh)
    nlinarith
  let V₀ : ℝ := K / Real.log 2 + C * ((h : ℝ) + 2)
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hV₀ : 0 ≤ V₀ := by dsimp [V₀]; positivity
  let B : ℝ := 2 * Real.sqrt (2 * V₀)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let t : ℝ := 32 * ((h : ℝ) + 1) / ε
  obtain ⟨ht, hparams⟩ := eventually_selection_small D B ε hD hB hε h
  have hloglim : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hloglim.eventually_ge_atTop (max 1 (24 / ε))
  filter_upwards [eventually_ge_atTop 48, hlarge, hparams] with n hn hlog hparam
  intro A hA m hm
  have hn2 : 2 ≤ n := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog1 : 1 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlog
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hεlog : 24 ≤ ε * Real.log n := by
    have hh' := (le_max_right 1 (24 / ε)).trans hlog
    have hh'' := (div_le_iff₀ hε).mp hh'
    nlinarith
  let L : ℕ := n / 12
  let X : ℕ := n ^ h
  let A₀ := intCutoff A X
  let x : Fin L → ℤ := fun i ↦ (n / 3 : ℕ) + (i.val : ℤ)
  let V : ℝ := K + C * Real.log (2 * (X : ℝ) + 2)
  let W : ℝ := B * Real.sqrt n * Real.log n
  let R : ℝ := ε * Real.log n / 16
  let T : Finset ℤ := Finset.Icc 0 (X : ℤ)
  have hLpos : 0 < L := by dsimp [L]; omega
  letI : NeZero L := ⟨by omega⟩
  have hLn : L ≤ n := Nat.div_le_self _ _
  have hL24 : (n : ℝ) / 24 ≤ L := by
    have hh' : n ≤ 24 * L := by dsimp [L]; omega
    have hh'' : (n : ℝ) ≤ 24 * L := by exact_mod_cast hh'
    linarith
  have hnX : n ≤ X := Nat.le_pow (by omega)
  have hxinj : Function.Injective x := by
    intro i j he
    apply Fin.ext
    dsimp [x] at he
    exact_mod_cast add_left_cancel he
  have hxhalf : ∀ i : Fin L, 2 * x i < (n : ℤ) := by
    intro i
    have hi := i.isLt
    have hh' : 2 * (n / 3 + i.val) < n := by dsimp [L] at hi; omega
    dsimp only [x]
    exact_mod_cast hh'
  have hxlow : ∀ i : Fin L, 0 ≤ x i ∧ (n : ℤ) ≤ 4 * x i := by
    intro i
    dsimp [x]
    have hh' : n ≤ 4 * (n / 3 + i.val) := by omega
    exact ⟨by positivity, by exact_mod_cast hh'⟩
  have hA₀ : ∀ z : ℤ, (pairCount A₀ A₀ z : ℝ) ≤ V :=
    intCutoff_uniform_bound hK hC hA X
  have hVbound : V ≤ V₀ * Real.log n := by
    dsimp [V, V₀, X]
    push_cast
    exact polynomial_cutoff_log_bound K C hK hC h n hn2
  have hchoice := interval_choice_bounds A₀ V hA₀ (n : ℤ) (n / 3 : ℕ) L
  have hcoarse : 2 * Real.sqrt (2 * (L : ℝ) * V) ≤ W :=
    coarse_choice_bound V V₀ hV₀ n L hLn hlog1 hVbound
  have hforbid : (forbidden A₀ (n : ℤ) x).card ≤ W := hchoice.1.trans hcoarse
  have htests : ∀ z ∈ T, (hitChoices A₀ (n : ℤ) x z).card ≤ W :=
    fun z _ ↦ (hchoice.2 z).trans hcoarse
  have hTcard : (T.card : ℝ) = (n : ℝ) ^ h + 1 := by
    have he : T.card = X + 1 := by
      dsimp [T]
      rw [Int.card_Icc]
      omega
    rw [he]
    simp [X]
  have hsmall : ((m : ℝ) ^ 4 + m * W) / Fintype.card (Fin L) +
      T.card * Real.exp ((m : ℝ) * Real.exp t * W / Fintype.card (Fin L) - t * R) < 1 := by
    rw [Fintype.card_fin, hTcard]
    exact hparam L m hL24 hm
  obtain ⟨Q, hQcard, hdis, hsub, hsym, hcenter, hself, hcoll⟩ :=
    exists_finite_repair A₀ (n : ℤ) x hxinj hxhalf m T W W R t hforbid htests ht hsmall
  have hQbounds : ∀ a ∈ Q, 0 ≤ a ∧ (n : ℤ) ≤ 4 * a ∧ a ≤ n := by
    intro a ha
    rcases Finset.mem_union.mp (hsub ha) with ha | ha
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      have hh' := hxhalf i
      have hh'' := hxlow i
      omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      have hh' := hxhalf i
      have hh'' := hxlow i
      omega
  let F := Q.image Int.toNat
  have hFcard : F.card = 2 * m := by
    rw [toNat_image_card Q (fun a ha ↦ (hQbounds a ha).1), hQcard]
  have hFsupport : ∀ a ∈ F, n ≤ 4 * a ∧ a ≤ n := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hh' := hQbounds b hb
    have he := Int.toNat_of_nonneg hh'.1
    constructor <;> omega
  have hFdis : Disjoint A (F : Set ℕ) :=
    disjoint_of_cutoff_disjoint A X Q (fun a ha ↦
      ⟨(hQbounds a ha).1, (hQbounds a ha).2.2.trans (by exact_mod_cast hnX)⟩) hdis
  have htransfer (z : ℕ) (hz : z ≤ X) :
      sumRep (A ∪ (F : Set ℕ)) z = pairCount (A₀ ∪ Q) (A₀ ∪ Q) (z : ℤ) :=
    cutoff_union_rep A X z Q (fun a ha ↦ (hQbounds a ha).1) hz
  have hbase (z : ℕ) (hz : z ≤ X) : pairCount A₀ A₀ (z : ℤ) = sumRep A z := cutoff_rep_eq A X z hz
  refine ⟨F, hFcard, hFdis, hFsupport, ?_, ?_⟩
  · rw [htransfer n hnX, hcenter, hbase n hnX]
  · intro z hzn
    have hmono : (sumRep A z : ℝ) ≤ sumRep (A ∪ (F : Set ℕ)) z := by
      exact_mod_cast sumRep_mono (Set.subset_union_left : A ⊆ A ∪ (F : Set ℕ)) z
    refine ⟨by linarith, ?_⟩
    by_cases hsmallz : 4 * z < n
    · have he := union_rep_unchanged_below A F z (fun a ha ↦ by have := (hFsupport a ha).1; omega)
      rw [he, sub_self]
      exact mul_nonneg hε.le (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith))
    by_cases hzX : z ≤ X
    · have hzT : (z : ℤ) ∈ T := Finset.mem_Icc.mpr ⟨by positivity, by exact_mod_cast hzX⟩
      have hh' := hcoll (z : ℤ) hzT (by exact_mod_cast hzn)
      rw [← htransfer z hzX, hbase z hzX] at hh'
      have hz4 : (4 : ℝ) ≤ (z : ℝ) + 2 := by
        have hzN : n ≤ 4 * z := by omega
        exact_mod_cast (show 4 ≤ z + 2 by omega)
      have harg : (n : ℝ) ≤ 4 * ((z : ℝ) + 2) := by exact_mod_cast (show n ≤ 4 * (z + 2) by omega)
      have hl₁ := Real.log_le_log hnp harg
      rw [Real.log_mul (by norm_num) (by positivity : (z : ℝ) + 2 ≠ 0)] at hl₁
      have hl₂ := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hz4
      have hlogcomp : Real.log n ≤ 2 * Real.log ((z : ℝ) + 2) := by linarith
      dsimp [R] at hh'
      nlinarith [mul_le_mul_of_nonneg_left hlogcomp hε.le]
    · have hh' := sumRep_union_finset_le A F z
      rw [hFcard] at hh'
      have hcount : (sumRep (A ∪ (F : Set ℕ)) z : ℝ) - sumRep A z ≤ 4 * m := by
        have hhR : (sumRep (A ∪ (F : Set ℕ)) z : ℝ) ≤ sumRep A z + 4 * m := by
          exact_mod_cast (show sumRep (A ∪ (F : Set ℕ)) z ≤ sumRep A z + 4 * m by omega)
        linarith
      have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
      have hlogX : Real.log (X : ℝ) = (h : ℝ) * Real.log n := by dsimp [X]; rw [Nat.cast_pow, Real.log_pow]
      have hlogle := Real.log_le_log hXpos (show (X : ℝ) ≤ (z : ℝ) + 2 by exact_mod_cast (show X ≤ z + 2 by omega))
      rw [hlogX] at hlogle
      have h₁ := mul_le_mul_of_nonneg_right hhD hlog0
      have h₂ := mul_le_mul_of_nonneg_left hlogle hε.le
      nlinarith

end Erdos66GlobalRepair
