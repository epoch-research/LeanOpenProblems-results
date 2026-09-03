import FormalConjecturesUtil
import Submission.Model126
import Submission.Energy126
import Submission.Pruning126
import Submission.Spherical126
import Submission.Packing126

/-! Polynomial capacity of signed laminar families satisfying the two global inequalities. -/

open scoped BigOperators

namespace E126

noncomputable section

variable {ι κ : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ]

namespace Capacity126

/-- On a set where all kernels are approximately flat, the sign vectors form
an almost-obtuse code. The diameter bound supplies the missing baseline mass. -/
theorem flat_independent_bound (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W))
    (a b : ι) (L : ℝ) (hLab : totalOpposition W a b = L) (hL : 0 < L)
    (β : κ → ℝ) (hβ : ∀ p, 0 ≤ β p) (e : ℝ) (he : 0 ≤ e)
    (hsmall : 16 * (Fintype.card κ : ℝ) ^ 2 * e ≤ L)
    (T : Finset ι)
    (hF : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → totalOpposition W i j ≤ (∑ p, β p) + e)
    (hR : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Spherical126.gram β (fun p => (W p).signVal) i j ≤ e) :
    T.card ≤ 4 * Fintype.card κ := by
  by_cases hc : T.card ≤ 2 * Fintype.card κ
  · omega
  have hc' : 2 * Fintype.card κ < T.card := by omega
  have hB : 0 ≤ ∑ p, β p := Finset.sum_nonneg (fun p _ => hβ p)
  have hd := totalOpposition_diameter_bound_of_offDiag W hV hCND T ((∑ p, β p) + e)
    (add_nonneg hB he) hF hc' a b
  rw [hLab] at hd
  have hsN : 0 < Fintype.card κ := by
    by_contra h
    have hz : Fintype.card κ = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero, zero_mul] at hd
    linarith
  have hs : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hsN
  have hs0 : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hsN
  have haux : 4 * (Fintype.card κ : ℝ) * e ≤ (∑ p, β p) + e := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * (Fintype.card κ : ℝ) by positivity)).mp
    nlinarith only [hsmall, hd]
  have hse : e ≤ (Fintype.card κ : ℝ) * e := by nlinarith only [mul_le_mul_of_nonneg_right hs he]
  have hBpos : 0 < ∑ p, β p := by
    by_contra h
    have hBn : (∑ p, β p) ≤ 0 := le_of_not_gt h
    have he0 : e = 0 := by nlinarith only [haux, hse, he, hBn]
    have hmul : 4 * (Fintype.card κ : ℝ) * (∑ p, β p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hBn
    rw [he0, add_zero] at hd
    linarith
  have heB : 2 * (Fintype.card κ : ℝ) * e ≤ ∑ p, β p := by
    nlinarith only [haux, hse, he]
  apply Spherical126.card_finset_le_four_mul T β (fun p => (W p).signVal) hβ
    (fun p i _ => (W p).signVal_sq i) hBpos
  intro i hi j hj hij
  exact (mul_le_mul_of_nonneg_left (hR i hi j hj hij) (by positivity)).trans heB

/-- Approximation of an unsigned entry also approximates its signed entry. -/
theorem signed_approx (W : OppositionFamily ι) (i j : ι) (β r : ℝ)
    (hlo : β ≤ W.unsigned i j) (hhi : W.unsigned i j ≤ β + r) :
    W.signed i j ≤ β * W.signVal i * W.signVal j + r ∧
      β * W.signVal i * W.signVal j ≤ W.signed i j + r := by
  cases hi : W.sign i <;> cases hj : W.sign j <;>
    simp [OppositionFamily.signed, OppositionFamily.signVal, hi, hj] <;> constructor <;> linarith

/-- The numerical budget used in the pruning step. -/
theorem error_budget (s : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    16 * (s : ℝ) ^ 2 * ((s : ℝ) * (2 * (2 * (s : ℝ) * L) /
      ((64 * (s + 1) ^ 4 : ℕ) : ℝ))) ≤ L := by
  have ht : (0 : ℝ) < ((64 * (s + 1) ^ 4 : ℕ) : ℝ) := by positivity
  have hp : (s : ℝ) ^ 4 ≤ ((s : ℝ) + 1) ^ 4 := by gcongr <;> norm_num
  have hh : 64 * (s : ℝ) ^ 4 * L ≤ ((64 * (s + 1) ^ 4 : ℕ) : ℝ) * L := by
    push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hL
  calc
    _ = (64 * (s : ℝ) ^ 4 * L) / ((64 * (s + 1) ^ 4 : ℕ) : ℝ) := by ring
    _ ≤ L := (div_le_iff₀ ht).mpr (by nlinarith only [hh])

/-- A generous integer bound, chosen to keep the eventual limit transfer simple. -/
theorem count_budget (s n : ℕ)
    (h : n ≤ s * (64 * (s + 1) ^ 4) +
      (4 * s) * (s * (64 * (s + 1) ^ 4) + 1)) :
    n ≤ 1024 * (s + 1) ^ 8 := by
  have hw : 1 ≤ s + 1 := by omega
  have hp : (s + 1) ^ 6 ≤ (s + 1) ^ 8 := Nat.pow_le_pow_right hw (by decide)
  have hpow : s + 1 ≤ (s + 1) ^ 6 := by
    calc
      s + 1 = (s + 1) ^ 1 := by simp
      _ ≤ (s + 1) ^ 6 := Nat.pow_le_pow_right hw (by decide)
  have hs1 : s ≤ (s + 1) ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have h1 : s * (64 * (s + 1) ^ 4) ≤ 64 * (s + 1) ^ 6 := by
    calc
      _ ≤ (s + 1) ^ 2 * (64 * (s + 1) ^ 4) := Nat.mul_le_mul_right _ hs1
      _ = _ := by ring
  have h2 : (4 * s) * (s * (64 * (s + 1) ^ 4) + 1) ≤
      256 * (s + 1) ^ 6 + 4 * (s + 1) := by
    calc
      _ = s ^ 2 * (256 * (s + 1) ^ 4) + 4 * s := by ring
      _ ≤ (s + 1) ^ 2 * (256 * (s + 1) ^ 4) + 4 * (s + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hs2) (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  omega

end Capacity126

/-- Polynomial capacity for all finite opposition-tree families. -/
theorem opposition_capacity (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) :
    Fintype.card ι ≤ 1024 * (Fintype.card κ + 1) ^ 8 := by
  classical
  let s := Fintype.card κ
  let t := 64 * (s + 1) ^ 4
  have ht : 2 ≤ t := by dsimp [t]; nlinarith [Nat.one_le_pow 4 (s + 1) (by omega)]
  by_cases hn : Fintype.card ι ≤ 2 * t
  · have hw : 1 ≤ s + 1 := by omega
    have hp : (s + 1) ^ 4 ≤ (s + 1) ^ 8 := Nat.pow_le_pow_right hw (by decide)
    dsimp [t] at hn
    change Fintype.card ι ≤ 1024 * (s + 1) ^ 8
    nlinarith
  have hnt : 2 * t < Fintype.card ι := by omega
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty ι := hι
  obtain ⟨ab, _, hab⟩ := (Finset.univ : Finset (ι × ι)).exists_max_image
    (fun x => totalOpposition W x.1 x.2) Finset.univ_nonempty
  let L := totalOpposition W ab.1 ab.2
  have hmax : ∀ i j, totalOpposition W i j ≤ L := fun i j => hab (i, j) (Finset.mem_univ _)
  have hL : 0 < L := by
    have htwo : 1 < Fintype.card ι := by omega
    obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp htwo
    have hU : 0 ≤ totalUnsigned W i j :=
      Finset.sum_nonneg (fun p _ => (W p).unsigned_nonneg i j)
    have heq := totalOpposition_eq W i j
    have hv := hV i j hij
    have hb := hmax i j
    linarith
  let M : ℝ := 2 * (s : ℝ) * L
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpr (p : κ) := (W p).toLaminarFamily.pruning hM
    (fun q hq => unsigned_energy_bound W hV hCND L hmax p q hq) t ht hnt
  choose Z β bad hZ hβ hbad hsym happ using hpr
  let Zall : Finset ι := Finset.univ.biUnion Z
  let badall : ι → Finset ι := fun i => Finset.univ.biUnion (fun p => bad p i)
  let Y : Finset ι := Finset.univ \ Zall
  have hZall : Zall.card ≤ s * t := by
    calc
      _ ≤ ∑ p : κ, (Z p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : κ, t := Finset.sum_le_sum (fun p _ => hZ p)
      _ = _ := by simp [s]
  have hbadall : ∀ i, (badall i).card ≤ s * t := by
    intro i
    calc
      _ ≤ ∑ p : κ, (bad p i).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : κ, t := Finset.sum_le_sum (fun p _ => hbad p i)
      _ = _ := by simp [s]
  have hsymall : ∀ i j, j ∈ badall i ↔ i ∈ badall j := by
    intro i j
    simp only [badall, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact exists_congr (fun p => hsym p i j)
  let r : ℝ := 2 * M / (t : ℝ)
  let e : ℝ := (s : ℝ) * r
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hsmall : 16 * (Fintype.card κ : ℝ) ^ 2 * e ≤ L :=
    Capacity126.error_budget s L hL.le
  have hind : ∀ T ⊆ Y, Packing126.Independent badall T → T.card ≤ 4 * s := by
    intro T hTY hTi
    have hlocal : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ p,
        β p ≤ (W p).unsigned i j ∧ (W p).unsigned i j ≤ β p + r := by
      intro i hi j hj hij p
      have hiz : i ∉ Zall := (Finset.mem_sdiff.mp (hTY hi)).2
      have hjz : j ∉ Zall := (Finset.mem_sdiff.mp (hTY hj)).2
      have hb : j ∉ badall i := hTi i hi j hj hij
      apply happ p i j hij
      · exact fun h => hiz (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, h⟩)
      · exact fun h => hjz (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, h⟩)
      · exact fun h => hb (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, h⟩)
    apply Capacity126.flat_independent_bound W hV hCND ab.1 ab.2 L rfl hL β hβ e he hsmall T
    · intro i hi j hj hij
      calc
        totalOpposition W i j ≤ ∑ p, (β p + r) := by
          apply Finset.sum_le_sum
          intro p hp
          have hu := (hlocal i hi j hj hij p).2
          have hβr := add_nonneg (hβ p) hr
          unfold OppositionFamily.opposition
          split <;> assumption
        _ = (∑ p, β p) + e := by simp [Finset.sum_add_distrib, e, s]
    · intro i hi j hj hij
      have hsum : Spherical126.gram β (fun p => (W p).signVal) i j ≤
          totalSigned W i j + e := by
        calc
          _ ≤ ∑ p, ((W p).signed i j + r) := by
            apply Finset.sum_le_sum
            intro p hp
            exact (Capacity126.signed_approx (W p) i j (β p) r
              (hlocal i hi j hj hij p).1 (hlocal i hi j hj hij p).2).2
          _ = _ := by simp [Finset.sum_add_distrib, totalSigned, e, s]
      exact hsum.trans (by linarith [hV i j hij])
  have hY : Y.card ≤ (4 * s) * (s * t + 1) :=
    Packing126.card_le Y badall hsymall (s * t) (4 * s) hbadall hind
  have hcard : Fintype.card ι = Y.card + Zall.card := by
    simpa [Y] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Zall)).symm
  apply Capacity126.count_budget s (Fintype.card ι)
  dsimp [t] at hY hZall
  omega

end
end E126
