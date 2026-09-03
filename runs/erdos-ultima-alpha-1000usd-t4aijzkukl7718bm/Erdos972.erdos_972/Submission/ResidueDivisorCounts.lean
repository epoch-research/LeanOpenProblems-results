import Submission.ResiduePrimeRows

/-! Uniform ordinary divisor counts with an arbitrary output residue. -/
namespace Erdos972ResidueDivisorCounts

open Finset
open Erdos972RationalRotationCount Erdos972ResiduePrimeRows
open Erdos972ReciprocalDivisorCounts Erdos972PrimePowerError

set_option maxHeartbeats 1500000

lemma rotationInterval_sub_card (θ : ℝ) (K : ℕ) {l u : ℝ} (hlu : l ≤ u) :
    (rotationInterval θ K 0 l).card+(rotationInterval θ K l u).card =
      (rotationInterval θ K 0 u).card := by
  classical
  have he : rotationInterval θ K 0 u =
      rotationInterval θ K 0 l ∪ rotationInterval θ K l u := by
    ext n
    simp only [rotationInterval, mem_filter, mem_range, mem_union,
      Int.fract_nonneg, true_and]
    constructor
    · rintro ⟨hn, hx⟩
      by_cases hh : Int.fract (θ*n) < l
      · exact Or.inl ⟨hn, hh⟩
      · exact Or.inr ⟨hn, le_of_not_gt hh, hx⟩
    · rintro (⟨hn, hx⟩ | ⟨hn, _, hx⟩)
      · exact ⟨hn, hx.trans_le hlu⟩
      · exact ⟨hn, hx⟩
  have hd : Disjoint (rotationInterval θ K 0 l) (rotationInterval θ K l u) := by
    apply disjoint_left.mpr
    intro n hn hn'
    exact (not_lt.mpr (mem_filter.mp hn').2.1) (mem_filter.mp hn).2.2
  rw [he, card_union_of_disjoint hd]

lemma rotationInterval_general_discrepancy {a q K : ℕ} (hq : 0 < q)
    (haq : a.Coprime q) {θ l u E : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1)
    (hE : 0 ≤ E) (hE1 : E ≤ 1) (happrox : |θ-(a : ℝ)/q| *K ≤ E) :
    |((rotationInterval θ K l u).card : ℝ)-(K : ℝ)*(u-l)| ≤
      4*K*E+2*K/(q : ℝ)+6*q+2 := by
  have h1 := rotationInterval_card_discrepancy hq haq hl (hlu.trans hu) hE hE1 happrox
  have h2 := rotationInterval_card_discrepancy hq haq (hl.trans hlu) hu hE hE1 happrox
  have he : ((rotationInterval θ K l u).card : ℝ)-(K : ℝ)*(u-l) =
      (((rotationInterval θ K 0 u).card : ℝ)-(K : ℝ)*u)-
        (((rotationInterval θ K 0 l).card : ℝ)-(K : ℝ)*l) := by
    have hh : ((rotationInterval θ K 0 l).card : ℝ)+(rotationInterval θ K l u).card =
        (rotationInterval θ K 0 u).card := by exact_mod_cast rotationInterval_sub_card θ K hlu
    linarith only [hh]
  rw [he]
  exact ((abs_sub _ _).trans (add_le_add h2 h1)).trans_eq (by ring)

noncomputable def residueDivisorRow (α : ℝ) (K d e j : ℕ) : Finset ℕ :=
  (range K).filter fun k => floorMul α (d*k)%e = j

noncomputable def residueDivisorPairs (α : ℝ) (N d e j : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => d ∣ n ∧ floorMul α n%e = j

lemma residueDivisorRow_eq_rotationInterval {α : ℝ} (hα : 0 ≤ α)
    (K d e j : ℕ) (he : 0 < e) :
    residueDivisorRow α K d e j = rotationInterval (α*d/e) K ((j : ℝ)/e) (((j : ℝ)+1)/e) := by
  ext k
  simp only [residueDivisorRow, rotationInterval, mem_filter, floorMul, Nat.cast_mul]
  rw [floor_mod_eq_iff_arc (by positivity : 0 ≤ α*((d : ℝ)*k)) he j]
  rw [show α*((d : ℝ)*k)/e = (α*d/e)*k by ring]

lemma residueDivisorRow_discrepancy {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (K d e j : ℕ) (hd : 0 < d) (he : 0 < e) (hj : j < e)
    (hsmall : |α-r| *((d : ℝ)/e)*K ≤ 1) :
    |((residueDivisorRow α K d e j).card : ℝ)-(K : ℝ)/e| ≤
      4*K*(|α-r| *((d : ℝ)/e)*K)+2*((K*d : ℝ)/r.den)+6*e*r.den+2 := by
  let s : ℚ := r*d/e
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hqR : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hsR : (0 : ℝ) < s.den := Nat.cast_pos.mpr s.pos
  have hjR : (j : ℝ)+1 ≤ e := by exact_mod_cast hj
  have herr : |α*d/e-(s.num.natAbs : ℝ)/s.den| *K = |α-r| *((d : ℝ)/e)*K := by
    rw [← nonneg_rat_cast_eq_natAbs_div s hs]
    simp only [s, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    rw [← sub_div, ← sub_mul, abs_div, abs_mul, abs_of_pos hdR, abs_of_pos heR]
    ring
  have hh := rotationInterval_general_discrepancy s.pos s.reduced
    (l := (j : ℝ)/e) (u := ((j : ℝ)+1)/e) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) heR.le) ((div_le_one heR).mpr hjR)
    (by positivity) hsmall herr.le
  rw [← residueDivisorRow_eq_rotationInterval hα K d e j he,
    show (K : ℝ)*(((j : ℝ)+1)/e-(j : ℝ)/e) = (K : ℝ)/e by ring] at hh
  have hlo : (r.den : ℝ) ≤ d*s.den := by exact_mod_cast den_le_mul_div_nat_den r d e hd he
  have hhi : (s.den : ℝ) ≤ r.den*e := by exact_mod_cast den_mul_div_nat_le r d e he
  have hdiv : (K : ℝ)/s.den ≤ (K*d : ℝ)/r.den := by
    apply (div_le_div_iff₀ hsR hqR).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α := ℝ) K)]
  rw [mul_div_assoc 2 (K : ℝ) (s.den : ℝ)] at hh
  nlinarith only [hh, hdiv, hhi]

lemma residueDivisorPairs_card (α : ℝ) (N d e j : ℕ) (hd : 0 < d) :
    (residueDivisorPairs α N d e j).card = ((residueDivisorRow α (N/d+1) d e j).erase 0).card := by
  classical
  let T := (Ioc 0 (N/d)).filter fun k => floorMul α (d*k)%e = j
  have he : T = (residueDivisorRow α (N/d+1) d e j).erase 0 := by
    ext k
    simp only [T, residueDivisorRow, mem_filter, mem_Ioc, mem_erase, mem_range]
    omega
  rw [← he]
  apply card_bij' (fun n _ => n/d) (fun k _ => d*k)
  · intro n hn
    obtain ⟨hnI, hdn, hen⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hnI
    have heq := Nat.mul_div_cancel' hdn
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hnN⟩, ?_⟩
    · apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, mul_zero] at heq
      exact (Nat.ne_of_gt hn0) heq.symm
    · simpa only [heq] using hen
  · intro k hk
    obtain ⟨hkI, hek⟩ := mem_filter.mp hk
    obtain ⟨hk0, hkN⟩ := mem_Ioc.mp hkI
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨Nat.mul_pos hd hk0, ?_⟩, dvd_mul_right d k, hek⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkN
  · intro n hn
    exact Nat.mul_div_cancel' (mem_filter.mp hn).2.1
  · intro k _
    exact Nat.mul_div_cancel_left k hd

lemma residueDivisorPairs_discrepancy_exact {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (N d e j : ℕ) (hd : 0 < d) (he : 0 < e) (hj : j < e)
    (hsmall : |α-r| *((d : ℝ)/e)*(N/d+1 : ℕ) ≤ 1) :
    |((residueDivisorPairs α N d e j).card : ℝ)-(N : ℝ)/(d*e)| ≤
      4*(N/d+1 : ℕ)*(|α-r| *((d : ℝ)/e)*(N/d+1 : ℕ))+
        2*(((N/d+1 : ℕ)*d : ℝ)/r.den)+6*e*r.den+4 := by
  classical
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hh := residueDivisorRow_discrepancy hα r hr (N/d+1) d e j hd he hj hsmall
  have hc : |((residueDivisorPairs α N d e j).card : ℝ)-
      (residueDivisorRow α (N/d+1) d e j).card| ≤ 1 := by
    rw [residueDivisorPairs_card α N d e j hd]
    by_cases hz : 0 ∈ residueDivisorRow α (N/d+1) d e j
    · have he' : (((residueDivisorRow α (N/d+1) d e j).erase 0).card : ℝ)+1 =
          (residueDivisorRow α (N/d+1) d e j).card := by exact_mod_cast card_erase_add_one hz
      rw [show (((residueDivisorRow α (N/d+1) d e j).erase 0).card : ℝ)-
        (residueDivisorRow α (N/d+1) d e j).card = -1 by linarith only [he']]
      norm_num
    · rw [erase_eq_of_notMem hz, sub_self, abs_zero]; norm_num
  have hoff : |((N/d+1 : ℕ) : ℝ)/e-(N : ℝ)/(d*e)| ≤ 1 := by
    have hlo : (N : ℝ) < d*((N/d+1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_mul_div_succ N hd
    have hhi : ((N/d+1 : ℕ) : ℝ) ≤ (N : ℝ)/d+1 := by
      have h := (Nat.cast_div_le : ((N/d : ℕ) : ℝ) ≤ (N : ℝ)/d)
      push_cast; linarith only [h]
    have hl : (N : ℝ)/(d*e) ≤ ((N/d+1 : ℕ) : ℝ)/e := by
      apply (div_le_div_iff₀ (mul_pos hdR heR) heR).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hlo.le heR.le]
    have hu : ((N/d+1 : ℕ) : ℝ)/e ≤ (N : ℝ)/(d*e)+1 := by
      have h := (div_le_div_of_nonneg_right hhi heR.le).trans
        (show ((N : ℝ)/d+1)/e ≤ (N : ℝ)/(d*e)+1 by
          rw [add_div, ← div_mul_eq_div_div]
          linarith only [(div_le_one heR).mpr he1])
      exact h
    rw [abs_of_nonneg (sub_nonneg.mpr hl)]
    linarith only [hu]
  have ht := abs_sub_le ((residueDivisorPairs α N d e j).card : ℝ)
    ((residueDivisorRow α (N/d+1) d e j).card : ℝ) (((N/d+1 : ℕ) : ℝ)/e)
  have ht' := abs_sub_le ((residueDivisorPairs α N d e j).card : ℝ)
    (((N/d+1 : ℕ) : ℝ)/e) ((N : ℝ)/(d*e))
  linarith only [ht, ht', hc, hh, hoff]

theorem residueDivisorPairs_discrepancy {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (N d e j : ℕ) (hd : 0 < d) (hdN : d ≤ N) (he : 0 < e) (hj : j < e)
    (hsmall : 2 * N * |α - r| ≤ 1) :
    |((residueDivisorPairs α N d e j).card : ℝ) - (N : ℝ) / (d * e)| ≤
      16 * (N : ℝ)^2 * |α - r| + 4 * N / (r.den : ℝ) + 6 * e * r.den + 4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hde : (0 : ℝ) < e := by positivity
  have hdN' : (d : ℝ) ≤ N := Nat.cast_le.mpr hdN
  have hK0 : (0 : ℝ) ≤ (N / d + 1 : ℕ) := Nat.cast_nonneg _
  have hKd : ((N / d + 1 : ℕ) : ℝ) * d ≤ 2 * N := by
    have hh : (N / d + 1) * d ≤ N + d := by
      have h := Nat.div_mul_le_self N d
      nlinarith
    have hhR : ((N / d + 1 : ℕ) : ℝ) * d ≤ N + d := by exact_mod_cast hh
    linarith
  have hK : ((N / d + 1 : ℕ) : ℝ) ≤ 2 * N := by nlinarith
  have hE : |α - r| * ((d : ℝ) / e) * (N / d + 1 : ℕ) ≤ 2 * N * |α - r| := by
    calc
      _ = (|α - r| * (((N / d + 1 : ℕ) : ℝ) * d)) / e := by ring
      _ ≤ (|α - r| * (2 * N)) / e := by gcongr
      _ ≤ |α - r| * (2 * N) := div_le_self (by positivity) heR
      _ = _ := by ring
  have hc := residueDivisorPairs_discrepancy_exact hα r hr N d e j hd he hj (hE.trans hsmall)
  apply hc.trans
  have hprod : 2 * (N / d + 1 : ℕ) *
      (|α - r| * ((d : ℝ) / e) * (N / d + 1 : ℕ)) ≤ 8 * (N : ℝ)^2 * |α - r| := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ) ≤ 2))
      hE (by positivity) (by positivity)
    convert hh using 1
    ring
  have hdiv : ((N / d + 1 : ℕ) * d : ℝ) / r.den ≤ 2 * N / (r.den : ℝ) := by
    exact div_le_div_of_nonneg_right hKd (Nat.cast_nonneg r.den)
  rw [mul_div_assoc 4 (N : ℝ) (r.den : ℝ)]
  rw [mul_div_assoc 2 (N : ℝ) (r.den : ℝ)] at hdiv
  nlinarith only [hc, hprod, hdiv]

theorem reciprocal_scale_residue_bound {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) {u v X d e j : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hαu : 4*α ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (hX : α*X ≤ (u : ℝ)^6) (hd : 0 < d) (hdX : d ≤ X) (he : 0 < e) (hev : e ≤ v) (hj : j < e) :
    |((residueDivisorPairs α X d e j).card : ℝ)-(X : ℝ)/(d*e)| ≤ 236*(v : ℝ)*(u : ℝ)^4 := by
  have hα0 : 0 < α := by linarith
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hq0 : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hloR : (u : ℝ)^4 ≤ r.den := by exact_mod_cast hlo
  have hhiR : (r.den : ℝ) ≤ 16*(u : ℝ)^4 := by exact_mod_cast hhi
  have hu4 : (u : ℝ) ≤ (u : ℝ)^4 := by exact_mod_cast Nat.le_self_pow (by norm_num : 4 ≠ 0) u
  have hq : 2*α ≤ r.den := by linarith only [hαu, hu4, hloR, hα0]
  obtain ⟨hs, hslo, hshi, herror⟩ := inverse_approximant_bounds hα r hr hq
  have hs0 : (0 : ℝ) < (r⁻¹).den := Nat.cast_pos.mpr (r⁻¹).pos
  have hdenmul : (r.den : ℝ) ≤ 2*α*(r⁻¹).den := by
    have hh := (div_le_iff₀ (show 0 < 2*α by positivity)).mp hslo
    nlinarith only [hh]
  have herr : |α-(r⁻¹ : ℚ)| *(r.den : ℝ)^2 ≤ 2*α^2 :=
    (le_div_iff₀ (sq_pos_of_pos hq0)).mp herror
  have hu8 : (u : ℝ)^8 ≤ (r.den : ℝ)^2 := by
    convert pow_le_pow_left₀ (by positivity) hloR 2 using 1 <;> ring
  have hsmall : 2*(X : ℝ)*|α-(r⁻¹ : ℚ)| ≤ 1 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hq0)).mp
    calc
      _ = 2*(X : ℝ)*(|α-(r⁻¹ : ℚ)| *(r.den : ℝ)^2) := by ring
      _ ≤ 2*(X : ℝ)*(2*α^2) := mul_le_mul_of_nonneg_left herr (by positivity)
      _ = (4*α)*(α*X) := by ring
      _ ≤ (u : ℝ)*(u : ℝ)^6 := mul_le_mul hαu hX (by positivity) (by positivity)
      _ = (u : ℝ)^7 := by ring
      _ ≤ (u : ℝ)^8 := pow_le_pow_right₀ huR (by norm_num)
      _ ≤ (r.den : ℝ)^2 := hu8
      _ = _ := by ring
  have hh := residueDivisorPairs_discrepancy hα0.le r⁻¹ hs.le X d e j hd hdX he hj hsmall
  have hfirst : 8*(X : ℝ)^2*|α-(r⁻¹ : ℚ)| ≤ 16*(u : ℝ)^4 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hq0)).mp
    calc
      _ = 8*(X : ℝ)^2*(|α-(r⁻¹ : ℚ)| *(r.den : ℝ)^2) := by ring
      _ ≤ 8*(X : ℝ)^2*(2*α^2) := mul_le_mul_of_nonneg_left herr (by positivity)
      _ = 16*(α*X)^2 := by ring
      _ ≤ 16*((u : ℝ)^6)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hX 2) (by norm_num)
      _ = 16*(u : ℝ)^4*(u : ℝ)^8 := by ring
      _ ≤ 16*(u : ℝ)^4*(r.den : ℝ)^2 := mul_le_mul_of_nonneg_left hu8 (by positivity)
      _ = _ := by ring
  have hsecond : 2*(X : ℝ)/((r⁻¹).den : ℝ) ≤ 4*(u : ℝ)^2 := by
    apply (div_le_iff₀ hs0).mpr
    apply (mul_le_mul_iff_left₀ hα0).mp
    calc
      _ = 2*(α*X) := by ring
      _ ≤ 2*(u : ℝ)^6 := mul_le_mul_of_nonneg_left hX (by norm_num)
      _ = 2*(u : ℝ)^2*(u : ℝ)^4 := by ring
      _ ≤ 2*(u : ℝ)^2*r.den := mul_le_mul_of_nonneg_left hloR (by positivity)
      _ ≤ 2*(u : ℝ)^2*(2*α*(r⁻¹).den) := mul_le_mul_of_nonneg_left hdenmul (by positivity)
      _ = _ := by ring
  have hthird : 3*(e : ℝ)*(r⁻¹).den ≤ 96*(v : ℝ)*(u : ℝ)^4 := by
    calc
      _ ≤ 3*(v : ℝ)*(2*r.den) := mul_le_mul (by exact_mod_cast Nat.mul_le_mul_left 3 hev) hshi (by positivity) (by positivity)
      _ ≤ 3*(v : ℝ)*(2*(16*(u : ℝ)^4)) := by gcongr
      _ = _ := by ring
  have hu24 : (u : ℝ)^2 ≤ (u : ℝ)^4 := pow_le_pow_right₀ huR (by norm_num)
  have hu14 : (1 : ℝ) ≤ (u : ℝ)^4 := one_le_pow₀ huR
  have hv4 := mul_le_mul_of_nonneg_right hvR (pow_nonneg hu0.le 4)
  rw [mul_div_assoc 4 (X : ℝ) ((r⁻¹).den : ℝ)] at hh
  rw [mul_div_assoc 2 (X : ℝ) ((r⁻¹).den : ℝ)] at hsecond
  nlinarith only [hh, hfirst, hsecond, hthird, hu24, hu14, hv4]

lemma residueDivisorPairs_empty_of_lt {α : ℝ} {X d e j : ℕ} (hdX : X < d) : residueDivisorPairs α X d e j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hnI, hdn, hen⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn0, hnX⟩ := Finset.mem_Ioc.mp hnI
  exact (not_le.mpr hdX) ((Nat.le_of_dvd hn0 hdn).trans hnX)

/-- The same bound also covers prefixes shorter than the input divisor. -/
theorem reciprocal_scale_residue_prefix_bound {α : ℝ} (hα : 1 ≤ α) (r : ℚ)
    (hr : |1/α-r| ≤ 1/(r.den : ℝ)^2) {u v X d e j : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hαu : 4*α ≤ u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (hX : α*X ≤ (u : ℝ)^6) (hd : 0 < d) (he : 0 < e) (hev : e ≤ v) (hj : j < e) :
    |((residueDivisorPairs α X d e j).card : ℝ)-(X : ℝ)/(d*e)| ≤ 236*(v : ℝ)*(u : ℝ)^4 := by
  by_cases hdX : d ≤ X
  · exact reciprocal_scale_residue_bound hα r hr hu hv hαu hlo hhi hX hd hdX he hev hj
  · have hXd : X < d := Nat.lt_of_not_ge hdX
    rw [residueDivisorPairs_empty_of_lt hXd, card_empty, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ (X : ℝ)/(d*e))]
    have hbound : (X : ℝ)/(d*e) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
      have hXdR : (X : ℝ) ≤ d := Nat.cast_le.mpr hXd.le
      nlinarith only [hXdR, heR, Nat.cast_nonneg (α := ℝ) d]
    have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
    have hh := mul_le_mul hvR (one_le_pow₀ huR (n := 4)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    nlinarith only [hbound, hh]


#print axioms reciprocal_scale_residue_prefix_bound
end Erdos972ResidueDivisorCounts
