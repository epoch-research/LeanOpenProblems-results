import FormalConjecturesUtil
import Submission.UpToRateRegularization

/-! Consequences of an exact power asymptotic retaining its leading constant. -/
open Filter SimpleGraph Asymptotics Finset

namespace Erdos713SharpDegree
open scoped Topology

lemma rpow_increment_lower {x r : ℝ} (hx : 1 ≤ x) (hr : 1 ≤ r) :
    r * (x-1)^(r-1) ≤ x^r - (x-1)^r := by
  have hh := (convexOn_rpow hr).le_slope_of_hasDerivAt
    (show x-1 ∈ Set.Ici (0 : ℝ) from sub_nonneg.mpr hx)
    (show x ∈ Set.Ici (0 : ℝ) from zero_le_one.trans hx)
    (show x-1 < x by linarith) (Real.hasDerivAt_rpow_const (Or.inr hr))
  simpa only [slope_def_field, sub_sub_cancel, div_one] using hh

lemma eventual_increment_lower {r t a : ℝ} (hr : 1 < r) (ht : 0 < t) (ha : a < t*r) :
    ∀ᶠ n : ℕ in atTop,
      a * (n : ℝ)^(r-1) ≤ t * ((n : ℝ)^r - ((n-1 : ℕ) : ℝ)^r) := by
  have hRatio : Tendsto (fun n : ℕ => (1 - 1/(n : ℝ))^(r-1)) atTop (𝓝 1) := by
    have hb : Tendsto (fun n : ℕ => 1-1/(n : ℝ)) atTop (𝓝 (1-0 : ℝ)) :=
      tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh := hb.rpow_const (p := r-1) (Or.inr (sub_nonneg.mpr hr.le))
    simpa using hh
  have hT : Tendsto (fun n : ℕ => t*r*(1-1/(n : ℝ))^(r-1)) atTop (𝓝 (t*r)) := by
    simpa using hRatio.const_mul (t*r)
  filter_upwards [hT.eventually_const_lt ha, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpred : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
  have hbase : 0 ≤ 1-1/(n : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hnpos).mpr hnreal
  have hEq : ((n : ℝ)-1)^(r-1) = (1-1/(n : ℝ))^(r-1) * (n : ℝ)^(r-1) := by
    rw [← Real.mul_rpow hbase hnpos.le]
    congr 1
    field_simp
  have hi := mul_le_mul_of_nonneg_left (rpow_increment_lower hnreal hr.le) ht.le
  have hm := mul_le_mul_of_nonneg_right hn.le (Real.rpow_nonneg hnpos.le (r-1))
  rw [hEq] at hi
  rw [hpred]
  nlinarith

lemma ratio_limit {f : ℕ → ℝ} {r c : ℝ}
    (h : IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ)^r)) :
    Tendsto (fun n : ℕ => f n / (n : ℝ)^r) atTop (𝓝 c) := by
  have hd : (fun n : ℕ => f n / (n : ℝ)^r) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^r / (n : ℝ)^r) := h.div .refl
  apply IsEquivalent.tendsto_const
  apply hd.congr_right
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change c * (n : ℝ)^r / (n : ℝ)^r = c
  exact mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (by exact_mod_cast hn) r).ne'

lemma potential_tendsto {f : ℕ → ℝ} {r c t : ℝ} (hr : 0 < r) (htc : t < c)
    (h : IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ)^r)) :
    Tendsto (fun n : ℕ => f n - t*(n : ℝ)^r) atTop atTop := by
  have hRatio := ratio_limit h
  have hLow : ∀ᶠ n : ℕ in atTop, (c-t)/2*(n : ℝ)^r ≤ f n-t*(n : ℝ)^r := by
    filter_upwards [hRatio.eventually_const_lt (show (c+t)/2 < c by linarith),
      eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hp := Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast hnp) r
    have hh := (lt_div_iff₀ hp).mp hn
    nlinarith
  have hTop : Tendsto (fun n : ℕ => (c-t)/2*(n : ℝ)^r) atTop atTop :=
    Tendsto.const_mul_atTop (by linarith) ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono' atTop hLow hTop

lemma exists_potential_record {W : Type*} (H : SimpleGraph W) {r c t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (htc : t < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^r)) (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ 0 < n ∧ t*(n : ℝ)^r < (extremalNumber n H : ℝ) ∧
      ∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ)-t*(j : ℝ)^r ≤
        (extremalNumber n H : ℝ)-t*(n : ℝ)^r := by
  classical
  let f : ℕ → ℝ := fun n => (extremalNumber n H : ℝ)-t*(n : ℝ)^r
  obtain ⟨n,hn⟩ := ((potential_tendsto hr htc h).eventually_gt_atTop ((M : ℝ)^2+1)).exists
  obtain ⟨m,hm,hMax⟩ := exists_max_image (range (n+1)) f ⟨n,by simp⟩
  have hBig : (M : ℝ)^2+1 < f m := hn.trans_le (hMax n (by simp))
  have hSquare : f m ≤ (m : ℝ)^2 := by
    have he : (extremalNumber m H : ℝ) ≤ (m : ℝ)^2 := by
      exact_mod_cast Erdos713RateRegularization.extremal_sq_bound H m
    dsimp only [f]
    nlinarith [mul_nonneg ht.le (Real.rpow_nonneg (Nat.cast_nonneg m) r)]
  have hM : M ≤ m := by
    by_contra hmM
    have hh : (m : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge hmM)
    have hh2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hh 2
    linarith
  have hmpos : 0 < m := by
    by_contra hh
    have hm0 : m = 0 := by omega
    rw [hm0] at hSquare hBig
    norm_num at hSquare
    nlinarith [sq_nonneg (M : ℝ)]
  refine ⟨m,hM,hmpos,?_,?_⟩
  · dsimp only [f] at hBig
    nlinarith [sq_nonneg (M : ℝ)]
  · intro j hj
    apply hMax j
    have hmN := mem_range.mp hm
    simp only [mem_range]
    omega

lemma exists_extremal_of_pos {W : Type*} (H : SimpleGraph W) (n : ℕ)
    (hn : 0 < extremalNumber n H) :
    ∃ G : SimpleGraph (Fin n), H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | H.Free G}
  have hS : S.Nonempty := by
    by_contra hs
    have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    change 0 < S.sup (fun G => G.edgeFinset.card) at hn
    simp only [he, sup_empty, bot_eq_zero, lt_self_iff_false] at hn
  obtain ⟨G,hG,he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
  refine ⟨G,by simpa [S] using hG,?_⟩
  change Nat.card G.edgeSet = S.sup (fun G => G.edgeFinset.card)
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using he.symm

lemma extremal_degree_of_record {W : Type*} (H : SimpleGraph W) {r t : ℝ} {n : ℕ}
    (hRecord : ∀ j : ℕ, j ≤ n → (extremalNumber j H : ℝ)-t*(j : ℝ)^r ≤
      (extremalNumber n H : ℝ)-t*(n : ℝ)^r)
    (G : SimpleGraph (Fin n)) (hFree : H.Free G) (he : Nat.card G.edgeSet = extremalNumber n H) :
    ∀ v, t*((n : ℝ)^r-((n-1 : ℕ) : ℝ)^r) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  classical
  intro v
  have hDel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hFree v
  rw [card_edgeFinset_deleteIncidenceSet] at hDel
  have hNat : G.edgeFinset.card ≤ extremalNumber (n-1) H + G.degree v := by
    simp only [Fintype.card_fin] at hDel
    have hh := G.degree_le_card_edgeFinset v
    omega
  simp only [edgeFinset_card, ← card_neighborSet_eq_degree, Fintype.card_eq_nat_card, he] at hNat
  have hReal : (extremalNumber n H : ℝ) ≤ (extremalNumber (n-1) H : ℝ) +
      (Nat.card (G.neighborSet v) : ℝ) := by exact_mod_cast hNat
  have hh := hRecord (n-1) (Nat.sub_le _ _)
  nlinarith

lemma exists_sharp_minimum_degree {W : Type*} (H : SimpleGraph W) {r c : ℝ}
    (hr : 1 < r) (_hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^r))
    (a b : ℝ) (_ha : 0 < a) (harc : a < r*c) (hb : 0 < b) (hbc : b < c) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n), H.Free G ∧
      Nat.card G.edgeSet = extremalNumber n H ∧
      b*(n : ℝ)^r ≤ (Nat.card G.edgeSet : ℝ) ∧
      ∀ v, a*(n : ℝ)^(r-1) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hamax : max (a/r) b < c := max_lt ((div_lt_iff₀ hrpos).mpr (by nlinarith)) hbc
  obtain ⟨t,htlow,htc⟩ := exists_between hamax
  have hbt : b < t := (le_max_right _ _).trans_lt htlow
  have ht : 0 < t := hb.trans hbt
  have hatr : a < t*r := (div_lt_iff₀ hrpos).mp ((le_max_left _ _).trans_lt htlow)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventual_increment_lower hr ht hatr)
  intro N
  obtain ⟨n,hn,hnpos,hLow,hRecord⟩ := exists_potential_record H hrpos ht htc h (max N M)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hepos : 0 < extremalNumber n H := by
    have hh : (0 : ℝ) < extremalNumber n H :=
      (mul_pos ht (Real.rpow_pos_of_pos hnr r)).trans hLow
    exact_mod_cast hh
  obtain ⟨G,hFree,hE⟩ := exists_extremal_of_pos H n hepos
  refine ⟨n,hnN,hnpos,G,hFree,hE,?_,?_⟩
  · rw [hE]
    exact (mul_le_mul_of_nonneg_right hbt.le (Real.rpow_nonneg hnr.le r)).trans hLow.le
  · intro v
    exact (hM n hnM).trans (extremal_degree_of_record H hRecord G hFree hE v)

end Erdos713SharpDegree
