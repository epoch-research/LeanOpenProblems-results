import FormalConjecturesUtil
import Submission.UpToTightExpansion

/-! Exact extremal witnesses with sharp minimum degree and expansion simultaneously.
The same graph realizes all the conclusions. Exact witnesses are not claimed to be
bipartite or almost regular. -/
open Filter SimpleGraph Asymptotics Finset
namespace Erdos713JointExact
open Erdos713Expansion

lemma expansionConstant_mono : Monotone expansionConstant := by
  intro x y hxy
  have hh := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) (sub_le_sub_right hxy 1)
  dsimp only [expansionConstant]
  linarith

lemma of_positive_lower_sequence {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (hc : 0 < c)
    (hLower : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ c*(n : ℝ)^α < (extremalNumber n H : ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t : ℝ, t < α → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n),
        H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        c*(n : ℝ)^α < (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, t*(Nat.card G.edgeSet : ℝ)/(n : ℝ) ≤
          (Nat.card (G.neighborSet v) : ℝ)) ∧
        (∀ S : Finset (Fin n), 2*S.card ≤ n →
          κ*(Nat.card G.edgeSet : ℝ)/(n : ℝ)*S.card ≤
            (Nat.card (Erdos713SwitchGluing.cross G (S : Set (Fin n))).edgeSet : ℝ)) := by
  let s : ℝ := (1+α)/2
  have hs : 1 < s := by dsimp [s]; linarith
  have hsα : s < α := by dsimp [s]; linarith
  refine ⟨expansionConstant s, expansionConstant_pos hs, ?_⟩
  intro t ht N
  obtain ⟨r,hrlo,hrα⟩ := exists_between (max_lt hsα ht)
  have hsr : s < r := (le_max_left _ _).trans_lt hrlo
  have htr : t < r := (le_max_right _ _).trans_lt hrlo
  have hr : 1 < r := hs.trans hsr
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (Erdos713SharpDegree.eventual_increment_lower (t := 1) hr (by norm_num)
      (show t < 1*r by simpa using htr))
  obtain ⟨n,hn,hnpos,C,hC,hEq,hUpper,hDense⟩ :=
    Erdos713TightExpansion.exists_tight_record H (zero_lt_one.trans hr) hrα hc hLower
      (max N M)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hepos : 0 < extremalNumber n H := by
    have : (0 : ℝ) < extremalNumber n H := by rw [hEq]; positivity
    exact_mod_cast this
  obtain ⟨G,hFree,hE⟩ := Erdos713SharpDegree.exists_extremal_of_pos H n hepos
  have hPotential : ∀ j : ℕ, j ≤ n →
      (extremalNumber j H : ℝ)-C*(j : ℝ)^r ≤
        (extremalNumber n H : ℝ)-C*(n : ℝ)^r := by
    intro j hj
    rw [hEq]
    linarith [hUpper j hj]
  have hDensity : (Nat.card G.edgeSet : ℝ)/(n : ℝ) = C*(n : ℝ)^(r-1) := by
    rw [hE,hEq,rpow_factor hnr.le hr]
    field_simp
  refine ⟨n,hnN,hnpos,G,hFree,hE,by simpa only [hE] using hDense,?_,?_⟩
  · intro v
    have hInc := mul_le_mul_of_nonneg_left (hM n hnM) hC.le
    have hDeg := Erdos713SharpDegree.extremal_degree_of_record H hPotential G hFree hE v
    rw [mul_div_assoc,hDensity]
    nlinarith
  · intro S hS
    have hCut := record_cut_bound H G hFree hr hC.le
      (by simpa only [Fintype.card_fin,hE] using hEq)
      (by simpa only [Fintype.card_fin] using hUpper) S
      (by simpa only [Fintype.card_fin] using hS)
    simp only [Fintype.card_fin] at hCut
    have hm := mul_le_mul_of_nonneg_right (expansionConstant_mono hsr.le)
      (show 0 ≤ C*(n : ℝ)^(r-1)*S.card by positivity)
    rw [mul_div_assoc,hDensity]
    nlinarith

lemma of_tight_rate {W : Type*} (H : SimpleGraph W) {α : ℝ}
    (hα : 1 < α) (h : Erdos713Tight.HasTightRate H α) :
    ∃ c κ : ℝ, 0 < c ∧ 0 < κ ∧ ∀ t : ℝ, t < α → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n),
        H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        c*(n : ℝ)^α < (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, t*(Nat.card G.edgeSet : ℝ)/(n : ℝ) ≤
          (Nat.card (G.neighborSet v) : ℝ)) ∧
        (∀ S : Finset (Fin n), 2*S.card ≤ n →
          κ*(Nat.card G.edgeSet : ℝ)/(n : ℝ)*S.card ≤
            (Nat.card (Erdos713SwitchGluing.cross G (S : Set (Fin n))).edgeSet : ℝ)) := by
  obtain ⟨c,hc,hLower⟩ := Erdos713Tight.exists_positive_lower_constant h
  obtain ⟨κ,hκ,hWitness⟩ := of_positive_lower_sequence H hα hc hLower
  exact ⟨c,κ,hc,hκ,hWitness⟩

lemma of_asymptotic {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : 1 < α) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a b : ℝ, 0 < a → a < α*c → 0 < b → b < c →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n),
        H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        b*(n : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, a*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ)) ∧
        (∀ S : Finset (Fin n), 2*S.card ≤ n →
          κ*S.card*(n : ℝ)^(α-1) ≤
            (Nat.card (Erdos713SwitchGluing.cross G (S : Set (Fin n))).edgeSet : ℝ)) := by
  have hαpos : 0 < α := zero_lt_one.trans hα
  obtain ⟨s,hcs,hsc⟩ := exists_between (div_lt_self hc hα)
  have hs : 0 < s := (div_pos hc hαpos).trans hcs
  have hcαs : c < α*s := by
    have hh := (div_lt_iff₀ hαpos).mp hcs
    nlinarith
  obtain ⟨C,hcC,hCαs⟩ := exists_between hcαs
  have hC : 0 < C := hc.trans hcC
  obtain ⟨B,hB,hUpper⟩ := linear_error_upper H hC hcC h
  let κ : ℝ := (α*s-C)*(1/2 : ℝ)^(α-1)/2
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos (mul_pos (sub_pos.mpr hCαs)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _)) (by norm_num)
  have hTop : Tendsto (fun n : ℕ => κ*(n : ℝ)^(α-1)) atTop atTop :=
    Tendsto.const_mul_atTop hκ ((tendsto_rpow_atTop (by linarith : 0 < α-1)).comp
      tendsto_natCast_atTop_atTop)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hTop.eventually_ge_atTop B)
  refine ⟨κ,hκ,?_⟩
  intro a b _ha hac hb hbc N
  have hLo : max (max s b) (a/α) < c :=
    max_lt (max_lt hsc hbc) ((div_lt_iff₀ hαpos).mpr (by nlinarith))
  obtain ⟨t,htlo,htc⟩ := exists_between hLo
  have hst : s < t := ((le_max_left s b).trans (le_max_left _ _)).trans_lt htlo
  have hbt : b < t := ((le_max_right s b).trans (le_max_left _ _)).trans_lt htlo
  have ht : 0 < t := hs.trans hst
  have hatα : a < t*α := (div_lt_iff₀ hαpos).mp ((le_max_right _ _).trans_lt htlo)
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (Erdos713SharpDegree.eventual_increment_lower hα ht hatα)
  obtain ⟨n,hn,hnpos,hLow,hRecord⟩ :=
    Erdos713SharpDegree.exists_potential_record H hαpos ht htc h (max (max N M) L)
  have hnN : N ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
  have hnM : M ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
  have hnL : L ≤ n := (le_max_right _ _).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hepos : 0 < extremalNumber n H := by
    have hh : (0 : ℝ) < extremalNumber n H :=
      (mul_pos ht (Real.rpow_pos_of_pos hnr α)).trans hLow
    exact_mod_cast hh
  obtain ⟨G,hFree,hE⟩ := Erdos713SharpDegree.exists_extremal_of_pos H n hepos
  refine ⟨n,hnN,hnpos,G,hFree,hE,?_,?_,?_⟩
  · rw [hE]
    exact (mul_le_mul_of_nonneg_right hbt.le (Real.rpow_nonneg hnr.le α)).trans hLow.le
  · intro v
    exact (hL n hnL).trans
      (Erdos713SharpDegree.extremal_degree_of_record H hRecord G hFree hE v)
  · intro S hS
    have hh := potential_record_cut_bound H G hFree hα ht.le hC.le
      (by simpa only [Fintype.card_fin] using hE)
      (by simpa only [Fintype.card_fin] using hRecord) hUpper S
      (by simpa only [Fintype.card_fin] using hS)
    simp only [Fintype.card_fin] at hh
    have hErr := mul_le_mul_of_nonneg_right (hM n hnM) (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
    have hInc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hst.le hαpos.le)
      (show 0 ≤ (1/2 : ℝ)^(α-1)*S.card*(n : ℝ)^(α-1) by positivity)
    dsimp only [κ] at hErr ⊢
    nlinarith

#print axioms of_asymptotic


universe u

lemma robust_of_tight_rate {W : Type u} [Fintype W] (H : SimpleGraph W) {α : ℝ}
    (hα : 1 < α) (h : Erdos713Tight.HasTightRate H α)
    (hNoIso : ∀ a, ∃ b, H.Adj a b)
    (hProper : ∀ J : SimpleGraph W, J < H →
      (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)^α)) :
    ∃ c κ : ℝ, 0 < c ∧ 0 < κ ∧ ∀ t : ℝ, t < α → ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ G : SimpleGraph (Fin n),
        H.Free G ∧ Nat.card G.edgeSet = extremalNumber n H ∧
        c*(n : ℝ)^α < (Nat.card G.edgeSet : ℝ) ∧
        (∀ v, t*(Nat.card G.edgeSet : ℝ)/(n : ℝ) ≤
          (Nat.card (G.neighborSet v) : ℝ)) ∧
        (∀ S : Finset (Fin n), 2*S.card ≤ n →
          κ*(Nat.card G.edgeSet : ℝ)/(n : ℝ)*S.card ≤
            (Nat.card (Erdos713SwitchGluing.cross G (S : Set (Fin n))).edgeSet : ℝ)) ∧
        (∀ (T : Type u) [Fintype T] (J : SimpleGraph T), J ⊑ H → ¬ Nonempty (J ≃g H) →
          ∀ F : SimpleGraph (Fin n), ε*(Nat.card G.edgeSet : ℝ) ≤ (Nat.card F.edgeSet : ℝ) →
            J ⊑ F) := by
  classical
  obtain ⟨c,κ,hc,hκ,hWitness⟩ := of_tight_rate H hα h
  refine ⟨c,κ,hc,hκ,?_⟩
  intro t ht ε hε N
  obtain ⟨M,hM⟩ := Erdos713TightExpansion.uniform_proper_littleO H hNoIso hProper
    (show 0 < ε*c by positivity)
  obtain ⟨n,hn,hnpos,G,hFree,hE,hDense,hDeg,hCuts⟩ := hWitness t ht (max N M)
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  refine ⟨n,hnN,hnpos,G,hFree,hE,hDense,hDeg,hCuts,?_⟩
  intro T _ J hJH hNe F hF
  have hu := hM n hnM T J hJH hNe
  have hl := mul_lt_mul_of_pos_left hDense hε
  have hlt : (extremalNumber n J : ℝ) < (Nat.card F.edgeSet : ℝ) := by nlinarith
  apply IsContained.of_extremalNumber_lt_card_edgeFinset
  simp only [edgeFinset_card,Fintype.card_eq_nat_card,Nat.card_fin]
  exact_mod_cast hlt

#print axioms robust_of_tight_rate

#print axioms of_positive_lower_sequence
#print axioms of_tight_rate
end Erdos713JointExact
