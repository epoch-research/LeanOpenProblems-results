import FormalConjecturesUtil
import Submission.ExactCloneSaturation

/-! Quadratic support records from a superlinear, subquadratic exact power
law, and exactly extremal hosts with no safe full clone. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713QuadraticSupports
open Erdos713ExactCloneSaturation Erdos713Cloning Erdos713CloneSymm

lemma exists_support (f : ℕ → ℕ)
    (hz : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : 0 < (f k : ℝ)-ε*(k : ℝ)^2) :
    ∃ n : ℕ, QuadSupport f ε n ∧
      (f k : ℝ)-ε*(k : ℝ)^2 ≤ (f n : ℝ)-ε*(n : ℝ)^2 := by
  have htail : ∀ᶠ n : ℕ in atTop, (f n : ℝ)-ε*(n : ℝ)^2 < 0 := by
    filter_upwards [hz.eventually_lt_const hε,eventually_gt_atTop (0 : ℕ)] with n hn hnp
    have hp : 0 < (n : ℝ)^2 := by positivity
    have hh := (div_lt_iff₀ hp).mp hn
    linarith
  obtain ⟨M,hM⟩ := eventually_atTop.mp htail
  let g : ℕ → ℝ := fun n => (f n : ℝ)-ε*(n : ℝ)^2
  obtain ⟨n,hn,hmax⟩ := (range (M+k+1)).exists_max_image g ⟨k,by simp⟩
  have hkn := hmax k (by simp)
  refine ⟨n,?_,hkn⟩
  intro m
  have hmn : g m ≤ g n := by
    by_cases hm : m < M+k+1
    · exact hmax m (mem_range.mpr hm)
    · exact (hM m (by omega)).le.trans (hk.le.trans hkn)
  dsimp only [g] at hmn
  linarith

lemma support_from_linear_record (f : ℕ → ℕ)
    (hz : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^2) atTop (𝓝 0))
    {k : ℕ} (hk : 0 < k) (hfk : 0 < (f k : ℝ))
    (hrec : ∀ j : ℕ, j ≤ k → (f j : ℝ) ≤ (f k : ℝ)/(k : ℝ)*j) :
    ∃ n : ℕ, k < 4*n ∧ QuadSupport f ((f k : ℝ)/(2*(k : ℝ)^2)) n := by
  let ε : ℝ := (f k : ℝ)/(2*(k : ℝ)^2)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : ε*(k : ℝ)^2 = (f k : ℝ)/2 := by dsimp [ε]; field_simp
  obtain ⟨n,hn,hmax⟩ := exists_support f hz hε (k := k) (by rw [heq]; linarith)
  refine ⟨n,?_,hn⟩
  by_contra hbad
  have hnk : n ≤ k := by omega
  have hbadR : 4*(n : ℝ) ≤ k := by exact_mod_cast (show 4*n ≤ k by omega)
  have hbound := hrec n hnk
  have hfrac : (f k : ℝ)/(k : ℝ)*n ≤ (f k : ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_left hbadR (div_nonneg hfk.le hkR.le)
    have he : (f k : ℝ)/(k : ℝ)*(k : ℝ) = (f k : ℝ) := div_mul_cancel₀ _ hkR.ne'
    nlinarith only [hh,he]
  have hp : 0 ≤ ε*(n : ℝ)^2 := by positivity
  rw [heq] at hmax
  linarith

/-- The support can have arbitrarily small curvature, arbitrarily large
order, and arbitrarily large slope at that order. -/
theorem cofinal_supports (f : ℕ → ℕ) (hf0 : f 0 = 0) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (N D : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ) (ε : ℝ), N ≤ n ∧ 0 < n ∧ 0 < ε ∧ ε < η ∧
      QuadSupport f ε n ∧ (D : ℝ) ≤ ε*(2*(n : ℝ)-1) := by
  have hz : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using Erdos713FutureRecords.higher_ratio_zero ha2 h
  have ht : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)) atTop atTop := by
    simpa only [Real.rpow_one] using Erdos713FutureRecords.lower_ratio_top ha hc h
  let b := min η 1
  have hb : 0 < b := lt_min hη (by norm_num)
  have hev : ∀ᶠ k : ℕ in atTop,
      4*((D : ℝ)+1) < (f k : ℝ)/(k : ℝ) ∧
      (f k : ℝ)/(k : ℝ)^2 < 2*b :=
    (ht.eventually_gt_atTop _).and (hz.eventually_lt_const (by positivity))
  obtain ⟨K,hK⟩ := eventually_atTop.mp hev
  obtain ⟨k,hkbound,hk,hfk,hrecord⟩ :=
    Erdos713FutureRecords.exists_past_record ha hc h (max K (4*N+1))
  have hkK : K ≤ k := (le_max_left _ _).trans hkbound
  obtain ⟨hlarge,hsmall⟩ := hK k hkK
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlin : ∀ j : ℕ, j ≤ k → (f j : ℝ) ≤ (f k : ℝ)/(k : ℝ)*j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j; simp [hf0]
    · have hjR : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
      have hh := hrecord j hj
      simp only [Real.rpow_one] at hh
      exact (div_le_iff₀ hjR).mp hh
  obtain ⟨n,hkn,hrec⟩ := support_from_linear_record f hz hk hfk hlin
  let ε : ℝ := (f k : ℝ)/(2*(k : ℝ)^2)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heps : ε = ((f k : ℝ)/(k : ℝ)^2)/2 := by dsimp [ε]; ring
  have hεb : ε < b := by rw [heps]; linarith
  have hεη : ε < η := hεb.trans_le (min_le_left _ _)
  have hεone : ε < 1 := hεb.trans_le (min_le_right _ _)
  have hN : N ≤ n := by have := (le_max_right K (4*N+1)).trans hkbound; omega
  have hn : 0 < n := by omega
  refine ⟨n,ε,hN,hn,hε,hεη,hrec,?_⟩
  have hknR : (k : ℝ) < 4*(n : ℝ) := by exact_mod_cast hkn
  have hm := mul_lt_mul_of_pos_left hknR hε
  have heq : 2*ε*(k : ℝ) = (f k : ℝ)/(k : ℝ) := by
    dsimp [ε]
    field_simp
  nlinarith only [hm,heq,hlarge,hεone]

/-- Exact ordinary extremal hosts with arbitrarily large minimum degree
and a single-fold obstruction at EVERY vertex. This does not assert that
the output is bipartite or secondary-optimal. -/
theorem exact_saturated_cofinal {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ a b, H.Adj a b) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      N ≤ Fintype.card U ∧ H.Free J ∧
      Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧ ∀ x, SingleFold H J x := by
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  let A : ℝ := (L : ℝ)^2+L+2
  have hA : 0 < A := by dsimp [A]; positivity
  have hη : 0 < (1 : ℝ)/A := by positivity
  have hzero : extremalNumber 0 H = 0 := Erdos713Cloning.extremal_zero H
  obtain ⟨n,ε,hN,hn,hε,hsmall,hrec,hD⟩ := cofinal_supports
    (fun n => extremalNumber n H) hzero ha ha2 hc h N (max D (Fintype.card W)) hη
  obtain ⟨G,hopt,he⟩ := exists_ordinary_optimal H hEdge n
  have hcurv : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2+
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)+(2 : ℝ)) < 1 := by
    have hh := (lt_div_iff₀ hA).mp hsmall
    simpa [A,L] using hh
  obtain ⟨U,hU,J,hnJ,_,hf,hE,hdeg,hfold⟩ := exact_at_quadratic_support H hH hn
    (le_max_right D _) G hopt he hε hrec hD hcurv
  exact ⟨U,hU,J,hN.trans hnJ,hf,hE,fun x => (le_max_left D _).trans (hdeg x),hfold⟩

#print axioms cofinal_supports
#print axioms exact_saturated_cofinal
end Erdos713QuadraticSupports
