import Submission.PatternInsertionDominationExplore
import Submission.ExactBracketHostEnvelopeExplore

/-! Downward-hereditary boundary and central-triple invariants preserved by
a sublogarithmic insertion. Constant triple caps are stronger than needed
for this stability statement; they are not claimed to be preserved. -/
namespace Erdos66SublogPatternInvariants
open Filter AdditiveCombinatorics Erdos66PatternInsertionDomination
  Erdos66BoundaryPairCounts Erdos66CentralTripleCounts Erdos66BoundaryPairPotential
  Erdos66JointBoundaryTripleCounts
open scoped Classical Topology
set_option maxHeartbeats 2600000

def SmallBoundary (A : Set ℕ) : Prop := ∀ ε : ℝ, 0<ε → ∃ d : ℕ, 2 ≤ d ∧
  ∀ᶠ n : ℕ in atTop, ((boundary A d n).card : ℝ) ≤ ε*Real.log ((n : ℝ)+2)

def SublogCentral (A : Set ℕ) : Prop := ∀ (C h : ℕ) (ε : ℝ), 0<ε →
  ∀ᶠ N : ℕ in atTop, ∀ n z, n ≤ C*N → z ≤ N^h → n≠z →
    ((fiber A N n z).card : ℝ) ≤ ε*Real.log ((N : ℝ)+2)

lemma smallBoundary_mono {A B : Set ℕ} (hAB : A ⊆ B) (hB : SmallBoundary B) : SmallBoundary A := by
  intro ε hε
  obtain ⟨d,hd,hD⟩ := hB ε hε
  refine ⟨d,hd,?_⟩
  filter_upwards [hD] with n hn
  exact (show ((boundary A d n).card : ℝ) ≤ (boundary B d n).card by
    exact_mod_cast Finset.card_le_card (boundary_mono hAB d n)).trans hn

lemma sublogCentral_mono {A B : Set ℕ} (hAB : A ⊆ B) (hB : SublogCentral B) : SublogCentral A := by
  intro C h ε hε
  filter_upwards [hB C h ε hε] with N hN
  intro n z hn hz hnz
  exact (show ((fiber A N n z).card : ℝ) ≤ (fiber B N n z).card by
    exact_mod_cast Finset.card_le_card (fiber_mono hAB N n z)).trans (hN n z hn hz hnz)

lemma log_polynomial_bound (N h x : ℕ) (hx : x ≤ N^h) :
    Real.log ((x : ℝ)+2) ≤ ((h : ℝ)+2)*Real.log ((N : ℝ)+2) := by
  have hp1 : 1 ≤ (N+2)^h := Nat.one_le_pow _ _ (by omega)
  have hp : x+2 ≤ (N+2)^(h+2) := by
    calc
      _ ≤ (N+2)^h+2*(N+2)^h := by have := Nat.pow_le_pow_left (show N ≤ N+2 by omega) h; omega
      _ = 3*(N+2)^h := by ring
      _ ≤ (N+2)^2*(N+2)^h := Nat.mul_le_mul_right _ (by
        have hh : (2 : ℕ)^2 ≤ (N+2)^2 := Nat.pow_le_pow_left (by omega) 2
        norm_num at hh
        omega)
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hh := Real.log_le_log (by positivity : (0 : ℝ)<(x : ℝ)+2)
    (show (x : ℝ)+2 ≤ ((N : ℝ)+2)^(h+2) by exact_mod_cast hp)
  rw [Real.log_pow] at hh
  simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

lemma uniform_polynomial_sublog (f : ℕ → ℝ)
    (hf : Tendsto (fun n : ℕ ↦ f n/Real.log ((n : ℝ)+2)) atTop (𝓝 0))
    (h : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x, N ≤ x → x ≤ N^h → f x ≤ ε*Real.log ((N : ℝ)+2) := by
  have hhpos : 0<(h : ℝ)+2 := by positivity
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hf.eventually_le_const (div_pos hε hhpos))
  filter_upwards [eventually_ge_atTop M] with N hN
  intro x hNx hx
  have hlx : 0<Real.log ((x : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) x; linarith)
  have hfX := (div_le_iff₀ hlx).mp (hM x (hN.trans hNx))
  calc
    _ ≤ (ε/((h : ℝ)+2))*Real.log ((x : ℝ)+2) := hfX
    _ ≤ (ε/((h : ℝ)+2))*(((h : ℝ)+2)*Real.log ((N : ℝ)+2)) :=
      mul_le_mul_of_nonneg_left (log_polynomial_bound N h x hx) (div_nonneg hε.le hhpos.le)
    _ = _ := by field_simp

lemma smallBoundary_of_certificate (A : Set ℕ) (NB : ℕ → ℕ)
    (hB : ∀ j n, NB j ≤ n → ((j : ℝ)+1)*((boundary A (cutoff j) n).card : ℝ) ≤
      20*Real.log ((n : ℝ)+1)) : SmallBoundary A := by
  intro ε hε
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 20
  simp only [mul_zero] at hlim
  obtain ⟨j,hj⟩ := (hlim.eventually_le_const hε).exists
  have hj' : 20/((j : ℝ)+1) ≤ ε := by simpa only [mul_one_div] using hj
  refine ⟨cutoff j,cutoff_ge_two j,?_⟩
  filter_upwards [eventually_ge_atTop (NB j)] with n hn
  have hh := hB j n hn
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<(n : ℝ)+1)
    (show (n : ℝ)+1 ≤ (n : ℝ)+2 by linarith)
  have hlpos : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hc : ((boundary A (cutoff j) n).card : ℝ) ≤ (20/((j : ℝ)+1))*Real.log ((n : ℝ)+2) := by
    have hb := (le_div_iff₀ (by positivity : (0 : ℝ)<(j : ℝ)+1)).mpr
      (show ((boundary A (cutoff j) n).card : ℝ)*((j : ℝ)+1) ≤ 20*Real.log ((n : ℝ)+2) by linarith)
    convert hb using 1
    ring
  exact hc.trans (mul_le_mul_of_nonneg_right hj' hlpos)

lemma sublogCentral_of_certificate (A : Set ℕ) (NT : ℕ → ℕ → ℕ)
    (hT : ∀ C h N n z, NT C h ≤ N → n ≤ C*N → z ≤ N^h → n≠z →
      (fiber A N n z).card ≤ tripleCap h) : SublogCentral A := by
  intro C h ε hε
  have hx : Tendsto (fun N : ℕ ↦ (N : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ by linarith) tendsto_natCast_atTop_atTop
  have hl := (Real.tendsto_log_atTop.comp hx).const_div_atTop (tripleCap h : ℝ)
  filter_upwards [hl.eventually_le_const hε,eventually_ge_atTop (NT C h)] with N hN hNT
  intro n z hn hz hnz
  have hlog : 0<Real.log ((N : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hh : ((fiber A N n z).card : ℝ) ≤ tripleCap h := by exact_mod_cast hT C h N n z hNT hn hz hnz
  exact hh.trans ((div_le_iff₀ hlog).mp hN)

lemma smallBoundary_insert (A B : Set ℕ) (hAB : A ⊆ B) (hA : SmallBoundary A)
    (hinc : Tendsto (fun n : ℕ ↦ ((sumRep B n : ℝ)-sumRep A n)/Real.log ((n : ℝ)+2)) atTop (𝓝 0)) :
    SmallBoundary B := by
  intro ε hε
  obtain ⟨d,hd,hD⟩ := hA (ε/2) (by positivity)
  refine ⟨d,hd,?_⟩
  filter_upwards [hD,hinc.eventually_le_const (show (0 : ℝ)<ε/2 by positivity)] with n hn hi
  have hl : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hh := (div_le_iff₀ hl).mp hi
  have hb := boundary_increment_bound A B hAB d n
  linarith

lemma sublogCentral_insert (A B : Set ℕ) (hAB : A ⊆ B) (hA : SublogCentral A)
    (hinc : Tendsto (fun n : ℕ ↦ ((sumRep B n : ℝ)-sumRep A n)/Real.log ((n : ℝ)+2)) atTop (𝓝 0)) :
    SublogCentral B := by
  intro C h ε hε
  let H := max h 2
  have hu := uniform_polynomial_sublog (fun n ↦ (sumRep B n : ℝ)-sumRep A n) hinc H (ε/3) (by positivity)
  filter_upwards [hA C h (ε/3) (by positivity),hu,eventually_ge_atTop (max C 1)] with N hN hi hNC
  intro n z hn hz hnz
  by_cases hlow : n<N ∨ z<N
  · rw [fiber_eq_empty_of_small B N n z hlow,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg hε.le (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith))
  · have hNp : 0<N := by omega
    have hn2 : n ≤ N^2 := by have hC : C ≤ N := (le_max_left _ _).trans hNC; nlinarith
    have hnH : n ≤ N^H := hn2.trans (Nat.pow_le_pow_right hNp (le_max_right _ _))
    have hzH : z ≤ N^H := hz.trans (Nat.pow_le_pow_right hNp (le_max_left _ _))
    have hin := hi n (by omega) hnH
    have hiz := hi z (by omega) hzH
    have hold := hN n z hn hz hnz
    have hb := fiber_increment_bound A B hAB N n z
    linarith

end Erdos66SublogPatternInvariants
