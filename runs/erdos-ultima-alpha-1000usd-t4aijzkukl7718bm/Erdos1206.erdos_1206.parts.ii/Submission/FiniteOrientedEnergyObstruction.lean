import Submission.FinitePrimeEnergyCompactness
import Submission.L2OrientedScoreObstruction

/-! The finite-prefix square-energy budgets needed for uniform absolute
oriented margins are unbounded. This concerns a score construction only. -/
namespace Erdos1206.FiniteOrientedEnergyObstruction
open Finset Filter FinitePrimeEnergyCompactness SquarefreeConicFamily
  QuadraticPrimeMoments QuadraticEqualDiscriminant ConicScoreSplit
open scoped Classical Topology
set_option maxHeartbeats 2000000

/-- The test constraints already use just one fixed conic. -/
def FamilyMargin (N : ℕ) (ε : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀x : ℕ × ℕ, 0<x.1 → (∀i,Squarefree (F i x.1 x.2)) →
    (∀i,F i x.1 x.2≤N) → ε≤|totalContrast w x|

lemma contrast_cutoff (N : ℕ) (w : ℕ → ℝ) {x : ℕ × ℕ}
    (hx0 : 0<x.1) (hx : ∀i,F i x.1 x.2≤N) :
    totalContrast (cutoffWeight N w) x=totalContrast w x := by
  unfold totalContrast
  apply sum_congr rfl
  intro i hi
  congr 1
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpr,hpd,_⟩ := Nat.mem_primeFactors.mp hp
  have hpN : p≤N := (Nat.le_of_dvd (F_pos i hx0) hpd).trans (hx i)
  exact if_pos ⟨hpr,hpN⟩

lemma contrast_tendsto {w : ℕ → ℝ} {v : ℕ → ℕ → ℝ}
    (hv : ∀p,Tendsto (fun j => v j p) atTop (nhds (w p))) (x : ℕ × ℕ) :
    Tendsto (fun j => totalContrast (v j) x) atTop (nhds (totalContrast w x)) := by
  apply tendsto_finset_sum
  intro i hi
  exact (tendsto_finset_sum (F i x.1 x.2).primeFactors (fun p hp => hv p)).const_mul (sign i)

/-- A bound at every finite cutoff would yield a forbidden finite-energy
infinite score by coordinatewise compactness. -/
theorem no_uniform_budget {C ε : ℝ} (hC : 0≤C) (hε : 0<ε) :
    ¬(∀N : ℕ,∃w : ℕ → ℝ,prefixEnergy N w≤C ∧ FamilyMargin N ε w) := by
  intro h
  choose w henergy hmargin using h
  obtain ⟨v,φ,hφ,hv,_,hs⟩ := subsequence hC w henergy
  obtain ⟨x,hx0,hxsf,_,hsmall⟩ := SquarefreeSmallContrast.exists_small_contrast v hs 0 hε
  let M := ∑i : Fin 4,F i x.1 x.2
  have hM (i : Fin 4) : F i x.1 x.2≤M :=
    single_le_sum (f := fun i : Fin 4 => F i x.1 x.2) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hgap : ∀ᶠ j : ℕ in atTop,
      ε≤|totalContrast (cutoffWeight (φ j) (w (φ j))) x| := by
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop M)] with j hj
    have hsize (i : Fin 4) : F i x.1 x.2≤φ j := (hM i).trans hj
    rw [contrast_cutoff (φ j) (w (φ j)) hx0 hsize]
    exact hmargin (φ j) x hx0 hxsf hsize
  have hlim := (contrast_tendsto hv x).abs
  have hh := ge_of_tendsto hlim hgap
  exact (not_le_of_gt hsmall) hh

/-- For every real budget C there is a finite cutoff requiring more energy
than C. No numerical optimizer or unproved asymptotic is used. -/
theorem unbounded_finite_energy (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃N : ℕ,∀w : ℕ → ℝ,FamilyMargin N ε w → C<prefixEnergy N w := by
  have h := no_uniform_budget (le_max_right C 0) hε
  push_neg at h
  obtain ⟨N,hN⟩ := h
  refine ⟨N,fun w hw => ?_⟩
  by_contra! hh
  exact hN w (hh.trans (le_max_left C 0)) hw

/-- The lower bound persists at every later cutoff, not just a subsequence. -/
theorem eventually_exceeds_budget (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀w : ℕ → ℝ,FamilyMargin N ε w → C<prefixEnergy N w := by
  obtain ⟨M,hM⟩ := unbounded_finite_energy C hε
  filter_upwards [eventually_ge_atTop M] with N hMN
  intro w hw
  have hsmall : FamilyMargin M ε w := by
    intro x hx0 hxsf hxM
    exact hw x hx0 hxsf (fun i => (hxM i).trans hMN)
  exact (hM w hsmall).trans_le (prefixEnergy_mono w hMN)

/-- A statement directly in terms of completely additive real scores and
all strict squarefree collisions below N. -/
theorem unbounded_additive_energy (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃N : ℕ,∀f : ℕ → ℝ,
      (∀a b : ℕ,0<a → 0<b → f (a*b)=f a+f b) →
      (∀n : Fin 4 → ℕ,(∀i,0<n i ∧ Squarefree (n i) ∧ n i≤N) →
        n 0<n 1 → n 1<n 2 → n 2<n 3 →
        (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 →
        ε≤|f (n 1)+f (n 2)-f (n 0)-f (n 3)|) →
      C<prefixEnergy N f := by
  obtain ⟨N,hN⟩ := unbounded_finite_energy C hε
  refine ⟨N,fun f hmul hmargin => hN f ?_⟩
  intro x hx0 hxsf hxN
  let n (i : Fin 4) := F i x.1 x.2
  have hn (i : Fin 4) : 0<n i ∧ Squarefree (n i) ∧ n i≤N :=
    ⟨F_pos i hx0,hxsf i,hxN i⟩
  obtain ⟨_,h01,h12,h23⟩ := SquarefreeSummablePrimeObstruction.ordered_of_first_pos x.1 x.2 hx0
  have hh := hmargin n hn h01 h12 h23 (identity x.1 x.2)
  have he : totalContrast f x=f (n 1)+f (n 2)-f (n 0)-f (n 3) := by
    dsimp only [totalContrast]
    simp_rw [L2OrientedScoreObstruction.primeScore_eq f hmul (hxsf _)]
    simp [Fin.sum_univ_succ,sign,n]
    ring
  rwa [he]

#print axioms no_uniform_budget
#print axioms unbounded_finite_energy
#print axioms unbounded_additive_energy
end Erdos1206.FiniteOrientedEnergyObstruction
