import Submission.SquarefreeSmallContrast
import Submission.SummableAdditiveBandObstruction

/-! Finite reciprocal-prime square energy rules out uniform absolute oriented
margins on squarefree cubic collisions. It does not rule out arbitrary score
bands, colorings, or positive-density cube-Sidon sets. -/
namespace Erdos1206.L2OrientedScoreObstruction
open Finset SquarefreeConicFamily QuadraticPrimeMoments QuadraticEqualDiscriminant
  ConicScoreSplit
open scoped Classical
set_option maxHeartbeats 2000000

lemma primeScore_eq (f : ℕ → ℝ)
    (hmul : ∀a b : ℕ,0<a → 0<b → f (a*b)=f a+f b)
    {n : ℕ} (hn : Squarefree n) : primeScore f n=f n := by
  conv_rhs => rw [←Nat.prod_primeFactors_of_squarefree hn]
  exact (SummableAdditiveBandObstruction.score_prod f hmul n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)).symm

/-- All four roots are squarefree and avoid any prescribed integer's prime
support. The smallness assertion concerns only their signed contrast. -/
theorem collision_small_contrast (f : ℕ → ℝ)
    (hmul : ∀a b : ℕ,0<a → 0<b → f (a*b)=f a+f b)
    (hs : Summable (fun p : ℕ => if p.Prime then f p^2/p else 0))
    (q : ℕ) (hq : 0<q) {ε : ℝ} (hε : 0<ε) :
    ∃n : Fin 4 → ℕ, (∀i,0<n i ∧ Squarefree (n i) ∧ (n i).Coprime q) ∧
      n 0<n 1 ∧ n 1<n 2 ∧ n 2<n 3 ∧
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 ∧
      |f (n 1)+f (n 2)-f (n 0)-f (n 3)|<ε := by
  obtain ⟨x,hx0,hxsf,hxavoid,hsmall⟩ := SquarefreeSmallContrast.exists_small_contrast f hs q hε
  let n (i : Fin 4) := F i x.1 x.2
  have hn (i : Fin 4) : 0<n i ∧ Squarefree (n i) ∧ (n i).Coprime q := by
    refine ⟨F_pos i hx0,hxsf i,?_⟩
    by_contra hh
    obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    exact hxavoid p hp (Nat.le_of_dvd hq hpq) i hpn
  obtain ⟨_,h01,h12,h23⟩ := SquarefreeSummablePrimeObstruction.ordered_of_first_pos x.1 x.2 hx0
  refine ⟨n,hn,h01,h12,h23,identity x.1 x.2,?_⟩
  have he : totalContrast f x=f (n 1)+f (n 2)-f (n 0)-f (n 3) := by
    dsimp only [totalContrast]
    simp_rw [primeScore_eq f hmul (hxsf _)]
    simp [Fin.sum_univ_succ,sign,n]
    ring
  rwa [he] at hsmall

/-- No finite-square-energy completely additive score separates all
squarefree cubic collisions by a fixed positive absolute oriented margin. -/
theorem no_uniform_absolute_gap (f : ℕ → ℝ)
    (hmul : ∀a b : ℕ,0<a → 0<b → f (a*b)=f a+f b)
    (hs : Summable (fun p : ℕ => if p.Prime then f p^2/p else 0))
    (q : ℕ) (hq : 0<q) {ε : ℝ} (hε : 0<ε) :
    ¬(∀n : Fin 4 → ℕ, (∀i,0<n i ∧ Squarefree (n i) ∧ (n i).Coprime q) →
      n 0<n 1 → n 1<n 2 → n 2<n 3 →
      (n 0)^3+(n 3)^3=(n 1)^3+(n 2)^3 →
      ε≤|f (n 1)+f (n 2)-f (n 0)-f (n 3)|) := by
  intro hgap
  obtain ⟨n,hn,h01,h12,h23,he,hsmall⟩ := collision_small_contrast f hmul hs q hq hε
  exact (not_le_of_gt hsmall) (hgap n hn h01 h12 h23 he)

#print axioms collision_small_contrast
#print axioms no_uniform_absolute_gap
end Erdos1206.L2OrientedScoreObstruction
