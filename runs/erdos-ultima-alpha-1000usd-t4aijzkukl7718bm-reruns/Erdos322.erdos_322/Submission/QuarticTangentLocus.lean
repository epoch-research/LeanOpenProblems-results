import Submission.QuarticRationalTangency
import Submission.QuarticAdditiveBound

/-!
The rational tangent-hyperplane locus is exactly the additive-triple locus for
nonnegative tuples. Its count is subpolynomial, not the unrestricted count.
-/
namespace Erdos322Research.QuarticTangentLocus

open QuarticRationalTangency

/-- A tuple lies on a rational hyperplane tangent at a nonzero complex point
of the all-positive Fermat quartic at infinity. -/
def HasRationalTangentRelation {n : ℕ} (x : Fin 4 → Fin (n+1)) : Prop :=
  ∃ a : Fin 4 → ℚ, ∃ z : Fin 4 → ℂ, ∃ t : ℂ,
    (∑ i, z i^4=0) ∧ (∃ k, z k ≠ 0) ∧
    (∀ i, z i^3=t*(a i : ℂ)) ∧ ∑ i, a i*((x i : ℕ) : ℚ)=0

private theorem signed_triple_additive {n : ℕ} (x : Fin 4 → Fin (n+1))
    (a : Fin 4 → ℚ) (j : Fin 4) (b : ℚ) (hb : b ≠ 0) (hj : a j=0)
    (ha : ∀ i, i ≠ j → a i=b ∨ a i=-b)
    (hp : ∑ i, a i*((x i : ℕ) : ℚ)=0) : HasAdditiveTriple x := by
  let σ : Equiv.Perm (Fin 4) := Equiv.swap j 3
  have hσ3 : σ 3=j := by simp [σ]
  have hσne (i : Fin 4) (hi : i ≠ 3) : σ i ≠ j := by
    rw [← hσ3]
    exact σ.injective.ne hi
  let y : Fin 4 → ℚ := fun i => ((x (σ i) : ℕ) : ℚ)
  have hy (i : Fin 4) : 0 ≤ y i := by dsimp [y]; positivity
  have hp' : a (σ 0)*y 0+a (σ 1)*y 1+a (σ 2)*y 2=0 := by
    have he := (Equiv.sum_comp σ (fun i => a i*((x i : ℕ) : ℚ))).trans hp
    simpa only [Fin.sum_univ_four,hσ3,hj,zero_mul,add_zero] using he
  have hn : (a (σ 0)/b)*y 0+(a (σ 1)/b)*y 1+(a (σ 2)/b)*y 2=0 := by
    calc
      _ = (a (σ 0)*y 0+a (σ 1)*y 1+a (σ 2)*y 2)/b := by ring
      _ = 0 := by rw [hp',zero_div]
  have hcast (i j k : Fin 4) (h : y i=y j+y k) :
      (x (σ i) : ℕ)=(x (σ j) : ℕ)+(x (σ k) : ℕ) := by
    dsimp only [y] at h
    exact_mod_cast h
  obtain h0 | h0 := ha (σ 0) (hσne 0 (by decide))
  all_goals obtain h1 | h1 := ha (σ 1) (hσne 1 (by decide))
  all_goals obtain h2 | h2 := ha (σ 2) (hσne 2 (by decide))
  all_goals rw [h0,h1,h2] at hn
  all_goals simp only [div_self hb, neg_div, one_mul, neg_one_mul] at hn
  all_goals first
    | exact ⟨σ, hcast 2 0 1 (by linarith [hy 0,hy 1,hy 2])⟩
    | refine ⟨(Equiv.swap (1:Fin 4) 2).trans σ, ?_⟩
      change (x (σ 1) : ℕ)=(x (σ 0) : ℕ)+(x (σ 2) : ℕ)
      exact hcast 1 0 2 (by linarith [hy 0,hy 1,hy 2])
    | refine ⟨(Equiv.swap (0:Fin 4) 2).trans σ, ?_⟩
      change (x (σ 0) : ℕ)=(x (σ 2) : ℕ)+(x (σ 1) : ℕ)
      exact hcast 0 2 1 (by linarith [hy 0,hy 1,hy 2])

/-- No nonadditive nonnegative tuple lies on one of these tangent hyperplanes. -/
theorem tangent_relation_implies_additive {n : ℕ} (x : Fin 4 → Fin (n+1))
    (h : HasRationalTangentRelation x) : HasAdditiveTriple x := by
  obtain ⟨a,z,t,hs,hn,hc,hp⟩ := h
  obtain ⟨j,hj,b,hb,ha⟩ := rational_tangent_normal_classification z a t hc hs hn
  exact signed_triple_additive x a j b hb hj ha hp

/-- Every additive-triple relation is a rational tangent-hyperplane relation. -/
theorem additive_implies_tangent_relation {n : ℕ} (x : Fin 4 → Fin (n+1))
    (h : HasAdditiveTriple x) : HasRationalTangentRelation x := by
  obtain ⟨σ,hσ⟩ := h
  obtain ⟨z,hn,hs,hc⟩ := standard_additive_tangency
  let a : Fin 4 → ℚ := ![1,1,-1,0]
  refine ⟨fun i => a (σ.symm i), fun i => z (σ.symm i), 1, ?_, ?_, ?_, ?_⟩
  · exact (Equiv.sum_comp σ.symm (fun i => z i^4)).trans hs
  · obtain ⟨k,hk⟩ := hn
    exact ⟨σ k, by simpa using hk⟩
  · intro i
    simpa only [one_mul] using hc (σ.symm i)
  · have he : (∑ i, a (σ.symm i)*((x i : ℕ) : ℚ)) =
        ∑ i, a i*((x (σ i) : ℕ) : ℚ) := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp σ (fun i => a (σ.symm i)*((x i : ℕ) : ℚ))).symm
    rw [he, Fin.sum_univ_four]
    change 1*((x (σ 0) : ℕ) : ℚ)+1*((x (σ 1) : ℕ) : ℚ)+
      (-1)*((x (σ 2) : ℕ) : ℚ)+0*((x (σ 3) : ℕ) : ℚ)=0
    rw [hσ]
    push_cast
    ring

/-- Exact identification of the two loci. This does not say that all
representations belong to either locus. -/
theorem tangent_relation_iff_additive {n : ℕ} (x : Fin 4 → Fin (n+1)) :
    HasRationalTangentRelation x ↔ HasAdditiveTriple x :=
  ⟨tangent_relation_implies_additive x, additive_implies_tangent_relation x⟩

/-- Count only the representations on the rational tangent-hyperplane locus. -/
noncomputable def tangentQuarticCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Fin 4 → Fin (n+1) =>
    (∑ i, (x i : ℕ)^4=n) ∧ HasRationalTangentRelation x)).card

theorem tangent_count_eq_additive (n : ℕ) :
    tangentQuarticCount n=additiveQuarticCount n := by
  classical
  simp only [tangentQuarticCount, additiveQuarticCount, tangent_relation_iff_additive]

/-- The entire rational tangent-hyperplane contribution is subpolynomial.
No upper bound for the nonadditive complement is asserted. -/
theorem tangent_quartic_subpolynomial (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (tangentQuarticCount n : ℝ) ≤ C*(n : ℝ)^ε := by
  simpa only [tangent_count_eq_additive] using additive_quartic_subpolynomial ε hε

end Erdos322Research.QuarticTangentLocus
