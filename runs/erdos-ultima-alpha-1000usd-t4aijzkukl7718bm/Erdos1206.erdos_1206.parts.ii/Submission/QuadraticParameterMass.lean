import Submission.AffineQuadraticSquarefreeSieve

/-! Quadratic height and a positive parameter proportion imply divergent
reciprocal mass on the parameter subtype. No root-set density is asserted. -/
namespace Erdos1206.QuadraticParameterMass
open Finset Filter
open scoped Classical Topology

theorem reciprocal_not_summable (P : ℕ × ℕ → Prop) (height : ℕ × ℕ → ℕ)
    (H : ℕ) (hHpos : 0 < H) (hpos : ∀ x, 0 < height x)
    (hbound : ∀ N, 0 < N → ∀ x ∈ (range N) ×ˢ (range N), height x ≤ (H*N)^2)
    (hmany : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
      (((range N) ×ˢ (range N)).filter P).card) :
    ¬ Summable (fun x : {x : ℕ × ℕ // P x} => (1:ℝ)/height x.val) := by
  intro hidx
  let weight (x : ℕ × ℕ) : ℝ := if P x then 1/(height x) else 0
  let good (N : ℕ) := ((range N) ×ˢ (range N)).filter P
  have hs : Summable weight := by
    have hh := (summable_subtype_iff_indicator (s := {x | P x})
      (f := fun x => (1:ℝ)/height x)).mp hidx
    simpa only [weight,Set.indicator,Set.mem_setOf_eq] using hh
  have hH : (0:ℝ)<H := by exact_mod_cast hHpos
  have hε : (0:ℝ)<1/(4*(H:ℝ)^2) := by positivity
  obtain ⟨S,hS⟩ := summable_iff_vanishing_norm.mp hs _ hε
  obtain ⟨N,hNg,hNS⟩ := (hmany.and
    (eventually_ge_atTop (4*S.card+1))).exists
  have hN : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hNSR : 4*(S.card:ℝ)+1≤N := by exact_mod_cast hNS
  let T := good N \ S
  have hTc : (N:ℝ)^2/4 ≤ T.card := by
    have hh : ((good N).card:ℝ)≤T.card+S.card := by
      exact_mod_cast (card_le_card_sdiff_add_card (s := good N) (t := S))
    nlinarith [show (0:ℝ)≤(N:ℝ)^2 by positivity]
  have hper : ∀ x∈T, 1/((H:ℝ)^2*(N:ℝ)^2)≤weight x := by
    intro x hx
    have hxg := (mem_sdiff.mp hx).1
    have hxG : P x := (mem_filter.mp hxg).2
    have hxN := (mem_filter.mp hxg).1
    have hrootR : (0:ℝ)<height x := by exact_mod_cast hpos x
    have hrootbound : (height x:ℝ)≤(H:ℝ)^2*(N:ℝ)^2 := by
      have hh := hbound N hN x hxN
      change height x≤(H*N)^2 at hh
      exact_mod_cast (by simpa only [mul_pow] using hh : height x≤H^2*N^2)
    simp only [weight,if_pos hxG]
    exact one_div_le_one_div_of_le hrootR hrootbound
  have hsum := sum_le_sum hper
  have hTsum : (T.card:ℝ)*(1/((H:ℝ)^2*(N:ℝ)^2))≤∑x∈T,weight x := by
    simpa only [sum_const,nsmul_eq_mul] using hsum
  have hlow : 1/(4*(H:ℝ)^2)≤∑x∈T,weight x := by
    calc
      1/(4*(H:ℝ)^2) = ((N:ℝ)^2/4)/((H:ℝ)^2*(N:ℝ)^2) := by
        field_simp
      _ ≤ (T.card:ℝ)/((H:ℝ)^2*(N:ℝ)^2) := div_le_div_of_nonneg_right hTc (by positivity)
      _ ≤ ∑x∈T,weight x := by simpa only [mul_one_div] using hTsum
  have htail := hS T sdiff_disjoint
  have habs : (∑x∈T,weight x) ≤ ‖∑x∈T,weight x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (∑x∈T,weight x)
  linarith

#print axioms reciprocal_not_summable
end Erdos1206.QuadraticParameterMass
