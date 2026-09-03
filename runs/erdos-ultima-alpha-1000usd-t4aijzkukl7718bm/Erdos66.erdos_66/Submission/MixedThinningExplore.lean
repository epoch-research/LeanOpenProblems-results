import Submission.BernoulliConcentrationExplore
import Submission.CenteredMixedEnergyExplore

/-! A finite thinning lemma controlling mixed counts with a prescribed finite
family. It does not assert self-flatness of the thinned set or an infinite
scale-compatible construction. -/
namespace Erdos66MixedThinning
open Erdos66FiniteBernoulli Erdos66BernoulliConcentration
  Erdos66MixedEnergy Erdos66CyclicVariance Erdos66CenteredMixedEnergy
open scoped Classical

section Linear
variable {ι κ : Type*} [Fintype ι]

lemma linear_centered_mgf (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 2) (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*((∑ i, w i*bit (ω i)) - ∑ i, w i*p i))) ≤
      Real.exp (2*t^2*(∑ i, w i*p i)) := by
  have hdis : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (fun i j ↦ Disjoint ({i} : Finset ι) {j}) := by
    intro i hi j hj hij
    exact Finset.disjoint_singleton.mpr hij
  simpa only [monomial,Finset.prod_singleton] using centered_mgf_bound p hp Finset.univ
    (fun i ↦ {i}) hdis w (fun i _ ↦ hw i) t ht

theorem exists_simultaneous_linear_thinning (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset κ) (w : κ → ι → ℝ)
    (hw : ∀ k ∈ S, ∀ i, 0 ≤ w k i ∧ w k i ≤ 2) (V ε : ℝ)
    (hV : 0 < V) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : ∀ k ∈ S, (∑ i, w k i*p i) ≤ V)
    (hsmall : 2*S.card*Real.exp (-ε^2*V/8) < 1) :
    ∃ ω : ι → Bool, ∀ k ∈ S,
      |(∑ i, w k i*bit (ω i)) - ∑ i, w k i*p i| < ε*V := by
  exact exists_simultaneous_bound p hp S (fun k ω ↦ ∑ i, w k i*bit (ω i))
    (fun k ↦ ∑ i, w k i*p i) V ε hV hε hε1 hm
    (fun k hk t ht ↦ linear_centered_mgf p hp (w k) (hw k hk) t ht) hsmall

end Linear

section Group
variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]

noncomputable def thinned (B : Finset G) (ω : G → Bool) : Finset G :=
  B.filter (fun x ↦ ω x = true)

lemma thinned_subset (B : Finset G) (ω : G → Bool) : thinned B ω ⊆ B :=
  Finset.filter_subset _ _

lemma thinned_indicator (B : Finset G) (ω : G → Bool) (x : G) :
    indicator (thinned B ω) x = indicator B x*bit (ω x) := by
  by_cases hx : x ∈ B <;> cases hω : ω x <;> simp [indicator,thinned,hx,hω,bit]

lemma thinned_conv (B C : Finset G) (ω : G → Bool) (z : G) :
    conv (indicator (thinned B ω)) (indicator C) z =
      ∑ x : G, (indicator B x*indicator C (z-x))*bit (ω x) := by
  unfold conv
  simp_rw [thinned_indicator]
  apply Finset.sum_congr rfl
  intro x hx
  ring

lemma indicator_product_bounds (B C : Finset G) (z x : G) :
    0 ≤ indicator B x*indicator C (z-x) ∧ indicator B x*indicator C (z-x) ≤ 2 := by
  simp only [indicator]
  split_ifs <;> norm_num

/-- Thin one set while simultaneously controlling its mixed convolution with
all members of a fixed finite family, at every group element. The mean is
linear in the retention probability. -/
theorem exists_mixed_thinning (B : Finset G) (C : I → Finset G) (θ V ε : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hV : 0 < V) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmean : ∀ i z, θ*conv (indicator B) (indicator (C i)) z ≤ V)
    (hsmall : 2*(Fintype.card I : ℝ)*Fintype.card G*Real.exp (-ε^2*V/8) < 1) :
    ∃ D : Finset G, D ⊆ B ∧ ∀ i z,
      |conv (indicator D) (indicator (C i)) z - θ*conv (indicator B) (indicator (C i)) z| < ε*V := by
  let w : (I × G) → G → ℝ := fun iz x ↦ indicator B x*indicator (C iz.1) (iz.2-x)
  have hmeanEq (iz : I × G) : (∑ x : G, w iz x*θ) =
      θ*conv (indicator B) (indicator (C iz.1)) iz.2 := by
    dsimp only [w,conv]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hsmall' : 2*(Finset.univ : Finset (I × G)).card*Real.exp (-ε^2*V/8) < 1 := by
    simpa only [Finset.card_univ,Fintype.card_prod,Nat.cast_mul,mul_assoc] using hsmall
  obtain ⟨ω,hω⟩ := exists_simultaneous_linear_thinning (fun _ : G ↦ θ)
    (fun _ ↦ ⟨hθ0,hθ1⟩) Finset.univ w
    (fun iz _ x ↦ indicator_product_bounds B (C iz.1) iz.2 x)
    V ε hV hε hε1 (fun iz _ ↦ by rw [hmeanEq]; exact hmean iz.1 iz.2) hsmall'
  refine ⟨thinned B ω,thinned_subset B ω,fun i z ↦ ?_⟩
  have hh := hω (i,z) (Finset.mem_univ _)
  rw [hmeanEq] at hh
  simpa only [thinned_conv,w] using hh

end Group
end Erdos66MixedThinning
