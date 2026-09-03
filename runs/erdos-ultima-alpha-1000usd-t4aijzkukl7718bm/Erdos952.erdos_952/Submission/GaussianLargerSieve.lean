import Submission.GaussianCollisionDiscriminant

/-! A finite Gaussian larger-sieve inequality. The local class counts and
actual pairwise distances are retained. This does not assert a uniform
bound on the length of admissible paths. -/
namespace Erdos952Investigation.GaussianLargerSieve
open GaussianCollisionDiscriminant
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

lemma classes_card_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → GaussianInt) (g : GaussianInt) : 0 < (classes z g).card := by
  exact Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Logarithmic form of the exact divisibility budget. -/
theorem collision_log_budget {ι J : Type*} [Fintype ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hg : ∀ j ∈ S, g j ≠ 0)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (∑ j ∈ S, (collisionCount z (g j) : ℝ)*Real.log ((g j).norm : ℝ)) ≤
      ∑ ij ∈ (Finset.univ : Finset ι).offDiag, Real.log ((z ij.1-z ij.2).norm : ℝ) := by
  have hgp (j) (hj : j ∈ S) : (0 : ℝ) < (g j).norm := by
    exact_mod_cast GaussianInt.norm_pos.mpr (hg j hj)
  have hzp (ij : ι × ι) (hij : ij ∈ (Finset.univ : Finset ι).offDiag) :
      (0 : ℝ) < (z ij.1-z ij.2).norm := by
    have hne : z ij.1-z ij.2 ≠ 0 := sub_ne_zero.mpr (fun he => (Finset.mem_offDiag.mp hij).2.2 (hz he))
    exact_mod_cast GaussianInt.norm_pos.mpr hne
  have hp : (∏ j ∈ S, ((g j).norm : ℝ)^(collisionCount z (g j))) ≤
      ∏ ij ∈ (Finset.univ : Finset ι).offDiag, ((z ij.1-z ij.2).norm : ℝ) := by
    exact_mod_cast collision_norm_product_le z hz g S hc
  have hh := Real.log_le_log (Finset.prod_pos (fun j hj => pow_pos (hgp j hj) _)) hp
  rw [Real.log_prod (fun j hj => (pow_pos (hgp j hj) _).ne'),
    Real.log_prod (fun ij hij => (hzp ij hij).ne')] at hh
  simpa only [Real.log_pow] using hh

/-- The larger sieve combines Cauchy-Schwarz for the local classes with the
prime-power divisibility of the product of differences. The moduli may be
composite, provided they are nonzero and pairwise coprime. -/
theorem larger_sieve_distance_inequality {ι J : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hg : ∀ j ∈ S, g j ≠ 0)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j))) :
    (Fintype.card ι : ℝ)^2*(∑ j ∈ S, Real.log ((g j).norm : ℝ)/(classes z (g j)).card) ≤
      (∑ ij ∈ (Finset.univ : Finset ι).offDiag, Real.log ((z ij.1-z ij.2).norm : ℝ))+
        (Fintype.card ι : ℝ)*(∑ j ∈ S, Real.log ((g j).norm : ℝ)) := by
  have hlocal (j) (hj : j ∈ S) :
      (Fintype.card ι : ℝ)^2/(classes z (g j)).card*Real.log ((g j).norm : ℝ) ≤
      ((Fintype.card ι : ℝ)+(collisionCount z (g j) : ℝ))*Real.log ((g j).norm : ℝ) := by
    have hr : (0 : ℝ) < (classes z (g j)).card := by exact_mod_cast classes_card_pos z (g j)
    have hn : (1 : ℤ) ≤ (g j).norm := by have := GaussianInt.norm_pos.mpr (hg j hj); omega
    have hl : 0 ≤ Real.log ((g j).norm : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    apply mul_le_mul_of_nonneg_right _ hl
    apply (div_le_iff₀ hr).mpr
    have hh : (Fintype.card ι : ℝ)^2 ≤
        ((classes z (g j)).card : ℝ)*((Fintype.card ι : ℝ)+(collisionCount z (g j) : ℝ)) := by
      exact_mod_cast class_collision_inequality z (g j)
    simpa only [mul_comm] using hh
  have hb := collision_log_budget z hz g S hg hc
  calc
    _ = ∑ j ∈ S, (Fintype.card ι : ℝ)^2/(classes z (g j)).card*Real.log ((g j).norm : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j ∈ S, ((Fintype.card ι : ℝ)+(collisionCount z (g j) : ℝ))*Real.log ((g j).norm : ℝ) :=
      Finset.sum_le_sum hlocal
    _ = (Fintype.card ι : ℝ)*(∑ j ∈ S, Real.log ((g j).norm : ℝ))+
        (∑ j ∈ S, (collisionCount z (g j) : ℝ)*Real.log ((g j).norm : ℝ)) := by
      simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := by linarith

/-- A diameter bound may be substituted for the exact geometric budget. -/
theorem larger_sieve_diameter_inequality {ι J : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hg : ∀ j ∈ S, g j ≠ 0)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j)))
    (B : ℝ) (hB : ∀ i j, i ≠ j → ((z i-z j).norm : ℝ) ≤ B) :
    (Fintype.card ι : ℝ)^2*(∑ j ∈ S, Real.log ((g j).norm : ℝ)/(classes z (g j)).card) ≤
      ((Fintype.card ι : ℝ)^2-(Fintype.card ι : ℝ))*Real.log B+
        (Fintype.card ι : ℝ)*(∑ j ∈ S, Real.log ((g j).norm : ℝ)) := by
  have hpair (ij : ι × ι) (hij : ij ∈ (Finset.univ : Finset ι).offDiag) :
      Real.log ((z ij.1-z ij.2).norm : ℝ) ≤ Real.log B := by
    have hne := (Finset.mem_offDiag.mp hij).2.2
    apply Real.log_le_log _ (hB ij.1 ij.2 hne)
    exact_mod_cast GaussianInt.norm_pos.mpr (sub_ne_zero.mpr (fun he => hne (hz he)))
  have hcard : (((Finset.univ : Finset ι).offDiag).card : ℝ) =
      (Fintype.card ι : ℝ)^2-(Fintype.card ι : ℝ) := by
    rw [Finset.offDiag_card,Finset.card_univ,Nat.cast_sub (Nat.le_mul_self _),Nat.cast_mul,pow_two]
  have hs := Finset.sum_le_sum hpair
  rw [Finset.sum_const,nsmul_eq_mul,hcard] at hs
  have hh := larger_sieve_distance_inequality z hz g S hg hc
  linarith

/-- Standard larger-sieve cardinal bound. Positivity of the denominator is
a real hypothesis; it has not been established for arbitrary moat paths. -/
theorem larger_sieve_card_bound {ι J : Type*} [Fintype ι] [Nonempty ι]
    (z : ι → GaussianInt) (hz : Function.Injective z)
    (g : J → GaussianInt) (S : Finset J)
    (hg : ∀ j ∈ S, g j ≠ 0)
    (hc : (S : Set J).Pairwise (fun i j => IsCoprime (g i) (g j)))
    (B : ℝ) (hB : ∀ i j, i ≠ j → ((z i-z j).norm : ℝ) ≤ B)
    (hden : 0 < (∑ j ∈ S, Real.log ((g j).norm : ℝ)/(classes z (g j)).card)-Real.log B) :
    (Fintype.card ι : ℝ) ≤
      ((∑ j ∈ S, Real.log ((g j).norm : ℝ))-Real.log B)/
        ((∑ j ∈ S, Real.log ((g j).norm : ℝ)/(classes z (g j)).card)-Real.log B) := by
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hh := larger_sieve_diameter_inequality z hz g S hg hc B hB
  apply (le_div_iff₀ hden).mpr
  apply (mul_le_mul_iff_of_pos_left hk).mp
  nlinarith

#print axioms collision_log_budget
#print axioms larger_sieve_distance_inequality
#print axioms larger_sieve_diameter_inequality
#print axioms larger_sieve_card_bound
end
end Erdos952Investigation.GaussianLargerSieve
