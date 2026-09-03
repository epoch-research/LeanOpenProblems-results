import Submission.FiniteTotientEnergy

/-!
# Combining disjoint finite prime supports

The collision energy is supermultiplicative on disjoint supports. A uniform
positive gain on infinitely many disjoint blocks would force divergence.
The existence of such gains for every subcritical exponent is not proved.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.FiniteEnergy

lemma output_union (P Q : Finset ℕ) (hPQ : Disjoint P Q) :
    output (P ∪ Q) = output P * output Q := Finset.prod_union hPQ

lemma sum_powerset_union_disjoint (P Q : Finset ℕ) (hPQ : Disjoint P Q)
    (f : Finset ℕ → ℝ) :
    (∑ R ∈ (P ∪ Q).powerset, f R) =
      ∑ S ∈ P.powerset, ∑ T ∈ Q.powerset, f (S ∪ T) := by
  symm
  rw [← Finset.sum_product P.powerset Q.powerset (fun U => f (U.1 ∪ U.2))]
  have hint (S T : Finset ℕ) (hS : S ⊆ P) (hT : T ⊆ Q) :
      (S ∪ T) ∩ P = S ∧ (S ∪ T) ∩ Q = T := by
    have hTP : Disjoint T P := hPQ.symm.mono_left hT
    have hSQ : Disjoint S Q := hPQ.mono_left hS
    constructor
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS,
        Finset.disjoint_iff_inter_eq_empty.mp hTP, Finset.union_empty]
    · rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hT,
        Finset.disjoint_iff_inter_eq_empty.mp hSQ, Finset.empty_union]
  refine Finset.sum_bij (fun U _ => U.1 ∪ U.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro U hU
    obtain ⟨hS, hT⟩ := Finset.mem_product.mp hU
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT))
  · intro U hU V hV he
    obtain ⟨hS, hT⟩ := Finset.mem_product.mp hU
    obtain ⟨hS', hT'⟩ := Finset.mem_product.mp hV
    have hu := hint U.1 U.2 (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)
    have hv := hint V.1 V.2 (Finset.mem_powerset.mp hS') (Finset.mem_powerset.mp hT')
    apply Prod.ext
    · exact hu.1.symm.trans ((congrArg (fun R => R ∩ P) he).trans hv.1)
    · exact hu.2.symm.trans ((congrArg (fun R => R ∩ Q) he).trans hv.2)
  · intro R hR
    refine ⟨(R ∩ P, R ∩ Q), Finset.mem_product.mpr
      ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩, ?_⟩
    change (R ∩ P) ∪ (R ∩ Q) = R
    rw [← Finset.inter_union_distrib_left]
    exact Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hR)

lemma kernel_mul_le (s : ℝ) (a b c d : ℕ) :
    kernel s a b * kernel s c d ≤ kernel s (a*c) (b*d) := by
  by_cases hab : a = b
  · subst b
    by_cases hcd : c = d
    · subst d
      simp only [kernel, ite_true, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact le_rfl
    · rw [show kernel s c d = 0 by simp [kernel, hcd], mul_zero]
      exact kernel_nonneg _ _ _
  · rw [show kernel s a b = 0 by simp [kernel, hab], zero_mul]
    exact kernel_nonneg _ _ _

/-- Collision pairs from the two disjoint input supports combine injectively.
Additional cross-support relations may make this inequality strict. -/
theorem energy_union_ge_mul (P Q : Finset ℕ) (hPQ : Disjoint P Q) (s : ℝ) :
    energy P s * energy Q s ≤ energy (P ∪ Q) s := by
  unfold energy
  rw [Finset.sum_mul_sum, sum_powerset_union_disjoint P Q hPQ]
  simp_rw [Finset.sum_mul_sum, sum_powerset_union_disjoint P Q hPQ]
  apply Finset.sum_le_sum
  intro S hS
  apply Finset.sum_le_sum
  intro T hT
  apply Finset.sum_le_sum
  intro U hU
  apply Finset.sum_le_sum
  intro V hV
  have hST : Disjoint S T := hPQ.mono
    (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)
  have hUV : Disjoint U V := hPQ.mono
    (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV)
  rw [output_union S T hST, output_union U V hUV]
  exact kernel_mul_le s _ _ _ _

lemma one_le_energy (P : Finset ℕ) (s : ℝ) : 1 ≤ energy P s := by
  have hempty : ∅ ∈ P.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  have hinner : 1 ≤ ∑ T ∈ P.powerset, kernel s (output ∅) (output T) := by
    have h := Finset.single_le_sum (fun T hT => kernel_nonneg s (output ∅) (output T)) hempty
    simpa only [output, Finset.prod_empty, kernel, ite_true, Nat.cast_one, Real.one_rpow] using h
  apply hinner.trans
  exact Finset.single_le_sum
    (fun S hS => Finset.sum_nonneg (fun T hT => kernel_nonneg s (output S) (output T))) hempty

lemma energy_union_ge_add_sub_one (P Q : Finset ℕ) (hPQ : Disjoint P Q) (s : ℝ) :
    energy P s + energy Q s - 1 ≤ energy (P ∪ Q) s := by
  have hP := one_le_energy P s
  have hQ := one_le_energy Q s
  have hmul := energy_union_ge_mul P Q hPQ s
  nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hQ)]

/-- The sum of the separate gains is at most the combined gain. There is
no uniform positive lower bound for the separate gains in this statement. -/
lemma sum_disjoint_block_gains_le (B : ℕ → Finset ℕ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (I : Finset ℕ) (s : ℝ) :
    (∑ i ∈ I, (energy (B i) s - 1)) ≤ energy (I.biUnion B) s - 1 := by
  induction I using Finset.induction_on with
  | empty => simp [energy_empty]
  | @insert i I hi ih =>
    have hdis : Disjoint (B i) (I.biUnion B) := by
      apply Finset.disjoint_left.mpr
      intro p hpi hpU
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpU
      have hij : i ≠ j := fun he => hi (he ▸ hj)
      exact Finset.disjoint_left.mp (hB hij) hpi hpj
    rw [Finset.sum_insert hi, Finset.biUnion_insert]
    have hgain := energy_union_ge_add_sub_one (B i) (I.biUnion B) hdis s
    linarith

/-- If the squarefree collision moment converges, every sequence of disjoint
prime blocks has summable energy gains. Qualitatively having a positive gain
on infinitely many fresh blocks is therefore not by itself a contradiction. -/
theorem summable_disjoint_block_gains (B : ℕ → Finset ℕ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hpr : ∀ i p, p ∈ B i → p.Prime) (s : ℝ)
    (H : Summable (fun n : ℕ => (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s)))) :
    Summable (fun i : ℕ => energy (B i) s - 1) := by
  let C := ∑' n : ℕ, (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))
  apply summable_of_sum_le (c := C-1) (fun i => sub_nonneg.mpr (one_le_energy (B i) s))
  intro I
  have hprime : ∀ p ∈ I.biUnion B, p.Prime := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact hpr i p hpi
  exact (sum_disjoint_block_gains_le B hB I s).trans
    (sub_le_sub_right (energy_le_squarefree_moment (I.biUnion B) hprime s H) 1)

lemma not_summable_moment_of_disjoint_block_gains (B : ℕ → Finset ℕ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hpr : ∀ i p, p ∈ B i → p.Prime) (s : ℝ)
    (H : ¬Summable (fun i : ℕ => energy (B i) s - 1)) :
    ¬Summable (fun n : ℕ => (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))) :=
  fun Hsum => H (summable_disjoint_block_gains B hB hpr s Hsum)

/-- A uniform gain would suffice at this exponent. Such uniform gains are
not obtained from the previously proved qualitative fresh-prime relations. -/
theorem not_summable_moment_of_uniform_disjoint_gain (B : ℕ → Finset ℕ)
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hpr : ∀ i p, p ∈ B i → p.Prime) (s δ : ℝ) (hδ : 0 < δ)
    (hgain : ∀ i, 1+δ ≤ energy (B i) s) :
    ¬Summable (fun n : ℕ => (gSquarefree n : ℝ)^2*(n : ℝ)^(-(2*s))) := by
  apply not_summable_moment_of_disjoint_block_gains B hB hpr s
  intro H
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (H.tendsto_atTop_zero.eventually_lt_const hδ)
  have h := hN N le_rfl
  linarith [hgain N]

lemma energy_singleton (p : ℕ) (hp : 2 < p) (s : ℝ) :
    energy {p} s = 1 + ((p-1 : ℕ) : ℝ)^(-(2*s)) := by
  have hc : correlation ∅ (p-1) s = 0 := by
    simp [correlation, output, show ¬1 = p-1 by omega]
  simpa only [Finset.insert_empty, energy_empty, hc, mul_one, mul_zero, add_zero]
    using energy_insert ∅ p (Finset.notMem_empty _) (by omega) s

/-- Actual singleton prime blocks have strictly positive gains, but these
gains are summable above one half. This does not address larger blocks that
contain genuinely distinct colliding inputs. -/
lemma summable_singleton_prime_gains (s : ℝ) (hs : 1/2 < s) :
    Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => energy {p.val} s - 1) := by
  have H := (summable_totient_neg_rpow (2*s) (by linarith)).subtype
    (fun p : ℕ => p.Prime ∧ 2 < p)
  apply H.congr
  intro p
  simp only [Function.comp_apply]
  rw [energy_singleton p.val p.property.2 s, Nat.totient_prime p.property.1]
  ring

lemma singleton_prime_gain_pos (p : ℕ) (hp : 2 < p) (s : ℝ) :
    0 < energy {p} s - 1 := by
  rw [energy_singleton p hp s]
  have hpos : (0 : ℝ) < (p-1 : ℕ) := by exact_mod_cast (show 0 < p-1 by omega)
  linarith [Real.rpow_pos_of_pos hpos (-(2*s))]

end Erdos821.FiniteEnergy
