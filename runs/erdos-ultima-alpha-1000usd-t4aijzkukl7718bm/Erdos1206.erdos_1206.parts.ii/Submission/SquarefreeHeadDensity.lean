import Submission.GeneralBoxDensityLimits
import Submission.QuantitativeParameterSieve
import Submission.QuadraticConditionalCounts
import Submission.SquarefreePrimeParameterSieve

/-! Squarefree parameters retain a fixed positive proportion of every finite
prime-unit head. The proportionality constant is independent of that head. -/
namespace Erdos1206.SquarefreeHeadDensity
open Finset Filter QuadraticSquarefreeSieve QuadraticRootLattice QuadraticConditionalCounts
  QuadraticSquareLocal BoxDensityLimits
open scoped Classical
set_option maxHeartbeats 2000000

lemma test_of_mem (a b c : Fin 4 → ℕ) {B : Set ℕ} {p : ℕ} (hpB : p∈B) (x : ℕ × ℕ) :
    test a b c B p x ↔ ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2 := by
  constructor
  · intro h i
    exact (h i).2 hpB
  · intro h i
    exact ⟨fun hd => h i ((dvd_pow_self p (by decide : 2≠0)).trans hd),fun _ => h i⟩

lemma residues_of_not_mem (a b c : Fin 4 → ℕ) {B : Set ℕ} {p : ℕ} (hpB : p∉B) :
    residues a b c B p=residues a b c ∅ p := by
  unfold residues
  split_ifs
  · congr 1
    funext x
    simp only [test,hpB,Set.notMem_empty,IsEmpty.forall_iff,and_true]
  · rfl

lemma local_density_of_mem (a b c : Fin 4 → ℕ) {B : Set ℕ} {p : ℕ}
    (hp : p.Prime) (hpB : p∈B) :
    CoprimeBoxCRT.localDensity (fun p => p^2) (residues a b c B) p=
      headDensity a b c {p} := by
  have hpos : ∀ q∈({p} : Finset ℕ), 0 < q^2 := by
    intro q hq
    simpa only [mem_singleton.mp hq] using pow_pos hp.pos 2
  have hcop : (↑({p} : Finset ℕ) : Set ℕ).Pairwise (fun q r => (q^2).Coprime (r^2)) := by
    intro q hq r hr hqr
    exact (hqr ((mem_singleton.mp hq).trans (mem_singleton.mp hr).symm)).elim
  have ht := GeneralBoxDensityLimits.joint_positive_density (fun q => q^2) {p} hpos hcop
    (residues a b c B)
  simp only [prod_singleton] at ht
  have heq (N : ℕ) : positiveBox N (fun x =>
      ∀ q∈({p} : Finset ℕ), ((x.1:ZMod (q^2)),(x.2:ZMod (q^2)))∈residues a b c B q)=
        positiveBox N (Head a b c {p}) := by
    ext x
    simp only [positiveBox,mem_filter]
    rw [show Head a b c {p} x ↔ ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2 from by
      simpa using mem_head a b c {p}
        (fun q hq => (mem_singleton.mp hq) ▸ hp) x]
    simp only [mem_singleton,forall_eq,mem_residues_nat a b c B hp,
      test_of_mem a b c hpB]
  simp only [heq] at ht
  exact tendsto_nhds_unique ht (head_tendsto a b c {p} (fun q hq => (mem_singleton.mp hq) ▸ hp))

noncomputable def squarefreeBox (a b c : Fin 4 → ℕ) (S : Finset ℕ) (N : ℕ) : Finset (ℕ × ℕ) :=
  positiveBox N (fun x => Head a b c S x ∧ ∀ i, Squarefree (quad (a i) (b i) (c i) x.1 x.2))

lemma mem_squarefreeBox (a b c : Fin 4 → ℕ) (S : Finset ℕ) (N : ℕ) (x : ℕ × ℕ) :
    x∈squarefreeBox a b c S N ↔ x∈range N ×ˢ range N ∧ 0 < x.1 ∧
      Head a b c S x ∧ ∀ i, Squarefree (quad (a i) (b i) (c i) x.1 x.2) := by
  simp only [squarefreeBox,positiveBox,mem_filter]

lemma squarefreeBox_subset (a b c : Fin 4 → ℕ) (S : Finset ℕ) (N : ℕ) :
    squarefreeBox a b c S N ⊆ positiveBox N (Head a b c S) := by
  intro x hx
  obtain ⟨hxN,hxp,hxH,_⟩ := (mem_squarefreeBox _ _ _ _ _ _).mp hx
  exact mem_filter.mpr ⟨hxN,hxp,hxH⟩

lemma good_eq_squarefreeBox (a b c : Fin 4 → ℕ) (S : Finset ℕ)
    (hS : ∀ p∈S, p.Prime) (N : ℕ) :
    PeriodicParameterSieve.good (fun p => p^2) (residues a b c (S : Set ℕ)) N=
      squarefreeBox a b c S N := by
  ext x
  simp only [PeriodicParameterSieve.good,mem_filter,mem_squarefreeBox]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h
    constructor
    · apply (mem_head a b c S hS x).mpr
      intro p hp i
      exact ((mem_residues_nat a b c (S : Set ℕ) (hS p hp) x).mp (h p (hS p hp)) i).2 hp
    · intro i
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hd
      exact ((mem_residues_nat a b c (S : Set ℕ) hp x).mp (h p hp) i).1
        (by simpa only [pow_two] using hd)
  · rintro ⟨hH,hsf⟩ p hp
    apply (mem_residues_nat a b c (S : Set ℕ) hp x).mpr
    intro i
    refine ⟨?_,?_⟩
    · simpa only [pow_two] using Nat.squarefree_iff_prime_squarefree.mp (hsf i) p hp
    · intro hpS
      exact (mem_head a b c S hS x).mp hH p hpS i

/-- A single positive constant works for every finite head, although the
cutoff in N may depend on the head. No root-density assertion is made. -/
theorem relative_density (a b c : Fin 4 → ℕ)
    (ha : ∀ i, 0 < a i) (hc : ∀ i, 0 < c i)
    (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i)≠0)
    (hloc : ∀ p, p.Prime → ∃ x : ℕ × ℕ,
      ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ S : Finset ℕ, (∀ p∈S, p.Prime) →
      ∀ᶠ N : ℕ in atTop, γ*headDensity a b c S*(N:ℝ)^2 ≤ (squarefreeBox a b c S N).card := by
  obtain ⟨γ,hγ,hγprod⟩ := SquarefreePrimeParameterSieve.product_lower a b c ∅ ha hQ hdisc
    (by simp only [Set.notMem_empty,if_false]; exact summable_zero) hloc
  refine ⟨γ/2,by positivity,fun S hS => ?_⟩
  let u (p : ℕ) : ℝ := headDensity a b c {p}
  let f (p : ℕ) : ℝ := CoprimeBoxCRT.localDensity (fun p => p^2) (residues a b c (S : Set ℕ)) p
  have hu (p : ℕ) (hp : p∈S) : 0 ≤ u p ∧ u p ≤ 1 := by
    refine ⟨(head_density_pos a b c {p} (fun q hq => (mem_singleton.mp hq) ▸ hS p hp) hQ hloc).le,?_⟩
    have hh := QuadraticSquareLocal.density_bounds a b c (S : Set ℕ) ha hQ hdisc (hS p hp) (hloc p (hS p hp))
    rw [local_density_of_mem a b c (B := (S : Set ℕ)) (hS p hp) hp] at hh
    exact hh.2.1
  have hhead : (∏p∈S,u p)=headDensity a b c S := by simp only [u,headDensity,prod_singleton]
  have hheadpos : 0 < headDensity a b c S := head_density_pos a b c S hS hQ hloc
  have hprod (T : Finset ℕ) (hT : ∀ p∈T, p.Prime) :
      γ*headDensity a b c S ≤ ∏p∈T,f p := by
    have hleft : headDensity a b c S ≤ ∏p∈T∩S,f p := by
      have heq : (∏p∈T∩S,f p)=∏p∈S∩T,u p := by
        rw [inter_comm T S]
        apply prod_congr rfl
        intro p hp
        exact local_density_of_mem a b c (B := (S : Set ℕ)) (hS p (mem_inter.mp hp).1) (mem_inter.mp hp).1
      rw [heq,←hhead,←prod_inter_mul_prod_diff S T u]
      have hrem : (∏p∈S\T,u p) ≤ 1 := prod_le_one
        (fun p hp => (hu p (mem_sdiff.mp hp).1).1) (fun p hp => (hu p (mem_sdiff.mp hp).1).2)
      exact mul_le_of_le_one_right (prod_nonneg (fun p hp => (hu p (mem_inter.mp hp).1).1)) hrem
    have hright : γ ≤ ∏p∈T\S,f p := by
      convert hγprod (T\S) (fun p hp => hT p (mem_sdiff.mp hp).1) using 1
      apply prod_congr rfl
      intro p hp
      dsimp only [f,CoprimeBoxCRT.localDensity]
      rw [residues_of_not_mem a b c (B := (S : Set ℕ)) (mem_sdiff.mp hp).2]
    rw [←prod_inter_mul_prod_diff T S f]
    calc
      γ*headDensity a b c S = headDensity a b c S*γ := mul_comm _ _
      _ ≤ _ := mul_le_mul hleft hright hγ.le (hheadpos.le.trans hleft)
  have hs : Summable (fun p : ℕ => if p∈(S : Set ℕ) then (1:ℝ)/p else 0) := by
    apply summable_of_ne_finset_zero (s := S)
    intro p hp
    exact if_neg hp
  have hh := QuantitativeParameterSieve.density_of_product_lower (fun p => p^2)
    (residues a b c (S : Set ℕ)) (fun p hp => pow_pos hp.pos _)
    (fun p q hp hq hpq => Nat.coprime_pow_primes 2 2 hp hq hpq)
    (γ*headDensity a b c S) (mul_pos hγ hheadpos) hprod
    (fun ε hε => SquarefreePrimeParameterSieve.uniform_tail a b c (S : Set ℕ)
      ha hc hQ hdisc hS (by
        convert hs using 1
        funext p
        split_ifs <;> rfl) hε)
  filter_upwards [hh] with N hN
  rw [good_eq_squarefreeBox a b c S hS N] at hN
  convert hN using 1; ring

#print axioms relative_density
end Erdos1206.SquarefreeHeadDensity
