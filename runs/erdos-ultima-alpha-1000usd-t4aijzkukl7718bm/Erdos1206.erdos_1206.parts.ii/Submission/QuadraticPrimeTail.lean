import Submission.QuadraticPrimeDivisibility

/-!
Uniform tail control for reciprocally summable forbidden prime sets, evaluated
on a fixed irreducible binary quadratic form. Auxiliary, not a settlement.
-/
namespace Erdos1206.QuadraticPrimeTail
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticPrimeDivisibility
open scoped Classical
set_option maxHeartbeats 1000000

lemma finite_prime_union_bound {a b c : ℤ} (hQ : Anisotropic a b c)
    (N : ℕ) (P : Finset ℕ) (hP : ∀ p∈P, p.Prime) :
    ((P.biUnion (points a b c N)).card:ℝ) ≤
      (48:ℝ)*mass a b c*(N:ℝ)^2*∑p∈P,1/(p:ℝ) := by
  have hloc (p : ℕ) (hp : p∈P) : ((points a b c N p).card:ℝ) ≤
      (48:ℝ)*mass a b c*(N:ℝ)^2*(1/(p:ℝ)) := by
    have hpR : (0:ℝ) < p := by exact_mod_cast (hP p hp).pos
    rw [mul_one_div]
    apply (le_div_iff₀ hpR).mpr
    have hh := prime_divisibility_bound hQ N p (hP p hp)
    have hhR : (p:ℝ)*(points a b c N p).card ≤
        (48:ℝ)*mass a b c*(N:ℝ)^2 := by exact_mod_cast hh
    simpa only [mul_comm] using hhR
  calc
    _ ≤ ∑p∈P,((points a b c N p).card:ℝ) := by
      exact_mod_cast (card_biUnion_le : (P.biUnion (points a b c N)).card ≤
        ∑p∈P,(points a b c N p).card)
    _ ≤ ∑p∈P,(48:ℝ)*mass a b c*(N:ℝ)^2*(1/(p:ℝ)) := sum_le_sum hloc
    _ = _ := (mul_sum _ _ _).symm

noncomputable def badTail (a b c : ℤ) (B : Set ℕ) (H N : ℕ) : Finset Vec :=
  (QuadraticLatticeLines.box N).filter (fun x => x ≠ 0 ∧
    ∃ p∈B, H < p ∧ (p:ℤ) ∣ form a b c x)

/-- A summable prime set has a uniformly negligible tail in quadratic
parameter boxes. The cutoff is independent of the box size. -/
theorem uniform_prime_tail {a b c : ℤ} (hQ : Anisotropic a b c)
    (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, ∀ N : ℕ, ((badTail a b c B H N).card:ℝ) ≤ ε*(N:ℝ)^2 := by
  have hC : (0:ℝ) < 48*mass a b c := by
    have hh : (0:ℝ) < mass a b c := by exact_mod_cast mass_pos a b c
    positivity
  obtain ⟨S,hS⟩ := summable_iff_vanishing_norm.mp hs _ (div_pos hε hC)
  let H := S.sup id
  refine ⟨H,fun N => ?_⟩
  let P := (range (mass a b c*N^2+1)).filter (fun p => p∈B ∧ H < p)
  have hP : ∀ p∈P, p.Prime := fun p hp => hB p (mem_filter.mp hp).2.1
  have hdis : Disjoint P S := by
    apply disjoint_left.mpr
    intro p hp hpS
    have hlow : p ≤ H := le_sup (f := id) hpS
    have hhigh : H < p := (mem_filter.mp hp).2.2
    omega
  have hsum : (∑p∈P,if p∈B then (1:ℝ)/p else 0)=∑p∈P,(1:ℝ)/p := by
    apply sum_congr rfl
    intro p hp
    exact if_pos (mem_filter.mp hp).2.1
  have hmass : (∑p∈P,(1:ℝ)/p) ≤ ε/(48*mass a b c) := by
    have hh := hS P hdis
    rw [hsum,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg (fun p _ => by positivity))] at hh
    exact hh.le
  have hcover : badTail a b c B H N ⊆ P.biUnion (points a b c N) := by
    intro x hx
    obtain ⟨hxbox,hxne,p,hpB,hpH,hpdiv⟩ := mem_filter.mp hx
    have hxpoint : x∈points a b c N p := mem_filter.mpr ⟨hxbox,hxne,hpdiv⟩
    have hpbound := prime_le_height hQ hxpoint
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_range.mpr (by omega),hpB,hpH⟩,hxpoint⟩
  calc
    ((badTail a b c B H N).card:ℝ) ≤ (P.biUnion (points a b c N)).card := by
      exact_mod_cast card_le_card hcover
    _ ≤ (48:ℝ)*mass a b c*(N:ℝ)^2*∑p∈P,1/(p:ℝ) := finite_prime_union_bound hQ N P hP
    _ ≤ (48:ℝ)*mass a b c*(N:ℝ)^2*(ε/(48*mass a b c)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = ε*(N:ℝ)^2 := by
      have hm : (mass a b c:ℝ) ≠ 0 := by exact_mod_cast (mass_pos a b c).ne'
      field_simp [hm]

#print axioms finite_prime_union_bound
#print axioms uniform_prime_tail
end Erdos1206.QuadraticPrimeTail
