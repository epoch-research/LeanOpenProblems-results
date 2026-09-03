import Submission.Shared47TernaryArithmetic

/-! CRT realization of the finite shared-prefix obstruction. No arbitrary
ternary exponent or unbounded-prime obstruction is asserted. -/
namespace Erdos7Shared47Arithmetic
open scoped BigOperators
open Erdos7Shared47DistinctBoxes Erdos7Shared47TernaryArithmetic
open Erdos7TernaryTwoRootEmbedding Erdos7TernaryTwoCoherentMixture
open Erdos7CompleteFamilyModel Erdos7Reduction Erdos7StarSieve
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

def caps (D : ℕ) (F : Fin 12 → ℕ) : Fin 14 → ℕ :=
  Fin.cases 2 (Fin.cases (D+1) F)

/-- Ternary exponents at most two and arbitrary finite later exponents. -/
theorem prime_product_not_cover {κ : Type} [Fintype κ]
    (D : ℕ) (F : Fin 12 → ℕ) (e : κ → Fin 14 → ℕ) (he : Function.Injective e)
    (he0 : ∀ k,∃ i,e k i≠0) (heE : ∀ k i,e k i≤caps D F i) (a : κ → ℤ) :
    ¬ (∀ z : ℤ,∃ k,((∏ i,primes i^e k i:ℕ):ℤ) ∣ z-a k) := by
  classical
  intro hcover
  let E := caps D F
  letI (i : Fin 14) : NeZero (primes i) := ⟨by have := primes_gt_one i; omega⟩
  let A (i : Fin 14) := ZMod (primes i^E i)
  let f (k : κ) (i : Fin 14) := ZMod.castHom (pow_dvd_pow (primes i) (heE k i))
    (ZMod (primes i^e k i))
  let B (k : κ) (i : Fin 14) : Finset (A i) :=
    Finset.univ.filter (fun x => f k i x = (a k:ZMod (primes i^e k i)))
  let ρ (i : Fin 14) (_ : A i) : ℝ := 1/Fintype.card (A i)
  have hρ (i : Fin 14) (x : A i) : 0 ≤ ρ i x := by dsimp only [ρ]; positivity
  have hρmass (i : Fin 14) : (∑ y,ρ i y) = 1 := by
    simp only [ρ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hn : (Fintype.card (A i):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    field_simp
  have hd (k : κ) (i : Fin 14) (_ : e k i ≠ 0) :
      (∑ y,if y ∈ B k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (primes i) (heE k i))) (a k)
    change ((B k i).card:ℚ) = _ at hh
    have hreal : ((B k i).card:ℝ) = (Fintype.card (A i):ℝ)/(primes i:ℝ)^(e k i) := by
      have hh' : ((B k i).card:ℚ) = (Fintype.card (A i):ℚ)/(primes i:ℚ)^(e k i) := by
        simpa only [A,ZMod.card,Nat.cast_pow] using hh
      have hcast := congrArg (fun q : ℚ => (q:ℝ)) hh'
      simpa only [Rat.cast_natCast,Rat.cast_div,Rat.cast_pow] using hcast
    have hn : (Fintype.card (A i):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    simp only [ρ,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,hreal]
    exact (by field_simp :
      (Fintype.card (A i):ℝ)/(primes i:ℝ)^(e k i)*(1/Fintype.card (A i)) =
        1/(primes i:ℝ)^(e k i)).le
  let a3 := pureResidue e a 1
  let a9 := pureResidue e a 2
  let ξ (x : Fin 5) : ∀ i,A i := Fin.cases (motive := A)
    ((point (residue3 a3) (residue9 a9) x).val : A 0) (fun _ => 0)
  have hmem (k : κ) (x : Fin 5) : ξ x 0∈B k 0 ↔
      ((point (residue3 a3) (residue9 a9) x).val : ZMod (3^e k 0))=(a k : ZMod (3^e k 0)) := by
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and,ξ,Fin.cases_zero,f,map_natCast]
  have havoid : ∀ k,(∀ i : Fin 14, 1 ≤ i.val → e k i=0) → ∀ x,ξ x 0∉B k 0 := by
    intro k hk x hm
    have hpure := eq_pure (e k) hk
    have hk0 : e k 0≠0 := by
      intro hz
      obtain ⟨i,hi⟩ := he0 k
      by_cases hi0 : i=0
      · exact hi (hi0 ▸ hz)
      · exact hi (hk i (by have hn : i.val≠0 := fun h => hi0 (Fin.ext h); omega))
    have hkle : e k 0≤2 := heE k 0
    rcases (show e k 0=1 ∨ e k 0=2 by omega) with h1|h2
    · have ha : a3=a k := pureResidue_eq e he a k 1 (by simpa only [h1] using hpure)
      have hh := (hmem k x).mp hm
      rw [h1] at hh
      exact (point_avoids_cast a3 a9 x).1 (hh.trans (congrArg (fun z : ℤ => (z : ZMod 3)) ha.symm))
    · have ha : a9=a k := pureResidue_eq e he a k 2 (by simpa only [h2] using hpure)
      have hh := (hmem k x).mp hm
      rw [h2] at hh
      exact (point_avoids_cast a3 a9 x).2 (hh.trans (congrArg (fun z : ℤ => (z : ZMod 9)) ha.symm))
  have hbranch : ∀ k,e k 0=1 → ∃ q : Fin 2,∀ x,ξ x 0∈B k 0 → branch x=q := by
    intro k hk
    obtain ⟨q,hq⟩ := point_branch_cast a3 a9 (a k)
    refine ⟨q,fun x hx => hq x ?_⟩
    have hh := (hmem k x).mp hx
    rw [hk] at hh
    exact hh
  have hpoint : ∀ k,e k 0=2 → ∃ y : Fin 5,∀ x,ξ x 0∈B k 0 → x=y := by
    intro k hk
    obtain ⟨y,hy⟩ := point_cell_cast a3 a9 (a k)
    refine ⟨y,fun x hx => hy x ?_⟩
    have hh := (hmem k x).mp hx
    rw [hk] at hh
    exact hh
  apply Erdos7Shared47DistinctBoxes.not_cover A E D rfl rfl e he heE he0 B ξ havoid hbranch hpoint ρ hρ hρmass hd
  intro x
  let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => primes i^E i) Finset.univ
    (fun i _ => pow_ne_zero _ (NeZero.ne _))
    (fun i _ j _ hij => (primes_coprime hij).pow _ _)
  have hz (i : Fin 14) : (z.val:A i) = x i := by
    rw [← ZMod.natCast_zmod_val (x i)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  obtain ⟨k,hk⟩ := hcover (z.val:ℤ)
  refine ⟨k,fun i _ => ?_⟩
  have hpi : primes i^e k i ∣ ∏ j,primes j^e k j :=
    Finset.dvd_prod_of_mem (fun j => primes j^e k j) (Finset.mem_univ i)
  have hpi' : ((primes i^e k i:ℕ):ℤ) ∣ ((∏ j,primes j^e k j:ℕ):ℤ) := by exact_mod_cast hpi
  have hqi := hpi'.trans hk
  simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← hz i,map_natCast]
  symm
  simpa only [Int.cast_natCast] using
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val:ℤ) (primes i^e k i)).mpr hqi


#print axioms prime_product_not_cover
end Erdos7Shared47Arithmetic
