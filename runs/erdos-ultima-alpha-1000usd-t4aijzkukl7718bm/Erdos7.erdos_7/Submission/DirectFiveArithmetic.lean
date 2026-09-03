import Submission.DirectFiveHoleMeasure
import Submission.FourExceptionPrimes
import Submission.DirectFiveWeight

/-! Arithmetic specialization of the stronger prime-dependent hole law. -/
namespace Erdos7DirectFiveArithmetic
open scoped BigOperators
open Erdos7Reduction Erdos7Compression Erdos7Distortion Erdos7StarSieve Erdos7CompressionSieve
open Erdos7DirectFiveScalar (cap cap_bounds primes)
open Erdos7DirectFiveWeight
open Erdos7WeightedExceptionArithmetic (schedule_product)
set_option maxHeartbeats 6000000

lemma schedule_weight {n : ℕ} (p : Fin n → ℕ) (hinj : Function.Injective p)
    (d : ℕ) (hd : d≠0) (hcover : ∀ q∈d.primeFactors, ∃ i, p i=q) :
    (∏ i∈expSupport (fun i => d.factorization (p i)),
      cap (p i)*((p i : ℚ)⁻¹)^d.factorization (p i)) = weight d := by
  classical
  rw [weight_eq_product d hd]
  have hmem (i : Fin n) : i∈expSupport (fun i => d.factorization (p i)) ↔ p i∈d.primeFactors := by
    rw [mem_expSupport,← Nat.support_factorization,Finsupp.mem_support_iff]
  apply Finset.prod_bij (fun i _ => p i)
  · intro i hi; exact (hmem i).mp hi
  · intro i hi j hj hij; exact hinj hij
  · intro q hq
    obtain ⟨i,hi⟩ := hcover q hq
    exact ⟨i,(hmem i).mpr (hi ▸ hq),hi⟩
  · intro i hi
    simp only [div_eq_mul_inv,inv_pow]

/-- All exponent caps and all exceptional exponent vectors are arbitrary. -/
theorem not_coordinate_cover_weighted {n : ℕ} {κ J : Type*} [Fintype κ] [Fintype J]
    (hn : 366 ≤ n) (p E : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    (g : J → Fin n → ℕ) (hgE : ∀ j i, g j i≤E i) (b : J → ℤ)
    (hE₀ : 1 ≤ E (Fin.castLE hn (0 : Fin 366))) (c₀ : ℤ)
    (hweight : (∑ j, ∏ i∈expSupport (g j), cap (p i)*((p i : ℚ)⁻¹)^(g j i)) ≤ 1/2) :
    ¬ (∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨ (5 : ℤ) ∣ x-c₀ ∨
      (∃ j, ((∏ i, p i ^ g j i : ℕ) : ℤ) ∣ x-b j)) := by
  classical
  intro hcover
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hmono.injective h))
  letI (i : Fin n) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let X (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x=(a k : ZMod (p i ^ e k i)))
  let f₀ (j : J) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (hgE j i)) (ZMod (p i ^ g j i))
  let Y (j : J) (i : Fin n) := Finset.univ.filter (fun x : A i => f₀ j i x=(b j : ZMod (p i ^ g j i)))
  have hXcard (k : κ) (i : Fin n) : ((X k i).card : ℚ) ≤
      (Fintype.card (A i) : ℚ)*((p i : ℚ)⁻¹)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (heE k i))) (a k)
    change ((X k i).card : ℚ) = _ at hh
    rw [hh]
    simp only [A,ZMod.card,Nat.cast_pow,div_eq_mul_inv,inv_pow]
    exact le_rfl
  have hX0 (k : κ) (i : Fin n) (hi : e k i=0) : X k i=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    simp only [X,Finset.mem_filter,Finset.mem_univ,true_and]
    have hsub : ∀ u v : ZMod (p i ^ e k i), u=v := by
      rw [hi,pow_zero]
      exact fun u v => Subsingleton.elim u v
    exact hsub _ _
  have hY (j : J) (i : Fin n) : fraction (Y j i) ≤ ((p i : ℚ)⁻¹)^(g j i) := by
    have hh := surjective_fiber_card_rat (f₀ j i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p i) (hgE j i))) (b j : ZMod (p i ^ g j i))
    change ((Y j i).card : ℚ) = _ at hh
    unfold fraction
    rw [hh]
    simp only [ZMod.card,Nat.cast_pow]
    have hcard : (Fintype.card (A i) : ℚ)≠0 := ne_of_gt card_pos_rat
    have hp0 : (p i : ℚ)≠0 := by exact_mod_cast (hp i).1.ne_zero
    apply le_of_eq
    rw [inv_pow]
    field_simp
    simp only [A,ZMod.card]
    simp only [A,ZMod.card,Nat.cast_pow]
  let j₀ : Fin n := Fin.castLE hn (0 : Fin 366)
  have hp₀ : p j₀=5 := hpre 0
  have hdiv : 5 ∣ p j₀^E j₀ := by
    rw [hp₀]
    simpa only [pow_one] using pow_dvd_pow 5 hE₀
  let fPure := ZMod.castHom hdiv (ZMod 5)
  let Y₀ := Finset.univ.filter (fun x : A j₀ => fPure x=(c₀ : ZMod 5))
  have hY₀ : fraction Y₀ ≤ (1/5 : ℚ) := by
    have hh := surjective_fiber_card_rat fPure.toAddMonoidHom (ZMod.castHom_surjective hdiv) (c₀ : ZMod 5)
    change ((Y₀.card : ℚ)) = _ at hh
    norm_num only [ZMod.card] at hh
    unfold fraction
    rw [hh]
    have hnz : (Fintype.card (A j₀) : ℚ)≠0 := ne_of_gt card_pos_rat
    apply le_of_eq
    field_simp
    simp only [A,ZMod.card]
  apply Erdos7DirectFiveHoleMeasure.not_cover_with_weighted_boxes hn A p E hp hmono hpre e hei he0 heE X hX0 hXcard Y₀ hY₀
    (fun j => expSupport (g j)) Y
  · apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hweight
    exact Finset.prod_le_prod (fun i _ => mul_nonneg (by have := (cap_bounds (p i)).1; linarith) (fraction_nonneg _))
      (fun i _ => mul_le_mul_of_nonneg_left (hY j i) (by have := (cap_bounds (p i)).1; linarith))
  intro x
  let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
    (fun i _ => pow_ne_zero _ (NeZero.ne _))
    (fun i _ j _ hij => (hcop hij).pow _ _)
  have hz (i : Fin n) : (z.val : A i)=x i := by
    rw [← ZMod.natCast_zmod_val (x i)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  rcases hcover (z.val : ℤ) with ⟨k,hk⟩ | hpure | hk
  · left
    refine ⟨k,fun i => ?_⟩
    have hpi : p i ^ e k i ∣ ∏ j, p j ^ e k j :=
      Finset.dvd_prod_of_mem (fun j => p j ^ e k j) (Finset.mem_univ i)
    have hpi' : ((p i ^ e k i : ℕ) : ℤ) ∣ ((∏ j, p j ^ e k j : ℕ) : ℤ) := by exact_mod_cast hpi
    have hqi := hpi'.trans hk
    simp only [X,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hz i,map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val : ℤ) (p i ^ e k i)).mpr hqi
  · right; left
    change x j₀∈Y₀
    simp only [Y₀,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hz j₀,map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub c₀ (z.val : ℤ) 5).mpr hpure
  · obtain ⟨j,hj⟩ := hk
    right; right
    refine ⟨j,fun i _ => ?_⟩
    have hpi : p i ^ g j i ∣ ∏ l, p l ^ g j l :=
      Finset.dvd_prod_of_mem (fun l => p l ^ g j l) (Finset.mem_univ i)
    have hh := (Int.natCast_dvd_natCast.mpr hpi).trans hj
    simp only [Y,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hz i,map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (b j) (z.val : ℤ) (p i^g j i)).mpr hh

lemma prime_factor_ge_five (d : ℕ) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (q : ℕ) (hq : q∈d.primeFactors) : q.Prime ∧ 5≤q := by
  have hh := Nat.mem_primeFactors.mp hq
  have hqo := ho.of_dvd_nat hh.2.1
  have hne : q≠3 := by intro h; exact h3 (h ▸ hh.2.1)
  have htwo := hh.1.two_le
  refine ⟨hh.1,?_⟩
  obtain ⟨k,hk⟩ := hqo
  omega

/-- No cardinality or injectivity assumption is imposed on the exceptional
family. It may include modulus1; the weight condition then cannot hold. -/
theorem not_cover_with_weighted_exceptions {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (c₀ : ℤ) (hd : ∀ j, 0 < d j ∧ Odd (d j))
    (hd3 : ∀ j, ¬ 3 ∣ d j) (hweight : (∑ j, weight (d j)) ≤ 1/2) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (5 : ℤ) ∣ x-c₀ ∨ ∃ j, (d j : ℤ) ∣ x-b j) := by
  classical
  intro hcover
  let P := (Finset.univ.biUnion (fun i => (m i).primeFactors)) ∪
    (Finset.univ.biUnion (fun j => (d j).primeFactors))
  have hP : ∀ q∈P, q.Prime ∧ 5≤q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hq
      exact prime_factor_ge_five (m i) (hm i).2 (h3 i) q hi
    · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hq
      exact prime_factor_ge_five (d j) (hd j).2 (hd3 j) q hj
  obtain ⟨n,hn,p,hp,hmono,hpre,hcovers⟩ := Erdos7FourExceptionPrimes.padded_primes P hP
  let e (k : I) (i : Fin n) := (m k).factorization (p i)
  let g (j : J) (i : Fin n) := (d j).factorization (p i)
  let E (i : Fin n) := max 1 (max (Finset.univ.sup (fun k => e k i)) (Finset.univ.sup (fun j => g j i)))
  have hmcover (k : I) : ∀ q∈(m k).primeFactors, ∃ i, p i=q := by
    intro q hq
    exact hcovers q (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hq⟩))
  have hdcover (j : J) : ∀ q∈(d j).primeFactors, ∃ i, p i=q := by
    intro q hq
    exact hcovers q (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hq⟩))
  have hmprod (k : I) : m k=∏ i,p i^e k i :=
    schedule_product p hmono.injective (m k) (by have := (hm k).1; omega) (hmcover k)
  have hdprod (j : J) : d j=∏ i,p i^g j i :=
    schedule_product p hmono.injective (d j) (by have := (hd j).1; omega) (hdcover j)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hinj
    rw [hmprod k,hmprod l,hkl]
  have he0 (k : I) : ∃ i, e k i≠0 := by
    by_contra! hz
    have hh := (hm k).1
    rw [hmprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  have heE (k : I) (i : Fin n) : e k i≤E i :=
    (Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hgE (j : J) (i : Fin n) : g j i≤E i :=
    (Finset.le_sup (f := fun j => g j i) (Finset.mem_univ j)).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hw : (∑ j, ∏ i∈expSupport (g j), cap (p i)*((p i : ℚ)⁻¹)^(g j i)) ≤ 1/2 := by
    apply le_trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))) hweight
    exact schedule_weight p hmono.injective (d j) (by have := (hd j).1; omega) (hdcover j)
  apply not_coordinate_cover_weighted hn p E hp hmono hpre e hei he0 heE a g hgE b (le_max_left _ _) c₀ hw
  intro x
  rcases hcover x with ⟨k,hk⟩ | hh | ⟨j,hj⟩
  · exact Or.inl ⟨k,by simpa only [← hmprod] using hk⟩
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr ⟨j,by simpa only [← hdprod] using hj⟩)



#print axioms not_cover_with_weighted_exceptions
end Erdos7DirectFiveArithmetic
