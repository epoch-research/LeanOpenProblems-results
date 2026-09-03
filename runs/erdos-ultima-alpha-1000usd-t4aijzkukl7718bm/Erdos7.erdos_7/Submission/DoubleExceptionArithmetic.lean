import Submission.DoubleExceptionBox

/-!
# Arithmetic specialization of the two-exception no-3 sieve

A padded prime schedule supplies the certified ninety-four-prime prefix.
-/
namespace Erdos7DoubleExceptionArithmetic
open scoped BigOperators
open Erdos7Reduction Erdos7Compression Erdos7Distortion Erdos7StarSieve
open Erdos7DoubleExceptionScalar Erdos7DoubleExceptionHybrid
set_option maxHeartbeats 6000000

/-- CRT specialization, allowing two extra classes at any used primes. -/
theorem not_coordinate_cover_two_exceptions {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 94 ≤ n) (p E : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    (i₀ : Fin 2 → Fin n) (hE0 : ∀ j, 1 ≤ E (i₀ j)) (b : Fin 2 → ℤ) :
    ¬ (∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      (∃ j, (p (i₀ j) : ℤ) ∣ x-b j)) := by
  classical
  intro hcover
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hmono.injective h))
  letI (i : Fin n) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let X (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x=(a k : ZMod (p i ^ e k i)))
  let f₀ (j : Fin 2) := ZMod.castHom (pow_dvd_pow (p (i₀ j)) (hE0 j)) (ZMod (p (i₀ j) ^ 1))
  let Y (j : Fin 2) := Finset.univ.filter (fun x : A (i₀ j) => f₀ j x=(b j : ZMod (p (i₀ j) ^ 1)))
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
  have hY (j : Fin 2) : fraction (Y j) ≤ 1/(p (i₀ j) : ℚ) := by
    have hh := surjective_fiber_card_rat (f₀ j).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (p (i₀ j)) (hE0 j))) (b j : ZMod (p (i₀ j) ^ 1))
    change ((Y j).card : ℚ) = _ at hh
    unfold fraction
    rw [hh]
    simp only [ZMod.card,pow_one]
    have hcard : (Fintype.card (A (i₀ j)) : ℚ)≠0 := ne_of_gt card_pos_rat
    have hp0 : (p (i₀ j) : ℚ)≠0 := by exact_mod_cast (hp (i₀ j)).1.ne_zero
    apply le_of_eq
    field_simp
    simp only [A,ZMod.card]
  apply Erdos7DoubleExceptionBox.not_cover_with_two_exceptions hn A p E hp hmono hpre e hei he0 heE X hX0 hXcard i₀ Y hY
  intro x
  let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
    (fun i _ => pow_ne_zero _ (NeZero.ne _))
    (fun i _ j _ hij => (hcop hij).pow _ _)
  have hz (i : Fin n) : (z.val : A i)=x i := by
    rw [← ZMod.natCast_zmod_val (x i)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  rcases hcover (z.val : ℤ) with ⟨k,hk⟩ | hk
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
  · obtain ⟨j,hj⟩ := hk
    right
    refine ⟨j,?_⟩
    simp only [Y,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← hz (i₀ j),map_natCast]
    symm
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (b j) (z.val : ℤ) (p (i₀ j)^1)).mpr
        (by simpa only [pow_one] using hj)

lemma small_primes_complete : ∀ q : Fin 504, q.val.Prime → 5 ≤ q.val →
    ∃ i : Fin 94, primes i=q.val := by
  decide +kernel

/-- Pad any finite collection of no-3 odd primes with the fixed prefix. -/
lemma padded_primes (P : Finset ℕ) (hP : ∀ q∈P, q.Prime ∧ 5 ≤ q) :
    ∃ n, ∃ hn : 94 ≤ n, ∃ p : Fin n → ℕ,
      (∀ i, (p i).Prime ∧ 5 ≤ p i) ∧ StrictMono p ∧
      (∀ i : Fin 94, p (Fin.castLE hn i)=primes i) ∧
      ∀ q∈P, ∃ i, p i=q := by
  classical
  let T := P.filter (fun q => 503<q)
  let p : Fin (94+T.card) → ℕ := Fin.addCases primes (T.orderEmbOfFin rfl)
  have hp (i : Fin (94+T.card)) : (p i).Prime ∧ 5 ≤ p i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have hh : (primes i).Prime ∧ 5 ≤ primes i := by revert i; decide +kernel
      simpa only [p,Fin.addCases_left] using hh
    · have hi : (T.orderEmbOfFin rfl) i ∈ P :=
        (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).1
      simpa only [p,Fin.addCases_right] using hP _ hi
  have hmono : StrictMono p := by
    intro i j hij
    revert hij
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij
      simp only [p,Fin.addCases_left]
      apply certified_prefix_mono
      exact hij
    · intro hij
      simp only [p,Fin.addCases_left,Fin.addCases_right]
      have hl := (certificate.1 i).2.1
      have hr := (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl j)).2
      omega
    · intro hij
      have hh := i.isLt
      have hj := j.isLt
      change 94+i.val < j.val at hij
      omega
    · intro hij
      simp only [p,Fin.addCases_right]
      apply (T.orderEmbOfFin rfl).strictMono
      change i.val < j.val
      change 94+i.val < 94+j.val at hij
      omega
  refine ⟨94+T.card,by omega,p,hp,hmono,?_,?_⟩
  · intro i
    change p (Fin.castAdd T.card i)=primes i
    exact Fin.addCases_left i
  · intro q hq
    by_cases hq53 : q≤503
    · obtain ⟨i,hi⟩ := small_primes_complete ⟨q,by omega⟩ (hP q hq).1 (hP q hq).2
      exact ⟨Fin.castAdd T.card i,by simpa only [p,Fin.addCases_left] using hi⟩
    · have hqT : q∈T := Finset.mem_filter.mpr ⟨hq,by omega⟩
      obtain ⟨i,hi⟩ := (T.orderIsoOfFin rfl).surjective ⟨q,hqT⟩
      refine ⟨Fin.natAdd 94 i,?_⟩
      simpa only [p,Fin.addCases_right] using congrArg Subtype.val hi

/-- A distinct nontrivial odd no-3 family cannot cover all integers even
with two additional nontrivial odd no-3 classes. The extra moduli may duplicate
each other or base labels. This is an absolute noncovering theorem. -/
theorem not_no_three_cover_with_two_exceptions {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : Fin 2 → ℕ) (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hd3 : ∀ j, ¬ 3 ∣ d j) (b : Fin 2 → ℤ) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (∃ j, (d j : ℤ) ∣ x-b j)) := by
  classical
  intro hcover
  have hex (j : Fin 2) : ∃ q, q.Prime ∧ q ∣ d j :=
    Nat.exists_prime_and_dvd (by have := (hd j).1; omega : d j≠1)
  choose q hq hqd using hex
  have hq5 (j : Fin 2) : 5 ≤ q j := by
    have hq2 := (hq j).two_le
    have hqo := (hd j).2.of_dvd_nat (hqd j)
    have hq3 : q j≠3 := by intro h; exact hd3 j (h ▸ hqd j)
    obtain ⟨k,hk⟩ := hqo
    omega
  let P := (Finset.univ.biUnion (fun i => (m i).primeFactors)) ∪ Finset.univ.image q
  have hP : ∀ r∈P, r.Prime ∧ 5 ≤ r := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hr
      have hh := Nat.mem_primeFactors.mp hi
      have ho := (hm i).2.of_dvd_nat hh.2.1
      have hne : r≠3 := by intro h; exact h3 i (h ▸ hh.2.1)
      have htwo := hh.1.two_le
      refine ⟨hh.1,?_⟩
      obtain ⟨k,hk⟩ := ho
      omega
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hr
      exact ⟨hq j,hq5 j⟩
  obtain ⟨n,hn,p,hp,hmono,hpre,hcovers⟩ := padded_primes P hP
  let e (k : I) (i : Fin n) := (m k).factorization (p i)
  let E (i : Fin n) := max 1 (Finset.univ.sup (fun k => e k i))
  have hprod (k : I) : m k=∏ i,p i^e k i := by
    let Q := Finset.univ.image p
    have hsub : (m k).primeFactors ⊆ Q := by
      intro r hr
      have hrP : r∈P := Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hr⟩)
      obtain ⟨i,hi⟩ := hcovers r hrP
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
    have hh := factorization_product_over_superset (m k)
      (by have := (hm k).1; omega) Q hsub
    rw [Finset.prod_coe_sort Q (fun r => r^(m k).factorization r)] at hh
    rw [hh]
    exact Finset.prod_image (fun i _ j _ hij => hmono.injective hij)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hinj
    rw [hprod k,hprod l,hkl]
  have he0 (k : I) : ∃ i, e k i≠0 := by
    by_contra! hz
    have hh := (hm k).1
    rw [hprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  have heE (k : I) (i : Fin n) : e k i≤E i :=
    (Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)).trans (le_max_right _ _)
  have hi (j : Fin 2) : ∃ i, p i=q j :=
    hcovers (q j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  choose i₀ hi₀ using hi
  apply not_coordinate_cover_two_exceptions hn p E hp hmono hpre e hei he0 heE a i₀
    (fun _ => le_max_left _ _) b
  intro x
  rcases hcover x with ⟨k,hk⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨k,by simpa only [← hprod] using hk⟩
  · right
    refine ⟨j,?_⟩
    rw [hi₀ j]
    exact (Int.natCast_dvd_natCast.mpr (hqd j)).trans hj

#print axioms not_no_three_cover_with_two_exceptions
#print axioms not_coordinate_cover_two_exceptions
#print axioms padded_primes
end Erdos7DoubleExceptionArithmetic
