import Submission.NoFiveBox

/-! CRT and factorization specialization of the no-five box criterion. -/
namespace Erdos7NoFiveArithmetic
open scoped BigOperators
open Erdos7Reduction Erdos7Compression Erdos7Distortion Erdos7StarSieve
open Erdos7NoFiveScalar Erdos7NoFiveHybrid
set_option maxHeartbeats 6000000

variable (hcert :
    (∀ i : Fin 366, 3 ≤ primes i ∧ primes i ≤ 2503 ∧
      Row (primes i) (states i.castSucc) (states i.succ)) ∧
    (∀ x : Fin 501, (states 366).values x=0) ∧
    (states 366).slope=0 ∧ (states 366).intercept=0)

include hcert in
theorem not_coordinate_cover {n : ℕ} {κ : Type*} [Fintype κ]
    (hn : 366 ≤ n) (p E : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime ∧ 3 ≤ p i ∧ p i ≠ 5) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=primes i)
    (e : κ → Fin n → ℕ) (hei : Function.Injective e)
    (he0 : ∀ k, ∃ i, e k i≠0) (heE : ∀ k i, e k i≤E i) (a : κ → ℤ)
    : ¬ (∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) := by
  classical
  intro hcover
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hmono.injective h))
  letI (i : Fin n) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  let A (i : Fin n) := ZMod (p i ^ E i)
  let f (k : κ) (i : Fin n) := ZMod.castHom (pow_dvd_pow (p i) (heE k i)) (ZMod (p i ^ e k i))
  let X (k : κ) (i : Fin n) := Finset.univ.filter (fun x : A i => f k i x=(a k : ZMod (p i ^ e k i)))
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
  apply Erdos7NoFiveBox.not_cover hcert hn A p E hp hmono hpre e hei he0 heE X hX0 hXcard
  intro x
  let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => p i ^ E i) Finset.univ
    (fun i _ => pow_ne_zero _ (NeZero.ne _))
    (fun i _ j _ hij => (hcop hij).pow _ _)
  have hz (i : Fin n) : (z.val : A i)=x i := by
    rw [← ZMod.natCast_zmod_val (x i)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  obtain ⟨k,hk⟩ := hcover (z.val : ℤ)
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

lemma prefix_prime_data (i : Fin 366) :
    (primes i).Prime ∧ 3 ≤ primes i ∧ primes i ≠ 5 := by
  have hmem : primes i ∈ Finset.univ.image primes := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  rw [Erdos7NoFiveSaving.prefix_set] at hmem
  rcases Finset.mem_union.mp hmem with hmem | hmem
  · rw [Finset.mem_singleton.mp hmem]
    norm_num
  · have hh := List.mem_filter.mp (List.mem_toFinset.mp hmem)
    have hc : 7 ≤ primes i ∧ (primes i).Prime := by
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using hh.2
    exact ⟨hc.2,by omega,by omega⟩

lemma small_primes_complete (q : ℕ) (hq : q.Prime) (hlo : 3 ≤ q) (hfive : q ≠ 5)
    (hhi : q ≤ 2503) : ∃ i : Fin 366, primes i=q := by
  have hmem : q ∈ Finset.univ.image primes := by
    rw [Erdos7NoFiveSaving.prefix_set]
    by_cases h3 : q=3
    · simp [h3]
    · have h7 : 7 ≤ q := by
        by_contra h
        have h6 : q ≤ 6 := by omega
        interval_cases q <;> norm_num at *
      apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      simp only [Erdos7NoFiveRawPrefix.primes,List.mem_filter,List.mem_range,
        Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨by omega,h7,hq⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i,hi⟩

include hcert in
lemma padded_primes (P : Finset ℕ) (hP : ∀ q∈P, q.Prime ∧ 3 ≤ q ∧ q ≠ 5) :
    ∃ n, ∃ hn : 366 ≤ n, ∃ p : Fin n → ℕ,
      (∀ i, (p i).Prime ∧ 3 ≤ p i ∧ p i ≠ 5) ∧ StrictMono p ∧
      (∀ i : Fin 366, p (Fin.castLE hn i)=primes i) ∧
      ∀ q∈P, ∃ i, p i=q := by
  classical
  let T := P.filter (fun q => 2503<q)
  let p : Fin (366+T.card) → ℕ := Fin.addCases primes (T.orderEmbOfFin rfl)
  have hp (i : Fin (366+T.card)) : (p i).Prime ∧ 3 ≤ p i ∧ p i ≠ 5 := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have hh := prefix_prime_data i
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
      have hl := (hcert.1 i).2.1
      have hr := (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl j)).2
      omega
    · intro hij
      have hh := i.isLt
      have hj := j.isLt
      change 366+i.val < j.val at hij
      omega
    · intro hij
      simp only [p,Fin.addCases_right]
      apply (T.orderEmbOfFin rfl).strictMono
      change i.val < j.val
      change 366+i.val < 366+j.val at hij
      omega
  refine ⟨366+T.card,by omega,p,hp,hmono,?_,?_⟩
  · intro i
    change p (Fin.castAdd T.card i)=primes i
    exact Fin.addCases_left i
  · intro q hq
    by_cases hq2503 : q≤2503
    · obtain ⟨i,hi⟩ := small_primes_complete q (hP q hq).1 (hP q hq).2.1 (hP q hq).2.2 hq2503
      exact ⟨Fin.castAdd T.card i,by simpa only [p,Fin.addCases_left] using hi⟩
    · have hqT : q∈T := Finset.mem_filter.mpr ⟨hq,by omega⟩
      obtain ⟨i,hi⟩ := (T.orderIsoOfFin rfl).surjective ⟨q,hqT⟩
      refine ⟨Fin.natAdd 366 i,?_⟩
      simpa only [p,Fin.addCases_right] using congrArg Subtype.val hi

include hcert in
theorem not_no_five_cover {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h5 : ∀ i, ¬ 5 ∣ m i) :
    ¬ (∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i) := by
  classical
  intro hcover
  let P := Finset.univ.biUnion (fun i => (m i).primeFactors)
  have hP : ∀ r∈P, r.Prime ∧ 3 ≤ r ∧ r ≠ 5 := by
    intro r hr
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hr
    have hh := Nat.mem_primeFactors.mp hi
    have ho := (hm i).2.of_dvd_nat hh.2.1
    have hne : r≠5 := by intro h; exact h5 i (h ▸ hh.2.1)
    have htwo := hh.1.two_le
    refine ⟨hh.1,?_,hne⟩
    obtain ⟨k,hk⟩ := ho
    omega
  obtain ⟨n,hn,p,hp,hmono,hpre,hcovers⟩ := padded_primes hcert P hP
  let e (k : I) (i : Fin n) := (m k).factorization (p i)
  let E (i : Fin n) := max 1 (Finset.univ.sup (fun k => e k i))
  have hprod (k : I) : m k=∏ i,p i^e k i := by
    let Q := Finset.univ.image p
    have hsub : (m k).primeFactors ⊆ Q := by
      intro r hr
      have hrP : r∈P := Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hr⟩
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
  apply not_coordinate_cover hcert hn p E hp hmono hpre e hei he0 heE a
  intro x
  obtain ⟨k,hk⟩ := hcover x
  exact ⟨k,by simpa only [← hprod] using hk⟩

include hcert in
theorem arithmetic_exists_five {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) : ∃ i,5 ∣ m i := by
  classical
  by_contra! hno
  exact not_no_five_cover hcert m a hc.1 hc.2.1 hno hc.2.2

include hcert in
theorem strict_exists_five (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) : ∃ i,5 ∣ (C.moduli i).absNorm := by
  letI := C.fintypeIndex
  exact arithmetic_exists_five hcert (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms arithmetic_exists_five
#print axioms strict_exists_five
end Erdos7NoFiveArithmetic
