import Submission.UniformSupportCompletion

/-! Arithmetic realization of bounded box families using distinct squarefree
prime products. Applied to UniformSupportCompletion, this gives genuine odd
congruence families with private points and divisor closure, but NOT covers. -/
namespace Erdos7SquarefreeBoxRealization
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

def modulus (S : Finset I) : ℕ := ∏ i ∈ S, p i

include hp hinj

lemma coprime : Pairwise (Function.onFun Nat.Coprime p) := by
  intro i j hij
  exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))

omit hinj in
lemma modulus_pos (S : Finset I) : 0 < modulus p S :=
  Finset.prod_pos (fun i _ => (hp i).pos)

lemma prime_dvd_modulus (S : Finset I) (i : I) : p i ∣ modulus p S ↔ i ∈ S := by
  rw [modulus, (hp i).prime.dvd_finset_prod_iff]
  constructor
  · rintro ⟨j,hj,hd⟩
    have he := ((hp j).dvd_iff_eq (hp i).ne_one).mp hd
    exact hinj he ▸ hj
  · intro hi
    exact ⟨i,hi,dvd_rfl⟩

lemma modulus_injective : Function.Injective (modulus p) := by
  intro S T h
  ext i
  rw [← prime_dvd_modulus p hp hinj S i, ← prime_dvd_modulus p hp hinj T i, h]

lemma modulus_squarefree (S : Finset I) : Squarefree (modulus p S) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    exact Nat.coprime_iff_isRelPrime.mp (coprime p hp hinj hij)
  · exact fun i _ => (hp i).squarefree

/-- Every divisor of a squarefree support product is the product of a subset. -/
lemma divisor_subset (S : Finset I) (d : ℕ) (hd : d ∣ modulus p S) :
    ∃ T ⊆ S, modulus p T = d := by
  classical
  let T := S.filter (fun i => p i ∣ d)
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (ne_of_gt (modulus_pos p hp S)) hd
  have hsq : Squarefree d := (modulus_squarefree p hp hinj S).squarefree_of_dvd hd
  have he : d.primeFactors = T.image p := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqprime,hqd,_⟩ := Nat.mem_primeFactors.mp hq
      obtain ⟨i,hi,hqi⟩ := hqprime.prime.dvd_finset_prod_iff p |>.mp (hqd.trans hd)
      have hqi' : q = p i := ((hp i).dvd_iff_eq hqprime.ne_one).mp hqi |>.symm
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hqi' ▸ hqd⟩,hqi'.symm⟩
    · rintro hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact Nat.mem_primeFactors.mpr ⟨hp i,(Finset.mem_filter.mp hi).2,hd0⟩
  refine ⟨T,Finset.filter_subset _ _,?_⟩
  have hh := Nat.prod_primeFactors_of_squarefree hsq
  rw [he, Finset.prod_image (by intro i _ j _ hij; exact hinj hij)] at hh
  exact hh

lemma integer_coordinates (x : I → ℤ) : ∃ a : ℤ, ∀ i, (p i : ℤ) ∣ a-x i := by
  letI (i : I) : NeZero (p i) := ⟨(hp i).ne_zero⟩
  let z := Nat.chineseRemainderOfFinset (fun i => (x i : ZMod (p i)).val) p Finset.univ
    (fun i _ => (hp i).ne_zero) (fun i _ j _ hij => coprime p hp hinj hij)
  refine ⟨z.val,fun i => ?_⟩
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (z.val : ℤ) (p i)).mp
  have hh : (z.val : ZMod (p i)) = x i := by
    rw [← ZMod.natCast_zmod_val (x i : ZMod (p i))]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  simpa only [Int.cast_natCast] using hh.symm

lemma modulus_dvd_iff (S : Finset I) (x : ℤ) :
    (modulus p S : ℤ) ∣ x ↔ ∀ i ∈ S, (p i : ℤ) ∣ x := by
  constructor
  · intro h i hi
    have hd : p i ∣ modulus p S := (prime_dvd_modulus p hp hinj S i).mpr hi
    exact (by exact_mod_cast hd : (p i : ℤ) ∣ (modulus p S : ℤ)).trans h
  · intro h
    rw [modulus,Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime (fun i _ j _ hij => (coprime p hp hinj hij).isCoprime) h

lemma realized_membership (S : Finset I) (r y : I → ℤ) (a z : ℤ)
    (ha : ∀ i, (p i : ℤ) ∣ a-r i) (hz : ∀ i, (p i : ℤ) ∣ z-y i) :
    (modulus p S : ℤ) ∣ z-a ↔ ∀ i ∈ S, (p i : ℤ) ∣ y i-r i := by
  rw [modulus_dvd_iff p hp hinj]
  constructor
  · intro h i hi
    convert dvd_add (dvd_sub (h i hi) (hz i)) (ha i) using 1 <;> ring
  · intro h i hi
    convert dvd_sub (dvd_add (h i hi) (hz i)) (ha i) using 1 <;> ring

end

lemma eq_of_bounded_congruent (p w : ℕ) (hp : w+3 ≤ p) (u v : ℤ)
    (hu : -3 ≤ u ∧ u < (w : ℤ)-1) (hv : -3 ≤ v ∧ v < (w : ℤ)-1)
    (h : (p : ℤ) ∣ u-v) : u = v := by
  by_cases huv : u ≤ v
  · have hd : (p : ℤ) ∣ v-u := by simpa only [neg_sub] using dvd_neg.mpr h
    have hh := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ v-u)
      (by omega : v-u < (p : ℤ)) hd
    omega
  · have hh := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ u-v)
      (by omega : u-v < (p : ℤ)) h
    omega

section Completion
open Erdos7UniformSupportCompletion
variable {I J : Type*} [Fintype I] [DecidableEq I]

/-- The completed boxes are actual residue classes with distinct squarefree
odd moduli, private integers, and the explicitly uncovered integer -3. The CRT
coordinate relation is retained for interpreting any selected branch pairs. -/
theorem exists_completed_arithmetic_family (w : ℕ) (hw : 0 < w)
    (S : J → Finset I) (hS : ∀ j, (S j).card = w) (hSi : Function.Injective S)
    (b : J → I → Fin 2) (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (hodd : ∀ i, Odd (p i)) (hbig : ∀ i, w+3 ≤ p i) :
    let m := fun k : Index (I := I) (J := J) w => modulus p (support w S k)
    Function.Injective m ∧
    (∀ k, 1 < m k ∧ Odd (m k) ∧ Squarefree (m k)) ∧
    (∀ k d, 1 < d → d ∣ m k → ∃ l, m l = d) ∧
    ∃ a : Index (I := I) (J := J) w → ℤ,
      (∀ k i, (p i : ℤ) ∣ a k-residue w b k i) ∧
      (∀ k, ∃ z : ℤ, ∀ l, ((m l : ℤ) ∣ z-a l) ↔ l=k) ∧
      ∀ k, ¬ (m k : ℤ) ∣ -3-a k := by
  classical
  dsimp only
  refine ⟨(modulus_injective p hp hpi).comp (support_injective w S hS hSi), ?_, ?_, ?_⟩
  · intro k
    have hpos := modulus_pos p hp (support w S k)
    obtain ⟨i,hi⟩ := support_nonempty w hw S hS k
    have hd := (prime_dvd_modulus p hp hpi (support w S k) i).mpr hi
    have hh := Nat.le_of_dvd hpos hd
    refine ⟨(hp i).one_lt.trans_le hh, ?_, modulus_squarefree p hp hpi _⟩
    exact Finset.prod_induction p Odd (fun _ _ hx hy => hx.mul hy) (by norm_num)
      (fun i _ => hodd i)
  · intro k d hd hdiv
    obtain ⟨T,hT,he⟩ := divisor_subset p hp hpi (support w S k) d hdiv
    have hne : T.Nonempty := by
      by_contra hn
      have hh : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [hh,modulus,Finset.prod_empty] at he
      omega
    obtain ⟨l,hl⟩ := divisor_closed w S hS k T hne hT
    exact ⟨l,by rw [hl,he]⟩
  · choose a ha using fun k => integer_coordinates p hp hpi (residue w b k)
    refine ⟨a,ha,?_,?_⟩
    · intro k
      obtain ⟨z,hz⟩ := integer_coordinates p hp hpi (privatePoint w S b k)
      refine ⟨z,fun l => ?_⟩
      rw [realized_membership p hp hpi (support w S l) (residue w b l)
        (privatePoint w S b k) (a l) z (ha l) hz]
      have he : (∀ i ∈ support w S l, (p i : ℤ) ∣ privatePoint w S b k i-residue w b l i) ↔
          ∀ i ∈ support w S l, privatePoint w S b k i=residue w b l i := by
        constructor
        · intro h i hi
          have hb := residue_bounds w hw b l i
          exact eq_of_bounded_congruent (p i) w (hbig i) _ _
            (private_bounds w hw S b k i) ⟨by omega,hb.2⟩ (h i hi)
        · intro h i hi
          rw [h i hi,sub_self]
          exact dvd_zero _
      rw [he]
      exact private_points w hw S hS hSi b k l
    · intro k hd
      obtain ⟨i,hi⟩ := support_nonempty w hw S hS k
      have hh := (modulus_dvd_iff p hp hpi _ _).mp hd i hi
      have hr : (p i : ℤ) ∣ -3-residue w b k i := by
        convert dvd_add hh (ha k i) using 1 <;> ring
      have hb := residue_bounds w hw b k i
      have he := eq_of_bounded_congruent (p i) w (hbig i) (-3) (residue w b k i)
        ⟨le_rfl,by omega⟩ ⟨by omega,hb.2⟩ hr
      omega

end Completion
#print axioms divisor_subset
#print axioms exists_completed_arithmetic_family
end Erdos7SquarefreeBoxRealization
