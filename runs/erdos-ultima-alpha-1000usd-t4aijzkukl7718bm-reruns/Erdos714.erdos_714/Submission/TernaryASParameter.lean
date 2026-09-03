import FormalConjecturesUtil

/-!
An elementary parameter for an equal-row cubic norm configuration.
Over every characteristic-three finite field with more than nine elements,
there is d outside the Artin--Schreier image such that d^2-1 is a nonzero
square. The argument uses a Laurent trace polynomial, not a character-sum
estimate or a finite search. This does not settle Erdős 714.
-/
noncomputable section
open Classical Polynomial Finset
set_option maxHeartbeats 3000000
namespace Erdos714TernaryASParameter
variable {F : Type*} [Field F] [CharP F 3]

def traceSum (m : ℕ) (x : F) : F := ∑ i ∈ range m, x^(3^i)

lemma traceSum_add (m : ℕ) (x y : F) :
    traceSum m (x+y)=traceSum m x+traceSum m y := by
  simp [traceSum,add_pow_char_pow,sum_add_distrib]

omit [CharP F 3] in
lemma traceSum_zero (m : ℕ) : traceSum (F := F) m 0=0 := by simp [traceSum]

lemma traceSum_neg (m : ℕ) (x : F) : traceSum m (-x)= -traceSum m x := by
  have h := traceSum_add m x (-x)
  rw [add_neg_cancel,traceSum_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma traceSum_sub (m : ℕ) (x y : F) :
    traceSum m (x-y)=traceSum m x-traceSum m y := by
  simp only [sub_eq_add_neg,traceSum_add,traceSum_neg]

variable [Fintype F]
omit [CharP F 3] in
lemma traceSum_cube (m : ℕ) (hcard : Fintype.card F=3^m) (x : F) :
    traceSum m (x^3)=traceSum m x := by
  have hp (i : ℕ) : (x^3)^(3^i)=x^(3^(i+1)) := by rw [← pow_mul,pow_succ']
  have ht := sum_range_sub (fun i : ℕ => x^(3^i)) m
  simp_rw [← hp] at ht
  rw [sum_sub_distrib] at ht
  have he : x^(3^m)-x^(3^0)=0 := by simp [← hcard,FiniteField.pow_card]
  rw [he] at ht
  exact sub_eq_zero.mp ht

lemma traceSum_AS (m : ℕ) (hcard : Fintype.card F=3^m) (x : F) :
    traceSum m (x^3-x)=0 := by rw [traceSum_sub,traceSum_cube m hcard,sub_self]

omit [CharP F 3] [Fintype F] in
def traceNumerator (m : ℕ) : F[X] :=
  ∑ i ∈ range m, (X^(3^(m-1)+3^i)+X^(3^(m-1)-3^i))

omit [CharP F 3] [Fintype F] in
lemma numerator_degree (m : ℕ) : (traceNumerator (F := F) m).natDegree  ≤  2*3^(m-1) := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ m-1 := by have := mem_range.mp hi; omega
  have hp : 3^i ≤ 3^(m-1) := Nat.pow_le_pow_right (by decide) hi'
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_X_pow_le _).trans (by omega)
  · exact (Polynomial.natDegree_X_pow_le _).trans ((Nat.sub_le _ _).trans (by omega))

omit [CharP F 3] [Fintype F] in
lemma numerator_coeff (m : ℕ) (hm : 0  <  m) :
    (traceNumerator (F := F) m).coeff (2*3^(m-1))=1 := by
  have he : 0 < (3:ℕ)^(m-1) := pow_pos (by decide) _
  simp only [traceNumerator,finset_sum_coeff,coeff_add,coeff_X_pow]
  rw [sum_eq_single (m-1)]
  · have hn : 3^(m-1)-3^(m-1) ≠ 2*3^(m-1) := by omega
    simp [show 3^(m-1)+3^(m-1)=2*3^(m-1) by omega]
  · intro i hi hne
    have hp : (3:ℕ)^i ≠ 3^(m-1) := fun h => hne (Nat.pow_right_injective (by decide) h)
    have hpos : 3^(m-1)+3^i ≠ 2*3^(m-1) := by omega
    have hneg : 3^(m-1)-3^i ≠ 2*3^(m-1) := by
      have hh := Nat.sub_le (3^(m-1)) (3^i)
      omega
    simp [Ne.symm hpos,Ne.symm hneg]
  · intro h
    exact False.elim (h (mem_range.mpr (by omega)))

omit [CharP F 3] [Fintype F] in
lemma numerator_ne_zero (m : ℕ) (hm : 0  <  m) : traceNumerator (F := F) m ≠ 0 := by
  intro h
  have he := numerator_coeff (F := F) m hm
  rw [h,coeff_zero] at he
  exact zero_ne_one he

omit [Fintype F] in
lemma numerator_eval (m : ℕ) (x : F) (hx : x ≠ 0) :
    (traceNumerator m).eval x=x^(3^(m-1))*traceSum m (x+x⁻¹) := by
  simp only [traceNumerator,eval_finset_sum,eval_add,eval_pow,eval_X,traceSum,mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ m-1 := by have := mem_range.mp hi; omega
  have hp : 3^i ≤ 3^(m-1) := Nat.pow_le_pow_right (by decide) hi'
  rw [add_pow_char_pow x x⁻¹ 3 i,pow_add,pow_sub₀ x hx hp,inv_pow,mul_add]

/-- The rational trace is nonzero away from its three exceptional parameters. -/
theorem exists_reciprocal_trace (m : ℕ) (hm : 3 ≤ m)
    (hcard : Fintype.card F=3^m) :
    ∃ u : F, u ≠ 0 ∧ u ≠ 1 ∧ u ≠  -1 ∧ traceSum m (u+u⁻¹) ≠ 0 := by
  let S : Finset F := univ \ {0,1,-1}
  have hS : Fintype.card F-3 ≤ S.card := by
    have h := card_sdiff_add_card_inter (univ : Finset F) {0,1,-1}
    have hsmall : ((univ : Finset F) ∩ {0,1,-1}).card ≤ 3 :=
      (card_le_card inter_subset_right).trans card_le_three
    dsimp only [S]
    simp only [card_univ] at h
    omega
  have he : 9 ≤ 3^(m-1) := by
    simpa using Nat.pow_le_pow_right (n := 3) (by decide) (show 2 ≤ m-1 by omega)
  have hpow : 3^m=3*3^(m-1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hdeg : (traceNumerator (F := F) m).natDegree < S.card := by
    have hd := numerator_degree (F := F) m
    rw [hcard,hpow] at hS
    omega
  by_contra! h
  have hzero : traceNumerator (F := F) m=0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S _ hdeg
    intro u hu
    have hn : u ≠ 0 ∧ u ≠ 1 ∧ u ≠  -1 := by simpa [S,mem_sdiff,mem_insert,mem_singleton] using hu
    rw [numerator_eval m u hn.1,h u hn.1 hn.2.1 hn.2.2,mul_zero]
  exact numerator_ne_zero m (by omega) hzero

/-- Uniformly chosen d is outside the Artin--Schreier image, with a nonzero
square root of d^2-1. In particular the associated cubic is irreducible. -/
theorem exists_parameter_pow (m : ℕ) (hm : 3 ≤ m)
    (hcard : Fintype.card F=3^m) :
    ∃ d v : F, d ≠ 0 ∧ v ≠ 0 ∧ v^2=d^2-1 ∧
      Irreducible (X^3-X-C d : F[X]) := by
  obtain ⟨u,hu,hu1,hum1,ht⟩ := exists_reciprocal_trace m hm hcard
  let d := -(u+u⁻¹)
  let v := -(u-u⁻¹)
  have hdtr : traceSum m d ≠ 0 := by simpa only [d,traceSum_neg,neg_ne_zero] using ht
  have hd : d ≠ 0 := fun h => hdtr (h ▸ traceSum_zero m)
  have hv : v ≠ 0 := by
    intro h
    have he : u=u⁻¹ := sub_eq_zero.mp (neg_eq_zero.mp h)
    have hh : u^2=1^2 := by
      calc
        u^2=u*u := pow_two u
        _ = u*u⁻¹ := congrArg (u*·) he
        _ = 1^2 := by simp [hu]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h | h
    · exact hu1 h
    · exact hum1 h
  refine ⟨d,v,hd,hv,?_,?_⟩
  · have hi := mul_inv_cancel₀ hu
    have h3 : (3 : F)=0 := CharP.cast_eq_zero F 3
    dsimp [d,v]
    linear_combination -hi-h3*(u*u⁻¹)
  · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have hdg : (X^3-X-C d : F[X]).natDegree=3 := by compute_degree!
      rw [hdg]; decide
    · intro x hx
      have he : x^3-x=d := by
        have hh : x^3-x-d=0 := by simpa [Polynomial.IsRoot.def] using hx
        exact sub_eq_zero.mp hh
      exact hdtr (he ▸ traceSum_AS m hcard x)

/-- The power-of-three presentation is supplied automatically for a finite field. -/
theorem exists_parameter (hq : 9 < Fintype.card F) :
    ∃ d v : F, d ≠ 0 ∧ v ≠ 0 ∧ v^2=d^2-1 ∧
      Irreducible (X^3-X-C d : F[X]) := by
  obtain ⟨m,_,hm⟩ := FiniteField.card F 3
  apply exists_parameter_pow m _ hm
  by_contra! h
  have hp : 3^(m : ℕ) ≤ 3^2 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [← hm] at hp
  norm_num at hp
  omega

end Erdos714TernaryASParameter
#print axioms Erdos714TernaryASParameter.exists_parameter
