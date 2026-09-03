import FormalConjecturesUtil

/-! Finiteness for a fixed affine expression at the dyadic tower 3^(2^r).
This is an arithmetic ingredient for fixed-residual polynomial families;
it does not by itself settle the missing-digit conjecture. -/
namespace Erdos406AffineTower

lemma three_tower_congruence (r : ℕ) : (2 : ℤ)^(r+1) ∣ 3^(2^r)-1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    obtain ⟨q,hq⟩ := ih
    have hh : (3 : ℤ)^(2^r) = 1+2^(r+1)*q := by omega
    refine ⟨q+2^r*q^2,?_⟩
    rw [pow_succ (2 : ℕ) r,pow_mul,hh]
    simp only [pow_succ]
    ring

lemma even_three_power_plus_one_bound (a C k : ℕ) (ha : Even a) (hC : 0 < C)
    (hd : 3^a+1 ∣ C*2^k) : 3^a+1 ≤ 2*C := by
  have hm : (3^a+1 : ℕ)%4 = 2 := by
    obtain ⟨t,ht⟩ := ha
    rw [ht,← two_mul,pow_mul]
    norm_num [Nat.add_mod,Nat.pow_mod]
  let q := (3^a+1)/2
  have he : 3^a+1 = 2*q := by dsimp [q]; omega
  have ho : Odd q := Nat.odd_iff.mpr (by omega)
  have hq : q ∣ C*2^k := (show q ∣ 3^a+1 from ⟨2,by omega⟩).trans hd
  have hqC : q ∣ C := (ho.coprime_two_right.pow_right k).dvd_of_dvd_mul_right hq
  have hb := Nat.le_of_dvd hC hqC
  omega

lemma affine_tower_injective (A B : ℤ) (hA : A ≠ 0) :
    Function.Injective (fun r : ℕ => A*(3 : ℤ)^(2^r)+B) := by
  intro r s h
  have hh : (3 : ℤ)^(2^r) = 3^(2^s) := mul_left_cancel₀ hA (add_right_cancel h)
  have hn : (3 : ℕ)^(2^r) = 3^(2^s) := by exact_mod_cast hh
  exact Nat.pow_right_injective (by decide : 2 ≤ 2)
    (Nat.pow_right_injective (by decide : 2 ≤ 3) hn)

lemma finite_affine_tower_nonzero_sum (A B C : ℤ) (hA : A ≠ 0) (hAB : A+B ≠ 0) :
    {r : ℕ | ∃ k : ℕ, C*2^k = A*3^(2^r)+B}.Finite := by
  let s := (A+B).natAbs+1
  have hsize : (A+B).natAbs < 2^s := by
    have hh : s < 2^s := Nat.lt_two_pow_self
    dsimp [s] at hh ⊢
    omega
  have hf (k : ℕ) : {r : ℕ | A*3^(2^r)+B = C*2^k}.Finite := by
    simpa using
      (Set.finite_singleton (C*2^k)).preimage (affine_tower_injective A B hA).injOn
  apply ((Set.finite_lt_nat s).union
    ((Set.finite_lt_nat s).biUnion (fun k _ => hf k))).subset
  rintro r ⟨k,he⟩
  by_cases hr : r < s
  · exact Or.inl hr
  right
  have hk : k < s := by
    by_contra hk
    have hds : (2 : ℤ)^s ∣ 3^(2^r)-1 :=
      (pow_dvd_pow 2 (by omega : s ≤ r+1)).trans (three_tower_congruence r)
    have hdk : (2 : ℤ)^s ∣ C*2^k :=
      dvd_mul_of_dvd_right (pow_dvd_pow 2 (by omega : s ≤ k)) C
    have hd : (2 : ℤ)^s ∣ A+B := by
      convert dvd_sub hdk (dvd_mul_of_dvd_right hds A) using 1
      rw [he]
      ring
    apply hAB
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
    simpa using hsize
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,he.symm⟩⟩

lemma finite_affine_tower_zero_sum (A B C : ℤ) (hC : C ≠ 0) (hAB : A+B = 0) :
    {r : ℕ | ∃ k : ℕ, C*2^k = A*3^(2^r)+B}.Finite := by
  apply (Set.finite_lt_nat (2*C.natAbs+2)).subset
  rintro r ⟨k,he⟩
  change r < 2*C.natAbs+2
  by_cases hr : r < 2
  · omega
  let a := 2^(r-1)
  have har : 2^r = 2*a := by
    dsimp [a]
    rw [← pow_succ',Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have ha : Even a := by
    apply Nat.even_iff.mpr
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_pow_self 2 (by omega : r-1 ≠ 0)
  have hdivZ : ((3 : ℤ)^a+1) ∣ C*2^k := by
    refine ⟨A*(3^a-1),?_⟩
    rw [he,har,Nat.mul_comm 2 a,pow_mul]
    have hB : B = -A := by omega
    rw [hB]
    ring
  have hdiv : 3^a+1 ∣ C.natAbs*2^k := by
    have hh := Int.natAbs_dvd_natAbs.mpr hdivZ
    have hp : (0 : ℤ) ≤ 3^a+1 := by positivity
    norm_num only [Int.natAbs_mul,Int.natAbs_pow] at hh
    have heq : ((3 : ℤ)^a+1).natAbs = (3^a+1 : ℕ) := by
      exact_mod_cast (Int.natAbs_of_nonneg hp)
    rwa [heq] at hh
  have hb := even_three_power_plus_one_bound a C.natAbs k ha
    (Int.natAbs_pos.mpr hC) hdiv
  have har' : r ≤ a := by
    have hh : r-1 < 2^(r-1) := Nat.lt_two_pow_self
    dsimp [a]
    omega
  have ha3 : a < 3^a := by
    exact (Nat.lt_two_pow_self (n := a)).trans_le (Nat.pow_le_pow_left (by decide : 2 ≤ 3) a)
  omega

/-- A fixed affine expression A*3^(2^r)+B is a fixed nonzero multiple of a
power of two only for finitely many r. Neither coefficient may be discarded. -/
theorem finite_affine_dyadic_tower (A B C : ℤ) (hA : A ≠ 0) (hC : C ≠ 0) :
    {r : ℕ | ∃ k : ℕ, C*2^k = A*3^(2^r)+B}.Finite := by
  by_cases hAB : A+B = 0
  · exact finite_affine_tower_zero_sum A B C hC hAB
  · exact finite_affine_tower_nonzero_sum A B C hA hAB

#print axioms three_tower_congruence
#print axioms finite_affine_dyadic_tower
end Erdos406AffineTower
