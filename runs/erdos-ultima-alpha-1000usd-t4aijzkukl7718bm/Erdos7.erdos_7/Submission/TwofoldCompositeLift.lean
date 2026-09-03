import Submission.TwofoldNoThreeLift
import Submission.Capped19Arithmetic
import Submission.NoFiveCompletion

/-!
The twofold lift needs a fresh cofactor, not a fresh prime. Choosing a large
power of an existing modulus preserves all prime factors except the added3.
This is still conditional on an actual no-three twofold cover.
-/
namespace Erdos7TwofoldCompositeLift
open scoped BigOperators
open Erdos7TwofoldNoThreeLift Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable
section
variable {I : Type} [Fintype I]
variable (m : I → ℕ) (q : ℕ)

lemma cofactor_data (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i)
    (hqOdd : Odd q) (hq3n : ¬ 3 ∣ q) (hq3 : 3 < q) (k : Option (Option I)) :
    0 < cofactor m q k ∧ Odd (cofactor m q k) ∧ ¬ 3 ∣ cofactor m q k := by
  cases k with
  | none =>
    exact ⟨by change 0 < q; omega,hqOdd,hq3n⟩
  | some k =>
    cases k with
    | none => norm_num [cofactor]
    | some i => exact ⟨by dsimp [cofactor]; have := (hm i).1; omega,(hm i).2,h3 i⟩

lemma modulus_data (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i) (hqOdd : Odd q) (hq3n : ¬ 3 ∣ q) (hq3 : 3 < q) (hqbig : ∀ i,m i < q) :
    Function.Injective (modulus m q) ∧
      ∀ k,1 < modulus m q k ∧ Odd (modulus m q k) := by
  have hc := cofactor_data m q hm h3 hqOdd hq3n hq3
  have hci := cofactor_injective m q hinj (fun i => (hm i).1) hq3 hqbig
  have hp (t : Fin q) : 3 ∣ 3^(t.val+1) := by
    rw [pow_succ]; exact dvd_mul_left _ _
  constructor
  · intro k l he
    cases k with
    | inl i =>
      cases l with
      | inl j => exact congrArg Sum.inl (hinj he)
      | inr z =>
        apply False.elim
        apply h3 i
        change m i=3^(z.1.val+1)*cofactor m q z.2 at he
        rw [he]
        exact dvd_mul_of_dvd_left (hp z.1) (cofactor m q z.2)
    | inr z =>
      cases l with
      | inl i =>
        apply False.elim
        apply h3 i
        change 3^(z.1.val+1)*cofactor m q z.2=m i at he
        rw [← he]
        exact dvd_mul_of_dvd_left (hp z.1) (cofactor m q z.2)
      | inr w =>
        obtain ⟨ht,hk⟩ := three_power_unique _ _ _ _ (hc z.2).1 (hc w.2).1
          (hc z.2).2.2 (hc w.2).2.2 he
        have ht' : z.1=w.1 := Fin.ext (by omega)
        exact congrArg Sum.inr (Prod.ext ht' (hci hk))
  · intro k
    cases k with
    | inl i => exact hm i
    | inr z =>
      change 1 < 3^(z.1.val+1)*cofactor m q z.2 ∧ Odd (3^(z.1.val+1)*cofactor m q z.2)
      have hp3 : 3 ≤ 3^(z.1.val+1) := by
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 3) (show 1≤z.1.val+1 by omega)
        simpa using hh
      have hcf := (hc z.2).1
      exact ⟨by nlinarith,((by decide : Odd 3).pow).mul (hc z.2).2.1⟩

variable (a₀ a₁ : I → ℤ)

lemma exists_residues (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i)
    (hqOdd : Odd q) (hq3n : ¬ 3 ∣ q) (hq3 : 3 < q) :
    ∃ a : Index (I := I) q → ℤ,
      (∀ i,a (.inl i)=a₀ i) ∧
      (∀ t k,(3 : ℤ)^(t.val+1) ∣ a (.inr (t,k))-ternaryResidue q t k ∧
        (cofactor m q k : ℤ) ∣ a (.inr (t,k))-cofactorResidue q a₁ t k) := by
  have hc (k) := (Nat.prime_three.coprime_iff_not_dvd.mpr
    (cofactor_data m q hm h3 hqOdd hq3n hq3 k).2.2)
  choose z hz using fun (t : Fin q) k => crt_pair (3^(t.val+1)) (cofactor m q k)
    ((hc k).pow_left _) (ternaryResidue q t k) (cofactorResidue q a₁ t k)
  refine ⟨Sum.elim a₀ (fun z' => z z'.1 z'.2),fun _ => rfl,?_⟩
  intro t k
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hz t k

lemma lifted_covers (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i)
    (hqOdd : Odd q) (hq3n : ¬ 3 ∣ q) (hq3 : 3 < q)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i)
    (a : Index (I := I) q → ℤ)
    (ha₀ : ∀ i,a (.inl i)=a₀ i)
    (ha : ∀ (t : Fin q) k,(3 : ℤ)^(t.val+1) ∣ a (.inr (t,k))-ternaryResidue q t k ∧
      (cofactor m q k : ℤ) ∣ a (.inr (t,k))-cofactorResidue q a₁ t k) :
    ∀ x : ℤ,∃ k,(modulus m q k : ℤ) ∣ x-a k := by
  intro x
  have hhit (t : Fin q) (k : Option (Option I))
      (hter : (3 : ℤ)^(t.val+1) ∣ x-ternaryResidue q t k)
      (hcf : (cofactor m q k : ℤ) ∣ x-cofactorResidue q a₁ t k) :
      (modulus m q (.inr (t,k)) : ℤ) ∣ x-a (.inr (t,k)) := by
    have hc := ((Nat.prime_three.coprime_iff_not_dvd.mpr
      (cofactor_data m q hm h3 hqOdd hq3n hq3 k).2.2).pow_left (t.val+1)).isCoprime
    have ht' : (3 : ℤ)^(t.val+1) ∣ x-a (.inr (t,k)) := by
      convert dvd_sub hter (ha t k).1 using 1 <;> ring
    have hc' : (cofactor m q k : ℤ) ∣ x-a (.inr (t,k)) := by
      convert dvd_sub hcf (ha t k).2 using 1 <;> ring
    simpa only [modulus,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      hc.mul_dvd (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht') hc'
  by_cases hstem : (3 : ℤ)^q ∣ x+1
  · have hqpos : (0 : ℤ) < q := by omega
    have hr0 := Int.emod_nonneg x hqpos.ne'
    have hrq := Int.emod_lt_of_pos x hqpos
    let t : Fin q := ⟨(x%(q : ℤ)).toNat,by omega⟩
    have ht : (t.val : ℤ)=x%(q : ℤ) := Int.toNat_of_nonneg hr0
    refine ⟨.inr (t,none),hhit t none ?_ ?_⟩
    · change (3 : ℤ)^(t.val+1) ∣ x-(-1)
      simpa only [sub_neg_eq_add] using
        (pow_dvd_pow (3 : ℤ) (by omega : t.val+1 ≤ q)).trans hstem
    · change (q : ℤ) ∣ x-(t.val : ℤ)
      rw [ht]
      exact ⟨x/(q : ℤ),by have hh := Int.emod_add_mul_ediv x (q : ℤ); nlinarith⟩
  · obtain ⟨e,c,he,heq,hc0,hc3,hx⟩ :=
      Erdos7PrimePowerFirstExit.first_exit 3 q (by decide) x hstem
    let t : Fin q := ⟨e-1,by omega⟩
    have ht : t.val+1=e := by dsimp [t]; omega
    by_cases hc1 : c=1
    · subst c
      refine ⟨.inr (t,some none),hhit t (some none) ?_ ?_⟩
      · simpa only [ternaryResidue,ht] using hx
      · change (1 : ℤ) ∣ x-0
        exact one_dvd _
    · have hc2 : c=2 := by omega
      subst c
      obtain ⟨i,hi | hi⟩ := hcover x
      · exact ⟨.inl i,by simpa only [modulus,ha₀] using hi⟩
      · refine ⟨.inr (t,some (some i)),hhit t (some (some i)) ?_ ?_⟩
        · simpa only [ternaryResidue,ht] using hx
        · exact hi


lemma prime_support
    (hqs : ∀ p,p.Prime → p ∣ q → ∃ i,p ∣ m i)
    (k : Index (I := I) q) (p : ℕ) (hp : p.Prime)
    (hpk : p ∣ modulus m q k) : p=3 ∨ ∃ i,p ∣ m i := by
  cases k with
  | inl i => exact Or.inr ⟨i,hpk⟩
  | inr z =>
    rcases z with ⟨t,k⟩
    change p ∣ 3^(t.val+1)*cofactor m q k at hpk
    rcases hp.dvd_mul.mp hpk with hh | hh
    · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow hh
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact False.elim (hp.ne_one h)
      · exact Or.inl h
    · right
      cases k with
      | none => exact hqs p hp hh
      | some k =>
        cases k with
        | none => have he : p=1 := Nat.dvd_one.mp hh; exact False.elim (hp.ne_one he)
        | some i => exact ⟨i,hh⟩

end

lemma fresh_power {I : Type} [Fintype I] (m : I → ℕ)
    (hm : ∀ i,1 < m i ∧ Odd (m i)) (h3 : ∀ i,¬ 3 ∣ m i) (i₀ : I) :
    ∃ q : ℕ, Odd q ∧ ¬ 3 ∣ q ∧ 3 < q ∧
      (∀ i,m i < q) ∧ (∀ p,p.Prime → p ∣ q → ∃ i,p ∣ m i) := by
  classical
  let M := 6+∑ i,m i
  let q := (m i₀)^M
  have h2 : 2 ≤ m i₀ := by have := (hm i₀).1; omega
  have hMq : M < q := (Nat.lt_two_pow_self (n := M)).trans_le (Nat.pow_le_pow_left h2 M)
  refine ⟨q,(hm i₀).2.pow,?_,by dsimp [M] at hMq; omega,?_,?_⟩
  · intro hh
    exact h3 i₀ (Nat.prime_three.dvd_of_dvd_pow hh)
  · intro i
    have hsum : m i ≤ ∑ j,m j := Finset.single_le_sum
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [M] at hMq
    omega
  · intro p hp hpq
    exact ⟨i₀,hp.dvd_of_dvd_pow hpq⟩

/-- No prime larger than3 need be introduced by the lift. -/
theorem exists_arithmetic_same_prime_support {I : Type} [Fintype I]
    (m : I → ℕ) (a₀ a₁ : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i) :
    ∃ (K : Type) (fK : Fintype K) (n : K → ℕ) (a : K → ℤ),
      IsOddArithmeticCover n a ∧
      ∀ k p,p.Prime → p ∣ n k → p=3 ∨ ∃ i,p ∣ m i := by
  obtain ⟨i₀,_⟩ := hcover 0
  obtain ⟨q,hqOdd,hq3n,hq3,hqbig,hqs⟩ := fresh_power m hm h3 i₀
  obtain ⟨a,ha₀,ha⟩ := exists_residues m q a₀ a₁ hm h3 hqOdd hq3n hq3
  have hd := modulus_data m q hinj hm h3 hqOdd hq3n hq3 hqbig
  refine ⟨Index (I := I) q,inferInstance,modulus m q,a,⟨hd.1,hd.2,?_⟩,?_⟩
  · exact lifted_covers m q a₀ a₁ hm h3 hqOdd hq3n hq3 hcover a ha₀ ha
  · exact prime_support m q hqs

theorem twofold_large_prime {I : Type} [Fintype I]
    (m : I → ℕ) (a₀ a₁ : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i) :
    ∃ i p,p.Prime ∧ p ∣ m i ∧ 19 < p := by
  obtain ⟨K,fK,n,a,hc,hs⟩ := exists_arithmetic_same_prime_support m a₀ a₁ hinj hm h3 hcover
  letI : Fintype K := fK
  obtain ⟨k,p,hp,hpk,hp19⟩ := Erdos7Capped19Schedule.arithmetic_large_prime n a hc
  rcases hs k p hp hpk with h | ⟨i,hi⟩
  · omega
  · exact ⟨i,p,hp,hi,hp19⟩

theorem twofold_five {I : Type} [Fintype I]
    (m : I → ℕ) (a₀ a₁ : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i) :
    ∃ i,5 ∣ m i := by
  obtain ⟨K,fK,n,a,hc,hs⟩ := exists_arithmetic_same_prime_support m a₀ a₁ hinj hm h3 hcover
  letI : Fintype K := fK
  obtain ⟨k,hk⟩ := Erdos7NoFive.arithmetic_exists_five n a hc
  rcases hs k 5 (by decide) hk with h | h
  · omega
  · exact h

#print axioms exists_arithmetic_same_prime_support
#print axioms twofold_large_prime
#print axioms twofold_five
end Erdos7TwofoldCompositeLift
