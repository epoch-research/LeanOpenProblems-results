import Submission.MultipleExceptionCompression

/-! Conditional deletion of any exceptional family lying over one prime
coordinate, when the smaller prime leaves enough unused digits. This does
not supply a covering witness or settle Erdős Problem 7. -/
namespace Erdos7CommonPrimeExceptionCompression
open Erdos7Reduction Erdos7Compression Erdos7Digits
open Erdos7MultipleExceptionCompression
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Unlike the uniform gap criterion, only one coordinate needs spare digits.
Every exceptional class must constrain that coordinate. -/
theorem compress_common_coordinate {ι I J : Type*}
    [Fintype ι] [Fintype I] [Fintype J] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) (E : ι → ℕ)
    (e : I → ι → ℕ) (e₀ : J → ι → ℕ)
    (he : ∀ k i, e k i ≤ E i) (he₀ : ∀ k i, e₀ k i ≤ E i)
    (hei : Function.Injective e) (henz : ∀ k, ∃ i, e k i ≠ 0)
    (a : I → ℤ) (a₀ : J → ℤ)
    (hc : ∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ∃ k, ((∏ i, p i ^ e₀ k i : ℕ) : ℤ) ∣ x-a₀ k)
    (q : ℕ) (hq : q.Prime ∧ Odd q) (hnew : ∀ i, p i ≠ q)
    (i₀ : ι) (hE : 0 < E i₀)
    (hgap : q + Fintype.card J ≤ p i₀) (hused : ∀ k, e₀ k i₀ ≠ 0) :
    ∃ b : I → ℤ, IsOddArithmeticCover
      (fun k => ∏ i, Function.update p i₀ q i ^ e k i) b := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  let j₀ : Fin (E i₀) := ⟨0,hE⟩
  let S := Finset.univ.image (fun k => zmodDigits (p i₀) (E i₀) (a₀ k) j₀)
  have hS : S.card ≤ Fintype.card J :=
    Finset.card_image_le.trans_eq Finset.card_univ
  obtain ⟨g₀,hg₀⟩ := embedding_avoiding_set (p i₀) q S (by omega)
  let q' := Function.update p i₀ q
  have hq' : ∀ i, (q' i).Prime ∧ Odd (q' i) := by
    intro i
    by_cases hi : i=i₀
    · simpa [q',hi] using hq
    · simpa [q',hi] using hp i
  have hqi : Function.Injective q' := by
    intro i j hij
    by_cases hi : i=i₀ <;> by_cases hj : j=i₀
    · exact hi.trans hj.symm
    · subst i
      exact False.elim (hnew j (by simpa [q',hj] using hij.symm))
    · subst j
      exact False.elim (hnew i (by simpa [q',hi] using hij))
    · apply hpi
      simpa [q',hi,hj] using hij
  let g : (i : ι) → Fin (E i) → (Fin (q' i) ↪ Fin (p i)) := fun i _ =>
    if h : i=i₀ then by
      subst i
      exact (Fin.castLEEmb (by simp [q'] : q' i₀ ≤ q)).trans g₀
    else Fin.castLEEmb (by simp [q',h] : q' i ≤ p i)
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  apply shrink_delete_exceptions p q' E (fun i => (hp i).1.pos) hq' hqi hcp
    e e₀ he he₀ hei henz a a₀ hc g
  intro k
  refine ⟨i₀,j₀,by have := hused k; dsimp [j₀]; omega,?_⟩
  rintro ⟨x,hx⟩
  have hm : zmodDigits (p i₀) (E i₀) (a₀ k) j₀ ∈ S :=
    Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  apply hg₀ _ hm
  simp only [g,dif_pos rfl,Function.Embedding.trans_apply] at hx
  exact ⟨_,hx⟩

/-- A no-three base family repaired by at most `p-3` exceptional classes,
all divisible by one prime `p`, would give a strict odd cover on the base
index type alone. Exception moduli need not be distinct. -/
theorem odd_cover_from_common_prime_exceptions_avoiding {I J : Type*}
    [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hd3 : ∀ j, ¬ 3 ∣ d j)
    (r : ℕ) (hr : r.Prime ∧ Odd r ∧ 3 < r)
    (hrd : ∀ j, r ∣ d j) (hgap : 3 + Fintype.card J ≤ r)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ (n : I → ℕ) (c : I → ℤ), IsOddArithmeticCover n c ∧
      ∀ k, ¬ r ∣ n k := by
  classical
  let P := insert r ((Finset.univ.biUnion (fun k => (m k).primeFactors)) ∪
    (Finset.univ.biUnion (fun j => (d j).primeFactors)))
  let p (i : P) := i.val
  let e (k : I) (i : P) := (m k).factorization i.val
  let e₀ (k : J) (i : P) := (d k).factorization i.val
  let E (i : P) := 1 + (Finset.univ.sup (fun k => e k i)) +
    (Finset.univ.sup (fun k => e₀ k i))
  have hp (i : P) : (p i).Prime ∧ Odd (p i) ∧ p i ≠ 3 := by
    rcases Finset.mem_insert.mp i.property with hi | hi
    · refine ⟨?_,?_,?_⟩
      · simpa [p,hi] using hr.1
      · simpa [p,hi] using hr.2.1
      · change i.val ≠ 3
        omega
    · rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hi
        have hh := Nat.mem_primeFactors.mp hk
        exact ⟨hh.1,(hm k).2.of_dvd_nat hh.2.1,
          fun he => h3 k (he ▸ hh.2.1)⟩
      · obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hi
        have hh := Nat.mem_primeFactors.mp hk
        exact ⟨hh.1,(hd k).2.of_dvd_nat hh.2.1,
          fun he => hd3 k (he ▸ hh.2.1)⟩
  have hprod (k : I) : m k = ∏ i : P, p i ^ e k i := by
    apply factorization_product_over_superset (m k) (by have := (hm k).1; omega) P
    intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hs⟩))
  have hprod₀ (k : J) : d k = ∏ i : P, p i ^ e₀ k i := by
    apply factorization_product_over_superset (d k) (by have := (hd k).1; omega) P
    intro s hs
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hs⟩))
  have hei : Function.Injective e := by
    intro k l hkl
    apply hinj
    rw [hprod k,hprod l,hkl]
  have henz (k : I) : ∃ i : P, e k i ≠ 0 := by
    by_contra! hz
    have hh := (hm k).1
    rw [hprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  let i₀ : P := ⟨r,Finset.mem_insert_self _ _⟩
  have hused (k : J) : e₀ k i₀ ≠ 0 := Nat.ne_of_gt
    (hr.1.factorization_pos_of_dvd (by have := (hd k).1; omega) (hrd k))
  have he (k : I) (i : P) : e k i ≤ E i := by
    have hh : e k i ≤ Finset.univ.sup (fun k => e k i) :=
      Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
    dsimp [E]
    omega
  have he₀ (k : J) (i : P) : e₀ k i ≤ E i := by
    have hh : e₀ k i ≤ Finset.univ.sup (fun k => e₀ k i) :=
      Finset.le_sup (f := fun k => e₀ k i) (Finset.mem_univ k)
    dsimp [E]
    omega
  have hcov : ∀ x : ℤ, (∃ k, ((∏ i : P, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ∃ k, ((∏ i : P, p i ^ e₀ k i : ℕ) : ℤ) ∣ x-b k := by
    simpa only [← hprod,← hprod₀] using hcover
  obtain ⟨c,hc⟩ := compress_common_coordinate p (fun i => ⟨(hp i).1,(hp i).2.1⟩)
    Subtype.val_injective E e e₀ he he₀ hei henz a b hcov
    3 ⟨by decide,by decide⟩ (fun i => (hp i).2.2) i₀
    (by dsimp [E]; omega) hgap hused
  refine ⟨_,c,hc,?_⟩
  intro k hdiv
  obtain ⟨j,_,hj⟩ := (hr.1.prime.dvd_finset_prod_iff
    (fun j : P => Function.update p i₀ 3 j ^ e k j)).mp hdiv
  have hbase : r ∣ Function.update p i₀ 3 j := hr.1.dvd_of_dvd_pow hj
  by_cases heq : j=i₀
  · subst j
    have hh : r ∣ 3 := by simpa using hbase
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hh
    omega
  · have hh : r ∣ p j := by simpa [heq] using hbase
    rcases (Nat.dvd_prime (hp j).1).mp hh with hh | hh
    · exact hr.1.ne_one hh
    · apply heq
      apply Subtype.ext
      exact hh.symm

/-- The same construction with its avoidance property omitted. -/
theorem odd_cover_from_common_prime_exceptions {I J : Type*}
    [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hd3 : ∀ j, ¬ 3 ∣ d j)
    (r : ℕ) (hr : r.Prime ∧ Odd r ∧ 3 < r)
    (hrd : ∀ j, r ∣ d j) (hgap : 3 + Fintype.card J ≤ r)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ (n : I → ℕ) (c : I → ℤ), IsOddArithmeticCover n c := by
  obtain ⟨n,c,hc,_⟩ := odd_cover_from_common_prime_exceptions_avoiding
    m a hinj hm h3 d b hd hd3 r hr hrd hgap hcover
  exact ⟨n,c,hc⟩

#print axioms compress_common_coordinate
#print axioms odd_cover_from_common_prime_exceptions_avoiding
#print axioms odd_cover_from_common_prime_exceptions
end Erdos7CommonPrimeExceptionCompression
