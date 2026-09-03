import Submission.ArithmeticReduction

/-!
# Removing one exceptional class by prime-alphabet compression

Distinctness is required only for the surviving base labels. An exceptional
label may duplicate one of them: after excluding an exceptional digit, the
shrunk cover consists of the base labels alone. This is a conditional
construction, not an odd covering witness.
-/

namespace Erdos7SingleExceptionCompression
open Erdos7Reduction Erdos7Compression Erdos7Digits
open scoped BigOperators
set_option maxHeartbeats 4000000

/-- Alphabet shrinking with one additional, possibly duplicate, class. -/
theorem shrink_delete_exception {ι I : Type*} [Fintype ι] [Fintype I]
    (p q E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, (q i).Prime ∧ Odd (q i)) (hqi : Function.Injective q)
    (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : I → ι → ℕ) (e₀ : ι → ℕ)
    (he : ∀ k i, e k i ≤ E i) (he₀ : ∀ i, e₀ i ≤ E i)
    (hei : Function.Injective e) (henz : ∀ k, ∃ i, e k i ≠ 0)
    (a : I → ℤ) (a₀ : ℤ)
    (hc : ∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ((∏ i, p i ^ e₀ i : ℕ) : ℤ) ∣ x-a₀)
    (g : (i : ι) → Fin (q i) ↪ Fin (p i)) [∀ i, NeZero (p i)]
    (i₀ : ι) (j₀ : Fin (E i₀)) (hj₀ : j₀.val < e₀ i₀)
    (hexcl : zmodDigits (p i₀) (E i₀) a₀ j₀ ∉ Set.range (g i₀)) :
    ∃ b : I → ℤ, IsOddArithmeticCover (fun k => ∏ i, q i ^ e k i) b := by
  classical
  let es : I ⊕ Unit → ι → ℕ := Sum.elim e (fun _ => e₀)
  let as : I ⊕ Unit → ℤ := Sum.elim a (fun _ => a₀)
  have hes : ∀ k i, es k i ≤ E i := by
    intro k i
    cases k with
    | inl k => exact he k i
    | inr u => exact he₀ i
  have hcs : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ es k i : ℕ) : ℤ) ∣ x-as k := by
    intro x
    rcases hc x with ⟨k,hk⟩ | hk
    · exact ⟨Sum.inl k,hk⟩
    · exact ⟨Sum.inr (),hk⟩
  have hcq : Pairwise (Function.onFun Nat.Coprime q) := by
    intro i j hij
    exact (Nat.coprime_primes (hq i).1 (hq j).1).mpr (fun h => hij (hqi h))
  obtain ⟨b,hb⟩ := shrink_alphabets_delete_class p q E hp (fun i => (hq i).1.pos)
    hcp hcq es hes as hcs g (Sum.inr ()) i₀ j₀ hj₀ hexcl
  let b₀ (k : I) := b ⟨Sum.inl k,by simp⟩
  refine ⟨b₀,?_,?_,?_⟩
  · intro k l hkl
    apply hei
    funext i
    have hh := congrArg (fun n : ℕ => n.factorization (q i)) hkl
    simpa only [factorization_prime_power_product q (fun i => (hq i).1) hqi] using hh
  · intro k
    change 1 < (∏ i, q i ^ e k i) ∧ Odd (∏ i, q i ^ e k i)
    have hpos : 0 < ∏ i, q i ^ e k i :=
      Finset.prod_pos (fun i _ => pow_pos (hq i).1.pos _)
    have hne : (∏ i, q i ^ e k i) ≠ 1 := by
      intro h
      obtain ⟨i,hi⟩ := henz k
      have hh := factorization_prime_power_product q (fun i => (hq i).1) hqi (e k) i
      rw [h,Nat.factorization_one,Finsupp.zero_apply] at hh
      exact hi hh.symm
    refine ⟨by omega,?_⟩
    exact Finset.prod_induction (fun i => q i ^ e k i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hq i).2.pow)
  · intro x
    obtain ⟨⟨k,hk⟩,hx⟩ := hb x
    cases k with
    | inl k => exact ⟨k,hx⟩
    | inr u => cases u; exact False.elim (hk rfl)

/-- Replacing an exceptional prime coordinate by a smaller unused odd prime
removes the entire extra class, without removing any base label. -/
theorem compress_exception {ι I : Type*} [Fintype ι] [Fintype I] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) (E : ι → ℕ)
    (e : I → ι → ℕ) (e₀ : ι → ℕ)
    (he : ∀ k i, e k i ≤ E i) (he₀ : ∀ i, e₀ i ≤ E i)
    (hei : Function.Injective e) (henz : ∀ k, ∃ i, e k i ≠ 0)
    (a : I → ℤ) (a₀ : ℤ)
    (hc : ∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ((∏ i, p i ^ e₀ i : ℕ) : ℤ) ∣ x-a₀)
    (q : ℕ) (hq : q.Prime ∧ Odd q) (hnew : ∀ i, p i ≠ q)
    (i₀ : ι) (hqp : q < p i₀) (hused : e₀ i₀ ≠ 0) :
    ∃ b : I → ℤ, IsOddArithmeticCover
      (fun k => ∏ i, Function.update p i₀ q i ^ e k i) b := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨(hp i).1.ne_zero⟩
  have hEpos : 0 < E i₀ := by have := he₀ i₀; omega
  let j₀ : Fin (E i₀) := ⟨0,hEpos⟩
  let r := zmodDigits (p i₀) (E i₀) a₀ j₀
  obtain ⟨g₀,hg₀⟩ := exists_fin_embedding_avoiding (p i₀) q hqp r
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
  let g : (i : ι) → Fin (q' i) ↪ Fin (p i) := fun i =>
    if h : i=i₀ then by
      subst i
      exact (Fin.castLEEmb (by simp [q'] : q' i₀ ≤ q)).trans g₀
    else Fin.castLEEmb (by simp [q',h] : q' i ≤ p i)
  have hg : r ∉ Set.range (g i₀) := by
    rintro ⟨x,hx⟩
    apply hg₀
    simp only [g,dif_pos rfl,Function.Embedding.trans_apply] at hx
    exact ⟨_,hx⟩
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  exact shrink_delete_exception p q' E (fun i => (hp i).1.pos) hq' hqi hcp e e₀
    he he₀ hei henz a a₀ hc g i₀ j₀ (by dsimp [j₀]; omega) hg

/-- Any no-3 distinct odd family repaired by one nontrivial no-3 odd class
would produce an odd strict cover with at most the BASE number of labels.
No such near-cover is supplied by this theorem. -/
theorem odd_cover_from_single_exception {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : ℕ) (hd : 1 < d ∧ Odd d) (hd3 : ¬ 3 ∣ d) (b : ℤ)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (d : ℤ) ∣ x-b) :
    ∃ (n : I → ℕ) (c : I → ℤ), IsOddArithmeticCover n c := by
  classical
  let P := (Finset.univ.biUnion (fun k => (m k).primeFactors)) ∪ d.primeFactors
  let p (i : P) := i.val
  let e (k : I) (i : P) := (m k).factorization i.val
  let e₀ (i : P) := d.factorization i.val
  let E (i : P) := max (e₀ i) (Finset.univ.sup (fun k => e k i))
  have hp (i : P) : (p i).Prime ∧ Odd (p i) := by
    rcases Finset.mem_union.mp i.property with h | h
    · obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp h
      have hh := Nat.mem_primeFactors.mp hk
      exact ⟨hh.1,(hm k).2.of_dvd_nat hh.2.1⟩
    · have hh := Nat.mem_primeFactors.mp h
      exact ⟨hh.1,hd.2.of_dvd_nat hh.2.1⟩
  have hnew : ∀ i : P, p i ≠ 3 := by
    intro i hi
    rcases Finset.mem_union.mp i.property with h | h
    · obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp h
      exact h3 k (by simpa only [← hi] using (Nat.mem_primeFactors.mp hk).2.1)
    · exact hd3 (by simpa only [← hi] using (Nat.mem_primeFactors.mp h).2.1)
  have hprod (k : I) : m k = ∏ i : P, p i ^ e k i := by
    apply factorization_product_over_superset (m k) (by have := (hm k).1; omega) P
    intro r hr
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hr⟩)
  have hprod₀ : d = ∏ i : P, p i ^ e₀ i := by
    apply factorization_product_over_superset d (by omega) P
    exact fun r hr => Finset.mem_union_right _ hr
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
  obtain ⟨p₀,hp₀,hp₀d⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hp₀P : p₀ ∈ P := Finset.mem_union_right _
    (Nat.mem_primeFactors.mpr ⟨hp₀,hp₀d,by omega⟩)
  let i₀ : P := ⟨p₀,hp₀P⟩
  have hbig : 3 < p i₀ := by
    have ht := hp₀.two_le
    have ho := hd.2.of_dvd_nat hp₀d
    have hne2 : p₀ ≠ 2 := by intro h; subst p₀; norm_num at ho
    have hne3 : p₀ ≠ 3 := by intro h; subst p₀; exact hd3 hp₀d
    change 3 < p₀
    omega
  have hused : e₀ i₀ ≠ 0 := Nat.ne_of_gt
    (hp₀.factorization_pos_of_dvd (by omega : d ≠ 0) hp₀d)
  have hc : ∀ x : ℤ, (∃ k, ((∏ i : P, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ((∏ i : P, p i ^ e₀ i : ℕ) : ℤ) ∣ x-b := by
    simpa only [← hprod,← hprod₀] using hcover
  obtain ⟨c,hc⟩ := compress_exception p hp Subtype.val_injective E e e₀
    (fun k i => (Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)).trans (le_max_right _ _))
    (fun i => le_max_left _ _) hei henz a b hc 3 ⟨by decide,by decide⟩ hnew i₀ hbig hused
  exact ⟨_,c,hc⟩

#print axioms shrink_delete_exception
#print axioms compress_exception
#print axioms odd_cover_from_single_exception
end Erdos7SingleExceptionCompression
