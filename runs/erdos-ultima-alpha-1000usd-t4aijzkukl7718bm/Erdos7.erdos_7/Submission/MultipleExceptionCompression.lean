import Submission.SingleExceptionCompression

/-!
# Simultaneous removal of exceptional classes

Digit injections may depend on the digit position. Distinctness is needed
only for surviving base moduli. All conclusions below are conditional
constructions, not odd covering witnesses.
-/
namespace Erdos7MultipleExceptionCompression
open Erdos7Reduction Erdos7Compression Erdos7Digits
open scoped BigOperators
set_option maxHeartbeats 4000000

/-- A finite alphabet embeds in the complement of a sufficiently small set. -/
lemma embedding_avoiding_set (p q : ℕ) (S : Finset (Fin p))
    (h : q+S.card ≤ p) :
    ∃ g : Fin q ↪ Fin p, ∀ r ∈ S, r ∉ Set.range g := by
  classical
  have hc : Fintype.card (Fin q) ≤ Fintype.card ↥(Sᶜ) := by
    rw [Fintype.card_fin,Fintype.card_coe,Finset.card_compl,Fintype.card_fin]
    omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨g.trans (Function.Embedding.subtype _),?_⟩
  intro r hr
  rintro ⟨x,hx⟩
  have hx' := (g x).property
  simp only [Finset.mem_compl] at hx'
  have he : (g x).val = r := hx
  exact hx' (he.symm ▸ hr)

/-- Simultaneous excluded digits delete every exceptional class. -/
theorem shrink_delete_exceptions {ι I J : Type*} [Fintype ι] [Fintype I]
    (p q E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, (q i).Prime ∧ Odd (q i)) (hqi : Function.Injective q)
    (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : I → ι → ℕ) (e₀ : J → ι → ℕ)
    (he : ∀ k i, e k i ≤ E i) (he₀ : ∀ k i, e₀ k i ≤ E i)
    (hei : Function.Injective e) (henz : ∀ k, ∃ i, e k i ≠ 0)
    (a : I → ℤ) (a₀ : J → ℤ)
    (hc : ∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ∃ k, ((∏ i, p i ^ e₀ k i : ℕ) : ℤ) ∣ x-a₀ k)
    (g : (i : ι) → Fin (E i) → (Fin (q i) ↪ Fin (p i)))
    [∀ i, NeZero (p i)]
    (hexcl : ∀ k, ∃ i, ∃ j : Fin (E i), j.val < e₀ k i ∧
      zmodDigits (p i) (E i) (a₀ k) j ∉ Set.range (g i j)) :
    ∃ b : I → ℤ, IsOddArithmeticCover (fun k => ∏ i, q i ^ e k i) b := by
  classical
  letI (i : ι) : NeZero (q i) := ⟨(hq i).1.ne_zero⟩
  have hcq : Pairwise (Function.onFun Nat.Coprime q) := by
    intro i j hij
    exact (Nat.coprime_primes (hq i).1 (hq j).1).mpr (fun h => hij (hqi h))
  let B (k : I) (i : ι) (j : Fin (E i)) : Fin (q i) :=
    Function.invFun (g i j) (zmodDigits (p i) (E i) (a k) j)
  choose b hb using fun k =>
    exists_integer_with_digits q E (fun i => (hq i).1.pos) hcq (B k)
  have hcov : ∀ x : ℤ, ∃ k, ((∏ i, q i ^ e k i : ℕ) : ℤ) ∣ x-b k := by
    intro x
    let X (i : ι) := zmodDigits (q i) (E i) (x : ZMod (q i ^ E i))
    obtain ⟨z,hz⟩ := exists_integer_with_digits p E hp hcp (fun i j => g i j (X i j))
    rcases hc z with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
      refine ⟨k,(divisor_product_iff_digits q E (e k) (he k) hcq x (b k)).mpr ?_⟩
      intro i j hj
      rw [hb]
      have hh := hkd i j hj
      rw [hz] at hh
      change X i j = B k i j
      dsimp only [B]
      rw [← hh]
      exact (Function.leftInverse_invFun (g i j).injective (X i j)).symm
    · obtain ⟨i,j,hj,hex⟩ := hexcl k
      have hkd := (divisor_product_iff_digits p E (e₀ k) (he₀ k) hcp z (a₀ k)).mp hk
      have hh := hkd i j hj
      rw [hz] at hh
      exact False.elim (hex ⟨X i j,hh⟩)
  refine ⟨b,?_,?_,hcov⟩
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
    exact ⟨by omega, Finset.prod_induction (fun i => q i ^ e k i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hq i).2.pow)⟩

/-- If each alphabet leaves at least as many spare symbols as exceptional
classes, all nontrivial exceptional classes can be removed simultaneously. -/
theorem shrink_small_exception_family {ι I J : Type*}
    [Fintype ι] [Fintype I] [Fintype J]
    (p q E : ι → ℕ) (hp : ∀ i, 0 < p i)
    (hq : ∀ i, (q i).Prime ∧ Odd (q i)) (hqi : Function.Injective q)
    (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : I → ι → ℕ) (e₀ : J → ι → ℕ)
    (he : ∀ k i, e k i ≤ E i) (he₀ : ∀ k i, e₀ k i ≤ E i)
    (hei : Function.Injective e) (henz : ∀ k, ∃ i, e k i ≠ 0)
    (he₀nz : ∀ k, ∃ i, e₀ k i ≠ 0)
    (a : I → ℤ) (a₀ : J → ℤ)
    (hc : ∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ∃ k, ((∏ i, p i ^ e₀ k i : ℕ) : ℤ) ∣ x-a₀ k)
    (hgap : ∀ i, q i + Fintype.card J ≤ p i) :
    ∃ b : I → ℤ, IsOddArithmeticCover (fun k => ∏ i, q i ^ e k i) b := by
  classical
  letI (i : ι) : NeZero (p i) := ⟨Nat.ne_of_gt (hp i)⟩
  let S (i : ι) (j : Fin (E i)) :=
    Finset.univ.image (fun k => zmodDigits (p i) (E i) (a₀ k) j)
  have hs (i : ι) (j : Fin (E i)) : (S i j).card ≤ Fintype.card J :=
    Finset.card_image_le.trans_eq (Finset.card_univ)
  choose g hg using fun i j => embedding_avoiding_set (p i) (q i) (S i j)
    (by have := hs i j; have := hgap i; omega)
  apply shrink_delete_exceptions p q E hp hq hqi hcp e e₀ he he₀ hei henz a a₀ hc g
  intro k
  obtain ⟨i,hi⟩ := he₀nz k
  have hE : 0 < E i := by have := he₀ k i; omega
  let j : Fin (E i) := ⟨0,hE⟩
  refine ⟨i,j,by dsimp [j]; omega,?_⟩
  exact hg i j _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)

/-- Shift a sorted finite list of no-3 odd primes one place to the left,
putting 3 at the beginning. Every coordinate gains at least two spare digits. -/
lemma previous_primes {n : ℕ} (p : Fin n → ℕ) (hp : StrictMono p)
    (hprime : ∀ i, (p i).Prime ∧ Odd (p i) ∧ 3 < p i) :
    ∃ q : Fin n → ℕ, Function.Injective q ∧
      (∀ i, (q i).Prime ∧ Odd (q i)) ∧ ∀ i, q i+2 ≤ p i := by
  let q (i : Fin n) : ℕ := if h : i.val=0 then 3 else p ⟨i.val-1,by omega⟩
  have hq (i : Fin n) : (q i).Prime ∧ Odd (q i) := by
    dsimp only [q]
    split
    · exact ⟨by decide,by decide⟩
    · exact ⟨(hprime _).1,(hprime _).2.1⟩
  have hg (i : Fin n) : q i+2 ≤ p i := by
    dsimp only [q]
    split
    · have ho := (hprime i).2.1
      have hb := (hprime i).2.2
      obtain ⟨k,hk⟩ := ho
      omega
    · rename_i hi
      have hh := hp (show (⟨i.val-1,by omega⟩ : Fin n) < i from by change i.val-1 < i.val; omega)
      have h₁ := (hprime i).2.1
      have h₂ := (hprime (⟨i.val-1,by omega⟩ : Fin n)).2.1
      obtain ⟨u,hu⟩ := h₁
      obtain ⟨v,hv⟩ := h₂
      omega
  have hmono : StrictMono q := by
    intro i j hij
    by_cases hi : i.val=0
    · have hj : j.val ≠ 0 := by have := hij; change i.val < j.val at this; omega
      simp only [q,dif_pos hi,dif_neg hj]
      exact (hprime _).2.2
    · have hj : j.val ≠ 0 := by have := hij; change i.val < j.val at this; omega
      simp only [q,dif_neg hi,dif_neg hj]
      apply hp
      change i.val-1 < j.val-1
      change i.val < j.val at hij
      omega
  exact ⟨q,hmono.injective,hq,hg⟩

/-- A distinct odd no-3 family repaired by at most two nontrivial odd no-3
classes gives an odd strict cover on the base labels alone. The exceptional
labels need not be distinct from one another or from the base labels. -/
theorem odd_cover_from_two_exceptions {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (b : J → ℤ) (hd : ∀ j, 1 < d j ∧ Odd (d j))
    (hd3 : ∀ j, ¬ 3 ∣ d j) (hJ : Fintype.card J ≤ 2)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ ∃ j, (d j : ℤ) ∣ x-b j) :
    ∃ (n : I → ℕ) (c : I → ℤ), IsOddArithmeticCover n c := by
  classical
  let P := (Finset.univ.biUnion (fun k => (m k).primeFactors)) ∪
    (Finset.univ.biUnion (fun j => (d j).primeFactors))
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  let e (k : I) (i : Fin P.card) := (m k).factorization (p i)
  let e₀ (j : J) (i : Fin P.card) := (d j).factorization (p i)
  let E (i : Fin P.card) := max (Finset.univ.sup (fun k => e k i))
    (Finset.univ.sup (fun j => e₀ j i))
  have hp (i : Fin P.card) : (p i).Prime ∧ Odd (p i) ∧ 3 < p i := by
    have hpi : p i ∈ P := P.orderEmbOfFin_mem rfl i
    have hh : (p i).Prime ∧ Odd (p i) ∧ p i ≠ 3 := by
      rcases Finset.mem_union.mp hpi with h | h
      · obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp h
        have hh := Nat.mem_primeFactors.mp hk
        exact ⟨hh.1,(hm k).2.of_dvd_nat hh.2.1,fun he => h3 k (he ▸ hh.2.1)⟩
      · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp h
        have hh := Nat.mem_primeFactors.mp hj
        exact ⟨hh.1,(hd j).2.of_dvd_nat hh.2.1,fun he => hd3 j (he ▸ hh.2.1)⟩
    refine ⟨hh.1,hh.2.1,?_⟩
    have htwo := hh.1.two_le
    obtain ⟨k,hk⟩ := hh.2.1
    have hne := hh.2.2
    omega
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr
      (fun h => hij (hmono.injective h))
  have prod_eq (v : ℕ) (hv : v ≠ 0) (hsub : v.primeFactors ⊆ P) :
      v = ∏ i : Fin P.card, p i ^ v.factorization (p i) := by
    have hvP := factorization_product_over_superset v hv P hsub
    conv_lhs => rw [hvP]
    symm
    apply Fintype.prod_equiv (P.orderIsoOfFin rfl).toEquiv
    intro i
    rfl
  have hprod (k : I) : m k = ∏ i, p i ^ e k i := by
    apply prod_eq (m k) (by have := (hm k).1; omega)
    intro r hr
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hr⟩)
  have hprod₀ (j : J) : d j = ∏ i, p i ^ e₀ j i := by
    apply prod_eq (d j) (by have := (hd j).1; omega)
    intro r hr
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hr⟩)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hinj
    rw [hprod k,hprod l,hkl]
  have henz (k : I) : ∃ i, e k i ≠ 0 := by
    by_contra! hz
    have hh := (hm k).1
    rw [hprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  have he₀nz (j : J) : ∃ i, e₀ j i ≠ 0 := by
    by_contra! hz
    have hh := (hd j).1
    rw [hprod₀ j] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  obtain ⟨q,hqi,hq,hgap⟩ := previous_primes p hmono hp
  have hc : ∀ x : ℤ, (∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) ∨
      ∃ j, ((∏ i, p i ^ e₀ j i : ℕ) : ℤ) ∣ x-b j := by
    simpa only [← hprod,← hprod₀] using hcover
  obtain ⟨c,hc⟩ := shrink_small_exception_family p q E (fun i => (hp i).1.pos)
    hq hqi hcop e e₀
    (fun k i => (Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)).trans (le_max_left _ _))
    (fun j i => (Finset.le_sup (f := fun j => e₀ j i) (Finset.mem_univ j)).trans (le_max_right _ _))
    hei henz he₀nz a b hc (fun i => by have := hgap i; omega)
  exact ⟨_,c,hc⟩

#print axioms embedding_avoiding_set
#print axioms shrink_delete_exceptions
#print axioms shrink_small_exception_family
#print axioms previous_primes
#print axioms odd_cover_from_two_exceptions
end Erdos7MultipleExceptionCompression
