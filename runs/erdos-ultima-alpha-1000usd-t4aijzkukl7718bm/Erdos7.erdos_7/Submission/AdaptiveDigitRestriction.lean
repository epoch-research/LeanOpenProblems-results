import Submission.ArithmeticReduction

/-! Prefix-dependent positions of digit deletion.  This supplies a more general
period reduction, not a solution of the odd covering-system problem. -/
namespace Erdos7AdaptiveDigitRestriction
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- A fixed-length low shortPrefix. -/
def shortPrefix {α : Type*} {n : ℕ} (s : ℕ) (hs : s ≤ n) (x : Fin n → α) :
    Fin s → α := fun j => x ⟨j.val, j.isLt.trans_le hs⟩

lemma prefix_insert {α : Type*} {n : ℕ} (s : ℕ) (hs : s ≤ n)
    (t : Fin n) (hst : s ≤ t.val) (r : α) (x : Fin n → α) :
    shortPrefix s hs (insertDigit t r x) = shortPrefix s hs x := by
  funext j
  simp only [shortPrefix, insertDigit]
  have hj : j.val < t.val := j.isLt.trans_le hst
  simp [hj]

lemma prefix_agree {α : Type*} {n : ℕ} (s : ℕ) (hs : s ≤ n)
    (x y : Fin n → α) (h : ∀ j : Fin n, j.val < s → x j = y j) :
    shortPrefix s hs x = shortPrefix s hs y := by
  funext j
  exact h _ j.isLt

section Arithmetic
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (i₀ : ι) (s : ℕ) (hs : s < E i₀)
    [∀ i, NeZero (p i)]

abbrev Branch := Fin s → Fin (p i₀)

def branch (a : ℤ) : Branch p i₀ s :=
  shortPrefix s hs.le (zmodDigits (p i₀) (E i₀) a)

variable (pos : Branch p i₀ s → Fin (E i₀))
    (hpos : ∀ u, s ≤ (pos u).val)
    (digit : (u : Branch p i₀ s) → (Fin (pos u).val → Fin (p i₀)) → Fin (p i₀))

def chosenPosition (a : ℤ) : Fin (E i₀) := pos (branch p E i₀ s hs a)

def active (e : ι → ℕ) (a : ℤ) : Prop :=
  e i₀ ≤ (chosenPosition p E i₀ s hs pos a).val ∨
    zmodDigits (p i₀) (E i₀) a (chosenPosition p E i₀ s hs pos a) =
      digit (branch p E i₀ s hs a)
        (shortPrefix (chosenPosition p E i₀ s hs pos a).val
          (chosenPosition p E i₀ s hs pos a).isLt.le
          (zmodDigits (p i₀) (E i₀) a))

include hpos in
/-- The deleted position may vary between branches, and the retained value may
also depend on every digit below that position.  A single residue assignment
works for all projected integers. -/
theorem simultaneous_adaptive_restriction
    (hp : ∀ i, 0 < p i) (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) :
    ∃ b : κ → ℤ,
      (∀ k i, zmodDigits (p i) (E i) (b k) =
        (Function.update (fun j => zmodDigits (p j) (E j) (a k)) i₀
          (deleteDigit (chosenPosition p E i₀ s hs pos (a k)) 0
            (zmodDigits (p i₀) (E i₀) (a k)))) i) ∧
      ∀ digit : (u : Branch p i₀ s) →
        (Fin (pos u).val → Fin (p i₀)) → Fin (p i₀),
      ∀ x : ℤ, ∃ k,
        active p E i₀ s hs pos digit (e k) (a k) ∧
        ((∏ i, p i ^ eraseExponent i₀
          (chosenPosition p E i₀ s hs pos (a k)).val (e k) i : ℕ) : ℤ) ∣ x-b k := by
  classical
  let A (k : κ) (i : ι) := zmodDigits (p i) (E i) (a k : ZMod (p i ^ E i))
  let T (k : κ) := chosenPosition p E i₀ s hs pos (a k)
  let B (k : κ) := Function.update (A k) i₀ (deleteDigit (T k) 0 (A k i₀))
  choose b hb using fun k => exists_integer_with_digits p E hp hcp (B k)
  refine ⟨b, hb, fun digit x => ?_⟩
  let X (i : ι) := zmodDigits (p i) (E i) (x : ZMod (p i ^ E i))
  let u := shortPrefix s hs.le (X i₀)
  let t := pos u
  let r := digit u (shortPrefix t.val t.isLt.le (X i₀))
  let Y := Function.update X i₀ (insertDigit t r (X i₀))
  obtain ⟨z, hz⟩ := exists_integer_with_digits p E hp hcp Y
  obtain ⟨k, hk⟩ := hc z
  have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
  have hmatch : ∀ j : Fin (E i₀), j.val < e k i₀ →
      insertDigit t r (X i₀) j = A k i₀ j := by
    intro j hj
    have hh := hkd i₀ j hj
    rw [hz] at hh
    simpa only [Y, Function.update_self] using hh
  have hst : s ≤ t.val := hpos u
  have hbranch (hsk : s < e k i₀) : branch p E i₀ s hs (a k) = u := by
    change shortPrefix s hs.le (A k i₀) = shortPrefix s hs.le (X i₀)
    rw [← prefix_insert s hs.le t hst r (X i₀)]
    exact prefix_agree s hs.le _ _ (fun j hj => (hmatch j (hj.trans hsk)).symm)
  have ht (hsk : s < e k i₀) : T k = t := by
    dsimp only [T, chosenPosition]
    rw [hbranch hsk]
  refine ⟨k, ?_, (divisor_product_iff_digits p E
    (eraseExponent i₀ (T k).val (e k))
    (fun i => (eraseExponent_le i₀ (T k).val (e k) i).trans (he k i))
    hcp x (b k)).mpr ?_⟩
  · by_cases hlow : e k i₀ ≤ s
    · exact Or.inl (hlow.trans (hpos _))
    · have hsk : s < e k i₀ := by omega
      by_cases hkt : e k i₀ ≤ t.val
      · left
        change e k i₀ ≤ (T k).val
        rw [ht hsk]
        exact hkt
      · have hpref : shortPrefix t.val t.isLt.le (A k i₀) =
            shortPrefix t.val t.isLt.le (X i₀) := by
          apply prefix_agree
          intro j hj
          have hh := hmatch j (by omega)
          simpa only [insertDigit, if_pos hj] using hh.symm
        have hvalue := hmatch t (by omega)
        rw [insertDigit_self] at hvalue
        right
        change A k i₀ (T k) = digit (branch p E i₀ s hs (a k))
          (shortPrefix (T k).val (T k).isLt.le (A k i₀))
        have hb' := hbranch hsk
        have hd := congrArg (fun v : Branch p i₀ s =>
          digit v (shortPrefix (pos v).val (pos v).isLt.le (A k i₀))) hb'
        exact (congrArg (A k i₀) (ht hsk)).trans
          (hvalue.symm.trans ((congrArg (digit u) hpref).symm.trans hd.symm))
  · intro i j hj
    rw [hb]
    by_cases hi : i = i₀
    · subst i
      change X i₀ j = B k i₀ j
      dsimp only [B]
      rw [Function.update_self]
      rw [eraseExponent_self] at hj
      by_cases hlow : e k i₀ ≤ s
      · have hjk : j.val < e k i₀ := hj.trans_le (eraseLevel_le _ _)
        have hjt : j.val < t.val := hjk.trans_le (hlow.trans hst)
        have hjT : j.val < (T k).val := hjk.trans_le (hlow.trans (hpos _))
        have hh := hmatch j hjk
        simpa only [insertDigit, deleteDigit, if_pos hjt, if_pos hjT] using hh
      · have hsk : s < e k i₀ := by omega
        rw [ht hsk] at hj ⊢
        exact prefix_agreement_after_deletion t r 0 (X i₀) (A k i₀) (e k i₀)
          (he k i₀) hmatch j hj
    · have hh := hkd i j (hj.trans_le (eraseExponent_le i₀ (T k).val (e k) i))
      rw [hz] at hh
      simp only [Y, Function.update_of_ne hi] at hh
      change X i j = B k i j
      simpa only [B, Function.update_of_ne hi] using hh
include hpos in
/-- The fixed-value specialization of simultaneous adaptive deletion. -/
theorem adaptive_restriction
    (hp : ∀ i, 0 < p i) (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) :
    ∃ b : κ → ℤ, ∀ x : ℤ, ∃ k,
      active p E i₀ s hs pos digit (e k) (a k) ∧
      ((∏ i, p i ^ eraseExponent i₀
        (chosenPosition p E i₀ s hs pos (a k)).val (e k) i : ℕ) : ℤ) ∣ x-b k := by
  obtain ⟨b,_,hb⟩ := simultaneous_adaptive_restriction p E i₀ s hs pos hpos
    hp hcp e he a hc
  exact ⟨b,hb digit⟩
end Arithmetic

/-- A safe family of individually digit-deleted classes gives a smaller odd
period; the deleted position is allowed to depend on the class. -/
theorem individual_smaller_period {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (i₀ : ι) (T : κ → Fin (E i₀)) (active : κ → Prop) (b : κ → ℤ)
    (hb : ∀ x : ℤ, ∃ k, active k ∧
      ((∏ i, p i ^ eraseExponent i₀ (T k).val (e k) i : ℕ) : ℤ) ∣ x-b k)
    (hunit : ∀ k, active k → ∃ i, eraseExponent i₀ (T k).val (e k) i ≠ 0)
    (hinj : ∀ k l, active k → active l →
      eraseExponent i₀ (T k).val (e k) = eraseExponent i₀ (T l).val (e l) → k = l) :
    ∃ N < ∏ i, p i ^ E i, HasOddArithmeticCover N (Fintype.card κ) := by
  classical
  let E' := Function.update E i₀ (E i₀ - 1)
  let N := ∏ i, p i ^ E' i
  let n (k : {k // active k}) := ∏ i, p i ^ eraseExponent i₀ (T k.val).val (e k.val) i
  have hE' (i : ι) : E' i ≤ E i := by
    by_cases hi : i = i₀
    · subst i; simp [E']
    · simp [E', hi]
  have hnewle (k : κ) (i : ι) : eraseExponent i₀ (T k).val (e k) i ≤ E' i := by
    by_cases hi : i = i₀
    · subst i
      simp only [eraseExponent_self, E', Function.update_self]
      unfold eraseLevel
      have hh := he k i₀
      have ht := (T k).isLt
      split_ifs <;> omega
    · simpa [E', eraseExponent, hi] using he k i
  have hNpos : 0 < N := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
  have hNlt : N < ∏ i, p i ^ E i := by
    apply Finset.prod_lt_prod (fun i _ => pow_pos (hp i).1.pos _)
      (fun i _ => Nat.pow_le_pow_right (hp i).1.pos (hE' i))
    refine ⟨i₀, Finset.mem_univ _, ?_⟩
    simp only [E', Function.update_self]
    exact Nat.pow_lt_pow_right (hp i₀).1.one_lt (by
      have : Nonempty κ := by obtain ⟨k, _⟩ := hb 0; exact ⟨k⟩
      let k : κ := Classical.arbitrary κ
      have := (T k).isLt
      omega)
  refine ⟨N, hNlt, hNpos, {k // active k}, inferInstance, n, (fun k => b k.val),
    ?_, ?_, ?_, ?_, Fintype.card_subtype_le _⟩
  · intro k l hkl
    apply Subtype.ext
    apply hinj k.val l.val k.property l.property
    funext i
    have hh := congrArg (fun m : ℕ => m.factorization (p i)) hkl
    simpa only [n, factorization_prime_power_product p (fun i => (hp i).1) hpi] using hh
  · intro k
    have hnpos : 0 < n k := Finset.prod_pos (fun i _ => pow_pos (hp i).1.pos _)
    have hnne : n k ≠ 1 := by
      intro h
      obtain ⟨i, hi⟩ := hunit k.val k.property
      have hh := factorization_prime_power_product p (fun i => (hp i).1) hpi
        (eraseExponent i₀ (T k.val).val (e k.val)) i
      change (n k).factorization (p i) = _ at hh
      rw [h, Nat.factorization_one, Finsupp.zero_apply] at hh
      exact hi hh.symm
    refine ⟨by omega, ?_⟩
    exact Finset.prod_induction (fun i => p i ^ eraseExponent i₀ (T k.val).val (e k.val) i) Odd
      (fun _ _ ha hb => ha.mul hb) (by norm_num) (fun i _ => (hp i).2.pow)
  · intro x
    obtain ⟨k, hk, hdiv⟩ := hb x
    exact ⟨⟨k, hk⟩, hdiv⟩
  · intro k
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow (p i) (hnewle k.val i))



/-- Equality after individual deletions has only the expected adjacent-level
causes.  This is a statement about exponent vectors, not about residues. -/
theorem erase_eq_cases {ι : Type*} [DecidableEq ι] (i₀ : ι)
    (t u : ℕ) (e f : ι → ℕ)
    (h : eraseExponent i₀ t e = eraseExponent i₀ u f) :
    e = f ∨
      (e i₀ = f i₀ + 1 ∧ t < e i₀ ∧ f i₀ ≤ u ∧
        ∀ i, i ≠ i₀ → e i = f i) ∨
      (f i₀ = e i₀ + 1 ∧ u < f i₀ ∧ e i₀ ≤ t ∧
        ∀ i, i ≠ i₀ → f i = e i) := by
  have hother (i : ι) (hi : i ≠ i₀) : e i = f i := by
    have hh := congrFun h i
    simpa only [eraseExponent_of_ne _ _ _ hi] using hh
  have heq (hh : e i₀ = f i₀) : e = f := by
    funext i
    by_cases hi : i = i₀
    · simpa [hi] using hh
    · exact hother i hi
  have hh := congrFun h i₀
  simp only [eraseExponent_self] at hh
  by_cases het : e i₀ ≤ t <;> by_cases hfu : f i₀ ≤ u
  · simp only [eraseLevel, if_pos het, if_pos hfu] at hh
    exact Or.inl (heq hh)
  · simp only [eraseLevel, if_pos het, if_neg hfu] at hh
    exact Or.inr (Or.inr ⟨by omega, by omega, het, fun i hi => (hother i hi).symm⟩)
  · simp only [eraseLevel, if_neg het, if_pos hfu] at hh
    exact Or.inr (Or.inl ⟨by omega, by omega, hfu, hother⟩)
  · simp only [eraseLevel, if_neg het, if_neg hfu] at hh
    exact Or.inl (heq (by omega))

lemma positive_position_nonunit {ι : Type*} [DecidableEq ι]
    (i₀ : ι) (t : ℕ) (ht : 0 < t) (e : ι → ℕ) (he : ∃ i, e i ≠ 0) :
    ∃ i, eraseExponent i₀ t e i ≠ 0 := by
  by_contra! hz
  have hh := hz i₀
  simp only [eraseExponent_self, eraseLevel] at hh
  by_cases het : e i₀ ≤ t
  · have heq := eraseExponent_eq_self i₀ t e het
    rw [heq] at hz
    obtain ⟨i,hi⟩ := he
    exact hi (hz i)
  · simp only [if_neg het] at hh
    omega

/-- Even branch-dependent deletion cannot evade every active adjacent pair in
a period-minimal cover.  Its upper member is shortened and its lower member is
not.  The assertion does NOT say that such pairs are nested across levels. -/
theorem minimal_period_adaptive_pair {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (s : ℕ) (hs0 : 0 < s) (hs : s < E i₀)
    (pos : Branch p i₀ s → Fin (E i₀)) (hpos : ∀ u, s ≤ (pos u).val)
    (digit : (u : Branch p i₀ s) →
      (Fin (pos u).val → Fin (p i₀)) → Fin (p i₀)) :
    ∃ k l,
      active p E i₀ s hs pos digit (e k) (a k) ∧
      active p E i₀ s hs pos digit (e l) (a l) ∧
      e k i₀ = e l i₀ + 1 ∧
      (∀ i, i ≠ i₀ → e k i = e l i) ∧
      (chosenPosition p E i₀ s hs pos (a k)).val < e k i₀ ∧
      e l i₀ ≤ (chosenPosition p E i₀ s hs pos (a l)).val := by
  classical
  let T (k : κ) := chosenPosition p E i₀ s hs pos (a k)
  let P (k : κ) := active p E i₀ s hs pos digit (e k) (a k)
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,hb⟩ := adaptive_restriction p E i₀ s hs pos hpos digit
    (fun i => (hp i).1.pos) hcp e he a hc
  by_contra hnot
  have hinj (k l : κ) (hk : P k) (hl : P l)
      (hkl : eraseExponent i₀ (T k).val (e k) =
        eraseExponent i₀ (T l).val (e l)) : k = l := by
    rcases erase_eq_cases i₀ (T k).val (T l).val (e k) (e l) hkl with hh | hh | hh
    · exact hei hh
    · exact (hnot ⟨k,l,hk,hl,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩).elim
    · exact (hnot ⟨l,k,hl,hk,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩).elim
  obtain ⟨N,hNlt,hN⟩ := individual_smaller_period p E hp hpi e he i₀ T P b hb
    (fun k _ => positive_position_nonunit i₀ (T k).val
      (hs0.trans_le (hpos _)) (e k) (he0 k)) hinj
  apply hmin N hNlt
  obtain ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard⟩ := hN
  exact ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard.trans hcard⟩

#print axioms simultaneous_adaptive_restriction
#print axioms adaptive_restriction
#print axioms individual_smaller_period
#print axioms erase_eq_cases
#print axioms minimal_period_adaptive_pair
end Erdos7AdaptiveDigitRestriction
