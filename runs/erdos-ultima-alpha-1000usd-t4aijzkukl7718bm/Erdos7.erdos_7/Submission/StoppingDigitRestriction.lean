import Submission.AdaptiveDigitRestriction

/-! Deleting one digit at a predictable stopping position. This is a period
reduction criterion, not a solution of the odd covering-system problem. -/
namespace Erdos7StoppingDigitRestriction
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7AdaptiveDigitRestriction
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Agreement of the first `s` digits, without any bound on `s`. -/
def Agree {α : Type*} {n : ℕ} (s : ℕ) (x y : Fin n → α) : Prop :=
  ∀ j : Fin n, j.val < s → x j = y j

/-- The stopping position is decided before its digit is read. -/
def Predictable {α : Type*} {n : ℕ} (T : (Fin n → α) → Fin n) : Prop :=
  ∀ x y, Agree (T x).val x y → T y = T x

/-- The retained value is also decided from the digits before the stopping
position. -/
def PredictableValue {α : Type*} {n : ℕ} (T : (Fin n → α) → Fin n)
    (R : (Fin n → α) → α) : Prop :=
  ∀ x y, Agree (T x).val x y → R y = R x

lemma Agree.symm {α : Type*} {n s : ℕ} {x y : Fin n → α}
    (h : Agree s x y) : Agree s y x := fun j hj => (h j hj).symm

lemma Agree.mono {α : Type*} {n s t : ℕ} {x y : Fin n → α}
    (h : Agree s x y) (ht : t ≤ s) : Agree t x y :=
  fun j hj => h j (hj.trans_le ht)

lemma agree_insert {α : Type*} {n : ℕ} (t : Fin n) (r : α) (x : Fin n → α) :
    Agree t.val x (insertDigit t r x) := by
  intro j hj
  simp [insertDigit, hj]

lemma predictable_insert {α : Type*} {n : ℕ} (T : (Fin n → α) → Fin n)
    (hT : Predictable T) (x : Fin n → α) (r : α) :
    T (insertDigit (T x) r x) = T x := hT x _ (agree_insert _ _ _)

/-- If a prefix has crossed either stopping position, both decisions agree.
Otherwise neither word has yet stopped in that prefix. -/
theorem predictable_agree {α : Type*} {n e : ℕ}
    (T : (Fin n → α) → Fin n) (hT : Predictable T)
    (x y : Fin n → α) (hxy : Agree e x y) :
    T x = T y ∨ (e ≤ (T x).val ∧ e ≤ (T y).val) := by
  by_cases hx : (T x).val < e
  · exact Or.inl (hT x y (hxy.mono hx.le)).symm
  · by_cases hy : (T y).val < e
    · exact Or.inl (hT y x (hxy.symm.mono hy.le))
    · exact Or.inr ⟨by omega, by omega⟩

section Arithmetic
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (i₀ : ι) [∀ i, NeZero (p i)]
    (T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀))

def active (R : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀))
    (e : ι → ℕ) (a : ℤ) : Prop :=
  let A := zmodDigits (p i₀) (E i₀) a
  e i₀ ≤ (T A).val ∨ A (T A) = R A

/-- One residue assignment works for every predictable retained value and
 every projected integer, even though the stopping depth varies by prefix. -/
theorem simultaneous_stopping_restriction (hT : Predictable T)
    (hp : ∀ i, 0 < p i) (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k) :
    ∃ b : κ → ℤ,
      (∀ k i, zmodDigits (p i) (E i) (b k) =
        (Function.update (fun j => zmodDigits (p j) (E j) (a k)) i₀
          (deleteDigit (T (zmodDigits (p i₀) (E i₀) (a k))) 0
            (zmodDigits (p i₀) (E i₀) (a k)))) i) ∧
      ∀ R : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀),
      PredictableValue T R → ∀ x : ℤ, ∃ k,
        active p E i₀ T R (e k) (a k) ∧
        ((∏ i, p i ^ eraseExponent i₀
          (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) i : ℕ) : ℤ) ∣ x-b k := by
  classical
  let A (k : κ) (i : ι) := zmodDigits (p i) (E i) (a k)
  let S (k : κ) := T (A k i₀)
  let B (k : κ) := Function.update (A k) i₀ (deleteDigit (S k) 0 (A k i₀))
  choose b hb using fun k => exists_integer_with_digits p E hp hcp (B k)
  refine ⟨b,hb,fun R hR x => ?_⟩
  let X (i : ι) := zmodDigits (p i) (E i) x
  let t := T (X i₀)
  let r := R (X i₀)
  let Y := Function.update X i₀ (insertDigit t r (X i₀))
  obtain ⟨z,hz⟩ := exists_integer_with_digits p E hp hcp Y
  obtain ⟨k,hk⟩ := hc z
  have hkd := (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mp hk
  have hmatch : Agree (e k i₀) (insertDigit t r (X i₀)) (A k i₀) := by
    intro j hj
    have hh := hkd i₀ j hj
    rw [hz] at hh
    simpa only [Y,Function.update_self] using hh
  have hTY : T (insertDigit t r (X i₀)) = t :=
    predictable_insert T hT (X i₀) r
  have hcases : S k = t ∨ (e k i₀ ≤ (S k).val ∧ e k i₀ ≤ t.val) := by
    have hh := predictable_agree T hT (A k i₀) (insertDigit t r (X i₀)) hmatch.symm
    simpa only [hTY] using hh
  refine ⟨k,?_,(divisor_product_iff_digits p E
    (eraseExponent i₀ (S k).val (e k))
    (fun i => (eraseExponent_le i₀ (S k).val (e k) i).trans (he k i))
    hcp x (b k)).mpr ?_⟩
  · by_cases hlow : e k i₀ ≤ (S k).val
    · exact Or.inl hlow
    · have hSt : S k = t := hcases.resolve_right (fun h => hlow h.1)
      have ht : t.val < e k i₀ := by omega
      have hpref : Agree t.val (X i₀) (A k i₀) := by
        intro j hj
        have hh := hmatch j (hj.trans ht)
        simpa only [insertDigit,if_pos hj] using hh
      have hval := hmatch t ht
      rw [insertDigit_self] at hval
      right
      change A k i₀ (S k) = R (A k i₀)
      rw [hSt]
      exact hval.symm.trans (hR (X i₀) (A k i₀) hpref).symm
  · intro i j hj
    rw [hb]
    by_cases hi : i = i₀
    · subst i
      change X i₀ j = B k i₀ j
      dsimp only [B]
      rw [Function.update_self]
      rw [eraseExponent_self] at hj
      rcases hcases with hSt | ⟨hS,ht⟩
      · rw [hSt] at hj ⊢
        exact prefix_agreement_after_deletion t r 0 (X i₀) (A k i₀)
          (e k i₀) (he k i₀) hmatch j hj
      · have hje : j.val < e k i₀ := hj.trans_le (eraseLevel_le _ _)
        have hjt : j.val < t.val := hje.trans_le ht
        have hjS : j.val < (S k).val := hje.trans_le hS
        have hh := hmatch j hje
        simpa only [insertDigit,deleteDigit,if_pos hjt,if_pos hjS] using hh
    · have hh := hkd i j (hj.trans_le (eraseExponent_le i₀ (S k).val (e k) i))
      rw [hz] at hh
      simp only [Y,Function.update_of_ne hi] at hh
      change X i j = B k i j
      simpa only [B,Function.update_of_ne hi] using hh
end Arithmetic

/-- Every predictable deletion policy in a minimum-period odd cover has a
unit image or an active adjacent-exponent collision. Positions may include0. -/
theorem minimal_period_stopping_obstruction {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀))
    (hT : Predictable T) (R : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀))
    (hR : PredictableValue T R) :
    (∃ k, active p E i₀ T R (e k) (a k) ∧
      ∀ i, eraseExponent i₀ (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) i = 0) ∨
    ∃ k l,
      active p E i₀ T R (e k) (a k) ∧
      active p E i₀ T R (e l) (a l) ∧
      e k i₀ = e l i₀ + 1 ∧ (∀ i, i ≠ i₀ → e k i = e l i) ∧
      (T (zmodDigits (p i₀) (E i₀) (a k))).val < e k i₀ ∧
      e l i₀ ≤ (T (zmodDigits (p i₀) (E i₀) (a l))).val := by
  classical
  let S (k : κ) := T (zmodDigits (p i₀) (E i₀) (a k))
  let P (k : κ) := active p E i₀ T R (e k) (a k)
  have hcp : Pairwise (Function.onFun Nat.Coprime p) := by
    intro i j hij
    exact (Nat.coprime_primes (hp i).1 (hp j).1).mpr (fun h => hij (hpi h))
  obtain ⟨b,_,hb⟩ := simultaneous_stopping_restriction p E i₀ T hT
    (fun i => (hp i).1.pos) hcp e he a hc
  by_contra hnot
  have hunit (k : κ) (hk : P k) : ∃ i, eraseExponent i₀ (S k).val (e k) i ≠ 0 := by
    by_contra! hz
    exact hnot (Or.inl ⟨k,hk,hz⟩)
  have hinj (k l : κ) (hk : P k) (hl : P l)
      (hkl : eraseExponent i₀ (S k).val (e k) =
        eraseExponent i₀ (S l).val (e l)) : k = l := by
    rcases erase_eq_cases i₀ (S k).val (S l).val (e k) (e l) hkl with hh | hh | hh
    · exact hei hh
    · exact (hnot (Or.inr ⟨k,l,hk,hl,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩)).elim
    · exact (hnot (Or.inr ⟨l,k,hl,hk,hh.1,hh.2.2.2,hh.2.1,hh.2.2.1⟩)).elim
  obtain ⟨N,hNlt,hN⟩ := individual_smaller_period p E hp hpi e he i₀ S P b
    (hb R hR) hunit hinj
  apply hmin N hNlt
  obtain ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard⟩ := hN
  exact ⟨hNpos,ν,fν,n,c,hni,hn,hnc,hnN,hncard.trans hcard⟩

/-- Positive stopping positions exclude the unit alternative. -/
theorem minimal_period_stopping_pair {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (p E : ι → ℕ) (hp : ∀ i, (p i).Prime ∧ Odd (p i))
    (hpi : Function.Injective p) [∀ i, NeZero (p i)]
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i)
    (hei : Function.Injective e) (he0 : ∀ k, ∃ i, e k i ≠ 0) (a : κ → ℤ)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (K : ℕ) (hcard : Fintype.card κ ≤ K)
    (hmin : ∀ N, N < ∏ i, p i ^ E i → ¬ HasOddArithmeticCover N K)
    (i₀ : ι) (T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀))
    (hT : Predictable T) (hpos : ∀ x, 0 < (T x).val)
    (R : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀)) (hR : PredictableValue T R) :
    ∃ k l,
      active p E i₀ T R (e k) (a k) ∧
      active p E i₀ T R (e l) (a l) ∧
      e k i₀ = e l i₀ + 1 ∧ (∀ i, i ≠ i₀ → e k i = e l i) ∧
      (T (zmodDigits (p i₀) (E i₀) (a k))).val < e k i₀ ∧
      e l i₀ ≤ (T (zmodDigits (p i₀) (E i₀) (a l))).val := by
  rcases minimal_period_stopping_obstruction p E hp hpi e he hei a hc K hcard hmin
    i₀ T hT R hR with ⟨k,_,hk⟩ | h
  · obtain ⟨i,hi⟩ := positive_position_nonunit i₀
      (T (zmodDigits (p i₀) (E i₀) (a k))).val (hpos _) (e k) (he0 k)
    exact (hi (hk i)).elim
  · exact h

#print axioms minimal_period_stopping_obstruction
#print axioms minimal_period_stopping_pair

#print axioms predictable_agree
#print axioms simultaneous_stopping_restriction
end Erdos7StoppingDigitRestriction
