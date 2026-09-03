import Submission.StoppingDigitRestriction

/-! Active projected classes lift under one common insertion map. In particular,
disjoint original classes cannot become identical nonempty projected classes. -/
namespace Erdos7StoppingPreimage
open scoped BigOperators
open Erdos7Digits Erdos7Compression Erdos7Reduction Erdos7AllDigits
open Erdos7StoppingDigitRestriction
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma agreement_before_insertion {α : Type*} {n : ℕ} (t : Fin n)
    (r d : α) (x a : Fin n → α) (e : ℕ) (he : e ≤ n)
    (ha : e ≤ t.val ∨ a t=r)
    (hh : Agree (eraseLevel t.val e) x (deleteDigit t d a)) :
    Agree e (insertDigit t r x) a := by
  intro j hj
  by_cases hje : j.val < t.val
  · have hjer : j.val < eraseLevel t.val e := by
      unfold eraseLevel
      split_ifs <;> omega
    have h := hh j hjer
    simpa only [insertDigit,deleteDigit,if_pos hje] using h
  · by_cases hjt : j=t
    · subst j
      rw [insertDigit_self]
      exact (ha.resolve_left (fun h => Nat.not_le_of_gt hj h)).symm
    · have hlt : t.val < j.val := by
        have hne : j.val ≠ t.val := fun h => hjt (Fin.ext h)
        omega
      let u : Fin n := ⟨j.val-1,by have := j.isLt; omega⟩
      have hu : t.val ≤ u.val := by dsimp [u]; omega
      have hue : u.val < eraseLevel t.val e := by
        dsimp [u]
        unfold eraseLevel
        split_ifs <;> omega
      have hun : u.val+1 < n := by dsimp [u]; omega
      have hus : u.val+1 = j.val := by dsimp [u]; omega
      have h := hh u hue
      have hnu : ¬ u.val < t.val := Nat.not_lt_of_ge hu
      simp only [deleteDigit,if_neg hnu,dif_pos hun] at h
      have hidx : (⟨u.val+1,hun⟩ : Fin n)=j := Fin.ext hus
      rw [hidx] at h
      simpa only [insertDigit,if_neg hje,if_neg hjt] using h

/-- Reverse prefix transfer for a predictable position and value. -/
theorem stopping_agreement_lift {α : Type*} {n : ℕ}
    (T : (Fin n → α) → Fin n) (V : (Fin n → α) → α)
    (hT : Predictable T) (hV : PredictableValue T V)
    (d : α) (x a : Fin n → α) (e : ℕ) (he : e ≤ n)
    (ha : e ≤ (T a).val ∨ a (T a)=V a)
    (hh : Agree (eraseLevel (T a).val e) x (deleteDigit (T a) d a)) :
    Agree e (insertDigit (T x) (V x) x) a := by
  by_cases hlow : e ≤ (T a).val
  · have hagree : Agree e x a := by
      intro j hj
      have hje : j.val < (T a).val := hj.trans_le hlow
      have h := hh j (by simpa only [eraseLevel,if_pos hlow] using hj)
      simpa only [deleteDigit,if_pos hje] using h
    have hxl : e ≤ (T x).val := by
      by_contra! hxt
      have htx := hT x a (hagree.mono hxt.le)
      rw [htx] at hlow
      omega
    intro j hj
    simpa only [insertDigit,if_pos (hj.trans_le hxl)] using hagree j hj
  · have hlt : (T a).val < e := by omega
    have hagree : Agree (T a).val a x := by
      intro j hj
      have hjer : j.val < eraseLevel (T a).val e := by
        unfold eraseLevel
        rw [if_neg hlow]
        omega
      have h := hh j hjer
      simpa only [deleteDigit,if_pos hj] using h.symm
    rw [hT a x hagree,hV a x hagree]
    exact agreement_before_insertion (T a) (V a) d x a e he ha hh

section Arithmetic
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (p E : ι → ℕ) (i₀ : ι) [∀ i, NeZero (p i)]
    (T : (Fin (E i₀) → Fin (p i₀)) → Fin (E i₀))
    (V : (Fin (E i₀) → Fin (p i₀)) → Fin (p i₀))
    (hT : Predictable T) (hV : PredictableValue T V)
    (hp : ∀ i, 0 < p i) (hcp : Pairwise (Function.onFun Nat.Coprime p))
    (e : κ → ι → ℕ) (he : ∀ k i, e k i ≤ E i) (a b : κ → ℤ)
    (hb : ∀ k i, zmodDigits (p i) (E i) (b k) =
      (Function.update (fun j => zmodDigits (p j) (E j) (a k)) i₀
        (deleteDigit (T (zmodDigits (p i₀) (E i₀) (a k))) 0
          (zmodDigits (p i₀) (E i₀) (a k)))) i)

include hT hV hp hcp he hb in
/-- One integer simultaneously lifts every active class hit at the same
projected integer. No assumption that the original family covers is used. -/
theorem simultaneous_lift (x : ℤ) : ∃ z : ℤ, ∀ k,
    active p E i₀ T V (e k) (a k) →
    ((∏ i, p i ^ eraseExponent i₀
      (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) i : ℕ) : ℤ) ∣ x-b k →
    ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ z-a k := by
  let X (i : ι) := zmodDigits (p i) (E i) x
  let Y := Function.update X i₀ (insertDigit (T (X i₀)) (V (X i₀)) (X i₀))
  obtain ⟨z,hz⟩ := exists_integer_with_digits p E hp hcp Y
  refine ⟨z,fun k hk hdiv => ?_⟩
  let A (i : ι) := zmodDigits (p i) (E i) (a k)
  let s := T (A i₀)
  have hm := (divisor_product_iff_digits p E (eraseExponent i₀ s.val (e k))
    (fun i => (eraseExponent_le i₀ s.val (e k) i).trans (he k i)) hcp x (b k)).mp hdiv
  apply (divisor_product_iff_digits p E (e k) (he k) hcp z (a k)).mpr
  intro i j hj
  rw [hz]
  by_cases hi : i=i₀
  · subst i
    dsimp only [Y]
    rw [Function.update_self]
    change insertDigit (T (X i₀)) (V (X i₀)) (X i₀) j = A i₀ j
    apply stopping_agreement_lift T V hT hV 0 (X i₀) (A i₀) (e k i₀)
      (he k i₀) hk _ j hj
    intro l hl
    have hh := hm i₀ l (by simpa only [eraseExponent_self] using hl)
    rw [hb] at hh
    simpa only [Function.update_self] using hh
  · have hh := hm i j (by simpa only [eraseExponent_of_ne _ _ _ hi] using hj)
    rw [hb] at hh
    change Y i j = A i j
    simpa only [Y,Function.update_of_ne hi] using hh

include hT hV hp hcp he hb in
theorem projected_disjoint (k l : κ)
    (hk : active p E i₀ T V (e k) (a k)) (hl : active p E i₀ T V (e l) (a l))
    (hdis : ∀ z : ℤ, ¬ (((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ z-a k ∧
      ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ z-a l)) (x : ℤ) :
    ¬ (((∏ i, p i ^ eraseExponent i₀
        (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) i : ℕ) : ℤ) ∣ x-b k ∧
      ((∏ i, p i ^ eraseExponent i₀
        (T (zmodDigits (p i₀) (E i₀) (a l))).val (e l) i : ℕ) : ℤ) ∣ x-b l) := by
  rintro ⟨hdk,hdl⟩
  obtain ⟨z,hz⟩ := simultaneous_lift p E i₀ T V hT hV hp hcp e he a b hb x
  exact hdis z ⟨hz k hk hdk,hz l hl hdl⟩
include hT hV hp hcp he hb in
/-- In an irredundant cover, active comparable original moduli have disjoint
projected classes. Thus an adjacent-exponent collision cannot be repaired by
identifying equal projected residue classes. -/
theorem irredundant_projected_disjoint
    (hpriv : ∀ k, ∃ x : ℤ, ∀ l, l ≠ k → ¬ ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ x-a l)
    (hc : ∀ x : ℤ, ∃ k, ((∏ i, p i ^ e k i : ℕ) : ℤ) ∣ x-a k)
    (k l : κ) (hne : l ≠ k) (hcomp : ∀ i, e l i ≤ e k i)
    (hk : active p E i₀ T V (e k) (a k)) (hl : active p E i₀ T V (e l) (a l))
    (x : ℤ) :
    ¬ (((∏ i, p i ^ eraseExponent i₀
        (T (zmodDigits (p i₀) (E i₀) (a k))).val (e k) i : ℕ) : ℤ) ∣ x-b k ∧
      ((∏ i, p i ^ eraseExponent i₀
        (T (zmodDigits (p i₀) (E i₀) (a l))).val (e l) i : ℕ) : ℤ) ∣ x-b l) := by
  have hd : (∏ i, p i ^ e l i) ∣ ∏ i, p i ^ e k i :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => pow_dvd_pow (p i) (hcomp i))
  have hnc := residue_not_congruent_of_proper_modulus_divisor
    (fun k => ∏ i, p i ^ e k i) a hpriv hc hne hd
  have hdZ : ((∏ i, p i ^ e l i : ℕ) : ℤ) ∣ ((∏ i, p i ^ e k i : ℕ) : ℤ) := by
    exact_mod_cast hd
  apply projected_disjoint p E i₀ T V hT hV hp hcp e he a b hb k l hk hl _ x
  rintro z ⟨hzk,hzl⟩
  apply hnc
  convert dvd_sub hzl (hdZ.trans hzk) using 1 <;> ring

end Arithmetic

#print axioms irredundant_projected_disjoint
#print axioms agreement_before_insertion
#print axioms stopping_agreement_lift
#print axioms simultaneous_lift
#print axioms projected_disjoint
end Erdos7StoppingPreimage
