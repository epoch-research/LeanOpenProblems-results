import FormalConjectures.Dev.Helpers
import FormalConjectures.Dev.Paley

open Matrix Nat Int Finset MulChar
open scoped BigOperators

lemma jacobi_eq_qchar {p : ℕ} [Fact p.Prime] (a : ℤ) :
    jacobiSym a p = quadraticChar (ZMod p) (a : ZMod p) := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  rfl

noncomputable def origRatMatrix (p m : ℕ) : Matrix (Fin m) (Fin m) ℚ := fun i j =>
  let Cint : ℤ := m.factorial.cast
  let ii : ℤ := (i.val + 1).cast
  let jj : ℤ := (j.val + 1).cast
  ((jacobiSym (ii * ii - Cint * jj) p : ℤ) : ℚ)

lemma odd_column_pred {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (C : ZMod p) (hCprod : C = ∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p)))
    (hoddm : Odd m) :
    Odd (Fintype.card {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1}) := by
  classical
  let g : Fin m → ℤ := fun j => quadraticChar (ZMod p) (((j.val + 1 : ℕ) : ZMod p))
  have hg : ∀ a, g a = 1 ∨ g a = -1 := by
    intro a
    have hne : ((a.val + 1 : ℕ) : ZMod p) ≠ 0 := one_to_m_cast_ne_zero hp a
    exact quadraticChar_dichotomy (F:=ZMod p) hne
  have hprodg : (∏ b, g b) = quadraticChar (ZMod p) C := by
    rw [hCprod]
    simp [g, map_prod]
  have hoddcard : Odd (Fintype.card (Fin m)) := by simpa using hoddm
  have hodd' := odd_count_prod_mul_eq_one_of_pm_one g hg hoddcard
  -- convert predicate `(∏g)*g a=1` to χ(C*a)=1
  let esub : {j : Fin m // (∏ b, g b) * g j = 1} ≃
      {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1} :=
    Equiv.subtypeEquivRight (fun j => by
      change (∏ b, g b) * g j = 1 ↔ quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1
      rw [hprodg]
      dsimp [g]
      have hm : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) =
          quadraticChar (ZMod p) C * quadraticChar (ZMod p) (((j.val + 1 : ℕ) : ZMod p)) := by
        rw [map_mul]
      constructor
      · intro h
        change quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1
        rw [hm]
        exact h
      · intro h
        change quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 at h
        rw [hm] at h
        exact h)
  have hcard := Fintype.card_congr esub
  rw [← hcard]
  exact hodd'

lemma paley_zero_orig_rat {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1)
    (hp2 : ringChar (ZMod p) ≠ 2)
    (hneg1 : quadraticChar (ZMod p) (-1) = -1)
    (hoddm : Odd m)
    (hCprod : ((m.factorial : ℕ) : ZMod p) = ∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) :
    Matrix.det (origRatMatrix p m) = 0 := by
  classical
  let C : ZMod p := (m.factorial : ℕ)
  have hC : C ≠ 0 := factorial_cast_zmod_ne_zero hp
  let eR := rowQREquiv hp hp2
  let eC := signedQREquiv hp hp2 hneg1 C hC
  let pred : QR2 (ZMod p) → Prop := fun s =>
    quadraticChar (ZMod p) (C * (((eC.symm s).val + 1 : ℕ) : ZMod p)) = 1
  have hodd_fin : Odd (Fintype.card {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1}) := by
    exact odd_column_pred hp C hCprod hoddm
  have hodd_qr : Odd (Fintype.card {s : QR2 (ZMod p) // pred s}) := by
    let esub : {j : Fin m // quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1} ≃ {s : QR2 (ZMod p) // pred s} :=
      Equiv.subtypeEquiv eC (by
        intro j
        dsimp [pred]
        simp [eC])
    have hcard := Fintype.card_congr esub
    rw [← hcard]
    exact hodd_fin
  let A : Matrix (QR2 (ZMod p)) (QR2 (ZMod p)) ℚ := fun r s => ((quadraticChar (ZMod p) ((r:ZMod p) - (s:ZMod p)) : ℤ) : ℚ)
  let B : Matrix (QR2 (ZMod p)) (QR2 (ZMod p)) ℚ := fun r s => ((quadraticChar (ZMod p) ((r:ZMod p) + (s:ZMod p)) : ℤ) : ℚ)
  let MQR : Matrix (QR2 (ZMod p)) (QR2 (ZMod p)) ℚ := fun i j => if pred j then A i j else B i j
  have hpal : Matrix.det MQR = 0 := by
    simpa [MQR, A, B] using (paley_mixed_det_zero (F:=ZMod p) hp2 hneg1 pred hodd_qr)
  have hreindex_zero : Matrix.det (Matrix.reindex eR.symm eC.symm MQR) = 0 := by
    rw [Matrix.det_reindex, hpal, mul_zero]
  have hmat : Matrix.reindex eR.symm eC.symm MQR = origRatMatrix p m := by
    ext i j
    simp only [Matrix.reindex_apply]
    change MQR (eR i) (eC j) = origRatMatrix p m i j
    have hspec := signedQR'_spec hp hneg1 C hC j
    have hrow : ((eR i : QR2 (ZMod p)) : ZMod p) = (((i.val + 1 : ℕ) : ZMod p) ^ 2) := by
      simp [eR, rowQREquiv, rowQRMap]
    have harg : (((((i.val + 1 : ℤ) * (i.val + 1 : ℤ) - (m.factorial : ℤ) * (j.val + 1 : ℤ)) : ℤ) : ZMod p)) =
          (((i.val + 1 : ℕ) : ZMod p) ^ 2 - C * ((j.val + 1 : ℕ) : ZMod p)) := by
      dsimp [C]
      norm_num [sq]
    rcases hspec with ⟨hcol, hchi⟩ | ⟨hcol, hchi⟩
    · have hcolE : ((eC j : QR2 (ZMod p)) : ZMod p) = C * ((j.val + 1 : ℕ) : ZMod p) := by
        simpa [eC, signedQREquiv] using hcol
      have hpred : pred (eC j) := by
        dsimp [pred]
        simpa [eC, signedQREquiv] using hchi
      simp only [MQR, hpred, if_true, A, origRatMatrix]
      rw [jacobi_eq_qchar]
      apply congrArg (fun z : ZMod p => ((quadraticChar (ZMod p) z : ℤ) : ℚ))
      rw [hrow, hcolE]
      exact harg.symm
    · have hcolE : ((eC j : QR2 (ZMod p)) : ZMod p) = -(C * ((j.val + 1 : ℕ) : ZMod p)) := by
        simpa [eC, signedQREquiv] using hcol
      have hpred : ¬ pred (eC j) := by
        intro hp1
        dsimp [pred] at hp1
        have hp1' : quadraticChar (ZMod p) (C * ((j.val + 1 : ℕ) : ZMod p)) = 1 := by
          simpa [eC, signedQREquiv] using hp1
        omega
      simp only [MQR, hpred, if_false, B, origRatMatrix]
      rw [jacobi_eq_qchar]
      apply congrArg (fun z : ZMod p => ((quadraticChar (ZMod p) z : ℤ) : ℚ))
      rw [hrow, hcolE]
      calc
        ((i.val + 1 : ℕ) : ZMod p) ^ 2 + -(C * ((j.val + 1 : ℕ) : ZMod p)) =
            ((i.val + 1 : ℕ) : ZMod p) ^ 2 - C * ((j.val + 1 : ℕ) : ZMod p) := by rw [sub_eq_add_neg]
        _ = (((i.val + 1 : ℤ) * (i.val + 1 : ℤ) - (m.factorial : ℤ) * (j.val + 1 : ℤ) : ℤ) : ZMod p) := harg.symm
  rw [← hmat]
  exact hreindex_zero

#print axioms paley_zero_orig_rat
