import FormalConjecturesUtil

/-! An explicit three-uniform incidence system with no quadrilateral or
hexagon and arbitrarily large column-to-row ratio. Auxiliary only. -/
namespace Erdos713BinaryTriangles
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000

abbrev Vectors (d : ℕ) := Fin d → ZMod 3
abbrev Slopes (d : ℕ) := Fin d → Fin 2
abbrev Rows (d : ℕ) := Fin 3 × Vectors d
abbrev Columns (d : ℕ) := Vectors d × Slopes d

def value {d : ℕ} (b : Columns d) (i : Fin 3) : Vectors d :=
  fun j => b.1 j + (i.val : ZMod 3)*(b.2 j).val

def Inc {d : ℕ} (a : Rows d) (b : Columns d) : Prop := a.2 = value b a.1

private lemma scalar_two_points :
    ∀ (i j : Fin 3) (x y : ZMod 3) (s t : Fin 2), i ≠ j →
      x+(i.val : ZMod 3)*s.val = y+(i.val : ZMod 3)*t.val →
      x+(j.val : ZMod 3)*s.val = y+(j.val : ZMod 3)*t.val → x = y ∧ s = t := by
  decide

private lemma scalar_triangle :
    ∀ (i j k : Fin 3) (x y z : ZMod 3) (s t u : Fin 2),
      i ≠ j → i ≠ k → j ≠ k →
      x+(i.val : ZMod 3)*s.val = y+(i.val : ZMod 3)*t.val →
      y+(j.val : ZMod 3)*t.val = z+(j.val : ZMod 3)*u.val →
      z+(k.val : ZMod 3)*u.val = x+(k.val : ZMod 3)*s.val → x = y ∧ s = t := by
  decide

lemma same_index {d : ℕ} {a a' : Rows d} {b : Columns d}
    (h : Inc a b) (h' : Inc a' b) (hi : a.1 = a'.1) : a = a' :=
  Prod.ext hi (h.trans ((congrArg (value b) hi).trans h'.symm))

lemma no_four {d : ℕ} {a a' : Rows d} {b b' : Columns d}
    (ha : a ≠ a') (h00 : Inc a b) (h01 : Inc a b')
    (h10 : Inc a' b) (h11 : Inc a' b') : b = b' := by
  have hi : a.1 ≠ a'.1 := fun he => ha (same_index h00 h10 he)
  have h0 := h00.symm.trans h01
  have h1 := h10.symm.trans h11
  have hcoord (j : Fin d) : b.1 j = b'.1 j ∧ b.2 j = b'.2 j :=
    scalar_two_points a.1 a'.1 (b.1 j) (b'.1 j) (b.2 j) (b'.2 j) hi
      (congr_fun h0 j) (congr_fun h1 j)
  exact Prod.ext (funext fun j => (hcoord j).1) (funext fun j => (hcoord j).2)

lemma no_six {d : ℕ} {a₀ a₁ a₂ : Rows d} {b₀ b₁ b₂ : Columns d}
    (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) (h12 : a₁ ≠ a₂)
    (h00 : Inc a₀ b₀) (h10 : Inc a₁ b₀) (h11 : Inc a₁ b₁)
    (h21 : Inc a₂ b₁) (h22 : Inc a₂ b₂) (h02' : Inc a₀ b₂) : b₀ = b₁ := by
  have hi01 : a₀.1 ≠ a₁.1 := fun he => h01 (same_index h00 h10 he)
  have hi02 : a₀.1 ≠ a₂.1 := fun he => h02 (same_index h02' h22 he)
  have hi12 : a₁.1 ≠ a₂.1 := fun he => h12 (same_index h11 h21 he)
  have hcoord (j : Fin d) : b₀.1 j = b₁.1 j ∧ b₀.2 j = b₁.2 j :=
    scalar_triangle a₁.1 a₂.1 a₀.1 (b₀.1 j) (b₁.1 j) (b₂.1 j)
      (b₀.2 j) (b₁.2 j) (b₂.2 j) hi12 hi01.symm hi02.symm
      (congr_fun (h10.symm.trans h11) j) (congr_fun (h21.symm.trans h22) j)
      (congr_fun (h02'.symm.trans h00) j)
  exact Prod.ext (funext fun j => (hcoord j).1) (funext fun j => (hcoord j).2)

lemma column_card {d : ℕ} (b : Columns d) : Nat.card {a : Rows d // Inc a b} = 3 := by
  let e : {a : Rows d // Inc a b} ≃ Fin 3 :=
    { toFun := fun a => a.val.1
      invFun := fun i => ⟨(i,value b i),rfl⟩
      left_inv := fun a => Subtype.ext (Prod.ext rfl a.property.symm)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_fin]

lemma rows_card (d : ℕ) : Nat.card (Rows d) = 3*3^d := by
  simp [Rows,Vectors,Nat.card_eq_fintype_card]

lemma columns_card (d : ℕ) : Nat.card (Columns d) = 3^d*2^d := by
  simp [Columns,Vectors,Slopes,Nat.card_eq_fintype_card]

#print axioms no_four
#print axioms no_six
#print axioms column_card
end Erdos713BinaryTriangles
