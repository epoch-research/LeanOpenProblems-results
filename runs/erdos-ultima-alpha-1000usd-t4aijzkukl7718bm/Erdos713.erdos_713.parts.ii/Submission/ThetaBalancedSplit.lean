import FormalConjecturesUtil
import Submission.ThetaColumnSplitting

/-! Column splitting without isolated padding columns. -/
open Finset
namespace Erdos713ThetaBalancedSplit
open Erdos713ThetaGram Erdos713ThetaSplit
variable {A B : Type*}

abbrev CoreColumns (R : A → B → Prop) (d : ℕ) :=
  Σ b : B, Fin (Nat.card {a // R a b}/d+1)

noncomputable def coreSplit [Fintype A] (R : A → B → Prop) (d : ℕ)
    (a : A) (c : CoreColumns R d) : Prop := split R d a (.inl c)

lemma core_no_theta [Fintype A] (R : A → B → Prop) (d : ℕ)
    (h : ¬ HasTheta R) : ¬ HasTheta (coreSplit R d) := by
  apply mt (theta_of_projection Sigma.fst ?_ ?_) h
  · rintro a ⟨b,i⟩ hh
    exact hh.choose
  · rintro a ⟨b,i⟩ ⟨c,j⟩ hi hj he
    change b = c at he
    subst c
    obtain ⟨ha,hi⟩ := hi
    obtain ⟨ha',hj⟩ := hj
    have hij : i = j := Fin.ext (hi.symm.trans hj)
    subst j
    rfl

noncomputable def coreRowEquiv [Fintype A] (R : A → B → Prop) (d : ℕ) (a : A) :
    {b // R a b} ≃ {c // coreSplit R d a c} where
  toFun b := ⟨⟨b.val,⟨(rank R b.val ⟨a,b.property⟩).val/d,
    Nat.lt_succ_of_le (Nat.div_le_div_right (rank R b.val ⟨a,b.property⟩).isLt.le)⟩⟩,
    b.property,rfl⟩
  invFun c := ⟨c.val.1,c.property.choose⟩
  left_inv b := rfl
  right_inv c := by
    rcases c with ⟨⟨b,i⟩,hc⟩
    apply Subtype.ext
    exact congrArg (Sigma.mk b) (Fin.ext hc.choose_spec)

lemma core_row_card [Fintype A] (R : A → B → Prop) (d : ℕ) (a : A) :
    Nat.card {c // coreSplit R d a c} = Nat.card {b // R a b} :=
  (Nat.card_congr (coreRowEquiv R d a)).symm

lemma core_column_le [Fintype A] (R : A → B → Prop) {d : ℕ} (hd : 0 < d)
    (c : CoreColumns R d) : Nat.card {a // coreSplit R d a c} ≤ d :=
  col_card_le R hd (.inl c)

lemma core_edge_card [Fintype A] [Fintype B] (R : A → B → Prop) (d : ℕ) :
    Nat.card {p : A × CoreColumns R d // coreSplit R d p.1 p.2} =
      Nat.card {p : A × B // R p.1 p.2} := by
  classical
  simp only [edge_card_eq_rows,core_row_card]

lemma core_columns_le [Fintype A] [Fintype B] (R : A → B → Prop) {d : ℕ} (hd : 0 < d)
    (he : Nat.card {p : A × B // R p.1 p.2} ≤ d*Nat.card B) :
    Nat.card (CoreColumns R d) ≤ 2*Nat.card B := by
  classical
  have hc : Nat.card (CoreColumns R d) =
      (∑ b, Nat.card {a // R a b}/d)+Nat.card B := by
    simp [CoreColumns,sum_add_distrib,Nat.card_eq_fintype_card]
  have hs : d*(∑ b, Nat.card {a // R a b}/d) ≤ d*Nat.card B := by
    calc
      _ = ∑ b, d*(Nat.card {a // R a b}/d) := by rw [mul_sum]
      _ ≤ ∑ b, Nat.card {a // R a b} := sum_le_sum (fun b _ => Nat.mul_div_le _ _)
      _ ≤ d*Nat.card B := by simpa only [← edge_card_eq_cols] using he
  have hsd := Nat.le_of_mul_le_mul_left hs hd
  omega

lemma balanced_cap {e k : ℕ} (hk : 0 < k) :
    0 < e/k+1 ∧ e ≤ (e/k+1)*k ∧ (e/k+1)*k ≤ e+k := by
  have h1 := Nat.div_add_mod e k
  have h2 := Nat.mod_lt e hk
  constructor
  · exact Nat.succ_pos _
  constructor
  · nlinarith
  · calc
      _ = (e/k)*k+k := by ring
      _ ≤ e+k := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

#print axioms core_no_theta
#print axioms core_row_card
#print axioms core_column_le
#print axioms core_edge_card
#print axioms core_columns_le
#print axioms balanced_cap
end Erdos713ThetaBalancedSplit
