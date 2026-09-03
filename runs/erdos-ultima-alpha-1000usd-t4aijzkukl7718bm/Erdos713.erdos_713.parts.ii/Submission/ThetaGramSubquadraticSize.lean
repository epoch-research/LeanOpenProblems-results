import FormalConjecturesUtil
import Submission.ThetaGramPairBound

/-! Fixed-Gram examples with enough rows to absorb every fixed
subquadratic power of the column count after relevant column splittings.
This is an auxiliary finite construction, not a settlement of Erdos 713. -/
open Finset
namespace Erdos713ThetaGramSubquadraticSize
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaGramPairBound
set_option maxHeartbeats 2000000

def dim (s : ℕ) := 14*s+29
def lowerExp (s : ℕ) := 42*s+68
def num (s : ℕ) := 2*s+3
def den (s : ℕ) := s+2
def base (s : ℕ) := (dim s+1)^9+1
def raw (s r : ℕ) := r*(1+r+r^2)^(dim s)
def param (s r : ℕ) := base s*(raw s r)^(2*num s)
def scale (s : ℕ) := base s*3^(dim s*(2*num s))
def paramExp (s : ℕ) := (1+2*dim s)*(2*num s)
def sizeExp (s : ℕ) := paramExp s*(3*dim s)
def sizeConst (s : ℕ) := (scale s)^(3*dim s)

lemma raw_pos (s : ℕ) {r : ℕ} (hr : 1 ≤ r) : 0 < raw s r := by
  unfold raw
  positivity

lemma param_pos (s : ℕ) {r : ℕ} (hr : 1 ≤ r) : 0 < param s r := by
  unfold param base
  exact Nat.mul_pos (by omega) (pow_pos (raw_pos s hr) _)

lemma raw_pow_le_param (s r : ℕ) : (raw s r)^(2*num s) ≤ param s r := by
  exact Nat.le_mul_of_pos_left _ (by unfold base; omega)

lemma base_lt_param (s : ℕ) {r : ℕ} (hr : 1 ≤ r) : (dim s+1)^9 < param s r := by
  have hh : 1 ≤ (raw s r)^(2*num s) := Nat.one_le_pow _ _ (raw_pos s hr)
  have h := Nat.le_mul_of_pos_right (base s) hh
  unfold base at h
  exact lt_of_lt_of_le (Nat.lt_succ_self _) h

lemma count_gap (s : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (dim s*(param s r)^2+1)^9 * (param s r)^(lowerExp s) < (param s r)^(3*dim s) := by
  let N := param s r
  have hN : 0 < N := param_pos s hr
  have hOne : 1 ≤ N^2 := Nat.one_le_pow _ _ hN
  have hg : (dim s*N^2+1)^9 ≤ (dim s+1)^9*N^18 := by
    calc
      _ ≤ ((dim s+1)*N^2)^9 := Nat.pow_le_pow_left (by nlinarith only [hOne]) 9
      _ = _ := by rw [mul_pow,← pow_mul]
  calc
    _ ≤ ((dim s+1)^9*N^18)*N^(lowerExp s) := Nat.mul_le_mul_right _ hg
    _ = (dim s+1)^9*N^(18+lowerExp s) := by rw [pow_add]; ac_rfl
    _ < N*N^(18+lowerExp s) := Nat.mul_lt_mul_of_pos_right (base_lt_param s hr) (pow_pos hN _)
    _ = _ := by rw [← pow_succ']; congr 1; unfold dim lowerExp; omega

lemma exists_fiber (s : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    ∃ g : GramCode (dim s) (param s r), (param s r)^(lowerExp s) < Fintype.card (Fiber g) := by
  classical
  have hc : Fintype.card (GramCode (dim s) (param s r)) * (param s r)^(lowerExp s) <
      Fintype.card (NatCoeffs (dim s) (param s r)) := by
    have h := count_gap s hr
    simpa only [GramCode,NatCoeffs,Fintype.card_fun,Fintype.card_prod,
      Fintype.card_fin,← pow_mul,Nat.mul_comm] using h
  obtain ⟨g,hg⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (gramCode (d := dim s) (N := param s r)) hc
  exact ⟨g,by simpa only [Fiber,Fintype.card_subtype] using hg⟩

lemma columns_formula (s r N : ℕ) :
    Fintype.card (Columns (dim s) r N) = raw s r*N^(dim s) := by
  classical
  simp only [Columns,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ColBound,
    mul_pow,raw,mul_assoc]

lemma columns_square_le (s : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (Fintype.card (Columns (dim s) r (param s r)))^2 ≤ (param s r)^(lowerExp s) := by
  let N := param s r
  have hN : 0 < N := param_pos s hr
  have hU : (raw s r)^2 ≤ N := by
    exact (Nat.pow_le_pow_right (raw_pos s hr) (by unfold num; omega)).trans (raw_pow_le_param s r)
  calc
    _ = (raw s r)^2*N^(2*dim s) := by rw [columns_formula,mul_pow,← pow_mul,Nat.mul_comm (dim s) 2]
    _ ≤ N*N^(2*dim s) := Nat.mul_le_mul_right _ hU
    _ = N^(2*dim s+1) := by rw [pow_succ'];
    _ ≤ N^(lowerExp s) := Nat.pow_le_pow_right hN (by unfold dim lowerExp; omega)

lemma split_power_le (s : ℕ) {r : ℕ} (hr : 1 ≤ r) {T : ℕ}
    (hT : T^2 ≤ (param s r)^(dim s)) :
    (Fintype.card (Columns (dim s) r (param s r))*T)^(num s) ≤
      ((param s r)^(lowerExp s))^(den s) := by
  let N := param s r
  have hN : 0 < N := param_pos s hr
  have hExp : 1+dim s*(3*num s) ≤ lowerExp s*(2*den s) := by
    unfold dim num lowerExp den
    nlinarith
  have hp : ((Fintype.card (Columns (dim s) r N)*T)^(num s))^2 ≤
      ((N^(lowerExp s))^(den s))^2 := by
    calc
      _ = (raw s r)^(2*num s)*N^(dim s*(2*num s))*(T^2)^(num s) := by
        rw [columns_formula]
        simp only [mul_pow,← pow_mul]
        simp only [Nat.mul_assoc,Nat.mul_comm]
      _ ≤ N*N^(dim s*(2*num s))*(N^(dim s))^(num s) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (raw_pow_le_param s r)) (Nat.pow_le_pow_left hT _)
      _ = N^(1+dim s*(3*num s)) := by
        rw [← pow_mul,← pow_succ',← pow_add]
        congr 1
        ring
      _ ≤ N^(lowerExp s*(2*den s)) := Nat.pow_le_pow_right hN hExp
      _ = _ := by simp only [← pow_mul]; congr 1; ring
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hp

lemma param_polynomial (s : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    param s r ≤ scale s*r^(paramExp s) := by
  have hr2 : r ≤ r^2 := by nlinarith only [hr]
  have hA : 1+r+r^2 ≤ 3*r^2 := by nlinarith only [hr,hr2]
  have hraw : raw s r ≤ 3^(dim s)*r^(1+2*dim s) := by
    calc
      _ ≤ r*(3*r^2)^(dim s) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA _)
      _ = _ := by
        simp only [mul_pow,← pow_mul,pow_add,pow_one]
        ring
  calc
    _ ≤ base s*(3^(dim s)*r^(1+2*dim s))^(2*num s) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hraw _)
    _ = _ := by simp only [mul_pow,← pow_mul,scale,paramExp,mul_assoc]

lemma fiber_polynomial (s : ℕ) {r : ℕ} (hr : 1 ≤ r)
    (g : GramCode (dim s) (param s r)) : Nat.card (Fiber g) ≤ sizeConst s*r^(sizeExp s) := by
  classical
  have hc : Nat.card (Fiber g) ≤ (param s r)^(3*dim s) := by
    have h := Fintype.card_subtype_le (fun f : NatCoeffs (dim s) (param s r) => gramCode f = g)
    simpa only [Fiber,Nat.card_eq_fintype_card,NatCoeffs,Fintype.card_fun,
      Fintype.card_fin,← pow_mul,Nat.mul_comm] using h
  calc
    _ ≤ (param s r)^(3*dim s) := hc
    _ ≤ (scale s*r^(paramExp s))^(3*dim s) := Nat.pow_le_pow_left (param_polynomial s hr) _
    _ = _ := by simp only [mul_pow,← pow_mul,sizeConst,sizeExp]

/-- The exponent ratio is (2s+3)/(s+2), tending to two from below. -/
theorem exists_examples (s r : ℕ) (hr : 1 ≤ r) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop) (Q : ℕ),
      ¬ HasTheta R ∧ (Nat.card B)^2 < Nat.card A ∧
      Nat.card A ≤ sizeConst s*r^(sizeExp s) ∧
      (∀ a, Nat.card {b // R a b} = r) ∧
      (∀ x y, x ≠ y → codegree R x y ≤ Q) ∧
      ∀ T : ℕ, T^2 ≤ Q → (Nat.card B*T)^(num s) ≤ (Nat.card A)^(den s) := by
  classical
  obtain ⟨g,hg⟩ := exists_fiber s hr
  refine ⟨Fiber g,Columns (dim s) r (param s r),inferInstance,inferInstance,
    incidence g,(param s r)^(dim s),incidence_no_theta g,?_,fiber_polynomial s hr g,
    row_card g,pair_codegree_le g,?_⟩
  · simpa only [Nat.card_eq_fintype_card] using (columns_square_le s hr).trans_lt hg
  · intro T hT
    simpa only [Nat.card_eq_fintype_card] using
      (split_power_le s hr hT).trans (Nat.pow_le_pow_left hg.le _)

#print axioms exists_examples
end Erdos713ThetaGramSubquadraticSize
