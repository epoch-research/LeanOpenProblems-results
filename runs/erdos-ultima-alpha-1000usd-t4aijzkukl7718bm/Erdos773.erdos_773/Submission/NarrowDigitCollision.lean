import FormalConjecturesUtil

/-!
A limitation of a multiscale digit candidate, not a disproof of Erdős 773.
Four nontrivially colliding square roots can have identical digit histograms,
identical end digits, and all digits arbitrarily close to the top of the base.
The identity is already a formal polynomial norm identity. These words do not
satisfy the Gaussian-Eisenstein hypotheses used in other constructions.
-/
namespace Erdos773.NarrowDigitCollision
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def base (t : ℕ) : ℕ := t^2+9*t+20

def alphabet (t : ℕ) : Fin 6 → ℕ :=
  ![t^2+6*t+9, t^2+5*t+6, t^2+7*t+12,
    t^2+4*t+2, t^2+8*t+14, t^2+6*t+10]

def pattern : Fin 4 → Fin 16 → Fin 6 :=
  ![![0,1,2,0,1,3,5,1,2,5,4,2,0,1,2,0],
    ![0,2,1,0,2,4,5,2,1,5,3,1,0,2,1,0],
    ![0,2,1,0,1,5,3,1,2,4,5,2,0,2,1,0],
    ![0,1,2,0,2,5,4,2,1,3,5,1,0,1,2,0]]

def word (t : ℕ) (j : Fin 4) (i : Fin 16) : ℕ := alphabet t (pattern j i)

def value (t B : ℕ) (j : Fin 4) : ℕ := ∑ i : Fin 16, word t j i * B^i.val

attribute [local irreducible] value

lemma end_digits (t : ℕ) (j : Fin 4) :
    word t j 0 = (t+3)^2 ∧ word t j 15 = (t+3)^2 := by
  fin_cases j <;> simp [word,pattern,alphabet] <;> ring

lemma histogram_perm (t : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (word t j)) (List.ofFn (word t 0)) := by
  apply List.perm_iff_count.mpr
  intro a
  fin_cases j <;> simp [word,pattern,List.ofFn_succ,List.count_cons] <;> omega

lemma digit_bounds (t : ℕ) (j : Fin 4) (i : Fin 16) :
    0 < word t j i ∧ word t j i < base t ∧
      base t ≤ word t j i + (5*t+18) := by
  unfold word
  generalize pattern j i = a
  fin_cases a <;> simp [alphabet,base] <;> omega

lemma digit_sum (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 16, word t j i) = 16*(t+3)^2 := by
  fin_cases j <;> simp [word,pattern,alphabet,Fin.sum_univ_succ] <;> ring

lemma digit_energy (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 16, (word t j i)^2) = 4*(2*(t+3)^2+1)^2 := by
  fin_cases j <;> simp [word,pattern,alphabet,Fin.sum_univ_succ] <;> ring

/-- The identity holds at every evaluation base; it is not a carry accident. -/
lemma collision (t B : ℕ) :
    value t B 0 ^ 2 + value t B 1 ^ 2 = value t B 2 ^ 2 + value t B 3 ^ 2 := by
  simp [value,word,pattern,alphabet,Fin.sum_univ_succ]
  ring

lemma first_difference (t B : ℕ) :
    value t B 0 + 2*B*((t+3)+(t+4)*B^4+(t+2)*B^8+(t+3)*B^12) =
      value t B 2 + 2*B^2*((t+3)+(t+4)*B^4+(t+2)*B^8+(t+3)*B^12) := by
  simp [value,word,pattern,alphabet,Fin.sum_univ_succ]
  ring

lemma second_difference (t B : ℕ) :
    value t B 0 + 2*B^4*((t+3)+(t+4)*B+(t+2)*B^2+(t+3)*B^3) =
      value t B 3 + 2*B^8*((t+3)+(t+4)*B+(t+2)*B^2+(t+3)*B^3) := by
  simp [value,word,pattern,alphabet,Fin.sum_univ_succ]
  ring

lemma nontrivial (t B : ℕ) (hB : 2 ≤ B) :
    value t B 2 < value t B 0 ∧ value t B 3 < value t B 0 := by
  have hBsq : B < B^2 := by nlinarith
  have hB4 : 2 ≤ B^4 := by nlinarith [sq_nonneg (B^2-1 : ℤ)]
  have hB8 : B^4 < B^8 := by nlinarith [sq_nonneg ((B^4 : ℕ) : ℤ)]
  have hC : 0 < (t+3)+(t+4)*B^4+(t+2)*B^8+(t+3)*B^12 := by positivity
  have hA : 0 < (t+3)+(t+4)*B+(t+2)*B^2+(t+3)*B^3 := by positivity
  constructor
  · have h := first_difference t B
    have hm := Nat.mul_lt_mul_of_pos_right hBsq hC
    nlinarith only [h,hm]
  · have h := second_difference t B
    have hm := Nat.mul_lt_mul_of_pos_right hB8 hA
    nlinarith only [h,hm]

lemma not_sidon (t B : ℕ) (hB : 2 ≤ B) :
    ¬IsSidon (((univ : Finset (Fin 4)).image (fun j => value t B j ^ 2)) : Set ℕ) := by
  intro h
  have hm (j : Fin 4) : value t B j ^ 2 ∈
      (((univ : Finset (Fin 4)).image (fun j => value t B j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe,Finset.mem_image]
    exact ⟨j,mem_univ _,rfl⟩
  rcases h _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t B) with hh | hh
  · have he := Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) hh.1
    exact (Nat.ne_of_lt (nontrivial t B hB).1) he.symm
  · have he := Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) hh.1
    exact (Nat.ne_of_lt (nontrivial t B hB).2) he.symm

/-- A finite sufficient parameter bound for a prescribed relative digit width. -/
lemma relative_digit_bounds (t : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (ht : 10/δ ≤ (t+3:ℕ)) (j : Fin 4) (i : Fin 16) :
    (1-δ)*(base t:ℝ) ≤ word t j i ∧ (word t j i:ℝ) < base t := by
  have hk : (0:ℝ) < (t+3:ℕ) := by positivity
  have hδk : 10 ≤ δ*(t+3:ℕ) := by
    have hh := (div_le_iff₀ hδ).mp ht
    nlinarith only [hh]
  have hb : (base t:ℝ) = (t+3:ℕ)^2 + 3*(t+3:ℕ) + 2 := by
    simp [base]
    ring
  have hgap : ((5*t+18:ℕ):ℝ) ≤ δ*(base t:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hδk hk.le
    rw [hb]
    push_cast at hh ⊢
    nlinarith [mul_nonneg hδ.le (show (0:ℝ) ≤ 3*((t:ℝ)+3)+2 by positivity)]
  have hd := digit_bounds t j i
  have hd' : (base t:ℝ) ≤ (word t j i:ℝ) + (5*t+18:ℕ) := by exact_mod_cast hd.2.2
  constructor
  · nlinarith only [hd',hgap]
  · exact_mod_cast hd.2.1

private lemma digit_eval_injective {B n : ℕ} (hB : 1 < B)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < B) (hb : ∀ i, b i < B)
    (he : (∑ i, a i * B ^ i.val) = ∑ i, b i * B ^ i.val) : a = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hf (f : Fin (n+1) → ℕ) : (∑ i, f i * B ^ i.val) =
        f 0 + B * ∑ i : Fin n, f i.succ * B ^ i.val := by
      rw [Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hf a, hf b] at he
    have he0 : a 0 = b 0 := by
      have hh := congrArg (· % B) he
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (ha 0),
        Nat.mod_eq_of_lt (hb 0)] using hh
    have het : (∑ i : Fin n, a i.succ * B ^ i.val) =
        ∑ i : Fin n, b i.succ * B ^ i.val := by
      rw [he0] at he
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < B) (Nat.add_left_cancel he)
    have ht := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ) het
    funext i
    refine Fin.cases he0 (fun j => congrFun ht j) i


lemma value_injective (t : ℕ) : Function.Injective (value t (base t)) := by
  intro a b he
  have hB : 1 < base t := by unfold base; omega
  have hw := digit_eval_injective hB (word t a) (word t b)
    (fun i => (digit_bounds t a i).2.1) (fun i => (digit_bounds t b i).2.1)
    (by simpa only [value] using he)
  have h1 := congrFun hw (1 : Fin 16)
  have h4 := congrFun hw (4 : Fin 16)
  fin_cases a <;> fin_cases b <;> simp [word,pattern,alphabet] at h1 h4 ⊢ <;> omega

lemma value_positive (t B : ℕ) (j : Fin 4) : 0 < value t B j := by
  have hh := Finset.single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 16))) =>
    Nat.zero_le (word t j i * B^i.val)) (mem_univ (0 : Fin 16))
  have hh' : word t j 0 ≤ value t B j := by simpa only [value,Fin.val_zero,pow_zero,mul_one] using hh
  exact (digit_bounds t j 0).1.trans_le hh'

/-- Unbounded bases with non-Sidon four-word families in any prescribed
    top-of-base digit band. The end digits and full histogram also agree. -/
theorem arbitrarily_narrow (δ : ℝ) (hδ : 0 < δ) (L : ℕ) :
    ∃ t : ℕ, L < base t ∧
      (∀ j : Fin 4, ∀ i : Fin 16,
        (1-δ)*(base t:ℝ) ≤ word t j i ∧ (word t j i:ℝ) < base t) ∧
      (∀ j : Fin 4, word t j 0 = (t+3)^2 ∧ word t j 15 = (t+3)^2) ∧
      (∀ j : Fin 4, List.Perm (List.ofFn (word t j)) (List.ofFn (word t 0))) ∧
      Function.Injective (value t (base t)) ∧
      (∀ j : Fin 4, 0 < value t (base t) j) ∧
      ¬IsSidon (((univ : Finset (Fin 4)).image (fun j => value t (base t) j ^ 2)) : Set ℕ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (10/δ)
  let t := max n L
  have ht : 10/δ ≤ (t+3:ℕ) := by
    have hn' : (n:ℝ) ≤ (t+3:ℕ) := by exact_mod_cast (show n ≤ t+3 by omega)
    exact hn.le.trans hn'
  refine ⟨t,?_,relative_digit_bounds t δ hδ ht,end_digits t,histogram_perm t,
    value_injective t,value_positive t (base t),?_⟩
  · have hL : L ≤ t := le_max_right _ _
    dsimp [base]
    omega
  · apply not_sidon
    unfold base
    omega

#print axioms collision
#print axioms histogram_perm
#print axioms digit_bounds
#print axioms not_sidon
#print axioms value_injective
#print axioms value_positive
#print axioms arbitrarily_narrow
end Erdos773.NarrowDigitCollision
