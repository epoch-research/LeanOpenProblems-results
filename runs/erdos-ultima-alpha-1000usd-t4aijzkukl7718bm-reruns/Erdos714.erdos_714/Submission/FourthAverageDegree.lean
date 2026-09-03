import Submission.FourthLocalDegree

/-!
A fourth-case average-degree refinement of the local star count.
This sharpens an upper-bound constant, not the exponent in Erdős 714.
-/
noncomputable section
open Finset SimpleGraph Classical
set_option maxHeartbeats 2000000
namespace Erdos714FourthLocal
open Erdos714Packing
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Weighted double counting of ordered pairs of rows through a column. -/
lemma weighted_pair_count (S : A → Finset B) (w : B → ℕ) :
    (∑ x : B, w x*(dual S x).card.descFactorial 2) =
      ∑ f : Fin 2 ↪ A, ∑ x ∈ S (f 0) ∩ S (f 1), w x := by
  have h := Fintype.sum_equiv (Erdos714Unbalanced.starEquiv (dual S) 2)
    (fun p => w p.1) (fun p => w p.2.val) (fun p => rfl)
  simp only [Fintype.sum_sigma, sum_const, card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, nsmul_eq_mul] at h
  have hdual : dual (dual S) = S := by
    funext a
    ext x
    simp only [mem_dual]
  rw [hdual] at h
  have hc (f : Fin 2 ↪ A) : common S f = S (f 0) ∩ S (f 1) := by
    ext x
    simp only [mem_common, Fin.forall_fin_two, mem_inter]
  simp_rw [sum_coe_sort, hc] at h
  simpa only [Fintype.card_coe, Nat.cast_id, mul_comm] using h

/-- The local inequality, summed over all ordered row pairs. -/
theorem degree_cubic_moment (S : A → Finset B) (q : ℕ)
    (hA : Fintype.card A ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x : B, (dual S x).card * (dual S x).card.descFactorial 2) ≤
      (q^3+2)*(∑ x : B, (dual S x).card.descFactorial 2) + 3*Fintype.card A^3 := by
  have hl (f : Fin 2 ↪ A) := local_degree_sum S (f 0) (f 1)
    (fun h => (by decide : (0 : Fin 2) ≠ 1) (f.injective h)) q hA hfree
  have h := sum_le_sum (s := (univ : Finset (Fin 2 ↪ A))) (fun f _ => hl f)
  have hsum (f : Fin 2 ↪ A) : (∑ x : PairCommon S (f 0) (f 1), (dual S x.val).card) =
      ∑ x ∈ S (f 0) ∩ S (f 1), (dual S x).card := sum_coe_sort (S (f 0) ∩ S (f 1)) (fun x => (dual S x).card)
  simp_rw [hsum] at h
  rw [sum_add_distrib, ← mul_sum, ← pair_count S,
    ← weighted_pair_count S (fun x => (dual S x).card)] at h
  simp only [sum_const, card_univ, nsmul_eq_mul] at h
  have hn : Fintype.card (Fin 2 ↪ A) ≤ Fintype.card A^2 := by
    simpa only [Fintype.card_embedding_eq, Fintype.card_fin] using
      Nat.descFactorial_le_pow (Fintype.card A) 2
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right (3*Fintype.card A) hn]

/-- A cubic supporting-line identity avoids any regularity assumption. -/
lemma cubic_support (Q D x : ℝ) (hx : 0 ≤ x) (hD : Q+1 ≤ 2*D) :
    D*(D-1)*(D-Q) + (D*(D-1)+(D-Q)*(2*D-1))*(x-D) ≤ x*(x-1)*(x-Q) := by
  have h := mul_nonneg (sq_nonneg (x-D)) (show 0 ≤ x+2*D-Q-1 by linarith)
  nlinarith

/-- Balanced fourth-case incidence graphs have leading average-degree constant one.
The row part may be smaller than the column part. -/
theorem average_degree_bound (S : A → Finset B) (q : ℕ)
    (hA : Fintype.card A ≤ q^4) (hAB : Fintype.card A ≤ Fintype.card B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ x : B, (dual S x).card) ≤ (q^3+3*q^2+2)*Fintype.card B := by
  let Q : ℝ := (q : ℝ)^3+2
  let D : ℝ := (q : ℝ)^3+3*(q : ℝ)^2+2
  let L : ℝ := D*(D-1)+(D-Q)*(2*D-1)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hQ : 2 ≤ Q := by dsimp [Q]; have := pow_nonneg hq 3; linarith
  have hDQ : Q ≤ D := by dsimp [Q,D]; nlinarith [sq_nonneg (q : ℝ)]
  have hD : 2 ≤ D := hQ.trans hDQ
  have hL : 0 < L := by
    dsimp [L]
    have h₁ : 0 < D*(D-1) := mul_pos (by linarith) (by linarith)
    have h₂ : 0 ≤ (D-Q)*(2*D-1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hfD : 3*(q : ℝ)^8 ≤ D*(D-1)*(D-Q) := by
    have h₁ : (q : ℝ)^3 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (q : ℝ)]
    have h₂ : (q : ℝ)^3 ≤ D-1 := by dsimp [D]; nlinarith [sq_nonneg (q : ℝ)]
    have hp : (q : ℝ)^6 ≤ D*(D-1) := by
      calc
        _ = (q : ℝ)^3*(q : ℝ)^3 := by ring
        _ ≤ _ := mul_le_mul h₁ h₂ (by positivity) (by linarith)
    have he : D-Q = 3*(q : ℝ)^2 := by dsimp [D,Q]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ 3*(q : ℝ)^2)]
  have hmoment : (∑ x : B, ((dual S x).card : ℝ)*((dual S x).card-1)*((dual S x).card-Q)) ≤
      3*(Fintype.card A : ℝ)^3 := by
    have h := (Nat.cast_le (α := ℝ)).mpr (degree_cubic_moment S q hA hfree)
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_descFactorial_two] at h
    calc
      _ = (∑ x : B, ((dual S x).card : ℝ)*((dual S x).card*((dual S x).card-1))) -
          Q*(∑ x : B, ((dual S x).card : ℝ)*((dual S x).card-1)) := by
        rw [mul_sum, ← sum_sub_distrib]
        apply sum_congr rfl
        intro x _
        ring
      _ ≤ _ := by dsimp [Q]; linarith
  have hsupport : (Fintype.card B : ℝ)*(D*(D-1)*(D-Q)) +
      L*((∑ x : B, ((dual S x).card : ℝ))-D*Fintype.card B) ≤
      ∑ x : B, ((dual S x).card : ℝ)*((dual S x).card-1)*((dual S x).card-Q) := by
    have h := sum_le_sum (s := (univ : Finset B))
      (fun x _ => cubic_support Q D ((dual S x).card) (by positivity) (by linarith))
    change (∑ x : B, (D*(D-1)*(D-Q)+L*(((dual S x).card : ℝ)-D))) ≤ _ at h
    rw [sum_add_distrib] at h
    rw [← mul_sum _ _ L, sum_sub_distrib] at h
    simp only [sum_const, card_univ, nsmul_eq_mul] at h
    (convert h using 1; ring)
  have hbudget : 3*(Fintype.card A : ℝ)^3 ≤ (Fintype.card B : ℝ)*(D*(D-1)*(D-Q)) := by
    have ha : (Fintype.card A : ℝ) ≤ (q : ℝ)^4 := by exact_mod_cast hA
    have hab : (Fintype.card A : ℝ) ≤ Fintype.card B := by exact_mod_cast hAB
    calc
      _ = 3*(Fintype.card A : ℝ)*(Fintype.card A : ℝ)^2 := by ring
      _ ≤ 3*(Fintype.card B : ℝ)*((q : ℝ)^4)^2 := by gcongr
      _ = (Fintype.card B : ℝ)*(3*(q : ℝ)^8) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfD (by positivity)
  have he : (∑ x : B, ((dual S x).card : ℝ)) ≤ D*Fintype.card B := by
    have h := hsupport.trans hmoment
    have hmul : L*((∑ x : B, ((dual S x).card : ℝ))-D*Fintype.card B) ≤ 0 := by linarith
    by_contra! hh
    have hp := mul_pos hL (sub_pos.mpr hh)
    linarith
  dsimp [D] at he
  exact_mod_cast he

#print axioms weighted_pair_count
#print axioms degree_cubic_moment
#print axioms cubic_support
#print axioms average_degree_bound
end Erdos714FourthLocal
