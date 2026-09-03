import FormalConjecturesUtil
import Submission.BinaryTriangleIncidence
import Submission.ThetaAffineStars

/-! Refutation of an AUXILIARY linear heavy-pair bound, even with a
column-degree cap. This is not a disproof of Erdős 713. -/
namespace Erdos713ThetaHeavyLinearCounterexample
open Erdos713ThetaGram Erdos713ThetaAffineStars
set_option maxHeartbeats 2000000

theorem exists_counterexample (N : ℕ) :
    ∃ (A B : Type) (_ : Fintype A) (_ : Fintype B) (R : A → B → Prop),
      ¬ HasTheta R ∧ (∀ b, Nat.card {a // R a b} ≤ Nat.card B) ∧
      N*(Nat.card A+Nat.card B) < heavyCount R ∧
      (Nat.card B)^2 ≤ 8*Erdos713ThetaCross.lightCount R := by
  classical
  let d := 5*N+1
  let A := Erdos713BinaryTriangles.Rows d
  let I := Erdos713BinaryTriangles.Columns d
  let L : A → I → Prop := Erdos713BinaryTriangles.Inc
  let m := Nat.card A
  let l := Nat.card I
  have hm : m = 3*3^d := Erdos713BinaryTriangles.rows_card d
  have hl : l = 3^d*2^d := Erdos713BinaryTriangles.columns_card d
  have hgap : N*(m+2) < l := by
    rw [hm,hl]
    have hp : 0 < (3 : ℕ)^d := pow_pos (by decide) _
    have ht : 5*N < 2^d := by have hh := (show d < 2^d from Nat.lt_two_pow_self); dsimp [d] at hh ⊢; omega
    have hmul := Nat.mul_lt_mul_of_pos_left ht hp
    nlinarith only [hp,hmul]
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (m+l+3)
  have hqm : m ≤ q := by omega
  have hql : l ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hqp : 0 < q := by omega
  letI : Fact q.Prime := ⟨hprime⟩
  let F := ZMod q
  have hF : Nat.card F = q := by simp [F,Nat.card_eq_fintype_card]
  obtain ⟨s : I ↪ F⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card I ≤ Fintype.card F by
      simpa only [← Nat.card_eq_fintype_card,hF] using hql)
  let U := Rows A F
  let V := Erdos713ThetaAffineStars.Columns I F
  let R := Inc s L
  have hU : Nat.card U = q^2*m := by simp only [U,Rows,Nat.card_prod,hF,← pow_two]; rfl
  have hV : Nat.card V = q^2+l*q := by simp only [V,Erdos713ThetaAffineStars.Columns,Nat.card_sum,Nat.card_prod,hF,← pow_two]; rfl
  have hcol (i : I) : Nat.card {a : A // L a i} = 3 := Erdos713BinaryTriangles.column_card i
  have hheavy : q^2*l ≤ heavyCount R := by
    simpa only [hF] using heavy_lower (s : I → F) L (fun i => (hcol i).ge)
  refine ⟨U,V,inferInstance,inferInstance,R,?_,?_,?_,?_⟩
  · exact no_theta s s.injective L Erdos713BinaryTriangles.no_four Erdos713BinaryTriangles.no_six
  · intro b
    cases b with
    | inl p =>
      rw [center_degree,hV]
      have hh : q ≤ q^2 := by nlinarith only [hqp]
      exact hqm.trans (hh.trans (Nat.le_add_right _ _))
    | inr b =>
      rw [leaf_degree,hcol,hF,hV]
      nlinarith only [hq3]
  · rw [hU,hV]
    have hsize : q^2*m+(q^2+l*q) ≤ q^2*(m+2) := by
      have hh := Nat.mul_le_mul_right q hql
      nlinarith only [hh]
    calc
      N*(q^2*m+(q^2+l*q)) ≤ N*(q^2*(m+2)) := Nat.mul_le_mul_left N hsize
      _ = q^2*(N*(m+2)) := by ring
      _ < q^2*l := Nat.mul_lt_mul_of_pos_left hgap (pow_pos hqp _)
      _ ≤ heavyCount R := hheavy
  · rw [hV]
    have hh : q^4-q^2 ≤ Erdos713ThetaCross.lightCount R := by
      simpa only [hF] using light_lower (s : I → F) L
    have hq2 : 2 ≤ q^2 := by nlinarith only [hq3]
    have hq4 : q^2 ≤ q^4 := by nlinarith only [hq2]
    have he := Nat.sub_add_cancel hq4
    have hmul := Nat.mul_le_mul_right q hql
    have hsq : (q^2+l*q)^2 ≤ (2*q^2)^2 :=
      Nat.pow_le_pow_left (by nlinarith only [hmul]) 2
    nlinarith only [hh,he,hsq,hq2]

/-- Negation of the proposed AUXILIARY estimate, not of the original
universally quantified rational-exponent conjecture. -/
theorem no_capped_linear_heavy_bound :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ (A B : Type) [Fintype A] [Fintype B] (R : A → B → Prop),
      ¬ HasTheta R → (∀ b, Nat.card {a // R a b} ≤ Nat.card B) →
      (heavyCount R : ℝ) ≤ C*((Nat.card A : ℝ)+Nat.card B) := by
  rintro ⟨C,hC,h⟩
  obtain ⟨N,hN⟩ := exists_nat_gt C
  obtain ⟨A,B,hA,hB,R,hFree,hCap,hGap,_hLight⟩ := exists_counterexample N
  have hu := h A B R hFree hCap
  have hg : (N : ℝ)*((Nat.card A : ℝ)+Nat.card B) < heavyCount R := by exact_mod_cast hGap
  have hh := mul_le_mul_of_nonneg_right hN.le
    (show 0 ≤ (Nat.card A : ℝ)+Nat.card B by positivity)
  linarith only [hu,hg,hh]

#print axioms exists_counterexample
#print axioms no_capped_linear_heavy_bound
end Erdos713ThetaHeavyLinearCounterexample
