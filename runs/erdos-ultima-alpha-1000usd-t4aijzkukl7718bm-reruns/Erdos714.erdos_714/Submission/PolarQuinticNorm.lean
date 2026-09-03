import Submission.NegativeRowNorm
import Submission.NormCircleTrace

/-!
Uniform failure of the polarized-quintic norm-weight construction.
This is not a proof or a disproof of Erdős 714.
-/

open SimpleGraph Polynomial
open Erdos714CharThreeNorm (normForm)
open Erdos714NegativeRowNorm (graph Point)

namespace Erdos714PolarQuinticNorm

variable {F : Type*} [Field F] [CharP F 3]

/-- The polarization of the exceptional fifth power. -/
def weight (a b : F) : F := (a + b) ^ 5 - a ^ 5 - b ^ 5

theorem weight_factor (a b : F) : weight a b = -a * b * (a + b) * (a - b) ^ 2 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  unfold weight
  linear_combination (a * b * (2*a^3 + 3*a^2*b + 3*a*b^2 + 2*b^3)) * h3

theorem weight_one (a : F) : weight a 1 = a ^ 3 - a + (a ^ 2 - a ^ 4) := by
  rw [weight_factor]
  ring

theorem weight_neg_one (a : F) : weight a (-1) = a ^ 3 - a - (a ^ 2 - a ^ 4) := by
  rw [weight_factor]
  ring

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have : (1 : F) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

private lemma self_ne_neg {u : F} (hu : u ≠ 0) : u ≠ -u := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  apply hu
  linear_combination -h + u * h3

private lemma norm_shift (d t s : F) (hs : s ^ 3 - s = 0) :
    normForm d ((t,0,0) + (s,-1,0)) = t ^ 3 - t - d := by
  dsimp [normForm]
  rw [add_pow_char t s 3]
  linear_combination hs

set_option maxHeartbeats 1000000 in
/-- Four scalar rows, three conjugate columns, and one opposite column. -/
theorem circle_not_free (u v : F) (huv : u ^ 2 + v ^ 2 = 1)
    (hne : u ^ 2 ≠ v ^ 2)
    (hAS : ∀ x : F, x ^ 3 - x ≠ -u ^ 2 * v ^ 2) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (-u ^ 2 * v ^ 2) (weight (F := F))) := by
  let d := -u ^ 2 * v ^ 2
  have hd : d ≠ 0 := by
    intro h
    exact hAS 0 (by simpa [d] using h.symm)
  have hu : u ≠ 0 := by intro h; apply hd; simp [d, h]
  have hv : v ≠ 0 := by intro h; apply hd; simp [d, h]
  have hun : u ≠ -u := self_ne_neg hu
  have hvn : v ≠ -v := self_ne_neg hv
  have huv' : u ≠ v := fun h => hne (congrArg (fun t : F => t^2) h)
  have hunv : u ≠ -v := by
    intro h
    apply hne
    rw [h, neg_sq]
  have hvnu : v ≠ -u := by
    intro h
    apply hunv
    rw [h, neg_neg]
  let values : Fin 4 → F := ![u,-u,v,-v]
  have hi : Function.Injective values := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [values, hun, hvn, huv', hunv, hvnu, Ne.symm hun, Ne.symm hvn,
        Ne.symm huv', Ne.symm hunv, Ne.symm hvnu] at hij ⊢
  let L : Fin 4 → Point F × F := fun i => ((values i,0,0), values i)
  let R : Fin 4 → Point F × F :=
    ![((0,-1,0),1), ((1,-1,0),1), ((-1,-1,0),1), ((0,1,0),-1)]
  have hL : Function.Injective L := by
    intro i j hij
    exact hi (congrArg Prod.snd hij)
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;>
      simp [R, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hval (i : Fin 4) : values i ^ 2 - values i ^ 4 = -d := by
    fin_cases i <;> dsimp [values, d]
    · linear_combination -u ^ 2 * huv
    · linear_combination -u ^ 2 * huv
    · linear_combination -v ^ 2 * huv
    · linear_combination -v ^ 2 * huv
  have hE : ∀ i j, (graph d weight).Adj (.inl (L i)) (.inr (R j)) := by
    intro i j
    let t := values i
    have hpos : weight t 1 = t ^ 3 - t - d := by rw [weight_one, hval]; ring
    have hneg : weight t (-1) = t ^ 3 - t + d := by rw [weight_neg_one, hval]; ring
    have hnpos : t ^ 3 - t - d ≠ 0 := sub_ne_zero.mpr (hAS t)
    have hnneg : t ^ 3 - t + d ≠ 0 := by
      intro h
      apply hAS (-t)
      dsimp [d] at h ⊢
      linear_combination -h
    have h0 := norm_shift d t 0 (by simp)
    have h1 := norm_shift d t 1 (by simp)
    have hm := norm_shift d t (-1) (by ring)
    fin_cases j <;>
      simp only [graph, L, R, Matrix.cons_val_zero', Matrix.cons_val_succ']
    · exact ⟨h0.trans hpos.symm, hpos ▸ hnpos⟩
    · exact ⟨h1.trans hpos.symm, hpos ▸ hnpos⟩
    · exact ⟨hm.trans hpos.symm, hpos ▸ hnpos⟩
    · refine ⟨?_, hneg ▸ hnneg⟩
      rw [hneg]
      dsimp [normForm, t]
      ring
  intro hf
  apply hf
  refine ⟨⟨⟨Sum.map L R, ?_⟩, Sum.map_injective.mpr ⟨hL, hR⟩⟩⟩
  rintro (i | i) (j | j) h
  · simp at h
  · exact hE i j
  · exact (hE j i).symm
  · simp at h

/-- The full candidate fails over every odd-degree characteristic-three base field
of order at least 27, not just the tested examples. -/
theorem odd_degree_not_free [Fintype F] (m : ℕ) (hm : 3 ≤ m)
    (hodd : Odd m) (hcard : Fintype.card F = 3 ^ m) :
    ∃ d : F, Irreducible (X ^ 3 - X - C d : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph d (weight (F := F))) := by
  obtain ⟨u,v,huv,hAS⟩ := Erdos714NormCircleTrace.exists_circle_parameter m hm hodd hcard
  have hns : ¬IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff, hcard]
    have hqmod : 3 ^ m % 4 = 3 := by
      obtain ⟨k, hk⟩ := hodd
      have hk' : m = 2*k+1 := by omega
      rw [hk', pow_add, pow_mul]
      norm_num [Nat.mul_mod, Nat.pow_mod]
    simp [hqmod]
  have hne : u ^ 2 ≠ v ^ 2 := by
    intro h
    apply hns
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    have he : v ^ 2 = -1 := by linear_combination -huv + h + v ^ 2 * h3
    exact ⟨v, by simpa [pow_two] using he.symm⟩
  refine ⟨-u ^ 2 * v ^ 2, ?_, circle_not_free u v huv hne hAS⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 3 - X - C (-u ^ 2 * v ^ 2) : F[X]).natDegree = 3 := by compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    apply hAS x
    simp only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    exact sub_eq_zero.mp hx

#print axioms weight_factor
#print axioms circle_not_free
#print axioms odd_degree_not_free

end Erdos714PolarQuinticNorm
