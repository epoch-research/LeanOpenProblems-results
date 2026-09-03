import Submission.CharThreeNorm

/-!
A characteristic-three obstruction to arbitrary weight laws with a pair of opposite rows.
This does not prove or disprove Erdős 714.
-/

set_option maxHeartbeats 3000000

open SimpleGraph Polynomial
open Erdos714CharThreeNorm (normForm)

namespace Erdos714NegativeRowNorm

variable {F U V : Type*} [Field F] [CharP F 3]

abbrev Point (F : Type*) := F × F × F

/-- The bipartite weighted norm graph; zero norm values are excluded. -/
def graph (d : F) (H : U → V → F) : SimpleGraph ((Point F × U) ⊕ (Point F × V)) where
  Adj x y := match x, y with
    | .inl p, .inr q => normForm d (p.1 + q.1) = H p.2 q.2 ∧ H p.2 q.2 ≠ 0
    | .inr q, .inl p => normForm d (p.1 + q.1) = H p.2 q.2 ∧ H p.2 q.2 ≠ 0
    | _, _ => False
  symm := by rintro (p | q) (p' | q') <;> simp_all
  loopless := by rintro (p | q) <;> simp

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have : (1 : F) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

/-- Only four values of the weight law are needed for the explicit copy. -/
theorem parameter_not_free (H : U → V → F) (a A : U) (b B : V)
    (c : F) (hc : c ≠ 0) (hd : -c ^ 3 - c ≠ 0)
    (hab : H a b = -c ^ 3 - c) (hAb : H A b = c ^ 3 + c)
    (haB : H a B = -c ^ 3) (hAB : H A B = c ^ 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (-c ^ 3 - c) H) := by
  let L : Fin 4 → Point F × U :=
    ![((0,0,0),a), ((1,0,0),a), ((-1,0,0),a), ((0,1,0),A)]
  let R : Fin 4 → Point F × V :=
    ![((0,1,0),b), ((1,1,0),b), ((-1,1,0),b), ((c,-1,0),B)]
  have hL : Function.Injective L := by
    intro i j hij
    have hp := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;>
      simp [L, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg Prod.fst hij
    fin_cases i <;> fin_cases j <;>
      simp [R, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h6 : (6 : F) = 0 := by linear_combination 2 * h3
  have h8 : (8 : F) = -1 := by linear_combination 3 * h3
  have hp : (c + 1) ^ 3 = c ^ 3 + 1 := by simpa using add_pow_char c (1 : F) 3
  have hm : (c - 1) ^ 3 = c ^ 3 - 1 := by simpa using sub_pow_char c (1 : F)
  have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc
  have hdc : c ^ 3 + c ≠ 0 := by
    intro h
    apply hd
    linear_combination -h
  have hE : ∀ i j, (graph (-c ^ 3 - c) H).Adj (.inl (L i)) (.inr (R j)) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [graph, L, R, normForm, hab, hAb, haB, hAB, hp, hm, hc3, hd, hdc,
        show (-1 : F) + c = c - 1 by ring, show (1 : F) + c = c + 1 by ring] <;>
      ring_nf <;> simp [h2, h3, h6, h8]
  intro hf
  apply hf
  refine ⟨⟨⟨Sum.map L R, ?_⟩, Sum.map_injective.mpr ⟨hL, hR⟩⟩⟩
  rintro (i | i) (j | j) h
  · simp at h
  · exact hE i j
  · exact (hE j i).symm
  · simp at h

/-- Any pointwise opposite pair, with one row attaining all nonzero values, fails. -/
theorem opposite_rows_obstruction [Finite F] (H : U → V → F) (a A : U)
    (hop : ∀ b, H A b = -H a b)
    (hrow : ∀ t : F, t ≠ 0 → ∃ b, H a b = t) :
    ∃ d : F, Irreducible (X ^ 3 - X - C d : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph d H) := by
  obtain ⟨c, hc⟩ := Erdos714CharThreeNorm.exists_outside_artinSchreier (F := F)
  obtain ⟨hc0, hd0, hirr⟩ := Erdos714CharThreeNorm.parameter_irreducible c hc
  obtain ⟨b, hb⟩ := hrow (-c ^ 3 - c) hd0
  obtain ⟨B, hB⟩ := hrow (-c ^ 3) (neg_ne_zero.mpr (pow_ne_zero 3 hc0))
  refine ⟨-c ^ 3 - c, hirr, parameter_not_free H a A b B c hc0 hd0 hb ?_ hB ?_⟩
  · rw [hop, hb]
    ring
  · rw [hop, hB, neg_neg]

/-- Additivity is needed only in the row label, and the column labels can be arbitrary. -/
theorem additive_rows_obstruction [Finite F] [AddGroup U]
    (H : U →+ (V → F)) (a : U)
    (hrow : ∀ t : F, t ≠ 0 → ∃ b, H a b = t) :
    ∃ d : F, Irreducible (X ^ 3 - X - C d : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph d (fun a b => H a b)) := by
  apply opposite_rows_obstruction (fun a b => H a b) a (-a) _ hrow
  intro b
  simp

#print axioms parameter_not_free
#print axioms opposite_rows_obstruction
#print axioms additive_rows_obstruction

end Erdos714NegativeRowNorm
