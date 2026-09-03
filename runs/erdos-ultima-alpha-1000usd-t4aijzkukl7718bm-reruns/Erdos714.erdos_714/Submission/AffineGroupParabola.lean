import FormalConjecturesUtil

/-!
A parametric obstruction to an affine-group parabola construction.
This file does not settle Erdős Problem 714.
-/

open SimpleGraph

set_option maxHeartbeats 4000000

namespace Erdos714AffineGroupParabola

variable {K : Type*} [Field K]

/-- The product-graph relation from the affine group. Zero first coordinates
are included as isolated vertices, to simplify the ambient vertex type. -/
def graph (ι : K) (T : Set K) : SimpleGraph ((K × K) ⊕ (K × K)) where
  Adj p q := match p, q with
    | .inl u, .inr v => u.1 ≠ 0 ∧ v.1 ≠ 0 ∧ ∃ t ∈ T,
        u.2 + u.1*v.2 = (u.1*v.1)^2 + (u.1*v.1)^3*(t+ι*t^2)
    | .inr v, .inl u => u.1 ≠ 0 ∧ v.1 ≠ 0 ∧ ∃ t ∈ T,
        u.2 + u.1*v.2 = (u.1*v.1)^2 + (u.1*v.1)^3*(t+ι*t^2)
    | _, _ => False
  symm := by intro p q; cases p <;> cases q <;> simp_all
  loopless := by intro p; cases p <;> simp

section CharThree

variable [CharP K 3]

private lemma imaginary_ne (ι : K) (hi : ι^2 = -1) :
    ι ≠ 0 ∧ ι ≠ 1 ∧ ι ≠ -1 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  constructor
  · intro h
    subst ι
    simp at hi
  constructor <;> intro h
  · subst ι
    have h1 : (1 : K) = 0 := by linear_combination h3 - hi
    exact one_ne_zero h1
  · subst ι
    have h1 : (1 : K) = 0 := by linear_combination h3 - hi
    exact one_ne_zero h1

private def left (ι : K) : Fin 4 → K × K :=
  ![(1,0), (ι-1,ι), (-ι-1,-1), (1-ι,1-ι)]

private def right (ι : K) : Fin 4 → K × K :=
  ![(ι-1,ι-1), (ι-1,ι), (ι,-ι), (1-ι,ι+1)]

private def label : Fin 4 → Fin 4 → K :=
  ![![-1,0,1,-1], ![1,0,1,1], ![0,1,-1,1], ![1,0,-1,1]]

private lemma left_injective (ι : K) (hi : ι^2 = -1) : Function.Injective (left ι) := by
  obtain ⟨hi0, hi1, him⟩ := imaginary_ne ι hi
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro a b hab
  have he := congrArg Prod.snd hab
  fin_cases a <;> fin_cases b <;> try rfl
  all_goals dsimp [left] at he
  all_goals exfalso
  · apply hi0
    linear_combination -he
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination he
  · apply hi1
    linear_combination he
  · apply hi0
    linear_combination he
  · apply him
    linear_combination he
  · apply him
    linear_combination -he + (ι) * h3
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -he
  · apply him
    linear_combination -he
  · apply him
    linear_combination he + (1) * h3
  · apply hi1
    linear_combination -he
  · apply him
    linear_combination he + (ι) * h3
  · apply him
    linear_combination -he + (1) * h3

private lemma right_injective (ι : K) (hi : ι^2 = -1) : Function.Injective (right ι) := by
  obtain ⟨hi0, hi1, him⟩ := imaginary_ne ι hi
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  intro a b hab
  have he := congrArg Prod.snd hab
  fin_cases a <;> fin_cases b <;> try rfl
  all_goals dsimp [right] at he
  all_goals exfalso
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -he
  · apply him
    linear_combination -he + (ι) * h3
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination he + (1) * h3
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination he
  · apply hi0
    linear_combination -he + (ι) * h3
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -he
  · apply him
    linear_combination he + (ι) * h3
  · apply hi0
    linear_combination he + (ι) * h3
  · apply hi1
    linear_combination he + (ι) * h3
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination -he + (1) * h3
  · apply (one_ne_zero : (1 : K) ≠ 0)
    linear_combination he
  · apply hi1
    linear_combination -he + (ι) * h3

private lemma all_edges (ι : K) (hi : ι^2 = -1) (T : Set K)
    (h0 : 0 ∈ T) (h1 : 1 ∈ T) (hm : -1 ∈ T) (a b : Fin 4) :
    (graph ι T).Adj (.inl (left ι a)) (.inr (right ι b)) := by
  obtain ⟨hi0, hi1, him⟩ := imaginary_ne ι hi
  have him1 : -ι ≠ 1 := fun h => him (by linear_combination -h)
  have hl : (left ι a).1 ≠ 0 := by
    fin_cases a <;> simp [left, sub_ne_zero, hi1, Ne.symm hi1, him1]
  have hr : (right ι b).1 ≠ 0 := by
    fin_cases b <;> simp [right, sub_ne_zero, hi1, Ne.symm hi1, hi0]
  refine ⟨hl, hr, label a b, ?_, ?_⟩
  · fin_cases a <;> fin_cases b <;> first | exact h0 | exact h1 | exact hm
  · have hi3 : ι^3 = -ι := by calc
      _ = ι^2*ι := by ring
      _ = _ := by rw [hi]; ring
    have hi4 : ι^4 = 1 := by calc
      _ = (ι^2)^2 := by ring
      _ = _ := by rw [hi]; ring
    have hi5 : ι^5 = ι := by calc
      _ = ι^4*ι := by ring
      _ = _ := by rw [hi4]; ring
    have hi6 : ι^6 = -1 := by calc
      _ = ι^4*ι^2 := by ring
      _ = _ := by rw [hi4, hi]; ring
    have hi7 : ι^7 = -ι := by calc
      _ = ι^6*ι := by ring
      _ = _ := by rw [hi6]; ring
    fin_cases a <;> fin_cases b <;> norm_num [left, right, label]
    all_goals apply sub_eq_zero.mp
    all_goals ring_nf
    all_goals simp only [hi, hi3, hi4, hi5, hi6, hi7]
    all_goals ring_nf
    all_goals reduce_mod_char!

/-- A symbolic K44 in every characteristic-three field containing a square
root of minus one, with the three prime-field edge parameters available. -/
def gridCopy (ι : K) (hi : ι^2 = -1) (T : Set K)
    (h0 : 0 ∈ T) (h1 : 1 ∈ T) (hm : -1 ∈ T) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph ι T) := by
  let L : Fin 4 ↪ K × K := ⟨left ι, left_injective ι hi⟩
  let R : Fin 4 ↪ K × K := ⟨right ι, right_injective ι hi⟩
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro p q hpq
  cases p with
  | inl a =>
    cases q with
    | inl b => simp at hpq
    | inr b => exact all_edges ι hi T h0 h1 hm a b
  | inr b =>
    cases q with
    | inl a => exact (all_edges ι hi T h0 h1 hm a b).symm
    | inr a => simp at hpq

theorem not_free (ι : K) (hi : ι^2 = -1) (T : Set K)
    (h0 : 0 ∈ T) (h1 : 1 ∈ T) (hm : -1 ∈ T) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ι T) :=
  fun h => h ⟨gridCopy ι hi T h0 h1 hm⟩

end CharThree

/-- Rescale the parabola parameter without changing the product-graph incidences.
The two sides are allowed different maps, as appropriate for a bipartite graph. -/
def scaleCopy (ι d : K) (hd : d ≠ 0) (T U : Set K)
    (hT : ∀ t ∈ T, t/d ∈ U) : Copy (graph ι T) (graph (d*ι) U) := by
  let L : K × K ↪ K × K := ⟨fun p => (p.1,d^2*p.2), by
    intro p q hpq
    apply Prod.ext
    · simpa only using congrArg Prod.fst hpq
    · exact mul_left_cancel₀ (pow_ne_zero 2 hd) (congrArg Prod.snd hpq)⟩
  let R : K × K ↪ K × K := ⟨fun p => (d*p.1,d^2*p.2), by
    intro p q hpq
    apply Prod.ext
    · exact mul_left_cancel₀ hd (congrArg Prod.fst hpq)
    · exact mul_left_cancel₀ (pow_ne_zero 2 hd) (congrArg Prod.snd hpq)⟩
  have hedge (p q : K × K)
      (h : (graph ι T).Adj (.inl p) (.inr q)) :
      (graph (d*ι) U).Adj (.inl (L p)) (.inr (R q)) := by
    obtain ⟨hp,hq,t,ht,he⟩ := h
    refine ⟨hp,mul_ne_zero hd hq,t/d,hT t ht,?_⟩
    change d^2*p.2+p.1*(d^2*q.2) =
      (p.1*(d*q.1))^2 + (p.1*(d*q.1))^3*(t/d+(d*ι)*(t/d)^2)
    calc
      _ = d^2*(p.2+p.1*q.2) := by ring
      _ = d^2*((p.1*q.1)^2+(p.1*q.1)^3*(t+ι*t^2)) := by rw [he]
      _ = _ := by field_simp
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro p q hpq
  cases p with
  | inl p =>
    cases q with
    | inl q => exact False.elim hpq
    | inr q => exact hedge p q hpq
  | inr p =>
    cases q with
    | inl q => exact (hedge q p hpq.symm).symm
    | inr q => exact False.elim hpq

/-- The characteristic-three obstruction survives every nonzero rescaling,
provided the three scaled prime-field edge labels are retained. -/
theorem scaled_not_free [CharP K 3] (ι d : K) (hi : ι^2 = -1) (hd : d ≠ 0)
    (T : Set K) (h0 : 0 ∈ T) (h1 : 1/d ∈ T) (hm : -1/d ∈ T) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (d*ι) T) := by
  let S : Set K := {0,1,-1}
  have hS : ∀ t ∈ S, t/d ∈ T := by
    intro t ht
    rcases ht with h | h | h
    · simpa [h] using h0
    · simpa [h] using h1
    · simpa [Set.mem_singleton_iff.mp h] using hm
  intro hf
  apply hf
  exact ⟨(scaleCopy ι d hd S T hS).comp (gridCopy ι hi S (by simp [S])
    (by simp [S]) (by simp [S]))⟩

/-- A conjugation-invariant parameter field allows every nonzero imaginary
parabola coefficient, not only a chosen normalization. -/
theorem conjugation_not_free [CharP K 3] (τ : K →+* K) (ι η : K)
    (hi : ι^2 = -1) (hτi : τ ι = -ι) (hη : η ≠ 0) (hτη : τ η = -η) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph η {t | τ t = t}) := by
  let d := η/ι
  have hi0 := (imaginary_ne ι hi).1
  have hd : d ≠ 0 := div_ne_zero hη hi0
  have hτd : τ d = d := by simp [d, map_div₀, hτi, hτη]
  have hdi : d*ι = η := div_mul_cancel₀ η hi0
  rw [← hdi]
  apply scaled_not_free ι d hi hd
  · simp
  · simp [hτd]
  · simp [hτd]

/-- Every odd-degree characteristic-three base field in the proposed quadratic
extension family fails, for every nonzero trace-zero parabola parameter. -/
theorem finite_field_not_free [CharP K 3] [Fintype K] (m : ℕ)
    (hcard : Fintype.card K = 3^(2*(2*m+1))) (η : K) (hη : η ≠ 0)
    (htrace : η^(3^(2*m+1)) = -η) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph η {t | t^(3^(2*m+1)) = t}) := by
  have hmod : Fintype.card K % 4 = 1 := by
    rw [hcard, pow_mul, Nat.pow_mod]
    norm_num
  have hsquare : IsSquare (-1 : K) :=
    FiniteField.isSquare_neg_one_iff.mpr (by rw [hmod]; decide)
  obtain ⟨ι, hi⟩ := hsquare
  have hi2 : ι^2 = -1 := by simpa only [pow_two] using hi.symm
  have hi3 : ι^3 = -ι := by calc
    _ = ι^2*ι := by ring
    _ = _ := by rw [hi2]; ring
  have hi4 : ι^4 = 1 := by calc
    _ = (ι^2)^2 := by ring
    _ = _ := by rw [hi2]; ring
  have hqmod : 3^(2*m+1) % 4 = 3 := by
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hτi : iterateFrobenius K 3 (2*m+1) ι = -ι := by
    change ι^(3^(2*m+1)) = -ι
    rw [pow_eq_pow_mod _ hi4, hqmod, hi3]
  exact conjugation_not_free (iterateFrobenius K 3 (2*m+1)) ι η hi2 hτi hη htrace

end Erdos714AffineGroupParabola

#print axioms Erdos714AffineGroupParabola.conjugation_not_free
#print axioms Erdos714AffineGroupParabola.finite_field_not_free
#print axioms Erdos714AffineGroupParabola.gridCopy
#print axioms Erdos714AffineGroupParabola.not_free

#print axioms Erdos714AffineGroupParabola.scaleCopy
#print axioms Erdos714AffineGroupParabola.scaled_not_free
