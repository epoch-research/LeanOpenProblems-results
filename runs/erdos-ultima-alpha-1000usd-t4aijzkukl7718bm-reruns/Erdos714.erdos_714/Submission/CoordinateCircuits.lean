import Submission.Coding

/-!
A coordinate-circuit obstruction for arbitrary codes. In particular, being
nonlinear in the messages does not rescue a code that is affine-additive in
its coordinate variable. This is not a resolution of Erdős 714.
-/

noncomputable section
open Finset SimpleGraph Classical

namespace Erdos714CoordinateCircuits

variable {C I A B : Type*} [Fintype C] [Fintype I] [Fintype A]

/-- If the values at `r` distinct coordinates are determined by an observation
in `B`, every observation fiber has at most `r-1` messages in a free code. -/
theorem bound_of_observation [Fintype B] (f : C → I → A)
    {r : ℕ} (hr : 0 < r) (e : Fin r ↪ I) (g : C → B)
    (hg : ∀ c d, g c = g d → ∀ j, f c (e j) = f d (e j))
    (hfree : (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714Coding.graph f)) :
    Fintype.card C ≤ (r-1) * Fintype.card B := by
  by_contra! hc
  obtain ⟨b, hb⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g (n := r-1)
    (by simpa only [mul_comm] using hc)
  obtain ⟨rows, hrows⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := univ.filter (fun c => g c = b)) (by
      simp only [Fintype.card_fin]
      omega)
  have heq (j : Fin r) : g (rows j) = b :=
    (mem_filter.mp (hrows ⟨j,rfl⟩)).2
  have ha := (Erdos714Coding.free_iff_agreement f hr).mp hfree rows
  have hsub : univ.map e ⊆ Erdos714Coding.agreement f hr rows := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_map.mp hi
    simp only [Erdos714Coding.agreement, mem_filter, mem_univ, true_and]
    intro k
    exact hg (rows k) (rows ⟨0,hr⟩) ((heq k).trans (heq _).symm) j
  have hn := card_le_card hsub
  simp only [card_map, card_univ, Fintype.card_fin] at hn
  omega

/-- One coordinate determined by three other coordinates is already too much
redundancy for a fourth-case code with more than `3*q^3` messages. -/
theorem three_coordinate_bound (f : C → I → A) (e : Fin 4 ↪ I)
    (Φ : A → A → A → A)
    (hΦ : ∀ c, f c (e 3) = Φ (f c (e 0)) (f c (e 1)) (f c (e 2)))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph f)) :
    Fintype.card C ≤ 3 * Fintype.card A ^ 3 := by
  let g (c : C) : A × A × A := (f c (e 0), f c (e 1), f c (e 2))
  have hg : ∀ c d, g c = g d → ∀ j, f c (e j) = f d (e j) := by
    intro c d h j
    have h₀ : f c (e 0) = f d (e 0) := congrArg Prod.fst h
    have h₁ : f c (e 1) = f d (e 1) := congrArg (fun p => p.2.1) h
    have h₂ : f c (e 2) = f d (e 2) := congrArg (fun p => p.2.2) h
    fin_cases j
    · exact h₀
    · exact h₁
    · exact h₂
    · change f c (e 3) = f d (e 3)
      rw [hΦ, hΦ, h₀, h₁, h₂]
  have hb := bound_of_observation f (by decide : 0 < 4) e g hg hfree
  simpa only [Nat.reduceSub, Fintype.card_prod, pow_succ, pow_zero, one_mul,
    mul_assoc] using hb

/-- Quadratic dependence along just one scalar line already bounds the total
number of messages. Nothing is assumed away from that line. -/
theorem quadratic_line_bound {F : Type*} [CommSemiring F] [Fintype F]
    (f : C → I → F) (line : F ↪ I) (P₀ P₁ P₂ : C → F)
    (hline : ∀ c s, f c (line s) = P₀ c + P₁ c * s + P₂ c * s^2)
    (hq : 4 ≤ Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph f)) :
    Fintype.card C ≤ 3 * Fintype.card F ^ 3 := by
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4) (β := F) (by simpa using hq)
  let e : Fin 4 ↪ I := t.trans line
  let g (c : C) : F × F × F := (P₀ c,P₁ c,P₂ c)
  have hg : ∀ c d, g c = g d → ∀ j, f c (e j) = f d (e j) := by
    intro c d h j
    have h₀ : P₀ c = P₀ d := congrArg Prod.fst h
    have h₁ : P₁ c = P₁ d := congrArg (fun p => p.2.1) h
    have h₂ : P₂ c = P₂ d := congrArg (fun p => p.2.2) h
    change f c (line (t j)) = f d (line (t j))
    rw [hline, hline, h₀, h₁, h₂]
  have hb := bound_of_observation f (by decide : 0 < 4) e g hg hfree
  simpa only [Nat.reduceSub, Fintype.card_prod, pow_succ, pow_zero, one_mul,
    mul_assoc] using hb

variable [AddCommGroup I]

/-- Every additive group with at least four elements has a nondegenerate
parallelogram. This includes groups of exponent two and exponent three. -/
lemma exists_parallelogram (hI : 4 ≤ Fintype.card I) :
    ∃ u v : I, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ u+v ≠ 0 := by
  obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card I) 0
  let S : Finset I := {0,u,-u}
  have hS : S.card ≤ 3 := by
    have h₁ := card_insert_le (0 : I) ({u,-u} : Finset I)
    have h₂ := card_insert_le u ({-u} : Finset I)
    simp only [card_singleton] at h₂
    change (insert 0 {u,-u} : Finset I).card ≤ 3
    omega
  have hnot : ¬ (univ : Finset I) ⊆ S := by
    intro h
    have hn := card_le_card h
    simp only [card_univ] at hn
    omega
  obtain ⟨v, _, hv⟩ := not_subset.mp hnot
  have hv' : v ≠ 0 ∧ v ≠ u ∧ v ≠ -u := by simpa [S] using hv
  refine ⟨u,v,hu,hv'.1,hv'.2.1.symm,?_⟩
  intro hs
  apply hv'.2.2
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs)

/-- Affine-additive coordinate dependence forces a uniform message bound.
The assignment of the affine map to each message is completely arbitrary. -/
theorem affine_coordinate_bound [AddCommGroup A]
    (L : C → (I →+ A)) (b : C → A) (hI : 4 ≤ Fintype.card I)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun c i => b c + L c i))) :
    Fintype.card C ≤ 3 * Fintype.card A ^ 3 := by
  obtain ⟨u,v,hu,hv,huv,hs⟩ := exists_parallelogram hI
  let e : Fin 4 ↪ I := ⟨![0,u,v,u+v], by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact False.elim (hu h)
      | exact False.elim (hu h.symm)
      | exact False.elim (hv h)
      | exact False.elim (hv h.symm)
      | exact False.elim (huv h)
      | exact False.elim (huv h.symm)
      | exact False.elim (hs h)
      | exact False.elim (hs h.symm)
      | exact False.elim (hu (by simpa using h))
      | exact False.elim (hu (by simpa using h.symm))
      | exact False.elim (hv (by simpa using h))⟩
  apply three_coordinate_bound (fun c i => b c + L c i) e
    (fun x y z => y+z-x) _ hfree
  intro c
  change b c + L c (u+v) = (b c + L c u) + (b c + L c v) - (b c + L c 0)
  rw [map_add, map_zero, add_zero]
  abel

/-- At quartic message size, a code affine-additive in its coordinate variable
cannot achieve the required forbidden-copy condition, even for nonlinear rows. -/
theorem quartic_not_free [AddCommGroup A]
    (L : C → (I →+ A)) (b : C → A)
    (hI : 4 ≤ Fintype.card I) (hq : 4 ≤ Fintype.card A)
    (hC : Fintype.card A ^ 4 ≤ Fintype.card C) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun c i => b c + L c i)) := by
  intro hfree
  have hb := hC.trans (affine_coordinate_bound L b hI hfree)
  have hq3 : Fintype.card A ≤ 3 := by
    apply Nat.le_of_mul_le_mul_left (c := Fintype.card A ^ 3) _ (by positivity)
    simpa only [pow_succ, mul_comm] using hb
  omega

end Erdos714CoordinateCircuits

#print axioms Erdos714CoordinateCircuits.bound_of_observation
#print axioms Erdos714CoordinateCircuits.three_coordinate_bound
#print axioms Erdos714CoordinateCircuits.exists_parallelogram
#print axioms Erdos714CoordinateCircuits.affine_coordinate_bound
#print axioms Erdos714CoordinateCircuits.quartic_not_free

#print axioms Erdos714CoordinateCircuits.quadratic_line_bound
