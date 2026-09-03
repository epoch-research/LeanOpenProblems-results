import Submission.EisensteinSplitting

/-! Independently choosing either factor above each split prime gives
exponentially many distinct Eisenstein integers of a common norm. -/
namespace Erdos322Research.EisensteinPrimeProducts
noncomputable section
open EisensteinIntegers EisensteinSplitting Finset
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

/-- The family consists of 2^|S| distinct elements of norm product(S).
No quotient by associates, or factorization-counting axiom, is used. -/
theorem exists_norm_family (S : Finset ℕ)
    (hp : ∀ p ∈ S, p.Prime ∧ 3 ∣ p-1) :
    ∃ v : (S → Bool) → E, Function.Injective v ∧
      ∀ c, (v c).norm=((∏ p ∈ S,p : ℕ) : ℤ) := by
  have hex (p : S) : ∃ (v : E) (f : E →+* ZMod p.val),
      v.norm=(p.val : ℤ) ∧ f v=0 ∧ f (star v)≠0 := by
    letI : Fact p.val.Prime := ⟨(hp p p.property).1⟩
    exact exists_separating_prime p (hp p p.property).2
  choose v f hnorm hzero hnonzero using hex
  let chooseFactor (p : S) (b : Bool) : E := if b then v p else star (v p)
  have chosen_norm (p : S) (b : Bool) : (chooseFactor p b).norm=(p.val : ℤ) := by
    cases b <;> simpa [chooseFactor] using hnorm p
  let F (c : S → Bool) : E := ∏ p, chooseFactor p (c p)
  have hF (c : S → Bool) : (F c).norm=((∏ p ∈ S,p : ℕ) : ℤ) := by
    simp only [F,map_prod,chosen_norm]
    simpa only [Nat.cast_prod] using Finset.prod_coe_sort S (fun p : ℕ ↦ (p : ℤ))
  have eval_zero (c : S → Bool) (p : S) : f p (F c)=0 ↔ c p=true := by
    letI : Fact p.val.Prime := ⟨(hp p p.property).1⟩
    simp only [F,map_prod,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨q,hq⟩
      by_cases he : q=p
      · subst q
        cases hc : c p
        · simp only [chooseFactor,hc,Bool.false_eq_true,if_false] at hq
          exact False.elim (hnonzero p hq)
        · rfl
      · have hpm : ¬p.val ∣ q.val := by
          intro hd
          rcases (Nat.dvd_prime (hp q q.property).1).mp hd with h | h
          · exact (hp p p.property).1.ne_one h
          · exact he (Subtype.ext h.symm)
        exact False.elim ((residue_nonzero_of_norm p q (f p)
          (chooseFactor q (c q)) (chosen_norm q (c q)) hpm) hq)
    · intro hc
      refine ⟨p,?_⟩
      simpa [chooseFactor,hc] using hzero p
  refine ⟨F,?_,hF⟩
  intro c d h
  funext p
  have he : c p=true ↔ d p=true := by rw [← eval_zero c p,← eval_zero d p,h]
  cases hc : c p <;> cases hd : d p <;> first | rfl | simp [hc,hd] at he

end
end Erdos322Research.EisensteinPrimeProducts
