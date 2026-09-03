import Submission.ArithmeticReduction

/-! Finite-index realizations of the ordered cubic prime budget. -/
namespace Erdos7CubicSieve
open scoped BigOperators
set_option maxHeartbeats 4000000

variable {n : ℕ}

def primePrefix (p : Fin n → ℕ) (start t : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun i => start ≤ i.val ∧ i.val < t)).image p

lemma mem_primePrefix (p : Fin n → ℕ) (start t q : ℕ) :
    q∈primePrefix p start t ↔ ∃ i : Fin n,start ≤ i.val ∧ i.val < t ∧ p i=q := by
  simp only [primePrefix,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  aesop

lemma primePrefix_empty (p : Fin n → ℕ) (start t : ℕ) (ht : t ≤ start) : primePrefix p start t=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨i,hi0,hi1,heq⟩ := (mem_primePrefix p start t q).mp hq
  omega

lemma primePrefix_succ (p : Fin n → ℕ) (start : ℕ) (i : Fin n) (hi : start ≤ i.val) :
    primePrefix p start (i.val+1)=insert (p i) (primePrefix p start i.val) := by
  ext q
  simp only [mem_primePrefix,Finset.mem_insert]
  constructor
  · rintro ⟨j,hj0,hj1,hjp⟩
    by_cases hji : j.val < i.val
    · exact Or.inr ⟨j,hj0,hji,hjp⟩
    · have heq : j=i := Fin.ext (by omega)
      exact Or.inl (by simpa only [heq] using hjp.symm)
  · rintro (heq | ⟨j,hj0,hj1,hjp⟩)
    · exact ⟨i,hi,by omega,heq.symm⟩
    · exact ⟨j,hj0,by omega,hjp⟩

lemma primePrefix_lt (p : Fin n → ℕ) (hp : StrictMono p) (start : ℕ) (i : Fin n)
    (q : ℕ) (hq : q∈primePrefix p start i.val) : q < p i := by
  obtain ⟨j,hj0,hj1,rfl⟩ := (mem_primePrefix p start i.val q).mp hq
  exact hp hj1

lemma primePrefix_budgetProduct_succ (p : Fin n → ℕ) (hp : StrictMono p) (start : ℕ)
    (i : Fin n) (hi : start ≤ i.val) :
    budgetProduct (primePrefix p start (i.val+1))=multiplier (p i)*budgetProduct (primePrefix p start i.val) := by
  rw [primePrefix_succ p start i hi]
  have hnot : p i∉primePrefix p start i.val := by
    intro h; exact (lt_irrefl _) (primePrefix_lt p hp start i _ h)
  rw [budgetProduct,Finset.prod_insert hnot]
  rfl

lemma primePrefix_budgetCost_succ (p : Fin n → ℕ) (hp : StrictMono p) (start : ℕ)
    (i : Fin n) (hi : start ≤ i.val) :
    budgetCost (primePrefix p start (i.val+1))=budgetCost (primePrefix p start i.val)+
      charge (p i)*budgetProduct (primePrefix p start i.val) := by
  rw [primePrefix_succ p start i hi]
  have heq : insert (p i) (primePrefix p start i.val)=primePrefix p start i.val∪{p i} := by
    ext q; simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]; tauto
  rw [heq,budgetCost_union (by
    intro q hq r hr
    have hr' : r=p i := Finset.mem_singleton.mp hr
    subst r
    exact primePrefix_lt p hp start i q hq),budgetCost_singleton]
  ring

noncomputable def sequenceCubic (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (t : ℕ) : ℚ :=
  C*budgetProduct (primePrefix p start t)
noncomputable def sequenceCost (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (t : ℕ) : ℚ :=
  C*budgetCost (primePrefix p start t)
noncomputable def sequenceLoss (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (i : Fin n) : ℚ :=
  charge (p i)*sequenceCubic p start C i.val

lemma sequenceCubic_initial (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (t : ℕ) (ht : t ≤ start) :
    sequenceCubic p start C t=C := by
  simp only [sequenceCubic,primePrefix_empty p start t ht,budgetProduct_empty,mul_one]

lemma sequenceCost_initial (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (t : ℕ) (ht : t ≤ start) :
    sequenceCost p start C t=0 := by
  simp only [sequenceCost,primePrefix_empty p start t ht,budgetCost_empty,mul_zero]

lemma sequenceCubic_succ (p : Fin n → ℕ) (hp : StrictMono p) (start : ℕ) (C : ℚ)
    (i : Fin n) (hi : start ≤ i.val) :
    sequenceCubic p start C (i.val+1)=multiplier (p i)*sequenceCubic p start C i.val := by
  simp only [sequenceCubic,primePrefix_budgetProduct_succ p hp start i hi]
  ring

lemma sequenceCost_succ (p : Fin n → ℕ) (hp : StrictMono p) (start : ℕ) (C : ℚ)
    (i : Fin n) (hi : start ≤ i.val) :
    sequenceCost p start C (i.val+1)=sequenceCost p start C i.val+sequenceLoss p start C i := by
  simp only [sequenceCost,sequenceLoss,sequenceCubic,primePrefix_budgetCost_succ p hp start i hi]
  ring

lemma sequenceCubic_nonneg (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (hC : 0 ≤ C)
    (hp : ∀ i : Fin n,start ≤ i.val → 5 ≤ p i) (t : ℕ) : 0 ≤ sequenceCubic p start C t := by
  apply mul_nonneg hC
  apply budgetProduct_nonneg
  intro q hq
  obtain ⟨i,hi0,hi1,rfl⟩ := (mem_primePrefix p start t q).mp hq
  exact hp i hi0

lemma sequenceCost_nonneg (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (hC : 0 ≤ C)
    (hp : ∀ i : Fin n,start ≤ i.val → 5 ≤ p i) (t : ℕ) : 0 ≤ sequenceCost p start C t := by
  apply mul_nonneg hC
  apply budgetCost_nonneg
  intro q hq
  obtain ⟨i,hi0,hi1,rfl⟩ := (mem_primePrefix p start t q).mp hq
  exact hp i hi0

lemma sequenceCost_bound (p : Fin n → ℕ) (start : ℕ) (C : ℚ) (hC : 0 ≤ C)
    (N : ℕ) (hN : 1000000 ≤ N) (hp : ∀ i : Fin n,start ≤ i.val → (p i).Prime ∧ N ≤ p i)
    (t : ℕ) : sequenceCost p start C t ≤ C*(6/(N:ℚ)^2) := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply tail_cost_bound N hN
  intro q hq
  obtain ⟨i,hi0,hi1,rfl⟩ := (mem_primePrefix p start t q).mp hq
  exact hp i hi0

#print axioms sequenceCost_bound
end Erdos7CubicSieve
