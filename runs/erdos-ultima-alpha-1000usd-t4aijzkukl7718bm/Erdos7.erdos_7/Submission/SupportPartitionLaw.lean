import Submission.SupportCriterion

/-! Symmetric multiset states for arbitrary finite prime-support bounds.
This is an exact finite law representation, not a uniform numerical sieve
certificate or a proof of the odd covering conjecture. -/
namespace Erdos7SupportPartitionLaw
open scoped BigOperators
open Erdos7SupportCompression
set_option autoImplicit false
set_option maxHeartbeats 3000000

lemma esymm_zero (s : Multiset ℕ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

lemma esymm_cons (a : ℕ) (s : Multiset ℕ) (k : ℕ) :
    (a ::ₘ s).esymm (k+1) = s.esymm (k+1) + a*s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add,
    Multiset.sum_add, Multiset.map_map, Function.comp_def, Multiset.prod_cons,
    Multiset.sum_map_mul_left]

/-- The sum of elementary symmetric counts through degree d. -/
noncomputable def count (d : ℕ) (s : Multiset ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d+1), s.esymm k

@[simp] lemma count_zero (s : Multiset ℕ) : count 0 s = 1 := by
  simp [count, esymm_zero]

lemma count_cons (d a : ℕ) (s : Multiset ℕ) :
    count (d+1) (a ::ₘ s) = count (d+1) s + a*count d s := by
  unfold count
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (f := fun k => s.esymm k) (n := d+1)]
  simp only [esymm_zero, esymm_cons, Finset.sum_add_distrib, Finset.mul_sum]
  ring

@[simp] lemma count_empty (d : ℕ) : count d 0 = 1 := by
  unfold count
  rw [Finset.sum_range_succ']
  simp [Multiset.esymm]

/-- Multiplicities indexed by already-used support size. -/
noncomputable def multiplicity (d : ℕ) (s : Multiset ℕ) (r : ℕ) : ℕ :=
  if r ≤ d then count (d-r) s else 0

@[simp] lemma multiplicity_empty (d : ℕ) : multiplicity d 0 = supportMultiplicity d := by
  funext r
  simp [multiplicity, supportMultiplicity]

lemma push_multiplicity (d a : ℕ) (s : Multiset ℕ) :
    pushMultiplicity (multiplicity d s) a = multiplicity d (a ::ₘ s) := by
  funext r
  by_cases hr : r < d
  · have hr0 : r ≤ d := by omega
    have hr1 : r+1 ≤ d := by omega
    have he : d-r = (d-(r+1))+1 := by omega
    simp only [pushMultiplicity, multiplicity, if_pos hr0, if_pos hr1]
    rw [he, count_cons]
  · by_cases he : r = d
    · subst r
      simp [pushMultiplicity, multiplicity]
    · have hr0 : ¬ r ≤ d := by omega
      have hr1 : ¬ r+1 ≤ d := by omega
      simp only [pushMultiplicity, multiplicity, if_neg hr0, if_neg hr1, mul_zero, add_zero]

lemma multiplicity_zero (d : ℕ) (s : Multiset ℕ) : multiplicity d s 0 = count d s := by
  simp [multiplicity]

/-- All increment orders give the same state; no labeled-prime information
is needed to evaluate the support count once the increments are known. -/
lemma count_cons_transfer (d a : ℕ) (s t : Multiset ℕ) :
    count d ((a ::ₘ s)+t) = count d (s+(a ::ₘ t)) := by
  congr 1
  simp [Multiset.cons_add, Multiset.add_cons]

noncomputable def expect (μ : Multiset ℕ →₀ ℚ) (f : Multiset ℕ → ℚ) : ℚ :=
  μ.sum (fun s w => w*f s)

lemma expect_congr (μ : Multiset ℕ →₀ ℚ) {f g : Multiset ℕ → ℚ}
    (h : ∀ s, f s = g s) : expect μ f = expect μ g := by
  unfold expect
  apply Finsupp.sum_congr
  intro s _
  rw [h s]

lemma expect_add (μ ν : Multiset ℕ →₀ ℚ) (f : Multiset ℕ → ℚ) :
    expect (μ+ν) f = expect μ f + expect ν f := by
  unfold expect
  exact Finsupp.sum_add_index (by intros; simp) (by intros; ring)

lemma expect_smul (a : ℚ) (μ : Multiset ℕ →₀ ℚ) (f : Multiset ℕ → ℚ) :
    expect (a • μ) f = a*expect μ f := by
  unfold expect
  rw [Finsupp.sum_smul_index (by intros; simp)]
  simp only [Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma expect_sum {I : Type*} (S : Finset I) (μ : I → Multiset ℕ →₀ ℚ)
    (f : Multiset ℕ → ℚ) : expect (∑ i ∈ S, μ i) f = ∑ i ∈ S, expect (μ i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [expect]
  | @insert i S hi ih => rw [Finset.sum_insert hi, expect_add, Finset.sum_insert hi, ih]

lemma expect_map (a : ℕ) (μ : Multiset ℕ →₀ ℚ) (f : Multiset ℕ → ℚ) :
    expect (μ.mapDomain (Multiset.cons a)) f = expect μ (fun s => f (a ::ₘ s)) := by
  unfold expect
  exact Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)

noncomputable def initial : Multiset ℕ →₀ ℚ := Finsupp.single 0 1

noncomputable def step (E : ℕ) (q : ℕ → ℚ) (μ : Multiset ℕ →₀ ℚ) : Multiset ℕ →₀ ℚ :=
  (1-q 0) • μ + ∑ g ∈ Finset.range E, (q g-q (g+1)) • μ.mapDomain (Multiset.cons (g+1))

lemma expect_initial (f : Multiset ℕ → ℚ) : expect initial f = f 0 := by
  simp [initial, expect]

lemma expect_step (E : ℕ) (q : ℕ → ℚ) (μ : Multiset ℕ →₀ ℚ) (f : Multiset ℕ → ℚ) :
    expect (step E q μ) f = (1-q 0)*expect μ f +
      ∑ g ∈ Finset.range E, (q g-q (g+1))*expect μ (fun s => f ((g+1) ::ₘ s)) := by
  simp only [step, expect_add, expect_smul, expect_sum, expect_map]

noncomputable def prefixLaw {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) :
    ℕ → (Multiset ℕ →₀ ℚ)
  | 0 => initial
  | t+1 => if h : t < n then step (E ⟨t,h⟩) (q ⟨t,h⟩) (prefixLaw E q t)
      else prefixLaw E q t

/-- Exact finite expectation representation, retaining all exponent levels.
The count depends only on the multiset of increments and the support bound. -/
theorem supportEnvelope_eq {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (φ : ℚ → ℚ) (t d : ℕ) (s : Multiset ℕ) :
    supportEnvelope E q φ t (multiplicity d s) =
      expect (prefixLaw E q t) (fun v => φ (count d (s+v))) := by
  induction t generalizing s with
  | zero => simp [supportEnvelope, prefixLaw, expect_initial, multiplicity_zero]
  | succ t ih =>
    simp only [supportEnvelope, prefixLaw]
    split_ifs
    · rw [expect_step, ih]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      rw [push_multiplicity, ih]
      congr 1
      apply expect_congr
      intro v
      rw [count_cons_transfer]
    · exact ih s

theorem supportEnvelope_initial_eq {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (φ : ℚ → ℚ) (t d : ℕ) :
    supportEnvelope E q φ t (supportMultiplicity d) =
      expect (prefixLaw E q t) (fun v => φ (count d v)) := by
  rw [← multiplicity_empty d, supportEnvelope_eq]
  apply expect_congr
  intro v
  simp

#print axioms count_cons
#print axioms push_multiplicity
#print axioms supportEnvelope_eq
#print axioms supportEnvelope_initial_eq
end Erdos7SupportPartitionLaw
