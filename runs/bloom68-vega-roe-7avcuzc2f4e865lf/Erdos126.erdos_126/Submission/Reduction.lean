import FormalConjecturesUtil

/-!
# An extremal-function reduction for Erdős problem 126

This file is independent of `Submission.Spec`.  It uses the product over ordered
pairs of distinct elements, exactly as in the conjecture.  It proves positivity
of that product, existence and uniqueness of the extremal function, and attainment
of every extremal value.  The asymptotic arithmetic bound itself is not assumed
as an axiom or proved here: it appears as the hypothesis of the reduction.
-/

open Filter

namespace Erdos126Reduction

/-- The product of the pair sums over the ordered off-diagonal. -/
def sumProduct (A : Finset ℕ) : ℕ :=
  ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)

/-- The number of distinct prime divisors of the pair-sum product. -/
def P (A : Finset ℕ) : ℕ :=
  (sumProduct A).primeFactors.card

/-- The original greatest-universal-lower-bound specification of `f`. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n, IsGreatest
    {m | ∀ A : Finset ℕ, A.card = n → m ≤ P A}
    (f n)

/-- Distinct natural numbers have a strictly positive sum, even if one is zero. -/
theorem sum_pos_of_mem_offDiag {A : Finset ℕ} {a b : ℕ}
    (hab : (a, b) ∈ A.offDiag) : 0 < a + b := by
  have hne : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
  omega

/-- In particular the product used in `P` is never zero. -/
theorem sumProduct_pos (A : Finset ℕ) : 0 < sumProduct A := by
  unfold sumProduct
  apply Finset.prod_pos
  rintro ⟨a, b⟩ hab
  exact sum_pos_of_mem_offDiag hab

theorem sumProduct_ne_zero (A : Finset ℕ) : sumProduct A ≠ 0 :=
  ne_of_gt (sumProduct_pos A)

@[simp] theorem P_empty : P ∅ = 0 := by
  simp [P, sumProduct]

@[simp] theorem P_singleton (a : ℕ) : P {a} = 0 := by
  simp [P, sumProduct, Finset.offDiag_singleton]

/-- A canonical extremal function, defined by minimizing the attained values. -/
noncomputable def extremal (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℕ, A.card = n ∧ P A = m}

/-- The defining set is nonempty (use `Finset.range n`), so its natural-number
infimum is itself attained. -/
theorem extremal_attained (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ P A = extremal n := by
  have hnonempty : {m : ℕ | ∃ A : Finset ℕ, A.card = n ∧ P A = m}.Nonempty :=
    ⟨P (Finset.range n), Finset.range n, Finset.card_range n, rfl⟩
  exact Nat.sInf_mem hnonempty

/-- The canonical extremal value is a lower bound for every set of that size. -/
theorem extremal_le {n : ℕ} {A : Finset ℕ} (hA : A.card = n) :
    extremal n ≤ P A := by
  exact Nat.sInf_le ⟨A, hA, rfl⟩

/-- The attained minimum satisfies the original `IsGreatest` specification. -/
theorem extremal_spec : IsMaximalAddFactorsCard extremal := by
  intro n
  refine ⟨fun A hA => extremal_le hA, ?_⟩
  intro m hm
  obtain ⟨A, hA, hP⟩ := extremal_attained n
  simpa only [hP] using hm A hA

/-- Any two functions satisfying the specification agree everywhere. -/
theorem spec_unique {f g : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f) (hg : IsMaximalAddFactorsCard g) : f = g := by
  funext n
  exact (hf n).unique (hg n)

theorem exists_spec : ∃ f : ℕ → ℕ, IsMaximalAddFactorsCard f :=
  ⟨extremal, extremal_spec⟩

theorem existsUnique_spec : ∃! f : ℕ → ℕ, IsMaximalAddFactorsCard f := by
  refine ⟨extremal, extremal_spec, ?_⟩
  intro f hf
  exact spec_unique hf extremal_spec

/-- Attainment for an arbitrary function satisfying the original specification. -/
theorem attained {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ P A = f n := by
  rw [spec_unique hf extremal_spec]
  exact extremal_attained n

/-- The lower-bound half of the specification, indexed by the actual cardinality. -/
theorem le_P {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) (A : Finset ℕ) :
    f A.card ≤ P A :=
  (hf A.card).1 A rfl

/-- The logarithmic denominator vanishes at these small sizes, which are excluded
by the thresholds in the asymptotic reduction. -/
theorem spec_zero {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) : f 0 = 0 := by
  have h := le_P hf ∅
  simpa using h

theorem spec_one {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) : f 1 = 0 := by
  have h := le_P hf {0}
  simpa using h

/-- The actual universally quantified asymptotic conjecture. -/
def Conjecture : Prop :=
  ∀ f : ℕ → ℕ, IsMaximalAddFactorsCard f →
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop

/-- The uniform arithmetic lower bound sufficient for the conjecture. -/
def UniformBound : Prop :=
  ∀ C : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
    C * Real.log (A.card : ℝ) ≤ (P A : ℝ)

/-- An equivalent version that explicitly avoids cardinalities zero and one. -/
def UniformBoundFromTwo : Prop :=
  ∀ C : ℝ, ∃ N : ℕ, 2 ≤ N ∧ ∀ A : Finset ℕ, N ≤ A.card →
    C * Real.log (A.card : ℝ) ≤ (P A : ℝ)

/-- Increasing a threshold to `max N 2` does not change the uniform bound. -/
theorem uniformBound_iff_fromTwo : UniformBound ↔ UniformBoundFromTwo := by
  constructor
  · intro h C
    obtain ⟨N, hN⟩ := h C
    refine ⟨max N 2, le_max_right N 2, ?_⟩
    intro A hA
    exact hN A ((le_max_left N 2).trans hA)
  · intro h C
    obtain ⟨N, _, hN⟩ := h C
    exact ⟨N, hN⟩

/-- Division by `log n` is order-preserving once `n ≥ 2`. -/
theorem log_nat_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < n by omega)

/-- The uniform bound applies to an attaining set at each cardinality, so it
forces every specified extremal function to grow faster than `log n`. -/
theorem tendsto_of_uniformBound {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f)
    (h : UniformBound) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro C
  obtain ⟨N, hNtwo, hN⟩ := uniformBound_iff_fromTwo.mp h C
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨A, hcard, hP⟩ := attained hf n
  have hbound := hN A (by simpa only [hcard] using hn)
  rw [hcard, hP] at hbound
  exact (le_div_iff₀ (log_nat_pos (hNtwo.trans hn))).mpr hbound

/-- Conversely, the limit gives a bound for `f(A.card)`, which is a lower bound
for `P A`.  The threshold is explicitly at least two. -/
theorem uniformBoundFromTwo_of_tendsto {f : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f)
    (h : Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop) :
    UniformBoundFromTwo := by
  intro C
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp h C
  refine ⟨max N 2, le_max_right N 2, ?_⟩
  intro A hA
  have hlog : 0 < Real.log (A.card : ℝ) :=
    log_nat_pos ((le_max_right N 2).trans hA)
  have hratio := hN A.card ((le_max_left N 2).trans hA)
  have hbound : C * Real.log (A.card : ℝ) ≤ (f A.card : ℝ) :=
    (le_div_iff₀ hlog).mp hratio
  exact hbound.trans (Nat.cast_le.mpr (le_P hf A))

theorem uniformBound_of_tendsto {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f)
    (h : Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop) :
    UniformBound :=
  uniformBound_iff_fromTwo.mpr (uniformBoundFromTwo_of_tendsto hf h)

/-- Equivalence for any function satisfying the greatest-lower-bound specification. -/
theorem tendsto_iff_uniformBound {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      UniformBound :=
  ⟨uniformBound_of_tendsto hf, tendsto_of_uniformBound hf⟩

theorem tendsto_iff_uniformBoundFromTwo {f : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      UniformBoundFromTwo :=
  (tendsto_iff_uniformBound hf).trans uniformBound_iff_fromTwo

/-- Existence of `extremal` makes the entire conjecture equivalent to the uniform
bound, not merely an implication with a possibly vacuous specification. -/
theorem conjecture_iff_uniformBound : Conjecture ↔ UniformBound := by
  constructor
  · intro h
    exact uniformBound_of_tendsto extremal_spec (h extremal extremal_spec)
  · intro h f hf
    exact tendsto_of_uniformBound hf h

/-- The same full equivalence with all thresholds constrained to be at least two. -/
theorem conjecture_iff_uniformBoundFromTwo : Conjecture ↔ UniformBoundFromTwo :=
  conjecture_iff_uniformBound.trans uniformBound_iff_fromTwo

/-- It also suffices to state the limit for the explicitly constructed function. -/
theorem conjecture_iff_extremal_tendsto : Conjecture ↔
    Tendsto (fun n : ℕ => (extremal n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  conjecture_iff_uniformBound.trans (tendsto_iff_uniformBound extremal_spec).symm

end Erdos126Reduction
