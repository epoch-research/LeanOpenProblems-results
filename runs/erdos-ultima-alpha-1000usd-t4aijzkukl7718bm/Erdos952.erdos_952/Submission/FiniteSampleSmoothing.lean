import Submission.FiniteConvolutionSmoothing

/-! Exact finite-sample meaning of iterated correlation. The resulting
functions are probability distributions of actual finite tuples, not a
formal iteration detached from a counting problem. -/
namespace Erdos952Investigation.FiniteSampleSmoothing
open FiniteConvolutionSmoothing
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Uniform finite sample pushed forward by f. -/
def density {Ω : Type*} [Fintype Ω] (f : Ω → G) (x : G) : ℝ :=
  (Nat.card {ω : Ω // f ω = x} : ℝ)/(Fintype.card Ω : ℝ)

omit [AddCommGroup G] [Fintype G] in
lemma density_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (f : Ω → G) (h : Ξ → G) (he : ∀ s, f s = h (e s)) (x : G) :
    density f x = density h x := by
  have hfib := Nat.card_congr (e.subtypeEquiv (p := fun s => f s = x) (q := fun s => h s = x) (fun s => by dsimp; rw [he s]))
  have hc := Fintype.card_congr e
  unfold density
  rw [hfib,hc]

omit [Fintype G] in
lemma density_add_const {Ω : Type*} [Fintype Ω] (f : Ω → G) (a x : G) :
    density (fun s => a+f s) x = density f (x-a) := by
  have he : {s : Ω // a+f s = x} ≃ {s : Ω // f s = x-a} :=
    Equiv.subtypeEquivRight (fun s => by
      rw [eq_sub_iff_add_eq]
      exact ⟨fun h => by simpa only [add_comm] using h,
        fun h => by simpa only [add_comm] using h⟩)
  unfold density
  rw [Nat.card_congr he]

omit [AddCommGroup G] [Fintype G] in
lemma density_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → G) (x : G) : 0 ≤ density f x := by
  unfold density
  positivity

omit [AddCommGroup G] in
lemma density_mass {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → G) : ∑ x, density f x = 1 := by
  have hc : (∑ x : G, (Nat.card {ω : Ω // f ω = x} : ℝ)) = (Fintype.card Ω : ℝ) := by
    have hh := Nat.card_congr (Equiv.sigmaFiberEquiv f)
    rw [Nat.card_sigma,Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  simp only [density,← Finset.sum_div,hc]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

def differenceFiberEquiv {Ω Ξ : Type*} (f : Ω → G) (h : Ξ → G) (x : G) :
    {s : Ω × Ξ // f s.1-h s.2 = x} ≃
      Σ y : G, {ω : Ω // f ω = x+y} × {ξ : Ξ // h ξ = y} where
  toFun s := ⟨h s.val.2,⟨s.val.1,sub_eq_iff_eq_add.mp s.property⟩,⟨s.val.2,rfl⟩⟩
  invFun s := ⟨(s.2.1.val,s.2.2.val),by
    change f s.2.1.val-h s.2.2.val = x
    rw [s.2.1.property,s.2.2.property]
    abel⟩
  left_inv s := rfl
  right_inv s := by
    rcases s with ⟨y,⟨ω,hω⟩,⟨ξ,hξ⟩⟩
    subst y
    rfl

lemma difference_count {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (f : Ω → G) (h : Ξ → G) (x : G) :
    Nat.card {s : Ω × Ξ // f s.1-h s.2 = x} =
      ∑ y, Nat.card {ω : Ω // f ω = x+y}*Nat.card {ξ : Ξ // h ξ = y} := by
  rw [Nat.card_congr (differenceFiberEquiv f h x),Nat.card_sigma]
  simp only [Nat.card_prod]

/-- Difference of independent uniform samples corresponds exactly to corr. -/
theorem density_difference {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (f : Ω → G) (h : Ξ → G) (x : G) :
    density (fun s : Ω × Ξ => f s.1-h s.2) x = corr (density f) (density h) x := by
  simp only [density,difference_count,Fintype.card_prod,Nat.cast_mul,Nat.cast_sum,
    Finset.sum_div,corr]
  apply Finset.sum_congr rfl
  intro y _
  rw [div_mul_div_comm]

/-- Recursive tuples. Sample Ω n contains n+1 independent samples from Ω. -/
def Sample (Ω : Type*) : ℕ → Type _
  | 0 => Ω
  | n+1 => Sample Ω n × Ω

instance sampleFintype {Ω : Type*} [Fintype Ω] (n : ℕ) : Fintype (Sample Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Ω)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Sample Ω n × Ω))

instance sampleNonempty {Ω : Type*} [Nonempty Ω] (n : ℕ) : Nonempty (Sample Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Ω)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Nonempty (Sample Ω n × Ω))

lemma sample_card {Ω : Type*} [Fintype Ω] (n : ℕ) :
    Fintype.card (Sample Ω n) = (Fintype.card Ω)^(n+1) := by
  induction n with
  | zero => simp only [Sample,Nat.zero_add,pow_one]
  | succ n ih =>
    change Fintype.card (Sample Ω n × Ω) = _
    rw [Fintype.card_prod,ih]
    exact (pow_succ _ _).symm

def value {Ω : Type*} (f : Ω → G) : (n : ℕ) → Sample Ω n → G
  | 0 => f
  | n+1 => fun s => value f n s.1-f s.2

/-- Exact identification of every iterate with a finite counting measure. -/
theorem density_value {Ω : Type*} [Fintype Ω] (f : Ω → G) (n : ℕ) (x : G) :
    density (value f n) x = iter (density f) n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change density (fun s : Sample Ω n × Ω => value f n s.1-f s.2) x = _
    rw [density_difference]
    change corr (density (value f n)) (density f) x = corr (iter (density f) n) (density f) x
    rw [funext ih]

/-- The geometric error estimate is therefore an estimate for actual tuple
counts. The source need not be an additive group. -/
theorem sample_error_ratio {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → G) (κ : ℝ) (hκ : 0 ≤ κ)
    (hf : ∀ x, |density f x-1/(Fintype.card G : ℝ)| ≤ κ/(Fintype.card G : ℝ))
    (n : ℕ) (x : G) :
    |density (value f n) x-1/(Fintype.card G : ℝ)| ≤ κ^(n+1)/(Fintype.card G : ℝ) := by
  rw [density_value]
  exact iter_error_ratio (density f) (density_mass f) κ hκ hf n x

#print axioms density_difference
#print axioms density_value
#print axioms sample_error_ratio
end
end Erdos952Investigation.FiniteSampleSmoothing
