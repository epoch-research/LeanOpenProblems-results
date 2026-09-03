import Submission.ExclusivePrefix

/-! Exact decomposition of the conditional-exit measure by first exit depth.
All finite endpoint mass is retained. -/
namespace Erdos7ExitDepthDecomposition
open scoped BigOperators
open Erdos7ConditionalExitMeasure Erdos7ExclusivePrefix
set_option autoImplicit false
set_option maxHeartbeats 2000000

def code {p : ℕ} (stem exit : Fin p) : (b : ℕ) → Fin (b+1) → Fin p
  | 0 => Fin.cons exit (fun i => i.elim0)
  | b+1 => Fin.cons stem (code stem exit b)

@[simp] lemma code_zero {p : ℕ} (stem exit : Fin p) : code stem exit 0 0=exit := rfl
@[simp] lemma code_succ_zero {p b : ℕ} (stem exit : Fin p) :
    code stem exit (b+1) 0=stem := rfl
@[simp] lemma code_tail {p b : ℕ} (stem exit : Fin p) :
    Fin.tail (code stem exit (b+1))=code stem exit b := by rfl

lemma terminal_count {p E : ℕ} (stem exit : Fin p) (hne : exit ≠ stem)
    (y : Fin E → Fin p) :
    (∑ b : Fin E, if prefixMatch (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) y
      then (1 : ℕ) else 0) =
      if firstExit stem E y=some exit then 1 else 0 := by
  induction E with
  | zero => simp [firstExit]
  | succ E ih =>
    rw [Fin.sum_univ_succ]
    have hzero : prefixMatch (Nat.succ_le_of_lt (show 0 < E+1 by omega))
        (code stem exit 0) y ↔ y 0=exit := by
      simp [prefixMatch, Fin.forall_fin_one]
    have hsucc (b : Fin E) :
        prefixMatch (Nat.succ_le_of_lt b.succ.isLt) (code stem exit b.succ.val) y ↔
          y 0=stem ∧ prefixMatch (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) (Fin.tail y) := by
      change (∀ i : Fin (b.val+1+1), y (Fin.castLE _ i)=code stem exit (b.val+1) i) ↔ _
      rw [Fin.forall_fin_succ]
      rfl
    simp only [Fin.val_zero, hzero, hsucc, ite_and, Finset.sum_ite_irrel]
    rw [ih]
    by_cases hs : y 0=stem
    · have hx : y 0 ≠ exit := by intro h; exact hne (h.symm.trans hs)
      simp [firstExit, hs, hne.symm]
    · simp [firstExit, hs]

/-- Uniform probability on an arbitrary fixed prefix cylinder. -/
def cylinderDensity {p a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p)
    (y : Fin E → Fin p) : ℚ :=
  (if prefixMatch ha v y then 1 else 0)/(p : ℚ)^(E-a)

lemma cylinderDensity_nonneg {p a E : ℕ} (ha : a ≤ E) (v : Fin a → Fin p)
    (y : Fin E → Fin p) : 0 ≤ cylinderDensity ha v y := by
  unfold cylinderDensity
  positivity

theorem cylinderDensity_mass {p a E : ℕ} (hp : 1 ≤ p) (ha : a ≤ E)
    (v : Fin a → Fin p) : (∑ y, cylinderDensity ha v y)=1 := by
  have hc : (∑ y : Fin E → Fin p, if prefixMatch ha v y then (1 : ℚ) else 0) =
      (p : ℚ)^(E-a) := by exact_mod_cast prefix_count ha v
  unfold cylinderDensity
  rw [← Finset.sum_div, hc]
  apply div_self
  positivity

lemma raw_decomposition {p E : ℕ} (stem exit : Fin p) (hne : exit ≠ stem)
    (y : Fin E → Fin p) :
    raw stem exit E y =
      (if prefixMatch (Nat.le_refl E) (fun _ => stem) y then 1 else 0)+
      (p-1)*(∑ b : Fin E,
        if prefixMatch (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) y then 1 else 0) := by
  rw [terminal_count stem exit hne, raw_classified]
  have he : prefixMatch (Nat.le_refl E) (fun _ => stem) y ↔ firstExit stem E y=none := by
    rw [firstExit_eq_none_iff]
    rfl
  simp only [he]
  cases firstExit stem E y with
  | none => simp
  | some d => by_cases h : d=exit <;> simp [h]

/-- The atom at the finite all-stem endpoint and every genuine exit layer
are present, with their exact geometric coefficients. -/
theorem density_decomposition {p E : ℕ} (hp : 1 ≤ p) (stem exit : Fin p)
    (hne : exit ≠ stem) (y : Fin E → Fin p) :
    density stem exit y =
      (1/(p : ℚ)^E)*cylinderDensity (Nat.le_refl E) (fun _ => stem) y+
      ∑ b : Fin E, ((p-1 : ℕ) : ℚ)/(p : ℚ)^(b.val+1)*
        cylinderDensity (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) y := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hr := raw_decomposition stem exit hne y
  have he (b : Fin E) : ((p-1 : ℕ) : ℚ)/(p : ℚ)^(b.val+1)*
      cylinderDensity (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) y =
      ((p-1 : ℕ) : ℚ)/(p : ℚ)^E *
        (if prefixMatch (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) y then 1 else 0) := by
    have hpow : (p : ℚ)^E = (p : ℚ)^(b.val+1)*(p : ℚ)^(E-(b.val+1)) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt b.isLt)]
    unfold cylinderDensity
    rw [hpow]
    field_simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hcast := congrArg (fun n : ℕ => (n : ℚ)) hr
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcast
  unfold density
  rw [hcast]
  simp only [cylinderDensity, Nat.sub_self, pow_zero, div_one]
  ring

/-- Integration against the exit measure is an exact positive mixture of
integrals against uniform prefix cylinders. -/
theorem sum_density_decomposition {p E : ℕ} (hp : 1 ≤ p) (stem exit : Fin p)
    (hne : exit ≠ stem) (f : (Fin E → Fin p) → ℚ) :
    (∑ y, density stem exit y*f y) =
      (1/(p : ℚ)^E)*(∑ y, cylinderDensity (Nat.le_refl E) (fun _ => stem) y*f y)+
      ∑ b : Fin E, ((p-1 : ℕ) : ℚ)/(p : ℚ)^(b.val+1)*
        (∑ y, cylinderDensity (Nat.succ_le_of_lt b.isLt) (code stem exit b.val) y*f y) := by
  simp_rw [density_decomposition hp stem exit hne, add_mul, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro _ _
  · ring
  · apply Finset.sum_congr rfl
    intro _ _
    ring

#print axioms terminal_count
#print axioms cylinderDensity_mass
#print axioms density_decomposition
#print axioms sum_density_decomposition
end Erdos7ExitDepthDecomposition
