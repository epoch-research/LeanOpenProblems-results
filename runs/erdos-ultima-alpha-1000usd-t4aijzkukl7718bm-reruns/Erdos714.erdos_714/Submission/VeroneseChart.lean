import Submission.QuadraticProfileThinning

/-!
A chart-level obstruction to a proposed quadratic projective-coordinate
construction. The actual incidence equation and its code identification are
checked. This is not a classification of projective varieties and does not
prove or disprove Erdős 714.
-/

noncomputable section
open Classical SimpleGraph Erdos714Tensor
set_option maxHeartbeats 1000000

namespace Erdos714VeroneseChart

variable {F C : Type*} [Field F]

/-- An affine chart of the quadratic projective embedding of the plane. -/
def point (s t : F) : Fin 6 → F := ![1, s, t, s^2, s*t, t^2]

def constant (s : F) : Fin 6 → F := ![1, s, 0, s^2, 0, 0]
def linear (s : F) : Fin 6 → F := ![0, 0, 1, 0, s, 0]
def quadratic : Fin 6 → F := ![0, 0, 0, 0, 0, 1]

lemma point_expansion (s t : F) :
    point s t = constant s + t • linear s + t^2 • quadratic := by
  ext i
  fin_cases i <;> simp [point, constant, linear, quadratic, mul_comm]

/-- Column coordinates are ((first point coordinate, second weight),
second point coordinate), first weight. -/
abbrev Columns (F : Type*) := ((F × F) × F) × F

/-- An arbitrary row functional and two weight coefficients. The first weight
coefficient is nonzero, rather than silently divided by zero. -/
def host (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F) :
    SimpleGraph (C ⊕ Columns F) :=
  incidence fun c v => (a c : F)*v.2 + b c*v.1.1.2 = L c (point v.1.1.1 v.1.2)

/-- The uniquely determined first column weight. -/
def code (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F)
    (c : C) (i : (F × F) × F) : F :=
  (L c (point i.1.1 i.2) - b c*i.1.2)/(a c : F)

lemma incidence_iff (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F)
    (c : C) (v : Columns F) :
    ((a c : F)*v.2 + b c*v.1.1.2 = L c (point v.1.1.1 v.1.2)) ↔
      code L a b c v.1 = v.2 := by
  rw [code, div_eq_iff (a c).ne_zero]
  constructor <;> intro h <;> linear_combination -h

lemma host_eq_code [Fintype F] (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F) :
    host L a b = Erdos714Coding.graph (code L a b) := by
  ext v w
  cases v with
  | inl c =>
    cases w with
    | inl d => rfl
    | inr v =>
      change _ ↔ v ∈ Erdos714Coding.symbols (code L a b) c
      rw [Erdos714Coding.mem_symbols]
      exact incidence_iff L a b c v
  | inr v =>
    cases w with
    | inr w => rfl
    | inl c =>
      change _ ↔ v ∈ Erdos714Coding.symbols (code L a b) c
      rw [Erdos714Coding.mem_symbols]
      exact incidence_iff L a b c v

lemma code_quadratic (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F)
    (c : C) (x : F × F) (t : F) :
    code L a b c (x,t) = (L c (constant x.1)-b c*x.2)/(a c : F) +
      (L c (linear x.1)/(a c : F))*t + (L c quadratic/(a c : F))*t^2 := by
  simp only [code, point_expansion, map_add, map_smul, smul_eq_mul]
  ring

variable [Fintype F] [Fintype C]

/-- The unthinned chart has precisely q cubed neighbors at every row. -/
theorem host_edges (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F) :
    (host L a b).edgeFinset.card = Fintype.card C * Fintype.card F^3 := by
  rw [host_eq_code, Erdos714Coding.edge_count]
  simp [pow_succ, mul_assoc]

/-- Arbitrary edge thinning cannot retain the proposed critical order of magnitude. -/
theorem thinning_bound (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F)
    (H : SimpleGraph (C ⊕ Columns F)) (hH : H ≤ host L a b)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hC : Fintype.card C ≤ Fintype.card F^4) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  apply Erdos714QuadraticProfileThinning.fourth_power_bound (code L a b)
    (fun x c => (L c (constant x.1)-b c*x.2)/(a c : F))
    (fun x c => L c (linear x.1)/(a c : F))
    (fun _ c => L c quadratic/(a c : F)) (code_quadratic L a b)
    H (by simpa only [host_eq_code] using hH) hf _ hC
  simp [pow_two]

/-- A fixed multiplicative critical-density constant forces a bounded field order. -/
theorem size_budget (L : C → (Fin 6 → F) →ₗ[F] F) (a : C → Fˣ) (b : C → F)
    (H : SimpleGraph (C ⊕ Columns F)) (hH : H ≤ host L a b)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (hC : Fintype.card C ≤ Fintype.card F^4)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*K^4 := by
  have he := thinning_bound L a b H hH hf hC
  have hh : Fintype.card F^27 * Fintype.card F ≤ Fintype.card F^27 * (165888*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

end Erdos714VeroneseChart

#print axioms Erdos714VeroneseChart.point_expansion
#print axioms Erdos714VeroneseChart.host_eq_code
#print axioms Erdos714VeroneseChart.host_edges
#print axioms Erdos714VeroneseChart.thinning_bound
#print axioms Erdos714VeroneseChart.size_budget
