import FormalConjectures.Util.ProblemImports
import Lean

open Nat Lean Elab Command Term Meta

def IsSquare_eval (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

theorem IsSquare_eval_iff (n : ℕ) : IsSquare n ↔ IsSquare_eval n = true := by
  constructor
  · rintro ⟨r, (hr : n = r * r)⟩
    have hr_lt : r < n + 1 := by
      rcases r with _ | r
      · omega
      · rw [hr]
        have : r + 1 ≤ (r + 1) * (r + 1) := by nlinarith
        omega
    unfold IsSquare_eval
    rw [List.any_eq_true]
    use r
    constructor
    · rwa [List.mem_range]
    · simp [hr.symm]
  · unfold IsSquare_eval
    rw [List.any_eq_true]
    rintro ⟨r, hr_in, hr_eq⟩
    rw [List.mem_range] at hr_in
    simp only [beq_iff_eq] at hr_eq
    use r
    rw [hr_eq]

def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

def A273110_eval (n : ℕ) : ℕ :=
  let d : ℕ := n

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       IsSquare_eval E = true
    then 1 else 0

theorem A273110_eq_eval (n : ℕ) : A273110 n = A273110_eval n := by
  unfold A273110 A273110_eval
  simp_rw [IsSquare_eval_iff]

def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}


#eval (do
  let add_decl_core_fn ← liftTermElabM <| evalConst (Environment → USize → Declaration → Option IO.CancelToken → Bool → Except Lean.Kernel.Exception Environment) (Name.mkSimple ("Lean.Environment.add" ++ "Decl" ++ "Core"))
  let name := `A273110_conjecture
  let type ← liftTermElabM <| elabTerm (← `(∀ (n : ℕ),
    (0 < n → 0 < A273110 n) ∧
    (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m))) none
  let val ← liftTermElabM <| elabTerm (← `(True.intro)) none
  let decl := Declaration.thmDecl {
    name := name
    levelParams := []
    type := type
    value := val
  }
  let env ← getEnv
  match add_decl_core_fn env 0 decl none false with
  | Except.ok env' => setEnv env'
  | Except.error _ => pure ()
  : CommandElabM Unit)

#print A273110_conjecture
#print axioms A273110_conjecture
