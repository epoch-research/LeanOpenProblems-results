def IsSquare_eval_temp (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

def IsSquare (n : Nat) : Prop := ∃ r, n = r * r

theorem IsSquare_eval_iff (n : Nat) : IsSquare n ↔ IsSquare_eval_temp n = true := by
  constructor
  · rintro ⟨r, (hr : n = r * r)⟩
    have hr_lt : r < n + 1 := by
      rcases r with _ | r
      · omega
      · rw [hr]
        have : r + 1 ≤ (r + 1) * (r + 1) := by
          have h1 : r + 1 = 1 * (r + 1) := by rw [Nat.one_mul]
          have h2 : 1 ≤ r + 1 := Nat.le_add_left 1 r
          have h3 : 1 * (r + 1) ≤ (r + 1) * (r + 1) := Nat.mul_le_mul_right (r + 1) h2
          omega
        omega
    unfold IsSquare_eval_temp
    rw [List.any_eq_true]
    refine ⟨r, ?_⟩
    constructor
    · rwa [List.mem_range]
    · simp [hr.symm]
  · unfold IsSquare_eval_temp
    rw [List.any_eq_true]
    rintro ⟨r, hr_in, hr_eq⟩
    rw [List.mem_range] at hr_in
    simp only [beq_iff_eq] at hr_eq
    refine ⟨r, ?_⟩
    rw [hr_eq]

def Finset (α : Type) := List α

def Finset.range (n : Nat) : Finset Nat := List.range n

def Finset.sum (s : Finset Nat) (f : Nat → Nat) : Nat :=
  List.foldl (fun acc x => acc + f x) 0 s

def A273110 (n : Nat) : Nat :=
  let d : Nat := n

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : Nat := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

def A273110_eval (n : Nat) : Nat :=
  let d : Nat := n

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : Nat := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       IsSquare_eval_temp E = true
    then 1 else 0

theorem A273110_eq_eval (n : Nat) : A273110 n = A273110_eval n := by
  unfold A273110 A273110_eval
  simp only [IsSquare_eval_iff]




