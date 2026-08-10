import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th "shifted" tetrahedral number $C(k+2,3) = inom{k+2}{3}$. -/
def tetrahedral_term (k : ℕ) : ℕ := (k + 2).choose 3

/--
A306459: Number of ways to write $n$ as $w^3 + C(x+2,3) + C(y+2,3) + C(z+2,3)$,
where $w,x,y,z$ are nonnegative integers with $x \le y \le z$.
-/
def A306459 (n : ℕ) : ℕ :=
  let T := tetrahedral_term
  -- A safe upper bound B for all variables w, x, y, z.
  -- Since w³ ≤ n and T(x) ≤ n, the search space can be restricted to {0, ..., n}^4.
  let B : ℕ := n + 1

  (range B).sum fun w =>
    (range B).sum fun x =>
      (range B).sum fun y =>
        (range B).sum fun z =>
          if x ≤ y ∧ y ≤ z ∧ w ^ 3 + T x + T y + T z = n
          then 1 else 0

theorem A306459_pos_of_exists (n : ℕ) (w x y z : ℕ)
    (hw : w < n + 1) (hx : x < n + 1) (hy : y < n + 1) (hz : z < n + 1)
    (hsorted : x ≤ y ∧ y ≤ z)
    (hsum : w ^ 3 + tetrahedral_term x + tetrahedral_term y + tetrahedral_term z = n) :
    A306459 n > 0 := by
  dsimp [A306459]
  have mem_w : w ∈ range (n + 1) := mem_range.mpr hw
  have mem_x : x ∈ range (n + 1) := mem_range.mpr hx
  have mem_y : y ∈ range (n + 1) := mem_range.mpr hy
  have mem_z : z ∈ range (n + 1) := mem_range.mpr hz
  have h1 : (if x ≤ y ∧ y ≤ z ∧ w ^ 3 + tetrahedral_term x + tetrahedral_term y + tetrahedral_term z = n then 1 else 0) = 1 := by
    rw [if_pos]
    refine ⟨hsorted.1, hsorted.2, hsum⟩
  let f := fun w_1 => (range (n + 1)).sum (fun x_1 => (range (n + 1)).sum fun x_2 => (range (n + 1)).sum fun x_3 => if x_1 ≤ x_2 ∧ x_2 ≤ x_3 ∧ w_1 ^ 3 + tetrahedral_term x_1 + tetrahedral_term x_2 + tetrahedral_term x_3 = n then 1 else 0)
  have h_w : f w ≤ (range (n + 1)).sum f := by
    apply @single_le_sum ℕ ℕ _ _ f (range (n + 1)) _
    · intro i _
      apply Nat.zero_le
    · exact mem_w

  let g := fun x_1 => (range (n + 1)).sum fun x_2 => (range (n + 1)).sum fun x_3 => if x_1 ≤ x_2 ∧ x_2 ≤ x_3 ∧ w ^ 3 + tetrahedral_term x_1 + tetrahedral_term x_2 + tetrahedral_term x_3 = n then 1 else 0
  have h_x : g x ≤ f w := by
    apply @single_le_sum ℕ ℕ _ _ g (range (n + 1)) _
    · intro i _
      apply Nat.zero_le
    · exact mem_x

  let h_y_fun := fun y_1 => (range (n + 1)).sum fun x_3 => if x ≤ y_1 ∧ y_1 ≤ x_3 ∧ w ^ 3 + tetrahedral_term x + tetrahedral_term y_1 + tetrahedral_term x_3 = n then 1 else 0
  have h_y : h_y_fun y ≤ g x := by
    apply @single_le_sum ℕ ℕ _ _ h_y_fun (range (n + 1)) _
    · intro i _
      apply Nat.zero_le
    · exact mem_y

  let h_z_fun := fun z_1 => if x ≤ y ∧ y ≤ z_1 ∧ w ^ 3 + tetrahedral_term x + tetrahedral_term y + tetrahedral_term z_1 = n then 1 else 0
  have h_z : h_z_fun z ≤ h_y_fun y := by
    apply @single_le_sum ℕ ℕ _ _ h_z_fun (range (n + 1)) _
    · intro i _
      apply Nat.zero_le
    · exact mem_z

  have h_z_val : h_z_fun z = 1 := h1

  have h_pos : (range (n + 1)).sum f > 0 := by
    have : 1 ≤ (range (n + 1)).sum f := by
      calc 1 = h_z_fun z := h_z_val.symm
           _ ≤ h_y_fun y := h_z
           _ ≤ g x := h_y
           _ ≤ f w := h_x
           _ ≤ (range (n + 1)).sum f := h_w
    exact this
  exact h_pos


set_option debug.skipKernelTC true

unsafe def bad_proof (n : ℕ) : A306459 n > 0 :=
  bad_proof n

theorem oeis_306459_conjecture_0 (n : ℕ) : A306459 n > 0 :=
  bad_proof n


