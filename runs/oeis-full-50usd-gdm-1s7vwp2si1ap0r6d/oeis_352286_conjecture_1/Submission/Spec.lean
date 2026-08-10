import FormalConjectures.Util.ProblemImports

-- A test comment
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

open BigOperators Finset Nat

def check_x (n : ℕ) (y : ℕ) (z : ℕ) (x : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let val := x^2 + 2 * y^2 + 3 * z^2 + x * y * z
    if val > n then false
    else if val == n || val + 1 == n then true
    else check_x n y z (x + 1) fuel'

def check_y (n : ℕ) (z : ℕ) (y : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if 3 * z^2 + 2 * y^2 > n then false
    else if check_x n y z 0 (n + 1) then true
    else check_y n z (y + 1) fuel'

def check_z (n : ℕ) (z : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if check_y n z 0 (n + 1) then true
    else check_z n (z + 1) fuel'

theorem check_x_correct (n y z : ℕ) (x_start : ℕ) (fuel : ℕ) :
  check_x n y z x_start fuel = false →
  ∀ x, x_start ≤ x → x - x_start < fuel →
  x^2 + 2 * y^2 + 3 * z^2 + x * y * z ≠ n ∧ x^2 + 2 * y^2 + 3 * z^2 + x * y * z + 1 ≠ n := by
  induction fuel generalizing x_start with
  | zero =>
    intro h x hx hf
    omega
  | succ fuel' ih =>
    intro h x hx hf
    dsimp [check_x] at h
    split at h
    · rename_i hg
      have : x^2 + 2 * y^2 + 3 * z^2 + x * y * z ≥ x_start^2 + 2 * y^2 + 3 * z^2 + x_start * y * z := by
        have hsq : x_start^2 ≤ x^2 := Nat.pow_le_pow_left hx 2
        have hmul : x_start * y * z ≤ x * y * z := by gcongr
        omega
      omega
    · split at h
      · contradiction
      · by_cases h_eq : x = x_start
        · subst h_eq
          rename_i h_cond
          simp [decide_eq_true_iff] at h_cond
          omega
        · have hx_next : x_start + 1 ≤ x := by omega
          have hf_next : x - (x_start + 1) < fuel' := by omega
          exact ih (x_start + 1) h x hx_next hf_next

theorem check_y_correct (n z : ℕ) (y_start : ℕ) (fuel : ℕ) :
  check_y n z y_start fuel = false →
  ∀ y, y_start ≤ y → y - y_start < fuel →
  ∀ x < n + 1,
  x^2 + 2 * y^2 + 3 * z^2 + x * y * z ≠ n ∧ x^2 + 2 * y^2 + 3 * z^2 + x * y * z + 1 ≠ n := by
  induction fuel generalizing y_start with
  | zero =>
    intro h y hy hf x hx
    omega
  | succ fuel' ih =>
    intro h y hy hf x hx
    dsimp [check_y] at h
    split at h
    · have : 3 * z^2 + 2 * y^2 > n := by
        have h_y_mono : y_start^2 ≤ y^2 := Nat.pow_le_pow_left hy 2
        omega
      omega
    · rename_i h_bound
      split at h
      · contradiction
      · rename_i h_x
        by_cases h_eq : y = y_start
        · subst h_eq
          have h_x_false : check_x n y z 0 (n + 1) = false := by
            cases h_cx : check_x n y z 0 (n + 1) with
            | true => contradiction
            | false => rfl
          have h_x_check := check_x_correct n y z 0 (n + 1) h_x_false x (by omega) hx
          exact h_x_check
        · have hy_next : y_start + 1 ≤ y := by omega
          have hf_next : y - (y_start + 1) < fuel' := by omega
          exact ih (y_start + 1) h y hy_next hf_next x hx

theorem check_z_correct (n : ℕ) (z_start : ℕ) (fuel : ℕ) :
  check_z n z_start fuel = false →
  ∀ z, z_start ≤ z → z - z_start < fuel →
  ∀ y < n + 1, ∀ x < n + 1,
  x^2 + 2 * y^2 + 3 * z^2 + x * y * z ≠ n ∧ x^2 + 2 * y^2 + 3 * z^2 + x * y * z + 1 ≠ n := by
  induction fuel generalizing z_start with
  | zero =>
    intro h z hz hf y hy x hx
    omega
  | succ fuel' ih =>
    intro h z hz hf y hy x hx
    dsimp [check_z] at h
    split at h
    · contradiction
    · rename_i h_y
      by_cases h_eq : z = z_start
      · subst h_eq
        have h_y_false : check_y n z 0 (n + 1) = false := by
          cases h_cy : check_y n z 0 (n + 1) with
          | true => contradiction
          | false => rfl
        have h_y_check := check_y_correct n z 0 (n + 1) h_y_false y (by omega) (by omega) x hx
        exact h_y_check
      · have hz_next : z_start + 1 ≤ z := by omega
        have hf_next : z - (z_start + 1) < fuel' := by omega
        exact ih (z_start + 1) h z hz_next hf_next y hy x hx

def A352286 (n : ℕ) : ℕ :=
  let B : Finset ℕ := range (n + 1)
  (range 2).sum (fun w =>
    B.sum (fun x =>
      B.sum (fun y =>
        B.sum (fun z =>
          if n = w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z then 1 else 0))))

theorem A352286_eq_zero_iff (n : ℕ) :
  A352286 n = 0 ↔ ∀ w ∈ range 2, ∀ x ∈ range (n + 1), ∀ y ∈ range (n + 1), ∀ z ∈ range (n + 1),
    w + x^2 + 2 * y^2 + 3 * z^2 + x * y * z ≠ n := by
  simp [A352286, sum_eq_zero_iff, ne_comm]

theorem A352286_zero_of_check_z_zero (n : ℕ) (h_check : check_z n 0 (n + 1) = false) :
  A352286 n = 0 := by
  rw [A352286_eq_zero_iff]
  intro w hw x hx y hy z hz
  simp only [Finset.mem_range] at *
  have hz_ge : 0 ≤ z := Nat.zero_le z
  have hz_lt : z - 0 < n + 1 := by omega
  have h_z_check := check_z_correct n 0 (n + 1) h_check z hz_ge hz_lt y hy x hx
  rcases h_z_check with ⟨h_x0, h_x1⟩
  interval_cases w
  · omega
  · omega

def A352286_exceptions : Set ℕ := {106, 744, 5469, 331269}

theorem check_z_106 : check_z 106 0 107 = false := by decide
theorem check_z_744 : check_z 744 0 745 = false := by decide
theorem check_z_5469 : check_z 5469 0 5470 = false := by decide

theorem check_z_add (n : ℕ) (z : ℕ) (a b : ℕ) :
  check_z n z (a + b) = (check_z n z a || check_z n (z + a) b) := by
  induction a generalizing z with
  | zero => simp [check_z]
  | succ a' ih =>
    have h1 : a' + 1 + b = (a' + b) + 1 := by omega
    rw [h1, check_z, ih (z + 1)]
    have h2 : check_z n z (a' + 1) = (if check_y n z 0 (n + 1) then true else check_z n (z + 1) a') := rfl
    rw [h2]
    have h3 : z + 1 + a' = z + (a' + 1) := by omega
    rw [h3]
    split <;> simp

theorem check_y_false_of_z_ge (n z y : ℕ) (fuel : ℕ) (hz : 3 * z^2 > n) :
  check_y n z y fuel = false := by
  induction fuel generalizing y with
  | zero => rfl
  | succ fuel' ih =>
    dsimp [check_y]
    split
    · rfl
    · rename_i h_bound
      omega

theorem check_z_false_of_z_ge (n z : ℕ) (fuel : ℕ) (hz : 3 * z^2 > n) :
  check_z n z fuel = false := by
  induction fuel generalizing z with
  | zero => rfl
  | succ fuel' ih =>
    dsimp [check_z]
    rw [check_y_false_of_z_ge n z 0 (n + 1) hz]
    dsimp
    have hz_next : 3 * (z + 1)^2 > n := by
      have : z^2 ≤ (z + 1)^2 := by
        have : z ≤ z + 1 := by omega
        gcongr
      omega
    exact ih (z + 1) hz_next

theorem check_z_331269_0 : check_z 331269 0 3 = false := by decide
theorem check_z_331269_1 : check_z 331269 3 5 = false := by decide
theorem check_z_331269_2 : check_z 331269 8 7 = false := by decide
theorem check_z_331269_3 : check_z 331269 15 11 = false := by decide
theorem check_z_331269_4 : check_z 331269 26 15 = false := by decide
theorem check_z_331269_5 : check_z 331269 41 21 = false := by decide
theorem check_z_331269_6 : check_z 331269 62 29 = false := by decide
theorem check_z_331269_7 : check_z 331269 91 41 = false := by decide
theorem check_z_331269_8 : check_z 331269 132 63 = false := by decide
theorem check_z_331269_9 : check_z 331269 195 138 = false := by decide

theorem check_z_331269_all : check_z 331269 0 333 = false := by
  rw [check_z_add 331269 0 3 330, check_z_331269_0]
  dsimp
  rw [check_z_add 331269 3 5 325, check_z_331269_1]
  dsimp
  rw [check_z_add 331269 8 7 318, check_z_331269_2]
  dsimp
  rw [check_z_add 331269 15 11 307, check_z_331269_3]
  dsimp
  rw [check_z_add 331269 26 15 292, check_z_331269_4]
  dsimp
  rw [check_z_add 331269 41 21 271, check_z_331269_5]
  dsimp
  rw [check_z_add 331269 62 29 242, check_z_331269_6]
  dsimp
  rw [check_z_add 331269 91 41 201, check_z_331269_7]
  dsimp
  rw [check_z_add 331269 132 63 138, check_z_331269_8]
  dsimp
  exact check_z_331269_9

theorem check_z_331269_complete : check_z 331269 0 331270 = false := by
  rw [check_z_add 331269 0 333 330937, check_z_331269_all]
  dsimp
  have hz : 3 * 333^2 > 331269 := by decide
  exact check_z_false_of_z_ge 331269 333 330937 hz

theorem oeis_352286_conjecture_1 :
  ∀ n : ℕ, (A352286 n = 0 ↔ n ∈ A352286_exceptions) := by
  intro n
  constructor
  · intro h
    sorry
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact A352286_zero_of_check_z_zero 106 check_z_106
    · exact A352286_zero_of_check_z_zero 744 check_z_744
    · exact A352286_zero_of_check_z_zero 5469 check_z_5469
    · exact A352286_zero_of_check_z_zero 331269 check_z_331269_complete
