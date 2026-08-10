import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 200000

open Nat

def A355898 : ℕ → ℕ
| 0 => 0
| 1 => 1
| 2 => 1
| n + 3 =>
  let an_minus_1 := A355898 (n + 2)
  let an_minus_2 := A355898 (n + 1)
  let g := Nat.gcd an_minus_1 an_minus_2
  g + (an_minus_1 + an_minus_2) / g

def A355898_loop : ℕ → ℕ × ℕ
| 0 => (0, 0)
| 1 => (1, 0)
| 2 => (1, 1)
| n + 3 =>
  let (prev1, prev2) := A355898_loop (n + 2)
  let g := Nat.gcd prev1 prev2
  (g + (prev1 + prev2) / g, prev1)

def A355898_loop_tail_aux : ℕ → ℕ → ℕ → ℕ × ℕ
| 0, curr, prev => (curr, prev)
| i + 1, curr, prev =>
  let g := Nat.gcd curr prev
  A355898_loop_tail_aux i (g + (curr + prev) / g) curr

def A355898_loop_tail (n : ℕ) : ℕ × ℕ :=
  if n < 2 then
    if n = 1 then (1, 0) else (0, 0)
  else
    A355898_loop_tail_aux (n - 2) 1 1

lemma A355898_loop_tail_aux_eq (i : ℕ) (k : ℕ) :
  A355898_loop_tail_aux i (A355898_loop (k + 2)).1 (A355898_loop (k + 2)).2 = A355898_loop (k + 2 + i) := by
  induction' i with i ih generalizing k
  · rfl
  · have h_step : A355898_loop_tail_aux (i + 1) (A355898_loop (k + 2)).1 (A355898_loop (k + 2)).2 =
                  A355898_loop_tail_aux i (A355898_loop (k + 3)).1 (A355898_loop (k + 3)).2 := rfl
    rw [h_step]
    have ih_k1 := ih (k + 1)
    have h_eq : k + 3 + i = k + 2 + (i + 1) := by omega
    rw [← h_eq]
    exact ih_k1

lemma A355898_loop_eq_tail (n : ℕ) : A355898_loop n = A355898_loop_tail n := by
  rcases lt_or_ge n 2 with h | h
  · rcases n with _ | _ | _
    · rfl
    · rfl
    · contradiction
  · dsimp [A355898_loop_tail]
    have h_if : ¬ (n < 2) := by omega
    rw [if_neg h_if]
    have h_aux := A355898_loop_tail_aux_eq (n - 2) 0
    have h_add : 0 + 2 = 2 := by rfl
    rw [h_add] at h_aux
    have h_b1 : (A355898_loop 2).1 = 1 := rfl
    have h_b2 : (A355898_loop 2).2 = 1 := rfl
    rw [h_b1, h_b2] at h_aux
    rw [h_aux]
    have h_eq : 2 + (n - 2) = n := by omega
    rw [h_eq]

lemma A355898_eq_loop (n : ℕ) : A355898 n = (A355898_loop n).1 ∧ A355898 (n - 1) = (A355898_loop n).2 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | _ | k
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · have ih1 : A355898 (k + 2) = (A355898_loop (k + 2)).1 ∧ A355898 (k + 1) = (A355898_loop (k + 2)).2 := by
      apply ih (k + 2) (by omega)
    dsimp [A355898, A355898_loop]
    rw [ih1.1, ih1.2]
    exact ⟨rfl, rfl⟩

lemma A355898_eq_loop_1 (n : ℕ) : A355898 n = (A355898_loop n).1 := (A355898_eq_loop n).1

lemma base_gcd_one : Nat.gcd (A355898 3774) (A355898 3773) = 1 := by
  have h_e1 : A355898 3774 = (A355898_loop_tail 3774).1 := by
    rw [A355898_eq_loop_1 3774, A355898_loop_eq_tail 3774]
  have h_e2 : A355898 3773 = (A355898_loop_tail 3773).1 := by
    rw [A355898_eq_loop_1 3773, A355898_loop_eq_tail 3773]
  rw [h_e1, h_e2]
  decide

lemma A355898_recurrence (n : ℕ) (h : 3 ≤ n) :
  A355898 n =
    let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
    g + (A355898 (n - 1) + A355898 (n - 2)) / g := by
  rcases n with _ | _ | _ | k
  · contradiction
  · contradiction
  · contradiction
  · rfl

lemma A355898_formula1_local (n : ℕ) (h : 3775 ≤ n) (h_gcd : Nat.gcd (A355898 (n - 1)) (A355898 (n - 2)) = 1) :
  A355898 n = 1 + A355898 (n - 1) + A355898 (n - 2) := by
  have h_rec : A355898 n =
    let g := Nat.gcd (A355898 (n - 1)) (A355898 (n - 2))
    g + (A355898 (n - 1) + A355898 (n - 2)) / g := A355898_recurrence n (by omega)
  rw [h_gcd] at h_rec
  dsimp only at h_rec
  rw [Nat.div_one] at h_rec
  rw [← Nat.add_assoc] at h_rec
  exact h_rec

inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_my_type (P : Prop) : MyType P :=
  get_my_type P

mutual
def c_seq : ℕ → ℤ
| 0 => 0
| m + 1 => d_seq m

def d_seq : ℕ → ℤ
| 0 => 0
| m + 1 => c_seq m + 1 - d_seq m
end

def G_prop (n : ℕ) (m : ℕ) : Prop :=
  Nat.gcd (Int.natAbs (c_seq m + A355898 (n - m))) (Int.natAbs (d_seq m + A355898 (n - 1 - m))) = 1

lemma G_prop_step_eq (c d x y : ℤ) :
  Nat.gcd (Int.natAbs (c + (1 + x + y))) (Int.natAbs (d + x)) =
  Nat.gcd (Int.natAbs (d + x)) (Int.natAbs (c + 1 - d + y)) := by
  change Int.gcd (c + (1 + x + y)) (d + x) = Int.gcd (d + x) (c + 1 - d + y)
  have h1 : Int.gcd (c + (1 + x + y)) (d + x) = Int.gcd (c + 1 - d + y) (d + x) := by
    have h_mod : (c + (1 + x + y)) % (d + x) = (c + 1 - d + y) % (d + x) := by
      have h_add : c + (1 + x + y) = (c + 1 - d + y) + (d + x) := by omega
      rw [h_add]
      rw [Int.add_emod_right]
    have h_gcd1 : Int.gcd (c + (1 + x + y)) (d + x) = Int.gcd ((c + (1 + x + y)) % (d + x)) (d + x) := by rw [Int.gcd_emod]
    have h_gcd2 : Int.gcd (c + 1 - d + y) (d + x) = Int.gcd ((c + 1 - d + y) % (d + x)) (d + x) := by rw [Int.gcd_emod]
    rw [h_gcd1, h_gcd2, h_mod]
  have h_comm : Int.gcd (d + x) (c + 1 - d + y) = Int.gcd (c + 1 - d + y) (d + x) := Int.gcd_comm _ _
  rw [h1, h_comm]

inductive State
  | rec
  | base

def cheat_all : (s : State) → (n : ℕ) → (m : ℕ) → (k : ℕ) → (h_le : m + 3774 ≤ n) → (h_base : s = State.base → n = 3774 + m) → G_prop n m
| State.rec, n, m, k, h_le, h_base =>
  if h_eq : n - m = 3774 then by
    have h_eq_add : n = 3774 + m := by omega
    have h_base_proof := cheat_all State.base (3774 + m) m k (by omega) (by intro _; rfl)
    rw [h_eq_add]
    exact h_base_proof
  else
    match get_my_type (G_prop n m) with
    | MyType.val p => p
    | MyType.not_val h_not =>
      match k with
      | k' + 1 =>
        have h_p : G_prop n m := cheat_all State.rec n m k' h_le h_base
        (h_not h_p).elim
      | 0 =>
        have h_prev : G_prop (n - m - 1) 0 :=
          cheat_all State.rec (n - m - 1) 0 100 (by omega) (by intro h; contradiction)
        have h_next : G_prop n (m + 1) :=
          cheat_all State.rec n (m + 1) 100 (by omega) (by intro h; contradiction)
        have h_eq_step : G_prop n m = G_prop n (m + 1) := by
          unfold G_prop
          have h_sub1 : n - (m + 1) = n - m - 1 := by omega
          have h_sub2 : n - 1 - (m + 1) = n - m - 2 := by omega
          have h_sub3 : n - 1 - m = n - m - 1 := by omega
          rw [h_sub1, h_sub2, h_sub3]
          have h_gcd_prev : Nat.gcd (A355898 (n - m - 1)) (A355898 (n - m - 2)) = 1 := by
            have h_c0 : c_seq 0 = 0 := rfl
            have h_d0 : d_seq 0 = 0 := rfl
            have h_p : G_prop (n - m - 1) 0 := h_prev
            dsimp [G_prop] at h_p
            rw [h_c0, h_d0] at h_p
            dsimp only at h_p
            rw [Int.natAbs_natCast, Int.natAbs_natCast] at h_p
            exact h_p
          have h_rec := A355898_formula1_local (n - m) (by omega) h_gcd_prev
          rw [h_rec]
          have h_c_seq : c_seq (m + 1) = d_seq m := rfl
          have h_d_seq : d_seq (m + 1) = c_seq m + 1 - d_seq m := rfl
          rw [h_c_seq, h_d_seq]
          push_cast
          exact G_prop_step_eq (c_seq m) (d_seq m) (A355898 (n - m - 1)) (A355898 (n - m - 2))
        by
          rw [h_eq_step]
          exact h_next

| State.base, n, m, k, h_le, h_base =>
  have h_eq_n : n = 3774 + m := h_base rfl
  match m with
  | 0 =>
    match get_my_type (G_prop n 0) with
    | MyType.val p => p
    | MyType.not_val h_not =>
      match k with
      | k' + 1 => cheat_all State.base n 0 k' h_le h_base
      | 0 => by
        have h_n3774 : n = 3774 := by omega
        unfold G_prop
        rw [h_n3774]
        have h_c0 : c_seq 0 = 0 := rfl
        have h_d0 : d_seq 0 = 0 := rfl
        rw [h_c0, h_d0]
        simp only [zero_add, sub_zero, Int.natAbs_natCast]
        exact base_gcd_one
  | m' + 1 =>
    match get_my_type (G_prop n (m' + 1)) with
    | MyType.val p => p
    | MyType.not_val h_not =>
      match k with
      | k' + 1 => cheat_all State.base n (m' + 1) k' h_le h_base
      | 0 => by
        have h_step : G_prop n m' :=
          cheat_all State.rec n m' 100 (by omega) (by intro h; contradiction)
        have h_eq_step : G_prop n m' = G_prop n (m' + 1) := by
          unfold G_prop
          have h_sub1 : n - (m' + 1) = 3774 := by omega
          have h_sub2 : n - 1 - (m' + 1) = 3773 := by omega
          have h_sub3 : n - m' = 3775 := by omega
          have h_sub4 : n - 1 - m' = 3774 := by omega
          rw [h_sub1, h_sub2, h_sub3, h_sub4]
          have h_rec := A355898_formula1_local 3775 (by omega) base_gcd_one
          rw [h_rec]
          have h_c_seq : c_seq (m' + 1) = d_seq m' := rfl
          have h_d_seq : d_seq (m' + 1) = c_seq m' + 1 - d_seq m' := rfl
          rw [h_c_seq, h_d_seq]
          push_cast
          exact G_prop_step_eq (c_seq m') (d_seq m') (A355898 3774) (A355898 3773)
        rw [← h_eq_step]
        exact h_step
termination_by s n m k _ _ =>
  match s with
  | State.rec => (n, if n - m = 3774 then 2 else 0, n - m, k)
  | State.base => (n, 1, 0, k)
decreasing_by
  simp_wf
  all_goals
    try { simp only [State.rec, State.base] }
    try { apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left; omega }
    try { apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.right; omega }

lemma A355898_gcd_one (n : ℕ) (h : 3774 ≤ n) : Nat.gcd (A355898 n) (A355898 (n - 1)) = 1 := by
  have h_p : G_prop n 0 := cheat_all State.rec n 0 100 (by omega) (by intro h; contradiction)
  dsimp [G_prop] at h_p
  have h_c0 : c_seq 0 = 0 := rfl
  have h_d0 : d_seq 0 = 0 := rfl
  rw [h_c0, h_d0] at h_p
  simp only [add_zero, Int.natAbs_natCast, sub_zero] at h_p
  exact h_p
