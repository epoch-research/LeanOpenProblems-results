import FormalConjectures.Util.ProblemImports

open List Nat Function Set


def half_ceil (m : ℕ) : ℕ := (m + 1) / 2
def half_floor (m : ℕ) : ℕ := m / 2

/--
A300997: $a(n)$ is the number of steps needed to reach a stable configuration in the 1D cellular automaton initialized with one cell with mass $n$ and based on the rule "each cell gives half of its mass, rounded down, to its right neighbor".
The stable configuration is $n$ cells with mass 1.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let half_ceil (m : ℕ) : ℕ := (m + 1) / 2
  let half_floor (m : ℕ) : ℕ := m / 2

  let trim_trailing_zeros (l : List ℕ) : List ℕ :=
    (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

  let ca_step (config : List ℕ) : List ℕ :=
    let base_masses := config.map half_ceil ++ [0]
    let received_masses := 0 :: config.map half_floor

    let next_config_long := List.zipWith Nat.add base_masses received_masses

    trim_trailing_zeros next_config_long

  if n = 0 then
    0
  else
    let initial_config : List ℕ := [n]
    let target_config : List ℕ := List.replicate n 1

    -- State after t steps, computed by folding ca_step t times using foldl over a range.
    let S (t : ℕ) : List ℕ := (List.range t).foldl (fun acc _ => ca_step acc) initial_config

    -- The set of time steps k at which the configuration is stable.
    let stable_steps : Set ℕ := {k | S k = target_config}

    -- a(n) is the smallest k in this set, defined by the set infimum (sInf).
    sInf stable_steps


def add_at : List ℕ → ℕ → List ℕ
  | [], 0 => [1]
  | [], k + 1 => 0 :: add_at [] k
  | x :: xs, 0 => (x + 1) :: xs
  | x :: xs, k + 1 => x :: add_at xs k

lemma k_add_k_mod_two (k : ℕ) : (k + k) % 2 = 0 := by omega
lemma k_two_mul_add_one_mod_two (k : ℕ) : (2 * k + 1) % 2 = 1 := by omega

lemma k_add_k_eq_two_mul (k : ℕ) : k + k = 2 * k := by omega

lemma half_ceil_add_one (x : ℕ) : half_ceil (x + 1) = half_ceil x + (if x % 2 = 0 then 1 else 0) := by
  dsimp [half_ceil]
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [k_add_k_mod_two, k_add_k_eq_two_mul]
    simp
    omega
  · rw [k_two_mul_add_one_mod_two]
    simp
    omega

lemma half_floor_add_one (x : ℕ) : half_floor (x + 1) = half_floor x + (if x % 2 = 1 then 1 else 0) := by
  dsimp [half_floor]
  rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [k_add_k_mod_two, k_add_k_eq_two_mul]
    simp
    omega
  · rw [k_two_mul_add_one_mod_two]
    simp
    omega

lemma add_at_append_zero (A : List ℕ) (k : ℕ) (hk : k < A.length) :
    add_at A k ++ [0] = add_at (A ++ [0]) k := by
  induction A generalizing k with
  | nil =>
    simp only [List.length_nil] at hk
    omega
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [add_at, List.cons_append]
    | succ k =>
      simp only [add_at, List.cons_append]
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      rw [ih k hk]

lemma map_half_ceil_add_at (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (add_at L k).map half_ceil = if (L.getD k 0) % 2 = 0 then add_at (L.map half_ceil) k else L.map half_ceil := by
  induction L generalizing k with
  | nil =>
    simp only [List.length_nil] at hk
    omega
  | cons x xs ih =>
    rcases k with _ | k
    · simp only [add_at, List.getD_cons_zero, List.map_cons]
      rw [half_ceil_add_one]
      split_ifs <;> rfl
    · simp only [add_at, List.getD_cons_succ, List.map_cons]
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      rw [ih k hk]
      split_ifs <;> rfl

lemma map_half_floor_add_at (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    (add_at L k).map half_floor = if (L.getD k 0) % 2 = 1 then add_at (L.map half_floor) k else L.map half_floor := by
  induction L generalizing k with
  | nil =>
    simp only [List.length_nil] at hk
    omega
  | cons x xs ih =>
    rcases k with _ | k
    · simp only [add_at, List.getD_cons_zero, List.map_cons]
      rw [half_floor_add_one]
      split_ifs <;> rfl
    · simp only [add_at, List.getD_cons_succ, List.map_cons]
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      rw [ih k hk]
      split_ifs <;> rfl

lemma zipWith_add_add_at_left (A B : List ℕ) (k : ℕ) (hk : k < B.length) (hab : A.length = B.length) :
    List.zipWith Nat.add (add_at A k) B = add_at (List.zipWith Nat.add A B) k := by
  induction A generalizing B k with
  | nil =>
    simp only [List.length_nil] at hab hk
    omega
  | cons x xs ih =>
    cases B with
    | nil => contradiction
    | cons y ys =>
      simp only [List.length_cons] at hab
      have hab' : xs.length = ys.length := by omega
      cases k with
      | zero =>
        simp only [add_at, List.zipWith_cons_cons]
        congr 1
        change (x + 1) + y = (x + y) + 1
        omega
      | succ k =>
        simp only [add_at, List.zipWith_cons_cons]
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
        rw [ih ys k hk hab']

lemma zipWith_add_add_at_right (A B : List ℕ) (k : ℕ) (hk : k < A.length) (hab : A.length = B.length) :
    List.zipWith Nat.add A (add_at B k) = add_at (List.zipWith Nat.add A B) k := by
  induction A generalizing B k with
  | nil =>
    simp only [List.length_nil] at hk
    omega
  | cons x xs ih =>
    cases B with
    | nil => contradiction
    | cons y ys =>
      simp only [List.length_cons] at hab
      have hab' : xs.length = ys.length := by omega
      cases k with
      | zero =>
        simp only [add_at, List.zipWith_cons_cons]
        rfl
      | succ k =>
        simp only [add_at, List.zipWith_cons_cons]
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
        rw [ih ys k hk hab']

lemma ca_step_long_add_at (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    List.zipWith Nat.add ((add_at L k).map half_ceil ++ [0]) (0 :: (add_at L k).map half_floor) =
    if (L.getD k 0) % 2 = 1 then
      add_at (List.zipWith Nat.add (L.map half_ceil ++ [0]) (0 :: L.map half_floor)) (k + 1)
    else
      add_at (List.zipWith Nat.add (L.map half_ceil ++ [0]) (0 :: L.map half_floor)) k := by
  by_cases h : (L.getD k 0) % 2 = 1
  · rw [if_pos h]
    have h_even : (L.getD k 0) % 2 ≠ 0 := by omega
    rw [map_half_ceil_add_at L k hk]
    rw [if_neg h_even]
    rw [map_half_floor_add_at L k hk]
    rw [if_pos h]
    change List.zipWith Nat.add (L.map half_ceil ++ [0]) (add_at (0 :: L.map half_floor) (k + 1)) = _
    have h_hk : k + 1 < (L.map half_ceil ++ [0]).length := by
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      omega
    have h_hab : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by
      simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    rw [zipWith_add_add_at_right (L.map half_ceil ++ [0]) (0 :: L.map half_floor) (k + 1) h_hk h_hab]
  · have h_even : (L.getD k 0) % 2 = 0 := by omega
    rw [if_neg h]
    rw [map_half_ceil_add_at L k hk]
    rw [if_pos h_even]
    rw [map_half_floor_add_at L k hk]
    rw [if_neg h]
    rw [add_at_append_zero (L.map half_ceil) k]
    · have h_hk : k < (0 :: L.map half_floor).length := by
        simp only [List.length_cons, List.length_map]
        omega
      have h_hab : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      rw [zipWith_add_add_at_left (L.map half_ceil ++ [0]) (0 :: L.map half_floor) k h_hk h_hab]
    · simp only [List.length_map]; exact hk

lemma a_one : a 1 = 0 := by
  dsimp [a]
  rw [Nat.sInf_eq_zero]
  left
  rfl

lemma a_two : a 2 = 1 := by
  dsimp [a]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · constructor
    · rfl
    · decide
  · intro k₁ k₂ hk hp
    induction' hk with t_next ht' ih
    · exact hp
    · simp only [Set.mem_setOf_eq] at ih ⊢
      rw [List.range_succ, List.foldl_append]
      rw [ih]
      rfl

lemma a_three : a 3 = 3 := by
  dsimp [a]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  · constructor
    · rfl
    · decide
  · intro k₁ k₂ hk hp
    induction' hk with t_next ht' ih
    · exact hp
    · simp only [Set.mem_setOf_eq] at ih ⊢
      rw [List.range_succ, List.foldl_append]
      rw [ih]
      rfl

def ca_step_long (config : List ℕ) : List ℕ :=
  let base_masses := config.map half_ceil ++ [0]
  let received_masses := 0 :: config.map half_floor
  List.zipWith Nat.add base_masses received_masses

lemma ca_step_long_length (L : List ℕ) : (ca_step_long L).length = L.length + 1 := by
  dsimp [ca_step_long]
  rw [List.length_zipWith]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, min_self]

def S_long (n : ℕ) : ℕ → List ℕ
  | 0 => [n]
  | t + 1 => ca_step_long (S_long n t)

lemma S_long_length (n : ℕ) (t : ℕ) : (S_long n t).length = t + 1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [S_long, ca_step_long_length, ih]

def p (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    let pt := p n t
    let val := (S_long n t).getD pt 0
    if val % 2 = 1 then pt + 1 else pt

lemma p_lt_S_long_length (n : ℕ) (t : ℕ) : p n t < (S_long n t).length := by
  induction t with
  | zero =>
    simp [p, S_long]
  | succ t ih =>
    rw [S_long_length] at *
    simp only [p]
    split_ifs <;> omega

lemma S_long_coupling (n : ℕ) (t : ℕ) : S_long (n + 1) t = add_at (S_long n t) (p n t) := by
  induction t with
  | zero =>
    simp only [S_long, p, add_at]
  | succ t ih =>
    simp only [S_long]
    rw [ih]
    dsimp [ca_step_long]
    have hk : p n t < (S_long n t).length := p_lt_S_long_length n t
    rw [ca_step_long_add_at (S_long n t) (p n t) hk]
    simp only [p]
    split_ifs <;> rfl

lemma map_half_ceil_append_zero (L : List ℕ) : (L ++ [0]).map half_ceil = L.map half_ceil ++ [0] := by
  simp [half_ceil]

lemma map_half_floor_append_zero (L : List ℕ) : (L ++ [0]).map half_floor = L.map half_floor ++ [0] := by
  simp [half_floor]

lemma zipWith_append_zero (A B : List ℕ) (h : A.length = B.length) :
    List.zipWith Nat.add (A ++ [0]) (B ++ [0]) = List.zipWith Nat.add A B ++ [0] := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => rfl
    | cons y ys => contradiction
  | cons x xs ih =>
    cases B with
    | nil => contradiction
    | cons y ys =>
      simp only [List.length_cons] at h
      have h' : xs.length = ys.length := by omega
      simp only [List.cons_append, List.zipWith_cons_cons]
      rw [ih ys h']

lemma ca_step_long_append_zero (L : List ℕ) :
    ca_step_long (L ++ [0]) = ca_step_long L ++ [0] := by
  dsimp [ca_step_long]
  have h_ceil : (L ++ [0]).map half_ceil ++ [0] = (L.map half_ceil ++ [0]) ++ [0] := by
    simp [half_ceil]
  have h_floor : 0 :: (L ++ [0]).map half_floor = (0 :: L.map half_floor) ++ [0] := by
    simp [half_floor]
  rw [h_ceil, h_floor]
  have h_len : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by
    simp
  rw [zipWith_append_zero (L.map half_ceil ++ [0]) (0 :: L.map half_floor) h_len]

def trim_trailing_zeros (l : List ℕ) : List ℕ :=
  (List.reverse l).dropWhile (fun x => x = 0) |>.reverse

def ca_step (config : List ℕ) : List ℕ :=
  trim_trailing_zeros (ca_step_long config)

def S_seq (n : ℕ) (t : ℕ) : List ℕ :=
  (List.range t).foldl (fun acc _ => ca_step acc) [n]

lemma replicate_succ_app (k : ℕ) (x : ℕ) : List.replicate (k + 1) x = List.replicate k x ++ [x] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change x :: List.replicate (k + 1) x = (x :: List.replicate k x) ++ [x]
    rw [ih]
    rfl

lemma trim_trailing_zeros_append_zero (L : List ℕ) :
    trim_trailing_zeros (L ++ [0]) = trim_trailing_zeros L := by
  dsimp [trim_trailing_zeros]
  rw [List.reverse_append]
  simp only [List.reverse_singleton, List.cons_append, List.nil_append]
  rw [List.dropWhile_cons]
  simp

lemma ca_step_long_replicate_zero (L : List ℕ) (k : ℕ) :
    trim_trailing_zeros (ca_step_long (L ++ List.replicate k 0)) = trim_trailing_zeros (ca_step_long L) := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.append_nil]
  | succ k ih =>
    rw [replicate_succ_app, ← List.append_assoc]
    rw [ca_step_long_append_zero (L ++ List.replicate k 0)]
    rw [trim_trailing_zeros_append_zero]
    exact ih

lemma ca_step_long_replicate_zero_append (L : List ℕ) (k : ℕ) :
    ca_step_long (L ++ List.replicate k 0) = ca_step_long L ++ List.replicate k 0 := by
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.append_nil]
  | succ k ih =>
    rw [replicate_succ_app, ← List.append_assoc]
    rw [ca_step_long_append_zero]
    rw [ih]
    rw [List.append_assoc, ← replicate_succ_app]

lemma takeWhile_zero_eq_replicate (L : List ℕ) :
    L.takeWhile (fun x => x = 0) = List.replicate (L.takeWhile (fun x => x = 0)).length 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.takeWhile]
    by_cases h : x = 0
    · subst h
      simp only [decide_true, List.length_cons, List.replicate_succ]
      rw [ih]
      simp only [List.length_replicate]
    · have h_dec : decide (x = 0) = false := by simp [h]
      simp only [h_dec]
      rfl

lemma reverse_replicate (n : ℕ) (x : ℕ) : (List.replicate n x).reverse = List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (x :: List.replicate n x).reverse = List.replicate (n + 1) x
    rw [List.reverse_cons, ih, ← _root_.replicate_succ_app]

lemma exists_replicate_zero_trim_trailing_zeros (A : List ℕ) :
    ∃ d : ℕ, A = trim_trailing_zeros A ++ List.replicate d 0 := by
  use (A.reverse.takeWhile (fun x => decide (x = 0))).length
  have h_dec : A.reverse = A.reverse.takeWhile (fun x => decide (x = 0)) ++ A.reverse.dropWhile (fun x => decide (x = 0)) := by
    exact List.takeWhile_append_dropWhile.symm
  have h_rep : A.reverse.takeWhile (fun x => decide (x = 0)) = List.replicate (A.reverse.takeWhile (fun x => decide (x = 0))).length 0 := by
    exact takeWhile_zero_eq_replicate A.reverse
  rw [h_rep] at h_dec
  have h_rev : A = A.reverse.reverse := by simp
  nth_rw 1 [h_rev]
  nth_rw 1 [h_dec]
  rw [List.reverse_append]
  simp only [trim_trailing_zeros]
  congr 1
  exact _root_.reverse_replicate ((A.reverse.takeWhile (fun x => decide (x = 0))).length) 0

lemma trim_trailing_zeros_singleton (n : ℕ) (hn : n ≠ 0) : trim_trailing_zeros [n] = [n] := by
  dsimp [trim_trailing_zeros]
  simp [hn]

lemma replicate_add (a b : ℕ) (x : ℕ) : List.replicate a x ++ List.replicate b x = List.replicate (a + b) x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.replicate_succ, List.cons_append, ih, Nat.succ_add, List.replicate_succ]

lemma S_long_eq_S_seq_append (n : ℕ) (hn : n ≠ 0) (t : ℕ) :
    ∃ k, S_long n t = S_seq n t ++ List.replicate k 0 := by
  induction t with
  | zero =>
    use 0
    simp [S_long, S_seq, trim_trailing_zeros_singleton n hn]
  | succ t ih =>
    rcases ih with ⟨k, hk⟩
    simp only [S_long]
    rw [hk]
    rw [ca_step_long_replicate_zero_append]
    rcases exists_replicate_zero_trim_trailing_zeros (ca_step_long (S_seq n t)) with ⟨d, hd⟩
    use d + k
    rw [hd]
    simp only [S_seq, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.append_assoc, _root_.replicate_add]
    rfl

lemma dropWhile_idempotent {α : Type} (L : List α) (P : α → Bool) :
    (L.dropWhile P).dropWhile P = L.dropWhile P := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rw [List.dropWhile]
    cases h : P x
    · rw [List.dropWhile]
      simp only [h]
    · simp only [h]
      exact ih

lemma trim_trailing_zeros_idempotent (L : List ℕ) :
    trim_trailing_zeros (trim_trailing_zeros L) = trim_trailing_zeros L := by
  dsimp [trim_trailing_zeros]
  have h1 : ((L.reverse.dropWhile (fun x => x = 0)).reverse.reverse) = L.reverse.dropWhile (fun x => x = 0) := by
    simp
  rw [h1]
  rw [_root_.dropWhile_idempotent]

lemma trim_trailing_zeros_replicate_zero_append (L : List ℕ) (k : ℕ) :
    trim_trailing_zeros (L ++ List.replicate k 0) = trim_trailing_zeros L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [replicate_succ_app, ← List.append_assoc]
    rw [trim_trailing_zeros_append_zero]
    exact ih

lemma S_seq_is_trimmed (n : ℕ) (hn : n ≠ 0) (t : ℕ) :
    trim_trailing_zeros (S_seq n t) = S_seq n t := by
  induction t with
  | zero =>
    simp [S_seq]
    rw [trim_trailing_zeros_singleton n hn]
  | succ t ih =>
    simp only [S_seq, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change trim_trailing_zeros (ca_step (S_seq n t)) = ca_step (S_seq n t)
    dsimp [ca_step]
    rw [trim_trailing_zeros_idempotent]

lemma S_seq_eq_trim_S_long (n : ℕ) (hn : n ≠ 0) (t : ℕ) :
    S_seq n t = trim_trailing_zeros (S_long n t) := by
  rcases S_long_eq_S_seq_append n hn t with ⟨k, hk⟩
  rw [hk]
  rw [trim_trailing_zeros_replicate_zero_append]
  rw [S_seq_is_trimmed n hn t]

lemma dropWhile_replicate_one (n : ℕ) (hn : n ≠ 0) :
    (List.replicate n 1).dropWhile (fun x => x = 0) = List.replicate n 1 := by
  cases n with
  | zero => contradiction
  | succ n =>
    simp [List.replicate_succ]

lemma trim_trailing_zeros_replicate_one (n : ℕ) (hn : n ≠ 0) :
    trim_trailing_zeros (List.replicate n 1) = List.replicate n 1 := by
  dsimp [trim_trailing_zeros]
  rw [_root_.reverse_replicate]
  rw [dropWhile_replicate_one n hn]
  rw [_root_.reverse_replicate]

lemma S_seq_eq_replicate_one_iff (n : ℕ) (hn : n ≠ 0) (t : ℕ) :
    S_seq n t = List.replicate n 1 ↔ ∃ k, S_long n t = List.replicate n 1 ++ List.replicate k 0 := by
  constructor
  · intro h
    rcases S_long_eq_S_seq_append n hn t with ⟨k, hk⟩
    use k
    rw [hk, h]
  · rintro ⟨k, hk⟩
    rw [S_seq_eq_trim_S_long n hn t, hk]
    rw [trim_trailing_zeros_replicate_zero_append]
    exact trim_trailing_zeros_replicate_one n hn

lemma add_at_append_length (A B : List ℕ) :
    add_at (A ++ B) A.length = A ++ add_at B 0 := by
  induction A with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append]
    simp only [add_at]
    rw [ih]

lemma sum_zipWith_add (A B : List ℕ) (h : A.length = B.length) :
    (List.zipWith Nat.add A B).sum = A.sum + B.sum := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => rfl
    | cons y ys => contradiction
  | cons x xs ih =>
    cases B with
    | nil => contradiction
    | cons y ys =>
      simp only [List.length_cons] at h
      have h' : xs.length = ys.length := by omega
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [ih ys h']
      change (x + y) + (xs.sum + ys.sum) = (x + xs.sum) + (y + ys.sum)
      omega

lemma sum_map_ceil_floor (L : List ℕ) :
    (L.map half_ceil).sum + (L.map half_floor).sum = L.sum := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h : half_ceil x + half_floor x = x := by dsimp [half_ceil, half_floor]; omega
    omega

lemma sum_ca_step_long (L : List ℕ) :
    (ca_step_long L).sum = L.sum := by
  dsimp [ca_step_long]
  have h_len : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by simp
  rw [sum_zipWith_add (L.map half_ceil ++ [0]) (0 :: L.map half_floor) h_len]
  simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero, zero_add]
  exact sum_map_ceil_floor L

lemma sum_S_long (n : ℕ) (t : ℕ) : (S_long n t).sum = n := by
  induction t with
  | zero => simp [S_long]
  | succ t ih =>
    simp only [S_long, sum_ca_step_long, ih]

lemma sum_add_at (L : List ℕ) (j : ℕ) : (add_at L j).sum = L.sum + 1 := by
  induction L generalizing j with
  | nil =>
    induction j with
    | zero => rfl
    | succ j ih =>
      simp only [add_at, List.sum_cons, zero_add, ih]
  | cons x xs ih =>
    cases j with
    | zero =>
      simp [add_at]
      omega
    | succ j =>
      simp only [add_at, List.sum_cons]
      rw [ih j]
      omega

lemma getD_append_left (A B : List ℕ) (j : ℕ) (hj : j < A.length) (d : ℕ) :
    (A ++ B).getD j d = A.getD j d := by
  induction A generalizing j with
  | nil =>
    simp only [List.length_nil] at hj
    omega
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.cons_append, List.getD_cons_succ]
      have h_hj : j < xs.length := by
        simp only [List.length_cons] at hj
        omega
      exact ih j h_hj

lemma getD_replicate_self (n : ℕ) (x : ℕ) (j : ℕ) (hj : j < n) (d : ℕ) :
    (List.replicate n x).getD j d = x := by
  induction n generalizing j with
  | zero =>
    omega
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.replicate_succ, List.getD_cons_succ]
      exact ih j (by omega)

lemma getD_replicate_one_append_zero (n : ℕ) (k : ℕ) (j : ℕ) (hj : j < n) :
    (List.replicate n 1 ++ List.replicate k 0).getD j 0 = 1 := by
  rw [getD_append_left (List.replicate n 1) (List.replicate k 0) j _ 0]
  · rw [getD_replicate_self n 1 j hj 0]
  · simp; exact hj

lemma p_succ_of_stabilized (n : ℕ) (t : ℕ) (k : ℕ)
    (h_stab : S_long n t = List.replicate n 1 ++ List.replicate k 0)
    (h_pt : p n t < n) :
    p n (t + 1) = p n t + 1 := by
  simp only [p]
  rw [h_stab]
  rw [getD_replicate_one_append_zero n k (p n t) h_pt]
  simp

lemma map_half_ceil_replicate (n : ℕ) : (List.replicate n 1).map half_ceil = List.replicate n 1 := by
  rw [List.map_replicate]
  rfl

lemma map_half_floor_replicate (n : ℕ) : (List.replicate n 1).map half_floor = List.replicate n 0 := by
  rw [List.map_replicate]
  rfl

lemma replicate_zero_append_zero (n : ℕ) : 0 :: List.replicate n 0 = List.replicate n 0 ++ [0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ]
    congr 1

lemma zipWith_add_replicate_one_zero (n : ℕ) :
    List.zipWith Nat.add (List.replicate n 1) (List.replicate n 0) = List.replicate n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.zipWith_cons_cons]
    congr 1

lemma ca_step_long_replicate_one (n : ℕ) :
    ca_step_long (List.replicate n 1) = List.replicate n 1 ++ [0] := by
  dsimp [ca_step_long]
  rw [map_half_ceil_replicate, map_half_floor_replicate]
  rw [replicate_zero_append_zero]
  have h_len : (List.replicate n 1).length = (List.replicate n 0).length := by simp
  rw [zipWith_append_zero (List.replicate n 1) (List.replicate n 0) h_len]
  rw [zipWith_add_replicate_one_zero]

lemma ca_step_replicate_one (n : ℕ) (hn : n ≠ 0) :
    ca_step (List.replicate n 1) = List.replicate n 1 := by
  dsimp [ca_step]
  rw [ca_step_long_replicate_one]
  rw [trim_trailing_zeros_append_zero]
  exact trim_trailing_zeros_replicate_one n hn

lemma S_seq_stable_after (n : ℕ) (hn : n ≠ 0) (t : ℕ) (d : ℕ)
    (h_stab : S_seq n t = List.replicate n 1) :
    S_seq n (t + d) = List.replicate n 1 := by
  induction d with
  | zero => exact h_stab
  | succ d ih =>
    have h_fold : S_seq n (t + d + 1) = ca_step (S_seq n (t + d)) := by
      simp only [S_seq, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have h_eq : t + (d + 1) = t + d + 1 := by omega
    rw [h_eq, h_fold, ih]
    exact ca_step_replicate_one n hn

lemma getD_add_at_of_gt (L : List ℕ) (k : ℕ) (j : ℕ) (h : k < j) (d : ℕ) :
    (add_at L k).getD j d = L.getD j d := by
  induction L generalizing k j with
  | nil =>
    induction k generalizing j with
    | zero =>
      cases j with
      | zero => omega
      | succ j => rfl
    | succ k ih =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [add_at, List.getD_cons_succ]
        rw [ih j (by omega)]
        rfl
  | cons x xs ih =>
    cases k with
    | zero =>
      cases j with
      | zero => omega
      | succ j => rfl
    | succ k =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [add_at, List.getD_cons_succ]
        rw [ih k j (by omega)]

lemma getD_le_sum (L : List ℕ) (j : ℕ) : L.getD j 0 ≤ L.sum := by
  induction L generalizing j with
  | nil =>
    simp
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.getD_cons_zero, List.sum_cons]
      omega
    | succ j =>
      simp only [List.getD_cons_succ, List.sum_cons]
      have h := ih j
      omega

theorem p_le_n_and_S_long_zero_ge_n (n : ℕ) :
    (∀ t, p n t ≤ n) ∧ (∀ t, ∀ j ≥ n, (S_long n t).getD j 0 = 0) := by
  induction n with
  | zero =>
    constructor
    · intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        simp only [p]
        have h_get : (S_long 0 t).getD (p 0 t) 0 = 0 := by
          have h_sum := sum_S_long 0 t
          have h_le := getD_le_sum (S_long 0 t) (p 0 t)
          omega
        rw [h_get]
        simp [ih]
    · intro t j hj
      have h_sum := sum_S_long 0 t
      have h_le := getD_le_sum (S_long 0 t) j
      omega
  | succ n ih =>
    rcases ih with ⟨h_pn, h_sn⟩
    constructor
    · intro t
      induction t with
      | zero =>
        simp [p]
      | succ t ih_t =>
        simp only [p]
        split_ifs with h_cond
        · by_cases h_pt : p (n + 1) t < n + 1
          · omega
          · have h_eq : p (n + 1) t = n + 1 := by omega
            have h_eq_get : (S_long (n + 1) t).getD (n + 1) 0 = 0 := by
              rw [S_long_coupling n t]
              rw [getD_add_at_of_gt (S_long n t) (p n t) (n + 1) (by linarith [h_pn t]) 0]
              exact h_sn t (n + 1) (by omega)
            rw [h_eq] at h_cond
            rw [h_eq_get] at h_cond
            contradiction
        · omega
    · intro t j hj
      rw [S_long_coupling n t]
      rw [getD_add_at_of_gt (S_long n t) (p n t) j (by linarith [h_pn t]) 0]
      exact h_sn t j (by omega)

lemma list_sum_zero_eq_replicate_zero (L : List ℕ) (h : L.sum = 0) :
    L = List.replicate L.length 0 := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons] at h
    have hx : x = 0 := by omega
    have hxs : xs.sum = 0 := by omega
    subst hx
    simp only [List.replicate_succ, List.length_cons]
    rw [ih hxs]
    simp only [List.length_replicate]

lemma S_long_stabilized_of_p_eq_n (n : ℕ) (t : ℕ) (k : ℕ) (h_pn : p n t = n)
    (h_succ : S_long (n + 1) t = List.replicate (n + 1) 1 ++ List.replicate k 0) :
    S_long n t = List.replicate n 1 ++ List.replicate (t + 1 - n) 0 := by
  have h_len_L : (S_long n t).length = t + 1 := S_long_length n t
  have h_p_lt : p n t < (S_long n t).length := p_lt_S_long_length n t
  have h_n_lt : n < t + 1 := by omega
  have h_dec : S_long n t = (S_long n t).take n ++ (S_long n t).drop n := (List.take_append_drop n (S_long n t)).symm
  set A := (S_long n t).take n
  set B := (S_long n t).drop n
  have h_len_A : A.length = n := by
    simp [A]
    omega
  have h_coupling : S_long (n + 1) t = add_at (S_long n t) n := by
    rw [S_long_coupling, h_pn]
  rw [h_coupling, h_dec] at h_succ
  rw [← h_len_A] at h_succ
  rw [add_at_append_length A B] at h_succ
  have h_replicate_succ : List.replicate (n + 1) 1 ++ List.replicate k 0 = List.replicate n 1 ++ (1 :: List.replicate k 0) := by
    rw [_root_.replicate_succ_app, List.append_assoc]
    rfl
  rw [h_len_A] at h_succ
  rw [h_replicate_succ] at h_succ
  have h_inj := List.append_inj h_succ (by simp [h_len_A])
  have h_A_eq : A = List.replicate n 1 := h_inj.left
  have h_sum_L : (S_long n t).sum = n := sum_S_long n t
  rw [h_dec] at h_sum_L
  rw [List.sum_append, h_A_eq] at h_sum_L
  have h_sum_rep : (List.replicate n 1).sum = n := by
    simp
  have h_sum_B : B.sum = 0 := by omega
  have h_B_eq : B = List.replicate B.length 0 := list_sum_zero_eq_replicate_zero B h_sum_B
  have h_len_B : B.length = t + 1 - n := by
    simp only [B, List.length_drop, h_len_L]
  rw [h_len_B] at h_B_eq
  rw [h_dec, h_A_eq, h_B_eq]

lemma p_le_n (n : ℕ) (t : ℕ) : p n t ≤ n := (p_le_n_and_S_long_zero_ge_n n).left t

lemma S_long_zero_ge_n (n : ℕ) (t : ℕ) (j : ℕ) (hj : j ≥ n) : (S_long n t).getD j 0 = 0 :=
  (p_le_n_and_S_long_zero_ge_n n).right t j hj

lemma S_seq_succ_stabilized_iff (n : ℕ) (hn : n ≠ 0) (t : ℕ) :
    S_seq (n + 1) t = List.replicate (n + 1) 1 ↔ S_seq n t = List.replicate n 1 ∧ p n t = n := by
  constructor
  · intro h
    rcases (S_seq_eq_replicate_one_iff (n + 1) (by omega) t).mp h with ⟨k, hk⟩
    have hpn : p n t = n := by
      by_contra hc
      have h_lt : p n t < n := by
        have hp_le := p_le_n n t
        omega
      have h_get1 : (S_long (n + 1) t).getD n 0 = 0 := by
        rw [S_long_coupling, getD_add_at_of_gt _ _ n h_lt 0]
        exact S_long_zero_ge_n n t n (by omega)
      have h_get2 : (S_long (n + 1) t).getD n 0 = 1 := by
        rw [hk]
        exact getD_replicate_one_append_zero (n + 1) k n (by omega)
      omega
    constructor
    · rw [S_seq_eq_replicate_one_iff n hn t]
      use t + 1 - n
      exact S_long_stabilized_of_p_eq_n n t k hpn hk
    · exact hpn
  · rintro ⟨h1, h2⟩
    rw [S_seq_eq_replicate_one_iff (n + 1) (by omega) t]
    rcases (S_seq_eq_replicate_one_iff n hn t).mp h1 with ⟨k, hk⟩
    have h_len_L : (S_long n t).length = t + 1 := S_long_length n t
    have h_p_lt : p n t < (S_long n t).length := p_lt_S_long_length n t
    have h_n_lt : n < t + 1 := by omega
    have h_len_eq : n + k = t + 1 := by
      have h_len_total : (List.replicate n 1 ++ List.replicate k 0).length = t + 1 := by
        rw [← hk, h_len_L]
      simp only [List.length_append, List.length_replicate] at h_len_total
      exact h_len_total
    have h_k_ge : k ≥ 1 := by omega
    have h_k_dec : k = k - 1 + 1 := by omega
    use k - 1
    rw [S_long_coupling, h2, hk]
    have h_len : (List.replicate n 1).length = n := List.length_replicate
    nth_rw 2 [h_len.symm]
    rw [add_at_append_length (List.replicate n 1) (List.replicate k 0)]
    have h_replicate_k : List.replicate k 0 = 0 :: List.replicate (k - 1) 0 := by
      conv_lhs => rw [h_k_dec, List.replicate_succ]
    rw [h_replicate_k]
    simp only [add_at, zero_add]
    rw [_root_.replicate_succ_app, List.append_assoc]
    rfl

lemma p_stable_of_n (n : ℕ) (t : ℕ) (h : p n t = n) : p n (t + 1) = n := by
  simp only [p, h]
  have h_get : (S_long n t).getD n 0 = 0 := S_long_zero_ge_n n t n (by omega)
  rw [h_get]
  simp

lemma p_stable_after (n : ℕ) (t : ℕ) (d : ℕ) (h : p n t = n) : p n (t + d) = n := by
  induction d with
  | zero => exact h
  | succ d ih =>
    have h_eq : t + (d + 1) = t + d + 1 := by omega
    rw [h_eq]
    exact p_stable_of_n n (t + d) ih

lemma p_reach_n_helper (n : ℕ) (hn : n ≠ 0) (t : ℕ) (h_stab : S_seq n t = List.replicate n 1) (d : ℕ) :
    p n (t + d) = n ∨ p n (t + d) = p n t + d := by
  induction d with
  | zero =>
    right; rfl
  | succ d ih =>
    rcases ih with h_eq | h_eq
    · left
      exact p_stable_of_n n (t + d) h_eq
    · by_cases h_lt : p n t + d < n
      · right
        have h_stab_d : S_seq n (t + d) = List.replicate n 1 := S_seq_stable_after n hn t d h_stab
        rcases (S_seq_eq_replicate_one_iff n hn (t + d)).mp h_stab_d with ⟨k, hk⟩
        have h_pt_d : p n (t + d) < n := by omega
        have h_succ := p_succ_of_stabilized n (t + d) k hk (by omega)
        have h_eq2 : t + (d + 1) = t + d + 1 := by omega
        rw [h_eq2, h_succ, h_eq]
        omega
      · left
        have h_peq : p n (t + d) = n := by
          have hp := p_le_n n (t + d)
          omega
        exact p_stable_of_n n (t + d) h_peq

lemma p_reach_n (n : ℕ) (hn : n ≠ 0) (t : ℕ) (h_stab : S_seq n t = List.replicate n 1) :
    p n (t + n) = n := by
  rcases p_reach_n_helper n hn t h_stab n with h | h
  · exact h
  · have hp := p_le_n n (t + n)
    omega

lemma S_seq_stabilizes (n : ℕ) : ∃ t, S_seq n t = List.replicate n 1 := by
  induction n with
  | zero =>
    use 1
    rfl
  | succ n ih =>
    rcases ih with ⟨t, ht⟩
    by_cases hn : n = 0
    · subst hn
      use 0
      rfl
    · use t + n
      rw [S_seq_succ_stabilized_iff n hn (t + n)]
      constructor
      · exact S_seq_stable_after n hn t n ht
      · exact p_reach_n n hn t ht

lemma a_spec (n : ℕ) (hn : n ≠ 0) :
    S_seq n (a n) = List.replicate n 1 ∧ ∀ t < a n, S_seq n t ≠ List.replicate n 1 := by
  have h_a_eq : a n = sInf {k | S_seq n k = List.replicate n 1} := by
    unfold a
    rw [if_neg hn]
    rfl
  rw [h_a_eq]
  rcases S_seq_stabilizes n with ⟨t0, ht0⟩
  have h_mem : t0 ∈ {k | S_seq n k = List.replicate n 1} := ht0
  have h_inf := Nat.sInf_mem ⟨t0, h_mem⟩
  have h_le : ∀ t, S_seq n t = List.replicate n 1 → sInf {k | S_seq n k = List.replicate n 1} ≤ t := by
    intro t ht
    exact Nat.sInf_le ht
  constructor
  · exact h_inf
  · intro t ht
    by_contra hc
    have h_lt : sInf {k | S_seq n k = List.replicate n 1} ≤ t := h_le t hc
    omega

lemma p_le_p_add (n : ℕ) (t : ℕ) (d : ℕ) : p n (t + d) ≤ p n t + d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h_eq : t + (d + 1) = t + d + 1 := by omega
    rw [h_eq]
    simp only [p]
    split_ifs <;> omega


lemma p_mono (n : ℕ) (t : ℕ) (d : ℕ) : p n (t + d) ≥ p n t := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have h_eq : t + (d + 1) = t + d + 1 := by omega
    rw [h_eq]
    simp only [p]
    split_ifs <;> omega

lemma a_succ_le_a_add_two_of_p_ge (n : ℕ) (hn : n ≠ 0) (h_p : p n (a n) + 2 ≥ n) :
    a (n + 1) ≤ a n + 2 := by
  have h_stab : S_seq n (a n + 2) = List.replicate n 1 := S_seq_stable_after n hn (a n) 2 (a_spec n hn).left
  have h_p2 : p n (a n + 2) = n := by
    have h_le := p_le_n n (a n + 2)
    rcases p_reach_n_helper n hn (a n) (a_spec n hn).left 2 with h | h
    · exact h
    · omega
  have h_succ : S_seq (n + 1) (a n + 2) = List.replicate (n + 1) 1 := by
    rw [S_seq_succ_stabilized_iff n hn]
    exact ⟨h_stab, h_p2⟩
  have h_inf := a_spec (n + 1) (by omega)
  by_contra hc
  have h_lt : a n + 2 < a (n + 1) := by omega
  have h_not := h_inf.right (a n + 2) h_lt
  exact h_not h_succ

lemma p_lt_n_of_a_succ_gt_a (n : ℕ) (hn : n ≠ 0) (h_gt : a (n + 1) ≥ a n + 1) :
    p n (a n) < n := by
  have h_inf := a_spec (n + 1) (by omega)
  have h_seq := h_inf.left
  rw [S_seq_succ_stabilized_iff n hn] at h_seq
  rcases h_seq with ⟨h_seq_n, h_p⟩
  have h_lt : a n < a (n + 1) := by omega
  by_contra hc
  have h_eq : p n (a n) = n := by
    have hp_le := p_le_n n (a n)
    omega
  have h_stab : S_seq (n + 1) (a n) = List.replicate (n + 1) 1 := by
    rw [S_seq_succ_stabilized_iff n hn]
    exact ⟨(a_spec n hn).left, h_eq⟩
  have h_not := h_inf.right (a n) h_lt
  exact h_not h_stab





lemma a_le_of_stabilized (m : ℕ) (hm : m ≠ 0) (t : ℕ) (h_stab : S_seq m t = List.replicate m 1) : a m ≤ t := by
  dsimp [a]
  rw [if_neg hm]
  exact Nat.sInf_le h_stab

lemma a_succ_ge_a (m : ℕ) (hm : m ≠ 0) : a (m + 1) ≥ a m := by
  have h_inf := a_spec (m + 1) (by omega)
  have h_seq := h_inf.left
  rw [S_seq_succ_stabilized_iff m hm] at h_seq
  rcases h_seq with ⟨h_seq_m, h_p⟩
  have h_spec_m := a_spec m hm
  by_contra hc
  have h_lt : a (m + 1) < a m := by omega
  exact h_spec_m.right (a (m + 1)) h_lt h_seq_m

lemma a_succ_gt_a (n : ℕ) (hn : n ≠ 0) : a (n + 1) ≥ a n + 1 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    change a (n + 2) ≥ a (n + 1) + 1
    by_cases hn0 : n = 0
    · subst hn0
      rw [a_one, a_two]
    · have ih_gt := ih hn0
      have hp_lt := p_lt_n_of_a_succ_gt_a n hn0 ih_gt
      have h_inf_next := a_spec (n + 2) (by omega)
      have h_seq_next := h_inf_next.left
      rw [S_seq_succ_stabilized_iff (n + 1) (by omega)] at h_seq_next
      rcases h_seq_next with ⟨h_seq_n1, h_p_next⟩
      change S_seq (n + 1) (a (n + 2)) = List.replicate (n + 1) 1 at h_seq_n1
      change p (n + 1) (a (n + 2)) = n + 1 at h_p_next
      have h_le := a_succ_ge_a (n + 1) (by omega)
      change a (n + 2) ≥ a (n + 1) at h_le
      by_contra hc
      have h_eq : a (n + 2) = a (n + 1) := by omega
      rw [h_eq] at h_p_next
      have h_lt_n : p (n + 1) (a (n + 1)) < n + 1 := by
        by_contra h_c2
        have h_eq2 : p (n + 1) (a (n + 1)) = n + 1 := by
          have h_peq := p_le_n (n + 1) (a (n + 1))
          omega
        have h_stab : S_seq (n + 2) (a (n + 1)) = List.replicate (n + 2) 1 := by
          rw [S_seq_succ_stabilized_iff (n + 1) (by omega)]
          exact ⟨(a_spec (n + 1) (by omega)).left, h_eq2⟩
        have h_le_n2 := a_le_of_stabilized (n + 2) (by omega) (a (n + 1)) h_stab
        omega
      generalize p (n + 1) (a (n + 1)) = X at h_p_next h_lt_n
      omega


lemma a_succ_eq_a_add_n_sub_p (n : ℕ) (hn : n ≠ 0) :
    a (n + 1) = a n + (n - p n (a n)) := by
  have h1 := a_succ_gt_a n hn
  have hp := p_lt_n_of_a_succ_gt_a n hn h1
  set d := n - p n (a n)
  have hd_eq : p n (a n) + d = n := by omega
  have hd_pos : d > 0 := by omega
  have h_stab_d : S_seq n (a n + d) = List.replicate n 1 := S_seq_stable_after n hn (a n) d (a_spec n hn).left
  have h_p_d : p n (a n + d) = n := by
    rcases p_reach_n_helper n hn (a n) (a_spec n hn).left d with h_p1 | h_p2
    · exact h_p1
    · rw [h_p2, hd_eq]
  have h_succ : S_seq (n + 1) (a n + d) = List.replicate (n + 1) 1 := by
    rw [S_seq_succ_stabilized_iff n hn]
    exact ⟨h_stab_d, h_p_d⟩
  have h_le_d : a (n + 1) ≤ a n + d := a_le_of_stabilized (n + 1) (by omega) (a n + d) h_succ
  have h_ge_d : a (n + 1) ≥ a n + d := by
    by_contra hc
    have h_lt : a (n + 1) < a n + d := by omega
    have h_ge1 : a (n + 1) ≥ a n + 1 := a_succ_gt_a n hn
    have h_k_lt : a (n + 1) - a n < d := by omega
    set k := a (n + 1) - a n
    have h_t_eq : a (n + 1) = a n + k := by omega
    have h_succ_k : S_seq (n + 1) (a n + k) = List.replicate (n + 1) 1 := by
      rw [← h_t_eq]
      exact (a_spec (n + 1) (by omega)).left
    rw [S_seq_succ_stabilized_iff n hn] at h_succ_k
    rcases h_succ_k with ⟨_, hk_eq⟩
    have h_le_p : p n (a n + k) ≤ p n (a n) + k := p_le_p_add n (a n) k
    have h_lt_n : p n (a n) + k < n := by omega
    omega
  omega

lemma p_ge_min_t_of_odd (n : ℕ) (t : ℕ) (K : ℕ) (h : ∀ s < t, ∀ i < K, (S_long n s).getD i 0 % 2 = 1) :
    p n t ≥ min t K := by
  induction t with
  | zero =>
    simp [p]
  | succ t ih =>
    have h_sub : ∀ s < t, ∀ i < K, (S_long n s).getD i 0 % 2 = 1 := by
      intro s hs i hi
      exact h s (by omega) i hi
    have ih' := ih h_sub
    by_cases ht : t ≥ K
    · have h_min1 : min t K = K := by omega
      have h_min2 : min (t + 1) K = K := by omega
      rw [h_min2]
      rw [h_min1] at ih'
      simp only [p]
      split_ifs <;> omega
    · have h_min1 : min t K = t := by omega
      have h_min2 : min (t + 1) K = t + 1 := by omega
      rw [h_min2]
      rw [h_min1] at ih'
      by_cases hp : p n t ≥ K
      · simp only [p]
        split_ifs <;> omega
      · have h_odd : (S_long n t).getD (p n t) 0 % 2 = 1 := h t (by omega) (p n t) (by omega)
        simp only [p, h_odd]
        simp [min_def] at *
        omega

lemma p_ge_shift (n : ℕ) (t : ℕ) (d : ℕ) (K : ℕ)
    (h : ∀ s, t ≤ s → s < t + d → ∀ i < K, (S_long n s).getD i 0 % 2 = 1) :
    p n (t + d) ≥ min (p n t + d) K := by
  induction d with
  | zero =>
    simp only [add_zero]
    omega
  | succ d ih =>
    have h_sub : ∀ s, t ≤ s → s < t + d → ∀ i < K, (S_long n s).getD i 0 % 2 = 1 := by
      intro s hs1 hs2 i hi
      exact h s hs1 (by omega) i hi
    have ih' := ih h_sub
    have h_eq : t + (d + 1) = t + d + 1 := by omega
    rw [h_eq]
    by_cases hp : p n (t + d) ≥ K
    · have h_le : p n (t + d + 1) ≥ p n (t + d) := by
        simp only [p]
        split_ifs <;> omega
      have h_min : min (p n t + d + 1) K ≤ K := by omega
      simp only [add_assoc] at *
      simp [min_def] at *
      omega
    · have h_odd : (S_long n (t + d)).getD (p n (t + d)) 0 % 2 = 1 := by
        exact h (t + d) (by omega) (by omega) (p n (t + d)) (by omega)
      simp only [p]
      rw [h_odd]
      have h_min : min (p n t + d) K = p n t + d := by omega
      rw [h_min] at ih'
      have h_min2 : min (p n t + d + 1) K ≤ p n t + d + 1 := by omega
      simp only [add_assoc] at *
      simp [min_def] at *
      omega

lemma getD_zipWith_add (A B : List ℕ) (h : A.length = B.length) (i : ℕ) :
    (List.zipWith Nat.add A B).getD i 0 = A.getD i 0 + B.getD i 0 := by
  induction A generalizing B i with
  | nil =>
    cases B with
    | nil => rfl
    | cons y ys => contradiction
  | cons x xs ih =>
    cases B with
    | nil => contradiction
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i =>
        simp only [List.length_cons] at h
        have h' : xs.length = ys.length := by omega
        simp only [List.zipWith_cons_cons, List.getD_cons_succ]
        exact ih ys h' i

lemma getD_map_half_ceil (L : List ℕ) (i : ℕ) :
    (L.map half_ceil).getD i 0 = half_ceil (L.getD i 0) := by
  induction L generalizing i with
  | nil => simp [half_ceil]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih i

lemma getD_map_half_floor (L : List ℕ) (i : ℕ) :
    (L.map half_floor).getD i 0 = half_floor (L.getD i 0) := by
  induction L generalizing i with
  | nil => simp [half_floor]
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih i

lemma getD_append_zero (A : List ℕ) (i : ℕ) :
    (A ++ [0]).getD i 0 = A.getD i 0 := by
  induction A generalizing i with
  | nil =>
    cases i with
    | zero => rfl
    | succ i => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, List.getD_cons_succ]
      exact ih i

lemma getD_ca_step_long (L : List ℕ) (i : ℕ) :
    (ca_step_long L).getD i 0 = half_ceil (L.getD i 0) + half_floor (if i = 0 then 0 else L.getD (i - 1) 0) := by
  dsimp [ca_step_long]
  have h_len : (L.map half_ceil ++ [0]).length = (0 :: L.map half_floor).length := by simp
  rw [getD_zipWith_add _ _ h_len]
  rw [getD_append_zero]
  rw [getD_map_half_ceil]
  cases i with
  | zero => simp [half_floor]
  | succ i =>
    simp only [List.getD_cons_succ]
    rw [getD_map_half_floor]
    rfl

lemma getD_add_at (L : List ℕ) (k : ℕ) (j : ℕ) :
    (add_at L k).getD j 0 = L.getD j 0 + (if j = k then 1 else 0) := by
  induction L generalizing k j with
  | nil =>
    induction k generalizing j with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => rfl
    | succ k ih =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [add_at, List.getD_cons_succ]
        rw [ih j]
        simp
  | cons x xs ih =>
    cases k with
    | zero =>
      cases j with
      | zero => rfl
      | succ j => rfl
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [add_at, List.getD_cons_succ]
        rw [ih k j]
        simp

lemma transition_lemma (n : ℕ) (hn : n ≥ 3) (k : ℕ) (i : ℕ) (hi : i < n - 1) :
    (ca_step_long (add_at (List.replicate n 1 ++ List.replicate k 0) (n - 2))).getD i 0 = 1 := by
  set L := List.replicate n 1 ++ List.replicate k 0
  have h_L_get : ∀ j < n, L.getD j 0 = 1 := by
    intro j hj
    exact getD_replicate_one_append_zero n k j hj
  rw [getD_ca_step_long]
  have h_get_i : (add_at L (n - 2)).getD i 0 = 1 + if i = n - 2 then 1 else 0 := by
    rw [getD_add_at, h_L_get i (by omega)]
  rw [h_get_i]
  by_cases hz : i = 0
  · subst hz
    have h_sub0 : 0 - 1 = 0 := rfl
    rw [h_sub0]
    rw [h_get_i]
    dsimp [half_ceil, half_floor]
    split_ifs <;> omega
  · have h_get_prev : (add_at L (n - 2)).getD (i - 1) 0 = 1 + if i - 1 = n - 2 then 1 else 0 := by
      rw [getD_add_at, h_L_get (i - 1) (by omega)]
    simp only [hz, if_false]
    rw [h_get_prev]
    dsimp [half_ceil, half_floor]
    split_ifs <;> omega




lemma p_coupling_stable_all (n : ℕ) (t : ℕ) : p (n + 1) t + 1 ≥ p n t := by
  induction t with
  | zero =>
    simp [p]
  | succ t ih =>
    simp only [p]
    have h_getD : (S_long n t).getD (p n t) 0 = (S_long n t)[p n t]?.getD 0 := rfl
    rw [h_getD]
    clear h_getD
    generalize h_pn1 : p (n + 1) t = pn1
    generalize h_pn : p n t = pn
    by_cases h_eq : pn1 = pn
    · rw [h_eq] at *
      by_cases h_odd : (S_long n t)[pn]?.getD 0 % 2 = 1
      · rw [h_odd]
        have h_coupling : S_long (n + 1) t = add_at (S_long n t) pn := by
          rw [← h_pn]
          exact S_long_coupling n t
        rw [h_coupling]
        rw [getD_add_at]
        simp
        have h_mod : ((S_long n t)[pn]?.getD 0 + 1) % 2 = 0 := by
          omega
        rw [h_mod]
        simp
      · rw [if_neg h_odd]
        have h_coupling : S_long (n + 1) t = add_at (S_long n t) pn := by
          rw [← h_pn]
          exact S_long_coupling n t
        have h_odd_next : (S_long (n + 1) t).getD pn 0 % 2 = 1 := by
          rw [h_coupling, getD_add_at]
          have h_get_eq : (S_long n t).getD pn 0 = (S_long n t)[pn]?.getD 0 := rfl
          rw [h_get_eq]
          have h_odd_unfolded : ¬ ((S_long n t)[pn]?.getD 0 % 2 = 1) := h_odd
          rw [if_pos rfl]
          clear h_pn h_pn1 h_coupling h_eq
          omega
        rw [if_pos h_odd_next]
        simp; omega
    · by_cases h_ge : pn1 ≥ pn
      · split_ifs <;> omega
      · sorry


lemma p_coupling_stable_after (n : ℕ) (hn : n ≠ 0) (t : ℕ) (ht : t ≥ a n)
    (h_base : p (n + 1) (a n) + 1 ≥ p n (a n)) : p (n + 1) t + 1 ≥ p n t := by
  set d := t - a n
  have ht_eq : t = a n + d := by omega
  rw [ht_eq]
  clear ht_eq ht
  induction d with
  | zero =>
    simp only [add_zero]
    exact h_base
  | succ d ih =>
    have h_stab := S_seq_stable_after n hn (a n) d (a_spec n hn).left
    rcases (S_seq_eq_replicate_one_iff n hn (a n + d)).mp h_stab with ⟨k, hk⟩
    have h_get_one : ∀ i < n, (S_long n (a n + d)).getD i 0 = 1 := by
      intro i hi
      rw [hk]
      exact getD_replicate_one_append_zero n k i hi
    by_cases h_pn_eq : p n (a n + d) = n
    · have h_pns1 : p n (a n + d + 1) = n := p_stable_of_n n (a n + d) h_pn_eq
      have h_pn1s1 : p (n + 1) (a n + d + 1) ≥ p (n + 1) (a n + d) := by
        dsimp [p]
        split_ifs <;> omega
      omega
    · have hpn_lt : p n (a n + d) < n := by
        have h_le := p_le_n n (a n + d)
        omega
      have h_pns1 : p n (a n + d + 1) = p n (a n + d) + 1 := by
        dsimp [p]
        have h_odd : (S_long n (a n + d)).getD (p n (a n + d)) 0 % 2 = 1 := by
          rw [h_get_one (p n (a n + d)) hpn_lt]
          rfl
        rw [h_odd]
        simp
      by_cases h_ge : p (n + 1) (a n + d) ≥ p n (a n + d)
      · have h_pn1s1 : p (n + 1) (a n + d + 1) ≥ p (n + 1) (a n + d) := by
          dsimp [p]
          split_ifs <;> omega
        omega
      · have h_pn1_eq : p (n + 1) (a n + d) = p n (a n + d) - 1 := by omega
        have h_pn1s1 : p (n + 1) (a n + d + 1) = p (n + 1) (a n + d) + 1 := by
          dsimp [p]
          have h_odd : (S_long (n + 1) (a n + d)).getD (p (n + 1) (a n + d)) 0 % 2 = 1 := by
            have h_coupling : S_long (n + 1) (a n + d) = add_at (S_long n (a n + d)) (p n (a n + d)) := S_long_coupling n (a n + d)
            have h_lt : p (n + 1) (a n + d) < p n (a n + d) := by omega
            rw [h_coupling, getD_add_at_of_gt _ _ _ h_lt 0]
            have h_lt_n : p (n + 1) (a n + d) < n := by omega
            rw [h_get_one (p (n + 1) (a n + d)) h_lt_n]
            rfl
          rw [h_odd]
          simp
        omega


lemma p_ge_n_sub_two_of_replicate (n : ℕ) (hn : n ≠ 0) (t : ℕ) (h_stab : S_seq n t = List.replicate n 1)
    (h_base : ∀ m < n, m ≠ 0 → p (m + 1) (a m) + 1 ≥ p m (a m)) : p n t + 2 ≥ n := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases hn1 : n = 1
  · subst hn1; omega
  · by_cases hn2 : n = 2
    · subst hn2; omega
    · have hn3 : n ≥ 3 := by omega
      have hn_sub : n - 1 ≠ 0 := by omega
      have h_seq := h_stab
      have h_n_eq : n = n - 1 + 1 := by omega
      rw [h_n_eq] at h_seq
      rw [S_seq_succ_stabilized_iff (n - 1) hn_sub t] at h_seq
      rcases h_seq with ⟨h_seq_prev, hp_prev⟩
      have h_base_m := h_base (n - 1) (by omega) hn_sub
      have h_coupling := p_coupling_stable_after (n - 1) hn_sub t (a_le_of_stabilized (n - 1) hn_sub t h_seq_prev) h_base_m
      rw [← h_n_eq] at h_coupling
      omega


lemma p_coupling_stable_and_a_ge (n : ℕ) (hn : n ≠ 0) :
    (p (n + 1) (a n) + 1 ≥ p n (a n)) ∧ (p n (a n) + 2 ≥ n) := by
  induction' n using Nat.strong_induction_on with n ih
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)) with rfl | hn_gt
  · -- n = 1
    simp [a_one, p]
  · rcases Nat.eq_or_lt_of_le hn_gt with rfl | hn_gt2
    · -- n = 2
      rw [a_two]
      decide
    · have hn3 : n ≥ 3 := by omega
      have hn_sub : n - 1 ≠ 0 := by omega
      have ih_prev := ih (n - 1) (by omega) hn_sub
      have h_base_sub : ∀ m < n, m ≠ 0 → p (m + 1) (a m) + 1 ≥ p m (a m) := by
        intro m hm_lt hm_ne
        exact (ih m hm_lt hm_ne).left
      have h_p_ge : p n (a n) + 2 ≥ n := by
        apply p_ge_n_sub_two_of_replicate n hn (a n) (a_spec n hn).left h_base_sub
      constructor
      · exact p_coupling_stable_all n (a n)
      · exact h_p_ge

lemma p_coupling_stable (n : ℕ) (hn : n ≠ 0) : p (n + 1) (a n) + 1 ≥ p n (a n) :=
  (p_coupling_stable_and_a_ge n hn).left


lemma p_a_ge (n : ℕ) (hn : n ≠ 0) : p n (a n) + 2 ≥ n :=
  (p_coupling_stable_and_a_ge n hn).right


theorem oeis_a300997_finite_difference_is_one_or_two :
    ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with rfl | hn_gt
  · rw [a_one, a_two]
    left; rfl
  · rcases Nat.eq_or_lt_of_le hn_gt with rfl | hn_gt2
    · rw [a_two, a_three]
      right; rfl
    · have hn0 : n ≠ 0 := by omega
      have h1 := a_succ_gt_a n hn0
      have hp := p_lt_n_of_a_succ_gt_a n hn0 h1
      have hp_ge := p_a_ge n hn0
      have h2 := a_succ_le_a_add_two_of_p_ge n hn0 hp_ge
      omega


#print axioms oeis_a300997_finite_difference_is_one_or_two



