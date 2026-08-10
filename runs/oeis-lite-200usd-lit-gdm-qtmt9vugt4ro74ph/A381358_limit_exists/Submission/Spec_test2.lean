import FormalConjectures.Util.ProblemImports
open List Nat

/-- Computes the run lengths of a list of natural numbers. -/
private def run_lengths_nat : List ℕ → List ℕ
  | [] => []
  | l@(h :: _) =>
    let run_prefix := l.takeWhile (fun x => decide (x = h))
    let rest := l.drop run_prefix.length
    run_prefix.length :: run_lengths_nat rest
termination_by l => l.length

/--
A381587 $T_n$: The $n$-th row of the irregular triangle, following the recurrence:
$T_1=[1], T_2=[1], T_3=[2]$. For $n \ge 4$, $T_n = \text{Runs}(\text{Reverse}(T_{n-1})) \frown T_{n-1}$.
$n$ is 1-indexed here.
-/
private def A381587_T : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1]
  | 3 => [2]
  | k + 4 => -- Covers indices >= 4. Recurses on k+3, which is n-1.
    let prev_T := A381587_T (k + 3)
    run_lengths_nat prev_T.reverse ++ prev_T

/--
A381358: Row sums of irregular triangle A381587.
Row $n$ elements are $T_n$. The sequence $a(n)$ is the list sum of $T_n$.
-/
def A381358 (n : ℕ) : ℕ :=
  (A381587_T n).sum

lemma length_takeWhile_le (p : α → Bool) (l : List α) : (takeWhile p l).length ≤ l.length := by
  have h_sum := takeWhile_append_dropWhile (p := p) (l := l)
  have h_len : (takeWhile p l).length + (dropWhile p l).length = l.length := by
    rw [← length_append, h_sum]
  omega

lemma run_lengths_nat_sum (l : List ℕ) : (run_lengths_nat l).sum = l.length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    rfl
  | case2 h tail run_prefix rest ih =>
    unfold run_lengths_nat
    change run_prefix.length + (run_lengths_nat rest).sum = (h :: tail).length
    rw [ih]
    have h_le : run_prefix.length ≤ (h :: tail).length := by
      exact length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
    rw [length_drop, Nat.add_sub_of_le h_le]

lemma A381587_T_sum_pos (n : ℕ) : n ≠ 0 → 1 ≤ (A381587_T n).sum := by
  induction n with
  | zero =>
    intro h
    exact (h rfl).elim
  | succ n ih =>
    intro _
    rcases n with _ | _ | _ | k
    · -- n = 0, so n + 1 = 1
      decide
    · -- n = 1, so n + 1 = 2
      decide
    · -- n = 2, so n + 1 = 3
      decide
    · -- n = k + 3, so n + 1 = k + 4
      dsimp [A381587_T]
      rw [List.sum_append]
      have h_ih : 1 ≤ (A381587_T (k + 3)).sum := by
        apply ih
        exact succ_ne_zero _
      omega

lemma run_lengths_nat_length_le (l : List ℕ) : (run_lengths_nat l).length ≤ l.length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    rfl
  | case2 h tail run_prefix rest ih =>
    unfold run_lengths_nat
    simp only [length_cons] at *
    have h_prefix_len : 1 ≤ run_prefix.length := by
      change 1 ≤ (takeWhile (fun x => decide (x = h)) (h :: tail)).length
      simp [takeWhile]
    have h_le : run_prefix.length ≤ (h :: tail).length := by
      exact length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
    have h_drop_len : rest.length = (h :: tail).length - run_prefix.length := length_drop (i := run_prefix.length) (l := h :: tail)
    have h_combined := ih.trans_eq h_drop_len
    dsimp only [rest, run_prefix] at *
    simp only [length_cons] at *
    generalize h_P : (takeWhile (fun x => decide (x = h)) (h :: tail)).length = P at *
    omega


lemma takeWhile_append_of_length_lt {α : Type*} (p : α → Bool) (l1 l2 : List α)
    (h : (takeWhile p l1).length < l1.length) :
    takeWhile p (l1 ++ l2) = takeWhile p l1 := by
  induction l1 with
  | nil =>
    simp at h
  | cons h' tail ih =>
    rw [cons_append]
    simp only [takeWhile_cons]
    split_ifs with hp
    · rw [takeWhile_cons] at h
      rw [hp] at h
      simp only [if_true, length_cons, add_lt_add_iff_right] at h
      rw [ih h]
    · rfl

lemma run_lengths_nat_nonempty {l : List ℕ} (h : l ≠ []) : (run_lengths_nat l).length ≥ 1 := by
  rcases l with - | ⟨hd, tl⟩
  · exact (h rfl).elim
  · unfold run_lengths_nat
    simp

lemma run_lengths_nat_length_mono (l1 l2 : List ℕ) :
    (run_lengths_nat l1).length ≤ (run_lengths_nat (l1 ++ l2)).length := by
  induction l1 using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    have h_nonempty : (h :: tail) ++ l2 ≠ [] := by simp
    have h_ge1 : (run_lengths_nat ((h :: tail) ++ l2)).length ≥ 1 := run_lengths_nat_nonempty h_nonempty
    by_cases h_lt : run_prefix.length < (h :: tail).length
    · have h_eq_prefix : ((h :: tail) ++ l2).takeWhile (fun x => decide (x = h)) = run_prefix := by
        exact takeWhile_append_of_length_lt (fun x => decide (x = h)) (h :: tail) l2 h_lt
      have h_eq_drop : ((h :: tail) ++ l2).drop run_prefix.length = rest ++ l2 := by
        rw [List.drop_append_of_le_length (le_of_lt h_lt)]
      have h_unfold_rhs : run_lengths_nat ((h :: tail) ++ l2) = run_prefix.length :: run_lengths_nat (rest ++ l2) := by
        change run_lengths_nat (h :: (tail ++ l2)) = _
        unfold run_lengths_nat
        dsimp only
        rw [← cons_append]
        rw [h_eq_prefix]
        rw [h_eq_drop]
        congr 1
        rw [run_lengths_nat.eq_def]
      rw [run_lengths_nat.eq_def (h :: tail)]
      rw [h_unfold_rhs]
      simp only [length_cons, add_le_add_iff_right]
      exact ih
    · have h_eq : run_prefix.length = (h :: tail).length := by
        have : run_prefix.length ≤ (h :: tail).length := length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
        omega
      have h_rest_empty : rest = [] := by
        change (h :: tail).drop run_prefix.length = []
        rw [h_eq, List.drop_length]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      change (run_prefix.length :: run_lengths_nat rest).length ≤ _
      rw [h_rest_empty]
      rw [run_lengths_nat.eq_def []]
      simp only [length_cons, length_nil]
      omega

lemma run_lengths_nat_prepend_mono (h_param : ℕ) (l : List ℕ) :
    (run_lengths_nat l).length ≤ (run_lengths_nat (h_param :: l)).length := by
  induction l using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    by_cases h_eq : h_param = h
    · rw [h_eq]
      have h_unfold_left : run_lengths_nat (h :: tail) = run_prefix.length :: run_lengths_nat rest := by
        rw [run_lengths_nat.eq_def (h :: tail)]
      have h_unfold_right : run_lengths_nat (h :: h :: tail) = (1 + run_prefix.length) :: run_lengths_nat rest := by
        rw [run_lengths_nat.eq_def (h :: h :: tail)]
        simp [takeWhile, run_prefix, rest]
        omega
      rw [h_unfold_left, h_unfold_right]
      simp only [length_cons]
      omega
    · have h_unfold_right : run_lengths_nat (h_param :: h :: tail) = 1 :: run_lengths_nat (h :: tail) := by
        rw [run_lengths_nat.eq_def (h_param :: h :: tail)]
        dsimp only
        have h_neq : h ≠ h_param := by omega
        simp [takeWhile, h_neq]
      rw [h_unfold_right]
      simp only [length_cons]
      omega

lemma run_lengths_nat_length_mono_left (l1 l2 : List ℕ) :
    (run_lengths_nat l2).length ≤ (run_lengths_nat (l1 ++ l2)).length := by
  induction l1 with
  | nil =>
    simp
  | cons hd tl ih =>
    simp only [cons_append]
    have ih_prep := run_lengths_nat_prepend_mono hd (tl ++ l2)
    omega

lemma run_lengths_nat_append_le (l1 l2 : List ℕ) :
    (run_lengths_nat l1).length + (run_lengths_nat l2).length ≤ (run_lengths_nat (l1 ++ l2)).length + 1 := by
  induction l1 using run_lengths_nat.induct with
  | case1 =>
    unfold run_lengths_nat
    simp
  | case2 h tail run_prefix rest ih =>
    by_cases h_lt : run_prefix.length < (h :: tail).length
    · have h_eq_prefix : ((h :: tail) ++ l2).takeWhile (fun x => decide (x = h)) = run_prefix := by
        exact takeWhile_append_of_length_lt (fun x => decide (x = h)) (h :: tail) l2 h_lt
      have h_eq_drop : ((h :: tail) ++ l2).drop run_prefix.length = rest ++ l2 := by
        rw [List.drop_append_of_le_length (le_of_lt h_lt)]
      have h_unfold_rhs : run_lengths_nat ((h :: tail) ++ l2) = run_prefix.length :: run_lengths_nat (rest ++ l2) := by
        change run_lengths_nat (h :: (tail ++ l2)) = _
        unfold run_lengths_nat
        dsimp only
        rw [← cons_append]
        rw [h_eq_prefix]
        rw [h_eq_drop]
        congr 1
        rw [run_lengths_nat.eq_def]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      change (run_prefix.length :: run_lengths_nat rest).length + _ ≤ _
      rw [h_unfold_rhs]
      simp only [length_cons]
      have ih' : (run_lengths_nat rest).length + (run_lengths_nat l2).length ≤ (run_lengths_nat (rest ++ l2)).length + 1 := ih
      omega
    · have h_eq : run_prefix.length = (h :: tail).length := by
        have : run_prefix.length ≤ (h :: tail).length := length_takeWhile_le (fun x => decide (x = h)) (h :: tail)
        omega
      have h_rest_empty : rest = [] := by
        change (h :: tail).drop run_prefix.length = []
        rw [h_eq, List.drop_length]
      rw [run_lengths_nat.eq_def (h :: tail)]
      dsimp only
      change (run_prefix.length :: run_lengths_nat rest).length + _ ≤ _
      rw [h_rest_empty]
      rw [run_lengths_nat.eq_def []]
      simp only [length_cons, length_nil]
      have h_mono := run_lengths_nat_length_mono_left (h :: tail) l2
      omega

noncomputable def u (n : ℕ) : ℝ :=
  if n = 0 then 0 else - Real.log (A381358 n : ℝ)

lemma u_subadditive (h_super : ∀ n m, A381358 (n + m) ≥ A381358 n * A381358 m) :
    Subadditive u := by
  intro m n
  by_cases hm : m = 0
  · subst hm; simp [u]
  · by_cases hn : n = 0
    · subst hn; simp [u]
    · have hmn : m + n ≠ 0 := by omega
      unfold u
      split_ifs
      have h1 : (A381358 m : ℝ) ≥ 1 := by
        have := A381587_T_sum_pos m hm
        exact (Nat.one_le_cast (α := ℝ)).mpr this
      have h2 : (A381358 n : ℝ) ≥ 1 := by
        have := A381587_T_sum_pos n hn
        exact (Nat.one_le_cast (α := ℝ)).mpr this
      have h_super_mn := h_super m n
      have h_super_cast : (A381358 (m + n) : ℝ) ≥ (A381358 m : ℝ) * (A381358 n : ℝ) := by
        have h_cast_le : (A381358 m * A381358 n : ℝ) ≤ (A381358 (m + n) : ℝ) := (Nat.cast_le (α := ℝ)).mpr h_super_mn
        rw [Nat.cast_mul] at h_cast_le
        exact h_cast_le
      have h_log_mono : Real.log (A381358 (m + n) : ℝ) ≥ Real.log ((A381358 m : ℝ) * (A381358 n : ℝ)) := by
        apply Real.log_le_log
        · linarith
        · exact h_super_cast
      rw [Real.log_mul] at h_log_mono
      · linarith
      · linarith
      · linarith

lemma u_div_n_ge (n : ℕ) : u n / (n : ℝ) ≥ - Real.log 2 := by
  by_cases hn : n = 0
  · subst hn
    unfold u
    simp
  · unfold u
    split_ifs
    have h_le := A381358_le_pow n
    have h_le_cast : (A381358 n : ℝ) ≤ (2 : ℝ) ^ n := by
      have h1 : (A381358 n : ℝ) ≤ (2 ^ n : ℝ) := (Nat.cast_le (α := ℝ)).mpr h_le
      have h2 : (2 ^ n : ℝ) = (2 : ℝ) ^ n := by simp
      rwa [h2] at h1
    have h_pos : (A381358 n : ℝ) ≥ 1 := by
      have := A381587_T_sum_pos n hn
      exact (Nat.one_le_cast (α := ℝ)).mpr this
    have h_log_mono : Real.log (A381358 n : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := by
      apply Real.log_le_log
      · linarith
      · exact h_le_cast
    have h_log_pow : Real.log ((2 : ℝ) ^ n) = n * Real.log 2 := by
      rw [← Real.log_rpow (by linarith)]
      simp
    rw [h_log_pow] at h_log_mono
    have h_div : - Real.log (A381358 n : ℝ) / (n : ℝ) ≥ - Real.log 2 := by
      have h_n_pos : (n : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [ge_iff_le]
      rw [neg_le_neg_iff]
      rw [div_le_iff₀ h_n_pos]
      linarith
    exact h_div

lemma exp_neg_u_div_n_eq (n : ℕ) (hn : n ≠ 0) :
    Real.exp (- (u n / (n : ℝ))) = (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹) := by
  unfold u
  split_ifs
  have h_pos : (A381358 n : ℝ) > 0 := by
    have := A381587_T_sum_pos n hn
    exact Nat.cast_pos.mpr this
  rw [neg_div, neg_neg]
  rw [Real.rpow_def_of_pos h_pos]
  congr 1
  rw [div_eq_mul_inv]

lemma tendsto_exp_neg_u_div_n {L' : ℝ} (h : Filter.Tendsto (fun n => u n / (n : ℝ)) Filter.atTop (nhds L')) :
    Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds (Real.exp (- L'))) := by
  have h_neg : Filter.Tendsto (fun n => - (u n / (n : ℝ))) Filter.atTop (nhds (- L')) := by
    exact Filter.Tendsto.neg h
  have h_exp : Filter.Tendsto (fun n => Real.exp (- (u n / (n : ℝ)))) Filter.atTop (nhds (Real.exp (- L'))) := by
    exact Real.tendsto_exp.comp h_neg
  apply Filter.Tendsto.congr' _ h_exp
  rw [Filter.EventuallyEq]
  have h_eventually : ∀ᶠ (n : ℕ) in Filter.atTop, n ≥ 1 := by
    exact Filter.eventually_ge_atTop 1
  apply h_eventually.mono
  intro n hn
  have hn_ne : n ≠ 0 := by omega
  exact exp_neg_u_div_n_eq n hn_ne

theorem A381358_limit_exists_of_subadditive (h_sub : Subadditive u) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) := by
  have h_bdd : BddBelow (Set.range (fun n => u n / (n : ℝ))) := by
    use - Real.log 2
    rintro x ⟨n, rfl⟩
    exact u_div_n_ge n
  have h_lim := h_sub.tendsto_lim h_bdd
  use Real.exp (- h_sub.lim)
  exact tendsto_exp_neg_u_div_n h_lim

lemma R_bound_L_L (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 2) :
    (run_lengths_nat (A381587_T (n + m)).reverse).length ≥ (A381587_T n).length * (A381587_T m).length := by
  sorry

lemma L_bound (n m : ℕ) (hn : n ≥ 2) (hm : m ≥ 1) :
    (A381587_T (n + m)).length ≥ (A381587_T n).length * A381358 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | k
    · omega
    · have h1 : A381358 1 = 1 := by decide
      rw [h1, mul_one]
      exact A381587_T_length_mono_le n (n + 1) (by omega)
    · have h2 : A381358 2 = 1 := by decide
      rw [h2, mul_one]
      exact A381587_T_length_mono_le n (n + 2) (by omega)
    · have h_rec := A381358_recurrence_step k
      rw [h_rec]
      rw [Nat.mul_add]
      have h_len_rec : (A381587_T (n + k + 3)).length = (run_lengths_nat (A381587_T (n + k + 2)).reverse).length + (A381587_T (n + k + 2)).length := by
        have h_eq : n + k + 3 = (n + k - 1) + 4 := by omega
        rw [h_eq]
        exact A381587_T_length_recurrence (n + k - 1)
      rw [h_len_rec]
      have ih_k2 := ih (k + 2) (by omega)
      have h_R := R_bound_L_L n (k + 2) hn (by omega)
      omega



lemma A381587_T_length_le_pow (n : ℕ) : (A381587_T n).length ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · dsimp [A381587_T]
      decide
    · dsimp [A381587_T]
      decide
    · dsimp [A381587_T]
      decide
    · dsimp [A381587_T]
      decide
    · -- n = k + 4
      dsimp [A381587_T]
      rw [length_append]
      have h_run := run_lengths_nat_length_le (l := (A381587_T (k + 3)).reverse)
      rw [length_reverse] at h_run
      have ih_k3 := ih (k + 3) (by omega)
      have h_pow : 2 ^ (k + 3) + 2 ^ (k + 3) = 2 ^ (k + 4) := by ring
      omega


lemma A381358_le_pow (n : ℕ) : A381358 n ≤ 2 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | k
    · dsimp [A381358, A381587_T]
      decide
    · dsimp [A381358, A381587_T]
      decide
    · dsimp [A381358, A381587_T]
      decide
    · dsimp [A381358, A381587_T]
      decide
    · -- n = k + 4
      dsimp [A381358, A381587_T]
      rw [List.sum_append, run_lengths_nat_sum, length_reverse]
      have ih_k3 := ih (k + 3) (by omega)
      have h_len := A381587_T_length_le_pow (k + 3)
      have h_pow : 2 ^ (k + 3) + 2 ^ (k + 3) = 2 ^ (k + 4) := by ring
      omega


lemma A381358_recurrence (k : ℕ) : A381358 (k + 4) = A381358 (k + 3) + (A381587_T (k + 3)).length := by
  dsimp [A381358, A381587_T]
  rw [List.sum_append, run_lengths_nat_sum, length_reverse]


lemma A381587_T_length_recurrence (k : ℕ) : (A381587_T (k + 4)).length = (run_lengths_nat (A381587_T (k + 3)).reverse).length + (A381587_T (k + 3)).length := by
  dsimp [A381587_T]
  rw [List.length_append]

lemma A381587_T_length_mono (n : ℕ) : (A381587_T n).length ≤ (A381587_T (n + 1)).length := by
  rcases n with _ | _ | _ | k
  · dsimp [A381587_T]
    decide
  · dsimp [A381587_T]
    decide
  · dsimp [A381587_T]
    decide
  · rw [A381587_T_length_recurrence k]
    omega


lemma A381587_T_length_mono_le (n m : ℕ) (h : n ≤ m) : (A381587_T n).length ≤ (A381587_T m).length := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    rw [this]
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · rw [h_eq]
    · have h_le : n ≤ m := by omega
      have ih_le := ih h_le
      exact ih_le.trans (A381587_T_length_mono m)



lemma A381358_mono (n : ℕ) : A381358 n ≤ A381358 (n + 1) := by
  rcases n with _ | _ | _ | k
  · -- n = 0
    dsimp [A381358, A381587_T]
    decide
  · -- n = 1
    dsimp [A381358, A381587_T]
    decide
  · -- n = 2
    dsimp [A381358, A381587_T]
    decide
  · -- n = k + 3
    rw [A381358_recurrence k]
    omega


lemma A381358_mono_le (n m : ℕ) (h : n ≤ m) : A381358 n ≤ A381358 m := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    rw [this]
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · rw [h_eq]
    · have h_le : n ≤ m := by omega
      have ih_le := ih h_le
      exact ih_le.trans (A381358_mono m)


lemma A381358_recurrence_add (n m : ℕ) (hn : n ≥ 3) (hm : m ≥ 1) :
    A381358 (n + m) = A381358 (n - 1 + m) + (A381587_T (n - 1 + m)).length := by
  rcases n with _ | _ | _ | k
  · omega
  · omega
  · omega
  · -- n = k + 3
    have h_eq1 : k + 3 + m = (k + m - 1) + 4 := by omega
    have h_eq2 : k + 3 - 1 + m = (k + m - 1) + 3 := by omega
    rw [h_eq1, A381358_recurrence, h_eq2]

lemma A381358_recurrence_step (k : ℕ) : A381358 (k + 3) = A381358 (k + 2) + (A381587_T (k + 2)).length := by
  rcases k with _ | k_prev
  · dsimp [A381358, A381587_T]
    decide
  · rw [show k_prev + 1 + 3 = k_prev + 4 by rfl]
    rw [show k_prev + 1 + 2 = k_prev + 3 by rfl]
    rw [A381358_recurrence]


lemma S_supermultiplicative_of_L_bound (hL : ∀ n ≥ 2, ∀ m ≥ 1, (A381587_T (n + m)).length ≥ (A381587_T n).length * A381358 m)
    (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) : A381358 (n + m) ≥ A381358 n * A381358 m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | k
    · omega
    · have h1 : A381358 1 = 1 := by decide
      rw [h1, one_mul]
      exact A381358_mono_le m (1 + m) (by omega)
    · have h2 : A381358 2 = 1 := by decide
      rw [h2, one_mul]
      exact A381358_mono_le m (2 + m) (by omega)
    · -- n = k + 3
      have h_rec := A381358_recurrence_add (k + 3) m (by omega) hm
      rw [h_rec]
      have ih_k2 := ih (k + 2) (by omega) (by omega) m hm
      have h_L_b := hL (k + 2) (by omega) m hm
      have h_step := A381358_recurrence_step k
      rw [h_step, Nat.add_mul]
      omega


/--
A381358 If it exists, the limit of $\mathrm{A381358}(n)^{1/n}$ as $n \to \infty$.
The conjecture is that this limit exists.
-/
theorem A381358_limit_exists :
  ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => (A381358 n : ℝ) ^ ((n : ℝ) ⁻¹)) Filter.atTop (nhds L) :=
  have h_super : ∀ n m, A381358 (n + m) ≥ A381358 n * A381358 m := by
    intro n m
    by_cases hn : n ≥ 1
    · by_cases hm : m ≥ 1
      · apply S_supermultiplicative_of_L_bound
        · intro n' hn' m' hm'
          exact L_bound n' m' hn' hm'
        · exact hn
        · exact hm
      · have : m = 0 := by omega
        subst this
        simp [A381358, A381587_T]
    · have : n = 0 := by omega
      subst this
      simp [A381358, A381587_T]
  have h_sub := u_subadditive h_super
  exact A381358_limit_exists_of_subadditive h_sub
