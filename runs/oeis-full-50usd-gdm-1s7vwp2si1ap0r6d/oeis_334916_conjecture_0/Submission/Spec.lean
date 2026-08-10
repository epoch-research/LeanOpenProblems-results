import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000


open Nat List Set Function

/--
A helper function to compute the "baseless" value of a sequence of digits $D$ (most significant first).
If $D = [d_k, d_{k-1}, \ldots, d_0]$, the value is computed by
$V_{k} = d_k$. The final result is $V_0 \cdot d_0$, where $V_0$ is accumulated by $V_{i} = V_{i+1} \cdot d_{i+1} + d_i$.
-/
def baseless_value_list (D : List ℕ) : ℕ :=
  match D with
  | [] => 0
  | [_] => 0 -- Single digit numbers A > 1 must have at least 2 digits to be baseless.
  | d_k :: ds_rest =>
    -- The initial state carries (current_value, multiplier_for_next_step).
    let initial_state : ℕ × ℕ := (d_k, d_k)

    -- ds_rest = [d_{k-1}, \ldots, d_0] are the digits for the fold.
    let V_0_and_d_0 : ℕ × ℕ := ds_rest.foldl
      (fun state d_curr =>
        let (V_prev, d_prev_mult) := state
        -- The multiplier for the next step is the digit just added, following the OEIS pattern.
        (V_prev * d_prev_mult + d_curr, d_curr)
      ) initial_state

    let (V₀, d₀) := V_0_and_d_0
    -- Final multiplication by the last digit, d₀.
    V₀ * d₀

/--
$A$ is a "baseless number" in base $b$ if adding and multiplying its base $b$ digits left to right yields $A$.
-/
def is_baseless (b A : ℕ) : Prop :=
  -- We use Nat.digits which is safe for base b >= 2.
  baseless_value_list ((digits b A).reverse) = A

/--
The set of numbers greater than 1 that are baseless in base $n$.
-/
def BaselessSet (n : ℕ) : Set ℕ :=
  { A : ℕ | A > 1 ∧ is_baseless n A }

open scoped Classical in
/--
A334916: $a(n)$ is the smallest number $> 1$ whose base $n$ digits yield the original number
when added and multiplied left to right; or $0$ if no such number exists.
-/
noncomputable def A334916 (n : ℕ) : ℕ :=
  if n < 4 then
    0 -- Bases 1, 2, 3 lead to a(n)=0. Base 1 is ill-defined for digits extraction.
  else
    sInf (BaselessSet n)

/--
The number 8385 = ((((8)8+3)3+8)8+5)5 is known to be the unique baseless number in base 10.
The conjecture is that the baseless numbers in base 6 and 10 are unique, and questions
whether another base $n$, other than 6 and 10, has a unique tasteless number.
We formalize the uniqueness claim for $n=6$ and $n=10$ using the unique existence quantifier.
-/
theorem digits_38_324224 : digits 38 324224 = [8, 20, 34, 5] := by
  have h_base : 1 < 38 := by decide
  have h1 : 324224 = 8 + 38 * 8532 := by decide
  rw [h1]
  rw [digits_add 38 h_base 8 8532 (by decide) (by decide)]
  have h2 : 8532 = 20 + 38 * 224 := by decide
  rw [h2]
  rw [digits_add 38 h_base 20 224 (by decide) (by decide)]
  have h3 : 224 = 34 + 38 * 5 := by decide
  rw [h3]
  rw [digits_add 38 h_base 34 5 (by decide) (by decide)]
  have h4 : 5 = 5 + 38 * 0 := by decide
  rw [h4]
  rw [digits_add 38 h_base 5 0 (by decide) (by decide)]
  rw [digits_zero]

theorem is_baseless_38_324224 : is_baseless 38 324224 := by
  unfold is_baseless
  rw [digits_38_324224]
  rfl

theorem digits_6_160 : digits 6 160 = [4, 2, 4] := by
  have h_base : 1 < 6 := by decide
  have h1 : 160 = 4 + 6 * 26 := by decide
  rw [h1]
  rw [digits_add 6 h_base 4 26 (by decide) (by decide)]
  have h2 : 26 = 2 + 6 * 4 := by decide
  rw [h2]
  rw [digits_add 6 h_base 2 4 (by decide) (by decide)]
  have h3 : 4 = 4 + 6 * 0 := by decide
  rw [h3]
  rw [digits_add 6 h_base 4 0 (by decide) (by decide)]
  rw [digits_zero]

theorem is_baseless_6_160 : is_baseless 6 160 := by
  unfold is_baseless
  rw [digits_6_160]
  rfl

theorem digits_10_8385 : digits 10 8385 = [5, 8, 3, 8] := by
  have h_base : 1 < 10 := by decide
  have h1 : 8385 = 5 + 10 * 838 := by decide
  rw [h1]
  rw [digits_add 10 h_base 5 838 (by decide) (by decide)]
  have h2 : 838 = 8 + 10 * 83 := by decide
  rw [h2]
  rw [digits_add 10 h_base 8 83 (by decide) (by decide)]
  have h3 : 83 = 3 + 10 * 8 := by decide
  rw [h3]
  rw [digits_add 10 h_base 3 8 (by decide) (by decide)]
  have h4 : 8 = 8 + 10 * 0 := by decide
  rw [h4]
  rw [digits_add 10 h_base 8 0 (by decide) (by decide)]
  rw [digits_zero]

theorem is_baseless_10_8385 : is_baseless 10 8385 := by
  unfold is_baseless
  rw [digits_10_8385]
  rfl

def fold_inv (state : ℕ × ℕ) (k : ℕ) : Prop :=
  4 * state.1 ≤ 5^(k+1) - 5 ∧ state.2 ≤ 5

theorem one_le_five_pow (k : ℕ) : 1 ≤ 5^k := by
  induction k with
  | zero => omega
  | succ k' ih =>
    rw [Nat.pow_succ]
    omega

theorem fold_step_inv (state : ℕ × ℕ) (k : ℕ) (d_curr : ℕ) (h_inv : fold_inv state k) (hd : d_curr ≤ 5) :
    fold_inv (state.1 * state.2 + d_curr, d_curr) (k + 1) := by
  unfold fold_inv at *
  refine ⟨?_, hd⟩
  have h1 : 4 * (state.1 * state.2 + d_curr) = (4 * state.1) * state.2 + 4 * d_curr := by ring
  rw [h1]
  have h2 : (4 * state.1) * state.2 ≤ (5^(k+1) - 5) * 5 := by
    apply Nat.mul_le_mul h_inv.1 h_inv.2
  have h3 : 4 * d_curr ≤ 20 := by omega
  have h4 : (4 * state.1) * state.2 + 4 * d_curr ≤ (5^(k+1) - 5) * 5 + 20 := by omega
  have h5 : (5^(k+1) - 5) * 5 + 20 = 5^(k + 2) - 5 := by
    rw [Nat.mul_sub_right_distrib]
    have h_pow : 5^(k+1) * 5 = 5^(k+2) := by rfl
    rw [h_pow]
    have h_ge : 5^(k+2) ≥ 25 := by
      rw [Nat.pow_succ, Nat.pow_succ]
      have h_one := one_le_five_pow k
      omega
    omega
  rw [h5] at h4
  exact h4

theorem fold_inv_of_list (D : List ℕ) (hD : ∀ x ∈ D, x ≤ 5) (state : ℕ × ℕ) (k : ℕ) (h_inv : fold_inv state k) :
    fold_inv (D.foldl (fun state d_curr => (state.1 * state.2 + d_curr, d_curr)) state) (k + D.length) := by
  induction D generalizing state k with
  | nil =>
    simp [h_inv]
  | cons d_curr ds_rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hd : d_curr ≤ 5 := by
      apply hD d_curr
      simp
    have h_next : fold_inv (state.1 * state.2 + d_curr, d_curr) (k + 1) := by
      apply fold_step_inv state k d_curr h_inv hd
    have h_ih := ih (by
      intro x hx
      apply hD x
      simp [hx]
    ) (state.1 * state.2 + d_curr, d_curr) (k + 1) h_next
    have h_assoc : k + 1 + ds_rest.length = k + (ds_rest.length + 1) := by omega
    rw [← h_assoc]
    exact h_ih

theorem baseless_value_list_le (D : List ℕ) (hD : ∀ x ∈ D, x ≤ 5) (hD_len : D.length ≥ 2) :
    4 * baseless_value_list D ≤ 5^(D.length + 2) - 25 := by
  match D with
  | [] => contradiction
  | [_] => contradiction
  | d_k :: d_next :: ds_rest =>
    have hd_k : d_k ≤ 5 := by
      apply hD d_k
      simp
    have h_init : fold_inv (d_k, d_k) 1 := by
      unfold fold_inv
      omega
    have h_fold := fold_inv_of_list (d_next :: ds_rest) (by
      intro x hx
      apply hD x
      simp [hx]
    ) (d_k, d_k) 1 h_init
    have h_len : (d_k :: d_next :: ds_rest).length = (d_next :: ds_rest).length + 1 := by rfl
    have h_fold_comm : 1 + (d_next :: ds_rest).length = (d_next :: ds_rest).length + 1 := by omega
    rw [h_fold_comm] at h_fold
    rw [← h_len] at h_fold
    unfold fold_inv at h_fold
    have h_mult : (4 * ((d_next :: ds_rest).foldl (fun state d_curr => (state.1 * state.2 + d_curr, d_curr)) (d_k, d_k)).1) *
      ((d_next :: ds_rest).foldl (fun state d_curr => (state.1 * state.2 + d_curr, d_curr)) (d_k, d_k)).2 ≤
      (5^((d_k :: d_next :: ds_rest).length + 1) - 5) * 5 := by
        apply Nat.mul_le_mul h_fold.1 h_fold.2
    have h_eq : 4 * baseless_value_list (d_k :: d_next :: ds_rest) =
      (4 * ((d_next :: ds_rest).foldl (fun state d_curr => (state.1 * state.2 + d_curr, d_curr)) (d_k, d_k)).1) *
      ((d_next :: ds_rest).foldl (fun state d_curr => (state.1 * state.2 + d_curr, d_curr)) (d_k, d_k)).2 := by
        unfold baseless_value_list
        ring
    rw [h_eq]
    have h_trans : (5^((d_k :: d_next :: ds_rest).length + 1) - 5) * 5 = 5^((d_k :: d_next :: ds_rest).length + 2) - 25 := by
      rw [Nat.mul_sub_right_distrib]
      have h_pow : 5^((d_k :: d_next :: ds_rest).length + 1) * 5 = 5^((d_k :: d_next :: ds_rest).length + 2) := by rfl
      rw [h_pow]
    rw [h_trans] at h_mult
    exact h_mult

def digits_fuel (b n fuel : ℕ) : List ℕ :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if n = 0 then []
    else (n % b) :: digits_fuel b (n / b) fuel'

def my_digits (b n : ℕ) : List ℕ :=
  digits_fuel b n (n + 1)

def my_is_baseless (b A : ℕ) : Bool :=
  baseless_value_list ((my_digits b A).reverse) == A

theorem digits_fuel_eq_digits (b n : ℕ) (hb : 2 ≤ b) (fuel : ℕ) (h_fuel : n < fuel) :
    digits_fuel b n fuel = digits b n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel' ih =>
    unfold digits_fuel
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [hn]
      have hb_pos : 0 < b := by omega
      have h_div_lt : n / b < n := Nat.div_lt_self (by positivity) hb
      have h_div_fuel : n / b < fuel' := by omega
      rw [ih (n / b) h_div_fuel]
      exact (digits_of_two_le_of_pos hb (by positivity)).symm

theorem my_digits_eq_digits (b n : ℕ) (hb : 2 ≤ b) : my_digits b n = digits b n := by
  unfold my_digits
  apply digits_fuel_eq_digits b n hb
  omega

theorem my_is_baseless_iff_is_baseless (b n : ℕ) (hb : 2 ≤ b) :
    my_is_baseless b n = true ↔ is_baseless b n := by
  unfold my_is_baseless is_baseless
  rw [my_digits_eq_digits b n hb]
  simp [beq_iff_eq]

theorem baseless_6_lt_1000_forall : ∀ A < 1000, A > 1 → my_is_baseless 6 A = true → A = 160 := by
  decide

theorem baseless_6_lt_1000 : ∀ A, A > 1 → A < 1000 → is_baseless 6 A → A = 160 := by
  intro A hA h_lt h_base
  have h_my := (my_is_baseless_iff_is_baseless 6 A (by decide)).mpr h_base
  exact baseless_6_lt_1000_forall A h_lt hA h_my


theorem baseless_10_lt_10000_forall : (List.range 10000).all (fun A =>
    if A > 1 ∧ my_is_baseless 10 A = true then A == 8385 else true) = true := by
  decide

theorem baseless_10_lt_10000 : ∀ A, A > 1 → A < 10000 → is_baseless 10 A → A = 8385 := by
  intro A hA h_lt h_base
  have h_my := (my_is_baseless_iff_is_baseless 10 A (by decide)).mpr h_base
  have h_all : (List.range 10000).all (fun A => if A > 1 ∧ my_is_baseless 10 A = true then A == 8385 else true) = true := baseless_10_lt_10000_forall
  rw [List.all_eq_true] at h_all
  have h_A := h_all A (by
    rw [List.mem_range]
    exact h_lt
  )
  split_ifs at h_A with h_cond
  · exact beq_iff_eq.mp h_A
  · exfalso
    exact h_cond ⟨hA, h_my⟩


theorem pow_bound_k (k : ℕ) : 5^(k + 22) - 25 < 4 * 6^(k + 19) := by
  induction k with
  | zero =>
    decide
  | succ k' ih =>
    have h_lhs : 4 * 6^(k' + 1 + 19) = (4 * 6^(k' + 19)) * 6 := by
      have : k' + 1 + 19 = k' + 19 + 1 := by omega
      rw [this, Nat.pow_succ]
      ring
    have h_rhs : 5^(k' + 1 + 22) = 5^(k' + 22) * 5 := by
      have : k' + 1 + 22 = k' + 22 + 1 := by omega
      rw [this, Nat.pow_succ]
    rw [h_lhs, h_rhs]
    have h_step : (5^(k' + 22) - 25) * 6 < (4 * 6^(k' + 19)) * 6 := Nat.mul_lt_mul_of_pos_right ih (by decide)
    have h_trans : 5^(k' + 22) * 5 - 25 ≤ (5^(k' + 22) - 25) * 6 := by
      have h_pow : 5^(k' + 22) ≥ 150 := by
        have : k' + 22 ≥ 22 := by omega
        have h_ge := Nat.pow_le_pow_right (by decide : 1 ≤ 5) this
        have h_22 : 5^22 ≥ 150 := by decide
        omega
      rw [Nat.mul_sub_right_distrib]
      have : 5^(k' + 22) * 6 = 5^(k' + 22) * 5 + 5^(k' + 22) := by ring
      rw [this]
      omega
    omega

theorem pow_bound (L : ℕ) (hL : L ≥ 20) : 5^(L + 2) - 25 < 4 * 6^(L - 1) := by
  have h_lhs : L - 1 = (L - 20) + 19 := by omega
  have h_rhs : L + 2 = (L - 20) + 22 := by omega
  rw [h_lhs, h_rhs]
  exact pow_bound_k (L - 20)


def fold_step (state : ℕ × ℕ) (d_curr : ℕ) : ℕ × ℕ :=
  (state.1 * state.2 + d_curr, d_curr)

def get_V_max (V : ℕ) (rem : ℕ) : ℕ :=
  match rem with
  | 0 => V
  | r + 1 => get_V_max (V * 5 + 5) r

def fold_val (acc : ℕ) (d : ℕ) : ℕ :=
  acc * 6 + d

def dfs_6_rec (rem : ℕ) (V : ℕ) (d_prev : ℕ) (val_b : ℕ) : List ℕ :=
  match rem with
  | 0 => if V * d_prev = val_b then [val_b] else []
  | rem' + 1 =>
    let d_curr_list := [0, 1, 2, 3, 4, 5]
    let filtered := d_curr_list.map (fun d_curr =>
      let V_next := V * d_prev + d_curr
      let val_b_next := val_b * 6 + d_curr
      if val_b_next * 6^rem' > get_V_max V_next rem' * 5 then
        []
      else
        dfs_6_rec rem' V_next d_curr val_b_next
    )
    List.flatten filtered

def dfs_6_start (L : ℕ) : List ℕ :=
  match L with
  | 0 => []
  | 1 => []
  | L' + 1 =>
    let d_curr_list := [1, 2, 3, 4, 5]
    let filtered := d_curr_list.map (fun d_curr =>
      let V_next := d_curr
      let val_b_next := d_curr
      if val_b_next * 6^L' > get_V_max V_next L' * 5 then
        []
      else
        dfs_6_rec L' V_next d_curr val_b_next
    )
    List.flatten filtered

theorem fold_le_get_V_max (D : List ℕ) (hD : ∀ x ∈ D, x ≤ 5) (state : ℕ × ℕ) (V : ℕ)
    (h_state1 : state.1 ≤ V) (h_state2 : state.2 ≤ 5) :
    (D.foldl fold_step state).1 ≤ get_V_max V D.length ∧ (D.foldl fold_step state).2 ≤ 5 := by
  induction D generalizing state V with
  | nil =>
    simp
    exact ⟨h_state1, h_state2⟩
  | cons d ds ih =>
    simp [fold_step]
    have hd : d ≤ 5 := hD d (by simp)
    have h_next1 : state.1 * state.2 + d ≤ V * 5 + 5 := by
      have h1 : state.1 * state.2 ≤ V * 5 := Nat.mul_le_mul h_state1 h_state2
      omega
    have h_next2 : d ≤ 5 := hd
    have h_ih := ih (fun x hx => hD x (by simp [hx])) (state.1 * state.2 + d, d) (V * 5 + 5) h_next1 h_next2
    exact h_ih

theorem foldl_base_ge (D : List ℕ) (state : ℕ) :
    D.foldl fold_val state ≥ state * 6^(D.length) := by
  induction D generalizing state with
  | nil => simp
  | cons d ds ih =>
    simp [fold_val]
    have h_step : (state * 6 + d) * 6^ds.length ≥ state * 6^(ds.length + 1) := by
      have : (state * 6 + d) * 6^ds.length = state * 6^(ds.length + 1) + d * 6^ds.length := by
        ring
      omega
    have h_ih := ih (state * 6 + d)
    omega

theorem mem_flatten_map {α β : Type} (x : α) (L : List α) (hx : x ∈ L) (f : α → List β) (y : β) (hy : y ∈ f x) :
    y ∈ List.flatten (L.map f) := by
  rw [List.mem_flatten]
  use f x
  refine ⟨?_, hy⟩
  rw [List.mem_map]
  use x

theorem dfs_6_rec_correct (rem : ℕ) (D_suff : List ℕ) (h_len : D_suff.length = rem)
    (hD : ∀ x ∈ D_suff, x ≤ 5) (V : ℕ) (d_prev : ℕ) (val_b : ℕ)
    (h_baseless : (D_suff.foldl fold_step (V, d_prev)).1 * (D_suff.foldl fold_step (V, d_prev)).2 = D_suff.foldl fold_val val_b) :
    D_suff.foldl fold_val val_b ∈ dfs_6_rec rem V d_prev val_b := by
  induction rem generalizing D_suff V d_prev val_b with
  | zero =>
    have h_nil : D_suff = [] := List.eq_nil_of_length_eq_zero h_len
    subst h_nil
    simp only [List.foldl_nil] at h_baseless
    simp [dfs_6_rec, h_baseless]
  | succ rem' ih =>
    match D_suff with
    | d_curr :: ds_rest =>
      have h_len_ds : ds_rest.length = rem' := by
        simp at h_len
        omega
      have hd_curr : d_curr ≤ 5 := hD d_curr (by simp)
      have hD_ds : ∀ x ∈ ds_rest, x ≤ 5 := fun x hx => hD x (by simp [hx])
      simp only [List.foldl_cons] at h_baseless
      unfold fold_step at h_baseless
      
      have h_val_ge : ds_rest.foldl fold_val (fold_val val_b d_curr) ≥ (fold_val val_b d_curr) * 6^rem' := by
        have h_ge := foldl_base_ge ds_rest (fold_val val_b d_curr)
        rw [h_len_ds] at h_ge
        exact h_ge
        
      have h_fold_le := fold_le_get_V_max ds_rest hD_ds (V * d_prev + d_curr, d_curr) (V * d_prev + d_curr) (by omega) hd_curr
      have h_baseless_le : (ds_rest.foldl fold_step (V * d_prev + d_curr, d_curr)).1 * (ds_rest.foldl fold_step (V * d_prev + d_curr, d_curr)).2 ≤
          get_V_max (V * d_prev + d_curr) rem' * 5 := by
        rw [h_len_ds] at h_fold_le
        apply Nat.mul_le_mul h_fold_le.1 h_fold_le.2
        
      have h_no_prune : (fold_val val_b d_curr) * 6^rem' ≤ get_V_max (V * d_prev + d_curr) rem' * 5 := by
        calc
          (fold_val val_b d_curr) * 6^rem' ≤ ds_rest.foldl fold_val (fold_val val_b d_curr) := h_val_ge
          _ = (ds_rest.foldl fold_step (V * d_prev + d_curr, d_curr)).1 * (ds_rest.foldl fold_step (V * d_prev + d_curr, d_curr)).2 := h_baseless.symm
          _ ≤ get_V_max (V * d_prev + d_curr) rem' * 5 := h_baseless_le
        
      have h_not_gt : ¬ ((fold_val val_b d_curr) * 6^rem' > get_V_max (V * d_prev + d_curr) rem' * 5) := by
        omega
        
      have h_ih := ih ds_rest h_len_ds hD_ds (V * d_prev + d_curr) d_curr (fold_val val_b d_curr) h_baseless
      
      have h_mem_list : d_curr ∈ [0, 1, 2, 3, 4, 5] := by
        simp
        omega
        
      unfold dfs_6_rec
      apply mem_flatten_map d_curr [0, 1, 2, 3, 4, 5] h_mem_list
      unfold fold_val at h_not_gt
      simp [h_not_gt]
      unfold fold_val at h_ih
      exact h_ih

theorem foldl_fold_val_eq_ofDigits_s (b : ℕ) (L : List ℕ) (s : ℕ) :
    L.reverse.foldl (fun acc d => acc * b + d) s = s * b^(L.length) + ofDigits b L := by
  induction L generalizing s with
  | nil => simp [ofDigits]
  | cons d L ih =>
    rw [List.reverse_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih s]
    simp [ofDigits]
    ring

theorem fold_val_digits_eq (b : ℕ) (A : ℕ) :
    ((digits b A).reverse).foldl (fun acc d => acc * b + d) 0 = A := by
  rw [foldl_fold_val_eq_ofDigits_s, zero_mul, zero_add, ofDigits_digits]

theorem getLast_eq_head_reverse {α : Type} [Inhabited α] (l : List α) (h : l ≠ []) :
    l.getLast h = l.reverse.head! := by
  match h_eq : l.reverse with
  | [] =>
    have : l = [] := by
      rw [← List.reverse_reverse l, h_eq]
      rfl
    contradiction
  | d :: ds =>
    have h_eq2 : l = ds.reverse ++ [d] := by
      have : l = l.reverse.reverse := by simp
      rw [this, h_eq]
      simp
    have : l.getLast h = (ds.reverse ++ [d]).getLast (by simp) := by
      congr
    rw [this]
    simp

theorem head_reverse_ne_zero (A : ℕ) (h_pos : A > 0) :
    ((digits 6 A).reverse).head! ≠ 0 := by
  have h_ne : digits 6 A ≠ [] := by
    rw [Nat.digits_ne_nil_iff_ne_zero]
    omega
  have h_getLast := Nat.getLast_digit_ne_zero 6 (by omega : A ≠ 0)
  rw [← getLast_eq_head_reverse (digits 6 A) h_ne]
  exact h_getLast

theorem digits_6_lt_6 (A : ℕ) (x : ℕ) (hx : x ∈ digits 6 A) : x < 6 :=
  Nat.digits_lt_base (by decide) hx

theorem reverse_digits_6_le_5 (A : ℕ) (x : ℕ) (hx : x ∈ (digits 6 A).reverse) : x ≤ 5 := by
  have h_mem : x ∈ digits 6 A := by
    rw [← List.mem_reverse]
    exact hx
  have h_lt := digits_6_lt_6 A x h_mem
  omega

theorem dfs_6_start_correct (A : ℕ) (h_baseless : is_baseless 6 A) (h_len : (digits 6 A).length = L) (h_A : A > 1) :
    A ∈ dfs_6_start L := by
  have h_pos : A > 0 := by omega
  have h_L_ne : L ≠ 0 := by
    rw [← h_len]
    intro hc
    have h_nil : digits 6 A = [] := List.eq_nil_of_length_eq_zero hc
    have h_A0 : A = 0 := by
      rw [← Nat.ofDigits_digits 6 A, h_nil]
      rfl
    omega
  have h_L_pos : L > 0 := by omega
  cases L with
  | zero => contradiction
  | succ L' =>
    cases L' with
    | zero =>
      have h_len_1 : (digits 6 A).length = 1 := h_len
      have h_rev_len : (digits 6 A).reverse.length = 1 := by simp [h_len_1]
      match h_eq : (digits 6 A).reverse with
      | [] =>
        simp [h_eq] at h_rev_len
      | [d] =>
        unfold is_baseless baseless_value_list at h_baseless
        rw [h_eq] at h_baseless
        simp at h_baseless
        omega
      | _ :: _ :: _ =>
        simp only [h_eq, List.length_cons] at h_rev_len
        omega
    | succ L'' =>
      match h_eq : (digits 6 A).reverse with
      | [] =>
        have : (digits 6 A).reverse.length = 0 := by simp [h_eq]
        simp [h_len] at this
      | [d] =>
        have h_rev_len : (digits 6 A).reverse.length = 1 := by simp [h_eq]
        have h_len_eq : (digits 6 A).reverse.length = L''.succ.succ := by simp [h_len]
        omega
      | d_curr :: d_next :: ds_rest' =>
        have h_len_ds : (d_next :: ds_rest').length = L''.succ := by
          have h1 : (digits 6 A).reverse.length = L''.succ.succ := by simp [h_len]
          have h2 : (digits 6 A).reverse.length = (d_next :: ds_rest').length + 1 := by
            rw [h_eq]
            rfl
          omega
        have hd_curr_ne : d_curr ≠ 0 := by
          have h_head : (digits 6 A).reverse.head! = d_curr := by simp [h_eq]
          rw [← h_head]
          exact head_reverse_ne_zero A h_pos
        have hd_curr_lt : d_curr < 6 := by
          have : d_curr ∈ (digits 6 A).reverse := by simp [h_eq]
          rw [List.mem_reverse] at this
          exact digits_6_lt_6 A d_curr this
        have hd_curr : d_curr ≤ 5 := by omega
        have hd_curr_mem : d_curr ∈ [1, 2, 3, 4, 5] := by
          simp
          omega
        have h_all : ∀ x ∈ d_next :: ds_rest', x ≤ 5 := by
          intro x hx
          have h_mem : x ∈ (digits 6 A).reverse := by
            rw [h_eq]
            exact List.Mem.tail d_curr hx
          exact reverse_digits_6_le_5 A x h_mem
        
        have h_fold_eq : (digits 6 A).reverse.foldl (fun acc d => acc * 6 + d) 0 = A := fold_val_digits_eq 6 A
        rw [h_eq] at h_fold_eq
        simp only [List.foldl_cons] at h_fold_eq
        simp only [zero_mul, zero_add] at h_fold_eq
        change (d_next :: ds_rest').foldl fold_val d_curr = A at h_fold_eq
        
        have h_base_eq : ((d_next :: ds_rest').foldl fold_step (d_curr, d_curr)).1 * ((d_next :: ds_rest').foldl fold_step (d_curr, d_curr)).2 =
            (d_next :: ds_rest').foldl fold_val d_curr := by
          unfold is_baseless baseless_value_list at h_baseless
          rw [h_eq] at h_baseless
          simp only at h_baseless
          rw [h_baseless, h_fold_eq]
          
        have h_rec := dfs_6_rec_correct L''.succ (d_next :: ds_rest') h_len_ds h_all d_curr d_curr d_curr h_base_eq
        
        have h_val_ge : (d_next :: ds_rest').foldl fold_val d_curr ≥ d_curr * 6^L''.succ := by
          have h_ge := foldl_base_ge (d_next :: ds_rest') d_curr
          rw [h_len_ds] at h_ge
          exact h_ge
          
        have h_fold_le := fold_le_get_V_max (d_next :: ds_rest') h_all (d_curr, d_curr) d_curr (by omega) hd_curr
        have h_baseless_le : ((d_next :: ds_rest').foldl fold_step (d_curr, d_curr)).1 * ((d_next :: ds_rest').foldl fold_step (d_curr, d_curr)).2 ≤
            get_V_max d_curr L''.succ * 5 := by
          rw [h_len_ds] at h_fold_le
          apply Nat.mul_le_mul h_fold_le.1 h_fold_le.2
        
        have h_not_gt_le : d_curr * 6^L''.succ ≤ get_V_max d_curr L''.succ * 5 := by
          calc
            d_curr * 6^L''.succ ≤ (d_next :: ds_rest').foldl fold_val d_curr := h_val_ge
            _ = ((d_next :: ds_rest').foldl fold_step (d_curr, d_curr)).1 * ((d_next :: ds_rest').foldl fold_step (d_curr, d_curr)).2 := h_base_eq.symm
            _ ≤ get_V_max d_curr L''.succ * 5 := h_baseless_le
        have h_not_gt : ¬ (d_curr * 6^L''.succ > get_V_max d_curr L''.succ * 5) := by
          omega
          
        unfold dfs_6_start
        apply mem_flatten_map d_curr [1, 2, 3, 4, 5] hd_curr_mem
        simp [h_not_gt]
        rw [h_fold_eq] at h_rec
        exact h_rec

theorem baseless_6_unique (A : ℕ) (hA : A > 1) (h_baseless : is_baseless 6 A) : A = 160 := by
  have h_len_eq : (digits 6 A).length = (digits 6 A).length := rfl
  have h_in := dfs_6_start_correct A h_baseless h_len_eq hA
  by_cases hL : (digits 6 A).length < 20
  · have h_len_A : (digits 6 A).length = (digits 6 A).length := rfl
    generalize h_len : (digits 6 A).length = L at h_in h_len_A hL
    interval_cases L
    · have h_ne : digits 6 A ≠ [] := by
        rw [Nat.digits_ne_nil_iff_ne_zero]
        omega
      have h_nil : digits 6 A = [] := List.eq_nil_of_length_eq_zero h_len
      contradiction
    · change A ∈ dfs_6_start 1 at h_in; contradiction
    · change A ∈ dfs_6_start 2 at h_in; contradiction
    · change A ∈ dfs_6_start 3 at h_in
      simp [dfs_6_start, get_V_max, dfs_6_rec] at h_in
      exact h_in
    · change A ∈ dfs_6_start 4 at h_in; contradiction
    · change A ∈ dfs_6_start 5 at h_in; contradiction
    · change A ∈ dfs_6_start 6 at h_in; contradiction
    · change A ∈ dfs_6_start 7 at h_in; contradiction
    · change A ∈ dfs_6_start 8 at h_in; contradiction
    · change A ∈ dfs_6_start 9 at h_in; contradiction
    · change A ∈ dfs_6_start 10 at h_in; contradiction
    · change A ∈ dfs_6_start 11 at h_in; contradiction
    · change A ∈ dfs_6_start 12 at h_in; contradiction
    · change A ∈ dfs_6_start 13 at h_in; contradiction
    · change A ∈ dfs_6_start 14 at h_in; contradiction
    · change A ∈ dfs_6_start 15 at h_in; contradiction
    · change A ∈ dfs_6_start 16 at h_in; contradiction
    · change A ∈ dfs_6_start 17 at h_in; contradiction
    · change A ∈ dfs_6_start 18 at h_in; contradiction
    · change A ∈ dfs_6_start 19 at h_in; contradiction
  · have hL_ge : (digits 6 A).length ≥ 20 := by omega
    let D := (digits 6 A).reverse
    have h_all : ∀ x ∈ D, x ≤ 5 := reverse_digits_6_le_5 A
    have hD_len : D.length ≥ 20 := by
      simp [D]
      omega
    have hD_len2 : D.length ≥ 2 := by omega
    have h_bound : 4 * baseless_value_list D ≤ 5 ^ (D.length + 2) - 25 := by
      exact baseless_value_list_le D h_all hD_len2
    have h_baseless' : baseless_value_list D = A := h_baseless
    rw [h_baseless'] at h_bound
    have h_pow := pow_bound D.length hD_len
    have h_lt : D.length - 1 < (digits 6 A).length := by
      simp [D]
      omega
    have h_ge_pow := (Nat.lt_digits_length_iff (by decide) A).mp h_lt
    have h_ge_pow_4 : 4 * 6^(D.length - 1) ≤ 4 * A := Nat.mul_le_mul_left 4 h_ge_pow
    omega

theorem oeis_334916_conjecture_0 :
    (∃! A, A > 1 ∧ is_baseless 6 A) ∧ (∃! A, A > 1 ∧ is_baseless 10 A) ∧
    -- Formalizing the open question part: "Are there number bases n, other than 6 and 10, that have a unique example?"
    (∃ n > 1, n ≠ 6 ∧ n ≠ 10 ∧ (∃! A, A > 1 ∧ is_baseless n A)) := by
  refine ⟨?_, ?_, ?_⟩
  · use 160
    refine ⟨⟨by decide, is_baseless_6_160⟩, ?_⟩
    intro y hy
    by_cases h_lt : y < 1000
    · exact baseless_6_lt_1000 y hy.1 h_lt hy.2
    · sorry
  · use 8385
    refine ⟨⟨by decide, is_baseless_10_8385⟩, ?_⟩
    intro y hy
    by_cases h_lt : y < 10000
    · exact baseless_10_lt_10000 y hy.1 h_lt hy.2
    · sorry
  · use 38
    refine ⟨by decide, by decide, by decide, ?_⟩
    use 324224
    refine ⟨⟨by decide, is_baseless_38_324224⟩, ?_⟩
    sorry




