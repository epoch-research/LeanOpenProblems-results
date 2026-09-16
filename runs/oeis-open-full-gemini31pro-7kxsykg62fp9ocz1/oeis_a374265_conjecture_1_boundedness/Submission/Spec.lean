import FormalConjectures.Util.ProblemImports
open Nat Finset



-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  -- Nat.digits returns the list of digits in reverse order.
  let digits := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  -- Nat.ofDigits interprets the list from most significant digit first if the base is 10
  ofDigits 10 digits

/--
The set of all possible values $f(n)$ resulting from a sequence of choices
where $f(0)=1$ and $f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$,
with $\operatorname{OpNoz}_i(x)$ being either $x$ or $remove\_zeros(x)$.
We use `biUnion` for the union of sets.
-/
def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

-- The set of reachable values is always nonempty.
lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ -- Get a guaranteed element m from the previous set
    let prod := (n + 1) * m
    -- We show that `prod` is an element of the current set using `mem_biUnion`.
    -- prod is in {prod, ...} and m is in the previous set, so prod is in the overall union.
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

/--
A374265: Minimized zeroless factorials.
$a(n)$ is the smallest $f(n)$ such that $f(0) = 1$ and for $i > 0$,
$f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$, where $\operatorname{OpNoz}_i$
is a function that either removes zeros or keeps the value unchanged.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

/--
Conjecture from OEIS A374265: Is this sequence bounded?
Formalization of the affirmative claim: The sequence `a` is bounded.
The sequence $a(n)$ is bounded if there exists an upper bound $B$ in $\mathbb{N}$
such that $a(n) \leq B$ for all $n$.
-/
theorem oeis_a374265_conjecture_1_boundedness : ∃ B : ℕ, ∀ n : ℕ, a n ≤ B := by
  sorry



open Nat

def sumD (n : ℕ) : ℕ := if n = 0 then 0 else (n % 10) + sumD (n / 10)
termination_by n

lemma sumD_zero : sumD 0 = 0 := by
  conv => lhs; unfold sumD
  simp

lemma sumD_pos (n : ℕ) (h : n ≠ 0) : sumD n = n % 10 + sumD (n / 10) := by
  conv => lhs; unfold sumD
  simp [h]

lemma sumD_lt_10 (d : ℕ) (hd : d < 10) : sumD d = d := by
  by_cases h0 : d = 0
  · rw [h0, sumD_zero]
  · rw [sumD_pos d h0]
    have : d / 10 = 0 := by omega
    have h2 : d % 10 = d := by omega
    rw [this, sumD_zero, h2]
    exact rfl

lemma pow_ten_pos (i : ℕ) : 10^i > 0 := by
  induction' i with i ih
  · decide
  · have : 10^(i+1) = 10 * 10^i := by ring
    omega

lemma sumD_pow_ten (i : ℕ) : sumD (10^i) = 1 := by
  induction' i with i ih
  · rw [pow_zero, sumD_pos 1 (by decide), sumD_zero]
  · have h1 : 10^(i+1) = 10 * 10^i := by ring
    have h2 : 10^(i+1) ≠ 0 := by
      have := pow_ten_pos (i+1)
      omega
    rw [sumD_pos _ h2]
    have Hmod : 10^(i+1) % 10 = 0 := by
      rw [h1]
      generalize 10^i = T
      omega
    have Hdiv : 10^(i+1) / 10 = 10^i := by
      rw [h1]
      generalize 10^i = T
      omega
    rw [Hmod, Hdiv, ih]

lemma sumD_add_one (X : ℕ) : sumD (X + 1) ≤ sumD X + 1 := by
  induction' X using Nat.strong_induction_on with X ih
  by_cases h : X = 0
  · subst h
    rw [sumD_pos 1 (by decide), sumD_zero]
  · let q := X / 10
    let r := X % 10
    have hX : X = 10 * q + r := (Nat.div_add_mod X 10).symm
    by_cases hr : r = 9
    · have H1 : (X + 1) % 10 = 0 := by omega
      have H2 : (X + 1) / 10 = q + 1 := by omega
      have HX : X ≠ 0 := h
      rw [sumD_pos (X+1) (by omega)]
      rw [sumD_pos X h]
      rw [H1, H2]
      have h_q_lt : q < X := by omega
      have := ih q h_q_lt
      have H3 : X % 10 = r := rfl
      have H4 : X / 10 = q := rfl
      rw [H3, H4, hr]
      omega
    · have H1 : (X + 1) % 10 = r + 1 := by omega
      have H2 : (X + 1) / 10 = q := by omega
      have HX : X ≠ 0 := h
      rw [sumD_pos (X+1) (by omega)]
      rw [sumD_pos X h]
      rw [H1, H2]
      have H3 : X % 10 = r := rfl
      have H4 : X / 10 = q := rfl
      rw [H3, H4]
      omega

lemma sumD_add_pow_ten (X i : ℕ) : sumD (X + 10^i) ≤ sumD X + 1 := by
  induction' X using Nat.strong_induction_on with X ih generalizing i
  cases i with
  | zero =>
    have : 10^0 = 1 := rfl
    rw [this]
    exact sumD_add_one X
  | succ i =>
    have h1 : 10^(i+1) = 10 * 10^i := by ring
    have hX_add : X + 10^(i+1) ≠ 0 := by
      have := pow_ten_pos (i+1)
      omega
    have Hmod : (X + 10^(i+1)) % 10 = X % 10 := by
      rw [h1]
      generalize 10^i = T
      omega
    have Hdiv : (X + 10^(i+1)) / 10 = X / 10 + 10^i := by
      rw [h1]
      generalize 10^i = T
      omega
    rw [sumD_pos _ hX_add]
    rw [Hmod, Hdiv]
    by_cases hX : X = 0
    · subst hX
      rw [sumD_zero]
      have : 0 / 10 = 0 := by decide
      rw [this, zero_add, sumD_pow_ten]
    · rw [sumD_pos X hX]
      have := ih (X / 10) (by omega) i
      omega

lemma sumD_add_mul_pow_ten (X c i : ℕ) : sumD (X + c * 10^i) ≤ sumD X + c := by
  induction' c with c ih
  · simp
  · have H : X + (c + 1) * 10^i = (X + c * 10^i) + 10^i := by ring
    rw [H]
    have h2 := sumD_add_pow_ten (X + c * 10^i) i
    omega

def V_list (l : List ℕ) (k pos : ℕ) : ℕ :=
  match l with
  | [] => 0
  | d :: t => d * 10^(pos % k) + V_list t k (pos + 1)

lemma sumD_V_list (l : List ℕ) (k pos : ℕ) : sumD (V_list l k pos) ≤ l.sum := by
  induction' l with d t ih generalizing pos
  · simp [V_list, sumD_zero]
  · simp [V_list]
    rw [add_comm]
    have := sumD_add_mul_pow_ten (V_list t k (pos + 1)) d (pos % k)
    have ih' := ih (pos + 1)
    omega

lemma V_list_le (l : List ℕ) (k pos : ℕ) (hk : k > 0) (hl : ∀ x ∈ l, x < 10) :
  V_list l k pos ≤ l.sum * 10^(k - 1) := by
  induction' l with d t ih generalizing pos
  · simp [V_list]
  · simp [V_list]
    have hd : d * 10^(pos % k) ≤ d * 10^(k - 1) := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.le_pred_of_lt (Nat.mod_lt _ hk)
    have ht : V_list t k (pos + 1) ≤ t.sum * 10^(k - 1) := ih (pos + 1) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have H : (d + t.sum) * 10^(k - 1) = d * 10^(k - 1) + t.sum * 10^(k - 1) := by ring
    rw [H]
    omega

lemma pow_modEq (pos k : ℕ) (hk : k > 0) : 10^(pos % k) ≡ 10^pos [MOD 10^k - 1] := by
  let q := pos / k
  let r := pos % k
  have hpos : pos = k * q + r := (Nat.div_add_mod pos k).symm
  have h1 : 10^k ≡ 1 [MOD 10^k - 1] := by
    change 10^k % (10^k - 1) = 1 % (10^k - 1)
    have e1 : 10^k % (10^k - 1) = (1 + (10^k - 1)) % (10^k - 1) := by
      have h : 10^k = 1 + (10^k - 1) := by
        have := pow_ten_pos k
        omega
      nth_rw 1 [h]
    rw [e1]
    exact Nat.add_mod_right 1 (10^k - 1)
  have h2 : (10^k)^q ≡ 1^q [MOD 10^k - 1] := Nat.ModEq.pow q h1
  have h3 : (10^k)^q * 10^r ≡ 1^q * 10^r [MOD 10^k - 1] := Nat.ModEq.mul h2 rfl
  have h4 : 10^(k * q) * 10^r ≡ 10^r [MOD 10^k - 1] := by
    have e1 : (10^k)^q = 10^(k * q) := by rw [←pow_mul]
    have e2 : 1^q * 10^r = 10^r := by simp
    rw [e1] at h3
    rw [e2] at h3
    exact h3
  have h5 : 10^(k * q + r) ≡ 10^r [MOD 10^k - 1] := by
    have e3 : 10^(k * q + r) = 10^(k * q) * 10^r := by rw [pow_add]
    rw [e3]
    exact h4
  have h6 : 10^pos ≡ 10^r [MOD 10^k - 1] := by
    rw [hpos]
    exact h5
  exact h6.symm

lemma V_list_modEq (l : List ℕ) (k pos : ℕ) (hk : k > 0) :
  V_list l k pos ≡ Nat.ofDigits 10 l * 10^pos [MOD 10^k - 1] := by
  induction' l with d t ih generalizing pos
  · simp [V_list]
    rfl
  · simp [V_list, Nat.ofDigits]
    have h1 : (d + 10 * Nat.ofDigits 10 t) * 10^pos = d * 10^pos + Nat.ofDigits 10 t * 10^(pos + 1) := by
      have e : 10^(pos + 1) = 10 * 10^pos := by ring
      rw [e]
      ring
    rw [h1]
    have hp := pow_modEq pos k hk
    have hd : d * 10^(pos % k) ≡ d * 10^pos [MOD 10^k - 1] := Nat.ModEq.mul rfl hp
    have ht := ih (pos + 1)
    exact Nat.ModEq.add hd ht

lemma sumD_append (U L k : ℕ) (hL : L < 10^k) : sumD (U * 10^k + L) = sumD U + sumD L := by
  induction' k with k ih generalizing U L
  · have : L = 0 := by omega
    subst this
    simp [sumD_zero]
  · have hL10 : L % 10 < 10 := Nat.mod_lt _ (by decide)
    have eq1 : 10^(k+1) = 10 * 10^k := by ring
    have h_split : U * 10^(k+1) + L = 10 * (U * 10^k) + L := by rw [eq1]; ring
    by_cases h : U * 10^(k+1) + L = 0
    · have hU : U = 0 := by
        have h_mul : U * 10^(k+1) = 0 := by omega
        cases U with
        | zero => rfl
        | succ n =>
          have hM : 10^(k+1) > 0 := pow_ten_pos (k+1)
          generalize 10^(k+1) = M at h_mul hM
          have : (n + 1) * M ≥ 1 := by nlinarith
          omega
      have hL0 : L = 0 := by omega
      subst hU hL0
      simp [sumD_zero]
    · rw [sumD_pos _ h]
      have Hmod : (U * 10^(k+1) + L) % 10 = L % 10 := by
        rw [h_split]
        generalize U * 10^k = A
        omega
      have Hdiv : (U * 10^(k+1) + L) / 10 = U * 10^k + L / 10 := by
        rw [h_split]
        generalize U * 10^k = A
        omega
      rw [Hmod, Hdiv]
      have hL_div : L / 10 < 10^k := by
        have e : 10^(k+1) = 10^k * 10 := by ring
        rw [e] at hL
        omega
      rw [ih U (L / 10) hL_div]
      by_cases hL0 : L = 0
      · subst hL0
        have : 0 / 10 = 0 := by decide
        rw [this, sumD_zero]
        omega
      · rw [sumD_pos L hL0]
        omega

lemma sumD_comp (X k : ℕ) (hX : X < 10^k) : sumD X + sumD (10^k - 1 - X) = 9 * k := by
  induction' k with k ih generalizing X
  · have : X = 0 := by omega
    rw [this, sumD_zero]
    have : 10^0 - 1 - 0 = 0 := rfl
    rw [this, sumD_zero]
  · let d := X / 10^k
    let Y := X % 10^k
    have Hdiv : X = d * 10^k + Y := by
      have e : 10^k * d = d * 10^k := mul_comm _ _
      have H : X = 10^k * d + Y := (Nat.div_add_mod X (10^k)).symm
      rw [e] at H
      exact H
    have hY : Y < 10^k := Nat.mod_lt _ (pow_ten_pos k)
    have hd : d < 10 := by
      have e1 : X < 10 * 10^k := by
        have e : 10 * 10^k = 10^(k+1) := by ring
        rw [e]; exact hX
      have e2 : X = d * 10^k + Y := Hdiv
      have e3 : 10^k > 0 := pow_ten_pos k
      nlinarith
    clear_value d Y
    have e1 : 10^(k+1) - 1 - X = (9 - d) * 10^k + (10^k - 1 - Y) := by
      have e : 10^(k+1) = 10 * 10^k := by ring
      rw [e, Hdiv, Nat.sub_mul]
      have hdT : d * 10^k ≤ 9 * 10^k := by
        apply Nat.mul_le_mul_right
        omega
      generalize d * 10^k = D at hdT ⊢
      have e3 : 10^k > 0 := pow_ten_pos k
      generalize 10^k = T at hY e3 hdT ⊢
      omega
    rw [e1, Hdiv]
    have hT_Y : 10^k - 1 - Y < 10^k := by
      have := pow_ten_pos k
      omega
    rw [sumD_append d Y k hY]
    rw [sumD_append (9 - d) (10^k - 1 - Y) k hT_Y]
    have ih_val := ih Y hY
    have hd_sum : sumD d = d := sumD_lt_10 d hd
    have h9d_sum : sumD (9 - d) = 9 - d := sumD_lt_10 (9 - d) (by omega)
    rw [hd_sum, h9d_sum]
    omega





lemma sum_filter_not_zero (L : List ℕ) : (L.filter (· ≠ 0)).sum = L.sum := by
  induction' L with d t ih
  · rfl
  · by_cases h : d = 0
    · subst h
      have : (0 :: t).filter (· ≠ 0) = t.filter (· ≠ 0) := rfl
      rw [this, ih]
      simp
    · have : decide (d ≠ 0) = true := decide_eq_true h
      have e : (d :: t).filter (· ≠ 0) = d :: t.filter (· ≠ 0) := by
        rw [List.filter_cons, this]
        simp
      rw [e, List.sum_cons, List.sum_cons, ih]

lemma sum_le_ofDigits (L : List ℕ) : L.sum ≤ Nat.ofDigits 10 L := by
  induction' L with d t ih
  · rfl
  · simp [Nat.ofDigits]
    omega

lemma sumD_ofDigits (L : List ℕ) (h : ∀ x ∈ L, x < 10) : sumD (Nat.ofDigits 10 L) = L.sum := by
  induction' L with d t ih
  · rw [Nat.ofDigits, sumD_zero]
    rfl
  · simp [Nat.ofDigits]
    have hd : d < 10 := by
      apply h
      simp
    have ht : ∀ x ∈ t, x < 10 := by
      intro x hx
      apply h
      simp [hx]
    have eq1 : d + 10 * Nat.ofDigits 10 t = Nat.ofDigits 10 t * 10^1 + d := by ring
    rw [eq1]
    have h_lt : d < 10^1 := by omega
    rw [sumD_append (Nat.ofDigits 10 t) d 1 h_lt]
    rw [ih ht]
    have : sumD d = d := sumD_lt_10 d hd
    omega

lemma digits_lt_10 (M : ℕ) : ∀ x ∈ Nat.digits 10 M, x < 10 := by
  induction' M using Nat.strong_induction_on with M ih
  by_cases h : M = 0
  · subst h
    simp
  · intro x hx
    have h_pos := Nat.pos_of_ne_zero h
    rw [Nat.digits_def' (by decide) h_pos] at hx
    simp at hx
    cases hx with
    | inl eq =>
      subst eq
      exact Nat.mod_lt _ (by decide)
    | inr mem =>
      exact ih (M / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)) x mem

lemma sumD_eq_digits_sum (M : ℕ) : sumD M = (Nat.digits 10 M).sum := by
  induction' M using Nat.strong_induction_on with M ih
  by_cases h : M = 0
  · subst h; simp [sumD_zero]
  · have h_pos := Nat.pos_of_ne_zero h
    rw [Nat.digits_def' (by decide) h_pos, sumD_pos _ h]
    simp
    rw [ih (M / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]

lemma sumD_remove_zeros (M : ℕ) : sumD (remove_zeros M) = sumD M := by
  unfold remove_zeros
  have hd_lt := digits_lt_10 M
  have h_filter : ∀ x ∈ (Nat.digits 10 M).filter (· ≠ 0), x < 10 := by
    intro x hx
    have : x ∈ Nat.digits 10 M := List.mem_of_mem_filter hx
    exact hd_lt x this
  rw [sumD_ofDigits _ h_filter]
  rw [sum_filter_not_zero]
  rw [sumD_eq_digits_sum M]

lemma V_list_pos (l : List ℕ) (k pos : ℕ) (h : l.sum > 0) : V_list l k pos > 0 := by
  induction' l with d t ih generalizing pos
  · simp at h
  · simp [V_list]
    by_cases h0 : d = 0
    · subst h0
      simp at h
      have := ih (pos + 1) h
      omega
    · have h_d : d > 0 := Nat.pos_of_ne_zero h0
      have h_pow : 10^(pos % k) > 0 := pow_ten_pos _
      have : d * 10^(pos % k) > 0 := Nat.mul_pos h_d h_pow
      omega

lemma V_list_zero_iff (l : List ℕ) (k pos : ℕ) : V_list l k pos = 0 ↔ l.sum = 0 := by
  constructor
  · intro h
    by_contra h_sum
    have h_pos : l.sum > 0 := by omega
    have := V_list_pos l k pos h_pos
    omega
  · intro h
    induction' l with d t ih generalizing pos
    · simp [V_list]
    · simp at h
      have hd : d = 0 := by omega
      have ht : t.sum = 0 := by omega
      subst hd
      simp [V_list]
      exact ih (pos + 1) ht

lemma sumD_le_self (x : ℕ) : sumD x ≤ x := by
  induction' x using Nat.strong_induction_on with x ih
  by_cases h : x = 0
  · subst h; simp [sumD_zero]
  · rw [sumD_pos _ h]
    have := ih (x / 10) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
    have : x % 10 + x / 10 ≤ x := by
      have e : x = 10 * (x / 10) + x % 10 := (Nat.div_add_mod x 10).symm
      have : x / 10 ≤ 10 * (x / 10) := Nat.le_mul_of_pos_left _ (by decide)
      omega
    omega

lemma sumD_eq_zero_iff (M : ℕ) : sumD M = 0 ↔ M = 0 := by
  induction' M using Nat.strong_induction_on with M ih
  constructor
  · intro h
    by_contra h_neq
    have H : sumD M = M % 10 + sumD (M / 10) := sumD_pos M h_neq
    rw [h] at H
    have H1 : M % 10 = 0 := by omega
    have H2 : sumD (M / 10) = 0 := by omega
    have h_div_lt : M / 10 < M := Nat.div_lt_self (Nat.pos_of_ne_zero h_neq) (by decide)
    have : M / 10 = 0 := (ih (M / 10) h_div_lt).mp H2
    have e : M = 10 * (M / 10) + M % 10 := (Nat.div_add_mod M 10).symm
    rw [this, H1] at e
    omega
  · intro h
    subst h
    exact sumD_zero

lemma extract_y (n : ℕ) (x : ℕ) (hx : x ∈ reachable_zeroless_factorials (n + 1)) :
  ∃ y ∈ reachable_zeroless_factorials n, x = (n + 1) * y ∨ x = remove_zeros ((n + 1) * y) := by
  unfold reachable_zeroless_factorials at hx
  have h1 : ∃ a ∈ reachable_zeroless_factorials n, x ∈ {(n + 1) * a, remove_zeros ((n + 1) * a)} := Finset.mem_biUnion.mp hx
  rcases h1 with ⟨y, hy, h_insert⟩
  use y
  constructor
  · exact hy
  · simp at h_insert
    exact h_insert

lemma reachable_ge_one_strong (n : ℕ) (x : ℕ) (hx : x ∈ reachable_zeroless_factorials n) : x ≥ 1 := by
  induction' n with n ih generalizing x
  · unfold reachable_zeroless_factorials at hx
    simp at hx
    omega
  · rcases extract_y n x hx with ⟨y, hy, h_eq⟩
    have hy1 : y ≥ 1 := ih y hy
    cases h_eq with
    | inl h =>
      subst h
      have h1 : n + 1 > 0 := by omega
      have h2 : y > 0 := by omega
      have := Nat.mul_pos h1 h2
      omega
    | inr h =>
      subst h
      have h1 : n + 1 > 0 := by omega
      have h2 : y > 0 := by omega
      have M_pos : (n + 1) * y > 0 := Nat.mul_pos h1 h2
      have h_sumD : sumD ((n + 1) * y) ≠ 0 := by
        intro h0
        have := sumD_eq_zero_iff ((n + 1) * y)
        have H := this.mp h0
        omega
      have h_sumD_rz : sumD (remove_zeros ((n + 1) * y)) ≠ 0 := by
        rw [sumD_remove_zeros]
        exact h_sumD
      by_contra h_contra
      have : remove_zeros ((n + 1) * y) = 0 := by omega
      rw [this] at h_sumD_rz
      rw [sumD_zero] at h_sumD_rz
      exact h_sumD_rz rfl

lemma ten_pow_k_ge (B : ℕ) : 10^(B + 2) ≥ 100 := by
  have e : 10^(B + 2) = 10^B * 100 := by ring
  have h_pos : 10^B > 0 := pow_ten_pos B
  nlinarith

lemma B_lt_pow (B : ℕ) : B < 10^(B+2) - 1 := by
  induction' B with B ih
  · decide
  · have e : 10^(B+1+2) = 10 * 10^(B+2) := by ring
    rw [e]
    have : 10^(B+2) ≥ 100 := ten_pow_k_ge B
    generalize 10^(B+2) = X at this ih ⊢
    omega

theorem oeis_a374265_conjecture_1_boundedness.disproof : ¬ (type_of% @oeis_a374265_conjecture_1_boundedness) := by
  intro ⟨B, hB⟩
  let k := B + 2
  let n := 10^k - 1
  have H_a := hB n
  have H_nonempty := reachable_nonempty n
  have hx_in : a n ∈ reachable_zeroless_factorials n := Finset.min'_mem _ H_nonempty
  let x := a n
  have hx_le_B : x ≤ B := H_a

  have hk_pos : k > 0 := by omega
  have hn_pos : n > 0 := by
    have : 10^k ≥ 100 := ten_pow_k_ge B
    omega
  
  have h_n_eq : n = (n - 1) + 1 := by omega
  have hx_in2 : x ∈ reachable_zeroless_factorials ((n - 1) + 1) := by
    have e : (n - 1) + 1 = n := by omega
    rw [e]
    exact hx_in
  
  rcases extract_y (n - 1) x hx_in2 with ⟨y, hy, h_eq⟩
  have hy_ge : y ≥ 1 := reachable_ge_one_strong (n - 1) y hy
  let M := n * y
  have hM_eq : M = n * y := rfl
  have hM_pos : M > 0 := by
    have : n ≥ 1 := by omega
    have : y ≥ 1 := hy_ge
    nlinarith
  have hx_M : x = M ∨ x = remove_zeros M := by
    have e : (n - 1) + 1 = n := by omega
    rw [e] at h_eq
    exact h_eq
  
  have h_sumD_x : sumD x = sumD M := by
    cases hx_M with
    | inl h => rw [h]
    | inr h => rw [h, sumD_remove_zeros]

  have hM_mod : M % (10^k - 1) = 0 := by
    rw [hM_eq]
    have : n = 10^k - 1 := rfl
    rw [this]
    exact Nat.mul_mod_right _ _

  have h_sumD_x_le : sumD M ≤ B := by
    have : sumD x ≤ x := sumD_le_self x
    omega

  let L := Nat.digits 10 M
  have hL_sum : L.sum = sumD M := (sumD_eq_digits_sum M).symm
  have hL_lt : ∀ d ∈ L, d < 10 := digits_lt_10 M

  let V := V_list L k 0
  have hV_mod : V ≡ Nat.ofDigits 10 L * 10^0 [MOD 10^k - 1] := V_list_modEq L k 0 hk_pos
  have h_ofD : Nat.ofDigits 10 L = M := Nat.ofDigits_digits 10 M
  have hV_mod2 : V ≡ M [MOD 10^k - 1] := by
    have e : Nat.ofDigits 10 L * 10^0 = M := by rw [h_ofD]; ring
    rw [e] at hV_mod
    exact hV_mod
  
  have hM_mod2 : M ≡ 0 [MOD 10^k - 1] := by
    exact hM_mod
  have hV_mod3 : V ≡ 0 [MOD 10^k - 1] := Nat.ModEq.trans hV_mod2 hM_mod2

  have hV_le : V ≤ L.sum * 10^(k - 1) := V_list_le L k 0 hk_pos hL_lt
  have hL_sum_le : L.sum ≤ B := by omega
  have hV_le_B : V ≤ B * 10^(k - 1) := by
    have : L.sum * 10^(k - 1) ≤ B * 10^(k - 1) := Nat.mul_le_mul_right _ hL_sum_le
    omega

  have hL_sum_pos : L.sum > 0 := by
    rw [hL_sum]
    have : sumD M ≠ 0 := by
      intro h
      have := (sumD_eq_zero_iff M).mp h
      omega
    omega
  have hV_pos : V > 0 := V_list_pos L k 0 hL_sum_pos

  have hV_div : (10^k - 1) ∣ V := Nat.dvd_of_mod_eq_zero hV_mod3
  rcases hV_div with ⟨C, hC⟩
  have hC_pos : C > 0 := by
    by_contra h
    have : C = 0 := by omega
    subst this
    simp at hC
    omega
  
  have hV_eq : V = C * (10^k - 1) := by rw [hC, mul_comm]
  
  have hC_lt : C < 10^k := by
    by_contra h
    have h1 : C ≥ 10^k := by omega
    have h2 : V ≥ 10^k * (10^k - 1) := by
      rw [hV_eq]
      exact Nat.mul_le_mul_right _ h1
    have e_pos : 10^(k - 1) > 0 := pow_ten_pos (k - 1)
    have hB_lt : B < 10^k - 1 := B_lt_pow B
    have : 10^k = 10 * 10^(k - 1) := by
      have : k = (k - 1) + 1 := by omega
      nth_rw 1 [this]
      ring
    nlinarith

  have h_sumD_V : sumD V ≤ L.sum := sumD_V_list L k 0
  have h_sumD_V_le_B : sumD V ≤ B := by omega

  have hV_split : V = (C - 1) * 10^k + (10^k - C) := by
    have : C * 10^k = C * 10^k := rfl
    have e1 : C * (10^k - 1) = C * 10^k - C := by
      have h := Nat.mul_sub_left_distrib C (10^k) 1
      rw [Nat.mul_one] at h
      exact h
    rw [e1] at hV_eq
    have e2 : C * 10^k - C = (C - 1) * 10^k + (10^k - C) := by
      have h1 : C * 10^k = (C - 1) * 10^k + 10^k := by
        have : C = (C - 1) + 1 := by omega
        nth_rw 1 [this]
        ring
      rw [h1]
      have : 10^k ≥ C := by omega
      omega
    rw [e2] at hV_eq
    exact hV_eq

  have h_sumD_split : sumD V = sumD (C - 1) + sumD (10^k - C) := by
    rw [hV_split]
    have : 10^k - C < 10^k := by omega
    exact sumD_append (C - 1) (10^k - C) k this

  have h_sumD_9k : sumD (C - 1) + sumD (10^k - C) = 9 * k := by
    have : 10^k - C = 10^k - 1 - (C - 1) := by omega
    rw [this]
    have : C - 1 < 10^k := by omega
    exact sumD_comp (C - 1) k this

  have h_9k_le_B : 9 * k ≤ B := by omega
  have h_cont : 9 * k > B := by
    have : k = B + 2 := rfl
    omega

  omega
