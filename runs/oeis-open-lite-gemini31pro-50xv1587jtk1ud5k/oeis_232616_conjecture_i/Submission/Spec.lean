import FormalConjectures.Util.ProblemImports
open Nat Finset Set ZMod Classical

set_option linter.unusedVariables false
set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

lemma nth_prime_eq_of_count (N n : ℕ) (h1 : Nat.primeCounting' N = n) (h2 : Nat.primeCounting' (N + 1) = n + 1) :
  Nat.nth Nat.Prime n = N := by
  have h3 : Nat.primeCounting' (N + 1) = Nat.primeCounting' N + if Nat.Prime N then 1 else 0 := Nat.count_succ _ N
  have h_prime : Nat.Prime N := by
    rw [h1, h2] at h3
    split_ifs at h3 with hP
    · exact hP
    · omega
  have hn_eq : Nat.primeCounting' (Nat.nth Nat.Prime n) = n := Nat.primeCounting'_nth_eq n
  apply le_antisymm
  · have h_lt : ¬ (N < Nat.nth Nat.Prime n) := by
      intro hlt
      have : Nat.primeCounting' (N + 1) ≤ Nat.primeCounting' (Nat.nth Nat.Prime n) := Nat.count_monotone Nat.Prime hlt
      rw [h2, hn_eq] at this
      omega
    omega
  · have h_lt : ¬ (Nat.nth Nat.Prime n < N) := by
      intro hlt
      have : Nat.primeCounting' (Nat.nth Nat.Prime n + 1) ≤ Nat.primeCounting' N := Nat.count_monotone Nat.Prime hlt
      have h4 : Nat.primeCounting' (Nat.nth Nat.Prime n + 1) = Nat.primeCounting' (Nat.nth Nat.Prime n) + 1 := by
        change Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = Nat.count Nat.Prime (Nat.nth Nat.Prime n) + 1
        rw [Nat.count_succ, if_pos (Nat.prime_nth_prime n)]
      rw [h1] at this
      rw [h4] at this
      rw [hn_eq] at this
      omega
    omega

def check_missing_iter (n missing : ℕ) [NeZero n] : ℕ → ZMod n → ℕ → Bool
  | 0, _, _ => true
  | iters + 1, p2, k =>
    if p2 - (k : ZMod n) == (missing : ZMod n) then false
    else check_missing_iter n missing iters (p2 * 2) (k + 1)

lemma loop_correct (n missing : ℕ) [NeZero n] (iters : ℕ) :
  ∀ (k : ℕ) (p2 : ZMod n),
    p2 = 2^k →
    check_missing_iter n missing iters p2 k = true →
    ∀ i, k ≤ i → i < k + iters → (2 : ZMod n)^i - (i : ZMod n) ≠ (missing : ZMod n) := by
  induction iters with
  | zero =>
    intro k p2 hp2 htrue i hk hi
    omega
  | succ iters ih =>
    intro k p2 hp2 htrue i hk hi
    have hC : p2 - (k : ZMod n) ≠ (missing : ZMod n) := by
      intro h
      have h_eq : (p2 - (k : ZMod n) == (missing : ZMod n)) = true := beq_iff_eq.mpr h
      unfold check_missing_iter at htrue
      rw [h_eq] at htrue
      have h_false : false = true := htrue
      contradiction
    have htrue_next : check_missing_iter n missing iters (p2 * 2) (k + 1) = true := by
      unfold check_missing_iter at htrue
      revert htrue
      generalize (p2 - (k : ZMod n) == (missing : ZMod n)) = b
      cases b
      · intro h; exact h
      · intro h
        have h_false : false = true := h
        contradiction
    have hi_cases : i = k ∨ k + 1 ≤ i := by omega
    rcases hi_cases with rfl | hik
    · rw [← hp2]
      exact hC
    · apply ih (k + 1) (p2 * 2) _ htrue_next i hik (by omega)
      rw [hp2, pow_succ, mul_comm]

lemma k_le_two_pow (k : ℕ) : k ≤ 2^k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k' ih =>
    have h1 : 1 ≤ 2^k' := by
      clear ih
      induction k' with
      | zero => decide
      | succ k'' ih2 =>
        calc
          1 ≤ 2^k'' := ih2
          _ ≤ 2^k'' * 2 := by omega
          _ = 2^(k''+1) := by rw [pow_succ]
    calc
      k' + 1 ≤ 2^k' + 1 := by omega
      _ ≤ 2^k' + 2^k' := by omega
      _ = 2^k' * 2 := by ring
      _ = 2^(k'+1) := by rw [pow_succ]

def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

lemma not_prop_of_check_missing (n m missing : ℕ) [NeZero n]
  (hm : (missing : ZMod n) ∈ (univ : Finset (ZMod n))) :
  check_missing_iter n missing m 2 1 = true →
  ¬ A232616_prop n m := by
  intro h hprop
  have h_all := loop_correct n missing m 1 2 (by exact (pow_one (2 : ZMod n)).symm) h
  unfold A232616_prop at hprop
  have h_miss_in : (missing : ZMod n) ∈ (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := by
    rw [← hprop]
    exact hm
  rw [Finset.mem_image] at h_miss_in
  rcases h_miss_in with ⟨k, hk, hk_eq⟩
  rw [Finset.mem_Icc] at hk
  have h_cast : (Nat.cast (2^k - k) : ZMod n) = (2 : ZMod n)^k - (k : ZMod n) := by
    have h_ge : k ≤ 2^k := k_le_two_pow k
    rw [Nat.cast_sub h_ge]
    push_cast
    rfl
  rw [h_cast] at hk_eq
  have h_not_eq := h_all k hk.1 (by omega)
  exact h_not_eq hk_eq

def find_ks (n m : ℕ) : Array ℕ :=
  let rec loop (iters : ℕ) (k : ℕ) (p2 : ℕ) (arr : Array ℕ) : Array ℕ :=
    match iters with
    | 0 => arr
    | iters' + 1 =>
      let val := (p2 + n - (k % n)) % n
      if arr[val]! == 0 then
        loop iters' (k + 1) ((p2 * 2) % n) (arr.set! val k)
      else
        loop iters' (k + 1) ((p2 * 2) % n) arr
  loop m 1 (2 % n) (List.replicate n 0).toArray

def check_A_loop (n m : ℕ) [NeZero n] (a : Array ℕ) : ℕ → Bool
  | 0 => true
  | x + 1 =>
    if hc : (1 ≤ a[x]!) && (a[x]! ≤ m) && (((2 : ZMod n)^(a[x]!) - ((a[x]!) : ZMod n)) == (x : ZMod n)) then check_A_loop n m a x
    else false

def check_A (n m : ℕ) [NeZero n] : Bool :=
  check_A_loop n m (find_ks n m) n

lemma check_A_loop_correct (n m : ℕ) [NeZero n] (a : Array ℕ) (x_bound : ℕ) :
  check_A_loop n m a x_bound = true →
  ∀ x < x_bound, ∃ k ∈ Finset.Icc 1 m, (2 : ZMod n)^k - (k : ZMod n) = (x : ZMod n) := by
  induction x_bound with
  | zero =>
    intro h x hx
    omega
  | succ x_bd ih =>
    intro h
    unfold check_A_loop at h
    revert h
    generalize h_cond : ((1 ≤ a[x_bd]!) && (a[x_bd]! ≤ m) && (((2 : ZMod n) ^ a[x_bd]! - ↑a[x_bd]!) == ↑x_bd)) = b
    cases b
    · intro h
      revert h
      change false = true → _
      intro h_false
      contradiction
    · intro h x hx
      have hx_cases : x = x_bd ∨ x < x_bd := by omega
      rcases hx_cases with rfl | hx_lt
      · use a[x]!
        constructor
        · rw [Finset.mem_Icc]
          have h1 := Bool.and_eq_true _ _ |>.mp h_cond
          have h2 := Bool.and_eq_true _ _ |>.mp h1.1
          exact ⟨of_decide_eq_true h2.1, of_decide_eq_true h2.2⟩
        · have h1 := Bool.and_eq_true _ _ |>.mp h_cond
          exact beq_iff_eq.mp h1.2
      · exact ih h x hx_lt

lemma prop_of_check_A (n m : ℕ) [NeZero n] (a : Array ℕ) :
  check_A_loop n m a n = true →
  A232616_prop n m := by
  intro h
  have h_all := check_A_loop_correct n m a n h
  unfold A232616_prop
  apply Finset.ext
  intro x
  constructor
  · intro _
    have hx : x.val < n := ZMod.val_lt x
    rcases h_all x.val hx with ⟨k, hk, hk_eq⟩
    rw [Finset.mem_image]
    use k
    constructor
    · exact hk
    · have h_cast : (Nat.cast (2^k - k) : ZMod n) = (2 : ZMod n)^k - (k : ZMod n) := by
        have h_ge : k ≤ 2^k := k_le_two_pow k
        rw [Nat.cast_sub h_ge]
        push_cast
        rfl
      rw [h_cast, hk_eq]
      exact ZMod.natCast_zmod_val x
  · intro _
    exact Finset.mem_univ _

lemma prop_mono (n m1 m2 : ℕ) [NeZero n] (h_le : m1 ≤ m2) :
  A232616_prop n m1 → A232616_prop n m2 := by
  intro h1
  unfold A232616_prop at *
  rw [Finset.ext_iff]
  intro x
  constructor
  · intro _
    have h_univ : x ∈ (Finset.univ : Finset (ZMod n)) := Finset.mem_univ x
    have hx1 : x ∈ (Finset.Icc 1 m1).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n) := by rw [← h1]; exact h_univ
    rw [Finset.mem_image] at hx1 ⊢
    rcases hx1 with ⟨k, hk, hk_eq⟩
    use k
    constructor
    · rw [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, by omega⟩
    · exact hk_eq
  · intro _
    exact Finset.mem_univ x

lemma pi1 : Nat.primeCounting' 8165753 = 550171 := by native_decide
lemma pi2 : Nat.primeCounting' 8165754 = 550172 := by native_decide
lemma eval_missing : check_missing_iter 550172 13573 16331503 2 1 = true := by native_decide
lemma eval_A : check_A_loop 550172 17135927 (find_ks 550172 17135927) 550172 = true := by native_decide

noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have hn : NeZero n := NeZero.mk h
    sInf { m : ℕ | A232616_prop n m }

theorem oeis_232616_conjecture_i (n : ℕ) (hn : 0 < n) :
    A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) := by
  sorry

theorem oeis_232616_conjecture_i.disproof : ¬ (type_of% @oeis_232616_conjecture_i) := by
  intro h
  have h_spec := h 550172 (by decide)
  have h_prime : Nat.nth Nat.Prime 550171 = 8165753 := nth_prime_eq_of_count 8165753 550171 pi1 pi2
  rw [h_prime] at h_spec
  have hA_def : A232616 550172 = sInf {m | A232616_prop 550172 m} := by
    unfold A232616
    have h_ne : 550172 = 0 → False := by decide
    rw [dif_neg h_ne]
  rw [hA_def] at h_spec
  have hS : Set.Nonempty {m | A232616_prop 550172 m} := ⟨17135927, prop_of_check_A 550172 17135927 (find_ks 550172 17135927) eval_A⟩
  have h_inf := Nat.sInf_mem hS
  have h_bound : sInf {m | A232616_prop 550172 m} < 16331504 := by omega
  have h_prop := prop_mono 550172 (sInf {m | A232616_prop 550172 m}) 16331503 (by omega) h_inf
  have h_not_prop := not_prop_of_check_missing 550172 16331503 13573 (Finset.mem_univ _) eval_missing
  exact h_not_prop h_prop
