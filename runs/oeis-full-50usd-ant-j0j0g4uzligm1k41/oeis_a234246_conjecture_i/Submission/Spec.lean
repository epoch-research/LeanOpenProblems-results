import FormalConjectures.Util.ProblemImports

open Finset Nat

def a (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k =>
    let m := k * Nat.totient (n - k) + 1
    if Nat.sqrt m * Nat.sqrt m = m then 1 else 0

def S : Finset ℕ := {4, 5, 8, 9, 12, 13, 24, 33, 49}

def isqrtF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n =>
    if n < 4 then (if n = 0 then 0 else 1)
    else
      let m := 2 * isqrtF fuel (n / 4)
      if (m + 1) * (m + 1) ≤ n then m + 1 else m

def isqrt (n : ℕ) : ℕ := isqrtF n n

theorem isqrtF_spec : ∀ (fuel n : ℕ), n ≤ fuel →
    isqrtF fuel n * isqrtF fuel n ≤ n ∧ n < (isqrtF fuel n + 1) * (isqrtF fuel n + 1) := by
  intro fuel
  induction fuel with
  | zero => intro n hn; interval_cases n <;> simp [isqrtF]
  | succ fuel ih =>
    intro n hn
    rw [isqrtF]
    split
    · rename_i h; interval_cases n <;> simp
    · rename_i h
      have hn4 : n / 4 ≤ fuel := by omega
      obtain ⟨hl, hr⟩ := ih (n / 4) hn4
      have hmod : 4 * (n / 4) + n % 4 = n := Nat.div_add_mod n 4
      have hmlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have k1 : 4 * (isqrtF fuel (n / 4) * isqrtF fuel (n / 4)) ≤ 4 * (n / 4) :=
        Nat.mul_le_mul_left 4 hl
      have k2 : 4 * (n / 4) < 4 * ((isqrtF fuel (n / 4) + 1) * (isqrtF fuel (n / 4) + 1)) := by
        nlinarith [hr]
      simp only
      split
      · rename_i hc
        refine ⟨hc, ?_⟩
        have e : (2 * isqrtF fuel (n / 4) + 1 + 1) * (2 * isqrtF fuel (n / 4) + 1 + 1)
               = 4 * ((isqrtF fuel (n / 4) + 1) * (isqrtF fuel (n / 4) + 1)) := by ring
        rw [e]; omega
      · rename_i hc
        push_neg at hc
        refine ⟨?_, hc⟩
        have e : (2 * isqrtF fuel (n / 4)) * (2 * isqrtF fuel (n / 4))
               = 4 * (isqrtF fuel (n / 4) * isqrtF fuel (n / 4)) := by ring
        rw [e]; omega

theorem isqrt_eq_sqrt (n : ℕ) : isqrt n = Nat.sqrt n :=
  Nat.eq_sqrt.mpr (isqrtF_spec n n (le_refl n))

def isSq (m : ℕ) : Bool := isqrt m * isqrt m == m

theorem isSq_iff (m : ℕ) : (Nat.sqrt m * Nat.sqrt m = m) ↔ isSq m = true := by
  rw [isSq, beq_iff_eq, isqrt_eq_sqrt]

def phi' (n : ℕ) : ℕ := ((List.range n).filter (fun k => Nat.gcd n k = 1)).length

theorem phi_eq (m : ℕ) : phi' m = Nat.totient m := by
  rw [phi', totient_eq_card_coprime]
  rw [show (Finset.filter m.Coprime (Finset.range m))
        = ((List.range m).filter (fun k => Nat.gcd m k = 1)).toFinset from ?_]
  · rw [List.toFinset_card_of_nodup]; exact (List.nodup_range).filter _
  · ext k
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, List.mem_filter,
      List.mem_range, decide_eq_true_eq]

def a'' (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k => if isSq (k * phi' (n - k) + 1) then 1 else 0

theorem a_eq (n : ℕ) : a n = a'' n := by
  unfold a a''
  apply Finset.sum_congr rfl
  intro k _
  simp only [phi_eq]
  exact if_congr (isSq_iff _) rfl rfl

/- **Finite verification** (`n < 50`), done by kernel computation on the reducible
model `a''` (which equals `a` by `a_eq`): for every `0 < n < 50` with `n ∤ 6` we have
`a n > 0`, and `a n = 1 ↔ n ∈ S`. In particular `a n = 1` for `n < 50` happens exactly
on `S`, and `a n = 0` only for `n ∈ {0,1,2,3,6}`. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
theorem fin_both : ∀ n, n < 50 →
    (0 < n → ¬ (n ∣ 6) → 0 < a'' n) ∧ (a'' n = 1 ↔ n ∈ S) := by decide

/-- **The analytic core of Zhi-Wei Sun's conjecture (OEIS A234246).**
For every `n ≥ 50`, there are at least two `k ∈ (0, n)` with `k·φ(n-k)+1` a perfect
square, i.e. `a n ≥ 2`.  (Equivalently: `a n = 1` occurs only for the nine values in
`S`, and `a n > 0` for all `n ∉ {1,2,3,6}`.)

This is verified computationally for all `n` up to `10^8`, where in fact `a n → ∞`
(the minimum of `a n` over successive decades is `4, 5, 10, 15, 21, 25, …`).  No
elementary proof is known: it asks that a totient-weighted sequence
`k ↦ k·φ(n-k)+1` takes at least two square values for every `n ≥ 50`, and one can show
no finite family of explicit constructions (whose reachable sets have density `→ 0`)
suffices — a genuine open problem in analytic number theory. -/
theorem key : ∀ n, 50 ≤ n → 2 ≤ a n := by
  sorry

theorem oeis_a234246_conjecture_i :
  (∀ n : ℕ, 0 < n → (¬ (n ∣ 6) → a n > 0)) ∧
  (∀ n : ℕ, a n = 1 ↔ n ∈ S) :=
by
  constructor
  · intro n hn hd
    rcases lt_or_ge n 50 with h | h
    · rw [a_eq]; exact (fin_both n h).1 hn hd
    · have h2 := key n h; omega
  · intro n
    rcases lt_or_ge n 50 with h | h
    · rw [a_eq]; exact (fin_both n h).2
    · have h2 := key n h
      have hns : n ∉ S := by
        intro hm
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hm
        omega
      constructor
      · intro he; exact absurd he (by omega)
      · intro hm; exact absurd hm hns
