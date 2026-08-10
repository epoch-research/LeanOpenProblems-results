import FormalConjectures.Util.ProblemImports

open Nat Int

/-- The rule function for Rule 167. Inputs must be 0 or 1. -/
def ca_rule_167 (c_L c_C c_R : ℕ) : ℕ :=
  let R : ℕ := 167
  let index : ℕ := 4 * c_L + 2 * c_C + c_R
  -- Rule 167 is determined by the index-th bit of R.
  (R / (2 ^ index)) % 2

/--
The state of the Rule 167 elementary cellular automaton at time $t$ and position $x$.
The initial condition is a single ON cell at $x=0$.
$C(t, x)$ is structurally recursive on $t$.
-/
def ca_state (t : ℕ) (x : ℤ) : ℕ :=
  match t with
  | 0 => if x = 0 then 1 else 0
  | t' + 1 =>
    let C_t' (y : ℤ) := ca_state t' y
    ca_rule_167 (C_t' (x - 1)) (C_t' x) (C_t' (x + 1))

/-- The sequence of bits forming the middle column of the CA pattern, $C_{t, 0}$. -/
def middle_column_bit (t : ℕ) : ℕ := ca_state t 0

/--
A267581: Decimal representation of the middle column of the "Rule 167" elementary cellular automaton
starting with a single ON (black) cell.
The term $a(n)$ is the decimal value of the binary number $C_{0, 0} C_{1, 0} \dots C_{n, 0}$,
where $C_{i, 0}$ is the state of the center cell at time $i$.
$$a(n) = \sum_{k=0}^n C_{k, 0} \cdot 2^{n-k}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (middle_column_bit k) * (2^ (n - k))

/-- The floor term in the conjectured recurrence relation for A267581.
This term, $\lfloor (1/2)^{(2^{n+1} \bmod n)} \rfloor$, simplifies to 1 if $(2^{n+1} \bmod n) = 0$
(i.e., $n \mid 2^{n+1}$), and 0 otherwise.
Since the recurrence is only stated for $n \ge 2$, the $n=0$ case is irrelevant to the conjecture. -/
def oeis_floor_term (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if (2 ^ (n + 1)) % n = 0 then 1 else 0

/-- Predicate: cell (t,x) is OFF (value 0), for t ≥ 1. -/
def zeroPred (t : ℕ) (x : ℤ) : Prop :=
  ∃ v : ℕ, x = (t : ℤ) - 2 * v ∧ Odd ((t - 1).choose v)

-- evaluation lemma
lemma zeroPred_eval (t : ℕ) (x : ℤ) (v : ℕ) (hx : x = (t : ℤ) - 2 * v) :
    zeroPred t x ↔ Odd ((t - 1).choose v) := by
  constructor
  · rintro ⟨v', hx', ho'⟩
    have : (v : ℤ) = v' := by
      have := hx.symm.trans hx'
      omega
    have hvv : v = v' := by exact_mod_cast this
    rw [hvv]; exact ho'
  · intro ho; exact ⟨v, hx, ho⟩

lemma zeroPred_none (t : ℕ) (x : ℤ) (h : ¬ ∃ v : ℕ, x = (t : ℤ) - 2 * v) :
    ¬ zeroPred t x := by
  rintro ⟨v, hx, _⟩; exact h ⟨v, hx⟩


-- core combinatorial step relating one row to the next via the local rule
open Classical in
lemma step (s : ℕ) (hs : 1 ≤ s) (x : ℤ) :
    (if zeroPred (s + 1) x then (0 : ℕ) else 1) =
      ca_rule_167 (if zeroPred s (x - 1) then 0 else 1)
        (if zeroPred s x then 0 else 1)
        (if zeroPred s (x + 1) then 0 else 1) := by
  by_cases hex : ∃ v0 : ℕ, x = (s + 1 : ℤ) - 2 * v0
  · obtain ⟨v0, hv0⟩ := hex
    -- middle: zeroPred s x is false (wrong parity)
    have hmid : ¬ zeroPred s x := by
      apply zeroPred_none
      rintro ⟨v, hv⟩
      omega
    -- left neighbor x-1 uses index v0
    have hleft : zeroPred s (x - 1) ↔ Odd ((s - 1).choose v0) := by
      apply zeroPred_eval
      push_cast at hv0 ⊢; omega
    -- the cell (s+1, x)
    have hcell : zeroPred (s + 1) x ↔ Odd ((s).choose v0) := by
      have := zeroPred_eval (s + 1) x v0 (by push_cast at hv0 ⊢; omega)
      simpa using this
    rw [if_neg hmid]
    by_cases hv0pos : 1 ≤ v0
    · -- general case, right neighbor uses index v0 - 1
      have hright : zeroPred s (x + 1) ↔ Odd ((s - 1).choose (v0 - 1)) := by
        apply zeroPred_eval
        have : ((v0 - 1 : ℕ) : ℤ) = (v0 : ℤ) - 1 := by omega
        push_cast at hv0 ⊢
        rw [this]; omega
      -- Pascal: choose s v0 = choose (s-1) (v0-1) + choose (s-1) v0
      have hpascal : (s).choose v0 = (s - 1).choose (v0 - 1) + (s - 1).choose v0 := by
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        obtain ⟨w, rfl⟩ : ∃ w, v0 = w + 1 := ⟨v0 - 1, by omega⟩
        simp [Nat.choose_succ_succ]
      rw [hcell, hleft, hright, hpascal]
      by_cases ha : Odd ((s - 1).choose (v0 - 1)) <;>
        by_cases hb : Odd ((s - 1).choose v0)
      · have : ¬ Odd ((s-1).choose (v0-1) + (s-1).choose v0) := by
          simp [Nat.not_odd_iff_even]; exact ha.add_odd hb
        rw [if_neg this, if_pos hb, if_pos ha]; decide
      · have : Odd ((s-1).choose (v0-1) + (s-1).choose v0) := by
          rw [Nat.not_odd_iff_even] at hb; exact ha.add_even hb
        rw [if_pos this, if_neg hb, if_pos ha]; decide
      · have : Odd ((s-1).choose (v0-1) + (s-1).choose v0) := by
          rw [Nat.not_odd_iff_even] at ha; exact ha.add_odd hb
        rw [if_pos this, if_pos hb, if_neg ha]; decide
      · have : ¬ Odd ((s-1).choose (v0-1) + (s-1).choose v0) := by
          rw [Nat.not_odd_iff_even] at ha hb
          simp [Nat.not_odd_iff_even]; exact ha.add hb
        rw [if_neg this, if_neg hb, if_neg ha]; decide
    · -- v0 = 0
      have hv00 : v0 = 0 := by omega
      subst hv00
      have hright : ¬ zeroPred s (x + 1) := by
        apply zeroPred_none
        rintro ⟨v, hv⟩
        push_cast at hv0
        omega
      rw [if_neg hright]
      have : (s).choose 0 = 1 := Nat.choose_zero_right _
      have h2 : (s - 1).choose 0 = 1 := Nat.choose_zero_right _
      rw [hcell, hleft, this, h2, if_pos odd_one]
      decide
  · -- no even-offset solution at (s+1,x); LHS = 1, and left/right neighbours false
    have hL : ¬ zeroPred (s + 1) x := zeroPred_none _ _ hex
    have hleft : ¬ zeroPred s (x - 1) := by
      apply zeroPred_none
      rintro ⟨v, hv⟩
      exact hex ⟨v, by push_cast at hv ⊢; omega⟩
    have hright : ¬ zeroPred s (x + 1) := by
      apply zeroPred_none
      rintro ⟨v, hv⟩
      exact hex ⟨v + 1, by push_cast at hv ⊢; omega⟩
    rw [if_neg hL, if_neg hleft, if_neg hright]
    by_cases hm : zeroPred s x
    · rw [if_pos hm]; decide
    · rw [if_neg hm]; decide

lemma zeroPred_one (x : ℤ) : zeroPred 1 x ↔ x = 1 := by
  constructor
  · rintro ⟨v, hx, ho⟩
    obtain _|v := v
    · simpa using hx
    · simp [Nat.choose_zero_succ] at ho
  · intro hx; exact ⟨0, by simp [hx], by simp⟩

lemma ca0 (y : ℤ) : ca_state 0 y = if y = 0 then 1 else 0 := rfl

lemma ca_succ (t : ℕ) (x : ℤ) :
    ca_state (t + 1) x =
      ca_rule_167 (ca_state t (x - 1)) (ca_state t x) (ca_state t (x + 1)) := rfl

-- grid lemma: for t ≥ 1, the cell value is 0 iff zeroPred t x
open Classical in
lemma aux : ∀ t x, ca_state (t + 1) x = if zeroPred (t + 1) x then 0 else 1 := by
  intro t
  induction t with
  | zero =>
    intro x
    rw [ca_succ, ca0, ca0, ca0, zeroPred_one]
    by_cases h1 : x = 1
    · rw [if_pos (by omega : x - 1 = 0), if_neg (by omega : ¬ x = 0),
        if_neg (by omega : ¬ x + 1 = 0), if_pos h1]; decide
    · by_cases h0 : x = 0
      · rw [if_neg (by omega : ¬ x - 1 = 0), if_pos h0,
          if_neg (by omega : ¬ x + 1 = 0), if_neg h1]; decide
      · by_cases hm1 : x = -1
        · rw [if_neg (by omega : ¬ x - 1 = 0), if_neg h0,
            if_pos (by omega : x + 1 = 0), if_neg h1]; decide
        · rw [if_neg (by omega : ¬ x - 1 = 0), if_neg h0,
            if_neg (by omega : ¬ x + 1 = 0), if_neg h1]; decide
  | succ t IH =>
    intro x
    have key := step (t + 1) (by omega) x
    rw [ca_succ, IH (x - 1), IH x, IH (x + 1)]
    exact key.symm

open Classical in
lemma gridlem (t : ℕ) (x : ℤ) (ht : 1 ≤ t) :
    ca_state t x = if zeroPred t x then 0 else 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  exact aux m x

lemma centralBinom_odd_iff (u : ℕ) : Odd (Nat.choose (2*u) u) ↔ u = 0 := by
  constructor
  · intro h
    rcases u with _ | w
    · rfl
    · exfalso
      have hsymm : Nat.choose (2*w+1) w = Nat.choose (2*w+1) (w+1) := by
        have := Nat.choose_symm (n := 2*w+1) (k := w+1) (by omega)
        simpa [show 2*w+1 - (w+1) = w by omega] using this
      have he : Nat.choose (2*(w+1)) (w+1) = 2 * Nat.choose (2*w+1) (w+1) := by
        have h2 : 2*(w+1) = (2*w+1)+1 := by ring
        rw [h2, Nat.choose_succ_succ, hsymm]; ring
      rw [he] at h
      exact (Nat.not_odd_iff_even.2 ⟨_, by ring⟩) h
  · rintro rfl; simp

lemma pow2_choose : ∀ v, 1 ≤ v → (Odd (Nat.choose (2*v-1) v) ↔ ∃ k, v = 2^k) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro v
  induction v using Nat.strong_induction_on with
  | _ v IH =>
  intro hv
  have hpar : ∀ a b : ℕ, a ≡ b [MOD 2] → (Odd a ↔ Odd b) := by
    intro a b h
    rw [Nat.odd_iff, Nat.odd_iff, h]
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := 2*v-1) (k := v)
  have hmod : (2*v-1) % 2 = 1 := by omega
  have hdiv : (2*v-1) / 2 = v - 1 := by omega
  rw [hmod, hdiv] at hlucas
  have key := hpar _ _ hlucas
  rw [key]
  rcases Nat.even_or_odd v with ⟨u, hu⟩ | ⟨u, hu⟩
  · have hu1 : 1 ≤ u := by omega
    have hvm : v % 2 = 0 := by omega
    have hvd : v / 2 = u := by omega
    rw [hvm, hvd]
    have e1 : Nat.choose 1 0 = 1 := by decide
    have e2 : v - 1 = 2*u - 1 := by omega
    rw [e1, e2, one_mul]
    rw [IH u (by omega) hu1]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k+1, by rw [hu, hk]; ring⟩
    · rintro ⟨k, hk⟩
      rcases k with _ | k'
      · simp at hk; omega
      · exact ⟨k', by rw [pow_succ] at hk; omega⟩
  · have hvm : v % 2 = 1 := by omega
    have hvd : v / 2 = u := by omega
    rw [hvm, hvd]
    have e1 : Nat.choose 1 1 = 1 := by decide
    have e2 : v - 1 = 2*u := by omega
    rw [e1, e2, one_mul]
    rw [centralBinom_odd_iff]
    constructor
    · rintro rfl; exact ⟨0, by omega⟩
    · rintro ⟨k, hk⟩
      rcases k with _ | k'
      · simp at hk; omega
      · rw [pow_succ] at hk; omega

-- n is a power of two iff n ∣ 2^(n+1)
lemma pow2_iff_dvd (n : ℕ) (hn : 1 ≤ n) : (∃ k, n = 2^k) ↔ n ∣ 2^(n+1) := by
  constructor
  · rintro ⟨k, rfl⟩
    have hk : k ≤ 2^k + 1 := by
      have hlt : k < 2^k := Nat.lt_two_pow_self; omega
    exact pow_dvd_pow 2 hk
  · intro hd
    rw [Nat.dvd_prime_pow Nat.prime_two] at hd
    obtain ⟨m, _, hm⟩ := hd
    exact ⟨m, hm⟩

open Classical in
lemma zeroPred_zero_iff (n : ℕ) (hn : 2 ≤ n) : zeroPred n 0 ↔ ∃ k, n = 2^k := by
  constructor
  · rintro ⟨v, hv, ho⟩
    have hnv : n = 2 * v := by
      have : (n : ℤ) = 2 * v := by linarith [hv]
      exact_mod_cast this
    have hv1 : 1 ≤ v := by omega
    have : n - 1 = 2 * v - 1 := by omega
    rw [this] at ho
    obtain ⟨k, hk⟩ := (pow2_choose v hv1).1 ho
    exact ⟨k + 1, by rw [hnv, hk]; ring⟩
  · rintro ⟨k, hk⟩
    have hk1 : 1 ≤ k := by
      rcases k with _ | k'
      · simp at hk; omega
      · omega
    have hX : n = 2 * 2^(k-1) := by
      rw [hk, ← pow_succ']; congr 1; omega
    refine ⟨2^(k-1), ?_, ?_⟩
    · rw [hX]; push_cast; ring
    · have hnv : n - 1 = 2 * 2^(k-1) - 1 := by omega
      rw [hnv]
      exact (pow2_choose (2^(k-1)) (Nat.one_le_two_pow)).2 ⟨k-1, rfl⟩

lemma oeis_floor_eq (n : ℕ) (hn : 2 ≤ n) :
    oeis_floor_term n = if n ∣ 2^(n+1) then 1 else 0 := by
  unfold oeis_floor_term
  rw [if_neg (by omega : ¬ n = 0)]
  simp only [Nat.dvd_iff_mod_eq_zero]

open Classical in
lemma mb_eq (n : ℕ) (hn : 2 ≤ n) :
    middle_column_bit n = 1 - oeis_floor_term n := by
  have hg : ca_state n 0 = if zeroPred n 0 then 0 else 1 := gridlem n 0 (by omega)
  have hz : zeroPred n 0 ↔ n ∣ 2^(n+1) :=
    (zeroPred_zero_iff n hn).trans (pow2_iff_dvd n (by omega))
  have hf : oeis_floor_term n = if n ∣ 2^(n+1) then 1 else 0 := oeis_floor_eq n hn
  unfold middle_column_bit
  rw [hg, hf]
  by_cases hd : n ∣ 2^(n+1)
  · rw [if_pos (hz.2 hd), if_pos hd]
  · rw [if_neg (fun h => hd (hz.1 h)), if_neg hd]

lemma hsum (m : ℕ) :
    Finset.sum (Finset.range (m+1)) (fun k => middle_column_bit k * 2^(m+1-k)) = 2 * a m := by
  unfold a
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [show m+1-k = (m-k)+1 by omega, pow_succ]
  ring

lemma a_succ (m : ℕ) : a (m+1) = 2 * a m + middle_column_bit (m+1) := by
  have : a (m+1) =
      Finset.sum (Finset.range (m+1)) (fun k => middle_column_bit k * 2^(m+1-k))
        + middle_column_bit (m+1) * 2^((m+1)-(m+1)) := by
    rw [a, Finset.sum_range_succ]
  rw [this, hsum, Nat.sub_self, pow_zero, mul_one]

lemma oeis_le_one (n : ℕ) : oeis_floor_term n ≤ 1 := by
  unfold oeis_floor_term
  split
  · omega
  · split <;> omega


/--
A267581 conjecture on the recurrence relation.

Assuming the conjecture that the positions of the 0-bits of the middle column ("Rule 167") are given by the sequence A000051, it follows that a possible formula could be: a(n) = 2*a(n-1) + 1 - floor((1/2)^((2^(n+1)) mod n)) with a(0)=1 and a(1)=3 (Not proved, but tested up to n = 10^4). - _Andres Cicuttin_, Mar 29 2016
-/
theorem oeis_267581_conjecture_0 (n : ℕ) (hn : 2 ≤ n) :
    a n = 2 * a (n - 1) + 1 - oeis_floor_term n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m from rfl]
  have hrec := a_succ m
  have hmb := mb_eq (m+1) hn
  have hle := oeis_le_one (m+1)
  omega
