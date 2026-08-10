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

/-
A267581 conjecture on the recurrence relation.

Assuming the conjecture that the positions of the 0-bits of the middle column ("Rule 167") are given by the sequence A000051, it follows that a possible formula could be: a(n) = 2*a(n-1) + 1 - floor((1/2)^((2^(n+1)) mod n)) with a(0)=1 and a(1)=3 (Not proved, but tested up to n = 10^4). - _Andres Cicuttin_, Mar 29 2016
-/
namespace Rule167Proof

/-- For `t ≥ 1`, zeroes are the mod-2 Pascal triangle started at `(1,1)`. -/
def zpos (t : ℕ) (x : ℤ) : Prop :=
  ∃ j : ℕ, j ≤ t - 1 ∧ x = (2 : ℤ) - (t : ℤ) + 2 * (j : ℤ) ∧ Odd ((t - 1).choose j)


noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma zpos_one_iff (x : ℤ) : zpos 1 x ↔ x = 1 := by
  constructor
  · rintro ⟨j, hj, hx, ho⟩
    have hj0 : j = 0 := by omega
    subst j
    norm_num at hx ⊢
    omega
  · intro hx
    subst hx
    refine ⟨0, by omega, ?_, ?_⟩
    · norm_num
    · norm_num

lemma ca_state_one (x : ℤ) : ca_state 1 x = if x = 1 then 0 else 1 := by
  by_cases h1 : x = 1
  · subst x
    norm_num [ca_state, ca_rule_167]
  · by_cases h0 : x = 0
    · subst x
      norm_num [ca_state, ca_rule_167]
    · by_cases hm1 : x = -1
      · subst x
        norm_num [ca_state, ca_rule_167]
      · have hm : x - 1 ≠ 0 := by omega
        have hp : x + 1 ≠ 0 := by omega
        simp [ca_state, ca_rule_167, h1, h0, hm, hp]

lemma ca_state_one_zpos (x : ℤ) : ca_state 1 x = if zpos 1 x then 0 else 1 := by
  classical
  rw [ca_state_one]
  by_cases h : zpos 1 x
  · rw [if_pos h, if_pos ((zpos_one_iff x).1 h)]
  · rw [if_neg h]
    exact if_neg (mt (zpos_one_iff x).2 h)

lemma zpos_not_right {t : ℕ} {x : ℤ} (h : zpos t x) : ¬ zpos t (x + 1) := by
  rintro ⟨j, hj, hx, ho⟩
  rcases h with ⟨i, hi, hxi, hoi⟩
  omega

lemma zpos_not_left {t : ℕ} {x : ℤ} (h : zpos t x) : ¬ zpos t (x - 1) := by
  rintro hz
  exact zpos_not_right hz (by simpa using h)

lemma rule_zero_iff_xor (P Q R : Prop)
    (hPQ : P → ¬ Q) (hRQ : R → ¬ Q) :
    ca_rule_167 (if P then 0 else 1) (if Q then 0 else 1) (if R then 0 else 1) = 0 ↔
      (P ∧ ¬ R) ∨ (¬ P ∧ R) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;>
    simp [ca_rule_167, hP, hQ, hR] at *


lemma rule_eq_xor (P Q R : Prop)
    (hPQ : P → ¬ Q) (hRQ : R → ¬ Q) :
    ca_rule_167 (if P then 0 else 1) (if Q then 0 else 1) (if R then 0 else 1) =
      if (P ∧ ¬ R) ∨ (¬ P ∧ R) then 0 else 1 := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;>
    simp [ca_rule_167, hP, hQ, hR] at *


lemma odd_add_iff_xor (a b : ℕ) :
    Odd (a + b) ↔ (Odd a ∧ ¬ Odd b) ∨ (¬ Odd a ∧ Odd b) := by
  rw [Nat.odd_add]
  by_cases ha : Odd a <;> by_cases hb : Odd b
  · have hbe : ¬ Even b := by
      rw [← Nat.not_odd_iff_even]
      exact not_not.mpr hb
    simp [ha, hb, hbe]
  · have hbe : Even b := (Nat.not_odd_iff_even.mp hb)
    simp [ha, hb, hbe]
  · have hbe : ¬ Even b := by
      rw [← Nat.not_odd_iff_even]
      exact not_not.mpr hb
    simp [ha, hb, hbe]
  · have hbe : Even b := (Nat.not_odd_iff_even.mp hb)
    simp [ha, hb, hbe]


lemma zpos_succ_iff (t : ℕ) (x : ℤ) (ht : 1 ≤ t) :
    zpos (t + 1) x ↔
      (zpos t (x - 1) ∧ ¬ zpos t (x + 1)) ∨
      (¬ zpos t (x - 1) ∧ zpos t (x + 1)) := by
  constructor
  · rintro ⟨j, hj, hx, ho⟩
    by_cases hj0 : j = 0
    · subst j
      right
      constructor
      · intro hz
        rcases hz with ⟨k, hk, hxk, hok⟩
        omega
      · refine ⟨0, by omega, ?_, by norm_num⟩
        omega
    · by_cases hjt : j = t
      · subst j
        left
        constructor
        · refine ⟨t - 1, by omega, ?_, ?_⟩
          · omega
          · have : (t - 1).choose (t - 1) = 1 := Nat.choose_self _
            rw [this]
            norm_num
        · intro hz
          rcases hz with ⟨k, hk, hxk, hok⟩
          omega
      · have hjpos : 0 < j := by omega
        have hjlt : j < t := by omega
        have hpas : t.choose j = (t - 1).choose (j - 1) + (t - 1).choose j := by
          simpa using (Nat.choose_eq_choose_pred_add (n := t) (k := j) (by omega) hjpos)
        have hxor : (Odd ((t - 1).choose (j - 1)) ∧ ¬ Odd ((t - 1).choose j)) ∨
            (¬ Odd ((t - 1).choose (j - 1)) ∧ Odd ((t - 1).choose j)) := by
          have ho' : Odd ((t - 1).choose (j - 1) + (t - 1).choose j) := by
            rwa [← hpas]
          exact (odd_add_iff_xor _ _).1 ho'
        rcases hxor with hleft | hright
        · left
          constructor
          · refine ⟨j - 1, by omega, ?_, hleft.1⟩
            omega
          · intro hz
            rcases hz with ⟨k, hk, hxk, hok⟩
            have hk_eq : k = j := by omega
            subst k
            exact hleft.2 hok
        · right
          constructor
          · intro hz
            rcases hz with ⟨k, hk, hxk, hok⟩
            have hk_eq : k = j - 1 := by omega
            subst k
            exact hright.1 hok
          · refine ⟨j, by omega, ?_, hright.2⟩
            omega
  · intro h
    rcases h with h | h
    · rcases h with ⟨⟨k, hk, hxk, hok⟩, hnright⟩
      by_cases hktop : k = t - 1
      · refine ⟨t, by omega, ?_, ?_⟩
        · omega
        · change Odd (t.choose t)
          have : t.choose t = 1 := Nat.choose_self _
          rw [this]
          norm_num
      · have hklt : k + 1 < t := by omega
        refine ⟨k + 1, by omega, ?_, ?_⟩
        · omega
        · change Odd (t.choose (k + 1))
          have hpas : t.choose (k + 1) = (t - 1).choose k + (t - 1).choose (k + 1) := by
            simpa [Nat.add_one_sub_one] using
              (Nat.choose_eq_choose_pred_add (n := t) (k := k + 1) (by omega) (Nat.succ_pos k))
          rw [hpas]
          apply (odd_add_iff_xor _ _).2
          left
          constructor
          · simpa using hok
          · intro hodd
            apply hnright
            refine ⟨k + 1, by omega, ?_, hodd⟩
            omega
    · rcases h with ⟨hnleft, ⟨k, hk, hxk, hok⟩⟩
      by_cases hk0 : k = 0
      · subst k
        refine ⟨0, by omega, ?_, ?_⟩
        · omega
        · norm_num
      · refine ⟨k, by omega, ?_, ?_⟩
        · omega
        · change Odd (t.choose k)
          have hkpos : 0 < k := by omega
          have hpas : t.choose k = (t - 1).choose (k - 1) + (t - 1).choose k := by
            simpa using (Nat.choose_eq_choose_pred_add (n := t) (k := k) (by omega) hkpos)
          rw [hpas]
          apply (odd_add_iff_xor _ _).2
          right
          constructor
          · intro hodd
            apply hnleft

            refine ⟨k - 1, by omega, ?_, hodd⟩
            omega
          · simpa using hok


lemma ca_state_eq_zpos (t : ℕ) (x : ℤ) (ht : 1 ≤ t) :
    ca_state t x = if zpos t x then 0 else 1 := by
  revert x ht
  induction t with
  | zero => intro x ht; omega
  | succ t ih =>
      intro x ht
      cases t with
      | zero =>
          simpa using ca_state_one_zpos x
      | succ u =>
          have hL : ca_state (u + 1) (x - 1) = if zpos (u + 1) (x - 1) then 0 else 1 :=
            ih (x - 1) (by omega)
          have hC : ca_state (u + 1) x = if zpos (u + 1) x then 0 else 1 :=
            ih x (by omega)
          have hR : ca_state (u + 1) (x + 1) = if zpos (u + 1) (x + 1) then 0 else 1 :=
            ih (x + 1) (by omega)
          change ca_rule_167 (ca_state (u + 1) (x - 1)) (ca_state (u + 1) x) (ca_state (u + 1) (x + 1)) =
            if zpos (u + 1 + 1) x then 0 else 1
          rw [hL, hC, hR]
          rw [rule_eq_xor]
          · let A := (zpos (u + 1) (x - 1) ∧ ¬ zpos (u + 1) (x + 1)) ∨
                (¬ zpos (u + 1) (x - 1) ∧ zpos (u + 1) (x + 1))
            have hiff : zpos (u + 1 + 1) x ↔ A := zpos_succ_iff (u + 1) x (by omega)
            by_cases hA : A
            · have hB : zpos (u + 1 + 1) x := hiff.mpr hA
              rw [if_pos hA, if_pos hB]
            · have hB : ¬ zpos (u + 1 + 1) x := fun hb => hA (hiff.mp hb)
              rw [if_neg hA, if_neg hB]
          · intro hP
            simpa using (zpos_not_right hP)
          · intro hRz
            simpa using (zpos_not_left hRz)


lemma odd_iff_of_modEq_two {a b : ℕ} (h : a ≡ b [MOD 2]) : Odd a ↔ Odd b := by
  unfold Nat.ModEq at h
  rw [Nat.odd_iff, Nat.odd_iff]
  rw [h]

lemma even_central_choose (r : ℕ) (hr : 0 < r) : Even ((2 * r).choose r) := by
  have hsucc : 2 * r = (2 * r - 1) + 1 := by omega
  rw [hsucc, Nat.choose_succ_left _ _ hr]
  have hsym : (2 * r - 1).choose r = (2 * r - 1).choose (r - 1) := by
    have hs : (2 * r - 1) - r = r - 1 := by omega
    rw [← hs]
    exact (Nat.choose_symm (n := 2 * r - 1) (k := r) (by omega)).symm
  rw [hsym]
  exact ⟨(2 * r - 1).choose (r - 1), by ring⟩

lemma odd_choose_even_reduce (r : ℕ) (hr : 0 < r) :
    Odd ((4*r - 1).choose (2*r - 1)) ↔ Odd ((2*r - 1).choose (r - 1)) := by
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 4*r - 1) (k := 2*r - 1) (p := 2) (by infer_instance)
  have h2 : (4*r - 1).choose (2*r - 1) ≡ ((2*r - 1).choose (r - 1)) [MOD 2] := by
    unfold Nat.ModEq at h ⊢
    rw [h]
    have h4 : (4 * r - 1) % 2 = 1 := by omega
    have h2m : (2 * r - 1) % 2 = 1 := by omega
    have hd1 : (4 * r - 1) / 2 = 2 * r - 1 := by omega
    have hd2 : (2 * r - 1) / 2 = r - 1 := by omega
    rw [h4, h2m, hd1, hd2]
    norm_num
  exact odd_iff_of_modEq_two h2

lemma not_odd_choose_odd_nonone (r : ℕ) (hr : 0 < r) :
    ¬ Odd ((4*r + 1).choose (2*r)) := by
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 4*r + 1) (k := 2*r) (p := 2) (by infer_instance)
  have h2 : (4*r + 1).choose (2*r) ≡ ((2*r).choose r) [MOD 2] := by
    unfold Nat.ModEq at h ⊢
    rw [h]
    have h4 : (4 * r + 1) % 2 = 1 := by omega
    have h2m : (2 * r) % 2 = 0 := by omega
    have hd1 : (4 * r + 1) / 2 = 2 * r := by omega
    have hd2 : (2 * r) / 2 = r := by omega
    rw [h4, h2m, hd1, hd2]
    norm_num
  have hiff := odd_iff_of_modEq_two h2
  intro ho
  have hcodd : Odd ((2*r).choose r) := hiff.mp ho
  have hceven : Even ((2*r).choose r) := even_central_choose r hr
  exact (Nat.not_odd_iff_even.mpr hceven) hcodd

lemma central_pred_odd_iff_pow (m : ℕ) (hm : 0 < m) :
    Odd ((2 * m - 1).choose (m - 1)) ↔ ∃ k : ℕ, m = 2 ^ k := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst m
      constructor
      · intro _; exact ⟨0, by norm_num⟩
      · intro _; norm_num
    · rcases Nat.even_or_odd m with he | ho
      · rcases he with ⟨r, rfl⟩
        have hr : 0 < r := by omega
        rw [show r + r = 2 * r by omega]
        have htop : 2 * (2 * r) - 1 = 4 * r - 1 := by omega
        rw [htop]
        have hred := odd_choose_even_reduce r hr
        rw [hred]
        have hih := ih r (by omega) hr
        rw [hih]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          rw [hk]
          ring
        · rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k =>
              refine ⟨k, ?_⟩
              rw [pow_succ] at hk
              omega
      · rcases ho with ⟨r, rfl⟩
        have hr : 0 < r := by omega
        have htop : 2 * (2 * r + 1) - 1 = 4 * r + 1 := by omega
        have hbot : (2 * r + 1) - 1 = 2 * r := by omega
        rw [htop, hbot]
        constructor
        · intro hodd
          exact False.elim ((not_odd_choose_odd_nonone r hr) hodd)
        · rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k =>
              rw [pow_succ] at hk
              omega

lemma zpos_zero_iff_pow (n : ℕ) (hn : 2 ≤ n) :
    zpos n 0 ↔ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · rintro ⟨j, hj, hx, ho⟩
    have hn_eq : n = 2 * (j + 1) := by omega
    subst n
    have ho' : Odd ((2 * (j + 1) - 1).choose ((j + 1) - 1)) := by
      simpa using ho
    have hp : ∃ k : ℕ, j + 1 = 2 ^ k := (central_pred_odd_iff_pow (j + 1) (by omega)).mp ho'
    rcases hp with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [hk]
    ring
  · rintro ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k =>
        subst n
        refine ⟨2 ^ k - 1, by omega, ?_, ?_⟩
        · norm_num
          have hp : (0 : ℤ) = 2 - (2 ^ (k + 1) : ℕ) + 2 * ((2 ^ k - 1 : ℕ) : ℤ) := by
            rw [pow_succ]
            have hpos : 0 < 2 ^ k := pow_pos (by norm_num) _
            omega
          simpa using hp
        · have hpodd : Odd ((2 * (2 ^ k) - 1).choose ((2 ^ k) - 1)) :=
            (central_pred_odd_iff_pow (2 ^ k) (pow_pos (by norm_num) _)).mpr ⟨k, rfl⟩
          have htop : 2 ^ (k + 1) - 1 = 2 * (2 ^ k) - 1 := by
            rw [pow_succ]
            omega
          rw [htop]
          simpa using hpodd


lemma a_succ (n : ℕ) : a (n + 1) = 2 * a n + middle_column_bit (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]
  rw [show n + 1 - (n + 1) = 0 by omega, pow_zero, mul_one]
  rw [Nat.add_right_cancel_iff]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hexp : n + 1 - k = (n - k) + 1 := by omega
  rw [hexp, pow_succ]
  ring

lemma floor_term_eq_pow (n : ℕ) (hn : 2 ≤ n) :
    oeis_floor_term n = if (∃ k : ℕ, n = 2 ^ k) then 1 else 0 := by
  unfold oeis_floor_term
  rw [if_neg (by omega : n ≠ 0)]
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · rw [if_pos hpow]
    rcases hpow with ⟨k, rfl⟩
    rw [if_pos]
    · have hk : k ≤ 2 ^ k + 1 := by
        have hlt := @Nat.lt_two_pow_self k
        omega
      exact Nat.dvd_iff_mod_eq_zero.mp (Nat.pow_dvd_pow 2 hk)
  · rw [if_neg hpow]
    rw [if_neg]
    intro hmod
    have hdvd : n ∣ 2 ^ (n + 1) := Nat.dvd_iff_mod_eq_zero.mpr hmod
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, hk, heq⟩
    exact hpow ⟨k, heq⟩



end Rule167Proof


theorem oeis_267581_conjecture_0 (n : ℕ) (hn : 2 ≤ n) :
  a n = 2 * a (n - 1) + 1 - oeis_floor_term n :=
by
  classical
  have hs : n - 1 + 1 = n := by omega
  have ha := Rule167Proof.a_succ (n - 1)
  rw [hs] at ha
  rw [ha]
  by_cases hpow : ∃ k : ℕ, n = 2 ^ k
  · have hz : Rule167Proof.zpos n 0 := (Rule167Proof.zpos_zero_iff_pow n hn).2 hpow
    have hm : middle_column_bit n = 0 := by
      unfold middle_column_bit
      rw [Rule167Proof.ca_state_eq_zpos n 0 (by omega), if_pos hz]
    have hf : oeis_floor_term n = 1 := by
      rw [Rule167Proof.floor_term_eq_pow n hn, if_pos hpow]
    rw [hm, hf]
    omega
  · have hz : ¬ Rule167Proof.zpos n 0 := fun hz => hpow ((Rule167Proof.zpos_zero_iff_pow n hn).1 hz)
    have hm : middle_column_bit n = 1 := by
      unfold middle_column_bit
      rw [Rule167Proof.ca_state_eq_zpos n 0 (by omega), if_neg hz]
    have hf : oeis_floor_term n = 0 := by
      rw [Rule167Proof.floor_term_eq_pow n hn, if_neg hpow]
    rw [hm, hf]
    omega
