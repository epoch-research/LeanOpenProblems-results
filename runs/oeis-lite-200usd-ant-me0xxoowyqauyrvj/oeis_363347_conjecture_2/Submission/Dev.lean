import FormalConjectures.Util.ProblemImports

open Rat Nat

private lemma sq5_1 : IsSquare ((1:ℕ) : ZMod 5) := ⟨1, by decide⟩
private lemma sq5_4 : IsSquare ((4:ℕ) : ZMod 5) := ⟨2, by decide⟩

-- (copied from Spec.lean for development)
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) + (n : ℚ) / 4
      else
        let R_next := continued_fraction_denominator n (k + 1)
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs

namespace A363

/-- Integer numerator sequence X_k for parameter n: X_n = 4, X_{n-1}=5n-4,
    X_k = k X_{k+1} - (k+1) X_{k+2} for 2 ≤ k ≤ n-2. -/
def Xb (n k : ℕ) : ℤ :=
  if k = n then 4
  else if k + 1 = n then 5 * (n : ℤ) - 4
  else if 2 ≤ k ∧ k + 2 ≤ n then (k : ℤ) * Xb n (k+1) - (k+1 : ℤ) * Xb n (k+2)
  else 0
termination_by n - k
decreasing_by
  · omega
  · omega

/-- Companion integer sequence U_k: U_n = 0, U_{n-1}=1, same recurrence. -/
def Ub (n k : ℕ) : ℤ :=
  if k = n then 0
  else if k + 1 = n then 1
  else if 2 ≤ k ∧ k + 2 ≤ n then (k : ℤ) * Ub n (k+1) - (k+1 : ℤ) * Ub n (k+2)
  else 0
termination_by n - k
decreasing_by
  · omega
  · omega

/-- Explicit closed-form solution S_j = (j-2)/(j-1)! over ℚ. -/
noncomputable def Sq (j : ℕ) : ℚ := ((j : ℚ) - 2) / ((j - 1).factorial : ℚ)

-- Base values
lemma Xb_top (n : ℕ) : Xb n n = 4 := by rw [Xb]; simp
lemma Ub_top (n : ℕ) : Ub n n = 0 := by rw [Ub]; simp

lemma Xb_sub1 (n : ℕ) (hn : 2 ≤ n) : Xb n (n-1) = 5 * (n : ℤ) - 4 := by
  rw [Xb]
  have h1 : n - 1 ≠ n := by omega
  have h2 : (n - 1) + 1 = n := by omega
  rw [if_neg h1, if_pos h2]

lemma Ub_sub1 (n : ℕ) (hn : 2 ≤ n) : Ub n (n-1) = 1 := by
  rw [Ub]
  have h1 : n - 1 ≠ n := by omega
  have h2 : (n - 1) + 1 = n := by omega
  rw [if_neg h1, if_pos h2]

-- Recurrence equations on the recursive range 2 ≤ k, k+2 ≤ n
lemma Xb_rec (n k : ℕ) (hk : 2 ≤ k) (hk2 : k + 2 ≤ n) :
    Xb n k = (k : ℤ) * Xb n (k+1) - (k+1 : ℤ) * Xb n (k+2) := by
  rw [Xb]
  have h1 : k ≠ n := by omega
  have h2 : k + 1 ≠ n := by omega
  rw [if_neg h1, if_neg h2, if_pos ⟨hk, hk2⟩]

lemma Ub_rec (n k : ℕ) (hk : 2 ≤ k) (hk2 : k + 2 ≤ n) :
    Ub n k = (k : ℤ) * Ub n (k+1) - (k+1 : ℤ) * Ub n (k+2) := by
  rw [Ub]
  have h1 : k ≠ n := by omega
  have h2 : k + 1 ≠ n := by omega
  rw [if_neg h1, if_neg h2, if_pos ⟨hk, hk2⟩]

lemma Sq_rec (j : ℕ) (hj : 1 ≤ j) :
    Sq j = (j : ℚ) * Sq (j+1) - (j+1 : ℚ) * Sq (j+2) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j-1, by omega⟩
  simp only [Sq]
  have e1 : m + 1 - 1 = m := by omega
  have e2 : m + 2 - 1 = m + 1 := by omega
  have e3 : m + 3 - 1 = m + 2 := by omega
  rw [e1, e2, e3, Nat.factorial_succ (m+1), Nat.factorial_succ m]
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  push_cast
  field_simp
  ring

/-- The "Casoratian weight": j! (a_j b_{j+1} - a_{j+1} b_j). -/
noncomputable def Wt (a b : ℕ → ℚ) (j : ℕ) : ℚ :=
  (j.factorial : ℚ) * (a j * b (j+1) - a (j+1) * b j)

/-- One-step invariance of the Casoratian weight given both sequences satisfy the
    recurrence at index j. -/
lemma Wt_step (a b : ℕ → ℚ) (j : ℕ)
    (ha : a j = (j : ℚ) * a (j+1) - (j+1 : ℚ) * a (j+2))
    (hb : b j = (j : ℚ) * b (j+1) - (j+1 : ℚ) * b (j+2)) :
    Wt a b j = Wt a b (j+1) := by
  unfold Wt
  rw [Nat.factorial_succ]
  rw [ha, hb]
  push_cast
  ring

/-- Constancy of the Casoratian weight along the recursive range. -/
lemma Wt_const (a b : ℕ → ℚ) (n : ℕ)
    (ha : ∀ j, 2 ≤ j → j + 2 ≤ n → a j = (j:ℚ) * a (j+1) - (j+1:ℚ) * a (j+2))
    (hb : ∀ j, 2 ≤ j → j + 2 ≤ n → b j = (j:ℚ) * b (j+1) - (j+1:ℚ) * b (j+2)) :
    ∀ i, 2 + i ≤ n - 1 → Wt a b 2 = Wt a b (2 + i) := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      have h1 : 2 + k ≤ n - 1 := by omega
      rw [ih h1]
      have : (2 + (k+1)) = (2 + k) + 1 := by omega
      rw [this]
      apply Wt_step
      · exact ha (2+k) (by omega) (by omega)
      · exact hb (2+k) (by omega) (by omega)

/-- Wt(Xq, Sq) and constancy: gives Wt at 2 equals Wt at n-1. -/
lemma Wt_two_eq_sub1 (a b : ℕ → ℚ) (n : ℕ) (hn : 3 ≤ n)
    (ha : ∀ j, 2 ≤ j → j + 2 ≤ n → a j = (j:ℚ) * a (j+1) - (j+1:ℚ) * a (j+2))
    (hb : ∀ j, 2 ≤ j → j + 2 ≤ n → b j = (j:ℚ) * b (j+1) - (j+1:ℚ) * b (j+2)) :
    Wt a b 2 = Wt a b (n-1) := by
  have := Wt_const a b n ha hb (n - 3) (by omega)
  have e : 2 + (n - 3) = n - 1 := by omega
  rwa [e] at this

-- Sq small values
lemma Sq_two : Sq 2 = 0 := by simp [Sq]
lemma Sq_three : Sq 3 = 1/2 := by
  simp [Sq]; norm_num [Nat.factorial]

-- ℚ-recurrences for Xb and Ub (casts of the integer recurrences)
lemma Xq_rec (n : ℕ) : ∀ j, 2 ≤ j → j + 2 ≤ n →
    (Xb n j : ℚ) = (j:ℚ) * (Xb n (j+1):ℚ) - (j+1:ℚ) * (Xb n (j+2):ℚ) := by
  intro j hj hj2
  have := Xb_rec n j hj hj2
  exact_mod_cast this

lemma Uq_rec (n : ℕ) : ∀ j, 2 ≤ j → j + 2 ≤ n →
    (Ub n j : ℚ) = (j:ℚ) * (Ub n (j+1):ℚ) - (j+1:ℚ) * (Ub n (j+2):ℚ) := by
  intro j hj hj2
  have := Ub_rec n j hj hj2
  exact_mod_cast this

lemma Sqq_rec : ∀ j, 2 ≤ j → (Sq j = (j:ℚ) * Sq (j+1) - (j+1:ℚ) * Sq (j+2)) := by
  intro j hj; exact Sq_rec j (by omega)

/-- X_2 closed form: X_2(n) = n^2 + 2n - 4 = (n+1)^2 - 5. -/
lemma Xb_two (n : ℕ) (hn : 3 ≤ n) : Xb n 2 = (n:ℤ)^2 + 2*(n:ℤ) - 4 := by
  set Xq : ℕ → ℚ := fun j => (Xb n j : ℚ) with hXq
  have hrecX : ∀ j, 2 ≤ j → j + 2 ≤ n → Xq j = (j:ℚ) * Xq (j+1) - (j+1:ℚ) * Xq (j+2) :=
    Xq_rec n
  have hrecS : ∀ j, 2 ≤ j → j + 2 ≤ n → Sq j = (j:ℚ) * Sq (j+1) - (j+1:ℚ) * Sq (j+2) :=
    fun j hj _ => Sqq_rec j hj
  have hconst := Wt_two_eq_sub1 Xq Sq n hn hrecX hrecS
  -- LHS: Wt Xq Sq 2 = Xb n 2
  have hL : Wt Xq Sq 2 = (Xb n 2 : ℚ) := by
    unfold Wt
    rw [show (2:ℕ)+1 = 3 from rfl]
    rw [Sq_three, Sq_two]
    simp [hXq, Nat.factorial]
    ring
  -- RHS: Wt Xq Sq (n-1) = n^2+2n-4
  have hR : Wt Xq Sq (n-1) = (n:ℚ)^2 + 2*(n:ℚ) - 4 := by
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
    have e1 : N + 3 - 1 = N + 2 := by omega
    unfold Wt
    rw [e1]
    have hx1 : Xb (N+3) (N+2) = 5 * ((N:ℤ)+3) - 4 := by
      have h := Xb_sub1 (N+3) (by omega); rw [e1] at h; rw [h]; push_cast; ring
    have hx2 : Xb (N+3) (N+3) = 4 := Xb_top (N+3)
    have hS1 : Sq (N+3) = ((N:ℚ)+1) / ((N+2).factorial : ℚ) := by
      simp only [Sq]; rw [show N+3-1 = N+2 from by omega]; push_cast; ring_nf
    have hS2 : Sq (N+2) = ((N:ℚ)) / ((N+1).factorial : ℚ) := by
      simp only [Sq]; rw [show N+2-1 = N+1 from by omega]; push_cast; ring_nf
    simp only [hXq]
    rw [show (N+2)+1 = N+3 from rfl, hx1, hx2, hS1, hS2]
    have hfp : ((N+2).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hfp1 : ((N+1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Nat.factorial_succ (N+1)]
    push_cast
    field_simp
    ring
  rw [hL, hR] at hconst
  have : (Xb n 2 : ℚ) = ((n:ℤ)^2 + 2*(n:ℤ) - 4 : ℤ) := by push_cast; linarith [hconst]
  exact_mod_cast this

/-- U_2 closed form: U_2(n) = n - 2. -/
lemma Ub_two (n : ℕ) (hn : 3 ≤ n) : Ub n 2 = (n:ℤ) - 2 := by
  set Uq : ℕ → ℚ := fun j => (Ub n j : ℚ) with hUq
  have hrecU : ∀ j, 2 ≤ j → j + 2 ≤ n → Uq j = (j:ℚ) * Uq (j+1) - (j+1:ℚ) * Uq (j+2) :=
    Uq_rec n
  have hrecS : ∀ j, 2 ≤ j → j + 2 ≤ n → Sq j = (j:ℚ) * Sq (j+1) - (j+1:ℚ) * Sq (j+2) :=
    fun j hj _ => Sqq_rec j hj
  have hconst := Wt_two_eq_sub1 Uq Sq n hn hrecU hrecS
  have hL : Wt Uq Sq 2 = (Ub n 2 : ℚ) := by
    unfold Wt
    rw [show (2:ℕ)+1 = 3 from rfl, Sq_three, Sq_two]
    simp [hUq, Nat.factorial]; ring
  have hR : Wt Uq Sq (n-1) = (n:ℚ) - 2 := by
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
    have e1 : N + 3 - 1 = N + 2 := by omega
    unfold Wt
    rw [e1]
    have hu1 : Ub (N+3) (N+2) = 1 := by
      have h := Ub_sub1 (N+3) (by omega); rw [e1] at h; exact h
    have hu2 : Ub (N+3) (N+3) = 0 := Ub_top (N+3)
    have hS1 : Sq (N+3) = ((N:ℚ)+1) / ((N+2).factorial : ℚ) := by
      simp only [Sq]; rw [show N+3-1 = N+2 from by omega]; push_cast; ring_nf
    have hS2 : Sq (N+2) = ((N:ℚ)) / ((N+1).factorial : ℚ) := by
      simp only [Sq]; rw [show N+2-1 = N+1 from by omega]; push_cast; ring_nf
    simp only [hUq]
    rw [show (N+2)+1 = N+3 from rfl, hu1, hu2, hS1, hS2]
    have hfp : ((N+2).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast
    field_simp
    ring
  rw [hL, hR] at hconst
  have : (Ub n 2 : ℚ) = ((n:ℤ) - 2 : ℤ) := by push_cast; linarith [hconst]
  exact_mod_cast this

/-- Relation (R-a): (n-2) X_3 - U_3 X_2 = 2 (n-1)!. -/
lemma Xb_ra (n : ℕ) (hn : 3 ≤ n) :
    ((n:ℤ) - 2) * Xb n 3 - Ub n 3 * Xb n 2 = 2 * ((n-1).factorial : ℤ) := by
  set Xq : ℕ → ℚ := fun j => (Xb n j : ℚ) with hXq
  set Uq : ℕ → ℚ := fun j => (Ub n j : ℚ) with hUq
  have hrecX : ∀ j, 2 ≤ j → j + 2 ≤ n → Xq j = (j:ℚ) * Xq (j+1) - (j+1:ℚ) * Xq (j+2) :=
    Xq_rec n
  have hrecU : ∀ j, 2 ≤ j → j + 2 ≤ n → Uq j = (j:ℚ) * Uq (j+1) - (j+1:ℚ) * Uq (j+2) :=
    Uq_rec n
  have hconst := Wt_two_eq_sub1 Xq Uq n hn hrecX hrecU
  have hL : Wt Xq Uq 2 = 2 * ((Xb n 2 : ℚ) * (Ub n 3 : ℚ) - (Xb n 3 : ℚ) * (Ub n 2 : ℚ)) := by
    unfold Wt
    rw [show (2:ℕ)+1 = 3 from rfl]
    simp only [hXq, hUq]
    norm_num [Wt, Nat.factorial]
  have hR : Wt Xq Uq (n-1) = -4 * ((n-1).factorial : ℚ) := by
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 3 := ⟨n - 3, by omega⟩
    have e1 : N + 3 - 1 = N + 2 := by omega
    unfold Wt
    rw [e1]
    have hx1 : Xb (N+3) (N+2) = 5 * ((N:ℤ)+3) - 4 := by
      have h := Xb_sub1 (N+3) (by omega); rw [e1] at h; rw [h]; push_cast; ring
    have hx2 : Xb (N+3) (N+3) = 4 := Xb_top (N+3)
    have hu1 : Ub (N+3) (N+2) = 1 := by
      have h := Ub_sub1 (N+3) (by omega); rw [e1] at h; exact h
    have hu2 : Ub (N+3) (N+3) = 0 := Ub_top (N+3)
    simp only [hXq, hUq]
    rw [show (N+2)+1 = N+3 from rfl, hx1, hx2, hu1, hu2]
    push_cast
    ring
  rw [hL, hR] at hconst
  rw [Ub_two n hn] at hconst
  -- hconst : 2*(X2*U3 - X3*(n-2)) = -4*(n-1)!  over ℚ
  have key : ((((n:ℤ)-2) * Xb n 3 - Ub n 3 * Xb n 2 : ℤ)) = (2 * ((n-1).factorial : ℤ)) := by
    have hq : ((((n:ℤ)-2) * Xb n 3 - Ub n 3 * Xb n 2 : ℤ) : ℚ)
        = ((2 * ((n-1).factorial : ℤ) : ℤ) : ℚ) := by
      push_cast
      push_cast at hconst
      linarith [hconst]
    exact_mod_cast hq
  exact key

/-- Positivity together with the sharp lower bound invariant. -/
lemma Xb_posbound (n : ℕ) (hn : 3 ≤ n) :
    ∀ d k, k + d = n - 1 → 2 ≤ k →
      Xb n k > 0 ∧ ((k:ℤ)-1) * Xb n k > (k:ℤ) * ((k:ℤ)-2) * Xb n (k+1) := by
  intro d
  induction d with
  | zero =>
      intro k hk hk2
      have hkn : k = n - 1 := by omega
      subst hkn
      have hx1 : Xb n (n-1) = 5 * (n:ℤ) - 4 := Xb_sub1 n (by omega)
      have he : (n-1) + 1 = n := by omega
      have hx2 : Xb n ((n-1)+1) = 4 := by rw [he]; exact Xb_top n
      have hcast : ((n-1 : ℕ) : ℤ) = (n:ℤ) - 1 := by
        have : 1 ≤ n := by omega
        omega
      have hn3 : (3:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
      refine ⟨?_, ?_⟩
      · rw [hx1]; linarith
      · rw [hx1, hx2, hcast]; nlinarith [hn3]
  | succ d ih =>
      intro k hkd hk2
      obtain ⟨hpos1, hbound1⟩ := ih (k+1) (by omega) (by omega)
      have hrec := Xb_rec n k hk2 (by omega)
      have hkk : (2:ℤ) ≤ (k:ℤ) := by exact_mod_cast hk2
      rw [show k+1+1 = k+2 from rfl] at hbound1
      push_cast at hbound1
      have hbound : ((k:ℤ)-1) * Xb n k > (k:ℤ) * ((k:ℤ)-2) * Xb n (k+1) := by
        rw [hrec]; nlinarith [hbound1]
      refine ⟨?_, hbound⟩
      have h1 : (0:ℤ) ≤ (k:ℤ)*((k:ℤ)-2) := by nlinarith [hkk]
      have h2 : (0:ℤ) ≤ (k:ℤ)*((k:ℤ)-2)*Xb n (k+1) := mul_nonneg h1 (le_of_lt hpos1)
      have h3 : ((k:ℤ)-1) * Xb n k > 0 := lt_of_le_of_lt h2 hbound
      have h4 : (0:ℤ) < (k:ℤ)-1 := by linarith
      nlinarith [h3, h4]

/-- Positivity of X_k for 2 ≤ k ≤ n. -/
lemma Xb_pos (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) : Xb n k > 0 := by
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact (Xb_posbound n hn (n - 1 - k) k (by omega) hk).1
  · have : k = n := by omega
    subst this; rw [Xb_top]; norm_num

lemma Xb_ne (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (Xb n k : ℚ) ≠ 0 := by
  have := Xb_pos n hn k hk hkn
  exact_mod_cast (ne_of_gt this)

-- cfd equation lemmas
lemma cfd_base (n : ℕ) (hn : 3 ≤ n) :
    continued_fraction_denominator n (n-1) = ((n-1:ℕ):ℚ) + (n:ℚ)/4 := by
  rw [continued_fraction_denominator]
  rw [if_neg (by omega : ¬ n ≤ 2)]
  rw [if_pos (⟨by omega, le_refl _⟩ : 2 ≤ n-1 ∧ n-1 ≤ n-1)]
  rw [if_pos rfl]

lemma cfd_rec (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) (hk2 : k + 2 ≤ n) :
    continued_fraction_denominator n k
      = (k:ℚ) - ((k:ℚ)+1) / (continued_fraction_denominator n (k+1)) := by
  rw [continued_fraction_denominator]
  rw [if_neg (by omega : ¬ n ≤ 2)]
  rw [if_pos (⟨hk, by omega⟩ : 2 ≤ k ∧ k ≤ n-1)]
  rw [if_neg (by omega : k ≠ n-1)]

/-- Connection: cfd n k = X_k / X_{k+1}. -/
lemma cfd_eq (n : ℕ) (hn : 3 ≤ n) : ∀ d k, k + d = n - 1 → 2 ≤ k →
    continued_fraction_denominator n k = (Xb n k : ℚ) / (Xb n (k+1) : ℚ) := by
  intro d
  induction d with
  | zero =>
      intro k hk hk2
      have hkn : k = n - 1 := by omega
      subst hkn
      rw [cfd_base n hn, Xb_sub1 n (by omega), show (n-1)+1 = n from by omega, Xb_top n]
      have hcast : ((n-1:ℕ):ℚ) = (n:ℚ)-1 := by
        have : (1:ℕ) ≤ n := by omega
        push_cast [Nat.cast_sub this]; ring
      rw [hcast]
      norm_num
      ring
  | succ d ih =>
      intro k hkd hk2
      rw [cfd_rec n k hn hk2 (by omega)]
      rw [ih (k+1) (by omega) (by omega)]
      have hne1 : (Xb n (k+1) : ℚ) ≠ 0 := Xb_ne n hn (k+1) (by omega) (by omega)
      have hne2 : (Xb n (k+2) : ℚ) ≠ 0 := Xb_ne n hn (k+2) (by omega) (by omega)
      rw [show k+1+1 = k+2 from rfl]
      rw [Xb_rec n k hk2 (by omega)]
      push_cast
      field_simp

/-- If X₂ = p·t with t | X₃ and p ∤ X₃ (p prime), then A363347 n = p. -/
lemma a_eq_p (n : ℕ) (p : ℕ) (hn : 3 ≤ n) (hp : p.Prime) (t : ℤ)
    (hpos_t : 0 < t)
    (hX2 : Xb n 2 = (p:ℤ) * t)
    (htX3 : t ∣ Xb n 3)
    (hpX3 : ¬ (p:ℤ) ∣ Xb n 3) :
    A363347 n = p := by
  obtain ⟨D, hD⟩ := htX3
  have hX3pos : 0 < Xb n 3 := Xb_pos n hn 3 (by norm_num) (by omega)
  have hDpos : 0 < D := by
    rcases lt_trichotomy D 0 with h | h | h
    · exfalso; nlinarith [hX3pos, hD, hpos_t, mul_neg_of_pos_of_neg hpos_t h]
    · exfalso; rw [h, mul_zero] at hD; omega
    · exact h
  have hpD : ¬ (p:ℤ) ∣ D := by
    intro hdvd; exact hpX3 (hD ▸ Dvd.dvd.mul_left hdvd t)
  unfold A363347
  rw [if_neg (by omega : ¬ n ≤ 2)]
  have hcfd : continued_fraction_denominator n 2 = (Xb n 2 : ℚ) / (Xb n 3 : ℚ) :=
    cfd_eq n hn (n-1-2) 2 (by omega) (by norm_num)
  simp only [hcfd, hX2, hD]
  have ht0 : ((t:ℤ):ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos_t)
  have hD0 : ((D:ℤ):ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hDpos)
  have heq : (((p:ℤ) * t : ℤ) : ℚ) / (((t * D) : ℤ) : ℚ) = ((p:ℤ) : ℚ) / ((D : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq]
  have hcop : ((p:ℤ).natAbs).Coprime (D.natAbs) := by
    have hpp : (p:ℤ).natAbs = p := by simp
    rw [hpp, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    apply hpD
    exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hdvd)
  rw [Rat.num_div_eq_of_coprime (by exact_mod_cast hDpos) hcop]
  simp

/-- The main construction: produce `A363347 n = p` from arithmetic hypotheses. -/
lemma construction (n p t : ℕ) (hn : 3 ≤ n) (hp : p.Prime)
    (ht_pos : 0 < t)
    (hPT : ((n:ℤ)+1)^2 - 5 = (p:ℤ) * (t:ℤ))
    (ht_le : t ≤ n - 1)
    (hcop : IsCoprime ((n:ℤ)-2) (t:ℤ))
    (hp_big : n - 1 < p) :
    A363347 n = p := by
  -- X2 = p t
  have hX2 : Xb n 2 = (p:ℤ) * (t:ℤ) := by
    rw [Xb_two n hn]; rw [← hPT]; ring
  -- the relation R-a
  have hra := Xb_ra n hn
  rw [hX2] at hra
  -- (n-2) X3 = U3 (p t) + 2 (n-1)!
  have hra' : ((n:ℤ)-2) * Xb n 3 = Ub n 3 * ((p:ℤ) * (t:ℤ)) + 2 * ((n-1).factorial : ℤ) := by
    linarith [hra]
  -- divisibility facts about factorial
  have htfact : (t:ℤ) ∣ ((n-1).factorial : ℤ) := by
    exact_mod_cast Nat.dvd_factorial ht_pos ht_le
  have hpfact : ¬ (p:ℤ) ∣ (2 * ((n-1).factorial : ℤ)) := by
    have hnat : ¬ p ∣ (2 * (n-1).factorial) := by
      intro h
      rcases (Nat.Prime.dvd_mul hp).mp h with h2 | hf
      · have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
        omega
      · have : p ≤ n - 1 := (Nat.Prime.dvd_factorial hp).mp hf
        omega
    intro h
    apply hnat
    have : (p:ℤ) ∣ ((2 * (n-1).factorial : ℕ) : ℤ) := by push_cast; exact h
    exact_mod_cast this
  -- t | X3
  have htX3 : (t:ℤ) ∣ Xb n 3 := by
    have hdvd : (t:ℤ) ∣ ((n:ℤ)-2) * Xb n 3 := by
      rw [hra']
      apply dvd_add
      · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_refl _) _) _
      · exact Dvd.dvd.mul_left htfact 2
    exact (hcop.symm).dvd_of_dvd_mul_left hdvd
  -- p ∤ X3
  have hpX3 : ¬ (p:ℤ) ∣ Xb n 3 := by
    intro h
    apply hpfact
    have h1 : (p:ℤ) ∣ ((n:ℤ)-2) * Xb n 3 := Dvd.dvd.mul_left h _
    have h2 : (p:ℤ) ∣ Ub n 3 * ((p:ℤ) * (t:ℤ)) :=
      Dvd.dvd.mul_left (Dvd.dvd.mul_right (dvd_refl _) _) _
    have : (p:ℤ) ∣ 2 * ((n-1).factorial : ℤ) := by
      have := dvd_sub h1 h2
      rwa [hra', add_sub_cancel_left] at this
    exact this
  exact a_eq_p n p hn hp (t:ℤ) (by exact_mod_cast ht_pos) hX2 htX3 hpX3

/-- 5 is a quadratic residue mod p (p ≡ ±1 mod 5): existence of an even square root. -/
theorem five_qr (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ m : ℕ, Even m ∧ 4 ≤ m ∧ m ≤ p - 2 ∧ (p:ℤ) ∣ ((m:ℤ)^2 - 5) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp2le : 2 ≤ p := hp.two_le
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hsq : IsSquare (5 : ZMod p) := by
    have hiff := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
      (by norm_num) hp2
    have h5 : (5 : ZMod p) = ((5:ℕ) : ZMod p) := by push_cast; ring
    rw [h5, ← hiff]
    rcases hmod with h | h
    · rw [← ZMod.natCast_mod p 5, h]; exact sq5_1
    · rw [← ZMod.natCast_mod p 5, h]; exact sq5_4
  obtain ⟨y, hy⟩ := hsq
  set m0 := y.val with hm0def
  have hm0cast : (m0 : ZMod p) = y := ZMod.natCast_rightInverse y
  have hm0lt : m0 < p := ZMod.val_lt y
  have h5ne : (5 : ZMod p) ≠ 0 := by
    rw [show (5:ZMod p) = ((5:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd)
  have hy0 : y ≠ 0 := by
    intro h; rw [h, mul_zero] at hy; exact h5ne hy
  have hm0pos : 1 ≤ m0 := by
    rcases Nat.eq_zero_or_pos m0 with h | h
    · exfalso; apply hy0; rw [← hm0cast, h]; simp
    · exact h
  have hdvd0 : (p:ℤ) ∣ ((m0:ℤ)^2 - 5) := by
    have hz : (((m0:ℤ)^2 - 5 : ℤ) : ZMod p) = 0 := by
      push_cast; rw [hm0cast, hy]; ring
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  set m := (if Even m0 then m0 else p - m0) with hmdef
  have hmpos : 1 ≤ m := by rw [hmdef]; split <;> omega
  have hmlt : m ≤ p - 1 := by rw [hmdef]; split <;> omega
  have hmeven : Even m := by
    rw [hmdef]; split
    · assumption
    · rename_i h; exact Nat.Odd.sub_odd hpodd (Nat.not_even_iff_odd.mp h)
  have hmdvd : (p:ℤ) ∣ ((m:ℤ)^2 - 5) := by
    rw [hmdef]; split
    · exact hdvd0
    · have hle : m0 ≤ p := le_of_lt hm0lt
      have hcast : ((p - m0 : ℕ) : ℤ) = (p:ℤ) - (m0:ℤ) := by
        push_cast [Nat.cast_sub hle]; ring
      rw [hcast]
      have hexp : ((p:ℤ) - m0)^2 - 5 = ((m0:ℤ)^2 - 5) + (p:ℤ) * ((p:ℤ) - 2*m0) := by ring
      rw [hexp]
      exact dvd_add hdvd0 (Dvd.dvd.mul_right (dvd_refl _) _)
  have hm_ne2 : m ≠ 2 := by
    intro h; rw [h] at hmdvd
    have hk : (((2:ℕ):ℤ)^2 - 5) = -1 := by norm_num
    rw [hk] at hmdvd
    have hpd1 : p ∣ ((-1 : ℤ)).natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hmdvd; simpa using this
    have := Nat.le_of_dvd (by norm_num) hpd1
    omega
  have hm_nep1 : m ≠ p - 1 := by
    intro h
    rw [h] at hmdvd
    have hcast : ((p - 1 : ℕ) : ℤ) = (p:ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [hcast] at hmdvd
    have hexp : ((p:ℤ) - 1)^2 - 5 = (p:ℤ) * ((p:ℤ) - 2) - 4 := by ring
    rw [hexp] at hmdvd
    have hp4 : (p:ℤ) ∣ 4 := by
      have h1 : (p:ℤ) ∣ (p:ℤ) * ((p:ℤ) - 2) := Dvd.dvd.mul_right (dvd_refl _) _
      have := dvd_sub h1 hmdvd
      simpa using this
    have hpn4 : p ∣ 4 := by exact_mod_cast hp4
    have h22 : p ∣ 2^2 := by rw [show (2:ℕ)^2 = 4 from by norm_num]; exact hpn4
    have hp2eq : p ∣ 2 := hp.dvd_of_dvd_pow h22
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2eq)
  have hm_ge4 : 4 ≤ m := by
    rcases hmeven with ⟨c, hc⟩; omega
  exact ⟨m, hmeven, hm_ge4, by omega, hmdvd⟩

/-- Final: every prime p ≡ ±1 mod 5 occurs in the sequence. -/
theorem exists_of_mod (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ n, A363347 n = p := by
  obtain ⟨m, hmeven, hm4, hmp2, hmdvd⟩ := five_qr p hp hp2 hp5 hmod
  -- n = m - 1
  refine ⟨m - 1, ?_⟩
  have hn3 : 3 ≤ m - 1 := by omega
  have hpm : m + 2 ≤ p := by omega
  -- (m:ℤ)^2 - 5 ≥ 0 and = ↑(m^2 - 5)
  have hm5 : 5 ≤ m^2 := by nlinarith [hm4]
  have hcastsub : ((m^2 - 5 : ℕ) : ℤ) = (m:ℤ)^2 - 5 := by
    push_cast [Nat.cast_sub hm5]; ring
  -- p ∣ (m^2 - 5) in ℕ
  have hdvdN : p ∣ (m^2 - 5) := by
    have : (p:ℤ) ∣ ((m^2 - 5 : ℕ) : ℤ) := by rw [hcastsub]; exact hmdvd
    exact_mod_cast this
  set t := (m^2 - 5) / p with htdef
  have hpt : p * t = m^2 - 5 := Nat.mul_div_cancel' hdvdN
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · exfalso; rw [h, mul_zero] at hpt; nlinarith [hm4]
    · exact h
  -- the integer identity X2 = p t  (with n = m-1, n+1 = m)
  have hn1 : ((m - 1 : ℕ) : ℤ) + 1 = (m:ℤ) := by
    have : (1:ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub this]; ring
  have hPTeq : (m:ℤ)^2 - 5 = (p:ℤ) * (t:ℤ) := by
    have h : ((m^2 - 5 : ℕ) : ℤ) = (p:ℤ) * (t:ℤ) := by exact_mod_cast hpt.symm
    rw [hcastsub] at h; exact h
  have hPT : (((m-1:ℕ):ℤ)+1)^2 - 5 = (p:ℤ) * (t:ℤ) := by rw [hn1]; exact hPTeq
  have hpmi : (m:ℤ) + 2 ≤ (p:ℤ) := by exact_mod_cast hpm
  -- t ≤ n - 1 = m - 2
  have htle : t ≤ (m - 1) - 1 := by
    have hkey : ((m:ℤ)+2) * (t:ℤ) ≤ (m:ℤ)^2 - 5 := by
      have h1 : ((m:ℤ)+2)*(t:ℤ) ≤ (p:ℤ)*(t:ℤ) :=
        mul_le_mul_of_nonneg_right hpmi (by exact_mod_cast Nat.zero_le t)
      rw [hPTeq]; exact h1
    have hti : (t:ℤ) ≤ (m:ℤ) - 2 := by nlinarith [hkey, hpmi]
    omega
  -- t is odd
  have htodd : Odd t := by
    have hmsq_odd : Odd (m^2 - 5) := by
      rcases hmeven with ⟨c, hc⟩
      refine Nat.Even.sub_odd ?_ ?_ ?_
      · exact hm5
      · exact ⟨c*c*2, by rw [hc]; ring⟩
      · decide
    rw [← hpt] at hmsq_odd
    exact (Nat.odd_mul.mp hmsq_odd).2
  -- coprimality:  IsCoprime ((n:ℤ)-2) (t:ℤ) = IsCoprime ((m:ℤ)-3) t
  have hcop : IsCoprime (((m-1:ℕ):ℤ) - 2) (t:ℤ) := by
    obtain ⟨k, hk⟩ := htodd
    have h2cop : IsCoprime (2:ℤ) (t:ℤ) := ⟨-(k:ℤ), 1, by push_cast [hk]; ring⟩
    have h4cop : IsCoprime ((2:ℤ)*2) (t:ℤ) := h2cop.mul_left h2cop
    obtain ⟨a, b, hab⟩ := h4cop
    rw [show (2:ℤ)*2 = 4 from by norm_num] at hab
    have hPTeq : (m:ℤ)^2 - 5 = (p:ℤ) * (t:ℤ) := by
      rw [← hn1] at *; linarith [hPT]
    have hnm : ((m-1:ℕ):ℤ) - 2 = (m:ℤ) - 3 := by rw [show ((m-1:ℕ):ℤ) = (m:ℤ)-1 from by omega]; ring
    rw [hnm]
    exact ⟨a * (-((m:ℤ)+3)), a * (p:ℤ) + b, by linear_combination (-a) * hPTeq + hab⟩
  exact construction (m-1) p t hn3 hp htpos hPT htle hcop (by omega)

end A363
