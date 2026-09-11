import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

/--
A185895: Exponential generating function is $\prod_{k>0} (1 - x^k/k!).$
The $n$-th term is
$$ a(n) = n! \cdot \left[x^n\right] \left( \prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right) \right) $$
The coefficients $a(n)$ are integers.
-/
noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  -- n! is defined for n=0, and Px_0 is 1, so a(0) = 1.
  -- We handle n=0 explicitly to avoid issues with 0.factorial.cast in the general case if k=0 were included.

  -- The finite product $\prod_{k=1}^n \left(1 - \frac{x^k}{k!}\right)$ is equivalent to the infinite product for the coefficient of $x^n$.
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    -- Factor is $1 - x^k/k!$.
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)

  -- $[x^n] Px$ is the coefficient of $x^n$.
  let coeff_n : ℚ := Polynomial.coeff Px n

  -- $a(n) = n! \cdot [x^n] Px$.
  let a_n_q : ℚ := coeff_n * n.factorial.cast

  -- The result is an integer, so Rat.floor converts the rational value to ℤ.
  a_n_q.floor

/-- A natural number $n$ is a triangular number if it is of the form $k(k+1)/2$ for some $k \in \mathbb{N}$. -/
def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2


/- # Proof of the conjecture -/

namespace A185895Proof
open Finset

/- ## Part C: the relaxed recursion `F` and its analytic majorants -/

def F (S : ℕ) : ℕ → ℕ → ℕ → ℚ
  | 0, _, _ => 1
  | k+1, t, M => F S k (M+1) (M+1) / (M+1) + if S + 2 ≤ t then F S k (t-1) M / (t-1) else 0

def cst (S b m : ℕ) : ℚ := 1 / (Nat.descFactorial (max (m-1) (S+b)) b : ℚ)
def zeta (S b : ℕ) : ℚ := 1 / (Nat.descFactorial (S+b) b : ℚ)

def run (S : ℕ) : ℕ → ℕ → ℕ → ℚ
  | 0, b, m => cst S b m
  | r+1, b, m => run S r (b+1) m + cst S b m * run S r 0 (m+1) / (m+1)

def init (S : ℕ) : ℕ → ℕ → ℕ → ℕ → ℚ
  | 0, b, t, _ => 1 / (Nat.descFactorial (t-1) b : ℚ)
  | r+1, b, t, m => (if S + 1 ≤ t - (b+1) then init S r (b+1) t m else 0)
      + (1 / (Nat.descFactorial (t-1) b : ℚ)) * run S r 0 (m+1) / (m+1)

def lrun (S : ℕ) : ℕ → ℕ → ℕ → ℚ
  | 0, b, _ => zeta S b
  | r+1, b, t => lrun S r (b+1) t + zeta S b * lrun S r 0 t / (t+1)

lemma F_nonneg (S : ℕ) : ∀ k t M, 0 ≤ F S k t M := by
  intro k
  induction k with
  | zero => intro t M; simp [F]
  | succ k ih =>
    intro t M
    simp only [F]
    have h1 := ih (M+1) (M+1)
    have h2 := ih (t-1) M
    have : (0:ℚ) ≤ (M:ℚ) + 1 := by positivity
    apply add_nonneg
    · exact div_nonneg h1 this
    · split_ifs with h
      · apply div_nonneg h2
        have : (1:ℚ) ≤ (t:ℚ) := by exact_mod_cast (by omega : 1 ≤ t)
        linarith
      · exact le_refl 0

lemma cst_nonneg (S b m : ℕ) : 0 ≤ cst S b m := by unfold cst; positivity
lemma zeta_nonneg (S b : ℕ) : 0 ≤ zeta S b := by unfold zeta; positivity

lemma run_nonneg (S : ℕ) : ∀ r b m, 0 ≤ run S r b m := by
  intro r
  induction r with
  | zero => intro b m; simp [run, cst_nonneg]
  | succ r ih =>
    intro b m
    simp only [run]
    have := ih (b+1) m
    have := ih 0 (m+1)
    have := cst_nonneg S b m
    positivity

lemma lrun_nonneg (S : ℕ) : ∀ r b t, 0 ≤ lrun S r b t := by
  intro r
  induction r with
  | zero => intro b t; simp [lrun, zeta_nonneg]
  | succ r ih =>
    intro b t
    simp only [lrun]
    have := ih (b+1) t
    have := ih 0 t
    have := zeta_nonneg S b
    positivity

lemma init_nonneg (S : ℕ) : ∀ r b t m, 0 ≤ init S r b t m := by
  intro r
  induction r with
  | zero => intro b t m; simp only [init]; positivity
  | succ r ih =>
    intro b t m
    simp only [init]
    have := ih (b+1) t m
    have := run_nonneg S r 0 (m+1)
    apply add_nonneg
    · split_ifs <;> simp [*]
    · positivity

/-- inverse of descFactorial is antitone in the base -/
lemma inv_descFactorial_le {a b k : ℕ} (h : a ≤ b) (hk : k ≤ a) :
    (1 : ℚ) / (Nat.descFactorial b k : ℚ) ≤ 1 / (Nat.descFactorial a k : ℚ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.descFactorial_pos.mpr hk
  · exact_mod_cast Nat.descFactorial_le k h

lemma one_div_descFactorial_le_cst {T b m S : ℕ} (h1 : m ≤ T + b) (h2 : 1 ≤ b → S + 1 ≤ T) :
    (1 : ℚ) / (Nat.descFactorial (T + b - 1) b : ℚ) ≤ cst S b m := by
  unfold cst
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  · have hT := h2 hb
    apply inv_descFactorial_le
    · apply max_le <;> omega
    · omega

/-- Key: `F` is bounded by the M-free `run` -/
lemma F_le_run (S : ℕ) : ∀ k b T M' m, S ≤ m → m ≤ T + b → m ≤ M' → (1 ≤ b → S + 1 ≤ T) →
    F S k T M' / (Nat.descFactorial (T + b - 1) b : ℚ) ≤ run S k b m := by
  intro k
  induction k with
  | zero =>
    intro b T M' m _ h1 _ h2
    simp only [F, run]
    exact one_div_descFactorial_le_cst h1 h2
  | succ k ih =>
    intro b T M' m hS h1 hM h2
    simp only [F, run]
    rw [add_div, add_comm]
    apply _root_.add_le_add
    · -- B branch: matches run S k (b+1) m
      split_ifs with ht
      · have hD : (Nat.descFactorial (T - 1 + (b+1) - 1) (b+1) : ℚ)
            = ((T:ℚ) - 1) * (Nat.descFactorial (T + b - 1) b : ℚ) := by
          have e1 : T - 1 + (b+1) - 1 = T + b - 1 := by omega
          rw [e1, Nat.descFactorial_succ]
          have e2 : T + b - 1 - b = T - 1 := by omega
          rw [e2]
          push_cast [Nat.cast_sub (by omega : 1 ≤ T)]
          ring
        have := ih (b+1) (T-1) M' m hS (by omega) hM (fun _ => by omega)
        rw [hD] at this
        have hT1 : (0:ℚ) < (T:ℚ) - 1 := by
          have : (2:ℚ) ≤ (T:ℚ) := by exact_mod_cast (by omega : 2 ≤ T)
          linarith
        have hDpos : (0:ℚ) < (Nat.descFactorial (T + b - 1) b : ℚ) := by
          exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
        calc F S k (T - 1) M' / ((T:ℚ) - 1) / (Nat.descFactorial (T + b - 1) b : ℚ)
            = F S k (T - 1) M' / (((T:ℚ) - 1) * (Nat.descFactorial (T + b - 1) b : ℚ)) := by
              rw [div_div]
          _ ≤ run S k (b+1) m := this
      · rw [zero_div]; exact run_nonneg S k (b+1) m
    · -- A branch
      have ih' := ih 0 (M'+1) (M'+1) (m+1) (by omega) (by omega) (by omega) (fun h => by omega)
      simp only [Nat.descFactorial_zero, Nat.cast_one, div_one] at ih'
      have hc := one_div_descFactorial_le_cst (S := S) h1 h2
      have hDpos : (0:ℚ) < (Nat.descFactorial (T + b - 1) b : ℚ) := by
        exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
      have hFnn := F_nonneg S k (M'+1) (M'+1)
      have hm : (0:ℚ) < (m:ℚ) + 1 := by positivity
      have hM' : (m:ℚ) + 1 ≤ (M':ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ hM
      calc F S k (M' + 1) (M' + 1) / ((M':ℚ) + 1) / (Nat.descFactorial (T + b - 1) b : ℚ)
          = (1 / (Nat.descFactorial (T + b - 1) b : ℚ)) * F S k (M' + 1) (M' + 1) / ((M':ℚ) + 1) := by
            ring
        _ ≤ cst S b m * run S k 0 (m+1) / ((M':ℚ) + 1) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            exact mul_le_mul hc ih' hFnn (cst_nonneg S b m)
        _ ≤ cst S b m * run S k 0 (m+1) / ((m:ℚ) + 1) := by
            apply div_le_div_of_nonneg_left _ hm hM'
            exact mul_nonneg (cst_nonneg S b m) (run_nonneg S k 0 (m+1))


/-- `F` from the exact initial state `(t, M')` is bounded by `init` -/
lemma F_le_init (S : ℕ) : ∀ k b t M' m, S ≤ m → m ≤ M' → (1 ≤ b → S + 1 ≤ t - b) →
    F S k (t - b) M' / (Nat.descFactorial (t - 1) b : ℚ) ≤ init S k b t m := by
  intro k
  induction k with
  | zero =>
    intro b t M' m _ _ _
    simp only [F, init]; exact le_refl _
  | succ k ih =>
    intro b t M' m hS hM h2
    simp only [F, init]
    rw [add_div, add_comm]
    apply _root_.add_le_add
    · split_ifs with ht ht' ht'
      · have hD : (Nat.descFactorial (t - 1) (b+1) : ℚ)
            = ((↑(t - b) : ℚ) - 1) * (Nat.descFactorial (t - 1) b : ℚ) := by
          rw [Nat.descFactorial_succ]
          have e2 : t - 1 - b = t - b - 1 := by omega
          rw [e2]
          push_cast [Nat.cast_sub (by omega : 1 ≤ t - b)]
          ring
        have := ih (b+1) t M' m hS hM (fun _ => by omega)
        rw [hD] at this
        have e3 : t - (b+1) = t - b - 1 := by omega
        rw [e3] at this
        rw [div_div]
        exact this
      · omega
      · omega
      · rw [zero_div]
    · have ih' := F_le_run S k 0 (M'+1) (M'+1) (m+1) (by omega) (by omega) (by omega) (fun h => by omega)
      simp only [Nat.descFactorial_zero, Nat.cast_one, div_one] at ih'
      have hDpos : (0:ℚ) < (Nat.descFactorial (t - 1) b : ℚ) := by
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb; simp
        · exact_mod_cast Nat.descFactorial_pos.mpr (by have := h2 hb; omega)
      have hFnn := F_nonneg S k (M'+1) (M'+1)
      have hm : (0:ℚ) < (m:ℚ) + 1 := by positivity
      have hM' : (m:ℚ) + 1 ≤ (M':ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ hM
      calc F S k (M' + 1) (M' + 1) / ((M':ℚ) + 1) / (Nat.descFactorial (t - 1) b : ℚ)
          = (1 / (Nat.descFactorial (t - 1) b : ℚ)) * F S k (M' + 1) (M' + 1) / ((M':ℚ) + 1) := by
            ring
        _ ≤ (1 / (Nat.descFactorial (t - 1) b : ℚ)) * run S k 0 (m+1) / ((M':ℚ) + 1) := by
            apply div_le_div_of_nonneg_right _ (by linarith)
            exact mul_le_mul_of_nonneg_left ih' (by positivity)
        _ ≤ (1 / (Nat.descFactorial (t - 1) b : ℚ)) * run S k 0 (m+1) / ((m:ℚ) + 1) := by
            apply div_le_div_of_nonneg_left _ hm hM'
            exact mul_nonneg (by positivity) (run_nonneg S k 0 (m+1))

lemma cst_le_zeta (S b m : ℕ) : cst S b m ≤ zeta S b := by
  unfold cst zeta
  apply inv_descFactorial_le (le_max_right _ _) (by omega)

lemma run_le_lrun (S : ℕ) : ∀ r b m t', t' ≤ m → run S r b m ≤ lrun S r b t' := by
  intro r
  induction r with
  | zero => intro b m t' _; simp only [run, lrun]; exact cst_le_zeta S b m
  | succ r ih =>
    intro b m t' h
    simp only [run, lrun]
    apply _root_.add_le_add (ih (b+1) m t' h)
    have h1 := ih 0 (m+1) t' (by omega)
    have ht : (t':ℚ) + 1 ≤ (m:ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ h
    calc cst S b m * run S r 0 (m+1) / ((m:ℚ) + 1)
        ≤ zeta S b * lrun S r 0 t' / ((m:ℚ) + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul (cst_le_zeta S b m) h1 (run_nonneg _ _ _ _) (zeta_nonneg _ _)
      _ ≤ zeta S b * lrun S r 0 t' / ((t':ℚ) + 1) := by
          apply div_le_div_of_nonneg_left _ (by positivity) ht
          exact mul_nonneg (zeta_nonneg _ _) (lrun_nonneg _ _ _ _)

lemma lrun_anti (S : ℕ) : ∀ r b t t', t ≤ t' → lrun S r b t' ≤ lrun S r b t := by
  intro r
  induction r with
  | zero => intro b t t' _; simp only [lrun]; exact le_refl _
  | succ r ih =>
    intro b t t' h
    simp only [lrun]
    apply _root_.add_le_add (ih (b+1) t t' h)
    have h1 := ih 0 t t' h
    have ht : (t:ℚ) + 1 ≤ (t':ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ h
    calc zeta S b * lrun S r 0 t' / ((t':ℚ) + 1)
        ≤ zeta S b * lrun S r 0 t / ((t':ℚ) + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h1 (zeta_nonneg _ _)
      _ ≤ zeta S b * lrun S r 0 t / ((t:ℚ) + 1) := by
          apply div_le_div_of_nonneg_left _ (by positivity) ht
          exact mul_nonneg (zeta_nonneg _ _) (lrun_nonneg _ _ _ _)

lemma init_le_lrun (S : ℕ) : ∀ r b t m t', t' ≤ m → (1 ≤ b → S + 1 ≤ t - b) →
    init S r b t m ≤ lrun S r b t' := by
  intro r
  induction r with
  | zero =>
    intro b t m t' _ h2
    simp only [init, lrun, zeta]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp
    · exact inv_descFactorial_le (by have := h2 hb; omega) (by omega)
  | succ r ih =>
    intro b t m t' h h2
    simp only [init, lrun]
    apply _root_.add_le_add
    · split_ifs with ht
      · exact ih (b+1) t m t' h (fun _ => ht)
      · exact lrun_nonneg _ _ _ _
    · have h1 := (run_le_lrun S r 0 (m+1) t' (by omega))
      have ht : (t':ℚ) + 1 ≤ (m:ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ h
      have hz : (1 : ℚ) / (Nat.descFactorial (t - 1) b : ℚ) ≤ zeta S b := by
        unfold zeta
        rcases Nat.eq_zero_or_pos b with hb | hb
        · subst hb; simp
        · exact inv_descFactorial_le (by have := h2 hb; omega) (by omega)
      calc (1 : ℚ) / (Nat.descFactorial (t - 1) b : ℚ) * run S r 0 (m+1) / ((m:ℚ) + 1)
          ≤ zeta S b * lrun S r 0 t' / ((m:ℚ) + 1) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul hz h1 (run_nonneg _ _ _ _) (zeta_nonneg _ _)
        _ ≤ zeta S b * lrun S r 0 t' / ((t':ℚ) + 1) := by
            apply div_le_div_of_nonneg_left _ (by positivity) ht
            exact mul_nonneg (zeta_nonneg _ _) (lrun_nonneg _ _ _ _)

lemma zeta_le_pow (S b : ℕ) : zeta S b ≤ 1 / ((S:ℚ) + 1) ^ b := by
  unfold zeta
  apply one_div_le_one_div_of_le (by positivity)
  have := Nat.pow_sub_le_descFactorial (S + b) b
  have e : S + b + 1 - b = S + 1 := by omega
  rw [e] at this
  exact_mod_cast this

lemma cst_le_pow (S b m : ℕ) : cst S b m ≤ 1 / ((S:ℚ) + 1) ^ b :=
  le_trans (cst_le_zeta S b m) (zeta_le_pow S b)

lemma run_le_pow (S : ℕ) : ∀ r b m, S ≤ m → run S r b m ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + b) := by
  intro r
  induction r with
  | zero => intro b m _; simp only [run, pow_zero, zero_add]; exact cst_le_pow S b m
  | succ r ih =>
    intro b m hS
    simp only [run]
    have h1 := ih (b+1) m hS
    have h2 := ih 0 (m+1) (by omega)
    have hc := cst_le_pow S b m
    have hSpos : (0:ℚ) < (S:ℚ) + 1 := by positivity
    have hm : (S:ℚ) + 1 ≤ (m:ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ hS
    have h3 : cst S b m * run S r 0 (m+1) / ((m:ℚ) + 1) ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + b + 1) := by
      calc cst S b m * run S r 0 (m+1) / ((m:ℚ) + 1)
          ≤ (1 / ((S:ℚ) + 1) ^ b) * (2 ^ r / ((S:ℚ) + 1) ^ (r + 0)) / ((S:ℚ) + 1) := by
            apply div_le_div₀ (by positivity) _ (by positivity) hm
            exact mul_le_mul hc h2 (run_nonneg _ _ _ _) (by positivity)
        _ = 2 ^ r / ((S:ℚ) + 1) ^ (r + b + 1) := by
            rw [add_zero]; field_simp; ring
    have e : r + 1 + b = r + (b + 1) := by ring
    rw [e]
    calc run S r (b + 1) m + cst S b m * run S r 0 (m + 1) / ((m:ℚ) + 1)
        ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + (b+1)) + 2 ^ r / ((S:ℚ) + 1) ^ (r + b + 1) := _root_.add_le_add h1 h3
      _ = 2 ^ (r+1) / ((S:ℚ) + 1) ^ (r + (b + 1)) := by
          rw [show r + b + 1 = r + (b+1) by ring]; ring

lemma init_le_pow (S : ℕ) : ∀ r b t m, S ≤ m → (1 ≤ b → S + 1 ≤ t - b) →
    init S r b t m ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + b) := by
  intro r
  induction r with
  | zero =>
    intro b t m _ h2
    simp only [init, pow_zero, zero_add]
    apply one_div_le_one_div_of_le (by positivity)
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp
    · have := Nat.pow_sub_le_descFactorial (S + b) b
      have e : S + b + 1 - b = S + 1 := by omega
      rw [e] at this
      have h3 := Nat.descFactorial_le b (show S + b ≤ t - 1 by have := h2 hb; omega)
      exact_mod_cast le_trans this h3
  | succ r ih =>
    intro b t m hS h2
    simp only [init]
    have hSpos : (0:ℚ) < (S:ℚ) + 1 := by positivity
    have hz : (1 : ℚ) / (Nat.descFactorial (t - 1) b : ℚ) ≤ 1 / ((S:ℚ) + 1) ^ b := by
      apply one_div_le_one_div_of_le (by positivity)
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; simp
      · have := Nat.pow_sub_le_descFactorial (S + b) b
        have e : S + b + 1 - b = S + 1 := by omega
        rw [e] at this
        have h3 := Nat.descFactorial_le b (show S + b ≤ t - 1 by have := h2 hb; omega)
        exact_mod_cast le_trans this h3
    have h2' := run_le_pow S r 0 (m+1) (by omega)
    have hm : (S:ℚ) + 1 ≤ (m:ℚ) + 1 := by exact_mod_cast Nat.succ_le_succ hS
    have h3 : (1 : ℚ) / (Nat.descFactorial (t - 1) b : ℚ) * run S r 0 (m+1) / ((m:ℚ) + 1)
        ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + b + 1) := by
      calc (1 : ℚ) / (Nat.descFactorial (t - 1) b : ℚ) * run S r 0 (m+1) / ((m:ℚ) + 1)
          ≤ (1 / ((S:ℚ) + 1) ^ b) * (2 ^ r / ((S:ℚ) + 1) ^ (r + 0)) / ((S:ℚ) + 1) := by
            apply div_le_div₀ (by positivity) _ (by positivity) hm
            exact mul_le_mul hz h2' (run_nonneg _ _ _ _) (by positivity)
        _ = 2 ^ r / ((S:ℚ) + 1) ^ (r + b + 1) := by
            rw [add_zero]; field_simp; ring
    have h1 : (if S + 1 ≤ t - (b + 1) then init S r (b + 1) t m else 0)
        ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + (b+1)) := by
      split_ifs with ht
      · exact ih (b+1) t m hS (fun _ => ht)
      · positivity
    have e : r + 1 + b = r + (b + 1) := by ring
    rw [e]
    calc _ ≤ 2 ^ r / ((S:ℚ) + 1) ^ (r + (b+1)) + 2 ^ r / ((S:ℚ) + 1) ^ (r + b + 1) := _root_.add_le_add h1 h3
      _ = 2 ^ (r+1) / ((S:ℚ) + 1) ^ (r + (b + 1)) := by
          rw [show r + b + 1 = r + (b+1) by ring]; ring


/- ### the tail sequence `u` -/

def u (s : ℕ) : ℚ := (s.factorial : ℚ) * 2 ^ s / ((s:ℚ) + 2) ^ s

lemma binom3 (x : ℚ) (hx : 0 ≤ x) : ∀ n : ℕ,
    x ^ (n+2) + n * x ^ (n+1) + ((n:ℚ) * (n - 1) / 2) * x ^ n ≤ x ^ 2 * (x + 1) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ x + 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left ih h1
    have hxn : 0 ≤ x ^ n := pow_nonneg hx n
    have hnn : (0:ℚ) ≤ (n:ℚ) * (n - 1) / 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : (1:ℚ) ≤ n := by exact_mod_cast h
        apply div_nonneg _ (by norm_num)
        apply mul_nonneg (by positivity); linarith
    have e : x ^ 2 * (x + 1) ^ (n + 1) = (x + 1) * (x ^ 2 * (x + 1) ^ n) := by ring
    rw [e]
    push_cast
    have := mul_nonneg hnn hxn
    have e2 : x ^ (n + 1 + 2) + ((n:ℚ) + 1) * x ^ (n + 1 + 1) + (((n:ℚ) + 1) * ((n:ℚ) + 1 - 1) / 2) * x ^ (n + 1)
        = (x + 1) * (x ^ (n+2) + n * x ^ (n+1) + ((n:ℚ) * (n - 1) / 2) * x ^ n) - ((n:ℚ) * (n - 1) / 2) * x ^ n := by
      ring
    rw [e2]
    linarith

lemma u_pos (s : ℕ) : 0 < u s := by unfold u; positivity

lemma u_ratio (s : ℕ) : 5 * u (s + 1) ≤ 4 * u s := by
  unfold u
  have hb := binom3 ((s:ℚ) + 2) (by positivity) s
  have hpos : (0:ℚ) < ((s:ℚ) + 2) ^ s := by positivity
  have hpos3 : (0:ℚ) < ((s:ℚ) + 3) ^ (s+1) := by positivity
  have hf : (0:ℚ) < (s.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos s
  have h2 : (0:ℚ) < (2:ℚ) ^ s := by positivity
  rw [Nat.factorial_succ]
  push_cast
  simp only [← mul_div_assoc]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : ((s:ℚ) + 1 + 2) = (s:ℚ) + 3 := by ring
  rw [e1]
  -- reduce to polynomial inequality
  have key : 5 * ((s:ℚ) + 1) * ((s:ℚ) + 2) ^ s ≤ 2 * ((s:ℚ) + 3) ^ (s + 1) := by
    have e2 : ((s:ℚ) + 3) ^ (s+1) = ((s:ℚ) + 3) * (((s:ℚ)+2) + 1) ^ s := by ring
    rw [e2]
    have e3 : ((s:ℚ) + 2) ^ (s+2) = ((s:ℚ)+2)^2 * ((s:ℚ) + 2) ^ s := by ring
    have e4 : ((s:ℚ) + 2) ^ (s+1) = ((s:ℚ)+2) * ((s:ℚ) + 2) ^ s := by ring
    rw [e3, e4] at hb
    have hs : (0:ℚ) ≤ s := by positivity
    nlinarith [hb, hpos, hs, mul_nonneg hs hpos.le, mul_nonneg (mul_nonneg hs hs) hpos.le]
  have e5 : ((s:ℚ) + 2) ^ (s+1) = ((s:ℚ) + 2) * ((s:ℚ) + 2) ^ s := by ring
  have e6 : (2:ℚ) ^ (s+1) = 2 * 2 ^ s := by ring
  rw [e6]
  nlinarith [key, hf, h2, hpos, hpos3, mul_pos hf h2, mul_pos (mul_pos hf h2) hpos]

lemma u_tail (a : ℕ) : ∀ N, a ≤ N + 1 → (∑ s ∈ Icc a N, u s) + 5 * u (N+1) ≤ 5 * u a := by
  intro N
  induction N with
  | zero =>
    intro h
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
    · subst h; simp
      have := u_ratio 0; simp at this; linarith
    · subst h; simp
  | succ N ih =>
    intro h
    rcases Nat.lt_or_ge (N+1) a with hlt | hge
    · have : a = N + 2 := by omega
      subst this
      simp
    · have := ih hge
      rw [Finset.sum_Icc_succ_top hge]
      have := u_ratio (N+1)
      linarith

lemma u_tail' (a N : ℕ) : (∑ s ∈ Icc a N, u s) ≤ 5 * u a := by
  rcases Nat.lt_or_ge (N+1) a with hlt | hge
  · rw [Finset.Icc_eq_empty (by omega)]; simp; exact (u_pos a).le
  · have := u_tail a N hge
    have := u_pos (N+1)
    linarith

/- ### the finite computations -/

def Gt (t : ℕ) : ℚ := ∑ s ∈ Icc 1 (t-2), (s.factorial : ℚ) * init (s+1) s 0 t t
def C1 : ℚ := ∑ s ∈ Icc 1 12, (s.factorial : ℚ) * lrun (s+1) s 0 17
def G0t (j : ℕ) : ℚ := ∑ s ∈ Icc 1 (j-1), (s.factorial : ℚ) * run (s+1) (s-1) 0 (j+1) / ((j:ℚ)+1)
def C0 : ℚ := ∑ s ∈ Icc 1 12, (s.factorial : ℚ) * lrun (s+1) (s-1) 0 18 / 18

lemma Gt_small : ∀ t ∈ Icc 0 16, Gt t ≤ 9/10 := by decide +kernel
lemma G0t_small : ∀ j ∈ Icc 0 16, G0t j ≤ 9/10 := by decide +kernel
lemma C1_bound : C1 + 5 * u 13 ≤ 9/10 := by decide +kernel
lemma C0_bound : C0 + 5 * u 13 / 2 ≤ 9/10 := by decide +kernel


lemma Icc_split (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) (f : ℕ → ℚ) :
    ∑ s ∈ Icc a c, f s = ∑ s ∈ Icc a b, f s + ∑ s ∈ Icc (b+1) c, f s := by
  have e : Icc a c = Icc a b ∪ Icc (b+1) c := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  rw [e, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Icc] at hx hx'
  omega

lemma cast_succ_add_one (s : ℕ) : (((s + 1 : ℕ) : ℚ) + 1) = (s:ℚ) + 2 := by push_cast; ring

theorem sumF_le (t M : ℕ) (h : t ≤ M) :
    ∑ s ∈ Icc 1 (t-2), (s.factorial : ℚ) * F (s+1) s t M ≤ 9/10 := by
  have hG : ∑ s ∈ Icc 1 (t-2), (s.factorial : ℚ) * F (s+1) s t M ≤ Gt t := by
    unfold Gt
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := F_le_init (s+1) s 0 t M t (by omega) h (fun h => by omega)
    simpa using this
  rcases Nat.lt_or_ge t 17 with ht | ht
  · exact le_trans hG (Gt_small t (by simp; omega))
  · apply le_trans hG
    unfold Gt
    rw [Icc_split 1 12 (t-2) (by omega) (by omega)]
    have hA : ∑ s ∈ Icc 1 12, (s.factorial : ℚ) * init (s+1) s 0 t t ≤ C1 := by
      unfold C1
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact init_le_lrun (s+1) s 0 t t 17 ht (fun h => by omega)
    have hB : ∑ s ∈ Icc 13 (t-2), (s.factorial : ℚ) * init (s+1) s 0 t t ≤ 5 * u 13 := by
      apply le_trans _ (u_tail' 13 (t-2))
      apply Finset.sum_le_sum
      intro s hs
      rw [Finset.mem_Icc] at hs
      unfold u
      have := init_le_pow (s+1) s 0 t t (by omega) (fun h => by omega)
      rw [add_zero, cast_succ_add_one] at this
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have := C1_bound
    linarith

theorem sumF0_le (j : ℕ) :
    ∑ s ∈ Icc 1 (j-1), (s.factorial : ℚ) * F (s+1) s (s+1) j ≤ 9/10 := by
  have hG : ∑ s ∈ Icc 1 (j-1), (s.factorial : ℚ) * F (s+1) s (s+1) j ≤ G0t j := by
    unfold G0t
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    simp only [F, Nat.add_sub_cancel]
    rw [if_neg (by omega), add_zero]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := F_le_run (s'+1+1) s' 0 (j+1) (j+1) (j+1) (by omega) (by omega) (by omega) (fun h => by omega)
    simpa using this
  rcases Nat.lt_or_ge j 17 with hj | hj
  · exact le_trans hG (G0t_small j (by simp; omega))
  · apply le_trans hG
    unfold G0t
    rw [Icc_split 1 12 (j-1) (by omega) (by omega)]
    have hA : ∑ s ∈ Icc 1 12, (s.factorial : ℚ) * run (s+1) (s-1) 0 (j+1) / ((j:ℚ)+1) ≤ C0 := by
      unfold C0
      apply Finset.sum_le_sum
      intro s hs
      have h1 := run_le_lrun (s+1) (s-1) 0 (j+1) 18 (by omega)
      have h18 : (18:ℚ) ≤ (j:ℚ) + 1 := by
        have : (17:ℚ) ≤ (j:ℚ) := by exact_mod_cast hj
        linarith
      calc (s.factorial : ℚ) * run (s+1) (s-1) 0 (j+1) / ((j:ℚ)+1)
          ≤ (s.factorial : ℚ) * lrun (s+1) (s-1) 0 18 / ((j:ℚ)+1) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (s.factorial : ℚ) * lrun (s+1) (s-1) 0 18 / 18 := by
            apply div_le_div_of_nonneg_left _ (by norm_num) h18
            exact mul_nonneg (by positivity) (lrun_nonneg _ _ _ _)
    have hB : ∑ s ∈ Icc 13 (j-1), (s.factorial : ℚ) * run (s+1) (s-1) 0 (j+1) / ((j:ℚ)+1)
        ≤ 5 * u 13 / 2 := by
      have : ∑ s ∈ Icc 13 (j-1), (s.factorial : ℚ) * run (s+1) (s-1) 0 (j+1) / ((j:ℚ)+1)
          ≤ ∑ s ∈ Icc 13 (j-1), u s / 2 := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.mem_Icc] at hs
        have h1 := run_le_pow (s+1) (s-1) 0 (j+1) (by omega)
        rw [add_zero, cast_succ_add_one] at h1
        have hs2 : (s:ℚ) + 2 ≤ (j:ℚ) + 1 := by
          have : ((s:ℚ) + 1) ≤ (j:ℚ) := by exact_mod_cast (by omega : s + 1 ≤ j)
          linarith
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at h1 ⊢
        unfold u
        push_cast at hs2 h1 ⊢
        have hpos : (0:ℚ) < ((s':ℚ) + 1 + 2) := by positivity
        calc ((s' + 1).factorial : ℚ) * run (s'+1+1) s' 0 (j+1) / ((j:ℚ)+1)
            ≤ ((s' + 1).factorial : ℚ) * (2 ^ s' / ((s':ℚ) + 1 + 2) ^ s') / ((j:ℚ)+1) := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ ((s' + 1).factorial : ℚ) * (2 ^ s' / ((s':ℚ) + 1 + 2) ^ s') / ((s':ℚ) + 1 + 2) := by
              apply div_le_div_of_nonneg_left _ hpos hs2
              positivity
          _ = ((s' + 1).factorial : ℚ) * 2 ^ (s'+1) / ((s':ℚ) + 1 + 2) ^ (s'+1) / 2 := by
              field_simp; ring
      apply le_trans this
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right (u_tail' 13 (j-1)) (by norm_num)
    have := C0_bound
    linarith

end A185895Proof

namespace A185895Proof
open Finset
open scoped Classical

/- ## Part A: sets, weights, the map ρ and its preimages -/

def Pf (X : Finset ℕ) : ℚ := ∏ x ∈ X, (x.factorial : ℚ)

lemma Pf_pos (X : Finset ℕ) : 0 < Pf X := by
  unfold Pf
  apply Finset.prod_pos
  intro x _
  exact_mod_cast Nat.factorial_pos x

lemma Pf_insert {X : Finset ℕ} {a : ℕ} (h : a ∉ X) : Pf (insert a X) = (a.factorial : ℚ) * Pf X := by
  unfold Pf; rw [Finset.prod_insert h]

lemma Pf_erase {X : Finset ℕ} {a : ℕ} (h : a ∈ X) : Pf X = (a.factorial : ℚ) * Pf (X.erase a) := by
  unfold Pf; rw [← Finset.mul_prod_erase X _ h]

lemma Pf_union {A B : Finset ℕ} (h : Disjoint A B) : Pf (A ∪ B) = Pf A * Pf B := by
  unfold Pf; rw [Finset.prod_union h]

/-- maximum (0 for the empty set) -/
def mx (X : Finset ℕ) : ℕ := X.sup id

lemma le_mx {X : Finset ℕ} {x : ℕ} (h : x ∈ X) : x ≤ mx X := Finset.le_sup (f := id) h

lemma mx_mem {X : Finset ℕ} (h : X.Nonempty) : mx X ∈ X := by
  obtain ⟨i, hi, hix⟩ := Finset.exists_mem_eq_sup X h id
  unfold mx; rw [hix]; exact hi

lemma mx_eq_of {X : Finset ℕ} {a : ℕ} (ha : a ∈ X) (h : ∀ x ∈ X, x ≤ a) : mx X = a :=
  le_antisymm (Finset.sup_le h) (le_mx ha)

/-- the predicate defining the bottom of the top run -/
def trP (X : Finset ℕ) (t : ℕ) : Prop := t ∈ X ∧ ∀ y, t ≤ y → y ≤ mx X → y ∈ X

lemma tr_exists {X : Finset ℕ} (h : X.Nonempty) : ∃ t, trP X t :=
  ⟨mx X, mx_mem h, fun y h1 h2 => by rw [le_antisymm h2 h1]; exact mx_mem h⟩

open Classical in
noncomputable def tr (X : Finset ℕ) : ℕ :=
  if h : X.Nonempty then Nat.find (tr_exists h) else 0

lemma tr_spec {X : Finset ℕ} (h : X.Nonempty) : trP X (tr X) := by
  unfold tr; rw [dif_pos h]; exact Nat.find_spec (tr_exists h)

lemma tr_min {X : Finset ℕ} (h : X.Nonempty) {t : ℕ} (ht : trP X t) : tr X ≤ t := by
  unfold tr; rw [dif_pos h]; exact Nat.find_min' (tr_exists h) ht

lemma tr_mem {X : Finset ℕ} (h : X.Nonempty) : tr X ∈ X := (tr_spec h).1

lemma tr_le_mx {X : Finset ℕ} (h : X.Nonempty) : tr X ≤ mx X := le_mx (tr_mem h)

lemma mem_of_tr_le {X : Finset ℕ} (h : X.Nonempty) {y : ℕ} (h1 : tr X ≤ y) (h2 : y ≤ mx X) : y ∈ X :=
  (tr_spec h).2 y h1 h2

lemma tr_pred_not_mem {X : Finset ℕ} (h : X.Nonempty) (h1 : 1 ≤ tr X) : tr X - 1 ∉ X := by
  intro hm
  have : trP X (tr X - 1) := by
    refine ⟨hm, fun y hy1 hy2 => ?_⟩
    rcases Nat.eq_or_lt_of_le hy1 with e | lt
    · rw [← e]; exact hm
    · exact mem_of_tr_le h (by omega) hy2
  have := tr_min h this
  omega

lemma tr_unique {X : Finset ℕ} (h : X.Nonempty) {t : ℕ} (ht : trP X t) (hp : 1 ≤ t → t - 1 ∉ X) :
    tr X = t := by
  have h1 := tr_min h ht
  rcases Nat.eq_or_lt_of_le h1 with e | lt
  · exact e
  · exfalso
    apply hp (by omega)
    exact mem_of_tr_le h (by omega) (by have := le_mx ht.1; omega)

/-- the map ρ -/
noncomputable def rho (X : Finset ℕ) : Finset ℕ :=
  if X.Nonempty then insert (tr X - 1) (X.erase (tr X)) else ∅

lemma rho_eq {X : Finset ℕ} (h : X.Nonempty) : rho X = insert (tr X - 1) (X.erase (tr X)) := by
  unfold rho; rw [if_pos h]

lemma card_rho (X : Finset ℕ) : (rho X).card = X.card := by
  by_cases h : X.Nonempty
  · rw [rho_eq h]
    rcases Nat.eq_zero_or_pos (tr X) with h0 | hpos
    · have : tr X - 1 = tr X := by omega
      rw [this, Finset.insert_erase (tr_mem h)]
    · rw [Finset.card_insert_of_notMem, Finset.card_erase_of_mem (tr_mem h)]
      · have : 1 ≤ X.card := Finset.card_pos.mpr h
        omega
      · intro hm
        rw [Finset.mem_erase] at hm
        exact tr_pred_not_mem h hpos hm.2
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h; simp [rho]

lemma sum_rho {X : Finset ℕ} (h : X.Nonempty) (h1 : 1 ≤ tr X) :
    ∑ x ∈ X, x = ∑ x ∈ rho X, x + 1 := by
  rw [rho_eq h, Finset.sum_insert, ← Finset.add_sum_erase X _ (tr_mem h)]
  · omega
  · intro hm
    rw [Finset.mem_erase] at hm
    exact tr_pred_not_mem h h1 hm.2

lemma rho_ge {X : Finset ℕ} {S : ℕ} (h : X.Nonempty) (hX : ∀ x ∈ X, S ≤ x) (ht : S + 1 ≤ tr X) :
    ∀ x ∈ rho X, S ≤ x := by
  intro x hx
  rw [rho_eq h, Finset.mem_insert, Finset.mem_erase] at hx
  rcases hx with e | ⟨_, hm⟩
  · omega
  · exact hX x hm

lemma rho_nonempty {X : Finset ℕ} (h : X.Nonempty) : (rho X).Nonempty := by
  rw [← Finset.card_pos, card_rho]; exact Finset.card_pos.mpr h

/-- the two candidate preimages -/
def Amap (X : Finset ℕ) : Finset ℕ := insert (mx X + 1) (X.erase (mx X))
noncomputable def Bmap (X : Finset ℕ) : Finset ℕ := insert (tr X - 1) (X.erase (tr X - 2))

lemma mem_le_sum {X : Finset ℕ} {x : ℕ} (h : x ∈ X) : x ≤ ∑ y ∈ X, y :=
  Finset.single_le_sum (f := fun y => y) (fun _ _ => Nat.zero_le _) h

/-- preimages of ρ have parts ≥ S and top-run bottom ≥ S+1 -/
lemma pre_ge {Z X : Finset ℕ} {S : ℕ} (hZ : Z.Nonempty) (hX : ∀ x ∈ X, S ≤ x) (hS : 1 ≤ S)
    (hr : rho Z = X) : (∀ z ∈ Z, S ≤ z) ∧ S + 1 ≤ tr Z := by
  rw [rho_eq hZ] at hr
  have htr : S + 1 ≤ tr Z := by
    have hm : tr Z - 1 ∈ X := by rw [← hr]; exact Finset.mem_insert_self _ _
    have := hX _ hm
    rcases Nat.eq_zero_or_pos (tr Z) with h0 | hpos
    · rw [h0] at this; simp at this; omega
    · omega
  refine ⟨fun z hz => ?_, htr⟩
  by_cases hzt : z = tr Z
  · omega
  · have : z ∈ X := by
      rw [← hr, Finset.mem_insert, Finset.mem_erase]
      exact Or.inr ⟨hzt, hz⟩
    exact hX z this

/-- the one-step preimage lemma -/
lemma rho_preimage {Z X : Finset ℕ} {S : ℕ} (hZ : Z.Nonempty) (hX : ∀ x ∈ X, S ≤ x) (hS : 1 ≤ S)
    (hr : rho Z = X) : Z = Amap X ∨ (tr X - 2 ∈ X ∧ Z = Bmap X) := by
  obtain ⟨hZge, htZ⟩ := pre_ge hZ hX hS hr
  set τ := tr Z with hτ
  have hτmem : τ ∈ Z := tr_mem hZ
  have hτpred : τ - 1 ∉ Z := tr_pred_not_mem hZ (by omega)
  rw [rho_eq hZ] at hr
  -- X = insert (τ-1) (Z.erase τ)
  have hXne : X.Nonempty := ⟨τ - 1, by rw [← hr]; exact Finset.mem_insert_self _ _⟩
  have hτnotX : τ ∉ X := by
    rw [← hr, Finset.mem_insert, Finset.mem_erase]
    rintro (h | ⟨h, _⟩)
    · omega
    · exact h rfl
  have hτ1X : τ - 1 ∈ X := by rw [← hr]; exact Finset.mem_insert_self _ _
  have hZeq : Z = insert τ (X.erase (τ - 1)) := by
    ext z
    rw [Finset.mem_insert, Finset.mem_erase, ← hr, Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro hz
      by_cases h : z = τ
      · exact Or.inl h
      · right
        refine ⟨?_, Or.inr ⟨h, hz⟩⟩
        intro e; rw [e] at hz; exact hτpred hz
    · rintro (h | ⟨h1, h2 | ⟨h3, h4⟩⟩)
      · rw [h]; exact hτmem
      · exact absurd h2 h1
      · exact h4
  -- elements of X other than τ-1 are in Z
  have hXsub : ∀ x ∈ X, x ≠ τ - 1 → x ∈ Z := by
    intro x hx hne
    rw [← hr, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with h | ⟨_, h⟩
    · exact absurd h hne
    · exact h
  set M := mx X with hM
  by_cases hcase : τ - 1 = M
  · -- A case
    left
    unfold Amap
    rw [hZeq, ← hM, ← hcase]
    congr 1
    omega
  · -- B case
    right
    have hτ1lt : τ - 1 < M := lt_of_le_of_ne (le_mx hτ1X) hcase
    have hτle : τ ≤ M := by omega
    have hτlt : τ < M := lt_of_le_of_ne hτle (fun e => hτnotX (e ▸ mx_mem hXne))
    -- max Z = M
    have hMZ : mx Z = M := by
      apply mx_eq_of
      · exact hXsub M (mx_mem hXne) (by omega)
      · intro z hz
        by_cases h : z = τ
        · omega
        · have : z ∈ X := by
            rw [← hr, Finset.mem_insert, Finset.mem_erase]; exact Or.inr ⟨h, hz⟩
          exact le_mx this
    -- Icc (τ+1) M ⊆ X
    have hrun : ∀ y, τ + 1 ≤ y → y ≤ M → y ∈ X := by
      intro y h1 h2
      have : y ∈ Z := mem_of_tr_le hZ (by omega) (by rw [hMZ]; exact h2)
      rw [← hr, Finset.mem_insert, Finset.mem_erase]
      right; exact ⟨by omega, this⟩
    have htX : tr X = τ + 1 := by
      apply tr_unique hXne
      · exact ⟨hrun (τ+1) le_rfl (by omega), fun y h1 h2 => hrun y h1 h2⟩
      · intro _; simp only [Nat.add_sub_cancel]; exact hτnotX
    refine ⟨?_, ?_⟩
    · rw [htX]; simpa using hτ1X
    · unfold Bmap
      rw [htX, hZeq]
      simp only [Nat.add_sub_cancel]
      have : τ + 1 - 2 = τ - 1 := by omega
      rw [this]

/- ### properties of `Amap` and `Bmap` -/

section AB
variable {X : Finset ℕ} {S : ℕ}

lemma Amap_nonempty : (Amap X).Nonempty := ⟨_, Finset.mem_insert_self _ _⟩

lemma Amap_ge (hX : ∀ x ∈ X, S ≤ x) (hXne : X.Nonempty) : ∀ x ∈ Amap X, S ≤ x := by
  intro x hx
  unfold Amap at hx
  rw [Finset.mem_insert, Finset.mem_erase] at hx
  rcases hx with e | ⟨_, h⟩
  · have := hX _ (mx_mem hXne); omega
  · exact hX x h

lemma mx_not_mem_erase : mx X ∉ X.erase (mx X) := by simp

lemma mx_succ_not_mem_erase : mx X + 1 ∉ X.erase (mx X) := by
  intro h
  rw [Finset.mem_erase] at h
  have := le_mx h.2
  omega

lemma mx_Amap : mx (Amap X) = mx X + 1 := by
  apply mx_eq_of (Finset.mem_insert_self _ _)
  intro x hx
  unfold Amap at hx
  rw [Finset.mem_insert, Finset.mem_erase] at hx
  rcases hx with e | ⟨_, h⟩
  · omega
  · have := le_mx h; omega

lemma tr_Amap : tr (Amap X) = mx X + 1 := by
  apply tr_unique Amap_nonempty
  · refine ⟨Finset.mem_insert_self _ _, fun y h1 h2 => ?_⟩
    rw [mx_Amap] at h2
    have : y = mx X + 1 := le_antisymm h2 h1
    rw [this]; exact Finset.mem_insert_self _ _
  · intro _
    simp only [Nat.add_sub_cancel]
    unfold Amap
    rw [Finset.mem_insert, Finset.mem_erase]
    rintro (h | ⟨h, _⟩)
    · omega
    · exact h rfl

lemma Pf_Amap (hXne : X.Nonempty) : Pf X / Pf (Amap X) = 1 / ((mx X : ℚ) + 1) := by
  unfold Amap
  rw [Pf_insert mx_succ_not_mem_erase, Pf_erase (mx_mem hXne)]
  have h1 : (0:ℚ) < Pf (X.erase (mx X)) := Pf_pos _
  have h2 : (0:ℚ) < ((mx X).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- hypotheses for the B case -/
lemma Bmap_facts (hXne : X.Nonempty) (hX : ∀ x ∈ X, S ≤ x) (hS : 1 ≤ S) (hB : tr X - 2 ∈ X) :
    S + 2 ≤ tr X ∧ (Bmap X).Nonempty ∧ (∀ x ∈ Bmap X, S ≤ x) ∧ mx (Bmap X) = mx X ∧
    tr (Bmap X) = tr X - 1 ∧ Pf X / Pf (Bmap X) = 1 / ((tr X : ℚ) - 1) := by
  have hSt : S + 2 ≤ tr X := by
    have := hX _ hB
    omega
  have hpred : tr X - 1 ∉ X := tr_pred_not_mem hXne (by omega)
  have hpred' : tr X - 1 ∉ X.erase (tr X - 2) := by
    intro h; rw [Finset.mem_erase] at h; exact hpred h.2
  have hBne : (Bmap X).Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
  have hmx : mx (Bmap X) = mx X := by
    apply mx_eq_of
    · unfold Bmap
      rw [Finset.mem_insert, Finset.mem_erase]
      right
      refine ⟨?_, mx_mem hXne⟩
      have := tr_le_mx hXne
      omega
    · intro x hx
      unfold Bmap at hx
      rw [Finset.mem_insert, Finset.mem_erase] at hx
      rcases hx with e | ⟨_, h⟩
      · have := tr_le_mx hXne; omega
      · exact le_mx h
  refine ⟨hSt, hBne, ?_, hmx, ?_, ?_⟩
  · intro x hx
    unfold Bmap at hx
    rw [Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with e | ⟨_, h⟩
    · omega
    · exact hX x h
  · apply tr_unique (X := Bmap X) hBne
    · refine ⟨Finset.mem_insert_self _ _, fun y h1 h2 => ?_⟩
      rw [hmx] at h2
      unfold Bmap
      rw [Finset.mem_insert, Finset.mem_erase]
      rcases Nat.eq_or_lt_of_le h1 with e | lt
      · left; exact e.symm
      · right
        exact ⟨by omega, mem_of_tr_le hXne (by omega) h2⟩
    · intro _
      have : tr X - 1 - 1 = tr X - 2 := by omega
      rw [this]
      unfold Bmap
      rw [Finset.mem_insert, Finset.mem_erase]
      rintro (h | ⟨h, _⟩)
      · omega
      · exact h rfl
  · unfold Bmap
    rw [Pf_insert hpred', Pf_erase hB]
    have h1 : (0:ℚ) < Pf (X.erase (tr X - 2)) := Pf_pos _
    have e : tr X - 1 = (tr X - 2) + 1 := by omega
    rw [e, Nat.factorial_succ]
    have h2 : (0:ℚ) < ((tr X - 2).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
    push_cast [Nat.cast_sub (by omega : 2 ≤ tr X)]
    have h3 : (tr X : ℚ) - 2 + 1 = (tr X : ℚ) - 1 := by ring
    rw [h3]
    have h4 : (0:ℚ) < (tr X : ℚ) - 1 := by
      have : (2:ℚ) ≤ (tr X : ℚ) := by exact_mod_cast (by omega : 2 ≤ tr X)
      linarith
    field_simp

lemma Amap_ne_Bmap : Amap X ≠ Bmap X := by
  intro h
  have : mx X + 1 ∈ Bmap X := by rw [← h]; exact Finset.mem_insert_self _ _
  unfold Bmap at this
  rw [Finset.mem_insert, Finset.mem_erase] at this
  rcases this with e | ⟨_, h2⟩
  · have := le_mx (X := X) (x := tr X)
    by_cases hne : X.Nonempty
    · have := tr_le_mx hne; omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [tr, mx] at e
  · have := le_mx h2; omega

end AB

/- ### fibers of iterates of ρ -/

noncomputable def Fib (k : ℕ) (X : Finset ℕ) (S : ℕ) : Finset (Finset ℕ) :=
  (Icc S (∑ x ∈ X, x + k)).powerset.filter (fun Y => rho^[k] Y = X)

noncomputable def fsum (k : ℕ) (X : Finset ℕ) (S : ℕ) : ℚ := ∑ Y ∈ Fib k X S, Pf X / Pf Y

lemma mem_Fib {k : ℕ} {X Y : Finset ℕ} {S : ℕ} :
    Y ∈ Fib k X S ↔ Y ⊆ Icc S (∑ x ∈ X, x + k) ∧ rho^[k] Y = X := by
  unfold Fib; rw [Finset.mem_filter, Finset.mem_powerset]

lemma card_rho_iterate (k : ℕ) (Y : Finset ℕ) : (rho^[k] Y).card = Y.card := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', card_rho, ih]

lemma fsum_nonneg (k : ℕ) (X : Finset ℕ) (S : ℕ) : 0 ≤ fsum k X S := by
  unfold fsum
  apply Finset.sum_nonneg
  intro Y _
  exact div_nonneg (Pf_pos X).le (Pf_pos Y).le

lemma Fib_succ_subset {k : ℕ} {X : Finset ℕ} {S : ℕ} (hXne : X.Nonempty) (hX : ∀ x ∈ X, S ≤ x)
    (hS : 1 ≤ S) : Fib (k+1) X S ⊆ (Fib 1 X S).biUnion (fun Y1 => Fib k Y1 S) := by
  intro Y hY
  rw [mem_Fib] at hY
  obtain ⟨hYsub, hYr⟩ := hY
  rw [Function.iterate_succ_apply'] at hYr
  set Y1 := rho^[k] Y with hY1
  have hY1ne : Y1.Nonempty := by
    rw [← Finset.card_pos, ← card_rho, hYr]; exact Finset.card_pos.mpr hXne
  obtain ⟨hY1ge, htr⟩ := pre_ge hY1ne hX hS hYr
  have hsum : ∑ x ∈ Y1, x = ∑ x ∈ X, x + 1 := by
    rw [← hYr]; exact sum_rho hY1ne (by omega)
  rw [Finset.mem_biUnion]
  refine ⟨Y1, ?_, ?_⟩
  · rw [mem_Fib]
    refine ⟨?_, by simpa using hYr⟩
    intro y hy
    rw [Finset.mem_Icc]
    exact ⟨hY1ge y hy, by rw [← hsum]; exact mem_le_sum hy⟩
  · rw [mem_Fib]
    refine ⟨?_, rfl⟩
    rw [hsum]
    intro y hy
    have := hYsub hy
    rw [Finset.mem_Icc] at this ⊢
    omega

lemma Fib_disjoint (k : ℕ) (S : ℕ) {Y1 Y2 : Finset ℕ} (h : Y1 ≠ Y2) :
    Disjoint (Fib k Y1 S) (Fib k Y2 S) := by
  rw [Finset.disjoint_left]
  intro Y h1 h2
  rw [mem_Fib] at h1 h2
  exact h (h1.2.symm.trans h2.2)

lemma Fib_one_subset {X : Finset ℕ} {S : ℕ} (hXne : X.Nonempty) (hX : ∀ x ∈ X, S ≤ x) (hS : 1 ≤ S) :
    Fib 1 X S ⊆ insert (Amap X) (if tr X - 2 ∈ X then {Bmap X} else ∅) := by
  intro Y hY
  rw [mem_Fib] at hY
  obtain ⟨_, hYr⟩ := hY
  simp only [Function.iterate_one] at hYr
  have hYne : Y.Nonempty := by
    rw [← Finset.card_pos, ← card_rho, hYr]; exact Finset.card_pos.mpr hXne
  rcases rho_preimage hYne hX hS hYr with h | ⟨hB, h⟩
  · rw [h]; exact Finset.mem_insert_self _ _
  · rw [h, if_pos hB]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

lemma fsum_zero_le (X : Finset ℕ) (S : ℕ) : fsum 0 X S ≤ 1 := by
  unfold fsum
  have : Fib 0 X S ⊆ {X} := by
    intro Y hY
    rw [mem_Fib] at hY
    simp only [Function.iterate_zero, id_eq] at hY
    rw [Finset.mem_singleton]; exact hY.2
  calc ∑ Y ∈ Fib 0 X S, Pf X / Pf Y ≤ ∑ Y ∈ {X}, Pf X / Pf Y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg this
        intro Y _ _; exact div_nonneg (Pf_pos X).le (Pf_pos Y).le
    _ = 1 := by rw [Finset.sum_singleton, div_self (Pf_pos X).ne']

lemma fsum_succ_le {k : ℕ} {X : Finset ℕ} {S : ℕ} (hXne : X.Nonempty) (hX : ∀ x ∈ X, S ≤ x)
    (hS : 1 ≤ S) : fsum (k+1) X S ≤ Pf X / Pf (Amap X) * fsum k (Amap X) S +
      (if tr X - 2 ∈ X then Pf X / Pf (Bmap X) * fsum k (Bmap X) S else 0) := by
  have hnn : ∀ Y, 0 ≤ Pf X / Pf Y := fun Y => div_nonneg (Pf_pos X).le (Pf_pos Y).le
  have step1 : fsum (k+1) X S ≤ ∑ Y1 ∈ Fib 1 X S, Pf X / Pf Y1 * fsum k Y1 S := by
    unfold fsum
    calc ∑ Y ∈ Fib (k+1) X S, Pf X / Pf Y
        ≤ ∑ Y ∈ (Fib 1 X S).biUnion (fun Y1 => Fib k Y1 S), Pf X / Pf Y := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Fib_succ_subset hXne hX hS)
          intro Y _ _; exact hnn Y
      _ = ∑ Y1 ∈ Fib 1 X S, ∑ Y ∈ Fib k Y1 S, Pf X / Pf Y := by
          apply Finset.sum_biUnion
          intro Y1 _ Y2 _ hne
          exact Fib_disjoint k S hne
      _ = ∑ Y1 ∈ Fib 1 X S, Pf X / Pf Y1 * ∑ Y ∈ Fib k Y1 S, Pf Y1 / Pf Y := by
          apply Finset.sum_congr rfl
          intro Y1 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro Y _
          have := (Pf_pos Y1).ne'
          field_simp
  have step2 : ∑ Y1 ∈ Fib 1 X S, Pf X / Pf Y1 * fsum k Y1 S
      ≤ ∑ Y1 ∈ insert (Amap X) (if tr X - 2 ∈ X then {Bmap X} else ∅), Pf X / Pf Y1 * fsum k Y1 S := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Fib_one_subset hXne hX hS)
    intro Y _ _; exact mul_nonneg (hnn Y) (fsum_nonneg _ _ _)
  refine le_trans step1 (le_trans step2 ?_)
  rw [Finset.sum_insert]
  · apply _root_.add_le_add (le_refl _)
    split_ifs
    · rw [Finset.sum_singleton]
    · rw [Finset.sum_empty]
  · split_ifs
    · rw [Finset.mem_singleton]; exact Amap_ne_Bmap
    · exact Finset.notMem_empty _

theorem fsum_le_F (S : ℕ) (hS : 1 ≤ S) : ∀ (k : ℕ) (X : Finset ℕ), X.Nonempty → (∀ x ∈ X, S ≤ x) →
    fsum k X S ≤ F S k (tr X) (mx X) := by
  intro k
  induction k with
  | zero => intro X _ _; simp only [F]; exact fsum_zero_le X S
  | succ k ih =>
    intro X hXne hX
    refine le_trans (fsum_succ_le hXne hX hS) ?_
    simp only [F]
    apply _root_.add_le_add
    · rw [Pf_Amap hXne, one_div_mul_eq_div]
      have := ih (Amap X) Amap_nonempty (Amap_ge hX hXne)
      rw [tr_Amap, mx_Amap] at this
      exact div_le_div_of_nonneg_right this (by positivity)
    · by_cases hB : tr X - 2 ∈ X
      · obtain ⟨hSt, hBne, hBge, hmx, htr, hPf⟩ := Bmap_facts hXne hX hS hB
        rw [if_pos hB, if_pos hSt, hPf, one_div_mul_eq_div]
        apply div_le_div_of_nonneg_right _ ?_
        · have := ih (Bmap X) hBne hBge
          rwa [hmx, htr] at this
        · have : (2:ℚ) ≤ (tr X : ℚ) := by exact_mod_cast (by omega : 2 ≤ tr X)
          linarith
      · rw [if_neg hB]
        split_ifs
        · apply div_nonneg (F_nonneg _ _ _ _)
          have : (2:ℚ) ≤ (tr X : ℚ) := by exact_mod_cast (by omega : 2 ≤ tr X)
          linarith
        · exact le_refl 0

end A185895Proof


namespace A185895Proof
open Finset
open scoped Classical

/- ## Part B: the transport map Φ -/

/-- strict partitions of `n` into `j` parts, all parts ≥ s -/
def SP (j s n : ℕ) : Finset (Finset ℕ) :=
  (Icc s n).powerset.filter (fun X => X.card = j ∧ ∑ x ∈ X, x = n)

lemma mem_SP {j s n : ℕ} {X : Finset ℕ} :
    X ∈ SP j s n ↔ X ⊆ Icc s n ∧ X.card = j ∧ ∑ x ∈ X, x = n := by
  unfold SP; rw [Finset.mem_filter, Finset.mem_powerset]

def Tri (k : ℕ) : ℕ := ∑ i ∈ Icc 1 k, i

lemma Tri_succ (k : ℕ) : Tri (k+1) = Tri k + (k+1) := by
  unfold Tri; rw [Finset.sum_Icc_succ_top (by omega)]

lemma Tri_zero : Tri 0 = 0 := by simp [Tri]

lemma Tri_eq (k : ℕ) : Tri k = k * (k+1) / 2 := by
  induction k with
  | zero => simp [Tri_zero]
  | succ k ih =>
    rw [Tri_succ, ih]
    have : (k+1)*(k+1+1) = k*(k+1) + 2*(k+1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

lemma Tri_mono {a b : ℕ} (h : a ≤ b) : Tri a ≤ Tri b := by
  unfold Tri
  apply Finset.sum_le_sum_of_subset
  intro x; simp only [Finset.mem_Icc]; omega

lemma Tri_lt (k : ℕ) : Tri k < Tri (k+1) := by rw [Tri_succ]; omega

lemma Tri_strictMono {a b : ℕ} (h : a < b) : Tri a < Tri b :=
  lt_of_lt_of_le (Tri_lt a) (Tri_mono h)

lemma Icc_split_nat (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) (f : ℕ → ℕ) :
    ∑ s ∈ Icc a c, f s = ∑ s ∈ Icc a b, f s + ∑ s ∈ Icc (b+1) c, f s := by
  have e : Icc a c = Icc a b ∪ Icc (b+1) c := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  rw [e, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Icc] at hx hx'
  omega

lemma sum_Icc_eq (s j : ℕ) (h : s ≤ j) : ∑ i ∈ Icc (s+1) j, i + Tri s = Tri j := by
  unfold Tri
  rw [Icc_split_nat 1 s j (by omega) h]
  omega

lemma card_Icc_one (k : ℕ) : (Icc 1 k).card = k := by simp

lemma Icc_one_eq_insert (s : ℕ) (hs : 1 ≤ s) : Icc 1 s = insert s (Icc 1 (s-1)) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

lemma Pf_Icc_succ (s : ℕ) (hs : 1 ≤ s) : Pf (Icc 1 s) = (s.factorial : ℚ) * Pf (Icc 1 (s-1)) := by
  rw [Icc_one_eq_insert s hs, Pf_insert]
  simp; omega

/-- the smallest positive integer not in `P` -/
lemma mm_exists (P : Finset ℕ) : ∃ i, 1 ≤ i ∧ i ∉ P :=
  ⟨mx P + 1, by omega, fun h => by have := le_mx h; omega⟩

noncomputable def mm (P : Finset ℕ) : ℕ := Nat.find (mm_exists P)

lemma mm_spec (P : Finset ℕ) : 1 ≤ mm P ∧ mm P ∉ P := Nat.find_spec (mm_exists P)

lemma mm_min (P : Finset ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i < mm P) : i ∈ P := by
  have := Nat.find_min (mm_exists P) h2
  simp only [not_and, not_not] at this
  exact this h1

/-- the upper part of `P` -/
def Pt (P : Finset ℕ) (s : ℕ) : Finset ℕ := P.filter (fun x => s < x)

noncomputable def Phi (P : Finset ℕ) : Finset ℕ := Icc 1 (mm P) ∪ rho^[mm P] (Pt P (mm P))

lemma Pt_ge (P : Finset ℕ) (s : ℕ) : ∀ z ∈ Pt P s, s + 1 ≤ z := by
  intro z hz; unfold Pt at hz; rw [Finset.mem_filter] at hz; omega

lemma P_decomp {P : Finset ℕ} (h0 : ∀ x ∈ P, 1 ≤ x) :
    P = Icc 1 (mm P - 1) ∪ Pt P (mm P) ∧ Disjoint (Icc 1 (mm P - 1)) (Pt P (mm P)) := by
  constructor
  · ext x
    rw [Finset.mem_union, Finset.mem_Icc]
    unfold Pt; rw [Finset.mem_filter]
    constructor
    · intro hx
      have h1 := h0 x hx
      by_cases h : x < mm P
      · left; omega
      · right
        refine ⟨hx, ?_⟩
        have : x ≠ mm P := fun e => (mm_spec P).2 (e ▸ hx)
        omega
    · rintro (h | ⟨h, _⟩)
      · exact mm_min P h.1 (by omega)
      · exact h
  · rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx
    unfold Pt at hx'; rw [Finset.mem_filter] at hx'
    omega

/-- the excess lemma: a non-minimal set has top-run bottom ≥ s+2 -/
lemma tr_ge_of_excess {Z : Finset ℕ} {s j : ℕ} (hZne : Z.Nonempty) (hZ : ∀ z ∈ Z, s + 1 ≤ z)
    (hcard : Z.card = j - s) (hsj : s < j) (hsum : ∑ i ∈ Icc (s+1) j, i < ∑ z ∈ Z, z) :
    s + 2 ≤ tr Z := by
  by_contra hcon
  have htr : tr Z = s + 1 := by have := hZ _ (tr_mem hZne); omega
  have hZeq : Z = Icc (s+1) (mx Z) := by
    ext x
    rw [Finset.mem_Icc]
    constructor
    · intro hx; exact ⟨hZ x hx, le_mx hx⟩
    · intro hx; exact mem_of_tr_le hZne (by omega) hx.2
  have hmx : mx Z = j := by
    have h1 : Z.card = mx Z + 1 - (s+1) := by
      calc Z.card = (Icc (s+1) (mx Z)).card := by rw [← hZeq]
        _ = mx Z + 1 - (s+1) := Nat.card_Icc _ _
    have h2 : s + 1 ≤ mx Z := hZ _ (mx_mem hZne)
    omega
  rw [hZeq, hmx] at hsum
  exact lt_irrefl _ hsum

/-- iterating ρ on the upper part keeps the invariants -/
lemma iter_facts {Z0 : Finset ℕ} {s j : ℕ} (hsj : s < j) (hZ0 : ∀ z ∈ Z0, s + 1 ≤ z)
    (hcard : Z0.card = j - s) (hsum : ∑ i ∈ Icc (s+1) j, i + s ≤ ∑ z ∈ Z0, z) :
    ∀ i ≤ s, (∀ z ∈ rho^[i] Z0, s + 1 ≤ z) ∧ (rho^[i] Z0).card = j - s ∧
      ∑ z ∈ rho^[i] Z0, z + i = ∑ z ∈ Z0, z := by
  intro i
  induction i with
  | zero => intro _; exact ⟨hZ0, hcard, by simp⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have h4 : ∑ i ∈ Icc (s+1) j, i < ∑ z ∈ rho^[i] Z0, z := by omega
    have hZne : (rho^[i] Z0).Nonempty := by rw [← Finset.card_pos, h2]; omega
    have htr : s + 2 ≤ tr (rho^[i] Z0) := tr_ge_of_excess hZne h1 h2 hsj h4
    rw [Function.iterate_succ_apply']
    refine ⟨rho_ge hZne h1 htr, by rw [card_rho, h2], ?_⟩
    have := sum_rho hZne (by omega)
    omega

/-- the facts about a `(j-1)`-set `P` needed for the transport -/
lemma P_facts {P : Finset ℕ} {j n : ℕ} (hP : P ∈ SP (j-1) 1 n) (hj : 2 ≤ j) (hn : Tri j ≤ n) :
    1 ≤ mm P ∧ mm P ≤ j - 1 ∧ (Pt P (mm P)).card = j - mm P ∧
    ∑ z ∈ Pt P (mm P), z + Tri (mm P - 1) = n ∧
    ∑ i ∈ Icc (mm P + 1) j, i + mm P ≤ ∑ z ∈ Pt P (mm P), z := by
  rw [mem_SP] at hP
  obtain ⟨hsub, hcard, hsum⟩ := hP
  have h0 : ∀ x ∈ P, 1 ≤ x := fun x hx => (Finset.mem_Icc.mp (hsub hx)).1
  obtain ⟨hdec, hdisj⟩ := P_decomp h0
  have hs1 : 1 ≤ mm P := (mm_spec P).1
  have hcard' : P.card = (mm P - 1) + (Pt P (mm P)).card := by
    conv_lhs => rw [hdec]
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Icc]; omega
  have hsum' : ∑ x ∈ P, x = Tri (mm P - 1) + ∑ z ∈ Pt P (mm P), z := by
    conv_lhs => rw [hdec]
    rw [Finset.sum_union hdisj]; rfl
  have hle : mm P ≤ j := by
    by_contra h
    push_neg at h
    have hsub' : Icc 1 j ⊆ P := fun i hi =>
      mm_min P (Finset.mem_Icc.1 hi).1 (by have := (Finset.mem_Icc.1 hi).2; omega)
    have := Finset.card_le_card hsub'
    rw [Nat.card_Icc] at this; omega
  have hne : mm P ≠ j := by
    intro e
    have hsub' : Icc 1 (j-1) ⊆ P := fun i hi =>
      mm_min P (Finset.mem_Icc.1 hi).1 (by have := (Finset.mem_Icc.1 hi).2; omega)
    have heq : Icc 1 (j-1) = P :=
      Finset.eq_of_subset_of_card_le hsub' (by rw [hcard, Nat.card_Icc]; omega)
    have h5 : ∑ x ∈ P, x = Tri (j-1) := by rw [← heq]; rfl
    have := Tri_strictMono (show j - 1 < j by omega)
    omega
  refine ⟨hs1, by omega, by omega, by omega, ?_⟩
  have e1 := sum_Icc_eq (mm P) j hle
  have e2 : Tri (mm P) = Tri (mm P - 1) + mm P := by
    have := Tri_succ (mm P - 1); rw [show mm P - 1 + 1 = mm P by omega] at this; exact this
  omega

/-- the transported set is in `SP j 1 n`; also record its structure -/
lemma Phi_facts {P : Finset ℕ} {j n : ℕ} (hP : P ∈ SP (j-1) 1 n) (hj : 2 ≤ j) (hn : Tri j ≤ n) :
    Phi P ∈ SP j 1 n ∧
    (∀ z ∈ rho^[mm P] (Pt P (mm P)), mm P + 1 ≤ z) ∧
    (rho^[mm P] (Pt P (mm P))).card = j - mm P ∧
    ∑ z ∈ rho^[mm P] (Pt P (mm P)), z + mm P = ∑ z ∈ Pt P (mm P), z := by
  obtain ⟨hs1, hsj, hcardPt, hsumPt, hexc⟩ := P_facts hP hj hn
  obtain ⟨h1, h2, h3⟩ := iter_facts (Z0 := Pt P (mm P)) (s := mm P) (j := j) (by omega)
    (Pt_ge P (mm P)) hcardPt hexc (mm P) le_rfl
  refine ⟨?_, h1, h2, h3⟩
  rw [mem_SP]
  have hdisj : Disjoint (Icc 1 (mm P)) (rho^[mm P] (Pt P (mm P))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx
    have := h1 x hx'
    omega
  have hsum : ∑ x ∈ Phi P, x = n := by
    unfold Phi
    rw [Finset.sum_union hdisj]
    have e2 : Tri (mm P) = Tri (mm P - 1) + mm P := by
      have := Tri_succ (mm P - 1); rw [show mm P - 1 + 1 = mm P by omega] at this; exact this
    have : ∑ x ∈ Icc 1 (mm P), x = Tri (mm P) := rfl
    omega
  refine ⟨?_, ?_, hsum⟩
  · intro x hx
    rw [Finset.mem_Icc]
    refine ⟨?_, by rw [← hsum]; exact mem_le_sum hx⟩
    unfold Phi at hx
    rw [Finset.mem_union, Finset.mem_Icc] at hx
    rcases hx with h | h
    · exact h.1
    · have := h1 x h; omega
  · unfold Phi
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Icc, h2]
    omega


lemma Icc_subset_Icc_one {a b : ℕ} (h : a ≤ b) : Icc 1 a ⊆ Icc 1 b := by
  intro x; simp only [Finset.mem_Icc]; omega

/-- for `P` in the fiber over `Q` with `mm P = s`, the upper part lies in the ρ-fiber -/
lemma fiber_facts {P Q : Finset ℕ} {j n s : ℕ} (hP : P ∈ SP (j-1) 1 n) (hj : 2 ≤ j) (hn : Tri j ≤ n)
    (hQ : Phi P = Q) (hs : mm P = s) :
    Icc 1 s ⊆ Q ∧ Pt P s ∈ Fib s (Q \ Icc 1 s) (s+1) ∧
    Pf Q / Pf P = (s.factorial : ℚ) * (Pf (Q \ Icc 1 s) / Pf (Pt P s)) := by
  obtain ⟨_, h1, h2, h3⟩ := Phi_facts hP hj hn
  obtain ⟨hs1, _, _, _, _⟩ := P_facts hP hj hn
  rw [hs] at h1 h2 h3
  have hQeq : Q = Icc 1 s ∪ rho^[s] (Pt P s) := by rw [← hQ]; unfold Phi; rw [hs]
  have hX : Q \ Icc 1 s = rho^[s] (Pt P s) := by
    ext x
    rw [Finset.mem_sdiff, hQeq, Finset.mem_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h
      refine ⟨Or.inr h, ?_⟩
      have := h1 x h
      rw [Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 s) (rho^[s] (Pt P s)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx
    have := h1 x hx'
    omega
  refine ⟨by rw [hQeq]; exact Finset.subset_union_left, ?_, ?_⟩
  · rw [mem_Fib, hX]
    refine ⟨?_, rfl⟩
    intro z hz
    rw [Finset.mem_Icc]
    refine ⟨Pt_ge P s z hz, ?_⟩
    have := mem_le_sum hz
    omega
  · have h0 : ∀ x ∈ P, 1 ≤ x := by
      rw [mem_SP] at hP
      exact fun x hx => (Finset.mem_Icc.mp (hP.1 hx)).1
    obtain ⟨hdec, hdisjP⟩ := P_decomp h0
    rw [hs] at hdec hdisjP
    have hPfQ : Pf Q = Pf (Icc 1 s) * Pf (Q \ Icc 1 s) := by
      rw [hX]; conv_lhs => rw [hQeq]
      exact Pf_union hdisj
    have hPfP : Pf P = Pf (Icc 1 (s-1)) * Pf (Pt P s) := by
      conv_lhs => rw [hdec]
      exact Pf_union hdisjP
    rw [hPfQ, hPfP, Pf_Icc_succ s (hs ▸ hs1)]
    have := (Pf_pos (Icc 1 (s-1))).ne'
    have := (Pf_pos (Pt P s)).ne'
    have := (Pf_pos (Q \ Icc 1 s)).ne'
    field_simp

lemma fiber_sum_le {Q : Finset ℕ} {j n : ℕ} (hj : 2 ≤ j) (hn : Tri j ≤ n) :
    ∑ P ∈ (SP (j-1) 1 n).filter (fun P => Phi P = Q), Pf Q / Pf P ≤
      ∑ s ∈ Icc 1 (j-1), (if Icc 1 s ⊆ Q then (s.factorial : ℚ) * fsum s (Q \ Icc 1 s) (s+1) else 0) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := mm) (t := Icc 1 (j-1))]
  · apply Finset.sum_le_sum
    intro s _
    by_cases hIcc : Icc 1 s ⊆ Q
    · rw [if_pos hIcc]
      set sub := ((SP (j-1) 1 n).filter (fun P => Phi P = Q)).filter (fun P => mm P = s) with hsub
      have hmem : ∀ P ∈ sub, P ∈ SP (j-1) 1 n ∧ Phi P = Q ∧ mm P = s := by
        intro P hP
        rw [hsub, Finset.mem_filter, Finset.mem_filter] at hP
        exact ⟨hP.1.1, hP.1.2, hP.2⟩
      have hterm : ∀ P ∈ sub, Pf Q / Pf P = (s.factorial : ℚ) * (Pf (Q \ Icc 1 s) / Pf (Pt P s)) := by
        intro P hP
        obtain ⟨h1, h2, h3⟩ := hmem P hP
        exact (fiber_facts h1 hj hn h2 h3).2.2
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hinj : Set.InjOn (fun P => Pt P s) (sub : Set (Finset ℕ)) := by
        intro P1 hP1 P2 hP2 he
        simp only at he
        obtain ⟨h1, _, h3⟩ := hmem P1 hP1
        obtain ⟨h1', _, h3'⟩ := hmem P2 hP2
        have h0 : ∀ x ∈ P1, 1 ≤ x := by
          rw [mem_SP] at h1; exact fun x hx => (Finset.mem_Icc.mp (h1.1 hx)).1
        have h0' : ∀ x ∈ P2, 1 ≤ x := by
          rw [mem_SP] at h1'; exact fun x hx => (Finset.mem_Icc.mp (h1'.1 hx)).1
        have d1 := (P_decomp h0).1
        have d2 := (P_decomp h0').1
        rw [h3] at d1; rw [h3'] at d2
        rw [d1, d2, he]
      rw [← Finset.sum_image (f := fun Y => Pf (Q \ Icc 1 s) / Pf Y) hinj]
      unfold fsum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro Y hY
        rw [Finset.mem_image] at hY
        obtain ⟨P, hP, rfl⟩ := hY
        obtain ⟨h1, h2, h3⟩ := hmem P hP
        exact (fiber_facts h1 hj hn h2 h3).2.1
      · intro Y _ _
        exact div_nonneg (Pf_pos _).le (Pf_pos _).le
    · rw [if_neg hIcc]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro P hP
      rw [Finset.mem_filter, Finset.mem_filter] at hP
      exact absurd (fiber_facts hP.1.1 hj hn hP.1.2 hP.2).1 hIcc
  · intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨h1, h2, _, _, _⟩ := P_facts hP.1 hj hn
    rw [Finset.mem_Icc]; exact ⟨h1, h2⟩


lemma X_facts {Q : Finset ℕ} {j n s : ℕ} (hQ : Q ∈ SP j 1 n) (hsj : s < j)
    (hIcc : Icc 1 s ⊆ Q) :
    (Q \ Icc 1 s).Nonempty ∧ (∀ x ∈ Q \ Icc 1 s, s + 1 ≤ x) := by
  rw [mem_SP] at hQ
  obtain ⟨hsub, hcard, _⟩ := hQ
  refine ⟨?_, ?_⟩
  · rw [← Finset.card_pos, Finset.card_sdiff_of_subset hIcc, Nat.card_Icc, hcard]; omega
  · intro x hx
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hx
    have := (Finset.mem_Icc.mp (hsub hx.1)).1
    omega

lemma tr_mx_Icc (s j : ℕ) (h : s < j) : tr (Icc (s+1) j) = s + 1 ∧ mx (Icc (s+1) j) = j := by
  have hne : (Icc (s+1) j).Nonempty := ⟨s+1, by rw [Finset.mem_Icc]; omega⟩
  have hmx : mx (Icc (s+1) j) = j := by
    apply mx_eq_of
    · rw [Finset.mem_Icc]; omega
    · intro x hx; rw [Finset.mem_Icc] at hx; omega
  refine ⟨?_, hmx⟩
  apply tr_unique hne
  · refine ⟨by rw [Finset.mem_Icc]; omega, fun y h1 h2 => ?_⟩
    rw [hmx] at h2
    rw [Finset.mem_Icc]; omega
  · intro _; rw [Finset.mem_Icc]; omega

lemma fiber_bound {Q : Finset ℕ} {j n : ℕ} (hj : 2 ≤ j) (hn : Tri j ≤ n) (hQ : Q ∈ SP j 1 n) :
    ∑ s ∈ Icc 1 (j-1), (if Icc 1 s ⊆ Q then (s.factorial : ℚ) * fsum s (Q \ Icc 1 s) (s+1) else 0)
      ≤ 9/10 := by
  have hQ' := hQ
  rw [mem_SP] at hQ'
  obtain ⟨hsub, hcard, hsumQ⟩ := hQ'
  by_cases hQeq : Q = Icc 1 j
  · -- base case
    subst hQeq
    apply le_trans _ (sumF0_le j)
    apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hIcc : Icc 1 s ⊆ Icc 1 j := Icc_subset_Icc_one (by omega)
    rw [if_pos hIcc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hX : Icc 1 j \ Icc 1 s = Icc (s+1) j := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
    obtain ⟨hne, hge⟩ := X_facts hQ (by omega) hIcc
    have := fsum_le_F (s+1) (by omega) s _ hne hge
    rw [hX] at this ⊢
    obtain ⟨e1, e2⟩ := tr_mx_Icc s j (by omega)
    rwa [e1, e2] at this
  · -- general case
    set sQ := mm Q - 1 with hsQ
    have hmm1 := (mm_spec Q).1
    have hmm2 := (mm_spec Q).2
    have hIccQ : Icc 1 sQ ⊆ Q := by
      intro x hx; rw [Finset.mem_Icc] at hx; exact mm_min Q hx.1 (by omega)
    have hsQj : sQ ≤ j - 1 := by
      by_contra h
      push_neg at h
      have hsub' : Icc 1 j ⊆ Q := Finset.Subset.trans (Icc_subset_Icc_one (by omega)) hIccQ
      have heq : Icc 1 j = Q :=
        Finset.eq_of_subset_of_card_le hsub' (by rw [hcard, Nat.card_Icc]; omega)
      exact hQeq heq.symm
    set Qp := Q \ Icc 1 sQ with hQp
    obtain ⟨hQpne, hQpge⟩ := X_facts hQ (by omega) hIccQ
    have hQpge2 : ∀ x ∈ Qp, sQ + 2 ≤ x := by
      intro x hx
      have h1 := hQpge x hx
      have h2 : x ≠ sQ + 1 := by
        intro e
        rw [Finset.mem_sdiff] at hx
        apply hmm2
        rw [show mm Q = sQ + 1 by omega, ← e]; exact hx.1
      omega
    set t := tr Qp with ht
    set M := mx Qp with hM
    have htge : sQ + 2 ≤ t := hQpge2 _ (tr_mem hQpne)
    have htM : t ≤ M := tr_le_mx hQpne
    -- each level s ≤ sQ has the same top run
    have hlevel : ∀ s, 1 ≤ s → s ≤ sQ → tr (Q \ Icc 1 s) = t ∧ mx (Q \ Icc 1 s) = M := by
      intro s hs1 hs2
      have hIcc : Icc 1 s ⊆ Q := Finset.Subset.trans (Icc_subset_Icc_one hs2) hIccQ
      obtain ⟨hXne, hXge⟩ := X_facts hQ (by omega) hIcc
      have hQpsub : Qp ⊆ Q \ Icc 1 s := by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨hx.1, fun h => hx.2 (Icc_subset_Icc_one hs2 h)⟩
      have hmxX : mx (Q \ Icc 1 s) = M := by
        apply mx_eq_of (hQpsub (mx_mem hQpne))
        intro x hx
        by_cases hxQp : x ∈ Qp
        · exact le_mx hxQp
        · rw [Finset.mem_sdiff] at hx hxQp
          have : x ∈ Icc 1 sQ := by
            by_contra h; exact hxQp ⟨hx.1, h⟩
          rw [Finset.mem_Icc] at this
          omega
      refine ⟨?_, hmxX⟩
      apply tr_unique hXne
      · refine ⟨hQpsub (tr_mem hQpne), fun y h1 h2 => ?_⟩
        rw [hmxX] at h2
        exact hQpsub (mem_of_tr_le hQpne h1 h2)
      · intro _ hmem
        have hpred := tr_pred_not_mem hQpne (le_trans (by omega : 1 ≤ sQ + 2) htge)
        apply hpred
        rw [Finset.mem_sdiff] at hmem ⊢
        refine ⟨hmem.1, ?_⟩
        have h5 : sQ + 2 ≤ tr (Q \ Icc 1 sQ) := htge
        rw [Finset.mem_Icc]; omega
    -- bound each term
    have hterm : ∀ s ∈ Icc 1 (j-1),
        (if Icc 1 s ⊆ Q then (s.factorial : ℚ) * fsum s (Q \ Icc 1 s) (s+1) else 0)
          ≤ (if s ≤ sQ then (s.factorial : ℚ) * F (s+1) s t M else 0) := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      by_cases hle : s ≤ sQ
      · have hIcc : Icc 1 s ⊆ Q := Finset.Subset.trans (Icc_subset_Icc_one hle) hIccQ
        rw [if_pos hIcc, if_pos hle]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        obtain ⟨hXne, hXge⟩ := X_facts hQ (by omega) hIcc
        have := fsum_le_F (s+1) (by omega) s _ hXne hXge
        obtain ⟨e1, e2⟩ := hlevel s hs.1 hle
        rwa [e1, e2] at this
      · have hIcc : ¬ Icc 1 s ⊆ Q := by
          intro h
          apply hmm2
          rw [show mm Q = sQ + 1 by omega]
          exact h (by rw [Finset.mem_Icc]; omega)
        rw [if_neg hIcc, if_neg hle]
    apply le_trans (Finset.sum_le_sum hterm)
    rw [← Finset.sum_filter]
    apply le_trans _ (sumF_le t M htM)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      rw [Finset.mem_filter, Finset.mem_Icc] at hs
      rw [Finset.mem_Icc]; omega
    · intro s _ _
      exact mul_nonneg (by positivity) (F_nonneg _ _ _ _)

/-- the transport inequality -/
theorem transport {j n : ℕ} (hj : 2 ≤ j) (hn : Tri j ≤ n) :
    ∑ P ∈ SP (j-1) 1 n, 1 / Pf P ≤ (9/10) * ∑ Q ∈ SP j 1 n, 1 / Pf Q := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Phi) (t := SP j 1 n)
    (fun P hP => (Phi_facts hP hj hn).1)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Q hQ
  have h := le_trans (fiber_sum_le (Q := Q) hj hn) (fiber_bound hj hn hQ)
  have e : ∑ P ∈ (SP (j-1) 1 n).filter (fun P => Phi P = Q), 1 / Pf P
      = (1 / Pf Q) * ∑ P ∈ (SP (j-1) 1 n).filter (fun P => Phi P = Q), Pf Q / Pf P := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    have := (Pf_pos Q).ne'
    field_simp
  rw [e]
  calc (1 / Pf Q) * ∑ P ∈ (SP (j-1) 1 n).filter (fun P => Phi P = Q), Pf Q / Pf P
      ≤ (1 / Pf Q) * (9/10) := mul_le_mul_of_nonneg_left h (by have := Pf_pos Q; positivity)
    _ = 9/10 * (1 / Pf Q) := by ring

end A185895Proof

namespace A185895Proof
open scoped Classical

/- ## Part D: connection with `A185895` and the sign argument -/

/-- the set of strict partitions of `n` (as subsets of `Icc 1 n`) -/
def Parts (n : ℕ) : Finset (Finset ℕ) := (Icc 1 n).powerset.filter (fun t => ∑ x ∈ t, x = n)

lemma coeff_prod (n : ℕ) :
    (∏ k ∈ Icc 1 n, ((1 : ℚ[X]) - C ((1:ℚ) / (k.factorial : ℚ)) * X ^ k)).coeff n
      = ∑ t ∈ Parts n, (-1) ^ t.card / Pf t := by
  have h1 : ∀ k ∈ Icc 1 n, ((1 : ℚ[X]) - C ((1:ℚ) / (k.factorial : ℚ)) * X ^ k)
      = (C (-(1:ℚ) / (k.factorial : ℚ)) * X ^ k) + 1 := by
    intro k _
    rw [sub_eq_neg_add, ← neg_mul, ← C_neg, neg_div]
  rw [Finset.prod_congr rfl h1, Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  rw [Polynomial.finset_sum_coeff]
  have h2 : ∀ t ∈ (Icc 1 n).powerset, (∏ i ∈ t, C (-(1:ℚ) / (i.factorial : ℚ)) * X ^ i).coeff n
      = if ∑ x ∈ t, x = n then (-1) ^ t.card / Pf t else 0 := by
    intro t _
    rw [Finset.prod_mul_distrib, ← map_prod C, Finset.prod_pow_eq_pow_sum, coeff_C_mul_X_pow]
    have : ∏ i ∈ t, (-(1:ℚ) / (i.factorial : ℚ)) = (-1) ^ t.card / Pf t := by
      unfold Pf
      rw [Finset.prod_div_distrib, Finset.prod_const]
    rw [this]
    by_cases h : ∑ x ∈ t, x = n
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (Ne.symm h), if_neg h]
  rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
  rfl

lemma multinomial_eq (t : Finset ℕ) :
    (Nat.multinomial t id : ℚ) = ((∑ x ∈ t, x).factorial : ℚ) / Pf t := by
  have := Nat.multinomial_spec t id
  simp only [id] at this
  rw [eq_div_iff (Pf_pos t).ne']
  unfold Pf
  have h2 : ((∏ i ∈ t, i.factorial : ℕ) : ℚ) * (Nat.multinomial t id : ℚ)
      = (((∑ i ∈ t, i).factorial : ℕ) : ℚ) := by exact_mod_cast this
  push_cast at h2
  rw [mul_comm]; exact h2

lemma A185895_eq (n : ℕ) (hn : 1 ≤ n) :
    ((A185895 n : ℤ) : ℚ) = (n.factorial : ℚ) * ∑ t ∈ Parts n, (-1) ^ t.card / Pf t := by
  have hne : n ≠ 0 := by omega
  simp only [A185895, if_neg hne]
  rw [coeff_prod]
  have key : (∑ t ∈ Parts n, (-1) ^ t.card / Pf t) * (n.factorial : ℚ)
      = ((∑ t ∈ Parts n, (-1) ^ t.card * (Nat.multinomial t id : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    unfold Parts at ht
    rw [Finset.mem_filter] at ht
    rw [multinomial_eq, ht.2]
    ring
  rw [key, Rat.floor_intCast, ← key]
  ring


def e (j n : ℕ) : ℚ := ∑ X ∈ SP j 1 n, 1 / Pf X

lemma e_nonneg (j n : ℕ) : 0 ≤ e j n := by
  unfold e; apply Finset.sum_nonneg; intro X _; exact (one_div_pos.mpr (Pf_pos X)).le

lemma Parts_sum_eq (n : ℕ) :
    ∑ t ∈ Parts n, (-1 : ℚ) ^ t.card / Pf t = ∑ j ∈ range (n+1), (-1) ^ j * e j n := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n+1))]
  · apply Finset.sum_congr rfl
    intro j _
    unfold e
    rw [Finset.mul_sum]
    have : (Parts n).filter (fun t => t.card = j) = SP j 1 n := by
      unfold Parts SP
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro t _; constructor <;> rintro ⟨a, b⟩ <;> exact ⟨b, a⟩
    rw [this]
    apply Finset.sum_congr rfl
    intro X hX
    rw [mem_SP] at hX
    rw [hX.2.1]; ring
  · intro t ht
    unfold Parts at ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    rw [Finset.mem_range]
    have := Finset.card_le_card ht.1
    rw [Nat.card_Icc] at this; omega

lemma alt_pos (c : ℕ → ℚ) (m : ℕ) (hm : 1 ≤ m) (h0 : 0 ≤ c 0)
    (hlt : ∀ j, 1 ≤ j → j ≤ m → c (j-1) < c j) :
    0 < (-1) ^ m * ∑ j ∈ range (m+1), (-1) ^ j * c j ∧
    (-1) ^ m * ∑ j ∈ range (m+1), (-1) ^ j * c j ≤ c m := by
  induction m, hm using Nat.le_induction with
  | base =>
    have := hlt 1 le_rfl le_rfl
    simp only [Nat.sub_self] at this
    simp [Finset.sum_range_succ]
    constructor <;> linarith
  | succ m hm ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun j h1 h2 => hlt j h1 (by omega))
    have hc := hlt (m+1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hc
    have hs2 : (-1:ℚ)^m * (-1)^m = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [Finset.sum_range_succ, pow_succ]
    have e : (-1:ℚ)^m * (-1) * (∑ j ∈ range (m+1), (-1) ^ j * c j + (-1)^m * (-1) * c (m+1))
        = c (m+1) - (-1)^m * ∑ j ∈ range (m+1), (-1) ^ j * c j := by
      linear_combination (c (m+1)) * hs2
    rw [e]
    constructor <;> linarith

lemma sum_range_stable (c : ℕ → ℚ) (m : ℕ) (hz : ∀ j, m < j → c j = 0) :
    ∀ n, m ≤ n → ∑ j ∈ range (n+1), (-1 : ℚ) ^ j * c j = ∑ j ∈ range (m+1), (-1) ^ j * c j := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, hz (n+1) (by omega)]; ring

lemma k_le_Tri (k : ℕ) : k ≤ Tri k := by
  induction k with
  | zero => simp [Tri_zero]
  | succ k ih => rw [Tri_succ]; omega

lemma Tri_le_sum : ∀ (k : ℕ) (X : Finset ℕ), X.card = k → (∀ x ∈ X, 1 ≤ x) → Tri k ≤ ∑ x ∈ X, x := by
  intro k
  induction k with
  | zero => intro X _ _; simp [Tri_zero]
  | succ k ih =>
    intro X hcard hX
    have hne : X.Nonempty := by rw [← Finset.card_pos]; omega
    have hsub : X ⊆ Icc 1 (mx X) := by
      intro x hx; rw [Finset.mem_Icc]; exact ⟨hX x hx, le_mx hx⟩
    have hM : k + 1 ≤ mx X := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this; omega
    have h1 := ih (X.erase (mx X)) (by rw [Finset.card_erase_of_mem (mx_mem hne)]; omega)
      (fun x hx => hX x (Finset.mem_of_mem_erase hx))
    rw [← Finset.add_sum_erase X _ (mx_mem hne), Tri_succ]
    omega

noncomputable def mN (n : ℕ) : ℕ := Nat.findGreatest (fun k => Tri k ≤ n) n

lemma Tri_mN_le (n : ℕ) : Tri (mN n) ≤ n :=
  Nat.findGreatest_spec (P := fun k => Tri k ≤ n) (Nat.zero_le n) (by simp [Tri_zero])

lemma le_mN {k n : ℕ} (h : Tri k ≤ n) : k ≤ mN n :=
  Nat.le_findGreatest (le_trans (k_le_Tri k) h) h

lemma mN_le (n : ℕ) : mN n ≤ n := Nat.findGreatest_le n

lemma e_eq_zero_of_lt {j n : ℕ} (h : mN n < j) : e j n = 0 := by
  unfold e
  apply Finset.sum_eq_zero
  intro X hX
  exfalso
  rw [mem_SP] at hX
  obtain ⟨hsub, hcard, hsum⟩ := hX
  have := Tri_le_sum j X hcard (fun x hx => (Finset.mem_Icc.mp (hsub hx)).1)
  rw [hsum] at this
  have := le_mN this
  omega

lemma e_pos {j n : ℕ} (hj : 1 ≤ j) (hn : Tri j ≤ n) : 0 < e j n := by
  have hT : Tri j = Tri (j-1) + j := by
    have := Tri_succ (j-1); rw [show j - 1 + 1 = j by omega] at this; exact this
  have hnot : n - Tri (j-1) ∉ Icc 1 (j-1) := by rw [Finset.mem_Icc]; omega
  have hmem : insert (n - Tri (j-1)) (Icc 1 (j-1)) ∈ SP j 1 n := by
    rw [mem_SP]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_Icc] at hx
      rw [Finset.mem_Icc]
      have := k_le_Tri j
      rcases hx with h | h
      · omega
      · omega
    · rw [Finset.card_insert_of_notMem hnot, Nat.card_Icc]; omega
    · rw [Finset.sum_insert hnot]
      have : ∑ x ∈ Icc 1 (j-1), x = Tri (j-1) := rfl
      omega
  unfold e
  apply lt_of_lt_of_le (one_div_pos.mpr (Pf_pos _))
  apply Finset.single_le_sum (f := fun X => 1 / Pf X) _ hmem
  intro X _; exact (one_div_pos.mpr (Pf_pos X)).le

lemma e_zero {n : ℕ} (hn : 1 ≤ n) : e 0 n = 0 := by
  unfold e
  apply Finset.sum_eq_zero
  intro X hX
  exfalso
  rw [mem_SP] at hX
  obtain ⟨_, hcard, hsum⟩ := hX
  rw [Finset.card_eq_zero] at hcard
  subst hcard
  simp at hsum; omega

lemma e_lt {j n : ℕ} (hj : 1 ≤ j) (hn : Tri j ≤ n) (hn1 : 1 ≤ n) : e (j-1) n < e j n := by
  rcases Nat.lt_or_ge j 2 with h | h
  · have : j = 1 := by omega
    subst this
    simp only [Nat.sub_self]
    rw [e_zero hn1]
    exact e_pos le_rfl hn
  · have h1 := transport h hn
    have h2 := e_pos hj hn
    unfold e at h2 ⊢
    linarith

theorem sign_sum (n : ℕ) (hn : 1 ≤ n) :
    0 < (-1) ^ (mN n) * ∑ t ∈ Parts n, (-1 : ℚ) ^ t.card / Pf t := by
  rw [Parts_sum_eq, sum_range_stable (fun j => e j n) (mN n) (fun j hj => e_eq_zero_of_lt hj) n (mN_le n)]
  have hm : 1 ≤ mN n := le_mN (by simp [Tri, hn])
  exact (alt_pos (fun j => e j n) (mN n) hm (e_nonneg 0 n)
    (fun j h1 h2 => e_lt h1 (le_trans (Tri_mono h2) (Tri_mN_le n)) hn)).1

theorem sign_A (n : ℕ) : 0 < (-1 : ℤ) ^ (mN n) * A185895 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have : mN 0 = 0 := by have := mN_le 0; omega
    simp [this, A185895]
  · have h1 := sign_sum n h
    have h2 := A185895_eq n h
    have h3 : (0:ℚ) < ((-1 : ℤ) ^ (mN n) * A185895 n : ℤ) := by
      push_cast
      rw [h2]
      have hf : (0:ℚ) < (n.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos n
      calc (0:ℚ) < (n.factorial : ℚ) * ((-1) ^ (mN n) * ∑ t ∈ Parts n, (-1 : ℚ) ^ t.card / Pf t) :=
            mul_pos hf h1
        _ = _ := by ring
    exact_mod_cast h3

lemma mN_pred (n : ℕ) (hn : 1 ≤ n) : mN (n-1) ≤ mN n ∧ mN n ≤ mN (n-1) + 1 := by
  constructor
  · apply le_mN; have := Tri_mN_le (n-1); omega
  · by_contra h
    push_neg at h
    have h1 : Tri (mN (n-1) + 1) ≤ Tri (mN n) := Tri_mono (by omega)
    have h2 := Tri_mN_le n
    have h3 : ¬ (mN (n-1) + 1 ≤ mN (n-1)) := by omega
    have h4 : ¬ Tri (mN (n-1) + 1) ≤ n - 1 := fun hc => h3 (le_mN hc)
    have h5 := Tri_strictMono (show mN (n-1) + 1 < mN n by omega)
    omega

lemma mN_ne_iff (n : ℕ) (hn : 1 ≤ n) : mN n ≠ mN (n-1) ↔ Tri (mN n) = n := by
  constructor
  · intro h
    by_contra hne
    have : Tri (mN n) ≤ n - 1 := by have := Tri_mN_le n; omega
    have := le_mN this
    have := (mN_pred n hn).1
    omega
  · intro h e
    have : Tri (mN n) ≤ n - 1 := by
      have := Tri_mN_le (n-1); rw [← e] at this; exact this
    omega

lemma triangular_iff (n : ℕ) : is_triangular n ↔ Tri (mN n) = n := by
  constructor
  · rintro ⟨k, hk⟩
    have hk' : Tri k = n := by rw [Tri_eq]; exact hk.symm
    have h1 : k ≤ mN n := le_mN hk'.le
    have h2 : mN n ≤ k := by
      by_contra h; push_neg at h
      have := Tri_strictMono h
      have := Tri_mN_le n
      omega
    rw [le_antisymm h2 h1, hk']
  · intro h
    exact ⟨mN n, by rw [← Tri_eq, h]⟩

theorem main_theorem : ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  intro n hn
  rw [triangular_iff, ← mN_ne_iff n hn]
  have h1 := sign_A n
  have h2 := sign_A (n-1)
  obtain ⟨hle, hle'⟩ := mN_pred n hn
  constructor
  · intro hprod hne
    rw [hne] at h1
    have : 0 < ((-1 : ℤ) ^ (mN (n-1)) * A185895 n) * ((-1 : ℤ) ^ (mN (n-1)) * A185895 (n-1)) :=
      mul_pos h1 h2
    have hs : ((-1 : ℤ) ^ (mN (n-1))) * ((-1 : ℤ) ^ (mN (n-1))) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have : ((-1 : ℤ) ^ (mN (n-1)) * A185895 n) * ((-1 : ℤ) ^ (mN (n-1)) * A185895 (n-1))
        = A185895 n * A185895 (n-1) := by linear_combination (A185895 n * A185895 (n-1)) * hs
    linarith
  · intro hne
    have heq : mN n = mN (n-1) + 1 := by omega
    rw [heq, pow_succ] at h1
    have : 0 < ((-1 : ℤ) ^ (mN (n-1)) * (-1) * A185895 n) * ((-1 : ℤ) ^ (mN (n-1)) * A185895 (n-1)) :=
      mul_pos h1 h2
    have hs : ((-1 : ℤ) ^ (mN (n-1))) * ((-1 : ℤ) ^ (mN (n-1))) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have : ((-1 : ℤ) ^ (mN (n-1)) * (-1) * A185895 n) * ((-1 : ℤ) ^ (mN (n-1)) * A185895 (n-1))
        = -(A185895 n * A185895 (n-1)) := by linear_combination (-(A185895 n * A185895 (n-1))) * hs
    linarith

end A185895Proof
/--
Conjectures: 1) a(n) differs in sign from a(n-1) iff n is a triangular number (checked up to n = 1225 = (50*51)/2)
The condition "differs in sign" for $a(n)$ and $a(n-1)$ is formalized as their product being strictly negative.
We only consider $n \ge 1$.
-/
theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) :=
  A185895Proof.main_theorem

theorem oeis_185895_conjecture_1.disproof : ¬ (type_of% @oeis_185895_conjecture_1) := sorry
