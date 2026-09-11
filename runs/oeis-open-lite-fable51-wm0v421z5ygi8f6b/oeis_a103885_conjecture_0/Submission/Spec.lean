import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

noncomputable section

namespace A103885Proof

/-- P₁(x) = x² - x + 1/5 -/
def P1 (x : ℝ) : ℝ := x^2 - x + 1/5
def c0 (x : ℝ) : ℝ := 4 * (55 * x^4 - 34 * x^2 + 3)

/-- polynomial P₁(X + k) -/
def P1p (k : ℝ) : ℝ[X] := (X + C k)^2 - (X + C k) + C (1/5)
/-- polynomial P₁(-(X + k)) -/
def P1negp (k : ℝ) : ℝ[X] := (X + C k)^2 + (X + C k) + C (1/5)
/-- polynomial c₀(X + k) -/
def c0p (k : ℝ) : ℝ[X] := C 4 * (C 55 * (X + C k)^4 - C 34 * (X + C k)^2 + C 3)

@[simp] lemma eval_P1p (k x : ℝ) : (P1p k).eval x = P1 (x + k) := by
  simp [P1p, P1]
@[simp] lemma eval_P1negp (k x : ℝ) : (P1negp k).eval x = P1 (-(x + k)) := by
  simp [P1negp, P1]; ring
@[simp] lemma eval_c0p (k x : ℝ) : (c0p k).eval x = c0 (x + k) := by
  simp [c0p, c0]

lemma P1p_monic (k : ℝ) : (P1p k).Monic := by
  unfold P1p; monicity!

lemma P1p_ne_zero (k : ℝ) : P1p k ≠ 0 := (P1p_monic k).ne_zero

/-- right-hand side polynomial of the recurrence defining B (m+2) -/
def Brhs (Bm Bm1 : ℝ[X]) (m : ℕ) : ℝ[X] :=
  c0p (m+1) * Bm1 + C 400 * (X + C ((m:ℝ) + 1/2))^2 * (X + C (m:ℝ)) * (X + C ((m:ℝ)+1)) * P1negp ((m:ℝ)+1) * Bm

def B : ℕ → ℝ[X]
  | 0 => 0
  | 1 => P1p 1
  | (m+2) => Brhs (B m) (B (m+1)) m /ₘ P1p ((m:ℝ)+1)

lemma B_zero : B 0 = 0 := rfl
lemma B_one : B 1 = P1p 1 := rfl
lemma B_succ_succ (m : ℕ) : B (m+2) = Brhs (B m) (B (m+1)) m /ₘ P1p ((m:ℝ)+1) := rfl

def Bf (m : ℕ) (x : ℝ) : ℝ := (B m).eval x

lemma eval_Brhs (Bm Bm1 : ℝ[X]) (m : ℕ) (x : ℝ) :
    (Brhs Bm Bm1 m).eval x = c0 (x + (m+1)) * Bm1.eval x
      + 400 * (x + (m + 1/2))^2 * (x + m) * (x + (m+1)) * P1 (-(x + (m+1))) * Bm.eval x := by
  simp [Brhs]

lemma B_two : B 2 = c0p 1 := by
  rw [B_succ_succ]
  have : Brhs (B 0) (B 1) 0 = P1p ((0:ℕ) + 1 : ℝ) * c0p 1 := by
    simp [Brhs, B_zero, B_one]; ring
  rw [this, Polynomial.mul_divByMonic_cancel_left _ (P1p_monic _)]

end A103885Proof

namespace A103885Proof

/-! ### Roots of P₁ -/

def rho1 : ℝ := (5 - Real.sqrt 5) / 10
def rho2 : ℝ := (5 + Real.sqrt 5) / 10

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
lemma sqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
lemma sqrt5_lt : Real.sqrt 5 < 5 := by
  have h := sqrt5_sq
  nlinarith [sqrt5_pos]

lemma P1_factor (x : ℝ) : P1 x = (x - rho1) * (x - rho2) := by
  unfold P1 rho1 rho2
  have h := sqrt5_sq
  ring_nf
  rw [h]; ring

lemma rho1_ne_rho2 : rho1 ≠ rho2 := by
  unfold rho1 rho2; have := sqrt5_pos; intro h; linarith

lemma rho1_pos : 0 < rho1 := by unfold rho1; have := sqrt5_lt; linarith
lemma rho2_lt_one : rho2 < 1 := by unfold rho2; have := sqrt5_lt; linarith
lemma rho1_lt_rho2 : rho1 < rho2 := by unfold rho1 rho2; have := sqrt5_pos; linarith

lemma P1_rho1 : P1 rho1 = 0 := by rw [P1_factor]; ring
lemma P1_rho2 : P1 rho2 = 0 := by rw [P1_factor]; ring

lemma P1_pos_of_nonpos {y : ℝ} (hy : y ≤ 0) : 0 < P1 y := by
  unfold P1; nlinarith

lemma P1_pos_of_one_le {y : ℝ} (hy : 1 ≤ y) : 0 < P1 y := by
  unfold P1; nlinarith

lemma P1_ne_zero_of_ne {x : ℝ} (h1 : x ≠ rho1) (h2 : x ≠ rho2) : P1 x ≠ 0 := by
  rw [P1_factor]; exact mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)

lemma P1p_eq_prod (k : ℝ) : P1p k = (X - C (rho1 - k)) * (X - C (rho2 - k)) := by
  apply Polynomial.funext; intro x
  simp [P1_factor]; ring

/-- divisibility from two distinct roots -/
lemma dvd_of_two_roots (p : ℝ[X]) (a b : ℝ) (hab : a ≠ b) (ha : p.eval a = 0) (hb : p.eval b = 0) :
    (X - C a) * (X - C b) ∣ p := by
  have h1 : (X - C a) * (p /ₘ (X - C a)) = p :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr ha
  set q := p /ₘ (X - C a) with hq
  have hqb : q.eval b = 0 := by
    have : p.eval b = (b - a) * q.eval b := by
      conv_lhs => rw [← h1]
      simp
    rw [hb] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd (sub_eq_zero.mp h) (Ne.symm hab)
    · exact h
  have h2 : (X - C b) ∣ q := Polynomial.dvd_iff_isRoot.mpr hqb
  rw [← h1]
  exact mul_dvd_mul_left _ h2

lemma P1p_dvd_of_roots (k : ℝ) (p : ℝ[X]) (h1 : p.eval (rho1 - k) = 0) (h2 : p.eval (rho2 - k) = 0) :
    P1p k ∣ p := by
  rw [P1p_eq_prod]
  apply dvd_of_two_roots _ _ _ _ h1 h2
  intro h; exact rho1_ne_rho2 (by linarith)

/-- exactness of division -/
lemma divByMonic_exact (p q : ℝ[X]) (hq : q.Monic) (h : q ∣ p) : (p /ₘ q) * q = p := by
  have := Polynomial.modByMonic_add_div p hq
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd hq).mpr h, zero_add] at this
  rw [mul_comm]; exact this

/-! ### Continuity and cancellation -/

lemma continuous_Bf (m : ℕ) : Continuous (Bf m) := by
  unfold Bf; exact Polynomial.continuous _
lemma continuous_P1 : Continuous P1 := by unfold P1; fun_prop
lemma continuous_c0 : Continuous c0 := by unfold c0; fun_prop

lemma eq_of_eq_off_finite {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s : Set ℝ) (hs : s.Finite) (h : ∀ x ∉ s, f x = g x) : ∀ x, f x = g x := by
  have hd : Dense sᶜ := hs.countable.dense_compl ℝ
  have := Continuous.ext_on hd hf hg (fun x hx => h x hx)
  exact fun x => congrFun this x

lemma cancel_P1 (c : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, P1 (x + c) * f x = P1 (x + c) * g x) : ∀ x, f x = g x := by
  apply eq_of_eq_off_finite hf hg {rho1 - c, rho2 - c} (Set.toFinite _)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  have hne : P1 (x + c) ≠ 0 := by
    apply P1_ne_zero_of_ne
    · intro h'; exact hx.1 (by linarith)
    · intro h'; exact hx.2 (by linarith)
  exact mul_left_cancel₀ hne (h x)

end A103885Proof

namespace A103885Proof

/-- left recurrence: B_{m+2}(x) P₁(x+m+1) = c₀(x+m+1) B_{m+1}(x) + 400 (x+m+1/2)² (x+m)(x+m+1) P₁(-(x+m+1)) B_m(x) -/
def Lst (m : ℕ) : Prop := ∀ x : ℝ, Bf (m+2) x * P1 (x + ((m:ℝ)+1)) =
  c0 (x + ((m:ℝ)+1)) * Bf (m+1) x
    + 400 * (x + ((m:ℝ) + 1/2))^2 * (x + m) * (x + ((m:ℝ)+1)) * P1 (-(x + ((m:ℝ)+1))) * Bf m x

/-- right recurrence (shifted form) -/
def RRst (m : ℕ) : Prop := ∀ y : ℝ, Bf (m+2) (y-1) * P1 (y+1) =
  c0 y * Bf (m+1) y + 400 * y * (y + 1/2)^2 * (y+1) * P1 y * Bf m (y+1)

lemma Bf_zero (x : ℝ) : Bf 0 x = 0 := by simp [Bf, B_zero]
lemma Bf_one (x : ℝ) : Bf 1 x = P1 (x+1) := by simp [Bf, B_one]
lemma Bf_two (x : ℝ) : Bf 2 x = c0 (x+1) := by simp [Bf, B_two]

lemma Lst_of_exact (m : ℕ) (h : B (m+2) * P1p ((m:ℝ)+1) = Brhs (B m) (B (m+1)) m) : Lst m := by
  intro x
  have := congrArg (Polynomial.eval x) h
  simp only [Polynomial.eval_mul, eval_P1p, eval_Brhs] at this
  simpa [Bf] using this

lemma Lst_zero : Lst 0 := by
  intro x; simp only [Nat.reduceAdd, zero_add, Bf_zero, Bf_one, Bf_two, Nat.cast_zero]; unfold P1 c0; ring

lemma RRst_zero : RRst 0 := by
  intro y; simp only [Nat.reduceAdd, zero_add, Bf_zero, Bf_one, Bf_two, Nat.cast_zero]; unfold P1 c0; ring

lemma B_three_exact : B 3 * P1p ((1:ℕ) + 1 : ℝ) = Brhs (B 1) (B 2) 1 := by
  rw [show (3:ℕ) = 1 + 2 from rfl, B_succ_succ]
  apply divByMonic_exact _ _ (P1p_monic _)
  apply P1p_dvd_of_roots
  · rw [eval_Brhs]
    simp only [Nat.reduceAdd, B_one, B_two, eval_P1p, eval_c0p]
    have hr : rho1^2 - rho1 + 1/5 = 0 := by have := P1_rho1; unfold P1 at this; exact this
    unfold P1 c0; push_cast
    linear_combination (48800*rho1^6 - 146400*rho1^5 + 76260*rho1^4 + 91480*rho1^3 - 62240*rho1^2 - 7900*rho1 + 5760) * hr
  · rw [eval_Brhs]
    simp only [Nat.reduceAdd, B_one, B_two, eval_P1p, eval_c0p]
    have hr : rho2^2 - rho2 + 1/5 = 0 := by have := P1_rho2; unfold P1 at this; exact this
    unfold P1 c0; push_cast
    linear_combination (48800*rho2^6 - 146400*rho2^5 + 76260*rho2^4 + 91480*rho2^3 - 62240*rho2^2 - 7900*rho2 + 5760) * hr

lemma Lst_one : Lst 1 := Lst_of_exact 1 B_three_exact

lemma RRst_one : RRst 1 := by
  intro y
  have h := Lst_one (y-1)
  simp only [Nat.reduceAdd, Bf_one, Bf_two, Nat.cast_one] at h ⊢
  unfold P1 c0 at h ⊢
  linear_combination h

/-- The inductive step. -/
theorem LR_step (m : ℕ) (hL0 : Lst m) (hR0 : RRst m) (hL1 : Lst (m+1)) (hR1 : RRst (m+1)) :
    Lst (m+2) ∧ RRst (m+2) := by
  -- F x = eval (x-1) of Brhs (B (m+2)) (B (m+3)) (m+2); G as below
  set G : ℝ → ℝ := fun x => c0 x * Bf (m+3) x + 400 * x * (x + 1/2)^2 * (x+1) * P1 x * Bf (m+2) (x+1) with hG
  set F : ℝ → ℝ := fun x => (Brhs (B (m+2)) (B (m+3)) (m+2)).eval (x-1) with hF
  have comm : ∀ x, P1 (x + ((m:ℝ)+2)) * G x = P1 (x+1) * F x := by
    intro x
    have H2 := hL1 x
    have H4 := hL0 (x+1)
    have H5 := hR1 x
    have H7 := hR0 x
    simp only [hG, hF, eval_Brhs]
    simp only [Bf] at H2 H4 H5 H7 ⊢
    push_cast at H2 H4 H5 H7 ⊢
    unfold P1 c0 at H2 H4 H5 H7 ⊢
    linear_combination (4 * (55 * x^4 - 34 * x^2 + 3)) * H2
      + 400 * x * (x + 1/2)^2 * (x+1) * (x^2 - x + 1/5) * H4
      - (4 * (55 * (x + (m+2))^4 - 34 * (x+(m+2))^2 + 3)) * H5
      - 400 * (x + (m+2) - 1/2)^2 * (x + (m+2) - 1) * (x + (m+2)) * ((-(x+(m+2)))^2 - (-(x+(m+2))) + 1/5) * H7
  -- divisibility
  have hdvd : P1p (((m+2:ℕ):ℝ)+1) ∣ Brhs (B (m+2)) (B (m+3)) (m+2) := by
    apply P1p_dvd_of_roots
    · have h := comm (rho1 - ((m:ℝ)+2))
      have h0 : P1 (rho1 - ((m:ℝ)+2) + ((m:ℝ)+2)) = 0 := by rw [sub_add_cancel]; exact P1_rho1
      rw [h0, zero_mul] at h
      have hne : P1 (rho1 - ((m:ℝ)+2) + 1) ≠ 0 := by
        apply _root_.ne_of_gt; apply P1_pos_of_nonpos
        have := rho2_lt_one; have := rho1_lt_rho2; have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hF0 : F (rho1 - ((m:ℝ)+2)) = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' hne
        · exact h'
      simp only [hF] at hF0
      convert hF0 using 2; push_cast; ring
    · have h := comm (rho2 - ((m:ℝ)+2))
      have h0 : P1 (rho2 - ((m:ℝ)+2) + ((m:ℝ)+2)) = 0 := by rw [sub_add_cancel]; exact P1_rho2
      rw [h0, zero_mul] at h
      have hne : P1 (rho2 - ((m:ℝ)+2) + 1) ≠ 0 := by
        apply _root_.ne_of_gt; apply P1_pos_of_nonpos
        have := rho2_lt_one; have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hF0 : F (rho2 - ((m:ℝ)+2)) = 0 := by
        rcases mul_eq_zero.mp h.symm with h' | h'
        · exact absurd h' hne
        · exact h'
      simp only [hF] at hF0
      convert hF0 using 2; push_cast; ring
  have hex : B (m+4) * P1p (((m+2:ℕ):ℝ)+1) = Brhs (B (m+2)) (B (m+3)) (m+2) := by
    rw [show m + 4 = (m+2) + 2 from rfl, B_succ_succ]
    exact divByMonic_exact _ _ (P1p_monic _) hdvd
  have hL2 : Lst (m+2) := Lst_of_exact (m+2) hex
  refine ⟨hL2, ?_⟩
  -- RR (m+2) via cancellation
  have hFeq : ∀ y, F y = Bf (m+4) (y-1) * P1 (y + ((m:ℝ)+2)) := by
    intro y
    have := congrArg (Polynomial.eval (y-1)) hex
    simp only [Polynomial.eval_mul, eval_P1p] at this
    simp only [hF, Bf]
    rw [← this]; push_cast; ring_nf
  have key : ∀ y, P1 (y + ((m:ℝ)+2)) * G y = P1 (y + ((m:ℝ)+2)) * (Bf (m+4) (y-1) * P1 (y+1)) := by
    intro y; rw [comm y, hFeq y]; ring
  have hc := cancel_P1 ((m:ℝ)+2) (f := G) (g := fun y => Bf (m+4) (y-1) * P1 (y+1))
    (by simp only [hG]; have := continuous_Bf (m+3); have := continuous_Bf (m+2); have := continuous_P1; have := continuous_c0; fun_prop)
    (by have := continuous_Bf (m+4); have := continuous_P1; fun_prop) key
  intro y
  have := hc y
  simp only [hG] at this
  rw [this]

theorem LR_all (m : ℕ) : (Lst m ∧ RRst m) ∧ (Lst (m+1) ∧ RRst (m+1)) := by
  induction m with
  | zero => exact ⟨⟨Lst_zero, RRst_zero⟩, ⟨Lst_one, RRst_one⟩⟩
  | succ k ih =>
    obtain ⟨⟨hL0, hR0⟩, ⟨hL1, hR1⟩⟩ := ih
    exact ⟨⟨hL1, hR1⟩, LR_step k hL0 hR0 hL1 hR1⟩

theorem Lrec (m : ℕ) : Lst m := (LR_all m).1.1
theorem RRrec (m : ℕ) : RRst m := (LR_all m).1.2

end A103885Proof

namespace A103885Proof

def Symst (m : ℕ) : Prop := ∀ x : ℝ, Bf m (-x - m) = Bf m x

lemma Symst_zero : Symst 0 := by intro x; simp [Bf_zero]
lemma Symst_one : Symst 1 := by
  intro x; simp only [Bf_one, Nat.cast_one]; unfold P1; ring

theorem Sym_step (m : ℕ) (h0 : Symst m) (h1 : Symst (m+1)) : Symst (m+2) := by
  have key : ∀ x, P1 (x + 2) * Bf (m+2) (-x - ((m+2:ℕ):ℝ)) = P1 (x+2) * Bf (m+2) x := by
    intro x
    have hL := Lrec m (-x - ((m+2:ℕ):ℝ))
    have hR := RRrec m (x+1)
    have hs1 : Bf (m+1) (-x - ((m+2:ℕ):ℝ)) = Bf (m+1) (x+1) := by
      have := h1 (x+1); convert this using 2; push_cast; ring
    have hs0 : Bf m (-x - ((m+2:ℕ):ℝ)) = Bf m (x+2) := by
      have := h0 (x+2); convert this using 2; push_cast; ring
    rw [hs1, hs0] at hL
    rw [add_sub_cancel_right, show x + 1 + 1 = x + 2 by ring] at hR
    push_cast at hL hR ⊢
    unfold P1 c0 at hL hR
    unfold P1
    linear_combination hL - hR
  exact cancel_P1 2 (f := fun x => Bf (m+2) (-x - ((m+2:ℕ):ℝ))) (g := fun x => Bf (m+2) x)
    (by have := continuous_Bf (m+2); fun_prop) (continuous_Bf (m+2)) key

theorem Sym_all (m : ℕ) : Symst m ∧ Symst (m+1) := by
  induction m with
  | zero => exact ⟨Symst_zero, Symst_one⟩
  | succ k ih => exact ⟨ih.2, Sym_step k ih.1 ih.2⟩

theorem Bf_sym (m : ℕ) (x : ℝ) : Bf m (-x - m) = Bf m x := (Sym_all m).1 x

end A103885Proof

namespace A103885Proof

/-! ### Sign lemmas -/

lemma P1_neg_eq (y : ℝ) : P1 (-y) = P1 (y + 1) := by unfold P1; ring

lemma P1_half_int_pos (t : ℤ) (ht : t ≠ 1) : 0 < P1 ((t:ℝ)/2) := by
  rcases le_or_gt t 0 with h | h
  · apply P1_pos_of_nonpos; have : (t:ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  · have h2 : 2 ≤ t := by omega
    apply P1_pos_of_one_le; have : (2:ℝ) ≤ t := by exact_mod_cast h2
    linarith

lemma P1_half_neg : P1 (1/2) < 0 := by unfold P1; norm_num

lemma c0_half_int_pos (t : ℤ) (h1 : t ≠ 1) (h2 : t ≠ -1) : 0 < c0 ((t:ℝ)/2) := by
  rcases eq_or_ne t 0 with h | h
  · subst h; unfold c0; norm_num
  · have h4 : (4:ℝ) ≤ (t:ℝ)^2 := by
      rcases le_or_gt 2 t with h3 | h3
      · have : (2:ℝ) ≤ t := by exact_mod_cast h3
        nlinarith
      · have h5 : t ≤ -2 := by omega
        have : (t:ℝ) ≤ -2 := by exact_mod_cast h5
        nlinarith
    unfold c0
    nlinarith [sq_nonneg ((t:ℝ)^2 - 4)]

lemma c0_half_neg : c0 (1/2) < 0 := by unfold c0; norm_num
lemma c0_neg_half_neg : c0 (-1/2) < 0 := by unfold c0; norm_num

lemma sign_aux_pos {A P R : ℝ} (hP : 0 < P) (h : A * P = R) (hR : 0 < R) : 0 < A := by
  by_contra hA; push_neg at hA; nlinarith
lemma sign_aux_neg {A P R : ℝ} (hP : 0 < P) (h : A * P = R) (hR : R < 0) : A < 0 := by
  by_contra hA; push_neg at hA; nlinarith
lemma sign_aux_neg' {A P R : ℝ} (hP : P < 0) (h : A * P = R) (hR : 0 < R) : A < 0 := by
  by_contra hA; push_neg at hA; nlinarith

/-- Core sign step, with abstract values. Here `t = 2m+2-j`. -/
lemma Sst_step_core (m : ℕ) (t : ℤ) (A2 A1 A0 : ℝ)
    (hL : A2 * P1 ((t:ℝ)/2) = c0 ((t:ℝ)/2) * A1
      + 400 * (((t:ℝ)-1)/2)^2 * (((t:ℝ)-2)/2) * ((t:ℝ)/2) * P1 ((t:ℝ)/2+1) * A0)
    (h1n : t % 2 = 1 → 0 ≤ t → t ≤ 2*(m:ℤ)+2 → A1 < 0)
    (h1p : t % 2 = 0 ∨ t < 0 ∨ 2*(m:ℤ)+2 < t → 0 < A1)
    (h0n : t % 2 = 1 → 2 ≤ t → t ≤ 2*(m:ℤ)+2 → A0 < 0)
    (h0p : t % 2 = 0 ∨ t < 2 ∨ 2*(m:ℤ)+2 < t → 0 < A0) :
    (t % 2 = 1 → -2 ≤ t → t ≤ 2*(m:ℤ)+2 → A2 < 0) ∧
    (t % 2 = 0 ∨ t < -2 ∨ 2*(m:ℤ)+2 < t → 0 < A2) := by
  rcases le_or_gt 3 t with ht | ht
  · -- t ≥ 3
    have ht' : (3:ℝ) ≤ t := by exact_mod_cast ht
    have hP := P1_half_int_pos t (by omega)
    have hc := c0_half_int_pos t (by omega) (by omega)
    have hP2 : 0 < P1 ((t:ℝ)/2 + 1) := P1_pos_of_one_le (by linarith)
    have hprod : 0 < 400 * (((t:ℝ)-1)/2)^2 * (((t:ℝ)-2)/2) * ((t:ℝ)/2) * P1 ((t:ℝ)/2 + 1) :=
      mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (by apply pow_pos; linarith))
        (by linarith)) (by linarith)) hP2
    constructor
    · intro ho hj0 hj1
      have b1 := h1n ho (by omega) hj1
      have b0 := h0n ho (by omega) hj1
      apply sign_aux_neg hP hL
      have := mul_neg_of_pos_of_neg hc b1; have := mul_neg_of_pos_of_neg hprod b0; linarith
    · intro h
      have b1 := h1p (by omega)
      have b0 := h0p (by omega)
      apply sign_aux_pos hP hL
      have := mul_pos hc b1; have := mul_pos hprod b0; linarith
  rcases le_or_gt t (-3) with ht2 | ht2
  · -- t ≤ -3
    have ht' : (t:ℝ) ≤ -3 := by exact_mod_cast ht2
    have hP := P1_half_int_pos t (by omega)
    have hc := c0_half_int_pos t (by omega) (by omega)
    have hP2 : 0 < P1 ((t:ℝ)/2 + 1) := P1_pos_of_nonpos (by linarith)
    have hprod : 0 < 400 * (((t:ℝ)-1)/2)^2 * (((t:ℝ)-2)/2) * ((t:ℝ)/2) * P1 ((t:ℝ)/2 + 1) :=
      mul_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (mul_pos (by norm_num)
        (by have : ((t:ℝ)-1)/2 ≠ 0 := by linarith
            positivity)) (by linarith)) (by linarith)) hP2
    constructor
    · intro ho hj0 hj1; omega
    · intro h
      have b1 := h1p (by omega)
      have b0 := h0p (by omega)
      apply sign_aux_pos hP hL
      have := mul_pos hc b1; have := mul_pos hprod b0; linarith
  have hlo : -2 ≤ t := by omega
  have hhi : t ≤ 2 := by omega
  interval_cases t
  · -- t = -2
    norm_num [P1, c0] at hL
    have b1 := h1p (by omega)
    have b0 := h0p (by omega)
    constructor
    · intro ho; omega
    · intro _; nlinarith
  · -- t = -1
    norm_num [P1, c0] at hL
    have b1 := h1p (by omega)
    have b0 := h0p (by omega)
    constructor
    · intro _ _ _; nlinarith
    · intro h; omega
  · -- t = 0
    norm_num [P1, c0] at hL
    have b1 := h1p (by omega)
    constructor
    · intro ho; omega
    · intro _; nlinarith
  · -- t = 1
    norm_num [P1, c0] at hL
    have b1 := h1n (by omega) (by omega) (by omega)
    constructor
    · intro _ _ _; nlinarith
    · intro h; omega
  · -- t = 2
    norm_num [P1, c0] at hL
    have b1 := h1p (by omega)
    constructor
    · intro ho; omega
    · intro _; nlinarith

end A103885Proof

namespace A103885Proof

/-- Sign pattern of `B m` at half-integers `-j/2`. -/
def Sst (m : ℕ) : Prop := ∀ j : ℤ,
  (j % 2 = 1 → 0 ≤ j → j ≤ 2*(m:ℤ) → Bf m (-(j:ℝ)/2) < 0) ∧
  ((j % 2 = 0 ∨ j < 0 ∨ 2*(m:ℤ) < j) → 0 < Bf m (-(j:ℝ)/2))

lemma Sst_one : Sst 1 := by
  intro j
  rw [Bf_one]
  have e : -(j:ℝ)/2 + 1 = ((2 - j : ℤ):ℝ)/2 := by push_cast; ring
  rw [e]
  constructor
  · intro h1 h2 h3
    have : j = 1 := by omega
    subst this; norm_num; exact P1_half_neg
  · intro h
    apply P1_half_int_pos; omega

lemma Sst_two : Sst 2 := by
  intro j
  rw [Bf_two]
  have e : -(j:ℝ)/2 + 1 = ((2 - j : ℤ):ℝ)/2 := by push_cast; ring
  rw [e]
  constructor
  · intro h1 h2 h3
    have : j = 1 ∨ j = 3 := by omega
    rcases this with rfl | rfl
    · norm_num; exact c0_half_neg
    · have := c0_neg_half_neg; norm_num at this ⊢; exact this
  · intro h
    apply c0_half_int_pos <;> omega

theorem Sst_step (m : ℕ) (h0 : Sst m) (h1 : Sst (m+1)) : Sst (m+2) := by
  intro j
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, j = 2*(m:ℤ)+2 - t := ⟨2*(m:ℤ)+2-j, by ring⟩
  have hL := Lrec m (-(((2*(m:ℤ)+2-t : ℤ)) : ℝ)/2)
  have e1 : -(((2*(m:ℤ)+2-t : ℤ)) : ℝ)/2 + ((m:ℝ)+1) = (t:ℝ)/2 := by push_cast; ring
  have e2 : -(((2*(m:ℤ)+2-t : ℤ)) : ℝ)/2 + (m:ℝ) = ((t:ℝ)-2)/2 := by push_cast; ring
  have e3 : -(((2*(m:ℤ)+2-t : ℤ)) : ℝ)/2 + ((m:ℝ)+1/2) = ((t:ℝ)-1)/2 := by push_cast; ring
  rw [e1, e2, e3, P1_neg_eq] at hL
  have hB1 := h1 (2*(m:ℤ)+2-t)
  have hB0 := h0 (2*(m:ℤ)+2-t)
  push_cast at hB1 hB0 hL ⊢
  have := Sst_step_core m t _ _ _ hL
    (fun a b c => hB1.1 (by omega) (by omega) (by omega))
    (fun a => hB1.2 (by omega))
    (fun a b c => hB0.1 (by omega) (by omega) (by omega))
    (fun a => hB0.2 (by omega))
  constructor
  · intro a b c; exact this.1 (by omega) (by omega) (by omega)
  · intro a; exact this.2 (by omega)

theorem Sst_all (m : ℕ) : Sst (m+1) ∧ Sst (m+2) := by
  induction m with
  | zero => exact ⟨Sst_one, Sst_two⟩
  | succ k ih => exact ⟨ih.2, Sst_step (k+1) ih.1 ih.2⟩

theorem Bf_sign (m : ℕ) (hm : 1 ≤ m) : Sst m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m-1, by omega⟩
  exact (Sst_all k).1

end A103885Proof
namespace A103885Proof

/-! ### Degree bounds -/

lemma natDegree_P1p (k : ℝ) : (P1p k).natDegree = 2 := by
  unfold P1p; compute_degree!

lemma natDegree_P1negp_le (k : ℝ) : (P1negp k).natDegree ≤ 2 := by
  unfold P1negp; compute_degree!

lemma natDegree_c0p_le (k : ℝ) : (c0p k).natDegree ≤ 4 := by
  unfold c0p; compute_degree!

lemma natDegree_Brhs_le (Bm Bm1 : ℝ[X]) (m d : ℕ) (h0 : Bm.natDegree ≤ d) (h1 : Bm1.natDegree ≤ d + 2) :
    (Brhs Bm Bm1 m).natDegree ≤ d + 6 := by
  unfold Brhs
  apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_le.trans (by have := natDegree_c0p_le ((m:ℝ)+1); omega)
  · have hX : ∀ c : ℝ, (X + C c).natDegree ≤ 1 := fun c => (natDegree_X_add_C c).le
    have hsq : ((X + C ((m:ℝ) + 1/2))^2).natDegree ≤ 2 :=
      natDegree_pow_le.trans (by have := hX ((m:ℝ) + 1/2); omega)
    have hC : (C (400:ℝ)).natDegree ≤ 0 := (natDegree_C _).le
    refine natDegree_mul_le.trans ?_
    have h5 := natDegree_P1negp_le ((m:ℝ)+1)
    have := hX (m:ℝ); have := hX ((m:ℝ)+1)
    have a1 := natDegree_mul_le (p := C (400:ℝ)) (q := (X + C ((m:ℝ) + 1/2))^2)
    have a2 := natDegree_mul_le (p := C (400:ℝ) * (X + C ((m:ℝ) + 1/2))^2) (q := X + C (m:ℝ))
    have a3 := natDegree_mul_le (p := C (400:ℝ) * (X + C ((m:ℝ) + 1/2))^2 * (X + C (m:ℝ))) (q := X + C ((m:ℝ)+1))
    have a4 := natDegree_mul_le (p := C (400:ℝ) * (X + C ((m:ℝ) + 1/2))^2 * (X + C (m:ℝ)) * (X + C ((m:ℝ)+1))) (q := P1negp ((m:ℝ)+1))
    omega

lemma natDegree_B_le_aux (m : ℕ) : (B m).natDegree ≤ 2*m ∧ (B (m+1)).natDegree ≤ 2*(m+1) := by
  induction m with
  | zero => exact ⟨by simp [B_zero], by rw [B_one, natDegree_P1p]⟩
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [show k + 1 + 1 = k + 2 from rfl, B_succ_succ, natDegree_divByMonic _ (P1p_monic _), natDegree_P1p]
    have := natDegree_Brhs_le (B k) (B (k+1)) k (2*k) ih.1 (by have := ih.2; omega)
    omega

lemma natDegree_B_le (m : ℕ) : (B m).natDegree ≤ 2*m := (natDegree_B_le_aux m).1

/-! ### Roots from sign changes -/

lemma roots_from_signs {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) (a : ℕ → ℝ) (ha : StrictMono a)
    (hs : ∀ j, j ≤ n → (Even j → 0 < f (a j)) ∧ (Odd j → f (a j) < 0)) :
    ∃ Z : Finset ℝ, Z.card = n ∧ ∀ r ∈ Z, f r = 0 ∧ a 0 < r ∧ r < a n := by
  have key : ∀ j, j < n → ∃ r, a j < r ∧ r < a (j+1) ∧ f r = 0 := by
    intro j hj
    have hc : ContinuousOn f (Set.Icc (a j) (a (j+1))) := hf.continuousOn
    have hle : a j ≤ a (j+1) := (ha (Nat.lt_succ_self j)).le
    rcases Nat.even_or_odd j with he | ho
    · have h1 : 0 < f (a j) := (hs j (by omega)).1 he
      have h2 : f (a (j+1)) < 0 := (hs (j+1) (by omega)).2 he.add_one
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hle hc (show (0:ℝ) ∈ Set.Ioo (f (a (j+1))) (f (a j)) from ⟨h2, h1⟩)
      exact ⟨r, hr.1, hr.2, hr0⟩
    · have h1 : f (a j) < 0 := (hs j (by omega)).2 ho
      have h2 : 0 < f (a (j+1)) := (hs (j+1) (by omega)).1 ho.add_one
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hle hc (show (0:ℝ) ∈ Set.Ioo (f (a j)) (f (a (j+1))) from ⟨h1, h2⟩)
      exact ⟨r, hr.1, hr.2, hr0⟩
  choose! r hr using key
  refine ⟨(Finset.range n).image r, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := (hr i hi).2.1; have h2 := (hr j hj).1
      have h3 := ha.monotone (show i+1 ≤ j by omega)
      linarith
    · have h1 := (hr j hj).2.1; have h2 := (hr i hi).1
      have h3 := ha.monotone (show j+1 ≤ i by omega)
      linarith
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨(hr j hj).2.2, ?_, ?_⟩
    · have := ha.monotone (Nat.zero_le j); linarith [(hr j hj).1]
    · have := ha.monotone (show j+1 ≤ n by omega); linarith [(hr j hj).2.1]

/-! ### Complex roots of a real polynomial with enough real roots -/

lemma complex_roots_of_real_roots (p : ℝ[X]) (hp : p ≠ 0) (Z : Finset ℝ)
    (hZ : ∀ r ∈ Z, p.eval r = 0) (hcard : p.natDegree ≤ Z.card) (z : ℂ)
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) : ∃ r ∈ Z, z = (r : ℂ) := by
  set pc := p.map (algebraMap ℝ ℂ) with hpc_def
  have hpc : pc ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp
  have hdeg : pc.natDegree = p.natDegree := natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective p
  have hroots : ∀ r ∈ Z, (r:ℂ) ∈ pc.roots := by
    intro r hr
    rw [mem_roots hpc, IsRoot, hpc_def, eval_map]
    have := eval₂_at_apply (algebraMap ℝ ℂ) r (p := p)
    simp only [Complex.coe_algebraMap] at this
    rw [this, hZ r hr, Complex.ofReal_zero]
  by_contra hne; push_neg at hne
  have hsub : (insert z (Z.image (fun r : ℝ => (r:ℂ)))).val ⊆ pc.roots := by
    intro w hw
    simp only [Finset.insert_val, Finset.image_val] at hw
    rw [Multiset.mem_ndinsert] at hw
    rcases hw with rfl | hw
    · exact (mem_roots hpc).mpr hz
    · rw [Multiset.mem_dedup, Multiset.mem_map] at hw
      obtain ⟨r, hr, rfl⟩ := hw
      exact hroots r hr
  have h1 := card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ Complex.ofReal_injective, hdeg] at h1
  · omega
  · simp only [Finset.mem_image, not_exists, not_and]
    intro r hr h; exact hne r hr h.symm

end A103885Proof

namespace A103885Proof

/-! ### Roots of B m -/

lemma B_roots (m : ℕ) (hm : 1 ≤ m) :
    ∃ Z : Finset ℝ, Z.card = 2*m ∧ ∀ r ∈ Z, Bf m r = 0 ∧ -(m:ℝ) < r ∧ r < 0 := by
  have hS := Bf_sign m hm
  have hs : ∀ j, j ≤ 2*m → (Even j → 0 < Bf m (((j:ℝ) - 2*m)/2)) ∧ (Odd j → Bf m (((j:ℝ) - 2*m)/2) < 0) := by
    intro j hj
    have e : ((j:ℝ) - 2*m)/2 = -(((2*(m:ℤ) - j : ℤ)):ℝ)/2 := by push_cast; ring
    rw [e]
    constructor
    · intro he; apply (hS _).2; left; obtain ⟨k, hk⟩ := he; omega
    · intro ho; obtain ⟨k, hk⟩ := ho
      apply (hS _).1 <;> omega
  obtain ⟨Z, hZc, hZ⟩ := roots_from_signs (continuous_Bf m) (2*m) (fun j => ((j:ℝ) - 2*m)/2)
    (by intro i j hij; simp only; have : (i:ℝ) < j := by exact_mod_cast hij
        linarith) hs
  refine ⟨Z, hZc, fun r hr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hZ r hr
  simp only [Nat.cast_zero, Nat.cast_mul, Nat.cast_ofNat] at h2 h3
  exact ⟨h1, by linarith, by linarith⟩

/-! ### The composed polynomials -/

/-- `Gp m k = B_k (m x - m)` -/
def Gp (m k : ℕ) : ℝ[X] := (B k).comp (C (m:ℝ) * X - C (m:ℝ))

lemma eval_Gp (m k : ℕ) (x : ℝ) : (Gp m k).eval x = Bf k (m*x - m) := by
  simp [Gp, Bf, eval_comp]

lemma Gp_ne_zero (m k : ℕ) (hk : 1 ≤ k) : Gp m k ≠ 0 := by
  intro h
  have := eval_Gp m k 1
  rw [h, eval_zero] at this
  have hpos := ((Bf_sign k hk) 0).2 (by left; rfl)
  simp at hpos this
  rw [← this] at hpos; exact lt_irrefl _ hpos

lemma natDegree_Gp_le (m k : ℕ) : (Gp m k).natDegree ≤ 2*k := by
  unfold Gp
  refine natDegree_comp_le.trans ?_
  have h1 : (C (m:ℝ) * X - C (m:ℝ)).natDegree ≤ 1 := by compute_degree
  have := natDegree_B_le k
  nlinarith

lemma Gp_roots (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    ∃ Z : Finset ℝ, Z.card = 2*k ∧ ∀ r ∈ Z, (Gp m k).eval r = 0 ∧ 1 - (k:ℝ)/m < r ∧ r < 1 := by
  obtain ⟨Z, hZc, hZ⟩ := B_roots k hk
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  refine ⟨Z.image (fun r => (r + m)/m), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ?_, hZc]
    intro a b hab
    simp only at hab
    have := hmpos.ne'
    field_simp at hab
    linarith
  · intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    obtain ⟨h1, h2, h3⟩ := hZ r hr
    refine ⟨?_, ?_, ?_⟩
    · rw [eval_Gp]; convert h1 using 2; field_simp; ring
    · rw [lt_div_iff₀ hmpos]; rw [sub_mul, div_mul_cancel₀ _ hmpos.ne']; linarith
    · rw [div_lt_iff₀ hmpos]; linarith

lemma Gp_natDegree (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) : (Gp m k).natDegree = 2*k := by
  obtain ⟨Z, hZc, hZ⟩ := Gp_roots m k hm hk
  apply le_antisymm (natDegree_Gp_le m k)
  rw [← hZc]
  apply card_le_degree_of_subset_roots
  intro r hr
  rw [Finset.mem_val] at hr
  rw [mem_roots (Gp_ne_zero m k hk)]
  exact (hZ r hr).1

lemma Gp_complex_roots (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (z : ℂ)
    (hz : ((Gp m k).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ 1 - (k:ℝ)/m < z.re ∧ z.re < 1 := by
  obtain ⟨Z, hZc, hZ⟩ := Gp_roots m k hm hk
  obtain ⟨r, hr, rfl⟩ := complex_roots_of_real_roots (Gp m k) (Gp_ne_zero m k hk) Z
    (fun r hr => (hZ r hr).1) (by rw [Gp_natDegree m k hm hk, hZc]) z hz
  obtain ⟨_, h2, h3⟩ := hZ r hr
  exact ⟨Complex.ofReal_im r, by simpa using h2, by simpa using h3⟩

/-! ### Even polynomials and contract -/

lemma coeff_comp_neg_X (p : ℝ[X]) (n : ℕ) : (p.comp (-X)).coeff n = (-1)^n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq, mul_add]
  | monomial k a =>
    rw [monomial_comp, neg_pow, show ((-1 : ℝ[X])^k) = C ((-1)^k) by simp, ← mul_assoc, ← C_mul,
      coeff_C_mul_X_pow, coeff_monomial]
    split_ifs with h1 h2 h2
    · subst h1; ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring

lemma even_expand_contract (E : ℝ[X]) (hE : ∀ x, E.eval (-x) = E.eval x) :
    expand ℝ 2 (contract 2 E) = E := by
  have hcomp : E.comp (-X) = E := Polynomial.funext (fun x => by simp [eval_comp, hE])
  have hodd : ∀ n, Odd n → E.coeff n = 0 := by
    intro n hn
    have := coeff_comp_neg_X E n
    rw [hcomp, hn.neg_one_pow] at this
    linarith
  ext n
  rw [coeff_expand (by norm_num), coeff_contract (by norm_num)]
  split_ifs with h
  · rw [Nat.div_mul_cancel h]
  · rw [hodd n (Nat.odd_iff.mpr (by omega))]

end A103885Proof

namespace A103885Proof
open scoped PowerSeries

/-! ### Power series: a(n) = [x^{2n}] ((1+x)/(1-x))^n -/

open PowerSeries in
/-- g = (1+X)/(1-X) -/
def g : ℝ⟦X⟧ := (1 + PowerSeries.X) * PowerSeries.mk 1

/-- e n j = coefficient of X^j in g^n -/
def e (n j : ℕ) : ℝ := PowerSeries.coeff j (g ^ n)

lemma one_sub_X_mul_g : (1 - PowerSeries.X) * g = 1 + PowerSeries.X := by
  unfold g; rw [mul_comm, mul_assoc, PowerSeries.mk_one_mul_one_sub_eq_one, mul_one]

lemma R1 (n j : ℕ) : e (n+1) (j+1) - e (n+1) j = e n (j+1) + e n j := by
  have h : (1 - PowerSeries.X) * g^(n+1) = (1 + PowerSeries.X) * g^n := by
    linear_combination (g^n) * one_sub_X_mul_g
  have := congrArg (PowerSeries.coeff (j+1)) h
  simp only [sub_mul, add_mul, one_mul, map_sub, map_add, PowerSeries.coeff_succ_X_mul] at this
  unfold e; linear_combination this

lemma D_mk_one : (1 - PowerSeries.X) * PowerSeries.derivative ℝ (PowerSeries.mk 1) = PowerSeries.mk 1 := by
  have h := congrArg (PowerSeries.derivative ℝ) (PowerSeries.mk_one_mul_one_sub_eq_one (S := ℝ))
  simp only [Derivation.leibniz, Derivation.map_one_eq_zero, map_sub, PowerSeries.derivative_X, smul_eq_mul] at h
  linear_combination h

lemma D_g : (1 - PowerSeries.X) * PowerSeries.derivative ℝ g = 1 + g := by
  have h : PowerSeries.derivative ℝ g = (1 + PowerSeries.X) * PowerSeries.derivative ℝ (PowerSeries.mk 1) + PowerSeries.mk 1 := by
    unfold g
    simp only [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul]
    ring
  have h2 := D_mk_one
  have h3 : g = (1 + PowerSeries.X) * PowerSeries.mk 1 := rfl
  have h4 := PowerSeries.mk_one_mul_one_sub_eq_one (S := ℝ)
  rw [h]
  linear_combination (1 + PowerSeries.X) * h2 - h3 + h4

lemma D_g_pow (n : ℕ) : (1 - PowerSeries.X^2) * PowerSeries.derivative ℝ (g^(n+1))
    = PowerSeries.C (2*((n:ℝ)+1)) * g^(n+1) := by
  have hpow := Derivation.leibniz_pow (PowerSeries.derivative ℝ) g (n+1)
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one] at hpow
  have hC : (PowerSeries.C (2*((n:ℝ)+1)) : ℝ⟦X⟧) = 2 * ((n : ℝ⟦X⟧) + 1) := by
    simp only [map_mul, map_add, map_natCast, map_one, map_ofNat]
  rw [hC, hpow]
  have h1 := D_g
  have h2 := one_sub_X_mul_g
  linear_combination (((n:ℝ⟦X⟧)+1) * g^n * (1 + PowerSeries.X)) * h1 - (((n:ℝ⟦X⟧)+1) * g^n) * h2

lemma R2_succ_succ (n j : ℕ) : ((j:ℝ)+3) * e (n+1) (j+3) - ((j:ℝ)+1) * e (n+1) (j+1) = 2*((n:ℝ)+1) * e (n+1) (j+2) := by
  have := congrArg (PowerSeries.coeff (j+2)) (D_g_pow n)
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative, if_pos (by omega), Nat.add_sub_cancel, PowerSeries.coeff_derivative] at this
  unfold e; push_cast at this; linear_combination this

lemma R2_succ_zero (n : ℕ) : 2 * e (n+1) 2 = 2*((n:ℝ)+1) * e (n+1) 1 := by
  have := congrArg (PowerSeries.coeff 1) (D_g_pow n)
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative, if_neg (by omega)] at this
  unfold e; push_cast at this; linear_combination this

lemma e_zero (j : ℕ) : e 0 j = if j = 0 then 1 else 0 := by
  unfold e; rw [pow_zero, PowerSeries.coeff_one]

lemma R2 (n j : ℕ) : ((j:ℝ)+2) * e n (j+2) - j * e n j = 2*(n:ℝ) * e n (j+1) := by
  cases n with
  | zero => simp [e_zero]
  | succ n =>
    cases j with
    | zero => have := R2_succ_zero n; push_cast; linear_combination this
    | succ j => have := R2_succ_succ n j; push_cast at this ⊢; linear_combination this

lemma coeff_one_add_X_pow' (n k : ℕ) :
    PowerSeries.coeff k ((1 + PowerSeries.X : ℝ⟦X⟧)^n) = (n.choose k : ℝ) := by
  have := Polynomial.coeff_one_add_X_pow ℝ n k
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X] at this
  exact this

lemma A103885_zero : A103885 0 = 1 := by simp [A103885]

lemma A103885_succ (d : ℕ) : A103885 (d+1) =
    (Finset.range (d+2)).sum (fun k => (d+1).choose k * (2*d+1+k).choose d) := by
  simp only [A103885, Nat.add_eq_zero, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  congr 2; omega

lemma sum_range_add_zero_tail (f : ℕ → ℝ) (n m : ℕ) (h : ∀ x, n ≤ x → f x = 0) :
    ∑ x ∈ Finset.range (n+m), f x = ∑ x ∈ Finset.range n, f x := by
  rw [Finset.sum_range_add, Finset.sum_eq_zero (fun x _ => h (n + x) (by omega)), add_zero]

lemma A_eq_e (n : ℕ) : (A103885 n : ℝ) = e n (2*n) := by
  cases n with
  | zero => simp [A103885_zero, e_zero]
  | succ d =>
    rw [A103885_succ]
    unfold e g
    rw [mul_pow, PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_one_add_X_pow', PowerSeries.coeff_mk]
    push_cast
    rw [show (2*(d+1)).succ = (d+2) + (d+1) by omega]
    rw [sum_range_add_zero_tail _ (d+2) (d+1) (fun x hx => by
      rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)]
    conv_rhs => rw [← Finset.sum_range_reflect _ (d+2)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show d + 2 - 1 - k = d + 1 - k by omega, Nat.choose_symm (by omega)]
    congr 3
    omega

/-- The shifted sequence: aS 0 = -4, aS (k+1) = a(k). -/
def aS : ℕ → ℝ
  | 0 => -4
  | (k+1) => (A103885 k : ℝ)

lemma aS_zero : aS 0 = -4 := rfl
lemma aS_succ (k : ℕ) : aS (k+1) = e k (2*k) := by simp [aS, A_eq_e]

lemma A103885_one : A103885 1 = 2 := by decide

/-- The three-term recurrence for a(n), in shifted form. -/
theorem a_rec (N : ℕ) :
    20 * ((N:ℝ) + 1/2) * ((N:ℝ) + 1) * P1 N * aS (N+2)
      - 20 * ((N:ℝ) - 1/2) * ((N:ℝ) - 1) * P1 (-(N:ℝ)) * aS N = c0 N * aS (N+1) := by
  cases N with
  | zero =>
    simp only [aS, A103885_zero, A103885_one, Nat.cast_zero]
    unfold P1 c0; norm_num
  | succ k =>
    rw [aS_succ, aS_succ, aS_succ]
    have r00 := R1 k (2*k); have r01 := R1 k (2*k+1); have r02 := R1 k (2*k+2); have r03 := R1 k (2*k+3)
    have r10 := R1 (k+1) (2*k); have r11 := R1 (k+1) (2*k+1); have r12 := R1 (k+1) (2*k+2); have r13 := R1 (k+1) (2*k+3)
    have s00 := R2 k (2*k); have s01 := R2 k (2*k+1); have s02 := R2 k (2*k+2)
    have s10 := R2 (k+1) (2*k); have s20 := R2 (k+2) (2*k)
    unfold P1 c0
    push_cast at *
    ring_nf at *
    have hk : (0:ℝ) < (k:ℝ) + 1 := by positivity
    apply mul_left_cancel₀ hk.ne'
    linear_combination
      (-40*(k:ℝ)^5-130*(k:ℝ)^4-138*(k:ℝ)^3-54*(k:ℝ)^2-4*(k:ℝ)) * r00
      + (-120*(k:ℝ)^5-500*(k:ℝ)^4-764*(k:ℝ)^3-528*(k:ℝ)^2-160*(k:ℝ)-16) * r01
      + (60*(k:ℝ)^5+330*(k:ℝ)^4+672*(k:ℝ)^3+624*(k:ℝ)^2+258*(k:ℝ)+36) * r02
      + (20*(k:ℝ)^5+110*(k:ℝ)^4+224*(k:ℝ)^3+208*(k:ℝ)^2+86*(k:ℝ)+12) * r03
      + (20*(k:ℝ)^5+90*(k:ℝ)^4+134*(k:ℝ)^3+74*(k:ℝ)^2+12*(k:ℝ)) * r10
      + (40*(k:ℝ)^5+220*(k:ℝ)^4+448*(k:ℝ)^3+416*(k:ℝ)^2+172*(k:ℝ)+24) * r11
      + (20*(k:ℝ)^5+110*(k:ℝ)^4+224*(k:ℝ)^3+208*(k:ℝ)^2+86*(k:ℝ)+12) * r12
      + (20*(k:ℝ)^5+110*(k:ℝ)^4+224*(k:ℝ)^3+208*(k:ℝ)^2+86*(k:ℝ)+12) * r13
      + (30*(k:ℝ)^4+110*(k:ℝ)^3+141*(k:ℝ)^2+75*(k:ℝ)+13) * s00
      + (50*(k:ℝ)^4+180*(k:ℝ)^3+220*(k:ℝ)^2+106*(k:ℝ)+16) * s01
      + (10*(k:ℝ)^4+35*(k:ℝ)^3+42*(k:ℝ)^2+20*(k:ℝ)+3) * s02
      + (10*(k:ℝ)^4+20*(k:ℝ)^3+2*(k:ℝ)^2-10*(k:ℝ)-4) * s10
      + (-10*(k:ℝ)^4-45*(k:ℝ)^3-67*(k:ℝ)^2-37*(k:ℝ)-6) * s20

end A103885Proof

namespace A103885Proof

/-! ### Transfer matrices -/

def Dred (m : ℕ) (x : ℝ) : ℝ := 5^m * (∏ k ∈ Finset.range (2*m), (2*x+1+k)) * P1 x
def Ered (m : ℕ) (x : ℝ) : ℝ := (-5)^m * (∏ j ∈ Finset.range (2*m), (2*x-2+j)) * P1 (x+m)

lemma Dred_succ (m : ℕ) (x : ℝ) :
    Dred (m+1) x = Dred m x * (5 * (2*x + 2*m + 1) * (2*x + 2*m + 2)) := by
  unfold Dred
  rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
  push_cast; ring

lemma Ered_succ (m : ℕ) (x : ℝ) :
    Ered (m+1) x * P1 (x+m) = Ered m x * ((-5) * (2*x + 2*m - 2) * (2*x + 2*m - 1) * P1 (x+m+1)) := by
  unfold Ered
  rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
  push_cast; ring

lemma Dred_one (x : ℝ) : Dred 1 x = 5 * (2*x+1) * (2*x+2) * P1 x := by
  unfold Dred; simp only [Finset.prod_range_succ, Finset.prod_range_zero]; push_cast; ring

lemma Ered_one (x : ℝ) : Ered 1 x = (-5) * (2*x-2) * (2*x-1) * P1 (x+1) := by
  unfold Ered; simp only [Finset.prod_range_succ, Finset.prod_range_zero]; push_cast; ring

lemma Dred_pos (m N : ℕ) : 0 < Dred m N := by
  unfold Dred
  apply mul_pos (mul_pos (by positivity) ?_) ?_
  · apply Finset.prod_pos; intro k _; positivity
  · rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp; exact P1_pos_of_nonpos le_rfl
    · exact P1_pos_of_one_le (by exact_mod_cast h)

/-- entries of R^{(m+1)} -/
def R11 (m : ℕ) (x : ℝ) : ℝ := Bf (m+2) (x-1)
def R12 (m : ℕ) (x : ℝ) : ℝ := 20*(x-1)*(x-1/2) * Bf (m+1) x
def R21 (m : ℕ) (x : ℝ) : ℝ := 20*(x+m+1/2)*(x+m+1) * Bf (m+1) (x-1)
def R22 (m : ℕ) (x : ℝ) : ℝ := 400*(x-1)*(x-1/2)*(x+m+1/2)*(x+m+1) * Bf m x
def M11 (y : ℝ) : ℝ := c0 y
def M12 (y : ℝ) : ℝ := 20*(y-1)*(y-1/2) * P1 (y+1)
def M21 (y : ℝ) : ℝ := 20*(y+1/2)*(y+1) * P1 y

lemma continuous_R11 (m : ℕ) : Continuous (R11 m) := by
  unfold R11; have := continuous_Bf (m+2); fun_prop
lemma continuous_R12 (m : ℕ) : Continuous (R12 m) := by
  unfold R12; have := continuous_Bf (m+1); fun_prop
lemma continuous_R21 (m : ℕ) : Continuous (R21 m) := by
  unfold R21; have := continuous_Bf (m+1); fun_prop
lemma continuous_R22 (m : ℕ) : Continuous (R22 m) := by
  unfold R22; have := continuous_Bf m; fun_prop

lemma R_zero (x : ℝ) : R11 0 x = M11 x ∧ R12 0 x = M12 x ∧ R21 0 x = M21 x ∧ R22 0 x = 0 := by
  simp only [R11, R12, R21, R22, M11, M12, M21, Nat.reduceAdd, zero_add, Bf_two, Bf_one, Bf_zero,
    Nat.cast_zero]
  rw [show x - 1 + 1 = x by ring]
  refine ⟨by ring, trivial, by ring, by ring⟩

/-- L-structure: P1(x+m+1) R^{(m+2)}(x) = M̃(x+m+1) R^{(m+1)}(x) -/
lemma Lstruct (m : ℕ) (x : ℝ) :
    P1 (x+m+1) * R11 (m+1) x = M11 (x+m+1) * R11 m x + M12 (x+m+1) * R21 m x ∧
    P1 (x+m+1) * R12 (m+1) x = M11 (x+m+1) * R12 m x + M12 (x+m+1) * R22 m x ∧
    P1 (x+m+1) * R21 (m+1) x = M21 (x+m+1) * R11 m x ∧
    P1 (x+m+1) * R22 (m+1) x = M21 (x+m+1) * R12 m x := by
  have L1 := Lrec (m+1) (x-1)
  have L0 := Lrec m x
  simp only [R11, R12, R21, R22, M11, M12, M21] at *
  push_cast at *
  rw [P1_neg_eq] at L1 L0
  ring_nf at L1 L0 ⊢
  refine ⟨?_, ?_, trivial, trivial⟩
  · linear_combination L1
  · linear_combination (20*(x-1)*(x-1/2)) * L0

end A103885Proof

namespace A103885Proof

/-- Transfer relation: Dred(m+1,N) (a(N+m+1), a(N+m)) = R^{(m+1)}(N) (a(N), a(N-1)). -/
def TRst (m : ℕ) : Prop := ∀ N : ℕ,
  Dred (m+1) N * aS (N+m+2) = R11 m N * aS (N+1) + R12 m N * aS N ∧
  Dred (m+1) N * aS (N+m+1) = R21 m N * aS (N+1) + R22 m N * aS N

theorem TR_all (m : ℕ) : TRst m := by
  induction m with
  | zero =>
    intro N
    have AR := a_rec N
    rw [P1_neg_eq] at AR
    obtain ⟨h1, h2, h3, h4⟩ := R_zero N
    rw [Dred_one, h1, h2, h3, h4]
    simp only [M11, M12, M21, Nat.cast_zero, add_zero, zero_add]
    constructor
    · linear_combination AR
    · ring
  | succ m ih =>
    intro N
    obtain ⟨T1, T2⟩ := ih N
    obtain ⟨L1, L2, L3, L4⟩ := Lstruct m N
    simp only [M11, M12, M21] at L1 L2 L3 L4
    have AR := a_rec (N+m+1)
    push_cast at AR
    rw [P1_neg_eq] at AR
    rw [show N + m + 1 + 2 = N + (m+1) + 2 by ring, show N + m + 1 + 1 = N + m + 2 by ring] at AR
    have hD := Dred_succ (m+1) N
    push_cast at hD
    have hp : 0 < P1 ((N:ℝ)+m+1) := P1_pos_of_one_le (by
      have : (0:ℝ) ≤ N := by positivity
      have : (0:ℝ) ≤ m := by positivity
      linarith)
    rw [show N + (m+1) + 1 = N + m + 2 by ring]
    constructor
    · apply mul_left_cancel₀ hp.ne'
      linear_combination (P1 ((N:ℝ)+m+1) * aS (N+(m+1)+2)) * hD + Dred (m+1) N * AR
        + c0 ((N:ℝ)+m+1) * T1 + (20*((N:ℝ)+m+1-1)*((N:ℝ)+m+1-1/2)*P1 ((N:ℝ)+m+1+1)) * T2
        - aS (N+1) * L1 - aS N * L2
    · apply mul_left_cancel₀ hp.ne'
      linear_combination (P1 ((N:ℝ)+m+1) * aS (N+m+2)) * hD
        + (20*((N:ℝ)+m+1+1/2)*((N:ℝ)+m+1+1)*P1 ((N:ℝ)+m+1)) * T1 - aS (N+1) * L3 - aS N * L4

end A103885Proof

namespace A103885Proof

/-- Composition: P1(x+m+1) R^{(m+m'+2)}(x) = R^{(m'+1)}(x+m+1) R^{(m+1)}(x). -/
def COMPst (m m' : ℕ) : Prop := ∀ x : ℝ,
  P1 (x+m+1) * R11 (m+m'+1) x = R11 m' (x+m+1) * R11 m x + R12 m' (x+m+1) * R21 m x ∧
  P1 (x+m+1) * R12 (m+m'+1) x = R11 m' (x+m+1) * R12 m x + R12 m' (x+m+1) * R22 m x ∧
  P1 (x+m+1) * R21 (m+m'+1) x = R21 m' (x+m+1) * R11 m x + R22 m' (x+m+1) * R21 m x ∧
  P1 (x+m+1) * R22 (m+m'+1) x = R21 m' (x+m+1) * R12 m x + R22 m' (x+m+1) * R22 m x

theorem COMP_all (m m' : ℕ) : COMPst m m' := by
  induction m' with
  | zero =>
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := R_zero (x+m+1)
    simp only [add_zero, h1, h2, h3, h4, zero_mul, add_zero]
    obtain ⟨L1, L2, L3, L4⟩ := Lstruct m x
    exact ⟨L1, L2, L3, L4⟩
  | succ m' ih =>
    have hc1 := continuous_P1
    have hR11 := continuous_R11 (m+(m'+1)+1); have hR12 := continuous_R12 (m+(m'+1)+1)
    have hR21 := continuous_R21 (m+(m'+1)+1); have hR22 := continuous_R22 (m+(m'+1)+1)
    have hR11' := continuous_R11 (m'+1); have hR12' := continuous_R12 (m'+1)
    have hR21' := continuous_R21 (m'+1); have hR22' := continuous_R22 (m'+1)
    have hR11m := continuous_R11 m; have hR12m := continuous_R12 m
    have hR21m := continuous_R21 m; have hR22m := continuous_R22 m
    have key : ∀ x : ℝ,
      P1 (x + ((m:ℝ)+m'+2)) * (P1 (x+m+1) * R11 (m+(m'+1)+1) x) = P1 (x + ((m:ℝ)+m'+2)) * (R11 (m'+1) (x+m+1) * R11 m x + R12 (m'+1) (x+m+1) * R21 m x) ∧
      P1 (x + ((m:ℝ)+m'+2)) * (P1 (x+m+1) * R12 (m+(m'+1)+1) x) = P1 (x + ((m:ℝ)+m'+2)) * (R11 (m'+1) (x+m+1) * R12 m x + R12 (m'+1) (x+m+1) * R22 m x) ∧
      P1 (x + ((m:ℝ)+m'+2)) * (P1 (x+m+1) * R21 (m+(m'+1)+1) x) = P1 (x + ((m:ℝ)+m'+2)) * (R21 (m'+1) (x+m+1) * R11 m x + R22 (m'+1) (x+m+1) * R21 m x) ∧
      P1 (x + ((m:ℝ)+m'+2)) * (P1 (x+m+1) * R22 (m+(m'+1)+1) x) = P1 (x + ((m:ℝ)+m'+2)) * (R21 (m'+1) (x+m+1) * R12 m x + R22 (m'+1) (x+m+1) * R22 m x) := by
      intro x
      obtain ⟨I11, I12, I21, I22⟩ := ih x
      obtain ⟨B11, B12, B21, B22⟩ := Lstruct (m+m'+1) x
      obtain ⟨S11, S12, S21, S22⟩ := Lstruct m' (x+m+1)
      simp only [M11, M12, M21] at B11 B12 B21 B22 S11 S12 S21 S22
      push_cast at B11 B12 B21 B22 S11 S12 S21 S22
      rw [show m + (m'+1) + 1 = m + m' + 1 + 1 by ring]
      have e1 : x + ((m:ℝ) + m' + 1) + 1 = x + ((m:ℝ)+m'+2) := by ring
      have e2 : x + (m:ℝ) + 1 + m' + 1 = x + ((m:ℝ)+m'+2) := by ring
      have e3 : x + ((m:ℝ) + m' + 1) + 1 + 1 = x + ((m:ℝ)+m'+2) + 1 := by ring
      have e4 : x + (m:ℝ) + 1 + m' + 1 + 1 = x + ((m:ℝ)+m'+2) + 1 := by ring
      rw [e3, e1] at B11 B12 B21 B22
      rw [e4, e2] at S11 S12 S21 S22
      refine ⟨?_, ?_, ?_, ?_⟩
      · linear_combination P1 (x+m+1) * B11 + c0 (x + ((m:ℝ)+m'+2)) * I11
          + (20 * (x + ((m:ℝ)+m'+2) - 1) * (x + ((m:ℝ)+m'+2) - 1/2) * P1 (x + ((m:ℝ)+m'+2) + 1)) * I21
          - R11 m x * S11 - R21 m x * S12
      · linear_combination P1 (x+m+1) * B12 + c0 (x + ((m:ℝ)+m'+2)) * I12
          + (20 * (x + ((m:ℝ)+m'+2) - 1) * (x + ((m:ℝ)+m'+2) - 1/2) * P1 (x + ((m:ℝ)+m'+2) + 1)) * I22
          - R12 m x * S11 - R22 m x * S12
      · linear_combination P1 (x+m+1) * B21
          + (20 * (x + ((m:ℝ)+m'+2) + 1/2) * (x + ((m:ℝ)+m'+2) + 1) * P1 (x + ((m:ℝ)+m'+2))) * I11
          - R11 m x * S21 - R21 m x * S22
      · linear_combination P1 (x+m+1) * B22
          + (20 * (x + ((m:ℝ)+m'+2) + 1/2) * (x + ((m:ℝ)+m'+2) + 1) * P1 (x + ((m:ℝ)+m'+2))) * I12
          - R12 m x * S21 - R22 m x * S22
    intro x
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact cancel_P1 ((m:ℝ)+m'+2) (by fun_prop) (by fun_prop) (fun y => (key y).1) x
    · exact cancel_P1 ((m:ℝ)+m'+2) (by fun_prop) (by fun_prop) (fun y => (key y).2.1) x
    · exact cancel_P1 ((m:ℝ)+m'+2) (by fun_prop) (by fun_prop) (fun y => (key y).2.2.1) x
    · exact cancel_P1 ((m:ℝ)+m'+2) (by fun_prop) (by fun_prop) (fun y => (key y).2.2.2) x

end A103885Proof

namespace A103885Proof

def DETst (m : ℕ) : Prop := ∀ x : ℝ,
  R11 m x * R22 m x - R12 m x * R21 m x = Dred (m+1) x * Ered (m+1) x

theorem DET_all (m : ℕ) : DETst m := by
  induction m with
  | zero =>
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := R_zero x
    rw [h1, h2, h3, h4, Dred_one, Ered_one]
    simp only [M11, M12, M21]; ring
  | succ m ih =>
    have hc1 := continuous_P1
    have hR11 := continuous_R11 (m+1); have hR12 := continuous_R12 (m+1)
    have hR21 := continuous_R21 (m+1); have hR22 := continuous_R22 (m+1)
    have hD : Continuous (fun x => Dred (m+1+1) x * Ered (m+1+1) x) := by
      unfold Dred Ered; fun_prop
    have key : ∀ x : ℝ, P1 (x + ((m:ℝ)+1)) * (P1 (x + ((m:ℝ)+1)) * (R11 (m+1) x * R22 (m+1) x - R12 (m+1) x * R21 (m+1) x))
        = P1 (x + ((m:ℝ)+1)) * (P1 (x + ((m:ℝ)+1)) * (Dred (m+1+1) x * Ered (m+1+1) x)) := by
      intro x
      obtain ⟨L1, L2, L3, L4⟩ := Lstruct m x
      simp only [M11, M12, M21] at L1 L2 L3 L4
      have I := ih x
      have hD := Dred_succ (m+1) x
      have hE := Ered_succ (m+1) x
      push_cast at hD hE
      have e1 : x + (m:ℝ) + 1 = x + ((m:ℝ)+1) := by ring
      have e2 : x + (m:ℝ) + 1 + 1 = x + ((m:ℝ)+1) + 1 := by ring
      rw [e2, e1] at L1 L2 L3 L4
      linear_combination (P1 (x + ((m:ℝ)+1)) * R22 (m+1) x) * L1
        + (c0 (x + ((m:ℝ)+1)) * R11 m x + 20 * (x + ((m:ℝ)+1) - 1) * (x + ((m:ℝ)+1) - 1/2) * P1 (x + ((m:ℝ)+1) + 1) * R21 m x) * L4
        - (P1 (x + ((m:ℝ)+1)) * R21 (m+1) x) * L2
        - (c0 (x + ((m:ℝ)+1)) * R12 m x + 20 * (x + ((m:ℝ)+1) - 1) * (x + ((m:ℝ)+1) - 1/2) * P1 (x + ((m:ℝ)+1) + 1) * R22 m x) * L3
        - (20 * (x + ((m:ℝ)+1) - 1) * (x + ((m:ℝ)+1) - 1/2) * P1 (x + ((m:ℝ)+1) + 1) * (20 * (x + ((m:ℝ)+1) + 1/2) * (x + ((m:ℝ)+1) + 1) * P1 (x + ((m:ℝ)+1)))) * I
        - (P1 (x + ((m:ℝ)+1)) * (P1 (x + ((m:ℝ)+1)) * Ered (m+1+1) x)) * hD
        - (P1 (x + ((m:ℝ)+1)) * Dred (m+1) x * (5*(2*x+2*((m:ℝ)+1)+1)*(2*x+2*((m:ℝ)+1)+2))) * hE
    have step1 := cancel_P1 ((m:ℝ)+1) (by fun_prop) (by fun_prop) key
    exact cancel_P1 ((m:ℝ)+1) (by fun_prop) (by fun_prop) step1

end A103885Proof

namespace A103885Proof

theorem KEY (m : ℕ) (x : ℝ) :
    Bf (m+1) x * Bf (2*m+3) (x-1) - Bf (2*m+2) x * Bf (m+2) (x-1)
      = -(-25)^(m+1) * (∏ k ∈ Finset.range (2*m+2), (2*x+1+k)) * (∏ j ∈ Finset.range (2*m+2), (2*x+j))
        * P1 x * Bf (m+1) (x+m+1) := by
  have hcont1 : Continuous (fun x : ℝ => Bf (m+1) x * Bf (2*m+3) (x-1) - Bf (2*m+2) x * Bf (m+2) (x-1)) := by
    have := continuous_Bf (m+1); have := continuous_Bf (2*m+3); have := continuous_Bf (2*m+2)
    have := continuous_Bf (m+2); fun_prop
  have hcont2 : Continuous (fun x : ℝ => -(-25:ℝ)^(m+1) * (∏ k ∈ Finset.range (2*m+2), (2*x+1+k))
      * (∏ j ∈ Finset.range (2*m+2), (2*x+j)) * P1 x * Bf (m+1) (x+m+1)) := by
    have := continuous_Bf (m+1); have := continuous_P1
    apply Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul continuous_const ?_) ?_) ?_) ?_
    · exact continuous_finset_prod _ (fun k _ => by fun_prop)
    · exact continuous_finset_prod _ (fun k _ => by fun_prop)
    · fun_prop
    · fun_prop
  have key : ∀ x : ℝ, (20*(x-1)*(x-1/2) * P1 (x+m+1)) * (Bf (m+1) x * Bf (2*m+3) (x-1) - Bf (2*m+2) x * Bf (m+2) (x-1))
      = (20*(x-1)*(x-1/2) * P1 (x+m+1)) * (-(-25)^(m+1) * (∏ k ∈ Finset.range (2*m+2), (2*x+1+k)) * (∏ j ∈ Finset.range (2*m+2), (2*x+j))
        * P1 x * Bf (m+1) (x+m+1)) := by
    intro x
    obtain ⟨C11, C12, _, _⟩ := COMP_all m m x
    have D := DET_all m x
    have hpow : (5:ℝ)^(m+1) * (-5)^(m+1) = (-25)^(m+1) := by rw [← mul_pow]; norm_num
    have hE : Ered (m+1) x = (-5)^(m+1) * ((2*x-2)*(2*x-1) * ∏ j ∈ Finset.range (2*m), (2*x+j)) * P1 (x+m+1) := by
      unfold Ered
      rw [show 2*(m+1) = 2*m+1+1 by ring, Finset.prod_range_succ', Finset.prod_range_succ']
      rw [Finset.prod_congr rfl (fun j _ => by push_cast; ring : ∀ j ∈ Finset.range (2*m), (2*x-2+((j+1+1 : ℕ):ℝ)) = 2*x+j)]
      push_cast; ring
    have hPP : ∏ j ∈ Finset.range (2*m+2), (2*x+j) = (∏ j ∈ Finset.range (2*m), (2*x+j)) * (2*x+2*m) * (2*x+2*m+1) := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]; push_cast; ring
    rw [hE] at D
    unfold Dred at D
    rw [hPP, ← hpow]
    simp only [R11, R12, R21, R22] at C11 C12 D
    rw [show m + m + 1 + 2 = 2*m+3 by ring] at C11
    rw [show m + m + 1 + 1 = 2*m+2 by ring] at C12
    rw [show 2*(m+1) = 2*m+2 by ring] at D
    linear_combination (20*(x-1)*(x-1/2) * Bf (m+1) x) * C11 - Bf (m+2) (x-1) * C12
      - (20*(x+m)*(x+m+1/2) * Bf (m+1) (x+m+1)) * D
  apply eq_of_eq_off_finite hcont1 hcont2 {1, 1/2, rho1 - ((m:ℝ)+1), rho2 - ((m:ℝ)+1)} (Set.toFinite _)
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy
  obtain ⟨h1, h2, h3, h4⟩ := hy
  have hne : 20*(y-1)*(y-1/2) * P1 (y+m+1) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr h1)) (sub_ne_zero.mpr h2))
    apply P1_ne_zero_of_ne
    · intro h; exact h3 (by linarith)
    · intro h; exact h4 (by linarith)
  exact mul_left_cancel₀ hne (key y)

end A103885Proof

namespace A103885Proof

/-! ### The polynomials P and Q -/

def Ppoly (m : ℕ) : ℝ[X] := C ((5:ℝ)^(m+1)) * Gp (m+1) (m+1)
def Epoly (m : ℕ) : ℝ[X] := Gp (m+1) (2*m+2)
def Qpoly (m : ℕ) : ℝ[X] := contract 2 (Epoly m)

lemma eval_Ppoly (m : ℕ) (x : ℝ) : (Ppoly m).eval x = 5^(m+1) * Bf (m+1) ((m+1)*x - (m+1)) := by
  simp only [Ppoly, eval_mul, eval_C, eval_Gp]; push_cast; ring_nf

lemma eval_Epoly (m : ℕ) (x : ℝ) : (Epoly m).eval x = Bf (2*m+2) ((m+1)*x - (m+1)) := by
  simp only [Epoly, eval_Gp]; push_cast; ring_nf

lemma Epoly_even (m : ℕ) (x : ℝ) : (Epoly m).eval (-x) = (Epoly m).eval x := by
  rw [eval_Epoly, eval_Epoly]
  have := Bf_sym (2*m+2) (((m:ℝ)+1)*x - ((m:ℝ)+1))
  push_cast at this
  rw [← this]; congr 1; ring

lemma expand_Qpoly (m : ℕ) : expand ℝ 2 (Qpoly m) = Epoly m :=
  even_expand_contract _ (Epoly_even m)

lemma eval_Qpoly_sq (m : ℕ) (x : ℝ) : (Qpoly m).eval (x^2) = (Epoly m).eval x := by
  rw [← expand_Qpoly, expand_eval]

lemma Ppoly_ne_zero (m : ℕ) : Ppoly m ≠ 0 := by
  unfold Ppoly
  exact mul_ne_zero (by simp) (Gp_ne_zero _ _ (by omega))

lemma Ppoly_degree (m : ℕ) : (Ppoly m).degree = (2*(m+1) : ℕ) := by
  rw [degree_eq_natDegree (Ppoly_ne_zero m), Ppoly, natDegree_C_mul (by positivity),
    Gp_natDegree (m+1) (m+1) (by omega) (by omega)]

lemma Epoly_natDegree (m : ℕ) : (Epoly m).natDegree = 2*(2*m+2) :=
  Gp_natDegree (m+1) (2*m+2) (by omega) (by omega)

lemma Qpoly_ne_zero (m : ℕ) : Qpoly m ≠ 0 := by
  intro h
  have := expand_Qpoly m
  rw [h, map_zero] at this
  exact Gp_ne_zero (m+1) (2*m+2) (by omega) this.symm

lemma Qpoly_degree (m : ℕ) : (Qpoly m).degree = (2*(m+1) : ℕ) := by
  rw [degree_eq_natDegree (Qpoly_ne_zero m)]
  have h := natDegree_expand 2 (Qpoly m)
  rw [expand_Qpoly, Epoly_natDegree] at h
  congr 1; omega

lemma Ppoly_symm (m : ℕ) (x : ℝ) : (Ppoly m).eval x = (Ppoly m).eval (1 - x) := by
  rw [eval_Ppoly, eval_Ppoly]
  have := Bf_sym (m+1) (((m:ℝ)+1)*x - ((m:ℝ)+1))
  push_cast at this
  rw [← this]; congr 2; ring

lemma Ppoly_complex_roots (m : ℕ) (z : ℂ) (hz : ((Ppoly m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (0:ℝ) 1 := by
  unfold Ppoly at hz
  rw [Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C] at hz
  have h5 : (algebraMap ℝ ℂ) ((5:ℝ)^(m+1)) ≠ 0 := by simp
  have hz' := (mul_eq_zero.mp hz).resolve_left h5
  obtain ⟨h1, h2, h3⟩ := Gp_complex_roots (m+1) (m+1) (by omega) (by omega) z hz'
  refine ⟨h1, ?_, h3.le⟩
  have hm : ((m+1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [div_self hm] at h2
  linarith

lemma Qpoly_complex_roots (m : ℕ) (z : ℂ) (hz : ((Qpoly m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1:ℝ) 1 := by
  have hE : ((Epoly m).map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [← expand_Qpoly, map_expand, expand_eval]; exact hz
  obtain ⟨h1, h2, h3⟩ := Gp_complex_roots (m+1) (2*m+2) (by omega) (by omega) z hE
  refine ⟨h1, ?_, h3.le⟩
  have hm : ((m+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have : ((2*m+2 : ℕ) : ℝ) / ((m+1 : ℕ) : ℝ) = 2 := by
    rw [div_eq_iff hm]; push_cast; ring
  rw [this] at h2
  linarith

/-! ### Products over Ioc -/

lemma prod_Ioc_eq_range (f : ℕ → ℝ) (n : ℕ) :
    ∏ k ∈ Finset.Ioc 0 n, f k = ∏ k ∈ Finset.range n, f (k+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Ioc_succ_top (by omega), ih, Finset.prod_range_succ]

lemma Dred_double (m : ℕ) (x : ℝ) :
    Dred (2*m+2) x = Dred (m+1) x * (5^(m+1) * ∏ k ∈ Finset.range (2*m+2), (2*x + (2*m+3) + k)) := by
  unfold Dred
  rw [show 2*(2*m+2) = 2*(m+1) + (2*m+2) by ring, Finset.prod_range_add,
    show 2*(m+1) = 2*m+2 by ring, pow_add]
  have : ∀ k ∈ Finset.range (2*m+2), (2*x+1+((2*m+2+k : ℕ) : ℝ)) = 2*x + (2*m+3) + k := by
    intro k _; push_cast; ring
  rw [Finset.prod_congr rfl this]
  ring

lemma aS_succ' (k : ℕ) : aS (k+1) = (A103885 k : ℝ) := rfl

/-- The main recurrence, for m+1 and n'+1. -/
theorem main_rec (m n' : ℕ) :
    (prod_factor_plus (m+1) (n'+1) * (Ppoly m).eval ((n'+1 : ℕ) : ℝ)) * A103885_subsequence_real (m+1) (n'+1+1)
      + ((-1 : ℝ)^(m+1) * prod_factor_minus (m+1) (n'+1) * (Ppoly m).eval (-((n'+1 : ℕ) : ℝ))) * A103885_subsequence_real (m+1) (n'+1-1)
      = (Qpoly m).eval (((n'+1 : ℕ) : ℝ)^2) * A103885_subsequence_real (m+1) (n'+1) := by
  -- set N₀
  set N₀ : ℕ := (m+1)*n' with hN₀
  obtain ⟨T1, _⟩ := TR_all m N₀
  obtain ⟨T2, _⟩ := TR_all (2*m+1) N₀
  have K := KEY m N₀
  simp only [R11, R12] at T1 T2
  rw [show N₀ + (2*m+1) + 2 = N₀ + 2*m + 3 by ring, show 2*m+1+2 = 2*m+3 by ring,
    show 2*m+1+1 = 2*m+2 by ring] at T2
  rw [Dred_double] at T2
  have hD := Dred_pos (m+1) N₀
  -- identify the sequence values
  have b1 : A103885_subsequence_real (m+1) (n'+1+1) = aS (N₀ + 2*m + 3) := by
    show (A103885 ((m+1)*(n'+1+1)) : ℝ) = (A103885 (N₀ + 2*m + 2) : ℝ)
    congr 2; rw [hN₀]; ring
  have b0 : A103885_subsequence_real (m+1) (n'+1) = aS (N₀ + m + 2) := by
    show (A103885 ((m+1)*(n'+1)) : ℝ) = (A103885 (N₀ + m + 1) : ℝ)
    congr 2
  have bm : A103885_subsequence_real (m+1) (n'+1-1) = aS (N₀ + 1) := by
    show (A103885 ((m+1)*(n'+1-1)) : ℝ) = (A103885 N₀ : ℝ)
    congr 2
  rw [b1, b0, bm]
  -- identify the polynomial values
  have hN : (N₀ : ℝ) = ((m:ℝ)+1) * ((n'+1 : ℕ) : ℝ) - ((m:ℝ)+1) := by rw [hN₀]; push_cast; ring
  have hP : (Ppoly m).eval ((n'+1 : ℕ) : ℝ) = 5^(m+1) * Bf (m+1) N₀ := by
    rw [eval_Ppoly, hN]
  have hPm : (Ppoly m).eval (-((n'+1 : ℕ) : ℝ)) = 5^(m+1) * Bf (m+1) ((N₀:ℝ) + m + 1) := by
    rw [eval_Ppoly]
    have := Bf_sym (m+1) ((N₀:ℝ) + m + 1)
    push_cast at this
    rw [← this]; congr 2; rw [hN]; ring
  have hQ : (Qpoly m).eval (((n'+1 : ℕ) : ℝ)^2) = Bf (2*m+2) N₀ := by
    rw [eval_Qpoly_sq, eval_Epoly, hN]
  -- identify the products
  have hplus : prod_factor_plus (m+1) (n'+1) = ∏ k ∈ Finset.range (2*m+2), (2*(N₀:ℝ) + (2*m+3) + k) := by
    unfold prod_factor_plus product_indices
    rw [show 2*(m+1) = 2*m+2 by ring, prod_Ioc_eq_range]
    apply Finset.prod_congr rfl
    intro k _; rw [hN₀]; push_cast; ring
  have hminus : prod_factor_minus (m+1) (n'+1) = ∏ j ∈ Finset.range (2*m+2), (2*(N₀:ℝ) + j) := by
    unfold prod_factor_minus product_indices
    rw [show 2*(m+1) = 2*m+2 by ring, prod_Ioc_eq_range,
      ← Finset.prod_range_reflect (fun j : ℕ => (2*(N₀:ℝ) + j)) (2*m+2)]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have e : ((2*m+2-1-j : ℕ) : ℝ) = 2*m+1 - j := by
      rw [Nat.cast_sub (by omega : j ≤ 2*m+2-1), Nat.cast_sub (by omega : 1 ≤ 2*m+2)]; push_cast; ring
    rw [e, hN₀]; push_cast; ring
  rw [hP, hPm, hQ, hplus, hminus]
  have hpow : (-1:ℝ)^(m+1) * 5^(m+1) = (-5)^(m+1) := by rw [← mul_pow]; norm_num
  have hpow2 : (5:ℝ)^(m+1) * (-5)^(m+1) = (-25)^(m+1) := by rw [← mul_pow]; norm_num
  -- the elimination
  have elim : Bf (m+1) N₀ * (Dred (m+1) N₀ * (5^(m+1) * ∏ k ∈ Finset.range (2*m+2), (2*(N₀:ℝ) + (2*m+3) + k))) * aS (N₀+2*m+3)
      - Bf (2*m+2) N₀ * (Dred (m+1) N₀ * aS (N₀+m+2))
      = (-(-25)^(m+1) * (∏ k ∈ Finset.range (2*m+2), (2*(N₀:ℝ)+1+k)) * (∏ j ∈ Finset.range (2*m+2), (2*(N₀:ℝ)+j))
        * P1 N₀ * Bf (m+1) ((N₀:ℝ)+m+1)) * aS (N₀+1) := by
    rw [← K]
    linear_combination Bf (m+1) N₀ * T2 - Bf (2*m+2) N₀ * T1
  apply mul_left_cancel₀ hD.ne'
  have hDred : Dred (m+1) N₀ = 5^(m+1) * (∏ k ∈ Finset.range (2*m+2), (2*(N₀:ℝ)+1+k)) * P1 N₀ := by
    unfold Dred; rw [show 2*(m+1) = 2*m+2 by ring]
  rw [hDred] at elim ⊢
  linear_combination elim + ((∏ j ∈ Finset.range (2*m+2), (2*(N₀:ℝ)+j)) * Bf (m+1) ((N₀:ℝ)+m+1) * aS (N₀+1) * (∏ k ∈ Finset.range (2*m+2), (2*(N₀:ℝ)+1+k)) * P1 N₀) * (5^(m+1) * hpow + hpow2)

end A103885Proof

end

/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  refine ⟨A103885Proof.Ppoly m, A103885Proof.Qpoly m, A103885Proof.Ppoly_degree m,
    A103885Proof.Qpoly_degree m, ?_, A103885Proof.Ppoly_symm m, A103885Proof.Ppoly_complex_roots m,
    A103885Proof.Qpoly_complex_roots m⟩
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n'+1 := ⟨n-1, by omega⟩
  exact A103885Proof.main_rec m n'


theorem oeis_a103885_conjecture_0.disproof : ¬ (type_of% @oeis_a103885_conjecture_0) := sorry
