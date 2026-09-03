import FormalConjecturesUtil

/-! Finite Bonferroni and upper-sieve inequalities. Arithmetic distribution
errors must be bounded separately when this tool is applied. -/

namespace Erdos371FiniteBrun

open Finset

variable {ι : Type*} [DecidableEq ι]

noncomputable def elem (s : Finset ι) (w : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard k, ∏ p ∈ t, w p

@[simp] lemma elem_zero (s : Finset ι) (w : ι → ℝ) : elem s w 0 = 1 := by
  simp [elem]

@[simp] lemma elem_empty (w : ι → ℝ) (k : ℕ) :
    elem ∅ w k = if k=0 then 1 else 0 := by
  cases k with
  | zero => simp [elem]
  | succ k =>
    rw [elem, Finset.powersetCard_eq_empty.mpr (by simp)]
    simp

lemma elem_nonneg {s : Finset ι} {w : ι → ℝ} (hw : ∀ p ∈ s, 0 ≤ w p) (k : ℕ) :
    0 ≤ elem s w k := by
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.prod_nonneg
  intro p hp
  exact hw p ((Finset.mem_powersetCard.mp ht).1 hp)

lemma elem_insert_succ {x : ι} {s : Finset ι} (hx : x ∉ s) (w : ι → ℝ) (k : ℕ) :
    elem (insert x s) w (k+1) = elem s w (k+1) + w x * elem s w k := by
  unfold elem
  rw [Finset.powersetCard_succ_insert hx, Finset.sum_union]
  · rw [Finset.sum_image, Finset.mul_sum]
    · congr 1
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.prod_insert (fun h => hx ((Finset.mem_powersetCard.mp ht).1 h))
    · intro a ha b hb hab
      have hxa : x ∉ a := fun h => hx ((Finset.mem_powersetCard.mp ha).1 h)
      have hxb : x ∉ b := fun h => hx ((Finset.mem_powersetCard.mp hb).1 h)
      have hh := congrArg (fun t : Finset ι => t.erase x) hab
      simpa [Finset.erase_insert hxa, Finset.erase_insert hxb] using hh
  · apply Finset.disjoint_left.mpr
    intro t ht hi
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    exact hx ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self _ _))

noncomputable def truncSum (s : Finset ι) (w : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (-1:ℝ)^j * elem s w j

@[simp] lemma partial_zero (s : Finset ι) (w : ι → ℝ) : truncSum s w 0 = 1 := by
  simp [truncSum]

@[simp] lemma partial_empty (w : ι → ℝ) (k : ℕ) : truncSum ∅ w k = 1 := by
  simp [truncSum]

lemma partial_succ (s : Finset ι) (w : ι → ℝ) (k : ℕ) :
    truncSum s w (k+1) = truncSum s w k + (-1:ℝ)^(k+1)*elem s w (k+1) := by
  exact Finset.sum_range_succ _ _

lemma partial_insert_succ {x : ι} {s : Finset ι} (hx : x ∉ s) (w : ι → ℝ) (k : ℕ) :
    truncSum (insert x s) w (k+1) = truncSum s w (k+1) - w x * truncSum s w k := by
  induction k with
  | zero => simp [partial_succ, elem_insert_succ hx]; ring
  | succ k ih =>
    rw [partial_succ, ih, elem_insert_succ hx, partial_succ s w (k+1), partial_succ s w k]
    simp only [pow_succ]
    ring

noncomputable def signedError (s : Finset ι) (w : ι → ℝ) (k : ℕ) : ℝ :=
  (-1:ℝ)^k * (truncSum s w k - ∏ p ∈ s, (1-w p))

@[simp] lemma signedError_zero (s : Finset ι) (w : ι → ℝ) :
    signedError s w 0 = 1 - ∏ p ∈ s, (1-w p) := by simp [signedError]

@[simp] lemma signedError_empty (w : ι → ℝ) (k : ℕ) : signedError ∅ w k = 0 := by
  simp [signedError]

lemma signedError_insert_succ {x : ι} {s : Finset ι} (hx : x ∉ s) (w : ι → ℝ) (k : ℕ) :
    signedError (insert x s) w (k+1) =
      signedError s w (k+1) + w x * signedError s w k := by
  simp only [signedError, partial_insert_succ hx, Finset.prod_insert hx, pow_succ]
  ring

/-- Bonferroni's alternating errors are nonnegative and at most the first
omitted elementary symmetric term. -/
theorem signedError_bounds {s : Finset ι} {w : ι → ℝ}
    (hw : ∀ p ∈ s, 0 ≤ w p ∧ w p ≤ 1) (k : ℕ) :
    0 ≤ signedError s w k ∧ signedError s w k ≤ elem s w (k+1) := by
  induction s using Finset.induction_on generalizing k with
  | empty => simp
  | @insert x s hx ih =>
    have hxw := hw x (Finset.mem_insert_self _ _)
    have hsw : ∀ p ∈ s, 0 ≤ w p ∧ w p ≤ 1 := fun p hp => hw p (Finset.mem_insert_of_mem hp)
    cases k with
    | zero =>
      have hb := ih hsw 0
      have hp0 : 0 ≤ ∏ p ∈ s, (1-w p) := Finset.prod_nonneg (fun p hp => by have := hsw p hp; linarith)
      have hp1 : (∏ p ∈ s, (1-w p)) ≤ 1 :=
        Finset.prod_le_one (fun p hp => by have := hsw p hp; linarith)
          (fun p hp => by have := hsw p hp; linarith)
      simp only [signedError_zero, elem_insert_succ hx, elem_zero] at hb ⊢
      rw [Finset.prod_insert hx]
      have hm0 := mul_nonneg hxw.1 hp0
      have hm1 := mul_le_mul_of_nonneg_left hp1 hxw.1
      constructor <;> nlinarith
    | succ k =>
      rw [signedError_insert_succ hx]
      have h1 := ih hsw (k+1)
      have h2 := ih hsw k
      rw [elem_insert_succ hx]
      exact ⟨add_nonneg h1.1 (mul_nonneg hxw.1 h2.1),
        add_le_add h1.2 (mul_le_mul_of_nonneg_left h2.2 hxw.1)⟩

lemma signedError_add_previous (s : Finset ι) (w : ι → ℝ) (k : ℕ) :
    signedError s w (k+1) + signedError s w k = elem s w (k+1) := by
  simp only [signedError, partial_succ, pow_succ]
  have hpow : (-1:ℝ)^k * (-1:ℝ)^k = 1 := by rw [← pow_two, ← pow_mul, mul_comm k 2, pow_mul]; norm_num
  calc
    _ = ((-1:ℝ)^k * (-1:ℝ)^k) * elem s w (k+1) := by ring
    _ = _ := by rw [hpow, one_mul]

/-- An even truncation bounds the Euler product from above, with error at
most its last included elementary symmetric term. -/
theorem even_truncation_bounds {s : Finset ι} {w : ι → ℝ}
    (hw : ∀ p ∈ s, 0 ≤ w p ∧ w p ≤ 1) {r : ℕ} (hr : 0 < r) :
    (∏ p ∈ s, (1-w p)) ≤ truncSum s w (2*r) ∧
      truncSum s w (2*r) ≤ (∏ p ∈ s, (1-w p)) + elem s w (2*r) := by
  have h0 := (signedError_bounds hw (2*r)).1
  have h1 := (signedError_bounds hw (2*r-1)).1
  have he := signedError_add_previous s w (2*r-1)
  have hidx : 2*r-1+1 = 2*r := by omega
  rw [hidx] at he
  have heven : signedError s w (2*r) = truncSum s w (2*r) - ∏ p ∈ s, (1-w p) := by
    simp [signedError, pow_mul]
  rw [heven] at h0 he
  constructor <;> linarith

lemma first_order_binomial {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    x^(k+1) + (k+1:ℕ)*y*x^k ≤ (x+y)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := mul_le_mul_of_nonneg_right ih (add_nonneg hx hy)
    have he : (0:ℝ) ≤ (k+1:ℕ) * y^2 * x^k := by positivity
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at ih hh he ⊢
    nlinarith

/-- The elementary symmetric sum is bounded by the corresponding power
of the first moment, divided by the factorial. -/
theorem factorial_mul_elem_le {s : Finset ι} {w : ι → ℝ}
    (hw : ∀ p ∈ s, 0 ≤ w p) (k : ℕ) :
    (k.factorial:ℝ) * elem s w k ≤ (∑ p ∈ s, w p)^k := by
  induction s using Finset.induction_on generalizing k with
  | empty => cases k <;> simp
  | @insert x s hx ih =>
    have hxw := hw x (Finset.mem_insert_self _ _)
    have hsw : ∀ p ∈ s, 0 ≤ w p := fun p hp => hw p (Finset.mem_insert_of_mem hp)
    cases k with
    | zero => simp
    | succ k =>
      have h1 := ih hsw (k+1)
      have h2 := ih hsw k
      have hm := mul_le_mul_of_nonneg_left h2
        (show (0:ℝ) ≤ (k+1:ℕ)*w x by positivity)
      have hb := first_order_binomial (Finset.sum_nonneg hsw) hxw k
      rw [elem_insert_succ hx, Finset.sum_insert hx]
      rw [Nat.factorial_succ] at h1 ⊢
      push_cast at h1 hm hb ⊢
      rw [add_comm (w x)]
      nlinarith


attribute [local instance] Classical.propDecidable

variable {α : Type*} [DecidableEq α]

noncomputable def hit (b : ι → α → Prop) (n : α) (p : ι) : ℝ := if b p n then 1 else 0

noncomputable def survivors (A : Finset α) (s : Finset ι) (b : ι → α → Prop) : Finset α :=
  A.filter fun n => ∀ p ∈ s, ¬b p n

noncomputable def jointCount (A : Finset α) (b : ι → α → Prop) (t : Finset ι) : ℝ :=
  ((A.filter fun n => ∀ p ∈ t, b p n).card : ℝ)

noncomputable def brunSum (s : Finset ι) (count : Finset ι → ℝ) (R : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (R+1), (-1:ℝ)^j * ∑ t ∈ s.powersetCard j, count t

lemma prod_miss_eq (s : Finset ι) (b : ι → α → Prop) (n : α) :
    (∏ p ∈ s, (1-hit b n p)) = if ∀ p ∈ s, ¬b p n then 1 else 0 := by
  have he (p : ι) : 1-hit b n p = if ¬b p n then (1:ℝ) else 0 := by
    unfold hit
    split_ifs <;> simp_all
  simp only [he, Finset.prod_boole]

lemma sum_hit_prod (A : Finset α) (b : ι → α → Prop) (t : Finset ι) :
    (∑ n ∈ A, ∏ p ∈ t, hit b n p) = jointCount A b t := by
  simp [hit, Finset.prod_boole, jointCount]

lemma sum_trunc_eq_brun (A : Finset α) (s : Finset ι) (b : ι → α → Prop) (R : ℕ) :
    (∑ n ∈ A, truncSum s (hit b n) R) = brunSum s (jointCount A b) R := by
  unfold truncSum brunSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  congr 1
  unfold elem
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun t _ => sum_hit_prod A b t)

/-- The exact finite Bonferroni upper bound, before any arithmetic estimate. -/
theorem survivors_le_brun (A : Finset α) (s : Finset ι) (b : ι → α → Prop)
    {r : ℕ} (hr : 0 < r) : (survivors A s b).card ≤ brunSum s (jointCount A b) (2*r) := by
  have hb (n : α) := (even_truncation_bounds
    (s := s) (w := hit b n) (fun p _ => by unfold hit; split_ifs <;> norm_num) hr).1
  have hh := Finset.sum_le_sum (fun n (_ : n ∈ A) => hb n)
  rw [sum_trunc_eq_brun] at hh
  simpa [prod_miss_eq, survivors] using hh

lemma brunSum_le_main_add_errors (s : Finset ι) (count E : Finset ι → ℝ)
    (ν : ι → ℝ) (X : ℝ) (R : ℕ)
    (hE : ∀ t ⊆ s, t.card ≤ R → |count t - X*(∏ p ∈ t, ν p)| ≤ E t) :
    brunSum s count R ≤ X * truncSum s ν R +
      ∑ j ∈ Finset.range (R+1), ∑ t ∈ s.powersetCard j, E t := by
  have ht (j : ℕ) (hj : j ∈ Finset.range (R+1)) (t : Finset ι)
      (ht : t ∈ s.powersetCard j) :
      (-1:ℝ)^j * count t ≤ X*((-1:ℝ)^j * ∏ p ∈ t, ν p) + E t := by
    have he := hE t (Finset.mem_powersetCard.mp ht).1 (by
      have := (Finset.mem_powersetCard.mp ht).2
      have := Finset.mem_range.mp hj
      omega)
    have hh : (-1:ℝ)^j * (count t - X*(∏ p ∈ t, ν p)) ≤ E t := by
      calc
        _ ≤ |(-1:ℝ)^j * (count t - X*(∏ p ∈ t, ν p))| := le_abs_self _
        _ = |count t - X*(∏ p ∈ t, ν p)| := by simp [abs_mul, abs_pow]
        _ ≤ _ := he
    nlinarith
  calc
    _ = ∑ j ∈ Finset.range (R+1), ∑ t ∈ s.powersetCard j, (-1:ℝ)^j * count t := by
      simp [brunSum, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (R+1), ∑ t ∈ s.powersetCard j,
        (X*((-1:ℝ)^j * ∏ p ∈ t, ν p) + E t) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun t ht' => ht j hj t ht'))
    _ = _ := by simp [truncSum, elem, Finset.sum_add_distrib, Finset.mul_sum]

/-- A finite upper-bound sieve with explicit truncation and distribution
errors. Its error hypotheses are not assertions of arithmetic cancellation. -/
theorem finite_brun_upper (A : Finset α) (s : Finset ι) (b : ι → α → Prop)
    (ν : ι → ℝ) (X : ℝ) (E : Finset ι → ℝ)
    (hν : ∀ p ∈ s, 0 ≤ ν p ∧ ν p ≤ 1) (hX : 0 ≤ X)
    {r : ℕ} (hr : 0 < r)
    (hE : ∀ t ⊆ s, t.card ≤ 2*r → |jointCount A b t - X*(∏ p ∈ t, ν p)| ≤ E t) :
    (survivors A s b).card ≤
      X * ((∏ p ∈ s, (1-ν p)) + (∑ p ∈ s, ν p)^(2*r) / ((2*r).factorial:ℝ)) +
        ∑ j ∈ Finset.range (2*r+1), ∑ t ∈ s.powersetCard j, E t := by
  have hf := factorial_mul_elem_le (fun p hp => (hν p hp).1) (2*r)
  have hfac : (0:ℝ) < (2*r).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have he : elem s ν (2*r) ≤ (∑ p ∈ s, ν p)^(2*r)/((2*r).factorial:ℝ) := by
    apply (le_div_iff₀ hfac).mpr
    simpa [mul_comm] using hf
  have hb := (even_truncation_bounds hν hr).2
  calc
    _ ≤ brunSum s (jointCount A b) (2*r) := survivors_le_brun A s b hr
    _ ≤ _ := (brunSum_le_main_add_errors s (jointCount A b) E ν X (2*r) hE).trans (by
      have hh := mul_le_mul_of_nonneg_left (hb.trans (add_le_add_right he _)) hX
      linarith)


lemma pow_le_double_factorial (r : ℕ) : r^r ≤ (2*r).factorial := by
  have hfac : 1 ≤ r.factorial := Nat.factorial_pos r
  have hh : r^r ≤ (r+1).ascFactorial r := by
    rw [Nat.ascFactorial_eq_prod_range]
    calc
      _ = ∏ _i ∈ Finset.range r, r := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => by omega)
  calc
    _ ≤ (r+1).ascFactorial r := hh
    _ ≤ r.factorial * (r+1).ascFactorial r := by nlinarith
    _ = _ := by rw [Nat.factorial_mul_ascFactorial]; congr 1; omega

lemma factorial_tail_bound {M : ℝ} (hM : 0 ≤ M) {r : ℕ} (hr : 0 < r)
    (hlarge : 4*M^2 ≤ (r:ℝ)) :
    M^(2*r)/((2*r).factorial:ℝ) ≤ (1/4:ℝ)^r := by
  have hr' : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hfac : (r:ℝ)^r ≤ (2*r).factorial := by exact_mod_cast pow_le_double_factorial r
  have hratio : M^2/(r:ℝ) ≤ (1/4:ℝ) := by
    apply (div_le_iff₀ hr').mpr
    linarith
  calc
    _ ≤ M^(2*r)/(r:ℝ)^r :=
      div_le_div_of_nonneg_left (pow_nonneg hM _) (pow_pos hr' _) hfac
    _ = (M^2/(r:ℝ))^r := by rw [div_pow, ← pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hratio r

lemma two_root_error_bound (s : Finset ι) (R : ℕ) :
    (∑ j ∈ Finset.range (R+1), ∑ t ∈ s.powersetCard j, (2:ℝ)^t.card) ≤
      (R+1:ℕ) * (2*(max 1 s.card):ℝ)^R := by
  let B : ℝ := 2*(max 1 s.card:ℕ)
  have hB : 1 ≤ B := by
    have hm : 1 ≤ max 1 s.card := le_max_left _ _
    dsimp [B]
    have hm' : (1:ℝ) ≤ (max 1 s.card:ℕ) := by exact_mod_cast hm
    linarith
  calc
    _ = ∑ j ∈ Finset.range (R+1), (s.card.choose j:ℝ)*(2:ℝ)^j := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ _t ∈ s.powersetCard j, (2:ℝ)^j :=
          Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_powersetCard.mp ht).2])
        _ = _ := by simp
    _ ≤ ∑ j ∈ Finset.range (R+1), B^j := by
      apply Finset.sum_le_sum
      intro j _
      have hc : (s.card.choose j:ℝ) ≤ (s.card:ℝ)^j := by exact_mod_cast Nat.choose_le_pow s.card j
      have hcb : 2*(s.card:ℝ) ≤ B := by
        dsimp [B]
        exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (le_max_right _ _)) (by norm_num)
      calc
        _ ≤ (s.card:ℝ)^j*(2:ℝ)^j := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = (2*(s.card:ℝ))^j := by rw [← mul_pow]; congr 1; ring
        _ ≤ B^j := pow_le_pow_left₀ (by positivity) hcb j
    _ ≤ ∑ _j ∈ Finset.range (R+1), B^R := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_right₀ hB (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp [B]

/-- A convenient version when each selected modulus has at most two forbidden
residues. The joint-count error assumption still has to be justified by CRT. -/
theorem finite_brun_upper_two_roots (A : Finset α) (s : Finset ι) (b : ι → α → Prop)
    (ν : ι → ℝ) (X : ℝ) (hν : ∀ p ∈ s, 0 ≤ ν p ∧ ν p ≤ 1) (hX : 0 ≤ X)
    {r : ℕ} (hr : 0 < r) (hlarge : 4*(∑ p ∈ s, ν p)^2 ≤ (r:ℝ))
    (hE : ∀ t ⊆ s, t.card ≤ 2*r →
      |jointCount A b t - X*(∏ p ∈ t, ν p)| ≤ (2:ℝ)^t.card) :
    (survivors A s b).card ≤
      X*((∏ p ∈ s, (1-ν p)) + (1/4:ℝ)^r) +
        (2*r+1:ℕ) * (2*(max 1 s.card):ℝ)^(2*r) := by
  have hb := finite_brun_upper A s b ν X (fun t => (2:ℝ)^t.card) hν hX hr hE
  have ht := factorial_tail_bound (Finset.sum_nonneg (fun p hp => (hν p hp).1)) hr hlarge
  have he := two_root_error_bound s (2*r)
  have hm := mul_le_mul_of_nonneg_left (add_le_add_right ht (∏ p ∈ s, (1-ν p))) hX
  linarith

end Erdos371FiniteBrun

#print axioms Erdos371FiniteBrun.even_truncation_bounds
#print axioms Erdos371FiniteBrun.factorial_mul_elem_le
#print axioms Erdos371FiniteBrun.finite_brun_upper
#print axioms Erdos371FiniteBrun.finite_brun_upper_two_roots
