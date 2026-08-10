import Mathlib
open Finset BigOperators Nat

namespace Dev

def beta (p : ℕ) : ℕ → ZMod p
  | 0 => 1
  | (m+1) => -((m+2 : ZMod p))⁻¹ * ∑ i : Fin (m+1), ((m+2).choose i : ZMod p) * beta p i

theorem beta_succ (p m : ℕ) :
    beta p (m+1) = -((m+2 : ZMod p))⁻¹ *
      ∑ i ∈ range (m+1), ((m+2).choose i : ZMod p) * beta p i := by
  conv_lhs => rw [beta]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((m+2).choose i : ZMod p) * beta p i)]

theorem beta_rec (p m : ℕ) [Fact p.Prime] (hinv : ((m+2 : ℕ) : ZMod p) ≠ 0) :
    ∑ i ∈ range (m+2), ((m+2).choose i : ZMod p) * beta p i = 0 := by
  rw [sum_range_succ]
  have hchoose : ((m+2).choose (m+1) : ZMod p) = (m+2 : ZMod p) := by
    rw [Nat.choose_succ_self_right]; push_cast; ring
  have hne : ((m+2 : ZMod p)) ≠ 0 := by push_cast at hinv ⊢; exact hinv
  rw [hchoose, beta_succ]
  set S := ∑ i ∈ range (m+1), ((m+2).choose i : ZMod p) * beta p i with hS
  have hu : IsUnit ((m+2 : ZMod p)) := by rw [isUnit_iff_ne_zero]; exact hne
  have hc : (m+2 : ZMod p) * (m+2 : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  linear_combination (-S) * hc

/-- recursion in the form ∑_{i<N} C(N,i) β_i = 0 for N ≥ 2 (and N invertible). -/
theorem beta_rec' (p N : ℕ) [Fact p.Prime] (hN : 2 ≤ N) (hinv : ((N : ℕ) : ZMod p) ≠ 0) :
    ∑ i ∈ range N, ((N.choose i : ZMod p)) * beta p i = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  exact beta_rec p m hinv

theorem choose_choose_swap {n i l : ℕ} (h : i + l ≤ n) :
    n.choose i * (n - i).choose l = n.choose l * (n - l).choose i := by
  have key : ∀ a b : ℕ, a + b ≤ n →
      n.choose a * (n - a).choose b * (a ! * b ! * (n - a - b)!) = n ! := by
    intro a b hab
    have ha : a ≤ n := le_trans (Nat.le_add_right a b) hab
    have hb : b ≤ n - a := Nat.le_sub_of_add_le (by omega)
    have e1 : n.choose a * a ! * (n - a)! = n ! := Nat.choose_mul_factorial_mul_factorial ha
    have e2 : (n - a).choose b * b ! * (n - a - b)! = (n - a)! :=
      Nat.choose_mul_factorial_mul_factorial hb
    calc n.choose a * (n - a).choose b * (a ! * b ! * (n - a - b)!)
        = (n.choose a * a !) * ((n - a).choose b * b ! * (n - a - b)!) := by ring
      _ = (n.choose a * a !) * (n - a)! := by rw [e2]
      _ = n.choose a * a ! * (n - a)! := by ring
      _ = n ! := e1
  have kA := key i l h
  have kB := key l i (by omega)
  have hsub : n - i - l = n - l - i := by omega
  rw [hsub] at kA
  have kB' : n.choose l * (n - l).choose i * (i ! * l ! * (n - l - i)!) = n ! := by
    rw [show i ! * l ! = l ! * i ! from mul_comm _ _]; exact kB
  have heq : n.choose i * (n - i).choose l * (i ! * l ! * (n - l - i)!)
       = n.choose l * (n - l).choose i * (i ! * l ! * (n - l - i)!) := by rw [kA, kB']
  have hpos : 0 < i ! * l ! * (n - l - i)! := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos heq

end Dev

namespace Dev

-- Expansion (x+1)^n - x^n
theorem binom_diff (p : ℕ) (x : ZMod p) (n : ℕ) (hn : 1 ≤ n) :
    (x+1)^n - x^n = ∑ l ∈ range n, ((n.choose l : ZMod p)) * x^l := by
  have h := add_pow x 1 n
  simp only [one_pow, mul_one] at h
  rw [h, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self]
  rw [add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem findiff (p m : ℕ) [Fact p.Prime] (hm : m + 1 ≤ p - 1) (x : ZMod p) :
    ∑ i ∈ range (m+1), ((m+1).choose i : ZMod p) * beta p i * ((x+1)^(m+1-i) - x^(m+1-i))
      = (m+1) * x^m := by
  -- substitute the binomial difference
  have step1 : ∀ i ∈ range (m+1),
      ((m+1).choose i : ZMod p) * beta p i * ((x+1)^(m+1-i) - x^(m+1-i))
      = ∑ l ∈ range (m+1-i),
          ((m+1).choose i : ZMod p) * beta p i * ((m+1-i).choose l : ZMod p) * x^l := by
    intro i hi
    rw [mem_range] at hi
    rw [binom_diff p x (m+1-i) (by omega), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l hl; ring
  rw [Finset.sum_congr rfl step1]
  -- swap the order of summation
  rw [Finset.sum_comm' (s := range (m+1)) (t := fun i => range (m+1-i))
        (t' := range (m+1)) (s' := fun l => range (m+1-l))
        (f := fun i l => ((m+1).choose i : ZMod p) * beta p i * ((m+1-i).choose l : ZMod p) * x^l)
        (fun i l => by simp only [mem_range]; omega)]
  -- only l = m survives
  rw [Finset.sum_eq_single m]
  · -- the l = m term
    rw [show m + 1 - m = 1 from by omega, Finset.sum_range_one, Nat.sub_zero,
        Nat.choose_succ_self_right]
    have hb : beta p 0 = 1 := by rw [beta]
    rw [hb]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
    push_cast; ring
  · -- l ≠ m terms vanish
    intro l hl hlm
    rw [mem_range] at hl
    have hN : 2 ≤ m + 1 - l := by omega
    -- factor x^l and C(m+1,l), apply subset identity and beta_rec'
    have : ∑ i ∈ range (m+1-l),
        ((m+1).choose i : ZMod p) * beta p i * ((m+1-i).choose l : ZMod p) * x^l
        = x^l * ((m+1).choose l : ZMod p) *
            ∑ i ∈ range (m+1-l), ((m+1-l).choose i : ZMod p) * beta p i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i hi
      rw [mem_range] at hi
      have hsub := choose_choose_swap (n := m+1) (i := i) (l := l) (by omega)
      -- C(m+1,i)*C(m+1-i,l) = C(m+1,l)*C(m+1-l,i)
      have hc : ((m+1).choose i : ZMod p) * ((m+1-i).choose l : ZMod p)
              = ((m+1).choose l : ZMod p) * ((m+1-l).choose i : ZMod p) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) hsub
      -- rearrange
      calc ((m+1).choose i : ZMod p) * beta p i * ((m+1-i).choose l : ZMod p) * x^l
          = (((m+1).choose i : ZMod p) * ((m+1-i).choose l : ZMod p)) * beta p i * x^l := by ring
        _ = (((m+1).choose l : ZMod p) * ((m+1-l).choose i : ZMod p)) * beta p i * x^l := by rw [hc]
        _ = x^l * ((m+1).choose l : ZMod p) * (((m+1-l).choose i : ZMod p) * beta p i) := by ring
    rw [this]
    have hinv : ((m+1-l : ℕ) : ZMod p) ≠ 0 := by
      have hlt : m + 1 - l < p := by omega
      have hpos : 0 < m + 1 - l := by omega
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd hpos hdvd
      omega
    rw [beta_rec' p (m+1-l) hN hinv, mul_zero]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

end Dev

namespace Dev

/-- Faulhaber polynomial (Bernoulli polynomial scaled) in ZMod p. -/
def G (p m : ℕ) (x : ZMod p) : ZMod p :=
  ∑ i ∈ range (m+1), ((m+1).choose i : ZMod p) * beta p i * x^(m+1-i)

theorem G_diff (p m : ℕ) [Fact p.Prime] (hm : m + 1 ≤ p - 1) (x : ZMod p) :
    G p m (x+1) - G p m x = (m+1) * x^m := by
  unfold G
  rw [← Finset.sum_sub_distrib]
  rw [← findiff p m hm x]
  apply Finset.sum_congr rfl; intro i hi; ring

theorem cast_ne_zero_of_lt (p m : ℕ) [Fact p.Prime] (hpos : 0 < m) (hlt : m < p) :
    ((m : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd; have := Nat.le_of_dvd hpos hdvd; omega

/-- Faulhaber's formula in ZMod p:  ∑_{k<j} k^m = (m+1)⁻¹ G(j). -/
theorem faulhaber (p m : ℕ) [Fact p.Prime] (hm : m + 1 ≤ p - 1) (j : ℕ) :
    ∑ k ∈ range j, ((k : ZMod p))^m = ((m+1 : ZMod p))⁻¹ * G p m (j : ZMod p) := by
  have hinv : ((m+1 : ℕ) : ZMod p) ≠ 0 :=
    cast_ne_zero_of_lt p (m+1) (by omega) (by omega)
  have hinv' : ((m+1 : ZMod p)) ≠ 0 := by push_cast at hinv ⊢; exact hinv
  have hu : IsUnit ((m+1 : ZMod p)) := by rw [isUnit_iff_ne_zero]; exact hinv'
  have hc : ((m+1 : ZMod p))⁻¹ * (m+1 : ZMod p) = 1 := by
    rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hu
  induction j with
  | zero =>
    simp only [range_zero, Finset.sum_empty, Nat.cast_zero]
    have hG0 : G p m 0 = 0 := by
      unfold G; apply Finset.sum_eq_zero; intro i hi
      rw [mem_range] at hi; rw [zero_pow (by omega), mul_zero]
    rw [hG0, mul_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hcast : ((n+1 : ℕ) : ZMod p) = (n : ZMod p) + 1 := by push_cast; ring
    rw [hcast]
    have hGd : G p m ((n:ZMod p)+1) = G p m (n:ZMod p) + ((m:ZMod p)+1)*(n:ZMod p)^m := by
      have h := G_diff p m hm (n:ZMod p); linear_combination h
    have hsimp : ((m:ZMod p)+1)⁻¹*(((m:ZMod p)+1)*(↑n:ZMod p)^m) = (↑n)^m := by
      rw [← mul_assoc, hc, one_mul]
    rw [hGd, mul_add, hsimp]

end Dev

namespace Dev

variable {p : ℕ} [Fact p.Prime]

theorem sum_pow_univ (i : ℕ) (h : i < p - 1) : ∑ x : ZMod p, x ^ i = 0 := by
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  exact FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) i (by rw [hc]; exact h)

theorem inv_pow_eq_pow {x : ZMod p} (hx : x ≠ 0) {a : ℕ} (ha : a ≤ p - 1) :
    x⁻¹^a = x^(p-1-a) := by
  have h1 : x^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have h2 : x^(p-1-a) * x^a = 1 := by rw [← pow_add, Nat.sub_add_cancel ha, h1]
  have hxa : x^a ≠ 0 := pow_ne_zero a hx
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_left h2

/-- Inverse power sum over 1..p-1 vanishes for 1 ≤ a ≤ p-2. -/
theorem sum_inv_pow_univ {a : ℕ} (ha1 : 1 ≤ a) (ha2 : a ≤ p - 2) :
    ∑ x : ZMod p, x⁻¹^a = 0 := by
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have key : ∑ x : ZMod p, x⁻¹^a = ∑ x : ZMod p, x^(p-1-a) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : x = 0
    · subst hx
      rw [inv_zero, zero_pow (by omega), zero_pow (by omega)]
    · exact inv_pow_eq_pow hx (by omega)
  rw [key]
  exact sum_pow_univ (p-1-a) (by omega)

theorem G_zero (m : ℕ) : G p m 0 = 0 := by
  unfold G; apply Finset.sum_eq_zero; intro i hi
  rw [mem_range] at hi; rw [zero_pow (by omega), mul_zero]

theorem G_one (m : ℕ) (hm : m + 1 ≤ p - 1) (hm1 : 1 ≤ m) : G p m 1 = 0 := by
  unfold G
  have : ∑ i ∈ range (m+1), ((m+1).choose i : ZMod p) * beta p i * (1:ZMod p)^(m+1-i)
       = ∑ i ∈ range (m+1), ((m+1).choose i : ZMod p) * beta p i := by
    apply Finset.sum_congr rfl; intro i hi; rw [one_pow, mul_one]
  rw [this]
  exact beta_rec' p (m+1) (by omega) (by
    have := cast_ne_zero_of_lt p (m+1) (by omega) (by omega); exact this)

/-- Symmetry of the Faulhaber polynomial G. -/
theorem G_symm (m : ℕ) (hm : m + 1 ≤ p - 1) (hm1 : 1 ≤ m) (x : ZMod p) :
    G p m x = (-1)^(m+1) * G p m (1 - x) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  set c : ZMod p := (-1)^(m+1) with hc
  -- the difference equation makes  h y := G y - c G(1-y)  periodic with period 1
  have hstep : ∀ y : ZMod p,
      G p m (y+1) - c * G p m (1 - (y+1)) = G p m y - c * G p m (1 - y) := by
    intro y
    have hd1 : G p m (y+1) - G p m y = (m+1) * y^m := G_diff p m hm y
    have hd2 : G p m ((-y)+1) - G p m (-y) = (m+1) * (-y)^m := G_diff p m hm (-y)
    have e1 : (1 : ZMod p) - (y+1) = -y := by ring
    have e2 : (1 : ZMod p) - y = (-y) + 1 := by ring
    have hsq : ((-1:ZMod p))^(m*2) = 1 := by
      rw [show m*2 = 2*m from by ring, pow_mul]; simp
    rw [e1, e2, hc]
    linear_combination hd1 + (-1)^(m+1) * hd2 - (↑m+1)*y^m*hsq
  have key : ∀ n : ℕ,
      G p m (n:ZMod p) - c * G p m (1 - (n:ZMod p))
        = G p m 0 - c * G p m (1 - 0) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hs := hstep (k:ZMod p)
      have hc1 : ((k+1:ℕ):ZMod p) = (k:ZMod p)+1 := by push_cast; ring
      rw [hc1, hs, ih]
  have hconst : G p m x - c * G p m (1 - x) = G p m 0 - c * G p m (1 - 0) := by
    have hx : x = ((x.val : ℕ) : ZMod p) := (ZMod.natCast_rightInverse x).symm
    rw [hx]; exact key x.val
  have hr : G p m 0 - c * G p m (1 - 0) = 0 := by
    rw [G_zero, sub_zero, G_one m hm hm1]; ring
  rw [hr] at hconst
  have : G p m x = c * G p m (1 - x) := by linear_combination hconst
  rw [this, hc]

end Dev

namespace Dev
open Polynomial
variable {p : ℕ} [Fact p.Prime]

/-- The Faulhaber polynomial as a genuine polynomial. -/
noncomputable def Qpoly (m : ℕ) : (ZMod p)[X] :=
  ∑ i ∈ range (m+1), C (((m+1).choose i : ZMod p) * beta p i) * X^(m+1-i)

theorem Qpoly_eval (m : ℕ) (x : ZMod p) : (Qpoly m).eval x = G p m x := by
  unfold Qpoly G
  rw [eval_finset_sum]
  apply Finset.sum_congr rfl; intro i hi
  simp only [eval_mul, eval_C, eval_pow, eval_X]

theorem Qpoly_natDegree_le (m : ℕ) : (Qpoly (p:=p) m).natDegree ≤ m + 1 := by
  unfold Qpoly
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [mem_range] at hi
  apply le_trans natDegree_mul_le
  rw [natDegree_C, natDegree_X_pow]
  omega

/-- The reflected polynomial. -/
noncomputable def Rpoly (m : ℕ) : (ZMod p)[X] :=
  C ((-1)^(m+1)) * (Qpoly m).comp (C 1 - X)

theorem Rpoly_natDegree_le (m : ℕ) : (Rpoly (p:=p) m).natDegree ≤ m + 1 := by
  unfold Rpoly
  apply le_trans natDegree_mul_le
  rw [natDegree_C]
  have h1 : ((Qpoly (p:=p) m).comp (C 1 - X)).natDegree ≤ m + 1 := by
    apply le_trans natDegree_comp_le
    have hcq := Qpoly_natDegree_le (p:=p) m
    have hcd : (C 1 - X : (ZMod p)[X]).natDegree ≤ 1 := by
      apply le_trans (natDegree_sub_le _ _); rw [natDegree_C, natDegree_X]; simp
    calc (Qpoly (p:=p) m).natDegree * (C 1 - X : (ZMod p)[X]).natDegree
        ≤ (m+1) * 1 := Nat.mul_le_mul hcq hcd
      _ = m + 1 := by ring
  omega

theorem Rpoly_eval (m : ℕ) (x : ZMod p) :
    (Rpoly m).eval x = (-1)^(m+1) * G p m (1 - x) := by
  unfold Rpoly
  rw [eval_mul, eval_C, eval_comp]
  simp only [eval_sub, eval_C, eval_X]
  rw [Qpoly_eval]

theorem Qpoly_eq_Rpoly (m : ℕ) (hm : m + 1 ≤ p - 1) (hm1 : 1 ≤ m) :
    Qpoly (p:=p) m = Rpoly m := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hp := (Fact.out (p := p.Prime)).two_le
  refine eq_of_natDegree_lt_card_of_eval_eq (Qpoly (p:=p) m) (Rpoly m)
      (f := id) Function.injective_id ?_ ?_
  · intro x
    simp only [id_eq]
    rw [Qpoly_eval, Rpoly_eval]
    exact G_symm m hm hm1 x
  · rw [ZMod.card]
    have h1 := Qpoly_natDegree_le (p:=p) m
    have h2 := Rpoly_natDegree_le (p:=p) m
    omega

/-- The evaluation of the derivative of `Qpoly`. -/
theorem Qpoly_deriv_eval (m : ℕ) (x : ZMod p) :
    (derivative (Qpoly (p:=p) m)).eval x
      = ∑ i ∈ range (m+1),
          (((m+1).choose i : ZMod p) * beta p i) * ((m+1-i : ℕ):ZMod p) * x^(m+1-i-1) := by
  unfold Qpoly
  rw [derivative_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [derivative_C_mul, derivative_X_pow]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem Qpoly_deriv_eval_zero (m : ℕ) (hm1 : 1 ≤ m) :
    (derivative (Qpoly (p:=p) m)).eval 0 = ((m:ZMod p)+1) * beta p m := by
  rw [Qpoly_deriv_eval]
  rw [Finset.sum_eq_single m]
  · rw [Nat.choose_succ_self_right]
    have h0 : (0:ZMod p)^(m+1-m-1) = 1 := by
      rw [show m+1-m-1 = 0 from by omega, pow_zero]
    rw [h0, show m+1-m = 1 from by omega]
    push_cast; ring
  · intro i hi hned
    rw [mem_range] at hi
    have hz : (0:ZMod p)^(m+1-i-1) = 0 := by
      apply zero_pow; omega
    rw [hz, mul_zero]
  · intro h; exact absurd (mem_range.mpr (by omega)) h

theorem Qpoly_deriv_eval_one (m : ℕ) (hm : m + 1 ≤ p - 1) (hm3 : 2 ≤ m) :
    (derivative (Qpoly (p:=p) m)).eval 1 = ((m:ZMod p)+1) * beta p m := by
  rw [Qpoly_deriv_eval]
  have hterm : ∀ i ∈ range (m+1),
      (((m+1).choose i : ZMod p) * beta p i) * ((m+1-i : ℕ):ZMod p) * (1:ZMod p)^(m+1-i-1)
        = ((m:ZMod p)+1) * (((m.choose i : ℕ):ZMod p) * beta p i) := by
    intro i hi
    rw [mem_range] at hi
    rw [one_pow, mul_one]
    have hc : (m+1).choose i * (m+1-i) = (m+1) * m.choose i := by
      rw [← Nat.choose_mul_succ_eq]; ring
    have hcast : ((m+1).choose i : ZMod p) * ((m+1-i : ℕ):ZMod p)
        = ((m+1 : ℕ):ZMod p) * ((m.choose i : ℕ):ZMod p) := by
      exact_mod_cast congrArg (Nat.cast (R := ZMod p)) hc
    rw [show (((m+1).choose i : ZMod p) * beta p i) * ((m+1-i : ℕ):ZMod p)
          = (((m+1).choose i : ZMod p) * ((m+1-i : ℕ):ZMod p)) * beta p i from by ring, hcast]
    push_cast; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hsplit : ∑ i ∈ range (m+1), (((m.choose i : ℕ):ZMod p) * beta p i) = beta p m := by
    rw [Finset.sum_range_succ]
    have h0 : ∑ i ∈ range m, (((m.choose i : ℕ):ZMod p) * beta p i) = 0 :=
      beta_rec' p m (by omega) (cast_ne_zero_of_lt p m (by omega) (by omega))
    rw [h0, Nat.choose_self]; push_cast; ring
  rw [hsplit]

theorem Rpoly_deriv_eval_zero (m : ℕ) :
    (derivative (Rpoly (p:=p) m)).eval 0
      = -((-1:ZMod p)^(m+1)) * (derivative (Qpoly (p:=p) m)).eval 1 := by
  unfold Rpoly
  rw [derivative_C_mul, Polynomial.derivative_comp]
  simp only [eval_mul, eval_C, eval_comp, derivative_sub, derivative_C, derivative_X,
    eval_sub, eval_X, eval_one, sub_zero, zero_sub, eval_neg]
  ring

theorem sum_pow_all (i : ℕ) (hi : 1 ≤ i) :
    ∑ x : ZMod p, (x:ZMod p) ^ i = if (p - 1) ∣ i then -1 else 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  have hi0 : i ≠ 0 := by omega
  let embU : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : (Finset.univ.map embU) = (Finset.univ \ {0} : Finset (ZMod p)) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, embU]
    exact isUnit_iff_ne_zero
  have step : (∑ x : ZMod p, x ^ i) = ∑ x : (ZMod p)ˣ, ((x:ZMod p) ^ i) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
        Finset.sum_singleton, zero_pow hi0, add_zero, ← hmap, Finset.sum_map]
    rfl
  rw [step, FiniteField.sum_pow_units (ZMod p) i, ZMod.card]

theorem sum_zmod_eq_sum_range (g : ZMod p → ZMod p) :
    ∑ x : ZMod p, g x = ∑ k ∈ range p, g (k:ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  apply Finset.sum_nbij' (fun x => ZMod.val x) (fun k => (k:ZMod p))
  · intro x _; rw [mem_range]; exact ZMod.val_lt x
  · intro k _; exact mem_univ _
  · intro x _; exact ZMod.natCast_rightInverse x
  · intro k hk; rw [mem_range] at hk; exact ZMod.val_cast_of_lt hk
  · intro x _; rw [ZMod.natCast_rightInverse x]

theorem sum_pow_range (e : ℕ) (he : 1 ≤ e) :
    ∑ k ∈ range p, (k:ZMod p)^e = if (p-1)∣e then -1 else 0 := by
  rw [← sum_zmod_eq_sum_range (fun x => x^e)]
  exact sum_pow_all e he

/-- Plain (Bernoulli) convolution P_n = ∑_{a=0}^n β_a β_{n-a}. -/
def Pconv (n : ℕ) : ZMod p := ∑ a ∈ range (n+1), beta p a * beta p (n - a)

/-- Partial harmonic sum H_{k-1} = ∑_{j=1}^{k-1} 1/j equals -G(k). -/
theorem Hm_eq (k : ℕ) : ∑ j ∈ range k, (j:ZMod p)^(p-2) = - G p (p-2) (k:ZMod p) := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have hval : ((p-2 : ℕ) : ZMod p) + 1 = -1 := by
    have h2 : ((p-2:ℕ):ZMod p) = -2 := by
      rw [Nat.cast_sub hp, ZMod.natCast_self]; push_cast; ring
    rw [h2]; ring
  rw [faulhaber p (p-2) (by omega) k, hval]
  rw [show ((-1:ZMod p))⁻¹ = -1 from by simp, neg_one_mul]

/-- Odd-indexed Bernoulli numbers (mod p) vanish. -/
theorem beta_odd (m : ℕ) (hm : m + 1 ≤ p - 1) (hodd : Odd m) (hm3 : 3 ≤ m) :
    beta p m = 0 := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have hQR := Qpoly_eq_Rpoly m hm (by omega)
  have hmaster : (derivative (Qpoly (p:=p) m)).eval 0
      = (derivative (Rpoly (p:=p) m)).eval 0 := by rw [hQR]
  rw [Qpoly_deriv_eval_zero m (by omega), Rpoly_deriv_eval_zero m,
      Qpoly_deriv_eval_one m hm (by omega)] at hmaster
  -- m odd ⇒ (-1)^(m+1) = 1
  have hsign : ((-1:ZMod p))^(m+1) = 1 := by
    obtain ⟨t, rfl⟩ := hodd
    rw [show 2*t+1+1 = 2*(t+1) from by ring, pow_mul]; simp
  rw [hsign] at hmaster
  -- hmaster : (↑m+1)*β = -(1)*((↑m+1)*β) = -(↑m+1)*β
  have hne1 : ((m:ZMod p)+1) ≠ 0 := by
    have := cast_ne_zero_of_lt p (m+1) (by omega) (by omega)
    push_cast at this; convert this using 1
  have h2 : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := cast_ne_zero_of_lt p 2 (by omega) (by omega)
    push_cast at this; exact this
  have hfinal : (2:ZMod p) * (((m:ZMod p)+1) * beta p m) = 0 := by
    linear_combination hmaster
  rcases mul_eq_zero.mp hfinal with h | h
  · exact absurd h h2
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hne1
    · exact h'

/-- C(p-1, a) ≡ (-1)^a  mod p. -/
theorem choose_pm1 (a : ℕ) (ha : a ≤ p - 1) : ((p-1).choose a : ZMod p) = (-1)^a := by
  have hp := (Fact.out (p := p.Prime)).two_le
  induction a with
  | zero => simp
  | succ n ih =>
    have hrec := Nat.choose_succ_right_eq (p-1) n
    have hcast : ((p-1).choose (n+1) : ZMod p) * ((n:ZMod p)+1)
        = ((p-1).choose n : ZMod p) * (((p-1-n : ℕ)):ZMod p) := by
      have h := congrArg (Nat.cast (R := ZMod p)) hrec
      push_cast at h
      linear_combination h
    have hpn : (((p-1-n:ℕ)):ZMod p) = -((n:ZMod p)+1) := by
      have h1 : ((p-1-n:ℕ):ZMod p) = ((p:ℕ):ZMod p) - 1 - n := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [h1, ZMod.natCast_self]; ring
    rw [hpn, ih (by omega)] at hcast
    have hne : ((n:ZMod p)+1) ≠ 0 := by
      have := cast_ne_zero_of_lt p (n+1) (by omega) (by omega); push_cast at this; convert this using 1
    have hfin : ((p-1).choose (n+1):ZMod p) = (-1)^n * (-1) := by
      apply mul_right_cancel₀ hne; rw [hcast]; ring
    rw [hfin]; ring

/-- coefficient abbreviation -/
private def cc (a : ℕ) : ZMod p := ((p-1).choose a : ZMod p) * beta p a

theorem comp1 (hp5 : 5 ≤ p) :
    (∑ k ∈ range p, (k:ZMod p)^(p-3) * (∑ j ∈ range k, (j:ZMod p)^(p-2))^2)
      = - Pconv (p-3) := by
  have hp := (Fact.out (p := p.Prime)).two_le
  -- expand each summand
  have e1 : ∀ k ∈ range p,
      (k:ZMod p)^(p-3) * (∑ j ∈ range k, (j:ZMod p)^(p-2))^2
        = ∑ a ∈ range (p-1), ∑ a' ∈ range (p-1),
            (cc a * cc a') * (k:ZMod p)^((p-3)+((p-1)-a)+((p-1)-a')) := by
    intro k hk
    rw [Hm_eq, neg_sq]
    unfold G
    rw [show p-2+1 = p-1 from by omega, pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a' ha'
    unfold cc
    ring
  rw [Finset.sum_congr rfl e1]
  -- swap sums: ∑_k ∑_a ∑_a' → ∑_a ∑_a' (cc cc) ∑_k
  rw [Finset.sum_comm]
  have hswap : ∀ a ∈ range (p-1),
      (∑ k ∈ range p, ∑ a' ∈ range (p-1),
          (cc a * cc a') * (k:ZMod p)^((p-3)+((p-1)-a)+((p-1)-a')))
      = ∑ a' ∈ range (p-1), (cc a * cc a') *
          (∑ k ∈ range p, (k:ZMod p)^((p-3)+((p-1)-a)+((p-1)-a'))) := by
    intro a ha
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a' ha'
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl hswap]
  -- divisibility characterization
  have hdvd : ∀ a a' : ℕ, a ≤ p-2 → a' ≤ p-2 →
      ((p-1) ∣ (3*p-5-a-a') ↔ (a+a' = p-3 ∨ a+a' = 2*p-4)) := by
    intro a a' ha ha'
    have hsum : (3*p-5-a-a') + (a+a'+2) = 3*(p-1) := by omega
    constructor
    · intro hd
      have hd2 : (p-1) ∣ (a+a'+2) := by
        have : (p-1) ∣ (3*(p-1) - (3*p-5-a-a')) := Nat.dvd_sub ⟨3, by ring⟩ hd
        have heq : 3*(p-1) - (3*p-5-a-a') = a+a'+2 := by omega
        rwa [heq] at this
      obtain ⟨c, hc⟩ := hd2
      have hcle : c ≤ 2 := Nat.le_of_mul_le_mul_left (by rw [← hc]; omega) (by omega)
      interval_cases c <;> omega
    · rintro (h | h)
      · exact ⟨2, by omega⟩
      · exact ⟨1, by omega⟩
  -- evaluate inner power sum
  have e2 : ∀ a ∈ range (p-1), ∀ a' ∈ range (p-1),
      (∑ k ∈ range p, (k:ZMod p)^((p-3)+((p-1)-a)+((p-1)-a')))
        = (if a + a' = p-3 then (-1:ZMod p) else 0)
          + (if a + a' = 2*p-4 then (-1:ZMod p) else 0) := by
    intro a ha a' ha'
    rw [mem_range] at ha ha'
    rw [sum_pow_range _ (by omega)]
    have hE : (p-3)+((p-1)-a)+((p-1)-a') = 3*p-5-a-a' := by omega
    rw [hE]
    have hiff := hdvd a a' (by omega) (by omega)
    by_cases h1 : a + a' = p-3
    · rw [if_pos (hiff.mpr (Or.inl h1)), if_pos h1, if_neg (by omega)]; ring
    · by_cases h2 : a + a' = 2*p-4
      · rw [if_pos (hiff.mpr (Or.inr h2)), if_neg h1, if_pos h2]; ring
      · rw [if_neg (fun hd => (by rcases hiff.mp hd with h|h; exacts [h1 h, h2 h])),
            if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun a' ha' => by
        rw [e2 a ha a' ha']))]
  -- split into two diagonal sums
  simp only [mul_add, Finset.sum_add_distrib]
  -- second diagonal vanishes
  have hpodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
  have hp2odd : Odd (p-2) := by rcases hpodd with ⟨t, ht⟩; exact ⟨t-1, by omega⟩
  have hbeta2 : beta p (p-2) = 0 := beta_odd (p-2) (by omega) hp2odd (by omega)
  have hD2 : (∑ a ∈ range (p-1), ∑ a' ∈ range (p-1),
        cc a * cc a' * (if a + a' = 2*p-4 then (-1:ZMod p) else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun a' ha' => ?_))
    rw [mem_range] at ha ha'
    by_cases h : a + a' = 2*p-4
    · have hae : a = p-2 := by omega
      have hca : cc (p:=p) a = 0 := by rw [hae]; unfold cc; rw [hbeta2, mul_zero]
      rw [hca, zero_mul, zero_mul]
    · rw [if_neg h, mul_zero]
  rw [hD2, add_zero]
  -- first diagonal
  have hD1 : (∑ a ∈ range (p-1), ∑ a' ∈ range (p-1),
        cc a * cc a' * (if a + a' = p-3 then (-1:ZMod p) else 0))
      = - ∑ a ∈ range (p-2), cc a * cc (p-3-a) := by
    have key : ∀ a ∈ range (p-1),
        (∑ a' ∈ range (p-1), cc a * cc a' * (if a + a' = p-3 then (-1:ZMod p) else 0))
        = (if a ≤ p-3 then -(cc a * cc (p-3-a)) else 0) := by
      intro a ha; rw [mem_range] at ha
      by_cases hale : a ≤ p-3
      · rw [if_pos hale, Finset.sum_eq_single (p-3-a)]
        · rw [if_pos (by omega)]; ring
        · intro b hb hbne; rw [if_neg (by omega), mul_zero]
        · intro hbmem; exact absurd (mem_range.mpr (by omega)) hbmem
      · rw [if_neg hale]
        refine Finset.sum_eq_zero (fun a' ha' => ?_); rw [mem_range] at ha'
        rw [if_neg (by omega), mul_zero]
    rw [Finset.sum_congr rfl key,
        show p-1 = (p-2)+1 from by omega, Finset.sum_range_succ, if_neg (by omega), add_zero]
    have hcong : ∀ a ∈ range (p-2),
        (if a ≤ p-3 then -(cc a * cc (p-3-a)) else (0:ZMod p)) = -(cc a * cc (p-3-a)) := by
      intro a ha; rw [mem_range] at ha; rw [if_pos (by omega)]
    rw [Finset.sum_congr rfl hcong, Finset.sum_neg_distrib]
  rw [hD1, neg_inj]
  -- ∑_{range(p-2)} cc a cc(p-3-a) = Pconv(p-3)
  unfold Pconv
  rw [show p-3+1 = p-2 from by omega]
  apply Finset.sum_congr rfl
  intro a ha; rw [mem_range] at ha
  unfold cc
  rw [choose_pm1 a (by omega), choose_pm1 (p-3-a) (by omega)]
  have hsign : ((-1:ZMod p))^a * (-1)^(p-3-a) = 1 := by
    rw [← pow_add, show a+(p-3-a)=p-3 from by omega]
    rcases hpodd with ⟨t, ht⟩
    rw [show p-3 = 2*(t-1) from by omega, pow_mul]; simp
  rw [show ((-1:ZMod p))^a * beta p a * ((-1)^(p-3-a) * beta p (p-3-a))
        = (((-1:ZMod p))^a * (-1)^(p-3-a)) * (beta p a * beta p (p-3-a)) from by ring,
      hsign, one_mul]

/-- Fermat reduction of exponents by `p-1` inside partial sums. -/
theorem pow_reduce (j : ℕ) (e : ℕ) (he : 1 ≤ e) :
    (j:ZMod p)^(e+(p-1)) = (j:ZMod p)^e := by
  by_cases hjz : (j:ZMod p) = 0
  · rw [hjz, zero_pow (by omega), zero_pow (by omega)]
  · rw [pow_add, ZMod.pow_card_sub_one_eq_one hjz, mul_one]

/-- (∑ f)² split into off-diagonal and diagonal parts. -/
theorem sq_sum_split (f : ℕ → ZMod p) (k : ℕ) :
    (∑ i ∈ range k, f i)^2
      = 2 * (∑ j ∈ range k, ∑ i ∈ range j, f i * f j) + ∑ i ∈ range k, (f i)^2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun i => f i),
        Finset.sum_range_succ (fun j => ∑ i ∈ range j, f i * f j),
        Finset.sum_range_succ (fun i => (f i)^2)]
    have hinner : ∑ i ∈ range n, f i * f n = (∑ i ∈ range n, f i) * f n := by
      rw [← Finset.sum_mul]
    rw [hinner]
    linear_combination ih

def Vgate : ZMod p :=
  ∑ k ∈ range p, (k:ZMod p)^(p-3) * (∑ j ∈ range k, (j:ZMod p)^(p-2))^2

def Z211 : ZMod p :=
  ∑ k ∈ range p, (k:ZMod p)^(p-3) *
    ∑ j ∈ range k, ∑ i ∈ range j, (i:ZMod p)^(p-2) * (j:ZMod p)^(p-2)

def Z22 : ZMod p :=
  ∑ k ∈ range p, (k:ZMod p)^(p-3) * ∑ i ∈ range k, ((i:ZMod p)^(p-2))^2

theorem hstuffle : Vgate (p:=p) = 2 * Z211 + Z22 := by
  unfold Vgate Z211 Z22
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sq_sum_split (fun j => (j:ZMod p)^(p-2)) k]
  ring

theorem hZ22 (hp7 : 7 ≤ p) : Z22 (p:=p) = 0 := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have hf : Z22 (p:=p)
      = ∑ k ∈ range p, ∑ i ∈ range k, (i:ZMod p)^(p-3) * (k:ZMod p)^(p-3) := by
    unfold Z22; apply Finset.sum_congr rfl; intro k hk
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
    have h : ((i:ZMod p)^(p-2))^2 = (i:ZMod p)^(p-3) := by
      rw [← pow_mul, show (p-2)*2 = (p-3)+(p-1) from by omega, pow_reduce i (p-3) (by omega)]
    rw [h]; ring
  have hsplit := sq_sum_split (p:=p) (fun k => (k:ZMod p)^(p-3)) p
  have hsf : (∑ k ∈ range p, (k:ZMod p)^(p-3)) = 0 := by
    rw [sum_pow_range (p-3) (by omega),
        if_neg (show ¬(p-1)∣(p-3) from fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
  have hsf2 : (∑ k ∈ range p, ((k:ZMod p)^(p-3))^2) = 0 := by
    have hc : ∀ k ∈ range p, ((k:ZMod p)^(p-3))^2 = (k:ZMod p)^(p-5) := by
      intro k hk; rw [← pow_mul, show (p-3)*2 = (p-5)+(p-1) from by omega, pow_reduce k (p-5) (by omega)]
    rw [Finset.sum_congr rfl hc, sum_pow_range (p-5) (by omega),
        if_neg (show ¬(p-1)∣(p-5) from fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
  rw [hsf, hsf2] at hsplit
  rw [hf]
  have h2 : (2:ZMod p) ≠ 0 := by
    have := cast_ne_zero_of_lt p 2 (by omega) (by omega); push_cast at this; exact this
  have : (2:ZMod p) * (∑ j ∈ range p, ∑ i ∈ range j, (i:ZMod p)^(p-3) * (j:ZMod p)^(p-3)) = 0 := by
    linear_combination -hsplit
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h h2
  · exact h

theorem phi_eq (hp7 : 7 ≤ p) (k : ℕ) :
    (∑ j ∈ range k, ∑ i ∈ range j, (i:ZMod p)^(p-2) * (j:ZMod p)^(p-2))
      = - ∑ b ∈ range (p-2), (((p-1).choose b : ZMod p) * beta p b * ((p-1-b : ℕ):ZMod p)⁻¹)
            * G p (p-2-b) (k:ZMod p) := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have hpodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
  have hp2odd : Odd (p-2) := by rcases hpodd with ⟨t, ht⟩; exact ⟨t-1, by omega⟩
  have hbeta2 : beta p (p-2) = 0 := beta_odd (p-2) (by omega) hp2odd (by omega)
  have step1 : ∀ j ∈ range k, (∑ i ∈ range j, (i:ZMod p)^(p-2) * (j:ZMod p)^(p-2))
      = (j:ZMod p)^(p-2) * (- G p (p-2) (j:ZMod p)) := by
    intro j hj; rw [← Finset.sum_mul, Hm_eq]; ring
  rw [Finset.sum_congr rfl step1]
  have step2 : ∀ j ∈ range k, (j:ZMod p)^(p-2) * (- G p (p-2) (j:ZMod p))
      = - ∑ b ∈ range (p-1), ((p-1).choose b : ZMod p) * beta p b * (j:ZMod p)^(2*p-3-b) := by
    intro j hj
    unfold G
    rw [show p-2+1 = p-1 from by omega, mul_neg]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b hb; rw [mem_range] at hb
    rw [show 2*p-3-b = (p-2)+(p-1-b) from by omega, pow_add]; ring
  rw [Finset.sum_congr rfl step2, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  rw [show p-1 = (p-2)+1 from by omega, Finset.sum_range_succ, hbeta2]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl; intro b hb; rw [mem_range] at hb
  rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j hj => by
        rw [show 2*p-3-b = (p-2-b)+(p-1) from by omega, pow_reduce j (p-2-b) (by omega)])]
  rw [faulhaber p (p-2-b) (by omega) k,
      show ((↑(p-2-b):ZMod p)+1) = ((p-2+1-b:ℕ):ZMod p) from by
        rw [show p-2+1-b = (p-2-b)+1 from by omega]; push_cast; ring]
  ring

private def dd (b : ℕ) : ZMod p :=
  ((p-1).choose b : ZMod p) * beta p b * ((p-1-b : ℕ):ZMod p)⁻¹

/-- Independent Faulhaber computation of `Z211` as a Bernoulli-weighted sum. -/
theorem comp2 (hp7 : 7 ≤ p) :
    Z211 (p:=p) = ∑ b ∈ range (p-2),
      dd b * ((p-1-b).choose (p-3-b) : ZMod p) * beta p (p-3-b) := by
  have hp := (Fact.out (p := p.Prime)).two_le
  unfold Z211
  rw [Finset.sum_congr rfl (fun k hk => by rw [phi_eq hp7 k])]
  -- distribute and fold dd
  have e0 : ∀ k ∈ range p,
      (k:ZMod p)^(p-3) * (- ∑ b ∈ range (p-2),
          (((p-1).choose b : ZMod p) * beta p b * ((p-1-b : ℕ):ZMod p)⁻¹) * G p (p-2-b) (k:ZMod p))
        = - ∑ b ∈ range (p-2), dd b * (G p (p-2-b) (k:ZMod p) * (k:ZMod p)^(p-3)) := by
    intro k hk
    rw [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro b hb
    unfold dd; ring
  rw [Finset.sum_congr rfl e0, Finset.sum_neg_distrib, Finset.sum_comm]
  -- inner Faulhaber-type evaluation
  have inner : ∀ b ∈ range (p-2),
      (∑ k ∈ range p, dd b * (G p (p-2-b) (k:ZMod p) * (k:ZMod p)^(p-3)))
        = - (dd b * ((p-1-b).choose (p-3-b) : ZMod p) * beta p (p-3-b)) := by
    intro b hb; rw [mem_range] at hb
    rw [← Finset.mul_sum]
    have hG : (∑ k ∈ range p, G p (p-2-b) (k:ZMod p) * (k:ZMod p)^(p-3))
        = - (((p-1-b).choose (p-3-b) : ZMod p) * beta p (p-3-b)) := by
      have hexp : ∀ k ∈ range p, G p (p-2-b) (k:ZMod p) * (k:ZMod p)^(p-3)
          = ∑ i ∈ range (p-1-b),
              ((p-1-b).choose i : ZMod p) * beta p i * (k:ZMod p)^(2*p-4-b-i) := by
        intro k hk
        unfold G
        rw [show p-2-b+1 = p-1-b from by omega, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i hi; rw [mem_range] at hi
        rw [show 2*p-4-b-i = (p-1-b-i)+(p-3) from by omega, pow_add]; ring
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
      have e3 : ∀ i ∈ range (p-1-b),
          (∑ k ∈ range p, ((p-1-b).choose i : ZMod p) * beta p i * (k:ZMod p)^(2*p-4-b-i))
            = ((p-1-b).choose i : ZMod p) * beta p i * (if i = p-3-b then (-1:ZMod p) else 0) := by
        intro i hi; rw [mem_range] at hi
        rw [← Finset.mul_sum, sum_pow_range _ (by omega)]
        congr 1
        have hdvd_i : (p-1) ∣ (2*p-4-b-i) ↔ i = p-3-b := by
          constructor
          · intro hd
            obtain ⟨c, hc⟩ := hd
            have hc_le : c ≤ 1 := by
              by_contra hcon
              have h2 : (p-1)*2 ≤ (p-1)*c := Nat.mul_le_mul (le_refl (p-1)) (by omega)
              rw [← hc] at h2; omega
            have hc_pos : c ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hc; omega
            have : c = 1 := by omega
            rw [this, mul_one] at hc; omega
          · intro h; exact ⟨1, by omega⟩
        by_cases h : i = p-3-b
        · rw [if_pos (hdvd_i.mpr h), if_pos h]
        · rw [if_neg (fun hd => h (hdvd_i.mp hd)), if_neg h]
      rw [Finset.sum_congr rfl e3,
          Finset.sum_eq_single (p-3-b)]
      · rw [if_pos rfl]; ring
      · intro i hi hine; rw [if_neg hine, mul_zero]
      · intro hmem; exact absurd (mem_range.mpr (by omega)) hmem
    rw [hG]; ring
  rw [Finset.sum_congr rfl inner, Finset.sum_neg_distrib, neg_neg]

/-- Relation (A): `2 Z211 = -P` from the stuffle identity. -/
theorem relA (hp7 : 7 ≤ p) : 2 * Z211 (p:=p) = - Pconv (p-3) := by
  have h := hstuffle (p:=p)
  rw [hZ22 hp7, add_zero] at h
  have hv : Vgate (p:=p) = - Pconv (p-3) := by unfold Vgate; exact comp1 (by omega)
  rw [hv] at h; exact h.symm

/-- Cast of `C(n,2)` into `ZMod p`. -/
theorem hchoose2 (n : ℕ) (hp3 : 3 ≤ p) :
    ((n.choose 2 : ℕ):ZMod p) = (n:ZMod p)*((n:ZMod p)-1)*(2:ZMod p)⁻¹ := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have h2 : (2:ZMod p) ≠ 0 := by
    have := cast_ne_zero_of_lt p 2 (by omega) (by omega); push_cast at this; exact this
  rcases Nat.eq_zero_or_pos n with hn|hn
  · subst hn; simp
  · have hev : 2 ∣ n*(n-1) := by
      have := (Nat.even_mul_succ_self (n-1)).two_dvd
      rw [show (n-1)+1 = n from by omega] at this
      rw [mul_comm]; exact this
    have hnat : n.choose 2 * 2 = n*(n-1) := by
      rw [Nat.choose_two_right, Nat.div_mul_cancel hev]
    have hcast : ((n.choose 2 : ℕ):ZMod p) * 2 = (n:ZMod p)*((n:ZMod p)-1) := by
      have : ((n.choose 2 * 2 : ℕ):ZMod p) = ((n*(n-1):ℕ):ZMod p) := by rw [hnat]
      push_cast [Nat.cast_sub hn] at this; push_cast; linear_combination this
    field_simp
    linear_combination hcast

/-- Relation (B): `2 Z211 = -2⁻¹ P` from the explicit weight computation. -/
theorem relB (hp7 : 7 ≤ p) : 2 * Z211 (p:=p) = - (2:ZMod p)⁻¹ * Pconv (p-3) := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have hpodd : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two (by omega)
  have h2 : (2:ZMod p) ≠ 0 := by
    have := cast_ne_zero_of_lt p 2 (by omega) (by omega); push_cast at this; exact this
  -- weight identity: each summand of comp2 equals (-1)^{b+1}(b+2)/2 β_b β_{p-3-b}
  have hw : ∀ b ∈ range (p-2),
      dd b * ((p-1-b).choose (p-3-b) : ZMod p) * beta p (p-3-b)
        = ((-1:ZMod p))^(b+1) * ((b:ZMod p)+2) * (2:ZMod p)⁻¹ * beta p b * beta p (p-3-b) := by
    intro b hb; rw [mem_range] at hb
    unfold dd
    -- cast pieces
    have hA : ((p-1).choose b : ZMod p) = (-1)^b := choose_pm1 b (by omega)
    have hB : ((p-1-b:ℕ):ZMod p) = -((b:ZMod p)+1) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast [ZMod.natCast_self]; ring
    have hsymm : (p-1-b).choose (p-3-b) = (p-1-b).choose 2 := by
      rw [show p-3-b = (p-1-b)-2 from by omega, Nat.choose_symm (by omega)]
    have hBne : ((b:ZMod p)+1) ≠ 0 := by
      have : ((b+1:ℕ):ZMod p) ≠ 0 := cast_ne_zero_of_lt p (b+1) (by omega) (by omega)
      push_cast at this; exact this
    have hD : ((p-1-b).choose (p-3-b) : ZMod p)
        = ((b:ZMod p)+1)*((b:ZMod p)+2)*(2:ZMod p)⁻¹ := by
      rw [hsymm, hchoose2 (p-1-b) (by omega), hB]; ring
    rw [hA, hD]
    -- (p-1-b)⁻¹ = -(b+1)⁻¹
    rw [hB]
    rw [pow_succ]
    have hinv : (-((b:ZMod p)+1))⁻¹ = -((b:ZMod p)+1)⁻¹ := by
      rw [neg_inv]
    rw [hinv]
    field_simp
  -- apply comp2 + weight identity
  rw [show 2 * Z211 (p:=p) = 2 * ∑ b ∈ range (p-2),
        ((-1:ZMod p))^(b+1) * ((b:ZMod p)+2) * (2:ZMod p)⁻¹ * beta p b * beta p (p-3-b) from by
      rw [comp2 hp7, Finset.sum_congr rfl hw]]
  -- symmetrize via reflection
  set f : ℕ → ZMod p := fun b => ((-1:ZMod p))^(b+1) * ((b:ZMod p)+2) * (2:ZMod p)⁻¹
      * beta p b * beta p (p-3-b) with hf
  have hrefl : (∑ b ∈ range (p-2), f b) = ∑ b ∈ range (p-2), f (p-3-b) := by
    rw [← Finset.sum_range_reflect f (p-2)]
    apply Finset.sum_congr rfl; intro b hb; rw [mem_range] at hb
    rw [show p - 2 - 1 - b = p - 3 - b from by omega]
  have hsum2 : (2:ZMod p) * ∑ b ∈ range (p-2), f b
      = ∑ b ∈ range (p-2), (f b + f (p-3-b)) := by
    rw [Finset.sum_add_distrib, ← hrefl]; ring
  rw [hsum2]
  -- f b + f (p-3-b) = (-1)^{b+1} 2⁻¹ β_b β_{p-3-b}
  have hpair : ∀ b ∈ range (p-2), f b + f (p-3-b)
      = ((-1:ZMod p))^(b+1) * (2:ZMod p)⁻¹ * beta p b * beta p (p-3-b) := by
    intro b hb; rw [mem_range] at hb
    simp only [hf]
    have hbcast : ((p-3-b:ℕ):ZMod p) = -((b:ZMod p)+3) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast [ZMod.natCast_self]; ring
    have hbeq : p-3-(p-3-b) = b := by omega
    rw [hbeq, hbcast]
    have hsign : ((-1:ZMod p))^(p-3-b+1) = ((-1:ZMod p))^(b+1) := by
      have hYY : ((-1:ZMod p))^(b+1) * ((-1:ZMod p))^(b+1) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
      have hXY : ((-1:ZMod p))^(p-3-b+1) * ((-1:ZMod p))^(b+1) = 1 := by
        rcases hpodd with ⟨t, ht⟩
        rw [← pow_add, show p-3-b+1+(b+1) = 2*t from by omega, pow_mul]; simp
      calc ((-1:ZMod p))^(p-3-b+1)
          = ((-1:ZMod p))^(p-3-b+1) * (((-1:ZMod p))^(b+1) * ((-1:ZMod p))^(b+1)) := by
            rw [hYY, mul_one]
        _ = (((-1:ZMod p))^(p-3-b+1) * ((-1:ZMod p))^(b+1)) * ((-1:ZMod p))^(b+1) := by ring
        _ = ((-1:ZMod p))^(b+1) := by rw [hXY, one_mul]
    rw [hsign]; ring
  rw [Finset.sum_congr rfl hpair]
  -- parity collapse: ∑ (-1)^{b+1} 2⁻¹ β_b β_{p-3-b} = -2⁻¹ Pconv
  have hcollapse : ∀ b ∈ range (p-2),
      ((-1:ZMod p))^(b+1) * (2:ZMod p)⁻¹ * beta p b * beta p (p-3-b)
        = -((2:ZMod p)⁻¹ * (beta p b * beta p (p-3-b))) := by
    intro b hb; rw [mem_range] at hb
    rcases Nat.even_or_odd b with he|ho
    · rw [Odd.neg_one_pow (by rcases he with ⟨t,ht⟩; exact ⟨t, by omega⟩)]; ring
    · -- b odd: β_b β_{p-3-b} = 0
      have hz : beta p b * beta p (p-3-b) = 0 := by
        rcases Nat.lt_or_ge b 3 with hlt|hge
        · -- b = 1
          have hb1 : b = 1 := by rcases ho with ⟨t,ht⟩; omega
          rw [hb1]
          have : beta p (p-3-1) = 0 :=
            beta_odd (p-3-1) (by omega) (by rcases hpodd with ⟨t,ht⟩; exact ⟨t-2, by omega⟩) (by omega)
          rw [this, mul_zero]
        · rw [beta_odd b (by omega) ho (by omega), zero_mul]
      have hfact : ((-1:ZMod p))^(b+1) * (2:ZMod p)⁻¹ * beta p b * beta p (p-3-b)
          = (((-1:ZMod p))^(b+1)*(2:ZMod p)⁻¹) * (beta p b * beta p (p-3-b)) := by ring
      rw [hfact, hz]; ring
  rw [Finset.sum_congr rfl hcollapse, Finset.sum_neg_distrib, ← Finset.mul_sum]
  unfold Pconv
  rw [show p-3+1 = p-2 from by omega]
  ring

/-- The gate: `Pconv (p-3) = 0`, hence `Vgate = 0`. -/
theorem Pconv_eq_zero (hp7 : 7 ≤ p) : Pconv (p:=p) (p-3) = 0 := by
  have hp := (Fact.out (p := p.Prime)).two_le
  have h2 : (2:ZMod p) ≠ 0 := by
    have := cast_ne_zero_of_lt p 2 (by omega) (by omega); push_cast at this; exact this
  have hA := relA hp7
  have hB := relB hp7
  rw [hA] at hB
  -- -P = -2⁻¹ P  ⟹  P = 0
  have hPP : (2:ZMod p)⁻¹ * Pconv (p-3) = Pconv (p-3) := by linear_combination hB
  have h3 : ((2:ZMod p)⁻¹ - 1) * Pconv (p-3) = 0 := by linear_combination hPP
  have hne : ((2:ZMod p)⁻¹ - 1) ≠ 0 := by
    intro hc
    have : (2:ZMod p)⁻¹ = 1 := by linear_combination hc
    have h22 : (2:ZMod p) = 1 := by
      rw [← inv_inv (2:ZMod p), this, inv_one]
    have : (1:ZMod p) = 0 := by linear_combination h22
    exact one_ne_zero this
  exact (mul_eq_zero.mp h3).resolve_left hne

theorem Vgate_eq_zero (hp7 : 7 ≤ p) : Vgate (p:=p) = 0 := by
  unfold Vgate; rw [comp1 (by omega), Pconv_eq_zero hp7, neg_zero]

end Dev
