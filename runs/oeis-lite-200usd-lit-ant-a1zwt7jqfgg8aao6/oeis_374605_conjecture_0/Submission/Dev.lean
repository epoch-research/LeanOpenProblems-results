import FormalConjectures.Util.ProblemImports

open Finset

-- Lucas helper: C(c*p, p) ≡ c (as ZMod p), for c ≥ 1
theorem choose_cmul_p (p c : ℕ) [hp : Fact p.Prime] (hc : 1 ≤ c) :
    ((Nat.choose (c*p) p : ZMod p) = (c : ZMod p)) := by
  have hp0 : 0 < p := hp.1.pos
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := c*p) (k := p) (p := p)
  rw [Nat.mul_mod_left, Nat.mod_self, Nat.mul_div_cancel _ hp0, Nat.div_self hp0] at h
  simp only [Nat.choose_zero_right, Nat.choose_one_right, one_mul] at h
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at this
  exact this

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

theorem a_p_mod_p (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    (a p : ZMod p) = 13 := by
  have hp0 : 0 < p := hp.1.pos
  unfold a
  push_cast
  rw [Finset.sum_range_succ]  -- peel k = p
  have hmid : (∑ x ∈ Finset.range p,
      ((Nat.choose p x : ZMod p))^2 * (Nat.choose (p + x) x) *
        (Nat.choose (3*p+2*x) p)) =
      ((Nat.choose p 0 : ZMod p))^2 * (Nat.choose (p + 0) 0) * (Nat.choose (3*p+2*0) p) := by
    apply Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hp0)
    intro x hx hx0
    rw [Finset.mem_range] at hx
    have : (Nat.choose p x : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hp.1.dvd_choose_self hx0 hx
    rw [this]; ring
  rw [hmid]
  simp only [Nat.choose_zero_right, Nat.add_zero, Nat.mul_zero, Nat.choose_self,
    Nat.cast_one, one_pow, one_mul, mul_one]
  -- Now: C(3p,p) + C(p+p,p)*C(3p+2p,p) = 13, i.e. C(3p,p) + C(2p,p)*C(5p,p)
  have e3 : (Nat.choose (3*p) p : ZMod p) = 3 := choose_cmul_p p 3 (by norm_num)
  have e2 : (Nat.choose (p+p) p : ZMod p) = 2 := by
    rw [show p + p = 2 * p from by ring]; exact choose_cmul_p p 2 (by norm_num)
  have e5 : (Nat.choose (3*p+2*p) p : ZMod p) = 5 := by
    rw [show 3*p+2*p = 5*p from by ring]; exact choose_cmul_p p 5 (by norm_num)
  rw [e3, e2, e5]
  norm_num
