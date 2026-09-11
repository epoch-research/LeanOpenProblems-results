import FormalConjectures.Util.ProblemImports

/-!
# Proof of the conjecture

Setup: for `n = p^v`, `N = p^(v+1)` and `J = {j < N : p ∤ j}`, put `F(t) = ∏_{j∈J} (1 + tN/j)`
(a `p`-adic integer).  Then `C(2N,N) = C(2n,n)·F(1)`, `C(3N,N) = C(3n,n)·F(2)`, and pairing `j ↔ N-j`
gives `F(t)² = G(t²+t)` with `G(u) = ∏ (1 + u·N²/(j(N-j)))`.  Expanding `G` to second order and
using bounds on the power sums `∑ 1/j²`, `∑ 1/j⁴` over `J` (obtained by reduction mod `p`) yields the
congruence.
-/


open Finset

namespace A357569

/-- Non-multiples of `p` in `[0, m)`. -/
def J (p m : ℕ) : Finset ℕ := (range m).filter (fun j => ¬ p ∣ j)

lemma mem_J {p m j : ℕ} : j ∈ J p m ↔ j < m ∧ ¬ p ∣ j := by
  simp [J]

section double
variable {M : Type*} [CommMonoid M] {A : Type*} [AddCommMonoid A]

lemma prod_range_mul' (g : ℕ → M) (m s : ℕ) :
    ∏ j ∈ range (m * s), g j = ∏ t ∈ range s, ∏ i ∈ range m, g (m * t + i) := by
  induction s with
  | zero => simp
  | succ s ih => rw [Nat.mul_succ, prod_range_add, ih, prod_range_succ]

lemma sum_range_mul' (g : ℕ → A) (m s : ℕ) :
    ∑ j ∈ range (m * s), g j = ∑ t ∈ range s, ∑ i ∈ range m, g (m * t + i) := by
  induction s with
  | zero => simp
  | succ s ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma prod_J_mul (g : ℕ → M) {p m : ℕ} (hm : p ∣ m) :
    ∏ j ∈ J p (m * p), g j = ∏ t ∈ range p, ∏ i ∈ J p m, g (m * t + i) := by
  unfold J
  rw [prod_filter, prod_range_mul']
  refine prod_congr rfl fun t _ => ?_
  rw [prod_filter]
  refine prod_congr rfl fun i _ => ?_
  have : p ∣ m * t + i ↔ p ∣ i := Nat.dvd_add_right (dvd_mul_of_dvd_left hm t)
  simp only [this]

lemma sum_J_mul (g : ℕ → A) {p m : ℕ} (hm : p ∣ m) :
    ∑ j ∈ J p (m * p), g j = ∑ t ∈ range p, ∑ i ∈ J p m, g (m * t + i) := by
  unfold J
  rw [sum_filter, sum_range_mul']
  refine sum_congr rfl fun t _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  have : p ∣ m * t + i ↔ p ∣ i := Nat.dvd_add_right (dvd_mul_of_dvd_left hm t)
  simp only [this]

lemma prod_J_low (f : ℕ → M) (p n : ℕ) (hp : 0 < p) :
    ∏ j ∈ J p (p * n), f j = ∏ i ∈ range n, ∏ r ∈ range (p - 1), f (p * i + r + 1) := by
  unfold J
  rw [prod_filter, prod_range_mul']
  refine prod_congr rfl fun t _ => ?_
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [prod_range_succ', Nat.add_sub_cancel]
  simp only [add_zero, dvd_mul_right, not_true_eq_false, if_false, mul_one]
  refine prod_congr rfl fun r hr => ?_
  rw [mem_range] at hr
  have : ¬ (q + 1) ∣ (q + 1) * t + (r + 1) := by
    intro h
    rw [Nat.dvd_add_right (dvd_mul_right _ _)] at h
    exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  simp [this, add_assoc]

end double

lemma factorial_add_eq (c k : ℕ) :
    (c + k).factorial = c.factorial * ∏ j ∈ range k, (c + j + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, Nat.factorial_succ, ih, prod_range_succ]; ring

lemma choose_mul_factorial_eq (c N : ℕ) :
    (c + N).choose N * N.factorial = ∏ j ∈ range N, (c + j + 1) := by
  have h := Nat.add_choose_mul_factorial_mul_factorial c N
  rw [factorial_add_eq] at h
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos c)
  calc c.factorial * ((c + N).choose N * N.factorial)
      = (c + N).choose N * c.factorial * N.factorial := by ring
    _ = _ := h

lemma prod_range_mul_split (p c' n : ℕ) (hp : 0 < p) :
    ∏ j ∈ range (p * n), (p * c' + j + 1) =
      p ^ n * (∏ i ∈ range n, (c' + i + 1)) * ∏ j ∈ J p (p * n), (p * c' + j) := by
  rw [prod_J_low (fun j => p * c' + j) p n hp, prod_range_mul']
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← card_range n, ← prod_const, card_range, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun t _ => ?_
  rw [prod_range_succ]
  ring_nf

lemma choose_mul_D (p c' n : ℕ) (hp : 0 < p) :
    (p * c' + p * n).choose (p * n) * ∏ j ∈ J p (p * n), j =
      (c' + n).choose n * ∏ j ∈ J p (p * n), (p * c' + j) := by
  have h1 := choose_mul_factorial_eq (p * c') (p * n)
  rw [prod_range_mul_split p c' n hp, ← choose_mul_factorial_eq c' n] at h1
  have h2 := choose_mul_factorial_eq 0 (p * n)
  have h3 := prod_range_mul_split p 0 n hp
  have h4 := choose_mul_factorial_eq 0 n
  simp only [zero_add, Nat.choose_self, one_mul, mul_zero] at h2 h3 h4
  rw [h2, h3, ← h4] at h1
  have hpos : 0 < p ^ n * n.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc p ^ n * n.factorial * ((p * c' + p * n).choose (p * n) * ∏ j ∈ J p (p * n), j)
      = (p * c' + p * n).choose (p * n) * (p ^ n * n.factorial * ∏ j ∈ J p (p * n), j) := by ring
    _ = p ^ n * ((c' + n).choose n * n.factorial) * ∏ j ∈ J p (p * n), (p * c' + j) := h1
    _ = _ := by ring

end A357569

open Finset

namespace A357569

section expansion
variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

lemma L0 (q u : R) (s : Finset ι) (w : ι → R) (hw : ∀ i ∈ s, q ∣ w i) :
    q ∣ ∏ i ∈ s, (1 + u * w i) - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have h1 := ih (fun i hi => hw i (mem_insert_of_mem hi))
    have h2 := hw a (mem_insert_self a s)
    have : (1 + u * w a) * ∏ i ∈ s, (1 + u * w i) - 1 =
        (∏ i ∈ s, (1 + u * w i) - 1) + u * w a * ∏ i ∈ s, (1 + u * w i) := by ring
    rw [this]
    exact dvd_add h1 ((h2.mul_left u).mul_right _)

lemma LA (q u : R) (s : Finset ι) (w : ι → R) (hw : ∀ i ∈ s, q ∣ w i) :
    q ^ 2 ∣ ∏ i ∈ s, (1 + u * w i) - 1 - u * ∑ i ∈ s, w i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have h1 := ih (fun i hi => hw i (mem_insert_of_mem hi))
    have h2 := hw a (mem_insert_self a s)
    have h0 := L0 q u s w (fun i hi => hw i (mem_insert_of_mem hi))
    have : (1 + u * w a) * ∏ i ∈ s, (1 + u * w i) - 1 - u * (w a + ∑ i ∈ s, w i) =
        (∏ i ∈ s, (1 + u * w i) - 1 - u * ∑ i ∈ s, w i)
          + u * (w a * (∏ i ∈ s, (1 + u * w i) - 1)) := by ring
    rw [this]
    exact dvd_add h1 (by rw [pow_two]; exact (mul_dvd_mul h2 h0).mul_left u)

lemma LB (q u : R) (s : Finset ι) (w : ι → R) (hw : ∀ i ∈ s, q ∣ w i) :
    q ^ 3 ∣ 2 * (∏ i ∈ s, (1 + u * w i) - 1 - u * ∑ i ∈ s, w i)
      - u ^ 2 * ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, (w i) ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, sum_insert ha]
    have h1 := ih (fun i hi => hw i (mem_insert_of_mem hi))
    have h2 := hw a (mem_insert_self a s)
    have hA := LA q u s w (fun i hi => hw i (mem_insert_of_mem hi))
    have : 2 * ((1 + u * w a) * ∏ i ∈ s, (1 + u * w i) - 1 - u * (w a + ∑ i ∈ s, w i))
          - u ^ 2 * ((w a + ∑ i ∈ s, w i) ^ 2 - (w a ^ 2 + ∑ i ∈ s, w i ^ 2)) =
        (2 * (∏ i ∈ s, (1 + u * w i) - 1 - u * ∑ i ∈ s, w i)
          - u ^ 2 * ((∑ i ∈ s, w i) ^ 2 - ∑ i ∈ s, (w i) ^ 2))
          + 2 * u * (w a * (∏ i ∈ s, (1 + u * w i) - 1 - u * ∑ i ∈ s, w i)) := by ring
    rw [this]
    exact dvd_add h1 (by rw [pow_succ, mul_comm (q ^ 2) q]; exact (mul_dvd_mul h2 hA).mul_left _)

end expansion

section padic
variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def y (p : ℕ) [Fact p.Prime] (j : ℕ) : ℤ_[p] := Ring.inverse (j : ℤ_[p])

lemma isUnit_natCast_iff {j : ℕ} : IsUnit (j : ℤ_[p]) ↔ ¬ p ∣ j := by
  rw [PadicInt.isUnit_iff]
  have hcast : ((j : ℤ) : ℤ_[p]) = (j : ℤ_[p]) := Int.cast_natCast j
  constructor
  · intro h hdvd
    have := (PadicInt.norm_int_lt_one_iff_dvd (j : ℤ)).mpr (Int.natCast_dvd_natCast.mpr hdvd)
    rw [hcast] at this
    linarith
  · intro h
    have h1 := PadicInt.norm_le_one (j : ℤ_[p])
    have h2 : ¬ ‖(j : ℤ_[p])‖ < 1 := by
      intro hlt
      rw [← hcast] at hlt
      have := (PadicInt.norm_int_lt_one_iff_dvd (j : ℤ)).mp hlt
      exact h (Int.natCast_dvd_natCast.mp this)
    exact le_antisymm h1 (not_lt.mp h2)

lemma mul_y {j : ℕ} (h : ¬ p ∣ j) : (j : ℤ_[p]) * y p j = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_natCast_iff.mpr h)

lemma dvd_iff_toZMod {x : ℤ_[p]} : (p : ℤ_[p]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker]

lemma toZMod_y (j : ℕ) : PadicInt.toZMod (y p j) = ((j : ZMod p))⁻¹ := by
  by_cases h : p ∣ j
  · have : ¬ IsUnit (j : ℤ_[p]) := fun hu => (isUnit_natCast_iff.mp hu) h
    rw [y, Ring.inverse_non_unit _ this, map_zero]
    have : (j : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff j p).mpr h
    rw [this, inv_zero]
  · have h1 := congrArg PadicInt.toZMod (mul_y (p := p) h)
    rw [map_mul, map_natCast, map_one] at h1
    exact eq_inv_of_mul_eq_one_right h1

lemma isUnit_two (hp2 : 2 < p) : IsUnit (2 : ℤ_[p]) := by
  have : ((2 : ℕ) : ℤ_[p]) = 2 := by norm_num
  rw [← this, isUnit_natCast_iff]
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h
  omega

lemma isUnit_four (hp2 : 2 < p) : IsUnit (4 : ℤ_[p]) := by
  have : (4 : ℤ_[p]) = 2 * 2 := by norm_num
  rw [this]
  exact (isUnit_two hp2).mul (isUnit_two hp2)

lemma sum_range_natCast_zmod (hp2 : 2 < p) : ∑ t ∈ range p, (t : ZMod p) = 0 := by
  have h := Finset.sum_range_id_mul_two p
  have h2 : ((∑ t ∈ range p, t : ℕ) : ZMod p) * 2 = (p : ZMod p) * ((p - 1 : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h
  rw [ZMod.natCast_self, zero_mul, Nat.cast_sum] at h2
  have h3 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    have := (ZMod.natCast_eq_zero_iff 2 p).mp h0'
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this
    omega
  exact (mul_eq_zero.mp h2).resolve_right h3

end padic

end A357569

namespace A357569
section main
variable {p : ℕ} [hp : Fact p.Prime]

lemma prod_J_reflect {M : Type*} [CommMonoid M] (f : ℕ → M) {N : ℕ} (hN : p ∣ N) :
    ∏ j ∈ J p N, f j = ∏ j ∈ J p N, f (N - j) := by
  have key : ∀ a ∈ J p N, N - a ∈ J p N := by
    intro a ha
    rw [mem_J] at ha ⊢
    have ha0 : a ≠ 0 := fun h => ha.2 (h ▸ dvd_zero p)
    refine ⟨by omega, fun h => ha.2 ?_⟩
    have := Nat.dvd_sub hN h
    rwa [Nat.sub_sub_self ha.1.le] at this
  apply prod_nbij' (fun j => N - j) (fun j => N - j) key key
  · intro a ha; rw [mem_J] at ha; exact Nat.sub_sub_self ha.1.le
  · intro a ha; rw [mem_J] at ha; exact Nat.sub_sub_self ha.1.le
  · intro a ha; rw [mem_J] at ha; rw [Nat.sub_sub_self ha.1.le]

lemma not_dvd_sub {N j : ℕ} (hN : p ∣ N) (hj : j ∈ J p N) : ¬ p ∣ N - j := by
  rw [mem_J] at hj
  intro h
  have := Nat.dvd_sub hN h
  rw [Nat.sub_sub_self hj.1.le] at this
  exact hj.2 this

lemma pair_y {N j : ℕ} (hN : p ∣ N) (hj : j ∈ J p N) :
    y p j + y p (N - j) = (N : ℤ_[p]) * y p j * y p (N - j) := by
  have e2 := mul_y (p := p) (not_dvd_sub hN hj)
  rw [mem_J] at hj
  have e1 := mul_y (p := p) hj.2
  rw [Nat.cast_sub hj.1.le] at e2
  linear_combination (-(y p j)) * e2 + (-(y p (N - j))) * e1

lemma pair_y_mul {N j : ℕ} (hN : p ∣ N) (hj : j ∈ J p N) :
    y p j * y p (N - j) = -(y p j)^2 + (N : ℤ_[p]) * (y p j)^2 * y p (N - j) := by
  have := pair_y hN hj
  linear_combination (y p j) * this

variable (p) in
noncomputable def z (v j : ℕ) : ℤ_[p] := ((p:ℤ_[p])^(v+1))^2 * y p j * y p (p^(v+1) - j)
variable (p) in
noncomputable def F (v : ℕ) (t : ℤ_[p]) : ℤ_[p] :=
  ∏ j ∈ J p (p^(v+1)), (1 + t * (p:ℤ_[p])^(v+1) * y p j)
variable (p) in
noncomputable def G (v : ℕ) (u : ℤ_[p]) : ℤ_[p] := ∏ j ∈ J p (p^(v+1)), (1 + u * z p v j)
variable (p) in
noncomputable def Z1 (v : ℕ) : ℤ_[p] := ∑ j ∈ J p (p^(v+1)), z p v j
variable (p) in
noncomputable def W (v : ℕ) : ℤ_[p] := ∑ j ∈ J p (p^(v+1)), (z p v j)^2
variable (p) in
noncomputable def P2 (v : ℕ) : ℤ_[p] := ∑ j ∈ J p (p^(v+1)), (y p j)^2
variable (p) in
noncomputable def U (v : ℕ) : ℤ_[p] := ∑ j ∈ J p (p^(v+1)), (y p j * y p (p^(v+1) - j))^2
variable (p) in
noncomputable def b2 (v : ℕ) : ℤ_[p] := ((2 * p^v).choose (p^v) : ℤ_[p])
variable (p) in
noncomputable def b3 (v : ℕ) : ℤ_[p] := ((3 * p^v).choose (p^v) : ℤ_[p])

omit hp in
lemma dvd_N (v : ℕ) : p ∣ p^(v+1) := dvd_pow_self p (Nat.succ_ne_zero v)

lemma F_mul_F (v : ℕ) (t : ℤ_[p]) : F p v t * F p v t = G p v (t * t + t) := by
  have hN := dvd_N (p := p) v
  have h1 : F p v t = ∏ j ∈ J p (p^(v+1)), (1 + t * (p:ℤ_[p])^(v+1) * y p (p^(v+1) - j)) :=
    prod_J_reflect (fun j => 1 + t * (p:ℤ_[p])^(v+1) * y p j) hN
  calc F p v t * F p v t
      = (∏ j ∈ J p (p^(v+1)), (1 + t * (p:ℤ_[p])^(v+1) * y p j)) *
          ∏ j ∈ J p (p^(v+1)), (1 + t * (p:ℤ_[p])^(v+1) * y p (p^(v+1) - j)) := by
        rw [← h1]; rfl
    _ = _ := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun j hj => ?_
      have := pair_y hN hj
      push_cast at this
      rw [z]
      linear_combination (t * (p:ℤ_[p])^(v+1)) * this

lemma choose_eq_mul_F (v t : ℕ) :
    ((t * p^(v+1) + p^(v+1)).choose (p^(v+1)) : ℤ_[p]) =
      ((t * p^v + p^v).choose (p^v) : ℤ_[p]) * F p v t := by
  have h := choose_mul_D p (t * p^v) (p^v) hp.out.pos
  have hN : p * p^v = p^(v+1) := by ring
  have hc : p * (t * p^v) = t * p^(v+1) := by ring
  rw [hN, hc] at h
  have h' := congrArg (Nat.cast : ℕ → ℤ_[p]) h
  push_cast at h'
  have hD : (∏ j ∈ J p (p^(v+1)), (j : ℤ_[p])) * ∏ j ∈ J p (p^(v+1)), y p j = 1 := by
    rw [← prod_mul_distrib]; exact prod_eq_one fun j hj => mul_y (mem_J.mp hj).2
  have hE : ∏ j ∈ J p (p^(v+1)), ((t:ℤ_[p]) * (p:ℤ_[p])^(v+1) + j) =
      (∏ j ∈ J p (p^(v+1)), (j : ℤ_[p])) * F p v t := by
    rw [F, ← prod_mul_distrib]
    refine prod_congr rfl fun j hj => ?_
    have := mul_y (p := p) (mem_J.mp hj).2
    linear_combination (-(t * (p:ℤ_[p])^(v+1))) * this
  rw [hE] at h'
  calc ((t * p^(v+1) + p^(v+1)).choose (p^(v+1)) : ℤ_[p])
      = ((t * p^(v+1) + p^(v+1)).choose (p^(v+1)) : ℤ_[p]) *
          ((∏ j ∈ J p (p^(v+1)), (j : ℤ_[p])) * ∏ j ∈ J p (p^(v+1)), y p j) := by rw [hD, mul_one]
    _ = ((t * p^(v+1) + p^(v+1)).choose (p^(v+1)) : ℤ_[p]) * (∏ j ∈ J p (p^(v+1)), (j : ℤ_[p]))
          * ∏ j ∈ J p (p^(v+1)), y p j := by ring
    _ = ((t * p^v + p^v).choose (p^v) : ℤ_[p]) * ((∏ j ∈ J p (p^(v+1)), (j : ℤ_[p])) * F p v t)
          * ∏ j ∈ J p (p^(v+1)), y p j := by rw [h']
    _ = ((t * p^v + p^v).choose (p^v) : ℤ_[p]) * F p v t *
          ((∏ j ∈ J p (p^(v+1)), (j : ℤ_[p])) * ∏ j ∈ J p (p^(v+1)), y p j) := by ring
    _ = _ := by rw [hD, mul_one]

lemma b2_succ (v : ℕ) : b2 p (v+1) = b2 p v * F p v 1 := by
  have := choose_eq_mul_F (p := p) v 1
  simp only [one_mul, Nat.cast_one] at this
  unfold b2
  rw [show 2 * p^(v+1) = p^(v+1) + p^(v+1) by ring, show 2 * p^v = p^v + p^v by ring]
  exact this

lemma b3_succ (v : ℕ) : b3 p (v+1) = b3 p v * F p v 2 := by
  have := choose_eq_mul_F (p := p) v 2
  unfold b3
  rw [show 3 * p^(v+1) = 2 * p^(v+1) + p^(v+1) by ring, show 3 * p^v = 2 * p^v + p^v by ring]
  exact_mod_cast this

lemma P2_step (v w : ℕ) (hw : w ≤ 1) (hp2 : 2 < p)
    (ih : (p:ℤ_[p])^(v+w) ∣ P2 p v) : (p:ℤ_[p])^(v+1+w) ∣ P2 p (v+1) := by
  have hpm : p ∣ p^(v+1) := dvd_N v
  have hm' : p^(v+1+1) = p^(v+1) * p := by ring
  unfold P2
  rw [hm', sum_J_mul _ hpm, sum_comm]
  have key : ∀ i ∈ J p (p^(v+1)), ∑ t ∈ range p, (y p (p^(v+1)*t+i))^2 =
      (p:ℤ_[p]) * (y p i)^2 - ((p^(v+1) : ℕ):ℤ_[p]) * ∑ t ∈ range p, (t:ℤ_[p]) *
        (y p i * y p (p^(v+1)*t+i) * (y p (p^(v+1)*t+i) + y p i)) := by
    intro i hi
    rw [mem_J] at hi
    have e1 := mul_y (p := p) hi.2
    have hp' : (p:ℤ_[p]) * (y p i)^2 = ∑ t ∈ range p, (y p i)^2 := by
      rw [sum_const, card_range, nsmul_eq_mul]
    rw [hp', mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    have hnd : ¬ p ∣ p^(v+1) * t + i :=
      fun h => hi.2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left hpm t)).mp h)
    have e2 := mul_y (p := p) hnd
    push_cast at e2 ⊢
    linear_combination (-(y p (p^(v+1)*t+i) + y p i) * y p (p^(v+1)*t+i)) * e1 +
      ((y p (p^(v+1)*t+i) + y p i) * y p i) * e2
  rw [sum_congr rfl key, sum_sub_distrib, ← mul_sum, ← mul_sum]
  apply dvd_sub
  · rw [show (p:ℤ_[p])^(v+1+w) = p * p^(v+w) by ring]
    exact mul_dvd_mul_left _ ih
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hw with rfl | rfl
    · rw [add_zero]; push_cast; exact dvd_mul_right _ _
    · push_cast
      rw [show (p:ℤ_[p])^(v+1+1) = p^(v+1) * p by ring]
      apply mul_dvd_mul_left
      rw [dvd_iff_toZMod, map_sum]
      apply sum_eq_zero
      intro i _
      rw [map_sum]
      have hm0 : ((p : ZMod p))^(v+1) = 0 := by
        rw [ZMod.natCast_self, zero_pow (Nat.succ_ne_zero v)]
      have : ∀ t ∈ range p, PadicInt.toZMod ((t:ℤ_[p]) * (y p i * y p (p^(v+1)*t+i) *
          (y p (p^(v+1)*t+i) + y p i))) =
          (t : ZMod p) * ((i : ZMod p)⁻¹ * (i:ZMod p)⁻¹ * ((i:ZMod p)⁻¹ + (i:ZMod p)⁻¹)) := by
        intro t _
        simp only [map_mul, map_add, map_natCast, toZMod_y, Nat.cast_add, Nat.cast_mul,
          Nat.cast_pow, hm0, zero_mul, zero_add]
      rw [sum_congr rfl this, ← sum_mul, sum_range_natCast_zmod hp2, zero_mul]

lemma P2_base (hp5 : 5 ≤ p) : (p:ℤ_[p]) ∣ P2 p 0 := by
  unfold P2
  rw [dvd_iff_toZMod, map_sum]
  simp only [toZMod_y, map_pow, zero_add, pow_one]
  have h1 : ∑ j ∈ J p p, ((j : ZMod p)⁻¹)^2 = ∑ j ∈ range p, ((j : ZMod p)⁻¹)^2 := by
    unfold J; rw [sum_filter]; refine sum_congr rfl fun j hj => ?_
    by_cases h : p ∣ j
    · have : j = 0 := Nat.eq_zero_of_dvd_of_lt h (mem_range.mp hj)
      subst this; simp
    · simp [h]
  have h2 : ∑ j ∈ range p, ((j : ZMod p)⁻¹)^2 = ∑ x : ZMod p, (x⁻¹)^2 := by
    apply sum_nbij' (fun j : ℕ => (j : ZMod p)) (fun x => x.val)
    · intros; exact mem_univ _
    · intro x _; exact mem_range.mpr (ZMod.val_lt x)
    · intro j hj; exact ZMod.val_natCast_of_lt (mem_range.mp hj)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intros; rfl
  have h3 : ∑ x : ZMod p, (x⁻¹)^2 = ∑ x : ZMod p, x^2 := by
    have := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x => x^2)
    simpa only [Equiv.inv_apply] using this
  rw [h1, h2, h3]
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [ZMod.card]; omega

lemma P2_dvd (w : ℕ) (hw : w ≤ 1) (hp2 : 2 < p) (hbase : (p:ℤ_[p])^w ∣ P2 p 0) (v : ℕ) :
    (p:ℤ_[p])^(v+w) ∣ P2 p v := by
  induction v with
  | zero => simpa using hbase
  | succ v ih => exact P2_step v w hw hp2 ih

lemma P4_dvd (v : ℕ) (hv : 1 ≤ v) : (p:ℤ_[p]) ∣ ∑ j ∈ J p (p^(v+1)), (y p j)^4 := by
  rw [dvd_iff_toZMod, map_sum]
  have hpm : p ∣ p^v := dvd_pow_self p (by omega)
  rw [pow_succ, sum_J_mul _ hpm]
  simp only [map_pow, toZMod_y, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    ZMod.natCast_self, zero_pow (by omega : v ≠ 0), zero_mul, zero_add]
  rw [sum_const, card_range, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

lemma U_dvd (v : ℕ) (hv : 1 ≤ v) : (p:ℤ_[p]) ∣ U p v := by
  have h := P4_dvd (p := p) v hv
  unfold U
  rw [dvd_iff_toZMod, map_sum] at h ⊢
  rw [← h]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_J] at hj
  have hN0 : ((p^(v+1) : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_pow, ZMod.natCast_self, zero_pow (Nat.succ_ne_zero v)]
  rw [map_pow, map_pow, map_mul, toZMod_y, toZMod_y, Nat.cast_sub hj.1.le, hN0, zero_sub, inv_neg]
  ring

lemma Z1_eq (v : ℕ) : Z1 p v = ((p:ℤ_[p])^(v+1))^2 *
    (-P2 p v + (p:ℤ_[p])^(v+1) * ∑ j ∈ J p (p^(v+1)), (y p j)^2 * y p (p^(v+1) - j)) := by
  unfold Z1 P2
  rw [mul_sum, ← sum_neg_distrib, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have := pair_y_mul (dvd_N v) hj
  push_cast at this
  rw [z]
  linear_combination ((p:ℤ_[p])^(v+1))^2 * this

lemma Z1_dvd (v w : ℕ) (hw : w ≤ 1) (hP2 : (p:ℤ_[p])^(v+w) ∣ P2 p v) :
    (p:ℤ_[p])^(3*v+2+w) ∣ Z1 p v := by
  rw [Z1_eq, show 3*v+2+w = 2*(v+1) + (v+w) by ring, pow_add,
    show ((p:ℤ_[p])^(v+1))^2 = (p:ℤ_[p])^(2*(v+1)) by ring]
  apply mul_dvd_mul (dvd_refl _)
  apply dvd_add (dvd_neg.mpr hP2)
  exact (pow_dvd_pow _ (by omega : v + w ≤ v + 1)).mul_right _

lemma W_eq (v : ℕ) : W p v = ((p:ℤ_[p])^(v+1))^4 * U p v := by
  unfold W U
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [z]; ring

lemma W_dvd (v : ℕ) (hv : 1 ≤ v) : (p:ℤ_[p])^(4*v+5) ∣ W p v := by
  rw [W_eq, show 4*v+5 = 4*(v+1) + 1 by ring, pow_add, pow_one,
    show ((p:ℤ_[p])^(v+1))^4 = (p:ℤ_[p])^(4*(v+1)) by ring]
  exact mul_dvd_mul (dvd_refl _) (U_dvd v hv)

lemma W_dvd' (v : ℕ) : (p:ℤ_[p])^(4*(v+1)) ∣ W p v := by
  rw [W_eq, show ((p:ℤ_[p])^(v+1))^4 = (p:ℤ_[p])^(4*(v+1)) by ring]
  exact dvd_mul_right _ _

lemma z_dvd (v j : ℕ) : (p:ℤ_[p])^(2*(v+1)) ∣ z p v j := by
  rw [z, show (p:ℤ_[p])^(2*(v+1)) = ((p:ℤ_[p])^(v+1))^2 by ring]
  exact (dvd_mul_right _ _).mul_right _

lemma G_sub_one_dvd (v : ℕ) (u : ℤ_[p]) : (p:ℤ_[p])^(2*(v+1)) ∣ G p v u - 1 :=
  L0 _ u _ _ (fun j _ => z_dvd v j)

lemma rho_dvd (v : ℕ) (u : ℤ_[p]) :
    (p:ℤ_[p])^(6*(v+1)) ∣ 2 * (G p v u - 1 - u * Z1 p v) - u^2 * ((Z1 p v)^2 - W p v) := by
  have := LB ((p:ℤ_[p])^(2*(v+1))) u (J p (p^(v+1))) (z p v) (fun j _ => z_dvd v j)
  rw [← pow_mul] at this
  rw [show 6*(v+1) = 2*(v+1)*3 by ring]
  exact this

lemma F_sub_one_dvd_N (v : ℕ) (t : ℤ_[p]) : (p:ℤ_[p])^(v+1) ∣ F p v t - 1 := by
  have := L0 ((p:ℤ_[p])^(v+1)) t (J p (p^(v+1))) (fun j => (p:ℤ_[p])^(v+1) * y p j)
    (fun j _ => dvd_mul_right _ _)
  unfold F
  simpa only [mul_assoc] using this

lemma F_sub_one_dvd (v w : ℕ) (hw : w ≤ 1) (hp2 : 2 < p) (hP2 : (p:ℤ_[p])^(v+w) ∣ P2 p v)
    (t : ℤ_[p]) : (p:ℤ_[p])^(3*v+2+w) ∣ F p v t - 1 := by
  have hG : F p v t * F p v t = G p v (t*t+t) := F_mul_F v t
  have hZ1 := Z1_dvd v w hw hP2
  have hW := W_dvd' (p := p) v
  have hρ := rho_dvd v (t*t+t)
  have hmain : (p:ℤ_[p])^(3*v+2+w) ∣ 2 * (2 * (F p v t - 1) + (F p v t - 1)^2) := by
    have : 2 * (2 * (F p v t - 1) + (F p v t - 1)^2) =
        2 * (t*t+t) * Z1 p v + (t*t+t)^2 * ((Z1 p v)^2 - W p v) +
        (2 * (G p v (t*t+t) - 1 - (t*t+t) * Z1 p v) - (t*t+t)^2 * ((Z1 p v)^2 - W p v)) := by
      linear_combination 2 * hG
    rw [this]
    refine dvd_add (dvd_add (hZ1.mul_left _) ?_) ?_
    · apply Dvd.dvd.mul_left
      apply dvd_sub
      · exact dvd_pow hZ1 two_ne_zero
      · exact dvd_trans (pow_dvd_pow _ (by omega)) hW
    · exact dvd_trans (pow_dvd_pow _ (by omega)) hρ
  have hε1 : (p:ℤ_[p])^(v+1) ∣ F p v t - 1 := F_sub_one_dvd_N v t
  have h4 := isUnit_four hp2
  have hε2 : (p:ℤ_[p])^(2*(v+1)) ∣ F p v t - 1 := by
    have : (4:ℤ_[p]) * (F p v t - 1) =
        2 * (2 * (F p v t - 1) + (F p v t - 1)^2) - 2 * (F p v t - 1)^2 := by ring
    rw [← h4.dvd_mul_left, this]
    apply dvd_sub
    · exact dvd_trans (pow_dvd_pow _ (by omega)) hmain
    · rw [mul_comm 2 (v+1), pow_mul]
      exact (pow_dvd_pow_of_dvd hε1 2).mul_left _
  have : (4:ℤ_[p]) * (F p v t - 1) =
      2 * (2 * (F p v t - 1) + (F p v t - 1)^2) - 2 * (F p v t - 1)^2 := by ring
  rw [← h4.dvd_mul_left, this]
  apply dvd_sub hmain
  have := pow_dvd_pow_of_dvd hε2 2
  rw [← pow_mul] at this
  exact (dvd_trans (pow_dvd_pow _ (by omega)) this).mul_left _

end main
end A357569

namespace A357569
section final
variable {p : ℕ} [hp : Fact p.Prime]

lemma b_mod_five (hp5 : 5 ≤ p) (v : ℕ) :
    (p:ℤ_[p])^3 ∣ b2 p v - 2 ∧ (p:ℤ_[p])^3 ∣ b3 p v - 3 := by
  have hP2 := P2_dvd (p := p) 1 le_rfl (by omega) (by simpa using P2_base hp5)
  induction v with
  | zero => norm_num [b2, b3, Nat.choose]
  | succ v ih =>
    rw [b2_succ, b3_succ]
    have h1 := F_sub_one_dvd v 1 le_rfl (by omega) (hP2 v) 1
    have h2 := F_sub_one_dvd v 1 le_rfl (by omega) (hP2 v) 2
    have h3 : (p:ℤ_[p])^3 ∣ (p:ℤ_[p])^(3*v+2+1) := pow_dvd_pow _ (by omega)
    constructor
    · have : b2 p v * F p v 1 - 2 = (b2 p v - 2) + b2 p v * (F p v 1 - 1) := by ring
      rw [this]; exact dvd_add ih.1 ((dvd_trans h3 h1).mul_left _)
    · have : b3 p v * F p v 2 - 3 = (b3 p v - 3) + b3 p v * (F p v 2 - 1) := by ring
      rw [this]; exact dvd_add ih.2 ((dvd_trans h3 h2).mul_left _)

lemma b_mod_three (hp3 : p = 3) (v : ℕ) :
    (p:ℤ_[p]) ∣ b2 p v - 2 ∧ (p:ℤ_[p])^2 ∣ b3 p v - 3 := by
  induction v with
  | zero => norm_num [b2, b3, Nat.choose]
  | succ v ih =>
    rw [b2_succ, b3_succ]
    have h1 := F_sub_one_dvd_N (p := p) v 1
    have h2 := F_sub_one_dvd_N (p := p) v 2
    have hp1 : (p:ℤ_[p]) ∣ (p:ℤ_[p])^(v+1) := dvd_pow_self _ (Nat.succ_ne_zero v)
    constructor
    · have : b2 p v * F p v 1 - 2 = (b2 p v - 2) + b2 p v * (F p v 1 - 1) := by ring
      rw [this]; exact dvd_add ih.1 ((dvd_trans hp1 h1).mul_left _)
    · have : b3 p v * F p v 2 - 3 = (b3 p v - 3) + b3 p v * (F p v 2 - 1) := by ring
      rw [this]
      refine dvd_add ih.2 ?_
      have hb3 : (p:ℤ_[p]) ∣ b3 p v := by
        have : b3 p v = (b3 p v - 3) + 3 := by ring
        rw [this]
        refine dvd_add (dvd_trans (dvd_pow_self _ two_ne_zero) ih.2) ?_
        subst hp3; norm_num
      rw [pow_two]; exact mul_dvd_mul hb3 (dvd_trans hp1 h2)

lemma main_dvd (v : ℕ) (hv : 1 ≤ v) (w : ℕ) (hw : w ≤ 1) (hp2 : 2 < p)
    (hP2 : (p:ℤ_[p])^(v+w) ∣ P2 p v)
    (hb : (p:ℤ_[p])^(4 - w) ∣ 12 * (2 * (b3 p v)^2 - 9 * b2 p v)) :
    (p:ℤ_[p])^(3*v+6) ∣ (b3 p (v+1))^2 - 27 * b2 p (v+1) - ((b3 p v)^2 - 27 * b2 p v) := by
  have hG2 : F p v 1 * F p v 1 = G p v 2 := by
    have := F_mul_F (p := p) v 1; rwa [show (1:ℤ_[p]) * 1 + 1 = 2 by norm_num] at this
  have hG6 : F p v 2 * F p v 2 = G p v 6 := by
    have := F_mul_F (p := p) v 2; rwa [show (2:ℤ_[p]) * 2 + 2 = 6 by norm_num] at this
  rw [b2_succ, b3_succ]
  have hρ6 := rho_dvd (p := p) v 6
  have hρ2 := rho_dvd (p := p) v 2
  have hZ1 := Z1_dvd v w hw hP2
  have hW := W_dvd (p := p) v hv
  have hε := F_sub_one_dvd v w hw hp2 hP2 1
  have key : 4 * ((b3 p v * F p v 2)^2 - 27 * (b2 p v * F p v 1) - ((b3 p v)^2 - 27 * b2 p v)) =
      Z1 p v * (12 * (2 * (b3 p v)^2 - 9 * b2 p v))
      + ((Z1 p v)^2 - W p v) * (72 * (b3 p v)^2 - 108 * b2 p v)
      + 2 * (b3 p v)^2 * (2 * (G p v 6 - 1 - 6 * Z1 p v) - 6^2 * ((Z1 p v)^2 - W p v))
      - 27 * b2 p v * (2 * (G p v 2 - 1 - 2 * Z1 p v) - 2^2 * ((Z1 p v)^2 - W p v))
      + 54 * b2 p v * (F p v 1 - 1)^2 := by
    linear_combination (4 * (b3 p v)^2) * hG6 - (54 * b2 p v) * hG2
  rw [← (isUnit_four hp2).dvd_mul_left, key]
  refine dvd_add (dvd_sub (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_
  · rw [show 3*v+6 = (3*v+2+w) + (4-w) by omega, pow_add]
    exact mul_dvd_mul hZ1 hb
  · apply Dvd.dvd.mul_right
    apply dvd_sub
    · have := pow_dvd_pow_of_dvd hZ1 2
      rw [← pow_mul] at this
      exact dvd_trans (pow_dvd_pow _ (by omega)) this
    · exact dvd_trans (pow_dvd_pow _ (by omega)) hW
  · exact (dvd_trans (pow_dvd_pow _ (by omega)) hρ6).mul_left _
  · exact (dvd_trans (pow_dvd_pow _ (by omega)) hρ2).mul_left _
  · have := pow_dvd_pow_of_dvd hε 2
    rw [← pow_mul] at this
    exact (dvd_trans (pow_dvd_pow _ (by omega)) this).mul_left _

lemma main_dvd' (v : ℕ) (hv : 1 ≤ v) (hp3 : 3 ≤ p) :
    (p:ℤ_[p])^(3*v+6) ∣ (b3 p (v+1))^2 - 27 * b2 p (v+1) - ((b3 p v)^2 - 27 * b2 p v) := by
  have hp2 : 2 < p := by omega
  rcases Nat.lt_or_ge p 5 with h5 | h5
  · -- p = 3 (p = 4 is not prime)
    have hp3' : p = 3 := by
      rcases (show p = 3 ∨ p = 4 by omega) with h | h
      · exact h
      · exfalso; rw [h] at hp; exact absurd hp.out (by decide)
    have hb := b_mod_three hp3' v
    obtain ⟨k, hk⟩ := hb.2
    obtain ⟨m, hm⟩ := hb.1
    apply main_dvd v hv 0 (Nat.zero_le _) hp2 (by simpa using P2_dvd 0 (Nat.zero_le _) hp2 (by simp) v)
    refine ⟨4 * (4 * k + 6 * k^2 - m), ?_⟩
    subst hp3'
    linear_combination (24 * (b3 3 v + 3 + 9 * k)) * hk - 108 * hm
  · have hb := b_mod_five h5 v
    obtain ⟨k, hk⟩ := hb.2
    obtain ⟨m, hm⟩ := hb.1
    apply main_dvd v hv 1 le_rfl hp2 (P2_dvd 1 le_rfl hp2 (by simpa using P2_base h5) v)
    refine ⟨12 * (2 * k * (b3 p v + 3) - 9 * m), ?_⟩
    linear_combination (24 * (b3 p v + 3)) * hk - 108 * hm

end final
end A357569


open Nat

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by
  haveI := Fact.mk hp
  obtain ⟨v, rfl⟩ : ∃ v, r = v + 1 := ⟨r - 1, by omega⟩
  have hv : 1 ≤ v := by omega
  simp only [Nat.add_sub_cancel]
  rw [Int.modEq_iff_dvd]
  have key : (p:ℤ_[p])^(3*v+6) ∣ ((a (p^v) - a (p^(v+1)) : ℤ) : ℤ_[p]) := by
    have h := A357569.main_dvd' (p := p) v hv hp3
    rw [← dvd_neg] at h
    convert h using 1
    simp only [a, A357569.b2, A357569.b3, Int.ofNat_eq_natCast]
    push_cast
    ring
  have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ (3*v+6)).mpr (Ideal.mem_span_singleton.mpr key)
  have h2 := PadicInt.norm_int_le_pow_iff_dvd.mp h1
  rw [show 3 * (v + 1) + 3 = 3 * v + 6 by ring]
  exact h2

theorem oeis_357569_conjecture_0.disproof : ¬ (type_of% @oeis_357569_conjecture_0) := sorry
