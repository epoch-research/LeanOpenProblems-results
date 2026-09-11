import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A357674: $a(n) = \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k} \right)^4 \cdot \left( \sum_{k = 0}^{2n} \binom{n+k-1}{k}^2 \right)^3$.

The terms $\sum_{k = 0}^{2n} \binom{n+k-1}{k}$ and $\sum_{k = 0}^{2n} \binom{n+k-1}{k}^2$ are the summations required.
For $n \ge 1$, the first sum is equal to $\binom{3n}{n}$. We keep the summation structure for fidelity to the OEIS definition, using Finset.sum and Nat.choose.
-/
def A357674 (n : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (2 * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ 4 * S2 ^ 3

/--
The general sequence $u(n, m)$ from conjecture 3.
$u(n, m) = \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k} \right)^{2m} \cdot \left( \sum_{k = 0}^{m*n} \binom{n+k-1}{k}^2 \right)^{m+1}$.
Note that `A357674 n = u_A357674 n 2`.
-/
def u_A357674 (n m : ℕ) : ℕ :=
  let S1 : ℕ := Finset.sum (range (m * n + 1)) (fun k => (n + k - 1).choose k)
  let S2 : ℕ := Finset.sum (range (m * n + 1)) (fun k => ((n + k - 1).choose k) ^ 2)
  S1 ^ (2 * m) * S2 ^ (m + 1)

/-
The auxiliary lemmas below work in arbitrary commutative rings where possible.
For primes p ≥ 7, put t = p in ZMod (p^5) and d = t^2 ∑_{i=1}^{p-1} i⁻².
The harmonic identities establish d² = 0 and the two evaluations
  S1 = 3(1 - 3d),   S2 = 3 + 12d.
These imply S1^4 S2^3 = 3^7. The primes 3 and 5 are checked separately.
-/

namespace A357674Proof

variable {R : Type*} [CommRing R]

def H (u : ℕ → R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range n, u i * f (i+1)

def T (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range n, (-1 : R)^i * (n.choose (i+1) : R) * f (i+1)

lemma sum_choose_range (n k : ℕ) :
    (∑ i ∈ range n, i.choose k) = n.choose (k+1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_range_succ, ih, Nat.choose_succ_succ, Nat.succ_eq_add_one]; omega

lemma sum_choose_Ico (n k : ℕ) (h : k ≤ n) :
    (∑ i ∈ Ico k n, i.choose k) = n.choose (k+1) := by
  have := sum_range_add_sum_Ico (fun i => i.choose k) h
  simpa [sum_choose_range] using this

lemma triangle_sum (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, ∑ j ∈ range (i+1), f i j) =
      ∑ j ∈ range n, ∑ i ∈ Ico j n, f i j := by
  simpa only [Nat.Ico_zero_eq_range] using (sum_Ico_Ico_comm 0 n (fun j i => f i j)).symm

lemma alternating_tail (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    (∑ i ∈ Ico j n, (-1 : R)^i * (n.choose (i+1) : R)) =
      (-1 : R)^j * ((n-1).choose j : R) := by
  have heq (i : ℕ) :
      (-1 : R)^i * (n.choose (i+1) : R) =
      (-1 : R)^i * ((n-1).choose i : R) -
      (-1 : R)^(i+1) * ((n-1).choose (i+1) : R) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, Nat.choose_succ_succ]
    push_cast
    rw [pow_succ]
    ring
  simp_rw [heq]
  have ht := sum_Ico_sub (fun i => (-1 : R)^i * ((n-1).choose i : R)) hj
  simp only [sum_sub_distrib, Nat.choose_eq_zero_of_lt (show n-1 < n by omega),
    Nat.cast_zero, mul_zero, zero_sub] at ht ⊢
  linear_combination -ht

lemma choose_fraction (u : ℕ → R) (i j : ℕ)
    (hi : (i+1 : R) * u i = 1) (hj : (j+1 : R) * u j = 1) :
    u i * ((i+1).choose (j+1) : R) = u j * (i.choose j : R) := by
  have hc : (i+1 : R) * (i.choose j : R) =
      ((i+1).choose (j+1) : R) * (j+1 : R) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using congrArg (fun k : ℕ => (k : R)) (Nat.add_one_mul_choose_eq i j)
  linear_combination -(u i*u j)*hc +
    (u j * (i.choose j : R))*hi - (u i * ((i+1).choose (j+1) : R))*hj

lemma T_H (u f : ℕ → R) (n : ℕ) (hn : 0 < n)
    (hu : ∀ i < n, (i+1 : R) * u i = 1) :
    T (H u f) n = u (n-1) * T f n := by
  unfold T H
  simp_rw [mul_sum]
  rw [triangle_sum]
  simp_rw [show ∀ i j, (-1 : R)^i * (n.choose (i+1) : R) * (u j * f (j+1)) =
    u j * f (j+1) * ((-1 : R)^i * (n.choose (i+1) : R)) by intros; ring]
  simp_rw [← mul_sum]
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn := mem_range.mp hj
  rw [alternating_tail n j hn (by omega)]
  have hc := choose_fraction u (n-1) j (by simpa [Nat.sub_add_cancel hn] using hu (n-1) (by omega)) (hu j hjn)
  rw [Nat.sub_add_cancel hn] at hc
  linear_combination (-1 : R)^j * f (j+1) * hc.symm

lemma H_T (u f : ℕ → R) (n : ℕ)
    (hu : ∀ i < n, (i+1 : R) * u i = 1) :
    H u (T f) n = T (fun k => u (k-1) * f k) n := by
  unfold H T
  simp_rw [mul_sum]
  rw [triangle_sum]
  apply sum_congr rfl
  intro j hj
  have hjn := mem_range.mp hj
  calc
    (∑ i ∈ Ico j n, u i * ((-1 : R)^j * ((i+1).choose (j+1) : R) * f (j+1))) =
        ∑ i ∈ Ico j n, (-1 : R)^j * u j * f (j+1) * (i.choose j : R) := by
      apply sum_congr rfl
      intro i hi
      have hc := choose_fraction u i j (hu i (mem_Ico.mp hi).2) (hu j hjn)
      linear_combination (-1 : R)^j * f (j+1) * hc
    _ = (-1 : R)^j * u j * f (j+1) * (n.choose (j+1) : R) := by
      rw [← mul_sum, ← Nat.cast_sum, sum_choose_Ico n j (by omega)]
    _ = _ := by simp only [Nat.add_sub_cancel]; ring

lemma T_one (n : ℕ) (hn : 0 < n) : T (fun _ => (1 : R)) n = 1 := by
  unfold T
  simp only [mul_one]
  simpa using alternating_tail (R := R) n 0 hn (Nat.zero_le _)

def ps (u : ℕ → R) (r n : ℕ) : R := ∑ i ∈ range n, u i ^ r

def ds (u : ℕ → R) (a b n : ℕ) : R :=
  ∑ j ∈ range n, ps u a j * u j ^ b

def qs (u : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ range n, (ps u 1 j)^2 * u j^2

lemma ps_succ (u : ℕ → R) (r n : ℕ) :
    ps u r (n+1) = ps u r n + u n^r := sum_range_succ _ _

lemma T_inv (u : ℕ → R) (n : ℕ)
    (hu : ∀ i < n, (i+1 : R) * u i = 1) :
    T (fun k => u (k-1)) n = ps u 1 n := by
  have hh := H_T u (fun _ => (1 : R)) n hu
  simp only [mul_one] at hh
  rw [← hh]
  unfold H ps
  apply sum_congr rfl
  intro i hi
  rw [T_one (i+1) (by omega)]
  simp

lemma sum_prefix_sq (u : ℕ → R) (n : ℕ) :
    2 * (∑ i ∈ range n, u i * ps u 1 (i+1)) =
      (ps u 1 n)^2 + ps u 2 n := by
  induction n with
  | zero => simp [ps]
  | succ n ih =>
    rw [sum_range_succ, ps_succ, ps_succ]
    simp only [pow_one]
    linear_combination ih

lemma T_inv_sq (u : ℕ → R) (n : ℕ)
    (hu : ∀ i < n, (i+1 : R) * u i = 1) :
    2 * T (fun k => u (k-1)^2) n = (ps u 1 n)^2 + ps u 2 n := by
  have hh := H_T u (fun k => u (k-1)) n hu
  simp only [← pow_two] at hh
  rw [← hh]
  unfold H
  have heq : (∑ i ∈ range n, u i * T (fun k => u (k-1)) (i+1)) =
      ∑ i ∈ range n, u i * ps u 1 (i+1) := by
    apply sum_congr rfl
    intro i hi
    rw [T_inv u (i+1) (fun j hj => hu j (by have := mem_range.mp hi; omega))]
  rw [heq]
  exact sum_prefix_sq u n

lemma harmonic_duality_four (u : ℕ → R) (n : ℕ)
    (hu : ∀ i < n, (i+1 : R) * u i = 1) :
    2 * T (fun k => u (k-1) * ps u 3 k) n =
      ∑ i ∈ range n, u i^2 * ((ps u 1 (i+1))^2 + ps u 2 (i+1)) := by
  rw [← H_T u (ps u 3) n hu]
  unfold H
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  have hsub : ∀ j < i+1, (j+1 : R) * u j = 1 := fun j hj => hu j (by omega)
  have heq : ps u 3 = H u (fun k => u (k-1)^2) := by
    funext m
    unfold ps H
    apply sum_congr rfl
    intro j hj
    simp only [Nat.add_sub_cancel]
    ring
  rw [heq, T_H u (fun k => u (k-1)^2) (i+1) (by omega) hsub]
  simp only [Nat.add_sub_cancel]
  linear_combination u i^2 * T_inv_sq u (i+1) hsub

lemma ps_mul_ps (u : ℕ → R) (a b n : ℕ) :
    ps u a n * ps u b n = ds u a b n + ds u b a n + ps u (a+b) n := by
  induction n with
  | zero => simp [ps, ds]
  | succ n ih =>
    simp only [ps_succ, ds, sum_range_succ] at ih ⊢
    rw [pow_add]
    linear_combination ih

lemma sum_range_zmod {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M]
    (f : ZMod p → M) : (∑ i ∈ range p, f (i : ZMod p)) = ∑ x : ZMod p, f x := by
  apply sum_bij (fun (i : ℕ) _ => (i : ZMod p))
  · intros; simp
  · intro i hi j hj hij
    have := congrArg ZMod.val hij
    simpa [ZMod.val_cast_of_lt (mem_range.mp hi), ZMod.val_cast_of_lt (mem_range.mp hj)] using this
  · intro x hx
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), by simp⟩
  · intros; rfl

noncomputable def invs (R : Type*) [Inv R] [NatCast R] (i : ℕ) : R := ((i+1 : ℕ) : R)⁻¹

lemma invs_unit_field (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p-1) :
    (i+1 : ZMod p) * invs (ZMod p) i = 1 := by
  unfold invs
  rw [Nat.cast_add, Nat.cast_one]
  apply mul_inv_cancel₀
  rw [← Nat.cast_add_one]
  intro h
  have hd := (ZMod.natCast_eq_zero_iff (i+1) p).mp h
  have := Nat.le_of_dvd (by omega : 0 < i+1) hd
  omega

lemma ps_field_zero (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 0 < r) (hrp : r < p-1) :
    ps (invs (ZMod p)) r (p-1) = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have heq : ps (invs (ZMod p)) r (p-1) = ∑ x : ZMod p, x⁻¹^r := by
    rw [← sum_range_zmod]
    have hs := sum_range_succ' (fun i => (i : ZMod p)⁻¹^r) (p-1)
    rw [Nat.sub_add_cancel hp] at hs
    rw [hs]
    simp [ps, invs, zero_pow (Nat.ne_of_gt hr)]
  rw [heq]
  have hperm := Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x : ZMod p => x⁻¹^r) (fun x : ZMod p => x^r) (fun x => rfl)
  rw [hperm]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) r (by simpa using hrp)

lemma invs_reflect_field (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p-1) :
    invs (ZMod p) (p-1-1-i) = -invs (ZMod p) i := by
  unfold invs
  have hn : p-1-1-i+1 = p-(i+1) := by omega
  rw [hn, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_sub, inv_neg]

lemma prefix_reflect (u : ℕ → R) (n j : ℕ) (hj : j ≤ n)
    (hu : ∀ i < n, u (n-1-i) = -u i) :
    ps u 1 (n-j) = ps u 1 n + ps u 1 j := by
  by_cases hn : n = 0
  · subst n
    have : j = 0 := by omega
    subst j
    simp [ps]
  have href := sum_Ico_reflect u 0 (m := j) (n := n-1) (by omega)
  simp only [Nat.Ico_zero_eq_range, Nat.sub_zero,
    Nat.sub_add_cancel (show 1 ≤ n from by omega)] at href
  have hanti : (∑ i ∈ range j, u (n-1-i)) = -ps u 1 j := by
    simp only [ps, pow_one, ← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    exact hu i (by have := mem_range.mp hi; omega)
  rw [hanti] at href
  have hs := sum_range_add_sum_Ico u (show n-j ≤ n by omega)
  rw [← href] at hs
  simp only [ps, pow_one] at *
  linear_combination hs

lemma ds13_of_reflect (u : ℕ → R) (n : ℕ)
    (hu : ∀ i < n, u (n-1-i) = -u i) (h1 : ps u 1 n = 0) :
    2 * ds u 1 3 n = -ps u 4 n := by
  have href := sum_range_reflect (fun j => ps u 1 j * u j^3) n
  change (∑ j ∈ range n, ps u 1 (n-1-j) * u (n-1-j)^3) = ds u 1 3 n at href
  have heq : (∑ j ∈ range n, ps u 1 (n-1-j) * u (n-1-j)^3) =
      -ds u 1 3 n - ps u 4 n := by
    rw [show -ds u 1 3 n - ps u 4 n =
      ∑ j ∈ range n, (-ps u 1 j * u j^3 - u j^4) by simp [ds, ps, sum_sub_distrib, sum_neg_distrib]]
    apply sum_congr rfl
    intro j hj
    have hjn := mem_range.mp hj
    rw [hu j hjn, show n-1-j = n-(j+1) by omega,
      prefix_reflect u n (j+1) (by omega) hu, h1, zero_add, ps_succ]
    simp only [pow_one]
    ring
  rw [heq] at href
  linear_combination -href

lemma choose_field (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : k < p) :
    ((p-1).choose k : ZMod p) = (-1 : ZMod p)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hc : (p.choose (k+1) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact (Fact.out : p.Prime).dvd_choose_self (by omega) hk
    have hpas := congrArg (fun m : ℕ => (m : ZMod p)) (Nat.choose_succ_succ (p-1) k)
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel hp, Nat.cast_add] at hpas
    rw [hc, ih (by omega)] at hpas
    rw [pow_succ]
    linear_combination -hpas

lemma T_field (p : ℕ) [Fact p.Prime] (f : ℕ → ZMod p) :
    T f (p-1) = -∑ i ∈ range (p-1), f (i+1) := by
  unfold T
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [choose_field p (i+1) (by have := mem_range.mp hi; omega)]
  have hs : (-1 : ZMod p)^i * (-1 : ZMod p)^(i+1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    simp
  rw [hs]
  ring

lemma duality_expand (u : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, u i^2 * ((ps u 1 (i+1))^2 + ps u 2 (i+1))) =
      qs u n + 2 * ds u 1 3 n + ds u 2 2 n + 2 * ps u 4 n := by
  unfold qs ds ps
  simp only [sum_range_succ, pow_one, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intros
  ring

lemma sum_last_prefix (u : ℕ → R) (a b n : ℕ) :
    (∑ i ∈ range n, u i^b * ps u a (i+1)) = ds u a b n + ps u (a+b) n := by
  unfold ds ps
  simp only [sum_range_succ, ← sum_add_distrib]
  apply sum_congr rfl
  intros
  rw [pow_add]
  ring

lemma field_weight_four (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ds (invs (ZMod p)) 1 3 (p-1) = 0 ∧
    ds (invs (ZMod p)) 2 2 (p-1) = 0 ∧
    qs (invs (ZMod p)) (p-1) = 0 := by
  let u := invs (ZMod p)
  have h1 : ps u 1 (p-1) = 0 := ps_field_zero p 1 (by omega) (by omega)
  have h2 : ps u 2 (p-1) = 0 := ps_field_zero p 2 (by omega) (by omega)
  have h3 : ps u 3 (p-1) = 0 := ps_field_zero p 3 (by omega) (by omega)
  have h4 : ps u 4 (p-1) = 0 := ps_field_zero p 4 (by omega) (by omega)
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega
  have hh13 := ds13_of_reflect u (p-1) (invs_reflect_field p) h1
  rw [h4, neg_zero] at hh13
  have h13 := (mul_eq_zero.mp hh13).resolve_left htwo
  have hh22 := ps_mul_ps u 2 2 (p-1)
  norm_num only [h2, h4, Nat.reduceAdd, zero_mul, add_zero, ← two_mul] at hh22
  have h22 := (mul_eq_zero.mp hh22.symm).resolve_left htwo
  have h31 : ds u 3 1 (p-1) = 0 := by
    have hh := ps_mul_ps u 1 3 (p-1)
    simpa [h1, h13, h4] using hh.symm
  have hh := harmonic_duality_four u (p-1) (invs_unit_field p)
  rw [T_field, duality_expand] at hh
  simp only [Nat.add_sub_cancel] at hh
  have hsum : (∑ i ∈ range (p-1), u i * ps u 3 (i+1)) = 0 := by
    simpa [h31, h4] using sum_last_prefix u 3 1 (p-1)
  rw [hsum, h13, h22, h4] at hh
  refine ⟨h13, h22, ?_⟩
  simpa using hh.symm

lemma unit_small (p k : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p) :
    IsUnit (k : ZMod (p^5)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
  intro h
  have := Nat.le_of_dvd hk h
  omega

lemma invs_unit (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p-1) :
    (i+1 : ZMod (p^5)) * invs (ZMod (p^5)) i = 1 := by
  simpa only [invs, Nat.cast_add, Nat.cast_one] using
    ZMod.mul_inv_of_unit ((i+1 : ℕ) : ZMod (p^5)) (unit_small p (i+1) (by omega) (by omega))

noncomputable def red (p : ℕ) : ZMod (p^5) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 5 ≠ 0)) (ZMod p)

lemma red_invs (p : ℕ) [Fact p.Prime] (i : ℕ) (hi : i < p-1) :
    red p (invs (ZMod (p^5)) i) = invs (ZMod p) i := by
  have hh := congrArg (red p) (invs_unit p i hi)
  simp only [map_mul, map_add, map_natCast, map_one] at hh
  have hn : (i+1 : ZMod p) ≠ 0 := by
    intro h
    have hh' := invs_unit_field p i hi
    rw [h, zero_mul] at hh'
    exact zero_ne_one hh'
  apply mul_left_cancel₀ hn
  rw [hh, invs_unit_field p i hi]

lemma red_ps (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ p-1) :
    red p (ps (invs (ZMod (p^5))) r n) = ps (invs (ZMod p)) r n := by
  unfold ps
  simp only [map_sum, map_pow]
  apply sum_congr rfl
  intro i hi
  rw [red_invs p i (by have := mem_range.mp hi; omega)]

lemma red_ds (p : ℕ) [Fact p.Prime] (a b n : ℕ) (hn : n ≤ p-1) :
    red p (ds (invs (ZMod (p^5))) a b n) = ds (invs (ZMod p)) a b n := by
  unfold ds
  simp only [map_sum, map_mul, map_pow]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  rw [red_invs p i (by omega), red_ps p a i (by omega)]

lemma red_qs (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : n ≤ p-1) :
    red p (qs (invs (ZMod (p^5))) n) = qs (invs (ZMod p)) n := by
  unfold qs
  simp only [map_sum, map_mul, map_pow]
  apply sum_congr rfl
  intro i hi
  have hin := mem_range.mp hi
  rw [red_invs p i (by omega), red_ps p 1 i (by omega)]

lemma lift_zero (p : ℕ) [Fact p.Prime] (x : ZMod (p^5)) (hx : red p x = 0) :
    (p : ZMod (p^5))^4 * x = 0 := by
  have hval : (x.val : ZMod p) = 0 := by
    simpa only [red, ZMod.castHom_apply, ZMod.cast_eq_val] using hx
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff x.val p).mp hval
  rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul]
  calc
    (p : ZMod (p^5))^4 * ((p : ZMod (p^5)) * k) = (p : ZMod (p^5))^5 * k := by ring
    _ = 0 := by rw [ZMod.natCast_pow_eq_zero_of_le p (by decide : 5 ≤ 5), zero_mul]

lemma cancel_small (p k : ℕ) [Fact p.Prime] (hk : 0 < k) (hkp : k < p)
    (x y : ZMod (p^5)) (h : (k : ZMod (p^5))*x = (k : ZMod (p^5))*y) : x = y :=
  (unit_small p k hk hkp).mul_left_cancel h

lemma reflect_linear (t a u v : R) (ht : t^5 = 0) (hu : a*u = 1) (hv : (t-a)*v = 1) :
    t*v = -t*u - t^2*u^2 - t^3*u^3 - t^4*u^4 := by
  have hrel : v+u = t*u*v := by
    linear_combination -u*hv-v*hu
  linear_combination (t+t^2*u+t^3*u^2+t^4*u^3)*hrel + u^4*v*ht

lemma reflect_cube (t a u v : R) (ht : t^5 = 0) (hu : a*u = 1) (hv : (t-a)*v = 1) :
    t^3*v^3 = -t^3*u^3 - 3*t^4*u^4 := by
  have hh := reflect_linear t a u v ht hu hv
  have hpow (k : ℕ) (hk : 5 ≤ k) : t^k = 0 := pow_eq_zero_of_le hk ht
  rw [← mul_pow, hh]
  ring_nf
  simp (disch := omega) only [hpow, zero_mul, add_zero, neg_zero, sub_zero]

lemma product_four (t : R) (u : ℕ → R) (n : ℕ) (ht : t^5 = 0) :
    24 * (∏ i ∈ range n, (1+t*u i)) =
      24 + 24*t*ps u 1 n + 12*t^2*((ps u 1 n)^2-ps u 2 n) +
      4*t^3*((ps u 1 n)^3-3*ps u 1 n*ps u 2 n+2*ps u 3 n) +
      t^4*((ps u 1 n)^4-6*(ps u 1 n)^2*ps u 2 n+3*(ps u 2 n)^2+
        8*ps u 1 n*ps u 3 n-6*ps u 4 n) := by
  have hpow (k : ℕ) (hk : 5 ≤ k) : t^k = 0 := pow_eq_zero_of_le hk ht
  induction n with
  | zero => simp [ps]
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ih]
    simp only [ps_succ, pow_one]
    ring_nf
    simp (disch := omega) only [hpow, zero_mul, add_zero, sub_zero]

lemma product_two (t : R) (a b : ℕ → R) (n : ℕ) (ht : t^5 = 0) :
    2*t^2 * (∏ i ∈ range n, (1+t*a i+t^2*b i)) =
      2*t^2 + 2*t^3*ps a 1 n +
        t^4*((ps a 1 n)^2-ps a 2 n+2*ps b 1 n) := by
  have hpow (k : ℕ) (hk : 5 ≤ k) : t^k = 0 := pow_eq_zero_of_le hk ht
  induction n with
  | zero => simp [ps]
  | succ n ih =>
    rw [prod_range_succ, ← mul_assoc, ih]
    simp only [ps_succ, pow_one]
    ring_nf
    simp (disch := omega) only [hpow, zero_mul, add_zero, sub_zero]

lemma choose_pred_prod (u : ℕ → R) (n k : ℕ) (hk : k < n)
    (hu : ∀ i < k, (i+1 : R)*u i = 1) :
    ((n-1).choose k : R) = (-1 : R)^k * ∏ i ∈ range k, (1-(n : R)*u i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := by omega
    have hi := ih hk' (fun i hi => hu i (by omega))
    have hc := congrArg (fun m : ℕ => (m : R)) (Nat.choose_succ_right_eq (n-1) k)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (show k ≤ n-1 by omega), Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] at hc
    have heq : (((n-1).choose (k+1) : ℕ) : R) =
        ((n-1).choose k : R) * ((n : R)*u k-1) := by
      linear_combination u k*hc - (((n-1).choose (k+1) : R)+((n-1).choose k : R)) * hu k (by omega)
    rw [heq, hi, prod_range_succ, pow_succ]
    ring

lemma choose_split_mul (p j : ℕ) :
    (p+j) * ((p-1+j).choose j * (3*p).choose (p+j)) =
      p * (3*p).choose p * (2*p).choose j := by
  by_cases hp : p = 0
  · subst p; cases j <;> simp
  have h1 := Nat.choose_mul (n := 3*p) (k := p+j) (s := p) (by omega)
  rw [Nat.choose_symm_add] at h1
  have heq : 3*p-p = 2*p := by omega
  simp only [heq, Nat.add_sub_cancel_left] at h1
  have h2 := Nat.choose_mul_succ_eq (p-1+j) j
  have htop : p-1+j+1 = p+j := by omega
  have hsub : p-1+j+1-j = p := by omega
  rw [htop, Nat.add_sub_cancel_right] at h2
  calc
    _ = ((p-1+j).choose j * (p+j)) * (3*p).choose (p+j) := by ring
    _ = ((p+j).choose j * p) * (3*p).choose (p+j) := by rw [h2]
    _ = p * ((3*p).choose (p+j) * (p+j).choose j) := by ring
    _ = _ := by rw [h1]; ring

lemma vandermonde_self (n k : ℕ) :
    (n+k).choose n = ∑ j ∈ range (n+1), n.choose j * k.choose j := by
  rw [Nat.add_comm n k, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => k.choose i * n.choose j)]
  apply sum_congr rfl
  intro j hj
  rw [Nat.choose_symm (by have := mem_range.mp hj; omega)]
  ring

lemma choose_square (n k : ℕ) :
    ((n+k).choose n)^2 =
      ∑ j ∈ range (n+1), n.choose j * (n+j).choose j * (n+k).choose (n+j) := by
  calc
    _ = (n+k).choose n * (∑ j ∈ range (n+1), n.choose j * k.choose j) := by
      rw [← vandermonde_self]; ring
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hc := Nat.choose_mul (n := n+k) (k := n+j) (s := n) (by omega)
      simp only [Nat.add_sub_cancel_left] at hc
      rw [Nat.choose_symm_add (a := n) (b := j)] at hc
      calc
        _ = n.choose j * ((n+k).choose n * k.choose j) := by ring
        _ = n.choose j * ((n+k).choose (n+j) * (n+j).choose j) := by rw [hc]
        _ = _ := by ring

lemma sum_add_choose (n m j : ℕ) :
    (∑ k ∈ range (m+1), (n+k).choose (n+j)) = (n+m+1).choose (n+j+1) := by
  have hs := sum_range_add (fun k => k.choose (n+j)) n (m+1)
  rw [sum_choose_range, sum_choose_range, Nat.choose_eq_zero_of_lt (by omega : n < n+j+1), zero_add] at hs
  simpa only [Nat.add_assoc] using hs.symm

lemma sum_choose_square (n m : ℕ) :
    (∑ k ∈ range (m+1), ((n+k).choose n)^2) =
      ∑ j ∈ range (n+1), n.choose j * (n+j).choose j * (n+m+1).choose (n+j+1) := by
  simp_rw [choose_square]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← mul_sum, sum_add_choose]

lemma product_negative_two (t : R) (u : ℕ → R) (n : ℕ) (ht : t^5 = 0) :
    2*t^2 * (∏ i ∈ range n, (1-t*u i)) =
      2*t^2 - 2*t^3*ps u 1 n + t^4*((ps u 1 n)^2-ps u 2 n) := by
  have hh := product_two t (fun i => -u i) (fun _ => 0) n ht
  simpa [ps, sum_neg_distrib, mul_neg, sub_eq_add_neg] using hh

lemma duality_expand_minus (u : ℕ → R) (n : ℕ) :
    (∑ i ∈ range n, u i^2 * ((ps u 1 (i+1))^2 - ps u 2 (i+1))) =
      qs u n + 2 * ds u 1 3 n - ds u 2 2 n := by
  unfold qs ds ps
  simp only [sum_range_succ, pow_one, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intros
  ring

lemma weighted_binomial_relation (p : ℕ) (u : ℕ → R) (hp : 0 < p)
    (ht : (p : R)^5 = 0) (hu : ∀ i < p-1, (i+1 : R)*u i = 1) :
    2*(p : R)^2*T (fun k => u (k-1)^2) (p-1) =
      -2*(p : R)^2*ps u 2 (p-1) + 2*(p : R)^3*(ds u 1 2 (p-1)+ps u 3 (p-1)) -
      (p : R)^4*(qs u (p-1)+2*ds u 1 3 (p-1)-ds u 2 2 (p-1)) := by
  have hterm (i : ℕ) (hi : i < p-1) :
      2*(p : R)^2*((-1 : R)^i * ((p-1).choose (i+1) : R)) =
        -(2*(p : R)^2-2*(p : R)^3*ps u 1 (i+1)+(p : R)^4*((ps u 1 (i+1))^2-ps u 2 (i+1))) := by
    rw [choose_pred_prod u p (i+1) (by omega) (fun j hj => hu j (by omega))]
    have hsign : (-1 : R)^i * (-1 : R)^(i+1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]; simp
    rw [← mul_assoc ((-1 : R)^i), hsign]
    linear_combination -product_negative_two (p : R) u (i+1) ht
  calc
    _ = ∑ i ∈ range (p-1),
        -(2*(p : R)^2-2*(p : R)^3*ps u 1 (i+1)+(p : R)^4*((ps u 1 (i+1))^2-ps u 2 (i+1))) * u i^2 := by
      unfold T
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      simp only [Nat.add_sub_cancel]
      linear_combination u i^2*hterm i (mem_range.mp hi)
    _ = -2*(p : R)^2*ps u 2 (p-1) +
        2*(p : R)^3*(∑ i ∈ range (p-1), u i^2*ps u 1 (i+1)) -
        (p : R)^4*(∑ i ∈ range (p-1), u i^2*((ps u 1 (i+1))^2-ps u 2 (i+1))) := by
      conv_rhs => lhs; lhs; rhs; unfold ps
      simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intros
      ring
    _ = _ := by rw [sum_last_prefix, duality_expand_minus]

structure HarmonicData (t : R) (u : ℕ → R) (n : ℕ) : Prop where
  nil : t^5 = 0
  one : 2*t*ps u 1 n = -t^2*ps u 2 n
  one4 : t^4*ps u 1 n = 0
  two4 : t^4*ps u 2 n = 0
  three : t^3*ps u 3 n = 0
  four : t^4*ps u 4 n = 0
  d13 : t^4*ds u 1 3 n = 0
  d22 : t^4*ds u 2 2 n = 0
  q : t^4*qs u n = 0
  oneSq : t^2*(ps u 1 n)^2 = 0
  d12 : 2*t^3*ds u 1 2 n = 3*t^2*ps u 2 n

lemma harmonic_data (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    HarmonicData (p : ZMod (p^5)) (invs (ZMod (p^5))) (p-1) := by
  let t : ZMod (p^5) := p
  let u := invs (ZMod (p^5))
  let n := p-1
  have ht : t^5 = 0 := ZMod.natCast_pow_eq_zero_of_le p (by decide : 5 ≤ 5)
  have hu : ∀ i < n, (i+1 : ZMod (p^5))*u i = 1 := invs_unit p
  have hv (i : ℕ) (hi : i < n) : (t-(i+1 : ZMod (p^5)))*u (n-1-i) = 1 := by
    have hin : i < p-1 := hi
    have hh := invs_unit p (p-1-1-i) (by omega)
    have hidx : p-1-1-i+1 = p-(i+1) := by omega
    rw [← Nat.cast_add_one, hidx, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hh
    exact hh
  have hz (r : ℕ) (hr : 0 < r) (hrp : r < p-1) : t^4*ps u r n = 0 := by
    apply lift_zero p
    rw [red_ps p r n (by rfl)]
    exact ps_field_zero p r hr hrp
  have h14 := hz 1 (by omega) (by omega)
  have h24 := hz 2 (by omega) (by omega)
  have h4 := hz 4 (by omega) (by omega)
  have hf := field_weight_four p hp
  have h13 : t^4*ds u 1 3 n = 0 := by
    apply lift_zero p
    rw [red_ds p 1 3 n (by rfl)]
    exact hf.1
  have h22 : t^4*ds u 2 2 n = 0 := by
    apply lift_zero p
    rw [red_ds p 2 2 n (by rfl)]
    exact hf.2.1
  have hq : t^4*qs u n = 0 := by
    apply lift_zero p
    rw [red_qs p n (by rfl)]
    exact hf.2.2
  have hc : t^3*ps u 3 n = -t^3*ps u 3 n-3*t^4*ps u 4 n := by
    calc
      _ = ∑ i ∈ range n, t^3*u (n-1-i)^3 := by
        rw [sum_range_reflect (fun i => t^3*u i^3)]
        simp only [ps, mul_sum]
      _ = ∑ i ∈ range n, (-t^3*u i^3-3*t^4*u i^4) := by
        apply sum_congr rfl
        intro i hi
        exact reflect_cube t (i+1 : ZMod (p^5)) (u i) (u (n-1-i)) ht (hu i (mem_range.mp hi)) (hv i (mem_range.mp hi))
      _ = _ := by simp only [ps, mul_sum, sum_sub_distrib]
  have h3 : t^3*ps u 3 n = 0 := by
    apply cancel_small p 2 (by omega) (by omega)
    linear_combination hc-3*h4
  have hl : t*ps u 1 n = -t*ps u 1 n-t^2*ps u 2 n-t^3*ps u 3 n-t^4*ps u 4 n := by
    calc
      _ = ∑ i ∈ range n, t*u (n-1-i) := by
        rw [sum_range_reflect (fun i => t*u i)]
        simp only [ps, pow_one, mul_sum]
      _ = ∑ i ∈ range n, (-t*u i-t^2*u i^2-t^3*u i^3-t^4*u i^4) := by
        apply sum_congr rfl
        intro i hi
        exact reflect_linear t (i+1 : ZMod (p^5)) (u i) (u (n-1-i)) ht (hu i (mem_range.mp hi)) (hv i (mem_range.mp hi))
      _ = _ := by simp only [ps, pow_one, mul_sum, sum_sub_distrib]
  have h1 : 2*t*ps u 1 n = -t^2*ps u 2 n := by
    linear_combination hl-h3-h4
  have hsq : t^2*(ps u 1 n)^2 = 0 := by
    apply cancel_small p 4 (by omega) (by omega)
    linear_combination (2*t*ps u 1 n-t^2*ps u 2 n)*h1 + ps u 2 n*h24
  have h12 : 2*t^3*ds u 1 2 n = 3*t^2*ps u 2 n := by
    have hb := weighted_binomial_relation p u (by omega) ht hu
    have hi := T_inv_sq u n hu
    change 2*t^2*T (fun k => u (k-1)^2) n = _ at hb
    linear_combination -hb+t^2*hi+hsq-2*h3+hq+2*h13-h22
  exact ⟨ht, h1, h14, h24, h3, h4, h13, h22, hq, hsq, h12⟩

lemma HarmonicData.delta_sq {t : R} {u : ℕ → R} {n : ℕ} (h : HarmonicData t u n) :
    (t^2*ps u 2 n)^2 = 0 := by
  linear_combination ps u 2 n*h.two4

lemma HarmonicData.product_scaled {t : R} {u : ℕ → R} {n : ℕ} (h : HarmonicData t u n) :
    24 * (∏ i ∈ range n, (1+2*t*u i)) = 24*(1-3*t^2*ps u 2 n) := by
  have ht : (2*t)^5 = 0 := by rw [mul_pow, h.nil, mul_zero]
  have hh := product_four (2*t) u n ht
  linear_combination hh + (24-48*t^2*ps u 2 n)*h.one +
    (48+32*t*ps u 1 n+16*t^2*(ps u 1 n)^2)*h.oneSq +
    64*h.three + (-96*(ps u 1 n)^2+96*ps u 2 n)*h.two4 +
    128*ps u 3 n*h.one4-96*h.four

lemma add_choose_prod (u : ℕ → R) (m k : ℕ)
    (hu : ∀ i < k, (i+1 : R)*u i = 1) :
    ((m+k).choose k : R) = ∏ i ∈ range k, (1+(m : R)*u i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hi := ih (fun i hi => hu i (by omega))
    have hc := congrArg (fun l : ℕ => (l : R)) (Nat.add_one_mul_choose_eq (m+k) k)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
    have heq : ((m+(k+1)).choose (k+1) : R) = ((m+k).choose k : R)*(1+(m : R)*u k) := by
      have he : m+k+1 = m+(k+1) := by omega
      rw [he] at hc
      linear_combination -u k*hc + (((m+k).choose k : R)-((m+(k+1)).choose (k+1) : R))*hu k (by omega)
    rw [heq, hi, prod_range_succ]

lemma choose_three (p : ℕ) (hp : 0 < p) :
    (3*p).choose p = 3*((2*p+(p-1)).choose (p-1)) := by
  have hh := Nat.add_one_mul_choose_eq (2*p+(p-1)) (p-1)
  rw [show 2*p+(p-1)+1 = 3*p by omega, Nat.sub_add_cancel hp] at hh
  apply Nat.eq_of_mul_eq_mul_right hp
  calc
    _ = (3*p) * (2*p+(p-1)).choose (p-1) := hh.symm
    _ = _ := by ring

lemma choose_three_product (p : ℕ) (hp : 0 < p) (u : ℕ → R)
    (hu : ∀ i < p-1, (i+1 : R)*u i = 1) :
    ((3*p).choose p : R) = 3*(∏ i ∈ range (p-1), (1+2*(p : R)*u i)) := by
  rw [choose_three p hp, Nat.cast_mul, add_choose_prod u (2*p) (p-1) hu]
  norm_num

lemma product_pair_two (t : R) (u : ℕ → R) (n : ℕ) (ht : t^5 = 0) :
    2*t^2*(∏ i ∈ range n, ((1-t*u i)*(1-2*t*u i))) =
      2*t^2-6*t^3*ps u 1 n+t^4*(9*(ps u 1 n)^2-5*ps u 2 n) := by
  have hh := product_two t (fun i => -3*u i) (fun i => 2*u i^2) n ht
  have hprod : (∏ i ∈ range n, (1+t*(-3*u i)+t^2*(2*u i^2))) =
      ∏ i ∈ range n, ((1-t*u i)*(1-2*t*u i)) := by
    apply prod_congr rfl
    intros
    ring
  have h1 : ps (fun i => -3*u i) 1 n = -3*ps u 1 n := by simp [ps, mul_sum]
  have h2 : ps (fun i => -3*u i) 2 n = 9*ps u 2 n := by norm_num [ps, mul_pow, mul_sum]
  have hb : ps (fun i => 2*u i^2) 1 n = 2*ps u 2 n := by simp [ps, mul_sum]
  rw [hprod, h1, h2, hb] at hh
  linear_combination hh

lemma product_pair_factor (t z : R) (u : ℕ → R) (n : ℕ) (ht : t^5 = 0) :
    2*t^2*(1-2*t*z+2*t^2*z^2)*(∏ i ∈ range n, ((1-t*u i)*(1-2*t*u i))) =
      2*t^2-6*t^3*ps u 1 n-4*t^3*z+
        t^4*(9*(ps u 1 n)^2-5*ps u 2 n+12*z*ps u 1 n+4*z^2) := by
  have hpow (k : ℕ) (hk : 5 ≤ k) : t^k = 0 := pow_eq_zero_of_le hk ht
  calc
    _ = (2*t^2*(∏ i ∈ range n, ((1-t*u i)*(1-2*t*u i))))*(1-2*t*z+2*t^2*z^2) := by ring
    _ = (2*t^2-6*t^3*ps u 1 n+t^4*(9*(ps u 1 n)^2-5*ps u 2 n))*(1-2*t*z+2*t^2*z^2) := by
      rw [product_pair_two t u n ht]
    _ = _ := by
      ring_nf
      simp (disch := omega) only [hpow, zero_mul, add_zero, sub_zero, neg_zero]

lemma HarmonicData.sum_correction {t : R} {u : ℕ → R} {n : ℕ} (h : HarmonicData t u n) (B : R) :
    (∑ j ∈ range n, -2*B*t^2*u j^2*(1-2*t*u j+2*t^2*u j^2)*
      (∏ i ∈ range j, ((1-t*u i)*(1-2*t*u i)))) = 7*B*t^2*ps u 2 n := by
  calc
    _ = ∑ j ∈ range n, -B*u j^2 * (2*t^2-6*t^3*ps u 1 j-4*t^3*u j+
        t^4*(9*(ps u 1 j)^2-5*ps u 2 j+12*u j*ps u 1 j+4*u j^2)) := by
      apply sum_congr rfl
      intro j hj
      linear_combination -B*u j^2*product_pair_factor t (u j) u j h.nil
    _ = -B*(2*t^2*ps u 2 n-6*t^3*ds u 1 2 n-4*t^3*ps u 3 n+
        t^4*(9*qs u n-5*ds u 2 2 n+12*ds u 1 3 n+4*ps u 4 n)) := by
      have hs (r : ℕ) : ps u r n = ∑ i ∈ range n, u i^r := rfl
      conv_rhs => unfold qs ds; rw [hs 2, hs 3, hs 4]
      simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_congr rfl
      intros
      ring
    _ = _ := by
      linear_combination 3*B*h.d12+4*B*h.three-9*B*h.q+5*B*h.d22-12*B*h.d13-4*B*h.four

lemma choose_succ_unit (n k : ℕ) (hn : 0 < n) (v : R) (hv : (k+1 : R)*v = 1) :
    (n.choose (k+1) : R) = (n : R)*v*((n-1).choose k : R) := by
  have hh := congrArg (fun l : ℕ => (l : R)) (Nat.add_one_mul_choose_eq (n-1) k)
  rw [Nat.sub_add_cancel hn] at hh
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hh
  linear_combination -v*hh-(n.choose (k+1) : R)*hv

lemma sign_adjacent (j : ℕ) : (-1 : R)^(j+1)*(-1 : R)^j = -1 := by
  calc
    _ = -((-1 : R)^j * (-1 : R)^j) := by rw [pow_succ]; ring
    _ = _ := by rw [← mul_pow]; simp

lemma choose_pair_product (p j : ℕ) (hj : j < p-1) (u : ℕ → R)
    (hu : ∀ i < p-1, (i+1 : R)*u i = 1) :
    ((p-1).choose (j+1) : R)*((2*p).choose (j+1) : R) =
      -2*(p : R)*u j*(1-(p : R)*u j)*
        (∏ i ∈ range j, ((1-(p : R)*u i)*(1-2*(p : R)*u i))) := by
  rw [choose_pred_prod u p (j+1) (by omega) (fun i hi => hu i (by omega)),
    choose_succ_unit (2*p) j (by omega) (u j) (hu j hj),
    choose_pred_prod u (2*p) j (by omega) (fun i hi => hu i (by omega)),
    prod_range_succ]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [prod_mul_distrib]
  calc
    _ = ((-1 : R)^(j+1)*(-1 : R)^j) *
      (2*(p : R)*u j*(1-(p : R)*u j)*
        (∏ i ∈ range j, (1-(p : R)*u i))*(∏ i ∈ range j, (1-2*(p : R)*u i))) := by ring
    _ = _ := by rw [sign_adjacent]; ring

lemma unit_one_add (t z : R) (ht : t^5 = 0) : IsUnit (1+t*z) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨1-t*z+t^2*z^2-t^3*z^3+t^4*z^4, ?_⟩
  ring_nf
  simp [ht]

lemma square_sum_term (p j : ℕ) (hj : j < p-1) (u : ℕ → R)
    (hu : ∀ i < p-1, (i+1 : R)*u i = 1) (ht : (p : R)^5 = 0) :
    ((p-1).choose (j+1) : R)*((p-1+(j+1)).choose (j+1) : R)*((3*p).choose (p+(j+1)) : R) =
      -2*((3*p).choose p : R)*(p : R)^2*u j^2*(1-2*(p : R)*u j+2*(p : R)^2*u j^2)*
        (∏ i ∈ range j, ((1-(p : R)*u i)*(1-2*(p : R)*u i))) := by
  let t : R := p
  let B : R := (3*p).choose p
  let A : R := (p-1).choose (j+1)
  let M : R := (p-1+(j+1)).choose (j+1)
  let L : R := (3*p).choose (p+(j+1))
  let G : R := ∏ i ∈ range j, ((1-t*u i)*(1-2*t*u i))
  have hc := congrArg (fun l : ℕ => (l : R)) (choose_split_mul p (j+1))
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hc
  change (t+(j+1 : R))*(M*L) = t*B*((2*p).choose (j+1) : R) at hc
  have ha : A*((2*p).choose (j+1) : R) = -2*t*u j*(1-t*u j)*G :=
    choose_pair_product p j hj u hu
  have heq : (1+t*u j)*(A*M*L) = -2*B*t^2*u j^2*(1-t*u j)*G := by
    linear_combination u j*A*hc-A*M*L*hu j hj+t*u j*B*ha
  change A*M*L = -2*B*t^2*u j^2*(1-2*t*u j+2*t^2*u j^2)*G
  apply (unit_one_add t (u j) ht).mul_left_cancel
  rw [heq]
  ring_nf
  simp [show t^5 = 0 from ht]

def s1 (p : ℕ) : ℕ := ∑ k ∈ range (2*p+1), (p+k-1).choose k

def s2 (p : ℕ) : ℕ := ∑ k ∈ range (2*p+1), ((p+k-1).choose k)^2

lemma choose_shift (p k : ℕ) (hp : 0 < p) :
    (p+k-1).choose k = (p-1+k).choose (p-1) := by
  rw [show p+k-1 = p-1+k by omega, Nat.choose_symm_add]

lemma s1_eq (p : ℕ) (hp : 0 < p) : s1 p = (3*p).choose p := by
  unfold s1
  simp_rw [choose_shift p _ hp, Nat.add_comm (p-1)]
  rw [Nat.sum_range_add_choose, show 2*p+(p-1)+1 = 3*p by omega, Nat.sub_add_cancel hp]

lemma s2_eq (p : ℕ) (hp : 0 < p) :
    s2 p = ∑ j ∈ range p, (p-1).choose j * (p-1+j).choose j * (3*p).choose (p+j) := by
  unfold s2
  simp_rw [choose_shift p _ hp]
  rw [sum_choose_square, Nat.sub_add_cancel hp, show p-1+2*p+1 = 3*p by omega]
  apply sum_congr rfl
  intro j hj
  rw [show p-1+j+1 = p+j by omega]

lemma s2_cast (p : ℕ) (hp : 0 < p) (u : ℕ → R)
    (hu : ∀ i < p-1, (i+1 : R)*u i = 1) (h : HarmonicData (p : R) u (p-1)) :
    (s2 p : R) = ((3*p).choose p : R)+7*((3*p).choose p : R)*(p : R)^2*ps u 2 (p-1) := by
  rw [s2_eq p hp, Nat.cast_sum]
  simp only [Nat.cast_mul]
  have hs := sum_range_succ' (fun j => ((p-1).choose j : R)*((p-1+j).choose j : R)*((3*p).choose (p+j) : R)) (p-1)
  rw [Nat.sub_add_cancel hp] at hs
  rw [hs]
  have hsum : (∑ j ∈ range (p-1), ((p-1).choose (j+1) : R)*((p-1+(j+1)).choose (j+1) : R)*((3*p).choose (p+(j+1)) : R)) =
      7*((3*p).choose p : R)*(p : R)^2*ps u 2 (p-1) := by
    calc
      _ = ∑ j ∈ range (p-1), -2*((3*p).choose p : R)*(p : R)^2*u j^2*(1-2*(p : R)*u j+2*(p : R)^2*u j^2)*
          (∏ i ∈ range j, ((1-(p : R)*u i)*(1-2*(p : R)*u i))) := by
        apply sum_congr rfl
        intro j hj
        exact square_sum_term p j (mem_range.mp hj) u hu h.nil
      _ = _ := h.sum_correction _
  rw [hsum]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_zero]
  ring

lemma final_algebra (d : R) (hd : d^2 = 0) : (3*(1-3*d))^4*(3+12*d)^3 = 2187 := by
  have hpow (k : ℕ) (hk : 2 ≤ k) : d^k = 0 := pow_eq_zero_of_le hk hd
  ring_nf
  simp (disch := omega) only [hpow, zero_mul, add_zero, sub_zero, neg_zero]

lemma main_large (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    (s1 p)^4*(s2 p)^3 ≡ 2187 [MOD p^5] := by
  letI : Fact p.Prime := ⟨hp⟩
  let t : ZMod (p^5) := p
  let u := invs (ZMod (p^5))
  let d : ZMod (p^5) := t^2*ps u 2 (p-1)
  have h : HarmonicData t u (p-1) := harmonic_data p hp7
  have hu : ∀ i < p-1, (i+1 : ZMod (p^5))*u i = 1 := invs_unit p
  have h24 : IsUnit (24 : ZMod (p^5)) := by
    have hh := (unit_small p 2 (by omega) (by omega)).pow 3 |>.mul (unit_small p 3 (by omega) (by omega))
    norm_num at hh ⊢
    exact hh
  have hprod : (∏ i ∈ range (p-1), (1+2*t*u i)) = 1-3*d := by
    apply h24.mul_left_cancel
    dsimp [d]
    linear_combination h.product_scaled
  have hb : ((3*p).choose p : ZMod (p^5)) = 3*(1-3*d) := by
    rw [choose_three_product p hp.pos u hu]
    rw [hprod]
  have hB : (s1 p : ZMod (p^5)) = 3*(1-3*d) := by rw [s1_eq p hp.pos, hb]
  have hS : (s2 p : ZMod (p^5)) = 3+12*d := by
    have hs := s2_cast p hp.pos u hu h
    rw [hb] at hs
    change (s2 p : ZMod (p^5)) = 3*(1-3*d)+7*(3*(1-3*d))*t^2*ps u 2 (p-1) at hs
    linear_combination hs-63*h.delta_sq
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [hB, hS]
  exact final_algebra d h.delta_sq

end A357674Proof

/--
Conjecture 1: $a(p) \equiv a(1) \pmod{p^5}$ for all primes $p \ge 3$.
-/
theorem A357674_conjecture_1 (p : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    A357674 p ≡ A357674 1 [MOD p ^ 5] := by
  by_cases h3 : p = 3
  · subst p
    norm_num [A357674, Nat.ModEq, Finset.sum_range_succ, Nat.choose]
  by_cases h5 : p = 5
  · subst p
    norm_num [A357674, Nat.ModEq, Finset.sum_range_succ, Nat.choose]
  have hp7 : 7 ≤ p := by
    by_contra h
    have hle : p ≤ 6 := by omega
    interval_cases p <;> norm_num at *
  have ha1 : A357674 1 = 2187 := by
    norm_num [A357674, Finset.sum_range_succ, Nat.choose]
  rw [ha1]
  change (A357674Proof.s1 p)^4 * (A357674Proof.s2 p)^3 ≡ 2187 [MOD p^5]
  exact A357674Proof.main_large p hp hp7

theorem A357674_conjecture_1.disproof : ¬ (type_of% @A357674_conjecture_1) := sorry
