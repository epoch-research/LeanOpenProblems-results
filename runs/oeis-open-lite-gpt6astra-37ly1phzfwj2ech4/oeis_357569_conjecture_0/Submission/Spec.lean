import FormalConjectures.Util.ProblemImports
open Nat

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

open scoped BigOperators
open Finset
namespace OEIS357569Proof

/-- Representatives of the units modulo a power of `p`. -/
def inds (p n : ℕ) : Finset ℕ := (range n).filter (fun i => ¬ p ∣ i)

lemma mem_inds {p n i : ℕ} : i ∈ inds p n ↔ i < n ∧ ¬p ∣ i := by simp [inds]

lemma pos_of_mem_inds {p n i : ℕ} (hi : i ∈ inds p n) : 0 < i := by
  have := (mem_inds.mp hi).2
  by_contra h
  have : i = 0 := by omega
  simp [this] at *

lemma refl_mem {p n i : ℕ} (hn : p ∣ n) (hi : i ∈ inds p n) :
    n-i ∈ inds p n := by
  obtain ⟨hlt, hnd⟩ := mem_inds.mp hi
  have hip := pos_of_mem_inds hi
  refine mem_inds.mpr ⟨by omega, ?_⟩
  intro h
  exact hnd ((Nat.dvd_sub_iff_right (by omega) hn).mp h)

lemma prod_refl {R : Type*} [CommMonoid R] {p n : ℕ} (hn : p ∣ n) (f : ℕ → R) :
    (∏ i ∈ inds p n, f (n-i)) = ∏ i ∈ inds p n, f i := by
  apply prod_bij (fun i _ => n-i)
  · intro i hi; exact refl_mem hn hi
  · intro i hi j hj h; have := (mem_inds.mp hi).1; have := (mem_inds.mp hj).1; omega
  · intro j hj; exact ⟨n-j, refl_mem hn hj, by have := (mem_inds.mp hj).1; omega⟩
  · intros; rfl

lemma unit_nat {p N i : ℕ} (hp : p.Prime) (hi : ¬p ∣ i) :
    IsUnit (i : ZMod (p^N)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  exact ((hp.coprime_iff_not_dvd.mpr hi).symm).pow_right _

lemma map_inv {m n : ℕ} (f : ZMod m →+* ZMod n) {x : ZMod m} (hx : IsUnit x) :
    f x⁻¹ = (f x)⁻¹ := by
  rcases hx with ⟨u, rfl⟩
  rw [ZMod.inv_coe_unit]
  change ((Units.map f.toMonoidHom) (u⁻¹) : ZMod n) = _
  rw [_root_.map_inv]
  exact (ZMod.inv_coe_unit ((Units.map f.toMonoidHom) u)).symm

lemma dvd_of_reduce_nat {m n : ℕ} [NeZero n] (hm : m ∣ n) {x : ZMod n}
    (h : ZMod.castHom hm (ZMod m) x = 0) : (m : ZMod n) ∣ x := by
  have hh : m ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using h
  obtain ⟨c, hc⟩ := hh
  refine ⟨(c : ℕ), ?_⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod n)) hc
  simpa using hcast

lemma dvd_of_reduce {p N k : ℕ} (hp : p ≠ 0) (hk : k ≤ N) {x : ZMod (p^N)}
    (h : ZMod.castHom (pow_dvd_pow p hk) (ZMod (p^k)) x = 0) :
    (p : ZMod (p^N))^k ∣ x := by
  haveI : NeZero (p^N) := ⟨pow_ne_zero _ hp⟩
  have hh : (p^k : ℕ) ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa using h
  obtain ⟨c, hc⟩ := hh
  refine ⟨(c : ℕ), ?_⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod (p^N))) hc
  simpa using hcast

lemma unit_of_reduce {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) {x : ZMod (p^N)}
    (hx : ZMod.castHom (by simpa using pow_dvd_pow p hN) (ZMod p) x ≠ 0) : IsUnit x := by
  haveI : NeZero (p^N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  apply unit_nat hp
  intro hd
  apply hx
  simpa using (ZMod.natCast_eq_zero_iff x.val p).mpr hd

lemma cancel_unit_dvd {R : Type*} [CommRing R] {d x u : R} (hu : IsUnit u)
    (h : d ∣ x*u) : d ∣ x := by
  exact (hu.dvd_mul_right).mp h

lemma sum_inds_units {A : Type*} [AddCommMonoid A] {p s : ℕ} (hp : p.Prime)
    (hs : 1 ≤ s) [NeZero (p^s)] (f : ZMod (p^s) → A) :
    (∑ i ∈ inds p (p^s), f i) = ∑ u : (ZMod (p^s))ˣ, f u := by
  classical
  haveI : NeZero (p^s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply sum_bij (fun i hi => (unit_nat hp (mem_inds.mp hi).2).unit)
  · intros; exact mem_univ _
  · intro i hi j hj he
    have he' := congrArg (fun u : (ZMod (p^s))ˣ => (u : ZMod (p^s)).val) he
    simpa [IsUnit.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_inds.mp hi).1,
      Nat.mod_eq_of_lt (mem_inds.mp hj).1] using he'
  · intro u hu
    have hv : (u : ZMod (p^s)).val ∈ inds p (p^s) := by
      refine mem_inds.mpr ⟨ZMod.val_lt _, ?_⟩
      have hc := ZMod.val_coe_unit_coprime u
      have hc' := hc.of_dvd_right (pow_dvd_pow p hs)
      simp only [pow_one] at hc'
      exact hp.coprime_iff_not_dvd.mp hc'.symm
    refine ⟨_, hv, ?_⟩
    apply Units.ext
    simp
  · intro i hi; simp [IsUnit.unit_spec]

lemma sum_units_inv_pow {R : Type*} [CommRing R] [Fintype Rˣ] (k : ℕ) :
    (∑ u : Rˣ, ((u⁻¹ : Rˣ) : R)^k) = ∑ u : Rˣ, (u : R)^k := by
  exact Equiv.sum_comp (Equiv.inv Rˣ) (fun u : Rˣ => (u : R)^k)

/-- Multiplication by a fixed unit permutes all units, even in a ring with zero divisors. -/
lemma unit_sum_pow_annihilate {R : Type*} [CommRing R] [Fintype Rˣ]
    (u : Rˣ) (k : ℕ) :
    ((u : R)^k-1) * (∑ v : Rˣ, (v : R)^k) = 0 := by
  have hh := Equiv.sum_comp (Equiv.mulLeft u) (fun v : Rˣ => (v : R)^k)
  change (∑ v : Rˣ, ((u*v : Rˣ) : R)^k) = _ at hh
  simp only [Units.val_mul, mul_pow, ← mul_sum] at hh
  rw [sub_mul, one_mul, hh, sub_self]

/-- Multiplication by `2` annihilates the reciprocal-square sum by `2^2 - 1 = 3`.
Keeping this factor of `3` allows the prime `3` to be treated uniformly. -/
lemma three_sum_inv_sq {p s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hs : 1 ≤ s) :
    (3 : ZMod (p^s)) * (∑ i ∈ inds p (p^s), (i : ZMod (p^s))⁻¹ ^ 2) = 0 := by
  haveI : NeZero (p^s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [sum_inds_units hp hs (fun x => x⁻¹ ^ 2)]
  simp_rw [ZMod.inv_coe_unit]
  rw [sum_units_inv_pow]
  have hu : IsUnit (2 : ZMod (p^s)) := unit_nat hp (by intro h; have := Nat.le_of_dvd (by decide : 0 < 2) h; omega)
  have hh := unit_sum_pow_annihilate hu.unit 2
  norm_num [IsUnit.unit_spec] at hh ⊢
  exact hh

lemma inv_neg_unit {n : ℕ} {x : ZMod n} (hx : IsUnit x) : (-x)⁻¹ = -x⁻¹ := by
  apply hx.neg.mul_left_cancel
  rw [ZMod.mul_inv_of_unit _ hx.neg, neg_mul_neg, ZMod.mul_inv_of_unit _ hx]

lemma sum_invprod_dvd {p N s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hs : 1 ≤ s) (hsN : s ≤ N) :
    (p : ZMod (p^N))^s ∣ 3 * (∑ i ∈ inds p (p^s),
      (i : ZMod (p^N))⁻¹ * ((p^s-i : ℕ) : ZMod (p^N))⁻¹) := by
  apply dvd_of_reduce hp.ne_zero hsN
  simp only [map_mul, map_ofNat, map_sum]
  have hh := three_sum_inv_sq hp hp3 hs
  have hn : p ∣ p^s := by simpa using pow_dvd_pow p hs
  have hterm : ∀ i ∈ inds p (p^s),
      ZMod.castHom (pow_dvd_pow p hsN) (ZMod (p^s))
        ((i : ZMod (p^N))⁻¹ * ((p^s-i : ℕ) : ZMod (p^N))⁻¹) =
      -(i : ZMod (p^s))⁻¹ ^ 2 := by
    intro i hi
    rw [map_mul, map_inv _ (unit_nat hp (mem_inds.mp hi).2),
      map_inv _ (unit_nat hp (mem_inds.mp (refl_mem hn hi)).2)]
    simp only [map_natCast]
    rw [Nat.cast_sub (Nat.le_of_lt (mem_inds.mp hi).1), ZMod.natCast_self]
    rw [zero_sub, inv_neg_unit (unit_nat hp (mem_inds.mp hi).2)]
    ring
  -- restore the mapped product to apply the pointwise identity
  have he := sum_congr rfl hterm
  simp only [map_mul] at he
  rw [he, sum_neg_distrib, mul_neg, hh, neg_zero]


/-- The error in the linear product expansion is divisible by the square of
a common divisor of the increments. -/
lemma prod_first_error {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R) (d : R) (h : ∀ i ∈ s, d ∣ f i) :
    d^2 ∣ (∏ i ∈ s, (1+f i)) - 1 - ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    have he : (1+f i)*(∏ j ∈ s, (1+f j))-1-(f i+∑ j ∈ s, f j) =
        (1+f i)*((∏ j ∈ s, (1+f j))-1-∑ j ∈ s, f j) + f i*(∑ j ∈ s, f j) := by ring
    rw [he]
    apply dvd_add
    · exact dvd_mul_of_dvd_right (ih (fun j hj => h j (mem_insert_of_mem hj))) _
    · simpa [pow_two] using mul_dvd_mul (h i (mem_insert_self _ _))
        (dvd_sum (fun j hj => h j (mem_insert_of_mem hj)))

/-- A denominator-free quadratic product expansion, with cubic error. -/
lemma prod_second_error {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R) (d : R) (h : ∀ i ∈ s, d ∣ f i) :
    d^3 ∣ 2*((∏ i ∈ s, (1+f i))-1-∑ i ∈ s, f i) -
      (∑ i ∈ s, f i)^2 + ∑ i ∈ s, (f i)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, sum_insert hi]
    have hs : ∀ j ∈ s, d ∣ f j := fun j hj => h j (mem_insert_of_mem hj)
    have hdS : d ∣ ∑ j ∈ s, f j := dvd_sum hs
    have hdQ : d^2 ∣ ∑ j ∈ s, (f j)^2 := dvd_sum (fun j hj => pow_dvd_pow_of_dvd (hs j hj) 2)
    have he : 2*((1+f i)*(∏ j ∈ s, (1+f j))-1-(f i+∑ j ∈ s, f j)) -
        (f i+∑ j ∈ s, f j)^2 + ((f i)^2+∑ j ∈ s, (f j)^2) =
        (1+f i)*(2*((∏ j ∈ s, (1+f j))-1-∑ j ∈ s, f j)-
          (∑ j ∈ s, f j)^2+∑ j ∈ s, (f j)^2) +
        f i*((∑ j ∈ s, f j)^2-∑ j ∈ s, (f j)^2) := by ring
    rw [he]
    apply dvd_add (dvd_mul_of_dvd_right (ih hs) _)
    have hh := mul_dvd_mul (h i (mem_insert_self _ _))
      (dvd_sub (pow_dvd_pow_of_dvd hdS 2) hdQ)
    simpa [pow_succ, mul_comm] using hh

lemma sum_range_cast_mul (n m : ℕ) (f : ZMod n → ZMod n) :
    (∑ i ∈ range (n*m), f i) = (m : ZMod n) * ∑ i ∈ range n, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add,
      Nat.cast_succ, add_mul, one_mul]

/-- At level `p^2`, the reciprocal fourth powers occur in `p` identical blocks
after reduction modulo `p`. This supplies the extra precision needed when `r = 2`. -/
lemma sum_invprod_sq_dvd {p N : ℕ} (hp : p.Prime) (hN : 1 ≤ N) :
    (p : ZMod (p^N)) ∣ ∑ i ∈ inds p (p^2),
      ((i : ZMod (p^N))⁻¹ * ((p^2-i : ℕ) : ZMod (p^N))⁻¹)^2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p^N) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hh : (1 : ℕ) ≤ 2 := by decide
  have hn : p ∣ p^2 := by simpa using pow_dvd_pow p hh
  have hNN : p ∣ p^N := by simpa using pow_dvd_pow p hN
  suffices ZMod.castHom hNN (ZMod p)
      (∑ i ∈ inds p (p^2), ((i : ZMod (p^N))⁻¹ * ((p^2-i : ℕ) : ZMod (p^N))⁻¹)^2) = 0 by
    exact dvd_of_reduce_nat hNN this
  rw [map_sum]
  have he : ∀ i ∈ inds p (p^2),
      ZMod.castHom hNN (ZMod p)
        (((i : ZMod (p^N))⁻¹ * ((p^2-i : ℕ) : ZMod (p^N))⁻¹)^2) =
      (i : ZMod p)⁻¹ ^ 4 := by
    intro i hi
    rw [map_pow, map_mul, map_inv _ (unit_nat hp (mem_inds.mp hi).2),
      map_inv _ (unit_nat hp (mem_inds.mp (refl_mem hn hi)).2)]
    simp only [map_natCast]
    rw [Nat.cast_sub (Nat.le_of_lt (mem_inds.mp hi).1)]
    simp [pow_succ]
    ring
  rw [sum_congr rfl he]
  have hfilter : (∑ i ∈ inds p (p^2), (i : ZMod p)⁻¹ ^ 4) =
      ∑ i ∈ range (p^2), (i : ZMod p)⁻¹ ^ 4 := by
    apply sum_filter_of_ne
    intro i hi hi0 hdi
    exact hi0 (by simp [(ZMod.natCast_eq_zero_iff i p).mpr hdi])
  rw [hfilter, pow_two, sum_range_cast_mul p p (fun x => x⁻¹ ^ 4)]
  simp


def invprod (p N s i : ℕ) : ZMod (p^N) :=
  (i : ZMod (p^N))⁻¹ * ((p^s-i : ℕ) : ZMod (p^N))⁻¹

def H (p N s : ℕ) : ZMod (p^N) := ∑ i ∈ inds p (p^s), invprod p N s i

/-- The product of the `p`-unit factors introduced at level `p^s`. -/
def T (p N s k : ℕ) : ZMod (p^N) :=
  ∏ i ∈ inds p (p^s), (1-(k : ZMod (p^N))*(p : ZMod (p^N))^s*(i : ZMod (p^N))⁻¹)

lemma paired_factor {R : Type*} [CommRing R] (a b ia ib k : R)
    (ha : a*ia=1) (hb : b*ib=1) :
    (1-k*(a+b)*ia)*(1-k*(a+b)*ib) = 1+k*(k-1)*(a+b)^2*(ia*ib) := by
  linear_combination k*(a+b)*ib*ha + k*(a+b)*ia*hb

/-- Pairing `i` with `p^s-i` converts the square of the product into factors
whose increments are divisible by `p^(2*s)`. -/
lemma T_sq {p N s : ℕ} (hp : p.Prime) (hs : 1 ≤ s) (k : ℕ) :
    T p N s k ^ 2 = ∏ i ∈ inds p (p^s),
      (1+(k : ZMod (p^N))*((k : ZMod (p^N))-1)*(p : ZMod (p^N))^(2*s)*invprod p N s i) := by
  have hn : p ∣ p^s := by simpa using pow_dvd_pow p hs
  unfold T
  rw [pow_two]
  nth_rw 2 [← prod_refl hn (fun i => 1-(k : ZMod (p^N))*(p : ZMod (p^N))^s*(i : ZMod (p^N))⁻¹)]
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have ha := ZMod.mul_inv_of_unit (i : ZMod (p^N)) (unit_nat hp (mem_inds.mp hi).2)
  have hb := ZMod.mul_inv_of_unit ((p^s-i : ℕ) : ZMod (p^N)) (unit_nat hp (mem_inds.mp (refl_mem hn hi)).2)
  have hn' : (i : ZMod (p^N)) + ((p^s-i : ℕ) : ZMod (p^N)) = (p : ZMod (p^N))^s := by
    rw [Nat.cast_sub (Nat.le_of_lt (mem_inds.mp hi).1), Nat.cast_pow]
    ring
  have hh := paired_factor _ _ _ _ (k : ZMod (p^N)) ha hb
  rw [hn'] at hh
  simpa [invprod, pow_mul, mul_comm 2 s] using hh

lemma T_reduce {p N s : ℕ} (_hp : p.Prime) (hs : 1 ≤ s) (hN : 1 ≤ N) (k : ℕ) :
    ZMod.castHom (by simpa using pow_dvd_pow p hN) (ZMod p) (T p N s k) = 1 := by
  simp only [T, map_prod, map_sub, map_one, map_mul, map_pow, map_natCast,
    ZMod.natCast_self, zero_pow (by omega : s ≠ 0), mul_zero, zero_mul, sub_zero, prod_const_one]

lemma two_unit {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : IsUnit (2 : ZMod (p^N)) :=
  unit_nat hp (by intro hd; have := Nat.le_of_dvd (by decide : 0 < 2) hd; omega)

lemma T_add_unit {p N s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hs : 1 ≤ s) (hN : 1 ≤ N) (k : ℕ) : IsUnit (T p N s k+1) := by
  apply unit_of_reduce hp hN
  rw [map_add, map_one, T_reduce hp hs hN]
  norm_num only [one_add_one_eq_two]
  intro h
  have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

lemma H_dvd {p N s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hs : 1 ≤ s) (hsN : s ≤ N) :
    (p : ZMod (p^N))^s ∣ 3*H p N s :=
  sum_invprod_dvd hp hp3 hs hsN

lemma T_sub_dvd {p N s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hs : 1 ≤ s) (hsN : s ≤ N) (k : ℕ) :
    (p : ZMod (p^N))^(3*s) ∣ 3*(T p N s k-1) := by
  let R := ZMod (p^N)
  let c : R := (k : R)*((k : R)-1)
  let f : ℕ → R := fun i => c*(p:R)^(2*s)*invprod p N s i
  have hf : ∀ i ∈ inds p (p^s), (p:R)^(2*s) ∣ f i := by
    intro i hi; exact ⟨c*invprod p N s i, by dsimp [f]; ring⟩
  have he := prod_first_error (inds p (p^s)) f ((p:R)^(2*s)) hf
  have he' : (p:R)^(3*s) ∣ (∏ i ∈ inds p (p^s), (1+f i))-1-∑ i ∈ inds p (p^s), f i := by
    apply dvd_trans (pow_dvd_pow (p:R) (show 3*s ≤ 2*s*2 by omega))
    simpa only [pow_mul] using he
  have hsum : (∑ i ∈ inds p (p^s), f i) = c*(p:R)^(2*s)*H p N s := by
    simp [f, H, mul_sum]
  have hd : (p:R)^(3*s) ∣ 3*(∑ i ∈ inds p (p^s), f i) := by
    rw [hsum]
    have hh := mul_dvd_mul (dvd_refl ((p:R)^(2*s))) (H_dvd hp hp3 hs hsN)
    have heq : (p:R)^(2*s)*(p:R)^s = (p:R)^(3*s) := by rw [← pow_add]; congr 1; omega
    rw [heq] at hh
    convert dvd_mul_of_dvd_left hh c using 1 <;> ring
  have htotal : (p:R)^(3*s) ∣ 3*((∏ i ∈ inds p (p^s), (1+f i))-1) := by
    convert dvd_add (dvd_mul_of_dvd_right he' (3:R)) hd using 1 <;> ring
  have hsq : (p:R)^(3*s) ∣ 3*(T p N s k ^ 2-1) := by
    rw [T_sq hp hs k]; exact htotal
  apply cancel_unit_dvd (T_add_unit hp hp3 hs (le_trans hs hsN) k)
  convert hsq using 1 <;> ring

lemma pow_top_zero (p N : ℕ) : (p : ZMod (p^N))^N = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

lemma pow_zero_of_ge {p N e : ℕ} (he : N ≤ e) : (p : ZMod (p^N))^e = 0 := by
  exact (zero_dvd_iff.mp (by simpa only [pow_top_zero] using pow_dvd_pow (p : ZMod (p^N)) he))

lemma sqsum_zero {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (c : ZMod (p^(3*r+3))) :
    (∑ i ∈ inds p (p^r), (c*(p : ZMod (p^(3*r+3)))^(2*r)*invprod p (3*r+3) r i)^2) = 0 := by
  by_cases hr3 : 3 ≤ r
  · apply sum_eq_zero
    intro i hi
    rw [mul_pow, mul_pow, ← pow_mul]
    have hz : (p : ZMod (p^(3*r+3)))^(2*r*2) = 0 := pow_zero_of_ge (by omega)
    rw [hz, mul_zero, zero_mul]
  · have hr2 : r = 2 := by omega
    subst r
    have hh := sum_invprod_sq_dvd (N := 3*2+3) hp (by omega)
    change (p : ZMod (p^(3*2+3))) ∣ ∑ i ∈ inds p (p^2), (invprod p (3*2+3) 2 i)^2 at hh
    obtain ⟨z, hz⟩ := hh
    simp only [mul_pow, ← pow_mul, ← mul_sum]
    rw [hz]
    have hpz : (p : ZMod (p^(3*2+3)))^(2*2*2) * (p : ZMod (p^(3*2+3))) = 0 := by
      rw [← pow_succ]; exact pow_top_zero p (3*2+3)
    calc
      _ = c^2 * ((p : ZMod (p^(3*2+3)))^(2*2*2) * (p : ZMod (p^(3*2+3)))) * z := by ring
      _ = 0 := by rw [hpz]; ring

/-- The squared level product is linear modulo `p^(3*r+3)` after multiplication
by `9`. The factor `9` avoids division by `3`. -/
lemma T_sq_linear {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) (k : ℕ) :
    (9 : ZMod (p^(3*r+3))) * (T p (3*r+3) r k ^ 2 - 1 -
      (k : ZMod (p^(3*r+3)))*((k : ZMod (p^(3*r+3)))-1)*
        (p : ZMod (p^(3*r+3)))^(2*r)*H p (3*r+3) r) = 0 := by
  let R := ZMod (p^(3*r+3))
  let c : R := (k:R)*((k:R)-1)
  let f : ℕ → R := fun i => c*(p:R)^(2*r)*invprod p (3*r+3) r i
  have hf : ∀ i ∈ inds p (p^r), (p:R)^(2*r) ∣ f i := by
    intro i hi; exact ⟨c*invprod p (3*r+3) r i, by dsimp [f]; ring⟩
  have hsum : (∑ i ∈ inds p (p^r), f i) = c*(p:R)^(2*r)*H p (3*r+3) r := by simp [f, H, mul_sum]
  have hS : (p:R)^(3*r) ∣ 3*(∑ i ∈ inds p (p^r), f i) := by
    rw [hsum]
    have hh := mul_dvd_mul (dvd_refl ((p:R)^(2*r))) (H_dvd hp hp3 (by omega) (show r ≤ 3*r+3 by omega))
    have heq : (p:R)^(2*r)*(p:R)^r = (p:R)^(3*r) := by rw [← pow_add]; congr 1; omega
    rw [heq] at hh
    convert dvd_mul_of_dvd_left hh c using 1 <;> ring
  have hS2 : 9*(∑ i ∈ inds p (p^r), f i)^2 = 0 := by
    have hh := pow_dvd_pow_of_dvd hS 2
    have hz : ((p:R)^(3*r))^2 = 0 := by rw [← pow_mul]; exact pow_zero_of_ge (by omega)
    rw [hz, zero_dvd_iff] at hh
    convert hh using 1 <;> ring
  have hQ : (∑ i ∈ inds p (p^r), (f i)^2) = 0 := sqsum_zero hp hr c
  have he := prod_second_error (inds p (p^r)) f ((p:R)^(2*r)) hf
  have hz : ((p:R)^(2*r))^3 = 0 := by rw [← pow_mul]; exact pow_zero_of_ge (by omega)
  rw [hz, zero_dvd_iff, hQ, add_zero] at he
  have ht : T p (3*r+3) r k ^ 2 = ∏ i ∈ inds p (p^r), (1+f i) := T_sq hp (by omega) k
  rw [ht, ← hsum]
  apply (two_unit hp hp3).mul_left_cancel
  change (2:R)*(9*((∏ i ∈ inds p (p^r), (1+f i))-1-∑ i ∈ inds p (p^r), f i)) = (2:R)*0
  linear_combination 9*he + hS2


lemma weighted_prod_sub_one_dvd {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R) (d c : R) (h : ∀ i ∈ s, d ∣ c*(f i-1)) :
    d ∣ c*((∏ i ∈ s, f i)-1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi]
    have he : c*(f i * ∏ j ∈ s, f j - 1) =
        c*(f i - 1) * ∏ j ∈ s, f j + c*((∏ j ∈ s, f j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left (h i (mem_insert_self _ _)) _) (ih (fun j hj => h j (mem_insert_of_mem hj)))

def U (p N r k : ℕ) : ZMod (p^N) := ∏ s ∈ range r, T p N (s+1) k

lemma U_succ (p N r k : ℕ) : U p N (r+1) k = U p N r k * T p N (r+1) k := by
  exact prod_range_succ _ _

lemma U_sub_dvd {p N r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hrN : r ≤ N) (k : ℕ) :
    (p : ZMod (p^N))^3 ∣ 3*(U p N r k-1) := by
  apply weighted_prod_sub_one_dvd
  intro s hs
  have hsN : s+1 ≤ N := by have := mem_range.mp hs; omega
  exact dvd_trans (pow_dvd_pow _ (by omega : 3 ≤ 3*(s+1)))
    (T_sub_dvd hp hp3 (by omega) hsN k)

/-- The linear terms for `k = 3` and `k = 2` cancel in the required combination. -/
lemma U_congr {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    (9 : ZMod (p^(3*r+3))) * U p (3*r+3) r 3 ^ 2 - 54*U p (3*r+3) r 2 =
    9 * U p (3*r+3) (r-1) 3 ^ 2 - 54*U p (3*r+3) (r-1) 2 := by
  let R := ZMod (p^(3*r+3))
  let u : R := U p (3*r+3) (r-1) 3
  let v : R := U p (3*r+3) (r-1) 2
  let t : R := T p (3*r+3) r 3
  let w : R := T p (3*r+3) r 2
  let y : R := (p:R)^(2*r)*H p (3*r+3) r
  have ht : 9*(t^2-1-6*y) = 0 := by
    have hh := T_sq_linear hp hp3 hr 3
    norm_num only [Nat.cast_ofNat] at hh
    convert hh using 1 <;> dsimp [t, y]; ring
  have hw : 9*(w^2-1-2*y) = 0 := by
    have hh := T_sq_linear hp hp3 hr 2
    norm_num only [Nat.cast_ofNat] at hh
    convert hh using 1 <;> dsimp [w, y]; ring
  have hu : (p:R)^3 ∣ 3*(u-1) := U_sub_dvd hp hp3 (by omega) 3
  have hv : (p:R)^3 ∣ 3*(v-1) := U_sub_dvd hp hp3 (by omega) 2
  have hw' : (p:R)^3 ∣ 3*(w-1) := dvd_trans (pow_dvd_pow _ (by omega : 3 ≤ 3*r))
    (T_sub_dvd hp hp3 (by omega) (by omega) 2)
  have hE : (p:R)^3 ∣ 3*(u^2*(w+1)-2*v) := by
    convert dvd_sub (dvd_add (dvd_mul_of_dvd_left hu ((u+1)*(w+1))) hw')
      (dvd_mul_of_dvd_left hv 2) using 1 <;> ring
  have hy : (p:R)^(3*r) ∣ 3*y := by
    have hh := mul_dvd_mul (dvd_refl ((p:R)^(2*r)))
      (H_dvd hp hp3 (by omega) (show r ≤ 3*r+3 by omega))
    have heq : (p:R)^(2*r)*(p:R)^r = (p:R)^(3*r) := by rw [← pow_add]; congr 1; omega
    rw [heq] at hh
    convert hh using 1 <;> dsimp [y]; ring
  have hzero : 54*y*(u^2*(w+1)-2*v) = 0 := by
    have hh := mul_dvd_mul hy hE
    rw [← pow_add, pow_top_zero, zero_dvd_iff] at hh
    linear_combination 6*hh
  have hdiff : (9*(u*t)^2-54*(v*w)-(9*u^2-54*v))*(w+1) = 0 := by
    linear_combination (u^2*(w+1))*ht - 6*v*hw + hzero
  have heq : r = (r-1)+1 := by omega
  rw [show U p (3*r+3) r 3 = u*t by simpa only [← heq] using U_succ p (3*r+3) (r-1) 3,
    show U p (3*r+3) r 2 = v*w by simpa only [← heq] using U_succ p (3*r+3) (r-1) 2]
  apply sub_eq_zero.mp
  apply (T_add_unit (s := r) (N := 3*r+3) hp hp3 (by omega) (by omega) 2).mul_right_cancel
  simpa only [zero_mul] using hdiff


/-- A binomial product identity with all denominators cleared in the integers. -/
lemma choose_prod_pos (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    ((k*n).choose n : ℤ) * (∏ i ∈ Ico 1 n, (i : ℤ)) =
      (k : ℤ) * ∏ i ∈ Ico 1 n, (((k*n : ℕ) : ℤ) - (i : ℤ)) := by
  have hkn : n ≤ k*n := by nlinarith
  have hd := congrArg (fun t : ℕ => (t : ℤ)) (Nat.descFactorial_eq_factorial_mul_choose (k*n) n)
  rw [Nat.descFactorial_eq_prod_range] at hd
  push_cast at hd
  have hprod : (∏ i ∈ range n, ((k*n-i : ℕ) : ℤ)) =
      ∏ i ∈ range n, (((k*n : ℕ) : ℤ)-(i : ℤ)) := by
    apply prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (by have := mem_range.mp hi; omega)]
  rw [hprod, prod_range_eq_mul_Ico _ (by omega)] at hd
  have hfac : n.factorial = (∏ i ∈ Ico 1 n, i)*n := by
    rw [← prod_Ico_id_eq_factorial n, prod_Ico_succ_top hn]
  rw [hfac] at hd
  push_cast at hd
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0))
  push_cast
  linear_combination -hd

lemma choose_prod (k n : ℕ) (hk : 1 ≤ k) (hn : Odd n) :
    ((k*n).choose n : ℤ) * (∏ i ∈ Ico 1 n, (i : ℤ)) =
      (k : ℤ) * ∏ i ∈ Ico 1 n, ((i : ℤ) - ((k*n : ℕ) : ℤ)) := by
  have hnp : 1 ≤ n := hn.pos
  have he : Even (n-1) := by
    rcases hn with ⟨j, hj⟩
    exact ⟨j, by omega⟩
  rw [show (∏ i ∈ Ico 1 n, ((i : ℤ)-((k*n : ℕ) : ℤ))) =
    ∏ i ∈ Ico 1 n, -(((k*n : ℕ) : ℤ)-(i : ℤ)) by apply prod_congr rfl; intros; ring]
  rw [prod_neg, Nat.card_Ico, he.neg_one_pow, one_mul]
  exact choose_prod_pos k n hk hnp

lemma prod_mult_indices {R : Type*} [CommMonoid R] {p m : ℕ} (hp : 0 < p)
    (f : ℕ → R) :
    (∏ i ∈ (Ico 1 (p*m)).filter (fun i => p ∣ i), f i) =
      ∏ j ∈ Ico 1 m, f (p*j) := by
  symm
  apply prod_bij (fun j _ => p*j)
  · intro j hj
    obtain ⟨hj1,hjm⟩ := mem_Ico.mp hj
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by nlinarith, Nat.mul_lt_mul_of_pos_left hjm hp⟩, dvd_mul_right _ _⟩
  · intro i hi j hj he; exact Nat.eq_of_mul_eq_mul_left hp he
  · intro i hi
    obtain ⟨him, j, rfl⟩ := mem_filter.mp hi
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp him
    refine ⟨j, mem_Ico.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra hh
      have : j = 0 := by omega
      simp [this] at hlo
    · exact Nat.lt_of_mul_lt_mul_left hhi
  · intros; rfl

lemma filter_Ico_eq_inds (p n : ℕ) : (Ico 1 n).filter (fun i => ¬p ∣ i) = inds p n := by
  ext i
  simp only [mem_filter, mem_Ico, mem_inds]
  constructor
  · tauto
  · intro hi
    exact ⟨⟨pos_of_mem_inds (mem_inds.mpr hi), hi.1⟩, hi.2⟩

lemma prod_decompose (p m : ℕ) (hp : 0 < p) (f g : ℕ → ℤ)
    (hfg : ∀ j ∈ Ico 1 m, f (p*j) = (p : ℤ)*g j) :
    (∏ i ∈ Ico 1 (p*m), f i) =
      (p : ℤ)^(m-1) * (∏ j ∈ Ico 1 m, g j) * ∏ i ∈ inds p (p*m), f i := by
  rw [← prod_filter_mul_prod_filter_not (Ico 1 (p*m)) (fun i => p ∣ i) f,
    filter_Ico_eq_inds, prod_mult_indices hp, prod_congr rfl hfg, prod_mul_distrib,
    prod_const, Nat.card_Ico]

/-- Separate the factors divisible by `p`, then cancel their common nonzero
integer product before passing to a modular ring. -/
lemma choose_step_int (k p m : ℕ) (hk : 1 ≤ k) (hp : Odd p) (hm : Odd m) :
    ((k*(p*m)).choose (p*m) : ℤ) * (∏ i ∈ inds p (p*m), (i : ℤ)) =
      ((k*m).choose m : ℤ) * ∏ i ∈ inds p (p*m), ((i : ℤ)-((k*(p*m) : ℕ) : ℤ)) := by
  have hbig := choose_prod k (p*m) hk (hp.mul hm)
  have hsmall := choose_prod k m hk hm
  have hD := prod_decompose p m hp.pos (fun i => (i : ℤ)) (fun j => (j : ℤ)) (by intros; push_cast; rfl)
  have hE := prod_decompose p m hp.pos (fun i => (i : ℤ)-((k*(p*m) : ℕ) : ℤ))
    (fun j => (j : ℤ)-((k*m : ℕ) : ℤ)) (by intros; push_cast; ring)
  rw [hD, hE] at hbig
  have hd0 : (p : ℤ)^(m-1) * (∏ j ∈ Ico 1 m, (j : ℤ)) ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero _ (by exact_mod_cast hp.pos.ne')
    · apply prod_ne_zero_iff.mpr
      intro j hj
      exact_mod_cast (show j ≠ 0 by have := (mem_Ico.mp hj).1; omega)
  apply mul_left_cancel₀ hd0
  linear_combination hbig - ((p : ℤ)^(m-1)*(∏ i ∈ inds p (p*m), ((i : ℤ)-((k*(p*m) : ℕ) : ℤ))))*hsmall

lemma choose_step {p N s : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (k : ℕ) (hk : 1 ≤ k) :
    ((k*p^(s+1)).choose (p^(s+1)) : ZMod (p^N)) =
      ((k*p^s).choose (p^s) : ZMod (p^N)) * T p N (s+1) k := by
  have hodd := hp.odd_of_ne_two (by omega)
  have hh := choose_step_int k p (p^s) hk hodd (hodd.pow (n := s))
  rw [← pow_succ'] at hh
  have hh' := congrArg (fun z : ℤ => (z : ZMod (p^N))) hh
  push_cast at hh'
  let D : ZMod (p^N) := ∏ i ∈ inds p (p^(s+1)), (i : ZMod (p^N))
  have hu : IsUnit D := by
    apply IsUnit.prod_iff.mpr
    intro i hi
    exact unit_nat hp (mem_inds.mp hi).2
  have hT : T p N (s+1) k * D =
      ∏ i ∈ inds p (p^(s+1)), ((i : ZMod (p^N))-(k : ZMod (p^N))*(p : ZMod (p^N))^(s+1)) := by
    dsimp only [T, D]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have hiu := ZMod.inv_mul_of_unit (i : ZMod (p^N)) (unit_nat hp (mem_inds.mp hi).2)
    linear_combination -(k : ZMod (p^N))*(p : ZMod (p^N))^(s+1)*hiu
  apply hu.mul_right_cancel
  rw [mul_assoc, hT]
  exact hh'

/-- Reassemble the binomial coefficient from its successive level products. -/
lemma choose_eq_U {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (k : ℕ) (hk : 1 ≤ k) (r : ℕ) :
    ((k*p^r).choose (p^r) : ZMod (p^N)) = (k : ZMod (p^N))*U p N r k := by
  induction r with
  | zero => simp [U]
  | succ r ih => rw [choose_step hp hp3 k hk, ih, U_succ, mul_assoc]

end OEIS357569Proof

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by
  have hz : (a (p^r) : ZMod (p^(3*r+3))) =
      (a (p^(r-1)) : ZMod (p^(3*r+3))) := by
    simp only [a, Int.ofNat_eq_natCast, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    rw [OEIS357569Proof.choose_eq_U hp hp3 3 (by omega), OEIS357569Proof.choose_eq_U hp hp3 2 (by omega),
      OEIS357569Proof.choose_eq_U hp hp3 3 (by omega), OEIS357569Proof.choose_eq_U hp hp3 2 (by omega)]
    convert OEIS357569Proof.U_congr hp hp3 hr using 1 <;> ring
  simpa only [Int.natCast_pow] using
    (ZMod.intCast_eq_intCast_iff (a (p^r)) (a (p^(r-1))) (p^(3*r+3))).mp hz

theorem oeis_357569_conjecture_0.disproof : ¬ (type_of% @oeis_357569_conjecture_0) := sorry
