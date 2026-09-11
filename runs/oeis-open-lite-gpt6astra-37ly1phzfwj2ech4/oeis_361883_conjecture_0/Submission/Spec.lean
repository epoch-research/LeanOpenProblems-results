import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

open scoped BigOperators
open Finset
namespace SC

/- We work in the p-adic integers and express congruences as divisibility.
   The final step uses `PadicInt.toZModPow` to return to natural-number congruences. -/
variable {p : ℕ} [Fact p.Prime]
noncomputable def iv (p : ℕ) [Fact p.Prime] (k : ℕ) : ℤ_[p] := Ring.inverse (k : ℤ_[p])
def D (p : ℕ) [Fact p.Prime] (e : ℕ) (x : ℤ_[p]) : Prop := (p : ℤ_[p]) ^ e ∣ x
lemma unit_nat {k : ℕ} (h : ¬p ∣ k) : IsUnit (k : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr h
lemma iv_mul {k : ℕ} (h : ¬p ∣ k) : iv p k * k = 1 :=
  Ring.inverse_mul_cancel _ (unit_nat h)
lemma mul_iv {k : ℕ} (h : ¬p ∣ k) : (k : ℤ_[p]) * iv p k = 1 := by
  rw [mul_comm]; exact iv_mul h
lemma coe_iv {k : ℕ} (h : ¬p ∣ k) : (iv p k : ℚ_[p]) = (k : ℚ_[p])⁻¹ := by
  have hh := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) (iv_mul h)
  simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_one] at hh
  exact eq_inv_of_mul_eq_one_left hh
lemma D_iff_mod (e : ℕ) (x : ℤ_[p]) : D p e x ↔ PadicInt.toZModPow e x = 0 := by
  rw [D, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
lemma D_nat (e n : ℕ) : D p e (n : ℤ_[p]) ↔ p^e ∣ n := by
  rw [D_iff_mod, map_natCast, ZMod.natCast_eq_zero_iff]
lemma D_zero (e : ℕ) : D p e 0 := dvd_zero _
lemma D_add {e : ℕ} {x y : ℤ_[p]} (hx : D p e x) (hy : D p e y) : D p e (x+y) := dvd_add hx hy
lemma D_sub {e : ℕ} {x y : ℤ_[p]} (hx : D p e x) (hy : D p e y) : D p e (x-y) := dvd_sub hx hy
lemma D_mul_left {e : ℕ} {x : ℤ_[p]} (hx : D p e x) (y : ℤ_[p]) : D p e (y*x) := dvd_mul_of_dvd_right hx y
lemma D_mul_right {e : ℕ} {x : ℤ_[p]} (hx : D p e x) (y : ℤ_[p]) : D p e (x*y) := dvd_mul_of_dvd_left hx y
lemma D_mul {e f : ℕ} {x y : ℤ_[p]} (hx : D p e x) (hy : D p f y) : D p (e+f) (x*y) := by
  simpa [D, pow_add] using mul_dvd_mul hx hy
lemma D_mono {e f : ℕ} {x : ℤ_[p]} (h : e ≤ f) (hx : D p f x) : D p e x :=
  dvd_trans (pow_dvd_pow _ h) hx
lemma D_sum {ι : Type*} (s : Finset ι) {e : ℕ} {f : ι → ℤ_[p]} (h : ∀ i ∈ s, D p e (f i)) : D p e (∑ i ∈ s, f i) :=
  dvd_sum h
lemma D_pow {e : ℕ} {x : ℤ_[p]} (hx : D p e x) (k : ℕ) : D p (e*k) (x^k) := by
  simpa [D, pow_mul] using pow_dvd_pow_of_dvd hx k
lemma D_cancel {e : ℕ} {x u : ℤ_[p]} (hu : IsUnit u) : D p e (u*x) ↔ D p e x := by
  exact hu.dvd_mul_left

lemma iv_eq_zero {k : ℕ} (h : p ∣ k) : iv p k = 0 := by
  apply Ring.inverse_non_unit
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
    Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
  exact not_not.mpr h

lemma map_inverse_unit {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x : R} (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  rw [← one_mul (Ring.inverse (f x)), Ring.eq_mul_inverse_iff_mul_eq _ 1 _ (hx.map f)]
  rw [← map_mul, Ring.inverse_mul_cancel _ hx, map_one]

lemma map_iv (e k : ℕ) : PadicInt.toZModPow e (iv p k) =
    Ring.inverse (k : ZMod (p^e)) := by
  by_cases he : e = 0
  · subst e; change (_ : ZMod 1) = _; exact Subsingleton.elim _ _
  by_cases hk : p ∣ k
  · rw [iv_eq_zero hk, map_zero, Ring.inverse_non_unit]
    rw [ZMod.isUnit_iff_coprime,
      Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero he), Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    exact not_not.mpr hk
  · simpa only [iv, map_natCast] using map_inverse_unit (PadicInt.toZModPow e) (unit_nat hk)

/-- Multiplication by 2 permutes a finite ring when 2 is a unit.
This forces the sum of inverse squares to vanish when 3 is also a unit. -/
lemma sum_inverse_sq {R : Type*} [CommRing R] [Fintype R]
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) :
    ∑ x : R, (Ring.inverse x)^2 = 0 := by
  classical
  obtain ⟨u, hu⟩ := h2
  have h2 : IsUnit (2 : R) := hu ▸ u.isUnit
  have hs := Equiv.sum_comp (Units.mulLeft u) (fun x : R => (Ring.inverse x)^2)
  change (∑ x : R, (Ring.inverse (↑u*x))^2) = _ at hs
  rw [hu] at hs
  simp_rw [Ring.mul_inverse_rev, mul_pow] at hs
  rw [← Finset.sum_mul] at hs
  have hi : Ring.inverse (2 : R) * 2 = 1 := Ring.inverse_mul_cancel _ h2
  have he : (3 : R) * (∑ x : R, (Ring.inverse x)^2) = 0 := by
    linear_combination -4 * hs + (∑ x : R, (Ring.inverse x)^2) * (Ring.inverse 2 * 2 + 1) * hi
  apply h3.mul_left_cancel
  simpa using he

lemma sum_range_zmod {m : ℕ} [NeZero m] {A : Type*} [AddCommMonoid A]
    (f : ZMod m → A) : (∑ k ∈ range m, f k) = ∑ x : ZMod m, f x := by
  classical
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ZMod m))
  · simp
  · intro a ha b hb hab
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp ha),
      Nat.mod_eq_of_lt (mem_range.mp hb)] using this
  · intro b _
    exact ⟨b.val, mem_range.mpr (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
  · simp

lemma unit_mod_nat (e : ℕ) {k : ℕ} (hk : ¬p ∣ k) : IsUnit (k : ZMod (p^e)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hk).symm.pow_right e

lemma harmonic2_block (hp5 : 5 ≤ p) (e A : ℕ) :
    D p e (∑ j ∈ range (p^e), (iv p (A+j))^2) := by
  rw [D_iff_mod, map_sum]
  simp_rw [map_pow, map_iv, Nat.cast_add]
  rw [sum_range_zmod (fun x : ZMod (p^e) => Ring.inverse (↑A+x)^2)]
  have hs := Equiv.sum_comp (Equiv.addLeft (A : ZMod (p^e)))
    (fun x : ZMod (p^e) => (Ring.inverse x)^2)
  change (∑ x : ZMod (p^e), Ring.inverse ((A : ZMod (p^e))+x)^2) = _ at hs
  rw [hs]
  apply sum_inverse_sq
  · exact unit_mod_nat e (k := 2) (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  · exact unit_mod_nat e (k := 3) (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))

lemma harmonic2_multiple (hp5 : 5 ≤ p) (e A L : ℕ) (hL : p^e ∣ L) :
    D p e (∑ j ∈ range L, (iv p (A+j))^2) := by
  obtain ⟨q, rfl⟩ := hL
  induction q with
  | zero => simp [D]
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add]
    apply D_add ih
    simpa only [Nat.add_assoc] using harmonic2_block hp5 e (A+p^e*q)

lemma iv_pair {L j : ℕ} (hL : p ∣ L) (hj : j ≤ L) :
    iv p j + iv p (L-j) = (L : ℤ_[p]) * iv p j * iv p (L-j) := by
  have hadd : (j : ℤ_[p]) + (L-j : ℕ) = L := by
    norm_cast; omega
  by_cases hjp : p ∣ j
  · have hjp' : p ∣ L-j := Nat.dvd_sub hL hjp
    simp [iv_eq_zero hjp, iv_eq_zero hjp']
  · have hjp' : ¬p ∣ L-j := by
      intro h
      apply hjp
      have := Nat.dvd_sub hL h
      simpa [Nat.sub_sub_self hj] using this
    have h1 := mul_iv hjp
    have h2 := mul_iv hjp'
    linear_combination -iv p (L-j) * h1 - iv p j * h2 + iv p j * iv p (L-j) * hadd

/-- Pairing j with L-j upgrades the reciprocal-sum divisibility from s to 2s. -/
lemma harmonic1_multiple (hp5 : 5 ≤ p) (s L : ℕ) (hs : 0 < s) (hL : p^s ∣ L) :
    D p (2*s) (∑ j ∈ range (L+1), iv p j) := by
  have hLp : p ∣ L := dvd_trans (dvd_pow_self p (Nat.ne_of_gt hs)) hL
  have h2 : D p s (∑ j ∈ range (L+1), (iv p j)^2) := by
    rw [sum_range_succ, iv_eq_zero hLp, zero_pow (by decide : 2 ≠ 0), add_zero]
    simpa using harmonic2_multiple hp5 s 0 L hL
  have hpL : D p s (L : ℤ_[p]) := (D_nat s L).mpr hL
  have hpL2 : D p (2*s) ((L : ℤ_[p])^2) := by
    simpa [Nat.mul_comm] using D_pow hpL 2
  have he : (2 : ℤ_[p]) * (∑ j ∈ range (L+1), iv p j) =
      (L : ℤ_[p])^2 * (∑ j ∈ range (L+1), (iv p j)^2 * iv p (L-j)) -
      (L : ℤ_[p]) * (∑ j ∈ range (L+1), (iv p j)^2) := by
    have hrev : (∑ j ∈ range (L+1), iv p (L-j)) = ∑ j ∈ range (L+1), iv p j := by
      simpa using sum_range_reflect (fun j => iv p j) (L+1)
    calc
      _ = ∑ j ∈ range (L+1), (iv p j + iv p (L-j)) := by rw [sum_add_distrib, hrev]; ring
      _ = ∑ j ∈ range (L+1), ((L : ℤ_[p])^2 * ((iv p j)^2 * iv p (L-j)) - (L : ℤ_[p])*(iv p j)^2) := by
        apply sum_congr rfl
        intro j hj
        have h := iv_pair hLp (by simpa using mem_range.mp hj : j ≤ L)
        linear_combination (1 + (L : ℤ_[p])*iv p j) * h
      _ = _ := by rw [sum_sub_distrib, ← mul_sum, ← mul_sum]
  apply (D_cancel (unit_nat (k := 2) (Nat.not_dvd_of_pos_of_lt (by decide) (by omega)))).mp
  simp only [Nat.cast_ofNat]
  rw [he]
  apply D_sub (D_mul_right hpL2 _)
  simpa [two_mul] using D_mul hpL h2

/-- The first two terms of a finite product expansion, with a cubic error term. -/
lemma product_expansion {ι : Type*} (s : Finset ι) (x : ι → ℤ_[p]) (r : ℕ)
    (hx : ∀ i ∈ s, D p r (x i)) :
    D p r ((∏ i ∈ s, (1+x i))-1) ∧
    D p (2*r) ((∏ i ∈ s, (1+x i))-1-(∑ i ∈ s, x i)) ∧
    D p (3*r) (2*(∏ i ∈ s, (1+x i))-2-2*(∑ i ∈ s, x i)-
      (∑ i ∈ s, x i)^2+(∑ i ∈ s, (x i)^2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D]
  | @insert i s hi ih =>
    obtain ⟨h1,h2,h3⟩ := ih (fun j hj => hx j (mem_insert_of_mem hj))
    have hxi := hx i (mem_insert_self i s)
    simp only [prod_insert hi, sum_insert hi]
    constructor
    · convert D_add h1 (D_mul_right hxi (∏ j ∈ s, (1+x j))) using 1 <;> ring
    constructor
    · have hmul : D p (2*r) (x i*((∏ j ∈ s, (1+x j))-1)) := by
        simpa [two_mul] using D_mul hxi h1
      convert D_add h2 hmul using 1 <;> ring
    · have hmul : D p (3*r) (x i*((∏ j ∈ s, (1+x j))-1-(∑ j ∈ s, x j))) := by
        convert D_mul hxi h2 using 1 <;> omega
      convert D_add h3 (D_mul_left hmul 2) using 1 <;> ring

/-- The part of the rising-factorial product whose denominators are prime to p.
The other factors are 1 because `iv p j = 0` when p divides j. -/
noncomputable def U (p : ℕ) [Fact p.Prime] (N L : ℕ) : ℤ_[p] :=
  ∏ j ∈ range (L+1), (1+(N : ℤ_[p])*iv p j)

lemma U_basic (N L r : ℕ) (hN : p^r ∣ N) : D p r (U p N L - 1) := by
  exact (product_expansion _ _ r (fun j _ => D_mul_right ((D_nat r N).mpr hN) _)).1

/-- A product congruence with the precision needed at indices divisible by p. -/
lemma U_strong (hp5 : 5 ≤ p) (N L r s : ℕ) (hsr : s ≤ r)
    (hN : p^r ∣ N) (hL : p^s ∣ L) : D p (r+2*s) (U p N L - 1) := by
  by_cases hs : s = 0
  · subst s; simpa using U_basic N L r hN
  have hs : 0 < s := Nat.pos_of_ne_zero hs
  have hNp : D p r (N : ℤ_[p]) := (D_nat r N).mpr hN
  let H : ℤ_[p] := ∑ j ∈ range (L+1), (N : ℤ_[p])*iv p j
  let Q : ℤ_[p] := ∑ j ∈ range (L+1), ((N : ℤ_[p])*iv p j)^2
  have hH : D p (r+2*s) H := by
    dsimp [H]; rw [← mul_sum]
    exact D_mul hNp (harmonic1_multiple hp5 s L hs hL)
  have hQ : D p (r+2*s) Q := by
    have hLp : p ∣ L := dvd_trans (dvd_pow_self p (Nat.ne_of_gt hs)) hL
    have h2 : D p s (∑ j ∈ range (L+1), (iv p j)^2) := by
      rw [sum_range_succ, iv_eq_zero hLp, zero_pow (by decide : 2 ≠ 0), add_zero]
      simpa using harmonic2_multiple hp5 s 0 L hL
    dsimp [Q]; simp_rw [mul_pow]; rw [← mul_sum]
    apply D_mono (by omega : r+2*s ≤ r*2+s)
    exact D_mul (D_pow hNp 2) h2
  have hexp : D p (r+2*s) (2*U p N L-2-2*H-H^2+Q) :=
    D_mono (by omega) (product_expansion _ _ r (fun j _ => D_mul_right hNp _)).2.2
  have h2 : IsUnit (2 : ℤ_[p]) := unit_nat (k := 2)
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  apply (D_cancel h2).mp
  convert D_sub (D_add (D_add hexp (D_mul_left hH 2)) (D_mul_right hH H)) hQ using 1 <;> ring

def C (N k : ℕ) : ℕ := Nat.choose (N+k) k
lemma C_zero (N : ℕ) : C N 0 = 1 := by simp [C]
lemma C_step (N k : ℕ) : C N (k+1) * (k+1) = C N k * (N+k+1) := by
  simpa [C, Nat.add_assoc, Nat.mul_comm] using (Nat.add_one_mul_choose_eq (N+k) k).symm
lemma C_step_cast (N k : ℕ) : (C N (k+1) : ℤ_[p]) * (k+1) = (C N k : ℤ_[p]) * (N+k+1) := by
  exact_mod_cast C_step N k
lemma U_zero (N : ℕ) : U p N 0 = 1 := by simp [U, iv_eq_zero (dvd_zero p)]
lemma U_step (N k : ℕ) : U p N (k+1) = U p N k * (1+(N : ℤ_[p])*iv p (k+1)) := by
  simp only [U, sum_range_succ, prod_range_succ]

/-- Split a binomial coefficient into its p-divisible and p-unit factors. -/
lemma C_split (n k : ℕ) : (C (p*n) k : ℤ_[p]) = (C n (k/p) : ℤ_[p]) * U p (p*n) k := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction k with
  | zero => simp [C_zero, U_zero]
  | succ k ih =>
    have hk0 : (k+1 : ℤ_[p]) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    apply mul_right_cancel₀ hk0
    rw [C_step_cast, ih, U_step]
    by_cases hk : p ∣ k+1
    · rw [iv_eq_zero hk, mul_zero, add_zero, mul_one]
      have hq : (k+1)/p = k/p+1 := Nat.succ_div_of_dvd hk
      rw [hq]
      have hkq : p*(k/p+1) = k+1 := by rw [← hq, Nat.mul_div_cancel' hk]
      have hsm := C_step_cast (p := p) n (k/p)
      have hkqc : (p : ℤ_[p])*((k/p : ℕ)+1) = k+1 := by exact_mod_cast hkq
      push_cast
      linear_combination -(p : ℤ_[p])*U p (p*n) k*hsm +
        U p (p*n) k*((C n (k/p+1) : ℤ_[p])-(C n (k/p) : ℤ_[p]))*hkqc
    · have hq : (k+1)/p = k/p := Nat.succ_div_of_not_dvd hk
      rw [hq]
      have hi := iv_mul hk
      push_cast at hi ⊢
      linear_combination -(C n (k/p) : ℤ_[p]) * U p (p*n) k * (p : ℤ_[p]) * n * hi

lemma D_power_congr {e : ℕ} {x y : ℤ_[p]} (h : D p e (x-y)) (k : ℕ) : D p e (x^k-y^k) := by
  rw [D_iff_mod, map_sub, sub_eq_zero] at h ⊢
  simp only [map_pow, h]

lemma C_approx (n k r : ℕ) (hn : p^r ∣ p*n) :
    D p r ((C (p*n) k : ℤ_[p]) - (C n (k/p) : ℤ_[p])) := by
  rw [C_split]
  convert D_mul_left (U_basic (p*n) k r hn) (C n (k/p)) using 1 <;> ring

lemma sum_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (b q : ℕ) :
    (∑ k ∈ range (b*q), f k) = ∑ t ∈ range q, ∑ j ∈ range b, f (b*t+j) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma sum_weight_blocks (f : ℕ → ℤ_[p]) (g : ℕ → ℤ_[p]) (b q : ℕ) (hb : 0 < b) :
    (∑ k ∈ range (b*q), f (k/b)*g k) =
      ∑ t ∈ range q, f t * (∑ j ∈ range b, g (b*t+j)) := by
  rw [sum_blocks]
  apply sum_congr rfl
  intro t ht
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [Nat.mul_add_div hb, Nat.div_eq_of_lt (mem_range.mp hj), Nat.add_zero]

lemma weighted_diff (hp5 : 5 ≤ p) (s r L : ℕ) (hL : p^s ∣ L)
    (f g : ℕ → ℤ_[p]) (hf : ∀ t, D p r (f t-g t)) :
    D p (s+r) ((∑ k ∈ range L, f (k/p^s)*(iv p k)^2) -
      ∑ k ∈ range L, g (k/p^s)*(iv p k)^2) := by
  obtain ⟨q,rfl⟩ := hL
  rw [← sum_sub_distrib]
  simp_rw [← sub_mul]
  rw [sum_weight_blocks (fun t => f t-g t) (fun k => (iv p k)^2) (p^s) q (pow_pos (Fact.out : p.Prime).pos _)]
  apply D_sum
  intro t ht
  simpa [Nat.add_comm] using D_mul (hf t) (harmonic2_block hp5 s (p^s*t))

/-- Repeatedly enlarge the blocks while removing one power of p from the
binomial parameter. The inverse-square sum supplies the precision of each block. -/
lemma weighted_harmonic (hp5 : 5 ≤ p) (n r s L : ℕ) (hL : p^(s+r) ∣ L) :
    D p (s+r) (∑ k ∈ range L, (C (n*p^r) (k/p^s) : ℤ_[p])^3*(iv p k)^2) := by
  induction r generalizing s with
  | zero =>
    simp only [Nat.add_zero, pow_zero, Nat.mul_one] at hL ⊢
    obtain ⟨q,rfl⟩ := hL
    rw [sum_weight_blocks (fun t => (C n t : ℤ_[p])^3) (fun k => (iv p k)^2) (p^s) q (pow_pos (Fact.out : p.Prime).pos _)]
    exact D_sum _ (fun t _ => D_mul_left (harmonic2_block hp5 s (p^s*t)) _)
  | succ r ih =>
    have hL' : p^s ∣ L := dvd_trans (pow_dvd_pow p (by omega : s ≤ s+(r+1))) hL
    have hmul : n*p^(r+1) = p*(n*p^r) := by ring
    have hd := weighted_diff hp5 s (r+1) L hL'
      (fun t => (C (n*p^(r+1)) t : ℤ_[p])^3)
      (fun t => (C (n*p^r) (t/p) : ℤ_[p])^3) (fun t => by
        rw [hmul]
        apply D_power_congr
        apply C_approx
        rw [← hmul]
        exact dvd_mul_left _ _)
    have hi := ih (s+1) (by convert hL using 1 <;> congr 1 <;> omega)
    have he : (∑ k ∈ range L, (C (n*p^r) ((k/p^s)/p) : ℤ_[p])^3*(iv p k)^2) =
        ∑ k ∈ range L, (C (n*p^r) (k/p^(s+1)) : ℤ_[p])^3*(iv p k)^2 := by
      simp only [Nat.div_div_eq_div_mul, pow_succ]
    rw [he] at hd
    have hi' : D p (s+(r+1)) (∑ k ∈ range L, (C (n*p^r) (k/p^(s+1)) : ℤ_[p])^3*(iv p k)^2) := by
      convert hi using 1 <;> omega
    convert D_add hd hi' using 1 <;> ring

/- Integral summands: k B(N,k) = N E(N,k), so the summand in the
   question equals T(N,k) = B(N,k)^2 (B(N,k) + 2 E(N,k)). -/
def B (N k : ℕ) : ℕ := Nat.choose (N+k-1) (N-1)
def E (N k : ℕ) : ℕ := Nat.choose (N+k-1) N
def T (N k : ℕ) : ℕ := B N k ^ 2 * (B N k + 2*E N k)

lemma B_zero {N : ℕ} (hN : 0 < N) : B N 0 = 1 := by simp [B]
lemma E_zero {N : ℕ} (hN : 0 < N) : E N 0 = 0 := by
  exact Nat.choose_eq_zero_of_lt (by simp only [Nat.add_zero]; omega)
lemma T_zero {N : ℕ} (hN : 0 < N) : T N 0 = 1 := by simp [T, B_zero hN, E_zero hN]
lemma E_succ (N k : ℕ) : E N (k+1) = C N k := by
  simpa [E, C, Nat.add_assoc] using (Nat.choose_symm_add (a := N) (b := k))
lemma C_eq_add {N : ℕ} (hN : 0 < N) (k : ℕ) : C N k = B N k + E N k := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [C, ← Nat.choose_symm_add]
  simp only [B, E, Nat.succ_sub_one, Nat.succ_add_sub_one]
  convert Nat.choose_succ_succ (N+k) N using 1 <;> congr 1 <;> omega
lemma B_mul {N : ℕ} (hN : 0 < N) (k : ℕ) : k * B N k = N * E N k := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simpa [B, E, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using
    (Nat.choose_succ_right_eq (N+k) N).symm
lemma B_mul_cast {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (k : ℤ_[p]) * (B N k : ℤ_[p]) = (N : ℤ_[p]) * (E N k : ℤ_[p]) := by
  exact_mod_cast B_mul hN k
lemma C_eq_add_cast {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (C N k : ℤ_[p]) = (B N k : ℤ_[p]) + (E N k : ℤ_[p]) := by
  exact_mod_cast C_eq_add hN k
lemma B_mul_C {N : ℕ} (hN : 0 < N) (k : ℕ) :
    ((N : ℤ_[p])+k)*(B N k : ℤ_[p]) = (N : ℤ_[p])*(C N k : ℤ_[p]) := by
  have h := B_mul_cast (p := p) hN k
  rw [C_eq_add_cast hN k]
  linear_combination h

lemma BE_split {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (B (p*n) (p*k) : ℤ_[p]) = (B n k : ℤ_[p]) * U p (p*n) (p*k) ∧
    (E (p*n) (p*k) : ℤ_[p]) = (E n k : ℤ_[p]) * U p (p*n) (p*k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpn : 0 < p*n := Nat.mul_pos hp hn
  have hC := C_split (p := p) n (p*k)
  rw [Nat.mul_div_cancel_left k hp] at hC
  have hB := B_mul_C (p := p) hpn (p*k)
  have hB' := B_mul_C (p := p) hn k
  have heq : (B (p*n) (p*k) : ℤ_[p]) = (B n k : ℤ_[p]) * U p (p*n) (p*k) := by
    have hne : ((p*n : ℕ) : ℤ_[p]) + (p*k : ℕ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.add_pos_left hpn (p*k)))
    apply mul_left_cancel₀ hne
    push_cast at hB ⊢
    linear_combination hB + (p : ℤ_[p])*n*hC - (p : ℤ_[p])*U p (p*n) (p*k)*hB'
  refine ⟨heq, ?_⟩
  rw [C_eq_add_cast hpn (p*k), C_eq_add_cast hn k, heq] at hC
  linear_combination hC

lemma T_split {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (T (p*n) (p*k) : ℤ_[p]) = (T n k : ℤ_[p]) * U p (p*n) (p*k)^3 := by
  obtain ⟨hB,hE⟩ := BE_split (p := p) hn k
  simp only [T, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [hB,hE]
  ring

lemma B_unit {N k : ℕ} (hN : 0 < N) (hk : ¬p ∣ k) :
    (B N k : ℤ_[p]) = (N : ℤ_[p])*iv p k*(E N k : ℤ_[p]) := by
  have h := B_mul_cast (p := p) hN k
  have hi := iv_mul hk
  linear_combination iv p k * h - (B N k : ℤ_[p])*hi

lemma E_approx (n k r : ℕ) (hn : p^r ∣ p*n) (hk : ¬p ∣ k) :
    D p r ((E (p*n) k : ℤ_[p]) - (C n (k/p) : ℤ_[p])) := by
  cases k with
  | zero => exact (hk (dvd_zero p)).elim
  | succ k =>
    rw [E_succ, Nat.succ_div_of_not_dvd hk]
    exact C_approx n k r hn

/-- At p-unit indices only the leading inverse-square term survives. -/
lemma T_nonmultiple {n : ℕ} (hn : 0 < n) (k r : ℕ)
    (hpn : p^r ∣ p*n) (hk : ¬p ∣ k) :
    D p (3*r) ((T (p*n) k : ℤ_[p]) -
      2*((p*n : ℕ) : ℤ_[p])^2*(iv p k)^2*(C n (k/p) : ℤ_[p])^3) := by
  have hN : D p r ((p*n : ℕ) : ℤ_[p]) := (D_nat r (p*n)).mpr hpn
  have hB := B_unit (p := p) (Nat.mul_pos (Fact.out : p.Prime).pos hn) hk
  have hE := D_power_congr (E_approx n k r hpn hk) 3
  have h1 : D p (3*r) (((p*n : ℕ) : ℤ_[p])^3 * ((iv p k)^3*(E (p*n) k : ℤ_[p])^3)) := by
    simpa [Nat.mul_comm] using D_mul_right (D_pow hN 3) ((iv p k)^3*(E (p*n) k : ℤ_[p])^3)
  have h2 : D p (3*r) (2*(iv p k)^2 *
      (((p*n : ℕ) : ℤ_[p])^2 * ((E (p*n) k : ℤ_[p])^3-(C n (k/p) : ℤ_[p])^3))) := by
    have hd := D_mul (D_pow hN 2) hE
    have he : r*2+r = 3*r := by omega
    rw [he] at hd
    exact D_mul_left hd _
  simp only [T, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [hB]
  convert D_add h1 h2 using 1 <;> push_cast <;> ring

lemma D_cancel_power (e t : ℕ) (x : ℤ_[p]) :
    D p (t+e) ((p : ℤ_[p])^t*x) ↔ D p e x := by
  rw [D, D, pow_add]
  exact mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))

lemma B_divisibility {n : ℕ} (hn : 0 < n) (e t u : ℕ)
    (hN : p^e ∣ n) (hu : ¬p ∣ u) :
    D p (e-t) (B n (p^t*u) : ℤ_[p]) := by
  by_cases ht : t ≤ e
  · have hd : D p e (((p^t*u : ℕ) : ℤ_[p])*(B n (p^t*u) : ℤ_[p])) := by
      rw [B_mul_cast hn]
      exact D_mul_right ((D_nat e n).mpr hN) _
    rw [show e = t+(e-t) by omega, Nat.cast_mul, Nat.cast_pow, mul_assoc,
      D_cancel_power, D_cancel (unit_nat hu)] at hd
    exact hd
  · simp [D, Nat.sub_eq_zero_of_le (by omega : e ≤ t)]

/-- At multiples of p the summands agree individually to the required precision. -/
lemma T_multiple {n : ℕ} (hp5 : 5 ≤ p) (hn : 0 < n) (k r : ℕ) (hr : 0 < r)
    (hN : p^(r-1) ∣ n) : D p (3*r) ((T (p*n) (p*k) : ℤ_[p]) - (T n k : ℤ_[p])) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpn : p^r ∣ p*n := by
    rw [show r = (r-1)+1 by omega, pow_succ']
    exact Nat.mul_dvd_mul_left p hN
  by_cases hk : k = 0
  · subst k; simp [T_zero hn, T_zero (Nat.mul_pos hp hn), D]
  obtain ⟨t,u,hu,hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p (Fact.out : p.Prime).ne_one
  subst k
  rw [T_split hn]
  have hpku : p^(t+1) ∣ p*(p^t*u) := by
    exact ⟨u, by ring⟩
  by_cases ht : r ≤ t+1
  · have hU := U_strong hp5 (p*n) (p*(p^t*u)) r r le_rfl hpn
      (dvd_trans (pow_dvd_pow p ht) hpku)
    have hU3 := D_power_congr hU 3
    simp only [one_pow, show r+2*r = 3*r by omega] at hU3
    convert D_mul_left hU3 (T n (p^t*u) : ℤ_[p]) using 1 <;> ring
  · have hU := U_strong hp5 (p*n) (p*(p^t*u)) r (t+1) (by omega) hpn hpku
    have hU3 := D_power_congr hU 3
    simp only [one_pow] at hU3
    have hT : D p (2*(r-(t+1))) (T n (p^t*u) : ℤ_[p]) := by
      have hB := B_divisibility (p := p) hn (r-1) t u hN hu
      have he : (r-1-t)*2 = 2*(r-(t+1)) := by omega
      have hB2 := D_pow hB 2
      rw [he] at hB2
      simpa [T] using D_mul_right hB2 ((B n (p^t*u) : ℤ_[p])+2*(E n (p^t*u) : ℤ_[p]))
    have hmul := D_mul hT hU3
    have he : 2*(r-(t+1))+(r+2*(t+1)) = 3*r := by omega
    rw [he] at hmul
    convert hmul using 1 <;> ring

lemma weighted_harmonic_dvd (hp5 : 5 ≤ p) (N r s L : ℕ)
    (hN : p^r ∣ N) (hL : p^(s+r) ∣ L) :
    D p (s+r) (∑ k ∈ range L, (C N (k/p^s) : ℤ_[p])^3*(iv p k)^2) := by
  obtain ⟨n,rfl⟩ := hN
  simpa only [Nat.mul_comm] using weighted_harmonic hp5 n r s L hL

lemma sum_nonmultiples {n : ℕ} (hp5 : 5 ≤ p) (hn : 0 < n) (r : ℕ) (hr : 0 < r)
    (hN : p^(r-1) ∣ n) :
    D p (3*r) (∑ k ∈ (range (p*n+1)).filter (fun k => ¬p ∣ k), (T (p*n) k : ℤ_[p])) := by
  have hpn : p^r ∣ p*n := by
    rw [show r = (r-1)+1 by omega, pow_succ']
    exact Nat.mul_dvd_mul_left p hN
  let G (k : ℕ) : ℤ_[p] := 2*((p*n : ℕ) : ℤ_[p])^2*(iv p k)^2*(C n (k/p) : ℤ_[p])^3
  have hd : D p (3*r) ((∑ k ∈ (range (p*n+1)).filter (fun k => ¬p ∣ k), (T (p*n) k : ℤ_[p])) -
      ∑ k ∈ (range (p*n+1)).filter (fun k => ¬p ∣ k), G k) := by
    rw [← sum_sub_distrib]
    apply D_sum
    intro k hk
    exact T_nonmultiple hn k r hpn (mem_filter.mp hk).2
  have hf : (∑ k ∈ (range (p*n+1)).filter (fun k => ¬p ∣ k), G k) =
      ∑ k ∈ range (p*n+1), G k := by
    rw [sum_filter]
    apply sum_congr rfl
    intro k hk
    by_cases h : p ∣ k
    · simp [h, G, iv_eq_zero h]
    · simp [h]
  have hG : D p (3*r) (∑ k ∈ range (p*n+1), G k) := by
    rw [sum_range_succ]
    have hGend : G (p*n) = 0 := by simp [G, iv_eq_zero (dvd_mul_right p n)]
    rw [hGend, add_zero]
    have hw := weighted_harmonic_dvd hp5 n (r-1) 1 (p*n) hN
      (by simpa only [show 1+(r-1)=r by omega] using hpn)
    simp only [pow_one, show 1+(r-1)=r by omega] at hw
    have hNp : D p r ((p*n : ℕ) : ℤ_[p]) := (D_nat r (p*n)).mpr hpn
    have hd := D_mul (D_pow hNp 2) hw
    rw [show r*2+r = 3*r by omega] at hd
    convert D_mul_left hd 2 using 1
    dsimp [G]
    simp only [mul_sum]
    apply sum_congr rfl
    intro k hk
    ring
  rw [hf] at hd
  convert D_add hd hG using 1 <;> ring

lemma sum_multiples {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    (∑ k ∈ (range (p*n+1)).filter (fun k => p ∣ k), f k) =
      ∑ k ∈ range (n+1), f (p*k) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  symm
  apply sum_bij (fun (k : ℕ) _ => p*k)
  · intro k hk
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (by have := mem_range.mp hk; nlinarith), dvd_mul_right p k⟩
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hp hab
  · intro b hb
    obtain ⟨hb,hbd⟩ := mem_filter.mp hb
    obtain ⟨k,rfl⟩ := hbd
    exact ⟨k, mem_range.mpr (by have := mem_range.mp hb; nlinarith), rfl⟩
  · simp

def F (N : ℕ) : ℕ := ∑ k ∈ range (N+1), T N k
/-- Combine termwise congruence at multiples of p with cancellation elsewhere. -/
lemma F_congruence {n : ℕ} (hp5 : 5 ≤ p) (hn : 0 < n) (r : ℕ) (hr : 0 < r)
    (hN : p^(r-1) ∣ n) : D p (3*r) ((F (p*n) : ℤ_[p]) - (F n : ℤ_[p])) := by
  classical
  have hm : D p (3*r) ((∑ k ∈ range (n+1), (T (p*n) (p*k) : ℤ_[p])) -
      ∑ k ∈ range (n+1), (T n k : ℤ_[p])) := by
    rw [← sum_sub_distrib]
    exact D_sum _ (fun k _ => T_multiple hp5 hn k r hr hN)
  have hn' := sum_nonmultiples hp5 hn r hr hN
  have hsplit := sum_filter_add_sum_filter_not (range (p*n+1))
    (fun k => p ∣ k) (fun k => (T (p*n) k : ℤ_[p]))
  rw [sum_multiples] at hsplit
  simp only [F, Nat.cast_sum]
  rw [← hsplit]
  convert D_add hm hn' using 1 <;> ring

end SC


/-- Remove the exact natural-number division in the definition of a. -/
lemma SC.a_eq_F {N : ℕ} (hN : 0 < N) : a N = SC.F N := by
  unfold a
  rw [if_neg (Nat.ne_of_gt hN)]
  change (∑ k ∈ range (N+1), (N+2*k)*(SC.B N k)^3) / N = SC.F N
  have hterm : ∀ k, (N+2*k)*(SC.B N k)^3 = N*SC.T N k := by
    intro k
    have h := SC.B_mul hN k
    unfold SC.T
    calc
      _ = N*(SC.B N k)^3+2*(k*SC.B N k)*(SC.B N k)^2 := by ring
      _ = _ := by rw [h]; ring
  simp_rw [hterm]
  rw [← mul_sum, Nat.mul_div_cancel_left _ hN]
  rfl

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$
and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  letI : Fact p.Prime := ⟨hp⟩
  have hsmall : 0 < n*p^(r-1) := Nat.mul_pos hn (pow_pos hp.pos _)
  have hbig : 0 < n*p^r := Nat.mul_pos hn (pow_pos hp.pos _)
  have hpow : p*(n*p^(r-1)) = n*p^r := by
    calc
      _ = n*(p*p^(r-1)) := by ring
      _ = _ := by rw [← pow_succ']; congr 2; omega
  have h := SC.F_congruence (p := p) hp5 hsmall r hr (dvd_mul_left _ _)
  rw [hpow, SC.D_iff_mod, map_sub, map_natCast, map_natCast, sub_eq_zero] at h
  rw [SC.a_eq_F hbig, SC.a_eq_F hsmall]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h

theorem oeis_361883_conjecture_0.disproof : ¬ (type_of% @oeis_361883_conjecture_0) := sorry
