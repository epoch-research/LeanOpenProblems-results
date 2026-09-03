import FormalConjecturesUtil

/-! Root bounds for digit polynomials. These do not settle Erdős406. -/

namespace Erdos406Newman
open Polynomial

def complement (w : List ℕ) : List ℕ := w.map (fun d => 1 - d)

lemma ofDigits_nonneg (r : ℝ) (hr : 0 ≤ r) (w : List ℕ) :
    0 ≤ Nat.ofDigits r w := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih => simp only [Nat.ofDigits]; positivity

lemma norm_ofDigits_le (z : ℂ) (w : List ℕ) :
    ‖Nat.ofDigits z w‖ ≤ Nat.ofDigits ‖z‖ w := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    simp only [Nat.ofDigits]
    calc
      ‖(d : ℂ) + z * Nat.ofDigits z w‖ ≤ ‖(d : ℂ)‖ + ‖z * Nat.ofDigits z w‖ :=
        norm_add_le _ _
      _ = (d : ℝ) + ‖z‖ * ‖Nat.ofDigits z w‖ := by simp
      _ ≤ (d : ℝ) + ‖z‖ * Nat.ofDigits ‖z‖ w := by gcongr

lemma complement_good {w : List ℕ} (hw : w ⊆ [0, 1]) : complement w ⊆ [0, 1] := by
  intro d hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  have hh := hw ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl <;> simp

lemma partition_geom {R : Type*} [CommRing R] (z : R) (w : List ℕ)
    (hw : w ⊆ [0, 1]) :
    (1-z) * (Nat.ofDigits z w + Nat.ofDigits z (complement w)) = 1-z^w.length := by
  induction w with
  | nil => simp [Nat.ofDigits, complement]
  | cons d w ih =>
    have hd := hw (List.mem_cons_self ..)
    have ht : w ⊆ [0, 1] := fun a ha => hw (List.mem_cons_of_mem _ ha)
    have hc : (d : R) + ((1-d : ℕ) : R) = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> norm_num
    have hh := ih ht
    simp only [complement, List.map_cons, Nat.ofDigits, List.length_cons, pow_succ]
    change (1-z) * ((d : R) + z * Nat.ofDigits z w +
      (((1-d : ℕ) : R) + z * Nat.ofDigits z (complement w))) = _
    calc
      _ = (1-z) * ((d : R) + ((1-d : ℕ) : R)) +
        z * ((1-z) * (Nat.ofDigits z w + Nat.ofDigits z (complement w))) := by ring
      _ = 1 - z ^ w.length * z := by rw [hc, hh]; ring

lemma lower_root_bound (z : ℂ) (w : List ℕ) (hw : w ⊆ [0, 1])
    (hz : Nat.ofDigits z (1 :: w) = 0) : 1 < ‖z‖ ^ 2 + ‖z‖ := by
  have hn : z ≠ 0 := by
    intro he
    simp [he, Nat.ofDigits] at hz
  have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hn
  by_cases hr : 1 ≤ ‖z‖
  · nlinarith [sq_nonneg (‖z‖ - 1)]
  have hr1 : ‖z‖ < 1 := lt_of_not_ge hr
  let v := 1 :: w
  let a := Nat.ofDigits ‖z‖ v
  let b := Nat.ofDigits ‖z‖ (complement v)
  have hv : v ⊆ [0, 1] := List.cons_subset.mpr ⟨by simp, hw⟩
  have ha : 2 ≤ a := by
    have he : z * Nat.ofDigits z w = -1 := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa [Nat.ofDigits, add_comm] using hz
    have hh := mul_le_mul_of_nonneg_left (norm_ofDigits_le z w) (norm_nonneg z)
    rw [← norm_mul, he] at hh
    norm_num at hh
    dsimp [a, v, Nat.ofDigits]
    norm_num only [Nat.cast_one]
    linarith
  have hb : 0 ≤ b := ofDigits_nonneg _ (norm_nonneg z) _
  have hg : (a+b) * (1-‖z‖) = 1-‖z‖^v.length := by
    simpa only [mul_comm] using partition_geom ‖z‖ v hv
  have hgC : (1-z) * Nat.ofDigits z (complement v) = 1-z^v.length := by
    have hh := partition_geom z v hv
    change Nat.ofDigits z v = 0 at hz
    simpa only [hz, zero_add] using hh
  have hnC : 1-‖z‖^v.length ≤ (1+‖z‖)*b := by
    calc
      1-‖z‖^v.length ≤ ‖1-z^v.length‖ := by
        simpa using norm_sub_norm_le (1 : ℂ) (z^v.length)
      _ = ‖1-z‖ * ‖Nat.ofDigits z (complement v)‖ := by rw [← hgC, norm_mul]
      _ ≤ (1+‖z‖)*b := by
        have hd : ‖(1 : ℂ)-z‖ ≤ 1+‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
        have he := norm_ofDigits_le z (complement v)
        exact mul_le_mul hd he (norm_nonneg _) (by positivity)
  have hlin : a * (1-‖z‖) ≤ 2*‖z‖*b := by nlinarith only [hg, hnC]
  have hmul := mul_le_mul_of_nonneg_right hlin (by linarith : 0 ≤ 1-‖z‖)
  have hgeom := congrArg (fun x : ℝ => 2*‖z‖*x) hg
  have hbound : a*(1-‖z‖^2) ≤ 2*‖z‖*(1-‖z‖^v.length) := by
    nlinarith only [hmul, hgeom]
  have hlow := mul_le_mul_of_nonneg_right ha (by nlinarith : 0 ≤ 1-‖z‖^2)
  have hp : 0 < ‖z‖^v.length := pow_pos hr0 _
  nlinarith

lemma ofDigits_append_general {R : Type*} [CommSemiring R] (z : R) (v w : List ℕ) :
    Nat.ofDigits z (v ++ w) = Nat.ofDigits z v + z^v.length * Nat.ofDigits z w := by
  induction v with
  | nil => simp [Nat.ofDigits]
  | cons d v ih =>
    simp only [List.cons_append, Nat.ofDigits, List.length_cons, pow_succ, ih]
    ring

lemma ofDigits_reverse_reciprocal (z : ℂ) (hz : z ≠ 0) (w : List ℕ) :
    z^w.length * Nat.ofDigits z⁻¹ w.reverse = z * Nat.ofDigits z w := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    rw [List.reverse_cons, ofDigits_append_general]
    simp only [List.length_cons, List.length_reverse, Nat.ofDigits, mul_zero,
      add_zero, pow_succ]
    have hi : z^w.length * (z⁻¹)^w.length = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
    calc
      _ = z * (z^w.length * Nat.ofDigits z⁻¹ w.reverse) +
        z * (z^w.length * (z⁻¹)^w.length) * (d : ℂ) := by ring
      _ = z * (z * Nat.ofDigits z w) + z * (d : ℂ) := by rw [ih, hi]; ring
      _ = _ := by ring

lemma upper_root_bound (z : ℂ) (w : List ℕ) (hw : w ⊆ [0, 1])
    (hz : Nat.ofDigits z (w ++ [1]) = 0) : ‖z‖^2 < ‖z‖ + 1 := by
  by_cases hn : z = 0
  · simp [hn]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hn
  have hrev : Nat.ofDigits z⁻¹ ((w ++ [1]).reverse) = 0 := by
    have hh := ofDigits_reverse_reciprocal z hn (w ++ [1])
    rw [hz, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hn)
  have hw' : w.reverse ⊆ [0, 1] := fun a ha => hw (List.mem_reverse.mp ha)
  have hb := lower_root_bound z⁻¹ w.reverse hw' (by simpa using hrev)
  have hh := mul_lt_mul_of_pos_right hb (pow_pos hr 2)
  have he : (‖z⁻¹‖^2 + ‖z⁻¹‖) * ‖z‖^2 = 1 + ‖z‖ := by
    rw [norm_inv]
    field_simp
  rw [one_mul, he] at hh
  linarith

/-- Every complex zero of the digit polynomial of a good power of two lies
strictly in the golden-ratio annulus. This does not bound the polynomial degree. -/
theorem good_power_digit_root_bounds {n : ℕ} (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0, 1]) {z : ℂ} (hz : Nat.ofDigits z (Nat.digits 3 n) = 0) :
    1 < ‖z‖^2 + ‖z‖ ∧ ‖z‖^2 < ‖z‖ + 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hp : 0 < 2^k := by positivity
  have hmod : 2^k % 3 = 1 := by
    have hm : 2^k % 3 ∈ Nat.digits 3 (2^k) := by
      rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp]
      exact List.mem_cons_self ..
    have hh := hg hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with hh | hh
    · have hd := Nat.dvd_of_mod_eq_zero hh
      have hf := Nat.prime_three.dvd_of_dvd_pow hd
      norm_num at hf
    · exact hh
  constructor
  · rw [Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 3) hp, hmod] at hz hg
    exact lower_root_bound z _ (fun a ha => hg (List.mem_cons_of_mem _ ha)) hz
  · have hne : Nat.digits 3 (2^k) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by positivity)
    have hl : (Nat.digits 3 (2^k)).getLast hne = 1 := by
      have hh := hg (List.getLast_mem hne)
      have hz' := Nat.getLast_digit_ne_zero 3 (by positivity : 2^k ≠ 0)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
      tauto
    have he := List.dropLast_append_getLast hne
    rw [hl] at he
    apply upper_root_bound z (Nat.digits 3 (2^k)).dropLast
      (fun a ha => hg (List.mem_of_mem_dropLast ha))
    rwa [he]

lemma sum_le_length {w : List ℕ} (hw : w ⊆ [0, 1]) : w.sum ≤ w.length := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd := hw (List.mem_cons_self ..)
    have ht := ih (fun a ha => hw (List.mem_cons_of_mem _ ha))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    simp only [List.sum_cons, List.length_cons]
    omega

lemma eval_one_digitPoly (w : List ℕ) :
    Polynomial.eval (1 : ℤ) (Nat.ofDigits (Polynomial.X : ℤ[X]) w) = (w.sum : ℤ) := by
  induction w with
  | nil => simp [Nat.ofDigits]
  | cons d w ih => simp [Nat.ofDigits, ih]

/-- Powers of X+1 cannot contribute linearly many factors: their value at one
already divides the digit sum. No bound for other irreducible factors follows. -/
lemma linear_factor_multiplicity_bound (w : List ℕ) (hw : w ⊆ [0, 1]) (r : ℕ)
    (hd : (Polynomial.X + 1 : ℤ[X])^r ∣ Nat.ofDigits (Polynomial.X : ℤ[X]) (1 :: w)) :
    2^r ≤ w.length + 1 := by
  have he := Polynomial.eval_dvd (x := (1 : ℤ)) hd
  rw [eval_one_digitPoly] at he
  norm_num only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, one_add_one_eq_two, List.sum_cons, Nat.cast_add,
    Nat.cast_one] at he
  have hn : 2^r ∣ 1+w.sum := by exact_mod_cast he
  have hle := Nat.le_of_dvd (by omega : 0 < 1+w.sum) hn
  have hs := sum_le_length hw
  omega

lemma exponential_degree_gap (D : ℕ) (hD : 29 ≤ D) :
    8^D * (D+1) < 9^D := by
  induction D, hD using Nat.le_induction with
  | base => norm_num
  | succ D hD ih =>
    calc
      8^(D+1)*(D+1+1) = 8^D * (8*(D+2)) := by rw [pow_succ]; ring
      _ ≤ 8^D * (9*(D+1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 9 * (8^D * (D+1)) := by ring
      _ < 9 * 9^D := by gcongr
      _ = 9^(D+1) := by rw [pow_succ]; ring

/-- A numerical cutoff from the proposed factorwise gap. The second hypothesis
is NOT proved here for arbitrary good powers or their noncyclotomic factors. -/
lemma degree_bound_of_factor_gap (D k r : ℕ)
    (hsize : 3^D ≤ 2^k) (hgap : 2*k ≤ 3*D+r) (hmult : 2^r ≤ D+1) :
    D ≤ 28 ∧ k ≤ 56 := by
  have hpow : 9^D ≤ 8^D*(D+1) := by
    calc
      9^D = (3^D)^2 := by rw [← pow_mul, Nat.mul_comm D 2, pow_mul]; norm_num
      _ ≤ (2^k)^2 := Nat.pow_le_pow_left hsize _
      _ = 2^(2*k) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ 2^(3*D+r) := Nat.pow_le_pow_right (by decide) hgap
      _ = 8^D*2^r := by rw [pow_add, pow_mul]; norm_num
      _ ≤ 8^D*(D+1) := Nat.mul_le_mul_left _ hmult
  have hD : D ≤ 28 := by
    by_contra hh
    exact (not_lt_of_ge hpow) (exponential_degree_gap D (by omega))
  have hr : r ≤ D := by
    have hh := Nat.lt_two_pow_self (n := r)
    omega
  exact ⟨hD, by omega⟩

#print axioms degree_bound_of_factor_gap
#print axioms linear_factor_multiplicity_bound
#print axioms lower_root_bound
#print axioms upper_root_bound
#print axioms good_power_digit_root_bounds
end Erdos406Newman
