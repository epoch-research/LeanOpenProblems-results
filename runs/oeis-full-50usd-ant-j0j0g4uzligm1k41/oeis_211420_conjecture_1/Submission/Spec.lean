import FormalConjectures.Util.ProblemImports

open Nat
open Finset

set_option maxHeartbeats 4000000

/--
A211420: $a(n) = \frac{(8n)! n!}{(4n)! (3n)! (2n)!}$
-/
def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

-- Defining the denominator product: $\prod_{k=0}^{r-1} (8n - (2k+1))$ in ℤ
/-- The denominator product $(8n - 1)(8n - 3) \cdots (8n - (2r - 1))$,
defined as $\prod_{k=0}^{r-1} (8n - (2k+1))$ in $\mathbb{Z}$. -/
def denominator_product (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ)) |>.prod

theorem keyfloor_base (q s t : ℤ) (hq : 0 < q) (hs0 : 0 ≤ s) (hsq : s < q)
    (ht0 : 0 ≤ t) (htq : t < q) :
    (2*s)/q + (3*s)/q + (4*s - t)/q ≤ (8*t)/q + s/q + (8*s - 2*t)/q := by
  have hsq0 : s / q = 0 := Int.ediv_eq_zero_of_lt hs0 hsq
  rw [hsq0, add_zero]
  rw [show (2*s)/q + (3*s)/q + (4*s - t)/q ≤ (8*t)/q + (8*s - 2*t)/q
        ↔ (2*s)/q + (3*s)/q + (4*s - t)/q - (8*s - 2*t)/q ≤ (8*t)/q from by omega,
     Int.le_ediv_iff_mul_le hq]
  set a2 := (2*s)/q with ha2
  set a3 := (3*s)/q with ha3
  set a4 := (4*s - t)/q with ha4
  set a82 := (8*s - 2*t)/q with ha82
  have e2 := Int.mul_ediv_add_emod (2*s) q
  have e3 := Int.mul_ediv_add_emod (3*s) q
  have e4 := Int.mul_ediv_add_emod (4*s - t) q
  have e82 := Int.mul_ediv_add_emod (8*s - 2*t) q
  have n2 := Int.emod_nonneg (2*s) (ne_of_gt hq)
  have n3 := Int.emod_nonneg (3*s) (ne_of_gt hq)
  have n4 := Int.emod_nonneg (4*s - t) (ne_of_gt hq)
  have n82 := Int.emod_nonneg (8*s - 2*t) (ne_of_gt hq)
  have l2 := Int.emod_lt_of_pos (2*s) hq
  have l3 := Int.emod_lt_of_pos (3*s) hq
  have l4 := Int.emod_lt_of_pos (4*s - t) hq
  have l82 := Int.emod_lt_of_pos (8*s - 2*t) hq
  rw [← ha2] at e2; rw [← ha3] at e3; rw [← ha4] at e4; rw [← ha82] at e82
  have b2l : 0 ≤ a2 := by rw [ha2]; apply Int.ediv_nonneg (by linarith) (le_of_lt hq)
  have b2u : a2 ≤ 1 := by rw [ha2, Int.ediv_le_iff_le_mul hq]; nlinarith
  have b3l : 0 ≤ a3 := by rw [ha3]; apply Int.ediv_nonneg (by linarith) (le_of_lt hq)
  have b3u : a3 ≤ 2 := by rw [ha3, Int.ediv_le_iff_le_mul hq]; nlinarith
  have b4l : -1 ≤ a4 := by rw [ha4, Int.le_ediv_iff_mul_le hq]; nlinarith
  have b4u : a4 ≤ 3 := by rw [ha4, Int.ediv_le_iff_le_mul hq]; nlinarith
  have rel1 : 2*a4 ≤ a82 := by nlinarith
  have rel2 : a82 ≤ 2*a4 + 1 := by nlinarith
  clear_value a2 a3 a4 a82
  interval_cases a2 <;> interval_cases a3 <;> interval_cases a4 <;> interval_cases a82 <;> omega

theorem keyfloor_int (q n r : ℤ) (hq : 0 < q) (hn : 0 ≤ n) (hr : 0 ≤ r) :
    (2*n)/q + (3*n)/q + (4*n - r)/q ≤ (8*r)/q + n/q + (8*n - 2*r)/q := by
  set A := n / q with hA
  set s := n % q with hs
  set B := r / q with hB
  set t := r % q with ht
  have hmodn : s + q * A = n := by rw [hs, hA]; exact Int.emod_add_ediv n q
  have hmodr : t + q * B = r := by rw [ht, hB]; exact Int.emod_add_ediv r q
  have hns : n = q * A + s := by omega
  have hrt : r = q * B + t := by omega
  have hs0 : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg n (ne_of_gt hq)
  have hsq : s < q := by rw [hs]; exact Int.emod_lt_of_pos n hq
  have ht0 : 0 ≤ t := by rw [ht]; exact Int.emod_nonneg r (ne_of_gt hq)
  have htq : t < q := by rw [ht]; exact Int.emod_lt_of_pos r hq
  have hB0 : 0 ≤ B := by rw [hB]; exact Int.ediv_nonneg hr (le_of_lt hq)
  have r2 : (2*n)/q = 2*A + (2*s)/q := by
    rw [show 2*n = 2*s + q*(2*A) by rw [hns]; ring, Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r3 : (3*n)/q = 3*A + (3*s)/q := by
    rw [show 3*n = 3*s + q*(3*A) by rw [hns]; ring, Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r4 : (4*n - r)/q = (4*A - B) + (4*s - t)/q := by
    rw [show 4*n - r = (4*s - t) + q*(4*A - B) by rw [hns, hrt]; ring,
       Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r8r : (8*r)/q = 8*B + (8*t)/q := by
    rw [show 8*r = 8*t + q*(8*B) by rw [hrt]; ring, Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have r82 : (8*n - 2*r)/q = (8*A - 2*B) + (8*s - 2*t)/q := by
    rw [show 8*n - 2*r = (8*s - 2*t) + q*(8*A - 2*B) by rw [hns, hrt]; ring,
       Int.add_mul_ediv_left _ _ (ne_of_gt hq)]; ring
  have hbase := keyfloor_base q s t hq hs0 hsq ht0 htq
  rw [r2, r3, r4, r8r, r82]
  have hsq0 : s / q = 0 := Int.ediv_eq_zero_of_lt hs0 hsq
  rw [hsq0, add_zero] at hbase
  linarith

open Nat in
theorem keyfloor_nat (q n r : ℕ) (hq : 0 < q) (hr : r ≤ 4*n) :
    2*n/q + 3*n/q + (4*n-r)/q ≤ 8*r/q + n/q + (8*n-2*r)/q := by
  have h2r : 2*r ≤ 8*n := by omega
  rw [← Nat.cast_le (α := ℤ)]
  push_cast [Int.natCast_ediv, Nat.cast_sub hr, Nat.cast_sub h2r]
  have := keyfloor_int q n r (by exact_mod_cast hq) (by positivity) (by positivity)
  convert this using 2 <;> ring

open Finset Nat in
theorem TARGET (n r : ℕ) (hr : r ≤ 4*n) :
    (2*n)! * (3*n)! * (4*n-r)! ∣ (8*r)! * n ! * (8*n-2*r)! := by
  have hf : ∀ m : ℕ, (m ! : ℕ) ≠ 0 := fun m => Nat.factorial_ne_zero m
  rw [← Nat.factorization_le_iff_dvd
      (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _))
      (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)), Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · set b := 8*n + 8*r + 1 with hb
    have hlt : ∀ k : ℕ, k ≤ 8*n+8*r → Nat.log p k < b := fun k hk =>
      lt_of_le_of_lt (Nat.log_le_self p k) (by omega)
    have f1 : ((2*n)!).factorization p = ∑ i ∈ Ico 1 b, 2*n/p^i :=
      Nat.factorization_factorial hp (hlt (2*n) (by omega))
    have f2 : ((3*n)!).factorization p = ∑ i ∈ Ico 1 b, 3*n/p^i :=
      Nat.factorization_factorial hp (hlt (3*n) (by omega))
    have f3 : ((4*n-r)!).factorization p = ∑ i ∈ Ico 1 b, (4*n-r)/p^i :=
      Nat.factorization_factorial hp (hlt (4*n-r) (by omega))
    have f4 : ((8*r)!).factorization p = ∑ i ∈ Ico 1 b, 8*r/p^i :=
      Nat.factorization_factorial hp (hlt (8*r) (by omega))
    have f5 : ((n)!).factorization p = ∑ i ∈ Ico 1 b, n/p^i :=
      Nat.factorization_factorial hp (hlt n (by omega))
    have f6 : ((8*n-2*r)!).factorization p = ∑ i ∈ Ico 1 b, (8*n-2*r)/p^i :=
      Nat.factorization_factorial hp (hlt (8*n-2*r) (by omega))
    rw [Nat.factorization_mul (mul_ne_zero (hf _) (hf _)) (hf _),
        Nat.factorization_mul (hf _) (hf _),
        Nat.factorization_mul (mul_ne_zero (hf _) (hf _)) (hf _),
        Nat.factorization_mul (hf _) (hf _)]
    simp only [Finsupp.coe_add, Pi.add_apply, f1, f2, f3, f4, f5, f6]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact keyfloor_nat (p^i) n r (pow_pos hp.pos i) hr
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

noncomputable def P (t : ℕ) : ℕ := ∏ k ∈ Finset.range t, (2*k+1)

theorem hP (t : ℕ) : P t * 2^t * t ! = (2*t)! := by
  induction t with
  | zero => simp [P]
  | succ m ih =>
    have hPs : P (m+1) = P m * (2*m+1) := by rw [P, Finset.prod_range_succ, ← P]
    have e : (2*(m+1))! = (2*m+2) * ((2*m+1) * (2*m)!) := by
      have h2 : 2*(m+1) = (2*m+1)+1 := by ring
      rw [h2, Nat.factorial_succ, Nat.factorial_succ]
    rw [hPs, e, Nat.factorial_succ, pow_succ, ← ih]; ring

theorem dp_succ (n m : ℕ) :
    denominator_product n (m+1) = denominator_product n m * ((8*n:ℤ)-(2*m+1)) := by
  simp only [denominator_product, List.range_succ, List.map_append, List.prod_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem dp_eq (n r : ℕ) :
    denominator_product n r = ∏ k ∈ Finset.range r, ((8*n:ℤ)-(2*k+1)) := by
  induction r with
  | zero => simp [denominator_product]
  | succ m ih => rw [dp_succ, ih, Finset.prod_range_succ]

theorem IdAZ (n : ℕ) : ∀ r, r ≤ 4*n →
    ((8*n).factorial : ℤ) * ((4*n-r).factorial : ℤ)
      = denominator_product n r * (2:ℤ)^r * ((4*n).factorial : ℤ) * ((8*n-2*r).factorial : ℤ) := by
  intro r
  induction r with
  | zero => intro _; simp [denominator_product]; ring
  | succ m ih =>
    intro hr
    have hm : m ≤ 4*n := by omega
    have IH := ih hm
    have e1 : ((4*n-m).factorial : ℤ) = ((4*n:ℤ)-m) * ((4*n-(m+1)).factorial : ℤ) := by
      have hnat : (4*n-m).factorial = (4*n-m) * (4*n-(m+1)).factorial := by
        obtain ⟨b, hb⟩ : ∃ b, 4*n-m = b+1 := ⟨4*n-m-1, by omega⟩
        have h2 : 4*n-(m+1) = b := by omega
        rw [hb, h2, Nat.factorial_succ]
      rw [hnat]; push_cast [Nat.cast_sub (show m ≤ 4*n by omega)]; ring
    have e2 : ((8*n-2*m).factorial : ℤ)
        = ((8*n:ℤ)-2*m) * (((8*n:ℤ)-2*m-1) * ((8*n-2*(m+1)).factorial : ℤ)) := by
      have hnat : (8*n-2*m).factorial
          = (8*n-2*m) * ((8*n-2*m-1) * (8*n-2*(m+1)).factorial) := by
        obtain ⟨b, hb⟩ : ∃ b, 8*n-2*m = b+2 := ⟨8*n-2*m-2, by omega⟩
        have h1 : 8*n-2*m-1 = b+1 := by omega
        have h2 : 8*n-2*(m+1) = b := by omega
        rw [h1, h2, hb, Nat.factorial_succ, Nat.factorial_succ]
      rw [hnat]
      push_cast [Nat.cast_sub (show 2*m ≤ 8*n by omega),
                 Nat.cast_sub (show 1 ≤ 8*n-2*m by omega)]
      ring
    rw [dp_succ]
    have hx : ((4*n:ℤ) - m) ≠ 0 := sub_ne_zero.mpr (by
      have hlt : (m:ℤ) < (4*n:ℤ) := by exact_mod_cast (show m < 4*n by omega)
      exact (ne_of_lt hlt).symm)
    apply mul_right_cancel₀ hx
    rw [e1, e2] at IH
    linear_combination IH

theorem a_int (n : ℕ) : (4*n)! * (3*n)! * (2*n)! ∣ (8*n)! * n ! := by
  have h := TARGET n 0 (by omega)
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.factorial_zero, one_mul] at h
  calc (4*n)! * (3*n)! * (2*n)! = (2*n)! * (3*n)! * (4*n)! := by ring
    _ ∣ n ! * (8*n)! := h
    _ = (8*n)! * n ! := by ring

theorem a_eq (n : ℕ) : a n * ((4*n)! * (3*n)! * (2*n)!) = (8*n)! * n ! := by
  unfold a
  exact Nat.div_mul_cancel (a_int n)

theorem natAbs_prod_range (f : ℕ → ℤ) (r : ℕ) :
    (∏ i ∈ Finset.range r, f i).natAbs = ∏ i ∈ Finset.range r, (f i).natAbs := by
  induction r with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, Finset.prod_range_succ, Int.natAbs_mul, ih]


/--
A211420: It also appears that a(n) is divisible by 8*n - 1 for all n. More generally, we
conjecture that there are constants K(r), r >= 0, such that
$a(n) \cdot K(r)/((8*n - 1)*(8*n - 3)*...*(8*n - (2*r+1)))$ is an integer for all n.
-/
theorem oeis_211420_conjecture_1 : ∀ r : ℕ, ∃ K : ℤ, K > 0 ∧ ∀ n : ℕ,
    denominator_product n r ∣ (a n : ℤ) * K := by
  intro r
  refine ⟨((8*r)! : ℤ), by exact_mod_cast Nat.factorial_pos (8*r), ?_⟩
  intro n
  by_cases hcase : r ≤ 4*n
  · -- main case
    obtain ⟨M, hM⟩ := TARGET n r hcase
    have H1 : (a n:ℤ) * (((4*n).factorial:ℤ)*((3*n).factorial:ℤ)*((2*n).factorial:ℤ))
        = ((8*n).factorial:ℤ)*(n.factorial:ℤ) := by exact_mod_cast a_eq n
    have H3 : ((8*r).factorial:ℤ)*(n.factorial:ℤ)*((8*n-2*r).factorial:ℤ)
        = ((2*n).factorial:ℤ)*((3*n).factorial:ℤ)*((4*n-r).factorial:ℤ)*(M:ℤ) := by
      exact_mod_cast hM
    have H2 := IdAZ n r hcase
    have hne : (((4*n).factorial:ℤ)*(n.factorial:ℤ)*((8*n-2*r).factorial:ℤ)) ≠ 0 := by
      have h := mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero (4*n)) (Nat.factorial_ne_zero n))
        (Nat.factorial_ne_zero (8*n-2*r))
      exact_mod_cast h
    refine ⟨(2:ℤ)^r * (M:ℤ), ?_⟩
    apply mul_right_cancel₀ hne
    linear_combination ((a n:ℤ) * ((4*n).factorial:ℤ)) * H3
      + (((4*n-r).factorial:ℤ) * (M:ℤ)) * H1
      + ((n.factorial:ℤ) * (M:ℤ)) * H2
  · -- small case: 4*n < r
    push_neg at hcase
    have hfirst : ∏ i ∈ Finset.range (4*n), ((8*n:ℤ)-(2*i+1)).natAbs = P (4*n) := by
      rw [P, ← Finset.prod_range_reflect (fun j => 2*j+1) (4*n)]
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hc : ((8*n:ℤ)-(2*i+1)) = ((8*n-(2*i+1) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub (show 2*i+1 ≤ 8*n by omega)]; ring
      rw [hc, Int.natAbs_natCast]; omega
    have hsecond : ∏ i ∈ Finset.range (r-4*n), ((8*n:ℤ)-(2*(4*n+i)+1)).natAbs = P (r-4*n) := by
      rw [P]
      apply Finset.prod_congr rfl
      intro i hi
      have hc : ((8*n:ℤ)-(2*(4*n+i)+1)) = -((2*i+1 : ℕ):ℤ) := by push_cast; ring
      rw [hc, Int.natAbs_neg, Int.natAbs_natCast]
    have key : ∏ k ∈ Finset.range r, ((8*n:ℤ)-(2*k+1)).natAbs = P (4*n) * P (r-4*n) := by
      have hr2 : r = 4*n + (r-4*n) := by omega
      calc ∏ k ∈ Finset.range r, ((8*n:ℤ)-(2*k+1)).natAbs
          = ∏ k ∈ Finset.range (4*n+(r-4*n)), ((8*n:ℤ)-(2*k+1)).natAbs := by rw [← hr2]
        _ = (∏ k ∈ Finset.range (4*n), ((8*n:ℤ)-(2*k+1)).natAbs)
            * (∏ i ∈ Finset.range (r-4*n), ((8*n:ℤ)-(2*(4*n+i)+1)).natAbs) :=
              Finset.prod_range_add _ (4*n) (r-4*n)
        _ = P (4*n) * P (r-4*n) := by rw [hfirst, hsecond]
    have hnat : (denominator_product n r).natAbs = P (4*n) * P (r-4*n) := by
      rw [dp_eq, natAbs_prod_range]; exact key
    have hd2 : P (4*n) * P (r-4*n) ∣ (8*r)! := by
      have hPdvd : ∀ t, P t ∣ (2*t)! := fun t => ⟨2^t * t.factorial, by rw [← hP t]; ring⟩
      have h1 : P (4*n) ∣ (8*n)! := by
        have := hPdvd (4*n); rwa [show 2*(4*n) = 8*n from by ring] at this
      have h2 : P (r-4*n) ∣ (2*(r-4*n))! := hPdvd (r-4*n)
      have hmul : P (4*n) * P (r-4*n) ∣ (8*n)! * (2*(r-4*n))! := mul_dvd_mul h1 h2
      have hadd : (8*n)! * (2*(r-4*n))! ∣ (8*n + 2*(r-4*n))! :=
        Nat.factorial_mul_factorial_dvd_factorial_add (8*n) (2*(r-4*n))
      rw [show 8*n + 2*(r-4*n) = 2*r from by omega] at hadd
      have hlast : (2*r)! ∣ (8*r)! := Nat.factorial_dvd_factorial (by omega)
      exact dvd_trans (dvd_trans hmul hadd) hlast
    have hdvd : denominator_product n r ∣ ((8*r).factorial : ℤ) := by
      rw [← Int.natAbs_dvd, hnat]
      exact_mod_cast hd2
    exact dvd_mul_of_dvd_right hdvd (a n:ℤ)

