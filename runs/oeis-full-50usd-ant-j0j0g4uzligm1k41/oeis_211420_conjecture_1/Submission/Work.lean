import Mathlib
open Finset Nat
set_option maxHeartbeats 4000000

def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

def denominator_product (n r : ℕ) : ℤ :=
  (List.range r).map (fun k : ℕ => (8 * n : ℤ) - (2 * k + 1 : ℤ)) |>.prod

-- Heavy lemma proven elsewhere
axiom TARGET (n r : ℕ) (hr : r ≤ 4*n) :
    (2*n)! * (3*n)! * (4*n-r)! ∣ (8*r)! * n ! * (8*n-2*r)!

-- P: product of first t odd numbers
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

theorem final : ∀ r : ℕ, ∃ K : ℤ, K > 0 ∧ ∀ n : ℕ,
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
