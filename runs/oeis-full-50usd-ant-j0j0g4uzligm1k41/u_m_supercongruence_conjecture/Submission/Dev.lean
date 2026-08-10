import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

noncomputable def u (m n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    (range (m * n + 1)).sum fun k : ℕ =>
      let term_q : ℚ := (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ)
      (Rat.floor term_q).toNat

/-- The integer value of the k-th term (c_k(n)). -/
def cval (n k : ℕ) : ℕ :=
  if k = 0 then 1 else (n + 2 * k).choose k - 2 * (n + 2 * k - 1).choose (k - 1)

-- key binomial identity: (n+2k) * C(n+2k-1, k-1) = k * C(n+2k, k)  for k ≥ 1
theorem key_id (n j : ℕ) :
    (n + 2 * (j+1)) * (n + 2 * (j+1) - 1).choose ((j+1) - 1)
      = (j+1) * (n + 2 * (j+1)).choose (j+1) := by
  have e1 : n + 2 * (j+1) - 1 = n + 2 * j + 1 := by omega
  have e2 : (j+1) - 1 = j := by omega
  have e3 : n + 2 * (j+1) = (n + 2 * j + 1) + 1 := by ring
  rw [e1, e2, e3, Nat.add_one_mul_choose_eq]
  ring

-- 2 * C(n+2k-1,k-1) ≤ C(n+2k,k) for k ≥ 1
theorem two_le (n j : ℕ) :
    2 * (n + 2 * (j+1) - 1).choose ((j+1) - 1) ≤ (n + 2 * (j+1)).choose (j+1) := by
  have hk := key_id n j
  set C := (n + 2 * (j+1)).choose (j+1) with hC
  set Cm := (n + 2 * (j+1) - 1).choose ((j+1) - 1) with hCm
  refine Nat.le_of_mul_le_mul_left (c := n + 2*(j+1)) ?_ (by omega)
  calc (n+2*(j+1)) * (2*Cm) = 2 * ((n+2*(j+1)) * Cm) := by ring
    _ = 2 * ((j+1) * C) := by rw [hk]
    _ = (2*(j+1)) * C := by ring
    _ ≤ (n+2*(j+1)) * C := by gcongr; omega

-- the rational term equals the integer cval (as a rational), for k ≥ 1
theorem ratterm_eq (n j : ℕ) (hn : 0 < n) :
    (n:ℚ)/(n+2*(j+1)) * ((n+2*(j+1)).choose (j+1) : ℚ) = (cval n (j+1) : ℚ) := by
  have hk := key_id n j
  have hkQ : ((n + 2 * (j+1) : ℕ) : ℚ) * ((n + 2 * (j+1) - 1).choose ((j+1) - 1) : ℚ)
      = ((j+1 : ℕ) : ℚ) * ((n + 2 * (j+1)).choose (j+1) : ℚ) := by
    exact_mod_cast hk
  have hden : ((n : ℚ) + 2*((j:ℚ)+1)) ≠ 0 := by positivity
  have hcval : cval n (j+1) = (n + 2 * (j+1)).choose (j+1) - 2 * (n + 2 * (j+1) - 1).choose ((j+1) - 1) := by
    rw [cval]; simp
  rw [hcval, Nat.cast_sub (two_le n j)]
  push_cast
  push_cast at hkQ
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  linear_combination 2 * hkQ

-- the rational term equals (cval : ℚ) for all k
theorem ratterm_all (n k : ℕ) (hn : 0 < n) :
    (n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ) = (cval n k : ℚ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [cval, if_pos, Nat.cast_zero, mul_zero, add_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [div_self hn']
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [← ratterm_eq n j hn]
    push_cast
    ring

-- The full floor term equals cval, as a natural number.
theorem floorterm_eq (n k : ℕ) (hn : 0 < n) :
    (Rat.floor ((n : ℚ) / (n + 2 * k : ℚ) * ((n + 2 * k).choose k : ℚ))).toNat = cval n k := by
  rw [ratterm_all n k hn,
    show Rat.floor ((cval n k : ℚ)) = ⌊((cval n k : ℚ))⌋ from rfl,
    Int.floor_natCast, Int.toNat_natCast]

-- Reformulation: u as the integer sum of cval.
theorem u_eq_sum (m n : ℕ) (hn : 0 < n) :
    u m n = ∑ k ∈ range (m * n + 1), cval n k := by
  rw [u, if_neg hn.ne']
  apply Finset.sum_congr rfl
  intro k _
  exact floorterm_eq n k hn


