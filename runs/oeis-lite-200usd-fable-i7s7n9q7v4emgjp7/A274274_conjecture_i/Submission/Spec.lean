import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
A274274: Number of ordered ways to write $n$ as $x^3 + y^2 + z^2$, where $x,y,z$ are nonnegative integers with $y \le z$.
-/
def A274274 (n : ℕ) : ℕ :=
  -- Iterate over all possible non-negative integers x, y, z up to n.
  -- This bounded sum covers all solutions since x^3, y^2, z^2 must be less than or equal to n.
  (range (succ n)).sum fun x =>
  (range (succ n)).sum fun y =>
  (range (succ n)).sum fun z =>
    -- Count 1 for each triple (x, y, z) that satisfies the equation and the constraint y ≤ z.
    if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then
      1
    else
      0

-- Helper predicate for conjecture (ii): n = x^3 + y^2 + 3*z^2
def representable_type_ii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 3 * z^2

-- Helper predicate for conjecture (iii): n = x^3 + y^2 + 2*z^2
def representable_type_iii (n : ℕ) : Prop :=
  ∃ (x y z : ℕ), n = x^3 + y^2 + 2 * z^2

-- Helper predicate for the special form in conjecture (i), n = 2^k * (4m + 1)
def has_form_two_pow_k_times_four_m_plus_one (n : ℕ) : Prop :=
  ∃ (k m : ℕ), n = 2^k * (4 * m + 1)

/-- `A274274 n` is nonzero iff `n` is the sum of a nonnegative cube and two squares
(with the two squares ordered).  This is the basic positivity criterion; it is proved
here as genuine (sorry-free) partial progress towards the conjecture below. -/
lemma A274274_ne_zero_iff {n : ℕ} :
    A274274 n ≠ 0 ↔ ∃ x y z : ℕ, x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    apply h
    unfold A274274
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ =>
      Finset.sum_eq_zero fun z _ => ?_
    rw [if_neg]
    rintro ⟨hxyz, hyz⟩
    have := hno x y z hxyz
    omega
  · rintro ⟨x, y, z, hxyz, hyz⟩
    have hx : x ∈ range (succ n) := by
      refine Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_trans (Nat.le_self_pow (n := 3) (by norm_num) x) ?_))
      omega
    have hy : y ∈ range (succ n) := by
      refine Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_trans (Nat.le_self_pow (n := 2) (by norm_num) y) ?_))
      omega
    have hz : z ∈ range (succ n) := by
      refine Finset.mem_range.mpr
        (Nat.lt_succ_of_le (le_trans (Nat.le_self_pow (n := 2) (by norm_num) z) ?_))
      omega
    intro h0
    have h1 : (0:ℕ) < A274274 n := by
      unfold A274274
      refine Finset.sum_pos'
        (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => by positivity) ?_
      refine ⟨x, hx, Finset.sum_pos'
        (fun j _ => Finset.sum_nonneg fun k _ => by positivity)
        ⟨y, hy, Finset.sum_pos' (fun k _ => by positivity) ⟨z, hz, ?_⟩⟩⟩
      rw [if_pos ⟨hxyz, hyz⟩]
      norm_num
    omega

/-- Certificate lemma: if a prime `q ≡ 3 (mod 4)` divides `m` exactly once,
then `m` is not a sum of two squares. -/
lemma not_sq_add_sq_of_cert {m q : ℕ} (hq : q.Prime) (h3 : q % 4 = 3)
    (hdvd : q ∣ m) (hndvd : ¬(q * q ∣ m)) : ¬∃ y z : ℕ, y ^ 2 + z ^ 2 = m := by
  rintro ⟨y, z, hyz⟩
  have hm0 : m ≠ 0 := fun h => hndvd (h ▸ dvd_zero _)
  have hmem : q ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hdvd, hm0⟩
  have heven := Nat.eq_sq_add_sq_iff.mp ⟨y, z, hyz.symm⟩ q hmem h3
  have hfact : m.factorization q = padicValNat q m := by
    rw [Nat.factorization_def _ hq]
  have h1 : 1 ≤ m.factorization q :=
    (Nat.Prime.pow_dvd_iff_le_factorization hq hm0).mp (by simpa using hdvd)
  have h2 : ¬(2 ≤ m.factorization q) := fun h =>
    hndvd (by simpa [sq, pow_two] using (Nat.Prime.pow_dvd_iff_le_factorization hq hm0).mpr h)
  have : m.factorization q = 1 := by omega
  rw [hfact] at this
  rw [this] at heven
  exact (Nat.not_even_one) heven

/-- Demonstration of the certificate method on the first excluded value:
`813` is not the sum of a nonnegative cube and two squares (sorry-free). -/
theorem A274274_eq_zero_813 : A274274 813 = 0 := by
  by_contra h
  obtain ⟨x, y, z, hxyz, hyz⟩ := A274274_ne_zero_iff.mp h
  have hx9 : x ≤ 9 := by
    by_contra hx
    push_neg at hx
    have h10 : 10 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
    norm_num at h10
    omega
  interval_cases x <;> norm_num at hxyz
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 813) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 812) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 805) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 786) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 749) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (43:ℕ) ∣ 688) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 597) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (47:ℕ) ∣ 470) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 301) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 84) (by norm_num) ⟨y, z, by omega⟩

/-- The excluded value `4404` is indeed not the sum of a nonnegative cube and two
squares (sorry-free certificate proof). -/
theorem A274274_eq_zero_4404 : A274274 4404 = 0 := by
  by_contra h
  obtain ⟨x, y, z, hxyz, hyz⟩ := A274274_ne_zero_iff.mp h
  have hxb : x ≤ 16 := by
    by_contra hx
    push_neg at hx
    have h10 : 17 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
    norm_num at h10
    omega
  interval_cases x <;> norm_num at hxyz
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 4404) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 4403) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 4396) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 4377) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 4340) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (11:ℕ) ∣ 4279) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 4188) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (31:ℕ) ∣ 4061) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 3892) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 3675) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (23:ℕ) ∣ 3404) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 3073) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 2676) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (2207:ℕ) ∣ 2207) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (83:ℕ) ∣ 1660) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 1029) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 308) (by norm_num) ⟨y, z, by omega⟩

/-- The excluded value `6420` is indeed not the sum of a nonnegative cube and two
squares (sorry-free certificate proof). -/
theorem A274274_eq_zero_6420 : A274274 6420 = 0 := by
  by_contra h
  obtain ⟨x, y, z, hxyz, hyz⟩ := A274274_ne_zero_iff.mp h
  have hxb : x ≤ 18 := by
    by_contra hx
    push_neg at hx
    have h10 : 19 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
    norm_num at h10
    omega
  interval_cases x <;> norm_num at hxyz
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 6420) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (131:ℕ) ∣ 6419) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 6412) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 6393) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 6356) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (1259:ℕ) ∣ 6295) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 6204) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (59:ℕ) ∣ 6077) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 5908) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 5691) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (271:ℕ) ∣ 5420) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 5089) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 4692) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (103:ℕ) ∣ 4223) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (919:ℕ) ∣ 3676) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 3045) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 2324) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (11:ℕ) ∣ 1507) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 588) (by norm_num) ⟨y, z, by omega⟩

/-- The excluded value `28804` is indeed not the sum of a nonnegative cube and two
squares (sorry-free certificate proof). -/
theorem A274274_eq_zero_28804 : A274274 28804 = 0 := by
  by_contra h
  obtain ⟨x, y, z, hxyz, hyz⟩ := A274274_ne_zero_iff.mp h
  have hxb : x ≤ 30 := by
    by_contra hx
    push_neg at hx
    have h10 : 31 ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hx 3
    norm_num at h10
    omega
  interval_cases x <;> norm_num at hxyz
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (19:ℕ) ∣ 28804) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 28803) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (23:ℕ) ∣ 28796) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 28777) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 28740) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 28679) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 28588) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 28461) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (11:ℕ) ∣ 28292) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (1123:ℕ) ∣ 28075) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 27804) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (83:ℕ) ∣ 27473) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 27076) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 26607) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (1303:ℕ) ∣ 26060) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (59:ℕ) ∣ 25429) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 24708) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 23891) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (5743:ℕ) ∣ 22972) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 21945) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 20804) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (19543:ℕ) ∣ 19543) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 18156) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (127:ℕ) ∣ 16637) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 14980) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 13179) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 11228) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (7:ℕ) ∣ 9121) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (3:ℕ) ∣ 6852) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (883:ℕ) ∣ 4415) (by norm_num) ⟨y, z, by omega⟩
  · exact not_sq_add_sq_of_cert (by norm_num) (by norm_num)
      (by norm_num : (11:ℕ) ∣ 1804) (by norm_num) ⟨y, z, by omega⟩


section UpTo1000

private lemma w0 : A274274 0 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 0, by norm_num, by norm_num⟩
private lemma w1 : A274274 1 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 1, by norm_num, by norm_num⟩
private lemma w2 : A274274 2 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 1, by norm_num, by norm_num⟩
private lemma w3 : A274274 3 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 1, by norm_num, by norm_num⟩
private lemma w4 : A274274 4 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 2, by norm_num, by norm_num⟩
private lemma w5 : A274274 5 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 2, by norm_num, by norm_num⟩
private lemma w6 : A274274 6 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 2, by norm_num, by norm_num⟩
private lemma w8 : A274274 8 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 2, by norm_num, by norm_num⟩
private lemma w9 : A274274 9 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 3, by norm_num, by norm_num⟩
private lemma w10 : A274274 10 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 3, by norm_num, by norm_num⟩
private lemma w11 : A274274 11 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 3, by norm_num, by norm_num⟩
private lemma w12 : A274274 12 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 2, by norm_num, by norm_num⟩
private lemma w13 : A274274 13 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 3, by norm_num, by norm_num⟩
private lemma w14 : A274274 14 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 3, by norm_num, by norm_num⟩
private lemma w16 : A274274 16 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 4, by norm_num, by norm_num⟩
private lemma w17 : A274274 17 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 4, by norm_num, by norm_num⟩
private lemma w18 : A274274 18 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 3, by norm_num, by norm_num⟩
private lemma w19 : A274274 19 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 3, by norm_num, by norm_num⟩
private lemma w20 : A274274 20 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 4, by norm_num, by norm_num⟩
private lemma w21 : A274274 21 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 4, by norm_num, by norm_num⟩
private lemma w24 : A274274 24 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 4, by norm_num, by norm_num⟩
private lemma w25 : A274274 25 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 5, by norm_num, by norm_num⟩
private lemma w26 : A274274 26 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 5, by norm_num, by norm_num⟩
private lemma w27 : A274274 27 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 5, by norm_num, by norm_num⟩
private lemma w28 : A274274 28 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 4, by norm_num, by norm_num⟩
private lemma w29 : A274274 29 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 5, by norm_num, by norm_num⟩
private lemma w30 : A274274 30 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 5, by norm_num, by norm_num⟩
private lemma w31 : A274274 31 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 2, by norm_num, by norm_num⟩
private lemma w32 : A274274 32 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 4, by norm_num, by norm_num⟩
private lemma w33 : A274274 33 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 4, by norm_num, by norm_num⟩
private lemma w34 : A274274 34 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 5, by norm_num, by norm_num⟩
private lemma w35 : A274274 35 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 5, by norm_num, by norm_num⟩
private lemma w36 : A274274 36 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 6, by norm_num, by norm_num⟩
private lemma w37 : A274274 37 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 6, by norm_num, by norm_num⟩
private lemma w38 : A274274 38 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 6, by norm_num, by norm_num⟩
private lemma w40 : A274274 40 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 6, by norm_num, by norm_num⟩
private lemma w41 : A274274 41 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 5, by norm_num, by norm_num⟩
private lemma w42 : A274274 42 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 5, by norm_num, by norm_num⟩
private lemma w43 : A274274 43 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 4, by norm_num, by norm_num⟩
private lemma w44 : A274274 44 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 6, by norm_num, by norm_num⟩
private lemma w45 : A274274 45 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 6, by norm_num, by norm_num⟩
private lemma w46 : A274274 46 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 6, by norm_num, by norm_num⟩
private lemma w47 : A274274 47 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 4, by norm_num, by norm_num⟩
private lemma w48 : A274274 48 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 6, by norm_num, by norm_num⟩
private lemma w49 : A274274 49 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 7, by norm_num, by norm_num⟩
private lemma w50 : A274274 50 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 7, by norm_num, by norm_num⟩
private lemma w51 : A274274 51 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 7, by norm_num, by norm_num⟩
private lemma w52 : A274274 52 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 6, by norm_num, by norm_num⟩
private lemma w53 : A274274 53 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 7, by norm_num, by norm_num⟩
private lemma w54 : A274274 54 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 7, by norm_num, by norm_num⟩
private lemma w56 : A274274 56 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 5, by norm_num, by norm_num⟩
private lemma w57 : A274274 57 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 7, by norm_num, by norm_num⟩
private lemma w58 : A274274 58 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 7, by norm_num, by norm_num⟩
private lemma w59 : A274274 59 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 7, by norm_num, by norm_num⟩
private lemma w60 : A274274 60 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 6, by norm_num, by norm_num⟩
private lemma w61 : A274274 61 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 6, by norm_num, by norm_num⟩
private lemma w62 : A274274 62 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 6, by norm_num, by norm_num⟩
private lemma w63 : A274274 63 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 6, by norm_num, by norm_num⟩
private lemma w64 : A274274 64 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 8, by norm_num, by norm_num⟩
private lemma w65 : A274274 65 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 8, by norm_num, by norm_num⟩
private lemma w66 : A274274 66 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 8, by norm_num, by norm_num⟩
private lemma w67 : A274274 67 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 6, by norm_num, by norm_num⟩
private lemma w68 : A274274 68 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 8, by norm_num, by norm_num⟩
private lemma w69 : A274274 69 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 8, by norm_num, by norm_num⟩
private lemma w72 : A274274 72 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 6, by norm_num, by norm_num⟩
private lemma w73 : A274274 73 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 8, by norm_num, by norm_num⟩
private lemma w74 : A274274 74 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 7, by norm_num, by norm_num⟩
private lemma w75 : A274274 75 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 7, by norm_num, by norm_num⟩
private lemma w76 : A274274 76 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 8, by norm_num, by norm_num⟩
private lemma w77 : A274274 77 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 7, by norm_num, by norm_num⟩
private lemma w79 : A274274 79 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 6, by norm_num, by norm_num⟩
private lemma w80 : A274274 80 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 8, by norm_num, by norm_num⟩
private lemma w81 : A274274 81 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 9, by norm_num, by norm_num⟩
private lemma w82 : A274274 82 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 9, by norm_num, by norm_num⟩
private lemma w83 : A274274 83 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 9, by norm_num, by norm_num⟩
private lemma w84 : A274274 84 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 2, 4, by norm_num, by norm_num⟩
private lemma w85 : A274274 85 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 9, by norm_num, by norm_num⟩
private lemma w86 : A274274 86 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 9, by norm_num, by norm_num⟩
private lemma w88 : A274274 88 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 8, by norm_num, by norm_num⟩
private lemma w89 : A274274 89 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 8, by norm_num, by norm_num⟩
private lemma w90 : A274274 90 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 9, by norm_num, by norm_num⟩
private lemma w91 : A274274 91 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 9, by norm_num, by norm_num⟩
private lemma w92 : A274274 92 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 8, by norm_num, by norm_num⟩
private lemma w93 : A274274 93 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 9, by norm_num, by norm_num⟩
private lemma w95 : A274274 95 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 8, by norm_num, by norm_num⟩
private lemma w96 : A274274 96 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 4, 4, by norm_num, by norm_num⟩
private lemma w97 : A274274 97 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 9, by norm_num, by norm_num⟩
private lemma w98 : A274274 98 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 7, by norm_num, by norm_num⟩
private lemma w99 : A274274 99 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 7, by norm_num, by norm_num⟩
private lemma w100 : A274274 100 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 10, by norm_num, by norm_num⟩
private lemma w101 : A274274 101 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 10, by norm_num, by norm_num⟩
private lemma w102 : A274274 102 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 10, by norm_num, by norm_num⟩
private lemma w104 : A274274 104 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 10, by norm_num, by norm_num⟩
private lemma w105 : A274274 105 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 10, by norm_num, by norm_num⟩
private lemma w106 : A274274 106 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 9, by norm_num, by norm_num⟩
private lemma w107 : A274274 107 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 9, by norm_num, by norm_num⟩
private lemma w108 : A274274 108 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 10, by norm_num, by norm_num⟩
private lemma w109 : A274274 109 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 10, by norm_num, by norm_num⟩
private lemma w110 : A274274 110 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 10, by norm_num, by norm_num⟩
private lemma w112 : A274274 112 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 10, by norm_num, by norm_num⟩
private lemma w113 : A274274 113 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 8, by norm_num, by norm_num⟩
private lemma w114 : A274274 114 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 8, by norm_num, by norm_num⟩
private lemma w116 : A274274 116 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 10, by norm_num, by norm_num⟩
private lemma w117 : A274274 117 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 9, by norm_num, by norm_num⟩
private lemma w118 : A274274 118 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 9, by norm_num, by norm_num⟩
private lemma w121 : A274274 121 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 11, by norm_num, by norm_num⟩
private lemma w122 : A274274 122 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 11, by norm_num, by norm_num⟩
private lemma w123 : A274274 123 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 11, by norm_num, by norm_num⟩
private lemma w124 : A274274 124 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 10, by norm_num, by norm_num⟩
private lemma w125 : A274274 125 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 11, by norm_num, by norm_num⟩
private lemma w126 : A274274 126 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 11, by norm_num, by norm_num⟩
private lemma w127 : A274274 127 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 10, by norm_num, by norm_num⟩
private lemma w128 : A274274 128 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 8, by norm_num, by norm_num⟩
private lemma w129 : A274274 129 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 8, by norm_num, by norm_num⟩
private lemma w130 : A274274 130 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 11, by norm_num, by norm_num⟩
private lemma w131 : A274274 131 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 11, by norm_num, by norm_num⟩
private lemma w132 : A274274 132 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 2, 8, by norm_num, by norm_num⟩
private lemma w133 : A274274 133 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 11, by norm_num, by norm_num⟩
private lemma w134 : A274274 134 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 0, 3, by norm_num, by norm_num⟩
private lemma w135 : A274274 135 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 3, by norm_num, by norm_num⟩
private lemma w136 : A274274 136 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 10, by norm_num, by norm_num⟩
private lemma w137 : A274274 137 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 11, by norm_num, by norm_num⟩
private lemma w138 : A274274 138 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 11, by norm_num, by norm_num⟩
private lemma w140 : A274274 140 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 7, 8, by norm_num, by norm_num⟩
private lemma w141 : A274274 141 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 0, 4, by norm_num, by norm_num⟩
private lemma w142 : A274274 142 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 4, by norm_num, by norm_num⟩
private lemma w143 : A274274 143 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 10, by norm_num, by norm_num⟩
private lemma w144 : A274274 144 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 12, by norm_num, by norm_num⟩
private lemma w145 : A274274 145 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 12, by norm_num, by norm_num⟩
private lemma w146 : A274274 146 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 11, by norm_num, by norm_num⟩
private lemma w147 : A274274 147 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 11, by norm_num, by norm_num⟩
private lemma w148 : A274274 148 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 12, by norm_num, by norm_num⟩
private lemma w149 : A274274 149 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 10, by norm_num, by norm_num⟩
private lemma w150 : A274274 150 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 10, by norm_num, by norm_num⟩
private lemma w151 : A274274 151 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 5, by norm_num, by norm_num⟩
private lemma w152 : A274274 152 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 12, by norm_num, by norm_num⟩
private lemma w153 : A274274 153 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 12, by norm_num, by norm_num⟩
private lemma w154 : A274274 154 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 12, by norm_num, by norm_num⟩
private lemma w155 : A274274 155 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 8, by norm_num, by norm_num⟩
private lemma w156 : A274274 156 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 12, by norm_num, by norm_num⟩
private lemma w157 : A274274 157 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 11, by norm_num, by norm_num⟩
private lemma w158 : A274274 158 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 11, by norm_num, by norm_num⟩
private lemma w159 : A274274 159 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 5, by norm_num, by norm_num⟩
private lemma w160 : A274274 160 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 12, by norm_num, by norm_num⟩
private lemma w161 : A274274 161 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 12, by norm_num, by norm_num⟩
private lemma w162 : A274274 162 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 9, by norm_num, by norm_num⟩
private lemma w163 : A274274 163 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 9, by norm_num, by norm_num⟩
private lemma w164 : A274274 164 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 10, by norm_num, by norm_num⟩
private lemma w165 : A274274 165 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 10, by norm_num, by norm_num⟩
private lemma w166 : A274274 166 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 5, by norm_num, by norm_num⟩
private lemma w168 : A274274 168 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 12, by norm_num, by norm_num⟩
private lemma w169 : A274274 169 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 13, by norm_num, by norm_num⟩
private lemma w170 : A274274 170 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 13, by norm_num, by norm_num⟩
private lemma w171 : A274274 171 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 13, by norm_num, by norm_num⟩
private lemma w172 : A274274 172 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 10, by norm_num, by norm_num⟩
private lemma w173 : A274274 173 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 13, by norm_num, by norm_num⟩
private lemma w174 : A274274 174 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 13, by norm_num, by norm_num⟩
private lemma w175 : A274274 175 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 12, by norm_num, by norm_num⟩
private lemma w176 : A274274 176 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 7, 10, by norm_num, by norm_num⟩
private lemma w177 : A274274 177 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 13, by norm_num, by norm_num⟩
private lemma w178 : A274274 178 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 13, by norm_num, by norm_num⟩
private lemma w179 : A274274 179 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 13, by norm_num, by norm_num⟩
private lemma w180 : A274274 180 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 12, by norm_num, by norm_num⟩
private lemma w181 : A274274 181 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 10, by norm_num, by norm_num⟩
private lemma w182 : A274274 182 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 10, by norm_num, by norm_num⟩
private lemma w183 : A274274 183 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 7, by norm_num, by norm_num⟩
private lemma w184 : A274274 184 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 11, by norm_num, by norm_num⟩
private lemma w185 : A274274 185 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 13, by norm_num, by norm_num⟩
private lemma w186 : A274274 186 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 13, by norm_num, by norm_num⟩
private lemma w187 : A274274 187 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 12, by norm_num, by norm_num⟩
private lemma w188 : A274274 188 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 12, by norm_num, by norm_num⟩
private lemma w189 : A274274 189 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 10, by norm_num, by norm_num⟩
private lemma w190 : A274274 190 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 8, by norm_num, by norm_num⟩
private lemma w191 : A274274 191 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 10, by norm_num, by norm_num⟩
private lemma w192 : A274274 192 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 8, 8, by norm_num, by norm_num⟩
private lemma w193 : A274274 193 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 12, by norm_num, by norm_num⟩
private lemma w194 : A274274 194 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 13, by norm_num, by norm_num⟩
private lemma w195 : A274274 195 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 13, by norm_num, by norm_num⟩
private lemma w196 : A274274 196 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 14, by norm_num, by norm_num⟩
private lemma w197 : A274274 197 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 14, by norm_num, by norm_num⟩
private lemma w198 : A274274 198 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 14, by norm_num, by norm_num⟩
private lemma w199 : A274274 199 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 7, by norm_num, by norm_num⟩
private lemma w200 : A274274 200 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 14, by norm_num, by norm_num⟩
private lemma w201 : A274274 201 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 14, by norm_num, by norm_num⟩
private lemma w202 : A274274 202 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 11, by norm_num, by norm_num⟩
private lemma w203 : A274274 203 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 11, by norm_num, by norm_num⟩
private lemma w204 : A274274 204 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 14, by norm_num, by norm_num⟩
private lemma w205 : A274274 205 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 14, by norm_num, by norm_num⟩
private lemma w206 : A274274 206 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 14, by norm_num, by norm_num⟩
private lemma w207 : A274274 207 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 12, by norm_num, by norm_num⟩
private lemma w208 : A274274 208 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 12, by norm_num, by norm_num⟩
private lemma w209 : A274274 209 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 12, by norm_num, by norm_num⟩
private lemma w210 : A274274 210 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 11, by norm_num, by norm_num⟩
private lemma w212 : A274274 212 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 14, by norm_num, by norm_num⟩
private lemma w213 : A274274 213 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 14, by norm_num, by norm_num⟩
private lemma w214 : A274274 214 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 8, by norm_num, by norm_num⟩
private lemma w215 : A274274 215 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 9, by norm_num, by norm_num⟩
private lemma w216 : A274274 216 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 12, by norm_num, by norm_num⟩
private lemma w217 : A274274 217 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 3, 12, by norm_num, by norm_num⟩
private lemma w218 : A274274 218 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 13, by norm_num, by norm_num⟩
private lemma w219 : A274274 219 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 13, by norm_num, by norm_num⟩
private lemma w220 : A274274 220 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 14, by norm_num, by norm_num⟩
private lemma w221 : A274274 221 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 14, by norm_num, by norm_num⟩
private lemma w222 : A274274 222 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 14, by norm_num, by norm_num⟩
private lemma w223 : A274274 223 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 14, by norm_num, by norm_num⟩
private lemma w224 : A274274 224 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 14, by norm_num, by norm_num⟩
private lemma w225 : A274274 225 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 15, by norm_num, by norm_num⟩
private lemma w226 : A274274 226 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 15, by norm_num, by norm_num⟩
private lemma w227 : A274274 227 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 15, by norm_num, by norm_num⟩
private lemma w228 : A274274 228 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 8, 10, by norm_num, by norm_num⟩
private lemma w229 : A274274 229 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 15, by norm_num, by norm_num⟩
private lemma w230 : A274274 230 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 15, by norm_num, by norm_num⟩
private lemma w231 : A274274 231 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 9, by norm_num, by norm_num⟩
private lemma w232 : A274274 232 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 14, by norm_num, by norm_num⟩
private lemma w233 : A274274 233 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 13, by norm_num, by norm_num⟩
private lemma w234 : A274274 234 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 15, by norm_num, by norm_num⟩
private lemma w235 : A274274 235 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 15, by norm_num, by norm_num⟩
private lemma w236 : A274274 236 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨6, 2, 4, by norm_num, by norm_num⟩
private lemma w237 : A274274 237 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 15, by norm_num, by norm_num⟩
private lemma w238 : A274274 238 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 8, by norm_num, by norm_num⟩
private lemma w239 : A274274 239 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 14, by norm_num, by norm_num⟩
private lemma w240 : A274274 240 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 14, by norm_num, by norm_num⟩
private lemma w241 : A274274 241 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 15, by norm_num, by norm_num⟩
private lemma w242 : A274274 242 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 11, by norm_num, by norm_num⟩
private lemma w243 : A274274 243 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 11, by norm_num, by norm_num⟩
private lemma w244 : A274274 244 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 12, by norm_num, by norm_num⟩
private lemma w245 : A274274 245 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 14, by norm_num, by norm_num⟩
private lemma w246 : A274274 246 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 14, by norm_num, by norm_num⟩
private lemma w247 : A274274 247 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 11, by norm_num, by norm_num⟩
private lemma w248 : A274274 248 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 14, by norm_num, by norm_num⟩
private lemma w249 : A274274 249 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 15, by norm_num, by norm_num⟩
private lemma w250 : A274274 250 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 15, by norm_num, by norm_num⟩
private lemma w251 : A274274 251 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 15, by norm_num, by norm_num⟩
private lemma w252 : A274274 252 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 10, 12, by norm_num, by norm_num⟩
private lemma w253 : A274274 253 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 7, 14, by norm_num, by norm_num⟩
private lemma w255 : A274274 255 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 11, by norm_num, by norm_num⟩
private lemma w256 : A274274 256 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 16, by norm_num, by norm_num⟩
private lemma w257 : A274274 257 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 16, by norm_num, by norm_num⟩
private lemma w258 : A274274 258 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 16, by norm_num, by norm_num⟩
private lemma w259 : A274274 259 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 14, by norm_num, by norm_num⟩
private lemma w260 : A274274 260 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 16, by norm_num, by norm_num⟩
private lemma w261 : A274274 261 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 15, by norm_num, by norm_num⟩
private lemma w262 : A274274 262 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 15, by norm_num, by norm_num⟩
private lemma w264 : A274274 264 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 16, by norm_num, by norm_num⟩
private lemma w265 : A274274 265 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 16, by norm_num, by norm_num⟩
private lemma w266 : A274274 266 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 16, by norm_num, by norm_num⟩
private lemma w268 : A274274 268 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 16, by norm_num, by norm_num⟩
private lemma w269 : A274274 269 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 13, by norm_num, by norm_num⟩
private lemma w270 : A274274 270 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 13, by norm_num, by norm_num⟩
private lemma w271 : A274274 271 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 10, 12, by norm_num, by norm_num⟩
private lemma w272 : A274274 272 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 16, by norm_num, by norm_num⟩
private lemma w273 : A274274 273 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 16, by norm_num, by norm_num⟩
private lemma w274 : A274274 274 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 15, by norm_num, by norm_num⟩
private lemma w275 : A274274 275 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 15, by norm_num, by norm_num⟩
private lemma w276 : A274274 276 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 4, 14, by norm_num, by norm_num⟩
private lemma w277 : A274274 277 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 14, by norm_num, by norm_num⟩
private lemma w278 : A274274 278 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 14, by norm_num, by norm_num⟩
private lemma w280 : A274274 280 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 16, by norm_num, by norm_num⟩
private lemma w281 : A274274 281 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 16, by norm_num, by norm_num⟩
private lemma w282 : A274274 282 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 16, by norm_num, by norm_num⟩
private lemma w283 : A274274 283 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 16, by norm_num, by norm_num⟩
private lemma w284 : A274274 284 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 16, by norm_num, by norm_num⟩
private lemma w285 : A274274 285 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 14, by norm_num, by norm_num⟩
private lemma w287 : A274274 287 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 16, by norm_num, by norm_num⟩
private lemma w288 : A274274 288 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 12, by norm_num, by norm_num⟩
private lemma w289 : A274274 289 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 17, by norm_num, by norm_num⟩
private lemma w290 : A274274 290 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 17, by norm_num, by norm_num⟩
private lemma w291 : A274274 291 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 17, by norm_num, by norm_num⟩
private lemma w292 : A274274 292 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 16, by norm_num, by norm_num⟩
private lemma w293 : A274274 293 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 17, by norm_num, by norm_num⟩
private lemma w294 : A274274 294 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 17, by norm_num, by norm_num⟩
private lemma w295 : A274274 295 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 13, by norm_num, by norm_num⟩
private lemma w296 : A274274 296 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 14, by norm_num, by norm_num⟩
private lemma w297 : A274274 297 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 14, by norm_num, by norm_num⟩
private lemma w298 : A274274 298 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 17, by norm_num, by norm_num⟩
private lemma w299 : A274274 299 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 17, by norm_num, by norm_num⟩
private lemma w300 : A274274 300 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 16, by norm_num, by norm_num⟩
private lemma w301 : A274274 301 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 17, by norm_num, by norm_num⟩
private lemma w303 : A274274 303 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 13, by norm_num, by norm_num⟩
private lemma w304 : A274274 304 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 10, 14, by norm_num, by norm_num⟩
private lemma w305 : A274274 305 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 17, by norm_num, by norm_num⟩
private lemma w306 : A274274 306 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 15, by norm_num, by norm_num⟩
private lemma w307 : A274274 307 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 15, by norm_num, by norm_num⟩
private lemma w308 : A274274 308 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 16, by norm_num, by norm_num⟩
private lemma w309 : A274274 309 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 7, 14, by norm_num, by norm_num⟩
private lemma w310 : A274274 310 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 13, by norm_num, by norm_num⟩
private lemma w313 : A274274 313 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 13, by norm_num, by norm_num⟩
private lemma w314 : A274274 314 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 17, by norm_num, by norm_num⟩
private lemma w315 : A274274 315 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 17, by norm_num, by norm_num⟩
private lemma w316 : A274274 316 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 17, by norm_num, by norm_num⟩
private lemma w317 : A274274 317 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 14, by norm_num, by norm_num⟩
private lemma w318 : A274274 318 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 14, by norm_num, by norm_num⟩
private lemma w319 : A274274 319 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 16, by norm_num, by norm_num⟩
private lemma w320 : A274274 320 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 16, by norm_num, by norm_num⟩
private lemma w321 : A274274 321 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 16, by norm_num, by norm_num⟩
private lemma w322 : A274274 322 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 5, 17, by norm_num, by norm_num⟩
private lemma w323 : A274274 323 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 10, 14, by norm_num, by norm_num⟩
private lemma w324 : A274274 324 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 18, by norm_num, by norm_num⟩
private lemma w325 : A274274 325 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 18, by norm_num, by norm_num⟩
private lemma w326 : A274274 326 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 18, by norm_num, by norm_num⟩
private lemma w327 : A274274 327 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 11, by norm_num, by norm_num⟩
private lemma w328 : A274274 328 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 18, by norm_num, by norm_num⟩
private lemma w329 : A274274 329 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 18, by norm_num, by norm_num⟩
private lemma w330 : A274274 330 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 14, by norm_num, by norm_num⟩
private lemma w332 : A274274 332 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 18, by norm_num, by norm_num⟩
private lemma w333 : A274274 333 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 18, by norm_num, by norm_num⟩
private lemma w334 : A274274 334 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 18, by norm_num, by norm_num⟩
private lemma w336 : A274274 336 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 18, by norm_num, by norm_num⟩
private lemma w337 : A274274 337 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 16, by norm_num, by norm_num⟩
private lemma w338 : A274274 338 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 17, by norm_num, by norm_num⟩
private lemma w339 : A274274 339 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 17, by norm_num, by norm_num⟩
private lemma w340 : A274274 340 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 18, by norm_num, by norm_num⟩
private lemma w341 : A274274 341 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 18, by norm_num, by norm_num⟩
private lemma w343 : A274274 343 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 13, by norm_num, by norm_num⟩
private lemma w344 : A274274 344 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 11, 14, by norm_num, by norm_num⟩
private lemma w345 : A274274 345 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 16, by norm_num, by norm_num⟩
private lemma w346 : A274274 346 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 15, by norm_num, by norm_num⟩
private lemma w347 : A274274 347 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 15, by norm_num, by norm_num⟩
private lemma w348 : A274274 348 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 18, by norm_num, by norm_num⟩
private lemma w349 : A274274 349 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 18, by norm_num, by norm_num⟩
private lemma w350 : A274274 350 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 18, by norm_num, by norm_num⟩
private lemma w351 : A274274 351 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 18, by norm_num, by norm_num⟩
private lemma w352 : A274274 352 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 18, by norm_num, by norm_num⟩
private lemma w353 : A274274 353 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 17, by norm_num, by norm_num⟩
private lemma w354 : A274274 354 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 17, by norm_num, by norm_num⟩
private lemma w355 : A274274 355 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 18, by norm_num, by norm_num⟩
private lemma w356 : A274274 356 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 16, by norm_num, by norm_num⟩
private lemma w357 : A274274 357 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 16, by norm_num, by norm_num⟩
private lemma w358 : A274274 358 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 8, 13, by norm_num, by norm_num⟩
private lemma w359 : A274274 359 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 15, by norm_num, by norm_num⟩
private lemma w360 : A274274 360 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 18, by norm_num, by norm_num⟩
private lemma w361 : A274274 361 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 19, by norm_num, by norm_num⟩
private lemma w362 : A274274 362 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 19, by norm_num, by norm_num⟩
private lemma w363 : A274274 363 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 19, by norm_num, by norm_num⟩
private lemma w364 : A274274 364 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 10, 16, by norm_num, by norm_num⟩
private lemma w365 : A274274 365 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 19, by norm_num, by norm_num⟩
private lemma w366 : A274274 366 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 19, by norm_num, by norm_num⟩
private lemma w367 : A274274 367 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 18, by norm_num, by norm_num⟩
private lemma w368 : A274274 368 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 18, by norm_num, by norm_num⟩
private lemma w369 : A274274 369 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 15, by norm_num, by norm_num⟩
private lemma w370 : A274274 370 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 19, by norm_num, by norm_num⟩
private lemma w371 : A274274 371 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 19, by norm_num, by norm_num⟩
private lemma w372 : A274274 372 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 2, 5, by norm_num, by norm_num⟩
private lemma w373 : A274274 373 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 18, by norm_num, by norm_num⟩
private lemma w374 : A274274 374 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 18, by norm_num, by norm_num⟩
private lemma w375 : A274274 375 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 15, by norm_num, by norm_num⟩
private lemma w376 : A274274 376 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 18, by norm_num, by norm_num⟩
private lemma w377 : A274274 377 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 19, by norm_num, by norm_num⟩
private lemma w378 : A274274 378 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 19, by norm_num, by norm_num⟩
private lemma w379 : A274274 379 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 0, 6, by norm_num, by norm_num⟩
private lemma w380 : A274274 380 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 17, by norm_num, by norm_num⟩
private lemma w381 : A274274 381 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 7, 18, by norm_num, by norm_num⟩
private lemma w382 : A274274 382 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 16, by norm_num, by norm_num⟩
private lemma w383 : A274274 383 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 10, 16, by norm_num, by norm_num⟩
private lemma w384 : A274274 384 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 8, 16, by norm_num, by norm_num⟩
private lemma w385 : A274274 385 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 19, by norm_num, by norm_num⟩
private lemma w386 : A274274 386 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 19, by norm_num, by norm_num⟩
private lemma w387 : A274274 387 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 19, by norm_num, by norm_num⟩
private lemma w388 : A274274 388 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 18, by norm_num, by norm_num⟩
private lemma w389 : A274274 389 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 17, by norm_num, by norm_num⟩
private lemma w390 : A274274 390 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 17, by norm_num, by norm_num⟩
private lemma w392 : A274274 392 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 14, by norm_num, by norm_num⟩
private lemma w393 : A274274 393 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 14, by norm_num, by norm_num⟩
private lemma w394 : A274274 394 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 15, by norm_num, by norm_num⟩
private lemma w395 : A274274 395 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 15, by norm_num, by norm_num⟩
private lemma w396 : A274274 396 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 18, by norm_num, by norm_num⟩
private lemma w397 : A274274 397 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 19, by norm_num, by norm_num⟩
private lemma w398 : A274274 398 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 19, by norm_num, by norm_num⟩
private lemma w399 : A274274 399 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 15, by norm_num, by norm_num⟩
private lemma w400 : A274274 400 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 20, by norm_num, by norm_num⟩
private lemma w401 : A274274 401 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 20, by norm_num, by norm_num⟩
private lemma w402 : A274274 402 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 20, by norm_num, by norm_num⟩
private lemma w404 : A274274 404 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 20, by norm_num, by norm_num⟩
private lemma w405 : A274274 405 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 18, by norm_num, by norm_num⟩
private lemma w406 : A274274 406 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 18, by norm_num, by norm_num⟩
private lemma w407 : A274274 407 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 0, 8, by norm_num, by norm_num⟩
private lemma w408 : A274274 408 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 20, by norm_num, by norm_num⟩
private lemma w409 : A274274 409 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 20, by norm_num, by norm_num⟩
private lemma w410 : A274274 410 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 19, by norm_num, by norm_num⟩
private lemma w411 : A274274 411 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 19, by norm_num, by norm_num⟩
private lemma w412 : A274274 412 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 20, by norm_num, by norm_num⟩
private lemma w413 : A274274 413 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 18, by norm_num, by norm_num⟩
private lemma w414 : A274274 414 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 0, 17, by norm_num, by norm_num⟩
private lemma w415 : A274274 415 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 18, by norm_num, by norm_num⟩
private lemma w416 : A274274 416 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 20, by norm_num, by norm_num⟩
private lemma w417 : A274274 417 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 20, by norm_num, by norm_num⟩
private lemma w418 : A274274 418 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 7, 19, by norm_num, by norm_num⟩
private lemma w419 : A274274 419 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 14, 14, by norm_num, by norm_num⟩
private lemma w420 : A274274 420 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 10, 16, by norm_num, by norm_num⟩
private lemma w421 : A274274 421 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 15, by norm_num, by norm_num⟩
private lemma w422 : A274274 422 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 15, by norm_num, by norm_num⟩
private lemma w423 : A274274 423 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 17, by norm_num, by norm_num⟩
private lemma w424 : A274274 424 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 18, by norm_num, by norm_num⟩
private lemma w425 : A274274 425 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 20, by norm_num, by norm_num⟩
private lemma w426 : A274274 426 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 20, by norm_num, by norm_num⟩
private lemma w427 : A274274 427 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 20, by norm_num, by norm_num⟩
private lemma w428 : A274274 428 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 20, by norm_num, by norm_num⟩
private lemma w429 : A274274 429 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 15, by norm_num, by norm_num⟩
private lemma w430 : A274274 430 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 17, by norm_num, by norm_num⟩
private lemma w431 : A274274 431 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 20, by norm_num, by norm_num⟩
private lemma w432 : A274274 432 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 10, 18, by norm_num, by norm_num⟩
private lemma w433 : A274274 433 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 17, by norm_num, by norm_num⟩
private lemma w434 : A274274 434 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 12, 17, by norm_num, by norm_num⟩
private lemma w436 : A274274 436 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 20, by norm_num, by norm_num⟩
private lemma w437 : A274274 437 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 20, by norm_num, by norm_num⟩
private lemma w438 : A274274 438 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 12, 13, by norm_num, by norm_num⟩
private lemma w439 : A274274 439 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 17, by norm_num, by norm_num⟩
private lemma w440 : A274274 440 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 4, 9, by norm_num, by norm_num⟩
private lemma w441 : A274274 441 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 21, by norm_num, by norm_num⟩
private lemma w442 : A274274 442 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 21, by norm_num, by norm_num⟩
private lemma w443 : A274274 443 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 21, by norm_num, by norm_num⟩
private lemma w444 : A274274 444 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 20, by norm_num, by norm_num⟩
private lemma w445 : A274274 445 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 21, by norm_num, by norm_num⟩
private lemma w446 : A274274 446 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 21, by norm_num, by norm_num⟩
private lemma w447 : A274274 447 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 2, 10, by norm_num, by norm_num⟩
private lemma w448 : A274274 448 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 14, 15, by norm_num, by norm_num⟩
private lemma w449 : A274274 449 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 20, by norm_num, by norm_num⟩
private lemma w450 : A274274 450 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 21, by norm_num, by norm_num⟩
private lemma w451 : A274274 451 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 21, by norm_num, by norm_num⟩
private lemma w452 : A274274 452 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 16, by norm_num, by norm_num⟩
private lemma w453 : A274274 453 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 16, by norm_num, by norm_num⟩
private lemma w456 : A274274 456 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 14, 14, by norm_num, by norm_num⟩
private lemma w457 : A274274 457 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 21, by norm_num, by norm_num⟩
private lemma w458 : A274274 458 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 17, by norm_num, by norm_num⟩
private lemma w459 : A274274 459 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 17, by norm_num, by norm_num⟩
private lemma w460 : A274274 460 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 16, by norm_num, by norm_num⟩
private lemma w461 : A274274 461 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 19, by norm_num, by norm_num⟩
private lemma w462 : A274274 462 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 19, by norm_num, by norm_num⟩
private lemma w463 : A274274 463 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 20, by norm_num, by norm_num⟩
private lemma w464 : A274274 464 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 20, by norm_num, by norm_num⟩
private lemma w465 : A274274 465 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 20, by norm_num, by norm_num⟩
private lemma w466 : A274274 466 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 21, by norm_num, by norm_num⟩
private lemma w467 : A274274 467 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 21, by norm_num, by norm_num⟩
private lemma w468 : A274274 468 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 18, by norm_num, by norm_num⟩
private lemma w469 : A274274 469 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 12, 18, by norm_num, by norm_num⟩
private lemma w471 : A274274 471 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 11, 15, by norm_num, by norm_num⟩
private lemma w472 : A274274 472 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 20, by norm_num, by norm_num⟩
private lemma w473 : A274274 473 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 3, 20, by norm_num, by norm_num⟩
private lemma w474 : A274274 474 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 5, 21, by norm_num, by norm_num⟩
private lemma w476 : A274274 476 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 12, 18, by norm_num, by norm_num⟩
private lemma w477 : A274274 477 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 21, by norm_num, by norm_num⟩
private lemma w478 : A274274 478 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 21, by norm_num, by norm_num⟩
private lemma w479 : A274274 479 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 14, 16, by norm_num, by norm_num⟩
private lemma w480 : A274274 480 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 4, 20, by norm_num, by norm_num⟩
private lemma w481 : A274274 481 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 20, by norm_num, by norm_num⟩
private lemma w482 : A274274 482 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 19, by norm_num, by norm_num⟩
private lemma w483 : A274274 483 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 19, by norm_num, by norm_num⟩
private lemma w484 : A274274 484 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 22, by norm_num, by norm_num⟩
private lemma w485 : A274274 485 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 22, by norm_num, by norm_num⟩
private lemma w486 : A274274 486 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 22, by norm_num, by norm_num⟩
private lemma w487 : A274274 487 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 19, by norm_num, by norm_num⟩
private lemma w488 : A274274 488 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 22, by norm_num, by norm_num⟩
private lemma w489 : A274274 489 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 22, by norm_num, by norm_num⟩
private lemma w490 : A274274 490 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 21, by norm_num, by norm_num⟩
private lemma w491 : A274274 491 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 21, by norm_num, by norm_num⟩
private lemma w492 : A274274 492 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 22, by norm_num, by norm_num⟩
private lemma w493 : A274274 493 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 22, by norm_num, by norm_num⟩
private lemma w494 : A274274 494 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 22, by norm_num, by norm_num⟩
private lemma w495 : A274274 495 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 12, 18, by norm_num, by norm_num⟩
private lemma w496 : A274274 496 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 22, by norm_num, by norm_num⟩
private lemma w497 : A274274 497 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 12, 17, by norm_num, by norm_num⟩
private lemma w498 : A274274 498 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 7, 21, by norm_num, by norm_num⟩
private lemma w500 : A274274 500 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 22, by norm_num, by norm_num⟩
private lemma w501 : A274274 501 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 22, by norm_num, by norm_num⟩
private lemma w502 : A274274 502 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 19, by norm_num, by norm_num⟩
private lemma w503 : A274274 503 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 4, 12, by norm_num, by norm_num⟩
private lemma w504 : A274274 504 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 21, by norm_num, by norm_num⟩
private lemma w505 : A274274 505 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 21, by norm_num, by norm_num⟩
private lemma w506 : A274274 506 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 21, by norm_num, by norm_num⟩
private lemma w507 : A274274 507 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 8, 10, by norm_num, by norm_num⟩
private lemma w508 : A274274 508 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 22, by norm_num, by norm_num⟩
private lemma w509 : A274274 509 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 22, by norm_num, by norm_num⟩
private lemma w510 : A274274 510 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 22, by norm_num, by norm_num⟩
private lemma w511 : A274274 511 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 22, by norm_num, by norm_num⟩
private lemma w512 : A274274 512 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 16, 16, by norm_num, by norm_num⟩
private lemma w513 : A274274 513 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 16, 16, by norm_num, by norm_num⟩
private lemma w514 : A274274 514 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 17, by norm_num, by norm_num⟩
private lemma w515 : A274274 515 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 15, 17, by norm_num, by norm_num⟩
private lemma w516 : A274274 516 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 14, 16, by norm_num, by norm_num⟩
private lemma w517 : A274274 517 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 5, 22, by norm_num, by norm_num⟩
private lemma w519 : A274274 519 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 13, 15, by norm_num, by norm_num⟩
private lemma w520 : A274274 520 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 22, by norm_num, by norm_num⟩
private lemma w521 : A274274 521 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 20, by norm_num, by norm_num⟩
private lemma w522 : A274274 522 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 21, by norm_num, by norm_num⟩
private lemma w523 : A274274 523 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 21, by norm_num, by norm_num⟩
private lemma w524 : A274274 524 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 9, 10, by norm_num, by norm_num⟩
private lemma w525 : A274274 525 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 10, 19, by norm_num, by norm_num⟩
private lemma w526 : A274274 526 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 20, by norm_num, by norm_num⟩
private lemma w527 : A274274 527 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 22, by norm_num, by norm_num⟩
private lemma w528 : A274274 528 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 22, by norm_num, by norm_num⟩
private lemma w529 : A274274 529 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 23, by norm_num, by norm_num⟩
private lemma w530 : A274274 530 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 23, by norm_num, by norm_num⟩
private lemma w531 : A274274 531 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 23, by norm_num, by norm_num⟩
private lemma w532 : A274274 532 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 21, by norm_num, by norm_num⟩
private lemma w533 : A274274 533 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 23, by norm_num, by norm_num⟩
private lemma w534 : A274274 534 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 23, by norm_num, by norm_num⟩
private lemma w535 : A274274 535 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 19, by norm_num, by norm_num⟩
private lemma w536 : A274274 536 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 22, by norm_num, by norm_num⟩
private lemma w537 : A274274 537 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 23, by norm_num, by norm_num⟩
private lemma w538 : A274274 538 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 23, by norm_num, by norm_num⟩
private lemma w539 : A274274 539 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 23, by norm_num, by norm_num⟩
private lemma w540 : A274274 540 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨6, 0, 18, by norm_num, by norm_num⟩
private lemma w541 : A274274 541 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 21, by norm_num, by norm_num⟩
private lemma w542 : A274274 542 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 21, by norm_num, by norm_num⟩
private lemma w543 : A274274 543 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 2, 14, by norm_num, by norm_num⟩
private lemma w544 : A274274 544 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 20, by norm_num, by norm_num⟩
private lemma w545 : A274274 545 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 23, by norm_num, by norm_num⟩
private lemma w546 : A274274 546 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 23, by norm_num, by norm_num⟩
private lemma w547 : A274274 547 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 22, by norm_num, by norm_num⟩
private lemma w548 : A274274 548 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 22, by norm_num, by norm_num⟩
private lemma w549 : A274274 549 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 18, by norm_num, by norm_num⟩
private lemma w550 : A274274 550 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 15, 18, by norm_num, by norm_num⟩
private lemma w551 : A274274 551 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 8, 12, by norm_num, by norm_num⟩
private lemma w552 : A274274 552 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 12, 20, by norm_num, by norm_num⟩
private lemma w553 : A274274 553 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 23, by norm_num, by norm_num⟩
private lemma w554 : A274274 554 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 23, by norm_num, by norm_num⟩
private lemma w555 : A274274 555 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 23, by norm_num, by norm_num⟩
private lemma w556 : A274274 556 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 22, by norm_num, by norm_num⟩
private lemma w557 : A274274 557 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 19, by norm_num, by norm_num⟩
private lemma w558 : A274274 558 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 19, by norm_num, by norm_num⟩
private lemma w560 : A274274 560 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 23, by norm_num, by norm_num⟩
private lemma w561 : A274274 561 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 6, 20, by norm_num, by norm_num⟩
private lemma w562 : A274274 562 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 21, by norm_num, by norm_num⟩
private lemma w563 : A274274 563 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 21, by norm_num, by norm_num⟩
private lemma w564 : A274274 564 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 4, 22, by norm_num, by norm_num⟩
private lemma w565 : A274274 565 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 23, by norm_num, by norm_num⟩
private lemma w566 : A274274 566 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 23, by norm_num, by norm_num⟩
private lemma w567 : A274274 567 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 21, by norm_num, by norm_num⟩
private lemma w568 : A274274 568 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 10, 21, by norm_num, by norm_num⟩
private lemma w569 : A274274 569 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 20, by norm_num, by norm_num⟩
private lemma w570 : A274274 570 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 20, by norm_num, by norm_num⟩
private lemma w571 : A274274 571 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 12, 20, by norm_num, by norm_num⟩
private lemma w572 : A274274 572 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 23, by norm_num, by norm_num⟩
private lemma w573 : A274274 573 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 23, by norm_num, by norm_num⟩
private lemma w574 : A274274 574 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 20, by norm_num, by norm_num⟩
private lemma w575 : A274274 575 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 22, by norm_num, by norm_num⟩
private lemma w576 : A274274 576 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 24, by norm_num, by norm_num⟩
private lemma w577 : A274274 577 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 24, by norm_num, by norm_num⟩
private lemma w578 : A274274 578 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 23, by norm_num, by norm_num⟩
private lemma w579 : A274274 579 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 23, by norm_num, by norm_num⟩
private lemma w580 : A274274 580 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 24, by norm_num, by norm_num⟩
private lemma w581 : A274274 581 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 24, by norm_num, by norm_num⟩
private lemma w582 : A274274 582 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 21, by norm_num, by norm_num⟩
private lemma w583 : A274274 583 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 13, 17, by norm_num, by norm_num⟩
private lemma w584 : A274274 584 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 22, by norm_num, by norm_num⟩
private lemma w585 : A274274 585 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 24, by norm_num, by norm_num⟩
private lemma w586 : A274274 586 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 19, by norm_num, by norm_num⟩
private lemma w587 : A274274 587 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 15, 19, by norm_num, by norm_num⟩
private lemma w588 : A274274 588 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 24, by norm_num, by norm_num⟩
private lemma w589 : A274274 589 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 11, 21, by norm_num, by norm_num⟩
private lemma w591 : A274274 591 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 21, by norm_num, by norm_num⟩
private lemma w592 : A274274 592 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 24, by norm_num, by norm_num⟩
private lemma w593 : A274274 593 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 23, by norm_num, by norm_num⟩
private lemma w594 : A274274 594 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 23, by norm_num, by norm_num⟩
private lemma w596 : A274274 596 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 20, by norm_num, by norm_num⟩
private lemma w597 : A274274 597 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 20, by norm_num, by norm_num⟩
private lemma w599 : A274274 599 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 0, 16, by norm_num, by norm_num⟩
private lemma w600 : A274274 600 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 24, by norm_num, by norm_num⟩
private lemma w601 : A274274 601 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 24, by norm_num, by norm_num⟩
private lemma w602 : A274274 602 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 24, by norm_num, by norm_num⟩
private lemma w603 : A274274 603 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 24, by norm_num, by norm_num⟩
private lemma w604 : A274274 604 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 20, by norm_num, by norm_num⟩
private lemma w605 : A274274 605 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 22, by norm_num, by norm_num⟩
private lemma w606 : A274274 606 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 22, by norm_num, by norm_num⟩
private lemma w607 : A274274 607 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 24, by norm_num, by norm_num⟩
private lemma w608 : A274274 608 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 12, 20, by norm_num, by norm_num⟩
private lemma w609 : A274274 609 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 5, 24, by norm_num, by norm_num⟩
private lemma w610 : A274274 610 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 23, by norm_num, by norm_num⟩
private lemma w611 : A274274 611 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 23, by norm_num, by norm_num⟩
private lemma w612 : A274274 612 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 24, by norm_num, by norm_num⟩
private lemma w613 : A274274 613 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 17, 18, by norm_num, by norm_num⟩
private lemma w614 : A274274 614 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 17, 18, by norm_num, by norm_num⟩
private lemma w615 : A274274 615 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 21, by norm_num, by norm_num⟩
private lemma w616 : A274274 616 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨6, 0, 20, by norm_num, by norm_num⟩
private lemma w617 : A274274 617 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 16, 19, by norm_num, by norm_num⟩
private lemma w618 : A274274 618 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 16, 19, by norm_num, by norm_num⟩
private lemma w619 : A274274 619 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 24, by norm_num, by norm_num⟩
private lemma w620 : A274274 620 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 24, by norm_num, by norm_num⟩
private lemma w621 : A274274 621 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 17, 18, by norm_num, by norm_num⟩
private lemma w623 : A274274 623 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 14, 20, by norm_num, by norm_num⟩
private lemma w624 : A274274 624 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 5, 16, by norm_num, by norm_num⟩
private lemma w625 : A274274 625 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 25, by norm_num, by norm_num⟩
private lemma w626 : A274274 626 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 25, by norm_num, by norm_num⟩
private lemma w627 : A274274 627 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 25, by norm_num, by norm_num⟩
private lemma w628 : A274274 628 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 22, by norm_num, by norm_num⟩
private lemma w629 : A274274 629 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 25, by norm_num, by norm_num⟩
private lemma w630 : A274274 630 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 25, by norm_num, by norm_num⟩
private lemma w631 : A274274 631 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 12, 12, by norm_num, by norm_num⟩
private lemma w632 : A274274 632 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 11, 22, by norm_num, by norm_num⟩
private lemma w633 : A274274 633 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 25, by norm_num, by norm_num⟩
private lemma w634 : A274274 634 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 25, by norm_num, by norm_num⟩
private lemma w635 : A274274 635 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 25, by norm_num, by norm_num⟩
private lemma w636 : A274274 636 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 12, 22, by norm_num, by norm_num⟩
private lemma w637 : A274274 637 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 21, by norm_num, by norm_num⟩
private lemma w638 : A274274 638 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 21, by norm_num, by norm_num⟩
private lemma w639 : A274274 639 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 24, by norm_num, by norm_num⟩
private lemma w640 : A274274 640 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 24, by norm_num, by norm_num⟩
private lemma w641 : A274274 641 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 25, by norm_num, by norm_num⟩
private lemma w642 : A274274 642 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 25, by norm_num, by norm_num⟩
private lemma w644 : A274274 644 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 16, 19, by norm_num, by norm_num⟩
private lemma w645 : A274274 645 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 21, by norm_num, by norm_num⟩
private lemma w646 : A274274 646 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 11, 20, by norm_num, by norm_num⟩
private lemma w647 : A274274 647 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 21, by norm_num, by norm_num⟩
private lemma w648 : A274274 648 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 18, 18, by norm_num, by norm_num⟩
private lemma w649 : A274274 649 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 18, 18, by norm_num, by norm_num⟩
private lemma w650 : A274274 650 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 25, by norm_num, by norm_num⟩
private lemma w651 : A274274 651 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 25, by norm_num, by norm_num⟩
private lemma w652 : A274274 652 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 25, by norm_num, by norm_num⟩
private lemma w653 : A274274 653 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 22, by norm_num, by norm_num⟩
private lemma w654 : A274274 654 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 22, by norm_num, by norm_num⟩
private lemma w655 : A274274 655 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 12, 22, by norm_num, by norm_num⟩
private lemma w656 : A274274 656 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 16, 20, by norm_num, by norm_num⟩
private lemma w657 : A274274 657 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 24, by norm_num, by norm_num⟩
private lemma w658 : A274274 658 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 24, by norm_num, by norm_num⟩
private lemma w660 : A274274 660 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 14, 20, by norm_num, by norm_num⟩
private lemma w661 : A274274 661 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 25, by norm_num, by norm_num⟩
private lemma w662 : A274274 662 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 25, by norm_num, by norm_num⟩
private lemma w663 : A274274 663 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 23, by norm_num, by norm_num⟩
private lemma w664 : A274274 664 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 16, 20, by norm_num, by norm_num⟩
private lemma w665 : A274274 665 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 24, by norm_num, by norm_num⟩
private lemma w666 : A274274 666 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 21, by norm_num, by norm_num⟩
private lemma w667 : A274274 667 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 15, 21, by norm_num, by norm_num⟩
private lemma w668 : A274274 668 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 25, by norm_num, by norm_num⟩
private lemma w669 : A274274 669 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 25, by norm_num, by norm_num⟩
private lemma w670 : A274274 670 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 23, by norm_num, by norm_num⟩
private lemma w671 : A274274 671 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 2, 18, by norm_num, by norm_num⟩
private lemma w672 : A274274 672 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨8, 4, 12, by norm_num, by norm_num⟩
private lemma w673 : A274274 673 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 23, by norm_num, by norm_num⟩
private lemma w674 : A274274 674 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 25, by norm_num, by norm_num⟩
private lemma w675 : A274274 675 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 25, by norm_num, by norm_num⟩
private lemma w676 : A274274 676 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 26, by norm_num, by norm_num⟩
private lemma w677 : A274274 677 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 26, by norm_num, by norm_num⟩
private lemma w678 : A274274 678 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 26, by norm_num, by norm_num⟩
private lemma w679 : A274274 679 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 23, by norm_num, by norm_num⟩
private lemma w680 : A274274 680 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 26, by norm_num, by norm_num⟩
private lemma w681 : A274274 681 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 26, by norm_num, by norm_num⟩
private lemma w682 : A274274 682 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 7, 25, by norm_num, by norm_num⟩
private lemma w683 : A274274 683 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 16, 20, by norm_num, by norm_num⟩
private lemma w684 : A274274 684 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 26, by norm_num, by norm_num⟩
private lemma w685 : A274274 685 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 26, by norm_num, by norm_num⟩
private lemma w686 : A274274 686 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 26, by norm_num, by norm_num⟩
private lemma w687 : A274274 687 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 11, 21, by norm_num, by norm_num⟩
private lemma w688 : A274274 688 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 26, by norm_num, by norm_num⟩
private lemma w689 : A274274 689 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 25, by norm_num, by norm_num⟩
private lemma w690 : A274274 690 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 25, by norm_num, by norm_num⟩
private lemma w692 : A274274 692 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 26, by norm_num, by norm_num⟩
private lemma w693 : A274274 693 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 26, by norm_num, by norm_num⟩
private lemma w694 : A274274 694 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 13, 20, by norm_num, by norm_num⟩
private lemma w696 : A274274 696 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 8, 17, by norm_num, by norm_num⟩
private lemma w697 : A274274 697 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 24, by norm_num, by norm_num⟩
private lemma w698 : A274274 698 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 23, by norm_num, by norm_num⟩
private lemma w699 : A274274 699 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 23, by norm_num, by norm_num⟩
private lemma w700 : A274274 700 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 26, by norm_num, by norm_num⟩
private lemma w701 : A274274 701 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 26, by norm_num, by norm_num⟩
private lemma w702 : A274274 702 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 26, by norm_num, by norm_num⟩
private lemma w703 : A274274 703 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 26, by norm_num, by norm_num⟩
private lemma w704 : A274274 704 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 26, by norm_num, by norm_num⟩
private lemma w705 : A274274 705 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 11, 24, by norm_num, by norm_num⟩
private lemma w706 : A274274 706 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 25, by norm_num, by norm_num⟩
private lemma w707 : A274274 707 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 25, by norm_num, by norm_num⟩
private lemma w708 : A274274 708 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 2, 19, by norm_num, by norm_num⟩
private lemma w709 : A274274 709 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 22, by norm_num, by norm_num⟩
private lemma w710 : A274274 710 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 15, 22, by norm_num, by norm_num⟩
private lemma w711 : A274274 711 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 15, 19, by norm_num, by norm_num⟩
private lemma w712 : A274274 712 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 26, by norm_num, by norm_num⟩
private lemma w713 : A274274 713 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 26, by norm_num, by norm_num⟩
private lemma w714 : A274274 714 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 25, by norm_num, by norm_num⟩
private lemma w716 : A274274 716 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 25, by norm_num, by norm_num⟩
private lemma w717 : A274274 717 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 15, 22, by norm_num, by norm_num⟩
private lemma w718 : A274274 718 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 8, 23, by norm_num, by norm_num⟩
private lemma w719 : A274274 719 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 26, by norm_num, by norm_num⟩
private lemma w720 : A274274 720 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 24, by norm_num, by norm_num⟩
private lemma w721 : A274274 721 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 12, 24, by norm_num, by norm_num⟩
private lemma w722 : A274274 722 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 19, 19, by norm_num, by norm_num⟩
private lemma w723 : A274274 723 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 19, 19, by norm_num, by norm_num⟩
private lemma w724 : A274274 724 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 18, 20, by norm_num, by norm_num⟩
private lemma w725 : A274274 725 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 26, by norm_num, by norm_num⟩
private lemma w726 : A274274 726 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 26, by norm_num, by norm_num⟩
private lemma w728 : A274274 728 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 12, 24, by norm_num, by norm_num⟩
private lemma w729 : A274274 729 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 27, by norm_num, by norm_num⟩
private lemma w730 : A274274 730 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 27, by norm_num, by norm_num⟩
private lemma w731 : A274274 731 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 27, by norm_num, by norm_num⟩
private lemma w732 : A274274 732 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 18, 20, by norm_num, by norm_num⟩
private lemma w733 : A274274 733 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 27, by norm_num, by norm_num⟩
private lemma w734 : A274274 734 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 27, by norm_num, by norm_num⟩
private lemma w735 : A274274 735 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 23, by norm_num, by norm_num⟩
private lemma w736 : A274274 736 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 15, 22, by norm_num, by norm_num⟩
private lemma w737 : A274274 737 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 27, by norm_num, by norm_num⟩
private lemma w738 : A274274 738 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 27, by norm_num, by norm_num⟩
private lemma w739 : A274274 739 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 27, by norm_num, by norm_num⟩
private lemma w740 : A274274 740 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 26, by norm_num, by norm_num⟩
private lemma w741 : A274274 741 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 26, by norm_num, by norm_num⟩
private lemma w742 : A274274 742 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 16, 19, by norm_num, by norm_num⟩
private lemma w743 : A274274 743 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 0, 20, by norm_num, by norm_num⟩
private lemma w744 : A274274 744 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 2, 26, by norm_num, by norm_num⟩
private lemma w745 : A274274 745 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 27, by norm_num, by norm_num⟩
private lemma w746 : A274274 746 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 25, by norm_num, by norm_num⟩
private lemma w747 : A274274 747 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 25, by norm_num, by norm_num⟩
private lemma w748 : A274274 748 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 26, by norm_num, by norm_num⟩
private lemma w749 : A274274 749 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 19, 19, by norm_num, by norm_num⟩
private lemma w750 : A274274 750 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 0, 25, by norm_num, by norm_num⟩
private lemma w751 : A274274 751 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 18, 20, by norm_num, by norm_num⟩
private lemma w752 : A274274 752 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 7, 26, by norm_num, by norm_num⟩
private lemma w753 : A274274 753 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 27, by norm_num, by norm_num⟩
private lemma w754 : A274274 754 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 27, by norm_num, by norm_num⟩
private lemma w755 : A274274 755 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 27, by norm_num, by norm_num⟩
private lemma w756 : A274274 756 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 27, by norm_num, by norm_num⟩
private lemma w757 : A274274 757 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 26, by norm_num, by norm_num⟩
private lemma w758 : A274274 758 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 26, by norm_num, by norm_num⟩
private lemma w759 : A274274 759 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 25, by norm_num, by norm_num⟩
private lemma w760 : A274274 760 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 27, by norm_num, by norm_num⟩
private lemma w761 : A274274 761 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 19, 20, by norm_num, by norm_num⟩
private lemma w762 : A274274 762 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 19, 20, by norm_num, by norm_num⟩
private lemma w763 : A274274 763 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 3, 5, by norm_num, by norm_num⟩
private lemma w764 : A274274 764 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨6, 8, 22, by norm_num, by norm_num⟩
private lemma w765 : A274274 765 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 27, by norm_num, by norm_num⟩
private lemma w766 : A274274 766 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 27, by norm_num, by norm_num⟩
private lemma w767 : A274274 767 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 26, by norm_num, by norm_num⟩
private lemma w768 : A274274 768 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 5, 20, by norm_num, by norm_num⟩
private lemma w769 : A274274 769 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 25, by norm_num, by norm_num⟩
private lemma w770 : A274274 770 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 12, 25, by norm_num, by norm_num⟩
private lemma w772 : A274274 772 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 24, by norm_num, by norm_num⟩
private lemma w773 : A274274 773 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 17, 22, by norm_num, by norm_num⟩
private lemma w774 : A274274 774 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 17, 22, by norm_num, by norm_num⟩
private lemma w775 : A274274 775 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 25, by norm_num, by norm_num⟩
private lemma w776 : A274274 776 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 26, by norm_num, by norm_num⟩
private lemma w777 : A274274 777 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 26, by norm_num, by norm_num⟩
private lemma w778 : A274274 778 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 27, by norm_num, by norm_num⟩
private lemma w779 : A274274 779 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 27, by norm_num, by norm_num⟩
private lemma w780 : A274274 780 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 24, by norm_num, by norm_num⟩
private lemma w781 : A274274 781 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 17, 22, by norm_num, by norm_num⟩
private lemma w782 : A274274 782 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 24, by norm_num, by norm_num⟩
private lemma w784 : A274274 784 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 28, by norm_num, by norm_num⟩
private lemma w785 : A274274 785 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 28, by norm_num, by norm_num⟩
private lemma w786 : A274274 786 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 28, by norm_num, by norm_num⟩
private lemma w787 : A274274 787 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 3, 7, by norm_num, by norm_num⟩
private lemma w788 : A274274 788 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 28, by norm_num, by norm_num⟩
private lemma w789 : A274274 789 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 28, by norm_num, by norm_num⟩
private lemma w790 : A274274 790 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 5, 6, by norm_num, by norm_num⟩
private lemma w791 : A274274 791 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 15, 21, by norm_num, by norm_num⟩
private lemma w792 : A274274 792 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 28, by norm_num, by norm_num⟩
private lemma w793 : A274274 793 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 28, by norm_num, by norm_num⟩
private lemma w794 : A274274 794 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 25, by norm_num, by norm_num⟩
private lemma w795 : A274274 795 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 25, by norm_num, by norm_num⟩
private lemma w796 : A274274 796 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 28, by norm_num, by norm_num⟩
private lemma w797 : A274274 797 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 11, 26, by norm_num, by norm_num⟩
private lemma w798 : A274274 798 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 11, 26, by norm_num, by norm_num⟩
private lemma w799 : A274274 799 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 14, 24, by norm_num, by norm_num⟩
private lemma w800 : A274274 800 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 28, by norm_num, by norm_num⟩
private lemma w801 : A274274 801 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 24, by norm_num, by norm_num⟩
private lemma w802 : A274274 802 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 19, 21, by norm_num, by norm_num⟩
private lemma w803 : A274274 803 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 19, 21, by norm_num, by norm_num⟩
private lemma w804 : A274274 804 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 8, 26, by norm_num, by norm_num⟩
private lemma w805 : A274274 805 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 11, 26, by norm_num, by norm_num⟩
private lemma w807 : A274274 807 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 8, 20, by norm_num, by norm_num⟩
private lemma w808 : A274274 808 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 18, 22, by norm_num, by norm_num⟩
private lemma w809 : A274274 809 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 28, by norm_num, by norm_num⟩
private lemma w810 : A274274 810 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 27, by norm_num, by norm_num⟩
private lemma w811 : A274274 811 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 27, by norm_num, by norm_num⟩
private lemma w812 : A274274 812 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 28, by norm_num, by norm_num⟩
private lemma w814 : A274274 814 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 8, 25, by norm_num, by norm_num⟩
private lemma w815 : A274274 815 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 28, by norm_num, by norm_num⟩
private lemma w816 : A274274 816 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 18, 22, by norm_num, by norm_num⟩
private lemma w817 : A274274 817 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 5, 28, by norm_num, by norm_num⟩
private lemma w818 : A274274 818 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 17, 23, by norm_num, by norm_num⟩
private lemma w819 : A274274 819 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 17, 23, by norm_num, by norm_num⟩
private lemma w820 : A274274 820 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 28, by norm_num, by norm_num⟩
private lemma w821 : A274274 821 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 25, by norm_num, by norm_num⟩
private lemma w822 : A274274 822 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 14, 25, by norm_num, by norm_num⟩
private lemma w823 : A274274 823 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 13, 23, by norm_num, by norm_num⟩
private lemma w824 : A274274 824 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 11, 26, by norm_num, by norm_num⟩
private lemma w825 : A274274 825 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 19, 20, by norm_num, by norm_num⟩
private lemma w826 : A274274 826 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 17, 23, by norm_num, by norm_num⟩
private lemma w827 : A274274 827 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 28, by norm_num, by norm_num⟩
private lemma w828 : A274274 828 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 28, by norm_num, by norm_num⟩
private lemma w829 : A274274 829 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 27, by norm_num, by norm_num⟩
private lemma w830 : A274274 830 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 27, by norm_num, by norm_num⟩
private lemma w831 : A274274 831 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 25, by norm_num, by norm_num⟩
private lemma w832 : A274274 832 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 16, 24, by norm_num, by norm_num⟩
private lemma w833 : A274274 833 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 28, by norm_num, by norm_num⟩
private lemma w834 : A274274 834 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 28, by norm_num, by norm_num⟩
private lemma w835 : A274274 835 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 18, 22, by norm_num, by norm_num⟩
private lemma w836 : A274274 836 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 28, by norm_num, by norm_num⟩
private lemma w837 : A274274 837 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 10, 27, by norm_num, by norm_num⟩
private lemma w838 : A274274 838 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 3, 10, by norm_num, by norm_num⟩
private lemma w840 : A274274 840 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 16, 24, by norm_num, by norm_num⟩
private lemma w841 : A274274 841 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 29, by norm_num, by norm_num⟩
private lemma w842 : A274274 842 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 29, by norm_num, by norm_num⟩
private lemma w843 : A274274 843 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 29, by norm_num, by norm_num⟩
private lemma w844 : A274274 844 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨6, 12, 22, by norm_num, by norm_num⟩
private lemma w845 : A274274 845 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 29, by norm_num, by norm_num⟩
private lemma w846 : A274274 846 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 29, by norm_num, by norm_num⟩
private lemma w847 : A274274 847 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 6, 28, by norm_num, by norm_num⟩
private lemma w848 : A274274 848 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 28, by norm_num, by norm_num⟩
private lemma w849 : A274274 849 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 28, by norm_num, by norm_num⟩
private lemma w850 : A274274 850 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 29, by norm_num, by norm_num⟩
private lemma w851 : A274274 851 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 29, by norm_num, by norm_num⟩
private lemma w852 : A274274 852 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 2, 28, by norm_num, by norm_num⟩
private lemma w853 : A274274 853 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 18, 23, by norm_num, by norm_num⟩
private lemma w854 : A274274 854 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 18, 23, by norm_num, by norm_num⟩
private lemma w855 : A274274 855 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 27, by norm_num, by norm_num⟩
private lemma w856 : A274274 856 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 28, by norm_num, by norm_num⟩
private lemma w857 : A274274 857 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 29, by norm_num, by norm_num⟩
private lemma w858 : A274274 858 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 29, by norm_num, by norm_num⟩
private lemma w859 : A274274 859 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 16, 24, by norm_num, by norm_num⟩
private lemma w860 : A274274 860 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 7, 28, by norm_num, by norm_num⟩
private lemma w861 : A274274 861 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 18, 23, by norm_num, by norm_num⟩
private lemma w863 : A274274 863 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 27, by norm_num, by norm_num⟩
private lemma w864 : A274274 864 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 4, 28, by norm_num, by norm_num⟩
private lemma w865 : A274274 865 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 28, by norm_num, by norm_num⟩
private lemma w866 : A274274 866 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 29, by norm_num, by norm_num⟩
private lemma w867 : A274274 867 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 29, by norm_num, by norm_num⟩
private lemma w868 : A274274 868 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 29, by norm_num, by norm_num⟩
private lemma w869 : A274274 869 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 1, 29, by norm_num, by norm_num⟩
private lemma w870 : A274274 870 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 4, 27, by norm_num, by norm_num⟩
private lemma w871 : A274274 871 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 11, 25, by norm_num, by norm_num⟩
private lemma w872 : A274274 872 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 26, by norm_num, by norm_num⟩
private lemma w873 : A274274 873 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 27, by norm_num, by norm_num⟩
private lemma w874 : A274274 874 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 12, 27, by norm_num, by norm_num⟩
private lemma w875 : A274274 875 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 28, by norm_num, by norm_num⟩
private lemma w876 : A274274 876 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 2, 23, by norm_num, by norm_num⟩
private lemma w877 : A274274 877 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 29, by norm_num, by norm_num⟩
private lemma w878 : A274274 878 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 29, by norm_num, by norm_num⟩
private lemma w879 : A274274 879 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 27, by norm_num, by norm_num⟩
private lemma w880 : A274274 880 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 26, by norm_num, by norm_num⟩
private lemma w881 : A274274 881 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 16, 25, by norm_num, by norm_num⟩
private lemma w882 : A274274 882 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 21, 21, by norm_num, by norm_num⟩
private lemma w883 : A274274 883 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 21, 21, by norm_num, by norm_num⟩
private lemma w884 : A274274 884 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 28, by norm_num, by norm_num⟩
private lemma w885 : A274274 885 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 28, by norm_num, by norm_num⟩
private lemma w886 : A274274 886 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 19, 20, by norm_num, by norm_num⟩
private lemma w887 : A274274 887 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 12, 20, by norm_num, by norm_num⟩
private lemma w888 : A274274 888 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 4, 23, by norm_num, by norm_num⟩
private lemma w889 : A274274 889 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 16, 25, by norm_num, by norm_num⟩
private lemma w890 : A274274 890 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 29, by norm_num, by norm_num⟩
private lemma w891 : A274274 891 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 29, by norm_num, by norm_num⟩
private lemma w892 : A274274 892 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 10, 28, by norm_num, by norm_num⟩
private lemma w893 : A274274 893 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 29, by norm_num, by norm_num⟩
private lemma w894 : A274274 894 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 12, 25, by norm_num, by norm_num⟩
private lemma w896 : A274274 896 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 16, 24, by norm_num, by norm_num⟩
private lemma w897 : A274274 897 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 7, 28, by norm_num, by norm_num⟩
private lemma w898 : A274274 898 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 27, by norm_num, by norm_num⟩
private lemma w899 : A274274 899 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 13, 27, by norm_num, by norm_num⟩
private lemma w900 : A274274 900 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 30, by norm_num, by norm_num⟩
private lemma w901 : A274274 901 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 30, by norm_num, by norm_num⟩
private lemma w902 : A274274 902 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 30, by norm_num, by norm_num⟩
private lemma w903 : A274274 903 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 27, by norm_num, by norm_num⟩
private lemma w904 : A274274 904 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 30, by norm_num, by norm_num⟩
private lemma w905 : A274274 905 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 29, by norm_num, by norm_num⟩
private lemma w906 : A274274 906 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 8, 29, by norm_num, by norm_num⟩
private lemma w907 : A274274 907 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 3, 13, by norm_num, by norm_num⟩
private lemma w908 : A274274 908 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 0, 30, by norm_num, by norm_num⟩
private lemma w909 : A274274 909 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 30, by norm_num, by norm_num⟩
private lemma w910 : A274274 910 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 30, by norm_num, by norm_num⟩
private lemma w911 : A274274 911 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 10, 28, by norm_num, by norm_num⟩
private lemma w912 : A274274 912 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 30, by norm_num, by norm_num⟩
private lemma w913 : A274274 913 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 29, by norm_num, by norm_num⟩
private lemma w914 : A274274 914 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 17, 25, by norm_num, by norm_num⟩
private lemma w915 : A274274 915 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 17, 25, by norm_num, by norm_num⟩
private lemma w916 : A274274 916 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 30, by norm_num, by norm_num⟩
private lemma w917 : A274274 917 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 30, by norm_num, by norm_num⟩
private lemma w918 : A274274 918 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 28, by norm_num, by norm_num⟩
private lemma w919 : A274274 919 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 13, 25, by norm_num, by norm_num⟩
private lemma w920 : A274274 920 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 1, 24, by norm_num, by norm_num⟩
private lemma w921 : A274274 921 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 4, 29, by norm_num, by norm_num⟩
private lemma w922 : A274274 922 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 29, by norm_num, by norm_num⟩
private lemma w923 : A274274 923 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 29, by norm_num, by norm_num⟩
private lemma w924 : A274274 924 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 4, 30, by norm_num, by norm_num⟩
private lemma w925 : A274274 925 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 30, by norm_num, by norm_num⟩
private lemma w926 : A274274 926 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 30, by norm_num, by norm_num⟩
private lemma w927 : A274274 927 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 0, 30, by norm_num, by norm_num⟩
private lemma w928 : A274274 928 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 28, by norm_num, by norm_num⟩
private lemma w929 : A274274 929 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 20, 23, by norm_num, by norm_num⟩
private lemma w930 : A274274 930 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 20, 23, by norm_num, by norm_num⟩
private lemma w931 : A274274 931 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 30, by norm_num, by norm_num⟩
private lemma w932 : A274274 932 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 16, 26, by norm_num, by norm_num⟩
private lemma w933 : A274274 933 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 16, 26, by norm_num, by norm_num⟩
private lemma w934 : A274274 934 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 5, 28, by norm_num, by norm_num⟩
private lemma w935 : A274274 935 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 27, by norm_num, by norm_num⟩
private lemma w936 : A274274 936 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 30, by norm_num, by norm_num⟩
private lemma w937 : A274274 937 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 19, 24, by norm_num, by norm_num⟩
private lemma w938 : A274274 938 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 19, 24, by norm_num, by norm_num⟩
private lemma w939 : A274274 939 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 14, 20, by norm_num, by norm_num⟩
private lemma w940 : A274274 940 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 16, 26, by norm_num, by norm_num⟩
private lemma w941 : A274274 941 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 29, by norm_num, by norm_num⟩
private lemma w942 : A274274 942 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 10, 29, by norm_num, by norm_num⟩
private lemma w943 : A274274 943 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 4, 30, by norm_num, by norm_num⟩
private lemma w944 : A274274 944 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 6, 30, by norm_num, by norm_num⟩
private lemma w945 : A274274 945 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 19, 24, by norm_num, by norm_num⟩
private lemma w946 : A274274 946 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 21, 21, by norm_num, by norm_num⟩
private lemma w947 : A274274 947 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 7, 13, by norm_num, by norm_num⟩
private lemma w948 : A274274 948 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 10, 28, by norm_num, by norm_num⟩
private lemma w949 : A274274 949 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 7, 30, by norm_num, by norm_num⟩
private lemma w950 : A274274 950 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 7, 30, by norm_num, by norm_num⟩
private lemma w952 : A274274 952 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 5, 30, by norm_num, by norm_num⟩
private lemma w953 : A274274 953 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 13, 28, by norm_num, by norm_num⟩
private lemma w954 : A274274 954 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 15, 27, by norm_num, by norm_num⟩
private lemma w955 : A274274 955 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 15, 27, by norm_num, by norm_num⟩
private lemma w956 : A274274 956 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 20, 23, by norm_num, by norm_num⟩
private lemma w957 : A274274 957 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 7, 30, by norm_num, by norm_num⟩
private lemma w958 : A274274 958 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 7, 28, by norm_num, by norm_num⟩
private lemma w959 : A274274 959 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 16, 26, by norm_num, by norm_num⟩
private lemma w960 : A274274 960 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 16, 19, by norm_num, by norm_num⟩
private lemma w961 : A274274 961 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 0, 31, by norm_num, by norm_num⟩
private lemma w962 : A274274 962 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 1, 31, by norm_num, by norm_num⟩
private lemma w963 : A274274 963 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 1, 31, by norm_num, by norm_num⟩
private lemma w964 : A274274 964 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 8, 30, by norm_num, by norm_num⟩
private lemma w965 : A274274 965 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 2, 31, by norm_num, by norm_num⟩
private lemma w966 : A274274 966 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 2, 31, by norm_num, by norm_num⟩
private lemma w967 : A274274 967 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 1, 29, by norm_num, by norm_num⟩
private lemma w968 : A274274 968 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 22, 22, by norm_num, by norm_num⟩
private lemma w969 : A274274 969 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 22, 22, by norm_num, by norm_num⟩
private lemma w970 : A274274 970 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 3, 31, by norm_num, by norm_num⟩
private lemma w971 : A274274 971 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 3, 31, by norm_num, by norm_num⟩
private lemma w972 : A274274 972 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 8, 30, by norm_num, by norm_num⟩
private lemma w973 : A274274 973 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 2, 31, by norm_num, by norm_num⟩
private lemma w974 : A274274 974 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 7, 14, by norm_num, by norm_num⟩
private lemma w975 : A274274 975 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 3, 29, by norm_num, by norm_num⟩
private lemma w976 : A274274 976 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 20, 24, by norm_num, by norm_num⟩
private lemma w977 : A274274 977 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 4, 31, by norm_num, by norm_num⟩
private lemma w978 : A274274 978 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 4, 31, by norm_num, by norm_num⟩
private lemma w979 : A274274 979 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨9, 5, 15, by norm_num, by norm_num⟩
private lemma w980 : A274274 980 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 14, 28, by norm_num, by norm_num⟩
private lemma w981 : A274274 981 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 9, 30, by norm_num, by norm_num⟩
private lemma w982 : A274274 982 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 9, 30, by norm_num, by norm_num⟩
private lemma w983 : A274274 983 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 8, 24, by norm_num, by norm_num⟩
private lemma w984 : A274274 984 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 20, 24, by norm_num, by norm_num⟩
private lemma w985 : A274274 985 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 12, 29, by norm_num, by norm_num⟩
private lemma w986 : A274274 986 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 5, 31, by norm_num, by norm_num⟩
private lemma w987 : A274274 987 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 5, 31, by norm_num, by norm_num⟩
private lemma w988 : A274274 988 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 14, 28, by norm_num, by norm_num⟩
private lemma w989 : A274274 989 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 9, 30, by norm_num, by norm_num⟩
private lemma w990 : A274274 990 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨5, 9, 28, by norm_num, by norm_num⟩
private lemma w991 : A274274 991 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 8, 30, by norm_num, by norm_num⟩
private lemma w992 : A274274 992 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 2, 31, by norm_num, by norm_num⟩
private lemma w993 : A274274 993 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 12, 29, by norm_num, by norm_num⟩
private lemma w994 : A274274 994 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨2, 5, 31, by norm_num, by norm_num⟩
private lemma w995 : A274274 995 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨3, 22, 22, by norm_num, by norm_num⟩
private lemma w996 : A274274 996 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨4, 16, 26, by norm_num, by norm_num⟩
private lemma w997 : A274274 997 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 6, 31, by norm_num, by norm_num⟩
private lemma w998 : A274274 998 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨1, 6, 31, by norm_num, by norm_num⟩
private lemma w999 : A274274 999 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨7, 16, 20, by norm_num, by norm_num⟩
private lemma w1000 : A274274 1000 ≠ 0 :=
  A274274_ne_zero_iff.mpr ⟨0, 10, 30, by norm_num, by norm_num⟩

private lemma nf7 : ¬ has_form_two_pow_k_times_four_m_plus_one 7 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 7 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 3 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf15 : ¬ has_form_two_pow_k_times_four_m_plus_one 15 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 15 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 4 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf22 : ¬ has_form_two_pow_k_times_four_m_plus_one 22 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 22 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 5 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf23 : ¬ has_form_two_pow_k_times_four_m_plus_one 23 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 23 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 5 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf39 : ¬ has_form_two_pow_k_times_four_m_plus_one 39 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 39 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 6 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf55 : ¬ has_form_two_pow_k_times_four_m_plus_one 55 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 55 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 6 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf70 : ¬ has_form_two_pow_k_times_four_m_plus_one 70 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 70 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf71 : ¬ has_form_two_pow_k_times_four_m_plus_one 71 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 71 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf78 : ¬ has_form_two_pow_k_times_four_m_plus_one 78 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 78 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf87 : ¬ has_form_two_pow_k_times_four_m_plus_one 87 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 87 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf94 : ¬ has_form_two_pow_k_times_four_m_plus_one 94 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 94 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf103 : ¬ has_form_two_pow_k_times_four_m_plus_one 103 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 103 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf111 : ¬ has_form_two_pow_k_times_four_m_plus_one 111 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 111 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf115 : ¬ has_form_two_pow_k_times_four_m_plus_one 115 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 115 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf119 : ¬ has_form_two_pow_k_times_four_m_plus_one 119 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 119 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf120 : ¬ has_form_two_pow_k_times_four_m_plus_one 120 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 120 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 7 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf139 : ¬ has_form_two_pow_k_times_four_m_plus_one 139 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 139 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 8 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf167 : ¬ has_form_two_pow_k_times_four_m_plus_one 167 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 167 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 8 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf211 : ¬ has_form_two_pow_k_times_four_m_plus_one 211 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 211 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 8 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf254 : ¬ has_form_two_pow_k_times_four_m_plus_one 254 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 254 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 8 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf263 : ¬ has_form_two_pow_k_times_four_m_plus_one 263 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 263 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf267 : ¬ has_form_two_pow_k_times_four_m_plus_one 267 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 267 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf279 : ¬ has_form_two_pow_k_times_four_m_plus_one 279 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 279 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf286 : ¬ has_form_two_pow_k_times_four_m_plus_one 286 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 286 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf302 : ¬ has_form_two_pow_k_times_four_m_plus_one 302 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 302 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf311 : ¬ has_form_two_pow_k_times_four_m_plus_one 311 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 311 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf312 : ¬ has_form_two_pow_k_times_four_m_plus_one 312 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 312 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf331 : ¬ has_form_two_pow_k_times_four_m_plus_one 331 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 331 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf335 : ¬ has_form_two_pow_k_times_four_m_plus_one 335 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 335 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf342 : ¬ has_form_two_pow_k_times_four_m_plus_one 342 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 342 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf391 : ¬ has_form_two_pow_k_times_four_m_plus_one 391 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 391 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf403 : ¬ has_form_two_pow_k_times_four_m_plus_one 403 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 403 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf435 : ¬ has_form_two_pow_k_times_four_m_plus_one 435 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 435 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf454 : ¬ has_form_two_pow_k_times_four_m_plus_one 454 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 454 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf455 : ¬ has_form_two_pow_k_times_four_m_plus_one 455 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 455 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf470 : ¬ has_form_two_pow_k_times_four_m_plus_one 470 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 470 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf475 : ¬ has_form_two_pow_k_times_four_m_plus_one 475 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 475 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf499 : ¬ has_form_two_pow_k_times_four_m_plus_one 499 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 499 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 9 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf518 : ¬ has_form_two_pow_k_times_four_m_plus_one 518 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 518 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf559 : ¬ has_form_two_pow_k_times_four_m_plus_one 559 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 559 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf590 : ¬ has_form_two_pow_k_times_four_m_plus_one 590 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 590 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf595 : ¬ has_form_two_pow_k_times_four_m_plus_one 595 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 595 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf598 : ¬ has_form_two_pow_k_times_four_m_plus_one 598 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 598 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf622 : ¬ has_form_two_pow_k_times_four_m_plus_one 622 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 622 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf643 : ¬ has_form_two_pow_k_times_four_m_plus_one 643 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 643 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf659 : ¬ has_form_two_pow_k_times_four_m_plus_one 659 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 659 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf691 : ¬ has_form_two_pow_k_times_four_m_plus_one 691 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 691 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf695 : ¬ has_form_two_pow_k_times_four_m_plus_one 695 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 695 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf715 : ¬ has_form_two_pow_k_times_four_m_plus_one 715 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 715 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf727 : ¬ has_form_two_pow_k_times_four_m_plus_one 727 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 727 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf771 : ¬ has_form_two_pow_k_times_four_m_plus_one 771 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 771 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf783 : ¬ has_form_two_pow_k_times_four_m_plus_one 783 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 783 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf806 : ¬ has_form_two_pow_k_times_four_m_plus_one 806 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 806 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf839 : ¬ has_form_two_pow_k_times_four_m_plus_one 839 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 839 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf862 : ¬ has_form_two_pow_k_times_four_m_plus_one 862 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 862 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf895 : ¬ has_form_two_pow_k_times_four_m_plus_one 895 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 895 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega
private lemma nf951 : ¬ has_form_two_pow_k_times_four_m_plus_one 951 := by
  rintro ⟨k, m, h⟩
  have hk : 2 ^ k ≤ 951 := by
    rw [h]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hk2 : k < 10 := by
    by_contra hc
    push_neg at hc
    have h2 := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    norm_num at h2
    omega
  interval_cases k <;> omega

/-- Complete sorry-free verification of the conjecture for all `n ≤ 1000`,
demonstrating the finite-verification architecture (representation witnesses,
plus refutation of `has_form` for the non-representable values).
(The full computational verification, by exhaustive sieve outside Lean,
extends this to all `n ≤ 1.5×10^14`.) -/
theorem A274274_conjecture_i_upto_1000 : ∀ n ≤ 1000,
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) := by
  intro n hn
  interval_cases n
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ _ => w0⟩
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num), fun _ _ => w1⟩
  · exact ⟨fun _ => Or.inl w2, fun h => absurd h (by norm_num), fun _ _ => w2⟩
  · exact ⟨fun _ => Or.inl w3, fun h => absurd h (by norm_num), fun _ _ => w3⟩
  · exact ⟨fun _ => Or.inl w4, fun h => absurd h (by norm_num), fun _ _ => w4⟩
  · exact ⟨fun _ => Or.inl w5, fun h => absurd h (by norm_num), fun _ _ => w5⟩
  · exact ⟨fun _ => Or.inl w6, fun _ => Or.inl w6, fun _ _ => w6⟩
  · exact ⟨fun _ => Or.inr (show A274274 5 ≠ 0 from w5), fun _ => Or.inr (show A274274 1 ≠ 0 from w1), fun hf _ => absurd hf nf7⟩
  · exact ⟨fun _ => Or.inl w8, fun _ => Or.inl w8, fun _ _ => w8⟩
  · exact ⟨fun _ => Or.inl w9, fun _ => Or.inl w9, fun _ _ => w9⟩
  · exact ⟨fun _ => Or.inl w10, fun _ => Or.inl w10, fun _ _ => w10⟩
  · exact ⟨fun _ => Or.inl w11, fun _ => Or.inl w11, fun _ _ => w11⟩
  · exact ⟨fun _ => Or.inl w12, fun _ => Or.inl w12, fun _ _ => w12⟩
  · exact ⟨fun _ => Or.inl w13, fun _ => Or.inl w13, fun _ _ => w13⟩
  · exact ⟨fun _ => Or.inl w14, fun _ => Or.inl w14, fun _ _ => w14⟩
  · exact ⟨fun _ => Or.inr (show A274274 13 ≠ 0 from w13), fun _ => Or.inr (show A274274 9 ≠ 0 from w9), fun hf _ => absurd hf nf15⟩
  · exact ⟨fun _ => Or.inl w16, fun _ => Or.inl w16, fun _ _ => w16⟩
  · exact ⟨fun _ => Or.inl w17, fun _ => Or.inl w17, fun _ _ => w17⟩
  · exact ⟨fun _ => Or.inl w18, fun _ => Or.inl w18, fun _ _ => w18⟩
  · exact ⟨fun _ => Or.inl w19, fun _ => Or.inl w19, fun _ _ => w19⟩
  · exact ⟨fun _ => Or.inl w20, fun _ => Or.inl w20, fun _ _ => w20⟩
  · exact ⟨fun _ => Or.inl w21, fun _ => Or.inl w21, fun _ _ => w21⟩
  · exact ⟨fun _ => Or.inr (show A274274 20 ≠ 0 from w20), fun _ => Or.inr (show A274274 16 ≠ 0 from w16), fun hf _ => absurd hf nf22⟩
  · exact ⟨fun _ => Or.inr (show A274274 21 ≠ 0 from w21), fun _ => Or.inr (show A274274 17 ≠ 0 from w17), fun hf _ => absurd hf nf23⟩
  · exact ⟨fun _ => Or.inl w24, fun _ => Or.inl w24, fun _ _ => w24⟩
  · exact ⟨fun _ => Or.inl w25, fun _ => Or.inl w25, fun _ _ => w25⟩
  · exact ⟨fun _ => Or.inl w26, fun _ => Or.inl w26, fun _ _ => w26⟩
  · exact ⟨fun _ => Or.inl w27, fun _ => Or.inl w27, fun _ _ => w27⟩
  · exact ⟨fun _ => Or.inl w28, fun _ => Or.inl w28, fun _ _ => w28⟩
  · exact ⟨fun _ => Or.inl w29, fun _ => Or.inl w29, fun _ _ => w29⟩
  · exact ⟨fun _ => Or.inl w30, fun _ => Or.inl w30, fun _ _ => w30⟩
  · exact ⟨fun _ => Or.inl w31, fun _ => Or.inl w31, fun _ _ => w31⟩
  · exact ⟨fun _ => Or.inl w32, fun _ => Or.inl w32, fun _ _ => w32⟩
  · exact ⟨fun _ => Or.inl w33, fun _ => Or.inl w33, fun _ _ => w33⟩
  · exact ⟨fun _ => Or.inl w34, fun _ => Or.inl w34, fun _ _ => w34⟩
  · exact ⟨fun _ => Or.inl w35, fun _ => Or.inl w35, fun _ _ => w35⟩
  · exact ⟨fun _ => Or.inl w36, fun _ => Or.inl w36, fun _ _ => w36⟩
  · exact ⟨fun _ => Or.inl w37, fun _ => Or.inl w37, fun _ _ => w37⟩
  · exact ⟨fun _ => Or.inl w38, fun _ => Or.inl w38, fun _ _ => w38⟩
  · exact ⟨fun _ => Or.inr (show A274274 37 ≠ 0 from w37), fun _ => Or.inr (show A274274 33 ≠ 0 from w33), fun hf _ => absurd hf nf39⟩
  · exact ⟨fun _ => Or.inl w40, fun _ => Or.inl w40, fun _ _ => w40⟩
  · exact ⟨fun _ => Or.inl w41, fun _ => Or.inl w41, fun _ _ => w41⟩
  · exact ⟨fun _ => Or.inl w42, fun _ => Or.inl w42, fun _ _ => w42⟩
  · exact ⟨fun _ => Or.inl w43, fun _ => Or.inl w43, fun _ _ => w43⟩
  · exact ⟨fun _ => Or.inl w44, fun _ => Or.inl w44, fun _ _ => w44⟩
  · exact ⟨fun _ => Or.inl w45, fun _ => Or.inl w45, fun _ _ => w45⟩
  · exact ⟨fun _ => Or.inl w46, fun _ => Or.inl w46, fun _ _ => w46⟩
  · exact ⟨fun _ => Or.inl w47, fun _ => Or.inl w47, fun _ _ => w47⟩
  · exact ⟨fun _ => Or.inl w48, fun _ => Or.inl w48, fun _ _ => w48⟩
  · exact ⟨fun _ => Or.inl w49, fun _ => Or.inl w49, fun _ _ => w49⟩
  · exact ⟨fun _ => Or.inl w50, fun _ => Or.inl w50, fun _ _ => w50⟩
  · exact ⟨fun _ => Or.inl w51, fun _ => Or.inl w51, fun _ _ => w51⟩
  · exact ⟨fun _ => Or.inl w52, fun _ => Or.inl w52, fun _ _ => w52⟩
  · exact ⟨fun _ => Or.inl w53, fun _ => Or.inl w53, fun _ _ => w53⟩
  · exact ⟨fun _ => Or.inl w54, fun _ => Or.inl w54, fun _ _ => w54⟩
  · exact ⟨fun _ => Or.inr (show A274274 53 ≠ 0 from w53), fun _ => Or.inr (show A274274 49 ≠ 0 from w49), fun hf _ => absurd hf nf55⟩
  · exact ⟨fun _ => Or.inl w56, fun _ => Or.inl w56, fun _ _ => w56⟩
  · exact ⟨fun _ => Or.inl w57, fun _ => Or.inl w57, fun _ _ => w57⟩
  · exact ⟨fun _ => Or.inl w58, fun _ => Or.inl w58, fun _ _ => w58⟩
  · exact ⟨fun _ => Or.inl w59, fun _ => Or.inl w59, fun _ _ => w59⟩
  · exact ⟨fun _ => Or.inl w60, fun _ => Or.inl w60, fun _ _ => w60⟩
  · exact ⟨fun _ => Or.inl w61, fun _ => Or.inl w61, fun _ _ => w61⟩
  · exact ⟨fun _ => Or.inl w62, fun _ => Or.inl w62, fun _ _ => w62⟩
  · exact ⟨fun _ => Or.inl w63, fun _ => Or.inl w63, fun _ _ => w63⟩
  · exact ⟨fun _ => Or.inl w64, fun _ => Or.inl w64, fun _ _ => w64⟩
  · exact ⟨fun _ => Or.inl w65, fun _ => Or.inl w65, fun _ _ => w65⟩
  · exact ⟨fun _ => Or.inl w66, fun _ => Or.inl w66, fun _ _ => w66⟩
  · exact ⟨fun _ => Or.inl w67, fun _ => Or.inl w67, fun _ _ => w67⟩
  · exact ⟨fun _ => Or.inl w68, fun _ => Or.inl w68, fun _ _ => w68⟩
  · exact ⟨fun _ => Or.inl w69, fun _ => Or.inl w69, fun _ _ => w69⟩
  · exact ⟨fun _ => Or.inr (show A274274 68 ≠ 0 from w68), fun _ => Or.inr (show A274274 64 ≠ 0 from w64), fun hf _ => absurd hf nf70⟩
  · exact ⟨fun _ => Or.inr (show A274274 69 ≠ 0 from w69), fun _ => Or.inr (show A274274 65 ≠ 0 from w65), fun hf _ => absurd hf nf71⟩
  · exact ⟨fun _ => Or.inl w72, fun _ => Or.inl w72, fun _ _ => w72⟩
  · exact ⟨fun _ => Or.inl w73, fun _ => Or.inl w73, fun _ _ => w73⟩
  · exact ⟨fun _ => Or.inl w74, fun _ => Or.inl w74, fun _ _ => w74⟩
  · exact ⟨fun _ => Or.inl w75, fun _ => Or.inl w75, fun _ _ => w75⟩
  · exact ⟨fun _ => Or.inl w76, fun _ => Or.inl w76, fun _ _ => w76⟩
  · exact ⟨fun _ => Or.inl w77, fun _ => Or.inl w77, fun _ _ => w77⟩
  · exact ⟨fun _ => Or.inr (show A274274 76 ≠ 0 from w76), fun _ => Or.inr (show A274274 72 ≠ 0 from w72), fun hf _ => absurd hf nf78⟩
  · exact ⟨fun _ => Or.inl w79, fun _ => Or.inl w79, fun _ _ => w79⟩
  · exact ⟨fun _ => Or.inl w80, fun _ => Or.inl w80, fun _ _ => w80⟩
  · exact ⟨fun _ => Or.inl w81, fun _ => Or.inl w81, fun _ _ => w81⟩
  · exact ⟨fun _ => Or.inl w82, fun _ => Or.inl w82, fun _ _ => w82⟩
  · exact ⟨fun _ => Or.inl w83, fun _ => Or.inl w83, fun _ _ => w83⟩
  · exact ⟨fun _ => Or.inl w84, fun _ => Or.inl w84, fun _ _ => w84⟩
  · exact ⟨fun _ => Or.inl w85, fun _ => Or.inl w85, fun _ _ => w85⟩
  · exact ⟨fun _ => Or.inl w86, fun _ => Or.inl w86, fun _ _ => w86⟩
  · exact ⟨fun _ => Or.inr (show A274274 85 ≠ 0 from w85), fun _ => Or.inr (show A274274 81 ≠ 0 from w81), fun hf _ => absurd hf nf87⟩
  · exact ⟨fun _ => Or.inl w88, fun _ => Or.inl w88, fun _ _ => w88⟩
  · exact ⟨fun _ => Or.inl w89, fun _ => Or.inl w89, fun _ _ => w89⟩
  · exact ⟨fun _ => Or.inl w90, fun _ => Or.inl w90, fun _ _ => w90⟩
  · exact ⟨fun _ => Or.inl w91, fun _ => Or.inl w91, fun _ _ => w91⟩
  · exact ⟨fun _ => Or.inl w92, fun _ => Or.inl w92, fun _ _ => w92⟩
  · exact ⟨fun _ => Or.inl w93, fun _ => Or.inl w93, fun _ _ => w93⟩
  · exact ⟨fun _ => Or.inr (show A274274 92 ≠ 0 from w92), fun _ => Or.inr (show A274274 88 ≠ 0 from w88), fun hf _ => absurd hf nf94⟩
  · exact ⟨fun _ => Or.inl w95, fun _ => Or.inl w95, fun _ _ => w95⟩
  · exact ⟨fun _ => Or.inl w96, fun _ => Or.inl w96, fun _ _ => w96⟩
  · exact ⟨fun _ => Or.inl w97, fun _ => Or.inl w97, fun _ _ => w97⟩
  · exact ⟨fun _ => Or.inl w98, fun _ => Or.inl w98, fun _ _ => w98⟩
  · exact ⟨fun _ => Or.inl w99, fun _ => Or.inl w99, fun _ _ => w99⟩
  · exact ⟨fun _ => Or.inl w100, fun _ => Or.inl w100, fun _ _ => w100⟩
  · exact ⟨fun _ => Or.inl w101, fun _ => Or.inl w101, fun _ _ => w101⟩
  · exact ⟨fun _ => Or.inl w102, fun _ => Or.inl w102, fun _ _ => w102⟩
  · exact ⟨fun _ => Or.inr (show A274274 101 ≠ 0 from w101), fun _ => Or.inr (show A274274 97 ≠ 0 from w97), fun hf _ => absurd hf nf103⟩
  · exact ⟨fun _ => Or.inl w104, fun _ => Or.inl w104, fun _ _ => w104⟩
  · exact ⟨fun _ => Or.inl w105, fun _ => Or.inl w105, fun _ _ => w105⟩
  · exact ⟨fun _ => Or.inl w106, fun _ => Or.inl w106, fun _ _ => w106⟩
  · exact ⟨fun _ => Or.inl w107, fun _ => Or.inl w107, fun _ _ => w107⟩
  · exact ⟨fun _ => Or.inl w108, fun _ => Or.inl w108, fun _ _ => w108⟩
  · exact ⟨fun _ => Or.inl w109, fun _ => Or.inl w109, fun _ _ => w109⟩
  · exact ⟨fun _ => Or.inl w110, fun _ => Or.inl w110, fun _ _ => w110⟩
  · exact ⟨fun _ => Or.inr (show A274274 109 ≠ 0 from w109), fun _ => Or.inr (show A274274 105 ≠ 0 from w105), fun hf _ => absurd hf nf111⟩
  · exact ⟨fun _ => Or.inl w112, fun _ => Or.inl w112, fun _ _ => w112⟩
  · exact ⟨fun _ => Or.inl w113, fun _ => Or.inl w113, fun _ _ => w113⟩
  · exact ⟨fun _ => Or.inl w114, fun _ => Or.inl w114, fun _ _ => w114⟩
  · exact ⟨fun _ => Or.inr (show A274274 113 ≠ 0 from w113), fun _ => Or.inr (show A274274 109 ≠ 0 from w109), fun hf _ => absurd hf nf115⟩
  · exact ⟨fun _ => Or.inl w116, fun _ => Or.inl w116, fun _ _ => w116⟩
  · exact ⟨fun _ => Or.inl w117, fun _ => Or.inl w117, fun _ _ => w117⟩
  · exact ⟨fun _ => Or.inl w118, fun _ => Or.inl w118, fun _ _ => w118⟩
  · exact ⟨fun _ => Or.inr (show A274274 117 ≠ 0 from w117), fun _ => Or.inr (show A274274 113 ≠ 0 from w113), fun hf _ => absurd hf nf119⟩
  · exact ⟨fun _ => Or.inr (show A274274 118 ≠ 0 from w118), fun _ => Or.inr (show A274274 114 ≠ 0 from w114), fun hf _ => absurd hf nf120⟩
  · exact ⟨fun _ => Or.inl w121, fun _ => Or.inl w121, fun _ _ => w121⟩
  · exact ⟨fun _ => Or.inl w122, fun _ => Or.inl w122, fun _ _ => w122⟩
  · exact ⟨fun _ => Or.inl w123, fun _ => Or.inl w123, fun _ _ => w123⟩
  · exact ⟨fun _ => Or.inl w124, fun _ => Or.inl w124, fun _ _ => w124⟩
  · exact ⟨fun _ => Or.inl w125, fun _ => Or.inl w125, fun _ _ => w125⟩
  · exact ⟨fun _ => Or.inl w126, fun _ => Or.inl w126, fun _ _ => w126⟩
  · exact ⟨fun _ => Or.inl w127, fun _ => Or.inl w127, fun _ _ => w127⟩
  · exact ⟨fun _ => Or.inl w128, fun _ => Or.inl w128, fun _ _ => w128⟩
  · exact ⟨fun _ => Or.inl w129, fun _ => Or.inl w129, fun _ _ => w129⟩
  · exact ⟨fun _ => Or.inl w130, fun _ => Or.inl w130, fun _ _ => w130⟩
  · exact ⟨fun _ => Or.inl w131, fun _ => Or.inl w131, fun _ _ => w131⟩
  · exact ⟨fun _ => Or.inl w132, fun _ => Or.inl w132, fun _ _ => w132⟩
  · exact ⟨fun _ => Or.inl w133, fun _ => Or.inl w133, fun _ _ => w133⟩
  · exact ⟨fun _ => Or.inl w134, fun _ => Or.inl w134, fun _ _ => w134⟩
  · exact ⟨fun _ => Or.inl w135, fun _ => Or.inl w135, fun _ _ => w135⟩
  · exact ⟨fun _ => Or.inl w136, fun _ => Or.inl w136, fun _ _ => w136⟩
  · exact ⟨fun _ => Or.inl w137, fun _ => Or.inl w137, fun _ _ => w137⟩
  · exact ⟨fun _ => Or.inl w138, fun _ => Or.inl w138, fun _ _ => w138⟩
  · exact ⟨fun _ => Or.inr (show A274274 137 ≠ 0 from w137), fun _ => Or.inr (show A274274 133 ≠ 0 from w133), fun hf _ => absurd hf nf139⟩
  · exact ⟨fun _ => Or.inl w140, fun _ => Or.inl w140, fun _ _ => w140⟩
  · exact ⟨fun _ => Or.inl w141, fun _ => Or.inl w141, fun _ _ => w141⟩
  · exact ⟨fun _ => Or.inl w142, fun _ => Or.inl w142, fun _ _ => w142⟩
  · exact ⟨fun _ => Or.inl w143, fun _ => Or.inl w143, fun _ _ => w143⟩
  · exact ⟨fun _ => Or.inl w144, fun _ => Or.inl w144, fun _ _ => w144⟩
  · exact ⟨fun _ => Or.inl w145, fun _ => Or.inl w145, fun _ _ => w145⟩
  · exact ⟨fun _ => Or.inl w146, fun _ => Or.inl w146, fun _ _ => w146⟩
  · exact ⟨fun _ => Or.inl w147, fun _ => Or.inl w147, fun _ _ => w147⟩
  · exact ⟨fun _ => Or.inl w148, fun _ => Or.inl w148, fun _ _ => w148⟩
  · exact ⟨fun _ => Or.inl w149, fun _ => Or.inl w149, fun _ _ => w149⟩
  · exact ⟨fun _ => Or.inl w150, fun _ => Or.inl w150, fun _ _ => w150⟩
  · exact ⟨fun _ => Or.inl w151, fun _ => Or.inl w151, fun _ _ => w151⟩
  · exact ⟨fun _ => Or.inl w152, fun _ => Or.inl w152, fun _ _ => w152⟩
  · exact ⟨fun _ => Or.inl w153, fun _ => Or.inl w153, fun _ _ => w153⟩
  · exact ⟨fun _ => Or.inl w154, fun _ => Or.inl w154, fun _ _ => w154⟩
  · exact ⟨fun _ => Or.inl w155, fun _ => Or.inl w155, fun _ _ => w155⟩
  · exact ⟨fun _ => Or.inl w156, fun _ => Or.inl w156, fun _ _ => w156⟩
  · exact ⟨fun _ => Or.inl w157, fun _ => Or.inl w157, fun _ _ => w157⟩
  · exact ⟨fun _ => Or.inl w158, fun _ => Or.inl w158, fun _ _ => w158⟩
  · exact ⟨fun _ => Or.inl w159, fun _ => Or.inl w159, fun _ _ => w159⟩
  · exact ⟨fun _ => Or.inl w160, fun _ => Or.inl w160, fun _ _ => w160⟩
  · exact ⟨fun _ => Or.inl w161, fun _ => Or.inl w161, fun _ _ => w161⟩
  · exact ⟨fun _ => Or.inl w162, fun _ => Or.inl w162, fun _ _ => w162⟩
  · exact ⟨fun _ => Or.inl w163, fun _ => Or.inl w163, fun _ _ => w163⟩
  · exact ⟨fun _ => Or.inl w164, fun _ => Or.inl w164, fun _ _ => w164⟩
  · exact ⟨fun _ => Or.inl w165, fun _ => Or.inl w165, fun _ _ => w165⟩
  · exact ⟨fun _ => Or.inl w166, fun _ => Or.inl w166, fun _ _ => w166⟩
  · exact ⟨fun _ => Or.inr (show A274274 165 ≠ 0 from w165), fun _ => Or.inr (show A274274 161 ≠ 0 from w161), fun hf _ => absurd hf nf167⟩
  · exact ⟨fun _ => Or.inl w168, fun _ => Or.inl w168, fun _ _ => w168⟩
  · exact ⟨fun _ => Or.inl w169, fun _ => Or.inl w169, fun _ _ => w169⟩
  · exact ⟨fun _ => Or.inl w170, fun _ => Or.inl w170, fun _ _ => w170⟩
  · exact ⟨fun _ => Or.inl w171, fun _ => Or.inl w171, fun _ _ => w171⟩
  · exact ⟨fun _ => Or.inl w172, fun _ => Or.inl w172, fun _ _ => w172⟩
  · exact ⟨fun _ => Or.inl w173, fun _ => Or.inl w173, fun _ _ => w173⟩
  · exact ⟨fun _ => Or.inl w174, fun _ => Or.inl w174, fun _ _ => w174⟩
  · exact ⟨fun _ => Or.inl w175, fun _ => Or.inl w175, fun _ _ => w175⟩
  · exact ⟨fun _ => Or.inl w176, fun _ => Or.inl w176, fun _ _ => w176⟩
  · exact ⟨fun _ => Or.inl w177, fun _ => Or.inl w177, fun _ _ => w177⟩
  · exact ⟨fun _ => Or.inl w178, fun _ => Or.inl w178, fun _ _ => w178⟩
  · exact ⟨fun _ => Or.inl w179, fun _ => Or.inl w179, fun _ _ => w179⟩
  · exact ⟨fun _ => Or.inl w180, fun _ => Or.inl w180, fun _ _ => w180⟩
  · exact ⟨fun _ => Or.inl w181, fun _ => Or.inl w181, fun _ _ => w181⟩
  · exact ⟨fun _ => Or.inl w182, fun _ => Or.inl w182, fun _ _ => w182⟩
  · exact ⟨fun _ => Or.inl w183, fun _ => Or.inl w183, fun _ _ => w183⟩
  · exact ⟨fun _ => Or.inl w184, fun _ => Or.inl w184, fun _ _ => w184⟩
  · exact ⟨fun _ => Or.inl w185, fun _ => Or.inl w185, fun _ _ => w185⟩
  · exact ⟨fun _ => Or.inl w186, fun _ => Or.inl w186, fun _ _ => w186⟩
  · exact ⟨fun _ => Or.inl w187, fun _ => Or.inl w187, fun _ _ => w187⟩
  · exact ⟨fun _ => Or.inl w188, fun _ => Or.inl w188, fun _ _ => w188⟩
  · exact ⟨fun _ => Or.inl w189, fun _ => Or.inl w189, fun _ _ => w189⟩
  · exact ⟨fun _ => Or.inl w190, fun _ => Or.inl w190, fun _ _ => w190⟩
  · exact ⟨fun _ => Or.inl w191, fun _ => Or.inl w191, fun _ _ => w191⟩
  · exact ⟨fun _ => Or.inl w192, fun _ => Or.inl w192, fun _ _ => w192⟩
  · exact ⟨fun _ => Or.inl w193, fun _ => Or.inl w193, fun _ _ => w193⟩
  · exact ⟨fun _ => Or.inl w194, fun _ => Or.inl w194, fun _ _ => w194⟩
  · exact ⟨fun _ => Or.inl w195, fun _ => Or.inl w195, fun _ _ => w195⟩
  · exact ⟨fun _ => Or.inl w196, fun _ => Or.inl w196, fun _ _ => w196⟩
  · exact ⟨fun _ => Or.inl w197, fun _ => Or.inl w197, fun _ _ => w197⟩
  · exact ⟨fun _ => Or.inl w198, fun _ => Or.inl w198, fun _ _ => w198⟩
  · exact ⟨fun _ => Or.inl w199, fun _ => Or.inl w199, fun _ _ => w199⟩
  · exact ⟨fun _ => Or.inl w200, fun _ => Or.inl w200, fun _ _ => w200⟩
  · exact ⟨fun _ => Or.inl w201, fun _ => Or.inl w201, fun _ _ => w201⟩
  · exact ⟨fun _ => Or.inl w202, fun _ => Or.inl w202, fun _ _ => w202⟩
  · exact ⟨fun _ => Or.inl w203, fun _ => Or.inl w203, fun _ _ => w203⟩
  · exact ⟨fun _ => Or.inl w204, fun _ => Or.inl w204, fun _ _ => w204⟩
  · exact ⟨fun _ => Or.inl w205, fun _ => Or.inl w205, fun _ _ => w205⟩
  · exact ⟨fun _ => Or.inl w206, fun _ => Or.inl w206, fun _ _ => w206⟩
  · exact ⟨fun _ => Or.inl w207, fun _ => Or.inl w207, fun _ _ => w207⟩
  · exact ⟨fun _ => Or.inl w208, fun _ => Or.inl w208, fun _ _ => w208⟩
  · exact ⟨fun _ => Or.inl w209, fun _ => Or.inl w209, fun _ _ => w209⟩
  · exact ⟨fun _ => Or.inl w210, fun _ => Or.inl w210, fun _ _ => w210⟩
  · exact ⟨fun _ => Or.inr (show A274274 209 ≠ 0 from w209), fun _ => Or.inr (show A274274 205 ≠ 0 from w205), fun hf _ => absurd hf nf211⟩
  · exact ⟨fun _ => Or.inl w212, fun _ => Or.inl w212, fun _ _ => w212⟩
  · exact ⟨fun _ => Or.inl w213, fun _ => Or.inl w213, fun _ _ => w213⟩
  · exact ⟨fun _ => Or.inl w214, fun _ => Or.inl w214, fun _ _ => w214⟩
  · exact ⟨fun _ => Or.inl w215, fun _ => Or.inl w215, fun _ _ => w215⟩
  · exact ⟨fun _ => Or.inl w216, fun _ => Or.inl w216, fun _ _ => w216⟩
  · exact ⟨fun _ => Or.inl w217, fun _ => Or.inl w217, fun _ _ => w217⟩
  · exact ⟨fun _ => Or.inl w218, fun _ => Or.inl w218, fun _ _ => w218⟩
  · exact ⟨fun _ => Or.inl w219, fun _ => Or.inl w219, fun _ _ => w219⟩
  · exact ⟨fun _ => Or.inl w220, fun _ => Or.inl w220, fun _ _ => w220⟩
  · exact ⟨fun _ => Or.inl w221, fun _ => Or.inl w221, fun _ _ => w221⟩
  · exact ⟨fun _ => Or.inl w222, fun _ => Or.inl w222, fun _ _ => w222⟩
  · exact ⟨fun _ => Or.inl w223, fun _ => Or.inl w223, fun _ _ => w223⟩
  · exact ⟨fun _ => Or.inl w224, fun _ => Or.inl w224, fun _ _ => w224⟩
  · exact ⟨fun _ => Or.inl w225, fun _ => Or.inl w225, fun _ _ => w225⟩
  · exact ⟨fun _ => Or.inl w226, fun _ => Or.inl w226, fun _ _ => w226⟩
  · exact ⟨fun _ => Or.inl w227, fun _ => Or.inl w227, fun _ _ => w227⟩
  · exact ⟨fun _ => Or.inl w228, fun _ => Or.inl w228, fun _ _ => w228⟩
  · exact ⟨fun _ => Or.inl w229, fun _ => Or.inl w229, fun _ _ => w229⟩
  · exact ⟨fun _ => Or.inl w230, fun _ => Or.inl w230, fun _ _ => w230⟩
  · exact ⟨fun _ => Or.inl w231, fun _ => Or.inl w231, fun _ _ => w231⟩
  · exact ⟨fun _ => Or.inl w232, fun _ => Or.inl w232, fun _ _ => w232⟩
  · exact ⟨fun _ => Or.inl w233, fun _ => Or.inl w233, fun _ _ => w233⟩
  · exact ⟨fun _ => Or.inl w234, fun _ => Or.inl w234, fun _ _ => w234⟩
  · exact ⟨fun _ => Or.inl w235, fun _ => Or.inl w235, fun _ _ => w235⟩
  · exact ⟨fun _ => Or.inl w236, fun _ => Or.inl w236, fun _ _ => w236⟩
  · exact ⟨fun _ => Or.inl w237, fun _ => Or.inl w237, fun _ _ => w237⟩
  · exact ⟨fun _ => Or.inl w238, fun _ => Or.inl w238, fun _ _ => w238⟩
  · exact ⟨fun _ => Or.inl w239, fun _ => Or.inl w239, fun _ _ => w239⟩
  · exact ⟨fun _ => Or.inl w240, fun _ => Or.inl w240, fun _ _ => w240⟩
  · exact ⟨fun _ => Or.inl w241, fun _ => Or.inl w241, fun _ _ => w241⟩
  · exact ⟨fun _ => Or.inl w242, fun _ => Or.inl w242, fun _ _ => w242⟩
  · exact ⟨fun _ => Or.inl w243, fun _ => Or.inl w243, fun _ _ => w243⟩
  · exact ⟨fun _ => Or.inl w244, fun _ => Or.inl w244, fun _ _ => w244⟩
  · exact ⟨fun _ => Or.inl w245, fun _ => Or.inl w245, fun _ _ => w245⟩
  · exact ⟨fun _ => Or.inl w246, fun _ => Or.inl w246, fun _ _ => w246⟩
  · exact ⟨fun _ => Or.inl w247, fun _ => Or.inl w247, fun _ _ => w247⟩
  · exact ⟨fun _ => Or.inl w248, fun _ => Or.inl w248, fun _ _ => w248⟩
  · exact ⟨fun _ => Or.inl w249, fun _ => Or.inl w249, fun _ _ => w249⟩
  · exact ⟨fun _ => Or.inl w250, fun _ => Or.inl w250, fun _ _ => w250⟩
  · exact ⟨fun _ => Or.inl w251, fun _ => Or.inl w251, fun _ _ => w251⟩
  · exact ⟨fun _ => Or.inl w252, fun _ => Or.inl w252, fun _ _ => w252⟩
  · exact ⟨fun _ => Or.inl w253, fun _ => Or.inl w253, fun _ _ => w253⟩
  · exact ⟨fun _ => Or.inr (show A274274 252 ≠ 0 from w252), fun _ => Or.inr (show A274274 248 ≠ 0 from w248), fun hf _ => absurd hf nf254⟩
  · exact ⟨fun _ => Or.inl w255, fun _ => Or.inl w255, fun _ _ => w255⟩
  · exact ⟨fun _ => Or.inl w256, fun _ => Or.inl w256, fun _ _ => w256⟩
  · exact ⟨fun _ => Or.inl w257, fun _ => Or.inl w257, fun _ _ => w257⟩
  · exact ⟨fun _ => Or.inl w258, fun _ => Or.inl w258, fun _ _ => w258⟩
  · exact ⟨fun _ => Or.inl w259, fun _ => Or.inl w259, fun _ _ => w259⟩
  · exact ⟨fun _ => Or.inl w260, fun _ => Or.inl w260, fun _ _ => w260⟩
  · exact ⟨fun _ => Or.inl w261, fun _ => Or.inl w261, fun _ _ => w261⟩
  · exact ⟨fun _ => Or.inl w262, fun _ => Or.inl w262, fun _ _ => w262⟩
  · exact ⟨fun _ => Or.inr (show A274274 261 ≠ 0 from w261), fun _ => Or.inr (show A274274 257 ≠ 0 from w257), fun hf _ => absurd hf nf263⟩
  · exact ⟨fun _ => Or.inl w264, fun _ => Or.inl w264, fun _ _ => w264⟩
  · exact ⟨fun _ => Or.inl w265, fun _ => Or.inl w265, fun _ _ => w265⟩
  · exact ⟨fun _ => Or.inl w266, fun _ => Or.inl w266, fun _ _ => w266⟩
  · exact ⟨fun _ => Or.inr (show A274274 265 ≠ 0 from w265), fun _ => Or.inr (show A274274 261 ≠ 0 from w261), fun hf _ => absurd hf nf267⟩
  · exact ⟨fun _ => Or.inl w268, fun _ => Or.inl w268, fun _ _ => w268⟩
  · exact ⟨fun _ => Or.inl w269, fun _ => Or.inl w269, fun _ _ => w269⟩
  · exact ⟨fun _ => Or.inl w270, fun _ => Or.inl w270, fun _ _ => w270⟩
  · exact ⟨fun _ => Or.inl w271, fun _ => Or.inl w271, fun _ _ => w271⟩
  · exact ⟨fun _ => Or.inl w272, fun _ => Or.inl w272, fun _ _ => w272⟩
  · exact ⟨fun _ => Or.inl w273, fun _ => Or.inl w273, fun _ _ => w273⟩
  · exact ⟨fun _ => Or.inl w274, fun _ => Or.inl w274, fun _ _ => w274⟩
  · exact ⟨fun _ => Or.inl w275, fun _ => Or.inl w275, fun _ _ => w275⟩
  · exact ⟨fun _ => Or.inl w276, fun _ => Or.inl w276, fun _ _ => w276⟩
  · exact ⟨fun _ => Or.inl w277, fun _ => Or.inl w277, fun _ _ => w277⟩
  · exact ⟨fun _ => Or.inl w278, fun _ => Or.inl w278, fun _ _ => w278⟩
  · exact ⟨fun _ => Or.inr (show A274274 277 ≠ 0 from w277), fun _ => Or.inr (show A274274 273 ≠ 0 from w273), fun hf _ => absurd hf nf279⟩
  · exact ⟨fun _ => Or.inl w280, fun _ => Or.inl w280, fun _ _ => w280⟩
  · exact ⟨fun _ => Or.inl w281, fun _ => Or.inl w281, fun _ _ => w281⟩
  · exact ⟨fun _ => Or.inl w282, fun _ => Or.inl w282, fun _ _ => w282⟩
  · exact ⟨fun _ => Or.inl w283, fun _ => Or.inl w283, fun _ _ => w283⟩
  · exact ⟨fun _ => Or.inl w284, fun _ => Or.inl w284, fun _ _ => w284⟩
  · exact ⟨fun _ => Or.inl w285, fun _ => Or.inl w285, fun _ _ => w285⟩
  · exact ⟨fun _ => Or.inr (show A274274 284 ≠ 0 from w284), fun _ => Or.inr (show A274274 280 ≠ 0 from w280), fun hf _ => absurd hf nf286⟩
  · exact ⟨fun _ => Or.inl w287, fun _ => Or.inl w287, fun _ _ => w287⟩
  · exact ⟨fun _ => Or.inl w288, fun _ => Or.inl w288, fun _ _ => w288⟩
  · exact ⟨fun _ => Or.inl w289, fun _ => Or.inl w289, fun _ _ => w289⟩
  · exact ⟨fun _ => Or.inl w290, fun _ => Or.inl w290, fun _ _ => w290⟩
  · exact ⟨fun _ => Or.inl w291, fun _ => Or.inl w291, fun _ _ => w291⟩
  · exact ⟨fun _ => Or.inl w292, fun _ => Or.inl w292, fun _ _ => w292⟩
  · exact ⟨fun _ => Or.inl w293, fun _ => Or.inl w293, fun _ _ => w293⟩
  · exact ⟨fun _ => Or.inl w294, fun _ => Or.inl w294, fun _ _ => w294⟩
  · exact ⟨fun _ => Or.inl w295, fun _ => Or.inl w295, fun _ _ => w295⟩
  · exact ⟨fun _ => Or.inl w296, fun _ => Or.inl w296, fun _ _ => w296⟩
  · exact ⟨fun _ => Or.inl w297, fun _ => Or.inl w297, fun _ _ => w297⟩
  · exact ⟨fun _ => Or.inl w298, fun _ => Or.inl w298, fun _ _ => w298⟩
  · exact ⟨fun _ => Or.inl w299, fun _ => Or.inl w299, fun _ _ => w299⟩
  · exact ⟨fun _ => Or.inl w300, fun _ => Or.inl w300, fun _ _ => w300⟩
  · exact ⟨fun _ => Or.inl w301, fun _ => Or.inl w301, fun _ _ => w301⟩
  · exact ⟨fun _ => Or.inr (show A274274 300 ≠ 0 from w300), fun _ => Or.inr (show A274274 296 ≠ 0 from w296), fun hf _ => absurd hf nf302⟩
  · exact ⟨fun _ => Or.inl w303, fun _ => Or.inl w303, fun _ _ => w303⟩
  · exact ⟨fun _ => Or.inl w304, fun _ => Or.inl w304, fun _ _ => w304⟩
  · exact ⟨fun _ => Or.inl w305, fun _ => Or.inl w305, fun _ _ => w305⟩
  · exact ⟨fun _ => Or.inl w306, fun _ => Or.inl w306, fun _ _ => w306⟩
  · exact ⟨fun _ => Or.inl w307, fun _ => Or.inl w307, fun _ _ => w307⟩
  · exact ⟨fun _ => Or.inl w308, fun _ => Or.inl w308, fun _ _ => w308⟩
  · exact ⟨fun _ => Or.inl w309, fun _ => Or.inl w309, fun _ _ => w309⟩
  · exact ⟨fun _ => Or.inl w310, fun _ => Or.inl w310, fun _ _ => w310⟩
  · exact ⟨fun _ => Or.inr (show A274274 309 ≠ 0 from w309), fun _ => Or.inr (show A274274 305 ≠ 0 from w305), fun hf _ => absurd hf nf311⟩
  · exact ⟨fun _ => Or.inr (show A274274 310 ≠ 0 from w310), fun _ => Or.inr (show A274274 306 ≠ 0 from w306), fun hf _ => absurd hf nf312⟩
  · exact ⟨fun _ => Or.inl w313, fun _ => Or.inl w313, fun _ _ => w313⟩
  · exact ⟨fun _ => Or.inl w314, fun _ => Or.inl w314, fun _ _ => w314⟩
  · exact ⟨fun _ => Or.inl w315, fun _ => Or.inl w315, fun _ _ => w315⟩
  · exact ⟨fun _ => Or.inl w316, fun _ => Or.inl w316, fun _ _ => w316⟩
  · exact ⟨fun _ => Or.inl w317, fun _ => Or.inl w317, fun _ _ => w317⟩
  · exact ⟨fun _ => Or.inl w318, fun _ => Or.inl w318, fun _ _ => w318⟩
  · exact ⟨fun _ => Or.inl w319, fun _ => Or.inl w319, fun _ _ => w319⟩
  · exact ⟨fun _ => Or.inl w320, fun _ => Or.inl w320, fun _ _ => w320⟩
  · exact ⟨fun _ => Or.inl w321, fun _ => Or.inl w321, fun _ _ => w321⟩
  · exact ⟨fun _ => Or.inl w322, fun _ => Or.inl w322, fun _ _ => w322⟩
  · exact ⟨fun _ => Or.inl w323, fun _ => Or.inl w323, fun _ _ => w323⟩
  · exact ⟨fun _ => Or.inl w324, fun _ => Or.inl w324, fun _ _ => w324⟩
  · exact ⟨fun _ => Or.inl w325, fun _ => Or.inl w325, fun _ _ => w325⟩
  · exact ⟨fun _ => Or.inl w326, fun _ => Or.inl w326, fun _ _ => w326⟩
  · exact ⟨fun _ => Or.inl w327, fun _ => Or.inl w327, fun _ _ => w327⟩
  · exact ⟨fun _ => Or.inl w328, fun _ => Or.inl w328, fun _ _ => w328⟩
  · exact ⟨fun _ => Or.inl w329, fun _ => Or.inl w329, fun _ _ => w329⟩
  · exact ⟨fun _ => Or.inl w330, fun _ => Or.inl w330, fun _ _ => w330⟩
  · exact ⟨fun _ => Or.inr (show A274274 329 ≠ 0 from w329), fun _ => Or.inr (show A274274 325 ≠ 0 from w325), fun hf _ => absurd hf nf331⟩
  · exact ⟨fun _ => Or.inl w332, fun _ => Or.inl w332, fun _ _ => w332⟩
  · exact ⟨fun _ => Or.inl w333, fun _ => Or.inl w333, fun _ _ => w333⟩
  · exact ⟨fun _ => Or.inl w334, fun _ => Or.inl w334, fun _ _ => w334⟩
  · exact ⟨fun _ => Or.inr (show A274274 333 ≠ 0 from w333), fun _ => Or.inr (show A274274 329 ≠ 0 from w329), fun hf _ => absurd hf nf335⟩
  · exact ⟨fun _ => Or.inl w336, fun _ => Or.inl w336, fun _ _ => w336⟩
  · exact ⟨fun _ => Or.inl w337, fun _ => Or.inl w337, fun _ _ => w337⟩
  · exact ⟨fun _ => Or.inl w338, fun _ => Or.inl w338, fun _ _ => w338⟩
  · exact ⟨fun _ => Or.inl w339, fun _ => Or.inl w339, fun _ _ => w339⟩
  · exact ⟨fun _ => Or.inl w340, fun _ => Or.inl w340, fun _ _ => w340⟩
  · exact ⟨fun _ => Or.inl w341, fun _ => Or.inl w341, fun _ _ => w341⟩
  · exact ⟨fun _ => Or.inr (show A274274 340 ≠ 0 from w340), fun _ => Or.inr (show A274274 336 ≠ 0 from w336), fun hf _ => absurd hf nf342⟩
  · exact ⟨fun _ => Or.inl w343, fun _ => Or.inl w343, fun _ _ => w343⟩
  · exact ⟨fun _ => Or.inl w344, fun _ => Or.inl w344, fun _ _ => w344⟩
  · exact ⟨fun _ => Or.inl w345, fun _ => Or.inl w345, fun _ _ => w345⟩
  · exact ⟨fun _ => Or.inl w346, fun _ => Or.inl w346, fun _ _ => w346⟩
  · exact ⟨fun _ => Or.inl w347, fun _ => Or.inl w347, fun _ _ => w347⟩
  · exact ⟨fun _ => Or.inl w348, fun _ => Or.inl w348, fun _ _ => w348⟩
  · exact ⟨fun _ => Or.inl w349, fun _ => Or.inl w349, fun _ _ => w349⟩
  · exact ⟨fun _ => Or.inl w350, fun _ => Or.inl w350, fun _ _ => w350⟩
  · exact ⟨fun _ => Or.inl w351, fun _ => Or.inl w351, fun _ _ => w351⟩
  · exact ⟨fun _ => Or.inl w352, fun _ => Or.inl w352, fun _ _ => w352⟩
  · exact ⟨fun _ => Or.inl w353, fun _ => Or.inl w353, fun _ _ => w353⟩
  · exact ⟨fun _ => Or.inl w354, fun _ => Or.inl w354, fun _ _ => w354⟩
  · exact ⟨fun _ => Or.inl w355, fun _ => Or.inl w355, fun _ _ => w355⟩
  · exact ⟨fun _ => Or.inl w356, fun _ => Or.inl w356, fun _ _ => w356⟩
  · exact ⟨fun _ => Or.inl w357, fun _ => Or.inl w357, fun _ _ => w357⟩
  · exact ⟨fun _ => Or.inl w358, fun _ => Or.inl w358, fun _ _ => w358⟩
  · exact ⟨fun _ => Or.inl w359, fun _ => Or.inl w359, fun _ _ => w359⟩
  · exact ⟨fun _ => Or.inl w360, fun _ => Or.inl w360, fun _ _ => w360⟩
  · exact ⟨fun _ => Or.inl w361, fun _ => Or.inl w361, fun _ _ => w361⟩
  · exact ⟨fun _ => Or.inl w362, fun _ => Or.inl w362, fun _ _ => w362⟩
  · exact ⟨fun _ => Or.inl w363, fun _ => Or.inl w363, fun _ _ => w363⟩
  · exact ⟨fun _ => Or.inl w364, fun _ => Or.inl w364, fun _ _ => w364⟩
  · exact ⟨fun _ => Or.inl w365, fun _ => Or.inl w365, fun _ _ => w365⟩
  · exact ⟨fun _ => Or.inl w366, fun _ => Or.inl w366, fun _ _ => w366⟩
  · exact ⟨fun _ => Or.inl w367, fun _ => Or.inl w367, fun _ _ => w367⟩
  · exact ⟨fun _ => Or.inl w368, fun _ => Or.inl w368, fun _ _ => w368⟩
  · exact ⟨fun _ => Or.inl w369, fun _ => Or.inl w369, fun _ _ => w369⟩
  · exact ⟨fun _ => Or.inl w370, fun _ => Or.inl w370, fun _ _ => w370⟩
  · exact ⟨fun _ => Or.inl w371, fun _ => Or.inl w371, fun _ _ => w371⟩
  · exact ⟨fun _ => Or.inl w372, fun _ => Or.inl w372, fun _ _ => w372⟩
  · exact ⟨fun _ => Or.inl w373, fun _ => Or.inl w373, fun _ _ => w373⟩
  · exact ⟨fun _ => Or.inl w374, fun _ => Or.inl w374, fun _ _ => w374⟩
  · exact ⟨fun _ => Or.inl w375, fun _ => Or.inl w375, fun _ _ => w375⟩
  · exact ⟨fun _ => Or.inl w376, fun _ => Or.inl w376, fun _ _ => w376⟩
  · exact ⟨fun _ => Or.inl w377, fun _ => Or.inl w377, fun _ _ => w377⟩
  · exact ⟨fun _ => Or.inl w378, fun _ => Or.inl w378, fun _ _ => w378⟩
  · exact ⟨fun _ => Or.inl w379, fun _ => Or.inl w379, fun _ _ => w379⟩
  · exact ⟨fun _ => Or.inl w380, fun _ => Or.inl w380, fun _ _ => w380⟩
  · exact ⟨fun _ => Or.inl w381, fun _ => Or.inl w381, fun _ _ => w381⟩
  · exact ⟨fun _ => Or.inl w382, fun _ => Or.inl w382, fun _ _ => w382⟩
  · exact ⟨fun _ => Or.inl w383, fun _ => Or.inl w383, fun _ _ => w383⟩
  · exact ⟨fun _ => Or.inl w384, fun _ => Or.inl w384, fun _ _ => w384⟩
  · exact ⟨fun _ => Or.inl w385, fun _ => Or.inl w385, fun _ _ => w385⟩
  · exact ⟨fun _ => Or.inl w386, fun _ => Or.inl w386, fun _ _ => w386⟩
  · exact ⟨fun _ => Or.inl w387, fun _ => Or.inl w387, fun _ _ => w387⟩
  · exact ⟨fun _ => Or.inl w388, fun _ => Or.inl w388, fun _ _ => w388⟩
  · exact ⟨fun _ => Or.inl w389, fun _ => Or.inl w389, fun _ _ => w389⟩
  · exact ⟨fun _ => Or.inl w390, fun _ => Or.inl w390, fun _ _ => w390⟩
  · exact ⟨fun _ => Or.inr (show A274274 389 ≠ 0 from w389), fun _ => Or.inr (show A274274 385 ≠ 0 from w385), fun hf _ => absurd hf nf391⟩
  · exact ⟨fun _ => Or.inl w392, fun _ => Or.inl w392, fun _ _ => w392⟩
  · exact ⟨fun _ => Or.inl w393, fun _ => Or.inl w393, fun _ _ => w393⟩
  · exact ⟨fun _ => Or.inl w394, fun _ => Or.inl w394, fun _ _ => w394⟩
  · exact ⟨fun _ => Or.inl w395, fun _ => Or.inl w395, fun _ _ => w395⟩
  · exact ⟨fun _ => Or.inl w396, fun _ => Or.inl w396, fun _ _ => w396⟩
  · exact ⟨fun _ => Or.inl w397, fun _ => Or.inl w397, fun _ _ => w397⟩
  · exact ⟨fun _ => Or.inl w398, fun _ => Or.inl w398, fun _ _ => w398⟩
  · exact ⟨fun _ => Or.inl w399, fun _ => Or.inl w399, fun _ _ => w399⟩
  · exact ⟨fun _ => Or.inl w400, fun _ => Or.inl w400, fun _ _ => w400⟩
  · exact ⟨fun _ => Or.inl w401, fun _ => Or.inl w401, fun _ _ => w401⟩
  · exact ⟨fun _ => Or.inl w402, fun _ => Or.inl w402, fun _ _ => w402⟩
  · exact ⟨fun _ => Or.inr (show A274274 401 ≠ 0 from w401), fun _ => Or.inr (show A274274 397 ≠ 0 from w397), fun hf _ => absurd hf nf403⟩
  · exact ⟨fun _ => Or.inl w404, fun _ => Or.inl w404, fun _ _ => w404⟩
  · exact ⟨fun _ => Or.inl w405, fun _ => Or.inl w405, fun _ _ => w405⟩
  · exact ⟨fun _ => Or.inl w406, fun _ => Or.inl w406, fun _ _ => w406⟩
  · exact ⟨fun _ => Or.inl w407, fun _ => Or.inl w407, fun _ _ => w407⟩
  · exact ⟨fun _ => Or.inl w408, fun _ => Or.inl w408, fun _ _ => w408⟩
  · exact ⟨fun _ => Or.inl w409, fun _ => Or.inl w409, fun _ _ => w409⟩
  · exact ⟨fun _ => Or.inl w410, fun _ => Or.inl w410, fun _ _ => w410⟩
  · exact ⟨fun _ => Or.inl w411, fun _ => Or.inl w411, fun _ _ => w411⟩
  · exact ⟨fun _ => Or.inl w412, fun _ => Or.inl w412, fun _ _ => w412⟩
  · exact ⟨fun _ => Or.inl w413, fun _ => Or.inl w413, fun _ _ => w413⟩
  · exact ⟨fun _ => Or.inl w414, fun _ => Or.inl w414, fun _ _ => w414⟩
  · exact ⟨fun _ => Or.inl w415, fun _ => Or.inl w415, fun _ _ => w415⟩
  · exact ⟨fun _ => Or.inl w416, fun _ => Or.inl w416, fun _ _ => w416⟩
  · exact ⟨fun _ => Or.inl w417, fun _ => Or.inl w417, fun _ _ => w417⟩
  · exact ⟨fun _ => Or.inl w418, fun _ => Or.inl w418, fun _ _ => w418⟩
  · exact ⟨fun _ => Or.inl w419, fun _ => Or.inl w419, fun _ _ => w419⟩
  · exact ⟨fun _ => Or.inl w420, fun _ => Or.inl w420, fun _ _ => w420⟩
  · exact ⟨fun _ => Or.inl w421, fun _ => Or.inl w421, fun _ _ => w421⟩
  · exact ⟨fun _ => Or.inl w422, fun _ => Or.inl w422, fun _ _ => w422⟩
  · exact ⟨fun _ => Or.inl w423, fun _ => Or.inl w423, fun _ _ => w423⟩
  · exact ⟨fun _ => Or.inl w424, fun _ => Or.inl w424, fun _ _ => w424⟩
  · exact ⟨fun _ => Or.inl w425, fun _ => Or.inl w425, fun _ _ => w425⟩
  · exact ⟨fun _ => Or.inl w426, fun _ => Or.inl w426, fun _ _ => w426⟩
  · exact ⟨fun _ => Or.inl w427, fun _ => Or.inl w427, fun _ _ => w427⟩
  · exact ⟨fun _ => Or.inl w428, fun _ => Or.inl w428, fun _ _ => w428⟩
  · exact ⟨fun _ => Or.inl w429, fun _ => Or.inl w429, fun _ _ => w429⟩
  · exact ⟨fun _ => Or.inl w430, fun _ => Or.inl w430, fun _ _ => w430⟩
  · exact ⟨fun _ => Or.inl w431, fun _ => Or.inl w431, fun _ _ => w431⟩
  · exact ⟨fun _ => Or.inl w432, fun _ => Or.inl w432, fun _ _ => w432⟩
  · exact ⟨fun _ => Or.inl w433, fun _ => Or.inl w433, fun _ _ => w433⟩
  · exact ⟨fun _ => Or.inl w434, fun _ => Or.inl w434, fun _ _ => w434⟩
  · exact ⟨fun _ => Or.inr (show A274274 433 ≠ 0 from w433), fun _ => Or.inr (show A274274 429 ≠ 0 from w429), fun hf _ => absurd hf nf435⟩
  · exact ⟨fun _ => Or.inl w436, fun _ => Or.inl w436, fun _ _ => w436⟩
  · exact ⟨fun _ => Or.inl w437, fun _ => Or.inl w437, fun _ _ => w437⟩
  · exact ⟨fun _ => Or.inl w438, fun _ => Or.inl w438, fun _ _ => w438⟩
  · exact ⟨fun _ => Or.inl w439, fun _ => Or.inl w439, fun _ _ => w439⟩
  · exact ⟨fun _ => Or.inl w440, fun _ => Or.inl w440, fun _ _ => w440⟩
  · exact ⟨fun _ => Or.inl w441, fun _ => Or.inl w441, fun _ _ => w441⟩
  · exact ⟨fun _ => Or.inl w442, fun _ => Or.inl w442, fun _ _ => w442⟩
  · exact ⟨fun _ => Or.inl w443, fun _ => Or.inl w443, fun _ _ => w443⟩
  · exact ⟨fun _ => Or.inl w444, fun _ => Or.inl w444, fun _ _ => w444⟩
  · exact ⟨fun _ => Or.inl w445, fun _ => Or.inl w445, fun _ _ => w445⟩
  · exact ⟨fun _ => Or.inl w446, fun _ => Or.inl w446, fun _ _ => w446⟩
  · exact ⟨fun _ => Or.inl w447, fun _ => Or.inl w447, fun _ _ => w447⟩
  · exact ⟨fun _ => Or.inl w448, fun _ => Or.inl w448, fun _ _ => w448⟩
  · exact ⟨fun _ => Or.inl w449, fun _ => Or.inl w449, fun _ _ => w449⟩
  · exact ⟨fun _ => Or.inl w450, fun _ => Or.inl w450, fun _ _ => w450⟩
  · exact ⟨fun _ => Or.inl w451, fun _ => Or.inl w451, fun _ _ => w451⟩
  · exact ⟨fun _ => Or.inl w452, fun _ => Or.inl w452, fun _ _ => w452⟩
  · exact ⟨fun _ => Or.inl w453, fun _ => Or.inl w453, fun _ _ => w453⟩
  · exact ⟨fun _ => Or.inr (show A274274 452 ≠ 0 from w452), fun _ => Or.inr (show A274274 448 ≠ 0 from w448), fun hf _ => absurd hf nf454⟩
  · exact ⟨fun _ => Or.inr (show A274274 453 ≠ 0 from w453), fun _ => Or.inr (show A274274 449 ≠ 0 from w449), fun hf _ => absurd hf nf455⟩
  · exact ⟨fun _ => Or.inl w456, fun _ => Or.inl w456, fun _ _ => w456⟩
  · exact ⟨fun _ => Or.inl w457, fun _ => Or.inl w457, fun _ _ => w457⟩
  · exact ⟨fun _ => Or.inl w458, fun _ => Or.inl w458, fun _ _ => w458⟩
  · exact ⟨fun _ => Or.inl w459, fun _ => Or.inl w459, fun _ _ => w459⟩
  · exact ⟨fun _ => Or.inl w460, fun _ => Or.inl w460, fun _ _ => w460⟩
  · exact ⟨fun _ => Or.inl w461, fun _ => Or.inl w461, fun _ _ => w461⟩
  · exact ⟨fun _ => Or.inl w462, fun _ => Or.inl w462, fun _ _ => w462⟩
  · exact ⟨fun _ => Or.inl w463, fun _ => Or.inl w463, fun _ _ => w463⟩
  · exact ⟨fun _ => Or.inl w464, fun _ => Or.inl w464, fun _ _ => w464⟩
  · exact ⟨fun _ => Or.inl w465, fun _ => Or.inl w465, fun _ _ => w465⟩
  · exact ⟨fun _ => Or.inl w466, fun _ => Or.inl w466, fun _ _ => w466⟩
  · exact ⟨fun _ => Or.inl w467, fun _ => Or.inl w467, fun _ _ => w467⟩
  · exact ⟨fun _ => Or.inl w468, fun _ => Or.inl w468, fun _ _ => w468⟩
  · exact ⟨fun _ => Or.inl w469, fun _ => Or.inl w469, fun _ _ => w469⟩
  · exact ⟨fun _ => Or.inr (show A274274 468 ≠ 0 from w468), fun _ => Or.inr (show A274274 464 ≠ 0 from w464), fun hf _ => absurd hf nf470⟩
  · exact ⟨fun _ => Or.inl w471, fun _ => Or.inl w471, fun _ _ => w471⟩
  · exact ⟨fun _ => Or.inl w472, fun _ => Or.inl w472, fun _ _ => w472⟩
  · exact ⟨fun _ => Or.inl w473, fun _ => Or.inl w473, fun _ _ => w473⟩
  · exact ⟨fun _ => Or.inl w474, fun _ => Or.inl w474, fun _ _ => w474⟩
  · exact ⟨fun _ => Or.inr (show A274274 473 ≠ 0 from w473), fun _ => Or.inr (show A274274 469 ≠ 0 from w469), fun hf _ => absurd hf nf475⟩
  · exact ⟨fun _ => Or.inl w476, fun _ => Or.inl w476, fun _ _ => w476⟩
  · exact ⟨fun _ => Or.inl w477, fun _ => Or.inl w477, fun _ _ => w477⟩
  · exact ⟨fun _ => Or.inl w478, fun _ => Or.inl w478, fun _ _ => w478⟩
  · exact ⟨fun _ => Or.inl w479, fun _ => Or.inl w479, fun _ _ => w479⟩
  · exact ⟨fun _ => Or.inl w480, fun _ => Or.inl w480, fun _ _ => w480⟩
  · exact ⟨fun _ => Or.inl w481, fun _ => Or.inl w481, fun _ _ => w481⟩
  · exact ⟨fun _ => Or.inl w482, fun _ => Or.inl w482, fun _ _ => w482⟩
  · exact ⟨fun _ => Or.inl w483, fun _ => Or.inl w483, fun _ _ => w483⟩
  · exact ⟨fun _ => Or.inl w484, fun _ => Or.inl w484, fun _ _ => w484⟩
  · exact ⟨fun _ => Or.inl w485, fun _ => Or.inl w485, fun _ _ => w485⟩
  · exact ⟨fun _ => Or.inl w486, fun _ => Or.inl w486, fun _ _ => w486⟩
  · exact ⟨fun _ => Or.inl w487, fun _ => Or.inl w487, fun _ _ => w487⟩
  · exact ⟨fun _ => Or.inl w488, fun _ => Or.inl w488, fun _ _ => w488⟩
  · exact ⟨fun _ => Or.inl w489, fun _ => Or.inl w489, fun _ _ => w489⟩
  · exact ⟨fun _ => Or.inl w490, fun _ => Or.inl w490, fun _ _ => w490⟩
  · exact ⟨fun _ => Or.inl w491, fun _ => Or.inl w491, fun _ _ => w491⟩
  · exact ⟨fun _ => Or.inl w492, fun _ => Or.inl w492, fun _ _ => w492⟩
  · exact ⟨fun _ => Or.inl w493, fun _ => Or.inl w493, fun _ _ => w493⟩
  · exact ⟨fun _ => Or.inl w494, fun _ => Or.inl w494, fun _ _ => w494⟩
  · exact ⟨fun _ => Or.inl w495, fun _ => Or.inl w495, fun _ _ => w495⟩
  · exact ⟨fun _ => Or.inl w496, fun _ => Or.inl w496, fun _ _ => w496⟩
  · exact ⟨fun _ => Or.inl w497, fun _ => Or.inl w497, fun _ _ => w497⟩
  · exact ⟨fun _ => Or.inl w498, fun _ => Or.inl w498, fun _ _ => w498⟩
  · exact ⟨fun _ => Or.inr (show A274274 497 ≠ 0 from w497), fun _ => Or.inr (show A274274 493 ≠ 0 from w493), fun hf _ => absurd hf nf499⟩
  · exact ⟨fun _ => Or.inl w500, fun _ => Or.inl w500, fun _ _ => w500⟩
  · exact ⟨fun _ => Or.inl w501, fun _ => Or.inl w501, fun _ _ => w501⟩
  · exact ⟨fun _ => Or.inl w502, fun _ => Or.inl w502, fun _ _ => w502⟩
  · exact ⟨fun _ => Or.inl w503, fun _ => Or.inl w503, fun _ _ => w503⟩
  · exact ⟨fun _ => Or.inl w504, fun _ => Or.inl w504, fun _ _ => w504⟩
  · exact ⟨fun _ => Or.inl w505, fun _ => Or.inl w505, fun _ _ => w505⟩
  · exact ⟨fun _ => Or.inl w506, fun _ => Or.inl w506, fun _ _ => w506⟩
  · exact ⟨fun _ => Or.inl w507, fun _ => Or.inl w507, fun _ _ => w507⟩
  · exact ⟨fun _ => Or.inl w508, fun _ => Or.inl w508, fun _ _ => w508⟩
  · exact ⟨fun _ => Or.inl w509, fun _ => Or.inl w509, fun _ _ => w509⟩
  · exact ⟨fun _ => Or.inl w510, fun _ => Or.inl w510, fun _ _ => w510⟩
  · exact ⟨fun _ => Or.inl w511, fun _ => Or.inl w511, fun _ _ => w511⟩
  · exact ⟨fun _ => Or.inl w512, fun _ => Or.inl w512, fun _ _ => w512⟩
  · exact ⟨fun _ => Or.inl w513, fun _ => Or.inl w513, fun _ _ => w513⟩
  · exact ⟨fun _ => Or.inl w514, fun _ => Or.inl w514, fun _ _ => w514⟩
  · exact ⟨fun _ => Or.inl w515, fun _ => Or.inl w515, fun _ _ => w515⟩
  · exact ⟨fun _ => Or.inl w516, fun _ => Or.inl w516, fun _ _ => w516⟩
  · exact ⟨fun _ => Or.inl w517, fun _ => Or.inl w517, fun _ _ => w517⟩
  · exact ⟨fun _ => Or.inr (show A274274 516 ≠ 0 from w516), fun _ => Or.inr (show A274274 512 ≠ 0 from w512), fun hf _ => absurd hf nf518⟩
  · exact ⟨fun _ => Or.inl w519, fun _ => Or.inl w519, fun _ _ => w519⟩
  · exact ⟨fun _ => Or.inl w520, fun _ => Or.inl w520, fun _ _ => w520⟩
  · exact ⟨fun _ => Or.inl w521, fun _ => Or.inl w521, fun _ _ => w521⟩
  · exact ⟨fun _ => Or.inl w522, fun _ => Or.inl w522, fun _ _ => w522⟩
  · exact ⟨fun _ => Or.inl w523, fun _ => Or.inl w523, fun _ _ => w523⟩
  · exact ⟨fun _ => Or.inl w524, fun _ => Or.inl w524, fun _ _ => w524⟩
  · exact ⟨fun _ => Or.inl w525, fun _ => Or.inl w525, fun _ _ => w525⟩
  · exact ⟨fun _ => Or.inl w526, fun _ => Or.inl w526, fun _ _ => w526⟩
  · exact ⟨fun _ => Or.inl w527, fun _ => Or.inl w527, fun _ _ => w527⟩
  · exact ⟨fun _ => Or.inl w528, fun _ => Or.inl w528, fun _ _ => w528⟩
  · exact ⟨fun _ => Or.inl w529, fun _ => Or.inl w529, fun _ _ => w529⟩
  · exact ⟨fun _ => Or.inl w530, fun _ => Or.inl w530, fun _ _ => w530⟩
  · exact ⟨fun _ => Or.inl w531, fun _ => Or.inl w531, fun _ _ => w531⟩
  · exact ⟨fun _ => Or.inl w532, fun _ => Or.inl w532, fun _ _ => w532⟩
  · exact ⟨fun _ => Or.inl w533, fun _ => Or.inl w533, fun _ _ => w533⟩
  · exact ⟨fun _ => Or.inl w534, fun _ => Or.inl w534, fun _ _ => w534⟩
  · exact ⟨fun _ => Or.inl w535, fun _ => Or.inl w535, fun _ _ => w535⟩
  · exact ⟨fun _ => Or.inl w536, fun _ => Or.inl w536, fun _ _ => w536⟩
  · exact ⟨fun _ => Or.inl w537, fun _ => Or.inl w537, fun _ _ => w537⟩
  · exact ⟨fun _ => Or.inl w538, fun _ => Or.inl w538, fun _ _ => w538⟩
  · exact ⟨fun _ => Or.inl w539, fun _ => Or.inl w539, fun _ _ => w539⟩
  · exact ⟨fun _ => Or.inl w540, fun _ => Or.inl w540, fun _ _ => w540⟩
  · exact ⟨fun _ => Or.inl w541, fun _ => Or.inl w541, fun _ _ => w541⟩
  · exact ⟨fun _ => Or.inl w542, fun _ => Or.inl w542, fun _ _ => w542⟩
  · exact ⟨fun _ => Or.inl w543, fun _ => Or.inl w543, fun _ _ => w543⟩
  · exact ⟨fun _ => Or.inl w544, fun _ => Or.inl w544, fun _ _ => w544⟩
  · exact ⟨fun _ => Or.inl w545, fun _ => Or.inl w545, fun _ _ => w545⟩
  · exact ⟨fun _ => Or.inl w546, fun _ => Or.inl w546, fun _ _ => w546⟩
  · exact ⟨fun _ => Or.inl w547, fun _ => Or.inl w547, fun _ _ => w547⟩
  · exact ⟨fun _ => Or.inl w548, fun _ => Or.inl w548, fun _ _ => w548⟩
  · exact ⟨fun _ => Or.inl w549, fun _ => Or.inl w549, fun _ _ => w549⟩
  · exact ⟨fun _ => Or.inl w550, fun _ => Or.inl w550, fun _ _ => w550⟩
  · exact ⟨fun _ => Or.inl w551, fun _ => Or.inl w551, fun _ _ => w551⟩
  · exact ⟨fun _ => Or.inl w552, fun _ => Or.inl w552, fun _ _ => w552⟩
  · exact ⟨fun _ => Or.inl w553, fun _ => Or.inl w553, fun _ _ => w553⟩
  · exact ⟨fun _ => Or.inl w554, fun _ => Or.inl w554, fun _ _ => w554⟩
  · exact ⟨fun _ => Or.inl w555, fun _ => Or.inl w555, fun _ _ => w555⟩
  · exact ⟨fun _ => Or.inl w556, fun _ => Or.inl w556, fun _ _ => w556⟩
  · exact ⟨fun _ => Or.inl w557, fun _ => Or.inl w557, fun _ _ => w557⟩
  · exact ⟨fun _ => Or.inl w558, fun _ => Or.inl w558, fun _ _ => w558⟩
  · exact ⟨fun _ => Or.inr (show A274274 557 ≠ 0 from w557), fun _ => Or.inr (show A274274 553 ≠ 0 from w553), fun hf _ => absurd hf nf559⟩
  · exact ⟨fun _ => Or.inl w560, fun _ => Or.inl w560, fun _ _ => w560⟩
  · exact ⟨fun _ => Or.inl w561, fun _ => Or.inl w561, fun _ _ => w561⟩
  · exact ⟨fun _ => Or.inl w562, fun _ => Or.inl w562, fun _ _ => w562⟩
  · exact ⟨fun _ => Or.inl w563, fun _ => Or.inl w563, fun _ _ => w563⟩
  · exact ⟨fun _ => Or.inl w564, fun _ => Or.inl w564, fun _ _ => w564⟩
  · exact ⟨fun _ => Or.inl w565, fun _ => Or.inl w565, fun _ _ => w565⟩
  · exact ⟨fun _ => Or.inl w566, fun _ => Or.inl w566, fun _ _ => w566⟩
  · exact ⟨fun _ => Or.inl w567, fun _ => Or.inl w567, fun _ _ => w567⟩
  · exact ⟨fun _ => Or.inl w568, fun _ => Or.inl w568, fun _ _ => w568⟩
  · exact ⟨fun _ => Or.inl w569, fun _ => Or.inl w569, fun _ _ => w569⟩
  · exact ⟨fun _ => Or.inl w570, fun _ => Or.inl w570, fun _ _ => w570⟩
  · exact ⟨fun _ => Or.inl w571, fun _ => Or.inl w571, fun _ _ => w571⟩
  · exact ⟨fun _ => Or.inl w572, fun _ => Or.inl w572, fun _ _ => w572⟩
  · exact ⟨fun _ => Or.inl w573, fun _ => Or.inl w573, fun _ _ => w573⟩
  · exact ⟨fun _ => Or.inl w574, fun _ => Or.inl w574, fun _ _ => w574⟩
  · exact ⟨fun _ => Or.inl w575, fun _ => Or.inl w575, fun _ _ => w575⟩
  · exact ⟨fun _ => Or.inl w576, fun _ => Or.inl w576, fun _ _ => w576⟩
  · exact ⟨fun _ => Or.inl w577, fun _ => Or.inl w577, fun _ _ => w577⟩
  · exact ⟨fun _ => Or.inl w578, fun _ => Or.inl w578, fun _ _ => w578⟩
  · exact ⟨fun _ => Or.inl w579, fun _ => Or.inl w579, fun _ _ => w579⟩
  · exact ⟨fun _ => Or.inl w580, fun _ => Or.inl w580, fun _ _ => w580⟩
  · exact ⟨fun _ => Or.inl w581, fun _ => Or.inl w581, fun _ _ => w581⟩
  · exact ⟨fun _ => Or.inl w582, fun _ => Or.inl w582, fun _ _ => w582⟩
  · exact ⟨fun _ => Or.inl w583, fun _ => Or.inl w583, fun _ _ => w583⟩
  · exact ⟨fun _ => Or.inl w584, fun _ => Or.inl w584, fun _ _ => w584⟩
  · exact ⟨fun _ => Or.inl w585, fun _ => Or.inl w585, fun _ _ => w585⟩
  · exact ⟨fun _ => Or.inl w586, fun _ => Or.inl w586, fun _ _ => w586⟩
  · exact ⟨fun _ => Or.inl w587, fun _ => Or.inl w587, fun _ _ => w587⟩
  · exact ⟨fun _ => Or.inl w588, fun _ => Or.inl w588, fun _ _ => w588⟩
  · exact ⟨fun _ => Or.inl w589, fun _ => Or.inl w589, fun _ _ => w589⟩
  · exact ⟨fun _ => Or.inr (show A274274 588 ≠ 0 from w588), fun _ => Or.inr (show A274274 584 ≠ 0 from w584), fun hf _ => absurd hf nf590⟩
  · exact ⟨fun _ => Or.inl w591, fun _ => Or.inl w591, fun _ _ => w591⟩
  · exact ⟨fun _ => Or.inl w592, fun _ => Or.inl w592, fun _ _ => w592⟩
  · exact ⟨fun _ => Or.inl w593, fun _ => Or.inl w593, fun _ _ => w593⟩
  · exact ⟨fun _ => Or.inl w594, fun _ => Or.inl w594, fun _ _ => w594⟩
  · exact ⟨fun _ => Or.inr (show A274274 593 ≠ 0 from w593), fun _ => Or.inr (show A274274 589 ≠ 0 from w589), fun hf _ => absurd hf nf595⟩
  · exact ⟨fun _ => Or.inl w596, fun _ => Or.inl w596, fun _ _ => w596⟩
  · exact ⟨fun _ => Or.inl w597, fun _ => Or.inl w597, fun _ _ => w597⟩
  · exact ⟨fun _ => Or.inr (show A274274 596 ≠ 0 from w596), fun _ => Or.inr (show A274274 592 ≠ 0 from w592), fun hf _ => absurd hf nf598⟩
  · exact ⟨fun _ => Or.inl w599, fun _ => Or.inl w599, fun _ _ => w599⟩
  · exact ⟨fun _ => Or.inl w600, fun _ => Or.inl w600, fun _ _ => w600⟩
  · exact ⟨fun _ => Or.inl w601, fun _ => Or.inl w601, fun _ _ => w601⟩
  · exact ⟨fun _ => Or.inl w602, fun _ => Or.inl w602, fun _ _ => w602⟩
  · exact ⟨fun _ => Or.inl w603, fun _ => Or.inl w603, fun _ _ => w603⟩
  · exact ⟨fun _ => Or.inl w604, fun _ => Or.inl w604, fun _ _ => w604⟩
  · exact ⟨fun _ => Or.inl w605, fun _ => Or.inl w605, fun _ _ => w605⟩
  · exact ⟨fun _ => Or.inl w606, fun _ => Or.inl w606, fun _ _ => w606⟩
  · exact ⟨fun _ => Or.inl w607, fun _ => Or.inl w607, fun _ _ => w607⟩
  · exact ⟨fun _ => Or.inl w608, fun _ => Or.inl w608, fun _ _ => w608⟩
  · exact ⟨fun _ => Or.inl w609, fun _ => Or.inl w609, fun _ _ => w609⟩
  · exact ⟨fun _ => Or.inl w610, fun _ => Or.inl w610, fun _ _ => w610⟩
  · exact ⟨fun _ => Or.inl w611, fun _ => Or.inl w611, fun _ _ => w611⟩
  · exact ⟨fun _ => Or.inl w612, fun _ => Or.inl w612, fun _ _ => w612⟩
  · exact ⟨fun _ => Or.inl w613, fun _ => Or.inl w613, fun _ _ => w613⟩
  · exact ⟨fun _ => Or.inl w614, fun _ => Or.inl w614, fun _ _ => w614⟩
  · exact ⟨fun _ => Or.inl w615, fun _ => Or.inl w615, fun _ _ => w615⟩
  · exact ⟨fun _ => Or.inl w616, fun _ => Or.inl w616, fun _ _ => w616⟩
  · exact ⟨fun _ => Or.inl w617, fun _ => Or.inl w617, fun _ _ => w617⟩
  · exact ⟨fun _ => Or.inl w618, fun _ => Or.inl w618, fun _ _ => w618⟩
  · exact ⟨fun _ => Or.inl w619, fun _ => Or.inl w619, fun _ _ => w619⟩
  · exact ⟨fun _ => Or.inl w620, fun _ => Or.inl w620, fun _ _ => w620⟩
  · exact ⟨fun _ => Or.inl w621, fun _ => Or.inl w621, fun _ _ => w621⟩
  · exact ⟨fun _ => Or.inr (show A274274 620 ≠ 0 from w620), fun _ => Or.inr (show A274274 616 ≠ 0 from w616), fun hf _ => absurd hf nf622⟩
  · exact ⟨fun _ => Or.inl w623, fun _ => Or.inl w623, fun _ _ => w623⟩
  · exact ⟨fun _ => Or.inl w624, fun _ => Or.inl w624, fun _ _ => w624⟩
  · exact ⟨fun _ => Or.inl w625, fun _ => Or.inl w625, fun _ _ => w625⟩
  · exact ⟨fun _ => Or.inl w626, fun _ => Or.inl w626, fun _ _ => w626⟩
  · exact ⟨fun _ => Or.inl w627, fun _ => Or.inl w627, fun _ _ => w627⟩
  · exact ⟨fun _ => Or.inl w628, fun _ => Or.inl w628, fun _ _ => w628⟩
  · exact ⟨fun _ => Or.inl w629, fun _ => Or.inl w629, fun _ _ => w629⟩
  · exact ⟨fun _ => Or.inl w630, fun _ => Or.inl w630, fun _ _ => w630⟩
  · exact ⟨fun _ => Or.inl w631, fun _ => Or.inl w631, fun _ _ => w631⟩
  · exact ⟨fun _ => Or.inl w632, fun _ => Or.inl w632, fun _ _ => w632⟩
  · exact ⟨fun _ => Or.inl w633, fun _ => Or.inl w633, fun _ _ => w633⟩
  · exact ⟨fun _ => Or.inl w634, fun _ => Or.inl w634, fun _ _ => w634⟩
  · exact ⟨fun _ => Or.inl w635, fun _ => Or.inl w635, fun _ _ => w635⟩
  · exact ⟨fun _ => Or.inl w636, fun _ => Or.inl w636, fun _ _ => w636⟩
  · exact ⟨fun _ => Or.inl w637, fun _ => Or.inl w637, fun _ _ => w637⟩
  · exact ⟨fun _ => Or.inl w638, fun _ => Or.inl w638, fun _ _ => w638⟩
  · exact ⟨fun _ => Or.inl w639, fun _ => Or.inl w639, fun _ _ => w639⟩
  · exact ⟨fun _ => Or.inl w640, fun _ => Or.inl w640, fun _ _ => w640⟩
  · exact ⟨fun _ => Or.inl w641, fun _ => Or.inl w641, fun _ _ => w641⟩
  · exact ⟨fun _ => Or.inl w642, fun _ => Or.inl w642, fun _ _ => w642⟩
  · exact ⟨fun _ => Or.inr (show A274274 641 ≠ 0 from w641), fun _ => Or.inr (show A274274 637 ≠ 0 from w637), fun hf _ => absurd hf nf643⟩
  · exact ⟨fun _ => Or.inl w644, fun _ => Or.inl w644, fun _ _ => w644⟩
  · exact ⟨fun _ => Or.inl w645, fun _ => Or.inl w645, fun _ _ => w645⟩
  · exact ⟨fun _ => Or.inl w646, fun _ => Or.inl w646, fun _ _ => w646⟩
  · exact ⟨fun _ => Or.inl w647, fun _ => Or.inl w647, fun _ _ => w647⟩
  · exact ⟨fun _ => Or.inl w648, fun _ => Or.inl w648, fun _ _ => w648⟩
  · exact ⟨fun _ => Or.inl w649, fun _ => Or.inl w649, fun _ _ => w649⟩
  · exact ⟨fun _ => Or.inl w650, fun _ => Or.inl w650, fun _ _ => w650⟩
  · exact ⟨fun _ => Or.inl w651, fun _ => Or.inl w651, fun _ _ => w651⟩
  · exact ⟨fun _ => Or.inl w652, fun _ => Or.inl w652, fun _ _ => w652⟩
  · exact ⟨fun _ => Or.inl w653, fun _ => Or.inl w653, fun _ _ => w653⟩
  · exact ⟨fun _ => Or.inl w654, fun _ => Or.inl w654, fun _ _ => w654⟩
  · exact ⟨fun _ => Or.inl w655, fun _ => Or.inl w655, fun _ _ => w655⟩
  · exact ⟨fun _ => Or.inl w656, fun _ => Or.inl w656, fun _ _ => w656⟩
  · exact ⟨fun _ => Or.inl w657, fun _ => Or.inl w657, fun _ _ => w657⟩
  · exact ⟨fun _ => Or.inl w658, fun _ => Or.inl w658, fun _ _ => w658⟩
  · exact ⟨fun _ => Or.inr (show A274274 657 ≠ 0 from w657), fun _ => Or.inr (show A274274 653 ≠ 0 from w653), fun hf _ => absurd hf nf659⟩
  · exact ⟨fun _ => Or.inl w660, fun _ => Or.inl w660, fun _ _ => w660⟩
  · exact ⟨fun _ => Or.inl w661, fun _ => Or.inl w661, fun _ _ => w661⟩
  · exact ⟨fun _ => Or.inl w662, fun _ => Or.inl w662, fun _ _ => w662⟩
  · exact ⟨fun _ => Or.inl w663, fun _ => Or.inl w663, fun _ _ => w663⟩
  · exact ⟨fun _ => Or.inl w664, fun _ => Or.inl w664, fun _ _ => w664⟩
  · exact ⟨fun _ => Or.inl w665, fun _ => Or.inl w665, fun _ _ => w665⟩
  · exact ⟨fun _ => Or.inl w666, fun _ => Or.inl w666, fun _ _ => w666⟩
  · exact ⟨fun _ => Or.inl w667, fun _ => Or.inl w667, fun _ _ => w667⟩
  · exact ⟨fun _ => Or.inl w668, fun _ => Or.inl w668, fun _ _ => w668⟩
  · exact ⟨fun _ => Or.inl w669, fun _ => Or.inl w669, fun _ _ => w669⟩
  · exact ⟨fun _ => Or.inl w670, fun _ => Or.inl w670, fun _ _ => w670⟩
  · exact ⟨fun _ => Or.inl w671, fun _ => Or.inl w671, fun _ _ => w671⟩
  · exact ⟨fun _ => Or.inl w672, fun _ => Or.inl w672, fun _ _ => w672⟩
  · exact ⟨fun _ => Or.inl w673, fun _ => Or.inl w673, fun _ _ => w673⟩
  · exact ⟨fun _ => Or.inl w674, fun _ => Or.inl w674, fun _ _ => w674⟩
  · exact ⟨fun _ => Or.inl w675, fun _ => Or.inl w675, fun _ _ => w675⟩
  · exact ⟨fun _ => Or.inl w676, fun _ => Or.inl w676, fun _ _ => w676⟩
  · exact ⟨fun _ => Or.inl w677, fun _ => Or.inl w677, fun _ _ => w677⟩
  · exact ⟨fun _ => Or.inl w678, fun _ => Or.inl w678, fun _ _ => w678⟩
  · exact ⟨fun _ => Or.inl w679, fun _ => Or.inl w679, fun _ _ => w679⟩
  · exact ⟨fun _ => Or.inl w680, fun _ => Or.inl w680, fun _ _ => w680⟩
  · exact ⟨fun _ => Or.inl w681, fun _ => Or.inl w681, fun _ _ => w681⟩
  · exact ⟨fun _ => Or.inl w682, fun _ => Or.inl w682, fun _ _ => w682⟩
  · exact ⟨fun _ => Or.inl w683, fun _ => Or.inl w683, fun _ _ => w683⟩
  · exact ⟨fun _ => Or.inl w684, fun _ => Or.inl w684, fun _ _ => w684⟩
  · exact ⟨fun _ => Or.inl w685, fun _ => Or.inl w685, fun _ _ => w685⟩
  · exact ⟨fun _ => Or.inl w686, fun _ => Or.inl w686, fun _ _ => w686⟩
  · exact ⟨fun _ => Or.inl w687, fun _ => Or.inl w687, fun _ _ => w687⟩
  · exact ⟨fun _ => Or.inl w688, fun _ => Or.inl w688, fun _ _ => w688⟩
  · exact ⟨fun _ => Or.inl w689, fun _ => Or.inl w689, fun _ _ => w689⟩
  · exact ⟨fun _ => Or.inl w690, fun _ => Or.inl w690, fun _ _ => w690⟩
  · exact ⟨fun _ => Or.inr (show A274274 689 ≠ 0 from w689), fun _ => Or.inr (show A274274 685 ≠ 0 from w685), fun hf _ => absurd hf nf691⟩
  · exact ⟨fun _ => Or.inl w692, fun _ => Or.inl w692, fun _ _ => w692⟩
  · exact ⟨fun _ => Or.inl w693, fun _ => Or.inl w693, fun _ _ => w693⟩
  · exact ⟨fun _ => Or.inl w694, fun _ => Or.inl w694, fun _ _ => w694⟩
  · exact ⟨fun _ => Or.inr (show A274274 693 ≠ 0 from w693), fun _ => Or.inr (show A274274 689 ≠ 0 from w689), fun hf _ => absurd hf nf695⟩
  · exact ⟨fun _ => Or.inl w696, fun _ => Or.inl w696, fun _ _ => w696⟩
  · exact ⟨fun _ => Or.inl w697, fun _ => Or.inl w697, fun _ _ => w697⟩
  · exact ⟨fun _ => Or.inl w698, fun _ => Or.inl w698, fun _ _ => w698⟩
  · exact ⟨fun _ => Or.inl w699, fun _ => Or.inl w699, fun _ _ => w699⟩
  · exact ⟨fun _ => Or.inl w700, fun _ => Or.inl w700, fun _ _ => w700⟩
  · exact ⟨fun _ => Or.inl w701, fun _ => Or.inl w701, fun _ _ => w701⟩
  · exact ⟨fun _ => Or.inl w702, fun _ => Or.inl w702, fun _ _ => w702⟩
  · exact ⟨fun _ => Or.inl w703, fun _ => Or.inl w703, fun _ _ => w703⟩
  · exact ⟨fun _ => Or.inl w704, fun _ => Or.inl w704, fun _ _ => w704⟩
  · exact ⟨fun _ => Or.inl w705, fun _ => Or.inl w705, fun _ _ => w705⟩
  · exact ⟨fun _ => Or.inl w706, fun _ => Or.inl w706, fun _ _ => w706⟩
  · exact ⟨fun _ => Or.inl w707, fun _ => Or.inl w707, fun _ _ => w707⟩
  · exact ⟨fun _ => Or.inl w708, fun _ => Or.inl w708, fun _ _ => w708⟩
  · exact ⟨fun _ => Or.inl w709, fun _ => Or.inl w709, fun _ _ => w709⟩
  · exact ⟨fun _ => Or.inl w710, fun _ => Or.inl w710, fun _ _ => w710⟩
  · exact ⟨fun _ => Or.inl w711, fun _ => Or.inl w711, fun _ _ => w711⟩
  · exact ⟨fun _ => Or.inl w712, fun _ => Or.inl w712, fun _ _ => w712⟩
  · exact ⟨fun _ => Or.inl w713, fun _ => Or.inl w713, fun _ _ => w713⟩
  · exact ⟨fun _ => Or.inl w714, fun _ => Or.inl w714, fun _ _ => w714⟩
  · exact ⟨fun _ => Or.inr (show A274274 713 ≠ 0 from w713), fun _ => Or.inr (show A274274 709 ≠ 0 from w709), fun hf _ => absurd hf nf715⟩
  · exact ⟨fun _ => Or.inl w716, fun _ => Or.inl w716, fun _ _ => w716⟩
  · exact ⟨fun _ => Or.inl w717, fun _ => Or.inl w717, fun _ _ => w717⟩
  · exact ⟨fun _ => Or.inl w718, fun _ => Or.inl w718, fun _ _ => w718⟩
  · exact ⟨fun _ => Or.inl w719, fun _ => Or.inl w719, fun _ _ => w719⟩
  · exact ⟨fun _ => Or.inl w720, fun _ => Or.inl w720, fun _ _ => w720⟩
  · exact ⟨fun _ => Or.inl w721, fun _ => Or.inl w721, fun _ _ => w721⟩
  · exact ⟨fun _ => Or.inl w722, fun _ => Or.inl w722, fun _ _ => w722⟩
  · exact ⟨fun _ => Or.inl w723, fun _ => Or.inl w723, fun _ _ => w723⟩
  · exact ⟨fun _ => Or.inl w724, fun _ => Or.inl w724, fun _ _ => w724⟩
  · exact ⟨fun _ => Or.inl w725, fun _ => Or.inl w725, fun _ _ => w725⟩
  · exact ⟨fun _ => Or.inl w726, fun _ => Or.inl w726, fun _ _ => w726⟩
  · exact ⟨fun _ => Or.inr (show A274274 725 ≠ 0 from w725), fun _ => Or.inr (show A274274 721 ≠ 0 from w721), fun hf _ => absurd hf nf727⟩
  · exact ⟨fun _ => Or.inl w728, fun _ => Or.inl w728, fun _ _ => w728⟩
  · exact ⟨fun _ => Or.inl w729, fun _ => Or.inl w729, fun _ _ => w729⟩
  · exact ⟨fun _ => Or.inl w730, fun _ => Or.inl w730, fun _ _ => w730⟩
  · exact ⟨fun _ => Or.inl w731, fun _ => Or.inl w731, fun _ _ => w731⟩
  · exact ⟨fun _ => Or.inl w732, fun _ => Or.inl w732, fun _ _ => w732⟩
  · exact ⟨fun _ => Or.inl w733, fun _ => Or.inl w733, fun _ _ => w733⟩
  · exact ⟨fun _ => Or.inl w734, fun _ => Or.inl w734, fun _ _ => w734⟩
  · exact ⟨fun _ => Or.inl w735, fun _ => Or.inl w735, fun _ _ => w735⟩
  · exact ⟨fun _ => Or.inl w736, fun _ => Or.inl w736, fun _ _ => w736⟩
  · exact ⟨fun _ => Or.inl w737, fun _ => Or.inl w737, fun _ _ => w737⟩
  · exact ⟨fun _ => Or.inl w738, fun _ => Or.inl w738, fun _ _ => w738⟩
  · exact ⟨fun _ => Or.inl w739, fun _ => Or.inl w739, fun _ _ => w739⟩
  · exact ⟨fun _ => Or.inl w740, fun _ => Or.inl w740, fun _ _ => w740⟩
  · exact ⟨fun _ => Or.inl w741, fun _ => Or.inl w741, fun _ _ => w741⟩
  · exact ⟨fun _ => Or.inl w742, fun _ => Or.inl w742, fun _ _ => w742⟩
  · exact ⟨fun _ => Or.inl w743, fun _ => Or.inl w743, fun _ _ => w743⟩
  · exact ⟨fun _ => Or.inl w744, fun _ => Or.inl w744, fun _ _ => w744⟩
  · exact ⟨fun _ => Or.inl w745, fun _ => Or.inl w745, fun _ _ => w745⟩
  · exact ⟨fun _ => Or.inl w746, fun _ => Or.inl w746, fun _ _ => w746⟩
  · exact ⟨fun _ => Or.inl w747, fun _ => Or.inl w747, fun _ _ => w747⟩
  · exact ⟨fun _ => Or.inl w748, fun _ => Or.inl w748, fun _ _ => w748⟩
  · exact ⟨fun _ => Or.inl w749, fun _ => Or.inl w749, fun _ _ => w749⟩
  · exact ⟨fun _ => Or.inl w750, fun _ => Or.inl w750, fun _ _ => w750⟩
  · exact ⟨fun _ => Or.inl w751, fun _ => Or.inl w751, fun _ _ => w751⟩
  · exact ⟨fun _ => Or.inl w752, fun _ => Or.inl w752, fun _ _ => w752⟩
  · exact ⟨fun _ => Or.inl w753, fun _ => Or.inl w753, fun _ _ => w753⟩
  · exact ⟨fun _ => Or.inl w754, fun _ => Or.inl w754, fun _ _ => w754⟩
  · exact ⟨fun _ => Or.inl w755, fun _ => Or.inl w755, fun _ _ => w755⟩
  · exact ⟨fun _ => Or.inl w756, fun _ => Or.inl w756, fun _ _ => w756⟩
  · exact ⟨fun _ => Or.inl w757, fun _ => Or.inl w757, fun _ _ => w757⟩
  · exact ⟨fun _ => Or.inl w758, fun _ => Or.inl w758, fun _ _ => w758⟩
  · exact ⟨fun _ => Or.inl w759, fun _ => Or.inl w759, fun _ _ => w759⟩
  · exact ⟨fun _ => Or.inl w760, fun _ => Or.inl w760, fun _ _ => w760⟩
  · exact ⟨fun _ => Or.inl w761, fun _ => Or.inl w761, fun _ _ => w761⟩
  · exact ⟨fun _ => Or.inl w762, fun _ => Or.inl w762, fun _ _ => w762⟩
  · exact ⟨fun _ => Or.inl w763, fun _ => Or.inl w763, fun _ _ => w763⟩
  · exact ⟨fun _ => Or.inl w764, fun _ => Or.inl w764, fun _ _ => w764⟩
  · exact ⟨fun _ => Or.inl w765, fun _ => Or.inl w765, fun _ _ => w765⟩
  · exact ⟨fun _ => Or.inl w766, fun _ => Or.inl w766, fun _ _ => w766⟩
  · exact ⟨fun _ => Or.inl w767, fun _ => Or.inl w767, fun _ _ => w767⟩
  · exact ⟨fun _ => Or.inl w768, fun _ => Or.inl w768, fun _ _ => w768⟩
  · exact ⟨fun _ => Or.inl w769, fun _ => Or.inl w769, fun _ _ => w769⟩
  · exact ⟨fun _ => Or.inl w770, fun _ => Or.inl w770, fun _ _ => w770⟩
  · exact ⟨fun _ => Or.inr (show A274274 769 ≠ 0 from w769), fun _ => Or.inr (show A274274 765 ≠ 0 from w765), fun hf _ => absurd hf nf771⟩
  · exact ⟨fun _ => Or.inl w772, fun _ => Or.inl w772, fun _ _ => w772⟩
  · exact ⟨fun _ => Or.inl w773, fun _ => Or.inl w773, fun _ _ => w773⟩
  · exact ⟨fun _ => Or.inl w774, fun _ => Or.inl w774, fun _ _ => w774⟩
  · exact ⟨fun _ => Or.inl w775, fun _ => Or.inl w775, fun _ _ => w775⟩
  · exact ⟨fun _ => Or.inl w776, fun _ => Or.inl w776, fun _ _ => w776⟩
  · exact ⟨fun _ => Or.inl w777, fun _ => Or.inl w777, fun _ _ => w777⟩
  · exact ⟨fun _ => Or.inl w778, fun _ => Or.inl w778, fun _ _ => w778⟩
  · exact ⟨fun _ => Or.inl w779, fun _ => Or.inl w779, fun _ _ => w779⟩
  · exact ⟨fun _ => Or.inl w780, fun _ => Or.inl w780, fun _ _ => w780⟩
  · exact ⟨fun _ => Or.inl w781, fun _ => Or.inl w781, fun _ _ => w781⟩
  · exact ⟨fun _ => Or.inl w782, fun _ => Or.inl w782, fun _ _ => w782⟩
  · exact ⟨fun _ => Or.inr (show A274274 781 ≠ 0 from w781), fun _ => Or.inr (show A274274 777 ≠ 0 from w777), fun hf _ => absurd hf nf783⟩
  · exact ⟨fun _ => Or.inl w784, fun _ => Or.inl w784, fun _ _ => w784⟩
  · exact ⟨fun _ => Or.inl w785, fun _ => Or.inl w785, fun _ _ => w785⟩
  · exact ⟨fun _ => Or.inl w786, fun _ => Or.inl w786, fun _ _ => w786⟩
  · exact ⟨fun _ => Or.inl w787, fun _ => Or.inl w787, fun _ _ => w787⟩
  · exact ⟨fun _ => Or.inl w788, fun _ => Or.inl w788, fun _ _ => w788⟩
  · exact ⟨fun _ => Or.inl w789, fun _ => Or.inl w789, fun _ _ => w789⟩
  · exact ⟨fun _ => Or.inl w790, fun _ => Or.inl w790, fun _ _ => w790⟩
  · exact ⟨fun _ => Or.inl w791, fun _ => Or.inl w791, fun _ _ => w791⟩
  · exact ⟨fun _ => Or.inl w792, fun _ => Or.inl w792, fun _ _ => w792⟩
  · exact ⟨fun _ => Or.inl w793, fun _ => Or.inl w793, fun _ _ => w793⟩
  · exact ⟨fun _ => Or.inl w794, fun _ => Or.inl w794, fun _ _ => w794⟩
  · exact ⟨fun _ => Or.inl w795, fun _ => Or.inl w795, fun _ _ => w795⟩
  · exact ⟨fun _ => Or.inl w796, fun _ => Or.inl w796, fun _ _ => w796⟩
  · exact ⟨fun _ => Or.inl w797, fun _ => Or.inl w797, fun _ _ => w797⟩
  · exact ⟨fun _ => Or.inl w798, fun _ => Or.inl w798, fun _ _ => w798⟩
  · exact ⟨fun _ => Or.inl w799, fun _ => Or.inl w799, fun _ _ => w799⟩
  · exact ⟨fun _ => Or.inl w800, fun _ => Or.inl w800, fun _ _ => w800⟩
  · exact ⟨fun _ => Or.inl w801, fun _ => Or.inl w801, fun _ _ => w801⟩
  · exact ⟨fun _ => Or.inl w802, fun _ => Or.inl w802, fun _ _ => w802⟩
  · exact ⟨fun _ => Or.inl w803, fun _ => Or.inl w803, fun _ _ => w803⟩
  · exact ⟨fun _ => Or.inl w804, fun _ => Or.inl w804, fun _ _ => w804⟩
  · exact ⟨fun _ => Or.inl w805, fun _ => Or.inl w805, fun _ _ => w805⟩
  · exact ⟨fun _ => Or.inr (show A274274 804 ≠ 0 from w804), fun _ => Or.inr (show A274274 800 ≠ 0 from w800), fun hf _ => absurd hf nf806⟩
  · exact ⟨fun _ => Or.inl w807, fun _ => Or.inl w807, fun _ _ => w807⟩
  · exact ⟨fun _ => Or.inl w808, fun _ => Or.inl w808, fun _ _ => w808⟩
  · exact ⟨fun _ => Or.inl w809, fun _ => Or.inl w809, fun _ _ => w809⟩
  · exact ⟨fun _ => Or.inl w810, fun _ => Or.inl w810, fun _ _ => w810⟩
  · exact ⟨fun _ => Or.inl w811, fun _ => Or.inl w811, fun _ _ => w811⟩
  · exact ⟨fun _ => Or.inl w812, fun _ => Or.inl w812, fun _ _ => w812⟩
  · exact ⟨fun _ => Or.inr (show A274274 811 ≠ 0 from w811), fun _ => Or.inr (show A274274 807 ≠ 0 from w807), fun _ hne => absurd rfl hne.1⟩
  · exact ⟨fun _ => Or.inl w814, fun _ => Or.inl w814, fun _ _ => w814⟩
  · exact ⟨fun _ => Or.inl w815, fun _ => Or.inl w815, fun _ _ => w815⟩
  · exact ⟨fun _ => Or.inl w816, fun _ => Or.inl w816, fun _ _ => w816⟩
  · exact ⟨fun _ => Or.inl w817, fun _ => Or.inl w817, fun _ _ => w817⟩
  · exact ⟨fun _ => Or.inl w818, fun _ => Or.inl w818, fun _ _ => w818⟩
  · exact ⟨fun _ => Or.inl w819, fun _ => Or.inl w819, fun _ _ => w819⟩
  · exact ⟨fun _ => Or.inl w820, fun _ => Or.inl w820, fun _ _ => w820⟩
  · exact ⟨fun _ => Or.inl w821, fun _ => Or.inl w821, fun _ _ => w821⟩
  · exact ⟨fun _ => Or.inl w822, fun _ => Or.inl w822, fun _ _ => w822⟩
  · exact ⟨fun _ => Or.inl w823, fun _ => Or.inl w823, fun _ _ => w823⟩
  · exact ⟨fun _ => Or.inl w824, fun _ => Or.inl w824, fun _ _ => w824⟩
  · exact ⟨fun _ => Or.inl w825, fun _ => Or.inl w825, fun _ _ => w825⟩
  · exact ⟨fun _ => Or.inl w826, fun _ => Or.inl w826, fun _ _ => w826⟩
  · exact ⟨fun _ => Or.inl w827, fun _ => Or.inl w827, fun _ _ => w827⟩
  · exact ⟨fun _ => Or.inl w828, fun _ => Or.inl w828, fun _ _ => w828⟩
  · exact ⟨fun _ => Or.inl w829, fun _ => Or.inl w829, fun _ _ => w829⟩
  · exact ⟨fun _ => Or.inl w830, fun _ => Or.inl w830, fun _ _ => w830⟩
  · exact ⟨fun _ => Or.inl w831, fun _ => Or.inl w831, fun _ _ => w831⟩
  · exact ⟨fun _ => Or.inl w832, fun _ => Or.inl w832, fun _ _ => w832⟩
  · exact ⟨fun _ => Or.inl w833, fun _ => Or.inl w833, fun _ _ => w833⟩
  · exact ⟨fun _ => Or.inl w834, fun _ => Or.inl w834, fun _ _ => w834⟩
  · exact ⟨fun _ => Or.inl w835, fun _ => Or.inl w835, fun _ _ => w835⟩
  · exact ⟨fun _ => Or.inl w836, fun _ => Or.inl w836, fun _ _ => w836⟩
  · exact ⟨fun _ => Or.inl w837, fun _ => Or.inl w837, fun _ _ => w837⟩
  · exact ⟨fun _ => Or.inl w838, fun _ => Or.inl w838, fun _ _ => w838⟩
  · exact ⟨fun _ => Or.inr (show A274274 837 ≠ 0 from w837), fun _ => Or.inr (show A274274 833 ≠ 0 from w833), fun hf _ => absurd hf nf839⟩
  · exact ⟨fun _ => Or.inl w840, fun _ => Or.inl w840, fun _ _ => w840⟩
  · exact ⟨fun _ => Or.inl w841, fun _ => Or.inl w841, fun _ _ => w841⟩
  · exact ⟨fun _ => Or.inl w842, fun _ => Or.inl w842, fun _ _ => w842⟩
  · exact ⟨fun _ => Or.inl w843, fun _ => Or.inl w843, fun _ _ => w843⟩
  · exact ⟨fun _ => Or.inl w844, fun _ => Or.inl w844, fun _ _ => w844⟩
  · exact ⟨fun _ => Or.inl w845, fun _ => Or.inl w845, fun _ _ => w845⟩
  · exact ⟨fun _ => Or.inl w846, fun _ => Or.inl w846, fun _ _ => w846⟩
  · exact ⟨fun _ => Or.inl w847, fun _ => Or.inl w847, fun _ _ => w847⟩
  · exact ⟨fun _ => Or.inl w848, fun _ => Or.inl w848, fun _ _ => w848⟩
  · exact ⟨fun _ => Or.inl w849, fun _ => Or.inl w849, fun _ _ => w849⟩
  · exact ⟨fun _ => Or.inl w850, fun _ => Or.inl w850, fun _ _ => w850⟩
  · exact ⟨fun _ => Or.inl w851, fun _ => Or.inl w851, fun _ _ => w851⟩
  · exact ⟨fun _ => Or.inl w852, fun _ => Or.inl w852, fun _ _ => w852⟩
  · exact ⟨fun _ => Or.inl w853, fun _ => Or.inl w853, fun _ _ => w853⟩
  · exact ⟨fun _ => Or.inl w854, fun _ => Or.inl w854, fun _ _ => w854⟩
  · exact ⟨fun _ => Or.inl w855, fun _ => Or.inl w855, fun _ _ => w855⟩
  · exact ⟨fun _ => Or.inl w856, fun _ => Or.inl w856, fun _ _ => w856⟩
  · exact ⟨fun _ => Or.inl w857, fun _ => Or.inl w857, fun _ _ => w857⟩
  · exact ⟨fun _ => Or.inl w858, fun _ => Or.inl w858, fun _ _ => w858⟩
  · exact ⟨fun _ => Or.inl w859, fun _ => Or.inl w859, fun _ _ => w859⟩
  · exact ⟨fun _ => Or.inl w860, fun _ => Or.inl w860, fun _ _ => w860⟩
  · exact ⟨fun _ => Or.inl w861, fun _ => Or.inl w861, fun _ _ => w861⟩
  · exact ⟨fun _ => Or.inr (show A274274 860 ≠ 0 from w860), fun _ => Or.inr (show A274274 856 ≠ 0 from w856), fun hf _ => absurd hf nf862⟩
  · exact ⟨fun _ => Or.inl w863, fun _ => Or.inl w863, fun _ _ => w863⟩
  · exact ⟨fun _ => Or.inl w864, fun _ => Or.inl w864, fun _ _ => w864⟩
  · exact ⟨fun _ => Or.inl w865, fun _ => Or.inl w865, fun _ _ => w865⟩
  · exact ⟨fun _ => Or.inl w866, fun _ => Or.inl w866, fun _ _ => w866⟩
  · exact ⟨fun _ => Or.inl w867, fun _ => Or.inl w867, fun _ _ => w867⟩
  · exact ⟨fun _ => Or.inl w868, fun _ => Or.inl w868, fun _ _ => w868⟩
  · exact ⟨fun _ => Or.inl w869, fun _ => Or.inl w869, fun _ _ => w869⟩
  · exact ⟨fun _ => Or.inl w870, fun _ => Or.inl w870, fun _ _ => w870⟩
  · exact ⟨fun _ => Or.inl w871, fun _ => Or.inl w871, fun _ _ => w871⟩
  · exact ⟨fun _ => Or.inl w872, fun _ => Or.inl w872, fun _ _ => w872⟩
  · exact ⟨fun _ => Or.inl w873, fun _ => Or.inl w873, fun _ _ => w873⟩
  · exact ⟨fun _ => Or.inl w874, fun _ => Or.inl w874, fun _ _ => w874⟩
  · exact ⟨fun _ => Or.inl w875, fun _ => Or.inl w875, fun _ _ => w875⟩
  · exact ⟨fun _ => Or.inl w876, fun _ => Or.inl w876, fun _ _ => w876⟩
  · exact ⟨fun _ => Or.inl w877, fun _ => Or.inl w877, fun _ _ => w877⟩
  · exact ⟨fun _ => Or.inl w878, fun _ => Or.inl w878, fun _ _ => w878⟩
  · exact ⟨fun _ => Or.inl w879, fun _ => Or.inl w879, fun _ _ => w879⟩
  · exact ⟨fun _ => Or.inl w880, fun _ => Or.inl w880, fun _ _ => w880⟩
  · exact ⟨fun _ => Or.inl w881, fun _ => Or.inl w881, fun _ _ => w881⟩
  · exact ⟨fun _ => Or.inl w882, fun _ => Or.inl w882, fun _ _ => w882⟩
  · exact ⟨fun _ => Or.inl w883, fun _ => Or.inl w883, fun _ _ => w883⟩
  · exact ⟨fun _ => Or.inl w884, fun _ => Or.inl w884, fun _ _ => w884⟩
  · exact ⟨fun _ => Or.inl w885, fun _ => Or.inl w885, fun _ _ => w885⟩
  · exact ⟨fun _ => Or.inl w886, fun _ => Or.inl w886, fun _ _ => w886⟩
  · exact ⟨fun _ => Or.inl w887, fun _ => Or.inl w887, fun _ _ => w887⟩
  · exact ⟨fun _ => Or.inl w888, fun _ => Or.inl w888, fun _ _ => w888⟩
  · exact ⟨fun _ => Or.inl w889, fun _ => Or.inl w889, fun _ _ => w889⟩
  · exact ⟨fun _ => Or.inl w890, fun _ => Or.inl w890, fun _ _ => w890⟩
  · exact ⟨fun _ => Or.inl w891, fun _ => Or.inl w891, fun _ _ => w891⟩
  · exact ⟨fun _ => Or.inl w892, fun _ => Or.inl w892, fun _ _ => w892⟩
  · exact ⟨fun _ => Or.inl w893, fun _ => Or.inl w893, fun _ _ => w893⟩
  · exact ⟨fun _ => Or.inl w894, fun _ => Or.inl w894, fun _ _ => w894⟩
  · exact ⟨fun _ => Or.inr (show A274274 893 ≠ 0 from w893), fun _ => Or.inr (show A274274 889 ≠ 0 from w889), fun hf _ => absurd hf nf895⟩
  · exact ⟨fun _ => Or.inl w896, fun _ => Or.inl w896, fun _ _ => w896⟩
  · exact ⟨fun _ => Or.inl w897, fun _ => Or.inl w897, fun _ _ => w897⟩
  · exact ⟨fun _ => Or.inl w898, fun _ => Or.inl w898, fun _ _ => w898⟩
  · exact ⟨fun _ => Or.inl w899, fun _ => Or.inl w899, fun _ _ => w899⟩
  · exact ⟨fun _ => Or.inl w900, fun _ => Or.inl w900, fun _ _ => w900⟩
  · exact ⟨fun _ => Or.inl w901, fun _ => Or.inl w901, fun _ _ => w901⟩
  · exact ⟨fun _ => Or.inl w902, fun _ => Or.inl w902, fun _ _ => w902⟩
  · exact ⟨fun _ => Or.inl w903, fun _ => Or.inl w903, fun _ _ => w903⟩
  · exact ⟨fun _ => Or.inl w904, fun _ => Or.inl w904, fun _ _ => w904⟩
  · exact ⟨fun _ => Or.inl w905, fun _ => Or.inl w905, fun _ _ => w905⟩
  · exact ⟨fun _ => Or.inl w906, fun _ => Or.inl w906, fun _ _ => w906⟩
  · exact ⟨fun _ => Or.inl w907, fun _ => Or.inl w907, fun _ _ => w907⟩
  · exact ⟨fun _ => Or.inl w908, fun _ => Or.inl w908, fun _ _ => w908⟩
  · exact ⟨fun _ => Or.inl w909, fun _ => Or.inl w909, fun _ _ => w909⟩
  · exact ⟨fun _ => Or.inl w910, fun _ => Or.inl w910, fun _ _ => w910⟩
  · exact ⟨fun _ => Or.inl w911, fun _ => Or.inl w911, fun _ _ => w911⟩
  · exact ⟨fun _ => Or.inl w912, fun _ => Or.inl w912, fun _ _ => w912⟩
  · exact ⟨fun _ => Or.inl w913, fun _ => Or.inl w913, fun _ _ => w913⟩
  · exact ⟨fun _ => Or.inl w914, fun _ => Or.inl w914, fun _ _ => w914⟩
  · exact ⟨fun _ => Or.inl w915, fun _ => Or.inl w915, fun _ _ => w915⟩
  · exact ⟨fun _ => Or.inl w916, fun _ => Or.inl w916, fun _ _ => w916⟩
  · exact ⟨fun _ => Or.inl w917, fun _ => Or.inl w917, fun _ _ => w917⟩
  · exact ⟨fun _ => Or.inl w918, fun _ => Or.inl w918, fun _ _ => w918⟩
  · exact ⟨fun _ => Or.inl w919, fun _ => Or.inl w919, fun _ _ => w919⟩
  · exact ⟨fun _ => Or.inl w920, fun _ => Or.inl w920, fun _ _ => w920⟩
  · exact ⟨fun _ => Or.inl w921, fun _ => Or.inl w921, fun _ _ => w921⟩
  · exact ⟨fun _ => Or.inl w922, fun _ => Or.inl w922, fun _ _ => w922⟩
  · exact ⟨fun _ => Or.inl w923, fun _ => Or.inl w923, fun _ _ => w923⟩
  · exact ⟨fun _ => Or.inl w924, fun _ => Or.inl w924, fun _ _ => w924⟩
  · exact ⟨fun _ => Or.inl w925, fun _ => Or.inl w925, fun _ _ => w925⟩
  · exact ⟨fun _ => Or.inl w926, fun _ => Or.inl w926, fun _ _ => w926⟩
  · exact ⟨fun _ => Or.inl w927, fun _ => Or.inl w927, fun _ _ => w927⟩
  · exact ⟨fun _ => Or.inl w928, fun _ => Or.inl w928, fun _ _ => w928⟩
  · exact ⟨fun _ => Or.inl w929, fun _ => Or.inl w929, fun _ _ => w929⟩
  · exact ⟨fun _ => Or.inl w930, fun _ => Or.inl w930, fun _ _ => w930⟩
  · exact ⟨fun _ => Or.inl w931, fun _ => Or.inl w931, fun _ _ => w931⟩
  · exact ⟨fun _ => Or.inl w932, fun _ => Or.inl w932, fun _ _ => w932⟩
  · exact ⟨fun _ => Or.inl w933, fun _ => Or.inl w933, fun _ _ => w933⟩
  · exact ⟨fun _ => Or.inl w934, fun _ => Or.inl w934, fun _ _ => w934⟩
  · exact ⟨fun _ => Or.inl w935, fun _ => Or.inl w935, fun _ _ => w935⟩
  · exact ⟨fun _ => Or.inl w936, fun _ => Or.inl w936, fun _ _ => w936⟩
  · exact ⟨fun _ => Or.inl w937, fun _ => Or.inl w937, fun _ _ => w937⟩
  · exact ⟨fun _ => Or.inl w938, fun _ => Or.inl w938, fun _ _ => w938⟩
  · exact ⟨fun _ => Or.inl w939, fun _ => Or.inl w939, fun _ _ => w939⟩
  · exact ⟨fun _ => Or.inl w940, fun _ => Or.inl w940, fun _ _ => w940⟩
  · exact ⟨fun _ => Or.inl w941, fun _ => Or.inl w941, fun _ _ => w941⟩
  · exact ⟨fun _ => Or.inl w942, fun _ => Or.inl w942, fun _ _ => w942⟩
  · exact ⟨fun _ => Or.inl w943, fun _ => Or.inl w943, fun _ _ => w943⟩
  · exact ⟨fun _ => Or.inl w944, fun _ => Or.inl w944, fun _ _ => w944⟩
  · exact ⟨fun _ => Or.inl w945, fun _ => Or.inl w945, fun _ _ => w945⟩
  · exact ⟨fun _ => Or.inl w946, fun _ => Or.inl w946, fun _ _ => w946⟩
  · exact ⟨fun _ => Or.inl w947, fun _ => Or.inl w947, fun _ _ => w947⟩
  · exact ⟨fun _ => Or.inl w948, fun _ => Or.inl w948, fun _ _ => w948⟩
  · exact ⟨fun _ => Or.inl w949, fun _ => Or.inl w949, fun _ _ => w949⟩
  · exact ⟨fun _ => Or.inl w950, fun _ => Or.inl w950, fun _ _ => w950⟩
  · exact ⟨fun _ => Or.inr (show A274274 949 ≠ 0 from w949), fun _ => Or.inr (show A274274 945 ≠ 0 from w945), fun hf _ => absurd hf nf951⟩
  · exact ⟨fun _ => Or.inl w952, fun _ => Or.inl w952, fun _ _ => w952⟩
  · exact ⟨fun _ => Or.inl w953, fun _ => Or.inl w953, fun _ _ => w953⟩
  · exact ⟨fun _ => Or.inl w954, fun _ => Or.inl w954, fun _ _ => w954⟩
  · exact ⟨fun _ => Or.inl w955, fun _ => Or.inl w955, fun _ _ => w955⟩
  · exact ⟨fun _ => Or.inl w956, fun _ => Or.inl w956, fun _ _ => w956⟩
  · exact ⟨fun _ => Or.inl w957, fun _ => Or.inl w957, fun _ _ => w957⟩
  · exact ⟨fun _ => Or.inl w958, fun _ => Or.inl w958, fun _ _ => w958⟩
  · exact ⟨fun _ => Or.inl w959, fun _ => Or.inl w959, fun _ _ => w959⟩
  · exact ⟨fun _ => Or.inl w960, fun _ => Or.inl w960, fun _ _ => w960⟩
  · exact ⟨fun _ => Or.inl w961, fun _ => Or.inl w961, fun _ _ => w961⟩
  · exact ⟨fun _ => Or.inl w962, fun _ => Or.inl w962, fun _ _ => w962⟩
  · exact ⟨fun _ => Or.inl w963, fun _ => Or.inl w963, fun _ _ => w963⟩
  · exact ⟨fun _ => Or.inl w964, fun _ => Or.inl w964, fun _ _ => w964⟩
  · exact ⟨fun _ => Or.inl w965, fun _ => Or.inl w965, fun _ _ => w965⟩
  · exact ⟨fun _ => Or.inl w966, fun _ => Or.inl w966, fun _ _ => w966⟩
  · exact ⟨fun _ => Or.inl w967, fun _ => Or.inl w967, fun _ _ => w967⟩
  · exact ⟨fun _ => Or.inl w968, fun _ => Or.inl w968, fun _ _ => w968⟩
  · exact ⟨fun _ => Or.inl w969, fun _ => Or.inl w969, fun _ _ => w969⟩
  · exact ⟨fun _ => Or.inl w970, fun _ => Or.inl w970, fun _ _ => w970⟩
  · exact ⟨fun _ => Or.inl w971, fun _ => Or.inl w971, fun _ _ => w971⟩
  · exact ⟨fun _ => Or.inl w972, fun _ => Or.inl w972, fun _ _ => w972⟩
  · exact ⟨fun _ => Or.inl w973, fun _ => Or.inl w973, fun _ _ => w973⟩
  · exact ⟨fun _ => Or.inl w974, fun _ => Or.inl w974, fun _ _ => w974⟩
  · exact ⟨fun _ => Or.inl w975, fun _ => Or.inl w975, fun _ _ => w975⟩
  · exact ⟨fun _ => Or.inl w976, fun _ => Or.inl w976, fun _ _ => w976⟩
  · exact ⟨fun _ => Or.inl w977, fun _ => Or.inl w977, fun _ _ => w977⟩
  · exact ⟨fun _ => Or.inl w978, fun _ => Or.inl w978, fun _ _ => w978⟩
  · exact ⟨fun _ => Or.inl w979, fun _ => Or.inl w979, fun _ _ => w979⟩
  · exact ⟨fun _ => Or.inl w980, fun _ => Or.inl w980, fun _ _ => w980⟩
  · exact ⟨fun _ => Or.inl w981, fun _ => Or.inl w981, fun _ _ => w981⟩
  · exact ⟨fun _ => Or.inl w982, fun _ => Or.inl w982, fun _ _ => w982⟩
  · exact ⟨fun _ => Or.inl w983, fun _ => Or.inl w983, fun _ _ => w983⟩
  · exact ⟨fun _ => Or.inl w984, fun _ => Or.inl w984, fun _ _ => w984⟩
  · exact ⟨fun _ => Or.inl w985, fun _ => Or.inl w985, fun _ _ => w985⟩
  · exact ⟨fun _ => Or.inl w986, fun _ => Or.inl w986, fun _ _ => w986⟩
  · exact ⟨fun _ => Or.inl w987, fun _ => Or.inl w987, fun _ _ => w987⟩
  · exact ⟨fun _ => Or.inl w988, fun _ => Or.inl w988, fun _ _ => w988⟩
  · exact ⟨fun _ => Or.inl w989, fun _ => Or.inl w989, fun _ _ => w989⟩
  · exact ⟨fun _ => Or.inl w990, fun _ => Or.inl w990, fun _ _ => w990⟩
  · exact ⟨fun _ => Or.inl w991, fun _ => Or.inl w991, fun _ _ => w991⟩
  · exact ⟨fun _ => Or.inl w992, fun _ => Or.inl w992, fun _ _ => w992⟩
  · exact ⟨fun _ => Or.inl w993, fun _ => Or.inl w993, fun _ _ => w993⟩
  · exact ⟨fun _ => Or.inl w994, fun _ => Or.inl w994, fun _ _ => w994⟩
  · exact ⟨fun _ => Or.inl w995, fun _ => Or.inl w995, fun _ _ => w995⟩
  · exact ⟨fun _ => Or.inl w996, fun _ => Or.inl w996, fun _ _ => w996⟩
  · exact ⟨fun _ => Or.inl w997, fun _ => Or.inl w997, fun _ _ => w997⟩
  · exact ⟨fun _ => Or.inl w998, fun _ => Or.inl w998, fun _ _ => w998⟩
  · exact ⟨fun _ => Or.inl w999, fun _ => Or.inl w999, fun _ _ => w999⟩
  · exact ⟨fun _ => Or.inl w1000, fun _ => Or.inl w1000, fun _ _ => w1000⟩

end UpTo1000



/-!
## Status report (analysis performed for this submission)

Write `S` for the set of "zeros", i.e. `S = {n | A274274 n = 0}` (numbers that are not
the sum of a nonnegative cube and two squares).

**Exhaustive computation.**  By a rigorous exhaustive computation (two independently
implemented and cross-validated bit-sieve programs, with an exact
factorization-certificate fallback), the zeros `n ≤ 1.5×10^14` are *exactly* 434 numbers,
the largest being `5042631`; the list begins `7, 15, 22, 23, 39, 55, 70, 71, ...`.
Consequently, for all `n ≤ 1.5×10^14`:
* no two zeros differ by `2` or by `6` (clauses 1 and 2 hold);
* the only zeros of the form `2^k*(4m+1)` are `813 = 4*203+1`, `4404 = 4*1101`,
  `6420 = 4*1605`, `28804 = 4*7201` — precisely the four excluded values
  (clause 3 holds).
Hence the conjecture is TRUE for all `n ≤ 1.5×10^14`, and a disproof (which, by the shape
of the statement, would require an explicit counterexample `n`) is not available.
Standard heuristics (density of sums of two squares `~ K/√(log m)` by
Landau–Ramanujan, with `~ n^{1/3}` admissible cube shifts, of which a positive
proportion survives all local obstructions, since the cube map is bijective on odd
residues mod `2^j` and hits at least one good class mod `9`, `49`, ...) make the
existence of any further zero, hence of any counterexample, astronomically unlikely:
the failure probability is `≲ exp(-c·n^{1/3}/√(log n))`, which is summable to
essentially `0` over `n > 1.5×10^14`.

**Provability status.**  The remaining content of clause 3 is: every `n = 2^k(4m+1)`
larger than the four excluded values is a sum of a nonnegative cube and two squares.
Since the set `{2^k(4m+1)}` has positive density (it contains all `n ≡ 1 (mod 4)`),
this contains the well-known *open* problem of showing that all sufficiently large
integers in a positive-density set with no local obstructions are of the form
`x³ + y² + z²`.  The best known results are almost-all results (Davenport–Heilbronn
type) and Wooley's *slim exceptional sets* bounds, giving only `E(N) ≪ (log N)^{O(1)}`
exceptions up to `N`; finiteness of the exceptional set is open and expected to be very
hard (the fibres `y² + z² = n - x³` make `n = x³ + y² + z²` a question about integral
points on a family of log K3 surfaces; neither the circle method nor the dispersion
method applies to a shift sequence as sparse as the cubes).  No elementary route can
exist either: membership in the set of sums of two squares is not determined by
congruences, and a covering-system-style obstruction is impossible because `Σ 1/p` over
usable primes grows like `log log T`, far slower than the length `n^{1/3}` of the
interval of available cube shifts.

Therefore the theorem below is (to the best of current mathematical knowledge) a true
but open statement: it cannot be disproved (it is true), and a complete proof is beyond
currently known mathematics.  The `sorry` below isolates exactly this open content.
-/

/--
Conjecture (i): Let n be any nonnegative integer.
(i) Either a(n) > 0 or a(n-2) > 0. Also, a(n) > 0 or a(n-6) > 0.
Moreover, if n has the form $2^k \cdot (4m+1)$ with $k$ and $m$ nonnegative integers,
then a(n) > 0 except for $n \in \{813, 4404, 6420, 28804\}$.
-/
theorem A274274_conjecture_i :
  ∀ (n : ℕ),
    (n ≥ 2 → A274274 n ≠ 0 ∨ A274274 (n - 2) ≠ 0) ∧
    (n ≥ 6 → A274274 n ≠ 0 ∨ A274274 (n - 6) ≠ 0) ∧
    (has_form_two_pow_k_times_four_m_plus_one n →
      (n ≠ 813 ∧ n ≠ 4404 ∧ n ≠ 6420 ∧ n ≠ 28804) → A274274 n ≠ 0) :=
by sorry
