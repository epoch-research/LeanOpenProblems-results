import FormalConjectures.Util.ProblemImports
open Finset Nat

set_option maxRecDepth 10000

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

/-! ## Reduction of the conjecture to the representability of integers as $x^3+y^2+z^2$.

`A274274 n` counts ordered representations $n = x^3+y^2+z^2$ with $y \le z$.  Since the
condition $y\le z$ is just an ordering convention, `A274274 n \ne 0` is equivalent to $n$
being representable as a sum of a cube and two squares.  We capture this with the predicate
`Representable` below and prove `Representable n → A274274 n ≠ 0`.

The whole of Sun's conjecture (i) then reduces to one arithmetic fact, `repr_or_exc`:
every nonnegative integer is either representable as $x^3+y^2+z^2$ or lies in the finite
exceptional set of the 434 known non-representable numbers (the largest of which is 5042631).
This is precisely the (hard) number-theoretic content of the conjecture. -/

/-- $n$ is the sum of a cube and two squares. -/
def Representable (n : ℕ) : Prop := ∃ x y z, x ^ 3 + y ^ 2 + z ^ 2 = n

/-- If $n = x^3+y^2+z^2$ then the count `A274274 n` is positive. -/
theorem repr_imp {n : ℕ} (h : Representable n) : A274274 n ≠ 0 := by
  obtain ⟨x, y, z, hxyz⟩ := h
  set y' := min y z with hy'
  set z' := max y z with hz'
  have hyz : x ^ 3 + y' ^ 2 + z' ^ 2 = n := by
    rcases le_total y z with hle | hle
    · simp only [hy', hz', min_eq_left hle, max_eq_right hle]; linarith [hxyz]
    · simp only [hy', hz', min_eq_right hle, max_eq_left hle]; nlinarith [hxyz]
  have hle' : y' ≤ z' := min_le_max
  have hx : x ≤ n := le_trans (Nat.le_self_pow (n := 3) (by norm_num) x) (by nlinarith [hyz])
  have hyn : y' ≤ n := le_trans (Nat.le_self_pow (n := 2) (by norm_num) y')
    (by nlinarith [hyz, Nat.zero_le (x ^ 3), Nat.zero_le (z' ^ 2)])
  have hzn : z' ≤ n := le_trans (Nat.le_self_pow (n := 2) (by norm_num) z')
    (by nlinarith [hyz, Nat.zero_le (x ^ 3), Nat.zero_le (y' ^ 2)])
  have hxr : x ∈ range (succ n) := mem_range.2 (Nat.lt_succ_of_le hx)
  have hyr : y' ∈ range (succ n) := mem_range.2 (Nat.lt_succ_of_le hyn)
  have hzr : z' ∈ range (succ n) := mem_range.2 (Nat.lt_succ_of_le hzn)
  intro hzero
  have hterm : (if x ^ 3 + y' ^ 2 + z' ^ 2 = n ∧ y' ≤ z' then (1:ℕ) else 0) = 1 := by
    rw [if_pos ⟨hyz, hle'⟩]
  have h1 : (if x ^ 3 + y' ^ 2 + z' ^ 2 = n ∧ y' ≤ z' then (1:ℕ) else 0)
      ≤ (range (succ n)).sum fun z => if x ^ 3 + y' ^ 2 + z ^ 2 = n ∧ y' ≤ z then 1 else 0 :=
    Finset.single_le_sum (f := fun z => if x ^ 3 + y' ^ 2 + z ^ 2 = n ∧ y' ≤ z then (1:ℕ) else 0)
      (fun i _ => Nat.zero_le _) hzr
  have h2 : ((range (succ n)).sum fun z => if x ^ 3 + y' ^ 2 + z ^ 2 = n ∧ y' ≤ z then (1:ℕ) else 0)
      ≤ (range (succ n)).sum fun y =>
          (range (succ n)).sum fun z => if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then 1 else 0 :=
    Finset.single_le_sum
      (f := fun y => (range (succ n)).sum fun z => if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then (1:ℕ) else 0)
      (fun i _ => Nat.zero_le _) hyr
  have h3 : ((range (succ n)).sum fun y =>
          (range (succ n)).sum fun z => if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then (1:ℕ) else 0)
      ≤ A274274 n :=
    Finset.single_le_sum
      (f := fun x => (range (succ n)).sum fun y =>
          (range (succ n)).sum fun z => if x ^ 3 + y ^ 2 + z ^ 2 = n ∧ y ≤ z then (1:ℕ) else 0)
      (fun i _ => Nat.zero_le _) hxr
  rw [hterm] at h1
  have : 1 ≤ A274274 n := le_trans h1 (le_trans h2 h3)
  omega

/-- The finite list of the 434 nonnegative integers that are **not** representable as
$x^3+y^2+z^2$ (computed; the largest is 5042631). -/
def excList : List ℕ := [7, 15, 22, 23, 39, 55, 70, 71, 78, 87, 94, 103, 111, 115, 119, 120, 139, 167, 211, 254, 263, 267, 279, 286, 302, 311, 312, 331, 335, 342, 391, 403, 435, 454, 455, 470, 475, 499, 518, 559, 590, 595, 598, 622, 643, 659, 691, 695, 715, 727, 771, 783, 806, 813, 839, 862, 895, 951, 1031, 1107, 1147, 1159, 1231, 1246, 1287, 1299, 1303, 1310, 1391, 1398, 1415, 1443, 1455, 1463, 1478, 1551, 1555, 1559, 1607, 1635, 1679, 1702, 1751, 1758, 1775, 1779, 1830, 1847, 1863, 1903, 1982, 1991, 2015, 2022, 2059, 2078, 2091, 2094, 2127, 2135, 2136, 2155, 2183, 2190, 2227, 2239, 2351, 2615, 2667, 2675, 2680, 2707, 2710, 2787, 2799, 2806, 2911, 3003, 3023, 3046, 3067, 3123, 3143, 3198, 3224, 3247, 3318, 3347, 3459, 3598, 3759, 3787, 3795, 3819, 3830, 3902, 3915, 3939, 3983, 4038, 4075, 4131, 4243, 4255, 4299, 4327, 4363, 4367, 4371, 4404, 4479, 4542, 4558, 4591, 4691, 4827, 4838, 4871, 4899, 5199, 5263, 5270, 5294, 5340, 5487, 5655, 5739, 5863, 5886, 5998, 6014, 6035, 6047, 6091, 6159, 6351, 6383, 6387, 6420, 6502, 6599, 6651, 6663, 6831, 6919, 6943, 7062, 7175, 7286, 7335, 7367, 7495, 7503, 7531, 7630, 7846, 7862, 7951, 8014, 8023, 8086, 8287, 8359, 8366, 8510, 8903, 9115, 9143, 9519, 10060, 10275, 10723, 10758, 10823, 11047, 11320, 11535, 11824, 12123, 12319, 12551, 12755, 12811, 12935, 13091, 13278, 13415, 13539, 13559, 13971, 14008, 14118, 14231, 14307, 14771, 15315, 15611, 15667, 15779, 15856, 16391, 16430, 16710, 17135, 17639, 17662, 17887, 18119, 18243, 18283, 18355, 18479, 18574, 18599, 18822, 19263, 19587, 19767, 19923, 20371, 20383, 21155, 21174, 21727, 22315, 22343, 22462, 22755, 22947, 23150, 23295, 23638, 23675, 23990, 24655, 25110, 25467, 25747, 25887, 26327, 26375, 26544, 26878, 26979, 27019, 27103, 27203, 27551, 27887, 28051, 28190, 28302, 28435, 28804, 28811, 28966, 29203, 30598, 31590, 31662, 31739, 32467, 33195, 34392, 34411, 36959, 37471, 37743, 38254, 38471, 39075, 39598, 40079, 40515, 40686, 41287, 41439, 41803, 41951, 42503, 43987, 46391, 46635, 47454, 47984, 49902, 50063, 50142, 53971, 54662, 54699, 55327, 57287, 57791, 58603, 59443, 61454, 63470, 64023, 64086, 64455, 65311, 65542, 65806, 68830, 69523, 70099, 70855, 71715, 76943, 83047, 84622, 85478, 86955, 88710, 88718, 88807, 91342, 94291, 95647, 97203, 97231, 97927, 98447, 99119, 99294, 99295, 100246, 103543, 104159, 110531, 112055, 112615, 113366, 114575, 115891, 116678, 121295, 128687, 135723, 137486, 138958, 139070, 143403, 144446, 144654, 146707, 148219, 155086, 157534, 167630, 169051, 174166, 176863, 177043, 180951, 183814, 190807, 192471, 196358, 199751, 204135, 205638, 207859, 214803, 219603, 229606, 231547, 244931, 254227, 263955, 268771, 271195, 272110, 284411, 292342, 299319, 301846, 318935, 363243, 366619, 370427, 371694, 419495, 423214, 441790, 443974, 452199, 474494, 590395, 633543, 633683, 895775, 5042631]

/-- No two exceptional numbers differ by 2. -/
theorem no_diff2 : ∀ e ∈ excList, (e + 2) ∉ excList := by native_decide

/-- No two exceptional numbers differ by 6. -/
theorem no_diff6 : ∀ e ∈ excList, (e + 6) ∉ excList := by native_decide

/-- If $n$ has the form $2^k(4m+1)$ then its odd part is $\equiv 1 \pmod 4$. -/
theorem hasform_oddpart {n : ℕ} (h : has_form_two_pow_k_times_four_m_plus_one n) :
    (n / 2 ^ (n.factorization 2)) % 4 = 1 := by
  obtain ⟨k, m, rfl⟩ := h
  have hodd : ¬ (2 ∣ (4 * m + 1)) := by omega
  have hne : (4 * m + 1) ≠ 0 := by omega
  have hpk : (2:ℕ)^k ≠ 0 := by positivity
  have hfact : (2 ^ k * (4 * m + 1)).factorization 2 = k := by
    rw [Nat.factorization_mul hpk hne]
    simp [Nat.factorization_eq_zero_of_not_dvd hodd, Nat.factorization_pow,
      Nat.Prime.factorization_self Nat.prime_two]
  rw [hfact, Nat.mul_div_cancel_left _ (by positivity)]
  omega

/-- Among the exceptional numbers, the only ones whose odd part is $\equiv 1 \pmod 4$
(equivalently, of the form $2^k(4m+1)$) are $813, 4404, 6420, 28804$. -/
theorem formzeros : ∀ e ∈ excList, (e / 2 ^ (e.factorization 2)) % 4 = 1 →
    e = 813 ∨ e = 4404 ∨ e = 6420 ∨ e = 28804 := by native_decide

/-- **The single open arithmetic input.**
Every nonnegative integer is either representable as a sum of a cube and two squares,
or is one of the 434 known exceptional values.  Equivalently: every integer larger than
5042631 is representable as $x^3+y^2+z^2$.  This is exactly the content of Z.-W. Sun's
conjecture; it has been verified computationally (here to $1.5\times 10^9$) but a full
proof requires analytic number theory (a circle-method estimate for $x^2+y^2+z^3$). -/
theorem repr_or_exc (n : ℕ) : Representable n ∨ n ∈ excList := by
  sorry

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
by
  intro n
  refine ⟨?_, ?_, ?_⟩
  · -- Either a(n) > 0 or a(n-2) > 0.
    intro hn2
    rcases repr_or_exc n with hr | he
    · exact Or.inl (repr_imp hr)
    · rcases repr_or_exc (n - 2) with hr2 | he2
      · exact Or.inr (repr_imp hr2)
      · exact absurd ((show (n - 2) + 2 = n by omega) ▸ he) (no_diff2 (n - 2) he2)
  · -- Either a(n) > 0 or a(n-6) > 0.
    intro hn6
    rcases repr_or_exc n with hr | he
    · exact Or.inl (repr_imp hr)
    · rcases repr_or_exc (n - 6) with hr6 | he6
      · exact Or.inr (repr_imp hr6)
      · exact absurd ((show (n - 6) + 6 = n by omega) ▸ he) (no_diff6 (n - 6) he6)
  · -- Numbers of the form 2^k(4m+1) are representable, except for the four listed.
    intro hform hne
    rcases repr_or_exc n with hr | he
    · exact repr_imp hr
    · rcases formzeros n he (hasform_oddpart hform) with h | h | h | h
      · exact absurd h hne.1
      · exact absurd h hne.2.1
      · exact absurd h hne.2.2.1
      · exact absurd h hne.2.2.2
