import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A347865: Number of ways to write $n$ as $w^2 + 2x^2 + y^4 + 3z^4$, where $w,x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  -- Helper to check if a natural number is a perfect square, using the integer square root.
  let is_perfect_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m

  -- Upper bounds derived from components $\le n$:
  -- w^2 <= n implies w <= sqrt(n). We use Nat.sqrt n + 1 for the range.
  let max_sq_term_root := Nat.sqrt n + 1
  -- y^4 <= n implies y <= n^(1/4) = sqrt(sqrt(n)).
  let max_quad_term_root := Nat.sqrt (Nat.sqrt n) + 1

  -- We iterate over the bounded ranges of $x, y, z$.
  Finset.sum (range max_quad_term_root) fun z =>
    Finset.sum (range max_quad_term_root) fun y =>
      Finset.sum (range max_sq_term_root) fun x =>
        let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4

        -- Check if $w^2 = n - rest$ is possible in $\mathbb{N}$.
        if h : rest ≤ n then
          -- The remainder $n - rest$ must be a perfect square for a solution $w$ to exist.
          if is_perfect_square (n - rest) then 1 else 0
        else
          0


lemma a_pos_of_repr {n w x y z : ℕ}
    (h : w^2 + 2*x^2 + y^4 + 3*z^4 = n) : 0 < a n := by
  unfold a
  let maxq := Nat.sqrt (Nat.sqrt n) + 1
  let maxs := Nat.sqrt n + 1
  let rest0 : ℕ := 2 * x^2 + y^4 + 3 * z^4
  have hx2 : x^2 ≤ n := by
    nlinarith [show 0 ≤ w^2 by positivity, show 0 ≤ y^4 by positivity,
      show 0 ≤ 3*z^4 by positivity, h]
  have hxmem : x ∈ Finset.range maxs := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.le_sqrt').mpr hx2)
  have hy4 : y^4 ≤ n := by
    nlinarith [show 0 ≤ w^2 by positivity, show 0 ≤ 2*x^2 by positivity,
      show 0 ≤ 3*z^4 by positivity, h]
  have hy2 : y^2 ≤ Nat.sqrt n := by
    apply (Nat.le_sqrt').mpr
    convert hy4 using 1
    ring
  have hymem : y ∈ Finset.range maxq := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.le_sqrt').mpr hy2)
  have hz4 : z^4 ≤ n := by
    nlinarith [show 0 ≤ w^2 by positivity, show 0 ≤ 2*x^2 by positivity,
      show 0 ≤ y^4 by positivity, h]
  have hz2 : z^2 ≤ Nat.sqrt n := by
    apply (Nat.le_sqrt').mpr
    convert hz4 using 1
    ring
  have hzmem : z ∈ Finset.range maxq := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((Nat.le_sqrt').mpr hz2)
  have hrest_le : rest0 ≤ n := by
    dsimp [rest0]
    nlinarith [show 0 ≤ w^2 by positivity, h]
  have hnsub : n - rest0 = w^2 := by
    dsimp [rest0]
    omega
  have hterm : (let rest : ℕ := 2 * x^2 + y^4 + 3 * z^4
        if hle : rest ≤ n then if (Nat.sqrt (n - rest)) ^ 2 = n - rest then 1 else 0 else 0) = 1 := by
    simp [hrest_le, hnsub, rest0, Nat.sqrt_eq']
  let inner : ℕ → ℕ := fun x' =>
        let rest : ℕ := 2 * x'^2 + y^4 + 3 * z^4
        if hle : rest ≤ n then if (Nat.sqrt (n - rest)) ^ 2 = n - rest then 1 else 0 else 0
  have hinner_le : 1 ≤ (Finset.range maxs).sum inner := by
    calc
      1 = inner x := by simpa [inner] using hterm.symm
      _ ≤ (Finset.range maxs).sum inner := by
        simpa using (Finset.single_le_sum (s := Finset.range maxs) (f := inner)
          (fun b hb => Nat.zero_le _) hxmem)
  let mid : ℕ → ℕ := fun y' =>
      (Finset.range maxs).sum (fun x' =>
        let rest : ℕ := 2 * x'^2 + y'^4 + 3 * z^4
        if hle : rest ≤ n then if (Nat.sqrt (n - rest)) ^ 2 = n - rest then 1 else 0 else 0)
  have hmid_at : mid y = (Finset.range maxs).sum inner := by rfl
  have hmid_le : 1 ≤ (Finset.range maxq).sum mid := by
    calc
      1 ≤ mid y := by simpa [hmid_at] using hinner_le
      _ ≤ (Finset.range maxq).sum mid := by
        simpa using (Finset.single_le_sum (s := Finset.range maxq) (f := mid)
          (fun b hb => Nat.zero_le _) hymem)
  let outer : ℕ → ℕ := fun z' =>
    (Finset.range maxq).sum (fun y' =>
      (Finset.range maxs).sum (fun x' =>
        let rest : ℕ := 2 * x'^2 + y'^4 + 3 * z'^4
        if hle : rest ≤ n then if (Nat.sqrt (n - rest)) ^ 2 = n - rest then 1 else 0 else 0))
  have houter_at : outer z = (Finset.range maxq).sum mid := by rfl
  have hout_le : 1 ≤ (Finset.range maxq).sum outer := by
    calc
      1 ≤ outer z := by simpa [houter_at] using hmid_le
      _ ≤ (Finset.range maxq).sum outer := by
        simpa using (Finset.single_le_sum (s := Finset.range maxq) (f := outer)
          (fun b hb => Nat.zero_le _) hzmem)
  simpa [maxq, maxs, outer] using hout_le

lemma repr_of_a_pos {n : ℕ} (ha : 0 < a n) :
    ∃ w x y z : ℕ, w^2 + 2*x^2 + y^4 + 3*z^4 = n := by
  unfold a at ha
  let maxs := Nat.sqrt n + 1
  let maxq := Nat.sqrt (Nat.sqrt n) + 1
  let outer : ℕ → ℕ := fun z =>
    ∑ y ∈ Finset.range maxq,
      ∑ x ∈ Finset.range maxs,
        (let rest : ℕ := 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4
        if h : rest ≤ n then if (Nat.sqrt (n - rest)) ^ 2 = n - rest then 1 else 0 else 0)
  have hsum : (∑ z ∈ Finset.range maxq, outer z) ≠ 0 := by
    exact Nat.ne_of_gt ha
  obtain ⟨z, hzmem, hzpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  dsimp [outer] at hzpos
  obtain ⟨y, hymem, hypos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hzpos
  obtain ⟨x, hxmem, hxpos⟩ := Finset.exists_ne_zero_of_sum_ne_zero hypos
  dsimp at hxpos
  by_cases hle : 2 * x ^ 2 + y ^ 4 + 3 * z ^ 4 ≤ n
  · simp [hle] at hxpos
    have hs : (Nat.sqrt (n - (2*x^2 + y^4 + 3*z^4)))^2 =
        n - (2*x^2 + y^4 + 3*z^4) := by
      by_contra hbad
      simp [hbad] at hxpos
    refine ⟨Nat.sqrt (n - (2*x^2 + y^4 + 3*z^4)), x, y, z, ?_⟩
    omega
  · simp [hle] at hxpos


set_option maxHeartbeats 0 in
lemma a744 : a 744 = 0 := by
  norm_num [a]
  intro i hi i_1 hi1 i_2 hi2 hle hs
  interval_cases i <;> interval_cases i_1 <;> interval_cases i_2 <;>
    (first | omega | norm_num at hle hs)



lemma y_succ_identity (w y z : ℕ) :
    w^2 + 2 * ((y + 1)^2)^2 + y^4 + 3*z^4 + 1 =
      w^2 + 2 * (y^2 + y + 1)^2 + (y+1)^4 + 3*z^4 := by
  ring


/--
Conjecture 1 from A347865: a(n) > 0 except for n = 744.
-/
theorem oeis_347865_conjecture_0 (n : ℕ) : (a n > 0) ↔ (n ≠ 744) := by
  sorry
