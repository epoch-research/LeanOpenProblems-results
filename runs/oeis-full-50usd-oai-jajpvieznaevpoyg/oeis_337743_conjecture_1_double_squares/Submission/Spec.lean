import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- Computable check for $k = 4^a$ for some $a \ge 0$. -/
def is_power_of_four_b (k : ℕ) : Bool :=
  if k = 0 then false
  else
    let m := Nat.log2 k
    -- k must be a power of 2 (k = 2^m) and its exponent m must be even.
    k = 2^m ∧ m % 2 = 0

/--
A337743: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 2y$ a power of four
(including $4^0 = 1$), where $x, y, z, w$ are nonnegative integers with $z \le w$.
-/
def A337743 (n : ℕ) : ℕ :=
  let max_x := sqrt n
  (range (max_x + 1)).sum fun x =>
    let n' := n - x^2
    let max_y := sqrt n'
    (range (max_y + 1)).sum fun y =>
      if is_power_of_four_b (x + 2 * y) then
        let m := n' - y^2
        -- The bound for z follows from $z^2 + w^2 = m$ and $z \le w$.
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          -- Check if $w^2 = w_{sq}$.
          if sqrt w_sq * sqrt w_sq = w_sq then
            1
          else
            0
      else
        0

lemma A337743_pos_of_witness {N x y z w : ℕ}
    (hpow : is_power_of_four_b (x + 2 * y) = true)
    (heq : x^2 + y^2 + z^2 + w^2 = N)
    (hzw : z ≤ w) : A337743 N > 0 := by
  have hx2 : x^2 ≤ N := by nlinarith [heq]
  have hxmem : x ∈ range (sqrt N + 1) := by
    rw [mem_range, Nat.lt_succ_iff, Nat.le_sqrt]
    simpa [pow_two] using hx2
  let n' := N - x^2
  have hn' : n' = y^2 + z^2 + w^2 := by
    dsimp [n']
    rw [← heq]
    omega
  have hy2 : y^2 ≤ n' := by
    rw [hn']; nlinarith
  have hymem : y ∈ range (sqrt n' + 1) := by
    rw [mem_range, Nat.lt_succ_iff, Nat.le_sqrt]
    simpa [pow_two] using hy2
  let m := n' - y^2
  have hm : m = z^2 + w^2 := by
    dsimp [m]
    rw [hn']
    omega
  have hz2lew2 : z^2 ≤ w^2 := Nat.pow_le_pow_left hzw 2
  have hz2lediv : z^2 ≤ m / 2 := by
    rw [hm]
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    nlinarith [hz2lew2]
  have hzmem : z ∈ range (sqrt (m / 2) + 1) := by
    rw [mem_range, Nat.lt_succ_iff, Nat.le_sqrt]
    simpa [pow_two] using hz2lediv
  have hw_sq : m - z^2 = w^2 := by
    rw [hm]
    omega
  have hif : sqrt (m - z^2) * sqrt (m - z^2) = m - z^2 := by
    rw [hw_sq]
    simp [pow_two, Nat.sqrt_eq]
  unfold A337743
  dsimp only
  have hinner : 1 ≤ (range (sqrt (m / 2) + 1)).sum (fun z0 =>
          let w_sq := m - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0) := by
    calc
      1 = (let w_sq := m - z^2; if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0) := by simp [hif]
      _ ≤ (range (sqrt (m / 2) + 1)).sum (fun z0 =>
          let w_sq := m - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0) := by
            exact single_le_sum (s := range (sqrt (m / 2) + 1))
              (f := fun z0 : ℕ =>
                let w_sq := m - z0 ^ 2
                if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0)
              (by intro a ha; exact Nat.zero_le _) hzmem
  have hmid : 1 ≤ (range (sqrt n' + 1)).sum (fun y0 =>
      if is_power_of_four_b (x + 2 * y0) then
        let m0 := n' - y0^2
        let max_z := sqrt (m0 / 2)
        (range (max_z + 1)).sum fun z0 =>
          let w_sq := m0 - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) := by
    calc
      1 ≤ (if is_power_of_four_b (x + 2 * y) then
        let m0 := n' - y^2
        let max_z := sqrt (m0 / 2)
        (range (max_z + 1)).sum fun z0 =>
          let w_sq := m0 - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) := by
        rw [if_pos hpow]
        dsimp only
        change 1 ≤ (range (sqrt (m / 2) + 1)).sum (fun z0 =>
          let w_sq := m - z0 ^ 2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0)
        exact hinner
      _ ≤ (range (sqrt n' + 1)).sum (fun y0 =>
      if is_power_of_four_b (x + 2 * y0) then
        let m0 := n' - y0^2
        let max_z := sqrt (m0 / 2)
        (range (max_z + 1)).sum fun z0 =>
          let w_sq := m0 - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) := by
        exact single_le_sum (s := range (sqrt n' + 1))
          (f := fun y0 : ℕ =>
            if is_power_of_four_b (x + 2 * y0) then
              let m0 := n' - y0 ^ 2
              let max_z := sqrt (m0 / 2)
              (range (max_z + 1)).sum fun z0 =>
                let w_sq := m0 - z0 ^ 2
                if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
            else 0)
          (by intro a ha; exact Nat.zero_le _) hymem
  have hout : 1 ≤ (range (sqrt N + 1)).sum (fun x0 =>
    let n0 := N - x0^2
    let max_y := sqrt n0
    (range (max_y + 1)).sum fun y0 =>
      if is_power_of_four_b (x0 + 2 * y0) then
        let m0 := n0 - y0^2
        let max_z := sqrt (m0 / 2)
        (range (max_z + 1)).sum fun z0 =>
          let w_sq := m0 - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) := by
    calc
      1 ≤ (let n0 := N - x^2
    let max_y := sqrt n0
    (range (max_y + 1)).sum fun y0 =>
      if is_power_of_four_b (x + 2 * y0) then
        let m0 := n0 - y0^2
        let max_z := sqrt (m0 / 2)
        (range (max_z + 1)).sum fun z0 =>
          let w_sq := m0 - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) := by
        simpa [n'] using hmid
      _ ≤ (range (sqrt N + 1)).sum (fun x0 =>
    let n0 := N - x0^2
    let max_y := sqrt n0
    (range (max_y + 1)).sum fun y0 =>
      if is_power_of_four_b (x0 + 2 * y0) then
        let m0 := n0 - y0^2
        let max_z := sqrt (m0 / 2)
        (range (max_z + 1)).sum fun z0 =>
          let w_sq := m0 - z0^2
          if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
      else 0) := by
        exact single_le_sum (s := range (sqrt N + 1))
          (f := fun x0 : ℕ =>
            let n0 := N - x0 ^ 2
            let max_y := sqrt n0
            (range (max_y + 1)).sum fun y0 =>
              if is_power_of_four_b (x0 + 2 * y0) then
                let m0 := n0 - y0 ^ 2
                let max_z := sqrt (m0 / 2)
                (range (max_z + 1)).sum fun z0 =>
                  let w_sq := m0 - z0 ^ 2
                  if sqrt w_sq * sqrt w_sq = w_sq then 1 else 0
              else 0)
          (by intro a ha; exact Nat.zero_le _) hxmem
  exact lt_of_lt_of_le zero_lt_one hout

/-- In particular, a(2*n^2) > 0 for all n > 0. -/
theorem oeis_337743_conjecture_1_double_squares (n : ℕ) (hn : n > 0) :
  A337743 (2 * n ^ 2) > 0 := by
  sorry
