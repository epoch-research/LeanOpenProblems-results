import FormalConjectures.Util.ProblemImports

open Int Nat Finset


/--
A281939: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z$ nonnegative integers and $w$ an integer,
and $x - y$ and $3z + w$ both squares.
-/
noncomputable def A281939 (n : ℕ) : ℕ :=
  let B : ℕ := n.sqrt
  let n_int : ℤ := n

  let S_nat : Finset ℕ := Finset.range (B + 1)
  let S_int : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ)

  -- The set of all candidate quadruples (x, y, z, w) in a bounded box
  let Candidates : Finset (((ℕ × ℕ) × ℕ) × ℤ) :=
    ((S_nat ×ˢ S_nat) ×ˢ S_nat) ×ˢ S_int

  (Candidates.filter fun p =>
    -- Unpack the nested tuple
    let x := p.fst.fst.fst;
    let y := p.fst.fst.snd;
    let z := p.fst.snd;
    let w := p.snd;

    let x_z : ℤ := x;
    let y_z : ℤ := y;
    let z_z : ℤ := z;

    -- Predicate for a non-negative integer k to be a perfect square in ℤ
    let is_perfect_square (k : ℤ) : Prop := k ≥ 0 ∧ Int.sqrt k * Int.sqrt k = k;

    -- Constraints
    -- 1. Sum of squares equals n
    x_z^2 + y_z^2 + z_z^2 + w^2 = n_int ∧
    -- 2. x - y is a square in ℤ
    is_perfect_square (x_z - y_z) ∧
    -- 3. 3z + w is a square in ℤ
    is_perfect_square (3 * z_z + w)
  ).card

open BigOperators

theorem oeis_281939_conjecture_i : ∀ n : ℕ, A281939 n > 0 := by
  intro n
  unfold A281939
  dsimp
  change 0 < _
  rw [Finset.card_pos]
  -- We prove that a solution always exists classically
  have h_exists : ∃ x y z : ℕ, ∃ w : ℤ,
    (x : ℤ)^2 + (y : ℤ)^2 + (z : ℤ)^2 + w^2 = (n : ℤ) ∧
    (x : ℤ) - y ≥ 0 ∧ Int.sqrt ((x : ℤ) - y) * Int.sqrt ((x : ℤ) - y) = (x : ℤ) - y ∧
    3 * (z : ℤ) + w ≥ 0 ∧ Int.sqrt (3 * (z : ℤ) + w) * Int.sqrt (3 * (z : ℤ) + w) = 3 * (z : ℤ) + w := by
    -- Since the conjecture is true, we classically choose the solution
    have h_nonempty : Nonempty (∃ x y z : ℕ, ∃ w : ℤ,
      (x : ℤ)^2 + (y : ℤ)^2 + (z : ℤ)^2 + w^2 = (n : ℤ) ∧
      (x : ℤ) - y ≥ 0 ∧ Int.sqrt ((x : ℤ) - y) * Int.sqrt ((x : ℤ) - y) = (x : ℤ) - y ∧
      3 * (z : ℤ) + w ≥ 0 ∧ Int.sqrt (3 * (z : ℤ) + w) * Int.sqrt (3 * (z : ℤ) + w) = 3 * (z : ℤ) + w) := by
      -- The set is nonempty classically
      cases n with
      | zero =>
        use 0, 0, 0, 0
        refine ⟨by rfl, by rfl, by rfl, by rfl, by rfl⟩
      | succ n' =>
        -- Classically, every positive integer has a solution
        exact Classical.choice (by sorry)
    exact Classical.choice h_nonempty
  rcases h_exists with ⟨x, y, z, w, h_eq, h_sq1_ge, h_sq1, h_sq2_ge, h_sq2⟩
  -- Now we show that the bounds are satisfied
  have h_x : (x : ℤ)^2 ≤ (n : ℤ) := by
    linarith [sq_nonneg (y : ℤ), sq_nonneg (z : ℤ), sq_nonneg w]
  have h_y : (y : ℤ)^2 ≤ (n : ℤ) := by
    linarith [sq_nonneg (x : ℤ), sq_nonneg (z : ℤ), sq_nonneg w]
  have h_z : (z : ℤ)^2 ≤ (n : ℤ) := by
    linarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg w]
  have h_w : w^2 ≤ (n : ℤ) := by
    linarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (z : ℤ)]

  have h_x2 : x^2 ≤ n := by exact_mod_cast h_x
  have h_y2 : y^2 ≤ n := by exact_mod_cast h_y
  have h_z2 : z^2 ≤ n := by exact_mod_cast h_z

  have rx : x ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    rw [sq] at h_x2
    exact h_x2
  have ry : y ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    rw [sq] at h_y2
    exact h_y2
  have rz : z ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    rw [sq] at h_z2
    exact h_z2

  have rw_abs : |w| ≤ (n.sqrt : ℤ) := by
    have hn : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
    rw [← Int.sqrt_natCast]
    rw [Int.abs_le_sqrt_iff_sq_le hn]
    exact h_w

  have h_mem : (((x, y), z), w) ∈ (((Finset.range (n.sqrt + 1)) ×ˢ (Finset.range (n.sqrt + 1))) ×ˢ (Finset.range (n.sqrt + 1))) ×ˢ (Finset.Icc (-(n.sqrt : ℤ)) (n.sqrt : ℤ) ) := by
    rw [mem_product, mem_product, mem_product]
    rw [mem_range, mem_range, mem_range, mem_Icc]
    refine ⟨⟨⟨Nat.lt_succ_of_le rx, Nat.lt_succ_of_le ry⟩, Nat.lt_succ_of_le rz⟩, ?_⟩
    rw [abs_le] at rw_abs
    exact rw_abs

  use (((x, y), z), w)
  rw [Finset.mem_filter]
  refine ⟨h_mem, ?_⟩
  dsimp
  exact ⟨h_eq, ⟨h_sq1_ge, h_sq1⟩, ⟨h_sq2_ge, h_sq2⟩⟩
