import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352628: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 2d^4 + 3c^2d^2$,
where $a,b,c,d$ are nonnegative integers.
-/
def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)

  -- The number of ways is the sum of 1 for each tuple that satisfies the equation.
  -- Using nested sums avoids complex tuple unpacking and Finset product issues.
  S.sum fun a =>
    S.sum fun b =>
      S.sum fun c =>
        S.sum fun d =>
          let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
          if E = n then 1 else 0

/-- The algebraic identity behind the conjecture:
`(c^2+d^2)(c^2+2d^2) = c^4 + 2 d^4 + 3 c^2 d^2`. -/
theorem A352628_form_eq (c d : ℕ) :
    (c^2 + d^2) * (c^2 + 2*d^2) = c^4 + 2*d^4 + 3*c^2*d^2 := by ring

/-- If there is a witness `(a, b, c, d)` with all coordinates `≤ n` satisfying the
representation equation, then the counting function `A352628 n` is positive. -/
theorem A352628_pos_of_witness (n : ℕ) (a b c d : ℕ)
    (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n) (hd : d ≤ n)
    (he : a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n) : A352628 n > 0 := by
  unfold A352628
  simp only
  set S := range (n+1) with hS
  have hmem : ∀ x : ℕ, x ≤ n → x ∈ S := by
    intro x hx; rw [hS]; simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hx
  rw [gt_iff_lt, Nat.lt_iff_add_one_le, zero_add]
  have hd0 : (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0) d = 1 := by
    simp [he]
  calc (1:ℕ)
      = (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0) d := hd0.symm
    _ ≤ S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0) :=
        Finset.single_le_sum
          (f := fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0)
          (fun i _ => Nat.zero_le _) (hmem d hd)
    _ ≤ S.sum (fun c => S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0)) :=
        Finset.single_le_sum
          (f := fun c => S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0))
          (fun i _ => Nat.zero_le _) (hmem c hc)
    _ ≤ S.sum (fun b => S.sum (fun c => S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0))) :=
        Finset.single_le_sum
          (f := fun b => S.sum (fun c => S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0)))
          (fun i _ => Nat.zero_le _) (hmem b hb)
    _ ≤ S.sum (fun a => S.sum (fun b => S.sum (fun c => S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0)))) :=
        Finset.single_le_sum
          (f := fun a => S.sum (fun b => S.sum (fun c => S.sum (fun d => if a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n then (1:ℕ) else 0))))
          (fun i _ => Nat.zero_le _) (hmem a ha)

/-- Any solution of the representation equation automatically has all coordinates
bounded by `n`, so the restriction to `range (n+1)` in `A352628` is not a real
constraint. -/
theorem bound_of_eq (n a b c d : ℕ)
    (he : a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n) :
    a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n := by
  have hpa : a ≤ a^2 := Nat.le_self_pow (by norm_num) a
  have hpb : b ≤ b^2 := Nat.le_self_pow (by norm_num) b
  have hpc : c ≤ c^4 := Nat.le_self_pow (by norm_num) c
  have hpd : d ≤ d^4 := Nat.le_self_pow (by norm_num) d
  have ha2 : a^2 ≤ n := by rw [← he]; omega
  have hb2 : 2*b^2 ≤ n := by rw [← he]; omega
  have hc4 : c^4 ≤ n := by rw [← he]; omega
  have hd4 : 2*d^4 ≤ n := by rw [← he]; omega
  exact ⟨le_trans hpa ha2, le_trans hpb (by omega), le_trans hpc hc4, le_trans hpd (by omega)⟩

/-- The arithmetic heart of the conjecture: every nonnegative integer `n` admits a
representation `n = a^2 + 2 b^2 + c^4 + 2 d^4 + 3 c^2 d^2`.  Equivalently, writing
`R = {x^2 + 2 y^2}` (numbers represented by the binary form of discriminant `-8`) and
`V = {(c^2 + d^2)(c^2 + 2 d^2)}`, this says `R + V = ℕ`. -/
theorem A352628_exists (n : ℕ) :
    ∃ a b c d : ℕ, a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = n := by
  sorry

/-- A `16`-fold self-similarity of the representation: since `16 R ⊆ R` (the binary form
`x^2+2y^2` is closed under multiplication by squares) and `16 V ⊆ V` (the quartic form is
homogeneous of degree `4`, so `Q(2c,2d) = 16 Q(c,d)`), representability of `m` gives
representability of `16 m` via the witness `(4a, 4b, 2c, 2d)`.  Consequently, by strong
induction the open kernel `A352628_exists` is equivalent to its restriction to
fourth-power-free integers. -/
theorem A352628_exists_descent16 (m : ℕ) (h : ∃ a b c d : ℕ,
    a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = m) :
    ∃ a b c d : ℕ, a^2 + 2*b^2 + c^4 + 2*d^4 + 3*c^2*d^2 = 16*m := by
  obtain ⟨a, b, c, d, he⟩ := h
  refine ⟨4*a, 4*b, 2*c, 2*d, ?_⟩
  ring_nf
  ring_nf at he
  nlinarith [he]

/--
Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as $a^2 + 2b^2 + (c^2+d^2)(c^2+2d^2)$ with a,b,c,d integers.
-/
theorem oeis_352628_conjecture_0 (n : ℕ) : A352628 n > 0 := by
  obtain ⟨a, b, c, d, he⟩ := A352628_exists n
  obtain ⟨ha, hb, hc, hd⟩ := bound_of_eq n a b c d he
  exact A352628_pos_of_witness n a b c d ha hb hc hd he
