import FormalConjectures.Util.ProblemImports

open Int Finset

/-- The quadratic form $x(5x+1)$. -/
def Q1 (x : ℤ) : ℤ := x * (5 * x + 1)

/-- The quadratic form $t(5t+1)/2$, which is an integer for all $t \in \mathbb{Z}$. -/
def Q2 (t : ℤ) : ℤ := (t * (5 * t + 1)) / 2

/--
A377224: Number of ways to write $n$ as $x(5x+1) + y(5y+1)/2 + z(5z+1)/2$,
where $x,y,z$ are integers with $y(5y+1) \le z(5z+1)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let N : ℤ := n
  -- A conservative absolute bound for the variables is $n+1$.
  let B : ℤ := n + 1

  let Range : Finset ℤ := Icc (-B) B

  -- The search space is the Cartesian product of three bounded integer ranges.
  -- The type is (ℤ × ℤ) × ℤ due to nested product.
  let triples : Finset ((ℤ × ℤ) × ℤ) := (Range.product Range).product Range

  triples.filter (fun p : (ℤ × ℤ) × ℤ =>
    let x := p.1.1
    let y := p.1.2
    let z := p.2

    let y_term := Q2 y
    let z_term := Q2 z

    -- Equation: $n = Q_1(x) + Q_2(y) + Q_2(z)$
    -- Constraint: $Q_2(y) \le Q_2(z)$ (equivalent to $y(5y+1) \le z(5z+1)$)
    N = Q1 x + y_term + z_term ∧ y_term ≤ z_term
  )
  |>.card

/-!
## Reduction of the conjecture to a single arithmetic lemma

The whole conjecture is reduced below to the lemma

  `key : ∀ n, 80 ≤ n → 2 ≤ a n`

(used in `oeis_A377224_conjecture1`).  Everything else — the nonnegativity of the
forms, the range-reduction making `a n` decidable, the 80 finite verifications,
and the assembly of the two iff's — is proved unconditionally and uses only the
allowed axioms.

`key` itself is the genuine mathematical content of A377224.  Setting
`u = 10x+1, v = 10y+1, w = 10z+1` turns the equation into
`2u² + v² + w² = 40n+4` with `u,v,w ≡ 1 (mod 10)`, i.e. `a n` is a Fourier
coefficient of the weight `3/2` modular form `f(q²)·f(q)²` with
`f(q) = ∑_{t∈ℤ} q^{t(5t+1)/2}`.  The underlying ternary form `2x²+y²+z²` is
regular, but the congruence `≡ 1 (mod 10)` introduces a nonzero cusp form (e.g.
`a 58 = 1` while the relevant class number is `h(-2324) = 28`, and for primes
`p = 10n+1` the ratio `a n / √p` fluctuates like `p^{-1/4}`).  Proving `key`
therefore requires effective lower bounds on the Eisenstein part together with
effective (Duke/Iwaniec-type) upper bounds on half-integral weight cusp form
coefficients, which are not available in current Mathlib.  This is left as the
single `sorry` below.
-/

-- nonnegativity of the underlying integer products
lemma prod_nonneg (t : ℤ) : 0 ≤ t * (5 * t + 1) := by
  rcases le_total 0 t with h | h
  · nlinarith
  · rcases eq_or_lt_of_le h with rfl | h2
    · simp
    · have ht : t ≤ -1 := by omega
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -t) (by linarith : (0:ℤ) ≤ -(5*t+1))]

lemma Q1_nonneg (x : ℤ) : 0 ≤ Q1 x := prod_nonneg x

lemma Q2_nonneg (t : ℤ) : 0 ≤ Q2 t := by
  unfold Q2
  exact Int.ediv_nonneg (prod_nonneg t) (by norm_num)

-- computable fixed-range mirror of `a`, valid for `n ≤ 79`
def a' (n : ℕ) : ℕ :=
  (((Icc (-5:ℤ) 5).product (Icc (-5) 5)).product (Icc (-5) 5)).filter
    (fun p : (ℤ × ℤ) × ℤ =>
      (n:ℤ) = Q1 p.1.1 + Q2 p.1.2 + Q2 p.2 ∧ Q2 p.1.2 ≤ Q2 p.2)
  |>.card

-- coordinate bound for satisfying triples when `n ≤ 79`: all coords lie in `[-5,5]`
lemma coord_bound (n : ℕ) (hn : n ≤ 79) (x y z : ℤ)
    (heq : (n:ℤ) = Q1 x + Q2 y + Q2 z) :
    x ∈ Icc (-5:ℤ) 5 ∧ y ∈ Icc (-5:ℤ) 5 ∧ z ∈ Icc (-5:ℤ) 5 := by
  have hn79 : (n:ℤ) ≤ 79 := by exact_mod_cast hn
  have hQ1 : 0 ≤ Q1 x := Q1_nonneg x
  have hQ2y : 0 ≤ Q2 y := Q2_nonneg y
  have hQ2z : 0 ≤ Q2 z := Q2_nonneg z
  have hx : Q1 x ≤ 79 := by linarith
  have hy : Q2 y ≤ 79 := by linarith
  have hz : Q2 z ≤ 79 := by linarith
  have hyp : y * (5 * y + 1) ≤ 159 := by
    have : (y * (5 * y + 1)) / 2 ≤ 79 := hy
    omega
  have hzp : z * (5 * z + 1) ≤ 159 := by
    have : (z * (5 * z + 1)) / 2 ≤ 79 := hz
    omega
  have hxp : x * (5 * x + 1) ≤ 79 := hx
  simp only [Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg z]
  · nlinarith [sq_nonneg z]

-- coordinate bound into the `[-(n+1), n+1]` search range, valid for all `n`
lemma coord_boundB (n : ℕ) (x y z : ℤ)
    (heq : (n:ℤ) = Q1 x + Q2 y + Q2 z) :
    x ∈ Icc (-((n:ℤ)+1)) ((n:ℤ)+1) ∧ y ∈ Icc (-((n:ℤ)+1)) ((n:ℤ)+1)
      ∧ z ∈ Icc (-((n:ℤ)+1)) ((n:ℤ)+1) := by
  have hn0 : 0 ≤ (n:ℤ) := Int.natCast_nonneg n
  have hQ1 : 0 ≤ Q1 x := Q1_nonneg x
  have hQ2y : 0 ≤ Q2 y := Q2_nonneg y
  have hQ2z : 0 ≤ Q2 z := Q2_nonneg z
  have hxa : Q1 x ≤ (n:ℤ) := by linarith
  have hya : Q2 y ≤ (n:ℤ) := by linarith
  have hza : Q2 z ≤ (n:ℤ) := by linarith
  have hxp : x * (5 * x + 1) ≤ (n:ℤ) := hxa
  have hyp : y * (5 * y + 1) ≤ 2 * (n:ℤ) + 1 := by
    have h2 : (y * (5 * y + 1)) / 2 ≤ (n:ℤ) := hya
    omega
  have hzp : z * (5 * z + 1) ≤ 2 * (n:ℤ) + 1 := by
    have h2 : (z * (5 * z + 1)) / 2 ≤ (n:ℤ) := hza
    omega
  simp only [Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg z]
  · nlinarith [sq_nonneg z]

lemma filter_eq_of_mems {α} [DecidableEq α] (S₁ S₂ : Finset α) (P : α → Prop) [DecidablePred P]
    (h₁ : ∀ x, P x → x ∈ S₁) (h₂ : ∀ x, P x → x ∈ S₂) :
    S₁.filter P = S₂.filter P := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, hP⟩; exact ⟨h₂ x hP, hP⟩
  · rintro ⟨_, hP⟩; exact ⟨h₁ x hP, hP⟩

set_option maxRecDepth 8000 in
lemma a_eq_a' (n : ℕ) (hn : n ≤ 79) : a n = a' n := by
  unfold a a'
  simp only
  congr 1
  apply filter_eq_of_mems
  · rintro p ⟨heq, _⟩
    obtain ⟨hx, hy, hz⟩ := coord_boundB n p.1.1 p.1.2 p.2 heq
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩
  · rintro p ⟨heq, _⟩
    obtain ⟨hx, hy, hz⟩ := coord_bound n hn p.1.1 p.1.2 p.2 heq
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩

-- A second computable mirror, valid for `n ≤ 313`, using the range `[-11,11]`.
def a'' (n : ℕ) : ℕ :=
  (((Icc (-11:ℤ) 11).product (Icc (-11) 11)).product (Icc (-11) 11)).filter
    (fun p : (ℤ × ℤ) × ℤ =>
      (n:ℤ) = Q1 p.1.1 + Q2 p.1.2 + Q2 p.2 ∧ Q2 p.1.2 ≤ Q2 p.2)
  |>.card

lemma coord_bound'' (n : ℕ) (hn : n ≤ 313) (x y z : ℤ)
    (heq : (n:ℤ) = Q1 x + Q2 y + Q2 z) :
    x ∈ Icc (-11:ℤ) 11 ∧ y ∈ Icc (-11:ℤ) 11 ∧ z ∈ Icc (-11:ℤ) 11 := by
  have hn313 : (n:ℤ) ≤ 313 := by exact_mod_cast hn
  have hQ1 : 0 ≤ Q1 x := Q1_nonneg x
  have hQ2y : 0 ≤ Q2 y := Q2_nonneg y
  have hQ2z : 0 ≤ Q2 z := Q2_nonneg z
  have hx : Q1 x ≤ 313 := by linarith
  have hy : Q2 y ≤ 313 := by linarith
  have hz : Q2 z ≤ 313 := by linarith
  have hyp : y * (5 * y + 1) ≤ 627 := by
    have : (y * (5 * y + 1)) / 2 ≤ 313 := hy
    omega
  have hzp : z * (5 * z + 1) ≤ 627 := by
    have : (z * (5 * z + 1)) / 2 ≤ 313 := hz
    omega
  have hxp : x * (5 * x + 1) ≤ 313 := hx
  simp only [Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg y]
  · nlinarith [sq_nonneg z]
  · nlinarith [sq_nonneg z]

set_option maxRecDepth 8000 in
lemma a_eq_a'' (n : ℕ) (hn : n ≤ 313) : a n = a'' n := by
  unfold a a''
  simp only
  congr 1
  apply filter_eq_of_mems
  · rintro p ⟨heq, _⟩
    obtain ⟨hx, hy, hz⟩ := coord_boundB n p.1.1 p.1.2 p.2 heq
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩
  · rintro p ⟨heq, _⟩
    obtain ⟨hx, hy, hz⟩ := coord_bound'' n hn p.1.1 p.1.2 p.2 heq
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩

/- Memory-light witness verification of the finite window `80 ≤ n ≤ 313`:
   for each such `n` two explicit solution triples (with coordinates in `[-11,11]`)
   are exhibited, giving `2 ≤ a'' n` via `Finset.one_lt_card_iff`.  This replaces
   the memory-heavy full `decide` (which exceeds the 10 GiB per-process limit). -/
set_option maxRecDepth 100000

theorem memwit (n : ℕ) (x y z : ℤ)
    (hx : x ∈ Icc (-11:ℤ) 11) (hy : y ∈ Icc (-11:ℤ) 11) (hz : z ∈ Icc (-11:ℤ) 11)
    (hP : (n:ℤ) = Q1 x + Q2 y + Q2 z ∧ Q2 y ≤ Q2 z) :
    (((x,y),z) : (ℤ × ℤ) × ℤ) ∈
      (((Icc (-11:ℤ) 11).product (Icc (-11) 11)).product (Icc (-11) 11)).filter
        (fun p : (ℤ × ℤ) × ℤ =>
          (n:ℤ) = Q1 p.1.1 + Q2 p.1.2 + Q2 p.2 ∧ Q2 p.1.2 ≤ Q2 p.2) :=
  Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hz⟩, hP⟩

lemma keyfin_80 : 2 ≤ a'' 80 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),(-1)), (((-3),0),(-4)),
    memwit 80 (-4) (-1) (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 80 (-3) 0 (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_81 : 2 ≤ a'' 81 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),1), (((-2),(-3)),4),
    memwit 81 (-4) (-1) 1 (by decide) (by decide) (by decide) (by decide),
    memwit 81 (-2) (-3) 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_82 : 2 ≤ a'' 82 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),1), (((-3),(-1)),(-4)),
    memwit 82 (-4) 1 1 (by decide) (by decide) (by decide) (by decide),
    memwit 82 (-3) (-1) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_83 : 2 ≤ a'' 83 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),1),(-4)), (((-2),0),5),
    memwit 83 (-3) 1 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 83 (-2) 0 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_84 : 2 ≤ a'' 84 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-3)),(-3)), (((-3),0),4),
    memwit 84 (-3) (-3) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 84 (-3) 0 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_85 : 2 ≤ a'' 85 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-2)), (((-2),(-1)),5),
    memwit 85 (-4) 0 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 85 (-2) (-1) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_86 : 2 ≤ a'' 86 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-1)),4), (((-2),1),5),
    memwit 86 (-3) (-1) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 86 (-2) 1 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_87 : 2 ≤ a'' 87 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),(-2)), (((-4),0),2),
    memwit 87 (-4) (-1) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 87 (-4) 0 2 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_88 : 2 ≤ a'' 88 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),(-2)), (((-1),3),(-5)),
    memwit 88 (-4) 1 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 88 (-1) 3 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_89 : 2 ≤ a'' 89 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),2), (((-3),(-2)),(-4)),
    memwit 89 (-4) (-1) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 89 (-3) (-2) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_90 : 2 ≤ a'' 90 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),2), (((-3),3),3),
    memwit 90 (-4) 1 2 (by decide) (by decide) (by decide) (by decide),
    memwit 90 (-3) 3 3 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_91 : 2 ≤ a'' 91 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),2),(-4)), (((-1),0),(-6)),
    memwit 91 (-3) 2 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 91 (-1) 0 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_92 : 2 ≤ a'' 92 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-2),(-2)),5), ((1,(-3)),5),
    memwit 92 (-2) (-2) 5 (by decide) (by decide) (by decide) (by decide),
    memwit 92 1 (-3) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_93 : 2 ≤ a'' 93 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-2)),4), (((-1),(-1)),(-6)),
    memwit 93 (-3) (-2) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 93 (-1) (-1) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_94 : 2 ≤ a'' 94 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),(-2)), (((-2),(-4)),(-4)),
    memwit 94 (-4) (-2) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 94 (-2) (-4) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_95 : 2 ≤ a'' 95 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),2),4), ((0,(-1)),6),
    memwit 95 (-3) 2 4 (by decide) (by decide) (by decide) (by decide),
    memwit 95 0 (-1) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_96 : 2 ≤ a'' 96 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),2), ((0,(-2)),(-6)),
    memwit 96 (-4) (-2) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 96 0 (-2) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_97 : 2 ≤ a'' 97 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-3)), (((-1),0),6),
    memwit 97 (-4) 0 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 97 (-1) 0 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_98 : 2 ≤ a'' 98 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),2),2), (((-2),(-4)),4),
    memwit 98 (-4) 2 2 (by decide) (by decide) (by decide) (by decide),
    memwit 98 (-2) (-4) 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_99 : 2 ≤ a'' 99 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),(-3)), (((-2),(-3)),(-5)),
    memwit 99 (-4) (-1) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 99 (-2) (-3) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_100 : 2 ≤ a'' 100 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),3), (((-4),1),(-3)),
    memwit 100 (-4) 0 3 (by decide) (by decide) (by decide) (by decide),
    memwit 100 (-4) 1 (-3) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_101 : 2 ≤ a'' 101 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-3)),(-4)), ((1,(-1)),6),
    memwit 101 (-3) (-3) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 101 1 (-1) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_102 : 2 ≤ a'' 102 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),3), (((-3),0),(-5)),
    memwit 102 (-4) (-1) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 102 (-3) 0 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_103 : 2 ≤ a'' 103 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),3), ((0,(-4)),5),
    memwit 103 (-4) 1 3 (by decide) (by decide) (by decide) (by decide),
    memwit 103 0 (-4) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_104 : 2 ≤ a'' 104 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-1)),(-5)), (((-3),3),(-4)),
    memwit 104 (-3) (-1) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 104 (-3) 3 (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_105 : 2 ≤ a'' 105 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-3)),4), (((-3),1),(-5)),
    memwit 105 (-3) (-3) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 105 (-3) 1 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_106 : 2 ≤ a'' 106 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),(-3)), (((-1),(-2)),6),
    memwit 106 (-4) (-2) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 106 (-1) (-2) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_107 : 2 ≤ a'' 107 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),0),5), (((-2),(-1)),(-6)),
    memwit 107 (-3) 0 5 (by decide) (by decide) (by decide) (by decide),
    memwit 107 (-2) (-1) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_108 : 2 ≤ a'' 108 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),2),(-3)), (((-3),3),4),
    memwit 108 (-4) 2 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 108 (-3) 3 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_109 : 2 ≤ a'' 109 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),3), (((-3),(-1)),5),
    memwit 109 (-4) (-2) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 109 (-3) (-1) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_110 : 2 ≤ a'' 110 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),1),5), ((1,2),6),
    memwit 110 (-3) 1 5 (by decide) (by decide) (by decide) (by decide),
    memwit 110 1 2 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_111 : 2 ≤ a'' 111 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),2),3), (((-3),(-2)),(-5)),
    memwit 111 (-4) 2 3 (by decide) (by decide) (by decide) (by decide),
    memwit 111 (-3) (-2) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_112 : 2 ≤ a'' 112 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),(-3)),(-6)), ((2,1),(-6)),
    memwit 112 (-1) (-3) (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 112 2 1 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_113 : 2 ≤ a'' 113 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),2),(-5)), (((-2),(-1)),6),
    memwit 113 (-3) 2 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 113 (-2) (-1) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_114 : 2 ≤ a'' 114 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-4)), (((-2),(-2)),(-6)),
    memwit 114 (-4) 0 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 114 (-2) (-2) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_115 : 2 ≤ a'' 115 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),3),(-6)), ((2,0),6),
    memwit 115 (-1) 3 (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 115 2 0 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_116 : 2 ≤ a'' 116 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-1)),(-4)), (((-3),(-2)),5),
    memwit 116 (-4) (-1) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 116 (-3) (-2) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_117 : 2 ≤ a'' 117 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),(-4)), ((0,3),6),
    memwit 117 (-4) 1 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 117 0 3 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_118 : 2 ≤ a'' 118 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),(-3)), (((-4),0),4),
    memwit 118 (-4) (-3) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 118 (-4) 0 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_119 : 2 ≤ a'' 119 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨((0,0),(-7)), ((3,2),(-5)),
    memwit 119 0 0 (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 119 3 2 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_120 : 2 ≤ a'' 120 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),0), (((-4),(-1)),4),
    memwit 120 (-5) 0 0 (by decide) (by decide) (by decide) (by decide),
    memwit 120 (-4) (-1) 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_121 : 2 ≤ a'' 121 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),3), (((-4),1),4),
    memwit 121 (-4) (-3) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 121 (-4) 1 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_122 : 2 ≤ a'' 122 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),(-1)), (((-3),(-4)),4),
    memwit 122 (-5) 0 (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 122 (-3) (-4) 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_123 : 2 ≤ a'' 123 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),1), (((-4),(-2)),(-4)),
    memwit 123 (-5) 0 1 (by decide) (by decide) (by decide) (by decide),
    memwit 123 (-4) (-2) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_124 : 2 ≤ a'' 124 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),(-1)), (((-4),3),3),
    memwit 124 (-5) (-1) (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 124 (-4) 3 3 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_125 : 2 ≤ a'' 125 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),1), (((-4),2),(-4)),
    memwit 125 (-5) (-1) 1 (by decide) (by decide) (by decide) (by decide),
    memwit 125 (-4) 2 (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_126 : 2 ≤ a'' 126 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),1),1), (((-3),3),(-5)),
    memwit 126 (-5) 1 1 (by decide) (by decide) (by decide) (by decide),
    memwit 126 (-3) 3 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_127 : 2 ≤ a'' 127 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),4), ((1,(-1)),(-7)),
    memwit 127 (-4) (-2) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 127 1 (-1) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_128 : 2 ≤ a'' 128 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-3)),5), ((0,(-2)),(-7)),
    memwit 128 (-3) (-3) 5 (by decide) (by decide) (by decide) (by decide),
    memwit 128 0 (-2) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_129 : 2 ≤ a'' 129 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),(-2)), (((-4),2),4),
    memwit 129 (-5) 0 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 129 (-4) 2 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_130 : 2 ≤ a'' 130 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),0),7), ((0,2),(-7)),
    memwit 130 (-1) 0 7 (by decide) (by decide) (by decide) (by decide),
    memwit 130 0 2 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_131 : 2 ≤ a'' 131 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),(-2)), (((-5),0),2),
    memwit 131 (-5) (-1) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 131 (-5) 0 2 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_132 : 2 ≤ a'' 132 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),1),(-2)), (((-3),1),(-6)),
    memwit 132 (-5) 1 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 132 (-3) 1 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_133 : 2 ≤ a'' 133 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),2), (((-1),1),7),
    memwit 133 (-5) (-1) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 133 (-1) 1 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_134 : 2 ≤ a'' 134 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),1),2), (((-1),2),(-7)),
    memwit 134 (-5) 1 2 (by decide) (by decide) (by decide) (by decide),
    memwit 134 (-1) 2 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_135 : 2 ≤ a'' 135 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),(-4)), (((-3),0),6),
    memwit 135 (-4) (-3) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 135 (-3) 0 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_136 : 2 ≤ a'' 136 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-5)), ((1,2),(-7)),
    memwit 136 (-4) 0 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 136 1 2 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_137 : 2 ≤ a'' 137 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-1)),6), (((-2),0),(-7)),
    memwit 137 (-3) (-1) 6 (by decide) (by decide) (by decide) (by decide),
    memwit 137 (-2) 0 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_138 : 2 ≤ a'' 138 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),(-2)), (((-4),(-1)),(-5)),
    memwit 138 (-5) (-2) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 138 (-4) (-1) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_139 : 2 ≤ a'' 139 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),4), (((-4),1),(-5)),
    memwit 139 (-4) (-3) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 139 (-4) 1 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_140 : 2 ≤ a'' 140 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),2), (((-3),(-4)),(-5)),
    memwit 140 (-5) (-2) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 140 (-3) (-4) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_141 : 2 ≤ a'' 141 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),(-3)), (((-4),0),5),
    memwit 141 (-5) 0 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 141 (-4) 0 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_142 : 2 ≤ a'' 142 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),2), (((-4),3),4),
    memwit 142 (-5) 2 2 (by decide) (by decide) (by decide) (by decide),
    memwit 142 (-4) 3 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_143 : 2 ≤ a'' 143 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),(-3)), (((-4),(-1)),5),
    memwit 143 (-5) (-1) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 143 (-4) (-1) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_144 : 2 ≤ a'' 144 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),3), (((-5),1),(-3)),
    memwit 144 (-5) 0 3 (by decide) (by decide) (by decide) (by decide),
    memwit 144 (-5) 1 (-3) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_145 : 2 ≤ a'' 145 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),(-5)), (((-3),(-4)),5),
    memwit 145 (-4) (-2) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 145 (-3) (-4) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_146 : 2 ≤ a'' 146 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),3), (((-3),2),6),
    memwit 146 (-5) (-1) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 146 (-3) 2 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_147 : 2 ≤ a'' 147 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),1),3), (((-4),2),(-5)),
    memwit 147 (-5) 1 3 (by decide) (by decide) (by decide) (by decide),
    memwit 147 (-4) 2 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_148 : 2 ≤ a'' 148 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-2),2),(-7)), (((-2),5),5),
    memwit 148 (-2) 2 (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 148 (-2) 5 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_149 : 2 ≤ a'' 149 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),4),5), (((-2),(-4)),6),
    memwit 149 (-3) 4 5 (by decide) (by decide) (by decide) (by decide),
    memwit 149 (-2) (-4) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_150 : 2 ≤ a'' 150 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),(-3)), (((-4),(-2)),5),
    memwit 150 (-5) (-2) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 150 (-4) (-2) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_151 : 2 ≤ a'' 151 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),(-5)),(-6)), (((-1),(-3)),7),
    memwit 151 (-1) (-5) (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 151 (-1) (-3) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_152 : 2 ≤ a'' 152 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),(-3)), (((-4),(-4)),(-4)),
    memwit 152 (-5) 2 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 152 (-4) (-4) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_153 : 2 ≤ a'' 153 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),3), (((-3),3),(-6)),
    memwit 153 (-5) (-2) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 153 (-3) 3 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_154 : 2 ≤ a'' 154 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),3),7), ((5,0),3),
    memwit 154 (-1) 3 7 (by decide) (by decide) (by decide) (by decide),
    memwit 154 5 0 3 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_155 : 2 ≤ a'' 155 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),3), (((-2),2),7),
    memwit 155 (-5) 2 3 (by decide) (by decide) (by decide) (by decide),
    memwit 155 (-2) 2 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_156 : 2 ≤ a'' 156 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-4)),4), (((-3),(-3)),6),
    memwit 156 (-4) (-4) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 156 (-3) (-3) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_157 : 2 ≤ a'' 157 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),(-5)), (((-1),(-5)),6),
    memwit 157 (-4) (-3) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 157 (-1) (-5) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_158 : 2 ≤ a'' 158 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),(-4)), (((-2),(-3)),(-7)),
    memwit 158 (-5) 0 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 158 (-2) (-3) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_159 : 2 ≤ a'' 159 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),3),6), ((0,1),(-8)),
    memwit 159 (-3) 3 6 (by decide) (by decide) (by decide) (by decide),
    memwit 159 0 1 (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_160 : 2 ≤ a'' 160 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),(-4)), (((-4),3),(-5)),
    memwit 160 (-5) (-1) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 160 (-4) 3 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_161 : 2 ≤ a'' 161 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),1),(-4)), (((-3),0),(-7)),
    memwit 161 (-5) 1 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 161 (-3) 0 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_162 : 2 ≤ a'' 162 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-3)),(-3)), (((-5),0),4),
    memwit 162 (-5) (-3) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 162 (-5) 0 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_163 : 2 ≤ a'' 163 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-6)), (((-3),(-1)),(-7)),
    memwit 163 (-4) 0 (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 163 (-3) (-1) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_164 : 2 ≤ a'' 164 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),4), (((-3),1),(-7)),
    memwit 164 (-5) (-1) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 164 (-3) 1 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_165 : 2 ≤ a'' 165 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-3)),3), (((-5),1),4),
    memwit 165 (-5) (-3) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 165 (-5) 1 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_166 : 2 ≤ a'' 166 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),(-6)), ((0,(-1)),8),
    memwit 166 (-4) 1 (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 166 0 (-1) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_167 : 2 ≤ a'' 167 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),(-4)), (((-3),(-5)),5),
    memwit 167 (-5) (-2) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 167 (-3) (-5) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_168 : 2 ≤ a'' 168 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),3),3), (((-3),0),7),
    memwit 168 (-5) 3 3 (by decide) (by decide) (by decide) (by decide),
    memwit 168 (-3) 0 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_169 : 2 ≤ a'' 169 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),(-4)), (((-4),0),6),
    memwit 169 (-5) 2 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 169 (-4) 0 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_170 : 2 ≤ a'' 170 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-2)),(-7)), (((-3),(-1)),7),
    memwit 170 (-3) (-2) (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 170 (-3) (-1) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_171 : 2 ≤ a'' 171 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),4), (((-4),(-1)),6),
    memwit 171 (-5) (-2) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 171 (-4) (-1) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_172 : 2 ≤ a'' 172 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),(-6)), (((-4),1),6),
    memwit 172 (-4) (-2) (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 172 (-4) 1 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_173 : 2 ≤ a'' 173 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),4), (((-3),(-4)),6),
    memwit 173 (-5) 2 4 (by decide) (by decide) (by decide) (by decide),
    memwit 173 (-3) (-4) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_174 : 2 ≤ a'' 174 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),0), (((-4),(-4)),(-5)),
    memwit 174 (-6) 0 0 (by decide) (by decide) (by decide) (by decide),
    memwit 174 (-4) (-4) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_175 : 2 ≤ a'' 175 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-2),(-4)),(-7)), ((0,2),8),
    memwit 175 (-2) (-4) (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 175 0 2 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_176 : 2 ≤ a'' 176 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),(-1)), (((-2),(-1)),(-8)),
    memwit 176 (-6) 0 (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 176 (-2) (-1) (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_177 : 2 ≤ a'' 177 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),1), (((-3),(-2)),7),
    memwit 177 (-6) 0 1 (by decide) (by decide) (by decide) (by decide),
    memwit 177 (-3) (-2) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_178 : 2 ≤ a'' 178 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-1)), (((-4),(-2)),6),
    memwit 178 (-6) (-1) (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 178 (-4) (-2) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_179 : 2 ≤ a'' 179 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),1), (((-5),(-3)),(-4)),
    memwit 179 (-6) (-1) 1 (by decide) (by decide) (by decide) (by decide),
    memwit 179 (-5) (-3) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_180 : 2 ≤ a'' 180 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),1),1), (((-5),0),(-5)),
    memwit 180 (-6) 1 1 (by decide) (by decide) (by decide) (by decide),
    memwit 180 (-5) 0 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_181 : 2 ≤ a'' 181 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),(-3)),(-8)), ((1,2),8),
    memwit 181 (-1) (-3) (-8) (by decide) (by decide) (by decide) (by decide),
    memwit 181 1 2 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_182 : 2 ≤ a'' 182 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-1)),(-5)), (((-5),3),(-4)),
    memwit 182 (-5) (-1) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 182 (-5) 3 (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_183 : 2 ≤ a'' 183 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),(-2)), (((-5),(-3)),4),
    memwit 183 (-6) 0 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 183 (-5) (-3) 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_184 : 2 ≤ a'' 184 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),(-6)), (((-2),(-1)),8),
    memwit 184 (-4) (-3) (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 184 (-2) (-1) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_185 : 2 ≤ a'' 185 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-2)), (((-6),0),2),
    memwit 185 (-6) (-1) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 185 (-6) 0 2 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_186 : 2 ≤ a'' 186 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),1),(-2)), (((-5),3),4),
    memwit 186 (-6) 1 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 186 (-5) 3 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_187 : 2 ≤ a'' 187 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),2), (((-5),(-1)),5),
    memwit 187 (-6) (-1) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 187 (-5) (-1) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_188 : 2 ≤ a'' 188 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),1),2), (((-5),1),5),
    memwit 188 (-6) 1 2 (by decide) (by decide) (by decide) (by decide),
    memwit 188 (-5) 1 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_189 : 2 ≤ a'' 189 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-2)),(-5)), (((-3),(-5)),(-6)),
    memwit 189 (-5) (-2) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 189 (-3) (-5) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_190 : 2 ≤ a'' 190 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),6), (((-1),(-5)),7),
    memwit 190 (-4) (-3) 6 (by decide) (by decide) (by decide) (by decide),
    memwit 190 (-1) (-5) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_191 : 2 ≤ a'' 191 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),(-5)), (((-2),(-2)),8),
    memwit 191 (-5) 2 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 191 (-2) (-2) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_192 : 2 ≤ a'' 192 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),(-2)), (((-3),3),7),
    memwit 192 (-6) (-2) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 192 (-3) 3 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_193 : 2 ≤ a'' 193 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),3),6), (((-2),2),8),
    memwit 193 (-4) 3 6 (by decide) (by decide) (by decide) (by decide),
    memwit 193 (-2) 2 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_194 : 2 ≤ a'' 194 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),2), (((-5),(-2)),5),
    memwit 194 (-6) (-2) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 194 (-5) (-2) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_195 : 2 ≤ a'' 195 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),(-3)), (((-4),0),(-7)),
    memwit 195 (-6) 0 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 195 (-4) 0 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_196 : 2 ≤ a'' 196 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),2), (((-5),(-4)),(-4)),
    memwit 196 (-6) 2 2 (by decide) (by decide) (by decide) (by decide),
    memwit 196 (-5) (-4) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_197 : 2 ≤ a'' 197 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-3)), (((-4),(-1)),(-7)),
    memwit 197 (-6) (-1) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 197 (-4) (-1) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_198 : 2 ≤ a'' 198 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),3), (((-6),1),(-3)),
    memwit 198 (-6) 0 3 (by decide) (by decide) (by decide) (by decide),
    memwit 198 (-6) 1 (-3) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_199 : 2 ≤ a'' 199 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-4)),(-7)), ((2,(-3)),(-8)),
    memwit 199 (-3) (-4) (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 199 2 (-3) (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_200 : 2 ≤ a'' 200 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),3), (((-5),(-4)),4),
    memwit 200 (-6) (-1) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 200 (-5) (-4) 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_201 : 2 ≤ a'' 201 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),1),3), (((-5),(-3)),(-5)),
    memwit 201 (-6) 1 3 (by decide) (by decide) (by decide) (by decide),
    memwit 201 (-5) (-3) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_202 : 2 ≤ a'' 202 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),7), (((-2),5),(-7)),
    memwit 202 (-4) 0 7 (by decide) (by decide) (by decide) (by decide),
    memwit 202 (-2) 5 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_203 : 2 ≤ a'' 203 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),4),(-7)), (((-2),(-3)),8),
    memwit 203 (-3) 4 (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 203 (-2) (-3) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_204 : 2 ≤ a'' 204 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),(-3)), (((-5),3),(-5)),
    memwit 204 (-6) (-2) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 204 (-5) 3 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_205 : 2 ≤ a'' 205 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),7), (((-4),4),(-6)),
    memwit 205 (-4) 1 7 (by decide) (by decide) (by decide) (by decide),
    memwit 205 (-4) 4 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_206 : 2 ≤ a'' 206 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),(-3)), (((-5),(-3)),5),
    memwit 206 (-6) 2 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 206 (-5) (-3) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_207 : 2 ≤ a'' 207 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),3), (((-5),0),(-6)),
    memwit 207 (-6) (-2) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 207 (-5) 0 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_208 : 2 ≤ a'' 208 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-1)),8), ((1,(-4)),8),
    memwit 208 (-3) (-1) 8 (by decide) (by decide) (by decide) (by decide),
    memwit 208 1 (-4) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_209 : 2 ≤ a'' 209 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),3), (((-5),(-1)),(-6)),
    memwit 209 (-6) 2 3 (by decide) (by decide) (by decide) (by decide),
    memwit 209 (-5) (-1) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_210 : 2 ≤ a'' 210 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),1),(-6)), (((-3),4),7),
    memwit 210 (-5) 1 (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 210 (-3) 4 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_211 : 2 ≤ a'' 211 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-2)),7), (((-4),4),6),
    memwit 211 (-4) (-2) 7 (by decide) (by decide) (by decide) (by decide),
    memwit 211 (-4) 4 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_212 : 2 ≤ a'' 212 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),(-4)), (((-2),(-4)),(-8)),
    memwit 212 (-6) 0 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 212 (-2) (-4) (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_213 : 2 ≤ a'' 213 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),6), (((-4),2),7),
    memwit 213 (-5) 0 6 (by decide) (by decide) (by decide) (by decide),
    memwit 213 (-4) 2 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_214 : 2 ≤ a'' 214 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-4)), (((-1),1),9),
    memwit 214 (-6) (-1) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 214 (-1) 1 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_215 : 2 ≤ a'' 215 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),1),(-4)), (((-5),(-1)),6),
    memwit 215 (-6) 1 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 215 (-5) (-1) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_216 : 2 ≤ a'' 216 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-3)),(-3)), (((-6),0),4),
    memwit 216 (-6) (-3) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 216 (-6) 0 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_217 : 2 ≤ a'' 217 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),2),8), (((-1),(-6)),7),
    memwit 217 (-3) 2 8 (by decide) (by decide) (by decide) (by decide),
    memwit 217 (-1) (-6) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_218 : 2 ≤ a'' 218 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),4), (((-5),(-4)),(-5)),
    memwit 218 (-6) (-1) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 218 (-5) (-4) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_219 : 2 ≤ a'' 219 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-3)),3), (((-6),1),4),
    memwit 219 (-6) (-3) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 219 (-6) 1 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_220 : 2 ≤ a'' 220 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-2),(-4)),8), (((-1),(-5)),(-8)),
    memwit 220 (-2) (-4) 8 (by decide) (by decide) (by decide) (by decide),
    memwit 220 (-1) (-5) (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_221 : 2 ≤ a'' 221 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),(-4)), (((-3),(-5)),(-7)),
    memwit 221 (-6) (-2) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 221 (-3) (-5) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_222 : 2 ≤ a'' 222 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),3),3), (((-5),(-2)),6),
    memwit 222 (-6) 3 3 (by decide) (by decide) (by decide) (by decide),
    memwit 222 (-5) (-2) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_223 : 2 ≤ a'' 223 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),(-4)), (((-5),(-4)),5),
    memwit 223 (-6) 2 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 223 (-5) (-4) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_224 : 2 ≤ a'' 224 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),6), (((-2),(-6)),(-7)),
    memwit 224 (-5) 2 6 (by decide) (by decide) (by decide) (by decide),
    memwit 224 (-2) (-6) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_225 : 2 ≤ a'' 225 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),4), (((-2),(-2)),(-9)),
    memwit 225 (-6) (-2) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 225 (-2) (-2) (-9) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_226 : 2 ≤ a'' 226 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),3),7), (((-3),5),(-7)),
    memwit 226 (-4) 3 7 (by decide) (by decide) (by decide) (by decide),
    memwit 226 (-3) 5 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_227 : 2 ≤ a'' 227 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),4), (((-5),4),5),
    memwit 227 (-6) 2 4 (by decide) (by decide) (by decide) (by decide),
    memwit 227 (-5) 4 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_228 : 2 ≤ a'' 228 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-3)),(-6)), (((-4),5),(-6)),
    memwit 228 (-5) (-3) (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 228 (-4) 5 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_229 : 2 ≤ a'' 229 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-5)),6), ((0,5),8),
    memwit 229 (-4) (-5) 6 (by decide) (by decide) (by decide) (by decide),
    memwit 229 0 5 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_230 : 2 ≤ a'' 230 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),3),8), (((-2),6),(-7)),
    memwit 230 (-3) 3 8 (by decide) (by decide) (by decide) (by decide),
    memwit 230 (-2) 6 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_231 : 2 ≤ a'' 231 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),3),(-6)), (((-2),(-6)),7),
    memwit 231 (-5) 3 (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 231 (-2) (-6) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_232 : 2 ≤ a'' 232 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-8)), (((-1),(-3)),9),
    memwit 232 (-4) 0 (-8) (by decide) (by decide) (by decide) (by decide),
    memwit 232 (-1) (-3) 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_233 : 2 ≤ a'' 233 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-3)),(-4)), (((-4),(-4)),(-7)),
    memwit 233 (-6) (-3) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 233 (-4) (-4) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_234 : 2 ≤ a'' 234 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),(-5)), (((-5),(-3)),6),
    memwit 234 (-6) 0 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 234 (-5) (-3) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_235 : 2 ≤ a'' 235 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),1),(-8)), (((-1),3),9),
    memwit 235 (-4) 1 (-8) (by decide) (by decide) (by decide) (by decide),
    memwit 235 (-1) 3 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_236 : 2 ≤ a'' 236 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-5)), (((-6),3),(-4)),
    memwit 236 (-6) (-1) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 236 (-6) 3 (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_237 : 2 ≤ a'' 237 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-3)),4), (((-6),1),(-5)),
    memwit 237 (-6) (-3) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 237 (-6) 1 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_238 : 2 ≤ a'' 238 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),0), ((0,(-7)),(-7)),
    memwit 238 (-7) 0 0 (by decide) (by decide) (by decide) (by decide),
    memwit 238 0 (-7) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_239 : 2 ≤ a'' 239 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),5), (((-5),0),(-7)),
    memwit 239 (-6) 0 5 (by decide) (by decide) (by decide) (by decide),
    memwit 239 (-5) 0 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_240 : 2 ≤ a'' 240 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),(-1)), (((-6),3),4),
    memwit 240 (-7) 0 (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 240 (-6) 3 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_241 : 2 ≤ a'' 241 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),1), (((-6),(-1)),5),
    memwit 241 (-7) 0 1 (by decide) (by decide) (by decide) (by decide),
    memwit 241 (-6) (-1) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_242 : 2 ≤ a'' 242 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),(-1)), (((-6),1),5),
    memwit 242 (-7) (-1) (-1) (by decide) (by decide) (by decide) (by decide),
    memwit 242 (-6) 1 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_243 : 2 ≤ a'' 243 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),1), (((-6),(-2)),(-5)),
    memwit 243 (-7) (-1) 1 (by decide) (by decide) (by decide) (by decide),
    memwit 243 (-6) (-2) (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_244 : 2 ≤ a'' 244 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),1),1), (((-4),4),7),
    memwit 244 (-7) 1 1 (by decide) (by decide) (by decide) (by decide),
    memwit 244 (-4) 4 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_245 : 2 ≤ a'' 245 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),(-5)), (((-5),(-5)),5),
    memwit 245 (-6) 2 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 245 (-5) (-5) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_246 : 2 ≤ a'' 246 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),0),7), (((-2),(-3)),9),
    memwit 246 (-5) 0 7 (by decide) (by decide) (by decide) (by decide),
    memwit 246 (-2) (-3) 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_247 : 2 ≤ a'' 247 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),(-2)), (((-2),5),8),
    memwit 247 (-7) 0 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 247 (-2) 5 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_248 : 2 ≤ a'' 248 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),5), (((-5),(-2)),(-7)),
    memwit 248 (-6) (-2) 5 (by decide) (by decide) (by decide) (by decide),
    memwit 248 (-5) (-2) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_249 : 2 ≤ a'' 249 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),(-2)), (((-7),0),2),
    memwit 249 (-7) (-1) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 249 (-7) 0 2 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_250 : 2 ≤ a'' 250 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),1),(-2)), (((-6),(-4)),(-4)),
    memwit 250 (-7) 1 (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 250 (-6) (-4) (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_251 : 2 ≤ a'' 251 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),2), (((-5),(-4)),6),
    memwit 251 (-7) (-1) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 251 (-5) (-4) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_252 : 2 ≤ a'' 252 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),1),2), (((-3),1),9),
    memwit 252 (-7) 1 2 (by decide) (by decide) (by decide) (by decide),
    memwit 252 (-3) 1 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_253 : 2 ≤ a'' 253 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-3)),(-8)), (((-1),4),9),
    memwit 253 (-4) (-3) (-8) (by decide) (by decide) (by decide) (by decide),
    memwit 253 (-1) 4 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_254 : 2 ≤ a'' 254 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-4)),4), (((-3),6),(-7)),
    memwit 254 (-6) (-4) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 254 (-3) 6 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_255 : 2 ≤ a'' 255 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-3)),(-5)), (((-5),(-2)),7),
    memwit 255 (-6) (-3) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 255 (-5) (-2) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_256 : 2 ≤ a'' 256 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),(-2)), (((-4),(-6)),6),
    memwit 256 (-7) (-2) (-2) (by decide) (by decide) (by decide) (by decide),
    memwit 256 (-4) (-6) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_257 : 2 ≤ a'' 257 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),2),7), ((0,(-1)),10),
    memwit 257 (-5) 2 7 (by decide) (by decide) (by decide) (by decide),
    memwit 257 0 (-1) 10 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_258 : 2 ≤ a'' 258 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),2), (((-6),3),(-5)),
    memwit 258 (-7) (-2) 2 (by decide) (by decide) (by decide) (by decide),
    memwit 258 (-6) 3 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_259 : 2 ≤ a'' 259 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),(-3)), (((-1),0),10),
    memwit 259 (-7) 0 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 259 (-1) 0 10 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_260 : 2 ≤ a'' 260 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),2),2), (((-6),(-3)),5),
    memwit 260 (-7) 2 2 (by decide) (by decide) (by decide) (by decide),
    memwit 260 (-6) (-3) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_261 : 2 ≤ a'' 261 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),(-3)), (((-6),0),(-6)),
    memwit 261 (-7) (-1) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 261 (-6) 0 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_262 : 2 ≤ a'' 262 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),3), (((-7),1),(-3)),
    memwit 262 (-7) 0 3 (by decide) (by decide) (by decide) (by decide),
    memwit 262 (-7) 1 (-3) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_263 : 2 ≤ a'' 263 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-6)), (((-6),3),5),
    memwit 263 (-6) (-1) (-6) (by decide) (by decide) (by decide) (by decide),
    memwit 263 (-6) 3 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_264 : 2 ≤ a'' 264 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),3), (((-6),1),(-6)),
    memwit 264 (-7) (-1) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 264 (-6) 1 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_265 : 2 ≤ a'' 265 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),1),3), (((-2),(-1)),(-10)),
    memwit 265 (-7) 1 3 (by decide) (by decide) (by decide) (by decide),
    memwit 265 (-2) (-1) (-10) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_266 : 2 ≤ a'' 266 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),(-5)),8), (((-2),1),(-10)),
    memwit 266 (-3) (-5) 8 (by decide) (by decide) (by decide) (by decide),
    memwit 266 (-2) 1 (-10) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_267 : 2 ≤ a'' 267 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),6), (((-5),(-5)),(-6)),
    memwit 267 (-6) 0 6 (by decide) (by decide) (by decide) (by decide),
    memwit 267 (-5) (-5) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_268 : 2 ≤ a'' 268 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),(-3)), (((-1),(-2)),10),
    memwit 268 (-7) (-2) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 268 (-1) (-2) 10 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_269 : 2 ≤ a'' 269 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),6), (((-2),(-6)),8),
    memwit 269 (-6) (-1) 6 (by decide) (by decide) (by decide) (by decide),
    memwit 269 (-2) (-6) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_270 : 2 ≤ a'' 270 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),2),(-3)), (((-6),(-2)),(-6)),
    memwit 270 (-7) 2 (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 270 (-6) (-2) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_271 : 2 ≤ a'' 271 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),3), (((-3),5),8),
    memwit 271 (-7) (-2) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 271 (-3) 5 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_272 : 2 ≤ a'' 272 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-4)),(-5)), (((-6),2),(-6)),
    memwit 272 (-6) (-4) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 272 (-6) 2 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_273 : 2 ≤ a'' 273 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),2),3), (((-5),(-5)),6),
    memwit 273 (-7) 2 3 (by decide) (by decide) (by decide) (by decide),
    memwit 273 (-5) (-5) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_274 : 2 ≤ a'' 274 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),0),(-9)), (((-4),4),(-8)),
    memwit 274 (-4) 0 (-9) (by decide) (by decide) (by decide) (by decide),
    memwit 274 (-4) 4 (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_275 : 2 ≤ a'' 275 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-2),(-1)),10), (((-2),6),8),
    memwit 275 (-2) (-1) 10 (by decide) (by decide) (by decide) (by decide),
    memwit 275 (-2) 6 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_276 : 2 ≤ a'' 276 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),(-4)), (((-6),(-2)),6),
    memwit 276 (-7) 0 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 276 (-6) (-2) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_277 : 2 ≤ a'' 277 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-4)),5), (((-5),(-4)),(-7)),
    memwit 277 (-6) (-4) 5 (by decide) (by decide) (by decide) (by decide),
    memwit 277 (-5) (-4) (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_278 : 2 ≤ a'' 278 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),(-4)), (((-6),2),6),
    memwit 278 (-7) (-1) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 278 (-6) 2 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_279 : 2 ≤ a'' 279 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),1),(-4)), (((-5),1),(-8)),
    memwit 279 (-7) 1 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 279 (-5) 1 (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_280 : 2 ≤ a'' 280 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-3)),(-3)), (((-7),0),4),
    memwit 280 (-7) (-3) (-3) (by decide) (by decide) (by decide) (by decide),
    memwit 280 (-7) 0 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_281 : 2 ≤ a'' 281 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),4),5), (((-5),4),(-7)),
    memwit 281 (-6) 4 5 (by decide) (by decide) (by decide) (by decide),
    memwit 281 (-5) 4 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_282 : 2 ≤ a'' 282 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),4), (((-6),(-3)),(-6)),
    memwit 282 (-7) (-1) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 282 (-6) (-3) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_283 : 2 ≤ a'' 283 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-3)),3), (((-7),1),4),
    memwit 283 (-7) (-3) 3 (by decide) (by decide) (by decide) (by decide),
    memwit 283 (-7) 1 4 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_284 : 2 ≤ a'' 284 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),(-4)),7), (((-5),0),8),
    memwit 284 (-5) (-4) 7 (by decide) (by decide) (by decide) (by decide),
    memwit 284 (-5) 0 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_285 : 2 ≤ a'' 285 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),(-4)), (((-6),3),(-6)),
    memwit 285 (-7) (-2) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 285 (-6) 3 (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_286 : 2 ≤ a'' 286 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),3),3), (((-5),(-1)),8),
    memwit 286 (-7) 3 3 (by decide) (by decide) (by decide) (by decide),
    memwit 286 (-5) (-1) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_287 : 2 ≤ a'' 287 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),2),(-4)), (((-5),1),8),
    memwit 287 (-7) 2 (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 287 (-5) 1 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_288 : 2 ≤ a'' 288 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-3)),6), (((-5),4),7),
    memwit 288 (-6) (-3) 6 (by decide) (by decide) (by decide) (by decide),
    memwit 288 (-5) 4 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_289 : 2 ≤ a'' 289 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),4), (((-4),(-6)),7),
    memwit 289 (-7) (-2) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 289 (-4) (-6) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_290 : 2 ≤ a'' 290 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-3),1),(-10)), (((-2),5),9),
    memwit 290 (-3) 1 (-10) (by decide) (by decide) (by decide) (by decide),
    memwit 290 (-2) 5 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_291 : 2 ≤ a'' 291 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),2),4), (((-6),3),6),
    memwit 291 (-7) 2 4 (by decide) (by decide) (by decide) (by decide),
    memwit 291 (-6) 3 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_292 : 2 ≤ a'' 292 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-4),(-5)),(-8)), (((-4),(-2)),9),
    memwit 292 (-4) (-5) (-8) (by decide) (by decide) (by decide) (by decide),
    memwit 292 (-4) (-2) 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_293 : 2 ≤ a'' 293 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),0),(-7)), (((-5),(-2)),8),
    memwit 293 (-6) 0 (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 293 (-5) (-2) 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_294 : 2 ≤ a'' 294 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-5)),(-5)), (((-5),(-6)),(-6)),
    memwit 294 (-6) (-5) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 294 (-5) (-6) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_295 : 2 ≤ a'' 295 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-1)),(-7)), (((-5),2),8),
    memwit 295 (-6) (-1) (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 295 (-5) 2 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_296 : 2 ≤ a'' 296 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),1),(-7)), (((-3),(-2)),(-10)),
    memwit 296 (-6) 1 (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 296 (-3) (-2) (-10) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_297 : 2 ≤ a'' 297 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-3)),(-4)), (((-5),(-3)),(-8)),
    memwit 297 (-7) (-3) (-4) (by decide) (by decide) (by decide) (by decide),
    memwit 297 (-5) (-3) (-8) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_298 : 2 ≤ a'' 298 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),(-5)), (((-4),3),(-9)),
    memwit 298 (-7) 0 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 298 (-4) 3 (-9) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_299 : 2 ≤ a'' 299 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-5)),5), (((-6),(-4)),(-6)),
    memwit 299 (-6) (-5) 5 (by decide) (by decide) (by decide) (by decide),
    memwit 299 (-6) (-4) (-6) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_300 : 2 ≤ a'' 300 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),(-5)), (((-7),3),(-4)),
    memwit 300 (-7) (-1) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 300 (-7) 3 (-4) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_301 : 2 ≤ a'' 301 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-3)),4), (((-7),1),(-5)),
    memwit 301 (-7) (-3) 4 (by decide) (by decide) (by decide) (by decide),
    memwit 301 (-7) 1 (-5) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_302 : 2 ≤ a'' 302 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),(-2)),(-7)), (((-6),(-1)),7),
    memwit 302 (-6) (-2) (-7) (by decide) (by decide) (by decide) (by decide),
    memwit 302 (-6) (-1) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_303 : 2 ≤ a'' 303 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),0),5), (((-6),1),7),
    memwit 303 (-7) 0 5 (by decide) (by decide) (by decide) (by decide),
    memwit 303 (-6) 1 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_304 : 2 ≤ a'' 304 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),3),4), (((-6),2),(-7)),
    memwit 304 (-7) 3 4 (by decide) (by decide) (by decide) (by decide),
    memwit 304 (-6) 2 (-7) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_305 : 2 ≤ a'' 305 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-1)),5), (((-6),(-4)),6),
    memwit 305 (-7) (-1) 5 (by decide) (by decide) (by decide) (by decide),
    memwit 305 (-6) (-4) 6 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_306 : 2 ≤ a'' 306 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),1),5), (((-5),(-5)),7),
    memwit 306 (-7) 1 5 (by decide) (by decide) (by decide) (by decide),
    memwit 306 (-5) (-5) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_307 : 2 ≤ a'' 307 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),(-2)),(-5)), (((-4),3),9),
    memwit 307 (-7) (-2) (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 307 (-4) 3 9 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_308 : 2 ≤ a'' 308 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-5),3),8), (((-3),(-3)),(-10)),
    memwit 308 (-5) 3 8 (by decide) (by decide) (by decide) (by decide),
    memwit 308 (-3) (-3) (-10) (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_309 : 2 ≤ a'' 309 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-7),2),(-5)), (((-6),(-2)),7),
    memwit 309 (-7) 2 (-5) (by decide) (by decide) (by decide) (by decide),
    memwit 309 (-6) (-2) 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_310 : 2 ≤ a'' 310 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-1),(-2)),(-11)), ((0,(-1)),11),
    memwit 310 (-1) (-2) (-11) (by decide) (by decide) (by decide) (by decide),
    memwit 310 0 (-1) 11 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_311 : 2 ≤ a'' 311 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-6),2),7), (((-5),5),7),
    memwit 311 (-6) 2 7 (by decide) (by decide) (by decide) (by decide),
    memwit 311 (-5) 5 7 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_312 : 2 ≤ a'' 312 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨(((-8),0),0), (((-7),(-2)),5),
    memwit 312 (-8) 0 0 (by decide) (by decide) (by decide) (by decide),
    memwit 312 (-7) (-2) 5 (by decide) (by decide) (by decide) (by decide),
    by decide⟩
lemma keyfin_313 : 2 ≤ a'' 313 := by
  unfold a''
  rw [show (2:ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  exact ⟨((2,6),(-9)), ((4,5),8),
    memwit 313 2 6 (-9) (by decide) (by decide) (by decide) (by decide),
    memwit 313 4 5 8 (by decide) (by decide) (by decide) (by decide),
    by decide⟩

lemma keyfin : ∀ n : ℕ, 80 ≤ n → n ≤ 313 → 2 ≤ a'' n := by
  intro n h1 h2
  interval_cases n
  exacts [keyfin_80, keyfin_81, keyfin_82, keyfin_83, keyfin_84, keyfin_85, keyfin_86, keyfin_87, keyfin_88, keyfin_89, keyfin_90, keyfin_91, keyfin_92, keyfin_93, keyfin_94, keyfin_95, keyfin_96, keyfin_97, keyfin_98, keyfin_99, keyfin_100, keyfin_101, keyfin_102, keyfin_103, keyfin_104, keyfin_105, keyfin_106, keyfin_107, keyfin_108, keyfin_109, keyfin_110, keyfin_111, keyfin_112, keyfin_113, keyfin_114, keyfin_115, keyfin_116, keyfin_117, keyfin_118, keyfin_119, keyfin_120, keyfin_121, keyfin_122, keyfin_123, keyfin_124, keyfin_125, keyfin_126, keyfin_127, keyfin_128, keyfin_129, keyfin_130, keyfin_131, keyfin_132, keyfin_133, keyfin_134, keyfin_135, keyfin_136, keyfin_137, keyfin_138, keyfin_139, keyfin_140, keyfin_141, keyfin_142, keyfin_143, keyfin_144, keyfin_145, keyfin_146, keyfin_147, keyfin_148, keyfin_149, keyfin_150, keyfin_151, keyfin_152, keyfin_153, keyfin_154, keyfin_155, keyfin_156, keyfin_157, keyfin_158, keyfin_159, keyfin_160, keyfin_161, keyfin_162, keyfin_163, keyfin_164, keyfin_165, keyfin_166, keyfin_167, keyfin_168, keyfin_169, keyfin_170, keyfin_171, keyfin_172, keyfin_173, keyfin_174, keyfin_175, keyfin_176, keyfin_177, keyfin_178, keyfin_179, keyfin_180, keyfin_181, keyfin_182, keyfin_183, keyfin_184, keyfin_185, keyfin_186, keyfin_187, keyfin_188, keyfin_189, keyfin_190, keyfin_191, keyfin_192, keyfin_193, keyfin_194, keyfin_195, keyfin_196, keyfin_197, keyfin_198, keyfin_199, keyfin_200, keyfin_201, keyfin_202, keyfin_203, keyfin_204, keyfin_205, keyfin_206, keyfin_207, keyfin_208, keyfin_209, keyfin_210, keyfin_211, keyfin_212, keyfin_213, keyfin_214, keyfin_215, keyfin_216, keyfin_217, keyfin_218, keyfin_219, keyfin_220, keyfin_221, keyfin_222, keyfin_223, keyfin_224, keyfin_225, keyfin_226, keyfin_227, keyfin_228, keyfin_229, keyfin_230, keyfin_231, keyfin_232, keyfin_233, keyfin_234, keyfin_235, keyfin_236, keyfin_237, keyfin_238, keyfin_239, keyfin_240, keyfin_241, keyfin_242, keyfin_243, keyfin_244, keyfin_245, keyfin_246, keyfin_247, keyfin_248, keyfin_249, keyfin_250, keyfin_251, keyfin_252, keyfin_253, keyfin_254, keyfin_255, keyfin_256, keyfin_257, keyfin_258, keyfin_259, keyfin_260, keyfin_261, keyfin_262, keyfin_263, keyfin_264, keyfin_265, keyfin_266, keyfin_267, keyfin_268, keyfin_269, keyfin_270, keyfin_271, keyfin_272, keyfin_273, keyfin_274, keyfin_275, keyfin_276, keyfin_277, keyfin_278, keyfin_279, keyfin_280, keyfin_281, keyfin_282, keyfin_283, keyfin_284, keyfin_285, keyfin_286, keyfin_287, keyfin_288, keyfin_289, keyfin_290, keyfin_291, keyfin_292, keyfin_293, keyfin_294, keyfin_295, keyfin_296, keyfin_297, keyfin_298, keyfin_299, keyfin_300, keyfin_301, keyfin_302, keyfin_303, keyfin_304, keyfin_305, keyfin_306, keyfin_307, keyfin_308, keyfin_309, keyfin_310, keyfin_311, keyfin_312, keyfin_313]

set_option maxHeartbeats 0 in
lemma key : ∀ n : ℕ, 80 ≤ n → 2 ≤ a n := by
  intro n hn
  rcases Nat.lt_or_ge n 314 with h | h
  · rw [a_eq_a'' n (by omega)]
    exact keyfin n hn (by omega)
  · -- The genuine remaining content: the infinite open analytic tail n ≥ 314.
    sorry

/-
Conjecture 1 from OEIS A377224:
a(n) = 0 only for n = 1.
Also, a(n) = 1 only for n = 0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61, 79.
-/
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem oeis_A377224_conjecture1 :
  (∀ (n : ℕ), a n = 0 ↔ n = 1) ∧
  (∀ (n : ℕ), a n = 1 ↔ n ∈ ({0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61, 79} : Finset ℕ)) :=
by
  constructor
  · intro n
    rcases Nat.lt_or_ge n 80 with h | h
    · rw [a_eq_a' n (by omega)]
      interval_cases n <;> decide
    · have h2 := key n h
      constructor
      · intro h0; omega
      · intro h1; exfalso; omega
  · intro n
    rcases Nat.lt_or_ge n 80 with h | h
    · rw [a_eq_a' n (by omega)]
      interval_cases n <;> decide
    · have h2 := key n h
      constructor
      · intro h1; omega
      · intro hmem; exfalso; fin_cases hmem <;> omega
