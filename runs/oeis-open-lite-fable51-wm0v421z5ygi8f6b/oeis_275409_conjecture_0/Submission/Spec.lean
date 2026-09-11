import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275409: Number of ordered ways to write $n$ as $2w^2 + x^2 + y^2 + z^2$ with $w + x + 2y + 4z$ a square, where $w,x,y,z$ are nonnegative integers.
$$a(n) = \# \left\{(w, x, y, z) \in \mathbb{N}^4 \mid 2w^2 + x^2 + y^2 + z^2 = n, \quad w + x + 2y + 4z \text{ is a square} \right\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define perfect square check using computable `Nat.sqrt`.
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- A safe upper bound for $w, x, y, z$ is $\lfloor\sqrt{n}\rfloor + 1$.
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M

  -- The search space of ordered quadruples, structured as $w \times (x \times (y \times z))$.
  -- This allows for robust iteration over $w, x, y, z$.
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))

  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd

    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z

    -- The bounds chosen ensures that we will find all solutions (w,x,y,z) where w^2, x^2, y^2, z^2 <= n.
    -- If $2w^2 + x^2 + y^2 + z^2 = n$, then $w, x, y, z \le \sqrt{n}$, so this upper bound is sufficient.
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

-- Proof snippets provided in the prompt are removed as requested, only
-- the definition needs to be present and the conjecture must be stated.
-- The definition has been corrected to rely on a mathematically sound search space bound
-- based on the fact that $w, x, y, z \le \sqrt{n}$.

/-- The set of natural numbers $n$ for which $a(n) = 0$ is conjectured to be $\{3, 10\}$. -/
def A275409_zero_set : Finset ℕ :=
  {3, 10}

/-- The set of natural numbers $n$ for which $a(n) = 1$ is conjectured to be a specific finite set. -/
def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

set_option maxRecDepth 1000000

/-- computable variant with explicit bound `M` and bounded square search -/
def a₂ (n M : ℕ) : ℕ :=
  ((range M).product ((range M).product ((range M).product (range M)))).sum
    fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
      if 2 * p.1^2 + p.2.1^2 + p.2.2.1^2 + p.2.2.2^2 = n ∧
          ∃ r ≤ p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2,
            r * r = p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2 then 1 else 0

lemma is_sq_iff (k : ℕ) : k.sqrt * k.sqrt = k ↔ ∃ r ≤ k, r * r = k := by
  constructor
  · intro h; exact ⟨k.sqrt, Nat.sqrt_le_self k, h⟩
  · rintro ⟨r, -, hr⟩
    have : Nat.sqrt k = r := by
      rw [← hr, Nat.sqrt_eq]
    rw [this, hr]

lemma a_eq_a₂ (n M : ℕ) (hM : n.sqrt + 1 = M) : a n = a₂ n M := by
  unfold a a₂
  subst hM
  apply Finset.sum_congr rfl
  intro p _
  simp only [is_sq_iff]

set_option maxRecDepth 100000 in
example : a₂ 3 2 = 0 := by decide

set_option maxRecDepth 100000 in
example : a₂ 10 4 = 0 := by decide

set_option maxRecDepth 1000000 in
example : a₂ 60 8 = 1 := by decide


/-- nested-sum variant -/
def a₃ (n M : ℕ) : ℕ :=
  (range M).sum fun w => (range M).sum fun x => (range M).sum fun y => (range M).sum fun z =>
    if 2 * w^2 + x^2 + y^2 + z^2 = n ∧
        ∃ r ≤ w + x + 2 * y + 4 * z, r * r = w + x + 2 * y + 4 * z then 1 else 0

lemma a₂_eq_a₃ (n M : ℕ) : a₂ n M = a₃ n M := by
  unfold a₂ a₃
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.product_eq_sprod, Finset.sum_product]

lemma a_eq_a₃ (n M : ℕ) (hM : n.sqrt + 1 = M) : a n = a₃ n M := by
  rw [a_eq_a₂ n M hM, a₂_eq_a₃]

lemma a_val_0 : a 0 = 1 := by
  rw [a_eq_a₃ 0 1 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 0 = Nat.sqrt 0)])]
  decide

lemma a_val_1 : a 1 = 2 := by
  rw [a_eq_a₃ 1 2 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 1 = Nat.sqrt 1)])]
  decide

lemma a_val_2 : a 2 = 1 := by
  rw [a_eq_a₃ 2 2 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 1 = Nat.sqrt 2)])]
  decide

lemma a_val_3 : a 3 = 0 := by
  rw [a_eq_a₃ 3 2 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 1 = Nat.sqrt 3)])]
  decide

lemma a_val_4 : a 4 = 2 := by
  rw [a_eq_a₃ 4 3 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 2 = Nat.sqrt 4)])]
  decide

lemma a_val_5 : a 5 = 2 := by
  rw [a_eq_a₃ 5 3 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 2 = Nat.sqrt 5)])]
  decide

lemma a_val_6 : a 6 = 2 := by
  rw [a_eq_a₃ 6 3 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 2 = Nat.sqrt 6)])]
  decide

lemma a_val_7 : a 7 = 1 := by
  rw [a_eq_a₃ 7 3 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 2 = Nat.sqrt 7)])]
  decide

lemma a_val_8 : a 8 = 1 := by
  rw [a_eq_a₃ 8 3 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 2 = Nat.sqrt 8)])]
  decide

lemma a_val_9 : a 9 = 1 := by
  rw [a_eq_a₃ 9 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 9)])]
  decide

lemma a_val_10 : a 10 = 0 := by
  rw [a_eq_a₃ 10 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 10)])]
  decide

lemma a_val_11 : a 11 = 3 := by
  rw [a_eq_a₃ 11 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 11)])]
  decide

lemma a_val_12 : a 12 = 1 := by
  rw [a_eq_a₃ 12 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 12)])]
  decide

lemma a_val_13 : a 13 = 2 := by
  rw [a_eq_a₃ 13 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 13)])]
  decide

lemma a_val_14 : a 14 = 1 := by
  rw [a_eq_a₃ 14 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 14)])]
  decide

lemma a_val_15 : a 15 = 1 := by
  rw [a_eq_a₃ 15 4 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 3 = Nat.sqrt 15)])]
  decide

lemma a_val_16 : a 16 = 3 := by
  rw [a_eq_a₃ 16 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 16)])]
  decide

lemma a_val_17 : a 17 = 2 := by
  rw [a_eq_a₃ 17 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 17)])]
  decide

lemma a_val_18 : a 18 = 5 := by
  rw [a_eq_a₃ 18 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 18)])]
  decide

lemma a_val_19 : a 19 = 3 := by
  rw [a_eq_a₃ 19 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 19)])]
  decide

lemma a_val_20 : a 20 = 4 := by
  rw [a_eq_a₃ 20 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 20)])]
  decide

lemma a_val_21 : a 21 = 3 := by
  rw [a_eq_a₃ 21 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 21)])]
  decide

lemma a_val_22 : a 22 = 1 := by
  rw [a_eq_a₃ 22 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 22)])]
  decide

lemma a_val_23 : a 23 = 1 := by
  rw [a_eq_a₃ 23 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 23)])]
  decide

lemma a_val_24 : a 24 = 1 := by
  rw [a_eq_a₃ 24 5 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 4 = Nat.sqrt 24)])]
  decide

lemma a_val_25 : a 25 = 1 := by
  rw [a_eq_a₃ 25 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 25)])]
  decide

lemma a_val_26 : a 26 = 2 := by
  rw [a_eq_a₃ 26 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 26)])]
  decide

lemma a_val_27 : a 27 = 2 := by
  rw [a_eq_a₃ 27 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 27)])]
  decide

lemma a_val_28 : a 28 = 2 := by
  rw [a_eq_a₃ 28 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 28)])]
  decide

lemma a_val_29 : a 29 = 4 := by
  rw [a_eq_a₃ 29 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 29)])]
  decide

lemma a_val_30 : a 30 = 2 := by
  rw [a_eq_a₃ 30 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 30)])]
  decide

lemma a_val_31 : a 31 = 2 := by
  rw [a_eq_a₃ 31 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 31)])]
  decide

lemma a_val_32 : a 32 = 4 := by
  rw [a_eq_a₃ 32 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 32)])]
  decide

lemma a_val_33 : a 33 = 2 := by
  rw [a_eq_a₃ 33 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 33)])]
  decide

lemma a_val_34 : a 34 = 7 := by
  rw [a_eq_a₃ 34 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 34)])]
  decide

lemma a_val_35 : a 35 = 3 := by
  rw [a_eq_a₃ 35 6 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 5 = Nat.sqrt 35)])]
  decide

lemma a_val_36 : a 36 = 1 := by
  rw [a_eq_a₃ 36 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 36)])]
  decide

lemma a_val_37 : a 37 = 6 := by
  rw [a_eq_a₃ 37 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 37)])]
  decide

lemma a_val_38 : a 38 = 2 := by
  rw [a_eq_a₃ 38 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 38)])]
  decide

lemma a_val_39 : a 39 = 1 := by
  rw [a_eq_a₃ 39 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 39)])]
  decide

lemma a_val_40 : a 40 = 2 := by
  rw [a_eq_a₃ 40 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 40)])]
  decide

lemma a_val_41 : a 41 = 3 := by
  rw [a_eq_a₃ 41 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 41)])]
  decide

lemma a_val_42 : a 42 = 4 := by
  rw [a_eq_a₃ 42 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 42)])]
  decide

lemma a_val_43 : a 43 = 5 := by
  rw [a_eq_a₃ 43 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 43)])]
  decide

lemma a_val_44 : a 44 = 1 := by
  rw [a_eq_a₃ 44 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 44)])]
  decide

lemma a_val_45 : a 45 = 1 := by
  rw [a_eq_a₃ 45 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 45)])]
  decide

lemma a_val_46 : a 46 = 3 := by
  rw [a_eq_a₃ 46 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 46)])]
  decide

lemma a_val_47 : a 47 = 5 := by
  rw [a_eq_a₃ 47 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 47)])]
  decide

lemma a_val_48 : a 48 = 3 := by
  rw [a_eq_a₃ 48 7 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 6 = Nat.sqrt 48)])]
  decide

lemma a_val_49 : a 49 = 3 := by
  rw [a_eq_a₃ 49 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 49)])]
  decide

lemma a_val_50 : a 50 = 4 := by
  rw [a_eq_a₃ 50 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 50)])]
  decide

lemma a_val_51 : a 51 = 3 := by
  rw [a_eq_a₃ 51 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 51)])]
  decide

lemma a_val_52 : a 52 = 7 := by
  rw [a_eq_a₃ 52 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 52)])]
  decide

lemma a_val_53 : a 53 = 3 := by
  rw [a_eq_a₃ 53 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 53)])]
  decide

lemma a_val_54 : a 54 = 2 := by
  rw [a_eq_a₃ 54 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 54)])]
  decide

lemma a_val_55 : a 55 = 4 := by
  rw [a_eq_a₃ 55 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 55)])]
  decide

lemma a_val_56 : a 56 = 3 := by
  rw [a_eq_a₃ 56 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 56)])]
  decide

lemma a_val_57 : a 57 = 4 := by
  rw [a_eq_a₃ 57 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 57)])]
  decide

lemma a_val_58 : a 58 = 4 := by
  rw [a_eq_a₃ 58 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 58)])]
  decide

lemma a_val_59 : a 59 = 3 := by
  rw [a_eq_a₃ 59 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 59)])]
  decide

lemma a_val_60 : a 60 = 1 := by
  rw [a_eq_a₃ 60 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 60)])]
  decide

lemma a_val_61 : a 61 = 4 := by
  rw [a_eq_a₃ 61 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 61)])]
  decide

lemma a_val_62 : a 62 = 5 := by
  rw [a_eq_a₃ 62 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 62)])]
  decide

lemma a_val_63 : a 63 = 3 := by
  rw [a_eq_a₃ 63 8 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 7 = Nat.sqrt 63)])]
  decide

lemma a_val_64 : a 64 = 6 := by
  rw [a_eq_a₃ 64 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 64)])]
  decide

lemma a_val_65 : a 65 = 4 := by
  rw [a_eq_a₃ 65 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 65)])]
  decide

lemma a_val_66 : a 66 = 4 := by
  rw [a_eq_a₃ 66 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 66)])]
  decide

lemma a_val_67 : a 67 = 4 := by
  rw [a_eq_a₃ 67 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 67)])]
  decide

lemma a_val_68 : a 68 = 5 := by
  rw [a_eq_a₃ 68 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 68)])]
  decide

lemma a_val_69 : a 69 = 7 := by
  rw [a_eq_a₃ 69 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 69)])]
  decide

lemma a_val_70 : a 70 = 7 := by
  rw [a_eq_a₃ 70 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 70)])]
  decide

lemma a_val_71 : a 71 = 3 := by
  rw [a_eq_a₃ 71 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 71)])]
  decide

lemma a_val_72 : a 72 = 6 := by
  rw [a_eq_a₃ 72 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 72)])]
  decide

lemma a_val_73 : a 73 = 5 := by
  rw [a_eq_a₃ 73 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 73)])]
  decide

lemma a_val_74 : a 74 = 5 := by
  rw [a_eq_a₃ 74 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 74)])]
  decide

lemma a_val_75 : a 75 = 4 := by
  rw [a_eq_a₃ 75 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 75)])]
  decide

lemma a_val_76 : a 76 = 3 := by
  rw [a_eq_a₃ 76 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 76)])]
  decide

lemma a_val_77 : a 77 = 11 := by
  rw [a_eq_a₃ 77 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 77)])]
  decide

lemma a_val_78 : a 78 = 2 := by
  rw [a_eq_a₃ 78 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 78)])]
  decide

lemma a_val_79 : a 79 = 2 := by
  rw [a_eq_a₃ 79 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 79)])]
  decide

lemma a_val_80 : a 80 = 4 := by
  rw [a_eq_a₃ 80 9 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 8 = Nat.sqrt 80)])]
  decide

lemma a_val_81 : a 81 = 7 := by
  rw [a_eq_a₃ 81 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 81)])]
  decide

lemma a_val_82 : a 82 = 5 := by
  rw [a_eq_a₃ 82 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 82)])]
  decide

lemma a_val_83 : a 83 = 5 := by
  rw [a_eq_a₃ 83 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 83)])]
  decide

lemma a_val_84 : a 84 = 5 := by
  rw [a_eq_a₃ 84 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 84)])]
  decide

lemma a_val_85 : a 85 = 3 := by
  rw [a_eq_a₃ 85 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 85)])]
  decide

lemma a_val_86 : a 86 = 6 := by
  rw [a_eq_a₃ 86 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 86)])]
  decide

lemma a_val_87 : a 87 = 1 := by
  rw [a_eq_a₃ 87 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 87)])]
  decide

lemma a_val_88 : a 88 = 3 := by
  rw [a_eq_a₃ 88 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 88)])]
  decide

lemma a_val_89 : a 89 = 3 := by
  rw [a_eq_a₃ 89 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 89)])]
  decide

lemma a_val_90 : a 90 = 4 := by
  rw [a_eq_a₃ 90 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 90)])]
  decide

lemma a_val_91 : a 91 = 8 := by
  rw [a_eq_a₃ 91 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 91)])]
  decide

lemma a_val_92 : a 92 = 8 := by
  rw [a_eq_a₃ 92 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 92)])]
  decide

lemma a_val_93 : a 93 = 2 := by
  rw [a_eq_a₃ 93 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 93)])]
  decide

lemma a_val_94 : a 94 = 5 := by
  rw [a_eq_a₃ 94 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 94)])]
  decide

lemma a_val_95 : a 95 = 2 := by
  rw [a_eq_a₃ 95 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 95)])]
  decide

lemma a_val_96 : a 96 = 5 := by
  rw [a_eq_a₃ 96 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 96)])]
  decide

lemma a_val_97 : a 97 = 6 := by
  rw [a_eq_a₃ 97 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 97)])]
  decide

lemma a_val_98 : a 98 = 1 := by
  rw [a_eq_a₃ 98 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 98)])]
  decide

lemma a_val_99 : a 99 = 6 := by
  rw [a_eq_a₃ 99 10 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 9 = Nat.sqrt 99)])]
  decide

lemma a_val_100 : a 100 = 8 := by
  rw [a_eq_a₃ 100 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 100)])]
  decide

lemma a_val_101 : a 101 = 8 := by
  rw [a_eq_a₃ 101 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 101)])]
  decide

lemma a_val_102 : a 102 = 6 := by
  rw [a_eq_a₃ 102 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 102)])]
  decide

lemma a_val_103 : a 103 = 7 := by
  rw [a_eq_a₃ 103 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 103)])]
  decide

lemma a_val_104 : a 104 = 4 := by
  rw [a_eq_a₃ 104 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 104)])]
  decide

lemma a_val_105 : a 105 = 3 := by
  rw [a_eq_a₃ 105 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 105)])]
  decide

lemma a_val_106 : a 106 = 1 := by
  rw [a_eq_a₃ 106 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 106)])]
  decide

lemma a_val_107 : a 107 = 2 := by
  rw [a_eq_a₃ 107 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 107)])]
  decide

lemma a_val_108 : a 108 = 3 := by
  rw [a_eq_a₃ 108 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 108)])]
  decide

lemma a_val_109 : a 109 = 7 := by
  rw [a_eq_a₃ 109 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 109)])]
  decide

lemma a_val_110 : a 110 = 1 := by
  rw [a_eq_a₃ 110 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 110)])]
  decide

lemma a_val_111 : a 111 = 1 := by
  rw [a_eq_a₃ 111 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 111)])]
  decide

lemma a_val_112 : a 112 = 7 := by
  rw [a_eq_a₃ 112 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 112)])]
  decide

lemma a_val_113 : a 113 = 2 := by
  rw [a_eq_a₃ 113 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 113)])]
  decide

lemma a_val_114 : a 114 = 3 := by
  rw [a_eq_a₃ 114 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 114)])]
  decide

lemma a_val_115 : a 115 = 11 := by
  rw [a_eq_a₃ 115 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 115)])]
  decide

lemma a_val_116 : a 116 = 8 := by
  rw [a_eq_a₃ 116 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 116)])]
  decide

lemma a_val_117 : a 117 = 9 := by
  rw [a_eq_a₃ 117 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 117)])]
  decide

lemma a_val_118 : a 118 = 10 := by
  rw [a_eq_a₃ 118 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 118)])]
  decide

lemma a_val_119 : a 119 = 4 := by
  rw [a_eq_a₃ 119 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 119)])]
  decide

lemma a_val_120 : a 120 = 2 := by
  rw [a_eq_a₃ 120 11 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 10 = Nat.sqrt 120)])]
  decide

lemma a_val_121 : a 121 = 6 := by
  rw [a_eq_a₃ 121 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 121)])]
  decide

lemma a_val_122 : a 122 = 14 := by
  rw [a_eq_a₃ 122 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 122)])]
  decide

lemma a_val_123 : a 123 = 5 := by
  rw [a_eq_a₃ 123 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 123)])]
  decide

lemma a_val_124 : a 124 = 7 := by
  rw [a_eq_a₃ 124 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 124)])]
  decide

lemma a_val_125 : a 125 = 7 := by
  rw [a_eq_a₃ 125 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 125)])]
  decide

lemma a_val_126 : a 126 = 6 := by
  rw [a_eq_a₃ 126 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 126)])]
  decide

lemma a_val_127 : a 127 = 9 := by
  rw [a_eq_a₃ 127 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 127)])]
  decide

lemma a_val_128 : a 128 = 8 := by
  rw [a_eq_a₃ 128 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 128)])]
  decide

lemma a_val_129 : a 129 = 5 := by
  rw [a_eq_a₃ 129 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 129)])]
  decide

lemma a_val_130 : a 130 = 13 := by
  rw [a_eq_a₃ 130 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 130)])]
  decide

lemma a_val_131 : a 131 = 11 := by
  rw [a_eq_a₃ 131 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 131)])]
  decide

lemma a_val_132 : a 132 = 5 := by
  rw [a_eq_a₃ 132 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 132)])]
  decide

lemma a_val_133 : a 133 = 6 := by
  rw [a_eq_a₃ 133 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 133)])]
  decide

lemma a_val_134 : a 134 = 6 := by
  rw [a_eq_a₃ 134 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 134)])]
  decide

lemma a_val_135 : a 135 = 7 := by
  rw [a_eq_a₃ 135 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 135)])]
  decide

lemma a_val_136 : a 136 = 2 := by
  rw [a_eq_a₃ 136 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 136)])]
  decide

lemma a_val_137 : a 137 = 10 := by
  rw [a_eq_a₃ 137 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 137)])]
  decide

lemma a_val_138 : a 138 = 7 := by
  rw [a_eq_a₃ 138 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 138)])]
  decide

lemma a_val_139 : a 139 = 11 := by
  rw [a_eq_a₃ 139 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 139)])]
  decide

lemma a_val_140 : a 140 = 6 := by
  rw [a_eq_a₃ 140 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 140)])]
  decide

lemma a_val_141 : a 141 = 7 := by
  rw [a_eq_a₃ 141 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 141)])]
  decide

lemma a_val_142 : a 142 = 7 := by
  rw [a_eq_a₃ 142 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 142)])]
  decide

lemma a_val_143 : a 143 = 3 := by
  rw [a_eq_a₃ 143 12 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 11 = Nat.sqrt 143)])]
  decide

lemma a_val_144 : a 144 = 7 := by
  rw [a_eq_a₃ 144 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 144)])]
  decide

lemma a_val_145 : a 145 = 7 := by
  rw [a_eq_a₃ 145 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 145)])]
  decide

lemma a_val_146 : a 146 = 9 := by
  rw [a_eq_a₃ 146 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 146)])]
  decide

lemma a_val_147 : a 147 = 5 := by
  rw [a_eq_a₃ 147 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 147)])]
  decide

lemma a_val_148 : a 148 = 8 := by
  rw [a_eq_a₃ 148 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 148)])]
  decide

lemma a_val_149 : a 149 = 4 := by
  rw [a_eq_a₃ 149 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 149)])]
  decide

lemma a_val_150 : a 150 = 7 := by
  rw [a_eq_a₃ 150 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 150)])]
  decide

lemma a_val_151 : a 151 = 9 := by
  rw [a_eq_a₃ 151 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 151)])]
  decide

lemma a_val_152 : a 152 = 7 := by
  rw [a_eq_a₃ 152 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 152)])]
  decide

lemma a_val_153 : a 153 = 6 := by
  rw [a_eq_a₃ 153 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 153)])]
  decide

lemma a_val_154 : a 154 = 9 := by
  rw [a_eq_a₃ 154 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 154)])]
  decide

lemma a_val_155 : a 155 = 9 := by
  rw [a_eq_a₃ 155 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 155)])]
  decide

lemma a_val_156 : a 156 = 2 := by
  rw [a_eq_a₃ 156 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 156)])]
  decide

lemma a_val_157 : a 157 = 8 := by
  rw [a_eq_a₃ 157 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 157)])]
  decide

lemma a_val_158 : a 158 = 6 := by
  rw [a_eq_a₃ 158 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 158)])]
  decide

lemma a_val_159 : a 159 = 4 := by
  rw [a_eq_a₃ 159 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 159)])]
  decide

lemma a_val_160 : a 160 = 4 := by
  rw [a_eq_a₃ 160 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 160)])]
  decide

lemma a_val_161 : a 161 = 7 := by
  rw [a_eq_a₃ 161 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 161)])]
  decide

lemma a_val_162 : a 162 = 6 := by
  rw [a_eq_a₃ 162 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 162)])]
  decide

lemma a_val_163 : a 163 = 11 := by
  rw [a_eq_a₃ 163 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 163)])]
  decide

lemma a_val_164 : a 164 = 4 := by
  rw [a_eq_a₃ 164 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 164)])]
  decide

lemma a_val_165 : a 165 = 6 := by
  rw [a_eq_a₃ 165 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 165)])]
  decide

lemma a_val_166 : a 166 = 16 := by
  rw [a_eq_a₃ 166 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 166)])]
  decide

lemma a_val_167 : a 167 = 6 := by
  rw [a_eq_a₃ 167 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 167)])]
  decide

lemma a_val_168 : a 168 = 6 := by
  rw [a_eq_a₃ 168 13 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 12 = Nat.sqrt 168)])]
  decide

lemma a_val_169 : a 169 = 3 := by
  rw [a_eq_a₃ 169 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 169)])]
  decide

lemma a_val_170 : a 170 = 5 := by
  rw [a_eq_a₃ 170 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 170)])]
  decide

lemma a_val_171 : a 171 = 7 := by
  rw [a_eq_a₃ 171 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 171)])]
  decide

lemma a_val_172 : a 172 = 8 := by
  rw [a_eq_a₃ 172 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 172)])]
  decide

lemma a_val_173 : a 173 = 6 := by
  rw [a_eq_a₃ 173 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 173)])]
  decide

lemma a_val_174 : a 174 = 2 := by
  rw [a_eq_a₃ 174 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 174)])]
  decide

lemma a_val_175 : a 175 = 5 := by
  rw [a_eq_a₃ 175 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 175)])]
  decide

lemma a_val_176 : a 176 = 9 := by
  rw [a_eq_a₃ 176 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 176)])]
  decide

lemma a_val_177 : a 177 = 4 := by
  rw [a_eq_a₃ 177 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 177)])]
  decide

lemma a_val_178 : a 178 = 6 := by
  rw [a_eq_a₃ 178 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 178)])]
  decide

lemma a_val_179 : a 179 = 7 := by
  rw [a_eq_a₃ 179 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 179)])]
  decide

lemma a_val_180 : a 180 = 6 := by
  rw [a_eq_a₃ 180 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 180)])]
  decide

lemma a_val_181 : a 181 = 8 := by
  rw [a_eq_a₃ 181 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 181)])]
  decide

lemma a_val_182 : a 182 = 10 := by
  rw [a_eq_a₃ 182 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 182)])]
  decide

lemma a_val_183 : a 183 = 1 := by
  rw [a_eq_a₃ 183 14 (by rw [← (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩ : 13 = Nat.sqrt 183)])]
  decide

/-- The remaining (open) content of the conjecture: at least two representations for all `n ≥ 184`. -/
theorem key (n : ℕ) (hn : 184 ≤ n) : 2 ≤ a n := sorry

/--
Conjecture (i) from A275409:
a(n) > 0 except for n = 3, 10, and a(n) = 1 only for
n = 0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183.
-/
theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) :=
by
  have h : ∀ n, (a n > 0 ↔ n ∉ A275409_zero_set) ∧ (a n = 1 ↔ n ∈ A275409_one_set) := by
    intro n
    rcases Nat.lt_or_ge n 184 with hn | hn
    · interval_cases n <;> simp only [a_val_0, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33, a_val_34, a_val_35, a_val_36, a_val_37, a_val_38, a_val_39, a_val_40, a_val_41, a_val_42, a_val_43, a_val_44, a_val_45, a_val_46, a_val_47, a_val_48, a_val_49, a_val_50, a_val_51, a_val_52, a_val_53, a_val_54, a_val_55, a_val_56, a_val_57, a_val_58, a_val_59, a_val_60, a_val_61, a_val_62, a_val_63, a_val_64, a_val_65, a_val_66, a_val_67, a_val_68, a_val_69, a_val_70, a_val_71, a_val_72, a_val_73, a_val_74, a_val_75, a_val_76, a_val_77, a_val_78, a_val_79, a_val_80, a_val_81, a_val_82, a_val_83, a_val_84, a_val_85, a_val_86, a_val_87, a_val_88, a_val_89, a_val_90, a_val_91, a_val_92, a_val_93, a_val_94, a_val_95, a_val_96, a_val_97, a_val_98, a_val_99, a_val_100, a_val_101, a_val_102, a_val_103, a_val_104, a_val_105, a_val_106, a_val_107, a_val_108, a_val_109, a_val_110, a_val_111, a_val_112, a_val_113, a_val_114, a_val_115, a_val_116, a_val_117, a_val_118, a_val_119, a_val_120, a_val_121, a_val_122, a_val_123, a_val_124, a_val_125, a_val_126, a_val_127, a_val_128, a_val_129, a_val_130, a_val_131, a_val_132, a_val_133, a_val_134, a_val_135, a_val_136, a_val_137, a_val_138, a_val_139, a_val_140, a_val_141, a_val_142, a_val_143, a_val_144, a_val_145, a_val_146, a_val_147, a_val_148, a_val_149, a_val_150, a_val_151, a_val_152, a_val_153, a_val_154, a_val_155, a_val_156, a_val_157, a_val_158, a_val_159, a_val_160, a_val_161, a_val_162, a_val_163, a_val_164, a_val_165, a_val_166, a_val_167, a_val_168, a_val_169, a_val_170, a_val_171, a_val_172, a_val_173, a_val_174, a_val_175, a_val_176, a_val_177, a_val_178, a_val_179, a_val_180, a_val_181, a_val_182, a_val_183] <;> decide
    · have h2 := key n hn
      have h3 : n ∉ A275409_zero_set := by
        simp only [A275409_zero_set, Finset.mem_insert, Finset.mem_singleton]; omega
      have h4 : n ∉ A275409_one_set := by
        simp only [A275409_one_set, Finset.mem_insert, Finset.mem_singleton]; omega
      refine ⟨⟨fun _ => h3, fun _ => ?_⟩, ⟨fun h => ?_, fun h => absurd h h4⟩⟩
      · exact Nat.lt_of_lt_of_le (by norm_num) h2
      · rw [h] at h2; norm_num at h2
  exact ⟨fun n => (h n).1, fun n => (h n).2⟩

theorem oeis_275409_conjecture_0.disproof : ¬ (type_of% @oeis_275409_conjecture_0) := sorry
