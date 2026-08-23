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
  let R : Finset ℕ := Finset.range M

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

/- Computable twin and basic lemmas. -/

def isSqB (k : ℕ) : Bool := k.sqrt * k.sqrt == k

def IsRep (n w x y z : ℕ) : Prop :=
  2 * w * w + x * x + y * y + z * z = n ∧
    (w + x + 2 * y + 4 * z).sqrt * (w + x + 2 * y + 4 * z).sqrt =
      w + x + 2 * y + 4 * z

instance (n w x y z : ℕ) : Decidable (IsRep n w x y z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Kernel-reducible counter. -/
def aList (n : ℕ) : ℕ :=
  let M := n.sqrt + 1
  let R := List.range M
  (R.product (R.product (R.product R))).countP fun p =>
    2 * p.1 * p.1 + p.2.1 * p.2.1 + p.2.2.1 * p.2.2.1 + p.2.2.2 * p.2.2.2 == n &&
      isSqB (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2)

lemma sq_le_w {n w x y z : ℕ} (h : 2 * w * w + x * x + y * y + z * z = n) :
    w * w ≤ n := by nlinarith

lemma sq_le_x {n w x y z : ℕ} (h : 2 * w * w + x * x + y * y + z * z = n) :
    x * x ≤ n := by nlinarith

lemma sq_le_y {n w x y z : ℕ} (h : 2 * w * w + x * x + y * y + z * z = n) :
    y * y ≤ n := by nlinarith

lemma sq_le_z {n w x y z : ℕ} (h : 2 * w * w + x * x + y * y + z * z = n) :
    z * z ≤ n := by nlinarith

lemma IsRep.lt_succ_sqrt {n w x y z : ℕ} (h : IsRep n w x y z) :
    w < n.sqrt + 1 ∧ x < n.sqrt + 1 ∧ y < n.sqrt + 1 ∧ z < n.sqrt + 1 := by
  obtain ⟨hQ, _⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr (sq_le_w hQ))
  · exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr (sq_le_x hQ))
  · exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr (sq_le_y hQ))
  · exact Nat.lt_succ_of_le (Nat.le_sqrt.mpr (sq_le_z hQ))

lemma a_eq_filter_card (n : ℕ) :
    a n = ((range (n.sqrt + 1)).product
        ((range (n.sqrt + 1)).product
          ((range (n.sqrt + 1)).product (range (n.sqrt + 1))))
        |>.filter (fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
          IsRep n p.1 p.2.1 p.2.2.1 p.2.2.2)).card := by
  unfold a
  simp only [pow_two, sum_boole]
  set S := (range (n.sqrt + 1)).product
      ((range (n.sqrt + 1)).product
        ((range (n.sqrt + 1)).product (range (n.sqrt + 1))))
  change (S.filter (fun p =>
      2 * (p.1 * p.1) + p.2.1 * p.2.1 + p.2.2.1 * p.2.2.1 + p.2.2.2 * p.2.2.2 = n ∧
        (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt *
          (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2).sqrt =
            p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2)).card =
    (S.filter (fun p => IsRep n p.1 p.2.1 p.2.2.1 p.2.2.2)).card
  congr 1
  ext p
  simp only [mem_filter, IsRep]
  have hmul : ∀ w : ℕ, 2 * (w * w) = 2 * w * w := by intro; ring
  constructor
  · intro ⟨hp, hQ, hL⟩
    exact ⟨hp, hmul p.1 ▸ hQ, hL⟩
  · intro ⟨hp, hQ, hL⟩
    exact ⟨hp, hmul p.1 ▸ hQ, hL⟩

lemma toFinset_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l₁ : List α) (l₂ : List β) :
    (l₁.product l₂).toFinset = l₁.toFinset.product l₂.toFinset := by
  ext ⟨a, b⟩
  simp [Finset.mem_product]

lemma aList_eq_filter_card (n : ℕ) :
    aList n =
      ((range (n.sqrt + 1)).product
        ((range (n.sqrt + 1)).product
          ((range (n.sqrt + 1)).product (range (n.sqrt + 1))))
        |>.filter (fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
          IsRep n p.1 p.2.1 p.2.2.1 p.2.2.2)).card := by
  unfold aList
  set M := n.sqrt + 1
  set RL := List.range M
  set RF := Finset.range M
  have hR : RL.toFinset = RF := List.toFinset_range M
  have hdup : (RL.product (RL.product (RL.product RL))).Nodup := by
    refine List.Nodup.product ?_ ?_
    · exact List.nodup_range
    · refine List.Nodup.product ?_ ?_
      · exact List.nodup_range
      · refine List.Nodup.product ?_ ?_ <;> exact List.nodup_range
  rw [List.countP_eq_length_filter]
  set Lprod := RL.product (RL.product (RL.product RL))
  have hdupf : (Lprod.filter (fun p =>
      2 * p.1 * p.1 + p.2.1 * p.2.1 + p.2.2.1 * p.2.2.1 + p.2.2.2 * p.2.2.2 == n &&
        isSqB (p.1 + p.2.1 + 2 * p.2.2.1 + 4 * p.2.2.2))).Nodup :=
    List.Nodup.filter _ hdup
  rw [← List.toFinset_card_of_nodup hdupf, List.toFinset_filter]
  have hprod : Lprod.toFinset = RF.product (RF.product (RF.product RF)) := by
    simp only [Lprod, toFinset_product, hR]
  rw [hprod]
  congr 1
  ext p
  simp [isSqB, IsRep, beq_iff_eq, Bool.and_eq_true]

lemma aList_eq_a (n : ℕ) : aList n = a n := by
  rw [aList_eq_filter_card, a_eq_filter_card]

lemma a_ge_two_of_two_IsRep {n w₁ x₁ y₁ z₁ w₂ x₂ y₂ z₂ : ℕ}
    (h₁ : IsRep n w₁ x₁ y₁ z₁) (h₂ : IsRep n w₂ x₂ y₂ z₂)
    (hne : (w₁, x₁, y₁, z₁) ≠ (w₂, x₂, y₂, z₂)) : 2 ≤ a n := by
  rw [a_eq_filter_card]
  set R := Finset.range (n.sqrt + 1)
  set S := (R.product (R.product (R.product R))).filter
    fun p => IsRep n p.1 p.2.1 p.2.2.1 p.2.2.2
  have hp1 : (w₁, (x₁, (y₁, z₁))) ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, h₁⟩
    simp [Finset.mem_product, R, Finset.mem_range]
    have := h₁.lt_succ_sqrt
    omega
  have hp2 : (w₂, (x₂, (y₂, z₂))) ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, h₂⟩
    simp [Finset.mem_product, R, Finset.mem_range]
    have := h₂.lt_succ_sqrt
    omega
  have hne' : (w₁, (x₁, (y₁, z₁))) ≠ (w₂, (x₂, (y₂, z₂))) := by
    intro eq
    apply hne
    injection eq with h_w eq2
    injection eq2 with h_x eq3
    injection eq3 with h_y h_z
    simp [h_w, h_x, h_y, h_z]
  have hcard : ({(w₁, (x₁, (y₁, z₁))), (w₂, (x₂, (y₂, z₂)))} : Finset _).card = 2 := by
    simp [hne']
  have hsub : ({(w₁, (x₁, (y₁, z₁))), (w₂, (x₂, (y₂, z₂)))} : Finset _) ⊆ S := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  exact hcard.symm.trans_le (Finset.card_le_card hsub)

lemma IsRep.of_mul_eq {n w x y z k : ℕ}
    (hQ : 2 * w * w + x * x + y * y + z * z = n)
    (hL : w + x + 2 * y + 4 * z = k * k) : IsRep n w x y z := by
  refine ⟨hQ, ?_⟩
  have : (w + x + 2 * y + 4 * z).sqrt = k := by
    rw [hL]
    simpa [pow_two] using (Nat.sqrt_eq' k).symm
  simp [hL]

lemma IsRep.fourth_power_fst (u : ℕ) : IsRep (u ^ 4) 0 (u ^ 2) 0 0 := by
  refine IsRep.of_mul_eq ?_ (k := u) ?_
  · ring
  · ring

lemma IsRep.fourth_power_snd (u : ℕ) : IsRep (u ^ 4) 0 0 0 (u ^ 2) := by
  refine IsRep.of_mul_eq ?_ (k := 2 * u) ?_
  · ring
  · ring

lemma a_ge_two_of_fourth_power {n u : ℕ} (h : n = u ^ 4) (hu : 1 ≤ u) : 2 ≤ a n := by
  have h1 : IsRep n 0 (u ^ 2) 0 0 := by simpa [h] using IsRep.fourth_power_fst u
  have h2 : IsRep n 0 0 0 (u ^ 2) := by simpa [h] using IsRep.fourth_power_snd u
  have hne : (0, u ^ 2, 0, 0) ≠ (0, 0, 0, u ^ 2) := by
    intro eq
    have : u ^ 2 = 0 := by
      simpa using congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.2.1) eq
    have : u = 0 := (Nat.pow_eq_zero.mp this).1
    omega
  exact a_ge_two_of_two_IsRep h1 h2 hne


/- G-form reconstruction: G(a,b,c) = 43Q - 2L^2 after the change
   a = x-2w, b = y-4w, c = z-8w. -/

def G (a b c : ℤ) : ℤ :=
  41 * a * a - 8 * a * b - 16 * a * c + 35 * b * b - 32 * b * c + 11 * c * c

lemma G_eq_43Q_sub_2Lsq (w x y z : ℤ) :
    G (x - 2 * w) (y - 4 * w) (z - 8 * w) =
      43 * (2 * w * w + x * x + y * y + z * z) -
        2 * (w + x + 2 * y + 4 * z) * (w + x + 2 * y + 4 * z) := by
  unfold G
  ring

lemma recover_Q_L (w x y z : ℤ) (a b c : ℤ)
    (ha : a = x - 2 * w) (hb : b = y - 4 * w) (hc : c = z - 8 * w) :
    G a b c =
      43 * (2 * w * w + x * x + y * y + z * z) -
        2 * (w + x + 2 * y + 4 * z) * (w + x + 2 * y + 4 * z) := by
  simpa [ha, hb, hc] using G_eq_43Q_sub_2Lsq w x y z

lemma isRep_of_G (n : ℕ) (k : ℕ) (a b c : ℤ) (w : ℤ)
    (hG : G a b c = 43 * n - 2 * (k : ℤ) ^ 4)
    (hw : (k : ℤ) ^ 2 = 43 * w + a + 2 * b + 4 * c)
    (x y z : ℤ) (hx : x = a + 2 * w) (hy : y = b + 4 * w) (hz : z = c + 8 * w)
    (_hw0 : 0 ≤ w) (_hx0 : 0 ≤ x) (_hy0 : 0 ≤ y) (_hz0 : 0 ≤ z) :
    2 * w * w + x * x + y * y + z * z = (n : ℤ) ∧
      w + x + 2 * y + 4 * z = (k : ℤ) ^ 2 := by
  have hx' : a = x - 2 * w := by linarith [hx]
  have hy' : b = y - 4 * w := by linarith [hy]
  have hz' : c = z - 8 * w := by linarith [hz]
  have hQL := recover_Q_L w x y z a b c hx' hy' hz'
  have hL : w + x + 2 * y + 4 * z = (k : ℤ) ^ 2 := by
    have : w + x + 2 * y + 4 * z = 43 * w + a + 2 * b + 4 * c := by
      simp [hx, hy, hz]; ring
    linarith [hw]
  have hQ'' : 2 * w * w + x * x + y * y + z * z = (n : ℤ) := by
    have h1 : G a b c =
        43 * (2 * w * w + x * x + y * y + z * z) - 2 * (k : ℤ) ^ 4 := by
      calc
        G a b c = 43 * (2 * w * w + x * x + y * y + z * z) -
            2 * (w + x + 2 * y + 4 * z) * (w + x + 2 * y + 4 * z) := hQL
        _ = 43 * (2 * w * w + x * x + y * y + z * z) -
            2 * ((k : ℤ) ^ 2) * ((k : ℤ) ^ 2) := by rw [hL]
        _ = 43 * (2 * w * w + x * x + y * y + z * z) - 2 * (k : ℤ) ^ 4 := by ring
    have h2 : 43 * (2 * w * w + x * x + y * y + z * z) - 2 * (k : ℤ) ^ 4 =
        43 * (n : ℤ) - 2 * (k : ℤ) ^ 4 := by
      rw [← h1, hG]
    have h3 : 43 * (2 * w * w + x * x + y * y + z * z) = 43 * (n : ℤ) := by
      linarith [h2]
    have : (43 : ℤ) ≠ 0 := by decide
    exact mul_left_cancel₀ this h3
  exact ⟨hQ'', hL⟩

lemma IsRep.of_G_nat (n k : ℕ) (a b c : ℤ) (w x y z : ℕ)
    (hG : G a b c = 43 * (n : ℤ) - 2 * (k : ℤ) ^ 4)
    (hw : (k : ℤ) ^ 2 = 43 * (w : ℤ) + a + 2 * b + 4 * c)
    (hx : (x : ℤ) = a + 2 * (w : ℤ))
    (hy : (y : ℤ) = b + 4 * (w : ℤ))
    (hz : (z : ℤ) = c + 8 * (w : ℤ)) :
    IsRep n w x y z := by
  have h := isRep_of_G n k a b c (w : ℤ) hG hw (x : ℤ) (y : ℤ) (z : ℤ)
    hx hy hz (Nat.cast_nonneg w) (Nat.cast_nonneg x) (Nat.cast_nonneg y)
    (Nat.cast_nonneg z)
  apply IsRep.of_mul_eq (k := k)
  · exact_mod_cast h.1
  · have : (w + x + 2 * y + 4 * z : ℤ) = (k : ℤ) ^ 2 := h.2
    have hk : (k : ℤ) ^ 2 = (k * k : ℤ) := by ring
    exact_mod_cast this.trans hk

/-- Rational equivalence `G ∘ P = H`, written integrally via `4P`. -/
def Hform (r s t : ℤ) : ℤ := r * r + 43 * s * s + 43 * t * t

def P4r (r s t : ℤ) : ℤ := r + s + 2 * t
def P4s (r s t : ℤ) : ℤ := r + s + 10 * t
def P4t (r s t : ℤ) : ℤ := 2 * r + 10 * s + 16 * t

lemma G_of_P4 (r s t : ℤ) :
    G (P4r r s t) (P4s r s t) (P4t r s t) = 16 * Hform r s t := by
  unfold G Hform P4r P4s P4t
  ring

lemma G_of_P_of_mod4 (r s t : ℤ) (h : r + s + 2 * t ≡ 0 [ZMOD 4]) :
    let a := (r + s + 2 * t) / 4
    let b := (r + s + 10 * t) / 4
    let c := (2 * r + 10 * s + 16 * t) / 4
    G a b c = Hform r s t := by
  intro a b c
  have h4 : (4 : ℤ) ∣ r + s + 2 * t := (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq] using h)
  have h4b : (4 : ℤ) ∣ r + s + 10 * t := by
    have : r + s + 10 * t = (r + s + 2 * t) + 8 * t := by ring
    rw [this]
    exact dvd_add h4 ⟨2 * t, by ring⟩
  have h4c : (4 : ℤ) ∣ 2 * r + 10 * s + 16 * t := by
    -- 2r+10s+16t = 2(r+s+2t) + 8s + 12t
    have : 2 * r + 10 * s + 16 * t = 2 * (r + s + 2 * t) + 8 * s + 12 * t := by ring
    rw [this]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right h4 _) ⟨2 * s, by ring⟩) ⟨3 * t, by ring⟩
  have ha : P4r r s t = 4 * a := by
    simp [P4r, a, Int.mul_ediv_cancel' h4]
  have hb : P4s r s t = 4 * b := by
    simp [P4s, b, Int.mul_ediv_cancel' h4b]
  have hc : P4t r s t = 4 * c := by
    simp [P4t, c, Int.mul_ediv_cancel' h4c]
  have hG := G_of_P4 r s t
  have hscale : G (4 * a) (4 * b) (4 * c) = 16 * G a b c := by
    unfold G; ring
  rw [← ha, ← hb, ← hc] at hscale
  have : 16 * G a b c = 16 * Hform r s t := by
    rw [← hscale, hG]
  exact mul_left_cancel₀ (by decide : (16 : ℤ) ≠ 0) this

/-- Second rational embedding, denominator 7: covers `n ≡ 1,7 [MOD 8]`. -/
def P7r (r s t : ℤ) : ℤ := r + 2 * s + 10 * t
def P7s (r s t : ℤ) : ℤ := 2 * r - 10 * s + 13 * t
def P7t (r s t : ℤ) : ℤ := 2 * r - 17 * s + 34 * t

lemma G_of_P7 (r s t : ℤ) :
    G (P7r r s t) (P7s r s t) (P7t r s t) = 49 * Hform r s t := by
  unfold G Hform P7r P7s P7t
  ring

lemma G_of_P_of_mod7 (r s t : ℤ)
    (h1 : r + 2 * s + 10 * t ≡ 0 [ZMOD 7])
    (h2 : 2 * r - 10 * s + 13 * t ≡ 0 [ZMOD 7])
    (h3 : 2 * r - 17 * s + 34 * t ≡ 0 [ZMOD 7]) :
    let a := (r + 2 * s + 10 * t) / 7
    let b := (2 * r - 10 * s + 13 * t) / 7
    let c := (2 * r - 17 * s + 34 * t) / 7
    G a b c = Hform r s t := by
  intro a b c
  have ha7 : (7 : ℤ) ∣ r + 2 * s + 10 * t :=
    (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq] using h1)
  have hb7 : (7 : ℤ) ∣ 2 * r - 10 * s + 13 * t :=
    (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq] using h2)
  have hc7 : (7 : ℤ) ∣ 2 * r - 17 * s + 34 * t :=
    (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq] using h3)
  have ha : P7r r s t = 7 * a := by
    simp [P7r, a, Int.mul_ediv_cancel' ha7]
  have hb : P7s r s t = 7 * b := by
    simp [P7s, b, Int.mul_ediv_cancel' hb7]
  have hc : P7t r s t = 7 * c := by
    simp [P7t, c, Int.mul_ediv_cancel' hc7]
  have hG := G_of_P7 r s t
  have hscale : G (7 * a) (7 * b) (7 * c) = 49 * G a b c := by
    unfold G; ring
  rw [← ha, ← hb, ← hc] at hscale
  have : 49 * G a b c = 49 * Hform r s t := by
    rw [← hscale, hG]
  exact mul_left_cancel₀ (by decide : (49 : ℤ) ≠ 0) this

/-- If `H(r,s,t) = 43n-2k⁴` and the recovered coordinates are nonnegative
naturals satisfying the linear relation, we get an `IsRep`. -/
lemma IsRep.of_Hform (n k : ℕ) (r s t a b c : ℤ) (w x y z : ℕ)
    (hH : Hform r s t = 43 * (n : ℤ) - 2 * (k : ℤ) ^ 4)
    (hGeq : G a b c = Hform r s t)
    (hw : (k : ℤ) ^ 2 = 43 * (w : ℤ) + a + 2 * b + 4 * c)
    (hx : (x : ℤ) = a + 2 * (w : ℤ))
    (hy : (y : ℤ) = b + 4 * (w : ℤ))
    (hz : (z : ℤ) = c + 8 * (w : ℤ)) :
    IsRep n w x y z :=
  IsRep.of_G_nat n k a b c w x y z (hGeq.trans hH) hw hx hy hz

/-- Numerator identities for the `γ = 16` family `r = 16 k² - 43 λ`. -/
lemma params16_num_coords (k : ℕ) (lam s t : ℤ) :
    let r := 16 * (k : ℤ) ^ 2 - 43 * lam
    let a4 := r + s + 2 * t
    let b4 := r + s + 10 * t
    let c4 := 2 * r + 10 * s + 16 * t
    let w4 := -4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t
    let x4 := 8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t
    let y4 := lam - 3 * s + 2 * t
    let z2 := lam + s
    x4 = a4 + 2 * w4 ∧ y4 = b4 + 4 * w4 ∧ 2 * z2 = c4 + 8 * w4 := by
  intro r a4 b4 c4 w4 x4 y4 z2
  refine ⟨?_, ?_, ?_⟩ <;> simp only [r, a4, b4, c4, w4, x4, y4, z2] <;> ring

lemma params16_num_linear (k : ℕ) (lam s t : ℤ) :
    let r := 16 * (k : ℤ) ^ 2 - 43 * lam
    let a4 := r + s + 2 * t
    let b4 := r + s + 10 * t
    let c4 := 2 * r + 10 * s + 16 * t
    let w4 := -4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t
    4 * (k : ℤ) ^ 2 = 43 * w4 + a4 + 2 * b4 + 4 * c4 := by
  intro r a4 b4 c4 w4
  simp only [r, a4, b4, c4, w4]
  ring

lemma params16_num_H (k : ℕ) (lam s t : ℤ) :
    let r := 16 * (k : ℤ) ^ 2 - 43 * lam
    Hform r s t = 43 *
      (6 * (k : ℤ) ^ 4 - 32 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2 + s * s + t * t)
      - 2 * (k : ℤ) ^ 4 := by
  intro r
  unfold Hform
  simp only [r]
  ring

/-- Recover an `IsRep` from `γ = 16` H-transfer data. -/
lemma IsRep.of_params16 (n k : ℕ) (lam s t : ℤ)
    (hM : (n : ℤ) = 6 * (k : ℤ) ^ 4 - 32 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2
      + s * s + t * t)
    (hdivw : (4 : ℤ) ∣ (-4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t))
    (hdivx : (4 : ℤ) ∣ (8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t))
    (hdivy : (4 : ℤ) ∣ (lam - 3 * s + 2 * t))
    (hdivz : (2 : ℤ) ∣ (lam + s))
    (hw0 : 0 ≤ (-4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t) / 4)
    (hx0 : 0 ≤ (8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t) / 4)
    (hy0 : 0 ≤ (lam - 3 * s + 2 * t) / 4)
    (hz0 : 0 ≤ (lam + s) / 2)
    (hmod : (16 * (k : ℤ) ^ 2 - 43 * lam + s + 2 * t) ≡ 0 [ZMOD 4]) :
    IsRep n
      (Int.toNat ((-4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t) / 4))
      (Int.toNat ((8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t) / 4))
      (Int.toNat ((lam - 3 * s + 2 * t) / 4))
      (Int.toNat ((lam + s) / 2)) := by
  set r := 16 * (k : ℤ) ^ 2 - 43 * lam
  set w4 := -4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t
  set x4 := 8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t
  set y4 := lam - 3 * s + 2 * t
  set z2 := lam + s
  set wZ := w4 / 4
  set xZ := x4 / 4
  set yZ := y4 / 4
  set zZ := z2 / 2
  set a := (r + s + 2 * t) / 4
  set b := (r + s + 10 * t) / 4
  set c := (2 * r + 10 * s + 16 * t) / 4
  have hG : G a b c = Hform r s t := by
    simpa [a, b, c, r] using G_of_P_of_mod4 r s t hmod
  have hH : Hform r s t = 43 * (n : ℤ) - 2 * (k : ℤ) ^ 4 := by
    have h1 := params16_num_H k lam s t
    simp only [r] at h1
    have h2 : (6 * (k : ℤ) ^ 4 - 32 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2 + s * s + t * t) = (n : ℤ) := by
      linarith [hM]
    simpa [h2] using h1
  have hw4eq : w4 = 4 * wZ := by
    simpa [wZ] using (Int.mul_ediv_cancel' hdivw).symm
  have hx4eq : x4 = 4 * xZ := by
    simpa [xZ] using (Int.mul_ediv_cancel' hdivx).symm
  have hy4eq : y4 = 4 * yZ := by
    simpa [yZ] using (Int.mul_ediv_cancel' hdivy).symm
  have hz2eq : z2 = 2 * zZ := by
    simpa [zZ] using (Int.mul_ediv_cancel' hdivz).symm
  have hcoords := params16_num_coords k lam s t
  have hxrel : xZ = a + 2 * wZ := by
    have : x4 = (r + s + 2 * t) + 2 * w4 := hcoords.1
    have ha4 : r + s + 2 * t = 4 * a := by
      have : (4 : ℤ) ∣ r + s + 2 * t :=
        (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq, r] using hmod)
      simpa [a] using (Int.mul_ediv_cancel' this).symm
    have : 4 * xZ = 4 * a + 2 * (4 * wZ) := by
      calc
        4 * xZ = x4 := hx4eq.symm
        _ = (r + s + 2 * t) + 2 * w4 := this
        _ = 4 * a + 2 * (4 * wZ) := by rw [ha4, hw4eq]
    linarith
  have hyrel : yZ = b + 4 * wZ := by
    have : y4 = (r + s + 10 * t) + 4 * w4 := hcoords.2.1
    have hb4 : r + s + 10 * t = 4 * b := by
      have h4 : (4 : ℤ) ∣ r + s + 2 * t :=
        (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq, r] using hmod)
      have : r + s + 10 * t = (r + s + 2 * t) + 8 * t := by ring
      have : (4 : ℤ) ∣ r + s + 10 * t := by
        rw [this]; exact dvd_add h4 ⟨2 * t, by ring⟩
      simpa [b] using (Int.mul_ediv_cancel' this).symm
    have : 4 * yZ = 4 * b + 4 * (4 * wZ) := by
      calc
        4 * yZ = y4 := hy4eq.symm
        _ = (r + s + 10 * t) + 4 * w4 := this
        _ = 4 * b + 4 * (4 * wZ) := by rw [hb4, hw4eq]
    linarith
  have hzrel : zZ = c + 8 * wZ := by
    have : 2 * z2 = (2 * r + 10 * s + 16 * t) + 8 * w4 := hcoords.2.2
    have hc4 : 2 * r + 10 * s + 16 * t = 4 * c := by
      have h4 : (4 : ℤ) ∣ r + s + 2 * t :=
        (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq, r] using hmod)
      have : 2 * r + 10 * s + 16 * t = 2 * (r + s + 2 * t) + 8 * s + 12 * t := by ring
      have : (4 : ℤ) ∣ 2 * r + 10 * s + 16 * t := by
        rw [this]
        exact dvd_add (dvd_add (dvd_mul_of_dvd_right h4 _) ⟨2 * s, by ring⟩) ⟨3 * t, by ring⟩
      simpa [c] using (Int.mul_ediv_cancel' this).symm
    have : 4 * zZ = 4 * c + 8 * (4 * wZ) := by
      have hL : 2 * (2 * zZ) = 4 * c + 8 * (4 * wZ) := by
        calc
          2 * (2 * zZ) = 2 * z2 := by rw [hz2eq]
          _ = (2 * r + 10 * s + 16 * t) + 8 * w4 := this
          _ = 4 * c + 8 * (4 * wZ) := by rw [hc4, hw4eq]
      linarith
    linarith
  have hlin := params16_num_linear k lam s t
  have hwrel : (k : ℤ) ^ 2 = 43 * wZ + a + 2 * b + 4 * c := by
    have : 4 * (k : ℤ) ^ 2 = 43 * w4 + (r + s + 2 * t) + 2 * (r + s + 10 * t)
        + 4 * (2 * r + 10 * s + 16 * t) := hlin
    have ha4 : r + s + 2 * t = 4 * a := by
      have : (4 : ℤ) ∣ r + s + 2 * t :=
        (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq, r] using hmod)
      simpa [a] using (Int.mul_ediv_cancel' this).symm
    have hb4 : r + s + 10 * t = 4 * b := by
      have h4 : (4 : ℤ) ∣ r + s + 2 * t :=
        (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq, r] using hmod)
      have : r + s + 10 * t = (r + s + 2 * t) + 8 * t := by ring
      have : (4 : ℤ) ∣ r + s + 10 * t := by
        rw [this]; exact dvd_add h4 ⟨2 * t, by ring⟩
      simpa [b] using (Int.mul_ediv_cancel' this).symm
    have hc4 : 2 * r + 10 * s + 16 * t = 4 * c := by
      have h4 : (4 : ℤ) ∣ r + s + 2 * t :=
        (Int.dvd_iff_emod_eq_zero).2 (by simpa [Int.ModEq, r] using hmod)
      have : 2 * r + 10 * s + 16 * t = 2 * (r + s + 2 * t) + 8 * s + 12 * t := by ring
      have : (4 : ℤ) ∣ 2 * r + 10 * s + 16 * t := by
        rw [this]
        exact dvd_add (dvd_add (dvd_mul_of_dvd_right h4 _) ⟨2 * s, by ring⟩) ⟨3 * t, by ring⟩
      simpa [c] using (Int.mul_ediv_cancel' this).symm
    have : 4 * (k : ℤ) ^ 2 = 43 * (4 * wZ) + 4 * a + 2 * (4 * b) + 4 * (4 * c) := by
      simpa [hw4eq, ha4, hb4, hc4] using this
    linarith
  have hwZ0 : 0 ≤ wZ := by simpa [wZ, w4] using hw0
  have hxZ0 : 0 ≤ xZ := by simpa [xZ, x4] using hx0
  have hyZ0 : 0 ≤ yZ := by simpa [yZ, y4] using hy0
  have hzZ0 : 0 ≤ zZ := by simpa [zZ, z2] using hz0
  have hwNat : ((Int.toNat wZ : ℤ) = wZ) := Int.toNat_of_nonneg hwZ0
  have hxNat : ((Int.toNat xZ : ℤ) = xZ) := Int.toNat_of_nonneg hxZ0
  have hyNat : ((Int.toNat yZ : ℤ) = yZ) := Int.toNat_of_nonneg hyZ0
  have hzNat : ((Int.toNat zZ : ℤ) = zZ) := Int.toNat_of_nonneg hzZ0
  refine IsRep.of_Hform n k r s t a b c
    (Int.toNat wZ) (Int.toNat xZ) (Int.toNat yZ) (Int.toNat zZ) hH hG ?_ ?_ ?_ ?_
  · rw [hwNat]; exact hwrel
  · rw [hxNat, hwNat]; exact hxrel
  · rw [hyNat, hwNat]; exact hyrel
  · rw [hzNat, hwNat]; exact hzrel

def zeroList : List ℕ := [3, 10]

def oneList : List ℕ :=
  [0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110,
   111, 183]

def inZero (n : ℕ) : Bool := zeroList.contains n

def inOne (n : ℕ) : Bool := oneList.contains n

lemma inZero_iff (n : ℕ) : inZero n = true ↔ n ∈ A275409_zero_set := by
  simp [inZero, zeroList, A275409_zero_set]

lemma inOne_iff (n : ℕ) : inOne n = true ↔ n ∈ A275409_one_set := by
  simp [inOne, oneList, A275409_one_set]

def checkWit : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Bool
  | (n, w1, x1, y1, z1, k1, w2, x2, y2, z2, k2) =>
      (2 * w1 * w1 + x1 * x1 + y1 * y1 + z1 * z1 == n) &&
      (w1 + x1 + 2 * y1 + 4 * z1 == k1 * k1) &&
      (2 * w2 * w2 + x2 * x2 + y2 * y2 + z2 * z2 == n) &&
      (w2 + x2 + 2 * y2 + 4 * z2 == k2 * k2) &&
      decide ((w1, x1, y1, z1) ≠ (w2, x2, y2, z2))

lemma checkWit_ge_two {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : checkWit t = true) : 2 ≤ a t.1 := by
  rcases t with ⟨n, w1, x1, y1, z1, k1, w2, x2, y2, z2, k2⟩
  simp only [checkWit, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hQ1, hL1⟩, hQ2⟩, hL2⟩, hne⟩
  exact a_ge_two_of_two_IsRep
    (IsRep.of_mul_eq (k := k1) hQ1 hL1)
    (IsRep.of_mul_eq (k := k2) hQ2 hL2)
    hne



def witSmall_0 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1, 0, 0, 0, 1, 2, 0, 1, 0, 0, 1),
  (4, 0, 0, 2, 0, 2, 1, 1, 1, 0, 2),
  (5, 0, 1, 0, 2, 3, 0, 2, 1, 0, 2),
  (6, 0, 1, 2, 1, 3, 1, 0, 0, 2, 3),
  (11, 0, 3, 1, 1, 3, 1, 3, 0, 0, 2),
  (13, 0, 0, 2, 3, 4, 1, 1, 1, 3, 4),
  (16, 0, 0, 0, 4, 4, 0, 4, 0, 0, 2),
  (17, 0, 1, 4, 0, 3, 0, 2, 3, 2, 4),
  (18, 0, 3, 3, 0, 3, 1, 0, 4, 0, 3),
  (19, 1, 3, 2, 2, 4, 1, 4, 0, 1, 3),
  (20, 0, 0, 4, 2, 4, 1, 3, 0, 3, 4),
  (21, 2, 0, 3, 2, 4, 2, 2, 0, 3, 4),
  (26, 0, 5, 0, 1, 3, 3, 2, 2, 0, 3),
  (27, 3, 0, 3, 0, 3, 3, 1, 2, 2, 4),
  (28, 1, 3, 4, 1, 4, 3, 1, 0, 3, 4),
  (29, 0, 5, 2, 0, 3, 1, 1, 5, 1, 4),
  (30, 0, 1, 2, 5, 5, 0, 2, 5, 1, 4),
  (31, 1, 0, 2, 5, 5, 1, 2, 3, 4, 5),
  (32, 1, 2, 1, 5, 5, 1, 5, 1, 2, 4),
  (33, 0, 1, 4, 4, 5, 0, 4, 4, 1, 4),
  (34, 0, 3, 3, 4, 5, 1, 0, 4, 4, 5),
  (35, 0, 3, 1, 5, 5, 2, 1, 1, 5, 5),
  (37, 0, 0, 6, 1, 4, 0, 1, 0, 6, 5),
  (38, 1, 0, 0, 6, 5, 1, 4, 2, 4, 5),
  (40, 1, 2, 5, 3, 5, 4, 0, 2, 2, 4)
  ]

lemma witSmall_0_ok : witSmall_0.all checkWit = true := by
  decide +kernel

lemma witSmall_0_ns :
    witSmall_0.map (fun t => t.1) = [1, 4, 5, 6, 11, 13, 16, 17, 18, 19, 20, 21, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 40] := by
  decide +kernel

def witSmall_1 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (41, 0, 6, 1, 2, 4, 4, 0, 0, 3, 4),
  (42, 2, 3, 0, 5, 5, 2, 3, 4, 3, 5),
  (43, 0, 3, 5, 3, 5, 1, 4, 0, 5, 5),
  (46, 0, 1, 6, 3, 5, 0, 6, 3, 1, 4),
  (47, 1, 0, 6, 3, 5, 1, 3, 6, 0, 4),
  (48, 2, 2, 6, 0, 4, 2, 6, 0, 2, 4),
  (49, 2, 4, 5, 0, 4, 2, 6, 2, 1, 4),
  (50, 0, 5, 0, 5, 5, 0, 5, 4, 3, 5),
  (51, 2, 5, 3, 3, 5, 3, 4, 1, 4, 5),
  (52, 0, 4, 6, 0, 4, 1, 1, 7, 0, 4),
  (53, 0, 2, 7, 0, 4, 4, 1, 2, 4, 5),
  (54, 3, 6, 0, 0, 3, 5, 0, 2, 0, 3),
  (55, 1, 6, 1, 4, 5, 1, 7, 0, 2, 4),
  (56, 1, 6, 3, 3, 5, 1, 7, 2, 1, 4),
  (57, 2, 0, 7, 0, 4, 2, 3, 6, 2, 5),
  (58, 1, 4, 6, 2, 5, 4, 1, 0, 5, 5),
  (59, 1, 2, 7, 2, 5, 3, 5, 4, 0, 4),
  (61, 0, 6, 5, 0, 4, 1, 1, 3, 7, 6),
  (62, 0, 2, 3, 7, 6, 0, 3, 7, 2, 5),
  (63, 1, 3, 4, 6, 6, 3, 4, 5, 2, 5),
  (64, 0, 0, 8, 0, 4, 1, 1, 5, 6, 6),
  (65, 0, 0, 4, 7, 6, 0, 2, 5, 6, 6),
  (66, 0, 7, 1, 4, 5, 1, 8, 0, 0, 3),
  (67, 0, 7, 3, 3, 5, 1, 6, 5, 2, 5),
  (68, 0, 0, 2, 8, 6, 0, 4, 4, 6, 6)
  ]

lemma witSmall_1_ok : witSmall_1.all checkWit = true := by
  decide +kernel

lemma witSmall_1_ns :
    witSmall_1.map (fun t => t.1) = [41, 42, 43, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68] := by
  decide +kernel

def witSmall_2 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (69, 0, 1, 8, 2, 5, 0, 2, 1, 8, 6),
  (70, 1, 0, 8, 2, 5, 2, 7, 2, 3, 5),
  (71, 3, 0, 7, 2, 5, 3, 1, 4, 6, 6),
  (72, 0, 0, 6, 6, 6, 1, 3, 6, 5, 6),
  (73, 2, 0, 1, 8, 6, 2, 2, 6, 5, 6),
  (74, 2, 4, 1, 7, 6, 2, 4, 5, 5, 6),
  (75, 1, 3, 0, 8, 6, 5, 0, 0, 5, 5),
  (76, 2, 2, 0, 8, 6, 3, 7, 3, 0, 4),
  (77, 0, 4, 6, 5, 6, 1, 1, 7, 5, 6),
  (78, 0, 2, 7, 5, 6, 0, 7, 5, 2, 5),
  (79, 1, 8, 2, 3, 5, 5, 4, 2, 3, 5),
  (80, 0, 4, 0, 8, 6, 0, 8, 4, 0, 4),
  (81, 0, 0, 0, 9, 6, 0, 6, 3, 6, 6),
  (82, 1, 8, 0, 4, 5, 2, 0, 7, 5, 6),
  (83, 1, 4, 8, 1, 5, 2, 5, 7, 1, 5),
  (84, 2, 6, 2, 6, 6, 3, 4, 7, 1, 5),
  (85, 1, 9, 1, 1, 4, 2, 6, 4, 5, 6),
  (86, 0, 6, 1, 7, 6, 0, 6, 5, 5, 6),
  (88, 1, 2, 9, 1, 5, 1, 6, 7, 1, 5),
  (89, 0, 0, 8, 5, 6, 2, 4, 7, 4, 6),
  (90, 0, 5, 8, 1, 5, 5, 0, 6, 2, 5),
  (91, 0, 3, 9, 1, 5, 1, 3, 8, 4, 6),
  (92, 1, 5, 7, 4, 6, 1, 7, 4, 5, 6),
  (93, 2, 6, 0, 7, 6, 4, 0, 6, 5, 6),
  (94, 0, 9, 2, 3, 5, 2, 7, 6, 1, 5)
  ]

lemma witSmall_2_ok : witSmall_2.all checkWit = true := by
  decide +kernel

lemma witSmall_2_ns :
    witSmall_2.map (fun t => t.1) = [69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 88, 89, 90, 91, 92, 93, 94] := by
  decide +kernel

def witSmall_3 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (95, 3, 5, 6, 4, 6, 3, 8, 3, 2, 5),
  (96, 0, 4, 8, 4, 6, 2, 6, 6, 4, 6),
  (97, 0, 9, 0, 4, 5, 4, 4, 0, 7, 6),
  (99, 0, 7, 7, 1, 5, 2, 9, 1, 3, 5),
  (100, 1, 1, 9, 4, 6, 1, 7, 0, 7, 6),
  (101, 0, 2, 9, 4, 6, 0, 6, 7, 4, 6),
  (102, 0, 1, 10, 1, 5, 0, 10, 1, 1, 4),
  (103, 1, 0, 10, 1, 5, 1, 7, 6, 4, 6),
  (104, 0, 8, 2, 6, 6, 3, 7, 1, 6, 6),
  (105, 0, 8, 4, 5, 6, 2, 0, 9, 4, 6),
  (107, 4, 7, 5, 1, 5, 6, 5, 1, 3, 5),
  (108, 3, 7, 5, 4, 6, 3, 8, 5, 1, 5),
  (109, 0, 10, 3, 0, 4, 2, 8, 1, 6, 6),
  (112, 1, 2, 5, 9, 7, 1, 10, 1, 3, 5),
  (113, 0, 8, 0, 7, 6, 2, 8, 5, 4, 6),
  (114, 2, 3, 4, 9, 7, 2, 4, 9, 3, 6),
  (115, 0, 3, 5, 9, 7, 1, 2, 3, 10, 7),
  (116, 0, 0, 10, 4, 6, 0, 8, 6, 4, 6),
  (117, 0, 1, 4, 10, 7, 1, 5, 9, 3, 6),
  (118, 0, 1, 6, 9, 7, 0, 3, 3, 10, 7),
  (119, 1, 0, 6, 9, 7, 1, 2, 7, 8, 7),
  (120, 1, 3, 10, 3, 6, 1, 9, 1, 6, 6),
  (121, 2, 2, 10, 3, 6, 2, 3, 2, 10, 7),
  (122, 0, 3, 7, 8, 7, 0, 5, 4, 9, 7),
  (123, 2, 5, 3, 9, 7, 3, 4, 5, 8, 7)
  ]

lemma witSmall_3_ok : witSmall_3.all checkWit = true := by
  decide +kernel

lemma witSmall_3_ns :
    witSmall_3.map (fun t => t.1) = [95, 96, 97, 99, 100, 101, 102, 103, 104, 105, 107, 108, 109, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123] := by
  decide +kernel

def witSmall_4 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (124, 1, 7, 8, 3, 6, 1, 9, 5, 4, 6),
  (125, 0, 4, 10, 3, 6, 0, 5, 6, 8, 7),
  (126, 0, 1, 2, 11, 7, 0, 6, 9, 3, 6),
  (127, 1, 0, 2, 11, 7, 1, 2, 11, 0, 5),
  (128, 1, 2, 1, 11, 7, 1, 6, 3, 9, 7),
  (129, 0, 1, 8, 8, 7, 0, 5, 2, 10, 7),
  (130, 0, 3, 11, 0, 5, 0, 7, 9, 0, 5),
  (131, 0, 3, 1, 11, 7, 0, 11, 1, 3, 5),
  (132, 3, 4, 7, 7, 7, 4, 8, 0, 6, 6),
  (133, 1, 1, 11, 3, 6, 4, 1, 6, 8, 7),
  (134, 0, 2, 11, 3, 6, 0, 10, 3, 5, 6),
  (135, 3, 2, 8, 7, 7, 3, 4, 1, 10, 7),
  (136, 1, 2, 9, 7, 7, 1, 6, 7, 7, 7),
  (137, 0, 8, 8, 3, 6, 0, 10, 1, 6, 6),
  (138, 0, 5, 8, 7, 7, 0, 7, 5, 8, 7),
  (139, 0, 3, 9, 7, 7, 0, 7, 3, 9, 7),
  (140, 2, 10, 4, 4, 6, 3, 0, 1, 11, 7),
  (141, 0, 10, 5, 4, 6, 1, 9, 7, 3, 6),
  (142, 2, 7, 2, 9, 7, 2, 7, 6, 7, 7),
  (143, 3, 2, 0, 11, 7, 5, 2, 5, 8, 7),
  (144, 2, 10, 0, 6, 6, 3, 9, 6, 3, 6),
  (145, 0, 1, 0, 12, 7, 0, 1, 12, 0, 5),
  (146, 0, 5, 0, 11, 7, 1, 0, 0, 12, 7),
  (147, 0, 7, 7, 7, 7, 0, 11, 5, 1, 5),
  (148, 0, 12, 2, 0, 4, 2, 6, 10, 2, 6)
  ]

lemma witSmall_4_ok : witSmall_4.all checkWit = true := by
  decide +kernel

lemma witSmall_4_ns :
    witSmall_4.map (fun t => t.1) = [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148] := by
  decide +kernel

def witSmall_5 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (149, 2, 4, 11, 2, 6, 4, 9, 6, 0, 5),
  (150, 0, 1, 10, 7, 7, 0, 7, 1, 10, 7),
  (151, 1, 0, 10, 7, 7, 1, 8, 2, 9, 7),
  (152, 1, 5, 11, 2, 6, 1, 11, 2, 5, 6),
  (153, 0, 0, 12, 3, 6, 2, 3, 10, 6, 7),
  (154, 1, 4, 10, 6, 7, 1, 12, 2, 2, 5),
  (155, 1, 6, 9, 6, 7, 1, 7, 10, 2, 6),
  (156, 3, 8, 5, 7, 7, 5, 9, 3, 4, 6),
  (157, 2, 7, 0, 10, 7, 2, 7, 8, 6, 7),
  (158, 0, 10, 7, 3, 6, 3, 2, 10, 6, 7),
  (159, 1, 3, 12, 2, 6, 1, 11, 0, 6, 6),
  (160, 2, 2, 12, 2, 6, 5, 5, 9, 2, 6),
  (161, 0, 5, 10, 6, 7, 0, 6, 11, 2, 6),
  (162, 2, 9, 3, 8, 7, 6, 0, 9, 3, 6),
  (163, 1, 2, 11, 6, 7, 1, 12, 4, 1, 5),
  (164, 0, 4, 12, 2, 6, 3, 8, 1, 9, 7),
  (165, 2, 11, 6, 0, 5, 3, 11, 1, 5, 6),
  (166, 0, 3, 11, 6, 7, 0, 7, 9, 6, 7),
  (167, 3, 1, 12, 2, 6, 3, 8, 7, 6, 7),
  (168, 0, 8, 10, 2, 6, 1, 9, 9, 2, 6),
  (169, 4, 1, 10, 6, 7, 8, 0, 4, 5, 6),
  (170, 0, 11, 7, 0, 5, 6, 5, 3, 8, 7),
  (171, 2, 9, 1, 9, 7, 5, 0, 0, 11, 7),
  (172, 1, 13, 1, 0, 4, 3, 12, 3, 1, 5),
  (173, 0, 12, 2, 5, 6, 3, 11, 5, 3, 6)
  ]

lemma witSmall_5_ok : witSmall_5.all checkWit = true := by
  decide +kernel

lemma witSmall_5_ns :
    witSmall_5.map (fun t => t.1) = [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173] := by
  decide +kernel

def witSmall_6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (174, 2, 9, 7, 6, 7, 6, 1, 1, 10, 7),
  (175, 1, 10, 3, 8, 7, 3, 0, 11, 6, 7),
  (176, 0, 12, 4, 4, 6, 1, 1, 13, 2, 6),
  (177, 0, 2, 13, 2, 6, 0, 13, 2, 2, 5),
  (178, 0, 13, 0, 3, 5, 2, 12, 1, 5, 6),
  (179, 2, 5, 11, 5, 7, 3, 6, 10, 5, 7),
  (180, 0, 12, 0, 6, 6, 3, 4, 11, 5, 7),
  (181, 0, 1, 12, 6, 7, 0, 9, 0, 10, 7),
  (182, 1, 0, 12, 6, 7, 1, 12, 6, 0, 5),
  (184, 1, 6, 11, 5, 7, 1, 10, 1, 9, 7),
  (185, 0, 10, 9, 2, 6, 4, 9, 6, 6, 7),
  (186, 0, 13, 4, 1, 5, 2, 3, 12, 5, 7),
  (187, 1, 4, 12, 5, 7, 1, 10, 7, 6, 7),
  (188, 3, 5, 12, 1, 6, 3, 8, 9, 5, 7),
  (189, 0, 12, 6, 3, 6, 2, 6, 12, 1, 6),
  (190, 3, 10, 6, 6, 7, 4, 6, 11, 1, 6),
  (191, 1, 3, 6, 12, 8, 1, 8, 10, 5, 7),
  (192, 2, 2, 6, 12, 8, 3, 11, 7, 2, 6),
  (193, 2, 4, 5, 12, 8, 4, 4, 12, 1, 6),
  (194, 0, 5, 12, 5, 7, 0, 11, 3, 8, 7),
  (195, 0, 7, 11, 5, 7, 0, 11, 5, 7, 7),
  (196, 0, 4, 6, 12, 8, 1, 1, 7, 12, 8),
  (197, 0, 2, 7, 12, 8, 0, 14, 1, 0, 4),
  (198, 0, 2, 5, 13, 8, 5, 12, 0, 2, 5),
  (199, 3, 1, 6, 12, 8, 3, 10, 0, 9, 7)
  ]

lemma witSmall_6_ok : witSmall_6.all checkWit = true := by
  decide +kernel

lemma witSmall_6_ns :
    witSmall_6.map (fun t => t.1) = [174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199] := by
  decide +kernel

lemma not_mem_zero_of_ge_200 {n : ℕ} (hn : 200 ≤ n) : n ∉ A275409_zero_set := by
  simp [A275409_zero_set]; omega

lemma not_mem_one_of_ge_200 {n : ℕ} (hn : 200 ≤ n) : n ∉ A275409_one_set := by
  simp [A275409_one_set]; omega
lemma wit_mem_ge_two {c : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hok : c.all checkWit = true) {n : ℕ}
    (hin : n ∈ c.map (fun t => t.1)) : 2 ≤ a n := by
  rw [List.all_eq_true] at hok
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hin
  have := hok t ht
  simpa using checkWit_ge_two this

lemma mem_of_map_add {lo n : ℕ}
    {c : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hns : c.map (fun t => t.1) = (List.range 50).map (· + lo))
    (h1 : lo ≤ n) (h2 : n < lo + 50) :
    n ∈ c.map (fun t => t.1) := by
  rw [hns, List.mem_map]
  refine ⟨n - lo, ?_, ?_⟩
  · simp [List.mem_range]; omega
  · omega



lemma aList_zero_3 : aList 3 = 0 := by decide +kernel
lemma aList_zero_10 : aList 10 = 0 := by decide +kernel

lemma aList_ones :
    (oneList.map aList).all (· == 1) = true := by
  decide +kernel

lemma aList_zeros :
    (zeroList.map aList).all (· == 0) = true := by
  decide +kernel

lemma a_eq_zero_of_mem_zero {n : ℕ} (h : n ∈ A275409_zero_set) : a n = 0 := by
  have hz : n ∈ zeroList := by
    simpa [zeroList, A275409_zero_set] using h
  have hall := aList_zeros
  have := (List.all_eq_true.mp hall) (aList n) (List.mem_map.mpr ⟨n, hz, rfl⟩)
  have : aList n = 0 := by simpa using this
  exact (aList_eq_a n).symm.trans this

lemma a_eq_one_of_mem_one {n : ℕ} (h : n ∈ A275409_one_set) : a n = 1 := by
  have ho : n ∈ oneList := by
    simpa [oneList, A275409_one_set] using h
  have hall := aList_ones
  have := (List.all_eq_true.mp hall) (aList n) (List.mem_map.mpr ⟨n, ho, rfl⟩)
  have : aList n = 1 := by simpa using this
  exact (aList_eq_a n).symm.trans this

def inSmall (n : ℕ) : Bool :=
  (witSmall_0.map (fun t => t.1)).contains n ||
  (witSmall_1.map (fun t => t.1)).contains n ||
  (witSmall_2.map (fun t => t.1)).contains n ||
  (witSmall_3.map (fun t => t.1)).contains n ||
  (witSmall_4.map (fun t => t.1)).contains n ||
  (witSmall_5.map (fun t => t.1)).contains n ||
  (witSmall_6.map (fun t => t.1)).contains n

lemma small_cover :
    ((List.range 200).filter (fun n => !inZero n && !inOne n)).all
      (fun n => inSmall n) = true := by
  decide +kernel

lemma mem_small_of_nonspecial {n : ℕ} (hn : n < 200)
    (hz : n ∉ A275409_zero_set) (ho : n ∉ A275409_one_set) :
    inSmall n = true := by
  have hmem : n ∈ (List.range 200).filter (fun n => !inZero n && !inOne n) := by
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hn, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · have : inZero n = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        exact hz ((inZero_iff n).mp h)
      exact this
    · have : inOne n = false := by
        by_contra h
        simp only [Bool.not_eq_false] at h
        exact ho ((inOne_iff n).mp h)
      exact this
  exact (List.all_eq_true.mp small_cover) n hmem

lemma contains_to_mem {n : ℕ} {c : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : (c.map (fun t => t.1)).contains n = true) :
    n ∈ c.map (fun t => t.1) :=
  List.mem_of_elem_eq_true h

lemma a_ge_two_of_nonspecial {n : ℕ} (hn : n < 200)
    (hz : n ∉ A275409_zero_set) (ho : n ∉ A275409_one_set) : 2 ≤ a n := by
  have hsm := mem_small_of_nonspecial hn hz ho
  unfold inSmall at hsm
  if h : (witSmall_0.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_0_ok (contains_to_mem h)
  else if h : (witSmall_1.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_1_ok (contains_to_mem h)
  else if h : (witSmall_2.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_2_ok (contains_to_mem h)
  else if h : (witSmall_3.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_3_ok (contains_to_mem h)
  else if h : (witSmall_4.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_4_ok (contains_to_mem h)
  else if h : (witSmall_5.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_5_ok (contains_to_mem h)
  else if h : (witSmall_6.map (fun t => t.1)).contains n = true then
    exact wit_mem_ge_two witSmall_6_ok (contains_to_mem h)
  else
    simp_all [Bool.or_eq_true]


def witChunk_0 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (200, 0, 0, 14, 2, 6, 1, 2, 13, 5, 7),
  (201, 0, 4, 4, 13, 8, 0, 4, 8, 11, 8),
  (202, 2, 0, 5, 13, 8, 2, 4, 3, 13, 8),
  (203, 0, 3, 13, 5, 7, 0, 11, 1, 9, 7),
  (204, 2, 6, 4, 12, 8, 2, 14, 0, 0, 4),
  (205, 0, 0, 6, 13, 8, 0, 6, 5, 12, 8),
  (206, 0, 2, 9, 11, 8, 0, 6, 7, 11, 8),
  (207, 3, 5, 8, 10, 8, 3, 10, 8, 5, 7),
  (208, 0, 0, 8, 12, 8, 1, 1, 3, 14, 8),
  (209, 0, 2, 3, 14, 8, 0, 8, 12, 1, 6),
  (210, 2, 0, 9, 11, 8, 2, 11, 0, 9, 7),
  (211, 1, 3, 2, 14, 8, 1, 3, 10, 10, 8),
  (212, 0, 0, 4, 14, 8, 0, 12, 8, 2, 6),
  (213, 0, 4, 14, 1, 6, 2, 0, 3, 14, 8),
  (214, 0, 6, 3, 13, 8, 1, 12, 2, 8, 7),
  (215, 1, 7, 8, 10, 8, 5, 10, 1, 8, 7),
  (216, 0, 4, 2, 14, 8, 0, 4, 10, 10, 8),
  (217, 0, 6, 9, 10, 8, 2, 6, 2, 13, 8),
  (218, 1, 12, 6, 6, 7, 2, 5, 13, 4, 7),
  (219, 3, 1, 2, 14, 8, 3, 1, 10, 10, 8),
  (220, 3, 7, 3, 12, 8, 3, 12, 3, 7, 7),
  (221, 0, 0, 10, 11, 8, 0, 8, 6, 11, 8),
  (222, 0, 1, 14, 5, 7, 0, 10, 11, 1, 6),
  (223, 1, 0, 14, 5, 7, 1, 6, 13, 4, 7),
  (224, 0, 8, 4, 12, 8, 1, 1, 11, 10, 8),
  (225, 0, 2, 11, 10, 8, 2, 6, 10, 9, 8),
  (226, 1, 8, 12, 4, 7, 2, 4, 11, 9, 8),
  (227, 0, 11, 9, 5, 7, 1, 12, 0, 9, 7),
  (228, 0, 8, 8, 10, 8, 5, 5, 3, 12, 8),
  (229, 0, 0, 2, 15, 8, 1, 1, 1, 15, 8),
  (230, 0, 2, 1, 15, 8, 0, 2, 15, 1, 6),
  (231, 9, 7, 2, 4, 6, 9, 8, 2, 1, 5),
  (232, 1, 7, 10, 9, 8, 1, 9, 7, 10, 8),
  (233, 0, 6, 1, 14, 8, 4, 2, 1, 14, 8),
  (234, 0, 7, 13, 4, 7, 0, 13, 4, 7, 7),
  (235, 0, 15, 3, 1, 5, 1, 12, 8, 5, 7),
  (236, 1, 3, 0, 15, 8, 1, 3, 12, 9, 8),
  (237, 0, 5, 14, 4, 7, 0, 8, 2, 13, 8),
  (238, 0, 6, 11, 9, 8, 2, 13, 5, 6, 7),
  (239, 1, 10, 11, 4, 7, 3, 5, 0, 14, 8),
  (240, 2, 6, 0, 14, 8, 2, 6, 14, 0, 6),
  (241, 0, 4, 0, 15, 8, 0, 4, 12, 9, 8),
  (242, 2, 8, 1, 13, 8, 2, 13, 1, 8, 7),
  (243, 3, 9, 12, 0, 6, 5, 7, 12, 0, 6),
  (244, 0, 0, 12, 10, 8, 2, 10, 6, 10, 8),
  (245, 0, 8, 10, 9, 8, 0, 12, 10, 1, 6),
  (246, 0, 10, 5, 11, 8, 4, 14, 3, 3, 6),
  (247, 1, 2, 15, 4, 7, 1, 7, 0, 14, 8),
  (248, 5, 1, 1, 14, 8, 5, 13, 5, 2, 6),
  (249, 0, 10, 7, 10, 8, 0, 14, 7, 2, 6)
  ]

lemma witChunk_0_ok : witChunk_0.all checkWit = true := by
  decide +kernel

def witChunk_1 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (250, 0, 3, 15, 4, 7, 0, 13, 0, 9, 7),
  (251, 2, 13, 7, 5, 7, 3, 5, 12, 8, 8),
  (252, 1, 5, 15, 0, 6, 1, 9, 13, 0, 6),
  (253, 0, 10, 3, 12, 8, 1, 1, 13, 9, 8),
  (254, 0, 2, 13, 9, 8, 4, 13, 2, 7, 7),
  (255, 5, 3, 0, 14, 8, 5, 3, 14, 0, 6),
  (256, 0, 0, 0, 16, 8, 0, 16, 0, 0, 4),
  (257, 0, 0, 16, 1, 6, 2, 4, 13, 8, 8),
  (258, 0, 11, 11, 4, 7, 0, 13, 8, 5, 7),
  (259, 1, 7, 12, 8, 8, 1, 11, 6, 10, 8),
  (260, 0, 8, 0, 14, 8, 0, 8, 14, 0, 6),
  (261, 0, 6, 15, 0, 6, 3, 15, 3, 3, 6),
  (262, 0, 10, 9, 9, 8, 1, 12, 10, 4, 7),
  (263, 1, 14, 1, 8, 7, 1, 16, 2, 1, 5),
  (264, 3, 11, 5, 10, 8, 5, 6, 13, 3, 7),
  (265, 4, 8, 0, 13, 8, 4, 13, 0, 8, 7),
  (266, 3, 14, 4, 6, 7, 4, 9, 12, 3, 7),
  (267, 1, 3, 16, 0, 6, 1, 11, 12, 0, 6),
  (268, 1, 9, 11, 8, 8, 1, 11, 8, 9, 8),
  (269, 0, 6, 13, 8, 8, 0, 10, 13, 0, 6),
  (270, 0, 10, 1, 13, 8, 8, 9, 6, 5, 7),
  (271, 1, 3, 14, 8, 8, 1, 8, 14, 3, 7),
  (272, 0, 4, 16, 0, 6, 0, 8, 12, 8, 8),
  (273, 0, 1, 16, 4, 7, 2, 12, 11, 0, 6),
  (274, 1, 0, 16, 4, 7, 1, 16, 4, 0, 5),
  (275, 3, 1, 16, 0, 6, 3, 14, 6, 5, 7),
  (276, 0, 4, 14, 8, 8, 0, 16, 2, 4, 6),
  (277, 0, 0, 14, 9, 8, 2, 10, 0, 13, 8),
  (278, 0, 14, 9, 1, 6, 3, 14, 0, 8, 7),
  (279, 3, 1, 14, 8, 8, 7, 9, 10, 0, 6),
  (280, 0, 12, 6, 10, 8, 1, 10, 13, 3, 7),
  (281, 0, 12, 4, 11, 8, 0, 16, 0, 5, 6),
  (282, 2, 3, 16, 3, 7, 2, 11, 12, 3, 7),
  (283, 0, 7, 15, 3, 7, 0, 15, 3, 7, 7),
  (284, 3, 11, 1, 12, 8, 3, 11, 9, 8, 8),
  (285, 0, 10, 11, 8, 8, 0, 13, 10, 4, 7),
  (286, 0, 9, 14, 3, 7, 0, 15, 5, 6, 7),
  (287, 1, 11, 10, 8, 8, 3, 2, 16, 3, 7),
  (288, 0, 12, 12, 0, 6, 3, 5, 14, 7, 8),
  (289, 0, 12, 8, 9, 8, 2, 6, 14, 7, 8),
  (290, 0, 5, 16, 3, 7, 0, 15, 1, 8, 7),
  (291, 5, 14, 3, 6, 7, 5, 15, 0, 4, 6),
  (292, 0, 12, 2, 12, 8, 1, 1, 15, 8, 8),
  (293, 0, 2, 15, 8, 8, 0, 2, 17, 0, 6),
  (294, 0, 17, 2, 1, 5, 2, 15, 6, 5, 7),
  (295, 1, 14, 9, 4, 7, 5, 15, 4, 2, 6),
  (296, 0, 16, 6, 2, 6, 1, 7, 14, 7, 8),
  (297, 2, 0, 15, 8, 8, 2, 0, 17, 0, 6),
  (298, 2, 4, 15, 7, 8, 4, 1, 16, 3, 7),
  (299, 0, 11, 13, 3, 7, 0, 15, 7, 5, 7)
  ]

lemma witChunk_1_ok : witChunk_1.all checkWit = true := by
  decide +kernel

def witChunk_2 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (300, 5, 13, 9, 0, 6, 6, 10, 8, 8, 8),
  (301, 1, 5, 15, 7, 8, 1, 9, 13, 7, 8),
  (302, 4, 10, 11, 7, 8, 4, 15, 3, 6, 7),
  (303, 3, 13, 4, 10, 8, 5, 12, 10, 3, 7),
  (304, 1, 2, 17, 3, 7, 2, 14, 10, 0, 6),
  (305, 0, 17, 4, 0, 5, 6, 0, 13, 8, 8),
  (306, 2, 3, 8, 15, 9, 2, 17, 3, 0, 5),
  (307, 0, 3, 17, 3, 7, 1, 4, 8, 15, 9),
  (308, 0, 12, 10, 8, 8, 1, 17, 1, 4, 6),
  (309, 0, 8, 14, 7, 8, 1, 17, 3, 3, 6),
  (310, 0, 6, 15, 7, 8, 1, 4, 6, 16, 9),
  (311, 1, 2, 7, 16, 9, 1, 16, 2, 7, 7),
  (312, 1, 2, 9, 15, 9, 1, 6, 7, 15, 9),
  (313, 0, 12, 0, 13, 8, 2, 3, 10, 14, 9),
  (314, 0, 3, 7, 16, 9, 0, 5, 8, 15, 9),
  (315, 0, 3, 9, 15, 9, 1, 6, 9, 14, 9),
  (316, 1, 3, 16, 7, 8, 1, 11, 12, 7, 8),
  (317, 0, 5, 6, 16, 9, 0, 14, 11, 0, 6),
  (318, 0, 10, 13, 7, 8, 2, 7, 6, 15, 9),
  (319, 1, 6, 5, 16, 9, 1, 16, 6, 5, 7),
  (320, 0, 0, 16, 8, 8, 1, 2, 5, 17, 9),
  (321, 0, 1, 8, 16, 9, 0, 4, 16, 7, 8),
  (322, 0, 13, 12, 3, 7, 0, 15, 9, 4, 7),
  (323, 0, 3, 5, 17, 9, 0, 7, 7, 15, 9),
  (324, 0, 0, 18, 0, 6, 3, 0, 9, 15, 9),
  (325, 4, 1, 6, 16, 9, 4, 12, 10, 7, 8),
  (326, 0, 1, 6, 17, 9, 0, 1, 10, 15, 9),
  (327, 1, 0, 6, 17, 9, 1, 0, 10, 15, 9),
  (328, 1, 6, 11, 13, 9, 1, 14, 11, 3, 7),
  (329, 2, 7, 4, 16, 9, 2, 11, 14, 2, 7),
  (330, 0, 5, 4, 17, 9, 0, 7, 5, 16, 9),
  (331, 1, 4, 12, 13, 9, 1, 6, 17, 2, 7),
  (332, 2, 14, 8, 8, 8, 3, 0, 5, 17, 9),
  (333, 2, 8, 15, 6, 8, 7, 15, 1, 3, 6),
  (334, 0, 1, 18, 3, 7, 2, 9, 7, 14, 9),
  (335, 1, 0, 18, 3, 7, 1, 8, 10, 13, 9),
  (336, 1, 6, 3, 17, 9, 2, 6, 16, 6, 8),
  (337, 0, 12, 12, 7, 8, 4, 0, 16, 7, 8),
  (338, 0, 5, 12, 13, 9, 1, 8, 4, 16, 9),
  (339, 0, 7, 11, 13, 9, 1, 2, 3, 18, 9),
  (340, 2, 10, 14, 6, 8, 4, 4, 16, 6, 8),
  (341, 0, 1, 4, 18, 9, 0, 1, 12, 14, 9),
  (342, 0, 2, 17, 7, 8, 0, 3, 3, 18, 9),
  (343, 1, 7, 16, 6, 8, 1, 15, 4, 10, 8),
  (344, 1, 2, 13, 13, 9, 1, 9, 15, 6, 8),
  (345, 2, 3, 2, 18, 9, 2, 3, 18, 2, 7),
  (346, 1, 4, 2, 18, 9, 1, 4, 18, 2, 7),
  (347, 0, 3, 13, 13, 9, 0, 7, 3, 17, 9),
  (348, 2, 14, 0, 12, 8, 2, 18, 0, 4, 6),
  (349, 2, 4, 17, 6, 8, 3, 15, 5, 9, 8)
  ]

lemma witChunk_2_ok : witChunk_2.all checkWit = true := by
  decide +kernel

def witChunk_3 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (350, 0, 9, 10, 13, 9, 0, 11, 15, 2, 7),
  (351, 1, 6, 13, 12, 9, 3, 0, 3, 18, 9),
  (352, 1, 5, 17, 6, 8, 1, 10, 5, 15, 9),
  (353, 0, 5, 2, 18, 9, 0, 5, 18, 2, 7),
  (354, 1, 8, 12, 12, 9, 2, 9, 3, 16, 9),
  (355, 0, 15, 11, 3, 7, 1, 11, 14, 6, 8),
  (356, 0, 8, 16, 6, 8, 0, 16, 10, 0, 6),
  (357, 2, 3, 14, 12, 9, 2, 12, 13, 6, 8),
  (358, 1, 4, 14, 12, 9, 2, 5, 1, 18, 9),
  (359, 1, 8, 2, 17, 9, 3, 4, 1, 18, 9),
  (360, 9, 7, 10, 7, 8, 11, 9, 6, 1, 6),
  (361, 0, 6, 17, 6, 8, 0, 10, 15, 6, 8),
  (362, 0, 7, 13, 12, 9, 2, 11, 8, 13, 9),
  (363, 0, 19, 1, 1, 5, 1, 6, 1, 18, 9),
  (364, 3, 16, 9, 3, 7, 7, 4, 5, 15, 9),
  (365, 0, 5, 14, 12, 9, 3, 15, 1, 11, 8),
  (366, 0, 1, 2, 19, 9, 0, 1, 14, 13, 9),
  (367, 1, 0, 2, 19, 9, 1, 0, 14, 13, 9),
  (368, 1, 2, 1, 19, 9, 5, 10, 7, 13, 9),
  (369, 0, 9, 12, 12, 9, 0, 13, 14, 2, 7),
  (370, 0, 19, 3, 0, 5, 2, 11, 4, 15, 9),
  (371, 0, 3, 1, 19, 9, 0, 11, 5, 15, 9),
  (372, 0, 16, 4, 10, 8, 1, 17, 9, 0, 6),
  (373, 0, 0, 18, 7, 8, 0, 16, 6, 9, 8),
  (374, 0, 3, 19, 2, 7, 0, 7, 1, 18, 9),
  (375, 1, 2, 15, 12, 9, 3, 10, 16, 1, 7),
  (376, 0, 4, 18, 6, 8, 0, 12, 14, 6, 8),
  (377, 2, 16, 7, 8, 8, 4, 8, 16, 5, 8),
  (378, 0, 3, 15, 12, 9, 1, 12, 6, 14, 9),
  (379, 1, 4, 0, 19, 9, 1, 12, 8, 13, 9),
  (380, 3, 0, 1, 19, 9, 3, 4, 15, 11, 9),
  (381, 0, 16, 2, 11, 8, 2, 7, 0, 18, 9),
  (382, 2, 7, 18, 1, 7, 3, 18, 2, 6, 7),
  (383, 1, 8, 14, 11, 9, 1, 19, 4, 2, 6),
  (384, 0, 16, 8, 8, 8, 1, 6, 15, 11, 9),
  (385, 4, 14, 11, 6, 8, 4, 16, 4, 9, 8),
  (386, 0, 5, 0, 19, 9, 0, 11, 3, 16, 9),
  (387, 1, 12, 4, 15, 9, 2, 17, 9, 3, 7),
  (388, 3, 12, 15, 1, 7, 4, 16, 6, 8, 8),
  (389, 2, 10, 16, 5, 8, 2, 11, 2, 16, 9),
  (390, 1, 8, 0, 18, 9, 1, 12, 10, 12, 9),
  (391, 1, 8, 18, 1, 7, 1, 18, 7, 4, 7),
  (392, 1, 10, 1, 17, 9, 1, 10, 13, 11, 9),
  (393, 2, 6, 18, 5, 8, 6, 10, 14, 5, 8),
  (394, 2, 3, 16, 11, 9, 2, 11, 12, 11, 9),
  (395, 0, 7, 15, 11, 9, 1, 4, 16, 11, 9),
  (396, 2, 18, 8, 0, 6, 3, 4, 19, 1, 7),
  (397, 1, 9, 17, 5, 8, 1, 17, 5, 9, 8),
  (398, 0, 9, 14, 11, 9, 0, 15, 13, 2, 7),
  (399, 3, 2, 16, 11, 9, 3, 16, 11, 2, 7)
  ]

lemma witChunk_3_ok : witChunk_3.all checkWit = true := by
  decide +kernel

def witChunk_4 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (400, 0, 16, 0, 12, 8, 1, 1, 19, 6, 8),
  (401, 0, 1, 0, 20, 9, 0, 1, 16, 12, 9),
  (402, 0, 5, 16, 11, 9, 0, 13, 8, 13, 9),
  (403, 1, 12, 16, 1, 7, 1, 20, 0, 1, 5),
  (404, 1, 11, 16, 5, 8, 1, 17, 7, 8, 8),
  (405, 0, 1, 20, 2, 7, 0, 9, 0, 18, 9),
  (406, 0, 9, 18, 1, 7, 0, 19, 3, 6, 7),
  (407, 1, 15, 12, 6, 8, 3, 8, 15, 10, 9),
  (408, 3, 13, 14, 5, 8, 5, 3, 18, 5, 8),
  (409, 2, 19, 2, 6, 7, 4, 9, 14, 10, 9),
  (410, 0, 13, 4, 15, 9, 2, 4, 19, 5, 8),
  (411, 0, 7, 19, 1, 7, 0, 11, 1, 17, 9),
  (412, 7, 12, 13, 1, 7, 7, 15, 5, 8, 8),
  (413, 0, 8, 18, 5, 8, 0, 13, 10, 12, 9),
  (414, 0, 10, 17, 5, 8, 2, 9, 15, 10, 9),
  (415, 3, 18, 8, 3, 7, 5, 12, 10, 11, 9),
  (416, 0, 20, 0, 4, 6, 1, 2, 17, 11, 9),
  (417, 6, 7, 14, 10, 9, 6, 16, 5, 8, 8),
  (418, 2, 3, 20, 1, 7, 2, 11, 0, 17, 9),
  (419, 0, 3, 17, 11, 9, 1, 4, 20, 1, 7),
  (420, 0, 20, 4, 2, 6, 3, 17, 8, 7, 8),
  (421, 1, 13, 15, 5, 8, 1, 17, 9, 7, 8),
  (422, 0, 6, 19, 5, 8, 1, 8, 16, 10, 9),
  (423, 1, 14, 9, 12, 9, 3, 2, 20, 1, 7),
  (424, 1, 14, 15, 1, 7, 4, 16, 10, 6, 8),
  (425, 0, 12, 16, 5, 8, 2, 11, 14, 10, 9),
  (426, 0, 5, 20, 1, 7, 0, 13, 16, 1, 7),
  (427, 1, 6, 17, 10, 9, 1, 10, 15, 10, 9),
  (428, 3, 0, 17, 11, 9, 3, 17, 0, 11, 8),
  (429, 0, 13, 2, 16, 9, 2, 18, 4, 9, 8),
  (430, 0, 18, 5, 9, 8, 2, 15, 14, 1, 7),
  (431, 3, 12, 13, 10, 9, 7, 8, 13, 10, 9),
  (432, 1, 14, 3, 15, 9, 2, 18, 6, 8, 8),
  (433, 0, 18, 3, 10, 8, 6, 19, 0, 0, 5),
  (434, 0, 13, 12, 11, 9, 2, 13, 1, 16, 9),
  (435, 1, 12, 0, 17, 9, 3, 14, 10, 11, 9),
  (436, 0, 0, 20, 6, 8, 0, 16, 12, 6, 8),
  (437, 0, 9, 16, 10, 9, 0, 17, 12, 2, 7),
  (438, 0, 7, 17, 10, 9, 2, 15, 6, 13, 9),
  (439, 3, 9, 18, 4, 8, 5, 7, 18, 4, 8),
  (440, 1, 14, 11, 11, 9, 4, 20, 2, 2, 6),
  (441, 0, 4, 20, 5, 8, 2, 3, 18, 10, 9),
  (442, 0, 21, 0, 1, 5, 1, 4, 18, 10, 9),
  (443, 0, 15, 7, 13, 9, 1, 20, 4, 5, 7),
  (444, 3, 1, 20, 5, 8, 3, 7, 19, 4, 8),
  (445, 0, 21, 2, 0, 5, 2, 15, 4, 14, 9),
  (446, 0, 1, 18, 11, 9, 0, 11, 15, 10, 9),
  (447, 1, 0, 18, 11, 9, 5, 6, 19, 0, 7),
  (448, 1, 2, 21, 1, 7, 1, 15, 14, 5, 8),
  (449, 0, 5, 18, 10, 9, 2, 8, 19, 4, 8)
  ]

lemma witChunk_4_ok : witChunk_4.all checkWit = true := by
  decide +kernel

def witChunk_5 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (450, 0, 15, 9, 12, 9, 2, 9, 19, 0, 7),
  (451, 0, 3, 21, 1, 7, 0, 15, 15, 1, 7),
  (452, 3, 8, 17, 9, 9, 3, 20, 3, 5, 7),
  (453, 1, 21, 1, 3, 6, 2, 11, 18, 0, 7),
  (454, 0, 18, 9, 7, 8, 1, 20, 6, 4, 7),
  (455, 1, 14, 1, 16, 9, 1, 16, 14, 1, 7),
  (456, 1, 21, 3, 2, 6, 5, 6, 17, 9, 9),
  (457, 2, 7, 20, 0, 7, 2, 12, 17, 4, 8),
  (458, 0, 13, 0, 17, 9, 2, 16, 13, 5, 8),
  (459, 0, 15, 3, 15, 9, 2, 9, 17, 9, 9),
  (460, 1, 9, 19, 4, 8, 1, 19, 4, 9, 8),
  (461, 9, 17, 3, 1, 6, 10, 0, 15, 6, 8),
  (462, 2, 7, 18, 9, 9, 2, 15, 2, 15, 9),
  (463, 1, 10, 19, 0, 7, 1, 11, 18, 4, 8),
  (464, 0, 20, 8, 0, 6, 4, 4, 20, 4, 8),
  (465, 0, 13, 14, 10, 9, 6, 4, 19, 4, 8),
  (466, 1, 8, 20, 0, 7, 1, 16, 8, 12, 9),
  (467, 0, 15, 11, 11, 9, 1, 2, 19, 10, 9),
  (468, 2, 6, 10, 18, 10, 2, 18, 10, 6, 8),
  (469, 1, 1, 21, 5, 8, 1, 5, 9, 19, 10),
  (470, 0, 2, 21, 5, 8, 0, 3, 19, 10, 9),
  (471, 1, 8, 18, 9, 9, 5, 4, 18, 9, 9),
  (472, 1, 3, 10, 19, 10, 1, 5, 11, 18, 10),
  (473, 2, 2, 10, 19, 10, 2, 4, 7, 20, 10),
  (474, 2, 0, 21, 5, 8, 2, 5, 21, 0, 7),
  (475, 1, 3, 8, 20, 10, 1, 7, 10, 18, 10),
  (476, 1, 5, 7, 20, 10, 1, 7, 8, 19, 10),
  (477, 0, 4, 10, 19, 10, 0, 10, 19, 4, 8),
  (478, 0, 6, 9, 19, 10, 4, 2, 9, 19, 10),
  (479, 1, 3, 12, 18, 10, 1, 6, 21, 0, 7),
  (480, 0, 4, 8, 20, 10, 0, 8, 20, 4, 8),
  (481, 0, 6, 11, 18, 10, 0, 9, 20, 0, 7),
  (482, 0, 11, 19, 0, 7, 0, 15, 1, 16, 9),
  (483, 1, 12, 16, 9, 9, 2, 13, 15, 9, 9),
  (484, 0, 4, 12, 18, 10, 0, 12, 18, 4, 8),
  (485, 0, 2, 9, 20, 10, 0, 6, 7, 20, 10),
  (486, 0, 1, 22, 1, 7, 0, 2, 11, 19, 10),
  (487, 1, 0, 22, 1, 7, 1, 7, 6, 20, 10),
  (488, 0, 8, 10, 18, 10, 1, 3, 6, 21, 10),
  (489, 0, 8, 8, 19, 10, 2, 0, 9, 20, 10),
  (490, 0, 7, 21, 0, 7, 0, 21, 0, 7, 7),
  (491, 0, 7, 19, 9, 9, 0, 11, 17, 9, 9),
  (492, 1, 21, 7, 0, 6, 3, 7, 5, 20, 10),
  (493, 0, 4, 6, 21, 10, 0, 6, 21, 4, 8),
  (494, 0, 2, 7, 21, 10, 0, 6, 13, 17, 10),
  (495, 3, 5, 14, 16, 10, 3, 16, 11, 10, 9),
  (496, 1, 1, 13, 18, 10, 1, 3, 14, 17, 10),
  (497, 0, 2, 13, 18, 10, 0, 8, 12, 17, 10),
  (498, 2, 0, 7, 21, 10, 2, 3, 20, 9, 9),
  (499, 1, 4, 20, 9, 9, 1, 15, 16, 4, 8)
  ]

lemma witChunk_5_ok : witChunk_5.all checkWit = true := by
  decide +kernel

def witChunk_6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (500, 0, 0, 10, 20, 10, 0, 8, 6, 20, 10),
  (501, 0, 1, 20, 10, 9, 0, 4, 14, 17, 10),
  (502, 0, 6, 5, 21, 10, 1, 0, 20, 10, 9),
  (503, 1, 7, 14, 16, 10, 3, 2, 20, 9, 9),
  (504, 0, 20, 2, 10, 8, 1, 14, 15, 9, 9),
  (505, 0, 0, 8, 21, 10, 0, 0, 12, 19, 10),
  (506, 0, 5, 20, 9, 9, 0, 13, 16, 9, 9),
  (507, 2, 21, 7, 3, 7, 3, 8, 19, 8, 9),
  (508, 1, 5, 15, 16, 10, 1, 7, 4, 21, 10),
  (509, 0, 0, 22, 5, 8, 0, 5, 22, 0, 7),
  (510, 0, 10, 7, 19, 10, 0, 10, 11, 17, 10),
  (511, 1, 3, 4, 22, 10, 1, 3, 22, 4, 8),
  (512, 1, 1, 5, 22, 10, 1, 11, 10, 17, 10),
  (513, 0, 2, 5, 22, 10, 0, 20, 8, 7, 8),
  (514, 0, 15, 17, 0, 7, 0, 21, 8, 3, 7),
  (515, 3, 9, 4, 20, 10, 3, 12, 17, 8, 9),
  (516, 0, 4, 4, 22, 10, 0, 4, 22, 4, 8),
  (517, 0, 6, 15, 16, 10, 1, 1, 15, 17, 10),
  (518, 0, 2, 15, 17, 10, 0, 17, 2, 15, 9),
  (519, 1, 18, 7, 12, 9, 3, 1, 4, 22, 10),
  (520, 0, 0, 6, 22, 10, 0, 0, 14, 18, 10),
  (521, 0, 8, 4, 21, 10, 0, 20, 0, 11, 8),
  (522, 2, 0, 15, 17, 10, 2, 8, 3, 21, 10),
  (523, 1, 3, 16, 16, 10, 1, 11, 12, 16, 10),
  (524, 2, 2, 16, 16, 10, 2, 10, 4, 20, 10),
  (525, 0, 10, 5, 20, 10, 0, 10, 13, 16, 10),
  (526, 4, 10, 13, 15, 10, 4, 14, 17, 3, 8),
  (527, 1, 10, 19, 8, 9, 1, 22, 5, 4, 7),
  (528, 0, 4, 16, 16, 10, 0, 16, 16, 4, 8),
  (529, 0, 6, 3, 22, 10, 2, 10, 14, 15, 10),
  (530, 0, 23, 1, 0, 5, 1, 8, 20, 8, 9),
  (531, 0, 3, 21, 9, 9, 0, 15, 15, 9, 9),
  (532, 0, 12, 8, 18, 10, 1, 7, 16, 15, 10),
  (533, 0, 12, 10, 17, 10, 0, 17, 12, 10, 9),
  (534, 1, 12, 18, 8, 9, 2, 21, 9, 2, 7),
  (535, 1, 2, 23, 0, 7, 1, 16, 14, 9, 9),
  (536, 0, 20, 10, 6, 8, 3, 5, 22, 3, 8),
  (537, 2, 6, 22, 3, 8, 2, 14, 18, 3, 8),
  (538, 0, 3, 23, 0, 7, 2, 1, 23, 0, 7),
  (539, 1, 7, 2, 22, 10, 1, 11, 4, 20, 10),
  (540, 1, 23, 0, 3, 6, 3, 0, 21, 9, 9),
  (541, 0, 12, 6, 19, 10, 1, 1, 3, 23, 10),
  (542, 0, 2, 3, 23, 10, 3, 18, 2, 14, 9),
  (543, 1, 6, 21, 8, 9, 3, 13, 10, 16, 10),
  (544, 0, 12, 12, 16, 10, 1, 3, 2, 23, 10),
  (545, 0, 0, 4, 23, 10, 0, 0, 16, 17, 10),
  (546, 0, 11, 19, 8, 9, 2, 0, 3, 23, 10),
  (547, 1, 18, 11, 10, 9, 1, 20, 12, 1, 7),
  (548, 1, 1, 17, 16, 10, 1, 1, 23, 4, 8),
  (549, 0, 2, 17, 16, 10, 0, 2, 23, 4, 8)
  ]

lemma witChunk_6_ok : witChunk_6.all checkWit = true := by
  decide +kernel

def witChunk_7 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (550, 0, 6, 17, 15, 10, 0, 10, 3, 21, 10),
  (551, 1, 14, 17, 8, 9, 1, 18, 15, 0, 7),
  (552, 0, 8, 2, 22, 10, 1, 18, 1, 15, 9),
  (553, 0, 12, 20, 3, 8, 2, 0, 17, 16, 10),
  (554, 0, 7, 21, 8, 9, 0, 19, 7, 12, 9),
  (555, 0, 19, 5, 13, 9, 5, 18, 9, 10, 9),
  (556, 3, 13, 12, 15, 10, 5, 13, 9, 16, 10),
  (557, 0, 8, 22, 3, 8, 0, 13, 18, 8, 9),
  (558, 6, 17, 1, 14, 9, 8, 6, 13, 15, 10),
  (559, 3, 21, 0, 10, 8, 3, 21, 8, 6, 8),
  (560, 0, 12, 4, 20, 10, 1, 3, 18, 15, 10),
  (561, 2, 2, 18, 15, 10, 2, 12, 3, 20, 10),
  (562, 2, 4, 23, 3, 8, 2, 16, 17, 3, 8),
  (563, 0, 19, 9, 11, 9, 0, 23, 3, 5, 7),
  (564, 2, 6, 18, 14, 10, 2, 14, 6, 18, 10),
  (565, 0, 4, 18, 15, 10, 0, 12, 14, 15, 10),
  (566, 0, 1, 22, 9, 9, 0, 6, 1, 23, 10),
  (567, 1, 0, 22, 9, 9, 1, 23, 6, 0, 6),
  (568, 1, 9, 1, 22, 10, 1, 9, 17, 14, 10),
  (569, 0, 14, 7, 18, 10, 0, 20, 12, 5, 8),
  (570, 0, 23, 5, 4, 7, 3, 2, 22, 8, 9),
  (571, 1, 7, 18, 14, 10, 1, 22, 9, 2, 7),
  (572, 2, 22, 4, 8, 8, 3, 5, 0, 23, 10),
  (573, 0, 5, 22, 8, 9, 0, 14, 11, 16, 10),
  (574, 0, 6, 23, 3, 8, 0, 22, 3, 9, 8),
  (575, 1, 11, 16, 14, 10, 1, 19, 14, 4, 8),
  (576, 1, 18, 13, 9, 9, 5, 6, 21, 7, 9),
  (577, 0, 1, 24, 0, 7, 2, 22, 2, 9, 8),
  (578, 0, 15, 17, 8, 9, 1, 0, 24, 0, 7),
  (579, 2, 9, 21, 7, 9, 3, 13, 14, 14, 10),
  (580, 0, 0, 2, 24, 10, 0, 0, 18, 16, 10),
  (581, 0, 2, 1, 24, 10, 2, 4, 19, 14, 10),
  (582, 0, 14, 5, 19, 10, 0, 19, 11, 10, 9),
  (583, 1, 15, 10, 16, 10, 3, 9, 0, 22, 10),
  (584, 0, 8, 18, 14, 10, 0, 24, 2, 2, 6),
  (585, 0, 10, 1, 22, 10, 0, 10, 17, 14, 10),
  (586, 0, 19, 15, 0, 7, 0, 21, 12, 1, 7),
  (587, 0, 19, 1, 15, 9, 0, 23, 7, 3, 7),
  (588, 2, 2, 0, 24, 10, 3, 20, 7, 11, 9),
  (589, 0, 12, 2, 21, 10, 0, 16, 18, 3, 8),
  (590, 0, 2, 19, 15, 10, 0, 14, 13, 15, 10),
  (591, 3, 13, 2, 20, 10, 3, 13, 20, 2, 8),
  (592, 0, 0, 24, 4, 8, 0, 4, 0, 24, 10),
  (593, 0, 6, 19, 14, 10, 0, 8, 0, 23, 10),
  (594, 2, 0, 19, 15, 10, 2, 12, 1, 21, 10),
  (595, 1, 12, 20, 7, 9, 3, 1, 0, 24, 10),
  (596, 0, 12, 16, 14, 10, 1, 3, 24, 3, 8),
  (597, 2, 2, 24, 3, 8, 2, 12, 21, 2, 8),
  (598, 1, 20, 14, 0, 7, 4, 6, 19, 13, 10),
  (599, 1, 2, 23, 8, 9, 1, 8, 22, 7, 9)
  ]

lemma witChunk_7_ok : witChunk_7.all checkWit = true := by
  decide +kernel

def witChunk_8 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (600, 3, 7, 23, 2, 8, 5, 15, 6, 17, 10),
  (601, 0, 4, 24, 3, 8, 0, 22, 9, 6, 8),
  (602, 0, 3, 23, 8, 9, 1, 20, 2, 14, 9),
  (603, 3, 22, 10, 1, 7, 5, 15, 18, 2, 8),
  (604, 1, 15, 4, 19, 10, 3, 1, 24, 3, 8),
  (605, 0, 14, 3, 20, 10, 2, 8, 23, 2, 8),
  (606, 2, 15, 18, 7, 9, 6, 19, 2, 13, 9),
  (607, 1, 3, 20, 14, 10, 1, 11, 0, 22, 10),
  (608, 1, 14, 19, 7, 9, 1, 22, 11, 1, 7),
  (609, 0, 16, 8, 17, 10, 0, 17, 16, 8, 9),
  (610, 1, 24, 4, 4, 7, 2, 12, 17, 13, 10),
  (611, 0, 11, 21, 7, 9, 0, 19, 13, 9, 9),
  (612, 0, 4, 20, 14, 10, 0, 16, 10, 16, 10),
  (613, 1, 9, 19, 13, 10, 1, 13, 1, 21, 10),
  (614, 0, 9, 22, 7, 9, 0, 23, 9, 2, 7),
  (615, 1, 18, 15, 8, 9, 3, 1, 20, 14, 10),
  (616, 0, 16, 6, 18, 10, 1, 6, 23, 7, 9),
  (617, 0, 14, 15, 14, 10, 2, 22, 10, 5, 8),
  (618, 0, 13, 20, 7, 9, 2, 21, 5, 12, 9),
  (619, 1, 15, 14, 14, 10, 2, 21, 7, 11, 9),
  (620, 1, 7, 20, 13, 10, 3, 20, 11, 9, 9),
  (621, 0, 21, 6, 12, 9, 3, 23, 5, 7, 8),
  (622, 0, 18, 17, 3, 8, 4, 14, 15, 13, 10),
  (623, 1, 24, 6, 3, 7, 3, 5, 24, 2, 8),
  (624, 2, 6, 24, 2, 8, 4, 24, 4, 0, 6),
  (625, 0, 0, 0, 25, 10, 0, 0, 20, 15, 10),
  (626, 0, 21, 4, 13, 9, 0, 21, 8, 11, 9),
  (627, 0, 7, 23, 7, 9, 1, 20, 0, 15, 9),
  (628, 0, 12, 0, 22, 10, 1, 17, 9, 16, 10),
  (629, 1, 13, 17, 13, 10, 1, 17, 7, 17, 10),
  (630, 0, 10, 19, 13, 10, 0, 22, 11, 5, 8),
  (631, 1, 7, 24, 2, 8, 1, 15, 2, 20, 10),
  (632, 0, 12, 22, 2, 8, 1, 25, 1, 2, 6),
  (633, 0, 8, 20, 13, 10, 0, 10, 23, 2, 8),
  (634, 2, 4, 21, 13, 10, 2, 16, 3, 19, 10),
  (635, 0, 15, 19, 7, 9, 2, 17, 17, 7, 9),
  (636, 5, 9, 19, 12, 10, 7, 23, 3, 0, 6),
  (637, 0, 12, 18, 13, 10, 0, 21, 14, 0, 7),
  (638, 0, 2, 25, 3, 8, 0, 14, 1, 21, 10),
  (639, 3, 12, 21, 6, 9, 5, 3, 24, 2, 8),
  (640, 1, 1, 21, 14, 10, 1, 17, 5, 18, 10),
  (641, 0, 1, 24, 8, 9, 0, 2, 21, 14, 10),
  (642, 1, 0, 24, 8, 9, 2, 0, 25, 3, 8),
  (643, 1, 4, 24, 7, 9, 3, 9, 20, 12, 10),
  (644, 0, 8, 24, 2, 8, 3, 11, 19, 12, 10),
  (645, 2, 0, 21, 14, 10, 2, 14, 0, 21, 10),
  (646, 0, 6, 21, 13, 10, 1, 24, 8, 2, 7),
  (647, 3, 2, 24, 7, 9, 3, 8, 23, 6, 9),
  (648, 0, 16, 14, 14, 10, 3, 25, 2, 1, 6),
  (649, 2, 11, 22, 6, 9, 4, 18, 17, 2, 8)
  ]

lemma witChunk_8_ok : witChunk_8.all checkWit = true := by
  decide +kernel

def witChunk_9 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (650, 0, 5, 24, 7, 9, 0, 19, 15, 8, 9),
  (651, 0, 23, 11, 1, 7, 2, 21, 11, 9, 9),
  (652, 1, 15, 16, 13, 10, 1, 25, 5, 0, 6),
  (653, 2, 4, 25, 2, 8, 3, 23, 9, 5, 8),
  (654, 0, 14, 17, 13, 10, 0, 25, 2, 5, 7),
  (655, 1, 22, 5, 12, 9, 1, 22, 13, 0, 7),
  (656, 0, 24, 4, 8, 8, 1, 5, 25, 2, 8),
  (657, 0, 25, 4, 4, 7, 2, 8, 21, 12, 10),
  (658, 2, 16, 15, 13, 10, 2, 24, 5, 7, 8),
  (659, 2, 25, 1, 5, 7, 3, 22, 6, 11, 9),
  (660, 0, 16, 2, 20, 10, 0, 16, 20, 2, 8),
  (661, 0, 18, 9, 16, 10, 0, 24, 2, 9, 8),
  (662, 0, 17, 18, 7, 9, 0, 18, 7, 17, 10),
  (663, 9, 16, 14, 7, 9, 9, 22, 1, 4, 7),
  (664, 1, 3, 22, 13, 10, 1, 18, 17, 7, 9),
  (665, 0, 6, 25, 2, 8, 0, 20, 16, 3, 8),
  (666, 0, 21, 0, 15, 9, 0, 21, 12, 9, 9),
  (667, 1, 10, 23, 6, 9, 1, 11, 20, 12, 10),
  (668, 1, 9, 21, 12, 10, 1, 15, 0, 21, 10),
  (669, 0, 4, 22, 13, 10, 0, 22, 13, 4, 8),
  (670, 0, 18, 11, 15, 10, 0, 25, 6, 3, 7),
  (671, 3, 5, 22, 12, 10, 3, 16, 19, 6, 9),
  (672, 2, 6, 22, 12, 10, 2, 14, 18, 12, 10),
  (673, 0, 18, 5, 18, 10, 4, 8, 24, 1, 8),
  (674, 2, 19, 16, 7, 9, 8, 19, 11, 8, 9),
  (675, 1, 14, 21, 6, 9, 3, 22, 2, 13, 9),
  (676, 0, 24, 0, 10, 8, 0, 24, 8, 6, 8),
  (677, 1, 21, 15, 3, 8, 4, 25, 2, 4, 7),
  (678, 1, 8, 24, 6, 9, 5, 4, 24, 6, 9),
  (679, 1, 7, 22, 12, 10, 1, 24, 10, 1, 7),
  (680, 0, 0, 22, 14, 10, 1, 2, 25, 7, 9),
  (681, 0, 16, 16, 13, 10, 0, 26, 1, 2, 6),
  (682, 2, 12, 23, 1, 8, 2, 21, 13, 8, 9),
  (683, 0, 3, 25, 7, 9, 1, 19, 8, 16, 10),
  (684, 3, 4, 11, 23, 11, 3, 19, 7, 16, 10),
  (685, 0, 0, 26, 3, 8, 0, 10, 21, 12, 10),
  (686, 0, 11, 23, 6, 9, 0, 26, 3, 1, 6),
  (687, 3, 4, 13, 22, 11, 3, 8, 11, 22, 11),
  (688, 0, 12, 20, 12, 10, 1, 6, 11, 23, 11),
  (689, 0, 13, 22, 6, 9, 0, 18, 13, 14, 10),
  (690, 2, 3, 12, 23, 11, 2, 5, 9, 24, 11),
  (691, 1, 3, 26, 2, 8, 1, 4, 12, 23, 11),
  (692, 0, 8, 22, 12, 10, 1, 17, 1, 20, 10),
  (693, 0, 9, 24, 6, 9, 0, 25, 8, 2, 7),
  (694, 0, 18, 3, 19, 10, 1, 4, 10, 24, 11),
  (695, 1, 6, 9, 24, 11, 1, 8, 10, 23, 11),
  (696, 0, 4, 26, 2, 8, 3, 19, 11, 14, 10),
  (697, 0, 16, 0, 21, 10, 2, 3, 14, 22, 11),
  (698, 0, 5, 12, 23, 11, 0, 23, 5, 12, 9),
  (699, 0, 7, 11, 23, 11, 0, 19, 17, 7, 9)
  ]

lemma witChunk_9_ok : witChunk_9.all checkWit = true := by
  decide +kernel

def witChunk_10 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (700, 1, 5, 23, 12, 10, 1, 11, 24, 1, 8),
  (701, 0, 5, 10, 24, 11, 0, 14, 19, 12, 10),
  (702, 0, 2, 23, 13, 10, 0, 7, 13, 22, 11),
  (703, 1, 2, 11, 24, 11, 1, 8, 14, 21, 11),
  (704, 1, 2, 13, 23, 11, 1, 6, 15, 21, 11),
  (705, 0, 5, 14, 22, 11, 6, 7, 10, 22, 11),
  (706, 0, 3, 11, 24, 11, 0, 7, 9, 24, 11),
  (707, 0, 3, 13, 23, 11, 0, 23, 3, 13, 9),
  (708, 3, 4, 7, 25, 11, 3, 13, 20, 11, 10),
  (709, 0, 6, 23, 12, 10, 0, 9, 12, 22, 11),
  (710, 0, 7, 25, 6, 9, 0, 9, 10, 23, 11),
  (711, 3, 2, 8, 25, 11, 3, 10, 8, 23, 11),
  (712, 1, 2, 9, 25, 11, 1, 6, 7, 25, 11),
  (713, 2, 7, 16, 20, 11, 2, 10, 22, 11, 10),
  (714, 0, 5, 8, 25, 11, 2, 3, 16, 21, 11),
  (715, 0, 3, 9, 25, 11, 0, 7, 15, 21, 11),
  (716, 3, 0, 13, 23, 11, 3, 12, 23, 5, 9),
  (717, 3, 7, 23, 11, 10, 3, 19, 13, 13, 10),
  (718, 0, 3, 15, 22, 11, 0, 9, 14, 21, 11),
  (719, 1, 22, 13, 8, 9, 3, 2, 16, 21, 11),
  (720, 0, 20, 8, 16, 10, 3, 5, 26, 1, 8),
  (721, 0, 1, 12, 24, 11, 0, 9, 8, 24, 11),
  (722, 0, 5, 16, 21, 11, 1, 0, 12, 24, 11),
  (723, 0, 7, 7, 25, 11, 1, 18, 19, 6, 9),
  (724, 0, 16, 18, 12, 10, 1, 17, 17, 12, 10),
  (725, 0, 17, 20, 6, 9, 0, 18, 1, 20, 10),
  (726, 0, 1, 10, 25, 11, 0, 1, 14, 23, 11),
  (727, 1, 0, 10, 25, 11, 1, 0, 14, 23, 11),
  (728, 0, 20, 18, 2, 8, 1, 7, 26, 1, 8),
  (729, 2, 3, 6, 26, 11, 2, 3, 26, 6, 9),
  (730, 1, 4, 6, 26, 11, 1, 4, 26, 6, 9),
  (731, 0, 11, 9, 23, 11, 0, 11, 13, 21, 11),
  (732, 2, 2, 24, 12, 10, 2, 18, 0, 20, 10),
  (733, 1, 9, 23, 11, 10, 1, 13, 21, 11, 10),
  (734, 0, 3, 7, 26, 11, 2, 1, 7, 26, 11),
  (735, 1, 24, 6, 11, 9, 1, 27, 0, 2, 6),
  (736, 0, 4, 24, 12, 10, 0, 24, 12, 4, 8),
  (737, 0, 2, 27, 2, 8, 0, 5, 6, 26, 11),
  (738, 0, 7, 17, 20, 11, 1, 24, 4, 12, 9),
  (739, 0, 3, 17, 21, 11, 1, 6, 5, 26, 11),
  (740, 0, 20, 4, 18, 10, 0, 20, 12, 14, 10),
  (741, 0, 1, 8, 26, 11, 0, 1, 16, 22, 11),
  (742, 0, 9, 6, 25, 11, 1, 0, 8, 26, 11),
  (743, 3, 0, 7, 26, 11, 3, 20, 17, 6, 9),
  (744, 5, 26, 3, 3, 7, 9, 14, 19, 5, 9),
  (745, 0, 0, 24, 13, 10, 2, 23, 12, 8, 9),
  (746, 0, 11, 7, 24, 11, 0, 11, 15, 20, 11),
  (747, 1, 12, 24, 5, 9, 1, 27, 4, 0, 6),
  (748, 1, 7, 24, 11, 10, 1, 15, 20, 11, 10),
  (749, 0, 5, 18, 20, 11, 0, 12, 22, 11, 10)
  ]

lemma witChunk_10_ok : witChunk_10.all checkWit = true := by
  decide +kernel

def witChunk_11 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (750, 0, 7, 5, 26, 11, 0, 10, 23, 11, 10),
  (751, 1, 8, 18, 19, 11, 1, 24, 2, 13, 9),
  (752, 1, 10, 5, 25, 11, 1, 10, 17, 19, 11),
  (753, 0, 13, 10, 22, 11, 6, 2, 26, 1, 8),
  (754, 0, 13, 12, 21, 11, 0, 27, 3, 4, 7),
  (755, 0, 27, 1, 5, 7, 2, 5, 19, 19, 11),
  (756, 2, 26, 6, 6, 8, 3, 4, 19, 19, 11),
  (757, 0, 18, 17, 12, 10, 1, 5, 27, 1, 8),
  (758, 0, 14, 21, 11, 10, 0, 19, 19, 6, 9),
  (759, 1, 24, 10, 9, 9, 3, 10, 4, 25, 11),
  (760, 1, 2, 5, 27, 11, 1, 6, 19, 19, 11),
  (761, 0, 8, 24, 11, 10, 0, 26, 7, 6, 8),
  (762, 0, 13, 8, 23, 11, 0, 23, 13, 8, 9),
  (763, 0, 3, 5, 27, 11, 0, 27, 5, 3, 7),
  (764, 1, 19, 20, 1, 8, 1, 25, 11, 4, 8),
  (765, 0, 13, 14, 20, 11, 0, 20, 2, 19, 10),
  (766, 0, 1, 6, 27, 11, 0, 1, 18, 21, 11),
  (767, 1, 0, 6, 27, 11, 1, 0, 18, 21, 11),
  (768, 3, 11, 23, 10, 10, 5, 14, 9, 21, 11),
  (769, 0, 25, 12, 0, 7, 4, 14, 21, 10, 10),
  (770, 0, 3, 19, 20, 11, 0, 5, 4, 27, 11),
  (771, 0, 7, 19, 19, 11, 0, 11, 5, 25, 11),
  (772, 1, 1, 25, 12, 10, 3, 0, 5, 27, 11),
  (773, 0, 2, 25, 12, 10, 0, 9, 4, 26, 11),
  (774, 0, 3, 27, 6, 9, 1, 24, 0, 14, 9),
  (775, 3, 9, 24, 10, 10, 3, 9, 26, 0, 8),
  (776, 1, 6, 3, 27, 11, 1, 14, 7, 23, 11),
  (777, 0, 16, 20, 11, 10, 0, 22, 17, 2, 8),
  (778, 2, 3, 20, 19, 11, 2, 13, 5, 24, 11),
  (779, 0, 15, 23, 5, 9, 1, 4, 20, 19, 11),
  (780, 2, 14, 24, 0, 8, 5, 17, 21, 0, 8),
  (781, 0, 13, 6, 24, 11, 0, 24, 14, 3, 8),
  (782, 0, 6, 25, 11, 10, 0, 9, 26, 5, 9),
  (783, 3, 0, 27, 6, 9, 3, 2, 20, 19, 11),
  (784, 1, 14, 15, 19, 11, 2, 10, 24, 10, 10),
  (785, 0, 25, 4, 12, 9, 6, 11, 4, 24, 11),
  (786, 0, 5, 20, 19, 11, 0, 13, 16, 19, 11),
  (787, 0, 7, 3, 27, 11, 0, 15, 11, 21, 11),
  (788, 0, 0, 28, 2, 8, 0, 28, 0, 2, 6),
  (789, 0, 22, 7, 16, 10, 0, 25, 8, 10, 9),
  (790, 0, 15, 9, 22, 11, 0, 22, 9, 15, 10),
  (791, 1, 23, 16, 2, 8, 3, 17, 22, 0, 8),
  (792, 1, 6, 27, 5, 9, 1, 18, 21, 5, 9),
  (793, 2, 16, 23, 0, 8, 4, 6, 25, 10, 10),
  (794, 0, 15, 13, 20, 11, 1, 12, 18, 18, 11),
  (795, 2, 25, 9, 9, 9, 3, 16, 11, 20, 11),
  (796, 1, 3, 28, 1, 8, 1, 13, 25, 0, 8),
  (797, 2, 2, 28, 1, 8, 2, 8, 25, 10, 10),
  (798, 0, 17, 22, 5, 9, 0, 22, 5, 17, 10),
  (799, 1, 2, 3, 28, 11, 1, 8, 2, 27, 11)
  ]

lemma witChunk_11_ok : witChunk_11.all checkWit = true := by
  decide +kernel

def witChunk_12 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (800, 0, 20, 0, 20, 10, 0, 20, 16, 12, 10),
  (801, 0, 1, 4, 28, 11, 0, 1, 20, 20, 11),
  (802, 0, 3, 3, 28, 11, 1, 0, 4, 28, 11),
  (803, 0, 7, 27, 5, 9, 0, 15, 7, 23, 11),
  (804, 3, 1, 28, 1, 8, 3, 16, 13, 19, 11),
  (805, 0, 9, 20, 18, 11, 1, 21, 1, 19, 10),
  (806, 0, 11, 3, 26, 11, 0, 11, 19, 18, 11),
  (807, 3, 10, 20, 17, 11, 3, 16, 7, 22, 11),
  (808, 1, 2, 21, 19, 11, 1, 3, 26, 11, 10),
  (809, 2, 2, 26, 11, 10, 2, 11, 2, 26, 11),
  (810, 0, 13, 4, 25, 11, 3, 2, 2, 28, 11),
  (811, 0, 3, 21, 19, 11, 0, 15, 15, 19, 11),
  (812, 1, 9, 27, 0, 8, 1, 21, 15, 12, 10),
  (813, 0, 4, 26, 11, 10, 0, 5, 2, 28, 11),
  (814, 0, 7, 21, 18, 11, 0, 9, 2, 27, 11),
  (815, 1, 16, 14, 19, 11, 9, 14, 21, 4, 9),
  (816, 2, 18, 22, 0, 8, 3, 1, 26, 11, 10),
  (817, 0, 13, 18, 18, 11, 0, 22, 3, 18, 10),
  (818, 2, 5, 1, 28, 11, 2, 11, 20, 17, 11),
  (819, 2, 9, 1, 27, 11, 2, 9, 21, 17, 11),
  (820, 0, 0, 26, 12, 10, 0, 12, 24, 10, 10),
  (821, 0, 1, 28, 6, 9, 0, 14, 25, 0, 8),
  (822, 0, 22, 13, 13, 10, 1, 0, 28, 6, 9),
  (823, 1, 6, 1, 28, 11, 1, 16, 6, 23, 11),
  (824, 1, 26, 5, 11, 9, 3, 23, 9, 14, 10),
  (825, 0, 10, 25, 10, 10, 0, 14, 23, 10, 10),
  (826, 0, 15, 5, 24, 11, 1, 4, 22, 18, 11),
  (827, 0, 19, 21, 5, 9, 1, 4, 28, 5, 9),
  (828, 2, 6, 28, 0, 8, 3, 16, 5, 23, 11),
  (829, 0, 10, 27, 0, 8, 2, 23, 16, 6, 9),
  (830, 0, 17, 10, 21, 11, 2, 7, 22, 17, 11),
  (831, 1, 26, 3, 12, 9, 3, 2, 28, 5, 9),
  (832, 0, 16, 24, 0, 8, 1, 10, 1, 27, 11),
  (833, 0, 5, 22, 18, 11, 0, 17, 12, 20, 11),
  (834, 0, 5, 28, 5, 9, 0, 7, 1, 28, 11),
  (835, 1, 7, 28, 0, 8, 1, 12, 20, 17, 11),
  (836, 0, 24, 16, 2, 8, 1, 23, 4, 17, 10),
  (837, 0, 17, 8, 22, 11, 2, 26, 12, 3, 8),
  (838, 0, 15, 17, 18, 11, 1, 12, 26, 4, 9),
  (839, 1, 8, 22, 17, 11, 1, 14, 25, 4, 9),
  (840, 0, 8, 26, 10, 10, 0, 16, 22, 10, 10),
  (841, 2, 7, 0, 28, 11, 4, 1, 22, 18, 11),
  (842, 2, 17, 23, 4, 9, 3, 18, 10, 20, 11),
  (843, 3, 14, 2, 25, 11, 3, 25, 14, 2, 8),
  (844, 1, 23, 12, 13, 10, 3, 13, 24, 9, 10),
  (845, 0, 20, 18, 11, 10, 1, 1, 29, 1, 8),
  (846, 0, 1, 2, 29, 11, 0, 1, 22, 19, 11),
  (847, 1, 0, 2, 29, 11, 1, 0, 22, 19, 11),
  (848, 0, 8, 28, 0, 8, 1, 2, 1, 29, 11),
  (849, 0, 13, 2, 26, 11, 0, 28, 4, 7, 8)
  ]

lemma witChunk_12_ok : witChunk_12.all checkWit = true := by
  decide +kernel

def witChunk_13 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (850, 0, 27, 11, 0, 7, 1, 8, 0, 28, 11),
  (851, 0, 3, 1, 29, 11, 0, 11, 1, 27, 11),
  (852, 0, 28, 2, 8, 8, 1, 29, 3, 0, 6),
  (853, 0, 18, 23, 0, 8, 0, 22, 15, 12, 10),
  (854, 0, 2, 27, 11, 10, 0, 9, 22, 17, 11),
  (855, 3, 24, 15, 6, 9, 5, 18, 9, 20, 11),
  (856, 0, 28, 6, 6, 8, 1, 5, 27, 10, 10),
  (857, 2, 7, 28, 4, 9, 2, 28, 1, 8, 8),
  (858, 0, 13, 20, 17, 11, 2, 0, 27, 11, 10),
  (859, 0, 15, 3, 25, 11, 1, 2, 23, 18, 11),
  (860, 3, 0, 1, 29, 11, 3, 23, 13, 12, 10),
  (861, 0, 13, 26, 4, 9, 0, 29, 2, 4, 7),
  (862, 0, 3, 23, 18, 11, 2, 1, 23, 18, 11),
  (863, 1, 19, 20, 10, 10, 1, 26, 11, 8, 9),
  (864, 5, 18, 7, 21, 11, 9, 26, 5, 1, 7),
  (865, 0, 6, 27, 10, 10, 0, 9, 0, 28, 11),
  (866, 0, 5, 0, 29, 11, 0, 11, 27, 4, 9),
  (867, 0, 7, 23, 17, 11, 2, 29, 3, 3, 7),
  (868, 0, 24, 6, 16, 10, 1, 5, 29, 0, 8),
  (869, 0, 17, 16, 18, 11, 2, 11, 22, 16, 11),
  (870, 0, 25, 14, 7, 9, 1, 24, 16, 6, 9),
  (871, 1, 16, 18, 17, 11, 1, 18, 23, 4, 9),
  (872, 0, 24, 10, 14, 10, 1, 2, 29, 5, 9),
  (873, 0, 28, 8, 5, 8, 2, 27, 6, 10, 9),
  (874, 2, 9, 23, 16, 11, 2, 13, 21, 16, 11),
  (875, 0, 3, 29, 5, 9, 0, 15, 19, 17, 11),
  (876, 7, 12, 25, 3, 9, 10, 26, 0, 0, 6),
  (877, 0, 6, 29, 0, 8, 1, 13, 25, 9, 10),
  (878, 0, 27, 7, 10, 9, 2, 29, 5, 2, 7),
  (879, 5, 12, 26, 3, 9, 7, 14, 24, 3, 9),
  (880, 1, 11, 26, 9, 10, 1, 18, 5, 23, 11),
  (881, 0, 9, 28, 4, 9, 0, 17, 4, 24, 11),
  (882, 0, 19, 11, 20, 11, 0, 27, 3, 12, 9),
  (883, 0, 19, 9, 21, 11, 1, 4, 24, 17, 11),
  (884, 0, 20, 22, 0, 8, 1, 15, 24, 9, 10),
  (885, 2, 27, 2, 12, 9, 5, 5, 27, 9, 10),
  (886, 1, 12, 22, 16, 11, 1, 28, 10, 0, 7),
  (887, 1, 10, 23, 16, 11, 1, 16, 2, 25, 11),
  (888, 5, 10, 27, 3, 9, 5, 18, 15, 17, 11),
  (889, 0, 24, 12, 13, 10, 2, 7, 24, 16, 11),
  (890, 0, 5, 24, 17, 11, 2, 5, 29, 4, 9),
  (891, 0, 19, 13, 19, 11, 0, 27, 9, 9, 9),
  (892, 1, 23, 0, 19, 10, 2, 22, 20, 0, 8),
  (893, 1, 9, 27, 9, 10, 3, 23, 15, 11, 10),
  (894, 0, 19, 7, 22, 11, 0, 22, 17, 11, 10),
  (895, 1, 3, 28, 10, 10, 1, 6, 29, 4, 9),
  (896, 1, 26, 13, 7, 9, 2, 2, 28, 10, 10),
  (897, 2, 18, 22, 9, 10, 2, 24, 13, 12, 10),
  (898, 0, 13, 0, 27, 11, 1, 8, 24, 16, 11),
  (899, 0, 27, 1, 13, 9, 2, 29, 7, 1, 7)
  ]

lemma witChunk_13_ok : witChunk_13.all checkWit = true := by
  decide +kernel

def witChunk_14 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (900, 0, 4, 28, 10, 10, 0, 20, 20, 10, 10),
  (901, 0, 0, 30, 1, 8, 0, 1, 0, 30, 11),
  (902, 0, 14, 25, 9, 10, 0, 15, 1, 26, 11),
  (903, 3, 1, 28, 10, 10, 3, 25, 8, 14, 10),
  (904, 0, 24, 2, 18, 10, 1, 18, 17, 17, 11),
  (905, 0, 0, 28, 11, 10, 0, 26, 15, 2, 8),
  (906, 0, 7, 29, 4, 9, 0, 11, 23, 16, 11),
  (907, 1, 20, 8, 21, 11, 1, 20, 12, 19, 11),
  (908, 1, 23, 16, 11, 10, 1, 25, 5, 16, 10),
  (909, 0, 13, 22, 16, 11, 0, 30, 3, 0, 6),
  (910, 0, 10, 27, 9, 10, 0, 19, 15, 18, 11),
  (911, 1, 3, 30, 0, 8, 1, 18, 3, 24, 11),
  (912, 2, 2, 30, 0, 8, 2, 30, 2, 0, 6),
  (913, 0, 9, 24, 16, 11, 0, 16, 24, 9, 10),
  (914, 0, 27, 11, 8, 9, 1, 16, 20, 16, 11),
  (915, 0, 19, 5, 23, 11, 0, 23, 19, 5, 9),
  (916, 0, 4, 30, 0, 8, 0, 24, 14, 12, 10),
  (917, 0, 25, 16, 6, 9, 1, 25, 11, 13, 10),
  (918, 0, 17, 2, 25, 11, 2, 15, 26, 3, 9),
  (919, 1, 6, 25, 16, 11, 1, 30, 1, 4, 7),
  (920, 1, 2, 25, 17, 11, 1, 30, 3, 3, 7),
  (921, 6, 16, 23, 8, 10, 6, 28, 7, 4, 8),
  (922, 0, 15, 21, 16, 11, 1, 20, 6, 22, 11),
  (923, 0, 3, 25, 17, 11, 1, 28, 4, 11, 9),
  (924, 5, 3, 28, 9, 10, 5, 9, 27, 8, 10),
  (925, 0, 22, 21, 0, 8, 1, 25, 3, 17, 10),
  (926, 0, 1, 30, 5, 9, 3, 26, 14, 6, 9),
  (927, 1, 0, 30, 5, 9, 1, 24, 18, 5, 9),
  (928, 1, 19, 22, 9, 10, 4, 16, 24, 8, 10),
  (929, 0, 8, 28, 9, 10, 6, 8, 27, 8, 10),
  (930, 0, 7, 25, 16, 11, 2, 11, 24, 15, 11),
  (931, 1, 23, 20, 0, 8, 1, 27, 14, 2, 8),
  (932, 3, 0, 25, 17, 11, 3, 8, 25, 15, 11),
  (933, 2, 3, 30, 4, 9, 4, 30, 1, 0, 6),
  (934, 0, 18, 23, 9, 10, 1, 4, 30, 4, 9),
  (935, 5, 2, 25, 16, 11, 5, 20, 14, 17, 11),
  (936, 1, 14, 27, 3, 9, 3, 23, 17, 10, 10),
  (937, 0, 24, 0, 19, 10, 0, 28, 12, 3, 8),
  (938, 3, 2, 30, 4, 9, 3, 30, 4, 2, 7),
  (939, 0, 19, 17, 17, 11, 1, 12, 28, 3, 9),
  (940, 1, 25, 13, 12, 10, 1, 29, 9, 4, 8),
  (941, 0, 5, 30, 4, 9, 0, 21, 10, 20, 11),
  (942, 2, 15, 22, 15, 11, 2, 21, 13, 18, 11),
  (943, 1, 16, 26, 3, 9, 1, 18, 19, 16, 11),
  (944, 1, 1, 29, 10, 10, 2, 14, 26, 8, 10),
  (945, 0, 2, 29, 10, 10, 0, 17, 20, 16, 11),
  (946, 0, 19, 3, 24, 11, 0, 21, 8, 21, 11),
  (947, 0, 27, 13, 7, 9, 1, 12, 24, 15, 11),
  (948, 7, 20, 21, 3, 9, 8, 24, 10, 12, 10),
  (949, 1, 5, 29, 9, 10, 2, 0, 29, 10, 10)
  ]

lemma witChunk_14_ok : witChunk_14.all checkWit = true := by
  decide +kernel

def witChunk_15 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (950, 0, 26, 7, 15, 10, 1, 4, 26, 16, 11),
  (951, 5, 18, 1, 24, 11, 5, 28, 6, 9, 9),
  (952, 1, 10, 25, 15, 11, 1, 10, 29, 3, 9),
  (953, 0, 24, 16, 11, 10, 0, 26, 9, 14, 10),
  (954, 2, 19, 24, 3, 9, 3, 2, 26, 16, 11),
  (955, 1, 23, 18, 10, 10, 1, 28, 0, 13, 9),
  (956, 2, 10, 28, 8, 10, 2, 26, 4, 16, 10),
  (957, 0, 5, 26, 16, 11, 0, 26, 5, 16, 10),
  (958, 0, 6, 29, 9, 10, 0, 30, 3, 7, 8),
  (959, 5, 19, 22, 8, 10, 5, 28, 2, 11, 9),
  (960, 1, 18, 25, 3, 9, 2, 30, 4, 6, 8),
  (961, 0, 21, 6, 22, 11, 0, 21, 14, 18, 11),
  (962, 0, 13, 28, 3, 9, 5, 20, 16, 16, 11),
  (963, 0, 15, 27, 3, 9, 2, 17, 21, 15, 11),
  (964, 1, 1, 31, 0, 8, 1, 13, 27, 8, 10),
  (965, 0, 2, 31, 0, 8, 0, 17, 0, 26, 11),
  (966, 0, 1, 26, 17, 11, 0, 26, 11, 13, 10),
  (967, 1, 0, 26, 17, 11, 1, 8, 26, 15, 11),
  (968, 1, 22, 11, 19, 11, 3, 5, 14, 27, 12),
  (969, 2, 0, 31, 0, 8, 2, 6, 14, 27, 12),
  (970, 0, 13, 24, 15, 11, 2, 8, 13, 27, 12),
  (971, 0, 11, 25, 15, 11, 0, 11, 29, 3, 9),
  (972, 2, 6, 12, 28, 12, 2, 18, 24, 8, 10),
  (973, 1, 25, 15, 11, 10, 1, 29, 11, 3, 8),
  (974, 0, 17, 26, 3, 9, 0, 25, 18, 5, 9),
  (975, 1, 8, 30, 3, 9, 3, 5, 16, 26, 12),
  (976, 0, 24, 20, 0, 8, 1, 7, 14, 27, 12),
  (977, 0, 29, 6, 10, 9, 2, 4, 13, 28, 12),
  (978, 0, 19, 19, 16, 11, 0, 29, 4, 11, 9),
  (979, 0, 15, 23, 15, 11, 0, 31, 3, 3, 7),
  (980, 1, 5, 13, 28, 12, 1, 17, 25, 8, 10),
  (981, 1, 5, 15, 27, 12, 1, 9, 13, 27, 12),
  (982, 0, 9, 26, 15, 11, 1, 20, 2, 24, 11),
  (983, 1, 2, 31, 4, 9, 1, 7, 16, 26, 12),
  (984, 0, 28, 14, 2, 8, 1, 9, 15, 26, 12),
  (985, 2, 6, 10, 29, 12, 2, 31, 0, 4, 7),
  (986, 0, 3, 31, 4, 9, 0, 21, 4, 23, 11),
  (987, 0, 19, 1, 25, 11, 1, 20, 24, 3, 9),
  (988, 1, 9, 11, 28, 12, 1, 9, 29, 8, 10),
  (989, 0, 6, 13, 28, 12, 0, 8, 14, 27, 12),
  (990, 0, 6, 15, 27, 12, 0, 9, 30, 3, 9),
  (991, 1, 2, 27, 16, 11, 1, 3, 14, 28, 12),
  (992, 0, 8, 12, 28, 12, 0, 12, 28, 8, 10),
  (993, 2, 2, 30, 9, 10, 2, 6, 18, 25, 12),
  (994, 0, 3, 27, 16, 11, 1, 24, 20, 4, 9),
  (995, 0, 19, 25, 3, 9, 1, 11, 14, 26, 12),
  (996, 0, 4, 14, 28, 12, 0, 8, 16, 26, 12),
  (997, 0, 4, 30, 9, 10, 0, 30, 9, 4, 8),
  (998, 0, 6, 11, 29, 12, 0, 10, 13, 27, 12),
  (999, 3, 1, 14, 28, 12, 3, 9, 18, 24, 12)
  ]

lemma witChunk_15_ok : witChunk_15.all checkWit = true := by
  decide +kernel



lemma witChunk_0_ns :
    witChunk_0.map (fun t => t.1) = (List.range 50).map (· + 200) := by
  decide +kernel
lemma witChunk_1_ns :
    witChunk_1.map (fun t => t.1) = (List.range 50).map (· + 250) := by
  decide +kernel
lemma witChunk_2_ns :
    witChunk_2.map (fun t => t.1) = (List.range 50).map (· + 300) := by
  decide +kernel
lemma witChunk_3_ns :
    witChunk_3.map (fun t => t.1) = (List.range 50).map (· + 350) := by
  decide +kernel
lemma witChunk_4_ns :
    witChunk_4.map (fun t => t.1) = (List.range 50).map (· + 400) := by
  decide +kernel
lemma witChunk_5_ns :
    witChunk_5.map (fun t => t.1) = (List.range 50).map (· + 450) := by
  decide +kernel
lemma witChunk_6_ns :
    witChunk_6.map (fun t => t.1) = (List.range 50).map (· + 500) := by
  decide +kernel
lemma witChunk_7_ns :
    witChunk_7.map (fun t => t.1) = (List.range 50).map (· + 550) := by
  decide +kernel
lemma witChunk_8_ns :
    witChunk_8.map (fun t => t.1) = (List.range 50).map (· + 600) := by
  decide +kernel
lemma witChunk_9_ns :
    witChunk_9.map (fun t => t.1) = (List.range 50).map (· + 650) := by
  decide +kernel
lemma witChunk_10_ns :
    witChunk_10.map (fun t => t.1) = (List.range 50).map (· + 700) := by
  decide +kernel
lemma witChunk_11_ns :
    witChunk_11.map (fun t => t.1) = (List.range 50).map (· + 750) := by
  decide +kernel
lemma witChunk_12_ns :
    witChunk_12.map (fun t => t.1) = (List.range 50).map (· + 800) := by
  decide +kernel
lemma witChunk_13_ns :
    witChunk_13.map (fun t => t.1) = (List.range 50).map (· + 850) := by
  decide +kernel
lemma witChunk_14_ns :
    witChunk_14.map (fun t => t.1) = (List.range 50).map (· + 900) := by
  decide +kernel
lemma witChunk_15_ns :
    witChunk_15.map (fun t => t.1) = (List.range 50).map (· + 950) := by
  decide +kernel

def witChunk_16 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1000, 0, 0, 30, 10, 10, 0, 24, 18, 10, 10),
  (1001, 0, 4, 12, 29, 12, 0, 4, 16, 27, 12),
  (1002, 2, 12, 11, 27, 12, 2, 12, 15, 25, 12),
  (1003, 0, 7, 27, 15, 11, 1, 19, 24, 8, 10),
  (1004, 1, 11, 16, 25, 12, 3, 1, 12, 29, 12),
  (1005, 0, 8, 10, 29, 12, 0, 10, 11, 28, 12),
  (1006, 0, 22, 21, 9, 10, 2, 31, 6, 1, 7),
  (1007, 1, 11, 10, 28, 12, 3, 5, 8, 30, 12),
  (1008, 1, 5, 9, 30, 12, 1, 6, 31, 3, 9),
  (1009, 2, 8, 19, 24, 12, 4, 12, 28, 7, 10),
  (1010, 0, 23, 9, 20, 11, 0, 29, 0, 13, 9),
  (1011, 0, 23, 11, 19, 11, 0, 31, 7, 1, 7),
  (1012, 1, 1, 15, 28, 12, 1, 23, 20, 9, 10),
  (1013, 0, 2, 15, 28, 12, 0, 8, 18, 25, 12),
  (1014, 0, 2, 13, 29, 12, 0, 10, 17, 25, 12),
  (1015, 1, 7, 8, 30, 12, 1, 7, 30, 8, 10),
  (1016, 0, 4, 10, 30, 12, 0, 4, 18, 26, 12),
  (1017, 0, 6, 9, 30, 12, 0, 12, 12, 27, 12),
  (1018, 1, 12, 26, 14, 11, 1, 28, 14, 6, 9),
  (1019, 0, 7, 31, 3, 9, 0, 23, 7, 21, 11),
  (1020, 1, 9, 19, 24, 12, 2, 6, 20, 24, 12),
  (1021, 0, 21, 2, 24, 11, 0, 21, 18, 16, 11),
  (1022, 0, 2, 17, 27, 12, 0, 6, 19, 25, 12),
  (1023, 1, 11, 18, 24, 12, 5, 3, 8, 30, 12),
  (1024, 0, 0, 32, 0, 8, 1, 1, 11, 30, 12),
  (1025, 0, 2, 11, 30, 12, 0, 12, 16, 25, 12),
  (1026, 0, 21, 24, 3, 9, 2, 0, 17, 27, 12),
  (1027, 0, 19, 21, 15, 11, 1, 4, 28, 15, 11),
  (1028, 0, 8, 8, 30, 12, 0, 8, 30, 8, 10),
  (1029, 2, 0, 11, 30, 12, 3, 11, 7, 29, 12),
  (1030, 0, 30, 11, 3, 8, 1, 16, 24, 14, 11),
  (1031, 1, 22, 17, 16, 11, 3, 2, 28, 15, 11),
  (1032, 1, 9, 7, 30, 12, 1, 30, 3, 11, 9),
  (1033, 2, 11, 30, 2, 9, 2, 14, 10, 27, 12),
  (1034, 0, 5, 28, 15, 11, 0, 29, 12, 7, 9),
  (1035, 2, 21, 19, 15, 11, 3, 9, 6, 30, 12),
  (1036, 1, 3, 8, 31, 12, 1, 3, 20, 25, 12),
  (1037, 0, 0, 14, 29, 12, 0, 10, 19, 24, 12),
  (1038, 0, 23, 5, 22, 11, 4, 6, 21, 23, 12),
  (1039, 1, 24, 10, 19, 11, 1, 32, 2, 3, 7),
  (1040, 0, 0, 16, 28, 12, 0, 8, 20, 24, 12),
  (1041, 0, 1, 28, 16, 11, 0, 1, 32, 4, 9),
  (1042, 0, 31, 9, 0, 7, 1, 0, 28, 16, 11),
  (1043, 0, 23, 15, 17, 11, 0, 27, 17, 5, 9),
  (1044, 0, 0, 12, 30, 12, 0, 12, 18, 24, 12),
  (1045, 0, 28, 6, 15, 10, 1, 1, 9, 31, 12),
  (1046, 0, 2, 9, 31, 12, 0, 2, 31, 9, 10),
  (1047, 1, 15, 12, 26, 12, 1, 30, 1, 12, 9),
  (1048, 1, 7, 6, 31, 12, 1, 15, 14, 25, 12),
  (1049, 0, 10, 7, 30, 12, 0, 12, 8, 29, 12)
  ]

lemma witChunk_16_ok : witChunk_16.all checkWit = true := by
  decide +kernel

lemma witChunk_16_ns :
    witChunk_16.map (fun t => t.1) = (List.range 50).map (· + 1000) := by
  decide +kernel


def witChunk_17 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1050, 1, 12, 30, 2, 9, 2, 0, 9, 31, 12),
  (1051, 1, 4, 32, 3, 9, 1, 18, 23, 14, 11),
  (1052, 1, 5, 31, 8, 10, 1, 11, 20, 23, 12),
  (1053, 0, 0, 18, 27, 12, 0, 6, 21, 24, 12),
  (1054, 2, 9, 31, 2, 9, 2, 29, 13, 6, 9),
  (1055, 1, 24, 6, 21, 11, 1, 26, 19, 4, 9),
  (1056, 0, 28, 4, 16, 10, 1, 15, 10, 27, 12),
  (1057, 0, 24, 20, 9, 10, 2, 6, 22, 23, 12),
  (1058, 0, 5, 32, 3, 9, 2, 8, 5, 31, 12),
  (1059, 1, 11, 6, 30, 12, 1, 15, 16, 24, 12),
  (1060, 1, 15, 28, 7, 10, 3, 12, 27, 13, 11),
  (1061, 0, 0, 10, 31, 12, 0, 6, 31, 8, 10),
  (1062, 3, 30, 0, 12, 9, 5, 24, 6, 20, 11),
  (1063, 1, 22, 1, 24, 11, 1, 24, 14, 17, 11),
  (1064, 1, 7, 22, 23, 12, 3, 11, 5, 30, 12),
  (1065, 0, 26, 17, 10, 10, 2, 16, 15, 24, 12),
  (1066, 0, 21, 0, 25, 11, 0, 21, 20, 15, 11),
  (1067, 0, 23, 3, 23, 11, 0, 23, 23, 3, 9),
  (1068, 3, 16, 25, 13, 11, 3, 32, 5, 1, 7),
  (1069, 1, 1, 21, 25, 12, 1, 9, 5, 31, 12),
  (1070, 0, 2, 21, 25, 12, 0, 10, 21, 23, 12),
  (1071, 1, 3, 6, 32, 12, 1, 3, 22, 24, 12),
  (1072, 0, 28, 12, 12, 10, 1, 2, 29, 15, 11),
  (1073, 0, 12, 20, 23, 12, 0, 13, 30, 2, 9),
  (1074, 0, 23, 17, 16, 11, 2, 0, 21, 25, 12),
  (1075, 0, 3, 29, 15, 11, 1, 6, 29, 14, 11),
  (1076, 0, 0, 20, 26, 12, 0, 4, 6, 32, 12),
  (1077, 0, 2, 7, 32, 12, 0, 8, 22, 23, 12),
  (1078, 1, 24, 4, 22, 11, 2, 15, 26, 13, 11),
  (1079, 1, 23, 22, 8, 10, 3, 1, 6, 32, 12),
  (1080, 0, 12, 6, 30, 12, 1, 15, 18, 23, 12),
  (1081, 2, 0, 7, 32, 12, 2, 14, 6, 29, 12),
  (1082, 1, 20, 22, 14, 11, 1, 20, 26, 2, 9),
  (1083, 2, 25, 21, 3, 9, 3, 5, 4, 32, 12),
  (1084, 2, 6, 4, 32, 12, 3, 0, 29, 15, 11),
  (1085, 0, 6, 5, 32, 12, 0, 16, 10, 27, 12),
  (1086, 0, 7, 29, 14, 11, 0, 10, 5, 31, 12),
  (1087, 1, 27, 16, 10, 10, 3, 18, 24, 13, 11),
  (1088, 0, 0, 8, 32, 12, 0, 16, 16, 24, 12),
  (1089, 0, 16, 28, 7, 10, 0, 25, 8, 20, 11),
  (1090, 1, 24, 16, 16, 11, 1, 32, 8, 0, 7),
  (1091, 0, 31, 3, 11, 9, 0, 31, 7, 9, 9),
  (1092, 1, 17, 15, 24, 12, 1, 33, 1, 0, 6),
  (1093, 0, 12, 30, 7, 10, 0, 25, 12, 18, 11),
  (1094, 0, 6, 23, 23, 12, 0, 19, 27, 2, 9),
  (1095, 5, 12, 30, 1, 9, 5, 15, 6, 28, 12),
  (1096, 1, 9, 23, 22, 12, 1, 13, 5, 30, 12),
  (1097, 2, 16, 7, 28, 12, 2, 31, 8, 8, 9),
  (1098, 3, 22, 20, 14, 11, 3, 30, 12, 6, 9),
  (1099, 1, 3, 32, 8, 10, 1, 12, 28, 13, 11)
  ]

lemma witChunk_17_ok : witChunk_17.all checkWit = true := by
  decide +kernel

lemma witChunk_17_ns :
    witChunk_17.map (fun t => t.1) = (List.range 50).map (· + 1050) := by
  decide +kernel


def witChunk_18 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1100, 1, 11, 4, 31, 12, 2, 2, 32, 8, 10),
  (1101, 0, 28, 14, 11, 10, 1, 17, 9, 27, 12),
  (1102, 0, 18, 27, 7, 10, 0, 25, 6, 21, 11),
  (1103, 1, 16, 26, 13, 11, 3, 5, 24, 22, 12),
  (1104, 0, 4, 32, 8, 10, 0, 8, 4, 32, 12),
  (1105, 0, 0, 32, 9, 10, 0, 33, 0, 4, 7),
  (1106, 0, 23, 1, 24, 11, 0, 27, 19, 4, 9),
  (1107, 0, 3, 33, 3, 9, 1, 30, 13, 6, 9),
  (1108, 0, 28, 0, 18, 10, 0, 28, 18, 0, 8),
  (1109, 0, 0, 22, 25, 12, 0, 2, 23, 24, 12),
  (1110, 0, 10, 31, 7, 10, 0, 25, 14, 17, 11),
  (1111, 1, 7, 24, 22, 12, 1, 15, 20, 22, 12),
  (1112, 0, 12, 22, 22, 12, 1, 10, 29, 13, 11),
  (1113, 0, 10, 23, 22, 12, 2, 0, 23, 24, 12),
  (1114, 1, 4, 30, 14, 11, 2, 19, 24, 13, 11),
  (1115, 0, 23, 19, 15, 11, 1, 22, 25, 2, 9),
  (1116, 1, 3, 4, 33, 12, 1, 3, 24, 23, 12),
  (1117, 1, 1, 5, 33, 12, 1, 21, 25, 7, 10),
  (1118, 0, 2, 5, 33, 12, 0, 18, 13, 25, 12),
  (1119, 3, 26, 8, 19, 11, 3, 29, 2, 16, 10),
  (1120, 1, 18, 25, 13, 11, 1, 26, 9, 19, 11),
  (1121, 0, 4, 4, 33, 12, 0, 4, 24, 23, 12),
  (1122, 0, 13, 28, 13, 11, 0, 29, 16, 5, 9),
  (1123, 0, 15, 27, 13, 11, 1, 22, 21, 14, 11),
  (1124, 0, 8, 24, 22, 12, 0, 24, 22, 8, 10),
  (1125, 0, 0, 6, 33, 12, 0, 18, 15, 24, 12),
  (1126, 0, 1, 30, 15, 11, 0, 30, 15, 1, 8),
  (1127, 1, 0, 30, 15, 11, 1, 24, 18, 15, 11),
  (1128, 1, 26, 21, 3, 9, 5, 9, 31, 6, 10),
  (1129, 2, 14, 22, 21, 12, 4, 1, 30, 14, 11),
  (1130, 2, 16, 5, 29, 12, 3, 26, 6, 20, 11),
  (1131, 0, 11, 29, 13, 11, 0, 31, 11, 7, 9),
  (1132, 1, 19, 12, 25, 12, 1, 25, 21, 8, 10),
  (1133, 0, 10, 3, 32, 12, 0, 16, 6, 29, 12),
  (1134, 0, 6, 3, 33, 12, 0, 17, 26, 13, 11),
  (1135, 1, 8, 30, 13, 11, 1, 19, 14, 24, 12),
  (1136, 1, 5, 25, 22, 12, 1, 17, 19, 22, 12),
  (1137, 0, 8, 32, 7, 10, 0, 25, 16, 16, 11),
  (1138, 2, 8, 25, 21, 12, 4, 9, 32, 1, 9),
  (1139, 1, 19, 10, 26, 12, 2, 13, 31, 1, 9),
  (1140, 0, 16, 20, 22, 12, 0, 28, 16, 10, 10),
  (1141, 1, 13, 3, 31, 12, 1, 13, 23, 21, 12),
  (1142, 0, 7, 33, 2, 9, 0, 18, 17, 23, 12),
  (1143, 1, 15, 4, 30, 12, 1, 32, 6, 9, 9),
  (1144, 1, 7, 2, 33, 12, 1, 26, 5, 21, 11),
  (1145, 0, 6, 25, 22, 12, 0, 30, 7, 14, 10),
  (1146, 2, 16, 21, 21, 12, 2, 27, 20, 3, 9),
  (1147, 1, 20, 24, 13, 11, 2, 21, 23, 13, 11),
  (1148, 1, 19, 16, 23, 12, 2, 26, 20, 8, 10),
  (1149, 1, 9, 25, 21, 12, 2, 12, 31, 6, 10)
  ]

lemma witChunk_18_ok : witChunk_18.all checkWit = true := by
  decide +kernel

lemma witChunk_18_ns :
    witChunk_18.map (fun t => t.1) = (List.range 50).map (· + 1100) := by
  decide +kernel


def witChunk_19 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1150, 0, 9, 30, 13, 11, 0, 30, 5, 15, 10),
  (1151, 1, 11, 2, 32, 12, 1, 32, 2, 11, 9),
  (1152, 0, 0, 24, 24, 12, 1, 15, 22, 21, 12),
  (1153, 0, 33, 8, 0, 7, 2, 20, 13, 24, 12),
  (1154, 1, 24, 0, 24, 11, 1, 32, 8, 8, 9),
  (1155, 0, 19, 25, 13, 11, 3, 22, 22, 13, 11),
  (1156, 1, 1, 33, 8, 10, 1, 19, 8, 27, 12),
  (1157, 0, 2, 33, 8, 10, 0, 8, 2, 33, 12),
  (1158, 0, 2, 25, 23, 12, 0, 22, 25, 7, 10),
  (1159, 1, 16, 30, 1, 9, 1, 26, 15, 16, 11),
  (1160, 1, 14, 31, 1, 9, 1, 31, 14, 1, 8),
  (1161, 0, 12, 24, 21, 12, 2, 0, 33, 8, 10),
  (1162, 2, 0, 25, 23, 12, 2, 4, 33, 7, 10),
  (1163, 1, 2, 31, 14, 11, 1, 15, 30, 6, 10),
  (1164, 2, 30, 16, 0, 8, 2, 34, 0, 0, 6),
  (1165, 0, 30, 3, 16, 10, 0, 30, 11, 12, 10),
  (1166, 0, 1, 34, 3, 9, 0, 3, 31, 14, 11),
  (1167, 1, 0, 34, 3, 9, 5, 27, 18, 8, 10),
  (1168, 1, 1, 3, 34, 12, 1, 6, 31, 13, 11),
  (1169, 0, 2, 3, 34, 12, 0, 18, 19, 22, 12),
  (1170, 1, 32, 0, 12, 9, 2, 17, 27, 12, 11),
  (1171, 0, 27, 9, 19, 11, 1, 3, 2, 34, 12),
  (1172, 0, 0, 4, 34, 12, 0, 12, 2, 32, 12),
  (1173, 1, 9, 1, 33, 12, 1, 17, 21, 21, 12),
  (1174, 0, 6, 33, 7, 10, 0, 25, 18, 15, 11),
  (1175, 1, 32, 10, 7, 9, 3, 0, 31, 14, 11),
  (1176, 0, 4, 2, 34, 12, 0, 4, 26, 22, 12),
  (1177, 2, 3, 34, 2, 9, 2, 12, 1, 32, 12),
  (1178, 0, 27, 7, 20, 11, 1, 4, 34, 2, 9),
  (1179, 0, 7, 31, 13, 11, 0, 27, 21, 3, 9),
  (1180, 2, 14, 24, 20, 12, 3, 33, 8, 3, 8),
  (1181, 0, 8, 26, 21, 12, 0, 16, 22, 21, 12),
  (1182, 3, 2, 34, 2, 9, 3, 26, 2, 22, 11),
  (1183, 1, 11, 32, 6, 10, 1, 14, 29, 12, 11),
  (1184, 1, 5, 1, 34, 12, 1, 22, 23, 13, 11),
  (1185, 0, 5, 34, 2, 9, 0, 20, 16, 23, 12),
  (1186, 0, 21, 24, 13, 11, 1, 16, 28, 12, 11),
  (1187, 0, 15, 31, 1, 9, 0, 27, 13, 17, 11),
  (1188, 1, 21, 13, 24, 12, 3, 9, 0, 33, 12),
  (1189, 0, 28, 18, 9, 10, 0, 30, 17, 0, 8),
  (1190, 0, 10, 1, 33, 12, 0, 17, 30, 1, 9),
  (1191, 3, 17, 22, 20, 12, 3, 34, 4, 1, 7),
  (1192, 0, 16, 30, 6, 10, 1, 10, 33, 1, 9),
  (1193, 0, 6, 1, 34, 12, 0, 14, 31, 6, 10),
  (1194, 0, 13, 32, 1, 9, 2, 4, 27, 21, 12),
  (1195, 0, 27, 5, 21, 11, 1, 27, 20, 8, 10),
  (1196, 1, 13, 1, 32, 12, 1, 13, 25, 20, 12),
  (1197, 1, 5, 27, 21, 12, 1, 21, 15, 23, 12),
  (1198, 4, 26, 21, 7, 10, 6, 27, 6, 19, 11),
  (1199, 1, 11, 26, 20, 12, 1, 18, 27, 12, 11)
  ]

lemma witChunk_19_ok : witChunk_19.all checkWit = true := by
  decide +kernel

lemma witChunk_19_ns :
    witChunk_19.map (fun t => t.1) = (List.range 50).map (· + 1150) := by
  decide +kernel


def witChunk_20 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1200, 1, 17, 3, 30, 12, 1, 21, 9, 26, 12),
  (1201, 0, 18, 29, 6, 10, 0, 24, 24, 7, 10),
  (1202, 2, 32, 13, 1, 8, 6, 5, 31, 12, 11),
  (1203, 0, 19, 29, 1, 9, 1, 15, 24, 20, 12),
  (1204, 0, 12, 32, 6, 10, 1, 19, 20, 21, 12),
  (1205, 0, 0, 26, 23, 12, 0, 25, 24, 2, 9),
  (1206, 0, 6, 27, 21, 12, 0, 18, 21, 21, 12),
  (1207, 1, 7, 0, 34, 12, 1, 10, 31, 12, 11),
  (1208, 0, 20, 18, 22, 12, 1, 9, 33, 6, 10),
  (1209, 6, 10, 26, 19, 12, 6, 28, 17, 8, 10),
  (1210, 0, 15, 29, 12, 11, 0, 27, 15, 16, 11),
  (1211, 0, 11, 33, 1, 9, 0, 31, 15, 5, 9),
  (1212, 1, 9, 27, 20, 12, 1, 11, 0, 33, 12),
  (1213, 0, 13, 30, 12, 11, 1, 29, 17, 9, 10),
  (1214, 0, 33, 2, 11, 9, 2, 7, 34, 1, 9),
  (1215, 3, 2, 32, 13, 11, 5, 3, 0, 34, 12),
  (1216, 1, 1, 27, 22, 12, 1, 3, 34, 7, 10),
  (1217, 0, 2, 27, 22, 12, 0, 17, 28, 12, 11),
  (1218, 0, 5, 32, 13, 11, 2, 21, 25, 12, 11),
  (1219, 1, 28, 12, 17, 11, 1, 31, 16, 0, 8),
  (1220, 0, 0, 34, 8, 10, 0, 8, 0, 34, 12),
  (1221, 0, 1, 32, 14, 11, 0, 4, 34, 7, 10),
  (1222, 0, 27, 3, 22, 11, 1, 0, 32, 14, 11),
  (1223, 1, 8, 34, 1, 9, 1, 31, 2, 16, 10),
  (1224, 3, 1, 34, 7, 10, 3, 13, 26, 19, 12),
  (1225, 0, 10, 33, 6, 10, 0, 30, 15, 10, 10),
  (1226, 0, 11, 31, 12, 11, 0, 21, 28, 1, 9),
  (1227, 0, 23, 23, 13, 11, 1, 35, 0, 0, 6),
  (1228, 1, 31, 12, 11, 10, 2, 6, 28, 20, 12),
  (1229, 0, 0, 2, 35, 12, 0, 10, 27, 20, 12),
  (1230, 0, 2, 1, 35, 12, 0, 22, 11, 25, 12),
  (1231, 1, 24, 22, 13, 11, 5, 28, 6, 19, 11),
  (1232, 0, 16, 24, 20, 12, 2, 22, 8, 26, 12),
  (1233, 0, 12, 0, 33, 12, 0, 18, 3, 30, 12),
  (1234, 0, 19, 27, 12, 11, 1, 8, 32, 12, 11),
  (1235, 0, 35, 1, 3, 7, 1, 2, 35, 2, 9),
  (1236, 1, 3, 0, 35, 12, 1, 3, 28, 21, 12),
  (1237, 2, 2, 0, 35, 12, 2, 2, 28, 21, 12),
  (1238, 0, 3, 35, 2, 9, 0, 9, 34, 1, 9),
  (1239, 5, 10, 33, 0, 9, 7, 32, 9, 6, 9),
  (1240, 4, 4, 34, 6, 10, 5, 17, 1, 30, 12),
  (1241, 0, 4, 0, 35, 12, 0, 4, 28, 21, 12),
  (1242, 2, 12, 27, 19, 12, 2, 35, 0, 3, 7),
  (1243, 0, 27, 17, 15, 11, 1, 7, 34, 6, 10),
  (1244, 3, 1, 0, 35, 12, 3, 1, 28, 21, 12),
  (1245, 1, 21, 19, 21, 12, 2, 24, 25, 6, 10),
  (1246, 0, 34, 9, 3, 8, 4, 10, 33, 5, 10),
  (1247, 1, 19, 22, 20, 12, 1, 32, 14, 5, 9),
  (1248, 0, 8, 28, 20, 12, 0, 28, 20, 8, 10),
  (1249, 0, 9, 32, 12, 11, 0, 22, 27, 6, 10)
  ]

lemma witChunk_20_ok : witChunk_20.all checkWit = true := by
  decide +kernel

lemma witChunk_20_ns :
    witChunk_20.map (fun t => t.1) = (List.range 50).map (· + 1200) := by
  decide +kernel


def witChunk_21 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1250, 0, 29, 20, 3, 9, 2, 16, 25, 19, 12),
  (1251, 0, 35, 5, 1, 7, 1, 15, 0, 32, 12),
  (1252, 1, 21, 5, 28, 12, 1, 31, 0, 17, 10),
  (1253, 0, 18, 23, 20, 12, 1, 17, 1, 31, 12),
  (1254, 0, 26, 23, 7, 10, 2, 15, 30, 11, 11),
  (1255, 1, 22, 25, 12, 11, 1, 24, 26, 1, 9),
  (1256, 0, 8, 34, 6, 10, 0, 32, 6, 14, 10),
  (1257, 0, 20, 4, 29, 12, 0, 22, 17, 22, 12),
  (1258, 2, 17, 31, 0, 9, 2, 20, 3, 29, 12),
  (1259, 0, 23, 27, 1, 9, 0, 27, 1, 23, 11),
  (1260, 3, 4, 35, 1, 9, 6, 2, 28, 20, 12),
  (1261, 0, 21, 26, 12, 11, 1, 13, 27, 19, 12),
  (1262, 0, 22, 7, 27, 12, 0, 27, 23, 2, 9),
  (1263, 3, 10, 32, 11, 11, 3, 26, 20, 13, 11),
  (1264, 1, 2, 33, 13, 11, 1, 6, 35, 1, 9),
  (1265, 0, 29, 10, 18, 11, 0, 32, 4, 15, 10),
  (1266, 0, 29, 8, 19, 11, 0, 31, 17, 4, 9),
  (1267, 0, 3, 33, 13, 11, 1, 19, 2, 30, 12),
  (1268, 0, 0, 28, 22, 12, 0, 32, 10, 12, 10),
  (1269, 0, 33, 12, 6, 9, 2, 18, 24, 19, 12),
  (1270, 0, 30, 17, 9, 10, 4, 6, 29, 19, 12),
  (1271, 1, 6, 33, 12, 11, 1, 23, 8, 26, 12),
  (1272, 1, 30, 19, 3, 9, 3, 23, 7, 26, 12),
  (1273, 4, 26, 23, 6, 10, 4, 29, 12, 16, 11),
  (1274, 0, 29, 12, 17, 11, 0, 35, 7, 0, 7),
  (1275, 0, 7, 35, 1, 9, 5, 15, 26, 18, 12),
  (1276, 1, 15, 32, 5, 10, 1, 35, 0, 7, 8),
  (1277, 0, 6, 29, 20, 12, 0, 29, 6, 20, 11),
  (1278, 0, 2, 35, 7, 10, 0, 25, 22, 13, 11),
  (1279, 1, 16, 30, 11, 11, 1, 35, 6, 4, 8),
  (1280, 0, 16, 0, 32, 12, 0, 32, 16, 0, 8),
  (1281, 0, 34, 11, 2, 8, 2, 24, 11, 24, 12),
  (1282, 0, 7, 33, 12, 11, 1, 16, 32, 0, 9),
  (1283, 3, 32, 15, 4, 9, 6, 29, 9, 17, 11),
  (1284, 0, 20, 22, 20, 12, 0, 32, 2, 16, 10),
  (1285, 1, 1, 29, 21, 12, 1, 9, 29, 19, 12),
  (1286, 0, 2, 29, 21, 12, 0, 14, 27, 19, 12),
  (1287, 1, 14, 33, 0, 9, 1, 18, 31, 0, 9),
  (1288, 0, 24, 26, 6, 10, 1, 5, 35, 6, 10),
  (1289, 0, 12, 28, 19, 12, 0, 32, 12, 11, 10),
  (1290, 2, 0, 29, 21, 12, 2, 21, 29, 0, 9),
  (1291, 1, 12, 32, 11, 11, 2, 33, 13, 5, 9),
  (1292, 2, 22, 4, 28, 12, 2, 22, 20, 20, 12),
  (1293, 0, 16, 26, 19, 12, 0, 22, 5, 28, 12),
  (1294, 2, 29, 21, 2, 9, 4, 29, 14, 15, 11),
  (1295, 3, 13, 28, 18, 12, 3, 34, 0, 11, 9),
  (1296, 0, 0, 0, 36, 12, 0, 24, 12, 24, 12),
  (1297, 0, 6, 35, 6, 10, 4, 2, 35, 6, 10),
  (1298, 0, 23, 25, 12, 11, 0, 29, 4, 21, 11),
  (1299, 2, 9, 33, 11, 11, 2, 21, 27, 11, 11)
  ]

lemma witChunk_21_ok : witChunk_21.all checkWit = true := by
  decide +kernel

lemma witChunk_21_ns :
    witChunk_21.map (fun t => t.1) = (List.range 50).map (· + 1250) := by
  decide +kernel


def witChunk_22 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1300, 1, 19, 24, 19, 12, 1, 31, 16, 9, 10),
  (1301, 0, 1, 36, 2, 9, 0, 24, 10, 25, 12),
  (1302, 0, 10, 29, 19, 12, 0, 25, 26, 1, 9),
  (1303, 3, 33, 14, 0, 8, 5, 23, 18, 20, 12),
  (1304, 0, 20, 2, 30, 12, 1, 11, 34, 5, 10),
  (1305, 0, 16, 32, 5, 10, 2, 6, 30, 19, 12),
  (1306, 1, 28, 18, 14, 11, 1, 36, 2, 2, 7),
  (1307, 0, 15, 31, 11, 11, 1, 20, 28, 11, 11),
  (1308, 3, 23, 19, 20, 12, 3, 29, 20, 7, 10),
  (1309, 1, 21, 29, 5, 10, 1, 33, 7, 13, 10),
  (1310, 0, 14, 33, 5, 10, 0, 17, 30, 11, 11),
  (1311, 1, 3, 30, 20, 12, 5, 6, 35, 0, 9),
  (1312, 1, 7, 30, 19, 12, 1, 10, 33, 11, 11),
  (1313, 0, 17, 32, 0, 9, 0, 32, 0, 17, 10),
  (1314, 0, 13, 32, 11, 11, 0, 15, 33, 0, 9),
  (1315, 1, 4, 36, 1, 9, 1, 28, 0, 23, 11),
  (1316, 0, 4, 30, 20, 12, 0, 24, 8, 26, 12),
  (1317, 0, 28, 22, 7, 10, 2, 3, 34, 12, 11),
  (1318, 1, 4, 34, 12, 11, 3, 30, 12, 16, 11),
  (1319, 3, 1, 30, 20, 12, 3, 2, 36, 1, 9),
  (1320, 0, 32, 14, 10, 10, 4, 8, 30, 18, 12),
  (1321, 2, 23, 28, 0, 9, 4, 17, 30, 10, 11),
  (1322, 0, 5, 36, 1, 9, 0, 19, 31, 0, 9),
  (1323, 0, 19, 29, 11, 11, 3, 9, 30, 18, 12),
  (1324, 1, 19, 0, 31, 12, 1, 25, 11, 24, 12),
  (1325, 0, 5, 34, 12, 11, 0, 8, 30, 19, 12),
  (1326, 0, 1, 34, 13, 11, 0, 34, 13, 1, 8),
  (1327, 1, 0, 34, 13, 11, 1, 10, 35, 0, 9),
  (1328, 3, 19, 25, 18, 12, 3, 33, 10, 11, 10),
  (1329, 0, 29, 2, 22, 11, 0, 29, 22, 2, 9),
  (1330, 2, 35, 4, 9, 9, 4, 1, 36, 1, 9),
  (1331, 0, 11, 33, 11, 11, 0, 31, 19, 3, 9),
  (1332, 2, 10, 30, 18, 12, 2, 18, 26, 18, 12),
  (1333, 1, 9, 35, 5, 10, 1, 21, 23, 19, 12),
  (1334, 0, 22, 3, 29, 12, 0, 35, 3, 10, 9),
  (1335, 1, 15, 28, 18, 12, 3, 10, 16, 31, 13),
  (1336, 0, 36, 2, 6, 8, 1, 13, 29, 18, 12),
  (1337, 0, 20, 24, 19, 12, 0, 26, 25, 6, 10),
  (1338, 0, 35, 7, 8, 9, 2, 9, 15, 32, 13),
  (1339, 0, 27, 21, 13, 11, 2, 9, 17, 31, 13),
  (1340, 1, 23, 28, 5, 10, 3, 8, 13, 33, 13),
  (1341, 0, 0, 30, 21, 12, 0, 21, 30, 0, 9),
  (1342, 2, 7, 14, 33, 13, 2, 7, 18, 31, 13),
  (1343, 1, 3, 36, 6, 10, 1, 8, 34, 11, 11),
  (1344, 1, 17, 27, 18, 12, 1, 21, 1, 30, 12),
  (1345, 0, 0, 36, 7, 10, 0, 25, 24, 12, 11),
  (1346, 0, 11, 35, 0, 9, 0, 21, 28, 11, 11),
  (1347, 0, 35, 1, 11, 9, 1, 11, 30, 18, 12),
  (1348, 0, 4, 36, 6, 10, 0, 36, 6, 4, 8),
  (1349, 1, 5, 31, 19, 12, 2, 11, 14, 32, 13)
  ]

lemma witChunk_22_ok : witChunk_22.all checkWit = true := by
  decide +kernel

lemma witChunk_22_ns :
    witChunk_22.map (fun t => t.1) = (List.range 50).map (· + 1300) := by
  decide +kernel


def witChunk_23 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1350, 0, 10, 35, 5, 10, 0, 22, 29, 5, 10),
  (1351, 1, 6, 17, 32, 13, 1, 8, 14, 33, 13),
  (1352, 1, 6, 15, 33, 13, 1, 10, 17, 31, 13),
  (1353, 2, 7, 36, 0, 9, 2, 11, 18, 30, 13),
  (1354, 2, 35, 0, 11, 9, 3, 6, 12, 34, 13),
  (1355, 0, 27, 25, 1, 9, 0, 35, 9, 7, 9),
  (1356, 3, 4, 19, 31, 13, 3, 19, 31, 4, 10),
  (1357, 1, 25, 17, 21, 12, 2, 7, 12, 34, 13),
  (1358, 0, 6, 31, 19, 12, 0, 9, 34, 11, 11),
  (1359, 1, 32, 18, 3, 9, 3, 4, 13, 34, 13),
  (1360, 1, 6, 19, 31, 13, 1, 10, 13, 33, 13),
  (1361, 0, 9, 16, 32, 13, 0, 14, 29, 18, 12),
  (1362, 0, 7, 17, 32, 13, 1, 8, 36, 0, 9),
  (1363, 0, 7, 15, 33, 13, 1, 4, 16, 33, 13),
  (1364, 0, 16, 28, 18, 12, 1, 1, 31, 20, 12),
  (1365, 0, 2, 31, 20, 12, 2, 3, 18, 32, 13),
  (1366, 0, 9, 14, 33, 13, 0, 9, 18, 31, 13),
  (1367, 3, 2, 16, 33, 13, 3, 25, 18, 20, 12),
  (1368, 0, 12, 30, 18, 12, 1, 9, 31, 18, 12),
  (1369, 0, 36, 8, 3, 8, 2, 0, 31, 20, 12),
  (1370, 0, 5, 16, 33, 13, 0, 11, 15, 32, 13),
  (1371, 0, 7, 19, 31, 13, 0, 11, 17, 31, 13),
  (1372, 1, 7, 36, 5, 10, 1, 35, 12, 1, 8),
  (1373, 0, 5, 18, 32, 13, 0, 26, 11, 24, 12),
  (1374, 0, 7, 13, 34, 13, 0, 22, 23, 19, 12),
  (1375, 1, 2, 35, 12, 11, 1, 24, 26, 11, 11),
  (1376, 0, 24, 4, 28, 12, 0, 24, 20, 20, 12),
  (1377, 0, 5, 14, 34, 13, 0, 9, 36, 0, 9),
  (1378, 0, 3, 35, 12, 11, 0, 37, 0, 3, 7),
  (1379, 0, 3, 37, 1, 9, 0, 11, 13, 33, 13),
  (1380, 3, 4, 11, 35, 13, 3, 4, 35, 11, 11),
  (1381, 0, 9, 12, 34, 13, 0, 9, 20, 30, 13),
  (1382, 0, 11, 19, 30, 13, 0, 26, 9, 25, 12),
  (1383, 3, 2, 20, 31, 13, 5, 12, 10, 33, 13),
  (1384, 1, 2, 17, 33, 13, 1, 6, 11, 35, 13),
  (1385, 0, 8, 36, 5, 10, 0, 10, 31, 18, 12),
  (1386, 0, 5, 20, 31, 13, 0, 13, 16, 31, 13),
  (1387, 0, 3, 17, 33, 13, 1, 2, 15, 34, 13),
  (1388, 1, 25, 19, 20, 12, 3, 0, 37, 1, 9),
  (1389, 0, 13, 14, 32, 13, 2, 15, 16, 30, 13),
  (1390, 0, 3, 15, 34, 13, 0, 7, 21, 30, 13),
  (1391, 1, 2, 19, 32, 13, 1, 8, 10, 35, 13),
  (1392, 1, 21, 25, 18, 12, 2, 6, 32, 18, 12),
  (1393, 0, 13, 18, 30, 13, 2, 12, 35, 4, 10),
  (1394, 0, 3, 19, 32, 13, 0, 5, 12, 35, 13),
  (1395, 0, 7, 11, 35, 13, 0, 7, 35, 11, 11),
  (1396, 0, 28, 24, 6, 10, 1, 3, 32, 19, 12),
  (1397, 1, 33, 15, 9, 10, 2, 2, 32, 19, 12),
  (1398, 0, 11, 11, 34, 13, 0, 34, 11, 11, 10),
  (1399, 1, 7, 32, 18, 12, 1, 15, 34, 4, 10)
  ]

lemma witChunk_23_ok : witChunk_23.all checkWit = true := by
  decide +kernel

lemma witChunk_23_ns :
    witChunk_23.map (fun t => t.1) = (List.range 50).map (· + 1350) := by
  decide +kernel


def witChunk_24 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1400, 0, 20, 26, 18, 12, 0, 36, 10, 2, 8),
  (1401, 0, 4, 32, 19, 12, 0, 26, 7, 26, 12),
  (1402, 0, 13, 12, 33, 13, 0, 27, 23, 12, 11),
  (1403, 0, 3, 13, 35, 13, 0, 11, 21, 29, 13),
  (1404, 1, 27, 12, 23, 12, 3, 1, 32, 19, 12),
  (1405, 0, 37, 6, 0, 7, 1, 37, 3, 5, 8),
  (1406, 0, 9, 10, 35, 13, 0, 9, 22, 29, 13),
  (1407, 1, 6, 37, 0, 9, 1, 26, 27, 0, 9),
  (1408, 1, 1, 37, 6, 10, 1, 2, 21, 31, 13),
  (1409, 0, 2, 37, 6, 10, 0, 5, 22, 30, 13),
  (1410, 0, 13, 20, 29, 13, 0, 29, 20, 13, 11),
  (1411, 0, 3, 21, 31, 13, 0, 15, 15, 31, 13),
  (1412, 0, 8, 32, 18, 12, 0, 32, 18, 8, 10),
  (1413, 0, 1, 16, 34, 13, 0, 17, 32, 10, 11),
  (1414, 0, 1, 18, 33, 13, 0, 15, 17, 30, 13),
  (1415, 1, 0, 18, 33, 13, 1, 6, 9, 36, 13),
  (1416, 1, 15, 30, 17, 12, 3, 37, 2, 5, 8),
  (1417, 2, 7, 8, 36, 13, 2, 7, 24, 28, 13),
  (1418, 0, 7, 37, 0, 9, 0, 15, 13, 32, 13),
  (1419, 0, 7, 23, 29, 13, 0, 35, 13, 5, 9),
  (1420, 1, 21, 31, 4, 10, 1, 25, 3, 28, 12),
  (1421, 0, 5, 10, 36, 13, 0, 24, 2, 29, 12),
  (1422, 0, 1, 14, 35, 13, 0, 19, 31, 10, 11),
  (1423, 1, 0, 14, 35, 13, 1, 2, 11, 36, 13),
  (1424, 0, 0, 32, 20, 12, 1, 26, 25, 11, 11),
  (1425, 0, 1, 20, 32, 13, 0, 13, 10, 34, 13),
  (1426, 0, 3, 11, 36, 13, 0, 7, 9, 36, 13),
  (1427, 0, 11, 9, 35, 13, 0, 15, 19, 29, 13),
  (1428, 0, 16, 34, 4, 10, 1, 27, 16, 21, 12),
  (1429, 0, 18, 33, 4, 10, 1, 25, 21, 19, 12),
  (1430, 0, 6, 37, 5, 10, 0, 26, 5, 27, 12),
  (1431, 1, 23, 0, 30, 12, 1, 23, 24, 18, 12),
  (1432, 1, 27, 26, 5, 10, 1, 30, 19, 13, 11),
  (1433, 0, 22, 25, 18, 12, 4, 25, 26, 10, 11),
  (1434, 0, 11, 23, 28, 13, 1, 36, 10, 6, 9),
  (1435, 0, 15, 11, 33, 13, 1, 2, 23, 30, 13),
  (1436, 1, 11, 32, 17, 12, 1, 19, 28, 17, 12),
  (1437, 0, 13, 22, 28, 13, 0, 14, 35, 4, 10),
  (1438, 0, 3, 23, 30, 13, 2, 1, 23, 30, 13),
  (1439, 1, 35, 4, 14, 10, 3, 2, 24, 29, 13),
  (1440, 0, 20, 32, 4, 10, 1, 5, 33, 18, 12),
  (1441, 0, 1, 12, 36, 13, 0, 1, 36, 12, 11),
  (1442, 0, 5, 24, 29, 13, 0, 5, 36, 11, 11),
  (1443, 1, 27, 6, 26, 12, 2, 9, 25, 27, 13),
  (1444, 1, 33, 17, 8, 10, 3, 16, 9, 33, 13),
  (1445, 0, 16, 30, 17, 12, 0, 17, 16, 30, 13),
  (1446, 0, 1, 22, 31, 13, 0, 1, 38, 1, 9),
  (1447, 1, 0, 22, 31, 13, 1, 0, 38, 1, 9),
  (1448, 1, 35, 10, 11, 10, 3, 27, 5, 26, 12),
  (1449, 0, 6, 33, 18, 12, 2, 28, 9, 24, 12)
  ]

lemma witChunk_24_ok : witChunk_24.all checkWit = true := by
  decide +kernel

lemma witChunk_24_ns :
    witChunk_24.map (fun t => t.1) = (List.range 50).map (· + 1400) := by
  decide +kernel


def witChunk_25 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1450, 0, 15, 21, 28, 13, 2, 3, 8, 37, 13),
  (1451, 1, 4, 8, 37, 13, 1, 12, 24, 27, 13),
  (1452, 3, 4, 7, 37, 13, 3, 7, 37, 4, 10),
  (1453, 1, 1, 33, 19, 12, 2, 7, 36, 10, 11),
  (1454, 0, 2, 33, 19, 12, 0, 17, 18, 29, 13),
  (1455, 1, 27, 18, 20, 12, 3, 2, 8, 37, 13),
  (1456, 0, 12, 36, 4, 10, 1, 2, 9, 37, 13),
  (1457, 0, 12, 32, 17, 12, 0, 17, 12, 32, 13),
  (1458, 0, 5, 8, 37, 13, 0, 7, 25, 28, 13),
  (1459, 0, 3, 9, 37, 13, 2, 1, 9, 37, 13),
  (1460, 0, 28, 10, 24, 12, 3, 15, 31, 16, 12),
  (1461, 0, 22, 31, 4, 10, 1, 9, 33, 17, 12),
  (1462, 0, 15, 9, 34, 13, 0, 34, 15, 9, 10),
  (1463, 3, 12, 25, 26, 13, 3, 17, 30, 16, 12),
  (1464, 0, 28, 14, 22, 12, 3, 35, 11, 10, 10),
  (1465, 0, 30, 23, 6, 10, 2, 19, 14, 30, 13),
  (1466, 0, 11, 7, 36, 13, 0, 35, 15, 4, 9),
  (1467, 0, 7, 7, 37, 13, 1, 36, 12, 5, 9),
  (1468, 1, 9, 37, 4, 10, 3, 0, 9, 37, 13),
  (1469, 0, 5, 38, 0, 9, 0, 26, 3, 28, 12),
  (1470, 0, 1, 10, 37, 13, 0, 23, 29, 10, 11),
  (1471, 1, 0, 10, 37, 13, 1, 8, 6, 37, 13),
  (1472, 1, 2, 25, 29, 13, 1, 14, 7, 35, 13),
  (1473, 0, 17, 20, 28, 13, 0, 20, 28, 17, 12),
  (1474, 0, 13, 24, 27, 13, 2, 19, 12, 31, 13),
  (1475, 0, 3, 25, 29, 13, 0, 11, 25, 27, 13),
  (1476, 0, 24, 0, 30, 12, 0, 24, 24, 18, 12),
  (1477, 0, 1, 24, 30, 13, 0, 9, 36, 10, 11),
  (1478, 0, 10, 33, 17, 12, 0, 17, 10, 33, 13),
  (1479, 3, 16, 7, 34, 13, 3, 16, 23, 26, 13),
  (1480, 0, 0, 38, 6, 10, 1, 3, 38, 5, 10),
  (1481, 0, 28, 16, 21, 12, 0, 38, 1, 6, 8),
  (1482, 0, 37, 8, 7, 9, 3, 2, 26, 28, 13),
  (1483, 0, 15, 23, 27, 13, 1, 28, 24, 11, 11),
  (1484, 1, 25, 29, 4, 10, 2, 14, 32, 16, 12),
  (1485, 0, 4, 38, 5, 10, 0, 5, 26, 28, 13),
  (1486, 0, 9, 6, 37, 13, 0, 9, 26, 27, 13),
  (1487, 1, 30, 21, 12, 11, 3, 8, 27, 26, 13),
  (1488, 2, 18, 30, 16, 12, 2, 38, 0, 6, 8),
  (1489, 0, 33, 12, 16, 11, 2, 6, 34, 17, 12),
  (1490, 0, 37, 0, 11, 9, 4, 9, 36, 9, 11),
  (1491, 0, 19, 13, 31, 13, 0, 19, 17, 29, 13),
  (1492, 0, 24, 30, 4, 10, 0, 36, 14, 0, 8),
  (1493, 0, 33, 20, 2, 9, 1, 29, 11, 23, 12),
  (1494, 2, 9, 27, 26, 13, 2, 15, 6, 35, 13),
  (1495, 1, 16, 34, 9, 11, 3, 10, 36, 9, 11),
  (1496, 0, 4, 34, 18, 12, 0, 28, 6, 26, 12),
  (1497, 2, 3, 6, 38, 13, 2, 12, 33, 16, 12),
  (1498, 1, 4, 6, 38, 13, 1, 12, 26, 26, 13),
  (1499, 0, 3, 37, 11, 11, 0, 15, 7, 35, 13)
  ]

lemma witChunk_25_ok : witChunk_25.all checkWit = true := by
  decide +kernel

lemma witChunk_25_ns :
    witChunk_25.map (fun t => t.1) = (List.range 50).map (· + 1450) := by
  decide +kernel

def witChunk_26 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1500, 1, 29, 9, 24, 12, 3, 20, 11, 31, 13),
  (1501, 0, 13, 6, 36, 13, 0, 36, 6, 13, 10),
  (1502, 0, 3, 7, 38, 13, 0, 17, 22, 27, 13),
  (1503, 3, 4, 5, 38, 13, 3, 4, 37, 10, 11),
  (1504, 0, 36, 8, 12, 10, 1, 14, 35, 9, 11),
  (1505, 0, 5, 6, 38, 13, 0, 33, 4, 20, 11),
  (1506, 0, 19, 11, 32, 13, 0, 19, 19, 28, 13),
  (1507, 0, 7, 27, 27, 13, 1, 6, 5, 38, 13),
  (1508, 0, 28, 18, 20, 12, 0, 36, 4, 14, 10),
  (1509, 0, 1, 8, 38, 13, 0, 8, 34, 17, 12),
  (1510, 0, 33, 14, 15, 11, 1, 0, 8, 38, 13),
  (1511, 1, 7, 38, 4, 10, 1, 32, 22, 1, 9),
  (1512, 3, 27, 21, 18, 12, 4, 0, 34, 18, 12),
  (1513, 2, 27, 26, 10, 11, 2, 31, 20, 12, 11),
  (1514, 2, 11, 4, 37, 13, 2, 28, 19, 19, 12),
  (1515, 0, 11, 5, 37, 13, 2, 21, 15, 29, 13),
  (1516, 1, 13, 33, 16, 12, 3, 12, 27, 25, 13),
  (1517, 0, 0, 34, 19, 12, 0, 29, 26, 0, 9),
  (1518, 0, 1, 26, 29, 13, 0, 7, 5, 38, 13),
  (1519, 1, 0, 26, 29, 13, 1, 2, 27, 28, 13),
  (1520, 2, 10, 34, 16, 12, 2, 38, 8, 2, 8),
  (1521, 0, 13, 26, 26, 13, 6, 2, 34, 17, 12),
  (1522, 0, 3, 27, 28, 13, 2, 1, 27, 28, 13),
  (1523, 0, 35, 17, 3, 9, 1, 12, 36, 9, 11),
  (1524, 0, 8, 38, 4, 10, 3, 16, 5, 35, 13),
  (1525, 0, 36, 2, 15, 10, 1, 17, 35, 3, 10),
  (1526, 0, 11, 27, 26, 13, 0, 15, 25, 26, 13),
  (1527, 1, 2, 39, 0, 9, 1, 30, 25, 0, 9),
  (1528, 1, 19, 34, 3, 10, 1, 22, 31, 9, 11),
  (1529, 0, 26, 23, 18, 12, 0, 28, 4, 27, 12),
  (1530, 0, 3, 39, 0, 9, 2, 1, 39, 0, 9),
  (1531, 0, 15, 35, 9, 11, 0, 19, 9, 33, 13),
  (1532, 1, 15, 36, 3, 10, 1, 29, 17, 20, 12),
  (1533, 0, 26, 29, 4, 10, 2, 39, 0, 2, 7),
  (1534, 0, 33, 2, 21, 11, 2, 15, 26, 25, 13),
  (1535, 1, 11, 34, 16, 12, 1, 34, 11, 16, 11),
  (1536, 0, 16, 32, 16, 12, 1, 38, 3, 9, 9),
  (1537, 0, 21, 14, 30, 13, 2, 28, 27, 4, 10),
  (1538, 0, 5, 28, 27, 13, 0, 21, 16, 29, 13),
  (1539, 1, 27, 22, 18, 12, 2, 9, 37, 9, 11),
  (1540, 0, 36, 12, 10, 10, 1, 21, 29, 16, 12),
  (1541, 0, 9, 4, 38, 13, 0, 9, 28, 26, 13),
  (1542, 2, 9, 3, 38, 13, 3, 22, 16, 28, 13),
  (1543, 3, 18, 24, 25, 13, 3, 33, 20, 6, 10),
  (1544, 0, 32, 22, 6, 10, 1, 29, 5, 26, 12),
  (1545, 0, 28, 20, 19, 12, 2, 15, 4, 36, 13),
  (1546, 0, 13, 36, 9, 11, 0, 15, 5, 36, 13),
  (1547, 1, 35, 16, 8, 10, 1, 38, 1, 10, 9),
  (1548, 2, 30, 8, 24, 12, 3, 7, 35, 16, 12),
  (1549, 0, 21, 18, 28, 13, 1, 1, 39, 5, 10)
  ]

lemma witChunk_26_ok : witChunk_26.all checkWit = true := by
  decide +kernel

lemma witChunk_26_ns :
    witChunk_26.map (fun t => t.1) = (List.range 50).map (· + 1500) := by
  decide +kernel

def witChunk_27 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1550, 0, 2, 39, 5, 10, 0, 6, 35, 17, 12),
  (1551, 3, 4, 29, 26, 13, 3, 29, 4, 26, 12),
  (1552, 0, 36, 0, 16, 10, 1, 1, 35, 18, 12),
  (1553, 0, 2, 35, 18, 12, 0, 30, 13, 22, 12),
  (1554, 0, 13, 4, 37, 13, 2, 0, 39, 5, 10),
  (1555, 0, 3, 5, 39, 13, 1, 4, 4, 39, 13),
  (1556, 0, 12, 34, 16, 12, 0, 20, 30, 16, 12),
  (1557, 0, 30, 9, 24, 12, 2, 0, 35, 18, 12),
  (1558, 0, 1, 6, 39, 13, 0, 18, 35, 3, 10),
  (1559, 1, 0, 6, 39, 13, 1, 16, 26, 25, 13),
  (1560, 7, 9, 34, 15, 12, 8, 28, 18, 18, 12),
  (1561, 0, 16, 36, 3, 10, 2, 3, 38, 10, 11),
  (1562, 0, 5, 4, 39, 13, 1, 4, 38, 10, 11),
  (1563, 1, 36, 16, 3, 9, 1, 38, 9, 6, 9),
  (1564, 1, 5, 39, 4, 10, 1, 9, 35, 16, 12),
  (1565, 0, 20, 34, 3, 10, 0, 21, 10, 32, 13),
  (1566, 0, 1, 38, 11, 11, 0, 7, 29, 26, 13),
  (1567, 1, 0, 38, 11, 11, 1, 34, 3, 20, 11),
  (1568, 1, 6, 3, 39, 13, 1, 10, 29, 25, 13),
  (1569, 0, 1, 28, 28, 13, 0, 5, 38, 10, 11),
  (1570, 0, 21, 20, 27, 13, 1, 0, 28, 28, 13),
  (1571, 0, 11, 37, 9, 11, 0, 23, 31, 9, 11),
  (1572, 0, 28, 2, 28, 12, 1, 27, 0, 29, 12),
  (1573, 0, 6, 39, 4, 10, 0, 33, 0, 22, 11),
  (1574, 0, 11, 3, 38, 13, 0, 14, 37, 3, 10),
  (1575, 3, 25, 26, 16, 12, 3, 34, 20, 1, 9),
  (1576, 1, 2, 29, 27, 13, 1, 11, 38, 3, 10),
  (1577, 2, 11, 2, 38, 13, 2, 23, 16, 28, 13),
  (1578, 0, 13, 28, 25, 13, 2, 16, 33, 15, 12),
  (1579, 0, 3, 29, 27, 13, 0, 7, 3, 39, 13),
  (1580, 5, 35, 16, 7, 10, 6, 26, 24, 16, 12),
  (1581, 0, 10, 35, 16, 12, 0, 22, 29, 16, 12),
  (1582, 0, 22, 33, 3, 10, 0, 33, 18, 13, 11),
  (1583, 3, 18, 4, 35, 13, 3, 29, 20, 18, 12),
  (1584, 0, 28, 28, 4, 10, 3, 21, 30, 15, 12),
  (1585, 2, 14, 34, 15, 12, 4, 18, 35, 2, 10),
  (1586, 0, 31, 25, 0, 9, 2, 17, 35, 8, 11),
  (1587, 0, 11, 29, 25, 13, 2, 21, 7, 33, 13),
  (1588, 1, 29, 27, 4, 10, 3, 0, 29, 27, 13),
  (1589, 0, 30, 17, 20, 12, 2, 19, 34, 8, 11),
  (1590, 0, 17, 26, 25, 13, 0, 26, 25, 17, 12),
  (1591, 1, 8, 2, 39, 13, 1, 8, 30, 25, 13),
  (1592, 0, 28, 22, 18, 12, 1, 31, 10, 23, 12),
  (1593, 2, 3, 30, 26, 13, 2, 15, 28, 24, 13),
  (1594, 0, 21, 8, 33, 13, 1, 4, 30, 26, 13),
  (1595, 0, 23, 15, 29, 13, 0, 35, 9, 17, 11),
  (1596, 1, 3, 36, 17, 12, 1, 27, 24, 17, 12),
  (1597, 0, 12, 38, 3, 10, 1, 25, 31, 3, 10),
  (1598, 0, 23, 13, 30, 13, 0, 35, 7, 18, 11),
  (1599, 3, 20, 5, 34, 13, 3, 34, 16, 13, 11)
  ]

lemma witChunk_27_ok : witChunk_27.all checkWit = true := by
  decide +kernel

lemma witChunk_27_ns :
    witChunk_27.map (fun t => t.1) = (List.range 50).map (· + 1550) := by
  decide +kernel

def witChunk_28 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1600, 1, 26, 29, 9, 11, 1, 31, 14, 21, 12),
  (1601, 0, 1, 40, 0, 9, 0, 4, 36, 17, 12),
  (1602, 0, 23, 17, 28, 13, 0, 35, 11, 16, 11),
  (1603, 0, 15, 3, 37, 13, 1, 7, 36, 16, 12),
  (1604, 3, 1, 36, 17, 12, 3, 8, 1, 39, 13),
  (1605, 1, 17, 33, 15, 12, 2, 11, 30, 24, 13),
  (1606, 0, 9, 2, 39, 13, 0, 9, 30, 25, 13),
  (1607, 1, 40, 2, 1, 7, 3, 12, 1, 38, 13),
  (1608, 1, 15, 34, 15, 12, 1, 29, 21, 18, 12),
  (1609, 0, 24, 32, 3, 10, 2, 39, 4, 8, 9),
  (1610, 0, 39, 5, 8, 9, 2, 13, 37, 8, 11),
  (1611, 0, 19, 5, 35, 13, 0, 19, 25, 25, 13),
  (1612, 1, 19, 32, 15, 12, 1, 25, 27, 16, 12),
  (1613, 0, 38, 13, 0, 8, 1, 9, 39, 3, 10),
  (1614, 2, 39, 2, 9, 9, 2, 39, 6, 7, 9),
  (1615, 1, 2, 3, 40, 13, 1, 14, 29, 24, 13),
  (1616, 0, 8, 36, 16, 12, 0, 24, 28, 16, 12),
  (1617, 0, 1, 4, 40, 13, 0, 13, 2, 38, 13),
  (1618, 0, 3, 3, 40, 13, 1, 0, 4, 40, 13),
  (1619, 0, 23, 19, 27, 13, 0, 35, 13, 15, 11),
  (1620, 0, 0, 36, 18, 12, 3, 4, 31, 25, 13),
  (1621, 1, 13, 35, 15, 12, 1, 37, 13, 9, 10),
  (1622, 0, 30, 19, 19, 12, 0, 39, 1, 10, 9),
  (1623, 5, 6, 31, 24, 13, 5, 12, 30, 23, 13),
  (1624, 1, 6, 31, 25, 13, 1, 10, 1, 39, 13),
  (1625, 0, 0, 40, 5, 10, 0, 28, 0, 29, 12),
  (1626, 1, 36, 18, 2, 9, 2, 9, 31, 24, 13),
  (1627, 1, 2, 39, 10, 11, 1, 3, 40, 4, 10),
  (1628, 1, 29, 1, 28, 12, 2, 2, 40, 4, 10),
  (1629, 0, 5, 2, 40, 13, 0, 40, 2, 5, 8),
  (1630, 0, 1, 30, 27, 13, 0, 3, 39, 10, 11),
  (1631, 1, 0, 30, 27, 13, 1, 14, 37, 8, 11),
  (1632, 0, 4, 40, 4, 10, 0, 40, 4, 4, 8),
  (1633, 0, 21, 6, 34, 13, 0, 33, 20, 12, 11),
  (1634, 0, 23, 9, 32, 13, 0, 35, 3, 20, 11),
  (1635, 0, 7, 31, 25, 13, 2, 5, 39, 9, 11),
  (1636, 0, 40, 0, 6, 8, 3, 4, 39, 9, 11),
  (1637, 0, 16, 34, 15, 12, 0, 38, 7, 12, 10),
  (1638, 0, 18, 33, 15, 12, 0, 30, 3, 27, 12),
  (1639, 1, 6, 1, 40, 13, 1, 10, 31, 24, 13),
  (1640, 1, 6, 39, 9, 11, 1, 22, 23, 25, 13),
  (1641, 2, 30, 2, 27, 12, 4, 18, 33, 14, 12),
  (1642, 0, 15, 29, 24, 13, 0, 21, 24, 25, 13),
  (1643, 0, 11, 1, 39, 13, 1, 2, 31, 26, 13),
  (1644, 1, 11, 36, 15, 12, 3, 16, 1, 37, 13),
  (1645, 0, 13, 30, 24, 13, 0, 30, 27, 4, 10),
  (1646, 0, 3, 31, 26, 13, 0, 14, 35, 15, 12),
  (1647, 3, 37, 14, 8, 10, 5, 34, 21, 0, 9),
  (1648, 1, 31, 18, 19, 12, 4, 0, 40, 4, 10),
  (1649, 0, 17, 28, 24, 13, 0, 17, 36, 8, 11)
  ]

lemma witChunk_28_ok : witChunk_28.all checkWit = true := by
  decide +kernel

lemma witChunk_28_ns :
    witChunk_28.map (fun t => t.1) = (List.range 50).map (· + 1600) := by
  decide +kernel

def witChunk_29 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1650, 0, 7, 1, 40, 13, 0, 19, 35, 8, 11),
  (1651, 0, 7, 39, 9, 11, 0, 27, 29, 9, 11),
  (1652, 0, 32, 12, 22, 12, 1, 5, 37, 16, 12),
  (1653, 0, 32, 10, 23, 12, 2, 6, 40, 3, 10),
  (1654, 1, 12, 38, 8, 11, 1, 20, 26, 24, 13),
  (1655, 1, 31, 4, 26, 12, 1, 31, 26, 4, 10),
  (1656, 1, 23, 30, 15, 12, 5, 2, 39, 9, 11),
  (1657, 2, 7, 0, 40, 13, 2, 7, 32, 24, 13),
  (1658, 0, 11, 31, 24, 13, 0, 15, 37, 8, 11),
  (1659, 2, 29, 27, 9, 11, 2, 33, 21, 11, 11),
  (1660, 1, 7, 40, 3, 10, 1, 37, 15, 8, 10),
  (1661, 0, 6, 37, 16, 12, 0, 21, 34, 8, 11),
  (1662, 0, 2, 37, 17, 12, 0, 17, 2, 37, 13),
  (1663, 1, 19, 36, 2, 10, 1, 27, 26, 16, 12),
  (1664, 0, 32, 8, 24, 12, 1, 17, 37, 2, 10),
  (1665, 0, 12, 36, 15, 12, 0, 25, 16, 28, 13),
  (1666, 0, 19, 3, 36, 13, 0, 19, 27, 24, 13),
  (1667, 0, 23, 7, 33, 13, 0, 35, 1, 21, 11),
  (1668, 0, 40, 8, 2, 8, 4, 12, 36, 14, 12),
  (1669, 0, 25, 12, 30, 13, 0, 36, 18, 7, 10),
  (1670, 0, 15, 1, 38, 13, 0, 22, 31, 15, 12),
  (1671, 3, 2, 32, 25, 13, 3, 10, 32, 23, 13),
  (1672, 1, 21, 35, 2, 10, 4, 40, 6, 2, 8),
  (1673, 0, 8, 40, 3, 10, 2, 28, 25, 16, 12),
  (1674, 0, 5, 32, 25, 13, 2, 9, 39, 8, 11),
  (1675, 1, 15, 38, 2, 10, 1, 36, 4, 19, 11),
  (1676, 3, 20, 27, 23, 13, 3, 36, 19, 1, 9),
  (1677, 0, 13, 38, 8, 11, 1, 9, 37, 15, 12),
  (1678, 0, 25, 18, 27, 13, 4, 21, 26, 23, 13),
  (1679, 3, 13, 36, 14, 12, 3, 21, 32, 14, 12),
  (1680, 0, 32, 16, 20, 12, 1, 38, 15, 3, 9),
  (1681, 0, 9, 0, 40, 13, 0, 9, 32, 24, 13),
  (1682, 0, 21, 4, 35, 13, 0, 23, 33, 8, 11),
  (1683, 0, 23, 23, 25, 13, 0, 35, 17, 13, 11),
  (1684, 2, 18, 34, 14, 12, 3, 36, 3, 19, 11),
  (1685, 0, 30, 1, 28, 12, 0, 32, 6, 25, 12),
  (1686, 0, 1, 2, 41, 13, 0, 25, 10, 31, 13),
  (1687, 1, 0, 2, 41, 13, 1, 10, 39, 8, 11),
  (1688, 1, 2, 1, 41, 13, 1, 14, 31, 23, 13),
  (1689, 2, 23, 24, 24, 13, 2, 39, 12, 4, 9),
  (1690, 0, 13, 0, 39, 13, 1, 36, 14, 14, 11),
  (1691, 0, 3, 1, 41, 13, 1, 23, 34, 2, 10),
  (1692, 2, 30, 0, 28, 12, 3, 16, 37, 7, 11),
  (1693, 0, 21, 26, 24, 13, 0, 28, 30, 3, 10),
  (1694, 0, 10, 37, 15, 12, 0, 33, 22, 11, 11),
  (1695, 3, 34, 20, 11, 11, 7, 38, 12, 3, 9),
  (1696, 1, 13, 39, 2, 10, 1, 18, 1, 37, 13),
  (1697, 0, 18, 37, 2, 10, 0, 37, 18, 2, 9),
  (1698, 2, 3, 0, 41, 13, 2, 3, 40, 9, 11),
  (1699, 1, 4, 0, 41, 13, 1, 4, 40, 9, 11)
  ]

lemma witChunk_29_ok : witChunk_29.all checkWit = true := by
  decide +kernel

lemma witChunk_29_ns :
    witChunk_29.map (fun t => t.1) = (List.range 50).map (· + 1650) := by
  decide +kernel

def witChunk_30 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1700, 0, 20, 36, 2, 10, 1, 1, 41, 4, 10),
  (1701, 0, 1, 32, 26, 13, 0, 1, 40, 10, 11),
  (1702, 1, 0, 32, 26, 13, 1, 0, 40, 10, 11),
  (1703, 1, 6, 33, 24, 13, 1, 24, 6, 33, 13),
  (1704, 0, 16, 38, 2, 10, 3, 11, 37, 14, 12),
  (1705, 2, 0, 41, 4, 10, 4, 17, 30, 22, 13),
  (1706, 0, 5, 0, 41, 13, 0, 5, 40, 9, 11),
  (1707, 2, 9, 33, 23, 13, 2, 21, 27, 23, 13),
  (1708, 1, 39, 4, 13, 10, 1, 39, 8, 11, 10),
  (1709, 0, 32, 18, 19, 12, 1, 37, 17, 7, 10),
  (1710, 0, 23, 5, 34, 13, 0, 34, 23, 5, 10),
  (1711, 1, 3, 38, 16, 12, 3, 18, 0, 37, 13),
  (1712, 1, 17, 35, 14, 12, 1, 30, 27, 9, 11),
  (1713, 0, 22, 35, 2, 10, 0, 25, 8, 32, 13),
  (1714, 0, 7, 33, 24, 13, 2, 4, 41, 3, 10),
  (1715, 0, 15, 31, 23, 13, 1, 19, 34, 14, 12),
  (1716, 0, 4, 38, 16, 12, 0, 28, 26, 16, 12),
  (1717, 1, 5, 41, 3, 10, 1, 41, 5, 3, 8),
  (1718, 0, 17, 30, 23, 13, 0, 30, 23, 17, 12),
  (1719, 1, 15, 36, 14, 12, 3, 1, 38, 16, 12),
  (1720, 1, 2, 33, 25, 13, 1, 7, 38, 15, 12),
  (1721, 0, 14, 39, 2, 10, 2, 7, 40, 8, 11),
  (1722, 0, 13, 32, 23, 13, 0, 37, 8, 17, 11),
  (1723, 0, 3, 33, 25, 13, 1, 36, 16, 13, 11),
  (1724, 1, 29, 25, 16, 12, 3, 33, 16, 19, 12),
  (1725, 0, 37, 10, 16, 11, 5, 33, 15, 19, 12),
  (1726, 0, 6, 41, 3, 10, 2, 15, 38, 7, 11),
  (1727, 1, 11, 40, 2, 10, 1, 40, 10, 5, 9),
  (1728, 1, 21, 33, 14, 12, 5, 3, 38, 15, 12),
  (1729, 0, 37, 6, 18, 11, 2, 40, 11, 0, 8),
  (1730, 0, 23, 25, 24, 13, 0, 35, 19, 12, 11),
  (1731, 0, 19, 1, 37, 13, 0, 19, 29, 23, 13),
  (1732, 0, 36, 20, 6, 10, 1, 33, 25, 4, 10),
  (1733, 0, 0, 38, 17, 12, 0, 8, 38, 15, 12),
  (1734, 0, 25, 22, 25, 13, 2, 39, 14, 3, 9),
  (1735, 3, 12, 33, 22, 13, 5, 39, 8, 10, 10),
  (1736, 0, 24, 34, 2, 10, 1, 13, 37, 14, 12),
  (1737, 2, 27, 10, 30, 13, 2, 27, 18, 26, 13),
  (1738, 0, 27, 15, 28, 13, 0, 37, 12, 15, 11),
  (1739, 0, 11, 33, 23, 13, 0, 27, 13, 29, 13),
  (1740, 1, 27, 28, 15, 12, 2, 30, 24, 16, 12),
  (1741, 0, 21, 2, 36, 13, 1, 33, 5, 25, 12),
  (1742, 0, 26, 29, 15, 12, 2, 7, 34, 23, 13),
  (1743, 3, 20, 29, 22, 13, 5, 26, 21, 24, 13),
  (1744, 0, 40, 12, 0, 8, 1, 18, 37, 7, 11),
  (1745, 0, 9, 40, 8, 11, 0, 18, 35, 14, 12),
  (1746, 0, 37, 4, 19, 11, 2, 21, 1, 36, 13),
  (1747, 0, 27, 17, 27, 13, 1, 20, 36, 7, 11),
  (1748, 0, 12, 40, 2, 10, 0, 16, 36, 14, 12),
  (1749, 2, 3, 34, 24, 13, 2, 34, 12, 21, 12)
  ]

lemma witChunk_30_ok : witChunk_30.all checkWit = true := by
  decide +kernel

lemma witChunk_30_ns :
    witChunk_30.map (fun t => t.1) = (List.range 50).map (· + 1700) := by
  decide +kernel

def witChunk_31 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1750, 0, 25, 6, 33, 13, 0, 27, 11, 30, 13),
  (1751, 1, 8, 34, 23, 13, 1, 16, 38, 7, 11),
  (1752, 0, 20, 34, 14, 12, 3, 7, 41, 2, 10),
  (1753, 2, 19, 30, 22, 13, 4, 6, 41, 2, 10),
  (1754, 0, 21, 28, 23, 13, 0, 27, 31, 8, 11),
  (1755, 0, 39, 15, 3, 9, 3, 28, 13, 28, 13),
  (1756, 1, 31, 28, 3, 10, 2, 34, 24, 4, 10),
  (1757, 0, 5, 34, 24, 13, 0, 32, 2, 27, 12),
  (1758, 3, 10, 34, 22, 13, 3, 34, 22, 10, 11),
  (1759, 1, 27, 32, 2, 10, 3, 24, 3, 34, 13),
  (1760, 1, 22, 35, 7, 11, 2, 34, 14, 20, 12),
  (1761, 0, 14, 37, 14, 12, 0, 34, 11, 22, 12),
  (1762, 1, 40, 12, 4, 9, 2, 27, 8, 31, 13),
  (1763, 0, 23, 3, 35, 13, 1, 11, 38, 14, 12),
  (1764, 3, 28, 11, 29, 13, 3, 31, 23, 16, 12),
  (1765, 0, 1, 0, 42, 13, 0, 33, 24, 10, 11),
  (1766, 0, 9, 34, 23, 13, 0, 27, 19, 26, 13),
  (1767, 3, 10, 40, 7, 11, 3, 26, 32, 7, 11),
  (1768, 1, 2, 41, 9, 11, 1, 9, 41, 2, 10),
  (1769, 0, 22, 33, 14, 12, 0, 26, 33, 2, 10),
  (1770, 0, 37, 20, 1, 9, 2, 4, 39, 15, 12),
  (1771, 0, 3, 41, 9, 11, 0, 27, 9, 31, 13),
  (1772, 3, 17, 36, 13, 12, 3, 39, 13, 8, 10),
  (1773, 0, 37, 2, 20, 11, 1, 5, 39, 15, 12),
  (1774, 2, 21, 29, 22, 13, 2, 41, 7, 6, 9),
  (1775, 1, 42, 3, 0, 7, 5, 26, 5, 32, 13),
  (1776, 1, 33, 3, 26, 12, 1, 33, 19, 18, 12),
  (1777, 0, 25, 24, 24, 13, 2, 18, 38, 1, 10),
  (1778, 2, 5, 41, 8, 11, 2, 11, 40, 7, 11),
  (1779, 0, 19, 37, 7, 11, 3, 4, 41, 8, 11),
  (1780, 0, 0, 42, 4, 10, 0, 40, 6, 12, 10),
  (1781, 0, 2, 39, 16, 12, 0, 30, 25, 16, 12),
  (1782, 0, 1, 34, 25, 13, 0, 6, 39, 15, 12),
  (1783, 1, 0, 34, 25, 13, 1, 6, 41, 8, 11),
  (1784, 0, 12, 38, 14, 12, 1, 3, 42, 3, 10),
  (1785, 0, 10, 41, 2, 10, 0, 40, 4, 13, 10),
  (1786, 0, 21, 36, 7, 11, 1, 12, 34, 22, 13),
  (1787, 0, 23, 27, 23, 13, 0, 35, 21, 11, 11),
  (1788, 3, 4, 35, 23, 13, 3, 13, 40, 1, 10),
  (1789, 0, 4, 42, 3, 10, 0, 42, 3, 4, 8),
  (1790, 0, 42, 1, 5, 8, 4, 7, 35, 22, 13),
  (1791, 3, 8, 35, 22, 13, 5, 11, 18, 36, 14),
  (1792, 1, 6, 35, 23, 13, 1, 26, 5, 33, 13),
  (1793, 0, 28, 28, 15, 12, 6, 8, 19, 36, 14),
  (1794, 0, 7, 41, 8, 11, 0, 37, 16, 13, 11),
  (1795, 0, 15, 39, 7, 11, 0, 27, 21, 25, 13),
  (1796, 0, 24, 32, 14, 12, 3, 11, 19, 36, 14),
  (1797, 0, 17, 32, 22, 13, 0, 25, 4, 34, 13),
  (1798, 0, 15, 33, 22, 13, 0, 42, 5, 3, 8),
  (1799, 3, 9, 16, 38, 14, 3, 26, 4, 33, 13)
  ]

lemma witChunk_31_ok : witChunk_31.all checkWit = true := by
  decide +kernel

lemma witChunk_31_ns :
    witChunk_31.map (fun t => t.1) = (List.range 50).map (· + 1750) := by
  decide +kernel

def witChunk_32 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1800, 0, 40, 2, 14, 10, 0, 40, 10, 10, 10),
  (1801, 2, 10, 18, 37, 14, 4, 6, 17, 38, 14),
  (1802, 0, 27, 7, 32, 13, 2, 8, 19, 37, 14),
  (1803, 0, 7, 35, 23, 13, 0, 23, 35, 7, 11),
  (1804, 1, 41, 11, 0, 8, 2, 10, 20, 36, 14),
  (1805, 0, 29, 30, 8, 11, 0, 36, 22, 5, 10),
  (1806, 0, 19, 31, 22, 13, 0, 34, 5, 25, 12),
  (1807, 1, 2, 35, 24, 13, 1, 24, 2, 35, 13),
  (1808, 0, 32, 0, 28, 12, 1, 19, 38, 1, 10),
  (1809, 0, 13, 34, 22, 13, 2, 8, 21, 36, 14),
  (1810, 0, 3, 35, 24, 13, 0, 21, 0, 37, 13),
  (1811, 1, 10, 35, 22, 13, 1, 22, 29, 22, 13),
  (1812, 0, 28, 32, 2, 10, 1, 35, 12, 21, 12),
  (1813, 1, 9, 19, 37, 14, 1, 17, 39, 1, 10),
  (1814, 0, 39, 17, 2, 9, 2, 29, 17, 26, 13),
  (1815, 5, 42, 1, 0, 7, 9, 40, 2, 7, 9),
  (1816, 1, 9, 17, 38, 14, 1, 11, 18, 37, 14),
  (1817, 0, 10, 39, 14, 12, 0, 32, 28, 3, 10),
  (1818, 0, 13, 40, 7, 11, 2, 8, 15, 39, 14),
  (1819, 1, 7, 18, 38, 14, 1, 7, 42, 2, 10),
  (1820, 1, 7, 20, 37, 14, 1, 9, 21, 36, 14),
  (1821, 0, 29, 14, 28, 13, 1, 33, 1, 27, 12),
  (1822, 3, 18, 38, 6, 11, 4, 6, 23, 35, 14),
  (1823, 1, 11, 16, 38, 14, 1, 35, 14, 20, 12),
  (1824, 2, 6, 22, 36, 14, 2, 14, 18, 36, 14),
  (1825, 0, 21, 30, 22, 13, 0, 40, 0, 15, 10),
  (1826, 0, 23, 1, 36, 13, 0, 29, 12, 29, 13),
  (1827, 1, 27, 30, 14, 12, 2, 17, 33, 21, 13),
  (1828, 1, 7, 16, 39, 14, 1, 13, 19, 36, 14),
  (1829, 1, 9, 15, 39, 14, 1, 13, 17, 37, 14),
  (1830, 0, 10, 19, 37, 14, 0, 11, 35, 22, 13),
  (1831, 1, 7, 22, 36, 14, 3, 9, 24, 34, 14),
  (1832, 0, 8, 18, 38, 14, 0, 8, 42, 2, 10),
  (1833, 0, 8, 20, 37, 14, 0, 10, 17, 38, 14),
  (1834, 0, 27, 23, 24, 13, 2, 4, 17, 39, 14),
  (1835, 2, 29, 19, 25, 13, 3, 32, 27, 8, 11),
  (1836, 1, 3, 40, 15, 12, 3, 7, 13, 40, 14),
  (1837, 0, 10, 21, 36, 14, 0, 12, 18, 37, 14),
  (1838, 4, 26, 31, 13, 12, 4, 34, 19, 17, 12),
  (1839, 1, 35, 6, 24, 12, 1, 42, 3, 8, 9),
  (1840, 0, 12, 20, 36, 14, 1, 11, 14, 39, 14),
  (1841, 0, 4, 40, 15, 12, 0, 6, 19, 38, 14),
  (1842, 2, 3, 36, 23, 13, 2, 12, 13, 39, 14),
  (1843, 0, 27, 5, 33, 13, 1, 4, 36, 23, 13),
  (1844, 0, 8, 22, 36, 14, 0, 12, 16, 38, 14),
  (1845, 0, 20, 38, 1, 10, 2, 3, 42, 8, 11),
  (1846, 0, 1, 42, 9, 11, 0, 6, 17, 39, 14),
  (1847, 1, 0, 42, 9, 11, 1, 7, 14, 40, 14),
  (1848, 1, 42, 1, 9, 9, 3, 7, 25, 34, 14),
  (1849, 2, 4, 15, 40, 14, 2, 4, 23, 36, 14)
  ]

lemma witChunk_32_ok : witChunk_32.all checkWit = true := by
  decide +kernel

lemma witChunk_32_ns :
    witChunk_32.map (fun t => t.1) = (List.range 50).map (· + 1800) := by
  decide +kernel

def witChunk_33 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1850, 0, 5, 36, 23, 13, 2, 16, 19, 35, 14),
  (1851, 0, 11, 41, 7, 11, 0, 43, 1, 1, 7),
  (1852, 1, 5, 15, 40, 14, 1, 5, 23, 36, 14),
  (1853, 0, 5, 42, 8, 11, 0, 12, 22, 35, 14),
  (1854, 0, 10, 23, 35, 14, 0, 14, 17, 37, 14),
  (1855, 1, 3, 20, 38, 14, 1, 11, 24, 34, 14),
  (1856, 0, 0, 40, 16, 12, 0, 32, 24, 16, 12),
  (1857, 0, 16, 40, 1, 10, 2, 2, 18, 39, 14),
  (1858, 0, 39, 9, 16, 11, 0, 43, 3, 0, 7),
  (1859, 0, 39, 7, 17, 11, 1, 28, 32, 7, 11),
  (1860, 0, 4, 20, 38, 14, 0, 8, 14, 40, 14),
  (1861, 0, 4, 18, 39, 14, 0, 6, 15, 40, 14),
  (1862, 0, 2, 43, 3, 10, 0, 14, 21, 35, 14),
  (1863, 3, 1, 20, 38, 14, 3, 17, 20, 34, 14),
  (1864, 1, 3, 22, 37, 14, 1, 9, 25, 34, 14),
  (1865, 0, 8, 24, 35, 14, 0, 14, 15, 38, 14),
  (1866, 0, 29, 8, 31, 13, 0, 29, 20, 25, 13),
  (1867, 0, 27, 33, 7, 11, 0, 39, 11, 15, 11),
  (1868, 1, 35, 4, 25, 12, 2, 2, 16, 40, 14),
  (1869, 0, 4, 22, 37, 14, 0, 10, 13, 40, 14),
  (1870, 0, 39, 5, 18, 11, 2, 7, 42, 7, 11),
  (1871, 1, 43, 2, 4, 8, 3, 42, 8, 5, 9),
  (1872, 0, 4, 16, 40, 14, 1, 42, 9, 5, 9),
  (1873, 0, 1, 36, 24, 13, 0, 24, 36, 1, 10),
  (1874, 1, 0, 36, 24, 13, 1, 24, 0, 36, 13),
  (1875, 1, 35, 18, 18, 12, 3, 1, 16, 40, 14),
  (1876, 0, 12, 24, 34, 14, 0, 16, 18, 36, 14),
  (1877, 1, 5, 13, 41, 14, 1, 5, 25, 35, 14),
  (1878, 0, 14, 41, 1, 10, 0, 22, 35, 13, 12),
  (1879, 1, 8, 42, 7, 11, 1, 38, 17, 12, 11),
  (1880, 0, 28, 30, 14, 12, 0, 36, 10, 22, 12),
  (1881, 0, 10, 25, 34, 14, 0, 14, 23, 34, 14),
  (1882, 1, 20, 38, 6, 11, 1, 36, 22, 10, 11),
  (1883, 0, 27, 25, 23, 13, 0, 39, 19, 1, 9),
  (1884, 2, 2, 24, 36, 14, 2, 18, 16, 36, 14),
  (1885, 0, 42, 11, 0, 8, 1, 1, 19, 39, 14),
  (1886, 0, 2, 19, 39, 14, 0, 6, 13, 41, 14),
  (1887, 1, 38, 21, 0, 9, 3, 4, 37, 22, 13),
  (1888, 0, 4, 24, 36, 14, 0, 12, 12, 40, 14),
  (1889, 0, 2, 21, 38, 14, 0, 6, 43, 2, 10),
  (1890, 0, 37, 20, 11, 11, 2, 0, 19, 39, 14),
  (1891, 0, 15, 35, 21, 13, 0, 19, 33, 21, 13),
  (1892, 0, 36, 14, 20, 12, 1, 1, 17, 40, 14),
  (1893, 0, 2, 17, 40, 14, 0, 4, 14, 41, 14),
  (1894, 0, 9, 42, 7, 11, 0, 27, 3, 34, 13),
  (1895, 3, 17, 12, 38, 14, 3, 17, 38, 12, 12),
  (1896, 0, 8, 26, 34, 14, 0, 16, 14, 38, 14),
  (1897, 2, 0, 17, 40, 14, 2, 18, 14, 37, 14),
  (1898, 2, 29, 5, 32, 13, 3, 18, 34, 20, 13),
  (1899, 2, 9, 37, 21, 13, 3, 16, 35, 20, 13)
  ]

lemma witChunk_33_ok : witChunk_33.all checkWit = true := by
  decide +kernel

lemma witChunk_33_ns :
    witChunk_33.map (fun t => t.1) = (List.range 50).map (· + 1850) := by
  decide +kernel

def witChunk_34 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1900, 3, 19, 15, 36, 14, 3, 19, 39, 0, 10),
  (1901, 0, 24, 34, 13, 12, 0, 29, 6, 32, 13),
  (1902, 0, 2, 23, 37, 14, 0, 7, 37, 22, 13),
  (1903, 1, 42, 11, 4, 9, 3, 21, 38, 0, 10),
  (1904, 1, 2, 37, 23, 13, 1, 5, 41, 14, 12),
  (1905, 0, 40, 16, 7, 10, 2, 12, 27, 32, 14),
  (1906, 0, 13, 36, 21, 13, 0, 21, 32, 21, 13),
  (1907, 0, 3, 37, 23, 13, 1, 35, 2, 26, 12),
  (1908, 0, 36, 6, 24, 12, 2, 6, 10, 42, 14),
  (1909, 0, 12, 26, 33, 14, 0, 12, 42, 1, 10),
  (1910, 0, 2, 15, 41, 14, 0, 2, 41, 15, 12),
  (1911, 3, 28, 25, 22, 13, 5, 36, 22, 9, 11),
  (1912, 1, 3, 26, 35, 14, 1, 5, 11, 42, 14),
  (1913, 0, 6, 41, 14, 12, 0, 12, 40, 13, 12),
  (1914, 0, 29, 32, 7, 11, 0, 31, 13, 28, 13),
  (1915, 0, 31, 15, 27, 13, 0, 39, 15, 13, 11),
  (1916, 1, 35, 20, 17, 12, 1, 37, 23, 4, 10),
  (1917, 0, 4, 26, 35, 14, 0, 14, 11, 40, 14),
  (1918, 0, 10, 27, 33, 14, 0, 18, 15, 37, 14),
  (1919, 1, 2, 43, 8, 11, 1, 3, 12, 42, 14),
  (1920, 2, 2, 12, 42, 14, 2, 18, 12, 38, 14),
  (1921, 0, 0, 20, 39, 14, 0, 6, 11, 42, 14),
  (1922, 0, 3, 43, 8, 11, 0, 39, 1, 20, 11),
  (1923, 0, 31, 11, 29, 13, 0, 43, 5, 7, 9),
  (1924, 0, 0, 18, 40, 14, 0, 4, 12, 42, 14),
  (1925, 0, 2, 25, 36, 14, 0, 12, 10, 41, 14),
  (1926, 0, 31, 17, 26, 13, 3, 22, 32, 20, 13),
  (1927, 1, 15, 10, 40, 14, 1, 15, 26, 32, 14),
  (1928, 0, 0, 22, 38, 14, 0, 8, 10, 42, 14),
  (1929, 2, 0, 25, 36, 14, 2, 11, 42, 6, 11),
  (1930, 4, 31, 19, 24, 13, 6, 16, 9, 39, 14),
  (1931, 0, 11, 37, 21, 13, 0, 23, 31, 21, 13),
  (1932, 2, 18, 24, 32, 14, 2, 18, 40, 0, 10),
  (1933, 0, 42, 5, 12, 10, 1, 9, 41, 13, 12),
  (1934, 0, 23, 37, 6, 11, 0, 26, 33, 13, 12),
  (1935, 3, 37, 8, 22, 12, 3, 40, 11, 14, 11),
  (1936, 1, 1, 13, 42, 14, 1, 6, 43, 7, 11),
  (1937, 0, 0, 16, 41, 14, 0, 2, 13, 42, 14),
  (1938, 2, 20, 21, 33, 14, 2, 21, 33, 20, 13),
  (1939, 1, 26, 35, 6, 11, 1, 44, 0, 1, 7),
  (1940, 1, 17, 25, 32, 14, 1, 37, 13, 20, 12),
  (1941, 0, 28, 34, 1, 10, 0, 34, 23, 16, 12),
  (1942, 0, 15, 41, 6, 11, 0, 18, 23, 33, 14),
  (1943, 1, 31, 28, 14, 12, 3, 25, 34, 12, 12),
  (1944, 0, 36, 18, 18, 12, 1, 42, 13, 3, 9),
  (1945, 0, 0, 24, 37, 14, 0, 0, 44, 3, 10),
  (1946, 0, 29, 4, 33, 13, 0, 29, 24, 23, 13),
  (1947, 0, 7, 43, 7, 11, 0, 31, 19, 25, 13),
  (1948, 1, 9, 29, 32, 14, 1, 39, 20, 5, 10),
  (1949, 0, 14, 27, 32, 14, 0, 20, 18, 35, 14)
  ]

lemma witChunk_34_ok : witChunk_34.all checkWit = true := by
  decide +kernel

lemma witChunk_34_ns :
    witChunk_34.map (fun t => t.1) = (List.range 50).map (· + 1900) := by
  decide +kernel

def witChunk_35 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1950, 0, 10, 41, 13, 12, 0, 10, 43, 1, 10),
  (1951, 1, 3, 28, 34, 14, 1, 3, 44, 2, 10),
  (1952, 0, 12, 28, 32, 14, 0, 20, 16, 36, 14),
  (1953, 0, 5, 38, 22, 13, 0, 37, 22, 10, 11),
  (1954, 0, 39, 17, 12, 11, 1, 16, 36, 20, 13),
  (1955, 0, 27, 1, 35, 13, 0, 43, 9, 5, 9),
  (1956, 0, 4, 28, 34, 14, 0, 4, 44, 2, 10),
  (1957, 0, 25, 36, 6, 11, 1, 1, 27, 35, 14),
  (1958, 0, 2, 27, 35, 14, 0, 14, 9, 41, 14),
  (1959, 3, 1, 28, 34, 14, 3, 1, 44, 2, 10),
  (1960, 0, 0, 14, 42, 14, 0, 40, 18, 6, 10),
  (1961, 0, 42, 1, 14, 10, 0, 44, 0, 5, 8),
  (1962, 0, 39, 21, 0, 9, 2, 0, 27, 35, 14),
  (1963, 1, 19, 24, 32, 14, 1, 19, 40, 0, 10),
  (1964, 1, 7, 8, 43, 14, 1, 21, 15, 36, 14),
  (1965, 0, 4, 10, 43, 14, 0, 10, 29, 32, 14),
  (1966, 0, 6, 9, 43, 14, 0, 6, 29, 33, 14),
  (1967, 1, 14, 37, 20, 13, 1, 32, 10, 29, 13),
  (1968, 2, 6, 30, 32, 14, 2, 14, 42, 0, 10),
  (1969, 0, 13, 42, 6, 11, 2, 10, 30, 31, 14),
  (1970, 2, 8, 7, 43, 14, 4, 41, 16, 1, 9),
  (1971, 0, 31, 7, 31, 13, 0, 31, 31, 7, 11),
  (1972, 0, 0, 26, 36, 14, 0, 12, 8, 42, 14),
  (1973, 0, 18, 25, 32, 14, 0, 20, 22, 33, 14),
  (1974, 0, 1, 38, 23, 13, 0, 2, 11, 43, 14),
  (1975, 1, 0, 38, 23, 13, 1, 7, 30, 32, 14),
  (1976, 0, 4, 42, 14, 12, 0, 36, 2, 26, 12),
  (1977, 0, 8, 8, 43, 14, 0, 28, 32, 13, 12),
  (1978, 0, 31, 21, 24, 13, 1, 28, 34, 6, 11),
  (1979, 2, 41, 17, 1, 9, 3, 1, 42, 14, 12),
  (1980, 2, 26, 36, 0, 10, 2, 42, 12, 8, 10),
  (1981, 0, 36, 26, 3, 10, 1, 9, 7, 43, 14),
  (1982, 2, 31, 22, 23, 13, 3, 42, 14, 2, 9),
  (1983, 5, 3, 30, 32, 14, 5, 12, 42, 5, 11),
  (1984, 1, 7, 42, 13, 12, 1, 11, 30, 31, 14),
  (1985, 0, 17, 36, 20, 13, 0, 36, 20, 17, 12),
  (1986, 0, 19, 35, 20, 13, 0, 43, 11, 4, 9),
  (1987, 1, 10, 43, 6, 11, 1, 38, 21, 10, 11),
  (1988, 0, 8, 30, 32, 14, 0, 20, 12, 38, 14),
  (1989, 0, 0, 42, 15, 12, 0, 18, 39, 12, 12),
  (1990, 0, 27, 35, 6, 11, 0, 30, 33, 1, 10),
  (1991, 1, 15, 42, 0, 10, 3, 17, 28, 30, 14),
  (1992, 3, 23, 17, 34, 14, 4, 0, 42, 14, 12),
  (1993, 0, 0, 12, 43, 14, 2, 10, 6, 43, 14),
  (1994, 0, 15, 37, 20, 13, 2, 8, 31, 31, 14),
  (1995, 1, 42, 15, 2, 9, 2, 5, 39, 21, 13),
  (1996, 1, 13, 41, 12, 12, 1, 21, 23, 32, 14),
  (1997, 0, 8, 42, 13, 12, 0, 21, 34, 20, 13),
  (1998, 0, 10, 7, 43, 14, 0, 14, 29, 31, 14),
  (1999, 3, 18, 36, 19, 13, 5, 12, 38, 19, 13)
  ]

lemma witChunk_35_ok : witChunk_35.all checkWit = true := by
  decide +kernel

lemma witChunk_35_ns :
    witChunk_35.map (fun t => t.1) = (List.range 50).map (· + 1950) := by
  decide +kernel

def witChunk_36 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2000, 0, 16, 40, 12, 12, 0, 20, 24, 32, 14),
  (2001, 0, 1, 44, 8, 11, 0, 2, 29, 34, 14),
  (2002, 1, 0, 44, 8, 11, 1, 24, 32, 20, 13),
  (2003, 0, 39, 19, 11, 11, 1, 4, 44, 7, 11),
  (2004, 0, 32, 28, 14, 12, 2, 14, 6, 42, 14),
  (2005, 0, 4, 30, 33, 14, 0, 12, 30, 31, 14),
  (2006, 0, 11, 43, 6, 11, 0, 34, 25, 15, 12),
  (2007, 3, 2, 44, 7, 11, 3, 9, 42, 12, 12),
  (2008, 1, 11, 6, 43, 14, 1, 21, 11, 38, 14),
  (2009, 0, 0, 28, 35, 14, 0, 14, 7, 42, 14),
  (2010, 0, 5, 44, 7, 11, 0, 31, 5, 32, 13),
  (2011, 0, 7, 39, 21, 13, 0, 27, 29, 21, 13),
  (2012, 1, 5, 7, 44, 14, 1, 5, 31, 32, 14),
  (2013, 0, 13, 38, 20, 13, 0, 38, 13, 20, 12),
  (2014, 0, 3, 39, 22, 13, 0, 18, 27, 31, 14),
  (2015, 1, 35, 28, 2, 10, 1, 43, 8, 10, 10),
  (2016, 0, 4, 8, 44, 14, 0, 24, 36, 12, 12),
  (2017, 0, 33, 12, 28, 13, 2, 28, 35, 0, 10),
  (2018, 0, 23, 33, 20, 13, 0, 35, 27, 8, 11),
  (2019, 0, 31, 23, 23, 13, 1, 44, 0, 9, 9),
  (2020, 0, 16, 42, 0, 10, 0, 24, 38, 0, 10),
  (2021, 0, 2, 9, 44, 14, 0, 6, 7, 44, 14),
  (2022, 0, 10, 31, 31, 14, 0, 22, 13, 37, 14),
  (2023, 1, 7, 6, 44, 14, 1, 10, 39, 20, 13),
  (2024, 1, 43, 2, 13, 10, 3, 17, 6, 41, 14),
  (2025, 0, 36, 0, 27, 12, 0, 40, 20, 5, 10),
  (2026, 0, 37, 24, 9, 11, 0, 45, 0, 1, 7),
  (2027, 0, 43, 13, 3, 9, 1, 15, 6, 42, 14),
  (2028, 1, 35, 24, 15, 12, 3, 5, 32, 31, 14),
  (2029, 0, 12, 6, 43, 14, 0, 45, 2, 0, 7),
  (2030, 0, 30, 31, 13, 12, 0, 33, 10, 29, 13),
  (2031, 1, 11, 42, 12, 12, 1, 27, 34, 12, 12),
  (2032, 1, 1, 45, 2, 10, 1, 13, 31, 30, 14),
  (2033, 0, 2, 45, 2, 10, 0, 29, 34, 6, 11),
  (2034, 2, 24, 15, 35, 14, 2, 24, 19, 33, 14),
  (2035, 2, 21, 35, 19, 13, 3, 9, 44, 0, 10),
  (2036, 0, 0, 10, 44, 14, 0, 8, 6, 44, 14),
  (2037, 0, 20, 26, 31, 14, 0, 22, 23, 32, 14),
  (2038, 0, 33, 18, 25, 13, 0, 33, 30, 7, 11),
  (2039, 1, 23, 22, 32, 14, 1, 26, 31, 20, 13),
  (2040, 5, 30, 1, 33, 13, 5, 42, 15, 1, 9),
  (2041, 4, 12, 4, 43, 14, 4, 12, 32, 29, 14),
  (2042, 0, 11, 39, 20, 13, 2, 4, 43, 13, 12),
  (2043, 3, 28, 29, 20, 13, 3, 37, 20, 16, 12),
  (2044, 1, 9, 5, 44, 14, 1, 23, 12, 37, 14),
  (2045, 0, 14, 43, 0, 10, 0, 26, 35, 12, 12),
  (2046, 0, 41, 2, 19, 11, 0, 41, 14, 13, 11),
  (2047, 1, 11, 32, 30, 14, 1, 16, 42, 5, 11),
  (2048, 1, 1, 43, 14, 12, 1, 34, 29, 7, 11),
  (2049, 0, 2, 43, 14, 12, 0, 8, 32, 31, 14)
  ]

lemma witChunk_36_ok : witChunk_36.all checkWit = true := by
  decide +kernel

lemma witChunk_36_ns :
    witChunk_36.map (fun t => t.1) = (List.range 50).map (· + 2000) := by
  decide +kernel

def witChunk_37 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2050, 2, 4, 45, 1, 10, 2, 20, 39, 11, 12),
  (2051, 2, 13, 43, 5, 11, 2, 41, 1, 19, 11),
  (2052, 0, 12, 42, 12, 12, 3, 13, 4, 43, 14),
  (2053, 0, 9, 44, 6, 11, 0, 33, 8, 30, 13),
  (2054, 0, 2, 31, 33, 14, 0, 6, 43, 13, 12),
  (2055, 3, 25, 16, 34, 14, 3, 32, 23, 22, 13),
  (2056, 0, 0, 30, 34, 14, 0, 16, 6, 42, 14),
  (2057, 0, 14, 31, 30, 14, 0, 24, 16, 35, 14),
  (2058, 2, 0, 31, 33, 14, 2, 3, 40, 21, 13),
  (2059, 0, 31, 3, 33, 13, 1, 3, 32, 32, 14),
  (2060, 2, 2, 32, 32, 14, 2, 10, 4, 44, 14),
  (2061, 0, 10, 5, 44, 14, 2, 8, 33, 30, 14),
  (2062, 0, 6, 45, 1, 10, 0, 39, 21, 10, 11),
  (2063, 1, 16, 38, 19, 13, 1, 34, 11, 28, 13),
  (2064, 0, 4, 32, 32, 14, 0, 20, 8, 40, 14),
  (2065, 0, 18, 29, 30, 14, 0, 24, 20, 33, 14),
  (2066, 0, 5, 40, 21, 13, 0, 21, 40, 5, 11),
  (2067, 0, 19, 41, 5, 11, 1, 39, 12, 20, 12),
  (2068, 0, 12, 32, 30, 14, 0, 24, 14, 36, 14),
  (2069, 1, 41, 19, 5, 10, 2, 14, 4, 43, 14),
  (2070, 0, 14, 5, 43, 14, 0, 22, 25, 31, 14),
  (2071, 1, 39, 8, 22, 12, 1, 42, 7, 16, 11),
  (2072, 1, 3, 6, 45, 14, 1, 9, 33, 30, 14),
  (2073, 2, 2, 6, 45, 14, 2, 18, 30, 29, 14),
  (2074, 2, 4, 5, 45, 14, 2, 4, 33, 31, 14),
  (2075, 0, 23, 39, 5, 11, 1, 11, 4, 44, 14),
  (2076, 1, 9, 43, 12, 12, 1, 29, 33, 12, 12),
  (2077, 0, 4, 6, 45, 14, 1, 1, 7, 45, 14),
  (2078, 0, 2, 7, 45, 14, 0, 17, 42, 5, 11),
  (2079, 3, 10, 40, 19, 13, 3, 10, 44, 5, 11),
  (2080, 0, 12, 44, 0, 10, 0, 28, 36, 0, 10),
  (2081, 0, 9, 40, 20, 13, 0, 34, 27, 14, 12),
  (2082, 2, 0, 7, 45, 14, 2, 12, 33, 29, 14),
  (2083, 0, 3, 45, 7, 11, 1, 42, 11, 14, 11),
  (2084, 0, 20, 28, 30, 14, 0, 24, 22, 32, 14),
  (2085, 0, 1, 40, 22, 13, 1, 21, 39, 11, 12),
  (2086, 0, 6, 5, 45, 14, 0, 6, 33, 31, 14),
  (2087, 3, 17, 4, 42, 14, 3, 42, 4, 17, 11),
  (2088, 1, 39, 6, 23, 12, 3, 25, 22, 31, 14),
  (2089, 0, 0, 8, 45, 14, 0, 10, 33, 30, 14),
  (2090, 0, 27, 31, 20, 13, 0, 45, 4, 7, 9),
  (2091, 0, 19, 37, 19, 13, 1, 44, 12, 3, 9),
  (2092, 1, 7, 4, 45, 14, 1, 15, 4, 43, 14),
  (2093, 0, 10, 43, 12, 12, 0, 32, 30, 13, 12),
  (2094, 0, 17, 38, 19, 13, 0, 25, 38, 5, 11),
  (2095, 1, 24, 34, 19, 13, 1, 34, 19, 24, 13),
  (2096, 0, 12, 4, 44, 14, 0, 44, 4, 12, 10),
  (2097, 0, 36, 24, 15, 12, 0, 45, 6, 6, 9),
  (2098, 0, 21, 36, 19, 13, 2, 45, 1, 8, 9),
  (2099, 0, 15, 43, 5, 11, 1, 6, 45, 6, 11)
  ]

lemma witChunk_37_ok : witChunk_37.all checkWit = true := by
  decide +kernel

lemma witChunk_37_ns :
    witChunk_37.map (fun t => t.1) = (List.range 50).map (· + 2050) := by
  decide +kernel

def witChunk_38 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2100, 0, 40, 22, 4, 10, 0, 44, 8, 10, 10),
  (2101, 1, 13, 33, 29, 14, 1, 33, 29, 13, 12),
  (2102, 0, 33, 22, 23, 13, 1, 40, 20, 10, 11),
  (2103, 1, 39, 16, 18, 12, 3, 34, 20, 23, 13),
  (2104, 1, 19, 30, 29, 14, 1, 37, 27, 2, 10),
  (2105, 0, 8, 4, 45, 14, 2, 10, 34, 29, 14),
  (2106, 0, 45, 0, 9, 9, 2, 8, 3, 45, 14),
  (2107, 0, 15, 39, 19, 13, 1, 7, 34, 30, 14),
  (2108, 1, 9, 45, 0, 10, 1, 39, 24, 3, 10),
  (2109, 0, 37, 26, 8, 11, 0, 44, 2, 13, 10),
  (2110, 0, 7, 45, 6, 11, 2, 33, 23, 22, 13),
  (2111, 3, 20, 37, 18, 13, 5, 11, 2, 44, 14),
  (2112, 1, 15, 42, 11, 12, 2, 18, 4, 42, 14),
  (2113, 0, 0, 32, 33, 14, 0, 18, 5, 42, 14),
  (2114, 0, 45, 8, 5, 9, 2, 5, 41, 20, 13),
  (2115, 0, 23, 35, 19, 13, 0, 35, 29, 7, 11),
  (2116, 1, 1, 33, 32, 14, 1, 3, 44, 13, 12),
  (2117, 0, 2, 33, 32, 14, 0, 20, 6, 41, 14),
  (2118, 0, 31, 1, 34, 13, 0, 34, 31, 1, 10),
  (2119, 1, 6, 41, 20, 13, 1, 31, 34, 0, 10),
  (2120, 0, 0, 46, 2, 10, 0, 8, 34, 30, 14),
  (2121, 0, 4, 44, 13, 12, 0, 16, 4, 43, 14),
  (2122, 2, 12, 43, 11, 12, 2, 16, 3, 43, 14),
  (2123, 0, 27, 37, 5, 11, 0, 35, 13, 27, 13),
  (2124, 2, 6, 44, 12, 12, 2, 26, 12, 36, 14),
  (2125, 0, 10, 45, 0, 10, 0, 30, 35, 0, 10),
  (2126, 0, 14, 33, 29, 14, 0, 18, 31, 29, 14),
  (2127, 1, 42, 19, 0, 9, 3, 13, 2, 44, 14),
  (2128, 1, 2, 41, 21, 13, 1, 3, 34, 31, 14),
  (2129, 0, 33, 4, 32, 13, 2, 2, 34, 31, 14),
  (2130, 0, 7, 41, 20, 13, 0, 13, 40, 19, 13),
  (2131, 0, 3, 41, 21, 13, 0, 31, 27, 21, 13),
  (2132, 0, 0, 44, 14, 12, 0, 44, 0, 14, 10),
  (2133, 0, 4, 34, 31, 14, 0, 4, 46, 1, 10),
  (2134, 0, 10, 3, 45, 14, 0, 46, 3, 3, 8),
  (2135, 1, 38, 25, 8, 11, 1, 42, 15, 12, 11),
  (2136, 1, 39, 18, 17, 12, 3, 1, 34, 31, 14),
  (2137, 2, 10, 2, 45, 14, 2, 16, 33, 28, 14),
  (2138, 1, 44, 14, 2, 9, 2, 8, 35, 29, 14),
  (2139, 0, 35, 17, 25, 13, 0, 43, 17, 1, 9),
  (2140, 1, 41, 21, 4, 10, 2, 18, 32, 28, 14),
  (2141, 0, 12, 34, 29, 14, 0, 14, 3, 44, 14),
  (2142, 0, 25, 34, 19, 13, 2, 17, 39, 18, 13),
  (2143, 1, 3, 4, 46, 14, 1, 19, 4, 42, 14),
  (2144, 0, 8, 44, 12, 12, 0, 40, 12, 20, 12),
  (2145, 0, 2, 5, 46, 14, 0, 46, 5, 2, 8),
  (2146, 2, 21, 41, 4, 11, 2, 36, 29, 1, 10),
  (2147, 0, 35, 9, 29, 13, 4, 35, 7, 29, 13),
  (2148, 0, 4, 4, 46, 14, 0, 40, 8, 22, 12),
  (2149, 0, 33, 24, 22, 13, 0, 33, 32, 6, 11)
  ]

lemma witChunk_38_ok : witChunk_38.all checkWit = true := by
  decide +kernel

lemma witChunk_38_ns :
    witChunk_38.map (fun t => t.1) = (List.range 50).map (· + 2100) := by
  decide +kernel

def witChunk_39 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2150, 0, 42, 19, 5, 10, 2, 31, 34, 5, 11),
  (2151, 3, 1, 4, 46, 14, 3, 25, 8, 38, 14),
  (2152, 0, 0, 6, 46, 14, 0, 24, 26, 30, 14),
  (2153, 2, 20, 31, 28, 14, 2, 23, 40, 4, 11),
  (2154, 0, 43, 7, 16, 11, 2, 24, 7, 39, 14),
  (2155, 0, 43, 9, 15, 11, 1, 27, 20, 32, 14),
  (2156, 1, 23, 28, 29, 14, 3, 9, 44, 11, 12),
  (2157, 0, 40, 14, 19, 12, 2, 15, 40, 18, 13),
  (2158, 4, 10, 1, 45, 14, 4, 11, 41, 18, 13),
  (2159, 3, 5, 46, 0, 10, 3, 21, 40, 10, 12),
  (2160, 2, 6, 46, 0, 10, 2, 26, 24, 30, 14),
  (2161, 0, 6, 3, 46, 14, 0, 6, 35, 30, 14),
  (2162, 0, 29, 36, 5, 11, 0, 35, 19, 24, 13),
  (2163, 0, 11, 41, 19, 13, 0, 43, 5, 17, 11),
  (2164, 1, 17, 33, 28, 14, 2, 6, 2, 46, 14),
  (2165, 0, 40, 6, 23, 12, 2, 10, 44, 11, 12),
  (2166, 0, 1, 46, 7, 11, 0, 10, 35, 29, 14),
  (2167, 1, 0, 46, 7, 11, 1, 7, 46, 0, 10),
  (2168, 0, 36, 26, 14, 12, 3, 23, 39, 10, 12),
  (2169, 2, 3, 46, 6, 11, 2, 35, 6, 30, 13),
  (2170, 1, 4, 46, 6, 11, 1, 20, 38, 18, 13),
  (2171, 0, 11, 45, 5, 11, 1, 7, 2, 46, 14),
  (2172, 3, 23, 5, 40, 14, 3, 23, 29, 28, 14),
  (2173, 0, 12, 2, 45, 14, 1, 45, 5, 11, 10),
  (2174, 0, 35, 7, 30, 13, 3, 2, 46, 6, 11),
  (2175, 5, 3, 46, 0, 10, 5, 27, 10, 36, 14),
  (2176, 1, 27, 22, 31, 14, 1, 42, 17, 11, 11),
  (2177, 0, 5, 46, 6, 11, 0, 38, 27, 2, 10),
  (2178, 0, 45, 12, 3, 9, 2, 12, 1, 45, 14),
  (2179, 0, 27, 33, 19, 13, 1, 22, 37, 18, 13),
  (2180, 0, 0, 34, 32, 14, 0, 8, 46, 0, 10),
  (2181, 0, 41, 20, 10, 11, 0, 44, 14, 7, 10),
  (2182, 0, 18, 3, 43, 14, 0, 33, 2, 33, 13),
  (2183, 1, 22, 41, 4, 11, 1, 46, 1, 8, 9),
  (2184, 0, 8, 2, 46, 14, 3, 7, 1, 46, 14),
  (2185, 0, 40, 24, 3, 10, 2, 15, 44, 4, 11),
  (2186, 2, 28, 13, 35, 14, 2, 40, 17, 17, 12),
  (2187, 0, 43, 13, 13, 11, 2, 33, 1, 33, 13),
  (2188, 1, 7, 36, 29, 14, 1, 21, 31, 28, 14),
  (2189, 0, 5, 42, 20, 13, 1, 1, 35, 31, 14),
  (2190, 0, 2, 35, 31, 14, 0, 22, 5, 41, 14),
  (2191, 1, 8, 42, 19, 13, 1, 18, 43, 4, 11),
  (2192, 0, 32, 32, 12, 12, 0, 40, 4, 24, 12),
  (2193, 2, 4, 45, 12, 12, 2, 40, 3, 24, 12),
  (2194, 1, 24, 40, 4, 11, 2, 0, 35, 31, 14),
  (2195, 0, 35, 21, 23, 13, 1, 44, 16, 1, 9),
  (2196, 0, 16, 2, 44, 14, 0, 16, 34, 28, 14),
  (2197, 0, 18, 33, 28, 14, 0, 28, 18, 33, 14),
  (2198, 0, 2, 45, 13, 12, 0, 38, 23, 15, 12),
  (2199, 1, 39, 0, 26, 12, 3, 41, 10, 20, 12)
  ]

lemma witChunk_39_ok : witChunk_39.all checkWit = true := by
  decide +kernel

lemma witChunk_39_ns :
    witChunk_39.map (fun t => t.1) = (List.range 50).map (· + 2150) := by
  decide +kernel

def witChunk_40 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2200, 1, 9, 1, 46, 14, 1, 27, 10, 37, 14),
  (2201, 0, 8, 36, 29, 14, 0, 12, 44, 11, 12),
  (2202, 0, 31, 29, 20, 13, 0, 37, 28, 7, 11),
  (2203, 1, 11, 36, 28, 14, 1, 14, 41, 18, 13),
  (2204, 1, 41, 11, 20, 12, 3, 29, 16, 33, 14),
  (2205, 0, 6, 45, 12, 12, 0, 14, 35, 28, 14),
  (2206, 0, 1, 42, 21, 13, 0, 9, 42, 19, 13),
  (2207, 1, 0, 42, 21, 13, 1, 3, 36, 30, 14),
  (2208, 0, 20, 32, 28, 14, 0, 28, 20, 32, 14),
  (2209, 0, 21, 38, 18, 13, 2, 24, 5, 40, 14),
  (2210, 0, 39, 25, 8, 11, 0, 43, 19, 0, 9),
  (2211, 0, 31, 35, 5, 11, 0, 35, 5, 31, 13),
  (2212, 0, 4, 36, 30, 14, 0, 24, 6, 40, 14),
  (2213, 0, 17, 40, 18, 13, 0, 40, 18, 17, 12),
  (2214, 0, 2, 47, 1, 10, 3, 46, 8, 4, 9),
  (2215, 1, 23, 30, 28, 14, 1, 26, 39, 4, 11),
  (2216, 1, 19, 2, 43, 14, 1, 21, 3, 42, 14),
  (2217, 0, 10, 1, 46, 14, 2, 11, 42, 18, 13),
  (2218, 0, 43, 15, 12, 11, 2, 0, 47, 1, 10),
  (2219, 3, 41, 6, 22, 12, 3, 41, 14, 18, 12),
  (2220, 3, 7, 37, 28, 14, 3, 29, 20, 31, 14),
  (2221, 0, 21, 42, 4, 11, 0, 42, 21, 4, 10),
  (2222, 0, 2, 3, 47, 14, 0, 9, 46, 5, 11),
  (2223, 3, 13, 44, 10, 12, 3, 34, 32, 5, 11),
  (2224, 0, 12, 36, 28, 14, 0, 28, 12, 36, 14),
  (2225, 0, 0, 4, 47, 14, 0, 45, 14, 2, 9),
  (2226, 0, 19, 43, 4, 11, 0, 23, 41, 4, 11),
  (2227, 1, 19, 42, 10, 12, 1, 26, 35, 18, 13),
  (2228, 0, 44, 16, 6, 10, 1, 17, 1, 44, 14),
  (2229, 0, 4, 2, 47, 14, 0, 22, 31, 28, 14),
  (2230, 0, 15, 41, 18, 13, 1, 44, 6, 16, 11),
  (2231, 1, 23, 40, 10, 12, 1, 47, 4, 2, 8),
  (2232, 1, 39, 22, 15, 12, 1, 41, 15, 18, 12),
  (2233, 2, 4, 47, 0, 10, 4, 28, 24, 29, 14),
  (2234, 1, 12, 42, 18, 13, 1, 36, 6, 30, 13),
  (2235, 3, 22, 38, 17, 13, 3, 44, 5, 16, 11),
  (2236, 1, 5, 47, 0, 10, 1, 9, 37, 28, 14),
  (2237, 1, 5, 1, 47, 14, 1, 5, 37, 29, 14),
  (2238, 0, 35, 23, 22, 13, 6, 37, 11, 26, 13),
  (2239, 1, 11, 0, 46, 14, 1, 14, 45, 4, 11),
  (2240, 1, 17, 43, 10, 12, 1, 31, 34, 11, 12),
  (2241, 0, 17, 44, 4, 11, 0, 25, 40, 4, 11),
  (2242, 0, 37, 12, 27, 13, 1, 40, 24, 8, 11),
  (2243, 1, 44, 4, 17, 11, 2, 5, 43, 19, 13),
  (2244, 3, 4, 43, 19, 13, 3, 16, 41, 17, 13),
  (2245, 0, 6, 47, 0, 10, 0, 25, 36, 18, 13),
  (2246, 0, 6, 1, 47, 14, 0, 6, 37, 29, 14),
  (2247, 5, 12, 42, 17, 13, 5, 15, 36, 26, 14),
  (2248, 1, 6, 43, 19, 13, 1, 19, 34, 27, 14),
  (2249, 0, 36, 28, 13, 12, 4, 28, 8, 37, 14)
  ]

lemma witChunk_40_ok : witChunk_40.all checkWit = true := by
  decide +kernel

lemma witChunk_40_ns :
    witChunk_40.map (fun t => t.1) = (List.range 50).map (· + 2200) := by
  decide +kernel

def witChunk_41 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2250, 0, 37, 16, 25, 13, 2, 12, 37, 27, 14),
  (2251, 1, 2, 47, 6, 11, 1, 35, 32, 0, 10),
  (2252, 1, 15, 0, 45, 14, 1, 15, 36, 27, 14),
  (2253, 0, 10, 37, 28, 14, 0, 20, 2, 43, 14),
  (2254, 0, 3, 47, 6, 11, 2, 1, 47, 6, 11),
  (2255, 1, 2, 43, 20, 13, 3, 8, 43, 18, 13),
  (2256, 0, 40, 20, 16, 12, 2, 30, 18, 32, 14),
  (2257, 0, 0, 36, 31, 14, 0, 13, 42, 18, 13),
  (2258, 0, 3, 43, 20, 13, 0, 35, 3, 32, 13),
  (2259, 0, 7, 43, 19, 13, 0, 43, 17, 11, 11),
  (2260, 0, 12, 0, 46, 14, 0, 24, 30, 28, 14),
  (2261, 0, 18, 1, 44, 14, 0, 34, 31, 12, 12),
  (2262, 0, 46, 5, 11, 10, 1, 44, 18, 0, 9),
  (2263, 1, 15, 44, 10, 12, 3, 0, 47, 6, 11),
  (2264, 0, 20, 42, 10, 12, 3, 11, 45, 10, 12),
  (2265, 0, 22, 41, 10, 12, 0, 38, 25, 14, 12),
  (2266, 0, 15, 45, 4, 11, 0, 27, 39, 4, 11),
  (2267, 0, 47, 3, 7, 9, 1, 43, 20, 4, 10),
  (2268, 1, 41, 3, 24, 12, 2, 18, 0, 44, 14),
  (2269, 0, 37, 18, 24, 13, 0, 46, 3, 12, 10),
  (2270, 0, 33, 34, 5, 11, 0, 47, 5, 6, 9),
  (2271, 1, 3, 46, 12, 12, 1, 35, 30, 12, 12),
  (2272, 1, 1, 37, 30, 14, 1, 6, 47, 5, 11),
  (2273, 0, 2, 37, 30, 14, 0, 8, 0, 47, 14),
  (2274, 0, 37, 8, 29, 13, 0, 47, 1, 8, 9),
  (2275, 1, 10, 43, 18, 13, 1, 27, 38, 10, 12),
  (2276, 0, 4, 46, 12, 12, 0, 24, 40, 10, 12),
  (2277, 2, 0, 37, 30, 14, 2, 12, 45, 10, 12),
  (2278, 0, 18, 35, 27, 14, 0, 27, 35, 18, 13),
  (2279, 1, 7, 38, 28, 14, 3, 1, 46, 12, 12),
  (2280, 0, 40, 26, 2, 10, 3, 5, 46, 11, 12),
  (2281, 0, 16, 0, 45, 14, 0, 16, 36, 27, 14),
  (2282, 0, 45, 16, 1, 9, 2, 35, 32, 5, 11),
  (2283, 0, 7, 47, 5, 11, 0, 31, 31, 19, 13),
  (2284, 1, 23, 32, 27, 14, 3, 24, 41, 3, 11),
  (2285, 0, 0, 46, 13, 12, 0, 20, 34, 27, 14),
  (2286, 0, 38, 29, 1, 10, 0, 42, 9, 21, 12),
  (2287, 1, 30, 37, 4, 11, 1, 32, 30, 19, 13),
  (2288, 1, 7, 46, 11, 12, 1, 27, 6, 39, 14),
  (2289, 2, 36, 29, 12, 12, 4, 24, 40, 9, 12),
  (2290, 6, 21, 39, 16, 13, 8, 15, 41, 16, 13),
  (2291, 0, 35, 25, 21, 13, 1, 20, 40, 17, 13),
  (2292, 0, 8, 38, 28, 14, 0, 16, 44, 10, 12),
  (2293, 1, 21, 1, 43, 14, 1, 29, 9, 37, 14),
  (2294, 0, 11, 43, 18, 13, 0, 14, 37, 27, 14),
  (2295, 1, 39, 24, 14, 12, 5, 38, 15, 24, 13),
  (2296, 1, 3, 38, 29, 14, 1, 11, 38, 27, 14),
  (2297, 0, 26, 39, 10, 12, 0, 42, 7, 22, 12),
  (2298, 0, 37, 20, 23, 13, 5, 32, 30, 18, 13),
  (2299, 0, 39, 27, 7, 11, 1, 19, 0, 44, 14)
  ]

lemma witChunk_41_ok : witChunk_41.all checkWit = true := by
  decide +kernel

lemma witChunk_41_ns :
    witChunk_41.map (fun t => t.1) = (List.range 50).map (· + 2250) := by
  decide +kernel

def witChunk_42 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2300, 1, 41, 19, 16, 12, 2, 26, 4, 40, 14),
  (2301, 0, 4, 38, 29, 14, 0, 8, 46, 11, 12),
  (2302, 0, 22, 33, 27, 14, 0, 30, 21, 31, 14),
  (2303, 3, 26, 40, 3, 11, 5, 44, 14, 11, 11),
  (2304, 2, 18, 36, 26, 14, 2, 30, 10, 36, 14),
  (2305, 0, 0, 48, 1, 10, 0, 37, 6, 30, 13),
  (2306, 0, 47, 9, 4, 9, 1, 48, 0, 0, 7),
  (2307, 2, 21, 43, 3, 11, 2, 45, 7, 15, 11),
  (2308, 0, 0, 2, 48, 14, 1, 1, 1, 48, 14),
  (2309, 0, 2, 1, 48, 14, 0, 40, 22, 15, 12),
  (2310, 0, 43, 19, 10, 11, 2, 23, 42, 3, 11),
  (2311, 1, 16, 42, 17, 13, 1, 24, 38, 17, 13),
  (2312, 1, 29, 37, 10, 12, 1, 41, 25, 2, 10),
  (2313, 0, 42, 15, 18, 12, 2, 0, 1, 48, 14),
  (2314, 0, 45, 8, 15, 11, 2, 3, 44, 19, 13),
  (2315, 0, 35, 1, 33, 13, 1, 3, 0, 48, 14),
  (2316, 2, 2, 0, 48, 14, 2, 2, 48, 0, 10),
  (2317, 0, 12, 38, 27, 14, 0, 30, 11, 36, 14),
  (2318, 0, 42, 5, 23, 12, 4, 6, 39, 27, 14),
  (2319, 3, 2, 44, 19, 13, 3, 29, 26, 28, 14),
  (2320, 0, 4, 0, 48, 14, 0, 4, 48, 0, 10),
  (2321, 0, 14, 45, 10, 12, 0, 29, 34, 18, 13),
  (2322, 0, 5, 44, 19, 13, 2, 8, 39, 27, 14),
  (2323, 1, 38, 29, 6, 11, 2, 25, 41, 3, 11),
  (2324, 0, 48, 4, 2, 8, 1, 31, 20, 31, 14),
  (2325, 2, 30, 24, 29, 14, 2, 48, 3, 2, 8),
  (2326, 1, 8, 44, 18, 13, 1, 36, 2, 32, 13),
  (2327, 1, 10, 47, 4, 11, 1, 40, 26, 7, 11),
  (2328, 0, 28, 38, 10, 12, 3, 25, 2, 41, 14),
  (2329, 0, 24, 32, 27, 14, 0, 30, 23, 30, 14),
  (2330, 0, 21, 40, 17, 13, 0, 45, 4, 17, 11),
  (2331, 0, 19, 41, 17, 13, 2, 17, 45, 3, 11),
  (2332, 1, 5, 39, 28, 14, 1, 31, 12, 35, 14),
  (2333, 1, 9, 39, 27, 14, 2, 40, 23, 14, 12),
  (2334, 0, 22, 1, 43, 14, 0, 46, 13, 7, 10),
  (2335, 1, 19, 36, 26, 14, 7, 38, 8, 27, 13),
  (2336, 0, 20, 0, 44, 14, 1, 14, 43, 17, 13),
  (2337, 0, 1, 44, 20, 13, 0, 37, 22, 22, 13),
  (2338, 0, 45, 12, 13, 11, 1, 0, 44, 20, 13),
  (2339, 0, 23, 39, 17, 13, 0, 35, 33, 5, 11),
  (2340, 0, 36, 30, 12, 12, 9, 23, 32, 25, 14),
  (2341, 0, 1, 48, 6, 11, 0, 6, 39, 28, 14),
  (2342, 0, 17, 42, 17, 13, 0, 38, 27, 13, 12),
  (2343, 3, 10, 44, 17, 13, 3, 25, 32, 26, 14),
  (2344, 0, 0, 38, 30, 14, 0, 24, 2, 42, 14),
  (2345, 2, 32, 17, 32, 14, 4, 26, 31, 26, 14),
  (2346, 0, 11, 47, 4, 11, 0, 31, 37, 4, 11),
  (2347, 1, 4, 48, 5, 11, 1, 15, 38, 26, 14),
  (2348, 1, 47, 4, 11, 10, 3, 43, 9, 20, 12),
  (2349, 0, 42, 3, 24, 12, 0, 45, 18, 0, 9)
  ]

lemma witChunk_42_ok : witChunk_42.all checkWit = true := by
  decide +kernel

lemma witChunk_42_ns :
    witChunk_42.map (fun t => t.1) = (List.range 50).map (· + 2300) := by
  decide +kernel

def witChunk_43 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2350, 0, 10, 39, 27, 14, 0, 30, 9, 37, 14),
  (2351, 1, 24, 42, 3, 11, 1, 43, 10, 20, 12),
  (2352, 0, 28, 28, 28, 14, 0, 44, 20, 4, 10),
  (2353, 0, 45, 2, 18, 11, 4, 20, 36, 25, 14),
  (2354, 0, 5, 48, 5, 11, 0, 35, 27, 20, 13),
  (2355, 3, 20, 41, 16, 13, 5, 10, 21, 42, 15),
  (2356, 1, 1, 47, 12, 12, 1, 29, 27, 28, 14),
  (2357, 0, 2, 47, 12, 12, 1, 5, 47, 11, 12),
  (2358, 0, 25, 38, 17, 13, 1, 48, 4, 6, 9),
  (2359, 1, 31, 10, 36, 14, 1, 31, 36, 10, 12),
  (2360, 0, 12, 46, 10, 12, 1, 18, 45, 3, 11),
  (2361, 2, 0, 47, 12, 12, 2, 39, 16, 24, 13),
  (2362, 1, 44, 18, 10, 11, 2, 28, 29, 27, 14),
  (2363, 0, 15, 43, 17, 13, 1, 23, 34, 26, 14),
  (2364, 7, 12, 21, 41, 15, 9, 17, 43, 8, 12),
  (2365, 0, 45, 14, 12, 11, 1, 1, 39, 29, 14),
  (2366, 0, 2, 39, 29, 14, 0, 6, 47, 11, 12),
  (2367, 1, 48, 6, 5, 9, 3, 10, 20, 43, 15),
  (2368, 0, 48, 8, 0, 8, 1, 13, 39, 26, 14),
  (2369, 0, 18, 37, 26, 14, 0, 30, 37, 10, 12),
  (2370, 1, 48, 0, 8, 9, 2, 0, 39, 29, 14),
  (2371, 0, 39, 11, 27, 13, 0, 39, 15, 25, 13),
  (2372, 0, 20, 36, 26, 14, 0, 32, 18, 32, 14),
  (2373, 1, 21, 43, 9, 12, 2, 6, 40, 27, 14),
  (2374, 0, 31, 33, 18, 13, 1, 32, 32, 18, 13),
  (2375, 1, 47, 10, 8, 10, 3, 8, 23, 42, 15),
  (2376, 0, 16, 38, 26, 14, 0, 32, 14, 34, 14),
  (2377, 0, 46, 15, 6, 10, 2, 7, 48, 4, 11),
  (2378, 2, 11, 20, 43, 15, 2, 32, 11, 35, 14),
  (2379, 2, 9, 21, 43, 15, 2, 29, 39, 3, 11),
  (2380, 1, 7, 40, 27, 14, 1, 19, 44, 9, 12),
  (2381, 0, 42, 19, 16, 12, 2, 8, 47, 10, 12),
  (2382, 0, 47, 13, 2, 9, 2, 5, 45, 18, 13),
  (2383, 1, 16, 46, 3, 11, 3, 4, 45, 18, 13),
  (2384, 2, 10, 40, 26, 14, 2, 26, 32, 26, 14),
  (2385, 0, 22, 35, 26, 14, 0, 32, 20, 31, 14),
  (2386, 0, 21, 44, 3, 11, 0, 37, 24, 21, 13),
  (2387, 0, 23, 43, 3, 11, 0, 27, 37, 17, 13),
  (2388, 2, 30, 6, 38, 14, 3, 8, 25, 41, 15),
  (2389, 1, 25, 41, 9, 12, 1, 29, 5, 39, 14),
  (2390, 0, 42, 1, 25, 12, 2, 7, 22, 43, 15),
  (2391, 5, 12, 26, 39, 15, 5, 39, 26, 12, 12),
  (2392, 1, 2, 45, 19, 13, 1, 9, 47, 10, 12),
  (2393, 0, 8, 40, 27, 14, 0, 14, 39, 26, 14),
  (2394, 0, 13, 44, 17, 13, 1, 12, 22, 42, 15),
  (2395, 0, 3, 45, 19, 13, 0, 19, 45, 3, 11),
  (2396, 1, 31, 8, 37, 14, 1, 43, 4, 23, 12),
  (2397, 0, 37, 2, 32, 13, 1, 17, 45, 9, 12),
  (2398, 0, 7, 45, 18, 13, 0, 25, 42, 3, 11),
  (2399, 1, 8, 22, 43, 15, 1, 10, 19, 44, 15)
  ]

lemma witChunk_43_ok : witChunk_43.all checkWit = true := by
  decide +kernel

lemma witChunk_43_ns :
    witChunk_43.map (fun t => t.1) = (List.range 50).map (· + 2350) := by
  decide +kernel

def witChunk_44 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2400, 0, 4, 40, 28, 14, 0, 28, 4, 40, 14),
  (2401, 0, 0, 0, 49, 14, 0, 9, 48, 4, 11),
  (2402, 0, 45, 16, 11, 11, 1, 8, 20, 44, 15),
  (2403, 1, 12, 24, 41, 15, 1, 14, 21, 42, 15),
  (2404, 1, 1, 49, 0, 10, 1, 33, 17, 32, 14),
  (2405, 0, 2, 49, 0, 10, 0, 38, 31, 0, 10),
  (2406, 0, 41, 26, 7, 11, 1, 8, 24, 42, 15),
  (2407, 1, 46, 17, 0, 9, 3, 25, 0, 42, 14),
  (2408, 0, 24, 34, 26, 14, 0, 32, 22, 30, 14),
  (2409, 0, 10, 47, 10, 12, 2, 0, 49, 0, 10),
  (2410, 2, 5, 21, 44, 15, 2, 11, 16, 45, 15),
  (2411, 0, 11, 21, 43, 15, 0, 39, 7, 29, 13),
  (2412, 1, 27, 40, 9, 12, 3, 4, 23, 43, 15),
  (2413, 0, 28, 30, 27, 14, 0, 30, 27, 28, 14),
  (2414, 0, 9, 22, 43, 15, 0, 11, 23, 42, 15),
  (2415, 1, 6, 21, 44, 15, 1, 8, 18, 45, 15),
  (2416, 1, 6, 23, 43, 15, 1, 10, 17, 45, 15),
  (2417, 0, 9, 20, 44, 15, 0, 13, 22, 42, 15),
  (2418, 0, 11, 19, 44, 15, 0, 13, 20, 43, 15),
  (2419, 0, 27, 41, 3, 11, 1, 44, 20, 9, 11),
  (2420, 0, 12, 40, 26, 14, 0, 32, 10, 36, 14),
  (2421, 0, 9, 24, 42, 15, 0, 24, 42, 9, 12),
  (2422, 1, 12, 26, 40, 15, 1, 16, 20, 42, 15),
  (2423, 1, 8, 26, 41, 15, 1, 14, 17, 44, 15),
  (2424, 1, 6, 19, 45, 15, 1, 15, 46, 9, 12),
  (2425, 0, 24, 0, 43, 14, 2, 15, 16, 44, 15),
  (2426, 0, 7, 21, 44, 15, 0, 13, 24, 41, 15),
  (2427, 0, 7, 23, 43, 15, 0, 11, 25, 41, 15),
  (2428, 3, 40, 9, 27, 13, 3, 49, 0, 3, 8),
  (2429, 0, 13, 18, 44, 15, 0, 38, 29, 12, 12),
  (2430, 0, 9, 18, 45, 15, 0, 15, 21, 42, 15),
  (2431, 1, 10, 27, 40, 15, 1, 16, 18, 43, 15),
  (2432, 1, 2, 49, 5, 11, 1, 19, 38, 25, 14),
  (2433, 2, 30, 38, 9, 12, 4, 32, 36, 9, 12),
  (2434, 1, 16, 24, 40, 15, 1, 24, 40, 16, 13),
  (2435, 0, 3, 49, 5, 11, 0, 7, 19, 45, 15),
  (2436, 0, 44, 10, 20, 12, 1, 3, 48, 11, 12),
  (2437, 0, 33, 32, 18, 13, 1, 5, 41, 27, 14),
  (2438, 0, 7, 25, 42, 15, 0, 9, 26, 41, 15),
  (2439, 3, 4, 17, 46, 15, 3, 18, 24, 39, 15),
  (2440, 0, 48, 6, 10, 10, 1, 9, 41, 26, 14),
  (2441, 0, 0, 40, 29, 14, 0, 4, 48, 11, 12),
  (2442, 0, 43, 23, 8, 11, 2, 3, 20, 45, 15),
  (2443, 0, 15, 47, 3, 11, 1, 4, 20, 45, 15),
  (2444, 2, 34, 16, 32, 14, 3, 0, 49, 5, 11),
  (2445, 0, 5, 22, 44, 15, 0, 13, 26, 40, 15),
  (2446, 0, 6, 41, 27, 14, 0, 30, 5, 39, 14),
  (2447, 3, 2, 20, 45, 15, 3, 2, 24, 43, 15),
  (2448, 0, 0, 48, 12, 12, 1, 6, 27, 41, 15),
  (2449, 0, 45, 18, 10, 11, 0, 48, 8, 9, 10)
  ]

lemma witChunk_44_ok : witChunk_44.all checkWit = true := by
  decide +kernel

lemma witChunk_44_ns :
    witChunk_44.map (fun t => t.1) = (List.range 50).map (· + 2400) := by
  decide +kernel

def witChunk_45 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2450, 0, 5, 20, 45, 15, 0, 5, 24, 43, 15),
  (2451, 1, 12, 28, 39, 15, 1, 18, 19, 42, 15),
  (2452, 0, 48, 2, 12, 10, 1, 15, 40, 25, 14),
  (2453, 0, 9, 16, 46, 15, 0, 16, 46, 9, 12),
  (2454, 0, 7, 17, 46, 15, 0, 17, 22, 41, 15),
  (2455, 1, 6, 49, 4, 11, 1, 7, 48, 10, 12),
  (2456, 0, 44, 6, 22, 12, 0, 44, 14, 18, 12),
  (2457, 0, 10, 41, 26, 14, 0, 32, 8, 37, 14),
  (2458, 0, 37, 0, 33, 13, 1, 4, 18, 46, 15),
  (2459, 0, 7, 27, 41, 15, 1, 12, 48, 3, 11),
  (2460, 3, 8, 13, 47, 15, 3, 20, 19, 41, 15),
  (2461, 0, 21, 42, 16, 13, 1, 13, 47, 9, 12),
  (2462, 0, 11, 15, 46, 15, 0, 17, 18, 43, 15),
  (2463, 3, 29, 2, 40, 14, 3, 40, 19, 22, 13),
  (2464, 1, 10, 29, 39, 15, 1, 18, 17, 43, 15),
  (2465, 0, 5, 18, 46, 15, 0, 5, 26, 42, 15),
  (2466, 0, 7, 49, 4, 11, 0, 19, 43, 16, 13),
  (2467, 2, 5, 15, 47, 15, 2, 9, 13, 47, 15),
  (2468, 0, 8, 48, 10, 12, 0, 48, 10, 8, 10),
  (2469, 0, 2, 41, 28, 14, 0, 20, 38, 25, 14),
  (2470, 0, 18, 39, 25, 14, 0, 30, 29, 27, 14),
  (2471, 1, 2, 23, 44, 15, 1, 8, 14, 47, 15),
  (2472, 1, 2, 21, 45, 15, 1, 6, 15, 47, 15),
  (2473, 0, 48, 0, 13, 10, 2, 0, 41, 28, 14),
  (2474, 0, 3, 23, 44, 15, 0, 13, 28, 39, 15),
  (2475, 0, 3, 21, 45, 15, 0, 15, 15, 45, 15),
  (2476, 1, 31, 28, 27, 14, 1, 43, 0, 25, 12),
  (2477, 1, 13, 41, 25, 14, 1, 25, 35, 25, 14),
  (2478, 0, 1, 46, 19, 13, 0, 22, 37, 25, 14),
  (2479, 1, 0, 46, 19, 13, 1, 6, 29, 40, 15),
  (2480, 1, 2, 25, 43, 15, 1, 10, 13, 47, 15),
  (2481, 0, 13, 14, 46, 15, 0, 16, 40, 25, 14),
  (2482, 0, 13, 48, 3, 11, 2, 3, 16, 47, 15),
  (2483, 0, 3, 25, 43, 15, 0, 7, 15, 47, 15),
  (2484, 0, 28, 32, 26, 14, 0, 32, 26, 28, 14),
  (2485, 4, 8, 42, 25, 14, 4, 9, 46, 16, 13),
  (2486, 0, 3, 19, 46, 15, 0, 9, 14, 47, 15),
  (2487, 1, 8, 30, 39, 15, 1, 18, 15, 44, 15),
  (2488, 1, 31, 38, 9, 12, 3, 9, 42, 25, 14),
  (2489, 0, 42, 23, 14, 12, 2, 19, 26, 38, 15),
  (2490, 0, 5, 16, 47, 15, 0, 5, 28, 41, 15),
  (2491, 0, 31, 39, 3, 11, 0, 39, 3, 31, 13),
  (2492, 1, 47, 16, 5, 10, 2, 22, 44, 8, 12),
  (2493, 0, 46, 19, 4, 10, 2, 10, 48, 9, 12),
  (2494, 0, 42, 27, 1, 10, 2, 9, 31, 38, 15),
  (2495, 1, 27, 0, 42, 14, 3, 0, 19, 46, 15),
  (2496, 3, 31, 29, 26, 14, 5, 6, 49, 3, 11),
  (2497, 0, 24, 36, 25, 14, 0, 34, 21, 30, 14),
  (2498, 0, 47, 17, 0, 9, 4, 1, 16, 47, 15),
  (2499, 0, 11, 13, 47, 15, 0, 19, 17, 43, 15)
  ]

lemma witChunk_45_ok : witChunk_45.all checkWit = true := by
  decide +kernel

lemma witChunk_45_ns :
    witChunk_45.map (fun t => t.1) = (List.range 50).map (· + 2450) := by
  decide +kernel

def witChunk_46 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2500, 0, 0, 50, 0, 10, 0, 40, 30, 0, 10),
  (2501, 0, 41, 12, 26, 13, 0, 41, 28, 6, 11),
  (2502, 0, 3, 27, 42, 15, 0, 9, 30, 39, 15),
  (2503, 1, 48, 14, 1, 9, 3, 18, 44, 15, 13),
  (2504, 0, 8, 42, 26, 14, 0, 32, 6, 38, 14),
  (2505, 2, 2, 42, 27, 14, 2, 7, 12, 48, 15),
  (2506, 0, 15, 45, 16, 13, 0, 27, 39, 16, 13),
  (2507, 0, 3, 17, 47, 15, 0, 19, 25, 39, 15),
  (2508, 1, 11, 48, 9, 12, 1, 45, 9, 20, 12),
  (2509, 0, 4, 42, 27, 14, 0, 30, 3, 40, 14),
  (2510, 0, 1, 22, 45, 15, 0, 15, 13, 46, 15),
  (2511, 1, 0, 22, 45, 15, 1, 6, 13, 48, 15),
  (2512, 1, 10, 49, 3, 11, 1, 11, 42, 25, 14),
  (2513, 0, 1, 24, 44, 15, 0, 13, 30, 38, 15),
  (2514, 0, 37, 28, 19, 13, 1, 0, 24, 44, 15),
  (2515, 1, 22, 45, 2, 11, 2, 5, 31, 39, 15),
  (2516, 0, 44, 2, 24, 12, 0, 44, 18, 16, 12),
  (2517, 0, 1, 20, 46, 15, 0, 17, 28, 38, 15),
  (2518, 1, 0, 20, 46, 15, 1, 4, 14, 48, 15),
  (2519, 3, 26, 40, 15, 13, 3, 41, 26, 12, 12),
  (2520, 1, 6, 31, 39, 15, 1, 18, 13, 45, 15),
  (2521, 2, 16, 41, 24, 14, 2, 31, 36, 16, 13),
  (2522, 0, 7, 13, 48, 15, 0, 13, 12, 47, 15),
  (2523, 0, 43, 25, 7, 11, 2, 21, 15, 43, 15),
  (2524, 1, 41, 29, 0, 10, 2, 34, 8, 36, 14),
  (2525, 0, 5, 14, 48, 15, 0, 5, 30, 40, 15),
  (2526, 0, 1, 26, 43, 15, 0, 1, 50, 5, 11),
  (2527, 1, 0, 26, 43, 15, 1, 0, 50, 5, 11),
  (2528, 0, 40, 28, 12, 12, 1, 2, 29, 41, 15),
  (2529, 0, 9, 12, 48, 15, 0, 12, 48, 9, 12),
  (2530, 2, 0, 49, 11, 12, 2, 19, 44, 15, 13),
  (2531, 0, 3, 29, 41, 15, 0, 7, 31, 39, 15),
  (2532, 1, 21, 45, 8, 12, 3, 4, 47, 17, 13),
  (2533, 0, 12, 42, 25, 14, 0, 34, 9, 36, 14),
  (2534, 0, 1, 18, 47, 15, 0, 19, 27, 38, 15),
  (2535, 1, 0, 18, 47, 15, 1, 2, 15, 48, 15),
  (2536, 0, 48, 14, 6, 10, 1, 6, 47, 17, 13),
  (2537, 0, 6, 49, 10, 12, 0, 30, 31, 26, 14),
  (2538, 0, 3, 15, 48, 15, 0, 21, 24, 39, 15),
  (2539, 1, 2, 47, 18, 13, 1, 12, 32, 37, 15),
  (2540, 1, 21, 39, 24, 14, 1, 25, 43, 8, 12),
  (2541, 0, 5, 50, 4, 11, 0, 13, 46, 16, 13),
  (2542, 0, 3, 47, 18, 13, 0, 33, 38, 3, 11),
  (2543, 1, 19, 46, 8, 12, 3, 45, 4, 22, 12),
  (2544, 1, 39, 30, 11, 12, 2, 14, 42, 24, 14),
  (2545, 4, 36, 16, 31, 14, 4, 44, 24, 1, 10),
  (2546, 0, 11, 11, 48, 15, 0, 21, 16, 43, 15),
  (2547, 0, 7, 47, 17, 13, 1, 50, 3, 6, 9),
  (2548, 0, 0, 42, 28, 14, 0, 28, 0, 42, 14),
  (2549, 0, 1, 28, 42, 15, 0, 9, 32, 38, 15)
  ]

lemma witChunk_46_ok : witChunk_46.all checkWit = true := by
  decide +kernel

lemma witChunk_46_ns :
    witChunk_46.map (fun t => t.1) = (List.range 50).map (· + 2500) := by
  decide +kernel

def witChunk_47 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2550, 1, 0, 28, 42, 15, 1, 12, 10, 48, 15),
  (2551, 1, 23, 38, 24, 14, 1, 38, 33, 4, 11),
  (2552, 0, 36, 34, 10, 12, 1, 5, 43, 26, 14),
  (2553, 2, 15, 32, 36, 15, 2, 36, 15, 32, 14),
  (2554, 1, 28, 42, 2, 11, 2, 8, 49, 9, 12),
  (2555, 0, 15, 11, 47, 15, 0, 15, 31, 37, 15),
  (2556, 1, 41, 27, 12, 12, 2, 26, 36, 24, 14),
  (2557, 1, 9, 43, 25, 14, 1, 29, 33, 25, 14),
  (2558, 0, 17, 30, 37, 15, 0, 23, 45, 2, 11),
  (2559, 1, 27, 42, 8, 12, 3, 50, 4, 5, 9),
  (2560, 1, 6, 11, 49, 15, 1, 10, 33, 37, 15),
  (2561, 0, 1, 16, 48, 15, 0, 6, 43, 26, 14),
  (2562, 0, 13, 32, 37, 15, 1, 0, 16, 48, 15),
  (2563, 1, 4, 12, 49, 15, 1, 4, 32, 39, 15),
  (2564, 1, 17, 47, 8, 12, 3, 8, 9, 49, 15),
  (2565, 0, 25, 44, 2, 11, 0, 28, 34, 25, 14),
  (2566, 0, 46, 21, 3, 10, 1, 16, 48, 2, 11),
  (2567, 1, 2, 31, 40, 15, 1, 8, 10, 49, 15),
  (2568, 3, 49, 10, 7, 10, 5, 6, 9, 49, 15),
  (2569, 2, 34, 6, 37, 14, 2, 34, 26, 27, 14),
  (2570, 0, 3, 31, 40, 15, 0, 5, 12, 49, 15),
  (2571, 0, 7, 11, 49, 15, 0, 19, 29, 37, 15),
  (2572, 1, 25, 37, 24, 14, 1, 45, 17, 16, 12),
  (2573, 0, 13, 10, 48, 15, 0, 21, 14, 44, 15),
  (2574, 0, 10, 43, 25, 14, 0, 19, 47, 2, 11),
  (2575, 1, 8, 50, 3, 11, 1, 48, 10, 13, 11),
  (2576, 0, 20, 40, 24, 14, 0, 24, 44, 8, 12),
  (2577, 2, 12, 43, 24, 14, 6, 35, 32, 16, 13),
  (2578, 1, 16, 32, 36, 15, 1, 24, 20, 40, 15),
  (2579, 0, 3, 13, 49, 15, 0, 11, 33, 37, 15),
  (2580, 0, 20, 46, 8, 12, 3, 31, 1, 40, 14),
  (2581, 0, 18, 41, 24, 14, 0, 22, 39, 24, 14),
  (2582, 0, 1, 30, 41, 15, 0, 2, 43, 27, 14),
  (2583, 1, 0, 30, 41, 15, 1, 14, 9, 48, 15),
  (2584, 1, 10, 9, 49, 15, 1, 22, 27, 37, 15),
  (2585, 0, 48, 16, 5, 10, 2, 19, 10, 46, 15),
  (2586, 0, 11, 47, 16, 13, 0, 31, 37, 16, 13),
  (2587, 1, 30, 41, 2, 11, 1, 35, 8, 36, 14),
  (2588, 1, 29, 41, 8, 12, 2, 46, 8, 20, 12),
  (2589, 0, 26, 43, 8, 12, 2, 30, 0, 41, 14),
  (2590, 0, 9, 50, 3, 11, 3, 42, 18, 22, 13),
  (2591, 1, 8, 34, 37, 15, 1, 22, 13, 44, 15),
  (2592, 1, 50, 9, 3, 9, 2, 42, 26, 12, 12),
  (2593, 0, 37, 30, 18, 13, 2, 28, 35, 24, 14),
  (2594, 0, 21, 28, 37, 15, 1, 48, 12, 12, 11),
  (2595, 1, 15, 48, 8, 12, 2, 21, 11, 45, 15),
  (2596, 0, 16, 42, 24, 14, 0, 24, 38, 24, 14),
  (2597, 0, 17, 48, 2, 11, 0, 18, 47, 8, 12),
  (2598, 0, 1, 14, 49, 15, 0, 17, 10, 47, 15),
  (2599, 1, 0, 14, 49, 15, 1, 16, 46, 15, 13)
  ]

lemma witChunk_47_ok : witChunk_47.all checkWit = true := by
  decide +kernel

lemma witChunk_47_ns :
    witChunk_47.map (fun t => t.1) = (List.range 50).map (· + 2550) := by
  decide +kernel

def witChunk_48 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2600, 0, 32, 30, 26, 14, 3, 17, 42, 23, 14),
  (2601, 2, 15, 8, 48, 15, 2, 46, 6, 21, 12),
  (2602, 0, 21, 44, 15, 13, 3, 42, 6, 28, 13),
  (2603, 0, 11, 9, 49, 15, 0, 23, 15, 43, 15),
  (2604, 1, 35, 36, 9, 12, 1, 45, 1, 24, 12),
  (2605, 0, 42, 29, 0, 10, 2, 6, 44, 25, 14),
  (2606, 0, 9, 34, 37, 15, 0, 34, 37, 9, 12),
  (2607, 3, 37, 14, 32, 14, 5, 6, 35, 36, 15),
  (2608, 1, 33, 29, 26, 14, 1, 49, 13, 6, 10),
  (2609, 0, 17, 32, 36, 15, 0, 29, 42, 2, 11),
  (2610, 0, 15, 9, 48, 15, 0, 15, 33, 36, 15),
  (2611, 0, 19, 45, 15, 13, 0, 39, 27, 19, 13),
  (2612, 0, 28, 42, 8, 12, 1, 7, 44, 25, 14),
  (2613, 0, 44, 26, 1, 10, 1, 45, 19, 15, 12),
  (2614, 0, 25, 42, 15, 13, 0, 30, 33, 25, 14),
  (2615, 3, 2, 48, 17, 13, 3, 4, 9, 50, 15),
  (2616, 0, 4, 50, 10, 12, 0, 44, 22, 14, 12),
  (2617, 2, 3, 10, 50, 15, 2, 3, 34, 38, 15),
  (2618, 0, 5, 48, 17, 13, 0, 19, 31, 36, 15),
  (2619, 0, 3, 33, 39, 15, 1, 6, 9, 50, 15),
  (2620, 1, 37, 15, 32, 14, 1, 47, 20, 3, 10),
  (2621, 0, 0, 50, 11, 12, 0, 13, 34, 36, 15),
  (2622, 2, 25, 15, 42, 15, 2, 33, 39, 2, 11),
  (2623, 1, 2, 51, 4, 11, 1, 3, 44, 26, 14),
  (2624, 0, 16, 48, 8, 12, 2, 2, 44, 26, 14),
  (2625, 0, 1, 32, 40, 15, 0, 5, 10, 50, 15),
  (2626, 0, 3, 51, 4, 11, 0, 39, 33, 4, 11),
  (2627, 0, 23, 27, 37, 15, 1, 2, 11, 50, 15),
  (2628, 0, 4, 44, 26, 14, 0, 32, 2, 40, 14),
  (2629, 0, 1, 48, 18, 13, 1, 37, 13, 33, 14),
  (2630, 0, 3, 11, 50, 15, 0, 7, 9, 50, 15),
  (2631, 3, 1, 44, 26, 14, 3, 8, 7, 50, 15),
  (2632, 1, 6, 35, 37, 15, 1, 7, 50, 9, 12),
  (2633, 0, 38, 33, 10, 12, 2, 11, 50, 2, 11),
  (2634, 0, 13, 8, 49, 15, 0, 23, 13, 44, 15),
  (2635, 0, 27, 41, 15, 13, 1, 11, 44, 24, 14),
  (2636, 1, 13, 49, 8, 12, 2, 46, 16, 16, 12),
  (2637, 0, 21, 30, 36, 15, 0, 42, 27, 12, 12),
  (2638, 2, 9, 7, 50, 15, 2, 31, 38, 15, 13),
  (2639, 1, 16, 34, 35, 15, 1, 26, 19, 40, 15),
  (2640, 1, 18, 33, 35, 15, 1, 26, 21, 39, 15),
  (2641, 0, 9, 48, 16, 13, 0, 33, 36, 16, 13),
  (2642, 0, 11, 35, 36, 15, 1, 40, 32, 4, 11),
  (2643, 0, 7, 35, 37, 15, 0, 43, 13, 25, 13),
  (2644, 0, 48, 18, 4, 10, 1, 29, 35, 24, 14),
  (2645, 0, 1, 12, 50, 15, 0, 8, 50, 9, 12),
  (2646, 0, 31, 41, 2, 11, 0, 41, 2, 31, 13),
  (2647, 1, 39, 32, 10, 12, 3, 10, 48, 15, 13),
  (2648, 1, 6, 51, 3, 11, 1, 14, 7, 49, 15),
  (2649, 0, 46, 23, 2, 10, 2, 7, 36, 36, 15)
  ]

lemma witChunk_48_ok : witChunk_48.all checkWit = true := by
  decide +kernel

lemma witChunk_48_ns :
    witChunk_48.map (fun t => t.1) = (List.range 50).map (· + 2600) := by
  decide +kernel

def witChunk_49 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2650, 0, 43, 15, 24, 13, 0, 45, 24, 7, 11),
  (2651, 0, 19, 9, 47, 15, 0, 47, 19, 9, 11),
  (2652, 2, 50, 0, 12, 10, 3, 13, 44, 23, 14),
  (2653, 1, 21, 41, 23, 14, 1, 37, 21, 29, 14),
  (2654, 0, 46, 3, 23, 12, 2, 23, 46, 1, 11),
  (2655, 3, 16, 35, 34, 15, 3, 37, 22, 28, 14),
  (2656, 0, 12, 44, 24, 14, 0, 28, 36, 24, 14),
  (2657, 0, 17, 8, 48, 15, 0, 21, 10, 46, 15),
  (2658, 1, 8, 36, 36, 15, 1, 24, 12, 44, 15),
  (2659, 0, 7, 51, 3, 11, 0, 15, 47, 15, 13),
  (2660, 1, 23, 40, 23, 14, 3, 17, 48, 7, 12),
  (2661, 0, 14, 49, 8, 12, 0, 46, 17, 16, 12),
  (2662, 0, 49, 6, 15, 11, 1, 48, 16, 10, 11),
  (2663, 3, 9, 50, 8, 12, 3, 20, 33, 34, 15),
  (2664, 1, 45, 21, 14, 12, 5, 2, 51, 3, 11),
  (2665, 0, 0, 44, 27, 14, 2, 11, 6, 50, 15),
  (2666, 0, 23, 29, 36, 15, 0, 29, 40, 15, 13),
  (2667, 0, 43, 17, 23, 13, 1, 12, 36, 35, 15),
  (2668, 3, 7, 45, 24, 14, 7, 12, 5, 49, 15),
  (2669, 1, 17, 43, 23, 14, 2, 14, 44, 23, 14),
  (2670, 0, 11, 7, 50, 15, 0, 17, 34, 35, 15),
  (2671, 1, 43, 26, 12, 12, 3, 40, 27, 18, 13),
  (2672, 1, 22, 31, 35, 15, 1, 26, 25, 37, 15),
  (2673, 0, 9, 36, 36, 15, 0, 13, 50, 2, 11),
  (2674, 0, 37, 36, 3, 11, 2, 4, 45, 25, 14),
  (2675, 0, 15, 7, 49, 15, 0, 15, 35, 35, 15),
  (2676, 1, 33, 39, 8, 12, 2, 38, 18, 30, 14),
  (2677, 1, 5, 45, 25, 14, 1, 25, 39, 23, 14),
  (2678, 0, 1, 34, 39, 15, 0, 3, 35, 38, 15),
  (2679, 1, 0, 34, 39, 15, 1, 18, 7, 48, 15),
  (2680, 1, 38, 35, 3, 11, 4, 20, 42, 22, 14),
  (2681, 0, 44, 24, 13, 12, 2, 19, 34, 34, 15),
  (2682, 0, 37, 32, 17, 13, 0, 43, 7, 28, 13),
  (2683, 1, 4, 8, 51, 15, 1, 4, 36, 37, 15),
  (2684, 1, 9, 45, 24, 14, 1, 37, 23, 28, 14),
  (2685, 2, 15, 36, 34, 15, 2, 18, 48, 7, 12),
  (2686, 0, 6, 45, 25, 14, 0, 34, 3, 39, 14),
  (2687, 1, 11, 50, 8, 12, 1, 35, 4, 38, 14),
  (2688, 0, 32, 40, 8, 12, 1, 2, 9, 51, 15),
  (2689, 0, 49, 12, 12, 11, 2, 34, 2, 39, 14),
  (2690, 0, 5, 8, 51, 15, 0, 5, 36, 37, 15),
  (2691, 0, 3, 9, 51, 15, 0, 27, 21, 39, 15),
  (2692, 1, 15, 44, 23, 14, 1, 33, 1, 40, 14),
  (2693, 0, 20, 42, 23, 14, 0, 33, 40, 2, 11),
  (2694, 0, 22, 41, 23, 14, 0, 38, 17, 31, 14),
  (2695, 1, 6, 49, 16, 13, 1, 16, 6, 49, 15),
  (2696, 1, 2, 49, 17, 13, 1, 10, 37, 35, 15),
  (2697, 2, 27, 14, 42, 15, 2, 27, 42, 14, 13),
  (2698, 0, 13, 48, 15, 13, 2, 5, 37, 36, 15),
  (2699, 0, 3, 49, 17, 13, 0, 7, 7, 51, 15)
  ]

lemma witChunk_49_ok : witChunk_49.all checkWit = true := by
  decide +kernel

lemma witChunk_49_ns :
    witChunk_49.map (fun t => t.1) = (List.range 50).map (· + 2650) := by
  decide +kernel

def witChunk_50 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2700, 2, 46, 0, 24, 12, 3, 0, 9, 51, 15),
  (2701, 0, 10, 45, 24, 14, 0, 30, 35, 24, 14),
  (2702, 0, 1, 10, 51, 15, 0, 18, 43, 23, 14),
  (2703, 1, 0, 10, 51, 15, 1, 6, 37, 36, 15),
  (2704, 1, 1, 45, 26, 14, 1, 1, 51, 10, 12),
  (2705, 0, 2, 45, 26, 14, 0, 2, 51, 10, 12),
  (2706, 0, 7, 49, 16, 13, 0, 35, 35, 16, 13),
  (2707, 0, 31, 39, 15, 13, 1, 10, 51, 2, 11),
  (2708, 0, 12, 50, 8, 12, 1, 49, 17, 4, 10),
  (2709, 1, 5, 51, 9, 12, 2, 0, 45, 26, 14),
  (2710, 1, 16, 36, 34, 15, 1, 24, 44, 14, 13),
  (2711, 1, 47, 4, 22, 12, 1, 48, 18, 9, 11),
  (2712, 0, 52, 2, 2, 8, 3, 19, 43, 22, 14),
  (2713, 0, 48, 20, 3, 10, 0, 52, 0, 3, 8),
  (2714, 0, 7, 37, 36, 15, 0, 19, 7, 48, 15),
  (2715, 0, 11, 37, 35, 15, 0, 23, 31, 35, 15),
  (2716, 1, 19, 48, 7, 12, 1, 27, 44, 7, 12),
  (2717, 2, 23, 8, 46, 15, 2, 23, 32, 34, 15),
  (2718, 0, 6, 51, 9, 12, 0, 9, 6, 51, 15),
  (2719, 1, 51, 4, 10, 10, 3, 37, 6, 36, 14),
  (2720, 0, 44, 28, 0, 10, 1, 51, 6, 9, 10),
  (2721, 0, 1, 52, 4, 11, 0, 16, 44, 23, 14),
  (2722, 1, 0, 52, 4, 11, 2, 37, 33, 16, 13),
  (2723, 0, 27, 25, 37, 15, 1, 14, 5, 50, 15),
  (2724, 0, 40, 32, 10, 12, 3, 32, 41, 1, 11),
  (2725, 0, 49, 0, 18, 11, 1, 13, 45, 23, 14),
  (2726, 0, 11, 51, 2, 11, 0, 17, 6, 49, 15),
  (2727, 1, 50, 15, 0, 9, 3, 17, 44, 22, 14),
  (2728, 1, 10, 5, 51, 15, 1, 10, 49, 15, 13),
  (2729, 2, 11, 38, 34, 15, 2, 50, 14, 5, 10),
  (2730, 2, 3, 52, 3, 11, 2, 27, 12, 43, 15),
  (2731, 0, 43, 21, 21, 13, 1, 4, 52, 3, 11),
  (2732, 3, 7, 51, 8, 12, 3, 16, 37, 33, 15),
  (2733, 2, 15, 48, 14, 13, 2, 30, 36, 23, 14),
  (2734, 2, 15, 50, 1, 11, 2, 29, 21, 38, 15),
  (2735, 1, 8, 38, 35, 15, 1, 26, 11, 44, 15),
  (2736, 2, 6, 46, 24, 14, 3, 13, 50, 7, 12),
  (2737, 0, 45, 26, 6, 11, 2, 8, 51, 8, 12),
  (2738, 0, 5, 52, 3, 11, 2, 29, 17, 40, 15),
  (2739, 0, 23, 47, 1, 11, 2, 25, 9, 45, 15),
  (2740, 0, 52, 6, 0, 8, 1, 39, 16, 31, 14),
  (2741, 0, 1, 36, 38, 15, 0, 17, 36, 34, 15),
  (2742, 0, 19, 35, 34, 15, 0, 22, 47, 7, 12),
  (2743, 1, 7, 46, 24, 14, 1, 39, 14, 32, 14),
  (2744, 1, 2, 37, 37, 15, 1, 22, 7, 47, 15),
  (2745, 4, 29, 24, 36, 15, 8, 24, 40, 21, 14),
  (2746, 0, 21, 48, 1, 11, 1, 12, 38, 34, 15),
  (2747, 0, 3, 37, 37, 15, 0, 11, 5, 51, 15),
  (2748, 1, 9, 51, 8, 12, 3, 40, 29, 17, 13),
  (2749, 2, 15, 4, 50, 15, 2, 24, 41, 22, 14)
  ]

lemma witChunk_50_ok : witChunk_50.all checkWit = true := by
  decide +kernel

lemma witChunk_50_ns :
    witChunk_50.map (fun t => t.1) = (List.range 50).map (· + 2700) := by
  decide +kernel

def witChunk_51 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2750, 0, 9, 38, 35, 15, 0, 14, 45, 23, 14),
  (2751, 3, 50, 8, 13, 11, 5, 3, 46, 24, 14),
  (2752, 1, 3, 46, 25, 14, 1, 18, 5, 49, 15),
  (2753, 0, 20, 48, 7, 12, 0, 21, 34, 34, 15),
  (2754, 0, 27, 27, 36, 15, 2, 19, 36, 33, 15),
  (2755, 0, 27, 45, 1, 11, 0, 39, 35, 3, 11),
  (2756, 0, 8, 46, 24, 14, 0, 32, 34, 24, 14),
  (2757, 0, 4, 46, 25, 14, 0, 25, 44, 14, 13),
  (2758, 0, 33, 38, 15, 13, 0, 43, 3, 30, 13),
  (2759, 1, 2, 7, 52, 15, 1, 16, 50, 1, 11),
  (2760, 1, 39, 34, 9, 12, 1, 47, 18, 15, 12),
  (2761, 2, 43, 2, 30, 13, 2, 48, 7, 20, 12),
  (2762, 0, 3, 7, 52, 15, 0, 29, 20, 39, 15),
  (2763, 0, 19, 49, 1, 11, 1, 12, 4, 51, 15),
  (2764, 1, 39, 20, 29, 14, 2, 34, 0, 40, 14),
  (2765, 0, 5, 6, 52, 15, 0, 5, 38, 36, 15),
  (2766, 0, 19, 47, 14, 13, 2, 9, 39, 34, 15),
  (2767, 1, 6, 5, 52, 15, 1, 40, 34, 3, 11),
  (2768, 0, 48, 8, 20, 12, 1, 11, 46, 23, 14),
  (2769, 0, 1, 8, 52, 15, 0, 13, 38, 34, 15),
  (2770, 1, 0, 8, 52, 15, 1, 48, 20, 8, 11),
  (2771, 0, 39, 31, 17, 13, 0, 51, 13, 1, 9),
  (2772, 0, 48, 12, 18, 12, 2, 42, 30, 10, 12),
  (2773, 1, 49, 19, 3, 10, 2, 3, 50, 16, 13),
  (2774, 0, 18, 49, 7, 12, 0, 23, 33, 34, 15),
  (2775, 3, 34, 40, 1, 11, 5, 18, 49, 0, 11),
  (2776, 1, 15, 50, 7, 12, 1, 21, 43, 22, 14),
  (2777, 2, 7, 4, 52, 15, 2, 46, 22, 13, 12),
  (2778, 0, 7, 5, 52, 15, 0, 29, 16, 41, 15),
  (2779, 1, 10, 39, 34, 15, 1, 23, 42, 22, 14),
  (2780, 2, 50, 16, 4, 10, 3, 4, 39, 35, 15),
  (2781, 0, 5, 50, 16, 13, 0, 21, 6, 48, 15),
  (2782, 2, 7, 50, 15, 13, 2, 23, 6, 47, 15),
  (2783, 1, 19, 44, 22, 14, 1, 51, 12, 6, 10),
  (2784, 1, 6, 39, 35, 15, 1, 18, 37, 33, 15),
  (2785, 4, 30, 37, 22, 14, 6, 36, 29, 24, 14),
  (2786, 0, 13, 4, 51, 15, 0, 27, 11, 44, 15),
  (2787, 0, 19, 5, 49, 15, 0, 23, 7, 47, 15),
  (2788, 1, 31, 36, 23, 14, 1, 47, 24, 1, 10),
  (2789, 0, 9, 52, 2, 11, 0, 12, 46, 23, 14),
  (2790, 0, 1, 50, 17, 13, 0, 17, 50, 1, 11),
  (2791, 1, 0, 50, 17, 13, 1, 8, 50, 15, 13),
  (2792, 0, 0, 46, 26, 14, 0, 48, 22, 2, 10),
  (2793, 2, 27, 30, 34, 15, 2, 48, 15, 16, 12),
  (2794, 0, 45, 12, 25, 13, 2, 40, 15, 31, 14),
  (2795, 0, 7, 39, 35, 15, 0, 27, 29, 35, 15),
  (2796, 1, 3, 52, 9, 12, 1, 45, 25, 12, 12),
  (2797, 0, 45, 14, 24, 13, 2, 2, 52, 9, 12),
  (2798, 0, 11, 39, 34, 15, 0, 30, 37, 23, 14),
  (2799, 3, 21, 48, 6, 12, 3, 26, 44, 13, 13)
  ]

lemma witChunk_51_ok : witChunk_51.all checkWit = true := by
  decide +kernel

lemma witChunk_51_ns :
    witChunk_51.map (fun t => t.1) = (List.range 50).map (· + 2750) := by
  decide +kernel

def witChunk_52 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2800, 1, 14, 51, 1, 11, 1, 17, 45, 22, 14),
  (2801, 0, 4, 52, 9, 12, 0, 9, 4, 52, 15),
  (2802, 2, 9, 3, 52, 15, 2, 12, 51, 7, 12),
  (2803, 2, 29, 27, 35, 15, 3, 24, 47, 0, 11),
  (2804, 0, 0, 52, 10, 12, 0, 36, 38, 8, 12),
  (2805, 0, 16, 50, 7, 12, 0, 17, 4, 50, 15),
  (2806, 0, 9, 50, 15, 13, 0, 49, 18, 9, 11),
  (2807, 1, 47, 20, 14, 12, 3, 10, 40, 33, 15),
  (2808, 1, 14, 3, 51, 15, 1, 14, 39, 33, 15),
  (2809, 2, 4, 47, 24, 14, 2, 39, 32, 16, 13),
  (2810, 0, 45, 16, 23, 13, 1, 52, 10, 2, 9),
  (2811, 0, 31, 43, 1, 11, 0, 43, 1, 31, 13),
  (2812, 1, 5, 47, 24, 14, 1, 39, 8, 35, 14),
  (2813, 0, 29, 26, 36, 15, 2, 7, 40, 34, 15),
  (2814, 0, 1, 38, 37, 15, 0, 46, 23, 13, 12),
  (2815, 1, 0, 38, 37, 15, 1, 10, 3, 52, 15),
  (2816, 0, 48, 16, 16, 12, 1, 53, 1, 2, 8),
  (2817, 0, 22, 43, 22, 14, 0, 37, 38, 2, 11),
  (2818, 0, 45, 8, 27, 13, 2, 11, 40, 33, 15),
  (2819, 0, 19, 37, 33, 15, 0, 35, 37, 15, 13),
  (2820, 0, 20, 44, 22, 14, 0, 40, 14, 32, 14),
  (2821, 0, 6, 47, 24, 14, 0, 34, 33, 24, 14),
  (2822, 0, 15, 49, 14, 13, 0, 17, 38, 33, 15),
  (2823, 1, 2, 39, 36, 15, 1, 24, 6, 47, 15),
  (2824, 0, 24, 42, 22, 14, 0, 40, 18, 30, 14),
  (2825, 0, 42, 31, 10, 12, 2, 11, 50, 14, 13),
  (2826, 0, 3, 39, 36, 15, 0, 21, 36, 33, 15),
  (2827, 0, 3, 53, 3, 11, 0, 15, 51, 1, 11),
  (2828, 1, 39, 24, 27, 14, 3, 20, 3, 49, 15),
  (2829, 0, 52, 2, 11, 10, 2, 24, 47, 6, 12),
  (2830, 4, 26, 41, 21, 14, 4, 38, 27, 25, 14),
  (2831, 3, 29, 44, 6, 12, 3, 53, 0, 2, 8),
  (2832, 0, 8, 52, 8, 12, 0, 52, 8, 8, 10),
  (2833, 0, 18, 45, 22, 14, 0, 40, 12, 33, 14),
  (2834, 0, 11, 3, 52, 15, 0, 29, 12, 43, 15),
  (2835, 0, 15, 3, 51, 15, 0, 15, 39, 33, 15),
  (2836, 1, 53, 5, 0, 8, 2, 26, 46, 6, 12),
  (2837, 0, 9, 40, 34, 15, 0, 32, 42, 7, 12),
  (2838, 0, 2, 47, 25, 14, 0, 10, 47, 23, 14),
  (2839, 1, 48, 22, 7, 11, 5, 26, 33, 32, 15),
  (2840, 1, 2, 5, 53, 15, 1, 34, 41, 1, 11),
  (2841, 0, 26, 41, 22, 14, 0, 40, 20, 29, 14),
  (2842, 1, 12, 50, 14, 13, 1, 28, 30, 34, 15),
  (2843, 0, 3, 5, 53, 15, 0, 23, 35, 33, 15),
  (2844, 2, 46, 24, 12, 12, 3, 16, 49, 13, 13),
  (2845, 0, 45, 6, 28, 13, 0, 46, 27, 0, 10),
  (2846, 0, 1, 6, 53, 15, 0, 14, 51, 7, 12),
  (2847, 1, 0, 6, 53, 15, 3, 2, 4, 53, 15),
  (2848, 0, 52, 0, 12, 10, 1, 29, 39, 22, 14),
  (2849, 0, 32, 36, 23, 14, 0, 38, 27, 26, 14)
  ]

lemma witChunk_52_ok : witChunk_52.all checkWit = true := by
  decide +kernel

lemma witChunk_52_ns :
    witChunk_52.map (fun t => t.1) = (List.range 50).map (· + 2800) := by
  decide +kernel

def witChunk_53 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2850, 0, 5, 4, 53, 15, 0, 5, 40, 35, 15),
  (2851, 0, 51, 5, 15, 11, 0, 51, 9, 13, 11),
  (2852, 1, 49, 7, 20, 12, 3, 0, 5, 53, 15),
  (2853, 0, 48, 18, 15, 12, 0, 52, 10, 7, 10),
  (2854, 0, 33, 42, 1, 11, 1, 12, 2, 52, 15),
  (2855, 1, 39, 6, 36, 14, 3, 41, 16, 30, 14),
  (2856, 0, 16, 46, 22, 14, 0, 40, 10, 34, 14),
  (2857, 2, 15, 40, 32, 15, 2, 23, 4, 48, 15),
  (2858, 0, 13, 40, 33, 15, 0, 21, 4, 49, 15),
  (2859, 0, 31, 23, 37, 15, 2, 5, 51, 15, 13),
  (2860, 3, 4, 51, 15, 13, 3, 39, 5, 36, 14),
  (2861, 0, 53, 6, 4, 9, 1, 49, 13, 17, 12),
  (2862, 0, 7, 53, 2, 11, 4, 29, 30, 33, 15),
  (2863, 1, 2, 51, 16, 13, 1, 16, 2, 51, 15),
  (2864, 1, 6, 51, 15, 13, 1, 13, 47, 22, 14),
  (2865, 0, 13, 50, 14, 13, 0, 49, 20, 8, 11),
  (2866, 0, 3, 51, 16, 13, 0, 39, 33, 16, 13),
  (2867, 0, 7, 3, 53, 15, 0, 31, 15, 41, 15),
  (2868, 0, 28, 40, 22, 14, 0, 40, 22, 28, 14),
  (2869, 1, 41, 15, 31, 14, 1, 49, 5, 21, 12),
  (2870, 0, 19, 3, 50, 15, 0, 25, 6, 47, 15),
  (2871, 1, 18, 39, 32, 15, 1, 23, 48, 6, 12),
  (2872, 1, 10, 41, 33, 15, 1, 25, 47, 6, 12),
  (2873, 2, 19, 2, 50, 15, 2, 35, 38, 14, 13),
  (2874, 0, 13, 52, 1, 11, 2, 20, 45, 21, 14),
  (2875, 0, 7, 51, 15, 13, 1, 6, 41, 34, 15),
  (2876, 1, 11, 52, 7, 12, 1, 35, 40, 7, 12),
  (2877, 0, 13, 2, 52, 15, 0, 29, 10, 44, 15),
  (2878, 4, 3, 41, 34, 15, 4, 7, 51, 14, 13),
  (2879, 1, 8, 2, 53, 15, 1, 22, 37, 32, 15),
  (2880, 0, 48, 0, 24, 12, 1, 21, 49, 6, 12),
  (2881, 0, 48, 24, 1, 10, 4, 4, 48, 23, 14),
  (2882, 0, 31, 25, 36, 15, 0, 45, 4, 29, 13),
  (2883, 1, 27, 46, 6, 12, 1, 39, 36, 8, 12),
  (2884, 0, 52, 12, 6, 10, 1, 7, 48, 23, 14),
  (2885, 0, 33, 40, 14, 13, 0, 46, 25, 12, 12),
  (2886, 0, 7, 41, 34, 15, 0, 34, 41, 7, 12),
  (2887, 1, 22, 49, 0, 11, 1, 26, 47, 0, 11),
  (2888, 3, 41, 10, 33, 14, 5, 14, 41, 31, 15),
  (2889, 0, 14, 47, 22, 14, 0, 40, 8, 35, 14),
  (2890, 0, 37, 36, 15, 13, 2, 43, 32, 3, 11),
  (2891, 0, 11, 41, 33, 15, 0, 51, 1, 17, 11),
  (2892, 2, 2, 48, 24, 14, 3, 8, 1, 53, 15),
  (2893, 1, 1, 53, 9, 12, 1, 37, 1, 39, 14),
  (2894, 0, 2, 53, 9, 12, 0, 9, 2, 53, 15),
  (2895, 5, 26, 45, 12, 13, 5, 28, 6, 45, 15),
  (2896, 0, 4, 48, 24, 14, 0, 36, 0, 40, 14),
  (2897, 0, 1, 40, 36, 15, 0, 8, 48, 23, 14),
  (2898, 1, 0, 40, 36, 15, 1, 24, 4, 48, 15),
  (2899, 1, 10, 51, 14, 13, 1, 19, 50, 6, 12)
  ]

lemma witChunk_53_ok : witChunk_53.all checkWit = true := by
  decide +kernel

lemma witChunk_53_ns :
    witChunk_53.map (fun t => t.1) = (List.range 50).map (· + 2850) := by
  decide +kernel

def witChunk_54 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2900, 0, 48, 20, 14, 12, 1, 5, 53, 8, 12),
  (2901, 2, 16, 51, 6, 12, 4, 9, 42, 32, 15),
  (2902, 0, 43, 27, 18, 13, 1, 20, 50, 0, 11),
  (2903, 1, 14, 1, 52, 15, 1, 14, 41, 32, 15),
  (2904, 1, 29, 45, 6, 12, 3, 49, 22, 1, 10),
  (2905, 0, 30, 39, 22, 14, 0, 40, 24, 27, 14),
  (2906, 0, 19, 39, 32, 15, 1, 20, 2, 50, 15),
  (2907, 0, 23, 47, 13, 13, 0, 27, 33, 33, 15),
  (2908, 1, 23, 44, 21, 14, 1, 37, 31, 24, 14),
  (2909, 0, 6, 53, 8, 12, 0, 21, 38, 32, 15),
  (2910, 0, 25, 46, 13, 13, 0, 34, 35, 23, 14),
  (2911, 1, 11, 48, 22, 14, 5, 11, 52, 6, 12),
  (2912, 1, 2, 41, 35, 15, 1, 10, 1, 53, 15),
  (2913, 0, 17, 40, 32, 15, 0, 53, 10, 2, 9),
  (2914, 0, 21, 48, 13, 13, 2, 16, 47, 21, 14),
  (2915, 0, 3, 41, 35, 15, 0, 31, 27, 35, 15),
  (2916, 0, 24, 48, 6, 12, 3, 16, 41, 31, 15),
  (2917, 1, 25, 43, 21, 14, 1, 49, 17, 15, 12),
  (2918, 0, 11, 51, 14, 13, 1, 48, 24, 6, 11),
  (2919, 1, 8, 42, 33, 15, 1, 30, 9, 44, 15),
  (2920, 1, 19, 46, 21, 14, 1, 30, 43, 13, 13),
  (2921, 0, 22, 49, 6, 12, 0, 26, 47, 6, 12),
  (2922, 0, 23, 37, 32, 15, 2, 33, 15, 40, 15),
  (2923, 0, 27, 45, 13, 13, 2, 29, 7, 45, 15),
  (2924, 1, 53, 7, 8, 10, 3, 0, 41, 35, 15),
  (2925, 0, 52, 14, 5, 10, 3, 7, 53, 7, 12),
  (2926, 0, 1, 54, 3, 11, 0, 51, 15, 10, 11),
  (2927, 1, 0, 54, 3, 11, 1, 16, 50, 13, 13),
  (2928, 1, 17, 51, 6, 12, 1, 18, 1, 51, 15),
  (2929, 0, 0, 48, 25, 14, 0, 25, 48, 0, 11),
  (2930, 0, 15, 1, 52, 15, 0, 15, 41, 32, 15),
  (2931, 0, 11, 1, 53, 15, 0, 11, 53, 1, 11),
  (2932, 0, 12, 48, 22, 14, 0, 40, 6, 36, 14),
  (2933, 0, 1, 4, 54, 15, 0, 33, 20, 38, 15),
  (2934, 0, 3, 3, 54, 15, 0, 9, 42, 33, 15),
  (2935, 1, 31, 44, 6, 12, 5, 30, 7, 44, 15),
  (2936, 0, 20, 50, 6, 12, 0, 28, 46, 6, 12),
  (2937, 2, 3, 2, 54, 15, 2, 3, 42, 34, 15),
  (2938, 0, 27, 47, 0, 11, 1, 4, 2, 54, 15),
  (2939, 0, 23, 3, 49, 15, 1, 52, 8, 13, 11),
  (2940, 2, 42, 12, 32, 14, 2, 54, 4, 0, 8),
  (2941, 0, 21, 50, 0, 11, 0, 45, 30, 4, 11),
  (2942, 0, 33, 22, 37, 15, 0, 35, 39, 14, 13),
  (2943, 3, 0, 3, 54, 15, 3, 18, 0, 51, 15),
  (2944, 1, 33, 37, 22, 14, 2, 14, 52, 6, 12),
  (2945, 0, 5, 2, 54, 15, 0, 5, 42, 34, 15),
  (2946, 0, 29, 44, 13, 13, 2, 3, 52, 15, 13),
  (2947, 0, 43, 33, 3, 11, 1, 4, 52, 15, 13),
  (2948, 3, 49, 0, 23, 12, 3, 53, 0, 11, 10),
  (2949, 0, 50, 7, 20, 12, 2, 14, 48, 21, 14)
  ]

lemma witChunk_54_ok : witChunk_54.all checkWit = true := by
  decide +kernel

lemma witChunk_54_ns :
    witChunk_54.map (fun t => t.1) = (List.range 50).map (· + 2900) := by
  decide +kernel

def witChunk_55 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (2950, 0, 22, 45, 21, 14, 0, 42, 15, 31, 14),
  (2951, 3, 2, 52, 15, 13, 3, 4, 1, 54, 15),
  (2952, 0, 32, 38, 22, 14, 0, 40, 26, 26, 14),
  (2953, 0, 24, 44, 21, 14, 0, 42, 17, 30, 14),
  (2954, 0, 5, 52, 15, 13, 0, 29, 32, 33, 15),
  (2955, 0, 47, 11, 25, 13, 1, 6, 1, 54, 15),
  (2956, 1, 43, 32, 9, 12, 2, 42, 20, 28, 14),
  (2957, 0, 13, 42, 32, 15, 0, 20, 46, 21, 14),
  (2958, 0, 10, 53, 7, 12, 0, 17, 50, 13, 13),
  (2959, 1, 32, 42, 13, 13, 1, 46, 21, 20, 13),
  (2960, 0, 40, 36, 8, 12, 1, 49, 19, 14, 12),
  (2961, 0, 1, 52, 16, 13, 0, 18, 51, 6, 12),
  (2962, 0, 19, 51, 0, 11, 0, 45, 24, 19, 13),
  (2963, 0, 19, 1, 51, 15, 0, 27, 5, 47, 15),
  (2964, 2, 34, 42, 6, 12, 3, 52, 11, 11, 11),
  (2965, 1, 29, 41, 21, 14, 2, 50, 4, 21, 12),
  (2966, 0, 6, 49, 23, 14, 0, 7, 1, 54, 15),
  (2967, 1, 15, 52, 6, 12, 3, 50, 20, 7, 11),
  (2968, 1, 9, 49, 22, 14, 1, 14, 51, 13, 13),
  (2969, 2, 31, 8, 44, 15, 6, 50, 6, 19, 12),
  (2970, 0, 37, 40, 1, 11, 2, 19, 0, 51, 15),
  (2971, 0, 39, 35, 15, 13, 0, 51, 17, 9, 11),
  (2972, 1, 15, 48, 21, 14, 1, 41, 35, 8, 12),
  (2973, 2, 7, 0, 54, 15, 2, 38, 0, 39, 14),
  (2974, 0, 18, 47, 21, 14, 0, 42, 11, 33, 14),
  (2975, 1, 10, 43, 32, 15, 1, 32, 10, 43, 15),
  (2976, 0, 52, 16, 4, 10, 1, 6, 43, 33, 15),
  (2977, 4, 10, 53, 6, 12, 4, 40, 36, 7, 12),
  (2978, 0, 13, 0, 53, 15, 0, 27, 35, 32, 15),
  (2979, 0, 31, 43, 13, 13, 0, 43, 29, 17, 13),
  (2980, 0, 48, 26, 0, 10, 1, 1, 49, 24, 14),
  (2981, 0, 2, 49, 24, 14, 0, 9, 52, 14, 13),
  (2982, 0, 47, 17, 22, 13, 1, 8, 0, 54, 15),
  (2983, 1, 8, 54, 1, 11, 1, 16, 42, 31, 15),
  (2984, 1, 41, 25, 26, 14, 3, 11, 53, 6, 12),
  (2985, 0, 10, 49, 22, 14, 0, 40, 4, 37, 14),
  (2986, 0, 31, 45, 0, 11, 0, 45, 0, 31, 13),
  (2987, 0, 7, 43, 33, 15, 0, 47, 7, 27, 13),
  (2988, 3, 19, 47, 20, 14, 3, 28, 35, 31, 15),
  (2989, 0, 28, 42, 21, 14, 0, 42, 21, 28, 14),
  (2990, 0, 1, 42, 35, 15, 0, 33, 26, 35, 15),
  (2991, 1, 0, 42, 35, 15, 1, 3, 54, 8, 12),
  (2992, 1, 50, 21, 7, 11, 2, 2, 54, 8, 12),
  (2993, 0, 17, 0, 52, 15, 0, 17, 52, 0, 11),
  (2994, 0, 11, 43, 32, 15, 2, 12, 49, 21, 14),
  (2995, 0, 15, 51, 13, 13, 1, 42, 35, 2, 11),
  (2996, 0, 4, 54, 8, 12, 0, 16, 52, 6, 12),
  (2997, 0, 0, 54, 9, 12, 0, 9, 0, 54, 15),
  (2998, 0, 9, 54, 1, 11, 3, 30, 44, 12, 13),
  (2999, 1, 39, 30, 24, 14, 3, 1, 54, 8, 12)
  ]

lemma witChunk_55_ok : witChunk_55.all checkWit = true := by
  decide +kernel

lemma witChunk_55_ns :
    witChunk_55.map (fun t => t.1) = (List.range 50).map (· + 2950) := by
  decide +kernel

def witChunk_56 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3000, 3, 29, 46, 5, 12, 3, 41, 26, 25, 14),
  (3001, 0, 16, 48, 21, 14, 0, 42, 9, 34, 14),
  (3002, 0, 21, 40, 31, 15, 1, 52, 14, 10, 11),
  (3003, 0, 19, 41, 31, 15, 1, 20, 0, 51, 15),
  (3004, 1, 31, 40, 21, 14, 1, 41, 5, 36, 14),
  (3005, 0, 53, 14, 0, 9, 1, 53, 13, 5, 10),
  (3006, 3, 18, 42, 30, 15, 3, 34, 26, 34, 15),
  (3007, 1, 14, 53, 0, 11, 1, 34, 43, 0, 11),
  (3008, 1, 14, 43, 31, 15, 1, 26, 37, 31, 15),
  (3009, 0, 34, 37, 22, 14, 0, 37, 38, 14, 13),
  (3010, 2, 24, 49, 5, 12, 2, 35, 16, 39, 15),
  (3011, 0, 23, 39, 31, 15, 0, 31, 31, 33, 15),
  (3012, 3, 43, 11, 32, 14, 3, 43, 19, 28, 14),
  (3013, 0, 49, 24, 6, 11, 1, 13, 49, 21, 14),
  (3014, 0, 3, 43, 34, 15, 0, 17, 42, 31, 15),
  (3015, 1, 30, 33, 32, 15, 1, 32, 30, 33, 15),
  (3016, 1, 7, 54, 7, 12, 1, 13, 53, 6, 12),
  (3017, 2, 7, 44, 32, 15, 2, 20, 47, 20, 14),
  (3018, 0, 47, 5, 28, 13, 2, 29, 45, 12, 13),
  (3019, 1, 12, 52, 13, 13, 1, 43, 12, 32, 14),
  (3020, 2, 26, 44, 20, 14, 3, 28, 3, 47, 15),
  (3021, 0, 29, 34, 32, 15, 2, 36, 41, 6, 12),
  (3022, 0, 30, 41, 21, 14, 0, 33, 42, 13, 13),
  (3023, 3, 0, 43, 34, 15, 3, 16, 43, 30, 15),
  (3024, 0, 48, 24, 12, 12, 2, 42, 24, 26, 14),
  (3025, 0, 33, 44, 0, 11, 0, 45, 26, 18, 13),
  (3026, 0, 51, 19, 8, 11, 1, 8, 44, 32, 15),
  (3027, 1, 35, 42, 6, 12, 1, 51, 10, 18, 12),
  (3028, 1, 49, 25, 0, 10, 1, 51, 8, 19, 12),
  (3029, 0, 8, 54, 7, 12, 0, 33, 28, 34, 15),
  (3030, 0, 1, 2, 55, 15, 0, 23, 1, 50, 15),
  (3031, 1, 0, 2, 55, 15, 1, 22, 49, 12, 13),
  (3032, 1, 2, 1, 55, 15, 1, 55, 2, 1, 8),
  (3033, 2, 19, 42, 30, 15, 2, 42, 6, 35, 14),
  (3034, 0, 15, 53, 0, 11, 2, 20, 51, 5, 12),
  (3035, 0, 3, 1, 55, 15, 0, 15, 43, 31, 15),
  (3036, 1, 51, 12, 17, 12, 2, 18, 48, 20, 14),
  (3037, 0, 52, 18, 3, 10, 1, 41, 27, 25, 14),
  (3038, 0, 3, 55, 2, 11, 0, 14, 49, 21, 14),
  (3039, 1, 51, 6, 20, 12, 3, 4, 53, 14, 13),
  (3040, 1, 2, 53, 15, 13, 1, 3, 50, 23, 14),
  (3041, 0, 9, 44, 32, 15, 0, 14, 53, 6, 12),
  (3042, 0, 13, 52, 13, 13, 0, 21, 0, 51, 15),
  (3043, 0, 3, 53, 15, 13, 0, 39, 39, 1, 11),
  (3044, 1, 39, 0, 39, 14, 3, 0, 1, 55, 15),
  (3045, 0, 4, 50, 23, 14, 2, 11, 54, 0, 11),
  (3046, 0, 54, 9, 7, 10, 1, 20, 50, 12, 13),
  (3047, 1, 23, 46, 20, 14, 1, 40, 38, 1, 11),
  (3048, 0, 8, 50, 22, 14, 0, 40, 2, 38, 14),
  (3049, 2, 10, 50, 21, 14, 2, 30, 46, 5, 12)
  ]

lemma witChunk_56_ok : witChunk_56.all checkWit = true := by
  decide +kernel

lemma witChunk_56_ns :
    witChunk_56.map (fun t => t.1) = (List.range 50).map (· + 3000) := by
  decide +kernel

def witChunk_57 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3050, 0, 5, 0, 55, 15, 0, 5, 44, 33, 15),
  (3051, 2, 45, 27, 17, 13, 2, 53, 3, 15, 11),
  (3052, 1, 21, 47, 20, 14, 1, 25, 45, 20, 14),
  (3053, 0, 42, 35, 8, 12, 0, 53, 10, 12, 11),
  (3054, 0, 7, 53, 14, 13, 2, 25, 39, 30, 15),
  (3055, 1, 51, 14, 16, 12, 5, 20, 42, 29, 15),
  (3056, 1, 23, 50, 5, 12, 3, 47, 27, 10, 12),
  (3057, 0, 46, 29, 10, 12, 0, 50, 19, 14, 12),
  (3058, 0, 45, 32, 3, 11, 2, 35, 12, 41, 15),
  (3059, 0, 27, 37, 31, 15, 0, 47, 3, 29, 13),
  (3060, 1, 27, 48, 5, 12, 1, 51, 4, 21, 12),
  (3061, 1, 41, 3, 37, 14, 2, 18, 52, 5, 12),
  (3062, 0, 38, 33, 23, 14, 0, 41, 34, 15, 13),
  (3063, 5, 15, 22, 48, 16, 5, 36, 14, 39, 15),
  (3064, 1, 6, 55, 1, 11, 1, 11, 50, 21, 14),
  (3065, 0, 32, 40, 21, 14, 0, 42, 25, 26, 14),
  (3066, 0, 13, 44, 31, 15, 0, 29, 4, 47, 15),
  (3067, 1, 19, 48, 20, 14, 1, 22, 41, 30, 15),
  (3068, 3, 8, 45, 31, 15, 3, 11, 25, 48, 16),
  (3069, 0, 53, 2, 16, 11, 1, 21, 51, 5, 12),
  (3070, 4, 10, 27, 47, 16, 4, 14, 21, 49, 16),
  (3071, 1, 18, 51, 12, 13, 1, 30, 45, 12, 13),
  (3072, 2, 30, 42, 20, 14, 3, 13, 22, 49, 16),
  (3073, 0, 25, 48, 12, 13, 0, 54, 11, 6, 10),
  (3074, 0, 23, 49, 12, 13, 0, 31, 33, 32, 15),
  (3075, 0, 7, 55, 1, 11, 0, 35, 13, 41, 15),
  (3076, 0, 0, 50, 24, 14, 0, 36, 36, 22, 14),
  (3077, 1, 29, 47, 5, 12, 2, 50, 20, 13, 12),
  (3078, 0, 33, 30, 33, 15, 0, 43, 35, 2, 11),
  (3079, 3, 9, 26, 48, 16, 3, 42, 36, 1, 11),
  (3080, 1, 10, 53, 13, 13, 1, 26, 1, 49, 15),
  (3081, 2, 12, 25, 48, 16, 2, 15, 52, 12, 13),
  (3082, 0, 27, 47, 12, 13, 2, 5, 45, 32, 15),
  (3083, 0, 55, 7, 3, 9, 3, 4, 45, 32, 15),
  (3084, 1, 51, 16, 15, 12, 2, 14, 24, 48, 16),
  (3085, 0, 12, 50, 21, 14, 0, 13, 54, 0, 11),
  (3086, 0, 39, 37, 14, 13, 2, 31, 34, 31, 15),
  (3087, 1, 6, 45, 32, 15, 1, 32, 6, 45, 15),
  (3088, 1, 10, 45, 31, 15, 1, 30, 35, 31, 15),
  (3089, 0, 33, 8, 44, 15, 2, 14, 22, 49, 16),
  (3090, 2, 12, 27, 47, 16, 2, 33, 43, 12, 13),
  (3091, 0, 51, 21, 7, 11, 1, 51, 2, 22, 12),
  (3092, 0, 24, 46, 20, 14, 0, 44, 16, 30, 14),
  (3093, 0, 1, 44, 34, 15, 0, 2, 55, 8, 12),
  (3094, 1, 0, 44, 34, 15, 1, 16, 44, 30, 15),
  (3095, 1, 47, 28, 10, 12, 3, 17, 22, 48, 16),
  (3096, 0, 12, 54, 6, 12, 0, 36, 42, 6, 12),
  (3097, 2, 0, 55, 8, 12, 2, 16, 23, 48, 16),
  (3098, 0, 7, 45, 32, 15, 0, 29, 36, 31, 15),
  (3099, 0, 11, 53, 13, 13, 0, 47, 23, 19, 13)
  ]

lemma witChunk_57_ok : witChunk_57.all checkWit = true := by
  decide +kernel

lemma witChunk_57_ns :
    witChunk_57.map (fun t => t.1) = (List.range 50).map (· + 3050) := by
  decide +kernel

def witChunk_58 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3100, 1, 11, 24, 49, 16, 1, 13, 25, 48, 16),
  (3101, 0, 24, 50, 5, 12, 0, 26, 45, 20, 14),
  (3102, 0, 26, 49, 5, 12, 0, 31, 5, 46, 15),
  (3103, 1, 11, 26, 48, 16, 1, 43, 24, 26, 14),
  (3104, 0, 20, 48, 20, 14, 0, 44, 12, 32, 14),
  (3105, 0, 21, 42, 30, 15, 0, 53, 14, 10, 11),
  (3106, 0, 19, 51, 12, 13, 1, 16, 52, 12, 13),
  (3107, 0, 11, 45, 31, 15, 1, 11, 22, 50, 16),
  (3108, 0, 52, 20, 2, 10, 3, 17, 20, 49, 16),
  (3109, 1, 9, 25, 49, 16, 1, 13, 27, 47, 16),
  (3110, 0, 6, 55, 7, 12, 0, 19, 43, 30, 15),
  (3111, 5, 6, 55, 0, 11, 5, 15, 30, 44, 16),
  (3112, 1, 5, 51, 22, 14, 1, 9, 23, 50, 16),
  (3113, 0, 28, 48, 5, 12, 2, 32, 41, 20, 14),
  (3114, 2, 8, 21, 51, 16, 2, 8, 51, 21, 14),
  (3115, 2, 49, 9, 25, 13, 3, 9, 30, 46, 16),
  (3116, 1, 9, 27, 48, 16, 1, 11, 28, 47, 16),
  (3117, 2, 18, 24, 47, 16, 2, 42, 36, 7, 12),
  (3118, 0, 34, 39, 21, 14, 0, 42, 27, 25, 14),
  (3119, 3, 5, 24, 50, 16, 3, 18, 44, 29, 15),
  (3120, 0, 28, 44, 20, 14, 0, 44, 20, 28, 14),
  (3121, 0, 6, 51, 22, 14, 0, 12, 24, 49, 16),
  (3122, 2, 8, 29, 47, 16, 2, 52, 7, 19, 12),
  (3123, 0, 3, 45, 33, 15, 1, 14, 45, 30, 15),
  (3124, 0, 12, 26, 48, 16, 1, 11, 20, 51, 16),
  (3125, 0, 14, 25, 48, 16, 0, 17, 44, 30, 15),
  (3126, 0, 10, 25, 49, 16, 0, 14, 23, 49, 16),
  (3127, 1, 7, 24, 50, 16, 1, 10, 55, 0, 11),
  (3128, 0, 12, 22, 50, 16, 0, 52, 10, 18, 12),
  (3129, 0, 10, 23, 50, 16, 0, 20, 52, 5, 12),
  (3130, 0, 31, 45, 12, 13, 1, 4, 54, 14, 13),
  (3131, 0, 27, 1, 49, 15, 1, 55, 2, 10, 10),
  (3132, 1, 51, 0, 23, 12, 2, 6, 28, 48, 16),
  (3133, 0, 10, 27, 48, 16, 0, 37, 42, 0, 11),
  (3134, 0, 2, 51, 23, 14, 0, 14, 27, 47, 16),
  (3135, 3, 26, 40, 29, 15, 5, 3, 24, 50, 16),
  (3136, 0, 16, 24, 48, 16, 1, 7, 22, 51, 16),
  (3137, 0, 1, 0, 56, 15, 0, 5, 54, 14, 13),
  (3138, 0, 37, 20, 37, 15, 0, 37, 40, 13, 13),
  (3139, 1, 7, 28, 48, 16, 1, 11, 30, 46, 16),
  (3140, 0, 8, 24, 50, 16, 0, 52, 6, 20, 12),
  (3141, 0, 1, 56, 2, 11, 0, 8, 26, 49, 16),
  (3142, 0, 1, 54, 15, 13, 0, 10, 21, 51, 16),
  (3143, 1, 0, 54, 15, 13, 1, 8, 46, 31, 15),
  (3144, 1, 9, 55, 6, 12, 3, 7, 31, 46, 16),
  (3145, 0, 12, 20, 51, 16, 2, 11, 46, 30, 15),
  (3146, 0, 11, 55, 0, 11, 0, 37, 16, 39, 15),
  (3147, 0, 31, 35, 31, 15, 0, 55, 11, 1, 9),
  (3148, 1, 9, 19, 52, 16, 1, 19, 24, 47, 16),
  (3149, 0, 8, 22, 51, 16, 0, 29, 2, 48, 15)
  ]

lemma witChunk_58_ok : witChunk_58.all checkWit = true := by
  decide +kernel

lemma witChunk_58_ns :
    witChunk_58.map (fun t => t.1) = (List.range 50).map (· + 3100) := by
  decide +kernel

def witChunk_59 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3150, 0, 10, 29, 47, 16, 0, 15, 45, 30, 15),
  (3151, 1, 8, 54, 13, 13, 1, 11, 18, 52, 16),
  (3152, 0, 8, 28, 48, 16, 0, 56, 4, 0, 8),
  (3153, 0, 14, 29, 46, 16, 0, 38, 35, 22, 14),
  (3154, 2, 3, 56, 1, 11, 2, 4, 23, 51, 16),
  (3155, 0, 35, 9, 43, 15, 0, 35, 29, 33, 15),
  (3156, 0, 16, 20, 50, 16, 0, 16, 28, 46, 16),
  (3157, 0, 18, 23, 48, 16, 0, 54, 15, 4, 10),
  (3158, 0, 9, 46, 31, 15, 0, 14, 19, 51, 16),
  (3159, 1, 39, 40, 6, 12, 3, 2, 56, 1, 11),
  (3160, 0, 12, 30, 46, 16, 1, 7, 30, 47, 16),
  (3161, 0, 6, 25, 50, 16, 0, 10, 55, 6, 12),
  (3162, 0, 5, 56, 1, 11, 1, 12, 46, 30, 15),
  (3163, 0, 43, 33, 15, 13, 1, 39, 34, 22, 14),
  (3164, 1, 13, 17, 52, 16, 1, 19, 20, 49, 16),
  (3165, 0, 5, 46, 32, 15, 0, 10, 19, 52, 16),
  (3166, 0, 6, 23, 51, 16, 0, 6, 27, 49, 16),
  (3167, 1, 56, 2, 5, 9, 3, 18, 52, 11, 13),
  (3168, 0, 8, 20, 52, 16, 1, 15, 54, 5, 12),
  (3169, 0, 18, 27, 46, 16, 0, 33, 44, 12, 13),
  (3170, 0, 37, 24, 35, 15, 1, 56, 4, 4, 9),
  (3171, 1, 30, 37, 30, 15, 1, 36, 28, 33, 15),
  (3172, 0, 12, 18, 52, 16, 1, 5, 21, 52, 16),
  (3173, 0, 8, 30, 47, 16, 0, 41, 36, 14, 13),
  (3174, 1, 56, 0, 6, 9, 3, 46, 28, 16, 13),
  (3175, 1, 54, 1, 16, 11, 3, 48, 23, 18, 13),
  (3176, 1, 22, 43, 29, 15, 1, 38, 19, 37, 15),
  (3177, 0, 10, 31, 46, 16, 2, 6, 18, 53, 16),
  (3178, 0, 15, 53, 12, 13, 2, 27, 40, 29, 15),
  (3179, 0, 31, 3, 47, 15, 0, 47, 31, 3, 11),
  (3180, 1, 45, 33, 8, 12, 3, 17, 32, 43, 16),
  (3181, 0, 6, 21, 52, 16, 0, 6, 29, 48, 16),
  (3182, 0, 14, 31, 45, 16, 0, 42, 37, 7, 12),
  (3183, 1, 24, 42, 29, 15, 1, 38, 21, 36, 15),
  (3184, 1, 7, 18, 53, 16, 1, 21, 25, 46, 16),
  (3185, 0, 13, 46, 30, 15, 0, 18, 19, 50, 16),
  (3186, 2, 8, 33, 45, 16, 2, 12, 15, 53, 16),
  (3187, 1, 3, 26, 50, 16, 1, 15, 16, 52, 16),
  (3188, 0, 20, 22, 48, 16, 0, 32, 42, 20, 14),
  (3189, 0, 14, 17, 52, 16, 0, 52, 22, 1, 10),
  (3190, 0, 18, 29, 45, 16, 2, 15, 46, 29, 15),
  (3191, 1, 7, 32, 46, 16, 3, 8, 47, 30, 15),
  (3192, 0, 4, 26, 50, 16, 0, 20, 26, 46, 16),
  (3193, 0, 4, 24, 51, 16, 0, 12, 32, 45, 16),
  (3194, 0, 37, 12, 41, 15, 0, 55, 13, 0, 9),
  (3195, 2, 37, 27, 33, 15, 3, 1, 26, 50, 16),
  (3196, 1, 3, 28, 49, 16, 1, 3, 56, 7, 12),
  (3197, 0, 8, 18, 53, 16, 0, 14, 51, 20, 14),
  (3198, 0, 10, 17, 53, 16, 2, 9, 47, 30, 15),
  (3199, 1, 3, 22, 52, 16, 1, 3, 52, 22, 14)
  ]

lemma witChunk_59_ok : witChunk_59.all checkWit = true := by
  decide +kernel

lemma witChunk_59_ns :
    witChunk_59.map (fun t => t.1) = (List.range 50).map (· + 3150) := by
  decide +kernel

def witChunk_60 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3200, 0, 0, 56, 8, 12, 1, 26, 41, 29, 15),
  (3201, 0, 4, 28, 49, 16, 0, 4, 56, 7, 12),
  (3202, 0, 39, 41, 0, 11, 1, 8, 56, 0, 11),
  (3203, 2, 5, 47, 31, 15, 3, 9, 52, 20, 14),
  (3204, 0, 4, 22, 52, 16, 0, 4, 52, 22, 14),
  (3205, 1, 13, 15, 53, 16, 1, 21, 19, 49, 16),
  (3206, 0, 1, 46, 33, 15, 0, 6, 19, 53, 16),
  (3207, 1, 0, 46, 33, 15, 1, 30, 1, 48, 15),
  (3208, 1, 6, 47, 31, 15, 1, 22, 51, 11, 13),
  (3209, 0, 8, 52, 21, 14, 0, 12, 16, 53, 16),
  (3210, 0, 35, 7, 44, 15, 0, 35, 31, 32, 15),
  (3211, 0, 39, 39, 13, 13, 1, 10, 47, 30, 15),
  (3212, 2, 10, 52, 20, 14, 2, 22, 28, 44, 16),
  (3213, 2, 8, 15, 54, 16, 3, 11, 35, 43, 16),
  (3214, 0, 10, 33, 45, 16, 0, 18, 17, 51, 16),
  (3215, 1, 3, 30, 48, 16, 1, 11, 34, 44, 16),
  (3216, 0, 16, 16, 52, 16, 0, 16, 32, 44, 16),
  (3217, 0, 9, 56, 0, 11, 2, 22, 18, 49, 16),
  (3218, 0, 21, 44, 29, 15, 0, 35, 43, 12, 13),
  (3219, 0, 7, 47, 31, 15, 0, 23, 43, 29, 15),
  (3220, 0, 4, 30, 48, 16, 1, 3, 20, 53, 16),
  (3221, 0, 14, 33, 44, 16, 0, 18, 31, 44, 16),
  (3222, 0, 22, 23, 47, 16, 1, 32, 36, 30, 15),
  (3223, 1, 7, 16, 54, 16, 1, 7, 56, 6, 12),
  (3224, 0, 20, 18, 50, 16, 0, 52, 18, 14, 12),
  (3225, 0, 4, 20, 53, 16, 0, 22, 25, 46, 16),
  (3226, 1, 52, 22, 6, 11, 2, 12, 35, 43, 16),
  (3227, 0, 19, 45, 29, 15, 0, 47, 27, 17, 13),
  (3228, 2, 30, 48, 4, 12, 3, 1, 20, 53, 16),
  (3229, 0, 13, 54, 12, 13, 0, 22, 21, 48, 16),
  (3230, 0, 2, 25, 51, 16, 0, 3, 55, 14, 13),
  (3231, 1, 51, 22, 12, 12, 3, 34, 44, 11, 13),
  (3232, 1, 1, 27, 50, 16, 1, 5, 17, 54, 16),
  (3233, 0, 0, 52, 23, 14, 0, 2, 27, 50, 16),
  (3234, 2, 0, 25, 51, 16, 2, 20, 15, 51, 16),
  (3235, 1, 11, 14, 54, 16, 1, 23, 20, 48, 16),
  (3236, 0, 8, 16, 54, 16, 0, 8, 56, 6, 12),
  (3237, 0, 2, 23, 52, 16, 0, 34, 41, 20, 14),
  (3238, 0, 22, 27, 45, 16, 2, 39, 22, 35, 15),
  (3239, 1, 2, 47, 32, 15, 1, 32, 2, 47, 15),
  (3240, 0, 40, 34, 22, 14, 0, 56, 2, 10, 10),
  (3241, 0, 6, 17, 54, 16, 0, 6, 33, 46, 16),
  (3242, 0, 3, 47, 32, 15, 0, 29, 0, 49, 15),
  (3243, 0, 7, 55, 13, 13, 0, 55, 7, 13, 11),
  (3244, 1, 3, 32, 47, 16, 1, 9, 35, 44, 16),
  (3245, 0, 8, 34, 45, 16, 1, 1, 29, 49, 16),
  (3246, 0, 2, 29, 49, 16, 0, 14, 55, 5, 12),
  (3247, 1, 27, 50, 4, 12, 1, 50, 27, 4, 11),
  (3248, 0, 12, 52, 20, 14, 0, 44, 4, 36, 14),
  (3249, 0, 4, 32, 47, 16, 0, 56, 8, 7, 10)
  ]

lemma witChunk_60_ok : witChunk_60.all checkWit = true := by
  decide +kernel

lemma witChunk_60_ns :
    witChunk_60.map (fun t => t.1) = (List.range 50).map (· + 3200) := by
  decide +kernel

def witChunk_61 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3250, 0, 55, 9, 12, 11, 2, 0, 29, 49, 16),
  (3251, 0, 23, 51, 11, 13, 0, 27, 41, 29, 15),
  (3252, 2, 2, 18, 54, 16, 2, 18, 34, 42, 16),
  (3253, 0, 18, 15, 52, 16, 1, 1, 21, 53, 16),
  (3254, 0, 2, 21, 53, 16, 0, 38, 37, 21, 14),
  (3255, 3, 25, 26, 44, 16, 5, 6, 55, 12, 13),
  (3256, 0, 4, 18, 54, 16, 0, 12, 14, 54, 16),
  (3257, 0, 20, 16, 51, 16, 0, 36, 44, 5, 12),
  (3258, 0, 39, 21, 36, 15, 0, 53, 20, 7, 11),
  (3259, 0, 3, 57, 1, 11, 0, 55, 3, 15, 11),
  (3260, 1, 29, 49, 4, 12, 1, 31, 44, 19, 14),
  (3261, 0, 10, 35, 44, 16, 0, 16, 14, 53, 16),
  (3262, 0, 18, 33, 43, 16, 2, 49, 23, 18, 13),
  (3263, 1, 19, 14, 52, 16, 1, 32, 46, 11, 13),
  (3264, 1, 30, 39, 29, 15, 1, 38, 27, 33, 15),
  (3265, 2, 6, 14, 55, 16, 4, 0, 32, 47, 16),
  (3266, 0, 21, 52, 11, 13, 0, 29, 48, 11, 13),
  (3267, 0, 39, 15, 39, 15, 0, 55, 11, 11, 11),
  (3268, 0, 24, 24, 46, 16, 1, 1, 31, 48, 16),
  (3269, 0, 2, 31, 48, 16, 0, 24, 22, 47, 16),
  (3270, 0, 14, 35, 43, 16, 0, 43, 35, 14, 13),
  (3271, 1, 10, 55, 12, 13, 1, 38, 41, 12, 13),
  (3272, 0, 56, 10, 6, 10, 1, 7, 14, 55, 16),
  (3273, 0, 20, 32, 43, 16, 0, 22, 17, 50, 16),
  (3274, 0, 45, 32, 15, 13, 2, 4, 15, 55, 16),
  (3275, 0, 15, 47, 29, 15, 0, 35, 5, 45, 15),
  (3276, 2, 6, 36, 44, 16, 3, 7, 53, 20, 14),
  (3277, 0, 0, 26, 51, 16, 0, 24, 26, 45, 16),
  (3278, 0, 57, 2, 5, 9, 4, 10, 11, 55, 16),
  (3279, 3, 50, 20, 19, 13, 3, 53, 16, 14, 12),
  (3280, 0, 0, 24, 52, 16, 0, 24, 20, 48, 16),
  (3281, 0, 2, 19, 54, 16, 0, 14, 13, 54, 16),
  (3282, 0, 29, 40, 29, 15, 0, 37, 8, 43, 15),
  (3283, 1, 3, 34, 46, 16, 1, 4, 48, 31, 15),
  (3284, 0, 0, 28, 50, 16, 1, 11, 56, 5, 12),
  (3285, 0, 8, 14, 55, 16, 0, 9, 48, 30, 15),
  (3286, 0, 6, 15, 55, 16, 0, 6, 35, 45, 16),
  (3287, 1, 6, 57, 0, 11, 1, 15, 12, 54, 16),
  (3288, 0, 4, 34, 46, 16, 5, 22, 45, 27, 15),
  (3289, 0, 12, 36, 43, 16, 2, 22, 14, 51, 16),
  (3290, 0, 5, 48, 31, 15, 0, 11, 55, 12, 13),
  (3291, 0, 19, 53, 11, 13, 0, 31, 47, 11, 13),
  (3292, 1, 3, 16, 55, 16, 1, 9, 53, 20, 14),
  (3293, 0, 0, 22, 53, 16, 0, 26, 51, 4, 12),
  (3294, 0, 10, 13, 55, 16, 0, 22, 31, 43, 16),
  (3295, 1, 16, 54, 11, 13, 1, 19, 54, 4, 12),
  (3296, 0, 8, 36, 44, 16, 0, 24, 28, 44, 16),
  (3297, 0, 2, 53, 22, 14, 0, 4, 16, 55, 16),
  (3298, 0, 7, 57, 0, 11, 0, 51, 11, 24, 13),
  (3299, 0, 51, 13, 23, 13, 1, 47, 32, 8, 12)
  ]

lemma witChunk_61_ok : witChunk_61.all checkWit = true := by
  decide +kernel

lemma witChunk_61_ns :
    witChunk_61.map (fun t => t.1) = (List.range 50).map (· + 3250) := by
  decide +kernel

def witChunk_62 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3300, 0, 20, 14, 52, 16, 0, 28, 50, 4, 12),
  (3301, 0, 0, 30, 49, 16, 0, 24, 18, 49, 16),
  (3302, 0, 2, 33, 47, 16, 0, 2, 57, 7, 12),
  (3303, 3, 28, 49, 10, 13, 3, 36, 33, 30, 15),
  (3304, 1, 13, 37, 42, 16, 1, 34, 45, 11, 13),
  (3305, 0, 12, 56, 5, 12, 0, 56, 12, 5, 10),
  (3306, 0, 47, 29, 16, 13, 2, 0, 33, 47, 16),
  (3307, 0, 51, 9, 25, 13, 1, 47, 14, 30, 14),
  (3308, 1, 47, 16, 29, 14, 3, 12, 55, 11, 13),
  (3309, 0, 10, 53, 20, 14, 0, 22, 53, 4, 12),
  (3310, 0, 22, 15, 51, 16, 0, 49, 30, 3, 11),
  (3311, 1, 26, 43, 28, 15, 1, 32, 38, 29, 15),
  (3312, 1, 5, 57, 6, 12, 1, 39, 42, 5, 12),
  (3313, 0, 12, 12, 55, 16, 0, 18, 35, 42, 16),
  (3314, 0, 13, 48, 29, 15, 2, 16, 37, 41, 16),
  (3315, 4, 23, 45, 27, 15, 4, 39, 9, 41, 15),
  (3316, 0, 0, 20, 54, 16, 0, 16, 12, 54, 16),
  (3317, 0, 30, 49, 4, 12, 0, 57, 8, 2, 9),
  (3318, 0, 2, 17, 55, 16, 0, 10, 37, 43, 16),
  (3319, 1, 18, 47, 28, 15, 1, 23, 32, 42, 16),
  (3320, 0, 20, 34, 42, 16, 3, 53, 18, 13, 12),
  (3321, 0, 6, 57, 6, 12, 0, 16, 52, 19, 14),
  (3322, 0, 45, 36, 1, 11, 2, 0, 17, 55, 16),
  (3323, 0, 31, 39, 29, 15, 0, 39, 11, 41, 15),
  (3324, 2, 6, 12, 56, 16, 2, 54, 12, 16, 12),
  (3325, 0, 24, 30, 43, 16, 1, 49, 29, 9, 12),
  (3326, 0, 17, 54, 11, 13, 0, 26, 21, 47, 16),
  (3327, 3, 2, 56, 13, 13, 3, 20, 53, 10, 13),
  (3328, 0, 0, 32, 48, 16, 1, 17, 11, 54, 16),
  (3329, 0, 1, 48, 32, 15, 0, 14, 37, 42, 16),
  (3330, 0, 5, 56, 13, 13, 1, 0, 48, 32, 15),
  (3331, 0, 51, 17, 21, 13, 0, 55, 15, 9, 11),
  (3332, 0, 20, 54, 4, 12, 0, 24, 16, 50, 16),
  (3333, 0, 1, 56, 14, 13, 2, 2, 36, 45, 16),
  (3334, 1, 0, 56, 14, 13, 1, 28, 42, 28, 15),
  (3335, 1, 47, 10, 32, 14, 3, 4, 49, 30, 15),
  (3336, 3, 5, 38, 43, 16, 3, 55, 17, 2, 10),
  (3337, 0, 4, 36, 45, 16, 0, 22, 33, 42, 16),
  (3338, 0, 23, 45, 28, 15, 2, 20, 11, 53, 16),
  (3339, 0, 39, 27, 33, 15, 1, 6, 49, 30, 15),
  (3340, 1, 9, 11, 56, 16, 1, 19, 36, 41, 16),
  (3341, 0, 6, 13, 56, 16, 0, 6, 37, 44, 16),
  (3342, 0, 14, 11, 55, 16, 2, 47, 30, 15, 13),
  (3343, 1, 3, 14, 56, 16, 1, 27, 26, 44, 16),
  (3344, 0, 8, 12, 56, 16, 0, 32, 48, 4, 12),
  (3345, 0, 2, 35, 46, 16, 0, 25, 44, 28, 15),
  (3346, 0, 39, 41, 12, 13, 0, 51, 27, 4, 11),
  (3347, 2, 37, 43, 11, 13, 2, 41, 17, 37, 15),
  (3348, 0, 4, 14, 56, 16, 0, 56, 14, 4, 10),
  (3349, 0, 0, 18, 55, 16, 1, 21, 35, 41, 16)
  ]

lemma witChunk_62_ok : witChunk_62.all checkWit = true := by
  decide +kernel

lemma witChunk_62_ns :
    witChunk_62.map (fun t => t.1) = (List.range 50).map (· + 3300) := by
  decide +kernel

def witChunk_63 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3350, 0, 7, 49, 30, 15, 0, 35, 3, 46, 15),
  (3351, 3, 1, 14, 56, 16, 3, 17, 38, 40, 16),
  (3352, 0, 12, 38, 42, 16, 1, 15, 10, 55, 16),
  (3353, 0, 20, 12, 53, 16, 2, 28, 25, 44, 16),
  (3354, 0, 19, 47, 28, 15, 0, 37, 32, 31, 15),
  (3355, 0, 51, 5, 27, 13, 1, 23, 50, 18, 14),
  (3356, 2, 14, 56, 4, 12, 3, 11, 9, 56, 16),
  (3357, 0, 8, 38, 43, 16, 0, 10, 11, 56, 16),
  (3358, 0, 54, 21, 1, 10, 2, 21, 53, 10, 13),
  (3359, 1, 11, 10, 56, 16, 1, 27, 18, 48, 16),
  (3360, 2, 6, 54, 20, 14, 2, 18, 52, 18, 14),
  (3361, 0, 9, 56, 12, 13, 0, 18, 11, 54, 16),
  (3362, 0, 27, 43, 28, 15, 0, 51, 19, 20, 13),
  (3363, 0, 11, 49, 29, 15, 3, 52, 25, 4, 11),
  (3364, 0, 24, 32, 42, 16, 1, 1, 15, 56, 16),
  (3365, 0, 0, 34, 47, 16, 0, 2, 15, 56, 16),
  (3366, 0, 1, 58, 1, 11, 0, 14, 53, 19, 14),
  (3367, 1, 0, 58, 1, 11, 1, 7, 54, 20, 14),
  (3368, 1, 2, 49, 31, 15, 1, 3, 54, 21, 14),
  (3369, 2, 0, 15, 56, 16, 2, 2, 54, 21, 14),
  (3370, 0, 43, 39, 0, 11, 2, 16, 9, 55, 16),
  (3371, 0, 3, 49, 31, 15, 0, 15, 55, 11, 13),
  (3372, 3, 23, 11, 52, 16, 3, 23, 35, 40, 16),
  (3373, 0, 4, 54, 21, 14, 0, 24, 14, 51, 16),
  (3374, 0, 10, 57, 5, 12, 0, 18, 37, 41, 16),
  (3375, 3, 10, 56, 11, 13, 3, 18, 48, 27, 15),
  (3376, 1, 29, 47, 18, 14, 2, 18, 38, 40, 16),
  (3377, 0, 17, 48, 28, 15, 0, 20, 36, 41, 16),
  (3378, 0, 55, 17, 8, 11, 2, 48, 15, 29, 14),
  (3379, 1, 15, 56, 4, 12, 1, 19, 10, 54, 16),
  (3380, 0, 8, 54, 20, 14, 0, 12, 10, 56, 16),
  (3381, 0, 16, 10, 55, 16, 0, 16, 38, 41, 16),
  (3382, 1, 4, 58, 0, 11, 1, 24, 52, 10, 13),
  (3383, 1, 14, 49, 28, 15, 1, 40, 10, 41, 15),
  (3384, 0, 28, 22, 46, 16, 3, 21, 54, 3, 12),
  (3385, 0, 10, 39, 42, 16, 0, 28, 24, 45, 16),
  (3386, 0, 39, 29, 32, 15, 1, 28, 50, 10, 13),
  (3387, 0, 43, 37, 13, 13, 2, 21, 47, 27, 15),
  (3388, 1, 13, 9, 56, 16, 1, 27, 16, 49, 16),
  (3389, 0, 5, 58, 0, 11, 0, 29, 42, 28, 15),
  (3390, 0, 22, 35, 41, 16, 0, 41, 22, 35, 15),
  (3391, 1, 3, 38, 44, 16, 1, 19, 52, 18, 14),
  (3392, 0, 0, 16, 56, 16, 0, 48, 32, 8, 12),
  (3393, 0, 28, 20, 47, 16, 0, 33, 0, 48, 15),
  (3394, 0, 51, 3, 28, 13, 1, 56, 0, 16, 11),
  (3395, 0, 47, 31, 15, 13, 1, 22, 53, 10, 13),
  (3396, 0, 4, 38, 44, 16, 0, 28, 26, 44, 16),
  (3397, 1, 1, 37, 45, 16, 1, 5, 11, 57, 16),
  (3398, 0, 2, 37, 45, 16, 0, 14, 39, 41, 16),
  (3399, 3, 1, 38, 44, 16, 3, 16, 55, 10, 13)
  ]

lemma witChunk_63_ok : witChunk_63.all checkWit = true := by
  decide +kernel

lemma witChunk_63_ns :
    witChunk_63.map (fun t => t.1) = (List.range 50).map (· + 3350) := by
  decide +kernel

def witChunk_64 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3400, 0, 0, 54, 22, 14, 0, 24, 50, 18, 14),
  (3401, 0, 26, 15, 50, 16, 0, 26, 31, 42, 16),
  (3402, 2, 0, 37, 45, 16, 2, 8, 9, 57, 16),
  (3403, 0, 51, 21, 19, 13, 1, 12, 56, 11, 13),
  (3404, 1, 3, 12, 57, 16, 1, 11, 40, 41, 16),
  (3405, 2, 2, 12, 57, 16, 2, 20, 9, 54, 16),
  (3406, 0, 6, 11, 57, 16, 0, 6, 39, 43, 16),
  (3407, 1, 8, 50, 29, 15, 1, 19, 38, 40, 16),
  (3408, 0, 16, 56, 4, 12, 2, 6, 40, 42, 16),
  (3409, 0, 4, 12, 57, 16, 0, 22, 51, 18, 14),
  (3410, 0, 15, 49, 28, 15, 0, 37, 4, 45, 15),
  (3411, 1, 3, 58, 6, 12, 2, 37, 3, 45, 15),
  (3412, 0, 0, 36, 46, 16, 0, 28, 18, 48, 16),
  (3413, 0, 0, 58, 7, 12, 0, 8, 10, 57, 16),
  (3414, 0, 22, 11, 53, 16, 2, 39, 6, 43, 15),
  (3415, 1, 7, 40, 42, 16, 1, 55, 8, 18, 12),
  (3416, 0, 4, 58, 6, 12, 0, 20, 10, 54, 16),
  (3417, 0, 28, 28, 43, 16, 2, 3, 50, 30, 15),
  (3418, 1, 4, 50, 30, 15, 1, 20, 54, 10, 13),
  (3419, 0, 39, 7, 43, 15, 1, 58, 7, 2, 9),
  (3420, 2, 30, 24, 44, 16, 3, 11, 41, 40, 16),
  (3421, 0, 12, 54, 19, 14, 0, 36, 42, 19, 14),
  (3422, 0, 2, 13, 57, 16, 0, 9, 50, 29, 15),
  (3423, 1, 24, 46, 27, 15, 1, 42, 19, 36, 15),
  (3424, 0, 24, 12, 52, 16, 1, 2, 57, 13, 13),
  (3425, 0, 5, 50, 30, 15, 0, 12, 40, 41, 16),
  (3426, 0, 13, 56, 11, 13, 0, 31, 41, 28, 15),
  (3427, 0, 3, 57, 13, 13, 1, 15, 8, 56, 16),
  (3428, 0, 8, 40, 42, 16, 0, 20, 52, 18, 14),
  (3429, 0, 25, 52, 10, 13, 0, 49, 32, 2, 11),
  (3430, 0, 10, 9, 57, 16, 0, 18, 9, 55, 16),
  (3431, 1, 6, 57, 12, 13, 1, 42, 39, 12, 13),
  (3432, 1, 26, 45, 27, 15, 1, 42, 21, 35, 15),
  (3433, 0, 30, 47, 18, 14, 0, 48, 20, 27, 14),
  (3434, 2, 8, 41, 41, 16, 2, 28, 31, 41, 16),
  (3435, 0, 35, 1, 47, 15, 0, 35, 37, 29, 15),
  (3436, 1, 11, 8, 57, 16, 1, 13, 57, 4, 12),
  (3437, 2, 46, 28, 23, 14, 2, 47, 32, 14, 13),
  (3438, 0, 23, 53, 10, 13, 6, 17, 49, 26, 15),
  (3439, 3, 21, 8, 54, 16, 3, 36, 45, 10, 13),
  (3440, 1, 7, 58, 5, 12, 1, 21, 9, 54, 16),
  (3441, 0, 28, 16, 49, 16, 0, 29, 50, 10, 13),
  (3442, 0, 7, 57, 12, 13, 2, 20, 55, 3, 12),
  (3443, 0, 39, 31, 31, 15, 0, 51, 1, 29, 13),
  (3444, 0, 20, 38, 40, 16, 0, 40, 38, 20, 14),
  (3445, 0, 0, 14, 57, 16, 0, 18, 39, 40, 16),
  (3446, 0, 26, 13, 51, 16, 0, 26, 33, 41, 16),
  (3447, 3, 25, 10, 52, 16, 3, 42, 12, 39, 15),
  (3448, 0, 28, 30, 42, 16, 1, 29, 29, 42, 16),
  (3449, 2, 4, 55, 20, 14, 2, 16, 7, 56, 16)
  ]

lemma witChunk_64_ok : witChunk_64.all checkWit = true := by
  decide +kernel

lemma witChunk_64_ns :
    witChunk_64.map (fun t => t.1) = (List.range 50).map (· + 3400) := by
  decide +kernel

def witChunk_65 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3450, 2, 12, 7, 57, 16, 2, 20, 39, 39, 16),
  (3451, 0, 51, 29, 3, 11, 1, 18, 55, 10, 13),
  (3452, 1, 5, 55, 20, 14, 1, 13, 41, 40, 16),
  (3453, 0, 8, 58, 5, 12, 0, 13, 50, 28, 15),
  (3454, 0, 30, 23, 45, 16, 0, 51, 23, 18, 13),
  (3455, 5, 19, 40, 38, 16, 5, 43, 34, 20, 14),
  (3456, 0, 16, 8, 56, 16, 0, 16, 40, 40, 16),
  (3457, 0, 12, 8, 57, 16, 0, 18, 53, 18, 14),
  (3458, 1, 56, 16, 8, 11, 2, 8, 55, 19, 14),
  (3459, 2, 9, 57, 11, 13, 2, 57, 9, 11, 11),
  (3460, 1, 1, 39, 44, 16, 1, 3, 40, 43, 16),
  (3461, 0, 2, 39, 44, 16, 0, 6, 55, 20, 14),
  (3462, 0, 1, 50, 31, 15, 0, 10, 41, 41, 16),
  (3463, 1, 0, 50, 31, 15, 1, 34, 39, 28, 15),
  (3464, 0, 32, 46, 18, 14, 0, 48, 22, 26, 14),
  (3465, 0, 4, 40, 43, 16, 0, 58, 1, 10, 10),
  (3466, 2, 16, 41, 39, 16, 2, 48, 23, 25, 14),
  (3467, 0, 23, 47, 27, 15, 1, 15, 54, 18, 14),
  (3468, 1, 51, 28, 9, 12, 2, 30, 16, 48, 16),
  (3469, 0, 0, 38, 45, 16, 0, 45, 38, 0, 11),
  (3470, 0, 2, 55, 21, 14, 0, 25, 46, 27, 15),
  (3471, 3, 5, 8, 58, 16, 5, 6, 51, 28, 15),
  (3472, 0, 24, 36, 40, 16, 1, 5, 9, 58, 16),
  (3473, 0, 33, 40, 28, 15, 2, 26, 50, 17, 14),
  (3474, 0, 21, 48, 27, 15, 2, 0, 55, 21, 14),
  (3475, 1, 3, 10, 58, 16, 1, 31, 24, 44, 16),
  (3476, 1, 17, 7, 56, 16, 1, 27, 12, 51, 16),
  (3477, 0, 14, 41, 40, 16, 1, 21, 55, 3, 12),
  (3478, 0, 30, 27, 43, 16, 0, 57, 2, 15, 11),
  (3479, 1, 7, 8, 58, 16, 1, 31, 20, 46, 16),
  (3480, 0, 4, 10, 58, 16, 0, 28, 14, 50, 16),
  (3481, 0, 6, 9, 58, 16, 0, 6, 41, 42, 16),
  (3482, 0, 39, 5, 44, 15, 0, 53, 12, 23, 13),
  (3483, 0, 27, 45, 27, 15, 2, 53, 15, 21, 13),
  (3484, 1, 19, 40, 39, 16, 1, 39, 40, 19, 14),
  (3485, 0, 24, 10, 53, 16, 0, 38, 45, 4, 12),
  (3486, 0, 10, 55, 19, 14, 0, 19, 55, 10, 13),
  (3487, 1, 2, 59, 0, 11, 1, 10, 51, 28, 15),
  (3488, 1, 1, 11, 58, 16, 1, 31, 26, 43, 16),
  (3489, 0, 2, 11, 58, 16, 0, 20, 8, 55, 16),
  (3490, 0, 3, 59, 0, 11, 0, 45, 36, 13, 13),
  (3491, 0, 7, 51, 29, 15, 0, 11, 57, 11, 13),
  (3492, 0, 8, 8, 58, 16, 3, 12, 51, 27, 15),
  (3493, 0, 30, 17, 48, 16, 0, 33, 48, 10, 13),
  (3494, 0, 14, 7, 57, 16, 0, 26, 53, 3, 12),
  (3495, 3, 20, 49, 26, 15, 3, 49, 20, 26, 14),
  (3496, 0, 16, 54, 18, 14, 0, 48, 6, 34, 14),
  (3497, 0, 28, 52, 3, 12, 2, 32, 23, 44, 16),
  (3498, 0, 53, 8, 25, 13, 2, 32, 21, 45, 16),
  (3499, 1, 52, 28, 3, 11, 2, 49, 33, 1, 11)
  ]

lemma witChunk_65_ok : witChunk_65.all checkWit = true := by
  decide +kernel

lemma witChunk_65_ns :
    witChunk_65.map (fun t => t.1) = (List.range 50).map (· + 3450) := by
  decide +kernel

def witChunk_66 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3500, 3, 59, 1, 0, 8, 5, 17, 5, 56, 16),
  (3501, 0, 24, 54, 3, 12, 0, 26, 11, 52, 16),
  (3502, 0, 55, 21, 6, 11, 2, 37, 45, 10, 13),
  (3503, 1, 11, 58, 4, 12, 3, 21, 40, 38, 16),
  (3504, 2, 18, 6, 56, 16, 3, 19, 41, 38, 16),
  (3505, 0, 30, 29, 42, 16, 0, 34, 45, 18, 14),
  (3506, 0, 11, 51, 28, 15, 0, 29, 44, 27, 15),
  (3507, 0, 43, 17, 37, 15, 0, 59, 1, 5, 9),
  (3508, 0, 0, 12, 58, 16, 0, 12, 42, 40, 16),
  (3509, 0, 8, 42, 41, 16, 0, 18, 7, 56, 16),
  (3510, 0, 3, 51, 30, 15, 0, 30, 51, 3, 12),
  (3511, 1, 23, 8, 54, 16, 1, 31, 28, 42, 16),
  (3512, 1, 15, 6, 57, 16, 1, 15, 42, 39, 16),
  (3513, 0, 10, 7, 58, 16, 2, 47, 36, 0, 11),
  (3514, 0, 43, 39, 12, 13, 1, 36, 46, 10, 13),
  (3515, 0, 43, 21, 35, 15, 0, 51, 25, 17, 13),
  (3516, 3, 7, 43, 40, 16, 3, 25, 8, 53, 16),
  (3517, 1, 21, 7, 55, 16, 1, 25, 9, 53, 16),
  (3518, 0, 17, 50, 27, 15, 0, 22, 55, 3, 12),
  (3519, 1, 32, 42, 27, 15, 1, 42, 27, 32, 15),
  (3520, 1, 1, 59, 6, 12, 1, 13, 55, 18, 14),
  (3521, 0, 2, 59, 6, 12, 0, 20, 40, 39, 16),
  (3522, 2, 12, 43, 39, 16, 2, 16, 57, 3, 12),
  (3523, 1, 11, 6, 58, 16, 1, 31, 16, 48, 16),
  (3524, 0, 12, 58, 4, 12, 0, 56, 8, 18, 12),
  (3525, 0, 17, 56, 10, 13, 0, 50, 31, 8, 12),
  (3526, 0, 18, 41, 39, 16, 0, 22, 39, 39, 16),
  (3527, 3, 33, 22, 44, 16, 3, 42, 8, 41, 15),
  (3528, 1, 14, 51, 27, 15, 1, 42, 9, 41, 15),
  (3529, 0, 28, 12, 51, 16, 2, 27, 46, 26, 15),
  (3530, 0, 35, 39, 28, 15, 2, 4, 59, 5, 12),
  (3531, 2, 29, 51, 9, 13, 3, 25, 38, 38, 16),
  (3532, 1, 9, 43, 40, 16, 1, 29, 33, 40, 16),
  (3533, 0, 5, 58, 12, 13, 0, 32, 22, 45, 16),
  (3534, 0, 1, 58, 13, 13, 0, 2, 41, 43, 16),
  (3535, 1, 0, 58, 13, 13, 1, 19, 6, 56, 16),
  (3536, 0, 0, 40, 44, 16, 0, 32, 24, 44, 16),
  (3537, 0, 56, 20, 1, 10, 2, 18, 54, 17, 14),
  (3538, 2, 0, 41, 43, 16, 2, 16, 5, 57, 16),
  (3539, 0, 31, 43, 27, 15, 0, 43, 13, 39, 15),
  (3540, 0, 28, 34, 40, 16, 0, 32, 20, 46, 16),
  (3541, 0, 16, 6, 57, 16, 0, 16, 42, 39, 16),
  (3542, 0, 6, 59, 5, 12, 0, 30, 31, 41, 16),
  (3543, 1, 47, 36, 6, 12, 3, 50, 32, 1, 11),
  (3544, 0, 4, 42, 42, 16, 0, 12, 6, 58, 16),
  (3545, 0, 14, 55, 18, 14, 0, 20, 56, 3, 12),
  (3546, 2, 45, 37, 12, 13, 2, 48, 3, 35, 14),
  (3547, 1, 3, 56, 20, 14, 1, 14, 57, 10, 13),
  (3548, 1, 7, 56, 19, 14, 1, 27, 36, 39, 16),
  (3549, 0, 10, 43, 40, 16, 0, 32, 26, 43, 16)
  ]

lemma witChunk_66_ok : witChunk_66.all checkWit = true := by
  decide +kernel

lemma witChunk_66_ns :
    witChunk_66.map (fun t => t.1) = (List.range 50).map (· + 3500) := by
  decide +kernel

def witChunk_67 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3550, 2, 29, 45, 26, 15, 2, 31, 50, 9, 13),
  (3551, 1, 8, 58, 11, 13, 3, 10, 52, 27, 15),
  (3552, 0, 4, 56, 20, 14, 0, 40, 44, 4, 12),
  (3553, 2, 22, 6, 55, 16, 2, 56, 3, 20, 12),
  (3554, 0, 53, 4, 27, 13, 1, 8, 52, 28, 15),
  (3555, 0, 15, 51, 27, 15, 0, 39, 3, 45, 15),
  (3556, 0, 24, 8, 54, 16, 0, 36, 44, 18, 14),
  (3557, 0, 32, 18, 47, 16, 0, 56, 14, 15, 12),
  (3558, 0, 22, 7, 55, 16, 0, 49, 34, 1, 11),
  (3559, 1, 54, 25, 4, 11, 1, 58, 7, 12, 11),
  (3560, 1, 13, 5, 58, 16, 1, 31, 14, 49, 16),
  (3561, 0, 4, 8, 59, 16, 0, 8, 56, 19, 14),
  (3562, 2, 3, 52, 29, 15, 2, 11, 52, 27, 15),
  (3563, 0, 43, 25, 33, 15, 0, 59, 9, 1, 9),
  (3564, 3, 1, 8, 59, 16, 3, 7, 59, 4, 12),
  (3565, 1, 1, 9, 59, 16, 1, 17, 5, 57, 16),
  (3566, 0, 2, 9, 59, 16, 0, 6, 7, 59, 16),
  (3567, 1, 51, 30, 8, 12, 3, 2, 52, 29, 15),
  (3568, 1, 7, 6, 59, 16, 1, 19, 54, 17, 14),
  (3569, 0, 9, 52, 28, 15, 0, 24, 52, 17, 14),
  (3570, 0, 5, 52, 29, 15, 0, 43, 11, 40, 15),
  (3571, 1, 19, 42, 38, 16, 1, 28, 52, 9, 13),
  (3572, 0, 20, 6, 56, 16, 0, 32, 28, 42, 16),
  (3573, 0, 28, 50, 17, 14, 0, 50, 17, 28, 14),
  (3574, 0, 15, 57, 10, 13, 1, 56, 20, 6, 11),
  (3575, 1, 23, 40, 38, 16, 1, 24, 54, 9, 13),
  (3576, 3, 23, 55, 2, 12, 5, 3, 6, 59, 16),
  (3577, 0, 0, 56, 21, 14, 2, 14, 58, 3, 12),
  (3578, 0, 37, 0, 47, 15, 0, 47, 37, 0, 11),
  (3579, 0, 55, 23, 5, 11, 1, 12, 52, 27, 15),
  (3580, 1, 9, 59, 4, 12, 1, 11, 44, 39, 16),
  (3581, 0, 0, 10, 59, 16, 0, 8, 6, 59, 16),
  (3582, 0, 18, 57, 3, 12, 0, 22, 53, 17, 14),
  (3583, 1, 11, 56, 18, 14, 1, 59, 0, 10, 10),
  (3584, 0, 32, 16, 48, 16, 1, 17, 43, 38, 16),
  (3585, 0, 14, 5, 58, 16, 0, 37, 46, 10, 13),
  (3586, 0, 51, 27, 16, 13, 2, 19, 56, 9, 13),
  (3587, 0, 39, 35, 29, 15, 1, 7, 44, 40, 16),
  (3588, 0, 28, 10, 52, 16, 0, 56, 16, 14, 12),
  (3589, 0, 30, 33, 40, 16, 1, 9, 5, 59, 16),
  (3590, 0, 30, 49, 17, 14, 0, 50, 19, 27, 14),
  (3591, 3, 49, 4, 34, 14, 5, 54, 7, 24, 13),
  (3592, 1, 22, 55, 9, 13, 1, 23, 6, 55, 16),
  (3593, 2, 11, 58, 10, 13, 2, 32, 31, 40, 16),
  (3594, 3, 14, 52, 26, 15, 4, 59, 9, 0, 9),
  (3595, 1, 47, 30, 22, 14, 2, 57, 17, 7, 11),
  (3596, 2, 50, 8, 32, 14, 3, 9, 4, 59, 16),
  (3597, 0, 10, 59, 4, 12, 0, 37, 38, 28, 15),
  (3598, 0, 18, 5, 57, 16, 0, 58, 15, 3, 10),
  (3599, 1, 38, 37, 28, 15, 1, 40, 34, 29, 15)
  ]

lemma witChunk_67_ok : witChunk_67.all checkWit = true := by
  decide +kernel

lemma witChunk_67_ns :
    witChunk_67.map (fun t => t.1) = (List.range 50).map (· + 3550) := by
  decide +kernel

def witChunk_68 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3600, 0, 8, 44, 40, 16, 1, 15, 58, 3, 12),
  (3601, 0, 1, 60, 0, 11, 0, 12, 44, 39, 16),
  (3602, 0, 13, 52, 27, 15, 0, 43, 27, 32, 15),
  (3603, 0, 47, 35, 13, 13, 1, 18, 51, 26, 15),
  (3604, 0, 12, 56, 18, 14, 0, 48, 2, 36, 14),
  (3605, 0, 1, 52, 30, 15, 0, 20, 54, 17, 14),
  (3606, 0, 10, 5, 59, 16, 0, 23, 49, 26, 15),
  (3607, 1, 15, 4, 58, 16, 1, 15, 44, 38, 16),
  (3608, 0, 20, 42, 38, 16, 1, 59, 10, 5, 10),
  (3609, 0, 22, 41, 38, 16, 0, 36, 48, 3, 12),
  (3610, 1, 12, 58, 10, 13, 1, 52, 30, 2, 11),
  (3611, 0, 43, 9, 41, 15, 1, 39, 42, 18, 14),
  (3612, 3, 13, 56, 17, 14, 3, 17, 44, 37, 16),
  (3613, 0, 0, 42, 43, 16, 0, 45, 38, 12, 13),
  (3614, 0, 27, 47, 26, 15, 3, 34, 42, 26, 15),
  (3615, 3, 29, 50, 16, 14, 5, 30, 51, 8, 13),
  (3616, 1, 1, 43, 42, 16, 1, 58, 13, 9, 11),
  (3617, 0, 2, 43, 42, 16, 0, 18, 43, 38, 16),
  (3618, 2, 8, 45, 39, 16, 2, 35, 48, 9, 13),
  (3619, 0, 27, 53, 9, 13, 1, 20, 56, 9, 13),
  (3620, 0, 24, 40, 38, 16, 0, 56, 0, 22, 12),
  (3621, 0, 32, 14, 49, 16, 0, 34, 23, 44, 16),
  (3622, 0, 25, 54, 9, 13, 0, 30, 11, 51, 16),
  (3623, 3, 26, 48, 25, 15, 3, 41, 40, 18, 14),
  (3624, 1, 57, 7, 18, 12, 3, 49, 26, 23, 14),
  (3625, 2, 22, 42, 37, 16, 2, 55, 24, 4, 11),
  (3626, 0, 29, 52, 9, 13, 2, 5, 53, 28, 15),
  (3627, 1, 36, 40, 27, 15, 1, 42, 31, 30, 15),
  (3628, 1, 3, 44, 41, 16, 1, 19, 4, 57, 16),
  (3629, 0, 16, 58, 3, 12, 0, 42, 43, 4, 12),
  (3630, 0, 34, 25, 43, 16, 2, 45, 21, 34, 15),
  (3631, 1, 2, 59, 12, 13, 1, 6, 53, 28, 15),
  (3632, 0, 44, 36, 20, 14, 1, 35, 46, 17, 14),
  (3633, 0, 4, 44, 41, 16, 0, 13, 58, 10, 13),
  (3634, 0, 3, 59, 12, 13, 2, 1, 59, 12, 13),
  (3635, 0, 23, 55, 9, 13, 0, 35, 41, 27, 15),
  (3636, 0, 0, 60, 6, 12, 0, 16, 4, 58, 16),
  (3637, 0, 24, 6, 55, 16, 1, 5, 57, 19, 14),
  (3638, 0, 18, 55, 17, 14, 0, 19, 51, 26, 15),
  (3639, 5, 12, 58, 9, 13, 5, 23, 42, 36, 16),
  (3640, 1, 6, 59, 11, 13, 1, 10, 53, 27, 15),
  (3641, 0, 4, 60, 5, 12, 0, 12, 4, 59, 16),
  (3642, 0, 7, 53, 28, 15, 1, 60, 6, 2, 9),
  (3643, 0, 31, 51, 9, 13, 1, 51, 16, 28, 14),
  (3644, 2, 22, 4, 56, 16, 2, 26, 52, 16, 14),
  (3645, 0, 22, 5, 56, 16, 0, 45, 18, 36, 15),
  (3646, 0, 6, 57, 19, 14, 0, 10, 45, 39, 16),
  (3647, 1, 3, 6, 60, 16, 1, 35, 22, 44, 16),
  (3648, 0, 32, 32, 40, 16, 1, 39, 46, 3, 12),
  (3649, 0, 34, 27, 42, 16, 2, 4, 5, 60, 16)
  ]

lemma witChunk_68_ok : witChunk_68.all checkWit = true := by
  decide +kernel

lemma witChunk_68_ns :
    witChunk_68.map (fun t => t.1) = (List.range 50).map (· + 3600) := by
  decide +kernel

def witChunk_69 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3650, 0, 45, 16, 37, 15, 0, 45, 20, 35, 15),
  (3651, 0, 7, 59, 11, 13, 0, 43, 29, 31, 15),
  (3652, 0, 4, 6, 60, 16, 1, 1, 7, 60, 16),
  (3653, 0, 2, 7, 60, 16, 0, 2, 57, 20, 14),
  (3654, 0, 34, 17, 47, 16, 0, 34, 47, 17, 14),
  (3655, 1, 58, 15, 8, 11, 3, 1, 6, 60, 16),
  (3656, 1, 2, 53, 29, 15, 1, 9, 57, 18, 14),
  (3657, 0, 28, 8, 53, 16, 0, 58, 17, 2, 10),
  (3658, 0, 21, 56, 9, 13, 2, 16, 45, 37, 16),
  (3659, 0, 3, 53, 29, 15, 0, 11, 53, 27, 15),
  (3660, 1, 57, 3, 20, 12, 2, 6, 4, 60, 16),
  (3661, 0, 6, 5, 60, 16, 0, 6, 45, 40, 16),
  (3662, 0, 31, 45, 26, 15, 0, 38, 47, 3, 12),
  (3663, 3, 8, 59, 10, 13, 5, 60, 2, 3, 9),
  (3664, 0, 0, 8, 60, 16, 1, 17, 3, 58, 16),
  (3665, 0, 14, 45, 38, 16, 0, 20, 4, 57, 16),
  (3666, 0, 55, 25, 4, 11, 2, 20, 3, 57, 16),
  (3667, 0, 51, 29, 15, 13, 1, 7, 4, 60, 16),
  (3668, 0, 32, 12, 50, 16, 0, 52, 30, 8, 12),
  (3669, 0, 17, 52, 26, 15, 2, 59, 6, 12, 11),
  (3670, 0, 33, 50, 9, 13, 2, 9, 59, 10, 13),
  (3671, 1, 23, 56, 2, 12, 1, 31, 52, 2, 12),
  (3672, 0, 28, 38, 38, 16, 1, 57, 15, 14, 12),
  (3673, 0, 10, 57, 18, 14, 0, 48, 0, 37, 14),
  (3674, 0, 39, 37, 28, 15, 0, 53, 24, 17, 13),
  (3675, 0, 55, 11, 23, 13, 0, 59, 5, 13, 11),
  (3676, 1, 47, 32, 21, 14, 1, 51, 32, 7, 12),
  (3677, 1, 25, 5, 55, 16, 1, 25, 41, 37, 16),
  (3678, 0, 34, 29, 41, 16, 0, 41, 34, 29, 15),
  (3679, 1, 51, 20, 26, 14, 7, 13, 46, 36, 16),
  (3680, 0, 8, 4, 60, 16, 0, 8, 60, 4, 12),
  (3681, 0, 16, 56, 17, 14, 0, 50, 5, 34, 14),
  (3682, 0, 55, 9, 24, 13, 1, 40, 36, 28, 15),
  (3683, 0, 59, 9, 11, 11, 1, 10, 59, 10, 13),
  (3684, 3, 25, 4, 55, 16, 3, 35, 29, 40, 16),
  (3685, 0, 30, 9, 52, 16, 0, 34, 15, 48, 16),
  (3686, 0, 14, 3, 59, 16, 0, 14, 59, 3, 12),
  (3687, 3, 49, 28, 22, 14, 3, 58, 16, 7, 11),
  (3688, 0, 40, 42, 18, 14, 0, 48, 30, 22, 14),
  (3689, 2, 14, 2, 59, 16, 2, 14, 46, 37, 16),
  (3690, 0, 45, 12, 39, 15, 0, 45, 24, 33, 15),
  (3691, 0, 19, 57, 9, 13, 0, 51, 33, 1, 11),
  (3692, 1, 9, 3, 60, 16, 1, 25, 53, 16, 14),
  (3693, 1, 57, 1, 21, 12, 2, 36, 25, 42, 16),
  (3694, 2, 55, 6, 25, 13, 4, 45, 26, 31, 15),
  (3695, 3, 37, 48, 2, 12, 3, 44, 29, 30, 15),
  (3696, 1, 21, 57, 2, 12, 1, 33, 51, 2, 12),
  (3697, 0, 18, 3, 58, 16, 0, 49, 36, 0, 11),
  (3698, 0, 37, 40, 27, 15, 2, 19, 52, 25, 15),
  (3699, 0, 55, 7, 25, 13, 3, 6, 54, 27, 15)
  ]

lemma witChunk_69_ok : witChunk_69.all checkWit = true := by
  decide +kernel

lemma witChunk_69_ns :
    witChunk_69.map (fun t => t.1) = (List.range 50).map (· + 3650) := by
  decide +kernel

def witChunk_70 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3700, 0, 0, 44, 42, 16, 0, 60, 0, 10, 10),
  (3701, 0, 8, 46, 39, 16, 0, 32, 34, 39, 16),
  (3702, 0, 11, 59, 10, 13, 0, 22, 43, 37, 16),
  (3703, 1, 16, 58, 9, 13, 1, 23, 54, 16, 14),
  (3704, 0, 12, 46, 38, 16, 0, 28, 54, 2, 12),
  (3705, 0, 20, 44, 37, 16, 0, 26, 55, 2, 12),
  (3706, 2, 48, 37, 5, 12, 2, 56, 21, 11, 12),
  (3707, 0, 35, 49, 9, 13, 0, 59, 1, 15, 11),
  (3708, 3, 9, 60, 3, 12, 3, 16, 53, 25, 15),
  (3709, 0, 10, 3, 60, 16, 0, 24, 42, 37, 16),
  (3710, 0, 2, 45, 41, 16, 0, 15, 53, 26, 15),
  (3711, 1, 8, 54, 27, 15, 1, 42, 3, 44, 15),
  (3712, 1, 15, 2, 59, 16, 1, 15, 46, 37, 16),
  (3713, 0, 30, 37, 38, 16, 0, 30, 53, 2, 12),
  (3714, 0, 55, 17, 20, 13, 2, 0, 45, 41, 16),
  (3715, 1, 28, 48, 25, 15, 1, 42, 43, 10, 13),
  (3716, 0, 24, 56, 2, 12, 0, 36, 22, 44, 16),
  (3717, 0, 34, 31, 40, 16, 0, 41, 44, 10, 13),
  (3718, 0, 18, 45, 37, 16, 1, 4, 54, 28, 15),
  (3719, 1, 31, 50, 16, 14, 3, 17, 46, 36, 16),
  (3720, 3, 7, 47, 38, 16, 3, 37, 22, 43, 16),
  (3721, 0, 36, 20, 45, 16, 0, 36, 24, 43, 16),
  (3722, 0, 47, 37, 12, 13, 2, 25, 55, 8, 13),
  (3723, 0, 43, 5, 43, 15, 2, 45, 27, 31, 15),
  (3724, 1, 21, 55, 16, 14, 1, 45, 41, 4, 12),
  (3725, 0, 5, 54, 28, 15, 0, 32, 10, 51, 16),
  (3726, 0, 9, 54, 27, 15, 0, 26, 5, 55, 16),
  (3727, 1, 3, 46, 40, 16, 1, 11, 2, 60, 16),
  (3728, 0, 24, 4, 56, 16, 1, 49, 29, 22, 14),
  (3729, 2, 20, 45, 36, 16, 2, 24, 3, 56, 16),
  (3730, 1, 56, 24, 4, 11, 2, 12, 47, 37, 16),
  (3731, 0, 59, 13, 9, 11, 1, 19, 2, 58, 16),
  (3732, 0, 4, 46, 40, 16, 0, 32, 52, 2, 12),
  (3733, 1, 29, 39, 37, 16, 2, 28, 5, 54, 16),
  (3734, 0, 14, 57, 17, 14, 0, 17, 58, 9, 13),
  (3735, 3, 1, 46, 40, 16, 3, 34, 44, 25, 15),
  (3736, 0, 28, 6, 54, 16, 0, 36, 18, 46, 16),
  (3737, 0, 22, 57, 2, 12, 0, 58, 7, 18, 12),
  (3738, 1, 12, 54, 26, 15, 1, 36, 42, 26, 15),
  (3739, 1, 4, 60, 11, 13, 1, 7, 58, 18, 14),
  (3740, 2, 46, 40, 4, 12, 3, 11, 1, 60, 16),
  (3741, 0, 4, 58, 19, 14, 0, 16, 2, 59, 16),
  (3742, 0, 22, 3, 57, 16, 3, 58, 18, 6, 11),
  (3743, 1, 59, 16, 2, 10, 3, 2, 60, 11, 13),
  (3744, 0, 28, 52, 16, 14, 0, 52, 16, 28, 14),
  (3745, 0, 1, 60, 12, 13, 2, 22, 2, 57, 16),
  (3746, 0, 5, 60, 11, 13, 0, 45, 40, 11, 13),
  (3747, 0, 55, 19, 19, 13, 2, 33, 45, 25, 15),
  (3748, 0, 12, 2, 60, 16, 0, 24, 54, 16, 14),
  (3749, 1, 1, 5, 61, 16, 1, 1, 61, 5, 12)
  ]

lemma witChunk_70_ok : witChunk_70.all checkWit = true := by
  decide +kernel

lemma witChunk_70_ns :
    witChunk_70.map (fun t => t.1) = (List.range 50).map (· + 3700) := by
  decide +kernel

def witChunk_71 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3750, 0, 2, 5, 61, 16, 0, 2, 61, 5, 12),
  (3751, 5, 31, 6, 52, 16, 5, 31, 38, 36, 16),
  (3752, 0, 8, 58, 18, 14, 3, 9, 58, 17, 14),
  (3753, 0, 4, 4, 61, 16, 0, 10, 47, 38, 16),
  (3754, 0, 37, 48, 9, 13, 2, 0, 5, 61, 16),
  (3755, 0, 23, 51, 25, 15, 0, 27, 49, 25, 15),
  (3756, 1, 57, 19, 12, 12, 3, 1, 4, 61, 16),
  (3757, 0, 0, 6, 61, 16, 0, 30, 51, 16, 14),
  (3758, 0, 1, 54, 29, 15, 0, 30, 7, 53, 16),
  (3759, 1, 0, 54, 29, 15, 3, 37, 16, 46, 16),
  (3760, 0, 60, 12, 4, 10, 1, 14, 59, 9, 13),
  (3761, 0, 13, 54, 26, 15, 0, 34, 51, 2, 12),
  (3762, 2, 21, 57, 8, 13, 2, 33, 51, 8, 13),
  (3763, 0, 55, 3, 27, 13, 0, 55, 27, 3, 11),
  (3764, 0, 0, 58, 20, 14, 0, 32, 36, 38, 16),
  (3765, 0, 22, 55, 16, 14, 0, 52, 10, 31, 14),
  (3766, 0, 6, 3, 61, 16, 0, 6, 47, 39, 16),
  (3767, 1, 26, 55, 8, 13, 1, 32, 46, 25, 15),
  (3768, 0, 20, 2, 58, 16, 0, 20, 58, 2, 12),
  (3769, 0, 42, 41, 18, 14, 0, 48, 32, 21, 14),
  (3770, 0, 21, 52, 25, 15, 0, 29, 48, 25, 15),
  (3771, 0, 39, 39, 27, 15, 2, 53, 27, 15, 13),
  (3772, 1, 13, 1, 60, 16, 1, 25, 3, 56, 16),
  (3773, 0, 6, 61, 4, 12, 0, 48, 38, 5, 12),
  (3774, 0, 14, 47, 37, 16, 2, 15, 54, 25, 15),
  (3775, 1, 19, 46, 36, 16, 1, 30, 53, 8, 13),
  (3776, 1, 7, 2, 61, 16, 1, 11, 58, 17, 14),
  (3777, 0, 34, 11, 50, 16, 0, 52, 32, 7, 12),
  (3778, 1, 24, 56, 8, 13, 1, 56, 8, 24, 13),
  (3779, 0, 43, 33, 29, 15, 2, 53, 31, 1, 11),
  (3780, 0, 32, 50, 16, 14, 0, 52, 20, 26, 14),
  (3781, 0, 9, 60, 10, 13, 1, 37, 27, 41, 16),
  (3782, 1, 60, 6, 12, 11, 2, 47, 14, 37, 15),
  (3783, 3, 8, 55, 26, 15, 3, 25, 2, 56, 16),
  (3784, 1, 23, 2, 57, 16, 1, 29, 5, 54, 16),
  (3785, 0, 58, 15, 14, 12, 2, 32, 7, 52, 16),
  (3786, 0, 61, 8, 1, 9, 2, 36, 31, 39, 16),
  (3787, 0, 15, 59, 9, 13, 1, 35, 48, 16, 14),
  (3788, 2, 38, 20, 44, 16, 3, 4, 55, 27, 15),
  (3789, 0, 8, 2, 61, 16, 2, 44, 39, 18, 14),
  (3790, 0, 30, 39, 37, 16, 0, 55, 21, 18, 13),
  (3791, 1, 27, 42, 36, 16, 3, 5, 48, 38, 16),
  (3792, 0, 20, 56, 16, 14, 0, 32, 8, 52, 16),
  (3793, 4, 20, 56, 15, 14, 6, 36, 11, 48, 16),
  (3794, 0, 43, 3, 44, 15, 0, 47, 17, 36, 15),
  (3795, 0, 19, 53, 25, 15, 0, 31, 47, 25, 15),
  (3796, 0, 36, 14, 48, 16, 0, 36, 30, 40, 16),
  (3797, 0, 0, 46, 41, 16, 0, 12, 58, 17, 14),
  (3798, 0, 42, 45, 3, 12, 0, 43, 43, 10, 13),
  (3799, 1, 7, 48, 38, 16, 1, 16, 54, 25, 15)
  ]

lemma witChunk_71_ok : witChunk_71.all checkWit = true := by
  decide +kernel

lemma witChunk_71_ns :
    witChunk_71.map (fun t => t.1) = (List.range 50).map (· + 3750) := by
  decide +kernel

def witChunk_72 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3800, 0, 36, 50, 2, 12, 3, 21, 46, 35, 16),
  (3801, 2, 38, 18, 45, 16, 2, 48, 33, 20, 14),
  (3802, 1, 44, 42, 10, 13, 1, 52, 30, 14, 13),
  (3803, 0, 7, 55, 27, 15, 0, 47, 15, 37, 15),
  (3804, 2, 14, 0, 60, 16, 2, 14, 48, 36, 16),
  (3805, 0, 22, 45, 36, 16, 0, 58, 21, 0, 10),
  (3806, 0, 18, 1, 59, 16, 0, 47, 21, 34, 15),
  (3807, 3, 13, 58, 16, 14, 3, 42, 0, 45, 15),
  (3808, 0, 24, 44, 36, 16, 1, 21, 1, 58, 16),
  (3809, 0, 18, 59, 2, 12, 0, 37, 42, 26, 15),
  (3810, 0, 55, 1, 28, 13, 2, 11, 60, 9, 13),
  (3811, 0, 39, 47, 9, 13, 3, 45, 38, 18, 14),
  (3812, 0, 8, 48, 38, 16, 0, 20, 46, 36, 16),
  (3813, 0, 2, 47, 40, 16, 0, 34, 49, 16, 14),
  (3814, 2, 45, 41, 10, 13, 4, 34, 49, 15, 14),
  (3815, 1, 2, 55, 28, 15, 3, 40, 39, 26, 15),
  (3816, 3, 45, 42, 3, 12, 5, 29, 3, 54, 16),
  (3817, 0, 12, 48, 37, 16, 2, 0, 47, 40, 16),
  (3818, 0, 3, 55, 28, 15, 0, 27, 55, 8, 13),
  (3819, 0, 59, 17, 7, 11, 3, 16, 59, 8, 13),
  (3820, 1, 29, 41, 36, 16, 1, 53, 15, 28, 14),
  (3821, 0, 26, 3, 56, 16, 0, 26, 43, 36, 16),
  (3822, 0, 10, 1, 61, 16, 0, 11, 55, 26, 15),
  (3823, 1, 34, 51, 8, 13, 1, 56, 18, 19, 13),
  (3824, 2, 14, 58, 16, 14, 2, 26, 2, 56, 16),
  (3825, 0, 25, 56, 8, 13, 0, 28, 4, 55, 16),
  (3826, 0, 51, 35, 0, 11, 2, 28, 3, 55, 16),
  (3827, 0, 47, 23, 33, 15, 1, 12, 60, 9, 13),
  (3828, 3, 61, 8, 5, 10, 5, 9, 49, 36, 16),
  (3829, 0, 18, 47, 36, 16, 0, 18, 57, 16, 14),
  (3830, 0, 10, 61, 3, 12, 0, 17, 54, 25, 15),
  (3831, 1, 15, 60, 2, 12, 1, 39, 48, 2, 12),
  (3832, 1, 5, 59, 18, 14, 1, 51, 2, 35, 14),
  (3833, 0, 38, 25, 42, 16, 2, 22, 46, 35, 16),
  (3834, 0, 31, 53, 8, 13, 0, 53, 32, 1, 11),
  (3835, 2, 45, 31, 29, 15, 3, 37, 12, 48, 16),
  (3836, 1, 3, 48, 39, 16, 1, 37, 47, 16, 14),
  (3837, 0, 32, 38, 37, 16, 2, 2, 48, 39, 16),
  (3838, 0, 34, 9, 51, 16, 2, 47, 10, 39, 15),
  (3839, 1, 59, 10, 16, 12, 3, 48, 19, 34, 15),
  (3840, 2, 30, 4, 54, 16, 2, 58, 18, 12, 12),
  (3841, 0, 4, 48, 39, 16, 0, 6, 59, 18, 14),
  (3842, 0, 23, 57, 8, 13, 2, 8, 49, 37, 16),
  (3843, 0, 55, 23, 17, 13, 1, 59, 6, 18, 12),
  (3844, 0, 28, 42, 36, 16, 1, 11, 0, 61, 16),
  (3845, 0, 62, 1, 0, 8, 1, 1, 59, 19, 14),
  (3846, 0, 2, 59, 19, 14, 0, 46, 37, 19, 14),
  (3847, 1, 15, 58, 16, 14, 3, 33, 6, 52, 16),
  (3848, 1, 2, 61, 11, 13, 1, 14, 55, 25, 15),
  (3849, 0, 22, 1, 58, 16, 0, 38, 17, 46, 16)
  ]

lemma witChunk_72_ok : witChunk_72.all checkWit = true := by
  decide +kernel

lemma witChunk_72_ns :
    witChunk_72.map (fun t => t.1) = (List.range 50).map (· + 3800) := by
  decide +kernel

def witChunk_73 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3850, 0, 13, 60, 9, 13, 2, 0, 59, 19, 14),
  (3851, 0, 3, 61, 11, 13, 0, 47, 11, 39, 15),
  (3852, 1, 59, 12, 15, 12, 2, 62, 0, 0, 8),
  (3853, 1, 9, 49, 37, 16, 1, 9, 59, 17, 14),
  (3854, 0, 38, 27, 41, 16, 0, 41, 38, 27, 15),
  (3855, 1, 26, 51, 24, 15, 1, 48, 18, 35, 15),
  (3856, 0, 16, 0, 60, 16, 0, 16, 48, 36, 16),
  (3857, 0, 2, 3, 62, 16, 0, 33, 52, 8, 13),
  (3858, 0, 43, 35, 28, 15, 0, 47, 25, 32, 15),
  (3859, 0, 51, 33, 13, 13, 1, 3, 2, 62, 16),
  (3860, 0, 0, 4, 62, 16, 0, 16, 60, 2, 12),
  (3861, 2, 0, 3, 62, 16, 2, 18, 48, 35, 16),
  (3862, 1, 28, 50, 24, 15, 1, 36, 50, 8, 13),
  (3863, 1, 39, 24, 42, 16, 1, 62, 1, 4, 9),
  (3864, 0, 4, 2, 62, 16, 1, 42, 37, 27, 15),
  (3865, 0, 12, 0, 61, 16, 2, 55, 24, 16, 13),
  (3866, 2, 28, 43, 35, 16, 2, 32, 5, 53, 16),
  (3867, 2, 57, 9, 23, 13, 2, 57, 13, 21, 13),
  (3868, 1, 13, 49, 36, 16, 1, 27, 56, 1, 12),
  (3869, 0, 0, 62, 5, 12, 0, 21, 58, 8, 13),
  (3870, 0, 7, 61, 10, 13, 0, 10, 49, 37, 16),
  (3871, 1, 3, 62, 4, 12, 1, 18, 59, 8, 13),
  (3872, 1, 5, 1, 62, 16, 1, 5, 49, 38, 16),
  (3873, 2, 38, 30, 39, 16, 2, 54, 30, 7, 12),
  (3874, 2, 43, 44, 9, 13, 4, 9, 56, 25, 15),
  (3875, 0, 15, 55, 25, 15, 0, 35, 45, 25, 15),
  (3876, 0, 4, 62, 4, 12, 0, 16, 58, 16, 14),
  (3877, 0, 30, 41, 36, 16, 0, 57, 12, 22, 13),
  (3878, 0, 38, 15, 47, 16, 0, 39, 41, 26, 15),
  (3879, 1, 30, 49, 24, 15, 1, 48, 22, 33, 15),
  (3880, 1, 31, 54, 1, 12, 1, 39, 26, 41, 16),
  (3881, 0, 6, 1, 62, 16, 0, 6, 49, 38, 16),
  (3882, 2, 3, 56, 27, 15, 2, 20, 57, 15, 14),
  (3883, 1, 4, 56, 27, 15, 1, 59, 20, 0, 10),
  (3884, 1, 53, 7, 32, 14, 3, 8, 61, 9, 13),
  (3885, 0, 38, 29, 40, 16, 1, 45, 43, 3, 12),
  (3886, 0, 57, 14, 21, 13, 2, 41, 39, 26, 15),
  (3887, 1, 59, 2, 20, 12, 3, 2, 56, 27, 15),
  (3888, 2, 6, 0, 62, 16, 3, 29, 2, 55, 16),
  (3889, 0, 45, 42, 10, 13, 0, 57, 8, 24, 13),
  (3890, 0, 5, 56, 27, 15, 0, 35, 51, 8, 13),
  (3891, 2, 9, 61, 9, 13, 2, 45, 3, 43, 15),
  (3892, 1, 19, 48, 35, 16, 1, 23, 56, 15, 14),
  (3893, 0, 9, 56, 26, 15, 0, 14, 49, 36, 16),
  (3894, 0, 34, 37, 37, 16, 0, 50, 37, 5, 12),
  (3895, 1, 7, 0, 62, 16, 1, 23, 0, 58, 16),
  (3896, 0, 36, 10, 50, 16, 0, 36, 34, 38, 16),
  (3897, 2, 6, 62, 3, 12, 2, 15, 60, 8, 13),
  (3898, 2, 17, 55, 24, 15, 2, 36, 35, 37, 16),
  (3899, 0, 47, 27, 31, 15, 1, 46, 41, 10, 13)
  ]

lemma witChunk_73_ok : witChunk_73.all checkWit = true := by
  decide +kernel

lemma witChunk_73_ns :
    witChunk_73.map (fun t => t.1) = (List.range 50).map (· + 3850) := by
  decide +kernel

def witChunk_74 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3900, 2, 38, 12, 48, 16, 3, 32, 53, 7, 13),
  (3901, 0, 61, 6, 12, 11, 1, 33, 53, 1, 12),
  (3902, 0, 42, 43, 17, 14, 0, 50, 31, 21, 14),
  (3903, 5, 3, 0, 62, 16, 5, 12, 30, 53, 17),
  (3904, 0, 0, 48, 40, 16, 1, 7, 62, 3, 12),
  (3905, 0, 25, 52, 24, 15, 0, 53, 30, 14, 13),
  (3906, 0, 19, 59, 8, 13, 0, 27, 51, 24, 15),
  (3907, 1, 12, 56, 25, 15, 1, 39, 28, 40, 16),
  (3908, 0, 8, 0, 62, 16, 0, 40, 48, 2, 12),
  (3909, 0, 34, 7, 52, 16, 0, 38, 47, 16, 14),
  (3910, 0, 57, 6, 25, 13, 2, 61, 9, 10, 11),
  (3911, 1, 38, 49, 8, 13, 1, 56, 22, 17, 13),
  (3912, 3, 5, 50, 37, 16, 3, 13, 50, 35, 16),
  (3913, 2, 6, 50, 37, 16, 4, 13, 24, 56, 17),
  (3914, 0, 23, 53, 24, 15, 2, 40, 25, 41, 16),
  (3915, 3, 14, 26, 55, 17, 3, 22, 58, 7, 13),
  (3916, 1, 53, 23, 24, 14, 3, 12, 27, 55, 17),
  (3917, 0, 8, 62, 3, 12, 0, 24, 46, 35, 16),
  (3918, 0, 22, 47, 35, 16, 0, 62, 5, 7, 10),
  (3919, 1, 11, 50, 36, 16, 3, 12, 29, 54, 17),
  (3920, 0, 32, 40, 36, 16, 0, 48, 40, 4, 12),
  (3921, 0, 1, 56, 28, 15, 0, 14, 61, 2, 12),
  (3922, 1, 0, 56, 28, 15, 1, 16, 60, 8, 13),
  (3923, 0, 11, 61, 9, 13, 2, 29, 55, 7, 13),
  (3924, 0, 28, 2, 56, 16, 1, 51, 36, 5, 12),
  (3925, 0, 28, 54, 15, 14, 0, 54, 15, 28, 14),
  (3926, 0, 2, 49, 39, 16, 0, 26, 1, 57, 16),
  (3927, 1, 18, 55, 24, 15, 1, 48, 10, 39, 15),
  (3928, 1, 39, 14, 47, 16, 3, 27, 45, 34, 16),
  (3929, 0, 20, 48, 35, 16, 0, 62, 7, 6, 10),
  (3930, 0, 13, 56, 25, 15, 0, 37, 44, 25, 15),
  (3931, 2, 13, 27, 55, 17, 2, 25, 57, 7, 13),
  (3932, 1, 35, 52, 1, 12, 2, 50, 32, 20, 14),
  (3933, 0, 8, 50, 37, 16, 0, 14, 59, 16, 14),
  (3934, 0, 30, 3, 55, 16, 0, 30, 53, 15, 14),
  (3935, 1, 3, 60, 18, 14, 3, 18, 28, 53, 17),
  (3936, 0, 40, 20, 44, 16, 1, 53, 33, 6, 12),
  (3937, 0, 24, 56, 15, 14, 0, 54, 11, 30, 14),
  (3938, 0, 31, 49, 24, 15, 2, 11, 28, 55, 17),
  (3939, 0, 47, 7, 41, 15, 2, 49, 21, 33, 15),
  (3940, 0, 4, 60, 18, 14, 0, 12, 50, 36, 16),
  (3941, 0, 24, 58, 1, 12, 0, 32, 54, 1, 12),
  (3942, 2, 15, 30, 53, 17, 2, 17, 27, 54, 17),
  (3943, 1, 34, 47, 24, 15, 1, 48, 26, 31, 15),
  (3944, 1, 39, 30, 39, 16, 1, 51, 30, 21, 14),
  (3945, 0, 28, 44, 35, 16, 2, 11, 30, 54, 17),
  (3946, 0, 61, 0, 15, 11, 0, 61, 12, 9, 11),
  (3947, 0, 43, 37, 27, 15, 0, 59, 21, 5, 11),
  (3948, 3, 8, 29, 55, 17, 3, 20, 59, 7, 13),
  (3949, 0, 40, 18, 45, 16, 2, 24, 47, 34, 16)
  ]

lemma witChunk_74_ok : witChunk_74.all checkWit = true := by
  decide +kernel

lemma witChunk_74_ns :
    witChunk_74.map (fun t => t.1) = (List.range 50).map (· + 3900) := by
  decide +kernel

def witChunk_75 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3950, 0, 18, 49, 35, 16, 0, 47, 29, 30, 15),
  (3951, 1, 59, 18, 12, 12, 3, 10, 32, 53, 17),
  (3952, 1, 14, 27, 55, 17, 1, 15, 50, 35, 16),
  (3953, 0, 8, 60, 17, 14, 0, 17, 60, 8, 13),
  (3954, 2, 9, 27, 56, 17, 2, 11, 24, 57, 17),
  (3955, 0, 43, 45, 9, 13, 1, 3, 50, 38, 16),
  (3956, 0, 32, 4, 54, 16, 0, 60, 10, 16, 12),
  (3957, 0, 40, 26, 41, 16, 0, 41, 40, 26, 15),
  (3958, 0, 22, 57, 15, 14, 0, 54, 9, 31, 14),
  (3959, 1, 14, 25, 56, 17, 1, 16, 26, 55, 17),
  (3960, 0, 4, 50, 38, 16, 0, 60, 6, 18, 12),
  (3961, 0, 0, 60, 19, 14, 0, 36, 8, 51, 16),
  (3962, 0, 19, 55, 24, 15, 1, 4, 62, 10, 13),
  (3963, 1, 6, 57, 26, 15, 1, 42, 39, 26, 15),
  (3964, 1, 19, 60, 1, 12, 1, 41, 45, 16, 14),
  (3965, 0, 45, 2, 44, 15, 0, 45, 34, 28, 15),
  (3966, 0, 1, 62, 11, 13, 0, 22, 59, 1, 12),
  (3967, 1, 0, 62, 11, 13, 1, 10, 27, 56, 17),
  (3968, 1, 10, 29, 55, 17, 1, 14, 31, 53, 17),
  (3969, 0, 5, 62, 10, 13, 0, 33, 48, 24, 15),
  (3970, 0, 51, 35, 12, 13, 1, 16, 24, 56, 17),
  (3971, 1, 11, 62, 2, 12, 1, 12, 24, 57, 17),
  (3972, 0, 40, 16, 46, 16, 0, 40, 46, 16, 14),
  (3973, 0, 0, 2, 63, 16, 0, 34, 39, 36, 16),
  (3974, 0, 2, 1, 63, 16, 0, 7, 57, 26, 15),
  (3975, 3, 8, 23, 58, 17, 3, 25, 56, 14, 14),
  (3976, 1, 10, 25, 57, 17, 1, 10, 57, 25, 15),
  (3977, 0, 38, 33, 38, 16, 0, 42, 47, 2, 12),
  (3978, 0, 13, 28, 55, 17, 2, 0, 1, 63, 16),
  (3979, 0, 15, 27, 55, 17, 0, 55, 27, 15, 13),
  (3980, 1, 3, 0, 63, 16, 1, 9, 51, 36, 16),
  (3981, 0, 13, 26, 56, 17, 0, 16, 50, 35, 16),
  (3982, 0, 15, 29, 54, 17, 0, 34, 51, 15, 14),
  (3983, 1, 14, 61, 8, 13, 3, 45, 44, 2, 12),
  (3984, 0, 40, 28, 40, 16, 0, 56, 28, 8, 12),
  (3985, 0, 4, 0, 63, 16, 0, 13, 30, 54, 17),
  (3986, 0, 11, 27, 56, 17, 0, 15, 25, 56, 17),
  (3987, 0, 3, 57, 27, 15, 0, 11, 29, 55, 17),
  (3988, 1, 1, 63, 4, 12, 2, 18, 50, 34, 16),
  (3989, 0, 2, 63, 4, 12, 0, 17, 28, 54, 17),
  (3990, 0, 17, 26, 55, 17, 0, 34, 5, 53, 16),
  (3991, 1, 8, 26, 57, 17, 1, 8, 30, 55, 17),
  (3992, 0, 12, 62, 2, 12, 0, 60, 14, 14, 12),
  (3993, 0, 58, 23, 10, 12, 2, 0, 63, 4, 12),
  (3994, 0, 13, 24, 57, 17, 1, 12, 22, 58, 17),
  (3995, 0, 11, 25, 57, 17, 0, 11, 57, 25, 15),
  (3996, 3, 0, 57, 27, 15, 3, 27, 57, 0, 12),
  (3997, 0, 10, 51, 36, 16, 1, 5, 51, 37, 16),
  (3998, 0, 11, 31, 54, 17, 0, 17, 30, 53, 17),
  (3999, 3, 10, 20, 59, 17, 3, 16, 19, 58, 17)
  ]

lemma witChunk_75_ok : witChunk_75.all checkWit = true := by
  decide +kernel

lemma witChunk_75_ns :
    witChunk_75.map (fun t => t.1) = (List.range 50).map (· + 3950) := by
  decide +kernel

def witChunk_76 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4000, 0, 12, 60, 16, 14, 0, 52, 0, 36, 14),
  (4001, 0, 9, 28, 56, 17, 0, 17, 24, 56, 17),
  (4002, 0, 13, 32, 53, 17, 0, 53, 32, 13, 13),
  (4003, 0, 15, 23, 57, 17, 1, 14, 21, 58, 17),
  (4004, 0, 60, 2, 20, 12, 1, 59, 20, 11, 12),
  (4005, 0, 40, 14, 47, 16, 1, 5, 63, 3, 12),
  (4006, 0, 6, 51, 37, 16, 0, 9, 26, 57, 17),
  (4007, 1, 54, 33, 0, 11, 1, 55, 14, 28, 14),
  (4008, 3, 53, 34, 5, 12, 3, 55, 17, 26, 14),
  (4009, 2, 60, 1, 20, 12, 4, 17, 18, 58, 17),
  (4010, 0, 15, 61, 8, 13, 0, 35, 47, 24, 15),
  (4011, 0, 19, 25, 55, 17, 0, 19, 29, 53, 17),
  (4012, 1, 41, 27, 40, 16, 1, 55, 12, 29, 14),
  (4013, 0, 32, 42, 35, 16, 1, 17, 61, 1, 12),
  (4014, 0, 6, 63, 3, 12, 0, 11, 23, 58, 17),
  (4015, 1, 6, 29, 56, 17, 1, 16, 34, 51, 17),
  (4016, 1, 6, 27, 57, 17, 1, 18, 21, 57, 17),
  (4017, 0, 13, 22, 58, 17, 0, 17, 32, 52, 17),
  (4018, 0, 15, 33, 52, 17, 2, 9, 35, 52, 17),
  (4019, 0, 11, 33, 53, 17, 0, 63, 7, 1, 9),
  (4020, 2, 30, 54, 14, 14, 2, 42, 22, 42, 16),
  (4021, 0, 0, 50, 39, 16, 0, 9, 24, 58, 17),
  (4022, 0, 14, 51, 35, 16, 0, 17, 22, 57, 17),
  (4023, 1, 14, 57, 24, 15, 1, 24, 54, 23, 15),
  (4024, 1, 6, 31, 55, 17, 1, 10, 21, 59, 17),
  (4025, 0, 38, 9, 50, 16, 0, 52, 36, 5, 12),
  (4026, 0, 7, 29, 56, 17, 0, 19, 23, 56, 17),
  (4027, 0, 7, 27, 57, 17, 0, 27, 57, 7, 13),
  (4028, 3, 9, 52, 35, 16, 3, 20, 19, 57, 17),
  (4029, 0, 13, 34, 52, 17, 2, 14, 60, 15, 14),
  (4030, 0, 15, 21, 58, 17, 0, 18, 59, 15, 14),
  (4031, 1, 8, 22, 59, 17, 1, 8, 34, 53, 17),
  (4032, 1, 30, 51, 23, 15, 1, 50, 21, 33, 15),
  (4033, 0, 21, 26, 54, 17, 0, 28, 0, 57, 16),
  (4034, 0, 21, 28, 53, 17, 2, 4, 61, 17, 14),
  (4035, 0, 7, 31, 55, 17, 0, 31, 55, 7, 13),
  (4036, 0, 24, 48, 34, 16, 0, 36, 6, 52, 16),
  (4037, 0, 30, 1, 56, 16, 0, 50, 39, 4, 12),
  (4038, 0, 7, 25, 58, 17, 0, 25, 58, 7, 13),
  (4039, 1, 42, 47, 8, 13, 1, 56, 26, 15, 13),
  (4040, 1, 14, 19, 59, 17, 1, 22, 23, 55, 17),
  (4041, 0, 22, 49, 34, 16, 0, 26, 47, 34, 16),
  (4042, 0, 21, 24, 55, 17, 0, 45, 44, 9, 13),
  (4043, 0, 11, 21, 59, 17, 1, 6, 33, 54, 17),
  (4044, 1, 57, 27, 8, 12, 2, 6, 52, 36, 16),
  (4045, 0, 21, 30, 52, 17, 0, 42, 45, 16, 14),
  (4046, 0, 6, 61, 17, 14, 0, 9, 22, 59, 17),
  (4047, 1, 38, 45, 24, 15, 1, 48, 30, 29, 15),
  (4048, 0, 40, 12, 48, 16, 1, 1, 51, 38, 16),
  (4049, 0, 2, 51, 38, 16, 0, 2, 61, 18, 14)
  ]

lemma witChunk_76_ok : witChunk_76.all checkWit = true := by
  decide +kernel

lemma witChunk_76_ns :
    witChunk_76.map (fun t => t.1) = (List.range 50).map (· + 4000) := by
  decide +kernel

def witChunk_77 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4050, 0, 11, 35, 52, 17, 0, 13, 20, 59, 17),
  (4051, 0, 15, 35, 51, 17, 0, 19, 21, 57, 17),
  (4052, 1, 11, 52, 35, 16, 1, 15, 60, 15, 14),
  (4053, 0, 17, 20, 58, 17, 0, 32, 2, 55, 16),
  (4054, 0, 7, 33, 54, 17, 0, 33, 54, 7, 13),
  (4055, 1, 8, 58, 25, 15, 1, 31, 44, 34, 16),
  (4056, 0, 20, 50, 34, 16, 0, 28, 46, 34, 16),
  (4057, 0, 42, 23, 42, 16, 2, 3, 26, 58, 17),
  (4058, 0, 5, 28, 57, 17, 1, 4, 26, 58, 17),
  (4059, 0, 7, 23, 59, 17, 0, 23, 59, 7, 13),
  (4060, 1, 9, 61, 16, 14, 1, 61, 9, 16, 12),
  (4061, 0, 5, 30, 56, 17, 0, 21, 22, 56, 17),
  (4062, 0, 34, 41, 35, 16, 0, 55, 29, 14, 13),
  (4063, 1, 10, 19, 60, 17, 1, 16, 18, 59, 17),
  (4064, 0, 8, 52, 36, 16, 1, 29, 55, 14, 14),
  (4065, 0, 5, 26, 58, 17, 0, 5, 58, 26, 15),
  (4066, 0, 13, 36, 51, 17, 0, 21, 32, 51, 17),
  (4067, 0, 15, 19, 59, 17, 0, 23, 27, 53, 17),
  (4068, 0, 40, 32, 38, 16, 0, 60, 18, 12, 12),
  (4069, 1, 61, 11, 15, 12, 2, 11, 58, 24, 15),
  (4070, 0, 9, 58, 25, 15, 0, 23, 25, 54, 17),
  (4071, 3, 2, 32, 55, 17, 3, 20, 17, 58, 17),
  (4072, 0, 48, 38, 18, 14, 1, 6, 35, 53, 17),
  (4073, 0, 10, 63, 2, 12, 0, 12, 52, 35, 16),
  (4074, 0, 5, 32, 55, 17, 0, 23, 29, 52, 17),
  (4075, 1, 2, 63, 10, 13, 1, 4, 24, 59, 17),
  (4076, 5, 61, 7, 16, 12, 6, 2, 52, 36, 16),
  (4077, 0, 10, 61, 16, 14, 0, 13, 62, 8, 13),
  (4078, 0, 3, 63, 10, 13, 0, 42, 17, 45, 16),
  (4079, 1, 6, 21, 60, 17, 1, 24, 30, 51, 17),
  (4080, 2, 34, 54, 0, 12, 3, 35, 41, 34, 16),
  (4081, 0, 9, 20, 60, 17, 0, 9, 36, 52, 17),
  (4082, 0, 5, 24, 59, 17, 0, 11, 19, 60, 17),
  (4083, 0, 7, 35, 53, 17, 0, 23, 23, 55, 17),
  (4084, 1, 3, 52, 37, 16, 1, 61, 19, 0, 10),
  (4085, 0, 17, 36, 50, 17, 0, 49, 28, 30, 15),
  (4086, 0, 19, 19, 58, 17, 0, 19, 35, 50, 17),
  (4087, 1, 14, 17, 60, 17, 1, 15, 52, 34, 16),
  (4088, 1, 6, 63, 9, 13, 1, 34, 49, 23, 15),
  (4089, 0, 4, 52, 37, 16, 2, 3, 34, 54, 17),
  (4090, 0, 7, 21, 60, 17, 0, 21, 20, 57, 17),
  (4091, 0, 11, 37, 51, 17, 0, 23, 31, 51, 17),
  (4092, 1, 29, 57, 0, 12, 2, 22, 60, 0, 12),
  (4093, 0, 13, 18, 60, 17, 0, 42, 27, 40, 16),
  (4094, 0, 1, 58, 27, 15, 0, 15, 37, 50, 17),
  (4095, 1, 0, 58, 27, 15, 1, 27, 58, 0, 12),
  (4096, 0, 0, 0, 64, 16, 0, 64, 0, 0, 8),
  (4097, 0, 5, 34, 54, 17, 0, 21, 34, 50, 17),
  (4098, 2, 12, 61, 15, 14, 2, 20, 51, 33, 16),
  (4099, 0, 3, 29, 57, 17, 0, 7, 63, 9, 13)
  ]

lemma witChunk_77_ok : witChunk_77.all checkWit = true := by
  decide +kernel

lemma witChunk_77_ns :
    witChunk_77.map (fun t => t.1) = (List.range 50).map (· + 4050) := by
  decide +kernel

def witChunk_78 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4100, 1, 37, 5, 52, 16, 1, 43, 20, 43, 16),
  (4101, 0, 16, 62, 1, 12, 0, 40, 10, 49, 16),
  (4102, 0, 3, 27, 58, 17, 1, 4, 22, 60, 17),
  (4103, 1, 2, 31, 56, 17, 1, 16, 38, 49, 17),
  (4104, 1, 18, 57, 23, 15, 1, 50, 9, 39, 15),
  (4105, 0, 42, 15, 46, 16, 2, 54, 34, 5, 12),
  (4106, 0, 3, 31, 56, 17, 0, 21, 56, 23, 15),
  (4107, 2, 57, 25, 15, 13, 3, 4, 37, 52, 17),
  (4108, 1, 25, 59, 0, 12, 1, 41, 11, 48, 16),
  (4109, 0, 5, 22, 60, 17, 0, 13, 58, 24, 15),
  (4110, 0, 25, 26, 53, 17, 2, 9, 39, 50, 17),
  (4111, 1, 6, 37, 52, 17, 1, 8, 18, 61, 17),
  (4112, 0, 0, 64, 4, 12, 1, 2, 25, 59, 17),
  (4113, 0, 13, 38, 50, 17, 0, 25, 28, 52, 17),
  (4114, 0, 15, 17, 60, 17, 0, 55, 33, 0, 11),
  (4115, 0, 3, 25, 59, 17, 0, 51, 17, 35, 15),
  (4116, 0, 16, 52, 34, 16, 0, 28, 56, 14, 14),
  (4117, 0, 25, 24, 54, 17, 1, 9, 53, 35, 16),
  (4118, 0, 23, 33, 50, 17, 0, 33, 50, 23, 15),
  (4119, 3, 10, 40, 49, 17, 3, 26, 20, 55, 17),
  (4120, 1, 2, 33, 55, 17, 1, 6, 19, 61, 17),
  (4121, 0, 4, 64, 3, 12, 0, 26, 57, 14, 14),
  (4122, 0, 7, 37, 52, 17, 0, 37, 52, 7, 13),
  (4123, 0, 3, 33, 55, 17, 1, 4, 36, 53, 17),
  (4124, 1, 27, 48, 33, 16, 1, 61, 1, 20, 12),
  (4125, 0, 40, 34, 37, 16, 2, 18, 52, 33, 16),
  (4126, 0, 9, 18, 61, 17, 0, 9, 38, 51, 17),
  (4127, 1, 35, 52, 14, 14, 1, 43, 26, 40, 16),
  (4128, 0, 44, 44, 16, 14, 0, 52, 32, 20, 14),
  (4129, 0, 21, 18, 58, 17, 0, 40, 48, 15, 14),
  (4130, 0, 5, 36, 53, 17, 2, 11, 40, 49, 17),
  (4131, 0, 7, 19, 61, 17, 0, 11, 17, 61, 17),
  (4132, 1, 5, 53, 36, 16, 1, 43, 16, 45, 16),
  (4133, 1, 21, 51, 33, 16, 3, 39, 37, 35, 16),
  (4134, 0, 10, 53, 35, 16, 0, 17, 38, 49, 17),
  (4135, 1, 2, 23, 60, 17, 1, 10, 63, 8, 13),
  (4136, 0, 24, 58, 14, 14, 0, 32, 54, 14, 14),
  (4137, 2, 15, 40, 48, 17, 2, 23, 36, 48, 17),
  (4138, 0, 3, 23, 60, 17, 0, 21, 36, 49, 17),
  (4139, 0, 19, 57, 23, 15, 0, 23, 19, 57, 17),
  (4140, 1, 59, 24, 9, 12, 3, 4, 59, 25, 15),
  (4141, 0, 6, 53, 36, 16, 1, 13, 63, 1, 12),
  (4142, 0, 11, 39, 50, 17, 0, 14, 61, 15, 14),
  (4143, 1, 35, 54, 0, 12, 3, 2, 20, 61, 17),
  (4144, 1, 3, 62, 17, 14, 1, 6, 59, 25, 15),
  (4145, 0, 17, 16, 60, 17, 0, 45, 38, 26, 15),
  (4146, 0, 5, 20, 61, 17, 0, 13, 16, 61, 17),
  (4147, 0, 15, 39, 49, 17, 0, 63, 3, 13, 11),
  (4148, 0, 0, 52, 38, 16, 0, 28, 58, 0, 12),
  (4149, 0, 1, 28, 58, 17, 0, 4, 62, 17, 14)
  ]

lemma witChunk_78_ok : witChunk_78.all checkWit = true := by
  decide +kernel

lemma witChunk_78_ns :
    witChunk_78.map (fun t => t.1) = (List.range 50).map (· + 4100) := by
  decide +kernel

def witChunk_79 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4150, 0, 1, 30, 57, 17, 0, 3, 35, 54, 17),
  (4151, 1, 0, 30, 57, 17, 1, 7, 62, 16, 14),
  (4152, 3, 1, 62, 17, 14, 3, 43, 13, 46, 16),
  (4153, 2, 47, 0, 44, 15, 2, 51, 10, 38, 15),
  (4154, 0, 11, 63, 8, 13, 0, 51, 23, 32, 15),
  (4155, 0, 7, 59, 25, 15, 0, 23, 35, 49, 17),
  (4156, 1, 19, 52, 33, 16, 1, 43, 28, 39, 16),
  (4157, 0, 26, 59, 0, 12, 0, 58, 27, 8, 12),
  (4158, 0, 1, 26, 59, 17, 2, 9, 15, 62, 17),
  (4159, 1, 0, 26, 59, 17, 1, 10, 59, 24, 15),
  (4160, 0, 32, 0, 56, 16, 0, 32, 56, 0, 12),
  (4161, 0, 1, 32, 56, 17, 0, 14, 53, 34, 16),
  (4162, 0, 27, 27, 52, 17, 1, 0, 32, 56, 17),
  (4163, 0, 27, 25, 53, 17, 0, 47, 35, 27, 15),
  (4164, 0, 8, 62, 16, 14, 0, 8, 64, 2, 12),
  (4165, 0, 24, 50, 33, 16, 1, 41, 9, 49, 16),
  (4166, 0, 3, 59, 26, 15, 0, 14, 63, 1, 12),
  (4167, 3, 4, 17, 62, 17, 3, 25, 50, 32, 16),
  (4168, 0, 0, 62, 18, 14, 0, 64, 6, 6, 10),
  (4169, 0, 42, 31, 38, 16, 2, 11, 14, 62, 17),
  (4170, 0, 13, 40, 49, 17, 3, 2, 38, 52, 17),
  (4171, 0, 3, 21, 61, 17, 0, 7, 39, 51, 17),
  (4172, 1, 53, 31, 20, 14, 2, 38, 4, 52, 16),
  (4173, 0, 5, 38, 52, 17, 0, 38, 5, 52, 16),
  (4174, 0, 22, 51, 33, 16, 0, 27, 23, 54, 17),
  (4175, 1, 16, 14, 61, 17, 1, 26, 19, 56, 17),
  (4176, 0, 24, 60, 0, 12, 2, 18, 62, 0, 12),
  (4177, 0, 1, 24, 60, 17, 0, 28, 48, 33, 16),
  (4178, 0, 11, 59, 24, 15, 0, 21, 16, 59, 17),
  (4179, 2, 21, 39, 47, 17, 2, 29, 27, 51, 17),
  (4180, 1, 37, 53, 0, 12, 2, 10, 54, 34, 16),
  (4181, 0, 9, 16, 62, 17, 0, 9, 40, 50, 17),
  (4182, 0, 1, 34, 55, 17, 0, 2, 53, 37, 16),
  (4183, 1, 0, 34, 55, 17, 1, 14, 41, 48, 17),
  (4184, 0, 44, 22, 42, 16, 0, 60, 22, 10, 12),
  (4185, 0, 44, 20, 43, 16, 0, 64, 8, 5, 10),
  (4186, 0, 19, 15, 60, 17, 0, 19, 39, 48, 17),
  (4187, 0, 3, 37, 53, 17, 0, 51, 25, 31, 15),
  (4188, 3, 28, 19, 55, 17, 3, 59, 25, 8, 12),
  (4189, 0, 21, 38, 48, 17, 0, 42, 11, 48, 16),
  (4190, 0, 11, 15, 62, 17, 0, 27, 31, 50, 17),
  (4191, 1, 42, 43, 24, 15, 1, 48, 34, 27, 15),
  (4192, 0, 40, 36, 36, 16, 1, 7, 54, 35, 16),
  (4193, 0, 5, 18, 62, 17, 0, 17, 40, 48, 17),
  (4194, 2, 3, 64, 9, 13, 2, 44, 15, 45, 16),
  (4195, 0, 27, 21, 55, 17, 1, 4, 64, 9, 13),
  (4196, 0, 20, 60, 14, 14, 0, 36, 52, 14, 14),
  (4197, 0, 1, 64, 10, 13, 2, 11, 42, 48, 17),
  (4198, 0, 25, 18, 57, 17, 0, 30, 47, 33, 16),
  (4199, 3, 2, 64, 9, 13, 3, 26, 16, 57, 17)
  ]

lemma witChunk_79_ok : witChunk_79.all checkWit = true := by
  decide +kernel

lemma witChunk_79_ns :
    witChunk_79.map (fun t => t.1) = (List.range 50).map (· + 4150) := by
  decide +kernel

def witChunk_80 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4200, 3, 37, 2, 53, 16, 3, 55, 1, 34, 14),
  (4201, 2, 55, 32, 12, 13, 2, 64, 9, 4, 10),
  (4202, 0, 5, 64, 9, 13, 0, 23, 37, 48, 17),
  (4203, 0, 11, 41, 49, 17, 0, 51, 9, 39, 15),
  (4204, 1, 41, 35, 36, 16, 1, 43, 12, 47, 16),
  (4205, 0, 8, 54, 35, 16, 0, 22, 61, 0, 12),
  (4206, 0, 1, 22, 61, 17, 0, 17, 14, 61, 17),
  (4207, 1, 0, 22, 61, 17, 1, 19, 62, 0, 12),
  (4208, 1, 14, 59, 23, 15, 1, 17, 61, 14, 14),
  (4209, 0, 13, 14, 62, 17, 0, 49, 32, 28, 15),
  (4210, 0, 15, 41, 48, 17, 2, 28, 57, 13, 14),
  (4211, 0, 59, 1, 27, 13, 0, 59, 21, 17, 13),
  (4212, 0, 36, 54, 0, 12, 0, 44, 26, 40, 16),
  (4213, 0, 1, 36, 54, 17, 0, 12, 62, 15, 14),
  (4214, 0, 3, 19, 62, 17, 0, 59, 27, 2, 11),
  (4215, 3, 4, 41, 50, 17, 3, 20, 41, 46, 17),
  (4216, 0, 12, 54, 34, 16, 0, 36, 2, 54, 16),
  (4217, 0, 44, 16, 45, 16, 2, 7, 64, 8, 13),
  (4218, 2, 3, 40, 51, 17, 2, 21, 13, 60, 17),
  (4219, 0, 27, 33, 49, 17, 1, 4, 40, 51, 17),
  (4220, 1, 11, 64, 1, 12, 2, 22, 52, 32, 16),
  (4221, 0, 29, 26, 52, 17, 0, 46, 43, 16, 14),
  (4222, 0, 18, 53, 33, 16, 0, 42, 33, 37, 16),
  (4223, 1, 3, 54, 36, 16, 1, 51, 36, 18, 14),
  (4224, 2, 2, 54, 36, 16, 2, 42, 34, 36, 16),
  (4225, 0, 25, 36, 48, 17, 10, 20, 59, 12, 14),
  (4226, 0, 5, 40, 51, 17, 0, 27, 19, 56, 17),
  (4227, 1, 39, 52, 0, 12, 2, 5, 15, 63, 17),
  (4228, 0, 4, 54, 36, 16, 1, 63, 16, 1, 10),
  (4229, 0, 32, 46, 33, 16, 0, 57, 28, 14, 13),
  (4230, 0, 7, 41, 50, 17, 0, 41, 50, 7, 13),
  (4231, 1, 2, 39, 52, 17, 1, 8, 14, 63, 17),
  (4232, 1, 6, 15, 63, 17, 1, 15, 54, 33, 16),
  (4233, 2, 7, 60, 24, 15, 2, 16, 63, 0, 12),
  (4234, 0, 3, 39, 52, 17, 2, 1, 39, 52, 17),
  (4235, 0, 15, 59, 23, 15, 0, 23, 15, 59, 17),
  (4236, 2, 30, 48, 32, 16, 2, 54, 36, 4, 12),
  (4237, 0, 13, 42, 48, 17, 0, 21, 14, 60, 17),
  (4238, 0, 2, 65, 3, 12, 0, 15, 13, 62, 17),
  (4239, 3, 16, 11, 62, 17, 3, 16, 43, 46, 17),
  (4240, 1, 10, 13, 63, 17, 1, 30, 23, 53, 17),
  (4241, 0, 9, 64, 8, 13, 0, 12, 64, 1, 12),
  (4242, 1, 8, 60, 24, 15, 1, 48, 0, 44, 15),
  (4243, 0, 7, 15, 63, 17, 0, 15, 63, 7, 13),
  (4244, 0, 20, 62, 0, 12, 0, 48, 44, 2, 12),
  (4245, 0, 1, 20, 62, 17, 0, 25, 16, 58, 17),
  (4246, 0, 9, 14, 63, 17, 0, 9, 42, 49, 17),
  (4247, 1, 40, 46, 23, 15, 1, 50, 31, 28, 15),
  (4248, 0, 44, 14, 46, 16, 1, 57, 31, 6, 12),
  (4249, 0, 64, 12, 3, 10, 2, 4, 63, 16, 14)
  ]

lemma witChunk_80_ok : witChunk_80.all checkWit = true := by
  decide +kernel

lemma witChunk_80_ns :
    witChunk_80.map (fun t => t.1) = (List.range 50).map (· + 4200) := by
  decide +kernel

def witChunk_81 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4250, 0, 5, 16, 63, 17, 0, 5, 60, 25, 15),
  (4251, 0, 19, 13, 61, 17, 0, 19, 41, 47, 17),
  (4252, 1, 5, 63, 16, 14, 1, 25, 51, 32, 16),
  (4253, 0, 38, 53, 0, 12, 2, 4, 65, 2, 12),
  (4254, 0, 1, 38, 53, 17, 0, 31, 53, 22, 15),
  (4255, 1, 0, 38, 53, 17, 1, 10, 43, 48, 17),
  (4256, 1, 5, 65, 2, 12, 1, 14, 43, 47, 17),
  (4257, 0, 9, 60, 24, 15, 0, 60, 24, 9, 12),
  (4258, 0, 27, 35, 48, 17, 0, 55, 33, 12, 13),
  (4259, 0, 11, 13, 63, 17, 0, 23, 39, 47, 17),
  (4260, 1, 17, 63, 0, 12, 3, 20, 11, 61, 17),
  (4261, 0, 6, 63, 16, 14, 0, 16, 54, 33, 16),
  (4262, 0, 2, 63, 17, 14, 0, 17, 42, 47, 17),
  (4263, 3, 10, 44, 47, 17, 3, 10, 64, 7, 13),
  (4264, 1, 2, 17, 63, 17, 1, 9, 55, 34, 16),
  (4265, 0, 6, 65, 2, 12, 2, 32, 47, 32, 16),
  (4266, 0, 29, 20, 55, 17, 0, 29, 32, 49, 17),
  (4267, 0, 3, 17, 63, 17, 0, 27, 17, 57, 17),
  (4268, 1, 29, 49, 32, 16, 1, 31, 56, 13, 14),
  (4269, 0, 40, 38, 35, 16, 2, 39, 52, 6, 13),
  (4270, 0, 34, 45, 33, 16, 2, 25, 39, 46, 17),
  (4271, 1, 64, 2, 13, 11, 3, 26, 56, 21, 15),
  (4272, 2, 18, 54, 32, 16, 2, 42, 48, 14, 14),
  (4273, 0, 57, 32, 0, 11, 4, 24, 52, 31, 16),
  (4274, 0, 11, 43, 48, 17, 0, 43, 43, 24, 15),
  (4275, 1, 12, 60, 23, 15, 1, 50, 3, 42, 15),
  (4276, 1, 21, 53, 32, 16, 2, 50, 42, 2, 12),
  (4277, 0, 1, 60, 26, 15, 0, 17, 12, 62, 17),
  (4278, 0, 25, 38, 47, 17, 1, 0, 60, 26, 15),
  (4279, 1, 39, 40, 34, 16, 1, 64, 10, 9, 11),
  (4280, 0, 44, 30, 38, 16, 1, 41, 49, 14, 14),
  (4281, 0, 10, 55, 34, 16, 0, 38, 41, 34, 16),
  (4282, 0, 13, 12, 63, 17, 1, 4, 42, 50, 17),
  (4283, 0, 15, 43, 47, 17, 0, 51, 29, 29, 15),
  (4284, 1, 41, 51, 0, 12, 3, 4, 43, 49, 17),
  (4285, 0, 0, 54, 37, 16, 0, 42, 35, 36, 16),
  (4286, 0, 6, 55, 35, 16, 0, 23, 61, 6, 13),
  (4287, 3, 28, 37, 46, 17, 5, 27, 58, 12, 14),
  (4288, 1, 2, 41, 51, 17, 1, 6, 43, 49, 17),
  (4289, 0, 5, 42, 50, 17, 0, 21, 58, 22, 15),
  (4290, 0, 31, 25, 52, 17, 0, 53, 16, 35, 15),
  (4291, 0, 3, 41, 51, 17, 0, 31, 27, 51, 17),
  (4292, 1, 65, 1, 8, 10, 3, 15, 55, 32, 16),
  (4293, 0, 18, 63, 0, 12, 2, 42, 36, 35, 16),
  (4294, 0, 1, 18, 63, 17, 0, 10, 63, 15, 14),
  (4295, 1, 0, 18, 63, 17, 1, 30, 33, 48, 17),
  (4296, 0, 16, 62, 14, 14, 0, 40, 50, 14, 14),
  (4297, 2, 7, 12, 64, 17, 2, 7, 44, 48, 17),
  (4298, 0, 13, 60, 23, 15, 0, 23, 13, 60, 17),
  (4299, 0, 7, 43, 49, 17, 0, 31, 23, 53, 17)
  ]

lemma witChunk_81_ok : witChunk_81.all checkWit = true := by
  decide +kernel

lemma witChunk_81_ns :
    witChunk_81.map (fun t => t.1) = (List.range 50).map (· + 4250) := by
  decide +kernel

def witChunk_82 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4300, 1, 23, 60, 13, 14, 1, 57, 5, 32, 14),
  (4301, 0, 26, 51, 32, 16, 0, 29, 18, 56, 17),
  (4302, 0, 25, 14, 59, 17, 0, 31, 29, 50, 17),
  (4303, 1, 6, 13, 64, 17, 1, 19, 54, 32, 16),
  (4304, 0, 24, 52, 32, 16, 0, 40, 52, 0, 12),
  (4305, 0, 1, 40, 52, 17, 0, 61, 10, 22, 13),
  (4306, 0, 21, 12, 61, 17, 0, 61, 12, 21, 13),
  (4307, 0, 27, 37, 47, 17, 0, 51, 5, 41, 15),
  (4308, 0, 28, 50, 32, 16, 2, 42, 6, 50, 16),
  (4309, 1, 9, 65, 1, 12, 1, 37, 43, 33, 16),
  (4310, 0, 14, 55, 33, 16, 0, 35, 51, 22, 15),
  (4311, 1, 63, 4, 18, 12, 1, 63, 12, 14, 12),
  (4312, 1, 2, 65, 9, 13, 1, 35, 54, 13, 14),
  (4313, 0, 42, 7, 50, 16, 0, 52, 40, 3, 12),
  (4314, 0, 7, 13, 64, 17, 0, 13, 44, 47, 17),
  (4315, 0, 3, 65, 9, 13, 0, 15, 11, 63, 17),
  (4316, 1, 43, 8, 49, 16, 1, 59, 28, 7, 12),
  (4317, 0, 5, 14, 64, 17, 0, 22, 53, 32, 16),
  (4318, 0, 27, 15, 58, 17, 0, 30, 57, 13, 14),
  (4319, 1, 10, 11, 64, 17, 1, 32, 22, 53, 17),
  (4320, 0, 40, 4, 52, 16, 1, 42, 45, 23, 15),
  (4321, 0, 9, 12, 64, 17, 0, 9, 44, 48, 17),
  (4322, 0, 53, 12, 37, 15, 1, 24, 12, 60, 17),
  (4323, 0, 31, 31, 49, 17, 0, 59, 29, 1, 11),
  (4324, 0, 48, 42, 16, 14, 0, 52, 36, 18, 14),
  (4325, 0, 2, 55, 36, 16, 0, 30, 49, 32, 16),
  (4326, 0, 10, 65, 1, 12, 0, 19, 11, 62, 17),
  (4327, 1, 2, 15, 64, 17, 1, 6, 65, 8, 13),
  (4328, 1, 22, 11, 61, 17, 1, 26, 13, 59, 17),
  (4329, 0, 32, 56, 13, 14, 0, 44, 32, 37, 16),
  (4330, 0, 3, 15, 64, 17, 2, 1, 15, 64, 17),
  (4331, 0, 59, 25, 15, 13, 1, 18, 63, 6, 13),
  (4332, 3, 8, 61, 23, 15, 3, 44, 43, 23, 15),
  (4333, 0, 61, 6, 24, 13, 1, 21, 61, 13, 14),
  (4334, 2, 29, 37, 46, 17, 2, 31, 34, 47, 17),
  (4335, 1, 6, 61, 24, 15, 3, 5, 56, 34, 16),
  (4336, 1, 10, 45, 47, 17, 1, 13, 63, 14, 14),
  (4337, 0, 49, 0, 44, 15, 4, 62, 19, 10, 12),
  (4338, 0, 7, 65, 8, 13, 0, 11, 11, 64, 17),
  (4339, 1, 14, 45, 46, 17, 1, 55, 36, 4, 12),
  (4340, 0, 20, 54, 32, 16, 0, 44, 10, 48, 16),
  (4341, 0, 17, 44, 46, 17, 0, 25, 40, 46, 17),
  (4342, 1, 12, 10, 64, 17, 1, 16, 60, 22, 15),
  (4343, 1, 7, 56, 34, 16, 1, 64, 14, 7, 11),
  (4344, 5, 30, 37, 45, 17, 5, 54, 17, 33, 15),
  (4345, 0, 24, 60, 13, 14, 0, 58, 9, 30, 14),
  (4346, 0, 7, 61, 24, 15, 0, 29, 16, 57, 17),
  (4347, 0, 31, 19, 55, 17, 2, 17, 9, 63, 17),
  (4348, 1, 11, 56, 33, 16, 2, 58, 20, 24, 14),
  (4349, 1, 37, 53, 13, 14, 1, 57, 3, 33, 14)
  ]

lemma witChunk_82_ok : witChunk_82.all checkWit = true := by
  decide +kernel

lemma witChunk_82_ns :
    witChunk_82.map (fun t => t.1) = (List.range 50).map (· + 4300) := by
  decide +kernel

def witChunk_83 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4350, 0, 34, 55, 13, 14, 0, 58, 19, 25, 14),
  (4351, 1, 43, 48, 14, 14, 1, 43, 50, 0, 12),
  (4352, 0, 16, 64, 0, 12, 0, 32, 48, 32, 16),
  (4353, 0, 1, 16, 64, 17, 0, 37, 50, 22, 15),
  (4354, 0, 31, 33, 48, 17, 1, 0, 16, 64, 17),
  (4355, 0, 3, 61, 25, 15, 0, 11, 45, 47, 17),
  (4356, 0, 8, 56, 34, 16, 0, 40, 40, 34, 16),
  (4357, 1, 45, 11, 47, 16, 1, 45, 31, 37, 16),
  (4358, 0, 3, 43, 50, 17, 0, 17, 10, 63, 17),
  (4359, 3, 2, 44, 49, 17, 3, 34, 28, 49, 17),
  (4360, 1, 22, 43, 45, 17, 1, 41, 39, 34, 16),
  (4361, 0, 14, 63, 14, 14, 0, 38, 1, 54, 16),
  (4362, 0, 5, 44, 49, 17, 0, 61, 4, 25, 13),
  (4363, 0, 51, 41, 9, 13, 1, 3, 64, 16, 14),
  (4364, 2, 2, 64, 16, 14, 2, 14, 56, 32, 16),
  (4365, 0, 0, 66, 3, 12, 0, 13, 10, 64, 17),
  (4366, 0, 1, 42, 51, 17, 0, 15, 45, 46, 17),
  (4367, 1, 0, 42, 51, 17, 1, 6, 45, 48, 17),
  (4368, 0, 4, 64, 16, 14, 1, 26, 57, 21, 15),
  (4369, 0, 12, 56, 33, 16, 0, 25, 12, 60, 17),
  (4370, 2, 52, 37, 17, 14, 4, 1, 44, 49, 17),
  (4371, 0, 11, 61, 23, 15, 0, 23, 11, 61, 17),
  (4372, 1, 3, 56, 35, 16, 1, 7, 64, 15, 14),
  (4373, 0, 17, 60, 22, 15, 0, 18, 55, 32, 16),
  (4374, 0, 22, 61, 13, 14, 0, 51, 3, 42, 15),
  (4375, 1, 14, 9, 64, 17, 1, 32, 18, 55, 17),
  (4376, 0, 4, 66, 2, 12, 1, 10, 65, 7, 13),
  (4377, 0, 4, 56, 35, 16, 2, 12, 65, 0, 12),
  (4378, 0, 7, 45, 48, 17, 0, 45, 48, 7, 13),
  (4379, 0, 27, 13, 59, 17, 2, 5, 11, 65, 17),
  (4380, 3, 1, 56, 35, 16, 3, 4, 11, 65, 17),
  (4381, 0, 36, 54, 13, 14, 0, 58, 21, 24, 14),
  (4382, 0, 33, 22, 53, 17, 0, 38, 43, 33, 16),
  (4383, 1, 24, 58, 21, 15, 1, 32, 54, 21, 15),
  (4384, 1, 6, 11, 65, 17, 1, 26, 41, 45, 17),
  (4385, 0, 0, 64, 17, 14, 0, 8, 64, 15, 14),
  (4386, 0, 31, 17, 56, 17, 2, 3, 12, 65, 17),
  (4387, 1, 4, 12, 65, 17, 1, 15, 56, 32, 16),
  (4388, 0, 44, 34, 36, 16, 3, 8, 9, 65, 17),
  (4389, 0, 34, 47, 32, 16, 0, 65, 8, 10, 11),
  (4390, 0, 33, 30, 49, 17, 0, 42, 5, 51, 16),
  (4391, 1, 8, 10, 65, 17, 1, 8, 46, 47, 17),
  (4392, 3, 43, 5, 50, 16, 3, 43, 37, 34, 16),
  (4393, 2, 15, 8, 64, 17, 2, 43, 50, 6, 13),
  (4394, 0, 5, 12, 65, 17, 0, 53, 8, 39, 15),
  (4395, 0, 7, 11, 65, 17, 0, 11, 65, 7, 13),
  (4396, 1, 13, 65, 0, 12, 1, 27, 52, 31, 16),
  (4397, 1, 25, 53, 31, 16, 2, 52, 41, 2, 12),
  (4398, 0, 65, 2, 13, 11, 4, 51, 1, 42, 15),
  (4399, 1, 16, 46, 45, 17, 1, 24, 10, 61, 17)
  ]

lemma witChunk_83_ok : witChunk_83.all checkWit = true := by
  decide +kernel

lemma witChunk_83_ns :
    witChunk_83.map (fun t => t.1) = (List.range 50).map (· + 4350) := by
  decide +kernel

def witChunk_84 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4400, 1, 2, 13, 65, 17, 1, 34, 29, 49, 17),
  (4401, 0, 13, 46, 46, 17, 0, 29, 14, 58, 17),
  (4402, 0, 15, 9, 64, 17, 0, 21, 44, 45, 17),
  (4403, 0, 3, 13, 65, 17, 0, 23, 43, 45, 17),
  (4404, 2, 54, 34, 18, 14, 3, 17, 56, 31, 16),
  (4405, 0, 33, 20, 54, 17, 1, 29, 51, 31, 16),
  (4406, 0, 9, 10, 65, 17, 0, 9, 46, 47, 17),
  (4407, 1, 66, 7, 0, 9, 3, 8, 47, 46, 17),
  (4408, 1, 7, 66, 1, 12, 1, 10, 9, 65, 17),
  (4409, 2, 23, 44, 44, 17, 2, 35, 26, 50, 17),
  (4410, 0, 61, 20, 17, 13, 2, 8, 57, 33, 16),
  (4411, 0, 19, 9, 63, 17, 0, 19, 45, 45, 17),
  (4412, 1, 45, 9, 48, 16, 1, 45, 33, 36, 16),
  (4413, 0, 20, 62, 13, 14, 0, 40, 2, 53, 16),
  (4414, 0, 25, 42, 45, 17, 0, 66, 3, 7, 10),
  (4415, 1, 11, 64, 14, 14, 1, 32, 58, 5, 13),
  (4416, 0, 16, 56, 32, 16, 0, 64, 8, 16, 12),
  (4417, 0, 33, 32, 48, 17, 0, 57, 32, 12, 13),
  (4418, 0, 29, 56, 21, 15, 1, 16, 8, 64, 17),
  (4419, 0, 27, 57, 21, 15, 0, 51, 33, 27, 15),
  (4420, 0, 64, 18, 0, 10, 1, 37, 45, 32, 16),
  (4421, 0, 8, 66, 1, 12, 0, 14, 65, 0, 12),
  (4422, 0, 1, 14, 65, 17, 0, 38, 53, 13, 14),
  (4423, 1, 0, 14, 65, 17, 1, 34, 31, 48, 17),
  (4424, 1, 26, 61, 5, 13, 1, 31, 50, 31, 16),
  (4425, 2, 12, 57, 32, 16, 2, 32, 57, 12, 14),
  (4426, 0, 63, 21, 4, 11, 2, 61, 21, 16, 13),
  (4427, 0, 11, 9, 65, 17, 0, 31, 55, 21, 15),
  (4428, 1, 45, 49, 0, 12, 2, 26, 60, 12, 14),
  (4429, 1, 17, 63, 13, 14, 1, 21, 55, 31, 16),
  (4430, 0, 15, 61, 22, 15, 0, 17, 46, 45, 17),
  (4431, 3, 53, 40, 2, 12, 5, 36, 22, 51, 17),
  (4432, 0, 0, 56, 36, 16, 1, 2, 45, 49, 17),
  (4433, 0, 60, 28, 7, 12, 0, 65, 12, 8, 11),
  (4434, 0, 53, 28, 29, 15, 2, 48, 21, 41, 16),
  (4435, 0, 3, 45, 49, 17, 0, 27, 41, 45, 17),
  (4436, 0, 12, 64, 14, 14, 0, 36, 46, 32, 16),
  (4437, 0, 1, 44, 50, 17, 0, 50, 41, 16, 14),
  (4438, 0, 1, 66, 9, 13, 0, 10, 57, 33, 16),
  (4439, 1, 0, 66, 9, 13, 1, 8, 62, 23, 15),
  (4440, 3, 65, 14, 1, 10, 5, 33, 49, 30, 16),
  (4441, 0, 6, 57, 34, 16, 0, 42, 39, 34, 16),
  (4442, 0, 59, 31, 0, 11, 2, 17, 7, 64, 17),
  (4443, 1, 20, 60, 21, 15, 1, 36, 52, 21, 15),
  (4444, 1, 13, 57, 32, 16, 2, 34, 56, 12, 14),
  (4445, 0, 5, 46, 48, 17, 0, 5, 62, 24, 15),
  (4446, 0, 11, 47, 46, 17, 0, 25, 10, 61, 17),
  (4447, 1, 22, 45, 44, 17, 1, 24, 62, 5, 13),
  (4448, 0, 56, 36, 4, 12, 1, 30, 39, 45, 17),
  (4449, 0, 17, 8, 64, 17, 0, 28, 52, 31, 16)
  ]

lemma witChunk_84_ok : witChunk_84.all checkWit = true := by
  decide +kernel

lemma witChunk_84_ns :
    witChunk_84.map (fun t => t.1) = (List.range 50).map (· + 4400) := by
  decide +kernel

def witChunk_85 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4450, 0, 27, 11, 60, 17, 0, 61, 0, 27, 13),
  (4451, 0, 23, 59, 21, 15, 0, 35, 25, 51, 17),
  (4452, 3, 4, 47, 47, 17, 3, 13, 64, 13, 14),
  (4453, 0, 24, 54, 31, 16, 0, 40, 42, 33, 16),
  (4454, 0, 9, 62, 23, 15, 0, 23, 9, 62, 17),
  (4455, 3, 9, 66, 0, 12, 3, 34, 16, 55, 17),
  (4456, 1, 6, 47, 47, 17, 1, 34, 33, 47, 17),
  (4457, 0, 44, 36, 35, 16, 2, 11, 62, 22, 15),
  (4458, 0, 13, 8, 65, 17, 0, 35, 23, 52, 17),
  (4459, 0, 15, 47, 45, 17, 1, 14, 65, 6, 13),
  (4460, 1, 19, 56, 31, 16, 3, 32, 13, 57, 17),
  (4461, 0, 61, 22, 16, 13, 0, 64, 2, 19, 12),
  (4462, 0, 18, 63, 13, 14, 0, 30, 51, 31, 16),
  (4463, 1, 26, 43, 44, 17, 3, 18, 64, 5, 13),
  (4464, 2, 10, 66, 0, 12, 3, 37, 46, 31, 16),
  (4465, 0, 48, 44, 15, 14, 0, 54, 35, 18, 14),
  (4466, 0, 29, 12, 59, 17, 0, 29, 40, 45, 17),
  (4467, 0, 7, 47, 47, 17, 0, 31, 59, 5, 13),
  (4468, 0, 48, 20, 42, 16, 1, 29, 59, 12, 14),
  (4469, 0, 14, 57, 32, 16, 0, 41, 48, 22, 15),
  (4470, 0, 1, 62, 25, 15, 0, 22, 55, 31, 16),
  (4471, 1, 0, 62, 25, 15, 1, 8, 66, 7, 13),
  (4472, 0, 44, 6, 50, 16, 0, 52, 42, 2, 12),
  (4473, 0, 40, 52, 13, 14, 0, 58, 25, 22, 14),
  (4474, 0, 21, 8, 63, 17, 1, 4, 10, 66, 17),
  (4475, 0, 27, 61, 5, 13, 0, 35, 21, 53, 17),
  (4476, 3, 20, 47, 43, 17, 5, 41, 51, 12, 14),
  (4477, 0, 42, 3, 52, 16, 0, 48, 18, 43, 16),
  (4478, 0, 2, 57, 35, 16, 0, 33, 58, 5, 13),
  (4479, 1, 11, 66, 0, 12, 3, 26, 8, 61, 17),
  (4480, 0, 48, 24, 40, 16, 1, 22, 63, 5, 13),
  (4481, 0, 5, 10, 66, 17, 0, 33, 16, 56, 17),
  (4482, 0, 21, 60, 21, 15, 1, 48, 40, 24, 15),
  (4483, 1, 2, 11, 66, 17, 1, 36, 28, 49, 17),
  (4484, 1, 1, 65, 16, 14, 1, 33, 57, 12, 14),
  (4485, 0, 2, 65, 16, 14, 0, 32, 50, 31, 16),
  (4486, 0, 3, 11, 66, 17, 0, 6, 65, 15, 14),
  (4487, 3, 8, 7, 66, 17, 3, 9, 58, 32, 16),
  (4488, 1, 18, 61, 21, 15, 1, 38, 51, 21, 15),
  (4489, 2, 0, 65, 16, 14, 2, 52, 39, 16, 14),
  (4490, 0, 23, 45, 44, 17, 0, 35, 31, 48, 17),
  (4491, 0, 59, 29, 13, 13, 2, 33, 37, 45, 17),
  (4492, 1, 15, 64, 13, 14, 1, 25, 61, 12, 14),
  (4493, 0, 21, 46, 44, 17, 0, 38, 45, 32, 16),
  (4494, 0, 25, 62, 5, 13, 0, 31, 13, 58, 17),
  (4495, 1, 32, 38, 45, 17, 3, 0, 11, 66, 17),
  (4496, 0, 48, 16, 44, 16, 0, 64, 0, 20, 12),
  (4497, 0, 2, 67, 2, 12, 0, 13, 62, 22, 15),
  (4498, 0, 13, 48, 45, 17, 1, 16, 48, 44, 17),
  (4499, 0, 15, 7, 65, 17, 0, 35, 57, 5, 13)
  ]

lemma witChunk_85_ok : witChunk_85.all checkWit = true := by
  decide +kernel

lemma witChunk_85_ns :
    witChunk_85.map (fun t => t.1) = (List.range 50).map (· + 4450) := by
  decide +kernel

def witChunk_86 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4500, 0, 12, 66, 0, 12, 2, 26, 54, 30, 16),
  (4501, 0, 1, 12, 66, 17, 0, 9, 8, 66, 17),
  (4502, 0, 35, 19, 54, 17, 0, 51, 35, 26, 15),
  (4503, 3, 49, 22, 40, 16, 3, 50, 44, 7, 13),
  (4504, 1, 7, 58, 33, 16, 1, 9, 65, 14, 14),
  (4505, 2, 31, 40, 44, 17, 2, 31, 56, 20, 15),
  (4506, 0, 19, 7, 64, 17, 0, 19, 47, 44, 17),
  (4507, 0, 31, 39, 45, 17, 0, 63, 23, 3, 11),
  (4508, 3, 8, 49, 45, 17, 3, 41, 0, 53, 16),
  (4509, 2, 24, 55, 30, 16, 2, 54, 36, 17, 14),
  (4510, 2, 47, 42, 23, 15, 3, 10, 6, 66, 17),
  (4511, 1, 11, 58, 32, 16, 1, 66, 3, 12, 11),
  (4512, 2, 30, 52, 30, 16, 2, 38, 54, 12, 14),
  (4513, 2, 60, 11, 28, 14, 4, 60, 16, 25, 14),
  (4514, 0, 27, 43, 44, 17, 0, 37, 52, 21, 15),
  (4515, 0, 55, 11, 37, 15, 0, 55, 23, 31, 15),
  (4516, 0, 40, 0, 54, 16, 1, 65, 17, 0, 10),
  (4517, 0, 8, 58, 33, 16, 0, 46, 49, 0, 12),
  (4518, 0, 1, 46, 49, 17, 0, 34, 49, 31, 16),
  (4519, 1, 0, 46, 49, 17, 1, 2, 47, 48, 17),
  (4520, 1, 43, 50, 13, 14, 1, 47, 10, 47, 16),
  (4521, 0, 10, 65, 14, 14, 0, 16, 64, 13, 14),
  (4522, 0, 3, 47, 48, 17, 0, 61, 24, 15, 13),
  (4523, 0, 19, 61, 21, 15, 0, 23, 63, 5, 13),
  (4524, 3, 16, 5, 65, 17, 3, 16, 49, 43, 17),
  (4525, 0, 30, 59, 12, 14, 0, 48, 14, 45, 16),
  (4526, 0, 6, 67, 1, 12, 0, 11, 7, 66, 17),
  (4527, 3, 32, 11, 58, 17, 3, 42, 48, 21, 15),
  (4528, 0, 28, 60, 12, 14, 0, 60, 12, 28, 14),
  (4529, 0, 17, 48, 44, 17, 0, 66, 13, 2, 10),
  (4530, 0, 37, 56, 5, 13, 2, 3, 48, 47, 17),
  (4531, 0, 27, 9, 61, 17, 0, 63, 11, 21, 13),
  (4532, 0, 12, 58, 32, 16, 0, 32, 58, 12, 14),
  (4533, 0, 25, 8, 62, 17, 0, 62, 25, 8, 12),
  (4534, 0, 18, 57, 31, 16, 0, 33, 14, 57, 17),
  (4535, 1, 14, 49, 44, 17, 3, 2, 48, 47, 17),
  (4536, 0, 4, 58, 34, 16, 0, 44, 38, 34, 16),
  (4537, 2, 23, 60, 20, 15, 4, 25, 6, 62, 17),
  (4538, 0, 5, 48, 47, 17, 0, 63, 13, 20, 13),
  (4539, 0, 35, 17, 55, 17, 3, 1, 58, 34, 16),
  (4540, 1, 37, 55, 12, 14, 1, 43, 40, 33, 16),
  (4541, 0, 26, 61, 12, 14, 0, 29, 10, 60, 17),
  (4542, 0, 43, 47, 22, 15, 2, 9, 63, 22, 15),
  (4543, 1, 16, 62, 21, 15, 1, 24, 46, 43, 17),
  (4544, 1, 22, 47, 43, 17, 1, 65, 11, 14, 12),
  (4545, 0, 37, 26, 50, 17, 2, 60, 19, 24, 14),
  (4546, 0, 37, 24, 51, 17, 2, 12, 65, 13, 14),
  (4547, 0, 7, 63, 23, 15, 0, 11, 49, 45, 17),
  (4548, 3, 56, 13, 35, 15, 3, 65, 4, 17, 12),
  (4549, 0, 34, 57, 12, 14, 0, 60, 18, 25, 14)
  ]

lemma witChunk_86_ok : witChunk_86.all checkWit = true := by
  decide +kernel

lemma witChunk_86_ns :
    witChunk_86.map (fun t => t.1) = (List.range 50).map (· + 4500) := by
  decide +kernel

def witChunk_87 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4550, 0, 17, 6, 65, 17, 0, 55, 9, 38, 15),
  (4551, 1, 2, 63, 24, 15, 1, 30, 57, 20, 15),
  (4552, 1, 15, 58, 31, 16, 1, 25, 55, 30, 16),
  (4553, 0, 44, 4, 51, 16, 4, 37, 56, 4, 13),
  (4554, 0, 3, 63, 24, 15, 0, 37, 28, 49, 17),
  (4555, 0, 63, 15, 19, 13, 1, 6, 49, 46, 17),
  (4556, 1, 21, 63, 12, 14, 1, 41, 43, 32, 16),
  (4557, 0, 37, 22, 52, 17, 2, 20, 57, 30, 16),
  (4558, 0, 33, 38, 45, 17, 2, 13, 5, 66, 17),
  (4559, 1, 2, 67, 8, 13, 1, 26, 59, 20, 15),
  (4560, 0, 40, 44, 32, 16, 0, 52, 40, 16, 14),
  (4561, 0, 13, 6, 66, 17, 0, 13, 66, 6, 13),
  (4562, 0, 3, 67, 8, 13, 0, 15, 49, 44, 17),
  (4563, 0, 31, 11, 59, 17, 0, 39, 51, 21, 15),
  (4564, 0, 24, 62, 12, 14, 0, 48, 12, 46, 16),
  (4565, 1, 13, 65, 13, 14, 1, 65, 13, 13, 12),
  (4566, 0, 7, 49, 46, 17, 0, 35, 35, 46, 17),
  (4567, 1, 23, 56, 30, 16, 1, 31, 52, 30, 16),
  (4568, 3, 55, 39, 2, 12, 4, 60, 6, 30, 14),
  (4569, 2, 48, 31, 36, 16, 2, 63, 4, 24, 13),
  (4570, 0, 63, 5, 24, 13, 1, 36, 34, 46, 17),
  (4571, 0, 39, 55, 5, 13, 1, 4, 8, 67, 17),
  (4572, 1, 9, 67, 0, 12, 2, 18, 64, 12, 14),
  (4573, 0, 21, 6, 64, 17, 0, 37, 30, 48, 17),
  (4574, 0, 11, 63, 22, 15, 0, 17, 62, 21, 15),
  (4575, 3, 2, 8, 67, 17, 5, 12, 66, 5, 13),
  (4576, 0, 36, 56, 12, 14, 0, 60, 20, 24, 14),
  (4577, 0, 49, 40, 24, 15, 0, 53, 2, 42, 15),
  (4578, 0, 5, 8, 67, 17, 0, 31, 41, 44, 17),
  (4579, 0, 3, 9, 67, 17, 1, 14, 5, 66, 17),
  (4580, 3, 29, 60, 11, 14, 3, 44, 51, 5, 13),
  (4581, 0, 16, 58, 31, 16, 2, 42, 0, 53, 16),
  (4582, 0, 63, 17, 18, 13, 0, 66, 15, 1, 10),
  (4583, 1, 24, 6, 63, 17, 1, 30, 9, 60, 17),
  (4584, 5, 45, 3, 50, 16, 5, 57, 31, 18, 14),
  (4585, 2, 31, 60, 4, 13, 4, 17, 50, 42, 17),
  (4586, 0, 35, 15, 56, 17, 0, 59, 31, 12, 13),
  (4587, 0, 7, 7, 67, 17, 0, 7, 67, 7, 13),
  (4588, 1, 9, 59, 32, 16, 1, 53, 39, 16, 14),
  (4589, 0, 0, 58, 35, 16, 0, 10, 67, 0, 12),
  (4590, 0, 1, 10, 67, 17, 0, 14, 65, 13, 14),
  (4591, 1, 0, 10, 67, 17, 1, 8, 6, 67, 17),
  (4592, 1, 3, 66, 15, 14, 1, 21, 57, 30, 16),
  (4593, 0, 61, 26, 14, 13, 2, 2, 66, 15, 14),
  (4594, 0, 21, 48, 43, 17, 2, 4, 59, 33, 16),
  (4595, 0, 51, 37, 25, 15, 0, 55, 7, 39, 15),
  (4596, 0, 64, 20, 10, 12, 1, 65, 15, 12, 12),
  (4597, 0, 4, 66, 15, 14, 0, 22, 63, 12, 14),
  (4598, 0, 63, 25, 2, 11, 3, 54, 40, 8, 13),
  (4599, 1, 48, 42, 23, 15, 1, 50, 39, 24, 15)
  ]

lemma witChunk_87_ok : witChunk_87.all checkWit = true := by
  decide +kernel

lemma witChunk_87_ns :
    witChunk_87.map (fun t => t.1) = (List.range 50).map (· + 4550) := by
  decide +kernel

def witChunk_88 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4600, 0, 28, 54, 30, 16, 1, 30, 43, 43, 17),
  (4601, 0, 26, 55, 30, 16, 0, 54, 41, 2, 12),
  (4602, 0, 37, 32, 47, 17, 2, 43, 48, 21, 15),
  (4603, 0, 27, 45, 43, 17, 0, 63, 3, 25, 13),
  (4604, 3, 32, 9, 59, 17, 3, 44, 47, 21, 15),
  (4605, 0, 10, 59, 32, 16, 0, 13, 50, 44, 17),
  (4606, 0, 6, 59, 33, 16, 0, 9, 6, 67, 17),
  (4607, 1, 16, 50, 43, 17, 1, 22, 5, 64, 17),
  (4608, 0, 48, 48, 0, 12, 1, 14, 63, 21, 15),
  (4609, 0, 1, 48, 48, 17, 0, 30, 53, 30, 16),
  (4610, 0, 27, 59, 20, 15, 0, 31, 57, 20, 15),
  (4611, 0, 19, 5, 65, 17, 0, 19, 49, 43, 17),
  (4612, 0, 0, 66, 16, 14, 0, 24, 56, 30, 16),
  (4613, 0, 38, 55, 12, 14, 0, 48, 10, 47, 16),
  (4614, 0, 38, 47, 31, 16, 1, 36, 54, 20, 15),
  (4615, 1, 34, 39, 44, 17, 3, 49, 30, 36, 16),
  (4616, 0, 8, 66, 14, 14, 0, 48, 46, 14, 14),
  (4617, 2, 27, 6, 62, 17, 2, 27, 46, 42, 17),
  (4618, 2, 25, 63, 4, 13, 2, 52, 41, 15, 14),
  (4619, 0, 3, 49, 47, 17, 0, 35, 37, 45, 17),
  (4620, 2, 42, 52, 12, 14, 2, 66, 16, 0, 10),
  (4621, 0, 61, 30, 0, 11, 1, 61, 13, 27, 14),
  (4622, 0, 27, 7, 62, 17, 0, 41, 50, 21, 15),
  (4623, 3, 10, 4, 67, 17, 3, 34, 40, 43, 17),
  (4624, 0, 48, 32, 36, 16, 1, 49, 45, 14, 14),
  (4625, 0, 25, 60, 20, 15, 0, 33, 40, 44, 17),
  (4626, 0, 29, 8, 61, 17, 0, 29, 44, 43, 17),
  (4627, 0, 55, 39, 9, 13, 1, 10, 67, 6, 13),
  (4628, 0, 0, 68, 2, 12, 0, 32, 52, 30, 16),
  (4629, 0, 50, 23, 40, 16, 1, 57, 37, 3, 12),
  (4630, 0, 25, 6, 63, 17, 1, 16, 4, 66, 17),
  (4631, 1, 55, 40, 2, 12, 5, 20, 50, 41, 17),
  (4632, 3, 67, 11, 2, 10, 5, 46, 45, 21, 15),
  (4633, 0, 22, 57, 30, 16, 2, 3, 50, 46, 17),
  (4634, 1, 4, 50, 46, 17, 1, 68, 2, 2, 9),
  (4635, 0, 11, 5, 67, 17, 0, 15, 63, 21, 15),
  (4636, 1, 3, 68, 1, 12, 1, 41, 53, 12, 14),
  (4637, 0, 42, 43, 32, 16, 0, 53, 42, 8, 13),
  (4638, 0, 14, 59, 31, 16, 0, 17, 50, 43, 17),
  (4639, 1, 10, 51, 44, 17, 1, 16, 66, 5, 13),
  (4640, 0, 20, 64, 12, 14, 0, 60, 4, 32, 14),
  (4641, 0, 2, 59, 34, 16, 0, 4, 68, 1, 12),
  (4642, 0, 31, 9, 60, 17, 0, 67, 3, 12, 11),
  (4643, 0, 35, 13, 57, 17, 1, 4, 64, 23, 15),
  (4644, 0, 44, 2, 52, 16, 3, 1, 68, 1, 12),
  (4645, 0, 57, 36, 10, 13, 0, 66, 17, 0, 10),
  (4646, 0, 11, 67, 6, 13, 0, 39, 25, 50, 17),
  (4647, 3, 2, 64, 23, 15, 3, 40, 23, 50, 17),
  (4648, 1, 11, 66, 13, 14, 1, 14, 51, 43, 17),
  (4649, 0, 60, 32, 5, 12, 2, 23, 4, 64, 17)
  ]

lemma witChunk_88_ok : witChunk_88.all checkWit = true := by
  decide +kernel

lemma witChunk_88_ns :
    witChunk_88.map (fun t => t.1) = (List.range 50).map (· + 4600) := by
  decide +kernel

def witChunk_89 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4650, 0, 5, 64, 23, 15, 0, 23, 5, 64, 17),
  (4651, 0, 39, 23, 51, 17, 0, 39, 27, 49, 17),
  (4652, 3, 20, 3, 65, 17, 3, 32, 57, 19, 15),
  (4653, 2, 63, 0, 26, 13, 2, 66, 8, 15, 12),
  (4654, 2, 49, 47, 6, 13, 2, 63, 26, 1, 11),
  (4655, 1, 34, 59, 4, 13, 1, 38, 53, 20, 15),
  (4656, 2, 38, 48, 30, 16, 2, 66, 6, 16, 12),
  (4657, 0, 34, 51, 30, 16, 2, 46, 38, 33, 16),
  (4658, 0, 11, 51, 44, 17, 0, 53, 0, 43, 15),
  (4659, 0, 31, 43, 43, 17, 0, 67, 1, 13, 11),
  (4660, 0, 40, 54, 12, 14, 0, 60, 24, 22, 14),
  (4661, 0, 9, 64, 22, 15, 0, 17, 4, 66, 17),
  (4662, 0, 57, 18, 33, 15, 0, 66, 9, 15, 12),
  (4663, 1, 26, 63, 4, 13, 1, 47, 36, 34, 16),
  (4664, 0, 20, 58, 30, 16, 1, 6, 51, 45, 17),
  (4665, 2, 30, 54, 29, 16, 2, 48, 7, 48, 16),
  (4666, 0, 39, 21, 52, 17, 0, 39, 29, 48, 17),
  (4667, 1, 44, 52, 5, 13, 1, 59, 28, 20, 14),
  (4668, 2, 6, 60, 32, 16, 2, 6, 68, 0, 12),
  (4669, 0, 12, 66, 13, 14, 1, 41, 45, 31, 16),
  (4670, 0, 17, 66, 5, 13, 0, 33, 10, 59, 17),
  (4671, 3, 10, 52, 43, 17, 3, 28, 5, 62, 17),
  (4672, 0, 48, 8, 48, 16, 1, 17, 59, 30, 16),
  (4673, 0, 1, 64, 24, 15, 0, 50, 27, 38, 16),
  (4674, 0, 13, 4, 67, 17, 0, 61, 28, 13, 13),
  (4675, 0, 7, 51, 45, 17, 0, 15, 51, 43, 17),
  (4676, 0, 68, 4, 6, 10, 3, 12, 67, 5, 13),
  (4677, 0, 40, 46, 31, 16, 0, 68, 2, 7, 10),
  (4678, 1, 4, 6, 68, 17, 1, 36, 38, 44, 17),
  (4679, 1, 2, 7, 68, 17, 1, 40, 26, 49, 17),
  (4680, 5, 2, 51, 45, 17, 5, 30, 61, 3, 13),
  (4681, 2, 39, 56, 4, 13, 4, 17, 2, 66, 17),
  (4682, 0, 3, 7, 68, 17, 0, 21, 4, 65, 17),
  (4683, 0, 43, 53, 5, 13, 1, 12, 64, 21, 15),
  (4684, 1, 11, 60, 31, 16, 1, 31, 60, 11, 14),
  (4685, 0, 5, 6, 68, 17, 0, 21, 62, 20, 15),
  (4686, 0, 46, 49, 13, 14, 0, 58, 31, 19, 14),
  (4687, 1, 6, 5, 68, 17, 1, 40, 22, 51, 17),
  (4688, 0, 8, 60, 32, 16, 0, 8, 68, 0, 12),
  (4689, 0, 1, 8, 68, 17, 0, 1, 68, 8, 13),
  (4690, 0, 37, 36, 45, 17, 1, 0, 8, 68, 17),
  (4691, 0, 39, 19, 53, 17, 0, 39, 31, 47, 17),
  (4692, 2, 66, 2, 18, 12, 3, 28, 47, 41, 17),
  (4693, 0, 18, 65, 12, 14, 0, 25, 48, 42, 17),
  (4694, 0, 23, 49, 42, 17, 0, 49, 42, 23, 15),
  (4695, 1, 18, 63, 20, 15, 1, 56, 6, 39, 15),
  (4696, 0, 36, 50, 30, 16, 1, 14, 3, 67, 17),
  (4697, 2, 7, 4, 68, 17, 2, 7, 52, 44, 17),
  (4698, 0, 5, 68, 7, 13, 0, 7, 5, 68, 17),
  (4699, 0, 63, 27, 1, 11, 1, 12, 52, 43, 17)
  ]

lemma witChunk_89_ok : witChunk_89.all checkWit = true := by
  decide +kernel

lemma witChunk_89_ns :
    witChunk_89.map (fun t => t.1) = (List.range 50).map (· + 4650) := by
  decide +kernel

def witChunk_90 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4700, 1, 3, 60, 33, 16, 1, 51, 24, 39, 16),
  (4701, 0, 29, 62, 4, 13, 0, 37, 14, 56, 17),
  (4702, 0, 27, 47, 42, 17, 0, 33, 42, 43, 17),
  (4703, 5, 2, 5, 68, 17, 7, 37, 56, 10, 14),
  (4704, 0, 68, 8, 4, 10, 2, 14, 60, 30, 16),
  (4705, 0, 4, 60, 33, 16, 0, 12, 60, 31, 16),
  (4706, 0, 13, 64, 21, 15, 1, 8, 4, 68, 17),
  (4707, 0, 67, 13, 7, 11, 2, 33, 57, 19, 15),
  (4708, 1, 27, 56, 29, 16, 1, 51, 16, 43, 16),
  (4709, 0, 50, 47, 0, 12, 1, 29, 55, 29, 16),
  (4710, 0, 1, 50, 47, 17, 0, 35, 11, 58, 17),
  (4711, 1, 0, 50, 47, 17, 1, 38, 57, 4, 13),
  (4712, 1, 5, 67, 14, 14, 1, 14, 67, 5, 13),
  (4713, 2, 60, 33, 4, 12, 4, 53, 36, 24, 15),
  (4714, 0, 27, 63, 4, 13, 2, 61, 29, 12, 13),
  (4715, 0, 55, 3, 41, 15, 0, 55, 31, 27, 15),
  (4716, 3, 40, 17, 53, 17, 3, 61, 4, 31, 14),
  (4717, 0, 42, 53, 12, 14, 0, 60, 26, 21, 14),
  (4718, 0, 2, 67, 15, 14, 0, 47, 45, 22, 15),
  (4719, 1, 51, 46, 0, 12, 3, 34, 8, 59, 17),
  (4720, 1, 22, 3, 65, 17, 1, 31, 54, 29, 16),
  (4721, 0, 6, 67, 14, 14, 0, 9, 4, 68, 17),
  (4722, 0, 13, 52, 43, 17, 0, 35, 59, 4, 13),
  (4723, 0, 15, 3, 67, 17, 0, 27, 5, 63, 17),
  (4724, 0, 44, 42, 32, 16, 2, 50, 10, 46, 16),
  (4725, 0, 57, 24, 30, 15, 0, 66, 15, 12, 12),
  (4726, 0, 3, 51, 46, 17, 0, 19, 3, 66, 17),
  (4727, 1, 15, 60, 30, 16, 1, 15, 66, 12, 14),
  (4728, 3, 37, 50, 29, 16, 5, 58, 15, 33, 15),
  (4729, 2, 15, 64, 20, 15, 2, 19, 2, 66, 17),
  (4730, 0, 19, 63, 20, 15, 0, 39, 53, 20, 15),
  (4731, 0, 31, 7, 61, 17, 2, 21, 51, 41, 17),
  (4732, 1, 45, 1, 52, 16, 1, 45, 41, 32, 16),
  (4733, 0, 68, 10, 3, 10, 2, 55, 32, 26, 15),
  (4734, 3, 58, 14, 34, 15, 4, 66, 15, 11, 12),
  (4735, 1, 10, 3, 68, 17, 1, 40, 18, 53, 17),
  (4736, 0, 64, 24, 8, 12, 1, 23, 58, 29, 16),
  (4737, 0, 25, 4, 64, 17, 0, 25, 64, 4, 13),
  (4738, 2, 25, 3, 64, 17, 2, 48, 5, 49, 16),
  (4739, 0, 15, 67, 5, 13, 2, 29, 47, 41, 17),
  (4740, 0, 56, 40, 2, 12, 3, 8, 53, 43, 17),
  (4741, 0, 9, 68, 6, 13, 0, 48, 6, 49, 16),
  (4742, 0, 30, 61, 11, 14, 0, 58, 37, 3, 12),
  (4743, 3, 4, 65, 22, 15, 3, 58, 20, 31, 15),
  (4744, 1, 30, 59, 19, 15, 1, 46, 51, 5, 13),
  (4745, 0, 32, 60, 11, 14, 0, 38, 49, 30, 16),
  (4746, 2, 3, 52, 45, 17, 2, 33, 7, 60, 17),
  (4747, 1, 4, 52, 45, 17, 1, 6, 65, 22, 15),
  (4748, 1, 23, 64, 11, 14, 1, 43, 44, 31, 16),
  (4749, 0, 28, 62, 11, 14, 0, 37, 38, 44, 17)
  ]

lemma witChunk_90_ok : witChunk_90.all checkWit = true := by
  decide +kernel

lemma witChunk_90_ns :
    witChunk_90.map (fun t => t.1) = (List.range 50).map (· + 4700) := by
  decide +kernel

def witChunk_91 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4750, 0, 31, 45, 42, 17, 0, 42, 45, 31, 16),
  (4751, 1, 16, 2, 67, 17, 1, 32, 58, 19, 15),
  (4752, 2, 62, 18, 24, 14, 3, 63, 27, 6, 12),
  (4753, 0, 33, 8, 60, 17, 2, 52, 21, 40, 16),
  (4754, 0, 5, 52, 45, 17, 0, 11, 3, 68, 17),
  (4755, 0, 35, 41, 43, 17, 2, 9, 65, 21, 15),
  (4756, 0, 0, 60, 34, 16, 0, 16, 60, 30, 16),
  (4757, 0, 17, 52, 42, 17, 0, 41, 24, 50, 17),
  (4758, 0, 7, 65, 22, 15, 0, 10, 67, 13, 14),
  (4759, 1, 24, 50, 41, 17, 3, 36, 9, 58, 17),
  (4760, 1, 2, 65, 23, 15, 1, 10, 53, 43, 17),
  (4761, 0, 28, 56, 29, 16, 2, 35, 42, 42, 17),
  (4762, 0, 37, 12, 57, 17, 1, 20, 2, 66, 17),
  (4763, 0, 3, 65, 23, 15, 0, 23, 3, 65, 17),
  (4764, 3, 16, 1, 67, 17, 3, 16, 53, 41, 17),
  (4765, 0, 61, 30, 12, 13, 1, 1, 69, 1, 12),
  (4766, 0, 2, 69, 1, 12, 0, 26, 57, 29, 16),
  (4767, 1, 42, 51, 20, 15, 1, 56, 30, 27, 15),
  (4768, 1, 10, 65, 21, 15, 1, 22, 51, 41, 17),
  (4769, 0, 41, 28, 48, 17, 0, 65, 12, 20, 13),
  (4770, 0, 23, 65, 4, 13, 0, 45, 48, 21, 15),
  (4771, 0, 39, 15, 55, 17, 0, 39, 35, 45, 17),
  (4772, 0, 60, 34, 4, 12, 0, 68, 12, 2, 10),
  (4773, 0, 65, 8, 22, 13, 2, 12, 61, 30, 16),
  (4774, 0, 57, 38, 9, 13, 1, 12, 2, 68, 17),
  (4775, 1, 64, 26, 1, 11, 3, 20, 1, 66, 17),
  (4776, 1, 57, 39, 2, 12, 5, 42, 19, 51, 17),
  (4777, 0, 48, 48, 13, 14, 0, 58, 33, 18, 14),
  (4778, 0, 69, 4, 1, 9, 2, 5, 53, 44, 17),
  (4779, 0, 11, 53, 43, 17, 2, 21, 63, 19, 15),
  (4780, 1, 39, 56, 11, 14, 1, 67, 8, 15, 12),
  (4781, 0, 6, 61, 32, 16, 0, 24, 58, 29, 16),
  (4782, 0, 10, 61, 31, 16, 0, 17, 2, 67, 17),
  (4783, 1, 6, 53, 44, 17, 1, 24, 62, 19, 15),
  (4784, 0, 44, 52, 12, 14, 0, 60, 28, 20, 14),
  (4785, 0, 17, 64, 20, 15, 0, 41, 20, 52, 17),
  (4786, 0, 39, 57, 4, 13, 2, 52, 15, 43, 16),
  (4787, 0, 11, 65, 21, 15, 0, 35, 9, 59, 17),
  (4788, 0, 52, 22, 40, 16, 1, 5, 69, 0, 12),
  (4789, 0, 33, 44, 42, 17, 1, 21, 65, 11, 14),
  (4790, 0, 41, 30, 47, 17, 0, 50, 9, 47, 16),
  (4791, 1, 63, 28, 6, 12, 3, 25, 58, 28, 16),
  (4792, 0, 52, 18, 42, 16, 1, 2, 5, 69, 17),
  (4793, 0, 24, 64, 11, 14, 0, 62, 7, 30, 14),
  (4794, 0, 7, 53, 44, 17, 0, 53, 44, 7, 13),
  (4795, 0, 3, 5, 69, 17, 1, 4, 4, 69, 17),
  (4796, 1, 67, 4, 17, 12, 5, 1, 61, 32, 16),
  (4797, 0, 6, 69, 0, 12, 0, 13, 2, 68, 17),
  (4798, 0, 1, 6, 69, 17, 0, 15, 53, 42, 17),
  (4799, 1, 0, 6, 69, 17, 1, 42, 27, 48, 17)
  ]

lemma witChunk_91_ok : witChunk_91.all checkWit = true := by
  decide +kernel

lemma witChunk_91_ns :
    witChunk_91.map (fun t => t.1) = (List.range 50).map (· + 4750) := by
  decide +kernel

def witChunk_92 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4800, 3, 31, 61, 10, 14, 5, 42, 31, 45, 17),
  (4801, 0, 21, 2, 66, 17, 0, 52, 24, 39, 16),
  (4802, 0, 5, 4, 69, 17, 0, 29, 60, 19, 15),
  (4803, 0, 31, 59, 19, 15, 0, 67, 17, 5, 11),
  (4804, 0, 40, 48, 30, 16, 1, 13, 67, 12, 14),
  (4805, 0, 65, 16, 18, 13, 0, 65, 24, 2, 11),
  (4806, 0, 22, 59, 29, 16, 0, 25, 50, 41, 17),
  (4807, 1, 24, 2, 65, 17, 1, 34, 7, 60, 17),
  (4808, 1, 6, 3, 69, 17, 1, 42, 21, 51, 17),
  (4809, 0, 52, 16, 43, 16, 2, 11, 54, 42, 17),
  (4810, 0, 63, 29, 0, 11, 2, 52, 27, 37, 16),
  (4811, 0, 23, 51, 41, 17, 0, 27, 49, 41, 17),
  (4812, 3, 23, 59, 28, 16, 3, 40, 13, 55, 17),
  (4813, 0, 21, 66, 4, 13, 1, 1, 61, 33, 16),
  (4814, 0, 2, 61, 33, 16, 0, 33, 58, 19, 15),
  (4815, 3, 58, 8, 37, 15, 3, 61, 26, 20, 14),
  (4816, 1, 2, 69, 7, 13, 1, 18, 1, 67, 17),
  (4817, 0, 14, 61, 30, 16, 0, 57, 28, 28, 15),
  (4818, 0, 13, 68, 5, 13, 0, 37, 40, 43, 17),
  (4819, 0, 3, 69, 7, 13, 0, 7, 3, 69, 17),
  (4820, 0, 48, 4, 50, 16, 0, 52, 46, 0, 12),
  (4821, 0, 1, 52, 46, 17, 0, 41, 32, 46, 17),
  (4822, 0, 54, 41, 15, 14, 1, 0, 52, 46, 17),
  (4823, 1, 14, 1, 68, 17, 1, 14, 65, 20, 15),
  (4824, 0, 52, 26, 38, 16, 3, 35, 59, 10, 14),
  (4825, 2, 28, 57, 28, 16, 4, 13, 0, 68, 17),
  (4826, 0, 21, 52, 41, 17, 0, 29, 4, 63, 17),
  (4827, 2, 29, 3, 63, 17, 2, 29, 63, 3, 13),
  (4828, 1, 61, 33, 4, 12, 1, 69, 7, 4, 10),
  (4829, 0, 14, 67, 12, 14, 0, 53, 38, 24, 15),
  (4830, 0, 22, 65, 11, 14, 0, 25, 62, 19, 15),
  (4831, 1, 3, 68, 14, 14, 1, 8, 2, 69, 17),
  (4832, 1, 38, 55, 19, 15, 1, 58, 25, 29, 15),
  (4833, 0, 37, 10, 58, 17, 0, 41, 56, 4, 13),
  (4834, 0, 27, 3, 64, 17, 1, 40, 36, 44, 17),
  (4835, 0, 35, 57, 19, 15, 0, 47, 51, 5, 13),
  (4836, 0, 4, 68, 14, 14, 0, 52, 14, 44, 16),
  (4837, 0, 48, 38, 33, 16, 1, 45, 43, 31, 16),
  (4838, 0, 35, 43, 42, 17, 0, 65, 18, 17, 13),
  (4839, 3, 1, 68, 14, 14, 3, 25, 64, 10, 14),
  (4840, 1, 2, 53, 45, 17, 1, 19, 66, 11, 14),
  (4841, 0, 20, 60, 29, 16, 0, 36, 52, 29, 16),
  (4842, 2, 27, 64, 3, 13, 2, 35, 60, 3, 13),
  (4843, 0, 3, 53, 45, 17, 1, 22, 1, 66, 17),
  (4844, 1, 7, 68, 13, 14, 1, 63, 12, 27, 14),
  (4845, 2, 66, 20, 9, 12, 5, 69, 3, 5, 10),
  (4846, 0, 7, 69, 6, 13, 0, 9, 2, 69, 17),
  (4847, 3, 28, 61, 18, 15, 3, 32, 59, 18, 15),
  (4848, 2, 50, 6, 48, 16, 3, 5, 62, 31, 16),
  (4849, 0, 0, 68, 15, 14, 0, 13, 54, 42, 17)
  ]

lemma witChunk_92_ok : witChunk_92.all checkWit = true := by
  decide +kernel

lemma witChunk_92_ns :
    witChunk_92.map (fun t => t.1) = (List.range 50).map (· + 4800) := by
  decide +kernel

def witChunk_93 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4850, 0, 15, 1, 68, 17, 0, 15, 65, 20, 15),
  (4851, 0, 19, 1, 67, 17, 0, 19, 53, 41, 17),
  (4852, 1, 51, 32, 35, 16, 1, 53, 21, 40, 16),
  (4853, 0, 41, 16, 54, 17, 0, 50, 7, 48, 16),
  (4854, 0, 25, 2, 65, 17, 0, 65, 2, 25, 13),
  (4855, 1, 16, 54, 41, 17, 1, 47, 50, 12, 14),
  (4856, 1, 7, 62, 31, 16, 1, 53, 43, 14, 14),
  (4857, 0, 8, 68, 13, 14, 0, 40, 56, 11, 14),
  (4858, 1, 4, 66, 22, 15, 1, 52, 46, 6, 13),
  (4859, 0, 23, 63, 19, 15, 0, 47, 47, 21, 15),
  (4860, 2, 54, 44, 0, 12, 3, 16, 65, 19, 15),
  (4861, 0, 46, 51, 12, 14, 0, 60, 30, 19, 14),
  (4862, 0, 41, 34, 45, 17, 0, 59, 15, 34, 15),
  (4863, 1, 8, 66, 21, 15, 1, 48, 46, 21, 15),
  (4864, 1, 10, 1, 69, 17, 1, 34, 45, 41, 17),
  (4865, 0, 5, 66, 22, 15, 0, 57, 4, 40, 15),
  (4866, 0, 19, 67, 4, 13, 0, 37, 56, 19, 15),
  (4867, 0, 63, 27, 13, 13, 1, 11, 62, 30, 16),
  (4868, 1, 67, 16, 11, 12, 3, 8, 69, 5, 13),
  (4869, 0, 8, 62, 31, 16, 2, 3, 54, 44, 17),
  (4870, 1, 4, 54, 44, 17, 1, 44, 54, 4, 13),
  (4871, 1, 63, 18, 24, 14, 3, 8, 55, 42, 17),
  (4872, 3, 13, 62, 29, 16, 3, 23, 65, 10, 14),
  (4873, 0, 42, 47, 30, 16, 0, 52, 12, 45, 16),
  (4874, 0, 35, 7, 60, 17, 2, 16, 67, 11, 14),
  (4875, 0, 43, 25, 49, 17, 0, 55, 35, 25, 15),
  (4876, 1, 29, 57, 28, 16, 1, 51, 8, 47, 16),
  (4877, 0, 5, 54, 44, 17, 0, 20, 66, 11, 14),
  (4878, 0, 9, 66, 21, 15, 0, 43, 23, 50, 17),
  (4879, 1, 3, 62, 32, 16, 1, 26, 51, 40, 17),
  (4880, 0, 68, 16, 0, 10, 1, 30, 3, 63, 17),
  (4881, 0, 50, 35, 34, 16, 0, 65, 20, 16, 13),
  (4882, 0, 43, 27, 48, 17, 1, 16, 0, 68, 17),
  (4883, 0, 11, 1, 69, 17, 0, 59, 21, 31, 15),
  (4884, 0, 4, 62, 32, 16, 2, 54, 42, 14, 14),
  (4885, 1, 53, 15, 43, 16, 2, 11, 66, 20, 15),
  (4886, 0, 1, 66, 23, 15, 0, 17, 54, 41, 17),
  (4887, 1, 0, 66, 23, 15, 3, 1, 62, 32, 16),
  (4888, 0, 12, 62, 30, 16, 1, 10, 69, 5, 13),
  (4889, 0, 58, 39, 2, 12, 2, 14, 62, 29, 16),
  (4890, 0, 43, 55, 4, 13, 2, 11, 0, 69, 17),
  (4891, 0, 39, 11, 57, 17, 0, 39, 39, 43, 17),
  (4892, 1, 25, 59, 28, 16, 2, 62, 32, 4, 12),
  (4893, 2, 23, 0, 66, 17, 2, 31, 60, 18, 15),
  (4894, 2, 29, 61, 18, 15, 2, 57, 31, 26, 15),
  (4895, 1, 22, 53, 40, 17, 1, 40, 38, 43, 17),
  (4896, 1, 63, 30, 5, 12, 3, 67, 17, 10, 12),
  (4897, 0, 37, 42, 42, 17, 0, 69, 6, 10, 11),
  (4898, 0, 21, 64, 19, 15, 0, 59, 11, 36, 15),
  (4899, 0, 43, 29, 47, 17, 2, 65, 21, 15, 13)
  ]

lemma witChunk_93_ok : witChunk_93.all checkWit = true := by
  decide +kernel

lemma witChunk_93_ns :
    witChunk_93.map (fun t => t.1) = (List.range 50).map (· + 4850) := by
  decide +kernel

def witChunk_94 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4900, 0, 52, 30, 36, 16, 1, 33, 55, 28, 16),
  (4901, 0, 0, 70, 1, 12, 0, 56, 42, 1, 12),
  (4902, 0, 41, 14, 55, 17, 0, 65, 26, 1, 11),
  (4903, 1, 30, 49, 40, 17, 3, 40, 39, 42, 17),
  (4904, 1, 14, 55, 41, 17, 1, 26, 1, 65, 17),
  (4905, 0, 60, 36, 3, 12, 2, 27, 62, 18, 15),
  (4906, 0, 69, 8, 9, 11, 2, 33, 47, 40, 17),
  (4907, 0, 11, 69, 5, 13, 0, 39, 55, 19, 15),
  (4908, 3, 4, 55, 43, 17, 3, 64, 25, 13, 13),
  (4909, 0, 48, 2, 51, 16, 0, 69, 2, 12, 11),
  (4910, 0, 11, 55, 42, 17, 0, 42, 55, 11, 14),
  (4911, 1, 3, 70, 0, 12, 3, 34, 4, 61, 17),
  (4912, 0, 12, 68, 12, 14, 1, 6, 55, 43, 17),
  (4913, 0, 17, 0, 68, 17, 0, 41, 36, 44, 17),
  (4914, 0, 37, 8, 59, 17, 0, 43, 19, 52, 17),
  (4915, 1, 2, 3, 70, 17, 1, 23, 60, 28, 16),
  (4916, 0, 4, 70, 0, 12, 0, 64, 28, 6, 12),
  (4917, 0, 1, 4, 70, 17, 2, 42, 48, 29, 16),
  (4918, 0, 3, 3, 70, 17, 1, 0, 4, 70, 17),
  (4919, 1, 46, 49, 20, 15, 1, 56, 34, 25, 15),
  (4920, 0, 52, 10, 46, 16, 0, 68, 10, 14, 12),
  (4921, 2, 3, 2, 70, 17, 2, 35, 58, 18, 15),
  (4922, 1, 4, 2, 70, 17, 1, 44, 22, 50, 17),
  (4923, 0, 7, 55, 43, 17, 0, 55, 43, 7, 13),
  (4924, 2, 54, 20, 40, 16, 2, 58, 36, 16, 14),
  (4925, 0, 13, 66, 20, 15, 0, 45, 50, 20, 15),
  (4926, 0, 43, 31, 46, 17, 0, 46, 43, 31, 16),
  (4927, 1, 27, 64, 10, 14, 1, 35, 54, 28, 16),
  (4928, 0, 48, 40, 32, 16, 1, 50, 49, 5, 13),
  (4929, 0, 5, 2, 70, 17, 0, 17, 68, 4, 13),
  (4930, 0, 13, 0, 69, 17, 0, 21, 0, 67, 17),
  (4931, 0, 15, 55, 41, 17, 0, 35, 45, 41, 17),
  (4932, 0, 28, 58, 28, 16, 3, 13, 32, 61, 18),
  (4933, 0, 0, 62, 33, 16, 0, 30, 57, 28, 16),
  (4934, 0, 18, 67, 11, 14, 0, 51, 43, 22, 15),
  (4935, 3, 4, 1, 70, 17, 3, 10, 56, 41, 17),
  (4936, 1, 38, 59, 3, 13, 1, 42, 53, 19, 15),
  (4937, 0, 68, 12, 13, 12, 2, 47, 52, 4, 13),
  (4938, 0, 23, 53, 40, 17, 0, 53, 40, 23, 15),
  (4939, 0, 31, 3, 63, 17, 0, 31, 63, 3, 13),
  (4940, 2, 38, 52, 28, 16, 3, 13, 28, 63, 18),
  (4941, 0, 16, 62, 29, 16, 0, 26, 59, 28, 16),
  (4942, 0, 1, 54, 45, 17, 0, 33, 62, 3, 13),
  (4943, 1, 0, 54, 45, 17, 1, 24, 66, 3, 13),
  (4944, 0, 32, 56, 28, 16, 2, 54, 16, 42, 16),
  (4945, 0, 70, 3, 6, 10, 2, 68, 13, 12, 12),
  (4946, 0, 29, 64, 3, 13, 2, 11, 56, 41, 17),
  (4947, 0, 19, 65, 19, 15, 0, 43, 17, 53, 17),
  (4948, 0, 48, 50, 12, 14, 0, 60, 32, 18, 14),
  (4949, 0, 33, 4, 62, 17, 0, 57, 32, 26, 15)
  ]

lemma witChunk_94_ok : witChunk_94.all checkWit = true := by
  decide +kernel

lemma witChunk_94_ns :
    witChunk_94.map (fun t => t.1) = (List.range 50).map (· + 4900) := by
  decide +kernel

def witChunk_95 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (4950, 0, 1, 70, 7, 13, 0, 7, 1, 70, 17),
  (4951, 1, 0, 70, 7, 13, 1, 18, 55, 40, 17),
  (4952, 0, 44, 46, 30, 16, 0, 68, 2, 18, 12),
  (4953, 0, 52, 32, 35, 16, 2, 3, 70, 6, 13),
  (4954, 0, 63, 29, 12, 13, 0, 69, 12, 7, 11),
  (4955, 0, 27, 1, 65, 17, 0, 35, 61, 3, 13),
  (4956, 2, 18, 32, 60, 18, 2, 50, 48, 12, 14),
  (4957, 0, 21, 54, 40, 17, 0, 45, 54, 4, 13),
  (4958, 0, 41, 54, 19, 15, 0, 49, 46, 21, 15),
  (4959, 3, 13, 26, 64, 18, 3, 21, 30, 60, 18),
  (4960, 0, 24, 60, 28, 16, 1, 1, 69, 14, 14),
  (4961, 0, 2, 69, 14, 14, 0, 5, 70, 6, 13),
  (4962, 0, 31, 49, 40, 17, 2, 12, 29, 63, 18),
  (4963, 0, 27, 65, 3, 13, 0, 43, 33, 45, 17),
  (4964, 0, 68, 14, 12, 12, 1, 37, 53, 28, 16),
  (4965, 0, 34, 55, 28, 16, 0, 70, 7, 4, 10),
  (4966, 0, 6, 63, 31, 16, 0, 6, 69, 13, 14),
  (4967, 1, 2, 55, 44, 17, 1, 34, 47, 40, 17),
  (4968, 0, 32, 62, 10, 14, 0, 64, 14, 26, 14),
  (4969, 0, 10, 63, 30, 16, 0, 30, 63, 10, 14),
  (4970, 0, 3, 55, 44, 17, 0, 55, 37, 24, 15),
  (4971, 0, 35, 5, 61, 17, 1, 15, 30, 62, 18),
  (4972, 1, 15, 32, 61, 18, 1, 15, 68, 11, 14),
  (4973, 0, 44, 54, 11, 14, 0, 62, 27, 20, 14),
  (4974, 0, 41, 38, 43, 17, 0, 59, 7, 38, 15),
  (4975, 1, 14, 69, 4, 13, 1, 16, 66, 19, 15),
  (4976, 1, 13, 31, 62, 18, 1, 17, 29, 62, 18),
  (4977, 0, 34, 61, 10, 14, 0, 52, 8, 47, 16),
  (4978, 0, 37, 60, 3, 13, 2, 9, 67, 20, 15),
  (4979, 0, 7, 67, 21, 15, 1, 2, 67, 22, 15),
  (4980, 0, 28, 64, 10, 14, 0, 64, 10, 28, 14),
  (4981, 0, 9, 0, 70, 17, 0, 9, 56, 42, 17),
  (4982, 0, 3, 67, 22, 15, 2, 1, 67, 22, 15),
  (4983, 1, 15, 34, 60, 18, 3, 41, 50, 28, 16),
  (4984, 1, 19, 30, 61, 18, 1, 22, 67, 3, 13),
  (4985, 0, 54, 25, 38, 16, 0, 68, 0, 19, 12),
  (4986, 0, 13, 56, 41, 17, 0, 19, 55, 40, 17),
  (4987, 1, 19, 32, 60, 18, 1, 23, 66, 10, 14),
  (4988, 1, 9, 69, 12, 14, 1, 51, 36, 33, 16),
  (4989, 0, 22, 61, 28, 16, 0, 52, 46, 13, 14),
  (4990, 0, 25, 66, 3, 13, 0, 43, 15, 54, 17),
  (4991, 1, 8, 70, 5, 13, 1, 10, 67, 20, 15),
  (4992, 1, 11, 30, 63, 18, 1, 65, 27, 6, 12),
  (4993, 0, 33, 48, 40, 17, 0, 69, 14, 6, 11),
  (4994, 0, 59, 27, 28, 15, 1, 16, 56, 40, 17),
  (4995, 2, 21, 55, 39, 17, 2, 45, 19, 51, 17),
  (4996, 0, 36, 54, 28, 16, 0, 36, 60, 10, 14),
  (4997, 0, 2, 63, 32, 16, 0, 65, 24, 14, 13),
  (4998, 1, 24, 64, 18, 15, 1, 60, 10, 36, 15),
  (4999, 1, 15, 26, 64, 18, 1, 30, 1, 64, 17)
  ]

lemma witChunk_95_ok : witChunk_95.all checkWit = true := by
  decide +kernel

lemma witChunk_95_ns :
    witChunk_95.map (fun t => t.1) = (List.range 50).map (· + 4950) := by
  decide +kernel

def witChunk_96 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5000, 0, 16, 30, 62, 18, 1, 11, 34, 61, 18),
  (5001, 0, 14, 31, 62, 18, 0, 16, 32, 61, 18),
  (5002, 0, 15, 69, 4, 13, 0, 45, 24, 49, 17),
  (5003, 1, 4, 56, 43, 17, 1, 11, 28, 64, 18),
  (5004, 1, 15, 36, 59, 18, 1, 21, 31, 60, 18),
  (5005, 0, 10, 69, 12, 14, 0, 37, 6, 60, 17),
  (5006, 0, 9, 70, 5, 13, 0, 14, 29, 63, 18),
  (5007, 3, 2, 56, 43, 17, 3, 53, 8, 46, 16),
  (5008, 0, 48, 0, 52, 16, 1, 19, 26, 63, 18),
  (5009, 0, 16, 28, 63, 18, 0, 18, 29, 62, 18),
  (5010, 0, 5, 56, 43, 17, 0, 11, 67, 20, 15),
  (5011, 0, 39, 59, 3, 13, 0, 67, 9, 21, 13),
  (5012, 0, 12, 32, 62, 18, 0, 16, 34, 60, 18),
  (5013, 0, 12, 30, 63, 18, 0, 18, 33, 60, 18),
  (5014, 0, 54, 27, 37, 16, 1, 36, 46, 40, 17),
  (5015, 1, 24, 54, 39, 17, 3, 32, 63, 2, 13),
  (5016, 0, 52, 34, 34, 16, 1, 9, 33, 62, 18),
  (5017, 2, 16, 63, 28, 16, 2, 62, 34, 3, 12),
  (5018, 0, 45, 28, 47, 17, 2, 8, 35, 61, 18),
  (5019, 0, 43, 53, 19, 15, 0, 67, 13, 19, 13),
  (5020, 1, 9, 29, 64, 18, 1, 51, 4, 49, 16),
  (5021, 0, 12, 34, 61, 18, 0, 14, 27, 64, 18),
  (5022, 0, 18, 27, 63, 18, 0, 27, 63, 18, 15),
  (5023, 1, 19, 36, 58, 18, 1, 42, 11, 56, 17),
  (5024, 0, 12, 28, 64, 18, 0, 20, 32, 60, 18),
  (5025, 0, 17, 56, 40, 17, 0, 38, 59, 10, 14),
  (5026, 0, 45, 20, 51, 17, 1, 48, 52, 4, 13),
  (5027, 0, 23, 67, 3, 13, 0, 51, 49, 5, 13),
  (5028, 0, 16, 26, 64, 18, 0, 20, 28, 62, 18),
  (5029, 0, 48, 42, 31, 16, 1, 9, 35, 61, 18),
  (5030, 0, 10, 31, 63, 18, 0, 18, 35, 59, 18),
  (5031, 1, 23, 30, 60, 18, 3, 9, 24, 66, 18),
  (5032, 0, 24, 66, 10, 14, 0, 64, 6, 30, 14),
  (5033, 0, 10, 33, 62, 18, 0, 16, 36, 59, 18),
  (5034, 0, 35, 47, 40, 17, 0, 47, 53, 4, 13),
  (5035, 1, 15, 38, 58, 18, 1, 19, 24, 64, 18),
  (5036, 1, 23, 28, 61, 18, 1, 23, 32, 59, 18),
  (5037, 0, 10, 29, 64, 18, 0, 20, 34, 59, 18),
  (5038, 0, 67, 15, 18, 13, 2, 41, 55, 18, 15),
  (5039, 1, 67, 22, 8, 12, 3, 5, 30, 64, 18),
  (5040, 0, 12, 36, 60, 18, 1, 69, 9, 14, 12),
  (5041, 0, 45, 30, 46, 17, 0, 46, 45, 30, 16),
  (5042, 0, 69, 16, 5, 11, 2, 61, 17, 32, 15),
  (5043, 0, 43, 13, 55, 17, 0, 67, 5, 23, 13),
  (5044, 0, 52, 6, 48, 16, 1, 1, 71, 0, 12),
  (5045, 0, 2, 71, 0, 12, 0, 12, 26, 65, 18),
  (5046, 0, 1, 2, 71, 17, 0, 10, 35, 61, 18),
  (5047, 1, 0, 2, 71, 17, 1, 7, 30, 64, 18),
  (5048, 0, 60, 38, 2, 12, 0, 68, 18, 10, 12),
  (5049, 2, 0, 71, 0, 12, 2, 19, 66, 18, 15)
  ]

lemma witChunk_96_ok : witChunk_96.all checkWit = true := by
  decide +kernel

lemma witChunk_96_ns :
    witChunk_96.map (fun t => t.1) = (List.range 50).map (· + 5000) := by
  decide +kernel

def witChunk_97 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5050, 1, 44, 14, 54, 17, 3, 66, 26, 0, 11),
  (5051, 0, 3, 1, 71, 17, 0, 11, 57, 41, 17),
  (5052, 1, 9, 37, 60, 18, 3, 5, 28, 65, 18),
  (5053, 0, 45, 18, 52, 17, 0, 54, 29, 36, 16),
  (5054, 0, 10, 27, 65, 18, 0, 22, 33, 59, 18),
  (5055, 1, 11, 24, 66, 18, 3, 28, 53, 38, 17),
  (5056, 1, 13, 23, 66, 18, 1, 13, 39, 58, 18),
  (5057, 0, 8, 32, 63, 18, 0, 16, 24, 65, 18),
  (5058, 0, 31, 1, 64, 17, 2, 3, 0, 71, 17),
  (5059, 0, 27, 53, 39, 17, 1, 4, 0, 71, 17),
  (5060, 0, 8, 30, 64, 18, 0, 8, 64, 30, 16),
  (5061, 1, 17, 39, 57, 18, 1, 21, 37, 57, 18),
  (5062, 0, 7, 57, 42, 17, 0, 25, 54, 39, 17),
  (5063, 3, 2, 0, 71, 17, 3, 9, 40, 58, 18),
  (5064, 0, 8, 34, 62, 18, 0, 16, 38, 58, 18),
  (5065, 2, 20, 39, 56, 18, 2, 22, 62, 27, 16),
  (5066, 0, 5, 0, 71, 17, 0, 29, 0, 65, 17),
  (5067, 0, 43, 37, 43, 17, 0, 51, 45, 21, 15),
  (5068, 1, 3, 64, 31, 16, 1, 7, 36, 61, 18),
  (5069, 0, 10, 37, 60, 18, 0, 12, 38, 59, 18),
  (5070, 0, 65, 26, 13, 13, 0, 70, 13, 1, 10),
  (5071, 1, 38, 5, 60, 17, 1, 38, 45, 40, 17),
  (5072, 0, 20, 24, 64, 18, 0, 56, 44, 0, 12),
  (5073, 0, 1, 56, 44, 17, 0, 4, 64, 31, 16),
  (5074, 0, 15, 57, 40, 17, 0, 21, 68, 3, 13),
  (5075, 0, 15, 67, 19, 15, 0, 23, 55, 39, 17),
  (5076, 0, 12, 24, 66, 18, 0, 24, 30, 60, 18),
  (5077, 0, 18, 63, 28, 16, 1, 25, 27, 61, 18),
  (5078, 0, 14, 69, 11, 14, 0, 18, 23, 65, 18),
  (5079, 3, 26, 64, 17, 15, 5, 12, 58, 39, 17),
  (5080, 1, 3, 70, 13, 14, 1, 25, 33, 58, 18),
  (5081, 0, 8, 36, 61, 18, 0, 10, 25, 66, 18),
  (5082, 0, 61, 20, 31, 15, 1, 20, 66, 18, 15),
  (5083, 0, 31, 51, 39, 17, 1, 2, 71, 6, 13),
  (5084, 1, 5, 31, 64, 18, 1, 59, 40, 1, 12),
  (5085, 0, 4, 70, 13, 14, 0, 13, 70, 4, 13),
  (5086, 0, 3, 71, 6, 13, 0, 55, 45, 6, 13),
  (5087, 1, 11, 40, 58, 18, 1, 19, 68, 10, 14),
  (5088, 0, 40, 52, 28, 16, 1, 17, 21, 66, 18),
  (5089, 0, 52, 36, 33, 16, 2, 24, 37, 56, 18),
  (5090, 0, 5, 68, 21, 15, 0, 45, 16, 53, 17),
  (5091, 3, 65, 8, 28, 14, 4, 39, 57, 17, 15),
  (5092, 1, 35, 56, 27, 16, 1, 65, 9, 28, 14),
  (5093, 0, 6, 31, 64, 18, 0, 20, 38, 57, 18),
  (5094, 0, 6, 33, 63, 18, 0, 18, 39, 57, 18),
  (5095, 1, 7, 38, 60, 18, 1, 7, 70, 12, 14),
  (5096, 0, 0, 70, 14, 14, 0, 8, 26, 66, 18),
  (5097, 2, 27, 54, 38, 17, 2, 27, 66, 2, 13),
  (5098, 0, 21, 56, 39, 17, 0, 61, 36, 9, 13),
  (5099, 1, 19, 40, 56, 18, 2, 5, 71, 5, 13)
  ]

lemma witChunk_97_ok : witChunk_97.all checkWit = true := by
  decide +kernel

lemma witChunk_97_ns :
    witChunk_97.map (fun t => t.1) = (List.range 50).map (· + 5050) := by
  decide +kernel

def witChunk_98 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5100, 1, 21, 39, 56, 18, 1, 57, 43, 0, 12),
  (5101, 0, 69, 18, 4, 11, 1, 9, 23, 67, 18),
  (5102, 0, 6, 29, 65, 18, 0, 10, 39, 59, 18),
  (5103, 3, 10, 68, 19, 15, 3, 40, 59, 2, 13),
  (5104, 1, 2, 57, 43, 17, 1, 6, 71, 5, 13),
  (5105, 0, 6, 35, 62, 18, 0, 9, 68, 20, 15),
  (5106, 0, 37, 4, 61, 17, 0, 43, 11, 56, 17),
  (5107, 0, 3, 57, 43, 17, 0, 43, 57, 3, 13),
  (5108, 0, 8, 38, 60, 18, 0, 8, 70, 12, 14),
  (5109, 0, 1, 68, 22, 15, 0, 20, 22, 65, 18),
  (5110, 0, 30, 59, 27, 16, 0, 33, 50, 39, 17),
  (5111, 1, 8, 58, 41, 17, 1, 23, 22, 64, 18),
  (5112, 1, 5, 27, 66, 18, 1, 27, 30, 59, 18),
  (5113, 0, 28, 60, 27, 16, 0, 42, 57, 10, 14),
  (5114, 1, 68, 22, 2, 11, 2, 4, 37, 61, 18),
  (5115, 0, 7, 71, 5, 13, 0, 67, 1, 25, 13),
  (5116, 1, 7, 24, 67, 18, 1, 15, 20, 67, 18),
  (5117, 0, 12, 22, 67, 18, 0, 26, 29, 60, 18),
  (5118, 0, 10, 23, 67, 18, 0, 26, 31, 59, 18),
  (5119, 1, 19, 20, 66, 18, 1, 27, 32, 58, 18),
  (5120, 0, 0, 64, 32, 16, 3, 9, 70, 11, 14),
  (5121, 0, 6, 27, 66, 18, 0, 18, 21, 66, 18),
  (5122, 1, 32, 0, 64, 17, 2, 27, 64, 17, 15),
  (5123, 1, 36, 48, 39, 17, 3, 9, 20, 68, 18),
  (5124, 0, 20, 68, 10, 14, 0, 64, 2, 32, 14),
  (5125, 0, 70, 15, 0, 10, 1, 25, 23, 63, 18),
  (5126, 0, 6, 37, 61, 18, 0, 9, 58, 41, 17),
  (5127, 1, 15, 42, 56, 18, 3, 65, 20, 22, 14),
  (5128, 1, 9, 41, 58, 18, 1, 27, 26, 61, 18),
  (5129, 0, 8, 24, 67, 18, 0, 26, 33, 58, 18),
  (5130, 2, 24, 39, 55, 18, 2, 28, 33, 57, 18),
  (5131, 0, 19, 57, 39, 17, 0, 19, 69, 3, 13),
  (5132, 1, 7, 40, 59, 18, 1, 25, 37, 56, 18),
  (5133, 0, 13, 58, 40, 17, 2, 38, 60, 9, 14),
  (5134, 0, 34, 57, 27, 16, 0, 43, 39, 42, 17),
  (5135, 1, 43, 50, 28, 16, 3, 13, 18, 68, 18),
  (5136, 0, 4, 32, 64, 18, 0, 16, 64, 28, 16),
  (5137, 0, 45, 14, 54, 17, 2, 2, 30, 65, 18),
  (5138, 0, 47, 25, 48, 17, 0, 53, 48, 5, 13),
  (5139, 0, 47, 23, 49, 17, 1, 18, 67, 18, 15),
  (5140, 0, 48, 44, 30, 16, 1, 31, 64, 9, 14),
  (5141, 0, 4, 30, 65, 18, 0, 4, 34, 63, 18),
  (5142, 0, 50, 41, 31, 16, 2, 15, 70, 3, 13),
  (5143, 1, 16, 58, 39, 17, 1, 46, 33, 44, 17),
  (5144, 1, 11, 70, 11, 14, 3, 1, 30, 65, 18),
  (5145, 0, 8, 40, 59, 18, 0, 10, 41, 58, 18),
  (5146, 0, 39, 5, 60, 17, 0, 39, 45, 40, 17),
  (5147, 0, 35, 49, 39, 17, 0, 47, 27, 47, 17),
  (5148, 1, 5, 39, 60, 18, 1, 9, 21, 68, 18),
  (5149, 0, 24, 62, 27, 16, 0, 42, 51, 28, 16)
  ]

lemma witChunk_98_ok : witChunk_98.all checkWit = true := by
  decide +kernel

lemma witChunk_98_ns :
    witChunk_98.map (fun t => t.1) = (List.range 50).map (· + 5100) := by
  decide +kernel

def witChunk_99 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5150, 0, 6, 25, 67, 18, 0, 22, 21, 65, 18),
  (5151, 1, 3, 28, 66, 18, 1, 3, 36, 62, 18),
  (5152, 0, 52, 48, 12, 14, 0, 60, 36, 16, 14),
  (5153, 0, 5, 58, 42, 17, 0, 65, 28, 12, 13),
  (5154, 0, 13, 68, 19, 15, 0, 61, 8, 37, 15),
  (5155, 0, 67, 21, 15, 13, 1, 30, 53, 38, 17),
  (5156, 0, 4, 28, 66, 18, 0, 4, 36, 62, 18),
  (5157, 0, 6, 39, 60, 18, 0, 12, 42, 57, 18),
  (5158, 0, 63, 33, 10, 13, 1, 24, 56, 38, 17),
  (5159, 1, 7, 22, 68, 18, 1, 10, 71, 4, 13),
  (5160, 1, 21, 19, 66, 18, 1, 30, 63, 17, 15),
  (5161, 0, 6, 65, 30, 16, 0, 36, 56, 27, 16),
  (5162, 2, 56, 13, 43, 16, 2, 56, 43, 13, 14),
  (5163, 0, 59, 1, 41, 15, 1, 27, 36, 56, 18),
  (5164, 1, 25, 21, 64, 18, 1, 51, 40, 31, 16),
  (5165, 0, 10, 21, 68, 18, 0, 12, 70, 11, 14),
  (5166, 0, 10, 65, 29, 16, 0, 46, 47, 29, 16),
  (5167, 1, 16, 70, 3, 13, 1, 48, 50, 19, 15),
  (5168, 0, 12, 20, 68, 18, 0, 28, 28, 60, 18),
  (5169, 2, 54, 6, 47, 16, 2, 54, 34, 33, 16),
  (5170, 0, 45, 36, 43, 17, 0, 45, 56, 3, 13),
  (5171, 0, 47, 19, 51, 17, 0, 47, 51, 19, 15),
  (5172, 0, 8, 22, 68, 18, 0, 28, 32, 58, 18),
  (5173, 1, 25, 39, 55, 18, 1, 37, 61, 9, 14),
  (5174, 0, 17, 58, 39, 17, 0, 18, 19, 67, 18),
  (5175, 1, 15, 18, 68, 18, 3, 64, 31, 10, 13),
  (5176, 1, 3, 26, 67, 18, 1, 3, 38, 61, 18),
  (5177, 0, 70, 9, 14, 12, 2, 2, 26, 67, 18),
  (5178, 0, 11, 71, 4, 13, 1, 44, 54, 18, 15),
  (5179, 0, 43, 9, 57, 17, 1, 7, 42, 58, 18),
  (5180, 1, 5, 23, 68, 18, 1, 13, 65, 28, 16),
  (5181, 0, 4, 26, 67, 18, 0, 4, 38, 61, 18),
  (5182, 0, 22, 63, 27, 16, 2, 23, 66, 17, 15),
  (5183, 1, 10, 59, 40, 17, 3, 20, 69, 2, 13),
  (5184, 0, 0, 72, 0, 12, 1, 27, 22, 63, 18),
  (5185, 0, 1, 0, 72, 17, 0, 18, 69, 10, 14),
  (5186, 0, 53, 44, 21, 15, 0, 71, 1, 12, 11),
  (5187, 1, 36, 60, 17, 15, 1, 62, 21, 30, 15),
  (5188, 1, 1, 33, 64, 18, 1, 15, 44, 55, 18),
  (5189, 0, 2, 33, 64, 18, 0, 6, 23, 68, 18),
  (5190, 0, 2, 31, 65, 18, 0, 2, 65, 31, 16),
  (5191, 1, 48, 22, 49, 17, 1, 48, 26, 47, 17),
  (5192, 0, 8, 42, 58, 18, 1, 26, 65, 17, 15),
  (5193, 2, 0, 33, 64, 18, 2, 10, 18, 69, 18),
  (5194, 0, 37, 48, 39, 17, 0, 45, 12, 55, 17),
  (5195, 0, 35, 1, 63, 17, 0, 47, 31, 45, 17),
  (5196, 2, 66, 16, 24, 14, 2, 70, 12, 12, 12),
  (5197, 1, 1, 35, 63, 18, 1, 25, 67, 9, 14),
  (5198, 0, 2, 35, 63, 18, 0, 6, 41, 59, 18),
  (5199, 1, 6, 69, 20, 15, 3, 16, 59, 38, 17)
  ]

lemma witChunk_99_ok : witChunk_99.all checkWit = true := by
  decide +kernel

lemma witChunk_99_ns :
    witChunk_99.map (fun t => t.1) = (List.range 50).map (· + 5150) := by
  decide +kernel

def witChunk_100 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5200, 1, 1, 29, 66, 18, 1, 6, 59, 41, 17),
  (5201, 0, 2, 29, 66, 18, 0, 22, 19, 66, 18),
  (5202, 0, 11, 59, 40, 17, 0, 47, 17, 52, 17),
  (5203, 1, 34, 51, 38, 17, 1, 46, 13, 54, 17),
  (5204, 0, 16, 18, 68, 18, 0, 28, 24, 62, 18),
  (5205, 0, 14, 65, 28, 16, 0, 25, 56, 38, 17),
  (5206, 0, 30, 65, 9, 14, 0, 34, 63, 9, 14),
  (5207, 1, 55, 8, 46, 16, 1, 55, 32, 34, 16),
  (5208, 0, 52, 2, 50, 16, 1, 2, 69, 21, 15),
  (5209, 2, 4, 71, 12, 14, 4, 4, 20, 69, 18),
  (5210, 0, 7, 69, 20, 15, 0, 51, 47, 20, 15),
  (5211, 0, 3, 69, 21, 15, 0, 7, 59, 41, 17),
  (5212, 1, 5, 71, 12, 14, 1, 7, 20, 69, 18),
  (5213, 0, 20, 18, 67, 18, 0, 26, 21, 64, 18),
  (5214, 0, 1, 58, 43, 17, 0, 2, 71, 13, 14),
  (5215, 1, 0, 58, 43, 17, 1, 19, 44, 54, 18),
  (5216, 0, 4, 24, 68, 18, 0, 4, 40, 60, 18),
  (5217, 0, 2, 37, 62, 18, 0, 16, 44, 55, 18),
  (5218, 0, 51, 51, 4, 13, 0, 67, 27, 0, 11),
  (5219, 0, 31, 63, 17, 15, 1, 44, 40, 41, 17),
  (5220, 0, 44, 50, 28, 16, 3, 0, 69, 21, 15),
  (5221, 0, 1, 72, 6, 13, 0, 6, 71, 12, 14),
  (5222, 0, 2, 27, 67, 18, 0, 10, 19, 69, 18),
  (5223, 1, 24, 66, 17, 15, 1, 62, 9, 36, 15),
  (5224, 0, 72, 2, 6, 10, 1, 10, 69, 19, 15),
  (5225, 0, 8, 20, 69, 18, 0, 20, 64, 27, 16),
  (5226, 0, 29, 64, 17, 15, 2, 0, 27, 67, 18),
  (5227, 0, 15, 59, 39, 17, 1, 4, 72, 5, 13),
  (5228, 1, 31, 28, 59, 18, 3, 5, 44, 57, 18),
  (5229, 0, 12, 18, 69, 18, 0, 30, 27, 60, 18),
  (5230, 0, 54, 35, 33, 16, 4, 6, 71, 11, 14),
  (5231, 1, 48, 18, 51, 17, 1, 48, 30, 45, 17),
  (5232, 1, 17, 45, 54, 18, 2, 70, 0, 18, 12),
  (5233, 0, 45, 38, 42, 17, 0, 72, 0, 7, 10),
  (5234, 0, 5, 72, 5, 13, 0, 47, 33, 44, 17),
  (5235, 0, 35, 61, 17, 15, 2, 41, 45, 39, 17),
  (5236, 0, 72, 6, 4, 10, 1, 7, 44, 57, 18),
  (5237, 0, 17, 68, 18, 15, 0, 18, 17, 68, 18),
  (5238, 0, 6, 21, 69, 18, 0, 30, 33, 57, 18),
  (5239, 1, 31, 26, 60, 18, 1, 31, 60, 26, 16),
  (5240, 1, 5, 43, 58, 18, 1, 29, 61, 26, 16),
  (5241, 0, 46, 55, 10, 14, 0, 56, 44, 13, 14),
  (5242, 1, 36, 50, 38, 17, 2, 20, 45, 53, 18),
  (5243, 0, 11, 69, 19, 15, 0, 27, 65, 17, 15),
  (5244, 1, 9, 45, 56, 18, 1, 15, 16, 69, 18),
  (5245, 0, 40, 54, 27, 16, 0, 54, 5, 48, 16),
  (5246, 0, 2, 39, 61, 18, 0, 14, 17, 69, 18),
  (5247, 1, 27, 40, 54, 18, 1, 59, 42, 0, 12),
  (5248, 1, 7, 66, 29, 16, 1, 14, 71, 3, 13),
  (5249, 0, 0, 32, 65, 18, 0, 6, 43, 58, 18)
  ]

lemma witChunk_100_ok : witChunk_100.all checkWit = true := by
  decide +kernel

lemma witChunk_100_ns :
    witChunk_100.map (fun t => t.1) = (List.range 50).map (· + 5200) := by
  decide +kernel

def witChunk_101 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5250, 2, 0, 39, 61, 18, 2, 11, 60, 39, 17),
  (5251, 0, 39, 3, 61, 17, 0, 39, 47, 39, 17),
  (5252, 0, 0, 34, 64, 18, 0, 20, 44, 54, 18),
  (5253, 0, 2, 25, 68, 18, 0, 25, 68, 2, 13),
  (5254, 0, 3, 59, 42, 17, 2, 1, 59, 42, 17),
  (5255, 1, 31, 34, 56, 18, 1, 40, 58, 17, 15),
  (5256, 0, 0, 30, 66, 18, 0, 16, 70, 10, 14),
  (5257, 0, 72, 8, 3, 10, 2, 0, 25, 68, 18),
  (5258, 0, 37, 60, 17, 15, 0, 61, 4, 39, 15),
  (5259, 0, 55, 47, 5, 13, 1, 15, 46, 54, 18),
  (5260, 1, 31, 24, 61, 18, 3, 45, 56, 9, 14),
  (5261, 0, 4, 22, 69, 18, 0, 4, 42, 59, 18),
  (5262, 0, 10, 71, 11, 14, 0, 22, 17, 67, 18),
  (5263, 1, 11, 66, 28, 16, 3, 0, 59, 42, 17),
  (5264, 1, 11, 46, 55, 18, 1, 22, 67, 17, 15),
  (5265, 0, 0, 36, 63, 18, 0, 18, 45, 54, 18),
  (5266, 0, 69, 8, 21, 13, 0, 69, 12, 19, 13),
  (5267, 1, 3, 66, 30, 16, 1, 12, 60, 39, 17),
  (5268, 1, 69, 21, 8, 12, 2, 2, 66, 30, 16),
  (5269, 0, 54, 47, 12, 14, 0, 60, 38, 15, 14),
  (5270, 0, 25, 66, 17, 15, 0, 35, 51, 38, 17),
  (5271, 1, 63, 36, 2, 12, 3, 34, 64, 1, 13),
  (5272, 0, 4, 66, 30, 16, 1, 9, 17, 70, 18),
  (5273, 0, 0, 28, 67, 18, 0, 16, 16, 69, 18),
  (5274, 2, 44, 51, 27, 16, 2, 44, 57, 9, 14),
  (5275, 0, 15, 71, 3, 13, 0, 63, 35, 9, 13),
  (5276, 1, 23, 16, 67, 18, 1, 23, 44, 53, 18),
  (5277, 1, 17, 15, 69, 18, 1, 21, 45, 53, 18),
  (5278, 0, 18, 65, 27, 16, 2, 69, 5, 22, 13),
  (5279, 1, 11, 16, 70, 18, 1, 56, 46, 5, 13),
  (5280, 0, 20, 16, 68, 18, 0, 28, 20, 64, 18),
  (5281, 0, 9, 60, 40, 17, 0, 9, 72, 4, 13),
  (5282, 0, 59, 35, 24, 15, 0, 63, 17, 32, 15),
  (5283, 0, 47, 35, 43, 17, 0, 63, 15, 33, 15),
  (5284, 0, 12, 66, 28, 16, 1, 1, 41, 60, 18),
  (5285, 0, 2, 41, 60, 18, 0, 12, 46, 55, 18),
  (5286, 0, 19, 59, 38, 17, 0, 49, 22, 49, 17),
  (5287, 1, 55, 46, 12, 14, 5, 46, 39, 40, 17),
  (5288, 0, 0, 38, 62, 18, 0, 8, 18, 70, 18),
  (5289, 0, 10, 17, 70, 18, 0, 32, 28, 59, 18),
  (5290, 0, 13, 60, 39, 17, 4, 17, 60, 37, 17),
  (5291, 0, 39, 59, 17, 15, 0, 63, 19, 31, 15),
  (5292, 1, 21, 15, 68, 18, 3, 19, 47, 52, 18),
  (5293, 1, 1, 23, 69, 18, 1, 53, 39, 31, 16),
  (5294, 0, 2, 23, 69, 18, 0, 23, 69, 2, 13),
  (5295, 3, 5, 46, 56, 18, 3, 37, 62, 8, 14),
  (5296, 1, 13, 15, 70, 18, 1, 13, 47, 54, 18),
  (5297, 0, 6, 19, 70, 18, 0, 30, 61, 26, 16),
  (5298, 0, 43, 43, 40, 17, 2, 0, 23, 69, 18),
  (5299, 1, 4, 60, 41, 17, 1, 47, 48, 28, 16)
  ]

lemma witChunk_101_ok : witChunk_101.all checkWit = true := by
  decide +kernel

lemma witChunk_101_ns :
    witChunk_101.map (fun t => t.1) = (List.range 50).map (· + 5250) := by
  decide +kernel

def witChunk_102 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5300, 0, 0, 26, 68, 18, 0, 12, 16, 70, 18),
  (5301, 0, 46, 49, 28, 16, 0, 49, 20, 50, 17),
  (5302, 0, 42, 53, 27, 16, 1, 16, 60, 38, 17),
  (5303, 1, 7, 46, 56, 18, 1, 23, 64, 26, 16),
  (5304, 0, 28, 62, 26, 16, 1, 27, 42, 53, 18),
  (5305, 0, 52, 0, 51, 16, 2, 48, 47, 28, 16),
  (5306, 0, 5, 60, 41, 17, 0, 45, 40, 41, 17),
  (5307, 0, 23, 67, 17, 15, 2, 57, 45, 5, 13),
  (5308, 1, 57, 11, 44, 16, 3, 67, 15, 24, 14),
  (5309, 0, 54, 37, 32, 16, 1, 17, 47, 53, 18),
  (5310, 0, 6, 45, 57, 18, 0, 15, 69, 18, 15),
  (5311, 1, 3, 20, 70, 18, 1, 3, 44, 58, 18),
  (5312, 1, 13, 71, 10, 14, 1, 15, 66, 27, 16),
  (5313, 0, 34, 59, 26, 16, 0, 37, 50, 38, 17),
  (5314, 1, 72, 8, 8, 11, 2, 43, 44, 39, 17),
  (5315, 0, 55, 43, 21, 15, 0, 63, 11, 35, 15),
  (5316, 0, 4, 20, 70, 18, 0, 4, 44, 58, 18),
  (5317, 0, 0, 66, 31, 16, 1, 9, 47, 55, 18),
  (5318, 0, 22, 45, 53, 18, 0, 41, 46, 39, 17),
  (5319, 3, 1, 20, 70, 18, 3, 1, 44, 58, 18),
  (5320, 0, 48, 54, 10, 14, 0, 64, 30, 18, 14),
  (5321, 0, 0, 40, 61, 18, 0, 14, 15, 70, 18),
  (5322, 2, 11, 72, 3, 13, 2, 33, 63, 16, 15),
  (5323, 1, 15, 14, 70, 18, 1, 31, 38, 54, 18),
  (5324, 2, 26, 44, 52, 18, 2, 34, 32, 56, 18),
  (5325, 0, 5, 70, 20, 15, 0, 20, 46, 53, 18),
  (5326, 0, 22, 69, 9, 14, 0, 42, 59, 9, 14),
  (5327, 1, 8, 70, 19, 15, 1, 40, 2, 61, 17),
  (5328, 2, 10, 48, 54, 18, 2, 30, 18, 64, 18),
  (5329, 0, 72, 12, 1, 10, 2, 54, 2, 49, 16),
  (5330, 1, 72, 0, 12, 11, 2, 29, 65, 16, 15),
  (5331, 1, 71, 12, 12, 12, 2, 9, 61, 39, 17),
  (5332, 1, 31, 20, 63, 18, 2, 58, 14, 42, 16),
  (5333, 0, 17, 60, 38, 17, 0, 22, 15, 68, 18),
  (5334, 0, 2, 43, 59, 18, 0, 10, 47, 55, 18),
  (5335, 1, 39, 56, 26, 16, 1, 46, 9, 56, 17),
  (5336, 0, 36, 58, 26, 16, 0, 68, 26, 6, 12),
  (5337, 0, 0, 24, 69, 18, 0, 14, 71, 10, 14),
  (5338, 0, 37, 0, 63, 17, 0, 45, 8, 57, 17),
  (5339, 0, 63, 23, 29, 15, 1, 3, 72, 12, 14),
  (5340, 1, 15, 48, 53, 18, 2, 2, 72, 12, 14),
  (5341, 0, 16, 66, 27, 16, 0, 69, 2, 24, 13),
  (5342, 0, 1, 70, 21, 15, 0, 9, 70, 19, 15),
  (5343, 1, 0, 70, 21, 15, 1, 11, 48, 54, 18),
  (5344, 0, 4, 72, 12, 14, 1, 1, 21, 70, 18),
  (5345, 0, 2, 21, 70, 18, 0, 21, 70, 2, 13),
  (5346, 0, 29, 56, 37, 17, 0, 63, 9, 36, 15),
  (5347, 0, 27, 57, 37, 17, 1, 50, 27, 46, 17),
  (5348, 0, 24, 64, 26, 16, 1, 7, 16, 71, 18),
  (5349, 0, 65, 32, 10, 13, 1, 9, 15, 71, 18)
  ]

lemma witChunk_102_ok : witChunk_102.all checkWit = true := by
  decide +kernel

lemma witChunk_102_ns :
    witChunk_102.map (fun t => t.1) = (List.range 50).map (· + 5300) := by
  decide +kernel

def witChunk_103 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5350, 1, 40, 48, 38, 17, 3, 30, 56, 36, 17),
  (5351, 1, 23, 14, 68, 18, 1, 23, 46, 52, 18),
  (5352, 0, 16, 14, 70, 18, 0, 32, 22, 62, 18),
  (5353, 0, 0, 72, 13, 14, 0, 58, 15, 42, 16),
  (5354, 0, 21, 68, 17, 15, 2, 4, 17, 71, 18),
  (5355, 0, 31, 55, 37, 17, 0, 43, 5, 59, 17),
  (5356, 1, 7, 72, 11, 14, 1, 9, 67, 28, 16),
  (5357, 0, 20, 14, 69, 18, 0, 28, 42, 53, 18),
  (5358, 0, 25, 58, 37, 17, 0, 58, 25, 37, 16),
  (5359, 1, 6, 61, 40, 17, 3, 48, 11, 54, 17),
  (5360, 1, 2, 73, 5, 13, 1, 11, 14, 71, 18),
  (5361, 0, 8, 16, 71, 18, 0, 34, 29, 58, 18),
  (5362, 0, 13, 72, 3, 13, 0, 67, 27, 12, 13),
  (5363, 0, 3, 73, 5, 13, 0, 11, 61, 39, 17),
  (5364, 0, 0, 42, 60, 18, 0, 12, 48, 54, 18),
  (5365, 0, 1, 60, 42, 17, 1, 73, 3, 5, 10),
  (5366, 0, 6, 17, 71, 18, 0, 6, 67, 29, 16),
  (5367, 1, 71, 0, 18, 12, 7, 38, 60, 15, 15),
  (5368, 0, 52, 42, 30, 16, 1, 50, 29, 45, 17),
  (5369, 0, 8, 72, 11, 14, 0, 16, 48, 53, 18),
  (5370, 0, 7, 61, 40, 17, 0, 61, 32, 25, 15),
  (5371, 1, 18, 71, 2, 13, 1, 19, 48, 52, 18),
  (5372, 1, 5, 47, 56, 18, 1, 31, 40, 53, 18),
  (5373, 0, 10, 67, 28, 16, 1, 21, 13, 69, 18),
  (5374, 0, 33, 54, 37, 17, 2, 39, 62, 1, 13),
  (5375, 1, 35, 28, 58, 18, 1, 42, 3, 60, 17),
  (5376, 1, 3, 18, 71, 18, 1, 3, 46, 57, 18),
  (5377, 2, 2, 18, 71, 18, 2, 2, 46, 57, 18),
  (5378, 0, 63, 25, 28, 15, 1, 32, 64, 16, 15),
  (5379, 0, 23, 59, 37, 17, 0, 59, 37, 23, 15),
  (5380, 0, 72, 14, 0, 10, 1, 7, 48, 55, 18),
  (5381, 0, 4, 18, 71, 18, 0, 4, 46, 57, 18),
  (5382, 0, 58, 13, 43, 16, 0, 58, 43, 13, 14),
  (5383, 1, 6, 73, 4, 13, 1, 30, 65, 16, 15),
  (5384, 0, 0, 22, 70, 18, 0, 32, 38, 54, 18),
  (5385, 0, 22, 65, 26, 16, 2, 39, 60, 16, 15),
  (5386, 0, 69, 0, 25, 13, 0, 69, 20, 15, 13),
  (5387, 0, 43, 57, 17, 15, 0, 63, 7, 37, 15),
  (5388, 2, 66, 0, 32, 14, 3, 40, 49, 37, 17),
  (5389, 0, 45, 42, 40, 17, 0, 58, 27, 36, 16),
  (5390, 0, 15, 61, 38, 17, 0, 26, 15, 67, 18),
  (5391, 3, 13, 50, 52, 18, 3, 50, 32, 43, 17),
  (5392, 0, 48, 48, 28, 16, 1, 1, 45, 58, 18),
  (5393, 0, 2, 45, 58, 18, 0, 2, 67, 30, 16),
  (5394, 0, 7, 73, 4, 13, 2, 24, 47, 51, 18),
  (5395, 0, 43, 45, 39, 17, 1, 19, 66, 26, 16),
  (5396, 0, 24, 14, 68, 18, 0, 24, 46, 52, 18),
  (5397, 0, 22, 47, 52, 18, 2, 0, 45, 58, 18),
  (5398, 0, 54, 39, 31, 16, 1, 28, 66, 16, 15),
  (5399, 1, 46, 41, 40, 17, 1, 50, 31, 44, 17)
  ]

lemma witChunk_103_ok : witChunk_103.all checkWit = true := by
  decide +kernel

lemma witChunk_103_ns :
    witChunk_103.map (fun t => t.1) = (List.range 50).map (· + 5350) := by
  decide +kernel

def witChunk_104 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5400, 1, 9, 49, 54, 18, 3, 19, 11, 70, 18),
  (5401, 2, 26, 46, 51, 18, 2, 31, 56, 36, 17),
  (5402, 0, 61, 0, 41, 15, 0, 63, 37, 8, 13),
  (5403, 0, 35, 53, 37, 17, 1, 35, 24, 60, 18),
  (5404, 1, 37, 63, 8, 14, 1, 59, 20, 39, 16),
  (5405, 0, 26, 45, 52, 18, 0, 70, 21, 8, 12),
  (5406, 0, 2, 19, 71, 18, 0, 14, 13, 71, 18),
  (5407, 1, 11, 72, 10, 14, 1, 19, 12, 70, 18),
  (5408, 0, 20, 48, 52, 18, 1, 2, 61, 41, 17),
  (5409, 0, 50, 53, 10, 14, 0, 64, 32, 17, 14),
  (5410, 0, 21, 60, 37, 17, 2, 0, 19, 71, 18),
  (5411, 0, 3, 61, 41, 17, 0, 19, 69, 17, 15),
  (5412, 0, 40, 56, 26, 16, 1, 15, 12, 71, 18),
  (5413, 1, 17, 71, 9, 14, 2, 52, 51, 10, 14),
  (5414, 0, 14, 67, 27, 16, 0, 22, 13, 69, 18),
  (5415, 3, 73, 8, 2, 10, 5, 28, 66, 15, 15),
  (5416, 1, 18, 61, 37, 17, 1, 27, 14, 67, 18),
  (5417, 0, 0, 44, 59, 18, 0, 10, 49, 54, 18),
  (5418, 2, 28, 45, 51, 18, 2, 33, 55, 36, 17),
  (5419, 0, 51, 53, 3, 13, 1, 27, 68, 8, 14),
  (5420, 1, 25, 13, 68, 18, 1, 57, 45, 12, 14),
  (5421, 0, 58, 11, 44, 16, 1, 33, 19, 63, 18),
  (5422, 2, 7, 62, 39, 17, 2, 15, 70, 17, 15),
  (5423, 1, 26, 67, 16, 15, 1, 38, 61, 16, 15),
  (5424, 0, 28, 44, 52, 18, 1, 29, 15, 66, 18),
  (5425, 0, 45, 6, 58, 17, 2, 8, 13, 72, 18),
  (5426, 0, 47, 9, 56, 17, 2, 16, 11, 71, 18),
  (5427, 0, 63, 27, 27, 15, 1, 50, 51, 18, 15),
  (5428, 0, 12, 72, 10, 14, 1, 47, 56, 9, 14),
  (5429, 0, 18, 49, 52, 18, 0, 41, 48, 38, 17),
  (5430, 0, 58, 29, 35, 16, 3, 70, 16, 16, 13),
  (5431, 1, 7, 14, 72, 18, 1, 8, 62, 39, 17),
  (5432, 0, 20, 66, 26, 16, 1, 11, 50, 53, 18),
  (5433, 0, 32, 40, 53, 18, 0, 68, 28, 5, 12),
  (5434, 0, 51, 23, 48, 17, 1, 12, 62, 38, 17),
  (5435, 0, 51, 25, 47, 17, 1, 44, 4, 59, 17),
  (5436, 1, 5, 15, 72, 18, 1, 9, 13, 72, 18),
  (5437, 0, 69, 26, 0, 11, 1, 25, 47, 51, 18),
  (5438, 0, 54, 49, 11, 14, 0, 62, 37, 15, 14),
  (5439, 1, 35, 36, 54, 18, 5, 3, 14, 72, 18),
  (5440, 1, 6, 71, 19, 15, 1, 10, 73, 3, 13),
  (5441, 0, 0, 20, 71, 18, 0, 16, 12, 71, 18),
  (5442, 0, 31, 65, 16, 15, 0, 37, 52, 37, 17),
  (5443, 0, 51, 21, 49, 17, 1, 43, 54, 26, 16),
  (5444, 0, 8, 14, 72, 18, 0, 20, 12, 70, 18),
  (5445, 0, 6, 15, 72, 18, 0, 34, 65, 8, 14),
  (5446, 0, 9, 62, 39, 17, 0, 18, 71, 9, 14),
  (5447, 1, 2, 71, 20, 15, 1, 16, 70, 17, 15),
  (5448, 1, 27, 46, 51, 18, 1, 71, 18, 9, 12),
  (5449, 2, 64, 33, 16, 14, 4, 8, 68, 27, 16)
  ]

lemma witChunk_104_ok : witChunk_104.all checkWit = true := by
  decide +kernel

lemma witChunk_104_ns :
    witChunk_104.map (fun t => t.1) = (List.range 50).map (· + 5400) := by
  decide +kernel

def witChunk_105 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5450, 0, 3, 71, 20, 15, 0, 35, 63, 16, 15),
  (5451, 0, 7, 71, 19, 15, 0, 19, 61, 37, 17),
  (5452, 1, 25, 69, 8, 14, 1, 27, 64, 25, 16),
  (5453, 0, 10, 13, 72, 18, 0, 12, 50, 53, 18),
  (5454, 0, 57, 42, 21, 15, 0, 66, 33, 3, 12),
  (5455, 1, 26, 59, 36, 17, 1, 59, 26, 36, 16),
  (5456, 0, 4, 16, 72, 18, 0, 4, 48, 56, 18),
  (5457, 0, 13, 62, 38, 17, 0, 73, 8, 8, 11),
  (5458, 0, 43, 3, 60, 17, 1, 24, 68, 16, 15),
  (5459, 0, 11, 73, 3, 13, 1, 7, 68, 28, 16),
  (5460, 0, 16, 50, 52, 18, 2, 6, 50, 54, 18),
  (5461, 0, 49, 12, 54, 17, 0, 49, 36, 42, 17),
  (5462, 0, 2, 47, 57, 18, 0, 6, 49, 55, 18),
  (5463, 3, 52, 25, 46, 17, 5, 38, 63, 0, 13),
  (5464, 1, 19, 50, 51, 18, 1, 21, 11, 70, 18),
  (5465, 0, 42, 55, 26, 16, 2, 68, 7, 28, 14),
  (5466, 0, 29, 68, 1, 13, 0, 37, 64, 1, 13),
  (5467, 0, 51, 29, 45, 17, 1, 7, 50, 54, 18),
  (5468, 1, 37, 31, 56, 18, 1, 41, 61, 8, 14),
  (5469, 0, 5, 62, 40, 17, 0, 26, 13, 68, 18),
  (5470, 0, 58, 9, 45, 16, 2, 63, 38, 7, 13),
  (5471, 1, 16, 62, 37, 17, 1, 35, 20, 62, 18),
  (5472, 0, 8, 68, 28, 16, 0, 12, 12, 72, 18),
  (5473, 0, 73, 0, 12, 11, 2, 18, 10, 71, 18),
  (5474, 0, 27, 67, 16, 15, 0, 53, 48, 19, 15),
  (5475, 3, 29, 46, 50, 18, 4, 27, 67, 15, 15),
  (5476, 1, 1, 17, 72, 18, 1, 1, 73, 12, 14),
  (5477, 0, 2, 17, 72, 18, 0, 2, 73, 12, 14),
  (5478, 0, 17, 70, 17, 15, 0, 70, 23, 7, 12),
  (5479, 1, 24, 70, 1, 13, 1, 34, 55, 36, 17),
  (5480, 0, 0, 46, 58, 18, 0, 8, 50, 54, 18),
  (5481, 0, 4, 68, 29, 16, 0, 24, 12, 69, 18),
  (5482, 0, 45, 44, 39, 17, 2, 8, 51, 53, 18),
  (5483, 2, 61, 35, 23, 15, 2, 65, 17, 31, 15),
  (5484, 3, 1, 68, 29, 16, 3, 19, 71, 8, 14),
  (5485, 1, 37, 33, 55, 18, 1, 57, 5, 47, 16),
  (5486, 0, 6, 73, 11, 14, 0, 11, 71, 18, 15),
  (5487, 1, 74, 3, 0, 9, 3, 13, 68, 26, 16),
  (5488, 1, 42, 1, 61, 17, 1, 42, 61, 1, 13),
  (5489, 0, 18, 67, 26, 16, 2, 44, 59, 8, 14),
  (5490, 0, 47, 41, 40, 17, 2, 60, 19, 39, 16),
  (5491, 0, 27, 69, 1, 13, 0, 39, 51, 37, 17),
  (5492, 0, 32, 42, 52, 18, 1, 15, 72, 9, 14),
  (5493, 0, 32, 62, 25, 16, 0, 50, 47, 28, 16),
  (5494, 0, 30, 63, 25, 16, 1, 52, 22, 48, 17),
  (5495, 1, 23, 70, 8, 14, 3, 8, 63, 38, 17),
  (5496, 3, 7, 73, 10, 14, 3, 59, 29, 34, 16),
  (5497, 0, 12, 68, 27, 16, 0, 54, 41, 30, 16),
  (5498, 0, 39, 61, 16, 15, 0, 51, 31, 44, 17),
  (5499, 0, 63, 3, 39, 15, 1, 27, 12, 68, 18)
  ]

lemma witChunk_105_ok : witChunk_105.all checkWit = true := by
  decide +kernel

lemma witChunk_105_ns :
    witChunk_105.map (fun t => t.1) = (List.range 50).map (· + 5450) := by
  decide +kernel

def witChunk_106 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5500, 1, 31, 44, 51, 18, 1, 37, 23, 60, 18),
  (5501, 0, 14, 11, 72, 18, 0, 14, 51, 52, 18),
  (5502, 0, 1, 74, 5, 13, 0, 17, 62, 37, 17),
  (5503, 1, 0, 74, 5, 13, 1, 22, 61, 36, 17),
  (5504, 1, 19, 10, 71, 18, 2, 14, 68, 26, 16),
  (5505, 0, 22, 11, 70, 18, 0, 25, 68, 16, 15),
  (5506, 0, 27, 59, 36, 17, 0, 31, 57, 36, 17),
  (5507, 0, 47, 7, 57, 17, 1, 46, 5, 58, 17),
  (5508, 0, 0, 18, 72, 18, 0, 36, 36, 54, 18),
  (5509, 0, 73, 12, 6, 11, 1, 25, 11, 69, 18),
  (5510, 0, 10, 51, 53, 18, 0, 65, 14, 33, 15),
  (5511, 1, 15, 10, 72, 18, 1, 48, 54, 17, 15),
  (5512, 1, 9, 73, 10, 14, 1, 23, 66, 25, 16),
  (5513, 0, 74, 1, 6, 10, 2, 20, 71, 8, 14),
  (5514, 2, 60, 15, 41, 16, 2, 68, 21, 21, 14),
  (5515, 1, 10, 63, 38, 17, 1, 31, 14, 66, 18),
  (5516, 2, 10, 52, 52, 18, 2, 34, 16, 64, 18),
  (5517, 0, 5, 74, 4, 13, 0, 74, 5, 4, 10),
  (5518, 4, 6, 11, 73, 18, 4, 22, 51, 49, 18),
  (5519, 1, 59, 10, 44, 16, 1, 72, 18, 3, 11),
  (5520, 1, 35, 18, 63, 18, 2, 70, 24, 6, 12),
  (5521, 0, 16, 72, 9, 14, 0, 25, 60, 36, 17),
  (5522, 0, 45, 4, 59, 17, 0, 53, 52, 3, 13),
  (5523, 0, 47, 55, 17, 15, 0, 71, 11, 19, 13),
  (5524, 0, 0, 68, 30, 16, 0, 60, 18, 40, 16),
  (5525, 0, 41, 0, 62, 17, 0, 62, 41, 0, 12),
  (5526, 0, 1, 62, 41, 17, 0, 18, 51, 51, 18),
  (5527, 1, 0, 62, 41, 17, 1, 15, 68, 26, 16),
  (5528, 0, 44, 54, 26, 16, 0, 60, 22, 38, 16),
  (5529, 0, 10, 73, 10, 14, 0, 58, 7, 46, 16),
  (5530, 0, 51, 15, 52, 17, 1, 52, 18, 50, 17),
  (5531, 0, 59, 45, 5, 13, 0, 71, 7, 21, 13),
  (5532, 1, 15, 52, 51, 18, 3, 29, 68, 7, 14),
  (5533, 0, 48, 50, 27, 16, 0, 58, 45, 12, 14),
  (5534, 0, 6, 13, 73, 18, 0, 11, 63, 38, 17),
  (5535, 1, 27, 48, 50, 18, 3, 34, 56, 35, 17),
  (5536, 1, 3, 14, 73, 18, 1, 3, 50, 55, 18),
  (5537, 0, 8, 12, 73, 18, 0, 38, 27, 58, 18),
  (5538, 2, 45, 57, 16, 15, 2, 69, 25, 12, 13),
  (5539, 0, 7, 63, 39, 17, 0, 51, 33, 43, 17),
  (5540, 0, 16, 10, 72, 18, 0, 24, 70, 8, 14),
  (5541, 0, 2, 49, 56, 18, 0, 4, 14, 73, 18),
  (5542, 0, 58, 33, 33, 16, 1, 20, 62, 36, 17),
  (5543, 3, 26, 68, 15, 15, 3, 33, 44, 50, 18),
  (5544, 1, 5, 51, 54, 18, 1, 21, 51, 50, 18),
  (5545, 0, 60, 24, 37, 16, 2, 0, 49, 56, 18),
  (5546, 0, 23, 61, 36, 17, 0, 23, 69, 16, 15),
  (5547, 2, 33, 65, 15, 15, 3, 53, 44, 28, 16),
  (5548, 1, 21, 71, 8, 14, 3, 27, 65, 24, 16),
  (5549, 0, 36, 38, 53, 18, 0, 42, 61, 8, 14)
  ]

lemma witChunk_106_ok : witChunk_106.all checkWit = true := by
  decide +kernel

lemma witChunk_106_ns :
    witChunk_106.map (fun t => t.1) = (List.range 50).map (· + 5500) := by
  decide +kernel

def witChunk_107 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5550, 0, 10, 11, 73, 18, 0, 38, 25, 59, 18),
  (5551, 1, 8, 74, 3, 13, 1, 38, 53, 36, 17),
  (5552, 0, 12, 52, 52, 18, 0, 28, 12, 68, 18),
  (5553, 0, 0, 48, 57, 18, 0, 6, 51, 54, 18),
  (5554, 2, 19, 72, 1, 13, 2, 35, 64, 15, 15),
  (5555, 0, 15, 71, 17, 15, 0, 63, 31, 25, 15),
  (5556, 0, 16, 68, 26, 16, 1, 17, 9, 72, 18),
  (5557, 0, 24, 66, 25, 16, 1, 1, 15, 73, 18),
  (5558, 0, 2, 15, 73, 18, 0, 15, 73, 2, 13),
  (5559, 1, 39, 30, 56, 18, 5, 66, 33, 8, 13),
  (5560, 0, 60, 14, 42, 16, 1, 69, 11, 26, 14),
  (5561, 0, 16, 52, 51, 18, 0, 32, 44, 51, 18),
  (5562, 2, 0, 15, 73, 18, 2, 3, 72, 19, 15),
  (5563, 0, 15, 63, 37, 17, 1, 4, 72, 19, 15),
  (5564, 1, 7, 52, 53, 18, 1, 57, 3, 48, 16),
  (5565, 1, 21, 9, 71, 18, 2, 7, 72, 18, 15),
  (5566, 0, 9, 74, 3, 13, 4, 18, 53, 49, 18),
  (5567, 1, 19, 52, 50, 18, 3, 2, 72, 19, 15),
  (5568, 5, 1, 51, 54, 18, 5, 9, 69, 26, 16),
  (5569, 0, 57, 48, 4, 13, 2, 4, 69, 28, 16),
  (5570, 0, 5, 72, 19, 15, 0, 63, 1, 40, 15),
  (5571, 0, 23, 71, 1, 13, 0, 43, 1, 61, 17),
  (5572, 0, 60, 26, 36, 16, 1, 5, 69, 28, 16),
  (5573, 0, 12, 10, 73, 18, 0, 38, 23, 60, 18),
  (5574, 1, 8, 72, 18, 15, 5, 4, 72, 18, 15),
  (5575, 1, 2, 63, 40, 17, 3, 25, 66, 24, 16),
  (5576, 0, 24, 10, 70, 18, 0, 24, 50, 50, 18),
  (5577, 0, 8, 52, 53, 18, 0, 26, 49, 50, 18),
  (5578, 0, 3, 63, 40, 17, 2, 1, 63, 40, 17),
  (5579, 0, 47, 43, 39, 17, 0, 51, 13, 53, 17),
  (5580, 1, 39, 24, 59, 18, 2, 18, 8, 72, 18),
  (5581, 0, 6, 69, 28, 16, 0, 21, 62, 36, 17),
  (5582, 2, 47, 58, 1, 13, 2, 61, 37, 22, 15),
  (5583, 3, 10, 64, 37, 17, 3, 29, 10, 68, 18),
  (5584, 1, 74, 5, 9, 11, 2, 34, 62, 24, 16),
  (5585, 0, 0, 16, 73, 18, 0, 1, 72, 20, 15),
  (5586, 0, 43, 59, 16, 15, 0, 71, 17, 16, 13),
  (5587, 1, 20, 72, 1, 13, 1, 46, 45, 38, 17),
  (5588, 0, 28, 48, 50, 18, 1, 29, 11, 68, 18),
  (5589, 0, 9, 72, 18, 15, 0, 18, 9, 72, 18),
  (5590, 0, 10, 69, 27, 16, 0, 51, 35, 42, 17),
  (5591, 1, 18, 63, 36, 17, 1, 47, 52, 26, 16),
  (5592, 1, 27, 10, 69, 18, 1, 35, 42, 51, 18),
  (5593, 0, 60, 12, 43, 16, 2, 28, 65, 24, 16),
  (5594, 0, 53, 24, 47, 17, 2, 11, 64, 37, 17),
  (5595, 0, 55, 47, 19, 15, 1, 39, 34, 54, 18),
  (5596, 1, 9, 53, 52, 18, 1, 31, 12, 67, 18),
  (5597, 0, 21, 70, 16, 15, 0, 53, 22, 48, 17),
  (5598, 0, 22, 67, 25, 16, 0, 47, 5, 58, 17),
  (5599, 1, 67, 28, 18, 14, 3, 69, 6, 28, 14)
  ]

lemma witChunk_107_ok : witChunk_107.all checkWit = true := by
  decide +kernel

lemma witChunk_107_ns :
    witChunk_107.map (fun t => t.1) = (List.range 50).map (· + 5550) := by
  decide +kernel

def witChunk_108 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5600, 0, 36, 40, 52, 18, 0, 44, 60, 8, 14),
  (5601, 0, 46, 53, 26, 16, 0, 49, 8, 56, 17),
  (5602, 1, 40, 52, 36, 17, 2, 11, 72, 17, 15),
  (5603, 0, 59, 41, 21, 15, 2, 61, 43, 5, 13),
  (5604, 0, 20, 52, 50, 18, 0, 52, 46, 28, 16),
  (5605, 1, 1, 69, 29, 16, 1, 61, 19, 39, 16),
  (5606, 0, 2, 69, 29, 16, 0, 14, 9, 73, 18),
  (5607, 1, 32, 66, 15, 15, 1, 39, 22, 60, 18),
  (5608, 1, 3, 74, 11, 14, 1, 13, 69, 26, 16),
  (5609, 0, 30, 47, 50, 18, 0, 60, 28, 35, 16),
  (5610, 0, 53, 20, 49, 17, 2, 0, 69, 29, 16),
  (5611, 1, 12, 64, 37, 17, 1, 19, 8, 72, 18),
  (5612, 1, 19, 68, 25, 16, 1, 43, 56, 25, 16),
  (5613, 0, 4, 74, 11, 14, 0, 10, 53, 52, 18),
  (5614, 4, 14, 69, 25, 16, 4, 34, 45, 49, 18),
  (5615, 1, 32, 58, 35, 17, 1, 56, 46, 19, 15),
  (5616, 1, 30, 67, 15, 15, 1, 33, 13, 66, 18),
  (5617, 0, 54, 51, 10, 14, 0, 64, 36, 15, 14),
  (5618, 0, 53, 28, 45, 17, 0, 71, 1, 24, 13),
  (5619, 0, 43, 49, 37, 17, 1, 12, 72, 17, 15),
  (5620, 0, 0, 74, 12, 14, 1, 15, 8, 73, 18),
  (5621, 0, 9, 64, 38, 17, 1, 61, 23, 37, 16),
  (5622, 0, 38, 37, 53, 18, 5, 64, 30, 24, 15),
  (5623, 1, 18, 71, 16, 15, 1, 46, 57, 16, 15),
  (5624, 1, 5, 11, 74, 18, 1, 26, 61, 35, 17),
  (5625, 2, 10, 54, 51, 18, 2, 15, 64, 36, 17),
  (5626, 0, 19, 63, 36, 17, 0, 21, 72, 1, 13),
  (5627, 0, 71, 19, 15, 13, 0, 75, 1, 1, 9),
  (5628, 1, 39, 36, 53, 18, 2, 38, 60, 24, 16),
  (5629, 0, 45, 2, 60, 17, 1, 1, 51, 55, 18),
  (5630, 0, 2, 51, 55, 18, 0, 50, 49, 27, 16),
  (5631, 1, 3, 12, 74, 18, 1, 3, 52, 54, 18),
  (5632, 1, 27, 50, 49, 18, 1, 34, 57, 35, 17),
  (5633, 0, 6, 11, 74, 18, 0, 14, 69, 26, 16),
  (5634, 0, 13, 64, 37, 17, 0, 63, 33, 24, 15),
  (5635, 0, 55, 51, 3, 13, 1, 4, 64, 39, 17),
  (5636, 0, 0, 50, 56, 18, 0, 4, 12, 74, 18),
  (5637, 2, 27, 70, 0, 13, 2, 75, 2, 0, 9),
  (5638, 0, 42, 57, 25, 16, 0, 51, 11, 54, 17),
  (5639, 1, 47, 58, 8, 14, 3, 1, 12, 74, 18),
  (5640, 0, 8, 10, 74, 18, 0, 8, 74, 10, 14),
  (5641, 2, 20, 7, 72, 18, 4, 13, 72, 16, 15),
  (5642, 0, 5, 64, 39, 17, 0, 13, 72, 17, 15),
  (5643, 1, 15, 54, 50, 18, 1, 54, 49, 18, 15),
  (5644, 1, 29, 65, 24, 16, 1, 39, 20, 61, 18),
  (5645, 0, 28, 10, 69, 18, 0, 30, 11, 68, 18),
  (5646, 4, 45, 58, 15, 15, 6, 43, 50, 35, 17),
  (5647, 1, 2, 75, 4, 13, 1, 24, 62, 35, 17),
  (5648, 0, 20, 8, 72, 18, 0, 20, 72, 8, 14),
  (5649, 0, 2, 13, 74, 18, 0, 13, 74, 2, 13)
  ]

lemma witChunk_108_ok : witChunk_108.all checkWit = true := by
  decide +kernel

lemma witChunk_108_ns :
    witChunk_108.map (fun t => t.1) = (List.range 50).map (· + 5600) := by
  decide +kernel

def witChunk_109 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5650, 0, 3, 75, 4, 13, 1, 16, 64, 36, 17),
  (5651, 0, 51, 37, 41, 17, 1, 67, 34, 2, 12),
  (5652, 3, 27, 51, 48, 18, 3, 40, 53, 35, 17),
  (5653, 1, 21, 53, 49, 18, 1, 29, 69, 7, 14),
  (5654, 0, 6, 53, 53, 18, 0, 70, 27, 5, 12),
  (5655, 1, 71, 24, 6, 12, 3, 50, 56, 1, 13),
  (5656, 0, 60, 30, 34, 16, 1, 18, 73, 1, 13),
  (5657, 0, 10, 9, 74, 18, 0, 26, 9, 70, 18),
  (5658, 0, 19, 71, 16, 15, 2, 41, 63, 0, 13),
  (5659, 0, 67, 33, 9, 13, 1, 36, 56, 35, 17),
  (5660, 1, 41, 29, 56, 18, 3, 23, 53, 48, 18),
  (5661, 0, 12, 54, 51, 18, 0, 36, 42, 51, 18),
  (5662, 0, 73, 18, 3, 11, 2, 23, 70, 15, 15),
  (5663, 1, 11, 8, 74, 18, 1, 27, 66, 24, 16),
  (5664, 1, 26, 69, 15, 15, 1, 66, 9, 35, 15),
  (5665, 2, 10, 74, 9, 14, 2, 40, 59, 24, 16),
  (5666, 0, 29, 60, 35, 17, 0, 53, 16, 51, 17),
  (5667, 0, 31, 59, 35, 17, 2, 5, 75, 3, 13),
  (5668, 1, 31, 48, 49, 18, 1, 37, 61, 24, 16),
  (5669, 0, 38, 39, 52, 18, 1, 17, 7, 73, 18),
  (5670, 0, 33, 66, 15, 15, 2, 39, 54, 35, 17),
  (5671, 1, 7, 54, 52, 18, 1, 38, 65, 0, 13),
  (5672, 0, 0, 14, 74, 18, 0, 16, 54, 50, 18),
  (5673, 2, 6, 70, 27, 16, 2, 15, 72, 16, 15),
  (5674, 2, 24, 7, 71, 18, 2, 24, 71, 7, 14),
  (5675, 0, 27, 61, 35, 17, 0, 31, 67, 15, 15),
  (5676, 1, 21, 7, 72, 18, 3, 8, 65, 37, 17),
  (5677, 0, 58, 3, 48, 16, 1, 17, 69, 25, 16),
  (5678, 0, 26, 51, 49, 18, 0, 33, 58, 35, 17),
  (5679, 3, 21, 6, 72, 18, 3, 21, 54, 48, 18),
  (5680, 0, 60, 44, 12, 14, 1, 7, 70, 27, 16),
  (5681, 0, 17, 64, 36, 17, 0, 24, 8, 71, 18),
  (5682, 0, 53, 32, 43, 17, 0, 61, 44, 5, 13),
  (5683, 0, 7, 75, 3, 13, 1, 52, 36, 41, 17),
  (5684, 0, 8, 54, 52, 18, 0, 12, 8, 74, 18),
  (5685, 0, 28, 50, 49, 18, 0, 65, 4, 38, 15),
  (5686, 0, 49, 6, 57, 17, 0, 49, 42, 39, 17),
  (5687, 1, 31, 10, 68, 18, 1, 50, 7, 56, 17),
  (5688, 1, 41, 33, 54, 18, 3, 61, 10, 43, 16),
  (5689, 0, 60, 8, 45, 16, 4, 42, 23, 58, 18),
  (5690, 0, 29, 68, 15, 15, 0, 37, 64, 15, 15),
  (5691, 0, 19, 73, 1, 13, 0, 47, 59, 1, 13),
  (5692, 1, 25, 67, 24, 16, 1, 37, 15, 64, 18),
  (5693, 0, 8, 70, 27, 16, 1, 41, 23, 59, 18),
  (5694, 0, 22, 53, 49, 18, 0, 25, 62, 35, 17),
  (5695, 1, 3, 70, 28, 16, 1, 27, 8, 70, 18),
  (5696, 0, 32, 64, 24, 16, 0, 64, 40, 0, 12),
  (5697, 0, 1, 64, 40, 17, 0, 32, 68, 7, 14),
  (5698, 0, 45, 48, 37, 17, 1, 0, 64, 40, 17),
  (5699, 0, 3, 73, 19, 15, 0, 35, 57, 35, 17)
  ]

lemma witChunk_109_ok : witChunk_109.all checkWit = true := by
  decide +kernel

lemma witChunk_109_ns :
    witChunk_109.map (fun t => t.1) = (List.range 50).map (· + 5650) := by
  decide +kernel

def witChunk_110 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5700, 0, 4, 70, 28, 16, 3, 8, 73, 17, 15),
  (5701, 0, 12, 74, 9, 14, 0, 30, 65, 24, 16),
  (5702, 0, 7, 73, 18, 15, 0, 18, 7, 73, 18),
  (5703, 1, 24, 70, 15, 15, 1, 66, 7, 36, 15),
  (5704, 1, 50, 41, 39, 17, 5, 6, 73, 17, 15),
  (5705, 0, 40, 36, 53, 18, 2, 62, 22, 37, 16),
  (5706, 0, 59, 47, 4, 13, 3, 66, 6, 36, 15),
  (5707, 0, 51, 9, 55, 17, 1, 6, 65, 38, 17),
  (5708, 1, 59, 4, 47, 16, 2, 50, 56, 8, 14),
  (5709, 0, 53, 14, 52, 17, 1, 9, 55, 51, 18),
  (5710, 0, 18, 69, 25, 16, 0, 30, 69, 7, 14),
  (5711, 3, 8, 75, 2, 13, 3, 42, 52, 35, 17),
  (5712, 1, 42, 61, 15, 15, 1, 66, 25, 27, 15),
  (5713, 0, 33, 68, 0, 13, 0, 60, 32, 33, 16),
  (5714, 0, 35, 67, 0, 13, 0, 47, 57, 16, 15),
  (5715, 0, 11, 65, 37, 17, 0, 27, 69, 15, 15),
  (5716, 0, 28, 66, 24, 16, 0, 36, 62, 24, 16),
  (5717, 0, 18, 73, 8, 14, 0, 20, 54, 49, 18),
  (5718, 0, 7, 65, 38, 17, 0, 38, 65, 7, 14),
  (5719, 1, 14, 65, 36, 17, 1, 26, 71, 0, 13),
  (5720, 0, 12, 70, 26, 16, 1, 10, 73, 17, 15),
  (5721, 0, 14, 7, 74, 18, 0, 14, 55, 50, 18),
  (5722, 0, 31, 69, 0, 13, 0, 51, 39, 40, 17),
  (5723, 0, 23, 63, 35, 17, 0, 63, 35, 23, 15),
  (5724, 1, 39, 40, 51, 18, 1, 41, 21, 60, 18),
  (5725, 0, 37, 66, 0, 13, 0, 54, 45, 28, 16),
  (5726, 0, 10, 55, 51, 18, 0, 38, 41, 51, 18),
  (5727, 1, 35, 12, 66, 18, 3, 13, 74, 8, 14),
  (5728, 1, 1, 53, 54, 18, 1, 19, 6, 73, 18),
  (5729, 0, 0, 52, 55, 18, 0, 2, 53, 54, 18),
  (5730, 0, 37, 56, 35, 17, 0, 59, 43, 20, 15),
  (5731, 0, 75, 5, 9, 11, 1, 10, 75, 2, 13),
  (5732, 0, 36, 44, 50, 18, 0, 48, 58, 8, 14),
  (5733, 0, 28, 70, 7, 14, 0, 62, 17, 40, 16),
  (5734, 0, 75, 3, 10, 11, 1, 44, 50, 36, 17),
  (5735, 1, 16, 74, 1, 13, 1, 42, 63, 0, 13),
  (5736, 0, 56, 50, 10, 14, 0, 64, 38, 14, 14),
  (5737, 0, 52, 48, 27, 16, 2, 2, 10, 75, 18),
  (5738, 0, 67, 15, 32, 15, 0, 75, 7, 8, 11),
  (5739, 0, 11, 73, 17, 15, 0, 67, 17, 31, 15),
  (5740, 1, 7, 8, 75, 18, 1, 25, 53, 48, 18),
  (5741, 0, 0, 70, 29, 16, 0, 4, 10, 75, 18),
  (5742, 0, 6, 9, 75, 18, 0, 30, 9, 69, 18),
  (5743, 1, 40, 54, 35, 17, 7, 4, 75, 2, 13),
  (5744, 1, 35, 46, 49, 18, 1, 43, 62, 7, 14),
  (5745, 0, 40, 64, 7, 14, 0, 70, 19, 22, 14),
  (5746, 0, 15, 65, 36, 17, 0, 39, 65, 0, 13),
  (5747, 0, 67, 13, 33, 15, 0, 75, 1, 11, 11),
  (5748, 0, 28, 8, 70, 18, 0, 32, 10, 68, 18),
  (5749, 1, 1, 11, 75, 18, 1, 1, 75, 11, 14)
  ]

lemma witChunk_110_ok : witChunk_110.all checkWit = true := by
  decide +kernel

lemma witChunk_110_ns :
    witChunk_110.map (fun t => t.1) = (List.range 50).map (· + 5700) := by
  decide +kernel

def witChunk_111 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5750, 0, 2, 11, 75, 18, 0, 2, 75, 11, 14),
  (5751, 1, 23, 6, 72, 18, 1, 23, 54, 48, 18),
  (5752, 0, 60, 6, 46, 16, 1, 2, 65, 39, 17),
  (5753, 0, 8, 8, 75, 18, 0, 42, 25, 58, 18),
  (5754, 2, 0, 11, 75, 18, 2, 0, 75, 11, 14),
  (5755, 0, 3, 65, 39, 17, 0, 75, 9, 7, 11),
  (5756, 1, 5, 55, 52, 18, 1, 41, 37, 52, 18),
  (5757, 0, 70, 29, 4, 12, 1, 9, 7, 75, 18),
  (5758, 0, 57, 50, 3, 13, 2, 25, 63, 34, 17),
  (5759, 1, 11, 56, 50, 18, 3, 28, 69, 14, 15),
  (5760, 2, 62, 12, 42, 16, 2, 62, 42, 12, 14),
  (5761, 0, 6, 75, 10, 14, 0, 69, 30, 10, 13),
  (5762, 0, 21, 64, 35, 17, 0, 53, 12, 53, 17),
  (5763, 0, 55, 23, 47, 17, 1, 44, 60, 15, 15),
  (5764, 1, 15, 56, 49, 18, 1, 23, 72, 7, 14),
  (5765, 0, 6, 55, 52, 18, 0, 20, 6, 73, 18),
  (5766, 0, 17, 74, 1, 13, 0, 26, 7, 71, 18),
  (5767, 1, 15, 74, 8, 14, 1, 31, 50, 48, 18),
  (5768, 0, 16, 6, 74, 18, 0, 40, 18, 62, 18),
  (5769, 0, 0, 12, 75, 18, 0, 42, 33, 54, 18),
  (5770, 0, 27, 71, 0, 13, 0, 55, 21, 48, 17),
  (5771, 0, 39, 55, 35, 17, 0, 67, 21, 29, 15),
  (5772, 1, 21, 55, 48, 18, 2, 18, 56, 48, 18),
  (5773, 1, 57, 41, 29, 16, 1, 61, 31, 33, 16),
  (5774, 0, 10, 7, 75, 18, 0, 42, 23, 59, 18),
  (5775, 5, 12, 66, 35, 17, 5, 60, 42, 19, 15),
  (5776, 0, 24, 68, 24, 16, 0, 40, 60, 24, 16),
  (5777, 0, 41, 64, 0, 13, 0, 50, 51, 26, 16),
  (5778, 0, 67, 35, 8, 13, 2, 8, 75, 9, 14),
  (5779, 0, 55, 27, 45, 17, 1, 30, 61, 34, 17),
  (5780, 0, 12, 56, 50, 18, 0, 60, 34, 32, 16),
  (5781, 0, 16, 70, 25, 16, 0, 49, 4, 58, 17),
  (5782, 0, 42, 63, 7, 14, 0, 70, 21, 21, 14),
  (5783, 1, 14, 73, 16, 15, 1, 50, 55, 16, 15),
  (5784, 0, 68, 34, 2, 12, 1, 11, 6, 75, 18),
  (5785, 0, 58, 39, 30, 16, 2, 35, 66, 14, 15),
  (5786, 0, 51, 7, 56, 17, 0, 53, 36, 41, 17),
  (5787, 0, 47, 47, 37, 17, 0, 55, 19, 49, 17),
  (5788, 1, 7, 56, 51, 18, 1, 31, 8, 69, 18),
  (5789, 0, 26, 53, 48, 18, 1, 9, 75, 9, 14),
  (5790, 0, 73, 10, 19, 13, 2, 57, 47, 18, 15),
  (5791, 1, 8, 66, 37, 17, 1, 43, 24, 58, 18),
  (5792, 0, 28, 52, 48, 18, 1, 17, 5, 74, 18),
  (5793, 0, 1, 76, 4, 13, 0, 16, 56, 49, 18),
  (5794, 1, 0, 76, 4, 13, 2, 4, 71, 27, 16),
  (5795, 0, 23, 71, 15, 15, 0, 43, 61, 15, 15),
  (5796, 0, 16, 74, 8, 14, 0, 24, 6, 72, 18),
  (5797, 0, 73, 12, 18, 13, 1, 5, 71, 27, 16),
  (5798, 0, 42, 35, 53, 18, 0, 62, 27, 35, 16),
  (5799, 3, 17, 4, 74, 18, 3, 20, 65, 34, 17)
  ]

lemma witChunk_111_ok : witChunk_111.all checkWit = true := by
  decide +kernel

lemma witChunk_111_ns :
    witChunk_111.map (fun t => t.1) = (List.range 50).map (· + 5750) := by
  decide +kernel

def witChunk_112 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5800, 1, 9, 71, 26, 16, 1, 42, 53, 35, 17),
  (5801, 0, 8, 56, 51, 18, 0, 40, 40, 51, 18),
  (5802, 0, 53, 52, 17, 15, 0, 55, 29, 44, 17),
  (5803, 0, 51, 41, 39, 17, 1, 4, 76, 3, 13),
  (5804, 3, 21, 4, 73, 18, 3, 21, 56, 47, 18),
  (5805, 0, 12, 6, 75, 18, 0, 30, 51, 48, 18),
  (5806, 0, 6, 71, 27, 16, 0, 9, 66, 37, 17),
  (5807, 3, 2, 76, 3, 13, 3, 37, 46, 48, 18),
  (5808, 0, 76, 4, 4, 10, 1, 27, 6, 71, 18),
  (5809, 0, 24, 72, 7, 14, 0, 25, 72, 0, 13),
  (5810, 0, 5, 76, 3, 13, 0, 15, 73, 16, 15),
  (5811, 0, 19, 65, 35, 17, 1, 20, 72, 15, 15),
  (5812, 0, 76, 0, 6, 10, 1, 55, 52, 9, 14),
  (5813, 0, 22, 55, 48, 18, 0, 36, 46, 49, 18),
  (5814, 0, 55, 17, 50, 17, 0, 62, 11, 43, 16),
  (5815, 1, 22, 73, 0, 13, 1, 39, 14, 64, 18),
  (5816, 1, 35, 10, 67, 18, 1, 41, 17, 62, 18),
  (5817, 0, 10, 71, 26, 16, 2, 3, 66, 38, 17),
  (5818, 0, 43, 63, 0, 13, 1, 4, 66, 38, 17),
  (5819, 0, 75, 13, 5, 11, 1, 71, 10, 26, 14),
  (5820, 3, 64, 41, 5, 13, 5, 9, 75, 8, 14),
  (5821, 0, 13, 66, 36, 17, 0, 22, 69, 24, 16),
  (5822, 0, 41, 54, 35, 17, 0, 63, 37, 22, 15),
  (5823, 3, 50, 44, 37, 17, 3, 64, 35, 22, 15),
  (5824, 1, 14, 75, 1, 13, 1, 46, 59, 15, 15),
  (5825, 0, 5, 66, 38, 17, 0, 5, 74, 18, 15),
  (5826, 2, 56, 51, 9, 14, 2, 60, 3, 47, 16),
  (5827, 1, 52, 40, 39, 17, 1, 59, 38, 30, 16),
  (5828, 0, 32, 50, 48, 18, 1, 1, 71, 28, 16),
  (5829, 0, 2, 71, 28, 16, 0, 44, 62, 7, 14),
  (5830, 1, 24, 64, 34, 17, 1, 56, 24, 46, 17),
  (5831, 1, 8, 74, 17, 15, 1, 56, 22, 47, 17),
  (5832, 0, 0, 54, 54, 18, 1, 9, 57, 50, 18),
  (5833, 2, 0, 71, 28, 16, 2, 27, 70, 14, 15),
  (5834, 0, 67, 7, 36, 15, 3, 6, 76, 2, 13),
  (5835, 0, 55, 31, 43, 17, 1, 35, 48, 48, 18),
  (5836, 1, 25, 5, 72, 18, 1, 61, 33, 32, 16),
  (5837, 0, 42, 37, 52, 18, 0, 60, 46, 11, 14),
  (5838, 0, 1, 74, 19, 15, 0, 2, 55, 53, 18),
  (5839, 1, 0, 74, 19, 15, 1, 16, 66, 35, 17),
  (5840, 0, 20, 56, 48, 18, 5, 19, 70, 23, 16),
  (5841, 0, 29, 62, 34, 17, 0, 62, 29, 34, 16),
  (5842, 1, 56, 20, 48, 17, 2, 0, 55, 53, 18),
  (5843, 0, 63, 43, 5, 13, 0, 67, 25, 27, 15),
  (5844, 0, 76, 8, 2, 10, 1, 17, 57, 48, 18),
  (5845, 0, 33, 60, 34, 17, 0, 48, 54, 25, 16),
  (5846, 0, 9, 74, 17, 15, 0, 14, 5, 75, 18),
  (5847, 3, 52, 41, 38, 17, 7, 9, 58, 48, 18),
  (5848, 1, 31, 66, 23, 16, 1, 37, 11, 66, 18),
  (5849, 0, 10, 57, 50, 18, 0, 30, 7, 70, 18)
  ]

lemma witChunk_112_ok : witChunk_112.all checkWit = true := by
  decide +kernel

lemma witChunk_112_ns :
    witChunk_112.map (fun t => t.1) = (List.range 50).map (· + 5800) := by
  decide +kernel

def witChunk_113 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5850, 0, 21, 72, 15, 15, 0, 45, 60, 15, 15),
  (5851, 0, 15, 75, 1, 13, 0, 51, 57, 1, 13),
  (5852, 1, 5, 7, 76, 18, 1, 35, 64, 23, 16),
  (5853, 0, 53, 38, 40, 17, 0, 61, 46, 4, 13),
  (5854, 0, 27, 63, 34, 17, 0, 54, 47, 27, 16),
  (5855, 1, 19, 4, 74, 18, 3, 5, 6, 76, 18),
  (5856, 0, 4, 8, 76, 18, 0, 4, 56, 52, 18),
  (5857, 0, 60, 36, 31, 16, 2, 18, 74, 7, 14),
  (5858, 0, 23, 73, 0, 13, 1, 56, 28, 44, 17),
  (5859, 1, 30, 69, 14, 15, 1, 68, 12, 33, 15),
  (5860, 1, 1, 9, 76, 18, 1, 13, 75, 8, 14),
  (5861, 0, 2, 9, 76, 18, 0, 6, 7, 76, 18),
  (5862, 0, 14, 71, 25, 16, 0, 22, 73, 7, 14),
  (5863, 1, 7, 6, 76, 18, 1, 56, 18, 49, 17),
  (5864, 0, 40, 42, 50, 18, 1, 41, 41, 50, 18),
  (5865, 0, 58, 49, 10, 14, 0, 64, 40, 13, 14),
  (5866, 0, 69, 32, 9, 13, 0, 75, 15, 4, 11),
  (5867, 0, 59, 45, 19, 15, 1, 22, 65, 34, 17),
  (5868, 1, 15, 4, 75, 18, 1, 75, 4, 15, 12),
  (5869, 0, 45, 62, 0, 13, 1, 37, 63, 23, 16),
  (5870, 0, 17, 66, 35, 17, 0, 38, 45, 49, 18),
  (5871, 1, 75, 10, 12, 12, 3, 44, 61, 14, 15),
  (5872, 1, 55, 46, 27, 16, 1, 63, 26, 35, 16),
  (5873, 2, 8, 5, 76, 18, 2, 10, 58, 49, 18),
  (5874, 2, 4, 57, 51, 18, 2, 9, 67, 36, 17),
  (5875, 0, 51, 5, 57, 17, 1, 50, 3, 58, 17),
  (5876, 0, 0, 10, 76, 18, 0, 8, 6, 76, 18),
  (5877, 0, 18, 57, 48, 18, 0, 25, 64, 34, 17),
  (5878, 0, 1, 66, 39, 17, 0, 55, 33, 42, 17),
  (5879, 1, 0, 66, 39, 17, 1, 63, 12, 42, 16),
  (5880, 0, 52, 50, 26, 16, 1, 18, 73, 15, 15),
  (5881, 2, 16, 71, 24, 16, 2, 19, 66, 34, 17),
  (5882, 0, 51, 55, 16, 15, 1, 28, 70, 14, 15),
  (5883, 0, 43, 53, 35, 17, 0, 67, 5, 37, 15),
  (5884, 1, 9, 5, 76, 18, 1, 27, 68, 23, 16),
  (5885, 0, 14, 75, 8, 14, 0, 26, 5, 72, 18),
  (5886, 0, 6, 57, 51, 18, 0, 42, 39, 51, 18),
  (5887, 1, 3, 76, 10, 14, 1, 10, 67, 36, 17),
  (5888, 1, 11, 58, 49, 18, 1, 19, 74, 7, 14),
  (5889, 0, 37, 58, 34, 17, 6, 4, 5, 76, 18),
  (5890, 2, 49, 59, 0, 13, 4, 9, 76, 1, 13),
  (5891, 0, 59, 49, 3, 13, 0, 71, 27, 11, 13),
  (5892, 0, 4, 76, 10, 14, 0, 20, 4, 74, 18),
  (5893, 1, 45, 29, 55, 18, 1, 69, 29, 17, 14),
  (5894, 0, 51, 43, 38, 17, 0, 62, 31, 33, 16),
  (5895, 1, 15, 58, 48, 18, 1, 48, 58, 15, 15),
  (5896, 1, 6, 67, 37, 17, 1, 37, 67, 6, 14),
  (5897, 0, 0, 76, 11, 14, 0, 16, 4, 75, 18),
  (5898, 0, 53, 8, 55, 17, 0, 55, 13, 52, 17),
  (5899, 1, 31, 6, 70, 18, 1, 31, 70, 6, 14)
  ]

lemma witChunk_113_ok : witChunk_113.all checkWit = true := by
  decide +kernel

lemma witChunk_113_ns :
    witChunk_113.map (fun t => t.1) = (List.range 50).map (· + 5850) := by
  decide +kernel

def witChunk_114 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5900, 1, 53, 55, 8, 14, 1, 71, 4, 29, 14),
  (5901, 0, 10, 5, 76, 18, 0, 13, 74, 16, 15),
  (5902, 2, 31, 62, 33, 17, 2, 57, 23, 46, 17),
  (5903, 3, 5, 72, 26, 16, 3, 45, 34, 52, 18),
  (5904, 0, 36, 48, 48, 18, 0, 52, 56, 8, 14),
  (5905, 0, 73, 0, 24, 13, 0, 73, 24, 0, 11),
  (5906, 0, 11, 67, 36, 17, 0, 47, 49, 36, 17),
  (5907, 0, 7, 67, 37, 17, 0, 67, 37, 7, 13),
  (5908, 0, 60, 2, 48, 16, 1, 7, 76, 9, 14),
  (5909, 0, 12, 58, 49, 18, 0, 28, 54, 47, 18),
  (5910, 0, 23, 65, 34, 17, 0, 26, 55, 47, 18),
  (5911, 1, 7, 72, 26, 16, 1, 63, 28, 34, 16),
  (5912, 1, 14, 67, 35, 17, 3, 23, 57, 46, 18),
  (5913, 2, 48, 55, 24, 16, 2, 60, 1, 48, 16),
  (5914, 1, 20, 66, 34, 17, 1, 52, 42, 38, 17),
  (5915, 0, 19, 73, 15, 15, 0, 47, 59, 15, 15),
  (5916, 1, 75, 0, 17, 12, 3, 29, 4, 71, 18),
  (5917, 0, 21, 74, 0, 13, 1, 25, 69, 23, 16),
  (5918, 0, 30, 53, 47, 18, 0, 30, 67, 23, 16),
  (5919, 3, 16, 67, 34, 17, 3, 44, 53, 34, 17),
  (5920, 0, 76, 12, 0, 10, 1, 29, 71, 6, 14),
  (5921, 0, 8, 76, 9, 14, 0, 24, 4, 73, 18),
  (5922, 2, 17, 75, 0, 13, 2, 24, 3, 73, 18),
  (5923, 0, 75, 17, 3, 11, 1, 12, 76, 1, 13),
  (5924, 0, 8, 72, 26, 16, 0, 16, 58, 48, 18),
  (5925, 0, 20, 74, 7, 14, 0, 73, 20, 14, 13),
  (5926, 0, 39, 57, 34, 17, 1, 56, 32, 42, 17),
  (5927, 1, 56, 50, 17, 15, 1, 62, 41, 20, 15),
  (5928, 0, 8, 58, 50, 18, 1, 21, 3, 74, 18),
  (5929, 0, 4, 72, 27, 16, 2, 43, 54, 34, 17),
  (5930, 0, 47, 61, 0, 13, 0, 53, 40, 39, 17),
  (5931, 0, 55, 35, 41, 17, 0, 63, 39, 21, 15),
  (5932, 1, 11, 72, 25, 16, 1, 51, 52, 25, 16),
  (5933, 0, 77, 2, 0, 9, 1, 41, 43, 49, 18),
  (5934, 0, 50, 53, 25, 16, 2, 15, 74, 15, 15),
  (5935, 1, 56, 14, 51, 17, 1, 67, 38, 0, 12),
  (5936, 0, 12, 4, 76, 18, 0, 44, 20, 60, 18),
  (5937, 0, 28, 68, 23, 16, 0, 29, 70, 14, 15),
  (5938, 2, 16, 75, 7, 14, 2, 52, 51, 25, 16),
  (5939, 0, 15, 67, 35, 17, 1, 2, 67, 38, 17),
  (5940, 0, 64, 20, 38, 16, 2, 30, 54, 46, 18),
  (5941, 0, 18, 71, 24, 16, 0, 46, 57, 24, 16),
  (5942, 0, 3, 67, 38, 17, 0, 22, 57, 47, 18),
  (5943, 1, 39, 46, 48, 18, 3, 20, 73, 14, 15),
  (5944, 0, 60, 38, 30, 16, 1, 2, 77, 3, 13),
  (5945, 0, 0, 56, 53, 18, 0, 42, 41, 50, 18),
  (5946, 0, 13, 76, 1, 13, 0, 53, 56, 1, 13),
  (5947, 0, 3, 77, 3, 13, 1, 42, 55, 34, 17),
  (5948, 1, 41, 13, 64, 18, 2, 10, 76, 8, 14),
  (5949, 0, 64, 22, 37, 16, 1, 45, 21, 59, 18)
  ]

lemma witChunk_114_ok : witChunk_114.all checkWit = true := by
  decide +kernel

lemma witChunk_114_ns :
    witChunk_114.map (fun t => t.1) = (List.range 50).map (· + 5900) := by
  decide +kernel

def witChunk_115 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (5950, 0, 57, 26, 45, 17, 2, 45, 61, 14, 15),
  (5951, 1, 18, 75, 0, 13, 1, 27, 72, 6, 14),
  (5952, 0, 64, 16, 40, 16, 1, 6, 75, 17, 15),
  (5953, 0, 12, 72, 25, 16, 0, 21, 66, 34, 17),
  (5954, 0, 45, 52, 35, 17, 2, 8, 59, 49, 18),
  (5955, 0, 55, 11, 53, 17, 0, 67, 29, 25, 15),
  (5956, 0, 36, 68, 6, 14, 0, 72, 14, 24, 14),
  (5957, 0, 2, 57, 52, 18, 0, 38, 47, 48, 18),
  (5958, 0, 3, 75, 18, 15, 0, 18, 3, 75, 18),
  (5959, 1, 16, 74, 15, 15, 1, 32, 62, 33, 17),
  (5960, 0, 32, 6, 70, 18, 0, 32, 70, 6, 14),
  (5961, 2, 0, 57, 52, 18, 2, 18, 2, 75, 18),
  (5962, 2, 69, 13, 32, 15, 4, 7, 75, 16, 15),
  (5963, 0, 7, 75, 17, 15, 1, 11, 76, 8, 14),
  (5964, 1, 75, 16, 9, 12, 2, 14, 72, 24, 16),
  (5965, 1, 9, 59, 49, 18, 1, 17, 75, 7, 14),
  (5966, 0, 26, 69, 23, 16, 0, 27, 71, 14, 15),
  (5967, 3, 0, 75, 18, 15, 3, 4, 77, 2, 13),
  (5968, 0, 0, 72, 28, 16, 0, 64, 24, 36, 16),
  (5969, 0, 22, 3, 74, 18, 0, 38, 67, 6, 14),
  (5970, 2, 9, 75, 16, 15, 2, 51, 56, 15, 15),
  (5971, 1, 6, 77, 2, 13, 1, 18, 67, 34, 17),
  (5972, 2, 22, 2, 74, 18, 2, 22, 58, 46, 18),
  (5973, 0, 20, 58, 47, 18, 0, 40, 62, 23, 16),
  (5974, 0, 51, 3, 58, 17, 0, 57, 18, 49, 17),
  (5975, 1, 56, 34, 41, 17, 3, 58, 48, 17, 15),
  (5976, 1, 3, 6, 77, 18, 1, 3, 58, 51, 18),
  (5977, 0, 30, 71, 6, 14, 0, 72, 8, 27, 14),
  (5978, 0, 69, 16, 31, 15, 1, 44, 62, 14, 15),
  (5979, 1, 39, 10, 66, 18, 2, 69, 11, 33, 15),
  (5980, 1, 43, 60, 23, 16, 1, 69, 31, 16, 14),
  (5981, 0, 4, 6, 77, 18, 0, 4, 58, 51, 18),
  (5982, 0, 2, 7, 77, 18, 0, 7, 77, 2, 13),
  (5983, 1, 10, 75, 16, 15, 1, 27, 56, 46, 18),
  (5984, 0, 12, 76, 8, 14, 0, 28, 4, 72, 18),
  (5985, 0, 62, 5, 46, 16, 0, 69, 18, 30, 15),
  (5986, 0, 19, 75, 0, 13, 1, 8, 68, 36, 17),
  (5987, 1, 15, 72, 24, 16, 1, 36, 60, 33, 17),
  (5988, 1, 45, 19, 60, 18, 3, 5, 4, 77, 18),
  (5989, 1, 69, 35, 1, 12, 2, 6, 4, 77, 18),
  (5990, 0, 6, 5, 77, 18, 0, 17, 74, 15, 15),
  (5991, 3, 58, 20, 47, 17, 5, 15, 60, 46, 18),
  (5992, 0, 40, 66, 6, 14, 0, 72, 18, 22, 14),
  (5993, 0, 0, 8, 77, 18, 0, 46, 31, 54, 18),
  (5994, 0, 55, 37, 40, 17, 0, 69, 12, 33, 15),
  (5995, 0, 51, 45, 37, 17, 1, 12, 68, 35, 17),
  (5996, 1, 7, 4, 77, 18, 3, 13, 60, 47, 18),
  (5997, 0, 58, 43, 28, 16, 0, 64, 26, 35, 16),
  (5998, 0, 18, 75, 7, 14, 0, 57, 30, 43, 17),
  (5999, 3, 48, 59, 14, 15, 3, 50, 0, 59, 17)
  ]

lemma witChunk_115_ok : witChunk_115.all checkWit = true := by
  decide +kernel

lemma witChunk_115_ns :
    witChunk_115.map (fun t => t.1) = (List.range 50).map (· + 5950) := by
  decide +kernel

def witChunk_116 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6000, 2, 50, 54, 24, 16, 4, 8, 60, 48, 18),
  (6001, 0, 9, 68, 36, 17, 0, 49, 0, 60, 17),
  (6002, 0, 11, 75, 16, 15, 0, 69, 20, 29, 15),
  (6003, 3, 9, 60, 48, 18, 3, 37, 50, 46, 18),
  (6004, 0, 28, 72, 6, 14, 0, 60, 48, 10, 14),
  (6005, 0, 24, 70, 23, 16, 0, 25, 72, 14, 15),
  (6006, 0, 19, 67, 34, 17, 2, 69, 9, 34, 15),
  (6007, 1, 15, 2, 76, 18, 1, 50, 47, 36, 17),
  (6008, 0, 76, 6, 14, 12, 1, 5, 59, 50, 18),
  (6009, 0, 8, 4, 77, 18, 0, 46, 23, 58, 18),
  (6010, 0, 63, 45, 4, 13, 1, 44, 54, 34, 17),
  (6011, 0, 67, 1, 39, 15, 1, 4, 68, 37, 17),
  (6012, 1, 41, 45, 48, 18, 2, 10, 60, 48, 18),
  (6013, 1, 21, 71, 23, 16, 1, 77, 9, 1, 10),
  (6014, 0, 18, 59, 47, 18, 0, 26, 3, 73, 18),
  (6015, 1, 75, 18, 8, 12, 3, 2, 68, 37, 17),
  (6016, 0, 16, 72, 24, 16, 0, 48, 56, 24, 16),
  (6017, 0, 6, 59, 50, 18, 0, 53, 42, 38, 17),
  (6018, 0, 5, 68, 37, 17, 0, 13, 68, 35, 17),
  (6019, 0, 31, 63, 33, 17, 1, 63, 32, 32, 16),
  (6020, 0, 40, 46, 48, 18, 0, 76, 10, 12, 12),
  (6021, 1, 9, 3, 77, 18, 2, 36, 51, 46, 18),
  (6022, 0, 33, 62, 33, 17, 0, 55, 9, 54, 17),
  (6023, 1, 24, 66, 33, 17, 1, 47, 26, 56, 18),
  (6024, 1, 35, 6, 69, 18, 3, 23, 1, 74, 18),
  (6025, 0, 42, 65, 6, 14, 0, 72, 20, 21, 14),
  (6026, 0, 29, 64, 33, 17, 0, 67, 31, 24, 15),
  (6027, 1, 11, 60, 48, 18, 1, 47, 30, 54, 18),
  (6028, 1, 61, 1, 48, 16, 1, 63, 44, 11, 14),
  (6029, 0, 20, 2, 75, 18, 0, 42, 13, 64, 18),
  (6030, 0, 43, 55, 34, 17, 0, 50, 59, 7, 14),
  (6031, 1, 48, 50, 35, 17, 1, 58, 19, 48, 17),
  (6032, 1, 1, 77, 10, 14, 1, 5, 73, 26, 16),
  (6033, 0, 2, 77, 10, 14, 0, 52, 52, 25, 16),
  (6034, 0, 61, 48, 3, 13, 1, 16, 76, 0, 13),
  (6035, 0, 35, 61, 33, 17, 0, 47, 51, 35, 17),
  (6036, 0, 16, 2, 76, 18, 0, 28, 56, 46, 18),
  (6037, 0, 57, 32, 42, 17, 1, 5, 77, 9, 14),
  (6038, 0, 10, 3, 77, 18, 0, 46, 21, 59, 18),
  (6039, 3, 58, 16, 49, 17, 3, 65, 14, 40, 16),
  (6040, 1, 21, 59, 46, 18, 3, 19, 75, 6, 14),
  (6041, 0, 6, 73, 26, 16, 0, 26, 57, 46, 18),
  (6042, 0, 77, 8, 7, 11, 1, 60, 46, 18, 15),
  (6043, 0, 27, 65, 33, 17, 1, 23, 74, 6, 14),
  (6044, 1, 37, 7, 68, 18, 1, 47, 32, 53, 18),
  (6045, 0, 46, 35, 52, 18, 0, 64, 10, 43, 16),
  (6046, 0, 6, 77, 9, 14, 0, 57, 14, 51, 17),
  (6047, 1, 35, 52, 46, 18, 1, 56, 10, 53, 17),
  (6048, 0, 12, 60, 48, 18, 1, 14, 75, 15, 15),
  (6049, 0, 73, 24, 12, 13, 2, 54, 50, 25, 16)
  ]

lemma witChunk_116_ok : witChunk_116.all checkWit = true := by
  decide +kernel

lemma witChunk_116_ns :
    witChunk_116.map (fun t => t.1) = (List.range 50).map (· + 6000) := by
  decide +kernel

def witChunk_117 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6050, 0, 63, 41, 20, 15, 0, 69, 8, 35, 15),
  (6051, 0, 11, 77, 1, 13, 0, 55, 55, 1, 13),
  (6052, 1, 7, 60, 49, 18, 1, 15, 76, 7, 14),
  (6053, 2, 68, 35, 14, 14, 2, 76, 13, 10, 12),
  (6054, 0, 10, 73, 25, 16, 0, 22, 71, 23, 16),
  (6055, 1, 40, 58, 33, 17, 1, 56, 54, 1, 13),
  (6056, 0, 24, 2, 74, 18, 0, 24, 58, 46, 18),
  (6057, 2, 12, 73, 24, 16, 2, 75, 10, 18, 13),
  (6058, 0, 37, 60, 33, 17, 2, 75, 8, 19, 13),
  (6059, 1, 47, 22, 58, 18, 2, 29, 71, 13, 15),
  (6060, 3, 7, 77, 8, 14, 5, 3, 60, 49, 18),
  (6061, 1, 1, 73, 27, 16, 2, 24, 1, 74, 18),
  (6062, 0, 2, 73, 27, 16, 0, 62, 3, 47, 16),
  (6063, 3, 74, 20, 13, 13, 7, 12, 75, 14, 15),
  (6064, 1, 22, 67, 33, 17, 1, 27, 2, 73, 18),
  (6065, 0, 8, 60, 49, 18, 0, 16, 60, 47, 18),
  (6066, 0, 69, 24, 27, 15, 2, 0, 73, 27, 16),
  (6067, 0, 55, 39, 39, 17, 0, 75, 9, 19, 13),
  (6068, 0, 0, 58, 52, 18, 0, 44, 64, 6, 14),
  (6069, 0, 1, 68, 38, 17, 0, 17, 68, 34, 17),
  (6070, 0, 25, 66, 33, 17, 0, 75, 11, 18, 13),
  (6071, 1, 31, 68, 22, 16, 1, 47, 34, 52, 18),
  (6072, 0, 76, 14, 10, 12, 3, 23, 71, 22, 16),
  (6073, 2, 26, 58, 45, 18, 2, 48, 25, 56, 18),
  (6074, 0, 53, 4, 57, 17, 0, 75, 7, 20, 13),
  (6075, 0, 15, 75, 15, 15, 0, 51, 57, 15, 15),
  (6076, 1, 9, 77, 8, 14, 1, 13, 73, 24, 16),
  (6077, 0, 12, 2, 77, 18, 0, 46, 19, 60, 18),
  (6078, 2, 61, 45, 18, 15, 3, 50, 58, 14, 15),
  (6079, 1, 19, 60, 46, 18, 1, 54, 5, 56, 17),
  (6080, 1, 37, 65, 22, 16, 2, 34, 4, 70, 18),
  (6081, 0, 16, 76, 7, 14, 0, 22, 59, 46, 18),
  (6082, 0, 51, 59, 0, 13, 2, 3, 76, 17, 15),
  (6083, 0, 51, 1, 59, 17, 0, 71, 31, 9, 13),
  (6084, 3, 21, 0, 75, 18, 3, 21, 60, 45, 18),
  (6085, 0, 64, 30, 33, 16, 1, 1, 59, 51, 18),
  (6086, 0, 2, 59, 51, 18, 0, 46, 37, 51, 18),
  (6087, 1, 78, 1, 0, 9, 3, 2, 76, 17, 15),
  (6088, 0, 24, 74, 6, 14, 0, 72, 2, 30, 14),
  (6089, 2, 7, 76, 16, 15, 2, 31, 64, 32, 17),
  (6090, 0, 5, 76, 17, 15, 0, 55, 53, 16, 15),
  (6091, 0, 39, 59, 33, 17, 0, 75, 5, 21, 13),
  (6092, 1, 47, 20, 59, 18, 3, 7, 61, 48, 18),
  (6093, 0, 10, 77, 8, 14, 0, 30, 3, 72, 18),
  (6094, 0, 1, 78, 3, 13, 2, 13, 69, 34, 17),
  (6095, 1, 0, 78, 3, 13, 1, 6, 69, 36, 17),
  (6096, 0, 64, 8, 44, 16, 1, 45, 15, 62, 18),
  (6097, 0, 45, 54, 34, 17, 0, 57, 12, 52, 17),
  (6098, 0, 77, 12, 5, 11, 1, 8, 76, 16, 15),
  (6099, 0, 55, 7, 55, 17, 5, 18, 37, 66, 19)
  ]

lemma witChunk_117_ok : witChunk_117.all checkWit = true := by
  decide +kernel

lemma witChunk_117_ns :
    witChunk_117.map (fun t => t.1) = (List.range 50).map (· + 6050) := by
  decide +kernel

def witChunk_118 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6100, 2, 42, 62, 22, 16, 4, 16, 76, 6, 14),
  (6101, 0, 1, 76, 18, 15, 0, 14, 73, 24, 16),
  (6102, 1, 0, 76, 18, 15, 1, 48, 60, 14, 15),
  (6103, 1, 39, 64, 22, 16, 1, 56, 38, 39, 17),
  (6104, 1, 21, 75, 6, 14, 1, 25, 1, 74, 18),
  (6105, 2, 3, 78, 2, 13, 2, 34, 54, 45, 18),
  (6106, 0, 7, 69, 36, 17, 0, 51, 47, 36, 17),
  (6107, 0, 11, 69, 35, 17, 0, 23, 67, 33, 17),
  (6108, 1, 9, 61, 48, 18, 1, 47, 36, 51, 18),
  (6109, 0, 78, 3, 4, 10, 1, 45, 41, 49, 18),
  (6110, 0, 22, 1, 75, 18, 0, 42, 11, 65, 18),
  (6111, 1, 3, 4, 78, 18, 1, 3, 60, 50, 18),
  (6112, 1, 1, 5, 78, 18, 1, 30, 71, 13, 15),
  (6113, 0, 2, 5, 78, 18, 0, 5, 78, 2, 13),
  (6114, 0, 53, 44, 37, 17, 2, 57, 51, 16, 15),
  (6115, 1, 14, 69, 34, 17, 1, 20, 68, 33, 17),
  (6116, 0, 4, 4, 78, 18, 0, 4, 60, 50, 18),
  (6117, 0, 28, 2, 73, 18, 0, 38, 7, 68, 18),
  (6118, 0, 58, 45, 27, 16, 0, 75, 3, 22, 13),
  (6119, 3, 1, 4, 78, 18, 3, 1, 60, 50, 18),
  (6120, 0, 0, 6, 78, 18, 0, 48, 30, 54, 18),
  (6121, 0, 46, 63, 6, 14, 0, 72, 24, 19, 14),
  (6122, 2, 16, 73, 23, 16, 2, 28, 1, 73, 18),
  (6123, 2, 69, 27, 25, 15, 3, 16, 35, 68, 19),
  (6124, 1, 31, 56, 45, 18, 1, 57, 53, 8, 14),
  (6125, 0, 10, 61, 48, 18, 2, 40, 49, 46, 18),
  (6126, 0, 14, 1, 77, 18, 0, 14, 61, 47, 18),
  (6127, 1, 14, 77, 0, 13, 1, 40, 66, 13, 15),
  (6128, 1, 17, 61, 46, 18, 1, 50, 49, 35, 17),
  (6129, 0, 6, 3, 78, 18, 0, 34, 67, 22, 16),
  (6130, 2, 11, 76, 15, 15, 2, 12, 77, 7, 14),
  (6131, 0, 59, 21, 47, 17, 0, 59, 25, 45, 17),
  (6132, 0, 32, 68, 22, 16, 1, 69, 37, 0, 12),
  (6133, 1, 25, 59, 45, 18, 1, 73, 19, 21, 14),
  (6134, 0, 41, 58, 33, 17, 2, 61, 49, 2, 13),
  (6135, 1, 47, 18, 60, 18, 3, 16, 31, 70, 19),
  (6136, 0, 36, 66, 22, 16, 1, 2, 69, 37, 17),
  (6137, 0, 46, 39, 50, 18, 0, 48, 32, 53, 18),
  (6138, 2, 36, 53, 45, 18, 2, 48, 35, 51, 18),
  (6139, 0, 3, 69, 37, 17, 0, 75, 17, 15, 13),
  (6140, 1, 73, 5, 28, 14, 2, 58, 52, 8, 14),
  (6141, 0, 77, 14, 4, 11, 1, 33, 3, 71, 18),
  (6142, 0, 15, 69, 34, 17, 0, 54, 51, 25, 16),
  (6143, 1, 35, 4, 70, 18, 3, 20, 37, 66, 19),
  (6144, 0, 64, 32, 32, 16, 2, 18, 76, 6, 14),
  (6145, 0, 22, 75, 6, 14, 0, 30, 69, 22, 16),
  (6146, 0, 59, 19, 48, 17, 0, 59, 27, 44, 17),
  (6147, 1, 12, 76, 15, 15, 1, 18, 75, 14, 15),
  (6148, 0, 60, 42, 28, 16, 1, 59, 44, 27, 16),
  (6149, 0, 62, 1, 48, 16, 1, 5, 61, 49, 18)
  ]

lemma witChunk_118_ok : witChunk_118.all checkWit = true := by
  decide +kernel

lemma witChunk_118_ns :
    witChunk_118.map (fun t => t.1) = (List.range 50).map (· + 6100) := by
  decide +kernel

def witChunk_119 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6150, 0, 55, 41, 38, 17, 2, 15, 34, 69, 19),
  (6151, 1, 8, 78, 1, 13, 1, 30, 65, 32, 17),
  (6152, 0, 8, 2, 78, 18, 0, 48, 22, 58, 18),
  (6153, 0, 26, 1, 74, 18, 0, 38, 65, 22, 16),
  (6154, 0, 15, 77, 0, 13, 0, 21, 68, 33, 17),
  (6155, 0, 35, 69, 13, 15, 0, 75, 1, 23, 13),
  (6156, 1, 15, 0, 77, 18, 1, 23, 0, 75, 18),
  (6157, 0, 64, 6, 45, 16, 1, 33, 71, 5, 14),
  (6158, 0, 6, 61, 49, 18, 0, 33, 70, 13, 15),
  (6159, 3, 20, 29, 70, 19, 3, 29, 58, 44, 18),
  (6160, 1, 42, 65, 13, 15, 1, 49, 29, 54, 18),
  (6161, 0, 18, 61, 46, 18, 0, 38, 51, 46, 18),
  (6162, 0, 37, 68, 13, 15, 2, 21, 33, 68, 19),
  (6163, 1, 3, 74, 26, 16, 1, 44, 56, 33, 17),
  (6164, 0, 48, 34, 52, 18, 0, 76, 18, 8, 12),
  (6165, 0, 8, 74, 25, 16, 1, 45, 13, 63, 18),
  (6166, 0, 9, 78, 1, 13, 0, 57, 54, 1, 13),
  (6167, 1, 54, 57, 0, 13, 1, 63, 36, 30, 16),
  (6168, 0, 4, 74, 26, 16, 0, 28, 70, 22, 16),
  (6169, 2, 19, 30, 70, 19, 2, 19, 38, 66, 19),
  (6170, 0, 13, 76, 15, 15, 0, 53, 56, 15, 15),
  (6171, 0, 31, 71, 13, 15, 0, 59, 17, 49, 17),
  (6172, 1, 31, 72, 5, 14, 1, 39, 68, 5, 14),
  (6173, 0, 28, 58, 45, 18, 0, 53, 58, 0, 13),
  (6174, 0, 14, 77, 7, 14, 0, 30, 57, 45, 18),
  (6175, 1, 11, 74, 24, 16, 1, 16, 34, 69, 19),
  (6176, 0, 20, 0, 76, 18, 0, 44, 12, 64, 18),
  (6177, 0, 53, 2, 58, 17, 0, 65, 44, 4, 13),
  (6178, 1, 16, 36, 68, 19, 2, 44, 45, 47, 18),
  (6179, 0, 39, 67, 13, 15, 0, 63, 43, 19, 15),
  (6180, 0, 40, 64, 22, 16, 1, 45, 43, 48, 18),
  (6181, 0, 4, 78, 9, 14, 0, 60, 50, 9, 14),
  (6182, 0, 18, 73, 23, 16, 0, 19, 75, 14, 15),
  (6183, 1, 39, 6, 68, 18, 3, 9, 0, 78, 18),
  (6184, 0, 0, 78, 10, 14, 0, 48, 62, 6, 14),
  (6185, 0, 10, 1, 78, 18, 0, 16, 0, 77, 18),
  (6186, 0, 55, 5, 56, 17, 2, 11, 36, 69, 19),
  (6187, 0, 43, 57, 33, 17, 0, 63, 47, 3, 13),
  (6188, 1, 47, 16, 61, 18, 1, 61, 41, 28, 16),
  (6189, 1, 21, 61, 45, 18, 2, 15, 40, 66, 19),
  (6190, 2, 21, 29, 70, 19, 4, 11, 41, 66, 19),
  (6191, 1, 8, 70, 35, 17, 1, 14, 37, 68, 19),
  (6192, 2, 6, 62, 48, 18, 2, 6, 78, 8, 14),
  (6193, 4, 14, 77, 6, 14, 6, 19, 24, 72, 19),
  (6194, 0, 29, 72, 13, 15, 0, 71, 33, 8, 13),
  (6195, 0, 67, 41, 5, 13, 1, 60, 48, 17, 15),
  (6196, 0, 12, 74, 24, 16, 0, 52, 54, 24, 16),
  (6197, 0, 12, 62, 47, 18, 0, 48, 58, 23, 16),
  (6198, 0, 46, 41, 49, 18, 0, 67, 35, 22, 15),
  (6199, 1, 7, 62, 48, 18, 1, 7, 78, 8, 14)
  ]

lemma witChunk_119_ok : witChunk_119.all checkWit = true := by
  decide +kernel

lemma witChunk_119_ns :
    witChunk_119.map (fun t => t.1) = (List.range 50).map (· + 6150) := by
  decide +kernel

def witChunk_120 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6200, 1, 14, 31, 71, 19, 1, 22, 35, 67, 19),
  (6201, 0, 0, 60, 51, 18, 0, 24, 0, 75, 18),
  (6202, 1, 12, 34, 70, 19, 1, 12, 70, 34, 17),
  (6203, 1, 12, 36, 69, 19, 1, 18, 39, 66, 19),
  (6204, 2, 54, 52, 24, 16, 2, 70, 36, 0, 12),
  (6205, 0, 0, 74, 27, 16, 0, 78, 11, 0, 10),
  (6206, 0, 9, 70, 35, 17, 0, 17, 34, 69, 19),
  (6207, 1, 11, 0, 78, 18, 1, 27, 0, 74, 18),
  (6208, 1, 14, 39, 67, 19, 1, 18, 29, 71, 19),
  (6209, 0, 17, 36, 68, 19, 0, 33, 64, 32, 17),
  (6210, 0, 19, 35, 68, 19, 0, 31, 65, 32, 17),
  (6211, 0, 15, 35, 69, 19, 0, 19, 33, 69, 19),
  (6212, 0, 8, 62, 48, 18, 0, 8, 78, 8, 14),
  (6213, 0, 17, 32, 70, 19, 0, 64, 34, 31, 16),
  (6214, 0, 15, 33, 70, 19, 0, 54, 57, 7, 14),
  (6215, 3, 26, 36, 65, 19, 3, 49, 36, 50, 18),
  (6216, 0, 16, 62, 46, 18, 0, 40, 50, 46, 18),
  (6217, 0, 42, 63, 22, 16, 2, 32, 1, 72, 18),
  (6218, 0, 15, 37, 68, 19, 0, 35, 63, 32, 17),
  (6219, 0, 19, 37, 67, 19, 2, 9, 33, 71, 19),
  (6220, 2, 26, 60, 44, 18, 2, 50, 24, 56, 18),
  (6221, 0, 5, 70, 36, 17, 0, 21, 34, 68, 19),
  (6222, 0, 17, 38, 67, 19, 0, 19, 31, 70, 19),
  (6223, 1, 6, 77, 16, 15, 1, 14, 29, 72, 19),
  (6224, 1, 1, 61, 50, 18, 1, 2, 77, 17, 15),
  (6225, 0, 2, 61, 50, 18, 0, 13, 34, 70, 19),
  (6226, 0, 13, 36, 69, 19, 0, 21, 32, 69, 19),
  (6227, 0, 3, 77, 17, 15, 0, 15, 31, 71, 19),
  (6228, 0, 12, 0, 78, 18, 0, 48, 18, 60, 18),
  (6229, 0, 57, 8, 54, 17, 1, 49, 35, 51, 18),
  (6230, 0, 17, 30, 71, 19, 0, 22, 61, 45, 18),
  (6231, 3, 10, 28, 73, 19, 3, 34, 64, 31, 17),
  (6232, 1, 10, 33, 71, 19, 1, 10, 37, 69, 19),
  (6233, 0, 32, 72, 5, 14, 0, 74, 9, 26, 14),
  (6234, 0, 7, 77, 16, 15, 0, 13, 32, 71, 19),
  (6235, 0, 15, 39, 67, 19, 0, 75, 21, 13, 13),
  (6236, 2, 34, 56, 44, 18, 2, 50, 32, 52, 18),
  (6237, 0, 13, 38, 68, 19, 0, 36, 54, 45, 18),
  (6238, 0, 19, 39, 66, 19, 2, 15, 26, 73, 19),
  (6239, 1, 18, 27, 72, 19, 1, 24, 30, 69, 19),
  (6240, 3, 47, 13, 62, 18, 3, 67, 17, 38, 16),
  (6241, 0, 21, 30, 70, 19, 0, 21, 38, 66, 19),
  (6242, 0, 23, 33, 68, 19, 0, 27, 67, 32, 17),
  (6243, 0, 19, 29, 71, 19, 0, 23, 35, 67, 19),
  (6244, 0, 24, 72, 22, 16, 1, 45, 11, 64, 18),
  (6245, 0, 17, 40, 66, 19, 1, 49, 19, 59, 18),
  (6246, 0, 11, 35, 70, 19, 3, 14, 44, 64, 19),
  (6247, 1, 10, 31, 72, 19, 1, 10, 39, 68, 19),
  (6248, 0, 48, 38, 50, 18, 4, 16, 74, 22, 16),
  (6249, 0, 40, 68, 5, 14, 0, 58, 47, 26, 16)
  ]

lemma witChunk_120_ok : witChunk_120.all checkWit = true := by
  decide +kernel

lemma witChunk_120_ns :
    witChunk_120.map (fun t => t.1) = (List.range 50).map (· + 6200) := by
  decide +kernel

def witChunk_121 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6250, 0, 15, 29, 72, 19, 0, 45, 56, 33, 17),
  (6251, 0, 11, 33, 71, 19, 0, 11, 37, 69, 19),
  (6252, 1, 39, 52, 45, 18, 3, 8, 29, 73, 19),
  (6253, 0, 13, 30, 72, 19, 0, 13, 78, 0, 13),
  (6254, 0, 2, 3, 79, 18, 0, 3, 79, 2, 13),
  (6255, 3, 58, 8, 53, 17, 5, 51, 30, 52, 18),
  (6256, 1, 3, 2, 79, 18, 1, 3, 62, 49, 18),
  (6257, 0, 0, 4, 79, 18, 0, 17, 28, 72, 19),
  (6258, 0, 13, 40, 67, 19, 2, 0, 3, 79, 18),
  (6259, 1, 12, 28, 73, 19, 1, 26, 35, 66, 19),
  (6260, 0, 28, 0, 74, 18, 0, 40, 6, 68, 18),
  (6261, 0, 4, 2, 79, 18, 0, 4, 62, 49, 18),
  (6262, 0, 15, 41, 66, 19, 1, 8, 36, 70, 19),
  (6263, 1, 8, 34, 71, 19, 1, 16, 26, 73, 19),
  (6264, 0, 44, 62, 22, 16, 3, 1, 2, 79, 18),
  (6265, 0, 60, 44, 27, 16, 2, 7, 32, 72, 19),
  (6266, 0, 11, 31, 72, 19, 0, 11, 39, 68, 19),
  (6267, 0, 19, 41, 65, 19, 1, 27, 60, 44, 18),
  (6268, 1, 51, 56, 23, 16, 1, 67, 16, 39, 16),
  (6269, 0, 20, 62, 45, 18, 0, 46, 43, 48, 18),
  (6270, 0, 1, 70, 37, 17, 0, 23, 29, 70, 19),
  (6271, 1, 0, 70, 37, 17, 1, 8, 38, 69, 19),
  (6272, 1, 10, 29, 73, 19, 1, 10, 41, 67, 19),
  (6273, 0, 25, 32, 68, 19, 0, 25, 68, 32, 17),
  (6274, 0, 19, 27, 72, 19, 0, 55, 57, 0, 13),
  (6275, 0, 11, 77, 15, 15, 0, 23, 39, 65, 19),
  (6276, 1, 33, 1, 72, 18, 1, 33, 57, 44, 18),
  (6277, 0, 9, 36, 70, 19, 0, 12, 78, 7, 14),
  (6278, 0, 6, 1, 79, 18, 0, 9, 34, 71, 19),
  (6279, 1, 47, 42, 48, 18, 1, 56, 54, 15, 15),
  (6280, 1, 6, 79, 1, 13, 1, 18, 25, 73, 19),
  (6281, 0, 14, 63, 46, 18, 0, 42, 49, 46, 18),
  (6282, 0, 13, 28, 73, 19, 0, 69, 0, 39, 15),
  (6283, 0, 15, 27, 73, 19, 0, 55, 3, 57, 17),
  (6284, 1, 9, 75, 24, 16, 1, 25, 61, 44, 18),
  (6285, 0, 28, 74, 5, 14, 0, 74, 5, 28, 14),
  (6286, 0, 6, 75, 25, 16, 0, 9, 38, 69, 19),
  (6287, 1, 67, 14, 40, 16, 3, 8, 27, 74, 19),
  (6288, 2, 66, 30, 32, 16, 3, 49, 62, 5, 14),
  (6289, 0, 9, 32, 72, 19, 0, 13, 42, 66, 19),
  (6290, 0, 45, 64, 13, 15, 0, 53, 0, 59, 17),
  (6291, 0, 7, 79, 1, 13, 0, 11, 29, 73, 19),
  (6292, 0, 64, 36, 30, 16, 1, 7, 0, 79, 18),
  (6293, 0, 50, 33, 52, 18, 0, 57, 40, 38, 17),
  (6294, 0, 17, 26, 73, 19, 0, 25, 38, 65, 19),
  (6295, 1, 8, 30, 73, 19, 1, 22, 25, 72, 19),
  (6296, 0, 76, 22, 6, 12, 1, 73, 31, 2, 12),
  (6297, 0, 22, 73, 22, 16, 2, 4, 63, 48, 18),
  (6298, 0, 75, 23, 12, 13, 1, 12, 26, 74, 19),
  (6299, 0, 15, 43, 65, 19, 0, 23, 27, 71, 19)
  ]

lemma witChunk_121_ok : witChunk_121.all checkWit = true := by
  decide +kernel

lemma witChunk_121_ns :
    witChunk_121.map (fun t => t.1) = (List.range 50).map (· + 6250) := by
  decide +kernel

def witChunk_122 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6300, 1, 5, 63, 48, 18, 1, 39, 4, 69, 18),
  (6301, 0, 10, 75, 24, 16, 0, 21, 26, 72, 19),
  (6302, 0, 42, 7, 67, 18, 0, 78, 7, 13, 12),
  (6303, 1, 51, 28, 54, 18, 3, 4, 37, 70, 19),
  (6304, 1, 1, 75, 26, 16, 1, 6, 35, 71, 19),
  (6305, 0, 2, 75, 26, 16, 0, 8, 0, 79, 18),
  (6306, 0, 19, 43, 64, 19, 0, 23, 41, 64, 19),
  (6307, 0, 27, 33, 67, 19, 1, 6, 37, 70, 19),
  (6308, 1, 79, 8, 1, 10, 3, 13, 64, 45, 18),
  (6309, 0, 6, 63, 48, 18, 0, 25, 28, 70, 19),
  (6310, 0, 9, 30, 73, 19, 0, 27, 35, 66, 19),
  (6311, 1, 6, 33, 72, 19, 1, 23, 62, 44, 18),
  (6312, 0, 64, 46, 10, 14, 1, 51, 30, 53, 18),
  (6313, 2, 20, 63, 44, 18, 2, 27, 26, 70, 19),
  (6314, 0, 23, 69, 32, 17, 0, 27, 31, 68, 19),
  (6315, 0, 7, 35, 71, 19, 0, 7, 71, 35, 17),
  (6316, 1, 67, 12, 41, 16, 3, 4, 39, 69, 19),
  (6317, 0, 30, 59, 44, 18, 0, 44, 66, 5, 14),
  (6318, 0, 7, 37, 70, 19, 0, 11, 71, 34, 17),
  (6319, 1, 8, 42, 67, 19, 1, 14, 45, 64, 19),
  (6320, 0, 28, 60, 44, 18, 1, 6, 39, 69, 19),
  (6321, 0, 13, 26, 74, 19, 0, 17, 44, 64, 19),
  (6322, 0, 7, 33, 72, 19, 0, 61, 24, 45, 17),
  (6323, 0, 23, 75, 13, 15, 0, 27, 37, 65, 19),
  (6324, 0, 32, 58, 44, 18, 1, 47, 12, 63, 18),
  (6325, 1, 1, 79, 9, 14, 1, 13, 75, 23, 16),
  (6326, 0, 2, 79, 9, 14, 0, 11, 27, 74, 19),
  (6327, 3, 16, 47, 62, 19, 3, 28, 25, 70, 19),
  (6328, 1, 6, 31, 73, 19, 1, 14, 71, 33, 17),
  (6329, 0, 40, 52, 45, 18, 2, 4, 79, 8, 14),
  (6330, 0, 13, 44, 65, 19, 0, 61, 20, 47, 17),
  (6331, 0, 7, 39, 69, 19, 0, 27, 29, 69, 19),
  (6332, 1, 5, 79, 8, 14, 1, 23, 76, 5, 14),
  (6333, 0, 26, 61, 44, 18, 0, 46, 11, 64, 18),
  (6334, 0, 9, 42, 67, 19, 2, 39, 62, 31, 17),
  (6335, 1, 11, 64, 46, 18, 3, 20, 21, 74, 19),
  (6336, 1, 51, 22, 57, 18, 2, 66, 6, 44, 16),
  (6337, 2, 58, 54, 7, 14, 4, 14, 75, 22, 16),
  (6338, 0, 23, 25, 72, 19, 0, 53, 48, 35, 17),
  (6339, 0, 7, 31, 73, 19, 0, 79, 7, 7, 11),
  (6340, 0, 52, 60, 6, 14, 0, 72, 30, 16, 14),
  (6341, 0, 6, 79, 8, 14, 0, 9, 28, 74, 19),
  (6342, 0, 25, 26, 71, 19, 0, 50, 19, 59, 18),
  (6343, 1, 2, 71, 36, 17, 1, 6, 41, 68, 19),
  (6344, 0, 0, 62, 50, 18, 0, 48, 14, 62, 18),
  (6345, 2, 27, 42, 62, 19, 2, 62, 42, 27, 16),
  (6346, 0, 3, 71, 36, 17, 0, 15, 45, 64, 19),
  (6347, 0, 23, 43, 63, 19, 0, 47, 63, 13, 15),
  (6348, 1, 15, 64, 45, 18, 1, 21, 63, 44, 18),
  (6349, 0, 61, 18, 48, 17, 1, 41, 65, 21, 16)
  ]

lemma witChunk_122_ok : witChunk_122.all checkWit = true := by
  decide +kernel

lemma witChunk_122_ns :
    witChunk_122.map (fun t => t.1) = (List.range 50).map (· + 6300) := by
  decide +kernel

def witChunk_123 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6350, 0, 14, 75, 23, 16, 0, 15, 77, 14, 15),
  (6351, 1, 38, 69, 12, 15, 1, 72, 18, 29, 15),
  (6352, 1, 10, 25, 75, 19, 1, 10, 45, 65, 19),
  (6353, 0, 29, 34, 66, 19, 0, 32, 0, 73, 18),
  (6354, 0, 7, 41, 68, 19, 0, 29, 32, 67, 19),
  (6355, 0, 15, 71, 33, 17, 0, 19, 45, 63, 19),
  (6356, 0, 12, 64, 46, 18, 0, 24, 62, 44, 18),
  (6357, 2, 3, 34, 72, 19, 2, 3, 78, 16, 15),
  (6358, 0, 25, 42, 63, 19, 0, 27, 27, 70, 19),
  (6359, 3, 2, 36, 71, 19, 3, 32, 31, 66, 19),
  (6360, 0, 20, 74, 22, 16, 1, 51, 34, 51, 18),
  (6361, 0, 36, 68, 21, 16, 2, 3, 38, 70, 19),
  (6362, 0, 5, 36, 71, 19, 0, 11, 79, 0, 13),
  (6363, 1, 54, 57, 14, 15, 1, 68, 36, 21, 15),
  (6364, 1, 67, 28, 33, 16, 2, 18, 64, 44, 18),
  (6365, 0, 5, 34, 72, 19, 0, 5, 78, 16, 15),
  (6366, 0, 7, 29, 74, 19, 0, 19, 23, 74, 19),
  (6367, 1, 8, 26, 75, 19, 1, 16, 22, 75, 19),
  (6368, 0, 36, 56, 44, 18, 0, 60, 52, 8, 14),
  (6369, 0, 5, 38, 70, 19, 0, 8, 64, 47, 18),
  (6370, 0, 13, 24, 75, 19, 1, 40, 68, 12, 15),
  (6371, 0, 11, 25, 75, 19, 0, 11, 45, 65, 19),
  (6372, 0, 48, 42, 48, 18, 3, 4, 43, 67, 19),
  (6373, 0, 9, 44, 66, 19, 1, 1, 63, 49, 18),
  (6374, 0, 1, 78, 17, 15, 0, 2, 63, 49, 18),
  (6375, 1, 0, 78, 17, 15, 1, 8, 78, 15, 15),
  (6376, 0, 16, 78, 6, 14, 1, 6, 43, 67, 19),
  (6377, 0, 16, 64, 45, 18, 0, 24, 76, 5, 14),
  (6378, 0, 5, 32, 73, 19, 0, 61, 16, 49, 17),
  (6379, 0, 15, 23, 75, 19, 0, 27, 41, 63, 19),
  (6380, 3, 32, 37, 63, 19, 3, 65, 36, 29, 16),
  (6381, 0, 13, 46, 64, 19, 0, 29, 38, 64, 19),
  (6382, 0, 9, 26, 75, 19, 0, 30, 71, 21, 16),
  (6383, 3, 2, 40, 69, 19, 3, 77, 20, 6, 12),
  (6384, 2, 74, 0, 30, 14, 2, 74, 24, 18, 14),
  (6385, 0, 25, 24, 72, 19, 0, 57, 56, 0, 13),
  (6386, 0, 5, 40, 69, 19, 0, 21, 76, 13, 15),
  (6387, 0, 7, 43, 67, 19, 0, 23, 23, 73, 19),
  (6388, 0, 48, 60, 22, 16, 1, 43, 64, 21, 16),
  (6389, 0, 22, 63, 44, 18, 0, 50, 17, 60, 18),
  (6390, 0, 9, 78, 15, 15, 0, 10, 79, 7, 14),
  (6391, 1, 18, 71, 32, 17, 1, 24, 22, 73, 19),
  (6392, 0, 60, 46, 26, 16, 0, 68, 18, 38, 16),
  (6393, 0, 68, 20, 37, 16, 2, 3, 30, 74, 19),
  (6394, 1, 4, 30, 74, 19, 1, 28, 42, 62, 19),
  (6395, 0, 27, 25, 71, 19, 0, 71, 27, 25, 15),
  (6396, 2, 6, 76, 24, 16, 3, 16, 49, 61, 19),
  (6397, 0, 40, 66, 21, 16, 1, 21, 77, 5, 14),
  (6398, 0, 17, 22, 75, 19, 0, 23, 45, 62, 19),
  (6399, 1, 42, 67, 12, 15, 1, 51, 36, 50, 18)
  ]

lemma witChunk_123_ok : witChunk_123.all checkWit = true := by
  decide +kernel

lemma witChunk_123_ns :
    witChunk_123.map (fun t => t.1) = (List.range 50).map (· + 6350) := by
  decide +kernel

def witChunk_124 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6400, 0, 64, 0, 48, 16, 1, 17, 75, 22, 16),
  (6401, 0, 5, 30, 74, 19, 0, 21, 22, 74, 19),
  (6402, 1, 80, 0, 0, 9, 2, 11, 48, 63, 19),
  (6403, 0, 7, 27, 75, 19, 0, 15, 47, 63, 19),
  (6404, 0, 0, 2, 80, 18, 0, 52, 28, 54, 18),
  (6405, 0, 1, 80, 2, 13, 0, 2, 1, 80, 18),
  (6406, 0, 31, 33, 66, 19, 0, 33, 66, 31, 17),
  (6407, 1, 8, 46, 65, 19, 1, 10, 23, 76, 19),
  (6408, 1, 51, 18, 59, 18, 1, 77, 21, 6, 12),
  (6409, 0, 28, 72, 21, 16, 2, 0, 1, 80, 18),
  (6410, 0, 29, 40, 63, 19, 0, 35, 71, 12, 15),
  (6411, 0, 31, 31, 67, 19, 0, 31, 35, 65, 19),
  (6412, 1, 3, 76, 25, 16, 1, 31, 60, 43, 18),
  (6413, 0, 5, 42, 68, 19, 0, 37, 70, 12, 15),
  (6414, 0, 19, 47, 62, 19, 0, 49, 62, 13, 15),
  (6415, 1, 2, 35, 72, 19, 1, 14, 21, 76, 19),
  (6416, 0, 4, 0, 80, 18, 0, 4, 64, 48, 18),
  (6417, 0, 4, 76, 25, 16, 0, 29, 26, 70, 19),
  (6418, 0, 3, 35, 72, 19, 1, 8, 24, 76, 19),
  (6419, 0, 3, 37, 71, 19, 0, 71, 3, 37, 15),
  (6420, 0, 68, 14, 40, 16, 0, 80, 2, 4, 10),
  (6421, 0, 9, 72, 34, 17, 1, 13, 65, 45, 18),
  (6422, 0, 9, 46, 65, 19, 0, 27, 43, 62, 19),
  (6423, 3, 2, 80, 1, 13, 3, 26, 20, 73, 19),
  (6424, 1, 2, 33, 73, 19, 1, 9, 65, 46, 18),
  (6425, 0, 48, 64, 5, 14, 0, 68, 24, 35, 16),
  (6426, 0, 5, 80, 1, 13, 0, 11, 23, 76, 19),
  (6427, 0, 3, 33, 73, 19, 0, 19, 21, 75, 19),
  (6428, 1, 11, 76, 23, 16, 1, 37, 71, 4, 14),
  (6429, 0, 13, 22, 76, 19, 2, 12, 79, 6, 14),
  (6430, 0, 3, 39, 70, 19, 0, 7, 45, 66, 19),
  (6431, 3, 2, 28, 75, 19, 3, 2, 72, 35, 17),
  (6432, 0, 20, 64, 44, 18, 0, 52, 32, 52, 18),
  (6433, 0, 9, 24, 76, 19, 0, 18, 75, 22, 16),
  (6434, 0, 5, 28, 75, 19, 0, 5, 72, 35, 17),
  (6435, 2, 21, 19, 75, 19, 2, 33, 37, 63, 19),
  (6436, 1, 33, 73, 4, 14, 3, 0, 33, 73, 19),
  (6437, 0, 17, 48, 62, 19, 0, 52, 22, 57, 18),
  (6438, 0, 22, 77, 5, 14, 0, 25, 22, 73, 19),
  (6439, 1, 6, 25, 76, 19, 1, 24, 70, 31, 17),
  (6440, 0, 80, 6, 2, 10, 1, 35, 58, 43, 18),
  (6441, 0, 10, 65, 46, 18, 0, 46, 47, 46, 18),
  (6442, 0, 13, 48, 63, 19, 0, 13, 72, 33, 17),
  (6443, 1, 2, 31, 74, 19, 1, 4, 44, 67, 19),
  (6444, 3, 32, 41, 61, 19, 3, 51, 15, 60, 18),
  (6445, 1, 25, 63, 43, 18, 2, 31, 24, 70, 19),
  (6446, 0, 3, 31, 74, 19, 0, 14, 65, 45, 18),
  (6447, 1, 26, 75, 12, 15, 1, 72, 6, 35, 15),
  (6448, 1, 2, 41, 69, 19, 1, 13, 79, 6, 14),
  (6449, 0, 12, 76, 23, 16, 0, 13, 78, 14, 15)
  ]

lemma witChunk_124_ok : witChunk_124.all checkWit = true := by
  decide +kernel

lemma witChunk_124_ns :
    witChunk_124.map (fun t => t.1) = (List.range 50).map (· + 6400) := by
  decide +kernel

def witChunk_125 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6450, 0, 5, 44, 67, 19, 0, 7, 25, 76, 19),
  (6451, 0, 3, 41, 69, 19, 0, 27, 69, 31, 17),
  (6452, 0, 0, 76, 26, 16, 0, 40, 54, 44, 18),
  (6453, 1, 41, 3, 69, 18, 1, 45, 49, 45, 18),
  (6454, 0, 75, 27, 10, 13, 1, 24, 20, 74, 19),
  (6455, 1, 31, 74, 4, 14, 1, 79, 4, 14, 12),
  (6456, 0, 68, 26, 34, 16, 1, 53, 27, 54, 18),
  (6457, 2, 7, 48, 64, 19, 2, 7, 80, 0, 13),
  (6458, 0, 29, 24, 71, 19, 0, 71, 29, 24, 15),
  (6459, 0, 19, 77, 13, 15, 0, 23, 47, 61, 19),
  (6460, 1, 41, 69, 4, 14, 3, 0, 41, 69, 19),
  (6461, 0, 29, 74, 12, 15, 0, 44, 6, 67, 18),
  (6462, 0, 25, 46, 61, 19, 2, 33, 39, 62, 19),
  (6463, 1, 18, 19, 76, 19, 1, 32, 26, 69, 19),
  (6464, 1, 63, 42, 27, 16, 1, 79, 10, 11, 12),
  (6465, 0, 17, 20, 76, 19, 0, 50, 59, 22, 16),
  (6466, 0, 21, 20, 75, 19, 0, 21, 48, 61, 19),
  (6467, 0, 63, 47, 17, 15, 2, 5, 47, 65, 19),
  (6468, 0, 52, 20, 58, 18, 0, 76, 26, 4, 12),
  (6469, 0, 33, 32, 66, 19, 1, 37, 57, 43, 18),
  (6470, 0, 6, 65, 47, 18, 0, 15, 49, 62, 19),
  (6471, 3, 32, 23, 70, 19, 3, 33, 60, 42, 18),
  (6472, 1, 2, 29, 75, 19, 1, 6, 47, 65, 19),
  (6473, 0, 14, 79, 6, 14, 0, 32, 60, 43, 18),
  (6474, 2, 20, 75, 21, 16, 2, 29, 21, 72, 19),
  (6475, 0, 3, 29, 75, 19, 0, 27, 45, 61, 19),
  (6476, 1, 23, 64, 43, 18, 1, 53, 23, 56, 18),
  (6477, 0, 5, 26, 76, 19, 0, 28, 62, 43, 18),
  (6478, 0, 33, 30, 67, 19, 2, 57, 55, 14, 15),
  (6479, 1, 2, 43, 68, 19, 1, 8, 22, 77, 19),
  (6480, 0, 4, 80, 8, 14, 0, 36, 0, 72, 18),
  (6481, 0, 0, 80, 9, 14, 0, 1, 36, 72, 19),
  (6482, 0, 3, 43, 68, 19, 0, 43, 67, 12, 15),
  (6483, 0, 7, 47, 65, 19, 0, 19, 49, 61, 19),
  (6484, 1, 29, 75, 4, 14, 2, 66, 2, 46, 16),
  (6485, 0, 18, 65, 44, 18, 0, 50, 41, 48, 18),
  (6486, 0, 1, 34, 73, 19, 0, 1, 38, 71, 19),
  (6487, 1, 0, 34, 73, 19, 1, 0, 38, 71, 19),
  (6488, 0, 68, 10, 42, 16, 1, 14, 19, 77, 19),
  (6489, 2, 3, 46, 66, 19, 2, 10, 66, 45, 18),
  (6490, 1, 4, 46, 66, 19, 1, 12, 50, 62, 19),
  (6491, 0, 11, 21, 77, 19, 0, 11, 49, 63, 19),
  (6492, 2, 30, 72, 20, 16, 3, 4, 23, 77, 19),
  (6493, 0, 24, 74, 21, 16, 1, 49, 11, 63, 18),
  (6494, 0, 9, 22, 77, 19, 0, 26, 63, 43, 18),
  (6495, 3, 34, 40, 61, 19, 5, 30, 19, 72, 19),
  (6496, 0, 36, 72, 4, 14, 0, 76, 12, 24, 14),
  (6497, 0, 0, 64, 49, 18, 0, 5, 46, 66, 19),
  (6498, 0, 13, 20, 77, 19, 0, 19, 19, 76, 19),
  (6499, 0, 27, 21, 73, 19, 0, 51, 53, 33, 17)
  ]

lemma witChunk_125_ok : witChunk_125.all checkWit = true := by
  decide +kernel

lemma witChunk_125_ns :
    witChunk_125.map (fun t => t.1) = (List.range 50).map (· + 6450) := by
  decide +kernel

def witChunk_126 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6500, 0, 48, 10, 64, 18, 0, 52, 36, 50, 18),
  (6501, 0, 1, 32, 74, 19, 0, 1, 40, 70, 19),
  (6502, 0, 33, 38, 63, 19, 0, 57, 2, 57, 17),
  (6503, 1, 2, 79, 16, 15, 1, 62, 49, 16, 15),
  (6504, 0, 40, 2, 70, 18, 1, 6, 79, 15, 15),
  (6505, 2, 31, 44, 60, 19, 4, 1, 46, 66, 19),
  (6506, 0, 3, 79, 16, 15, 0, 59, 55, 0, 13),
  (6507, 0, 7, 23, 77, 19, 1, 51, 40, 48, 18),
  (6508, 1, 39, 56, 43, 18, 1, 71, 36, 13, 14),
  (6509, 0, 20, 78, 5, 14, 0, 29, 22, 72, 19),
  (6510, 0, 17, 50, 61, 19, 2, 29, 69, 30, 17),
  (6511, 1, 2, 27, 76, 19, 1, 16, 18, 77, 19),
  (6512, 3, 17, 66, 43, 18, 3, 63, 43, 26, 16),
  (6513, 0, 8, 80, 7, 14, 0, 13, 50, 62, 19),
  (6514, 0, 3, 27, 76, 19, 2, 1, 27, 76, 19),
  (6515, 0, 7, 79, 15, 15, 0, 15, 19, 77, 19),
  (6516, 0, 16, 76, 22, 16, 0, 32, 74, 4, 14),
  (6517, 1, 21, 65, 43, 18, 1, 65, 47, 9, 14),
  (6518, 0, 73, 10, 33, 15, 1, 60, 54, 0, 13),
  (6519, 1, 15, 66, 44, 18, 3, 4, 73, 34, 17),
  (6520, 1, 2, 45, 67, 19, 1, 10, 73, 33, 17),
  (6521, 0, 24, 64, 43, 18, 0, 46, 7, 66, 18),
  (6522, 2, 3, 24, 77, 19, 2, 21, 77, 12, 15),
  (6523, 0, 3, 45, 67, 19, 0, 63, 23, 45, 17),
  (6524, 2, 74, 28, 16, 14, 3, 17, 76, 21, 16),
  (6525, 0, 12, 66, 45, 18, 0, 45, 66, 12, 15),
  (6526, 0, 1, 30, 75, 19, 0, 1, 42, 69, 19),
  (6527, 1, 0, 30, 75, 19, 1, 0, 42, 69, 19),
  (6528, 2, 34, 60, 42, 18, 2, 42, 66, 20, 16),
  (6529, 0, 25, 48, 60, 19, 0, 60, 48, 25, 16),
  (6530, 0, 5, 24, 77, 19, 0, 23, 49, 60, 19),
  (6531, 0, 23, 71, 31, 17, 0, 31, 23, 71, 19),
  (6532, 1, 1, 65, 48, 18, 1, 5, 77, 24, 16),
  (6533, 0, 2, 65, 48, 18, 0, 33, 40, 62, 19),
  (6534, 0, 7, 73, 34, 17, 0, 42, 3, 69, 18),
  (6535, 1, 6, 49, 64, 19, 1, 8, 50, 63, 19),
  (6536, 0, 8, 66, 46, 18, 0, 48, 46, 46, 18),
  (6537, 0, 68, 8, 43, 16, 2, 0, 65, 48, 18),
  (6538, 0, 27, 47, 60, 19, 0, 61, 36, 39, 17),
  (6539, 0, 11, 73, 33, 17, 0, 35, 33, 65, 19),
  (6540, 1, 47, 48, 45, 18, 5, 75, 24, 17, 14),
  (6541, 0, 6, 77, 24, 16, 0, 21, 18, 76, 19),
  (6542, 0, 17, 18, 77, 19, 0, 17, 78, 13, 15),
  (6543, 3, 10, 52, 61, 19, 3, 58, 44, 35, 17),
  (6544, 1, 18, 17, 77, 19, 1, 34, 25, 69, 19),
  (6545, 0, 25, 76, 12, 15, 0, 62, 45, 26, 16),
  (6546, 0, 7, 49, 64, 19, 0, 35, 35, 64, 19),
  (6547, 0, 15, 51, 61, 19, 0, 63, 27, 43, 17),
  (6548, 0, 16, 66, 44, 18, 0, 68, 30, 32, 16),
  (6549, 0, 52, 38, 49, 18, 0, 73, 8, 34, 15)
  ]

lemma witChunk_126_ok : witChunk_126.all checkWit = true := by
  decide +kernel

lemma witChunk_126_ns :
    witChunk_126.map (fun t => t.1) = (List.range 50).map (· + 6500) := by
  decide +kernel

def witChunk_127 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6550, 0, 9, 50, 63, 19, 0, 22, 75, 21, 16),
  (6551, 1, 14, 73, 32, 17, 1, 22, 17, 76, 19),
  (6552, 0, 52, 58, 22, 16, 3, 11, 77, 22, 16),
  (6553, 2, 31, 20, 72, 19, 2, 48, 65, 4, 14),
  (6554, 0, 5, 48, 65, 19, 1, 12, 18, 78, 19),
  (6555, 0, 35, 29, 67, 19, 2, 61, 51, 15, 15),
  (6556, 1, 73, 35, 0, 12, 3, 36, 39, 61, 19),
  (6557, 0, 29, 46, 60, 19, 0, 77, 22, 12, 13),
  (6558, 0, 2, 77, 25, 16, 0, 10, 77, 23, 16),
  (6559, 1, 11, 80, 6, 14, 1, 22, 77, 12, 15),
  (6560, 0, 52, 16, 60, 18, 1, 2, 25, 77, 19),
  (6561, 0, 0, 0, 81, 18, 0, 1, 28, 76, 19),
  (6562, 0, 19, 51, 60, 19, 0, 63, 17, 48, 17),
  (6563, 0, 3, 25, 77, 19, 0, 3, 73, 35, 17),
  (6564, 1, 39, 0, 71, 18, 1, 45, 51, 44, 18),
  (6565, 0, 9, 20, 78, 19, 0, 33, 24, 70, 19),
  (6566, 0, 11, 19, 78, 19, 0, 11, 51, 62, 19),
  (6567, 3, 28, 17, 74, 19, 3, 28, 49, 58, 19),
  (6568, 1, 2, 81, 1, 13, 1, 19, 66, 43, 18),
  (6569, 0, 76, 28, 3, 12, 2, 23, 16, 76, 19),
  (6570, 0, 29, 20, 73, 19, 2, 35, 24, 69, 19),
  (6571, 0, 3, 81, 1, 13, 0, 63, 51, 1, 13),
  (6572, 1, 25, 77, 4, 14, 1, 29, 73, 20, 16),
  (6573, 0, 52, 62, 5, 14, 0, 74, 29, 16, 14),
  (6574, 0, 3, 47, 66, 19, 0, 7, 21, 78, 19),
  (6575, 3, 26, 16, 75, 19, 3, 44, 61, 30, 17),
  (6576, 0, 28, 76, 4, 14, 0, 44, 4, 68, 18),
  (6577, 0, 13, 18, 78, 19, 2, 2, 66, 47, 18),
  (6578, 0, 15, 73, 32, 17, 0, 35, 27, 68, 19),
  (6579, 0, 19, 17, 77, 19, 2, 33, 21, 71, 19),
  (6580, 0, 12, 80, 6, 14, 1, 19, 76, 21, 16),
  (6581, 0, 4, 66, 47, 18, 0, 54, 23, 56, 18),
  (6582, 0, 55, 49, 34, 17, 3, 38, 32, 64, 19),
  (6583, 1, 47, 66, 4, 14, 1, 63, 44, 26, 16),
  (6584, 1, 13, 77, 22, 16, 1, 41, 1, 70, 18),
  (6585, 0, 40, 56, 43, 18, 2, 3, 22, 78, 19),
  (6586, 0, 21, 72, 31, 17, 0, 31, 21, 72, 19),
  (6587, 0, 71, 39, 5, 13, 1, 20, 16, 77, 19),
  (6588, 3, 55, 29, 52, 18, 3, 64, 25, 43, 17),
  (6589, 0, 48, 62, 21, 16, 0, 64, 42, 27, 16),
  (6590, 0, 18, 79, 5, 14, 0, 35, 39, 62, 19),
  (6591, 1, 27, 64, 42, 18, 1, 35, 60, 42, 18),
  (6592, 1, 26, 17, 75, 19, 1, 30, 19, 73, 19),
  (6593, 0, 5, 22, 78, 19, 0, 17, 52, 60, 19),
  (6594, 0, 13, 52, 61, 19, 0, 23, 17, 76, 19),
  (6595, 0, 63, 15, 49, 17, 2, 29, 75, 11, 15),
  (6596, 0, 36, 70, 20, 16, 0, 68, 6, 44, 16),
  (6597, 0, 34, 71, 20, 16, 1, 9, 67, 45, 18),
  (6598, 0, 15, 17, 78, 19, 1, 16, 16, 78, 19),
  (6599, 1, 6, 81, 0, 13, 1, 64, 50, 1, 13)
  ]

lemma witChunk_127_ok : witChunk_127.all checkWit = true := by
  decide +kernel

lemma witChunk_127_ns :
    witChunk_127.map (fun t => t.1) = (List.range 50).map (· + 6550) := by
  decide +kernel

def witChunk_128 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6600, 5, 30, 49, 57, 19, 8, 0, 66, 46, 18),
  (6601, 2, 27, 50, 58, 19, 2, 43, 62, 30, 17),
  (6602, 0, 23, 77, 12, 15, 0, 53, 52, 33, 17),
  (6603, 0, 79, 19, 1, 11, 1, 36, 72, 11, 15),
  (6604, 2, 70, 20, 36, 16, 3, 4, 51, 63, 19),
  (6605, 0, 20, 66, 43, 18, 0, 38, 69, 20, 16),
  (6606, 0, 1, 26, 77, 19, 0, 1, 46, 67, 19),
  (6607, 1, 0, 26, 77, 19, 1, 0, 46, 67, 19),
  (6608, 0, 32, 72, 20, 16, 0, 52, 40, 48, 18),
  (6609, 0, 14, 77, 22, 16, 0, 61, 38, 38, 17),
  (6610, 0, 7, 81, 0, 13, 1, 24, 16, 76, 19),
  (6611, 0, 23, 51, 59, 19, 0, 27, 49, 59, 19),
  (6612, 0, 80, 4, 14, 12, 2, 22, 66, 42, 18),
  (6613, 0, 33, 68, 30, 17, 0, 57, 0, 58, 17),
  (6614, 0, 10, 67, 45, 18, 0, 33, 22, 71, 19),
  (6615, 1, 50, 63, 12, 15, 1, 72, 30, 23, 15),
  (6616, 1, 18, 53, 59, 19, 1, 18, 73, 31, 17),
  (6617, 0, 20, 76, 21, 16, 2, 35, 22, 70, 19),
  (6618, 0, 37, 32, 65, 19, 2, 27, 16, 75, 19),
  (6619, 0, 7, 51, 63, 19, 1, 2, 23, 78, 19),
  (6620, 1, 55, 28, 53, 18, 2, 46, 64, 20, 16),
  (6621, 0, 5, 50, 64, 19, 0, 14, 67, 44, 18),
  (6622, 0, 3, 23, 78, 19, 0, 31, 69, 30, 17),
  (6623, 1, 32, 46, 59, 19, 1, 32, 74, 11, 15),
  (6624, 0, 40, 68, 20, 16, 3, 67, 1, 46, 16),
  (6625, 0, 33, 44, 60, 19, 0, 37, 30, 66, 19),
  (6626, 0, 21, 16, 77, 19, 0, 21, 52, 59, 19),
  (6627, 0, 35, 41, 61, 19, 2, 69, 43, 3, 13),
  (6628, 1, 1, 81, 8, 14, 1, 55, 24, 55, 18),
  (6629, 0, 2, 81, 8, 14, 0, 9, 52, 62, 19),
  (6630, 0, 46, 5, 67, 18, 0, 65, 46, 17, 15),
  (6631, 1, 8, 18, 79, 19, 1, 8, 74, 33, 17),
  (6632, 0, 32, 62, 42, 18, 1, 2, 49, 65, 19),
  (6633, 0, 30, 63, 42, 18, 0, 48, 48, 45, 18),
  (6634, 0, 15, 53, 60, 19, 0, 37, 36, 63, 19),
  (6635, 0, 3, 49, 65, 19, 0, 15, 79, 13, 15),
  (6636, 1, 53, 15, 60, 18, 1, 53, 39, 48, 18),
  (6637, 0, 61, 54, 0, 13, 0, 70, 21, 36, 16),
  (6638, 0, 42, 55, 43, 18, 0, 63, 13, 50, 17),
  (6639, 3, 34, 68, 29, 17, 5, 60, 42, 35, 17),
  (6640, 1, 6, 19, 79, 19, 1, 22, 15, 77, 19),
  (6641, 0, 6, 67, 46, 18, 0, 29, 18, 74, 19),
  (6642, 0, 37, 28, 67, 19, 2, 3, 80, 15, 15),
  (6643, 0, 27, 17, 75, 19, 1, 4, 80, 15, 15),
  (6644, 0, 28, 64, 42, 18, 0, 80, 12, 10, 12),
  (6645, 2, 11, 54, 60, 19, 2, 38, 72, 3, 14),
  (6646, 0, 6, 81, 7, 14, 0, 9, 18, 79, 19),
  (6647, 1, 47, 50, 44, 18, 1, 55, 22, 56, 18),
  (6648, 1, 30, 75, 11, 15, 1, 42, 69, 11, 15),
  (6649, 0, 54, 57, 22, 16, 0, 58, 57, 6, 14)
  ]

lemma witChunk_128_ok : witChunk_128.all checkWit = true := by
  decide +kernel

lemma witChunk_128_ns :
    witChunk_128.map (fun t => t.1) = (List.range 50).map (· + 6600) := by
  decide +kernel

def witChunk_129 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6650, 0, 5, 80, 15, 15, 0, 51, 55, 32, 17),
  (6651, 0, 7, 19, 79, 19, 0, 11, 17, 79, 19),
  (6652, 1, 15, 80, 5, 14, 1, 25, 75, 20, 16),
  (6653, 0, 42, 67, 20, 16, 0, 46, 51, 44, 18),
  (6654, 0, 35, 23, 70, 19, 0, 70, 23, 35, 16),
  (6655, 1, 16, 54, 59, 19, 1, 51, 44, 46, 18),
  (6656, 0, 80, 0, 16, 12, 1, 77, 7, 26, 14),
  (6657, 0, 1, 80, 16, 15, 0, 5, 74, 34, 17),
  (6658, 0, 63, 33, 40, 17, 1, 0, 80, 16, 15),
  (6659, 1, 4, 20, 79, 19, 1, 22, 53, 58, 19),
  (6660, 0, 0, 66, 48, 18, 0, 28, 74, 20, 16),
  (6661, 0, 1, 24, 78, 19, 0, 1, 48, 66, 19),
  (6662, 0, 18, 67, 43, 18, 0, 50, 61, 21, 16),
  (6663, 3, 2, 20, 79, 19, 3, 16, 55, 58, 19),
  (6664, 1, 7, 78, 23, 16, 1, 14, 15, 79, 19),
  (6665, 0, 26, 65, 42, 18, 0, 42, 1, 70, 18),
  (6666, 0, 5, 20, 79, 19, 0, 13, 16, 79, 19),
  (6667, 1, 28, 16, 75, 19, 1, 30, 17, 74, 19),
  (6668, 2, 10, 68, 44, 18, 2, 22, 76, 20, 16),
  (6669, 0, 13, 74, 32, 17, 0, 21, 78, 12, 15),
  (6670, 0, 19, 15, 78, 19, 0, 27, 71, 30, 17),
  (6671, 1, 3, 78, 24, 16, 1, 56, 58, 13, 15),
  (6672, 1, 51, 10, 63, 18, 1, 62, 51, 15, 15),
  (6673, 0, 33, 20, 72, 19, 0, 61, 6, 54, 17),
  (6674, 0, 35, 43, 60, 19, 0, 37, 72, 11, 15),
  (6675, 0, 35, 73, 11, 15, 0, 55, 59, 13, 15),
  (6676, 0, 4, 78, 24, 16, 0, 24, 78, 4, 14),
  (6677, 0, 8, 78, 23, 16, 0, 9, 80, 14, 15),
  (6678, 0, 62, 47, 25, 16, 2, 21, 73, 30, 17),
  (6679, 1, 26, 15, 76, 19, 1, 32, 18, 73, 19),
  (6680, 0, 68, 34, 30, 16, 0, 76, 30, 2, 12),
  (6681, 0, 16, 80, 5, 14, 0, 70, 25, 34, 16),
  (6682, 0, 79, 21, 0, 11, 1, 20, 14, 78, 19),
  (6683, 0, 23, 15, 77, 19, 0, 39, 71, 11, 15),
  (6684, 2, 78, 24, 4, 12, 3, 16, 13, 79, 19),
  (6685, 0, 13, 54, 60, 19, 1, 45, 53, 43, 18),
  (6686, 0, 17, 54, 59, 19, 0, 33, 46, 59, 19),
  (6687, 3, 4, 53, 62, 19, 3, 10, 80, 13, 15),
  (6688, 1, 2, 21, 79, 19, 1, 38, 39, 61, 19),
  (6689, 0, 38, 59, 42, 18, 0, 73, 28, 24, 15),
  (6690, 0, 37, 40, 61, 19, 0, 61, 40, 37, 17),
  (6691, 0, 3, 21, 79, 19, 0, 15, 15, 79, 19),
  (6692, 0, 44, 66, 20, 16, 0, 52, 12, 62, 18),
  (6693, 0, 25, 52, 58, 19, 2, 6, 68, 45, 18),
  (6694, 0, 18, 77, 21, 16, 0, 27, 51, 58, 19),
  (6695, 1, 16, 14, 79, 19, 1, 16, 74, 31, 17),
  (6696, 0, 24, 66, 42, 18, 0, 48, 6, 66, 18),
  (6697, 0, 10, 81, 6, 14, 2, 52, 63, 4, 14),
  (6698, 0, 5, 52, 63, 19, 2, 11, 80, 13, 15),
  (6699, 2, 29, 15, 75, 19, 2, 29, 51, 57, 19)
  ]

lemma witChunk_129_ok : witChunk_129.all checkWit = true := by
  decide +kernel

lemma witChunk_129_ns :
    witChunk_129.map (fun t => t.1) = (List.range 50).map (· + 6650) := by
  decide +kernel

def witChunk_130 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6700, 1, 7, 68, 45, 18, 1, 15, 68, 43, 18),
  (6701, 0, 26, 75, 20, 16, 0, 44, 2, 69, 18),
  (6702, 0, 1, 74, 35, 17, 0, 2, 67, 47, 18),
  (6703, 1, 0, 74, 35, 17, 1, 2, 51, 64, 19),
  (6704, 0, 12, 68, 44, 18, 1, 14, 55, 59, 19),
  (6705, 0, 29, 50, 58, 19, 0, 77, 26, 10, 13),
  (6706, 0, 3, 51, 64, 19, 0, 37, 24, 69, 19),
  (6707, 0, 31, 75, 11, 15, 0, 35, 21, 71, 19),
  (6708, 0, 64, 44, 26, 16, 3, 19, 77, 20, 16),
  (6709, 0, 0, 78, 25, 16, 0, 25, 72, 30, 17),
  (6710, 2, 31, 70, 29, 17, 2, 65, 19, 46, 17),
  (6711, 1, 18, 79, 12, 15, 5, 6, 15, 80, 19),
  (6712, 0, 12, 78, 22, 16, 1, 35, 74, 3, 14),
  (6713, 0, 8, 68, 45, 18, 2, 7, 16, 80, 19),
  (6714, 0, 51, 63, 12, 15, 1, 60, 54, 14, 15),
  (6715, 0, 39, 35, 63, 19, 0, 55, 51, 33, 17),
  (6716, 1, 39, 72, 3, 14, 1, 47, 4, 67, 18),
  (6717, 2, 47, 60, 30, 17, 2, 63, 36, 38, 17),
  (6718, 0, 9, 54, 61, 19, 0, 39, 29, 66, 19),
  (6719, 1, 67, 38, 28, 16, 3, 26, 72, 29, 17),
  (6720, 0, 80, 16, 8, 12, 2, 18, 68, 42, 18),
  (6721, 0, 21, 14, 78, 19, 0, 21, 54, 58, 19),
  (6722, 0, 29, 16, 75, 19, 0, 69, 40, 19, 15),
  (6723, 2, 21, 55, 57, 19, 3, 4, 17, 80, 19),
  (6724, 1, 55, 36, 49, 18, 1, 63, 52, 7, 14),
  (6725, 0, 78, 25, 4, 12, 1, 33, 75, 3, 14),
  (6726, 0, 1, 22, 79, 19, 0, 1, 50, 65, 19),
  (6727, 1, 0, 22, 79, 19, 1, 0, 50, 65, 19),
  (6728, 0, 40, 58, 42, 18, 0, 56, 26, 54, 18),
  (6729, 0, 16, 68, 43, 18, 0, 56, 28, 53, 18),
  (6730, 0, 27, 15, 76, 19, 2, 28, 77, 3, 14),
  (6731, 0, 15, 55, 59, 19, 0, 35, 45, 59, 19),
  (6732, 2, 62, 48, 24, 16, 2, 66, 48, 8, 14),
  (6733, 0, 37, 42, 60, 19, 1, 41, 71, 3, 14),
  (6734, 0, 39, 37, 62, 19, 0, 50, 47, 45, 18),
  (6735, 3, 10, 56, 59, 19, 3, 50, 64, 11, 15),
  (6736, 1, 18, 13, 79, 19, 1, 26, 53, 57, 19),
  (6737, 0, 9, 16, 80, 19, 0, 22, 67, 42, 18),
  (6738, 0, 7, 17, 80, 19, 0, 13, 80, 13, 15),
  (6739, 0, 39, 27, 67, 19, 1, 22, 13, 78, 19),
  (6740, 0, 48, 50, 44, 18, 0, 56, 30, 52, 18),
  (6741, 0, 22, 79, 4, 14, 0, 46, 65, 20, 16),
  (6742, 0, 33, 18, 73, 19, 0, 82, 3, 3, 10),
  (6743, 1, 24, 54, 57, 19, 1, 71, 16, 38, 16),
  (6744, 0, 68, 2, 46, 16, 1, 51, 46, 45, 18),
  (6745, 0, 52, 60, 21, 16, 0, 70, 9, 42, 16),
  (6746, 0, 11, 15, 80, 19, 0, 11, 55, 60, 19),
  (6747, 2, 5, 75, 33, 17, 2, 33, 49, 57, 19),
  (6748, 1, 31, 76, 3, 14, 2, 18, 80, 4, 14),
  (6749, 0, 5, 18, 80, 19, 0, 5, 82, 0, 13)
  ]

lemma witChunk_130_ok : witChunk_130.all checkWit = true := by
  decide +kernel

lemma witChunk_130_ns :
    witChunk_130.map (fun t => t.1) = (List.range 50).map (· + 6700) := by
  decide +kernel

def witChunk_131 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6750, 0, 19, 55, 58, 19, 0, 25, 14, 77, 19),
  (6751, 1, 3, 68, 46, 18, 1, 10, 75, 32, 17),
  (6752, 0, 24, 76, 20, 16, 1, 6, 75, 33, 17),
  (6753, 0, 37, 22, 70, 19, 0, 82, 5, 2, 10),
  (6754, 0, 63, 9, 52, 17, 2, 19, 12, 79, 19),
  (6755, 0, 75, 13, 31, 15, 0, 75, 17, 29, 15),
  (6756, 0, 4, 68, 46, 18, 0, 52, 44, 46, 18),
  (6757, 0, 33, 48, 58, 19, 1, 13, 81, 5, 14),
  (6758, 0, 23, 73, 30, 17, 0, 65, 18, 47, 17),
  (6759, 3, 1, 68, 46, 18, 3, 34, 16, 73, 19),
  (6760, 1, 22, 55, 57, 19, 1, 34, 69, 29, 17),
  (6761, 0, 56, 32, 51, 18, 0, 56, 60, 5, 14),
  (6762, 0, 61, 4, 55, 17, 2, 12, 69, 43, 18),
  (6763, 0, 7, 75, 33, 17, 0, 39, 39, 61, 19),
  (6764, 1, 47, 52, 43, 18, 1, 55, 16, 59, 18),
  (6765, 0, 13, 14, 80, 19, 0, 70, 29, 32, 16),
  (6766, 0, 66, 41, 27, 16, 0, 81, 14, 3, 11),
  (6767, 1, 2, 19, 80, 19, 1, 14, 13, 80, 19),
  (6768, 1, 27, 66, 41, 18, 1, 81, 3, 14, 12),
  (6769, 0, 45, 62, 30, 17, 2, 8, 69, 44, 18),
  (6770, 0, 3, 19, 80, 19, 0, 11, 75, 32, 17),
  (6771, 0, 19, 13, 79, 19, 0, 79, 19, 13, 13),
  (6772, 0, 60, 56, 6, 14, 0, 72, 38, 12, 14),
  (6773, 0, 52, 10, 63, 18, 0, 65, 28, 42, 17),
  (6774, 0, 46, 53, 43, 18, 0, 50, 7, 65, 18),
  (6775, 1, 32, 50, 57, 19, 1, 55, 38, 48, 18),
  (6776, 1, 26, 13, 77, 19, 1, 34, 17, 73, 19),
  (6777, 0, 42, 57, 42, 18, 2, 3, 54, 62, 19),
  (6778, 0, 63, 53, 0, 13, 1, 4, 54, 62, 19),
  (6779, 0, 27, 77, 11, 15, 1, 19, 80, 4, 14),
  (6780, 1, 9, 69, 44, 18, 3, 4, 55, 61, 19),
  (6781, 0, 16, 78, 21, 16, 0, 36, 74, 3, 14),
  (6782, 0, 14, 81, 5, 14, 0, 23, 13, 78, 19),
  (6783, 1, 24, 78, 11, 15, 1, 48, 66, 11, 15),
  (6784, 1, 2, 53, 63, 19, 1, 3, 82, 7, 14),
  (6785, 0, 5, 54, 62, 19, 0, 56, 20, 57, 18),
  (6786, 0, 13, 56, 59, 19, 0, 37, 44, 59, 19),
  (6787, 0, 3, 53, 63, 19, 0, 27, 53, 57, 19),
  (6788, 0, 0, 82, 8, 14, 0, 20, 68, 42, 18),
  (6789, 0, 4, 82, 7, 14, 0, 17, 56, 58, 19),
  (6790, 0, 3, 75, 34, 17, 0, 25, 54, 57, 19),
  (6791, 1, 80, 10, 17, 13, 3, 4, 81, 14, 15),
  (6792, 0, 56, 34, 50, 18, 1, 2, 81, 15, 15),
  (6793, 0, 40, 72, 3, 14, 0, 78, 15, 22, 14),
  (6794, 0, 15, 13, 80, 19, 0, 29, 52, 57, 19),
  (6795, 0, 3, 81, 15, 15, 0, 7, 55, 61, 19),
  (6796, 1, 53, 63, 4, 14, 1, 57, 29, 52, 18),
  (6797, 0, 10, 69, 44, 18, 0, 53, 62, 12, 15),
  (6798, 0, 35, 47, 58, 19, 0, 70, 7, 43, 16),
  (6799, 1, 40, 66, 29, 17, 1, 64, 10, 51, 17)
  ]

lemma witChunk_131_ok : witChunk_131.all checkWit = true := by
  decide +kernel

lemma witChunk_131_ns :
    witChunk_131.map (fun t => t.1) = (List.range 50).map (· + 6750) := by
  decide +kernel

def witChunk_132 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6800, 0, 48, 64, 20, 16, 1, 31, 74, 19, 16),
  (6801, 0, 1, 20, 80, 19, 0, 1, 52, 64, 19),
  (6802, 0, 39, 41, 60, 19, 1, 0, 20, 80, 19),
  (6803, 0, 23, 55, 57, 19, 0, 67, 45, 17, 15),
  (6804, 1, 39, 60, 41, 18, 2, 6, 82, 6, 14),
  (6805, 0, 82, 9, 0, 10, 1, 41, 69, 19, 16),
  (6806, 0, 6, 79, 23, 16, 0, 7, 81, 14, 15),
  (6807, 3, 74, 28, 23, 15, 3, 82, 4, 7, 11),
  (6808, 1, 9, 79, 22, 16, 1, 34, 49, 57, 19),
  (6809, 0, 32, 76, 3, 14, 0, 48, 4, 67, 18),
  (6810, 0, 37, 20, 71, 19, 0, 71, 37, 20, 15),
  (6811, 0, 15, 75, 31, 17, 0, 31, 15, 75, 19),
  (6812, 3, 8, 13, 81, 19, 3, 8, 57, 59, 19),
  (6813, 0, 22, 77, 20, 16, 0, 29, 14, 76, 19),
  (6814, 0, 42, 71, 3, 14, 0, 78, 17, 21, 14),
  (6815, 3, 29, 66, 40, 18, 3, 44, 69, 10, 15),
  (6816, 0, 20, 80, 4, 14, 0, 52, 64, 4, 14),
  (6817, 0, 9, 56, 60, 19, 0, 21, 74, 30, 17),
  (6818, 1, 80, 4, 20, 13, 2, 17, 11, 80, 19),
  (6819, 0, 47, 67, 11, 15, 2, 5, 15, 81, 19),
  (6820, 1, 1, 79, 24, 16, 1, 67, 40, 27, 16),
  (6821, 0, 2, 79, 24, 16, 0, 28, 66, 41, 18),
  (6822, 0, 6, 69, 45, 18, 0, 65, 14, 49, 17),
  (6823, 1, 8, 14, 81, 19, 1, 42, 31, 64, 19),
  (6824, 0, 8, 82, 6, 14, 0, 56, 18, 58, 18),
  (6825, 0, 10, 79, 22, 16, 2, 0, 79, 24, 16),
  (6826, 0, 21, 12, 79, 19, 0, 21, 56, 57, 19),
  (6827, 0, 27, 13, 77, 19, 0, 35, 69, 29, 17),
  (6828, 1, 57, 21, 56, 18, 5, 57, 35, 48, 18),
  (6829, 1, 29, 75, 19, 16, 1, 69, 35, 29, 16),
  (6830, 0, 25, 78, 11, 15, 0, 33, 70, 29, 17),
  (6831, 3, 28, 77, 10, 15, 3, 37, 62, 40, 18),
  (6832, 1, 10, 13, 81, 19, 1, 10, 57, 59, 19),
  (6833, 0, 0, 68, 47, 18, 0, 17, 12, 80, 19),
  (6834, 0, 37, 68, 29, 17, 2, 3, 16, 81, 19),
  (6835, 0, 7, 15, 81, 19, 1, 4, 16, 81, 19),
  (6836, 0, 44, 0, 70, 18, 0, 44, 56, 42, 18),
  (6837, 0, 50, 49, 44, 18, 0, 64, 46, 25, 16),
  (6838, 0, 9, 14, 81, 19, 0, 15, 57, 58, 19),
  (6839, 1, 26, 55, 56, 19, 1, 47, 2, 68, 18),
  (6840, 1, 57, 33, 50, 18, 3, 55, 41, 46, 18),
  (6841, 0, 36, 72, 19, 16, 2, 16, 81, 4, 14),
  (6842, 0, 5, 16, 81, 19, 2, 41, 23, 68, 19),
  (6843, 0, 31, 71, 29, 17, 0, 35, 17, 73, 19),
  (6844, 1, 47, 68, 3, 14, 1, 73, 37, 12, 14),
  (6845, 0, 44, 70, 3, 14, 0, 52, 46, 45, 18),
  (6846, 0, 26, 67, 41, 18, 0, 34, 73, 19, 16),
  (6847, 1, 18, 11, 80, 19, 1, 19, 78, 20, 16),
  (6848, 1, 22, 11, 79, 19, 1, 22, 79, 11, 15),
  (6849, 0, 18, 69, 42, 18, 0, 37, 46, 58, 19)
  ]

lemma witChunk_132_ok : witChunk_132.all checkWit = true := by
  decide +kernel

lemma witChunk_132_ns :
    witChunk_132.map (fun t => t.1) = (List.range 50).map (· + 6800) := by
  decide +kernel

def witChunk_133 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6850, 1, 24, 56, 56, 19, 2, 20, 69, 41, 18),
  (6851, 0, 11, 13, 81, 19, 0, 11, 57, 59, 19),
  (6852, 0, 68, 38, 28, 16, 1, 81, 15, 8, 12),
  (6853, 0, 25, 12, 78, 19, 1, 13, 79, 21, 16),
  (6854, 1, 80, 16, 14, 13, 2, 23, 74, 29, 17),
  (6855, 3, 10, 76, 31, 17, 3, 26, 56, 55, 19),
  (6856, 1, 2, 17, 81, 19, 1, 42, 37, 61, 19),
  (6857, 0, 48, 52, 43, 18, 2, 7, 76, 32, 17),
  (6858, 0, 55, 53, 32, 17, 2, 72, 21, 35, 16),
  (6859, 0, 3, 17, 81, 19, 0, 19, 57, 57, 19),
  (6860, 2, 34, 64, 40, 18, 2, 58, 28, 52, 18),
  (6861, 0, 32, 74, 19, 16, 0, 40, 70, 19, 16),
  (6862, 0, 39, 21, 70, 19, 4, 13, 10, 81, 19),
  (6863, 1, 82, 11, 4, 11, 3, 18, 80, 11, 15),
  (6864, 0, 52, 8, 64, 18, 1, 51, 6, 65, 18),
  (6865, 4, 30, 77, 2, 14, 6, 31, 54, 54, 19),
  (6866, 0, 29, 72, 29, 17, 1, 8, 76, 32, 17),
  (6867, 2, 73, 33, 21, 15, 3, 12, 81, 12, 15),
  (6868, 1, 17, 81, 4, 14, 1, 27, 76, 19, 16),
  (6869, 0, 50, 63, 20, 16, 0, 65, 12, 50, 17),
  (6870, 0, 58, 59, 5, 14, 0, 74, 35, 13, 14),
  (6871, 1, 16, 58, 57, 19, 1, 22, 57, 56, 19),
  (6872, 1, 11, 70, 43, 18, 1, 11, 82, 5, 14),
  (6873, 0, 56, 16, 59, 18, 0, 58, 55, 22, 16),
  (6874, 0, 13, 12, 81, 19, 1, 12, 58, 58, 19),
  (6875, 0, 35, 49, 57, 19, 0, 75, 5, 35, 15),
  (6876, 3, 32, 53, 55, 19, 3, 49, 64, 19, 16),
  (6877, 0, 28, 78, 3, 14, 0, 37, 18, 72, 19),
  (6878, 0, 3, 55, 62, 19, 0, 14, 79, 21, 16),
  (6879, 3, 2, 56, 61, 19, 3, 5, 70, 44, 18),
  (6880, 0, 72, 20, 36, 16, 1, 1, 69, 46, 18),
  (6881, 0, 2, 69, 46, 18, 0, 9, 76, 32, 17),
  (6882, 0, 5, 56, 61, 19, 0, 19, 11, 80, 19),
  (6883, 1, 4, 76, 33, 17, 1, 12, 76, 31, 17),
  (6884, 0, 20, 78, 20, 16, 0, 56, 38, 48, 18),
  (6885, 1, 21, 69, 41, 18, 2, 0, 69, 46, 18),
  (6886, 0, 1, 18, 81, 19, 0, 1, 54, 63, 19),
  (6887, 1, 0, 18, 81, 19, 1, 0, 54, 63, 19),
  (6888, 3, 17, 70, 41, 18, 5, 14, 9, 81, 19),
  (6889, 0, 70, 33, 30, 16, 2, 31, 12, 76, 19),
  (6890, 0, 5, 76, 33, 17, 0, 27, 55, 56, 19),
  (6891, 0, 23, 11, 79, 19, 0, 23, 79, 11, 15),
  (6892, 1, 55, 12, 61, 18, 3, 12, 59, 57, 19),
  (6893, 0, 12, 70, 43, 18, 0, 12, 82, 5, 14),
  (6894, 2, 15, 10, 81, 19, 2, 39, 18, 71, 19),
  (6895, 1, 2, 83, 0, 13, 1, 24, 74, 29, 17),
  (6896, 1, 43, 58, 41, 18, 1, 78, 27, 9, 13),
  (6897, 0, 13, 58, 58, 19, 0, 25, 56, 56, 19),
  (6898, 0, 3, 83, 0, 13, 0, 7, 57, 60, 19),
  (6899, 0, 27, 73, 29, 17, 0, 59, 57, 13, 15)
  ]

lemma witChunk_133_ok : witChunk_133.all checkWit = true := by
  decide +kernel

lemma witChunk_133_ns :
    witChunk_133.map (fun t => t.1) = (List.range 50).map (· + 6850) := by
  decide +kernel

def witChunk_134 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6900, 0, 8, 70, 44, 18, 2, 78, 22, 18, 14),
  (6901, 0, 18, 81, 4, 14, 0, 49, 60, 30, 17),
  (6902, 0, 17, 58, 57, 19, 0, 58, 27, 53, 18),
  (6903, 1, 14, 81, 12, 15, 3, 34, 52, 55, 19),
  (6904, 1, 38, 47, 57, 19, 1, 54, 55, 31, 17),
  (6905, 0, 46, 55, 42, 18, 0, 58, 25, 54, 18),
  (6906, 0, 13, 76, 31, 17, 0, 31, 13, 76, 19),
  (6907, 0, 15, 11, 81, 19, 0, 43, 33, 63, 19),
  (6908, 2, 26, 68, 40, 18, 2, 58, 20, 56, 18),
  (6909, 0, 58, 29, 52, 18, 0, 80, 22, 5, 12),
  (6910, 0, 33, 14, 75, 19, 0, 39, 45, 58, 19),
  (6911, 1, 8, 58, 59, 19, 1, 64, 38, 37, 17),
  (6912, 2, 82, 6, 12, 12, 3, 31, 77, 2, 14),
  (6913, 2, 18, 70, 41, 18, 2, 56, 13, 60, 18),
  (6914, 0, 23, 57, 56, 19, 0, 29, 12, 77, 19),
  (6915, 0, 43, 29, 65, 19, 0, 43, 65, 29, 17),
  (6916, 0, 72, 24, 34, 16, 1, 33, 65, 40, 18),
  (6917, 0, 82, 7, 12, 12, 1, 25, 77, 19, 16),
  (6918, 0, 43, 35, 62, 19, 0, 58, 23, 55, 18),
  (6919, 1, 16, 10, 81, 19, 1, 24, 10, 79, 19),
  (6920, 0, 16, 70, 42, 18, 1, 62, 43, 35, 17),
  (6921, 0, 28, 76, 19, 16, 0, 44, 68, 19, 16),
  (6922, 0, 37, 48, 57, 19, 2, 33, 71, 28, 17),
  (6923, 0, 39, 19, 71, 19, 0, 71, 39, 19, 15),
  (6924, 1, 57, 37, 48, 18, 2, 54, 60, 20, 16),
  (6925, 2, 7, 12, 82, 19, 2, 66, 44, 25, 16),
  (6926, 0, 9, 58, 59, 19, 0, 22, 69, 41, 18),
  (6927, 3, 4, 13, 82, 19, 3, 5, 80, 22, 16),
  (6928, 0, 72, 12, 40, 16, 1, 14, 59, 57, 19),
  (6929, 0, 33, 52, 56, 19, 0, 65, 52, 0, 13),
  (6930, 0, 15, 81, 12, 15, 0, 75, 3, 36, 15),
  (6931, 1, 6, 13, 82, 19, 1, 30, 77, 10, 15),
  (6932, 0, 48, 2, 68, 18, 0, 56, 14, 60, 18),
  (6933, 0, 1, 76, 34, 17, 2, 36, 75, 2, 14),
  (6934, 0, 27, 11, 78, 19, 0, 43, 27, 66, 19),
  (6935, 1, 7, 80, 22, 16, 3, 24, 79, 10, 15),
  (6936, 1, 3, 70, 45, 18, 5, 9, 71, 42, 18),
  (6937, 0, 48, 68, 3, 14, 0, 78, 23, 18, 14),
  (6938, 1, 4, 14, 82, 19, 1, 4, 82, 14, 15),
  (6939, 0, 43, 37, 61, 19, 2, 17, 9, 81, 19),
  (6940, 1, 3, 80, 23, 16, 1, 23, 80, 3, 14),
  (6941, 0, 4, 70, 45, 18, 0, 21, 10, 80, 19),
  (6942, 0, 2, 83, 7, 14, 0, 7, 13, 82, 19),
  (6943, 1, 18, 59, 56, 19, 1, 64, 6, 53, 17),
  (6944, 0, 52, 48, 44, 18, 1, 19, 70, 41, 18),
  (6945, 0, 4, 80, 23, 16, 0, 5, 14, 82, 19),
  (6946, 0, 63, 41, 36, 17, 1, 32, 12, 76, 19),
  (6947, 0, 51, 65, 11, 15, 1, 10, 11, 82, 19),
  (6948, 0, 8, 80, 22, 16, 0, 52, 62, 20, 16),
  (6949, 0, 9, 12, 82, 19, 0, 72, 26, 33, 16)
  ]

lemma witChunk_134_ok : witChunk_134.all checkWit = true := by
  decide +kernel

lemma witChunk_134_ns :
    witChunk_134.map (fun t => t.1) = (List.range 50).map (· + 6900) := by
  decide +kernel

def witChunk_135 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (6950, 0, 1, 82, 15, 15, 0, 17, 10, 81, 19),
  (6951, 1, 0, 82, 15, 15, 5, 76, 6, 33, 15),
  (6952, 1, 5, 83, 6, 14, 1, 22, 75, 29, 17),
  (6953, 0, 58, 33, 50, 18, 0, 68, 40, 27, 16),
  (6954, 0, 37, 16, 73, 19, 0, 67, 23, 44, 17),
  (6955, 0, 15, 59, 57, 19, 0, 67, 21, 45, 17),
  (6956, 1, 53, 7, 64, 18, 1, 53, 47, 44, 18),
  (6957, 1, 45, 57, 41, 18, 1, 57, 15, 59, 18),
  (6958, 0, 3, 15, 82, 19, 0, 81, 6, 19, 13),
  (6959, 1, 8, 82, 13, 15, 1, 66, 51, 0, 13),
  (6960, 1, 81, 19, 6, 12, 2, 38, 72, 18, 16),
  (6961, 0, 6, 83, 6, 14, 0, 81, 12, 16, 13),
  (6962, 0, 21, 80, 11, 15, 0, 35, 51, 56, 19),
  (6963, 0, 43, 25, 67, 19, 0, 67, 25, 43, 17),
  (6964, 1, 11, 80, 21, 16, 2, 34, 74, 18, 16),
  (6965, 0, 17, 76, 30, 17, 0, 18, 79, 20, 16),
  (6966, 0, 11, 11, 82, 19, 0, 11, 59, 58, 19),
  (6967, 1, 15, 82, 4, 14, 1, 22, 9, 80, 19),
  (6968, 1, 18, 9, 81, 19, 1, 42, 21, 69, 19),
  (6969, 2, 15, 60, 56, 19, 2, 39, 16, 72, 19),
  (6970, 0, 43, 39, 60, 19, 0, 61, 0, 57, 17),
  (6971, 0, 59, 49, 33, 17, 0, 83, 1, 9, 11),
  (6972, 1, 47, 0, 69, 18, 2, 42, 60, 40, 18),
  (6973, 1, 9, 71, 43, 18, 1, 73, 39, 11, 14),
  (6974, 0, 9, 82, 13, 15, 0, 58, 19, 57, 18),
  (6975, 1, 51, 4, 66, 18, 1, 59, 24, 54, 18),
  (6976, 0, 0, 80, 24, 16, 0, 64, 48, 24, 16),
  (6977, 0, 57, 52, 32, 17, 0, 81, 4, 20, 13),
  (6978, 0, 19, 59, 56, 19, 2, 11, 60, 57, 19),
  (6979, 0, 3, 57, 61, 19, 0, 39, 47, 57, 19),
  (6980, 0, 32, 66, 40, 18, 3, 53, 48, 43, 18),
  (6981, 0, 1, 16, 82, 19, 0, 1, 56, 62, 19),
  (6982, 0, 51, 59, 30, 17, 0, 67, 27, 42, 17),
  (6983, 1, 34, 71, 28, 17, 1, 38, 49, 56, 19),
  (6984, 0, 48, 54, 42, 18, 1, 59, 30, 51, 18),
  (6985, 0, 12, 80, 21, 16, 0, 24, 80, 3, 14),
  (6986, 0, 69, 44, 17, 15, 2, 5, 77, 32, 17),
  (6987, 0, 67, 17, 47, 17, 2, 45, 27, 65, 19),
  (6988, 1, 25, 69, 40, 18, 1, 55, 44, 45, 18),
  (6989, 0, 5, 58, 60, 19, 0, 30, 67, 40, 18),
  (6990, 0, 10, 71, 43, 18, 0, 31, 77, 10, 15),
  (6991, 1, 6, 77, 32, 17, 1, 38, 69, 28, 17),
  (6992, 0, 36, 64, 40, 18, 0, 68, 48, 8, 14),
  (6993, 0, 13, 10, 82, 19, 0, 57, 60, 12, 15),
  (6994, 0, 39, 17, 72, 19, 1, 16, 60, 56, 19),
  (6995, 0, 23, 75, 29, 17, 0, 75, 1, 37, 15),
  (6996, 0, 16, 82, 4, 14, 0, 56, 62, 4, 14),
  (6997, 1, 9, 83, 5, 14, 1, 61, 57, 5, 14),
  (6998, 0, 50, 3, 67, 18, 0, 50, 67, 3, 14),
  (6999, 3, 26, 8, 79, 19, 3, 44, 41, 58, 19)
  ]

lemma witChunk_135_ok : witChunk_135.all checkWit = true := by
  decide +kernel

lemma witChunk_135_ns :
    witChunk_135.map (fun t => t.1) = (List.range 50).map (· + 6950) := by
  decide +kernel

def witChunk_136 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7000, 0, 60, 54, 22, 16, 1, 6, 59, 59, 19),
  (7001, 0, 14, 71, 42, 18, 0, 56, 12, 61, 18),
  (7002, 0, 7, 77, 32, 17, 0, 29, 56, 55, 19),
  (7003, 0, 19, 9, 81, 19, 0, 27, 57, 55, 19),
  (7004, 1, 5, 71, 44, 18, 1, 41, 61, 40, 18),
  (7005, 0, 37, 50, 56, 19, 2, 72, 7, 42, 16),
  (7006, 0, 66, 45, 25, 16, 0, 66, 51, 7, 14),
  (7007, 1, 35, 76, 2, 14, 1, 59, 32, 50, 18),
  (7008, 0, 28, 68, 40, 18, 1, 18, 81, 11, 15),
  (7009, 0, 33, 12, 76, 19, 4, 68, 48, 7, 14),
  (7010, 0, 23, 9, 80, 19, 1, 40, 68, 28, 17),
  (7011, 0, 7, 59, 59, 19, 0, 11, 77, 31, 17),
  (7012, 0, 72, 8, 42, 16, 1, 65, 47, 24, 16),
  (7013, 0, 6, 71, 44, 18, 0, 38, 63, 40, 18),
  (7014, 0, 10, 83, 5, 14, 0, 25, 58, 55, 19),
  (7015, 1, 30, 73, 28, 17, 1, 56, 54, 31, 17),
  (7016, 0, 0, 70, 46, 18, 0, 56, 42, 46, 18),
  (7017, 0, 58, 17, 58, 18, 0, 70, 1, 46, 16),
  (7018, 0, 13, 60, 57, 19, 0, 45, 32, 63, 19),
  (7019, 0, 35, 13, 75, 19, 0, 47, 63, 29, 17),
  (7020, 1, 57, 13, 60, 18, 1, 77, 33, 0, 12),
  (7021, 0, 24, 78, 19, 16, 0, 45, 30, 64, 19),
  (7022, 2, 37, 13, 74, 19, 4, 50, 1, 67, 18),
  (7023, 5, 68, 18, 45, 17, 9, 26, 59, 52, 19),
  (7024, 1, 2, 77, 33, 17, 1, 33, 77, 2, 14),
  (7025, 0, 17, 60, 56, 19, 0, 29, 10, 78, 19),
  (7026, 0, 53, 64, 11, 15, 0, 61, 56, 13, 15),
  (7027, 0, 3, 77, 33, 17, 1, 14, 77, 30, 17),
  (7028, 1, 47, 56, 41, 18, 1, 49, 1, 68, 18),
  (7029, 1, 81, 21, 5, 12, 2, 44, 69, 18, 16),
  (7030, 0, 15, 9, 82, 19, 0, 33, 54, 55, 19),
  (7031, 1, 23, 70, 40, 18, 1, 39, 72, 18, 16),
  (7032, 3, 53, 62, 19, 16, 4, 60, 22, 54, 18),
  (7033, 4, 21, 76, 28, 17, 4, 58, 39, 46, 18),
  (7034, 0, 45, 28, 65, 19, 0, 77, 12, 31, 15),
  (7035, 0, 23, 59, 55, 19, 2, 45, 39, 59, 19),
  (7036, 1, 69, 47, 8, 14, 3, 0, 77, 33, 17),
  (7037, 0, 13, 82, 12, 15, 0, 26, 69, 40, 18),
  (7038, 0, 65, 38, 37, 17, 2, 33, 55, 54, 19),
  (7039, 1, 42, 67, 28, 17, 1, 43, 72, 2, 14),
  (7040, 1, 33, 75, 18, 16, 1, 42, 45, 57, 19),
  (7041, 0, 37, 14, 74, 19, 2, 34, 66, 39, 18),
  (7042, 0, 45, 36, 61, 19, 1, 24, 8, 80, 19),
  (7043, 0, 19, 81, 11, 15, 0, 63, 43, 35, 17),
  (7044, 0, 40, 62, 40, 18, 3, 4, 11, 83, 19),
  (7045, 0, 9, 60, 58, 19, 0, 72, 30, 31, 16),
  (7046, 0, 18, 71, 41, 18, 0, 41, 18, 71, 19),
  (7047, 3, 9, 72, 42, 18, 3, 16, 7, 82, 19),
  (7048, 0, 64, 54, 6, 14, 0, 72, 42, 10, 14),
  (7049, 2, 20, 71, 40, 18, 2, 58, 14, 59, 18)
  ]

lemma witChunk_136_ok : witChunk_136.all checkWit = true := by
  decide +kernel

lemma witChunk_136_ns :
    witChunk_136.map (fun t => t.1) = (List.range 50).map (· + 7000) := by
  decide +kernel

def witChunk_137 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7050, 0, 35, 71, 28, 17, 0, 67, 31, 40, 17),
  (7051, 0, 27, 9, 79, 19, 0, 43, 21, 69, 19),
  (7052, 1, 67, 44, 25, 16, 1, 73, 11, 40, 16),
  (7053, 0, 37, 70, 28, 17, 0, 52, 50, 43, 18),
  (7054, 0, 15, 77, 30, 17, 0, 22, 81, 3, 14),
  (7055, 1, 8, 10, 83, 19, 1, 14, 61, 56, 19),
  (7056, 0, 16, 80, 20, 16, 1, 59, 18, 57, 18),
  (7057, 0, 1, 84, 0, 13, 0, 33, 72, 28, 17),
  (7058, 0, 5, 12, 83, 19, 0, 21, 76, 29, 17),
  (7059, 0, 7, 11, 83, 19, 0, 35, 53, 55, 19),
  (7060, 1, 51, 64, 19, 16, 1, 55, 8, 63, 18),
  (7061, 0, 54, 7, 64, 18, 0, 54, 47, 44, 18),
  (7062, 0, 43, 43, 58, 19, 0, 82, 17, 7, 12),
  (7063, 1, 31, 76, 18, 16, 5, 12, 62, 55, 19),
  (7064, 0, 68, 42, 26, 16, 1, 2, 13, 83, 19),
  (7065, 0, 48, 0, 69, 18, 2, 18, 82, 3, 14),
  (7066, 0, 21, 8, 81, 19, 0, 21, 60, 55, 19),
  (7067, 0, 3, 13, 83, 19, 0, 83, 13, 3, 11),
  (7068, 3, 17, 80, 19, 16, 3, 53, 4, 65, 18),
  (7069, 0, 45, 38, 60, 19, 0, 52, 66, 3, 14),
  (7070, 0, 2, 71, 45, 18, 0, 9, 10, 83, 19),
  (7071, 1, 11, 72, 42, 18, 1, 51, 52, 42, 18),
  (7072, 0, 84, 0, 4, 10, 1, 5, 81, 22, 16),
  (7073, 0, 38, 75, 2, 14, 0, 50, 53, 42, 18),
  (7074, 0, 31, 73, 28, 17, 2, 0, 71, 45, 18),
  (7075, 0, 39, 15, 73, 19, 1, 26, 59, 54, 19),
  (7076, 0, 24, 70, 40, 18, 0, 36, 76, 2, 14),
  (7077, 0, 17, 8, 82, 19, 2, 6, 72, 43, 18),
  (7078, 1, 24, 80, 10, 15, 1, 32, 56, 54, 19),
  (7079, 1, 55, 46, 44, 18, 3, 20, 81, 10, 15),
  (7080, 0, 40, 74, 2, 14, 0, 56, 10, 62, 18),
  (7081, 0, 6, 81, 22, 16, 2, 43, 18, 70, 19),
  (7082, 0, 15, 61, 56, 19, 0, 77, 8, 33, 15),
  (7083, 1, 59, 36, 48, 18, 2, 37, 75, 9, 15),
  (7084, 1, 7, 72, 43, 18, 1, 21, 71, 40, 18),
  (7085, 0, 42, 61, 40, 18, 0, 60, 26, 53, 18),
  (7086, 0, 1, 14, 83, 19, 0, 1, 58, 61, 19),
  (7087, 1, 0, 14, 83, 19, 1, 0, 58, 61, 19),
  (7088, 0, 60, 28, 52, 18, 1, 29, 79, 2, 14),
  (7089, 0, 25, 8, 80, 19, 0, 34, 77, 2, 14),
  (7090, 0, 3, 59, 60, 19, 0, 45, 24, 67, 19),
  (7091, 0, 11, 9, 83, 19, 0, 11, 61, 57, 19),
  (7092, 0, 12, 72, 42, 18, 0, 60, 24, 54, 18),
  (7093, 0, 84, 6, 1, 10, 1, 1, 81, 23, 16),
  (7094, 0, 2, 81, 23, 16, 0, 3, 83, 14, 15),
  (7095, 3, 82, 8, 17, 13, 5, 68, 30, 39, 17),
  (7096, 0, 36, 74, 18, 16, 1, 6, 83, 13, 15),
  (7097, 0, 8, 72, 43, 18, 0, 38, 73, 18, 16),
  (7098, 0, 37, 52, 55, 19, 2, 0, 81, 23, 16),
  (7099, 0, 67, 33, 39, 17, 1, 4, 60, 59, 19)
  ]

lemma witChunk_137_ok : witChunk_137.all checkWit = true := by
  decide +kernel

lemma witChunk_137_ns :
    witChunk_137.map (fun t => t.1) = (List.range 50).map (· + 7050) := by
  decide +kernel

def witChunk_138 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7100, 3, 11, 81, 20, 16, 3, 12, 7, 83, 19),
  (7101, 0, 14, 83, 4, 14, 0, 29, 74, 28, 17),
  (7102, 0, 10, 81, 21, 16, 0, 73, 42, 3, 13),
  (7103, 1, 3, 84, 6, 14, 1, 16, 82, 11, 15),
  (7104, 1, 35, 66, 39, 18, 2, 2, 84, 6, 14),
  (7105, 0, 0, 84, 7, 14, 0, 34, 75, 18, 16),
  (7106, 0, 5, 60, 59, 19, 0, 45, 40, 59, 19),
  (7107, 0, 7, 83, 13, 15, 0, 19, 61, 55, 19),
  (7108, 0, 4, 84, 6, 14, 0, 40, 72, 18, 16),
  (7109, 0, 60, 22, 55, 18, 1, 49, 55, 41, 18),
  (7110, 0, 43, 19, 70, 19, 0, 67, 11, 50, 17),
  (7111, 1, 8, 78, 31, 17, 1, 42, 47, 56, 19),
  (7112, 0, 32, 78, 2, 14, 0, 80, 6, 26, 14),
  (7113, 2, 11, 78, 30, 17, 2, 12, 81, 20, 16),
  (7114, 0, 61, 48, 33, 17, 3, 66, 6, 52, 17),
  (7115, 0, 55, 63, 11, 15, 0, 67, 49, 15, 15),
  (7116, 1, 83, 0, 15, 12, 1, 83, 12, 9, 12),
  (7117, 1, 37, 65, 39, 18, 2, 31, 8, 78, 19),
  (7118, 0, 33, 10, 77, 19, 0, 62, 57, 5, 14),
  (7119, 3, 4, 61, 58, 19, 3, 34, 56, 53, 19),
  (7120, 0, 84, 8, 0, 10, 1, 46, 39, 59, 19),
  (7121, 0, 16, 72, 41, 18, 0, 29, 58, 54, 19),
  (7122, 0, 13, 8, 83, 19, 0, 35, 11, 76, 19),
  (7123, 0, 43, 45, 57, 19, 1, 6, 61, 58, 19),
  (7124, 0, 32, 76, 18, 16, 0, 44, 72, 2, 14),
  (7125, 0, 22, 71, 40, 18, 0, 25, 80, 10, 15),
  (7126, 0, 9, 78, 31, 17, 0, 27, 59, 54, 19),
  (7127, 1, 16, 62, 55, 19, 1, 26, 7, 80, 19),
  (7128, 4, 36, 66, 38, 18, 5, 61, 21, 54, 18),
  (7129, 0, 42, 71, 18, 16, 2, 19, 6, 82, 19),
  (7130, 0, 77, 24, 25, 15, 1, 12, 78, 30, 17),
  (7131, 0, 19, 77, 29, 17, 1, 3, 72, 44, 18),
  (7132, 1, 7, 84, 5, 14, 1, 13, 81, 20, 16),
  (7133, 0, 5, 78, 32, 17, 0, 20, 82, 3, 14),
  (7134, 0, 7, 61, 58, 19, 0, 17, 82, 11, 15),
  (7135, 1, 10, 83, 12, 15, 1, 27, 80, 2, 14),
  (7136, 0, 4, 72, 44, 18, 0, 44, 60, 40, 18),
  (7137, 0, 62, 53, 22, 16, 2, 42, 62, 39, 18),
  (7138, 0, 27, 75, 28, 17, 0, 37, 12, 75, 19),
  (7139, 0, 23, 7, 81, 19, 0, 47, 31, 63, 19),
  (7140, 1, 39, 64, 39, 18, 3, 64, 1, 55, 17),
  (7141, 0, 25, 60, 54, 19, 0, 33, 56, 54, 19),
  (7142, 0, 47, 33, 62, 19, 0, 74, 21, 35, 16),
  (7143, 3, 44, 17, 70, 19, 5, 55, 48, 42, 18),
  (7144, 1, 62, 47, 33, 17, 1, 73, 7, 42, 16),
  (7145, 0, 8, 84, 5, 14, 0, 30, 79, 2, 14),
  (7146, 0, 29, 8, 79, 19, 0, 47, 29, 64, 19),
  (7147, 0, 39, 51, 55, 19, 1, 19, 72, 40, 18),
  (7148, 3, 36, 55, 53, 19, 3, 59, 57, 20, 16),
  (7149, 0, 13, 62, 56, 19, 2, 24, 79, 18, 16)
  ]

lemma witChunk_138_ok : witChunk_138.all checkWit = true := by
  decide +kernel

lemma witChunk_138_ns :
    witChunk_138.map (fun t => t.1) = (List.range 50).map (· + 7100) := by
  decide +kernel

def witChunk_139 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7150, 0, 54, 65, 3, 14, 0, 63, 45, 34, 17),
  (7151, 1, 83, 14, 8, 12, 3, 74, 36, 19, 15),
  (7152, 1, 27, 70, 39, 18, 1, 38, 75, 9, 15),
  (7153, 0, 13, 78, 30, 17, 0, 30, 77, 18, 16),
  (7154, 0, 11, 83, 12, 15, 2, 43, 16, 71, 19),
  (7155, 0, 47, 35, 61, 19, 0, 75, 33, 21, 15),
  (7156, 1, 61, 27, 52, 18, 3, 12, 63, 55, 19),
  (7157, 0, 14, 81, 20, 16, 0, 60, 34, 49, 18),
  (7158, 0, 17, 62, 55, 19, 0, 67, 35, 38, 17),
  (7159, 1, 8, 62, 57, 19, 1, 40, 74, 9, 15),
  (7160, 0, 44, 70, 18, 16, 1, 59, 14, 59, 18),
  (7161, 0, 20, 80, 19, 16, 0, 46, 71, 2, 14),
  (7162, 0, 75, 39, 4, 13, 1, 20, 6, 82, 19),
  (7163, 0, 15, 7, 83, 19, 0, 47, 27, 65, 19),
  (7164, 3, 21, 72, 39, 18, 3, 37, 76, 1, 14),
  (7165, 0, 45, 66, 28, 17, 1, 61, 29, 51, 18),
  (7166, 0, 23, 61, 54, 19, 0, 34, 67, 39, 18),
  (7167, 3, 20, 5, 82, 19, 3, 34, 8, 77, 19),
  (7168, 1, 34, 9, 77, 19, 1, 34, 77, 9, 15),
  (7169, 0, 32, 68, 39, 18, 0, 56, 8, 63, 18),
  (7170, 0, 77, 4, 35, 15, 2, 5, 9, 84, 19),
  (7171, 0, 67, 9, 51, 17, 1, 38, 53, 54, 19),
  (7172, 0, 52, 52, 42, 18, 3, 12, 83, 11, 15),
  (7173, 0, 36, 66, 39, 18, 0, 60, 18, 57, 18),
  (7174, 0, 1, 78, 33, 17, 0, 9, 62, 57, 19),
  (7175, 1, 0, 78, 33, 17, 1, 6, 9, 84, 19),
  (7176, 1, 9, 73, 42, 18, 1, 42, 73, 9, 15),
  (7177, 0, 60, 56, 21, 16, 2, 7, 8, 84, 19),
  (7178, 0, 27, 7, 80, 19, 0, 47, 37, 60, 19),
  (7179, 0, 43, 17, 71, 19, 0, 71, 43, 17, 15),
  (7180, 1, 55, 48, 43, 18, 2, 10, 84, 4, 14),
  (7181, 0, 5, 10, 84, 19, 0, 69, 22, 44, 17),
  (7182, 0, 30, 69, 39, 18, 2, 17, 63, 54, 19),
  (7183, 1, 2, 11, 84, 19, 1, 16, 6, 83, 19),
  (7184, 0, 20, 72, 40, 18, 1, 61, 31, 50, 18),
  (7185, 0, 25, 76, 28, 17, 0, 68, 44, 25, 16),
  (7186, 0, 3, 11, 84, 19, 0, 7, 9, 84, 19),
  (7187, 2, 13, 83, 11, 15, 2, 41, 13, 73, 19),
  (7188, 0, 28, 80, 2, 14, 0, 56, 46, 44, 18),
  (7189, 1, 17, 83, 3, 14, 1, 25, 71, 39, 18),
  (7190, 0, 23, 81, 10, 15, 0, 38, 65, 39, 18),
  (7191, 1, 32, 78, 9, 15, 1, 78, 9, 32, 15),
  (7192, 0, 28, 78, 18, 16, 1, 14, 63, 55, 19),
  (7193, 0, 10, 73, 42, 18, 2, 16, 73, 40, 18),
  (7194, 0, 43, 47, 56, 19, 2, 9, 7, 84, 19),
  (7195, 1, 11, 84, 4, 14, 1, 28, 60, 53, 19),
  (7196, 1, 83, 16, 7, 12, 3, 20, 63, 53, 19),
  (7197, 0, 46, 59, 40, 18, 0, 52, 2, 67, 18),
  (7198, 2, 21, 5, 82, 19, 2, 47, 70, 9, 15),
  (7199, 1, 22, 77, 28, 17, 1, 32, 58, 53, 19)
  ]

lemma witChunk_139_ok : witChunk_139.all checkWit = true := by
  decide +kernel

lemma witChunk_139_ns :
    witChunk_139.map (fun t => t.1) = (List.range 50).map (· + 7150) := by
  decide +kernel

def witChunk_140 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7200, 0, 60, 36, 48, 18, 1, 51, 54, 41, 18),
  (7201, 0, 1, 12, 84, 19, 0, 1, 60, 60, 19),
  (7202, 1, 0, 12, 84, 19, 1, 0, 60, 60, 19),
  (7203, 1, 44, 72, 9, 15, 1, 78, 21, 26, 15),
  (7204, 3, 84, 11, 3, 11, 7, 28, 61, 51, 19),
  (7205, 0, 28, 70, 39, 18, 1, 5, 73, 43, 18),
  (7206, 0, 14, 73, 41, 18, 0, 41, 14, 73, 19),
  (7207, 1, 10, 7, 84, 19, 1, 10, 63, 56, 19),
  (7208, 0, 48, 70, 2, 14, 0, 80, 22, 18, 14),
  (7209, 0, 0, 72, 45, 18, 2, 6, 82, 21, 16),
  (7210, 0, 45, 44, 57, 19, 2, 43, 68, 27, 17),
  (7211, 0, 3, 61, 59, 19, 0, 47, 39, 59, 19),
  (7212, 1, 57, 45, 44, 18, 3, 53, 52, 41, 18),
  (7213, 0, 72, 2, 45, 16, 1, 17, 81, 19, 16),
  (7214, 0, 6, 73, 43, 18, 0, 17, 6, 83, 19),
  (7215, 3, 40, 11, 74, 19, 5, 84, 10, 3, 11),
  (7216, 0, 12, 84, 4, 14, 0, 60, 60, 4, 14),
  (7217, 0, 40, 64, 39, 18, 2, 38, 74, 17, 16),
  (7218, 0, 47, 65, 28, 17, 2, 27, 80, 9, 15),
  (7219, 0, 15, 63, 55, 19, 1, 3, 82, 22, 16),
  (7220, 0, 60, 16, 58, 18, 1, 17, 73, 40, 18),
  (7221, 2, 11, 6, 84, 19, 2, 83, 18, 0, 11),
  (7222, 0, 18, 83, 3, 14, 0, 25, 6, 81, 19),
  (7223, 1, 71, 46, 8, 14, 3, 8, 79, 30, 17),
  (7224, 0, 4, 82, 22, 16, 1, 30, 79, 9, 15),
  (7225, 2, 3, 62, 58, 19, 2, 58, 62, 3, 14),
  (7226, 0, 11, 7, 84, 19, 0, 11, 63, 56, 19),
  (7227, 0, 39, 75, 9, 15, 0, 47, 23, 67, 19),
  (7228, 3, 45, 72, 1, 14, 3, 57, 60, 19, 16),
  (7229, 0, 8, 82, 21, 16, 0, 61, 58, 12, 15),
  (7230, 2, 9, 79, 30, 17, 2, 33, 7, 78, 19),
  (7231, 1, 24, 62, 53, 19, 1, 32, 74, 27, 17),
  (7232, 1, 55, 62, 19, 16, 2, 10, 82, 20, 16),
  (7233, 0, 5, 62, 58, 19, 2, 68, 45, 24, 16),
  (7234, 1, 64, 0, 56, 17, 2, 36, 77, 1, 14),
  (7235, 0, 15, 83, 11, 15, 0, 35, 9, 77, 19),
  (7236, 0, 84, 6, 12, 12, 1, 23, 72, 39, 18),
  (7237, 0, 33, 8, 78, 19, 0, 81, 24, 10, 13),
  (7238, 0, 26, 71, 39, 18, 0, 41, 74, 9, 15),
  (7239, 1, 62, 57, 12, 15, 1, 72, 42, 17, 15),
  (7240, 1, 6, 79, 31, 17, 1, 18, 5, 83, 19),
  (7241, 0, 26, 79, 18, 16, 0, 26, 81, 2, 14),
  (7242, 0, 23, 77, 28, 17, 0, 67, 7, 52, 17),
  (7243, 1, 4, 84, 13, 15, 1, 10, 79, 30, 17),
  (7244, 2, 50, 56, 40, 18, 2, 58, 44, 44, 18),
  (7245, 0, 37, 10, 76, 19, 0, 58, 59, 20, 16),
  (7246, 0, 18, 81, 19, 16, 0, 19, 63, 54, 19),
  (7247, 1, 11, 82, 20, 16, 1, 59, 58, 20, 16),
  (7248, 4, 84, 4, 12, 12, 5, 50, 27, 63, 19),
  (7249, 0, 45, 18, 70, 19, 2, 34, 78, 1, 14)
  ]

lemma witChunk_140_ok : witChunk_140.all checkWit = true := by
  decide +kernel

lemma witChunk_140_ns :
    witChunk_140.map (fun t => t.1) = (List.range 50).map (· + 7200) := by
  decide +kernel

def witChunk_141 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7250, 0, 5, 84, 13, 15, 0, 29, 60, 53, 19),
  (7251, 0, 7, 79, 31, 17, 0, 31, 7, 79, 19),
  (7252, 0, 48, 68, 18, 16, 1, 49, 57, 40, 18),
  (7253, 0, 0, 82, 23, 16, 0, 1, 84, 14, 15),
  (7254, 0, 33, 78, 9, 15, 0, 42, 63, 39, 18),
  (7255, 1, 23, 80, 18, 16, 1, 50, 63, 28, 17),
  (7256, 0, 84, 2, 14, 12, 0, 84, 10, 10, 12),
  (7257, 0, 64, 56, 5, 14, 0, 70, 41, 26, 16),
  (7258, 0, 43, 15, 72, 19, 1, 84, 14, 2, 11),
  (7259, 0, 27, 61, 53, 19, 0, 43, 73, 9, 15),
  (7260, 3, 29, 80, 1, 14, 3, 85, 4, 1, 10),
  (7261, 0, 13, 6, 84, 19, 0, 69, 14, 48, 17),
  (7262, 0, 11, 79, 30, 17, 0, 33, 58, 53, 19),
  (7263, 3, 13, 74, 40, 18, 3, 16, 83, 10, 15),
  (7264, 0, 72, 36, 28, 16, 1, 1, 85, 6, 14),
  (7265, 0, 2, 85, 6, 14, 0, 21, 82, 10, 15),
  (7266, 0, 83, 11, 16, 13, 1, 8, 84, 12, 15),
  (7267, 0, 7, 63, 57, 19, 0, 39, 11, 75, 19),
  (7268, 0, 12, 82, 20, 16, 0, 48, 58, 40, 18),
  (7269, 0, 2, 73, 44, 18, 0, 49, 32, 62, 19),
  (7270, 0, 49, 30, 63, 19, 1, 16, 64, 54, 19),
  (7271, 1, 2, 79, 32, 17, 1, 62, 49, 32, 17),
  (7272, 1, 59, 42, 45, 18, 3, 13, 82, 19, 16),
  (7273, 2, 0, 73, 44, 18, 2, 31, 60, 52, 19),
  (7274, 0, 3, 79, 32, 17, 0, 47, 21, 68, 19),
  (7275, 0, 19, 5, 83, 19, 0, 43, 49, 55, 19),
  (7276, 1, 73, 3, 44, 16, 1, 85, 7, 0, 10),
  (7277, 0, 29, 6, 80, 19, 0, 45, 46, 56, 19),
  (7278, 0, 23, 5, 82, 19, 0, 25, 62, 53, 19),
  (7279, 1, 14, 5, 84, 19, 1, 46, 45, 56, 19),
  (7280, 1, 11, 74, 41, 18, 1, 14, 79, 29, 17),
  (7281, 0, 9, 84, 12, 15, 0, 24, 72, 39, 18),
  (7282, 0, 37, 72, 27, 17, 2, 33, 59, 52, 19),
  (7283, 0, 31, 79, 9, 15, 0, 35, 57, 53, 19),
  (7284, 0, 64, 52, 22, 16, 2, 6, 74, 42, 18),
  (7285, 0, 57, 56, 30, 17, 1, 37, 75, 17, 16),
  (7286, 0, 6, 85, 5, 14, 0, 62, 29, 51, 18),
  (7287, 1, 48, 70, 9, 15, 1, 78, 25, 24, 15),
  (7288, 1, 39, 74, 17, 16, 1, 70, 19, 45, 17),
  (7289, 0, 56, 48, 43, 18, 0, 58, 9, 62, 18),
  (7290, 0, 13, 64, 55, 19, 0, 45, 72, 9, 15),
  (7291, 0, 39, 71, 27, 17, 1, 7, 74, 42, 18),
  (7292, 1, 15, 84, 3, 14, 1, 35, 76, 17, 16),
  (7293, 0, 85, 2, 8, 11, 1, 21, 73, 39, 18),
  (7294, 0, 33, 74, 27, 17, 2, 49, 23, 66, 19),
  (7295, 1, 35, 68, 38, 18, 3, 10, 84, 11, 15),
  (7296, 1, 33, 69, 38, 18, 1, 81, 27, 2, 12),
  (7297, 0, 49, 36, 60, 19, 0, 85, 6, 6, 11),
  (7298, 0, 77, 0, 37, 15, 0, 83, 3, 20, 13),
  (7299, 2, 45, 15, 71, 19, 3, 16, 79, 28, 17)
  ]

lemma witChunk_141_ok : witChunk_141.all checkWit = true := by
  decide +kernel

lemma witChunk_141_ns :
    witChunk_141.map (fun t => t.1) = (List.range 50).map (· + 7250) := by
  decide +kernel

def witChunk_142 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7300, 0, 24, 80, 18, 16, 0, 72, 0, 46, 16),
  (7301, 0, 12, 74, 41, 18, 0, 17, 64, 54, 19),
  (7302, 0, 49, 26, 65, 19, 2, 47, 18, 69, 19),
  (7303, 1, 15, 74, 40, 18, 1, 32, 6, 79, 19),
  (7304, 0, 8, 74, 42, 18, 0, 24, 82, 2, 14),
  (7305, 0, 62, 31, 50, 18, 2, 15, 4, 84, 19),
  (7306, 0, 15, 5, 84, 19, 0, 67, 39, 36, 17),
  (7307, 0, 15, 79, 29, 17, 0, 23, 63, 53, 19),
  (7308, 3, 4, 7, 85, 19, 3, 7, 85, 4, 14),
  (7309, 0, 21, 78, 28, 17, 1, 33, 77, 17, 16),
  (7310, 0, 41, 70, 27, 17, 0, 62, 21, 55, 18),
  (7311, 3, 2, 8, 85, 19, 5, 14, 3, 84, 19),
  (7312, 1, 2, 9, 85, 19, 1, 6, 7, 85, 19),
  (7313, 0, 9, 64, 56, 19, 0, 50, 67, 18, 16),
  (7314, 0, 5, 8, 85, 19, 0, 37, 56, 53, 19),
  (7315, 0, 3, 9, 85, 19, 0, 27, 5, 81, 19),
  (7316, 0, 60, 40, 46, 18, 0, 68, 46, 24, 16),
  (7317, 0, 65, 44, 34, 17, 2, 82, 24, 3, 12),
  (7318, 0, 81, 26, 9, 13, 1, 24, 4, 82, 19),
  (7319, 1, 48, 42, 57, 19, 1, 71, 40, 26, 16),
  (7320, 1, 26, 81, 9, 15, 1, 78, 3, 35, 15),
  (7321, 0, 16, 84, 3, 14, 4, 36, 68, 37, 18),
  (7322, 0, 29, 80, 9, 15, 0, 45, 16, 71, 19),
  (7323, 0, 7, 7, 85, 19, 0, 59, 61, 11, 15),
  (7324, 1, 9, 85, 4, 14, 1, 43, 72, 17, 16),
  (7325, 0, 58, 45, 44, 18, 2, 79, 20, 26, 15),
  (7326, 0, 1, 10, 85, 19, 0, 1, 62, 59, 19),
  (7327, 1, 0, 10, 85, 19, 1, 0, 62, 59, 19),
  (7328, 0, 52, 0, 68, 18, 1, 21, 81, 18, 16),
  (7329, 2, 18, 74, 39, 18, 2, 60, 11, 60, 18),
  (7330, 1, 16, 4, 84, 19, 1, 32, 60, 52, 19),
  (7331, 0, 47, 19, 69, 19, 0, 47, 71, 9, 15),
  (7332, 0, 16, 74, 40, 18, 0, 52, 68, 2, 14),
  (7333, 0, 49, 24, 66, 19, 1, 33, 79, 1, 14),
  (7334, 0, 22, 73, 39, 18, 0, 62, 33, 49, 18),
  (7335, 3, 40, 71, 26, 17, 3, 57, 48, 42, 18),
  (7336, 1, 3, 74, 43, 18, 1, 21, 83, 2, 14),
  (7337, 0, 74, 31, 30, 16, 2, 2, 74, 43, 18),
  (7338, 2, 60, 61, 3, 14, 2, 83, 0, 21, 13),
  (7339, 0, 43, 69, 27, 17, 1, 2, 63, 58, 19),
  (7340, 1, 73, 35, 28, 16, 7, 64, 55, 11, 15),
  (7341, 0, 4, 74, 43, 18, 0, 10, 85, 4, 14),
  (7342, 0, 3, 63, 58, 19, 0, 9, 6, 85, 19),
  (7343, 1, 34, 59, 52, 19, 1, 56, 58, 29, 17),
  (7344, 0, 60, 12, 60, 18, 1, 50, 69, 9, 15),
  (7345, 6, 51, 24, 64, 19, 6, 54, 66, 1, 14),
  (7346, 0, 13, 84, 11, 15, 0, 21, 4, 83, 19),
  (7347, 0, 43, 13, 73, 19, 0, 55, 59, 29, 17),
  (7348, 1, 81, 1, 28, 14, 2, 66, 50, 22, 16),
  (7349, 0, 50, 57, 40, 18, 2, 74, 4, 43, 16)
  ]

lemma witChunk_142_ok : witChunk_142.all checkWit = true := by
  decide +kernel

lemma witChunk_142_ns :
    witChunk_142.map (fun t => t.1) = (List.range 50).map (· + 7300) := by
  decide +kernel

def witChunk_143 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7350, 0, 19, 83, 10, 15, 0, 55, 65, 10, 15),
  (7351, 1, 18, 79, 28, 17, 1, 26, 63, 52, 19),
  (7352, 1, 10, 5, 85, 19, 1, 10, 65, 55, 19),
  (7353, 2, 35, 6, 78, 19, 2, 51, 30, 62, 19),
  (7354, 0, 45, 48, 55, 19, 0, 51, 63, 28, 17),
  (7355, 0, 39, 55, 53, 19, 0, 75, 37, 19, 15),
  (7356, 1, 63, 24, 53, 18, 1, 63, 28, 51, 18),
  (7357, 0, 72, 38, 27, 16, 1, 5, 83, 21, 16),
  (7358, 0, 35, 7, 78, 19, 0, 38, 75, 17, 16),
  (7359, 1, 27, 72, 38, 18, 3, 10, 4, 85, 19),
  (7360, 1, 18, 65, 53, 19, 1, 19, 74, 39, 18),
  (7361, 0, 17, 4, 84, 19, 0, 34, 69, 38, 18),
  (7362, 0, 37, 8, 77, 19, 0, 63, 57, 12, 15),
  (7363, 1, 4, 64, 57, 19, 1, 28, 4, 81, 19),
  (7364, 0, 36, 68, 38, 18, 0, 60, 58, 20, 16),
  (7365, 0, 25, 4, 82, 19, 0, 40, 74, 17, 16),
  (7366, 0, 6, 83, 21, 16, 0, 15, 65, 54, 19),
  (7367, 3, 2, 64, 57, 19, 3, 17, 84, 2, 14),
  (7368, 0, 32, 70, 38, 18, 3, 25, 82, 1, 14),
  (7369, 0, 22, 81, 18, 16, 2, 39, 8, 76, 19),
  (7370, 0, 5, 64, 57, 19, 0, 47, 45, 56, 19),
  (7371, 0, 11, 5, 85, 19, 0, 11, 65, 55, 19),
  (7372, 1, 9, 83, 20, 16, 1, 57, 5, 64, 18),
  (7373, 0, 62, 35, 48, 18, 1, 29, 79, 17, 16),
  (7374, 0, 34, 77, 17, 16, 0, 38, 77, 1, 14),
  (7375, 1, 70, 13, 48, 17, 3, 34, 60, 51, 19),
  (7376, 1, 1, 83, 22, 16, 3, 33, 70, 37, 18),
  (7377, 0, 2, 83, 22, 16, 0, 22, 83, 2, 14),
  (7378, 0, 39, 9, 76, 19, 0, 45, 68, 27, 17),
  (7379, 0, 79, 7, 33, 15, 1, 4, 80, 31, 17),
  (7380, 2, 18, 82, 18, 16, 3, 37, 68, 37, 18),
  (7381, 0, 9, 80, 30, 17, 0, 36, 78, 1, 14),
  (7382, 0, 42, 73, 17, 16, 0, 49, 70, 9, 15),
  (7383, 1, 24, 82, 9, 15, 1, 78, 1, 36, 15),
  (7384, 0, 52, 66, 18, 16, 1, 22, 3, 83, 19),
  (7385, 0, 30, 71, 38, 18, 2, 31, 4, 80, 19),
  (7386, 0, 5, 80, 31, 17, 0, 19, 79, 28, 17),
  (7387, 0, 27, 77, 27, 17, 1, 12, 4, 85, 19),
  (7388, 2, 62, 56, 20, 16, 2, 82, 16, 20, 14),
  (7389, 0, 10, 83, 20, 16, 0, 29, 62, 52, 19),
  (7390, 0, 42, 75, 1, 14, 0, 82, 15, 21, 14),
  (7391, 1, 18, 3, 84, 19, 1, 24, 78, 27, 17),
  (7392, 2, 18, 84, 2, 14, 2, 78, 34, 12, 14),
  (7393, 0, 33, 60, 52, 19, 2, 50, 58, 39, 18),
  (7394, 0, 63, 49, 32, 17, 0, 77, 32, 21, 15),
  (7395, 0, 19, 65, 53, 19, 0, 67, 41, 35, 17),
  (7396, 0, 76, 18, 36, 16, 1, 13, 75, 40, 18),
  (7397, 0, 20, 74, 39, 18, 0, 32, 78, 17, 16),
  (7398, 0, 34, 79, 1, 14, 0, 47, 17, 70, 19),
  (7399, 1, 6, 65, 56, 19, 1, 38, 57, 52, 19)
  ]

lemma witChunk_143_ok : witChunk_143.all checkWit = true := by
  decide +kernel

lemma witChunk_143_ns :
    witChunk_143.map (fun t => t.1) = (List.range 50).map (· + 7350) := by
  decide +kernel

def witChunk_144 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7400, 0, 40, 66, 38, 18, 0, 56, 50, 42, 18),
  (7401, 0, 76, 16, 37, 16, 0, 76, 20, 35, 16),
  (7402, 0, 27, 63, 52, 19, 2, 5, 85, 12, 15),
  (7403, 0, 3, 85, 13, 15, 2, 1, 85, 13, 15),
  (7404, 3, 44, 11, 73, 19, 3, 52, 31, 61, 19),
  (7405, 0, 45, 14, 72, 19, 1, 13, 85, 3, 14),
  (7406, 0, 10, 75, 41, 18, 0, 41, 10, 75, 19),
  (7407, 1, 6, 85, 12, 15, 3, 28, 77, 26, 17),
  (7408, 1, 62, 51, 31, 17, 1, 85, 9, 10, 12),
  (7409, 0, 44, 72, 17, 16, 0, 54, 67, 2, 14),
  (7410, 0, 7, 65, 56, 19, 0, 13, 4, 85, 19),
  (7411, 0, 51, 29, 63, 19, 0, 51, 33, 61, 19),
  (7412, 0, 0, 74, 44, 18, 0, 28, 72, 38, 18),
  (7413, 0, 44, 74, 1, 14, 0, 82, 17, 20, 14),
  (7414, 0, 49, 42, 57, 19, 0, 67, 3, 54, 17),
  (7415, 1, 22, 65, 52, 19, 3, 80, 31, 6, 13),
  (7416, 0, 76, 14, 38, 16, 0, 76, 22, 34, 16),
  (7417, 2, 15, 80, 28, 17, 2, 51, 38, 58, 19),
  (7418, 0, 7, 85, 12, 15, 0, 29, 4, 81, 19),
  (7419, 0, 71, 23, 43, 17, 2, 21, 79, 27, 17),
  (7420, 1, 27, 80, 17, 16, 1, 73, 45, 8, 14),
  (7421, 0, 14, 75, 40, 18, 0, 60, 10, 61, 18),
  (7422, 0, 58, 47, 43, 18, 0, 62, 37, 47, 18),
  (7423, 1, 16, 66, 53, 19, 1, 19, 84, 2, 14),
  (7424, 0, 80, 32, 0, 12, 1, 34, 5, 79, 19),
  (7425, 0, 1, 80, 32, 17, 0, 6, 75, 42, 18),
  (7426, 0, 19, 3, 84, 19, 0, 51, 27, 64, 19),
  (7427, 0, 23, 3, 83, 19, 0, 47, 67, 27, 17),
  (7428, 3, 8, 85, 11, 15, 3, 35, 77, 16, 16),
  (7429, 1, 61, 41, 45, 18, 1, 73, 37, 27, 16),
  (7430, 0, 14, 85, 3, 14, 0, 25, 82, 9, 15),
  (7431, 1, 63, 18, 56, 18, 1, 63, 34, 48, 18),
  (7432, 0, 0, 86, 6, 14, 1, 3, 86, 5, 14),
  (7433, 0, 42, 65, 38, 18, 0, 62, 15, 58, 18),
  (7434, 2, 24, 81, 17, 16, 2, 27, 64, 51, 19),
  (7435, 1, 46, 49, 54, 19, 1, 58, 63, 10, 15),
  (7436, 1, 53, 55, 40, 18, 1, 79, 32, 13, 14),
  (7437, 0, 4, 86, 5, 14, 0, 37, 58, 52, 19),
  (7438, 0, 25, 78, 27, 17, 2, 7, 66, 55, 19),
  (7439, 1, 38, 77, 8, 15, 1, 80, 14, 29, 15),
  (7440, 0, 52, 56, 40, 18, 1, 45, 63, 38, 18),
  (7441, 0, 13, 66, 54, 19, 0, 45, 50, 54, 19),
  (7442, 0, 61, 60, 11, 15, 0, 71, 49, 0, 13),
  (7443, 0, 47, 47, 55, 19, 0, 51, 69, 9, 15),
  (7444, 1, 59, 60, 19, 16, 1, 61, 11, 60, 18),
  (7445, 0, 17, 84, 10, 15, 0, 57, 64, 10, 15),
  (7446, 0, 14, 83, 19, 16, 0, 43, 11, 74, 19),
  (7447, 1, 8, 66, 55, 19, 1, 48, 46, 55, 19),
  (7448, 0, 20, 82, 18, 16, 1, 10, 85, 11, 15),
  (7449, 0, 26, 73, 38, 18, 2, 3, 6, 86, 19)
  ]

lemma witChunk_144_ok : witChunk_144.all checkWit = true := by
  decide +kernel

lemma witChunk_144_ns :
    witChunk_144.map (fun t => t.1) = (List.range 50).map (· + 7400) := by
  decide +kernel

def witChunk_145 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7450, 1, 4, 6, 86, 19, 1, 36, 74, 26, 17),
  (7451, 0, 51, 25, 65, 19, 0, 51, 37, 59, 19),
  (7452, 3, 43, 73, 16, 16, 3, 53, 68, 1, 14),
  (7453, 0, 60, 62, 3, 14, 0, 64, 54, 21, 16),
  (7454, 0, 3, 7, 86, 19, 0, 17, 66, 53, 19),
  (7455, 1, 42, 75, 8, 15, 1, 80, 18, 27, 15),
  (7456, 1, 22, 79, 27, 17, 1, 22, 83, 9, 15),
  (7457, 0, 5, 6, 86, 19, 0, 68, 48, 23, 16),
  (7458, 0, 23, 65, 52, 19, 2, 51, 40, 57, 19),
  (7459, 0, 15, 3, 85, 19, 1, 6, 5, 86, 19),
  (7460, 0, 20, 84, 2, 14, 0, 72, 40, 26, 16),
  (7461, 0, 1, 8, 86, 19, 0, 1, 64, 58, 19),
  (7462, 0, 9, 66, 55, 19, 0, 27, 3, 82, 19),
  (7463, 1, 7, 86, 4, 14, 1, 34, 79, 8, 15),
  (7464, 3, 61, 58, 19, 16, 5, 18, 67, 51, 19),
  (7465, 0, 54, 65, 18, 16, 2, 27, 2, 82, 19),
  (7466, 2, 40, 67, 37, 18, 2, 59, 56, 29, 17),
  (7467, 0, 11, 85, 11, 15, 0, 43, 53, 53, 19),
  (7468, 3, 39, 77, 0, 14, 3, 40, 57, 51, 19),
  (7469, 2, 7, 4, 86, 19, 4, 5, 4, 86, 19),
  (7470, 0, 7, 5, 86, 19, 0, 18, 75, 39, 18),
  (7471, 1, 24, 2, 83, 19, 1, 32, 62, 51, 19),
  (7472, 0, 60, 44, 44, 18, 1, 30, 3, 81, 19),
  (7473, 0, 17, 80, 28, 17, 0, 28, 80, 17, 16),
  (7474, 0, 39, 57, 52, 19, 2, 24, 83, 1, 14),
  (7475, 0, 47, 15, 71, 19, 0, 71, 15, 47, 17),
  (7476, 0, 8, 86, 4, 14, 0, 44, 64, 38, 18),
  (7477, 1, 1, 75, 43, 18, 1, 25, 81, 17, 16),
  (7478, 0, 2, 75, 43, 18, 0, 75, 43, 2, 13),
  (7479, 3, 18, 84, 9, 15, 3, 50, 44, 55, 19),
  (7480, 1, 2, 65, 57, 19, 1, 34, 61, 51, 19),
  (7481, 0, 62, 39, 46, 18, 0, 64, 24, 53, 18),
  (7482, 0, 71, 29, 40, 17, 0, 85, 16, 1, 11),
  (7483, 0, 3, 65, 57, 19, 1, 28, 64, 51, 19),
  (7484, 2, 10, 76, 40, 18, 2, 38, 76, 16, 16),
  (7485, 0, 58, 5, 64, 18, 0, 74, 35, 28, 16),
  (7486, 0, 49, 18, 69, 19, 0, 49, 66, 27, 17),
  (7487, 1, 16, 2, 85, 19, 1, 50, 19, 68, 19),
  (7488, 1, 51, 58, 39, 18, 1, 54, 67, 9, 15),
  (7489, 0, 37, 6, 78, 19, 0, 48, 72, 1, 14),
  (7490, 1, 32, 80, 8, 15, 1, 72, 48, 0, 13),
  (7491, 0, 35, 5, 79, 19, 0, 79, 35, 5, 13),
  (7492, 1, 65, 57, 4, 14, 1, 75, 4, 43, 16),
  (7493, 0, 9, 4, 86, 19, 0, 48, 70, 17, 16),
  (7494, 0, 62, 13, 59, 18, 0, 67, 43, 34, 17),
  (7495, 1, 42, 55, 52, 19, 1, 86, 9, 4, 11),
  (7496, 0, 24, 74, 38, 18, 0, 56, 2, 66, 18),
  (7497, 2, 27, 78, 26, 17, 2, 42, 66, 37, 18),
  (7498, 0, 45, 12, 73, 19, 2, 19, 80, 27, 17),
  (7499, 0, 23, 79, 27, 17, 0, 23, 83, 9, 15)
  ]

lemma witChunk_145_ok : witChunk_145.all checkWit = true := by
  decide +kernel

lemma witChunk_145_ns :
    witChunk_145.map (fun t => t.1) = (List.range 50).map (· + 7450) := by
  decide +kernel

def witChunk_146 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7500, 2, 6, 84, 20, 16, 3, 5, 76, 41, 18),
  (7501, 0, 21, 2, 84, 19, 0, 21, 66, 52, 19),
  (7502, 0, 50, 59, 39, 18, 0, 74, 1, 45, 16),
  (7503, 3, 77, 20, 34, 16, 5, 27, 82, 0, 14),
  (7504, 1, 10, 81, 29, 17, 1, 17, 83, 18, 16),
  (7505, 0, 33, 4, 80, 19, 0, 65, 56, 12, 15),
  (7506, 2, 19, 84, 9, 15, 2, 21, 1, 84, 19),
  (7507, 1, 7, 84, 20, 16, 1, 10, 3, 86, 19),
  (7508, 0, 60, 8, 62, 18, 1, 3, 84, 21, 16),
  (7509, 0, 28, 82, 1, 14, 0, 82, 1, 28, 14),
  (7510, 0, 7, 81, 30, 17, 0, 81, 30, 7, 13),
  (7511, 1, 46, 73, 8, 15, 1, 80, 22, 25, 15),
  (7512, 1, 21, 75, 38, 18, 3, 73, 46, 7, 14),
  (7513, 0, 4, 84, 21, 16, 2, 10, 86, 3, 14),
  (7514, 0, 39, 77, 8, 15, 0, 53, 68, 9, 15),
  (7515, 0, 67, 1, 55, 17, 2, 53, 27, 63, 19),
  (7516, 1, 31, 72, 37, 18, 1, 39, 68, 37, 18),
  (7517, 0, 5, 66, 56, 19, 0, 37, 78, 8, 15),
  (7518, 0, 17, 2, 85, 19, 0, 25, 2, 83, 19),
  (7519, 1, 18, 67, 52, 19, 1, 72, 22, 43, 17),
  (7520, 0, 8, 84, 20, 16, 0, 12, 76, 40, 18),
  (7521, 0, 8, 76, 41, 18, 0, 37, 74, 26, 17),
  (7522, 1, 56, 60, 28, 17, 1, 72, 20, 44, 17),
  (7523, 0, 11, 81, 29, 17, 0, 15, 67, 53, 19),
  (7524, 1, 15, 76, 39, 18, 1, 81, 31, 0, 12),
  (7525, 1, 61, 9, 61, 18, 1, 77, 15, 37, 16),
  (7526, 0, 11, 3, 86, 19, 0, 11, 67, 54, 19),
  (7527, 1, 30, 81, 8, 15, 1, 66, 55, 12, 15),
  (7528, 1, 2, 81, 31, 17, 1, 11, 86, 3, 14),
  (7529, 0, 46, 63, 38, 18, 0, 58, 49, 42, 18),
  (7530, 0, 35, 79, 8, 15, 0, 55, 61, 28, 17),
  (7531, 0, 3, 81, 31, 17, 0, 31, 3, 81, 19),
  (7532, 3, 17, 36, 77, 20, 3, 17, 40, 75, 20),
  (7533, 1, 57, 51, 41, 18, 3, 19, 35, 77, 20),
  (7534, 0, 33, 62, 51, 19, 2, 31, 2, 81, 19),
  (7535, 1, 24, 66, 51, 19, 1, 72, 18, 45, 17),
  (7536, 2, 38, 78, 0, 14, 3, 19, 41, 74, 20),
  (7537, 0, 18, 83, 18, 16, 0, 61, 54, 30, 17),
  (7538, 0, 29, 64, 51, 19, 0, 43, 75, 8, 15),
  (7539, 1, 20, 84, 9, 15, 2, 21, 67, 51, 19),
  (7540, 0, 0, 84, 22, 16, 1, 11, 84, 19, 16),
  (7541, 0, 33, 76, 26, 17, 0, 41, 72, 26, 17),
  (7542, 0, 49, 46, 55, 19, 0, 50, 71, 1, 14),
  (7543, 1, 14, 81, 28, 17, 1, 22, 1, 84, 19),
  (7544, 1, 23, 82, 17, 16, 1, 57, 63, 18, 16),
  (7545, 2, 36, 79, 0, 14, 2, 47, 12, 72, 19),
  (7546, 1, 12, 2, 86, 19, 1, 28, 78, 26, 17),
  (7547, 0, 35, 61, 51, 19, 1, 83, 16, 20, 14),
  (7548, 2, 42, 76, 0, 14, 3, 4, 67, 55, 19),
  (7549, 0, 12, 86, 3, 14, 0, 85, 18, 0, 11)
  ]

lemma witChunk_146_ok : witChunk_146.all checkWit = true := by
  decide +kernel

lemma witChunk_146_ns :
    witChunk_146.map (fun t => t.1) = (List.range 50).map (· + 7500) := by
  decide +kernel

def witChunk_147 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7550, 0, 15, 85, 10, 15, 0, 50, 69, 17, 16),
  (7551, 1, 3, 76, 42, 18, 1, 59, 48, 42, 18),
  (7552, 1, 6, 67, 55, 19, 1, 18, 1, 85, 19),
  (7553, 0, 16, 76, 39, 18, 0, 18, 85, 2, 14),
  (7554, 0, 19, 67, 52, 19, 0, 53, 32, 61, 19),
  (7555, 0, 27, 65, 51, 19, 0, 43, 9, 75, 19),
  (7556, 0, 4, 76, 42, 18, 0, 56, 64, 18, 16),
  (7557, 0, 49, 16, 70, 19, 1, 65, 27, 51, 18),
  (7558, 1, 4, 86, 12, 15, 1, 44, 54, 52, 19),
  (7559, 1, 64, 50, 31, 17, 3, 1, 76, 42, 18),
  (7560, 3, 13, 38, 77, 20, 5, 11, 42, 75, 20),
  (7561, 0, 12, 84, 19, 16, 0, 60, 60, 19, 16),
  (7562, 0, 47, 13, 72, 19, 0, 53, 28, 63, 19),
  (7563, 0, 7, 67, 55, 19, 0, 71, 11, 49, 17),
  (7564, 1, 41, 75, 16, 16, 2, 22, 36, 76, 20),
  (7565, 0, 5, 86, 12, 15, 0, 36, 70, 37, 18),
  (7566, 0, 1, 86, 13, 15, 0, 26, 83, 1, 14),
  (7567, 1, 0, 86, 13, 15, 1, 34, 3, 80, 19),
  (7568, 1, 26, 1, 83, 19, 1, 46, 11, 73, 19),
  (7569, 0, 13, 2, 86, 19, 0, 29, 2, 82, 19),
  (7570, 0, 15, 81, 28, 17, 0, 21, 80, 27, 17),
  (7571, 0, 59, 57, 29, 17, 0, 63, 59, 11, 15),
  (7572, 2, 18, 34, 78, 20, 2, 18, 42, 74, 20),
  (7573, 0, 72, 42, 25, 16, 1, 53, 69, 1, 14),
  (7574, 0, 38, 69, 37, 18, 0, 62, 61, 3, 14),
  (7575, 1, 56, 66, 9, 15, 1, 78, 33, 20, 15),
  (7576, 0, 76, 6, 42, 16, 0, 76, 30, 30, 16),
  (7577, 0, 32, 72, 37, 18, 0, 86, 9, 10, 12),
  (7578, 0, 21, 84, 9, 15, 0, 43, 55, 52, 19),
  (7579, 1, 12, 68, 53, 19, 1, 60, 56, 29, 17),
  (7580, 1, 63, 60, 3, 14, 1, 77, 25, 32, 16),
  (7581, 0, 53, 26, 64, 19, 0, 85, 10, 16, 13),
  (7582, 0, 25, 66, 51, 19, 2, 85, 5, 18, 13),
  (7583, 1, 8, 86, 11, 15, 1, 19, 38, 76, 20),
  (7584, 1, 65, 21, 54, 18, 2, 14, 36, 78, 20),
  (7585, 0, 85, 6, 18, 13, 2, 22, 42, 73, 20),
  (7586, 0, 23, 1, 84, 19, 0, 31, 81, 8, 15),
  (7587, 0, 19, 1, 85, 19, 2, 17, 81, 27, 17),
  (7588, 1, 17, 39, 76, 20, 1, 19, 36, 77, 20),
  (7589, 0, 24, 82, 17, 16, 0, 52, 58, 39, 18),
  (7590, 2, 45, 9, 74, 19, 2, 79, 30, 21, 15),
  (7591, 1, 32, 2, 81, 19, 1, 42, 7, 76, 19),
  (7592, 0, 48, 62, 38, 18, 3, 11, 37, 78, 20),
  (7593, 0, 40, 68, 37, 18, 0, 58, 65, 2, 14),
  (7594, 0, 85, 12, 15, 13, 2, 16, 33, 79, 20),
  (7595, 0, 55, 67, 9, 15, 0, 75, 41, 17, 15),
  (7596, 1, 63, 12, 59, 18, 1, 63, 40, 45, 18),
  (7597, 1, 1, 87, 5, 14, 1, 17, 41, 75, 20),
  (7598, 0, 2, 87, 5, 14, 0, 9, 86, 11, 15),
  (7599, 3, 13, 44, 74, 20, 3, 40, 59, 50, 19)
  ]

lemma witChunk_147_ok : witChunk_147.all checkWit = true := by
  decide +kernel

lemma witChunk_147_ns :
    witChunk_147.map (fun t => t.1) = (List.range 50).map (· + 7550) := by
  decide +kernel

def witChunk_148 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7600, 1, 2, 5, 87, 19, 1, 15, 38, 77, 20),
  (7601, 0, 29, 78, 26, 17, 0, 45, 10, 74, 19),
  (7602, 0, 13, 68, 53, 19, 0, 47, 73, 8, 15),
  (7603, 0, 3, 5, 87, 19, 0, 39, 59, 51, 19),
  (7604, 2, 14, 86, 2, 14, 2, 26, 38, 74, 20),
  (7605, 0, 52, 70, 1, 14, 0, 60, 6, 63, 18),
  (7606, 0, 1, 6, 87, 19, 0, 1, 66, 57, 19),
  (7607, 1, 0, 6, 87, 19, 1, 0, 66, 57, 19),
  (7608, 0, 68, 50, 22, 16, 1, 57, 1, 66, 18),
  (7609, 2, 4, 87, 4, 14, 2, 12, 41, 76, 20),
  (7610, 0, 5, 4, 87, 19, 0, 53, 24, 65, 19),
  (7611, 2, 5, 3, 87, 19, 2, 81, 9, 31, 15),
  (7612, 1, 5, 87, 4, 14, 1, 9, 77, 40, 18),
  (7613, 1, 65, 19, 55, 18, 1, 85, 19, 5, 12),
  (7614, 0, 81, 18, 27, 15, 2, 53, 21, 66, 19),
  (7615, 1, 48, 50, 53, 19, 1, 83, 20, 18, 14),
  (7616, 1, 6, 3, 87, 19, 1, 15, 42, 75, 20),
  (7617, 0, 17, 68, 52, 19, 0, 52, 68, 17, 16),
  (7618, 2, 12, 35, 79, 20, 2, 16, 45, 73, 20),
  (7619, 0, 23, 67, 51, 19, 0, 27, 1, 83, 19),
  (7620, 0, 20, 38, 76, 20, 0, 20, 76, 38, 18),
  (7621, 0, 6, 87, 4, 14, 0, 9, 68, 54, 19),
  (7622, 0, 15, 1, 86, 19, 0, 18, 37, 77, 20),
  (7623, 3, 25, 82, 16, 16, 3, 34, 80, 7, 15),
  (7624, 1, 13, 37, 78, 20, 1, 15, 34, 79, 20),
  (7625, 0, 0, 76, 43, 18, 0, 20, 36, 77, 20),
  (7626, 0, 37, 4, 79, 19, 0, 79, 37, 4, 13),
  (7627, 0, 7, 3, 87, 19, 0, 87, 3, 7, 11),
  (7628, 1, 13, 41, 76, 20, 1, 19, 32, 79, 20),
  (7629, 0, 10, 77, 40, 18, 0, 16, 38, 77, 20),
  (7630, 0, 18, 41, 75, 20, 0, 22, 39, 75, 20),
  (7631, 1, 2, 67, 56, 19, 1, 8, 82, 29, 17),
  (7632, 0, 16, 40, 76, 20, 0, 40, 76, 16, 16),
  (7633, 0, 18, 35, 78, 20, 0, 24, 84, 1, 14),
  (7634, 0, 3, 67, 56, 19, 0, 35, 3, 80, 19),
  (7635, 0, 71, 35, 37, 17, 2, 81, 21, 25, 15),
  (7636, 0, 16, 36, 78, 20, 0, 16, 84, 18, 16),
  (7637, 0, 81, 20, 26, 15, 1, 5, 77, 41, 18),
  (7638, 0, 22, 35, 77, 20, 0, 49, 14, 71, 19),
  (7639, 1, 8, 2, 87, 19, 1, 15, 44, 74, 20),
  (7640, 0, 20, 34, 78, 20, 0, 20, 42, 74, 20),
  (7641, 0, 22, 41, 74, 20, 0, 76, 4, 43, 16),
  (7642, 1, 4, 82, 30, 17, 1, 12, 86, 10, 15),
  (7643, 0, 79, 31, 21, 15, 0, 87, 7, 5, 11),
  (7644, 2, 34, 72, 36, 18, 2, 66, 24, 52, 18),
  (7645, 0, 16, 42, 75, 20, 0, 24, 38, 75, 20),
  (7646, 0, 6, 77, 41, 18, 0, 9, 82, 29, 17),
  (7647, 1, 51, 60, 38, 18, 5, 12, 82, 27, 17),
  (7648, 0, 24, 36, 76, 20, 1, 69, 49, 22, 16),
  (7649, 0, 5, 82, 30, 17, 0, 14, 37, 78, 20)
  ]

lemma witChunk_148_ok : witChunk_148.all checkWit = true := by
  decide +kernel

lemma witChunk_148_ns :
    witChunk_148.map (fun t => t.1) = (List.range 50).map (· + 7600) := by
  decide +kernel

def witChunk_149 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7650, 0, 85, 16, 13, 13, 2, 8, 87, 3, 14),
  (7651, 0, 19, 81, 27, 17, 0, 51, 17, 69, 19),
  (7652, 0, 24, 40, 74, 20, 0, 56, 54, 40, 18),
  (7653, 0, 14, 41, 76, 20, 0, 16, 34, 79, 20),
  (7654, 0, 9, 2, 87, 19, 0, 18, 33, 79, 20),
  (7655, 3, 9, 34, 80, 20, 3, 20, 81, 26, 17),
  (7656, 0, 16, 86, 2, 14, 0, 64, 14, 58, 18),
  (7657, 0, 22, 33, 78, 20, 0, 58, 63, 18, 16),
  (7658, 0, 53, 40, 57, 19, 0, 67, 55, 12, 15),
  (7659, 0, 47, 11, 73, 19, 2, 9, 1, 87, 19),
  (7660, 1, 11, 36, 79, 20, 1, 13, 33, 80, 20),
  (7661, 0, 6, 85, 20, 16, 0, 24, 34, 77, 20),
  (7662, 0, 14, 35, 79, 20, 0, 22, 43, 73, 20),
  (7663, 1, 11, 42, 76, 20, 1, 14, 69, 52, 19),
  (7664, 1, 17, 77, 38, 18, 1, 59, 50, 41, 18),
  (7665, 0, 13, 86, 10, 15, 0, 20, 32, 79, 20),
  (7666, 0, 21, 0, 85, 19, 0, 21, 68, 51, 19),
  (7667, 0, 19, 85, 9, 15, 1, 4, 68, 55, 19),
  (7668, 0, 16, 44, 74, 20, 0, 44, 74, 16, 16),
  (7669, 0, 24, 42, 73, 20, 0, 73, 24, 42, 17),
  (7670, 0, 2, 85, 21, 16, 0, 14, 43, 75, 20),
  (7671, 1, 63, 10, 60, 18, 1, 63, 42, 44, 18),
  (7672, 0, 12, 38, 78, 20, 1, 10, 1, 87, 19),
  (7673, 0, 12, 40, 77, 20, 0, 26, 39, 74, 20),
  (7674, 0, 5, 68, 55, 19, 0, 43, 7, 76, 19),
  (7675, 1, 28, 0, 83, 19, 1, 44, 56, 51, 19),
  (7676, 1, 23, 76, 37, 18, 1, 47, 64, 37, 18),
  (7677, 0, 13, 82, 28, 17, 0, 26, 35, 76, 20),
  (7678, 0, 10, 87, 3, 14, 0, 18, 45, 73, 20),
  (7679, 1, 11, 34, 80, 20, 1, 27, 42, 72, 20),
  (7680, 0, 16, 32, 80, 20, 0, 32, 80, 16, 16),
  (7681, 0, 12, 36, 79, 20, 0, 25, 0, 84, 19),
  (7682, 0, 27, 83, 8, 15, 0, 83, 27, 8, 13),
  (7683, 2, 81, 5, 33, 15, 2, 81, 33, 5, 13),
  (7684, 0, 12, 42, 76, 20, 0, 24, 32, 78, 20),
  (7685, 0, 14, 33, 80, 20, 0, 17, 0, 86, 19),
  (7686, 0, 1, 82, 31, 17, 0, 10, 85, 19, 16),
  (7687, 1, 0, 82, 31, 17, 1, 31, 82, 0, 14),
  (7688, 1, 9, 39, 78, 20, 1, 15, 30, 81, 20),
  (7689, 2, 30, 34, 75, 20, 2, 84, 7, 24, 14),
  (7690, 0, 15, 69, 52, 19, 2, 12, 47, 73, 20),
  (7691, 0, 11, 1, 87, 19, 0, 11, 69, 53, 19),
  (7692, 2, 14, 48, 72, 20, 2, 30, 40, 72, 20),
  (7693, 0, 22, 45, 72, 20, 0, 42, 77, 0, 14),
  (7694, 0, 26, 33, 77, 20, 0, 35, 63, 50, 19),
  (7695, 3, 13, 28, 82, 20, 3, 29, 44, 70, 20),
  (7696, 0, 24, 44, 72, 20, 0, 36, 80, 0, 14),
  (7697, 0, 2, 77, 42, 18, 0, 14, 45, 74, 20),
  (7698, 0, 53, 20, 67, 19, 0, 61, 56, 29, 17),
  (7699, 0, 43, 57, 51, 19, 0, 87, 11, 3, 11)
  ]

lemma witChunk_149_ok : witChunk_149.all checkWit = true := by
  decide +kernel

lemma witChunk_149_ns :
    witChunk_149.map (fun t => t.1) = (List.range 50).map (· + 7650) := by
  decide +kernel

def witChunk_150 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7700, 0, 12, 34, 80, 20, 0, 20, 30, 80, 20),
  (7701, 0, 16, 46, 73, 20, 0, 25, 80, 26, 17),
  (7702, 0, 78, 23, 33, 16, 1, 24, 68, 50, 19),
  (7703, 1, 40, 74, 25, 17, 3, 44, 57, 50, 19),
  (7704, 0, 28, 38, 74, 20, 3, 9, 78, 39, 18),
  (7705, 0, 10, 39, 78, 20, 0, 12, 44, 75, 20),
  (7706, 0, 51, 71, 8, 15, 0, 71, 37, 36, 17),
  (7707, 0, 55, 31, 61, 19, 1, 35, 72, 36, 18),
  (7708, 1, 9, 35, 80, 20, 1, 9, 43, 76, 20),
  (7709, 0, 26, 43, 72, 20, 0, 53, 42, 56, 19),
  (7710, 0, 10, 37, 79, 20, 0, 10, 41, 77, 20),
  (7711, 1, 16, 82, 27, 17, 1, 27, 82, 16, 16),
  (7712, 0, 44, 76, 0, 14, 0, 60, 4, 64, 18),
  (7713, 0, 28, 40, 73, 20, 0, 37, 62, 50, 19),
  (7714, 0, 45, 8, 75, 19, 0, 55, 33, 60, 19),
  (7715, 1, 6, 69, 54, 19, 1, 11, 46, 74, 20),
  (7716, 0, 28, 34, 76, 20, 0, 76, 2, 44, 16),
  (7717, 0, 16, 30, 81, 20, 0, 18, 47, 72, 20),
  (7718, 0, 14, 31, 81, 20, 0, 27, 67, 50, 19),
  (7719, 1, 2, 87, 12, 15, 1, 39, 70, 36, 18),
  (7720, 0, 72, 50, 6, 14, 1, 13, 85, 18, 16),
  (7721, 0, 24, 76, 37, 18, 0, 26, 31, 78, 20),
  (7722, 0, 3, 87, 12, 15, 0, 47, 53, 52, 19),
  (7723, 0, 19, 69, 51, 19, 0, 55, 27, 63, 19),
  (7724, 3, 4, 87, 11, 15, 3, 11, 49, 72, 20),
  (7725, 0, 10, 35, 80, 20, 0, 10, 43, 76, 20),
  (7726, 0, 7, 69, 54, 19, 0, 18, 29, 81, 20),
  (7727, 3, 5, 40, 78, 20, 3, 5, 78, 40, 18),
  (7728, 1, 6, 87, 11, 15, 1, 11, 78, 39, 18),
  (7729, 0, 12, 32, 81, 20, 0, 49, 12, 72, 19),
  (7730, 0, 29, 0, 83, 19, 0, 75, 43, 16, 15),
  (7731, 0, 55, 35, 59, 19, 1, 87, 4, 12, 12),
  (7732, 0, 28, 42, 72, 20, 1, 29, 83, 0, 14),
  (7733, 0, 24, 46, 71, 20, 0, 78, 25, 32, 16),
  (7734, 0, 14, 47, 73, 20, 0, 22, 47, 71, 20),
  (7735, 1, 7, 40, 78, 20, 1, 7, 78, 40, 18),
  (7736, 0, 12, 46, 74, 20, 0, 84, 26, 2, 12),
  (7737, 0, 28, 32, 77, 20, 0, 62, 7, 62, 18),
  (7738, 0, 13, 0, 87, 19, 1, 52, 46, 54, 19),
  (7739, 0, 7, 87, 11, 15, 1, 70, 41, 34, 17),
  (7740, 1, 41, 69, 36, 18, 2, 6, 36, 80, 20),
  (7741, 0, 46, 75, 0, 14, 0, 84, 18, 19, 14),
  (7742, 0, 17, 82, 27, 17, 0, 26, 45, 71, 20),
  (7743, 1, 54, 69, 8, 15, 1, 80, 30, 21, 15),
  (7744, 0, 16, 48, 72, 20, 0, 48, 72, 16, 16),
  (7745, 0, 14, 85, 18, 16, 0, 20, 28, 81, 20),
  (7746, 0, 55, 25, 64, 19, 0, 59, 59, 28, 17),
  (7747, 1, 7, 36, 80, 20, 1, 11, 30, 82, 20),
  (7748, 0, 8, 40, 78, 20, 0, 8, 78, 40, 18),
  (7749, 0, 8, 38, 79, 20, 0, 12, 78, 39, 18)
  ]

lemma witChunk_150_ok : witChunk_150.all checkWit = true := by
  decide +kernel

lemma witChunk_150_ns :
    witChunk_150.map (fun t => t.1) = (List.range 50).map (· + 7700) := by
  decide +kernel

def witChunk_151 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7750, 0, 10, 33, 81, 20, 0, 10, 45, 75, 20),
  (7751, 3, 8, 87, 10, 15, 3, 50, 72, 7, 15),
  (7752, 0, 88, 2, 2, 10, 1, 87, 10, 9, 12),
  (7753, 0, 88, 0, 3, 10, 2, 22, 50, 69, 20),
  (7754, 2, 32, 41, 71, 20, 2, 67, 56, 11, 15),
  (7755, 1, 15, 78, 38, 18, 3, 5, 44, 76, 20),
  (7756, 1, 11, 48, 73, 20, 1, 13, 49, 72, 20),
  (7757, 0, 8, 42, 77, 20, 0, 53, 18, 68, 19),
  (7758, 0, 26, 29, 79, 20, 0, 55, 37, 58, 19),
  (7759, 1, 2, 3, 88, 19, 1, 16, 70, 51, 19),
  (7760, 0, 8, 36, 80, 20, 0, 24, 28, 80, 20),
  (7761, 0, 1, 4, 88, 19, 0, 1, 68, 56, 19),
  (7762, 0, 3, 3, 88, 19, 0, 45, 56, 51, 19),
  (7763, 1, 7, 44, 76, 20, 1, 19, 26, 82, 20),
  (7764, 0, 16, 28, 82, 20, 0, 28, 82, 16, 16),
  (7765, 0, 30, 33, 76, 20, 0, 30, 41, 72, 20),
  (7766, 0, 17, 86, 9, 15, 0, 18, 49, 71, 20),
  (7767, 1, 87, 0, 14, 12, 3, 25, 50, 68, 20),
  (7768, 0, 12, 30, 82, 20, 0, 28, 30, 78, 20),
  (7769, 0, 0, 88, 5, 14, 0, 14, 87, 2, 14),
  (7770, 0, 37, 76, 25, 17, 0, 53, 44, 55, 19),
  (7771, 0, 39, 3, 79, 19, 0, 39, 75, 25, 17),
  (7772, 1, 25, 83, 16, 16, 1, 71, 52, 5, 14),
  (7773, 0, 5, 2, 88, 19, 0, 13, 70, 52, 19),
  (7774, 0, 22, 27, 81, 20, 0, 78, 27, 31, 16),
  (7775, 1, 8, 70, 53, 19, 1, 10, 83, 28, 17),
  (7776, 0, 4, 88, 4, 14, 0, 8, 44, 76, 20),
  (7777, 0, 12, 48, 73, 20, 0, 18, 27, 82, 20),
  (7778, 1, 72, 36, 36, 17, 2, 5, 1, 88, 19),
  (7779, 0, 7, 83, 29, 17, 0, 35, 77, 25, 17),
  (7780, 0, 24, 48, 70, 20, 0, 48, 74, 0, 14),
  (7781, 0, 4, 78, 41, 18, 0, 8, 34, 81, 20),
  (7782, 0, 22, 77, 37, 18, 0, 41, 74, 25, 17),
  (7783, 1, 6, 1, 88, 19, 1, 32, 66, 49, 19),
  (7784, 0, 16, 78, 38, 18, 1, 34, 65, 49, 19),
  (7785, 0, 10, 31, 82, 20, 0, 10, 47, 74, 20),
  (7786, 0, 69, 0, 55, 17, 0, 69, 44, 33, 17),
  (7787, 0, 35, 1, 81, 19, 0, 59, 65, 9, 15),
  (7788, 3, 55, 67, 16, 16, 3, 68, 55, 11, 15),
  (7789, 0, 30, 83, 0, 14, 0, 84, 2, 27, 14),
  (7790, 0, 9, 70, 53, 19, 0, 11, 87, 10, 15),
  (7791, 1, 83, 30, 0, 12, 3, 5, 32, 82, 20),
  (7792, 1, 2, 69, 55, 19, 1, 5, 41, 78, 20),
  (7793, 0, 56, 56, 39, 18, 2, 4, 37, 80, 20),
  (7794, 0, 7, 1, 88, 19, 0, 11, 83, 28, 17),
  (7795, 0, 3, 69, 55, 19, 0, 55, 39, 57, 19),
  (7796, 0, 32, 36, 74, 20, 0, 32, 74, 36, 18),
  (7797, 0, 16, 50, 71, 20, 0, 20, 86, 1, 14),
  (7798, 0, 3, 83, 30, 17, 0, 6, 39, 79, 20),
  (7799, 1, 7, 32, 82, 20, 1, 31, 44, 70, 20)
  ]

lemma witChunk_151_ok : witChunk_151.all checkWit = true := by
  decide +kernel

lemma witChunk_151_ns :
    witChunk_151.map (fun t => t.1) = (List.range 50).map (· + 7750) := by
  decide +kernel

def witChunk_152 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7800, 0, 20, 26, 82, 20, 0, 20, 50, 70, 20),
  (7801, 0, 6, 41, 78, 20, 0, 76, 0, 45, 16),
  (7802, 1, 20, 70, 50, 19, 1, 20, 82, 26, 17),
  (7803, 0, 43, 5, 77, 19, 0, 43, 73, 25, 17),
  (7804, 1, 7, 88, 3, 14, 1, 69, 55, 4, 14),
  (7805, 0, 6, 37, 80, 20, 0, 8, 46, 75, 20),
  (7806, 3, 74, 14, 46, 17, 3, 74, 46, 14, 15),
  (7807, 1, 3, 86, 20, 16, 1, 11, 50, 72, 20),
  (7808, 0, 32, 40, 72, 20, 1, 7, 86, 19, 16),
  (7809, 0, 28, 28, 79, 20, 0, 49, 52, 52, 19),
  (7810, 1, 8, 0, 88, 19, 1, 56, 24, 64, 19),
  (7811, 0, 39, 79, 7, 15, 0, 51, 13, 71, 19),
  (7812, 0, 4, 86, 20, 16, 0, 8, 32, 82, 20),
  (7813, 0, 24, 26, 81, 20, 0, 33, 0, 82, 19),
  (7814, 0, 6, 43, 77, 20, 0, 14, 27, 83, 20),
  (7815, 3, 1, 86, 20, 16, 3, 16, 71, 50, 19),
  (7816, 1, 14, 83, 27, 17, 1, 19, 78, 37, 18),
  (7817, 0, 8, 88, 3, 14, 0, 12, 28, 83, 20),
  (7818, 0, 23, 85, 8, 15, 0, 37, 80, 7, 15),
  (7819, 1, 52, 48, 53, 19, 1, 54, 65, 26, 17),
  (7820, 2, 22, 52, 68, 20, 2, 86, 20, 4, 12),
  (7821, 0, 8, 86, 19, 16, 0, 16, 26, 83, 20),
  (7822, 0, 6, 35, 81, 20, 0, 55, 21, 66, 19),
  (7823, 1, 48, 54, 51, 19, 1, 72, 6, 51, 17),
  (7824, 0, 32, 32, 76, 20, 2, 6, 48, 74, 20),
  (7825, 0, 9, 0, 88, 19, 0, 18, 51, 70, 20),
  (7826, 0, 53, 16, 69, 19, 1, 56, 68, 8, 15),
  (7827, 0, 31, 79, 25, 17, 0, 43, 77, 7, 15),
  (7828, 0, 12, 50, 72, 20, 1, 5, 45, 76, 20),
  (7829, 0, 32, 42, 71, 20, 0, 50, 73, 0, 14),
  (7830, 0, 10, 29, 83, 20, 0, 10, 49, 73, 20),
  (7831, 1, 7, 48, 74, 20, 1, 15, 52, 70, 20),
  (7832, 1, 39, 78, 15, 16, 1, 85, 11, 22, 14),
  (7833, 0, 22, 25, 82, 20, 2, 3, 70, 54, 19),
  (7834, 0, 45, 72, 25, 17, 0, 75, 47, 0, 13),
  (7835, 0, 35, 81, 7, 15, 0, 47, 55, 51, 19),
  (7836, 2, 14, 24, 84, 20, 2, 30, 48, 68, 20),
  (7837, 0, 0, 86, 21, 16, 0, 6, 45, 76, 20),
  (7838, 0, 14, 51, 71, 20, 0, 18, 25, 83, 20),
  (7839, 1, 59, 0, 66, 18, 3, 16, 83, 26, 17),
  (7840, 0, 28, 84, 0, 14, 0, 84, 0, 28, 14),
  (7841, 0, 5, 70, 54, 19, 0, 21, 70, 50, 19),
  (7842, 0, 55, 41, 56, 19, 2, 27, 84, 7, 15),
  (7843, 0, 15, 83, 27, 17, 1, 11, 86, 18, 16),
  (7844, 0, 8, 48, 74, 20, 1, 65, 41, 44, 18),
  (7845, 1, 9, 79, 39, 18, 2, 32, 27, 78, 20),
  (7846, 0, 22, 51, 69, 20, 0, 33, 66, 49, 19),
  (7847, 1, 10, 71, 52, 19, 1, 38, 1, 80, 19),
  (7848, 0, 0, 78, 42, 18, 1, 14, 87, 9, 15),
  (7849, 0, 6, 33, 82, 20, 0, 28, 48, 69, 20)
  ]

lemma witChunk_152_ok : witChunk_152.all checkWit = true := by
  decide +kernel

lemma witChunk_152_ns :
    witChunk_152.map (fun t => t.1) = (List.range 50).map (· + 7800) := by
  decide +kernel

def witChunk_153 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7850, 0, 45, 76, 7, 15, 0, 55, 69, 8, 15),
  (7851, 0, 31, 67, 49, 19, 0, 35, 65, 49, 19),
  (7852, 1, 3, 40, 79, 20, 1, 13, 25, 84, 20),
  (7853, 0, 8, 30, 83, 20, 0, 20, 78, 37, 18),
  (7854, 0, 34, 37, 73, 20, 0, 58, 67, 1, 14),
  (7855, 1, 3, 38, 80, 20, 1, 11, 26, 84, 20),
  (7856, 0, 28, 76, 36, 18, 0, 44, 68, 36, 18),
  (7857, 0, 4, 40, 79, 20, 0, 34, 35, 74, 20),
  (7858, 0, 87, 17, 0, 11, 2, 4, 47, 75, 20),
  (7859, 0, 67, 57, 11, 15, 0, 71, 3, 53, 17),
  (7860, 0, 4, 38, 80, 20, 0, 16, 52, 70, 20),
  (7861, 0, 34, 39, 72, 20, 1, 5, 47, 75, 20),
  (7862, 0, 10, 79, 39, 18, 0, 26, 25, 81, 20),
  (7863, 1, 47, 66, 36, 18, 1, 87, 16, 6, 12),
  (7864, 0, 4, 42, 78, 20, 0, 12, 86, 18, 16),
  (7865, 0, 20, 24, 83, 20, 0, 20, 52, 69, 20),
  (7866, 0, 11, 71, 52, 19, 0, 29, 68, 49, 19),
  (7867, 0, 15, 71, 51, 19, 1, 18, 71, 50, 19),
  (7868, 1, 3, 36, 81, 20, 1, 5, 79, 40, 18),
  (7869, 0, 61, 58, 28, 17, 2, 2, 36, 81, 20),
  (7870, 0, 6, 47, 75, 20, 0, 30, 27, 79, 20),
  (7871, 1, 11, 88, 2, 14, 1, 83, 28, 14, 14),
  (7872, 2, 18, 22, 84, 20, 2, 18, 54, 68, 20),
  (7873, 0, 4, 36, 81, 20, 0, 57, 32, 60, 19),
  (7874, 1, 56, 40, 56, 19, 2, 4, 31, 83, 20),
  (7875, 0, 15, 87, 9, 15, 0, 47, 71, 25, 17),
  (7876, 0, 12, 26, 84, 20, 0, 24, 24, 82, 20),
  (7877, 0, 6, 79, 40, 18, 0, 14, 25, 84, 20),
  (7878, 0, 34, 41, 71, 20, 0, 58, 65, 17, 16),
  (7879, 1, 24, 70, 49, 19, 1, 62, 57, 28, 17),
  (7880, 1, 7, 50, 73, 20, 1, 13, 53, 70, 20),
  (7881, 0, 4, 44, 77, 20, 0, 14, 79, 38, 18),
  (7882, 0, 85, 24, 9, 13, 2, 3, 88, 11, 15),
  (7883, 0, 47, 7, 75, 19, 0, 47, 75, 7, 15),
  (7884, 2, 6, 28, 84, 20, 2, 30, 24, 80, 20),
  (7885, 0, 10, 27, 84, 20, 0, 10, 51, 72, 20),
  (7886, 0, 6, 31, 83, 20, 0, 57, 34, 59, 19),
  (7887, 3, 2, 88, 11, 15, 3, 37, 32, 74, 20),
  (7888, 0, 16, 24, 84, 20, 0, 24, 84, 16, 16),
  (7889, 0, 1, 88, 12, 15, 0, 12, 52, 71, 20),
  (7890, 0, 5, 88, 11, 15, 1, 0, 88, 12, 15),
  (7891, 0, 27, 69, 49, 19, 0, 39, 63, 49, 19),
  (7892, 0, 12, 88, 2, 14, 0, 32, 28, 78, 20),
  (7893, 0, 8, 50, 73, 20, 0, 34, 31, 76, 20),
  (7894, 0, 18, 53, 69, 20, 0, 18, 87, 1, 14),
  (7895, 1, 63, 60, 18, 16, 3, 40, 79, 6, 15),
  (7896, 0, 4, 34, 82, 20, 0, 76, 38, 26, 16),
  (7897, 2, 7, 84, 28, 17, 2, 22, 54, 67, 20),
  (7898, 0, 61, 64, 9, 15, 0, 83, 15, 28, 15),
  (7899, 0, 7, 71, 53, 19, 0, 31, 83, 7, 15)
  ]

lemma witChunk_153_ok : witChunk_153.all checkWit = true := by
  decide +kernel

lemma witChunk_153_ns :
    witChunk_153.map (fun t => t.1) = (List.range 50).map (· + 7850) := by
  decide +kernel

def witChunk_154 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7900, 2, 50, 64, 36, 18, 2, 66, 40, 44, 18),
  (7901, 0, 21, 86, 8, 15, 0, 26, 51, 68, 20),
  (7902, 0, 19, 71, 50, 19, 0, 22, 23, 83, 20),
  (7903, 1, 3, 46, 76, 20, 1, 19, 22, 84, 20),
  (7904, 0, 8, 28, 84, 20, 0, 24, 52, 68, 20),
  (7905, 0, 14, 53, 70, 20, 0, 34, 43, 70, 20),
  (7906, 0, 51, 11, 72, 19, 0, 51, 51, 52, 19),
  (7907, 0, 83, 17, 27, 15, 0, 87, 7, 17, 13),
  (7908, 0, 4, 46, 76, 20, 0, 28, 50, 68, 20),
  (7909, 0, 18, 23, 84, 20, 0, 40, 78, 15, 16),
  (7910, 0, 38, 79, 15, 16, 0, 58, 55, 39, 18),
  (7911, 1, 23, 78, 36, 18, 3, 1, 46, 76, 20),
  (7912, 1, 15, 86, 17, 16, 1, 31, 82, 15, 16),
  (7913, 0, 6, 49, 74, 20, 0, 72, 52, 5, 14),
  (7914, 2, 3, 84, 29, 17, 2, 11, 72, 51, 19),
  (7915, 0, 27, 81, 25, 17, 0, 75, 21, 43, 17),
  (7916, 3, 19, 79, 36, 18, 3, 64, 61, 9, 15),
  (7917, 0, 22, 53, 68, 20, 0, 52, 62, 37, 18),
  (7918, 0, 42, 77, 15, 16, 0, 49, 54, 51, 19),
  (7919, 1, 46, 5, 76, 19, 1, 58, 67, 8, 15),
  (7920, 1, 59, 54, 39, 18, 1, 87, 18, 5, 12),
  (7921, 0, 9, 84, 28, 17, 0, 28, 24, 81, 20),
  (7922, 0, 5, 84, 29, 17, 0, 39, 1, 80, 19),
  (7923, 2, 57, 21, 65, 19, 3, 64, 55, 28, 17),
  (7924, 0, 36, 38, 72, 20, 1, 1, 39, 80, 20),
  (7925, 0, 2, 39, 80, 20, 0, 9, 88, 10, 15),
  (7926, 0, 1, 2, 89, 19, 0, 1, 70, 55, 19),
  (7927, 1, 0, 2, 89, 19, 1, 0, 70, 55, 19),
  (7928, 0, 36, 34, 74, 20, 1, 2, 1, 89, 19),
  (7929, 0, 4, 32, 83, 20, 0, 26, 23, 82, 20),
  (7930, 0, 37, 0, 81, 19, 2, 0, 41, 79, 20),
  (7931, 0, 3, 1, 89, 19, 0, 59, 61, 27, 17),
  (7932, 1, 39, 72, 35, 18, 2, 6, 52, 72, 20),
  (7933, 0, 6, 29, 84, 20, 0, 16, 54, 69, 20),
  (7934, 0, 2, 37, 81, 20, 0, 18, 79, 37, 18),
  (7935, 5, 35, 24, 78, 20, 5, 35, 48, 66, 20),
  (7936, 1, 1, 43, 78, 20, 1, 15, 22, 85, 20),
  (7937, 0, 2, 43, 78, 20, 0, 36, 40, 71, 20),
  (7938, 0, 55, 17, 68, 19, 2, 0, 37, 81, 20),
  (7939, 0, 75, 17, 45, 17, 0, 87, 3, 19, 13),
  (7940, 0, 20, 22, 84, 20, 0, 20, 54, 68, 20),
  (7941, 0, 2, 89, 4, 14, 0, 16, 86, 17, 16),
  (7942, 0, 34, 45, 69, 20, 0, 34, 81, 15, 16),
  (7943, 1, 88, 14, 1, 11, 3, 2, 0, 89, 19),
  (7944, 0, 56, 58, 38, 18, 0, 64, 62, 2, 14),
  (7945, 0, 4, 48, 75, 20, 0, 12, 24, 85, 20),
  (7946, 0, 5, 0, 89, 19, 0, 29, 84, 7, 15),
  (7947, 2, 81, 37, 3, 13, 3, 13, 56, 68, 20),
  (7948, 1, 89, 5, 0, 10, 2, 22, 20, 84, 20),
  (7949, 0, 24, 22, 83, 20, 0, 62, 3, 64, 18)
  ]

lemma witChunk_154_ok : witChunk_154.all checkWit = true := by
  decide +kernel

lemma witChunk_154_ns :
    witChunk_154.map (fun t => t.1) = (List.range 50).map (· + 7900) := by
  decide +kernel

def witChunk_155 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (7950, 0, 10, 25, 85, 20, 0, 10, 53, 71, 20),
  (7951, 1, 34, 67, 48, 19, 1, 38, 77, 24, 17),
  (7952, 0, 8, 52, 72, 20, 0, 32, 48, 68, 20),
  (7953, 0, 2, 35, 82, 20, 2, 30, 22, 81, 20),
  (7954, 0, 13, 72, 51, 19, 0, 13, 84, 27, 17),
  (7955, 0, 83, 21, 25, 15, 1, 52, 68, 25, 17),
  (7956, 0, 24, 78, 36, 18, 0, 48, 66, 36, 18),
  (7957, 0, 1, 84, 30, 17, 0, 54, 71, 0, 14),
  (7958, 0, 2, 45, 77, 20, 0, 47, 57, 50, 19),
  (7959, 1, 18, 87, 8, 15, 3, 17, 86, 16, 16),
  (7960, 0, 12, 54, 70, 20, 0, 36, 42, 70, 20),
  (7961, 2, 32, 23, 80, 20, 2, 67, 58, 10, 15),
  (7962, 0, 83, 7, 32, 15, 2, 0, 45, 77, 20),
  (7963, 0, 87, 15, 13, 13, 1, 2, 71, 54, 19),
  (7964, 1, 31, 76, 35, 18, 2, 14, 56, 68, 20),
  (7965, 0, 8, 26, 85, 20, 0, 16, 22, 85, 20),
  (7966, 0, 3, 71, 54, 19, 0, 6, 51, 73, 20),
  (7967, 1, 3, 30, 84, 20, 1, 11, 80, 38, 18),
  (7968, 2, 2, 30, 84, 20, 2, 30, 52, 66, 20),
  (7969, 0, 9, 72, 52, 19, 0, 34, 27, 78, 20),
  (7970, 0, 45, 4, 77, 19, 0, 87, 1, 20, 13),
  (7971, 0, 23, 71, 49, 19, 0, 43, 61, 49, 19),
  (7972, 0, 4, 30, 84, 20, 0, 24, 86, 0, 14),
  (7973, 0, 2, 87, 20, 16, 0, 17, 72, 50, 19),
  (7974, 0, 25, 82, 25, 17, 0, 26, 53, 67, 20),
  (7975, 1, 34, 79, 24, 17, 1, 38, 65, 48, 19),
  (7976, 0, 64, 6, 62, 18, 0, 64, 46, 42, 18),
  (7977, 0, 28, 52, 67, 20, 2, 0, 87, 20, 16),
  (7978, 2, 4, 27, 85, 20, 2, 25, 71, 48, 19),
  (7979, 0, 51, 73, 7, 15, 0, 71, 43, 33, 17),
  (7980, 1, 21, 79, 36, 18, 3, 59, 65, 16, 16),
  (7981, 0, 22, 21, 84, 20, 0, 24, 54, 67, 20),
  (7982, 0, 2, 33, 83, 20, 0, 14, 55, 69, 20),
  (7983, 3, 13, 20, 86, 20, 3, 29, 20, 82, 20),
  (7984, 1, 58, 37, 57, 19, 1, 71, 50, 21, 16),
  (7985, 0, 8, 80, 39, 18, 0, 57, 40, 56, 19),
  (7986, 2, 0, 33, 83, 20, 2, 29, 81, 24, 17),
  (7987, 0, 51, 69, 25, 17, 0, 75, 29, 39, 17),
  (7988, 0, 12, 80, 38, 18, 0, 80, 12, 38, 16),
  (7989, 0, 2, 47, 76, 20, 0, 34, 47, 68, 20),
  (7990, 0, 6, 27, 85, 20, 0, 18, 21, 85, 20),
  (7991, 1, 58, 23, 64, 19, 3, 12, 73, 50, 19),
  (7992, 0, 4, 50, 74, 20, 0, 28, 22, 82, 20),
  (7993, 0, 10, 87, 18, 16, 0, 36, 44, 69, 20),
  (7994, 0, 13, 88, 9, 15, 0, 19, 87, 8, 15),
  (7995, 1, 51, 64, 36, 18, 3, 1, 50, 74, 20),
  (7996, 1, 15, 80, 37, 18, 1, 55, 60, 37, 18),
  (7997, 0, 36, 74, 35, 18, 0, 38, 37, 72, 20),
  (7998, 0, 22, 55, 67, 20, 0, 38, 35, 73, 20),
  (7999, 1, 67, 12, 58, 18, 1, 72, 2, 53, 17)
  ]

lemma witChunk_155_ok : witChunk_155.all checkWit = true := by
  decide +kernel

lemma witChunk_155_ns :
    witChunk_155.map (fun t => t.1) = (List.range 50).map (· + 7950) := by
  decide +kernel

lemma a_ge_two_of_lt_8000_b0 {n : ℕ} (hn : 200 ≤ n) (hlt : n < 1200) : 2 ≤ a n := by
  have hdiv : (n - 200) / 50 < 20 := by omega
  interval_cases h : (n - 200) / 50
  · exact wit_mem_ge_two witChunk_0_ok
      (mem_of_map_add witChunk_0_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_1_ok
      (mem_of_map_add witChunk_1_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_2_ok
      (mem_of_map_add witChunk_2_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_3_ok
      (mem_of_map_add witChunk_3_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_4_ok
      (mem_of_map_add witChunk_4_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_5_ok
      (mem_of_map_add witChunk_5_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_6_ok
      (mem_of_map_add witChunk_6_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_7_ok
      (mem_of_map_add witChunk_7_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_8_ok
      (mem_of_map_add witChunk_8_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_9_ok
      (mem_of_map_add witChunk_9_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_10_ok
      (mem_of_map_add witChunk_10_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_11_ok
      (mem_of_map_add witChunk_11_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_12_ok
      (mem_of_map_add witChunk_12_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_13_ok
      (mem_of_map_add witChunk_13_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_14_ok
      (mem_of_map_add witChunk_14_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_15_ok
      (mem_of_map_add witChunk_15_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_16_ok
      (mem_of_map_add witChunk_16_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_17_ok
      (mem_of_map_add witChunk_17_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_18_ok
      (mem_of_map_add witChunk_18_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_19_ok
      (mem_of_map_add witChunk_19_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b20 {n : ℕ} (hn : 1200 ≤ n) (hlt : n < 2200) : 2 ≤ a n := by
  have hdiv : (n - 1200) / 50 < 20 := by omega
  interval_cases h : (n - 1200) / 50
  · exact wit_mem_ge_two witChunk_20_ok
      (mem_of_map_add witChunk_20_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_21_ok
      (mem_of_map_add witChunk_21_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_22_ok
      (mem_of_map_add witChunk_22_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_23_ok
      (mem_of_map_add witChunk_23_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_24_ok
      (mem_of_map_add witChunk_24_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_25_ok
      (mem_of_map_add witChunk_25_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_26_ok
      (mem_of_map_add witChunk_26_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_27_ok
      (mem_of_map_add witChunk_27_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_28_ok
      (mem_of_map_add witChunk_28_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_29_ok
      (mem_of_map_add witChunk_29_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_30_ok
      (mem_of_map_add witChunk_30_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_31_ok
      (mem_of_map_add witChunk_31_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_32_ok
      (mem_of_map_add witChunk_32_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_33_ok
      (mem_of_map_add witChunk_33_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_34_ok
      (mem_of_map_add witChunk_34_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_35_ok
      (mem_of_map_add witChunk_35_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_36_ok
      (mem_of_map_add witChunk_36_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_37_ok
      (mem_of_map_add witChunk_37_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_38_ok
      (mem_of_map_add witChunk_38_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_39_ok
      (mem_of_map_add witChunk_39_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b40 {n : ℕ} (hn : 2200 ≤ n) (hlt : n < 3200) : 2 ≤ a n := by
  have hdiv : (n - 2200) / 50 < 20 := by omega
  interval_cases h : (n - 2200) / 50
  · exact wit_mem_ge_two witChunk_40_ok
      (mem_of_map_add witChunk_40_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_41_ok
      (mem_of_map_add witChunk_41_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_42_ok
      (mem_of_map_add witChunk_42_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_43_ok
      (mem_of_map_add witChunk_43_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_44_ok
      (mem_of_map_add witChunk_44_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_45_ok
      (mem_of_map_add witChunk_45_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_46_ok
      (mem_of_map_add witChunk_46_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_47_ok
      (mem_of_map_add witChunk_47_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_48_ok
      (mem_of_map_add witChunk_48_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_49_ok
      (mem_of_map_add witChunk_49_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_50_ok
      (mem_of_map_add witChunk_50_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_51_ok
      (mem_of_map_add witChunk_51_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_52_ok
      (mem_of_map_add witChunk_52_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_53_ok
      (mem_of_map_add witChunk_53_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_54_ok
      (mem_of_map_add witChunk_54_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_55_ok
      (mem_of_map_add witChunk_55_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_56_ok
      (mem_of_map_add witChunk_56_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_57_ok
      (mem_of_map_add witChunk_57_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_58_ok
      (mem_of_map_add witChunk_58_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_59_ok
      (mem_of_map_add witChunk_59_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b60 {n : ℕ} (hn : 3200 ≤ n) (hlt : n < 4200) : 2 ≤ a n := by
  have hdiv : (n - 3200) / 50 < 20 := by omega
  interval_cases h : (n - 3200) / 50
  · exact wit_mem_ge_two witChunk_60_ok
      (mem_of_map_add witChunk_60_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_61_ok
      (mem_of_map_add witChunk_61_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_62_ok
      (mem_of_map_add witChunk_62_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_63_ok
      (mem_of_map_add witChunk_63_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_64_ok
      (mem_of_map_add witChunk_64_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_65_ok
      (mem_of_map_add witChunk_65_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_66_ok
      (mem_of_map_add witChunk_66_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_67_ok
      (mem_of_map_add witChunk_67_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_68_ok
      (mem_of_map_add witChunk_68_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_69_ok
      (mem_of_map_add witChunk_69_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_70_ok
      (mem_of_map_add witChunk_70_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_71_ok
      (mem_of_map_add witChunk_71_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_72_ok
      (mem_of_map_add witChunk_72_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_73_ok
      (mem_of_map_add witChunk_73_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_74_ok
      (mem_of_map_add witChunk_74_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_75_ok
      (mem_of_map_add witChunk_75_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_76_ok
      (mem_of_map_add witChunk_76_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_77_ok
      (mem_of_map_add witChunk_77_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_78_ok
      (mem_of_map_add witChunk_78_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_79_ok
      (mem_of_map_add witChunk_79_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b80 {n : ℕ} (hn : 4200 ≤ n) (hlt : n < 5200) : 2 ≤ a n := by
  have hdiv : (n - 4200) / 50 < 20 := by omega
  interval_cases h : (n - 4200) / 50
  · exact wit_mem_ge_two witChunk_80_ok
      (mem_of_map_add witChunk_80_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_81_ok
      (mem_of_map_add witChunk_81_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_82_ok
      (mem_of_map_add witChunk_82_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_83_ok
      (mem_of_map_add witChunk_83_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_84_ok
      (mem_of_map_add witChunk_84_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_85_ok
      (mem_of_map_add witChunk_85_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_86_ok
      (mem_of_map_add witChunk_86_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_87_ok
      (mem_of_map_add witChunk_87_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_88_ok
      (mem_of_map_add witChunk_88_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_89_ok
      (mem_of_map_add witChunk_89_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_90_ok
      (mem_of_map_add witChunk_90_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_91_ok
      (mem_of_map_add witChunk_91_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_92_ok
      (mem_of_map_add witChunk_92_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_93_ok
      (mem_of_map_add witChunk_93_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_94_ok
      (mem_of_map_add witChunk_94_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_95_ok
      (mem_of_map_add witChunk_95_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_96_ok
      (mem_of_map_add witChunk_96_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_97_ok
      (mem_of_map_add witChunk_97_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_98_ok
      (mem_of_map_add witChunk_98_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_99_ok
      (mem_of_map_add witChunk_99_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b100 {n : ℕ} (hn : 5200 ≤ n) (hlt : n < 6200) : 2 ≤ a n := by
  have hdiv : (n - 5200) / 50 < 20 := by omega
  interval_cases h : (n - 5200) / 50
  · exact wit_mem_ge_two witChunk_100_ok
      (mem_of_map_add witChunk_100_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_101_ok
      (mem_of_map_add witChunk_101_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_102_ok
      (mem_of_map_add witChunk_102_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_103_ok
      (mem_of_map_add witChunk_103_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_104_ok
      (mem_of_map_add witChunk_104_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_105_ok
      (mem_of_map_add witChunk_105_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_106_ok
      (mem_of_map_add witChunk_106_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_107_ok
      (mem_of_map_add witChunk_107_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_108_ok
      (mem_of_map_add witChunk_108_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_109_ok
      (mem_of_map_add witChunk_109_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_110_ok
      (mem_of_map_add witChunk_110_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_111_ok
      (mem_of_map_add witChunk_111_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_112_ok
      (mem_of_map_add witChunk_112_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_113_ok
      (mem_of_map_add witChunk_113_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_114_ok
      (mem_of_map_add witChunk_114_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_115_ok
      (mem_of_map_add witChunk_115_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_116_ok
      (mem_of_map_add witChunk_116_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_117_ok
      (mem_of_map_add witChunk_117_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_118_ok
      (mem_of_map_add witChunk_118_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_119_ok
      (mem_of_map_add witChunk_119_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b120 {n : ℕ} (hn : 6200 ≤ n) (hlt : n < 7200) : 2 ≤ a n := by
  have hdiv : (n - 6200) / 50 < 20 := by omega
  interval_cases h : (n - 6200) / 50
  · exact wit_mem_ge_two witChunk_120_ok
      (mem_of_map_add witChunk_120_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_121_ok
      (mem_of_map_add witChunk_121_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_122_ok
      (mem_of_map_add witChunk_122_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_123_ok
      (mem_of_map_add witChunk_123_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_124_ok
      (mem_of_map_add witChunk_124_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_125_ok
      (mem_of_map_add witChunk_125_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_126_ok
      (mem_of_map_add witChunk_126_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_127_ok
      (mem_of_map_add witChunk_127_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_128_ok
      (mem_of_map_add witChunk_128_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_129_ok
      (mem_of_map_add witChunk_129_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_130_ok
      (mem_of_map_add witChunk_130_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_131_ok
      (mem_of_map_add witChunk_131_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_132_ok
      (mem_of_map_add witChunk_132_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_133_ok
      (mem_of_map_add witChunk_133_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_134_ok
      (mem_of_map_add witChunk_134_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_135_ok
      (mem_of_map_add witChunk_135_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_136_ok
      (mem_of_map_add witChunk_136_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_137_ok
      (mem_of_map_add witChunk_137_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_138_ok
      (mem_of_map_add witChunk_138_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_139_ok
      (mem_of_map_add witChunk_139_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000_b140 {n : ℕ} (hn : 7200 ≤ n) (hlt : n < 8000) : 2 ≤ a n := by
  have hdiv : (n - 7200) / 50 < 16 := by omega
  interval_cases h : (n - 7200) / 50
  · exact wit_mem_ge_two witChunk_140_ok
      (mem_of_map_add witChunk_140_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_141_ok
      (mem_of_map_add witChunk_141_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_142_ok
      (mem_of_map_add witChunk_142_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_143_ok
      (mem_of_map_add witChunk_143_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_144_ok
      (mem_of_map_add witChunk_144_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_145_ok
      (mem_of_map_add witChunk_145_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_146_ok
      (mem_of_map_add witChunk_146_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_147_ok
      (mem_of_map_add witChunk_147_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_148_ok
      (mem_of_map_add witChunk_148_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_149_ok
      (mem_of_map_add witChunk_149_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_150_ok
      (mem_of_map_add witChunk_150_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_151_ok
      (mem_of_map_add witChunk_151_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_152_ok
      (mem_of_map_add witChunk_152_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_153_ok
      (mem_of_map_add witChunk_153_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_154_ok
      (mem_of_map_add witChunk_154_ns (by omega) (by omega))
  · exact wit_mem_ge_two witChunk_155_ok
      (mem_of_map_add witChunk_155_ns (by omega) (by omega))

lemma a_ge_two_of_lt_8000 {n : ℕ} (hn : 200 ≤ n) (hlt : n < 8000) : 2 ≤ a n := by
  if h0 : n < 1200 then
    exact a_ge_two_of_lt_8000_b0 hn h0
  else if h1 : n < 2200 then
    exact a_ge_two_of_lt_8000_b20 (by omega) h1
  else if h2 : n < 3200 then
    exact a_ge_two_of_lt_8000_b40 (by omega) h2
  else if h3 : n < 4200 then
    exact a_ge_two_of_lt_8000_b60 (by omega) h3
  else if h4 : n < 5200 then
    exact a_ge_two_of_lt_8000_b80 (by omega) h4
  else if h5 : n < 6200 then
    exact a_ge_two_of_lt_8000_b100 (by omega) h5
  else if h6 : n < 7200 then
    exact a_ge_two_of_lt_8000_b120 (by omega) h6
  else
    exact a_ge_two_of_lt_8000_b140 (by omega) hlt


def checkWit10 (n : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → Bool
  | (w1, x1, y1, z1, k1, w2, x2, y2, z2, k2) =>
      checkWit (n, w1, x1, y1, z1, k1, w2, x2, y2, z2, k2)

lemma checkWit10_ge_two {n : ℕ} {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (h : checkWit10 n t = true) : 2 ≤ a n := by
  rcases t with ⟨w1, x1, y1, z1, k1, w2, x2, y2, z2, k2⟩
  exact checkWit_ge_two (t := (n, w1, x1, y1, z1, k1, w2, x2, y2, z2, k2)) h

lemma getD_check_ge_two {lo : ℕ}
    {c : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hok : ∀ i : ℕ, i < c.length → checkWit10 (lo + i) (c.getD i default) = true)
    {n : ℕ} (h1 : lo ≤ n) (h2 : n < lo + c.length) : 2 ≤ a n := by
  have hi : n - lo < c.length := by omega
  have := hok (n - lo) hi
  have hn : lo + (n - lo) = n := by omega
  rw [hn] at this
  exact checkWit10_ge_two this

def witC_8000 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (25, 82, 5, 1, 11, 8, 88, 8, 8, 12),
  (62, 12, 13, 0, 10, 60, 28, 4, 1, 10),
  (61, 20, 12, 4, 11, 24, 75, 35, 0, 13),
  (41, 68, 4, 1, 11, 15, 85, 18, 2, 12),
  (5, 85, 27, 0, 12, 48, 56, 16, 2, 12),
  (63, 3, 3, 7, 10, 13, 85, 21, 1, 12),
  (6, 81, 37, 2, 13, 20, 79, 31, 2, 13),
  (17, 72, 34, 33, 17, 17, 72, 6, 47, 17),
  (63, 3, 5, 6, 10, 53, 45, 19, 2, 12),
  (12, 17, 86, 6, 15, 36, 13, 72, 8, 15),
  (59, 30, 12, 2, 11, 12, 79, 35, 16, 15),
  (13, 87, 2, 10, 12, 59, 29, 12, 8, 12),
  (63, 3, 1, 8, 10, 57, 17, 35, 0, 12),
  (62, 6, 8, 15, 12, 38, 63, 34, 0, 13),
  (62, 1, 17, 6, 11, 28, 79, 3, 14, 13),
  (61, 19, 4, 14, 12, 61, 2, 13, 20, 13),
  (62, 2, 18, 0, 10, 8, 88, 0, 12, 12),
  (62, 2, 6, 17, 12, 30, 75, 24, 4, 13),
  (62, 4, 5, 17, 12, 54, 41, 21, 8, 13),
  (60, 23, 17, 1, 11, 62, 9, 15, 5, 11),
  (58, 34, 6, 10, 12, 62, 6, 10, 14, 12),
  (63, 3, 7, 5, 10, 8, 88, 10, 7, 12),
  (41, 68, 6, 0, 11, 53, 48, 10, 0, 11),
  (45, 60, 18, 7, 13, 61, 10, 9, 20, 13),
  (57, 1, 39, 2, 12, 53, 46, 1, 17, 13),
  (14, 8, 87, 0, 14, 8, 72, 52, 3, 14),
  (61, 16, 18, 2, 11, 42, 67, 0, 3, 11),
  (6, 89, 3, 5, 11, 61, 0, 24, 3, 11),
  (62, 14, 12, 0, 10, 59, 15, 21, 20, 14),
  (58, 34, 8, 9, 12, 62, 6, 4, 17, 12),
  (6, 89, 1, 6, 11, 0, 89, 10, 3, 11),
  (17, 78, 37, 0, 13, 47, 56, 21, 6, 13),
  (12, 88, 0, 0, 10, 62, 18, 2, 4, 10),
  (12, 18, 85, 14, 16, 8, 76, 40, 23, 16),
  (6, 89, 5, 4, 11, 44, 63, 7, 12, 13),
  (13, 80, 36, 1, 13, 28, 79, 1, 15, 13),
  (59, 32, 5, 5, 11, 0, 88, 16, 6, 12),
  (62, 18, 4, 3, 10, 62, 18, 0, 5, 10),
  (3, 78, 44, 0, 13, 23, 82, 0, 16, 13),
  (57, 31, 24, 2, 12, 53, 47, 14, 4, 12),
  (25, 81, 15, 2, 12, 28, 80, 6, 6, 12),
  (10, 79, 40, 0, 13, 52, 49, 6, 14, 13),
  (52, 47, 19, 8, 13, 59, 14, 28, 10, 13),
  (11, 86, 18, 9, 13, 44, 63, 9, 11, 13),
  (63, 3, 9, 4, 10, 13, 65, 59, 0, 14),
  (6, 86, 24, 1, 12, 34, 74, 16, 1, 12),
  (60, 26, 7, 11, 12, 14, 81, 33, 2, 13),
  (23, 37, 74, 12, 16, 7, 76, 27, 38, 17),
  (54, 46, 6, 8, 12, 58, 34, 10, 8, 12),
  (62, 0, 19, 0, 10, 30, 79, 2, 2, 11)
  ]

lemma witC_8000_len : witC_8000.length = 50 := by decide +kernel

lemma witC_8000_all :
    (List.range 50).all (fun i => checkWit10 (8000 + i) (witC_8000.getD i default)) = true := by
  decide +kernel

lemma witC_8000_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8000 + i) (witC_8000.getD i default) = true := by
  intro i hi
  have h := witC_8000_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8050 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (62, 8, 3, 17, 12, 12, 79, 39, 0, 13),
  (6, 89, 7, 3, 11, 24, 83, 1, 3, 11),
  (62, 18, 6, 2, 10, 8, 88, 12, 6, 12),
  (14, 86, 16, 3, 12, 58, 34, 0, 13, 12),
  (24, 83, 3, 2, 11, 2, 89, 11, 2, 11),
  (29, 78, 15, 8, 13, 23, 81, 6, 20, 14),
  (49, 53, 11, 18, 14, 49, 37, 43, 6, 14),
  (58, 35, 10, 2, 11, 10, 88, 7, 8, 12),
  (1, 84, 18, 26, 15, 1, 84, 10, 30, 15),
  (59, 30, 14, 1, 11, 23, 82, 14, 9, 13),
  (61, 5, 23, 8, 12, 49, 53, 7, 20, 14),
  (54, 47, 2, 4, 11, 20, 84, 14, 3, 12),
  (4, 87, 19, 10, 13, 44, 63, 11, 10, 13),
  (61, 22, 11, 4, 11, 3, 12, 85, 26, 17),
  (62, 6, 14, 12, 12, 55, 41, 18, 3, 12),
  (62, 16, 11, 0, 10, 54, 39, 26, 6, 13),
  (62, 17, 5, 8, 11, 2, 88, 17, 5, 12),
  (24, 83, 5, 1, 11, 62, 17, 3, 9, 11),
  (11, 88, 9, 1, 11, 16, 84, 4, 22, 14),
  (1, 89, 5, 11, 12, 48, 56, 18, 1, 12),
  (32, 75, 19, 6, 13, 0, 67, 59, 10, 15),
  (1, 88, 10, 15, 13, 57, 31, 6, 24, 14),
  (63, 5, 10, 3, 10, 1, 89, 7, 10, 12),
  (28, 69, 40, 12, 15, 12, 58, 65, 14, 16),
  (62, 9, 17, 4, 11, 55, 42, 8, 14, 13),
  (55, 45, 0, 0, 10, 62, 17, 7, 7, 11),
  (1, 89, 3, 12, 12, 61, 21, 7, 12, 12),
  (61, 25, 1, 3, 10, 62, 18, 8, 1, 10),
  (6, 89, 9, 2, 11, 62, 17, 1, 10, 11),
  (3, 88, 11, 14, 13, 27, 76, 29, 2, 13),
  (61, 25, 3, 2, 10, 56, 32, 28, 0, 12),
  (10, 86, 22, 1, 12, 62, 10, 2, 17, 12),
  (60, 25, 16, 1, 11, 6, 65, 61, 8, 15),
  (61, 24, 4, 7, 11, 61, 8, 24, 1, 11),
  (30, 78, 14, 2, 12, 42, 66, 14, 2, 12),
  (8, 89, 0, 6, 11, 1, 89, 9, 9, 12),
  (61, 24, 2, 8, 11, 5, 88, 6, 16, 13),
  (45, 63, 2, 8, 12, 1, 86, 25, 8, 13),
  (61, 21, 3, 14, 12, 23, 75, 37, 6, 14),
  (20, 85, 8, 0, 11, 28, 24, 76, 13, 16),
  (24, 83, 7, 0, 11, 29, 80, 2, 2, 11),
  (29, 80, 0, 3, 11, 18, 85, 7, 13, 13),
  (63, 1, 12, 3, 10, 63, 9, 8, 3, 10),
  (61, 25, 5, 1, 10, 63, 11, 3, 5, 10),
  (62, 17, 9, 6, 11, 18, 85, 5, 14, 13),
  (13, 75, 46, 4, 14, 35, 13, 74, 0, 14),
  (63, 11, 1, 6, 10, 51, 51, 17, 2, 12),
  (42, 58, 34, 7, 14, 6, 86, 2, 25, 14),
  (4, 89, 12, 1, 11, 18, 85, 9, 12, 13),
  (29, 80, 4, 1, 11, 48, 59, 1, 3, 11)
  ]

lemma witC_8050_len : witC_8050.length = 50 := by decide +kernel

lemma witC_8050_all :
    (List.range 50).all (fun i => checkWit10 (8050 + i) (witC_8050.getD i default)) = true := by
  decide +kernel

lemma witC_8050_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8050 + i) (witC_8050.getD i default) = true := by
  intro i hi
  have h := witC_8050_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8100 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (63, 11, 5, 4, 10, 57, 9, 39, 0, 12),
  (25, 81, 17, 1, 12, 55, 39, 23, 1, 12),
  (13, 88, 2, 4, 11, 48, 59, 3, 2, 11),
  (63, 4, 7, 10, 11, 3, 89, 10, 8, 12),
  (61, 21, 11, 10, 12, 13, 86, 17, 9, 13),
  (44, 65, 2, 2, 11, 60, 29, 0, 8, 11),
  (63, 2, 8, 10, 11, 22, 84, 1, 9, 12),
  (13, 88, 4, 3, 11, 13, 88, 0, 5, 11),
  (1, 89, 11, 8, 12, 15, 87, 5, 8, 12),
  (15, 87, 3, 9, 12, 60, 20, 22, 5, 12),
  (60, 30, 3, 1, 10, 16, 87, 5, 2, 11),
  (59, 28, 13, 14, 13, 5, 76, 46, 13, 15),
  (62, 18, 10, 0, 10, 2, 90, 0, 2, 10),
  (26, 80, 19, 0, 12, 52, 48, 20, 1, 12),
  (44, 55, 31, 16, 15, 24, 3, 83, 8, 15),
  (6, 89, 11, 1, 11, 48, 59, 5, 1, 11),
  (61, 25, 7, 0, 10, 14, 86, 18, 2, 12),
  (63, 11, 7, 3, 10, 15, 87, 7, 7, 12),
  (29, 80, 6, 0, 11, 59, 30, 16, 0, 11),
  (63, 0, 9, 10, 11, 25, 79, 22, 12, 14),
  (63, 3, 13, 2, 10, 15, 87, 1, 10, 12),
  (44, 57, 26, 18, 15, 58, 15, 12, 32, 15),
  (13, 88, 6, 2, 11, 61, 0, 26, 2, 11),
  (62, 17, 11, 5, 11, 63, 2, 10, 9, 11),
  (49, 57, 3, 8, 12, 27, 79, 13, 16, 14),
  (49, 57, 5, 7, 12, 58, 10, 36, 1, 12),
  (26, 77, 29, 2, 13, 40, 46, 53, 1, 14),
  (23, 84, 3, 2, 11, 63, 8, 5, 10, 11),
  (62, 14, 10, 12, 12, 22, 82, 6, 20, 14),
  (38, 71, 2, 14, 13, 22, 4, 83, 16, 16),
  (0, 83, 35, 4, 13, 18, 85, 1, 16, 13),
  (19, 86, 2, 3, 11, 51, 54, 2, 3, 11),
  (45, 61, 19, 0, 12, 21, 65, 55, 0, 14),
  (35, 75, 3, 7, 12, 49, 57, 1, 9, 12),
  (4, 90, 1, 1, 10, 19, 86, 0, 4, 11),
  (3, 18, 88, 7, 15, 1, 62, 65, 8, 15),
  (15, 87, 9, 6, 12, 35, 75, 5, 6, 12),
  (38, 72, 1, 8, 12, 4, 76, 48, 5, 14),
  (19, 86, 4, 2, 11, 48, 59, 7, 0, 11),
  (62, 9, 19, 3, 11, 3, 86, 26, 7, 13),
  (35, 75, 1, 8, 12, 7, 75, 49, 4, 14),
  (1, 89, 13, 7, 12, 26, 82, 4, 7, 12),
  (18, 85, 13, 10, 13, 54, 25, 41, 2, 13),
  (53, 4, 50, 3, 13, 49, 48, 26, 19, 15),
  (63, 11, 9, 2, 10, 6, 86, 26, 0, 12),
  (12, 88, 8, 7, 12, 20, 0, 84, 17, 16),
  (56, 43, 3, 4, 11, 62, 1, 21, 4, 11),
  (13, 88, 8, 1, 11, 56, 43, 1, 5, 11),
  (26, 82, 6, 6, 12, 39, 71, 1, 8, 12),
  (35, 75, 7, 5, 12, 62, 14, 12, 11, 12)
  ]

lemma witC_8100_len : witC_8100.length = 50 := by decide +kernel

lemma witC_8100_all :
    (List.range 50).all (fun i => checkWit10 (8100 + i) (witC_8100.getD i default)) = true := by
  decide +kernel

lemma witC_8100_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8100 + i) (witC_8100.getD i default) = true := by
  intro i hi
  have h := witC_8100_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8150 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (63, 2, 12, 8, 11, 48, 58, 13, 3, 12),
  (1, 87, 24, 2, 12, 45, 31, 56, 2, 14),
  (63, 13, 6, 3, 10, 1, 85, 27, 14, 14),
  (52, 21, 48, 0, 13, 16, 78, 39, 6, 14),
  (45, 64, 2, 2, 11, 63, 10, 4, 10, 11),
  (19, 86, 6, 1, 11, 45, 64, 0, 3, 11),
  (3, 87, 13, 20, 14, 51, 39, 37, 8, 14),
  (26, 82, 0, 9, 12, 39, 71, 7, 5, 12),
  (40, 70, 3, 7, 12, 52, 39, 35, 2, 13),
  (3, 90, 4, 5, 11, 59, 34, 4, 5, 11),
  (0, 88, 20, 4, 12, 54, 46, 14, 4, 12),
  (10, 82, 34, 9, 14, 0, 49, 72, 24, 17),
  (6, 89, 13, 0, 11, 62, 17, 13, 4, 11),
  (45, 64, 4, 1, 11, 63, 10, 2, 11, 11),
  (16, 84, 20, 14, 14, 36, 72, 8, 18, 14),
  (15, 87, 11, 5, 12, 26, 82, 8, 5, 12),
  (63, 10, 8, 8, 11, 24, 82, 17, 1, 12),
  (1, 80, 42, 1, 13, 7, 65, 62, 0, 14),
  (53, 50, 7, 1, 11, 59, 19, 29, 2, 12),
  (62, 20, 9, 0, 10, 58, 36, 1, 12, 12),
  (22, 81, 25, 4, 13, 55, 42, 16, 10, 13),
  (61, 24, 12, 3, 11, 61, 23, 2, 14, 12),
  (25, 81, 19, 0, 12, 35, 75, 9, 4, 12),
  (6, 90, 0, 1, 10, 58, 38, 0, 1, 10),
  (56, 43, 7, 2, 11, 48, 51, 31, 2, 13),
  (35, 53, 54, 0, 14, 15, 13, 80, 34, 18),
  (6, 90, 2, 0, 10, 58, 38, 2, 0, 10),
  (22, 83, 16, 8, 13, 32, 77, 10, 10, 13),
  (36, 71, 23, 4, 13, 60, 25, 8, 17, 13),
  (55, 45, 2, 10, 12, 10, 85, 27, 5, 13),
  (21, 85, 3, 8, 12, 39, 71, 9, 4, 12),
  (63, 11, 11, 1, 10, 20, 84, 18, 1, 12),
  (13, 88, 10, 0, 11, 19, 86, 8, 0, 11),
  (37, 70, 23, 4, 13, 45, 23, 60, 2, 14),
  (1, 89, 15, 6, 12, 27, 79, 17, 14, 14),
  (52, 29, 44, 0, 13, 44, 61, 24, 4, 13),
  (6, 88, 19, 3, 12, 21, 80, 30, 2, 13),
  (63, 10, 10, 7, 11, 63, 2, 14, 7, 11),
  (49, 57, 11, 4, 12, 3, 87, 5, 24, 14),
  (9, 89, 5, 9, 12, 14, 86, 20, 1, 12),
  (50, 45, 29, 18, 15, 50, 7, 54, 15, 15),
  (5, 90, 5, 4, 11, 63, 12, 3, 10, 11),
  (9, 89, 3, 10, 12, 21, 85, 7, 6, 12),
  (56, 42, 11, 6, 12, 44, 54, 37, 6, 14),
  (4, 87, 23, 8, 13, 32, 59, 51, 8, 15),
  (55, 2, 46, 5, 13, 31, 72, 33, 0, 13),
  (9, 89, 7, 8, 12, 55, 39, 25, 0, 12),
  (63, 15, 5, 3, 10, 7, 87, 23, 1, 12),
  (49, 52, 26, 4, 13, 2, 85, 17, 26, 15),
  (7, 89, 12, 6, 12, 27, 66, 48, 9, 15)
  ]

lemma witC_8150_len : witC_8150.length = 50 := by decide +kernel

lemma witC_8150_all :
    (List.range 50).all (fun i => checkWit10 (8150 + i) (witC_8150.getD i default)) = true := by
  decide +kernel

lemma witC_8150_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8150 + i) (witC_8150.getD i default) = true := by
  intro i hi
  have h := witC_8150_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8200 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (3, 87, 17, 18, 14, 11, 79, 41, 6, 14),
  (52, 13, 32, 40, 17, 2, 10, 82, 37, 18),
  (15, 82, 32, 2, 13, 38, 65, 33, 0, 13),
  (56, 43, 9, 1, 11, 62, 21, 5, 7, 11),
  (15, 87, 13, 4, 12, 18, 86, 12, 4, 12),
  (8, 88, 18, 3, 12, 9, 89, 1, 11, 12),
  (60, 31, 3, 6, 11, 28, 79, 19, 6, 13),
  (51, 5, 48, 26, 16, 3, 8, 75, 50, 19),
  (56, 44, 0, 0, 10, 30, 78, 18, 0, 12),
  (26, 66, 50, 1, 14, 40, 48, 52, 1, 14),
  (6, 84, 31, 11, 14, 14, 80, 37, 7, 14),
  (60, 31, 5, 5, 11, 60, 31, 1, 7, 11),
  (52, 52, 8, 6, 12, 52, 52, 0, 10, 12),
  (9, 89, 9, 7, 12, 21, 85, 9, 5, 12),
  (62, 9, 21, 2, 11, 5, 80, 42, 0, 13),
  (61, 26, 9, 4, 11, 59, 33, 10, 8, 12),
  (57, 38, 7, 15, 13, 35, 71, 25, 10, 14),
  (36, 70, 25, 10, 14, 18, 19, 82, 22, 17),
  (61, 24, 14, 2, 11, 63, 10, 12, 6, 11),
  (58, 37, 11, 1, 11, 37, 74, 1, 2, 11),
  (39, 59, 41, 4, 14, 15, 67, 55, 16, 16),
  (31, 79, 3, 7, 12, 61, 21, 17, 7, 12),
  (38, 73, 1, 2, 11, 14, 73, 49, 10, 15),
  (9, 88, 14, 11, 13, 9, 34, 83, 4, 15),
  (31, 79, 5, 6, 12, 58, 34, 18, 4, 12),
  (30, 35, 72, 4, 15, 22, 67, 52, 8, 15),
  (60, 31, 7, 4, 11, 18, 85, 17, 8, 13),
  (7, 90, 2, 5, 11, 38, 73, 3, 1, 11),
  (60, 32, 0, 2, 10, 63, 11, 13, 0, 10),
  (60, 32, 2, 1, 10, 12, 89, 2, 4, 11),
  (7, 90, 4, 4, 11, 1, 84, 34, 4, 13),
  (9, 87, 10, 20, 14, 51, 17, 52, 6, 14),
  (61, 5, 27, 6, 12, 53, 2, 51, 3, 13),
  (4, 1, 90, 10, 15, 26, 11, 82, 6, 15),
  (7, 90, 0, 6, 11, 63, 2, 16, 6, 11),
  (17, 84, 24, 5, 13, 24, 83, 5, 13, 13),
  (63, 3, 17, 0, 10, 62, 22, 8, 0, 10),
  (0, 88, 22, 3, 12, 1, 89, 17, 5, 12),
  (60, 29, 14, 1, 11, 63, 14, 2, 10, 11),
  (61, 12, 22, 13, 13, 41, 67, 8, 18, 14),
  (60, 32, 4, 0, 10, 9, 89, 11, 6, 12),
  (36, 74, 13, 2, 12, 56, 41, 12, 12, 13),
  (38, 73, 5, 0, 11, 56, 43, 11, 0, 11),
  (7, 90, 6, 3, 11, 24, 83, 9, 11, 13),
  (2, 90, 6, 10, 12, 21, 85, 11, 4, 12),
  (2, 90, 4, 11, 12, 43, 67, 3, 7, 12),
  (34, 77, 1, 2, 11, 60, 30, 5, 11, 12),
  (57, 34, 23, 8, 13, 41, 48, 50, 9, 15),
  (35, 75, 13, 2, 12, 43, 67, 5, 6, 12),
  (56, 34, 25, 14, 14, 60, 18, 7, 26, 14)
  ]

lemma witC_8200_len : witC_8200.length = 50 := by decide +kernel

lemma witC_8200_all :
    (List.range 50).all (fun i => checkWit10 (8200 + i) (witC_8200.getD i default)) = true := by
  decide +kernel

lemma witC_8200_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8200 + i) (witC_8200.getD i default) = true := by
  intro i hi
  have h := witC_8200_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8250 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (54, 49, 1, 4, 11, 11, 86, 24, 6, 13),
  (34, 77, 3, 1, 11, 54, 49, 3, 3, 11),
  (63, 17, 4, 3, 10, 43, 67, 1, 8, 12),
  (2, 90, 8, 9, 12, 15, 87, 15, 3, 12),
  (18, 87, 6, 1, 11, 60, 15, 27, 10, 13),
  (25, 83, 10, 4, 12, 19, 84, 21, 6, 13),
  (2, 90, 2, 12, 12, 20, 84, 20, 0, 12),
  (64, 2, 5, 6, 10, 18, 78, 30, 25, 16),
  (58, 29, 25, 8, 13, 56, 11, 43, 4, 13),
  (63, 10, 14, 5, 11, 33, 76, 16, 7, 13),
  (64, 4, 4, 6, 10, 31, 79, 9, 4, 12),
  (64, 4, 2, 7, 10, 43, 67, 7, 5, 12),
  (54, 49, 5, 2, 11, 4, 90, 3, 11, 12),
  (51, 33, 44, 6, 14, 27, 73, 30, 24, 16),
  (64, 0, 6, 6, 10, 63, 7, 9, 14, 12),
  (20, 81, 30, 2, 13, 60, 17, 26, 10, 13),
  (7, 90, 8, 2, 11, 34, 77, 5, 0, 11),
  (0, 83, 37, 3, 13, 6, 89, 7, 15, 13),
  (63, 7, 5, 16, 12, 11, 84, 31, 3, 13),
  (64, 4, 6, 5, 10, 17, 85, 5, 21, 14),
  (62, 17, 17, 2, 11, 0, 90, 1, 13, 12),
  (51, 37, 32, 26, 16, 3, 64, 59, 26, 17),
  (64, 4, 0, 8, 10, 2, 90, 10, 8, 12),
  (64, 6, 3, 6, 10, 42, 32, 61, 0, 14),
  (30, 80, 7, 5, 12, 58, 36, 15, 5, 12),
  (61, 24, 16, 1, 11, 4, 87, 25, 7, 13),
  (8, 88, 20, 2, 12, 26, 82, 14, 2, 12),
  (2, 90, 0, 13, 12, 9, 89, 13, 5, 12),
  (55, 42, 20, 8, 13, 62, 9, 5, 22, 13),
  (43, 66, 0, 15, 13, 7, 9, 90, 0, 14),
  (49, 57, 15, 2, 12, 61, 21, 19, 6, 12),
  (52, 13, 52, 0, 13, 20, 85, 0, 16, 13),
  (62, 23, 4, 7, 11, 10, 85, 29, 4, 13),
  (54, 49, 7, 1, 11, 6, 89, 11, 13, 13),
  (43, 67, 9, 4, 12, 11, 89, 0, 11, 12),
  (21, 85, 13, 3, 12, 57, 41, 5, 9, 12),
  (60, 31, 11, 2, 11, 50, 53, 21, 6, 13),
  (41, 70, 5, 0, 11, 21, 3, 86, 0, 14),
  (64, 4, 8, 4, 10, 21, 86, 1, 3, 11),
  (30, 43, 68, 4, 15, 48, 49, 32, 16, 15),
  (62, 1, 5, 24, 13, 10, 85, 17, 24, 15),
  (63, 2, 18, 5, 11, 6, 89, 3, 17, 13),
  (59, 36, 3, 5, 11, 7, 87, 25, 0, 12),
  (31, 79, 11, 3, 12, 58, 34, 20, 3, 12),
  (42, 69, 1, 2, 11, 48, 59, 3, 14, 13),
  (63, 16, 1, 10, 11, 5, 87, 26, 0, 12),
  (64, 8, 2, 6, 10, 61, 18, 19, 13, 13),
  (54, 44, 23, 0, 12, 42, 55, 40, 12, 15),
  (38, 72, 15, 1, 12, 10, 77, 45, 12, 15),
  (7, 90, 10, 1, 11, 42, 69, 3, 1, 11)
  ]

lemma witC_8250_len : witC_8250.length = 50 := by decide +kernel

lemma witC_8250_all :
    (List.range 50).all (fun i => checkWit10 (8250 + i) (witC_8250.getD i default)) = true := by
  decide +kernel

lemma witC_8250_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8250 + i) (witC_8250.getD i default) = true := by
  intro i hi
  have h := witC_8250_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8300 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (1, 89, 19, 4, 12, 63, 7, 13, 12, 12),
  (2, 90, 12, 7, 12, 35, 75, 15, 1, 12),
  (44, 66, 7, 5, 12, 58, 13, 37, 6, 13),
  (7, 86, 28, 5, 13, 55, 20, 43, 2, 13),
  (58, 26, 30, 0, 12, 59, 21, 30, 1, 12),
  (42, 36, 59, 0, 14, 60, 4, 0, 33, 14),
  (61, 28, 8, 4, 11, 6, 89, 13, 12, 13),
  (21, 80, 32, 1, 13, 29, 80, 12, 9, 13),
  (8, 84, 32, 10, 14, 7, 67, 61, 0, 14),
  (39, 71, 15, 1, 12, 57, 41, 9, 7, 12),
  (63, 10, 16, 4, 11, 48, 59, 11, 10, 13),
  (11, 88, 15, 10, 13, 31, 78, 16, 7, 13),
  (15, 87, 17, 2, 12, 59, 35, 5, 10, 12),
  (62, 24, 7, 0, 10, 42, 52, 41, 20, 16),
  (25, 84, 2, 2, 11, 42, 69, 5, 0, 11),
  (25, 84, 0, 3, 11, 9, 90, 7, 2, 11),
  (63, 19, 1, 4, 10, 57, 33, 27, 0, 12),
  (63, 19, 3, 3, 10, 64, 4, 10, 3, 10),
  (62, 1, 25, 2, 11, 6, 89, 1, 18, 13),
  (23, 77, 36, 6, 14, 41, 59, 30, 24, 16),
  (59, 27, 25, 2, 12, 4, 88, 12, 20, 14),
  (0, 89, 16, 12, 13, 48, 53, 30, 2, 13),
  (56, 45, 4, 3, 11, 14, 81, 37, 0, 13),
  (25, 84, 4, 1, 11, 13, 88, 4, 15, 13),
  (0, 88, 24, 2, 12, 9, 89, 15, 4, 12),
  (11, 87, 15, 17, 14, 51, 7, 55, 7, 14),
  (0, 91, 3, 6, 11, 13, 88, 10, 12, 13),
  (3, 8, 87, 26, 17, 21, 62, 55, 24, 17),
  (63, 19, 5, 2, 10, 5, 87, 22, 15, 14),
  (64, 10, 1, 6, 10, 14, 4, 89, 0, 14),
  (14, 89, 1, 4, 11, 19, 86, 4, 14, 13),
  (0, 91, 5, 5, 11, 0, 91, 1, 7, 11),
  (59, 35, 9, 8, 12, 59, 35, 1, 12, 12),
  (26, 82, 16, 1, 12, 46, 62, 16, 1, 12),
  (8, 90, 5, 9, 12, 0, 27, 87, 6, 15),
  (25, 80, 26, 3, 13, 55, 16, 45, 2, 13),
  (16, 88, 4, 8, 12, 21, 85, 15, 2, 12),
  (38, 18, 70, 15, 16, 24, 74, 35, 22, 16),
  (2, 85, 33, 4, 13, 42, 61, 33, 0, 13),
  (62, 17, 19, 1, 11, 63, 1, 0, 20, 12),
  (2, 90, 14, 6, 12, 59, 9, 36, 1, 12),
  (16, 88, 6, 7, 12, 16, 88, 2, 9, 12),
  (7, 90, 12, 0, 11, 14, 89, 5, 2, 11),
  (9, 16, 86, 23, 17, 33, 8, 74, 25, 17),
  (59, 3, 37, 2, 12, 56, 44, 10, 6, 12),
  (50, 55, 16, 8, 13, 52, 25, 46, 14, 15),
  (0, 91, 7, 4, 11, 41, 68, 18, 6, 13),
  (63, 18, 6, 7, 11, 63, 18, 2, 9, 11),
  (55, 47, 5, 8, 12, 57, 1, 43, 0, 12),
  (63, 19, 7, 1, 10, 54, 46, 20, 1, 12)
  ]

lemma witC_8300_len : witC_8300.length = 50 := by decide +kernel

lemma witC_8300_all :
    (List.range 50).all (fun i => checkWit10 (8300 + i) (witC_8300.getD i default)) = true := by
  decide +kernel

lemma witC_8300_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8300 + i) (witC_8300.getD i default) = true := by
  intro i hi
  have h := witC_8300_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8350 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (64, 3, 7, 10, 11, 18, 85, 21, 6, 13),
  (51, 56, 3, 2, 11, 35, 74, 20, 5, 13),
  (62, 22, 6, 12, 12, 53, 42, 31, 3, 13),
  (28, 82, 5, 6, 12, 62, 3, 20, 16, 13),
  (64, 3, 3, 12, 11, 28, 79, 23, 4, 13),
  (49, 59, 6, 6, 12, 62, 9, 19, 15, 13),
  (64, 4, 12, 2, 10, 16, 88, 8, 6, 12),
  (8, 88, 22, 1, 12, 55, 47, 7, 7, 12),
  (60, 34, 1, 1, 10, 63, 2, 20, 4, 11),
  (53, 52, 6, 1, 11, 29, 76, 30, 1, 13),
  (43, 67, 13, 2, 12, 55, 47, 1, 10, 12),
  (0, 90, 15, 6, 12, 48, 60, 12, 3, 12),
  (63, 18, 8, 6, 11, 63, 18, 0, 10, 11),
  (14, 89, 7, 1, 11, 64, 3, 9, 9, 11),
  (35, 75, 17, 0, 12, 17, 69, 55, 0, 14),
  (64, 12, 2, 5, 10, 48, 61, 6, 0, 11),
  (30, 81, 1, 2, 11, 44, 67, 1, 2, 11),
  (61, 27, 0, 14, 12, 25, 32, 78, 3, 15),
  (64, 12, 4, 4, 10, 4, 88, 4, 24, 14),
  (30, 44, 67, 12, 16, 34, 70, 14, 31, 16),
  (26, 77, 33, 0, 13, 54, 41, 29, 4, 13),
  (0, 91, 9, 3, 11, 30, 81, 3, 1, 11),
  (62, 26, 2, 2, 10, 64, 12, 0, 6, 10),
  (62, 26, 0, 3, 10, 1, 89, 21, 3, 12),
  (62, 25, 5, 6, 11, 20, 86, 13, 3, 12),
  (11, 89, 14, 4, 12, 45, 15, 64, 2, 14),
  (55, 47, 9, 6, 12, 63, 7, 17, 10, 12),
  (4, 89, 18, 10, 13, 52, 37, 40, 0, 13),
  (62, 25, 1, 8, 11, 9, 84, 34, 2, 13),
  (20, 87, 1, 3, 11, 53, 51, 12, 4, 12),
  (7, 91, 1, 0, 10, 63, 19, 9, 0, 10),
  (62, 26, 4, 1, 10, 64, 12, 6, 3, 10),
  (20, 87, 3, 2, 11, 6, 89, 17, 10, 13),
  (63, 6, 20, 3, 11, 9, 51, 74, 12, 16),
  (63, 15, 5, 14, 12, 17, 86, 19, 7, 13),
  (62, 11, 24, 0, 11, 0, 80, 44, 7, 14),
  (30, 81, 5, 0, 11, 60, 31, 15, 0, 11),
  (62, 25, 7, 5, 11, 63, 18, 10, 5, 11),
  (60, 20, 28, 2, 12, 63, 15, 9, 12, 12),
  (2, 90, 16, 5, 12, 31, 79, 15, 1, 12),
  (3, 86, 20, 24, 15, 2, 85, 1, 34, 15),
  (1, 66, 63, 8, 15, 19, 8, 87, 6, 15),
  (63, 21, 2, 3, 10, 59, 35, 13, 6, 12),
  (2, 91, 10, 2, 11, 58, 38, 14, 5, 12),
  (14, 89, 9, 0, 11, 62, 9, 25, 0, 11),
  (20, 87, 5, 1, 11, 10, 85, 31, 3, 13),
  (33, 77, 17, 0, 12, 35, 71, 29, 8, 14),
  (62, 15, 22, 0, 11, 10, 90, 4, 9, 12),
  (38, 73, 9, 10, 13, 46, 59, 26, 3, 13),
  (63, 14, 16, 3, 11, 59, 5, 34, 16, 14)
  ]

lemma witC_8350_len : witC_8350.length = 50 := by decide +kernel

lemma witC_8350_all :
    (List.range 50).all (fun i => checkWit10 (8350 + i) (witC_8350.getD i default)) = true := by
  decide +kernel

lemma witC_8350_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8350 + i) (witC_8350.getD i default) = true := by
  intro i hi
  have h := witC_8350_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8400 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (62, 26, 6, 0, 10, 10, 90, 6, 8, 12),
  (38, 67, 32, 0, 13, 46, 63, 10, 10, 13),
  (62, 17, 13, 16, 13, 62, 17, 5, 20, 13),
  (35, 57, 52, 0, 14, 27, 73, 40, 4, 14),
  (64, 12, 8, 2, 10, 63, 4, 21, 3, 11),
  (64, 4, 14, 1, 10, 27, 83, 3, 7, 12),
  (0, 91, 11, 2, 11, 32, 75, 27, 2, 13),
  (11, 90, 8, 1, 11, 61, 30, 7, 4, 11),
  (27, 83, 5, 6, 12, 1, 82, 41, 1, 13),
  (60, 25, 22, 10, 13, 50, 51, 18, 22, 15),
  (49, 60, 2, 2, 11, 62, 25, 9, 4, 11),
  (49, 60, 0, 3, 11, 34, 77, 7, 11, 13),
  (27, 83, 1, 8, 12, 49, 57, 19, 0, 12),
  (62, 7, 26, 0, 11, 10, 90, 8, 7, 12),
  (0, 83, 39, 2, 13, 38, 73, 1, 14, 13),
  (9, 86, 29, 4, 13, 47, 60, 19, 6, 13),
  (16, 88, 12, 4, 12, 29, 81, 13, 2, 12),
  (54, 50, 6, 7, 12, 42, 20, 67, 0, 14),
  (20, 87, 7, 0, 11, 62, 17, 21, 0, 11),
  (49, 60, 4, 1, 11, 64, 11, 5, 9, 11),
  (36, 76, 4, 6, 12, 57, 41, 15, 4, 12),
  (0, 88, 26, 1, 12, 10, 90, 0, 11, 12),
  (63, 18, 12, 4, 11, 64, 11, 3, 10, 11),
  (57, 39, 20, 2, 12, 9, 26, 87, 4, 15),
  (3, 91, 5, 10, 12, 37, 75, 6, 5, 12),
  (46, 64, 9, 4, 12, 52, 40, 24, 29, 16),
  (64, 11, 7, 8, 11, 55, 42, 24, 6, 13),
  (17, 84, 28, 3, 13, 18, 85, 23, 5, 13),
  (63, 16, 15, 3, 11, 61, 21, 23, 4, 12),
  (3, 91, 7, 9, 12, 3, 91, 3, 11, 12),
  (22, 81, 1, 30, 15, 46, 57, 25, 18, 15),
  (35, 77, 4, 6, 12, 9, 27, 86, 12, 16),
  (22, 86, 2, 8, 12, 36, 76, 0, 8, 12),
  (40, 29, 66, 6, 15, 24, 77, 34, 14, 15),
  (8, 91, 3, 4, 11, 60, 33, 12, 1, 11),
  (8, 91, 1, 5, 11, 59, 38, 2, 5, 11),
  (10, 90, 10, 6, 12, 22, 86, 6, 6, 12),
  (64, 12, 10, 1, 10, 40, 72, 2, 7, 12),
  (49, 60, 6, 0, 11, 59, 38, 4, 4, 11),
  (33, 56, 50, 25, 17, 45, 50, 17, 40, 17),
  (5, 90, 11, 13, 13, 33, 78, 3, 13, 13),
  (54, 12, 49, 8, 14, 54, 32, 39, 8, 14),
  (59, 38, 0, 6, 11, 63, 10, 20, 2, 11),
  (8, 91, 5, 3, 11, 52, 55, 1, 3, 11),
  (3, 91, 9, 8, 12, 3, 91, 1, 12, 12),
  (22, 86, 0, 9, 12, 40, 72, 6, 5, 12),
  (52, 55, 3, 2, 11, 64, 7, 13, 6, 11),
  (21, 84, 22, 5, 13, 55, 32, 37, 2, 13),
  (2, 90, 18, 4, 12, 8, 88, 24, 0, 12),
  (62, 19, 20, 0, 11, 54, 51, 0, 4, 11)
  ]

lemma witC_8400_len : witC_8400.length = 50 := by decide +kernel

lemma witC_8400_all :
    (List.range 50).all (fun i => checkWit10 (8400 + i) (witC_8400.getD i default)) = true := by
  decide +kernel

lemma witC_8400_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8400 + i) (witC_8400.getD i default) = true := by
  intro i hi
  have h := witC_8400_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8450 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (38, 73, 13, 8, 13, 50, 53, 25, 4, 13),
  (0, 91, 13, 1, 11, 59, 38, 6, 3, 11),
  (31, 79, 17, 0, 12, 47, 63, 1, 8, 12),
  (16, 89, 4, 2, 11, 64, 9, 12, 6, 11),
  (57, 44, 2, 4, 11, 3, 86, 32, 4, 13),
  (51, 9, 56, 6, 14, 49, 24, 46, 31, 17),
  (1, 89, 23, 2, 12, 15, 89, 2, 9, 12),
  (60, 1, 34, 10, 13, 36, 5, 76, 8, 15),
  (7, 90, 8, 14, 13, 42, 69, 5, 12, 13),
  (52, 55, 5, 1, 11, 57, 44, 4, 3, 11),
  (15, 87, 21, 0, 12, 5, 45, 79, 12, 16),
  (16, 88, 14, 3, 12, 47, 63, 7, 5, 12),
  (8, 91, 7, 2, 11, 46, 65, 1, 2, 11),
  (47, 61, 18, 0, 12, 53, 44, 30, 3, 13),
  (64, 4, 16, 0, 10, 40, 72, 8, 4, 12),
  (24, 84, 16, 1, 12, 6, 2, 90, 17, 16),
  (26, 84, 3, 7, 12, 60, 31, 7, 16, 13),
  (46, 65, 3, 1, 11, 63, 18, 14, 3, 11),
  (0, 92, 0, 2, 10, 21, 85, 19, 0, 12),
  (0, 92, 2, 1, 10, 3, 91, 11, 7, 12),
  (64, 11, 11, 6, 11, 62, 27, 2, 7, 11),
  (21, 86, 7, 12, 13, 59, 26, 28, 7, 13),
  (17, 87, 18, 1, 12, 33, 79, 2, 7, 12),
  (34, 68, 39, 4, 14, 58, 26, 30, 13, 14),
  (57, 44, 6, 2, 11, 59, 38, 8, 2, 11),
  (36, 71, 29, 1, 13, 44, 63, 25, 3, 13),
  (63, 0, 23, 3, 11, 43, 67, 17, 0, 12),
  (63, 23, 1, 3, 10, 27, 83, 11, 3, 12),
  (60, 31, 11, 14, 13, 48, 55, 29, 2, 13),
  (63, 6, 12, 19, 13, 1, 11, 90, 16, 16),
  (0, 92, 4, 0, 10, 64, 12, 12, 0, 10),
  (62, 3, 28, 0, 11, 50, 6, 54, 23, 16),
  (46, 65, 5, 0, 11, 52, 55, 7, 0, 11),
  (54, 41, 31, 3, 13, 63, 2, 10, 21, 13),
  (59, 39, 1, 0, 10, 47, 63, 9, 4, 12),
  (64, 1, 16, 6, 11, 62, 14, 24, 5, 12),
  (62, 25, 13, 2, 11, 12, 90, 7, 7, 12),
  (3, 1, 92, 2, 14, 3, 73, 56, 2, 14),
  (37, 73, 15, 14, 14, 53, 25, 47, 6, 14),
  (6, 86, 30, 11, 14, 42, 44, 55, 0, 14),
  (62, 21, 19, 0, 11, 54, 49, 1, 16, 13),
  (8, 91, 9, 1, 11, 7, 90, 2, 17, 13),
  (59, 35, 17, 4, 12, 63, 7, 21, 8, 12),
  (40, 72, 10, 3, 12, 55, 47, 15, 3, 12),
  (60, 31, 3, 18, 13, 40, 70, 13, 15, 14),
  (47, 53, 22, 28, 16, 27, 50, 64, 21, 17),
  (58, 2, 42, 0, 12, 0, 76, 52, 4, 14),
  (4, 92, 0, 1, 10, 62, 28, 5, 0, 10),
  (6, 89, 21, 8, 13, 8, 83, 35, 16, 15),
  (57, 44, 8, 1, 11, 56, 47, 3, 3, 11)
  ]

lemma witC_8450_len : witC_8450.length = 50 := by decide +kernel

lemma witC_8450_all :
    (List.range 50).all (fun i => checkWit10 (8450 + i) (witC_8450.getD i default)) = true := by
  decide +kernel

lemma witC_8450_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8450 + i) (witC_8450.getD i default) = true := by
  intro i hi
  have h := witC_8450_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)


lemma a_ge_two_of_lt_8500 {n : ℕ} (hn : 8000 ≤ n) (hlt : n < 8500) : 2 ≤ a n := by
  have hdiv : (n - 8000) / 50 < 10 := by omega
  interval_cases h : (n - 8000) / 50
  · have : n < 8000 + witC_8000.length := by rw [witC_8000_len]; omega
    exact getD_check_ge_two (c := witC_8000) (lo := 8000)
      (fun i hi => by
        have : i < 50 := by rw [witC_8000_len] at hi; exact hi
        exact witC_8000_ok i this) hn this
  · have h1 : 8050 ≤ n := by omega
    have : n < 8050 + witC_8050.length := by rw [witC_8050_len]; omega
    exact getD_check_ge_two (c := witC_8050) (lo := 8050)
      (fun i hi => by
        have : i < 50 := by rw [witC_8050_len] at hi; exact hi
        exact witC_8050_ok i this) h1 this
  · have h1 : 8100 ≤ n := by omega
    have : n < 8100 + witC_8100.length := by rw [witC_8100_len]; omega
    exact getD_check_ge_two (c := witC_8100) (lo := 8100)
      (fun i hi => by
        have : i < 50 := by rw [witC_8100_len] at hi; exact hi
        exact witC_8100_ok i this) h1 this
  · have h1 : 8150 ≤ n := by omega
    have : n < 8150 + witC_8150.length := by rw [witC_8150_len]; omega
    exact getD_check_ge_two (c := witC_8150) (lo := 8150)
      (fun i hi => by
        have : i < 50 := by rw [witC_8150_len] at hi; exact hi
        exact witC_8150_ok i this) h1 this
  · have h1 : 8200 ≤ n := by omega
    have : n < 8200 + witC_8200.length := by rw [witC_8200_len]; omega
    exact getD_check_ge_two (c := witC_8200) (lo := 8200)
      (fun i hi => by
        have : i < 50 := by rw [witC_8200_len] at hi; exact hi
        exact witC_8200_ok i this) h1 this
  · have h1 : 8250 ≤ n := by omega
    have : n < 8250 + witC_8250.length := by rw [witC_8250_len]; omega
    exact getD_check_ge_two (c := witC_8250) (lo := 8250)
      (fun i hi => by
        have : i < 50 := by rw [witC_8250_len] at hi; exact hi
        exact witC_8250_ok i this) h1 this
  · have h1 : 8300 ≤ n := by omega
    have : n < 8300 + witC_8300.length := by rw [witC_8300_len]; omega
    exact getD_check_ge_two (c := witC_8300) (lo := 8300)
      (fun i hi => by
        have : i < 50 := by rw [witC_8300_len] at hi; exact hi
        exact witC_8300_ok i this) h1 this
  · have h1 : 8350 ≤ n := by omega
    have : n < 8350 + witC_8350.length := by rw [witC_8350_len]; omega
    exact getD_check_ge_two (c := witC_8350) (lo := 8350)
      (fun i hi => by
        have : i < 50 := by rw [witC_8350_len] at hi; exact hi
        exact witC_8350_ok i this) h1 this
  · have h1 : 8400 ≤ n := by omega
    have : n < 8400 + witC_8400.length := by rw [witC_8400_len]; omega
    exact getD_check_ge_two (c := witC_8400) (lo := 8400)
      (fun i hi => by
        have : i < 50 := by rw [witC_8400_len] at hi; exact hi
        exact witC_8400_ok i this) h1 this
  · have h1 : 8450 ≤ n := by omega
    have : n < 8450 + witC_8450.length := by rw [witC_8450_len]; omega
    exact getD_check_ge_two (c := witC_8450) (lo := 8450)
      (fun i hi => by
        have : i < 50 := by rw [witC_8450_len] at hi; exact hi
        exact witC_8450_ok i this) h1 this


def witC_8500 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (32, 80, 4, 6, 12, 53, 53, 3, 8, 12),
  (32, 80, 2, 7, 12, 53, 53, 5, 7, 12),
  (54, 49, 13, 10, 13, 59, 30, 24, 8, 13),
  (45, 58, 33, 0, 13, 55, 46, 16, 9, 13),
  (3, 91, 13, 6, 12, 5, 89, 7, 22, 14),
  (6, 90, 18, 3, 12, 34, 78, 10, 3, 12),
  (0, 91, 15, 0, 11, 1, 92, 2, 6, 11),
  (1, 92, 4, 5, 11, 59, 38, 10, 1, 11),
  (29, 65, 51, 0, 14, 11, 83, 9, 36, 16),
  (32, 80, 6, 5, 12, 53, 53, 1, 9, 12),
  (62, 1, 25, 14, 13, 6, 81, 41, 14, 15),
  (17, 75, 48, 2, 14, 23, 72, 37, 30, 17),
  (10, 90, 14, 4, 12, 32, 80, 0, 8, 12),
  (8, 89, 20, 8, 13, 30, 51, 64, 4, 15),
  (18, 85, 25, 4, 13, 20, 73, 48, 9, 15),
  (1, 92, 0, 7, 11, 61, 32, 0, 7, 11),
  (3, 92, 3, 5, 11, 63, 20, 13, 3, 11),
  (2, 90, 20, 3, 12, 22, 86, 12, 3, 12),
  (1, 92, 6, 4, 11, 61, 32, 6, 4, 11),
  (13, 90, 9, 0, 11, 55, 8, 49, 2, 13),
  (65, 5, 3, 6, 10, 27, 83, 13, 2, 12),
  (0, 36, 84, 13, 16, 40, 30, 65, 14, 16),
  (39, 74, 0, 2, 11, 63, 18, 16, 2, 11),
  (39, 74, 2, 1, 11, 63, 10, 22, 1, 11),
  (59, 28, 27, 7, 13, 63, 0, 15, 19, 13),
  (65, 5, 5, 5, 10, 65, 5, 1, 7, 10),
  (56, 27, 39, 2, 13, 6, 85, 35, 2, 13),
  (17, 82, 35, 0, 13, 39, 70, 24, 3, 13),
  (0, 88, 28, 0, 12, 32, 80, 8, 4, 12),
  (18, 88, 11, 4, 12, 38, 50, 54, 15, 16),
  (8, 91, 11, 0, 11, 62, 1, 29, 0, 11),
  (13, 88, 20, 7, 13, 14, 89, 7, 13, 13),
  (40, 72, 12, 2, 12, 59, 27, 29, 0, 12),
  (61, 33, 1, 1, 10, 53, 53, 9, 5, 12),
  (39, 74, 4, 0, 11, 57, 44, 10, 0, 11),
  (59, 36, 9, 14, 13, 53, 46, 15, 24, 15),
  (7, 91, 11, 6, 12, 7, 75, 53, 2, 14),
  (6, 92, 1, 0, 10, 40, 60, 36, 21, 16),
  (35, 78, 0, 2, 11, 8, 83, 39, 0, 13),
  (1, 92, 8, 3, 11, 35, 78, 2, 1, 11),
  (61, 33, 3, 0, 10, 65, 5, 7, 4, 10),
  (62, 23, 18, 0, 11, 30, 79, 22, 4, 13),
  (28, 79, 27, 2, 13, 30, 81, 9, 10, 13),
  (59, 29, 22, 16, 14, 55, 45, 12, 18, 14),
  (57, 41, 19, 2, 12, 61, 29, 15, 6, 12),
  (42, 16, 69, 0, 14, 38, 70, 26, 9, 14),
  (5, 92, 4, 4, 11, 56, 43, 19, 8, 13),
  (60, 35, 11, 1, 11, 31, 81, 0, 8, 12),
  (44, 68, 4, 6, 12, 59, 4, 39, 7, 13),
  (1, 89, 25, 1, 12, 3, 91, 15, 5, 12)
  ]

lemma witC_8500_len : witC_8500.length = 50 := by decide +kernel

lemma witC_8500_all :
    (List.range 50).all (fun i => checkWit10 (8500 + i) (witC_8500.getD i default)) = true := by
  decide +kernel

lemma witC_8500_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8500 + i) (witC_8500.getD i default) = true := by
  intro i hi
  have h := witC_8500_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8550 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (35, 78, 4, 0, 11, 59, 38, 12, 0, 11),
  (55, 49, 0, 10, 12, 25, 71, 44, 18, 16),
  (55, 47, 17, 2, 12, 9, 90, 13, 11, 13),
  (32, 72, 36, 5, 14, 20, 84, 24, 11, 14),
  (64, 11, 15, 4, 11, 7, 90, 16, 10, 13),
  (14, 89, 11, 11, 13, 48, 59, 21, 5, 13),
  (5, 89, 3, 24, 14, 51, 23, 53, 4, 14),
  (32, 80, 10, 3, 12, 44, 68, 6, 5, 12),
  (30, 81, 1, 14, 13, 0, 59, 71, 6, 15),
  (63, 14, 8, 19, 13, 35, 5, 78, 0, 14),
  (53, 54, 5, 1, 11, 44, 68, 0, 8, 12),
  (38, 74, 14, 1, 12, 54, 47, 22, 6, 13),
  (41, 72, 4, 0, 11, 20, 87, 7, 12, 13),
  (15, 90, 2, 3, 11, 55, 50, 2, 3, 11),
  (22, 86, 14, 2, 12, 50, 58, 14, 2, 12),
  (65, 5, 9, 3, 10, 10, 90, 16, 3, 12),
  (15, 90, 0, 4, 11, 55, 50, 0, 4, 11),
  (45, 47, 48, 2, 14, 3, 68, 57, 26, 17),
  (57, 17, 41, 10, 14, 41, 54, 47, 9, 15),
  (34, 79, 4, 0, 11, 52, 5, 56, 0, 13),
  (1, 92, 10, 2, 11, 15, 90, 4, 2, 11),
  (0, 83, 41, 1, 13, 6, 89, 23, 7, 13),
  (63, 25, 0, 3, 10, 17, 89, 3, 8, 12),
  (17, 89, 5, 7, 12, 27, 83, 15, 1, 12),
  (51, 58, 2, 2, 11, 20, 87, 3, 14, 13),
  (63, 22, 12, 3, 11, 55, 36, 35, 2, 13),
  (44, 68, 8, 4, 12, 61, 13, 31, 2, 12),
  (54, 48, 21, 0, 12, 24, 85, 2, 14, 13),
  (64, 3, 19, 4, 11, 4, 87, 31, 4, 13),
  (62, 29, 1, 7, 11, 3, 86, 34, 3, 13),
  (64, 8, 0, 18, 12, 11, 87, 25, 12, 14),
  (64, 17, 8, 6, 11, 16, 88, 18, 1, 12),
  (26, 85, 1, 2, 11, 48, 62, 11, 3, 12),
  (9, 22, 89, 4, 15, 9, 58, 71, 4, 15),
  (17, 89, 7, 6, 12, 49, 61, 5, 6, 12),
  (30, 82, 6, 5, 12, 8, 86, 31, 10, 14),
  (12, 91, 1, 4, 11, 0, 91, 7, 16, 13),
  (15, 90, 6, 1, 11, 26, 85, 3, 1, 11),
  (59, 40, 1, 5, 11, 5, 89, 19, 16, 14),
  (58, 42, 4, 9, 12, 56, 36, 30, 11, 14),
  (20, 87, 11, 10, 13, 55, 6, 50, 2, 13),
  (27, 80, 27, 2, 13, 61, 28, 14, 13, 13),
  (8, 92, 0, 0, 10, 58, 42, 6, 8, 12),
  (8, 90, 19, 2, 12, 20, 42, 77, 10, 16),
  (30, 81, 13, 8, 13, 36, 71, 31, 0, 13),
  (18, 89, 5, 1, 11, 0, 91, 5, 17, 13),
  (7, 92, 5, 3, 11, 2, 90, 22, 2, 12),
  (61, 29, 17, 5, 12, 62, 22, 20, 5, 12),
  (0, 91, 11, 14, 13, 53, 8, 54, 0, 13),
  (29, 79, 24, 10, 14, 17, 87, 14, 16, 14)
  ]

lemma witC_8550_len : witC_8550.length = 50 := by decide +kernel

lemma witC_8550_all :
    (List.range 50).all (fun i => checkWit10 (8550 + i) (witC_8550.getD i default)) = true := by
  decide +kernel

lemma witC_8550_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8550 + i) (witC_8550.getD i default) = true := by
  intro i hi
  have h := witC_8550_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8600 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (65, 5, 11, 2, 10, 59, 31, 1, 26, 14),
  (26, 83, 18, 6, 13, 14, 72, 55, 0, 14),
  (26, 85, 5, 0, 11, 43, 70, 0, 2, 11),
  (65, 7, 10, 2, 10, 43, 70, 2, 1, 11),
  (62, 30, 4, 0, 10, 3, 91, 17, 4, 12),
  (64, 20, 2, 3, 10, 17, 89, 9, 5, 12),
  (2, 85, 37, 2, 13, 54, 41, 33, 2, 13),
  (65, 3, 12, 2, 10, 43, 69, 12, 2, 12),
  (64, 20, 0, 4, 10, 29, 78, 29, 1, 13),
  (30, 80, 3, 20, 14, 62, 14, 10, 25, 14),
  (54, 52, 5, 7, 12, 38, 69, 31, 0, 13),
  (1, 92, 12, 1, 11, 61, 32, 12, 1, 11),
  (64, 20, 4, 2, 10, 4, 92, 4, 10, 12),
  (4, 92, 6, 9, 12, 11, 91, 3, 9, 12),
  (15, 90, 8, 0, 11, 43, 70, 4, 0, 11),
  (59, 2, 40, 7, 13, 63, 0, 1, 26, 13),
  (65, 9, 9, 2, 10, 65, 2, 9, 9, 11),
  (58, 43, 6, 2, 11, 2, 92, 1, 12, 12),
  (22, 81, 33, 0, 13, 63, 2, 0, 26, 13),
  (63, 2, 26, 1, 11, 0, 91, 13, 13, 13),
  (29, 81, 11, 16, 14, 41, 61, 39, 4, 14),
  (4, 92, 2, 11, 12, 11, 91, 7, 7, 12),
  (60, 31, 19, 10, 13, 47, 62, 18, 6, 13),
  (31, 69, 44, 2, 14, 57, 27, 36, 10, 14),
  (65, 1, 13, 2, 10, 4, 92, 8, 8, 12),
  (6, 91, 4, 16, 13, 40, 45, 58, 6, 15),
  (64, 19, 3, 8, 11, 16, 83, 35, 0, 13),
  (64, 19, 5, 7, 11, 63, 13, 22, 6, 12),
  (10, 90, 18, 2, 12, 58, 42, 10, 6, 12),
  (64, 20, 6, 1, 10, 58, 11, 42, 4, 13),
  (65, 4, 10, 8, 11, 9, 84, 34, 16, 15),
  (65, 0, 10, 9, 11, 65, 8, 6, 9, 11),
  (59, 35, 21, 2, 12, 49, 58, 21, 5, 13),
  (0, 92, 0, 13, 12, 2, 47, 80, 4, 15),
  (21, 88, 2, 2, 11, 32, 75, 31, 0, 13),
  (21, 88, 0, 3, 11, 64, 19, 1, 9, 11),
  (17, 89, 11, 4, 12, 27, 83, 17, 0, 12),
  (44, 69, 0, 2, 11, 63, 23, 7, 11, 12),
  (64, 19, 7, 6, 11, 46, 65, 9, 10, 13),
  (65, 11, 8, 2, 10, 61, 34, 5, 4, 11),
  (4, 92, 0, 12, 12, 11, 91, 9, 6, 12),
  (16, 82, 37, 6, 14, 42, 48, 53, 0, 14),
  (30, 73, 37, 12, 15, 46, 25, 61, 8, 15),
  (21, 88, 4, 1, 11, 0, 91, 1, 19, 13),
  (65, 13, 3, 4, 10, 63, 24, 11, 3, 11),
  (65, 13, 1, 5, 10, 65, 5, 13, 1, 10),
  (9, 92, 2, 4, 11, 45, 64, 22, 4, 13),
  (57, 15, 32, 30, 16, 55, 33, 8, 38, 16),
  (63, 23, 9, 10, 12, 63, 7, 25, 6, 12),
  (2, 44, 81, 12, 16, 0, 52, 76, 13, 16)
  ]

lemma witC_8600_len : witC_8600.length = 50 := by decide +kernel

lemma witC_8600_all :
    (List.range 50).all (fun i => checkWit10 (8600 + i) (witC_8600.getD i default)) = true := by
  decide +kernel

lemma witC_8600_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8600 + i) (witC_8600.getD i default) = true := by
  intro i hi
  have h := witC_8600_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

def witC_8650 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
  (31, 82, 0, 2, 11, 0, 91, 15, 12, 13),
  (9, 92, 4, 3, 11, 9, 92, 0, 5, 11),
  (1, 89, 27, 0, 12, 59, 3, 41, 0, 12),
  (1, 93, 1, 1, 10, 65, 13, 5, 3, 10),
  (6, 89, 25, 6, 13, 8, 91, 7, 14, 13),
  (57, 11, 44, 10, 14, 9, 83, 2, 40, 16),
  (64, 20, 8, 0, 10, 25, 86, 3, 1, 11),
  (24, 74, 45, 2, 14, 26, 80, 29, 8, 14),
  (20, 87, 15, 8, 13, 50, 20, 57, 3, 14),
  (64, 19, 9, 5, 11, 65, 4, 12, 7, 11),
  (1, 93, 3, 0, 10, 61, 29, 19, 4, 12),
  (56, 48, 6, 7, 12, 56, 48, 2, 9, 12),
  (1, 92, 14, 0, 11, 21, 88, 6, 0, 11),
  (63, 17, 20, 6, 12, 5, 68, 58, 25, 17),
  (63, 23, 1, 14, 12, 29, 81, 15, 14, 14),
  (50, 34, 50, 3, 14, 58, 2, 42, 13, 14),
  (9, 92, 6, 2, 11, 63, 26, 4, 6, 11),
  (63, 26, 2, 7, 11, 29, 80, 24, 3, 13),
  (46, 66, 8, 4, 12, 55, 43, 25, 12, 14),
  (3, 91, 19, 3, 12, 11, 91, 11, 5, 12),
  (60, 37, 10, 1, 11, 64, 6, 19, 9, 12),
  (37, 74, 21, 4, 13, 55, 4, 51, 2, 13),
  (63, 27, 1, 2, 10, 65, 13, 7, 2, 10),
  (62, 27, 16, 0, 11, 64, 12, 16, 9, 12),
  (8, 91, 11, 12, 13, 8, 91, 3, 16, 13),
  (63, 26, 6, 5, 11, 33, 79, 16, 0, 12),
  (4, 92, 12, 6, 12, 28, 84, 4, 6, 12),
  (63, 27, 3, 1, 10, 17, 89, 13, 3, 12),
  (63, 26, 0, 8, 11, 64, 11, 19, 2, 11),
  (23, 6, 84, 23, 17, 5, 78, 39, 32, 17),
  (31, 81, 14, 1, 12, 45, 66, 15, 7, 13),
  (20, 49, 74, 2, 15, 36, 61, 48, 8, 15),
  (62, 12, 29, 3, 12, 62, 16, 27, 3, 12),
  (13, 88, 24, 5, 13, 23, 82, 30, 1, 13),
  (45, 65, 3, 20, 14, 43, 15, 69, 0, 14),
  (2, 90, 24, 1, 12, 23, 87, 3, 7, 12),
  (14, 91, 2, 3, 11, 56, 49, 2, 3, 11),
  (57, 42, 19, 8, 13, 9, 83, 40, 6, 14),
  (22, 86, 18, 0, 12, 23, 87, 5, 6, 12),
  (8, 92, 4, 9, 12, 64, 4, 20, 9, 12),
  (64, 19, 11, 4, 11, 46, 65, 13, 8, 13),
  (2, 93, 3, 5, 11, 9, 92, 8, 1, 11),
  (63, 27, 5, 0, 10, 23, 87, 1, 8, 12),
  (30, 83, 0, 2, 11, 44, 68, 14, 1, 12),
  (2, 93, 1, 6, 11, 63, 26, 8, 4, 11),
  (1, 90, 23, 8, 13, 17, 88, 18, 7, 13),
  (61, 5, 35, 2, 12, 0, 92, 14, 6, 12),
  (26, 84, 17, 0, 12, 20, 88, 12, 3, 12),
  (2, 93, 5, 4, 11, 65, 12, 2, 10, 11),
  (4, 87, 33, 3, 13, 8, 91, 13, 11, 13)
  ]

lemma witC_8650_len : witC_8650.length = 50 := by decide +kernel

lemma witC_8650_all :
    (List.range 50).all (fun i => checkWit10 (8650 + i) (witC_8650.getD i default)) = true := by
  decide +kernel

lemma witC_8650_ok : ∀ i : ℕ, i < 50 →
    checkWit10 (8650 + i) (witC_8650.getD i default) = true := by
  intro i hi
  have h := witC_8650_all
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)



lemma a_ge_two_of_lt_8700 {n : ℕ} (hn : 8500 ≤ n) (hlt : n < 8700) : 2 ≤ a n := by
  have hdiv : (n - 8500) / 50 < 4 := by omega
  interval_cases h : (n - 8500) / 50
  · have : n < 8500 + witC_8500.length := by rw [witC_8500_len]; omega
    exact getD_check_ge_two (c := witC_8500) (lo := 8500)
      (fun i hi => by
        have : i < 50 := by rw [witC_8500_len] at hi; exact hi
        exact witC_8500_ok i this) hn this
  · have h1 : 8550 ≤ n := by omega
    have : n < 8550 + witC_8550.length := by rw [witC_8550_len]; omega
    exact getD_check_ge_two (c := witC_8550) (lo := 8550)
      (fun i hi => by
        have : i < 50 := by rw [witC_8550_len] at hi; exact hi
        exact witC_8550_ok i this) h1 this
  · have h1 : 8600 ≤ n := by omega
    have : n < 8600 + witC_8600.length := by rw [witC_8600_len]; omega
    exact getD_check_ge_two (c := witC_8600) (lo := 8600)
      (fun i hi => by
        have : i < 50 := by rw [witC_8600_len] at hi; exact hi
        exact witC_8600_ok i this) h1 this
  · have h1 : 8650 ≤ n := by omega
    have : n < 8650 + witC_8650.length := by rw [witC_8650_len]; omega
    exact getD_check_ge_two (c := witC_8650) (lo := 8650)
      (fun i hi => by
        have : i < 50 := by rw [witC_8650_len] at hi; exact hi
        exact witC_8650_ok i this) h1 this


/- ### Tail: `n ≥ 8500` via the `γ = 16` family -/

/-- All four integrality conditions (and the `P4` congruence) follow from
`λ + s + 2 t ≡ 0 [ZMOD 4]`. -/
lemma params16_div_of_cong (k : ℕ) (lam s t : ℤ)
    (h : lam + s + 2 * t ≡ 0 [ZMOD 4]) :
    (4 : ℤ) ∣ (-4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t) ∧
    (4 : ℤ) ∣ (8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t) ∧
    (4 : ℤ) ∣ (lam - 3 * s + 2 * t) ∧
    (2 : ℤ) ∣ (lam + s) ∧
    (16 * (k : ℤ) ^ 2 - 43 * lam + s + 2 * t) ≡ 0 [ZMOD 4] := by
  have h' : (lam + s + 2 * t) % 4 = 0 := by
    simpa [Int.ModEq] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · change (16 * (k : ℤ) ^ 2 - 43 * lam + s + 2 * t) % 4 = 0
    omega

/-- Streamlined `γ = 16` constructor: one congruence plus nonnegativity of
the four numerators. -/
lemma IsRep.of_params16_simple (n k : ℕ) (lam s t : ℤ)
    (hM : (n : ℤ) = 6 * (k : ℤ) ^ 4 - 32 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2
      + s * s + t * t)
    (hcong : lam + s + 2 * t ≡ 0 [ZMOD 4])
    (hwN : 0 ≤ -4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t)
    (hxN : 0 ≤ 8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t)
    (hyN : 0 ≤ lam - 3 * s + 2 * t)
    (hzN : 0 ≤ lam + s) :
    IsRep n
      (Int.toNat ((-4 * (k : ℤ) ^ 2 + 11 * lam - s - 2 * t) / 4))
      (Int.toNat ((8 * (k : ℤ) ^ 2 - 21 * lam - s - 2 * t) / 4))
      (Int.toNat ((lam - 3 * s + 2 * t) / 4))
      (Int.toNat ((lam + s) / 2)) := by
  obtain ⟨hdivw, hdivx, hdivy, hdivz, hmod⟩ := params16_div_of_cong k lam s t hcong
  refine IsRep.of_params16 n k lam s t hM hdivw hdivx hdivy hdivz ?_ ?_ ?_ ?_ hmod
  · exact Int.ediv_nonneg hwN (by decide)
  · exact Int.ediv_nonneg hxN (by decide)
  · exact Int.ediv_nonneg hyN (by decide)
  · exact Int.ediv_nonneg hzN (by decide)

/- The `γ = 27` family (covers some `n ≡ 1, 7 [MOD 8]`) -/

lemma params27_num_H (k : ℕ) (lam s t : ℤ) :
    let r := 27 * (k : ℤ) ^ 2 - 43 * lam
    Hform r s t = 43 *
      (17 * (k : ℤ) ^ 4 - 54 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2 + s * s + t * t)
      - 2 * (k : ℤ) ^ 4 := by
  intro r
  unfold Hform
  simp only [r]
  ring

lemma params27_div_of_cong (k : ℕ) (lam s t : ℤ)
    (h : (27 * (k : ℤ) ^ 2 - 43 * lam + 2 * s + 10 * t) % 7 = 0) :
    (7 : ℤ) ∣ (-8 * (k : ℤ) ^ 2 + 13 * lam + 2 * s - 4 * t) ∧
    (7 : ℤ) ∣ (11 * (k : ℤ) ^ 2 - 17 * lam + 6 * s + 2 * t) ∧
    (7 : ℤ) ∣ (22 * (k : ℤ) ^ 2 - 34 * lam - 2 * s - 3 * t) ∧
    (7 : ℤ) ∣ (-10 * (k : ℤ) ^ 2 + 18 * lam - s + 2 * t) ∧
    (27 * (k : ℤ) ^ 2 - 43 * lam + 2 * s + 10 * t) % 7 = 0 ∧
    (2 * (27 * (k : ℤ) ^ 2 - 43 * lam) - 10 * s + 13 * t) % 7 = 0 ∧
    (2 * (27 * (k : ℤ) ^ 2 - 43 * lam) - 17 * s + 34 * t) % 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, h, ?_, ?_⟩
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · exact Int.dvd_iff_emod_eq_zero.mpr (by omega)
  · omega
  · omega

lemma IsRep.of_params27_simple (n k : ℕ) (lam s t : ℤ)
    (hM : (n : ℤ) = 17 * (k : ℤ) ^ 4 - 54 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2
      + s * s + t * t)
    (hcong : (27 * (k : ℤ) ^ 2 - 43 * lam + 2 * s + 10 * t) % 7 = 0)
    (hwN : 0 ≤ -8 * (k : ℤ) ^ 2 + 13 * lam + 2 * s - 4 * t)
    (hxN : 0 ≤ 11 * (k : ℤ) ^ 2 - 17 * lam + 6 * s + 2 * t)
    (hyN : 0 ≤ 22 * (k : ℤ) ^ 2 - 34 * lam - 2 * s - 3 * t)
    (hzN : 0 ≤ -10 * (k : ℤ) ^ 2 + 18 * lam - s + 2 * t) :
    IsRep n
      (Int.toNat ((-8 * (k : ℤ) ^ 2 + 13 * lam + 2 * s - 4 * t) / 7))
      (Int.toNat ((11 * (k : ℤ) ^ 2 - 17 * lam + 6 * s + 2 * t) / 7))
      (Int.toNat ((22 * (k : ℤ) ^ 2 - 34 * lam - 2 * s - 3 * t) / 7))
      (Int.toNat ((-10 * (k : ℤ) ^ 2 + 18 * lam - s + 2 * t) / 7)) := by
  obtain ⟨hdivw, hdivx, hdivy, hdivz, h1, h2, h3⟩ := params27_div_of_cong k lam s t hcong
  set r := 27 * (k : ℤ) ^ 2 - 43 * lam
  set a := (r + 2 * s + 10 * t) / 7
  set b := (2 * r - 10 * s + 13 * t) / 7
  set c := (2 * r - 17 * s + 34 * t) / 7
  have hG : G a b c = Hform r s t :=
    G_of_P_of_mod7 r s t (by simpa [Int.ModEq, r] using h1)
      (by simpa [Int.ModEq, r] using h2)
      (by simpa [Int.ModEq, r] using h3)
  have hH : Hform r s t = 43 * (n : ℤ) - 2 * (k : ℤ) ^ 4 := by
    have h1' := params27_num_H k lam s t
    simp only [r] at h1'
    have h2' : (17 * (k : ℤ) ^ 4 - 54 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2 + s * s + t * t) = (n : ℤ) := by
      linarith [hM]
    simpa [h2'] using h1'
  set wZ := (-8 * (k : ℤ) ^ 2 + 13 * lam + 2 * s - 4 * t) / 7
  set xZ := (11 * (k : ℤ) ^ 2 - 17 * lam + 6 * s + 2 * t) / 7
  set yZ := (22 * (k : ℤ) ^ 2 - 34 * lam - 2 * s - 3 * t) / 7
  set zZ := (-10 * (k : ℤ) ^ 2 + 18 * lam - s + 2 * t) / 7
  have hw0 : 0 ≤ wZ := Int.ediv_nonneg hwN (by decide)
  have hx0 : 0 ≤ xZ := Int.ediv_nonneg hxN (by decide)
  have hy0 : 0 ≤ yZ := Int.ediv_nonneg hyN (by decide)
  have hz0 : 0 ≤ zZ := Int.ediv_nonneg hzN (by decide)
  have hwNat : ((Int.toNat wZ : ℤ) = wZ) := Int.toNat_of_nonneg hw0
  have hxNat : ((Int.toNat xZ : ℤ) = xZ) := Int.toNat_of_nonneg hx0
  have hyNat : ((Int.toNat yZ : ℤ) = yZ) := Int.toNat_of_nonneg hy0
  have hzNat : ((Int.toNat zZ : ℤ) = zZ) := Int.toNat_of_nonneg hz0
  have hw7 : 7 * wZ = -8 * (k : ℤ) ^ 2 + 13 * lam + 2 * s - 4 * t :=
    Int.mul_ediv_cancel' hdivw
  have hx7 : 7 * xZ = 11 * (k : ℤ) ^ 2 - 17 * lam + 6 * s + 2 * t :=
    Int.mul_ediv_cancel' hdivx
  have hy7 : 7 * yZ = 22 * (k : ℤ) ^ 2 - 34 * lam - 2 * s - 3 * t :=
    Int.mul_ediv_cancel' hdivy
  have hz7 : 7 * zZ = -10 * (k : ℤ) ^ 2 + 18 * lam - s + 2 * t :=
    Int.mul_ediv_cancel' hdivz
  have hxrel : xZ = a + 2 * wZ := by
    have : 7 * xZ = (r + 2 * s + 10 * t) + 2 * (7 * wZ) := by
      simp only [r] at hx7 hw7 ⊢
      linarith [hx7, hw7]
    have ha : r + 2 * s + 10 * t = 7 * a := by
      have : (7 : ℤ) ∣ r + 2 * s + 10 * t :=
        Int.dvd_iff_emod_eq_zero.mpr (by simpa [r] using h1)
      simpa [a] using (Int.mul_ediv_cancel' this).symm
    linarith
  have hyrel : yZ = b + 4 * wZ := by
    have : 7 * yZ = (2 * r - 10 * s + 13 * t) + 4 * (7 * wZ) := by
      simp only [r] at hy7 hw7 ⊢
      linarith [hy7, hw7]
    have hb : 2 * r - 10 * s + 13 * t = 7 * b := by
      have : (7 : ℤ) ∣ 2 * r - 10 * s + 13 * t :=
        Int.dvd_iff_emod_eq_zero.mpr (by simpa [r] using h2)
      simpa [b] using (Int.mul_ediv_cancel' this).symm
    linarith
  have hzrel : zZ = c + 8 * wZ := by
    have : 7 * zZ = (2 * r - 17 * s + 34 * t) + 8 * (7 * wZ) := by
      simp only [r] at hz7 hw7 ⊢
      linarith [hz7, hw7]
    have hc : 2 * r - 17 * s + 34 * t = 7 * c := by
      have : (7 : ℤ) ∣ 2 * r - 17 * s + 34 * t :=
        Int.dvd_iff_emod_eq_zero.mpr (by simpa [r] using h3)
      simpa [c] using (Int.mul_ediv_cancel' this).symm
    linarith
  have hwrel : (k : ℤ) ^ 2 = 43 * wZ + a + 2 * b + 4 * c := by
    have ha : r + 2 * s + 10 * t = 7 * a := by
      have : (7 : ℤ) ∣ r + 2 * s + 10 * t :=
        Int.dvd_iff_emod_eq_zero.mpr (by simpa [r] using h1)
      simpa [a] using (Int.mul_ediv_cancel' this).symm
    have hb : 2 * r - 10 * s + 13 * t = 7 * b := by
      have : (7 : ℤ) ∣ 2 * r - 10 * s + 13 * t :=
        Int.dvd_iff_emod_eq_zero.mpr (by simpa [r] using h2)
      simpa [b] using (Int.mul_ediv_cancel' this).symm
    have hc : 2 * r - 17 * s + 34 * t = 7 * c := by
      have : (7 : ℤ) ∣ 2 * r - 17 * s + 34 * t :=
        Int.dvd_iff_emod_eq_zero.mpr (by simpa [r] using h3)
      simpa [c] using (Int.mul_ediv_cancel' this).symm
    have : 7 * (k : ℤ) ^ 2 = 43 * (7 * wZ) + 7 * a + 2 * (7 * b) + 4 * (7 * c) := by
      simp only [r] at hw7 ha hb hc ⊢
      linarith [hw7, ha, hb, hc]
    linarith
  refine IsRep.of_Hform n k r s t a b c
    (Int.toNat wZ) (Int.toNat xZ) (Int.toNat yZ) (Int.toNat zZ) hH hG ?_ ?_ ?_ ?_
  · rw [hwNat]; exact hwrel
  · rw [hxNat, hwNat]; exact hxrel
  · rw [hyNat, hwNat]; exact hyrel
  · rw [hzNat, hwNat]; exact hzrel



/-- `⌊3 k² / 8⌋` lies in the params16 cone for `k ≥ 10`. -/
lemma lam_three_eighths_mem_cone {k : ℕ} (hk : 10 ≤ k) :
    let lam : ℤ := (3 * (k : ℤ) ^ 2) / 8
    4 * (k : ℤ) ^ 2 ≤ 11 * lam ∧ 21 * lam ≤ 8 * (k : ℤ) ^ 2 := by
  intro lam
  have hk2 : (100 : ℤ) ≤ (k : ℤ) ^ 2 := by
    have : (10 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    nlinarith
  have hrem_nonneg : (0 : ℤ) ≤ (3 * (k : ℤ) ^ 2) % 8 :=
    Int.emod_nonneg _ (by decide : (8 : ℤ) ≠ 0)
  have hrem_lt : (3 * (k : ℤ) ^ 2) % 8 < 8 :=
    Int.emod_lt_of_pos _ (by decide : (0 : ℤ) < 8)
  have hsplit : 8 * lam = 3 * (k : ℤ) ^ 2 - (3 * (k : ℤ) ^ 2) % 8 := by
    have := Int.mul_ediv_add_emod (3 * (k : ℤ) ^ 2) 8
    simp [lam] at this ⊢
    linarith
  constructor
  · have : 32 * (k : ℤ) ^ 2 ≤ 11 * (8 * lam) := by
      have : 32 * (k : ℤ) ^ 2 ≤ 11 * (3 * (k : ℤ) ^ 2 - (3 * (k : ℤ) ^ 2) % 8) := by
        nlinarith
      simpa [hsplit]
    nlinarith
  · have : 21 * (8 * lam) ≤ 64 * (k : ℤ) ^ 2 := by
      have : 21 * (3 * (k : ℤ) ^ 2 - (3 * (k : ℤ) ^ 2) % 8) ≤ 64 * (k : ℤ) ^ 2 := by
        nlinarith
      simpa [hsplit]
    nlinarith

lemma ten_mul_div_le (a : ℤ) : 10 * (a / 10) ≤ a := by
  have := Int.ediv_mul_le a (by decide : (10 : ℤ) ≠ 0)
  linarith

/-- Slack around `⌊3k²/8⌋` is at least `k²/10` for `k ≥ 20`. -/
lemma cone_slack_of_ge {k : ℕ} (hk : 20 ≤ k) :
    let lam : ℤ := (3 * (k : ℤ) ^ 2) / 8
    4 * (k : ℤ) ^ 2 + (k : ℤ) ^ 2 / 10 ≤ 11 * lam ∧
      21 * lam + (k : ℤ) ^ 2 / 10 ≤ 8 * (k : ℤ) ^ 2 := by
  intro lam
  have hk2 : (400 : ℤ) ≤ (k : ℤ) ^ 2 := by
    have : (20 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    nlinarith
  have hrem0 : (0 : ℤ) ≤ (3 * (k : ℤ) ^ 2) % 8 :=
    Int.emod_nonneg _ (by decide : (8 : ℤ) ≠ 0)
  have hrem7 : (3 * (k : ℤ) ^ 2) % 8 ≤ 7 := by
    have := Int.emod_lt_of_pos (3 * (k : ℤ) ^ 2) (by decide : (0 : ℤ) < 8)
    omega
  have hsplit : 8 * lam = 3 * (k : ℤ) ^ 2 - (3 * (k : ℤ) ^ 2) % 8 := by
    have := Int.mul_ediv_add_emod (3 * (k : ℤ) ^ 2) 8
    simp [lam] at this ⊢
    linarith
  have hd10 : 10 * ((k : ℤ) ^ 2 / 10) ≤ (k : ℤ) ^ 2 := ten_mul_div_le _
  constructor
  · have hmul : 110 * (8 * lam) ≥ 328 * (k : ℤ) ^ 2 := by
      have : 110 * (3 * (k : ℤ) ^ 2 - (3 * (k : ℤ) ^ 2) % 8)
          ≥ 328 * (k : ℤ) ^ 2 := by nlinarith [hrem0, hrem7]
      simpa [hsplit]
    have : 880 * lam ≥ 328 * (k : ℤ) ^ 2 := by nlinarith
    nlinarith [hd10]
  · have : 210 * (8 * lam) ≤ 632 * (k : ℤ) ^ 2 := by
      have : 210 * (3 * (k : ℤ) ^ 2 - (3 * (k : ℤ) ^ 2) % 8)
          ≤ 632 * (k : ℤ) ^ 2 := by nlinarith [hrem0, hrem7]
      simpa [hsplit]
    nlinarith [hd10]

/-- Bambah–Chowla: there is a sum of two squares in `(X, X + 2⌊√X⌋ + 1]`. -/
lemma bambah_chowla (X : ℕ) :
    ∃ s t : ℕ, X < s ^ 2 + t ^ 2 ∧ s ^ 2 + t ^ 2 ≤ X + 2 * X.sqrt + 1 := by
  set a := X.sqrt
  have ha : a ^ 2 ≤ X := Nat.sqrt_le' X
  set rem := X - a ^ 2
  set b := rem.sqrt
  have hb : b ^ 2 ≤ rem := Nat.sqrt_le' rem
  have hsum : a ^ 2 + b ^ 2 ≤ X := by
    have := Nat.add_le_add_left hb (a ^ 2)
    simpa [rem, Nat.add_sub_cancel' ha] using this
  have hnext : X < a ^ 2 + (b + 1) ^ 2 := by
    have : rem < (b + 1) ^ 2 := Nat.lt_succ_sqrt' rem
    omega
  have hb_le_a : b ≤ a := by
    simpa [a, b, rem] using Nat.sqrt_le_sqrt (Nat.sub_le X (a ^ 2))
  have hle : a ^ 2 + (b + 1) ^ 2 ≤ X + 2 * a + 1 := by
    have : (b + 1) ^ 2 = b ^ 2 + 2 * b + 1 := by ring
    omega
  refine ⟨a, b + 1, hnext, ?_⟩
  simpa [a] using hle

/-- The `γ = 16` quartic. -/
def Q16 (k : ℕ) (lam : ℤ) : ℤ :=
  6 * (k : ℤ) ^ 4 - 32 * (k : ℤ) ^ 2 * lam + 43 * lam ^ 2

lemma Q16_mul_43 (k : ℕ) (lam : ℤ) :
    43 * Q16 k lam = 2 * (k : ℤ) ^ 4 + (16 * (k : ℤ) ^ 2 - 43 * lam) ^ 2 := by
  unfold Q16
  ring

lemma Q16_floor_vertex (k : ℕ) :
    let lam := 16 * (k : ℤ) ^ 2 / 43
    let r := 16 * (k : ℤ) ^ 2 % 43
    43 * Q16 k lam = 2 * (k : ℤ) ^ 4 + r ^ 2 := by
  intro lam r
  have hsplit : 16 * (k : ℤ) ^ 2 = 43 * lam + r :=
    (Int.mul_ediv_add_emod (16 * (k : ℤ) ^ 2) 43).symm
  have h := Q16_mul_43 k lam
  have hr : 16 * (k : ℤ) ^ 2 - 43 * lam = r := by linarith [hsplit]
  simpa [hr] using h

lemma Q16_floor_vertex_nonneg (k : ℕ) :
    0 ≤ Q16 k (16 * (k : ℤ) ^ 2 / 43) := by
  have h := Q16_floor_vertex k
  simp only at h
  have hsum : 0 ≤ 2 * (k : ℤ) ^ 4 + (16 * (k : ℤ) ^ 2 % 43) ^ 2 := by
    nlinarith [sq_nonneg (16 * (k : ℤ) ^ 2 % 43)]
  have hdvd : (43 : ℤ) ∣ 2 * (k : ℤ) ^ 4 + (16 * (k : ℤ) ^ 2 % 43) ^ 2 :=
    ⟨Q16 k (16 * (k : ℤ) ^ 2 / 43), by linarith [h]⟩
  have hdiv := Int.mul_ediv_cancel' hdvd
  have hQ : Q16 k (16 * (k : ℤ) ^ 2 / 43) =
      (2 * (k : ℤ) ^ 4 + (16 * (k : ℤ) ^ 2 % 43) ^ 2) / 43 := by
    linarith [hdiv, h]
  rw [hQ]
  exact Int.ediv_nonneg hsum (by decide : (0 : ℤ) ≤ 43)

/-- Largest `k` with `2 k^4 ≤ 43 n`, searched up to `3 ⌊n^{1/4}⌋ + 5`
(comfortably above `(43 n / 2)^{1/4} ≈ 2.15 n^{1/4}`). -/
def kMax (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => 2 * k ^ 4 ≤ 43 * n) (3 * n.sqrt.sqrt + 5)

lemma kMax_spec (n : ℕ) :
    2 * (kMax n) ^ 4 ≤ 43 * n ∧
      ∀ k, k ≤ 3 * n.sqrt.sqrt + 5 → 2 * k ^ 4 ≤ 43 * n → k ≤ kMax n := by
  set P : ℕ → Prop := fun k => 2 * k ^ 4 ≤ 43 * n
  constructor
  · have h0 : P 0 := by simp [P]
    simpa [kMax, P] using
      Nat.findGreatest_spec (P := P) (m := 0) (n := 3 * n.sqrt.sqrt + 5)
        (Nat.zero_le _) h0
  · intro k hk hle
    exact Nat.le_findGreatest (P := P) hk hle

lemma Q16_shift (k : ℕ) (lam : ℤ) (d : ℤ) :
    Q16 k (lam + d) = Q16 k lam - 2 * (16 * (k : ℤ) ^ 2 - 43 * lam) * d + 43 * d ^ 2 := by
  unfold Q16
  ring

lemma Q16_shift_vertex (k : ℕ) (d : ℤ) :
    let lam := 16 * (k : ℤ) ^ 2 / 43
    let r := 16 * (k : ℤ) ^ 2 % 43
    Q16 k (lam + d) = Q16 k lam - 2 * r * d + 43 * d ^ 2 := by
  intro lam r
  have h := Q16_shift k lam d
  have hsplit : 16 * (k : ℤ) ^ 2 = 43 * lam + r :=
    (Int.mul_ediv_add_emod (16 * (k : ℤ) ^ 2) 43).symm
  have hr : 16 * (k : ℤ) ^ 2 - 43 * lam = r := by linarith [hsplit]
  simpa [hr] using h

lemma kMax_ge_twenty {n : ℕ} (hn : 8700 ≤ n) : 20 ≤ kMax n := by
  have hbd : 20 ≤ 3 * n.sqrt.sqrt + 5 := by
    have : 5 ≤ n.sqrt.sqrt := by
      have : 625 ≤ n := by omega
      have hs : 25 ≤ n.sqrt := Nat.le_sqrt.mpr (by omega)
      exact Nat.le_sqrt.mpr (by omega)
    omega
  have := (kMax_spec n).2 20 hbd (by
    have : 2 * 20 ^ 4 = 320000 := by decide
    have : 43 * 8700 ≤ 43 * n := Nat.mul_le_mul_left 43 hn
    omega)
  exact this

/-- Increment of type `(-1, 1, 0, 0)` when `x + 1 = 2w`. -/
lemma IsRep.inc_neg1_pos1 {n w x y z : ℕ} (h : IsRep n w x y z)
    (hx : x + 1 = 2 * w) (hw : 1 ≤ w) :
    IsRep (n + 1) (w - 1) (x + 1) y z := by
  obtain ⟨hQ, hL⟩ := h
  refine IsRep.of_mul_eq (k := (w + x + 2 * y + 4 * z).sqrt) ?_ ?_
  · have hZ :
        (2 * ((w : ℤ) - 1) * ((w : ℤ) - 1) + ((x : ℤ) + 1) * ((x : ℤ) + 1)
          + (y : ℤ) * y + (z : ℤ) * z)
          = (n : ℤ) + 1 := by
      have hxrel : (x : ℤ) + 1 = 2 * (w : ℤ) := by exact_mod_cast hx
      have hQn : (2 * (w : ℤ) * w + (x : ℤ) * x + (y : ℤ) * y + (z : ℤ) * z)
          = (n : ℤ) := by exact_mod_cast hQ
      nlinarith
    have hw1 : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
    have : (2 * (w - 1) * (w - 1) + (x + 1) * (x + 1) + y * y + z * z : ℤ)
        = (n + 1 : ℤ) := by
      simpa [hw1, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hZ
    exact_mod_cast this
  · have : (w - 1) + (x + 1) + 2 * y + 4 * z = w + x + 2 * y + 4 * z := by omega
    simpa [this] using hL.symm

/-- Increment of type `(1, -1, 0, 0)` when `x = 2w + 1`. -/
lemma IsRep.inc_pos1_neg1 {n w x y z : ℕ} (h : IsRep n w x y z)
    (hx : x = 2 * w + 1) (hx0 : 1 ≤ x) :
    IsRep (n + 1) (w + 1) (x - 1) y z := by
  obtain ⟨hQ, hL⟩ := h
  refine IsRep.of_mul_eq (k := (w + x + 2 * y + 4 * z).sqrt) ?_ ?_
  · have hZ :
        (2 * ((w : ℤ) + 1) * ((w : ℤ) + 1) + ((x : ℤ) - 1) * ((x : ℤ) - 1)
          + (y : ℤ) * y + (z : ℤ) * z)
          = (n : ℤ) + 1 := by
      have hxrel : (x : ℤ) = 2 * (w : ℤ) + 1 := by exact_mod_cast hx
      have hQn : (2 * (w : ℤ) * w + (x : ℤ) * x + (y : ℤ) * y + (z : ℤ) * z)
          = (n : ℤ) := by exact_mod_cast hQ
      nlinarith
    have hx1 : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by omega
    have : (2 * (w + 1) * (w + 1) + (x - 1) * (x - 1) + y * y + z * z : ℤ)
        = (n + 1 : ℤ) := by
      simpa [hx1, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hZ
    exact_mod_cast this
  · have : (w + 1) + (x - 1) + 2 * y + 4 * z = w + x + 2 * y + 4 * z := by omega
    simpa [this] using hL.symm

lemma Q16_le_n_of_kMax (n : ℕ) :
    Q16 (kMax n) (16 * ((kMax n) : ℤ) ^ 2 / 43) ≤ (n : ℤ) + 42 := by
  have h := Q16_floor_vertex (kMax n)
  simp only at h
  have hk := (kMax_spec n).1
  have hr : (16 * ((kMax n) : ℤ) ^ 2 % 43) ^ 2 ≤ (42 : ℤ) ^ 2 := by
    have hlt : 16 * ((kMax n) : ℤ) ^ 2 % 43 < 43 :=
      Int.emod_lt_of_pos _ (by decide)
    have hnn : 0 ≤ 16 * ((kMax n) : ℤ) ^ 2 % 43 :=
      Int.emod_nonneg _ (by decide)
    have : 16 * ((kMax n) : ℤ) ^ 2 % 43 ≤ 42 := by omega
    nlinarith
  have : 43 * Q16 (kMax n) (16 * ((kMax n) : ℤ) ^ 2 / 43)
      ≤ 43 * (n : ℤ) + 42 * 42 := by
    have hcast : (2 * (kMax n) ^ 4 : ℤ) ≤ 43 * (n : ℤ) := by exact_mod_cast hk
    nlinarith [h, hcast, hr]
  nlinarith

/-- Remainder `n - Q16` at the vertex, as an integer. -/
def Mvertex (n : ℕ) : ℤ :=
  (n : ℤ) - Q16 (kMax n) (16 * ((kMax n) : ℤ) ^ 2 / 43)

lemma Mvertex_eq_shift (n : ℕ) (d : ℤ) :
    (n : ℤ) - Q16 (kMax n) (16 * ((kMax n) : ℤ) ^ 2 / 43 + d)
      = Mvertex n + 2 * (16 * ((kMax n) : ℤ) ^ 2 % 43) * d - 43 * d ^ 2 := by
  have h := Q16_shift_vertex (kMax n) d
  simp only at h
  simp [Mvertex, h]
  ring

lemma a_ge_two_of_ge_8700 (n : ℕ) (hn : 8700 ≤ n) : 2 ≤ a n := by
  have _hk20 := kMax_ge_twenty hn
  have _hQ := Q16_le_n_of_kMax n
  have _hM := Mvertex_eq_shift n 0
  sorry

lemma a_ge_two_of_ge_200 (n : ℕ) (hn : 200 ≤ n) : 2 ≤ a n := by
  if h0 : n < 8000 then
    exact a_ge_two_of_lt_8000 hn h0
  else if h1 : n < 8500 then
    exact a_ge_two_of_lt_8500 (by omega) h1
  else if h2 : n < 8700 then
    exact a_ge_two_of_lt_8700 (by omega) h2
  else
    exact a_ge_two_of_ge_8700 n (by omega)




lemma a_spec_of_lt_200 {n : ℕ} (hn : n < 200) :
    ((0 < a n) ↔ n ∉ A275409_zero_set) ∧
      ((a n = 1) ↔ n ∈ A275409_one_set) := by
  constructor
  · constructor
    · intro hpos hz
      have : a n = 0 := a_eq_zero_of_mem_zero hz
      omega
    · intro hz
      by_cases ho : n ∈ A275409_one_set
      · have : a n = 1 := a_eq_one_of_mem_one ho
        omega
      · have : 2 ≤ a n := a_ge_two_of_nonspecial hn hz ho
        omega
  · constructor
    · intro ha
      by_cases hz : n ∈ A275409_zero_set
      · have : a n = 0 := a_eq_zero_of_mem_zero hz
        omega
      · by_cases ho : n ∈ A275409_one_set
        · exact ho
        · have : 2 ≤ a n := a_ge_two_of_nonspecial hn hz ho
          omega
    · intro ho
      exact a_eq_one_of_mem_one ho

theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) := by
  constructor
  · intro n
    by_cases hN : n < 200
    · exact (a_spec_of_lt_200 hN).1
    · have hn : 200 ≤ n := Nat.le_of_not_lt hN
      have hpos : 0 < a n :=
        lt_of_lt_of_le (by decide : (0 : ℕ) < 2) (a_ge_two_of_ge_200 n hn)
      exact ⟨fun _ => not_mem_zero_of_ge_200 hn, fun _ => hpos⟩
  · intro n
    by_cases hN : n < 200
    · exact (a_spec_of_lt_200 hN).2
    · have hn : 200 ≤ n := Nat.le_of_not_lt hN
      have hne : a n ≠ 1 := by
        have : 2 ≤ a n := a_ge_two_of_ge_200 n hn
        omega
      exact ⟨fun h => (hne h).elim, fun h => (not_mem_one_of_ge_200 hn h).elim⟩
