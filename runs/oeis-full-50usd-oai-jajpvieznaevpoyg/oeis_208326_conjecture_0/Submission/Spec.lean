import FormalConjectures.Util.ProblemImports

open Real

/--
A208326: $c(n) = n + \lfloor nr/t \rfloor + \lfloor ns/t \rfloor$, where $\lfloor \cdot \rfloor$ is the floor function, $r=5$, $s=(1+\sqrt{5})/2$, and $t=1/s$.
-/
noncomputable def A208326 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / t)
  let term2_int : ℤ := Int.floor (n_r * s / t)

  -- Sum the components in ℤ and convert the final result back to ℕ.
  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A207672: $a(n) = n + \lfloor ns/r \rfloor + \lfloor nt/r \rfloor$.
-/
noncomputable def A207672 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * s / r)
  let term2_int : ℤ := Int.floor (n_r * t / r)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

/--
A207673: $b(n) = n + \lfloor nr/s \rfloor + \lfloor nt/s \rfloor$.
-/
noncomputable def A207673 (n : ℕ) : ℕ :=
  let r : ℝ := 5
  let s : ℝ := goldenRatio
  let t : ℝ := 1 / s
  let n_r : ℝ := n

  let term1_int : ℤ := Int.floor (n_r * r / s)
  let term2_int : ℤ := Int.floor (n_r * t / s)

  let result_int : ℤ := n.cast + term1_int + term2_int
  result_int.toNat

open scoped goldenRatio

inductive Ev where | A : ℕ → Ev | B : ℕ → Ev | C : ℕ → Ev deriving DecidableEq

lemma nat_lt_floor_iff {a : ℝ} (ha : 0 ≤ a) (i : ℕ) : i < ⌊a⌋₊ ↔ ((i+1:ℕ) : ℝ) ≤ a := by
  rw [← Nat.succ_le_iff]
  constructor
  · intro h
    exact le_trans (by exact_mod_cast h) (Nat.floor_le ha)
  · intro h
    exact Nat.le_floor h

example {a : ℝ} (ha : 0 ≤ a) (i : ℕ) : i < ⌊a⌋₊ ↔ ((Nat.succ i:ℕ) : ℝ) ≤ a := by
  simpa [Nat.succ_eq_add_one] using nat_lt_floor_iff ha i

noncomputable abbrev x : ℝ := φ / 5
noncomputable abbrev y : ℝ := (1 / φ) / 5
noncomputable def tm : Ev → ℝ
| Ev.A i => (i.succ : ℝ)
| Ev.B i => (i.succ : ℝ) / x
| Ev.C i => (i.succ : ℝ) / y

noncomputable def evBelow (T : ℝ) : Finset Ev :=
  ((Finset.range ⌊T⌋₊).image Ev.A) ∪
  ((Finset.range ⌊T*x⌋₊).image Ev.B) ∪
  ((Finset.range ⌊T*y⌋₊).image Ev.C)

lemma mem_evBelow {T : ℝ} (hT : 0 ≤ T) (hx : 0 < x) (hy : 0 < y) (e : Ev) :
    e ∈ evBelow T ↔ tm e ≤ T := by
  cases e with
  | A i =>
      simp [evBelow, tm, nat_lt_floor_iff hT]
  | B i =>
      have hTx : 0 ≤ T*x := mul_nonneg hT hx.le
      simp [evBelow, tm, nat_lt_floor_iff hTx, div_le_iff₀ hx]
  | C i =>
      have hTy : 0 ≤ T*y := mul_nonneg hT hy.le
      simp [evBelow, tm, nat_lt_floor_iff hTy, div_le_iff₀ hy]

noncomputable def rnk (T : ℝ) : ℕ := ⌊T⌋₊ + ⌊T*x⌋₊ + ⌊T*y⌋₊



lemma card_evBelow (T : ℝ) : (evBelow T).card = rnk T := by
  let SA : Finset Ev := (Finset.range ⌊T⌋₊).image Ev.A
  let SB : Finset Ev := (Finset.range ⌊T*x⌋₊).image Ev.B
  let SC : Finset Ev := (Finset.range ⌊T*y⌋₊).image Ev.C
  change ((SA ∪ SB) ∪ SC).card = _
  have hAB : Disjoint SA SB := by
    simp [SA, SB, Finset.disjoint_left]
  have hAC : Disjoint SA SC := by
    simp [SA, SC, Finset.disjoint_left]
  have hBC : Disjoint SB SC := by
    simp [SB, SC, Finset.disjoint_left]
  have hAB_C : Disjoint (SA ∪ SB) SC := hAC.sup_left hBC
  rw [Finset.card_union_of_disjoint hAB_C, Finset.card_union_of_disjoint hAB]
  rw [Finset.card_image_of_injective _ (by intro a b h; cases h; rfl),
      Finset.card_image_of_injective _ (by intro a b h; cases h; rfl),
      Finset.card_image_of_injective _ (by intro a b h; cases h; rfl)]
  simp [rnk, Nat.add_assoc]

lemma x_pos : 0 < x := by
  dsimp [x]
  positivity
lemma y_pos : 0 < y := by
  dsimp [y]
  positivity
lemma x_lt_one : x < 1 := by
  dsimp [x]
  have := Real.goldenRatio_lt_two
  nlinarith
lemma y_lt_one : y < 1 := by
  dsimp [y]
  have hp : 0 < φ := Real.goldenRatio_pos
  have hinv : (1 / φ : ℝ) < 1 := by
    simpa [one_div] using inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  nlinarith
lemma x_irr : Irrational x := by
  dsimp [x]
  simpa using Real.goldenRatio_irrational.div_natCast (by norm_num : (5:ℕ) ≠ 0)
lemma y_irr : Irrational y := by
  dsimp [y]
  have hi : Irrational φ⁻¹ := Real.goldenRatio_irrational.inv
  simpa [one_div] using hi.div_natCast (by norm_num : (5:ℕ) ≠ 0)

lemma time_A_B_ne (i j : ℕ) : tm (Ev.A i) ≠ tm (Ev.B j) := by
  intro h
  have hm : ((i.succ : ℝ) * x) = (j.succ : ℝ) := by
    dsimp [tm] at h
    rw [h]
    field_simp [ne_of_gt x_pos]
  have hirr : Irrational ((i.succ : ℝ) * x) := by
    simpa [mul_comm] using x_irr.natCast_mul (Nat.succ_ne_zero i)
  exact hirr.ne_nat j.succ hm

lemma time_A_C_ne (i j : ℕ) : tm (Ev.A i) ≠ tm (Ev.C j) := by
  intro h
  have hm : ((i.succ : ℝ) * y) = (j.succ : ℝ) := by
    dsimp [tm] at h
    rw [h]
    field_simp [ne_of_gt y_pos]
  have hirr : Irrational ((i.succ : ℝ) * y) := by
    simpa [mul_comm] using y_irr.natCast_mul (Nat.succ_ne_zero i)
  exact hirr.ne_nat j.succ hm

lemma xy_ratio_irr : Irrational (y / x) := by
  dsimp [x, y]
  have hi : Irrational (φ⁻¹ / φ) := by
    -- = φ⁻2, irrational because inverse of φ^2
    have hsq : Irrational (φ^2) := by
      rw [Real.goldenRatio_sq]
      simpa using Real.goldenRatio_irrational.add_natCast 1
    have hsqinv : Irrational ((φ^2)⁻¹) := hsq.inv
    convert hsqinv using 1; field_simp [ne_of_gt Real.goldenRatio_pos]
  convert hi using 1; field_simp [ne_of_gt Real.goldenRatio_pos]

lemma time_B_C_ne (i j : ℕ) : tm (Ev.B i) ≠ tm (Ev.C j) := by
  intro h
  have hm : ((i.succ : ℝ) * (y / x)) = (j.succ : ℝ) := by
    dsimp [tm] at h
    have hxne : x ≠ 0 := ne_of_gt x_pos
    have hyne : y ≠ 0 := ne_of_gt y_pos
    field_simp [hxne, hyne] at h ⊢
    nlinarith
  have hirr : Irrational ((i.succ : ℝ) * (y / x)) := by
    simpa [mul_comm] using xy_ratio_irr.natCast_mul (Nat.succ_ne_zero i)
  exact hirr.ne_nat j.succ hm

lemma tm_inj : Function.Injective tm := by
  intro e f h
  cases e with
  | A i =>
    cases f with
    | A j =>
      dsimp [tm] at h
      exact congrArg Ev.A (Nat.succ.inj (Nat.cast_injective h))
    | B j => exact (time_A_B_ne i j h).elim
    | C j => exact (time_A_C_ne i j h).elim
  | B i =>
    cases f with
    | A j => exact (time_A_B_ne j i h.symm).elim
    | B j =>
      dsimp [tm] at h
      have hxne : x ≠ 0 := ne_of_gt x_pos
      field_simp [hxne] at h
      exact congrArg Ev.B (Nat.succ.inj (Nat.cast_injective h))
    | C j => exact (time_B_C_ne i j h).elim
  | C i =>
    cases f with
    | A j => exact (time_A_C_ne j i h.symm).elim
    | B j => exact (time_B_C_ne j i h.symm).elim
    | C j =>
      dsimp [tm] at h
      have hyne : y ≠ 0 := ne_of_gt y_pos
      field_simp [hyne] at h
      exact congrArg Ev.C (Nat.succ.inj (Nat.cast_injective h))

lemma tm_pos (e : Ev) : 0 < tm e := by
  cases e <;> dsimp [tm] <;> positivity

lemma evBelow_subset_of_le {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T) :
    evBelow S ⊆ evBelow T := by
  intro e he
  rw [mem_evBelow hT x_pos y_pos]
  exact (mem_evBelow hS x_pos y_pos e).1 he |>.trans hST

lemma rank_lt_of_time_lt {e f : Ev} (h : tm e < tm f) : rnk (tm e) < rnk (tm f) := by
  have hse : evBelow (tm e) ⊂ evBelow (tm f) := by
    constructor
    · exact evBelow_subset_of_le (tm_pos e).le (tm_pos f).le h.le
    · intro hsub
      have hfmem : f ∈ evBelow (tm f) := by
        rw [mem_evBelow (tm_pos f).le x_pos y_pos]
      have hfmem2 := hsub hfmem
      have : tm f ≤ tm e := (mem_evBelow (tm_pos e).le x_pos y_pos f).1 hfmem2
      linarith
  have hc := Finset.card_lt_card hse
  simpa [card_evBelow] using hc

lemma rank_ne_of_ne {e f : Ev} (hef : e ≠ f) : rnk (tm e) ≠ rnk (tm f) := by
  intro h
  have htne : tm e ≠ tm f := fun ht => hef (tm_inj ht)
  rcases lt_or_gt_of_ne htne with hlt | hgt
  · exact ne_of_lt (rank_lt_of_time_lt hlt) h
  · exact ne_of_gt (rank_lt_of_time_lt hgt) h

lemma exists_next (e : Ev) : ∃ f : Ev, tm e < tm f ∧ ∀ g : Ev, tm e < tm g → tm f ≤ tm g := by
  let B : ℝ := (⌊tm e⌋₊ + 1 : ℕ)
  let cand : Finset Ev := (evBelow B).filter (fun f => tm e < tm f)
  have hBnonneg : 0 ≤ B := by positivity
  have hA_mem : Ev.A ⌊tm e⌋₊ ∈ cand := by
    dsimp [cand]
    rw [Finset.mem_filter]
    constructor
    · rw [mem_evBelow hBnonneg x_pos y_pos]
      dsimp [tm, B]
      norm_num
    · simpa [tm, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (tm e)
  have hne : cand.Nonempty := ⟨_, hA_mem⟩
  rcases Finset.exists_min_image cand tm hne with ⟨f, hfmem, hmin⟩
  refine ⟨f, ?_, ?_⟩
  · exact (Finset.mem_filter.1 hfmem).2
  · intro g hg
    by_cases hgb : tm g ≤ B
    · exact hmin g (Finset.mem_filter.2 ⟨(mem_evBelow hBnonneg x_pos y_pos g).2 hgb, hg⟩)
    · have hBlt : B < tm g := lt_of_not_ge hgb
      have hfB : tm f ≤ B := by
        exact (mem_evBelow hBnonneg x_pos y_pos f).1 (Finset.mem_filter.1 hfmem).1
      linarith

lemma rank_next {e f : Ev} (hef : tm e < tm f) (hmin : ∀ g : Ev, tm e < tm g → tm f ≤ tm g) :
    rnk (tm f) = rnk (tm e) + 1 := by
  have hposE := (tm_pos e).le
  have hposF := (tm_pos f).le
  have hsub : evBelow (tm e) ⊆ evBelow (tm f) := evBelow_subset_of_le hposE hposF hef.le
  have hfmemF : f ∈ evBelow (tm f) := by rw [mem_evBelow hposF x_pos y_pos]
  have hfnotE : f ∉ evBelow (tm e) := by
    intro hfE
    have : tm f ≤ tm e := (mem_evBelow hposE x_pos y_pos f).1 hfE
    linarith
  have h_eq : evBelow (tm f) = insert f (evBelow (tm e)) := by
    ext g
    constructor
    · intro hgF
      by_cases hge : tm g ≤ tm e
      · exact Finset.mem_insert.2 (.inr ((mem_evBelow hposE x_pos y_pos g).2 hge))
      · have heg : tm e < tm g := lt_of_not_ge hge
        have hfg : tm f ≤ tm g := hmin g heg
        have hgf : tm g ≤ tm f := (mem_evBelow hposF x_pos y_pos g).1 hgF
        have ht : tm g = tm f := le_antisymm hgf hfg
        exact Finset.mem_insert.2 (.inl (tm_inj ht))
    · intro hg
      rcases Finset.mem_insert.1 hg with rfl | hgE
      · exact hfmemF
      · exact hsub hgE
  have hc : (evBelow (tm f)).card = (evBelow (tm e)).card + 1 := by
    rw [h_eq, Finset.card_insert_of_notMem hfnotE]
  simpa [card_evBelow] using hc

lemma exists_event_rank : ∀ n : ℕ, ∃ e : Ev, rnk (tm e) = n.succ
| 0 => by
    refine ⟨Ev.A 0, ?_⟩
    dsimp [rnk, tm]
    have hx0 : ⌊(x:ℝ)⌋₊ = 0 := by
      rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ x)]
      constructor <;> norm_num [x_pos.le, x_lt_one]
    have hy0 : ⌊(y:ℝ)⌋₊ = 0 := by
      rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ y)]
      constructor <;> norm_num [y_pos.le, y_lt_one]
    simp [hx0, hy0]
| n+1 => by
    rcases exists_event_rank n with ⟨e, he⟩
    rcases exists_next e with ⟨f, hef, hmin⟩
    refine ⟨f, ?_⟩
    rw [rank_next hef hmin, he]

lemma intFloorSum_toNat (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((n : ℤ) + ⌊a⌋ + ⌊b⌋).toNat = n + ⌊a⌋₊ + ⌊b⌋₊ := by
  have hfa : 0 ≤ ⌊a⌋ := Int.floor_nonneg.2 ha
  have hfb : 0 ≤ ⌊b⌋ := Int.floor_nonneg.2 hb
  rw [Int.toNat_add (add_nonneg (by exact_mod_cast (Nat.zero_le n)) hfa) hfb]
  rw [Int.toNat_add (by exact_mod_cast (Nat.zero_le n)) hfa]
  simp [Int.floor_toNat, Nat.add_assoc]

lemma intFloorSum_toNat_of_nonneg {z : ℤ} {a b : ℝ} (hz : 0 ≤ z) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (z + ⌊a⌋ + ⌊b⌋).toNat = z.toNat + ⌊a⌋₊ + ⌊b⌋₊ := by
  have hfa : 0 ≤ ⌊a⌋ := Int.floor_nonneg.2 ha
  have hfb : 0 ≤ ⌊b⌋ := Int.floor_nonneg.2 hb
  rw [Int.toNat_add (add_nonneg hz hfa) hfb]
  rw [Int.toNat_add hz hfa]
  simp [Int.floor_toNat, Nat.add_assoc]

lemma seqA_rank (i : ℕ) : A207672 i.succ = rnk (tm (Ev.A i)) := by
  dsimp [A207672, rnk, tm, x, y]
  rw [intFloorSum_toNat_of_nonneg]
  · have hz : (↑i + 1 : ℤ).toNat = i + 1 := by omega
    rw [hz, Nat.floor_natCast]
    ring_nf
  · positivity
  · positivity
  · positivity

lemma seqB_rank (i : ℕ) : A207673 i.succ = rnk (tm (Ev.B i)) := by
  dsimp [A207673, rnk, tm, x, y]
  rw [intFloorSum_toNat_of_nonneg]
  · have hz : (↑i + 1 : ℤ).toNat = i + 1 := by omega
    rw [hz]
    have h1 : ⌊(((i+1:ℕ):ℝ)) / (φ / 5)⌋₊ = ⌊(((i+1:ℕ):ℝ)) * 5 / φ⌋₊ := by
      congr 1
      field_simp [ne_of_gt Real.goldenRatio_pos]
    have h2 : ⌊(((i+1:ℕ):ℝ)) / (φ / 5) * (φ / 5)⌋₊ = i + 1 := by
      rw [show (((i+1:ℕ):ℝ)) / (φ / 5) * (φ / 5) = (((i+1:ℕ):ℝ)) by
        field_simp [ne_of_gt Real.goldenRatio_pos]]
      exact Nat.floor_natCast (i+1)
    have h3 : ⌊(((i+1:ℕ):ℝ)) / (φ / 5) * (1 / φ / 5)⌋₊ = ⌊(((i+1:ℕ):ℝ)) * (1 / φ) / φ⌋₊ := by
      congr 1
      field_simp [ne_of_gt Real.goldenRatio_pos]
    rw [h1, h2, h3]
    omega
  · positivity
  · positivity
  · positivity

lemma seqC_rank (i : ℕ) : A208326 i.succ = rnk (tm (Ev.C i)) := by
  dsimp [A208326, rnk, tm, x, y]
  rw [intFloorSum_toNat_of_nonneg]
  · have hz : (↑i + 1 : ℤ).toNat = i + 1 := by omega
    rw [hz]
    have h1 : ⌊(((i+1:ℕ):ℝ)) / (1 / φ / 5)⌋₊ = ⌊(((i+1:ℕ):ℝ)) * 5 / (1 / φ)⌋₊ := by
      congr 1
      field_simp [ne_of_gt Real.goldenRatio_pos]
    have h2 : ⌊(((i+1:ℕ):ℝ)) / (1 / φ / 5) * (φ / 5)⌋₊ = ⌊(((i+1:ℕ):ℝ)) * φ / (1 / φ)⌋₊ := by
      congr 1
      field_simp [ne_of_gt Real.goldenRatio_pos]
    have h3 : ⌊(((i+1:ℕ):ℝ)) / (1 / φ / 5) * (1 / φ / 5)⌋₊ = i + 1 := by
      rw [show (((i+1:ℕ):ℝ)) / (1 / φ / 5) * (1 / φ / 5) = (((i+1:ℕ):ℝ)) by
        field_simp [ne_of_gt Real.goldenRatio_pos]]
      exact Nat.floor_natCast (i+1)
    rw [h1, h2, h3]
    omega
  · positivity
  · positivity
  · positivity


lemma ev_rank_pos (e : Ev) : 0 < rnk (tm e) := by
  have hmem : e ∈ evBelow (tm e) := by
    rw [mem_evBelow (tm_pos e).le x_pos y_pos]
  have : 0 < (evBelow (tm e)).card := Finset.card_pos.2 ⟨e, hmem⟩
  simpa [card_evBelow] using this

lemma event_rank_mem (e : Ev) : rnk (tm e) ∈
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) := by
  cases e with
  | A i =>
      left; left
      exact ⟨i, by simp [seqA_rank]⟩
  | B i =>
      left; right
      exact ⟨i, by simp [seqB_rank]⟩
  | C i =>
      right
      exact ⟨i, by simp [seqC_rank]⟩

lemma range_pos_A {n : ℕ} (hn : n ∈ Set.range (A207672 ∘ Nat.succ)) : 0 < n := by
  rcases hn with ⟨i, rfl⟩
  rw [Function.comp_apply, seqA_rank]
  exact ev_rank_pos (Ev.A i)
lemma range_pos_B {n : ℕ} (hn : n ∈ Set.range (A207673 ∘ Nat.succ)) : 0 < n := by
  rcases hn with ⟨i, rfl⟩
  rw [Function.comp_apply, seqB_rank]
  exact ev_rank_pos (Ev.B i)
lemma range_pos_C {n : ℕ} (hn : n ∈ Set.range (A208326 ∘ Nat.succ)) : 0 < n := by
  rcases hn with ⟨i, rfl⟩
  rw [Function.comp_apply, seqC_rank]
  exact ev_rank_pos (Ev.C i)

lemma disj_AB : Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = (∅ : Set ℕ) := by
  ext n; constructor
  · intro h
    rcases h with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [← hi] at hj
    simp [Function.comp_apply, seqA_rank, seqB_rank] at hj
    exact (rank_ne_of_ne (by intro h; cases h) hj.symm).elim
  · simp
lemma disj_AC : Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = (∅ : Set ℕ) := by
  ext n; constructor
  · intro h
    rcases h with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [← hi] at hj
    simp [Function.comp_apply, seqA_rank, seqC_rank] at hj
    exact (rank_ne_of_ne (by intro h; cases h) hj.symm).elim
  · simp
lemma disj_BC : Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = (∅ : Set ℕ) := by
  ext n; constructor
  · intro h
    rcases h with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [← hi] at hj
    simp [Function.comp_apply, seqB_rank, seqC_rank] at hj
    exact (rank_ne_of_ne (by intro h; cases h) hj.symm).elim
  · simp

/--
oeis_208326_conjecture_0: %C A208326 The sequences A207672, A207673, and A208326 partition the positive integers.
-/
theorem oeis_208326_conjecture_0 :
  ({n : ℕ | 0 < n} : Set ℕ) =
    (Set.range (A207672 ∘ Nat.succ)) ∪
    (Set.range (A207673 ∘ Nat.succ)) ∪
    (Set.range (A208326 ∘ Nat.succ)) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A207673 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207672 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅) ∧
  (Set.range (A207673 ∘ Nat.succ) ∩ Set.range (A208326 ∘ Nat.succ) = ∅)
  := by
  constructor
  · ext n; constructor
    · intro hn
      rcases n with _ | k
      · cases hn
      · rcases exists_event_rank k with ⟨e, he⟩
        have hm := event_rank_mem e
        simpa [he] using hm
    · intro hn
      rcases hn with hnAB | hnC
      · rcases hnAB with hnA | hnB
        · exact range_pos_A hnA
        · exact range_pos_B hnB
      · exact range_pos_C hnC
  · exact ⟨disj_AB, disj_AC, disj_BC⟩
