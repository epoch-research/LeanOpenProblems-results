import Submission.Basic

/-!
# Binary-phase interpolation

Public interface for the pressure/repair development: `E74.phase_patch`.
It applies to an arbitrary vertex type (no finiteness or connectivity hypothesis):

```
phase_patch (G : SimpleGraph V) (b b' : V → Bool)
    (c' : G.Coloring (Fin 3)) (level : V → ℕ) (s : ℕ)
    (hs : 2 ≤ s)
    (hlevel : ∀ ⦃x y⦄, G.Adj x y →
      level x ≤ level y + 1 ∧ level y ≤ level x + 1)
    (hb : ∀ ⦃x y⦄, G.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) → b x ≠ b y)
    (hband : ∀ x, s - 2 ≤ level x → level x ≤ s + 6 →
      c' x = base (b' x)) :
    ∃ c : G.Coloring (Fin 3),
      (∀ x, level x ≤ s → c x = c' x) ∧
      (∀ x, s + 3 ≤ level x → c x = base (b x))
```

The height uses only walks of lengths zero, one, and two from flipped
interface vertices. Thus empty flipped sets and unreachable vertices need
no separate graph-metric convention. The four rows are `(0,1)`, `(2,1)`,
`(2,0)`, `(1,0)`, indexed by the old binary shore.
-/

namespace E74

open SimpleGraph

universe u
variable {V : Type u}

namespace Phase

/-- A vertex joined by one edge to the set `S`. -/
def nearOne (G : SimpleGraph V) (S : V → Prop) (x : V) : Prop :=
  ∃ y, S y ∧ G.Adj x y

/-- A vertex joined by a walk of length two to the set `S`. -/
def nearTwo (G : SimpleGraph V) (S : V → Prop) (x : V) : Prop :=
  ∃ y, nearOne G S y ∧ G.Adj x y

/-- Truncated distance height, defined by bounded-length walks. -/
noncomputable def height (G : SimpleGraph V) (S : V → Prop) (x : V) : ℕ := by
  classical
  exact if S x then 3 else if nearOne G S x then 2 else if nearTwo G S x then 1 else 0

theorem height_le_three (G : SimpleGraph V) (S : V → Prop) (x : V) :
    height G S x ≤ 3 := by
  classical
  unfold height
  split_ifs <;> omega

theorem height_of_mem (G : SimpleGraph V) (S : V → Prop) {x : V} (hx : S x) :
    height G S x = 3 := by
  classical
  simp [height, hx]

/-- The truncated height changes by at most one along an edge. -/
theorem height_step (G : SimpleGraph V) (S : V → Prop) {x y : V}
    (hxy : G.Adj x y) : height G S x ≤ height G S y + 1 := by
  classical
  by_cases hx : S x
  · have hy : nearOne G S y := ⟨x, hx, hxy.symm⟩
    simp only [height, if_pos hx]
    by_cases hyS : S y
    · simp [hyS]
    · simp [hyS, hy]
  · by_cases hx1 : nearOne G S x
    · have hy : nearTwo G S y := ⟨x, hx1, hxy.symm⟩
      simp only [height, if_neg hx, if_pos hx1]
      by_cases hyS : S y
      · simp [hyS]
      · by_cases hy1 : nearOne G S y
        · simp [hyS, hy1]
        · simp [hyS, hy1, hy]
    · have hh : height G S x ≤ 1 := by
        simp only [height, if_neg hx, if_neg hx1]
        split_ifs <;> omega
      omega

theorem height_lipschitz (G : SimpleGraph V) (S : V → Prop) {x y : V}
    (hxy : G.Adj x y) :
    height G S x ≤ height G S y + 1 ∧ height G S y ≤ height G S x + 1 :=
  ⟨height_step G S hxy, height_step G S hxy.symm⟩

/-- The interpolation table; only heights at most three will be used. -/
def table : ℕ → Bool → Fin 3
  | 0, false => 0
  | 0, true => 1
  | 1, false => 2
  | 1, true => 1
  | 2, false => 2
  | 2, true => 0
  | _, false => 1
  | _, true => 0

@[simp] theorem table_zero (a : Bool) : table 0 a = base a := by
  cases a <;> rfl

theorem table_three_of_ne (a a' : Bool) (ha : a' ≠ a) :
    table 3 a = base a' := by
  cases a <;> cases a' <;> simp_all [table, base]

/-- Same or consecutive rows are compatible in both shore orientations. -/
theorem table_ne (h k : ℕ) (a d : Bool) (had : a ≠ d)
    (hh : h ≤ 3) (hk : k ≤ 3) (hhk : h ≤ k + 1) (hkh : k ≤ h + 1) :
    table h a ≠ table k d := by
  interval_cases h <;> interval_cases k <;> cases a <;> cases d <;>
    norm_num [table] at * <;> decide

/-- Two proper binary cuts have the same flip status at adjacent vertices. -/
theorem bool_flip_iff (a a' d d' : Bool) (had : a ≠ d) (had' : a' ≠ d') :
    (a' ≠ a ↔ d' ≠ d) := by
  cases a <;> cases a' <;> cases d <;> cases d' <;> simp_all

/-- The flipped part of the level-`s` interface. -/
def flipped (b b' : V → Bool) (level : V → ℕ) (s : ℕ) (x : V) : Prop :=
  level x = s ∧ b' x ≠ b x

/-- Flip status is constant on every edge contained in the clean binary band. -/
theorem flip_iff_on_band (G : SimpleGraph V) (b b' : V → Bool)
    (c' : G.Coloring (Fin 3)) (level : V → ℕ) (s : ℕ)
    (hb : ∀ ⦃x y : V⦄, G.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) → b x ≠ b y)
    (hband : ∀ x, s - 2 ≤ level x → level x ≤ s + 6 → c' x = base (b' x))
    {x y : V} (hxy : G.Adj x y)
    (hxlo : s - 2 ≤ level x) (hxhi : level x ≤ s + 6)
    (hylo : s - 2 ≤ level y) (hyhi : level y ≤ s + 6) :
    (b' x ≠ b x ↔ b' y ≠ b y) := by
  apply bool_flip_iff _ _ _ _ (hb hxy (Or.inl hxlo))
  intro heq
  apply c'.valid hxy
  rw [hband x hxlo hxhi, hband y hylo hyhi, heq]

/-- A nonflipped interface vertex is not within two edges of a flipped one. -/
theorem interface_height_zero (G : SimpleGraph V) (b b' : V → Bool)
    (c' : G.Coloring (Fin 3)) (level : V → ℕ) (s : ℕ) (hs : 2 ≤ s)
    (hlevel : ∀ ⦃x y : V⦄, G.Adj x y →
      level x ≤ level y + 1 ∧ level y ≤ level x + 1)
    (hb : ∀ ⦃x y : V⦄, G.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) → b x ≠ b y)
    (hband : ∀ x, s - 2 ≤ level x → level x ≤ s + 6 → c' x = base (b' x))
    {x : V} (hx : level x = s) (hflip : ¬b' x ≠ b x) :
    height G (flipped b b' level s) x = 0 := by
  classical
  have hxlo : s - 2 ≤ level x := by omega
  have hxhi : level x ≤ s + 6 := by omega
  have hnS : ¬flipped b b' level s x := by
    rintro ⟨_, hf⟩
    exact hflip hf
  have hn1 : ¬nearOne G (flipped b b' level s) x := by
    rintro ⟨z, ⟨hz, hzf⟩, hxz⟩
    have hzlo : s - 2 ≤ level z := by omega
    have hzhi : level z ≤ s + 6 := by omega
    exact hflip ((flip_iff_on_band G b b' c' level s hb hband hxz
      hxlo hxhi hzlo hzhi).mpr hzf)
  have hn2 : ¬nearTwo G (flipped b b' level s) x := by
    rintro ⟨y, ⟨z, ⟨hz, hzf⟩, hyz⟩, hxy⟩
    have hyl := hlevel hxy
    have hylo : s - 2 ≤ level y := by omega
    have hyhi : level y ≤ s + 6 := by omega
    have hzlo : s - 2 ≤ level z := by omega
    have hzhi : level z ≤ s + 6 := by omega
    have hyf : b' y ≠ b y :=
      (flip_iff_on_band G b b' c' level s hb hband hyz hylo hyhi hzlo hzhi).mpr hzf
    exact hflip ((flip_iff_on_band G b b' c' level s hb hband hxy
      hxlo hxhi hylo hyhi).mpr hyf)
  simp [height, hnS, hn1, hn2]

/-- On the interface, the table exactly matches the retained coloring. -/
theorem interface_table (G : SimpleGraph V) (b b' : V → Bool)
    (c' : G.Coloring (Fin 3)) (level : V → ℕ) (s : ℕ) (hs : 2 ≤ s)
    (hlevel : ∀ ⦃x y : V⦄, G.Adj x y →
      level x ≤ level y + 1 ∧ level y ≤ level x + 1)
    (hb : ∀ ⦃x y : V⦄, G.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) → b x ≠ b y)
    (hband : ∀ x, s - 2 ≤ level x → level x ≤ s + 6 → c' x = base (b' x))
    {x : V} (hx : level x = s) :
    table (height G (flipped b b' level s) x) (b x) = c' x := by
  classical
  rw [hband x (by omega) (by omega)]
  by_cases hf : b' x ≠ b x
  · rw [height_of_mem G _ (show flipped b b' level s x from ⟨hx, hf⟩)]
    exact table_three_of_ne _ _ hf
  · rw [interface_height_zero G b b' c' level s hs hlevel hb hband hx hf]
    have heq : b' x = b x := by simpa using hf
    simp [heq]

/-- The truncated height has vanished by level `s + 3`. -/
theorem outer_height_zero (G : SimpleGraph V) (b b' : V → Bool)
    (level : V → ℕ) (s : ℕ)
    (hlevel : ∀ ⦃x y : V⦄, G.Adj x y →
      level x ≤ level y + 1 ∧ level y ≤ level x + 1)
    {x : V} (hx : s + 3 ≤ level x) :
    height G (flipped b b' level s) x = 0 := by
  classical
  have hnS : ¬flipped b b' level s x := by
    rintro ⟨hl, _⟩
    omega
  have hn1 : ¬nearOne G (flipped b b' level s) x := by
    rintro ⟨z, ⟨hz, _⟩, hxz⟩
    have := (hlevel hxz).1
    omega
  have hn2 : ¬nearTwo G (flipped b b' level s) x := by
    rintro ⟨y, ⟨z, ⟨hz, _⟩, hyz⟩, hxy⟩
    have := (hlevel hxy).1
    have := (hlevel hyz).1
    omega
  simp [height, hnS, hn1, hn2]

end Phase

/-- Interpolate two clean binary phases using three colors, retaining the
inner proper coloring and returning to the old cut outside level `s + 2`.
No finiteness, connectivity, or graph-distance assumptions are required. -/
theorem phase_patch (G : SimpleGraph V) (b b' : V → Bool)
    (c' : G.Coloring (Fin 3)) (level : V → ℕ) (s : ℕ) (hs : 2 ≤ s)
    (hlevel : ∀ ⦃x y : V⦄, G.Adj x y →
      level x ≤ level y + 1 ∧ level y ≤ level x + 1)
    (hb : ∀ ⦃x y : V⦄, G.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) → b x ≠ b y)
    (hband : ∀ x, s - 2 ≤ level x → level x ≤ s + 6 → c' x = base (b' x)) :
    ∃ c : G.Coloring (Fin 3),
      (∀ x, level x ≤ s → c x = c' x) ∧
      (∀ x, s + 3 ≤ level x → c x = base (b x)) := by
  classical
  let S := Phase.flipped b b' level s
  let f : V → Fin 3 := fun x =>
    if level x ≤ s then c' x else Phase.table (Phase.height G S x) (b x)
  have htable : ∀ ⦃x y : V⦄, G.Adj x y →
      (s - 2 ≤ level x ∨ s - 2 ≤ level y) →
      Phase.table (Phase.height G S x) (b x) ≠
        Phase.table (Phase.height G S y) (b y) := by
    intro x y hxy hgood
    have hstep := Phase.height_lipschitz G S hxy
    exact Phase.table_ne _ _ _ _ (hb hxy hgood)
      (Phase.height_le_three G S x) (Phase.height_le_three G S y) hstep.1 hstep.2
  have hinterface : ∀ x, level x = s →
      Phase.table (Phase.height G S x) (b x) = c' x := by
    intro x hx
    exact Phase.interface_table G b b' c' level s hs hlevel hb hband hx
  have hf : ∀ ⦃x y : V⦄, G.Adj x y → f x ≠ f y := by
    intro x y hxy
    have hl := hlevel hxy
    by_cases hx : level x ≤ s
    · by_cases hy : level y ≤ s
      · simpa only [f, if_pos hx, if_pos hy] using c'.valid hxy
      · have hxs : level x = s := by omega
        have ht := htable hxy (Or.inr (show s - 2 ≤ level y by omega))
        rw [hinterface x hxs] at ht
        simpa only [f, if_pos hx, if_neg hy] using ht
    · by_cases hy : level y ≤ s
      · have hys : level y = s := by omega
        have ht := htable hxy (Or.inl (show s - 2 ≤ level x by omega))
        rw [hinterface y hys] at ht
        simpa only [f, if_neg hx, if_pos hy] using ht
      · simpa only [f, if_neg hx, if_neg hy] using
          htable hxy (Or.inl (show s - 2 ≤ level x by omega))
  refine ⟨Coloring.mk f (fun {x y} hxy => hf hxy), ?_, ?_⟩
  · intro x hx
    change f x = c' x
    simp only [f, if_pos hx]
  · intro x hx
    change f x = base (b x)
    have hn : ¬level x ≤ s := by omega
    have hh : Phase.height G S x = 0 :=
      Phase.outer_height_zero G b b' level s hlevel hx
    simp only [f, if_neg hn, hh, Phase.table_zero]

end E74
