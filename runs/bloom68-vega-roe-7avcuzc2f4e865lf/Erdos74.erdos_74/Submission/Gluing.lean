import FormalConjecturesUtil

/-!
# Three-color gluing across a four-level annulus

This file is independent of `Submission.Spec`.  Vertices may have any type; no
finiteness or decidable-adjacency assumption is used.

`glue level a γ c c₁` retains `γ` at levels at most `a`, retains the Boolean
coloring `c` (embedded in `Fin 3`) at levels at least `a + 3`, and interpolates
on the two intervening levels.  When `c` and `c₁` differ, the four rows of the
interpolation, listed in the order `(c = false, c = true)`, are
`(1, 0), (2, 0), (2, 1), (0, 1)`.

The core theorem `glue_proper_of_xor` assumes that the XOR of the two Boolean
colorings is constant along edges in the closed band.  `glue_proper` derives
this condition from properness of both Boolean colorings there.
`exists_coloring` packages the result as a mathlib graph coloring, and
`exists_coloring_of_band` accepts the stronger full-band matching hypotheses.

The edge-level hypothesis is the oriented inequality `level u ≤ level v + 1`
for every edge.  By symmetry this is precisely the usual distance-at-most-one
condition; `level_step_of_dist` converts from a `Nat.dist` formulation.
There is no need to assume `1 ≤ a` once the exterior Boolean coloring is
assumed proper on all levels at least `a`.
-/

namespace Erdos74.AnnulusGluing

universe u

variable {V : Type u}

/-- Embed the two Boolean colors as colors `0` and `1` of `Fin 3`. -/
def boolColor : Bool → Fin 3
  | false => 0
  | true => 1

@[simp] theorem boolColor_false : boolColor false = 0 := rfl

@[simp] theorem boolColor_true : boolColor true = 1 := rfl

theorem boolColor_injective : Function.Injective boolColor := by decide

/-- The transition when the two Boolean colorings disagree.
Rows beyond the fourth have already reached the exterior coloring. -/
def swapRow (row : ℕ) (b : Bool) : Fin 3 :=
  if row = 0 then boolColor (!b)
  else if row = 1 then if b then 0 else 2
  else if row = 2 then if b then 1 else 2
  else boolColor b

/-- The color in the closed band: unchanged where the Boolean colorings agree,
and the four-row transition where they disagree. -/
def bandColor (row : ℕ) (b b₁ : Bool) : Fin 3 :=
  if b = b₁ then boolColor b else swapRow row b

@[simp] theorem bandColor_same (row : ℕ) (b : Bool) :
    bandColor row b b = boolColor b := by
  simp [bandColor]

@[simp] theorem bandColor_zero (b b₁ : Bool) :
    bandColor 0 b b₁ = boolColor b₁ := by
  cases b <;> cases b₁ <;> decide

theorem bandColor_of_three_le (row : ℕ) (b b₁ : Bool) (hrow : 3 ≤ row) :
    bandColor row b b₁ = boolColor b := by
  have h0 : row ≠ 0 := by omega
  have h1 : row ≠ 1 := by omega
  have h2 : row ≠ 2 := by omega
  simp [bandColor, swapRow, h0, h1, h2]

@[simp] theorem bandColor_three (b b₁ : Bool) :
    bandColor 3 b b₁ = boolColor b :=
  bandColor_of_three_le 3 b b₁ (by omega)

/-- Two proper Boolean colorings have the same XOR at the endpoints of an edge. -/
theorem xor_eq_of_ne {b d b₁ d₁ : Bool} (h : b ≠ d) (h₁ : b₁ ≠ d₁) :
    Bool.xor b b₁ = Bool.xor d d₁ := by
  cases b <;> cases d <;> cases b₁ <;> cases d₁ <;> simp_all

/-- The finite check behind the gluing argument. -/
private theorem bandColor_ne_finite :
    ∀ (i j : Fin 4) (b b₁ d d₁ : Bool),
      i.val ≤ j.val + 1 → j.val ≤ i.val + 1 →
      b ≠ d → Bool.xor b b₁ = Bool.xor d d₁ →
      bandColor i.val b b₁ ≠ bandColor j.val d d₁ := by
  decide

/-- Neighboring rows give distinct colors whenever the exterior colors differ
and the XOR is unchanged along the edge. -/
theorem bandColor_ne_of_xor {i j : ℕ} {b b₁ d d₁ : Bool}
    (hi : i ≤ 3) (hj : j ≤ 3)
    (hij : i ≤ j + 1) (hji : j ≤ i + 1)
    (h : b ≠ d) (hδ : Bool.xor b b₁ = Bool.xor d d₁) :
    bandColor i b b₁ ≠ bandColor j d d₁ :=
  bandColor_ne_finite ⟨i, by omega⟩ ⟨j, by omega⟩ b b₁ d d₁ hij hji h hδ

/-- A version of the row lemma using properness of both Boolean colorings. -/
theorem bandColor_ne {i j : ℕ} {b b₁ d d₁ : Bool}
    (hi : i ≤ 3) (hj : j ≤ 3)
    (hij : i ≤ j + 1) (hji : j ≤ i + 1)
    (h : b ≠ d) (h₁ : b₁ ≠ d₁) :
    bandColor i b b₁ ≠ bandColor j d d₁ :=
  bandColor_ne_of_xor hi hj hij hji h (xor_eq_of_ne h h₁)

/-- The explicit global coloring.  Its inner and outer agreement properties
hold without any graph-theoretic assumptions. -/
def glue (level : V → ℕ) (a : ℕ) (γ : V → Fin 3) (c c₁ : V → Bool)
    (v : V) : Fin 3 :=
  if level v ≤ a then γ v
  else if a + 3 ≤ level v then boolColor (c v)
  else bandColor (level v - a) (c v) (c₁ v)

variable {G : SimpleGraph V} {level : V → ℕ} {a : ℕ}
  {γ : V → Fin 3} {c c₁ : V → Bool}

theorem glue_eq_inner {v : V} (hv : level v ≤ a) :
    glue level a γ c c₁ v = γ v := by
  simp [glue, hv]

theorem glue_eq_outer {v : V} (hv : a + 3 ≤ level v) :
    glue level a γ c c₁ v = boolColor (c v) := by
  have hinner : ¬ level v ≤ a := by omega
  simp [glue, hinner, hv]

/-- Once the lower boundary matches, the formula for the band also describes
all vertices on or beyond that boundary. -/
theorem glue_eq_band
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v))
    {v : V} (hv : a ≤ level v) :
    glue level a γ c c₁ v = bandColor (level v - a) (c v) (c₁ v) := by
  by_cases hinner : level v ≤ a
  · have heq : level v = a := by omega
    rw [glue_eq_inner hinner, hmatch v heq, heq, Nat.sub_self, bandColor_zero]
  · unfold glue
    rw [if_neg hinner]
    split_ifs with houter
    · exact (bandColor_of_three_le _ _ _ (by omega)).symm
    · rfl

/-- Convert the natural-number absolute-distance bound to the oriented
edge-level hypothesis used below.  The reverse inequality follows by applying
this hypothesis to the reverse edge. -/
theorem level_step_of_dist
    (hlevel : ∀ {u v : V}, G.Adj u v → Nat.dist (level u) (level v) ≤ 1) :
    ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1 := by
  intro u v huv
  have h := hlevel huv
  unfold Nat.dist at h
  omega

/-- Core gluing lemma.  Only the level-`a` boundary needs to match the inner
coloring, and the inner coloring only needs to be proper through level `a`.
The Boolean coloring must be proper on the exterior, including this boundary.
The XOR condition is only needed on edges entirely in the closed four-level
band `[a, a + 3]`. -/
theorem glue_proper_of_xor
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v → level u ≤ a → level v ≤ a → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hδ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      Bool.xor (c u) (c₁ u) = Bool.xor (c v) (c₁ v))
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v)) :
    ∀ {u v : V}, G.Adj u v →
      glue level a γ c c₁ u ≠ glue level a γ c c₁ v := by
  have ordered : ∀ {u v : V}, G.Adj u v → level u ≤ level v →
      glue level a γ c c₁ u ≠ glue level a γ c c₁ v := by
    intro u v huv huv_level
    have hstep := hlevel huv.symm
    by_cases hv : level v ≤ a
    · have hu : level u ≤ a := le_trans huv_level hv
      rw [glue_eq_inner hu, glue_eq_inner hv]
      exact hγ huv hu hv
    by_cases hu : a + 3 ≤ level u
    · have hv : a + 3 ≤ level v := le_trans hu huv_level
      rw [glue_eq_outer hu, glue_eq_outer hv]
      exact boolColor_injective.ne (hc huv (by omega) (by omega))
    have hulo : a ≤ level u := by omega
    have hvlo : a ≤ level v := by omega
    have huhi : level u ≤ a + 3 := by omega
    have hvhi : level v ≤ a + 3 := by omega
    rw [glue_eq_band hmatch hulo, glue_eq_band hmatch hvlo]
    exact bandColor_ne_of_xor (by omega) (by omega) (by omega) (by omega)
      (hc huv hulo hvlo) (hδ huv hulo huhi hvlo hvhi)
  intro u v huv
  rcases le_total (level u) (level v) with h | h
  · exact ordered huv h
  · exact (ordered huv.symm h).symm

/-- Gluing from two proper Boolean colorings.  No separate hypothesis about
XORs or connected components of the band is necessary. -/
theorem glue_proper
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v → level u ≤ a → level v ≤ a → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hc₁ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      c₁ u ≠ c₁ v)
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v)) :
    ∀ {u v : V}, G.Adj u v →
      glue level a γ c c₁ u ≠ glue level a γ c c₁ v := by
  intro u v huv
  apply glue_proper_of_xor hlevel hγ hc ?_ hmatch huv
  intro x y hxy hxlo hxhi hylo hyhi
  exact xor_eq_of_ne (hc hxy hxlo hylo) (hc₁ hxy hxlo hxhi hylo hyhi)

/-- A proper mathlib three-coloring with prescribed inner and outer colors.
This form uses only properness through level `a` and matching at level `a`. -/
theorem exists_coloring
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v → level u ≤ a → level v ≤ a → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hc₁ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      c₁ u ≠ c₁ v)
    (hmatch : ∀ v, level v = a → γ v = boolColor (c₁ v)) :
    ∃ C : G.Coloring (Fin 3),
      (∀ v, level v ≤ a → C v = γ v) ∧
      (∀ v, a + 3 ≤ level v → C v = boolColor (c v)) := by
  let C : G.Coloring (Fin 3) := SimpleGraph.Coloring.mk
    (glue level a γ c c₁) (fun {u v} huv => glue_proper hlevel hγ hc hc₁ hmatch huv)
  refine ⟨C, ?_, ?_⟩
  · intro v hv
    change glue level a γ c c₁ v = γ v
    exact glue_eq_inner hv
  · intro v hv
    change glue level a γ c c₁ v = boolColor (c v)
    exact glue_eq_outer hv

/-- Convenience form with the original full-band hypotheses: `γ` is proper
through level `a + 3` and agrees with the embedded `c₁` throughout the band.
The XOR condition follows automatically, so is not an extra argument. -/
theorem exists_coloring_of_band
    (hlevel : ∀ {u v : V}, G.Adj u v → level u ≤ level v + 1)
    (hγ : ∀ {u v : V}, G.Adj u v →
      level u ≤ a + 3 → level v ≤ a + 3 → γ u ≠ γ v)
    (hc : ∀ {u v : V}, G.Adj u v → a ≤ level u → a ≤ level v → c u ≠ c v)
    (hc₁ : ∀ {u v : V}, G.Adj u v →
      a ≤ level u → level u ≤ a + 3 → a ≤ level v → level v ≤ a + 3 →
      c₁ u ≠ c₁ v)
    (hmatch : ∀ v, a ≤ level v → level v ≤ a + 3 → γ v = boolColor (c₁ v)) :
    ∃ C : G.Coloring (Fin 3),
      (∀ v, level v ≤ a → C v = γ v) ∧
      (∀ v, a + 3 ≤ level v → C v = boolColor (c v)) := by
  apply exists_coloring hlevel ?_ hc hc₁ ?_
  · intro u v huv hu hv
    exact hγ huv (by omega) (by omega)
  · intro v hv
    exact hmatch v (by omega) (by omega)

end Erdos74.AnnulusGluing
