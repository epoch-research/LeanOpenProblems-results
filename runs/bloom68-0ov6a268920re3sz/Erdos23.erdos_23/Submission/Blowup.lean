import Mathlib

/-!
# Blow-ups of a "skeleton" graph and the `Erdos23` bipartization problem

This file is self-contained (it only imports `Mathlib`) and does **not** depend on
`Submission.Spec`.

## Data

A *skeleton* consists of
* `k : ℕ`, the number of classes,
* `A : Fin k → Fin k → Bool`, a symmetric, irreflexive, triangle-free adjacency relation
  (hypotheses `hsymm`, `hirr`, `htf`),
* `m : Fin k → ℕ`, the class sizes.

Its *blow-up* is the graph on `Σ i : Fin k, Fin (m i)` in which `(i, a)` and `(j, b)` are adjacent
iff `A i j = true` (so every class is an independent set); see `SkeletonBlowup.blowup`.
It is triangle-free and has `∑ i, m i` vertices.

For a class-level 2-colouring `c : Fin k → Bool` define

* `monoS A m c = ∑ i, ∑ j, if A i j ∧ c i = c j then m i * m j else 0`
  (ordered sum: every monochromatic edge is counted twice),
* `monoW A m c = monoS A m c / 2` (the number of monochromatic edges of the blow-up when every
  vertex gets the colour of its class; the division is exact because `monoS` is even for symmetric
  irreflexive `A`, but this fact is never needed).

## Main results

* `skeleton_not_erdos23_bound`: if `B < monoW A m c` for every `c : Fin k → Bool`, then the blow-up
  `G` is triangle-free on `∑ m i` vertices and every bipartite `H ≤ G` misses more than `B` edges
  of `G`, i.e. `B < (G.edgeFinset \ H.edgeFinset).card`.
  The proof shows that the minimum, over *all* vertex 2-colourings, of the number of
  monochromatic edges is attained at a colouring that is constant on every class: that number is
  a multi-affine function of the class "imbalances" `s_i = #true - #false` because `A i i = false`.
* `skeleton_disproof`: if `∑ m i = 5 * n` and `n ^ 2 < monoW A m c` for all `c`, then the statement
  of `Erdos23.erdos_23` is false.  Its conclusion is syntactically the negation of the type of
  `Erdos23.erdos_23` (checked against `Submission.Spec`), so
  `theorem Erdos23.erdos_23.disproof : ¬ (type_of% @Erdos23.erdos_23) := skeleton_disproof k n A m ..`
  works.
* `skeleton_disproof_ordered`: the same with the hypothesis `2 * n ^ 2 < monoS A m c`.
* `skeleton_disproof_check` / `skeleton_not_erdos23_bound_check`: the same, but the finite
  hypothesis on all `2 ^ k` colourings is replaced by `SkeletonBlowup.cutCheck A m (2 * n ^ 2) = true`,
  a branch-and-bound search that is much faster than enumerating all colourings.

## How to instantiate

`hsymm`, `hirr`, `htf`, `hsum` are `decide`-able (use `decide +kernel` when `k` is large: this
only uses the kernel's evaluator, no extra axioms).  `hcut` is `decide`-able for tiny `k` (the
pentagon, `k = 5`, works with plain `decide`; `decide +kernel` copes with `k ≈ 9`).  For larger `k`
use `skeleton_disproof_check` and prove `SkeletonBlowup.cutCheck A m (2 * n ^ 2) = true` by
`decide +kernel` (hard instances with `k ≈ 20` take seconds, `k ≈ 30` about a minute).  Recommended data format:
`A i j := Nat.testBit M (i.val * k + j.val)` with `M = ∑_{edges {i,j}} (2^(i*k+j) + 2^(j*k+i))`
a numeral, and `m i := (sizes : List ℕ).getD i.val 0`.  Number the classes so that every class has
many neighbours among the earlier ones (the search branches on class `0, 1, 2, ...` in this order).
-/

open Finset

/-- Ordered monochromatic weight of a class colouring `c`
(every unordered pair of adjacent classes is counted twice). -/
def monoS {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) (c : Fin k → Bool) : ℕ :=
  ∑ i, ∑ j, if A i j = true ∧ c i = c j then m i * m j else 0

namespace SkeletonBlowup

/-- `0/1` weight (as an integer) of the pair of classes `i j`. -/
def sw {k : ℕ} (A : Fin k → Fin k → Bool) (i j : Fin k) : ℤ := if A i j = true then 1 else 0

/-- The quadratic form `∑ i j, [A i j] s_i s_j`. -/
def Qf {k : ℕ} (A : Fin k → Fin k → Bool) (s : Fin k → ℤ) : ℤ := ∑ i, ∑ j, sw A i j * s i * s j

/-- `Qf` is affine in each coordinate separately (because `A i i = false`):
changing the `i`-th coordinate from `s i` to `x` changes `Qf` by `2 * (x - s i) * ∑ b, [A i b] s_b`.
-/
lemma Qf_update {k : ℕ} (A : Fin k → Fin k → Bool) (hsymm : ∀ i j, A i j = A j i)
    (hirr : ∀ i, A i i = false) (s : Fin k → ℤ) (i : Fin k) (x : ℤ) :
    Qf A (Function.update s i x) = Qf A s + 2 * (x - s i) * ∑ b, sw A i b * s b := by
  have hws : ∀ a b, sw A a b = sw A b a := fun a b => by simp [sw, hsymm a b]
  have hwd : ∀ a, sw A a a = 0 := fun a => by simp [sw, hirr a]
  set δ : ℤ := x - s i with hδ
  have ht : ∀ a, Function.update s i x a = s a + δ * (if a = i then 1 else 0) := by
    intro a
    by_cases h : a = i
    · subst h; simp [hδ]
    · simp [h]
  have expand : ∀ a b : Fin k, sw A a b * Function.update s i x a * Function.update s i x b
      = sw A a b * s a * s b + δ * ((if a = i then 1 else 0) * (sw A a b * s b))
        + δ * ((if b = i then 1 else 0) * (sw A a b * s a))
        + δ ^ 2 * ((if a = i then 1 else 0) * (if b = i then 1 else 0) * sw A a b) := by
    intro a b
    rw [ht a, ht b]
    ring
  unfold Qf
  simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ i_1, (if i_1 = i then (1:ℤ) else 0) * ∑ b, sw A i_1 b * s b
      = ∑ b, sw A i b * s b := by
    simp [ite_mul]
  have h3 : ∑ i_1, ∑ i_2, (if i_2 = i then (1:ℤ) else 0) * (sw A i_1 i_2 * s i_1)
      = ∑ b, sw A i b * s b := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl (fun a _ => by rw [hws a i])
  have h4 : ∑ i_1 : Fin k, ∑ i_2 : Fin k,
      ((if i_1 = i then (1:ℤ) else 0) * if i_2 = i then (1:ℤ) else 0) * sw A i_1 i_2 = 0 := by
    simp [ite_mul, hwd]
  rw [h2, h3, h4]
  ring

/-- Corner argument: a multi-affine function on a box is minimised at a corner.  For every point
`s` of the box `∏ i, [-m i, m i]` there is a corner `(±m i)_i` (given by a class colouring `c`)
at which `Qf` is not larger. -/
lemma exists_extreme {k : ℕ} (A : Fin k → Fin k → Bool) (hsymm : ∀ i j, A i j = A j i)
    (hirr : ∀ i, A i i = false) (m : Fin k → ℕ) :
    ∀ (S : Finset (Fin k)) (s : Fin k → ℤ), (∀ i, -(m i : ℤ) ≤ s i ∧ s i ≤ m i) →
      (∀ i, i ∉ S → s i = m i ∨ s i = -(m i : ℤ)) →
      ∃ c : Fin k → Bool,
        Qf A (fun i => if c i = true then (m i : ℤ) else -(m i : ℤ)) ≤ Qf A s := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro s hbox hext
    refine ⟨fun i => decide (s i = m i), le_of_eq ?_⟩
    congr 1
    funext i
    rcases hext i (by simp) with h | h
    · simp [h]
    · by_cases h' : s i = m i
      · simp [h']
      · simp [h]
  | insert i S hi ih =>
    intro s hbox hext
    have key : ∀ x : ℤ, -(m i : ℤ) ≤ x → x ≤ m i → (x = m i ∨ x = -(m i : ℤ)) →
        Qf A (Function.update s i x) ≤ Qf A s →
        ∃ c : Fin k → Bool,
          Qf A (fun i => if c i = true then (m i : ℤ) else -(m i : ℤ)) ≤ Qf A s := by
      intro x hx1 hx2 hx3 hle
      have hbox' : ∀ j, -(m j : ℤ) ≤ Function.update s i x j ∧ Function.update s i x j ≤ m j := by
        intro j
        by_cases hj : j = i
        · subst hj; simpa using ⟨hx1, hx2⟩
        · simpa [Function.update_of_ne hj] using hbox j
      have hext' : ∀ j, j ∉ S →
          Function.update s i x j = m j ∨ Function.update s i x j = -(m j : ℤ) := by
        intro j hj
        by_cases hji : j = i
        · subst hji; simpa using hx3
        · rw [Function.update_of_ne hji]
          exact hext j (by simp [hji, hj])
      obtain ⟨c, hc⟩ := ih _ hbox' hext'
      exact ⟨c, hc.trans hle⟩
    have hm0 : (0 : ℤ) ≤ m i := Int.natCast_nonneg (m i)
    by_cases hL : (∑ b, sw A i b * s b) ≤ 0
    · refine key (m i) (by linarith) le_rfl (Or.inl rfl) ?_
      rw [Qf_update A hsymm hirr]
      nlinarith [(hbox i).2]
    · push_neg at hL
      refine key (-(m i)) (le_refl _) (by linarith) (Or.inr rfl) ?_
      rw [Qf_update A hsymm hirr]
      nlinarith [(hbox i).1]

/- ### Counting identities -/

/-- `T = ∑ i j, [A i j] m_i m_j`. -/
def Tw {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) : ℤ :=
  ∑ i, ∑ j, sw A i j * (m i : ℤ) * (m j : ℤ)

/-- The sign of a boolean colour. -/
def sg (b : Bool) : ℤ := if b = true then 1 else -1

/-- `2 * monoS` in terms of the quadratic form at the corner of the colouring `c`. -/
lemma two_mul_monoS {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) (c : Fin k → Bool) :
    2 * (monoS A m c : ℤ)
      = Tw A m + Qf A (fun i => if c i = true then (m i : ℤ) else -(m i : ℤ)) := by
  have pt : ∀ i j, 2 * ((if A i j = true ∧ c i = c j then m i * m j else 0 : ℕ) : ℤ)
      = sw A i j * (m i : ℤ) * (m j : ℤ)
        + sw A i j * (if c i = true then (m i : ℤ) else -(m i : ℤ))
          * (if c j = true then (m j : ℤ) else -(m j : ℤ)) := by
    intro i j
    by_cases h : A i j = true <;> cases hci : c i <;> cases hcj : c j <;> simp [sw, h] <;> ring
  unfold monoS Tw Qf
  simp only [Nat.cast_sum]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  simp_rw [pt, Finset.sum_add_distrib]

/-- Summing over the sigma type `Σ i, Fin (m i)` twice. -/
lemma sum_sigma_sigma {k : ℕ} {m : Fin k → ℕ} (F : Fin k → Fin k → ℤ)
    (u v : (Σ i : Fin k, Fin (m i)) → ℤ) :
    ∑ x : (Σ i : Fin k, Fin (m i)), ∑ y : (Σ i : Fin k, Fin (m i)), F x.1 y.1 * u x * v y
      = ∑ i, ∑ j, F i j * (∑ a : Fin (m i), u ⟨i, a⟩) * (∑ b : Fin (m j), v ⟨j, b⟩) := by
  have h1 : ∀ x : (Σ i : Fin k, Fin (m i)),
      ∑ y : (Σ i : Fin k, Fin (m i)), F x.1 y.1 * u x * v y
        = u x * ∑ j, F x.1 j * ∑ b : Fin (m j), v ⟨j, b⟩ := by
    intro x
    rw [Fintype.sum_sigma]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  calc ∑ x : (Σ i : Fin k, Fin (m i)), ∑ y : (Σ i : Fin k, Fin (m i)), F x.1 y.1 * u x * v y
      = ∑ x : (Σ i : Fin k, Fin (m i)), u x * ∑ j, F x.1 j * ∑ b : Fin (m j), v ⟨j, b⟩ :=
        Finset.sum_congr rfl (fun x _ => h1 x)
    _ = ∑ i, ∑ a : Fin (m i), u ⟨i, a⟩ * ∑ j, F i j * ∑ b : Fin (m j), v ⟨j, b⟩ :=
        Fintype.sum_sigma (fun x : (Σ i : Fin k, Fin (m i)) =>
          u x * ∑ j, F x.1 j * ∑ b : Fin (m j), v ⟨j, b⟩)
    _ = ∑ i, (∑ a : Fin (m i), u ⟨i, a⟩) * ∑ j, F i j * ∑ b : Fin (m j), v ⟨j, b⟩ := by
        simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, F i j * (∑ a : Fin (m i), u ⟨i, a⟩) * (∑ b : Fin (m j), v ⟨j, b⟩) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Ordered number of monochromatic adjacent pairs of a vertex colouring. -/
def vS {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (g : (Σ i : Fin k, Fin (m i)) → Bool) : ℕ :=
  ∑ x : (Σ i : Fin k, Fin (m i)), ∑ y : (Σ i : Fin k, Fin (m i)),
    if A x.1 y.1 = true ∧ g x = g y then 1 else 0

/-- `2 * vS` (ordered number of monochromatic adjacent pairs of a vertex colouring `g`) in terms
of the quadratic form at the point `s_i = ∑ a, ±1` (imbalance of the class `i`). -/
lemma two_mul_vS {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (g : (Σ i : Fin k, Fin (m i)) → Bool) :
    2 * (vS A m g : ℤ) = Tw A m + Qf A (fun i => ∑ a : Fin (m i), sg (g ⟨i, a⟩)) := by
  have pt : ∀ x y : (Σ i : Fin k, Fin (m i)),
      2 * ((if A x.1 y.1 = true ∧ g x = g y then 1 else 0 : ℕ) : ℤ)
        = sw A x.1 y.1 * (fun _ => (1:ℤ)) x * (fun _ => (1:ℤ)) y
          + sw A x.1 y.1 * sg (g x) * sg (g y) := by
    intro x y
    by_cases h : A x.1 y.1 = true <;> cases hx : g x <;> cases hy : g y <;> simp [sw, sg, h]
  unfold vS
  simp only [Nat.cast_sum]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  simp_rw [pt, Finset.sum_add_distrib]
  rw [sum_sigma_sigma (m := m) (fun i j => sw A i j) (fun _ => (1:ℤ)) (fun _ => (1:ℤ)),
    sum_sigma_sigma (m := m) (fun i j => sw A i j) (fun x => sg (g x)) (fun x => sg (g x))]
  simp [Tw, Qf]

/- ### The blow-up graph -/

/-- The blow-up of the skeleton `A` with class sizes `m`: vertices `(i, a)` with `a < m i`,
`(i, a) ~ (j, b)` iff `A i j`. -/
def blowup {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false) :
    SimpleGraph (Σ i : Fin k, Fin (m i)) where
  Adj x y := A x.1 y.1 = true
  symm := fun x y h => by
    show A y.1 x.1 = true
    rw [hsymm]; exact h
  loopless := fun x h => by
    have h' : A x.1 x.1 = true := h
    rw [hirr] at h'
    exact Bool.noConfusion h'

lemma blowup_cliqueFree {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False) :
    (blowup A m hsymm hirr).CliqueFree 3 := by
  classical
  intro t ht
  rw [SimpleGraph.is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  exact htf a.1 b.1 c.1 hab hbc hac

/-- Edges of `G` that are monochromatic for `g` are not edges of `H` (if `g` is a proper colouring
of `H`); counting ordered pairs gives a bound on the number of deleted edges. -/
lemma card_pairs_le {V : Type} [Fintype V] (G H : SimpleGraph V)
    (iG : Fintype G.edgeSet) (iH : Fintype H.edgeSet) (dE : DecidableEq (Sym2 V))
    (g : V → Bool) (hg : ∀ x y, H.Adj x y → g x ≠ g y)
    (p : V → V → Prop) [∀ x y, Decidable (p x y)] (hp : ∀ x y, p x y ↔ G.Adj x y ∧ g x = g y) :
    ∑ x, ∑ y, (if p x y then 1 else 0) ≤ 2 * (G.edgeFinset \ H.edgeFinset).card := by
  classical
  let M : SimpleGraph V :=
    { Adj := fun x y => p x y
      symm := fun x y h => (hp y x).2 (by
        have h' := (hp x y).1 h
        exact ⟨h'.1.symm, h'.2.symm⟩)
      loopless := fun x h => G.loopless x ((hp x x).1 h).1 }
  have hM := SimpleGraph.two_mul_card_edgeFinset M
  have hsub : M.edgeFinset ⊆ G.edgeFinset \ H.edgeFinset := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have he' := (hp x y).1 he
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      exact ⟨he'.1, fun hH => hg x y hH he'.2⟩
  have hcard : ∑ x, ∑ y, (if p x y then 1 else 0)
      = (Finset.univ.filter fun q : V × V => M.Adj q.1 q.2).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
  calc _ = _ := hcard
    _ = 2 * M.edgeFinset.card := hM.symm
    _ ≤ 2 * (G.edgeFinset \ H.edgeFinset).card := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)

open scoped Classical in
/-- Generic form of the blow-up bound, with the ordered mono weight `monoS` (no division). -/
theorem skeleton_bound_ordered (k B : ℕ) (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False)
    (hcut : ∀ c : Fin k → Bool, 2 * B < monoS A m c) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Fintype.card V = ∑ i, m i ∧
      G.CliqueFree 3 ∧
      ∀ H : SimpleGraph V, H ≤ G → H.IsBipartite → B < (G.edgeFinset \ H.edgeFinset).card := by
  refine ⟨Σ i : Fin k, Fin (m i), inferInstance, blowup A m hsymm hirr, ?_, ?_, ?_⟩
  · simp [Fintype.card_sigma]
  · exact blowup_cliqueFree A m hsymm hirr htf
  · intro H hHG hHb
    obtain ⟨col⟩ := hHb
    obtain ⟨g, hg⟩ : ∃ g : (Σ i : Fin k, Fin (m i)) → Bool,
        ∀ x y, H.Adj x y → g x ≠ g y := by
      refine ⟨fun x => decide (col x = 0), fun x y hxy => ?_⟩
      have hne : col x ≠ col y := col.valid hxy
      show decide (col x = 0) ≠ decide (col y = 0)
      revert hne
      generalize col x = a
      generalize col y = b
      revert a b
      decide
    have hbox : ∀ i, -(m i : ℤ) ≤ (∑ a : Fin (m i), sg (g ⟨i, a⟩)) ∧
        (∑ a : Fin (m i), sg (g ⟨i, a⟩)) ≤ m i := by
      intro i
      constructor
      · calc -(m i : ℤ) = ∑ _a : Fin (m i), (-1 : ℤ) := by simp
          _ ≤ ∑ a : Fin (m i), sg (g ⟨i, a⟩) :=
            Finset.sum_le_sum (fun a _ => by cases h : g ⟨i, a⟩ <;> simp [sg])
      · calc (∑ a : Fin (m i), sg (g ⟨i, a⟩)) ≤ ∑ _a : Fin (m i), (1 : ℤ) :=
            Finset.sum_le_sum (fun a _ => by cases h : g ⟨i, a⟩ <;> simp [sg])
          _ = m i := by simp
    obtain ⟨c, hc⟩ := exists_extreme A hsymm hirr m Finset.univ
      (fun i => ∑ a : Fin (m i), sg (g ⟨i, a⟩)) hbox (fun i hi => absurd (Finset.mem_univ i) hi)
    have h1 := two_mul_monoS A m c
    have h2 := two_mul_vS A m g
    have hle : monoS A m c ≤ vS A m g := by
      have : (monoS A m c : ℤ) ≤ vS A m g := by linarith
      exact_mod_cast this
    have h4 := hcut c
    refine Nat.lt_of_mul_lt_mul_left (a := 2) ?_
    exact lt_of_lt_of_le h4 (hle.trans (card_pairs_le (blowup A m hsymm hirr) H _ _ _ g hg
      (fun x y => A x.1 y.1 = true ∧ g x = g y) (fun x y => Iff.rfl)))

end SkeletonBlowup

/-- Number of monochromatic edges of the blow-up of the skeleton `(A, m)` when every vertex gets the
colour `c i` of its class `i` (`monoS` counts every such edge twice; it is even as soon as `A` is
symmetric and irreflexive, so the division is exact). -/
def monoW {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) (c : Fin k → Bool) : ℕ :=
  monoS A m c / 2

open scoped Classical in
/-- **Generic blow-up bound.** If the skeleton `(A, m)` is symmetric, irreflexive and triangle-free
and every class-level 2-colouring `c` has more than `B` monochromatic edges (`B < monoW A m c`),
then there is a triangle-free graph `G` on `∑ i, m i` vertices such that every bipartite subgraph
`H ≤ G` misses more than `B` edges of `G`. -/
theorem skeleton_not_erdos23_bound (k B : ℕ) (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False)
    (hcut : ∀ c : Fin k → Bool, B < monoW A m c) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Fintype.card V = ∑ i, m i ∧
      G.CliqueFree 3 ∧
      ∀ H : SimpleGraph V, H ≤ G → H.IsBipartite → B < (G.edgeFinset \ H.edgeFinset).card :=
  SkeletonBlowup.skeleton_bound_ordered k B A m hsymm hirr htf
    (fun c => by have := hcut c; unfold monoW at this; omega)

open scoped Classical in
/-- **Disproof of `Erdos23.erdos_23` from a skeleton.** The conclusion is (definitionally, in fact
syntactically) the negation of the type of `Erdos23.erdos_23`. -/
theorem skeleton_disproof_ordered (k n : ℕ) (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsum : ∑ i, m i = 5 * n)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False)
    (hcut : ∀ c : Fin k → Bool, 2 * n ^ 2 < monoS A m c) :
    ¬ (∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2) := by
  intro h
  obtain ⟨V, hV, G, hcard, hG, hH⟩ :=
    SkeletonBlowup.skeleton_bound_ordered k (n ^ 2) A m hsymm hirr htf hcut
  obtain ⟨H, hHG, hHb, hle⟩ := h n V (hcard.trans hsum) G hG
  exact absurd hle (not_le.mpr (hH H hHG hHb))

open scoped Classical in
/-- **Disproof of `Erdos23.erdos_23` from a skeleton.** The conclusion is (definitionally, in fact
syntactically) the negation of the type of `Erdos23.erdos_23`. -/
theorem skeleton_disproof (k n : ℕ) (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsum : ∑ i, m i = 5 * n)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False)
    (hcut : ∀ c : Fin k → Bool, n ^ 2 < monoW A m c) :
    ¬ (∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2) :=
  skeleton_disproof_ordered k n A m hsum hsymm hirr htf
    (fun c => by have := hcut c; unfold monoW at this; omega)

/- ### Scalable check of the hypothesis `hcut` (branch and bound)

For skeletons with more than ~9 classes, `decide` on `∀ c : Fin k → Bool, B < monoW A m c`
(`2 ^ k` colourings) is too slow.  `SkeletonBlowup.cutCheck A m T` is a Boolean branch-and-bound
search (over the colours of the classes `0, 1, 2, ...` in this order) whose soundness is proved in
`SkeletonBlowup.cutCheck_sound`:
`cutCheck A m T = true → ∀ c, T < monoS A m c`.
It is meant to be evaluated by the kernel (`by decide +kernel`) and only explores partial
colourings whose lower bound on the cost is still `≤ T`. -/

namespace SkeletonBlowup

/-- `monoS` plus the unary terms `u0 i` (if `c i = false`) / `u1 i` (if `c i = true`). -/
def Fw {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) (u0 u1 : Fin k → ℕ)
    (c : Fin k → Bool) : ℕ :=
  monoS A m c + ∑ i, (if c i = true then u1 i else u0 i)

lemma Fw_cons {k : ℕ} (A : Fin (k+1) → Fin (k+1) → Bool) (m : Fin (k+1) → ℕ)
    (u0 u1 : Fin (k+1) → ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false) (b : Bool) (c' : Fin k → Bool) :
    Fw A m u0 u1 (Fin.cons b c' : Fin (k+1) → Bool) =
      Fw (fun i j => A i.succ j.succ) (fun i => m i.succ)
        (fun j => u0 j.succ + if b = false ∧ A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0)
        (fun j => u1 j.succ + if b = true ∧ A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0) c'
      + (if b = true then u1 0 else u0 0) := by
  unfold Fw monoS
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have h00 : A 0 0 = false := hirr 0
  simp only [h00, Bool.false_eq_true, if_false, zero_add, and_true]
  rw [Finset.sum_add_distrib]
  have hsym : ∑ x : Fin k, (if A x.succ 0 = true ∧ c' x = b then m x.succ * m 0 else 0)
      = ∑ x : Fin k, (if A 0 x.succ = true ∧ b = c' x then m 0 * m x.succ else 0) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : c' x = b
    · subst h; simp [hsymm x.succ 0, mul_comm]
    · have h' : ¬ b = c' x := fun e => h e.symm
      simp [h, h']
  have hun : ∑ x : Fin k, (if c' x = true
        then u1 x.succ + (if b = true ∧ A 0 x.succ = true then 2 * (m 0 * m x.succ) else 0)
        else u0 x.succ + (if b = false ∧ A 0 x.succ = true then 2 * (m 0 * m x.succ) else 0))
      = ∑ x, (if c' x = true then u1 x.succ else u0 x.succ)
        + 2 * ∑ x : Fin k, (if A 0 x.succ = true ∧ b = c' x then m 0 * m x.succ else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    cases b <;> cases hx : c' x <;> simp
  rw [hsym, hun]
  omega


/- ### List-based branch and bound -/

/-- Pointwise sum of two lists, padding with zeros. -/
def addL : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addL xs ys

lemma getD_addL : ∀ (xs ys : List ℕ) (j : ℕ),
    (addL xs ys).getD j 0 = xs.getD j 0 + ys.getD j 0
  | [], ys, j => by simp [addL]
  | x :: xs, [], j => by simp [addL]
  | x :: xs, y :: ys, 0 => by simp [addL]
  | x :: xs, y :: ys, j + 1 => by
    simp only [addL, List.getD_cons_succ]
    exact getD_addL xs ys j

lemma getD_tail (u : List ℕ) (j : ℕ) : u.tail.getD j 0 = u.getD (j + 1) 0 := by
  cases u <;> simp

/-- `∑_{j < n} min (u0_j) (u1_j)`, where lists are padded with zeros. -/
def minSumN : ℕ → List ℕ → List ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, u0, u1 => min (u0.headD 0) (u1.headD 0) + minSumN n u0.tail u1.tail

lemma minSumN_eq : ∀ (n : ℕ) (u0 u1 : List ℕ),
    minSumN n u0 u1 = ∑ j : Fin n, min (u0.getD j.val 0) (u1.getD j.val 0)
  | 0, u0, u1 => by simp [minSumN]
  | n + 1, u0, u1 => by
    rw [minSumN, Fin.sum_univ_succ, minSumN_eq n u0.tail u1.tail]
    simp only [Fin.val_zero, Fin.val_succ, getD_tail]
    congr 1
    · cases u0 <;> cases u1 <;> simp

/-- The list `[f 0, f 1, ..., f (n-1)]`. -/
def rowL : (n : ℕ) → (Fin n → ℕ) → List ℕ
  | 0, _ => []
  | n + 1, f => f 0 :: rowL n (fun j => f j.succ)

lemma getD_rowL : ∀ (n : ℕ) (f : Fin n → ℕ) (j : Fin n), (rowL n f).getD j.val 0 = f j
  | 0, f, j => j.elim0
  | n + 1, f, j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [rowL]
    · simp only [rowL, Fin.val_succ, List.getD_cons_succ]
      exact getD_rowL n _ j

/-- The "first rows" of the successive sub-skeletons: row `d` lists the weights
`2 * m_d * m_j` of the edges from class `d` to the later classes `j > d`. -/
def mkRows : (n : ℕ) → (Fin n → Fin n → Bool) → (Fin n → ℕ) → List (List ℕ)
  | 0, _, _ => []
  | n + 1, A, m =>
    rowL n (fun j => if A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0) ::
      mkRows n (fun i j => A i.succ j.succ) (fun i => m i.succ)

lemma length_mkRows : ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (m : Fin n → ℕ),
    (mkRows n A m).length = n
  | 0, _, _ => rfl
  | n + 1, A, m => by simp [mkRows, length_mkRows n]

/-- Branch-and-bound over the colours of the classes `0, 1, 2, ...` (in this order).
State: remaining rows, unary terms `u0`, `u1` of the remaining classes, accumulated cost `cst`. -/
def chk : List (List ℕ) → List ℕ → List ℕ → ℕ → ℕ → Bool
  | [], _, _, cst, T => decide (T < cst)
  | w :: rows, u0, u1, cst, T =>
    decide (T < cst + minSumN (rows.length + 1) u0 u1) ||
      (chk rows (addL u0.tail w) u1.tail (cst + u0.headD 0) T &&
       chk rows u0.tail (addL u1.tail w) (cst + u1.headD 0) T)

theorem chk_sound : ∀ (n : ℕ) (A : Fin n → Fin n → Bool) (m : Fin n → ℕ) (u0 u1 : List ℕ)
    (cst T : ℕ), (∀ i j, A i j = A j i) → (∀ i, A i i = false) →
    chk (mkRows n A m) u0 u1 cst T = true →
    ∀ c : Fin n → Bool,
      T < cst + Fw A m (fun j => u0.getD j.val 0) (fun j => u1.getD j.val 0) c := by
  intro n
  induction n with
  | zero =>
    intro A m u0 u1 cst T hsymm hirr h c
    simp only [mkRows, chk, decide_eq_true_eq] at h
    simp [Fw, monoS, h]
  | succ n ih =>
    intro A m u0 u1 cst T hsymm hirr h c
    simp only [mkRows, chk, length_mkRows, Bool.or_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h
    rcases h with h | ⟨h0, h1⟩
    · have hle : minSumN (n + 1) u0 u1 ≤
          Fw A m (fun j => u0.getD j.val 0) (fun j => u1.getD j.val 0) c := by
        rw [minSumN_eq]
        unfold Fw
        refine le_trans ?_ (Nat.le_add_left _ _)
        refine Finset.sum_le_sum (fun j _ => ?_)
        cases hj : c j <;> simp
      omega
    · obtain ⟨b, c', rfl⟩ : ∃ (b : Bool) (c' : Fin n → Bool), c = Fin.cons b c' :=
        ⟨c 0, Fin.tail c, (Fin.cons_self_tail c).symm⟩
      rw [Fw_cons A m _ _ hsymm hirr b c']
      cases b
      · have := ih _ _ _ _ _ T (fun i j => hsymm _ _) (fun i => hirr _) h0 c'
        have e0 : (fun j : Fin n => (addL u0.tail (rowL n fun j =>
              if A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0)).getD (↑j) 0)
            = (fun j : Fin n => u0.getD (↑j.succ) 0 +
              if false = false ∧ A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0) := by
          funext j
          rw [getD_addL, getD_tail, getD_rowL]
          simp
        have e1 : (fun j : Fin n => u1.tail.getD (↑j) 0)
            = (fun j : Fin n => u1.getD (↑j.succ) 0 +
              if false = true ∧ A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0) := by
          funext j
          rw [getD_tail]
          simp
        rw [e0, e1] at this
        have e2 : (if false = true then u1.getD (↑(0 : Fin (n + 1))) 0
            else u0.getD (↑(0 : Fin (n + 1))) 0) = u0.headD 0 := by cases u0 <;> simp
        rw [e2]
        omega
      · have := ih _ _ _ _ _ T (fun i j => hsymm _ _) (fun i => hirr _) h1 c'
        have e0 : (fun j : Fin n => u0.tail.getD (↑j) 0)
            = (fun j : Fin n => u0.getD (↑j.succ) 0 +
              if true = false ∧ A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0) := by
          funext j
          rw [getD_tail]
          simp
        have e1 : (fun j : Fin n => (addL u1.tail (rowL n fun j =>
              if A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0)).getD (↑j) 0)
            = (fun j : Fin n => u1.getD (↑j.succ) 0 +
              if true = true ∧ A 0 j.succ = true then 2 * (m 0 * m j.succ) else 0) := by
          funext j
          rw [getD_addL, getD_tail, getD_rowL]
          simp
        rw [e0, e1] at this
        have e2 : (if true = true then u1.getD (↑(0 : Fin (n + 1))) 0
            else u0.getD (↑(0 : Fin (n + 1))) 0) = u1.headD 0 := by cases u1 <;> simp
        rw [e2]
        omega

/-- The branch-and-bound check for the hypothesis `∀ c, T < monoS A m c` (see
`cutCheck_sound`).  It branches on the colours of the classes `0, 1, 2, ...` in this order and
prunes a partial colouring as soon as (cost so far) + (for every unassigned class, the cheaper of its
two colours with respect to the assigned classes) exceeds `T`. -/
def cutCheck {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) (T : ℕ) : Bool :=
  chk (mkRows k A m) (List.replicate k 0) (List.replicate k 0) 0 T

/-- Soundness of the branch-and-bound check. -/
theorem cutCheck_sound {k : ℕ} (A : Fin k → Fin k → Bool) (m : Fin k → ℕ) (T : ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (h : cutCheck A m T = true) : ∀ c : Fin k → Bool, T < monoS A m c := by
  intro c
  have := chk_sound k A m _ _ 0 T hsymm hirr h c
  simpa [Fw] using this

end SkeletonBlowup

open scoped Classical in
/-- Variant of `skeleton_not_erdos23_bound` whose finite hypothesis is the branch-and-bound check
`SkeletonBlowup.cutCheck A m (2 * B) = true` (instead of `∀ c, B < monoW A m c`). -/
theorem skeleton_not_erdos23_bound_check (k B : ℕ) (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False)
    (hcheck : SkeletonBlowup.cutCheck A m (2 * B) = true) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Fintype.card V = ∑ i, m i ∧
      G.CliqueFree 3 ∧
      ∀ H : SimpleGraph V, H ≤ G → H.IsBipartite → B < (G.edgeFinset \ H.edgeFinset).card :=
  SkeletonBlowup.skeleton_bound_ordered k B A m hsymm hirr htf
    (SkeletonBlowup.cutCheck_sound A m (2 * B) hsymm hirr hcheck)

open scoped Classical in
/-- Variant of `skeleton_disproof` whose finite hypothesis is the branch-and-bound check
`SkeletonBlowup.cutCheck A m (2 * n ^ 2) = true`.  The conclusion is the negation of the type of
`Erdos23.erdos_23`. -/
theorem skeleton_disproof_check (k n : ℕ) (A : Fin k → Fin k → Bool) (m : Fin k → ℕ)
    (hsum : ∑ i, m i = 5 * n)
    (hsymm : ∀ i j, A i j = A j i) (hirr : ∀ i, A i i = false)
    (htf : ∀ i j l, A i j = true → A j l = true → A i l = true → False)
    (hcheck : SkeletonBlowup.cutCheck A m (2 * n ^ 2) = true) :
    ¬ (∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n ^ 2) :=
  skeleton_disproof_ordered k n A m hsum hsymm hirr htf
    (SkeletonBlowup.cutCheck_sound A m (2 * n ^ 2) hsymm hirr hcheck)

/- ### Validation: the blow-up of the pentagon

The pentagon blow-up with classes of size `n` needs exactly `n ^ 2` deletions (this is the
extremal example of the conjecture), so `hcut` holds with `B = n ^ 2 - 1` and fails with
`B = n ^ 2`. This checks that the generic lemma is usable with `decide` for the finite hypotheses. -/

section PentagonTest

/-- Adjacency of the 5-cycle on `Fin 5`. -/
def pentagon : Fin 5 → Fin 5 → Bool := fun i j => decide (j = i + 1 ∨ i = j + 1)

open scoped Classical in
/-- Every bipartite subgraph of the blow-up of `C₅` with classes of size `3` (15 vertices) misses
more than `8 = 3 ^ 2 - 1` edges. -/
theorem pentagon_test :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Fintype.card V = 5 * 3 ∧
      G.CliqueFree 3 ∧
      ∀ H : SimpleGraph V, H ≤ G → H.IsBipartite → 8 < (G.edgeFinset \ H.edgeFinset).card := by
  have := skeleton_not_erdos23_bound 5 8 pentagon (fun _ => 3) (by decide) (by decide)
    (by decide) (by decide)
  simpa using this

/-- The threshold `n ^ 2 = 9` itself is *not* certified by the pentagon: the check is sharp. -/
example : ¬ (∀ c : Fin 5 → Bool, 9 < monoW pentagon (fun _ => 3) c) := by decide

open scoped Classical in
/-- Same statement as `pentagon_test`, but using the branch-and-bound check. -/
theorem pentagon_test_check :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Fintype.card V = 5 * 3 ∧
      G.CliqueFree 3 ∧
      ∀ H : SimpleGraph V, H ≤ G → H.IsBipartite → 8 < (G.edgeFinset \ H.edgeFinset).card := by
  have := skeleton_not_erdos23_bound_check 5 8 pentagon (fun _ => 3) (by decide) (by decide)
    (by decide) (by decide +kernel)
  simpa using this

/-- The branch-and-bound check is sharp as well. -/
example : SkeletonBlowup.cutCheck pentagon (fun _ => 3) (2 * 9) = false := by decide +kernel

end PentagonTest

section AndrasfaiTest

/-- The Andrásfai graph `And(4)` (11 vertices, 22 edges, triangle-free), as a bit matrix:
`and4A i j` is bit number `i * 11 + j` of the numeral `and4M`.  This is the recommended format
for skeletons with many classes (all lookups are cheap kernel operations on `Nat`). -/
def and4M : ℕ := 760207733346609932729655410744175762

def and4A : Fin 11 → Fin 11 → Bool := fun i j => Nat.testBit and4M (i.val * 11 + j.val)

open scoped Classical in
/-- Every bipartite subgraph of `And(4)` misses more than `3` of its edges (it has `11` vertices
and needs `4` deletions); all finite hypotheses are discharged by `decide +kernel`. -/
theorem andrasfai4_test :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V), Fintype.card V = 11 ∧
      G.CliqueFree 3 ∧
      ∀ H : SimpleGraph V, H ≤ G → H.IsBipartite → 3 < (G.edgeFinset \ H.edgeFinset).card := by
  have := skeleton_not_erdos23_bound_check 11 3 and4A (fun _ => 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simpa using this

end AndrasfaiTest

#print axioms skeleton_not_erdos23_bound
#print axioms skeleton_disproof
#print axioms skeleton_disproof_ordered
#print axioms pentagon_test
#print axioms pentagon_test_check
#print axioms andrasfai4_test
#print axioms skeleton_not_erdos23_bound_check
#print axioms skeleton_disproof_check
