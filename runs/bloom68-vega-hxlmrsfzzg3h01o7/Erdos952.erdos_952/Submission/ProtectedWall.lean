import FormalConjecturesUtil
import Submission.WallObstruction

/-!
# Exact bridge filling on the Gaussian-integer lattice

`Wsharp W` fills precisely the horizontal and vertical length-two white bridges.
The original relation `R2Adj W` uses squared norm at most four; `KingAdj` allows
stationary steps. This file is generic in the white predicate `W`.

The local witness argument gives exact component correspondence, including
finiteness/infinity of components. The infinite-sequence transfer uses finite
fibers and last-visit loop erasure, not injectivity of the midpoint-filled walk.
The complementary predicate `Bsharp` is only a formula: no protected-wall
certificate, and no all-step-bounds Gaussian-moat result, is asserted here.

This file does not import `Submission.Spec`.
-/

namespace Erdos952.ProtectedWall

abbrev G := GaussianInt

/-- The vertical unit, with the same convention as the wall framework. -/
abbrev I : G := WallObstruction.I

/-- Fill the midpoints of axial length-two white bridges. -/
def Wsharp (W : G → Prop) (v : G) : Prop :=
  W v ∨ (W (v - 1) ∧ W (v + 1)) ∨ (W (v - I) ∧ W (v + I))

/-- White adjacency of Euclidean radius two (squared norm at most four). -/
def R2Adj (W : G → Prop) (p q : G) : Prop :=
  W p ∧ W q ∧ (q - p).norm ≤ 4

/-- White king adjacency, including stationary steps. -/
def KingAdj (W : G → Prop) (p q : G) : Prop :=
  W p ∧ W q ∧ WallObstruction.KingAdjacent p q

abbrev R2Reach (W : G → Prop) := Relation.ReflTransGen (R2Adj W)
abbrev KingReach (W : G → Prop) := Relation.ReflTransGen (KingAdj W)

theorem white_sharp {W : G → Prop} {v : G} (hv : W v) : Wsharp W v :=
  Or.inl hv

theorem king_refl (v : G) : WallObstruction.KingAdjacent v v := by
  simp [WallObstruction.KingAdjacent]

theorem KingAdj.symm {W : G → Prop} {p q : G} (h : KingAdj W p q) :
    KingAdj W q p := ⟨h.2.1, h.1, h.2.2.symm⟩

theorem KingReach.symm {W : G → Prop} {p q : G} (h : KingReach W p q) :
    KingReach W q p := Relation.ReflTransGen.symmetric (fun _ _ => KingAdj.symm) h

theorem king_norm_le_two {p q : G} (h : WallObstruction.KingAdjacent p q) :
    (q - p).norm ≤ 2 := by
  rcases h with ⟨hx, hy⟩
  rw [abs_le] at hx hy
  have hx' : (q.re - p.re) ^ 2 ≤ 1 := by nlinarith
  have hy' : (q.im - p.im) ^ 2 ≤ 1 := by nlinarith
  simp only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub]
  nlinarith

theorem king_r2 {W : G → Prop} {p q : G} (hp : W p) (hq : W q)
    (h : WallObstruction.KingAdjacent p q) : R2Adj W p q :=
  ⟨hp, hq, (king_norm_le_two h).trans (by norm_num)⟩

/- ## Local witness sets -/

/-- The three possible witnesses: a singleton, or one of the two axial pairs. -/
inductive WitnessKind where
  | point | horizontal | vertical
  deriving DecidableEq, Fintype

/-- The point witness is listed twice; the other two witnesses list both ends. -/
def witness (v : G) (k : WitnessKind) (b : Bool) : G :=
  match k with
  | .point => v
  | .horizontal => if b then v + 1 else v - 1
  | .vertical => if b then v + I else v - I

/-- Every point of this witness set is original-white. -/
def Supported (W : G → Prop) (v : G) (k : WitnessKind) : Prop :=
  ∀ b, W (witness v k b)

theorem sharp_iff_supported (W : G → Prop) (v : G) :
    Wsharp W v ↔ ∃ k, Supported W v k := by
  constructor
  · rintro (h | h | h)
    · exact ⟨.point, fun _ => h⟩
    · refine ⟨.horizontal, ?_⟩
      intro b
      cases b <;> simp_all [witness]
    · refine ⟨.vertical, ?_⟩
      intro b
      cases b <;> simp_all [witness]
  · rintro ⟨k, hk⟩
    cases k
    · exact Or.inl (hk false)
    · exact Or.inr (Or.inl ⟨hk false, hk true⟩)
    · exact Or.inr (Or.inr ⟨hk false, hk true⟩)

theorem witness_near (v : G) (k : WitnessKind) (b : Bool) :
    WallObstruction.KingAdjacent v (witness v k b) := by
  cases k <;> cases b <;>
    simp [witness, WallObstruction.KingAdjacent, I]

/-- Both ends of any one supported witness set are R2-adjacent. -/
theorem witness_r2 {W : G → Prop} {v : G} {k : WitnessKind}
    (hk : Supported W v k) (a b : Bool) :
    R2Adj W (witness v k a) (witness v k b) := by
  refine ⟨hk a, hk b, ?_⟩
  cases k <;> cases a <;> cases b <;>
    norm_num [witness, Zsqrtd.norm, I] <;> nlinarith

/-- For *any* choices of witness kinds at neighboring centers, some two
witnesses are king-adjacent (possibly equal). This is a finite coordinate check. -/
theorem nearby_witnesses {u v : G} (h : WallObstruction.KingAdjacent u v)
    (k l : WitnessKind) :
    ∃ a b, WallObstruction.KingAdjacent (witness u k a) (witness v l b) := by
  rcases h with ⟨hx, hy⟩
  rw [abs_le] at hx hy
  cases k <;> cases l <;>
    simp [witness, WallObstruction.KingAdjacent, I, abs_le] <;> omega

/-- Deterministically prefer an original-white point, then a horizontal bridge. -/
noncomputable def chosenKind (W : G → Prop) (v : G) : WitnessKind := by
  classical
  exact if W v then .point
    else if W (v - 1) ∧ W (v + 1) then .horizontal else .vertical

theorem chosenKind_supported {W : G → Prop} {v : G} (hv : Wsharp W v) :
    Supported W v (chosenKind W v) := by
  classical
  unfold chosenKind
  split
  · intro b
    assumption
  · split
    · intro b
      cases b <;> simp_all [witness]
    · have h : W (v - I) ∧ W (v + I) := by simpa [Wsharp, *] using hv
      intro b
      cases b <;> simp_all [witness]

/-- A chosen original-white representative of a filled vertex. It is within
one king step, and it fixes every original-white vertex. -/
noncomputable def anchor (W : G → Prop) (v : G) : G :=
  witness v (chosenKind W v) false

theorem anchor_eq {W : G → Prop} {v : G} (hv : W v) : anchor W v = v := by
  simp [anchor, chosenKind, hv, witness]

theorem anchor_white {W : G → Prop} {v : G} (hv : Wsharp W v) :
    W (anchor W v) := chosenKind_supported hv false

theorem anchor_near (W : G → Prop) (v : G) :
    WallObstruction.KingAdjacent v (anchor W v) := witness_near _ _ _

theorem king_anchor {W : G → Prop} {v : G} (hv : Wsharp W v) :
    KingAdj (Wsharp W) v (anchor W v) :=
  ⟨hv, white_sharp (anchor_white hv), anchor_near W v⟩

/-- A filled king edge connects the chosen representatives by three R2 edges. -/
theorem king_edge_anchor_reach {W : G → Prop} {u v : G}
    (h : KingAdj (Wsharp W) u v) : R2Reach W (anchor W u) (anchor W v) := by
  obtain ⟨a, b, hab⟩ := nearby_witnesses h.2.2 (chosenKind W u) (chosenKind W v)
  have hu := chosenKind_supported h.1
  have hv := chosenKind_supported h.2.1
  exact ((Relation.ReflTransGen.single (witness_r2 hu false a)).tail
    (king_r2 (hu a) (hv b) hab)).tail (witness_r2 hv b false)

theorem king_reach_anchor {W : G → Prop} {u v : G}
    (h : KingReach (Wsharp W) u v) : R2Reach W (anchor W u) (anchor W v) :=
  h.lift' (anchor W) (fun _ _ => king_edge_anchor_reach)

/- ## Inserting the axial midpoints -/

/-- The exact integral possibilities at squared distance at most four. -/
theorem norm_le_four_coordinates {x y : ℤ} (h : x ^ 2 + y ^ 2 ≤ 4) :
    (|x| ≤ 1 ∧ |y| ≤ 1) ∨ (x = 2 ∧ y = 0) ∨ (x = -2 ∧ y = 0) ∨
      (x = 0 ∧ y = 2) ∨ (x = 0 ∧ y = -2) := by
  have hx : -2 ≤ x ∧ x ≤ 2 := by constructor <;> nlinarith [sq_nonneg y]
  have hy : -2 ≤ y ∧ y ≤ 2 := by constructor <;> nlinarith [sq_nonneg x]
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  interval_cases x <;> interval_cases y <;> norm_num at *

/-- Every R2 edge becomes two filled king edges. For an already-king edge
one of these can be stationary. -/
theorem r2_edge_bridge {W : G → Prop} {p q : G} (h : R2Adj W p q) :
    ∃ m, KingAdj (Wsharp W) p m ∧ KingAdj (Wsharp W) m q := by
  rcases h with ⟨hp, hq, hn⟩
  have hs : (q.re - p.re) ^ 2 + (q.im - p.im) ^ 2 ≤ 4 := by
    simp only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub] at hn
    nlinarith only [hn]
  rcases norm_le_four_coordinates hs with h | ⟨hx, hy⟩ | ⟨hx, hy⟩ |
      ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact ⟨p, ⟨white_sharp hp, white_sharp hp, king_refl p⟩,
      ⟨white_sharp hp, white_sharp hq, h⟩⟩
  · have he : q = p + 1 + 1 := by ext <;> simp <;> omega
    subst q
    have hm : Wsharp W (p + 1) :=
      Or.inr (Or.inl ⟨by simpa using hp, hq⟩)
    refine ⟨p + 1, ⟨white_sharp hp, hm, ?_⟩, ⟨hm, white_sharp hq, ?_⟩⟩ <;>
      simp [WallObstruction.KingAdjacent]
  · have he : q = p - 1 - 1 := by ext <;> simp <;> omega
    subst q
    have hm : Wsharp W (p - 1) :=
      Or.inr (Or.inl ⟨hq, by simpa using hp⟩)
    refine ⟨p - 1, ⟨white_sharp hp, hm, ?_⟩, ⟨hm, white_sharp hq, ?_⟩⟩ <;>
      simp [WallObstruction.KingAdjacent]
  · have he : q = p + I + I := by ext <;> simp [I] <;> omega
    subst q
    have hm : Wsharp W (p + I) :=
      Or.inr (Or.inr ⟨by simpa using hp, hq⟩)
    refine ⟨p + I, ⟨white_sharp hp, hm, ?_⟩, ⟨hm, white_sharp hq, ?_⟩⟩ <;>
      simp [WallObstruction.KingAdjacent, I]
  · have he : q = p - I - I := by ext <;> simp [I] <;> omega
    subst q
    have hm : Wsharp W (p - I) :=
      Or.inr (Or.inr ⟨hq, by simpa using hp⟩)
    refine ⟨p - I, ⟨white_sharp hp, hm, ?_⟩, ⟨hm, white_sharp hq, ?_⟩⟩ <;>
      simp [WallObstruction.KingAdjacent, I]

theorem r2_reach_king {W : G → Prop} {p q : G} (h : R2Reach W p q) :
    KingReach (Wsharp W) p q := by
  apply h.lift' id
  intro u v huv
  obtain ⟨m, hm, hm'⟩ := r2_edge_bridge huv
  exact (Relation.ReflTransGen.single hm).tail hm'

/-- Exact connectivity, for arbitrary filled-white vertices and their chosen
original-white representatives. -/
theorem reach_iff_anchor {W : G → Prop} {u v : G}
    (hu : Wsharp W u) (hv : Wsharp W v) :
    KingReach (Wsharp W) u v ↔ R2Reach W (anchor W u) (anchor W v) := by
  refine ⟨king_reach_anchor, fun h => ?_⟩
  exact ((r2_reach_king h).head (king_anchor hu)).tail (king_anchor hv).symm

/-- In particular bridge filling neither merges nor splits original-white
components. -/
theorem r2_reach_iff_king {W : G → Prop} {p q : G} (hp : W p) (hq : W q) :
    R2Reach W p q ↔ KingReach (Wsharp W) p q := by
  simpa only [anchor_eq hp, anchor_eq hq] using
    (reach_iff_anchor (white_sharp hp) (white_sharp hq)).symm

/- ## Exact component sets, finite fibers, and infinite components -/

/-- The original-white component of `p`. The white condition excludes spurious
black singletons from the reflexive closure. -/
def R2Component (W : G → Prop) (p : G) : Set G :=
  {q | W q ∧ R2Reach W p q}

/-- The filled-white component of `v`. -/
def SharpComponent (W : G → Prop) (v : G) : Set G :=
  {q | Wsharp W q ∧ KingReach (Wsharp W) v q}

/-- At most three filled vertices can choose any particular anchor: it must be
that vertex, its eastern neighbor, or its northern neighbor. -/
theorem anchor_finite_fiber (W : G → Prop) (z : G) :
    ((anchor W) ⁻¹' {z}).Finite := by
  classical
  apply ({z, z + 1, z + I} : Finset G).finite_toSet.subset
  intro v hv
  have he : anchor W v = z := hv
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  cases hk : chosenKind W v
  · exact Or.inl (by simpa [anchor, hk, witness] using he)
  · right; left
    exact sub_eq_iff_eq_add.mp (by simpa [anchor, hk, witness] using he)
  · right; right
    exact sub_eq_iff_eq_add.mp (by simpa [anchor, hk, witness] using he)

/-- The exact inverse-image description of the corresponding filled component. -/
theorem component_eq_preimage {W : G → Prop} {v : G} (hv : Wsharp W v) :
    SharpComponent W v = {q | Wsharp W q} ∩
      (anchor W) ⁻¹' R2Component W (anchor W v) := by
  ext q
  constructor
  · rintro ⟨hq, hr⟩
    exact ⟨hq, anchor_white hq, king_reach_anchor hr⟩
  · rintro ⟨hq, _, hr⟩
    exact ⟨hq, (reach_iff_anchor hv hq).mpr hr⟩

/-- Every corresponding original-white component is exactly the image under
`anchor`, not just a superset of that image. -/
theorem component_anchor_image {W : G → Prop} {v : G} (hv : Wsharp W v) :
    anchor W '' SharpComponent W v = R2Component W (anchor W v) := by
  ext q
  constructor
  · rintro ⟨u, ⟨hu, hr⟩, rfl⟩
    exact ⟨anchor_white hu, king_reach_anchor hr⟩
  · rintro ⟨hq, hr⟩
    refine ⟨q, ⟨white_sharp hq, ?_⟩, anchor_eq hq⟩
    apply (reach_iff_anchor hv (white_sharp hq)).mpr
    simpa only [anchor_eq hq] using hr

/-- On original-white vertices the component sets agree exactly. -/
theorem component_inter_white {W : G → Prop} {p : G} (hp : W p) :
    R2Component W p = SharpComponent W p ∩ {q | W q} := by
  ext q
  constructor
  · rintro ⟨hq, hr⟩
    exact ⟨⟨white_sharp hq, r2_reach_king hr⟩, hq⟩
  · rintro ⟨⟨_, hr⟩, hq⟩
    exact ⟨hq, (r2_reach_iff_king hp hq).mpr hr⟩

/-- Finiteness is preserved in *both* directions, using the finite fibers of
`anchor` in the nontrivial direction. -/
theorem component_finite_iff {W : G → Prop} {v : G} (hv : Wsharp W v) :
    (SharpComponent W v).Finite ↔ (R2Component W (anchor W v)).Finite := by
  constructor
  · intro h
    rw [← component_anchor_image hv]
    exact h.image (anchor W)
  · intro h
    have hf := h.preimage' (fun z _ => anchor_finite_fiber W z)
    apply hf.subset
    rintro q ⟨hq, hr⟩
    exact ⟨anchor_white hq, king_reach_anchor hr⟩

/-- Thus an infinite filled component corresponds to an infinite original R2
component, and conversely. This is stronger than a mere RTC comparison. -/
theorem component_infinite_iff {W : G → Prop} {v : G} (hv : Wsharp W v) :
    (SharpComponent W v).Infinite ↔ (R2Component W (anchor W v)).Infinite :=
  not_congr (component_finite_iff hv)

theorem white_component_infinite_iff {W : G → Prop} {p : G} (hp : W p) :
    (R2Component W p).Infinite ↔ (SharpComponent W p).Infinite := by
  simpa only [anchor_eq hp] using (component_infinite_iff (white_sharp hp)).symm

/- ## Finite-fiber loop erasure and infinite sequences -/

/-- Last-visit loop erasure. An infinite walk with finite vertex fibers has
an injective subwalk, with strictly increasing indices and the same first
vertex. No symmetry, local finiteness, or irreflexivity of `R` is required. -/
theorem exists_injective_subwalk {X : Type*} (R : X → X → Prop) (f : ℕ → X)
    (hstep : ∀ n, R (f n) (f (n + 1)))
    (hfiber : ∀ v, {n | f n = v}.Finite) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ Function.Injective (f ∘ t) ∧
      (∀ n, R (f (t n)) (f (t (n + 1)))) ∧ f (t 0) = f 0 := by
  classical
  have hlast : ∀ n, ∃ m, f m = f n ∧ ∀ k, f k = f n → k ≤ m := by
    intro n
    exact Set.exists_max_image {k | f k = f n} id (hfiber (f n)) ⟨n, rfl⟩
  choose last heq hmax using hlast
  have hle (n) : n ≤ last n := hmax n n rfl
  let t : ℕ → ℕ := Nat.rec (last 0) (fun _ k => last (k + 1))
  have hmono : StrictMono t := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (Nat.lt_succ_self (t n)).trans_le (hle (t n + 1))
  have hterminal : ∀ i k, f k = f (t i) → k ≤ t i := by
    intro i k hk
    cases i with
    | zero => exact hmax 0 k (hk.trans (heq 0))
    | succ i => exact hmax (t i + 1) k (hk.trans (heq (t i + 1)))
  refine ⟨t, hmono, ?_, ?_, heq 0⟩
  · intro i j hij
    apply hmono.injective
    exact le_antisymm (hterminal j (t i) hij) (hterminal i (t j) hij.symm)
  · intro n
    change R (f (t n)) (f (last (t n + 1)))
    rw [heq (t n + 1)]
    exact hstep (t n)

/-- The king neighborhood, including the center, is a finite nine-point box. -/
theorem finite_king_neighbors (v : G) :
    {q | WallObstruction.KingAdjacent v q}.Finite := by
  classical
  apply (((Finset.Icc (v.re - 1) (v.re + 1)) ×ˢ
    (Finset.Icc (v.im - 1) (v.im + 1))).image
      (fun xy : ℤ × ℤ => (⟨xy.1, xy.2⟩ : G))).finite_toSet.subset
  intro q hq
  rcases hq with ⟨hx, hy⟩
  rw [abs_le] at hx hy
  apply Finset.mem_image.mpr
  refine ⟨(q.re, q.im), Finset.mem_product.mpr ?_, by cases q; rfl⟩
  exact ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_Icc.mpr (by omega)⟩

/-- Interleave original vertices with bridge midpoints. -/
def interleave {X : Type*} (f m : ℕ → X) (n : ℕ) : X :=
  if n % 2 = 0 then f (n / 2) else m (n / 2)

@[simp] theorem interleave_even {X : Type*} (f m : ℕ → X) (n : ℕ) :
    interleave f m (2 * n) = f n := by simp [interleave]

@[simp] theorem interleave_odd {X : Type*} (f m : ℕ → X) (n : ℕ) :
    interleave f m (2 * n + 1) = m n := by
  have hdiv : (2 * n + 1) / 2 = n := by omega
  simp [interleave, hdiv]

theorem interleave_steps {X : Type*} (R : X → X → Prop) (f m : ℕ → X)
    (h₀ : ∀ n, R (f n) (m n)) (h₁ : ∀ n, R (m n) (f (n + 1))) :
    ∀ n, R (interleave f m n) (interleave f m (n + 1)) := by
  intro n
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · subst n
    simpa only [interleave_even, interleave_odd] using h₀ k
  · subst n
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    simpa only [interleave_even, interleave_odd] using h₁ k

/-- An interleaved walk whose inserted vertices stay within one king step of
an injective original sequence has finite fibers. Repeated midpoints are
explicitly permitted. -/
theorem interleave_finite_fibers {f m : ℕ → G} (hf : Function.Injective f)
    (hm : ∀ n, WallObstruction.KingAdjacent (f n) (m n)) (v : G) :
    {n | interleave f m n = v}.Finite := by
  have hnear (n) :
      WallObstruction.KingAdjacent (f (n / 2)) (interleave f m n) := by
    unfold interleave
    split
    · exact king_refl _
    · exact hm _
  have hb : {i : ℕ | WallObstruction.KingAdjacent v (f i)}.Finite :=
    (finite_king_neighbors v).preimage hf.injOn
  obtain ⟨M, hM⟩ := hb.bddAbove
  apply (Finset.range (2 * M + 2)).finite_toSet.subset
  intro n hn
  have he : interleave f m n = v := hn
  have hle : n / 2 ≤ M := hM (by
    change WallObstruction.KingAdjacent v (f (n / 2))
    rw [← he]
    exact (hnear n).symm)
  simp only [Finset.mem_coe, Finset.mem_range]
  omega

/-- An injective infinite original R2 sequence yields an injective infinite
filled-white king sequence. Only the final loop-erased sequence is claimed
injective, never the intermediate midpoint-filled walk. -/
theorem infinite_r2_sequence_gives_king {W : G → Prop}
    (h : ∃ f : ℕ → G, Function.Injective f ∧ ∀ n, R2Adj W (f n) (f (n + 1))) :
    ∃ g : ℕ → G, Function.Injective g ∧
      ∀ n, KingAdj (Wsharp W) (g n) (g (n + 1)) := by
  classical
  obtain ⟨f, hf, hs⟩ := h
  choose m hm hm' using fun n => r2_edge_bridge (hs n)
  have hsteps := interleave_steps (KingAdj (Wsharp W)) f m hm hm'
  have hfib := interleave_finite_fibers hf (fun n => (hm n).2.2)
  obtain ⟨t, _, ht, hwalk, _⟩ :=
    exists_injective_subwalk (KingAdj (Wsharp W)) (interleave f m) hsteps hfib
  exact ⟨interleave f m ∘ t, ht, hwalk⟩

/-- The requested generic next-scale obstruction transfer. -/
theorem no_r2_sequence_of_no_sharp_king_sequence {W : G → Prop}
    (h : ¬ ∃ g : ℕ → G, Function.Injective g ∧
      ∀ n, KingAdj (Wsharp W) (g n) (g (n + 1))) :
    ¬ ∃ f : ℕ → G, Function.Injective f ∧ ∀ n, R2Adj W (f n) (f (n + 1)) :=
  fun hf => h (infinite_r2_sequence_gives_king hf)

/-- The same theorem with whiteness and geometry separated, in the signature
used by `WallObstruction`. -/
theorem no_r2_sequence_of_no_white_king {W : G → Prop}
    (h : ¬ ∃ g : ℕ → G, Function.Injective g ∧ (∀ n, Wsharp W (g n)) ∧
      ∀ n, WallObstruction.KingAdjacent (g n) (g (n + 1))) :
    ¬ ∃ f : ℕ → G, Function.Injective f ∧ (∀ n, W (f n)) ∧
      ∀ n, (f (n + 1) - f n).norm ≤ 4 := by
  rintro ⟨f, hf, hw, hs⟩
  obtain ⟨g, hg, hgstep⟩ := infinite_r2_sequence_gives_king
    ⟨f, hf, fun n => ⟨hw n, hw (n + 1), hs n⟩⟩
  exact h ⟨g, hg, fun n => (hgstep n).1, fun n => (hgstep n).2.2⟩

/- ## Black complement and conditional reuse of the wall obstruction -/

/-- The protected black predicate: the exact complement of filled whiteness.
This definition is not a certificate that a wall for this predicate exists. -/
def Bsharp (B : G → Prop) (v : G) : Prop :=
  B v ∧ (B (v - 1) ∨ B (v + 1)) ∧ (B (v - I) ∨ B (v + I))

theorem Bsharp_iff_not_Wsharp (B : G → Prop) (v : G) :
    Bsharp B v ↔ ¬ Wsharp (fun u => ¬ B u) v := by
  classical
  unfold Bsharp Wsharp
  tauto

theorem not_Bsharp_iff_Wsharp (B : G → Prop) (v : G) :
    ¬ Bsharp B v ↔ Wsharp (fun u => ¬ B u) v := by
  classical
  rw [Bsharp_iff_not_Wsharp, not_not]

/-- Rotation preservation of original blackness implies preservation of the
protected predicate, since rotation interchanges the two axial pairs. -/
theorem Bsharp_rotation {B : G → Prop}
    (hR : ∀ v, B v → B (WallObstruction.R v)) :
    ∀ v, Bsharp B v → Bsharp B (WallObstruction.R v) := by
  intro v ⟨hv, hx, hy⟩
  have hxm : WallObstruction.R (v - 1) = WallObstruction.R v - I := by
    ext <;> simp [WallObstruction.R, I]
  have hxp : WallObstruction.R (v + 1) = WallObstruction.R v + I := by
    ext <;> simp [WallObstruction.R, I]
  have hym : WallObstruction.R (v - I) = WallObstruction.R v + 1 := by
    ext <;> simp [WallObstruction.R, I]
    ring
  have hyp : WallObstruction.R (v + I) = WallObstruction.R v - 1 := by
    ext <;> simp [WallObstruction.R, I]
    ring
  refine ⟨hR v hv, ?_, ?_⟩
  · rcases hy with hy | hy
    · exact Or.inr (by simpa only [hym] using hR (v - I) hy)
    · exact Or.inl (by simpa only [hyp] using hR (v + I) hy)
  · rcases hx with hx | hx
    · exact Or.inl (by simpa only [hxm] using hR (v - 1) hx)
    · exact Or.inr (by simpa only [hxp] using hR (v + 1) hx)

/-- Direct interface from the black-predicate formulation of `WallObstruction`
to original-white R2 sequences. -/
theorem no_white_r2_of_no_Bsharp_king {B : G → Prop}
    (h : ¬ ∃ g : ℕ → G, Function.Injective g ∧ (∀ n, ¬ Bsharp B (g n)) ∧
      ∀ n, WallObstruction.KingAdjacent (g n) (g (n + 1))) :
    ¬ ∃ f : ℕ → G, Function.Injective f ∧ (∀ n, ¬ B (f n)) ∧
      ∀ n, (f (n + 1) - f n).norm ≤ 4 := by
  apply no_r2_sequence_of_no_white_king (W := fun w => ¬ B w)
  simpa only [not_Bsharp_iff_Wsharp] using h

/- ## Original coordinates and the exact squared-norm bound eight -/

/-- The usual affine change from wall coordinates to original coordinates.
It is explicitly defined here so no prime-specific certificate is imported. -/
def original (w : G) : G := 1 + (1 + I) * w

/-- An original-coordinate white point is the image of an original-white
wall-lattice point. This makes the lifting hypothesis completely explicit. -/
def OriginalWhite (W : G → Prop) (z : G) : Prop :=
  ∃ w, W w ∧ original w = z

theorem norm_original_sub (u v : G) :
    (original v - original u).norm = 2 * (v - u).norm := by
  have he : original v - original u = (1 + I) * (v - u) := by
    unfold original
    ring
  have hi : (1 + I).norm = 2 := by norm_num [Zsqrtd.norm, I]
  rw [he, Zsqrtd.norm_mul, hi]

/-- Squared original steps at most eight are exactly wall-coordinate R2 steps,
not merely the strict bound below eight handled by unfilled king adjacency. -/
theorem original_step_le_eight_iff (u v : G) :
    (original v - original u).norm ≤ 8 ↔ (v - u).norm ≤ 4 := by
  rw [norm_original_sub]
  omega

/-- Transfer a wall-coordinate R2 obstruction to original-coordinate sequences.
The only lifting assumption is the displayed predicate `OriginalWhite W`. -/
theorem no_original_sequence_of_no_r2 {W : G → Prop}
    (h : ¬ ∃ f : ℕ → G, Function.Injective f ∧ (∀ n, W (f n)) ∧
      ∀ n, (f (n + 1) - f n).norm ≤ 4) :
    ¬ ∃ x : ℕ → G, Function.Injective x ∧ (∀ n, OriginalWhite W (x n)) ∧
      ∀ n, (x (n + 1) - x n).norm ≤ 8 := by
  classical
  rintro ⟨x, hx, hw, hs⟩
  choose f hf heq using hw
  apply h
  refine ⟨f, ?_, hf, ?_⟩
  · intro i j hij
    apply hx
    rw [← heq i, ← heq j, hij]
  · intro n
    apply (original_step_le_eight_iff (f n) (f (n + 1))).mp
    simpa only [heq] using hs n

/-- The desired next-scale original-coordinate conclusion, conditional solely
on the no-white-king conclusion for the protected black predicate. -/
theorem no_original_sequence_of_no_Bsharp_king {B : G → Prop}
    (h : ¬ ∃ g : ℕ → G, Function.Injective g ∧ (∀ n, ¬ Bsharp B (g n)) ∧
      ∀ n, WallObstruction.KingAdjacent (g n) (g (n + 1))) :
    ¬ ∃ x : ℕ → G, Function.Injective x ∧
      (∀ n, OriginalWhite (fun w => ¬ B w) (x n)) ∧
      ∀ n, (x (n + 1) - x n).norm ≤ 8 :=
  no_original_sequence_of_no_r2 (no_white_r2_of_no_Bsharp_king h)

section WallCertificate

open scoped BigOperators

variable {α : Type*} [AddCommGroup α] [Fintype α]

/-- Conditional reuse of the existing wall framework. Crucially the support
hypothesis is `WhiteZero r (Bsharp B)`, NOT `WhiteZero r B`. No such protected
certificate is constructed here. -/
theorem no_r2_sequence_of_protected_wall
    (r : G →+ α) (hr : Function.Surjective r) (p : G) (hp : p ≠ 0)
    (hrp : r p = 0) (hrIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ v, B v → B (WallObstruction.R v))
    (Cx Cy : α → ℤ) (hdiv : WallObstruction.DivergenceFree r Cx Cy)
    (hw : WallObstruction.WhiteZero r (Bsharp B) Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0) :
    ¬ ∃ f : ℕ → G, Function.Injective f ∧ (∀ n, ¬ B (f n)) ∧
      ∀ n, (f (n + 1) - f n).norm ≤ 4 :=
  no_white_r2_of_no_Bsharp_king
    (WallObstruction.no_injective_white_king_sequence_of_black_rotation
      r hr p hp hrp hrIp hker (Bsharp B) (Bsharp_rotation hR) Cx Cy hdiv hw hflux)

/-- A protected-wall certificate excludes original-coordinate squared steps
`≤ 8` on the explicitly lifted white set. This is conditional, and does not
assert a certificate for any particular black predicate or all step bounds. -/
theorem no_original_sequence_of_protected_wall
    (r : G →+ α) (hr : Function.Surjective r) (p : G) (hp : p ≠ 0)
    (hrp : r p = 0) (hrIp : r (I * p) = 0)
    (hker : ∀ u v : G, r u = r v →
      ∃ m n : ℤ, v - u = m • p + n • (I * p))
    (B : G → Prop) (hR : ∀ v, B v → B (WallObstruction.R v))
    (Cx Cy : α → ℤ) (hdiv : WallObstruction.DivergenceFree r Cx Cy)
    (hw : WallObstruction.WhiteZero r (Bsharp B) Cx Cy)
    (hflux : (∑ a : α, Cx a) ≠ 0 ∨ (∑ a : α, Cy a) ≠ 0) :
    ¬ ∃ x : ℕ → G, Function.Injective x ∧
      (∀ n, OriginalWhite (fun w => ¬ B w) (x n)) ∧
      ∀ n, (x (n + 1) - x n).norm ≤ 8 :=
  no_original_sequence_of_no_r2
    (no_r2_sequence_of_protected_wall r hr p hp hrp hrIp hker B hR Cx Cy hdiv hw hflux)

end WallCertificate

/- Kernel dependency audit: only the standard logical axioms are permitted. -/
#print axioms r2_edge_bridge
#print axioms reach_iff_anchor
#print axioms component_infinite_iff
#print axioms exists_injective_subwalk
#print axioms no_r2_sequence_of_no_sharp_king_sequence
#print axioms Bsharp_iff_not_Wsharp
#print axioms no_original_sequence_of_protected_wall

end Erdos952.ProtectedWall
