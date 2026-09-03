import FormalConjecturesUtil
import Submission.CompactFixedFoldAudit

/-! Extremal bounds for copies glued along a common edge. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713EdgeFan
open Finset Erdos713Rate

abbrev Vertex {W : Type*} (x y : W) (t : ℕ) := Bool ⊕ (Fin t × {w : W // w ≠ x ∧ w ≠ y})

def base {W : Type*} (x y : W) {t : ℕ} : Vertex x y t → W :=
  Sum.elim (fun b => if b then y else x) (fun z => z.2.val)

def fan {W : Type*} (H : SimpleGraph W) (x y : W) (t : ℕ) : SimpleGraph (Vertex x y t) where
  Adj a b := H.Adj (base x y a) (base x y b) ∧
    match a, b with
    | Sum.inr (i, _), Sum.inr (j, _) => i = j
    | _, _ => True
  symm := by
    rintro (a | ⟨i,a⟩) (b | ⟨j,b⟩) h
    · exact ⟨h.1.symm, trivial⟩
    · exact ⟨h.1.symm, trivial⟩
    · exact ⟨h.1.symm, trivial⟩
    · exact ⟨h.1.symm, h.2.symm⟩
  loopless a h := H.loopless _ h.1

noncomputable def petalMap {W : Type*} (x y : W) {t : ℕ} (i : Fin t) : W → Vertex x y t := by
  classical
  exact fun w => if h : w = x then Sum.inl false else
    if h' : w = y then Sum.inl true else Sum.inr (i, ⟨w,h,h'⟩)

lemma base_petalMap {W : Type*} {x y : W} (hxy : x ≠ y) {t : ℕ} (i : Fin t) (w : W) :
    base x y (petalMap x y i w) = w := by
  classical
  by_cases hx : w = x <;> by_cases hy : w = y <;> simp [petalMap, base, hx, hy, hxy.symm]

noncomputable def petalCopy {W : Type*} (H : SimpleGraph W) {x y : W} (hxy : x ≠ y)
    {t : ℕ} (i : Fin t) : H.Copy (fan H x y t) := by
  classical
  refine ⟨⟨petalMap x y i, ?_⟩, ?_⟩
  · intro a b hab
    refine ⟨?_, ?_⟩
    · simpa only [base_petalMap hxy] using hab
    · by_cases ha : a = x <;> by_cases ha' : a = y <;>
        by_cases hb : b = x <;> by_cases hb' : b = y <;> simp [petalMap, ha, ha', hb, hb', hxy.symm]
  · change Function.Injective (petalMap x y i)
    intro a b hab
    have hh := congrArg (base x y) hab
    simpa only [base_petalMap hxy] using hh

structure Packing {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V)
    (x y : W) (u v : V) (t : ℕ) where
  copies : Fin t → H.Copy G
  left : ∀ i, copies i x = u
  right : ∀ i, copies i y = v
  disjoint : ∀ i j, i ≠ j → ∀ a b,
    (a ≠ x ∧ a ≠ y) → (b ≠ x ∧ b ≠ y) → copies i a ≠ copies j b

def Packing.empty {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V)
    (x y : W) (u v : V) : Packing H G x y u v 0 where
  copies := Fin.elim0
  left i := Fin.elim0 i
  right i := Fin.elim0 i
  disjoint i := Fin.elim0 i

noncomputable def Packing.blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) : Finset V := by
  classical
  exact univ.biUnion (fun i => (univ.filter (fun a => a ≠ x ∧ a ≠ y)).image (p.copies i))

lemma Packing.mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) {z : V} :
    z ∈ p.blocker ↔ ∃ i a, (a ≠ x ∧ a ≠ y) ∧ p.copies i a = z := by
  classical
  simp [blocker]

lemma Packing.left_not_mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) : u ∉ p.blocker := by
  intro hu
  obtain ⟨i,a,ha,he⟩ := p.mem_blocker.mp hu
  exact ha.1 ((p.copies i).injective (he.trans (p.left i).symm))

lemma Packing.right_not_mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) : v ∉ p.blocker := by
  intro hv
  obtain ⟨i,a,ha,he⟩ := p.mem_blocker.mp hv
  exact ha.2 ((p.copies i).injective (he.trans (p.right i).symm))

lemma Packing.card_blocker_le {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) : p.blocker.card ≤ t * Fintype.card W := by
  classical
  calc
    p.blocker.card ≤ ∑ i : Fin t, ((univ.filter (fun a => a ≠ x ∧ a ≠ y)).image (p.copies i)).card :=
      card_biUnion_le
    _ ≤ ∑ _ : Fin t, Fintype.card W := sum_le_sum fun _ _ =>
      card_image_le.trans ((card_filter_le _ _).trans_eq card_univ)
    _ = _ := by simp

noncomputable def Packing.cons {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) (f : H.Copy G)
    (hfx : f x = u) (hfy : f y = v) (havoid : ∀ a, (a ≠ x ∧ a ≠ y) → f a ∉ p.blocker) :
    Packing H G x y u v (t + 1) where
  copies := Fin.cases f p.copies
  left i := by induction i using Fin.cases <;> simp [hfx, p.left]
  right i := by induction i using Fin.cases <;> simp [hfy, p.right]
  disjoint i j hij a b ha hb := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        intro hab
        exact havoid a ha (p.mem_blocker.mpr ⟨j,b,hb,hab.symm⟩)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        intro hab
        exact havoid b hb (p.mem_blocker.mpr ⟨i,a,ha,hab⟩)
      | succ j =>
        simp only [Fin.cases_succ]
        exact p.disjoint i j (fun h => hij (congrArg Fin.succ h)) a b ha hb

lemma packing_or_blocker {W V : Type*} [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (x y : W) (u v : V) (t : ℕ) : Nonempty (Packing H G x y u v t) ∨
    ∃ B : Finset V, u ∉ B ∧ v ∉ B ∧ B.card ≤ t * Fintype.card W ∧
      ∀ f : H.Copy G, f x = u → f y = v → ∃ a, (a ≠ x ∧ a ≠ y) ∧ f a ∈ B := by
  classical
  induction t with
  | zero => exact Or.inl ⟨Packing.empty H G x y u v⟩
  | succ t ih =>
    rcases ih with hp | ⟨B,hu,hv,hc,hB⟩
    · obtain ⟨p⟩ := hp
      change Packing H G x y u v t at p
      by_cases hh : ∃ f : H.Copy G, f x = u ∧ f y = v ∧ ∀ a, (a ≠ x ∧ a ≠ y) → f a ∉ p.blocker
      · obtain ⟨f,hfx,hfy,havoid⟩ := hh
        exact Or.inl ⟨p.cons f hfx hfy havoid⟩
      · refine Or.inr ⟨p.blocker,p.left_not_mem_blocker,p.right_not_mem_blocker,
          p.card_blocker_le.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)), ?_⟩
        intro f hfx hfy
        have hh' : ¬ ∀ a, (a ≠ x ∧ a ≠ y) → f a ∉ p.blocker := fun hh' => hh ⟨f,hfx,hfy,hh'⟩
        push_neg at hh'
        exact hh'
    · exact Or.inr ⟨B,hu,hv,hc.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)),hB⟩

noncomputable def Packing.toCopy {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    {x y : W} {u v : V} {t : ℕ} (p : Packing H G x y u v t) (hxy : x ≠ y) (ht : 1 ≤ t) :
    (fan H x y t).Copy G := by
  let i0 : Fin t := ⟨0, by omega⟩
  let f : Vertex x y t → V := Sum.elim (fun b => if b then v else u) (fun z => p.copies z.1 z.2.val)
  have hroot (i : Fin t) (b : Bool) : f (Sum.inl b) = p.copies i (base x y (Sum.inl b : Vertex x y t)) := by
    cases b <;> simp [f, base, p.left, p.right]
  refine ⟨⟨f, ?_⟩, ?_⟩
  · rintro (a | ⟨i,a⟩) (b | ⟨j,b⟩) hab
    · rw [hroot i0 a, hroot i0 b]
      exact (p.copies i0).toHom.map_adj hab.1
    · rw [hroot j a]
      exact (p.copies j).toHom.map_adj hab.1
    · rw [hroot i b]
      exact (p.copies i).toHom.map_adj hab.1
    · have hij : i = j := hab.2
      subst j
      exact (p.copies i).toHom.map_adj hab.1
  · change Function.Injective f
    rintro (a | ⟨i,a⟩) (b | ⟨j,b⟩) hab
    · rw [hroot i0 a, hroot i0 b] at hab
      have hh := (p.copies i0).injective hab
      cases a <;> cases b <;> simp_all [base, Ne.symm hxy]
    · rw [hroot j a] at hab
      have hh := (p.copies j).injective hab
      cases a
      · exact (b.prop.1 (by simpa [base] using hh.symm)).elim
      · exact (b.prop.2 (by simpa [base] using hh.symm)).elim
    · rw [hroot i b] at hab
      have hh := (p.copies i).injective hab
      cases b <;> simp_all [base, a.prop.1, a.prop.2]
    · by_cases hij : i = j
      · subst j
        have hh : a = b := Subtype.ext ((p.copies i).injective hab)
        subst b
        rfl
      · exact (p.disjoint i j hij a b a.prop b.prop hab).elim

lemma blockers_of_free {W V : Type*} [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    {x y : W} (hxy : x ≠ y) {t : ℕ} (ht : 1 ≤ t) (hfree : (fan H x y t).Free G) :
    ∀ u v, ∃ B : Finset V, u ∉ B ∧ v ∉ B ∧ B.card ≤ t * Fintype.card W ∧
      ∀ f : H.Copy G, f x = u → f y = v → ∃ a, (a ≠ x ∧ a ≠ y) ∧ f a ∈ B := by
  intro u v
  rcases packing_or_blocker H G x y u v t with hp | hB
  · obtain ⟨p⟩ := hp
    exact (hfree ⟨p.toCopy hxy ht⟩).elim
  · exact hB


def kept {V : Type*} (B : V → V → Finset V) (σ : V → Bool) (u v : V) : Prop :=
  σ u = true ∧ σ v = true ∧ (∀ z ∈ B u v, σ z = false) ∧ ∀ z ∈ B v u, σ z = false

def keep {V : Type*} (G : SimpleGraph V) (B : V → V → Finset V) (σ : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ kept B σ u v
  symm _ _ h := ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  loopless u h := G.loopless u h.1

lemma keep_le {V : Type*} (G : SimpleGraph V) (B : V → V → Finset V) (σ : V → Bool) :
    keep G B σ ≤ G := fun _ _ h => h.1

open scoped Classical in
lemma pair_survival {V : Type*} [Fintype V] (B : V → V → Finset V) (k : ℕ)
    (hk : ∀ u v, (B u v).card ≤ k) (hb : ∀ u v, u ∉ B u v ∧ v ∉ B u v)
    {u v : V} (huv : u ≠ v) :
    Fintype.card (V → Bool) ≤ 2 ^ (2 * k + 2) * Nat.card {σ : V → Bool // kept B σ u v} := by
  classical
  let D : V → Finset V := fun w => if w = u then B u v else B v u
  have hD (w : V) : (D w).card ≤ k := by dsimp [D]; split_ifs <;> exact hk _ _
  have hDu : D u = B u v := by simp [D]
  have hDv : D v = B v u := by simp [D,huv.symm]
  have hh := Erdos713Blocking.pair_survival D k hD
    (show u ∉ D u by simpa [hDu] using (hb u v).1)
    (show v ∉ D v by simpa [hDv] using (hb v u).1)
    (show v ∉ D u by simpa [hDu] using (hb u v).2)
    (show u ∉ D v by simpa [hDv] using (hb v u).2)
  have hiff : (fun σ => Erdos713Blocking.selected D σ u ∧ Erdos713Blocking.selected D σ v) =
      (fun σ => kept B σ u v) := by
    funext σ
    simp only [Erdos713Blocking.selected, hDu, hDv, kept]
    exact propext (by tauto)
  simpa only [hiff] using hh

open scoped Classical in
lemma edges_le_of_keep_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (B : V → V → Finset V) (k M : ℕ) (hb : ∀ u v, u ∉ B u v ∧ v ∉ B u v)
    (hk : ∀ u v, (B u v).card ≤ k)
    (hM : ∀ σ : V → Bool, (keep G B σ).edgeFinset.card ≤ M) :
    G.edgeFinset.card ≤ 2 ^ (2 * k + 2) * M := by
  classical
  let C := 2 ^ (2 * k + 2)
  let A := Fintype.card (V → Bool)
  let rel : (V → Bool) → Sym2 V → Prop := fun σ e => e ∈ (keep G B σ).edgeFinset
  have hBelow : ∀ e ∈ G.edgeFinset,
      A ≤ C * ((univ : Finset (V → Bool)).bipartiteBelow rel e).card := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj : G.Adj u v := by simpa using he
      have hrel (σ : V → Bool) : rel σ s(u,v) ↔ kept B σ u v := by
        change (s(u,v) ∈ (keep G B σ).edgeFinset) ↔ _
        simp only [mem_edgeFinset, mem_edgeSet, keep, hadj, true_and]
      have hh := pair_survival B k hk hb hadj.ne
      simpa only [A, C, Nat.card_eq_fintype_card, Fintype.card_subtype, bipartiteBelow, hrel] using hh
  have hAbove (σ : V → Bool) : (G.edgeFinset.bipartiteAbove rel σ).card ≤ M := by
    apply (card_le_card (show G.edgeFinset.bipartiteAbove rel σ ⊆ (keep G B σ).edgeFinset from ?_)).trans (hM σ)
    intro e he
    exact (mem_filter.mp he).2
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := rel) (s := (univ : Finset (V → Bool))) (t := G.edgeFinset)
  have hCount : G.edgeFinset.card * A ≤ C * (A * M) := by
    calc
      G.edgeFinset.card * A = ∑ _e ∈ G.edgeFinset, A := by simp
      _ ≤ ∑ e ∈ G.edgeFinset, C * ((univ : Finset (V → Bool)).bipartiteBelow rel e).card :=
        sum_le_sum hBelow
      _ = C * ∑ σ : V → Bool, (G.edgeFinset.bipartiteAbove rel σ).card := by
        rw [← mul_sum, ← hsum]
      _ ≤ C * ∑ _σ : V → Bool, M := Nat.mul_le_mul_left C (sum_le_sum fun σ _ => hAbove σ)
      _ = C * (A * M) := by simp [A]
  have hA : 0 < A := Fintype.card_pos
  exact Nat.le_of_mul_le_mul_left
    (show A * G.edgeFinset.card ≤ A * (C * M) by nlinarith only [hCount]) hA

open scoped Classical in
lemma free_edge_bound {W V : Type*} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) {x y : W} (hxy : H.Adj x y)
    {t : ℕ} (ht : 1 ≤ t) (hfree : (fan H x y t).Free G) :
    G.edgeFinset.card ≤ 2 ^ (2 * (t * Fintype.card W) + 2) *
      (extremalNumber (Fintype.card V) H + Fintype.card W * Fintype.card V) := by
  classical
  choose B hleft hright hk hB using blockers_of_free H G hxy.ne ht hfree
  apply edges_le_of_keep_bound G B (t * Fintype.card W) _ (fun u v => ⟨hleft u v, hright u v⟩) hk
  intro σ
  let S : Set V := {v | σ v = true}
  have hS : (keep G B σ).support ⊆ S := by
    rintro v ⟨w,hvw⟩
    exact hvw.2.1
  apply Erdos713Support.edges_le_of_free_induce H (keep G B σ) S hS
  rintro ⟨f⟩
  let g : H.Copy G := (Copy.ofLE _ _ (keep_le G B σ)).comp ((Copy.induce _ S).comp f)
  obtain ⟨a, _, ha⟩ := hB (g x) (g y) g rfl rfl
  have hkeep : kept B σ (g x) (g y) := (f.toHom.map_adj hxy).2
  have hfalse : σ (g a) = false := hkeep.2.2.1 (g a) ha
  have htrue : σ (g a) = true := (f a).prop
  exact Bool.noConfusion (htrue.symm.trans hfalse)

open scoped Classical in
lemma extremal_bound {W : Type*} [Fintype W] (H : SimpleGraph W)
    {x y : W} (hxy : H.Adj x y) {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    extremalNumber n (fan H x y t) ≤ 2 ^ (2 * (t * Fintype.card W) + 2) *
      (extremalNumber n H + Fintype.card W * n) := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hfree
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using free_edge_bound H G hxy ht hfree

lemma upper {W : Type*} [Fintype W] (H : SimpleGraph W)
    {x y : W} (hxy : H.Adj x y) {t : ℕ} (ht : 1 ≤ t) {r : ℝ} (hr : 1 ≤ r)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r)) :
    (fun n : ℕ => (extremalNumber n (fan H x y t) : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ r) := by
  let C : ℕ := 2 ^ (2 * (t * Fintype.card W) + 2)
  apply IsBigO.trans _ ((hH.add (cast_linear_bigO hr (Fintype.card W))).const_mul_left (C : ℝ))
  apply IsBigO.of_bound 1
  filter_upwards with n
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast extremal_bound H hxy ht n

lemma rate {W : Type*} [Fintype W] (H : SimpleGraph W)
    {x y : W} (hxy : H.Adj x y) {t : ℕ} (ht : 1 ≤ t) {r : ℝ} (h : HasRate H r) :
    HasRate (fan H x y t) r := by
  refine ⟨h.one_le, upper H hxy ht h.one_le h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO ⟨petalCopy H hxy.ne ⟨0,by omega⟩⟩).trans hA)

lemma rate_of_sandwich {W U : Type*} [Fintype W] (J : SimpleGraph W)
    {x y : W} (hxy : J.Adj x y) {t : ℕ} (ht : 1 ≤ t)
    {H : SimpleGraph U} (hlo : J ⊑ H) (hhi : H ⊑ fan J x y t) {r : ℝ} (h : HasRate J r) :
    HasRate H r := by
  refine ⟨h.one_le, (extremal_mono_bigO hhi).trans (upper J hxy ht h.one_le h.upper), ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO hlo).trans hA)

lemma rate_of_sandwich_converse {W U : Type*} [Fintype W] (J : SimpleGraph W)
    {x y : W} (hxy : J.Adj x y) {t : ℕ} (ht : 1 ≤ t)
    {H : SimpleGraph U} (hlo : J ⊑ H) (hhi : H ⊑ fan J x y t) {r : ℝ} (h : HasRate H r) :
    HasRate J r := by
  refine ⟨h.one_le, (extremal_mono_bigO hlo).trans h.upper, ?_⟩
  intro a ha hA
  exact h.lower a ha ((extremal_mono_bigO hhi).trans (upper J hxy ht ha hA))


end Erdos713EdgeFan

