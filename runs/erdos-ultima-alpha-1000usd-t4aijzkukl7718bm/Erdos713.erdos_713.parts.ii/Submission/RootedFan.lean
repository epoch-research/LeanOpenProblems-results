import FormalConjecturesUtil
import Submission.Verified

/-! Rooted fans: copies of a graph intersecting only at their common root. -/

open Filter SimpleGraph Asymptotics

namespace Erdos713Fan
open Finset
universe u v

abbrev Vertex {W : Type u} (x : W) (t : ℕ) := Option (Fin t × {w : W // w ≠ x})

def fan {W : Type*} (H : SimpleGraph W) (x : W) (t : ℕ) : SimpleGraph (Vertex x t) where
  Adj
    | none, none => False
    | none, some (_, b) => H.Adj x b.val
    | some (_, a), none => H.Adj a.val x
    | some (i, a), some (j, b) => i = j ∧ H.Adj a.val b.val
  symm := by
    rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩)
    · exact id
    · exact H.adj_symm
    · exact H.adj_symm
    · exact fun h => ⟨h.1.symm, h.2.symm⟩
  loopless := by
    rintro (_ | ⟨i, a⟩)
    · exact not_false
    · exact fun h => H.loopless _ h.2

noncomputable def petalCopy {W : Type*} (H : SimpleGraph W) (x : W) {t : ℕ} (i : Fin t) :
    H.Copy (fan H x t) := by
  classical
  let f : W → Vertex x t := fun w => if h : w = x then none else some (i, ⟨w, h⟩)
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro a b hab
    by_cases ha : a = x <;> by_cases hb : b = x
    · subst a; subst b; exact (H.loopless _ hab).elim
    · subst a; simpa [f, fan, hb] using hab
    · subst b; simpa [f, fan, ha] using hab
    · simpa [f, fan, ha, hb] using hab
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = x <;> by_cases hb : b = x
    · exact ha.trans hb.symm
    · simp [f, ha, hb] at hab
    · simp [f, ha, hb] at hab
    · simpa [f, ha, hb] using hab

structure Packing {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (x : W) (v : V) (t : ℕ) where
  copies : Fin t → H.Copy G
  root : ∀ i, copies i x = v
  disjoint : ∀ i j, i ≠ j → ∀ a b, a ≠ x → b ≠ x → copies i a ≠ copies j b

noncomputable def Packing.toCopy {W V : Type*} {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : (fan H x t).Copy G := by
  let f : Vertex x t → V := fun z => match z with
    | none => v
    | some (i, a) => p.copies i a.val
  refine ⟨⟨f, ?_⟩, ?_⟩
  · rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) hab
    · exact hab.elim
    · change G.Adj v (p.copies j b.val)
      have hh : G.Adj (p.copies j x) (p.copies j b.val) := (p.copies j).toHom.map_adj hab
      simpa only [p.root j] using hh
    · change G.Adj (p.copies i a.val) v
      have hh : G.Adj (p.copies i a.val) (p.copies i x) := (p.copies i).toHom.map_adj hab
      simpa only [p.root i] using hh
    · obtain ⟨hij, hab⟩ := hab
      subst j
      exact (p.copies i).toHom.map_adj hab
  · rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) hab
    · rfl
    · change v = p.copies j b.val at hab
      exact (b.prop ((p.copies j).injective ((p.root j).trans hab)).symm).elim
    · change p.copies i a.val = v at hab
      exact (a.prop ((p.copies i).injective (hab.trans (p.root i).symm))).elim
    · change p.copies i a.val = p.copies j b.val at hab
      by_cases hij : i = j
      · subst j
        have hh : a = b := Subtype.ext ((p.copies i).injective hab)
        subst b
        rfl
      · exact (p.disjoint i j hij a b a.prop b.prop hab).elim

def Packing.empty {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) (x : W) (v : V) :
    Packing H G x v 0 where
  copies := Fin.elim0
  root i := Fin.elim0 i
  disjoint i := Fin.elim0 i

noncomputable def Packing.blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : Finset V := by
  classical
  exact univ.biUnion (fun i => (univ.filter (fun a => a ≠ x)).image (p.copies i))

lemma Packing.mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) {z : V} :
    z ∈ p.blocker ↔ ∃ i a, a ≠ x ∧ p.copies i a = z := by
  classical
  simp [blocker]

lemma Packing.root_not_mem_blocker {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : v ∉ p.blocker := by
  rintro hv
  obtain ⟨i, a, ha, hav⟩ := p.mem_blocker.mp hv
  exact ha ((p.copies i).injective (hav.trans (p.root i).symm))

lemma Packing.card_blocker_le {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) : p.blocker.card ≤ t * Fintype.card W := by
  classical
  calc
    p.blocker.card ≤ ∑ i : Fin t, ((univ.filter (fun a => a ≠ x)).image (p.copies i)).card :=
      card_biUnion_le
    _ ≤ ∑ _ : Fin t, Fintype.card W := sum_le_sum fun _ _ =>
      (card_image_le).trans ((card_filter_le _ _).trans_eq (card_univ))
    _ = _ := by simp

noncomputable def Packing.cons {W V : Type*} [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {x : W} {v : V} {t : ℕ} (p : Packing H G x v t) (f : H.Copy G) (hf : f x = v)
    (havoid : ∀ a, a ≠ x → f a ∉ p.blocker) : Packing H G x v (t + 1) where
  copies := Fin.cases f p.copies
  root i := by induction i using Fin.cases <;> simp [hf, p.root]
  disjoint i j hij a b ha hb := by
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        intro hab
        exact havoid a ha (p.mem_blocker.mpr ⟨j, b, hb, hab.symm⟩)
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ]
        intro hab
        exact havoid b hb (p.mem_blocker.mpr ⟨i, a, ha, hab⟩)
      | succ j =>
        simp only [Fin.cases_succ]
        exact p.disjoint i j (fun h => hij (congrArg Fin.succ h)) a b ha hb

theorem packing_or_blocker {W V : Type*} [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (x : W) (v : V) (t : ℕ) : Nonempty (Packing H G x v t) ∨
    ∃ B : Finset V, v ∉ B ∧ B.card ≤ t * Fintype.card W ∧
      ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B := by
  classical
  induction t with
  | zero => exact Or.inl ⟨Packing.empty H G x v⟩
  | succ t ih =>
    rcases ih with hp | ⟨B, hv, hc, hB⟩
    · obtain ⟨p⟩ := hp
      change Packing H G x v t at p
      by_cases h : ∃ f : H.Copy G, f x = v ∧ ∀ a, a ≠ x → f a ∉ p.blocker
      · obtain ⟨f, hf, havoid⟩ := h
        exact Or.inl ⟨p.cons f hf havoid⟩
      · right
        refine ⟨p.blocker, p.root_not_mem_blocker, p.card_blocker_le.trans ?_, ?_⟩
        · exact Nat.mul_le_mul_right _ (Nat.le_succ _)
        · intro f hf
          have hh : ¬∀ a, a ≠ x → f a ∉ p.blocker := fun hh => h ⟨f, hf, hh⟩
          push_neg at hh
          exact hh
    · exact Or.inr ⟨B, hv, hc.trans (Nat.mul_le_mul_right _ (Nat.le_succ _)), hB⟩

theorem blockers_of_fan_free {W V : Type*} [Fintype W] (H : SimpleGraph W) (G : SimpleGraph V)
    (x : W) (t : ℕ) (hfree : (fan H x t).Free G) :
    ∀ v, ∃ B : Finset V, v ∉ B ∧ B.card ≤ t * Fintype.card W ∧
      ∀ f : H.Copy G, f x = v → ∃ a, a ≠ x ∧ f a ∈ B := by
  intro v
  rcases packing_or_blocker H G x v t with hp | hB
  · obtain ⟨p⟩ := hp
    exact (hfree ⟨p.toCopy⟩).elim
  · exact hB

#print axioms blockers_of_fan_free

end Erdos713Fan
