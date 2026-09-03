import FormalConjecturesUtil
import Submission.ThetaColumnSplitting
import Submission.GlobalLightPairs

/-! Disjoint copies with degree-two rows completing cross-copy pairs.
This does not assert realization as links of a single extremal host. -/
open Finset
namespace Erdos713ThetaCross
open Erdos713ThetaGram Erdos713ThetaSplit Erdos713GlobalLight
variable {A B I : Type*}

abbrev Cols (I B : Type*) := I × B
abbrev Fillers (I B : Type*) := (Cols I B × Cols I B) × Fin 3
abbrev Rows (I A B : Type*) := (I × A) ⊕ Fillers I B

def complete (R : A → B → Prop) : Rows I A B → Cols I B → Prop
  | .inl a, b => a.1 = b.1 ∧ R a.2 b.2
  | .inr p, b => p.1.1.1 ≠ p.1.2.1 ∧ (b = p.1.1 ∨ b = p.1.2)

lemma old_of_three {R : A → B → Prop} {a : Rows I A B} {x y z : Cols I B}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : complete R a x) (hy : complete R a y) (hz : complete R a z) :
    ∃ p : I × A, a = .inl p := by
  cases a with
  | inl p => exact ⟨p,rfl⟩
  | inr p =>
    obtain ⟨_,hx⟩ := hx
    obtain ⟨_,hy⟩ := hy
    obtain ⟨_,hz⟩ := hz
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      rcases hz with rfl | rfl <;> simp_all

lemma old_of_same_block {R : A → B → Prop} {a : Rows I A B} {x y : Cols I B}
    (hxy : x ≠ y) (hi : x.1 = y.1) (hx : complete R a x) (hy : complete R a y) :
    ∃ p : I × A, a = .inl p := by
  cases a with
  | inl p => exact ⟨p,rfl⟩
  | inr p =>
    obtain ⟨hp,hx⟩ := hx
    obtain ⟨_,hy⟩ := hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

lemma complete_no_theta {R : A → B → Prop} (hf : ¬ HasTheta R) :
    ¬ HasTheta (complete (I := I) R) := by
  rintro ⟨f,g,hfi,hgi,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hne (i j : Fin 4) (hij : i ≠ j) : g i ≠ g j := fun h => hij (hgi h)
  obtain ⟨a,ha⟩ := old_of_three (hne 0 1 (by decide)) (hne 0 2 (by decide))
    (hne 1 2 (by decide)) h00 h01 h02
  obtain ⟨b,hb⟩ := old_of_three (hne 0 1 (by decide)) (hne 0 3 (by decide))
    (hne 1 3 (by decide)) h10 h11 h13
  rw [ha] at h00 h01 h02
  rw [hb] at h10 h11 h13
  have hab : a.1 = b.1 := h00.1.trans h10.1.symm
  have h23i : (g 2).1 = (g 3).1 := h02.1.symm.trans (hab.trans h13.1)
  obtain ⟨c,hc⟩ := old_of_same_block (hne 2 3 (by decide)) h23i h22 h23
  rw [hc] at h22 h23
  have hac : a.1 = c.1 := h02.1.trans h22.1.symm
  let f' : Fin 3 → A := ![a.2,b.2,c.2]
  let g' : Fin 4 → B := fun j => (g j).2
  have hmap (i : Fin 3) : f i = .inl (a.1,f' i) := by
    fin_cases i
    · simpa [f'] using ha
    · change f 1 = .inl (a.1,b.2)
      exact hb.trans (congrArg Sum.inl (Prod.ext hab.symm rfl))
    · change f 2 = .inl (a.1,c.2)
      exact hc.trans (congrArg Sum.inl (Prod.ext hac.symm rfl))
  have hmapg (i : Fin 4) : g i = (a.1,g' i) := by
    refine Prod.ext ?_ rfl
    fin_cases i
    · exact h00.1.symm
    · exact h01.1.symm
    · exact h02.1.symm
    · exact h13.1.symm.trans hab.symm
  have hfi' : Function.Injective f' := by
    intro i j he
    apply hfi
    rw [hmap,hmap,he]
  have hgi' : Function.Injective g' := by
    intro i j he
    apply hgi
    rw [hmapg,hmapg,he]
  exact hf ⟨f',g',hfi',hgi',h00.2,h10.2,h01.2,h11.2,h02.2,h22.2,h13.2,h23.2⟩

lemma cross_heavy [Fintype A] [Fintype B] [Fintype I] (R : A → B → Prop)
    (x y : Cols I B) (hi : x.1 ≠ y.1) : 3 ≤ codegree (complete R) x y := by
  let f : Fin 3 → {a : Rows I A B // complete R a x ∧ complete R a y} :=
    fun j => ⟨.inr ((x,y),j),⟨hi,Or.inl rfl⟩,⟨hi,Or.inr rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j he
    have hh := Sum.inr.inj (congrArg Subtype.val he)
    exact congrArg Prod.snd hh
  have hh := Nat.card_le_card_of_injective f hf
  simpa [codegree] using hh

noncomputable def lightCount [Fintype B] (R : A → B → Prop) : ℕ :=
  Nat.card {p : B × B // codegree R p.1 p.2 ≤ 2}

lemma lightCount_le [Fintype A] [Fintype B] [Fintype I] (R : A → B → Prop) :
    lightCount (complete (I := I) R) ≤ Nat.card I*(Nat.card B)^2 := by
  classical
  let T := {p : Cols I B × Cols I B // codegree (complete R) p.1 p.2 ≤ 2}
  have heq (p : T) : p.val.1.1 = p.val.2.1 := by
    by_contra hh
    have hc := cross_heavy R p.val.1 p.val.2 hh
    have hp := p.property
    omega
  let f : T → I × (B × B) := fun p => (p.val.1.1,p.val.1.2,p.val.2.2)
  have hf : Function.Injective f := by
    intro p q hpq
    have hi := congrArg Prod.fst hpq
    have hj := congrArg (fun z : I × (B × B) => z.2.1) hpq
    have hk := congrArg (fun z : I × (B × B) => z.2.2) hpq
    apply Subtype.ext
    exact Prod.ext (Prod.ext hi hj) (Prod.ext ((heq p).symm.trans (hi.trans (heq q))) hk)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [lightCount,T,Nat.card_prod,pow_two] using hh

lemma rows_card [Fintype A] [Fintype B] [Fintype I] :
    Nat.card (Rows I A B) = Nat.card I*Nat.card A+3*(Nat.card I)^2*(Nat.card B)^2 := by
  simp only [Rows,Fillers,Cols,Nat.card_sum,Nat.card_prod,Nat.card_fin]
  ring

lemma edges_lower [Fintype A] [Fintype B] [Fintype I] (R : A → B → Prop) :
    Nat.card I * Nat.card {p : A × B // R p.1 p.2} ≤
      Nat.card {p : Rows I A B × Cols I B // complete R p.1 p.2} := by
  let f : I × {p : A × B // R p.1 p.2} →
      {p : Rows I A B × Cols I B // complete R p.1 p.2} :=
    fun p => ⟨(.inl (p.1,p.2.val.1),(p.1,p.2.val.2)),rfl,p.2.property⟩
  have hf : Function.Injective f := by
    intro p q he
    have hrow := Sum.inl.inj (congrArg (fun z => z.val.1) he)
    have hcol := congrArg (fun z => z.val.2.2) he
    apply Prod.ext
    · exact congrArg (fun z : I × A => z.1) hrow
    · exact Subtype.ext (Prod.ext (congrArg (fun z : I × A => z.2) hrow) hcol)
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

lemma column_le [Fintype A] [Fintype B] [Fintype I] (R : A → B → Prop) (D : ℕ)
    (hD : ∀ b, Nat.card {a // R a b} ≤ D) (c : Cols I B) :
    Nat.card {a : Rows I A B // complete R a c} ≤ D+6*Nat.card I*Nat.card B := by
  classical
  let T := {a : A // R a c.2} ⊕ ((Cols I B × Fin 3) ⊕ (Cols I B × Fin 3))
  let f : {a : Rows I A B // complete R a c} → T := fun a =>
    match a with
    | ⟨.inl p,hp⟩ => .inl ⟨p.2,hp.2⟩
    | ⟨.inr p,hp⟩ => if c=p.1.1 then .inr (.inl (p.1.2,p.2)) else .inr (.inr (p.1.1,p.2))
  have hf : Function.Injective f := by
    rintro ⟨p,hp⟩ ⟨q,hq⟩ he
    cases p with
    | inl p =>
      cases q with
      | inl q =>
        apply Subtype.ext
        have he' : p.2 = q.2 := congrArg Subtype.val (Sum.inl.inj he)
        exact congrArg Sum.inl (Prod.ext (hp.1.trans hq.1.symm) he')
      | inr q => dsimp [f] at he; split_ifs at he <;> cases he
    | inr p =>
      cases q with
      | inl q => dsimp [f] at he; split_ifs at he <;> cases he
      | inr q =>
        apply Subtype.ext
        dsimp only [f] at he
        by_cases hpc : c=p.1.1 <;> by_cases hqc : c=q.1.1
        · simp only [if_pos hpc,if_pos hqc] at he
          have hh := Sum.inl.inj (Sum.inr.inj he)
          apply congrArg Sum.inr
          apply Prod.ext
          · exact Prod.ext (hpc.symm.trans hqc) (congrArg (fun z : Cols I B × Fin 3 => z.1) hh)
          · exact congrArg (fun z : Cols I B × Fin 3 => z.2) hh
        · simp only [if_pos hpc,if_neg hqc] at he
          cases (Sum.inr.inj he)
        · simp only [if_neg hpc,if_pos hqc] at he
          cases (Sum.inr.inj he)
        · simp only [if_neg hpc,if_neg hqc] at he
          have hh := Sum.inr.inj (Sum.inr.inj he)
          have hp' : c = p.1.2 := hp.2.resolve_left hpc
          have hq' : c = q.1.2 := hq.2.resolve_left hqc
          apply congrArg Sum.inr
          apply Prod.ext
          · exact Prod.ext (congrArg (fun z : Cols I B × Fin 3 => z.1) hh) (hp'.symm.trans hq')
          · exact congrArg (fun z : Cols I B × Fin 3 => z.2) hh
  have hh := Nat.card_le_card_of_injective f hf
  have ht : Nat.card T = Nat.card {a : A // R a c.2}+6*Nat.card I*Nat.card B := by
    simp only [T,Cols,Nat.card_sum,Nat.card_prod,Nat.card_fin]
    ring
  rw [ht] at hh
  exact hh.trans (Nat.add_le_add_right (hD c.2) _)

#print axioms complete_no_theta
#print axioms cross_heavy
#print axioms lightCount_le
#print axioms rows_card
#print axioms edges_lower
#print axioms column_le
end Erdos713ThetaCross
