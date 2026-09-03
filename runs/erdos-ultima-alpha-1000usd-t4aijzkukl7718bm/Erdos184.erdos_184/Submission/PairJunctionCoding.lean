import Submission.JunctionCounts

/-! Encoding vertices with exactly two color incidences by an ordered color
pair and one of two slots. The construction is independent of cyclic orders. -/
open scoped Classical
namespace Erdos184Work.PairJunctionCoding
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

abbrev PairIndex (l : ℕ) := {p : Fin l × Fin l // p.1 < p.2}

def pairSet {l : ℕ} (p : PairIndex l) : Finset (Fin l) := {p.val.1,p.val.2}

lemma pairSet_card {l : ℕ} (p : PairIndex l) : (pairSet p).card = 2 :=
  Finset.card_pair (ne_of_lt p.property)

lemma pairSet_injective (l : ℕ) : Function.Injective (@pairSet l) := by
  intro p q he
  have h1 : p.val.1 ∈ pairSet q := he ▸ (by simp [pairSet])
  have h2 : p.val.2 ∈ pairSet q := he ▸ (by simp [pairSet])
  simp only [pairSet,Finset.mem_insert,Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact (ne_of_lt p.property (h1.trans h2.symm)).elim
  · exact Subtype.ext (Prod.ext h1 h2)
  · have hp := p.property
    rw [h1,h2] at hp
    exact (lt_asymm hp q.property).elim
  · exact (ne_of_lt p.property (h1.trans h2.symm)).elim

lemma exists_pair_of_card_two {l : ℕ} (s : Finset (Fin l)) (hs : s.card = 2) :
    ∃ p : PairIndex l, pairSet p = s := by
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hs
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨⟨(i,j),h⟩,rfl⟩
  · exact ⟨⟨(j,i),h⟩,Finset.pair_comm _ _⟩

def slot {l : ℕ} : PairIndex l × Fin 2 ↪ Fin ((l*l)*2) where
  toFun z := finProdFinEquiv (finProdFinEquiv z.1.val,z.2)
  inj' := by
    intro x y h
    have he := finProdFinEquiv.injective h
    have hp := finProdFinEquiv.injective (congrArg Prod.fst he)
    have hr : x.2 = y.2 := congrArg (fun z : Fin (l*l) × Fin 2 => z.2) he
    exact Prod.ext (Subtype.ext hp) hr

def decodedPair {l : ℕ} (z : Fin ((l*l)*2)) : Fin l × Fin l :=
  finProdFinEquiv.symm (finProdFinEquiv.symm z).1

lemma decodedPair_slot {l : ℕ} (p : PairIndex l) (j : Fin 2) :
    decodedPair (slot (p,j)) = p.val := by
  simp [decodedPair,slot]

section Family
variable {J : Type*} [Fintype J] {l : ℕ}
    (inc : J → Finset (Fin l)) (htwo : ∀ x, (inc x).card = 2)

noncomputable def pair (x : J) : PairIndex l :=
  (exists_pair_of_card_two (inc x) (htwo x)).choose

lemma pairSet_pair (x : J) : pairSet (pair inc htwo x) = inc x :=
  (exists_pair_of_card_two (inc x) (htwo x)).choose_spec

lemma mem_pair (x : J) (i : Fin l) :
    i ∈ inc x ↔ i = (pair inc htwo x).val.1 ∨ i = (pair inc htwo x).val.2 := by
  rw [← pairSet_pair inc htwo x]
  simp only [pairSet,Finset.mem_insert,Finset.mem_singleton]

lemma pair_eq_iff (x : J) (p : PairIndex l) :
    pair inc htwo x = p ↔ p.val.1 ∈ inc x ∧ p.val.2 ∈ inc x := by
  constructor
  · intro h
    rw [← pairSet_pair inc htwo x,h]
    simp [pairSet]
  · intro h
    apply pairSet_injective l
    rw [pairSet_pair]
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      by_contra hn
      have hs : pairSet p ⊂ inc x := Finset.ssubset_iff_subset_ne.mpr ⟨by
        intro j hj
        simp only [pairSet,Finset.mem_insert,Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> tauto,
        by intro he; exact hn (he ▸ hi)⟩
      have hc := Finset.card_lt_card hs
      rw [pairSet_card,htwo] at hc
      omega
    · rw [pairSet_card,htwo]

noncomputable def fiberEquiv (p : PairIndex l) :
    {x : J // pair inc htwo x = p} ≃ {x : J // p.val.1 ∈ inc x ∧ p.val.2 ∈ inc x} :=
  Equiv.subtypeEquivRight (fun x => pair_eq_iff inc htwo x p)

noncomputable def multiplicity (p : PairIndex l) : ℕ := Fintype.card {x : J // pair inc htwo x = p}

lemma multiplicity_eq (p : PairIndex l) : multiplicity inc htwo p =
    Fintype.card {x : J // p.val.1 ∈ inc x ∧ p.val.2 ∈ inc x} :=
  Fintype.card_congr (fiberEquiv inc htwo p)

noncomputable def fiberNumbering : J ≃ (Σ p : PairIndex l, Fin (multiplicity inc htwo p)) :=
  (Equiv.sigmaFiberEquiv (pair inc htwo)).symm.trans
    (Equiv.sigmaCongrRight fun p => Fintype.equivFin {x : J // pair inc htwo x = p})

lemma fiberNumbering_fst (x : J) : (fiberNumbering inc htwo x).1 = pair inc htwo x := rfl

variable (hbound : ∀ p, multiplicity inc htwo p ≤ 2)

noncomputable def coding : J ↪ Fin ((l*l)*2) :=
  (fiberNumbering inc htwo).toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl (PairIndex l))
      (fun p => Fin.castLEEmb (hbound p))).trans
      ((Equiv.sigmaEquivProd (PairIndex l) (Fin 2)).toEmbedding.trans slot))

lemma coding_eq (x : J) : coding inc htwo hbound x =
    slot ((fiberNumbering inc htwo x).1,
      Fin.castLE (hbound (fiberNumbering inc htwo x).1) (fiberNumbering inc htwo x).2) := rfl

lemma coding_pair (x : J) : decodedPair (coding inc htwo hbound x) = (pair inc htwo x).val := by
  rw [coding_eq,decodedPair_slot,fiberNumbering_fst]

lemma coding_incidence (x : J) (i : Fin l) : i ∈ inc x ↔
    i = (decodedPair (coding inc htwo hbound x)).1 ∨
    i = (decodedPair (coding inc htwo hbound x)).2 := by
  rw [coding_pair]
  exact mem_pair inc htwo x i

lemma coding_fiber_inverse (p : PairIndex l) (r : Fin (multiplicity inc htwo p)) :
    coding inc htwo hbound ((fiberNumbering inc htwo).symm ⟨p,r⟩) =
      slot (p,Fin.castLE (hbound p) r) := by
  rw [coding_eq,(fiberNumbering inc htwo).apply_symm_apply]

lemma slot_mem_range (p : PairIndex l) (r : Fin 2) :
    slot (p,r) ∈ Set.range (coding inc htwo hbound) ↔ r.val < multiplicity inc htwo p := by
  constructor
  · rintro ⟨x,hx⟩
    rw [coding_eq] at hx
    have he := slot.injective hx
    have hp := congrArg Prod.fst he
    change (fiberNumbering inc htwo x).1 = p at hp
    have hr := congrArg (fun z : PairIndex l × Fin 2 => z.2.val) he
    have hb := (fiberNumbering inc htwo x).2.isLt
    change (fiberNumbering inc htwo x).2.val = r.val at hr
    rwa [hr,hp] at hb
  · intro hr
    refine ⟨(fiberNumbering inc htwo).symm ⟨p,⟨r.val,hr⟩⟩,?_⟩
    rw [coding_fiber_inverse]
    rfl

#print axioms coding_incidence
#print axioms slot_mem_range
end Family
end Erdos184Work.PairJunctionCoding
