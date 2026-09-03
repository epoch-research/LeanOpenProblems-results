import Submission.TwoValueCore

/-! Exact event compression for Boolean cores with two fixed coordinate
symbols. A minimal-core event depends only on its used coordinates. -/
namespace Erdos7BooleanCoreFootprint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

section
variable {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
variable (A : I → Type*) [∀ i, DecidableEq (A i)]

noncomputable def pair (enc : (i : I) → Fin 2 → A i) (i : I) : Finset (A i) :=
  Finset.univ.image (enc i)

lemma pair_card (enc : (i : I) → Fin 2 → A i) (he : ∀ i, Function.Injective (enc i)) (i : I) :
    (pair A enc i).card = 2 := by
  rw [pair, Finset.card_image_of_injective _ (he i)]
  decide

lemma mem_pair (enc : (i : I) → Fin 2 → A i) (i : I) (x : A i) :
    x ∈ pair A enc i ↔ ∃ v : Fin 2, x = enc i v := by
  simp only [pair,Finset.mem_image,Finset.mem_univ,true_and]
  exact exists_congr fun v => eq_comm

/-- Coverage and irredundance of a subfamily on a selected product. -/
def MinimalEvent (S : J → Finset I) (b : J → I → Fin 2)
    (enc : (i : I) → Fin 2 → A i) (s : Finset J) (z : (i : I) → Finset (A i)) : Prop :=
  (∀ x : (i : I) → A i, (∀ i, x i ∈ z i) →
    ∃ k ∈ s, ∀ i ∈ S k, x i = enc i (b k i)) ∧
  ∀ k ∈ s, ∃ x : (i : I) → A i, (∀ i, x i ∈ z i) ∧
    ∀ l ∈ s, (∀ i ∈ S l, x i = enc i (b l i)) ↔ l=k

/-- A fixed minimal Boolean cover, with injectively encoded symbols, occurs
as a minimal cover of a two-value product exactly when each used coordinate
selects its two prescribed symbols. Unused coordinates are unrestricted. -/
theorem minimal_event_iff (S : J → Finset I) (b : J → I → Fin 2) (s : Finset J)
    (hc : ∀ x : I → Fin 2, ∃ k ∈ s, ∀ i ∈ S k, x i = b k i)
    (hpriv : ∀ k ∈ s, ∃ x : I → Fin 2, ∀ l ∈ s,
      (∀ i ∈ S l, x i = b l i) ↔ l=k)
    (enc : (i : I) → Fin 2 → A i) (he : ∀ i, Function.Injective (enc i))
    (z : (i : I) → Finset (A i)) (hz : ∀ i, (z i).card = 2) :
    MinimalEvent A S b enc s z ↔ ∀ i ∈ s.biUnion S, z i = pair A enc i := by
  classical
  have hused (k : J) (hk : k ∈ s) (i : I) (hi : i ∈ S k) : i ∈ s.biUnion S :=
    Finset.mem_biUnion.mpr ⟨k,hk,hi⟩
  have hcov : ∀ x : I → Fin 2, ∃ k : s, ∀ i ∈ S k.val, x i = b k.val i := by
    intro x
    obtain ⟨k,hk,hx⟩ := hc x
    exact ⟨⟨k,hk⟩,hx⟩
  have hpr : ∀ k : s, ∃ x : I → Fin 2, ∀ l : s, l ≠ k →
      ¬ ∀ i ∈ S l.val, x i = b l.val i := by
    intro k
    obtain ⟨x,hx⟩ := hpriv k.val k.property
    refine ⟨x,fun l hl hm => ?_⟩
    exact hl (Subtype.ext ((hx l.val l.property).mp hm))
  have hboth (i : I) (hi : i ∈ s.biUnion S) (v : Fin 2) :
      ∃ k ∈ s, i ∈ S k ∧ b k i = v := by
    obtain ⟨k,hk,hik⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨l,hil,hlv⟩ := Erdos7TwoValueCore.irredundant_all_values (fun _ : I => Fin 2)
      (fun j : s => S j.val) (fun j : s => b j.val) hcov hpr i ⟨⟨k,hk⟩,hik⟩ v
    exact ⟨l.val,l.property,hil,hlv⟩
  constructor
  · intro h i hi
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨r,rfl⟩ := (mem_pair A enc i v).mp hv
      obtain ⟨k,hk,hik,hkv⟩ := hboth i hi r
      obtain ⟨x,hxz,hxp⟩ := h.2 k hk
      have hmatch := (hxp k hk).mpr rfl
      rw [← hkv, ← hmatch i hik]
      exact hxz i
    · rw [hz,pair_card A enc he]
  · intro hpair
    have hn (i : I) : (z i).Nonempty := Finset.card_pos.mp (by rw [hz]; decide)
    choose c hc' using hn
    constructor
    · intro x hx
      have hchoice (i : I) : ∃ r : Fin 2, i ∈ s.biUnion S → x i = enc i r := by
        by_cases hi : i ∈ s.biUnion S
        · have hh : x i ∈ pair A enc i := by rw [← hpair i hi]; exact hx i
          obtain ⟨r,hr⟩ := (mem_pair A enc i (x i)).mp hh
          exact ⟨r,fun _ => hr⟩
        · exact ⟨0,fun h => False.elim (hi h)⟩
      choose u hu using hchoice
      obtain ⟨k,hk,hmatch⟩ := hc u
      refine ⟨k,hk,fun i hi => ?_⟩
      rw [hu i (hused k hk i hi),hmatch i hi]
    · intro k hk
      obtain ⟨u,hu⟩ := hpriv k hk
      let x (i : I) : A i := if i ∈ s.biUnion S then enc i (u i) else c i
      refine ⟨x,?_,?_⟩
      · intro i
        by_cases hi : i ∈ s.biUnion S
        · simp only [x,if_pos hi]
          rw [hpair i hi]
          exact (mem_pair A enc i _).mpr ⟨u i,rfl⟩
        · simpa only [x,if_neg hi] using hc' i
      · intro l hl
        have hh : (∀ i ∈ S l, x i = enc i (b l i)) ↔ ∀ i ∈ S l, u i = b l i := by
          constructor
          · intro h i hi
            apply he i
            simpa only [x,if_pos (hused l hl i hi)] using h i hi
          · intro h i hi
            simp only [x,if_pos (hused l hl i hi),h i hi]
        exact hh.trans (hu l hl)

end
#print axioms minimal_event_iff
end Erdos7BooleanCoreFootprint
