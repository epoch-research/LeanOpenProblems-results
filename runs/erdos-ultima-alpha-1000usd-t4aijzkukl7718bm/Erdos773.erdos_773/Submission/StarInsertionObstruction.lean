import Submission.QuantitativeRotationSpecialization

/-!
One new positive integer root can require deleting a linear fraction of a
Sidon square carrier. The realization has polynomial height. This rules
out a uniform cheap-insertion assertion, not the Erdős 773 conjecture.
-/
namespace Erdos773.StarInsertionObstruction
open Finset QuadraticRotationTrade QuantitativeRotationSpecialization
noncomputable section
set_option maxHeartbeats 2500000

abbrev Vertex (k : ℕ) := Option (Fin k × Fin 3)

def starEdge {k : ℕ} (i : Fin k) : Edge (k+1) :=
  ⟨(0,i.succ),by simp⟩

def embed {k : ℕ} : Vertex k → Root (k+1)
  | none => .core 0
  | some (i,j) => if j=0 then .core i.succ else
      if j=1 then .plus (starEdge i) else .minus (starEdge i)

lemma starEdge_injective {k : ℕ} : Function.Injective (@starEdge k) := by
  intro i j h
  have hh := congrArg (fun e : Edge (k+1) => e.val.2) h
  exact Fin.succ_injective _ hh

lemma embed_injective {k : ℕ} : Function.Injective (@embed k) := by
  intro u v h
  rcases u with _ | ⟨i,j⟩ <;> rcases v with _ | ⟨a,b⟩
  · rfl
  · fin_cases b <;> simp [embed,eq_comm] at h
  · fin_cases j <;> simp [embed] at h
  · fin_cases j <;> fin_cases b <;> simp [embed] at h
    all_goals
      have hi : i=a := by
        first | exact h | exact Fin.succ_injective _ h | exact starEdge_injective h
      subst a
      rfl

lemma embed_not_center {k : ℕ} (i : Fin k) (j : Fin 3) :
    embed (some (i,j)) ≠ Root.core 0 := by
  have hh := @embed_injective k
  intro he
  have : (some (i,j) : Vertex k)=none := hh he
  cases this

lemma plus_in_image {k : ℕ} {e : Edge (k+1)} {i : Fin k} {j : Fin 3}
    (h : embed (some (i,j))=Root.plus e) : e=starEdge i := by
  fin_cases j <;> simp [embed] at h
  exact h.symm

lemma formal_sidon {k : ℕ} (u v w z : Fin k × Fin 3)
    (h : value (embed (some u))+value (embed (some v))=
      value (embed (some w))+value (embed (some z))) :
    (u=w ∧ v=z) ∨ (u=z ∧ v=w) := by
  classical
  rcases pair_classification h with hh | ⟨e,he⟩
  · rcases hh with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨Option.some.inj (embed_injective h₁), Option.some.inj (embed_injective h₂)⟩
    · exact Or.inr ⟨Option.some.inj (embed_injective h₁), Option.some.inj (embed_injective h₂)⟩
  · have hp : Root.plus e ∈ ({embed (some u),embed (some v),embed (some w),embed (some z)} : Finset _) := by
      rw [he]
      simp [support]
    have hs : ∃ i : Fin k, e=starEdge i := by
      simp only [mem_insert,mem_singleton] at hp
      rcases hp with hp | hp | hp | hp
      · exact ⟨u.1,plus_in_image hp.symm⟩
      · exact ⟨v.1,plus_in_image hp.symm⟩
      · exact ⟨w.1,plus_in_image hp.symm⟩
      · exact ⟨z.1,plus_in_image hp.symm⟩
    obtain ⟨i,rfl⟩ := hs
    have hc : Root.core (0 : Fin (k+1)) ∈
        ({embed (some u),embed (some v),embed (some w),embed (some z)} : Finset _) := by
      rw [he]
      simp [support,starEdge]
    simp only [mem_insert,mem_singleton] at hc
    rcases hc with hc | hc | hc | hc
    · exact (embed_not_center u.1 u.2 hc.symm).elim
    · exact (embed_not_center v.1 v.2 hc.symm).elim
    · exact (embed_not_center w.1 w.2 hc.symm).elim
    · exact (embed_not_center z.1 z.2 hc.symm).elim

lemma vertex_card (k : ℕ) : Fintype.card (Vertex k)=3*k+1 := by
  simp [Vertex]
  omega

lemma formal_trade {k : ℕ} (i : Fin k) :
    value (embed (none : Vertex k))+value (embed (some (i,0)))=
      value (embed (some (i,1)))+value (embed (some (i,2))) := by
  simpa [embed,starEdge] using (trade (starEdge i)).symm

/-- For every `k`, a Sidon set of `3*k` positive square roots has an outside
root whose insertion requires at least `k` deletions. All roots have height
at most `28*(2*(3*k+1)^4+1)`. This is not an upper bound on the unrestricted
square-Sidon maximum. -/
theorem insertion_cost (k : ℕ) :
    ∃ x : ℕ, ∃ S : Finset ℕ,
      S.card=3*k ∧ x ∉ S ∧
      (∀ a ∈ insert x S, 0 < a ∧ a ≤ 28*(2*(3*k+1)^4+1)) ∧
      IsSidon (S.image (fun a => a^2) : Set ℕ) ∧
      ∀ T ⊆ S, IsSidon ((insert x T).image (fun a => a^2) : Set ℕ) →
        T.card ≤ 2*k := by
  classical
  obtain ⟨f,hbound,hf,hrel⟩ := bounded_model (@embed k) embed_injective
  have hb (u : Vertex k) : 0 < f u ∧ f u ≤ 28*(2*(3*k+1)^4+1) := by
    simpa only [vertex_card] using hbound u
  let x := f none
  let S : Finset ℕ := univ.image (fun u : Fin k × Fin 3 => f (some u))
  have hfi : Function.Injective (fun u : Fin k × Fin 3 => f (some u)) :=
    hf.comp (Option.some_injective _)
  have hSc : S.card=3*k := by
    rw [card_image_of_injective _ hfi]
    simp
    omega
  have hxS : x ∉ S := by
    intro hx
    obtain ⟨u,_,hu⟩ := mem_image.mp hx
    have hh : (some u : Vertex k)=none := hf hu
    cases hh
  have hs : IsSidon (S.image (fun a => a^2) : Set ℕ) := by
    intro a ha b hb c hc d hd heq
    obtain ⟨a',ha',rfl⟩ := mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := mem_image.mp hb
    obtain ⟨c',hc',rfl⟩ := mem_image.mp hc
    obtain ⟨d',hd',rfl⟩ := mem_image.mp hd
    obtain ⟨u,_,rfl⟩ := mem_image.mp ha'
    obtain ⟨v,_,rfl⟩ := mem_image.mp hb'
    obtain ⟨w,_,rfl⟩ := mem_image.mp hc'
    obtain ⟨z,_,rfl⟩ := mem_image.mp hd'
    have hh := formal_sidon u w v z ((hrel _ _ _ _).mp heq)
    rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  refine ⟨x,S,hSc,hxS,?_,hs,?_⟩
  · intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact hb none
    · obtain ⟨u,_,rfl⟩ := mem_image.mp ha
      exact hb (some u)
  · intro T hTS hT
    have hmiss (i : Fin k) : ∃ j : Fin 3, f (some (i,j)) ∉ T := by
      by_contra! hfull
      have hx : x^2 ∈ ((insert x T).image (fun a => a^2) : Set ℕ) :=
        mem_image.mpr ⟨x,mem_insert_self _ _,rfl⟩
      have hj (j : Fin 3) : f (some (i,j))^2 ∈
          ((insert x T).image (fun a => a^2) : Set ℕ) :=
        mem_image.mpr ⟨_,mem_insert_of_mem (hfull j),rfl⟩
      have hh := hT _ hx _ (hj 1) _ (hj 0) _ (hj 2)
        ((hrel _ _ _ _).mpr (formal_trade i))
      rcases hh with ⟨hh,_⟩ | ⟨hh,_⟩
      all_goals
        have he := hf (Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0) hh)
        cases he
    choose j hj using hmiss
    let g (i : Fin k) := f (some (i,j i))
    have hgi : Function.Injective g := by
      intro i a h
      have hh := Option.some.inj (hf h)
      exact congrArg Prod.fst hh
    have hgsub : univ.image g ⊆ S \ T := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      refine mem_sdiff.mpr ⟨?_,hj i⟩
      exact mem_image.mpr ⟨(i,j i),mem_univ _,rfl⟩
    have hkc := card_le_card hgsub
    rw [card_image_of_injective _ hgi,card_univ,Fintype.card_fin,
      card_sdiff_of_subset hTS,hSc] at hkc
    have htc := card_le_card hTS
    rw [hSc] at htc
    omega

lemma height_bound {k : ℕ} (hk : 1 ≤ k) :
    28*(2*(3*k+1)^4+1) ≤ 15000*k^4 := by
  have h₁ : 3*k+1 ≤ 4*k := by omega
  have h₂ := Nat.pow_le_pow_left h₁ 4
  have h₃ := Nat.pow_le_pow_left hk 4
  norm_num only [one_pow,mul_pow] at h₂ h₃
  nlinarith only [h₂,h₃]

/-- The insertion obstruction also has an integral power-scale certificate:
the fourth power of every adequate deletion set is at least height/15000. -/
theorem deletion_power_obstruction (k : ℕ) (hk : 1 ≤ k) :
    ∃ x : ℕ, ∃ S : Finset ℕ,
      S.card=3*k ∧ x ∉ S ∧
      (∀ a ∈ insert x S, 0 < a ∧ a ≤ 28*(2*(3*k+1)^4+1)) ∧
      IsSidon (S.image (fun a => a^2) : Set ℕ) ∧
      ∀ R ⊆ S, IsSidon ((insert x (S \ R)).image (fun a => a^2) : Set ℕ) →
        k ≤ R.card ∧ 28*(2*(3*k+1)^4+1) ≤ 15000*R.card^4 := by
  classical
  obtain ⟨x,S,hSc,hx,hbound,hs,hcost⟩ := insertion_cost k
  refine ⟨x,S,hSc,hx,hbound,hs,?_⟩
  intro R hR hsidon
  have hc := hcost (S \ R) sdiff_subset hsidon
  rw [card_sdiff_of_subset hR,hSc] at hc
  have hRc := card_le_card hR
  rw [hSc] at hRc
  have hkr : k ≤ R.card := by omega
  refine ⟨hkr,(height_bound hk).trans ?_⟩
  exact Nat.mul_le_mul_left 15000 (Nat.pow_le_pow_left hkr 4)

#print axioms formal_sidon
#print axioms insertion_cost
#print axioms deletion_power_obstruction
end
end Erdos773.StarInsertionObstruction
