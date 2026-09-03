import Submission.Work

/-! Extending finite partial vertex labelings to permutations. -/
namespace Erdos583FinitePortLabelsDevelopment
open scoped Classical
set_option maxHeartbeats 1000000

lemma extend_pair {A B : Type*} [Finite A] (f g : B → A)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : Equiv.Perm A, ∀ b, e (f b)=g b := by
  classical
  let ef := Equiv.ofInjective f hf
  let eg := Equiv.ofInjective g hg
  let e := ef.symm.trans eg
  refine ⟨e.extendSubtype,?_⟩
  intro b
  rw [Equiv.extendSubtype_apply_of_mem e (f b) ⟨b,rfl⟩]
  have hh : (⟨f b,⟨b,rfl⟩⟩ : Set.range f)=ef b := rfl
  rw [hh]
  simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

lemma label_three {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e : Equiv.Perm (Fin 7), e 0=a ∧ e 1=b ∧ e 2=c := by
  let f : Fin 3 → Fin 7 := fun i ↦ ⟨i.val,by omega⟩
  let g : Fin 3 → Fin 7 := ![a,b,c]
  have hf : Function.Injective f := by intro i j he; exact Fin.ext (congrArg (fun x : Fin 7 ↦ x.val) he)
  have hg : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨e,he⟩ := extend_pair f g hf hg
  exact ⟨e,he 0,he 1,he 2⟩

lemma label_four {a b c d : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm (Fin 7), e 0=a ∧ e 1=b ∧ e 2=c ∧ e 3=d := by
  let f : Fin 4 → Fin 7 := fun i ↦ ⟨i.val,by omega⟩
  let g : Fin 4 → Fin 7 := ![a,b,c,d]
  have hf : Function.Injective f := by intro i j he; exact Fin.ext (congrArg (fun x : Fin 7 ↦ x.val) he)
  have hg : Function.Injective g := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨e,he⟩ := extend_pair f g hf hg
  exact ⟨e,he 0,he 1,he 2,he 3⟩


lemma assign_slots {V B I : Type*} [Fintype B] [Fintype I] (port : B → V) (start : I → V)
    (hcap : ∀ v, Fintype.card {b // port b=v} ≤ Fintype.card {i // start i=v}) :
    ∃ slot : B ↪ I, ∀ b, start (slot b)=port b := by
  classical
  let f (v : V) : {b // port b=v} ↪ {i // start i=v} :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hcap v))
  let mid := Function.Embedding.sigmaMap
    (β := fun v ↦ {b // port b=v}) (β' := fun v ↦ {i // start i=v})
    (Function.Embedding.refl V) f
  let slot : B ↪ I := (Equiv.sigmaFiberEquiv port).symm.toEmbedding.trans
    (mid.trans (Equiv.sigmaFiberEquiv start).toEmbedding)
  refine ⟨slot,?_⟩
  intro b
  exact (f (port b) ⟨b,rfl⟩).property

end Erdos583FinitePortLabelsDevelopment
