import FormalConjecturesUtil

/-! A finite Cauchy--Schwarz bound for collision counts after adding a label. -/
namespace Erdos322Research.FiniteCollisionEnergy

open Finset
open scoped Classical
set_option Elab.async false

noncomputable def energy {α β : Type*} (S : Finset α) (f : α → β) : ℕ := by
  classical
  exact ((S ×ˢ S).filter (fun p => f p.1=f p.2)).card

lemma energy_def {α β : Type*} [DecidableEq β] (S : Finset α) (f : α → β) :
    energy S f=((S ×ˢ S).filter (fun p => f p.1=f p.2)).card := by
  classical
  unfold energy
  congr 1
  ext p
  simp only [Finset.mem_filter]

lemma energy_eq_sum {α β : Type*}
    (S : Finset α) (f : α → β) (T : Finset β) (hf : ∀ a ∈ S, f a ∈ T) :
    energy S f=∑ t ∈ T, ((S.filter (fun a => f a=t)).card)^2 := by
  classical
  let P := (S ×ˢ S).filter (fun p => f p.1=f p.2)
  have hh : ∀ p ∈ P, f p.1 ∈ T := by
    intro p hp
    exact hf p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  change P.card=_
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => f p.1) (s := P) (t := T) hh]
  apply Finset.sum_congr rfl
  intro t ht
  have he : P.filter (fun p => f p.1=t)=
      (S.filter (fun a => f a=t)) ×ˢ (S.filter (fun a => f a=t)) := by
    ext p
    simp only [P,Finset.mem_filter,Finset.mem_product]
    aesop
  rw [he,Finset.card_product,pow_two]

/-- Partitioning by a label with `r` values costs at most a factor `r`
in collision energy. -/
theorem energy_le_label_card_mul {α β ι : Type*} [Fintype ι]
    (S : Finset α) (f : α → β) (h : α → ι) :
    energy S f ≤ Fintype.card ι * energy S (fun a => (f a,h a)) := by
  classical
  let T := S.image f
  have hf : ∀ a ∈ S, f a ∈ T := fun a ha => Finset.mem_image.mpr ⟨a,ha,rfl⟩
  rw [energy_eq_sum S f T hf]
  have hp : ∀ a ∈ S, (f a,h a) ∈ T ×ˢ (Finset.univ : Finset ι) := by
    intro a ha
    exact Finset.mem_product.mpr ⟨hf a ha,Finset.mem_univ _⟩
  rw [energy_eq_sum S (fun a => (f a,h a)) (T ×ˢ Finset.univ) hp,
    Finset.sum_product,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  let A := S.filter (fun a => f a=t)
  have hc : A.card=∑ i : ι, (A.filter (fun a => h a=i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (h a))
  change A.card^2 ≤ _
  rw [hc]
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : ι => (A.filter (fun a => h a=i)).card)
  simp only [Finset.card_univ,Nat.cast_id] at hCS
  convert hCS using 1
  congr 2
  funext i
  congr 2
  ext a
  simp only [A,Finset.mem_filter,Prod.mk.injEq]
  tauto

lemma energy_le_card_mul_max_fiber {α β : Type*}
    (S : Finset α) (f : α → β) (M : ℕ)
    (hf : ∀ t, (S.filter (fun a => f a=t)).card ≤ M) :
    energy S f ≤ S.card*M := by
  classical
  have hsum : energy S f=∑ a ∈ S, (S.filter (fun b => f a=f b)).card := by
    unfold energy
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
      (by intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
    apply Finset.sum_congr rfl
    intro a ha
    have he : ((S ×ˢ S).filter (fun p => f p.1=f p.2)).filter (fun p => p.1=a)=
        {a} ×ˢ (S.filter (fun b => f a=f b)) := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_singleton]
      aesop
    rw [he,Finset.card_product,Finset.card_singleton,one_mul]
  rw [hsum]
  calc
    ∑ a ∈ S, (S.filter (fun b => f a=f b)).card ≤ ∑ _a ∈ S, M := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [eq_comm] using hf (f a)
    _ = S.card*M := by simp

end Erdos322Research.FiniteCollisionEnergy
