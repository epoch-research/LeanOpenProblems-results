import Submission.UnbalancedBounds

/-! C4-free incidence systems whose edges preserve a color. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714ColoredC4
open Erdos714Packing
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- The integer square-root form of the unbalanced C4 bound. -/
lemma square_row_bound (S : A → Finset B) (q : ℕ) (hq : Fintype.card A ≤ q^2)
    (hf : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence S)) :
    (∑ a, (S a).card) ≤ q*Fintype.card B+Fintype.card A := by
  have h := Erdos714Unbalanced.power_bound S (by decide : 1 ≤ 2) hf
  norm_num at h
  have hh : ((∑ a, (S a).card)-Fintype.card A)^2 ≤ (q*Fintype.card B)^2 := by
    calc
      _ ≤ Fintype.card A*Fintype.card B^2 := h
      _ ≤ q^2*Fintype.card B^2 := Nat.mul_le_mul_right _ hq
      _ = _ := by ring
  have hl := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hh
  omega

def block (S : A → Finset B) (f : A → C) (g : B → C) (c : C)
    (a : {a : A // f a=c}) : Finset {b : B // g b=c} :=
  univ.filter (fun b => b.val ∈ S a.val)

omit [Fintype A] [Fintype C] in
lemma block_free (S : A → Finset B) (f : A → C) (g : B → C) (c : C)
    (hf : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence S)) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence (block S f g c)) := by
  rw [free_iff_no_rectangle _ (by decide)] at hf ⊢
  intro u v huv
  apply hf (u.trans (Function.Embedding.subtype _)) (v.trans (Function.Embedding.subtype _))
  intro i j
  simpa only [block,mem_filter,mem_univ,true_and] using huv i j

omit [Fintype A] [Fintype C] in
lemma block_card (S : A → Finset B) (f : A → C) (g : B → C)
    (hcol : ∀ a b, b ∈ S a → f a=g b) (c : C) (a : {a : A // f a=c}) :
    (block S f g c a).card = (S a.val).card := by
  apply card_nbij Subtype.val
  · intro b hb
    simpa [block] using hb
  · intro b hb d hd hbd
    exact Subtype.ext hbd
  · intro b hb
    have hg : g b=c := (hcol a.val b hb).symm.trans a.property
    exact ⟨⟨b,hg⟩,by simpa [block] using hb,rfl⟩

/-- Partitioning by a preserved color improves the root parameter from the
whole row set to the largest single color class. -/
theorem colored_bound (S : A → Finset B) (f : A → C) (g : B → C)
    (hcol : ∀ a b, b ∈ S a → f a=g b) (q : ℕ)
    (hq : ∀ c, Fintype.card {a : A // f a=c} ≤ q^2)
    (hf : (completeBipartiteGraph (Fin 2) (Fin 2)).Free (incidence S)) :
    (∑ a, (S a).card) ≤ q*Fintype.card B+Fintype.card A := by
  have h (c : C) := square_row_bound (block S f g c) q (hq c) (block_free S f g c hf)
  simp_rw [block_card S f g hcol] at h
  have hh := sum_le_sum (s := (univ : Finset C)) (fun c _ => h c)
  rw [Fintype.sum_fiberwise f (fun a => (S a).card), sum_add_distrib,← mul_sum] at hh
  have hcA : (∑ c, Fintype.card {a : A // f a=c})=Fintype.card A := by
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using
      Fintype.sum_fiberwise f (fun _ => (1 : ℕ))
  have hcB : (∑ c, Fintype.card {b : B // g b=c})=Fintype.card B := by
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using
      Fintype.sum_fiberwise g (fun _ => (1 : ℕ))
  simpa only [hcA,hcB] using hh

#print axioms colored_bound
end Erdos714ColoredC4
