import Submission.Coding

/-!
A parallelogram counting bound for additive codes. The message group and alphabet
may be arbitrary finite abelian groups; no linearity over the alphabet field is
assumed. This rules out a construction approach, not the Erdős 714 conjecture.
-/

set_option maxRecDepth 4096

noncomputable section

open Finset SimpleGraph
open Classical

namespace Erdos714AdditiveCoding

variable {V I A : Type*} [AddCommGroup V] [AddCommGroup A]
  [Fintype V] [Fintype I] [Fintype A]

/-- Fibers of an additive homomorphism are no larger than its kernel. -/
lemma card_le_alphabet_mul_kernel (l : V →+ A) :
    Fintype.card V ≤ Fintype.card A * (univ.filter (fun v => l v = 0)).card := by
  have hf (a : A) : (univ.filter (fun v => l v = a)).card ≤
      (univ.filter (fun v => l v = 0)).card := by
    by_cases hn : (univ.filter (fun v => l v = a)).Nonempty
    · obtain ⟨v₀, hv₀⟩ := hn
      have hv₀' := (mem_filter.mp hv₀).2
      apply card_le_card_of_injOn (fun v => v-v₀)
      · intro v hv
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hv ⊢
        simp [map_sub, hv, hv₀']
      · exact sub_left_injective.injOn
    · simp [not_nonempty_iff_eq_empty.mp hn]
  have hsum : Fintype.card V = ∑ a : A, (univ.filter (fun v => l v = a)).card := by
    simpa using (card_eq_sum_card_fiberwise (s := (univ : Finset V))
      (t := (univ : Finset A)) (f := l) (fun _ _ => mem_univ _))
  rw [hsum]
  calc
    ∑ a : A, (univ.filter (fun v => l v = a)).card ≤
        ∑ _a : A, (univ.filter (fun v => l v = 0)).card := sum_le_sum (fun a _ => hf a)
    _ = _ := by simp

omit [Fintype V] in
/-- Two nondegenerate directions give four distinct codewords in a parallelogram. -/
lemma common_zeros_le_three (f : V →+ (I → A))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => f v i)))
    {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hs : u+v ≠ 0) :
    (univ.filter (fun i => f u i = 0 ∧ f v i = 0)).card ≤ 3 := by
  let g : Fin 4 ↪ V := ⟨![0,u,v,u+v], by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact False.elim (hu h)
      | exact False.elim (hu h.symm)
      | exact False.elim (hv h)
      | exact False.elim (hv h.symm)
      | exact False.elim (huv h)
      | exact False.elim (huv h.symm)
      | exact False.elim (hs h)
      | exact False.elim (hs h.symm)
      | exact False.elim (hu (by simpa using h))
      | exact False.elim (hu (by simpa using h.symm))
      | exact False.elim (hv (by simpa using h))⟩
  have hg := (Erdos714Coding.free_iff_agreement (fun v i => f v i) (by decide)).mp hfree g
  have hle : (univ.filter (fun i => f u i = 0 ∧ f v i = 0)).card ≤
      (Erdos714Coding.agreement (fun v i => f v i) (by decide : 0 < 4) g).card := by
    apply card_le_card
    intro i hi
    obtain ⟨hfu,hfv⟩ := (mem_filter.mp hi).2
    simp only [Erdos714Coding.agreement, mem_filter, mem_univ, true_and]
    intro j
    fin_cases j <;> simp [g, hfu, hfv]
  omega

/-- Degenerate parallelogram direction pairs. -/
def degeneratePairs : Finset (V × V) :=
  univ.filter (fun p => p.1 = 0 ∨ p.2 = 0 ∨ p.1 = p.2 ∨ p.1+p.2 = 0)

/-- There are at most four degenerate choices per group element. -/
lemma degeneratePairs_card : (degeneratePairs : Finset (V × V)).card ≤ 4 * Fintype.card V := by
  have h₀ : (univ.filter (fun p : V × V => p.1 = 0)).card = Fintype.card V := by
    rw [card_filter, Fintype.sum_prod_type, sum_comm]
    simp [-sum_boole]
  have h₁ : (univ.filter (fun p : V × V => p.2 = 0)).card = Fintype.card V := by
    simp [card_filter, Fintype.sum_prod_type, -sum_boole]
  have h₂ : (univ.filter (fun p : V × V => p.1 = p.2)).card = Fintype.card V := by
    simp [card_filter, Fintype.sum_prod_type, -sum_boole]
  have h₃ : (univ.filter (fun p : V × V => p.1+p.2 = 0)).card = Fintype.card V := by
    rw [card_filter, Fintype.sum_prod_type, sum_comm]
    simp [add_eq_zero_iff_eq_neg, -sum_boole]
  unfold degeneratePairs
  simp only [filter_or]
  have h := card_union_le (univ.filter (fun p : V × V => p.1 = 0))
    ((univ.filter (fun p : V × V => p.2 = 0)) ∪
      ((univ.filter (fun p : V × V => p.1 = p.2)) ∪
        (univ.filter (fun p : V × V => p.1+p.2 = 0))))
  have h' := card_union_le (univ.filter (fun p : V × V => p.2 = 0))
    ((univ.filter (fun p : V × V => p.1 = p.2)) ∪
      (univ.filter (fun p : V × V => p.1+p.2 = 0)))
  have h'' := card_union_le (univ.filter (fun p : V × V => p.1 = p.2))
    (univ.filter (fun p : V × V => p.1+p.2 = 0))
  omega

/-- Double-counting zero pairs bounds the second moment of coordinate kernel sizes. -/
theorem kernel_second_moment_bound (f : V →+ (I → A))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => f v i))) :
    ∑ i : I, (univ.filter (fun v => f v i = 0)).card ^ 2 ≤
      3 * (Fintype.card V)^2 + 4 * Fintype.card I * Fintype.card V := by
  let c (p : V × V) := (univ.filter (fun i => f p.1 i = 0 ∧ f p.2 i = 0)).card
  have hc (p : V × V) : c p ≤ 3 + if p ∈ degeneratePairs then Fintype.card I else 0 := by
    by_cases hp : p ∈ degeneratePairs
    · have hle : c p ≤ Fintype.card I := card_le_univ _
      simp only [if_pos hp]
      omega
    · have hgood : p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ p.1+p.2 ≠ 0 := by
        simpa only [degeneratePairs, mem_filter, mem_univ, true_and, not_or] using hp
      simpa only [if_neg hp, add_zero] using
        common_zeros_le_three f hfree hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
  have he : ∑ i : I, (univ.filter (fun v => f v i = 0)).card ^ 2 = ∑ p : V × V, c p := by
    have hh (i : I) : (univ.filter (fun v => f v i = 0)).card ^ 2 =
        (univ.filter (fun p : V × V => f p.1 i = 0 ∧ f p.2 i = 0)).card := by
      rw [pow_two, ← card_product]
      congr 1
      ext p
      simp
    simp_rw [hh]
    simp only [c, card_filter]
    rw [sum_comm]
  have hb : (∑ p : V × V, if p ∈ degeneratePairs then Fintype.card I else 0) =
      (degeneratePairs : Finset (V × V)).card * Fintype.card I := by
    rw [← sum_filter]
    simp
  rw [he]
  calc
    ∑ p : V × V, c p ≤ ∑ p : V × V, (3 + if p ∈ degeneratePairs then Fintype.card I else 0) :=
      sum_le_sum (fun p _ => hc p)
    _ = 3 * (Fintype.card V)^2 + (degeneratePairs : Finset (V × V)).card * Fintype.card I := by
      rw [sum_add_distrib, hb]
      simp [pow_two, mul_comm]
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right (Fintype.card I) (degeneratePairs_card (V := V))
      nlinarith

/-- With sufficiently many messages, an additive K44-free code has length at most 6q^2. -/
theorem length_bound (f : V →+ (I → A))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => f v i)))
    (hsize : 8 * (Fintype.card A)^2 ≤ Fintype.card V) :
    Fintype.card I ≤ 6 * (Fintype.card A)^2 := by
  have hk (i : I) : Fintype.card V ≤
      Fintype.card A * (univ.filter (fun v => f v i = 0)).card :=
    card_le_alphabet_mul_kernel ((Pi.evalAddMonoidHom (fun _ : I => A) i).comp f)
  have hsq (i : I) : (Fintype.card V)^2 ≤ (Fintype.card A)^2 *
      (univ.filter (fun v => f v i = 0)).card ^ 2 := by
    have h := Nat.mul_le_mul (hk i) (hk i)
    nlinarith
  have hsum : Fintype.card I * (Fintype.card V)^2 ≤
      (Fintype.card A)^2 * ∑ i : I, (univ.filter (fun v => f v i = 0)).card ^ 2 := by
    have h := sum_le_sum (s := (univ : Finset I)) (fun i _ => hsq i)
    simpa only [sum_const, card_univ, smul_eq_mul, ← mul_sum] using h
  have hm := Nat.mul_le_mul_left ((Fintype.card A)^2) (kernel_second_moment_bound f hfree)
  have ht := hsum.trans hm
  have hv : 0 < Fintype.card V := Fintype.card_pos
  have hc : Fintype.card I * Fintype.card V ≤
      3 * (Fintype.card A)^2 * Fintype.card V + 4 * (Fintype.card A)^2 * Fintype.card I := by
    apply Nat.le_of_mul_le_mul_right (c := Fintype.card V) _ hv
    nlinarith
  have hh := Nat.mul_le_mul_right (Fintype.card I) hsize
  apply Nat.le_of_mul_le_mul_right (c := Fintype.card V) _ hv
  nlinarith

/-- No additive code realizes the fourth-case critical q^4/q^3 parameters for q>6. -/
theorem quartic_size_not_free (f : V →+ (I → A))
    (hq : 7 ≤ Fintype.card A)
    (hV : Fintype.card V = (Fintype.card A)^4)
    (hI : Fintype.card I = (Fintype.card A)^3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun v i => f v i)) := by
  intro hfree
  have hsize : 8 * (Fintype.card A)^2 ≤ Fintype.card V := by
    rw [hV, show (Fintype.card A)^4 = (Fintype.card A)^2 * (Fintype.card A)^2 by ring]
    apply Nat.mul_le_mul_right
    nlinarith
  have hlen := length_bound f hfree hsize
  rw [hI] at hlen
  have hp : 0 < (Fintype.card A)^2 := pow_pos Fintype.card_pos 2
  have hle : Fintype.card A ≤ 6 := by
    apply Nat.le_of_mul_le_mul_right (c := (Fintype.card A)^2) _ hp
    nlinarith
  omega

#print axioms common_zeros_le_three
#print axioms kernel_second_moment_bound
#print axioms length_bound
#print axioms quartic_size_not_free

end Erdos714AdditiveCoding
