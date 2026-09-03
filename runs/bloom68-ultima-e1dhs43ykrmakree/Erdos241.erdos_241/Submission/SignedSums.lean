import Submission.Reductions

/-!
Exact finite counting consequences of the strong multiset B₃ property.
These are auxiliary bounds, not a proof of the sharp asymptotic in Spec.
-/

open Finset

namespace Erdos241

/-- A positive pair with a denominator excluded from that pair. -/
def reducedPairs (A : Finset ℕ) : Finset (Σ _ : ℕ, Sym2 ℕ) :=
  A.sigma fun c => (A.erase c).sym2

/-- The integer represented by a reduced signed pair. -/
def reducedPairValue (v : Σ _ : ℕ, Sym2 ℕ) : ℤ :=
  (v.2.toMultiset.sum : ℤ) - (v.1 : ℤ)

private theorem sym2_toMultiset_injective :
    Function.Injective (Sym2.toMultiset : Sym2 ℕ → Multiset ℕ) := by
  intro p q hpq
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toMultiset, ← Sym2.mem_toMultiset, hpq]

private theorem reducedPair_data {A : Finset ℕ} {v : Σ _ : ℕ, Sym2 ℕ}
    (hv : v ∈ reducedPairs A) :
    v.1 ∈ A ∧ (∀ x ∈ v.2.toMultiset, x ∈ A) ∧ v.1 ∉ v.2.toMultiset := by
  obtain ⟨hc, hp⟩ := Finset.mem_sigma.mp hv
  refine ⟨hc, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_of_mem_erase ((Finset.mem_sym2_iff.mp hp) x
      (Sym2.mem_toMultiset.mp hx))
  · intro hx
    exact Finset.notMem_erase _ _ ((Finset.mem_sym2_iff.mp hp) v.1
      (Sym2.mem_toMultiset.mp hx))

/-- Reduced signed representations are unique, including repeated positive terms. -/
theorem reducedPairValue_injOn {A : Finset ℕ} (hA : IsBrSet 3 A) :
    Set.InjOn reducedPairValue (reducedPairs A) := by
  rintro ⟨c, p⟩ hv ⟨d, q⟩ hw heq
  obtain ⟨hc, hp, hcp⟩ := reducedPair_data hv
  obtain ⟨hd, hq, hdq⟩ := reducedPair_data hw
  have hs : p.toMultiset.sum + d = q.toMultiset.sum + c := by
    have hi : (p.toMultiset.sum : ℤ) + (d : ℤ) =
        (q.toMultiset.sum : ℤ) + (c : ℤ) := by
      dsimp [reducedPairValue] at heq
      omega
    exact_mod_cast hi
  have hm : p.toMultiset + {d} = q.toMultiset + {c} :=
    hA _ _ (by simp [Sym2.card_toMultiset])
      (by simp [Sym2.card_toMultiset])
      (by intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
          · exact hp x hx
          · simpa using (Multiset.mem_singleton.mp hx) ▸ hd)
      (by intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
          · exact hq x hx
          · simpa using (Multiset.mem_singleton.mp hx) ▸ hc)
      (by simpa using hs)
  have hcd : c = d := by
    have hmem : c ∈ p.toMultiset + {d} := by rw [hm]; simp
    rcases Multiset.mem_add.mp hmem with hmem | hmem
    · exact False.elim (hcp hmem)
    · exact Multiset.mem_singleton.mp hmem
  subst d
  have hpq : p = q := sym2_toMultiset_injective (add_right_cancel hm)
  subst q
  rfl

/-- No reduced signed value is an element of the original set. -/
theorem reducedPairValue_notMem {A : Finset ℕ} (hA : IsBrSet 3 A)
    {v : Σ _ : ℕ, Sym2 ℕ} (hv : v ∈ reducedPairs A)
    {a : ℕ} (ha : a ∈ A) : reducedPairValue v ≠ (a : ℤ) := by
  obtain ⟨hc, hp, hcp⟩ := reducedPair_data hv
  intro heq
  have hs : v.2.toMultiset.sum = a + v.1 := by
    have hi : (v.2.toMultiset.sum : ℤ) = (a : ℤ) + (v.1 : ℤ) := by
      dsimp [reducedPairValue] at heq
      omega
    exact_mod_cast hi
  have hm : v.2.toMultiset + {v.1} = ({a} + {v.1}) + {v.1} :=
    hA _ _ (by simp [Sym2.card_toMultiset]) (by simp)
      (by intro x hx; rcases Multiset.mem_add.mp hx with hx | hx
          · exact hp x hx
          · simpa using (Multiset.mem_singleton.mp hx) ▸ hc)
      (by intro x hx; simp only [Multiset.mem_add, Multiset.mem_singleton] at hx
          rcases hx with (rfl | rfl) | rfl <;> assumption)
      (by simp [hs, add_assoc])
  have hp' : v.2.toMultiset = {a} + {v.1} := add_right_cancel hm
  exact hcp (by rw [hp']; simp)

/-- Exact cardinality of the reduced representation domain. -/
theorem card_reducedPairs (A : Finset ℕ) :
    (reducedPairs A).card = A.card * A.card.choose 2 := by
  unfold reducedPairs
  rw [Finset.card_sigma]
  calc
    ∑ c ∈ A, ((A.erase c).sym2).card = ∑ _c ∈ A, A.card.choose 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.card_sym2, Finset.card_erase_of_mem hc]
      have hpos : 0 < A.card := Finset.card_pos.mpr ⟨c, hc⟩
      congr 1
      omega
    _ = A.card * A.card.choose 2 := by simp

private theorem reducedPairValue_mem_Icc {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) {v : Σ _ : ℕ, Sym2 ℕ} (hv : v ∈ reducedPairs A) :
    reducedPairValue v ∈ Icc (2 - (N : ℤ)) (2 * (N : ℤ) - 1) := by
  rcases v with ⟨c, p⟩
  induction p with | _ a b =>
    obtain ⟨hc, hp, _⟩ := reducedPair_data hv
    have ha : a ∈ A := hp a (by simp [Sym2.toMultiset])
    have hb : b ∈ A := hp b (by simp [Sym2.toMultiset])
    obtain ⟨hc1, hcN⟩ := Finset.mem_Icc.mp (hsub hc)
    dsimp only at hc1 hcN
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hsub ha)
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp (hsub hb)
    simp only [reducedPairValue, Sym2.toMultiset, Sym2.lift_mk]
    simp only [Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add]
    exact Finset.mem_Icc.mpr (by constructor <;> omega)

/-- The elementary signed-sum packing bound, with exact lower-order terms. -/
theorem signed_pair_count_le {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) (hA : IsBrSet 3 A) :
    A.card + A.card * A.card.choose 2 ≤ 3 * N - 2 := by
  let B : Finset ℤ := A.image (fun a : ℕ => (a : ℤ))
  let C : Finset ℤ := (reducedPairs A).image reducedPairValue
  have hB : B.card = A.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hC : C.card = A.card * A.card.choose 2 := by
    rw [Finset.card_image_of_injOn (reducedPairValue_injOn hA), card_reducedPairs]
  have hdis : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxC
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxB
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hxC
    exact reducedPairValue_notMem hA hv ha heq
  have hBC : B ∪ C ⊆ Icc (2 - (N : ℤ)) (2 * (N : ℤ) - 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hsub ha)
      exact Finset.mem_Icc.mpr (by constructor <;> omega)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact reducedPairValue_mem_Icc hsub hv
  calc
    A.card + A.card * A.card.choose 2 = (B ∪ C).card := by
      rw [Finset.card_union_of_disjoint hdis, hB, hC]
    _ ≤ (Icc (2 - (N : ℤ)) (2 * (N : ℤ) - 1)).card := Finset.card_le_card hBC
    _ = 3 * N - 2 := by rw [Int.card_Icc]; omega

/-- A convenient polynomial form of the elementary upper bound. -/
theorem cube_card_le {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Icc 1 N) (hA : IsBrSet 3 A) :
    A.card ^ 3 + 2 * A.card ≤ 6 * N + A.card ^ 2 := by
  have hcount : A.card + A.card * A.card.choose 2 ≤ 3 * N :=
    (signed_pair_count_le hsub hA).trans (Nat.sub_le _ _)
  have hpoly (n : ℕ) : 2 * n * n.choose 2 + n ^ 2 = n ^ 3 := by
    cases n with
    | zero => simp
    | succ m =>
      have hc := Nat.add_one_mul_choose_eq m 1
      simp only [Nat.choose_one_right] at hc
      have hc' := congrArg (fun x : ℕ => (m + 1) * x) hc
      nlinarith
  have hp := hpoly A.card
  nlinarith

/-- The same unconditional estimate for the maximum in the specification. -/
theorem cube_f_le (N : ℕ) : (f N 3) ^ 3 + 2 * f N 3 ≤ 6 * N + (f N 3) ^ 2 := by
  obtain ⟨A, hsub, hA, hcard⟩ := exists_maximizer N 3
  simpa only [hcard] using cube_card_le hsub hA

end Erdos241

#print axioms Erdos241.reducedPairValue_injOn
#print axioms Erdos241.reducedPairValue_notMem
#print axioms Erdos241.card_reducedPairs
#print axioms Erdos241.signed_pair_count_le
#print axioms Erdos241.cube_card_le
#print axioms Erdos241.cube_f_le
