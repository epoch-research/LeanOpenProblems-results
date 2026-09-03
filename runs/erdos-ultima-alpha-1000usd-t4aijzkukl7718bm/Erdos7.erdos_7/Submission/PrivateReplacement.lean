import FormalConjecturesUtil

/-!
# Replacement using private points

A class replacement need only retain points not covered by another class.
The minimum-sum consequence below is a necessary condition, not a resolution
of the odd covering conjecture.
-/

namespace Erdos7PrivateReplacement
open scoped BigOperators

/-- The points for which class `i` is the sole witness. -/
def Private {I : Type*} (m : I → ℕ) (a : I → ℤ) (i : I) (x : ℤ) : Prop :=
  (m i : ℤ) ∣ x-a i ∧ ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x-a j

/-- A local replacement preserves the covered union, even for a partial family.
No divisibility relation between the old and new moduli is assumed. -/
theorem replace_private_union {I : Type*} [DecidableEq I]
    (m : I → ℕ) (a : I → ℤ) (i : I) (d : ℕ) (b : ℤ)
    (hp : ∀ x, Private m a i x → (d : ℤ) ∣ x-b) :
    ∀ x, (∃ j, (m j : ℤ) ∣ x-a j) →
      ∃ j, (Function.update m i d j : ℤ) ∣ x-Function.update a i b j := by
  classical
  intro x hx
  by_cases hother : ∃ j, j ≠ i ∧ (m j : ℤ) ∣ x-a j
  · obtain ⟨j,hji,hj⟩ := hother
    exact ⟨j, by simpa [hji] using hj⟩
  · obtain ⟨j,hj⟩ := hx
    have hji : j=i := by
      by_contra h
      exact hother ⟨j,h,hj⟩
    subst j
    refine ⟨i, ?_⟩
    simpa using hp x ⟨hj, fun k hki hk => hother ⟨k,hki,hk⟩⟩

/-- A strict odd cover with a prescribed common period. -/
def OddCover {I : Type*} (N : ℕ) (m : I → ℕ) (a : I → ℤ) : Prop :=
  Function.Injective m ∧ (∀ i, 1 < m i ∧ Odd (m i) ∧ m i ∣ N) ∧
  ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i

/-- The replacement is a strict odd cover whenever the new modulus is missing,
odd, nontrivial, and divides the retained period. -/
theorem replace_private_cover {I : Type*} [DecidableEq I]
    (N : ℕ) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a)
    (i : I) (d : ℕ) (b : ℤ) (hd : 1 < d ∧ Odd d ∧ d ∣ N)
    (hmissing : ∀ j, m j ≠ d)
    (hp : ∀ x, Private m a i x → (d : ℤ) ∣ x-b) :
    OddCover N (Function.update m i d) (Function.update a i b) := by
  obtain ⟨hinj,hm,hcov⟩ := hc
  refine ⟨?_, ?_, fun x => replace_private_union m a i d b hp x (hcov x)⟩
  · intro j k hjk
    by_cases hji : j=i <;> by_cases hki : k=i
    · exact hji.trans hki.symm
    · subst j
      exact False.elim (hmissing k (by simpa [hki] using hjk.symm))
    · subst k
      exact False.elim (hmissing j (by simpa [hji] using hjk))
    · apply hinj
      simpa [hji,hki] using hjk
  · intro j
    by_cases hji : j=i
    · subst j; simpa using hd
    · simpa [hji] using hm j

lemma sum_update_lt {I : Type*} [Fintype I] [DecidableEq I]
    (m : I → ℕ) (i : I) (d : ℕ) (hd : d < m i) :
    (∑ j, Function.update m i d j) < ∑ j, m j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hs := Finset.sum_erase_add (Finset.univ : Finset I) m (Finset.mem_univ i)
  have he : (Finset.univ : Finset I) \ {i} = Finset.univ.erase i := by
    ext j; simp
  rw [he]
  omega

/-- Every missing smaller odd divisor of the period has a private escape from
EVERY proposed residue class in a minimum-sum cover. Unlike ordinary divisor
closure, the candidate need not divide the old modulus. -/
theorem private_escape_of_minimal_sum {I : Type*} [Fintype I]
    (N : ℕ) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a)
    (hmin : ∀ (n : I → ℕ) (c : I → ℤ), OddCover N n c →
      (∑ j, m j) ≤ ∑ j, n j)
    (i : I) (d : ℕ) (hd : 1 < d ∧ Odd d ∧ d ∣ N)
    (hlt : d < m i) (hmissing : ∀ j, m j ≠ d) (b : ℤ) :
    ∃ x, Private m a i x ∧ ¬ (d : ℤ) ∣ x-b := by
  classical
  by_contra h
  have hp : ∀ x, Private m a i x → (d : ℤ) ∣ x-b := by
    intro x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  have hnew := replace_private_cover N m a hc i d b hd hmissing hp
  have hle := hmin _ _ hnew
  have hlt' := sum_update_lt m i d hlt
  omega

/-- Minimization provides this stronger private-point normal form without
increasing the number of classes or changing the supplied period. -/
theorem exists_private_rigid_cover {I : Type*} [Fintype I]
    (N : ℕ) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a) :
    ∃ (n : I → ℕ) (c : I → ℤ), OddCover N n c ∧
      (∑ j, n j) ≤ ∑ j, m j ∧
      ∀ i d, (1 < d ∧ Odd d ∧ d ∣ N) → d < n i →
        (∀ j, n j ≠ d) → ∀ b : ℤ,
          ∃ x, Private n c i x ∧ ¬ (d : ℤ) ∣ x-b := by
  classical
  let P (s : ℕ) := ∃ (n : I → ℕ) (c : I → ℤ), OddCover N n c ∧ ∑ j, n j = s
  have hex : ∃ s, P s := ⟨∑ j, m j, m,a,hc,rfl⟩
  obtain ⟨n,c,hn,hs⟩ := Nat.find_spec hex
  have hmin : ∀ (l : I → ℕ) (b : I → ℤ), OddCover N l b →
      (∑ j, n j) ≤ ∑ j, l j := by
    intro l b hl
    rw [hs]
    exact Nat.find_min' hex ⟨l,b,hl,rfl⟩
  refine ⟨n,c,hn,hmin m a hc,?_⟩
  intro i d hd hlt hmissing b
  exact private_escape_of_minimal_sum N n c hn hmin i d hd hlt hmissing b

section Control

/-- An irredundant divisor-closed PARTIAL odd family. -/
def modulus : Fin 9 → ℕ := ![3,5,7,9,15,21,35,63,105]
def residue : Fin 9 → ℤ := ![0,0,0,7,2,2,2,22,1]
def point : Fin 9 → ℤ := ![3,5,14,16,17,23,37,22,1]

lemma control_data : Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 315) ∧
    (∀ i, Private modulus residue i (point i)) := by
  unfold Private
  decide +kernel

lemma control_divisors : ∀ i, ∀ d ∈ (modulus i).divisors,
    1 < d → ∃ j, modulus j = d := by
  decide +kernel

lemma control_divisor_closed : ∀ i d, 1 < d → d ∣ modulus i →
    ∃ j, modulus j = d := by
  intro i d hd hdi
  exact control_divisors i d (Nat.mem_divisors.mpr
    ⟨hdi, by have := (control_data.2.1 i).1; omega⟩) hd

/-- Its 105-class has only the point 1 modulo 315 as a private point. -/
lemma control_private_span (x : ℤ) (hx : Private modulus residue 8 x) :
    (315 : ℤ) ∣ x-1 := by
  have h105 := hx.1
  have h9 := hx.2 3 (by decide)
  have h63 := hx.2 7 (by decide)
  change (105 : ℤ) ∣ x-1 at h105
  change ¬ (9 : ℤ) ∣ x-7 at h9
  change ¬ (63 : ℤ) ∣ x-22 at h63
  obtain ⟨k,hk⟩ := h105
  have h3 := Int.emod_add_mul_ediv k 3
  have hres : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hres with h | h | h
  · exact ⟨k/3, by omega⟩
  · exact False.elim (h9 ⟨35*(k/3)+11, by omega⟩)
  · exact False.elim (h63 ⟨5*(k/3)+3, by omega⟩)

lemma control_missing : (∀ i, modulus i ≠ 45) ∧
    (45 : ℕ) < modulus 8 ∧ ¬ (45 : ℕ) ∣ modulus 8 := by
  decide +kernel

/-- Replacing 105 by the NONDIVISOR 45 retains every originally covered point. -/
theorem control_union_enlargement : ∀ x : ℤ,
    (∃ i, (modulus i : ℤ) ∣ x-residue i) →
    ∃ i, (Function.update modulus 8 45 i : ℤ) ∣
      x-Function.update residue 8 1 i := by
  apply replace_private_union modulus residue 8 45 1
  intro x hx
  exact (show (45 : ℤ) ∣ 315 by norm_num).trans (control_private_span x hx)

lemma control_strict_gain :
    (∀ i, ¬ (modulus i : ℤ) ∣ (46 : ℤ)-residue i) ∧
    (45 : ℤ) ∣ (46 : ℤ)-1 := by
  decide +kernel

/-- Neither the old family nor the enlarged family is a covering witness. -/
lemma control_hole :
    (∀ i, ¬ (modulus i : ℤ) ∣ (4 : ℤ)-residue i) ∧
    (∀ i, ¬ (Function.update modulus 8 45 i : ℤ) ∣
      (4 : ℤ)-Function.update residue 8 1 i) := by
  decide +kernel

end Control

#print axioms replace_private_union
#print axioms replace_private_cover
#print axioms private_escape_of_minimal_sum
#print axioms exists_private_rigid_cover
#print axioms control_data
#print axioms control_divisor_closed
#print axioms control_private_span
#print axioms control_union_enlargement
#print axioms control_hole
end Erdos7PrivateReplacement
