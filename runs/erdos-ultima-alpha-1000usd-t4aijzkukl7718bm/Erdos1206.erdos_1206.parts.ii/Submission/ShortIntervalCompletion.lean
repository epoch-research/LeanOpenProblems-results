import Submission.ShortIntervals
import Submission.EntropyBoundaryCriterion

/-!
A sufficiently short, distant interval has no outside three-root completions.
Consequently its cube-Sidon property survives adjoining any one integer.
This local result does not control completions using several intervals.
-/
namespace Erdos1206.ShortIntervalCompletion
open Finset
open scoped Classical

lemma lower_cube_bound {M L : ℕ} (h : 4*L ≤ M) :
    (M-4*L)^3+(M+L)^3 ≤ 2*M^3 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  nlinarith [Nat.zero_le (k^2*L),Nat.zero_le (k*L^2),Nat.zero_le (L^3)]

lemma upper_cube_bound (M L : ℕ) :
    2*(M+L)^3 ≤ (M+2*L)^3+M^3 := by
  nlinarith [Nat.zero_le (M*L^2),Nat.zero_le (L^3)]

lemma completion_in_enlarged {M L x a b c : ℕ} (hM : 4*L ≤ M)
    (ha : a ∈ Set.Icc M (M+L)) (hb : b ∈ Set.Icc M (M+L))
    (hc : c ∈ Set.Icc M (M+L)) (he : x^3+a^3=b^3+c^3) :
    x ∈ Set.Icc (M-4*L) (M+2*L) := by
  have haL := Nat.pow_le_pow_left ha.1 3
  have haU := Nat.pow_le_pow_left ha.2 3
  have hbL := Nat.pow_le_pow_left hb.1 3
  have hbU := Nat.pow_le_pow_left hb.2 3
  have hcL := Nat.pow_le_pow_left hc.1 3
  have hcU := Nat.pow_le_pow_left hc.2 3
  constructor
  · by_contra hx
    have hh := Nat.pow_lt_pow_left (show x < M-4*L by omega) (by decide : 3≠0)
    have hl := lower_cube_bound hM
    omega
  · by_contra hx
    have hh := Nat.pow_lt_pow_left (show M+2*L < x by omega) (by decide : 3≠0)
    have hu := upper_cube_bound M L
    omega

/-- Three roots in a band of length `L` beginning beyond `6L²+4L`
cannot complete a nontrivial cube collision, even with an unrestricted fourth root. -/
theorem completion_trivial {M L x a b c : ℕ} (hM : 6*L^2+4*L ≤ M)
    (ha : a ∈ Set.Icc M (M+L)) (hb : b ∈ Set.Icc M (M+L))
    (hc : c ∈ Set.Icc M (M+L)) (he : x^3+a^3=b^3+c^3) :
    x=b ∨ x=c := by
  have h4 : 4*L ≤ M := by omega
  have hbase : M-4*L+4*L=M := Nat.sub_add_cancel h4
  have hsize : (6*L)^2 ≤ 6*(M-4*L)+9 := by nlinarith
  have hs := cubes_sidon_on_short_interval (6*L) (M-4*L) hsize
  have hx := completion_in_enlarged h4 ha hb hc he
  have htop : M-4*L+6*L=M+2*L := by omega
  have hmem {n : ℕ} (hn : n ∈ Set.Icc M (M+L)) :
      n ∈ Set.Icc (M-4*L) (M-4*L+6*L) := by
    rw [htop]
    obtain ⟨hnL,hnU⟩ := hn
    constructor <;> omega
  rw [←htop] at hx
  have hh := hs _ ⟨x,hx,rfl⟩ _ ⟨b,hmem hb,rfl⟩
    _ ⟨a,hmem ha,rfl⟩ _ ⟨c,hmem hc,rfl⟩ he
  rcases hh with hh | hh
  · exact Or.inl (Nat.pow_left_injective (by decide : 3≠0) hh.1)
  · exact Or.inr (Nat.pow_left_injective (by decide : 3≠0) hh.1)

/-- The same interval remains cube-Sidon after adjoining ANY one root. -/
theorem cube_sidon_union_singleton {M L : ℕ} (hM : 6*L^2+4*L ≤ M) (x : ℕ) :
    IsSidon ((fun a : ℕ => a^3) '' (Set.Icc M (M+L) ∪ {x})) := by
  have hs := cubes_sidon_on_short_interval L M (show L^2 ≤ 6*M+9 by nlinarith)
  rw [Set.image_union,Set.image_singleton]
  apply (Set.IsSidon.insert hs).mpr
  by_cases hx : x ∈ Set.Icc M (M+L)
  · exact Or.inl ⟨x,hx,rfl⟩
  right
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
  refine ⟨?_,?_⟩
  · intro he
    dsimp only at he
    have hx' : x < M ∨ M+L < x := by
      simp only [Set.mem_Icc,not_and_or,not_le] at hx
      exact hx
    rcases hx' with hx' | hx'
    · have hh := Nat.pow_lt_pow_left hx' (by decide : 3≠0)
      have ha' := Nat.pow_le_pow_left ha.1 3
      have hb' := Nat.pow_le_pow_left hb.1 3
      omega
    · have hh := Nat.pow_lt_pow_left hx' (by decide : 3≠0)
      have ha' := Nat.pow_le_pow_left ha.2 3
      have hb' := Nat.pow_le_pow_left hb.2 3
      omega
  · rintro _ ⟨c,hc,rfl⟩ he
    rcases completion_trivial hM ha hb hc he with h | h
    · exact hx (h ▸ hb)
    · exact hx (h ▸ hc)

/-- Every subset of the short band has empty completion boundary, regardless
of the prefix in which possible new roots are tested. -/
theorem boundary_eq_empty {M L : ℕ} (hM : 6*L^2+4*L ≤ M)
    (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ Set.Icc M (M+L)) (N : ℕ) :
    EntropyBoundaryCriterion.boundary S N = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := (mem_filter.mp hx).2
  apply hh
  apply Set.IsSidon.subset (cube_sidon_union_singleton hM x)
  apply Set.image_mono
  intro y hy
  have hy' : y=x ∨ y∈S := mem_insert.mp hy
  rcases hy' with rfl | hy'
  · exact Or.inr (by simp)
  · exact Or.inl (hS hy')

#print axioms completion_trivial
#print axioms cube_sidon_union_singleton
#print axioms boundary_eq_empty
end Erdos1206.ShortIntervalCompletion
