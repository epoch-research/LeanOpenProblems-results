import FormalConjecturesUtil

/-!
Additive-line obstructions to a norm perturbed by a linear functional of a power.
These results rule out a candidate construction; they do not settle Erdős 714.
-/

open SimpleGraph

namespace Erdos714QuinticNormLift

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The additive-weight lift of a field-valued function. -/
def graph (f : E → F) : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj u v := match u, v with
    | .inl x, .inr y => f (x.1 + y.1) = x.2 + y.2
    | .inr y, .inl x => f (x.1 + y.1) = x.2 + y.2
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp_all
  loopless := by intro u; cases u <;> simp

/-- An additive restriction to a scalar line gives a complete bipartite graph
with one vertex on each side for every scalar. -/
def lineCopy {p : ℕ} [Fact p.Prime] [CharP F p]
    (f : E → F) (b : E) (hb : b ≠ 0) (c : F)
    (hf : ∀ t : F, f (t • b) = t ^ p * c) :
    Copy (completeBipartiteGraph F F) (graph f) := by
  let e : F ↪ E × F :=
    ⟨fun t => (t • b, t ^ p * c), by
      intro s t h
      exact smul_left_injective F hb (congrArg Prod.fst h)⟩
  refine ⟨⟨e.sumMap e, ?_⟩, (e.sumMap e).injective⟩
  intro u v huv
  cases u with
  | inl s =>
    cases v with
    | inl t => simp at huv
    | inr t =>
      change f (s • b + t • b) = s ^ p * c + t ^ p * c
      rw [← add_smul, hf, add_pow_char, add_mul]
  | inr t =>
    cases v with
    | inl s =>
      change f (s • b + t • b) = s ^ p * c + t ^ p * c
      rw [← add_smul, hf, add_pow_char, add_mul]
    | inr s => simp at huv

/-- The scalar-line copy contains every balanced biclique up to the base-field order. -/
theorem not_free_of_line [Fintype F] {p r : ℕ} [Fact p.Prime] [CharP F p]
    (f : E → F) (b : E) (hb : b ≠ 0) (c : F)
    (hf : ∀ t : F, f (t • b) = t ^ p * c) (hr : r ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph f) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin r) (β := F) (by simpa using hr)
  let g : Copy (completeBipartiteGraph (Fin r) (Fin r))
      (completeBipartiteGraph F F) :=
    ⟨⟨e.sumMap e, by intro u v huv; cases u <;> cases v <;> simp_all⟩,
      (e.sumMap e).injective⟩
  intro hfree
  exact hfree ⟨(lineCopy f b hb c hf).comp g⟩

/-- A linear functional into a strictly smaller finite field has a nonzero kernel vector. -/
lemma exists_nonzero_kernel [Fintype F] [Fintype E]
    (L : E →ₗ[F] F) (hcard : Fintype.card F < Fintype.card E) :
    ∃ z : E, z ≠ 0 ∧ L z = 0 := by
  by_contra! h
  have hinj : Function.Injective L := by
    intro x y hxy
    by_contra hne
    exact h (x - y) (sub_ne_zero.mpr hne) (by simp [hxy])
  exact (not_le_of_gt hcard) (Fintype.card_le_of_injective L hinj)

/-- If powering is onto, a nonzero kernel vector can be chosen to be a power. -/
lemma exists_power_in_kernel [Fintype F] [Fintype E]
    (L : E →ₗ[F] F) {d : ℕ} (hd : 0 < d)
    (hpow : Function.Surjective (fun x : E => x ^ d))
    (hcard : Fintype.card F < Fintype.card E) :
    ∃ b : E, b ≠ 0 ∧ L (b ^ d) = 0 := by
  obtain ⟨z, hz, hL⟩ := exists_nonzero_kernel L hcard
  obtain ⟨b, hb⟩ := hpow z
  refine ⟨b, ?_, by simpa [hb] using hL⟩
  intro h
  subst b
  exact hz (by simpa [Nat.ne_of_gt hd] using hb.symm)

/-- Along the chosen line, a norm plus a homogeneous perturbation reduces to the norm. -/
lemma restriction (L : E →ₗ[F] F) {d p : ℕ}
    (hdegree : Module.finrank F E = p) {b : E} (hb : L (b ^ d) = 0) (t : F) :
    Algebra.norm F (t • b) + L ((t • b) ^ d) = t ^ p * Algebra.norm F b := by
  rw [smul_pow, L.map_smul, hb, smul_zero, add_zero, Algebra.smul_def,
    map_mul, Algebra.norm_algebraMap, hdegree]

/-- In extension degree equal to the characteristic, adding a linear functional
of a bijective power never removes all scalar-line bicliques. -/
theorem norm_plus_power_not_free [Fintype F] [Fintype E]
    {p d r : ℕ} [Fact p.Prime] [CharP F p]
    (L : E →ₗ[F] F) (hdegree : Module.finrank F E = p) (hd : 0 < d)
    (hpow : Function.Surjective (fun x : E => x ^ d))
    (hcard : Fintype.card F < Fintype.card E) (hr : r ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free
      (graph (fun x => Algebra.norm F x + L (x ^ d))) := by
  obtain ⟨b, hb, hL⟩ := exists_power_in_kernel L hd hpow hcard
  exact not_free_of_line _ b hb (Algebra.norm F b)
    (restriction L hdegree hL) hr

/-- The order of an odd-degree extension of F3 is either two or three modulo five. -/
lemma odd_power_three_mod_five (k : ℕ) :
    3 ^ (2 * k + 1) % 5 = 2 ∨ 3 ^ (2 * k + 1) % 5 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [he, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> norm_num [h]

/-- Fifth powering is onto in every field of order 3^(2k+1). -/
theorem fifth_power_surjective [Fintype E] (k : ℕ)
    (hcard : Fintype.card E = 3 ^ (2 * k + 1)) :
    Function.Surjective (fun x : E => x ^ 5) := by
  classical
  have hcop : (3 ^ (2 * k + 1) - 1).Coprime 5 := by
    apply Nat.Coprime.symm
    apply (Nat.prime_five.coprime_iff_not_dvd).mpr
    intro hd
    have hp : 1 ≤ 3 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by decide)
    have hm : (3 ^ (2 * k + 1) - 1 + 1) % 5 = 1 := by
      simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    rw [Nat.sub_add_cancel hp] at hm
    have h := odd_power_three_mod_five k
    omega
  have hunit : (Nat.card Eˣ).Coprime 5 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_units, hcard] using hcop
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · obtain ⟨y, hy⟩ := hunit.pow_left_bijective.surjective (Units.mk0 x hx)
    exact ⟨(y : E), by simpa using congrArg Units.val hy⟩

/-- The cubic-extension case for any linear perturbation of fifth powers. -/
theorem cubic_fifth_not_free [Fintype F] [Fintype E] [CharP F 3]
    (L : E →ₗ[F] F) (hdegree : Module.finrank F E = 3)
    (k : ℕ) (hcard : Fintype.card E = 3 ^ (2 * k + 1))
    (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun x => Algebra.norm F x + L (x ^ 5))) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply norm_plus_power_not_free L hdegree (by decide : 0 < 5)
    (fifth_power_surjective k hcard) _ hq
  rw [Module.card_eq_pow_finrank (K := F) (V := E), hdegree]
  have hq0 : 0 < Fintype.card F := by omega
  nlinarith [sq_nonneg (Fintype.card F),
    Nat.mul_lt_mul_of_pos_left (show 1 < Fintype.card F by omega) hq0]

/-- In particular, this applies to every trace coefficient, including nonzero
coefficients whose own trace does not vanish. -/
theorem trace_fifth_not_free [Fintype F] [Fintype E] [CharP F 3]
    (δ : E) (hdegree : Module.finrank F E = 3)
    (k : ℕ) (hcard : Fintype.card E = 3 ^ (2 * k + 1))
    (hq : 4 ≤ Fintype.card F) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun x => Algebra.norm F x + Algebra.trace F E (δ * x ^ 5))) := by
  exact cubic_fifth_not_free ((Algebra.trace F E).comp (LinearMap.mulLeft F δ))
    hdegree k hcard hq

/-- Uniformly over every cubic extension of a field of order 3^(2k+3).
This includes the whole sufficiently large odd-degree base-field sequence. -/
theorem odd_base_trace_fifth_not_free [Fintype F] [Fintype E] [CharP F 3]
    (δ : E) (hdegree : Module.finrank F E = 3)
    (k : ℕ) (hcard : Fintype.card F = 3 ^ (2 * k + 3)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (fun x => Algebra.norm F x + Algebra.trace F E (δ * x ^ 5))) := by
  apply trace_fifth_not_free δ hdegree (3 * k + 4)
  · rw [Module.card_eq_pow_finrank (K := F) (V := E), hdegree, hcard, ← pow_mul]
    congr 1
    omega
  · rw [hcard, pow_add]
    have hp : 1 ≤ 3 ^ (2 * k) := Nat.one_le_pow _ _ (by decide)
    norm_num
    omega

end Erdos714QuinticNormLift

#print axioms Erdos714QuinticNormLift.lineCopy
#print axioms Erdos714QuinticNormLift.norm_plus_power_not_free
#print axioms Erdos714QuinticNormLift.fifth_power_surjective
#print axioms Erdos714QuinticNormLift.cubic_fifth_not_free
#print axioms Erdos714QuinticNormLift.trace_fifth_not_free

#print axioms Erdos714QuinticNormLift.odd_base_trace_fifth_not_free
