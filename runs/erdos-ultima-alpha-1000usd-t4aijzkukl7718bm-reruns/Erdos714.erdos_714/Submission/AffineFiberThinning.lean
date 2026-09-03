import Submission.EnergyThinning

/-!
An additive-energy bound for arbitrary K44-free selections from affine
homomorphism fibers of bounded size. Unlike the additive-code theorem, no
complete collection of levels or injective column parametrization is needed.
This is a host-specific bound, not a resolution of Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714AffineFibers
open Erdos714EnergyThinning (parallelograms commonParallelogram)
variable {V Y A : Type*} [AddCommGroup V] [Fintype V] [Fintype Y] [AddCommGroup A]

def degenerate (p : V × V × V) : Prop := p.2.1=0 ∨ p.2.2=0 ∨ p.2.1=p.2.2 ∨ p.2.1+p.2.2=0

/-- Each degenerate parallelogram is determined by two of its points. -/
lemma degenerate_card (S : Finset V) :
    ((parallelograms S).filter degenerate).card ≤ 4*S.card^2 := by
  let T := parallelograms S
  have hmem (p : V × V × V) (hp : p ∈ T) :
      p.1 ∈ S ∧ p.1+p.2.1 ∈ S ∧ p.1+p.2.2 ∈ S ∧ p.1+p.2.1+p.2.2 ∈ S :=
    (mem_filter.mp hp).2
  have h0 : (T.filter (fun p => p.2.1=0)).card ≤ S.card^2 := by
    apply (card_le_card_of_injOn (fun p : V × V × V => (p.1,p.1+p.2.2))
      (t := S ×ˢ S) ?_ ?_).trans (by simp [pow_two])
    · intro p hp
      have hm := hmem p (mem_filter.mp hp).1
      exact mem_product.mpr ⟨hm.1,hm.2.2.1⟩
    · intro p hp q hq he
      have hx := congrArg Prod.fst he
      change p.1=q.1 at hx
      have hz : p.2.2=q.2.2 := by
        have hh : p.1+p.2.2=q.1+q.2.2 := congrArg Prod.snd he
        rw [hx] at hh
        exact add_left_cancel hh
      exact Prod.ext hx (Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) hz)
  have h1 : (T.filter (fun p => p.2.2=0)).card ≤ S.card^2 := by
    apply (card_le_card_of_injOn (fun p : V × V × V => (p.1,p.1+p.2.1))
      (t := S ×ˢ S) ?_ ?_).trans (by simp [pow_two])
    · intro p hp
      have hm := hmem p (mem_filter.mp hp).1
      exact mem_product.mpr ⟨hm.1,hm.2.1⟩
    · intro p hp q hq he
      have hx := congrArg Prod.fst he
      change p.1=q.1 at hx
      have hu : p.2.1=q.2.1 := by
        have hh : p.1+p.2.1=q.1+q.2.1 := congrArg Prod.snd he
        rw [hx] at hh
        exact add_left_cancel hh
      exact Prod.ext hx (Prod.ext hu ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm))
  have h2 : (T.filter (fun p => p.2.1=p.2.2)).card ≤ S.card^2 := by
    apply (card_le_card_of_injOn (fun p : V × V × V => (p.1,p.1+p.2.1))
      (t := S ×ˢ S) ?_ ?_).trans (by simp [pow_two])
    · intro p hp
      have hm := hmem p (mem_filter.mp hp).1
      exact mem_product.mpr ⟨hm.1,hm.2.1⟩
    · intro p hp q hq he
      have hx := congrArg Prod.fst he
      change p.1=q.1 at hx
      have hu : p.2.1=q.2.1 := by
        have hh : p.1+p.2.1=q.1+q.2.1 := congrArg Prod.snd he
        rw [hx] at hh
        exact add_left_cancel hh
      have hv : p.2.2=q.2.2 := (mem_filter.mp hp).2.symm.trans (hu.trans (mem_filter.mp hq).2)
      exact Prod.ext hx (Prod.ext hu hv)
  have h3 : (T.filter (fun p => p.2.1+p.2.2=0)).card ≤ S.card^2 := by
    apply (card_le_card_of_injOn (fun p : V × V × V => (p.1,p.1+p.2.1))
      (t := S ×ˢ S) ?_ ?_).trans (by simp [pow_two])
    · intro p hp
      have hm := hmem p (mem_filter.mp hp).1
      exact mem_product.mpr ⟨hm.1,hm.2.1⟩
    · intro p hp q hq he
      have hx := congrArg Prod.fst he
      change p.1=q.1 at hx
      have hu : p.2.1=q.2.1 := by
        have hh : p.1+p.2.1=q.1+q.2.1 := congrArg Prod.snd he
        rw [hx] at hh
        exact add_left_cancel hh
      have hv : p.2.2=q.2.2 := by
        have hh := (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
        rw [hu] at hh
        exact add_left_cancel hh
      exact Prod.ext hx (Prod.ext hu hv)
  have he : T.filter degenerate =
      T.filter (fun p => p.2.1=0) ∪ T.filter (fun p => p.2.2=0) ∪
        T.filter (fun p => p.2.1=p.2.2) ∪ T.filter (fun p => p.2.1+p.2.2=0) := by
    ext p
    simp only [mem_filter,mem_union,degenerate]
    tauto
  change (T.filter degenerate).card ≤ _
  rw [he]
  have hu0 := card_union_le (T.filter (fun p => p.2.1=0)) (T.filter (fun p => p.2.2=0))
  have hu1 := card_union_le (T.filter (fun p => p.2.1=0) ∪ T.filter (fun p => p.2.2=0))
    (T.filter (fun p => p.2.1=p.2.2))
  have hu2 := card_union_le (T.filter (fun p => p.2.1=0) ∪ T.filter (fun p => p.2.2=0) ∪
    T.filter (fun p => p.2.1=p.2.2)) (T.filter (fun p => p.2.1+p.2.2=0))
  omega

/-- The degenerate term depends on neighborhood squares, not ambient size. -/
theorem neighborhood_energy (N : Y → Finset V)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N)) :
    ∑ y, (N y).addEnergy (N y) ≤ 3*Fintype.card V^3+4*∑ y, (N y).card^2 := by
  let G (y : Y) := (parallelograms (N y)).filter (fun p => ¬degenerate p)
  let D (y : Y) := (parallelograms (N y)).filter degenerate
  have he (y : Y) : (N y).addEnergy (N y)=(G y).card+(D y).card := by
    rw [Erdos714EnergyThinning.energy_eq_parallelograms]
    have h := card_filter_add_card_filter_not (s := parallelograms (N y)) (p := degenerate)
    simpa only [G,D,add_comm] using h.symm
  have hgood : (∑ y, (G y).card) ≤ 3*Fintype.card V^3 := by
    have hswap : (∑ y, (G y).card) = ∑ p : V × V × V,
        if degenerate p then 0 else (commonParallelogram N p.1 p.2.1 p.2.2).card := by
      simp only [G,parallelograms,filter_filter,card_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      by_cases hp : degenerate p
      · simp [hp]
      · simp only [hp,not_false_eq_true,and_true,if_false,commonParallelogram,card_filter]
    rw [hswap]
    calc
      _ ≤ ∑ _p : V × V × V, 3 := by
        apply sum_le_sum
        intro p _
        split_ifs with hp
        · omega
        · have hh : p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.1 ≠ p.2.2 ∧ p.2.1+p.2.2 ≠ 0 := by
            simpa only [degenerate,not_or] using hp
          exact Erdos714EnergyThinning.commonParallelogram_le_three N hf _ _ _
            hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
      _ = _ := by simp [Fintype.card_prod]; ring
  have hbad : (∑ y, (D y).card) ≤ 4*∑ y, (N y).card^2 := by
    have h := sum_le_sum (s := (univ : Finset Y)) (fun y _ => degenerate_card (N y))
    simpa only [D,← mul_sum] using h
  simp_rw [he]
  rw [sum_add_distrib]
  omega

/-- Different columns may use different additive maps and different levels.
Every selected neighborhood is only required to lie in its stated fiber. -/
theorem fourth_power (l : Y → V →+ A) (a : Y → A) (K : ℕ)
    (hK : ∀ y, (univ.filter (fun v => l y v=0)).card ≤ K)
    (N : Y → Finset V) (hN : ∀ y v, v ∈ N y → l y v=a y)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N)) :
    (∑ y, (N y).card)^4 ≤ Fintype.card Y^3*K*
      (3*Fintype.card V^3+4*Fintype.card Y*K^2) := by
  have hc (y : Y) : (N y).card ≤ K := by
    calc
      _ ≤ (univ.filter (fun v => l y v=a y)).card := card_le_card (fun v hv => mem_filter.mpr ⟨mem_univ _,hN y v hv⟩)
      _ ≤ (univ.filter (fun v => l y v=0)).card := Erdos714EnergyThinning.fiber_card_le_kernel _ _
      _ ≤ K := hK y
  have hlow : (∑ y, (N y).card)^4 ≤ Fintype.card Y^3*K*∑ y, (N y).addEnergy (N y) := by
    calc
      _ ≤ Fintype.card Y^3*∑ y, (N y).card^4 := by
        simpa using Erdos714EnergyThinning.fourth_moment (univ : Finset Y) (fun y => (N y).card)
      _ ≤ Fintype.card Y^3*∑ y, K*(N y).addEnergy (N y) := by
        apply Nat.mul_le_mul_left
        exact sum_le_sum (fun y _ => (Erdos714EnergyThinning.fiber_energy_bound (l y) (N y) (a y) (hN y)).trans
          (Nat.mul_le_mul_right _ (hK y)))
      _ = _ := by rw [← mul_sum]; ring
  have hsq : (∑ y, (N y).card^2) ≤ Fintype.card Y*K^2 := by
    have h := sum_le_sum (s := (univ : Finset Y)) (fun y _ => Nat.pow_le_pow_left (hc y) 2)
    simpa using h
  have hup := neighborhood_energy N hf
  exact hlow.trans (Nat.mul_le_mul_left _ (by nlinarith only [hup,hsq]))

/-- The q²-by-q⁴ case loses a quarter power from its q⁵ host edge scale. -/
theorem critical_layer (l : Y → V →+ A) (a : Y → A) (q : ℕ)
    (hK : ∀ y, (univ.filter (fun v => l y v=0)).card ≤ q)
    (hV : Fintype.card V ≤ q^2) (hY : Fintype.card Y ≤ q^4)
    (N : Y → Finset V) (hN : ∀ y v, v ∈ N y → l y v=a y)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (Erdos714Packing.incidence N)) :
    (∑ y, (N y).card)^4 ≤ 7*q^19 := by
  calc
    _ ≤ Fintype.card Y^3*q*(3*Fintype.card V^3+4*Fintype.card Y*q^2) := fourth_power l a q hK N hN hf
    _ ≤ (q^4)^3*q*(3*(q^2)^3+4*q^4*q^2) := by gcongr
    _ = _ := by ring

#print axioms degenerate_card
#print axioms neighborhood_energy
#print axioms fourth_power
#print axioms critical_layer
end Erdos714AffineFibers
