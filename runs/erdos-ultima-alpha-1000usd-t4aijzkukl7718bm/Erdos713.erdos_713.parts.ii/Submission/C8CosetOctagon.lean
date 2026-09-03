import FormalConjecturesUtil

/-! A group-theoretic octagon criterion for coset incidence graphs.
This is an auxiliary construction obstruction, not a solution of Erdos 713. -/
open SimpleGraph
namespace Erdos713C8CosetOctagon
variable {G : Type*} [Group G]
set_option maxHeartbeats 2000000

/-- The two cosets are incident when they share a group element. -/
def Inc (H K : Subgroup G) (a : G ⧸ H) (b : G ⧸ K) : Prop :=
  ∃ g : G, (g : G ⧸ H) = a ∧ (g : G ⧸ K) = b

def graph (H K : Subgroup G) : SimpleGraph ((G ⧸ H) ⊕ (G ⧸ K)) where
  Adj a b := match a,b with
    | .inl p,.inr l => Inc H K p l
    | .inr l,.inl p => Inc H K p l
    | _,_ => False
  symm := by intro a b; cases a <;> cases b <;> exact id
  loopless := by intro a; cases a <;> exact id

lemma contains_of_octagon (H K : Subgroup G)
    (p : Fin 4 → G ⧸ H) (l : Fin 4 → G ⧸ K)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, Inc H K (p i) (l i))
    (hB : ∀ i, Inc H K (p (i+1)) (l i)) :
    cycleGraph 8 ⊑ graph H K := by
  let f : Fin 8 → (G ⧸ H) ⊕ (G ⧸ K) :=
    ![Sum.inl (p 0),Sum.inr (l 0),Sum.inl (p 1),Sum.inr (l 1),
      Sum.inl (p 2),Sum.inr (l 2),Sum.inl (p 3),Sum.inr (l 3)]
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try (exfalso; revert hij; decide)
    all_goals dsimp [f,graph]
    all_goals first | exact hA 0 | exact hA 1 | exact hA 2 | exact hA 3 | exact hB 0 | exact hB 1 | exact hB 2 | exact hB 3
  · intro i j hij
    change f i = f j at hij
    fin_cases i <;> fin_cases j <;> dsimp [f] at hij
    all_goals first | rfl | (have he := hp (Sum.inl.inj hij); exfalso; revert he; decide) | (have he := hl (Sum.inr.inj hij); exfalso; revert he; decide) | cases hij

def powers (m : G) : Fin 4 → G := ![1,m,m^2,m^3]

lemma cube_eq_inv (m : G) (h4 : m^4 = 1) : m^3 = m⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using h4

lemma orbit_injective (H : Subgroup G) (m : G) (h4 : m^4 = 1)
    (h1 : m ∉ H) (h2 : m^2 ∉ H) :
    Function.Injective (fun i : Fin 4 => ((powers m i : G) : G ⧸ H)) := by
  have h01 : ((1 : G) : G ⧸ H) ≠ (m : G ⧸ H) := by
    simpa only [Ne,QuotientGroup.eq,inv_one,one_mul] using h1
  have h02 : ((1 : G) : G ⧸ H) ≠ (m^2 : G) := by
    simpa only [Ne,QuotientGroup.eq,inv_one,one_mul] using h2
  have h03 : ((1 : G) : G ⧸ H) ≠ (m^3 : G) := by
    simpa only [Ne,QuotientGroup.eq,inv_one,one_mul,cube_eq_inv m h4,
      H.inv_mem_iff] using h1
  have h12 : (m : G ⧸ H) ≠ (m^2 : G) := by
    simpa only [Ne,QuotientGroup.eq,pow_two,inv_mul_cancel_left] using h1
  have h13 : (m : G ⧸ H) ≠ (m^3 : G) := by
    rw [Ne,QuotientGroup.eq,show m⁻¹*m^3=m^2 by group]
    exact h2
  have h23 : (m^2 : G) ≠ ((m^3 : G) : G ⧸ H) := by
    rw [Ne,QuotientGroup.eq,show (m^2)⁻¹*m^3=m by group]
    exact h1
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | (
    dsimp [powers] at he
    first | exact (h01 he).elim | exact (h01 he.symm).elim |
      exact (h02 he).elim | exact (h02 he.symm).elim |
      exact (h03 he).elim | exact (h03 he.symm).elim |
      exact (h12 he).elim | exact (h12 he.symm).elim |
      exact (h13 he).elim | exact (h13 he.symm).elim |
      exact (h23 he).elim | exact (h23 he.symm).elim)

/-- Powers of the product yield an injective octagon if the product and
its square avoid each relevant subgroup. No finiteness or trivial-
intersection assumption is needed. -/
theorem contains (H K : Subgroup G) (x y : G) (hx : x ∈ H) (hy : y ∈ K)
    (h4 : (x*y)^4 = 1)
    (hH1 : x*y ∉ H) (hH2 : (x*y)^2 ∉ H)
    (hK1 : y*x ∉ K) (hK2 : (y*x)^2 ∉ K) :
    cycleGraph 8 ⊑ graph H K := by
  let m := x*y
  let n := y*x
  have hn4 : n^4 = 1 := by
    calc
      n^4 = x⁻¹*(x*y)^4*x := by dsimp [n]; simp only [pow_succ,pow_zero]; group
      _ = 1 := by rw [h4]; group
  let p : Fin 4 → G ⧸ H := fun i => ((powers m i : G) : G ⧸ H)
  let l : Fin 4 → G ⧸ K := fun i => (powers m i*x : G ⧸ K)
  have hp : Function.Injective p := orbit_injective H m h4 hH1 hH2
  have hpow : ∀ i : Fin 4, powers m i*x = x*powers n i := by
    intro i
    fin_cases i <;> dsimp [powers,m,n] <;> (try simp only [pow_succ,pow_zero]) <;> group
  have hl : Function.Injective l := by
    intro i j he
    apply orbit_injective K n hn4 hK1 hK2
    apply QuotientGroup.eq.mpr
    have hh := QuotientGroup.eq.mp he
    change (powers m i*x)⁻¹*(powers m j*x) ∈ K at hh
    rw [hpow i,hpow j] at hh
    simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hh
  apply contains_of_octagon H K p l hp hl
  · intro i
    refine ⟨powers m i*x,?_,rfl⟩
    apply QuotientGroup.eq.mpr
    change (powers m i*x)⁻¹*powers m i ∈ H
    simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one] using H.inv_mem hx
  · intro i
    have hnext : powers m (i+1) = powers m i*m := by
      fin_cases i <;> dsimp [powers]
      · simp
      · exact pow_two _
      · exact pow_succ _ _
      · simpa only [← pow_succ] using h4.symm
    refine ⟨powers m (i+1),rfl,?_⟩
    apply QuotientGroup.eq.mpr
    change (powers m (i+1))⁻¹*(powers m i*x) ∈ K
    rw [hnext]
    have heq : (powers m i*m)⁻¹*(powers m i*x) = y⁻¹ := by dsimp [m]; group
    rw [heq]
    exact K.inv_mem hy

end Erdos713C8CosetOctagon
