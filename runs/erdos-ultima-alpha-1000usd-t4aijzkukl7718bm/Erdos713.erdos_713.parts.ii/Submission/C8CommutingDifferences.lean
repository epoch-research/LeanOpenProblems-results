import FormalConjecturesUtil

/-! A commuting-difference obstruction in bipartite Cayley incidence graphs.
This is an auxiliary C8 construction diagnostic, not a proof of Erdős 713. -/
open SimpleGraph
namespace Erdos713C8CommutingDifferences
set_option maxHeartbeats 2000000
variable {G I : Type*} [Group G]

def Inc (g : I → G) (p l : G) : Prop := ∃ i, l = p*g i

def graph (g : I → G) : SimpleGraph (G ⊕ G) where
  Adj v w := match v,w with
    | .inl p,.inr l => Inc g p l
    | .inr l,.inl p => Inc g p l
    | _,_ => False
  symm := by intro v w; cases v <;> cases w <;> exact id
  loopless := by intro v; cases v <;> exact id

lemma contains_of_octagon (g : I → G) (p l : Fin 4 → G)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hA : ∀ i, Inc g (p i) (l i)) (hB : ∀ i, Inc g (p (i+1)) (l i)) :
    cycleGraph 8 ⊑ graph g := by
  let f : Fin 8 → G ⊕ G :=
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

variable {K : Type*} [Field K]

lemma coord_inv (φ : G → K) (hφ1 : φ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y) (x : G) : φ x⁻¹ = -φ x := by
  have h := hφmul x x⁻¹
  rw [mul_inv_cancel,hφ1] at h
  linear_combination -h

/-- The two additive coordinates distinguish the explicit commutator octagon.
The group itself need not be commutative, finite, or of exponent two. -/
theorem contains_commuting_fibers [CharP K 2]
    (φ ψ : G → K) (hφ1 : φ 1 = 0) (hψ1 : ψ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (hψmul : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a) (hψg : ∀ a, ψ (g a) = a^3)
    (hc : ∀ x y, φ x = φ y → Commute x y) (w : K) (hw : w ≠ 0) (hw1 : w ≠ 1) :
    cycleGraph 8 ⊑ graph g := by
  let a := g 0
  let b := g 1
  let c := g w
  let d := g (w+1)
  let X := a*b⁻¹
  let Y := c*d⁻¹
  have hφX : φ X = 1 := by
    simp only [X,a,b,hφmul,hφg,coord_inv φ hφ1 hφmul,zero_add]
    exact CharTwo.neg_eq _
  have hφY : φ Y = 1 := by
    simp only [Y,c,d,hφmul,hφg,coord_inv φ hφ1 hφmul,CharTwo.neg_eq]
    linear_combination w*(CharTwo.two_eq_zero (R := K))
  have hφXY : φ (X*Y) = 0 := by
    rw [hφmul,hφX,hφY]
    simpa only [one_add_one_eq_two] using (CharTwo.two_eq_zero (R := K))
  have hψX : ψ X = 1 := by
    simp only [X,a,b,hψmul,hψg,coord_inv ψ hψ1 hψmul,zero_pow (by decide : 3 ≠ 0),one_pow,zero_add,CharTwo.neg_eq]
  have hψY : ψ Y = w^2+w+1 := by
    simp only [Y,c,d,hψmul,hψg,coord_inv ψ hψ1 hψmul,CharTwo.neg_eq]
    ring_nf
    reduce_mod_char!
  have hψXY : ψ (X*Y) = w^2+w := by
    rw [hψmul,hψX,hψY]
    linear_combination CharTwo.two_eq_zero (R := K)
  have hww : w^2+w ≠ 0 := by
    have hw' : w+1 ≠ 0 := by simpa only [← CharTwo.sub_eq_add,sub_ne_zero] using hw1
    convert mul_ne_zero hw hw' using 1; ring
  have hXY : Commute X Y := hc X Y (hφX.trans hφY.symm)
  let p : Fin 4 → G := ![1,X,X*Y,Y]
  let l : Fin 4 → G := ![a,X*c,Y*a,c]
  have hp : Function.Injective p := by
    intro i j he
    have h1 := congrArg φ he
    have h2 := congrArg ψ he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [p] at h1 h2
      simp only [hφ1,hφX,hφY,hφXY,hψ1,hψX,hψY,hψXY] at h1 h2
      first | exact (zero_ne_one h1).elim | exact (one_ne_zero h1).elim |
        exact (hww h2).elim | exact (hww h2.symm).elim |
        (exfalso; apply hww; linear_combination h2) |
        (exfalso; apply hww; linear_combination -h2))
  have h1w : 1+w ≠ 0 := by
    rw [add_comm,← CharTwo.sub_eq_add]
    exact sub_ne_zero.mpr hw1
  have hl : Function.Injective l := by
    intro i j he
    have h1 := congrArg φ he
    fin_cases i <;> fin_cases j <;> first | rfl | (
      dsimp [l] at h1
      simp only [hφmul,hφX,hφY,a,c,hφg,add_zero] at h1
      first | exact (zero_ne_one h1).elim | exact (one_ne_zero h1).elim |
        exact (hw h1).elim | exact (hw h1.symm).elim |
        exact (hw1 h1).elim | exact (hw1 h1.symm).elim |
        exact (h1w h1).elim | exact (h1w h1.symm).elim |
        (exfalso; apply hw; linear_combination h1) |
        (exfalso; apply hw; linear_combination -h1) |
        (exfalso; apply one_ne_zero (α := K); linear_combination h1) |
        (exfalso; apply one_ne_zero (α := K); linear_combination -h1))
  apply contains_of_octagon g p l hp hl
  · intro i
    fin_cases i
    · exact ⟨0,(one_mul a).symm⟩
    · exact ⟨w,rfl⟩
    · refine ⟨1,?_⟩
      change Y*a = (X*Y)*b
      have hXb : X*b = a := by simp [X]
      rw [hXY.eq,mul_assoc Y X b,hXb]
    · refine ⟨w+1,?_⟩
      change c = Y*d
      simp [Y]
  · intro i
    fin_cases i
    · refine ⟨1,?_⟩
      change a = X*b
      simp [X]
    · refine ⟨w+1,?_⟩
      change X*c = (X*Y)*d
      simp [Y,mul_assoc]
    · exact ⟨0,rfl⟩
    · exact ⟨w,(one_mul c).symm⟩

theorem contains_commuting_fibers_finite [Fintype K] [CharP K 2]
    (φ ψ : G → K) (hφ1 : φ 1 = 0) (hψ1 : ψ 1 = 0)
    (hφmul : ∀ x y, φ (x*y) = φ x+φ y)
    (hψmul : ∀ x y, ψ (x*y) = ψ x+ψ y)
    (g : K → G) (hφg : ∀ a, φ (g a) = a) (hψg : ∀ a, ψ (g a) = a^3)
    (hc : ∀ x y, φ x = φ y → Commute x y) (hq : 2 < Fintype.card K) :
    cycleGraph 8 ⊑ graph g := by
  classical
  obtain ⟨w,_,hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({0,1} : Finset K).card < (Finset.univ : Finset K).card from
      Finset.card_le_two.trans_lt (by simpa using hq))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hw
  exact contains_commuting_fibers φ ψ hφ1 hψ1 hφmul hψmul g hφg hψg hc w hw.1 hw.2

#print axioms contains_commuting_fibers
#print axioms contains_commuting_fibers_finite
end Erdos713C8CommutingDifferences
