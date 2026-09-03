import FormalConjecturesUtil

/-!
The full quartic norm-one torus host has four identical column profiles on
the norm-one circle of its quadratic subfield. This rules out this host as
an unthinned K44-free construction; it does not settle Erdős 714.
-/
noncomputable section
open Classical SimpleGraph Finset
set_option maxHeartbeats 2000000
namespace Erdos714QuarticNormOneTorus
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

abbrev q := Fintype.card F
abbrev D (q : ℕ) := q^3+q^2+q+1

lemma exists_root (hd : Module.finrank F E=4) :
    ∃ v : E, IsPrimitiveRoot v (D (q (F := F))) := by
  let q := Fintype.card F
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hcard : Nat.card Eˣ = q^4-1 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_units,Module.card_eq_pow_finrank (K := F),hd]
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  have hp : IsPrimitiveRoot (g : E) (q^4-1) := by
    apply IsPrimitiveRoot.coe_units_iff.mpr
    simpa only [hg,hcard] using IsPrimitiveRoot.orderOf g
  refine ⟨(g : E)^(q-1),hp.pow (by have : 1 < q^4 := one_lt_pow₀ (by omega) (by decide); omega) ?_⟩
  dsimp [D]
  have he : q^4-1+1=q^4 := Nat.sub_add_cancel (by exact one_le_pow₀ (by omega))
  have hs : q-1+1=q := Nat.sub_add_cancel (by omega)
  nlinarith [show q^4=q*q*q*q by ring]

lemma norm_root (hd : Module.finrank F E=4) (v : E)
    (hv : IsPrimitiveRoot v (D (q (F := F)))) : Algebra.norm F v=1 := by
  apply (algebraMap F E).injective
  rw [FiniteField.algebraMap_norm_eq_pow_sum,hd,map_one]
  simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,zero_add,Nat.card_eq_fintype_card]
  convert hv.pow_eq_one using 2
  dsimp [D,q]
  omega

omit [Fintype F] [Fintype E] in
lemma norm_neg_one (hd : Module.finrank F E=4) : Algebra.norm F (-1:E)=1 := by
  have he : (-1:E)=algebraMap F E (-1:F) := by simp
  rw [he,Algebra.norm_algebraMap,hd]
  norm_num

lemma profile (hd : Module.finrank F E=4) {v u : E}
    (hv : Algebra.norm F v=1) (hu : u^(q (F := F)+1)=1) :
    Algebra.norm F ((v^(q (F := F)))⁻¹-u)=Algebra.norm F (v-u) := by
  let q := Fintype.card F
  have hv0 : v ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have hu0 : u ≠ 0 := by intro he; simp [he] at hu
  have hNu : Algebra.norm F u=1 := by
    apply (algebraMap F E).injective
    rw [FiniteField.algebraMap_norm_eq_pow_sum,hd,map_one]
    simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,zero_add,Nat.card_eq_fintype_card]
    have hp : 1+q+q^2+q^3=(q+1)*(q^2+1) := by ring
    change u^(1+q+q^2+q^3)=1
    rw [hp,pow_mul,hu,one_pow]
  have hfrob : (v-u)^q=v^q-u^q := by
    simpa only [FiniteField.frobeniusAlgHom_apply] using
      (FiniteField.frobeniusAlgHom F E).map_sub v u
  have he : (v^q)⁻¹-u=(-u/(v^q))*(v-u)^q := by
    rw [hfrob]
    have hu' : u*u^q=1 := by simpa only [pow_succ,mul_comm] using hu
    field_simp
    linear_combination -hu'
  rw [he,map_mul,div_eq_mul_inv,map_mul,show -u=(-1:E)*u by ring,map_mul,norm_neg_one hd,hNu,
    Algebra.norm_inv,
    map_pow,hv,one_pow,mul_one,inv_one,one_mul,map_pow,FiniteField.pow_card,one_mul]

lemma twist_norm {v : E} (hv : Algebra.norm F v=1) :
    Algebra.norm F ((v^(q (F := F)))⁻¹)=1 := by
  rw [Algebra.norm_inv,map_pow,hv,one_pow,inv_one]

omit [Field F] [Fintype E] [Algebra F E] in
lemma twist_twice (v : E) :
    (((v^(q (F := F)))⁻¹)^(q (F := F)))⁻¹=v^(q (F := F)^2) := by
  rw [inv_pow,inv_inv,←pow_mul,pow_two]

lemma twist_four (hd : Module.finrank F E=4) (v : E) :
    (((v^(q (F := F)^2))^(q (F := F)))⁻¹)^(q (F := F))=v⁻¹ := by
  rw [inv_pow,←pow_mul,←pow_mul]
  have he : q (F := F)^2*(q (F := F)*q (F := F))=Fintype.card E := by
    rw [Module.card_eq_pow_finrank (K := F),hd]; dsimp [q]; ring
  rw [he,FiniteField.pow_card]


def left (v : E) (i : Fin 4) : E := (v^(q (F := F)^2+1))^(i : ℕ)
def exponent (q : ℕ) : Fin 4 → ℕ := ![1,q^3+q^2+1,q^2,q^2+q+1]
def right (v : E) (j : Fin 4) : E := v^(exponent (q (F := F)) j)

omit [Field F] [Fintype E] [Algebra F E] in
lemma circle_root (v : E) (hv : IsPrimitiveRoot v (D (q (F := F)))) :
    IsPrimitiveRoot (v^(q (F := F)^2+1)) (q (F := F)+1) := by
  exact hv.pow (by dsimp [D]; omega) (by dsimp [D]; ring)

omit [Field F] [Fintype E] [Algebra F E] in
lemma left_injective (hq : 3 ≤ q (F := F)) (v : E)
    (hv : IsPrimitiveRoot v (D (q (F := F)))) : Function.Injective (left (F := F) v) := by
  intro i j he
  apply Fin.ext
  exact (circle_root v hv).pow_inj (by omega) (by omega) he

omit [Field F] [Fintype E] [Algebra F E] in
lemma left_circle (v : E) (hv : IsPrimitiveRoot v (D (q (F := F)))) (i : Fin 4) :
    left (F := F) v i^(q (F := F)+1)=1 := by
  dsimp [left]
  rw [←pow_mul,mul_comm,pow_mul,(circle_root v hv).pow_eq_one,one_pow]

lemma left_norm (hd : Module.finrank F E=4) (v : E)
    (hv : IsPrimitiveRoot v (D (q (F := F)))) (i : Fin 4) :
    Algebra.norm F (left (F := F) v i)=1 := by
  simp only [left,map_pow,norm_root hd v hv,one_pow]

omit [Fintype E] [Algebra F E] in
lemma right_injective (v : E) (hv : IsPrimitiveRoot v (D (q (F := F)))) :
    Function.Injective (right (F := F) v) := by
  have hq : 2 ≤ q (F := F) := Fintype.one_lt_card
  have hq2 : q (F := F) < q (F := F)^2 := by nlinarith
  have hq3 : q (F := F)^2 < q (F := F)^3 := by nlinarith [sq_nonneg (q (F := F)-1 : ℤ)]
  intro i j he
  have hb (i : Fin 4) : exponent (q (F := F)) i < D (q (F := F)) := by
    fin_cases i <;> simp [exponent,D] <;> omega
  have hh := hv.pow_inj (hb i) (hb j) he
  fin_cases i <;> fin_cases j <;> simp [exponent] at hh ⊢ <;> omega

omit [Field F] [Fintype E] [Algebra F E] in
lemma right_twists (v : E) (hv : IsPrimitiveRoot v (D (q (F := F)))) :
    right (F := F) v 0=v ∧
    right (F := F) v 1=(v^(q (F := F)))⁻¹ ∧
    right (F := F) v 2=v^(q (F := F)^2) ∧
    right (F := F) v 3=((v^(q (F := F)^2))^(q (F := F)))⁻¹ := by
  refine ⟨by simp [right,exponent],?_,by simp [right,exponent],?_⟩
  · apply eq_inv_of_mul_eq_one_left
    dsimp [right,exponent]
    rw [←pow_add]
    convert hv.pow_eq_one using 2
    dsimp [D]
    omega
  · apply eq_inv_of_mul_eq_one_left
    dsimp [right,exponent]
    rw [←pow_mul,←pow_add]
    convert hv.pow_eq_one using 2
    dsimp [D]
    ring

lemma right_norm (hd : Module.finrank F E=4) (v : E)
    (hv : IsPrimitiveRoot v (D (q (F := F)))) (j : Fin 4) :
    Algebra.norm F (right (F := F) v j)=1 := by
  simp only [right,map_pow,norm_root hd v hv,one_pow]

lemma edges (hd : Module.finrank F E=4) (v : E)
    (hv : IsPrimitiveRoot v (D (q (F := F)))) (i j : Fin 4) :
    Algebra.norm F (right (F := F) v j-left (F := F) v i)=
      Algebra.norm F (v-left (F := F) v i) := by
  obtain ⟨h0,h1,h2,h3⟩ := right_twists (F := F) v hv
  have hn := norm_root hd v hv
  have hc := left_circle v hv i
  have hp := profile hd hn hc
  have hp2 := profile hd (twist_norm hn) hc
  rw [twist_twice] at hp2
  have hnn : Algebra.norm F (v^(q (F := F)^2))=1 := by rw [map_pow,hn,one_pow]
  have hp3 := profile hd hnn hc
  fin_cases j
  · exact congrArg (fun z => Algebra.norm F (z-left (F := F) v i)) h0
  · exact (congrArg (fun z => Algebra.norm F (z-left (F := F) v i)) h1).trans hp
  · exact (congrArg (fun z => Algebra.norm F (z-left (F := F) v i)) h2).trans (hp2.trans hp)
  · exact (congrArg (fun z => Algebra.norm F (z-left (F := F) v i)) h3).trans (hp3.trans (hp2.trans hp))

lemma weights_ne_zero (v : E) (hv : IsPrimitiveRoot v (D (q (F := F)))) (i : Fin 4) :
    Algebra.norm F (v-left (F := F) v i) ≠ 0 := by
  apply Algebra.norm_ne_zero_iff.mpr
  intro he
  have he' := sub_eq_zero.mp he
  have hh : v^(q (F := F)+1)=1 := by rw [he']; exact left_circle v hv i
  have hdiv := hv.dvd_of_pow_eq_one _ hh
  have hq : 2 ≤ q (F := F) := Fintype.one_lt_card
  apply Nat.not_dvd_of_pos_of_lt (by omega : 0 < q (F := F)+1) _ hdiv
  dsimp [D]
  nlinarith

abbrev Vertex (F E : Type*) [Field F] [Field E] [Algebra F E] :=
  {v : E // Algebra.norm F v=1} × Fˣ

def graph : SimpleGraph (Vertex F E ⊕ Vertex F E) where
  Adj x y := match x,y with
    | .inl x,.inr y => Algebra.norm F (y.1.val-x.1.val)=(x.2 : F)*(y.2 : F)
    | .inr y,.inl x => Algebra.norm F (y.1.val-x.1.val)=(x.2 : F)*(y.2 : F)
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

/-- Every full quartic norm-one torus host over a field with at least three
 elements contains K44. The norm and vertex restrictions are the actual ones. -/
theorem not_free (hd : Module.finrank F E=4) (hq : 3 ≤ q (F := F)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) (E := E)) := by
  obtain ⟨v,hv⟩ := exists_root hd
  let l : Fin 4 ↪ Vertex F E := ⟨fun i =>
    (⟨left (F := F) v i,left_norm hd v hv i⟩,
      Units.mk0 (Algebra.norm F (v-left (F := F) v i)) (weights_ne_zero v hv i)),by
    intro i j he
    exact left_injective hq v hv (congrArg (fun z : Vertex F E => z.1.val) he)⟩
  let r : Fin 4 ↪ Vertex F E := ⟨fun j =>
    (⟨right (F := F) v j,right_norm hd v hv j⟩,1),by
    intro i j he
    exact right_injective v hv (congrArg (fun z : Vertex F E => z.1.val) he)⟩
  have he (i j : Fin 4) : (graph (F := F) (E := E)).Adj (.inl (l i)) (.inr (r j)) := by
    change Algebra.norm F (right (F := F) v j-left (F := F) v i)=
      Algebra.norm F (v-left (F := F) v i)*1
    rw [mul_one]
    exact edges hd v hv i j
  intro hf
  apply hf
  refine ⟨⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact he i j
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact he j i

#print axioms exists_root
#print axioms profile
#print axioms left_injective
#print axioms right_injective
#print axioms edges
#print axioms not_free
end Erdos714QuarticNormOneTorus
