import Submission.CubicNormSeventhRoots

/-!
Seventh roots give a K44 in the threefold power cover with BASE-FIELD weights,
even after restricting to nonzero points and square weights. This excludes
one proposed construction on stated congruence classes, not Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714ThreefoldSeventhRoots
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]

omit [Fintype E] in
lemma cube_root_in_base (hq : Fintype.card F % 3 = 1) (x : E) (hx : x^3=1) :
    ∃ a : F, algebraMap F E a=x ∧ a^3=1 := by
  have hdvd : 3 ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units]
    omega
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := Fˣ) 3 hdvd
  have hp : IsPrimitiveRoot (u : F) 3 := by
    apply IsPrimitiveRoot.coe_units_iff.mpr
    simpa only [hu] using IsPrimitiveRoot.orderOf u
  have hm := hp.map_of_injective (algebraMap F E).injective
  obtain ⟨i,_,hi⟩ := hm.eq_pow_of_pow_eq_one hx
  refine ⟨(u:F)^i,by simpa using hi,?_⟩
  rw [←pow_mul,pow_mul',hp.pow_eq_one,one_pow]

lemma exponent_seven (q d : ℕ) (hd : 3*d=q^2+q+1)
    (hq : q%7=2 ∨ q%7=4) : 7 ∣ d := by
  have hh : 7 ∣ 3*d := by
    rw [hd,Nat.dvd_iff_mod_eq_zero]
    rcases hq with h | h <;> norm_num [Nat.add_mod,Nat.pow_mod,h]
  exact (by decide : Nat.Coprime 7 3).dvd_of_dvd_mul_left hh

omit [Field F] [Algebra F E] [Fintype E] in
lemma power_root (d : ℕ) (hd : 3*d=Fintype.card F^2+Fintype.card F+1)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) : ζ^d=1 :=
  (hζ.pow_eq_one_iff_dvd d).mpr (exponent_seven _ _ hd hq)

lemma phase_cube (d : ℕ) (hd : 3*d=Fintype.card F^2+Fintype.card F+1)
    (hdegree : Module.finrank F E=3)
    (hq : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) : ((1+ζ)^d)^3=1 := by
  have hn := Erdos714CubicNormSeventhRoots.norm_one_add_root hdegree hq ζ hζ
  have hm := congrArg (algebraMap F E) hn
  rw [FiniteField.algebraMap_norm_eq_pow_sum,hdegree,map_one] at hm
  simp only [sum_range_succ,sum_range_zero,pow_zero,pow_one,zero_add,
    Nat.card_eq_fintype_card] at hm
  rw [←pow_mul,Nat.mul_comm d 3,hd]
  convert hm using 1
  congr 1
  omega

omit [Fintype E] in
lemma cube_root_fixed (q : ℕ) (hq : q%3=1) (x : E) (hx : x^3=1) : x^q=x := by
  rw [pow_eq_pow_mod q hx,hq,pow_one]

lemma phases (d : ℕ) (hd : 3*d=Fintype.card F^2+Fintype.card F+1)
    (hdegree : Module.finrank F E=3) (hq3 : Fintype.card F%3=1)
    (hq7 : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) (k : ℕ) (hk0 : 0<k) (hk7 : k<7) :
    (1+ζ^k)^d=(1+ζ)^d := by
  have hz := power_root d hd hq7 ζ hζ
  have hc := phase_cube d hd hdegree hq7 ζ hζ
  have hf := cube_root_fixed _ hq3 _ hc
  have hf2 : ((1+ζ)^d)^(Fintype.card F^2)=(1+ζ)^d := by
    rw [pow_two,pow_mul,hf,hf]
  have hF (x : E) : (1+x)^Fintype.card F=1+x^Fintype.card F := by
    simpa only [FiniteField.frobeniusAlgHom_apply,map_one] using
      (FiniteField.frobeniusAlgHom F E).map_add 1 x
  have hF2 : (1+ζ)^(Fintype.card F^2)=1+ζ^(Fintype.card F^2) := by
    rw [pow_two,pow_mul,hF,hF,←pow_mul]
  have he1 : (1+ζ^(Fintype.card F%7))^d=(1+ζ)^d := by
    rw [←pow_eq_pow_mod (Fintype.card F) hζ.pow_eq_one,←hF,←pow_mul,
      Nat.mul_comm (Fintype.card F) d,pow_mul]
    exact hf
  have he2 : (1+ζ^((Fintype.card F^2)%7))^d=(1+ζ)^d := by
    rw [←pow_eq_pow_mod (Fintype.card F^2) hζ.pow_eq_one,←hF2,←pow_mul,
      Nat.mul_comm (Fintype.card F^2) d,pow_mul]
    exact hf2
  have he24 : (1+ζ^2)^d=(1+ζ)^d ∧ (1+ζ^4)^d=(1+ζ)^d := by
    rcases hq7 with h | h
    · constructor
      · simpa only [h] using he1
      · simpa only [Nat.pow_mod,h,Nat.reducePow,Nat.reduceMod] using he2
    · constructor
      · simpa only [Nat.pow_mod,h,Nat.reducePow,Nat.reduceMod] using he2
      · simpa only [h] using he1
  have hinv (j : ℕ) (hj : j≤7) : (1+ζ^(7-j))^d=(1+ζ^j)^d := by
    have he : (1+ζ^j)*ζ^(7-j)=1+ζ^(7-j) := by
      rw [add_mul,one_mul,←pow_add,Nat.add_sub_of_le hj,hζ.pow_eq_one,add_comm]
    rw [←he,mul_pow,←pow_mul,pow_mul',hz,one_pow,mul_one]
  interval_cases k
  · simp
  · exact he24.1
  · simpa only [Nat.reduceSub] using (hinv 4 (by omega)).trans he24.2
  · exact he24.2
  · simpa only [Nat.reduceSub] using (hinv 2 (by omega)).trans he24.1
  · simpa only [Nat.reduceSub,pow_one] using hinv 1 (by omega)


lemma power_sum (d : ℕ) (hd : 3*d=Fintype.card F^2+Fintype.card F+1)
    (hdegree : Module.finrank F E=3) (hq3 : Fintype.card F%3=1)
    (hq7 : Fintype.card F%7=2 ∨ Fintype.card F%7=4)
    (ζ : E) (hζ : IsPrimitiveRoot ζ 7) (i j : ℕ) (hij : i<j) (hj : j<7) :
    (ζ^i+ζ^j)^d=(1+ζ)^d := by
  have he : ζ^i+ζ^j=ζ^i*(1+ζ^(j-i)) := by
    rw [mul_add,mul_one,←pow_add,Nat.add_sub_of_le hij.le]
  rw [he,mul_pow,←pow_mul,pow_mul',power_root d hd hq7 ζ hζ,one_pow,one_mul]
  exact phases d hd hdegree hq3 hq7 ζ hζ _ (by omega) (by omega)

/-- Opposite translation removes every zero point without changing any sum. -/
lemma translate_nonzero (L R : Fin 4 ↪ E) (hsize : 8<Fintype.card E) :
    ∃ c : E, (∀ i, L i+c ≠ 0) ∧ (∀ j, R j-c ≠ 0) := by
  let S : Finset E := (univ.image (fun i => -L i)) ∪ (univ.image R)
  have hS : S.card ≤ 8 := by
    calc
      S.card ≤ (univ.image (fun i => -L i)).card+(univ.image R).card := card_union_le _ _
      _ ≤ (univ : Finset (Fin 4)).card+(univ : Finset (Fin 4)).card :=
        Nat.add_le_add (card_image_le) (card_image_le)
      _ = 8 := by simp
  have hne : S ≠ univ := (card_lt_iff_ne_univ S).mp (lt_of_le_of_lt hS hsize)
  obtain ⟨c,hc⟩ := not_forall.mp (show ¬ ∀ c, c ∈ S from fun h => hne (eq_univ_of_forall h))
  refine ⟨c,?_,?_⟩
  · intro i he
    apply hc
    apply mem_union_left
    apply mem_image.mpr
    exact ⟨i,mem_univ _,by linear_combination -he⟩
  · intro j he
    apply hc
    apply mem_union_right
    apply mem_image.mpr
    exact ⟨j,mem_univ _,sub_eq_zero.mp he⟩

omit [Fintype F] in
lemma cube_root_square (a : F) (ha : a^3=1) : a ≠ 0 ∧ IsSquare a := by
  constructor
  · intro h
    simp [h] at ha
  · refine ⟨a^2,?_⟩
    calc
      a = a*a^3 := by rw [ha,mul_one]
      _ = a^2*a^2 := by ring

/-- Both sides use actual base-field weights, all square and nonzero. -/
def relation (d : ℕ) (u v : E × F) : Prop :=
  u.1 ≠ 0 ∧ v.1 ≠ 0 ∧ u.2 ≠ 0 ∧ v.2 ≠ 0 ∧
    IsSquare u.2 ∧ IsSquare v.2 ∧ (u.1+v.1)^d=algebraMap F E (u.2*v.2)

def graph (d : ℕ) : SimpleGraph ((E × F) ⊕ (E × F)) where
  Adj u v := match u,v with
    | .inl x,.inr y => relation d x y
    | .inr y,.inl x => relation d x y
    | _,_ => False
  symm := by intro u v; cases u <;> cases v <;> exact id
  loopless := by intro u; cases u <;> exact not_false

/-- An actual copy, including the nonzero-point and square-weight restrictions. -/
theorem exists_copy (d : ℕ) (hd : 3*d=Fintype.card F^2+Fintype.card F+1)
    (hdegree : Module.finrank F E=3) (hq3 : Fintype.card F%3=1)
    (hq7 : Fintype.card F%7=2 ∨ Fintype.card F%7=4) :
    Nonempty (Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (F := F) (E := E) d)) := by
  obtain ⟨ζ,hζ⟩ := Erdos714CubicNormSeventhRoots.exists_root hdegree hq7
  obtain ⟨a,ha,hac⟩ := cube_root_in_base hq3 _ (phase_cube d hd hdegree hq7 ζ hζ)
  have has := cube_root_square a hac
  let L : Fin 4 ↪ E := ⟨Erdos714CubicNormSeventhRoots.left ζ,
    Erdos714CubicNormSeventhRoots.left_injective ζ hζ⟩
  let R : Fin 4 ↪ E := ⟨Erdos714CubicNormSeventhRoots.right ζ,
    Erdos714CubicNormSeventhRoots.right_injective ζ hζ⟩
  have hcard : Fintype.card E=Fintype.card F^3 := by
    rw [Module.card_eq_pow_finrank (K := F),hdegree]
  have hq : 4≤Fintype.card F := by have := Fintype.one_lt_card (α := F); omega
  have hsize : 8<Fintype.card E := by
    rw [hcard]
    nlinarith [Nat.pow_le_pow_left hq 3]
  obtain ⟨c,hL,hR⟩ := translate_nonzero L R hsize
  let l : Fin 4 ↪ E × F := ⟨fun i => (L i+c,1),by
    intro i j h
    exact L.injective (add_right_cancel (congrArg Prod.fst h))⟩
  let r : Fin 4 ↪ E × F := ⟨fun j => (R j-c,if j=0 then 1 else a),by
    intro i j h
    exact R.injective (sub_left_injective (congrArg Prod.fst h))⟩
  have he (i j : Fin 4) : relation d (l i) (r j) := by
    refine ⟨hL i,hR j,one_ne_zero,?_,IsSquare.one,?_,?_⟩
    · change (if j=0 then 1 else a) ≠ 0
      split <;> simp_all
    · change IsSquare (if j=0 then 1 else a)
      split <;> simp_all [IsSquare.one]
    · change (L i+c+(R j-c))^d=algebraMap F E (1*(if j=0 then 1 else a))
      rw [show L i+c+(R j-c)=L i+R j by ring,one_mul]
      by_cases hj : j=0
      · subst j
        simp only [L,R,Erdos714CubicNormSeventhRoots.left,Erdos714CubicNormSeventhRoots.right,
          Function.Embedding.coeFn_mk,ite_true,add_zero,map_one]
        rw [←pow_mul,pow_mul',power_root d hd hq7 ζ hζ,one_pow]
      · simp only [L,R,Erdos714CubicNormSeventhRoots.left,Erdos714CubicNormSeventhRoots.right,
          Function.Embedding.coeFn_mk,if_neg hj]
        rw [ha]
        exact power_sum d hd hdegree hq3 hq7 ζ hζ _ _ (by omega) (by omega)
  refine ⟨⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩⟩
  intro x y hxy
  cases x with
  | inl i => cases y with
    | inl j => simp at hxy
    | inr j => exact he i j
  | inr i => cases y with
    | inr j => simp at hxy
    | inl j => exact he j i

/-- The exponent is the original threefold power, not an independently assigned map. -/
theorem not_free (hdegree : Module.finrank F E=3) (hq3 : Fintype.card F%3=1)
    (hq7 : Fintype.card F%7=2 ∨ Fintype.card F%7=4) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := F) (E := E) ((Fintype.card F^2+Fintype.card F+1)/3)) := by
  intro hf
  apply hf
  apply exists_copy _ _ hdegree hq3 hq7
  have hm : (Fintype.card F^2+Fintype.card F+1)%3=0 := by
    norm_num [Nat.add_mod,Nat.pow_mod,hq3]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)


section ConcreteFamily
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
abbrev Base (k : ℕ) := GaloisField 37 (3*k+1)
abbrev Ext (k : ℕ) := FiniteField.Extension (Base k) 37 3
local instance (k : ℕ) : Fintype (Base k) := Fintype.ofFinite _
local instance (k : ℕ) : Fintype (Ext k) := Fintype.ofFinite _

def familyGraph (k : ℕ) : SimpleGraph ((Ext k × Base k) ⊕ (Ext k × Base k)) :=
  graph (((37^(3*k+1))^2+37^(3*k+1)+1)/3)

/-- An explicit unbounded family, with the cubic extension and all cardinality
and congruence hypotheses discharged rather than supplied as assumptions. -/
theorem family_not_free (k : ℕ) :
    ¬(completeBipartiteGraph (Fin 4) (Fin 4)).Free (familyGraph k) := by
  have hc : Fintype.card (Base k)=37^(3*k+1) := by
    rw [Fintype.card_eq_nat_card,GaloisField.card 37 _ (by omega)]
  have h3 : Fintype.card (Base k)%3=1 := by
    rw [hc]
    norm_num [Nat.pow_mod]
  have h7 : Fintype.card (Base k)%7=2 := by
    rw [hc,pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  have hn := not_free (FiniteField.finrank_extension (Base k) 37 3) h3 (Or.inl h7)
  simpa only [familyGraph,hc] using hn
end ConcreteFamily

#print axioms cube_root_in_base
#print axioms phases
#print axioms power_sum
#print axioms translate_nonzero
#print axioms exists_copy
#print axioms not_free
#print axioms family_not_free
end Erdos714ThreefoldSeventhRoots
