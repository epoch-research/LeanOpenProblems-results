import FormalConjecturesUtil

/-! An exact characteristic-five obstruction to a parabola fusion of finite
upper-half-plane graphs. This does not settle Erdős 714. -/

set_option maxHeartbeats 4000000

noncomputable section
open SimpleGraph Classical

namespace Erdos714UpperHalfPlane
variable {K : Type*} [Field K]

/-- Coordinates `(v,u)` encode `u+v*sqrt(δ)`, with `v != 0`. -/
def numerator (δ : K) (p q : K × K) : K :=
  (q.2-p.2)^2-δ*(q.1-p.1)^2

def denominator (δ : K) (p q : K × K) : K :=
  numerator δ p q-4*δ*p.1*q.1

def level (η t : K) : K := t+η*t^2

/-- The actual cross-ratio relation, with all forbidden denominator and level
values excluded. Zero first coordinates are isolated vertices. -/
def graph (δ η : K) (T : Set K) : SimpleGraph ((K × K) ⊕ (K × K)) where
  Adj p q := match p,q with
    | .inl p,.inr q => p.1 ≠ 0 ∧ q.1 ≠ 0 ∧ denominator δ p q ≠ 0 ∧
        ∃ t ∈ T, t ≠ 0 ∧ level η t ≠ 0 ∧ level η t ≠ 1 ∧
          numerator δ p q / denominator δ p q = level η t
    | .inr q,.inl p => p.1 ≠ 0 ∧ q.1 ≠ 0 ∧ denominator δ p q ≠ 0 ∧
        ∃ t ∈ T, t ≠ 0 ∧ level η t ≠ 0 ∧ level η t ≠ 1 ∧
          numerator δ p q / denominator δ p q = level η t
    | _,_ => False
  symm := by intro p q; cases p <;> cases q <;> simp_all
  loopless := by intro p; cases p <;> simp

lemma denominator_ne_zero {δ η t : K} {p q : K × K}
    (h4 : (4 : K) ≠ 0) (hδ : δ ≠ 0) (hp : p.1 ≠ 0) (hq : q.1 ≠ 0)
    (he : numerator δ p q=level η t*denominator δ p q) : denominator δ p q ≠ 0 := by
  intro hz
  rw [hz,mul_zero] at he
  have hh : 4*δ*p.1*q.1=0 := by
    dsimp [denominator] at hz
    linear_combination he-hz
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 hδ) hp) hq) hh

def scalePoint (d : K) (p : K × K) : K × K := (p.1,d*p.2)

lemma numerator_scale (δ d : K) (p q : K × K) :
    numerator (d^2*δ) (scalePoint d p) (scalePoint d q)=d^2*numerator δ p q := by
  dsimp [numerator,scalePoint]
  ring

lemma denominator_scale (δ d : K) (p q : K × K) :
    denominator (d^2*δ) (scalePoint d p) (scalePoint d q)=d^2*denominator δ p q := by
  dsimp [denominator]
  rw [numerator_scale]
  dsimp [scalePoint]
  ring

/-- Rescaling the real coordinate changes the nonsquare parameter by a square,
without changing any cross-ratio level. -/
def scaleCopy (δ η d : K) (hd : d ≠ 0) (T : Set K) :
    Copy (graph δ η T) (graph (d^2*δ) η T) := by
  let f : K × K ↪ K × K := ⟨scalePoint d,by
    intro p q he
    apply Prod.ext
    · simpa only [scalePoint] using congrArg Prod.fst he
    · apply mul_left_cancel₀ hd
      exact congrArg Prod.snd he⟩
  have he (p q : K × K) (hh : (graph δ η T).Adj (.inl p) (.inr q)) :
      (graph (d^2*δ) η T).Adj (.inl (f p)) (.inr (f q)) := by
    rcases hh with ⟨hp,hq,hden,t,ht,ht0,hlev0,hlev1,hr⟩
    refine ⟨hp,hq,?_,t,ht,ht0,hlev0,hlev1,?_⟩
    · change denominator (d^2*δ) (scalePoint d p) (scalePoint d q) ≠ 0
      rw [denominator_scale]
      exact mul_ne_zero (pow_ne_zero _ hd) hden
    · change numerator (d^2*δ) (scalePoint d p) (scalePoint d q) /
        denominator (d^2*δ) (scalePoint d p) (scalePoint d q)=_
      rw [numerator_scale,denominator_scale,mul_div_mul_left _ _ (pow_ne_zero _ hd)]
      exact hr
  refine ⟨⟨f.sumMap f,?_⟩,(f.sumMap f).injective⟩
  intro u v hh
  cases u with
  | inl p =>
    cases v with
    | inl q => simp [graph] at hh
    | inr q => exact he p q hh
  | inr q =>
    cases v with
    | inl p => exact he p q hh
    | inr p => simp [graph] at hh

section CharFive
variable [CharP K 5]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma two_ne_zero : (2 : K) ≠ 0 :=
  (CharP.cast_eq_zero_iff K 5 2).not.mpr (by decide)
private lemma three_ne_zero : (3 : K) ≠ 0 :=
  (CharP.cast_eq_zero_iff K 5 3).not.mpr (by decide)
private lemma four_ne_zero : (4 : K) ≠ 0 :=
  (CharP.cast_eq_zero_iff K 5 4).not.mpr (by decide)

private def scalar : Fin 4 → K := ![1,2,4,3]
private def left (η : K) (j : Fin 4) : K × K :=
  (scalar j, (3-η)*(1-scalar j))
private def right (η : K) (j : Fin 4) : K × K :=
  (scalar j, (3-η)+scalar j*(2*η+1))
private def label : Fin 4 → Fin 4 → K :=
  ![![2,3,3,2],![2,2,3,3],![3,2,2,3],![3,3,2,2]]

private lemma scalar_injective : Function.Injective (scalar : Fin 4 → K) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals dsimp [scalar] at he
  all_goals have hh := sub_eq_zero.mpr he
  all_goals norm_num at hh
  all_goals reduce_mod_char! at hh
  all_goals norm_num [two_ne_zero (K := K),three_ne_zero (K := K),four_ne_zero (K := K)] at hh

private lemma scalar_ne_zero (i : Fin 4) : (scalar i : K) ≠ 0 := by
  fin_cases i <;> dsimp [scalar] <;> norm_num [two_ne_zero (K := K),three_ne_zero (K := K),four_ne_zero (K := K)]

private lemma eta_ne_nat (η : K) (hη : η^2=2) (n : Fin 5) : η ≠ (n.val : K) := by
  intro he
  rw [he] at hη
  have hh := sub_eq_zero.mpr hη
  fin_cases n <;> norm_num at hh
  all_goals reduce_mod_char! at hh
  all_goals norm_num [two_ne_zero (K := K),three_ne_zero (K := K),four_ne_zero (K := K)] at hh

lemma parameter_ne_zero (η : K) (hη : η^2=2) : (3-η) ≠ 0 := by
  intro h
  apply eta_ne_nat η hη ⟨3,by decide⟩
  change η=3
  linear_combination -h

private lemma level_valid (η : K) (hη : η^2=2) (i j : Fin 4) :
    label (K := K) i j ≠ 0 ∧ level η (label i j) ≠ 0 ∧ level η (label i j) ≠ 1 := by
  have h₀ : (2 : K) ≠ 0 := by norm_num [two_ne_zero (K := K),three_ne_zero (K := K),four_ne_zero (K := K)]
  have h₁ : (3 : K) ≠ 0 := by norm_num [two_ne_zero (K := K),three_ne_zero (K := K),four_ne_zero (K := K)]
  have ha (t : K) (ht : t=2 ∨ t=3) : level η t ≠ 0 ∧ level η t ≠ 1 := by
    rcases ht with rfl | rfl <;> constructor <;> intro he
    all_goals dsimp [level] at he
    · apply eta_ne_nat η hη ⟨2,by decide⟩
      change η=2
      linear_combination (norm := (ring_nf; reduce_mod_char!)) 4*he
    · apply eta_ne_nat η hη ⟨1,by decide⟩
      norm_num only [Nat.cast_one]
      linear_combination (norm := (ring_nf; reduce_mod_char!)) 4*he
    · apply eta_ne_nat η hη ⟨3,by decide⟩
      change η=3
      linear_combination (norm := (ring_nf; reduce_mod_char!)) 4*he
    · apply eta_ne_nat η hη ⟨2,by decide⟩
      change η=2
      linear_combination (norm := (ring_nf; reduce_mod_char!)) 4*he
  fin_cases i <;> fin_cases j <;>
    first | exact ⟨h₀,ha 2 (Or.inl rfl)⟩ | exact ⟨h₁,ha 3 (Or.inr rfl)⟩

private lemma all_identities (η : K) (hη : η^2=2) (i j : Fin 4) :
    numerator (3-η) (left η i) (right η j) =
      level η (label i j)*denominator (3-η) (left η i) (right η j) := by
  have hη3 : η^3=2*η := by calc
    _ = η^2*η := by ring
    _ = _ := by rw [hη]
  fin_cases i <;> fin_cases j <;>
    norm_num [denominator,numerator,level,left,right,scalar,label]
  all_goals apply sub_eq_zero.mp
  all_goals ring_nf
  all_goals simp only [hη,hη3]
  all_goals ring_nf
  all_goals reduce_mod_char!

private lemma all_edges (η : K) (hη : η^2=2) (T : Set K)
    (h₂ : 2 ∈ T) (h₃ : 3 ∈ T) (i j : Fin 4) :
    (graph (3-η) η T).Adj (.inl (left η i)) (.inr (right η j)) := by
  have hi : (left η i).1 ≠ 0 := scalar_ne_zero i
  have hj : (right η j).1 ≠ 0 := scalar_ne_zero j
  have he := all_identities η hη i j
  have hd := denominator_ne_zero (by norm_num [two_ne_zero (K := K),three_ne_zero (K := K),four_ne_zero (K := K)] : (4 : K) ≠ 0)
    (parameter_ne_zero η hη) hi hj he
  have hv := level_valid η hη i j
  refine ⟨hi,hj,hd,label i j,?_,hv.1,hv.2.1,hv.2.2,?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact h₂ | exact h₃
  · exact (div_eq_iff hd).mpr he

/-- A cyclic-four coset certificate, using only the parabola parameters 2 and 3. -/
def gridCopy (η : K) (hη : η^2=2) (T : Set K) (h₂ : 2 ∈ T) (h₃ : 3 ∈ T) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (3-η) η T) := by
  let L : Fin 4 ↪ K × K := ⟨left η, by
    intro i j he
    exact scalar_injective (congrArg Prod.fst he)⟩
  let R : Fin 4 ↪ K × K := ⟨right η, by
    intro i j he
    exact scalar_injective (congrArg Prod.fst he)⟩
  refine ⟨⟨L.sumMap R, ?_⟩, (L.sumMap R).injective⟩
  intro p q hpq
  cases p with
  | inl i =>
    cases q with
    | inl j => simp at hpq
    | inr j => exact all_edges η hη T h₂ h₃ i j
  | inr j =>
    cases q with
    | inl i => exact all_edges η hη T h₂ h₃ i j
    | inr i => simp at hpq

theorem not_free (η : K) (hη : η^2=2) (T : Set K) (h₂ : 2 ∈ T) (h₃ : 3 ∈ T) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (3-η) η T) :=
  fun h => h ⟨gridCopy η hη T h₂ h₃⟩


/-- The square root and its Frobenius conjugate exist at every required
characteristic-five field size. -/
lemma exists_imaginary [Fintype K] (m : ℕ)
    (hcard : Fintype.card K=5^(2*(2*m+1))) :
    ∃ η : K, η^2=2 ∧ η^(5^(2*m+1)) = -η := by
  have hmod : Fintype.card K % 8 = 1 := by
    rw [hcard,pow_mul,Nat.pow_mod]
    norm_num
  have hhalf : (Fintype.card K/2)%4=0 := by omega
  have hc : ringChar K ≠ 2 := by rw [ringChar.eq K 5]; decide
  have h24 : (2 : K)^4=1 := by reduce_mod_char!
  have hs : IsSquare (2 : K) := (FiniteField.isSquare_iff hc two_ne_zero).mpr (by
    rw [pow_eq_pow_mod _ h24,hhalf,pow_zero])
  obtain ⟨η,hη⟩ := hs
  have he : η^2=2 := by simpa only [pow_two] using hη.symm
  have he4 : η^4 = -1 := by
    calc
      _ = (η^2)^2 := by ring
      _ = _ := by rw [he]; reduce_mod_char!
  have he8 : η^8=1 := by
    calc
      _ = (η^4)^2 := by ring
      _ = _ := by rw [he4]; ring
  have he5 : η^5 = -η := by
    calc
      _ = η^4*η := by ring
      _ = _ := by rw [he4]; ring
  have hqmod : 5^(2*m+1)%8=5 := by
    rw [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    norm_num
  exact ⟨η,he,by rw [pow_eq_pow_mod _ he8,hqmod,he5]⟩

lemma finite_parameter_nonsquare [Fintype K] (m : ℕ)
    (hcard : Fintype.card K=5^(2*(2*m+1))) (η : K)
    (hη : η^2=2) (hconj : η^(5^(2*m+1)) = -η) : ¬ IsSquare (3-η) := by
  let q := 5^(2*m+1)
  have hqmod : q%8=5 := by
    dsimp [q]
    rw [pow_add,pow_mul,Nat.mul_mod,Nat.pow_mod]
    norm_num
  have hqodd : q = 2*(q/2)+1 := by omega
  have hqhalf : (q/2)%4=2 := by omega
  have hN : Fintype.card K=q^2 := by rw [hcard]; dsimp [q]; rw [←pow_mul]; congr 1; omega
  have hhalf : Fintype.card K/2=(q+1)*(q/2) := by
    have he : q^2=2*((q+1)*(q/2))+1 := by nth_rw 1 [hqodd]; nth_rw 2 [hqodd]; ring
    rw [hN]
    omega
  have hδq : (3-η)^q=3+η := by
    have hh := map_sub (iterateFrobenius K 5 (2*m+1)) (3 : K) η
    change (3-η)^q=(iterateFrobenius K 5 (2*m+1)) 3-η^q at hh
    rw [map_ofNat,hconj] at hh
    simpa using hh
  have hnorm : (3-η)^(q+1)=2 := by
    rw [pow_add,pow_one,hδq]
    linear_combination (norm := (ring_nf; reduce_mod_char!)) -hη
  have h24 : (2 : K)^4=1 := by reduce_mod_char!
  have heuler : (3-η)^(Fintype.card K/2) = -1 := by
    rw [hhalf,pow_mul,hnorm,pow_eq_pow_mod _ h24,hqhalf]
    reduce_mod_char!
  have hc : ringChar K ≠ 2 := by rw [ringChar.eq K 5]; decide
  intro hs
  have hh := (FiniteField.isSquare_iff hc (parameter_ne_zero η hη)).mp hs
  rw [heuler] at hh
  have hz : (2 : K)=0 := by linear_combination -hh
  exact two_ne_zero hz

/-- This supplies actual nonsplit upper-half-plane parameters, and an actual
K44, for every q=5^(2m+1), not only for the prime-field example. It fixes the
parabola normalization η^2=2; arbitrary imaginary coefficients are not claimed. -/
theorem finite_field_obstruction [Fintype K] (m : ℕ)
    (hcard : Fintype.card K=5^(2*(2*m+1))) :
    ∃ η : K, η^2=2 ∧ η^(5^(2*m+1)) = -η ∧ ¬ IsSquare (3-η) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
        (graph (3-η) η {t | iterateFrobenius K 5 (2*m+1) t=t}) := by
  obtain ⟨η,hη,hconj⟩ := exists_imaginary m hcard
  refine ⟨η,hη,hconj,finite_parameter_nonsquare m hcard η hη hconj,?_⟩
  apply not_free η hη
  · exact map_ofNat (iterateFrobenius K 5 (2*m+1)) 2
  · exact map_ofNat (iterateFrobenius K 5 (2*m+1)) 3


lemma square_ratio [Fintype K] {a b : K} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) :
    IsSquare (a/b) := by
  have ha0 : a ≠ 0 := by intro hz; subst a; exact ha IsSquare.zero
  have hb0 : b ≠ 0 := by intro hz; subst b; exact hb IsSquare.zero
  have hc : ringChar K ≠ 2 := by rw [ringChar.eq K 5]; decide
  have hea : a^(Fintype.card K/2) = -1 := (FiniteField.pow_dichotomy hc ha0).resolve_left
    (fun h => ha ((FiniteField.isSquare_iff hc ha0).mpr h))
  have heb : b^(Fintype.card K/2) = -1 := (FiniteField.pow_dichotomy hc hb0).resolve_left
    (fun h => hb ((FiniteField.isSquare_iff hc hb0).mpr h))
  apply (FiniteField.isSquare_iff hc (div_ne_zero ha0 hb0)).mpr
  rw [div_pow,hea,heb]
  simp

/-- Changing the nonsquare defining the upper half-plane does not rescue the
canonical characteristic-five parabola fusion. -/
theorem all_nonsquare_parameters [Fintype K] (m : ℕ)
    (hcard : Fintype.card K=5^(2*(2*m+1))) (η : K)
    (hη : η^2=2) (hconj : η^(5^(2*m+1)) = -η) (δ : K) (hδ : ¬ IsSquare δ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph δ η {t | iterateFrobenius K 5 (2*m+1) t=t}) := by
  obtain ⟨d,hd⟩ := square_ratio hδ (finite_parameter_nonsquare m hcard η hη hconj)
  have hδ0 : δ ≠ 0 := by intro hz; subst δ; exact hδ IsSquare.zero
  have hd0 : d ≠ 0 := by
    intro hz
    have hh : δ/(3-η)=0 := by simpa [hz] using hd
    exact (div_ne_zero hδ0 (parameter_ne_zero η hη)) hh
  have hscale : d^2*(3-η)=δ := by
    calc
      _ = (δ/(3-η))*(3-η) := by rw [hd]; ring
      _ = _ := div_mul_cancel₀ _ (parameter_ne_zero η hη)
  let T : Set K := {t | iterateFrobenius K 5 (2*m+1) t=t}
  have h₂ : 2 ∈ T := map_ofNat (iterateFrobenius K 5 (2*m+1)) 2
  have h₃ : 3 ∈ T := map_ofNat (iterateFrobenius K 5 (2*m+1)) 3
  intro hf
  rw [←hscale] at hf
  exact hf ⟨(scaleCopy (3-η) η d hd0 T).comp (gridCopy η hη T h₂ h₃)⟩

end CharFive
end Erdos714UpperHalfPlane
#print axioms Erdos714UpperHalfPlane.gridCopy
#print axioms Erdos714UpperHalfPlane.not_free

#print axioms Erdos714UpperHalfPlane.finite_field_obstruction

#print axioms Erdos714UpperHalfPlane.scaleCopy
#print axioms Erdos714UpperHalfPlane.all_nonsquare_parameters
