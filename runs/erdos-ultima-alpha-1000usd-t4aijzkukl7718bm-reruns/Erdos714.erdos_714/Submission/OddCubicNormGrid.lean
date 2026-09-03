import Submission.CubicTraceNormPlane
import Submission.QuinticNormProduct

/-!
A uniform opposite-value grid in finite cubic norm graphs away from
characteristics two and three. This is a construction obstruction, not a
proof or disproof of Erdős 714.
-/
noncomputable section
open Polynomial Classical SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714OddCubicNormGrid
open Erdos714CubicTraceNormPlane
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The cubic map has a collision at zero and one in every field. -/
lemma exists_irreducible [Fintype F] :
    ∃ d : F, d ≠ 0 ∧ Irreducible (pencil 0 (-1) d) := by
  have hn : ¬ Function.Surjective (fun x : F => x^3-x) := by
    intro hs
    have hi := Finite.injective_iff_surjective.mpr hs
    exact zero_ne_one (hi (by simp : (0 : F)^3-0=1^3-1))
  simp only [Function.Surjective,not_forall,not_exists] at hn
  obtain ⟨d,hd⟩ := hn
  refine ⟨d,fun h => hd 0 (by simp [h]),?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [degree_pencil]
  · intro t ht
    apply hd t
    have he : t^3-t-d=0 := by
      simpa [Polynomial.IsRoot,pencil,sub_eq_add_neg] using ht
    exact sub_eq_zero.mp he

/-- Three distinct conjugates with zero sum and a common cubic shift norm. -/
theorem exists_conjugates [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) :
    ∃ d : F, d ≠ 0 ∧ ∃ r : Fin 3 → E, Function.Injective r ∧
      (∀ i, Algebra.trace F E (r i) = 0) ∧ r 0+r 1+r 2=0 ∧
      ∀ i (t : F), Algebra.norm F (r i+algebraMap F E t)=t^3-t+d := by
  obtain ⟨d,hd,hp⟩ := exists_irreducible (F := F)
  obtain ⟨pb,hpb,hmin⟩ := exists_powerBasis hdim 0 (-1) d hp
  letI : FiniteDimensional F E := pb.finite
  have ht : Algebra.trace F E pb.gen = 0 := by
    rw [pb.trace_gen_eq_nextCoeff_minpoly,hmin]
    rw [Polynomial.nextCoeff,degree_pencil]
    norm_num [pencil,coeff_X]
  have hz : pb.gen^3=pb.gen+algebraMap F E d := by
    have h := minpoly.aeval F pb.gen
    rw [hmin] at h
    simp [pencil, map_add] at h
    linear_combination h
  let B : Module.Basis (Fin 3) F E := pb.basis.reindex (finCongr hpb)
  have hB (i : Fin 3) : B i=pb.gen^(i : ℕ) := by simp [B]
  have hn (t : F) : Algebra.norm F (pb.gen+algebraMap F E t)=t^3-t+d := by
    have h := Erdos714QuinticNormProduct.norm_plane d pb.gen hz B hB t 1
    simpa [Erdos714QuinticNormProduct.element,add_comm] using h
  have hcard : Fintype.card (E ≃ₐ[F] E) = 3 := by
    rw [← Nat.card_eq_fintype_card,IsGalois.card_aut_eq_finrank,hdim]
  let sigma : Fin 3 ≃ (E ≃ₐ[F] E) := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let r : Fin 3 → E := fun i => sigma i pb.gen
  have hr : Function.Injective r := by
    intro i j hij
    apply sigma.injective
    ext z
    exact DFunLike.congr_fun (pb.algHom_ext (f := (sigma i).toAlgHom)
      (g := (sigma j).toAlgHom) hij) z
  refine ⟨d,hd,r,hr,?_,?_,?_⟩
  · intro i
    change Algebra.trace F E (sigma i pb.gen)=0
    rw [Algebra.trace_eq_of_algEquiv,ht]
  · have hs := trace_eq_sum_automorphisms (K := F) pb.gen
    rw [ht,map_zero] at hs
    have he : (∑ i : Fin 3, r i) = ∑ s : E ≃ₐ[F] E, s pb.gen :=
      Fintype.sum_equiv sigma _ _ (fun _ => rfl)
    rw [← hs] at he
    simpa [Fin.sum_univ_succ,add_assoc] using he
  · intro i t
    have he : r i+algebraMap F E t = sigma i (pb.gen+algebraMap F E t) := by
      simp [r]
    rw [he,Algebra.norm_eq_of_algEquiv,hn]

/-- Four corners, without any quotient or repeated weighted representatives. -/
def corners (b : E) : Fin 4 → E := ![1+b,-1+b,1-b,-1-b]

lemma corners_injective (h2 : (2 : E) ≠ 0) (b : E)
    (hb0 : b ≠ 0) (hb1 : b ≠ 1) (hbm1 : b ≠ -1) :
    Function.Injective (corners b) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals exfalso; dsimp [corners] at he
  all_goals first
    | exact h2 (by linear_combination he)
    | exact h2 (by linear_combination -he)
    | exact hb0 (mul_left_cancel₀ h2 (show (2:E)*b=2*0 by linear_combination he))
    | exact hb0 (mul_left_cancel₀ h2 (show (2:E)*b=2*0 by linear_combination -he))
    | exact hb1 (mul_left_cancel₀ h2 (show (2:E)*b=2*1 by linear_combination he))
    | exact hb1 (mul_left_cancel₀ h2 (show (2:E)*b=2*1 by linear_combination -he))
    | exact hbm1 (mul_left_cancel₀ h2 (show (2:E)*b=2*(-1) by linear_combination he))
    | exact hbm1 (mul_left_cancel₀ h2 (show (2:E)*b=2*(-1) by linear_combination -he))

/-- Trace zero excludes both nonzero scalar corner collisions. -/
lemma corners_injective_of_trace [FiniteDimensional F E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : E) ≠ 0) (h3 : (3 : F) ≠ 0)
    (b : E) (hb : b ≠ 0) (ht : Algebra.trace F E b = 0) :
    Function.Injective (corners b) := by
  apply corners_injective h2 b hb
  · intro he
    have h1 : Algebra.trace F E (1:E) = (3:F) := by
      simpa [hdim] using (Algebra.trace_algebraMap (R := F) (S := E) (1:F))
    rw [he,h1] at ht
    exact h3 ht
  · intro he
    have h1 : Algebra.trace F E (1:E) = (3:F) := by
      simpa [hdim] using (Algebra.trace_algebraMap (R := F) (S := E) (1:F))
    rw [he,map_neg,h1] at ht
    exact h3 (neg_eq_zero.mp ht)

/-- The four columns all have the same norm profile; the last two rows have
its negative. This is an identity for the actual field norm. -/
theorem exists_planar_grid [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ d : F, d ≠ 0 ∧ ∃ b : E, ∃ L R : Fin 4 ↪ E,
      (∀ i, L i = corners b i) ∧
      ∀ i j, Algebra.norm F (L i+R j) = ![d,d,-d,-d] i := by
  obtain ⟨d,hd,r,hr,ht,hs,hn⟩ := exists_conjugates (F := F) (E := E) hdim
  have h2E : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff (algebraMap F E) (algebraMap F E).injective).mpr h2
  have hzero (i : Fin 3) : r i ≠ 0 := by
    intro he
    have h := hn i 0
    simp [he] at h
    exact hd h.symm
  have hv : r 1-r 2 ≠ 0 := sub_ne_zero.mpr (hr.ne (by decide))
  have hvtrace : Algebra.trace F E (r 1-r 2)=0 := by rw [map_sub,ht,ht,sub_self]
  let L : Fin 4 ↪ E := ⟨corners (r 0),corners_injective_of_trace hdim h2E h3 _ (hzero 0) (ht 0)⟩
  let R : Fin 4 ↪ E := ⟨corners (r 1-r 2),corners_injective_of_trace hdim h2E h3 _ hv hvtrace⟩
  have hscale (i : Fin 3) (s t : F) (ht : t^3-t=0) :
      Algebra.norm F (algebraMap F E s*(r i+algebraMap F E t))=s^3*d := by
    rw [map_mul,Algebra.norm_algebraMap,hdim,hn]
    rw [show t^3-t+d=d by rw [ht,zero_add]]
  have hp (i : Fin 3) (t : F) (ht : t^3-t=0) :
      Algebra.norm F (2*(r i+algebraMap F E t))=8*d := by
    have h := hscale i 2 t ht
    norm_num only [map_ofNat] at h
    exact h
  have hm (i : Fin 3) (t : F) (ht : t^3-t=0) :
      Algebra.norm F (-2*(r i+algebraMap F E t))= -8*d := by
    have h := hscale i (-2) t ht
    norm_num only [map_ofNat,map_neg] at h
    exact h
  refine ⟨-8*d,mul_ne_zero (neg_ne_zero.mpr ?_) hd,r 0,L,R,fun _ => rfl,?_⟩
  · have h8 : (8 : F)=2^3 := by norm_num
    rw [h8]
    exact pow_ne_zero 3 h2
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp [L,R,corners]
    · convert hm 2 (-1) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 2 (0) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 1 (-1) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 1 (0) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 2 (0) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 2 (1) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 1 (0) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hm 1 (1) (by ring) using 1
      congr 1
      norm_num only [map_neg,map_one,map_zero]
      linear_combination hs
    · convert hp 1 (1) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 1 (0) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 2 (1) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 2 (0) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 1 (0) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 1 (-1) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 2 (0) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring
    · convert hp 2 (-1) (by ring) using 1
      · congr 1
        norm_num only [map_neg,map_one,map_zero]
        linear_combination -hs
      · ring

/-- Four columns with opposite constant row values. -/
theorem exists_grid [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ∃ d : F, d ≠ 0 ∧ ∃ L R : Fin 4 ↪ E,
      ∀ i j, Algebra.norm F (L i+R j) = ![d,d,-d,-d] i := by
  obtain ⟨d,hd,b,L,R,_,hN⟩ := exists_planar_grid (E := E) hdim h2 h3
  exact ⟨d,hd,L,R,hN⟩

/-- The row points can lie in ANY prescribed linear hyperplane. -/
theorem exists_grid_in_kernel [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (l : E →ₗ[F] F) :
    ∃ d : F, d ≠ 0 ∧ ∃ L R : Fin 4 ↪ E,
      (∀ i, l (L i) = 0) ∧
      ∀ i j, Algebra.norm F (L i+R j) = ![d,d,-d,-d] i := by
  obtain ⟨d,hd,b,L,R,hL,hN⟩ := exists_planar_grid (E := E) hdim h2 h3
  obtain ⟨c,hc,hc1,hcb⟩ := exists_scale hdim l 1 b
  simp only [mul_one] at hc1
  let L' : Fin 4 ↪ E := ⟨fun i => c*L i,
    fun i j he => L.injective (mul_left_cancel₀ hc he)⟩
  let R' : Fin 4 ↪ E := ⟨fun i => c*R i,
    fun i j he => R.injective (mul_left_cancel₀ hc he)⟩
  refine ⟨Algebra.norm F c*d,mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hc) hd,
    L',R',?_,?_⟩
  · intro i
    change l (c*L i)=0
    rw [hL]
    fin_cases i <;> simp [corners,mul_add,mul_sub,hc1,hcb]
  · intro i j
    change Algebra.norm F (c*L i+c*R j)=_
    rw [← mul_add,map_mul,hN]
    fin_cases i <;> simp

/-- Norm surjectivity permits ANY prescribed nonzero pair of opposite values. -/
theorem exists_grid_value [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (d : F) (hd : d ≠ 0) :
    ∃ L R : Fin 4 ↪ E, ∀ i j, Algebra.norm F (L i+R j) = ![d,d,-d,-d] i := by
  obtain ⟨c,hc,L,R,hN⟩ := exists_grid (F := F) (E := E) hdim h2 h3
  obtain ⟨z,hz⟩ := FiniteField.norm_surjective F E (d/c)
  have hz0 : z ≠ 0 := Algebra.norm_ne_zero_iff.mp (by rw [hz]; exact div_ne_zero hd hc)
  let L' : Fin 4 ↪ E := ⟨fun i => z*L i,fun i j he => L.injective (mul_left_cancel₀ hz0 he)⟩
  let R' : Fin 4 ↪ E := ⟨fun j => z*R j,fun i j he => R.injective (mul_left_cancel₀ hz0 he)⟩
  refine ⟨L',R',?_⟩
  intro i j
  change Algebra.norm F (z*L i+z*R j)=_
  rw [← mul_add,map_mul,hz,hN]
  fin_cases i <;> dsimp <;> field_simp

/-- No separability or algebraic assumptions are imposed on the weight law. -/
def graph {A B : Type*} (H : A → B → F) : SimpleGraph ((E × A) ⊕ (E × B)) where
  Adj p q := match p,q with
    | .inl x,.inr y => Algebra.norm F (x.1+y.1)=H x.2 y.2
    | .inr y,.inl x => Algebra.norm F (x.1+y.1)=H x.2 y.2
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> simp_all
  loopless := by intro x; cases x <;> simp

/-- A SINGLE column of the weight law taking opposite nonzero values is enough. -/
theorem contains_copy_of_opposites [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {A B : Type*} (H : A → B → F) (ap am : A) (b : B) (d : F) (hd : d ≠ 0)
    (hplus : H ap b=d) (hminus : H am b= -d) :
    Nonempty (Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph (E := E) H)) := by
  obtain ⟨L,R,hN⟩ := exists_grid_value (E := E) hdim h2 h3 d hd
  let w : Fin 4 → A := ![ap,ap,am,am]
  let l : Fin 4 ↪ E × A := ⟨fun i => (L i,w i),fun i j he => L.injective (congrArg Prod.fst he)⟩
  let r : Fin 4 ↪ E × B := ⟨fun j => (R j,b),fun i j he => R.injective (congrArg Prod.fst he)⟩
  have he (i j : Fin 4) : (graph (E := E) H).Adj (.inl (l i)) (.inr (r j)) := by
    change Algebra.norm F (L i+R j)=H (w i) b
    rw [hN]
    fin_cases i <;> simp [w,hplus,hminus]
  refine ⟨⟨⟨l.sumMap r,?_⟩,(l.sumMap r).injective⟩⟩
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j => simp at h
    | inr j => exact he i j
  | inr j =>
    cases y with
    | inl i => exact he i j
    | inr k => simp at h

theorem not_free_of_opposites [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {A B : Type*} (H : A → B → F) (ap am : A) (b : B) (d : F) (hd : d ≠ 0)
    (hplus : H ap b=d) (hminus : H am b= -d) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) H) := by
  intro hf
  exact hf (contains_copy_of_opposites hdim h2 h3 H ap am b d hd hplus hminus)

/-- A weight law whose fixed column attains every nonzero scalar cannot work. -/
theorem not_free_of_full_column [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {A B : Type*} (H : A → B → F) (b : B)
    (hH : ∀ d : F, d ≠ 0 → ∃ a : A, H a b=d) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) H) := by
  obtain ⟨ap,hp⟩ := hH 1 one_ne_zero
  obtain ⟨am,hm⟩ := hH (-1) (neg_ne_zero.mpr one_ne_zero)
  exact not_free_of_opposites hdim h2 h3 H ap am b 1 one_ne_zero hp hm

/-- A free model can use at most half of the nonzero field values in any
single weight column. Repeated labels are allowed in this necessary bound. -/
theorem column_image_bound [Fintype F] [Fintype E]
    (hdim : Module.finrank F E = 3) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {A B : Type*} [Fintype A] (H : A → B → F) (b : B)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (E := E) H)) :
    2 * (((Finset.univ.image (fun a => H a b)).erase 0).card) ≤ Fintype.card F-1 := by
  let S := (Finset.univ.image (fun a => H a b)).erase 0
  have hnonzero {x : F} (hx : x ∈ S) : x ≠ 0 := (Finset.mem_erase.mp hx).1
  have hwitness {x : F} (hx : x ∈ S) : ∃ a : A, H a b=x := by
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hx).2
    exact ⟨a,ha⟩
  have hdisjoint : Disjoint S (S.image Neg.neg) := by
    apply Finset.disjoint_left.mpr
    intro x hx hn
    obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hn
    obtain ⟨ap,hp⟩ := hwitness hx
    obtain ⟨am,hm⟩ := hwitness hy
    have hminus : H am b= -x := by rw [← hxy,neg_neg]; exact hm
    exact not_free_of_opposites hdim h2 h3 H ap am b x (hnonzero hx) hp hminus hf
  have hsub : S ∪ S.image Neg.neg ⊆ Finset.univ.erase 0 := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    rcases Finset.mem_union.mp hx with h | h
    · exact hnonzero h
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
      exact neg_ne_zero.mpr (hnonzero hy)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injective S neg_injective] at hcard
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ (0:F)),Finset.card_univ,two_mul,S]
    using hcard

end Erdos714OddCubicNormGrid
#print axioms Erdos714OddCubicNormGrid.exists_conjugates
#print axioms Erdos714OddCubicNormGrid.exists_grid

#print axioms Erdos714OddCubicNormGrid.exists_grid_value
#print axioms Erdos714OddCubicNormGrid.contains_copy_of_opposites
#print axioms Erdos714OddCubicNormGrid.not_free_of_full_column

#print axioms Erdos714OddCubicNormGrid.column_image_bound

#print axioms Erdos714OddCubicNormGrid.exists_planar_grid
#print axioms Erdos714OddCubicNormGrid.exists_grid_in_kernel
