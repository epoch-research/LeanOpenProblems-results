import Submission.AffineCompactnessReduction

/-!
Prescribed affine edge representations do not always extend across one cone,
even over Q and even after enlarging the vector space. The base is the union
of two four-cycles meeting at one vertex. This is not an Erdős 595 witness.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595AffineConeExtension
open Erdos595Work Erdos595AffineCompactness

variable {K : Type*} [Field K]

/-- A cycle whose edge labels all have one coordinate k, and have a second
coordinate supported at just one edge, forces its initial vertex coordinate. -/
lemma cycle_level (a u v : Fin 4 → K) (k : K)
    (ha : ∀ i, a i ≠ 0) (ha1 : a 0 ≠ 1)
    (hu : ∀ i, u (i+1) = a i*u i+(1-a i)*k)
    (hv : ∀ i, v (i+1) = a i*v i+(1-a i)*(if i=0 then 1 else 0)) : u 0 = k := by
  have hu0 := hu 0
  have hu1 := hu 1
  have hu2 := hu 2
  have hu3 := hu 3
  have hv0 := hv 0
  have hv1 := hv 1
  have hv2 := hv 2
  have hv3 := hv 3
  simp +decide at hu0 hu1 hu2 hu3 hv0 hv1 hv2 hv3
  have hV : (1-a 3*a 2*a 1*a 0)*v 0 = a 3*a 2*a 1*(1-a 0) := by
    linear_combination hv3 + a 3*hv2 + (a 3*a 2)*hv1 + (a 3*a 2*a 1)*hv0
  have hp : 1-a 3*a 2*a 1*a 0 ≠ 0 := by
    intro h
    rw [h,zero_mul] at hV
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ha 3) (ha 2)) (ha 1))
      (sub_ne_zero.mpr ha1.symm) hV.symm
  have hU : (1-a 3*a 2*a 1*a 0)*(u 0-k)=0 := by
    linear_combination hu3 + a 3*hu2 + (a 3*a 2)*hu1 + (a 3*a 2*a 1)*hu0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hU).resolve_left hp)

def src : Fin 8 → Fin 7 := ![0,1,2,3,0,4,5,6]
def dst : Fin 8 → Fin 7 := ![1,2,3,0,4,5,6,0]

/-- The two cycles cannot share a spoke label when their old edge labels are
independent basis vectors. No inequality between spoke labels is assumed. -/
theorem no_vector_solution (x : Fin 7 → Fin 8 → K) (t : Fin 8 → K)
    (ht0 : ∀ i, t i ≠ 0) (ht1 : ∀ i, t i ≠ 1)
    (h : ∀ i, x (dst i) = t i • x (src i)+(1-t i) • (Pi.single i (1 : K) : Fin 8 → K)) : False := by
  classical
  let U : Fin 7 → K := fun v => x v 0+x v 1+x v 2+x v 3
  have hc (i j : Fin 8) : x (dst i) j = t i*x (src i) j+(1-t i)*(if j=i then 1 else 0) := by
    simpa [Pi.single_apply,eq_comm] using congrArg (fun f : Fin 8 → K => f j) (h i)
  have hu (i : Fin 8) : U (dst i) = t i*U (src i)+(1-t i)*(if i.val<4 then 1 else 0) := by
    have h0 := hc i 0
    have h1 := hc i 1
    have h2 := hc i 2
    have h3 := hc i 3
    fin_cases i <;> simp +decide [src,dst,U] at * <;>
      linear_combination h0+h1+h2+h3
  have first : U 0 = 1 := by
    apply cycle_level ![t 0,t 1,t 2,t 3] ![U 0,U 1,U 2,U 3]
      ![x 0 0,x 1 0,x 2 0,x 3 0] 1
    · intro i; fin_cases i <;> exact ht0 _
    · exact ht1 0
    · intro i; fin_cases i <;> first
        | simpa +decide [src,dst] using hu 0
        | simpa +decide [src,dst] using hu 1
        | simpa +decide [src,dst] using hu 2
        | simpa +decide [src,dst] using hu 3
    · intro i; fin_cases i <;> first
        | simpa +decide [src,dst] using hc 0 0
        | simpa +decide [src,dst] using hc 1 0
        | simpa +decide [src,dst] using hc 2 0
        | simpa +decide [src,dst] using hc 3 0
  have second : U 0 = 0 := by
    apply cycle_level ![t 4,t 5,t 6,t 7] ![U 0,U 4,U 5,U 6]
      ![x 0 4,x 4 4,x 5 4,x 6 4] 0
    · intro i; fin_cases i <;> exact ht0 _
    · exact ht1 4
    · intro i; fin_cases i <;> first
        | simpa +decide [src,dst] using hu 4
        | simpa +decide [src,dst] using hu 5
        | simpa +decide [src,dst] using hu 6
        | simpa +decide [src,dst] using hu 7
    · intro i; fin_cases i <;> first
        | simpa +decide [src,dst] using hc 4 4
        | simpa +decide [src,dst] using hc 5 4
        | simpa +decide [src,dst] using hc 6 4
        | simpa +decide [src,dst] using hc 7 4
  exact one_ne_zero (first.symm.trans second)

/-- The same obstruction survives every injective linear enlargement. -/
theorem no_enlarged_solution {E : Type*} [AddCommGroup E] [Module K E]
    (ι : (Fin 8 → K) →ₗ[K] E) (hι : Function.Injective ι)
    (x : Fin 7 → E) (t : Fin 8 → K)
    (ht0 : ∀ i, t i ≠ 0) (ht1 : ∀ i, t i ≠ 1)
    (h : ∀ i, x (dst i) = t i • x (src i) +
      (1-t i) • ι (Pi.single i (1 : K))) : False := by
  obtain ⟨g,hg⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hι)
  have hgi (y : Fin 8 → K) : g (ι y) = y :=
    LinearMap.congr_fun hg y
  apply no_vector_solution (fun v => g (x v)) t ht0 ht1
  intro i
  simpa only [map_add, map_smul, hgi] using congrArg g (h i)

def baseAdjacent (a b : Fin 7) : Prop :=
  (a,b) ∈ ([(0,1),(1,0),(1,2),(2,1),(2,3),(3,2),(3,0),(0,3),
    (0,4),(4,0),(4,5),(5,4),(5,6),(6,5),(6,0),(0,6)] : List (Fin 7 × Fin 7))

instance : DecidableRel baseAdjacent := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ (_ : List (Fin 7 × Fin 7))))

def base : SimpleGraph (Fin 7) where
  Adj := baseAdjacent
  symm := by change ∀ a b, baseAdjacent a b → baseAdjacent b a; decide +kernel
  loopless := by change ∀ a, ¬baseAdjacent a a; decide +kernel

lemma base_triangleFree : base.CliqueFree 3 := by
  have hn : ∀ a b c : Fin 7,
      ¬(baseAdjacent a b ∧ baseAdjacent a c ∧ baseAdjacent b c) := by decide +kernel
  classical
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  exact hn (f 0) (f 1) (f 2) ⟨f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide)⟩

/-- The prescribed independent labeling of the old edges. -/
noncomputable def baseLabels : Sym2 (Fin 7) → (Fin 8 → K) :=
  fun e i => if e = s(src i,dst i) then 1 else 0

lemma baseLabels_edge (i : Fin 8) :
    baseLabels (K := K) s(src i,dst i) = Pi.single i (1 : K) := by
  have he : ∀ i j : Fin 8, s(src i,dst i) = s(src j,dst j) ↔ i=j := by decide +kernel
  classical
  funext j
  simp only [baseLabels,he,Pi.single_apply,eq_comm]

lemma baseLabels_represents : Represents (K := K) base (baseLabels (K := K)) := by
  intro a b c hab hac hbc
  exact (base_triangleFree _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)).elim

def coneAdjacent (a b : Option (Fin 7)) : Prop :=
  match a,b with
  | none,none => False
  | none,some _ => True
  | some _,none => True
  | some x,some y => baseAdjacent x y

instance : DecidableRel coneAdjacent := fun a b => by
  cases a <;> cases b <;> unfold coneAdjacent <;> infer_instance

def cone : SimpleGraph (Option (Fin 7)) where
  Adj := coneAdjacent
  symm := by
    intro a b h
    cases a <;> cases b <;> first | exact h | exact base.symm h
  loopless := by intro a; cases a <;> simp only [coneAdjacent, not_false_eq_true]; exact base.loopless _

lemma cone_cliqueFree : cone.CliqueFree 4 := by
  have hn : ∀ a b c d : Option (Fin 7),
      ¬(coneAdjacent a b ∧ coneAdjacent a c ∧ coneAdjacent a d ∧
        coneAdjacent b c ∧ coneAdjacent b d ∧ coneAdjacent c d) := by decide +kernel
  classical
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  exact hn (f 0) (f 1) (f 2) (f 3) ⟨f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide), f.map_rel_iff.mpr (by decide),
    f.map_rel_iff.mpr (by decide)⟩

/-- No affine representation of the cone preserves the independent labels of
its eight base edges, even in a larger vector space. -/
theorem no_cone_extension {E : Type*} [AddCommGroup E] [Module K E]
    (ι : (Fin 8 → K) →ₗ[K] E) (hι : Function.Injective ι)
    (f : Sym2 (Option (Fin 7)) → E)
    (hf : Represents (K := K) cone f)
    (hbase : ∀ i : Fin 8, f s(some (src i), some (dst i)) =
      ι (Pi.single i (1 : K))) : False := by
  have he (i : Fin 8) : cone.Adj (some (src i)) (some (dst i)) := by
    change baseAdjacent (src i) (dst i)
    fin_cases i <;> decide +kernel
  have ht (i : Fin 8) := hf none (some (src i)) (some (dst i))
    (by trivial) (by trivial) (he i)
  choose t ht0 ht1 hrel hne using ht
  apply no_enlarged_solution ι hι (fun v => f s(none,some v)) t ht0 ht1
  intro i
  simpa only [hbase] using hrel i

#print axioms no_enlarged_solution
#print axioms baseLabels_edge
#print axioms baseLabels_represents
#print axioms base_triangleFree
#print axioms cone_cliqueFree
#print axioms no_cone_extension
#print axioms no_vector_solution
end Erdos595AffineConeExtension
