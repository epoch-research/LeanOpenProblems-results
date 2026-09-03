import Submission.SeededRecursiveSieve
import Submission.RecursiveSieveTransfer
import Submission.UndiscountedReferenceSource
import Submission.SieveReferenceCriterion

/-! Sound first-prime reference transfer with density-normalized cardinality
sources at every recursive child. Source bounds are established hypotheses;
uniform positivity of the resulting envelope is not asserted. -/
namespace Erdos970.RecursiveSieve
open Finset FiniteSelberg

def prefixIndices (K n : ℕ) : Finset (Fin K) := univ.filter (fun i => i.val < n)

lemma prefixIndices_card (K n : ℕ) (hn : n ≤ K) : (prefixIndices K n).card = n := by
  by_cases hlt : n < K
  · have he : prefixIndices K n = Iio (⟨n,hlt⟩ : Fin K) := by
      ext i
      simp only [prefixIndices,mem_filter,mem_univ,true_and,mem_Iio,Fin.lt_def]
    rw [he,Fin.card_Iio]
  · have he : n = K := by omega
    subst n
    have hf : prefixIndices K K = univ := filter_eq_self.mpr (fun i _ => i.isLt)
    rw [hf]
    simp

lemma avoid_extendPattern (K n : ℕ) (hn : n ≤ K) (ω : Fin K → Bool) :
    avoid n (extendPattern ω) = avoidMonomial (prefixIndices K n) ω := by
  have he : (∀ i < n, extendPattern ω i = false) ↔
      ∀ i ∈ prefixIndices K n, ω i = false := by
    constructor
    · intro hh i hi
      have hh' := hh i.val (mem_filter.mp hi).2
      simpa only [extendPattern,i.isLt,dif_pos] using hh'
    · intro hh i hi
      have hik : i < K := hi.trans_le hn
      have hh' := hh ⟨i,hik⟩ (mem_filter.mpr ⟨mem_univ _,hi⟩)
      simpa only [extendPattern,hik,dif_pos] using hh'
  simp only [avoid,avoidMonomial,he]
  split_ifs <;> rfl

lemma liftSet_disjoint_prefix (K n : ℕ) (T : Finset ℕ)
    (hT : ∀ i ∈ T, n ≤ i) : Disjoint (liftSet K T) (prefixIndices K n) := by
  apply disjoint_left.mpr
  intro i hi hj
  exact (not_lt_of_ge (hT i.val (mem_filter.mp hi).2)) (mem_filter.mp hj).2

lemma boosted_sifted (K n m : ℕ) (hn : n ≤ K) (a : Fin K → ℝ)
    (ω : ℕ → Fin K → Bool) (T : Finset ℕ) :
    sifted ((range m) ×ˢ (univ : Finset (Fin K → Bool)))
      (fun x => probability a x.2)
      (fun x => extendPattern (fun i => ω x.1 i || x.2 i)) T n =
    average a (fun η => mixedMass m (liftSet K T) (prefixIndices K n)
      (fun x i => ω x i || η i)) := by
  simp only [FiniteSelberg.mixedMass,average_sum]
  rw [sifted,sum_product]
  apply sum_congr rfl
  intro x hx
  simp only [hit_extendPattern,avoid_extendPattern K n hn,average,mixedMonomial]

/-- The gain includes the second charge for the reference core. The extra unit
inside x-1 is the exact uniform CRT progression-length error allowance. -/
noncomputable def blockSource (j g : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (((j n+1-2*n : ℕ) : ℝ)/(g n : ℝ)*(x-1)-((j n+1-2*n : ℕ) : ℝ))

/-- Arithmetic source inequalities and unit moment bounds are both transferred
to the SAME boosted weighted population. This is essential for recursive use. -/
theorem survivor_from_reference_sources (K m : ℕ) (p v : Fin K → ℕ)
    (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (hvp : ∀ i, v i ≤ p i) (r : ℕ → ℕ) (j g : ℕ → ℕ)
    (hknown : ∀ n ≤ K, IsJacobsthalBound (j n) (g n) ∧ 0 < g n)
    (hpos : 0 < (seededEnvelope
      (fun T => (m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(v i : ℝ)-1)
      (fun T => (m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(v i : ℝ)+1)
      (fun n T => blockSource j g n ((m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(v i : ℝ)))
      K ∅).1) :
    ∃ x < m, ∀ i : Fin K, ¬x ≡ r (p i) [MOD p i] := by
  let q (i : Fin K) : ℝ := 1/(p i : ℝ)
  let q' (i : Fin K) : ℝ := 1/(v i : ℝ)
  let a (i : Fin K) : ℝ := (q' i-q i)/(1-q i)
  let ω (x : ℕ) (i : Fin K) := decide (x ≡ r (p i) [MOD p i])
  have hq (i : Fin K) : q i < 1 ∧ q i ≤ q' i ∧ q' i ≤ 1 := by
    have hpR : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hvR : (1 : ℝ) < v i := by exact_mod_cast (hv i).one_lt
    refine ⟨(div_lt_one (by linarith : (0 : ℝ) < p i)).mpr hpR,
      one_div_le_one_div_of_le (by linarith) (by exact_mod_cast hvp i),
      (div_le_one (by linarith : (0 : ℝ) < v i)).mpr hvR.le⟩
  have ha (i : Fin K) : 0 ≤ a i ∧ a i ≤ 1 := by
    have hd : 0 < 1-q i := sub_pos.mpr (hq i).1
    refine ⟨div_nonneg (sub_nonneg.mpr (hq i).2.1) hd.le, ?_⟩
    exact (div_le_one hd).mpr (by linarith [(hq i).2.2])
  have hae (i : Fin K) : a i+(1-a i)*q i = q' i := by
    have hn : 1-q i ≠ 0 := (sub_pos.mpr (hq i).1).ne'
    dsimp only [a]
    field_simp
    ring
  let A := (range m) ×ˢ (univ : Finset (Fin K → Bool))
  let w (x : ℕ × (Fin K → Bool)) := probability a x.2
  let Ω (x : ℕ × (Fin K → Bool)) := extendPattern (fun i => ω x.1 i || x.2 i)
  have hw : ∀ x ∈ A, 0 ≤ w x := by
    intro x hx
    apply prod_nonneg
    intro i hi
    split_ifs
    · exact (ha i).1
    · exact sub_nonneg.mpr (ha i).2
  have hmom (T : Finset ℕ) :
      |moment A w Ω T-(m : ℝ)*∏ i ∈ liftSet K T, q' i| ≤ 1 := by
    have hh := added_hits_moment_error a q ha m ω
      (prime_hits_intersection_error p hp hpinj r m) (liftSet K T)
    simpa only [hae,A,w,Ω,boosted_moment] using hh
  have hsource (n : ℕ) (hn : n ≤ K) (T : Finset ℕ) (hT : ∀ i ∈ T, n ≤ i) :
      blockSource j g n ((m : ℝ)*∏ i ∈ liftSet K T, q' i) ≤ sifted A w Ω T n := by
    have hh := undiscounted_reference_cardinality_lower (hknown n hn).1 (hknown n hn).2
      p v hp hv hpinj hvinj hvp r m (liftSet K T) (prefixIndices K n)
      (liftSet_disjoint_prefix K n T hT)
    rw [prefixIndices_card K n hn] at hh
    change blockSource j g n ((m : ℝ)*∏ i ∈ liftSet K T, q' i) ≤
      sifted (range m ×ˢ univ) (fun x => probability a x.2)
        (fun x => extendPattern (fun i => ω x.1 i || x.2 i)) T n
    rw [boosted_sifted K n m hn]
    simpa only [blockSource,ω,a,q,q'] using hh
  obtain ⟨x,hx,hall⟩ := weighted_survivor_of_positive_seededEnvelope A w Ω hw
    (fun T => (m : ℝ)*∏ i ∈ liftSet K T, q' i-1)
    (fun T => (m : ℝ)*∏ i ∈ liftSet K T, q' i+1)
    (fun n T => blockSource j g n ((m : ℝ)*∏ i ∈ liftSet K T, q' i))
    (fun T => by linarith [(abs_le.mp (hmom T)).1])
    (fun T => by linarith [(abs_le.mp (hmom T)).2]) K hsource hpos
  refine ⟨x.1,mem_range.mp (mem_product.mp hx).1,?_⟩
  intro i
  have hh := hall i.val i.isLt
  simp only [Ω,extendPattern,i.isLt,dif_pos] at hh
  have hf := (Bool.or_eq_false_iff.mp hh).1
  exact of_decide_eq_false hf

/-- Purely numerical reference positivity with a specified family of valid
block sources. Its existence at quadratic length is still unproved. -/
noncomputable def SeededReferencePositive (K m : ℕ) (j g : ℕ → ℕ) : Prop :=
  0 < (seededEnvelope
    (fun T => (m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(Nat.nth Nat.Prime i.val : ℝ)-1)
    (fun T => (m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(Nat.nth Nat.Prime i.val : ℝ)+1)
    (fun n T => blockSource j g n
      ((m : ℝ)*∏ i ∈ liftSet K T, (1 : ℝ)/(Nat.nth Nat.Prime i.val : ℝ))) K ∅).1

/-- Reference positivity applies to arbitrary prime sets of the same size. -/
theorem survivor_of_seededReferencePositive (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (m : ℕ) (j g : ℕ → ℕ)
    (hknown : ∀ n ≤ P.card, IsJacobsthalBound (j n) (g n) ∧ 0 < g n)
    (hpos : SeededReferencePositive P.card m j g) :
    ∃ x < m, ∀ p ∈ P, ¬x ≡ r p [MOD p] := by
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  let v (i : Fin P.card) := Nat.nth Nat.Prime i.val
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  have hv : ∀ i, (v i).Prime := fun i => Nat.prime_nth_prime i.val
  have hvinj : Function.Injective v := by
    intro i l he
    exact Fin.ext ((Nat.nth_strictMono Nat.infinite_setOf_prime).injective he)
  have hvp : ∀ i, v i ≤ p i := nth_prime_le_sorted p hp hmono
  obtain ⟨x,hxm,hx⟩ := survivor_from_reference_sources P.card m p v hp hv hmono.injective
    hvinj hvp r j g hknown hpos
  refine ⟨x,hxm,?_⟩
  intro q hq
  have hqr : q ∈ Set.range p := by
    simpa only [p,Finset.range_orderEmbOfFin,Finset.mem_coe] using hq
  obtain ⟨i,rfl⟩ := hqr
  exact hx i

/-- Padding to the full budget keeps the selected source family unchanged. -/
theorem isJacobsthalBound_of_seededReferencePositive (K m : ℕ) (j g : ℕ → ℕ)
    (hknown : ∀ n ≤ K, IsJacobsthalBound (j n) (g n) ∧ 0 < g n)
    (hpos : SeededReferencePositive K m j g) : IsJacobsthalBound K m := by
  classical
  by_contra hbad
  obtain ⟨P,hP,hPK,r,hcover⟩ := (not_isJacobsthalBound_iff_cover K m).mp hbad
  obtain ⟨R,hR,hRK⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq K
  have hcard : K ≤ (P ∪ R).card := by
    rw [← hRK]
    exact card_le_card subset_union_right
  obtain ⟨Q,hPQ,hQPR,hQK⟩ := exists_subsuperset_card_eq subset_union_left hPK hcard
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    rcases mem_union.mp (hQPR hp) with hp | hp
    · exact hP p hp
    · exact hR hp
  obtain ⟨x,hxm,hx⟩ := survivor_of_seededReferencePositive Q hQ r m j g
    (hQK ▸ hknown) (hQK ▸ hpos)
  obtain ⟨p,hp,hh⟩ := hcover x hxm
  exact hx p (hPQ hp) hh

#print axioms survivor_from_reference_sources
#print axioms survivor_of_seededReferencePositive
#print axioms isJacobsthalBound_of_seededReferencePositive
end Erdos970.RecursiveSieve
