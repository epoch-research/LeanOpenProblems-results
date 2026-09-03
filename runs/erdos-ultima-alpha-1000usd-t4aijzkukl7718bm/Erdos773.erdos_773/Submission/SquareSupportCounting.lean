import Submission.SharpSquareCollisionCount
import Submission.SquareCollisionIntersections

/-!
Identification of the ordered collision count with the unordered hyperedge
count, and the resulting explicit logarithmic upper bound. These are not
independent-set or Sidon-extraction theorems.
-/
noncomputable section
namespace Erdos773.SquareSupportCounting
open Finset Filter PrimitiveSquareCollisions SharpSquareCollisionCount
open SquareCollisionCodegrees SquareCollisionIntersections
set_option maxHeartbeats 1000000

def support (q : Quad) : Finset ℕ := {q.1.1,q.1.2,q.2.1,q.2.2}

lemma support_mem {N : ℕ} {q : Quad} (hq : q ∈ ordered N) :
    support q ∈ edges (Icc 1 N) := by
  classical
  rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
  obtain ⟨hm,hab,hbc,hcd,he⟩ := mem_filter.mp hq
  simp only [mem_product] at hm
  dsimp only at hab hbc hcd he
  apply mem_filter.mpr
  refine ⟨mem_powerset.mpr ?_,?_,a,d,b,c,?_,he⟩
  · intro n hn
    simp only [support,mem_insert,mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact hm.1.1
    · exact hm.1.2
    · exact hm.2.1
    · exact hm.2.2
  · simp [support,hab.ne,(hab.trans hbc).ne,((hab.trans hbc).trans hcd).ne,
      hbc.ne,(hbc.trans hcd).ne,hcd.ne]
  · ext n
    simp only [support,mem_insert,mem_singleton]
    tauto

lemma support_injective (N : ℕ) : Set.InjOn support (ordered N : Set Quad) := by
  rintro ⟨⟨a,b⟩,⟨c,d⟩⟩ hq ⟨⟨a',b'⟩,⟨c',d'⟩⟩ hr he
  obtain ⟨_,hab,hbc,hcd,_⟩ := mem_filter.mp hq
  obtain ⟨_,hab',hbc',hcd',_⟩ := mem_filter.mp hr
  dsimp only at hab hbc hcd hab' hbc' hcd'
  change ({a,b,c,d} : Finset ℕ) = {a',b',c',d'} at he
  have ha : a=a' := by
    have h1 : a ∈ ({a',b',c',d'} : Finset ℕ) := he ▸ (by simp)
    have h2 : a' ∈ ({a,b,c,d} : Finset ℕ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at h1 h2
    omega
  subst a'
  have hb : b=b' := by
    have h1 : b ∈ ({a,b',c',d'} : Finset ℕ) := he ▸ (by simp)
    have h2 : b' ∈ ({a,b,c,d} : Finset ℕ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at h1 h2
    omega
  subst b'
  have hc : c=c' := by
    have h1 : c ∈ ({a,b,c',d'} : Finset ℕ) := he ▸ (by simp)
    have h2 : c' ∈ ({a,b,c,d} : Finset ℕ) := he.symm ▸ (by simp)
    simp only [mem_insert,mem_singleton] at h1 h2
    omega
  subst c'
  have hd : d=d' := by
    have h1 : d ∈ ({a,b,c,d'} : Finset ℕ) := he ▸ (by simp)
    simp only [mem_insert,mem_singleton] at h1
    omega
  simp [hd]

lemma ordered_representation {N : ℕ} {e : Finset ℕ} (he : e ∈ edges (Icc 1 N)) :
    ∃ q ∈ ordered N, support q = e := by
  classical
  have heA := mem_powerset.mp (mem_filter.mp he).1
  have he4 := (mem_filter.mp he).2.1
  let f := e.orderIsoOfFin he4
  let a : ℕ := (f 0).val
  let b : ℕ := (f 1).val
  let c : ℕ := (f 2).val
  let d : ℕ := (f 3).val
  have hab : a < b := f.strictMono (by decide : (0:Fin 4)<1)
  have hbc : b < c := f.strictMono (by decide : (1:Fin 4)<2)
  have hcd : c < d := f.strictMono (by decide : (2:Fin 4)<3)
  have hrep : e = {a,b,c,d} := by
    ext n
    simp only [mem_insert,mem_singleton]
    constructor
    · intro hn
      obtain ⟨i,hi⟩ := f.surjective ⟨n,hn⟩
      have hiv := congrArg Subtype.val hi
      fin_cases i
      · exact Or.inl hiv.symm
      · exact Or.inr (Or.inl hiv.symm)
      · exact Or.inr (Or.inr (Or.inl hiv.symm))
      · exact Or.inr (Or.inr (Or.inr hiv.symm))
    · intro hn
      rcases hn with rfl | rfl | rfl | rfl
      · exact (f 0).property
      · exact (f 1).property
      · exact (f 2).property
      · exact (f 3).property
  have hpart := partitions (hrep ▸ he)
  have heq : a^2+d^2=b^2+c^2 := by
    rcases hpart with hh | hh | hh
    · have hac := Nat.pow_lt_pow_left (hab.trans hbc) (by decide : (2:ℕ) ≠ 0)
      have hbd := Nat.pow_lt_pow_left (hbc.trans hcd) (by decide : (2:ℕ) ≠ 0)
      omega
    · have hab2 := Nat.pow_lt_pow_left hab (by decide : (2:ℕ) ≠ 0)
      have hcd2 := Nat.pow_lt_pow_left hcd (by decide : (2:ℕ) ≠ 0)
      omega
    · exact hh
  refine ⟨((a,b),(c,d)),mem_filter.mpr ⟨?_,hab,hbc,hcd,heq⟩,hrep.symm⟩
  simp only [mem_product]
  exact ⟨⟨heA (f 0).property,heA (f 1).property⟩,
    ⟨heA (f 2).property,heA (f 3).property⟩⟩

/-- Every nontrivial four-root support is counted exactly once. -/
theorem edges_card (N : ℕ) : (edges (Icc 1 N)).card = (ordered N).card := by
  symm
  exact card_nbij support (fun _ h => support_mem h) (support_injective N)
    (fun _ h => ordered_representation h)

/-- Explicit bound for the actual four-uniform collision hypergraph. -/
theorem edges_log_bound (N : ℕ) :
    ((edges (Icc 1 N)).card : ℝ) ≤
      (N:ℝ)^2*((41/500:ℝ)*(1+Real.log (2*N))+244) := by
  rw [edges_card]
  exact ordered_log_bound N

/-- An asymptotic leading coefficient. No independent-set assertion is made. -/
theorem edges_eventually_bound (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ((edges (Icc 1 N)).card : ℝ) ≤
      (41/500+η)*(N:ℝ)^2*Real.log N := by
  have ht : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop ((244+(41/500:ℝ)*(1+Real.log 2))/η),
    eventually_ge_atTop 1] with N hlog hN
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hc : 244+(41/500:ℝ)*(1+Real.log 2) ≤ η*Real.log N := by
    have hh := (div_le_iff₀ hη).mp hlog
    nlinarith only [hh]
  have hb := edges_log_bound N
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hN0.ne'] at hb
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (N:ℝ))
  nlinarith only [hb,hh]

/-- In particular the leading coefficient is strictly below 1/12. -/
theorem edges_eventually_small_constant :
    ∀ᶠ N : ℕ in atTop, ((edges (Icc 1 N)).card : ℝ) ≤
      (83/1000:ℝ)*(N:ℝ)^2*Real.log N := by
  have hh := edges_eventually_bound (1/1000) (by norm_num)
  norm_num at hh ⊢
  exact hh

#print axioms edges_card
#print axioms edges_log_bound
#print axioms edges_eventually_bound
#print axioms edges_eventually_small_constant
end Erdos773.SquareSupportCounting
