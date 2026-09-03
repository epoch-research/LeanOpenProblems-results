import FormalConjecturesUtil

/-! Finite-image energy estimates and reciprocal-mass transfer.
These are auxiliary counting statements. -/
namespace Erdos1206.FiniteImageEnergy
open Finset Filter
open scoped Classical Topology

def equalPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) : Finset (α × α) :=
  (S ×ˢ S).filter (fun p => f p.1=f p.2)

lemma fiber_card_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∑ y∈S.image f, (S.filter (fun x => f x=y)).card=S.card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  exact filter_true_of_mem (fun x hx => mem_image_of_mem f hx)

lemma fiber_sq_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∑ y∈S.image f, (S.filter (fun x => f x=y)).card^2=(equalPairs S f).card := by
  have hmap : ∀ p∈equalPairs S f, f p.1∈S.image f := by
    intro p hp
    exact mem_image_of_mem f (mem_product.mp (mem_filter.mp hp).1).1
  have hh := sum_card_fiberwise_eq_card_filter (equalPairs S f) (S.image f) (fun p => f p.1)
  have he : (equalPairs S f).filter (fun p => f p.1∈S.image f)=equalPairs S f :=
    filter_true_of_mem hmap
  rw [he] at hh
  rw [← hh]
  apply sum_congr rfl
  intro y hy
  have hf : (equalPairs S f).filter (fun p => f p.1=y)=
      (S.filter (fun x => f x=y)) ×ˢ (S.filter (fun x => f x=y)) := by
    ext p
    simp only [equalPairs,mem_filter,mem_product]
    grind
  rw [hf,card_product,pow_two]


lemma fiber_sq_sum_of_mapsTo {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → β) (hmap : ∀ x∈S, f x∈T) :
    ∑ y∈T, (S.filter (fun x => f x=y)).card^2=(equalPairs S f).card := by
  rw [← fiber_sq_sum S f]
  symm
  apply sum_subset (image_subset_iff.mpr hmap)
  intro y hy hy'
  have hz : S.filter (fun x => f x=y)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hy' (mem_image.mpr ⟨x,(mem_filter.mp hx).1,(mem_filter.mp hx).2⟩)
  simp [hz]

/-- Switching between finitely many maps incurs at most the square of the
number of maps in equal-value energy. No regularity of the selector is assumed. -/
theorem selector_energy {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (S : Finset α) (f : ι → α → β) (sel : α → ι) :
    (equalPairs S (fun x => f (sel x) x)).card ≤
      Fintype.card ι * ∑i : ι, (equalPairs S (f i)).card := by
  let T := Finset.univ.biUnion (fun i : ι => S.image (f i))
  have hm (i : ι) : ∀ x∈S, f i x∈T := by
    intro x hx
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image_of_mem _ hx⟩
  have hs : ∀ x∈S, f (sel x) x∈T := fun x hx => hm (sel x) x hx
  rw [← fiber_sq_sum_of_mapsTo S T (fun x => f (sel x) x) hs]
  have hper (y : β) : (S.filter (fun x => f (sel x) x=y)).card^2 ≤
      Fintype.card ι * ∑i : ι, (S.filter (fun x => f i x=y)).card^2 := by
    have hsub : S.filter (fun x => f (sel x) x=y) ⊆
        Finset.univ.biUnion (fun i : ι => S.filter (fun x => f i x=y)) := by
      intro x hx
      exact mem_biUnion.mpr ⟨sel x,mem_univ _,mem_filter.mpr (mem_filter.mp hx)⟩
    have hc := (card_le_card hsub).trans card_biUnion_le
    have hsq := Nat.pow_le_pow_left hc 2
    have hcs := sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun i => (S.filter (fun x => f i x=y)).card) (fun _ => (1:ℕ))
    simp only [mul_one,one_pow,sum_const,card_univ,smul_eq_mul,mul_one] at hcs
    exact hsq.trans (by simpa [mul_comm] using hcs)
  calc
    _ ≤ ∑y∈T, Fintype.card ι * ∑i : ι, (S.filter (fun x => f i x=y)).card^2 :=
      sum_le_sum (fun y _ => hper y)
    _ = Fintype.card ι * ∑i : ι, ∑y∈T, (S.filter (fun x => f i x=y)).card^2 := by
      rw [← mul_sum,sum_comm]
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro i hi
      exact fiber_sq_sum_of_mapsTo S T (f i) (hm i)

/-- Cauchy--Schwarz, with the multiplicities retained explicitly. -/
theorem image_card_energy {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) :
    (S.card:ℝ)^2 ≤ ((S.image f).card:ℝ)*(equalPairs S f).card := by
  have hc := sum_mul_sq_le_sq_mul_sq (S.image f)
    (fun y => ((S.filter (fun x => f x=y)).card:ℝ)) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  have h1 : (∑ y∈S.image f, ((S.filter (fun x => f x=y)).card:ℝ))=S.card := by
    exact_mod_cast fiber_card_sum S f
  have h2 : (∑ y∈S.image f, ((S.filter (fun x => f x=y)).card:ℝ)^2)=(equalPairs S f).card := by
    exact_mod_cast fiber_sq_sum S f
  rw [h1,h2] at hc
  simpa only [mul_comm] using hc

/-- Image cardinality is bounded by a height cutoff times reciprocal mass. -/
lemma image_card_le_height_mul_mass {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) {H : ℝ} (hH : 0 < H)
    (hf : ∀ x∈S, 0<f x ∧ (f x:ℝ)≤H) :
    ((S.image f).card:ℝ) ≤ H*∑n∈S.image f, (1:ℝ)/n := by
  calc
    ((S.image f).card:ℝ) = ∑_n∈S.image f, (1:ℝ) := by simp
    _ ≤ ∑n∈S.image f, H*((1:ℝ)/n) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
      have hp : (0:ℝ)<f x := by exact_mod_cast (hf x hx).1
      have hh : (1:ℝ) ≤ H/f x := (le_div_iff₀ hp).mpr (by simpa using (hf x hx).2)
      simpa only [one_mul,mul_one_div] using hh
    _ = _ := (mul_sum ..).symm

lemma equalPairs_mono {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S T : Finset α} (hST : S⊆T) (f : α → β) : equalPairs S f⊆equalPairs T f := by
  intro p hp
  obtain ⟨hpm,he⟩ := mem_filter.mp hp
  obtain ⟨hx,hy⟩ := mem_product.mp hpm
  exact mem_filter.mpr ⟨mem_product.mpr ⟨hST hx,hST hy⟩,he⟩

/-- Summability on a root set forces summability of the masses of disjoint
finite subsets. No collision multiplicity is counted in this lemma. -/
lemma disjoint_masses_summable {A : Set ℕ}
    (hs : Summable (fun n : ℕ => if n∈A then (1:ℝ)/n else 0))
    (S : ℕ → Finset ℕ) (hS : ∀ j, (S j:Set ℕ)⊆A)
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    Summable (fun j => ∑n∈S j, (1:ℝ)/n) := by
  let w (n : ℕ) : ℝ := if n∈A then 1/n else 0
  have hw : ∀ n, 0 ≤ w n := by intro n; dsimp [w]; split_ifs <;> positivity
  have hh : Summable w := hs
  apply summable_of_sum_range_le (c := ∑'n, w n)
  · intro j
    exact sum_nonneg (fun _ _ => by positivity)
  · intro L
    have he (j : ℕ) : (∑n∈S j, (1:ℝ)/n)=∑n∈S j, w n := by
      apply sum_congr rfl
      intro n hn
      simp [w,hS j hn]
    simp_rw [he]
    rw [← sum_biUnion (fun i _ j _ hij => hdis hij)]
    exact hh.sum_le_tsum _ (fun n _ => hw n)

#print axioms selector_energy
#print axioms image_card_energy
#print axioms disjoint_masses_summable
end Erdos1206.FiniteImageEnergy
