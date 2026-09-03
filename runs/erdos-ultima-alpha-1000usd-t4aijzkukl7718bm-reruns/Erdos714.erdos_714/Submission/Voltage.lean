import Submission.Packing

/-!
Exact biclique-lifting criteria for finite-group voltage covers.
These are tools for investigating constructions, not a solution to Erdős 714.
-/

open Finset SimpleGraph
open Classical

namespace Erdos714Voltage

variable {X Y Γ : Type*} [Group Γ]

/-- Each base incidence is replaced by a perfect matching between the sheets. -/
def neighbors (S : X → Finset Y) (v : X → Y → Γ) (p : X × Γ) : Finset (Y × Γ) :=
  (S p.1).map ⟨fun y => (y,p.2*v p.1 y), fun _ _ h => congrArg Prod.fst h⟩

@[simp] lemma mem_neighbors (S : X → Finset Y) (v : X → Y → Γ)
    (x : X) (g : Γ) (y : Y) (h : Γ) :
    (y,h) ∈ neighbors S v (x,g) ↔ y ∈ S x ∧ h = g*v x y := by
  simp [neighbors, eq_comm]

def cover (S : X → Finset Y) (v : X → Y → Γ) :
    SimpleGraph ((X × Γ) ⊕ (Y × Γ)) :=
  Erdos714Packing.incidence (neighbors S v)

/-- Trivial voltage around every rectangle, with a fixed row and column as reference. -/
def Flat {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Γ) : Prop :=
  ∀ i j, M i j = M i ⟨0,hr⟩ * (M ⟨0,hr⟩ ⟨0,hr⟩)⁻¹ * M ⟨0,hr⟩ j

lemma flat_of_factorization {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Γ)
    (a b : Fin r → Γ) (h : ∀ i j, M i j = (a i)⁻¹*b j) : Flat hr M := by
  intro i j
  simp only [h]
  group

lemma factorization_of_flat {r : ℕ} (hr : 0 < r) {M : Fin r → Fin r → Γ}
    (h : Flat hr M) :
    ∃ a b : Fin r → Γ, ∀ i j, b j = a i * M i j := by
  refine ⟨fun i => M ⟨0,hr⟩ ⟨0,hr⟩ * (M i ⟨0,hr⟩)⁻¹,
    fun j => M ⟨0,hr⟩ j, ?_⟩
  intro i j
  rw [h i j]
  group

/-- A flat complete rectangle lifts to a genuine biclique in the cover. -/
theorem not_free_of_flat (S : X → Finset Y) (v : X → Y → Γ) {r : ℕ}
    (hr : 0 < r) (f : Fin r ↪ X) (g : Fin r ↪ Y)
    (hrect : ∀ i j, g j ∈ S (f i))
    (hflat : Flat hr (fun i j => v (f i) (g j))) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) := by
  obtain ⟨a,b,hab⟩ := factorization_of_flat hr hflat
  let L : Fin r ↪ X × Γ :=
    ⟨fun i => (f i,a i), fun i j h => f.injective (congrArg Prod.fst h)⟩
  let R : Fin r ↪ Y × Γ :=
    ⟨fun i => (g i,b i), fun i j h => g.injective (congrArg Prod.fst h)⟩
  intro hfree
  have h := (Erdos714Packing.free_iff_no_rectangle (neighbors S v) hr).mp hfree L R
  apply h
  intro i j
  exact (mem_neighbors S v (f i) (a i) (g j) (b j)).mpr ⟨hrect i j, hab i j⟩

/-- In a lifted biclique, projection is injective on each side. This uses the
perfect-matching property, not an assumption on the base graph. -/
lemma projection_injective (S : X → Finset Y) (v : X → Y → Γ) {r : ℕ}
    (hr : 0 < r) (L : Fin r ↪ X × Γ) (R : Fin r ↪ Y × Γ)
    (h : ∀ i j, R j ∈ neighbors S v (L i)) :
    Function.Injective (fun i => (L i).1) ∧ Function.Injective (fun j => (R j).1) := by
  have he (i j : Fin r) : (R j).2 = (L i).2 * v (L i).1 (R j).1 :=
    (mem_neighbors S v _ _ _ _ |>.mp (h i j)).2
  constructor
  · intro i k hik
    change (L i).1 = (L k).1 at hik
    have hs : (L i).2 = (L k).2 := by
      have hi := he i ⟨0,hr⟩
      have hk := he k ⟨0,hr⟩
      rw [hik] at hi
      exact mul_right_cancel (hi.symm.trans hk)
    exact L.injective (Prod.ext hik hs)
  · intro j k hjk
    change (R j).1 = (R k).1 at hjk
    have hs : (R j).2 = (R k).2 := by
      rw [he ⟨0,hr⟩ j, he ⟨0,hr⟩ k, hjk]
    exact R.injective (Prod.ext hjk hs)

/-- Exact lifting criterion, valid for noncommutative sheet groups. -/
theorem free_iff_no_flat_rectangle (S : X → Finset Y) (v : X → Y → Γ) {r : ℕ}
    (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) ↔
      ∀ f : Fin r ↪ X, ∀ g : Fin r ↪ Y,
        (∀ i j, g j ∈ S (f i)) → ¬ Flat hr (fun i j => v (f i) (g j)) := by
  constructor
  · intro hfree f g hrect hflat
    exact not_free_of_flat S v hr f g hrect hflat hfree
  · intro hn
    apply (Erdos714Packing.free_iff_no_rectangle (neighbors S v) hr).mpr
    intro L R hrect
    obtain ⟨hL,hR⟩ := projection_injective S v hr L R hrect
    let f : Fin r ↪ X := ⟨fun i => (L i).1,hL⟩
    let g : Fin r ↪ Y := ⟨fun j => (R j).1,hR⟩
    have hmem (i j : Fin r) : (R j).1 ∈ S (L i).1 ∧
        (R j).2 = (L i).2 * v (L i).1 (R j).1 :=
      (mem_neighbors S v _ _ _ _).mp (hrect i j)
    apply hn f g (fun i j => (hmem i j).1)
    apply flat_of_factorization hr _ (fun i => (L i).2) (fun j => (R j).2)
    intro i j
    change v (L i).1 (R j).1 = (L i).2⁻¹*(R j).2
    rw [(hmem i j).2]
    group

/-- A gauge change relabels the sheets at each vertex and preserves flatness. -/
theorem flat_gauge_iff {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Γ)
    (a b : Fin r → Γ) :
    Flat hr (fun i j => (a i)⁻¹ * M i j * b j) ↔ Flat hr M := by
  constructor
  · intro h i j
    have he := h i j
    have he' := congrArg (fun z : Γ => a i * z * (b j)⁻¹) he
    simp only [mul_assoc, mul_inv_cancel_left] at he'
    convert he' using 1 <;> group
  · intro h i j
    dsimp only
    rw [h i j]
    group

/-- Separable labels are only a relabeling of independent copies of the base graph. -/
theorem separable_free_iff (S : X → Finset Y) (a : X → Γ) (b : Y → Γ)
    {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      (cover S (fun x y => (a x)⁻¹*b y)) ↔
    (completeBipartiteGraph (Fin r) (Fin r)).Free (Erdos714Packing.incidence S) := by
  rw [free_iff_no_flat_rectangle _ _ hr, Erdos714Packing.free_iff_no_rectangle _ hr]
  constructor
  · intro h f g hrect
    exact h f g hrect (flat_of_factorization hr _ (fun i => a (f i))
      (fun j => b (g j)) (fun _ _ => rfl))
  · intro h f g hrect
    exact False.elim (h f g hrect)

/-- A biclique-free base has a biclique-free cover, regardless of the labels. -/
theorem free_of_base_free (S : X → Finset Y) (v : X → Y → Γ) {r : ℕ}
    (hr : 0 < r)
    (hbase : (completeBipartiteGraph (Fin r) (Fin r)).Free (Erdos714Packing.incidence S)) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) := by
  apply (free_iff_no_flat_rectangle S v hr).mpr
  intro f g hrect
  exact False.elim ((Erdos714Packing.free_iff_no_rectangle S hr).mp hbase f g hrect)

/-- Separability only needs to hold on edges. Values assigned to nonedges do not matter. -/
theorem edgewise_separable_free_iff (S : X → Finset Y) (v : X → Y → Γ)
    (a : X → Γ) (b : Y → Γ) (hsep : ∀ x y, y ∈ S x → v x y = (a x)⁻¹*b y)
    {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) ↔
      (completeBipartiteGraph (Fin r) (Fin r)).Free (Erdos714Packing.incidence S) := by
  constructor
  · intro hfree
    apply (Erdos714Packing.free_iff_no_rectangle S hr).mpr
    intro f g hrect
    apply (free_iff_no_flat_rectangle S v hr).mp hfree f g hrect
    exact flat_of_factorization hr _ (fun i => a (f i)) (fun j => b (g j))
      (fun i j => hsep (f i) (g j) (hrect i j))
  · exact free_of_base_free S v hr

variable [Fintype X] [Fintype Γ]

/-- A finite cover multiplies the number of base incidences by its sheet count. -/
theorem edge_count [Fintype Y] (S : X → Finset Y) (v : X → Y → Γ) :
    (cover S v).edgeFinset.card = Fintype.card Γ * ∑ x, (S x).card := by
  rw [cover, Erdos714Packing.incidence_edges]
  simp only [neighbors, card_map, Fintype.sum_prod_type]
  simp [Finset.mul_sum, mul_comm]

omit [Group Γ] in
theorem vertex_count [Fintype Y] :
    Fintype.card ((X × Γ) ⊕ (Y × Γ)) =
      Fintype.card Γ * (Fintype.card X + Fintype.card Y) := by
  simp [mul_add, mul_comm]

end Erdos714Voltage

#print axioms Erdos714Voltage.free_iff_no_flat_rectangle
#print axioms Erdos714Voltage.flat_gauge_iff
#print axioms Erdos714Voltage.separable_free_iff
#print axioms Erdos714Voltage.edge_count

#print axioms Erdos714Voltage.edgewise_separable_free_iff
