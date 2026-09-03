import Submission.Voltage

/-!
Exact biclique criteria for arbitrary permutation-labelled matching covers,
and a transfer to regular symmetric-group covers. This is a reduction of a
construction problem, not an existence theorem or a solution of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714PermutationVoltage
variable {X Y Ω : Type*}

/-- An arbitrary perfect matching above every base edge. -/
def neighbors (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω) (p : X × Ω) :
    Finset (Y × Ω) :=
  (S p.1).map ⟨fun y => (y,v p.1 y p.2),fun _ _ h => congrArg Prod.fst h⟩

@[simp] lemma mem_neighbors (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    (x : X) (s : Ω) (y : Y) (t : Ω) :
    (y,t) ∈ neighbors S v (x,s) ↔ y ∈ S x ∧ t=v x y s := by
  simp [neighbors,eq_comm]

def cover (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω) :
    SimpleGraph ((X × Ω) ⊕ (Y × Ω)) := Erdos714Packing.incidence (neighbors S v)

/-- The sheet assignments for a complete indexed rectangle. -/
def Lifts {r : ℕ} (M : Fin r → Fin r → Equiv.Perm Ω) :=
  {p : (Fin r → Ω) × (Fin r → Ω) // ∀ i j, p.2 j=M i j (p.1 i)}

/-- Cycle permutations relative to row zero and column zero. -/
def holonomy {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Equiv.Perm Ω)
    (i j : Fin r) : Equiv.Perm Ω :=
  (M ⟨0,hr⟩ j)⁻¹ * M i j * (M i ⟨0,hr⟩)⁻¹ * M ⟨0,hr⟩ ⟨0,hr⟩

def FixedSheets {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Equiv.Perm Ω) :=
  {s : Ω // ∀ i j, holonomy hr M i j s=s}

lemma fixed_iff {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Equiv.Perm Ω)
    (s : Ω) :
    (∀ i j, holonomy hr M i j s=s) ↔
      ∀ i j, M i j ((M i ⟨0,hr⟩)⁻¹ (M ⟨0,hr⟩ ⟨0,hr⟩ s))=M ⟨0,hr⟩ j s := by
  constructor
  · intro h i j
    have he := congrArg (M ⟨0,hr⟩ j) (h i j)
    simpa [holonomy,Equiv.Perm.mul_apply] using he
  · intro h i j
    simp only [holonomy,Equiv.Perm.mul_apply]
    rw [h i j]
    simp

/-- A lift is determined by its sheet above the distinguished row. -/
def liftsEquivFixed {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Equiv.Perm Ω) :
    Lifts M ≃ FixedSheets hr M where
  toFun p := ⟨p.val.1 ⟨0,hr⟩, by
    apply (fixed_iff hr M _).mpr
    intro i j
    rw [← p.property ⟨0,hr⟩ ⟨0,hr⟩,p.property i ⟨0,hr⟩]
    simp only [Equiv.Perm.inv_def,Equiv.symm_apply_apply]
    exact (p.property i j).symm.trans (p.property ⟨0,hr⟩ j)⟩
  invFun s := ⟨(fun i => (M i ⟨0,hr⟩)⁻¹ (M ⟨0,hr⟩ ⟨0,hr⟩ s.val),
    fun j => M ⟨0,hr⟩ j s.val), by
      intro i j
      exact ((fixed_iff hr M s.val).mp s.property i j).symm⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change (M i ⟨0,hr⟩)⁻¹ (M ⟨0,hr⟩ ⟨0,hr⟩ (p.val.1 ⟨0,hr⟩))=p.val.1 i
      rw [← p.property ⟨0,hr⟩ ⟨0,hr⟩,p.property i ⟨0,hr⟩]
      simp
    · funext j
      exact (p.property ⟨0,hr⟩ j).symm
  right_inv s := by
    apply Subtype.ext
    change (M ⟨0,hr⟩ ⟨0,hr⟩)⁻¹ (M ⟨0,hr⟩ ⟨0,hr⟩ s.val)=s.val
    simp

/-- In a lifted biclique, the base coordinates on each side are distinct. -/
lemma projection_injective (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r) (L : Fin r ↪ X × Ω) (R : Fin r ↪ Y × Ω)
    (h : ∀ i j, R j ∈ neighbors S v (L i)) :
    Function.Injective (fun i => (L i).1) ∧ Function.Injective (fun j => (R j).1) := by
  have he (i j : Fin r) : (R j).2=v (L i).1 (R j).1 (L i).2 :=
    (mem_neighbors S v _ _ _ _ |>.mp (h i j)).2
  constructor
  · intro i k hik
    change (L i).1=(L k).1 at hik
    have hsheet : (L i).2=(L k).2 := by
      have hh := (he i ⟨0,hr⟩).symm.trans (he k ⟨0,hr⟩)
      rw [hik] at hh
      exact (v (L k).1 (R ⟨0,hr⟩).1).injective hh
    exact L.injective (Prod.ext hik hsheet)
  · intro j k hjk
    change (R j).1=(R k).1 at hjk
    have hsheet : (R j).2=(R k).2 := by
      rw [he ⟨0,hr⟩ j,he ⟨0,hr⟩ k,hjk]
    exact R.injective (Prod.ext hjk hsheet)

lemma not_free_of_lift (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r) (f : Fin r ↪ X) (g : Fin r ↪ Y)
    (hrect : ∀ i j, g j ∈ S (f i)) (p : Lifts (fun i j => v (f i) (g j))) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) := by
  let L : Fin r ↪ X × Ω := ⟨fun i => (f i,p.val.1 i),by
    intro i j h; exact f.injective (congrArg Prod.fst h)⟩
  let R : Fin r ↪ Y × Ω := ⟨fun j => (g j,p.val.2 j),by
    intro i j h; exact g.injective (congrArg Prod.fst h)⟩
  intro hf
  apply (Erdos714Packing.free_iff_no_rectangle _ hr).mp hf L R
  intro i j
  exact (mem_neighbors S v _ _ _ _).mpr ⟨hrect i j,p.property i j⟩

/-- For a nonregular cover it is common fixed sheets, NOT identity
holonomies, that exactly characterize forbidden lifts. -/
theorem free_iff_no_fixed_sheet (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) ↔
      ∀ f : Fin r ↪ X, ∀ g : Fin r ↪ Y, (∀ i j, g j ∈ S (f i)) →
        IsEmpty (FixedSheets hr (fun i j => v (f i) (g j))) := by
  constructor
  · intro hf f g hrect
    exact ⟨fun s => not_free_of_lift S v hr f g hrect ((liftsEquivFixed hr _).symm s) hf⟩
  · intro hn
    apply (Erdos714Packing.free_iff_no_rectangle _ hr).mpr
    intro L R hrect
    obtain ⟨hL,hR⟩ := projection_injective S v hr L R hrect
    let f : Fin r ↪ X := ⟨fun i => (L i).1,hL⟩
    let g : Fin r ↪ Y := ⟨fun j => (R j).1,hR⟩
    have hm (i j : Fin r) := (mem_neighbors S v _ _ _ _).mp (hrect i j)
    let p : Lifts (fun i j => v (f i) (g j)) :=
      ⟨(fun i => (L i).2,fun j => (R j).2),fun i j => (hm i j).2⟩
    exact (hn f g (fun i j => (hm i j).1)).false ((liftsEquivFixed hr _) p)

/-- Flat inverse labels give a lift through every sheet in the permutation
cover. The regular cover uses RIGHT multiplication, hence the inverse. -/
lemma lift_of_inverse_flat {r : ℕ} (hr : 0 < r)
    (M : Fin r → Fin r → Equiv.Perm Ω) (s : Ω)
    (hflat : Erdos714Voltage.Flat hr (fun i j => (M i j)⁻¹)) : Nonempty (Lifts M) := by
  obtain ⟨a,b,hab⟩ := Erdos714Voltage.factorization_of_flat hr hflat
  refine ⟨⟨(fun i => (a i)⁻¹ s,fun j => (b j)⁻¹ s),?_⟩⟩
  intro i j
  change (b j)⁻¹ s=M i j ((a i)⁻¹ s)
  rw [hab i j,mul_inv_rev,inv_inv]
  rfl

/-- Any free matching cover yields a free regular symmetric-group cover.
For m sheets the new sheet group has m! elements, a constant if m is fixed. -/
theorem regularization [Nonempty Ω] (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v)) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714Voltage.cover S (fun x y => (v x y)⁻¹)) := by
  apply (Erdos714Voltage.free_iff_no_flat_rectangle _ _ hr).mpr
  intro f g hrect hflat
  obtain ⟨p⟩ := lift_of_inverse_flat hr _ (Classical.choice ‹Nonempty Ω›) hflat
  exact not_free_of_lift S v hr f g hrect p hf

/-- The abstract perfect-matching axioms produce permutation labels. Thus
there is no additional algebraic assumption in the permutation presentation. -/
theorem matching_representation [Finite Ω] (S : X → Finset Y)
    (R : X × Ω → Finset (Y × Ω))
    (hbase : ∀ x s y t, (y,t) ∈ R (x,s) → y ∈ S x)
    (hex : ∀ x y, y ∈ S x → ∀ s, ∃! t, (y,t) ∈ R (x,s))
    (hinj : ∀ x y s s' t, (y,t) ∈ R (x,s) → (y,t) ∈ R (x,s') → s=s') :
    ∃ v : X → Y → Equiv.Perm Ω, R=neighbors S v := by
  let f (x : X) (y : Y) (s : Ω) : Ω :=
    if h : y ∈ S x then Classical.choose (hex x y h s) else s
  have hfmem (x : X) (y : Y) (hy : y ∈ S x) (s : Ω) :
      (y,f x y s) ∈ R (x,s) := by
    dsimp [f]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hex x y hy s)).1
  have hfuniq (x : X) (y : Y) (hy : y ∈ S x) (s t : Ω)
      (ht : (y,t) ∈ R (x,s)) : t=f x y s := by
    dsimp [f]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hex x y hy s)).2 t ht
  have hfi (x : X) (y : Y) : Function.Injective (f x y) := by
    by_cases hy : y ∈ S x
    · intro s t he
      have ht := hfmem x y hy t
      rw [← he] at ht
      exact hinj x y s t (f x y s) (hfmem x y hy s) ht
    · simpa [f,hy] using (Function.injective_id : Function.Injective (id : Ω → Ω))
  let v (x : X) (y : Y) : Equiv.Perm Ω :=
    Equiv.ofBijective (f x y) ⟨hfi x y,Finite.surjective_of_injective (hfi x y)⟩
  refine ⟨v,?_⟩
  funext p
  ext q
  rcases p with ⟨x,s⟩
  rcases q with ⟨y,t⟩
  rw [mem_neighbors]
  constructor
  · intro h
    have hy := hbase x s y t h
    exact ⟨hy,hfuniq x y hy s t h⟩
  · rintro ⟨hy,ht⟩
    change t=f x y s at ht
    rw [ht]
    exact hfmem x y hy s

/-- Regular group voltages are a special case of permutation voltages. -/
lemma regular_as_permutation {Γ : Type*} [Group Γ]
    (S : X → Finset Y) (v : X → Y → Γ) :
    cover S (fun x y => Equiv.mulRight (v x y))=Erdos714Voltage.cover S v := by
  rfl

/-- Cardinality of the actual sheet assignments, including zero lifts. -/
theorem lifts_card {r : ℕ} (hr : 0 < r) (M : Fin r → Fin r → Equiv.Perm Ω) :
    Nat.card (Lifts M)=Nat.card (FixedSheets hr M) :=
  Nat.card_congr (liftsEquivFixed hr M)

/-- Common fixed sheets need not mean flatness. This prevents using the
regular-cover criterion as a false converse for arbitrary permutation covers. -/
theorem nonflat_lift (σ : Equiv.Perm Ω) (hσ : σ ≠ 1) (s : Ω) (hs : σ s=s) :
    ∃ M : Fin 4 → Fin 4 → Equiv.Perm Ω,
      Nonempty (Lifts M) ∧ ¬ Erdos714Voltage.Flat (by decide : 0<4) (fun i j => (M i j)⁻¹) := by
  let M (i j : Fin 4) : Equiv.Perm Ω := if i=1 ∧ j=1 then σ else 1
  refine ⟨M,⟨⟨(fun _ => s,fun _ => s),?_⟩⟩,?_⟩
  · intro i j
    change s=M i j s
    dsimp [M]
    split_ifs <;> simp [hs]
  · intro hflat
    have h := hflat 1 1
    have he : σ⁻¹=1 := by simpa [M] using h
    exact hσ (inv_eq_one.mp he)

/-- Fix both endpoint sheets. For a fixed left sheet, these sets partition
all base edges as the right sheet varies. -/
def phase (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω) (s t : Ω)
    (x : X) : Finset Y := (S x).filter (fun y => v x y s=t)

@[simp] lemma mem_phase (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    (s t : Ω) (x : X) (y : Y) :
    y ∈ phase S v s t x ↔ y ∈ S x ∧ v x y s=t := by
  simp [phase]

theorem phase_free (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v)) (s t : Ω) :
    (completeBipartiteGraph (Fin r) (Fin r)).Free
      (Erdos714Packing.incidence (phase S v s t)) := by
  apply (Erdos714Packing.free_iff_no_rectangle _ hr).mpr
  intro f g hrect
  have h (i j) := (mem_phase S v s t _ _).mp (hrect i j)
  exact not_free_of_lift S v hr f g (fun i j => (h i j).1)
    ⟨(fun _ => s,fun _ => t),fun i j => (h i j).2.symm⟩ hf

/-- This Ramsey assumption is explicit. No such assertion about norm graphs
is inferred from a bounded common-neighbor count. -/
theorem not_free_of_edge_ramsey (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r) (s : Ω)
    (hRamsey : ∀ c : X → Y → Ω, ∃ f : Fin r ↪ X, ∃ g : Fin r ↪ Y, ∃ t : Ω,
      (∀ i j, g j ∈ S (f i)) ∧ ∀ i j, c (f i) (g j)=t) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v) := by
  obtain ⟨f,g,t,hrect,he⟩ := hRamsey (fun x y => v x y s)
  exact not_free_of_lift S v hr f g hrect
    ⟨(fun _ => s,fun _ => t),fun i j => (he i j).symm⟩

variable [Fintype X] [Fintype Y] [Fintype Ω]

omit [Fintype Y] in
theorem phase_edge_partition (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω) (s : Ω) :
    ∑ t, ∑ x, (phase S v s t x).card = ∑ x, (S x).card := by
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [phase,card_filter]
  rw [sum_comm]
  simp

omit [Fintype Y] in
/-- A free m-sheet cover supplies a free subgraph of the base retaining at
least1/m of its edges. This is necessary, not a converse cover construction. -/
theorem extract_dense_phase (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω)
    {r : ℕ} (hr : 0 < r) (s : Ω)
    (hf : (completeBipartiteGraph (Fin r) (Fin r)).Free (cover S v)) :
    ∃ T : X → Finset Y, (∀ x, T x ⊆ S x) ∧
      (completeBipartiteGraph (Fin r) (Fin r)).Free (Erdos714Packing.incidence T) ∧
      (∑ x, (S x).card) ≤ Fintype.card Ω*∑ x, (T x).card := by
  letI : Nonempty Ω := ⟨s⟩
  obtain ⟨t,_,hmax⟩ := Finset.exists_max_image (univ : Finset Ω)
    (fun t => ∑ x, (phase S v s t x).card) univ_nonempty
  refine ⟨phase S v s t,fun x => filter_subset _ _,phase_free S v hr hf s t,?_⟩
  calc
    ∑ x, (S x).card = ∑ u, ∑ x, (phase S v s u x).card :=
      (phase_edge_partition S v s).symm
    _ ≤ ∑ _u : Ω, ∑ x, (phase S v s t x).card :=
      sum_le_sum (fun u _ => hmax u (mem_univ u))
    _ = _ := by simp

/-- Matching covers preserve each base degree and multiply the total edge
count by the number of sheets. -/
theorem edge_count (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω) :
    (cover S v).edgeFinset.card=Fintype.card Ω*∑ x, (S x).card := by
  rw [cover,Erdos714Packing.incidence_edges]
  simp only [neighbors,card_map,Fintype.sum_prod_type]
  simp [Finset.mul_sum,mul_comm]

theorem vertex_count : Fintype.card ((X × Ω) ⊕ (Y × Ω)) =
    Fintype.card Ω*(Fintype.card X+Fintype.card Y) := by
  simp [mul_add,mul_comm]

theorem regularized_edges (S : X → Finset Y) (v : X → Y → Equiv.Perm Ω) :
    (Erdos714Voltage.cover S (fun x y => (v x y)⁻¹)).edgeFinset.card =
      (Fintype.card Ω).factorial * ∑ x, (S x).card := by
  rw [Erdos714Voltage.edge_count,Fintype.card_perm]

theorem regularized_vertices :
    Fintype.card ((X × Equiv.Perm Ω) ⊕ (Y × Equiv.Perm Ω)) =
      (Fintype.card Ω).factorial*(Fintype.card X+Fintype.card Y) := by
  rw [Erdos714Voltage.vertex_count,Fintype.card_perm]

#print axioms liftsEquivFixed
#print axioms projection_injective
#print axioms free_iff_no_fixed_sheet
#print axioms regularization
#print axioms matching_representation
#print axioms regular_as_permutation
#print axioms lifts_card
#print axioms nonflat_lift
#print axioms phase_free
#print axioms not_free_of_edge_ramsey
#print axioms phase_edge_partition
#print axioms extract_dense_phase
#print axioms edge_count
#print axioms regularized_edges
#print axioms regularized_vertices
end Erdos714PermutationVoltage
