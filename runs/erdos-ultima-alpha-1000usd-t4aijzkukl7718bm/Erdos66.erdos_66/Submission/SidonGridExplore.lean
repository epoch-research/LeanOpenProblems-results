import Submission.NaturalSidonExtractionExplore
import Submission.CarryExplore
import Submission.SidonColorBlockEnergyExplore

/-! Finite natural B₂[4] sets need arbitrarily many Sidon colors.
This blocks a proposed extraction inference; it does not settle Erdős 66. -/
namespace Erdos66SidonGrid
open Erdos66NaturalSidonExtraction Erdos66NatPairAlgebra Erdos66Carry
  Erdos66SidonColorBlockEnergy AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 2200000

noncomputable def encode (X Y : Finset ℕ) (M : ℕ) (a : X×Y) : ℕ :=
  a.1.val+M*a.2.val

noncomputable def grid (X Y : Finset ℕ) (M : ℕ) : Finset ℕ :=
  Finset.univ.image (encode X Y M)

lemma encode_injective (X Y : Finset ℕ) (M : ℕ) (hM : 0<M)
    (hX : ∀x∈X, x<M) : Function.Injective (encode X Y M) := by
  intro a b he
  have hm := congrArg (fun n : ℕ ↦ n%M) he
  have hd := congrArg (fun n : ℕ ↦ n/M) he
  simp only [encode,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hX _ a.1.property),Nat.mod_eq_of_lt (hX _ b.1.property)] at hm
  simp only [encode,Nat.add_mul_div_left _ _ hM,
    Nat.div_eq_of_lt (hX _ a.1.property),Nat.div_eq_of_lt (hX _ b.1.property),zero_add] at hd
  exact Prod.ext (Subtype.ext hm) (Subtype.ext hd)

lemma encode_mem (X Y : Finset ℕ) (M : ℕ) (a : X×Y) : encode X Y M a∈grid X Y M :=
  Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩

lemma sum_coordinates (X Y : Finset ℕ) (M : ℕ) (hM : 0<M)
    (hX : ∀x∈X, ∀y∈X, x+y<M) (a b : X×Y) (n : ℕ)
    (he : encode X Y M a+encode X Y M b=n) :
    a.1.val+b.1.val=n%M ∧ a.2.val+b.2.val=n/M := by
  have hh : (a.1.val+b.1.val)+M*(a.2.val+b.2.val)=n := by
    dsimp [encode] at he
    nlinarith
  have hx := hX _ a.1.property _ b.1.property
  have hm := congrArg (fun n : ℕ ↦ n%M) hh
  have hd := congrArg (fun n : ℕ ↦ n/M) hh
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx] at hm
  simp only [Nat.add_mul_div_left _ _ hM,Nat.div_eq_of_lt hx,zero_add] at hd
  exact ⟨hm,hd⟩

/-- The integer carry is excluded explicitly, not replaced by a product
analogy. The representation bound is for ordinary natural-number sums. -/
theorem grid_rep_le_four (X Y : Finset ℕ) (hSX : NatSidon X) (hSY : NatSidon Y)
    (M : ℕ) (hM : 0<M) (hX : ∀x∈X, x<M) (hXX : ∀x∈X, ∀y∈X, x+y<M)
    (n : ℕ) : sumRep (grid X Y M : Set ℕ) n≤4 := by
  rw [grid,sumRep_image_eq _ _ (encode_injective X Y M hM hX)]
  let PX := (X×ˢX).filter (fun ab : ℕ×ℕ ↦ ab.1+ab.2=n%M)
  let PY := (Y×ˢY).filter (fun ab : ℕ×ℕ ↦ ab.1+ab.2=n/M)
  have hb : ((Finset.univ×ˢFinset.univ).filter
      (fun ab : (X×Y)×(X×Y) ↦ encode X Y M ab.1+encode X Y M ab.2=n)).card≤
      (PX×ˢPY).card := by
    apply Finset.card_le_card_of_injOn
      (fun ab : (X×Y)×(X×Y) ↦ ((ab.1.1.val,ab.2.1.val),(ab.1.2.val,ab.2.2.val)))
    · intro ab hab
      have hh := sum_coordinates X Y M hM hXX ab.1 ab.2 n (Finset.mem_filter.mp hab).2
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ab.1.1.property,ab.2.1.property⟩,hh.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ab.1.2.property,ab.2.2.property⟩,hh.2⟩⟩
    · intro ab hab cd hcd he
      apply Prod.ext
      · apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) ↦ z.1.1) he
        · apply Subtype.ext
          exact congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) ↦ z.2.1) he
      · apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) ↦ z.1.2) he
        · apply Subtype.ext
          exact congrArg (fun z : (ℕ×ℕ)×(ℕ×ℕ) ↦ z.2.2) he
  have hx : PX.card≤2 := by
    change pairs X X (n%M)≤2
    rw [pairs_self]
    exact natSidon_rep_le_two hSX (n%M)
  have hy : PY.card≤2 := by
    change pairs Y Y (n/M)≤2
    rw [pairs_self]
    exact natSidon_rep_le_two hSY (n/M)
  rw [Finset.card_product] at hb
  exact hb.trans (by nlinarith)

/-- Two elementary pigeonhole steps force a monochromatic rectangle. -/
theorem exists_mono_rectangle {I J C : Type*} [Fintype I] [Fintype J] [Fintype C]
    (f : I → J → C) (hI : Fintype.card C<Fintype.card I)
    (hJ : Fintype.card I*Fintype.card I*Fintype.card C<Fintype.card J) :
    ∃ i i' : I, ∃ j j' : J, i≠i' ∧ j≠j' ∧
      f i j=f i' j ∧ f i j=f i j' ∧ f i j=f i' j' := by
  have hcol (j : J) : ∃ i i' : I, i≠i' ∧ f i j=f i' j :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i ↦ f i j) hI
  choose r s hrs hfs using hcol
  let label : J → I×I×C := fun j ↦ (r j,s j,f (r j) j)
  have hcard : Fintype.card (I×I×C)<Fintype.card J := by
    simpa only [Fintype.card_prod,mul_assoc] using hJ
  obtain ⟨j,j',hjj',he⟩ := Fintype.exists_ne_map_eq_of_card_lt label hcard
  have hr : r j=r j' := congrArg Prod.fst he
  have hs : s j=s j' := congrArg (fun z : I×I×C ↦ z.2.1) he
  have hf : f (r j) j=f (r j') j' := congrArg (fun z : I×I×C ↦ z.2.2) he
  refine ⟨r j,s j,j,j',hrs j,hjj',hfs j,?_,?_⟩
  · simpa only [hr] using hf
  · exact hf.trans (by simpa only [hs] using hfs j')

theorem grid_not_sidon_colored (X Y : Finset ℕ) (M : ℕ) (hM : 0<M)
    (hX : ∀x∈X, x<M) (m : ℕ) (hXm : m<X.card)
    (hYm : X.card*X.card*m<Y.card) (col : ℕ → Fin m) :
    ¬DistinctColorDifferences (grid X Y M) col := by
  intro hcol
  obtain ⟨i,i',j,j',hii',hjj',h₁,h₂,h₃⟩ := exists_mono_rectangle
    (fun (i : X) (j : Y) ↦ col (encode X Y M (i,j)))
    (by simpa only [Fintype.card_fin,Fintype.card_coe] using hXm)
    (by simpa only [Fintype.card_fin,Fintype.card_coe] using hYm)
  have hne : i.val≠i'.val := fun he ↦ hii' (Subtype.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := hcol _ (encode_mem X Y M (i,j)) _ (encode_mem X Y M (i',j))
      _ (encode_mem X Y M (i,j')) _ (encode_mem X Y M (i',j'))
      (by dsimp [encode]; omega) (by dsimp [encode]; omega)
      h₁ (h₂.symm.trans h₃) h₂ (by dsimp [encode]; omega)
    have he := encode_injective X Y M hM hX hh.1
    exact hjj' (congrArg Prod.snd he)
  · have hh := hcol _ (encode_mem X Y M (i',j)) _ (encode_mem X Y M (i,j))
      _ (encode_mem X Y M (i',j')) _ (encode_mem X Y M (i,j'))
      (by dsimp [encode]; omega) (by dsimp [encode]; omega)
      h₁.symm (h₃.symm.trans h₂) (h₁.symm.trans h₃) (by dsimp [encode]; omega)
    have he := encode_injective X Y M hM hX hh.1
    exact hjj' (congrArg Prod.snd he)

/-- No bound depending only on the maximum sum-representation count can
bound the number of Sidon colors. The cap here is always four. -/
theorem exists_cap_four_not_sidon_colored (m : ℕ) :
    ∃ S : Finset ℕ, (∀ n : ℕ, sumRep (S:Set ℕ) n≤4) ∧
      ∀ col : ℕ → Fin m, ¬DistinctColorDifferences S col := by
  let r := m+1
  let s := r*r*m+1
  let L := r^4+1
  obtain ⟨X,hXL,hXcard,hSX⟩ := exists_natSidon_subset (Finset.range L) r
    (by simp only [Finset.card_range]; dsimp [L]; omega)
  obtain ⟨Y,hYL,hYcard,hSY⟩ := exists_natSidon_subset (Finset.range (s^4+1)) s
    (by simp only [Finset.card_range]; omega)
  have hL : 0<L := by dsimp [L]; omega
  have hX (x : ℕ) (hx : x∈X) : x<L := Finset.mem_range.mp (hXL hx)
  refine ⟨grid X Y (2*L),?_,?_⟩
  · intro n
    apply grid_rep_le_four X Y hSX hSY (2*L) (by omega)
      (fun x hx ↦ by have := hX x hx; omega)
      (fun x hx y hy ↦ by have := hX x hx; have := hX y hy; omega) n
  · intro col
    apply grid_not_sidon_colored X Y (2*L) (by omega)
      (fun x hx ↦ by have := hX x hx; omega) m
    · rw [hXcard]
      dsimp [r]
      omega
    · rw [hXcard,hYcard]
      dsimp [s]
      omega

end Erdos66SidonGrid
