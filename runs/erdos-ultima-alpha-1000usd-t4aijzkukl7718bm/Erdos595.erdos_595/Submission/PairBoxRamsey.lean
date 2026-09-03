import Submission.InfiniteFourRamsey

/-! Finite products of ordered-pair Ramsey spaces, with arbitrary palettes. -/
set_option autoImplicit false
open Set
namespace Erdos595PairBoxRamsey

universe u
structure Axis where
  Carrier : Type u
  order : LinearOrder Carrier

instance (a : Axis) : LinearOrder a.Carrier := a.order

abbrev Pair (a : Axis) := {p : a.Carrier × a.Carrier // p.1 < p.2}
abbrev SmallPair := {p : Fin 4 × Fin 4 // p.1 < p.2}
abbrev Family {I : Type*} (A : I → Axis) := ∀ i, Pair (A i)

def pairMap {a : Axis} (f : Fin 4 ↪o a.Carrier) (p : SmallPair) : Pair a :=
  ⟨(f p.val.1,f p.val.2),f.strictMono p.property⟩

def boxMap {I : Type*} {A : I → Axis} (f : ∀ i, Fin 4 ↪o (A i).Carrier)
    (p : I → SmallPair) : Family A := fun i => pairMap (f i) (p i)

theorem box (n : ℕ) (C : Type u) [Nonempty C] :
    ∃ A : Fin n → Axis.{u}, ∀ c : Family A → C,
      ∃ (f : ∀ i, Fin 4 ↪o (A i).Carrier) (z : C),
        ∀ p, c (boxMap f p) = z := by
  classical
  induction n with
  | zero =>
    let A : Fin 0 → Axis.{u} := Fin.elim0
    refine ⟨A,fun c => ⟨(fun i => Fin.elim0 i),c (fun i => Fin.elim0 i),?_⟩⟩
    intro p
    congr 1
    exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    obtain ⟨A,hA⟩ := ih
    obtain ⟨B,oB,hB⟩ := Erdos595InfiniteFourRamsey.host (Family A → C)
    letI : LinearOrder B := oB
    let aB : Axis.{u} := ⟨B,oB⟩
    let A' : Fin (n+1) → Axis.{u} := Fin.cases aB A
    refine ⟨A',?_⟩
    intro c
    let d (x y : B) : Family A → C := fun t =>
      if h : x < y then c (Fin.cases ⟨(x,y),h⟩ t) else Classical.arbitrary C
    obtain ⟨g,zg,hg,hgc⟩ := hB d
    let g' : Fin 4 ↪o B := OrderEmbedding.ofStrictMono g hg
    obtain ⟨f,z,hf⟩ := hA zg
    let f' : ∀ i, Fin 4 ↪o (A' i).Carrier := Fin.cases g' f
    refine ⟨f',z,?_⟩
    intro p
    let t : Family A := boxMap f (fun i => p i.succ)
    have he := congrFun (hgc (p 0).val.1 (p 0).val.2 (p 0).property) t
    have hp := hg (p 0).property
    simp only [d,dif_pos hp] at he
    have hh : Fin.cases ⟨(g (p 0).val.1,g (p 0).val.2),hp⟩ t = boxMap f' p := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
    rw [hh] at he
    exact he.trans (hf (fun i => p i.succ))

/-- Coordinate sets can be any finite type, not only Fin n. -/
theorem box_finite (I : Type u) [Finite I] (C : Type u) [Nonempty C] :
    ∃ A : I → Axis.{u}, ∀ c : Family A → C,
      ∃ (f : ∀ i, Fin 4 ↪o (A i).Carrier) (z : C),
        ∀ p, c (boxMap f p) = z := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  obtain ⟨A,hA⟩ := box (Fintype.card I) C
  refine ⟨fun i => A (e i),?_⟩
  intro c
  let d : Family A → C := fun t => c (fun i => t (e i))
  obtain ⟨f,z,hf⟩ := hA d
  refine ⟨fun i => f (e i),z,?_⟩
  intro p
  have h := hf (fun j => p (e.symm j))
  simpa only [d,boxMap,Equiv.symm_apply_apply] using h

#print axioms box
#print axioms box_finite
end Erdos595PairBoxRamsey
