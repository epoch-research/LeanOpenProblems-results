import Submission.QuaternionNormPlane

/-! Quaternion-type cubic norm graphs fail in every binary cubic model.
This is a construction obstruction, not a disproof of Erdős 714. -/
noncomputable section
open SimpleGraph Classical
open scoped CharTwo
set_option maxHeartbeats 5000000
namespace Erdos714QuaternionCubicNorm

section Orbit
variable {G F : Type*} [Group G] [Field F]

def weightedGraph (f : G → F) : SimpleGraph ((G × Fˣ) ⊕ (G × Fˣ)) where
  Adj a b := match a,b with
    | .inl a,.inr b => f (a.1⁻¹*b.1)=(a.2:F)*(b.2:F)
    | .inr b,.inl a => f (a.1⁻¹*b.1)=(a.2:F)*(b.2:F)
    | _,_ => False
  symm := by intro a b h; cases a <;> cases b <;> exact h
  loopless := by intro a; cases a <;> simp

lemma order_four (g : G) (h4 : g^4=1) (h2 : g^2 ≠ 1) : orderOf g=4 := by
  have h1 : g ≠ 1 := by intro h; exact h2 (by simp [h])
  have h3 : g^3 ≠ 1 := by
    intro h
    have he : g^4=g := by rw [show (4:ℕ)=3+1 by rfl,pow_succ,h,one_mul]
    exact h1 (he.symm.trans h4)
  apply (orderOf_eq_iff (by decide : 0<4)).mpr
  refine ⟨h4,?_⟩
  intro m hm hm0
  have : m=1 ∨ m=2 ∨ m=3 := by omega
  rcases this with rfl | rfl | rfl <;> simpa using (by assumption)

/-- A constant-weight orbit of a cyclic group of order four supplies all
sixteen original relative-product edges. -/
def cyclicCopy (f : G → F) (g h : G) (d : F) (hd : d ≠ 0)
    (h4 : g^4=1) (h2 : g^2 ≠ 1) (hn : ∀ i : Fin 4, f (g^(i:ℕ)*h)=d) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (weightedGraph f) := by
  have ho := order_four g h4 h2
  have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
  have hinj : Function.Injective (fun i : Fin 4 => g^(i:ℕ)) := by
    intro i j hij
    have he := (pow_inj_mod (x := g)).mp hij
    rw [ho,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] at he
    exact Fin.ext he
  have hclosed (i j : Fin 4) : ∃ k : Fin 4, (g^(i:ℕ))⁻¹*g^(j:ℕ)=g^(k:ℕ) := by
    have hm : (g^(i:ℕ))⁻¹*g^(j:ℕ) ∈ Subgroup.zpowers g :=
      (Subgroup.zpowers g).mul_mem
        ((Subgroup.zpowers g).inv_mem ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) _))
        ((Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) _)
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hm)
    have hk' : k<4 := by simpa [ho] using hk
    exact ⟨⟨k,hk'⟩,he.symm⟩
  let L : Fin 4 → G × Fˣ := fun i => (g^(i:ℕ),1)
  let R : Fin 4 → G × Fˣ := fun i => (g^(i:ℕ)*h,Units.mk0 d hd)
  have hL : Function.Injective L := fun i j hij => hinj (congrArg Prod.fst hij)
  have hR : Function.Injective R := fun i j hij => hinj (mul_right_cancel (congrArg Prod.fst hij))
  have hedge (i j : Fin 4) : (weightedGraph f).Adj (.inl (L i)) (.inr (R j)) := by
    change f ((g^(i:ℕ))⁻¹*(g^(j:ℕ)*h))=1*d
    obtain ⟨k,hk⟩ := hclosed i j
    rw [← mul_assoc,hk,one_mul]
    exact hn k
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro a b hab
  cases a with
  | inl i => cases b with
    | inl j => simp at hab
    | inr j => exact hedge i j
  | inr i => cases b with
    | inl j => exact hedge j i
    | inr j => simp at hab
end Orbit

open Erdos714QuaternionNormPlane (quad central)

@[ext] structure Root (F : Type*) (_eta : F) where
  x : F
  y : F
  z : F
  deriving Fintype, DecidableEq

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (eta : F)

def cocycle (a b x y : F) : F := a*x+a*y+eta*b*y
instance rootMul : Mul (Root F eta) :=
  ⟨fun a b => ⟨a.x+b.x,a.y+b.y,a.z+b.z+cocycle eta a.x a.y b.x b.y⟩⟩
instance rootOne : One (Root F eta) := ⟨⟨0,0,0⟩⟩
instance rootInv : Inv (Root F eta) := ⟨fun a => ⟨-a.x,-a.y,-a.z+quad eta a.x a.y⟩⟩

instance : Group (Root F eta) where
  mul_assoc a b c := by
    apply Root.ext
    · change (a.x+b.x)+c.x=a.x+(b.x+c.x); ring
    · change (a.y+b.y)+c.y=a.y+(b.y+c.y); ring
    · change (a.z+b.z+cocycle eta a.x a.y b.x b.y)+c.z+cocycle eta (a.x+b.x) (a.y+b.y) c.x c.y=
        a.z+(b.z+c.z+cocycle eta b.x b.y c.x c.y)+cocycle eta a.x a.y (b.x+c.x) (b.y+c.y)
      unfold cocycle; ring
  one_mul a := by
    apply Root.ext
    · change 0+a.x=a.x; ring
    · change 0+a.y=a.y; ring
    · change 0+a.z+cocycle eta 0 0 a.x a.y=a.z; unfold cocycle; ring
  mul_one a := by
    apply Root.ext
    · change a.x+0=a.x; ring
    · change a.y+0=a.y; ring
    · change a.z+0+cocycle eta a.x a.y 0 0=a.z; unfold cocycle; ring
  inv_mul_cancel a := by
    apply Root.ext
    · change -a.x+a.x=0; ring
    · change -a.y+a.y=0; ring
    · change (-a.z+quad eta a.x a.y)+a.z+cocycle eta (-a.x) (-a.y) a.x a.y=0
      unfold cocycle quad; ring

def coords : Root F eta ≃ (F × F × F) where
  toFun a := (a.x,a.y,a.z)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨x,y,z⟩; rfl

def center (s : F) : Root F eta := ⟨0,0,s⟩

lemma center_ne_one {s : F} (hs : s ≠ 0) : center eta s ≠ 1 := by
  intro h
  exact hs (congrArg Root.z h)

lemma square [CharP F 2] (a : Root F eta) : a^2=center eta (quad eta a.x a.y) := by
  rw [pow_two]
  apply Root.ext
  · change a.x+a.x=0; simp
  · change a.y+a.y=0; simp
  · change a.z+a.z+cocycle eta a.x a.y a.x a.y=quad eta a.x a.y
    simp [cocycle,quad,pow_two,mul_assoc]

lemma center_square [CharP F 2] (s : F) : (center eta s)^2=1 := by
  rw [square]
  simp only [center,quad,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
  rfl

variable (b : (F × F × F) ≃ₗ[F] E)
def value (a : Root F eta) : E := b (coords eta a)
def fromE (p : E) : Root F eta := (coords eta).symm (b.symm p)
lemma value_fromE (p : E) : value eta b (fromE eta b p)=p := by simp [value,fromE]

lemma value_center_mul (s : F) (a : Root F eta) :
    value eta b (center eta s*a)=s • central b+value eta b a := by
  have he : coords eta (center eta s*a)=s • (0,0,(1:F))+coords eta a := by
    change (0+a.x,0+a.y,s+a.z+cocycle eta 0 0 a.x a.y)=_
    simp [cocycle,coords]
  rw [value,he,map_add,map_smul]
  rfl

/-- Choose the central coordinate so that the first orbit step is the
specified additive displacement v at p. -/
def generator (p v : E) : Root F eta :=
  ⟨(b.symm v).1,(b.symm v).2.1,
    (b.symm v).2.2-cocycle eta (b.symm v).1 (b.symm v).2.1 (b.symm p).1 (b.symm p).2.1⟩

lemma generator_step (p v : E) :
    value eta b (generator eta b p v*fromE eta b p)=v+p := by
  have he : coords eta (generator eta b p v*fromE eta b p)=b.symm v+b.symm p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change (b.symm v).2.2-cocycle eta (b.symm v).1 (b.symm v).2.1 (b.symm p).1 (b.symm p).2.1+
          (b.symm p).2.2+cocycle eta (b.symm v).1 (b.symm v).2.1 (b.symm p).1 (b.symm p).2.1=
          (b.symm v).2.2+(b.symm p).2.2
        ring
  simp [value,he]

/-- The actual norm graph for this quaternion-type central extension. -/
def graph := weightedGraph (fun a : Root F eta => Algebra.norm F (value eta b a))

/-- Uniform exclusion, including every linear coordinate choice. -/
theorem not_free [Fintype F] [Fintype E] [CharP F 2]
    (hdim : Module.finrank F E=3)
    (hQ : ∀ x y, quad eta x y=0 → x=0 ∧ y=0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph eta b) := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  obtain ⟨p,v,hs,hp,hn⟩ := Erdos714QuaternionNormPlane.exists_cyclic_plane hdim b eta hQ
  let s := quad eta (b.symm v).1 (b.symm v).2.1
  let g := generator eta b p v
  let h := fromE eta b p
  have hg2 : g^2=center eta s := square eta g
  have h2 : g^2 ≠ 1 := by rw [hg2]; exact center_ne_one eta hs
  have h4 : g^4=1 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hg2,center_square]
  have hN (i : Fin 4) : Algebra.norm F (value eta b (g^(i:ℕ)*h))=Algebra.norm F p := by
    fin_cases i
    · simp [h,value_fromE]
    · change Algebra.norm F (value eta b (g^1*h))=Algebra.norm F p
      rw [pow_one,generator_step]
      simpa [Erdos714BinaryLift.plane,add_comm] using hn 2
    · change Algebra.norm F (value eta b (g^2*h))=Algebra.norm F p
      rw [hg2,value_center_mul,value_fromE]
      simpa [Erdos714BinaryLift.plane,add_comm] using hn 1
    · change Algebra.norm F (value eta b (g^3*h))=Algebra.norm F p
      rw [show (3:ℕ)=2+1 by rfl,pow_succ,hg2,mul_assoc,value_center_mul,generator_step]
      simpa [Erdos714BinaryLift.plane,add_comm,add_left_comm,add_assoc] using hn 3
  exact fun hf => hf ⟨cyclicCopy _ g h (Algebra.norm F p) hp h4 h2 hN⟩

#print axioms cyclicCopy
#print axioms generator_step
#print axioms not_free
end Erdos714QuaternionCubicNorm
