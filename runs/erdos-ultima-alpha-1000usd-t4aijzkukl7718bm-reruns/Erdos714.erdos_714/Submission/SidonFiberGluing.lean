import FormalConjecturesUtil

/-! A norm-ratio grid obstructs a proposed gluing of additive Sidon norm-circle
fibers. The quotient weight labels are used throughout, so the result is not
an artifact of retaining several identical representatives of each vertex.
This is not a proof or disproof of Erdős 714. -/

noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 2000000

namespace Erdos714SidonGluing
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The quotient label, not a chosen representative of its fiber. -/
def ratio (σ : E →+* E) (a : Eˣ) : Eˣ := Units.map σ.toMonoidHom a / a

abbrev Weight (σ : E →+* E) := Set.range (ratio σ)
abbrev Vertex (σ : E →+* E) := E × Weight σ

def label (σ : E →+* E) (a : Eˣ) : Weight σ := ⟨ratio σ a,⟨a,rfl⟩⟩

def form (σ : E →+* E) (δ x : E) : E := x+δ*σ x

def kernel (σ : E →+* E) (δ : E) (a b : Vertex σ) : E :=
  a.1+b.1+δ*((a.2.1 : E)*(b.2.1 : E))*σ (a.1+b.1)

def graph (σ : E →+* E) (δ : E) : SimpleGraph (Vertex σ ⊕ Vertex σ) where
  Adj a b := match a,b with
    | .inl u,.inr v => Algebra.norm F (kernel σ δ u v)=1
    | .inr v,.inl u => Algebra.norm F (kernel σ δ u v)=1
    | _,_ => False
  symm := by intro a b; cases a <;> cases b <;> simp_all
  loopless := by intro a; cases a <;> simp

/-- A prescribed ratio has at most three representatives when sigma squared
is fourth powering. This proves the multiplicity bound before any quotient. -/
lemma ratio_cube (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x^4)
    (a c : Eˣ) (ha : ratio σ a=c) : (a : E)^3=σ (c : E)*(c : E) := by
  have he : σ (a : E)=(c : E)*(a : E) := by
    have hh := congrArg (fun u : Eˣ => (u : E)) ha
    simp only [ratio,Units.val_div_eq_div_val,Units.coe_map] at hh
    exact (div_eq_iff (Units.ne_zero a)).mp hh
  have he' : (a : E)^4=σ (c : E)*(c : E)*(a : E) := by
    calc
      _ = σ (σ (a : E)) := (hσ _).symm
      _ = σ ((c : E)*(a : E)) := congrArg σ he
      _ = _ := by rw [map_mul,he]; ring
  apply mul_right_cancel₀ (Units.ne_zero a)
  simpa only [←pow_succ] using he'

lemma ratio_fiber_bound [Fintype E] (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x^4)
    (c : Eˣ) : (univ.filter (fun a : Eˣ => ratio σ a=c)).card ≤ 3 := by
  apply (show _ ≤ (Polynomial.nthRoots 3 (σ (c : E)*(c : E))).toFinset.card from ?_).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 _))
  apply card_le_card_of_injOn (fun a : Eˣ => (a : E))
  · intro a ha
    change (a : E) ∈ (Polynomial.nthRoots 3 (σ (c : E)*(c : E))).toFinset
    rw [Multiset.mem_toFinset,Polynomial.mem_nthRoots (by decide : 0<3)]
    exact ratio_cube σ hσ a c (mem_filter.mp ha).2
  · intro a ha b hb hab
    exact Units.ext hab

lemma ratio_image_bound [Fintype E] (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x^4)
    (S : Finset Eˣ) : S.card ≤ 3*(S.image (ratio σ)).card := by
  apply card_le_mul_card_image S 3
  intro c hc
  exact (card_le_card (filter_subset_filter _ (subset_univ S))).trans
    (ratio_fiber_bound σ hσ c)

/-- The noncube condition makes the additive binomial nonsingular. -/
lemma form_ne_zero [CharP E 2] (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x^4)
    (δ : E) (hδ : ∀ z : E, z^3≠δ*σ δ) {a : E} (ha : a≠0) :
    form σ δ a≠0 := by
  intro hh
  have he : a=δ*σ a := CharTwo.add_eq_zero.mp hh
  have he' : σ a=σ δ*a^4 := by
    calc
      _ = σ (δ*σ a) := congrArg σ he
      _ = _ := by rw [map_mul,hσ]
  have hc : (δ*σ δ)*a^3=1 := by
    apply mul_right_cancel₀ ha
    calc
      (δ*σ δ)*a^3*a = δ*(σ δ*a^4) := by ring
      _ = δ*σ a := by rw [←he']
      _ = 1*a := by simpa using he.symm
  apply hδ a⁻¹
  rw [inv_pow,inv_eq_one_div]
  apply (div_eq_iff (pow_ne_zero 3 ha)).mpr
  exact hc.symm

/-- Norm-one circles in a binary quadratic field have unique nonzero pair sums.
Only the displayed norm identities and an additive field homomorphism are used. -/
lemma norm_circle_pair_unique [CharP E 2] (ρ : E →+* E)
    (x y z w : E) (hx : x*ρ x=1) (hy : y*ρ y=1) (hz : z*ρ z=1) (hw : w*ρ w=1)
    (hxy : x≠y) (hs : x+y=z+w) : x=z ∨ x=w := by
  have hsum : x+y≠0 := fun he => hxy (CharTwo.add_eq_zero.mp he)
  have pair (a b : E) (ha : a*ρ a=1) (hb : b*ρ b=1) :
      (ρ a+ρ b)*(a*b)=a+b := by linear_combination b*ha+a*hb
  have hrho : ρ x+ρ y=ρ z+ρ w := by simpa only [map_add] using congrArg ρ hs
  have hp : (x+y)*(z*w)=(z+w)*(x*y) := by
    calc
      _ = ((ρ x+ρ y)*(x*y))*(z*w) := by rw [pair x y hx hy]
      _ = ((ρ z+ρ w)*(z*w))*(x*y) := by rw [hrho]; ring
      _ = _ := by rw [pair z w hz hw]
  rw [←hs] at hp
  have hprod : z*w=x*y := mul_left_cancel₀ hsum hp
  have hh : (x-z)*(x-w)=0 := by linear_combination hprod+x*hs
  rcases mul_eq_zero.mp hh with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

lemma form_add (σ : E →+* E) (δ x y : E) :
    form σ δ (x+y)=form σ δ x+form σ δ y := by
  simp only [form,map_add]
  ring

lemma form_injective [CharP E 2] (σ : E →+* E) (δ : E)
    (hL : ∀ a : E, a≠0 → form σ δ a≠0) : Function.Injective (form σ δ) := by
  intro a b hab
  by_contra hn
  apply hL (a+b) (fun he => hn (CharTwo.add_eq_zero.mp he))
  rw [form_add,hab]
  simp

/-- All local binomials are conjugate to the same injective additive map. -/
lemma local_form_identity (σ : E →+* E) (δ x : E) (a b : Eˣ) :
    form σ (δ*((ratio σ a : E)*(ratio σ b : E))) x =
      form σ δ ((a : E)*(b : E)*x)/((a : E)*(b : E)) := by
  simp only [form,ratio,Units.val_div_eq_div_val,Units.coe_map,map_mul]
  change x+δ*((σ (a : E)/(a : E))*(σ (b : E)/(b : E)))*σ x =
    ((a : E)*(b : E)*x+δ*(σ (a : E)*σ (b : E)*σ x))/((a : E)*(b : E))
  field_simp

lemma local_form_injective [CharP E 2] (σ : E →+* E) (δ : E)
    (hL : ∀ a : E, a≠0 → form σ δ a≠0) (s t : Weight σ) :
    Function.Injective (form σ (δ*((s.1 : E)*(t.1 : E)))) := by
  obtain ⟨a,ha⟩ := s.property
  obtain ⟨b,hb⟩ := t.property
  have hI := form_injective σ δ hL
  intro x y h
  rw [←ha,←hb,local_form_identity,local_form_identity] at h
  apply mul_left_cancel₀ (mul_ne_zero (Units.ne_zero a) (Units.ne_zero b))
  apply hI
  exact (div_left_inj' (mul_ne_zero (Units.ne_zero a) (Units.ne_zero b))).mp h

/-- The local norm fibers are genuinely Sidon, independently of the later
counterexample to their global gluing. -/
lemma local_fiber_pair_unique [CharP E 2] (σ ρ : E →+* E) (δ : E)
    (hL : ∀ a : E, a≠0 → form σ δ a≠0)
    (hN : ∀ a : E, algebraMap F E (Algebra.norm F a)=a*ρ a)
    (s t : Weight σ) (x y z w : E)
    (hx : Algebra.norm F (form σ (δ*((s.1 : E)*(t.1 : E))) x)=1)
    (hy : Algebra.norm F (form σ (δ*((s.1 : E)*(t.1 : E))) y)=1)
    (hz : Algebra.norm F (form σ (δ*((s.1 : E)*(t.1 : E))) z)=1)
    (hw : Algebra.norm F (form σ (δ*((s.1 : E)*(t.1 : E))) w)=1)
    (hxy : x≠y) (hs : x+y=z+w) : x=z ∨ x=w := by
  let L := form σ (δ*((s.1 : E)*(t.1 : E)))
  have hI : Function.Injective L := local_form_injective σ δ hL s t
  have H (a : E) (ha : Algebra.norm F (L a)=1) : (L a)*ρ (L a)=1 := by
    rw [←hN,ha,map_one]
  have he : L x+L y=L z+L w := by
    change form σ _ x+form σ _ y=form σ _ z+form σ _ w
    rw [←form_add,←form_add,hs]
  rcases norm_circle_pair_unique ρ (L x) (L y) (L z) (L w)
    (H x hx) (H y hy) (H z hz) (H w hw) (hI.ne hxy) he with h | h
  · exact Or.inl (hI h)
  · exact Or.inr (hI h)

variable [Fintype E] [Fintype F]

/-- The norm identity used by the local Sidon theorem is the actual quadratic
finite-field norm, not an additional property of a hypothetical kernel. -/
lemma quadratic_norm_formula (ρ : E →+* E) (q : ℕ)
    (hF : Fintype.card F=q) (hE : Fintype.card E=q^2) (hρ : ∀ x, ρ x=x^q)
    (x : E) : algebraMap F E (Algebra.norm F x)=x*ρ x := by
  have hq : 1<q := by simpa only [hF] using (Fintype.one_lt_card (α := F))
  have he : q^2-1=(q+1)*(q-1) := by
    have h1 := Nat.sub_add_cancel (show 1≤q by omega)
    have h2 := Nat.sub_add_cancel (show 1≤q^2 by nlinarith)
    nlinarith
  rw [FiniteField.algebraMap_norm_eq_pow]
  simp only [←Fintype.card_eq_nat_card,hE,hF,he,Nat.mul_div_cancel _ (by omega : 0<q-1)]
  rw [hρ,pow_succ,mul_comm]

def formUnit (σ : E →+* E) (δ : E) (hL : ∀ a : E, a≠0 → form σ δ a≠0)
    (a : Eˣ) : Eˣ := Units.mk0 (form σ δ a) (hL a (Units.ne_zero a))

def normProfile (σ : E →+* E) (δ : E) (hL : ∀ a : E, a≠0 → form σ δ a≠0)
    (a : Eˣ) : Fˣ := Units.map (Algebra.norm F) (formUnit σ δ hL a / a)

def row (σ : E →+* E) (a : Eˣ) : Vertex σ := (0,label σ a)
def column (σ : E →+* E) (b : Eˣ) : Vertex σ := ((b : E)⁻¹,label σ b)

omit [Fintype E] in
lemma kernel_identity (σ : E →+* E) (δ : E) (a b : Eˣ) :
    kernel σ δ (row σ a) (column σ b)=form σ δ (a : E)/((a : E)*(b : E)) := by
  simp only [kernel,row,column,label,ratio,zero_add,Units.val_div_eq_div_val,
    Units.coe_map,map_inv₀,form]
  change (b : E)⁻¹+δ*((σ (a : E)/(a : E))*(σ (b : E)/(b : E)))*(σ (b : E))⁻¹ =
    ((a : E)+δ*σ (a : E))/((a : E)*(b : E))
  have hb : σ (b : E)≠0 := by simpa only [map_zero] using σ.injective.ne (Units.ne_zero b)
  field_simp

omit [Fintype E] [Fintype F] in
lemma grid_edge (σ : E →+* E) (δ : E) (hL : ∀ a : E, a≠0 → form σ δ a≠0)
    (c : Fˣ) (a b : Eˣ) (ha : normProfile (F := F) σ δ hL a=c)
    (hb : Units.map (Algebra.norm F) b=c) :
    (graph (F := F) σ δ).Adj (.inl (row σ a)) (.inr (column σ b)) := by
  have hn : Units.map (Algebra.norm F) (formUnit σ δ hL a/(a*b))=1 := by
    rw [div_mul_eq_div_div,map_div]
    change normProfile σ δ hL a / _=1
    rw [ha,hb]
    simp
  have hn' := congrArg (fun u : Fˣ => (u : F)) hn
  change Algebra.norm F (kernel σ δ (row σ a) (column σ b))=1
  rw [kernel_identity]
  simpa only [Units.coe_map,Units.val_div_eq_div_val,Units.val_mul,Units.val_one,
    formUnit,Units.val_mk0] using hn'

/-- The grid is in the actual quotient-label graph. -/
def gridCopy (σ : E →+* E) (δ : E) (hL : ∀ a : E, a≠0 → form σ δ a≠0)
    {r : ℕ} (c : Fˣ) (a : Fin r → Eˣ) (b : Fin r ↪ Eˣ)
    (hai : Function.Injective (fun i => ratio σ (a i)))
    (ha : ∀ i, normProfile (F := F) σ δ hL (a i)=c)
    (hb : ∀ j, Units.map (Algebra.norm F) (b j)=c) :
    Copy (completeBipartiteGraph (Fin r) (Fin r)) (graph (F := F) σ δ) := by
  let L : Fin r ↪ Vertex σ := ⟨fun i => row σ (a i),by
    intro i j hij
    exact hai (congrArg (fun v : Vertex σ => v.2.1) hij)⟩
  let R : Fin r ↪ Vertex σ := ⟨fun j => column σ (b j),by
    intro i j hij
    apply b.injective
    apply Units.ext
    exact inv_injective (congrArg Prod.fst hij)⟩
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨L.injective,R.injective⟩⟩
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl j => simp at huv
    | inr j => exact grid_edge σ δ hL c (a i) (b j) (ha i) (hb j)
  | inr i =>
    cases v with
    | inl j => exact (grid_edge σ δ hL c (a j) (b i) (ha j) (hb i)).symm
    | inr j => simp at huv

/-- Pigeonhole on the norm ratio, with the three-to-one weight quotient
fully accounted for, gives growing actual bicliques. -/
theorem not_free_of_card (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x^4)
    (δ : E) (hL : ∀ a : E, a≠0 → form σ δ a≠0)
    (r : ℕ) (hr : 1≤r)
    (hc : Fintype.card Fˣ*(3*(r-1))<Fintype.card Eˣ) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph (F := F) σ δ) := by
  obtain ⟨c,hc'⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (normProfile (F := F) σ δ hL) hc
  let S : Finset Eˣ := univ.filter (fun a => normProfile (F := F) σ δ hL a=c)
  have hS : 3*(r-1)<S.card := hc'
  have hi : r≤(S.image (ratio σ)).card := by
    have hh := ratio_image_bound σ hσ S
    omega
  obtain ⟨w : Fin r ↪ Eˣ,hw⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := S.image (ratio σ)) (by simpa using hi)
  have hpre : ∀ i, ∃ a : Eˣ, normProfile (F := F) σ δ hL a=c ∧ ratio σ a=w i := by
    intro i
    obtain ⟨a,ha,he⟩ := mem_image.mp (hw ⟨i,rfl⟩)
    exact ⟨a,(mem_filter.mp ha).2,he⟩
  choose a ha haw using hpre
  obtain ⟨c',hc'⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
    (Units.map (Algebra.norm F (S := E))) hc
  have hnorm : (univ.filter (fun b : Eˣ => Units.map (Algebra.norm F) b=c')).card =
      (univ.filter (fun b : Eˣ => Units.map (Algebra.norm F) b=c)).card :=
    MonoidHom.card_fiber_eq_of_mem_range (Units.map (Algebra.norm F (S := E)))
      (x := c') (y := c)
      (FiniteField.unitsMap_norm_surjective F E c') (FiniteField.unitsMap_norm_surjective F E c)
  rw [hnorm] at hc'
  have hbcard : r≤(univ.filter (fun b : Eˣ => Units.map (Algebra.norm F) b=c)).card := by omega
  obtain ⟨b : Fin r ↪ Eˣ,hb⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin r) (s := univ.filter (fun b : Eˣ => Units.map (Algebra.norm F) b=c))
    (by simpa using hbcard)
  intro hfree
  apply hfree
  refine ⟨gridCopy σ δ hL c a b ?_ ha ?_⟩
  · intro i j hij
    apply w.injective
    simpa only [haw] using hij
  · intro j
    exact (mem_filter.mp (hb ⟨j,rfl⟩)).2

/-- At quadratic-extension sizes this excludes every scale with q+1>3(r-1). -/
theorem quadratic_scale_not_free [CharP E 2]
    (σ : E →+* E) (hσ : ∀ x, σ (σ x)=x^4)
    (δ : E) (hδ : ∀ z : E, z^3≠δ*σ δ) (q r : ℕ)
    (hF : Fintype.card F=q) (hE : Fintype.card E=q^2)
    (hr : 1≤r) (hq : 3*(r-1)<q+1) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph (F := F) σ δ) := by
  apply not_free_of_card σ hσ δ (fun a ha => form_ne_zero σ hσ δ hδ ha) r hr
  have hq2 : 2≤q := by simpa only [hF] using (Fintype.one_lt_card (α := F))
  rw [Fintype.card_units,Fintype.card_units,hF,hE]
  have hqsub : q-1+1=q := Nat.sub_add_cancel (by omega)
  have hqsub2 : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
  nlinarith

omit [Fintype F] in
/-- The concrete Frobenius exponent has the required fourth-power square. -/
lemma sigma_square_of_power (σ : E →+* E) (q : ℕ)
    (hE : Fintype.card E=q^2) (hp : ∀ x, σ x=x^(2*q)) (x : E) :
    σ (σ x)=x^4 := by
  rw [hp,hp,←pow_mul]
  calc
    x^(2*q*(2*q)) = x^(q^2*4) := by congr 1; ring
    _ = (x^(q^2))^4 := pow_mul ..
    _ = x^4 := by rw [←hE,FiniteField.pow_card]

omit [Fintype E] [Fintype F] in
/-- A noncube remains a noncube after the exponent 2q+1 when q is 2 mod 3. -/
lemma noncube_product (σ : E →+* E) (q : ℕ) (hq : q%3=2)
    (hp : ∀ x, σ x=x^(2*q)) (δ : E) (hδ : ∀ z : E, z^3≠δ) :
    ∀ z : E, z^3≠δ*σ δ := by
  have hd : δ≠0 := by
    intro he
    apply hδ 0
    simp [he]
  intro z hz
  have hz' : z^3=δ^(2*q+1) := by
    rw [hp] at hz
    simpa only [pow_succ,mul_comm] using hz
  have hz0 : z≠0 := by
    intro he
    rw [he,zero_pow (by decide : (3:ℕ)≠0)] at hz'
    exact pow_ne_zero _ hd hz'.symm
  have he : ((2*q+2)/3)*3=2*q+2 := by omega
  apply hδ (δ^((2*q+2)/3)/z)
  rw [div_pow,←pow_mul,he,hz']
  apply (div_eq_iff (pow_ne_zero _ hd)).mpr
  rw [show 2*q+2=(2*q+1)+1 by omega,pow_succ]
  ring

/-- All hypotheses are discharged for the specified power law, except for the
explicit field sizes and the chosen noncube parameter. -/
theorem noncube_gluing_not_free [CharP E 2]
    (σ : E →+* E) (q : ℕ) (hF : Fintype.card F=q) (hE : Fintype.card E=q^2)
    (hp : ∀ x, σ x=x^(2*q)) (hq3 : q%3=2) (δ : E) (hδ : ∀ z : E, z^3≠δ)
    (hq : 8<q) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (F := F) σ δ) := by
  apply quadratic_scale_not_free σ (sigma_square_of_power σ q hE hp) δ
    (noncube_product σ q hq3 hp δ hδ) q 4 hF hE (by omega)
  omega

/-- In particular the entire intended odd-degree binary family fails from q=32 on.
The vertex labels remain the exact image of sigma(A)/A throughout. -/
theorem binary_odd_not_free [CharP E 2] (k : ℕ) (hk : 2≤k)
    (hF : Fintype.card F=2^(2*k+1)) (hE : Fintype.card E=(2^(2*k+1))^2)
    (δ : E) (hδ : ∀ z : E, z^3≠δ) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (graph (F := F) (iterateFrobenius E 2 (2*k+2)) δ) := by
  apply noncube_gluing_not_free (iterateFrobenius E 2 (2*k+2))
    (2^(2*k+1)) hF hE ?_ ?_ δ hδ ?_
  · intro x
    simp only [iterateFrobenius_def]
    congr 1
    rw [show 2*k+2=(2*k+1)+1 by omega,pow_succ]
    ring
  · rw [pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]
  · have hh : 2^5≤2^(2*k+1) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh
    omega

end Erdos714SidonGluing

#print axioms Erdos714SidonGluing.ratio_fiber_bound
#print axioms Erdos714SidonGluing.ratio_image_bound
#print axioms Erdos714SidonGluing.form_ne_zero
#print axioms Erdos714SidonGluing.kernel_identity
#print axioms Erdos714SidonGluing.gridCopy
#print axioms Erdos714SidonGluing.not_free_of_card
#print axioms Erdos714SidonGluing.quadratic_scale_not_free

#print axioms Erdos714SidonGluing.noncube_product
#print axioms Erdos714SidonGluing.noncube_gluing_not_free
#print axioms Erdos714SidonGluing.binary_odd_not_free

#print axioms Erdos714SidonGluing.norm_circle_pair_unique
#print axioms Erdos714SidonGluing.local_form_injective
#print axioms Erdos714SidonGluing.local_fiber_pair_unique

#print axioms Erdos714SidonGluing.quadratic_norm_formula
