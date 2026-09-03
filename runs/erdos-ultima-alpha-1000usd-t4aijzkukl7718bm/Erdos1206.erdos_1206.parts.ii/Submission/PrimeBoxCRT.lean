import Submission.PeriodicBoxCount

/-!
Chinese-remainder factorization of arbitrary two-coordinate local conditions
at finitely many distinct primes, with a uniform box discrepancy.
-/
namespace Erdos1206.PrimeBoxCRT
open Finset PeriodicBoxCount
open scoped Classical

lemma prime_product_pos (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hS p hp).pos)

/-- The local residue sets may have any shape. -/
theorem exists_joint_residues (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (B : (p : ℕ) → Finset (ZMod p × ZMod p)) :
    ∃ C : Finset (ℕ × ℕ),
      C ⊆ (range (∏ p ∈ S, p)) ×ˢ (range (∏ p ∈ S, p)) ∧
      (∀ t u : ℕ, (t%(∏ p ∈ S, p),u%(∏ p ∈ S, p)) ∈ C ↔
        ∀ p ∈ S, ((t:ZMod p),(u:ZMod p)) ∈ B p) ∧
      C.card=∏ p ∈ S, (B p).card := by
  let d : ℕ := ∏ p ∈ S, p
  have hd : 0 < d := prime_product_pos S hS
  letI : NeZero d := ⟨hd.ne'⟩
  have hcop : Pairwise (Function.onFun Nat.Coprime (fun p : S => (p:ℕ))) := by
    intro p q hpq
    apply (Nat.coprime_primes (hS p p.property) (hS q q.property)).mpr
    exact fun h => hpq (Subtype.ext h)
  have hdprod : (∏ p : S, (p:ℕ))=d := prod_coe_sort S id
  let e : ZMod d ≃+* ((p : S) → ZMod (p:ℕ)) :=
    (ZMod.ringEquivCongr hdprod.symm).trans (ZMod.prodEquivPi (fun p : S => (p:ℕ)) hcop)
  have hecast (n : ℕ) (p : S) : e (n:ZMod d) p=(n:ZMod (p:ℕ)) := by
    exact congrFun (map_natCast e n) p
  let C : Finset (ℕ × ℕ) := ((range d) ×ˢ (range d)).filter (fun x =>
    ∀ p ∈ S, ((x.1:ZMod p),(x.2:ZMod p)) ∈ B p)
  have hC : C ⊆ (range d) ×ˢ (range d) := filter_subset _ _
  have hperiod (n p : ℕ) (hp : p ∈ S) : ((n%d:ℕ):ZMod p)=(n:ZMod p) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    exact Nat.mod_mod_of_dvd n (dvd_prod_of_mem id hp)
  refine ⟨C,hC,?_,?_⟩
  · intro t u
    change ((t%d,u%d) ∈ C) ↔ _
    simp only [C,mem_filter,mem_product,mem_range,Nat.mod_lt _ hd,true_and]
    exact forall₂_congr (fun p hp => by rw [hperiod t p hp,hperiod u p hp])
  · let f : C → ((p : S) → ↥(B (p:ℕ))) := fun x p =>
      ⟨(((x.val.1):ZMod (p:ℕ)),((x.val.2):ZMod (p:ℕ))),
        (mem_filter.mp x.property).2 p p.property⟩
    have hinj : Function.Injective f := by
      intro x y hxy
      have he1 : e (x.val.1:ZMod d)=e (y.val.1:ZMod d) := by
        funext p
        simpa only [hecast] using congrArg (fun z => (z p).val.1) hxy
      have he2 : e (x.val.2:ZMod d)=e (y.val.2:ZMod d) := by
        funext p
        simpa only [hecast] using congrArg (fun z => (z p).val.2) hxy
      have h1 := congrArg ZMod.val (e.injective he1)
      have h2 := congrArg ZMod.val (e.injective he2)
      obtain ⟨hx1,hx2⟩ := mem_product.mp (hC x.property)
      obtain ⟨hy1,hy2⟩ := mem_product.mp (hC y.property)
      rw [ZMod.val_cast_of_lt (mem_range.mp hx1),ZMod.val_cast_of_lt (mem_range.mp hy1)] at h1
      rw [ZMod.val_cast_of_lt (mem_range.mp hx2),ZMod.val_cast_of_lt (mem_range.mp hy2)] at h2
      exact Subtype.ext (Prod.ext h1 h2)
    have hsurj : Function.Surjective f := by
      intro y
      let a : ZMod d := e.symm (fun p => (y p).val.1)
      let b : ZMod d := e.symm (fun p => (y p).val.2)
      have ha (p : S) : (a.val:ZMod (p:ℕ))=(y p).val.1 := by
        calc
          _ = e (a.val:ZMod d) p := (hecast a.val p).symm
          _ = e a p := by rw [ZMod.natCast_zmod_val]
          _ = _ := congrFun (e.apply_symm_apply _) p
      have hb (p : S) : (b.val:ZMod (p:ℕ))=(y p).val.2 := by
        calc
          _ = e (b.val:ZMod d) p := (hecast b.val p).symm
          _ = e b p := by rw [ZMod.natCast_zmod_val]
          _ = _ := congrFun (e.apply_symm_apply _) p
      have hc : (a.val,b.val) ∈ C := by
        apply mem_filter.mpr
        refine ⟨mem_product.mpr ⟨mem_range.mpr a.val_lt,mem_range.mpr b.val_lt⟩,?_⟩
        intro p hp
        rw [ha ⟨p,hp⟩,hb ⟨p,hp⟩]
        exact (y ⟨p,hp⟩).property
      refine ⟨⟨(a.val,b.val),hc⟩,?_⟩
      funext p
      apply Subtype.ext
      exact Prod.ext (ha p) (hb p)
    have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
    simp only [Fintype.card_coe,Fintype.card_pi] at hcard
    exact hcard.trans (prod_coe_sort S (fun p => (B p).card))

noncomputable def localDensity (B : (p : ℕ) → Finset (ZMod p × ZMod p)) (p : ℕ) : ℝ :=
  (B p).card/(p:ℝ)^2

/-- An exact CRT main term with an error polynomial in the modulus. -/
theorem joint_box_discrepancy (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (B : (p : ℕ) → Finset (ZMod p × ZMod p)) (N : ℕ) :
    |((((range N) ×ˢ (range N)).filter (fun x =>
        ∀ p ∈ S, ((x.1:ZMod p),(x.2:ZMod p)) ∈ B p)).card:ℝ) -
        (N:ℝ)^2*(∏ p ∈ S, localDensity B p)| ≤
      2*(N:ℝ)*(∏ p ∈ S, (p:ℝ))+(∏ p ∈ S, (p:ℝ))^2 := by
  obtain ⟨C,hC,hiff,hcard⟩ := exists_joint_residues S hS B
  have hd := prime_product_pos S hS
  have hecount : (((range N) ×ˢ (range N)).filter (fun x =>
      ∀ p ∈ S, ((x.1:ZMod p),(x.2:ZMod p)) ∈ B p)).card =
      boxCount N (∏ p ∈ S, p) C := by
    congr 1
    ext x
    simp only [mem_filter,hiff]
  have heprod : (∏ p ∈ S, localDensity B p) = (C.card:ℝ)/(∏ p ∈ S, (p:ℝ))^2 := by
    rw [hcard,Nat.cast_prod]
    simp only [localDensity,prod_div_distrib,prod_pow]
  have hh := boxCount_discrepancy N (∏ p ∈ S, p) C hd hC
  rw [hecount,heprod]
  simpa only [Nat.cast_prod,div_eq_mul_inv,mul_assoc] using hh

#print axioms exists_joint_residues
#print axioms joint_box_discrepancy
end Erdos1206.PrimeBoxCRT
