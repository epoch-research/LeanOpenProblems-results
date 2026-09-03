import Submission.GaussianWeightedSieve

/-! Chinese remaindering of the Gaussian polynomial root counts used in the
weighted sieve. Multiplicativity is proved for coprime Gaussian moduli,
without treating distinct pattern vertices as distinct residue classes. -/
namespace Erdos952Investigation.GaussianRootCRT
open GaussianIdealRepresentatives GaussianPolynomialBoxCounts GaussianWeightedSieve
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

lemma mem_multiples_iff (g z : GaussianInt) : z ∈ multiples g ↔ g ∣ z := by
  change (∃ w, g*w = z) ↔ g ∣ z
  constructor <;> rintro ⟨w,hw⟩ <;> exact ⟨w,hw.symm⟩

def quotientMap (h g : GaussianInt) (hgh : g ∣ h) :
    (GaussianInt ⧸ multiples h) →ₗ[ℤ] (GaussianInt ⧸ multiples g) :=
  (multiples h).mapQ (multiples g) LinearMap.id (by
    intro z hz
    change z ∈ multiples g
    exact (mem_multiples_iff g z).mpr (hgh.trans ((mem_multiples_iff h z).mp hz)))

lemma quotientMap_mk (h g : GaussianInt) (hgh : g ∣ h) (z : GaussianInt) :
    quotientMap h g hgh (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := rfl

def crtMap (a b : GaussianInt) : (GaussianInt ⧸ multiples (a*b)) →
    (GaussianInt ⧸ multiples a) × (GaussianInt ⧸ multiples b) := fun q =>
  (quotientMap (a*b) a (dvd_mul_right a b) q,
   quotientMap (a*b) b (dvd_mul_left b a) q)

lemma crtMap_mk (a b z : GaussianInt) :
    crtMap a b (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk z,Submodule.Quotient.mk z) := rfl

lemma crtMap_injective (a b : GaussianInt) (hc : IsCoprime a b) :
    Function.Injective (crtMap a b) := by
  intro x y he
  obtain ⟨x,rfl⟩ := (Submodule.Quotient.mk_surjective (multiples (a*b))) x
  obtain ⟨y,rfl⟩ := (Submodule.Quotient.mk_surjective (multiples (a*b))) y
  rw [crtMap_mk,crtMap_mk] at he
  apply (quotient_eq_iff_dvd (a*b) x y).mpr
  exact hc.mul_dvd ((quotient_eq_iff_dvd a x y).mp (congrArg Prod.fst he))
    ((quotient_eq_iff_dvd b x y).mp (congrArg Prod.snd he))

lemma crtMap_surjective (a b : GaussianInt) (hc : IsCoprime a b) :
    Function.Surjective (crtMap a b) := by
  rintro ⟨q,r⟩
  obtain ⟨x,rfl⟩ := (Submodule.Quotient.mk_surjective (multiples a)) q
  obtain ⟨y,rfl⟩ := (Submodule.Quotient.mk_surjective (multiples b)) r
  obtain ⟨u,v,hc⟩ := hc
  let w : GaussianInt := x*(v*b)+y*(u*a)
  refine ⟨Submodule.Quotient.mk w,?_⟩
  rw [crtMap_mk]
  apply Prod.ext
  · apply (quotient_eq_iff_dvd a w x).mpr
    refine ⟨u*(y-x),?_⟩
    dsimp [w]
    linear_combination x*hc
  · apply (quotient_eq_iff_dvd b w y).mpr
    refine ⟨v*(x-y),?_⟩
    dsimp [w]
    linear_combination y*hc

def crtEquiv (a b : GaussianInt) (hc : IsCoprime a b) :
    (GaussianInt ⧸ multiples (a*b)) ≃
      (GaussianInt ⧸ multiples a) × (GaussianInt ⧸ multiples b) :=
  Equiv.ofBijective (crtMap a b) ⟨crtMap_injective a b hc,crtMap_surjective a b hc⟩

lemma crtEquiv_mk (a b : GaussianInt) (hc : IsCoprime a b) (z : GaussianInt) :
    crtEquiv a b hc (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk z,Submodule.Quotient.mk z) := rfl

lemma rootCount_card (g : GaussianInt) (hg : g ≠ 0) (P : Polynomial GaussianInt) :
    rootCount g hg P = Nat.card {q : GaussianInt ⧸ multiples g // q ∈ rootClasses g hg P} := by
  simp [rootCount,Nat.card_eq_fintype_card]

/-- Exact multiplicativity of polynomial root counts at coprime moduli. -/
theorem rootCount_mul (a b : GaussianInt) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) (P : Polynomial GaussianInt) :
    rootCount (a*b) (mul_ne_zero ha hb) P = rootCount a ha P*rootCount b hb P := by
  let e := crtEquiv a b hc
  have he (q : GaussianInt ⧸ multiples (a*b)) :
      q ∈ rootClasses (a*b) (mul_ne_zero ha hb) P ↔
      (e q).1 ∈ rootClasses a ha P ∧ (e q).2 ∈ rootClasses b hb P := by
    obtain ⟨t,rfl⟩ := (Submodule.Quotient.mk_surjective (multiples (a*b))) q
    change _ ↔ (crtEquiv a b hc (Submodule.Quotient.mk t)).1 ∈ _ ∧
      (crtEquiv a b hc (Submodule.Quotient.mk t)).2 ∈ _
    rw [crtEquiv_mk]
    simp only [mem_rootClasses]
    exact ⟨fun h => ⟨(dvd_mul_right a b).trans h,(dvd_mul_left b a).trans h⟩,
      fun h => hc.mul_dvd h.1 h.2⟩
  let ee := (e.subtypeEquiv he).trans (Equiv.subtypeProdEquivProd
    (p := fun q => q ∈ rootClasses a ha P) (q := fun r => r ∈ rootClasses b hb P))
  rw [rootCount_card,rootCount_card,rootCount_card,← Nat.card_prod]
  exact Nat.card_congr ee

theorem rho_mul (a b : GaussianInt) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : IsCoprime a b) (P : Polynomial GaussianInt) :
    rho P (a*b) = rho P a*rho P b := by
  rw [rho_of_ne_zero P (a*b) (mul_ne_zero ha hb),rho_of_ne_zero P a ha,rho_of_ne_zero P b hb]
  exact rootCount_mul a b ha hb hc P


/-- The CRT root count for a finite pairwise-coprime family. -/
theorem rho_prod {ι : Type*} (g : ι → GaussianInt) (h0 : ∀ i, g i ≠ 0)
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j)))
    (s : Finset ι) (P : Polynomial GaussianInt) :
    rho P (∏ i ∈ s, g i) = ∏ i ∈ s, rho P (g i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [rho_of_ne_zero P 1 one_ne_zero,rootCount_of_isUnit 1 one_ne_zero P isUnit_one]
  | @insert i s hi ih =>
    have hs : ∏ j ∈ s, g j ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => h0 j)
    have hcop : IsCoprime (g i) (∏ j ∈ s, g j) := IsCoprime.prod_right
      (fun j hj => hc (by intro he; exact hi (he ▸ hj)))
    rw [Finset.prod_insert hi,rho_mul (g i) _ (h0 i) hs hcop P,ih,Finset.prod_insert hi]

/-- A k-vertex pattern has at most k^r roots at a squarefree product of r
pairwise-coprime Gaussian primes. The actual local collisions remain in rho. -/
theorem rho_pattern_prod_le {ι κ : Type*} [Fintype κ]
    (z : κ → GaussianInt) (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j))) (s : Finset ι) :
    rho (patternPolynomial z) (∏ i ∈ s, g i) ≤ (Fintype.card κ)^s.card := by
  rw [rho_prod g (fun i => (hg i).ne_zero) hc]
  calc
    _ ≤ ∏ _i ∈ s, Fintype.card κ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun i _ => by
        rw [rho_of_ne_zero _ _ (hg i).ne_zero]
        exact rootCount_prime_pattern_le z (g i) (hg i))
    _ = _ := Finset.prod_const _

/-- Equality when every local quotient separates all vertices. -/
theorem rho_pattern_prod_eq {ι κ : Type*} [Fintype κ]
    (z : κ → GaussianInt) (hz : Function.Injective z)
    (g : ι → GaussianInt) (hg : ∀ i, Prime (g i))
    (hc : Pairwise (fun i j => IsCoprime (g i) (g j))) (s : Finset ι)
    (hb : ∀ j ∈ s, ∀ u v, (z u-z v).norm < (g j).norm) :
    rho (patternPolynomial z) (∏ i ∈ s, g i) = (Fintype.card κ)^s.card := by
  rw [rho_prod g (fun i => (hg i).ne_zero) hc]
  calc
    _ = ∏ _i ∈ s, Fintype.card κ := Finset.prod_congr rfl (fun i hi => by
      rw [rho_of_ne_zero _ _ (hg i).ne_zero]
      exact rootCount_prime_pattern_of_norm_bound z hz (g i) (hg i) (hb i hi))
    _ = _ := Finset.prod_const _

#print axioms rho_prod
#print axioms rho_pattern_prod_le
#print axioms rho_pattern_prod_eq

#print axioms crtEquiv
#print axioms rootCount_mul
#print axioms rho_mul
end
end Erdos952Investigation.GaussianRootCRT
