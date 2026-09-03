import Submission.BlockSecondMoment

/-! Exact fiber counts for complementary linear-map blocks. -/
noncomputable section
open Finset Classical Module
set_option maxHeartbeats 2000000
namespace Erdos714LinearBlocks

variable {F V W : Type*} [Field F] [Fintype F]
  [AddCommGroup V] [Module F V] [Fintype V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] [Fintype W] [FiniteDimensional F W]

lemma fiber_card (f : V →ₗ[F] W) (hf : Function.Surjective f) (w : W) :
    (univ.filter (fun x => f x = w)).card =
      Fintype.card F^(finrank F V-finrank F W) := by
  obtain ⟨v, rfl⟩ := hf w
  let e : {x : V // f x = f v} ≃ f.ker := {
    toFun := fun x => ⟨x.val-v, by simp [LinearMap.mem_ker, x.property]⟩
    invFun := fun x => ⟨x.val+v, by simp [LinearMap.mem_ker.mp x.property]⟩
    left_inv := by intro x; apply Subtype.ext; simp
    right_inv := by intro x; apply Subtype.ext; simp }
  have hk := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hk
  have hd : finrank F f.ker = finrank F V-finrank F W := by omega
  calc
    _ = Fintype.card {x : V // f x = f v} := (Fintype.card_subtype _).symm
    _ = Fintype.card f.ker := Fintype.card_congr e
    _ = _ := by rw [Module.card_eq_pow_finrank (K := F), hd]

abbrev End := V →ₗ[F] V
local instance endFintype : Fintype (End (F := F) (V := V)) := Fintype.ofInjective (fun f => (f : V → V)) DFunLike.coe_injective
local instance dualFintype : Fintype (Module.Dual F V) :=
  Fintype.ofInjective (fun f => (f : V → F)) DFunLike.coe_injective

def atPoint (v : V) : End (F := F) (V := V) →ₗ[F] V := LinearMap.applyₗ (R := F) (M₂ := V) v

lemma atPoint_surjective (v : V) (hv : v ≠ 0) : Function.Surjective (atPoint (F := F) v) := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hv
  intro w
  exact ⟨φ.smulRight w, by simp [atPoint, hφ]⟩

lemma point_count (hd : finrank F V = 3) (v w : V) (hv : v ≠ 0) :
    (univ.filter (fun f : End (F := F) (V := V) => f v = w)).card = Fintype.card F^6 := by
  have h := fiber_card (atPoint (F := F) v) (atPoint_surjective v hv) w
  simpa [atPoint, Module.finrank_linearMap, hd] using h

def twoPoint (v w : V) : End (F := F) (V := V) →ₗ[F] V × V :=
  (atPoint v).prod (atPoint w)

/-- Linear independence stated directly, so no projective convention is hidden. -/
lemma twoPoint_surjective (v w : V)
    (hind : ∀ a b : F, a • v+b • w = 0 → a = 0 ∧ b = 0) :
    Function.Surjective (twoPoint (F := F) v w) := by
  let j : (F × F) →ₗ[F] V :=
    (LinearMap.toSpanSingleton F V v).coprod (LinearMap.toSpanSingleton F V w)
  have hj : Function.Injective j := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot.mpr
    intro a b h
    have hz : j (a-b) = 0 := by rw [map_sub, h, sub_self]
    obtain ⟨h₁,h₂⟩ := hind (a-b).1 (a-b).2 hz
    apply Prod.ext
    · exact sub_eq_zero.mp h₁
    · exact sub_eq_zero.mp h₂
  obtain ⟨k, hk⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  intro p
  let g : (F × F) →ₗ[F] V :=
    (LinearMap.toSpanSingleton F V p.1).coprod (LinearMap.toSpanSingleton F V p.2)
  refine ⟨g.comp k, ?_⟩
  have h₁ := LinearMap.congr_fun hk (1,0)
  have h₂ := LinearMap.congr_fun hk (0,1)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, j, LinearMap.coprod_apply,
    LinearMap.toSpanSingleton_apply, one_smul, zero_smul, add_zero, zero_add] at h₁ h₂
  apply Prod.ext
  · change g (k v) = p.1
    rw [h₁]
    simp [g]
  · change g (k w) = p.2
    rw [h₂]
    simp [g]

lemma two_point_count (hd : finrank F V = 3) (v w a b : V)
    (hind : ∀ s t : F, s • v+t • w = 0 → s = 0 ∧ t = 0) :
    (univ.filter (fun f : End (F := F) (V := V) => f v = a ∧ f w = b)).card = Fintype.card F^3 := by
  have h := fiber_card (twoPoint v w) (twoPoint_surjective v w hind) (a,b)
  simpa [twoPoint, atPoint, Prod.mk.injEq, Module.finrank_linearMap, hd,
    Module.finrank_prod] using h

def compatibility (v : V) (φ : Module.Dual F V) : (V × Module.Dual F V) →ₗ[F] F :=
  (φ.comp (LinearMap.fst F V (Module.Dual F V))) -
    ((LinearMap.applyₗ (R := F) (M₂ := F) v).comp (LinearMap.snd F V (Module.Dual F V)))

lemma compatibility_surjective (v : V) (φ : Module.Dual F V) (hφ : φ ≠ 0) :
    Function.Surjective (compatibility v φ) := by
  have hs : Function.Surjective φ := (LinearMap.surjective_iff_ne_zero).mpr hφ
  intro a
  obtain ⟨w, hw⟩ := hs a
  exact ⟨(w,0), by simp [compatibility, hw]⟩

def paired (v : V) (φ : Module.Dual F V) :
    End (F := F) (V := V) →ₗ[F] (compatibility v φ).ker :=
  LinearMap.codRestrict _
    ((atPoint v).prod (LinearMap.llcomp F V V F φ)) (by intro f; simp [compatibility, atPoint])

lemma paired_surjective (v : V) (φ : Module.Dual F V) (hv : v ≠ 0) (hφ : φ ≠ 0) :
    Function.Surjective (paired v φ) := by
  obtain ⟨α, hα⟩ := Module.Projective.exists_dual_eq_one F hv
  obtain ⟨w₀, hw₀⟩ := ((LinearMap.surjective_iff_ne_zero).mpr hφ) 1
  intro p
  let w := p.val.1
  let ψ := p.val.2
  have hp : φ w = ψ v := by
    have h := p.property
    change φ w-ψ v = 0 at h
    exact sub_eq_zero.mp h
  let f : End (F := F) (V := V) := α.smulRight w + (ψ-(φ w) • α).smulRight w₀
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change f v = w
    simp [f, hα, hp]
  · change φ.comp f = ψ
    ext x
    simp [f, hw₀, LinearMap.comp_apply]
    ring

lemma paired_count (hd : finrank F V = 3) (v w : V) (φ ψ : Module.Dual F V)
    (hv : v ≠ 0) (hφ : φ ≠ 0) (hc : φ w = ψ v) :
    (univ.filter (fun f : End (F := F) (V := V) => f v = w ∧ φ.comp f = ψ)).card = Fintype.card F^4 := by
  let p : (compatibility v φ).ker := ⟨(w,ψ), by simp [compatibility, hc]⟩
  have hr := (compatibility v φ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (compatibility_surjective v φ hφ), finrank_top] at hr
  have hk : finrank F (compatibility v φ).ker = 5 := by
    simp only [Module.finrank_prod, Subspace.dual_finrank_eq, hd, Module.finrank_self] at hr
    omega
  have h := fiber_card (paired v φ) (paired_surjective v φ hv hφ) p
  have he (f : End (F := F) (V := V)) : paired v φ f = p ↔ f v = w ∧ φ.comp f = ψ := by
    rw [Subtype.ext_iff]
    change (f v, φ.comp f) = (w,ψ) ↔ _
    simp only [Prod.mk.injEq]
  simpa only [he, Module.finrank_linearMap, hd, hk, Nat.reduceMul, Nat.reduceSub] using h

/-- Dualization is an equivalence on endomorphism spaces, not just on invertible maps. -/
def dualize : End (F := F) (V := V) →ₗ[F] (Module.Dual F V →ₗ[F] Module.Dual F V) where
  toFun f := f.dualMap
  map_add' := by intro f g; ext φ x; simp
  map_smul' := by intro a f; ext φ x; simp

lemma dualize_injective : Function.Injective (dualize (F := F) (V := V)) := by
  intro f g h
  ext v
  apply (Module.evalEquiv F V).injective
  ext φ
  exact congrArg (fun k : Module.Dual F V →ₗ[F] Module.Dual F V => k φ v) h

def dualizeEquiv : End (F := F) (V := V) ≃ₗ[F] (Module.Dual F V →ₗ[F] Module.Dual F V) := by
  have hd : finrank F (End (F := F) (V := V)) =
      finrank F (Module.Dual F V →ₗ[F] Module.Dual F V) := by
    simp only [Module.finrank_linearMap, Module.finrank_self, mul_one]
  refine LinearEquiv.ofBijective (dualize (F := F) (V := V)) ⟨dualize_injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := F)
    (V := End (F := F) (V := V)) (V₂ := Module.Dual F V →ₗ[F] Module.Dual F V)
    (f := dualize (F := F) (V := V)) hd).mp
  exact dualize_injective

lemma dual_point_count (hd : finrank F V = 3) (φ ψ : Module.Dual F V) (hφ : φ ≠ 0) :
    (univ.filter (fun f : End (F := F) (V := V) => φ.comp f = ψ)).card = Fintype.card F^6 := by
  letI := endFintype (F := F) (V := Module.Dual F V)
  let e := dualizeEquiv (F := F) (V := V)
  have h := point_count (F := F) (by simpa only [Subspace.dual_finrank_eq] using hd) φ ψ hφ
  have hc : (univ.filter (fun f : End (F := F) (V := V) => φ.comp f = ψ)).card =
      (univ.filter (fun g : Module.Dual F V →ₗ[F] Module.Dual F V => g φ = ψ)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (e.toEquiv.subtypeEquiv (fun f => by rfl))
  rw [hc]
  convert h using 1 <;> congr 1
  ext g
  simp only [mem_filter, mem_univ, true_and]

lemma dual_two_point_count (hd : finrank F V = 3) (φ ψ α β : Module.Dual F V)
    (hind : ∀ s t : F, s • φ+t • ψ = 0 → s = 0 ∧ t = 0) :
    (univ.filter (fun f : End (F := F) (V := V) => φ.comp f = α ∧ ψ.comp f = β)).card =
      Fintype.card F^3 := by
  letI := endFintype (F := F) (V := Module.Dual F V)
  let e := dualizeEquiv (F := F) (V := V)
  have h := two_point_count (F := F) (by simpa only [Subspace.dual_finrank_eq] using hd) φ ψ α β hind
  have hc : (univ.filter (fun f : End (F := F) (V := V) => φ.comp f = α ∧ ψ.comp f = β)).card =
      (univ.filter (fun g : Module.Dual F V →ₗ[F] Module.Dual F V => g φ = α ∧ g ψ = β)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (e.toEquiv.subtypeEquiv (fun f => by rfl))
  rw [hc]
  convert h using 1 <;> congr 1
  ext g
  simp only [mem_filter, mem_univ, true_and]

#print axioms dual_point_count
#print axioms dual_two_point_count
#print axioms fiber_card
#print axioms point_count
#print axioms two_point_count
#print axioms paired_count
end Erdos714LinearBlocks
