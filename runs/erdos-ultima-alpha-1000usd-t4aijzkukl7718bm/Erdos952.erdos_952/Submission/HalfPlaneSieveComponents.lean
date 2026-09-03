import Submission.ExceptionSieveReduction

/-! Repeated residues in a half-plane sieve component can be pumped in the
nonnegative projection direction. Finite components therefore have the same
residue-cardinality bound as in the unrestricted periodic graph. -/
namespace Erdos952Investigation
namespace HalfPlaneSieveComponents
open FiniteSieveReduction PeriodicSieveComponents
set_option maxHeartbeats 0

def halfGraph (C : ℤ) (N : ℕ) (l : GaussianInt →+ ℤ) (R : ℤ) :
    SimpleGraph GaussianInt where
  Adj z w := (sieveGraph C N).Adj z w ∧ R ≤ l z ∧ R ≤ l w
  symm := by intro z w h; exact ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := by intro z h; exact h.1.2.2.1 rfl

lemma projection_nat_mul (l : GaussianInt →+ ℤ) (n : ℕ) (d : GaussianInt) :
    l ((n : GaussianInt)*d) = (n : ℤ)*l d := by
  rw [← nsmul_eq_mul,map_nsmul,nsmul_eq_mul]

lemma reachable_add_period {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ} {R : ℤ}
    {z w d : GaussianInt} (h : (halfGraph C N l R).Reachable z w)
    (hd : IsPeriod N d) (hld : 0 ≤ l d) :
    (halfGraph C N l R).Reachable (z+d) (w+d) := by
  let f : halfGraph C N l R →g halfGraph C N l R :=
    ⟨fun z => z+d,fun {z w} h =>
      ⟨⟨allowed_add_period h.1.1 hd,allowed_add_period h.1.2.1 hd,
          fun he => h.1.2.2.1 (add_right_cancel he),by
            simpa only [add_sub_add_right_eq_sub] using h.1.2.2.2⟩,
        by rw [map_add]; exact le_add_of_le_of_nonneg h.2.1 hld,
        by rw [map_add]; exact le_add_of_le_of_nonneg h.2.2 hld⟩⟩
  exact h.map f

lemma reachable_multiples_of_period {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ}
    {R : ℤ} {z w : GaussianInt} (h : (halfGraph C N l R).Reachable z w)
    (hd : IsPeriod N (w-z)) (hl : l z ≤ l w) :
    ∀ n : ℕ, (halfGraph C N l R).Reachable z (z+(n : GaussianInt)*(w-z)) := by
  intro n
  induction n with
  | zero => simpa using (SimpleGraph.Reachable.refl z : (halfGraph C N l R).Reachable z z)
  | succ n ih =>
    have hld : 0 ≤ l ((n : GaussianInt)*(w-z)) := by
      rw [projection_nat_mul,map_sub]
      exact mul_nonneg (Int.natCast_nonneg _) (sub_nonneg.mpr hl)
    have ht := reachable_add_period h (period_nat_mul hd n) hld
    have he : w+(n : GaussianInt)*(w-z) = z+((n+1 : ℕ) : GaussianInt)*(w-z) := by
      push_cast; ring
    rw [he] at ht
    exact ih.trans ht

lemma infinite_component_of_repeated_residue_ordered {C : ℤ} {N : ℕ}
    {l : GaussianInt →+ ℤ} {R : ℤ} {z u v : GaussianInt}
    (hu : (halfGraph C N l R).Reachable z u)
    (hv : (halfGraph C N l R).Reachable z v)
    (hne : u ≠ v) (hres : residue N u = residue N v) (hl : l u ≤ l v) :
    {w | (halfGraph C N l R).Reachable z w}.Infinite := by
  have huv := hu.symm.trans hv
  have hd := period_of_same_residue hres
  have hdne : v-u ≠ 0 := sub_ne_zero.mpr hne.symm
  have hinj : Function.Injective (fun n : ℕ => u+(n : GaussianInt)*(v-u)) := by
    intro i j he
    exact Nat.cast_injective (mul_right_cancel₀ hdne (add_left_cancel he))
  apply (Set.infinite_range_of_injective hinj).mono
  rintro w ⟨n,rfl⟩
  exact hu.trans (reachable_multiples_of_period huv hd hl n)

lemma infinite_component_of_repeated_residue {C : ℤ} {N : ℕ}
    {l : GaussianInt →+ ℤ} {R : ℤ} {z u v : GaussianInt}
    (hu : (halfGraph C N l R).Reachable z u)
    (hv : (halfGraph C N l R).Reachable z v)
    (hne : u ≠ v) (hres : residue N u = residue N v) :
    {w | (halfGraph C N l R).Reachable z w}.Infinite := by
  rcases le_total (l u) (l v) with hl | hl
  · exact infinite_component_of_repeated_residue_ordered hu hv hne hres hl
  · exact infinite_component_of_repeated_residue_ordered hv hu hne.symm hres.symm hl

theorem component_finite_iff_residue_injective (C : ℤ) (N : ℕ)
    (l : GaussianInt →+ ℤ) (R : ℤ) (z : GaussianInt) :
    {w | (halfGraph C N l R).Reachable z w}.Finite ↔
      Set.InjOn (residue N) {w | (halfGraph C N l R).Reachable z w} := by
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  constructor
  · intro hf u hu v hv he
    by_contra hne
    exact infinite_component_of_repeated_residue hu hv hne he hf
  · intro hinj
    let f : {w | (halfGraph C N l R).Reachable z w} →
        ZMod N.factorial × ZMod N.factorial := fun w => residue N w.val
    have hfi : Function.Injective f := by
      intro u v he
      exact Subtype.ext (hinj u.property v.property he)
    haveI : Finite {w | (halfGraph C N l R).Reachable z w} := Finite.of_injective f hfi
    exact Set.toFinite _

theorem finite_component_card_le (C : ℤ) (N : ℕ) (l : GaussianInt →+ ℤ)
    (R : ℤ) (z : GaussianInt)
    (hf : {w | (halfGraph C N l R).Reachable z w}.Finite) :
    Nat.card {w | (halfGraph C N l R).Reachable z w} ≤ N.factorial^2 := by
  letI : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩
  have hinj := (component_finite_iff_residue_injective C N l R z).mp hf
  let f : {w | (halfGraph C N l R).Reachable z w} →
      ZMod N.factorial × ZMod N.factorial := fun w => residue N w.val
  have hfi : Function.Injective f := by
    intro u v he
    exact Subtype.ext (hinj u.property v.property he)
  have hc := Nat.card_le_card_of_injective f hfi
  simpa [Nat.card_eq_fintype_card,Fintype.card_prod,ZMod.card,pow_two] using hc

lemma walk_projection_le {G : SimpleGraph GaussianInt} (l : GaussianInt →+ ℤ)
    (D : ℤ) (hD : ∀ {u v}, G.Adj u v → l v-l u ≤ D)
    {z w : GaussianInt} (p : G.Walk z w) : l w-l z ≤ (p.length : ℤ)*D := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have hh := hD huv
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma finite_component_projection_bound {C : ℤ} {N : ℕ} {l : GaussianInt →+ ℤ}
    {R D : ℤ} (hD : 0 ≤ D)
    (hs : ∀ {u v}, (sieveGraph C N).Adj u v → l v-l u ≤ D)
    {z w : GaussianInt} (hf : {v | (halfGraph C N l R).Reachable z v}.Finite)
    (hw : (halfGraph C N l R).Reachable z w) :
    l w ≤ l z+(N.factorial^2 : ℕ)*D := by
  classical
  obtain ⟨p,hp⟩ := hw.exists_isPath
  let S := {v | (halfGraph C N l R).Reachable z v}
  letI : Finite S := hf
  let f : Fin (p.length+1) → S := fun i =>
    ⟨p.getVert i.val,(p.takeUntil _ (p.getVert_mem_support i.val)).reachable⟩
  have hfi : Function.Injective f := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) (congrArg Subtype.val he)
  have hcard := Nat.card_le_card_of_injective f hfi
  have hbound := finite_component_card_le C N l R z hf
  simp only [Nat.card_fin] at hcard
  change p.length+1 ≤ Nat.card {v | (halfGraph C N l R).Reachable z v} at hcard
  have hlen : p.length ≤ N.factorial^2 := by omega
  have hlen' : (p.length : ℤ) ≤ (N.factorial^2 : ℕ) := by exact_mod_cast hlen
  have hproj := walk_projection_le (G := halfGraph C N l R) l D (fun {_ _} h => hs h.1) p
  have hmul := mul_le_mul_of_nonneg_right hlen' hD
  omega

#print axioms component_finite_iff_residue_injective
#print axioms finite_component_projection_bound
end HalfPlaneSieveComponents
end Erdos952Investigation
