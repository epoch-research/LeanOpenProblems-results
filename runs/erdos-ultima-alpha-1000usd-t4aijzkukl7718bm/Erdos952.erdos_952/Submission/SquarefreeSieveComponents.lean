import Submission.ExactSievePeriod

/-! Squarefree-period certificates for finite Gaussian sieves. These replace
the factorial cell by the exact rational primorial period. They do not prove
that the cutoff search terminates for an arbitrary jump bound. -/
namespace Erdos952Investigation
namespace SquarefreeSieveComponents
open FiniteSieveReduction ExactSievePeriod

set_option maxHeartbeats 0

def IsPeriod (N : ℕ) (d : GaussianInt) : Prop :=
  ((primorial N) : ℤ) ∣ d.re ∧ ((primorial N) : ℤ) ∣ d.im

def residue (N : ℕ) (z : GaussianInt) : ZMod (primorial N) × ZMod (primorial N) :=
  (z.re, z.im)

lemma period_of_same_residue {N : ℕ} {z w : GaussianInt}
    (h : residue N z = residue N w) : IsPeriod N (w - z) := by
  have hr := congrArg Prod.fst h
  have hi := congrArg Prod.snd h
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (primorial N)).mp
    change ((w.re - z.re : ℤ) : ZMod (primorial N)) = 0
    change (z.re : ZMod (primorial N)) = w.re at hr
    push_cast
    rw [hr, sub_self]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (primorial N)).mp
    change ((w.im - z.im : ℤ) : ZMod (primorial N)) = 0
    change (z.im : ZMod (primorial N)) = w.im at hi
    push_cast
    rw [hi, sub_self]

lemma period_nat_mul {N : ℕ} {d : GaussianInt} (hd : IsPeriod N d) (n : ℕ) :
    IsPeriod N ((n : GaussianInt) * d) := by
  constructor
  · simpa using dvd_mul_of_dvd_right hd.1 (n : ℤ)
  · simpa using dvd_mul_of_dvd_right hd.2 (n : ℤ)

lemma allowed_add_period {N : ℕ} {z d : GaussianInt} (hz : Allowed N z)
    (hd : IsPeriod N d) : Allowed N (z + d) := by
  intro p hpN hp hdiv
  have hpF : p ∣ (primorial N) := prime_dvd_primorial hp hpN
  have hpF' : (p : ℤ) ∣ (primorial N) := by exact_mod_cast hpF
  have hr : (d.re : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hpF'.trans hd.1)
  have hi : (d.im : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hpF'.trans hd.2)
  have hn : ((z + d).norm : ZMod p) = (z.norm : ZMod p) := by
    simp [gaussian_norm_sq, hr, hi]
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
  rw [hn] at he
  exact hz p hpN hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he)

lemma reachable_add_period {C : ℤ} {N : ℕ} {z w d : GaussianInt}
    (h : (sieveGraph C N).Reachable z w) (hd : IsPeriod N d) :
    (sieveGraph C N).Reachable (z + d) (w + d) := by
  let f : sieveGraph C N →g sieveGraph C N :=
    ⟨fun z => z + d, fun {z w} h =>
      ⟨allowed_add_period h.1 hd, allowed_add_period h.2.1 hd,
        fun he => h.2.2.1 (add_right_cancel he), by
          simpa only [add_sub_add_right_eq_sub] using h.2.2.2⟩⟩
  exact h.map f

lemma reachable_multiples_of_period {C : ℤ} {N : ℕ} {z w : GaussianInt}
    (h : (sieveGraph C N).Reachable z w) (hd : IsPeriod N (w - z)) :
    ∀ n : ℕ, (sieveGraph C N).Reachable z (z + (n : GaussianInt)*(w - z)) := by
  intro n
  induction n with
  | zero => simpa using (SimpleGraph.Reachable.refl z : (sieveGraph C N).Reachable z z)
  | succ n ih =>
    have ht := reachable_add_period h (period_nat_mul hd n)
    have he : w + (n : GaussianInt)*(w - z) = z + ((n + 1 : ℕ) : GaussianInt)*(w - z) := by
      push_cast
      ring
    rw [he] at ht
    exact ih.trans ht

/-- Repetition of a residue in one connected component gives an unbounded
translation orbit inside that same component. -/
lemma infinite_component_of_repeated_residue {C : ℤ} {N : ℕ} {z u v : GaussianInt}
    (hu : (sieveGraph C N).Reachable z u) (hv : (sieveGraph C N).Reachable z v)
    (hne : u ≠ v) (hres : residue N u = residue N v) :
    {w | (sieveGraph C N).Reachable z w}.Infinite := by
  have huv := hu.symm.trans hv
  have hd := period_of_same_residue hres
  have hdne : v - u ≠ 0 := sub_ne_zero.mpr hne.symm
  have hinj : Function.Injective (fun n : ℕ => u + (n : GaussianInt)*(v - u)) := by
    intro i j he
    have ht := mul_right_cancel₀ hdne (add_left_cancel he)
    exact Nat.cast_injective ht
  apply (Set.infinite_range_of_injective hinj).mono
  rintro w ⟨n, rfl⟩
  exact hu.trans (reachable_multiples_of_period huv hd n)

/-- A finite component contains at most one representative of each residue. -/
theorem component_finite_iff_residue_injective (C : ℤ) (N : ℕ) (z : GaussianInt) :
    {w | (sieveGraph C N).Reachable z w}.Finite ↔
      Set.InjOn (residue N) {w | (sieveGraph C N).Reachable z w} := by
  letI : NeZero (primorial N) := ⟨(primorial_pos N).ne'⟩
  constructor
  · intro hf u hu v hv he
    by_contra hne
    exact infinite_component_of_repeated_residue hu hv hne he hf
  · intro hinj
    let f : {w | (sieveGraph C N).Reachable z w} → ZMod (primorial N) × ZMod (primorial N) :=
      fun w => residue N w.val
    have hf : Function.Injective f := by
      intro u v he
      exact Subtype.ext (hinj u.property v.property he)
    haveI : Finite {w | (sieveGraph C N).Reachable z w} := Finite.of_injective f hf
    exact Set.toFinite _

/-- Consequently every finite component has an explicit cardinality bound. -/
theorem finite_component_card_le (C : ℤ) (N : ℕ) (z : GaussianInt)
    (hf : {w | (sieveGraph C N).Reachable z w}.Finite) :
    Nat.card {w | (sieveGraph C N).Reachable z w} ≤ (primorial N)^2 := by
  letI : NeZero (primorial N) := ⟨(primorial_pos N).ne'⟩
  have hinj := (component_finite_iff_residue_injective C N z).mp hf
  let f : {w | (sieveGraph C N).Reachable z w} → ZMod (primorial N) × ZMod (primorial N) :=
    fun w => residue N w.val
  have hfi : Function.Injective f := by
    intro u v he
    exact Subtype.ext (hinj u.property v.property he)
  have hc := Nat.card_le_card_of_injective f hfi
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card, pow_two] using hc

lemma prefix_reachable {V : Type*} {G : SimpleGraph V} {z : V} {n : ℕ}
    (f : RayReduction.Prefix G z n) (i : Fin (n + 1)) : G.Reachable z (f.val i) := by
  induction i using Fin.induction with
  | zero => rw [f.property.1]
  | succ i ih => exact ih.trans (f.property.2.2 i).reachable

lemma finite_prefix {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] (z : V) (n : ℕ) :
    Finite (RayReduction.Prefix G z n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    letI : Finite (RayReduction.Prefix G z n) := ih
    let r := RayReduction.restrict G z (Nat.le_succ n)
    let T := Σ a : RayReduction.Prefix G z n,
      {b : RayReduction.Prefix G z (n + 1) // r b = a}
    letI (a : RayReduction.Prefix G z n) :
        Finite {b : RayReduction.Prefix G z (n + 1) // r b = a} :=
      RayReduction.finite_extension_fiber G z n a
    let f : RayReduction.Prefix G z (n + 1) → T := fun b => ⟨r b, ⟨b, rfl⟩⟩
    have hf : Function.Injective f := by
      intro b c he
      exact congrArg (fun t : T => t.2.val) he
    exact Finite.of_injective f hf

/-- For a fixed cutoff, an infinite component is equivalent to the existence
of one finite simple path of this explicitly bounded length. -/
theorem infinite_component_iff_long_prefix (C : ℤ) (N : ℕ) (z : GaussianInt) :
    {w | (sieveGraph C N).Reachable z w}.Infinite ↔
      Nonempty (RayReduction.Prefix (sieveGraph C N) z ((primorial N)^2)) := by
  constructor
  · intro h
    exact RayReduction.prefixes_of_infinite_component (sieveGraph C N) z h _
  · rintro ⟨f⟩ hf
    let T := {w | (sieveGraph C N).Reachable z w}
    letI : Finite T := hf
    let g : Fin ((primorial N)^2 + 1) → T := fun i => ⟨f.val i, prefix_reachable f i⟩
    have hg : Function.Injective g := by
      intro i j he
      exact f.property.2.1 (congrArg Subtype.val he)
    have hl := Nat.card_le_card_of_injective g hg
    have hu := finite_component_card_le C N z hf
    simp only [Nat.card_fin] at hl
    change (primorial N)^2 + 1 ≤ Nat.card {w | (sieveGraph C N).Reachable z w} at hl
    omega

def representative (N : ℕ) (r : ZMod (primorial N) × ZMod (primorial N)) : GaussianInt :=
  ⟨r.1.val, r.2.val⟩

lemma residue_representative (N : ℕ) (r : ZMod (primorial N) × ZMod (primorial N)) :
    residue N (representative N r) = r := by
  letI : NeZero (primorial N) := ⟨(primorial_pos N).ne'⟩
  simp [residue, representative]

lemma infinite_component_add_period {C : ℤ} {N : ℕ} {z d : GaussianInt}
    (h : {w | (sieveGraph C N).Reachable z w}.Infinite) (hd : IsPeriod N d) :
    {w | (sieveGraph C N).Reachable (z + d) w}.Infinite := by
  have hinj : Function.Injective (fun w : GaussianInt => w + d) := by
    intro u v he
    exact add_right_cancel he
  apply (h.image hinj.injOn).mono
  rintro w ⟨v, hv, rfl⟩
  exact reachable_add_period hv hd

/-- One only needs to test starting vertices in one period cell, and one only
needs to test prefixes of one explicit finite length. -/
theorem sieve_ray_iff_fundamental_cell_prefix (C : ℤ) (N : ℕ) :
    HasSieveRay C N ↔ ∃ r : ZMod (primorial N) × ZMod (primorial N),
      Nonempty (RayReduction.Prefix (sieveGraph C N) (representative N r) ((primorial N)^2)) := by
  rw [sieve_ray_iff_infinite_component]
  constructor
  · rintro ⟨z, hz⟩
    let w := representative N (residue N z)
    have hr : residue N z = residue N w := (residue_representative N (residue N z)).symm
    have hd := period_of_same_residue hr
    have hw := infinite_component_add_period hz hd
    have he : z + (w - z) = w := by abel
    rw [he] at hw
    exact ⟨residue N z, (infinite_component_iff_long_prefix C N w).mp hw⟩
  · rintro ⟨r, hr⟩
    exact ⟨representative N r, (infinite_component_iff_long_prefix C N _).mpr hr⟩

/-- The remaining universal sieve hypothesis can therefore be stated entirely
using bounded-length prefixes and finite sets of starting residues. This is a
reformulation, not a proof that a successful cutoff exists. -/
theorem no_admissible_ray_iff_bounded_prefix_obstruction (C : ℤ) :
    (¬ HasAdmissibleRay C) ↔ ∃ N : ℕ,
      ∀ r : ZMod (primorial N) × ZMod (primorial N),
        IsEmpty (RayReduction.Prefix (sieveGraph C N) (representative N r) ((primorial N)^2)) := by
  rw [admissible_ray_iff_finite_sieve_rays]
  simp only [not_forall, sieve_ray_iff_fundamental_cell_prefix, not_exists, not_nonempty_iff]

#print axioms finite_prefix
#print axioms sieve_ray_iff_fundamental_cell_prefix
#print axioms no_admissible_ray_iff_bounded_prefix_obstruction

#print axioms component_finite_iff_residue_injective
#print axioms finite_component_card_le
#print axioms infinite_component_iff_long_prefix

end SquarefreeSieveComponents
end Erdos952Investigation
