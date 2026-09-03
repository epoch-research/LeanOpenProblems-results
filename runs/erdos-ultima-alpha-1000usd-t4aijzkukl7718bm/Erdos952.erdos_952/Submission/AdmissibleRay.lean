import Submission.GraphReduction

/-! A compactness reduction to a bounded-step path avoiding a residue class at every prime. -/

namespace Erdos952Investigation
namespace AdmissibleRay

set_option maxHeartbeats 0

def latticeGraph (C : ℤ) : SimpleGraph GaussianInt where
  Adj z w := z ≠ w ∧ (w - z).norm < C
  symm := by
    intro z w h
    exact ⟨h.1.symm, by rw [norm_sub_comm]; exact h.2⟩
  loopless := by intro z h; exact h.1 rfl

lemma latticeGraph_finite_neighbors (C : ℤ) (z : GaussianInt) :
    ((latticeGraph C).neighborSet z).Finite := by
  have hinj : Function.Injective (fun w : GaussianInt => w - z) := by
    intro w v h
    simpa using h
  apply ((norm_sublevel_finite C).preimage (f := fun w => w - z) hinj.injOn).subset
  intro w hw
  exact le_of_lt hw.2

noncomputable instance (C : ℤ) : (latticeGraph C).LocallyFinite :=
  fun z => (latticeGraph_finite_neighbors C z).fintype

def Good (p : ℕ) (a b : ZMod p) (z : GaussianInt) : Prop :=
  (a + (z.re : ZMod p)) ^ 2 + (b + (z.im : ZMod p)) ^ 2 ≠ 0

def Prefix (C : ℤ) (n : ℕ) :=
  {f : RayReduction.Prefix (latticeGraph C) 0 n //
    ∀ p ≤ n, p.Prime → ∃ a b : ZMod p, ∀ i, Good p a b (f.val i)}

def restrict (C : ℤ) {i j : ℕ} (hij : i ≤ j) (f : Prefix C j) : Prefix C i :=
  ⟨RayReduction.restrict (latticeGraph C) 0 hij f.val, by
    intro p hp hpprime
    obtain ⟨a, b, hab⟩ := f.property p (hp.trans hij) hpprime
    exact ⟨a, b, fun k => hab (Fin.castLE (Nat.succ_le_succ hij) k)⟩⟩

lemma restrict_refl (C : ℤ) {i : ℕ} (f : Prefix C i) : restrict C le_rfl f = f := by
  apply Subtype.ext
  exact RayReduction.restrict_refl _ _ _

lemma restrict_trans (C : ℤ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (f : Prefix C k) : restrict C hij (restrict C hjk f) = restrict C (hij.trans hjk) f := by
  apply Subtype.ext
  exact RayReduction.restrict_trans _ _ hij hjk _

instance (C : ℤ) : Subsingleton (Prefix C 0) :=
  inferInstanceAs (Subsingleton (Subtype _))

lemma finite_extension_fiber (C : ℤ) (n : ℕ) (a : Prefix C n) :
    {b : Prefix C (n + 1) | restrict C (Nat.le_succ n) b = a}.Finite := by
  let T := {b : Prefix C (n + 1) // restrict C (Nat.le_succ n) b = a}
  let U := {b : RayReduction.Prefix (latticeGraph C) 0 (n + 1) //
    RayReduction.restrict (latticeGraph C) 0 (Nat.le_succ n) b = a.val}
  let f : T → U := fun b => ⟨b.val.val, congrArg Subtype.val b.property⟩
  have hinj : Function.Injective f := by
    intro b c h
    exact Subtype.ext (Subtype.ext (congrArg (fun u : U => u.val) h))
  have : Finite U := RayReduction.finite_extension_fiber (latticeGraph C) 0 n a.val
  exact Finite.of_injective f hinj

lemma finite_choice_prefix {A : Type*} [Finite A] (P : ℕ → A → Prop)
    (h : ∀ n, ∃ a, ∀ i ≤ n, P i a) : ∃ a, ∀ i, P i a := by
  classical
  letI := Fintype.ofFinite A
  by_contra! hn
  choose f hf using hn
  obtain ⟨a, ha⟩ := h (Finset.univ.sup f)
  exact hf a (ha (f a) (Finset.le_sup (Finset.mem_univ a)))

lemma good_of_large_prime {z w : GaussianInt} {p : ℕ} (hz : Prime z)
    (hp : p.Prime) (hnorm : (p : ℤ)^2 < z.norm) :
    Good p (w.re : ZMod p) (w.im : ZMod p) (z - w) := by
  intro hn
  have hn' : (z.norm : ZMod p) = 0 := by
    simpa [Good, gaussian_norm_sq, Int.cast_add, Int.cast_pow] using hn
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z.norm p).mp hn'
  have := prime_norm_divisor_bound hz hp hd
  omega

lemma prefixes_of_prime_walk (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    ∀ n, Nonempty (Prefix C n) := by
  intro n
  obtain ⟨N, hN⟩ := injective_escapes_norm x hx ((n : ℤ)^2)
  let f : Fin (n + 1) → GaussianInt := fun i => x (N + i.val) - x N
  have hf0 : f 0 = 0 := by simp [f]
  have hfi : Function.Injective f := by
    intro i j hij
    have he : x (N + i.val) = x (N + j.val) := by simpa [f] using hij
    have := hx he
    exact Fin.ext (by omega)
  have hstep (i : Fin n) : (latticeGraph C).Adj (f i.castSucc) (f i.succ) := by
    refine ⟨fun he => ?_, ?_⟩
    · have := hfi he
      have := congrArg Fin.val this
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    · have he : f i.succ - f i.castSucc = x (N + i.val + 1) - x (N + i.val) := by
        simp [f, Nat.add_assoc]
      rw [he]
      exact (h (N + i.val)).2
  refine ⟨⟨⟨f, hf0, hfi, hstep⟩, ?_⟩⟩
  intro p hpn hp
  refine ⟨(x N).re, (x N).im, fun i => ?_⟩
  apply good_of_large_prime (h (N + i.val)).1 hp
  have hpcast : (p : ℤ) ≤ n := by exact_mod_cast hpn
  have hp0 : 0 ≤ (p : ℤ) := Int.natCast_nonneg p
  have hn0 : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  have hh := hN (N + i.val) (Nat.le_add_right _ _)
  nlinarith

lemma ray_of_prefixes (C : ℤ) (h : ∀ n, Nonempty (Prefix C n)) :
    ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
      (∀ n, (y (n + 1) - y n).norm < C) ∧
      ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n) := by
  classical
  letI (n : ℕ) : Nonempty (Prefix C n) := h n
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (restrict C) (fun {_} a => restrict_refl C a)
    (fun {_ _ _} hij hjk a => restrict_trans C hij hjk a) (finite_extension_fiber C)
  let y : ℕ → GaussianInt := fun n => (f n).val.val (Fin.last n)
  have hy {i j : ℕ} (hij : i ≤ j) : y i = (f j).val.val ⟨i, by omega⟩ :=
    (congrArg (fun a : Prefix C i => a.val.val (Fin.last i)) (hf hij)).symm
  refine ⟨y, (f 0).val.property.1, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hy (Nat.le_add_right i j), hy (Nat.le_add_left j i)] at hij
    exact congrArg Fin.val ((f (i + j)).val.property.2.1 hij)
  · intro n
    rw [hy (Nat.le_succ n), hy (le_refl (n + 1))]
    exact ((f (n + 1)).val.property.2.2 (Fin.last n)).2
  · intro p hp
    letI : NeZero p := ⟨hp.ne_zero⟩
    have hfinite : ∀ k, ∃ ab : ZMod p × ZMod p, ∀ i ≤ k, Good p ab.1 ab.2 (y i) := by
      intro k
      obtain ⟨a, b, hab⟩ := (f (max p k)).property p (le_max_left _ _) hp
      refine ⟨(a, b), fun i hi => ?_⟩
      rw [hy (hi.trans (le_max_right _ _))]
      exact hab _
    obtain ⟨⟨a, b⟩, hab⟩ := finite_choice_prefix (fun n (ab : ZMod p × ZMod p) => Good p ab.1 ab.2 (y n)) hfinite
    exact ⟨a, b, hab⟩

theorem prime_walk_yields_admissible_ray (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) :
    ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
      (∀ n, (y (n + 1) - y n).norm < C) ∧
      ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n) :=
  ray_of_prefixes C (prefixes_of_prime_walk x C hx h)

#print axioms prime_walk_yields_admissible_ray

end AdmissibleRay
end Erdos952Investigation
