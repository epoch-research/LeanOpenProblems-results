import FormalConjectures.Util.ProblemImports
open Nat
open scoped BigOperators


section GeneralProd
variable {ι R : Type*} [CommRing R]

theorem prod_one_add_sub_one (d : R) (f : ι → R) (s : Finset ι)
    (hf : ∀ t ∈ s, d ∣ f t) : d ∣ (∏ t ∈ s, (1 + f t) - 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hP : d ∣ (∏ t ∈ s, (1 + f t) - 1) :=
      ih (fun t ht => hf t (Finset.mem_insert_of_mem ht))
    have hfa : d ∣ f a := hf a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    have key : (1 + f a) * (∏ t ∈ s, (1 + f t)) - 1
        = (∏ t ∈ s, (1 + f t) - 1) + f a * (∏ t ∈ s, (1 + f t)) := by ring
    rw [key]; exact dvd_add hP (Dvd.dvd.mul_right hfa _)

theorem prod_one_add_sub_linear (d : R) (f : ι → R) (s : Finset ι)
    (hf : ∀ t ∈ s, d ∣ f t) : d^2 ∣ (∏ t ∈ s, (1 + f t) - 1 - ∑ t ∈ s, f t) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hsub : ∀ t ∈ s, d ∣ f t := fun t ht => hf t (Finset.mem_insert_of_mem ht)
    have hP : d^2 ∣ (∏ t ∈ s, (1 + f t) - 1 - ∑ t ∈ s, f t) := ih hsub
    have hfa : d ∣ f a := hf a (Finset.mem_insert_self a s)
    have hP1 : d ∣ (∏ t ∈ s, (1 + f t) - 1) := prod_one_add_sub_one d f s hsub
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have key : (1 + f a) * (∏ t ∈ s, (1 + f t)) - 1 - (f a + ∑ t ∈ s, f t)
        = (∏ t ∈ s, (1 + f t) - 1 - ∑ t ∈ s, f t) + f a * (∏ t ∈ s, (1 + f t) - 1) := by ring
    rw [key]
    exact dvd_add hP (by rw [pow_two]; exact mul_dvd_mul hfa hP1)

theorem prod_diff_dvd (d : R) (f g : ι → R) (s : Finset ι)
    (hf : ∀ t ∈ s, d ∣ f t) (hg : ∀ t ∈ s, d ∣ g t) (hfg : ∀ t ∈ s, d^2 ∣ (f t - g t)) :
    d^2 ∣ (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t)) := by
  have hPf := prod_one_add_sub_linear d f s hf
  have hPg := prod_one_add_sub_linear d g s hg
  have hsum : d^2 ∣ ∑ t ∈ s, (f t - g t) := Finset.dvd_sum hfg
  have e : (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t))
      = (∏ t ∈ s, (1 + f t) - 1 - ∑ t ∈ s, f t)
        - (∏ t ∈ s, (1 + g t) - 1 - ∑ t ∈ s, g t)
        + ∑ t ∈ s, (f t - g t) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]; exact dvd_add (dvd_sub hPf hPg) hsum

theorem prod_cmp (d : R) (f g : ι → R) (s : Finset ι)
    (hf : ∀ t ∈ s, d ∣ f t) (hg : ∀ t ∈ s, d ∣ g t) (hfg : ∀ t ∈ s, d^2 ∣ (f t - g t)) :
    d^3 ∣ (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t) - ∑ t ∈ s, (f t - g t)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hfs : ∀ t ∈ s, d ∣ f t := fun t ht => hf t (Finset.mem_insert_of_mem ht)
    have hgs : ∀ t ∈ s, d ∣ g t := fun t ht => hg t (Finset.mem_insert_of_mem ht)
    have hfgs : ∀ t ∈ s, d^2 ∣ (f t - g t) := fun t ht => hfg t (Finset.mem_insert_of_mem ht)
    have hE : d^3 ∣ (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t) - ∑ t ∈ s, (f t - g t)) :=
      ih hfs hgs hfgs
    have hfa : d ∣ f a := hf a (Finset.mem_insert_self a s)
    have hga : d ∣ g a := hg a (Finset.mem_insert_self a s)
    have hfga : d^2 ∣ (f a - g a) := hfg a (Finset.mem_insert_self a s)
    have hP1f : d ∣ (∏ t ∈ s, (1 + f t) - 1) := prod_one_add_sub_one d f s hfs
    have hPfg : d^2 ∣ (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t)) :=
      prod_diff_dvd d f g s hfs hgs hfgs
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have key : (1 + f a) * (∏ t ∈ s, (1 + f t)) - (1 + g a) * (∏ t ∈ s, (1 + g t))
          - (f a - g a + ∑ t ∈ s, (f t - g t))
        = (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t) - ∑ t ∈ s, (f t - g t))
          + (f a - g a) * (∏ t ∈ s, (1 + f t) - 1)
          + g a * (∏ t ∈ s, (1 + f t) - ∏ t ∈ s, (1 + g t)) := by ring
    rw [key]
    refine dvd_add (dvd_add hE ?_) ?_
    · have : d^3 = d^2 * d := by ring
      rw [this]; exact mul_dvd_mul hfga hP1f
    · have : d^3 = d * d^2 := by ring
      rw [this]; exact mul_dvd_mul hga hPfg

theorem inv_add_eq {a b s : R} (ha : IsUnit a) (hb : IsUnit b) (hs : a + b = s) :
    Ring.inverse a + Ring.inverse b = s * Ring.inverse (a * b) := by
  have hab : IsUnit (a*b) := ha.mul hb
  have h : (Ring.inverse a + Ring.inverse b) * (a*b) = (s * Ring.inverse (a*b)) * (a*b) := by
    rw [add_mul, mul_assoc s, Ring.inverse_mul_cancel _ hab, mul_one]
    rw [show Ring.inverse a * (a*b) = (Ring.inverse a * a) * b by ring,
        Ring.inverse_mul_cancel a ha, one_mul]
    rw [show Ring.inverse b * (a*b) = (Ring.inverse b * b) * a by ring,
        Ring.inverse_mul_cancel b hb, one_mul]
    rw [← hs]; ring
  exact hab.mul_right_cancel h

theorem map_ring_inverse {R S F : Type*} [CommRing R] [CommRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) {u : R} (hu : IsUnit u) :
    f (Ring.inverse u) = Ring.inverse (f u) := by
  have hfu : IsUnit (f u) := hu.map f
  have h1 : f (Ring.inverse u) * f u = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  have h2 : Ring.inverse (f u) * f u = 1 := Ring.inverse_mul_cancel _ hfu
  exact hfu.mul_right_cancel (by rw [h1, h2])

theorem ring_inv_inv {R : Type*} [CommRing R] {u : R} (hu : IsUnit u) :
    Ring.inverse (Ring.inverse u) = u := by
  obtain ⟨v, rfl⟩ := hu
  rw [Ring.inverse_unit, Ring.inverse_unit, inv_inv]

/-- Closed form for the sum of squares over `range N` in ℤ. -/
theorem sum_sq_range (N : ℕ) :
    6 * (∑ i ∈ Finset.range N, (i : ℤ)^2) = ((N : ℤ) - 1) * N * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast; ring

end GeneralProd

section Padic
variable (p : ℕ)

def Tset (m : ℕ) : Finset ℕ := (Finset.range (p^m)).filter (fun t => ¬ p ∣ t)
def Gp (m : ℕ) (c : ℤ) : ℤ := ∏ t ∈ Tset p m, ((t : ℤ) + c * (p^m : ℤ))

theorem mem_Tset {m t : ℕ} : t ∈ Tset p m ↔ t < p^m ∧ ¬ p ∣ t := by
  simp [Tset, Finset.mem_filter, Finset.mem_range]

variable [Fact p.Prime]

theorem Tset_one_le {m t : ℕ} (ht : t ∈ Tset p m) : 1 ≤ t := by
  rw [mem_Tset] at ht
  exact Nat.one_le_iff_ne_zero.mpr (fun h => ht.2 (h ▸ dvd_zero p))

theorem Tset_symm {m t : ℕ} (ht : t ∈ Tset p m) : (p^m - t) ∈ Tset p m := by
  have h1 := Tset_one_le p ht
  rw [mem_Tset] at ht ⊢
  refine ⟨by omega, ?_⟩
  intro hd
  exact ht.2 (by
    have : p ∣ p^m - (p^m - t) := Nat.dvd_sub (dvd_pow_self p (by
      rintro rfl; simp only [pow_zero] at ht; omega)) hd
    rwa [Nat.sub_sub_self (le_of_lt ht.1)] at this)

theorem reindex_prod {M} [CommMonoid M] (m : ℕ) (F : ℕ → M) :
    ∏ t ∈ Tset p m, F (p^m - t) = ∏ t ∈ Tset p m, F t := by
  apply Finset.prod_nbij' (fun t => p^m - t) (fun t => p^m - t)
  · exact fun a ha => Tset_symm p ha
  · exact fun a ha => Tset_symm p ha
  · intro a ha; have := Tset_one_le p ha; rw [mem_Tset] at ha; omega
  · intro a ha; have := Tset_one_le p ha; rw [mem_Tset] at ha; omega
  · intro a _; rfl

theorem reindex_sum {M} [AddCommMonoid M] (m : ℕ) (F : ℕ → M) :
    ∑ t ∈ Tset p m, F (p^m - t) = ∑ t ∈ Tset p m, F t := by
  apply Finset.sum_nbij' (fun t => p^m - t) (fun t => p^m - t)
  · exact fun a ha => Tset_symm p ha
  · exact fun a ha => Tset_symm p ha
  · intro a ha; have := Tset_one_le p ha; rw [mem_Tset] at ha; omega
  · intro a ha; have := Tset_one_le p ha; rw [mem_Tset] at ha; omega
  · intro a _; rfl

theorem isUnit_cast {t : ℕ} (ht : ¬ p ∣ t) : IsUnit ((t : ℤ_[p])) := by
  rw [show ((t:ℤ_[p])) = ((t:ℤ):ℤ_[p]) by push_cast; ring, PadicInt.isUnit_iff,
      PadicInt.norm_intCast_eq_one_iff]
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hnd : ¬ (p:ℤ) ∣ (t:ℤ) := fun h => ht (by exact_mod_cast h)
  exact ((hpp.coprime_iff_not_dvd).mpr hnd).symm

theorem isUnit_cast_Tset {m t : ℕ} (ht : t ∈ Tset p m) : IsUnit ((t : ℤ_[p])) :=
  isUnit_cast p ((mem_Tset p).mp ht).2

theorem isUnit_cast_symm {m t : ℕ} (ht : t ∈ Tset p m) :
    IsUnit (((p^m - t : ℕ) : ℤ_[p])) :=
  isUnit_cast_Tset p (Tset_symm p ht)

/-- `F_c := ∏_{t∈T} (1 + c·x·u_t)`, x=p^m, u_t=inverse t. -/
noncomputable def Fp (m : ℕ) (cc : ℤ_[p]) : ℤ_[p] :=
  ∏ t ∈ Tset p m, (1 + cc * ((p:ℤ_[p])^m * Ring.inverse (t:ℤ_[p])))

/-- Σ2 := ∑ u_t². -/
noncomputable def Sig2 (m : ℕ) : ℤ_[p] := ∑ t ∈ Tset p m, (Ring.inverse (t:ℤ_[p]))^2

/-- D := ∑ v_t², v_t = inverse(τ_t·τ_{x-t}). -/
noncomputable def Dd (m : ℕ) : ℤ_[p] :=
  ∑ t ∈ Tset p m, (Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])))^2

theorem tau_add {m t : ℕ} (ht : t ∈ Tset p m) :
    (t:ℤ_[p]) + ((p^m - t : ℕ):ℤ_[p]) = (p:ℤ_[p])^m := by
  have hle : t ≤ p^m := le_of_lt ((mem_Tset p).mp ht).1
  rw [← Nat.cast_add, show t + (p^m - t) = p^m by omega]
  push_cast; ring

/-- pairing (i): u_t + u_{x-t} = x · v_t. -/
theorem pair_i {m t : ℕ} (ht : t ∈ Tset p m) :
    Ring.inverse (t:ℤ_[p]) + Ring.inverse ((p^m - t : ℕ):ℤ_[p])
      = (p:ℤ_[p])^m * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])) :=
  inv_add_eq (isUnit_cast_Tset p ht) (isUnit_cast_symm p ht) (tau_add p ht)

/-- v_t = u_t · u_{x-t}. -/
theorem vmul {m t : ℕ} :
    Ring.inverse (t:ℤ_[p]) * Ring.inverse ((p^m - t : ℕ):ℤ_[p])
      = Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])) := by
  rw [Ring.mul_inverse_rev]; ring

/-- Squaring identity: F_c² = ∏ (1 + (c²+c)·x²·v_t). -/
theorem Fsq (m : ℕ) (cc : ℤ_[p]) :
    (Fp p m cc)^2 =
      ∏ t ∈ Tset p m,
        (1 + (cc^2 + cc) * ((p:ℤ_[p])^m * (p:ℤ_[p])^m)
          * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p]))) := by
  have hre : Fp p m cc
      = ∏ t ∈ Tset p m, (1 + cc * ((p:ℤ_[p])^m * Ring.inverse (((p^m - t : ℕ):ℤ_[p])))) := by
    unfold Fp
    exact (reindex_prod p m (fun s => 1 + cc * ((p:ℤ_[p])^m * Ring.inverse ((s:ℕ):ℤ_[p])))).symm
  rw [pow_two]
  nth_rewrite 2 [hre]
  unfold Fp
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  have hi := pair_i p ht
  have hm := vmul p (m := m) (t := t)
  set x := (p:ℤ_[p])^m
  set ut := Ring.inverse (t:ℤ_[p])
  set us := Ring.inverse ((p^m - t : ℕ):ℤ_[p])
  set vt := Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p]))
  -- hi : ut + us = x * vt ; hm : ut * us = vt
  linear_combination (cc * x) * hi + (cc^2 * x * x) * hm

def wv : ℕ := if p = 3 then 1 else 0

theorem wv_le_one : wv p ≤ 1 := by unfold wv; split <;> norm_num

theorem not_dvd_two (hp3 : 3 ≤ p) : ¬ p ∣ 2 := by
  intro h; have := Nat.le_of_dvd (by norm_num) h; omega

theorem isUnit_of_dvd_sub {z u : ℤ_[p]} (hu : IsUnit u) (h : (p:ℤ_[p]) ∣ (z - u)) : IsUnit z := by
  rw [PadicInt.isUnit_iff] at hu ⊢
  have h1 : ‖z - u‖ < 1 := (PadicInt.norm_lt_one_iff_dvd _).mpr h
  have hne : ‖u‖ ≠ ‖z - u‖ := by rw [hu]; exact ne_of_gt h1
  have hz : z = u + (z - u) := by ring
  rw [hz, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hu, max_eq_left (le_of_lt h1)]

theorem Fp_zero (m : ℕ) : Fp p m 0 = 1 := by unfold Fp; simp

/-- v_t = -u_t² + x·(u_t²·u_{x-t}). -/
theorem vterm {m t : ℕ} (ht : t ∈ Tset p m) :
    Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p]))
      = -(Ring.inverse (t:ℤ_[p]))^2
        + (p:ℤ_[p])^m * ((Ring.inverse (t:ℤ_[p]))^2 * Ring.inverse ((p^m - t : ℕ):ℤ_[p])) := by
  have hvt := (vmul p (m := m) (t := t))
  have hut : (t:ℤ_[p]) * Ring.inverse (t:ℤ_[p]) = 1 := Ring.mul_inverse_cancel _ (isUnit_cast_Tset p ht)
  have hus : ((p^m - t : ℕ):ℤ_[p]) * Ring.inverse ((p^m - t : ℕ):ℤ_[p]) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_cast_symm p ht)
  have hsum := tau_add p ht
  set x := (p:ℤ_[p])^m
  set ut := Ring.inverse (t:ℤ_[p])
  set us := Ring.inverse ((p^m - t : ℕ):ℤ_[p])
  set vt := Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p]))
  set τt := (t:ℤ_[p])
  set τs := ((p^m - t : ℕ):ℤ_[p])
  -- hvt : ut*us = vt, hut : τt*ut=1, hus: τs*us=1, hsum: τt+τs=x
  linear_combination -hvt + (ut^2 * us) * hsum - (ut * us) * hut - ut^2 * hus

/-- R := ∑ u_t²·u_{x-t}. -/
noncomputable def Rsum (m : ℕ) : ℤ_[p] :=
  ∑ t ∈ Tset p m, (Ring.inverse (t:ℤ_[p]))^2 * Ring.inverse ((p^m - t : ℕ):ℤ_[p])

theorem sumv (m : ℕ) :
    (∑ t ∈ Tset p m, Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])))
      = - Sig2 p m + (p:ℤ_[p])^m * Rsum p m := by
  unfold Sig2 Rsum
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  exact vterm p ht

noncomputable def gam (m : ℕ) (cc : ℤ_[p]) (t : ℕ) : ℤ_[p] :=
  (cc^2 + cc) * ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p]))

theorem Fsq' (m : ℕ) (cc : ℤ_[p]) :
    (Fp p m cc)^2 = ∏ t ∈ Tset p m, (1 + gam p m cc t) := by
  rw [Fsq]; rfl

theorem cast_Gp (m : ℕ) (c : ℤ) :
    ((Gp p m c : ℤ) : ℤ_[p]) = ∏ t ∈ Tset p m, ((t:ℤ_[p]) + (c:ℤ_[p]) * (p:ℤ_[p])^m) := by
  unfold Gp; push_cast; rfl

theorem GpZ_factor (m : ℕ) (cc : ℤ_[p]) :
    ∏ t ∈ Tset p m, ((t:ℤ_[p]) + cc * (p:ℤ_[p])^m)
      = (∏ t ∈ Tset p m, (t:ℤ_[p])) * Fp p m cc := by
  unfold Fp; rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl; intro t ht
  have hu : (t:ℤ_[p]) * Ring.inverse (t:ℤ_[p]) = 1 :=
    Ring.mul_inverse_cancel _ (isUnit_cast_Tset p ht)
  linear_combination (-(cc*(p:ℤ_[p])^m)) * hu

theorem cast_Gp_diff (m : ℕ) (c : ℤ) :
    ((Gp p m c - Gp p m 0 : ℤ) : ℤ_[p])
      = (∏ t ∈ Tset p m, (t:ℤ_[p])) * (Fp p m (c:ℤ_[p]) - 1) := by
  have hsub : ((Gp p m c - Gp p m 0 : ℤ) : ℤ_[p])
      = ((Gp p m c : ℤ) : ℤ_[p]) - ((Gp p m 0 : ℤ) : ℤ_[p]) := by push_cast; ring
  rw [hsub, cast_Gp, cast_Gp, GpZ_factor, GpZ_factor]
  simp only [Int.cast_zero]
  rw [Fp_zero]; ring

theorem Fsq_dvd (m : ℕ) (hm : 1 ≤ m) (cc : ℤ_[p])
    (hSig : (p:ℤ_[p])^(m - wv p) ∣ Sig2 p m) :
    (p:ℤ_[p])^(3*m - wv p) ∣ ((Fp p m cc)^2 - 1) := by
  have hw := wv_le_one p
  have hx2 : (p:ℤ_[p])^m * (p:ℤ_[p])^m = (p:ℤ_[p])^(2*m) := by rw [← pow_add]; congr 1; omega
  rw [Fsq']
  have hsplit : (∏ t ∈ Tset p m, (1 + gam p m cc t)) - 1
      = ((∏ t ∈ Tset p m, (1 + gam p m cc t)) - 1 - ∑ t ∈ Tset p m, gam p m cc t)
        + ∑ t ∈ Tset p m, gam p m cc t := by ring
  rw [hsplit]
  refine dvd_add ?_ ?_
  · -- second-order remainder, divisible by (x²)² = p^(4m)
    have hd : ∀ t ∈ Tset p m, ((p:ℤ_[p])^m * (p:ℤ_[p])^m) ∣ gam p m cc t := by
      intro t ht
      exact ⟨(cc^2 + cc) * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])), by unfold gam; ring⟩
    have hP2 := prod_one_add_sub_linear ((p:ℤ_[p])^m * (p:ℤ_[p])^m) (gam p m cc) (Tset p m) hd
    have hpow : ((p:ℤ_[p])^m * (p:ℤ_[p])^m)^2 = (p:ℤ_[p])^(4*m) := by
      rw [hx2, ← pow_mul]; congr 1; omega
    rw [hpow] at hP2
    exact dvd_trans (pow_dvd_pow _ (by omega)) hP2
  · -- linear term ∑ gam = (cc²+cc)·x²·(-Σ2 + x·R)
    have hgam_sum : (∑ t ∈ Tset p m, gam p m cc t)
        = (cc^2 + cc) * ((p:ℤ_[p])^m * (p:ℤ_[p])^m)
            * (∑ t ∈ Tset p m, Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p]))) := by
      unfold gam; rw [← Finset.mul_sum]
    rw [hgam_sum, sumv]
    rw [mul_assoc]
    apply Dvd.dvd.mul_left
    -- goal: p^(3m-w) ∣ (x*x)*(-Sig2 + x*Rsum)
    have hM1 : (p:ℤ_[p])^(3*m - wv p) ∣ ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * (- Sig2 p m) := by
      rw [hx2]
      obtain ⟨k, hk⟩ := hSig
      refine ⟨-k, ?_⟩
      rw [hk]
      rw [show (p:ℤ_[p])^(3*m - wv p) = (p:ℤ_[p])^(2*m) * (p:ℤ_[p])^(m - wv p) by
        rw [← pow_add]; congr 1; omega]
      ring
    have hM2 : (p:ℤ_[p])^(3*m - wv p) ∣ ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * ((p:ℤ_[p])^m * Rsum p m) := by
      have : ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * ((p:ℤ_[p])^m * Rsum p m)
          = (p:ℤ_[p])^(3*m) * Rsum p m := by
        rw [hx2, ← mul_assoc, ← pow_add, show 2*m+m = 3*m by omega]
      rw [this]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
    have := dvd_add hM1 hM2
    have e : ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * (- Sig2 p m)
        + ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * ((p:ℤ_[p])^m * Rsum p m)
        = ((p:ℤ_[p])^m * (p:ℤ_[p])^m) * (- Sig2 p m + (p:ℤ_[p])^m * Rsum p m) := by ring
    rwa [e] at this

theorem Fp_dvd (m : ℕ) (hm : 1 ≤ m) (cc : ℤ_[p]) (hp3 : 3 ≤ p)
    (hSig : (p:ℤ_[p])^(m - wv p) ∣ Sig2 p m) :
    (p:ℤ_[p])^(3*m - wv p) ∣ (Fp p m cc - 1) := by
  have hFsq := Fsq_dvd p m hm cc hSig
  -- Fp cc + 1 is a unit
  have hdvd1 : (p:ℤ_[p]) ∣ (Fp p m cc - 1) := by
    unfold Fp
    apply prod_one_add_sub_one
    intro t ht
    have hpm : (p:ℤ_[p]) ∣ (p:ℤ_[p])^m := dvd_pow_self _ (by omega)
    exact (hpm.mul_right (Ring.inverse (t:ℤ_[p]))).mul_left cc
  have hunit : IsUnit (Fp p m cc + 1) := by
    apply isUnit_of_dvd_sub (u := 2)
    · rw [show (2:ℤ_[p]) = ((2:ℕ):ℤ_[p]) by norm_num]
      exact isUnit_cast p (not_dvd_two p hp3)
    · have : Fp p m cc + 1 - 2 = Fp p m cc - 1 := by ring
      rw [this]; exact hdvd1
  have hcancel : (Fp p m cc - 1)
      = ((Fp p m cc)^2 - 1) * Ring.inverse (Fp p m cc + 1) := by
    have h1 : (Fp p m cc)^2 - 1 = (Fp p m cc - 1) * (Fp p m cc + 1) := by ring
    rw [h1, mul_assoc, Ring.mul_inverse_cancel _ hunit, mul_one]
  rw [hcancel]; exact Dvd.dvd.mul_right hFsq _

/-- Extracted: (p) ∣ (Fp cc − 1). -/
theorem Fp_sub_one_dvd (m : ℕ) (hm : 1 ≤ m) (cc : ℤ_[p]) : (p:ℤ_[p]) ∣ (Fp p m cc - 1) := by
  unfold Fp
  apply prod_one_add_sub_one
  intro t ht
  have hpm : (p:ℤ_[p]) ∣ (p:ℤ_[p])^m := dvd_pow_self _ (by omega)
  exact (hpm.mul_right (Ring.inverse (t:ℤ_[p]))).mul_left cc

theorem cast_Gp_core (m : ℕ) :
    ((Gp p m 2 * (Gp p m 0)^2 - (Gp p m 1)^3 : ℤ) : ℤ_[p])
      = (∏ t ∈ Tset p m, (t:ℤ_[p]))^3 * (Fp p m 2 - (Fp p m 1)^3) := by
  have e2 : ((Gp p m 2 : ℤ):ℤ_[p]) = (∏ t ∈ Tset p m, (t:ℤ_[p])) * Fp p m 2 := by
    rw [cast_Gp, show ((2:ℤ):ℤ_[p]) = (2:ℤ_[p]) by norm_num]; exact GpZ_factor p m 2
  have e1 : ((Gp p m 1 : ℤ):ℤ_[p]) = (∏ t ∈ Tset p m, (t:ℤ_[p])) * Fp p m 1 := by
    rw [cast_Gp, show ((1:ℤ):ℤ_[p]) = (1:ℤ_[p]) by norm_num]; exact GpZ_factor p m 1
  have e0 : ((Gp p m 0 : ℤ):ℤ_[p]) = (∏ t ∈ Tset p m, (t:ℤ_[p])) := by
    rw [cast_Gp, show ((0:ℤ):ℤ_[p]) = (0:ℤ_[p]) by norm_num, GpZ_factor, Fp_zero, mul_one]
  push_cast
  rw [e2, e1, e0]; ring

-- Step: the p∣· part reindexes.
theorem pdvd_reindex (m : ℕ) (hm : 1 ≤ m) (hp : 0 < p) :
    ((Finset.range (p^m)).filter (fun t => p ∣ t))
      = (Finset.range (p^(m-1))).image (fun s => p * s) := by
  have hpm : p^m = p * p^(m-1) := by rw [← pow_succ']; congr 1; omega
  ext t
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨htlt, s, rfl⟩
    refine ⟨s, ?_, rfl⟩
    rw [hpm] at htlt
    exact lt_of_mul_lt_mul_left htlt (Nat.zero_le p)
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, ⟨s, rfl⟩⟩
    rw [hpm]
    exact Nat.mul_lt_mul_of_pos_left hs hp

theorem sq_split (m : ℕ) (hm : 1 ≤ m) (hp : 0 < p) :
    (∑ t ∈ Tset p m, (t:ℤ)^2)
      = (∑ t ∈ Finset.range (p^m), (t:ℤ)^2)
        - (p:ℤ)^2 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2) := by
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (p^m))
    (fun t => p ∣ t) (fun t => (t:ℤ)^2)
  have himg : (∑ t ∈ (Finset.range (p^m)).filter (fun t => p ∣ t), (t:ℤ)^2)
      = (p:ℤ)^2 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2) := by
    rw [pdvd_reindex p m hm hp, Finset.sum_image (by
      intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hp hab)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; push_cast; ring
  rw [himg] at hpart
  unfold Tset
  linarith [hpart]

theorem faulhaber (m : ℕ) (hm : 1 ≤ m) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (p:ℤ)^(m - wv p) ∣ (∑ t ∈ Tset p m, (t:ℤ)^2) := by
  have hp0 : 0 < p := by omega
  set Ssq := ∑ t ∈ Tset p m, (t:ℤ)^2 with hSsq
  have hx : (p:ℤ)^m = (p:ℤ) * (p:ℤ)^(m-1) := by
    nth_rewrite 1 [show m = 1 + (m-1) by omega]
    rw [pow_add, pow_one]
  -- 6 * Ssq = p^m * K
  have h6 : 6 * Ssq = (p:ℤ)^m * ((((p:ℤ)^m - 1) * (2*(p:ℤ)^m - 1))
      - p * (((p:ℤ)^(m-1) - 1) * (2*(p:ℤ)^(m-1) - 1))) := by
    rw [hSsq, sq_split p m hm hp0, mul_sub]
    rw [show (6:ℤ) * (∑ t ∈ Finset.range (p^m), (t:ℤ)^2) = _ from sum_sq_range (p^m)]
    rw [show (6:ℤ) * ((p:ℤ)^2 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2))
        = (p:ℤ)^2 * (6 * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2)) by ring]
    rw [show (6:ℤ) * (∑ s ∈ Finset.range (p^(m-1)), (s:ℤ)^2) = _ from sum_sq_range (p^(m-1))]
    push_cast
    rw [hx]; ring
  have hdvd6 : (p:ℤ)^m ∣ 6 * Ssq := ⟨_, h6⟩
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hp3eq : p = 3
  · -- w = 1, need 3^(m-1) ∣ Ssq
    have hwv : wv p = 1 := by unfold wv; rw [if_pos hp3eq]
    rw [hwv]
    have hp3z : (p:ℤ) = 3 := by rw [hp3eq]; norm_num
    have h1 : (p:ℤ)^m ∣ 3 * (2 * Ssq) := by
      have : (6:ℤ) * Ssq = 3 * (2 * Ssq) := by ring
      rwa [this] at hdvd6
    have hxm : (p:ℤ)^m = (3:ℤ) * (p:ℤ)^(m-1) := by rw [hx, hp3z]
    have h2 : (3:ℤ) * (p:ℤ)^(m-1) ∣ 3 * (2 * Ssq) := by rw [← hxm]; exact h1
    have h3 : (p:ℤ)^(m-1) ∣ 2 * Ssq :=
      (mul_dvd_mul_iff_left (by norm_num : (3:ℤ) ≠ 0)).mp h2
    have hcop : IsCoprime ((p:ℤ)^(m-1)) 2 := by
      apply IsCoprime.pow_left
      rw [hp3z, Int.isCoprime_iff_gcd_eq_one]; decide
    exact hcop.dvd_of_dvd_mul_left h3
  · -- w = 0, need p^m ∣ Ssq
    have hwv : wv p = 0 := by unfold wv; simp [hp3eq]
    rw [hwv, Nat.sub_zero]
    have hcop : IsCoprime ((p:ℤ)^m) 6 := by
      apply IsCoprime.pow_left
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p <;> first | (exact absurd rfl hp3eq) | (exact absurd hp (by decide)) | omega
        · exact h
      have hnd2 : ¬ (p:ℤ) ∣ 2 := by
        intro h; have := Int.le_of_dvd (by norm_num) h; omega
      have hnd3 : ¬ (p:ℤ) ∣ 3 := by
        intro h; have := Int.le_of_dvd (by norm_num) h; omega
      have hnd6 : ¬ (p:ℤ) ∣ 6 := by
        intro h
        rcases hpp.dvd_mul.mp (show (p:ℤ) ∣ 2 * 3 by rwa [show (2:ℤ)*3 = 6 by norm_num]) with h2 | h3
        · exact hnd2 h2
        · exact hnd3 h3
      exact (hpp.coprime_iff_not_dvd).mpr hnd6
    exact hcop.dvd_of_dvd_mul_left hdvd6


/-- Fiber counting mod p: for m ≥ 2, any `F`-sum over Tset vanishes mod p. -/
theorem sum_Tset_mod_p (m : ℕ) (hm : 2 ≤ m) (F : ZMod p → ZMod p) :
    (∑ t ∈ Tset p m, F ((t : ZMod p))) = 0 := by
  have hp := (Fact.out : p.Prime)
  have hp0 : 0 < p := hp.pos
  have hbij : (∑ t ∈ Tset p m, F ((t:ZMod p)))
      = ∑ q ∈ (Tset p 1) ×ˢ (Finset.range (p^(m-1))), F ((q.1 : ZMod p)) := by
    have hpp : p * p^(m-1) = p^m := by
      conv_rhs => rw [show m = 1 + (m-1) by omega]
      rw [pow_add, pow_one]
    apply Finset.sum_nbij' (fun t => (t % p, t / p)) (fun q => q.1 + p * q.2)
    · intro t ht
      rw [mem_Tset] at ht
      rw [Finset.mem_product, mem_Tset, Finset.mem_range]
      refine ⟨⟨by rw [pow_one]; exact Nat.mod_lt _ hp0, ?_⟩, ?_⟩
      · intro hd
        exact ht.2 (Nat.dvd_of_mod_eq_zero
          (Nat.eq_zero_of_dvd_of_lt hd (Nat.mod_lt _ hp0)))
      · rw [Nat.div_lt_iff_lt_mul hp0, mul_comm, hpp]; exact ht.1
    · intro q hq
      rw [Finset.mem_product, mem_Tset, Finset.mem_range] at hq
      rw [mem_Tset]
      obtain ⟨⟨hr1, hr2⟩, hs⟩ := hq
      rw [pow_one] at hr1
      refine ⟨?_, ?_⟩
      · have h1 : q.1 + p * q.2 < p * q.2 + p := by omega
        have h2 : p * (q.2 + 1) ≤ p^m := by
          rw [← hpp]; exact mul_le_mul_left' (by omega) p
        have h3 : p * q.2 + p = p * (q.2 + 1) := by ring
        omega
      · intro hd
        exact hr2 ((Nat.dvd_add_right (Dvd.intro q.2 rfl)).mp (by rwa [add_comm] at hd))
    · intro t ht; simp [Nat.mod_add_div]
    · intro q hq
      rw [Finset.mem_product, mem_Tset, Finset.mem_range] at hq
      obtain ⟨⟨hr1, hr2⟩, hs⟩ := hq
      rw [pow_one] at hr1
      ext
      · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr1]
      · rw [Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hr1, zero_add]
    · intro t ht
      show F ((t:ZMod p)) = F (((t % p : ℕ):ZMod p))
      rw [ZMod.natCast_mod]
  rw [hbij, Finset.sum_product]
  apply Finset.sum_eq_zero
  intro r hr
  dsimp only
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hz : ((p^(m-1) : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_pow (by omega : m - 1 ≠ 0)]
  rw [hz, zero_mul]


theorem zmod_inv_sq_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ t ∈ Tset p m, (Ring.inverse ((t : ZMod (p^m))))^2)
      = (∑ t ∈ Tset p m, ((t : ZMod (p^m)))^2) := by
  haveI hne : NeZero (p^m) := ⟨(pow_pos (Fact.out : p.Prime).pos m).ne'⟩
  have hp := (Fact.out : p.Prime)
  set σ : ℕ → ℕ := fun t => (Ring.inverse ((t : ZMod (p^m)))).val with hσ
  -- (a): ↑(σ t) = Ring.inverse ↑t
  have ha : ∀ t, ((σ t : ℕ) : ZMod (p^m)) = Ring.inverse ((t : ZMod (p^m))) := by
    intro t; rw [hσ]; exact ZMod.natCast_zmod_val _
  -- unit facts
  have hunit_t : ∀ t ∈ Tset p m, IsUnit ((t : ZMod (p^m))) := by
    intro t ht
    rw [ZMod.isUnit_iff_coprime]
    exact (((hp.coprime_iff_not_dvd).mpr ((mem_Tset p).mp ht).2).symm).pow_right m
  -- σ maps Tset to Tset
  have hmaps : ∀ t ∈ Tset p m, σ t ∈ Tset p m := by
    intro t ht
    rw [mem_Tset]
    refine ⟨by rw [hσ]; exact ZMod.val_lt _, ?_⟩
    -- ↑(σ t) is a unit ⟹ coprime ⟹ ¬p∣σt
    have huσ : IsUnit ((σ t : ZMod (p^m))) := by
      rw [ha t]; obtain ⟨u, hu⟩ := hunit_t t ht
      rw [← hu, Ring.inverse_unit]; exact (u⁻¹).isUnit
    rw [ZMod.isUnit_iff_coprime] at huσ
    have hcp : Nat.Coprime (σ t) p := huσ.coprime_dvd_right (dvd_pow_self p (by omega))
    exact (hp.coprime_iff_not_dvd).mp hcp.symm
  -- σ is an involution on Tset
  have hinv : ∀ t ∈ Tset p m, σ (σ t) = t := by
    intro t ht
    have h1 : ((σ (σ t) : ℕ) : ZMod (p^m)) = ((t : ℕ) : ZMod (p^m)) := by
      rw [ha (σ t), ha t, ring_inv_inv (hunit_t t ht)]
    -- cast injective on values < p^m
    have hlt1 : σ (σ t) < p^m := by rw [hσ]; exact ZMod.val_lt _
    have hlt2 : t < p^m := ((mem_Tset p).mp ht).1
    -- use ZMod.val injective
    have := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at this
  -- rewrite LHS via ha, then reindex by σ
  rw [show (∑ t ∈ Tset p m, (Ring.inverse ((t : ZMod (p^m))))^2)
      = (∑ t ∈ Tset p m, (((σ t : ℕ) : ZMod (p^m)))^2) from
        Finset.sum_congr rfl (fun t _ => by rw [ha t])]
  exact Finset.sum_nbij' σ σ hmaps hmaps hinv hinv (fun a _ => rfl)


/-- ANALYTIC INPUT A -/
theorem Sig2_dvd (m : ℕ) (hm : 1 ≤ m) (hp3 : 3 ≤ p) :
    (p:ℤ_[p])^(m - wv p) ∣ Sig2 p m := by
  have hp := (Fact.out : p.Prime)
  set Ssum : ℤ_[p] := ∑ t ∈ Tset p m, ((t:ℤ_[p]))^2 with hSsum
  -- bridge via toZModPow m
  have hSig2map : PadicInt.toZModPow m (Sig2 p m)
      = ∑ t ∈ Tset p m, (Ring.inverse ((t:ZMod (p^m))))^2 := by
    unfold Sig2
    rw [map_sum]
    apply Finset.sum_congr rfl; intro t ht
    rw [map_pow, map_ring_inverse _ (isUnit_cast p ((mem_Tset p).mp ht).2), map_natCast]
  have hSsummap : PadicInt.toZModPow m Ssum
      = ∑ t ∈ Tset p m, ((t:ZMod (p^m)))^2 := by
    rw [hSsum, map_sum]
    apply Finset.sum_congr rfl; intro t _; rw [map_pow, map_natCast]
  have hbridge : (p:ℤ_[p])^m ∣ (Sig2 p m - Ssum) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        hSig2map, hSsummap, zmod_inv_sq_sum p m hm, sub_self]
  -- Faulhaber transported to ℤ_[p]
  obtain ⟨k, hk⟩ := faulhaber p m hm hp hp3
  have hSs_cast : Ssum = (((∑ t ∈ Tset p m, (t:ℤ)^2 : ℤ)):ℤ_[p]) := by
    rw [hSsum, Int.cast_sum]; apply Finset.sum_congr rfl; intro t _; push_cast; ring
  have hfaul_padic : (p:ℤ_[p])^(m - wv p) ∣ Ssum := by
    refine ⟨(k:ℤ_[p]), ?_⟩
    rw [hSs_cast, hk]; push_cast; ring
  have hsplit : Sig2 p m = (Sig2 p m - Ssum) + Ssum := by ring
  rw [hsplit]
  exact dvd_add (dvd_trans (pow_dvd_pow _ (Nat.sub_le m (wv p))) hbridge) hfaul_padic

/-- ANALYTIC INPUT B -/
theorem Dd_dvd (m : ℕ) (hm : 2 ≤ m) (hp3 : 3 ≤ p) : (p:ℤ_[p]) ∣ Dd p m := by
  have hp := (Fact.out : p.Prime)
  have h0 : PadicInt.toZMod (Dd p m) = 0 := by
    unfold Dd
    rw [map_sum]
    have hterm : ∀ t ∈ Tset p m,
        PadicInt.toZMod ((Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])))^2)
          = (fun a => (Ring.inverse (a * (-a)))^2) ((t:ZMod p)) := by
      intro t ht
      have hu : IsUnit ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])) :=
        (isUnit_cast p ((mem_Tset p).mp ht).2).mul
          (isUnit_cast p ((mem_Tset p).mp (Tset_symm p ht)).2)
      have hpm0 : ((p^m : ℕ) : ZMod p) = 0 := by
        push_cast; rw [ZMod.natCast_self]; exact zero_pow (by omega)
      have hcast : ((p^m - t : ℕ) : ZMod p) = -(t : ZMod p) := by
        have hle : t ≤ p^m := le_of_lt ((mem_Tset p).mp ht).1
        rw [Nat.cast_sub hle, hpm0]; ring
      simp only
      rw [map_pow, map_ring_inverse _ hu, map_mul, map_natCast, map_natCast, hcast]
    rw [Finset.sum_congr rfl hterm]
    exact sum_Tset_mod_p p m hm (fun a => (Ring.inverse (a * (-a)))^2)
  rw [← PadicInt.norm_lt_one_iff_dvd]
  have hnu : ¬ IsUnit (Dd p m) := by
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact h0
  rw [PadicInt.isUnit_iff] at hnu
  exact lt_of_le_of_ne (PadicInt.norm_le_one _) hnu


theorem CORE_F (m : ℕ) (hm : 2 ≤ m) (hp3 : 3 ≤ p) :
    (p:ℤ_[p])^(3*m+3) ∣ (Fp p m 2 - (Fp p m 1)^3) := by
  set x := (p:ℤ_[p])^m with hxdef
  have hx2 : x * x = (p:ℤ_[p])^(2*m) := by rw [hxdef, ← pow_add]; congr 1; omega
  -- product forms
  have hF2sq : (Fp p m 2)^2 = ∏ t ∈ Tset p m, (1 + gam p m 2 t) := Fsq' p m 2
  have hF1_6 : (Fp p m 1)^6 = ∏ t ∈ Tset p m, (1 + ((1 + gam p m 1 t)^3 - 1)) := by
    have h6 : (Fp p m 1)^6 = ((Fp p m 1)^2)^3 := by ring
    rw [h6, Fsq' p m 1, ← Finset.prod_pow]
    apply Finset.prod_congr rfl; intro t _; ring
  -- prod_cmp
  have hdG : ∀ t ∈ Tset p m, (x*x) ∣ gam p m 2 t := by
    intro t ht
    exact ⟨(2^2+2) * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])), by unfold gam; rw [hxdef]; ring⟩
  have hdB : ∀ t ∈ Tset p m, (x*x) ∣ ((1 + gam p m 1 t)^3 - 1) := by
    intro t ht
    obtain ⟨w, hw⟩ : (x*x) ∣ gam p m 1 t :=
      ⟨(1^2+1) * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])), by unfold gam; rw [hxdef]; ring⟩
    exact ⟨w * (3 + 3*(gam p m 1 t) + (gam p m 1 t)^2), by rw [hw]; ring⟩
  have hdGB : ∀ t ∈ Tset p m, (x*x)^2 ∣ (gam p m 2 t - ((1 + gam p m 1 t)^3 - 1)) := by
    intro t ht
    obtain ⟨w, hw⟩ : (x*x) ∣ gam p m 1 t :=
      ⟨(1^2+1) * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])), by unfold gam; rw [hxdef]; ring⟩
    -- gam2 = 3*gam1, so difference = -3*gam1^2 - gam1^3, divisible by (x*x)^2
    have hgeq : gam p m 2 t = 3 * gam p m 1 t := by unfold gam; ring
    refine ⟨-(3*w^2) - w^2*(gam p m 1 t), ?_⟩
    rw [hgeq]
    have : gam p m 1 t = (x*x) * w := hw
    rw [this]; ring
  have hcmp := prod_cmp (x*x) (fun t => gam p m 2 t) (fun t => (1 + gam p m 1 t)^3 - 1)
    (Tset p m) hdG hdB hdGB
  -- F2^2 - F1^6 = ∑(G-B) + (mult of (x*x)^3)
  have hbig : (p:ℤ_[p])^(3*m+3) ∣ ((Fp p m 2)^2 - (Fp p m 1)^6) := by
    rw [hF2sq, hF1_6]
    have hsplit : (∏ t ∈ Tset p m, (1 + gam p m 2 t)) - (∏ t ∈ Tset p m, (1 + ((1 + gam p m 1 t)^3 - 1)))
        = ((∏ t ∈ Tset p m, (1 + gam p m 2 t)) - (∏ t ∈ Tset p m, (1 + ((1 + gam p m 1 t)^3 - 1)))
            - ∑ t ∈ Tset p m, (gam p m 2 t - ((1 + gam p m 1 t)^3 - 1)))
          + ∑ t ∈ Tset p m, (gam p m 2 t - ((1 + gam p m 1 t)^3 - 1)) := by ring
    rw [hsplit]
    refine dvd_add ?_ ?_
    · -- prod_cmp remainder, divisible by (x*x)^3 = p^(6m)
      have hpow : (x*x)^3 = (p:ℤ_[p])^(6*m) := by rw [hx2, ← pow_mul]; congr 1; omega
      rw [hpow] at hcmp
      exact dvd_trans (pow_dvd_pow _ (by omega)) hcmp
    · -- ∑(G-B) = -3·∑gam1² - ∑gam1³
      have hterm : ∀ t ∈ Tset p m, (gam p m 2 t - ((1 + gam p m 1 t)^3 - 1))
          = -(3 * (gam p m 1 t)^2) - (gam p m 1 t)^3 := by
        intro t _; unfold gam; ring
      rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_sub_distrib]
      refine dvd_sub ?_ ?_
      · -- -3·∑gam1² = -12·(x*x)²·Dd
        have hgam1sq : (∑ t ∈ Tset p m, -(3 * (gam p m 1 t)^2))
            = -(12 * (x*x)^2 * Dd p m) := by
          unfold Dd gam
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro t _; rw [hxdef]; ring
        rw [hgam1sq]
        -- p^(3m+3) ∣ 12·(x*x)²·Dd since (x*x)²=p^(4m), p∣Dd, 3m+3≤4m+1
        obtain ⟨k, hk⟩ := Dd_dvd p m hm hp3
        refine Dvd.dvd.neg_right ?_
        rw [hk]
        have hxx2 : (x*x)^2 = (p:ℤ_[p])^(4*m) := by rw [hx2, ← pow_mul]; congr 1; omega
        rw [hxx2, show (12 : ℤ_[p]) * (p:ℤ_[p])^(4*m) * ((p:ℤ_[p]) * k)
            = (p:ℤ_[p])^(4*m+1) * (12 * k) by rw [pow_succ]; ring]
        exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      · -- ∑gam1³ : each term div by (x*x)^3 = p^(6m)
        apply Finset.dvd_sum
        intro t _
        obtain ⟨w, hw⟩ : (x*x) ∣ gam p m 1 t :=
          ⟨(1^2+1) * Ring.inverse ((t:ℤ_[p]) * ((p^m - t : ℕ):ℤ_[p])), by unfold gam; rw [hxdef]; ring⟩
        have hpow : (x*x)^3 = (p:ℤ_[p])^(6*m) := by rw [hx2, ← pow_mul]; congr 1; omega
        have : (gam p m 1 t)^3 = (x*x)^3 * w^3 := by rw [hw]; ring
        rw [this, hpow]
        exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
  -- cancel F2 + F1^3 (unit)
  have hunit : IsUnit (Fp p m 2 + (Fp p m 1)^3) := by
    apply isUnit_of_dvd_sub (u := 2)
    · rw [show (2:ℤ_[p]) = ((2:ℕ):ℤ_[p]) by norm_num]
      exact isUnit_cast p (not_dvd_two p hp3)
    · have hF2 := Fp_sub_one_dvd p m (by omega) 2
      have hF1 := Fp_sub_one_dvd p m (by omega) 1
      have hF13 : (p:ℤ_[p]) ∣ ((Fp p m 1)^3 - 1) := by
        obtain ⟨k, hk⟩ := hF1
        exact ⟨k * ((Fp p m 1)^2 + Fp p m 1 + 1), by
          have : Fp p m 1 = 1 + (p:ℤ_[p]) * k := by linear_combination hk
          rw [this]; ring⟩
      have : Fp p m 2 + (Fp p m 1)^3 - 2 = (Fp p m 2 - 1) + ((Fp p m 1)^3 - 1) := by ring
      rw [this]; exact dvd_add hF2 hF13
  have hcancel : (Fp p m 2 - (Fp p m 1)^3)
      = ((Fp p m 2)^2 - (Fp p m 1)^6) * Ring.inverse (Fp p m 2 + (Fp p m 1)^3) := by
    have h1 : (Fp p m 2)^2 - (Fp p m 1)^6
        = (Fp p m 2 - (Fp p m 1)^3) * (Fp p m 2 + (Fp p m 1)^3) := by ring
    rw [h1, mul_assoc, Ring.mul_inverse_cancel _ hunit, mul_one]
  rw [hcancel]; exact Dvd.dvd.mul_right hbig _

theorem LEVEL_DIFF (m : ℕ) (hm : 1 ≤ m) (c : ℤ) (hc : c = 1 ∨ c = 2) (hp3 : 3 ≤ p) :
    (p:ℤ)^(3*m - wv p) ∣ (Gp p m c - Gp p m 0) := by
  rw [← PadicInt.pow_p_dvd_int_iff, cast_Gp_diff]
  exact (Fp_dvd p m hm (c:ℤ_[p]) hp3 (Sig2_dvd p m hm hp3)).mul_left _

theorem CORE (m : ℕ) (hm : 2 ≤ m) (hp3 : 3 ≤ p) :
    (p:ℤ)^(3*m+3) ∣ (Gp p m 2 * (Gp p m 0)^2 - (Gp p m 1)^3) := by
  rw [← PadicInt.pow_p_dvd_int_iff, cast_Gp_core]
  exact (CORE_F p m hm hp3).mul_left _

end Padic

namespace Work

variable (p : ℕ)

/-- reduced residues in [0, p^m): {t : 0 ≤ t < p^m, ¬ p ∣ t}. -/
def Tset (m : ℕ) : Finset ℕ := (Finset.range (p^m)).filter (fun t => ¬ p ∣ t)

/-- G_c at level m : ∏_{t ∈ Tset} (t + c·p^m). -/
def Gp (m : ℕ) (c : ℤ) : ℤ := ∏ t ∈ Tset p m, ((t : ℤ) + c * (p^m : ℤ))

/-- w := v_p(3): 1 if p = 3 else 0. -/
def wv : ℕ := if p = 3 then 1 else 0

/-! ## The seven key lemmas (to be proven). -/

theorem G0_unit (m : ℕ) [hp : Fact p.Prime] : ¬ (p:ℤ) ∣ Gp p m 0 := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  unfold Gp
  simp only [zero_mul, add_zero]
  rw [hpp.dvd_finset_prod_iff]
  push_neg
  intro t ht
  simp only [Tset, Finset.mem_filter, Finset.mem_range] at ht
  intro hdvd
  exact ht.2 (by exact_mod_cast hdvd)

def GpN (m c : ℕ) : ℕ := ∏ t ∈ Tset p m, (t + c * p^m)

/-- The "coprime part" product: ∏_{k ∈ [1,L], ¬ p ∣ k} k. -/
def QR (L : ℕ) : ℕ := ∏ k ∈ (Finset.Icc 1 L).filter (fun k => ¬ p ∣ k), k

/-- `∏_{i ∈ [1,L]} i = L!`. -/
theorem prod_Icc_id : ∀ (L : ℕ), ∏ i ∈ Finset.Icc 1 L, i = L ! := by
  intro L
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega : (1:ℕ) ≤ n + 1), ih, Nat.factorial_succ]
    ring

/-- FACT_SPLIT: for `L = q*p`, `(q*p)! = p^q * q! * QR(q*p)`. -/
theorem FS (q : ℕ) [hp : Fact p.Prime] : (q * p)! = p ^ q * q ! * QR p (q * p) := by
  have hp0 : 0 < p := hp.out.pos
  have hPdvd : (∏ x ∈ (Finset.Icc 1 (q * p)).filter (fun k => p ∣ k), x) = p ^ q * q ! := by
    have hbij : (∏ x ∈ (Finset.Icc 1 (q * p)).filter (fun k => p ∣ k), x)
              = ∏ j ∈ Finset.Icc 1 q, p * j := by
      refine Finset.prod_bij' (fun x _ => x / p) (fun j _ => p * j) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        dsimp only
        rw [Finset.mem_filter, Finset.mem_Icc] at hx
        obtain ⟨⟨hx1, hx2⟩, hxd⟩ := hx
        rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [Nat.one_le_div_iff hp0]; exact Nat.le_of_dvd (by omega) hxd
        · exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hx2)
      · intro j hj
        dsimp only
        rw [Finset.mem_Icc] at hj
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact Nat.mul_pos hp0 hj.1
        · calc p * j ≤ p * q := Nat.mul_le_mul_left p hj.2
            _ = q * p := Nat.mul_comm p q
        · exact dvd_mul_right p j
      · intro x hx
        dsimp only
        rw [Finset.mem_filter] at hx
        exact Nat.mul_div_cancel' hx.2
      · intro j _
        dsimp only
        exact Nat.mul_div_cancel_left j hp0
      · intro x hx
        dsimp only
        rw [Finset.mem_filter] at hx
        exact (Nat.mul_div_cancel' hx.2).symm
    rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, prod_Icc_id, Nat.card_Icc,
      Nat.add_sub_cancel]
  have key : (q * p)! = (∏ x ∈ (Finset.Icc 1 (q * p)).filter (fun k => p ∣ k), x) * QR p (q * p) := by
    unfold QR
    rw [← prod_Icc_id (q * p)]
    exact (Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (q * p)) (fun k => p ∣ k)
      (fun x => x)).symm
  rw [key, hPdvd]

/-- BLOCK: `QR (a * p^m) = ∏_{j < a} GpN p m j`. -/
theorem QReq (m a : ℕ) (hm : 1 ≤ m) [hp : Fact p.Prime] :
    QR p (a * p ^ m) = ∏ j ∈ Finset.range a, GpN p m j := by
  have hp0 : 0 < p := hp.out.pos
  have hNpos : 0 < p ^ m := pow_pos hp0 m
  have hpN : p ∣ p ^ m := dvd_pow_self p (by omega : m ≠ 0)
  have hbij : (∏ x ∈ (Finset.range a ×ˢ Tset p m), (x.2 + x.1 * p ^ m)) = QR p (a * p ^ m) := by
    unfold QR
    refine Finset.prod_bij' (fun x _ => x.2 + x.1 * p ^ m) (fun k _ => (k / p ^ m, k % p ^ m))
      ?_ ?_ ?_ ?_ ?_
    · -- hi : image in filter
      intro x hx
      dsimp only
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
      simp only [Tset, Finset.mem_filter, Finset.mem_range] at hx1 hx2
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hx2ne : x.2 ≠ 0 := by
        intro h; exact hx2.2 (by rw [h]; exact dvd_zero p)
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · have h1 : x.1 + 1 ≤ a := by omega
        have h2 : (x.1 + 1) * p ^ m ≤ a * p ^ m := Nat.mul_le_mul_right (p ^ m) h1
        have hexp : (x.1 + 1) * p ^ m = x.1 * p ^ m + p ^ m := by ring
        rw [hexp] at h2
        have := hx2.1
        omega
      · intro hdvd
        apply hx2.2
        have hpm : p ∣ x.1 * p ^ m := Dvd.dvd.mul_left hpN x.1
        exact (Nat.dvd_add_right hpm).mp (by rwa [add_comm] at hdvd)
    · -- hj : inverse in product
      intro k hk
      dsimp only
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk1, hk2⟩, hk3⟩ := hk
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_range, Nat.div_lt_iff_lt_mul hNpos]
        rcases lt_or_eq_of_le hk2 with h | h
        · exact h
        · exact absurd (by rw [h]; exact Dvd.dvd.mul_left hpN a) hk3
      · simp only [Tset, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt k hNpos, ?_⟩
        intro hdvd
        apply hk3
        have hkeq : k = p ^ m * (k / p ^ m) + k % p ^ m := (Nat.div_add_mod k (p ^ m)).symm
        rw [hkeq]
        exact dvd_add (Dvd.dvd.mul_right hpN _) hdvd
    · -- left_inv
      intro x hx
      dsimp only
      obtain ⟨_, hx2⟩ := Finset.mem_product.mp hx
      simp only [Tset, Finset.mem_filter, Finset.mem_range] at hx2
      have e1 : (x.2 + x.1 * p ^ m) / p ^ m = x.1 := by
        rw [Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hx2.1, zero_add]
      have e2 : (x.2 + x.1 * p ^ m) % p ^ m = x.2 := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx2.1]
      exact Prod.ext e1 e2
    · -- right_inv
      intro k _
      dsimp only
      exact Nat.mod_add_div' k (p ^ m)
    · -- value compatibility
      intro x _
      rfl
  rw [← hbij, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro i _
  unfold GpN
  apply Finset.prod_congr rfl
  intro t _
  rfl

/-- Casting `Gp` to its Nat version. -/
theorem Gp_cast (m c : ℕ) : Gp p m (c : ℤ) = (GpN p m c : ℤ) := by
  unfold Gp GpN
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro t _
  push_cast
  ring

theorem GpN_pos (m c : ℕ) [hp : Fact p.Prime] : 0 < GpN p m c := by
  unfold GpN
  apply Finset.prod_pos
  intro t ht
  simp only [Tset, Finset.mem_filter, Finset.mem_range] at ht
  rcases Nat.eq_zero_or_pos t with h | h
  · exact absurd (by rw [h]; exact dvd_zero p) ht.2
  · omega

theorem BINOM3 (m : ℕ) (hm : 1 ≤ m) [hp : Fact p.Prime] :
    ((3 * p^m).choose (p^m) : ℤ) * Gp p m 0
      = ((3 * p^(m-1)).choose (p^(m-1)) : ℤ) * Gp p m 2 := by
  have hp0 : 0 < p := hp.out.pos
  have hN : p ^ m = p ^ (m - 1) * p := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  set n := p ^ (m - 1) with hndef
  have FS_N : (p ^ m)! = p ^ n * n ! * QR p (p ^ m) := by
    have h := FS p n
    rwa [← hN] at h
  have FS_2N : (2 * p ^ m)! = p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m) := by
    have h := FS p (2 * n)
    rwa [show 2 * n * p = 2 * p ^ m by rw [hN]; ring] at h
  have FS_3N : (3 * p ^ m)! = p ^ (3 * n) * (3 * n)! * QR p (3 * p ^ m) := by
    have h := FS p (3 * n)
    rwa [show 3 * n * p = 3 * p ^ m by rw [hN]; ring] at h
  have CH3N : (3 * p ^ m).choose (p ^ m) * (p ^ m)! * (2 * p ^ m)! = (3 * p ^ m)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p ^ m ≤ 3 * p ^ m by omega)
    rwa [show 3 * p ^ m - p ^ m = 2 * p ^ m by omega] at h
  have CH3n : (3 * n).choose n * n ! * (2 * n)! = (3 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 3 * n by omega)
    rwa [show 3 * n - n = 2 * n by omega] at h
  have hpow3 : p ^ (3 * n) = p ^ n * p ^ (2 * n) := by rw [← pow_add]; congr 1; ring
  have hK : 0 < p ^ (3 * n) * (n ! * (2 * n)!) :=
    Nat.mul_pos (pow_pos hp0 _) (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have qr1 : QR p (p ^ m) = GpN p m 0 := by
    have h := QReq p m 1 hm
    rw [one_mul] at h
    rw [h, Finset.prod_range_one]
  have qr2 : QR p (2 * p ^ m) = GpN p m 0 * GpN p m 1 := by
    have h := QReq p m 2 hm
    rw [h, show (2:ℕ) = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
  have qr3 : QR p (3 * p ^ m) = GpN p m 0 * GpN p m 1 * GpN p m 2 := by
    have h := QReq p m 3 hm
    rw [h, show (3:ℕ) = 2 + 1 from rfl, Finset.prod_range_succ, show (2:ℕ) = 1 + 1 from rfl,
      Finset.prod_range_succ, Finset.prod_range_one]
  have reduced : (3 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (2 * p ^ m)
               = (3 * n).choose n * QR p (3 * p ^ m) := by
    apply Nat.eq_of_mul_eq_mul_right hK
    calc (3 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (2 * p ^ m)
            * (p ^ (3 * n) * (n ! * (2 * n)!))
        = (3 * p ^ m).choose (p ^ m) * (p ^ n * n ! * QR p (p ^ m))
            * (p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m)) := by rw [hpow3]; ring
      _ = (3 * p ^ m).choose (p ^ m) * (p ^ m)! * (2 * p ^ m)! := by rw [← FS_N, ← FS_2N]
      _ = (3 * p ^ m)! := CH3N
      _ = p ^ (3 * n) * (3 * n)! * QR p (3 * p ^ m) := FS_3N
      _ = p ^ (3 * n) * ((3 * n).choose n * n ! * (2 * n)!) * QR p (3 * p ^ m) := by rw [← CH3n]
      _ = (3 * n).choose n * QR p (3 * p ^ m) * (p ^ (3 * n) * (n ! * (2 * n)!)) := by ring
  rw [qr1, qr2, qr3] at reduced
  have hGpos : 0 < GpN p m 0 * GpN p m 1 := Nat.mul_pos (GpN_pos p m 0) (GpN_pos p m 1)
  have natEq : (3 * p ^ m).choose (p ^ m) * GpN p m 0 = (3 * n).choose n * GpN p m 2 := by
    apply Nat.eq_of_mul_eq_mul_right hGpos
    have hR : (3 * n).choose n * GpN p m 2 * (GpN p m 0 * GpN p m 1)
            = (3 * n).choose n * (GpN p m 0 * GpN p m 1 * GpN p m 2) := by ring
    rw [hR, ← reduced]
  have g0 : Gp p m 0 = (GpN p m 0 : ℤ) := by
    rw [show (0:ℤ) = ((0:ℕ):ℤ) by norm_num]; exact Gp_cast p m 0
  have g2 : Gp p m 2 = (GpN p m 2 : ℤ) := by
    rw [show (2:ℤ) = ((2:ℕ):ℤ) by norm_num]; exact Gp_cast p m 2
  rw [g0, g2]
  exact_mod_cast natEq

theorem BINOM2 (m : ℕ) (hm : 1 ≤ m) [hp : Fact p.Prime] :
    ((2 * p^m).choose (p^m) : ℤ) * Gp p m 0
      = ((2 * p^(m-1)).choose (p^(m-1)) : ℤ) * Gp p m 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hN : p ^ m = p ^ (m - 1) * p := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  set n := p ^ (m - 1) with hndef
  have FS_N : (p ^ m)! = p ^ n * n ! * QR p (p ^ m) := by
    have h := FS p n
    rwa [← hN] at h
  have FS_2N : (2 * p ^ m)! = p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m) := by
    have h := FS p (2 * n)
    rwa [show 2 * n * p = 2 * p ^ m by rw [hN]; ring] at h
  have CH2N : (2 * p ^ m).choose (p ^ m) * (p ^ m)! * (p ^ m)! = (2 * p ^ m)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show p ^ m ≤ 2 * p ^ m by omega)
    rwa [show 2 * p ^ m - p ^ m = p ^ m by omega] at h
  have CH2n : (2 * n).choose n * n ! * n ! = (2 * n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rwa [show 2 * n - n = n by omega] at h
  have hpow2 : p ^ (2 * n) = p ^ n * p ^ n := by rw [← pow_add]; congr 1; ring
  have hK : 0 < p ^ (2 * n) * (n ! * n !) :=
    Nat.mul_pos (pow_pos hp0 _) (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have qr1 : QR p (p ^ m) = GpN p m 0 := by
    have h := QReq p m 1 hm
    rw [one_mul] at h
    rw [h, Finset.prod_range_one]
  have qr2 : QR p (2 * p ^ m) = GpN p m 0 * GpN p m 1 := by
    have h := QReq p m 2 hm
    rw [h, show (2:ℕ) = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
  have reduced : (2 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (p ^ m)
               = (2 * n).choose n * QR p (2 * p ^ m) := by
    apply Nat.eq_of_mul_eq_mul_right hK
    calc (2 * p ^ m).choose (p ^ m) * QR p (p ^ m) * QR p (p ^ m)
            * (p ^ (2 * n) * (n ! * n !))
        = (2 * p ^ m).choose (p ^ m) * (p ^ n * n ! * QR p (p ^ m))
            * (p ^ n * n ! * QR p (p ^ m)) := by rw [hpow2]; ring
      _ = (2 * p ^ m).choose (p ^ m) * (p ^ m)! * (p ^ m)! := by rw [← FS_N]
      _ = (2 * p ^ m)! := CH2N
      _ = p ^ (2 * n) * (2 * n)! * QR p (2 * p ^ m) := FS_2N
      _ = p ^ (2 * n) * ((2 * n).choose n * n ! * n !) * QR p (2 * p ^ m) := by rw [← CH2n]
      _ = (2 * n).choose n * QR p (2 * p ^ m) * (p ^ (2 * n) * (n ! * n !)) := by ring
  rw [qr1, qr2] at reduced
  have natEq : (2 * p ^ m).choose (p ^ m) * GpN p m 0 = (2 * n).choose n * GpN p m 1 := by
    apply Nat.eq_of_mul_eq_mul_right (GpN_pos p m 0)
    have hR : (2 * n).choose n * GpN p m 1 * GpN p m 0
            = (2 * n).choose n * (GpN p m 0 * GpN p m 1) := by ring
    rw [hR, ← reduced]
  have g0 : Gp p m 0 = (GpN p m 0 : ℤ) := by
    rw [show (0:ℤ) = ((0:ℕ):ℤ) by norm_num]; exact Gp_cast p m 0
  have g1 : Gp p m 1 = (GpN p m 1 : ℤ) := by
    rw [show (1:ℤ) = ((1:ℕ):ℤ) by norm_num]; exact Gp_cast p m 1
  rw [g0, g1]
  exact_mod_cast natEq

theorem kummer3 (k : ℕ) : (3 * 3^k).choose (3^k) ≡ 0 [MOD 3] := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction k with
  | zero => decide
  | succ j ih =>
    have hstep := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 3*3^(j+1)) (k := 3^(j+1)) (p := 3)
    have hpn : 3*3^(j+1) = 3*(3^(j+1)) := by ring
    have e1 : 3*3^(j+1) % 3 = 0 := by rw [hpn, Nat.mul_mod_right]
    have e2 : 3*3^(j+1) / 3 = 3^(j+1) := by rw [hpn, Nat.mul_div_cancel_left _ (by norm_num)]
    have e3 : 3^(j+1) % 3 = 0 := by
      have : 3^(j+1) = 3*3^j := by ring
      rw [this, Nat.mul_mod_right]
    have e4 : 3^(j+1) / 3 = 3^j := by
      have : 3^(j+1) = 3*3^j := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e1, e2, e3, e4] at hstep
    simp only [Nat.choose_zero_right, one_mul] at hstep
    have hre : (3^(j+1)).choose (3^j) = (3*3^j).choose (3^j) := by
      congr 1; ring
    rw [hre] at hstep
    exact hstep.trans ih

theorem KUMMER (k : ℕ) [hp : Fact p.Prime] :
    (p:ℤ)^(wv p) ∣ ((3 * p^k).choose (p^k) : ℤ) := by
  unfold wv
  split
  · rename_i h; subst h
    simp only [pow_one]
    have hz : (3 * 3^k).choose (3^k) ≡ 0 [MOD 3] := kummer3 k
    have : (3:ℕ) ∣ (3 * 3^k).choose (3^k) := (Nat.modEq_zero_iff_dvd).mp hz
    exact_mod_cast this
  · simp

theorem central_mod (k : ℕ) [hp : Fact p.Prime] :
    (2*p^k).choose (p^k) ≡ 2 [MOD p] := by
  induction k with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    have hstep := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2*p^(n+1)) (k := p^(n+1)) (p := p)
    have hpn : 2*p^(n+1) = p*(2*p^n) := by ring
    have hqn : p^(n+1) = p*p^n := by ring
    have e1 : 2*p^(n+1) % p = 0 := by rw [hpn, Nat.mul_mod_right]
    have e2 : 2*p^(n+1) / p = 2*p^n := by rw [hpn, Nat.mul_div_cancel_left _ (hp.out.pos)]
    have e3 : p^(n+1) % p = 0 := by rw [hqn, Nat.mul_mod_right]
    have e4 : p^(n+1) / p = p^n := by rw [hqn, Nat.mul_div_cancel_left _ (hp.out.pos)]
    rw [e1, e2, e3, e4] at hstep
    simp only [Nat.choose_self, one_mul] at hstep
    exact hstep.trans ih

theorem CENTRAL (k : ℕ) (hp3 : 3 ≤ p) [hp : Fact p.Prime] : ¬ (p:ℤ) ∣ ((2 * p^k).choose (p^k) : ℤ) := by
  intro hd
  have hn : (p:ℕ) ∣ (2 * p^k).choose (p^k) := by exact_mod_cast hd
  have hz : (2 * p^k).choose (p^k) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hn
  have h2 : (2 : ℕ) ≡ 0 [MOD p] := (central_mod p k).symm.trans hz
  have hp2 : p ∣ 2 := (Nat.modEq_zero_iff_dvd).mp h2
  have := Nat.le_of_dvd (by norm_num) hp2
  omega

theorem LEVEL_DIFF (m : ℕ) (hm : 1 ≤ m) (c : ℤ) (hc : c = 1 ∨ c = 2) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*m - wv p) ∣ (Gp p m c - Gp p m 0) :=
  _root_.LEVEL_DIFF p m hm c hc hp3

theorem CORE (m : ℕ) (hm : 2 ≤ m) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*m+3) ∣ (Gp p m 2 * (Gp p m 0)^2 - (Gp p m 1)^3) :=
  _root_.CORE p m hm hp3

/-! ## Generic divisibility helpers. -/

theorem pcancel [hp : Fact p.Prime] {b c : ℤ} {m : ℕ} (hb : ¬ (p:ℤ) ∣ b)
    (h : (p:ℤ)^m ∣ b * c) : (p:ℤ)^m ∣ c := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime ((p:ℤ)^m) b := (hpp.coprime_iff_not_dvd.mpr hb).pow_left
  exact hcop.dvd_of_dvd_mul_left h

theorem extract3 [hp : Fact p.Prime] {c : ℤ} {m : ℕ}
    (h : (p:ℤ)^m ∣ 3 * c) : (p:ℤ)^(m-1) ∣ c := by
  rcases eq_or_ne p 3 with h3 | h3
  · subst h3
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      have hpow : ((3:ℕ):ℤ)^m = 3 * ((3:ℕ):ℤ)^(m-1) := by
        rw [show m = (m-1)+1 by omega, pow_succ]; push_cast; ring
      rw [hpow] at hk
      have h3ne : (3:ℤ) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3ne; push_cast at hk ⊢; linarith [hk]
  · have hnd : ¬ (p:ℤ) ∣ 3 := by
      have hn : ¬ p ∣ 3 := by
        intro hd; rcases (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hd; exact h3 rfl
      intro hd; exact hn (by exact_mod_cast hd)
    exact dvd_trans (pow_dvd_pow _ (Nat.sub_le m 1)) (pcancel p hnd h)

theorem pmul {a b : ℕ} {x y : ℤ} (hx : (p:ℤ)^a ∣ x) (hy : (p:ℤ)^b ∣ y) :
    (p:ℤ)^(a+b) ∣ x * y := by rw [pow_add]; exact mul_dvd_mul hx hy

theorem dvdK {a K : ℕ} {x : ℤ} (hx : (p:ℤ)^a ∣ x) (h : K ≤ a) : (p:ℤ)^K ∣ x :=
  dvd_trans (pow_dvd_pow _ h) hx

theorem hwle : wv p ≤ 1 := by unfold wv; split <;> norm_num

theorem pw_dvd_3 : (p:ℤ)^(wv p) ∣ (3:ℤ) := by
  unfold wv; split
  · rename_i h; subst h; norm_num
  · simp

theorem G0cube_unit (m : ℕ) [hp : Fact p.Prime] : ¬ (p:ℤ) ∣ (Gp p m 0)^3 := by
  intro hd
  exact G0_unit p m ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd)

/-! ## Assembly lemma (final integer arithmetic). -/

theorem assembly [hp : Fact p.Prime] (r : ℕ) (hr : 2 ≤ r)
    (A a0 B b0 : ℤ) (hb0 : ¬ (p:ℤ) ∣ b0)
    (H1 : (p:ℤ)^3 ∣ (a0 - 3)) (H2 : (p:ℤ)^3 ∣ 3*(b0 - 2))
    (Fα : (p:ℤ)^(3*r) ∣ (A - a0)) (Fβ : (p:ℤ)^(3*r) ∣ 3*(B - b0))
    (F3 : (p:ℤ)^(3*r+3) ∣ (A*b0^3 - a0*B^3)) :
    (p:ℤ)^(3*r+3) ∣ ((a0^2 - 27*b0) - (A^2 - 27*B)) := by
  set K := 3*r+3 with hK
  set α := A - a0 with hα
  set β := B - b0 with hβ
  have hβ1 : (p:ℤ)^(3*r-1) ∣ β := extract3 p Fβ
  have hα2 : (p:ℤ)^K ∣ α^2 := by
    rw [pow_two]; exact dvdK p (pmul p Fα Fα) (by rw [hK]; omega)
  have hβ2 : (p:ℤ)^K ∣ β^2 := by
    rw [pow_two]; exact dvdK p (pmul p hβ1 hβ1) (by rw [hK]; omega)
  have hβ3 : (p:ℤ)^K ∣ β^3 := by
    have h1 : (p:ℤ)^((3*r-1)+(3*r-1)+(3*r-1)) ∣ β^3 := by
      have e : β^3 = β*β*β := by ring
      rw [e, pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hβ1 hβ1) hβ1
    exact dvdK p h1 (by rw [hK]; omega)
  have hb02 : ¬ (p:ℤ) ∣ b0^2 := by
    intro hd; exact hb0 ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd)
  have HP : (p:ℤ)^K ∣ (α*b0^3 - 3*a0*b0^2*β) := by
    have key : α*b0^3 - 3*a0*b0^2*β = (A*b0^3 - a0*B^3) + 3*a0*b0*β^2 + a0*β^3 := by
      rw [hα, hβ]; ring
    rw [key]
    exact dvd_add (dvd_add F3 (Dvd.dvd.mul_left hβ2 _)) (Dvd.dvd.mul_left hβ3 _)
  have HQ : (p:ℤ)^K ∣ (α*b0 - 3*a0*β) := by
    apply pcancel p hb02
    have : b0^2 * (α*b0 - 3*a0*β) = α*b0^3 - 3*a0*b0^2*β := by ring
    rw [this]; exact HP
  have HR : (p:ℤ)^K ∣ (α*b0 - 9*β) := by
    have t : (p:ℤ)^K ∣ (3*a0*β - 9*β) := by
      have e : 3*a0*β - 9*β = (a0 - 3)*(3*β) := by ring
      rw [e, hK, show 3*r+3 = 3+3*r by ring]; exact pmul p H1 Fβ
    have := dvd_add HQ t
    have e2 : (α*b0 - 3*a0*β) + (3*a0*β - 9*β) = α*b0 - 9*β := by ring
    rwa [e2] at this
  have T3ab : (p:ℤ)^K ∣ (3*α*b0 - 6*α) := by
    have e : 3*α*b0 - 6*α = α*(3*(b0-2)) := by ring
    rw [e, hK]; exact pmul p Fα H2
  have T2aa : (p:ℤ)^K ∣ (2*a0*α - 6*α) := by
    have e : 2*a0*α - 6*α = α*(2*(a0-3)) := by ring
    rw [e]
    have h2 : (p:ℤ)^3 ∣ 2*(a0-3) := Dvd.dvd.mul_left H1 2
    rw [hK]; exact pmul p Fα h2
  have HS : (p:ℤ)^K ∣ (6*α - 27*β) := by
    have h3 : (p:ℤ)^K ∣ (3*α*b0 - 27*β) := by
      have e : 3*α*b0 - 27*β = 3*(α*b0 - 9*β) := by ring
      rw [e]; exact Dvd.dvd.mul_left HR 3
    have := dvd_sub h3 T3ab
    have e2 : (3*α*b0 - 27*β) - (3*α*b0 - 6*α) = 6*α - 27*β := by ring
    rwa [e2] at this
  have main : (p:ℤ)^K ∣ (27*β - 2*a0*α) := by
    have := dvd_add HS T2aa
    have e : (6*α - 27*β) + (2*a0*α - 6*α) = -(27*β - 2*a0*α) := by ring
    rw [e] at this
    exact (dvd_neg).mp this
  have goaleq : ((a0^2 - 27*b0) - (A^2 - 27*B)) = (27*β - 2*a0*α) - α^2 := by
    rw [hα, hβ]; ring
  rw [goaleq]; exact dvd_sub main hα2

/-! ## Telescoping steps. -/

theorem STEP3 (k : ℕ) (hk : 1 ≤ k) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*k) ∣ (((3*p^k).choose (p^k) : ℤ) - ((3*p^(k-1)).choose (p^(k-1)) : ℤ)) := by
  set C3 : ℤ := ((3*p^k).choose (p^k) : ℤ)
  set c3 : ℤ := ((3*p^(k-1)).choose (p^(k-1)) : ℤ)
  have hb := BINOM3 p k hk
  have hprod : (p:ℤ)^(wv p + (3*k - wv p)) ∣ (c3 * (Gp p k 2 - Gp p k 0)) :=
    pmul p (KUMMER p (k-1)) (LEVEL_DIFF p k hk 2 (Or.inr rfl) hp3)
  have hexp : wv p + (3*k - wv p) = 3*k := by have := hwle p; omega
  rw [hexp] at hprod
  have hcast : c3 * (Gp p k 2 - Gp p k 0) = (C3 - c3) * Gp p k 0 := by
    linear_combination -hb
  rw [hcast, mul_comm (C3 - c3) (Gp p k 0)] at hprod
  exact pcancel p (G0_unit p k) hprod

theorem STEP2 (k : ℕ) (hk : 1 ≤ k) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^(3*k - wv p) ∣ (((2*p^k).choose (p^k) : ℤ) - ((2*p^(k-1)).choose (p^(k-1)) : ℤ)) := by
  set C2 : ℤ := ((2*p^k).choose (p^k) : ℤ)
  set c2 : ℤ := ((2*p^(k-1)).choose (p^(k-1)) : ℤ)
  have hb := BINOM2 p k hk
  have hprod : (p:ℤ)^(3*k - wv p) ∣ (c2 * (Gp p k 1 - Gp p k 0)) :=
    Dvd.dvd.mul_left (LEVEL_DIFF p k hk 1 (Or.inl rfl) hp3) c2
  have hcast : c2 * (Gp p k 1 - Gp p k 0) = (C2 - c2) * Gp p k 0 := by
    linear_combination -hb
  rw [hcast, mul_comm (C2 - c2) (Gp p k 0)] at hprod
  exact pcancel p (G0_unit p k) hprod

/-! ## H1, H2 via telescoping induction. -/

theorem H1_gen (j : ℕ) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^3 ∣ (((3*p^j).choose (p^j) : ℤ) - 3) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hstep : (p:ℤ)^3 ∣ (((3*p^(n+1)).choose (p^(n+1)) : ℤ) - ((3*p^n).choose (p^n) : ℤ)) := by
      have := STEP3 p (n+1) (by omega) hp3
      simp only [Nat.add_sub_cancel] at this
      exact dvdK p this (by omega)
    have : (p:ℤ)^3 ∣ ((((3*p^(n+1)).choose (p^(n+1)) : ℤ) - ((3*p^n).choose (p^n) : ℤ))
        + (((3*p^n).choose (p^n) : ℤ) - 3)) := dvd_add hstep ih
    have e : (((3*p^(n+1)).choose (p^(n+1)) : ℤ) - ((3*p^n).choose (p^n) : ℤ))
        + (((3*p^n).choose (p^n) : ℤ) - 3) = ((3*p^(n+1)).choose (p^(n+1)) : ℤ) - 3 := by ring
    rwa [e] at this

theorem H2_gen (j : ℕ) (hp3 : 3 ≤ p) [hp : Fact p.Prime] :
    (p:ℤ)^3 ∣ 3 * (((2*p^j).choose (p^j) : ℤ) - 2) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hstep : (p:ℤ)^3 ∣ 3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ)) := by
      have hd := STEP2 p (n+1) (by omega) hp3
      simp only [Nat.add_sub_cancel] at hd
      have hprod : (p:ℤ)^(wv p + (3*(n+1) - wv p)) ∣
          3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ)) :=
        pmul p (pw_dvd_3 p) hd
      have hexp : wv p + (3*(n+1) - wv p) = 3*(n+1) := by have := hwle p; omega
      rw [hexp] at hprod
      exact dvdK p hprod (by omega)
    have : (p:ℤ)^3 ∣ (3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ))
        + 3 * (((2*p^n).choose (p^n) : ℤ) - 2)) := dvd_add hstep ih
    have e : (3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - ((2*p^n).choose (p^n) : ℤ))
        + 3 * (((2*p^n).choose (p^n) : ℤ) - 2))
        = 3 * (((2*p^(n+1)).choose (p^(n+1)) : ℤ) - 2) := by ring
    rwa [e] at this

/-! ## The main theorem-input package. -/

theorem main_dvd [hp : Fact p.Prime] (r : ℕ) (hr : 2 ≤ r) (hp3 : 3 ≤ p) :
    (p:ℤ)^(3*r+3) ∣
      ((((3*p^(r-1)).choose (p^(r-1)) : ℤ)^2 - 27*((2*p^(r-1)).choose (p^(r-1)) : ℤ))
        - (((3*p^r).choose (p^r) : ℤ)^2 - 27*((2*p^r).choose (p^r) : ℤ))) := by
  set A : ℤ := ((3*p^r).choose (p^r) : ℤ) with hA
  set a0 : ℤ := ((3*p^(r-1)).choose (p^(r-1)) : ℤ) with ha0
  set B : ℤ := ((2*p^r).choose (p^r) : ℤ) with hB
  set b0 : ℤ := ((2*p^(r-1)).choose (p^(r-1)) : ℤ) with hb0def
  -- hb0
  have hb0 : ¬ (p:ℤ) ∣ b0 := CENTRAL p (r-1) hp3
  -- H1
  have H1 : (p:ℤ)^3 ∣ (a0 - 3) := H1_gen p (r-1) hp3
  -- H2
  have H2 : (p:ℤ)^3 ∣ 3*(b0 - 2) := H2_gen p (r-1) hp3
  -- Fα
  have Fα : (p:ℤ)^(3*r) ∣ (A - a0) := by
    exact STEP3 p r (by omega) hp3
  -- Fβ
  have Fβ : (p:ℤ)^(3*r) ∣ 3*(B - b0) := by
    have hd := STEP2 p r (by omega) hp3
    have hprod : (p:ℤ)^(wv p + (3*r - wv p)) ∣ 3*(B - b0) := pmul p (pw_dvd_3 p) hd
    have hexp : wv p + (3*r - wv p) = 3*r := by have := hwle p; omega
    rwa [hexp] at hprod
  -- F3
  have F3 : (p:ℤ)^(3*r+3) ∣ (A*b0^3 - a0*B^3) := by
    have hcore := CORE p r hr hp3
    have h3 := BINOM3 p r (by omega)
    have h2 := BINOM2 p r (by omega)
    -- multiply core by a0*b0^3
    have hmul : (p:ℤ)^(3*r+3) ∣ (a0*b0^3*(Gp p r 2 * (Gp p r 0)^2 - (Gp p r 1)^3)) :=
      Dvd.dvd.mul_left hcore _
    have hid : a0*b0^3*(Gp p r 2 * (Gp p r 0)^2 - (Gp p r 1)^3)
        = (Gp p r 0)^3 * (A*b0^3 - a0*B^3) := by
      linear_combination (-(b0^3)*(Gp p r 0)^2) * h3
        + a0*((B*Gp p r 0)^2 + (B*Gp p r 0)*(b0*Gp p r 1) + (b0*Gp p r 1)^2) * h2
    rw [hid] at hmul
    exact pcancel p (G0cube_unit p r) hmul
  exact assembly p r hr A a0 B b0 hb0 H1 H2 Fα Fβ F3

/-! ## Connection to the Spec goal (test). -/

def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

theorem spec_test (r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Int.modEq_iff_dvd]
  have := main_dvd p r hr hp3
  simp only [a, Int.ofNat_eq_natCast]
  convert this using 2

end Work

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] :=
by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Int.modEq_iff_dvd]
  have := Work.main_dvd p r hr hp3
  simp only [a, Int.ofNat_eq_natCast]
  convert this using 2
