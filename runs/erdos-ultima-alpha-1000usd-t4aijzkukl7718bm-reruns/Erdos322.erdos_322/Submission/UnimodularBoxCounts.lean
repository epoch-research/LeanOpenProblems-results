import Submission.UnimodularRootCRT

/-! Box counts and common-divisor bounds for unimodular congruence roots. -/
namespace Erdos322Research.UnimodularBoxCounts
noncomputable section
open Finset UnimodularRootCRT
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

abbrev BoxRoots (k q B : ℕ) := {x : Fin k → Fin B //
  (∑ i, ((x i : ℕ) : ZMod q)^k=0) ∧ Unimodular (fun i ↦ ((x i : ℕ) : ZMod q))}

abbrev Divisible (k q B d : ℕ) := {x : BoxRoots k q B // ∀ i, d ∣ (x.val i : ℕ)}

def boxCount (k q B : ℕ) : ℕ := Fintype.card (BoxRoots k q B)

def divisorCount (k q B d : ℕ) : ℕ := Fintype.card (Divisible k q B d)

def coordGCD {k B : ℕ} (x : Fin k → Fin B) : ℕ := univ.gcd (fun i ↦ (x i : ℕ))

def primitiveBoxCount (k q B : ℕ) : ℕ :=
  Fintype.card {x : BoxRoots k q B // coordGCD x.val=1}

lemma lift_lower (k q T : ℕ) [NeZero q] :
    count k q*T^k ≤ boxCount k q (q*T) := by
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  let f : URoots k (ZMod q) × (Fin k → Fin T) → BoxRoots k q (q*T) := fun z ↦
    ⟨fun i ↦ ⟨(z.1.val i).val+q*(z.2 i : ℕ),by
      have hi := ZMod.val_lt (z.1.val i)
      have ht := (z.2 i).isLt
      nlinarith⟩,by
      have he (i) : (((z.1.val i).val+q*(z.2 i : ℕ) : ℕ) : ZMod q)=z.1.val i := by
        simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val]
      simpa only [he] using z.1.property⟩
  have hf : Function.Injective f := by
    rintro ⟨a,x⟩ ⟨b,y⟩ h
    have he (i) : (a.val i).val+q*(x i : ℕ)=(b.val i).val+q*(y i : ℕ) :=
      congrArg (fun z : BoxRoots k q (q*T) ↦ (z.val i : ℕ)) h
    have hab : a=b := by
      apply Subtype.ext
      funext i
      have hh := congrArg (fun n : ℕ ↦ (n : ZMod q)) (he i)
      simpa only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val] using hh
    subst b
    refine Prod.ext rfl ?_
    funext i
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel (he i))
  have hh := Fintype.card_le_of_injective f hf
  simpa only [count,boxCount,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using hh

lemma divided_is_root (k q B d : ℕ) (x : Divisible k q B d) :
    (∑ i, ((x.val.val i : ℕ)/d : ZMod q)^k=0) ∧
      Unimodular (fun i ↦ ((x.val.val i : ℕ)/d : ZMod q)) := by
  let y : Fin k → ZMod q := fun i ↦ ((x.val.val i : ℕ)/d : ℕ)
  have he (i) : ((x.val.val i : ℕ) : ZMod q)=(d : ZMod q)*y i := by
    dsimp only [y]
    rw [← Nat.cast_mul,Nat.mul_div_cancel' (x.property i)]
  obtain ⟨a,ha⟩ := x.val.property.2
  have hu : (d : ZMod q)*(∑ i, a i*y i)=1 := by
    calc
      (d : ZMod q)*(∑ i, a i*y i)=∑ i, a i*((d : ZMod q)*y i) := by rw [mul_sum]; congr 1; funext i; ring
      _ = 1 := by simpa only [← he] using ha
  have hd : IsUnit (d : ZMod q) := IsUnit.of_mul_eq_one _ hu
  constructor
  · have hh := x.val.property.1
    simp only [he,mul_pow,← mul_sum] at hh
    change (∑ i, y i^k)=0
    exact (hd.pow k).mul_left_cancel (by simpa only [mul_zero] using hh)
  · refine ⟨fun i ↦ a i*(d : ZMod q),?_⟩
    change ∑ i, (a i*(d : ZMod q))*y i=1
    simpa only [mul_assoc,← he] using ha

/-- The modular root factor is retained when dividing a common factor out. -/
theorem divisor_bound_modular (k q B d : ℕ) [NeZero q] :
    divisorCount k q B d ≤ count k q*(B/(d*q)+1)^k := by
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  let f : Divisible k q B d → URoots k (ZMod q) × (Fin k → Fin (B/(d*q)+1)) := fun x ↦
    (⟨fun i ↦ ((x.val.val i : ℕ)/d : ℕ),divided_is_root k q B d x⟩,
      fun i ↦ ⟨((x.val.val i : ℕ)/d)/q,by
        rw [Nat.div_div_eq_div_mul]
        exact Nat.lt_succ_of_le (Nat.div_le_div_right (x.val.val i).isLt.le)⟩)
  have hf : Function.Injective f := by
    intro x y h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hr : (x.val.val i : ℕ)/d%q=(y.val.val i : ℕ)/d%q := by
      have hh := congrArg (fun z : URoots k (ZMod q) ↦ (z.val i).val) h0
      simpa only [f,ZMod.val_natCast] using hh
    have ht : (x.val.val i : ℕ)/d/q=(y.val.val i : ℕ)/d/q := by
      exact congrArg (fun z : Fin k → Fin (B/(d*q)+1) ↦ (z i : ℕ)) h1
    have he : (x.val.val i : ℕ)/d=(y.val.val i : ℕ)/d := by
      calc
        (x.val.val i : ℕ)/d = (x.val.val i : ℕ)/d%q+q*((x.val.val i : ℕ)/d/q) :=
          (Nat.mod_add_div _ _).symm
        _ = (y.val.val i : ℕ)/d%q+q*((y.val.val i : ℕ)/d/q) := by rw [hr,ht]
        _ = (y.val.val i : ℕ)/d := Nat.mod_add_div _ _
    calc
      (x.val.val i : ℕ)=d*((x.val.val i : ℕ)/d) := (Nat.mul_div_cancel' (x.property i)).symm
      _ = d*((y.val.val i : ℕ)/d) := by rw [he]
      _ = (y.val.val i : ℕ) := Nat.mul_div_cancel' (y.property i)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [divisorCount,count,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin] using hh

/-- A coarser bound without the modular root factor is useful for large divisors. -/
theorem divisor_bound_box (k q B d : ℕ) :
    divisorCount k q B d ≤ (B/d+1)^k := by
  let f : Divisible k q B d → (Fin k → Fin (B/d+1)) := fun x i ↦
    ⟨(x.val.val i : ℕ)/d,Nat.lt_succ_of_le (Nat.div_le_div_right (x.val.val i).isLt.le)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    have he : (x.val.val i : ℕ)/d=(y.val.val i : ℕ)/d :=
      congrArg (fun z : Fin k → Fin (B/d+1) ↦ (z i : ℕ)) h
    calc
      (x.val.val i : ℕ)=d*((x.val.val i : ℕ)/d) := (Nat.mul_div_cancel' (x.property i)).symm
      _ = d*((y.val.val i : ℕ)/d) := by rw [he]
      _ = (y.val.val i : ℕ) := Nat.mul_div_cancel' (y.property i)
  have hh := Fintype.card_le_of_injective f hf
  simpa only [divisorCount,Fintype.card_fun,Fintype.card_fin] using hh

lemma has_nonzero_coordinate (k q B : ℕ) (hq : 1<q) (x : BoxRoots k q B) :
    ∃ i, (x.val i : ℕ)≠0 := by
  by_contra h
  push_neg at h
  obtain ⟨a,ha⟩ := x.property.2
  simp only [h,Nat.cast_zero,mul_zero,Finset.sum_const_zero] at ha
  have hd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).mp (by simpa using ha.symm)
  have := Nat.le_of_dvd (by omega : 0<1) hd
  omega

/-- A union bound over common divisors covers every nonprimitive tuple. -/
theorem box_le_primitive_add_divisors (k q B : ℕ) (hq : 1<q) :
    boxCount k q B ≤ primitiveBoxCount k q B+∑ d ∈ Icc 2 B, divisorCount k q B d := by
  let N := {x : BoxRoots k q B // coordGCD x.val ≠ 1}
  have hcoord (x : N) : coordGCD x.val.val ∈ Icc 2 B := by
    obtain ⟨i,hi⟩ := has_nonzero_coordinate k q B hq x.val
    have hd : coordGCD x.val.val ∣ (x.val.val i : ℕ) := Finset.gcd_dvd (mem_univ i)
    have hg0 : coordGCD x.val.val ≠ 0 := by
      intro h
      rw [h,zero_dvd_iff] at hd
      exact hi hd
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hd
    exact mem_Icc.mpr ⟨by have := x.property; omega,by have := (x.val.val i).isLt; omega⟩
  let f : N → Σ d : (Icc 2 B : Finset ℕ), Divisible k q B d.val := fun x ↦
    ⟨⟨coordGCD x.val.val,hcoord x⟩,x.val,fun i ↦ Finset.gcd_dvd (mem_univ i)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Σ d : (Icc 2 B : Finset ℕ), Divisible k q B d.val ↦ z.2.val) h
  have hn := Fintype.card_le_of_injective f hf
  have hn' : Fintype.card N ≤ ∑ d ∈ Icc 2 B, divisorCount k q B d := by
    rw [Fintype.card_sigma] at hn
    convert hn using 1
    exact (Finset.sum_coe_sort (Icc 2 B) (fun d ↦ divisorCount k q B d)).symm
  have he := Fintype.card_subtype_compl (fun x : BoxRoots k q B ↦ coordGCD x.val=1)
  have hle := Fintype.card_subtype_le (fun x : BoxRoots k q B ↦ coordGCD x.val=1)
  change Fintype.card N=boxCount k q B-primitiveBoxCount k q B at he
  change primitiveBoxCount k q B ≤ boxCount k q B at hle
  omega

end
end Erdos322Research.UnimodularBoxCounts
