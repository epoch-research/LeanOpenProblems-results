import FormalConjectures.Util.ProblemImports
open Finset
variable {p : ℕ}

theorem mulu_cancel {R : Type*} [CommRing R] {u a b : R} (hu : IsUnit u) (h : a * u = b * u) :
    a = b := by
  obtain ⟨w, rfl⟩ := hu
  have h2 : a * (w:R) * (↑w⁻¹) = b * (w:R) * ↑w⁻¹ := by rw [h]
  simpa [mul_assoc, Units.mul_inv] using h2

namespace A374605
noncomputable def cc (p k : ℕ) : ZMod (p^3) := 0
axiom ratioZ (p : ℕ) (hp5 : 5 ≤ p) (k : ℕ) (hk : k ≤ p-1) :
    (((k:ZMod (p^3))+1)^3*(2*(p:ZMod (p^3))+2*k-1)*(2*(p:ZMod (p^3))+2*k)) * cc p (k+1)
      = (((p:ZMod (p^3))-1-k)^2*((p:ZMod (p^3))+k)*(3*(p:ZMod (p^3))+2*k-2)*(3*(p:ZMod (p^3))+2*k-1)) * cc p k
axiom c1_val (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    cc p 1 = (p:ZMod (p^3))*((p:ZMod (p^3))-1)^2

lemma huni3 (p m : ℕ) (hp : Nat.Prime p) (h : ¬ p ∣ m) : IsUnit ((m:ℕ):ZMod (p^3)) :=
  (ZMod.isUnit_iff_coprime m (p^3)).mpr
    (Nat.Coprime.pow_right 3 (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr h)))

lemma pndvd_lt {p m : ℕ} (h0 : 0 < m) (hlt : m < p) : ¬ p ∣ m := fun hd => by
  have := Nat.le_of_dvd h0 hd; omega

lemma pndvd_res {p : ℕ} (q r m : ℕ) (hm : m = q * p + r) (h0 : 0 < r) (hlt : r < p) :
    ¬ p ∣ m := by
  subst hm; intro hd
  have hr : p ∣ r := (Nat.dvd_add_right (dvd_mul_left p q)).mp hd
  have := Nat.le_of_dvd h0 hr; omega

lemma pnd16 {p : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) : ¬ p ∣ 16 := by
  intro hd
  have : p ∣ 2 := hp.dvd_of_dvd_pow (n := 4) (by rwa [show (2:ℕ)^4 = 16 by norm_num])
  have := Nat.le_of_dvd (by norm_num) this; omega

set_option maxHeartbeats 1600000 in
lemma invA (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (k : ℕ) (hk2 : 2 ≤ k) :
    k ≤ (p+1)/2 →
    2*(k:ZMod (p^3))*((k:ZMod (p^3))-1)*cc p k = 3*(p:ZMod (p^3))^2 := by
  have hp30 : ((p:ZMod (p^3)))^3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  induction k, hk2 using Nat.le_induction with
  | base =>
   intro _
   have hc1 := c1_val p hp hp5
   have hr1 := ratioZ p hp5 1 (by omega)
   have hA1u : IsUnit ((32*(p:ZMod (p^3))^2 + 48*(p:ZMod (p^3)) + 16) : ZMod (p^3)) := by
     have e1 : (32*(p:ZMod (p^3))^2 + 48*(p:ZMod (p^3)) + 16)
         = (((16*(2*p+1)*(p+1) : ℕ)):ZMod (p^3)) := by push_cast; ring
     rw [e1]; apply huni3 p _ hp
     intro hd; rw [hp.dvd_mul, hp.dvd_mul] at hd
     rcases hd with (h|h)|h
     · exact pnd16 hp hp5 h
     · exact pndvd_res 2 1 (2*p+1) (by ring) (by norm_num) (by omega) h
     · exact pndvd_res 1 1 (p+1) (by ring) (by norm_num) (by omega) h
   apply mulu_cancel hA1u
   push_cast at hr1 hc1 ⊢
   linear_combination 4*hr1 + (4*(9*(p:ZMod (p^3))^5 - 24*(p:ZMod (p^3))^4 - 9*(p:ZMod (p^3))^3 + 36*(p:ZMod (p^3))^2 + 12*(p:ZMod (p^3))))*hc1 + (36*(p:ZMod (p^3))^5 - 168*(p:ZMod (p^3))^4 + 192*(p:ZMod (p^3))^3 + 120*(p:ZMod (p^3))^2 - 372*(p:ZMod (p^3)) - 96)*hp30
  | succ k hk2 IH =>
   intro hub
   have hubk : k ≤ (p+1)/2 := by omega
   have IHk := IH hubk
   have hkp : k ≤ p - 1 := by omega
   have hr := ratioZ p hp5 k hkp
   have hUu : IsUnit (((k:ZMod (p^3))-1)*((k:ZMod (p^3))+1)^3*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3)))) := by
     have e1 : ((k:ZMod (p^3))-1)*((k:ZMod (p^3))+1)^3*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3))-1)*(2*(p:ZMod (p^3))+2*(k:ZMod (p^3)))
         = ((( (k-1)*(k+1)^3*(2*p+2*k-1)*(2*p+2*k) : ℕ)):ZMod (p^3)) := by
       have hk1 : (1:ℕ) ≤ k := by omega
       push_cast [Nat.cast_sub hk1, Nat.cast_sub (show (1:ℕ) ≤ 2*p+2*k by omega)]
       ring
     rw [e1]; apply huni3 p _ hp
     intro hd
     rw [hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at hd
     rcases hd with (((h|h)|h)|h)
     · exact pndvd_lt (by omega) (by omega) h
     · exact pndvd_lt (by omega) (by omega) (hp.dvd_of_dvd_pow h)
     · exact pndvd_res 2 (2*k-1) (2*p+2*k-1) (by omega) (by omega) (by omega) h
     · exact pndvd_res 2 (2*k) (2*p+2*k) (by ring) (by omega) (by omega) h
   apply mulu_cancel hUu
   push_cast at hr IHk ⊢
   linear_combination (2*((k:ZMod (p^3))+1)*(k:ZMod (p^3))*((k:ZMod (p^3))-1))*hr + (((k:ZMod (p^3))+1)*(4*(k:ZMod (p^3))^5 + 8*(k:ZMod (p^3))^4*(p:ZMod (p^3)) + 2*(k:ZMod (p^3))^4 - 7*(k:ZMod (p^3))^3*(p:ZMod (p^3))^2 + 21*(k:ZMod (p^3))^3*(p:ZMod (p^3)) - 6*(k:ZMod (p^3))^3 - 17*(k:ZMod (p^3))^2*(p:ZMod (p^3))^3 + 25*(k:ZMod (p^3))^2*(p:ZMod (p^3))^2 - 4*(k:ZMod (p^3))^2*(p:ZMod (p^3)) - 2*(k:ZMod (p^3))^2 + 3*(k:ZMod (p^3))*(p:ZMod (p^3))^4 - 21*(k:ZMod (p^3))*(p:ZMod (p^3))^3 + 31*(k:ZMod (p^3))*(p:ZMod (p^3))^2 - 15*(k:ZMod (p^3))*(p:ZMod (p^3)) + 2*(k:ZMod (p^3)) + 9*(p:ZMod (p^3))^5 - 27*(p:ZMod (p^3))^4 + 29*(p:ZMod (p^3))^3 - 13*(p:ZMod (p^3))^2 + 2*(p:ZMod (p^3))))*IHk + (3*(-11*(k:ZMod (p^3))^4*(p:ZMod (p^3)) + 15*(k:ZMod (p^3))^4 - 17*(k:ZMod (p^3))^3*(p:ZMod (p^3))^2 + 10*(k:ZMod (p^3))^3*(p:ZMod (p^3)) + 21*(k:ZMod (p^3))^3 + 3*(k:ZMod (p^3))^2*(p:ZMod (p^3))^3 - 38*(k:ZMod (p^3))^2*(p:ZMod (p^3))^2 + 56*(k:ZMod (p^3))^2*(p:ZMod (p^3)) - 3*(k:ZMod (p^3))^2 + 9*(k:ZMod (p^3))*(p:ZMod (p^3))^4 - 24*(k:ZMod (p^3))*(p:ZMod (p^3))^3 + 8*(k:ZMod (p^3))*(p:ZMod (p^3))^2 + 26*(k:ZMod (p^3))*(p:ZMod (p^3)) - 9*(k:ZMod (p^3)) + 9*(p:ZMod (p^3))^4 - 27*(p:ZMod (p^3))^3 + 29*(p:ZMod (p^3))^2 - 9*(p:ZMod (p^3))))*hp30


end A374605
