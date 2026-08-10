import FormalConjectures.Util.ProblemImports
open Finset

noncomputable def T (n k : ℕ) : ℕ :=
  (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

-- elementary single-shift building blocks (over ℕ), no nat subtraction

-- (n+k+1).choose k * (n+1) = (n+k).choose k * (n+k+1)
theorem shiftB (n k : ℕ) :
    (Nat.choose (n + k + 1) k) * (n + 1) = (Nat.choose (n + k) k) * (n + k + 1) := by
  have h := Nat.choose_mul_succ_eq (n + k) k
  -- h : (n+k).choose k * (n+k+1) = (n+k+1).choose k * (n+k+1-k)
  have hs : n + k + 1 - k = n + 1 := by omega
  rw [hs] at h
  omega

-- ((k+e+1).choose k) * (e+1) = ((k+e).choose k) * (k+e+1)
theorem shiftA0 (k e : ℕ) :
    (Nat.choose (k + e + 1) k) * (e + 1) = (Nat.choose (k + e) k) * (k + e + 1) := by
  have h := Nat.choose_mul_succ_eq (k + e) k
  have hs : k + e + 1 - k = e + 1 := by omega
  rw [hs] at h
  omega

-- cC' : (n+d+3).choose (n+1) * ((n+1)*(d+1)*(d+2)) = (n+d).choose n * ((n+d+1)*(n+d+2)*(n+d+3))
theorem cC' (n d : ℕ) :
    (Nat.choose (n + d + 3) (n + 1)) * ((n + 1) * (d + 1) * (d + 2))
      = (Nat.choose (n + d) n) * ((n + d + 1) * (n + d + 2) * (n + d + 3)) := by
  -- ci : (n+d+1).choose (n+1) * (n+1) = (n+d+1) * (n+d).choose n
  have ci : (Nat.choose (n + d + 1) (n + 1)) * (n + 1) = (n + d + 1) * (Nat.choose (n + d) n) := by
    have h := Nat.succ_mul_choose_eq (n + d) n
    -- h : (n+d).succ * (n+d).choose n = (n+d).succ.choose (n.succ) * n.succ
    simp only [Nat.succ_eq_add_one] at h
    have e1 : n + d + 1 = (n + d) + 1 := rfl
    omega
  -- cii : (n+d+1).choose (n+1) * (n+d+2) = (n+d+2).choose (n+1) * (d+1)
  have cii : (Nat.choose (n + d + 1) (n + 1)) * (n + d + 2) = (Nat.choose (n + d + 2) (n + 1)) * (d + 1) := by
    have h := Nat.choose_mul_succ_eq (n + d + 1) (n + 1)
    have hs : n + d + 1 + 1 - (n + 1) = d + 1 := by omega
    rw [hs] at h
    have : n + d + 1 + 1 = n + d + 2 := by omega
    rw [this] at h
    omega
  -- ciii : (n+d+2).choose (n+1) * (n+d+3) = (n+d+3).choose (n+1) * (d+2)
  have ciii : (Nat.choose (n + d + 2) (n + 1)) * (n + d + 3) = (Nat.choose (n + d + 3) (n + 1)) * (d + 2) := by
    have h := Nat.choose_mul_succ_eq (n + d + 2) (n + 1)
    have hs : n + d + 2 + 1 - (n + 1) = d + 2 := by omega
    rw [hs] at h
    have : n + d + 2 + 1 = n + d + 3 := by omega
    rw [this] at h
    omega
  -- combine over ℤ
  have ciZ : ((Nat.choose (n + d + 1) (n + 1)):ℤ) * (n + 1) = (n + d + 1) * (Nat.choose (n + d) n) := by exact_mod_cast ci
  have ciiZ : ((Nat.choose (n + d + 1) (n + 1)):ℤ) * (n + d + 2) = (Nat.choose (n + d + 2) (n + 1)) * (d + 1) := by exact_mod_cast cii
  have ciiiZ : ((Nat.choose (n + d + 2) (n + 1)):ℤ) * (n + d + 3) = (Nat.choose (n + d + 3) (n + 1)) * (d + 2) := by exact_mod_cast ciii
  have goalZ : ((Nat.choose (n + d + 3) (n + 1)):ℤ) * ((n + 1) * (d + 1) * (d + 2))
      = (Nat.choose (n + d) n) * ((n + d + 1) * (n + d + 2) * (n + d + 3)) := by
    linear_combination (((n:ℤ)+d+2)*((n:ℤ)+d+3)) * ciZ - (((n:ℤ)+1)*((n:ℤ)+d+3)) * ciiZ - (((n:ℤ)+1)*((d:ℤ)+1)) * ciiiZ
  exact_mod_cast goalZ

-- shiftTop2 : C(r+d+2,r) (d+1)(d+2) = C(r+d,r) (r+d+1)(r+d+2)
theorem shiftTop2 (r d : ℕ) :
    (Nat.choose (r + d + 2) r) * ((d + 1) * (d + 2))
      = (Nat.choose (r + d) r) * ((r + d + 1) * (r + d + 2)) := by
  have ci : (Nat.choose (r + d + 1) r) * (d + 1) = (Nat.choose (r + d) r) * (r + d + 1) := by
    have h := Nat.choose_mul_succ_eq (r + d) r
    have hs : r + d + 1 - r = d + 1 := by omega
    rw [hs] at h; omega
  have cii : (Nat.choose (r + d + 2) r) * (d + 2) = (Nat.choose (r + d + 1) r) * (r + d + 2) := by
    have h := Nat.choose_mul_succ_eq (r + d + 1) r
    have hs : r + d + 1 + 1 - r = d + 2 := by omega
    rw [hs] at h
    have : r + d + 1 + 1 = r + d + 2 := by omega
    rw [this] at h; omega
  have ciZ : ((Nat.choose (r + d + 1) r):ℤ) * (d + 1) = (Nat.choose (r + d) r) * (r + d + 1) := by exact_mod_cast ci
  have ciiZ : ((Nat.choose (r + d + 2) r):ℤ) * (d + 2) = (Nat.choose (r + d + 1) r) * (r + d + 2) := by exact_mod_cast cii
  have goalZ : ((Nat.choose (r + d + 2) r):ℤ) * ((d + 1) * (d + 2))
      = (Nat.choose (r + d) r) * ((r + d + 1) * (r + d + 2)) := by
    linear_combination ((r:ℤ) + d + 2) * ciZ + ((d:ℤ) + 1) * ciiZ
  exact_mod_cast goalZ

-- rk ratio identity: T(n,k+1) * 2(k+1)^3 (2k+2n+1) = T(n,k) * (n-k)^2 (3n+2k+1)(3n+2k+2)
theorem rk_id (n k : ℕ) (h : k ≤ n) :
    T n (k + 1) * (2 * (k + 1)^3 * (2*k+2*n+1))
      = T n k * ((n - k)^2 * (3*n+2*k+1) * (3*n+2*k+2)) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = k + e := ⟨n - k, by omega⟩
  have hsub : (k + e) - k = e := by omega
  rw [hsub]
  set a := Nat.choose (k + e) (k + 1) with ha
  set c := Nat.choose (k + e) k with hc
  set b := Nat.choose (k + e + (k + 1)) (k + 1) with hb
  set bc := Nat.choose (k + e + k) k with hbc
  set cc := Nat.choose (3 * (k + e) + 2 * (k + 1)) (k + e) with hcc
  set cd := Nat.choose (3 * (k + e) + 2 * k) (k + e) with hcd
  have hT1 : T (k + e) (k + 1) = a ^ 2 * b * cc := by unfold T; rw [ha, hb, hcc]
  have hT0 : T (k + e) k = c ^ 2 * bc * cd := by unfold T; rw [hc, hbc, hcd]
  rw [hT1, hT0]
  -- A : a (k+1) = c e
  have A : (a:ℤ) * (k + 1) = c * e := by
    have h0 := Nat.choose_succ_right_eq (k + e) k
    rw [← ha, ← hc] at h0
    have hs : k + e - k = e := by omega
    rw [hs] at h0; exact_mod_cast h0
  -- B : b (k+1) = (k+e+k+1) bc
  have B : (b:ℤ) * (k + 1) = (k + e + k + 1) * bc := by
    have h0 := Nat.succ_mul_choose_eq (k + e + k) k
    simp only [Nat.succ_eq_add_one] at h0
    -- h0 : (k+e+k+1) * (k+e+k).choose k = (k+e+k+1).choose (k+1) * (k+1)
    have e1 : Nat.choose (k + e + k + 1) (k + 1) = b := by rw [hb]; congr 1 <;> omega
    rw [← hbc, e1] at h0
    -- h0 : (k+e+k+1) * bc = b * (k+1)
    push_cast at h0 ⊢; linarith [h0]
  -- C : cc ((2(k+e)+2k+1)(2(k+e)+2k+2)) = cd ((3(k+e)+2k+1)(3(k+e)+2k+2))
  have C : (cc:ℤ) * ((2 * (k + e) + 2 * k + 1) * (2 * (k + e) + 2 * k + 2))
      = cd * ((3 * (k + e) + 2 * k + 1) * (3 * (k + e) + 2 * k + 2)) := by
    have h0 := shiftTop2 (k + e) (2 * (k + e) + 2 * k)
    have e1 : Nat.choose (k + e + (2 * (k + e) + 2 * k) + 2) (k + e) = cc := by
      rw [hcc]; congr 1 <;> omega
    have e2 : Nat.choose (k + e + (2 * (k + e) + 2 * k)) (k + e) = cd := by
      rw [hcd]; congr 1 <;> omega
    rw [e1, e2] at h0
    have e3 : k + e + (2 * (k + e) + 2 * k) + 1 = 3 * (k + e) + 2 * k + 1 := by omega
    have e4 : k + e + (2 * (k + e) + 2 * k) + 2 = 3 * (k + e) + 2 * k + 2 := by omega
    rw [e3, e4] at h0
    exact_mod_cast h0
  -- cancel F = (k+e+k+1)
  have hFpos : (0:ℤ) < ((k + e + k + 1 : ℕ) : ℤ) := by positivity
  have key : ((a ^ 2 * b * cc : ℕ) : ℤ) * (2 * (k + 1)^3 * (2*k+2*(k+e)+1)) * ((k + e + k + 1 : ℕ):ℤ)
      = ((c ^ 2 * bc * cd : ℕ) : ℤ)
        * ((e:ℤ)^2 * (3*(k+e)+2*k+1) * (3*(k+e)+2*k+2)) * ((k + e + k + 1 : ℕ):ℤ) := by
    push_cast
    linear_combination
      (((a:ℤ) * (k + 1) + (c:ℤ) * e) * ((b:ℤ) * (k + 1))
        * ((cc:ℤ) * ((2 * (k + e) + 2 * k + 1) * (2 * (k + e) + 2 * k + 2)))) * A
      + (((c:ℤ) ^ 2 * e ^ 2)
        * ((cc:ℤ) * ((2 * (k + e) + 2 * k + 1) * (2 * (k + e) + 2 * k + 2)))) * B
      + (((c:ℤ) ^ 2 * e ^ 2) * (((k:ℤ) + e + k + 1) * bc)) * C
  have key2 : ((a ^ 2 * b * cc : ℕ) : ℤ) * (2 * (k + 1)^3 * (2*k+2*(k+e)+1))
      = ((c ^ 2 * bc * cd : ℕ) : ℤ) * ((e:ℤ)^2 * (3*(k+e)+2*k+1) * (3*(k+e)+2*k+2)) :=
    mul_right_cancel₀ (ne_of_gt hFpos) key
  exact_mod_cast key2
theorem rn_id (n k : ℕ) (h : k ≤ n) :
    T (n+1) k * (2 * (n - k + 1)^2 * (2*k+2*n+1))
      = T n k * ((3*n+2*k+1)*(3*n+2*k+2)*(3*n+2*k+3)) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = k + e := ⟨n - k, by omega⟩
  have hsub : (k + e) - k + 1 = e + 1 := by omega
  rw [hsub]
  -- atoms (exact args as appear after unfolding T)
  set a := Nat.choose (k + e + 1) k with ha
  set c := Nat.choose (k + e) k with hc
  set b := Nat.choose (k + e + 1 + k) k with hb
  set bc := Nat.choose (k + e + k) k with hbc
  set cc := Nat.choose (3 * (k + e + 1) + 2 * k) (k + e + 1) with hcc
  set cd := Nat.choose (3 * (k + e) + 2 * k) (k + e) with hcd
  -- express T's
  have hT1 : T (k + e + 1) k = a ^ 2 * b * cc := by
    unfold T; rw [ha, hb, hcc]
  have hT0 : T (k + e) k = c ^ 2 * bc * cd := by
    unfold T; rw [hc, hbc, hcd]
  rw [hT1, hT0]
  -- A,B,C over ℤ
  have A : (a:ℤ) * (e + 1) = c * (k + e + 1) := by
    have h0 := shiftA0 k e; rw [← ha, ← hc] at h0; exact_mod_cast h0
  have B : (b:ℤ) * (k + e + 1) = bc * (k + e + k + 1) := by
    have h0 := shiftB (k + e) k
    have e1 : Nat.choose (k + e + k + 1) k = b := by rw [hb]; congr 1; omega
    rw [e1, ← hbc] at h0; exact_mod_cast h0
  have C : (cc:ℤ) * ((k + e + 1) * (2 * (k + e) + 2 * k + 1) * (2 * (k + e) + 2 * k + 2))
      = cd * ((3 * (k + e) + 2 * k + 1) * (3 * (k + e) + 2 * k + 2) * (3 * (k + e) + 2 * k + 3)) := by
    have h0 := cC' (k + e) (2 * (k + e) + 2 * k)
    have e1 : Nat.choose (k + e + (2 * (k + e) + 2 * k) + 3) (k + e + 1) = cc := by
      rw [hcc]; congr 1 <;> omega
    have e2 : Nat.choose (k + e + (2 * (k + e) + 2 * k)) (k + e) = cd := by
      rw [hcd]; congr 1 <;> omega
    rw [e1, e2] at h0
    have := h0
    -- normalize the polynomial args
    have e3 : k + e + (2 * (k + e) + 2 * k) + 1 = 3 * (k + e) + 2 * k + 1 := by omega
    have e4 : k + e + (2 * (k + e) + 2 * k) + 2 = 3 * (k + e) + 2 * k + 2 := by omega
    have e5 : k + e + (2 * (k + e) + 2 * k) + 3 = 3 * (k + e) + 2 * k + 3 := by omega
    rw [e3, e4, e5] at this
    exact_mod_cast this
  -- cancel common factor F = (k+e+1)^2 * (k+e+k+1) > 0, work over ℤ
  have hFpos : (0:ℤ) < ((k + e + 1) ^ 2 * (k + e + k + 1)) := by positivity
  have key : ((a ^ 2 * b * cc : ℕ) : ℤ) * (2 * (e + 1) ^ 2 * (2 * k + 2 * (k + e) + 1))
      * ((k + e + 1) ^ 2 * (k + e + k + 1))
      = ((c ^ 2 * bc * cd : ℕ) : ℤ)
        * ((3 * (k + e) + 2 * k + 1) * (3 * (k + e) + 2 * k + 2) * (3 * (k + e) + 2 * k + 3))
        * ((k + e + 1) ^ 2 * (k + e + k + 1)) := by
    push_cast
    linear_combination
      (((a:ℤ) * (e + 1) + (c:ℤ) * (k + e + 1)) * ((b:ℤ) * (k + e + 1))
        * ((cc:ℤ) * ((k + e + 1) * (2 * (k + e) + 2 * k + 1) * (2 * (k + e) + 2 * k + 2)))) * A
      + (((c:ℤ) ^ 2 * (k + e + 1) ^ 2)
        * ((cc:ℤ) * ((k + e + 1) * (2 * (k + e) + 2 * k + 1) * (2 * (k + e) + 2 * k + 2)))) * B
      + (((c:ℤ) ^ 2 * (k + e + 1) ^ 2) * ((bc:ℤ) * (k + e + k + 1))) * C
  have key2 : ((a ^ 2 * b * cc : ℕ) : ℤ) * (2 * (e + 1) ^ 2 * (2 * k + 2 * (k + e) + 1))
      = ((c ^ 2 * bc * cd : ℕ) : ℤ)
        * ((3 * (k + e) + 2 * k + 1) * (3 * (k + e) + 2 * k + 2) * (3 * (k + e) + 2 * k + 3)) :=
    mul_right_cancel₀ (ne_of_gt hFpos) key
  exact_mod_cast key2

def cc0 (n : ℤ) : ℤ := -110539728*n^11 - 1271206872*n^10 - 6407584137*n^9 - 18628227396*n^8 - 34600706334*n^7 - 42998248332*n^6 - 36403747137*n^5 - 20972151936*n^4 - 8053976448*n^3 - 1964534256*n^2 - 274291056*n - 16642368
def cc1 (n : ℤ) : ℤ := -2620200960*n^11 - 34062612480*n^10 - 198250115328*n^9 - 681106542912*n^8 - 1532821148280*n^7 - 2369391446412*n^6 - 2563251742332*n^5 - 1937758760676*n^4 - 1001713365324*n^3 - 336786073920*n^2 - 66214903824*n - 5766185664
def cc2 (n : ℤ) : ℤ := 23003136*n^11 + 333545472*n^10 + 2154811392*n^9 + 8173740032*n^8 + 20192782592*n^7 + 34051403648*n^6 + 39921001392*n^5 + 32478522768*n^4 + 17939360256*n^3 + 6397982080*n^2 + 1324960000*n + 120736000
def Ncert (n k : ℤ) : ℤ := 3824675712*k^7*n^9 + 39079025856*k^7*n^8 + 173321167896*k^7*n^7 + 437106689800*k^7*n^6 + 689437265816*k^7*n^5 + 703946473464*k^7*n^4 + 464521657072*k^7*n^3 + 190817019232*k^7*n^2 + 44265723840*k^7*n + 4423482112*k^7 + 10489969152*k^6*n^10 + 105282837504*k^6*n^9 + 456039119520*k^6*n^8 + 1113468064080*k^6*n^7 + 1676384444576*k^6*n^6 + 1593361184576*k^6*n^5 + 930220886400*k^6*n^4 + 296465836336*k^6*n^3 + 27969137728*k^6*n^2 - 9664503744*k^6*n - 2197012224*k^6 - 167401728*k^5*n^11 - 33965163648*k^5*n^10 - 355913768880*k^5*n^9 - 1672514324352*k^5*n^8 - 4566739199526*k^5*n^7 - 7989463928002*k^5*n^6 - 9338776308054*k^5*n^5 - 7377441046638*k^5*n^4 - 3886978230108*k^5*n^3 - 1307061075864*k^5*n^2 - 253410907248*k^5*n - 21532892864*k^5 - 21723406848*k^4*n^12 - 305617328640*k^4*n^11 - 1914243132384*k^4*n^10 - 7058870804880*k^4*n^9 - 17065371652812*k^4*n^8 - 28488833849064*k^4*n^7 - 33667535729060*k^4*n^6 - 28376564363708*k^4*n^5 - 16930566038160*k^4*n^4 - 6975769777804*k^4*n^3 - 1885191336016*k^4*n^2 - 300330787920*k^4*n - 21358789440*k^4 - 14887836288*k^3*n^13 - 208008171072*k^3*n^12 - 1312145146152*k^3*n^11 - 4943888136648*k^3*n^10 - 12403305548406*k^3*n^9 - 21864735074610*k^3*n^8 - 27846820844958*k^3*n^7 - 25933339272822*k^3*n^6 - 17657147828828*k^3*n^5 - 8681735148312*k^3*n^4 - 2997417553408*k^3*n^3 - 688614393568*k^3*n^2 - 94443166656*k^3*n - 5847265664*k^3
def Dden (n k : ℤ) : ℤ := 2*k^5 - 6*k^4*n - 11*k^4 + 4*k^3*n^2 + 20*k^3*n + 20*k^3 + 4*k^2*n^3 + 6*k^2*n^2 - 8*k^2*n - 11*k^2 - 6*k*n^4 - 28*k*n^3 - 44*k*n^2 - 26*k*n - 4*k + 2*n^5 + 13*n^4 + 32*n^3 + 37*n^2 + 20*n + 4


theorem PS_int (n k : ℕ) (h : k ≤ n) :
    (cc0 (n:ℤ) * (T n k : ℤ) + cc1 (n:ℤ) * (T (n+1) k : ℤ) + cc2 (n:ℤ) * (T (n+2) k : ℤ))
        * Dden (n:ℤ) (k:ℤ) * Dden (n:ℤ) ((k:ℤ)+1)
      = Ncert (n:ℤ) ((k:ℤ)+1) * (T n (k+1) : ℤ) * Dden (n:ℤ) (k:ℤ)
        - Ncert (n:ℤ) (k:ℤ) * (T n k : ℤ) * Dden (n:ℤ) ((k:ℤ)+1) := by
  have R1 : ((T (n+1) k : ℤ)) * (2*((n:ℤ)-(k:ℤ)+1)^2*(2*(k:ℤ)+2*(n:ℤ)+1))
      = ((T n k : ℤ))*((3*(n:ℤ)+2*(k:ℤ)+1)*(3*(n:ℤ)+2*(k:ℤ)+2)*(3*(n:ℤ)+2*(k:ℤ)+3)) := by
    have hh := rn_id n k h
    have : ((T (n+1) k : ℤ)) * (2*(((n-k+1:ℕ)):ℤ)^2*(2*(k:ℤ)+2*(n:ℤ)+1))
        = ((T n k : ℤ))*((3*(n:ℤ)+2*(k:ℤ)+1)*(3*(n:ℤ)+2*(k:ℤ)+2)*(3*(n:ℤ)+2*(k:ℤ)+3)) := by exact_mod_cast hh
    rw [show (((n-k+1:ℕ)):ℤ) = (n:ℤ)-(k:ℤ)+1 from by push_cast [Nat.cast_sub h]; ring] at this
    linear_combination this
  have R2 : ((T (n+2) k : ℤ)) * (2*((n:ℤ)+2-(k:ℤ))^2*(2*(k:ℤ)+2*(n:ℤ)+3))
      = ((T (n+1) k : ℤ))*((3*(n:ℤ)+2*(k:ℤ)+4)*(3*(n:ℤ)+2*(k:ℤ)+5)*(3*(n:ℤ)+2*(k:ℤ)+6)) := by
    have hh := rn_id (n+1) k (by omega)
    have : ((T (n+1+1) k : ℤ)) * (2*(((n+1-k+1:ℕ)):ℤ)^2*(2*(k:ℤ)+2*((n:ℤ)+1)+1))
        = ((T (n+1) k : ℤ))*((3*((n:ℤ)+1)+2*(k:ℤ)+1)*(3*((n:ℤ)+1)+2*(k:ℤ)+2)*(3*((n:ℤ)+1)+2*(k:ℤ)+3)) := by exact_mod_cast hh
    rw [show (((n+1-k+1:ℕ)):ℤ) = (n:ℤ)+2-(k:ℤ) from by push_cast [Nat.cast_sub (show k ≤ n+1 by omega)]; ring] at this
    have e : n+1+1 = n+2 := by omega
    rw [e] at this
    linear_combination this
  have R3 : ((T n (k+1) : ℤ)) * (2*((k:ℤ)+1)^3*(2*(k:ℤ)+2*(n:ℤ)+1))
      = ((T n k : ℤ))*(((n:ℤ)-(k:ℤ))^2*(3*(n:ℤ)+2*(k:ℤ)+1)*(3*(n:ℤ)+2*(k:ℤ)+2)) := by
    have hh := rk_id n k h
    have : ((T n (k+1) : ℤ)) * (2*((k:ℤ)+1)^3*(2*(k:ℤ)+2*(n:ℤ)+1))
        = ((T n k : ℤ))*((((n-k:ℕ)):ℤ)^2*(3*(n:ℤ)+2*(k:ℤ)+1)*(3*(n:ℤ)+2*(k:ℤ)+2)) := by exact_mod_cast hh
    rw [show (((n-k:ℕ)):ℤ) = (n:ℤ)-(k:ℤ) from by push_cast [Nat.cast_sub h]; ring] at this
    linear_combination this
  simp only [cc0, cc1, cc2, Ncert, Dden]
  linear_combination (-2574194688*(k:ℤ)^7*(n:ℤ)^11 - 33395521536*(k:ℤ)^7*(n:ℤ)^10 - 193940492544*(k:ℤ)^7*(n:ℤ)^9 - 664759062848*(k:ℤ)^7*(n:ℤ)^8 - 1492435583096*(k:ℤ)^7*(n:ℤ)^7 - 2301288639116*(k:ℤ)^7*(n:ℤ)^6 - 2483409739548*(k:ℤ)^7*(n:ℤ)^5 - 1872801715140*(k:ℤ)^7*(n:ℤ)^4 - 965834644812*(k:ℤ)^7*(n:ℤ)^3 - 323990109760*(k:ℤ)^7*(n:ℤ)^2 - 63564983824*(k:ℤ)^7*(n:ℤ) - 5524713664*(k:ℤ)^7 + 13124007936*(k:ℤ)^6*(n:ℤ)^12 + 182690546688*(k:ℤ)^6*(n:ℤ)^11 + 1150356144384*(k:ℤ)^6*(n:ℤ)^10 + 4329534898880*(k:ℤ)^6*(n:ℤ)^9 + 10839189107448*(k:ℤ)^6*(n:ℤ)^8 + 19000824411480*(k:ℤ)^6*(n:ℤ)^7 + 23893006662034*(k:ℤ)^6*(n:ℤ)^6 + 21695036181954*(k:ℤ)^6*(n:ℤ)^5 + 14103684360366*(k:ℤ)^6*(n:ℤ)^4 + 6395371458454*(k:ℤ)^6*(n:ℤ)^3 + 1918314614640*(k:ℤ)^6*(n:ℤ)^2 + 341493291528*(k:ℤ)^6*(n:ℤ) + 27275931488*(k:ℤ)^6 - 23823341568*(k:ℤ)^5*(n:ℤ)^13 - 349851820032*(k:ℤ)^5*(n:ℤ)^12 - 2335093975296*(k:ℤ)^5*(n:ℤ)^11 - 9368034466368*(k:ℤ)^5*(n:ℤ)^10 - 25169268394872*(k:ℤ)^5*(n:ℤ)^9 - 47749290926004*(k:ℤ)^5*(n:ℤ)^8 - 65693936918184*(k:ℤ)^5*(n:ℤ)^7 - 66239073652176*(k:ℤ)^5*(n:ℤ)^6 - 48845931915672*(k:ℤ)^5*(n:ℤ)^5 - 25959408860148*(k:ℤ)^5*(n:ℤ)^4 - 9641394165888*(k:ℤ)^5*(n:ℤ)^3 - 2363773573296*(k:ℤ)^5*(n:ℤ)^2 - 341963216256*(k:ℤ)^5*(n:ℤ) - 21978118656*(k:ℤ)^5 + 13072250880*(k:ℤ)^4*(n:ℤ)^14 + 188598758400*(k:ℤ)^4*(n:ℤ)^13 + 1212533925120*(k:ℤ)^4*(n:ℤ)^12 + 4539425932736*(k:ℤ)^4*(n:ℤ)^11 + 10766807957624*(k:ℤ)^4*(n:ℤ)^10 + 16116392402080*(k:ℤ)^4*(n:ℤ)^9 + 12823040008282*(k:ℤ)^4*(n:ℤ)^8 - 2051753394950*(k:ℤ)^4*(n:ℤ)^7 - 19450930362484*(k:ℤ)^4*(n:ℤ)^6 - 26401735892744*(k:ℤ)^4*(n:ℤ)^5 - 20463644966966*(k:ℤ)^4*(n:ℤ)^4 - 10142994375874*(k:ℤ)^4*(n:ℤ)^3 - 3186394425184*(k:ℤ)^4*(n:ℤ)^2 - 580197132664*(k:ℤ)^4*(n:ℤ) - 46747736480*(k:ℤ)^4 + 13561067520*(k:ℤ)^3*(n:ℤ)^15 + 257717790720*(k:ℤ)^3*(n:ℤ)^14 + 2257301341440*(k:ℤ)^3*(n:ℤ)^13 + 12074157100096*(k:ℤ)^3*(n:ℤ)^12 + 44059801355736*(k:ℤ)^3*(n:ℤ)^11 + 116058022417996*(k:ℤ)^3*(n:ℤ)^10 + 227722673254356*(k:ℤ)^3*(n:ℤ)^9 + 338556310411812*(k:ℤ)^3*(n:ℤ)^8 + 384090310474868*(k:ℤ)^3*(n:ℤ)^7 + 332155298042488*(k:ℤ)^3*(n:ℤ)^6 + 216937139861760*(k:ℤ)^3*(n:ℤ)^5 + 104980112837552*(k:ℤ)^3*(n:ℤ)^4 + 36403870807464*(k:ℤ)^3*(n:ℤ)^3 + 8533722856032*(k:ℤ)^3*(n:ℤ)^2 + 1208633015392*(k:ℤ)^3*(n:ℤ) + 77949671296*(k:ℤ)^3 - 23685322752*(k:ℤ)^2*(n:ℤ)^16 - 445279970304*(k:ℤ)^2*(n:ℤ)^15 - 3878040796416*(k:ℤ)^2*(n:ℤ)^14 - 20749185556416*(k:ℤ)^2*(n:ℤ)^13 - 76254483304536*(k:ℤ)^2*(n:ℤ)^12 - 203864053268552*(k:ℤ)^2*(n:ℤ)^11 - 409594123626506*(k:ℤ)^2*(n:ℤ)^10 - 629924839063890*(k:ℤ)^2*(n:ℤ)^9 - 748175081424910*(k:ℤ)^2*(n:ℤ)^8 - 687227142170146*(k:ℤ)^2*(n:ℤ)^7 - 485458124045328*(k:ℤ)^2*(n:ℤ)^6 - 260248952088028*(k:ℤ)^2*(n:ℤ)^5 - 103448049840976*(k:ℤ)^2*(n:ℤ)^4 - 29346791218776*(k:ℤ)^2*(n:ℤ)^3 - 5570031039008*(k:ℤ)^2*(n:ℤ)^2 - 626351042144*(k:ℤ)^2*(n:ℤ) - 30975033984*(k:ℤ)^2 + 12790462464*(k:ℤ)*(n:ℤ)^17 + 249896005632*(k:ℤ)*(n:ℤ)^16 + 2264958326016*(k:ℤ)*(n:ℤ)^15 + 12634472460096*(k:ℤ)*(n:ℤ)^14 + 48520587122712*(k:ℤ)*(n:ℤ)^13 + 135938998309748*(k:ℤ)*(n:ℤ)^12 + 287223580252368*(k:ℤ)*(n:ℤ)^11 + 466522523647280*(k:ℤ)*(n:ℤ)^10 + 588251348805000*(k:ℤ)*(n:ℤ)^9 + 577288080102140*(k:ℤ)*(n:ℤ)^8 + 439101446401608*(k:ℤ)*(n:ℤ)^7 + 255938124279856*(k:ℤ)*(n:ℤ)^6 + 111976225452648*(k:ℤ)*(n:ℤ)^5 + 35523092993392*(k:ℤ)*(n:ℤ)^4 + 7701153977760*(k:ℤ)*(n:ℤ)^3 + 1018853070400*(k:ℤ)*(n:ℤ)^2 + 61950067968*(k:ℤ)*(n:ℤ) - 2464929792*(n:ℤ)^18 - 50375789568*(n:ℤ)^17 - 478074472704*(n:ℤ)^16 - 2795611306176*(n:ℤ)^15 - 11270198261016*(n:ℤ)^14 - 33199604707632*(n:ℤ)^13 - 73890829892802*(n:ℤ)^12 - 126685402414890*(n:ℤ)^11 - 169007565292356*(n:ℤ)^10 - 175926472570284*(n:ℤ)^9 - 142330172716002*(n:ℤ)^8 - 88498485658074*(n:ℤ)^7 - 41430964709184*(n:ℤ)^6 - 14107849379328*(n:ℤ)^5 - 3293008217664*(n:ℤ)^4 - 470451699552*(n:ℤ)^3 - 30975033984*(n:ℤ)^2)*R1 + (23003136*(k:ℤ)^7*(n:ℤ)^11 + 333545472*(k:ℤ)^7*(n:ℤ)^10 + 2154811392*(k:ℤ)^7*(n:ℤ)^9 + 8173740032*(k:ℤ)^7*(n:ℤ)^8 + 20192782592*(k:ℤ)^7*(n:ℤ)^7 + 34051403648*(k:ℤ)^7*(n:ℤ)^6 + 39921001392*(k:ℤ)^7*(n:ℤ)^5 + 32478522768*(k:ℤ)^7*(n:ℤ)^4 + 17939360256*(k:ℤ)^7*(n:ℤ)^3 + 6397982080*(k:ℤ)^7*(n:ℤ)^2 + 1324960000*(k:ℤ)^7*(n:ℤ) + 120736000*(k:ℤ)^7 - 115015680*(k:ℤ)^6*(n:ℤ)^12 - 1748238336*(k:ℤ)^6*(n:ℤ)^11 - 11941466112*(k:ℤ)^6*(n:ℤ)^10 - 48410540032*(k:ℤ)^6*(n:ℤ)^9 - 129572003072*(k:ℤ)^6*(n:ℤ)^8 - 240931757312*(k:ℤ)^6*(n:ℤ)^7 - 318784919728*(k:ℤ)^6*(n:ℤ)^6 - 302116118712*(k:ℤ)^6*(n:ℤ)^5 - 203371630968*(k:ℤ)^6*(n:ℤ)^4 - 94777671296*(k:ℤ)^6*(n:ℤ)^3 - 29017737280*(k:ℤ)^6*(n:ℤ)^2 - 5241040000*(k:ℤ)^6*(n:ℤ) - 422576000*(k:ℤ)^6 + 207028224*(k:ℤ)^5*(n:ℤ)^13 + 3300950016*(k:ℤ)^5*(n:ℤ)^12 + 23821406208*(k:ℤ)^5*(n:ℤ)^11 + 102910390272*(k:ℤ)^5*(n:ℤ)^10 + 296612909312*(k:ℤ)^5*(n:ℤ)^9 + 601663766656*(k:ℤ)^5*(n:ℤ)^8 + 882728390320*(k:ℤ)^5*(n:ℤ)^7 + 947485337600*(k:ℤ)^5*(n:ℤ)^6 + 743359043856*(k:ℤ)^5*(n:ℤ)^5 + 420707613120*(k:ℤ)^5*(n:ℤ)^4 + 166855848064*(k:ℤ)^5*(n:ℤ)^3 + 43903032320*(k:ℤ)^5*(n:ℤ)^2 + 6869408000*(k:ℤ)^5*(n:ℤ) + 482944000*(k:ℤ)^5 - 115015680*(k:ℤ)^4*(n:ℤ)^14 - 1955266560*(k:ℤ)^4*(n:ℤ)^13 - 15127400448*(k:ℤ)^4*(n:ℤ)^12 - 70495209472*(k:ℤ)^4*(n:ℤ)^11 - 220707699968*(k:ℤ)^4*(n:ℤ)^10 - 490211532288*(k:ℤ)^4*(n:ℤ)^9 - 794963553328*(k:ℤ)^4*(n:ℤ)^8 - 954009143016*(k:ℤ)^4*(n:ℤ)^7 - 849097750664*(k:ℤ)^4*(n:ℤ)^6 - 555981097136*(k:ℤ)^4*(n:ℤ)^5 - 262592980816*(k:ℤ)^4*(n:ℤ)^4 - 86288896896*(k:ℤ)^4*(n:ℤ)^3 - 18506862080*(k:ℤ)^4*(n:ℤ)^2 - 2290848000*(k:ℤ)^4*(n:ℤ) - 120736000*(k:ℤ)^4 - 115015680*(k:ℤ)^3*(n:ℤ)^15 - 1897758720*(k:ℤ)^3*(n:ℤ)^14 - 14293536768*(k:ℤ)^3*(n:ℤ)^13 - 65177190400*(k:ℤ)^3*(n:ℤ)^12 - 201296989440*(k:ℤ)^3*(n:ℤ)^11 - 446527555456*(k:ℤ)^3*(n:ℤ)^10 - 736511075696*(k:ℤ)^3*(n:ℤ)^9 - 922958727344*(k:ℤ)^3*(n:ℤ)^8 - 890248437280*(k:ℤ)^3*(n:ℤ)^7 - 664947104320*(k:ℤ)^3*(n:ℤ)^6 - 383954595312*(k:ℤ)^3*(n:ℤ)^5 - 169273100432*(k:ℤ)^3*(n:ℤ)^4 - 55338328576*(k:ℤ)^3*(n:ℤ)^3 - 12663710080*(k:ℤ)^3*(n:ℤ)^2 - 1807904000*(k:ℤ)^3*(n:ℤ) - 120736000*(k:ℤ)^3 + 207028224*(k:ℤ)^2*(n:ℤ)^16 + 3634495488*(k:ℤ)^2*(n:ℤ)^15 + 29301903360*(k:ℤ)^2*(n:ℤ)^14 + 143908485120*(k:ℤ)^2*(n:ℤ)^13 + 481585692928*(k:ℤ)^2*(n:ℤ)^12 + 1163789669120*(k:ℤ)^2*(n:ℤ)^11 + 2099939806064*(k:ℤ)^2*(n:ℤ)^10 + 2885195352440*(k:ℤ)^2*(n:ℤ)^9 + 3050061711608*(k:ℤ)^2*(n:ℤ)^8 + 2489158408928*(k:ℤ)^2*(n:ℤ)^7 + 1563172794000*(k:ℤ)^2*(n:ℤ)^6 + 747520049704*(k:ℤ)^2*(n:ℤ)^5 + 266818700104*(k:ℤ)^2*(n:ℤ)^4 + 68672422528*(k:ℤ)^2*(n:ℤ)^3 + 11997039040*(k:ℤ)^2*(n:ℤ)^2 + 1266160000*(k:ℤ)^2*(n:ℤ) + 60368000*(k:ℤ)^2 - 115015680*(k:ℤ)*(n:ℤ)^17 - 2104786944*(k:ℤ)*(n:ℤ)^16 - 17755508736*(k:ℤ)*(n:ℤ)^15 - 91609452544*(k:ℤ)*(n:ℤ)^14 - 323431623936*(k:ℤ)*(n:ℤ)^13 - 828238657664*(k:ℤ)*(n:ℤ)^12 - 1590871614704*(k:ℤ)*(n:ℤ)^11 - 2337557585888*(k:ℤ)*(n:ℤ)^10 - 2655128063984*(k:ℤ)*(n:ℤ)^9 - 2339209028736*(k:ℤ)*(n:ℤ)^8 - 1593557415440*(k:ℤ)*(n:ℤ)^7 - 830979284128*(k:ℤ)*(n:ℤ)^6 - 325406550160*(k:ℤ)*(n:ℤ)^5 - 92605042816*(k:ℤ)*(n:ℤ)^4 - 18087422080*(k:ℤ)*(n:ℤ)^3 - 2170112000*(k:ℤ)*(n:ℤ)^2 - 120736000*(k:ℤ)*(n:ℤ) + 23003136*(n:ℤ)^18 + 437059584*(n:ℤ)^17 + 3839791104*(n:ℤ)^16 + 20699777024*(n:ℤ)^15 + 76616931584*(n:ℤ)^14 + 206404663296*(n:ℤ)^13 + 418541965680*(n:ℤ)^12 + 651482362152*(n:ℤ)^11 + 786485767176*(n:ℤ)^10 + 738650897360*(n:ℤ)^9 + 537769126784*(n:ℤ)^8 + 300238503432*(n:ℤ)^7 + 125986208712*(n:ℤ)^6 + 38404234368*(n:ℤ)^5 + 8019023040*(n:ℤ)^4 + 1024688000*(n:ℤ)^3 + 60368000*(n:ℤ)^2)*R2 + (-1912337856*(k:ℤ)^8*(n:ℤ)^9 - 19539512928*(k:ℤ)^8*(n:ℤ)^8 - 86660583948*(k:ℤ)^8*(n:ℤ)^7 - 218553344900*(k:ℤ)^8*(n:ℤ)^6 - 344718632908*(k:ℤ)^8*(n:ℤ)^5 - 351973236732*(k:ℤ)^8*(n:ℤ)^4 - 232260828536*(k:ℤ)^8*(n:ℤ)^3 - 95408509616*(k:ℤ)^8*(n:ℤ)^2 - 22132861920*(k:ℤ)^8*(n:ℤ) - 2211741056*(k:ℤ)^8 + 2404366848*(k:ℤ)^7*(n:ℤ)^10 + 29341308672*(k:ℤ)^7*(n:ℤ)^9 + 157701801888*(k:ℤ)^7*(n:ℤ)^8 + 490800515456*(k:ℤ)^7*(n:ℤ)^7 + 977788999144*(k:ℤ)^7*(n:ℤ)^6 + 1300649620456*(k:ℤ)^7*(n:ℤ)^5 + 1167879344408*(k:ℤ)^7*(n:ℤ)^4 + 697922777368*(k:ℤ)^7*(n:ℤ)^3 + 265363898048*(k:ℤ)^7*(n:ℤ)^2 + 57944939936*(k:ℤ)^7*(n:ℤ) + 5521988224*(k:ℤ)^7 + 9589612032*(k:ℤ)^6*(n:ℤ)^11 + 122221457280*(k:ℤ)^6*(n:ℤ)^10 + 698478539472*(k:ℤ)^6*(n:ℤ)^9 + 2360308296960*(k:ℤ)^6*(n:ℤ)^8 + 5234225017527*(k:ℤ)^6*(n:ℤ)^7 + 7987521038309*(k:ℤ)^6*(n:ℤ)^6 + 8545953423551*(k:ℤ)^6*(n:ℤ)^5 + 6399876994483*(k:ℤ)^6*(n:ℤ)^4 + 3281816096942*(k:ℤ)^6*(n:ℤ)^3 + 1095661614940*(k:ℤ)^6*(n:ℤ)^2 + 214055501048*(k:ℤ)^6*(n:ℤ) + 18529633376*(k:ℤ)^6 - 13293656064*(k:ℤ)^5*(n:ℤ)^12 - 196090861824*(k:ℤ)^5*(n:ℤ)^11 - 1308778375392*(k:ℤ)^5*(n:ℤ)^10 - 5221577608672*(k:ℤ)^5*(n:ℤ)^9 - 13854634115846*(k:ℤ)^5*(n:ℤ)^8 - 25725635263804*(k:ℤ)^5*(n:ℤ)^7 - 34232107165358*(k:ℤ)^5*(n:ℤ)^6 - 32843942715282*(k:ℤ)^5*(n:ℤ)^5 - 22516083301868*(k:ℤ)^5*(n:ℤ)^4 - 10739665835794*(k:ℤ)^5*(n:ℤ)^3 - 3378256098088*(k:ℤ)^5*(n:ℤ)^2 - 628516871928*(k:ℤ)^5*(n:ℤ) - 52277331680*(k:ℤ)^5 - 16433089920*(k:ℤ)^4*(n:ℤ)^13 - 248657048640*(k:ℤ)^4*(n:ℤ)^12 - 1717845684840*(k:ℤ)^4*(n:ℤ)^11 - 7170643517000*(k:ℤ)^4*(n:ℤ)^10 - 20166550278451*(k:ℤ)^4*(n:ℤ)^9 - 40328339545113*(k:ℤ)^4*(n:ℤ)^8 - 58958598326571*(k:ℤ)^4*(n:ℤ)^7 - 63757012405605*(k:ℤ)^4*(n:ℤ)^6 - 50957641249652*(k:ℤ)^4*(n:ℤ)^5 - 29703924786998*(k:ℤ)^4*(n:ℤ)^4 - 12262754195794*(k:ℤ)^4*(n:ℤ)^3 - 3391771648576*(k:ℤ)^4*(n:ℤ)^2 - 562810458392*(k:ℤ)^4*(n:ℤ) - 42284538400*(k:ℤ)^4 + 29814759936*(k:ℤ)^3*(n:ℤ)^14 + 510982587648*(k:ℤ)^3*(n:ℤ)^13 + 4026852538848*(k:ℤ)^3*(n:ℤ)^12 + 19332166608960*(k:ℤ)^3*(n:ℤ)^11 + 63133590746532*(k:ℤ)^3*(n:ℤ)^10 + 148280811799664*(k:ℤ)^3*(n:ℤ)^9 + 258130480250700*(k:ℤ)^3*(n:ℤ)^8 + 338101475613038*(k:ℤ)^3*(n:ℤ)^7 + 334555053962408*(k:ℤ)^3*(n:ℤ)^6 + 248649818766144*(k:ℤ)^3*(n:ℤ)^5 + 136500354047760*(k:ℤ)^3*(n:ℤ)^4 + 53613829736746*(k:ℤ)^3*(n:ℤ)^3 + 14227319439768*(k:ℤ)^3*(n:ℤ)^2 + 2280941975608*(k:ℤ)^3*(n:ℤ) + 166561454176*(k:ℤ)^3 + 1300396032*(k:ℤ)^2*(n:ℤ)^15 + 17520167808*(k:ℤ)^2*(n:ℤ)^14 + 97896665232*(k:ℤ)^2*(n:ℤ)^13 + 259827740064*(k:ℤ)^2*(n:ℤ)^12 + 84737986065*(k:ℤ)^2*(n:ℤ)^11 - 1845288857989*(k:ℤ)^2*(n:ℤ)^10 - 7378056806343*(k:ℤ)^2*(n:ℤ)^9 - 16249762122631*(k:ℤ)^2*(n:ℤ)^8 - 24232841217057*(k:ℤ)^2*(n:ℤ)^7 - 25928651303647*(k:ℤ)^2*(n:ℤ)^6 - 20234636868717*(k:ℤ)^2*(n:ℤ)^5 - 11451711394745*(k:ℤ)^2*(n:ℤ)^4 - 4581079259916*(k:ℤ)^2*(n:ℤ)^3 - 1227837262268*(k:ℤ)^2*(n:ℤ)^2 - 197656847808*(k:ℤ)^2*(n:ℤ) - 14432919104*(k:ℤ)^2 - 18913969152*(k:ℤ)*(n:ℤ)^16 - 375307395840*(k:ℤ)*(n:ℤ)^15 - 3462575509152*(k:ℤ)*(n:ℤ)^14 - 19709503826400*(k:ℤ)*(n:ℤ)^13 - 77443531754598*(k:ℤ)*(n:ℤ)^12 - 222638892462732*(k:ℤ)*(n:ℤ)^11 - 484207337954214*(k:ℤ)*(n:ℤ)^10 - 812259823034568*(k:ℤ)*(n:ℤ)^9 - 1061579118737430*(k:ℤ)*(n:ℤ)^8 - 1083926493644052*(k:ℤ)*(n:ℤ)^7 - 861243821698986*(k:ℤ)*(n:ℤ)^6 - 526570282108896*(k:ℤ)*(n:ℤ)^5 - 242694397999908*(k:ℤ)*(n:ℤ)^4 - 81456076413240*(k:ℤ)*(n:ℤ)^3 - 18762317289072*(k:ℤ)*(n:ℤ)^2 - 2648067528480*(k:ℤ)*(n:ℤ) - 172431501696*(k:ℤ) + 7443918144*(n:ℤ)^17 + 159529297824*(n:ℤ)^16 + 1594930607892*(n:ℤ)^15 + 9877175135532*(n:ℤ)^14 + 42424020032535*(n:ℤ)^13 + 134078183707941*(n:ℤ)^12 + 322764196542363*(n:ℤ)^11 + 604301115354813*(n:ℤ)^10 + 890539801368129*(n:ℤ)^9 + 1038455002040247*(n:ℤ)^8 + 957791595076173*(n:ℤ)^7 + 694431647096283*(n:ℤ)^6 + 390750520547628*(n:ℤ)^5 + 166973749533360*(n:ℤ)^4 + 52298671132224*(n:ℤ)^3 + 11307994254864*(n:ℤ)^2 + 1506242151936*(n:ℤ) + 93024956160)*R3

theorem Dden_eq (n k : ℤ) : Dden n k = (n+1-k)^2*(n+2-k)^2*(2*k+2*n+1) := by
  unfold Dden; ring

theorem Dden_pos0 (n k : ℕ) (hk : k < n) : (0:ℤ) < Dden (n:ℤ) (k:ℤ) := by
  rw [Dden_eq]
  have hkn : (k:ℤ) < n := by exact_mod_cast hk
  apply mul_pos; apply mul_pos
  · exact pow_pos (by omega) 2
  · exact pow_pos (by omega) 2
  · positivity

theorem Dden_pos1 (n k : ℕ) (hk : k < n) : (0:ℤ) < Dden (n:ℤ) ((k:ℤ)+1) := by
  rw [Dden_eq]
  have hkn : (k:ℤ) < n := by exact_mod_cast hk
  apply mul_pos; apply mul_pos
  · exact pow_pos (by omega) 2
  · exact pow_pos (by omega) 2
  · positivity

noncomputable def gg (n k : ℕ) : ℚ :=
  ((Ncert (n:ℤ) (k:ℤ) : ℚ)) * (T n k : ℚ) / ((Dden (n:ℤ) (k:ℤ) : ℚ))

theorem PS_Q (n k : ℕ) (hk : k < n) :
    ((cc0 (n:ℤ):ℚ)) * (T n k:ℚ) + ((cc1 (n:ℤ):ℚ))*(T (n+1) k:ℚ) + ((cc2 (n:ℤ):ℚ))*(T (n+2) k:ℚ)
      = gg n (k+1) - gg n k := by
  have hD0 : (Dden (n:ℤ) (k:ℤ) : ℚ) ≠ 0 := by
    have := Dden_pos0 n k hk; positivity
  have hD1 : (Dden (n:ℤ) ((k:ℤ)+1) : ℚ) ≠ 0 := by
    have := Dden_pos1 n k hk
    have h2 : ((Dden (n:ℤ) ((k:ℤ)+1):ℤ):ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt this)
    exact h2
  have hps := PS_int n k (le_of_lt hk)
  have hpsQ : (((cc0 (n:ℤ) * (T n k : ℤ) + cc1 (n:ℤ) * (T (n+1) k : ℤ) + cc2 (n:ℤ) * (T (n+2) k : ℤ))
        * Dden (n:ℤ) (k:ℤ) * Dden (n:ℤ) ((k:ℤ)+1) : ℤ) : ℚ)
      = (((Ncert (n:ℤ) ((k:ℤ)+1) * (T n (k+1) : ℤ) * Dden (n:ℤ) (k:ℤ)
        - Ncert (n:ℤ) (k:ℤ) * (T n k : ℤ) * Dden (n:ℤ) ((k:ℤ)+1) : ℤ) : ℚ)) := by
    exact_mod_cast hps
  push_cast at hpsQ
  unfold gg
  simp only [Nat.cast_add, Nat.cast_one]
  rw [div_sub_div _ _ hD1 hD0, eq_div_iff (mul_ne_zero hD1 hD0)]
  push_cast
  push_cast at hpsQ
  linear_combination hpsQ

noncomputable def aN (n : ℕ) : ℕ := Finset.sum (Finset.range (n + 1)) (fun k => T n k)

theorem T_zero (n k : ℕ) (h : n < k) : T n k = 0 := by
  unfold T
  have : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt h
  rw [this]; ring

theorem Dden_nn_pos (n : ℕ) : (0:ℤ) < Dden (n:ℤ) (n:ℤ) := by
  rw [Dden_eq]; ring_nf; positivity

-- boundary ratio identities (solved form over ℚ)
theorem BDRY (n : ℕ) :
    gg n n
      + ((cc0 (n:ℤ):ℚ)*(T n n:ℚ) + (cc1 (n:ℤ):ℚ)*(T (n+1) n:ℚ) + (cc2 (n:ℤ):ℚ)*(T (n+2) n:ℚ))
      + ((cc0 (n:ℤ):ℚ)*(T n (n+1):ℚ) + (cc1 (n:ℤ):ℚ)*(T (n+1) (n+1):ℚ) + (cc2 (n:ℤ):ℚ)*(T (n+2) (n+1):ℚ))
      + ((cc0 (n:ℤ):ℚ)*(T n (n+2):ℚ) + (cc1 (n:ℤ):ℚ)*(T (n+1) (n+2):ℚ) + (cc2 (n:ℤ):ℚ)*(T (n+2) (n+2):ℚ))
      = 0 := by
  -- zero terms
  have z1 : (T n (n+1) : ℚ) = 0 := by rw [T_zero n (n+1) (by omega)]; simp
  have z2 : (T n (n+2) : ℚ) = 0 := by rw [T_zero n (n+2) (by omega)]; simp
  have z3 : (T (n+1) (n+2) : ℚ) = 0 := by rw [T_zero (n+1) (n+2) (by omega)]; simp
  -- nonzero denominators
  have hd_a : (2*(4*(n:ℚ)+1)) ≠ 0 := by positivity
  have hd_b : (2*((n:ℚ)+1)^3*(4*(n:ℚ)+3)) ≠ 0 := by positivity
  have hd_c : (8*(4*(n:ℚ)+3)) ≠ 0 := by positivity
  have hd_d : (2*((n:ℚ)+1)^3*(4*(n:ℚ)+5)) ≠ 0 := by positivity
  have hd_e : (2*((n:ℚ)+2)^3*(4*(n:ℚ)+7)) ≠ 0 := by positivity
  have hd_g : (Dden (n:ℤ) (n:ℤ):ℚ) ≠ 0 := by
    have := Dden_nn_pos n; positivity
  -- ratio: ra
  have hra : (T (n+1) n : ℚ) = (T n n : ℚ) * ((5*(n:ℚ)+1)*(5*n+2)*(5*n+3)) / (2*(4*(n:ℚ)+1)) := by
    have h := rn_id n n (le_refl n)
    have e1 : 2*(n-n+1)^2*(2*n+2*n+1) = 2*(4*n+1) := by simp only [Nat.sub_self]; ring
    have e2 : (3*n+2*n+1)*(3*n+2*n+2)*(3*n+2*n+3) = (5*n+1)*(5*n+2)*(5*n+3) := by ring
    rw [e1, e2] at h
    have hQ : (T (n+1) n : ℚ) * (2*(4*(n:ℚ)+1)) = (T n n:ℚ)*((5*(n:ℚ)+1)*(5*n+2)*(5*n+3)) := by exact_mod_cast h
    rw [eq_div_iff hd_a]; linear_combination hQ
  -- rb
  have hrb : (T (n+1) (n+1) : ℚ) = (T (n+1) n : ℚ) * ((5*(n:ℚ)+4)*(5*n+5)) / (2*((n:ℚ)+1)^3*(4*(n:ℚ)+3)) := by
    have h := rk_id (n+1) n (by omega)
    have e1 : 2*(n+1)^3*(2*n+2*(n+1)+1) = 2*(n+1)^3*(4*n+3) := by ring
    have e2 : ((n+1)-n)^2*(3*(n+1)+2*n+1)*(3*(n+1)+2*n+2) = (5*n+4)*(5*n+5) := by
      have : (n+1) - n = 1 := by omega
      rw [this]; ring
    rw [e1, e2] at h
    have hQ : (T (n+1) (n+1) : ℚ) * (2*((n:ℚ)+1)^3*(4*(n:ℚ)+3)) = (T (n+1) n:ℚ)*((5*(n:ℚ)+4)*(5*n+5)) := by exact_mod_cast h
    rw [eq_div_iff hd_b]; linear_combination hQ
  -- rc
  have hrc : (T (n+2) n : ℚ) = (T (n+1) n : ℚ) * ((5*(n:ℚ)+4)*(5*n+5)*(5*n+6)) / (8*(4*(n:ℚ)+3)) := by
    have h := rn_id (n+1) n (by omega)
    have e1 : 2*((n+1)-n+1)^2*(2*n+2*(n+1)+1) = 8*(4*n+3) := by
      have : (n+1) - n = 1 := by omega
      rw [this]; ring
    have e2 : (3*(n+1)+2*n+1)*(3*(n+1)+2*n+2)*(3*(n+1)+2*n+3) = (5*n+4)*(5*n+5)*(5*n+6) := by ring
    have e3 : n + 1 + 1 = n + 2 := by omega
    rw [e1, e2, e3] at h
    have hQ : (T (n+2) n : ℚ) * (8*(4*(n:ℚ)+3)) = (T (n+1) n:ℚ)*((5*(n:ℚ)+4)*(5*n+5)*(5*n+6)) := by exact_mod_cast h
    rw [eq_div_iff hd_c]; linear_combination hQ
  -- rd
  have hrd : (T (n+2) (n+1) : ℚ) = (T (n+2) n : ℚ) * (4*(5*(n:ℚ)+7)*(5*n+8)) / (2*((n:ℚ)+1)^3*(4*(n:ℚ)+5)) := by
    have h := rk_id (n+2) n (by omega)
    have e1 : 2*(n+1)^3*(2*n+2*(n+2)+1) = 2*(n+1)^3*(4*n+5) := by ring
    have e2 : ((n+2)-n)^2*(3*(n+2)+2*n+1)*(3*(n+2)+2*n+2) = 4*(5*n+7)*(5*n+8) := by
      have : (n+2) - n = 2 := by omega
      rw [this]; ring
    rw [e1, e2] at h
    have hQ : (T (n+2) (n+1) : ℚ) * (2*((n:ℚ)+1)^3*(4*(n:ℚ)+5)) = (T (n+2) n:ℚ)*(4*(5*(n:ℚ)+7)*(5*n+8)) := by exact_mod_cast h
    rw [eq_div_iff hd_d]; linear_combination hQ
  -- re
  have hre : (T (n+2) (n+2) : ℚ) = (T (n+2) (n+1) : ℚ) * ((5*(n:ℚ)+9)*(5*n+10)) / (2*((n:ℚ)+2)^3*(4*(n:ℚ)+7)) := by
    have h := rk_id (n+2) (n+1) (by omega)
    have e1 : 2*((n+1)+1)^3*(2*(n+1)+2*(n+2)+1) = 2*((n:ℕ)+2)^3*(4*n+7) := by
      have : (n+1)+1 = n+2 := by omega
      rw [this]; ring
    have e2 : ((n+2)-(n+1))^2*(3*(n+2)+2*(n+1)+1)*(3*(n+2)+2*(n+1)+2) = (5*n+9)*(5*n+10) := by
      have : (n+2)-(n+1) = 1 := by omega
      rw [this]; ring
    have e3 : n + 1 + 1 = n + 2 := by omega
    rw [e1, e2, e3] at h
    have hQ : (T (n+2) (n+2) : ℚ) * (2*((n:ℚ)+2)^3*(4*(n:ℚ)+7)) = (T (n+2) (n+1):ℚ)*((5*(n:ℚ)+9)*(5*n+10)) := by exact_mod_cast h
    rw [eq_div_iff hd_e]; linear_combination hQ
  -- gg
  have hgg : gg n n = (Ncert (n:ℤ) (n:ℤ):ℚ) * (T n n:ℚ) / (Dden (n:ℤ) (n:ℤ):ℚ) := by
    unfold gg; rfl
  rw [z1, z2, z3, hre, hrd, hrc, hrb, hra, hgg]
  rw [Dden_eq]
  simp only [cc0, cc1, cc2, Ncert]
  push_cast
  field_simp
  ring

theorem Ncert_zero (n : ℤ) : Ncert n 0 = 0 := by unfold Ncert; ring

theorem gg_zero (n : ℕ) : gg n 0 = 0 := by
  unfold gg
  have : Ncert (n:ℤ) ((0:ℕ):ℤ) = 0 := by norm_num [Ncert_zero]
  rw [this]; simp

theorem REC (n : ℕ) :
    (cc0 (n:ℤ):ℚ)*(aN n:ℚ) + (cc1 (n:ℤ):ℚ)*(aN (n+1):ℚ) + (cc2 (n:ℤ):ℚ)*(aN (n+2):ℚ) = 0 := by
  have ea : (aN n : ℚ) = ∑ k ∈ Finset.range (n+3), (T n k : ℚ) := by
    unfold aN; push_cast
    rw [Finset.sum_range_succ (fun k => (T n k:ℚ)) (n+2), Finset.sum_range_succ (fun k => (T n k:ℚ)) (n+1)]
    rw [show (T n (n+1):ℚ) = 0 from by rw [T_zero n (n+1) (by omega)]; simp,
        show (T n (n+2):ℚ) = 0 from by rw [T_zero n (n+2) (by omega)]; simp]
    ring
  have eb : (aN (n+1) : ℚ) = ∑ k ∈ Finset.range (n+3), (T (n+1) k : ℚ) := by
    unfold aN; push_cast
    rw [show n + 1 + 1 = n + 2 from by omega]
    rw [Finset.sum_range_succ (fun k => (T (n+1) k:ℚ)) (n+2)]
    rw [show (T (n+1) (n+2):ℚ) = 0 from by rw [T_zero (n+1) (n+2) (by omega)]; simp]
    ring
  have ec : (aN (n+2) : ℚ) = ∑ k ∈ Finset.range (n+3), (T (n+2) k : ℚ) := by
    unfold aN; push_cast
    rw [show n + 2 + 1 = n + 3 from by omega]
  rw [ea, eb, ec, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have htel : ∑ k ∈ Finset.range n,
      ((cc0 (n:ℤ):ℚ)*(T n k:ℚ) + (cc1 (n:ℤ):ℚ)*(T (n+1) k:ℚ) + (cc2 (n:ℤ):ℚ)*(T (n+2) k:ℚ))
      = gg n n - gg n 0 := by
    rw [← Finset.sum_range_sub (gg n) n]
    exact Finset.sum_congr rfl (fun k hk => PS_Q n k (Finset.mem_range.mp hk))
  rw [htel, gg_zero]
  have hb := BDRY n
  linear_combination hb

theorem REC_int (n : ℕ) :
    cc0 (n:ℤ) * (aN n : ℤ) + cc1 (n:ℤ) * (aN (n+1) : ℤ) + cc2 (n:ℤ) * (aN (n+2) : ℤ) = 0 := by
  have h := REC n
  have : ((cc0 (n:ℤ) * (aN n : ℤ) + cc1 (n:ℤ) * (aN (n+1) : ℤ) + cc2 (n:ℤ) * (aN (n+2) : ℤ) : ℤ):ℚ) = 0 := by
    push_cast; linear_combination h
  exact_mod_cast this

section ZModHelpers
open Finset
open Finset

-- ascFactorial first-factor split: n.ascFactorial (k+1) = n * (n+1).ascFactorial k
theorem asc_split (n k : ℕ) : n.ascFactorial (k+1) = n * (n+1).ascFactorial k := by
  induction k with
  | zero => simp [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
  | succ k ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring

theorem choose_mul_fact (p k : ℕ) (hk : 1 ≤ k) (hkp : k ≤ p) :
    (Nat.choose (p - 1 + k) k) * (Nat.factorial k) = p.ascFactorial k := by
  have hpk : k ≤ p - 1 + k := by omega
  have h1 := Nat.choose_mul_factorial_mul_factorial hpk
  have hsub : (p - 1 + k) - k = p - 1 := by omega
  rw [hsub] at h1
  have h2 : (Nat.factorial (p-1)) * p.ascFactorial k = (Nat.factorial (p-1+k)) := by
    have := Nat.factorial_mul_ascFactorial (p-1) k
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1] at this; exact this
  rw [← h2] at h1
  have hpos : 0 < (Nat.factorial (p-1)) := Nat.factorial_pos _
  have key : (Nat.factorial (p-1)) * ((p - 1 + k).choose k * k.factorial) = (Nat.factorial (p-1)) * p.ascFactorial k := by
    rw [← Nat.mul_assoc, Nat.mul_comm (Nat.factorial (p-1))] at *
    linarith [h1]
  exact Nat.eq_of_mul_eq_mul_left hpos key

-- p divides C(p-1+k,k) for 1 ≤ k ≤ p-1
theorem p_dvd_choose1 (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    p ∣ Nat.choose (p - 1 + k) k := by
  apply hp.1.dvd_choose (a := k) (b := p - 1 + k) <;> omega

-- (A_k : ZMod p) where A_k = C(p-1+k,k)/p satisfies A_k * k = 1
-- (p+1).ascFactorial m ≡ m! mod p
theorem asc_mod (p m : ℕ) : (((p+1).ascFactorial m : ℕ) : ZMod p) = (m.factorial : ZMod p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.ascFactorial_succ, Nat.factorial_succ]
    push_cast [ih]
    have hpz : (p : ZMod p) = 0 := ZMod.natCast_self p
    have hh : ((p : ZMod p) + 1 + (m:ZMod p)) = (m:ZMod p) + 1 := by rw [hpz]; ring
    rw [hh]

theorem Ak_mod (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k) (hkp : k ≤ p - 1) :
    ((Nat.choose (p-1+k) k / p : ℕ) : ZMod p) * (k : ZMod p) = 1 := by
  have hcf := choose_mul_fact p k hk (by omega)
  have hsplit := asc_split p (k-1)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hsplit
  -- hcf: C*k! = p.asc k ; hsplit: p.asc k = p * (p+1).asc (k-1)
  rw [hsplit] at hcf
  -- hcf : C * k! = p * (p+1).asc (k-1)
  have hdvd := p_dvd_choose1 p k hk hkp
  obtain ⟨A, hA⟩ := hdvd   -- C = p * A
  rw [hA] at hcf
  -- p*A*k! = p*(p+1).asc(k-1)
  have hp0 : 0 < p := hp.1.pos
  have hAk : A * k.factorial = (p+1).ascFactorial (k-1) := by
    have : p * (A * k.factorial) = p * (p+1).ascFactorial (k-1) := by ring_nf; ring_nf at hcf; linarith [hcf]
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  -- divide: A_k = C/p = A
  have hquot : Nat.choose (p-1+k) k / p = A := by rw [hA]; exact Nat.mul_div_cancel_left A hp0
  rw [hquot]
  -- (A:ZMod p) * k = 1
  -- from hAk cast: A * k! = (k-1)! mod p, and k! = k*(k-1)!
  have hcast : (A : ZMod p) * (k.factorial : ZMod p) = ((k-1).factorial : ZMod p) := by
    have hc : ((A * k.factorial : ℕ) : ZMod p) = (((p+1).ascFactorial (k-1) : ℕ) : ZMod p) := by
      rw [hAk]
    push_cast at hc
    rw [hc, asc_mod]
  have hfact : (k.factorial : ZMod p) = (k : ZMod p) * ((k-1).factorial : ZMod p) := by
    have : k.factorial = k * (k-1).factorial := by
      conv_lhs => rw [← hk1, Nat.factorial_succ, hk1]
    rw [this]; push_cast; ring
  have hunit : ((k-1).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.Prime.dvd_factorial hp.1 |>.mp hd
    omega
  rw [hfact] at hcast
  -- (A) * (k * (k-1)!) = (k-1)!  => (A*k)*(k-1)! = 1*(k-1)!
  have : ((A : ZMod p) * (k:ZMod p)) * ((k-1).factorial : ZMod p) = 1 * ((k-1).factorial : ZMod p) := by
    rw [one_mul]; linear_combination hcast
  exact mul_right_cancel₀ hunit this


-- General product expansion modulo e^3 = 0.
-- ∏ (1 + e * b i) = 1 + e * (∑ b) + e² * ((∑b)² - ∑ b²) * half,  where 2*half=1.
theorem prod_one_add_e {R : Type*} [CommRing R] (e : R) (he : e^3 = 0)
    (half : R) (hhalf : 2 * half = 1)
    (s : Finset ℕ) (b : ℕ → R) :
    ∏ i ∈ s, (1 + e * b i)
      = 1 + e * (∑ i ∈ s, b i)
          + e^2 * ((∑ i ∈ s, b i)^2 - (∑ i ∈ s, (b i)^2)) * half := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    linear_combination (-(e^2 * b a * (∑ i ∈ s, b i))) * hhalf
      + (b a * ((∑ i ∈ s, b i)^2 - (∑ i ∈ s, (b i)^2)) * half) * he

-- Sum of all elements of ZMod p is 0 (p odd prime)
theorem sum_zmod_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : ((2:ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
      have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hneg : ∑ x : ZMod p, x = ∑ x : ZMod p, (-x) :=
    (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x => x)).symm
  rw [Finset.sum_neg_distrib] at hneg
  have h2eq : (2 : ZMod p) * ∑ x : ZMod p, x = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2eq).resolve_left h2

-- Sum of inverses of all elements is 0
theorem sum_inv_zmod_eq_zero (p : ℕ) [hp : Fact p.Prime] (hp2 : 2 < p) :
    ∑ x : ZMod p, x⁻¹ = 0 := by
  have : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
    Equiv.sum_comp (Equiv.mk (·⁻¹) (·⁻¹) inv_inv inv_inv) (fun x => x)
  rw [this]; exact sum_zmod_eq_zero p hp2


theorem prod_erase_zero (p : ℕ) [hp : Fact p.Prime] :
    ∏ x ∈ (univ : Finset (ZMod p)).erase 0, x = -1 := by
  have hp0 : 0 < p := hp.1.pos
  rw [← ZMod.prod_Ico_one_prime (p := p)]
  apply Finset.prod_nbij' (fun (x : ZMod p) => x.val) (fun (i : ℕ) => (i : ZMod p))
  · intro x hx
    rw [Finset.mem_erase] at hx
    rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h; exact hx.1 ((ZMod.val_eq_zero x).mp h)
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h; have := Nat.le_of_dvd (by omega) h; omega
  · intro x hx; simp
  · intro i hi
    rw [Finset.mem_Ico] at hi
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi.2]
  · intro x hx; rw [ZMod.natCast_val, ZMod.cast_id]

-- window product: ∏_{i ∈ range(p-1), i ≠ i₀} (↑(M - i)) = -(a+1)⁻¹ where a = ↑M
theorem window_prod (p M i₀ : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hM : p - 2 ≤ M) (hi₀ : i₀ < p - 1) (hzero : (M : ZMod p) = (i₀ : ZMod p))
    (hane : (M : ZMod p) + 1 ≠ 0) :
    ∏ i ∈ (Finset.range (p-1)).erase i₀, ((M - i : ℕ) : ZMod p) = -((M : ZMod p) + 1)⁻¹ := by
  set a : ZMod p := (M : ZMod p) with ha
  -- rewrite terms as a - ↑i
  have hterm : ∀ i ∈ (Finset.range (p-1)).erase i₀, ((M - i : ℕ) : ZMod p) = a - (i : ZMod p) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    rw [Nat.cast_sub (by omega)]
  rw [Finset.prod_congr rfl hterm]
  -- φ injective
  have hinj : Set.InjOn (fun (i:ℕ) => a - (i:ZMod p)) (↑((Finset.range (p-1)).erase i₀) : Set ℕ) := by
    intro i hi j hj h
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_range] at hi hj
    simp only at h
    have : (i : ZMod p) = (j : ZMod p) := by linear_combination -h
    have := (ZMod.natCast_eq_natCast_iff' i j p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  rw [← Finset.prod_image (f := fun (x:ZMod p) => x) (g := fun (i:ℕ) => a - (i:ZMod p)) hinj]
  -- image = (univ.erase (a+1)).erase 0
  have e1 : ((p-1:ℕ):ZMod p) = -1 := by
    have h : ((p-1:ℕ):ZMod p) = (p:ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [h, ZMod.natCast_self]; ring
  have himg : ((Finset.range (p-1)).erase i₀).image (fun (i:ℕ) => a - (i:ZMod p))
      = ((univ : Finset (ZMod p)).erase (a+1)).erase 0 := by
    ext y
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨i, ⟨hii₀, hilt⟩, rfl⟩

      refine ⟨?_, ?_⟩
      · -- a - ↑i ≠ 0
        intro h
        apply hii₀
        have hc : (i : ZMod p) = (i₀ : ZMod p) := by rw [← hzero]; linear_combination -h
        have := (ZMod.natCast_eq_natCast_iff' i i₀ p).mp hc
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      · -- a - ↑i ≠ a + 1
        intro h
        have hc : (i : ZMod p) = ((p-1:ℕ):ZMod p) := by rw [e1]; linear_combination -h
        have := (ZMod.natCast_eq_natCast_iff' i (p-1) p).mp hc
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
    · rintro ⟨hy0, hya1⟩
      have hv : ((a-y).val : ZMod p) = a - y := by rw [ZMod.natCast_val, ZMod.cast_id]
      refine ⟨(a - y).val, ⟨?_, ?_⟩, ?_⟩
      · -- (a-y).val ≠ i₀
        intro h
        apply hy0
        have h2 : (a - y) = a := by rw [← hv, h, ← hzero]
        linear_combination -h2
      · -- (a-y).val < p-1
        have hlt : (a-y).val < p := ZMod.val_lt _
        rcases Nat.lt_or_ge ((a-y).val) (p-1) with h | h
        · exact h
        · exfalso; apply hya1
          have hval : (a-y).val = p-1 := by omega
          rw [hval, e1] at hv
          linear_combination hv
      · -- a - ↑(a-y).val = y
        rw [hv]; ring
    
  rw [himg]
  -- ∏ over (erase (a+1)).erase 0 = -(a+1)⁻¹
  have hmem : (a+1) ∈ (univ : Finset (ZMod p)).erase 0 := by
    rw [Finset.mem_erase]; exact ⟨by rw [add_comm]; exact fun h => hane (by linear_combination h), Finset.mem_univ _⟩
  have := Finset.prod_erase_mul ((univ : Finset (ZMod p)).erase 0) (fun x => x) hmem
  rw [prod_erase_zero] at this
  -- this : (∏ x ∈ (erase 0).erase (a+1), x) * (a+1) = -1
  have hid : (∏ x ∈ ((univ : Finset (ZMod p)).erase 0).erase (a+1), x) = -((a+1)⁻¹) := by
    have hne : (a+1) ≠ 0 := hane
    field_simp at this ⊢
    linear_combination this
  rw [Finset.erase_right_comm] at hid
  rw [hid]
end ZModHelpers

-- ===== from Bulk =====

theorem zmod_sum_range (p:ℕ)[NeZero p](f : ZMod p → ZMod p) :
    ∑ m ∈ Finset.range p, f (m:ZMod p) = ∑ x : ZMod p, f x := by
  apply Finset.sum_nbij' (i := fun (m:ℕ) => (m : ZMod p)) (j := fun (x:ZMod p) => x.val)
  · intro a ha; exact Finset.mem_univ _
  · intro a ha; rw [Finset.mem_range]; exact ZMod.val_lt a
  · intro a ha; rw [Finset.mem_range] at ha; exact ZMod.val_cast_of_lt ha
  · intro a ha; rw [ZMod.natCast_val, ZMod.cast_id]
  · intro a ha; rfl


lemma reduce_p2' (p : ℕ) (hp : 1 ≤ p) (x y : ZMod (p^3))
    (h : (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) x
       = (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) y) :
    (p:ZMod (p^3))^2 * x = (p:ZMod (p^3))^2 * y := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  -- reduce h to val congruence
  have hx : (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  have hy : (ZMod.castHom (show p ∣ p^3 by exact ⟨p^2, by ring⟩) (ZMod p)) y = (y.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  rw [hx, hy] at h
  -- now (x.val:ZMod p) = (y.val:ZMod p), so p | x.val - y.val (in ℤ)
  have hpd : (p:ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h]; ring
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = (((p:ℤ) * d : ℤ) : ZMod (p^3)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^3))^2 * (x - y) = 0 := by
    rw [e1]
    have : (p:ZMod (p^3))^2 * (((p:ℤ) * d : ℤ) : ZMod (p^3))
         = (((p:ℕ)^3 : ℕ):ZMod (p^3)) * (d : ZMod (p^3)) := by push_cast; ring
    rw [this, ZMod.natCast_self, zero_mul]
  linear_combination e2


theorem choose_mul_fact_asc (a b : ℕ) :
    (Nat.choose (a+b) b) * b.factorial = (a+1).ascFactorial b := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left b a)
  rw [Nat.add_sub_cancel] at h1
  have h2 := Nat.factorial_mul_ascFactorial a b
  have hpos : 0 < a.factorial := Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, mul_comm ((a+1).ascFactorial b) a.factorial, h2]

-- C(p-1,k) ≡ (-1)^k mod p

theorem C_pm1_mod (p k:ℕ)[hp:Fact p.Prime](hk:k ≤ p-1) :
    ((Nat.choose (p-1) k : ℕ):ZMod p) = (-1)^k := by
  have hp0 := hp.1.pos
  have hkfu : IsUnit ((k.factorial:ℕ):ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    refine (hp.1.coprime_iff_not_dvd.mpr ?_).symm
    intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
  have hd : (p-1).descFactorial k = k.factorial * (p-1).choose k :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hprodneg : (∏ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod p)) = (-1)^k * ((k.factorial:ℕ):ZMod p) := by
    rw [show (∏ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod p)) = ∏ i ∈ Finset.range k, ((-1)*(↑(i+1):ZMod p)) from ?_]
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          show (∏ i ∈ Finset.range k, ((i+1:ℕ):ZMod p)) = ((k.factorial:ℕ):ZMod p) from by
            rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]]
    · apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      have hsum : (p-1-i) + (i+1) = p := by omega
      have h2 : ((p-1-i:ℕ):ZMod p) + ((i+1:ℕ):ZMod p) = 0 := by
        rw [← Nat.cast_add, hsum, ZMod.natCast_self]
      linear_combination h2
  have hfin : ((k.factorial:ℕ):ZMod p) * ((Nat.choose (p-1) k:ℕ):ZMod p)
            = ((k.factorial:ℕ):ZMod p) * ((-1)^k) := by
    have h1 : (((p-1).descFactorial k : ℕ):ZMod p) = ((k.factorial:ℕ):ZMod p) * ((Nat.choose (p-1) k:ℕ):ZMod p) := by
      rw [hd]; push_cast; ring
    rw [← h1, Nat.descFactorial_eq_prod_range, Nat.cast_prod, hprodneg]; ring
  exact hkfu.mul_right_injective hfin


set_option maxHeartbeats 1000000 in
theorem Bk_mod (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    ((Nat.choose (3*p-3+2*k) (p-1) / p : ℕ):ZMod p) * (2*((k:ZMod p)-1))
      = (((3*p-3+2*k)/p : ℕ):ZMod p) := by
  set M := 3*p-3+2*k with hM
  set i₀ := M % p with hi₀def
  set c := M / p with hcdef
  have hp0 := hp.1.pos
  -- basic facts about i₀, c
  have hMval : ((M:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
    have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
    have h1 : M + 3 = 3*p + 2*k := by rw [hM]; omega
    have h2 : ((M:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
      rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
    have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
    linear_combination h2 + h3
  -- i₀ ≠ p-1 : else 2k ≡ 2
  have hi₀ne : i₀ ≠ p - 1 := by
    intro hcontra
    have : ((i₀:ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hcontra]
    rw [hi₀def, ZMod.natCast_mod] at this
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hMval, hp1c] at this
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hi₀lt : i₀ < p - 1 := by
    have : i₀ < p := Nat.mod_lt _ hp0
    omega
  have hci : M - i₀ = c * p := by
    have hdm : p * c + i₀ = M := by rw [hcdef, hi₀def]; exact Nat.div_add_mod M p
    rw [Nat.mul_comm]; omega
  have hMi : ((M:ℕ):ZMod p) = ((i₀:ℕ):ZMod p) := by rw [hi₀def, ZMod.natCast_mod]
  -- C * (p-1)! = descFactorial = prod
  have hCfact : (Nat.choose M (p-1)) * (p-1).factorial = ∏ i ∈ Finset.range (p-1), (M - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have hi₀mem : i₀ ∈ Finset.range (p-1) := Finset.mem_range.mpr hi₀lt
  have hpull : ∏ i ∈ Finset.range (p-1), (M - i) = (M - i₀) * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i) := by
    rw [← Finset.mul_prod_erase _ _ hi₀mem]
  rw [hpull, hci] at hCfact
  have hdvdC : p ∣ Nat.choose M (p-1) := by
    have hpdvd : p ∣ (Nat.choose M (p-1)) * (p-1).factorial := by
      rw [hCfact]; exact ⟨c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i), by ring⟩
    rcases (Nat.Prime.dvd_mul hp.1).mp hpdvd with h | h
    · exact h
    · exfalso; have := (Nat.Prime.dvd_factorial hp.1).mp h; omega
  obtain ⟨B, hB⟩ := hdvdC
  rw [hB] at hCfact
  have hBfact : B * (p-1).factorial = c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i) := by
    have hh : p * (B * (p-1).factorial) = p * (c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i)) := by
      rw [← Nat.mul_assoc, hCfact]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 hh
  have hBeq : Nat.choose M (p-1) / p = B := by rw [hB]; exact Nat.mul_div_cancel_left B hp0
  rw [hBeq]
  have hcast : (B:ZMod p) * (((p-1).factorial:ℕ):ZMod p)
             = (c:ZMod p) * (∏ i ∈ (Finset.range (p-1)).erase i₀, ((M - i:ℕ):ZMod p)) := by
    have h := congrArg (Nat.cast (R := ZMod p)) hBfact
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod] at h
    exact h
  rw [ZMod.wilsons_lemma p] at hcast
  have hM2 : p - 2 ≤ M := by rw [hM]; omega
  have hane : ((M:ℕ):ZMod p) + 1 ≠ 0 := by
    rw [hMval]
    intro hcontra
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination hcontra
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hwin := window_prod p M i₀ hp5 hM2 hi₀lt hMi hane
  rw [hwin] at hcast
  have hMp1 : ((M:ℕ):ZMod p) + 1 = 2*((k:ZMod p)-1) := by rw [hMval]; ring
  rw [hMp1] at hcast
  have hu : (2*((k:ZMod p)-1)) * (2*((k:ZMod p)-1))⁻¹ = 1 := by
    apply mul_inv_cancel₀; rw [← hMp1]; exact hane
  have hBval : (B:ZMod p) = (c:ZMod p)*(2*((k:ZMod p)-1))⁻¹ := by linear_combination -hcast
  rw [hBval]
  linear_combination (c:ZMod p)*hu


theorem M_cast (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((3*p-3+2*k:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
  have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
  have h1 : (3*p-3+2*k) + 3 = 3*p + 2*k := by omega
  have h2 : ((3*p-3+2*k:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
    rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
  have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
  linear_combination h2 + h3


theorem M_mod_lt (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (3*p-3+2*k) % p < p - 1 := by
  have hp0 := hp.1.pos
  have hlt : (3*p-3+2*k) % p < p := Nat.mod_lt _ hp0
  rcases Nat.lt_or_ge ((3*p-3+2*k) % p) (p-1) with h|h
  · exact h
  · exfalso
    have hval : (3*p-3+2*k) % p = p - 1 := by omega
    have hc : (((3*p-3+2*k) % p : ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hval]
    rw [ZMod.natCast_mod, M_cast p k hp5] at hc
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hp1c] at hc
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination hc
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega


theorem p_dvd_choose2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    p ∣ Nat.choose (3*p-3+2*k) (p-1) := by
  set M := 3*p-3+2*k with hM
  have hp0 := hp.1.pos
  have hi₀lt : M % p < p - 1 := M_mod_lt p k hp5 hk2 hkp
  have hCfact : (Nat.choose M (p-1)) * (p-1).factorial = ∏ i ∈ Finset.range (p-1), (M - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have hi₀mem : M % p ∈ Finset.range (p-1) := Finset.mem_range.mpr hi₀lt
  have hfac : p ∣ (M - M % p) := ⟨M / p, by have := Nat.div_add_mod M p; omega⟩
  have hdvd : p ∣ ∏ i ∈ Finset.range (p-1), (M - i) :=
    dvd_trans hfac (Finset.dvd_prod_of_mem _ hi₀mem)
  rw [← hCfact] at hdvd
  rcases (Nat.Prime.dvd_mul hp.1).mp hdvd with h | h
  · exact h
  · exfalso; have := (Nat.Prime.dvd_factorial hp.1).mp h; omega


set_option maxHeartbeats 1000000 in
theorem Mk_val (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (((Nat.choose (p-1) k)^2 * (Nat.choose ((p-1)+k) k / p) * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ):ZMod p)
      = (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (((k-1:ℕ):ZMod p)⁻¹ - ((k:ℕ):ZMod p)⁻¹) := by
  have hkne : ((k:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have hk1ne : ((k-1:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by omega) h; omega
  have h2ne : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hk1cast : ((k-1:ℕ):ZMod p) = (k:ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcp := C_pm1_mod p k hkp
  have hak := Ak_mod p k (by omega) hkp
  have hbk := Bk_mod p k hp5 hk2 hkp
  -- expand casts
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hcp]
  -- ((-1)^k)^2 = 1
  have hcc2 : ((-1:ZMod p)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hcc2, one_mul]
  -- now: A_k * B_k = ...
  -- A_k = k⁻¹, B_k = c*(2(k-1))⁻¹
  have hAA : ((Nat.choose ((p-1)+k) k / p:ℕ):ZMod p) = (k:ZMod p)⁻¹ := eq_inv_of_mul_eq_one_left hak
  have hk1ne2 : ((k:ZMod p)-1) ≠ 0 := by rw [← hk1cast]; exact hk1ne
  have hXne : (2*((k:ZMod p)-1)) ≠ 0 := mul_ne_zero h2ne hk1ne2
  have hBB : ((Nat.choose (3*p-3+2*k) (p-1) / p:ℕ):ZMod p) = (((3*p-3+2*k)/p:ℕ):ZMod p) * (2*((k:ZMod p)-1))⁻¹ := by
    field_simp [h2ne, hk1ne2]
    linear_combination hbk
  rw [hAA, hBB, hk1cast]
  field_simp [hkne, hk1ne2, h2ne]
  ring


theorem T_factor (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    T (p-1) k = p^2 * ((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p)) := by
  unfold T
  have e2 : 3*(p-1)+2*k = 3*p-3+2*k := by omega
  have hd1 := p_dvd_choose1 p k (by omega) hkp
  have hd2 := p_dvd_choose2 p k hp5 hk2 hkp
  have hA : Nat.choose (p-1+k) k = p * (Nat.choose (p-1+k) k / p) := (Nat.mul_div_cancel' hd1).symm
  have hB : Nat.choose (3*p-3+2*k) (p-1) = p * (Nat.choose (3*p-3+2*k) (p-1) / p) := (Nat.mul_div_cancel' hd2).symm
  rw [e2]
  rw [show (p-1)+k = p-1+k from rfl]
  conv_lhs => rw [hA, hB]
  ring


lemma tele {A:Type*}[AddCommGroup A](a:ℕ)(ha:1≤a)(G:ℕ→A) :
    ∀ b, a-1 ≤ b → ∑ k ∈ Finset.Icc a b, (G (k-1) - G k) = G (a-1) - G b := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega)]; simp
  | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      rw [show b+1-1 = b by omega]; abel


set_option maxHeartbeats 1000000 in
theorem sum_Mk (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    2 * ∑ k ∈ Finset.Icc 2 (p-1),
      (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ) : ZMod p) = 9 := by
  have hodd : p % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
  set m := (p+1)/2 with hm
  have h2m : 2*m = p+1 := by rw [hm]; omega
  set G : ℕ → ZMod p := fun j => ((j:ℕ):ZMod p)⁻¹ with hG
  -- rewrite summand
  have hsumrw : ∑ k ∈ Finset.Icc 2 (p-1),
      (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ) : ZMod p)
      = ∑ k ∈ Finset.Icc 2 (p-1),
          (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have := Mk_val p k hp5 hk.1 hk.2
    rw [this, hG]
  rw [hsumrw]
  -- split Icc 2 (p-1) = Icc 2 m ∪ Icc (m+1) (p-1)  via Ioc
  have hIcc1 : Finset.Icc 2 (p-1) = Finset.Ioc 1 (p-1) := by
    rw [show (2:ℕ) = 1+1 from rfl, Icc_add_one_left_eq_Ioc]
  have hIcc2 : Finset.Icc 2 m = Finset.Ioc 1 m := by
    rw [show (2:ℕ) = 1+1 from rfl, Icc_add_one_left_eq_Ioc]
  have hIcc3 : Finset.Icc (m+1) (p-1) = Finset.Ioc m (p-1) := by
    rw [Icc_add_one_left_eq_Ioc]
  have hsplit : ∑ k ∈ Finset.Icc 2 (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
      = (∑ k ∈ Finset.Icc 2 m, (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k))
      + (∑ k ∈ Finset.Icc (m+1) (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)) := by
    rw [hIcc1, hIcc2, hIcc3]
    rw [← Finset.sum_Ioc_consecutive _ (show 1 ≤ m by omega) (show m ≤ p-1 by omega)]
  rw [hsplit]
  -- region 1: ck = 3
  have hr1 : ∑ k ∈ Finset.Icc 2 m, (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
      = (3:ZMod p) * (2:ZMod p)⁻¹ * (G 1 - G m) := by
    rw [show ∑ k ∈ Finset.Icc 2 m, (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
          = ∑ k ∈ Finset.Icc 2 m, (3:ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k) from ?_]
    · rw [← Finset.mul_sum, tele 2 (by omega) G m (by omega)]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hck : (3*p-3+2*k)/p = 3 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hck]; norm_num
  -- region 2: ck = 4
  have hr2 : ∑ k ∈ Finset.Icc (m+1) (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
      = (4:ZMod p) * (2:ZMod p)⁻¹ * (G m - G (p-1)) := by
    rw [show ∑ k ∈ Finset.Icc (m+1) (p-1), (((3*p-3+2*k)/p : ℕ):ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k)
          = ∑ k ∈ Finset.Icc (m+1) (p-1), (4:ZMod p) * (2:ZMod p)⁻¹ * (G (k-1) - G k) from ?_]
    · rw [← Finset.mul_sum, tele (m+1) (by omega) G (p-1) (by omega)]
      rw [show (m+1)-1 = m by omega]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hck : (3*p-3+2*k)/p = 4 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [hck]; norm_num
  rw [hr1, hr2]
  -- G values
  have hG1 : G 1 = 1 := by rw [hG]; simp
  have h2ne : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hGm : G m = 2 := by
    simp only [hG]
    have hmc : (m:ZMod p) = (2:ZMod p)⁻¹ := by
      have : (2:ZMod p) * (m:ZMod p) = 1 := by
        have : ((2*m:ℕ):ZMod p) = ((p+1:ℕ):ZMod p) := by rw [h2m]
        push_cast at this
        rw [ZMod.natCast_self] at this
        linear_combination this
      field_simp at this ⊢
      linear_combination this
    rw [hmc, inv_inv]
  have hGp1 : G (p-1) = -1 := by
    simp only [hG]
    have hpm1 : ((p-1:ℕ):ZMod p) = -1 := by
      rw [Nat.cast_sub (by omega)]; rw [ZMod.natCast_self]; simp
    rw [hpm1]; simp
  rw [hG1, hGm, hGp1]
  field_simp
  ring


set_option maxHeartbeats 1000000 in
theorem bulk_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((2 * ∑ k ∈ Finset.Icc 2 (p-1), T (p-1) k : ℕ) : ZMod (p^3))
      = 9 * (p:ZMod (p^3))^2 := by
  set Mk : ℕ → ℕ := fun k => (Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p)
        * (Nat.choose (3*p-3+2*k) (p-1) / p) with hMk
  have hTf : ∑ k ∈ Finset.Icc 2 (p-1), T (p-1) k = p^2 * ∑ k ∈ Finset.Icc 2 (p-1), Mk k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [hMk]; exact T_factor p k hp5 hk.1 hk.2
  set S := ∑ k ∈ Finset.Icc 2 (p-1), Mk k with hS
  rw [hTf]
  have hpc : ((2 * (p^2 * S) : ℕ) : ZMod (p^3)) = (p:ZMod (p^3))^2 * ((2*S:ℕ):ZMod (p^3)) := by
    push_cast; ring
  rw [hpc]
  have hred := reduce_p2' p (by omega) (((2*S:ℕ)):ZMod (p^3)) (((9:ℕ)):ZMod (p^3)) ?_
  · rw [hred]; push_cast; ring
  · rw [map_natCast, map_natCast]
    rw [Nat.cast_mul, hS, Nat.cast_sum]
    simp only [hMk, Nat.cast_ofNat]
    exact sum_Mk p hp5

lemma peel2 {F:Type*}[AddCommMonoid F](g:ℕ→F)(N:ℕ)(hN:2≤N) :
    ∑ k ∈ Finset.range N, g k = (∑ k ∈ Finset.range (N-2), g k) + g (N-2) + g (N-1) := by
  obtain ⟨M,rfl⟩ : ∃ M, N=M+2 := ⟨N-2, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  congr 2

-- harmonic sum over [1,p-3] = 3/2  (range form)


lemma pprod2 {R:Type*}[CommMonoid R](f:ℕ→R)(N:ℕ)(hN:2≤N) :
    ∏ i ∈ Finset.range N, f i = (∏ i ∈ Finset.range (N-2), f (i+2)) * f 1 * f 0 := by
  obtain ⟨M,rfl⟩ : ∃ M, N=M+2 := ⟨N-2, by omega⟩
  rw [Finset.prod_range_succ', Finset.prod_range_succ']
  simp only [Nat.add_sub_cancel]




theorem harmonic_range (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-3), ((i+1:ℕ):ZMod p)⁻¹ = 3 * (2:ZMod p)⁻¹ := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hp2 : 2 < p := by omega
  have hfull : ∑ m ∈ Finset.range p, ((m:ZMod p))⁻¹ = 0 := by
    rw [zmod_sum_range]; exact sum_inv_zmod_eq_zero p hp2
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  rw [Finset.sum_range_succ'] at hfull
  simp only [Nat.cast_zero, inv_zero, add_zero] at hfull
  rw [peel2 (fun k => ((k+1:ℕ):ZMod (n+1))⁻¹) n (by omega)] at hfull
  have c1 : ((n-2+1 : ℕ):ZMod (n+1)) = -2 := by
    have h0 : ((n-2+1:ℕ):ZMod (n+1)) + 2 = 0 := by
      have : ((n-2+1:ℕ):ZMod (n+1)) + 2 = (((n-2+1)+2 : ℕ):ZMod (n+1)) := by push_cast; ring
      rw [this, show (n-2+1)+2 = n+1 by omega, ZMod.natCast_self]
    linear_combination h0
  have c2 : ((n-1+1 : ℕ):ZMod (n+1)) = -1 := by
    have h0 : ((n-1+1:ℕ):ZMod (n+1)) + 1 = 0 := by
      have : ((n-1+1:ℕ):ZMod (n+1)) + 1 = (((n-1+1)+1 : ℕ):ZMod (n+1)) := by push_cast; ring
      rw [this, show (n-1+1)+1 = n+1 by omega, ZMod.natCast_self]
    linear_combination h0
  rw [c1, c2] at hfull
  have h2 : (2:ZMod (n+1)) ≠ 0 := by
    have : ((2:ℕ):ZMod (n+1)) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  rw [show n+1-3 = n-2 by omega]
  simp only [inv_neg, inv_one] at hfull
  linear_combination hfull - inv_mul_cancel₀ h2



lemma castHom_inv (p a:ℕ)[Fact p.Prime](hcop: a.Coprime p) :
    (ZMod.castHom (show p∣p^3 from ⟨p^2,by ring⟩) (ZMod p)) ((a:ZMod (p^3))⁻¹) = ((a:ZMod p))⁻¹ := by
  have hu : IsUnit ((a:ZMod (p^3))) := by rw[ZMod.isUnit_iff_coprime]; exact hcop.pow_right 3
  have h1 : (ZMod.castHom (show p∣p^3 from ⟨p^2,by ring⟩) (ZMod p)) ((a:ZMod (p^3))) = (a:ZMod p) := map_natCast _ a
  have h2 : (a:ZMod p) * (ZMod.castHom (show p∣p^3 from ⟨p^2,by ring⟩) (ZMod p)) ((a:ZMod (p^3))⁻¹) = 1 := by
    rw [← h1, ← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm



set_option maxHeartbeats 1000000 in
theorem T0_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (2 * (Nat.choose (3*p-3) (p-1)) : ZMod (p^3))
      = -2*(p:ZMod (p^3)) - 5*(p:ZMod (p^3))^2 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  -- integer identity
  have hC : (Nat.choose (3*n) n) * n.factorial = (2*n+1).ascFactorial n := by
    have h := choose_mul_fact_asc (2*n) n
    rwa [show 2*n+n = 3*n by ring] at h
  rw [show 3*(n+1)-3 = 3*n by omega, show (n+1)-1 = n by omega]
  -- key abbreviation
  set P : ZMod ((n+1)^3) := ((n+1:ℕ):ZMod ((n+1)^3)) with hP
  have hP3 : P^3 = 0 := by rw [hP, ← Nat.cast_pow, ZMod.natCast_self]
  -- 2 is a unit
  have h2cop : (2:ℕ).Coprime (n+1) := (Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)
  have h2u : IsUnit ((2:ℕ):ZMod ((n+1)^3)) := by rw [ZMod.isUnit_iff_coprime]; exact h2cop.pow_right 3
  set half : ZMod ((n+1)^3) := ((2:ℕ):ZMod ((n+1)^3))⁻¹ with hhalf0
  have hhalf : 2 * half = 1 := by
    rw [hhalf0]
    have : (2:ZMod ((n+1)^3)) = ((2:ℕ):ZMod ((n+1)^3)) := by push_cast; ring
    rw [this]; exact ZMod.mul_inv_of_unit _ h2u
  -- cast the integer identity, expand product
  have hCz : ((Nat.choose (3*n) n : ℕ):ZMod ((n+1)^3)) * ((n.factorial:ℕ):ZMod ((n+1)^3))
            = (((2*n+1).ascFactorial n : ℕ):ZMod ((n+1)^3)) := by
    rw [← Nat.cast_mul, hC]
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod] at hCz
  rw [pprod2 (fun i => ((2*n+1+i:ℕ):ZMod ((n+1)^3))) n (by omega)] at hCz
  -- rewrite the middle product into factorial * (prod of 1+e*b)
  have hbig : ∏ i ∈ Finset.range (n-2), ((2*n+1+(i+2):ℕ):ZMod ((n+1)^3))
            = (((n-2).factorial : ℕ):ZMod ((n+1)^3))
              * ∏ i ∈ Finset.range (n-2), (1 + (2*P) * ((i+1:ℕ):ZMod ((n+1)^3))⁻¹) := by
    rw [← Finset.prod_range_add_one_eq_factorial (n-2), Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hcop : (i+1).Coprime (n+1) :=
      (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
    have huu : ((i+1:ℕ):ZMod ((n+1)^3)) * (((i+1:ℕ):ZMod ((n+1)^3)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 3)
    rw [show ((2*n+1+(i+2):ℕ):ZMod ((n+1)^3)) = ((i+1:ℕ):ZMod ((n+1)^3)) + 2*P from by rw [hP]; push_cast; ring]
    linear_combination -(2*P)*huu
  rw [hbig] at hCz
  -- apply prod_one_add_e
  rw [prod_one_add_e (2*P) (by rw [mul_pow]; rw [hP3]; ring) half hhalf
        (Finset.range (n-2)) (fun i => ((i+1:ℕ):ZMod ((n+1)^3))⁻¹)] at hCz
  -- now hCz: C * (n! cast) = ((n-2)! * (1 + 2P*Σ + (2P)^2*G*half)) * f1 * f0
  -- simplify f0, f1
  have hf0 : ((2*n+1+0:ℕ):ZMod ((n+1)^3)) = 2*P - 1 := by rw [hP]; push_cast; ring
  have hf1 : ((2*n+1+1:ℕ):ZMod ((n+1)^3)) = 2*P := by rw [hP]; push_cast; ring
  rw [hf0, hf1] at hCz
  -- relate (n!) and (n-2)!
  have hfact : (n.factorial : ℕ) = n * (n-1) * (n-2).factorial := by
    have e1 : n = (n-1)+1 := by omega
    have e2 : n-1 = (n-2)+1 := by omega
    rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
    rw [← e2, ← e1]; ring
  rw [hfact, Nat.cast_mul, Nat.cast_mul] at hCz
  -- cast n and n-1
  have hcn : ((n:ℕ):ZMod ((n+1)^3)) = P - 1 := by rw [hP]; push_cast; ring
  have hcn1 : ((n-1:ℕ):ZMod ((n+1)^3)) = P - 2 := by
    rw [hP, show (n-1:ℕ) = n-1 from rfl, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcn, hcn1] at hCz
  -- Now harmonic reduction:  P^2 * (-4 * Σ) = P^2 * (-6)
  set Sb : ZMod ((n+1)^3) := ∑ i ∈ Finset.range (n-2), ((i+1:ℕ):ZMod ((n+1)^3))⁻¹ with hSb
  have hred : P^2 * (-4 * Sb) = P^2 * (-6 : ZMod ((n+1)^3)) := by
    rw [hP]
    apply reduce_p2' (n+1) (by omega)
    -- castHom of Sb = harmonic value
    have hcast : (ZMod.castHom (show (n+1) ∣ (n+1)^3 by exact ⟨(n+1)^2, by ring⟩) (ZMod (n+1))) Sb
               = 3 * (2:ZMod (n+1))⁻¹ := by
      rw [hSb, map_sum]
      rw [show (∑ i ∈ Finset.range (n-2), (ZMod.castHom (show (n+1) ∣ (n+1)^3 by exact ⟨(n+1)^2, by ring⟩) (ZMod (n+1))) (((i+1:ℕ):ZMod ((n+1)^3))⁻¹))
            = ∑ i ∈ Finset.range (n+1-3), ((i+1:ℕ):ZMod (n+1))⁻¹ from ?_]
      · exact harmonic_range (n+1) hp5
      · rw [show n+1-3 = n-2 by omega]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        exact castHom_inv (n+1) (i+1) hcop
    have h2u' : (2:ZMod (n+1)) ≠ 0 := by
      have : ((2:ℕ):ZMod (n+1)) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    rw [show (-4 * Sb : ZMod ((n+1)^3)) = ((-4:ℤ):ZMod ((n+1)^3))*Sb from by push_cast; ring,
        show ((-6:ZMod ((n+1)^3))) = ((-6:ℤ):ZMod ((n+1)^3)) from by push_cast; ring,
        map_mul, map_intCast, map_intCast, hcast]
    push_cast
    field_simp
    ring
  set C := ((3*n).choose n : ZMod ((n+1)^3)) with hCdef
  set S2 := ∑ i ∈ Finset.range (n-2), (((i+1:ℕ):ZMod ((n+1)^3))⁻¹)^2 with hS2def
  set F2 := (((n-2).factorial:ℕ):ZMod ((n+1)^3)) with hF2def
  have hF2u : IsUnit F2 := by
    rw [hF2def, ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega)).symm))
  have hPu : IsUnit ((P-1)*(P-2)) := by
    have hu1 : IsUnit (P-1) := by
      rw [← hcn, ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    have hu2 : IsUnit (P-2) := by
      rw [← hcn1, ZMod.isUnit_iff_coprime]
      exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := Nat.le_of_dvd (by omega) hd; omega)).symm))
    exact hu1.mul hu2
  have hkey : F2 * (C*(P-1)*(P-2))
            = F2 * ((1 + 2*P*Sb + (2*P)^2*(Sb^2-S2)*half)*(2*P)*(2*P-1)) := by
    linear_combination hCz
  have hEq1 := hF2u.mul_right_injective hkey
  have hEq2 : C*(P-1)*(P-2) = -2*P-2*P^2 := by
    rw [hEq1]
    linear_combination hred + (8*Sb - 8*(Sb^2-S2)*half + 16*P*(Sb^2-S2)*half)*hP3
  have hC2 : (2*C)*((P-1)*(P-2)) = (-2*P-5*P^2)*((P-1)*(P-2)) := by
    have h0 : (2*C)*((P-1)*(P-2)) = 2*(C*(P-1)*(P-2)) := by ring
    rw [h0, hEq2]
    linear_combination (5*P-13)*hP3
  have hfin := hPu.mul_left_injective hC2
  linear_combination hfin




theorem harmonic_full (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-1), ((i+1:ℕ):ZMod p)⁻¹ = 0 := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hp2 : 2 < p := by omega
  have hfull : ∑ m ∈ Finset.range p, ((m:ZMod p))⁻¹ = 0 := by
    rw [zmod_sum_range]; exact sum_inv_zmod_eq_zero p hp2
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  rw [Finset.sum_range_succ'] at hfull
  simp only [Nat.cast_zero, inv_zero, add_zero] at hfull
  rw [show n+1-1 = n by omega]
  exact hfull

-- reduce: p * x = p * y  in ZMod (p^3) from equality mod p^2


lemma reduce_p1_3 (p : ℕ) (hp : 1 ≤ p) (x y : ZMod (p^3))
    (h : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) x
       = (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) y) :
    (p:ZMod (p^3)) * x = (p:ZMod (p^3)) * y := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hx : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) x = (x.val : ZMod (p^2)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  have hy : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) y = (y.val : ZMod (p^2)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  rw [hx, hy] at h
  have hpd : ((p:ℤ)^2) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    have hd0 : (((p^2:ℕ)):ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
    rwa [Nat.cast_pow] at hd0
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = ((((p:ℤ)^2) * d : ℤ) : ZMod (p^3)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^3)) * (x - y) = 0 := by
    rw [e1]
    have : (p:ZMod (p^3)) * ((((p:ℤ)^2) * d : ℤ) : ZMod (p^3))
         = (((p:ℕ)^3 : ℕ):ZMod (p^3)) * (d : ZMod (p^3)) := by push_cast; ring
    rw [this, ZMod.natCast_self, zero_mul]
  linear_combination e2



lemma reduce_gen (p a b:ℕ)(hp:1≤p)(hba:b≤a)(x y:ZMod (p^a))
    (h : (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) x
       = (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) y) :
    (p:ZMod (p^a))^(a-b) * x = (p:ZMod (p^a))^(a-b) * y := by
  haveI : NeZero (p^a) := ⟨by positivity⟩
  haveI : NeZero (p^b) := ⟨by positivity⟩
  have hx : (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) x = (x.val : ZMod (p^b)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]; rw [map_natCast]
  have hy : (ZMod.castHom (pow_dvd_pow p hba) (ZMod (p^b))) y = (y.val : ZMod (p^b)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]; rw [map_natCast]
  rw [hx, hy] at h
  have hpd : ((p:ℤ)^b) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    have hd0 : (((p^b:ℕ)):ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
    rwa [Nat.cast_pow] at hd0
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = ((((p:ℤ)^b) * d : ℤ) : ZMod (p^a)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^a))^(a-b) * (x - y) = 0 := by
    rw [e1]
    have hcast : (p:ZMod (p^a))^(a-b) * ((((p:ℤ)^b) * d : ℤ) : ZMod (p^a))
         = (((p:ℕ)^a : ℕ):ZMod (p^a)) * (d : ZMod (p^a)) := by
      push_cast
      rw [← mul_assoc, ← pow_add, show a-b+b = a by omega]
    rw [hcast, ZMod.natCast_self, zero_mul]
  linear_combination e2



lemma castHom_inv_to_p (p e a:ℕ)[Fact p.Prime](he:1≤e)(hcop: a.Coprime p) :
    (ZMod.castHom (dvd_pow_self p (show e ≠ 0 by omega)) (ZMod p)) ((a:ZMod (p^e))⁻¹) = ((a:ZMod p))⁻¹ := by
  have hu : IsUnit ((a:ZMod (p^e))) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right e
  have h1 : (ZMod.castHom (dvd_pow_self p (show e ≠ 0 by omega)) (ZMod p)) ((a:ZMod (p^e))) = (a:ZMod p) := map_natCast _ a
  have h2 : (a:ZMod p) * (ZMod.castHom (dvd_pow_self p (show e ≠ 0 by omega)) (ZMod p)) ((a:ZMod (p^e))⁻¹) = 1 := by
    rw [← h1, ← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
  exact (inv_eq_of_mul_eq_one_right h2).symm



lemma reduce_p0_2 (p : ℕ) (hp : 1 ≤ p) (x y : ZMod (p^2))
    (h : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) x
       = (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) y) :
    (p:ZMod (p^2)) * x = (p:ZMod (p^2)) * y := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hx : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]; rw [map_natCast]
  have hy : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) y = (y.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val y]; rw [map_natCast]
  rw [hx, hy] at h
  have hpd : (p:ℤ) ∣ ((x.val:ℤ) - (y.val:ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  obtain ⟨d, hd⟩ := hpd
  have e1 : x - y = (((p:ℤ) * d : ℤ) : ZMod (p^2)) := by
    rw [← hd, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have e2 : (p:ZMod (p^2)) * (x - y) = 0 := by
    rw [e1]
    have hcast : (p:ZMod (p^2)) * (((p:ℤ) * d : ℤ) : ZMod (p^2))
         = (((p:ℕ)^2 : ℕ):ZMod (p^2)) * (d : ZMod (p^2)) := by push_cast; ring
    rw [hcast, ZMod.natCast_self, zero_mul]
  linear_combination e2



set_option maxHeartbeats 1000000 in
theorem C3p1_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((Nat.choose (3*p-1) (p-1) : ℕ):ZMod (p^2)) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  have hC : (Nat.choose (3*n+2) n) * n.factorial = (2*n+3).ascFactorial n := by
    have h := choose_mul_fact_asc (2*n+2) n
    rwa [show 2*n+2+n = 3*n+2 by ring, show 2*n+2+1 = 2*n+3 by ring] at h
  rw [show 3*(n+1)-1 = 3*n+2 by omega, show (n+1)-1 = n by omega]
  set P : ZMod ((n+1)^2) := ((n+1:ℕ):ZMod ((n+1)^2)) with hP
  have hP2 : P^2 = 0 := by rw [hP, ← Nat.cast_pow, ZMod.natCast_self]
  have hP3 : P^3 = 0 := by rw [show (3:ℕ) = 2+1 by rfl, pow_add, hP2, zero_mul]
  have h2cop : (2:ℕ).Coprime (n+1) := (Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)
  have h2u : IsUnit ((2:ℕ):ZMod ((n+1)^2)) := by rw [ZMod.isUnit_iff_coprime]; exact h2cop.pow_right 2
  set half : ZMod ((n+1)^2) := ((2:ℕ):ZMod ((n+1)^2))⁻¹ with hhalf0
  have hhalf : 2 * half = 1 := by
    rw [hhalf0]; rw [show (2:ZMod ((n+1)^2)) = ((2:ℕ):ZMod ((n+1)^2)) by push_cast; ring]
    exact ZMod.mul_inv_of_unit _ h2u
  -- cast and expand product
  have hCz : ((Nat.choose (3*n+2) n : ℕ):ZMod ((n+1)^2)) * ((n.factorial:ℕ):ZMod ((n+1)^2))
            = (((2*n+3).ascFactorial n : ℕ):ZMod ((n+1)^2)) := by rw [← Nat.cast_mul, hC]
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod] at hCz
  -- product into factorial * prod(1+e b)
  have hbig : ∏ i ∈ Finset.range n, ((2*n+3+i:ℕ):ZMod ((n+1)^2))
            = ((n.factorial : ℕ):ZMod ((n+1)^2))
              * ∏ i ∈ Finset.range n, (1 + (2*P) * ((i+1:ℕ):ZMod ((n+1)^2))⁻¹) := by
    rw [← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hcop : (i+1).Coprime (n+1) :=
      (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
    have huu : ((i+1:ℕ):ZMod ((n+1)^2)) * (((i+1:ℕ):ZMod ((n+1)^2)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 2)
    rw [show ((2*n+3+i:ℕ):ZMod ((n+1)^2)) = ((i+1:ℕ):ZMod ((n+1)^2)) + 2*P from by rw [hP]; push_cast; ring]
    linear_combination -(2*P)*huu
  rw [hbig] at hCz
  rw [prod_one_add_e (2*P) (by rw [mul_pow]; rw [hP3]; ring) half hhalf
        (Finset.range n) (fun i => ((i+1:ℕ):ZMod ((n+1)^2))⁻¹)] at hCz
  -- the e^2 term vanishes since (2P)^2 = 0
  set Sb : ZMod ((n+1)^2) := ∑ i ∈ Finset.range n, ((i+1:ℕ):ZMod ((n+1)^2))⁻¹ with hSb
  set S2 : ZMod ((n+1)^2) := ∑ i ∈ Finset.range n, (((i+1:ℕ):ZMod ((n+1)^2))⁻¹)^2 with hS2
  -- 2P * Sb = 0
  have hred : (2*P) * Sb = 0 := by
    have hstep : (2*P)*Sb = (↑(n+1):ZMod ((n+1)^2)) * (2*Sb) := by rw [hP]; ring
    rw [hstep]
    have h0 : (↑(n+1):ZMod ((n+1)^2)) * (2*Sb) = (↑(n+1):ZMod ((n+1)^2)) * (0:ZMod ((n+1)^2)) := by
      apply reduce_p0_2 (n+1) (by omega)
      rw [map_mul, map_sum, map_zero]
      have hsum0 : (∑ i ∈ Finset.range n, (ZMod.castHom (dvd_pow_self (n+1) (show (2:ℕ) ≠ 0 by omega)) (ZMod (n+1))) (((i+1:ℕ):ZMod ((n+1)^2))⁻¹)) = (0:ZMod (n+1)) := by
        rw [← harmonic_full (n+1) hp5]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        exact castHom_inv_to_p (n+1) 2 (i+1) (by omega) hcop
      rw [hsum0]; ring
    rw [h0]; ring
  -- now hCz: C * n! = n! * (1 + 2P*Sb + (2P)^2*(Sb^2-S2)*half)
  set C := ((3*n+2).choose n : ZMod ((n+1)^2)) with hCdef
  set F := ((n.factorial:ℕ):ZMod ((n+1)^2)) with hFdef
  have hFu : IsUnit F := by
    rw [hFdef, ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right 2 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega)).symm))
  have hkey : F * C = F * 1 := by
    rw [mul_one]
    have hsq : (2*P)^2 = 0 := by rw [mul_pow, hP2]; ring
    linear_combination hCz + (F * (Sb^2 - S2) * half) * hsq + F * hred
  exact hFu.mul_right_injective hkey



set_option maxHeartbeats 1000000 in
theorem T1_mod (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (2 * ((Nat.choose (p-1) 1)^2 * (Nat.choose ((p-1)+1) 1) * (Nat.choose (3*(p-1)+2*1) (p-1))) : ZMod (p^3))
      = 2*(p:ZMod (p^3)) - 4*(p:ZMod (p^3))^2 := by
  have hC3 := C3p1_mod p hp5
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  rw [show (n+1)-1 = n by omega, Nat.choose_one_right, Nat.choose_one_right,
      show 3*n+2*1 = 3*n+2 by ring, show 3*(n+1)-1 = 3*n+2 by omega] at *
  have hQ2 : ((n+1:ℕ):ZMod ((n+1)^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have key : (↑(n+1):ZMod ((n+1)^3)) * (2*((↑(n+1):ZMod ((n+1)^3))-1)^2*(↑((3*n+2).choose n):ZMod ((n+1)^3)))
           = (↑(n+1):ZMod ((n+1)^3)) * (2 - 4*(↑(n+1):ZMod ((n+1)^3))) := by
    apply reduce_p1_3 (n+1) (by omega)
    simp only [map_mul, map_pow, map_sub, map_ofNat, map_one, map_natCast]
    rw [hC3]
    linear_combination (2:ZMod ((n+1)^2)) * hQ2
  rw [show (2 * ((n:ZMod ((n+1)^3))^2 * (↑(n+1)) * ↑((3*n+2).choose n)) : ZMod ((n+1)^3))
        = (↑(n+1):ZMod ((n+1)^3)) * (2*((↑(n+1):ZMod ((n+1)^3))-1)^2*(↑((3*n+2).choose n))) from by push_cast; ring,
      show (2*(↑(n+1):ZMod ((n+1)^3)) - 4*(↑(n+1):ZMod ((n+1)^3))^2 : ZMod ((n+1)^3))
        = (↑(n+1):ZMod ((n+1)^3))*(2-4*(↑(n+1):ZMod ((n+1)^3))) from by ring]
  exact key




theorem apm1 (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (p^3 : ℕ) ∣ ∑ k ∈ Finset.range p, T (p-1) k := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  have hT0eq : T (p-1) 0 = Nat.choose (3*p-3) (p-1) := by
    unfold T
    rw [show 3*(p-1)+2*0 = 3*p-3 by omega]
    simp
  have hT1eq : T (p-1) 1 = (Nat.choose (p-1) 1)^2 * (Nat.choose ((p-1)+1) 1) * (Nat.choose (3*(p-1)+2*1) (p-1)) := rfl
  have e : (∑ k ∈ Finset.range p, T (p-1) k)
      = T (p-1) 0 + T (p-1) 1 + ∑ k ∈ Finset.Icc 2 (p-1), T (p-1) k := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) (show 2 ≤ p by omega),
        Nat.Ico_zero_eq_range, Finset.sum_range_succ, Finset.sum_range_one,
        show Finset.Ico 2 p = Finset.Icc 2 (p-1) by ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega]
  have h2u : IsUnit ((2:ℕ):ZMod (p^3)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)).pow_right 3
  have key : ((2:ℕ):ZMod (p^3)) * ((∑ k ∈ Finset.range p, T (p-1) k :ℕ):ZMod (p^3)) = 0 := by
    rw [e, Nat.cast_add, Nat.cast_add, hT0eq]
    have a0 := T0_mod p hp5
    have a1 := T1_mod p hp5
    have a2 := bulk_mod p hp5
    rw [Nat.cast_mul, Nat.cast_ofNat] at a2
    have hT1cast : ((T (p-1) 1 :ℕ):ZMod (p^3))
        = ((Nat.choose (p-1) 1):ZMod (p^3))^2 * ((Nat.choose ((p-1)+1) 1):ZMod (p^3))
            * ((Nat.choose (3*(p-1)+2*1) (p-1)):ZMod (p^3)) := by
      rw [hT1eq]; push_cast; ring
    rw [hT1cast, Nat.cast_ofNat]
    linear_combination a0 + a1 + a2
  have hN0 : ((∑ k ∈ Finset.range p, T (p-1) k :ℕ):ZMod (p^3)) = 0 :=
    (h2u.mul_right_eq_zero).mp key
  exact (ZMod.natCast_eq_zero_iff _ (p^3)).mp hN0


-- ===== induction machinery =====

theorem cc_unit (p:ℕ)[hp:Fact p.Prime](m:ℤ)(h: ((m:ℤ):ZMod p) ≠ 0) :
    IsUnit ((m:ℤ):ZMod (p^3)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  have hnd : ¬ (p:ℤ) ∣ m := by
    intro hd; exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).mpr hd)
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.1
  have hco : IsCoprime (p:ℤ) m := (hpp.coprime_iff_not_dvd).mpr hnd
  have hcm : IsCoprime m ((p:ℤ)^3) := (hco.symm).pow_right
  rw [Nat.cast_pow]; exact hcm.symm

theorem rec_step (p n : ℕ) [NeZero (p^3)]
    (h1 : ((aN (n+1):ℕ):ZMod (p^3)) = 0) (h2 : ((aN (n+2):ℕ):ZMod (p^3)) = 0)
    (hu : IsUnit ((cc0 (n:ℤ)):ZMod (p^3))) :
    ((aN n:ℕ):ZMod (p^3)) = 0 := by
  have key : ((cc0 (n:ℤ)):ZMod (p^3)) * ((aN n:ℕ):ZMod (p^3))
       + ((cc1 (n:ℤ)):ZMod (p^3)) * ((aN (n+1):ℕ):ZMod (p^3))
       + ((cc2 (n:ℤ)):ZMod (p^3)) * ((aN (n+2):ℕ):ZMod (p^3)) = 0 := by
    have h := congrArg (fun z:ℤ => (z:ZMod (p^3))) (REC_int n)
    push_cast at h
    linear_combination h
  rw [h1, h2, mul_zero, mul_zero, add_zero, add_zero] at key
  exact hu.mul_right_eq_zero.mp key

def Q0poly (n:ℤ) : ℤ := 5616*n^4+36504*n^3+88731*n^2+95597*n+38524

theorem cc0_fac (n:ℤ) : cc0 n = -27*(n+2)*(3*n+1)^3*(3*n+2)^3*Q0poly n := by
  unfold cc0 Q0poly; ring

-- p does not divide small/range naturals
theorem ndvd_np2 (p n:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hn:n ≤ p-3) : ¬ p ∣ (n+2) := by
  intro hd; have := Nat.le_of_dvd (by omega) hd; omega

theorem ndvd_3n1 (p n:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hL:(2*p+3)/3 ≤ n)(hn:n ≤ p-1) : ¬ p ∣ (3*n+1) := by
  intro hd; obtain ⟨k,hk⟩ := hd
  have hlo : 2*p < 3*n+1 := by omega
  have hhi : 3*n+1 < 3*p := by omega
  rw [hk] at hlo hhi
  have hk1 : 2 < k := by nlinarith [hp.1.pos]
  have hk2 : k < 3 := by nlinarith [hp.1.pos]
  omega

theorem ndvd_3n2 (p n:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hL:(2*p+3)/3 ≤ n)(hn:n ≤ p-1) : ¬ p ∣ (3*n+2) := by
  intro hd; obtain ⟨k,hk⟩ := hd
  have hlo : 2*p < 3*n+2 := by omega
  have hhi : 3*n+2 < 3*p := by omega
  rw [hk] at hlo hhi
  have hk1 : 2 < k := by nlinarith [hp.1.pos]
  have hk2 : k < 3 := by nlinarith [hp.1.pos]
  omega

theorem natcast_ne (p a:ℕ)[hp:Fact p.Prime](h: ¬ p ∣ a) : ((a:ℤ):ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.pos.ne'⟩
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  exact h

theorem ndvd_27 (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) : ¬ p ∣ 27 := by
  intro h
  rw [show (27:ℕ)=3^3 from by norm_num] at h
  have h3 := hp.1.dvd_of_dvd_pow h
  have := Nat.le_of_dvd (by norm_num) h3; omega

theorem cc0_ne (p n:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hL:(2*p+3)/3 ≤ n)(hn:n ≤ p-3)
    (hQ0 : ((Q0poly (n:ℤ)):ZMod p) ≠ 0) : ((cc0 (n:ℤ)):ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.pos.ne'⟩
  rw [cc0_fac]
  have f1 : (-27:ZMod p) ≠ 0 := by
    rw [show (-27:ZMod p) = -((27:ℕ):ZMod p) by push_cast; ring, neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_27 p hp5
  have f2 : ((n:ZMod p)+2) ≠ 0 := by
    rw [show ((n:ZMod p)+2) = ((n+2:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_np2 p n hp5 hn
  have f3 : (3*(n:ZMod p)+1) ≠ 0 := by
    rw [show (3*(n:ZMod p)+1) = ((3*n+1:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_3n1 p n hp5 hL (by omega)
  have f4 : (3*(n:ZMod p)+2) ≠ 0 := by
    rw [show (3*(n:ZMod p)+2) = ((3*n+2:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_3n2 p n hp5 hL (by omega)
  push_cast
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero f1 f2) (pow_ne_zero 3 f3)) (pow_ne_zero 3 f4)) hQ0

theorem ndvd_19600 (p:ℕ)[hp:Fact p.Prime](hp11:11≤p) : ¬ p ∣ 19600 := by
  intro h
  rw [show (19600:ℕ)=2^4*5^2*7^2 from by norm_num] at h
  rcases (hp.1.dvd_mul.mp h) with h1|h1
  · rcases (hp.1.dvd_mul.mp h1) with h2|h2
    · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h1); omega

set_option maxHeartbeats 1000000 in
theorem main_ind (p:ℕ)[hp:Fact p.Prime](hp5:5≤p)
    (base1 : (aN (p-1):ZMod (p^3))=0)
    (base2 : (aN (p-2):ZMod (p^3))=0)
    (order3 : ∀ n, (2*p+3)/3 ≤ n → n ≤ p-4 → ((Q0poly (n:ℤ)):ZMod p)=0 →
        (aN (n+1):ZMod (p^3))=0 → (aN (n+2):ZMod (p^3))=0 → (aN (n+3):ZMod (p^3))=0 →
        (aN n:ZMod (p^3))=0) :
    ∀ n, (2*p+3)/3 ≤ n → n ≤ p-1 → (aN n:ZMod (p^3))=0 := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  have Q : ∀ k, ∀ n, p-1-n = k → (2*p+3)/3 ≤ n → n ≤ p-1 → (aN n:ZMod (p^3))=0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IH =>
      intro n hk hL hn
      by_cases hn1 : n = p-1
      · subst hn1; exact base1
      by_cases hn2 : n = p-2
      · subst hn2; exact base2
      have hle3 : n ≤ p-3 := by omega
      have ha1 : (aN (n+1):ZMod (p^3))=0 := IH (p-1-(n+1)) (by omega) (n+1) rfl (by omega) (by omega)
      have ha2 : (aN (n+2):ZMod (p^3))=0 := IH (p-1-(n+2)) (by omega) (n+2) rfl (by omega) (by omega)
      by_cases hQ : ((Q0poly (n:ℤ)):ZMod p)=0
      · have hle4 : n ≤ p-4 := by
          by_contra hcon
          have hn3 : n = p-3 := by omega
          have hpne10 : p ≠ 10 := by rintro rfl; exact absurd hp.1 (by decide)
          have hp11 : 11 ≤ p := by omega
          have hc : ((p-3:ℕ):ZMod p) = -3 := by
            rw [Nat.cast_sub (by omega)]; push_cast; rw [ZMod.natCast_self]; ring
          have hval : ((Q0poly ((p-3:ℕ):ℤ)):ZMod p) = 19600 := by
            unfold Q0poly; push_cast; rw [hc]; ring
          have h19600 : (19600:ZMod p) ≠ 0 := by
            have : ((19600:ℕ):ZMod p) ≠ 0 := by
              rw [Ne, ZMod.natCast_eq_zero_iff]; exact ndvd_19600 p hp11
            simpa using this
          rw [hn3, hval] at hQ; exact h19600 hQ
        have ha3 : (aN (n+3):ZMod (p^3))=0 := IH (p-1-(n+3)) (by omega) (n+3) rfl (by omega) (by omega)
        exact order3 n hL hle4 hQ ha1 ha2 ha3
      · have hu : IsUnit ((cc0 (n:ℤ)):ZMod (p^3)) := cc_unit p _ (cc0_ne p n hp5 hL hle3 hQ)
        exact rec_step p n ha1 ha2 hu
  intro n hL hn
  exact Q (p-1-n) n rfl hL hn
theorem bezout_B1 (n:ℤ) :
    (-20909003129037504*n^3 - 93641762646688880*n^2 - 137903183681013012*n - 66738515861324233) * (30344107201349939244*n^3 + 132355633063333406103*n^2 + 189743430825201948957*n + 89407875686059905276) + (112974542809984924870590335220336*n^2 + 264401232087924145585161499507968*n + 154890138874844652761100861071913) * (Q0poly n) = 38780413101174352847728031023104 := by
  unfold Q0poly; ring
set_option maxHeartbeats 4000000 in
theorem rec3_R1 (n:ℕ) :
    ((1132754853132022841344*(n:ℤ)^7 + 21522342209508433985536*(n:ℤ)^6 + 174869030452256026132480*(n:ℤ)^5 + 787547811640038880444416*(n:ℤ)^4 + 2123105606895499233067008*(n:ℤ)^3 + 3425809086586485876326400*(n:ℤ)^2 + 3063336383231528661024768*(n:ℤ) + 1170927806717843001704448)*(aN (n+3):ℤ) + (124289463096729351143424*(n:ℤ)^10 + 1536444377801248440545280*(n:ℤ)^9 + 8330208334507208194947072*(n:ℤ)^8 + 25916756058356813636141568*(n:ℤ)^7 + 49676624715617974316448960*(n:ℤ)^6 + 51999520361094492877211760*(n:ℤ)^5 - 8775099685670584133442672*(n:ℤ)^4 - 138772308052487029495071744*(n:ℤ)^3 - 248075119390461968115695232*(n:ℤ)^2 - 214073749814132433418316544*(n:ℤ) - 76745186405461745368127232)*(aN (n+2):ℤ) + (-14157346655861827653680640*(n:ℤ)^10 - 153774597425130713700339840*(n:ℤ)^9 - 739259950115360081540030112*(n:ℤ)^8 - 2069199556237879013123017416*(n:ℤ)^7 - 3730068475192870679509169436*(n:ℤ)^6 - 4519685329367613970379014764*(n:ℤ)^5 - 3724192948678484645299878900*(n:ℤ)^4 - 2059939983200697976859464140*(n:ℤ)^3 - 733406450024011104009248256*(n:ℤ)^2 - 153094371823610765811087120*(n:ℤ) - 14614962440299705397267136)*(aN (n+1):ℤ) + (-597263062044170854139652*(n:ℤ)^10 - 5591471235806445703023609*(n:ℤ)^9 - 22534042509954058712964012*(n:ℤ)^8 - 51390131842212002357979006*(n:ℤ)^7 - 73358429286819366694562328*(n:ℤ)^6 - 68455754900250086668349601*(n:ℤ)^5 - 42298254810009547772731776*(n:ℤ)^4 - 17099492178033865511805888*(n:ℤ)^3 - 4333306289120789624146224*(n:ℤ)^2 - 622707994265777549058672*(n:ℤ) - 38624202296377879079232)*(aN n:ℤ)) = 0 := by
  have hQ : (0:ℤ) < Q0poly (n:ℤ) := by unfold Q0poly; positivity
  have h1 := REC_int n
  have h2 := REC_int (n+1)
  simp only [cc0, cc1, cc2] at h1 h2
  simp only [show n+1+1 = n+2 from rfl, show n+1+2 = n+3 from rfl] at h2
  push_cast at h1 h2
  have hmul : Q0poly (n:ℤ) * ((1132754853132022841344*(n:ℤ)^7 + 21522342209508433985536*(n:ℤ)^6 + 174869030452256026132480*(n:ℤ)^5 + 787547811640038880444416*(n:ℤ)^4 + 2123105606895499233067008*(n:ℤ)^3 + 3425809086586485876326400*(n:ℤ)^2 + 3063336383231528661024768*(n:ℤ) + 1170927806717843001704448)*(aN (n+3):ℤ) + (124289463096729351143424*(n:ℤ)^10 + 1536444377801248440545280*(n:ℤ)^9 + 8330208334507208194947072*(n:ℤ)^8 + 25916756058356813636141568*(n:ℤ)^7 + 49676624715617974316448960*(n:ℤ)^6 + 51999520361094492877211760*(n:ℤ)^5 - 8775099685670584133442672*(n:ℤ)^4 - 138772308052487029495071744*(n:ℤ)^3 - 248075119390461968115695232*(n:ℤ)^2 - 214073749814132433418316544*(n:ℤ) - 76745186405461745368127232)*(aN (n+2):ℤ) + (-14157346655861827653680640*(n:ℤ)^10 - 153774597425130713700339840*(n:ℤ)^9 - 739259950115360081540030112*(n:ℤ)^8 - 2069199556237879013123017416*(n:ℤ)^7 - 3730068475192870679509169436*(n:ℤ)^6 - 4519685329367613970379014764*(n:ℤ)^5 - 3724192948678484645299878900*(n:ℤ)^4 - 2059939983200697976859464140*(n:ℤ)^3 - 733406450024011104009248256*(n:ℤ)^2 - 153094371823610765811087120*(n:ℤ) - 14614962440299705397267136)*(aN (n+1):ℤ) + (-597263062044170854139652*(n:ℤ)^10 - 5591471235806445703023609*(n:ℤ)^9 - 22534042509954058712964012*(n:ℤ)^8 - 51390131842212002357979006*(n:ℤ)^7 - 73358429286819366694562328*(n:ℤ)^6 - 68455754900250086668349601*(n:ℤ)^5 - 42298254810009547772731776*(n:ℤ)^4 - 17099492178033865511805888*(n:ℤ)^3 - 4333306289120789624146224*(n:ℤ)^2 - 622707994265777549058672*(n:ℤ) - 38624202296377879079232)*(aN n:ℤ)) = 0 := by
    unfold Q0poly
    linear_combination (276551477815435264:ℤ) * h2 + (30344107201349939244*(n:ℤ)^3 + 132355633063333406103*(n:ℤ)^2 + 189743430825201948957*(n:ℤ) + 89407875686059905276) * h1
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hQ)

-- ===== p=69921781 vacuity =====
theorem pow_fact699 : (27240069 : ZMod 69921781)^(34960890:ℕ) = 69921780 := by
  have h0 : (27240069 : ZMod 69921781)^(1:ℕ) = 27240069 := by decide
  have h1 : (27240069 : ZMod 69921781)^(2:ℕ) = 21902458 := by rw [show (2:ℕ) = 1*2 by norm_num, pow_mul, h0]; decide
  have h2 : (27240069 : ZMod 69921781)^(4:ℕ) = 59401489 := by rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, h1]; decide
  have h3 : (27240069 : ZMod 69921781)^(8:ℕ) = 13648042 := by rw [show (8:ℕ) = 4*2 by norm_num, pow_mul, h2]; decide
  have h4 : (27240069 : ZMod 69921781)^(16:ℕ) = 12955661 := by rw [show (16:ℕ) = 8*2 by norm_num, pow_mul, h3]; decide
  have h5 : (27240069 : ZMod 69921781)^(32:ℕ) = 28768334 := by rw [show (32:ℕ) = 16*2 by norm_num, pow_mul, h4]; decide
  have h6 : (27240069 : ZMod 69921781)^(33:ℕ) = 35980963 := by rw [show (33:ℕ) = 32+1 by norm_num, pow_succ, h5]; decide
  have h7 : (27240069 : ZMod 69921781)^(66:ℕ) = 24401750 := by rw [show (66:ℕ) = 33*2 by norm_num, pow_mul, h6]; decide
  have h8 : (27240069 : ZMod 69921781)^(132:ℕ) = 46523782 := by rw [show (132:ℕ) = 66*2 by norm_num, pow_mul, h7]; decide
  have h9 : (27240069 : ZMod 69921781)^(133:ℕ) = 7417382 := by rw [show (133:ℕ) = 132+1 by norm_num, pow_succ, h8]; decide
  have h10 : (27240069 : ZMod 69921781)^(266:ℕ) = 21884760 := by rw [show (266:ℕ) = 133*2 by norm_num, pow_mul, h9]; decide
  have h11 : (27240069 : ZMod 69921781)^(532:ℕ) = 56316148 := by rw [show (532:ℕ) = 266*2 by norm_num, pow_mul, h10]; decide
  have h12 : (27240069 : ZMod 69921781)^(533:ℕ) = 60671955 := by rw [show (533:ℕ) = 532+1 by norm_num, pow_succ, h11]; decide
  have h13 : (27240069 : ZMod 69921781)^(1066:ℕ) = 53083874 := by rw [show (1066:ℕ) = 533*2 by norm_num, pow_mul, h12]; decide
  have h14 : (27240069 : ZMod 69921781)^(2132:ℕ) = 50318023 := by rw [show (2132:ℕ) = 1066*2 by norm_num, pow_mul, h13]; decide
  have h15 : (27240069 : ZMod 69921781)^(2133:ℕ) = 24022394 := by rw [show (2133:ℕ) = 2132+1 by norm_num, pow_succ, h14]; decide
  have h16 : (27240069 : ZMod 69921781)^(4266:ℕ) = 47100400 := by rw [show (4266:ℕ) = 2133*2 by norm_num, pow_mul, h15]; decide
  have h17 : (27240069 : ZMod 69921781)^(4267:ℕ) = 32483746 := by rw [show (4267:ℕ) = 4266+1 by norm_num, pow_succ, h16]; decide
  have h18 : (27240069 : ZMod 69921781)^(8534:ℕ) = 31736437 := by rw [show (8534:ℕ) = 4267*2 by norm_num, pow_mul, h17]; decide
  have h19 : (27240069 : ZMod 69921781)^(8535:ℕ) = 41990179 := by rw [show (8535:ℕ) = 8534+1 by norm_num, pow_succ, h18]; decide
  have h20 : (27240069 : ZMod 69921781)^(17070:ℕ) = 23496108 := by rw [show (17070:ℕ) = 8535*2 by norm_num, pow_mul, h19]; decide
  have h21 : (27240069 : ZMod 69921781)^(34140:ℕ) = 18871069 := by rw [show (34140:ℕ) = 17070*2 by norm_num, pow_mul, h20]; decide
  have h22 : (27240069 : ZMod 69921781)^(34141:ℕ) = 20152486 := by rw [show (34141:ℕ) = 34140+1 by norm_num, pow_succ, h21]; decide
  have h23 : (27240069 : ZMod 69921781)^(68282:ℕ) = 66861194 := by rw [show (68282:ℕ) = 34141*2 by norm_num, pow_mul, h22]; decide
  have h24 : (27240069 : ZMod 69921781)^(136564:ℕ) = 51471123 := by rw [show (136564:ℕ) = 68282*2 by norm_num, pow_mul, h23]; decide
  have h25 : (27240069 : ZMod 69921781)^(136565:ℕ) = 5438350 := by rw [show (136565:ℕ) = 136564+1 by norm_num, pow_succ, h24]; decide
  have h26 : (27240069 : ZMod 69921781)^(273130:ℕ) = 65873339 := by rw [show (273130:ℕ) = 136565*2 by norm_num, pow_mul, h25]; decide
  have h27 : (27240069 : ZMod 69921781)^(273131:ℕ) = 24431111 := by rw [show (273131:ℕ) = 273130+1 by norm_num, pow_succ, h26]; decide
  have h28 : (27240069 : ZMod 69921781)^(546262:ℕ) = 12114417 := by rw [show (546262:ℕ) = 273131*2 by norm_num, pow_mul, h27]; decide
  have h29 : (27240069 : ZMod 69921781)^(546263:ℕ) = 31422529 := by rw [show (546263:ℕ) = 546262+1 by norm_num, pow_succ, h28]; decide
  have h30 : (27240069 : ZMod 69921781)^(1092526:ℕ) = 283720 := by rw [show (1092526:ℕ) = 546263*2 by norm_num, pow_mul, h29]; decide
  have h31 : (27240069 : ZMod 69921781)^(1092527:ℕ) = 28000969 := by rw [show (1092527:ℕ) = 1092526+1 by norm_num, pow_succ, h30]; decide
  have h32 : (27240069 : ZMod 69921781)^(2185054:ℕ) = 8442756 := by rw [show (2185054:ℕ) = 1092527*2 by norm_num, pow_mul, h31]; decide
  have h33 : (27240069 : ZMod 69921781)^(2185055:ℕ) = 57745663 := by rw [show (2185055:ℕ) = 2185054+1 by norm_num, pow_succ, h32]; decide
  have h34 : (27240069 : ZMod 69921781)^(4370110:ℕ) = 40267946 := by rw [show (4370110:ℕ) = 2185055*2 by norm_num, pow_mul, h33]; decide
  have h35 : (27240069 : ZMod 69921781)^(4370111:ℕ) = 52158162 := by rw [show (4370111:ℕ) = 4370110+1 by norm_num, pow_succ, h34]; decide
  have h36 : (27240069 : ZMod 69921781)^(8740222:ℕ) = 200216 := by rw [show (8740222:ℕ) = 4370111*2 by norm_num, pow_mul, h35]; decide
  have h37 : (27240069 : ZMod 69921781)^(17480444:ℕ) = 21266143 := by rw [show (17480444:ℕ) = 8740222*2 by norm_num, pow_mul, h36]; decide
  have h38 : (27240069 : ZMod 69921781)^(17480445:ℕ) = 15053141 := by rw [show (17480445:ℕ) = 17480444+1 by norm_num, pow_succ, h37]; decide
  have h39 : (27240069 : ZMod 69921781)^(34960890:ℕ) = 69921780 := by rw [show (34960890:ℕ) = 17480445*2 by norm_num, pow_mul, h38]; decide

  exact h39
theorem ne_fact699 : (27240069 : ZMod 69921781) ≠ 0 := by decide
theorem one_ne699 : (69921780 : ZMod 69921781) ≠ 1 := by decide
theorem hp699cast : (69921781 : ZMod 69921781) = 0 := by decide
theorem h5616_699 : (5616 : ZMod 69921781) ≠ 0 := by decide
theorem D_nonsquare699 : ¬ IsSquare (27240069 : ZMod 69921781) := by
  haveI : Fact (Nat.Prime 69921781) := ⟨by norm_num⟩
  rw [ZMod.euler_criterion 69921781 ne_fact699, show (69921781/2:ℕ)=34960890 by norm_num, pow_fact699]
  exact one_ne699
theorem vac_699 (n:ℕ) (hL : 46614521 ≤ n) (hn : n ≤ 69921777)
    (hQ : (Q0poly (↑n) : ZMod 69921781) = 0) : False := by
  have key : (Q0poly (↑n) : ZMod 69921781)
      = 5616*((n:ZMod 69921781)+64177925)*((n:ZMod 69921781)+64177926)
          *((n:ZMod 69921781)^2+46448608*(n:ZMod 69921781)+9012783) := by
    unfold Q0poly
    push_cast
    linear_combination (-(14040*(n:ZMod 69921781)^3+809669448225*(n:ZMod 69921781)^2+15365923715173848151*(n:ZMod 69921781)+2981569118325062996)) * hp699cast
  rw [key] at hQ
  haveI : Fact (Nat.Prime 69921781) := ⟨by norm_num⟩
  rcases mul_eq_zero.mp hQ with h | hq
  · rcases mul_eq_zero.mp h with h' | hb2
    · rcases mul_eq_zero.mp h' with h5 | hb1
      · exact h5616_699 h5
      · have hne : (↑n : ZMod 69921781) = ↑(5743856:ℕ) := by
          push_cast; linear_combination hb1 - hp699cast
        rw [ZMod.natCast_eq_natCast_iff] at hne
        unfold Nat.ModEq at hne
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)] at hne
        omega
    · have hne : (↑n : ZMod 69921781) = ↑(5743855:ℕ) := by
        push_cast; linear_combination hb2 - hp699cast
      rw [ZMod.natCast_eq_natCast_iff] at hne
      unfold Nat.ModEq at hne
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)] at hne
      omega
  · apply D_nonsquare699
    refine ⟨2*(n:ZMod 69921781)+46448608, ?_⟩
    linear_combination (-4:ZMod 69921781)*hq - (30855523:ZMod 69921781)*hp699cast

-- ===== R1 machinery =====
theorem ndvd_Gc (p:ℕ)[hp:Fact p.Prime](hp5:5≤p)(h13:p≠13)(h37:p≠37139)(h69:p≠69921781) :
    ¬ p ∣ 38780413101174352847728031023104 := by
  intro h
  rw [show (38780413101174352847728031023104:ℕ) = 2^14*3^3*13*37139^2*69921781^2 from by norm_num] at h
  rcases hp.1.dvd_mul.mp h with h1 | h69'
  · rcases hp.1.dvd_mul.mp h1 with h2 | h37'
    · rcases hp.1.dvd_mul.mp h2 with h3 | h13'
      · rcases hp.1.dvd_mul.mp h3 with h4 | h3p
        · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h4); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h3p); omega
      · exact h13 ((Nat.prime_dvd_prime_iff_eq hp.1 (by norm_num)).mp h13')
    · exact h37 ((Nat.prime_dvd_prime_iff_eq hp.1 (by norm_num)).mp (hp.1.dvd_of_dvd_pow h37'))
  · exact h69 ((Nat.prime_dvd_prime_iff_eq hp.1 (by norm_num)).mp (hp.1.dvd_of_dvd_pow h69'))

def D0R1 (n:ℤ):ℤ := -27*(30344107201349939244*n^3 + 132355633063333406103*n^2 + 189743430825201948957*n + 89407875686059905276)*(n+2)*(3*n+1)^3*(3*n+2)^3

theorem B1_ne (p n:ℕ)[hp:Fact p.Prime](hp5:5≤p)
    (hGc:¬ p ∣ 38780413101174352847728031023104)
    (hQ:((Q0poly (n:ℤ)):ZMod p)=0) :
    ((30344107201349939244*(n:ZMod p)^3 + 132355633063333406103*(n:ZMod p)^2 + 189743430825201948957*(n:ZMod p) + 89407875686059905276)) ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.pos.ne'⟩
  intro hB
  apply hGc
  have hGc0 : ((38780413101174352847728031023104:ℕ):ZMod p) = 0 := by
    have h := congrArg (fun z:ℤ => (z:ZMod p)) (bezout_B1 (n:ℤ))
    push_cast at h
    push_cast
    linear_combination -h + (-20909003129037504*(n:ZMod p)^3 - 93641762646688880*(n:ZMod p)^2 - 137903183681013012*(n:ZMod p) - 66738515861324233)*hB + (112974542809984924870590335220336*(n:ZMod p)^2 + 264401232087924145585161499507968*(n:ZMod p) + 154890138874844652761100861071913)*hQ
  rwa [ZMod.natCast_eq_zero_iff] at hGc0

theorem D0R1_ne (p n:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hL:(2*p+3)/3 ≤ n)(hn:n ≤ p-3)
    (hGc:¬ p ∣ 38780413101174352847728031023104)
    (hQ:((Q0poly (n:ℤ)):ZMod p)=0) : ((D0R1 (n:ℤ)):ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.pos.ne'⟩
  rw [D0R1]
  have f1 : (-27:ZMod p) ≠ 0 := by
    rw [show (-27:ZMod p) = -((27:ℕ):ZMod p) by push_cast; ring, neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_27 p hp5
  have fB : ((30344107201349939244*(n:ZMod p)^3 + 132355633063333406103*(n:ZMod p)^2 + 189743430825201948957*(n:ZMod p) + 89407875686059905276)) ≠ 0 := B1_ne p n hp5 hGc hQ
  have f2 : ((n:ZMod p)+2) ≠ 0 := by
    rw [show ((n:ZMod p)+2) = ((n+2:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_np2 p n hp5 hn
  have f3 : (3*(n:ZMod p)+1) ≠ 0 := by
    rw [show (3*(n:ZMod p)+1) = ((3*n+1:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_3n1 p n hp5 hL (by omega)
  have f4 : (3*(n:ZMod p)+2) ≠ 0 := by
    rw [show (3*(n:ZMod p)+2) = ((3*n+2:ℕ):ZMod p) by push_cast; ring, Ne, ZMod.natCast_eq_zero_iff]
    exact ndvd_3n2 p n hp5 hL (by omega)
  push_cast
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero f1 fB) f2) (pow_ne_zero 3 f3)) (pow_ne_zero 3 f4)

def L0poly (n:ℤ) : ℤ := (109670025484692067469373)*(n:ℤ)^9 + (899680496523766556555844)*(n:ℤ)^8 + (3095420602579239403943766)*(n:ℤ)^7 + (5849463034616741716365396)*(n:ℤ)^6 + (6690724496530301160569925)*(n:ℤ)^5 + (4814156561093123030290224)*(n:ℤ)^4 + (2185564407300967214492352)*(n:ℤ)^3 + (605694037018808521211184)*(n:ℤ)^2 + (93324177834693649359408)*(n:ℤ) + (6115230230833506846528)
def L1poly (n:ℤ) : ℤ := (2599585789266774932607360)*(n:ℤ)^9 + (25220600990392906828921248)*(n:ℤ)^8 + (106438250683815786044064432)*(n:ℤ)^7 + (255877835452374859727396652)*(n:ℤ)^6 + (384760443850427580829592940)*(n:ℤ)^5 + (372691505494048811446146564)*(n:ℤ)^4 + (228814729054961982072073380)*(n:ℤ)^3 + (82076447054168177531584608)*(n:ℤ)^2 + (13180511531184930146143440)*(n:ℤ) + (-78183088629788728846656)
def L2poly (n:ℤ) : ℤ := (-22822152333754951397376)*(n:ℤ)^9 + (-363246681161484780650496)*(n:ℤ)^8 + (-3345641548052489716925952)*(n:ℤ)^7 + (-21480335091187506538451712)*(n:ℤ)^6 + (-94439220141553376700037680)*(n:ℤ)^5 + (-277608144217363340530854960)*(n:ℤ)^4 + (-534943902878309976526160064)*(n:ℤ)^3 + (-649437403953486054529434528)*(n:ℤ)^2 + (-451506530478035088691712640)*(n:ℤ) + (-137333928784396170722482944)
def L3poly (n:ℤ) : ℤ := (944269425236310360064)*(n:ℤ)^8 + (19960133986242619736064)*(n:ℤ)^7 + (184132875749157146836992)*(n:ℤ)^6 + (968188744125496374726656)*(n:ℤ)^5 + (3173550281140966249029120)*(n:ℤ)^4 + (6639979184636537616241536)*(n:ℤ)^3 + (8659750582647270311361408)*(n:ℤ)^2 + (6436161477504946995375744)*(n:ℤ) + (2087054131754893755839616)
set_option maxHeartbeats 4000000 in
theorem rec3_alt (n:ℕ) :
    (L0poly (n:ℤ))*(aN n:ℤ) + (L1poly (n:ℤ))*(aN (n+1):ℤ) + (L2poly (n:ℤ))*(aN (n+2):ℤ) + (L3poly (n:ℤ))*(aN (n+3):ℤ) = 0 := by
  have hQ : (0:ℤ) < Q0poly (n:ℤ) := by unfold Q0poly; positivity
  have h1 := REC_int n
  have h2 := REC_int (n+1)
  simp only [cc0, cc1, cc2] at h1 h2
  simp only [show n+1+1 = n+2 from rfl, show n+1+2 = n+3 from rfl] at h2
  push_cast at h1 h2
  have hmul : Q0poly (n:ℤ) * ((L0poly (n:ℤ))*(aN n:ℤ) + (L1poly (n:ℤ))*(aN (n+1):ℤ) + (L2poly (n:ℤ))*(aN (n+2):ℤ) + (L3poly (n:ℤ))*(aN (n+3):ℤ)) = 0 := by
    unfold Q0poly L0poly L1poly L2poly L3poly
    linear_combination ((230534527645583584)*(n:ℤ) + (492923561218926488)) * h2 + ((-5571814534608142431)*(n:ℤ)^2 + (-17849431951445725713)*(n:ℤ) + (-14155625534336821404)) * h1
  exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hQ)
theorem L0_ne : ((L0poly ((24806:ℕ):ℤ)):ZMod 37139) ≠ 0 := by
  unfold L0poly; push_cast; decide

theorem Q0_13_ne : ((Q0poly ((9:ℕ):ℤ)):ZMod 13) ≠ 0 := by decide
theorem hp37cast_lem : (37139 : ZMod 37139) = 0 := by decide
theorem h5616_37 : (5616 : ZMod 37139) ≠ 0 := by decide

theorem order3_gen (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∀ n, (2*p+3)/3 ≤ n → n ≤ p-4 → ((Q0poly (n:ℤ)):ZMod p)=0 →
        (aN (n+1):ZMod (p^3))=0 → (aN (n+2):ZMod (p^3))=0 → (aN (n+3):ZMod (p^3))=0 →
        (aN n:ZMod (p^3))=0 := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  intro n hL hn4 hQ ha1 ha2 ha3
  by_cases hp13 : p = 13
  · subst hp13
    have hn9 : n = 9 := by omega
    subst hn9
    exact absurd hQ Q0_13_ne
  by_cases hp37 : p = 37139
  · subst hp37
    have hp37cast : (37139 : ZMod 37139) = 0 := hp37cast_lem
    have key : ((Q0poly (n:ℤ)):ZMod 37139)
        = 5616*((n:ZMod 37139)+27128)*((n:ZMod 37139)+27127)*((n:ZMod 37139)+26266)*((n:ZMod 37139)+12333) := by
      unfold Q0poly; push_cast
      linear_combination (-14040*(n:ZMod 37139)^3 - 476938647*(n:ZMod 37139)^2 - 6952949464673*(n:ZMod 37139) - 36047828558608876) * hp37cast
    rw [key] at hQ
    have h5616 : (5616 : ZMod 37139) ≠ 0 := h5616_37
    rcases mul_eq_zero.mp hQ with h | h4
    · rcases mul_eq_zero.mp h with h' | h3
      · rcases mul_eq_zero.mp h' with h'' | h2
        · rcases mul_eq_zero.mp h'' with h5 | h1
          · exact absurd h5 h5616
          · exfalso
            have hc : (↑n : ZMod 37139) = ↑(10011:ℕ) := by push_cast; linear_combination h1 - hp37cast
            rw [ZMod.natCast_eq_natCast_iff] at hc
            unfold Nat.ModEq at hc
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)] at hc
            omega
        · exfalso
          have hc : (↑n : ZMod 37139) = ↑(10012:ℕ) := by push_cast; linear_combination h2 - hp37cast
          rw [ZMod.natCast_eq_natCast_iff] at hc
          unfold Nat.ModEq at hc
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)] at hc
          omega
      · exfalso
        have hc : (↑n : ZMod 37139) = ↑(10873:ℕ) := by push_cast; linear_combination h3 - hp37cast
        rw [ZMod.natCast_eq_natCast_iff] at hc
        unfold Nat.ModEq at hc
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)] at hc
        omega
    · have hc : (↑n : ZMod 37139) = ↑(24806:ℕ) := by push_cast; linear_combination h4 - hp37cast
      rw [ZMod.natCast_eq_natCast_iff] at hc
      unfold Nat.ModEq at hc
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by norm_num)] at hc
      have hn : n = 24806 := hc
      subst hn
      have hu : IsUnit ((L0poly ((24806:ℕ):ℤ)):ZMod (37139^3)) := cc_unit 37139 (L0poly ((24806:ℕ):ℤ)) L0_ne
      have key : ((L0poly ((24806:ℕ):ℤ)):ZMod (37139^3)) * ((aN 24806:ℕ):ZMod (37139^3)) = 0 := by
        have h := congrArg (fun z:ℤ => (z:ZMod (37139^3))) (rec3_alt 24806)
        push_cast at h
        rw [show ((aN (24806+1):ℕ):ZMod (37139^3)) = 0 from ha1,
            show ((aN (24806+2):ℕ):ZMod (37139^3)) = 0 from ha2,
            show ((aN (24806+3):ℕ):ZMod (37139^3)) = 0 from ha3] at h
        simp only [mul_zero, zero_add, add_zero] at h
        exact h
      exact hu.mul_right_eq_zero.mp key
  by_cases hp69 : p = 69921781
  · subst hp69
    exact (vac_699 n (by omega) (by omega) hQ).elim
  · have hGc := ndvd_Gc p hp5 hp13 hp37 hp69
    have hD := D0R1_ne p n hp5 hL (by omega) hGc hQ
    have hu : IsUnit ((D0R1 (n:ℤ)):ZMod (p^3)) := cc_unit p (D0R1 (n:ℤ)) hD
    have key : ((D0R1 (n:ℤ)):ZMod (p^3)) * ((aN n:ℕ):ZMod (p^3)) = 0 := by
      have h := congrArg (fun z:ℤ => (z:ZMod (p^3))) (rec3_R1 n)
      push_cast at h
      rw [show ((aN (n+1):ℕ):ZMod (p^3)) = 0 from ha1,
          show ((aN (n+2):ℕ):ZMod (p^3)) = 0 from ha2,
          show ((aN (n+3):ℕ):ZMod (p^3)) = 0 from ha3] at h
      simp only [mul_zero, zero_add, add_zero] at h
      unfold D0R1; push_cast; linear_combination h
    exact hu.mul_right_eq_zero.mp key

-- ===== ASSEMBLY TEST (stubs) =====
def aTest (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)
theorem a_eq_aN (n : ℕ) : aTest n = aN n := by
  unfold aTest aN; apply Finset.sum_congr rfl; intro k _; unfold T; ring
-- ===== Wolstenholme mod p^2 and mod-p^4 machinery =====
theorem sum_inv_sq (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) : ∑ x : ZMod p, (x⁻¹)^2 = 0 := by
  have h2 : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hbij : ∑ x : ZMod p, (x⁻¹)^2 = ∑ x : ZMod p, ((2*x)⁻¹)^2 :=
    (Equiv.sum_comp (Equiv.mulLeft₀ (2:ZMod p) h2) (fun x => (x⁻¹)^2)).symm
  have hrw : ∑ x : ZMod p, ((2*x)⁻¹)^2 = ((2:ZMod p)⁻¹)^2 * ∑ x : ZMod p, (x⁻¹)^2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; rw [mul_inv]; ring
  rw [hrw] at hbij
  have hne : (1 - ((2:ZMod p)⁻¹)^2) ≠ 0 := by
    intro hc
    have h21 : ((2:ZMod p)⁻¹)^2 = 1 := by linear_combination -hc
    have h4 : (4:ZMod p) = 1 := by
      have hm : (2:ZMod p)*(2:ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2
      have hh : ((2:ZMod p))^2 * ((2:ZMod p)⁻¹)^2 = 1 := by rw [← mul_pow, hm]; ring
      rw [h21, mul_one] at hh; linear_combination hh
    have h3 : ((3:ℕ):ZMod p) = 0 := by
      have : (3:ZMod p) = 0 := by linear_combination h4
      rw [show ((3:ℕ):ZMod p) = (3:ZMod p) by push_cast; ring]; exact this
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3; omega
  have hz : (1 - ((2:ZMod p)⁻¹)^2) * (∑ x : ZMod p, (x⁻¹)^2) = 0 := by linear_combination hbij
  exact (mul_eq_zero.mp hz).resolve_left hne

theorem sq_harmonic_full (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-1), (((i+1:ℕ):ZMod p)⁻¹)^2 = 0 := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hfull : ∑ m ∈ Finset.range p, (((m:ZMod p))⁻¹)^2 = 0 := by
    rw [zmod_sum_range p (fun x => (x⁻¹)^2)]; exact sum_inv_sq p hp5
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  rw [Finset.sum_range_succ'] at hfull
  simp only [Nat.cast_zero, inv_zero, add_zero] at hfull
  rw [show n+1-1 = n by omega]
  simpa using hfull

open Finset in
theorem sq_harmonic_half (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ k ∈ Finset.Icc 1 ((p-1)/2), (((k:ℕ):ZMod p)⁻¹)^2 = 0 := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hodd : p % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
  have hfull : ∑ k ∈ Finset.Ico 1 p, (((k:ℕ):ZMod p)⁻¹)^2 = 0 := by
    rw [Finset.sum_Ico_eq_sum_range, show p - 1 = p - 1 from rfl, ← sq_harmonic_full p hp5]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm]
  set m := (p-1)/2 with hm
  have hm2 : p - 1 = 2*m := by omega
  have hsplit := Finset.sum_Ico_consecutive (fun k => (((k:ℕ):ZMod p)⁻¹)^2) (show 1 ≤ m+1 by omega) (show m+1 ≤ p by omega)
  rw [hfull] at hsplit
  have hIcc : Finset.Ico 1 (m+1) = Finset.Icc 1 m := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have hrev : ∑ k ∈ Finset.Ico (m+1) p, (((k:ℕ):ZMod p)⁻¹)^2
      = ∑ k ∈ Finset.Ico 1 (m+1), (((k:ℕ):ZMod p)⁻¹)^2 := by
    apply Finset.sum_nbij' (i := fun k => p - k) (j := fun k => p - k)
    · intro a ha; rw [Finset.mem_Ico] at *; omega
    · intro a ha; rw [Finset.mem_Ico] at *; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha; omega
    · intro a ha; rw [Finset.mem_Ico] at ha
      have hpk : ((p-a:ℕ):ZMod p) = -(a:ZMod p) := by
        have : ((p-a:ℕ):ZMod p) + (a:ZMod p) = 0 := by
          rw [← Nat.cast_add, show p-a+a = p by omega, ZMod.natCast_self]
        linear_combination this
      rw [hpk, inv_neg, neg_pow, neg_one_sq, one_mul]
  rw [hrev, hIcc] at hsplit
  have h2 : (2:ZMod p) * (∑ k ∈ Finset.Icc 1 m, (((k:ℕ):ZMod p)⁻¹)^2) = 0 := by
    rw [two_mul]; linear_combination hsplit
  have h2u : (2:ZMod p) ≠ 0 := by
    intro h
    have : ((2:ℕ):ZMod p) = 0 := by push_cast; exact h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this; omega
  rcases mul_eq_zero.mp h2 with h|h
  · exact absurd h h2u
  · exact h



open Finset in
theorem sq_harmonic_range (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-3), (((i+1:ℕ):ZMod p)⁻¹)^2 = -((2:ZMod p)⁻¹)^2 - 1 := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have sqfull := sq_harmonic_full p hp5
  rw [show p-1 = (p-3)+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ] at sqfull
  have hpm1 : (((p-3)+1+1:ℕ):ZMod p) = -1 := by
    have : (((p-3)+1+1:ℕ):ZMod p) + 1 = 0 := by
      rw [show (((p-3)+1+1:ℕ):ZMod p)+1 = (((p-3)+1+1+1:ℕ):ZMod p) by push_cast; ring,
          show (p-3)+1+1+1 = p by omega, ZMod.natCast_self]
    linear_combination this
  have hpm2 : (((p-3)+1:ℕ):ZMod p) = -2 := by
    have : (((p-3)+1:ℕ):ZMod p) + 2 = 0 := by
      rw [show (((p-3)+1:ℕ):ZMod p)+2 = (((p-3)+1+2:ℕ):ZMod p) by push_cast; ring,
          show (p-3)+1+2 = p by omega, ZMod.natCast_self]
    linear_combination this
  rw [hpm1, hpm2] at sqfull
  have hn1 : ((-1:ZMod p))⁻¹ = -1 := by simp
  have hinv2 : (-2:ZMod p)⁻¹ = -(2:ZMod p)⁻¹ := by rw [inv_neg]
  rw [hn1, hinv2] at sqfull
  have hsq : (-(2:ZMod p)⁻¹)^2 = ((2:ZMod p)⁻¹)^2 := by ring
  rw [hsq] at sqfull
  linear_combination sqfull

theorem wolstenholme (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-1), ((i+1:ℕ):ZMod (p^2))⁻¹ = 0 := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  set S := ∑ i ∈ Finset.range (p-1), ((i+1:ℕ):ZMod (p^2))⁻¹ with hS
  have hreidx : S = ∑ i ∈ Finset.range (p-1), ((p-1-i:ℕ):ZMod (p^2))⁻¹ := by
    rw [hS]
    apply Finset.sum_nbij' (i := fun i => p-2-i) (j := fun i => p-2-i)
    · intro a ha; rw [Finset.mem_range] at *; omega
    · intro a ha; rw [Finset.mem_range] at *; omega
    · intro a ha; rw [Finset.mem_range] at ha; omega
    · intro a ha; rw [Finset.mem_range] at ha; omega
    · intro a ha; rw [Finset.mem_range] at ha; rw [show p-1-(p-2-a) = a+1 from by omega]
  have hterm : ∀ i ∈ Finset.range (p-1),
      ((i+1:ℕ):ZMod (p^2))⁻¹ + ((p-1-i:ℕ):ZMod (p^2))⁻¹
        = -(p:ZMod (p^2)) * (((i+1:ℕ):ZMod (p^2))⁻¹)^2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    set ac := ((i+1:ℕ):ZMod (p^2)) with hac
    set bc := ((p-1-i:ℕ):ZMod (p^2)) with hbc
    have hpc2 : (p:ZMod (p^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    have hacu : IsUnit ac := by
      rw [hac, ZMod.isUnit_iff_coprime]
      exact ((hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm).pow_right 2
    have hbcu : IsUnit bc := by
      rw [hbc, ZMod.isUnit_iff_coprime]
      exact ((hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm).pow_right 2
    have hacinv : ac * ac⁻¹ = 1 := ZMod.mul_inv_of_unit ac hacu
    have hbcinv : bc * bc⁻¹ = 1 := ZMod.mul_inv_of_unit bc hbcu
    have hb : bc = (p:ZMod (p^2)) - ac := by
      rw [hbc, hac, show (p-1-i:ℕ) = p - (i+1) from by omega, Nat.cast_sub (by omega)]
    have hw : bc * (-ac⁻¹ - (p:ZMod (p^2))*(ac⁻¹)^2) = 1 := by
      rw [hb]; linear_combination (1 + (p:ZMod (p^2))*ac⁻¹) * hacinv - (ac⁻¹)^2 * hpc2
    have hinv : bc⁻¹ = -ac⁻¹ - (p:ZMod (p^2))*(ac⁻¹)^2 := by
      calc bc⁻¹ = 1 * bc⁻¹ := (one_mul _).symm
        _ = ((-ac⁻¹ - (p:ZMod (p^2))*(ac⁻¹)^2) * bc) * bc⁻¹ := by rw [mul_comm _ bc, hw]
        _ = (-ac⁻¹ - (p:ZMod (p^2))*(ac⁻¹)^2) * (bc * bc⁻¹) := by ring
        _ = (-ac⁻¹ - (p:ZMod (p^2))*(ac⁻¹)^2) * 1 := by rw [hbcinv]
        _ = -ac⁻¹ - (p:ZMod (p^2))*(ac⁻¹)^2 := mul_one _
    rw [hinv]; ring
  have h2S : 2*S = ∑ i ∈ Finset.range (p-1),
      (((i+1:ℕ):ZMod (p^2))⁻¹ + ((p-1-i:ℕ):ZMod (p^2))⁻¹) := by
    rw [Finset.sum_add_distrib, ← hreidx, ← hS, two_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h2S
  have hsum2 : (p:ZMod (p^2)) * (∑ i ∈ Finset.range (p-1), (((i+1:ℕ):ZMod (p^2))⁻¹)^2) = 0 := by
    have := reduce_p0_2 p (by omega) (∑ i ∈ Finset.range (p-1), (((i+1:ℕ):ZMod (p^2))⁻¹)^2) 0 ?_
    · rw [mul_zero] at this; exact this
    · rw [map_sum, map_zero]
      rw [← sq_harmonic_full p hp5]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [map_pow]
      congr 1
      have hcop : (i+1).Coprime p :=
        (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
      have hu : IsUnit ((i+1:ℕ):ZMod (p^2)) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 2
      have h1 : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((i+1:ℕ):ZMod (p^2)) = ((i+1:ℕ):ZMod p) := map_natCast _ _
      have h2 : ((i+1:ℕ):ZMod p) * (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) (((i+1:ℕ):ZMod (p^2))⁻¹) = 1 := by
        rw [← h1, ← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
      exact (inv_eq_of_mul_eq_one_right h2).symm
  have h2u : IsUnit ((2:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)).pow_right 2
  have hfin : ((2:ℕ):ZMod (p^2)) * S = 0 := by
    rw [show ((2:ℕ):ZMod (p^2)) = 2 from by push_cast; ring, h2S, neg_mul, hsum2, neg_zero]
  exact h2u.mul_right_eq_zero.mp hfin


open Finset in
theorem harmonic_range2 (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ i ∈ Finset.range (p-3), ((i+1:ℕ):ZMod (p^2))⁻¹
      = 1 + (2:ZMod (p^2))⁻¹ + (p:ZMod (p^2)) * (1 + ((2:ZMod (p^2))⁻¹)^2) := by
  haveI : NeZero (p^2) := ⟨by have := hp.1.pos; positivity⟩
  have wolst := wolstenholme p hp5
  have hpsq : (p:ZMod (p^2))^2 = 0 := by
    have : ((p^2:ℕ):ZMod (p^2)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  have invhelp : ∀ (a b : ZMod (p^2)), IsUnit a → a * b = 1 → a⁻¹ = b := by
    intro a b hau hab
    have h : a⁻¹ * a = 1 := by rw [mul_comm]; exact ZMod.mul_inv_of_unit a hau
    linear_combination b*h - a⁻¹*hab
  have h2u : IsUnit (2:ZMod (p^2)) := by
    rw [show (2:ZMod (p^2)) = ((2:ℕ):ZMod (p^2)) by push_cast; ring, ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by norm_num) hd; omega
  have h2inv := ZMod.mul_inv_of_unit _ h2u
  rw [show p-1 = (p-3)+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ] at wolst
  have huA : IsUnit (((p-3)+1:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
  have huB : IsUnit (((p-3)+1+1:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
  have hcastA : (((p-3)+1:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) - 2 := by
    rw [show (p-3)+1 = p-2 by omega, Nat.cast_sub (by omega)]; push_cast; ring
  have hcastB : (((p-3)+1+1:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) - 1 := by
    rw [show (p-3)+1+1 = p-1 by omega, Nat.cast_sub (by omega)]; push_cast; ring
  have hA : (((p-3)+1:ℕ):ZMod (p^2))⁻¹ = -(2:ZMod (p^2))⁻¹ - (p:ZMod (p^2))*((2:ZMod (p^2))⁻¹)^2 := by
    apply invhelp _ _ huA
    rw [hcastA]
    linear_combination (1 + (p:ZMod (p^2))*(2:ZMod (p^2))⁻¹) * h2inv - ((2:ZMod (p^2))⁻¹)^2 * hpsq
  have hB : (((p-3)+1+1:ℕ):ZMod (p^2))⁻¹ = -1 - (p:ZMod (p^2)) := by
    apply invhelp _ _ huB
    rw [hcastB]
    linear_combination -hpsq
  rw [hA, hB] at wolst
  linear_combination wolst

lemma castHom_inv_p2 (p a:ℕ)[hp:Fact p.Prime](hcop:a.Coprime p) :
    (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))⁻¹) = ((a:ZMod (p^2)))⁻¹ := by
  have hu3 : IsUnit ((a:ZMod (p^3))) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 3
  have hu2 : IsUnit ((a:ZMod (p^2))) := by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 2
  have h1 : (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))) = (a:ZMod (p^2)) := map_natCast _ a
  have hri : (a:ZMod (p^2)) * (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))⁻¹) = 1 := by
    rw [← h1, ← map_mul, ZMod.mul_inv_of_unit _ hu3, map_one]
  have hli : ((a:ZMod (p^2)))⁻¹ * (a:ZMod (p^2)) = 1 := by
    rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hu2
  calc (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))⁻¹)
      = 1 * (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))⁻¹) := (one_mul _).symm
    _ = (((a:ZMod (p^2)))⁻¹ * (a:ZMod (p^2))) * (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))⁻¹) := by rw [hli]
    _ = ((a:ZMod (p^2)))⁻¹ * ((a:ZMod (p^2)) * (ZMod.castHom (show p^2 ∣ p^3 by exact ⟨p, by ring⟩) (ZMod (p^2))) ((a:ZMod (p^3))⁻¹)) := by ring
    _ = ((a:ZMod (p^2)))⁻¹ * 1 := by rw [hri]
    _ = ((a:ZMod (p^2)))⁻¹ := mul_one _

set_option maxHeartbeats 1000000 in
theorem C3p1_mod3 (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ((Nat.choose (3*p-1) (p-1) : ℕ):ZMod (p^3)) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  have hC : (Nat.choose (3*n+2) n) * n.factorial = (2*n+3).ascFactorial n := by
    have h := choose_mul_fact_asc (2*n+2) n
    rwa [show 2*n+2+n = 3*n+2 by ring, show 2*n+2+1 = 2*n+3 by ring] at h
  rw [show 3*(n+1)-1 = 3*n+2 by omega, show (n+1)-1 = n by omega]
  set P : ZMod ((n+1)^3) := ((n+1:ℕ):ZMod ((n+1)^3)) with hP
  have hP3 : P^3 = 0 := by rw [hP, ← Nat.cast_pow, ZMod.natCast_self]
  have h2cop : (2:ℕ).Coprime (n+1) := (Nat.coprime_primes Nat.prime_two hp.1).mpr (by omega)
  have h2u : IsUnit ((2:ℕ):ZMod ((n+1)^3)) := by rw [ZMod.isUnit_iff_coprime]; exact h2cop.pow_right 3
  set half : ZMod ((n+1)^3) := ((2:ℕ):ZMod ((n+1)^3))⁻¹ with hhalf0
  have hhalf : 2 * half = 1 := by
    rw [hhalf0]; rw [show (2:ZMod ((n+1)^3)) = ((2:ℕ):ZMod ((n+1)^3)) by push_cast; ring]
    exact ZMod.mul_inv_of_unit _ h2u
  have hCz : ((Nat.choose (3*n+2) n : ℕ):ZMod ((n+1)^3)) * ((n.factorial:ℕ):ZMod ((n+1)^3))
            = (((2*n+3).ascFactorial n : ℕ):ZMod ((n+1)^3)) := by rw [← Nat.cast_mul, hC]
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod] at hCz
  have hbig : ∏ i ∈ Finset.range n, ((2*n+3+i:ℕ):ZMod ((n+1)^3))
            = ((n.factorial : ℕ):ZMod ((n+1)^3))
              * ∏ i ∈ Finset.range n, (1 + (2*P) * ((i+1:ℕ):ZMod ((n+1)^3))⁻¹) := by
    rw [← Finset.prod_range_add_one_eq_factorial n, Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hcop : (i+1).Coprime (n+1) :=
      (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
    have huu : ((i+1:ℕ):ZMod ((n+1)^3)) * (((i+1:ℕ):ZMod ((n+1)^3)))⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (by rw [ZMod.isUnit_iff_coprime]; exact hcop.pow_right 3)
    rw [show ((2*n+3+i:ℕ):ZMod ((n+1)^3)) = ((i+1:ℕ):ZMod ((n+1)^3)) + 2*P from by rw [hP]; push_cast; ring]
    linear_combination -(2*P)*huu
  rw [hbig] at hCz
  rw [prod_one_add_e (2*P) (by rw [mul_pow]; rw [hP3]; ring) half hhalf
        (Finset.range n) (fun i => ((i+1:ℕ):ZMod ((n+1)^3))⁻¹)] at hCz
  set Sb : ZMod ((n+1)^3) := ∑ i ∈ Finset.range n, ((i+1:ℕ):ZMod ((n+1)^3))⁻¹ with hSb
  set S2 : ZMod ((n+1)^3) := ∑ i ∈ Finset.range n, (((i+1:ℕ):ZMod ((n+1)^3))⁻¹)^2 with hS2
  have hred1 : (2*P) * Sb = 0 := by
    have hstep : (2*P)*Sb = P*(2*Sb) := by ring
    rw [hstep]
    have h0 : P*(2*Sb) = P*(0:ZMod ((n+1)^3)) := by
      rw [hP]
      apply reduce_p1_3 (n+1) (by omega)
      rw [map_mul, map_sum, map_zero]
      have hsum0 : (∑ i ∈ Finset.range n, (ZMod.castHom (show (n+1)^2 ∣ (n+1)^3 by exact ⟨n+1, by ring⟩) (ZMod ((n+1)^2))) (((i+1:ℕ):ZMod ((n+1)^3))⁻¹)) = (0:ZMod ((n+1)^2)) := by
        rw [← wolstenholme (n+1) hp5, show (n+1)-1 = n by omega]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        exact castHom_inv_p2 (n+1) (i+1) hcop
      rw [hsum0]; ring
    rw [h0]; ring
  have hred2 : (2*P)^2 * ((Sb^2 - S2)*half) = 0 := by
    have hstep : (2*P)^2 * ((Sb^2 - S2)*half) = P^2 * (4*((Sb^2 - S2)*half)) := by ring
    rw [hstep]
    have h0 : P^2 * (4*((Sb^2 - S2)*half)) = P^2 * (0:ZMod ((n+1)^3)) := by
      rw [hP]
      apply reduce_p2' (n+1) (by omega)
      rw [map_mul, map_mul, map_sub, map_pow, map_zero]
      have hSb0 : (ZMod.castHom (show (n+1) ∣ (n+1)^3 by exact ⟨(n+1)^2, by ring⟩) (ZMod (n+1))) Sb = 0 := by
        rw [hSb, map_sum, ← harmonic_full (n+1) hp5, show (n+1)-1 = n by omega]
        apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        exact castHom_inv (n+1) (i+1) hcop
      have hS20 : (ZMod.castHom (show (n+1) ∣ (n+1)^3 by exact ⟨(n+1)^2, by ring⟩) (ZMod (n+1))) S2 = 0 := by
        rw [hS2, map_sum, ← sq_harmonic_full (n+1) hp5, show (n+1)-1 = n by omega]
        apply Finset.sum_congr rfl
        intro i hi; rw [Finset.mem_range] at hi
        have hcop : (i+1).Coprime (n+1) :=
          (hp.1.coprime_iff_not_dvd.mpr (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)).symm
        rw [map_pow]; congr 1; exact castHom_inv (n+1) (i+1) hcop
      rw [hSb0, hS20]; ring
    rw [h0]; ring
  set C := ((3*n+2).choose n : ZMod ((n+1)^3)) with hCdef
  set F := ((n.factorial:ℕ):ZMod ((n+1)^3)) with hFdef
  have hFu : IsUnit F := by
    rw [hFdef, ZMod.isUnit_iff_coprime]
    exact (Nat.Coprime.pow_right 3 ((hp.1.coprime_iff_not_dvd.mpr (fun hd => by have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega)).symm))
  have hkey : F * C = F * 1 := by
    rw [mul_one]
    linear_combination hCz + F * hred1 + F * hred2
  exact hFu.mul_right_injective hkey

set_option maxHeartbeats 1000000 in
theorem T1_mod4 (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (4 * ((Nat.choose (p-1) 1)^2 * (Nat.choose ((p-1)+1) 1) * (Nat.choose (3*(p-1)+2*1) (p-1))) : ZMod (p^4))
      = 4*(p:ZMod (p^4))*((p:ZMod (p^4))-1)^2 := by
  have hC3 := C3p1_mod3 p hp5
  obtain ⟨n, rfl⟩ : ∃ n, p = n+1 := ⟨p-1, by omega⟩
  have hn4 : 4 ≤ n := by omega
  rw [show (n+1)-1 = n by omega, Nat.choose_one_right, Nat.choose_one_right,
      show 3*n+2*1 = 3*n+2 by ring, show 3*(n+1)-1 = 3*n+2 by omega] at *
  have key : (↑(n+1):ZMod ((n+1)^4)) * (4*(↑n:ZMod ((n+1)^4))^2*(↑((3*n+2).choose n):ZMod ((n+1)^4)))
           = (↑(n+1):ZMod ((n+1)^4)) * (4*(↑n:ZMod ((n+1)^4))^2) := by
    have hmul := reduce_gen (n+1) 4 3 (by omega) (by omega)
        (4*(↑n:ZMod ((n+1)^4))^2*(↑((3*n+2).choose n):ZMod ((n+1)^4)))
        (4*(↑n:ZMod ((n+1)^4))^2) ?_
    · rw [show (4:ℕ)-3 = 1 from rfl, pow_one] at hmul; exact hmul
    · simp only [map_mul, map_pow, map_ofNat, map_natCast]
      rw [hC3, mul_one]
  rw [show (4 * ((↑n:ZMod ((n+1)^4))^2 * ↑(n+1) * ↑((3*n+2).choose n)) : ZMod ((n+1)^4))
        = (↑(n+1):ZMod ((n+1)^4)) * (4*(↑n:ZMod ((n+1)^4))^2*(↑((3*n+2).choose n))) from by push_cast; ring,
      show (4*(↑(n+1):ZMod ((n+1)^4))*((↑(n+1):ZMod ((n+1)^4))-1)^2 : ZMod ((n+1)^4))
        = (↑(n+1):ZMod ((n+1)^4)) * (4*(↑n:ZMod ((n+1)^4))^2) from by push_cast; ring]
  exact key

-- ===== base2 via recurrence (route b) =====
def Q2poly (n:ℤ) : ℤ := 5616*n^4+14040*n^3+12915*n^2+5183*n+770
def VV0 (P:ℤ) : ℤ := -27*(3*P-5)^3*(3*P-4)^3*Q0poly (P-2)
def VV2 (P:ℤ) : ℤ := 16*(4*P-3)^2*(4*P-1)^2*Q2poly (P-2)
def RR (P:ℤ) : ℤ := -2620200960*P^10 + 23581808640*P^9 - 93442076928*P^8 + 214491513024*P^7 - 315443351160*P^6 + 309842689284*P^5 - 205022409548*P^4 + 89644219236*P^3 - 24543031308*P^2 + 3751388600*P - 240840912

theorem cc0_at (P:ℤ) : cc0 (P-2) = P * VV0 P := by unfold cc0 VV0 Q0poly; ring
theorem cc2_at (P:ℤ) : cc2 (P-2) = P^3 * VV2 P := by unfold cc2 VV2 Q2poly; ring
theorem cc1_id (P:ℤ) : cc1 (P-2) - 13 * VV2 P = P * RR P := by unfold cc1 VV2 Q2poly RR; ring

theorem ndvd_big (p:ℕ)[hp:Fact p.Prime](hp7:7≤p)(h13:p≠13) : ¬ p ∣ 16848000 := by
  intro h
  rw [show (16848000:ℕ) = 2^7*3^4*5^3*13 from by norm_num] at h
  rcases (hp.1.dvd_mul.mp h) with h1|h1
  · rcases (hp.1.dvd_mul.mp h1) with h2|h2
    · rcases (hp.1.dvd_mul.mp h2) with h3|h3
      · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h3); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h3); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.1.dvd_of_dvd_pow h2); omega
  · exact h13 ((Nat.prime_dvd_prime_iff_eq hp.1 (by norm_num)).mp h1)

set_option maxHeartbeats 1000000 in
open Finset
theorem prod_e2 {R:Type*}[CommRing R](e:R)(he:e^2=0)(s:Finset ℕ)(b:ℕ→R) :
    ∏ i ∈ s, (1 + e * b i) = 1 + e * ∑ i ∈ s, b i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]; ring_nf; rw [he]; ring
noncomputable def Hs (p k:ℕ) : ZMod (p^2) := ∑ j ∈ Finset.range k, ((j+1:ℕ):ZMod (p^2))⁻¹
theorem C_pm1_mod2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk:k≤p-1) :
    ((Nat.choose (p-1) k : ℕ):ZMod (p^2)) = (-1)^k * (1 - (p:ZMod (p^2)) * Hs p k) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hp0 := hp.1.pos
  have hpsq : (p:ZMod (p^2))^2 = 0 := by
    have : ((p^2:ℕ):ZMod (p^2)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  -- factorial unit
  have hkfu : IsUnit ((k.factorial:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have : Nat.Coprime k.factorial p := by
      apply Nat.Coprime.symm
      rw [hp.1.coprime_iff_not_dvd]
      intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
    have h2 : Nat.Coprime k.factorial (p^2) := this.pow_right 2
    exact h2
  -- descFactorial = k! * C
  have hd : (p-1).descFactorial k = k.factorial * (p-1).choose k :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  -- product form
  have hterm : ∀ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod (p^2)) = (-1)*((i+1:ℕ):ZMod (p^2))*(1+(p:ZMod (p^2))*(-((i+1:ℕ):ZMod (p^2))⁻¹)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiu : IsUnit ((i+1:ℕ):ZMod (p^2)) := by
      rw [ZMod.isUnit_iff_coprime]
      have : Nat.Coprime (i+1) p := by
        rw [Nat.coprime_comm, hp.1.coprime_iff_not_dvd]
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      exact this.pow_right 2
    have hinv := ZMod.mul_inv_of_unit _ hiu
    have hsum : (p-1-i) + (i+1) = p := by omega
    have hcast : ((p-1-i:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) - ((i+1:ℕ):ZMod (p^2)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]
    linear_combination (-(p:ZMod (p^2)))*hinv
  -- product identity
  have hprod : (∏ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod (p^2)))
      = (-1)^k * ((k.factorial:ℕ):ZMod (p^2)) * (1 - (p:ZMod (p^2)) * Hs p k) := by
    rw [Finset.prod_congr rfl hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [prod_e2 (p:ZMod (p^2)) hpsq (Finset.range k) (fun i => -((i+1:ℕ):ZMod (p^2))⁻¹)]
    rw [show (∏ i ∈ Finset.range k, ((i+1:ℕ):ZMod (p^2))) = ((k.factorial:ℕ):ZMod (p^2)) from by
          rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]]
    have hsn : (∑ i ∈ Finset.range k, -((i+1:ℕ):ZMod (p^2))⁻¹) = - Hs p k := by
      unfold Hs; rw [← Finset.sum_neg_distrib]
    rw [hsn]; ring
  -- combine
  have hcast2 : (((p-1).descFactorial k : ℕ):ZMod (p^2)) = ∏ i ∈ Finset.range k, ((p-1-i:ℕ):ZMod (p^2)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hfin : ((k.factorial:ℕ):ZMod (p^2)) * ((Nat.choose (p-1) k:ℕ):ZMod (p^2))
      = ((k.factorial:ℕ):ZMod (p^2)) * ((-1)^k * (1 - (p:ZMod (p^2)) * Hs p k)) := by
    have h1 : (((p-1).descFactorial k : ℕ):ZMod (p^2)) = ((k.factorial:ℕ):ZMod (p^2)) * ((Nat.choose (p-1) k:ℕ):ZMod (p^2)) := by
      rw [hd]; push_cast; ring
    rw [← h1, hcast2, hprod]; ring
  exact hkfu.mul_left_cancel hfin
theorem C_pm2_mod2 (p j:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hj:j≤p-2) :
    ((Nat.choose (p-2) j : ℕ):ZMod (p^2)) = (-1)^j * (j+1) * (1 - (p:ZMod (p^2)) * (Hs p (j+1) - 1)) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hp0 := hp.1.pos
  have hpsq : (p:ZMod (p^2))^2 = 0 := by
    have : ((p^2:ℕ):ZMod (p^2)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  have hkfu : IsUnit ((j.factorial:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have : Nat.Coprime j.factorial p := by
      apply Nat.Coprime.symm
      rw [hp.1.coprime_iff_not_dvd]
      intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
    exact this.pow_right 2
  have hd : (p-2).descFactorial j = j.factorial * (p-2).choose j :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have hterm : ∀ i ∈ Finset.range j, ((p-2-i:ℕ):ZMod (p^2)) = (-1)*((i+2:ℕ):ZMod (p^2))*(1+(p:ZMod (p^2))*(-((i+2:ℕ):ZMod (p^2))⁻¹)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiu : IsUnit ((i+2:ℕ):ZMod (p^2)) := by
      rw [ZMod.isUnit_iff_coprime]
      have : Nat.Coprime (i+2) p := by
        rw [Nat.coprime_comm, hp.1.coprime_iff_not_dvd]
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      exact this.pow_right 2
    have hinv := ZMod.mul_inv_of_unit _ hiu
    have hcast : ((p-2-i:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) - ((i+2:ℕ):ZMod (p^2)) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast]
    linear_combination (-(p:ZMod (p^2)))*hinv
  have hprod : (∏ i ∈ Finset.range j, ((p-2-i:ℕ):ZMod (p^2)))
      = (-1)^j * ((j+1) * ((j.factorial:ℕ):ZMod (p^2))) * (1 - (p:ZMod (p^2)) * (Hs p (j+1) - 1)) := by
    rw [Finset.prod_congr rfl hterm]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [prod_e2 (p:ZMod (p^2)) hpsq (Finset.range j) (fun i => -((i+2:ℕ):ZMod (p^2))⁻¹)]
    rw [show (∏ i ∈ Finset.range j, ((i+2:ℕ):ZMod (p^2))) = ((j+1) * ((j.factorial:ℕ):ZMod (p^2))) from ?_]
    · have hHrw : Hs p (j+1) = (∑ i ∈ Finset.range j, ((i+2:ℕ):ZMod (p^2))⁻¹) + 1 := by
        unfold Hs
        rw [Finset.sum_range_succ' (fun i => ((i+1:ℕ):ZMod (p^2))⁻¹) j]
        congr 1 <;> norm_num
      have hsn : (∑ i ∈ Finset.range j, -((i+2:ℕ):ZMod (p^2))⁻¹) = - (Hs p (j+1) - 1) := by
        rw [hHrw, Finset.sum_neg_distrib]; ring
      rw [hsn]; ring
    · have hnat : (∏ i ∈ Finset.range j, (i+2)) = (j+1).factorial := by
        rw [← Finset.prod_range_add_one_eq_factorial]
        rw [Finset.prod_range_succ' (fun i => (i+1)) j]
        simp
      rw [show (∏ i ∈ Finset.range j, ((i+2:ℕ):ZMod (p^2))) = (((∏ i ∈ Finset.range j, (i+2)):ℕ):ZMod (p^2)) from by rw [Nat.cast_prod]]
      rw [hnat, Nat.factorial_succ]
      push_cast; ring
  have hcast2 : (((p-2).descFactorial j : ℕ):ZMod (p^2)) = ∏ i ∈ Finset.range j, ((p-2-i:ℕ):ZMod (p^2)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hfin : ((j.factorial:ℕ):ZMod (p^2)) * ((Nat.choose (p-2) j:ℕ):ZMod (p^2))
      = ((j.factorial:ℕ):ZMod (p^2)) * ((-1)^j * (j+1) * (1 - (p:ZMod (p^2)) * (Hs p (j+1) - 1))) := by
    have h1 : (((p-2).descFactorial j : ℕ):ZMod (p^2)) = ((j.factorial:ℕ):ZMod (p^2)) * ((Nat.choose (p-2) j:ℕ):ZMod (p^2)) := by
      rw [hd]; push_cast; ring
    rw [← h1, hcast2, hprod]; ring
  exact hkfu.mul_left_cancel hfin

open Finset
theorem window_int (p i₀ : ℕ)(h5:5≤p)(h: i₀ ≤ p-2) :
    ∏ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ℤ)-(i:ℤ))
      = (-1)^(p-2-i₀) * (i₀.factorial : ℤ) * ((p-2-i₀).factorial : ℤ) := by
  have hsplit : (Finset.range (p-1)).erase i₀ = Finset.range i₀ ∪ Finset.Ico (i₀+1) (p-1) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range i₀) (Finset.Ico (i₀+1) (p-1)) := by
    rw [Finset.disjoint_left]; intro x hx hx2
    rw [Finset.mem_range] at hx; rw [Finset.mem_Ico] at hx2; omega
  rw [hsplit, Finset.prod_union hdisj]
  have hleft : ∏ i ∈ Finset.range i₀, ((i₀:ℤ)-(i:ℤ)) = (i₀.factorial : ℤ) := by
    rw [show ∏ i ∈ Finset.range i₀, ((i₀:ℤ)-(i:ℤ)) = ∏ i ∈ Finset.range i₀, (((i₀-i:ℕ)):ℤ) from ?_]
    · rw [← Nat.cast_prod]
      congr 1
      rw [← Finset.prod_range_reflect (fun j => i₀ - j) i₀]
      rw [show (∏ j ∈ Finset.range i₀, (i₀ - (i₀ - 1 - j))) = ∏ j ∈ Finset.range i₀, (j+1) from ?_]
      · rw [Finset.prod_range_add_one_eq_factorial]
      · apply Finset.prod_congr rfl; intro j hj; rw [Finset.mem_range] at hj; omega
    · apply Finset.prod_congr rfl; intro i hi; rw [Finset.mem_range] at hi
      rw [Nat.cast_sub (by omega)]
  have hright : ∏ i ∈ Finset.Ico (i₀+1) (p-1), ((i₀:ℤ)-(i:ℤ)) = (-1)^(p-2-i₀) * ((p-2-i₀).factorial : ℤ) := by
    rw [Finset.prod_Ico_eq_prod_range]
    rw [show (p-1)-(i₀+1) = p-2-i₀ from by omega]
    rw [show ∏ l ∈ Finset.range (p-2-i₀), ((i₀:ℤ)-((i₀+1+l:ℕ):ℤ)) = ∏ l ∈ Finset.range (p-2-i₀), (-1)*((l+1:ℕ):ℤ) from ?_]
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
          show (∏ l ∈ Finset.range (p-2-i₀), ((l+1:ℕ):ℤ)) = ((p-2-i₀).factorial:ℤ) from by
            rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]]
    · apply Finset.prod_congr rfl; intro l hl; push_cast; ring
  rw [hleft, hright]; ring


theorem asc_prod2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk:1≤k)(hkp:k≤p-1) :
    (((p+1).ascFactorial (k-1) : ℕ):ZMod (p^2)) = (((k-1).factorial:ℕ):ZMod (p^2)) * (1 + (p:ZMod (p^2)) * Hs p (k-1)) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hpsq : (p:ZMod (p^2))^2 = 0 := by
    have : ((p^2:ℕ):ZMod (p^2)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
  have hterm : ∀ i ∈ Finset.range (k-1), (((p+1+i:ℕ)):ZMod (p^2)) = ((i+1:ℕ):ZMod (p^2))*(1+(p:ZMod (p^2))*((i+1:ℕ):ZMod (p^2))⁻¹) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hiu : IsUnit ((i+1:ℕ):ZMod (p^2)) := by
      rw [ZMod.isUnit_iff_coprime]
      have : Nat.Coprime (i+1) p := by
        rw [Nat.coprime_comm, hp.1.coprime_iff_not_dvd]
        intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      exact this.pow_right 2
    have hinv := ZMod.mul_inv_of_unit _ hiu
    have : ((p+1+i:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) + ((i+1:ℕ):ZMod (p^2)) := by push_cast; ring
    rw [this]; linear_combination (-(p:ZMod (p^2)))*hinv
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  rw [prod_e2 (p:ZMod (p^2)) hpsq (Finset.range (k-1)) (fun i => ((i+1:ℕ):ZMod (p^2))⁻¹)]
  rw [show (∏ i ∈ Finset.range (k-1), ((i+1:ℕ):ZMod (p^2))) = (((k-1).factorial:ℕ):ZMod (p^2)) from by
        rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod]]
  unfold Hs; ring
theorem Ak_mod2 (p k : ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk:1≤k)(hkp:k≤p-1) :
    ((Nat.choose (p-1+k) k / p : ℕ):ZMod (p^2)) * (k:ZMod (p^2)) = 1 + (p:ZMod (p^2)) * Hs p (k-1) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hp0 := hp.1.pos
  have hcf := choose_mul_fact p k hk (by omega)
  have hsplit := asc_split p (k-1)
  rw [show k-1+1 = k from by omega] at hsplit
  rw [hsplit] at hcf
  have hdvd : p ∣ Nat.choose (p-1+k) k := by
    apply hp.1.dvd_choose (a := k) (b := p-1+k) <;> omega
  obtain ⟨A, hA⟩ := hdvd
  rw [hA] at hcf
  have hAk : A * k.factorial = (p+1).ascFactorial (k-1) := by
    have : p * (A * k.factorial) = p * (p+1).ascFactorial (k-1) := by ring_nf; ring_nf at hcf; linarith [hcf]
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  have hquot : Nat.choose (p-1+k) k / p = A := by rw [hA]; exact Nat.mul_div_cancel_left A hp0
  rw [hquot]
  -- cast hAk
  have hcast : (A:ZMod (p^2)) * ((k.factorial:ℕ):ZMod (p^2)) = (((k-1).factorial:ℕ):ZMod (p^2)) * (1 + (p:ZMod (p^2)) * Hs p (k-1)) := by
    have h := congrArg (Nat.cast (R := ZMod (p^2))) hAk
    rw [Nat.cast_mul] at h
    rw [h, asc_prod2 p k hp5 hk hkp]
  have hfact : ((k.factorial:ℕ):ZMod (p^2)) = (k:ZMod (p^2)) * (((k-1).factorial:ℕ):ZMod (p^2)) := by
    have : k.factorial = k * (k-1).factorial := by
      conv_lhs => rw [show k = (k-1)+1 from by omega, Nat.factorial_succ, show (k-1)+1 = k from by omega]
    rw [this]; push_cast; ring
  have hunit : IsUnit (((k-1).factorial:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have : Nat.Coprime (k-1).factorial p := by
      apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]
      intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
    exact this.pow_right 2
  rw [hfact] at hcast
  have : (A:ZMod (p^2)) * (k:ZMod (p^2)) * (((k-1).factorial:ℕ):ZMod (p^2)) = (1 + (p:ZMod (p^2)) * Hs p (k-1)) * (((k-1).factorial:ℕ):ZMod (p^2)) := by
    rw [mul_comm (1 + (p:ZMod (p^2)) * Hs p (k-1))]; linear_combination hcast
  exact hunit.mul_left_cancel (by rw [mul_comm (((k-1).factorial:ℕ):ZMod (p^2))] ; linear_combination this)


theorem prod_erase_zero_sum (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) : ∑ x : ZMod p, x⁻¹ = 0 := by
  haveI : NeZero p := ⟨hp.1.pos.ne'⟩
  have h2 : (2:ZMod p) ≠ 0 := by
    have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    simpa using this
  have hbij : ∑ x : ZMod p, x⁻¹ = ∑ x : ZMod p, x :=
    Equiv.sum_comp ⟨fun x => x⁻¹, fun x => x⁻¹, inv_inv, inv_inv⟩ (fun x => x)
  have hsx : ∑ x : ZMod p, x = 0 := by
    have hbij2 : ∑ x : ZMod p, x = ∑ x : ZMod p, (2*x) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ (2:ZMod p) h2) (fun x => x)).symm
    rw [← Finset.mul_sum] at hbij2
    have h3 : ((2:ZMod p)-1) * ∑ x : ZMod p, x = 0 := by linear_combination -hbij2
    rcases mul_eq_zero.mp h3 with h|h
    · exact absurd (show (1:ZMod p) = 0 by linear_combination h) one_ne_zero
    · exact h
  rw [hbij, hsx]
theorem window_sum (p i₀ : ℕ)[hp:Fact p.Prime](hp5:5≤p)(hi₀:i₀<p-1) :
    ∑ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ZMod p)-(i:ZMod p))⁻¹ = -((i₀:ZMod p)+1)⁻¹ := by
  haveI : NeZero p := ⟨hp.1.pos.ne'⟩
  set a : ZMod p := (i₀:ZMod p) with ha
  have hzero : (i₀:ZMod p) = (i₀:ZMod p) := rfl
  have hane : a + 1 ≠ 0 := by
    rw [ha]
    intro hc
    have : ((i₀:ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by
      have h1 : ((p-1:ℕ):ZMod p) = -1 := by
        rw [Nat.cast_sub (by omega)]; rw [ZMod.natCast_self]; simp
      rw [h1]; linear_combination hc
    have := (ZMod.natCast_eq_natCast_iff' i₀ (p-1) p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  -- reindex sum over image
  have hinj : Set.InjOn (fun (i:ℕ) => a - (i:ZMod p)) (↑((Finset.range (p-1)).erase i₀) : Set ℕ) := by
    intro i hi j hj h
    rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_range] at hi hj
    simp only at h
    have : (i : ZMod p) = (j : ZMod p) := by linear_combination -h
    have := (ZMod.natCast_eq_natCast_iff' i j p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  rw [show (∑ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ZMod p)-(i:ZMod p))⁻¹)
        = ∑ i ∈ (Finset.range (p-1)).erase i₀, (fun x:ZMod p => x⁻¹) (a - (i:ZMod p)) from by rw [ha]]
  rw [← Finset.sum_image (g := fun (i:ℕ) => a - (i:ZMod p)) (f := fun x:ZMod p => x⁻¹) (fun x hx y hy => hinj hx hy)]
  have e1 : ((p-1:ℕ):ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
  have himg : ((Finset.range (p-1)).erase i₀).image (fun (i:ℕ) => a - (i:ZMod p))
      = ((univ : Finset (ZMod p)).erase (a+1)).erase 0 := by
    ext y
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_range, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨i, ⟨hii₀, hilt⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply hii₀
        have hc : (i : ZMod p) = a := by linear_combination -h
        rw [ha] at hc
        have := (ZMod.natCast_eq_natCast_iff' i i₀ p).mp hc
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      · intro h
        have hc : (i : ZMod p) = ((p-1:ℕ):ZMod p) := by rw [e1]; linear_combination -h
        have := (ZMod.natCast_eq_natCast_iff' i (p-1) p).mp hc
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
    · rintro ⟨hya1, hy0⟩
      have hv : ((a-y).val : ZMod p) = a - y := by rw [ZMod.natCast_val, ZMod.cast_id]
      refine ⟨(a - y).val, ⟨?_, ?_⟩, ?_⟩
      · intro h
        apply hya1
        have h2 : (a - y) = a := by rw [← hv, h, ha]
        linear_combination -h2
      · have hlt : (a-y).val < p := ZMod.val_lt _
        rcases Nat.lt_or_ge ((a-y).val) (p-1) with h | h
        · exact h
        · exfalso; apply hy0
          have hval : (a-y).val = p-1 := by omega
          rw [hval, e1] at hv
          linear_combination hv
      · rw [hv]; ring
  rw [himg]
  have hmem0 : (0:ZMod p) ∈ (univ:Finset (ZMod p)).erase (a+1) := by
    rw [Finset.mem_erase]; exact ⟨fun h => hane h.symm, Finset.mem_univ _⟩
  rw [Finset.sum_erase_eq_sub hmem0, Finset.sum_erase_eq_sub (Finset.mem_univ (a+1))]
  rw [prod_erase_zero_sum p hp5]
  rw [inv_zero]
  rw [ha]; ring

theorem window_prod2 (p M i₀ c : ℕ)[hp:Fact p.Prime](hp5:5≤p)
    (hM : p-2 ≤ M)(hi₀ : i₀ < p-1)(hci : M - i₀ = c*p) :
    (∏ i ∈ (Finset.range (p-1)).erase i₀, ((M-i:ℕ):ZMod (p^2)))
      = (((-1)^(p-2-i₀) * (i₀.factorial:ℤ) * ((p-2-i₀).factorial:ℤ) : ℤ):ZMod (p^2))
        * (1 + (c*p:ℕ) * ∑ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ℤ)-(i:ℤ) : ZMod (p^2))⁻¹) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hpsq : ((c*p:ℕ):ZMod (p^2))^2 = 0 := by
    rw [show ((c*p:ℕ):ZMod (p^2))^2 = ((c^2*(p^2):ℕ):ZMod (p^2)) from by push_cast; ring]
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  -- each term M-i = (c*p) + (i₀ - i) as ZMod p^2 (integer)
  have hnu : ∀ n:ℕ, 0 < n → n < p → IsUnit ((n:ℕ):ZMod (p^2)) := by
    intro n hn hnp
    rw [ZMod.isUnit_iff_coprime]
    have : Nat.Coprime n p := by
      rw [Nat.coprime_comm, hp.1.coprime_iff_not_dvd]
      intro hd; have := Nat.le_of_dvd hn hd; omega
    exact this.pow_right 2
  have hunit : ∀ i ∈ (Finset.range (p-1)).erase i₀, IsUnit (((i₀:ℤ)-(i:ℤ) : ZMod (p^2))) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    by_cases h : i ≤ i₀
    · rw [show ((i₀:ℤ)-(i:ℤ) : ZMod (p^2)) = ((i₀-i:ℕ):ZMod (p^2)) from by rw [Nat.cast_sub h]; push_cast; ring]
      exact hnu _ (by omega) (by omega)
    · rw [show ((i₀:ℤ)-(i:ℤ) : ZMod (p^2)) = -((i-i₀:ℕ):ZMod (p^2)) from by rw [Nat.cast_sub (by omega)]; push_cast; ring]
      exact (hnu _ (by omega) (by omega)).neg
  have hterm : ∀ i ∈ (Finset.range (p-1)).erase i₀, ((M-i:ℕ):ZMod (p^2))
      = ((i₀:ℤ)-(i:ℤ) : ZMod (p^2)) * (1 + ((c*p:ℕ):ZMod (p^2)) * ((i₀:ℤ)-(i:ℤ) : ZMod (p^2))⁻¹) := by
    intro i hi
    rw [Finset.mem_erase, Finset.mem_range] at hi
    have hinv := ZMod.mul_inv_of_unit _ (hunit i (by rw [Finset.mem_erase, Finset.mem_range]; exact hi))
    have hcast : ((M-i:ℕ):ZMod (p^2)) = ((c*p:ℕ):ZMod (p^2)) + ((i₀:ℤ)-(i:ℤ) : ZMod (p^2)) := by
      have hh : (M:ℤ) - (i₀:ℤ) = ((c*p:ℕ):ℤ) := by rw [← hci, Nat.cast_sub (by omega)]
      have hz : ((M-i:ℕ):ℤ) = ((c*p:ℕ):ℤ) + ((i₀:ℤ)-(i:ℤ)) := by
        rw [Nat.cast_sub (by omega)]; linarith [hh]
      rw [show ((M-i:ℕ):ZMod (p^2)) = (((M-i:ℕ):ℤ):ZMod (p^2)) from by push_cast; ring, hz]
      push_cast; ring
    rw [hcast]; linear_combination (-((c*p:ℕ):ZMod (p^2)))*hinv
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  rw [prod_e2 ((c*p:ℕ):ZMod (p^2)) hpsq _ (fun i => ((i₀:ℤ)-(i:ℤ) : ZMod (p^2))⁻¹)]
  congr 1
  rw [show (∏ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ℤ)-(i:ℤ) : ZMod (p^2)))
        = (((∏ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ℤ)-(i:ℤ))):ℤ):ZMod (p^2)) from by
        push_cast; rfl]
  rw [window_int p i₀ hp5 (by omega)]


set_option maxHeartbeats 1000000 in
theorem Bk_mod2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    ((Nat.choose (3*p-3+2*k) (p-1) / p : ℕ):ZMod (p^2))
      * (((p-1) * Nat.choose (p-2) ((3*p-3+2*k) % p) : ℕ):ZMod (p^2))
      = (((3*p-3+2*k)/p : ℕ):ZMod (p^2)) * ((-1:ZMod (p^2))^(p-2-((3*p-3+2*k)%p)))
        * (1 + (((3*p-3+2*k)/p * p:ℕ):ZMod (p^2))
              * ∑ i ∈ (Finset.range (p-1)).erase ((3*p-3+2*k)%p), (((((3*p-3+2*k)%p:ℕ):ℤ)-(i:ℤ)) : ZMod (p^2))⁻¹) := by
  set M := 3*p-3+2*k with hM
  set i₀ := M % p with hi₀def
  set c := M / p with hcdef
  have hp0 := hp.1.pos
  -- basic facts about i₀, c
  have hMval : ((M:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
    have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
    have h1 : M + 3 = 3*p + 2*k := by rw [hM]; omega
    have h2 : ((M:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
      rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
    have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
    linear_combination h2 + h3
  -- i₀ ≠ p-1 : else 2k ≡ 2
  have hi₀ne : i₀ ≠ p - 1 := by
    intro hcontra
    have : ((i₀:ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hcontra]
    rw [hi₀def, ZMod.natCast_mod] at this
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hMval, hp1c] at this
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hi₀lt : i₀ < p - 1 := by
    have : i₀ < p := Nat.mod_lt _ hp0
    omega
  have hci : M - i₀ = c * p := by
    have hdm : p * c + i₀ = M := by rw [hcdef, hi₀def]; exact Nat.div_add_mod M p
    rw [Nat.mul_comm]; omega
  have hMi : ((M:ℕ):ZMod p) = ((i₀:ℕ):ZMod p) := by rw [hi₀def, ZMod.natCast_mod]
  -- C * (p-1)! = descFactorial = prod
  have hCfact : (Nat.choose M (p-1)) * (p-1).factorial = ∏ i ∈ Finset.range (p-1), (M - i) := by
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have hi₀mem : i₀ ∈ Finset.range (p-1) := Finset.mem_range.mpr hi₀lt
  have hpull : ∏ i ∈ Finset.range (p-1), (M - i) = (M - i₀) * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i) := by
    rw [← Finset.mul_prod_erase _ _ hi₀mem]
  rw [hpull, hci] at hCfact
  have hdvdC : p ∣ Nat.choose M (p-1) := by
    have hpdvd : p ∣ (Nat.choose M (p-1)) * (p-1).factorial := by
      rw [hCfact]; exact ⟨c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i), by ring⟩
    rcases (Nat.Prime.dvd_mul hp.1).mp hpdvd with h | h
    · exact h
    · exfalso; have := (Nat.Prime.dvd_factorial hp.1).mp h; omega
  obtain ⟨B, hB⟩ := hdvdC
  rw [hB] at hCfact
  have hBfact : B * (p-1).factorial = c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i) := by
    have hh : p * (B * (p-1).factorial) = p * (c * ∏ i ∈ (Finset.range (p-1)).erase i₀, (M - i)) := by
      rw [← Nat.mul_assoc, hCfact]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 hh
  have hBeq : Nat.choose M (p-1) / p = B := by rw [hB]; exact Nat.mul_div_cancel_left B hp0
  rw [hBeq]
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hcast : (B:ZMod (p^2)) * (((p-1).factorial:ℕ):ZMod (p^2))
      = (c:ZMod (p^2)) * ∏ i ∈ (Finset.range (p-1)).erase i₀, ((M-i:ℕ):ZMod (p^2)) := by
    have h := congrArg (Nat.cast (R := ZMod (p^2))) hBfact
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod] at h
    exact h
  rw [window_prod2 p M i₀ c hp5 (by rw [hM]; omega) hi₀lt hci] at hcast
  have hfacid : (p-1).factorial = (p-1) * (Nat.choose (p-2) i₀ * (i₀.factorial * (p-2-i₀).factorial)) := by
    have h2 := Nat.choose_mul_factorial_mul_factorial (show i₀ ≤ p-2 from by omega)
    have h1 : (p-1).factorial = (p-1)*(p-2).factorial := by
      conv_lhs => rw [show p-1 = (p-2)+1 from by omega]
      rw [Nat.factorial_succ, show (p-2)+1 = p-1 from by omega]
    rw [h1, ← h2]; ring
  rw [hfacid] at hcast
  set F : ZMod (p^2) := ((i₀.factorial:ℕ):ZMod (p^2)) * (((p-2-i₀).factorial:ℕ):ZMod (p^2)) with hF
  have hFu : IsUnit F := by
    rw [hF]
    apply IsUnit.mul
    · rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
      apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]
      intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
    · rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
      apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]
      intro hd; have := (Nat.Prime.dvd_factorial hp.1).mp hd; omega
  have hFF := ZMod.mul_inv_of_unit F hFu
  have key : ((B:ZMod (p^2)) * (((p-1) * Nat.choose (p-2) i₀:ℕ):ZMod (p^2))) * F
      = ((c:ZMod (p^2)) * ((-1:ZMod (p^2))^(p-2-i₀)) * (1 + ((c*p:ℕ):ZMod (p^2)) * ∑ i ∈ (Finset.range (p-1)).erase i₀, (((i₀:ℤ)-(i:ℤ)):ZMod (p^2))⁻¹)) * F := by
    rw [hF]
    push_cast at hcast ⊢
    linear_combination hcast
  have hgoal : (B:ZMod (p^2)) * (((p-1) * Nat.choose (p-2) i₀:ℕ):ZMod (p^2))
      = (c:ZMod (p^2)) * ((-1:ZMod (p^2))^(p-2-i₀)) * (1 + ((c*p:ℕ):ZMod (p^2)) * ∑ i ∈ (Finset.range (p-1)).erase i₀, (((i₀:ℤ)-(i:ℤ)):ZMod (p^2))⁻¹) := by
    have h := key
    calc (B:ZMod (p^2)) * (((p-1) * Nat.choose (p-2) i₀:ℕ):ZMod (p^2))
        = ((B:ZMod (p^2)) * (((p-1) * Nat.choose (p-2) i₀:ℕ):ZMod (p^2))) * F * F⁻¹ := by rw [mul_assoc, hFF, mul_one]
      _ = ((c:ZMod (p^2)) * ((-1:ZMod (p^2))^(p-2-i₀)) * (1 + ((c*p:ℕ):ZMod (p^2)) * ∑ i ∈ (Finset.range (p-1)).erase i₀, (((i₀:ℤ)-(i:ℤ)):ZMod (p^2))⁻¹)) * F * F⁻¹ := by rw [h]
      _ = _ := by rw [mul_assoc, hFF, mul_one]
  exact hgoal

set_option maxHeartbeats 1000000 in
theorem Mk_val2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p) * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ):ZMod (p^2))
      * ((k * ((p-1) * Nat.choose (p-2) ((3*p-3+2*k)%p)) : ℕ):ZMod (p^2))
    = ((-1:ZMod (p^2))^k * (1 - (p:ZMod (p^2)) * Hs p k))^2
      * (1 + (p:ZMod (p^2)) * Hs p (k-1))
      * ((((3*p-3+2*k)/p : ℕ):ZMod (p^2)) * ((-1:ZMod (p^2))^(p-2-((3*p-3+2*k)%p)))
        * (1 + (((3*p-3+2*k)/p * p:ℕ):ZMod (p^2)) * ∑ i ∈ (Finset.range (p-1)).erase ((3*p-3+2*k)%p), (((((3*p-3+2*k)%p:ℕ):ℤ)-(i:ℤ)) : ZMod (p^2))⁻¹)) := by
  rw [show (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p) * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ):ZMod (p^2)) * ((k * ((p-1) * Nat.choose (p-2) ((3*p-3+2*k)%p)) : ℕ):ZMod (p^2))
      = ((Nat.choose (p-1) k :ℕ):ZMod (p^2))^2 * (((Nat.choose (p-1+k) k / p:ℕ):ZMod (p^2)) * ((k:ℕ):ZMod (p^2))) * (((Nat.choose (3*p-3+2*k) (p-1) / p:ℕ):ZMod (p^2)) * (((p-1) * Nat.choose (p-2) ((3*p-3+2*k)%p):ℕ):ZMod (p^2))) from by push_cast; ring]
  rw [C_pm1_mod2 p k hp5 hkp, Ak_mod2 p k hp5 (by omega) hkp, Bk_mod2 p k hp5 hk2 hkp]

set_option maxHeartbeats 4000000 in
theorem Mk_red (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p) * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ):ZMod (p^2))
    = (((3*p-3+2*k)/p : ℕ):ZMod (p^2)) * ((k:ℕ):ZMod (p^2))⁻¹ * ((((3*p-3+2*k)%p+1:ℕ)):ZMod (p^2))⁻¹
      * (1 + (p:ZMod (p^2)) * (-2*Hs p k + Hs p (k-1) + Hs p ((3*p-3+2*k)%p+1)
          + (((3*p-3+2*k)/p:ℕ):ZMod (p^2))
            * ∑ i ∈ (Finset.range (p-1)).erase ((3*p-3+2*k)%p), (((((3*p-3+2*k)%p:ℕ):ℤ)-(i:ℤ)) : ZMod (p^2))⁻¹)) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hp0 := hp.1.pos
  have hpsq : (p:ZMod (p^2))^2 = 0 := by
    have : ((p^2:ℕ):ZMod (p^2)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  set M := 3*p-3+2*k with hM
  set i₀ := M % p with hi₀def
  set c := M / p with hcdef
  set W : ZMod (p^2) := ∑ i ∈ (Finset.range (p-1)).erase i₀, (((i₀:ℕ):ℤ)-(i:ℤ) : ZMod (p^2))⁻¹ with hWdef
  have hMval : ((M:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
    have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
    have h1 : M + 3 = 3*p + 2*k := by rw [hM]; omega
    have h2 : ((M:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
      rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
    have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
    linear_combination h2 + h3
  have hi₀ne : i₀ ≠ p - 1 := by
    intro hcontra
    have : ((i₀:ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hcontra]
    rw [hi₀def, ZMod.natCast_mod] at this
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hMval, hp1c] at this
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hi₀lt : i₀ < p - 1 := by have : i₀ < p := Nat.mod_lt _ hp0; omega
  have hi₀le : i₀ ≤ p - 2 := by omega
  have hval := Mk_val2 p k hp5 hk2 hkp
  rw [← hM, ← hi₀def, ← hcdef, ← hWdef] at hval
  have hku : IsUnit ((k:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hkinv := ZMod.mul_inv_of_unit _ hku
  have hkinv' : ((k:ℕ):ZMod (p^2))⁻¹ * ((k:ℕ):ZMod (p^2)) = 1 := by rw [mul_comm]; exact hkinv
  have hi1u : IsUnit (((i₀+1:ℕ)):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  have hi1inv := ZMod.mul_inv_of_unit _ hi1u
  have hi1inv' : (((i₀+1:ℕ)):ZMod (p^2))⁻¹ * (((i₀+1:ℕ)):ZMod (p^2)) = 1 := by rw [mul_comm]; exact hi1inv
  have hcp2 := C_pm2_mod2 p i₀ hp5 hi₀le
  have hcp2' : ((Nat.choose (p-2) i₀:ℕ):ZMod (p^2)) = (-1)^i₀ * (((i₀+1:ℕ)):ZMod (p^2)) * (1 - (p:ZMod (p^2))*(Hs p (i₀+1)-1)) := by
    rw [hcp2]; push_cast; ring
  have hpm1 : ((p-1:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsq : ((-1:ZMod (p^2))^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hodd : Odd (p-2) := by
    rcases hp.1.eq_two_or_odd' with h|h
    · omega
    · rcases h with ⟨t,ht⟩; exact ⟨t-1, by omega⟩
  have hsign : (-1:ZMod (p^2))^(p-2-i₀) = -((-1:ZMod (p^2))^i₀) := by
    have e1 : (-1:ZMod (p^2))^(p-2-i₀) * (-1:ZMod (p^2))^i₀ = (-1:ZMod (p^2))^(p-2) := by
      rw [← pow_add]; congr 1; omega
    have e2 : (-1:ZMod (p^2))^(p-2) = -1 := hodd.neg_one_pow
    have e3 : ((-1:ZMod (p^2))^i₀)*((-1:ZMod (p^2))^i₀) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    calc (-1:ZMod (p^2))^(p-2-i₀) = (-1:ZMod (p^2))^(p-2-i₀) * ((-1:ZMod (p^2))^i₀ * (-1:ZMod (p^2))^i₀) := by rw [e3, mul_one]
      _ = ((-1:ZMod (p^2))^(p-2-i₀) * (-1:ZMod (p^2))^i₀) * (-1:ZMod (p^2))^i₀ := by ring
      _ = (-1:ZMod (p^2))^(p-2) * (-1:ZMod (p^2))^i₀ := by rw [e1]
      _ = -((-1:ZMod (p^2))^i₀) := by rw [e2]; ring
  have hNFcast : ((k * ((p-1) * Nat.choose (p-2) i₀) : ℕ):ZMod (p^2))
      = ((k:ℕ):ZMod (p^2)) * (((p:ZMod (p^2))-1) * ((Nat.choose (p-2) i₀:ℕ):ZMod (p^2))) := by
    rw [Nat.cast_mul, Nat.cast_mul, hpm1]
  have hNFu : IsUnit ((k * ((p-1) * Nat.choose (p-2) i₀) : ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]
    intro hd
    rcases (Nat.Prime.dvd_mul hp.1).mp hd with h|h
    · have := Nat.le_of_dvd (by omega) h; omega
    rcases (Nat.Prime.dvd_mul hp.1).mp h with h2|h2
    · have := Nat.le_of_dvd (by omega) h2; omega
    · have hcf := Nat.choose_mul_factorial_mul_factorial hi₀le
      have hpf : p ∣ (p-2).factorial := by
        rw [← hcf]; exact (h2.mul_right _).mul_right _
      exact absurd ((Nat.Prime.dvd_factorial hp.1).mp hpf) (by omega)
  set redv := (((c:ℕ):ZMod (p^2)) * ((k:ℕ):ZMod (p^2))⁻¹ * (((i₀+1:ℕ)):ZMod (p^2))⁻¹
      * (1 + (p:ZMod (p^2)) * (-2*Hs p k + Hs p (k-1) + Hs p (i₀+1)
          + ((c:ℕ):ZMod (p^2)) * W))) with hredvdef
  have hkey : redv * ((k * ((p-1) * Nat.choose (p-2) i₀) : ℕ):ZMod (p^2)) = 
      ((-1:ZMod (p^2))^k * (1 - (p:ZMod (p^2)) * Hs p k))^2
        * (1 + (p:ZMod (p^2)) * Hs p (k-1))
        * (((c : ℕ):ZMod (p^2)) * ((-1:ZMod (p^2))^(p-2-i₀))
          * (1 + (((c * p:ℕ)):ZMod (p^2)) * W)) := by
    rw [hNFcast, hcp2', hredvdef, hsign, mul_pow, hsq]
    have hstep : ((c:ℕ):ZMod (p^2)) * ((k:ℕ):ZMod (p^2))⁻¹ * (((i₀+1:ℕ)):ZMod (p^2))⁻¹
        * (1 + (p:ZMod (p^2)) * (-2*Hs p k + Hs p (k-1) + Hs p (i₀+1) + ((c:ℕ):ZMod (p^2)) * W))
        * (((k:ℕ):ZMod (p^2)) * (((p:ZMod (p^2))-1) * ((-1)^i₀ * (((i₀+1:ℕ)):ZMod (p^2)) * (1 - (p:ZMod (p^2))*(Hs p (i₀+1)-1)))))
        = ((c:ℕ):ZMod (p^2)) * (((k:ℕ):ZMod (p^2))⁻¹ * ((k:ℕ):ZMod (p^2))) * ((((i₀+1:ℕ)):ZMod (p^2))⁻¹ * (((i₀+1:ℕ)):ZMod (p^2)))
          * ((-1:ZMod (p^2))^i₀ * ((p:ZMod (p^2))-1)
            * (1 + (p:ZMod (p^2)) * (-2*Hs p k + Hs p (k-1) + Hs p (i₀+1) + ((c:ℕ):ZMod (p^2)) * W))
            * (1 - (p:ZMod (p^2))*(Hs p (i₀+1)-1))) := by ring
    rw [hstep, hkinv', hi1inv']
    push_cast
    linear_combination (-((c:ℕ):ZMod (p^2))^2*(Hs p (i₀+1))*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀)*W + ((c:ℕ):ZMod (p^2))^2*(Hs p (i₀+1))*((-1:ZMod (p^2))^i₀)*W + ((c:ℕ):ZMod (p^2))^2*(Hs p k)^2*(Hs p (k-1))*(p:ZMod (p^2))^2*((-1:ZMod (p^2))^i₀)*W + ((c:ℕ):ZMod (p^2))^2*(Hs p k)^2*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀)*W - 2*((c:ℕ):ZMod (p^2))^2*(Hs p k)*(Hs p (k-1))*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀)*W - 2*((c:ℕ):ZMod (p^2))^2*(Hs p k)*((-1:ZMod (p^2))^i₀)*W + ((c:ℕ):ZMod (p^2))^2*(Hs p (k-1))*((-1:ZMod (p^2))^i₀)*W + ((c:ℕ):ZMod (p^2))^2*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀)*W - ((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))^2*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))^2*((-1:ZMod (p^2))^i₀) + 2*((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))*(Hs p k)*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) - 2*((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))*(Hs p k)*((-1:ZMod (p^2))^i₀) - ((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))*(Hs p (k-1))*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))*(Hs p (k-1))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) - ((c:ℕ):ZMod (p^2))*(Hs p (i₀+1))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*(Hs p k)^2*(Hs p (k-1))*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*(Hs p k)^2*((-1:ZMod (p^2))^i₀) - 2*((c:ℕ):ZMod (p^2))*(Hs p k)*(Hs p (k-1))*((-1:ZMod (p^2))^i₀) - 2*((c:ℕ):ZMod (p^2))*(Hs p k)*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*(Hs p (k-1))*(p:ZMod (p^2))*((-1:ZMod (p^2))^i₀) + ((c:ℕ):ZMod (p^2))*((-1:ZMod (p^2))^i₀)) * hpsq
  have he := hval
  rw [← hkey] at he
  have hNFinv := ZMod.mul_inv_of_unit _ hNFu
  have h2 := congrArg (fun z => z * (((k * ((p-1) * Nat.choose (p-2) i₀) : ℕ):ZMod (p^2)))⁻¹) he
  simpa only [mul_assoc, hNFinv, mul_one] using h2

lemma chinv (p a b:ℕ)[hp:Fact p.Prime] (ha:a<p)(hb:b<p)(hab:a≠b) :
    (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((((a:ℤ)-(b:ℤ)):ZMod (p^2))⁻¹)
      = (((a:ZMod p))-((b:ZMod p)))⁻¹ := by
  haveI : NeZero (p^2) := ⟨by have := hp.1.pos; positivity⟩
  have hu : IsUnit ((((a:ℤ)-(b:ℤ)):ZMod (p^2))) := by
    rcases lt_or_gt_of_ne hab with h|h
    · rw [show (((a:ℤ)-(b:ℤ)):ZMod (p^2)) = -(((b-a:ℕ):ℤ):ZMod (p^2)) from by
          rw [Nat.cast_sub (le_of_lt h)]; push_cast; ring]
      rw [IsUnit.neg_iff, Int.cast_natCast, ZMod.isUnit_iff_coprime]
      refine Nat.Coprime.pow_right 2 ?_
      apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
    · rw [show (((a:ℤ)-(b:ℤ)):ZMod (p^2)) = (((a-b:ℕ):ℤ):ZMod (p^2)) from by
          rw [Nat.cast_sub (le_of_lt h)]; push_cast; ring]
      rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
      refine Nat.Coprime.pow_right 2 ?_
      apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
  have h1 : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((((a:ℤ)-(b:ℤ)):ZMod (p^2))) = ((a:ZMod p))-((b:ZMod p)) := by
    rw [map_sub, map_intCast, map_intCast]; push_cast; ring
  have h2 : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((((a:ℤ)-(b:ℤ)):ZMod (p^2)))
      * (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((((a:ℤ)-(b:ℤ)):ZMod (p^2))⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
  rw [h1] at h2
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)

set_option maxHeartbeats 2000000 in
theorem Mk_red2 (p k:ℕ)[hp:Fact p.Prime](hp5:5≤p)(hk2:2≤k)(hkp:k≤p-1) :
    (((Nat.choose (p-1) k)^2 * (Nat.choose (p-1+k) k / p) * (Nat.choose (3*p-3+2*k) (p-1) / p) : ℕ):ZMod (p^2))
    = (((3*p-3+2*k)/p : ℕ):ZMod (p^2)) * ((k:ℕ):ZMod (p^2))⁻¹ * ((((3*p-3+2*k)%p+1:ℕ)):ZMod (p^2))⁻¹
      * (1 + (p:ZMod (p^2)) * (-2*Hs p k + Hs p (k-1) + Hs p ((3*p-3+2*k)%p+1)
          - (((3*p-3+2*k)/p:ℕ):ZMod (p^2)) * ((((3*p-3+2*k)%p+1:ℕ)):ZMod (p^2))⁻¹)) := by
  haveI : NeZero (p^2) := ⟨by positivity⟩
  have hp0 := hp.1.pos
  set M := 3*p-3+2*k with hM
  set i₀ := M % p with hi₀def
  set c := M / p with hcdef
  have hMval : ((M:ℕ):ZMod p) = 2*(k:ZMod p)-3 := by
    have hpz : ((p:ℕ):ZMod p) = 0 := ZMod.natCast_self p
    have h1 : M + 3 = 3*p + 2*k := by rw [hM]; omega
    have h2 : ((M:ℕ):ZMod p) + 3 = ((3*p+2*k:ℕ):ZMod p) := by
      rw [show (3:ZMod p) = ((3:ℕ):ZMod p) by push_cast; ring, ← Nat.cast_add, h1]
    have h3 : ((3*p+2*k:ℕ):ZMod p) = 2*(k:ZMod p) := by push_cast [hpz]; ring
    linear_combination h2 + h3
  have hi₀ne : i₀ ≠ p - 1 := by
    intro hcontra
    have : ((i₀:ℕ):ZMod p) = ((p-1:ℕ):ZMod p) := by rw [hcontra]
    rw [hi₀def, ZMod.natCast_mod] at this
    have hp1c : ((p-1:ℕ):ZMod p) = -1 := by
      have : ((p-1:ℕ):ZMod p) + 1 = 0 := by
        rw [show ((p-1:ℕ):ZMod p) + 1 = (((p-1)+1:ℕ):ZMod p) by push_cast; ring, show (p-1)+1 = p by omega, ZMod.natCast_self]
      linear_combination this
    rw [hMval, hp1c] at this
    have h2u : (2:ZMod p) ≠ 0 := by
      have : ((2:ℕ):ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; have := Nat.le_of_dvd (by norm_num) h; omega
      simpa using this
    have hk1 : (k:ZMod p) = 1 := by
      have h0 : (2:ZMod p)*((k:ZMod p)-1) = 0 := by linear_combination this
      rcases mul_eq_zero.mp h0 with h|h
      · exact absurd h h2u
      · linear_combination h
    have : ((k:ℕ):ZMod p) = ((1:ℕ):ZMod p) := by push_cast; exact hk1
    have := (ZMod.natCast_eq_natCast_iff' k 1 p).mp this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hi₀lt : i₀ < p - 1 := by have : i₀ < p := Nat.mod_lt _ hp0; omega
  -- window reduction
  have hWred : (p:ZMod (p^2)) * (((c:ℕ):ZMod (p^2)) * (∑ i ∈ (Finset.range (p-1)).erase i₀, (((i₀:ℕ):ℤ)-(i:ℤ) : ZMod (p^2))⁻¹))
      = (p:ZMod (p^2)) * (-(((c:ℕ):ZMod (p^2)) * (((i₀+1:ℕ)):ZMod (p^2))⁻¹)) := by
    apply reduce_p0_2 p (by omega)
    have hsumc : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) (∑ i ∈ (Finset.range (p-1)).erase i₀, (((i₀:ℕ):ℤ)-(i:ℤ) : ZMod (p^2))⁻¹)
        = ∑ i ∈ (Finset.range (p-1)).erase i₀, ((i₀:ZMod p)-(i:ZMod p))⁻¹ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hie : i ∈ Finset.range (p-1) := Finset.mem_of_mem_erase hi
      have hine : i ≠ i₀ := Finset.ne_of_mem_erase hi
      rw [Finset.mem_range] at hie
      rw [chinv p i₀ i (by omega) (by omega) (by omega)]
    have hcinv : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((((i₀+1:ℕ)):ZMod (p^2))⁻¹)
        = (((i₀+1:ℕ)):ZMod p)⁻¹ := by
      have hu : IsUnit (((i₀+1:ℕ)):ZMod (p^2)) := by
        rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
        apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
      have h2 : (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) (((i₀+1:ℕ)):ZMod (p^2))
          * (ZMod.castHom (dvd_pow_self p (show (2:ℕ) ≠ 0 by omega)) (ZMod p)) ((((i₀+1:ℕ)):ZMod (p^2))⁻¹) = 1 := by
        rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
      rw [map_natCast] at h2
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2)
    simp only [map_mul, map_neg, map_natCast, hsumc, hcinv]
    rw [window_sum p i₀ hp5 hi₀lt]
    push_cast; ring
  rw [Mk_red p k hp5 hk2 hkp, ← hM, ← hi₀def, ← hcdef]
  linear_combination (((c:ℕ):ZMod (p^2)) * ((k:ℕ):ZMod (p^2))⁻¹ * (((i₀+1:ℕ)):ZMod (p^2))⁻¹) * hWred

open Finset in
lemma euler_sum {R:Type*}[CommRing R] (b:ℕ→R) : ∀ n,
    2 * ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range (j+1), b i) * b j
    = (∑ i ∈ Finset.range n, b i)^2 + ∑ i ∈ Finset.range n, (b i)^2 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h3 : ∑ i ∈ Finset.range (n+1), b i = (∑ i ∈ Finset.range n, b i) + b n := Finset.sum_range_succ b n
    rw [Finset.sum_range_succ (fun j => (∑ i ∈ Finset.range (j+1), b i) * b j) n,
        Finset.sum_range_succ (fun i => (b i)^2) n]
    linear_combination ih + (b n - (∑ i ∈ Finset.range n, b i) - (∑ i ∈ Finset.range (n+1), b i)) * h3

open Finset in
lemma lead_sum (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    (∑ k ∈ Finset.Icc 2 ((p+1)/2), (3:ZMod (p^2)) * (2:ZMod (p^2))⁻¹ * (((k-1:ℕ):ZMod (p^2))⁻¹ - ((k:ℕ):ZMod (p^2))⁻¹))
    + (∑ k ∈ Finset.Icc ((p+1)/2+1) (p-1), (2:ZMod (p^2)) * (((k-1:ℕ):ZMod (p^2))⁻¹ - ((k:ℕ):ZMod (p^2))⁻¹))
    = (9:ZMod (p^2)) * (2:ZMod (p^2))⁻¹ + (p:ZMod (p^2)) := by
  haveI : NeZero (p^2) := ⟨by have := hp.1.pos; positivity⟩
  have hp0 := hp.1.pos
  have hodd : p % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
  set m := (p+1)/2 with hm
  have hpsq : (p:ZMod (p^2))^2 = 0 := by
    have : ((p^2:ℕ):ZMod (p^2)) = 0 := ZMod.natCast_self _
    push_cast at this; linear_combination this
  have invhelp : ∀ (a b : ZMod (p^2)), IsUnit a → a * b = 1 → a⁻¹ = b := by
    intro a b hau hab
    have h : a⁻¹ * a = 1 := by rw [mul_comm]; exact ZMod.mul_inv_of_unit a hau
    linear_combination b*h - a⁻¹*hab
  have hmu : IsUnit ((m:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
  have hpmu : IsUnit ((p-1:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]; refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by omega) hd; omega
  have h2u : IsUnit (2:ZMod (p^2)) := by
    rw [show (2:ZMod (p^2)) = ((2:ℕ):ZMod (p^2)) by push_cast; ring, ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right 2 ?_
    apply Nat.Coprime.symm; rw [hp.1.coprime_iff_not_dvd]; intro hd; have:=Nat.le_of_dvd (by norm_num) hd; omega
  have h2inv := ZMod.mul_inv_of_unit _ h2u
  have t1 := tele 2 (by omega) (fun j => ((j:ℕ):ZMod (p^2))⁻¹) m (by omega)
  have t2 := tele (m+1) (by omega) (fun j => ((j:ℕ):ZMod (p^2))⁻¹) (p-1) (by omega)
  simp only [] at t1 t2
  rw [show (2:ℕ)-1 = 1 by rfl] at t1
  rw [show m+1-1 = m by omega] at t2
  rw [← Finset.mul_sum, ← Finset.mul_sum, t1, t2]
  have hG1 : ((1:ℕ):ZMod (p^2))⁻¹ = 1 := by norm_num
  have hGm : ((m:ℕ):ZMod (p^2))⁻¹ = 2 - 2*(p:ZMod (p^2)) := by
    apply invhelp _ _ hmu
    have h2m' : 2*((m:ℕ):ZMod (p^2)) = (p:ZMod (p^2))+1 := by
      have : ((2*m:ℕ):ZMod (p^2)) = ((p+1:ℕ):ZMod (p^2)) := by rw [show 2*m = p+1 by omega]
      push_cast at this; linear_combination this
    linear_combination (1-(p:ZMod (p^2)))*h2m' - hpsq
  have hGp : ((p-1:ℕ):ZMod (p^2))⁻¹ = -1 - (p:ZMod (p^2)) := by
    apply invhelp _ _ hpmu
    rw [Nat.cast_sub (by omega)]; push_cast; linear_combination -hpsq
  rw [hG1, hGm, hGp]
  linear_combination (3*(p:ZMod (p^2)) - 6) * h2inv


open Finset in
theorem pairlem {p:ℕ} (f:ℕ→ZMod p) : ∀ m,
    ∑ k ∈ Finset.Icc 1 m, (f (2*k-1) + f (2*k)) = ∑ j ∈ Finset.Icc 1 (2*m), f j := by
  intro m
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n+1 by omega), ih]
    rw [show 2*(n+1) = 2*n+1+1 by ring]
    rw [Finset.sum_Icc_succ_top (show 1 ≤ 2*n+1+1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ 2*n+1 by omega)]
    rw [show 2*n+1+1-1 = 2*n+1 by omega]
    ring

open Finset in
theorem odd_harmonic (p:ℕ)[hp:Fact p.Prime](hp5:5≤p) :
    ∑ k ∈ Finset.Icc 1 ((p-1)/2), ((2*k-1:ℕ):ZMod p)⁻¹
      = -(2:ZMod p)⁻¹ * ∑ k ∈ Finset.Icc 1 ((p-1)/2), ((k:ℕ):ZMod p)⁻¹ := by
  haveI : NeZero p := ⟨by have := hp.1.pos; omega⟩
  have hodd : p % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
  have hfull : ∑ j ∈ Finset.Icc 1 (p-1), ((j:ℕ):ZMod p)⁻¹ = 0 := by
    rw [show Finset.Icc 1 (p-1) = Finset.Ico 1 p by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sum_range, show p - 1 = p - 1 from rfl, ← harmonic_full p hp5]
    apply Finset.sum_congr rfl; intro i hi; rw [Nat.add_comm]
  set m := (p-1)/2 with hm
  have hm2 : 2*m = p-1 := by omega
  have hpair := pairlem (fun j => ((j:ℕ):ZMod p)⁻¹) m
  simp only [] at hpair
  rw [hm2, hfull] at hpair
  rw [Finset.sum_add_distrib] at hpair
  have heven : ∑ k ∈ Finset.Icc 1 m, ((2*k:ℕ):ZMod p)⁻¹
      = (2:ZMod p)⁻¹ * ∑ k ∈ Finset.Icc 1 m, ((k:ℕ):ZMod p)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show ((2*k:ℕ):ZMod p) = (2:ZMod p)*((k:ℕ):ZMod p) by push_cast; ring, mul_inv]
  rw [heven] at hpair
  linear_combination hpair

theorem cbin (p a:ℕ)[hp:Fact p.Prime] : (Nat.choose (a*p) p : ZMod p) = (a:ZMod p) := by
  have hp0 := hp.1.pos
  have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (a*p) p p _
  rw [Nat.mul_mod_left, Nat.mod_self, Nat.mul_div_cancel _ hp0, Nat.div_self hp0,
      Nat.choose_zero_right, Nat.choose_one_right, one_mul] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
theorem ap13 (p:ℕ)[hp:Fact p.Prime](hp7:7≤p) : (p:ℤ) ∣ ((aN p:ℤ) - 13) := by
  have hmid : ∀ k ∈ Finset.Ico 1 p, (T p k : ZMod p) = 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hcpk : (Nat.choose p k : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hp.1.dvd_choose_self (by omega) (by omega)
    unfold T; push_cast; rw [hcpk]; ring
  have key : (aN p : ZMod p) = (T p 0 : ZMod p) + (T p p : ZMod p) := by
    unfold aN
    rw [Nat.cast_sum]
    rw [show Finset.range (p+1) = insert 0 (insert p (Finset.Ico 1 p)) from by
          ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega]
    rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
        Finset.sum_insert (by simp only [Finset.mem_Ico]; omega),
        Finset.sum_eq_zero hmid, add_zero]
  have h0 : (T p 0 : ZMod p) = 3 := by
    unfold T
    rw [show 3*p+2*0 = 3*p from by ring]
    push_cast
    simp only [Nat.choose_zero_right, Nat.add_zero, Nat.cast_one, one_pow, mul_one, one_mul]
    rw [cbin p 3]; norm_num
  have hpp : (T p p : ZMod p) = 10 := by
    unfold T
    rw [show 3*p+2*p = 5*p from by ring, show p+p = 2*p from by ring]
    push_cast
    simp only [Nat.choose_self, Nat.cast_one, one_pow, one_mul]
    rw [cbin p 2, cbin p 5]; norm_num
  have hcast : (aN p : ZMod p) = 13 := by rw [key, h0, hpp]; norm_num
  have hmod : (aN p) ≡ 13 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by push_cast [hcast]; norm_num)
  have hd : (p:ℤ) ∣ ((13:ℤ) - (aN p:ℤ)) := by
    have := (Nat.modEq_iff_dvd).mp hmod
    exact_mod_cast this
  rw [show (aN p:ℤ)-13 = -((13:ℤ)-(aN p:ℤ)) from by ring]
  exact hd.neg_right
theorem base2_combine (p:ℕ)[hp:Fact p.Prime](hp7:7≤p)(h13:p≠13)
    (apm4 : ((p:ℤ))^4 ∣ ((aN (p-1):ℤ) + (p:ℤ)^3))
    (ap13 : (p:ℤ) ∣ ((aN p:ℤ) - 13)) :
    (aN (p-2):ZMod (p^3))=0 := by
  haveI : NeZero (p^3) := ⟨by positivity⟩
  set P : ℤ := (p:ℤ) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast hp.1.pos.ne'
  have hrec := REC_int (p-2)
  rw [show p-2+1 = p-1 from by omega, show p-2+2 = p from by omega] at hrec
  rw [show ((p-2:ℕ):ℤ) = P-2 from by rw [hP, Nat.cast_sub (by omega)]; norm_num] at hrec
  rw [cc0_at, cc2_at] at hrec
  obtain ⟨s, hs⟩ := apm4
  obtain ⟨t, ht⟩ := ap13
  have hB : (aN (p-1):ℤ) = P^4*s - P^3 := by rw [hP] at hs ⊢; linarith [hs]
  have hD : (aN p:ℤ) = P*t + 13 := by rw [hP] at ht ⊢; linarith [ht]
  have hcc1 := cc1_id P
  have key : P * (VV0 P * (aN (p-2):ℤ)) = P * (P^3 * (RR P - cc1 (P-2)*s - VV2 P * t)) := by
    rw [hB, hD] at hrec
    linear_combination hrec + (P^3) * hcc1
  have key2 : VV0 P * (aN (p-2):ℤ) = P^3 * (RR P - cc1 (P-2)*s - VV2 P * t) :=
    mul_left_cancel₀ hP0 key
  have hdvd : P^3 ∣ VV0 P * (aN (p-2):ℤ) := ⟨_, key2⟩
  have hc : ((VV0 P:ℤ):ZMod p) = ((-16848000:ℤ):ZMod p) := by
    unfold VV0 Q0poly
    push_cast [hP]
    rw [ZMod.natCast_self]
    ring
  have hcne : ((VV0 P:ℤ):ZMod p) ≠ 0 := by
    rw [hc, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have hdn : (p:ℤ) ∣ (16848000:ℤ) := (dvd_neg).mp hd
    have : p ∣ 16848000 := by exact_mod_cast hdn
    exact ndvd_big p hp7 h13 this
  have hnd : ¬(p:ℤ) ∣ VV0 P := fun hd => hcne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd)
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.1
  have hcopP : IsCoprime (p:ℤ) (VV0 P) := (hpp.coprime_iff_not_dvd).mpr hnd
  have hcop : IsCoprime (P^3) (VV0 P) := by rw [hP]; exact hcopP.pow_left
  have hdvdA : P^3 ∣ (aN (p-2):ℤ) := hcop.dvd_of_dvd_mul_left hdvd
  have hnatdvd : (p^3:ℕ) ∣ aN (p-2) := by
    have : ((p^3:ℕ):ℤ) ∣ (aN (p-2):ℤ) := by rw [hP] at hdvdA; push_cast; exact hdvdA
    exact_mod_cast this
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hnatdvd
theorem base2_stub (p:ℕ)[hp:Fact p.Prime](hp7:7≤p) : (aN (p-2):ZMod (p^3))=0 := sorry
theorem final_test (p : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
  ∀ n : ℕ, (2 * p + 3) / 3 ≤ n → n ≤ p - 1 → (p ^ 3 : ℕ) ∣ aTest n := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro n hL hn
  rw [a_eq_aN]
  by_cases hp5eq : p = 5
  · subst hp5eq
    have hn4 : n = 4 := by omega
    subst hn4
    rw [← a_eq_aN]; decide
  · have hp6 : p ≠ 6 := by rintro rfl; exact absurd hp (by decide)
    have hp7 : 7 ≤ p := by omega
    have base1 : (aN (p-1):ZMod (p^3))=0 := by
      rw [show aN (p-1) = ∑ k ∈ Finset.range p, T (p-1) k from by
        unfold aN; rw [Nat.sub_add_cancel (by omega)]]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (apm1 p hp5)
    have key := main_ind p hp5 base1 (base2_stub p hp7) (order3_gen p hp5) n hL hn
    exact (ZMod.natCast_eq_zero_iff _ _).mp key
