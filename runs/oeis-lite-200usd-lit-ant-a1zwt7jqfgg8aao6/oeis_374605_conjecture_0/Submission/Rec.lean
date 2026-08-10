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
