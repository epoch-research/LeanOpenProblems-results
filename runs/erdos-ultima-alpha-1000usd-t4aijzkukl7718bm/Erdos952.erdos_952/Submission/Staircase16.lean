import Submission.Staircase16Logic
import Submission.Staircase16Check0
import Submission.Staircase16Check1
import Submission.Staircase16Check2
import Submission.Staircase16Check3
import Submission.Staircase16Check4
import Submission.Staircase16Check5
import Submission.Staircase16Check6
import Submission.Staircase16Check7
import Submission.Staircase16Check8
import Submission.Staircase16Check9
import Submission.Staircase16Check10
import Submission.Staircase16Check11
import Submission.Staircase16Check12
import Submission.Staircase16Check13
import Submission.Staircase16Check14
import Submission.Staircase16Check15
import Submission.Staircase16Check16
import Submission.Staircase16Check17
import Submission.Staircase16Check18
import Submission.Staircase16Check19
import Submission.Staircase16Check20
import Submission.Staircase16Check21
import Submission.Staircase16Check22
import Submission.Staircase16Check23
import Submission.Staircase16Check24
import Submission.Staircase16Check25
import Submission.Staircase16Check26
import Submission.Staircase16Check27
import Submission.Staircase16Check28
import Submission.Staircase16Check29
import Submission.Staircase16Check30
import Submission.Staircase16Check31
import Submission.Staircase16Check32
import Submission.Staircase16Check33
import Submission.Staircase16Check34
import Submission.Staircase16Check35
import Submission.Staircase16Check36
import Submission.Staircase16Check37
import Submission.Staircase16Check38
import Submission.Staircase16Check39
import Submission.Staircase16Check40
import Submission.Staircase16Check41
import Submission.Staircase16Check42
import Submission.Staircase16Check43
import Submission.Staircase16Check44
import Submission.Staircase16Check45
import Submission.Staircase16Check46
import Submission.Staircase16Check47
import Submission.Staircase16Check48
import Submission.Staircase16Check49
import Submission.Staircase16Check50
import Submission.Staircase16Check51
import Submission.Staircase16Check52
import Submission.Staircase16Check53
import Submission.Staircase16Check54
import Submission.Staircase16Check55
import Submission.Staircase16Check56
import Submission.Staircase16Check57
import Submission.Staircase16Check58
import Submission.Staircase16Check59
import Submission.Staircase16Check60
import Submission.Staircase16Check61
import Submission.Staircase16Check62
import Submission.Staircase16Check63
import Submission.Staircase16Check64

/-! A kernel-verified finite moat around 3 for squared jumps strictly below 16.
This fixed-seed, fixed-bound result does not settle the unrestricted conjecture. -/
namespace Erdos952Investigation.Staircase16
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma all_rows_checked : ∀ r : Fin (radius+1), RowCheck r := by
  intro r
  have hr : r.val < 6439 := r.isLt
  by_cases h0 : r.val < 100
  · have he : 0+(r.val-0) = r.val := by omega
    have hh := block_checked_0 ⟨r.val-0,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h1 : r.val < 200
  · have he : 100+(r.val-100) = r.val := by omega
    have hh := block_checked_1 ⟨r.val-100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h2 : r.val < 300
  · have he : 200+(r.val-200) = r.val := by omega
    have hh := block_checked_2 ⟨r.val-200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h3 : r.val < 400
  · have he : 300+(r.val-300) = r.val := by omega
    have hh := block_checked_3 ⟨r.val-300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h4 : r.val < 500
  · have he : 400+(r.val-400) = r.val := by omega
    have hh := block_checked_4 ⟨r.val-400,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h5 : r.val < 600
  · have he : 500+(r.val-500) = r.val := by omega
    have hh := block_checked_5 ⟨r.val-500,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h6 : r.val < 700
  · have he : 600+(r.val-600) = r.val := by omega
    have hh := block_checked_6 ⟨r.val-600,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h7 : r.val < 800
  · have he : 700+(r.val-700) = r.val := by omega
    have hh := block_checked_7 ⟨r.val-700,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h8 : r.val < 900
  · have he : 800+(r.val-800) = r.val := by omega
    have hh := block_checked_8 ⟨r.val-800,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h9 : r.val < 1000
  · have he : 900+(r.val-900) = r.val := by omega
    have hh := block_checked_9 ⟨r.val-900,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h10 : r.val < 1100
  · have he : 1000+(r.val-1000) = r.val := by omega
    have hh := block_checked_10 ⟨r.val-1000,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h11 : r.val < 1200
  · have he : 1100+(r.val-1100) = r.val := by omega
    have hh := block_checked_11 ⟨r.val-1100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h12 : r.val < 1300
  · have he : 1200+(r.val-1200) = r.val := by omega
    have hh := block_checked_12 ⟨r.val-1200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h13 : r.val < 1400
  · have he : 1300+(r.val-1300) = r.val := by omega
    have hh := block_checked_13 ⟨r.val-1300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h14 : r.val < 1500
  · have he : 1400+(r.val-1400) = r.val := by omega
    have hh := block_checked_14 ⟨r.val-1400,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h15 : r.val < 1600
  · have he : 1500+(r.val-1500) = r.val := by omega
    have hh := block_checked_15 ⟨r.val-1500,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h16 : r.val < 1700
  · have he : 1600+(r.val-1600) = r.val := by omega
    have hh := block_checked_16 ⟨r.val-1600,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h17 : r.val < 1800
  · have he : 1700+(r.val-1700) = r.val := by omega
    have hh := block_checked_17 ⟨r.val-1700,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h18 : r.val < 1900
  · have he : 1800+(r.val-1800) = r.val := by omega
    have hh := block_checked_18 ⟨r.val-1800,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h19 : r.val < 2000
  · have he : 1900+(r.val-1900) = r.val := by omega
    have hh := block_checked_19 ⟨r.val-1900,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h20 : r.val < 2100
  · have he : 2000+(r.val-2000) = r.val := by omega
    have hh := block_checked_20 ⟨r.val-2000,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h21 : r.val < 2200
  · have he : 2100+(r.val-2100) = r.val := by omega
    have hh := block_checked_21 ⟨r.val-2100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h22 : r.val < 2300
  · have he : 2200+(r.val-2200) = r.val := by omega
    have hh := block_checked_22 ⟨r.val-2200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h23 : r.val < 2400
  · have he : 2300+(r.val-2300) = r.val := by omega
    have hh := block_checked_23 ⟨r.val-2300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h24 : r.val < 2500
  · have he : 2400+(r.val-2400) = r.val := by omega
    have hh := block_checked_24 ⟨r.val-2400,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h25 : r.val < 2600
  · have he : 2500+(r.val-2500) = r.val := by omega
    have hh := block_checked_25 ⟨r.val-2500,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h26 : r.val < 2700
  · have he : 2600+(r.val-2600) = r.val := by omega
    have hh := block_checked_26 ⟨r.val-2600,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h27 : r.val < 2800
  · have he : 2700+(r.val-2700) = r.val := by omega
    have hh := block_checked_27 ⟨r.val-2700,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h28 : r.val < 2900
  · have he : 2800+(r.val-2800) = r.val := by omega
    have hh := block_checked_28 ⟨r.val-2800,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h29 : r.val < 3000
  · have he : 2900+(r.val-2900) = r.val := by omega
    have hh := block_checked_29 ⟨r.val-2900,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h30 : r.val < 3100
  · have he : 3000+(r.val-3000) = r.val := by omega
    have hh := block_checked_30 ⟨r.val-3000,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h31 : r.val < 3200
  · have he : 3100+(r.val-3100) = r.val := by omega
    have hh := block_checked_31 ⟨r.val-3100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h32 : r.val < 3300
  · have he : 3200+(r.val-3200) = r.val := by omega
    have hh := block_checked_32 ⟨r.val-3200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h33 : r.val < 3400
  · have he : 3300+(r.val-3300) = r.val := by omega
    have hh := block_checked_33 ⟨r.val-3300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h34 : r.val < 3500
  · have he : 3400+(r.val-3400) = r.val := by omega
    have hh := block_checked_34 ⟨r.val-3400,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h35 : r.val < 3600
  · have he : 3500+(r.val-3500) = r.val := by omega
    have hh := block_checked_35 ⟨r.val-3500,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h36 : r.val < 3700
  · have he : 3600+(r.val-3600) = r.val := by omega
    have hh := block_checked_36 ⟨r.val-3600,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h37 : r.val < 3800
  · have he : 3700+(r.val-3700) = r.val := by omega
    have hh := block_checked_37 ⟨r.val-3700,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h38 : r.val < 3900
  · have he : 3800+(r.val-3800) = r.val := by omega
    have hh := block_checked_38 ⟨r.val-3800,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h39 : r.val < 4000
  · have he : 3900+(r.val-3900) = r.val := by omega
    have hh := block_checked_39 ⟨r.val-3900,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h40 : r.val < 4100
  · have he : 4000+(r.val-4000) = r.val := by omega
    have hh := block_checked_40 ⟨r.val-4000,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h41 : r.val < 4200
  · have he : 4100+(r.val-4100) = r.val := by omega
    have hh := block_checked_41 ⟨r.val-4100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h42 : r.val < 4300
  · have he : 4200+(r.val-4200) = r.val := by omega
    have hh := block_checked_42 ⟨r.val-4200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h43 : r.val < 4400
  · have he : 4300+(r.val-4300) = r.val := by omega
    have hh := block_checked_43 ⟨r.val-4300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h44 : r.val < 4500
  · have he : 4400+(r.val-4400) = r.val := by omega
    have hh := block_checked_44 ⟨r.val-4400,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h45 : r.val < 4600
  · have he : 4500+(r.val-4500) = r.val := by omega
    have hh := block_checked_45 ⟨r.val-4500,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h46 : r.val < 4700
  · have he : 4600+(r.val-4600) = r.val := by omega
    have hh := block_checked_46 ⟨r.val-4600,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h47 : r.val < 4800
  · have he : 4700+(r.val-4700) = r.val := by omega
    have hh := block_checked_47 ⟨r.val-4700,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h48 : r.val < 4900
  · have he : 4800+(r.val-4800) = r.val := by omega
    have hh := block_checked_48 ⟨r.val-4800,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h49 : r.val < 5000
  · have he : 4900+(r.val-4900) = r.val := by omega
    have hh := block_checked_49 ⟨r.val-4900,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h50 : r.val < 5100
  · have he : 5000+(r.val-5000) = r.val := by omega
    have hh := block_checked_50 ⟨r.val-5000,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h51 : r.val < 5200
  · have he : 5100+(r.val-5100) = r.val := by omega
    have hh := block_checked_51 ⟨r.val-5100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h52 : r.val < 5300
  · have he : 5200+(r.val-5200) = r.val := by omega
    have hh := block_checked_52 ⟨r.val-5200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h53 : r.val < 5400
  · have he : 5300+(r.val-5300) = r.val := by omega
    have hh := block_checked_53 ⟨r.val-5300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h54 : r.val < 5500
  · have he : 5400+(r.val-5400) = r.val := by omega
    have hh := block_checked_54 ⟨r.val-5400,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h55 : r.val < 5600
  · have he : 5500+(r.val-5500) = r.val := by omega
    have hh := block_checked_55 ⟨r.val-5500,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h56 : r.val < 5700
  · have he : 5600+(r.val-5600) = r.val := by omega
    have hh := block_checked_56 ⟨r.val-5600,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h57 : r.val < 5800
  · have he : 5700+(r.val-5700) = r.val := by omega
    have hh := block_checked_57 ⟨r.val-5700,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h58 : r.val < 5900
  · have he : 5800+(r.val-5800) = r.val := by omega
    have hh := block_checked_58 ⟨r.val-5800,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h59 : r.val < 6000
  · have he : 5900+(r.val-5900) = r.val := by omega
    have hh := block_checked_59 ⟨r.val-5900,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h60 : r.val < 6100
  · have he : 6000+(r.val-6000) = r.val := by omega
    have hh := block_checked_60 ⟨r.val-6000,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h61 : r.val < 6200
  · have he : 6100+(r.val-6100) = r.val := by omega
    have hh := block_checked_61 ⟨r.val-6100,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h62 : r.val < 6300
  · have he : 6200+(r.val-6200) = r.val := by omega
    have hh := block_checked_62 ⟨r.val-6200,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  by_cases h63 : r.val < 6400
  · have he : 6300+(r.val-6300) = r.val := by omega
    have hh := block_checked_63 ⟨r.val-6300,by omega⟩
    simpa only [Fin.val_mk,he] using hh
  have he : 6400+(r.val-6400) = r.val := by omega
  have hh := block_checked_64 ⟨r.val-6400,by omega⟩
  simpa only [Fin.val_mk,he] using hh

theorem certificate : ∃ S : Finset GaussianInt, MoatCertificate 16 S :=
  certificate_of_rows all_rows_checked

theorem component_finite :
    {w | (primeGraph 16).Reachable (3 : GaussianInt) w}.Finite :=
  component_finite_of_rows all_rows_checked

theorem step_bound_gt_sixteen_from_three (x : ℕ → GaussianInt) (C : ℤ)
    (hx0 : x 0 = 3) (hx : Function.Injective x)
    (hp : ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) : 16 < C :=
  step_bound_gt_sixteen_of_rows all_rows_checked x C hx0 hx hp

theorem certificate_le_sixteen (C : ℤ) (hC : C ≤ 16) :
    ∃ S : Finset GaussianInt, MoatCertificate C S := by
  obtain ⟨S,hS⟩ := certificate
  refine ⟨S,hS.1,?_⟩
  intro z hz w hw
  exact hS.2 z hz w ⟨hw.1,hw.2.1,hw.2.2.1,lt_of_lt_of_le hw.2.2.2 hC⟩

theorem finite_path_length_bound (x : ℕ → GaussianInt) (L : ℕ) (hx0 : x 0 = 3)
    (hx : Set.InjOn x (Set.Iic L)) (hp : ∀ n ≤ L, Prime (x n))
    (hs : ∀ n < L, (x (n+1)-x n).norm < 16) : L < 165817129 := by
  simpa only [radius] using finite_path_length_bound_of_rows all_rows_checked x L hx0 hx hp hs

#print axioms finite_path_length_bound

#print axioms all_rows_checked
#print axioms certificate
#print axioms step_bound_gt_sixteen_from_three

end Erdos952Investigation.Staircase16
