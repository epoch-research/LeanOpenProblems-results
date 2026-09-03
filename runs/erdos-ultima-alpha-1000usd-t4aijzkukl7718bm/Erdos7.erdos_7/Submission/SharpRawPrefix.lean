import Submission.SharpRawCheck0
import Submission.SharpRawCheck1
import Submission.SharpRawCheck2
import Submission.SharpRawCheck3
import Submission.SharpRawCheck4
import Submission.SharpRawCheck5
import Submission.SharpRawCheck6
import Submission.SharpRawCheck7
import Submission.SharpRawCheck8
import Submission.SharpRawCheck9
import Submission.SharpRawCheck10
import Submission.SharpRawCheck11
import Submission.SharpRawCheck12
import Submission.SharpRawCheck13
import Submission.SharpRawCheck14
import Submission.SharpRawCheck15
import Submission.SharpRawCheck16
import Submission.SharpRawCheck17
import Submission.SharpRawCheck18
import Submission.SharpRawCheck19
namespace Erdos7SharpRawPrefix
open Erdos7No23Sieve
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma fold_info_0 : (primeRange 0 0).foldl roundedStep (1000000,0) = (1000000,0) ∧
    ((primeRange 0 0).map Nat.log2).sum = 0 := by constructor <;> rfl

lemma fold_info_1 : (primeRange 0 1000).foldl roundedStep (1000000,0) = (160681849,779751374) ∧
    ((primeRange 0 1000).map Nat.log2).sum = 1287 := by
  rw [show 1000 = 0+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_0.1, fold_info_0.2, chunk_info_0.1, chunk_info_0.2]
  norm_num

lemma fold_info_2 : (primeRange 0 2000).foldl roundedStep (1000000,0) = (228892975,800021834) ∧
    ((primeRange 0 2000).map Nat.log2).sum = 2633 := by
  rw [show 2000 = 1000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_1.1, fold_info_1.2, chunk_info_1.1, chunk_info_1.2]
  norm_num

lemma fold_info_3 : (primeRange 0 3000).foldl roundedStep (1000000,0) = (277755577,808353307) ∧
    ((primeRange 0 3000).map Nat.log2).sum = 4024 := by
  rw [show 3000 = 2000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_2.1, fold_info_2.2, chunk_info_2.1, chunk_info_2.2]
  norm_num

lemma fold_info_4 : (primeRange 0 4000).foldl roundedStep (1000000,0) = (316155790,812974409) ∧
    ((primeRange 0 4000).map Nat.log2).sum = 5344 := by
  rw [show 4000 = 3000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_3.1, fold_info_3.2, chunk_info_3.1, chunk_info_3.2]
  norm_num

lemma fold_info_5 : (primeRange 0 5000).foldl roundedStep (1000000,0) = (349324668,816072447) ∧
    ((primeRange 0 5000).map Nat.log2).sum = 6758 := by
  rw [show 5000 = 4000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_4.1, fold_info_4.2, chunk_info_4.1, chunk_info_4.2]
  norm_num

lemma fold_info_6 : (primeRange 0 6000).foldl roundedStep (1000000,0) = (377655260,818229175) ∧
    ((primeRange 0 6000).map Nat.log2).sum = 8126 := by
  rw [show 6000 = 5000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_5.1, fold_info_5.2, chunk_info_5.1, chunk_info_5.2]
  norm_num

lemma fold_info_7 : (primeRange 0 7000).foldl roundedStep (1000000,0) = (404074231,819927831) ∧
    ((primeRange 0 7000).map Nat.log2).sum = 9530 := by
  rw [show 7000 = 6000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_6.1, fold_info_6.2, chunk_info_6.1, chunk_info_6.2]
  norm_num

lemma fold_info_8 : (primeRange 0 8000).foldl roundedStep (1000000,0) = (426295223,821164254) ∧
    ((primeRange 0 8000).map Nat.log2).sum = 10814 := by
  rw [show 8000 = 7000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_7.1, fold_info_7.2, chunk_info_7.1, chunk_info_7.2]
  norm_num

lemma fold_info_9 : (primeRange 0 9000).foldl roundedStep (1000000,0) = (447512157,822206007) ∧
    ((primeRange 0 9000).map Nat.log2).sum = 12223 := by
  rw [show 9000 = 8000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_8.1, fold_info_8.2, chunk_info_8.1, chunk_info_8.2]
  norm_num

lemma fold_info_10 : (primeRange 0 10000).foldl roundedStep (1000000,0) = (467786023,823097714) ∧
    ((primeRange 0 10000).map Nat.log2).sum = 13679 := by
  rw [show 10000 = 9000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_9.1, fold_info_9.2, chunk_info_9.1, chunk_info_9.2]
  norm_num

lemma fold_info_11 : (primeRange 0 11000).foldl roundedStep (1000000,0) = (485861664,823816476) ∧
    ((primeRange 0 11000).map Nat.log2).sum = 15057 := by
  rw [show 11000 = 10000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_10.1, fold_info_10.2, chunk_info_10.1, chunk_info_10.2]
  norm_num

lemma fold_info_12 : (primeRange 0 12000).foldl roundedStep (1000000,0) = (502448988,824417482) ∧
    ((primeRange 0 12000).map Nat.log2).sum = 16396 := by
  rw [show 12000 = 11000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_11.1, fold_info_11.2, chunk_info_11.1, chunk_info_11.2]
  norm_num

lemma fold_info_13 : (primeRange 0 13000).foldl roundedStep (1000000,0) = (519155939,824974797) ∧
    ((primeRange 0 13000).map Nat.log2).sum = 17813 := by
  rw [show 13000 = 12000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_12.1, fold_info_12.2, chunk_info_12.1, chunk_info_12.2]
  norm_num

lemma fold_info_14 : (primeRange 0 14000).foldl roundedStep (1000000,0) = (534529271,825449745) ∧
    ((primeRange 0 14000).map Nat.log2).sum = 19178 := by
  rw [show 14000 = 13000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_13.1, fold_info_13.2, chunk_info_13.1, chunk_info_13.2]
  norm_num

lemma fold_info_15 : (primeRange 0 15000).foldl roundedStep (1000000,0) = (548799383,825859450) ∧
    ((primeRange 0 15000).map Nat.log2).sum = 20504 := by
  rw [show 15000 = 14000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_14.1, fold_info_14.2, chunk_info_14.1, chunk_info_14.2]
  norm_num

lemma fold_info_16 : (primeRange 0 16000).foldl roundedStep (1000000,0) = (563336693,826250610) ∧
    ((primeRange 0 16000).map Nat.log2).sum = 21908 := by
  rw [show 16000 = 15000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_15.1, fold_info_15.2, chunk_info_15.1, chunk_info_15.2]
  norm_num

lemma fold_info_17 : (primeRange 0 17000).foldl roundedStep (1000000,0) = (576027674,826571283) ∧
    ((primeRange 0 17000).map Nat.log2).sum = 23242 := by
  rw [show 17000 = 16000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_16.1, fold_info_16.2, chunk_info_16.1, chunk_info_16.2]
  norm_num

lemma fold_info_18 : (primeRange 0 18000).foldl roundedStep (1000000,0) = (589007277,826880397) ∧
    ((primeRange 0 18000).map Nat.log2).sum = 24698 := by
  rw [show 18000 = 17000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_17.1, fold_info_17.2, chunk_info_17.1, chunk_info_17.2]
  norm_num

lemma fold_info_19 : (primeRange 0 19000).foldl roundedStep (1000000,0) = (600366131,827136951) ∧
    ((primeRange 0 19000).map Nat.log2).sum = 26014 := by
  rw [show 19000 = 18000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_18.1, fold_info_18.2, chunk_info_18.1, chunk_info_18.2]
  norm_num

lemma fold_info_20 : (primeRange 0 20000).foldl roundedStep (1000000,0) = (612492348,827396111) ∧
    ((primeRange 0 20000).map Nat.log2).sum = 27470 := by
  rw [show 20000 = 19000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_19.1, fold_info_19.2, chunk_info_19.1, chunk_info_19.2]
  norm_num

lemma fold_info_21 : (primeRange 0 21000).foldl roundedStep (1000000,0) = (623581399,827621788) ∧
    ((primeRange 0 21000).map Nat.log2).sum = 28842 := by
  rw [show 21000 = 20000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_20.1, fold_info_20.2, chunk_info_20.1, chunk_info_20.2]
  norm_num

lemma fold_info_22 : (primeRange 0 22000).foldl roundedStep (1000000,0) = (635004423,827843405) ∧
    ((primeRange 0 22000).map Nat.log2).sum = 30298 := by
  rw [show 22000 = 21000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_21.1, fold_info_21.2, chunk_info_21.1, chunk_info_21.2]
  norm_num

lemma fold_info_23 : (primeRange 0 23000).foldl roundedStep (1000000,0) = (645688371,828041546) ∧
    ((primeRange 0 23000).map Nat.log2).sum = 31698 := by
  rw [show 23000 = 22000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_22.1, fold_info_22.2, chunk_info_22.1, chunk_info_22.2]
  norm_num

lemma fold_info_24 : (primeRange 0 24000).foldl roundedStep (1000000,0) = (656498381,828233376) ∧
    ((primeRange 0 24000).map Nat.log2).sum = 33154 := by
  rw [show 24000 = 23000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_23.1, fold_info_23.2, chunk_info_23.1, chunk_info_23.2]
  norm_num

lemma fold_info_25 : (primeRange 0 25000).foldl roundedStep (1000000,0) = (666022132,828395580) ∧
    ((primeRange 0 25000).map Nat.log2).sum = 34470 := by
  rw [show 25000 = 24000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_24.1, fold_info_24.2, chunk_info_24.1, chunk_info_24.2]
  norm_num

lemma fold_info_26 : (primeRange 0 26000).foldl roundedStep (1000000,0) = (675686844,828553514) ∧
    ((primeRange 0 26000).map Nat.log2).sum = 35842 := by
  rw [show 26000 = 25000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_25.1, fold_info_25.2, chunk_info_25.1, chunk_info_25.2]
  norm_num

lemma fold_info_27 : (primeRange 0 27000).foldl roundedStep (1000000,0) = (685410248,828706414) ∧
    ((primeRange 0 27000).map Nat.log2).sum = 37256 := by
  rw [show 27000 = 26000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_26.1, fold_info_26.2, chunk_info_26.1, chunk_info_26.2]
  norm_num

lemma fold_info_28 : (primeRange 0 28000).foldl roundedStep (1000000,0) = (694245171,828840231) ∧
    ((primeRange 0 28000).map Nat.log2).sum = 38572 := by
  rw [show 28000 = 27000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_27.1, fold_info_27.2, chunk_info_27.1, chunk_info_27.2]
  norm_num

lemma fold_info_29 : (primeRange 0 29000).foldl roundedStep (1000000,0) = (703254435,828971992) ∧
    ((primeRange 0 29000).map Nat.log2).sum = 39944 := by
  rw [show 29000 = 28000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_28.1, fold_info_28.2, chunk_info_28.1, chunk_info_28.2]
  norm_num

lemma fold_info_30 : (primeRange 0 30000).foldl roundedStep (1000000,0) = (711536051,829089140) ∧
    ((primeRange 0 30000).map Nat.log2).sum = 41232 := by
  rw [show 30000 = 29000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_29.1, fold_info_29.2, chunk_info_29.1, chunk_info_29.2]
  norm_num

lemma fold_info_31 : (primeRange 0 31000).foldl roundedStep (1000000,0) = (719897589,829203451) ∧
    ((primeRange 0 31000).map Nat.log2).sum = 42562 := by
  rw [show 31000 = 30000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_30.1, fold_info_30.2, chunk_info_30.1, chunk_info_30.2]
  norm_num

lemma fold_info_32 : (primeRange 0 32000).foldl roundedStep (1000000,0) = (727835540,829308634) ∧
    ((primeRange 0 32000).map Nat.log2).sum = 43850 := by
  rw [show 32000 = 31000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_31.1, fold_info_31.2, chunk_info_31.1, chunk_info_31.2]
  norm_num

lemma fold_info_33 : (primeRange 0 33000).foldl roundedStep (1000000,0) = (736794977,829423593) ∧
    ((primeRange 0 33000).map Nat.log2).sum = 45360 := by
  rw [show 33000 = 32000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_32.1, fold_info_32.2, chunk_info_32.1, chunk_info_32.2]
  norm_num

lemma fold_info_34 : (primeRange 0 34000).foldl roundedStep (1000000,0) = (745088999,829526806) ∧
    ((primeRange 0 34000).map Nat.log2).sum = 46860 := by
  rw [show 34000 = 33000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_33.1, fold_info_33.2, chunk_info_33.1, chunk_info_33.2]
  norm_num

lemma fold_info_35 : (primeRange 0 35000).foldl roundedStep (1000000,0) = (752741182,829619286) ∧
    ((primeRange 0 35000).map Nat.log2).sum = 48270 := by
  rw [show 35000 = 34000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_34.1, fold_info_34.2, chunk_info_34.1, chunk_info_34.2]
  norm_num

lemma fold_info_36 : (primeRange 0 36000).foldl roundedStep (1000000,0) = (760092838,829705633) ∧
    ((primeRange 0 36000).map Nat.log2).sum = 49650 := by
  rw [show 36000 = 35000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_35.1, fold_info_35.2, chunk_info_35.1, chunk_info_35.2]
  norm_num

lemma fold_info_37 : (primeRange 0 37000).foldl roundedStep (1000000,0) = (767859774,829794306) ∧
    ((primeRange 0 37000).map Nat.log2).sum = 51135 := by
  rw [show 37000 = 36000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_36.1, fold_info_36.2, chunk_info_36.1, chunk_info_36.2]
  norm_num

lemma fold_info_38 : (primeRange 0 38000).foldl roundedStep (1000000,0) = (775111938,829874940) ∧
    ((primeRange 0 38000).map Nat.log2).sum = 52545 := by
  rw [show 38000 = 37000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_37.1, fold_info_37.2, chunk_info_37.1, chunk_info_37.2]
  norm_num

lemma fold_info_39 : (primeRange 0 39000).foldl roundedStep (1000000,0) = (781932368,829948754) ∧
    ((primeRange 0 39000).map Nat.log2).sum = 53895 := by
  rw [show 39000 = 38000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_38.1, fold_info_38.2, chunk_info_38.1, chunk_info_38.2]
  norm_num

lemma fold_info_40 : (primeRange 0 40000).foldl roundedStep (1000000,0) = (789092232,830024338) ∧
    ((primeRange 0 40000).map Nat.log2).sum = 55335 := by
  rw [show 40000 = 39000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_39.1, fold_info_39.2, chunk_info_39.1, chunk_info_39.2]
  norm_num

lemma fold_info_41 : (primeRange 0 41000).foldl roundedStep (1000000,0) = (795547438,830090789) ∧
    ((primeRange 0 41000).map Nat.log2).sum = 56655 := by
  rw [show 41000 = 40000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_40.1, fold_info_40.2, chunk_info_40.1, chunk_info_40.2]
  norm_num

lemma fold_info_42 : (primeRange 0 42000).foldl roundedStep (1000000,0) = (802840450,830164059) ∧
    ((primeRange 0 42000).map Nat.log2).sum = 58170 := by
  rw [show 42000 = 41000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_41.1, fold_info_41.2, chunk_info_41.1, chunk_info_41.2]
  norm_num

lemma fold_info_43 : (primeRange 0 43000).foldl roundedStep (1000000,0) = (810099236,830235282) ∧
    ((primeRange 0 43000).map Nat.log2).sum = 59700 := by
  rw [show 43000 = 42000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_42.1, fold_info_42.2, chunk_info_42.1, chunk_info_42.2]
  norm_num

lemma fold_info_44 : (primeRange 0 44000).foldl roundedStep (1000000,0) = (816054806,830292351) ∧
    ((primeRange 0 44000).map Nat.log2).sum = 60975 := by
  rw [show 44000 = 43000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_43.1, fold_info_43.2, chunk_info_43.1, chunk_info_43.2]
  norm_num

lemma fold_info_45 : (primeRange 0 45000).foldl roundedStep (1000000,0) = (822683628,830354472) ∧
    ((primeRange 0 45000).map Nat.log2).sum = 62415 := by
  rw [show 45000 = 44000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_44.1, fold_info_44.2, chunk_info_44.1, chunk_info_44.2]
  norm_num

lemma fold_info_46 : (primeRange 0 46000).foldl roundedStep (1000000,0) = (828534672,830408090) ∧
    ((primeRange 0 46000).map Nat.log2).sum = 63705 := by
  rw [show 46000 = 45000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_45.1, fold_info_45.2, chunk_info_45.1, chunk_info_45.2]
  norm_num

lemma fold_info_47 : (primeRange 0 47000).foldl roundedStep (1000000,0) = (834570861,830462231) ∧
    ((primeRange 0 47000).map Nat.log2).sum = 65055 := by
  rw [show 47000 = 46000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_46.1, fold_info_46.2, chunk_info_46.1, chunk_info_46.2]
  norm_num

lemma fold_info_48 : (primeRange 0 48000).foldl roundedStep (1000000,0) = (840851924,830517364) ∧
    ((primeRange 0 48000).map Nat.log2).sum = 66480 := by
  rw [show 48000 = 47000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_47.1, fold_info_47.2, chunk_info_47.1, chunk_info_47.2]
  norm_num

lemma fold_info_49 : (primeRange 0 49000).foldl roundedStep (1000000,0) = (846656888,830567268) ∧
    ((primeRange 0 49000).map Nat.log2).sum = 67815 := by
  rw [show 49000 = 48000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_48.1, fold_info_48.2, chunk_info_48.1, chunk_info_48.2]
  norm_num

lemma fold_info_50 : (primeRange 0 50000).foldl roundedStep (1000000,0) = (852967523,830620449) ∧
    ((primeRange 0 50000).map Nat.log2).sum = 69285 := by
  rw [show 50000 = 49000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_49.1, fold_info_49.2, chunk_info_49.1, chunk_info_49.2]
  norm_num

lemma fold_info_51 : (primeRange 0 51000).foldl roundedStep (1000000,0) = (858625394,830667191) ∧
    ((primeRange 0 51000).map Nat.log2).sum = 70620 := by
  rw [show 51000 = 50000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_50.1, fold_info_50.2, chunk_info_50.1, chunk_info_50.2]
  norm_num

lemma fold_info_52 : (primeRange 0 52000).foldl roundedStep (1000000,0) = (864710282,830716461) ∧
    ((primeRange 0 52000).map Nat.log2).sum = 72075 := by
  rw [show 52000 = 51000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_51.1, fold_info_51.2, chunk_info_51.1, chunk_info_51.2]
  norm_num

lemma fold_info_53 : (primeRange 0 53000).foldl roundedStep (1000000,0) = (870223592,830760249) ∧
    ((primeRange 0 53000).map Nat.log2).sum = 73410 := by
  rw [show 53000 = 52000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_52.1, fold_info_52.2, chunk_info_52.1, chunk_info_52.2]
  norm_num

lemma fold_info_54 : (primeRange 0 54000).foldl roundedStep (1000000,0) = (875853384,830804137) ∧
    ((primeRange 0 54000).map Nat.log2).sum = 74790 := by
  rw [show 54000 = 53000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_53.1, fold_info_53.2, chunk_info_53.1, chunk_info_53.2]
  norm_num

lemma fold_info_55 : (primeRange 0 55000).foldl roundedStep (1000000,0) = (881294082,830845780) ∧
    ((primeRange 0 55000).map Nat.log2).sum = 76140 := by
  rw [show 55000 = 54000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_54.1, fold_info_54.2, chunk_info_54.1, chunk_info_54.2]
  norm_num

lemma fold_info_56 : (primeRange 0 56000).foldl roundedStep (1000000,0) = (886847630,830887507) ∧
    ((primeRange 0 56000).map Nat.log2).sum = 77535 := by
  rw [show 56000 = 55000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_55.1, fold_info_55.2, chunk_info_55.1, chunk_info_55.2]
  norm_num

lemma fold_info_57 : (primeRange 0 57000).foldl roundedStep (1000000,0) = (892691186,830930629) ∧
    ((primeRange 0 57000).map Nat.log2).sum = 79020 := by
  rw [show 57000 = 56000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_56.1, fold_info_56.2, chunk_info_56.1, chunk_info_56.2]
  norm_num

lemma fold_info_58 : (primeRange 0 58000).foldl roundedStep (1000000,0) = (898004955,830969183) ∧
    ((primeRange 0 58000).map Nat.log2).sum = 80385 := by
  rw [show 58000 = 57000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_57.1, fold_info_57.2, chunk_info_57.1, chunk_info_57.2]
  norm_num

lemma fold_info_59 : (primeRange 0 59000).foldl roundedStep (1000000,0) = (903202732,831006263) ∧
    ((primeRange 0 59000).map Nat.log2).sum = 81735 := by
  rw [show 59000 = 58000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_58.1, fold_info_58.2, chunk_info_58.1, chunk_info_58.2]
  norm_num

lemma fold_info_60 : (primeRange 0 60000).foldl roundedStep (1000000,0) = (908573340,831043947) ∧
    ((primeRange 0 60000).map Nat.log2).sum = 83145 := by
  rw [show 60000 = 59000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_59.1, fold_info_59.2, chunk_info_59.1, chunk_info_59.2]
  norm_num

lemma fold_info_61 : (primeRange 0 61000).foldl roundedStep (1000000,0) = (913543102,831078219) ∧
    ((primeRange 0 61000).map Nat.log2).sum = 84465 := by
  rw [show 61000 = 60000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_60.1, fold_info_60.2, chunk_info_60.1, chunk_info_60.2]
  norm_num

lemma fold_info_62 : (primeRange 0 62000).foldl roundedStep (1000000,0) = (918401330,831111171) ∧
    ((primeRange 0 62000).map Nat.log2).sum = 85770 := by
  rw [show 62000 = 61000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_61.1, fold_info_61.2, chunk_info_61.1, chunk_info_61.2]
  norm_num

lemma fold_info_63 : (primeRange 0 63000).foldl roundedStep (1000000,0) = (923263233,831143630) ∧
    ((primeRange 0 63000).map Nat.log2).sum = 87090 := by
  rw [show 63000 = 62000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_62.1, fold_info_62.2, chunk_info_62.1, chunk_info_62.2]
  norm_num

lemma fold_info_64 : (primeRange 0 64000).foldl roundedStep (1000000,0) = (928346880,831177029) ∧
    ((primeRange 0 64000).map Nat.log2).sum = 88485 := by
  rw [show 64000 = 63000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_63.1, fold_info_63.2, chunk_info_63.1, chunk_info_63.2]
  norm_num

lemma fold_info_65 : (primeRange 0 65000).foldl roundedStep (1000000,0) = (932675038,831205028) ∧
    ((primeRange 0 65000).map Nat.log2).sum = 89685 := by
  rw [show 65000 = 64000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_64.1, fold_info_64.2, chunk_info_64.1, chunk_info_64.2]
  norm_num

lemma fold_info_66 : (primeRange 0 66000).foldl roundedStep (1000000,0) = (937923119,831238462) ∧
    ((primeRange 0 66000).map Nat.log2).sum = 91204 := by
  rw [show 66000 = 65000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_65.1, fold_info_65.2, chunk_info_65.1, chunk_info_65.2]
  norm_num

lemma fold_info_67 : (primeRange 0 67000).foldl roundedStep (1000000,0) = (942375150,831266393) ∧
    ((primeRange 0 67000).map Nat.log2).sum = 92548 := by
  rw [show 67000 = 66000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_66.1, fold_info_66.2, chunk_info_66.1, chunk_info_66.2]
  norm_num

lemma fold_info_68 : (primeRange 0 68000).foldl roundedStep (1000000,0) = (947572084,831298520) ∧
    ((primeRange 0 68000).map Nat.log2).sum = 94132 := by
  rw [show 68000 = 67000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_67.1, fold_info_67.2, chunk_info_67.1, chunk_info_67.2]
  norm_num

lemma fold_info_69 : (primeRange 0 69000).foldl roundedStep (1000000,0) = (951729918,831323846) ∧
    ((primeRange 0 69000).map Nat.log2).sum = 95412 := by
  rw [show 69000 = 68000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_68.1, fold_info_68.2, chunk_info_68.1, chunk_info_68.2]
  norm_num

lemma fold_info_70 : (primeRange 0 70000).foldl roundedStep (1000000,0) = (955899720,831348891) ∧
    ((primeRange 0 70000).map Nat.log2).sum = 96708 := by
  rw [show 70000 = 69000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_69.1, fold_info_69.2, chunk_info_69.1, chunk_info_69.2]
  norm_num

lemma fold_info_71 : (primeRange 0 71000).foldl roundedStep (1000000,0) = (960895734,831378465) ∧
    ((primeRange 0 71000).map Nat.log2).sum = 98276 := by
  rw [show 71000 = 70000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_70.1, fold_info_70.2, chunk_info_70.1, chunk_info_70.2]
  norm_num

lemma fold_info_72 : (primeRange 0 72000).foldl roundedStep (1000000,0) = (965694246,831406470) ∧
    ((primeRange 0 72000).map Nat.log2).sum = 99796 := by
  rw [show 72000 = 71000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_71.1, fold_info_71.2, chunk_info_71.1, chunk_info_71.2]
  norm_num

lemma fold_info_73 : (primeRange 0 73000).foldl roundedStep (1000000,0) = (970199492,831432398) ∧
    ((primeRange 0 73000).map Nat.log2).sum = 101236 := by
  rw [show 73000 = 72000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_72.1, fold_info_72.2, chunk_info_72.1, chunk_info_72.2]
  norm_num

lemma fold_info_74 : (primeRange 0 74000).foldl roundedStep (1000000,0) = (974316380,831455776) ∧
    ((primeRange 0 74000).map Nat.log2).sum = 102564 := by
  rw [show 74000 = 73000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_73.1, fold_info_73.2, chunk_info_73.1, chunk_info_73.2]
  norm_num

lemma fold_info_75 : (primeRange 0 75000).foldl roundedStep (1000000,0) = (978839435,831481121) ∧
    ((primeRange 0 75000).map Nat.log2).sum = 104036 := by
  rw [show 75000 = 74000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_74.1, fold_info_74.2, chunk_info_74.1, chunk_info_74.2]
  norm_num

lemma fold_info_76 : (primeRange 0 76000).foldl roundedStep (1000000,0) = (983273475,831505634) ∧
    ((primeRange 0 76000).map Nat.log2).sum = 105492 := by
  rw [show 76000 = 75000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_75.1, fold_info_75.2, chunk_info_75.1, chunk_info_75.2]
  norm_num

lemma fold_info_77 : (primeRange 0 77000).foldl roundedStep (1000000,0) = (987282198,831527511) ∧
    ((primeRange 0 77000).map Nat.log2).sum = 106820 := by
  rw [show 77000 = 76000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_76.1, fold_info_76.2, chunk_info_76.1, chunk_info_76.2]
  norm_num

lemma fold_info_78 : (primeRange 0 78000).foldl roundedStep (1000000,0) = (991831212,831552018) ∧
    ((primeRange 0 78000).map Nat.log2).sum = 108340 := by
  rw [show 78000 = 77000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_77.1, fold_info_77.2, chunk_info_77.1, chunk_info_77.2]
  norm_num

lemma fold_info_79 : (primeRange 0 79000).foldl roundedStep (1000000,0) = (995819094,831573224) ∧
    ((primeRange 0 79000).map Nat.log2).sum = 109684 := by
  rw [show 79000 = 78000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_78.1, fold_info_78.2, chunk_info_78.1, chunk_info_78.2]
  norm_num

lemma fold_info_80 : (primeRange 0 80000).foldl roundedStep (1000000,0) = (1000101383,831595712) ∧
    ((primeRange 0 80000).map Nat.log2).sum = 111140 := by
  rw [show 80000 = 79000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_79.1, fold_info_79.2, chunk_info_79.1, chunk_info_79.2]
  norm_num

lemma fold_info_81 : (primeRange 0 81000).foldl roundedStep (1000000,0) = (1004208912,831617012) ∧
    ((primeRange 0 81000).map Nat.log2).sum = 112548 := by
  rw [show 81000 = 80000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_80.1, fold_info_80.2, chunk_info_80.1, chunk_info_80.2]
  norm_num

lemma fold_info_82 : (primeRange 0 82000).foldl roundedStep (1000000,0) = (1008469964,831638848) ∧
    ((primeRange 0 82000).map Nat.log2).sum = 114020 := by
  rw [show 82000 = 81000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_81.1, fold_info_81.2, chunk_info_81.1, chunk_info_81.2]
  norm_num

lemma fold_info_83 : (primeRange 0 83000).foldl roundedStep (1000000,0) = (1012559622,831659557) ∧
    ((primeRange 0 83000).map Nat.log2).sum = 115444 := by
  rw [show 83000 = 82000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_82.1, fold_info_82.2, chunk_info_82.1, chunk_info_82.2]
  norm_num

lemma fold_info_84 : (primeRange 0 84000).foldl roundedStep (1000000,0) = (1016387483,831678705) ∧
    ((primeRange 0 84000).map Nat.log2).sum = 116788 := by
  rw [show 84000 = 83000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_83.1, fold_info_83.2, chunk_info_83.1, chunk_info_83.2]
  norm_num

lemma fold_info_85 : (primeRange 0 85000).foldl roundedStep (1000000,0) = (1020320068,831698144) ∧
    ((primeRange 0 85000).map Nat.log2).sum = 118180 := by
  rw [show 85000 = 84000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_84.1, fold_info_84.2, chunk_info_84.1, chunk_info_84.2]
  norm_num

lemma fold_info_86 : (primeRange 0 86000).foldl roundedStep (1000000,0) = (1024132130,831716772) ∧
    ((primeRange 0 86000).map Nat.log2).sum = 119540 := by
  rw [show 86000 = 85000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_85.1, fold_info_85.2, chunk_info_85.1, chunk_info_85.2]
  norm_num

lemma fold_info_87 : (primeRange 0 87000).foldl roundedStep (1000000,0) = (1028047832,831735684) ∧
    ((primeRange 0 87000).map Nat.log2).sum = 120948 := by
  rw [show 87000 = 86000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_86.1, fold_info_86.2, chunk_info_86.1, chunk_info_86.2]
  norm_num

lemma fold_info_88 : (primeRange 0 88000).foldl roundedStep (1000000,0) = (1032153146,831755280) ∧
    ((primeRange 0 88000).map Nat.log2).sum = 122436 := by
  rw [show 88000 = 87000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_87.1, fold_info_87.2, chunk_info_87.1, chunk_info_87.2]
  norm_num

lemma fold_info_89 : (primeRange 0 89000).foldl roundedStep (1000000,0) = (1035480974,831770979) ∧
    ((primeRange 0 89000).map Nat.log2).sum = 123652 := by
  rw [show 89000 = 88000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_88.1, fold_info_88.2, chunk_info_88.1, chunk_info_88.2]
  norm_num

lemma fold_info_90 : (primeRange 0 90000).foldl roundedStep (1000000,0) = (1039567741,831790055) ∧
    ((primeRange 0 90000).map Nat.log2).sum = 125156 := by
  rw [show 90000 = 89000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_89.1, fold_info_89.2, chunk_info_89.1, chunk_info_89.2]
  norm_num

lemma fold_info_91 : (primeRange 0 91000).foldl roundedStep (1000000,0) = (1043409968,831807796) ∧
    ((primeRange 0 91000).map Nat.log2).sum = 126580 := by
  rw [show 91000 = 90000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_90.1, fold_info_90.2, chunk_info_90.1, chunk_info_90.2]
  norm_num

lemma fold_info_92 : (primeRange 0 92000).foldl roundedStep (1000000,0) = (1047051451,831824421) ∧
    ((primeRange 0 92000).map Nat.log2).sum = 127940 := by
  rw [show 92000 = 91000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_91.1, fold_info_91.2, chunk_info_91.1, chunk_info_91.2]
  norm_num

lemma fold_info_93 : (primeRange 0 93000).foldl roundedStep (1000000,0) = (1051176583,831843048) ∧
    ((primeRange 0 93000).map Nat.log2).sum = 129492 := by
  rw [show 93000 = 92000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_92.1, fold_info_92.2, chunk_info_92.1, chunk_info_92.2]
  norm_num

lemma fold_info_94 : (primeRange 0 94000).foldl roundedStep (1000000,0) = (1054808687,831859277) ∧
    ((primeRange 0 94000).map Nat.log2).sum = 130868 := by
  rw [show 94000 = 93000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_93.1, fold_info_93.2, chunk_info_93.1, chunk_info_93.2]
  norm_num

lemma fold_info_95 : (primeRange 0 95000).foldl roundedStep (1000000,0) = (1058456560,831875404) ∧
    ((primeRange 0 95000).map Nat.log2).sum = 132260 := by
  rw [show 95000 = 94000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_94.1, fold_info_94.2, chunk_info_94.1, chunk_info_94.2]
  norm_num

lemma fold_info_96 : (primeRange 0 96000).foldl roundedStep (1000000,0) = (1062412715,831892710) ∧
    ((primeRange 0 96000).map Nat.log2).sum = 133780 := by
  rw [show 96000 = 95000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_95.1, fold_info_95.2, chunk_info_95.1, chunk_info_95.2]
  norm_num

lemma fold_info_97 : (primeRange 0 97000).foldl roundedStep (1000000,0) = (1065885958,831907750) ∧
    ((primeRange 0 97000).map Nat.log2).sum = 135124 := by
  rw [show 97000 = 96000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_96.1, fold_info_96.2, chunk_info_96.1, chunk_info_96.2]
  norm_num

lemma fold_info_98 : (primeRange 0 98000).foldl roundedStep (1000000,0) = (1069252623,831922181) ∧
    ((primeRange 0 98000).map Nat.log2).sum = 136436 := by
  rw [show 98000 = 97000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_97.1, fold_info_97.2, chunk_info_97.1, chunk_info_97.2]
  norm_num

lemma fold_info_99 : (primeRange 0 99000).foldl roundedStep (1000000,0) = (1072798738,831937219) ∧
    ((primeRange 0 99000).map Nat.log2).sum = 137828 := by
  rw [show 99000 = 98000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_98.1, fold_info_98.2, chunk_info_98.1, chunk_info_98.2]
  norm_num

lemma fold_info_100 : (primeRange 0 100000).foldl roundedStep (1000000,0) = (1076322120,831952011) ∧
    ((primeRange 0 100000).map Nat.log2).sum = 139220 := by
  rw [show 100000 = 99000+1000 by rfl, primeRange_append]
  simp only [Nat.zero_add, List.foldl_append, List.map_append, List.sum_append,
    fold_info_99.1, fold_info_99.2, chunk_info_99.1, chunk_info_99.2]
  norm_num
def fixedPrimes : List ℕ := primeRange 0 100000

def rounded : ℕ × ℕ := fixedPrimes.foldl roundedStep (1000000,0)
def bits : ℕ := (fixedPrimes.map Nat.log2).sum

lemma rounded_certificate : rounded = (1076322120,831952011) := fold_info_100.1
lemma bits_certificate : bits = 139220 := fold_info_100.2

lemma fixedPrimes_eq : fixedPrimes = (List.range 100000).filter (fun p =>
    decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p)) := by
  simp only [fixedPrimes, primeRange, List.range_eq_range']

lemma mem_prefix (p : ℕ) : p ∈ fixedPrimes ↔ p.Prime ∧ 5 ≤ p ∧ p < 100000 := by
  rw [fixedPrimes_eq]
  simp only [List.mem_filter,List.mem_range,Bool.and_eq_true,decide_eq_true_eq]
  tauto

lemma prefix_ge_five : ∀ p ∈ fixedPrimes.toFinset, 5 ≤ p := by
  intro p hp
  exact ((mem_prefix p).mp (List.mem_toFinset.mp hp)).2.1

lemma prefix_pairwise : fixedPrimes.Pairwise (· < ·) := by
  rw [fixedPrimes_eq]
  exact List.Pairwise.filter _ List.pairwise_lt_range

#print axioms rounded_certificate
#print axioms bits_certificate
end Erdos7SharpRawPrefix
