import Submission.No9PrefixCert0
import Submission.No9PrefixCert1
import Submission.No9PrefixCert2
import Submission.No9PrefixCert3
import Submission.No9PrefixCert4
import Submission.No9PrefixCert5
import Submission.No9PrefixCert6
import Submission.No9PrefixCert7
import Submission.No9PrefixCert8
import Submission.No9PrefixCert9
import Submission.No9PrefixCert10
import Submission.No9PrefixCert11
import Submission.No9PrefixCert12
import Submission.No9PrefixCert13
import Submission.No9PrefixCert14
import Submission.No9PrefixCert15
import Submission.No9PrefixCert16
import Submission.No9PrefixCert17
import Submission.No9PrefixCert18
import Submission.No9PrefixCert19
import Submission.No9PrefixCert20
import Submission.No9PrefixCert21
import Submission.No9PrefixCert22
import Submission.No9PrefixCert23
import Submission.No9PrefixCert24
import Submission.No9PrefixCert25
import Submission.No9PrefixCert26
import Submission.No9PrefixCert27
import Submission.No9PrefixCert28
import Submission.No9PrefixCert29
import Submission.No9PrefixCert30
import Submission.No9PrefixCert31
import Submission.No9PrefixCert32
import Submission.No9PrefixCert33
import Submission.No9PrefixCert34
import Submission.No9PrefixCert35
import Submission.No9PrefixCert36
import Submission.No9PrefixCert37
import Submission.No9PrefixCert38
import Submission.No9PrefixCert39
import Submission.No9PrefixCert40
import Submission.No9PrefixCert41
import Submission.No9BlockCert0
import Submission.No9BlockCert1
import Submission.No9BlockCert2
import Submission.No9BlockCert3
import Submission.No9BlockCert4
import Submission.No9BlockCert5
import Submission.No9BlockCert6
import Submission.No9BlockCert7
import Submission.No9BlockCert8
import Submission.No9BlockCert9
import Submission.No9BlockCert10
import Submission.No9BlockCert11
import Submission.No9BlockCert12
import Submission.No9BlockCert13
import Submission.No9BlockCert14
import Submission.No9BlockCert15
import Submission.No9BlockCert16
import Submission.No9BlockCert17

/-! All finite integer transitions have been checked by the kernel.
Prime coverage and the arithmetic gluing are separate obligations. -/
namespace Erdos7No9Certificate
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000
theorem prefix_checks_all (i : ℕ) (hi : i < prefixLength) : prefixTransitionCheck i=true := by
  change i < 668 at hi
  have hk : i/16 < 42 := by omega
  generalize heq : i/16=k at *
  interval_cases k
  · exact prefix_transitions_0 i (by omega) (by omega)
  · exact prefix_transitions_1 i (by omega) (by omega)
  · exact prefix_transitions_2 i (by omega) (by omega)
  · exact prefix_transitions_3 i (by omega) (by omega)
  · exact prefix_transitions_4 i (by omega) (by omega)
  · exact prefix_transitions_5 i (by omega) (by omega)
  · exact prefix_transitions_6 i (by omega) (by omega)
  · exact prefix_transitions_7 i (by omega) (by omega)
  · exact prefix_transitions_8 i (by omega) (by omega)
  · exact prefix_transitions_9 i (by omega) (by omega)
  · exact prefix_transitions_10 i (by omega) (by omega)
  · exact prefix_transitions_11 i (by omega) (by omega)
  · exact prefix_transitions_12 i (by omega) (by omega)
  · exact prefix_transitions_13 i (by omega) (by omega)
  · exact prefix_transitions_14 i (by omega) (by omega)
  · exact prefix_transitions_15 i (by omega) (by omega)
  · exact prefix_transitions_16 i (by omega) (by omega)
  · exact prefix_transitions_17 i (by omega) (by omega)
  · exact prefix_transitions_18 i (by omega) (by omega)
  · exact prefix_transitions_19 i (by omega) (by omega)
  · exact prefix_transitions_20 i (by omega) (by omega)
  · exact prefix_transitions_21 i (by omega) (by omega)
  · exact prefix_transitions_22 i (by omega) (by omega)
  · exact prefix_transitions_23 i (by omega) (by omega)
  · exact prefix_transitions_24 i (by omega) (by omega)
  · exact prefix_transitions_25 i (by omega) (by omega)
  · exact prefix_transitions_26 i (by omega) (by omega)
  · exact prefix_transitions_27 i (by omega) (by omega)
  · exact prefix_transitions_28 i (by omega) (by omega)
  · exact prefix_transitions_29 i (by omega) (by omega)
  · exact prefix_transitions_30 i (by omega) (by omega)
  · exact prefix_transitions_31 i (by omega) (by omega)
  · exact prefix_transitions_32 i (by omega) (by omega)
  · exact prefix_transitions_33 i (by omega) (by omega)
  · exact prefix_transitions_34 i (by omega) (by omega)
  · exact prefix_transitions_35 i (by omega) (by omega)
  · exact prefix_transitions_36 i (by omega) (by omega)
  · exact prefix_transitions_37 i (by omega) (by omega)
  · exact prefix_transitions_38 i (by omega) (by omega)
  · exact prefix_transitions_39 i (by omega) (by omega)
  · exact prefix_transitions_40 i (by omega) (by omega)
  · exact prefix_transitions_41 i (by omega) (by omega)
theorem block_checks_all (i : ℕ) (hi : i < blockLength) : blockTransitionCheck i=true := by
  change i < 288 at hi
  have hk : i/16 < 18 := by omega
  generalize heq : i/16=k at *
  interval_cases k
  · exact block_transitions_0 i (by omega) (by omega)
  · exact block_transitions_1 i (by omega) (by omega)
  · exact block_transitions_2 i (by omega) (by omega)
  · exact block_transitions_3 i (by omega) (by omega)
  · exact block_transitions_4 i (by omega) (by omega)
  · exact block_transitions_5 i (by omega) (by omega)
  · exact block_transitions_6 i (by omega) (by omega)
  · exact block_transitions_7 i (by omega) (by omega)
  · exact block_transitions_8 i (by omega) (by omega)
  · exact block_transitions_9 i (by omega) (by omega)
  · exact block_transitions_10 i (by omega) (by omega)
  · exact block_transitions_11 i (by omega) (by omega)
  · exact block_transitions_12 i (by omega) (by omega)
  · exact block_transitions_13 i (by omega) (by omega)
  · exact block_transitions_14 i (by omega) (by omega)
  · exact block_transitions_15 i (by omega) (by omega)
  · exact block_transitions_16 i (by omega) (by omega)
  · exact block_transitions_17 i (by omega) (by omega)

theorem final_integer_margin :
    6*(blockState blockLength).cubic < (blockState blockLength).mass*1500000^2 := by decide +kernel

theorem final_mass_positive : 0 < (blockState blockLength).mass := by decide +kernel

def prefixOrderCheck : Bool :=
  (prefixControl 0).p==3 && decide ((prefixControl (prefixLength-1)).p < 5000) &&
    (List.range (prefixLength-1)).all (fun i => decide ((prefixControl i).p < (prefixControl (i+1)).p))

def blockOrderCheck : Bool :=
  (blockControl 0).lo==5000 && (blockControl (blockLength-1)).hi==1500001 &&
    (List.range (blockLength-1)).all (fun i => (blockControl i).hi==(blockControl (i+1)).lo)

theorem prefix_order_check : prefixOrderCheck=true := by decide +kernel
theorem block_order_check : blockOrderCheck=true := by decide +kernel

theorem prefix_block_state_agree : prefixState prefixLength=blockState 0 := by rfl

#print axioms prefix_checks_all
#print axioms block_checks_all
#print axioms final_integer_margin
end Erdos7No9Certificate
