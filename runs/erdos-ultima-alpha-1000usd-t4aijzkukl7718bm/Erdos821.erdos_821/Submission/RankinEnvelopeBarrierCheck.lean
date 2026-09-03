import Submission.RankinEnvelopeBarrier

/-! Audits for a lower bound on the explicit majorant, not on g. -/

open Erdos821.RankinEnvelope

#check smooth_constant_ge_one
#check envelope_ge_power
#check majorant
#check eventually_majorant_ge_power
#check eventually_majorant_gt_power

#print axioms smooth_constant_ge_one
#print axioms envelope_ge_power
#print axioms eventually_majorant_ge_power
#print axioms eventually_majorant_gt_power
