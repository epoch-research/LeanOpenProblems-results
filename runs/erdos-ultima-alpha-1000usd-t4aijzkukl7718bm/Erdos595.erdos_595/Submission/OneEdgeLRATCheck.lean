import FormalConjecturesUtil
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos595OneEdgeLRATCheck
lrat_proof finite_obstruction
  (include_str "/tmp/oneedge_local_core.cnf")
  (include_str "/tmp/oneedge_local_core.lrat")
#print axioms finite_obstruction
end Erdos595OneEdgeLRATCheck
