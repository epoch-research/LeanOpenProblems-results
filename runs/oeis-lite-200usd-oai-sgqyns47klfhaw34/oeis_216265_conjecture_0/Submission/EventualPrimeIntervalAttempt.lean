import FormalConjectures.Util.ProblemImports
open Filter Nat
open scoped Nat.Prime

-- Check available asymptotic lower/upper ingredients for eventual prime intervals.
#check Chebyshev.primeCounting_sub_theta_div_log_isBigO
#check Chebyshev.eventually_primeCounting_le
#check Chebyshev.theta_pos
#check Chebyshev.theta_mono
#check Nat.tendsto_primeCounting
#check Filter.Tendsto.eventually
#check tendsto_atTop_mono
#check eventually_ge_atTop
#check Asymptotics.IsBigO.bound
#check Asymptotics.IsLittleO.bound
