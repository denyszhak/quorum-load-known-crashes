import TwoCrashBases
import TwoCrashTransport

namespace QuorumAudit.TwoCrash
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem zero_scale_rejected : ¬ Valid {base11 with scale := 0} := by decide +kernel
theorem missing_read_rejected : ¬ Valid {base11 with reads := []} := by decide +kernel
theorem wrong_read_size_rejected :
    ¬ ReadValid 11 3 ({1,2,3,6} : Finset Nat) := by decide +kernel
theorem foreign_server_rejected :
    ¬ ReadValid 11 3 ({1,2,3,6,11} : Finset Nat) := by decide +kernel
theorem empty_uniform_rejected : ¬ Valid {base11 with uniform := []} := by decide +kernel
theorem empty_critical_rejected : ¬ Valid {base11 with criticalFlow := []} := by decide +kernel
theorem failed_read_rejected :
    ¬ Valid {base11 with reads := [[0,2,3,6,9],[1,2,5,8,9],[2,3,6,7,10]]} := by decide +kernel

/-- Removing positive mass from one write preserves nonnegativity but
breaks the exact semantic mass/degree conditions. -/
theorem altered_weight_rejected :
    ¬ Valid {base11 with uniform := base11.uniform.set 2 0} := by decide +kernel

#print axioms zero_scale_rejected
#print axioms missing_read_rejected
#print axioms wrong_read_size_rejected
#print axioms foreign_server_rejected
#print axioms empty_uniform_rejected
#print axioms empty_critical_rejected
#print axioms failed_read_rejected
#print axioms altered_weight_rejected
end QuorumAudit.TwoCrash
