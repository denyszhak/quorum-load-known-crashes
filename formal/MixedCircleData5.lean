import MixedCircleRow5_001
import MixedCircleRow5_002
import MixedCircleRow5_003
import MixedCircleRow5_004
import MixedCircleRow5_005
import MixedCircleRow5_006
import MixedCircleRow5_007
import MixedCircleRow5_008
import MixedCircleRow5_009
import MixedCircleRow5_010
import MixedCircleRow5_011
import MixedCircleRow5_012

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificates5 : List CircleCertificate := [certificate_5_1, certificate_5_2, certificate_5_3, certificate_5_4, certificate_5_5, certificate_5_6, certificate_5_7, certificate_5_8, certificate_5_9, certificate_5_10, certificate_5_11, certificate_5_12]

theorem certificates5_valid : ∀ c ∈ certificates5, c.Valid 24 5 := by
  intro c hc
  simp only [certificates5, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact certificate_5_1_valid
  · exact certificate_5_2_valid
  · exact certificate_5_3_valid
  · exact certificate_5_4_valid
  · exact certificate_5_5_valid
  · exact certificate_5_6_valid
  · exact certificate_5_7_valid
  · exact certificate_5_8_valid
  · exact certificate_5_9_valid
  · exact certificate_5_10_valid
  · exact certificate_5_11_valid
  · exact certificate_5_12_valid

theorem certificates5_coverage :
    ∀ d ∈ Finset.Ico 1 (24 / 2 + 1), ∃ c ∈ certificates5, c.failed = {0, d} := by decide +kernel

#print axioms certificates5_valid
#print axioms certificates5_coverage
end QuorumAudit.MixedCircle
