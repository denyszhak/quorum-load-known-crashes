import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_8 : CircleCertificate := {
  failed := {0, 8},
  read := ⟨[
    ({2, 3, 4, 5, 6}, 1),
    ({9, 10, 11, 12, 13}, 1),
    ({14, 15, 16, 17, 18}, 1),
    ({19, 20, 21, 22, 23}, 1)], 4⟩,
  write := ⟨[
    ({1, 4, 7, 12, 16, 20}, 1),
    ({1, 5, 9, 13, 17, 21}, 1),
    ({2, 6, 10, 14, 18, 22}, 1),
    ({3, 7, 11, 15, 19, 23}, 1)], 4⟩ }

theorem certificate_5_8_valid : certificate_5_8.Valid 24 5 := by decide +kernel

#print axioms certificate_5_8_valid
end QuorumAudit.MixedCircle
