import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_5 : CircleCertificate := {
  failed := {0, 5},
  read := ⟨[
    ({6, 7, 8, 9, 10}, 4),
    ({11, 12, 13, 14, 15}, 3),
    ({16, 17, 18, 19, 20}, 2),
    ({9, 10, 11, 12, 13}, 2),
    ({14, 15, 16, 17, 18}, 3),
    ({19, 20, 21, 22, 23}, 4)], 18⟩,
  write := ⟨[
    ({1, 3, 6, 10, 15, 20}, 3),
    ({1, 3, 6, 11, 16, 21}, 2),
    ({1, 3, 7, 11, 16, 21}, 2),
    ({1, 3, 7, 12, 17, 21}, 1),
    ({1, 3, 7, 12, 17, 22}, 1),
    ({2, 4, 7, 12, 17, 22}, 1),
    ({2, 4, 8, 12, 17, 22}, 1),
    ({2, 4, 8, 13, 18, 22}, 2),
    ({2, 4, 8, 13, 18, 23}, 2),
    ({2, 4, 9, 14, 19, 23}, 3)], 18⟩ }

theorem certificate_5_5_valid : certificate_5_5.Valid 24 5 := by decide +kernel

#print axioms certificate_5_5_valid
end QuorumAudit.MixedCircle
