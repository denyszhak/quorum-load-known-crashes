import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_1 : CircleCertificate := {
  failed := {0, 1},
  read := ⟨[
    ({4, 5, 6, 7, 8}, 4),
    ({9, 10, 11, 12, 13}, 3),
    ({14, 15, 16, 17, 18}, 2),
    ({7, 8, 9, 10, 11}, 2),
    ({12, 13, 14, 15, 16}, 3),
    ({17, 18, 19, 20, 21}, 4)], 18⟩,
  write := ⟨[
    ({2, 4, 8, 13, 18, 22}, 3),
    ({2, 4, 9, 14, 19, 22}, 2),
    ({2, 5, 9, 14, 19, 22}, 2),
    ({2, 5, 10, 15, 19, 22}, 1),
    ({2, 5, 10, 15, 20, 22}, 1),
    ({3, 5, 10, 15, 20, 23}, 1),
    ({3, 6, 10, 15, 20, 23}, 1),
    ({3, 6, 11, 16, 20, 23}, 2),
    ({3, 6, 11, 16, 21, 23}, 2),
    ({3, 7, 12, 17, 21, 23}, 3)], 18⟩ }

theorem certificate_5_1_valid : certificate_5_1.Valid 24 5 := by decide +kernel

#print axioms certificate_5_1_valid
end QuorumAudit.MixedCircle
