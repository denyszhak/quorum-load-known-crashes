import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_10 : CircleCertificate := {
  failed := {0, 10},
  read := ⟨[
    ({1, 2, 3, 4, 5}, 6),
    ({5, 6, 7, 8, 9}, 6),
    ({11, 12, 13, 14, 15}, 7),
    ({16, 17, 18, 19, 20}, 5),
    ({14, 15, 16, 17, 18}, 5),
    ({19, 20, 21, 22, 23}, 7)], 36⟩,
  write := ⟨[
    ({1, 4, 7, 11, 15, 20}, 3),
    ({1, 4, 7, 11, 16, 21}, 2),
    ({1, 4, 7, 12, 16, 21}, 1),
    ({1, 4, 8, 12, 16, 21}, 5),
    ({1, 4, 8, 12, 17, 21}, 1),
    ({2, 5, 8, 12, 17, 21}, 2),
    ({2, 5, 8, 12, 17, 22}, 2),
    ({2, 5, 8, 13, 17, 22}, 2),
    ({2, 6, 9, 13, 17, 22}, 1),
    ({2, 6, 9, 13, 18, 22}, 5),
    ({3, 6, 9, 13, 18, 22}, 1),
    ({3, 6, 9, 13, 18, 23}, 2),
    ({3, 6, 9, 14, 19, 23}, 3),
    ({3, 7, 11, 14, 19, 23}, 3),
    ({3, 7, 11, 15, 20, 23}, 3)], 36⟩ }

theorem certificate_5_10_valid : certificate_5_10.Valid 24 5 := by decide +kernel

#print axioms certificate_5_10_valid
end QuorumAudit.MixedCircle
