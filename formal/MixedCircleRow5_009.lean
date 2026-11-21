import MixedCircleCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace QuorumAudit.MixedCircle

def certificate_5_9 : CircleCertificate := {
  failed := {0, 9},
  read := ⟨[
    ({1, 2, 3, 4, 5}, 6),
    ({4, 5, 6, 7, 8}, 6),
    ({10, 11, 12, 13, 14}, 7),
    ({15, 16, 17, 18, 19}, 5),
    ({14, 15, 16, 17, 18}, 5),
    ({19, 20, 21, 22, 23}, 7)], 36⟩,
  write := ⟨[
    ({1, 4, 8, 12, 16, 20}, 3),
    ({1, 4, 8, 12, 16, 21}, 3),
    ({1, 5, 8, 12, 17, 21}, 3),
    ({1, 5, 8, 13, 17, 21}, 3),
    ({2, 6, 10, 13, 17, 21}, 2),
    ({2, 6, 10, 13, 18, 22}, 6),
    ({2, 6, 10, 14, 18, 22}, 2),
    ({2, 6, 10, 14, 19, 22}, 1),
    ({2, 6, 11, 14, 19, 22}, 1),
    ({3, 7, 11, 14, 19, 22}, 1),
    ({3, 7, 11, 14, 19, 23}, 1),
    ({3, 7, 11, 15, 19, 23}, 2),
    ({3, 7, 11, 15, 20, 23}, 6),
    ({3, 7, 12, 16, 20, 23}, 2)], 36⟩ }

theorem certificate_5_9_valid : certificate_5_9.Valid 24 5 := by decide +kernel

#print axioms certificate_5_9_valid
end QuorumAudit.MixedCircle
