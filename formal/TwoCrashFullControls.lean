import TwoCrashOptimal

namespace QuorumAudit.TwoCrash
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem boundary_cut_rejected : ¬RationalCut base02 0 := by decide +kernel
theorem nonperiodic_cut_rejected : ¬RationalCut base02 9 := by decide +kernel
theorem missing_expansion_cut_rejected : ¬ExpansionReady {base02 with cuts:=[]} := by decide +kernel
theorem wrong_normalization_rejected : ¬RationalReady {base02 with scale:=3} := by decide +kernel

theorem eleven_endpoint : LoadFeasible 11 (3/13) (5/13) := by
  apply (two_crash_exact_optimum 3 (by omega) (3/13) (5/13)
    (by norm_num) (by norm_num [critical])).mpr
  norm_num [target]

theorem zero_read_fraction (k : Nat) (hk : 3≤k) :
    LoadFeasible (3*k+2) 0 (1/(k:ℝ)) := by
  have hkR : (3:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (k:ℝ)≠0 := by linarith
  apply (two_crash_exact_optimum k hk 0 (1/(k:ℝ)) (by rfl)
    (by unfold critical; positivity)).mpr
  unfold target
  field_simp
  norm_num

#print axioms boundary_cut_rejected
#print axioms nonperiodic_cut_rejected
#print axioms missing_expansion_cut_rejected
#print axioms wrong_normalization_rejected
#print axioms eleven_endpoint
#print axioms zero_read_fraction
end QuorumAudit.TwoCrash
