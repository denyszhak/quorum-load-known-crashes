import GeneralFOptimal

namespace QuorumAudit.GeneralF
noncomputable section

theorem one_crash_four_servers : LoadFeasible 1 4 (1 / 4) (3 / 4) := by
  apply (arbitrary_f_exact_optimum 1 2 (by decide) (by decide) 4 rfl
    (1 / 4) (3 / 4) (by norm_num) (by norm_num [endpoint])).mpr
  norm_num [value]

theorem three_crash_forty_servers (a L : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 118) :
    LoadFeasible 3 40 a L ↔ (4 + 9 * a) / 37 ≤ L := by
  have h := arbitrary_f_exact_optimum 3 10 (by decide) (by decide) 40 rfl
    a L ha (by norm_num [endpoint]; exact ha1)
  norm_num [value] at h
  exact h

theorem zero_reads_still_feasible : LoadFeasible 3 40 0 (4 / 37) := by
  apply (three_crash_forty_servers 0 (4 / 37) (by norm_num) (by norm_num)).mpr
  norm_num

theorem too_low_load_rejected : ¬ LoadFeasible 3 40 (1 / 118) (13 / 118 - 1 / 10000) := by
  rw [three_crash_forty_servers (1 / 118) _ (by norm_num) (by norm_num)]
  norm_num

theorem oversized_block_rejected : (Circle.colors 3 0 4).card ≠ 4 := by decide

theorem missing_live_read_rejected :
    ¬ ∃ s : ZMod 9, Disjoint (Circle.arc 5 s) ({0, 4} : Finset (ZMod 9)) := by decide

#print axioms one_crash_four_servers
#print axioms three_crash_forty_servers
#print axioms zero_reads_still_feasible
#print axioms too_low_load_rejected
#print axioms oversized_block_rejected
#print axioms missing_live_read_rejected
#check arbitrary_f_exact_optimum
end
end QuorumAudit.GeneralF
