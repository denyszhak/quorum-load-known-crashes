import GeneralFWeights
import CircleRanked
set_option maxHeartbeats 2000000

namespace QuorumAudit.GeneralF
noncomputable section
open Finset
open scoped BigOperators
open Circle

theorem exact_failures_attain (f k : ℕ) (hf : 1 ≤ f) (hk : f * f + 1 ≤ k)
    (n : ℕ) [NeZero n] (hn : n = (f + 1) * k)
    (F : Finset (ZMod n)) (hFc : F.card = f)
    (a : ℝ) (ha : 0 ≤ a) (hareg : a ≤ endpoint f k) :
    ∃ read : Routing (reads n (k + f)) univ F,
    ∃ write : Routing (rankedWrites n (k + f) (f + 1)) univ F,
      ∀ i ∈ univ \ F, combined read write a i = value f k a := by
  have hk2 : 2 ≤ k := by nlinarith
  have hfN : f < n := by rw [hn]; nlinarith
  have hrn : k + f ≤ n := by rw [hn]; nlinarith
  have hrp : 1 ≤ k + f := by omega
  have hroom : F.card * (k + f) < n := by rw [hFc, hn]; nlinarith
  obtain ⟨s, hs⟩ := live_arc (k + f) F hroom
  let R := arc (k + f) s
  have hRc : R.card = k + f := arc_card _ hrn _
  have hRlive : R ⊆ univ \ F := by
    intro i hi
    exact mem_sdiff.mpr ⟨mem_univ _, fun hiF => disjoint_left.mp hs hi hiF⟩
  let m := n - f
  let M := (k - 1) * (k + f)
  have hmp : 0 < m := by dsimp [m]; omega
  have hMp : 0 < M := Nat.mul_pos (by omega) (by omega)
  let _ : NeZero m := ⟨ne_of_gt hmp⟩
  let _ : NeZero M := ⟨ne_of_gt hMp⟩
  have hlc : (univ \ F : Finset (ZMod n)).card = m := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card, hFc]
  have hkm : k - 1 + 1 = k := by omega
  have hqmax : f + 1 ≤ m := by
    have : n - f + f = n := Nat.sub_add_cancel (le_of_lt hfN)
    dsimp [m]
    nlinarith
  have hrmax : k + f ≤ M := by dsimp [M]; nlinarith
  have hwindow : ∀ t : ZMod n, k ≤ (arc (k + f) t \ F).card := by
    intro t
    have hcard := card_sdiff_add_card_inter (arc (k + f) t) F
    have hle : (arc (k + f) t ∩ F).card ≤ f := by
      simpa [hFc] using card_le_card (inter_subset_right : arc (k + f) t ∩ F ⊆ F)
    rw [arc_card _ hrn] at hcard
    omega
  have hUtotal : (∑ i : ZMod n, uniformWeight F (f + 1) i) = (f + 1) * m := by
    rw [uniform_sum, hlc, mul_comm]
  obtain ⟨U, hU⟩ := ranked_sampled_routing (h := m) (uniformWeight F (f + 1)) F (k + f) (f + 1) hrn (by simpa [hFc] using hroom)
    hUtotal (by intro i; unfold uniformWeight; split_ifs <;> omega)
    (by intro i hi; simp [uniformWeight, hi]) (by
      intro t
      rw [uniform_sum]
      have hle := Nat.mul_le_mul_right (f + 1) (hwindow t)
      exact le_trans (Nat.sub_le n f) (le_trans (by nlinarith [hn] : n ≤ k * (f + 1)) hle))
  have hCtotal : (∑ i : ZMod n, compensationWeight F R (k + f) i) = (f + 1) * M := by
    rw [compensation_sum F R univ (k + f) hrp hRlive, hlc, hRc]
    have hprod : m * (k + f) = (f + 1) * M + (k + f) := by
      dsimp [m, M]
      have hnf : n - f + f = n := Nat.sub_add_cancel (le_of_lt hfN)
      nlinarith
    omega
  obtain ⟨C, hC⟩ := ranked_sampled_routing (h := M) (compensationWeight F R (k + f)) F (k + f) (f + 1) hrn (by simpa [hFc] using hroom)
    hCtotal (by intro i; unfold compensationWeight; split_ifs <;> omega)
    (by intro i hi; simp [compensationWeight, hi]) (by
      intro t
      apply le_trans _ (compensation_window F R (arc (k + f) t) (k + f))
      have hle := Nat.mul_le_mul_right (k + f - 1) (hwindow t)
      have hrsub : k + f - 1 + 1 = k + f := by omega
      dsimp [M]
      nlinarith)
  let read : Routing (reads n (k + f)) univ F := {
    quorums := {R}
    subset := by intro r hr; have he : r = R := mem_singleton.mp hr; rw [he]; exact mem_image.mpr ⟨s, mem_univ _, rfl⟩
    live := by intro r hr; simpa only [mem_singleton.mp hr] using hRlive
    p := fun _ => 1
    nonnegative := by intros; norm_num
    normalized := by simp }
  have hread : ∀ i, incidence read.quorums read.p i = if i ∈ R then 1 else 0 := by
    intro i
    change (∑ q ∈ {R}, if i ∈ q then (1 : ℝ) else 0) = _
    rw [sum_singleton]
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hmR : (m : ℝ) = ((f : ℝ) + 1) * k - f := by
    dsimp [m]
    rw [Nat.cast_sub (le_of_lt hfN), hn]
    push_cast
    ring
  have hMR : (M : ℝ) = ((k : ℝ) - 1) * (k + f) := by
    dsimp [M]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k)]
    push_cast
    ring
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmp
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hMp
  have ha1 : a < 1 := lt_of_le_of_lt hareg (endpoint_lt_one f k hf hk2)
  have hreg : a * ((M : ℝ) + 1) ≤ 1 := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < M + 1)).mp
    simpa [endpoint, hMR] using hareg
  let b := (1 - a * ((M : ℝ) + 1)) / (1 - a)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hb1 : b ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1 - a)).mpr
    nlinarith
  let write := mixed_route U C b hb hb1
  refine ⟨read, write, ?_⟩
  intro i hi
  have hiF := (mem_sdiff.mp hi).2
  have hUi : incidence U.quorums U.p i = ((f : ℝ) + 1) / m := by
    rw [hU]
    simp [uniformWeight, hiF]
  have hCi : incidence C.quorums C.p i = ((k : ℝ) + f - (if i ∈ R then 1 else 0)) / M := by
    rw [hC]
    simp only [compensationWeight, ite_eq_right hiF]
    split_ifs <;> rw [Nat.cast_sub (by omega)] <;> push_cast <;> ring
  unfold combined
  rw [hread, mixed_incidence, hUi, hCi]
  unfold value
  dsimp [b]
  rw [← hmR]
  field_simp [ne_of_gt hm0, ne_of_gt hM0, ne_of_gt (show 0 < 1 - a by linarith)]
  rw [hmR, hMR]
  ring

#print axioms exact_failures_attain
end
end QuorumAudit.GeneralF
