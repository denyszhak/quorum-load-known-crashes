import MixedCircleBufferedRouting
import MixedCircleCloseRouting
import MixedCircleOverlapRouting
import MixedCircleFinite
import MixedCircleResidues

set_option maxHeartbeats 4000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem equal_routes_upper (r : ℕ) (hr : 5 ≤ r) (F : Finset (ZMod n))
    (read : Routing (reads n r) univ F) (write : Routing (mixedWrites n r) univ F)
    (he : ∀ i ∈ univ \ F, combined read write (1 / 2) i = cap r / 2) :
    ∀ i, combined read write (1 / 2) i ≤ cap r / 2 := by
  intro i
  by_cases hi : i ∈ F
  · unfold combined
    rw [failed_incidence_zero read i hi, failed_incidence_zero write i hi]
    have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
    have hc : 0 ≤ cap r := div_nonneg (by linarith) (le_of_lt (den_pos r hrR))
    nlinarith
  · exact (he i (mem_sdiff.mpr ⟨mem_univ _, hi⟩)).le

theorem translate_upper (r : ℕ) (F : Finset (ZMod n))
    (read : Routing (reads n r) univ F) (write : Routing (mixedWrites n r) univ F)
    (hload : ∀ i, combined read write (1 / 2) i ≤ cap r / 2) (a : ZMod n) :
    ∃ read' : Routing (reads n r) univ (F.image (translateEquiv a)),
    ∃ write' : Routing (mixedWrites n r) univ (F.image (translateEquiv a)),
      ∀ i, combined read' write' (1 / 2) i ≤ cap r / 2 := by
  let read' := relabelRoute read (translateEquiv a) (translate_reads r a)
  let write' := relabelRoute write (translateEquiv a) (translate_mixed_writes r a)
  refine ⟨read', write', ?_⟩
  intro i
  have hbound := hload ((translateEquiv a).symm i)
  have hincR := relabelRoute_incidence read (translateEquiv a) (translate_reads r a)
    ((translateEquiv a).symm i)
  have hincW := relabelRoute_incidence write (translateEquiv a) (translate_mixed_writes r a)
    ((translateEquiv a).symm i)
  simp only [Equiv.apply_symm_apply] at hincR hincW
  unfold combined at hbound ⊢
  change (1 / 2 : ℝ) * incidence read'.quorums read'.p i +
    (1 - 1 / 2) * incidence write'.quorums write'.p i ≤ _
  rw [hincR, hincW]
  exact hbound

theorem canonical_upper (r d : ℕ) (hr : 10 ≤ r) (hn : n + 1 = r * r)
    (hd : 1 ≤ d) (hdhalf : d ≤ n / 2) :
    ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
    ∃ write : Routing (mixedWrites n r) univ {0, (d : ZMod n)},
      ∀ i, combined read write (1 / 2) i ≤ cap r / 2 := by
  by_cases hclose : d ≤ r
  · let a := (r - d) / 2
    have ha0 : 2 * a ≤ r - d := by dsimp [a]; omega
    have ha1 : r - d ≤ 2 * a + 1 := by dsimp [a]; omega
    obtain ⟨read, write, he⟩ := close_attains (n := n) r a d (by omega) hn ⟨hd, hclose⟩ ha0 ha1
    have hu := equal_routes_upper r (by omega) _ read write he
    have ht := translate_upper r _ read write hu (-(a : ZMod n))
    have hF : ({(a : ZMod n), ((a + d : ℕ) : ZMod n)} : Finset (ZMod n)).image
        (translateEquiv (-(a : ZMod n))) = {0, (d : ZMod n)} := by
      simp [translateEquiv, Nat.cast_add]
    rwa [hF] at ht
  · let LA := d - 1
    let LB := n - d - 1
    let kA := LA / r
    let kB := LB / r
    let tA := LA % r
    let tB := LB % r
    have hlarge : 2 * r < n := by nlinarith
    have hdlt : d < n := by omega
    have hLA : r ≤ LA := by dsimp [LA]; omega
    have hLB : r ≤ LB := by dsimp [LB]; omega
    have hkA : 0 < kA := Nat.div_pos hLA (by omega)
    have hkB : 0 < kB := Nat.div_pos hLB (by omega)
    have htA : tA < r := Nat.mod_lt _ (by omega)
    have htB : tB < r := Nat.mod_lt _ (by omega)
    have hdivA : kA * r + tA = LA := by simpa [kA, tA, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div LA r
    have hdivB : kB * r + tB = LB := by simpa [kB, tB, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div LB r
    have hA : 1 + kA * r + tA = d := by dsimp [LA] at hdivA; omega
    have hB : d + 1 + kB * r + tB = n := by dsimp [LB] at hdivB; omega
    have hr1 : r - 1 + 1 = r := by omega
    have hr3 : r - 3 + 3 = r := by omega
    have hsum : (kA + kB) * r + (tA + tB) = (r - 1) * r + (r - 3) := by
      nlinarith only [hA, hB, hn, hr1, hr3]
    have hc := live_arc_remainders r kA kB tA tB hr htA htB hsum
    rcases hc with ⟨hT, hK⟩ | ⟨hT, hK, hδA0, hδA1, hδB0, hδB1⟩
    · obtain ⟨read, write, he⟩ := buffered_attains (n := n) r d kA kB tA tB hr hn hkA hkB hA hB hK hT
      exact ⟨read, write, equal_routes_upper r (by omega) _ read write he⟩
    · have hAB : LA ≤ LB := by dsimp [LA, LB]; omega
      have hkle : kA ≤ kB := Nat.div_le_div_right hAB
      have hA' : 1 + ((kA + 1) * r - (r - tA)) = d := by
        have hp : (kA + 1) * r = kA * r + r := by ring
        omega
      have hB' : d + 1 + ((kB + 1) * r - (r - tB)) = n := by
        have hp : (kB + 1) * r = kB * r + r := by ring
        omega
      obtain ⟨read, write, he⟩ := overlap_attains (n := n) r (kA + 1) (kB + 1) (r - tA) (r - tB) d
        (by omega) hn (by omega) (by omega) hK (by omega) ⟨hδA0, hδA1⟩ ⟨hδB0, hδB1⟩ hA' hB'
      exact ⟨read, write, equal_routes_upper r (by omega) _ read write he⟩

theorem symbolic_pair_upper (r : ℕ) (hr : 10 ≤ r) (hn : n + 1 = r * r)
    (F : Finset (ZMod n)) (hF : F.card = 2) :
    ∃ read : Routing (reads n r) univ F,
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i, combined read write (1 / 2) i ≤ cap r / 2 := by
  obtain ⟨a, d, hd, hFeq⟩ := canonical_failure_pair F hF
  have hdp := mem_Ico.mp hd
  obtain ⟨read, write, hu⟩ := canonical_upper r d hr hn hdp.1 (by omega)
  rw [hFeq]
  exact translate_upper r _ read write hu a

theorem balanced_interval_upper (r : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (F : Finset (ZMod n)) (hF : F.card ≤ 2) :
    ∃ read : Routing (reads n r) univ F,
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i, combined read write (1 / 2) i ≤ cap r / 2 := by
  by_cases hsmall : r ≤ 9
  · exact finite_interval_upper r hr hsmall hn F hF
  · obtain ⟨G, hFG, _, hGc⟩ := pad_failures univ F (subset_univ _) hF
      (by rw [card_univ, ZMod.card]; nlinarith)
    obtain ⟨read, write, hu⟩ := symbolic_pair_upper r (by omega) hn G hGc
    exact ⟨unpad_routing read hFG, unpad_routing write hFG, hu⟩

theorem balanced_interval_exact (r : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r) :
    (∀ q ∈ reads n r, ∀ w ∈ mixedWrites n r, (q ∩ w).Nonempty) ∧
    (∀ F : Finset (ZMod n), F.card ≤ 2 →
      ∃ read : Routing (reads n r) univ F,
      ∃ write : Routing (mixedWrites n r) univ F,
        ∀ i, combined read write (1 / 2) i ≤ cap r / 2) ∧
    (∀ W : Finset (Finset (ZMod n)), ∀ L : ℝ,
      (∀ q ∈ reads n r, ∀ w ∈ W, (q ∩ w).Nonempty) →
      (∀ F : Finset (ZMod n), F.card ≤ 2 →
        ∃ read : Routing (reads n r) univ F,
        ∃ write : Routing W univ F,
          ∀ i ∈ univ \ F, combined read write (1 / 2) i ≤ L) → cap r / 2 ≤ L) := by
  exact ⟨mixed_safe r, balanced_interval_upper r hr hn,
    fun W L hs h => balanced_fixed_read_lower r hr hn W L hs h⟩

#print axioms live_arc_remainders
#print axioms canonical_upper
#print axioms balanced_interval_upper
#print axioms balanced_interval_exact
#check balanced_interval_exact
end
end QuorumAudit.MixedCircle
