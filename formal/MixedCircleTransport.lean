import MixedCircleCertificates

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def translateEquiv (a : ZMod n) : ZMod n ≃ ZMod n where
  toFun := fun i => a + i
  invFun := fun i => -a + i
  left_inv := by intro i; dsimp; ring
  right_inv := by intro i; dsimp; ring

theorem translate_arc (r : ℕ) (a s : ZMod n) :
    (arc r s).image (translateEquiv a) = arc r (a + s) := by
  rw [arc, image_image]
  apply image_congr
  intro j _
  change a + (s + (j : ZMod n)) = (a + s) + (j : ZMod n)
  ring

theorem translate_reads (r : ℕ) (a : ZMod n) :
    ∀ q ∈ reads n r, q.image (translateEquiv a) ∈ reads n r := by
  intro q hq
  obtain ⟨s, _, rfl⟩ := mem_image.mp hq
  rw [translate_arc]
  exact mem_image.mpr ⟨a + s, mem_univ _, rfl⟩

theorem translate_mixed_writes (r : ℕ) (a : ZMod n) :
    ∀ q ∈ mixedWrites n r, q.image (translateEquiv a) ∈ mixedWrites n r := by
  intro q hq
  have hqbase : q ∈ writes n r := by
    rcases mem_union.mp hq with h | h <;> exact (mem_filter.mp h).1
  have hqcard : q.card = r ∨ q.card = r + 1 := by
    rcases mem_union.mp hq with h | h
    · exact Or.inl (mem_filter.mp h).2
    · exact Or.inr (mem_filter.mp h).2
  have hbase : q.image (translateEquiv a) ∈ writes n r := by
    refine mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩
    intro s
    obtain ⟨i, hi⟩ := (mem_filter.mp hqbase).2 (s - a)
    refine ⟨a + i, mem_inter.mpr ⟨?_, mem_image_of_mem _ (mem_inter.mp hi).2⟩⟩
    have hm := mem_image_of_mem (translateEquiv a) (mem_inter.mp hi).1
    rw [translate_arc] at hm
    have he : a + (s - a) = s := by ring
    change a + i ∈ arc r (a + (s - a)) at hm
    simpa only [he] using hm
  have hc : (q.image (translateEquiv a)).card = q.card := card_image_of_injective _ (translateEquiv a).injective
  rcases hqcard with h | h
  · exact mem_union_left _ (mem_filter.mpr ⟨hbase, hc.trans h⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hbase, hc.trans h⟩)

def relabelRoute {family : Finset (Finset (ZMod n))} {F : Finset (ZMod n)}
    (route : Routing family univ F) (e : ZMod n ≃ ZMod n)
    (hfamily : ∀ q ∈ family, q.image e ∈ family) :
    Routing family univ (F.image e) :=
  routing_from_indexed route.quorums (fun q => q.image e) route.p family univ (F.image e)
    (fun q hq => hfamily q (route.subset hq))
    (by
      intro q hq i hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro hf
      obtain ⟨k, hk, hkj⟩ := mem_image.mp hf
      have heq : k = j := e.injective hkj
      exact (mem_sdiff.mp (route.live q hq hj)).2 (heq ▸ hk))
    route.nonnegative route.normalized

theorem relabelRoute_incidence {family : Finset (Finset (ZMod n))} {F : Finset (ZMod n)}
    (route : Routing family univ F) (e : ZMod n ≃ ZMod n)
    (hfamily : ∀ q ∈ family, q.image e ∈ family) (i : ZMod n) :
    incidence (relabelRoute route e hfamily).quorums (relabelRoute route e hfamily).p (e i) =
      incidence route.quorums route.p i := by
  change incidence (route.quorums.image (fun q => q.image e))
    (mergedProbability route.quorums (fun q => q.image e) route.p) (e i) = _
  rw [merged_incidence]
  unfold incidence
  apply sum_congr rfl
  intro q _
  have hm : e i ∈ q.image e ↔ i ∈ q := by
    constructor
    · rintro h
      obtain ⟨j, hj, heq⟩ := mem_image.mp h
      exact e.injective heq ▸ hj
    · exact mem_image_of_mem e
  simp only [hm]

theorem canonical_failure_pair (F : Finset (ZMod n)) (hF : F.card = 2) :
    ∃ a : ZMod n, ∃ d ∈ Ico 1 (n / 2 + 1),
      F = ({0, (d : ZMod n)} : Finset (ZMod n)).image (translateEquiv a) := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hF
  have hz : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hp : 0 < (b - a).val := by
    by_contra h
    have he : b - a = 0 := by
      apply ZMod.val_injective
      simpa using (show (b - a).val = 0 by omega)
    exact hz he
  have hnval := ZMod.val_lt (b - a)
  by_cases hsmall : (b - a).val ≤ n / 2
  · refine ⟨a, (b - a).val, mem_Ico.mpr ⟨hp, by omega⟩, ?_⟩
    simp only [image_insert, image_singleton, translateEquiv, Equiv.coe_fn_mk,
      add_zero, ZMod.natCast_zmod_val]
    have he : a + (b - a) = b := by ring
    rw [he]
  · have hneg : (a - b).val = n - (b - a).val := by
      rw [show a - b = -(b - a) by ring, ZMod.neg_val, if_neg hz]
    refine ⟨b, (a - b).val, mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    simp only [image_insert, image_singleton, translateEquiv, Equiv.coe_fn_mk,
      add_zero, ZMod.natCast_zmod_val]
    have he : b + (a - b) = a := by ring
    rw [he, pair_comm]

theorem pair_upper_of_certificates (r : ℕ) (hr : 5 ≤ r)
    (certificates : List CircleCertificate)
    (hvalid : ∀ c ∈ certificates, c.Valid n r)
    (hcoverage : ∀ d ∈ Ico 1 (n / 2 + 1), ∃ c ∈ certificates, c.failed = {0, d})
    (F : Finset (ZMod n)) (hF : F.card = 2) :
    ∃ read : Routing (reads n r) univ F,
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i : ZMod n, combined read write (1 / 2) i ≤ cap r / 2 := by
  obtain ⟨a, d, hd, hFeq⟩ := canonical_failure_pair F hF
  obtain ⟨c, hc, hcF⟩ := hcoverage d hd
  have hs : ∃ read : Routing (reads n r) univ {0, (d : ZMod n)},
      ∃ write : Routing (mixedWrites n r) univ {0, (d : ZMod n)},
        ∀ i : ZMod n, combined read write (1 / 2) i ≤ cap r / 2 := by
    have hi : c.failed.image (fun i : ℕ => (i : ZMod n)) = {0, (d : ZMod n)} := by
      rw [hcF]
      simp
    have hcSound := c.sound r hr (hvalid c hc)
    rw [hi] at hcSound
    exact hcSound
  obtain ⟨read, write, hload⟩ := hs
  rw [hFeq]
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

theorem all_failures_upper_of_certificates (r : ℕ) (hr : 5 ≤ r)
    (hn : n + 1 = r * r) (certificates : List CircleCertificate)
    (hvalid : ∀ c ∈ certificates, c.Valid n r)
    (hcoverage : ∀ d ∈ Ico 1 (n / 2 + 1), ∃ c ∈ certificates, c.failed = {0, d})
    (F : Finset (ZMod n)) (hF : F.card ≤ 2) :
    ∃ read : Routing (reads n r) univ F,
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i : ZMod n, combined read write (1 / 2) i ≤ cap r / 2 := by
  obtain ⟨G, hFG, _, hGc⟩ := pad_failures univ F (subset_univ _) hF
    (by rw [card_univ, ZMod.card]; nlinarith)
  obtain ⟨read, write, h⟩ := pair_upper_of_certificates r hr certificates hvalid hcoverage G hGc
  exact ⟨unpad_routing read hFG, unpad_routing write hFG, h⟩

theorem balanced_fixed_read_lower (r : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (W : Finset (Finset (ZMod n))) (L : ℝ)
    (hsafe : ∀ q ∈ reads n r, ∀ w ∈ W, (q ∩ w).Nonempty)
    (hroutes : ∀ F : Finset (ZMod n), F.card ≤ 2 →
      ∃ read : Routing (reads n r) univ F, ∃ write : Routing W univ F,
        ∀ i ∈ univ \ F, combined read write (1 / 2) i ≤ L) : cap r / 2 ≤ L := by
  obtain ⟨read, write, hL⟩ := hroutes (bottleneckFailures (n := n) r)
    (by simp [bottleneckFailures]; exact card_insert_le _ _)
  have h := interval_read_family_lower_bound r hr hn W hsafe read write
    (1 / 2) L (by norm_num) (by norm_num) hL
  have he : (((r : ℝ) - 1 + 1 / 2) / den r) = cap r / 2 := by unfold cap; ring
  simpa only [he] using h

#print axioms canonical_failure_pair
#print axioms all_failures_upper_of_certificates
#print axioms balanced_fixed_read_lower
end
end QuorumAudit.MixedCircle
