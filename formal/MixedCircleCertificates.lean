import MixedCircleLower
import FiniteRouting

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

def natArc (n r s : ℕ) : Finset ℕ :=
  (range r).image (fun j => (s + j) % n)

def natReads (n r : ℕ) : Finset (Finset ℕ) := (range n).image (natArc n r)
def mixedWrites (n r : ℕ) [NeZero n] : Finset (Finset (ZMod n)) :=
  rankedWrites n r r ∪ rankedWrites n r (r + 1)

theorem mixed_safe (r : ℕ) :
    ∀ R ∈ reads n r, ∀ W ∈ mixedWrites n r, (R ∩ W).Nonempty := by
  intro R hR W hW
  rcases mem_union.mp hW with h | h
  · exact ranked_safe r r R hR W h
  · exact ranked_safe r (r + 1) R hR W h

def circleDistribution (d : NatDistribution ℕ) : NatDistribution (ZMod n) :=
  ⟨d.entries.map (fun e => (e.1.image (fun i : ℕ => (i : ZMod n)), e.2)), d.scale⟩

theorem cast_natArc (r s : ℕ) :
    (natArc n r s).image (fun i : ℕ => (i : ZMod n)) = arc r (s : ZMod n) := by
  rw [natArc, image_image]
  apply image_congr
  intro j _
  simp

theorem cast_membership (q : Finset ℕ) (hq : q ⊆ range n) (i : ZMod n) :
    i ∈ q.image (fun j : ℕ => (j : ZMod n)) ↔ i.val ∈ q := by
  constructor
  · rintro hi
    obtain ⟨j, hj, he⟩ := mem_image.mp hi
    have hjn : j < n := mem_range.mp (hq hj)
    have hv : i.val = j := by rw [← he, ZMod.val_natCast, Nat.mod_eq_of_lt hjn]
    simpa [hv] using hj
  · intro hi
    exact mem_image.mpr ⟨i.val, hi, by simp⟩

theorem circleDistribution_degree (d : NatDistribution ℕ)
    (hU : ∀ e ∈ d.entries, e.1 ⊆ range n) (i : ZMod n) :
    (circleDistribution (n := n) d).degree i = d.degree i.val := by
  unfold NatDistribution.degree circleDistribution
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_apply]
  simp only [cast_membership e.1 (hU e he) i]

theorem circleDistribution_valid (d : NatDistribution ℕ) (F : Finset ℕ)
    (family : Finset (Finset (ZMod n))) (hF : F ⊆ range n)
    (hscale : 0 < d.scale) (hnorm : (d.entries.map Prod.snd).sum = d.scale)
    (hlegal : ∀ e ∈ d.entries,
      e.1.image (fun i : ℕ => (i : ZMod n)) ∈ family ∧ e.1 ⊆ range n \ F) :
    (circleDistribution (n := n) d).Valid family univ
      (F.image (fun i : ℕ => (i : ZMod n))) := by
  refine ⟨hscale, ?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    refine ⟨(hlegal a ha).1, ?_⟩
    intro i hi
    have hiq : i.val ∈ a.1 := (cast_membership a.1
      (fun j hj => (mem_sdiff.mp ((hlegal a ha).2 hj)).1) i).mp hi
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hif
    obtain ⟨j, hjF, hji⟩ := mem_image.mp hif
    have hjn : j < n := mem_range.mp (hF hjF)
    have hij : i.val = j := by rw [← hji, ZMod.val_natCast, Nat.mod_eq_of_lt hjn]
    exact (mem_sdiff.mp ((hlegal a ha).2 hiq)).2 (by simpa [hij] using hjF)
  · simpa [circleDistribution, List.map_map, Function.comp_def] using hnorm

structure CircleCertificate where
  failed : Finset ℕ
  read : NatDistribution ℕ
  write : NatDistribution ℕ

def CircleCertificate.Valid (n r : ℕ) (c : CircleCertificate) : Prop :=
  c.failed ⊆ range n ∧ c.failed.card = 2 ∧
  c.read.Valid (natReads n r) (range n) c.failed ∧
  0 < c.write.scale ∧
  (∀ e ∈ c.write.entries,
    e.1 ⊆ range n \ c.failed ∧ (e.1.card = r ∨ e.1.card = r + 1) ∧
      ∀ s ∈ range n, (natArc n r s ∩ e.1).Nonempty) ∧
  (c.write.entries.map Prod.snd).sum = c.write.scale ∧
  (∀ i ∈ range n,
    ((r - 2) * (r + 1)) *
      (c.read.degree i * c.write.scale + c.write.degree i * c.read.scale) ≤
    (2 * r - 1) * c.read.scale * c.write.scale)

instance (r : ℕ) (c : CircleCertificate) : Decidable (c.Valid n r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem CircleCertificate.sound (r : ℕ) (hr : 5 ≤ r)
    (c : CircleCertificate) (h : c.Valid n r) :
    ∃ read : Routing (reads n r) univ (c.failed.image (fun i : ℕ => (i : ZMod n))),
    ∃ write : Routing (mixedWrites n r) univ (c.failed.image (fun i : ℕ => (i : ZMod n))),
      ∀ i : ZMod n, combined read write (1 / 2) i ≤ cap r / 2 := by
  obtain ⟨hF, _, hR, hWp, hW, hWnorm, hload⟩ := h
  have hread : (circleDistribution (n := n) c.read).Valid (reads n r) univ
      (c.failed.image (fun i : ℕ => (i : ZMod n))) := by
    apply circleDistribution_valid c.read c.failed _ hF hR.1 hR.2.2
    intro e he
    obtain ⟨s, hs, hsq⟩ := mem_image.mp (hR.2.1 e he).1
    refine ⟨?_, (hR.2.1 e he).2⟩
    rw [← hsq, cast_natArc]
    exact mem_image.mpr ⟨(s : ZMod n), mem_univ _, rfl⟩
  have hwrite : (circleDistribution (n := n) c.write).Valid (mixedWrites n r) univ
      (c.failed.image (fun i : ℕ => (i : ZMod n))) := by
    apply circleDistribution_valid c.write c.failed _ hF hWp hWnorm
    intro e he
    refine ⟨?_, (hW e he).1⟩
    have hsub : e.1 ⊆ range n := fun i hi => (mem_sdiff.mp ((hW e he).1 hi)).1
    have hcard : (e.1.image (fun i : ℕ => (i : ZMod n))).card = e.1.card := by
      apply card_image_of_injOn
      intro i hi j hj hij
      exact cast_injective_below (mem_range.mp (hsub hi)) (mem_range.mp (hsub hj)) hij
    have hhit : ∀ s : ZMod n, (arc r s ∩ e.1.image (fun i : ℕ => (i : ZMod n))).Nonempty := by
      intro s
      obtain ⟨i, hi⟩ := (hW e he).2.2 s.val (mem_range.mpr (ZMod.val_lt s))
      refine ⟨(i : ZMod n), mem_inter.mpr ⟨?_, mem_image_of_mem _ (mem_inter.mp hi).2⟩⟩
      rw [← ZMod.natCast_zmod_val s, ← cast_natArc]
      exact mem_image_of_mem _ (mem_inter.mp hi).1
    have hbase : e.1.image (fun i : ℕ => (i : ZMod n)) ∈ writes n r :=
      mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), hhit⟩
    rcases (hW e he).2.1 with hc | hc
    · exact mem_union_left _ (mem_filter.mpr ⟨hbase, hcard.trans hc⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hbase, hcard.trans hc⟩)
  let read := (circleDistribution (n := n) c.read).toRouting _ _ _ hread
  let write := (circleDistribution (n := n) c.write).toRouting _ _ _ hwrite
  refine ⟨read, write, ?_⟩
  intro i
  unfold combined
  rw [NatDistribution.toRouting_incidence, NatDistribution.toRouting_incidence,
    circleDistribution_degree c.read (fun e he j hj => (mem_sdiff.mp ((hR.2.1 e he).2 hj)).1),
    circleDistribution_degree c.write (fun e he j hj => (mem_sdiff.mp ((hW e he).1 hj)).1)]
  change (1 / 2 : ℝ) * ((c.read.degree i.val : ℝ) / c.read.scale) +
    (1 - 1 / 2) * ((c.write.degree i.val : ℝ) / c.write.scale) ≤ cap r / 2
  have hRp : (0 : ℝ) < c.read.scale := by exact_mod_cast hR.1
  have hWpos : (0 : ℝ) < c.write.scale := by exact_mod_cast hWp
  have hd := den_pos r (by exact_mod_cast hr)
  have hb := hload i.val (mem_range.mpr (ZMod.val_lt i))
  have hbR : den r * ((c.read.degree i.val : ℝ) * c.write.scale +
      c.write.degree i.val * c.read.scale) ≤
      (2 * (r : ℝ) - 1) * c.read.scale * c.write.scale := by
    have hcast : (((r - 2) * (r + 1) : ℕ) : ℝ) = den r := by
      simp [den, Nat.cast_sub (by omega : 2 ≤ r)]
    have hbC : (((r - 2) * (r + 1) : ℕ) : ℝ) *
        ((c.read.degree i.val : ℝ) * c.write.scale + c.write.degree i.val * c.read.scale) ≤
        ((2 * r - 1 : ℕ) : ℝ) * c.read.scale * c.write.scale := by exact_mod_cast hb
    simpa [hcast, Nat.cast_sub (by omega : 1 ≤ 2 * r)] using hbC
  unfold cap
  apply (mul_le_mul_iff_of_pos_right (mul_pos hRp (mul_pos hWpos hd))).mp
  field_simp [ne_of_gt hRp, ne_of_gt hWpos, ne_of_gt hd]
  nlinarith

#print axioms CircleCertificate.sound
end
end QuorumAudit.MixedCircle
