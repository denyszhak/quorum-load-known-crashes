import TwoCrashTransport
import Mathlib.Data.ZMod.Basic

namespace QuorumAudit.TwoCrash
noncomputable section
open Finset

theorem writeSet_explicit (n j : Nat) :
    writeSet n j = {j/2 % n, (j/2+(j%2+1))%n, (j/2+2*(j%2+1))%n} := by
  simp [writeSet, triple, List.range_succ, Nat.mul_comm]

theorem writes_subset (n : Nat) (hn : 0<n) :
    ∀ q∈writes n, q⊆range n := by
  intro q hq
  obtain ⟨j, _, rfl⟩ := mem_image.mp hq
  rw [writeSet_explicit]
  intro i hi
  simp only [mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> exact mem_range.mpr (Nat.mod_lt _ hn)

def rotation (n : Nat) [NeZero n] (d : ZMod n) (i : Nat) : Nat :=
  ((i : ZMod n)+d).val

theorem rotation_injective (n : Nat) [NeZero n] (d : ZMod n) :
    Set.InjOn (rotation n d) (range n) := by
  intro i hi j hj heq
  have he := ZMod.val_injective n heq
  have hc : (i : ZMod n)=(j : ZMod n) := add_right_cancel he
  have hv := congrArg ZMod.val hc
  simpa only [ZMod.val_natCast_of_lt (mem_range.mp hi),
    ZMod.val_natCast_of_lt (mem_range.mp hj)] using hv

theorem rotation_offset (n : Nat) [NeZero n] (d : ZMod n) (s t : Nat) :
    rotation n d ((s+t)%n) = (rotation n d s+t)%n := by
  calc
    _ = ((s : ZMod n)+d+(t : ZMod n)).val := by
      unfold rotation
      congr 1
      rw [ZMod.natCast_mod, Nat.cast_add]
      ac_rfl
    _ = ((rotation n d s+t : Nat) : ZMod n).val := by
      congr 1
      simp only [Nat.cast_add, rotation, ZMod.natCast_val, ZMod.cast_id]
    _ = _ := ZMod.val_natCast n _

theorem rotation_write (n : Nat) [NeZero n] (d : ZMod n) (j : Nat) :
    (writeSet n j).image (rotation n d) =
      writeSet n (2*rotation n d (j/2)+j%2) := by
  have hj : j%2<2 := Nat.mod_lt _ (by decide)
  have hs : (2*rotation n d (j/2)+j%2)/2=rotation n d (j/2) := by omega
  have he : (2*rotation n d (j/2)+j%2)%2=j%2 := by omega
  rw [writeSet_explicit, writeSet_explicit, hs, he]
  simp only [image_insert, image_singleton]
  have hzero := rotation_offset n d (j/2) 0
  simp only [Nat.add_zero] at hzero
  rw [hzero, rotation_offset, rotation_offset]

theorem rotation_writes_closed (n : Nat) [NeZero n] (d : ZMod n) :
    ∀ q∈writes n, q.image (rotation n d)∈writes n := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
  rw [rotation_write]
  apply mem_image_of_mem
  apply mem_range.mpr
  have hs : rotation n d (j/2)<n := ZMod.val_lt _
  have he : j%2<2 := Nat.mod_lt _ (by decide)
  omega

theorem rotation_inverse (n : Nat) [NeZero n] (d : ZMod n) (i : Nat) (hi : i<n) :
    rotation n (-d) (rotation n d i)=i := by
  unfold rotation
  rw [ZMod.natCast_val, ZMod.cast_id, add_neg_cancel_right]
  exact ZMod.val_natCast_of_lt hi

theorem rotation_universe (n : Nat) [NeZero n] (d : ZMod n) :
    (range n).image (rotation n d)=range n := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (ZMod.val_lt _)
  · intro hi
    refine mem_image.mpr ⟨rotation n (-d) i, mem_range.mpr (ZMod.val_lt _), ?_⟩
    simpa only [neg_neg] using rotation_inverse n (-d) i (mem_range.mp hi)

theorem image_inverse_on_universe (n : Nat) [NeZero n] (d : ZMod n)
    (q : Finset Nat) (hq : q⊆range n) :
    (q.image (rotation n d)).image (rotation n (-d))=q := by
  rw [image_image]
  have h : ∀ i∈q, rotation n (-d) (rotation n d i)=i :=
    fun i hi => rotation_inverse n d i (mem_range.mp (hq hi))
  calc
    _ = q.image (fun i => i) := image_congr h
    _ = q := image_id'

theorem rotation_writes (n : Nat) [NeZero n] (d : ZMod n) :
    (writes n).image (fun q => q.image (rotation n d))=writes n := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨q0, hq0, rfl⟩ := mem_image.mp hq
    exact rotation_writes_closed n d q0 hq0
  · intro q hq
    refine mem_image.mpr ⟨q.image (rotation n (-d)),
      rotation_writes_closed n (-d) q hq, ?_⟩
    simpa only [neg_neg] using image_inverse_on_universe n (-d) q
      (writes_subset n (NeZero.pos n) q hq)

theorem reads_subset (n k : Nat) : ∀ q∈reads n k, q⊆range n := by
  intro q hq
  exact mem_powerset.mp (mem_filter.mp hq).1

theorem rotation_reads_closed (n k : Nat) [NeZero n] (d : ZMod n) :
    ∀ q∈reads n k, q.image (rotation n d)∈reads n k := by
  intro q hq
  have hqV := reads_subset n k q hq
  refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_, ?_⟩
  · rw [← rotation_universe n d]
    exact image_subset_image hqV
  · have hc : (q.image (rotation n d)).card=q.card :=
      card_image_of_injOn (fun i hi j hj heq =>
        rotation_injective n d (hqV hi) (hqV hj) heq)
    rw [hc]
    exact (mem_filter.mp hq).2.1
  · intro w hw
    rw [← rotation_writes n d] at hw
    obtain ⟨w0, hw0, rfl⟩ := mem_image.mp hw
    obtain ⟨i, hi⟩ := (mem_filter.mp hq).2.2 w0 hw0
    exact ⟨rotation n d i, mem_inter.mpr
      ⟨mem_image_of_mem _ (mem_inter.mp hi).1,
        mem_image_of_mem _ (mem_inter.mp hi).2⟩⟩

theorem rotation_reads (n k : Nat) [NeZero n] (d : ZMod n) :
    (reads n k).image (fun q => q.image (rotation n d))=reads n k := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨q0, hq0, rfl⟩ := mem_image.mp hq
    exact rotation_reads_closed n k d q0 hq0
  · intro q hq
    refine mem_image.mpr ⟨q.image (rotation n (-d)),
      rotation_reads_closed n k (-d) q hq, ?_⟩
    simpa only [neg_neg] using image_inverse_on_universe n (-d) q
      (reads_subset n k q hq)

/-- Rotation preserves the SAME fixed cyclic families, not merely an
isomorphic replacement design. It also preserves the bound after mapping
the actual failure set. -/
theorem rotation_routes (n k : Nat) [NeZero n] (d : ZMod n)
    (F : Finset Nat) (hF : F⊆range n)
    (r : Routing (reads n k) (range n) F)
    (w : Routing (writes n) (range n) F)
    (a L : ℝ) (hL : ∀ i∈range n, combined r w a i≤L) :
    ∃ r' : Routing (reads n k) (range n) (F.image (rotation n d)),
    ∃ w' : Routing (writes n) (range n) (F.image (rotation n d)),
      ∀ i∈range n, combined r' w' a i≤L := by
  have rlive : ∀ q∈r.quorums,
      q.image (rotation n d)⊆range n\F.image (rotation n d) := by
    intro q hq
    have h := image_live _ _ q (rotation n d) hF (rotation_injective n d) (r.live q hq)
    rwa [rotation_universe] at h
  have wlive : ∀ q∈w.quorums,
      q.image (rotation n d)⊆range n\F.image (rotation n d) := by
    intro q hq
    have h := image_live _ _ q (rotation n d) hF (rotation_injective n d) (w.live q hq)
    rwa [rotation_universe] at h
  let r' := routing_from_indexed r.quorums (fun q => q.image (rotation n d)) r.p
    (reads n k) (range n) (F.image (rotation n d))
    (fun q hq => rotation_reads_closed n k d q (r.subset hq)) rlive r.nonnegative r.normalized
  let w' := routing_from_indexed w.quorums (fun q => q.image (rotation n d)) w.p
    (writes n) (range n) (F.image (rotation n d))
    (fun q hq => rotation_writes_closed n d q (w.subset hq)) wlive w.nonnegative w.normalized
  refine ⟨r',w',?_⟩
  intro i hi
  have him : i∈(range n).image (rotation n d) := by rwa [rotation_universe]
  exact imageRouting_bound r w (rotation n d) hF (rotation_injective n d) a L hL i him

#print axioms rotation_writes
#print axioms rotation_reads
#print axioms rotation_universe
#print axioms rotation_routes
end
end QuorumAudit.TwoCrash
