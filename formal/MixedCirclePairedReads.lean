import MixedCircleWindows
import MixedCircleCompensation

set_option maxHeartbeats 3000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem list_range_sum {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    ((List.range m).map f).sum = (range m).sum f := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, sum_range_succ, ih]

def blockInterval (b r j : ℕ) : Finset ℕ := Ico (b + j * r) (b + (j + 1) * r)

def pairedReadDistribution (r k δ b : ℕ) : NatDistribution ℕ := {
  entries := ((List.range (k - 1)).map (fun j =>
      (blockInterval b r j, 2 * (k - 1 - j) + (r - k + 1)))) ++
    ((List.range (k - 1)).map (fun j =>
      (blockInterval (b + (r - δ)) r j, 2 * (j + 1) + (r - k + 1))))
  scale := 2 * (k - 1) * (r + 1) }

def placedMass (r k δ b i : ℕ) : ℕ := if b ≤ i then pairedMass r k δ (i - b) else 0

theorem tileMass_shift (b a r k i : ℕ) (w : ℕ → ℕ) :
    tileMass (b + a) r k w i = if b ≤ i then tileMass a r k w (i - b) else 0 := by
  unfold tileMass
  by_cases hbi : b ≤ i
  · rw [ite_eq_left hbi]
    apply sum_congr rfl
    intro j _
    have he : (b + a + j * r ≤ i ∧ i < b + a + (j + 1) * r) ↔
        (a + j * r ≤ i - b ∧ i - b < a + (j + 1) * r) := by omega
    simp only [he]
  · rw [ite_eq_right hbi]
    apply sum_eq_zero
    intro j _
    exact ite_eq_right (by omega)

theorem pairedReadDistribution_degree (r k δ b i : ℕ) :
    (pairedReadDistribution r k δ b).degree i = placedMass r k δ b i := by
  unfold NatDistribution.degree pairedReadDistribution
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_apply]
  rw [list_range_sum, list_range_sum]
  simp only [Function.comp_def, blockInterval, mem_Ico]
  change tileMass b r (k - 1) (fun j => 2 * (k - 1 - j) + (r - k + 1)) i +
    tileMass (b + (r - δ)) r (k - 1) (fun j => 2 * (j + 1) + (r - k + 1)) i = _
  have hs1 := tileMass_shift b 0 r (k - 1) i (fun j => 2 * (k - 1 - j) + (r - k + 1))
  simp only [Nat.add_zero] at hs1
  rw [hs1, tileMass_shift]
  by_cases hbi : b ≤ i <;> simp [placedMass, hbi, pairedMass]

theorem pairedReadDistribution_normalized (r k δ b : ℕ) (hk : 2 ≤ k) (hkr : k ≤ r) :
    ((pairedReadDistribution r k δ b).entries.map Prod.snd).sum =
      (pairedReadDistribution r k δ b).scale := by
  unfold pairedReadDistribution
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_apply]
  rw [list_range_sum, list_range_sum]
  exact paired_weights_normalized r k hk hkr

theorem blockInterval_member (r b j : ℕ) (hr : 0 < r)
    (hroom : b + (j + 1) * r ≤ n) : blockInterval b r j ∈ natReads n r := by
  have he : b + j * r + r = b + (j + 1) * r := by ring
  apply mem_image.mpr
  refine ⟨b + j * r, mem_range.mpr (by omega), ?_⟩
  rw [natArc_nowrap n r (b + j * r) (by omega), he]
  rfl

theorem pairedReadDistribution_valid (r k δ b : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (F : Finset ℕ)
    (hroom : b + (k * r - δ) ≤ n)
    (hlive : ∀ i ∈ Ico b (b + (k * r - δ)), i ∉ F) :
    (pairedReadDistribution r k δ b).Valid (natReads n r) (range n) F := by
  have hprod : (k - 1) * r + r = k * r := by
    calc _ = (k - 1 + 1) * r := by ring
         _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  refine ⟨by
    change 0 < 2 * (k - 1) * (r + 1)
    exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega),
    ?_, pairedReadDistribution_normalized r k δ b hk hkr⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hjk : j + 1 ≤ k - 1 := by have := List.mem_range.mp hj; omega
    have hmul : (j + 1) * r ≤ (k - 1) * r := Nat.mul_le_mul_right r hjk
    have heRoom : b + (j + 1) * r ≤ n := by omega
    refine ⟨blockInterval_member r b j (by omega) heRoom, ?_⟩
    intro i hi
    have hlo := (mem_Ico.mp hi).1
    have hhi := (mem_Ico.mp hi).2
    refine mem_sdiff.mpr ⟨mem_range.mpr (by omega), ?_⟩
    apply hlive i
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
    have hjk : j + 1 ≤ k - 1 := by have := List.mem_range.mp hj; omega
    have hmul : (j + 1) * r ≤ (k - 1) * r := Nat.mul_le_mul_right r hjk
    have heRoom : b + (r - δ) + (j + 1) * r ≤ n := by omega
    refine ⟨blockInterval_member r (b + (r - δ)) j (by omega) heRoom, ?_⟩
    intro i hi
    have hlo := (mem_Ico.mp hi).1
    have hhi := (mem_Ico.mp hi).2
    refine mem_sdiff.mpr ⟨mem_range.mpr (by omega), ?_⟩
    apply hlive i
    exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem nat_read_distribution_valid (r : ℕ) (d : NatDistribution ℕ) (F : Finset ℕ)
    (hF : F ⊆ range n) (h : d.Valid (natReads n r) (range n) F) :
    (circleDistribution (n := n) d).Valid (reads n r) univ
      (F.image (fun i : ℕ => (i : ZMod n))) := by
  apply circleDistribution_valid d F _ hF h.1 h.2.2
  intro e he
  obtain ⟨s, hs, hsq⟩ := mem_image.mp (h.2.1 e he).1
  refine ⟨?_, (h.2.1 e he).2⟩
  rw [← hsq, cast_natArc]
  exact mem_image.mpr ⟨(s : ZMod n), mem_univ _, rfl⟩

theorem paired_read_route (r k δ b : ℕ) (hr : 3 ≤ r) (hk : 2 ≤ k)
    (hkr : k ≤ r) (hδ : 1 ≤ δ ∧ δ ≤ 2) (F : Finset ℕ) (hF : F ⊆ range n)
    (hroom : b + (k * r - δ) ≤ n)
    (hlive : ∀ i ∈ Ico b (b + (k * r - δ)), i ∉ F) :
    ∃ read : Routing (reads n r) univ (F.image (fun i : ℕ => (i : ZMod n))),
      ∀ i : ZMod n, incidence read.quorums read.p i =
        (placedMass r k δ b i.val : ℝ) / (2 * (k - 1) * (r + 1) : ℕ) := by
  let d := pairedReadDistribution r k δ b
  have hd := pairedReadDistribution_valid r k δ b hr hk hkr hδ F hroom hlive
  have hc := nat_read_distribution_valid r d F hF hd
  let read := (circleDistribution (n := n) d).toRouting _ _ _ hc
  refine ⟨read, ?_⟩
  intro i
  rw [NatDistribution.toRouting_incidence,
    circleDistribution_degree d (fun e he j hj => (mem_sdiff.mp ((hd.2.1 e he).2 hj)).1),
    pairedReadDistribution_degree]
  rfl

#print axioms pairedReadDistribution_degree
#print axioms paired_read_route

def appendReadDistribution (a b : NatDistribution ℕ) : NatDistribution ℕ :=
  ⟨a.entries ++ b.entries, a.scale + b.scale⟩

theorem append_read_valid (r : ℕ) (F : Finset ℕ) (a b : NatDistribution ℕ)
    (ha : a.Valid (natReads n r) (range n) F) (hb : b.Valid (natReads n r) (range n) F) :
    (appendReadDistribution a b).Valid (natReads n r) (range n) F := by
  refine ⟨by change 0 < a.scale + b.scale; have := ha.1; omega, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact ha.2.1 e he
    · exact hb.2.1 e he
  · change ((a.entries ++ b.entries).map Prod.snd).sum = a.scale + b.scale
    rw [List.map_append, List.sum_append, ha.2.2, hb.2.2]

theorem append_read_degree (a b : NatDistribution ℕ) (i : ℕ) :
    (appendReadDistribution a b).degree i = a.degree i + b.degree i := by
  simp [NatDistribution.degree, appendReadDistribution, List.map_append, List.sum_append]

theorem read_distribution_route (r : ℕ) (d : NatDistribution ℕ) (F : Finset ℕ)
    (hF : F ⊆ range n) (h : d.Valid (natReads n r) (range n) F) :
    ∃ read : Routing (reads n r) univ (F.image (fun i : ℕ => (i : ZMod n))),
      ∀ i : ZMod n, incidence read.quorums read.p i = (d.degree i.val : ℝ) / d.scale := by
  have hc := nat_read_distribution_valid r d F hF h
  let read := (circleDistribution (n := n) d).toRouting _ _ _ hc
  refine ⟨read, ?_⟩
  intro i
  rw [NatDistribution.toRouting_incidence,
    circleDistribution_degree d (fun e he j hj => (mem_sdiff.mp ((h.2.1 e he).2 hj)).1)]
  rfl

#print axioms append_read_valid
#print axioms read_distribution_route
end
end QuorumAudit.MixedCircle
