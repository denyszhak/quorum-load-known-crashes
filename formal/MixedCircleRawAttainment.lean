import MixedCircleStrides
import MixedCirclePairedReads

set_option maxHeartbeats 3000000

namespace QuorumAudit.MixedCircle
noncomputable section
open Finset Circle
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem raw_arc_sum (x : ℕ → ℕ) (r : ℕ) (hrn : r ≤ n) (s : ZMod n) :
    (∑ i ∈ arc r s, x i.val) = cyclicSum n x s.val r := by
  rw [sum_arc (fun i : ZMod n => x i.val) r hrn s]
  apply sum_congr rfl
  intro j _
  have he : s + (j : ZMod n) = ((s.val + j : ℕ) : ZMod n) := by simp
  rw [he, ZMod.val_natCast]

theorem raw_attains (r : ℕ) (hr : 5 ≤ r) (hn : n + 1 = r * r)
    (F : Finset (ZMod n)) (hF : F.card = 2)
    (read : Routing (reads n r) univ F) (x : ℕ → ℕ)
    (h μ C : ℕ) (hp : 0 < h)
    (hread : ∀ i, incidence read.quorums read.p i = (x i.val : ℝ) / h)
    (hmix : (μ : ℝ) = mixture r * h) (hcap : (C : ℝ) = cap r * h)
    (q : Finset (ZMod n)) (hq : q ∈ rankedWrites n r r) (hqlive : q ⊆ univ \ F)
    (hpoint : ∀ i < n, ((r - 2) * (r + 1)) * x i ≤ (r + 1) * h)
    (hwindow : ∀ s : ZMod n,
      cyclicSum n x s.val r + μ * (arc r s ∩ q).card + (h - μ) ≤
      C * (r - (arc r s ∩ F).card)) :
    ∃ write : Routing (mixedWrites n r) univ F,
      ∀ i ∈ univ \ F, combined read write (1 / 2) i = cap r / 2 := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have hpR : (0 : ℝ) < h := by exact_mod_cast hp
  have hd := den_pos (r : ℝ) hrR
  have hD : (((r - 2) * (r + 1) : ℕ) : ℝ) = den r := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ r)]
    simp [den]
  have hrn : r ≤ n := by nlinarith
  have hμle : μ ≤ h := by
    have hm := (parameters (r : ℝ) hrR).2.1
    have hh : (μ : ℝ) ≤ h := by nlinarith
    exact_mod_cast hh
  apply compensation_attains r hr hn F hF read (fun i => x i.val)
    h μ C hp hread hmix hcap q hq hqlive
  · intro i _
    rw [hread]
    have hh : den r * (x i.val : ℝ) ≤ ((r : ℝ) + 1) * h := by
      have hh := hpoint i.val (ZMod.val_lt i)
      have hhR : (((r - 2) * (r + 1) : ℕ) : ℝ) * (x i.val : ℝ) ≤
          ((r : ℝ) + 1) * h := by exact_mod_cast hh
      rwa [hD] at hhR
    apply (div_le_iff₀ hpR).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · intro s
    have hcard := card_sdiff_add_card_inter (arc r s) F
    rw [arc_card r hrn s] at hcard
    have hfle : (arc r s ∩ F).card ≤ r := by omega
    have hdif : (arc r s \ F).card = r - (arc r s ∩ F).card := by omega
    have hh : ((cyclicSum n x s.val r : ℕ) : ℝ) + μ * ((arc r s ∩ q).card : ℝ) +
        (h - μ : ℝ) ≤ (C : ℝ) * ((arc r s \ F).card : ℝ) := by
      have hw := hwindow s
      rw [← hdif] at hw
      have hh : ((cyclicSum n x s.val r + μ * (arc r s ∩ q).card + (h - μ) : ℕ) : ℝ) ≤
          ((C * (arc r s \ F).card : ℕ) : ℝ) := by exact_mod_cast hw
      push_cast [Nat.cast_sub hμle] at hh
      exact hh
    rw [hmix, hcap] at hh
    have hsum : (∑ i ∈ arc r s, incidence read.quorums read.p i) =
        ((cyclicSum n x s.val r : ℕ) : ℝ) / h := by
      simp_rw [hread]
      rw [← sum_div, ← Nat.cast_sum, raw_arc_sum x r hrn s]
    rw [hsum]
    have hhdiv := (div_le_div_iff_of_pos_right hpR).mpr hh
    convert hhdiv using 1 <;> field_simp <;> ring

#print axioms raw_arc_sum
#print axioms raw_attains

theorem twice_parameters (r : ℕ) (hr : 5 ≤ r) :
    (2 * (r - 5) : ℕ) = mixture r * (2 * (r - 2) * (r + 1) : ℕ) ∧
    (2 * (2 * r - 1) : ℕ) = cap r * (2 * (r - 2) * (r + 1) : ℕ) := by
  have hrR : (5 : ℝ) ≤ r := by exact_mod_cast hr
  have hd := ne_of_gt (den_pos (r : ℝ) hrR)
  push_cast [Nat.cast_sub (by omega : 5 ≤ r), Nat.cast_sub (by omega : 2 ≤ r),
    Nat.cast_sub (by omega : 1 ≤ 2 * r)]
  unfold mixture cap
  constructor <;> field_simp <;> unfold den <;> ring

theorem cast_pair_count (r d : ℕ) (hd : d < n) (s : ZMod n) :
    (arc r s ∩ {0, (d : ZMod n)}).card = (natArc n r s.val ∩ {0, d}).card := by
  have hA : natArc n r s.val ⊆ range n := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (Nat.mod_lt _ (NeZero.pos n))
  have hB : ({0, d} : Finset ℕ) ⊆ range n := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact mem_range.mpr (NeZero.pos n)
    · exact mem_range.mpr hd
  have he := cast_intersection (natArc n r s.val) {0, d} hA hB
  rw [cast_natArc, ZMod.natCast_zmod_val] at he
  simp only [image_insert, image_singleton, Nat.cast_zero] at he
  rw [← he]
  apply card_image_of_injOn
  intro i hi j hj hij
  exact cast_injective_below (mem_range.mp (hA (mem_inter.mp hi).1))
    (mem_range.mp (hA (mem_inter.mp hj).1)) hij

#print axioms twice_parameters
#print axioms cast_pair_count
end
end QuorumAudit.MixedCircle
