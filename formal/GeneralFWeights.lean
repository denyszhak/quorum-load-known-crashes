import CircleFamilies
import GeneralFLower
import Mathlib.Data.Finset.Sum

namespace QuorumAudit.GeneralF
noncomputable section
open Finset
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

def uniformWeight (F : Finset ι) (q : ℕ) (i : ι) : ℕ := if i ∈ F then 0 else q
def compensationWeight (F R : Finset ι) (r : ℕ) (i : ι) : ℕ :=
  if i ∈ F then 0 else r - (if i ∈ R then 1 else 0)

theorem sum_after_failures (w : ι → ℕ) (A F : Finset ι) (hz : ∀ i ∈ F, w i = 0) :
    ∑ i ∈ A, w i = ∑ i ∈ A \ F, w i := by
  symm
  apply sum_subset sdiff_subset
  intro i hi hnot
  apply hz i
  by_contra hf
  exact hnot (mem_sdiff.mpr ⟨hi, hf⟩)

theorem uniform_sum (F A : Finset ι) (q : ℕ) :
    ∑ i ∈ A, uniformWeight F q i = (A \ F).card * q := by
  rw [sum_after_failures _ A F (by intro i hi; simp [uniformWeight, hi])]
  simp only [uniformWeight]
  calc
    (∑ i ∈ A \ F, if i ∈ F then 0 else q) = ∑ _i ∈ A \ F, q :=
      sum_congr rfl (fun i hi => ite_eq_right (mem_sdiff.mp hi).2)
    _ = _ := by simp

theorem compensation_sum (F R A : Finset ι) (r : ℕ) (hr : 1 ≤ r) (hR : R ⊆ A \ F) :
    ∑ i ∈ A, compensationWeight F R r i = (A \ F).card * r - R.card := by
  rw [sum_after_failures _ A F (by intro i hi; simp [compensationWeight, hi])]
  have heq : (∑ i ∈ A \ F, compensationWeight F R r i) =
      ∑ i ∈ A \ F, (r - if i ∈ R then 1 else 0) :=
    sum_congr rfl (fun i hi => by simp [compensationWeight, (mem_sdiff.mp hi).2])
  rw [heq, sum_tsub_distrib _ (by intro i hi; split_ifs <;> omega)]
  simp [inter_eq_right.mpr hR]

theorem compensation_window (F R J : Finset ι) (r : ℕ) :
    (J \ F).card * (r - 1) ≤ ∑ i ∈ J, compensationWeight F R r i := by
  rw [sum_after_failures _ J F (by intro i hi; simp [compensationWeight, hi])]
  calc
    (J \ F).card * (r - 1) = ∑ _i ∈ J \ F, (r - 1) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      simp only [compensationWeight, ite_eq_right (mem_sdiff.mp hi).2]
      split_ifs <;> omega

def mixed_route {R : Finset (Finset ι)} {U F : Finset ι}
    (r₁ r₂ : Routing R U F) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : Routing R U F :=
  routing_from_indexed (r₁.quorums.disjSum r₂.quorums) (Sum.elim id id)
    (Sum.elim (fun q => b * r₁.p q) (fun q => (1 - b) * r₂.p q)) R U F
    (by intro j hj; cases j with
        | inl q => exact r₁.subset (by simpa using hj)
        | inr q => exact r₂.subset (by simpa using hj))
    (by intro j hj; cases j with
        | inl q => exact r₁.live q (by simpa using hj)
        | inr q => exact r₂.live q (by simpa using hj))
    (by intro j hj; cases j with
        | inl q => exact mul_nonneg hb (r₁.nonnegative q (by simpa using hj))
        | inr q => exact mul_nonneg (by linarith) (r₂.nonnegative q (by simpa using hj)))
    (by rw [sum_disjSum]; simp only [Sum.elim_inl, Sum.elim_inr];
        rw [← mul_sum, ← mul_sum, r₁.normalized, r₂.normalized]; ring)

theorem mixed_incidence {R : Finset (Finset ι)} {U F : Finset ι}
    (r₁ r₂ : Routing R U F) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) (i : ι) :
    incidence (mixed_route r₁ r₂ b hb hb1).quorums (mixed_route r₁ r₂ b hb hb1).p i =
      b * incidence r₁.quorums r₁.p i + (1 - b) * incidence r₂.quorums r₂.p i := by
  change incidence ((r₁.quorums.disjSum r₂.quorums).image (Sum.elim id id))
    (mergedProbability (r₁.quorums.disjSum r₂.quorums) (Sum.elim id id)
      (Sum.elim (fun q => b * r₁.p q) (fun q => (1 - b) * r₂.p q))) i = _
  rw [merged_incidence, sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
  unfold incidence
  rw [mul_sum, mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intros <;> split_ifs <;> simp_all

#print axioms mixed_incidence
end
end QuorumAudit.GeneralF
