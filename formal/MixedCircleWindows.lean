import MixedCircleCertificates
import MixedCircleProfiles

set_option maxHeartbeats 2000000

namespace QuorumAudit.MixedCircle
open Finset
open scoped BigOperators

def lineSum {α : Type*} [AddCommMonoid α] (x : ℕ → α) (s r : ℕ) : α :=
  ∑ j ∈ range r, x (s + j)

def cyclicSum {α : Type*} [AddCommMonoid α] (n : ℕ) (x : ℕ → α) (s r : ℕ) : α :=
  ∑ j ∈ range r, x ((s + j) % n)

theorem lineSum_add {α : Type*} [AddCommMonoid α] (x : ℕ → α) (s a b : ℕ) :
    lineSum x s (a + b) = lineSum x s a + lineSum x (s + a) b := by
  unfold lineSum
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [Nat.add_assoc]

theorem lineSum_split_zero {α : Type*} [AddCommMonoid α] (x : ℕ → α) (s r d : ℕ)
    (hs : s ≤ d) (hd : d < s + r) (hx : x d = 0) :
    lineSum x s r = lineSum x s (d - s) + lineSum x (d + 1) (r - (d - s) - 1) := by
  have hlen : (d - s) + (1 + (r - (d - s) - 1)) = r := by omega
  rw [← hlen, lineSum_add, lineSum_add]
  have he : s + (d - s) = d := by omega
  rw [he]
  simp [lineSum, hx]

theorem cyclicSum_nowrap {α : Type*} [AddCommMonoid α] (n : ℕ) (x : ℕ → α)
    (s r : ℕ) (h : s + r ≤ n) : cyclicSum n x s r = lineSum x s r := by
  unfold cyclicSum lineSum
  apply sum_congr rfl
  intro j hj
  rw [Nat.mod_eq_of_lt (by have := mem_range.mp hj; omega)]

theorem cyclicSum_wrap {α : Type*} [AddCommMonoid α] (n : ℕ) (x : ℕ → α)
    (s r : ℕ) (hs : s < n) (hr : r ≤ n) (hwrap : n < s + r) :
    cyclicSum n x s r = lineSum x s (n - s) + lineSum x 0 (r - (n - s)) := by
  have hlen : (n - s) + (r - (n - s)) = r := by omega
  unfold cyclicSum
  conv_lhs => rw [← hlen, sum_range_add]
  congr 1
  · unfold lineSum
    apply sum_congr rfl
    intro j hj
    rw [Nat.mod_eq_of_lt (by have := mem_range.mp hj; omega)]
  · unfold lineSum
    apply sum_congr rfl
    intro j hj
    have he : s + (n - s + j) = n + j := by omega
    have hjn : j < n := by have := mem_range.mp hj; omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hjn, Nat.zero_add]

theorem natArc_nowrap (n r s : ℕ) (h : s + r ≤ n) :
    natArc n r s = Ico s (s + r) := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := mem_image.mp hi
    have hjr := mem_range.mp hj
    rw [Nat.mod_eq_of_lt (by omega)] at he
    apply mem_Ico.mpr
    omega
  · intro hi
    have hlo := (mem_Ico.mp hi).1
    have hhi := (mem_Ico.mp hi).2
    exact mem_image.mpr ⟨i - s, mem_range.mpr (by omega), by
      rw [Nat.add_sub_of_le hlo, Nat.mod_eq_of_lt (by omega)]⟩

theorem natArc_wrap (n r s : ℕ) (hs : s < n) (hr : r ≤ n) (hwrap : n < s + r) :
    natArc n r s = Ico s n ∪ Ico 0 (s + r - n) := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := mem_image.mp hi
    have hjr := mem_range.mp hj
    by_cases hlin : s + j < n
    · rw [Nat.mod_eq_of_lt hlin] at he
      exact mem_union_left _ (mem_Ico.mpr ⟨by omega, by omega⟩)
    · have hsub : s + j - n < n := by omega
      rw [Nat.mod_eq_sub_mod (by omega : n ≤ s + j), Nat.mod_eq_of_lt hsub] at he
      exact mem_union_right _ (mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩)
  · rintro hi
    rcases mem_union.mp hi with hi | hi
    · have hlo := (mem_Ico.mp hi).1
      have hhi := (mem_Ico.mp hi).2
      exact mem_image.mpr ⟨i - s, mem_range.mpr (by omega), by
        rw [Nat.add_sub_of_le hlo, Nat.mod_eq_of_lt hhi]⟩
    · have hhi := (mem_Ico.mp hi).2
      refine mem_image.mpr ⟨n - s + i, mem_range.mpr (by omega), ?_⟩
      have he : s + (n - s + i) = n + i := by omega
      rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : i < n)]

theorem far_windows_bound {α : Type*} [AddCommMonoid α] [LE α]
    (n r d : ℕ) (x : ℕ → α) (N₀ N₁ : α)
    (hr : 0 < r) (hd : r < d) (hdr : d + r < n) (hx0 : x 0 = 0) (hxd : x d = 0)
    (hA : ∀ s, 1 ≤ s → s + r ≤ d → lineSum x s r ≤ N₀)
    (hB : ∀ s, d + 1 ≤ s → s + r ≤ n → lineSum x s r ≤ N₀)
    (hcross0 : ∀ ℓ ≤ r - 1,
      lineSum x (n - ℓ) ℓ + lineSum x 1 (r - 1 - ℓ) ≤ N₁)
    (hcrossd : ∀ ℓ ≤ r - 1,
      lineSum x (d - ℓ) ℓ + lineSum x (d + 1) (r - 1 - ℓ) ≤ N₁)
    (s : ℕ) (hs : s < n) :
    ((natArc n r s ∩ {0, d}).card = 0 ∧ cyclicSum n x s r ≤ N₀) ∨
    ((natArc n r s ∩ {0, d}).card = 1 ∧ cyclicSum n x s r ≤ N₁) := by
  by_cases hz : s = 0
  · subst s
    right
    have harc := natArc_nowrap n r 0 (by omega)
    have heF : natArc n r 0 ∩ {0, d} = {0} := by
      rw [harc]
      ext i
      simp only [mem_inter, mem_insert, mem_singleton, mem_Ico]
      omega
    refine ⟨by rw [heF]; simp, ?_⟩
    rw [cyclicSum_nowrap n x 0 r (by omega), lineSum_split_zero x 0 r 0 (by omega) (by omega) hx0]
    simpa [lineSum] using hcross0 0 (by omega)
  · by_cases hwrap : n < s + r
    · right
      have harc := natArc_wrap n r s hs (by omega) hwrap
      have heF : natArc n r s ∩ {0, d} = {0} := by
        rw [harc]
        ext i
        simp only [mem_inter, mem_insert, mem_singleton, mem_union, mem_Ico]
        omega
      refine ⟨by rw [heF]; simp, ?_⟩
      rw [cyclicSum_wrap n x s r hs (by omega) hwrap,
        lineSum_split_zero x 0 (r - (n - s)) 0 (by omega) (by omega) hx0]
      have he : n - (n - s) = s := by omega
      have hrlen : r - (n - s) - 1 = r - 1 - (n - s) := by omega
      simpa [lineSum, he, hrlen] using hcross0 (n - s) (by omega)
    · have hnowrap : s + r ≤ n := by omega
      rw [cyclicSum_nowrap n x s r hnowrap]
      by_cases hleft : s + r ≤ d
      · left
        have heF : natArc n r s ∩ {0, d} = ∅ := by
          rw [natArc_nowrap n r s hnowrap]
          ext i
          simp only [mem_inter, mem_insert, mem_singleton, mem_Ico, Finset.notMem_empty, iff_false]
          omega
        exact ⟨by rw [heF]; simp, hA s (by omega) hleft⟩
      · by_cases hright : d < s
        · left
          have heF : natArc n r s ∩ {0, d} = ∅ := by
            rw [natArc_nowrap n r s hnowrap]
            ext i
            simp only [mem_inter, mem_insert, mem_singleton, mem_Ico, Finset.notMem_empty, iff_false]
            omega
          exact ⟨by rw [heF]; simp, hB s (by omega) hnowrap⟩
        · right
          have heF : natArc n r s ∩ {0, d} = {d} := by
            rw [natArc_nowrap n r s hnowrap]
            ext i
            simp only [mem_inter, mem_insert, mem_singleton, mem_Ico]
            omega
          refine ⟨by rw [heF]; simp, ?_⟩
          rw [lineSum_split_zero x s r d (by omega) (by omega) hxd]
          have he : d - (d - s) = s := by omega
          have hlen : r - (d - s) - 1 = r - 1 - (d - s) := by omega
          simpa [he, hlen] using hcrossd (d - s) (by omega)

#print axioms lineSum_split_zero
#print axioms far_windows_bound
end QuorumAudit.MixedCircle
