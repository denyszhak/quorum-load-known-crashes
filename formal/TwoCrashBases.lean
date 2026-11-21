import TwoCrashWitness
import Compression

namespace QuorumAudit
namespace TwoCrash
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem base00_semantic : Valid base00 := by decide +kernel

theorem base01_semantic : Valid base01 := by decide +kernel

theorem base02_semantic : Valid base02 := by decide +kernel

theorem base03_semantic : Valid base03 := by decide +kernel

theorem base04_semantic : Valid base04 := by decide +kernel

theorem base05_semantic : Valid base05 := by decide +kernel

theorem base06_semantic : Valid base06 := by decide +kernel

theorem base07_semantic : Valid base07 := by decide +kernel

theorem base08_semantic : Valid base08 := by decide +kernel

theorem base09_semantic : Valid base09 := by decide +kernel

theorem base10_semantic : Valid base10 := by decide +kernel

theorem base11_semantic : Valid base11 := by decide +kernel

theorem base12_semantic : Valid base12 := by decide +kernel

theorem base13_semantic : Valid base13 := by decide +kernel

theorem base14_semantic : Valid base14 := by decide +kernel

theorem base15_semantic : Valid base15 := by decide +kernel

theorem base16_semantic : Valid base16 := by decide +kernel

theorem base17_semantic : Valid base17 := by decide +kernel

theorem base18_semantic : Valid base18 := by decide +kernel

theorem base19_semantic : Valid base19 := by decide +kernel

theorem base20_semantic : Valid base20 := by decide +kernel

theorem base21_semantic : Valid base21 := by decide +kernel

theorem base22_semantic : Valid base22 := by decide +kernel

theorem base23_semantic : Valid base23 := by decide +kernel

theorem base24_semantic : Valid base24 := by decide +kernel

theorem base25_semantic : Valid base25 := by decide +kernel

theorem base26_semantic : Valid base26 := by decide +kernel

theorem base27_semantic : Valid base27 := by decide +kernel

theorem base28_semantic : Valid base28 := by decide +kernel

theorem base29_semantic : Valid base29 := by decide +kernel

theorem base30_semantic : Valid base30 := by decide +kernel

theorem base31_semantic : Valid base31 := by decide +kernel

theorem base32_semantic : Valid base32 := by decide +kernel

theorem base33_semantic : Valid base33 := by decide +kernel

theorem base34_semantic : Valid base34 := by decide +kernel

theorem base35_semantic : Valid base35 := by decide +kernel

theorem base36_semantic : Valid base36 := by decide +kernel

theorem base37_semantic : Valid base37 := by decide +kernel

theorem base38_semantic : Valid base38 := by decide +kernel

theorem base39_semantic : Valid base39 := by decide +kernel

theorem base40_semantic : Valid base40 := by decide +kernel

theorem base41_semantic : Valid base41 := by decide +kernel

theorem base42_semantic : Valid base42 := by decide +kernel

theorem base43_semantic : Valid base43 := by decide +kernel

theorem base44_semantic : Valid base44 := by decide +kernel

theorem base45_semantic : Valid base45 := by decide +kernel

theorem base46_semantic : Valid base46 := by decide +kernel

theorem base47_semantic : Valid base47 := by decide +kernel

theorem base48_semantic : Valid base48 := by decide +kernel

theorem base49_semantic : Valid base49 := by decide +kernel

theorem all_bases_semantic : ∀ g ∈ bases, Valid g := by
  intro g hg
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49
  · subst g; exact base00_semantic
  · subst g; exact base01_semantic
  · subst g; exact base02_semantic
  · subst g; exact base03_semantic
  · subst g; exact base04_semantic
  · subst g; exact base05_semantic
  · subst g; exact base06_semantic
  · subst g; exact base07_semantic
  · subst g; exact base08_semantic
  · subst g; exact base09_semantic
  · subst g; exact base10_semantic
  · subst g; exact base11_semantic
  · subst g; exact base12_semantic
  · subst g; exact base13_semantic
  · subst g; exact base14_semantic
  · subst g; exact base15_semantic
  · subst g; exact base16_semantic
  · subst g; exact base17_semantic
  · subst g; exact base18_semantic
  · subst g; exact base19_semantic
  · subst g; exact base20_semantic
  · subst g; exact base21_semantic
  · subst g; exact base22_semantic
  · subst g; exact base23_semantic
  · subst g; exact base24_semantic
  · subst g; exact base25_semantic
  · subst g; exact base26_semantic
  · subst g; exact base27_semantic
  · subst g; exact base28_semantic
  · subst g; exact base29_semantic
  · subst g; exact base30_semantic
  · subst g; exact base31_semantic
  · subst g; exact base32_semantic
  · subst g; exact base33_semantic
  · subst g; exact base34_semantic
  · subst g; exact base35_semantic
  · subst g; exact base36_semantic
  · subst g; exact base37_semantic
  · subst g; exact base38_semantic
  · subst g; exact base39_semantic
  · subst g; exact base40_semantic
  · subst g; exact base41_semantic
  · subst g; exact base42_semantic
  · subst g; exact base43_semantic
  · subst g; exact base44_semantic
  · subst g; exact base45_semantic
  · subst g; exact base46_semantic
  · subst g; exact base47_semantic
  · subst g; exact base48_semantic
  · subst g; exact base49_semantic

/-- Compression selects an actual semantic witness, rather than merely a
Boolean check, for every possible pair of healthy arc lengths. -/
theorem semantic_base_for_every_pair (A B k : Nat) (hk : 3 ≤ k) (hs : A+B=3*k) :
    ∃ g ∈ bases,
      g.a = min (compressArc A) (compressArc B) ∧
      g.b = max (compressArc A) (compressArc B) ∧ Valid g := by
  obtain ⟨g, hg, ha, hb, _⟩ := checked_base_for_every_pair A B k hk hs
  exact ⟨g, hg, ha, hb, all_bases_semantic g hg⟩

/-- Unconditional real routing for every one of the fifty base witnesses,
with all real read shares in its stated interval. -/
theorem every_base_routes (g : Gadget) (hg : g ∈ bases) (a : ℝ)
    (ha : 0 ≤ a) (haReg : a ≤ critical (rankParameter g)) :
    ∃ r : Routing (reads (nodes g) (rankParameter g)) (range (nodes g)) (failures g),
    ∃ w : Routing (writes (nodes g)) (range (nodes g)) (failures g),
      ∀ i ∈ range (nodes g), combined r w a i ≤ target (rankParameter g) a :=
  sound g (all_bases_semantic g hg) a ha haReg

#print axioms all_bases_semantic
#print axioms semantic_base_for_every_pair
#print axioms every_base_routes
end TwoCrash
end QuorumAudit
