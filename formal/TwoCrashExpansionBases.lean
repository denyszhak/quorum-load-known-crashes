import TwoCrashRationalBases
namespace QuorumAudit.TwoCrash
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem base00_expansion_ready : ExpansionReady base00 := by decide +kernel
theorem base01_expansion_ready : ExpansionReady base01 := by decide +kernel
theorem base02_expansion_ready : ExpansionReady base02 := by decide +kernel
theorem base03_expansion_ready : ExpansionReady base03 := by decide +kernel
theorem base04_expansion_ready : ExpansionReady base04 := by decide +kernel
theorem base05_expansion_ready : ExpansionReady base05 := by decide +kernel
theorem base06_expansion_ready : ExpansionReady base06 := by decide +kernel
theorem base07_expansion_ready : ExpansionReady base07 := by decide +kernel
theorem base08_expansion_ready : ExpansionReady base08 := by decide +kernel
theorem base09_expansion_ready : ExpansionReady base09 := by decide +kernel
theorem base10_expansion_ready : ExpansionReady base10 := by decide +kernel
theorem base11_expansion_ready : ExpansionReady base11 := by decide +kernel
theorem base12_expansion_ready : ExpansionReady base12 := by decide +kernel
theorem base13_expansion_ready : ExpansionReady base13 := by decide +kernel
theorem base14_expansion_ready : ExpansionReady base14 := by decide +kernel
theorem base15_expansion_ready : ExpansionReady base15 := by decide +kernel
theorem base16_expansion_ready : ExpansionReady base16 := by decide +kernel
theorem base17_expansion_ready : ExpansionReady base17 := by decide +kernel
theorem base18_expansion_ready : ExpansionReady base18 := by decide +kernel
theorem base19_expansion_ready : ExpansionReady base19 := by decide +kernel
theorem base20_expansion_ready : ExpansionReady base20 := by decide +kernel
theorem base21_expansion_ready : ExpansionReady base21 := by decide +kernel
theorem base22_expansion_ready : ExpansionReady base22 := by decide +kernel
theorem base23_expansion_ready : ExpansionReady base23 := by decide +kernel
theorem base24_expansion_ready : ExpansionReady base24 := by decide +kernel
theorem base25_expansion_ready : ExpansionReady base25 := by decide +kernel
theorem base26_expansion_ready : ExpansionReady base26 := by decide +kernel
theorem base27_expansion_ready : ExpansionReady base27 := by decide +kernel
theorem base28_expansion_ready : ExpansionReady base28 := by decide +kernel
theorem base29_expansion_ready : ExpansionReady base29 := by decide +kernel
theorem base30_expansion_ready : ExpansionReady base30 := by decide +kernel
theorem base31_expansion_ready : ExpansionReady base31 := by decide +kernel
theorem base32_expansion_ready : ExpansionReady base32 := by decide +kernel
theorem base33_expansion_ready : ExpansionReady base33 := by decide +kernel
theorem base34_expansion_ready : ExpansionReady base34 := by decide +kernel
theorem base35_expansion_ready : ExpansionReady base35 := by decide +kernel
theorem base36_expansion_ready : ExpansionReady base36 := by decide +kernel
theorem base37_expansion_ready : ExpansionReady base37 := by decide +kernel
theorem base38_expansion_ready : ExpansionReady base38 := by decide +kernel
theorem base39_expansion_ready : ExpansionReady base39 := by decide +kernel
theorem base40_expansion_ready : ExpansionReady base40 := by decide +kernel
theorem base41_expansion_ready : ExpansionReady base41 := by decide +kernel
theorem base42_expansion_ready : ExpansionReady base42 := by decide +kernel
theorem base43_expansion_ready : ExpansionReady base43 := by decide +kernel
theorem base44_expansion_ready : ExpansionReady base44 := by decide +kernel
theorem base45_expansion_ready : ExpansionReady base45 := by decide +kernel
theorem base46_expansion_ready : ExpansionReady base46 := by decide +kernel
theorem base47_expansion_ready : ExpansionReady base47 := by decide +kernel
theorem base48_expansion_ready : ExpansionReady base48 := by decide +kernel
theorem base49_expansion_ready : ExpansionReady base49 := by decide +kernel

theorem all_bases_expansion_ready (g : Gadget) (hg : g∈bases) : ExpansionReady g := by
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h00 | h01 | h02 | h03 | h04 | h05 | h06 | h07 | h08 | h09 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49
  · subst g; exact base00_expansion_ready
  · subst g; exact base01_expansion_ready
  · subst g; exact base02_expansion_ready
  · subst g; exact base03_expansion_ready
  · subst g; exact base04_expansion_ready
  · subst g; exact base05_expansion_ready
  · subst g; exact base06_expansion_ready
  · subst g; exact base07_expansion_ready
  · subst g; exact base08_expansion_ready
  · subst g; exact base09_expansion_ready
  · subst g; exact base10_expansion_ready
  · subst g; exact base11_expansion_ready
  · subst g; exact base12_expansion_ready
  · subst g; exact base13_expansion_ready
  · subst g; exact base14_expansion_ready
  · subst g; exact base15_expansion_ready
  · subst g; exact base16_expansion_ready
  · subst g; exact base17_expansion_ready
  · subst g; exact base18_expansion_ready
  · subst g; exact base19_expansion_ready
  · subst g; exact base20_expansion_ready
  · subst g; exact base21_expansion_ready
  · subst g; exact base22_expansion_ready
  · subst g; exact base23_expansion_ready
  · subst g; exact base24_expansion_ready
  · subst g; exact base25_expansion_ready
  · subst g; exact base26_expansion_ready
  · subst g; exact base27_expansion_ready
  · subst g; exact base28_expansion_ready
  · subst g; exact base29_expansion_ready
  · subst g; exact base30_expansion_ready
  · subst g; exact base31_expansion_ready
  · subst g; exact base32_expansion_ready
  · subst g; exact base33_expansion_ready
  · subst g; exact base34_expansion_ready
  · subst g; exact base35_expansion_ready
  · subst g; exact base36_expansion_ready
  · subst g; exact base37_expansion_ready
  · subst g; exact base38_expansion_ready
  · subst g; exact base39_expansion_ready
  · subst g; exact base40_expansion_ready
  · subst g; exact base41_expansion_ready
  · subst g; exact base42_expansion_ready
  · subst g; exact base43_expansion_ready
  · subst g; exact base44_expansion_ready
  · subst g; exact base45_expansion_ready
  · subst g; exact base46_expansion_ready
  · subst g; exact base47_expansion_ready
  · subst g; exact base48_expansion_ready
  · subst g; exact base49_expansion_ready

#print axioms all_bases_expansion_ready
end QuorumAudit.TwoCrash
