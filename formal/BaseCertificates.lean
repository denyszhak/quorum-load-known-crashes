import CertificateChecker



namespace QuorumAudit

set_option maxRecDepth 100000

set_option maxHeartbeats 0

-- Source SHA256: b88735680de9122d430846aa82912d78a8dca8d070439c7c1af67c3ae187a47b

def base00 : Gadget := { a := 0, b := 9, reads := [[2, 3, 4, 7, 10], [2, 3, 6, 9, 10], [2, 5, 8, 9, 10]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 3, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0], cuts := [] }

theorem base00_checked : checkGadget base00 = true := by decide

def base01 : Gadget := { a := 0, b := 12, reads := [[2, 5, 6, 9, 10, 13], [2, 5, 6, 9, 10, 13], [2, 5, 6, 9, 10, 13]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 0], cuts := [] }

theorem base01_checked : checkGadget base01 = true := by decide

def base02 : Gadget := { a := 0, b := 15, reads := [[2, 3, 4, 7, 10, 13, 16], [2, 3, 6, 9, 12, 15, 16], [2, 5, 8, 11, 14, 15, 16]], scale := 2, uniform := [0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 8, 0, 2, 0, 0, 2, 10, 0, 0, 0, 0, 2, 10, 0, 0, 0, 0, 2, 10, 0, 0, 0, 2, 0, 8, 0, 0, 0, 0, 0], cuts := [8] }

theorem base02_checked : checkGadget base02 = true := by decide

def base03 : Gadget := { a := 1, b := 8, reads := [[1, 3, 4, 6, 9], [1, 4, 7, 8, 9], [1, 4, 7, 9, 10]], scale := 1, uniform := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 2, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 1], cuts := [] }

theorem base03_checked : checkGadget base03 = true := by decide

def base04 : Gadget := { a := 1, b := 11, reads := [[1, 4, 7, 8, 9, 12], [1, 4, 7, 8, 9, 12], [1, 4, 7, 8, 9, 12]], scale := 1, uniform := [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 0, 3], cuts := [] }

theorem base04_checked : checkGadget base04 = true := by decide

def base05 : Gadget := { a := 1, b := 14, reads := [[1, 3, 4, 6, 9, 12, 15], [1, 4, 7, 10, 12, 13, 15], [1, 4, 7, 10, 13, 14, 15]], scale := 1, uniform := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 0, 2, 0, 0, 3, 0, 1, 0, 1, 0, 4, 0, 0, 0, 2, 1, 2, 2, 0, 0, 1, 2, 0, 3, 0, 0, 2, 1, 0, 0, 0, 1], cuts := [] }

theorem base05_checked : checkGadget base05 = true := by decide

def base06 : Gadget := { a := 1, b := 17, reads := [[1, 3, 4, 6, 9, 12, 15, 18], [1, 4, 5, 8, 11, 14, 15, 18], [1, 4, 7, 10, 13, 16, 18, 19]], scale := 2, uniform := [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], criticalFlow := [0, 0, 0, 0, 0, 0, 1, 5, 4, 5, 0, 4, 0, 5, 0, 5, 0, 4, 0, 5, 0, 5, 0, 4, 1, 4, 0, 4, 4, 0, 0, 0, 6, 0, 4, 2, 0, 0, 0, 8], cuts := [9] }

theorem base06_checked : checkGadget base06 = true := by decide

def base07 : Gadget := { a := 2, b := 7, reads := [[1, 4, 5, 8, 9], [1, 2, 4, 7, 10], [2, 5, 6, 9, 10]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0], cuts := [] }

theorem base07_checked : checkGadget base07 = true := by decide

def base08 : Gadget := { a := 2, b := 10, reads := [[1, 2, 5, 8, 9, 12], [1, 4, 7, 9, 10, 12], [2, 5, 7, 8, 10, 13]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 1, 2, 0, 0, 1, 0, 1, 4, 0, 0, 0, 0], cuts := [] }

theorem base08_checked : checkGadget base08 = true := by decide

def base09 : Gadget := { a := 2, b := 13, reads := [[1, 2, 5, 8, 9, 12, 15], [1, 4, 7, 10, 11, 12, 15], [2, 5, 7, 8, 10, 13, 16]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 0, 5, 0, 0, 1, 0, 1, 3, 0, 0, 0, 1, 0, 5, 0, 2, 0, 0, 0, 3, 0, 0, 1, 0, 1, 5, 0, 0, 0, 0], cuts := [] }

theorem base09_checked : checkGadget base09 = true := by decide

def base10 : Gadget := { a := 2, b := 16, reads := [[1, 2, 5, 6, 9, 12, 15, 18], [2, 5, 8, 11, 14, 16, 17, 19], [1, 4, 7, 10, 13, 16, 18, 19]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 0, 6, 0, 0, 1, 0, 0, 5, 0, 0, 2, 0, 0, 5, 0, 0, 2, 0, 0, 5, 0, 0, 2, 0, 0, 5, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0], cuts := [10] }

theorem base10_checked : checkGadget base10 = true := by decide

def base11 : Gadget := { a := 3, b := 6, reads := [[1, 2, 3, 6, 9], [1, 2, 5, 8, 9], [2, 3, 6, 7, 10]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0], cuts := [] }

theorem base11_checked : checkGadget base11 = true := by decide

def base12 : Gadget := { a := 3, b := 9, reads := [[2, 5, 6, 9, 12, 13], [2, 5, 6, 9, 12, 13], [2, 5, 6, 9, 12, 13]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 3, 0, 0, 0, 0], cuts := [] }

theorem base12_checked : checkGadget base12 = true := by decide

def base13 : Gadget := { a := 3, b := 12, reads := [[1, 2, 5, 8, 9, 12, 15], [2, 5, 8, 9, 10, 13, 16], [2, 5, 6, 9, 12, 15, 16]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 4, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 4, 0, 3, 1, 0, 0, 0, 1, 0, 3, 0, 1, 0, 2, 0, 3, 1, 0, 0, 0, 1], cuts := [] }

theorem base13_checked : checkGadget base13 = true := by decide

def base14 : Gadget := { a := 3, b := 15, reads := [[1, 2, 5, 6, 9, 12, 15, 18], [2, 3, 6, 7, 10, 13, 16, 19], [2, 5, 8, 11, 14, 15, 16, 19]], scale := 2, uniform := [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 10, 4, 0, 0, 0, 0, 0, 0, 8, 0, 4, 0, 2, 0, 8, 0, 4, 0, 2, 0, 8, 0, 4, 0, 2, 0, 6, 2, 2, 2, 2, 0, 10, 0, 0, 0, 0, 0], cuts := [11] }

theorem base14_checked : checkGadget base14 = true := by decide

def base15 : Gadget := { a := 4, b := 5, reads := [[1, 2, 3, 6, 9], [2, 3, 6, 7, 10], [1, 4, 7, 9, 10]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 2], cuts := [] }

theorem base15_checked : checkGadget base15 = true := by decide

def base16 : Gadget := { a := 4, b := 8, reads := [[1, 4, 7, 8, 9, 12], [1, 4, 7, 10, 11, 12], [2, 3, 6, 9, 10, 13]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 1, 0, 1, 3, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 1, 2, 0, 1, 0, 2, 0, 0, 0, 0, 3], cuts := [] }

theorem base16_checked : checkGadget base16 = true := by decide

def base17 : Gadget := { a := 4, b := 11, reads := [[1, 4, 7, 8, 9, 12, 15], [1, 4, 7, 8, 9, 12, 15], [2, 3, 4, 7, 10, 13, 16]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 2, 0, 1, 3, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 2, 4, 0, 0, 0, 3, 0, 0, 0, 0, 3], cuts := [] }

theorem base17_checked : checkGadget base17 = true := by decide

def base18 : Gadget := { a := 4, b := 14, reads := [[1, 4, 7, 8, 9, 12, 15, 18], [1, 4, 7, 10, 13, 15, 16, 18], [2, 3, 6, 9, 10, 13, 16, 19]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 3, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 3, 2, 4, 0, 0, 0, 0, 3, 0, 0, 1, 4, 0, 0, 1, 2, 2, 2, 0, 0, 0, 4, 1, 0, 0, 0, 2], cuts := [] }

theorem base18_checked : checkGadget base18 = true := by decide

def base19 : Gadget := { a := 4, b := 17, reads := [[1, 2, 3, 6, 9, 12, 15, 18, 21], [1, 4, 7, 8, 11, 14, 17, 20, 21], [2, 3, 4, 7, 10, 13, 16, 19, 22]], scale := 2, uniform := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], criticalFlow := [0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 2, 0, 10, 2, 4, 0, 0, 0, 10, 2, 4, 0, 0, 0, 10, 2, 4, 0, 0, 0, 0, 12, 0, 14, 2, 2, 0, 0, 0, 0, 0, 0, 0, 14], cuts := [12] }

theorem base19_checked : checkGadget base19 = true := by decide

def base20 : Gadget := { a := 5, b := 7, reads := [[1, 4, 5, 8, 11, 12], [2, 5, 8, 9, 10, 13], [1, 4, 7, 10, 12, 13]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 1, 0, 4, 0, 0, 1, 0, 0, 0, 3, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 1, 3, 0, 0, 0, 0], cuts := [] }

theorem base20_checked : checkGadget base20 = true := by decide

def base21 : Gadget := { a := 5, b := 10, reads := [[1, 4, 7, 8, 9, 12, 15], [2, 4, 5, 7, 10, 13, 16], [2, 5, 8, 11, 12, 13, 16]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 2, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 2, 0, 5, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0], cuts := [] }

theorem base21_checked : checkGadget base21 = true := by decide

def base22 : Gadget := { a := 5, b := 13, reads := [[1, 4, 7, 10, 13, 15, 16, 18], [1, 4, 5, 8, 11, 14, 17, 18], [2, 5, 8, 11, 12, 13, 16, 19]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 1, 0, 6, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 6, 1, 0, 0, 0, 1, 3, 0, 0, 2, 0, 0, 5, 0, 2, 1, 0, 0, 4, 0, 0, 0, 1], cuts := [] }

theorem base22_checked : checkGadget base22 = true := by decide

def base23 : Gadget := { a := 5, b := 16, reads := [[1, 4, 7, 8, 9, 12, 15, 18, 21], [2, 4, 5, 7, 10, 13, 16, 19, 22], [2, 5, 8, 11, 14, 17, 18, 19, 22]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 2, 7, 0, 0, 0, 0, 0, 0, 5, 0, 0, 2, 0, 1, 4, 0, 0, 3, 0, 1, 4, 0, 0, 3, 0, 1, 4, 0, 0, 3, 0, 0, 5, 0, 0, 2, 0, 1, 6, 0, 0, 0, 0], cuts := [13] }

theorem base23_checked : checkGadget base23 = true := by decide

def base24 : Gadget := { a := 6, b := 6, reads := [[2, 5, 6, 9, 12, 13], [2, 5, 6, 9, 12, 13], [2, 5, 6, 9, 12, 13]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0], cuts := [] }

theorem base24_checked : checkGadget base24 = true := by decide

def base25 : Gadget := { a := 6, b := 9, reads := [[1, 2, 5, 6, 9, 12, 15], [2, 3, 6, 9, 10, 13, 16], [2, 5, 8, 11, 12, 15, 16]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 4, 0, 0, 0, 2, 0, 3, 2, 0, 0, 0, 0, 0, 0, 1, 3, 0, 4, 0, 2, 0, 2, 0, 0, 0, 0, 3, 2, 0, 0, 0, 0], cuts := [] }

theorem base25_checked : checkGadget base25 = true := by decide

def base26 : Gadget := { a := 6, b := 12, reads := [[1, 4, 5, 8, 11, 12, 15, 18], [2, 3, 6, 9, 10, 13, 16, 19], [2, 5, 8, 11, 14, 15, 18, 19]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 6, 0, 0, 0, 0, 0, 6, 1, 0, 0, 0, 0, 0, 0, 5, 0, 2, 0, 0, 0, 4, 0, 0, 3, 3, 0, 0, 1, 3, 0, 0, 0, 5, 0, 0, 0, 0, 1], cuts := [] }

theorem base26_checked : checkGadget base26 = true := by decide

def base27 : Gadget := { a := 6, b := 15, reads := [[1, 4, 5, 8, 9, 12, 15, 18, 21], [2, 5, 6, 9, 10, 13, 16, 19, 22], [2, 5, 8, 11, 14, 17, 18, 21, 22]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 2, 5, 0, 5, 1, 0, 0, 2, 0, 0, 0, 1, 0, 0, 3, 1, 0, 4, 3, 0, 0, 1, 0, 4, 3, 0, 0, 1, 0, 4, 3, 0, 1, 0, 2, 0, 1, 0, 6, 0, 0, 0, 0, 1], cuts := [14] }

theorem base27_checked : checkGadget base27 = true := by decide

def base28 : Gadget := { a := 7, b := 8, reads := [[1, 4, 5, 6, 9, 12, 15], [2, 5, 6, 9, 10, 13, 16], [1, 4, 7, 10, 13, 15, 16]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 2, 0, 0, 4, 1, 1, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 1, 0, 0, 4, 0, 4, 0, 2, 1, 0, 0, 0, 0, 0, 0, 3], cuts := [] }

theorem base28_checked : checkGadget base28 = true := by decide

def base29 : Gadget := { a := 7, b := 11, reads := [[1, 4, 7, 10, 11, 12, 15, 18], [1, 4, 7, 10, 13, 15, 16, 18], [2, 5, 6, 9, 12, 15, 16, 19]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 2, 0, 3, 2, 0, 0, 1, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 5, 2, 4, 0, 0, 0, 0, 2, 0, 0, 2, 3, 0, 1, 0, 3, 1, 0, 0, 0, 3], cuts := [] }

theorem base29_checked : checkGadget base29 = true := by decide

def base30 : Gadget := { a := 7, b := 14, reads := [[1, 3, 4, 6, 9, 12, 15, 18, 21], [1, 4, 7, 10, 13, 16, 19, 20, 21], [2, 5, 6, 9, 12, 15, 16, 19, 22]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 1, 0, 4, 3, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 5, 0, 6, 2, 0, 0, 0, 1, 1, 0, 0, 5, 0, 0, 4, 2, 0, 1, 0, 2, 3, 0, 0, 0, 3], cuts := [] }

theorem base30_checked : checkGadget base30 = true := by decide

def base31 : Gadget := { a := 7, b := 17, reads := [[1, 2, 5, 6, 9, 12, 15, 18, 21, 24], [1, 4, 7, 10, 11, 14, 17, 20, 21, 24], [2, 3, 6, 7, 10, 13, 16, 19, 22, 25]], scale := 2, uniform := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], criticalFlow := [0, 0, 0, 0, 4, 12, 0, 0, 2, 0, 2, 14, 0, 0, 0, 0, 0, 0, 1, 3, 7, 8, 0, 7, 0, 3, 0, 8, 0, 7, 0, 3, 0, 8, 0, 7, 1, 2, 7, 0, 0, 0, 2, 0, 14, 0, 2, 2, 0, 0, 0, 14], cuts := [15] }

theorem base31_checked : checkGadget base31 = true := by decide

def base32 : Gadget := { a := 8, b := 10, reads := [[1, 4, 7, 10, 11, 14, 15, 18], [2, 3, 6, 7, 10, 13, 16, 19], [2, 5, 8, 11, 14, 15, 18, 19]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 1, 0, 5, 0, 0, 1, 2, 0, 4, 0, 1, 0, 0, 0, 0, 6, 0, 0, 0, 0, 1, 5, 1, 0, 0, 0, 0, 5, 1, 0, 1, 0, 0, 6, 0, 0, 0, 0], cuts := [] }

theorem base32_checked : checkGadget base32 = true := by decide

def base33 : Gadget := { a := 8, b := 13, reads := [[1, 4, 7, 10, 11, 14, 17, 18, 21], [2, 4, 5, 7, 10, 13, 16, 19, 22], [2, 5, 8, 11, 12, 15, 18, 19, 22]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 3, 6, 1, 0, 0, 0, 0, 4, 0, 3, 1, 0, 0, 0, 4, 0, 0, 2, 0, 0, 5, 2, 0, 0, 1, 2, 4, 0, 0, 2, 0, 0, 5, 1, 0, 1, 0, 2, 5, 0, 0, 0, 0], cuts := [] }

theorem base33_checked : checkGadget base33 = true := by decide

def base34 : Gadget := { a := 8, b := 16, reads := [[1, 4, 7, 10, 11, 14, 17, 20, 23, 24], [2, 3, 4, 7, 10, 13, 16, 19, 22, 25], [2, 5, 8, 11, 12, 15, 18, 21, 22, 25]], scale := 2, uniform := [0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 6, 0, 16, 0, 12, 0, 0, 0, 0, 4, 0, 0, 0, 0, 14, 0, 0, 1, 1, 0, 15, 2, 0, 0, 1, 0, 15, 2, 0, 0, 1, 0, 15, 2, 0, 1, 0, 0, 14, 2, 0, 0, 0, 4, 12, 0, 0, 0, 0], cuts := [16] }

theorem base34_checked : checkGadget base34 = true := by decide

def base35 : Gadget := { a := 9, b := 9, reads := [[1, 2, 5, 8, 11, 12, 15, 18], [2, 5, 8, 9, 12, 15, 16, 19], [2, 5, 8, 9, 12, 15, 16, 19]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 4, 0, 1, 0, 1, 0, 4, 2, 0, 0, 2, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 2, 5, 0, 0, 1, 0, 3, 2, 0, 1, 0, 3, 1, 0, 0, 0, 2], cuts := [] }

theorem base35_checked : checkGadget base35 = true := by decide

def base36 : Gadget := { a := 9, b := 12, reads := [[1, 2, 5, 8, 9, 12, 15, 18, 21], [1, 2, 5, 8, 11, 14, 17, 18, 21], [1, 2, 5, 8, 11, 14, 17, 18, 21]], scale := 1, uniform := [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 0, 0, 6, 3, 0, 0, 0, 3, 0, 0, 0, 6, 0, 0, 0, 0, 2, 0, 0, 5, 0, 2, 1, 0, 0, 1, 3, 1, 6, 0, 3, 0, 0, 0, 0, 3, 0, 3, 0, 0, 0, 0, 6], cuts := [] }

theorem base36_checked : checkGadget base36 = true := by decide

def base37 : Gadget := { a := 9, b := 15, reads := [[1, 3, 4, 6, 9, 12, 15, 18, 21, 24], [2, 5, 8, 11, 12, 13, 16, 19, 22, 25], [2, 5, 8, 11, 14, 17, 20, 21, 24, 25]], scale := 1, uniform := [0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 7, 0, 8, 0, 1, 0, 1, 0, 0, 0, 0, 7, 2, 0, 0, 0, 0, 0, 0, 4, 2, 0, 4, 3, 0, 0, 2, 0, 4, 3, 0, 0, 2, 0, 4, 3, 0, 0, 2, 3, 0, 0, 0, 6, 1, 0, 0, 0, 1], cuts := [17] }

theorem base37_checked : checkGadget base37 = true := by decide

def base38 : Gadget := { a := 10, b := 11, reads := [[1, 4, 5, 6, 9, 12, 15, 18, 21], [1, 4, 7, 10, 13, 16, 18, 19, 21], [2, 5, 8, 9, 12, 13, 16, 19, 22]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 1, 1, 3, 4, 0, 0, 0, 0, 2, 4, 2, 0, 0, 0, 3, 3, 0, 0, 0, 2, 0, 0, 2, 0, 2, 3, 3, 0, 0, 0, 4, 0, 0, 2, 3, 0, 2, 0, 3, 1, 0, 0, 0, 4], cuts := [] }

theorem base38_checked : checkGadget base38 = true := by decide

def base39 : Gadget := { a := 10, b := 14, reads := [[1, 4, 7, 10, 13, 16, 19, 21, 22, 24], [2, 3, 6, 9, 12, 15, 18, 21, 22, 25], [1, 4, 7, 10, 13, 16, 19, 22, 24, 25]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 1, 6, 1, 7, 0, 0, 0, 0, 2, 2, 0, 0, 4, 0, 3, 3, 0, 0, 0, 2, 0, 0, 4, 0, 4, 0, 0, 0, 5, 0, 2, 1, 3, 0, 0, 3, 5, 0, 0, 1, 3, 0, 0, 0, 7, 0, 0, 0, 0, 1], cuts := [] }

theorem base39_checked : checkGadget base39 = true := by decide

def base40 : Gadget := { a := 10, b := 17, reads := [[1, 4, 5, 8, 9, 12, 15, 18, 21, 24, 27], [1, 4, 7, 10, 13, 14, 17, 20, 23, 24, 27], [2, 5, 6, 9, 10, 13, 16, 19, 22, 25, 28]], scale := 2, uniform := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], criticalFlow := [0, 0, 2, 0, 2, 16, 0, 2, 0, 0, 0, 16, 0, 4, 2, 0, 0, 14, 0, 0, 0, 0, 0, 0, 6, 0, 3, 9, 8, 3, 0, 0, 0, 9, 8, 3, 0, 0, 0, 9, 8, 3, 0, 0, 0, 9, 0, 11, 6, 0, 3, 0, 4, 0, 0, 0, 0, 16], cuts := [18] }

theorem base40_checked : checkGadget base40 = true := by decide

def base41 : Gadget := { a := 11, b := 13, reads := [[1, 4, 7, 10, 13, 16, 19, 20, 21, 24], [2, 5, 7, 8, 10, 13, 16, 19, 22, 25], [2, 5, 8, 11, 14, 17, 18, 21, 22, 25]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 5, 3, 5, 0, 2, 1, 0, 0, 0, 0, 4, 0, 6, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 5, 0, 0, 4, 2, 0, 0, 2, 0, 7, 0, 3, 1, 0, 0, 3, 0, 0, 2, 0, 4, 4, 0, 0, 0, 0], cuts := [] }

theorem base41_checked : checkGadget base41 = true := by decide

def base42 : Gadget := { a := 11, b := 16, reads := [[1, 4, 7, 10, 13, 14, 17, 20, 23, 24, 27], [2, 5, 8, 10, 11, 13, 16, 19, 22, 25, 28], [2, 5, 8, 11, 14, 15, 18, 21, 24, 27, 28]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 1, 4, 5, 1, 3, 0, 0, 0, 4, 0, 6, 3, 0, 0, 0, 3, 1, 0, 0, 0, 5, 0, 0, 1, 2, 1, 7, 0, 1, 0, 2, 0, 7, 0, 1, 0, 2, 0, 7, 0, 1, 0, 2, 0, 7, 0, 0, 2, 0, 0, 7, 0, 0, 0, 2], cuts := [19] }

theorem base42_checked : checkGadget base42 = true := by decide

def base43 : Gadget := { a := 12, b := 12, reads := [[1, 2, 5, 8, 11, 12, 15, 18, 21, 24], [1, 4, 5, 8, 11, 14, 17, 18, 21, 24], [2, 5, 6, 9, 12, 15, 16, 19, 22, 25]], scale := 1, uniform := [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 5, 2, 6, 0, 2, 0, 1, 0, 0, 2, 0, 1, 5, 0, 4, 3, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 5, 0, 8, 0, 3, 0, 1, 0, 0, 0, 0, 7, 0, 0, 0, 2, 0, 6, 2, 0, 0, 0, 1], cuts := [] }

theorem base43_checked : checkGadget base43 = true := by decide

def base44 : Gadget := { a := 12, b := 15, reads := [[1, 4, 7, 8, 11, 14, 15, 18, 21, 24, 27], [2, 3, 6, 9, 12, 15, 16, 19, 22, 25, 28], [2, 5, 8, 11, 14, 17, 20, 23, 24, 27, 28]], scale := 2, uniform := [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 16, 2, 16, 0, 0, 2, 0, 0, 2, 0, 2, 16, 2, 0, 0, 0, 0, 16, 4, 0, 0, 0, 0, 0, 0, 6, 8, 3, 9, 0, 3, 0, 8, 0, 9, 0, 3, 0, 8, 0, 9, 0, 3, 0, 8, 3, 4, 0, 0, 10, 2, 0, 0, 0, 2], cuts := [20] }

theorem base44_checked : checkGadget base44 = true := by decide

def base45 : Gadget := { a := 13, b := 14, reads := [[1, 4, 7, 10, 13, 16, 19, 21, 22, 24, 27], [2, 5, 8, 9, 10, 13, 16, 19, 22, 25, 28], [2, 3, 6, 9, 12, 15, 18, 21, 24, 27, 28]], scale := 1, uniform := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1], criticalFlow := [0, 0, 4, 0, 2, 3, 0, 0, 5, 0, 2, 3, 0, 0, 5, 0, 0, 5, 0, 1, 4, 0, 1, 5, 0, 0, 0, 2, 0, 0, 3, 0, 6, 0, 0, 0, 2, 2, 0, 7, 0, 7, 0, 2, 0, 0, 0, 2, 2, 0, 4, 0, 3, 2, 0, 0, 0, 4], cuts := [] }

theorem base45_checked : checkGadget base45 = true := by decide

def base46 : Gadget := { a := 13, b := 17, reads := [[1, 4, 7, 10, 13, 16, 17, 20, 23, 26, 27, 30], [2, 3, 6, 9, 12, 13, 16, 19, 22, 25, 28, 31], [2, 5, 8, 11, 12, 15, 18, 21, 24, 27, 30, 31]], scale := 2, uniform := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], criticalFlow := [0, 0, 0, 2, 0, 20, 0, 2, 2, 0, 0, 16, 0, 0, 2, 2, 0, 20, 2, 0, 0, 0, 0, 18, 0, 0, 0, 2, 0, 0, 0, 2, 18, 2, 0, 0, 0, 2, 18, 2, 0, 0, 0, 2, 18, 2, 0, 0, 2, 0, 0, 18, 0, 18, 2, 0, 2, 0, 0, 2, 0, 0, 0, 18], cuts := [21] }

theorem base46_checked : checkGadget base46 = true := by decide

def base47 : Gadget := { a := 14, b := 16, reads := [[1, 4, 7, 10, 13, 16, 17, 18, 21, 24, 27, 30], [2, 5, 7, 8, 10, 13, 16, 19, 22, 25, 28, 31], [2, 5, 8, 11, 14, 17, 20, 23, 26, 27, 28, 31]], scale := 1, uniform := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], criticalFlow := [0, 0, 0, 4, 1, 9, 0, 6, 0, 1, 0, 0, 2, 0, 2, 0, 0, 5, 5, 5, 0, 0, 1, 0, 4, 2, 0, 0, 0, 5, 0, 0, 3, 0, 1, 6, 1, 1, 3, 0, 0, 6, 1, 1, 3, 0, 0, 6, 1, 1, 0, 3, 0, 9, 0, 1, 0, 0, 2, 6, 0, 0, 0, 1], cuts := [22] }

theorem base47_checked : checkGadget base47 = true := by decide

def base48 : Gadget := { a := 15, b := 15, reads := [[1, 2, 5, 8, 11, 14, 17, 18, 21, 24, 27, 30], [1, 4, 7, 10, 11, 14, 17, 20, 23, 26, 27, 30], [2, 3, 6, 9, 12, 15, 18, 19, 22, 25, 28, 31]], scale := 2, uniform := [0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0], criticalFlow := [0, 0, 9, 7, 0, 11, 4, 0, 0, 7, 0, 11, 4, 0, 0, 7, 0, 11, 4, 0, 0, 7, 0, 9, 4, 0, 9, 2, 0, 0, 0, 2, 0, 0, 16, 0, 2, 2, 0, 2, 18, 0, 0, 2, 0, 2, 18, 0, 0, 2, 0, 2, 0, 18, 2, 16, 0, 0, 2, 2, 0, 0, 0, 2], cuts := [7, 23] }

theorem base48_checked : checkGadget base48 = true := by decide

def base49 : Gadget := { a := 16, b := 17, reads := [[1, 4, 7, 10, 13, 16, 19, 20, 23, 26, 29, 30, 33], [2, 5, 8, 11, 12, 15, 16, 19, 22, 25, 28, 31, 34], [2, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 34]], scale := 2, uniform := [0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2], criticalFlow := [0, 0, 2, 0, 2, 18, 2, 0, 2, 0, 2, 18, 2, 0, 2, 0, 2, 18, 2, 0, 0, 2, 0, 22, 2, 0, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 2, 11, 11, 0, 11, 0, 2, 0, 11, 0, 11, 0, 2, 0, 11, 0, 11, 2, 0, 0, 9, 2, 9, 0, 0, 13, 0, 0, 4, 0, 0, 0, 18], cuts := [7, 24] }

theorem base49_checked : checkGadget base49 = true := by decide

def bases : List Gadget := [base00, base01, base02, base03, base04, base05, base06, base07, base08, base09, base10, base11, base12, base13, base14, base15, base16, base17, base18, base19, base20, base21, base22, base23, base24, base25, base26, base27, base28, base29, base30, base31, base32, base33, base34, base35, base36, base37, base38, base39, base40, base41, base42, base43, base44, base45, base46, base47, base48, base49]

theorem all_bases_checked : bases.all checkGadget = true := by decide

theorem base_table_complete : bases.map (fun g => (g.a, g.b)) = expectedPairs := by decide

theorem exactly_fifty_bases : bases.length = 50 := by decide

theorem bad_scale_rejected : checkGadget { base49 with scale := 0 } = false := by decide

theorem missing_reads_rejected : checkGadget { base49 with reads := [] } = false := by decide

theorem missing_flow_rejected : checkGadget { base49 with uniform := [] } = false := by decide

theorem missing_cuts_rejected : checkGadget { base49 with cuts := [] } = false := by decide

#print axioms all_bases_checked

#print axioms base_table_complete

#print axioms bad_scale_rejected

#print axioms missing_reads_rejected

#print axioms missing_flow_rejected

#print axioms missing_cuts_rejected

#print axioms base00_checked

#print axioms base01_checked

#print axioms base02_checked

#print axioms base03_checked

#print axioms base04_checked

#print axioms base05_checked

#print axioms base06_checked

#print axioms base07_checked

#print axioms base08_checked

#print axioms base09_checked

#print axioms base10_checked

#print axioms base11_checked

#print axioms base12_checked

#print axioms base13_checked

#print axioms base14_checked

#print axioms base15_checked

#print axioms base16_checked

#print axioms base17_checked

#print axioms base18_checked

#print axioms base19_checked

#print axioms base20_checked

#print axioms base21_checked

#print axioms base22_checked

#print axioms base23_checked

#print axioms base24_checked

#print axioms base25_checked

#print axioms base26_checked

#print axioms base27_checked

#print axioms base28_checked

#print axioms base29_checked

#print axioms base30_checked

#print axioms base31_checked

#print axioms base32_checked

#print axioms base33_checked

#print axioms base34_checked

#print axioms base35_checked

#print axioms base36_checked

#print axioms base37_checked

#print axioms base38_checked

#print axioms base39_checked

#print axioms base40_checked

#print axioms base41_checked

#print axioms base42_checked

#print axioms base43_checked

#print axioms base44_checked

#print axioms base45_checked

#print axioms base46_checked

#print axioms base47_checked

#print axioms base48_checked

#print axioms base49_checked

end QuorumAudit
