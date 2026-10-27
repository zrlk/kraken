import Spike.Test.X64Ret0PlaceOKBase

/-!
# `PlaceOK` on `ret0.w` on x86-64: the hand checks

Each of the hand checks of `Spike/Lib/X64Ret0Code.lean` re-derived from
`ret0_placeOK` (`Spike/Test/X64Ret0PlaceOKBase.lean`) by an
extraction lemma, at the hand statement. Part of `Spike/Test/X64Ret0PlaceOK.lean`.
-/

namespace Scc.Cert.PlaceOK.X64.Test

open Kraken Kraken.Promising.X64 Scc.Cert.Rt.X64 Scc.Cert.Link.X64 SccCode

example : ret0Λ.WF := by
  have h := wf_link_of_placeOK ret0Imms ret0_placeOK; dsimp only [Config.canonical] at h; exact h
/-- `X64Ret0Correct.ret0_clear`'s statement. -/
example : Scc.Sem.Entry.linux.clear ret0Λ = true := by
  have h := clear_link_of_placeOK ret0Imms ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : abortsIn ret0Cells ret0Λ = true := by
  have h := abortsIn_link_of_placeOK ret0Imms ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : imageIn ret0Cells ret0Secs ret0Λ = true := by
  have h := imageIn_link_of_placeOK ret0Imms ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : loadOk ret0Λ ret0Cells ret0Secs ret0Asm.labelOffs = true := by
  have h := loadOk_link_of_placeOK ret0Imms ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : Scc.Cert.WideX64.wideIn (ret0Cells.map (·.1)) = true := by
  have h := wideIn_of_placeOK ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : blocksIn ret0Cells ret0T := by
  have h := blocksIn_of_placeOK ret0_placeOK
  simp only [ret0Place, toGrps_withEvs, toGrps_ofGrps] at h
  exact h
example : coverOk ret0Cells ret0Place.blocks = true := by
  have h := cover_of_placeOK ret0_placeOK
  simp only at h
  exact h
example : Scc.Cert.Rt.X64.Abort.abortIn ret0Cells = true := by
  have h := abortIn_of_placeOK ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : Scc.Cert.Rt.X64.Print.printIn ret0Cells = true := by
  have h := printIn_of_placeOK ret0_placeOK; dsimp only [Config.canonical] at h; exact h
example : Spike.Lib.X64.Flow.mainExit = true := by
  have h := mainIn0_of_placeOK ret0_placeOK rfl; dsimp only [Config.canonical] at h; exact h
example : Scc.Cert.NeedX64.needOk ret0Cells ret0Need 12288 ["scc_rt_main"] = true := by
  have h := needOk_of_placeOK ret0_placeOK; dsimp only [Config.canonical] at h; exact h

/-! ### ret0's `block_spec` coverage checks

Each hand `block_spec`'s `_ok` (`okBlk lo hi o blk`, by `decide`) whose
region and offsets are the row's, re-derived from `ret0_placeOK` (A5) by a
lookup of its row (`rowIn`): `scc_rt_print`'s, `scc_rt_abort`'s and the
stubs'. The other hand checks state other offsets than the rows (the rows
also know `%rbp`'s, after the frame's setup, and their regions are the
whole function's); the rows' checks are at the rows'. -/

section Blocks

open Spike.Lib.X64

example : okBlk (-8) 16 Abort.oE Abort.Disp.d0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.oE, Abort.Disp.d0⟩)
    (l := "scc_rt_abort") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.g1 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.g1⟩)
    (l := ".Lscc_rt_abort.is0") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.g2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.g2⟩)
    (l := ".Lscc_rt_abort.is2") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.g3 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.g3⟩)
    (l := ".Lscc_rt_abort.is4") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.g4 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.g4⟩)
    (l := ".Lscc_rt_abort.is6") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.g5 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.g5⟩)
    (l := ".Lscc_rt_abort.is8") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.j1 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-8), 16, Abort.Disp.oD, Abort.Disp.j1⟩)
    (l := ".Lscc_rt_abort.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.j2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-8), 16, Abort.Disp.oD, Abort.Disp.j2⟩)
    (l := ".Lscc_rt_abort.next1") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.j3 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-8), 16, Abort.Disp.oD, Abort.Disp.j3⟩)
    (l := ".Lscc_rt_abort.next3") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.j4 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-8), 16, Abort.Disp.oD, Abort.Disp.j4⟩)
    (l := ".Lscc_rt_abort.next5") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.j5 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-8), 16, Abort.Disp.oD, Abort.Disp.j5⟩)
    (l := ".Lscc_rt_abort.next7") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.t1 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.t1⟩)
    (l := ".Lscc_rt_abort.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.t2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.t2⟩)
    (l := ".Lscc_rt_abort.next1") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.t3 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.t3⟩)
    (l := ".Lscc_rt_abort.next3") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.t4 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.t4⟩)
    (l := ".Lscc_rt_abort.next5") ret0_placeOK (by decide +kernel)
example : okBlk (-8) 16 Abort.Disp.oD Abort.Disp.t5 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-8), 16, Abort.Disp.oD, Abort.Disp.t5⟩)
    (l := ".Lscc_rt_abort.next7") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oE Abort.x0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-24), 16, Abort.oE, Abort.x0⟩)
    (l := "scc_rt_abort_overflow") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oI Abort.x1Heap = true :=
  okBlk_of_rowIn_placeOK (b := ⟨1, 7, (-24), 16, Abort.oI, Abort.x1Heap⟩)
    (l := ".Lscc_rt_abort_heap.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oI Abort.x1Overflow = true :=
  okBlk_of_rowIn_placeOK (b := ⟨1, 7, (-24), 16, Abort.oI, Abort.x1Overflow⟩)
    (l := ".Lscc_rt_abort_overflow.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oI Abort.x1Stack = true :=
  okBlk_of_rowIn_placeOK (b := ⟨1, 7, (-24), 16, Abort.oI, Abort.x1Stack⟩)
    (l := ".Lscc_rt_abort_stack.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oI Abort.x1Threads = true :=
  okBlk_of_rowIn_placeOK (b := ⟨1, 7, (-24), 16, Abort.oI, Abort.x1Threads⟩)
    (l := ".Lscc_rt_abort_heap.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oI Abort.x1Write = true :=
  okBlk_of_rowIn_placeOK (b := ⟨1, 7, (-24), 16, Abort.oI, Abort.x1Write⟩)
    (l := ".Lscc_rt_abort_write.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-24) 16 Abort.oI Abort.x2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨7, 36, (-24), 16, Abort.oI, Abort.x2⟩)
    (l := ".Lscc_rt_abort_overflow.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oE Print.x0 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oE, Print.x0⟩)
    (l := "scc_rt_print") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x10 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-40), 16, Print.oI, Print.x10⟩)
    (l := ".Lscc_rt_print.chk3") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x11 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x11⟩)
    (l := ".Lscc_rt_print.adv") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x12 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x12⟩)
    (l := ".Lscc_rt_print.fail") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x13 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x13⟩)
    (l := ".Lscc_rt_print.done") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x1 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x1⟩)
    (l := ".Lscc_rt_print.entry") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x2 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x2⟩)
    (l := ".Lscc_rt_print.loop") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x3 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 20, (-40), 16, Print.oI, Print.x3⟩)
    (l := ".Lscc_rt_print.loop") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x4 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x4⟩)
    (l := ".Lscc_rt_print.write") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x5 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨5, 22, (-40), 16, Print.oI, Print.x5⟩)
    (l := ".Lscc_rt_print.write") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x6 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨10, 42, (-40), 16, Print.oI, Print.x6⟩)
    (l := ".Lscc_rt_print.write") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x7 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x7⟩)
    (l := ".Lscc_rt_print.chk2") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x8 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨4, 16, (-40), 16, Print.oI, Print.x8⟩)
    (l := ".Lscc_rt_print.chk2") ret0_placeOK (by decide +kernel)
example : okBlk (-40) 16 Print.oI Print.x9 = true :=
  okBlk_of_rowIn_placeOK (b := ⟨0, 0, (-40), 16, Print.oI, Print.x9⟩)
    (l := ".Lscc_rt_print.chk3") ret0_placeOK (by decide +kernel)

end Blocks

end Scc.Cert.PlaceOK.X64.Test
