import Scc.Cert.PlaceOKX64
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Ret0Segs
import Spike.Test.X64Ret0Offs
import Spike.Lib.X64Print
import Spike.Lib.X64Abort
import Spike.Lib.Ret0Src
import Spike.Lib.Hello1Src
import Spike.Lib.X64Hello1Code

/-!
# `PlaceOK` against the hand checks of `ret0.w` on x86-64

One kernel decision of `PlaceOK` (`Scc/Cert/PlaceOKX64.lean`),
`ret0_placeOK`, and each of the hand checks of `Spike/Lib/X64Ret0Code.lean`
re-derived from it by an extraction lemma, at the hand statement: the
components cover the hand facts, and the facts follow without another
decision; and five wrong outputs rejected. `hello1.w`'s twin is
`Spike/Test/X64Hello1PlaceOK.lean` (a module of its own: one per program
keeps each file's memory under the per-process budget). The x64 twin of
`Spike/Test/A64Ret0PlaceOK.lean`.

The block table of the placement data is the hand table `ret0T` with the
static offsets the analyser gives its blocks (`ret0Offs`,
`Spike/Test/X64Ret0Offs.lean`), zipped by `ofGrps`, and each group's cells
in no block (`ret0Evs`, `withEvs`); the table is the hand one again by
`toGrps_withEvs` and `toGrps_ofGrps`.
-/

namespace Scc.Cert.PlaceOK.X64.Test

open Kraken Kraken.Promising.X64 Scc.Cert.Rt.X64 Scc.Cert.Link.X64 SccCode

/-! ## ret0 -/

/-- `ret0.w`'s placement data: its block table with its offsets, stack need and `scc_rt_main`'s tail. The output is
`⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩`, written out so that the extraction lemmas'
`o.prog` reduces to `ret0Cells` by projection. -/
def ret0Place : PlaceData :=
  { blocks := withEvs (ofGrps ret0T ret0Offs) ret0Evs, need := ret0Need, tail := .bare,
    ir := some (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src).low.ir }

theorem ret0_placeOK :
    placeOK Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩ = true := by decide +kernel

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

/-! ## A wrong output is rejected

Each part decides `false` on a wrong output, so `PlaceOK` does: its
conjunction is `false` (`placeOK_eq_false_of_a3`, `…_a5`, `…_a7`, `…_a2`, `…_a8`, `…_a9`). -/

/-- A block table with a block that is not in the program fails A3. -/
example : placeOK Config.canonical
    ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs,
      { ret0Place with blocks := [⟨"scc_rt_main", [⟨0, 0, 0, 0, ⟨0, []⟩, [(.label "x", 0)]⟩], []⟩] }⟩ = false :=
  placeOK_eq_false_of_a3 (by decide +kernel)

/-- An empty block table fails A3: the program's cells are in no row
(`coverOk`). -/
example : placeOK Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, { ret0Place with blocks := [] }⟩ =
    false :=
  placeOK_eq_false_of_a3 (by decide +kernel)

/-- The block table without its single instructions fails A3: the cells
between blocks are in no row. -/
example : placeOK Config.canonical
    ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, { ret0Place with blocks := ofGrps ret0T ret0Offs }⟩ = false :=
  placeOK_eq_false_of_a3 (by decide +kernel)

/-- Offsets under which a block is not covered fail A5: `ret0`'s table with
every row at `%rsp`'s entry offset and an empty region. -/
example : placeOK Config.canonical
    ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, { ret0Place with blocks := ofGrps ret0T [] }⟩ = false :=
  placeOK_eq_false_of_a5 (by decide +kernel)

/-- An output without its IR fails A9. -/
example : placeOK Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, { ret0Place with ir := none }⟩ = false :=
  placeOK_eq_false_of_a9 rfl

/-- `ret0.w`'s IR against `hello1.w`'s cells fails A9 (`main`'s code block
is not there: `hello1.w`'s `wc_main` is another body). -/
example : placeOK Config.canonical
    ⟨hello1Cells, hello1Secs, hello1Asm.labelOffs, ret0Place⟩ = false :=
  placeOK_eq_false_of_a9 (by decide +kernel)

/-- The wrong tail shape fails A7. -/
example : placeOK Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, { ret0Place with tail := .setup }⟩ =
    false :=
  placeOK_eq_false_of_a7 (by decide +kernel)

/-- A wrong label offset from the assembler fails A2 (the size table). -/
example : placeOK Config.canonical
    ⟨ret0Cells, ret0Secs, ("_start", 1) :: ret0Asm.labelOffs.tail, ret0Place⟩ = false :=
  placeOK_eq_false_of_a2 (by decide +kernel)

/-- A7's abort path phase check (`abortPhC`) holds on `ret0.x` at its link
and fails closed: with the heap abort's label at the overflow stub's first
instruction (a site there, so that pc is not off the sites), and with the
dispatcher's `.Lscc_rt_abort.is0` renamed (a branch target that does not
resolve). -/
example :
    let Λ := linkOf ret0Cells ret0Secs
    let Λ' := { Λ with abortLbl := fun k => match k with
      | .heap => Spike.Lib.X64.Abort.overflow.entry
      | k => Λ.abortLbl k }
    let c := ret0Cells.map fun dz => if dz.1 == .label ".Lscc_rt_abort.is0" then (.label ".Lx", dz.2) else dz
    (Spike.Lib.X64.StubW.abortPhC Λ.code.lo Λ ret0Cells, Spike.Lib.X64.StubW.abortPhC Λ.code.lo Λ' ret0Cells,
      Spike.Lib.X64.StubW.abortPhC Λ.code.lo Λ c) = (true, false, false) := by
  decide +kernel

/-- Without its `.bss` (the runtime's counters and the first TCB), the
runtime's data words are not data symbols: A8 fails. -/
example : placeOK Config.canonical ⟨ret0Cells, { ret0Secs with bss := [] }, ret0Asm.labelOffs, ret0Place⟩ = false :=
  placeOK_eq_false_of_a8 (by decide +kernel)

/-- `ret0.w`'s layout at its canonical tables. -/
abbrev ret0LΛ : Scc.Sem.Layout := (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ

/-- A8's `rtInitOk` holds on `ret0.w`, and the limit word (`scc_rt_pinned + 16`, the
`ret0_limInit` of `Spike/Lib/X64Ret0Correct.lean`) starts at `0` in the loaded memory
(`initVal_rt_of_rtInitOk`). -/
theorem ret0_limInitOk :
    rtA ret0LΛ ret0Cells ret0Secs "scc_rt_pinned" + 16#64
        = BitVec.ofNat 64 134217744 ∧
      ({ init := initOf ret0LΛ ret0Cells ret0Secs, msgs := #[] } :
        Kraken.Promising.Memory).initVal ⟨BitVec.ofNat 64 134217744, 8⟩ = 0 := by
  have hl : rtA ret0LΛ ret0Cells ret0Secs "scc_rt_pinned" + 16#64
      = BitVec.ofNat 64 134217744 := by decide +kernel
  have h := initVal_rt_of_rtInitOk (rtInit_of_placeOK ret0_placeOK)
    (m := { init := initOf ret0LΛ ret0Cells ret0Secs, msgs := #[] }) rfl
    (a := rtA ret0LΛ ret0Cells ret0Secs "scc_rt_pinned" + 16#64)
    (List.mem_append_right _ (List.mem_map.mpr ⟨1, List.mem_range.mpr (by decide), rfl⟩))
  exact ⟨hl, hl ▸ h⟩

/-- `rtInitOk` fails closed: with an image word at the limit word, or with
`.rodata` laid out over it, a runtime word has an initial word in the load. -/
example :
    let Λ := (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ
    let Λi := { Λ with image := (134217744, 1) :: Λ.image }
    let Λr := { Λ with rodata := ⟨134217744, 8⟩ }
    (rtInitOk Λ ret0Cells ret0Secs, rtInitOk Λi ret0Cells ret0Secs,
      rtInitOk Λr ret0Cells { ret0Secs with rodata := [.quad 1] }) = (true, false, false) := by
  decide +kernel

/-- A1's `_start` check holds on `ret0.w`: `_start` is the first code label,
at the code base (`start_at_lo_of_placeOK`). -/
example : Scc.Sem.X64.codeLabel ret0LΛ.code.lo ret0Cells "_start" = some 4194304 ∧ ret0LΛ.code.lo = 4194304 :=
  ⟨start_at_lo_of_placeOK ret0_placeOK, rfl⟩

/-- A1's `_start` check fails closed: with an instruction before `_start`
(`_start` then 2 bytes past the code base) or with `_start` renamed, A1 fails. -/
example :
    let p := (ret0Cells.drop 1).take 1 ++ ret0Cells
    let q := ret0Cells.map fun dz => if dz.1 == .label "_start" then (.label "_strt", dz.2) else dz
    let lo := ret0LΛ.code.lo
    (Scc.Sem.X64.codeLabel lo p "_start", Scc.Sem.X64.codeLabel lo q "_start",
      a1 ⟨p, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
        (tablesOf Config.canonical ⟨p, ret0Secs, ret0Asm.labelOffs, ret0Place⟩),
      a1 ⟨q, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
        (tablesOf Config.canonical ⟨q, ret0Secs, ret0Asm.labelOffs, ret0Place⟩)) =
      (some (4194304 + 2), none, false, false) := by
  decide +kernel

example :
    placeOK Config.canonical ⟨(ret0Cells.drop 1).take 1 ++ ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩ =
      false :=
  placeOK_eq_false_of_a1 (by decide +kernel)

/-- A8's `rtOffOk` holds on `ret0.w`: the limit word (`scc_rt_pinned + 16`) is in
the pinned region, clear of `.data` and the heap (`rtOff_of_placeOK`). -/
example : ret0LΛ.pinned.contains 134217744 = true ∧
    clearB ret0LΛ.data (BitVec.ofNat 64 134217744) = true ∧ clearB ret0LΛ.heap (BitVec.ofNat 64 134217744) = true := by
  have h := clear_of_rtOffOk (rtOff_of_placeOK ret0_placeOK) (j := 2) (by decide)
  have hl : rtA ret0LΛ ret0Cells ret0Secs "scc_rt_pinned" + BitVec.ofNat 64 (8 * 2) = BitVec.ofNat 64 134217744 :=
    ret0_limInitOk.1
  rw [hl] at h
  exact ⟨by decide +kernel, h⟩

/-- `rtOffOk` fails closed: with `.data` or the heap laid out over the first TCB
(the limit word in it), a TCB word is not clear of it. -/
example :
    let Λ := ret0LΛ
    (rtOffOk Λ ret0Cells ret0Secs, rtOffOk { Λ with data := ⟨134217744, 8⟩ } ret0Cells ret0Secs,
      rtOffOk { Λ with heap := ⟨134217728, 4096⟩ } ret0Cells ret0Secs) = (true, false, false) := by
  decide +kernel

/-- `cells` with the cell `off` bytes after the label `l` replaced by `c`. -/
def breakAtB (cells : List (Directive × Nat)) (l : String) (off : Nat) (c : Directive × Nat) :
    List (Directive × Nat) :=
  match cells.findIdx? (·.1 == .label l) with
  | some i =>
    let rest := cells.drop (i + 1)
    let k := ((List.range rest.length).find? fun j => ((rest.take j).map (·.2)).sum == off).getD rest.length
    cells.set (i + 1 + k) c
  | none => cells

/-- With `ud2` in place of the overflow stub's `write` system call (34
bytes after its entry), A7 fails (`Abort.stubIn`'s `syscall`), the stub's
other blocks still in place. -/
example : placeOK Config.canonical
    ⟨breakAtB ret0Cells Spike.Lib.X64.Abort.overflow.entry 34 (Spike.Lib.X64.ud2Dir, 2), ret0Secs,
      ret0Asm.labelOffs, ret0Place⟩ = false :=
  placeOK_eq_false_of_a7 (by decide +kernel)

example : let c := breakAtB ret0Cells Spike.Lib.X64.Abort.overflow.entry 34 (Spike.Lib.X64.ud2Dir, 2)
    (blockAtB c Spike.Lib.X64.Abort.overflow.entry 34 [(.instr (.regular .W64 .W64 .syscall), 2)],
      blockAtB c Spike.Lib.X64.Abort.overflow.entry 7 Spike.Lib.X64.Abort.x1Overflow &&
        blockAtB c Spike.Lib.X64.Abort.overflow.entry 36 Spike.Lib.X64.Abort.x2) = (false, true) := by
  decide +kernel

/-- A6's runtime phase facts (`rtPhOk` at `rtPhTab none`) and A11's
`scc_rt_main` facts (`mainPhTab`) hold on `ret0.w`; a wrong `scc_rt_main`
phase fact fails. -/
example :
    let Λ := (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩).Λ
    rtPhOk Λ.code.lo ret0Cells Λ (Spike.Lib.X64.Rt.rtPhTab none) = true ∧
      rtPhOk Λ.code.lo ret0Cells Λ (Spike.Lib.X64.Rt.mainPhTab Spike.Lib.X64.Rt.bareMC) = true ∧
      rtPhOk Λ.code.lo ret0Cells Λ [.ph Spike.Lib.X64.Rt.bareMC.sc 0 13] = false :=
  ⟨rtPh_of_placeOK ret0_placeOK, mainPh_of_placeOK ret0_placeOK rfl, by decide +kernel⟩

end Scc.Cert.PlaceOK.X64.Test
