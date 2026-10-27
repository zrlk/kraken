import Spike.Test.X64Ret0PlaceOKBase

/-!
# `PlaceOK` on `ret0.w` on x86-64: wrong outputs rejected

Wrong outputs against `ret0Place` (`Spike/Test/X64Ret0PlaceOKBase.lean`)
rejected, and the A1/A6/A8/A11 facts at `ret0.w`. Part of
`Spike/Test/X64Ret0PlaceOK.lean`.
-/

namespace Scc.Cert.PlaceOK.X64.Test

open Kraken Kraken.Promising.X64 Scc.Cert.Rt.X64 Scc.Cert.Link.X64 SccCode

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
