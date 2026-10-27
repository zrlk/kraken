import Scc.Cert.PlaceOKX64
import Scc.Cert.A12StageX64
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Ret0Segs
import Spike.Test.X64Ret0Offs
import Spike.Lib.X64Print
import Spike.Lib.X64Abort
import Spike.Lib.Ret0Src
import Spike.Lib.Hello1Src
import Spike.Lib.X64Hello1Code

/-!
# `PlaceOK` on `ret0.w` on x86-64: the decision

`ret0.w`'s placement data `ret0Place` and `PlaceOK`
(`Scc/Cert/PlaceOKX64.lean`) on it, `ret0_placeOK`, decided by the kernel one
component at a time (`ret0P_part1` … `ret0P_part12`, combined by
`placeOK_of`), with the definitions the checks against it share. Part of
`Spike/Test/X64Ret0PlaceOK.lean`, which imports every part: the checks are
split over `Spike/Test/X64Ret0PlaceOKA.lean` (the hand checks re-derived)
and `Spike/Test/X64Ret0PlaceOKB.lean` (wrong outputs rejected), so that
each module stays under the per-process memory budget.
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

/-! ### `ret0_placeOK`, one component at a time

Each component of `PlaceOK` decided by the kernel in a declaration of its
own, then combined by `placeOK_of` (as `Spike/Test/X64Ret0PlaceOKE.lean`
does on scc's output), so that no single decision holds the whole check. -/

theorem ret0P_part1 :
    a1 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part2 :
    a2 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part3 :
    a3 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part4 :
    a4 Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part5 :
    a5 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part6 :
    a6 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part7 :
    a7 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part8 :
    a8 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part9 :
    a9 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part11 :
    a11 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true := by
  decide +kernel

theorem ret0P_part12 :
    a12 ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩
      (tablesOf Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩) = true :=
  a12_of_split (by decide +kernel) (by decide +kernel)

theorem ret0_placeOK :
    placeOK Config.canonical ⟨ret0Cells, ret0Secs, ret0Asm.labelOffs, ret0Place⟩ = true :=
  placeOK_of ret0P_part1 ret0P_part2 ret0P_part3 ret0P_part4 ret0P_part5 ret0P_part6 ret0P_part7 ret0P_part8
    ret0P_part9 ret0P_part11 ret0P_part12

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

/-- `cells` with the cell `off` bytes after the label `l` replaced by `c`. -/
def breakAtB (cells : List (Directive × Nat)) (l : String) (off : Nat) (c : Directive × Nat) :
    List (Directive × Nat) :=
  match cells.findIdx? (·.1 == .label l) with
  | some i =>
    let rest := cells.drop (i + 1)
    let k := ((List.range rest.length).find? fun j => ((rest.take j).map (·.2)).sum == off).getD rest.length
    cells.set (i + 1 + k) c
  | none => cells

end Scc.Cert.PlaceOK.X64.Test
