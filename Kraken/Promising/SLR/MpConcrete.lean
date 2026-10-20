/-
`mp_armv8` (`SLR/MpAdequacy.lean`) at a concrete instance: the writer laid
out at `0x100000` and the reader at `0x200000` (4 bytes per instruction,
labels empty, as the `.kl` runner lays out text), the flag at `0x1000`, the
data at `0x1100`, both initially `0`; every hypothesis discharged.
-/
import Kraken.Promising.SLR.MpAdequacy
import Kraken.Promising.SLR.RunSched
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.SLR.MpConcrete

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR (runSched runSched_reachable)

/-! ## The layouts -/

/-- The writer's layout: text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def wLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize mpWriter

/-- The reader's layout: text at `0x200000`, each directive its `fakeSize`. -/
@[reducible] def rLayout : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize mpReader

theorem wLayout_cells : ((wLayout mpWriter).2.map (·.2)) = [4, 4, 4, 4, 0] := by decide

theorem rLayout_cells : ((rLayout mpReader).2.map (·.2)) = [0, 4, 4, 4, 0] := by decide

instance wValid : Executable.ValidLayout (wLayout mpWriter) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance rValid : Executable.ValidLayout (rLayout mpReader) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- The flag word's address. -/
def flagAddr : BitVec 64 := 0x1000
/-- The data word's address. -/
def dataAddr : BitVec 64 := 0x1100

/-- The parameters; the ghost token `W = ⟨0, 5⟩` (never 4 bytes wide). -/
def Pmp : Params where
  f := flagAddr
  d := dataAddr
  W := ⟨0, 5⟩

theorem mpLocs : MpLocs Pmp where
  fd := by decide
  wf := by decide
  wd := by decide

/-- The writer's initial state: `X0 = flag`, `X1 = data`, at `0x100000`,
halting at the end of its text (`0x100000 + 16`). -/
def writer0 : State where
  exe := wLayout mpWriter
  endPc := 0x100000 + 16
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x100000)

/-- The reader's initial state: `X0 = flag`, `X1 = data`, at `0x200000`
(the label `spin`), halting at the end of its text (`0x200000 + 12`). -/
def reader0 : State where
  exe := rLayout mpReader
  endPc := 0x200000 + 12
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x200000)

/-- The initial memory: `flag = 0`, `data = 0`. -/
def initMemMp : List (Loc × Val) := [(Pmp.Fl, 0), (Pmp.Dt, 0)]

theorem writer0_frame : FrameW (layout := wLayout) Pmp writer0 ∧ AtPos (layout := wLayout) mpWriter writer0 0 := by
  refine ⟨FrameW.mk (layout := wLayout) rfl rfl (by decide) (by decide) (by decide) ?_ ?_,
    show writer0.st.2 = (wLayout mpWriter).addrOf 0 by decide⟩ <;>
    simp [writer0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

theorem reader0_frame : FrameR (layout := rLayout) Pmp reader0 ∧ AtPos (layout := rLayout) mpReader reader0 0 := by
  refine ⟨FrameR.mk (layout := rLayout) rfl rfl (by decide) (by decide) (by decide) ?_ ?_,
    show reader0.st.2 = (rLayout mpReader).addrOf 0 by decide⟩ <;>
    simp [reader0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

/-! ## The instance -/

/-- **Message passing** for the concrete writer and reader under
`Arch.armv8`: every reachable final configuration has the reader's `W4` at
`1` and the data word at `1`. -/
theorem mp_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writer0, reader0] initMemMp) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal Pmp.Dt = 1#128 :=
  mp_armv8 wLayout rLayout Pmp mpLocs writer0_frame reader0_frame (by decide) hc hf

/-! ## Non-vacuity: a reachable final configuration

The writer runs its four instructions; the reader's acquire load then reads
the flag message `1` (the second successor; the first reads the initial `0`
and would spin), `cbz` falls through, and the data load reads `1`. The
machine's successor function is not kernel-reducible (`Std.HashMap`
certification cache, `Std.ExtHashMap` private memory), so the run is checked
by `native_decide`: **`mp_final_witness` depends on the axiom `native_decide`
adds (`schedMp_final._native.native_decide.ax_1_1`).** `mp_concrete` and
`mp_armv8` do not. -/

/-- The schedule: four writer steps, the reader's load of the flag message
`1`, then the reader's two remaining steps. -/
def schedMp : List Nat := [0, 0, 0, 0, 1, 0, 0]

/-- The run along `schedMp` ends in a final configuration where the reader's
`W4` and the data word are `1` (checked by evaluation). -/
theorem schedMp_final :
    ((runSched (I := isa) Arch.armv8 0 (Config.init [writer0, reader0] initMemMp) schedMp).map
      fun c => c.final && c.mem.finalVal Pmp.Dt == 1#128 &&
        (c.threads[1]?.map fun t => BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec == 1) == some true) =
      some true := by
  native_decide

/-- **Non-vacuity**: a final configuration is reachable from the initial
configuration of `mp_concrete`, and in it the reader's `W4` and the data
word are literally `1` (by evaluation, independently of `mp_concrete`).
Depends on the `native_decide` axiom of `schedMp_final`. -/
theorem mp_final_witness :
    ∃ c : Config isa, Reachable Arch.armv8 0 (Config.init [writer0, reader0] initMemMp) c ∧ c.final = true ∧
      c.mem.finalVal Pmp.Dt = 1#128 ∧
      ∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1 := by
  have h := schedMp_final
  cases hr : runSched (I := isa) Arch.armv8 0 (Config.init [writer0, reader0] initMemMp) schedMp with
  | none => rw [hr] at h; cases h
  | some c =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hf, hd⟩, ht⟩ := h
    cases ht1 : c.threads[1]? with
    | none => rw [ht1] at ht; cases ht
    | some t =>
      rw [ht1] at ht
      simp only [Option.map_some, Option.some.injEq, beq_iff_eq] at ht
      exact ⟨c, runSched_reachable hr, hf, hd, t, ht1, ht⟩

/-- The initial configuration is `Config.Live` (Theorem 1′'s liveness
premise holds at the start). Depends on the `native_decide` axiom, through
`mp_final_witness`. -/
theorem mp_init_live : (Config.init [writer0, reader0] initMemMp : Config isa).Live Arch.armv8 0 :=
  let ⟨c, hc, hf, _⟩ := mp_final_witness
  ⟨c, hc, hf⟩

/-- The witness agrees with `mp_concrete` (a consistency check of the
theorem's conclusion against an actual run). -/
theorem mp_witness_consistent :
    ∃ c : Config isa, Reachable Arch.armv8 0 (Config.init [writer0, reader0] initMemMp) c ∧ c.final = true ∧
      c.mem.finalVal Pmp.Dt = 1#128 :=
  let ⟨c, hc, hf, _⟩ := mp_final_witness
  ⟨c, hc, hf, (mp_concrete hc hf).2⟩

/-- The explorer on the theorem's initial configuration: the final
`(W4 of the reader, data)` pairs. -/
def exploreFinals : List (Nat × Nat) × Bool :=
  let r := explore Arch.armv8 (Config.init [writer0, reader0] initMemMp : Config isa)
    (fun c => ((c.threads[1]?.map fun t => (BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec).toNat).getD 0,
      (c.mem.finalVal Pmp.Dt).toNat)) { fuel := 64 }
  (r.finals, r.boundHit || !r.faults.isEmpty)

/-- info: ([(1, 1)], false) -/
#guard_msgs in
#eval exploreFinals

end Kraken.Promising.SLR.MpConcrete
