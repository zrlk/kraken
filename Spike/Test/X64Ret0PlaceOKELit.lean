import Scc.Cert.PlaceDataX64
import Scc.Cert.OutLitX64
import Scc.Cert.OutStageX64
import Scc.Cert.OutStageWX64
import Scc.Cert.MapsPart
import Scc.Cert.MapsEmitX64
import Spike.Lib.Ret0Src
import Spike.Lib.X64Ret0Code

/-!
# `ret0.w`'s x86-64 output as a literal

The x86-64 twin of `Spike/Test/A64Ret0PlaceOKELit.lean`: scc's x86-64
output for `ret0.w` (`ret0O`, computed by `lowerAll` and `Out.ofEmitted`
at the assembler's sizes and label offsets, `SccCode.ret0Asm`) and its
value written out at elaboration time (`ret0L`, `scc_lit%`), equal by
kernel runs of the pipeline's stages (`ret0_out_eq`), in a file of its own:
`Spike/Test/X64Ret0PlaceOKE.lean` decides `PlaceOK`'s parts on the
literal, one declaration each.

The pipeline ends with the GC tables' stage (`Scc.Lower.X64.tablesOf`), whose
reference fixpoint (`gcWit = none`) the kernel cannot afford. As a
certificate does (`Scc.Config.gcWit`), the equation goes through the run at
scc's ranked witness (`Stage.gwL`, `Stage.cfgW`), equal to scc's run where the
tables' stage at the witness succeeds
(`Scc.Cert.OutStageWX64.lowerAll_eq_of_tables`), and that run is checked in
stages on literals (`Stage`: the lowering, the emitter, the tables' items,
`scc_stackmap` table, tags, least fixpoints, maps, successors and
serialisation, then `ofStage`), each its own kernel check.
-/

namespace Spike.Test.X64Ret0PlaceOKE

set_option maxRecDepth 100000

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- scc's x86-64 output for `ret0.w` as `PlaceOK` reads it, at the
assembler's sizes and label offsets. -/
def ret0O : Out :=
  Out.ofEmitted (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src)
    SccCode.ret0Asm.sizes SccCode.ret0Asm.labelOffs

/-- `ret0O` as a literal: its value computed at elaboration time. -/
def ret0L : Out := scc_lit% ret0O

/-! ## The pipeline's stages on literals

Each `…Val` is computed at elaboration time (untrusted), its `…L` the
literal, which the theorem after checks in the kernel. -/

namespace Stage

open Scc.Cert.Maps

/-- scc's run, at elaboration time. -/
def run : Scc.Lower.X64.Emitted := Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src

/-- scc's ranked witness for the GC tables (`gcWitness`), at elaboration time. -/
def gwVal : GcWit := (Scc.Cert.MapsX64.gcWitness run.low.ir run.items).toOption.getD []

/-- The witness, as a literal (untrusted: the tables' stage checks it, `hle`). -/
noncomputable def gwL : GcWit := scc_lit% gwVal

/-- scc's configuration with the witness. -/
noncomputable def cfgW : Scc.Config := { ({ arch := .x64 } : Scc.Config) with gcWit := some gwL }

def irVal : Scc.IR.Program × Bool := (lowered1 { arch := .x64 } Spike.Lib.Ret0Src.ret0Src).getD default
noncomputable def irL : Scc.IR.Program × Bool := scc_lit% irVal

def emVal : List Scc.Emit.X64.Item × List (String × List Int × List Int) :=
  (Scc.Emit.X64.emitItemsMaps irVal.1).toOption.getD default
noncomputable def emL : List Scc.Emit.X64.Item × List (String × List Int × List Int) := scc_lit% emVal

def itVal : List Item := (Scc.Cert.MapsX64.itemsOf emVal.1 (Scc.Cert.MapsX64.unitSizes emVal.1)).toOption.getD []
noncomputable def itL : List Item := scc_lit% itVal

def stVal : List (Nat × List Int × List Int) := (Scc.Cert.MapsX64.stackTable emVal.1 itVal).toOption.getD []
noncomputable def stL : List (Nat × List Int × List Int) := scc_lit% stVal

def fnsVal : List FnTags :=
  (irVal.1.funcs.mapM (Scc.Cert.MapsX64.tagsOf irVal.1 itVal stVal)).toOption.getD []
noncomputable def fnsL : List FnTags := scc_lit% fnsVal

def msVal : List (List RootMap) :=
  ((fnsVal.zip (gwVal.map Prod.fst)).mapM (fun (t, w) => fnMapsW t itVal w)).toOption.getD []
noncomputable def msL : List (List RootMap) := scc_lit% msVal

def osVal : List (List Succs) :=
  ((fnsVal.zip msVal).mapM (fun (p : FnTags × List RootMap) =>
    outSuccs p.1 itVal (p.2.map fun (m : RootMap) => m.pt.addr))).toOption.getD []
noncomputable def osL : List (List Succs) := scc_lit% osVal

def fsVal : List Succs := fnsVal.flatMap (fun t => fnSuccs t itVal)
noncomputable def fsL : List Succs := scc_lit% fsVal

def tVal : Scc.Cert.Maps.Tables := (computeW fnsVal itVal (gwVal.map Prod.fst)).toOption.getD default
noncomputable def tL : Scc.Cert.Maps.Tables := scc_lit% tVal

def labsVal : List (Nat × String) := labelMap itVal
noncomputable def labsL : List (Nat × String) := scc_lit% labsVal

def tblVal : List DItem :=
  (tableItems tVal (labelIn labsVal) {} (fun g => (labelAddr itVal g).isSome)).toOption.getD []
noncomputable def tblL : List DItem := scc_lit% tblVal

theorem h1 : lowered1 cfgW Spike.Lib.Ret0Src.ret0Src = some irL := by kernel_rfl
theorem h2 : Scc.Emit.X64.emitItemsMaps irL.1 = .ok emL := by kernel_rfl
theorem hg : irL.1.growth.isSome = true := by kernel_rfl
theorem hi : Scc.Cert.MapsX64.itemsOf emL.1 (Scc.Cert.MapsX64.unitSizes emL.1) = .ok itL := by kernel_rfl
theorem hst : Scc.Cert.MapsX64.stackTable emL.1 itL = .ok stL := by kernel_rfl
theorem hfn : irL.1.funcs.mapM (Scc.Cert.MapsX64.tagsOf irL.1 itL stL) = .ok fnsL := by kernel_rfl
theorem hle : leastFrom itL fnsL gwL = true := by kernel_rfl
theorem hs : stubsOk fnsL itL = .ok () := by kernel_rfl
theorem hl : (gwL.map (·.1)).length = fnsL.length := by kernel_rfl
theorem hm : (fnsL.zip (gwL.map (·.1))).mapM (fun (t, w) => fnMapsW t itL w) = .ok msL := by kernel_rfl
theorem ho : (fnsL.zip msL).mapM (fun (p : FnTags × List RootMap) =>
    outSuccs p.1 itL (p.2.map fun (m : RootMap) => m.pt.addr)) = .ok osL := by kernel_rfl
theorem hf : fnsL.flatMap (fun t => fnSuccs t itL) = fsL := by kernel_rfl
theorem ht : (⟨sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) msL.flatten,
    sortStable (fun a b => decide (a.addr ≤ b.addr)) (fsL ++ osL.flatten), []⟩ : Scc.Cert.Maps.Tables) = tL := by
  kernel_rfl
theorem hlab : labelMap itL = labsL := by kernel_rfl
theorem hser : tableItems tL (labelIn labsL) {} (fun g => (labelAddr itL g).isSome) = .ok tblL := by kernel_rfl

/-- The tables' stage at the witness, from the stages above. -/
theorem h3 : Scc.Lower.X64.tablesOf irL.1 emL.1 cfgW.gcWit =
    .ok (.dir ".section .rodata" :: tblL.map Scc.Cert.MapsX64.dataItem, tblL) := by
  have hc : computeWR fnsL itL gwL = .ok tL := ht ▸ computeWR_of_least hle (computeW_of_stagesF hs hl hm ho hf)
  exact Scc.Cert.MapsX64.emitTablesW_of_stages hg (Scc.Cert.MapsX64.fnTagsX64_of_stages hi hst hfn) hc hlab hser

/-- `ofStage` of the stages is the literal. -/
theorem hF : ofStage SccCode.ret0Asm.sizes SccCode.ret0Asm.labelOffs
    (irL.1, emL.1, emL.2, tblL, (Scc.Lower.stackNeed .x64 irL.1).toOption, irL.2) = ret0L := by
  kernel_rfl

end Stage

open Stage in
/-- The literal is the pipeline's output: scc's run is the run at its ranked witness
(`lowerAll_eq_of_tables`), which is `ofStage` of the stages' literals (`ofEmitted_of_stages`). -/
theorem ret0_out_eq : ret0O = ret0L :=
  (congrArg (Out.ofEmitted · SccCode.ret0Asm.sizes SccCode.ret0Asm.labelOffs)
    (Scc.Cert.OutStageWX64.lowerAll_eq_of_tables (cfg := { arch := .x64 }) rfl _ gwL
      (tables_of_stages h1 h2 h3))).trans
    ((ofEmitted_of_stages SccCode.ret0Asm.sizes SccCode.ret0Asm.labelOffs h1 h2 h3).trans hF)

end Spike.Test.X64Ret0PlaceOKE
