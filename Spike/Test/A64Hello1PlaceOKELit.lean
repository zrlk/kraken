import Scc.Cert.PlaceDataA64
import Scc.Cert.OutLitA64
import Scc.Cert.OutStageA64
import Scc.Cert.OutStageWA64
import Scc.Cert.MapsPart
import Scc.Cert.MapsEmitA64
import Spike.Lib.Hello1Src

/-!
# `hello1.w`'s output as a literal

scc's AArch64 output for `hello1.w` (`hello1O`, computed by `lowerAll` and
`Out.ofEmitted`) and its value written out at elaboration time (`hello1L`,
`scc_lit%`), equal by kernel runs of the pipeline's stages (`hello1_out_eq`), in
a file of its own: `Spike/Test/A64Hello1PlaceOKE.lean` decides `PlaceOK`'s
parts on the literal, each well within the kernel's memory.

The pipeline ends with the GC tables' stage (`Scc.Lower.A64.tablesOf`), whose
reference fixpoint (`gcWit = none`) the kernel cannot afford. As a
certificate does (`Scc.Config.gcWit`), the equation goes through the run at
scc's ranked witness (`Stage.gwL`, `Stage.cfgW`), equal to scc's run where the
tables' stage at the witness succeeds
(`Scc.Cert.OutStageWA64.lowerAll_eq_of_tables`), and that run is checked in
stages on literals (`Stage`: the lowering, the emitter, the tables' items,
`scc_stackmap` table, tags, least fixpoints, maps, successors and
serialisation, then `ofStage`), each its own kernel check.
-/

namespace Spike.Test.A64Hello1PlaceOKE

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- scc's AArch64 output for `hello1.w` as `PlaceOK` reads it. -/
def hello1O : Out := Out.ofEmitted (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Hello1Src.hello1Src)

-- implemented_by: untrusted (compiled code only); kernel and theorems see the literal (= hello1O, hello1_out_eq).
/-- `hello1O` as a literal: its value computed at elaboration time. Compiled code
(the `#guard`s of `Spike/Test/A64Hello1NeedOk1.lean`) runs `hello1O` instead, equal to it by
`hello1_out_eq`: the code generator cannot compile the literal at the default `maxRecDepth`. -/
@[implemented_by hello1O] def hello1L : Out := scc_lit% hello1O

/-! ## The pipeline's stages on literals

Each `…Val` is computed at elaboration time (untrusted), its `…L` the
literal, which the theorem after checks in the kernel. -/

namespace Stage

open Scc.Cert.Maps

/-- scc's run, at elaboration time. -/
def run : Scc.Lower.A64.Emitted := Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Hello1Src.hello1Src

/-- scc's ranked witness for the GC tables (`gcWitness`), at elaboration time. -/
def gwVal : GcWit := (Scc.Cert.MapsA64.gcWitness run.low.ir run.items).toOption.getD []

/-- The witness, as a literal (untrusted: the tables' stage checks it, `hle`). -/
noncomputable def gwL : GcWit := scc_lit% gwVal

/-- scc's configuration with the witness. -/
noncomputable def cfgW : Scc.Config := { ({ arch := .arm } : Scc.Config) with gcWit := some gwL }

def irVal : Scc.IR.Program × Bool := (lowered1 { arch := .arm } Spike.Lib.Hello1Src.hello1Src).getD default
noncomputable def irL : Scc.IR.Program × Bool := scc_lit% irVal

def emVal : List Scc.Emit.A64.Item × List Scc.Emit.A64.Safepoint :=
  (Scc.Emit.A64.emitItemsMaps irVal.1).toOption.getD default
noncomputable def emL : List Scc.Emit.A64.Item × List Scc.Emit.A64.Safepoint := scc_lit% emVal

def areasVal : List (Scc.IR.Sym × Nat) := (Scc.Emit.A64.emitPre irVal.1).toOption.getD []
noncomputable def areasL : List (Scc.IR.Sym × Nat) := scc_lit% areasVal

def itVal : List Item := (Scc.Cert.MapsA64.itemsOf emVal.1).toOption.getD []
noncomputable def itL : List Item := scc_lit% itVal

def stVal : List (Nat × List Int × List Int) := (Scc.Cert.MapsA64.stackTable emVal.1 itVal).toOption.getD []
noncomputable def stL : List (Nat × List Int × List Int) := scc_lit% stVal

def fnsVal : List FnTags :=
  (irVal.1.funcs.zipIdx.mapM (Scc.Cert.MapsA64.tagsOf irVal.1 areasVal itVal stVal)).toOption.getD []
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

theorem h1 : lowered1 cfgW Spike.Lib.Hello1Src.hello1Src = some irL := by kernel_rfl
theorem h2 : Scc.Emit.A64.emitItemsMaps irL.1 = .ok emL := by kernel_rfl
theorem hg : irL.1.growth.isSome = true := by kernel_rfl
theorem ha : Scc.Emit.A64.emitPre irL.1 = .ok areasL := by kernel_rfl
theorem hi : Scc.Cert.MapsA64.itemsOf emL.1 = .ok itL := by kernel_rfl
theorem hst : Scc.Cert.MapsA64.stackTable emL.1 itL = .ok stL := by kernel_rfl
theorem hfn : irL.1.funcs.zipIdx.mapM (Scc.Cert.MapsA64.tagsOf irL.1 areasL itL stL) = .ok fnsL := by kernel_rfl
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
theorem h3 : Scc.Lower.A64.tablesOf irL.1 emL.1 cfgW.gcWit =
    .ok (.raw ".section .rodata" :: tblL.map Scc.Cert.MapsA64.dataItem, tblL) := by
  have hc : computeWR fnsL itL gwL = .ok tL := ht ▸ computeWR_of_least hle (computeW_of_stagesF hs hl hm ho hf)
  exact Scc.Cert.MapsA64.emitTablesW_of_stages hg (Scc.Cert.MapsA64.fnTagsA64_of_stages ha hi hst hfn) hc hlab hser

/-- `ofStage` of the stages is the literal. -/
theorem hF : ofStage
    (irL.1, emL.1, emL.2, tblL, (Scc.Lower.stackNeed .arm irL.1).toOption, irL.2) = hello1L := by
  kernel_rfl

end Stage

open Stage in
/-- The literal is the pipeline's output: scc's run is the run at its ranked witness
(`lowerAll_eq_of_tables`), which is `ofStage` of the stages' literals (`ofEmitted_of_stages`). -/
theorem hello1_out_eq : hello1O = hello1L :=
  (congrArg (Out.ofEmitted ·)
    (Scc.Cert.OutStageWA64.lowerAll_eq_of_tables (cfg := { arch := .arm }) rfl _ gwL
      (tables_of_stages h1 h2 h3))).trans
    ((ofEmitted_of_stages h1 h2 h3).trans hF)

end Spike.Test.A64Hello1PlaceOKE
