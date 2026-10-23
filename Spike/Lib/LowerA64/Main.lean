/-
**The user `main` of an `Accepted0` program is one segment** (AArch64),
from the program's `PlaceOK`.

`main_seg_of_placeOK`: on an `Accepted0` program that lowers and emits
(`lowerAll?`), whose output passes `PlaceOK`, `main`'s lowered body `r`
(`lower0` of the source body) is the `fi`th function `func0 main r` of the
lowered IR, its context `cx` (`ctxOf`) has a valid frame of at most 4095
bytes (`Accepted0`'s bound on the body's slots), a multiple of 16, and in any valid
layout of the output's instructions `fn0_seg` holds of it: from `main`'s
label to the return's exit or the overflow abort label (its immediates
`immsOf d`'s). The code facts are
`PlaceOK`'s A9 (`fnCode_of_placeOKAt`) at the IR the output names
(`lowerAll_place_ir`), the context and the body's shape `main_inv_a64`.
-/
import Spike.Lib.LowerA64.Fn
import Scc.Cert.PlaceDataA64
import Scc.Lower.InvBodyA64

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.Form (NodeJ SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 Res func0)

/-- The environment of a code block's body (its `Unit` argument, no word)
is fresh. -/
theorem fresh_unit (arg : String) : Fresh [(arg, .unit, [])] 0 := by
  intro v hv o ho
  simp only [List.mem_singleton] at hv
  subst hv
  cases ho

/-- **The segment of the user `main`** of `cfg`'s output for `[d]`:
`main`'s lowered body `r`, its index `fi` in the lowered IR, its context
`cx` (a valid frame of at most 4095 bytes, a multiple of 16, no outgoing
area); in any valid layout of the output's instructions, from `main`'s
label to the return's exit or the overflow abort label, given the
prologue's obligations (`ProW`, the edge) and the body's blocks' (`BlkW`
at its nodes and pending stores, each block one of the body's, `InBody`). -/
def MainSeg (cfg : Scc.Config) (d : Decl) : Prop :=
  ∃ (r : Res) (fi : Nat), lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
    (func0 (Scc.Lower.Names.user "main") r, fi) ∈ (Scc.Lower.A64.lowerAll cfg [d]).low.ir.funcs.zipIdx ∧
    let cx := Scc.Lower.A64.ctxOf (Scc.Lower.A64.lowerAll cfg [d]).low.ir fi (func0 (Scc.Lower.Names.user "main") r)
    FrameOk cx ∧ cx.frame ≤ 4095 ∧ cx.frame % 16 = 0 ∧ cx.out = 0 ∧
    ∀ {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
      {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
      {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
      {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl},
      Lays exe (Scc.Lower.A64.lowerAll cfg [d]).prog →
      endPc = endOf exe (Scc.Lower.A64.lowerAll cfg [d]).prog →
      FStable R F → R.OK → R.base.toNat % 16 = 0 → R.lo ≤ -(cx.frame : Int) → 0 ≤ R.hi →
      ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label (Scc.Lower.Names.user "main"))
        (Int64.ofInt cx.frame) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL cx) [] J →
      (∀ pc t s blk, CdOf exe endPc pc blk →
        InBody (_root_.Executable.labels exe).label cx (cx.prefix ++ "0_entry") r.insts r.ret pc blk →
        BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc t s) blk) →
      (∀ pc t s k blk, CdOf exe endPc pc blk →
        InBody (_root_.Executable.labels exe).label cx (cx.prefix ++ "0_entry") r.insts r.ret pc blk →
        BlkW W K exe endPc R F (pendN p lbl cx fp ra c0 pc t s k) blk) →
      (∀ σ c, J σ c →
        (ms.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
          ms.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
          (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
          ∀ v : Val, ms.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
            (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt cx.frame).toBitVec).toNat) ∧
        σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
        (∀ sl, NJ p lbl (rsOf cx) d.body (ofEnv [(d.arg, .unit, [])]) sl c) ∧ LocalRun p c0 c) →
      SegW W K p lbl ms
        (At exe endPc R F ⟨(_root_.Executable.labels exe).label (Scc.Lower.Names.user "main"), ⟨0, []⟩, J⟩)
        (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
          At exe endPc R F (abortN (immsOf d) (InWalk d) p lbl cx (_root_.Executable.labels exe).label fp ra c0) s c)

/-- **The user `main` of an `Accepted0` program is one segment**, from its
`PlaceOK` (`MainSeg`). -/
theorem main_seg_of_placeOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (hpl : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ
      (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])) = true) :
    MainSeg cfg d := by
  obtain ⟨r, rt, hr, -, hir, hmem, hinv⟩ := main_inv_a64 cfg hd hlow
  obtain ⟨hfo, hout, h16, -, -, -, -, hI, -, -, -, hle⟩ := hinv
  rw [← hir] at hmem hfo hout h16 hle
  refine ⟨r, rt.length, hr, hmem, hfo, hle, h16, hout, ?_⟩
  intro p lbl ms exe _ endPc R F W K J fp ra c0 hp hend hF hR hal hlo hhi hWp hWb hWs hedge
  obtain ⟨w, hw⟩ := Scc.Lower.Inv.accepted0_ret_singleton hd hr
  obtain ⟨hpro, hbody⟩ := Scc.Cert.PlaceOK.A64.fnCode_of_placeOKAt hpl
    (Scc.Cert.PlaceOK.A64.lowerAll_place_ir cfg [d]) hmem hI hw
  exact fn0_seg hfo hle h16 hp hend hpro hr (fresh_unit d.arg) hbody (walk_immsOf d) hF hR hal hlo hhi hWp hWb hWs
    hedge

end Spike.Lib.LowerA64
