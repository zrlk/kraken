/-
**The user `main` of an `Accepted0` program is one segment** (x86-64),
from the program's `PlaceOK`; the twin of `Spike/Lib/LowerA64/Main.lean`.

`main_seg_of_placeOK`: on an `Accepted0` program that lowers and emits
(`lowerAll?`), whose output at the assembler's sizes passes `PlaceOK`,
`main`'s lowered body `r` (`lower0` of the source body) is a function
`func0 main r` of the lowered IR, its frame `fr` (`frOf`, as `emitFunc`
builds it) is valid, a multiple of 16, at most 4096 bytes, and in any
valid layout of the output's cells `fn0_seg` holds of it: from `main`'s
label to the return's exit or the overflow abort label. The code facts are
`PlaceOK`'s A9 (`fnCode_of_placeOK`) at the IR the output names
(`lowerAll_place_ir`), the frame and the body's shape `main_inv_x64`.

Where x86-64 differs from AArch64:
- the frame is the emitter's `Frame` at no function index (`frOf`), and
  `main` is a member of the IR's functions (AArch64: the `fi`th);
- the prologue's cells' sizes are the listing's, existential in `MainSeg`
  (A9 reads them off the cells, `proInS`), and the prologue's obligation
  `XProW` is stated at them;
- the frame's bound comes from `Accepted0` itself (`accepted0_next_x64`:
  at most 508 slots), no hypothesis `hsz`;
- A9 checks only functions returning one word (`fnCodeOk`); `main`'s body
  is one (`Scc.Lower.Inv.accepted0_ret_singleton`: `Accepted0`'s `ret` atom is never `Unit`),
  so this needs no hypothesis;
- the body and its exits are in the region `rbR R` (based at the frame
  record), the entry in `R` (based at the entry `%rsp`), the return address
  the entry's top cell.
-/
import Spike.Lib.LowerX64.Fn
import Scc.Cert.PlaceDataX64
import Scc.Lower.InvBodyX64

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW)
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.Form (SEnv)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (lower0 Res func0)

/-- The environment of a code block's body (its `Unit` argument, no word)
is fresh. -/
theorem fresh_unit (arg : String) : Fresh [(arg, .unit, [])] 0 := by
  intro v hv o ho
  simp only [List.mem_singleton] at hv
  subst hv
  cases ho

/-- The counter at the end of an `Accepted0` body is at most `maxAdds0`
(508): one step per checked `+` (the x86-64 copy of `accepted0_next`, which
is in an AArch64 file). -/
theorem accepted0_next_x64 {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) {r : Res}
    (hr : lower0 [(d.arg, .unit, [])] 0 d.body = some r) : r.next ≤ 508 := by
  have := Scc.Lower.Inv.lower0_next_adds _ _ _ _ hr
  have := Scc.Lower.Inv.accepted0_adds hd
  simp only [Scc.Lower.maxAdds0] at this
  omega

/-- **The segment of the user `main`** of `cfg`'s output for `[d]` at the
assembler's sizes `sizes`: `main`'s lowered body `r`, a function of the
lowered IR, its frame `fr` (valid, a multiple of 16, at most 4096 bytes);
at the listing's sizes of the prologue's cells, in any valid layout of the
output's cells, from `main`'s label to the return's exit or the overflow
abort label, given the prologue's obligations (`XProW`, the edge) and the
body's blocks' (`BlkW` at its nodes and pending stores, each block one of
the body's, `InBody`). -/
def MainSeg (cfg : Scc.Config) (d : Decl) (sizes : List Nat) : Prop :=
  ∃ r : Res, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
    func0 (Scc.Lower.Names.user "main") r ∈ (Scc.Lower.X64.lowerAll cfg [d]).low.ir.funcs ∧
    let fr := frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir (func0 (Scc.Lower.Names.user "main") r)
    FrameOk fr ∧ fr.size ≤ 4096 ∧ fr.size % 16 = 0 ∧
    ∃ zl zf z1 z2 zs : Nat,
    ∀ {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
      {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
      {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
      {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl},
      Lays exe (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes) →
      endPc = endOf exe (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes) →
      FStable R F → R.OK → R.lo ≤ -8 - (fr.size : Int) → 8 ≤ R.hi →
      XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label (Scc.Lower.Names.user "main"))
        (Int64.ofInt fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs [] J →
      (∀ pc t s blk, CdOf exe endPc pc blk →
        InBody (_root_.Executable.labels exe).label
          (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes) fr
          (Scc.Emit.X64.labelOf (Scc.Lower.Names.user "main") "entry") r.insts r.ret pc blk →
        BlkW W K exe endPc (rbR R) F (bodyN p lbl fr fp ra c0 pc t s) blk) →
      (∀ pc t s k blk, CdOf exe endPc pc blk →
        InBody (_root_.Executable.labels exe).label
          (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes) fr
          (Scc.Emit.X64.labelOf (Scc.Lower.Names.user "main") "entry") r.insts r.ret pc blk →
        BlkW W K exe endPc (rbR R) F (pendN p lbl fr fp ra c0 pc t s k) blk) →
      (∀ σ c, J σ c →
        (ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
          ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
          (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
            = none) ∧
          ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
            (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt fr.size).toBitVec).toNat) ∧
        σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧
        (∀ sl, NJ p lbl (rsOf fr) d.body (ofEnv [(d.arg, .unit, [])]) sl c) ∧ LocalRun p c0 c) →
      SegW W K p lbl ms
        (At exe endPc R F ⟨(_root_.Executable.labels exe).label (Scc.Lower.Names.user "main"), ⟨0, []⟩, J⟩)
        (fun s c => At exe endPc (rbR R) F (retN p lbl fp ra c0) s c ∨
          At exe endPc (rbR R) F (abortN (immsOf d) (InWalk d) p lbl fr (_root_.Executable.labels exe).label fp ra c0)
            s c)

/-- **The user `main` of an `Accepted0` program is one segment**, from its
`PlaceOK` (`MainSeg`). -/
theorem main_seg_of_placeOK {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em)
    {pcfg : Scc.Cert.PlaceOK.Config} {sizes : List Nat} {labelOffs : List (String × Nat)}
    (hpl : Scc.Cert.PlaceOK.X64.placeOK pcfg
      (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs) = true) :
    MainSeg cfg d sizes := by
  obtain ⟨r, rt, hr, -, hir, hinv⟩ := main_inv_x64 cfg hd hlow
  obtain ⟨-, hsz, h16, hsl, -, -, hI, -, -, -⟩ := hinv
  have hmem : func0 (Scc.Lower.Names.user "main") r ∈ (Scc.Lower.X64.lowerAll cfg [d]).low.ir.funcs := by
    rw [hir]; simp [Scc.Lower.Inv.progOf]
  have hnext := accepted0_next_x64 hd hr
  rw [← hir] at hsz h16 hsl
  have hle : (frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir (func0 (Scc.Lower.Names.user "main") r)).size ≤ 4096 := by
    simp only [frOf] at hsz hsl ⊢
    omega
  have hfo : FrameOk (frOf (Scc.Lower.X64.lowerAll cfg [d]).low.ir (func0 (Scc.Lower.Names.user "main") r)) :=
    ⟨_, _, rfl, rfl⟩
  obtain ⟨⟨zl, zf, z1, z2, zs, hpro⟩, hbody⟩ := Scc.Cert.PlaceOK.X64.fnCode_of_placeOK hpl
    (Scc.Cert.PlaceOK.X64.lowerAll_place_ir cfg [d] sizes labelOffs) hmem hI
    (Scc.Lower.Inv.accepted0_ret_singleton hd hr).choose_spec
  refine ⟨r, hr, hmem, hfo, hle, h16, zl, zf, z1, z2, zs, ?_⟩
  intro p lbl ms exe _ endPc R F W K J fp ra c0 hp hend hF hR hlo hhi hWp hWb hWs hedge
  exact fn0_seg hfo (by omega) hp hend hpro hr (fresh_unit d.arg) hbody (walk_immsOf d) hF hR hlo hhi hWp hWb hWs hedge

end Spike.Lib.LowerX64
