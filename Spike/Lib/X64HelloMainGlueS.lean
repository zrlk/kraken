/-
**hello.w on x86-64: `scc_rt_main`'s premises from `wc_rodata`'s `.sp0` to `wc_main`'s box, with frames** (the
twin of `Spike/Lib/A64HelloMainGlueS.lean`'s live part).

`scc_rt_main` up to `call wc_rodata` is at `[]`, `wc_rodata` (call taken at its entry, return popped at `.sp0`)
at `[fr]`, and `scc_rt_main`'s rest with `wc_main` at `[]` again (`HelloM.hello_main_post_segWST`, then
`HelloWc.hello_wc_entry_segJrA` at every caller's state there).

- `NSW`: `NoSetFsW`'s body (see below).
- `MainWcPS`: `wc_rodata`'s premises at `[fr]` (`hW : MainPostSWH`, `hbp`, `hra` … `hfen`, `hedge` under
  `ms [fr]`, `hedge` into `retJH fr Jr`, `hsl`), `wc_main`'s at `[]` under `ms []` (`hJpT` … `hxa`).

**Where this differs from AArch64** (forced by the x86-64 shape):
- The fields are `HelloM.hello_main_post_segWST`'s premises (`X64HelloMainPostT`): there is no fence
  instruction, so `hfen` (`FenceRun … J4 → J5`, as AArch64's) is taken as a source stutter before
  `wc_rodata`'s last block, whose source invariant is `HelloRd.J4P J4 J4x` (`hW`): the publication's targets are
  in `J4x` (`hpubx`), each running locally into `J5` (`hlocx`); `hedge` is from `J5`. The
  composed segment is a `SegWSP` (`Spike/Lib/X64SegWPub.lean`; AArch64: a `SegWS`).
  `rodata`'s results are in `%rax`, `%rdx`, `%rcx`, `%rsi`, its saved `%rbp` at `slot (-8)`, and the caller's
  `%rsp` is `%rbp + 16` (AArch64: `x0` … `x3`, `x29`/`x30` at `slot (-16)`/`slot (-8)`).
- `hbp` (`%rbp` at `mR R`'s saved-`%rbp` slot at `.sp0`) and `hsl` (`.sp0`'s `slot (-8)`, the `%rbp` the
  return restores, at `R`'s) are new: `scc_rt_main`'s rest addresses its frame off `%rbp`. `hsl` is asked of
  `Jp`, not of `Jr`: the source's return `Jr` does not know `%rbp`.
- `hra` is `.Lscc_rt_main.x0`, the return address pushed at `slot 0` (AArch64: `.L1_scc_rt_main.sp0` at
  `slot (-8)`, `x30`); `hmem`'s cells are off `%rax` (`bAddr`; AArch64: `rAddr … .X0`).
- The thread pointer is `fsBase` (`hJpT`), the box's segment inside `NoSetFsW (tpG t W) K` (AArch64:
  `TPIDR_EL0`, `NoMsrW`); `hlim`'s limit word is at `fsBase + 8`, bounded by `Jr`'s `%rsp - 8 - 8 - 128`
  (`HelloWc.lim_wcJ0`; AArch64: `tcbA _ 8`, `SP - 144`).
- The box's landing (`hxa`) is on the frame based at the saved `%rbp`, `(wcR R D).fp (-8)`
  (`HelloWc.hello_wc_entry_segJrA`; AArch64: `wcR R D`).
- `SegWS.seq_or`, `main_wc_segWS` and `hello_main_wc_segWS` are not twinned: they are dead in hello (its
  consumers take `MainWcPS` to `X64HelloWcPreA`'s forms with the abort at `wXA`). `MainGlueW` is not imported.
- `hWp`/`hWs` are inside `NSW`, `NoSetFsW`'s body, definitionally both `Spike.Lib.X64.NoSetFsW` (`X64KeepTPW`,
  `X64HelloWcPreA`'s) and `Spike.Lib.X64.Flow.NoSetFsW` (`X64Hello1RodataTP`, under `X64HelloMainPostT`).
-/
import Spike.Lib.X64HelloMainPostT
import Spike.Lib.X64HelloWcPreA

namespace Spike.Lib.X64.HelloPh.MainGlueS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (FragS Frag MemSide Region SegW SegWS LocalRun XchgSite)
open Spike.Lib.X64 (At AS bAddr)
open Spike.Lib.X64.Flow.Ret0 (LimOk)
open Spike.Lib.X64.Flow.Hello1 (mR mF rpK1 rpK2 mWC)
open Spike.Lib.X64.Flow.HelloM (MainPostSWH wcR wcF wcJ0 JrT)
open Spike.Lib.X64.Flow.HelloWc (bXH WcPreWH WcSp0WH)
open Spike.Lib.X64.Flow.WakeWc (AGB BoxW)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64HelloRdCf (retJH)
/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-- **`W` at no `arch_prctl`, not moved by `K`**: `NoSetFsW`'s body (`X64KeepTPW`, `X64Hello1RodataTP`). -/
abbrev NSW (W : Frag isa) (K : State → State → Prop) : Frag isa :=
  fun s c => W s c ∧ Spike.Lib.X64.KeepTP.NoSetFsAt s ∧ ∀ s', ¬ K s s'

example (W : Frag isa) (K : State → State → Prop) : NSW W K = Spike.Lib.X64.Flow.NoSetFsW W K := rfl

/-- **`wc_rodata`'s rest and `wc_main`'s premises past the layout's**, for a caller's state `m0`, `σC` at
`wc_rodata`'s call under the frame `fr` and `wc_main`'s region `D` deep at its call: `wc_rodata`'s states at
`[fr]` and the `.sp0` block's at `[]` (`hW`), `wc_rodata`'s source and frame facts from `.sp0` under `ms [fr]`
(`hbp` … `hedge`, the publication's targets `J4x`, its source's `ret` popping `fr` into `Jr`: `retJH fr Jr`; the `%rbp` it restores, `hsl`), and
`wc_main`'s entry's at `[]` under `ms []` (`hJpT` … `hxa`; `wc_main`'s at `JrT Jr t R`, `Jp`'s thread pointer
`t` by `hJpT`). The allocator's words (`hmem0`) are left to the caller. -/
structure MainWcPS (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (D : Int)
    (F : MachineData → Prop) (fr : TermRun.Frame) (m0 : MachineData) (σC : FAS)
    (Jp Jp' J1 J2 J2' J3 J4 J4x J5 Jr Jr1 : FAS → Ctl → Prop) (t : UInt64) : Prop where
  hW : MainPostSWH W K exe endPc R F fr m0 σC Jp Jp' J1 J2 J2' J3 (Spike.Lib.X64.Flow.HelloRd.J4P J4 J4x)
    (JrT Jr t R)
  hbp : ∀ σ0 c, Jp σ0 c → σ0.regs.get64 .rbp = (mR R).addr (-8)
  hra : ∀ σ0 c, Jp σ0 c → (_root_.Executable.labels exe).label ".Lscc_rt_main.x0" = Int64.ofBitVec (σ0.slot 0)
  hmem : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
    ∀ m, mF R F m0 σC m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none
  hr0 : ∀ σ0 c, Jp σ0 c → ∃ c', LocalRun p c c' ∧ Jp' σ0 c'
  h1 : ∀ σ0 c, Jp' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J1 σ0 { c with hold := some ((bAddr σ0.regs .rax 0).toNat, w') }
  h2 : ∀ σ0 c, J1 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 0).toNat ∧
    c.hold = some ((bAddr σ0.regs .rax 0).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK1.setWidth 128).toNat ∧ J2 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hr2 : ∀ σ0 c, J2 σ0 c → ∃ c', LocalRun p c c' ∧ J2' σ0 c'
  h3 : ∀ σ0 c, J2' σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧ c.hold = none ∧
    ∀ (r : Val) (w' : TermRun.Word), (ms [fr]).rd w' → Scc.Sem.ValRep lbl w'.val (r.setWidth 64).toNat →
      J3 σ0 { c with hold := some ((bAddr σ0.regs .rax 8).toNat, w') }
  h4 : ∀ σ0 c, J3 σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr) (tv : Ty)
    (wv wold : TermRun.Word),
    XchgSite c x sa u v e ∧ Scc.Sem.ValRep lbl (.loc sa 0) (bAddr σ0.regs .rax 8).toNat ∧
    c.hold = some ((bAddr σ0.regs .rax 8).toNat, wold) ∧ TermRun.evalAt c.env v = some (tv, [wv]) ∧
    Scc.Sem.ValRep lbl wv.val (rpK2.setWidth 128).toNat ∧ J4 σ0 ⟨e, (x, u, [wold]) :: c.env, none⟩
  hfen : ∀ σ0 c, J4 σ0 c → ∃ c', Spike.Lib.FenceRun p (ms [fr]).pub .st c c' ∧ J5 σ0 c'
  hpubx : ∀ σ0 c c₁, J4 σ0 c → Spike.Lib.PubStep .st c c₁ → J4x σ0 c₁
  hlocx : ∀ σ0 c, J4x σ0 c → ∃ c', LocalRun p c c' ∧ J5 σ0 c'
  hedge : ∀ σ0 c, J5 σ0 c → ∀ σ' : FAS, σ'.regs.rax.toBitVec = σ0.regs.rax.toBitVec →
    σ'.regs.rdx.toBitVec = 0#64 → σ'.regs.rcx.toBitVec = 2#64 → σ'.regs.rsi.toBitVec = 13#64 →
    σ'.regs.rbp.toBitVec = σ0.slot (-8) → σ'.regs.rsp.toBitVec = σ0.regs.rbp.toBitVec + 8#64 + 8#64 →
    ∃ c', LocalRun p c c' ∧ retJH fr Jr σ' c'
  hsl : ∀ σ0 c, Jp σ0 c → σ0.slot (-8) = R.addr (-8)
  hJpT : ∀ σ0 c, Jp σ0 c → σ0.regs.fsBase = t
  hWp : ∀ m1 σ1, WcPreWH (NSW (tpG t fun s c => W s c []) K) K exe endPc (wcR R D)
    (wcF R D F m1 σ1)
    (tpXa (ms []) t) (wcJ0 (mWC (_root_.Executable.labels exe).label σC (JrT Jr t R)).J σ1)
    (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
  hWs : ∀ m1 σ1, WcSp0WH (NSW (tpG t fun s c => W s c []) K) K exe endPc (wcR R D)
    (wcF R D F m1 σ1)
    (tpXa (ms []) t) (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)
  hlim : ∀ σ c, JrT Jr t R σ c → LimOk (ms []) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
    (σ.regs.rsp.toBitVec - 8#64 - 8#64 - (128 : Int64).toBitVec)
  hloc : ∀ σ c, JrT Jr t R σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c'
  hq : ∀ σ c, Jr1 σ c → ∃ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
    q.h = 256#64 ∧ q.k = 1#64 ∧ q.u (ms []) = 2#64
  hbox : ∀ q : AGB (ms []) (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → BoxW lbl q.1
  hcell0 : ∀ q : AGB (ms []) (_root_.Executable.labels exe).label, (∃ σ, Jr1 σ q.1.c0) → ∀ o : Nat,
    (ms []).lo o → o + (ms []).units 1 q.1.τ ≤ (ms []).cells →
    (ms []).mp ⟨BitVec.ofNat 64 ((ms []).heap + 16 * o + (ms []).off 1 q.1.τ), 8⟩ true ∧
    ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ((ms []).heap + 16 * o + (ms []).off 1 q.1.τ)) 8 = none
  hxa : ∀ m1 σ1, ∀ l A s c, lbl l = none → At exe endPc ((wcR R D).fp (-8)) (wcF R D F m1 σ1)
    (bXH (ms []) (_root_.Executable.labels exe).label
      (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) l A) s c →
    TP t s → (ms []).xa l A 1 s c

/-- **The fields compose**: `HelloM.hello_main_post_segWST` from `wc_rodata`'s `.sp0` at `[fr]`, then at every
caller's state at `wc_main`'s call `HelloWc.hello_wc_entry_segJrA` at `[]`, to `wc_main`'s heap abort at `wXA`
(a check of the field shapes: `main_wc_segWS`'s twin is not a live constant). -/
example {W : FragS isa} {K : State → State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fr : TermRun.Frame}
    (hK : (ms []).K = some Scc.Sem.X64.abi) (hK' : (ms [fr]).K = some Scc.Sem.X64.abi) {kp : Nat}
    (hp : Scc.Cert.Rt.X64.Lays exe SccCode.helloCells kp)
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe SccCode.helloCells kp) {D : Int} (hD : 304 ≤ D) (hD8 : D % 8 = 0)
    (hF : Spike.Lib.X64.FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 8 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {Jp Jp' J1 J2 J2' J3 J4 J4x J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J4x J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    Spike.Lib.X64SegWPub.SegWSP W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (Spike.Lib.X64.Flow.HelloRd.pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (Spike.Lib.X64.Flow.HelloWc.wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  Spike.Lib.X64.Flow.HelloM.hello_main_post_segWST hp hend hK' (by omega) hD8 hF hR hlo hloD hhi hfr
    hP.hJpT hP.hW hP.hbp hP.hra hP.hmem hP.hr0 hP.h1 hP.h2 hP.hr2 hP.h3 hP.h4 hP.hfen hP.hpubx hP.hlocx hP.hedge hP.hsl
    fun m1 σ1 hR' hF' =>
      Spike.Lib.X64.Flow.HelloWc.hello_wc_entry_segJrA hK hp hend hF' hR' (show -D ≤ -304 by omega)
        (show (8 : Int) ≤ 8 by decide) (fun _ _ h => h.2.1) (hP.hWp m1 σ1) (hP.hWs m1 σ1) hP.hlim hP.hloc
        hP.hq hmem0 hP.hbox hP.hcell0 (hP.hxa m1 σ1)

end Spike.Lib.X64.HelloPh.MainGlueS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.MainGlueS.MainWcPS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainGlueS.MainWcPS
