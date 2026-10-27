/-
**A code block's prologue inside the body's fragment at depth** (x86-64,
H7a calls): the prologue obligation `XProW` of `CalleePre`'s `hpro`
(`Spike/Lib/LowerX64/ProgCB.lean`) inside `BodyWS0` at the frames `fs`,
from the prologue's code and phase facts, with no premise about the call
brackets.

- `proW_bodyS`: a stack-checked prologue with saved registers `ps` in the
  frame (`proW_sfactsP` at the held-back control `c0`) inside `BodyWS0` at
  `fs`, every control of its invariant `Good1` at `fs` with no hold;
- `spillsOk_of_hps`: `FnCode`'s parameter spill (`hps`) at cells of the
  frame, as `proW_bodyS` takes it.
-/
import Spike.Lib.LowerX64.BodyWS1
import Spike.Lib.LowerX64.UserW
import Spike.Lib.LowerX64.Construct

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow (XProW prologueIn)
open Scc.Lower.InvX64
open Scc.Emit.X64 (labelOf)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl K0)
open Spike.Lib.X64ConsumerS (SFactsS)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA)

/-- **`FnCode`'s parameter spill is at a cell of the frame**: no spill, or
the parameter's `%rdi` at `o` with `-8 + o` a cell of the frame below the
saved `%rbp`. -/
theorem spillsOk_of_hps {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31) {ps : List (Reg64 × Int64 × Nat)}
    {prs : List Scc.IR.Reg}
    (hps : (ps = [] ∧ prs = []) ∨ ∃ pr o zp, ps = [(.rdi, o, zp)] ∧ prs = [pr] ∧
      (∀ k, rsOf fr pr = some k → k = o.toInt) ∧ o.toInt ≤ -8 ∧
      offOk (-8 - (fr.size : Int)) 0 (-8 + o.toInt) = true) :
    ∀ q ∈ ps, offOk (-8 - (Int64.ofInt fr.size).toInt) 0 (-8 + q.2.1.toInt) = true := by
  have hF64 : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  rw [hF64]
  rcases hps with ⟨rfl, -⟩ | ⟨pr, o, zp, rfl, -, -, -, hok⟩
  · intro q hq; cases hq
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hok

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl}

/-- **A code block's prologue is inside `BodyWS0` at the frames `fs`**
(`CalleePre`'s `hpro`): its code (`hin`, at the frame `fr`, the limit at
`Tcb.stackLimit`) with its saved registers at cells of the frame (`hps`),
its phase facts (`hph`), every control of its invariant `Good1` at `fs`
with no hold and the `%fs` base `tp` (`hJ`), the thread pointer's limit
word mapped (`hmr`) and unmapped in private memory (`hun`), in any
8-aligned region holding the frame below the saved `%rbp`: `proW_sfactsP`
at the held-back control `c0` (`Good1` with no frame and no hold), its
facts lifted to `SFactsS` at the empty frames (`SFactsS.ofSFacts0`). -/
theorem proW_bodyS {ms : MemSide isa} {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (h1 : fr.size ≤ 2 ^ 31) {fn entry : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn (labelOf fr.fn "chk") entry (Int64.ofInt fr.size)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL fr) zl zf z1 z2 zs ps = true)
    (hps : ∀ q ∈ ps, offOk (-8 - (Int64.ofInt fr.size).toInt) 0 (-8 + q.2.1.toInt) = true)
    (hph : ProPh okPc ph lab fn (labelOf fr.fn "chk") (Int64.ofInt fr.size) (proL fr) zl zf z1 z2 zs ps)
    (hC0 : CFacts Λ lbl c0) (hp : Scc.Lower.Accepted1 p = true) (hg0 : Good1 p (c0, []))
    {cl ctr : Nat} {fs : List TermRun.Frame} {tp : UInt64} {J : AS → Ctl → Prop}
    (hJ : ∀ σ c, J σ c → σ.regs.fsBase = tp ∧ Good1 p (c, fs) ∧ c.hold = none)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -8 - (fr.size : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hmr : Scc.Sem.Kernel.mapped (K0 Λ) false ⟨limA tp, 8⟩ = true)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    XProW (fun s c => BodyWS0 Λ μ p own rS Tk lbl cl ctr c0 s c fs) K exe endPc R F ms
      ((_root_.Executable.labels exe).label fn) (Int64.ofInt fr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit)
      (proL fr) zl zf z1 z2 zs ps J := by
  have hF64 : (Int64.ofInt fr.size).toInt = fr.size := toInt_ofInt_small (by omega) (by omega)
  have H := proW_sfactsP (J := fun σ c => c = c0 ∧ ∃ c1, J σ c1) (ms := ms) hI hin hps hC0 (fun _ _ h => h.1)
    (fun _ _ ⟨_, _, h⟩ => (hJ _ _ h).1) hph hR hR8 (by rw [hF64]; exact hlo) hhi hl hh (by rw [hF64]; omega)
    hmr hun hsub hfit hFO
  exact XProW.mapC H fun σ c hJc =>
    ⟨c0, ⟨rfl, c, hJc⟩, fun _ hs => ⟨(hJ σ c hJc).2.1, (hJ σ c hJc).2.2, SFactsS.ofSFacts0 hs hp hg0⟩⟩

end W

end Spike.Lib.LowerX64
