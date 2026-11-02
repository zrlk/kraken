/-
**The heap abort's obligations at `wXA` at both TCB self words** (x86-64 only): `HabCtlA.wc_heapAbStubKHA`'s
statement at the own map `ownGHXW L a` (main's and the worker's TCB words appended to `ownGH`'s), the map the
root's data owns once main's and the worker's memory sides own their self words.

- `wc_heapAbStubKHAX`: `HabCtlA.wc_heapAbStubKHAg` at `own := ownGHXW L a`, its `hP0` by `HabLftX.hP0X` (the path
  at `ownGH` lifted where both appended maps may be appended, the dispatcher's band on the stack pool `hb`).

Unlike AArch64, whose level owns `ownGH` only (`A64HelloHabCtlA.wc_heapAbStubKHA`, main owning no TCB word
there), x86-64's heap abort runs while the own map carries both self words, so this instance adds the TCB
separation `hsep`, `ha`, `hW` and the band premise `hb` of `HabLftX.hP0X`.
-/
import Spike.Lib.X64HelloHabCtlA
import Spike.Lib.X64HelloHabLftX

namespace Spike.Lib.X64.HelloPh.HabCtlAX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (FStable)
open Spike.Lib.X64.WakeWf (DtW W0)
open Spike.Lib.X64.WakePh (BandIn tcbM)
open Spike.Lib.X64.HelloPh.StartWf (pfxM)
open Spike.Lib.X64.HelloPh (lo ownGHXW)
open Spike.Lib.X64.HelloPh.HabCtlA (WcHAbStubHA HabCtlHA wc_heapAbStubKHAg)
open Spike.Lib.X64HelloOwnLift (tcbWH)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

section Inst

variable {L : RuntimeLayout}
variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hp hlo hlab

/-- **`WcHAbStubHA` from `HabCtlHA` at `ownGHXW L a`**: `wc_heapAbStubKHAg` at both TCB self words, the path
inside `W0` at `ownGHXW` by `HabLftX.hP0X` (`main`'s TCB off `a` and `ownGH`'s words, `hsep`, `ha`; the
worker's off `ownGHX`'s, `hW`; the dispatcher's band on the pool, `hb`). -/
theorem wc_heapAbStubKHAX {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {J1 : FAS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandIn L (R.callee (-304 - 8) (-24) 16))
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : FStable R F) (hR : R.OK) (hlo' : R.lo ≤ -336) (hhi : -296 ≤ R.hi)
    (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : HabCtlHA (ms fs) L.lab p L.Λ L0 ar fs J1 R F)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, Spike.Lib.X64.WakePh.inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStubHA (W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.X64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J1 :=
  wc_heapAbStubKHAg hp hlo hlab hF hR hlo' hhi hK hctl hab
    (Spike.Lib.X64.HelloPh.HabLftX.hP0X (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0)
      (frM := frM) (X0 := X0) hp hlo hlab a hsep ha hW hb hΛ hR hlo' hhi hfs hcl hX0)

end Inst

end Spike.Lib.X64.HelloPh.HabCtlAX

/-- info: 'Spike.Lib.X64.HelloPh.HabCtlAX.wc_heapAbStubKHAX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.HelloPh.HabCtlAX.wc_heapAbStubKHAX
