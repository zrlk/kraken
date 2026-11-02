/-
**`ChildPrem.hsvc` at the clone's data on x86-64** (the twin of `Spike/Lib/HelloCPSvc.lean`; the `hCP` call site):
at main's `clone` over the placed layout (`PreRH` at `(LH hp i).Λ`), under `VBufR`, `print`'s `write` in the child
meets `PI`'s memory side (`hsvc_I`) at the clone's words `wordsX th`: the slice's buffer is `lBH`
(`X64HelloNewBuf.clonePreH_labels`), placed at main's `%r12` (`X64HelloPreA.hsvc_clone`), whose 13 bytes fit
(`X64HelloCloneMem.r12_fit_preRH`).

- `hsvc_preRH`: `SvcX … (wordsX th) tp w0 w1 w2 w3 w4 13 2` at the record's placement and `msWH`.

## Differences from the AArch64 version

Unlike AArch64, the buffer's address is main's `%r12` at the clone (AArch64: `x9`), so the fit is
`r12_fit_preRH` (AArch64: `x9_fit_preRH`). `X64HelloNewBuf.clonePreH_labels` already names the buffer label
`lBH`, so the proof needs no step that reads the label off the source's word. The placed program is
`SccCode.helloCells` (AArch64: `helloProg`).
-/
import Spike.Lib.X64HelloChildSvcI
import Spike.Lib.X64HelloChildSvcClone
import Spike.Lib.X64HelloCloneMem
import Spike.Lib.X64HelloChildWords
import Spike.Lib.X64HelloChildX
import Spike.Lib.X64HelloNewBuf

namespace Spike.Lib.X64HelloAssemblyI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64HelloMsW (msWH)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (wordsX SvcX)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`ChildPrem.hsvc` at `PreRH`** (module doc). -/
theorem hsvc_preRH (ho : o.prog = SccCode.helloCells) (G0 : ιH hp i → Loc → Val → Prop) {arch : WeakMem.Arch}
    {R1 : Cfg → TermRun.Cfg → Prop} {cT : ιH hp i → Loc} {cS : ιH hp i → WeakMem.Address} {pT : ιH hp i → Loc}
    {Pa : ιH hp i → Spike.Lib.Inv2Core.Inv2Params isa} {G : ιH hp i → Loc → Val → Prop}
    {passT : State → Prop} {M : Spike.Lib.X64WakeM0.MSide (ιH hp i)} {D : X64HelloW1.WSideH (ιH hp i)}
    {r0 r1 : ιH hp i → Scc.Sem.Range} {w : ιH hp i} {d : Cfg} {th : Thread isa} {stack : Nat}
    {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {j : Nat} {own₀ : List (Loc × Val)}
    {l : WeakMem.AllocLabel} (hv : X64HelloVBuf.VBufR s)
    (hR : PreRH arch R1 (SRH hp i) cT cS pT Pa G passT M D r0 r1 (LH hp i).Λ w d th stack s s' s0 s1 lbl lsize ts j
      own₀ l)
    {F : MachineData → Prop} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word}
    (h0 : w0.val = .loc ⟨lBH, 0⟩ 0) (h2 : w2.val = .num 13) :
    SvcX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) F (wordsX th) tp w0 w1 w2 w3 w4 13 2 := by
  obtain ⟨X, hC⟩ := hR.clone
  have hth := hR.pre.threads
  obtain ⟨lb, ⟨th0, hd, l', hs, hS⟩, -, -, hl, -, hfit, hlen⟩ :=
    X64HelloPreA.hsvc_clone hC hth (X64HelloCloneMem.r12_fit_preRH hR hC)
  obtain ⟨th0', hd', l'', lb', ws, hs', hS', hh, hlb', -, -⟩ := X64HelloNewBuf.clonePreH_labels hv hC
  obtain rfl : th0 = th0' := by
    rw [hs] at hs'
    exact List.singleton_inj.mp (congrArg Array.toList hs')
  have hws : ws = [TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)] := by
    have e := hS'.2.2.2.2.1
    rw [hS.2.2.2.2.1] at e
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at e
    exact e.symm
  subst hws
  simp only [List.head?_cons, Option.some.injEq] at hh
  have hlb : lb = lBH := by
    have e := congrArg (fun x : TermRun.Word => x.val) hh
    simp only [TermRun.cst, Promises.TVal.mk0] at e
    cases e
    exact hlb'
  subst hlb
  rw [← X64HelloSpawnR.lbl_clone hR] at hl
  exact hsvc_I hp i ho G0 w h0 hl h2 hfit hlen

end Inst

end Spike.Lib.X64HelloAssemblyI

/-- info: 'Spike.Lib.X64HelloAssemblyI.hsvc_preRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hsvc_preRH
