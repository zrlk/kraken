/-
**`ChildPrem.hsvc` at the worker's owning memory side on x86-64**: `X64HelloCPSvc.hsvc_preRH` restated at
`X64HelloOwnLift.msWHX` (`msWH` owning hello's second TCB word `tcbWH`, its runtime writes off both self words).
`msWHX` changes only `own` and `mp`; its byte step `bo`, abort justification `we` and ABI `K` are `msWH`'s, so
`SegR.hsvc_IW` closes `hsvc` exactly as at `msWH`.

- `hsvc_IX`: `ChildPrem.hsvc` at the instance's owning worker side.
- `hsvc_preRHX`: `SvcX … (wordsX th) tp w0 w1 w2 w3 w4 13 2` at the record's placement and `msWHX`.

## Differences from the AArch64 version

Unlike AArch64, the worker's memory side owns its TCB's self word (`%fs:0` is a load of that word), so the
child's segment is stated at `msWHX` rather than at the non-owning side; AArch64 reads `tpidr_el0`, a register,
and has no such side.
-/
import Spike.Lib.X64HelloCPSvc
import Spike.Lib.X64HelloOwnLift

namespace Spike.Lib.X64HelloAssemblyI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloOwnLift (msWHX)
open Spike.Lib.X64HelloSpawnR (PreRH)
open Spike.Lib.X64HelloOkW (lBH)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (wordsX SvcX)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`ChildPrem.hsvc` at the instance's owning worker side** (`hsvc_I` at `msWHX`: its `bo`, `we` and `K` are
`msWH`'s). -/
theorem hsvc_IX (ho : o.prog = SccCode.helloCells) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i)
    {F : MachineData → Prop} {w' : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    {l : WeakMem.AllocLabel} (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : (SRH hp i w).lbl l = some (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63) :
    SvcX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) F w' tp w0 w1 w2 w3 w4 n m := by
  haveI := (LH hp i).valid
  exact Hello.SegR.hsvc_IW (F := F) (ms := fun _ => msWHX (LH hp i) (GH hp i G0) (SRH hp i) w)
    (lays_H hp i ho) rfl (fun _ => rfl) hpw hl hwn hfit hlen (fun _ _ _ _ _ h => h) (fun _ _ _ h => h)

/-- **`ChildPrem.hsvc` at `PreRH` and the owning worker side** (`hsvc_preRH`'s proof, closing at `hsvc_IX`). -/
theorem hsvc_preRHX (ho : o.prog = SccCode.helloCells) (G0 : ιH hp i → Loc → Val → Prop) {arch : WeakMem.Arch}
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
      (fun _ => msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) F (wordsX th) tp w0 w1 w2 w3 w4 13 2 := by
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
  exact hsvc_IX hp i ho G0 w h0 hl h2 hfit hlen

end Inst

end Spike.Lib.X64HelloAssemblyI

/-- info: 'Spike.Lib.X64HelloAssemblyI.hsvc_IX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hsvc_IX

/-- info: 'Spike.Lib.X64HelloAssemblyI.hsvc_preRHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssemblyI.hsvc_preRHX
